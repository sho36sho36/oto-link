"use strict";

const SLOT_MS = 80;
const TONE_MS = 56;
const LANE_OFFSET_MS = 2;
const PREAMBLE = [0xd, 0x2, 0xf, 0x0, 0x9, 0x6, 0xa, 0x5, 0x3, 0xc, 0x1, 0xe, 0x4, 0xb, 0x7, 0x8];
const CARRIERS = [
  { zero: 880, one: 1080 },
  { zero: 1480, one: 1680 },
  { zero: 2080, one: 2280 },
  { zero: 2680, one: 2880 },
];
const HEADER_LENGTH = 6;
const SALT_LENGTH = 16;
const IV_LENGTH = 12;
const MAX_CIPHER_BYTES = 528;
const MAX_TEXT_BYTES = 512;
const PBKDF2_ITERATIONS = 180000;
const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8", { fatal: true });

const el = (id) => document.getElementById(id);
const messageInput = el("message");
const encryptToggle = el("encrypt-toggle");
const passphraseInput = el("passphrase");
const sendButton = el("send-button");
const listenButton = el("listen-button");
const stopSendButton = el("stop-send");
const inboxList = el("inbox-list");
const clearInboxButton = el("clear-inbox");
const meters = [...document.querySelectorAll(".meter-track i")];

let rxContext = null;
let rxStream = null;
let rxAnalyser = null;
let rxTimer = null;
let rxFrequencyData = null;
let rxHistory = [];
let rxCapture = null;
let txContext = null;
let txCancelled = false;
let txTimer = null;
let isSending = false;
let toastTimer = null;
let receivedCount = 0;

const crcTable = new Uint32Array(256);
for (let n = 0; n < 256; n += 1) {
  let c = n;
  for (let k = 0; k < 8; k += 1) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
  crcTable[n] = c >>> 0;
}

function crc32(bytes) {
  let crc = 0xffffffff;
  for (const byte of bytes) crc = crcTable[(crc ^ byte) & 0xff] ^ (crc >>> 8);
  return (crc ^ 0xffffffff) >>> 0;
}

function setStatus(id, text, tone = "") {
  const node = el(id);
  node.className = "inline-status" + (tone ? " is-" + tone : "");
  node.lastElementChild.textContent = text;
}

function showToast(text) {
  const toast = el("toast");
  toast.textContent = text;
  toast.classList.add("visible");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => toast.classList.remove("visible"), 2400);
}

function formatDuration(seconds) {
  if (seconds < 60) return Math.max(1, Math.round(seconds)) + " 秒";
  const mins = Math.floor(seconds / 60);
  const secs = Math.round(seconds % 60);
  return mins + " 分 " + secs + " 秒";
}

function updateComposer() {
  const bytes = encoder.encode(messageInput.value);
  const encrypted = encryptToggle.checked;
  const cipherLength = bytes.length + (encrypted ? 16 : 0);
  const frameLength = HEADER_LENGTH + SALT_LENGTH + IV_LENGTH + cipherLength + 4;
  const seconds = (PREAMBLE.length + frameLength * 2) * SLOT_MS / 1000;
  el("byte-count").textContent = bytes.length + " bytes";
  el("time-estimate").textContent = "約 " + formatDuration(seconds);
  el("volume-value").textContent = String(Math.round(Number(el("volume").value) * 100)).padStart(2, "0");
  el("password-area").parentElement.classList.toggle("disabled", !encrypted);
  passphraseInput.disabled = !encrypted;

  const needsPhrase = encrypted && passphraseInput.value.length < 8;
  const valid = bytes.length > 0 && bytes.length <= MAX_TEXT_BYTES && !needsPhrase && !isSending;
  sendButton.disabled = !valid;
  if (bytes.length > MAX_TEXT_BYTES) {
    setStatus("send-status", "UTF-8で" + MAX_TEXT_BYTES + "バイトを超えています", "warn");
  } else if (needsPhrase) {
    setStatus("send-status", "暗号化には8文字以上の合言葉が必要です", "warn");
  } else if (bytes.length === 0 && !isSending) {
    setStatus("send-status", "メッセージを入力してください");
  } else if (!isSending) {
    setStatus("send-status", "準備完了 · 相手側にも同じ合言葉を設定", "good");
  }
}

function concatBytes(...arrays) {
  const total = arrays.reduce((sum, arr) => sum + arr.length, 0);
  const result = new Uint8Array(total);
  let offset = 0;
  for (const arr of arrays) {
    result.set(arr, offset);
    offset += arr.length;
  }
  return result;
}

function uint16be(value) {
  return new Uint8Array([(value >>> 8) & 0xff, value & 0xff]);
}

function uint32be(value) {
  return new Uint8Array([(value >>> 24) & 0xff, (value >>> 16) & 0xff, (value >>> 8) & 0xff, value & 0xff]);
}

function readUint32be(bytes, offset) {
  return (((bytes[offset] << 24) | (bytes[offset + 1] << 16) | (bytes[offset + 2] << 8) | bytes[offset + 3]) >>> 0);
}

async function deriveAesKey(passphrase, salt) {
  const material = await crypto.subtle.importKey("raw", encoder.encode(passphrase), "PBKDF2", false, ["deriveKey"]);
  return crypto.subtle.deriveKey(
    { name: "PBKDF2", salt: salt, iterations: PBKDF2_ITERATIONS, hash: "SHA-256" },
    material,
    { name: "AES-GCM", length: 256 },
    false,
    ["encrypt", "decrypt"],
  );
}

async function buildFrame(plainBytes, encrypted, passphrase) {
  const salt = encrypted ? crypto.getRandomValues(new Uint8Array(SALT_LENGTH)) : new Uint8Array(SALT_LENGTH);
  const iv = encrypted ? crypto.getRandomValues(new Uint8Array(IV_LENGTH)) : new Uint8Array(IV_LENGTH);
  const cipherLength = plainBytes.length + (encrypted ? 16 : 0);
  if (cipherLength > MAX_CIPHER_BYTES) throw new Error("送信できるメッセージの上限を超えました。");

  const header = new Uint8Array([0xa5, 0x5a, 1, encrypted ? 1 : 0, ...uint16be(cipherLength)]);
  let payload = plainBytes;
  if (encrypted) {
    const key = await deriveAesKey(passphrase, salt);
    const encryptedBuffer = await crypto.subtle.encrypt(
      { name: "AES-GCM", iv: iv, additionalData: header, tagLength: 128 },
      key,
      plainBytes,
    );
    payload = new Uint8Array(encryptedBuffer);
  }

  const content = concatBytes(header, salt, iv, payload);
  return concatBytes(content, uint32be(crc32(content)));
}

function frameToNibbles(frame) {
  const nibbles = [...PREAMBLE];
  for (const byte of frame) nibbles.push((byte >>> 4) & 0x0f, byte & 0x0f);
  return nibbles;
}

function setTransmitEnabled(enabled) {
  isSending = enabled;
  sendButton.disabled = enabled;
  stopSendButton.hidden = !enabled;
  updateComposer();
}

function cancelTransmit() {
  if (!isSending) return;
  txCancelled = true;
  clearInterval(txTimer);
  if (txContext && txContext.state !== "closed") txContext.close().catch(() => {});
  txContext = null;
  setTransmitEnabled(false);
  setStatus("send-status", "送信を停止しました", "warn");
}

async function transmit() {
  const plainBytes = encoder.encode(messageInput.value);
  const encrypted = encryptToggle.checked;
  const passphrase = passphraseInput.value;
  if (plainBytes.length === 0 || plainBytes.length > MAX_TEXT_BYTES) return;
  if (encrypted && passphrase.length < 8) {
    setStatus("send-status", "8文字以上の合言葉を入力してください", "warn");
    passphraseInput.focus();
    return;
  }
  if (!window.isSecureContext || !crypto || !crypto.subtle) {
    setStatus("send-status", "暗号化にはHTTPSまたはlocalhostで開いてください", "error");
    return;
  }

  setTransmitEnabled(true);
  txCancelled = false;
  setStatus("send-status", encrypted ? "暗号鍵を準備しています…" : "送信データを準備しています…");
  let nibbles;
  try {
    const frame = await buildFrame(plainBytes, encrypted, passphrase);
    nibbles = frameToNibbles(frame);
  } catch (error) {
    setTransmitEnabled(false);
    setStatus("send-status", "準備できませんでした: " + error.message, "error");
    return;
  }
  if (txCancelled) return;

  const AudioContextClass = window.AudioContext || window.webkitAudioContext;
  if (!AudioContextClass) {
    setTransmitEnabled(false);
    setStatus("send-status", "このブラウザーはWeb Audioに対応していません", "error");
    return;
  }

  try {
    txContext = new AudioContextClass({ latencyHint: "interactive" });
    await txContext.resume();
    const startAt = txContext.currentTime + 0.12;
    const level = Number(el("volume").value);
    const oscillators = [];

    CARRIERS.forEach((carrier, lane) => {
      const oscillator = txContext.createOscillator();
      const gain = txContext.createGain();
      oscillator.type = "sine";
      gain.gain.value = 0;
      oscillator.connect(gain);
      gain.connect(txContext.destination);
      oscillator.start(startAt);
      oscillator.stop(startAt + (nibbles.length * SLOT_MS) / 1000 + 0.12);
      oscillators.push({ oscillator: oscillator, gain: gain, carrier: carrier, lane: lane });
    });

    nibbles.forEach((nibble, symbolIndex) => {
      const slotStart = startAt + (symbolIndex * SLOT_MS) / 1000;
      for (const item of oscillators) {
        const toneStart = slotStart + (item.lane * LANE_OFFSET_MS) / 1000;
        const toneEnd = toneStart + TONE_MS / 1000;
        const bit = (nibble >>> item.lane) & 1;
        item.oscillator.frequency.setValueAtTime(bit ? item.carrier.one : item.carrier.zero, toneStart);
        item.gain.gain.setValueAtTime(0, toneStart);
        item.gain.gain.linearRampToValueAtTime(level, toneStart + 0.003);
        item.gain.gain.setValueAtTime(level, toneEnd - 0.003);
        item.gain.gain.linearRampToValueAtTime(0, toneEnd);
      }
    });

    const totalMs = nibbles.length * SLOT_MS;
    const startedAt = performance.now();
    txTimer = setInterval(() => {
      if (txCancelled) return;
      const elapsed = performance.now() - startedAt;
      const progress = Math.min(100, Math.floor((elapsed / totalMs) * 100));
      setStatus("send-status", "送信中 · " + progress + "% · 相手側で受信を開始してください", "good");
    }, 250);

    await new Promise((resolve) => setTimeout(resolve, totalMs + 150));
    clearInterval(txTimer);
    txTimer = null;
    if (txCancelled) return;
    if (txContext && txContext.state !== "closed") await txContext.close();
    txContext = null;
    setTransmitEnabled(false);
    setStatus("send-status", "送信完了 · 相手側で受信できたか確認してください", "good");
  } catch (error) {
    clearInterval(txTimer);
    txTimer = null;
    if (txContext && txContext.state !== "closed") txContext.close().catch(() => {});
    txContext = null;
    setTransmitEnabled(false);
    setStatus("send-status", "音声を再生できませんでした: " + error.message, "error");
  }
}

function binPower(data, frequency, sampleRate) {
  const bin = Math.round(frequency * data.length * 2 / sampleRate);
  let max = -120;
  for (let offset = -1; offset <= 1; offset += 1) {
    const value = data[bin + offset];
    if (Number.isFinite(value) && value > max) max = value;
  }
  return max;
}

function measureSpectrum() {
  rxAnalyser.getFloatFrequencyData(rxFrequencyData);
  const sampleRate = rxContext.sampleRate;
  const values = [];
  let maxLevel = -120;
  for (const carrier of CARRIERS) {
    const zero = binPower(rxFrequencyData, carrier.zero, sampleRate);
    const one = binPower(rxFrequencyData, carrier.one, sampleRate);
    values.push(zero, one);
    maxLevel = Math.max(maxLevel, zero, one);
  }
  const meterWidth = Math.max(0, Math.min(100, ((maxLevel + 92) / 65) * 100));
  meters.forEach((meter) => { meter.style.width = meterWidth + "%"; });
  return values;
}

function decodeNibble(values, strict = false) {
  let nibble = 0;
  let confident = 0;
  for (let lane = 0; lane < 4; lane += 1) {
    const zero = values[lane * 2];
    const one = values[lane * 2 + 1];
    const difference = Math.abs(one - zero);
    const bit = one > zero ? 1 : 0;
    if (Math.max(one, zero) > -88 && difference >= (strict ? 4 : 2.5)) confident += 1;
    nibble |= bit << lane;
  }
  return { nibble: nibble, confident: confident };
}

function closestHistoryPoint(target) {
  for (let i = rxHistory.length - 1; i >= 0; i -= 1) {
    if (rxHistory[i].time <= target) {
      const before = rxHistory[i];
      const after = rxHistory[i + 1];
      if (after && Math.abs(after.time - target) < Math.abs(before.time - target)) return after;
      return before;
    }
  }
  return rxHistory[0];
}

function findPreamble(currentPoint) {
  let matches = 0;
  let confidentBits = 0;
  for (let symbol = 0; symbol < PREAMBLE.length; symbol += 1) {
    const targetTime = currentPoint.time - (PREAMBLE.length - 1 - symbol) * SLOT_MS;
    const point = closestHistoryPoint(targetTime);
    if (!point || Math.abs(point.time - targetTime) > 15) return false;
    const decoded = decodeNibble(point.values, true);
    const expected = PREAMBLE[symbol];
    for (let lane = 0; lane < 4; lane += 1) {
      const expectedBit = (expected >>> lane) & 1;
      const actualBit = (decoded.nibble >>> lane) & 1;
      if (actualBit === expectedBit) matches += 1;
      if (Math.max(point.values[lane * 2], point.values[lane * 2 + 1]) > -88 &&
          Math.abs(point.values[lane * 2 + 1] - point.values[lane * 2]) >= 4) confidentBits += 1;
    }
  }
  return matches >= 56 && confidentBits >= 52;
}

function abandonCapture(text, tone = "warn") {
  rxCapture = null;
  setStatus("receive-status", text, tone);
}

function processCapturedNibble(nibble) {
  const capture = rxCapture;
  if (!capture) return;
  if (capture.highNibble === null) {
    capture.highNibble = nibble;
  } else {
    capture.bytes.push((capture.highNibble << 4) | nibble);
    capture.highNibble = null;
  }

  if (capture.bytes.length >= HEADER_LENGTH && capture.expectedLength === null) {
    const bytes = capture.bytes;
    if (bytes[0] !== 0xa5 || bytes[1] !== 0x5a || bytes[2] !== 1 || (bytes[3] & 0xfe) !== 0) {
      abandonCapture("フレーム同期に失敗しました · 音を再検出しています");
      return;
    }
    const cipherLength = (bytes[4] << 8) | bytes[5];
    if (cipherLength > MAX_CIPHER_BYTES || cipherLength < ((bytes[3] & 1) ? 16 : 1)) {
      abandonCapture("受信サイズが範囲外です · 音を再検出しています");
      return;
    }
    capture.expectedLength = HEADER_LENGTH + SALT_LENGTH + IV_LENGTH + cipherLength + 4;
    setStatus("receive-status", "データを受信しています…", "good");
  }

  if (capture.expectedLength !== null && capture.bytes.length === capture.expectedLength) {
    const frame = new Uint8Array(capture.bytes);
    rxCapture = null;
    void finishFrame(frame);
  }
}

async function finishFrame(frame) {
  const storedCrc = readUint32be(frame, frame.length - 4);
  const actualCrc = crc32(frame.subarray(0, frame.length - 4));
  if (storedCrc !== actualCrc) {
    setStatus("receive-status", "CRC不一致 · 音の反響やノイズで破損した可能性があります", "error");
    return;
  }

  const encrypted = (frame[3] & 1) === 1;
  const header = frame.subarray(0, HEADER_LENGTH);
  const salt = frame.subarray(HEADER_LENGTH, HEADER_LENGTH + SALT_LENGTH);
  const iv = frame.subarray(HEADER_LENGTH + SALT_LENGTH, HEADER_LENGTH + SALT_LENGTH + IV_LENGTH);
  const payload = frame.subarray(HEADER_LENGTH + SALT_LENGTH + IV_LENGTH, frame.length - 4);
  let plainBytes = payload;

  if (encrypted) {
    const passphrase = passphraseInput.value;
    if (passphrase.length < 8) {
      setStatus("receive-status", "復号には送信側と同じ8文字以上の合言葉が必要です", "warn");
      return;
    }
    try {
      const key = await deriveAesKey(passphrase, salt);
      const decrypted = await crypto.subtle.decrypt(
        { name: "AES-GCM", iv: iv, additionalData: header, tagLength: 128 },
        key,
        payload,
      );
      plainBytes = new Uint8Array(decrypted);
    } catch {
      setStatus("receive-status", "復号できません · 合言葉が違うかデータが改変されています", "error");
      return;
    }
  }

  let text;
  try {
    text = decoder.decode(plainBytes);
  } catch {
    setStatus("receive-status", "UTF-8として読めません · 受信データが破損しています", "error");
    return;
  }
  addInboxMessage(text, encrypted);
  setStatus("receive-status", "メッセージを受信しました · " + plainBytes.length + " bytes", "good");
}

function addInboxMessage(text, encrypted) {
  if (inboxList.classList.contains("inbox-empty")) {
    inboxList.className = "message-list";
    inboxList.replaceChildren();
  }
  receivedCount += 1;
  clearInboxButton.disabled = false;
  const card = document.createElement("article");
  card.className = "received-card";
  const marker = document.createElement("span");
  marker.className = "received-marker";
  const content = document.createElement("div");
  content.className = "received-content";
  const meta = document.createElement("div");
  meta.className = "received-meta";
  const time = document.createElement("time");
  time.textContent = new Intl.DateTimeFormat("ja-JP", { hour: "2-digit", minute: "2-digit" }).format(new Date());
  meta.append(time);
  if (encrypted) {
    const chip = document.createElement("span");
    chip.className = "encrypted-chip";
    chip.textContent = "AES-GCM";
    meta.append(chip);
  }
  const body = document.createElement("p");
  body.className = "received-text";
  body.textContent = text;
  const copy = document.createElement("button");
  copy.type = "button";
  copy.className = "copy-message";
  copy.textContent = "コピー";
  copy.addEventListener("click", async () => {
    try {
      await navigator.clipboard.writeText(text);
      showToast("メッセージをコピーしました");
    } catch {
      showToast("クリップボードを利用できませんでした");
    }
  });
  content.append(meta, body);
  card.append(marker, content, copy);
  inboxList.prepend(card);
}

function receiveTick() {
  if (!rxContext || !rxAnalyser || rxContext.state !== "running") return;
  const point = { time: rxContext.currentTime * 1000, values: measureSpectrum() };
  rxHistory.push(point);
  const historyWindow = (PREAMBLE.length + 2) * SLOT_MS;
  while (rxHistory.length && point.time - rxHistory[0].time > historyWindow) rxHistory.shift();

  if (isSending) return;
  if (!rxCapture) {
    if (rxHistory.length > PREAMBLE.length * SLOT_MS / 8 && findPreamble(point)) {
      rxCapture = { bytes: [], highNibble: null, expectedLength: null, nextSampleAt: point.time + SLOT_MS };
      setStatus("receive-status", "信号を検出 · フレームを読み取っています…", "good");
    }
    return;
  }

  const capture = rxCapture;
  if (point.time + 5 < capture.nextSampleAt) return;
  if (point.time - capture.nextSampleAt > SLOT_MS * 0.42) {
    abandonCapture("受信タイミングが途切れました · 音を再検出しています");
    return;
  }
  const decoded = decodeNibble(point.values);
  processCapturedNibble(decoded.nibble);
  if (rxCapture) rxCapture.nextSampleAt += SLOT_MS;
}

async function startListening() {
  if (rxStream) {
    await stopListening();
    return;
  }
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    setStatus("receive-status", "このブラウザーではマイクを利用できません", "error");
    return;
  }
  if (!window.isSecureContext) {
    setStatus("receive-status", "受信にはHTTPSまたはlocalhostで開いてください", "error");
    return;
  }
  const AudioContextClass = window.AudioContext || window.webkitAudioContext;
  if (!AudioContextClass) {
    setStatus("receive-status", "このブラウザーはWeb Audioに対応していません", "error");
    return;
  }

  listenButton.disabled = true;
  setStatus("receive-status", "マイクへの接続を待っています…");
  try {
    rxStream = await navigator.mediaDevices.getUserMedia({
      audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false, channelCount: 1 },
    });
    rxContext = new AudioContextClass({ latencyHint: "interactive" });
    await rxContext.resume();
    const source = rxContext.createMediaStreamSource(rxStream);
    rxAnalyser = rxContext.createAnalyser();
    rxAnalyser.fftSize = 2048;
    rxAnalyser.smoothingTimeConstant = 0.04;
    rxAnalyser.minDecibels = -100;
    rxAnalyser.maxDecibels = -10;
    rxFrequencyData = new Float32Array(rxAnalyser.frequencyBinCount);
    source.connect(rxAnalyser);
    rxHistory = [];
    rxCapture = null;
    rxTimer = setInterval(receiveTick, 8);

    listenButton.disabled = false;
    listenButton.classList.add("listening");
    listenButton.innerHTML = '<span class="mic-symbol">Ⅱ</span><span>受信を停止</span><span class="listen-arrow">×</span>';
    el("receiver-visual").classList.add("active");
    el("receiver-state").textContent = "LISTENING · 4 CHANNELS";
    el("rx-badge").classList.add("listening");
    el("rx-badge").innerHTML = '<span class="rx-badge-dot"></span> LISTENING';
    el("mic-note").textContent = "メッセージを受け取る距離に端末を置いてください。";
    setStatus("receive-status", "マイク受信中 · プリアンブルを待っています", "good");
  } catch (error) {
    if (rxStream) rxStream.getTracks().forEach((track) => track.stop());
    rxStream = null;
    if (rxContext && rxContext.state !== "closed") await rxContext.close().catch(() => {});
    rxContext = null;
    setStatus("receive-status", "マイクを開始できません: " + error.message, "error");
    listenButton.disabled = false;
  }
}

async function stopListening() {
  clearInterval(rxTimer);
  rxTimer = null;
  if (rxStream) rxStream.getTracks().forEach((track) => track.stop());
  rxStream = null;
  if (rxContext && rxContext.state !== "closed") await rxContext.close().catch(() => {});
  rxContext = null;
  rxAnalyser = null;
  rxFrequencyData = null;
  rxHistory = [];
  rxCapture = null;
  meters.forEach((meter) => { meter.style.width = "0"; });
  listenButton.disabled = false;
  listenButton.classList.remove("listening");
  listenButton.innerHTML = '<span class="mic-symbol">◖</span><span>受信を開始</span><span class="listen-arrow">→</span>';
  el("receiver-visual").classList.remove("active");
  el("receiver-state").textContent = "MICROPHONE OFF";
  el("rx-badge").classList.remove("listening");
  el("rx-badge").innerHTML = '<span class="rx-badge-dot"></span> STANDBY';
  el("mic-note").textContent = "受信中はこのページを開いたままにしてください。";
  setStatus("receive-status", "マイクを停止しました");
}

messageInput.addEventListener("input", updateComposer);
encryptToggle.addEventListener("change", updateComposer);
passphraseInput.addEventListener("input", updateComposer);
el("volume").addEventListener("input", updateComposer);
sendButton.addEventListener("click", transmit);
stopSendButton.addEventListener("click", cancelTransmit);
listenButton.addEventListener("click", startListening);
el("show-password").addEventListener("click", () => {
  const visible = passphraseInput.type === "text";
  passphraseInput.type = visible ? "password" : "text";
  el("show-password").setAttribute("aria-label", visible ? "合言葉を表示" : "合言葉を隠す");
});
clearInboxButton.addEventListener("click", () => {
  receivedCount = 0;
  inboxList.className = "inbox-empty";
  inboxList.innerHTML = '<div class="empty-symbol" aria-hidden="true">∿</div><p>まだメッセージはありません</p><span>受信を開始すると、ここに表示されます。</span>';
  clearInboxButton.disabled = true;
});

updateComposer();



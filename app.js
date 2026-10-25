"use strict";

const MIN_SLOT_MS = 48;
const MAX_SLOT_MS = 96;
const SLOT_STEP_MS = 2;
const CONTROL_TONE_RATIO = 0.78;
const PREAMBLE = [0xd, 0x2, 0xf, 0x0, 0x9, 0x6, 0xa, 0x5, 0x3, 0xc, 0x1, 0xe, 0x4, 0xb, 0x7, 0x8];
const PROFILE_BASES = [720, 800, 880, 960, 1040];
const LANE_SPACING_HZ = 600;
const TONE_SPACING_HZ = 200;
const HEADER_LENGTH = 10;
const SALT_LENGTH = 16;
const IV_LENGTH = 12;
const MAX_CIPHER_BYTES = 528;
const MAX_TEXT_BYTES = 512;
const PBKDF2_ITERATIONS = 180000;
const HISTORY_MS = PREAMBLE.length * MAX_SLOT_MS + 250;
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
const recentMessageIds = new Map();

let rxContext = null;
let rxStream = null;
let rxAnalyser = null;
let rxTimer = null;
let rxFrequencyData = null;
let rxHistory = [];
let rxCapture = null;
let txContext = null;
let txCancelled = false;
let txProgressTimer = null;
let txDelayTimer = null;
let txWaitResolver = null;
let isSending = false;
let toastTimer = null;

const crcTable = new Uint32Array(256);
for (let n = 0; n < 256; n += 1) {
  let c = n;
  for (let k = 0; k < 8; k += 1) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
  crcTable[n] = c >>> 0;
}

function carriersForProfile(profile) {
  const base = PROFILE_BASES[profile] ?? PROFILE_BASES[2];
  return Array.from({ length: 4 }, (_, lane) => {
    const zero = base + lane * LANE_SPACING_HZ;
    return { zero: zero, one: zero + TONE_SPACING_HZ };
  });
}

const FREQUENCY_PROFILES = PROFILE_BASES.map((_, index) => carriersForProfile(index));

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

function getTxConfig() {
  const slotMs = Number(el("symbol-ms").value);
  const profile = Number(el("frequency-profile").value);
  const requestedToneMs = Math.round(slotMs * Number(el("tone-ratio").value) / 100);
  const staggerMs = Number(el("lane-offset").value);
  const toneMs = Math.max(20, Math.min(requestedToneMs, slotMs - 3 * staggerMs - 5));
  const repeatLimit = Number(el("repeat-count").value);
  return {
    slotMs: slotMs,
    profile: profile,
    toneMs: toneMs,
    toneRatio: Number(el("tone-ratio").value),
    staggerMs: staggerMs,
    waveform: el("waveform").value,
    volume: Number(el("volume").value),
    laneGains: [0, 1, 2, 3].map((lane) => Number(el("lane-gain-" + lane).value) / 100),
    attackMs: Number(el("attack-ms").value),
    releaseMs: Number(el("release-ms").value),
    leadDelayMs: Number(el("lead-delay").value),
    looping: el("loop-toggle").checked,
    repeatLimit: repeatLimit === 0 ? Infinity : repeatLimit,
    repeatGapMs: Number(el("repeat-gap").value),
    maxDurationMs: Number(el("max-loop-ms").value),
    clearAfterSend: el("clear-after-send").checked,
    gapJitterMs: Number(el("gap-jitter").value),
    pan: Number(el("pan").value) / 100,
  };
}

function updateFrequencyLabels(profile) {
  const carriers = FREQUENCY_PROFILES[profile] || FREQUENCY_PROFILES[2];
  carriers.forEach((carrier, lane) => {
    const label = document.querySelector('[data-frequency-lane="' + lane + '"]');
    if (label) label.textContent = carrier.zero + " / " + carrier.one;
  });
}

function updateSettingReadouts(config) {
  el("symbol-ms-value").textContent = config.slotMs + " ms";
  el("tone-ratio-value").textContent = config.toneRatio + "%";
  el("lane-offset-value").textContent = config.staggerMs + " ms";
  el("volume-value").textContent = String(Math.round(config.volume * 100)).padStart(2, "0");
  el("attack-ms-value").textContent = config.attackMs + " ms";
  el("release-ms-value").textContent = config.releaseMs + " ms";
  el("lead-delay-value").textContent = config.leadDelayMs + " ms";
  el("repeat-gap-value").textContent = config.repeatGapMs + " ms";
  el("gap-jitter-value").textContent = config.gapJitterMs + " ms";
  el("pan-value").textContent = config.pan === 0 ? "中央" : (config.pan < 0 ? "左 " : "右 ") + Math.abs(Math.round(config.pan * 100)) + "%";
  config.laneGains.forEach((gain, lane) => {
    el("lane-gain-" + lane + "-value").textContent = Math.round(gain * 100) + "%";
  });
  el("send-speed-label").textContent = config.slotMs + " ms / symbol";
  updateFrequencyLabels(config.profile);
}

function updateComposer() {
  const bytes = encoder.encode(messageInput.value);
  const encrypted = encryptToggle.checked;
  const config = getTxConfig();
  updateSettingReadouts(config);
  const cipherLength = bytes.length + (encrypted ? 16 : 0);
  const frameLength = HEADER_LENGTH + SALT_LENGTH + IV_LENGTH + cipherLength + 4;
  const passSymbols = PREAMBLE.length + frameLength * 2;
  const passSeconds = passSymbols * config.slotMs / 1000;
  const repeatCount = config.looping ? config.repeatLimit : 1;
  const estimatedSeconds = Number.isFinite(repeatCount)
    ? passSeconds * repeatCount + Math.max(0, repeatCount - 1) * config.repeatGapMs / 1000
    : Infinity;
  const totalSeconds = config.looping && config.maxDurationMs > 0
    ? Math.min(estimatedSeconds, config.maxDurationMs / 1000)
    : estimatedSeconds;

  el("byte-count").textContent = bytes.length + " bytes";
  el("time-estimate").textContent = Number.isFinite(totalSeconds)
    ? "約 " + formatDuration(totalSeconds)
    : "1回 約 " + formatDuration(passSeconds) + " · ∞";
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
    setStatus("send-status", "準備完了 · 受信側は速度と周波数を自動判定", "good");
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
  const messageId = crypto.getRandomValues(new Uint8Array(4));
  const cipherLength = plainBytes.length + (encrypted ? 16 : 0);
  if (cipherLength > MAX_CIPHER_BYTES) throw new Error("送信できるメッセージの上限を超えました。");

  const header = new Uint8Array([0xa5, 0x5a, 2, encrypted ? 1 : 0, ...uint16be(cipherLength), ...messageId]);
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
  const wasSending = isSending;
  isSending = enabled;
  sendButton.disabled = enabled;
  stopSendButton.hidden = !enabled;
  if (wasSending && !enabled && rxContext) {
    rxHistory = [];
    rxCapture = null;
  }
  updateComposer();
}

function cancelTransmit() {
  if (!isSending) return;
  txCancelled = true;
  clearInterval(txProgressTimer);
  txProgressTimer = null;
  if (txDelayTimer !== null) clearTimeout(txDelayTimer);
  txDelayTimer = null;
  if (txWaitResolver) txWaitResolver();
  txWaitResolver = null;
  if (txContext && txContext.state !== "closed") txContext.close().catch(() => {});
  txContext = null;
  setTransmitEnabled(false);
  setStatus("send-status", "送信を停止しました", "warn");
}

function cancellableDelay(ms) {
  return new Promise((resolve) => {
    let settled = false;
    const finish = () => {
      if (settled) return;
      settled = true;
      clearTimeout(txDelayTimer);
      txDelayTimer = null;
      txWaitResolver = null;
      resolve();
    };
    txWaitResolver = finish;
    txDelayTimer = setTimeout(finish, Math.max(0, ms));
  });
}

function scheduleFrame(context, nibbles, config, graph, startAt) {
  const oscillators = [];
  const carriers = FREQUENCY_PROFILES[config.profile];
  const durationSec = nibbles.length * config.slotMs / 1000;

  carriers.forEach((carrier, lane) => {
    const oscillator = context.createOscillator();
    const gain = context.createGain();
    oscillator.type = config.waveform;
    gain.gain.value = 0;
    oscillator.connect(gain);
    gain.connect(graph.input);
    oscillator.start(startAt);
    oscillator.stop(startAt + durationSec + 0.12);
    oscillators.push({ oscillator: oscillator, gain: gain, carrier: carrier, lane: lane });
  });

  nibbles.forEach((nibble, symbolIndex) => {
    const slotStart = startAt + (symbolIndex * config.slotMs) / 1000;
    for (const item of oscillators) {
      const toneStart = slotStart + (item.lane * config.staggerMs) / 1000;
      const toneEnd = toneStart + config.toneMs / 1000;
      const amplitude = Math.min(0.28, config.volume * config.laneGains[item.lane]);
      const bit = (nibble >>> item.lane) & 1;
      const attack = Math.min(config.attackMs / 1000, (toneEnd - toneStart) / 3);
      const release = Math.min(config.releaseMs / 1000, (toneEnd - toneStart) / 3);
      item.oscillator.frequency.setValueAtTime(bit ? item.carrier.one : item.carrier.zero, toneStart);
      item.gain.gain.setValueAtTime(0, toneStart);
      if (attack > 0) item.gain.gain.linearRampToValueAtTime(amplitude, toneStart + attack);
      else item.gain.gain.setValueAtTime(amplitude, toneStart);
      if (release > 0) {
        item.gain.gain.setValueAtTime(amplitude, toneEnd - release);
        item.gain.gain.linearRampToValueAtTime(0, toneEnd);
      } else {
        item.gain.gain.setValueAtTime(0, toneEnd);
      }
    }
  });

  return durationSec * 1000;
}

function createOutputGraph(context, config) {
  const input = context.createGain();
  input.gain.value = 1;
  let output = input;
  if (context.createStereoPanner) {
    const panner = context.createStereoPanner();
    panner.pan.value = config.pan;
    input.connect(panner);
    output = panner;
  }
  output.connect(context.destination);
  return { input: input };
}

async function transmit() {
  const plainBytes = encoder.encode(messageInput.value);
  const encrypted = encryptToggle.checked;
  const passphrase = passphraseInput.value;
  const config = getTxConfig();
  if (plainBytes.length === 0 || plainBytes.length > MAX_TEXT_BYTES) return;
  if (encrypted && passphrase.length < 8) {
    setStatus("send-status", "8文字以上の合言葉を入力してください", "warn");
    passphraseInput.focus();
    return;
  }
  if (!window.isSecureContext || !window.crypto || !crypto.subtle) {
    setStatus("send-status", "暗号化にはHTTPSまたはlocalhostで開いてください", "error");
    return;
  }

  setTransmitEnabled(true);
  txCancelled = false;
  setStatus("send-status", encrypted ? "暗号鍵を準備しています…" : "送信データを準備しています…");
  let nibbles;
  try {
    nibbles = frameToNibbles(await buildFrame(plainBytes, encrypted, passphrase));
  } catch (error) {
    setTransmitEnabled(false);
    setStatus("send-status", "準備できませんでした: " + error.message, "error");
    return;
  }
  if (txCancelled) {
    setTransmitEnabled(false);
    return;
  }

  const AudioContextClass = window.AudioContext || window.webkitAudioContext;
  if (!AudioContextClass) {
    setTransmitEnabled(false);
    setStatus("send-status", "このブラウザーはWeb Audioに対応していません", "error");
    return;
  }

  try {
    txContext = new AudioContextClass({ latencyHint: "interactive" });
    await txContext.resume();
    const graph = createOutputGraph(txContext, config);
    const frameMs = nibbles.length * config.slotMs;
    const repeats = config.looping ? config.repeatLimit : 1;
    const infinite = !Number.isFinite(repeats);
    let pass = 0;
    const stopAt = config.looping && config.maxDurationMs > 0
      ? performance.now() + config.maxDurationMs
      : Infinity;

    txProgressTimer = setInterval(() => {
      if (txCancelled) return;
      const label = infinite ? "送信回 " + (pass + 1) + " / ∞" : "送信回 " + (pass + 1) + " / " + repeats;
      setStatus("send-status", "連続ループ中 · " + label + " · 相手側で受信を開始してください", "good");
    }, 300);

    while (!txCancelled && pass < repeats && (pass === 0 || performance.now() < stopAt)) {
      const delayMs = pass === 0 ? config.leadDelayMs : 0;
      const startAt = txContext.currentTime + (delayMs + 100) / 1000;
      const scheduledMs = scheduleFrame(txContext, nibbles, config, graph, startAt);
      await cancellableDelay(scheduledMs + delayMs + 150);
      if (txCancelled) break;
      pass += 1;
      if (pass < repeats) {
        const jitter = config.gapJitterMs ? (Math.random() * 2 - 1) * config.gapJitterMs : 0;
        await cancellableDelay(Math.max(0, config.repeatGapMs + jitter));
      }
    }

    clearInterval(txProgressTimer);
    txProgressTimer = null;
    if (txContext && txContext.state !== "closed") await txContext.close();
    txContext = null;
    if (!txCancelled) {
      setTransmitEnabled(false);
      setStatus("send-status", "送信完了 · " + pass + " 回再生 · 受信側で到着を確認してください", "good");
      if (config.clearAfterSend) {
        messageInput.value = "";
        updateComposer();
      }
    }
  } catch (error) {
    clearInterval(txProgressTimer);
    txProgressTimer = null;
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

function measureProfileSpectrum(data, profile, sampleRate) {
  const values = [];
  for (const carrier of FREQUENCY_PROFILES[profile]) {
    values.push(binPower(data, carrier.zero, sampleRate), binPower(data, carrier.one, sampleRate));
  }
  return values;
}

function measureSpectra() {
  rxAnalyser.getFloatFrequencyData(rxFrequencyData);
  const profiles = FREQUENCY_PROFILES.map((_, profile) => measureProfileSpectrum(rxFrequencyData, profile, rxContext.sampleRate));
  meters.forEach((meter, lane) => {
    let level = -120;
    for (const values of profiles) level = Math.max(level, values[lane * 2], values[lane * 2 + 1]);
    const width = Math.max(0, Math.min(100, ((level + 92) / 65) * 100));
    meter.style.width = width + "%";
  });
  return profiles;
}

function decodeNibble(values, strict = false) {
  let nibble = 0;
  let confident = 0;
  let strength = 0;
  for (let lane = 0; lane < 4; lane += 1) {
    const zero = values[lane * 2];
    const one = values[lane * 2 + 1];
    const difference = Math.abs(one - zero);
    const bit = one > zero ? 1 : 0;
    const signal = Math.max(one, zero);
    if (signal > -88 && difference >= (strict ? 4 : 2.5)) confident += 1;
    strength += Math.min(24, difference);
    nibble |= bit << lane;
  }
  return { nibble: nibble, confident: confident, strength: strength };
}

function closestHistoryPoint(target) {
  let low = 0;
  let high = rxHistory.length - 1;
  while (low <= high) {
    const middle = (low + high) >> 1;
    if (rxHistory[middle].time < target) low = middle + 1;
    else high = middle - 1;
  }
  const after = rxHistory[Math.min(rxHistory.length - 1, low)];
  const before = rxHistory[Math.max(0, low - 1)];
  return Math.abs(after.time - target) < Math.abs(before.time - target) ? after : before;
}

function scorePreamble(point, profile, slotMs) {
  if (rxHistory.length === 0 || point.time - rxHistory[0].time < (PREAMBLE.length - 1) * slotMs) return null;
  let matches = 0;
  let confidentBits = 0;
  let strength = 0;
  for (let symbol = 0; symbol < PREAMBLE.length; symbol += 1) {
    const targetTime = point.time - (PREAMBLE.length - 1 - symbol) * slotMs;
    const sample = closestHistoryPoint(targetTime);
    if (!sample || Math.abs(sample.time - targetTime) > 9) return null;
    const decoded = decodeNibble(sample.profiles[profile], true);
    const expected = PREAMBLE[symbol];
    for (let lane = 0; lane < 4; lane += 1) {
      if (((decoded.nibble >>> lane) & 1) === ((expected >>> lane) & 1)) matches += 1;
    }
    confidentBits += decoded.confident;
    strength += decoded.strength;
  }
  if (matches >= 56 && confidentBits >= 52) return { profile: profile, slotMs: slotMs, score: strength };
  return null;
}

function findPreamble(point) {
  let best = null;
  for (let profile = 0; profile < FREQUENCY_PROFILES.length; profile += 1) {
    for (let slotMs = MIN_SLOT_MS; slotMs <= MAX_SLOT_MS; slotMs += SLOT_STEP_MS) {
      const score = scorePreamble(point, profile, slotMs);
      if (score && (!best || score.score > best.score)) best = score;
    }
  }
  return best;
}

function abandonCapture(text, tone = "warn") {
  rxCapture = null;
  setStatus("receive-status", text, tone);
}

function bitCount(value) {
  let count = 0;
  while (value) {
    count += value & 1;
    value >>>= 1;
  }
  return count;
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
    const fixedHeader = [0xa5, 0x5a, 2];
    for (let index = 0; index < fixedHeader.length; index += 1) {
      if (bitCount(bytes[index] ^ fixedHeader[index]) > 1) {
        abandonCapture("フレーム同期に失敗 · 音量と距離を調整して再送してください");
        return;
      }
      bytes[index] = fixedHeader[index];
    }
    if (bitCount(bytes[3] & 0xfe) > 1) {
      abandonCapture("フレーム同期に失敗 · 音量と距離を調整して再送してください");
      return;
    }
    bytes[3] &= 0x01;
    const cipherLength = (bytes[4] << 8) | bytes[5];
    if (cipherLength > MAX_CIPHER_BYTES || cipherLength < ((bytes[3] & 1) ? 16 : 1)) {
      abandonCapture("受信サイズが範囲外です · 音を再検出しています");
      return;
    }
    capture.expectedLength = HEADER_LENGTH + SALT_LENGTH + IV_LENGTH + cipherLength + 4;
    setStatus("receive-status", "データを受信しています · " + capture.slotMs + " ms · CH " + String(capture.profile + 1).padStart(2, "0"), "good");
  }

  if (capture.expectedLength !== null && capture.bytes.length === capture.expectedLength) {
    const frame = new Uint8Array(capture.bytes);
    rxCapture = null;
    void finishFrame(frame);
  }
}

function frameMessageId(frame) {
  return Array.from(frame.subarray(6, 10)).map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

async function finishFrame(frame) {
  const storedCrc = readUint32be(frame, frame.length - 4);
  const actualCrc = crc32(frame.subarray(0, frame.length - 4));
  if (storedCrc !== actualCrc) {
    setStatus("receive-status", "CRC不一致 · 音の反響やノイズで破損した可能性があります", "error");
    return;
  }

  const messageId = frameMessageId(frame);
  const priorTime = recentMessageIds.get(messageId);
  if (priorTime && Date.now() - priorTime < 30 * 60 * 1000) {
    setStatus("receive-status", "ループ再送を受信 · 重複表示をスキップしました", "good");
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
  recentMessageIds.set(messageId, Date.now());
  for (const [id, time] of recentMessageIds) {
    if (Date.now() - time > 30 * 60 * 1000) recentMessageIds.delete(id);
  }
  addInboxMessage(text, encrypted);
  setStatus("receive-status", "メッセージを受信しました · " + plainBytes.length + " bytes", "good");
}

function addInboxMessage(text, encrypted) {
  if (inboxList.classList.contains("inbox-empty")) {
    inboxList.className = "message-list";
    inboxList.replaceChildren();
  }
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

function pollReceiver() {
  if (!rxContext) {
    rxTimer = null;
    return;
  }
  receiveTick();
  rxTimer = setTimeout(pollReceiver, 8 + Math.random() * 4);
}

function receiveTick() {
  if (!rxContext || !rxAnalyser || rxContext.state !== "running") return;
  const point = { time: rxContext.currentTime * 1000, profiles: measureSpectra() };
  rxHistory.push(point);
  while (rxHistory.length && point.time - rxHistory[0].time > HISTORY_MS) rxHistory.shift();

  if (isSending) return;
  if (!rxCapture) {
    const match = findPreamble(point);
    if (match) {
      rxCapture = {
        bytes: [],
        highNibble: null,
        expectedLength: null,
        profile: match.profile,
        slotMs: match.slotMs,
        nextSampleAt: point.time + match.slotMs,
      };
      setStatus("receive-status", "信号を検出 · " + match.slotMs + " ms / CH " + String(match.profile + 1).padStart(2, "0"), "good");
    }
    return;
  }

  const capture = rxCapture;
  if (point.time + 5 < capture.nextSampleAt) return;
  if (point.time - capture.nextSampleAt > capture.slotMs * 0.42) {
    abandonCapture("受信タイミングが途切れました · 音を再検出しています");
    return;
  }
  const decoded = decodeNibble(point.profiles[capture.profile]);
  processCapturedNibble(decoded.nibble);
  if (rxCapture) rxCapture.nextSampleAt += capture.slotMs;
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
    rxAnalyser.fftSize = 1024;
    rxAnalyser.smoothingTimeConstant = 0.02;
    rxAnalyser.minDecibels = -100;
    rxAnalyser.maxDecibels = -10;
    rxFrequencyData = new Float32Array(rxAnalyser.frequencyBinCount);
    source.connect(rxAnalyser);
    rxHistory = [];
    rxCapture = null;
    rxTimer = setTimeout(pollReceiver, 0);

    listenButton.disabled = false;
    listenButton.classList.add("listening");
    listenButton.innerHTML = '<span class="mic-symbol">Ⅱ</span><span>受信を停止</span><span class="listen-arrow">×</span>';
    el("receiver-visual").classList.add("active");
    el("receiver-state").textContent = "AUTO SYNC · 5 BANDS";
    el("rx-badge").classList.add("listening");
    el("rx-badge").innerHTML = '<span class="rx-badge-dot"></span> LISTENING';
    el("mic-note").textContent = "送信側の速度と周波数を自動で合わせます。";
    setStatus("receive-status", "マイク受信中 · 速度・周波数の同期信号を待っています", "good");
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
  clearTimeout(rxTimer);
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
  el("mic-note").textContent = "速度と周波数バンクは自動判定。ページを開いたままにしてください。";
  setStatus("receive-status", "マイクを停止しました");
}

messageInput.addEventListener("input", updateComposer);
encryptToggle.addEventListener("change", updateComposer);
passphraseInput.addEventListener("input", updateComposer);
el("send-button").addEventListener("click", transmit);
el("stop-send").addEventListener("click", cancelTransmit);
el("listen-button").addEventListener("click", startListening);
el("show-password").addEventListener("click", () => {
  const visible = passphraseInput.type === "text";
  passphraseInput.type = visible ? "password" : "text";
  el("show-password").setAttribute("aria-label", visible ? "合言葉を表示" : "合言葉を隠す");
});
clearInboxButton.addEventListener("click", () => {
  inboxList.className = "inbox-empty";
  inboxList.innerHTML = '<div class="empty-symbol" aria-hidden="true">∿</div><p>まだメッセージはありません</p><span>受信を開始すると、ここに表示されます。</span>';
  clearInboxButton.disabled = true;
});
document.querySelectorAll("#custom-settings input, #custom-settings select, #volume").forEach((control) => {
  control.addEventListener("input", updateComposer);
  control.addEventListener("change", updateComposer);
});
el("repeat-count").addEventListener("change", updateComposer);

updateComposer();








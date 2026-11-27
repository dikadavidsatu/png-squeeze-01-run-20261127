// png-squeeze: lossless PNG re-encoder that squeezes screenshots into the
// smallest valid PNG it can. Written from scratch.
//
// Pipeline per image:
//   1. Decode the stored RGBA PNG (own decoder, all colour types, bit depth 8).
//   2. Analyse: opaque? grey? <=256 distinct colours? a single transparent
//      value that a tRNS key can express?
//   3. Build candidate lossless forms (palette count/luminance order;
//      grey / grey+alpha / RGB / RGBA with a tRNS key when applicable) and
//      filter each with several per-row strategies (fixed 0, minsum, pairs,
//      brute-force per-row deflate cost for grey).
//   4. Screen every candidate with zlib level 6 (fast, C) and keep the best.
//   5. Compress the winner with our own optimal-parsing DEFLATE (hash-chain
//      LZ77, dynamic-programming optimal parse, iterative Huffman refinement,
//      per-block dynamic/fixed Huffman choice), falling back to zlib level 9
//      if that is ever smaller. Deterministic: no clock, no randomness, no
//      environment-dependent choices anywhere in the output path.
//   6. Write a minimal valid PNG: IHDR / PLTE / tRNS / IDAT / IEND only,
//      bit depth 8, non-interlaced, one zlib stream in IDAT.
//
// Node 22 stdlib only. Fully synchronous; exits 0.
import { deflateSync, inflateSync, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// ---------- CRC-32 (PNG) ----------
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
    t[n] = c;
  }
  return t;
})();
function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

const SIG = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CH = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

function chunkBytes(type, data) {
  const out = new Uint8Array(12 + data.length);
  const v = new DataView(out.buffer);
  v.setUint32(0, data.length);
  out.set([type.charCodeAt(0), type.charCodeAt(1), type.charCodeAt(2), type.charCodeAt(3)], 4);
  out.set(data, 8);
  v.setUint32(8 + data.length, crc32(out, 4, 8 + data.length));
  return out;
}
function ihdr(width, height, colourType) {
  const d = new Uint8Array(13);
  const dv = new DataView(d.buffer);
  dv.setUint32(0, width);
  dv.setUint32(4, height);
  d[8] = 8; d[9] = colourType;
  return d;
}
function pngOf(chunks) {
  let size = 8;
  for (const c of chunks) size += c.length;
  const out = new Uint8Array(size);
  out.set(SIG, 0);
  let at = 8;
  for (const c of chunks) { out.set(c, at); at += c.length; }
  return out;
}

// ---------- PNG decoder (bit depth 8, colour types 0/2/3/4/6) ----------
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

function decodePng(bytes) {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null, palette = null, trns = null;
  const idat = [];
  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), colourType: data[9] };
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  const { width, height, colourType } = header;
  const bpp = CH[colourType];
  const stride = width * bpp;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride, p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    else if (ft === 2) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    else if (ft === 3) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    else for (let i = 0; i < stride; i++) {
      const a = i >= bpp ? samples[o + i - bpp] : 0;
      const b = y > 0 ? samples[p + i] : 0;
      const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
      samples[o + i] = raw[src + i] + paeth(a, b, c);
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const lut = new Uint8Array(palette.length / 3 * 4);
    for (let e = 0; e < palette.length / 3; e++) {
      lut[e * 4] = palette[e * 3]; lut[e * 4 + 1] = palette[e * 3 + 1]; lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i] * 4;
      rgba[d] = lut[e]; rgba[d + 1] = lut[e + 1]; rgba[d + 2] = lut[e + 2]; rgba[d + 3] = lut[e + 3];
    }
  }
  return { width, height, rgba };
}

// ---------- analysis ----------
function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  let opaque = true, grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [...counts.keys()].map((c) => {
      const b = new Uint8Array(Uint32Array.of(c).buffer);
      return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
    });
  }
  return { opaque, grey, colours };
}

// The one transparent value (grey or RGB) keyable by tRNS: every
// non-opaque pixel is exactly that value at alpha 0, and no opaque
// pixel uses that value. Null otherwise.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

// ---------- palette ----------
function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  const entries = [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0]; plte[i * 3 + 1] = c.rgba[1]; plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}

// ---------- filtering ----------
function filterRowInto(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  else if (type === 2) for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  else if (type === 3) for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  else for (let i = 0; i < n; i++) {
    const a = i >= bpp ? cur[i - bpp] : 0;
    const b = prev === null ? 0 : prev[i];
    const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
    out[i] = cur[i] - paeth(a, b, c);
  }
}
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) { const v = row[i]; s += v < 128 ? v : 256 - v; }
  return s;
}

// Filter a whole image's samples by `choice`:
// a fixed type 0-4, 'minsum', 'pairs' or 'brute' (per-row real
// deflate cost at level 4 with the previous 32 KiB as dictionary).
function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = [];
  for (let t = 0; t < 5; t++) trial.push(new Uint8Array(stride));
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRowInto(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    let type = 0, best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRowInto(t, cur, prev, bpp, trial[t]);
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t]);
      else if (choice === 'pairs') {
        let n = 0;
        const row = trial[t];
        const st = ++stamp;
        for (let i = 1; i < row.length; i++) {
          const pair = (row[i - 1] << 8) | row[i];
          if (seen[pair] !== st) { seen[pair] = st; n++; }
        }
        cost = n;
      } else {
        // brute: real deflate cost of this row, context = previous 32 KiB
        const rowBuf = new Uint8Array(stride + 1);
        rowBuf[0] = t;
        rowBuf.set(trial[t], 1);
        const before = raw.subarray(Math.max(0, at - 32768), at);
        cost = before.length === 0
          ? deflateSync(rowBuf, { level: 4, memLevel: 8 }).length
          : deflateSync(rowBuf, { level: 4, memLevel: 8, dictionary: before }).length;
      }
      if (cost < best) { best = cost; type = t; }
    }
    raw[at] = type;
    raw.set(trial[type], at + 1);
  }
  return raw;
}

// ---------- own DEFLATE (zlib stream out) ----------
// LZ77 hash-chain matcher, optimal-parsing DP over the token stream,
// iterative Huffman refinement, input split into blocks so each block
// gets its own Huffman tables. Deterministic: fixed effort, no clock.
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LEN_SYM = new Uint16Array(259);
const LEN_SYM_EXTRA = new Uint8Array(259);
for (let s = 0; s < 29; s++) {
  for (let l = LEN_BASE[s]; l < (s === 28 ? 259 : LEN_BASE[s + 1]); l++) {
    LEN_SYM[l] = 257 + s;
    LEN_SYM_EXTRA[l] = l - LEN_BASE[s];
  }
}
LEN_SYM[258] = 285; LEN_SYM_EXTRA[258] = 0;
const DIST_SYM_OF = new Uint8Array(32769);
const DIST_SYM_EXTRA = new Uint16Array(32769);
const DIST_EXTRA_OF_DIST = new Uint8Array(32769);
for (let d = 1; d <= 32768; d++) {
  let s = 0;
  while (s < 29 && DIST_BASE[s + 1] <= d) s++;
  DIST_SYM_OF[d] = s;
  DIST_SYM_EXTRA[d] = d - DIST_BASE[s];
  DIST_EXTRA_OF_DIST[d] = DIST_EXTRA[s];
}
const LEN_EXTRA_OF_LEN = new Uint8Array(259);
for (let l = 3; l <= 258; l++) LEN_EXTRA_OF_LEN[l] = LEN_EXTRA[LEN_SYM[l] - 257];
const FIXED_LIT_LEN = new Uint8Array(288);
for (let i = 0; i < 144; i++) FIXED_LIT_LEN[i] = 8;
for (let i = 144; i < 256; i++) FIXED_LIT_LEN[i] = 9;
for (let i = 256; i < 280; i++) FIXED_LIT_LEN[i] = 7;
for (let i = 280; i < 288; i++) FIXED_LIT_LEN[i] = 8;
const FIXED_DIST_LEN = new Uint8Array(30).fill(5);

class BitWriter {
  constructor(cap) {
    this.buf = new Uint8Array(cap);
    this.at = 0;
    this.bitBuf = 0;
    this.bitCnt = 0;
  }
  grow(need) {
    if (this.at + need + 8 > this.buf.length) {
      const nb = new Uint8Array(Math.max(this.buf.length * 2, this.at + need + 1024));
      nb.set(this.buf.subarray(0, this.at));
      this.buf = nb;
    }
  }
  writeBits(code, len) {
    this.bitBuf |= code << this.bitCnt;
    this.bitCnt += len;
    while (this.bitCnt >= 8) {
      this.grow(1);
      this.buf[this.at++] = this.bitBuf & 0xff;
      this.bitBuf >>>= 8;
      this.bitCnt -= 8;
    }
  }
  writeCode(code, len) {
    let r = 0;
    for (let i = 0; i < len; i++) r = (r << 1) | ((code >> i) & 1);
    this.writeBits(r, len);
  }
  alignByte() {
    if (this.bitCnt > 0) {
      this.grow(1);
      this.buf[this.at++] = this.bitBuf & 0xff;
      this.bitBuf = 0; this.bitCnt = 0;
    }
  }
  bytes() { return this.buf.subarray(0, this.at); }
}

function huffmanLengths(freqs, maxBits) {
  const n = freqs.length;
  const lens = new Uint8Array(n);
  const used = [];
  for (let i = 0; i < n; i++) if (freqs[i] > 0) used.push(i);
  if (used.length === 0) return lens;
  if (used.length === 1) { lens[used[0]] = 1; return lens; }
  const nodes = used.map((s) => ({ freq: freqs[s], left: -1, right: -1, sym: s }));
  const alive = nodes.map((_, i) => i);
  while (alive.length > 1) {
    let ai = 0, bi = 1;
    if (nodes[alive[bi]].freq < nodes[alive[ai]].freq) { const t = ai; ai = bi; bi = t; }
    for (let i = 2; i < alive.length; i++) {
      if (nodes[alive[i]].freq < nodes[alive[ai]].freq) { bi = ai; ai = i; }
      else if (nodes[alive[i]].freq < nodes[alive[bi]].freq) bi = i;
    }
    const x = alive[ai], y = alive[bi];
    alive.splice(Math.max(ai, bi), 1);
    alive.splice(Math.min(ai, bi), 1);
    nodes.push({ freq: nodes[x].freq + nodes[y].freq, left: x, right: y, sym: -1 });
    alive.push(nodes.length - 1);
  }
  const depths = new Uint8Array(n);
  (function walk(idx, d) {
    const nd = nodes[idx];
    if (nd.sym >= 0) { depths[nd.sym] = d; return; }
    walk(nd.left, d + 1);
    walk(nd.right, d + 1);
  })(alive[0], 0);
  const blCount = new Int32Array(maxBits + 1);
  let overflow = 0;
  for (const s of used) {
    const d = depths[s];
    if (d > maxBits) { overflow++; blCount[maxBits]++; }
    else blCount[d]++;
  }
  if (overflow > 0) {
    do {
      let bits = maxBits - 1;
      while (blCount[bits] === 0) bits--;
      blCount[bits]--;
      blCount[bits + 1] += 2;
      blCount[maxBits]--;
      overflow -= 2;
    } while (overflow > 0);
    const order = used.slice().sort((a, b) => freqs[b] - freqs[a] || a - b);
    let k = 0;
    for (let b = 1; b <= maxBits; b++) {
      for (let j = 0; j < blCount[b]; j++) lens[order[k++]] = b;
    }
  } else {
    for (const s of used) lens[s] = depths[s];
  }
  return lens;
}

function buildCodes(lengths) {
  const n = lengths.length;
  const blCount = new Int32Array(16);
  for (let i = 0; i < n; i++) blCount[lengths[i]]++;
  blCount[0] = 0;
  const nextCode = new Int32Array(16);
  let code = 0;
  for (let b = 1; b <= 15; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  const codes = new Uint32Array(n);
  for (let i = 0; i < n; i++) {
    const l = lengths[i];
    if (l !== 0) codes[i] = nextCode[l]++;
  }
  return { codes, lens: lengths };
}

function adler32(data) {
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

class Matcher {
  constructor(data) {
    this.d = data;
    this.n = data.length;
    this.head = new Int32Array(32768).fill(-1);
    this.prev = new Int32Array(32768).fill(-1);
  }
  hashAt(i) {
    const d = this.d;
    return ((d[i] << 10) ^ (d[i + 1] << 5) ^ d[i + 2]) & 0x7fff;
  }
  insert(i) {
    const h = this.hashAt(i);
    this.prev[i & 0x7fff] = this.head[h];
    this.head[h] = i;
  }
  find(pos, maxChain, maxLen, out) {
    const d = this.d, n = this.n;
    const limit = pos - 32768 > 0 ? pos - 32768 : 0;
    let cur = this.head[this.hashAt(pos)];
    let best = 2;
    let cnt = 0;
    let minDist3 = 0;
    let chain = 0;
    const maxPossible = Math.min(maxLen, n - pos);
    while (cur >= limit && cur !== -1 && chain < maxChain) {
      chain++;
      if (best < maxPossible && d[cur + best] !== d[pos + best]) {
        cur = this.prev[cur & 0x7fff];
        continue;
      }
      let len = 0;
      while (len < maxPossible && d[cur + len] === d[pos + len]) len++;
      if (len >= 3) {
        const dist = pos - cur;
        if (minDist3 === 0) minDist3 = dist;
        if (len > best && cnt < 16) {
          out[cnt++] = (dist << 9) | len;
          best = len;
          if (len >= maxPossible) break;
        }
      }
      cur = this.prev[cur & 0x7fff];
    }
    if (minDist3 !== 0 && (cnt === 0 || (out[0] & 511) !== 3)) {
      for (let i = cnt; i > 0; i--) out[i] = out[i - 1];
      out[0] = (minDist3 << 9) | 3;
      cnt++;
    }
    return cnt;
  }
}

const MAX_CAND = 16;

function computeCandidates(matcher, data, base, len, maxChain) {
  const off = new Int32Array(len + 1);
  const packed = new Int32Array(len * MAX_CAND);
  const cand = new Int32Array(24);
  let total = 0;
  for (let i = 0; i < len; i++) {
    off[i] = total;
    const pos = base + i;
    if (pos + 2 < data.length && i + 3 <= len) {
      const cnt = matcher.find(pos, maxChain, 258, cand);
      for (let k = 0; k < cnt; k++) packed[total++] = cand[k];
    }
    if (pos + 2 < data.length) matcher.insert(pos);
  }
  off[len] = total;
  return { off, packed: packed.subarray(0, total) };
}

const LEN_BOUNDS = [3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 22, 26, 30, 34, 42, 50, 58, 66, 82, 98, 114, 130, 162, 194, 226, 257, 258];
function dpParse(data, base, len, cand, litLen, distLen, rich = false) {
  const cost = new Float64Array(len + 1);
  const prevPos = new Int32Array(len + 1);
  const tokLen = new Int16Array(len + 1);
  const tokDist = new Int32Array(len + 1);
  for (let i = 0; i <= len; i++) cost[i] = Infinity;
  cost[0] = 0;
  const litCost = new Float64Array(288);
  for (let s = 0; s < 288; s++) litCost[s] = litLen[s] > 0 ? litLen[s] : FIXED_LIT_LEN[s];
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litCost[LEN_SYM[l]] + LEN_EXTRA_OF_LEN[l];
  const distCost = new Float64Array(32769);
  for (let dd = 1; dd <= 32768; dd++) {
    const ds = DIST_SYM_OF[dd];
    distCost[dd] = (distLen[ds] > 0 ? distLen[ds] : FIXED_DIST_LEN[ds]) + DIST_EXTRA_OF_DIST[dd];
  }
  for (let i = 0; i < len; i++) {
    const ci = cost[i];
    if (ci === Infinity) continue;
    const pos = base + i;
    const lc = ci + litCost[data[pos]];
    if (lc < cost[i + 1]) {
      cost[i + 1] = lc; prevPos[i + 1] = i; tokLen[i + 1] = 0; tokDist[i + 1] = 0;
    }
    const from = cand.off[i], to = cand.off[i + 1];
    for (let k = from; k < to; k++) {
      const p = cand.packed[k];
      const dist = p >>> 9;
      let ml = p & 511;
      if (ml > len - i) ml = len - i;
      const dc = distCost[dist];
      if (rich) {
        for (let b = 0; b < LEN_BOUNDS.length; b++) {
          const L = LEN_BOUNDS[b];
          if (L > ml) break;
          if (L < 3) continue;
          const j = i + L;
          const c = ci + lenCost[L] + dc;
          if (c < cost[j]) {
            cost[j] = c; prevPos[j] = i; tokLen[j] = L; tokDist[j] = dist;
          }
        }
        if (ml !== LEN_BOUNDS[LEN_BOUNDS.length - 1] && ml >= 3) {
          const j = i + ml;
          const c = ci + lenCost[ml] + dc;
          if (c < cost[j]) {
            cost[j] = c; prevPos[j] = i; tokLen[j] = ml; tokDist[j] = dist;
          }
        }
      } else {
        for (let L = ml; L >= 3 && L >= ml - 1; L--) {
          const j = i + L;
          const c = ci + lenCost[L] + dc;
          if (c < cost[j]) {
            cost[j] = c; prevPos[j] = i; tokLen[j] = L; tokDist[j] = dist;
          }
        }
      }
    }
  }
  const rev = [];
  let j = len;
  while (j > 0) {
    const p = prevPos[j];
    const L = tokLen[j];
    if (L === 0) rev.push([0, data[base + p]]);
    else rev.push([1, L, tokDist[j]]);
    j = p;
  }
  const toks = [];
  for (let k = rev.length - 1; k >= 0; k--) {
    const t = rev[k];
    toks.push(t[0], t[1]);
    if (t[0] === 1) toks.push(t[2]);
  }
  return toks;
}

function tokenFrequencies(toks) {
  const litFreq = new Int32Array(288);
  const distFreq = new Int32Array(30);
  for (let i = 0; i < toks.length;) {
    if (toks[i] === 0) { litFreq[toks[i + 1]]++; i += 2; }
    else {
      litFreq[LEN_SYM[toks[i + 1]]]++;
      distFreq[DIST_SYM_OF[toks[i + 2]]]++;
      i += 3;
    }
  }
  litFreq[256]++;
  return { litFreq, distFreq };
}

function emitTokens(w, toks, litCodes, litLens, distCodes, distLens) {
  for (let i = 0; i < toks.length;) {
    if (toks[i] === 0) {
      const s = toks[i + 1];
      w.writeCode(litCodes[s], litLens[s]);
      i += 2;
    } else {
      const L = toks[i + 1], dist = toks[i + 2];
      const ls = LEN_SYM[L];
      w.writeCode(litCodes[ls], litLens[ls]);
      if (LEN_EXTRA_OF_LEN[L]) w.writeBits(LEN_SYM_EXTRA[L], LEN_EXTRA_OF_LEN[L]);
      const ds = DIST_SYM_OF[dist];
      w.writeCode(distCodes[ds], distLens[ds]);
      if (DIST_EXTRA[ds]) w.writeBits(DIST_SYM_EXTRA[dist], DIST_EXTRA[ds]);
      i += 3;
    }
  }
  w.writeCode(litCodes[256], litLens[256]);
}

const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

function rleLengths(seq) {
  const items = [];
  for (let i = 0; i < seq.length;) {
    const v = seq[i];
    if (v === 0) {
      let run = 0;
      while (i + run < seq.length && seq[i + run] === 0 && run < 138) run++;
      if (run >= 3) {
        if (run <= 10) items.push([17, run - 3, 3]);
        else items.push([18, run - 11, 7]);
        i += run;
      } else { for (let k = 0; k < run; k++) items.push([0, 0, 0]); i += run; }
    } else {
      items.push([v, 0, 0]);
      i++;
      let run = 0;
      while (i + run < seq.length && seq[i + run] === v && run < 6) run++;
      if (run >= 3) { items.push([16, run - 3, 2]); i += run; }
    }
  }
  return items;
}

function dynamicHeaderBits(litLens, distLens) {
  let hlit = 286;
  while (hlit > 257 && litLens[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLens[hdist - 1] === 0) hdist--;
  const seq = [];
  for (let i = 0; i < hlit; i++) seq.push(litLens[i]);
  for (let i = 0; i < hdist; i++) seq.push(distLens[i]);
  const items = rleLengths(seq);
  const clFreq = new Int32Array(19);
  for (const [s] of items) clFreq[s]++;
  const clLens = huffmanLengths(clFreq, 7);
  let hclen = 19;
  while (hclen > 4 && clLens[CL_ORDER[hclen - 1]] === 0) hclen--;
  let bits = 5 + 5 + 4 + hclen * 3;
  for (const [s, , eb] of items) bits += clLens[s] + eb;
  return bits;
}

function emitDynamicHeader(w, litLens, distLens) {
  let hlit = 286;
  while (hlit > 257 && litLens[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLens[hdist - 1] === 0) hdist--;
  const seq = [];
  for (let i = 0; i < hlit; i++) seq.push(litLens[i]);
  for (let i = 0; i < hdist; i++) seq.push(distLens[i]);
  const items = rleLengths(seq);
  const clFreq = new Int32Array(19);
  for (const [s] of items) clFreq[s]++;
  const clLens = huffmanLengths(clFreq, 7);
  let hclen = 19;
  while (hclen > 4 && clLens[CL_ORDER[hclen - 1]] === 0) hclen--;
  w.writeBits(hlit - 257, 5);
  w.writeBits(hdist - 1, 5);
  w.writeBits(hclen - 4, 4);
  for (let i = 0; i < hclen; i++) w.writeBits(clLens[CL_ORDER[i]], 3);
  const { codes: clCodes } = buildCodes(clLens);
  for (const [s, extra] of items) {
    w.writeCode(clCodes[s], clLens[s]);
    if (s === 16) w.writeBits(extra, 2);
    else if (s === 17) w.writeBits(extra, 3);
    else if (s === 18) w.writeBits(extra, 7);
  }
}

function tokenBits(toks, litLens, distLens) {
  let bits = 0;
  for (let i = 0; i < toks.length;) {
    if (toks[i] === 0) { bits += litLens[toks[i + 1]]; i += 2; }
    else {
      const L = toks[i + 1], dist = toks[i + 2];
      bits += litLens[LEN_SYM[L]] + LEN_EXTRA_OF_LEN[L] + distLens[DIST_SYM_OF[dist]] + DIST_EXTRA_OF_DIST[dist];
      i += 3;
    }
  }
  return bits + litLens[256];
}

function emitBlock(w, toks, isFinal) {
  const { litFreq, distFreq } = tokenFrequencies(toks);
  const litLens = huffmanLengths(litFreq, 15);
  const distLens = huffmanLengths(distFreq, 15);
  const fixedBits = 3 + tokenBits(toks, FIXED_LIT_LEN, FIXED_DIST_LEN);
  const dynBits = 3 + dynamicHeaderBits(litLens, distLens) + tokenBits(toks, litLens, distLens);
  if (fixedBits <= dynBits) {
    const { codes: lc } = buildCodes(FIXED_LIT_LEN);
    const dc = new Uint32Array(30);
    for (let i = 0; i < 30; i++) dc[i] = i;
    w.writeBits(isFinal ? 1 : 0, 1);
    w.writeBits(1, 2);
    emitTokens(w, toks, lc, FIXED_LIT_LEN, dc, FIXED_DIST_LEN);
    return fixedBits;
  }
  w.writeBits(isFinal ? 1 : 0, 1);
  w.writeBits(2, 2);
  emitDynamicHeader(w, litLens, distLens);
  const { codes: lc } = buildCodes(litLens);
  const { codes: dc } = buildCodes(distLens);
  emitTokens(w, toks, lc, litLens, dc, distLens);
  return dynBits;
}

function deflateOptimal(data, opts) {
  const maxChain = opts.maxChain ?? 128;
  const iterations = opts.iterations ?? 2;
  const blockSize = opts.blockSize ?? 200000;
  const richLast = opts.richLast ?? false;
  const n = data.length;
  const w = new BitWriter(Math.max(1024, n >> 2));
  const matcher = new Matcher(data);
  if (n === 0) {
    w.writeBits(1, 1);
    w.writeBits(1, 2);
    const { codes: lc } = buildCodes(FIXED_LIT_LEN);
    w.writeCode(lc[256], 7);
  }
  for (let base = 0; base < n; base += blockSize) {
    const len = Math.min(blockSize, n - base);
    const isFinal = base + len >= n;
    const cand = computeCandidates(matcher, data, base, len, maxChain);
    let toks = dpParse(data, base, len, cand, FIXED_LIT_LEN, FIXED_DIST_LEN);
    for (let it = 1; it < iterations; it++) {
      const { litFreq, distFreq } = tokenFrequencies(toks);
      const litLens = huffmanLengths(litFreq, 15);
      const distLens = huffmanLengths(distFreq, 15);
      toks = dpParse(data, base, len, cand, litLens, distLens, richLast && it === iterations - 1);
    }
    emitBlock(w, toks, isFinal);
  }
  w.alignByte();
  const body = w.bytes();
  const out = new Uint8Array(body.length + 6);
  out[0] = 0x78; out[1] = 0xda;
  out.set(body, 2);
  const ad = adler32(data);
  out[out.length - 4] = (ad >>> 24) & 0xff;
  out[out.length - 3] = (ad >>> 16) & 0xff;
  out[out.length - 2] = (ad >>> 8) & 0xff;
  out[out.length - 1] = ad & 0xff;
  return out;
}

// ---------- encode one image ----------
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };

// Effort for the optimal-parsing DEFLATE, by filtered-data size.
// Small (palette/grey, ~0.9 MB) gets a longer chain; large (RGB/RGBA,
// ~2.8-3.7 MB) gets a shorter one so the whole set stays well inside
// the 60 s budget. Fixed constants only: output is timing-independent.
function deflateOpts(rawLen) {
  return rawLen <= 1_000_000
    ? { maxChain: 512, iterations: 3, blockSize: 200000, richLast: true }
    : { maxChain: 128, iterations: 3, blockSize: 200000, richLast: true };
}

function encode(rgba, width, height) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const order of ['count', 'luminance']) {
      const p = paletteForm(rgba, colours, order);
      forms.push({
        colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns,
        filters: order === 'count' ? [0, 'minsum', 'pairs'] : [0, 'minsum', 'pairs'],
      });
    }
    if (!grey) return finish(forms, width, height);
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct, trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  forms.push({
    colourType: ct, bpp: { 0: 1, 2: 3, 4: 2, 6: 4 }[ct],
    samples: samplesOf(rgba, ct), plte: null, trns,
    filters: ct === 0 ? [0, 'minsum', 'pairs', 'brute'] : [0, 'minsum', 'pairs'],
  });
  return finish(forms, width, height);
}

function finish(forms, width, height) {
  // Screen every (form, filter) candidate with zlib level 6 (fast, C),
  // then run the optimal-parsing DEFLATE only on the single global
  // winner (plus zlib level 9 as a safety net, taking the smaller
  // stream). Running the slow deflate once per image, not once per form,
  // is what keeps the whole set inside the 60 s wall.
  let best = null;
  for (const form of forms) {
    const chunkOverhead = (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const z = deflateSync(data, SCREEN);
      const screenBytes = z.length + chunkOverhead;
      if (best === null || screenBytes < best.screenBytes) {
        best = { screenBytes, form, data, choice, chunkOverhead };
      }
    }
  }
  const mine = deflateOptimal(best.data, deflateOpts(best.data.length));
  const z9 = deflateSync(best.data, { level: 9, memLevel: 8 });
  const zlib = mine.length <= z9.length ? mine : z9;
  const bytes = zlib.length + best.chunkOverhead;
  const chunks = [chunkBytes('IHDR', ihdr(width, height, best.form.colourType))];
  if (best.form.plte !== null) chunks.push(chunkBytes('PLTE', best.form.plte));
  if (best.form.trns !== null) chunks.push(chunkBytes('tRNS', best.form.trns));
  chunks.push(chunkBytes('IDAT', zlib));
  chunks.push(chunkBytes('IEND', new Uint8Array(0)));
  return { png: pngOf(chunks), info: { colourType: best.form.colourType, choice: best.choice, bytes } };
}

// ---------- main ----------
// Layout (as the kit's starter and baseline do it): the input directory
// holds one subdirectory per instance id, each with image.png; the
// program writes /output/<id>/image.png, creating each directory itself.
function main() {
  const inputDir = process.env.MAKEFUN_INPUT_DIR || '/input';
  const outputDir = process.env.MAKEFUN_OUTPUT_DIR || '/output';
  const ids = readdirSync(inputDir).sort();
  for (const id of ids) {
    const bytes = readFileSync(join(inputDir, id, 'image.png'));
    const { width, height, rgba } = decodePng(new Uint8Array(bytes));
    const { png, info } = encode(rgba, width, height);
    mkdirSync(join(outputDir, id), { recursive: true });
    writeFileSync(join(outputDir, id, 'image.png'), png);
    console.log(`${id}: ${width}x${height} ct=${info.colourType} filter=${info.choice} bytes=${info.bytes}`);
  }
}

main();

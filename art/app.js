// The artist's tool (the hand-made art lane, 2026-11-10). One static page: pick
// the kind, photograph the drawing, see it cleaned and in the game, send it.
// Everything happens here in the browser: finding the paper, straightening
// it, levelling the whites, lifting the drawing off the paper, the palette
// snap, the crop to the kind's canvas, and the preview in real renders of the
// game (frames.json). Only "Finish and import" talks to a server: the pages
// function, with the artist's token from the link's #t= fragment. No AI
// image service is called, ever. No cookies, no analytics.
"use strict";

const CFG = window.ART_CONFIG;
const $ = (id) => document.getElementById(id);
const state = {
  token: "",
  artist: "",
  kind: null,
  frames: null,
  file: null,
  src: null, // ImageData of the photo at work size
  corners: null, // [[x,y] x4] in src pixels: top-left, top-right, bottom-right, bottom-left of the sheet
  fit: "fill",
  whites: 0.95,
  lines: 0.04,
  lift: false,
  snap: false,
  trim: true,
  showBefore: false,
  flat: null, // Float32Array rgb at canvas size, the levelled-whites sheet before levels
  piece: null, // ImageData at canvas size: what gets sent
  busy: false,
};

// ---- small helpers ---------------------------------------------------------

function show(id) {
  for (const s of document.querySelectorAll("main > section")) s.hidden = s.id !== id;
  window.scrollTo(0, 0);
}

function say(el, text, kind) {
  el.textContent = text;
  el.className = "note" + (kind ? " " + kind : "");
  el.hidden = !text;
}

function canvas(w, h) {
  const c = document.createElement("canvas");
  c.width = w;
  c.height = h;
  return c;
}

const clamp01 = (v) => (v < 0 ? 0 : v > 1 ? 1 : v);

function hexRgb(h) {
  const n = parseInt(h.slice(1), 16);
  return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}

// ---- geometry: the square-to-quad homography (Heckbert) --------------------

function squareToQuad(p) {
  const [x0, y0] = p[0], [x1, y1] = p[1], [x2, y2] = p[2], [x3, y3] = p[3];
  const dx1 = x1 - x2, dx2 = x3 - x2, dy1 = y1 - y2, dy2 = y3 - y2;
  const sx = x0 - x1 + x2 - x3, sy = y0 - y1 + y2 - y3;
  let g = 0, h = 0;
  if (Math.abs(sx) > 1e-9 || Math.abs(sy) > 1e-9) {
    const den = dx1 * dy2 - dx2 * dy1;
    g = (sx * dy2 - dx2 * sy) / den;
    h = (dx1 * sy - sx * dy1) / den;
  }
  return [x1 - x0 + g * x1, x3 - x0 + h * x3, x0, y1 - y0 + g * y1, y3 - y0 + h * y3, y0, g, h, 1];
}

function invert3(m) {
  const [a, b, c, d, e, f, g, h, i] = m;
  const A = e * i - f * h, B = -(d * i - f * g), C = d * h - e * g;
  const det = a * A + b * B + c * C;
  return [A / det, -(b * i - c * h) / det, (b * f - c * e) / det, B / det, (a * i - c * g) / det, -(a * f - c * d) / det, C / det, -(a * h - b * g) / det, (a * e - b * d) / det];
}

function apply3(m, x, y) {
  const w = m[6] * x + m[7] * y + m[8];
  return [(m[0] * x + m[1] * y + m[2]) / w, (m[3] * x + m[4] * y + m[5]) / w];
}

// Bilinear RGBA sample of ImageData img at (x, y) into out[0..3], 0..255.
function sample(img, x, y, out) {
  const w = img.width, h = img.height, d = img.data;
  x = Math.max(0, Math.min(w - 1.001, x));
  y = Math.max(0, Math.min(h - 1.001, y));
  const x0 = x | 0, y0 = y | 0, fx = x - x0, fy = y - y0;
  const i00 = (y0 * w + x0) * 4, i10 = i00 + 4, i01 = i00 + w * 4, i11 = i01 + 4;
  for (let k = 0; k < 4; k++) {
    const top = d[i00 + k] + (d[i10 + k] - d[i00 + k]) * fx;
    const bot = d[i01 + k] + (d[i11 + k] - d[i01 + k]) * fx;
    out[k] = top + (bot - top) * fy;
  }
}

// ---- 1. the photo -----------------------------------------------------------

async function loadPhoto(file) {
  let bmp;
  try {
    bmp = await createImageBitmap(file, { imageOrientation: "from-image" });
  } catch {
    bmp = await new Promise((ok, bad) => {
      const im = new Image();
      im.onload = () => ok(im);
      im.onerror = () => bad(new Error("not an image"));
      im.src = URL.createObjectURL(file);
    });
  }
  const long = Math.max(bmp.width, bmp.height);
  const s = Math.min(1, CFG.upload.work_px / long);
  const c = canvas(Math.round(bmp.width * s), Math.round(bmp.height * s));
  const g = c.getContext("2d");
  g.imageSmoothingQuality = "high";
  g.drawImage(bmp, 0, 0, c.width, c.height);
  return g.getImageData(0, 0, c.width, c.height);
}

// The paper: the largest bright patch of a small copy (Otsu's threshold), its
// corners the extremes of x + y and x - y. A sheet that fills the photo, or no
// clear sheet, falls back to the photo's own corners.
function findPaper(img) {
  const s = Math.min(1, 400 / Math.max(img.width, img.height));
  const w = Math.max(1, Math.round(img.width * s)), h = Math.max(1, Math.round(img.height * s));
  const lum = new Float32Array(w * h);
  const px = [0, 0, 0, 0];
  const hist = new Array(256).fill(0);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      sample(img, (x + 0.5) / s - 0.5, (y + 0.5) / s - 0.5, px);
      const l = 0.299 * px[0] + 0.587 * px[1] + 0.114 * px[2];
      lum[y * w + x] = l;
      hist[l | 0]++;
    }
  }
  const n = w * h;
  let sum = 0;
  for (let i = 0; i < 256; i++) sum += i * hist[i];
  let sumB = 0, wB = 0, best = 0, t = 128;
  for (let i = 0; i < 256; i++) {
    wB += hist[i];
    if (wB === 0) continue;
    const wF = n - wB;
    if (wF === 0) break;
    sumB += i * hist[i];
    const mB = sumB / wB, mF = (sum - sumB) / wF;
    const between = wB * wF * (mB - mF) * (mB - mF);
    if (between > best) {
      best = between;
      t = i;
    }
  }
  const seen = new Uint8Array(n);
  let bestPix = null;
  for (let start = 0; start < n; start++) {
    if (seen[start] || lum[start] <= t) continue;
    const comp = [];
    const stack = [start];
    seen[start] = 1;
    while (stack.length) {
      const i = stack.pop();
      comp.push(i);
      const x = i % w, y = (i / w) | 0;
      const nb = [x > 0 ? i - 1 : -1, x < w - 1 ? i + 1 : -1, y > 0 ? i - w : -1, y < h - 1 ? i + w : -1];
      for (const j of nb) {
        if (j >= 0 && !seen[j] && lum[j] > t) {
          seen[j] = 1;
          stack.push(j);
        }
      }
    }
    if (!bestPix || comp.length > bestPix.length) bestPix = comp;
  }
  const full = [[0, 0], [img.width, 0], [img.width, img.height], [0, img.height]];
  if (!bestPix || bestPix.length < n * 0.12 || bestPix.length > n * 0.97) return full;
  let tl = [1e9, 0, 0], br = [-1e9, 0, 0], tr = [-1e9, 0, 0], bl = [1e9, 0, 0];
  for (const i of bestPix) {
    const x = i % w, y = (i / w) | 0;
    if (x + y < tl[0]) tl = [x + y, x, y];
    if (x + y > br[0]) br = [x + y, x, y];
    if (x - y > tr[0]) tr = [x - y, x, y];
    if (x - y < bl[0]) bl = [x - y, x, y];
  }
  // Pull each corner a little inside the sheet, off its shadowed edge.
  const pts = [tl, tr, br, bl].map((c) => [(c[1] + 0.5) / s, (c[2] + 0.5) / s]);
  const cx = pts.reduce((a, p) => a + p[0], 0) / 4, cy = pts.reduce((a, p) => a + p[1], 0) / 4;
  return pts.map(([x, y]) => [x + (cx - x) * 0.012, y + (cy - y) * 0.012]);
}

// ---- 2. straighten and fit to the canvas ------------------------------------

function sheetAspect(c) {
  const d = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);
  return (d(c[0], c[1]) + d(c[3], c[2])) / 2 / Math.max(1, (d(c[0], c[3]) + d(c[1], c[2])) / 2);
}

// How bright the paper is anywhere in the photo: a smooth surface (a
// quadratic in the photo's x and y) fitted to the paper alone, the bright,
// grey cells of a grid over the whole sheet, and the paper's tint. A drawing
// that fills a region (a sky, a sea) is not paper and does not pull it: its
// cells are coloured or darker than the paper and are left out. Light falls
// off smoothly across a sheet, so the surface carries it under the drawing.
function paperModel() {
  const m = squareToQuad(state.corners);
  const n = 96, cell = 6;
  const px = [0, 0, 0, 0];
  const cand = [];
  const all = [];
  for (let gy = 0; gy < n / cell; gy++) {
    for (let gx = 0; gx < n / cell; gx++) {
      const vals = [];
      for (let y = 0; y < cell; y++) {
        for (let x = 0; x < cell; x++) {
          const u = (gx * cell + x + 0.5) / n, v = (gy * cell + y + 0.5) / n;
          const [sx, sy] = apply3(m, u, v);
          sample(state.src, sx, sy, px);
          const l = 0.299 * px[0] + 0.587 * px[1] + 0.114 * px[2];
          const sat = Math.max(px[0], px[1], px[2]) - Math.min(px[0], px[1], px[2]);
          if (sat < 0.12 * l + 6) vals.push([l, px[0], px[1], px[2], sx, sy]);
        }
      }
      if (vals.length < cell * cell * 0.5) continue;
      vals.sort((p, q) => p[0] - q[0]);
      const top = vals[Math.floor(vals.length * 0.85)];
      cand.push(top);
      all.push(top[0]);
    }
  }
  all.sort((p, q) => p - q);
  const level = all.length ? all[Math.floor(all.length * 0.95)] : 255;
  const ok = cand.filter((c) => c[0] >= level * 0.78);
  const tint = [1, 1, 1];
  if (ok.length) {
    let r = 0, g = 0, b = 0;
    for (const c of ok) {
      r += c[1] / c[0];
      g += c[2] / c[0];
      b += c[3] / c[0];
    }
    tint[0] = r / ok.length;
    tint[1] = g / ok.length;
    tint[2] = b / ok.length;
  }
  const sw = state.src.width, sh = state.src.height;
  const terms = (x, y) => [1, x, y, x * x, x * y, y * y];
  let coef = null;
  if (ok.length >= 10) {
    const A = Array.from({ length: 6 }, () => new Array(6).fill(0));
    const rhs = new Array(6).fill(0);
    for (const c of ok) {
      const t = terms(c[4] / sw, c[5] / sh);
      for (let i = 0; i < 6; i++) {
        rhs[i] += t[i] * c[0];
        for (let j = 0; j < 6; j++) A[i][j] += t[i] * t[j];
      }
    }
    for (let i = 0; i < 6; i++) A[i][i] += 1e-6;
    coef = solve(A, rhs);
  }
  const floor = level * 0.55;
  return {
    tint,
    at: (sx, sy) => {
      if (!coef) return level;
      const t = terms(sx / sw, sy / sh);
      let v = 0;
      for (let i = 0; i < 6; i++) v += coef[i] * t[i];
      return Math.max(floor, Math.min(255, v));
    },
  };
}

// Gaussian elimination with partial pivoting; null when singular.
function solve(A, b) {
  const n = b.length;
  const M = A.map((row, i) => [...row, b[i]]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    if (Math.abs(M[p][c]) < 1e-12) return null;
    [M[c], M[p]] = [M[p], M[c]];
    for (let r = c + 1; r < n; r++) {
      const f = M[r][c] / M[c][c];
      for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
    }
  }
  const x = new Array(n).fill(0);
  for (let r = n - 1; r >= 0; r--) {
    let s = M[r][n];
    for (let k = r + 1; k < n; k++) s -= M[r][k] * x[k];
    x[r] = s / M[r][r];
  }
  return x;
}

// The straightened sheet at the kind's canvas, its whites levelled: each pixel
// divided by the paper's brightness and tint where it was in the photo
// (paperModel), so shade and a phone's uneven light fall away.
// The drawing's box on the sheet, in the sheet's own 0..1 coordinates: where a
// small straightened copy, its paper levelled, is darker or more coloured than
// paper. A margin of blank paper round a drawing is left out of the piece.
function drawingBox(corners) {
  const m = squareToQuad(corners);
  const a = sheetAspect(corners);
  const n = 160, w = Math.max(8, Math.round(a >= 1 ? n : n * a)), h = Math.max(8, Math.round(a >= 1 ? n / a : n));
  const lum = new Float32Array(w * h), sat = new Float32Array(w * h);
  const px = [0, 0, 0, 0];
  let top = 0;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const [sx, sy] = apply3(m, (x + 0.5) / w, (y + 0.5) / h);
      sample(state.src, sx, sy, px);
      const i = y * w + x;
      lum[i] = 0.299 * px[0] + 0.587 * px[1] + 0.114 * px[2];
      sat[i] = Math.max(px[0], px[1], px[2]) - Math.min(px[0], px[1], px[2]);
    }
  }
  // The paper's brightness per row band, so a light falling off down the sheet is not "drawing".
  let x0 = w, x1 = -1, y0 = h, y1 = -1;
  for (let y = 0; y < h; y++) {
    const row = Array.from(lum.subarray(y * w, y * w + w)).sort((p, q) => p - q);
    const paper = row[Math.floor(w * 0.9)];
    top = Math.max(top, paper);
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      if (lum[i] < paper * 0.78 || sat[i] > 60) {
        x0 = Math.min(x0, x);
        x1 = Math.max(x1, x);
        y0 = Math.min(y0, y);
        y1 = Math.max(y1, y);
      }
    }
  }
  if (x1 < 0 || (x1 - x0) < w * 0.2 || (y1 - y0) < h * 0.2) return [0, 0, 1, 1];
  const pad = 1.5;
  return [Math.max(0, (x0 - pad) / w), Math.max(0, (y0 - pad) / h), Math.min(1, (x1 + 1 + pad) / w), Math.min(1, (y1 + 1 + pad) / h)];
}

function trimmedCorners() {
  if (!state.trim) return state.corners;
  const [u0, v0, u1, v1] = drawingBox(state.corners);
  const m = squareToQuad(state.corners);
  return [apply3(m, u0, v0), apply3(m, u1, v0), apply3(m, u1, v1), apply3(m, u0, v1)];
}

function straighten() {
  const [W, H] = state.kind.canvas;
  const corners = trimmedCorners();
  const m = squareToQuad(corners);
  const a = sheetAspect(corners);
  let sw, sh;
  if (state.fit === "fill" ? a > W / H : a < W / H) {
    sh = H;
    sw = H * a;
  } else {
    sw = W;
    sh = W / a;
  }
  const ox = (W - sw) / 2, oy = (H - sh) / 2;
  const rgb = new Float32Array(W * H * 3);
  const srcXY = new Float32Array(W * H * 2);
  const inside = new Uint8Array(W * H);
  const px = [0, 0, 0, 0];
  for (let y = 0; y < H; y++) {
    const v = (y + 0.5 - oy) / sh;
    for (let x = 0; x < W; x++) {
      const u = (x + 0.5 - ox) / sw;
      const i = y * W + x;
      if (u < 0 || u > 1 || v < 0 || v > 1) {
        rgb[i * 3] = rgb[i * 3 + 1] = rgb[i * 3 + 2] = 255;
        continue;
      }
      const [sx, sy] = apply3(m, u, v);
      sample(state.src, sx, sy, px);
      srcXY[i * 2] = sx;
      srcXY[i * 2 + 1] = sy;
      rgb[i * 3] = px[0];
      rgb[i * 3 + 1] = px[1];
      rgb[i * 3 + 2] = px[2];
      inside[i] = 1;
    }
  }
  const paper = paperModel();
  const flat = new Float32Array(W * H * 3);
  for (let i = 0; i < W * H; i++) {
    if (!inside[i]) {
      flat[i * 3] = flat[i * 3 + 1] = flat[i * 3 + 2] = 1;
      continue;
    }
    const bg = paper.at(srcXY[i * 2], srcXY[i * 2 + 1]);
    for (let k = 0; k < 3; k++) flat[i * 3 + k] = rgb[i * 3 + k] / (bg * paper.tint[k]);
  }
  state.flat = flat;
}

// ---- 3. levels, lift, snap ---------------------------------------------------

let paletteLab = null;
let paletteRgb = null;
let snapCache = null;

function toLab(r, g, b) {
  const lin = (c) => {
    c /= 255;
    return c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
  };
  const R = lin(r), G = lin(g), B = lin(b);
  const f = (t) => (t > 0.008856 ? Math.cbrt(t) : 7.787 * t + 16 / 116);
  const X = f((R * 0.4124 + G * 0.3576 + B * 0.1805) / 0.95047);
  const Y = f(R * 0.2126 + G * 0.7152 + B * 0.0722);
  const Z = f((R * 0.0193 + G * 0.1192 + B * 0.9505) / 1.08883);
  return [116 * Y - 16, 500 * (X - Y), 200 * (Y - Z)];
}

function nearest(r, g, b) {
  if (!paletteLab) {
    paletteRgb = [];
    for (const ramp of Object.values(CFG.palette.ramps)) for (const h of ramp) paletteRgb.push(hexRgb(h));
    paletteLab = paletteRgb.map((c) => toLab(c[0], c[1], c[2]));
    snapCache = new Int16Array(32768).fill(-1);
  }
  const key = ((r >> 3) << 10) | ((g >> 3) << 5) | (b >> 3);
  let idx = snapCache[key];
  if (idx < 0) {
    const L = toLab((r & 248) + 4, (g & 248) + 4, (b & 248) + 4);
    let best = 1e9;
    for (let i = 0; i < paletteLab.length; i++) {
      const p = paletteLab[i];
      const d = (p[0] - L[0]) ** 2 + (p[1] - L[1]) ** 2 + (p[2] - L[2]) ** 2;
      if (d < best) {
        best = d;
        idx = i;
      }
    }
    snapCache[key] = idx;
  }
  return paletteRgb[idx];
}

function finish(snap) {
  const [W, H] = state.kind.canvas;
  const out = new ImageData(W, H);
  const d = out.data, f = state.flat;
  const lo = state.lines, hi = Math.max(lo + 0.05, state.whites);
  for (let i = 0; i < W * H; i++) {
    let r = clamp01((f[i * 3] - lo) / (hi - lo));
    let g = clamp01((f[i * 3 + 1] - lo) / (hi - lo));
    let b = clamp01((f[i * 3 + 2] - lo) / (hi - lo));
    let a = 1;
    if (state.lift) {
      a = 1 - Math.min(r, g, b);
      if (a < 0.06) a = 0;
      if (a > 0) {
        r = clamp01(1 - (1 - r) / a);
        g = clamp01(1 - (1 - g) / a);
        b = clamp01(1 - (1 - b) / a);
      }
    }
    let R = r * 255, G = g * 255, B = b * 255;
    if (snap) {
      if (state.lift) a = a >= 0.45 ? 1 : 0;
      if (a > 0) [R, G, B] = nearest(R | 0, G | 0, B | 0);
    }
    d[i * 4] = R;
    d[i * 4 + 1] = G;
    d[i * 4 + 2] = B;
    d[i * 4 + 3] = a * 255;
  }
  return out;
}

// ---- 4. the preview: the piece in the game's own renders --------------------

const FRAME_SCALE = 2; // frames are rendered at 540 x 960; the preview composites at the phone's 1080 x 1920

function loadImage(src) {
  return new Promise((ok, bad) => {
    const im = new Image();
    im.onload = () => ok(im);
    im.onerror = () => bad(new Error("could not load " + src));
    im.src = src;
  });
}

async function frameImage(f) {
  if (!f._img) f._img = await loadImage("frames/" + f.image);
  return f._img;
}

// One quad of a frame: the piece warped onto it (tiled when the kind repeats),
// only over the frame's pixels near a key colour when the quad names keys (so
// the seats, the seat map, the pass's print stay in front), shaded by how much
// darker the render is there than the key, so the room's light falls on it.
function paintQuad(dst, q, piece, tile) {
  const S = FRAME_SCALE;
  const pts = q.pts.map(([x, y]) => [x * S, y * S]);
  const inv = invert3(squareToQuad(pts));
  const W = dst.width, d = dst.data;
  const keys = (q.keys || []).map((k) => [k[0], k[1], k[2], 0.299 * k[0] + 0.587 * k[1] + 0.114 * k[2]]);
  const tol = q.tol ?? 40;
  const reps = q.repeat || [1, 1];
  const minX = Math.max(0, Math.floor(Math.min(...pts.map((p) => p[0])))), maxX = Math.min(W - 1, Math.ceil(Math.max(...pts.map((p) => p[0]))));
  const minY = Math.max(0, Math.floor(Math.min(...pts.map((p) => p[1])))), maxY = Math.min(dst.height - 1, Math.ceil(Math.max(...pts.map((p) => p[1]))));
  const px = [0, 0, 0, 0];
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      let [u, v] = apply3(inv, x + 0.5, y + 0.5);
      if (u < 0 || u > 1 || v < 0 || v > 1) continue;
      const i = (y * W + x) * 4;
      let shade = q.shade ?? 1;
      if (keys.length) {
        let hit = null;
        for (const k of keys) {
          if (Math.abs(d[i] - k[0]) <= tol && Math.abs(d[i + 1] - k[1]) <= tol && Math.abs(d[i + 2] - k[2]) <= tol) {
            hit = k;
            break;
          }
        }
        if (!hit) continue;
        if (q.mode === "multiply") shade *= Math.max(0.35, Math.min(1.25, (0.299 * d[i] + 0.587 * d[i + 1] + 0.114 * d[i + 2]) / Math.max(1, hit[3])));
      }
      if (tile) {
        u = (u * reps[0]) % 1;
        v = (v * reps[1]) % 1;
      }
      sample(piece, u * piece.width - 0.5, v * piece.height - 0.5, px);
      const a = px[3] / 255;
      for (let k = 0; k < 3; k++) d[i + k] = d[i + k] * (1 - a) + Math.min(255, px[k] * shade) * a;
    }
  }
}

async function composite(f, piece) {
  const img = await frameImage(f);
  const c = canvas(img.width * FRAME_SCALE, img.height * FRAME_SCALE);
  const g = c.getContext("2d");
  g.imageSmoothingQuality = "high";
  g.drawImage(img, 0, 0, c.width, c.height);
  for (const r of f.clear || []) {
    g.fillStyle = r.color;
    g.fillRect(r.x * FRAME_SCALE, r.y * FRAME_SCALE, r.w * FRAME_SCALE, r.h * FRAME_SCALE);
  }
  const dst = g.getImageData(0, 0, c.width, c.height);
  for (const q of f.quads) paintQuad(dst, q, piece, !!state.kind.tile);
  g.putImageData(dst, 0, 0);
  return c;
}

function checker(w, h) {
  const c = canvas(w, h);
  const g = c.getContext("2d");
  const s = Math.max(8, Math.round(Math.min(w, h) / 24));
  for (let y = 0; y < h; y += s) for (let x = 0; x < w; x += s) {
    g.fillStyle = ((x + y) / s) % 2 ? "#e9dcc0" : "#fff6e0";
    g.fillRect(x, y, s, s);
  }
  return c;
}

function pieceCanvas(piece) {
  const c = canvas(piece.width, piece.height);
  c.getContext("2d").putImageData(piece, 0, 0);
  return c;
}

// The object kind: the cleaned drawing beside the gate, never pasted into it.
async function objectPreview(piece) {
  const f = state.frames[state.kind.frames[0]];
  const img = await frameImage(f);
  const H = img.height * FRAME_SCALE;
  const c = canvas(img.width * FRAME_SCALE * 2, H);
  const g = c.getContext("2d");
  g.fillStyle = "#fff6e0";
  g.fillRect(0, 0, c.width, c.height);
  const side = c.width - img.width * FRAME_SCALE;
  const s = Math.min(side / piece.width, H / piece.height) * 0.9;
  g.drawImage(checker(Math.round(piece.width * s), Math.round(piece.height * s)), (side - piece.width * s) / 2, (H - piece.height * s) / 2);
  g.drawImage(pieceCanvas(piece), (side - piece.width * s) / 2, (H - piece.height * s) / 2, piece.width * s, piece.height * s);
  g.drawImage(img, side, 0, img.width * FRAME_SCALE, H);
  return c;
}

let renderGen = 0;

// Builds the preview off the page and swaps it in only if no newer edit has
// started meanwhile, so quick slider moves never leave two previews behind.
async function render() {
  if (!state.flat) return;
  const gen = ++renderGen;
  const piece = finish(state.snap);
  const shown = state.snap && state.showBefore ? finish(false) : piece;
  const figs = [];
  if (state.kind.object) {
    const fig = document.createElement("figure");
    const c = await objectPreview(shown);
    c.className = "wide";
    fig.append(c);
    const cap = document.createElement("figcaption");
    cap.textContent = "Built in 3D from this, you'll get a render to approve.";
    fig.append(cap);
    figs.push(fig);
  } else {
    for (const id of state.kind.frames) {
      const f = state.frames[id];
      const fig = document.createElement("figure");
      const c = await composite(f, shown);
      if (gen !== renderGen) return;
      c.className = "phone";
      fig.append(c);
      const cap = document.createElement("figcaption");
      cap.textContent = f.caption;
      fig.append(cap);
      figs.push(fig);
    }
  }
  if (gen !== renderGen) return;
  state.piece = piece;
  $("frames").replaceChildren(...figs);
  const p = $("piece");
  const [W, H] = state.kind.canvas;
  p.width = W;
  p.height = H;
  const g = p.getContext("2d");
  g.drawImage(checker(W, H), 0, 0);
  g.drawImage(pieceCanvas(shown), 0, 0);
  $("piece-cap").textContent = `The piece itself, ${W} by ${H}` + (state.lift ? ", lifted off the paper (the checks show through)." : ".");
  $("before").hidden = !state.snap;
  $("before").textContent = state.showBefore ? "Show after the snap" : "Show before the snap";
}

// ---- the corner editor --------------------------------------------------------

function drawCorners() {
  const c = $("paper");
  const img = state.src;
  const s = Math.min(1, 900 / Math.max(img.width, img.height));
  c.width = Math.round(img.width * s);
  c.height = Math.round(img.height * s);
  c.dataset.scale = String(s);
  const g = c.getContext("2d");
  const tmp = canvas(img.width, img.height);
  tmp.getContext("2d").putImageData(img, 0, 0);
  g.drawImage(tmp, 0, 0, c.width, c.height);
  const p = state.corners.map(([x, y]) => [x * s, y * s]);
  g.lineWidth = Math.max(2, c.width / 220);
  g.strokeStyle = "#e4572e";
  g.beginPath();
  p.forEach(([x, y], i) => (i ? g.lineTo(x, y) : g.moveTo(x, y)));
  g.closePath();
  g.stroke();
  if (state.trim) {
    const t = trimmedCorners().map(([x, y]) => [x * s, y * s]);
    g.setLineDash([g.lineWidth * 3, g.lineWidth * 2]);
    g.strokeStyle = "#1f5fae";
    g.beginPath();
    t.forEach(([x, y], i) => (i ? g.lineTo(x, y) : g.moveTo(x, y)));
    g.closePath();
    g.stroke();
    g.setLineDash([]);
  }
  const r = Math.max(10, c.width / 40);
  p.forEach(([x, y], i) => {
    g.fillStyle = i === 0 ? "#ffd23f" : "#fff";
    g.strokeStyle = "#2a1e14";
    g.beginPath();
    g.arc(x, y, r, 0, Math.PI * 2);
    g.fill();
    g.stroke();
  });
}

function wireCorners() {
  const c = $("paper");
  let drag = -1;
  const at = (e) => {
    const b = c.getBoundingClientRect();
    const s = Number(c.dataset.scale);
    return [((e.clientX - b.left) / b.width) * c.width / s, ((e.clientY - b.top) / b.height) * c.height / s];
  };
  c.addEventListener("pointerdown", (e) => {
    const [x, y] = at(e);
    const b = c.getBoundingClientRect();
    const reach = (44 / b.width) * c.width / Number(c.dataset.scale);
    let best = reach;
    drag = -1;
    state.corners.forEach(([cx, cy], i) => {
      const d = Math.hypot(cx - x, cy - y);
      if (d < best) {
        best = d;
        drag = i;
      }
    });
    if (drag >= 0) {
      c.setPointerCapture(e.pointerId);
      e.preventDefault();
    }
  });
  c.addEventListener("pointermove", (e) => {
    if (drag < 0) return;
    const [x, y] = at(e);
    state.corners[drag] = [Math.max(0, Math.min(state.src.width, x)), Math.max(0, Math.min(state.src.height, y))];
    drawCorners();
  });
  const end = () => {
    if (drag < 0) return;
    drag = -1;
    rework(true);
  };
  c.addEventListener("pointerup", end);
  c.addEventListener("pointercancel", end);
}

// ---- the flow -------------------------------------------------------------------

let pending = null;
function rework(geometry) {
  clearTimeout(pending);
  pending = setTimeout(async () => {
    $("working").hidden = false;
    await new Promise((r) => requestAnimationFrame(() => setTimeout(r, 0)));
    if (geometry) straighten();
    await render();
    $("working").hidden = true;
  }, 30);
}

function pickKind(k) {
  state.kind = k;
  state.lift = !!k.cutout;
  state.fit = "fill";
  $("kind-name").textContent = k.label;
  $("kind-hint").textContent = k.hint;
  $("kind-where").textContent = k.object
    ? "We build it in 3D from your drawing, by hand. You get a render to approve before it goes in."
    : k.in_game
      ? "It shows in the game as you drew it."
      : "It shows in the game as you drew it. Its place in the game gets wired the first time one arrives, so this one takes a little longer.";
  $("photo-input").value = "";
  show("photo");
}

async function takePhoto(file) {
  if (!file) return;
  state.file = file;
  say($("photo-msg"), "Reading the photo...", "");
  try {
    state.src = await loadPhoto(file);
  } catch {
    say($("photo-msg"), "That file did not open as a picture. Try a JPEG or PNG photo.", "error");
    return;
  }
  say($("photo-msg"), "", "");
  state.corners = findPaper(state.src);
  state.piece = null;
  state.flat = null;
  $("frames").replaceChildren();
  state.snap = false;
  state.showBefore = false;
  $("fit-fill").checked = true;
  state.trim = !state.kind.tile;
  $("trim").checked = state.trim;
  $("lift").checked = state.lift;
  $("snap").checked = false;
  $("whites").value = String(state.whites);
  $("lines").value = String(state.lines);
  $("name").value = "";
  $("note").value = "";
  say($("send-msg"), "", "");
  $("edit").open = false;
  show("preview");
  $("pv-kind").textContent = state.kind.label;
  drawCorners();
  rework(true);
}

function blob(c, type, q) {
  return new Promise((ok) => c.toBlob(ok, type, q));
}

async function photoBlob() {
  const f = state.file;
  if (/^image\/(jpeg|png|webp)$/.test(f.type) && f.size <= CFG.upload.photo_max_bytes) return f;
  const c = canvas(state.src.width, state.src.height);
  c.getContext("2d").putImageData(state.src, 0, 0);
  return blob(c, "image/jpeg", 0.9);
}

async function send() {
  if (state.busy) return;
  if (!state.piece) return;
  const name = $("name").value.trim();
  if (!name) {
    say($("send-msg"), "Give the piece a name first.", "error");
    $("name").focus();
    return;
  }
  state.busy = true;
  $("send").disabled = true;
  say($("send-msg"), "Sending...", "");
  try {
    const png = await blob(pieceCanvas(state.piece), "image/png");
    const prev = state.kind.object ? await objectPreview(state.piece) : await composite(state.frames[state.kind.frames[0]], state.piece);
    let preview = await blob(prev, "image/jpeg", 0.85);
    if (preview.size > CFG.upload.preview_max_bytes) {
      const half = canvas(prev.width / 2, prev.height / 2);
      half.getContext("2d").drawImage(prev, 0, 0, half.width, half.height);
      preview = await blob(half, "image/jpeg", 0.8);
    }
    const form = new FormData();
    form.append("token", state.token);
    form.append("kind", state.kind.id);
    form.append("name", name);
    form.append("note", $("note").value.trim());
    form.append("settings", JSON.stringify({
      corners: state.corners.map(([x, y]) => [Math.round(x), Math.round(y)]),
      work: [state.src.width, state.src.height],
      fit: state.fit,
      trim: state.trim,
      whites: state.whites,
      lines: state.lines,
      lift: state.lift,
      snap: state.snap,
    }));
    form.append("png", png, "clean.png");
    form.append("photo", await photoBlob(), "photo");
    form.append("preview", preview, "preview.jpg");
    const r = await fetch(CFG.functionUrl + "/art/submit", { method: "POST", body: form });
    const body = await r.json().catch(() => ({}));
    if (!r.ok) throw new Error(body.message || "The upload did not go through (" + r.status + ").");
    $("sent-name").textContent = name;
    const keep = $("sent-preview");
    keep.width = prev.width;
    keep.height = prev.height;
    keep.getContext("2d").drawImage(prev, 0, 0);
    show("sent");
  } catch (e) {
    say($("send-msg"), (e && e.message) || "Something went wrong. Please try again.", "error");
  } finally {
    state.busy = false;
    $("send").disabled = false;
  }
}

async function hello() {
  const t = new URLSearchParams(location.hash.slice(1)).get("t") || sessionStorage.getItem("art_t") || "";
  if (!t) {
    say($("who"), "This page needs your invite link. Ask Stephen for it.", "error");
    return false;
  }
  try {
    const r = await fetch(CFG.functionUrl + "/art/hello", { method: "POST", headers: { "content-type": "text/plain" }, body: JSON.stringify({ token: t }) });
    const body = await r.json().catch(() => ({}));
    if (!r.ok) {
      say($("who"), body.message || "This invite link is not active. Ask Stephen for a new one.", "error");
      return false;
    }
    state.token = t;
    state.artist = body.name;
    try {
      sessionStorage.setItem("art_t", t);
    } catch {
      // private mode: the link's fragment is enough for this visit
    }
    history.replaceState(null, "", location.pathname);
    $("hi").textContent = `Hi ${body.name}.`;
    return true;
  } catch {
    say($("who"), "The art desk could not be reached. Check the connection and reload.", "error");
    return false;
  }
}

async function main() {
  const grid = $("kind-grid");
  for (const k of CFG.kinds) {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "kind";
    const t = document.createElement("strong");
    t.textContent = k.label;
    const h = document.createElement("span");
    h.textContent = k.hint;
    b.append(t, h);
    if (k.in_game) {
      const tag = document.createElement("em");
      tag.textContent = "in the game now";
      b.append(tag);
    }
    b.addEventListener("click", () => pickKind(k));
    grid.append(b);
  }
  $("photo-input").addEventListener("change", (e) => takePhoto(e.target.files[0]));
  $("back-kinds").addEventListener("click", () => show("kinds"));
  $("back-photo").addEventListener("click", () => show("photo"));
  $("again").addEventListener("click", () => show("kinds"));
  $("fit-fill").addEventListener("change", () => { state.fit = "fill"; rework(true); });
  $("fit-whole").addEventListener("change", () => { state.fit = "whole"; rework(true); });
  $("whites").addEventListener("input", (e) => { state.whites = Number(e.target.value); rework(false); });
  $("lines").addEventListener("input", (e) => { state.lines = Number(e.target.value); rework(false); });
  $("lift").addEventListener("change", (e) => { state.lift = e.target.checked; rework(false); });
  $("trim").addEventListener("change", (e) => { state.trim = e.target.checked; drawCorners(); rework(true); });
  $("snap").addEventListener("change", (e) => { state.snap = e.target.checked; state.showBefore = false; rework(false); });
  $("before").addEventListener("click", () => { state.showBefore = !state.showBefore; rework(false); });
  $("turn").addEventListener("click", () => { state.corners = [state.corners[3], state.corners[0], state.corners[1], state.corners[2]]; drawCorners(); rework(true); });
  $("refind").addEventListener("click", () => { state.corners = findPaper(state.src); drawCorners(); rework(true); });
  $("whole-photo").addEventListener("click", () => {
    const w = state.src.width, h = state.src.height;
    state.corners = [[0, 0], [w, 0], [w, h], [0, h]];
    drawCorners();
    rework(true);
  });
  $("keep").addEventListener("click", () => { $("edit").open = true; $("edit").scrollIntoView({ behavior: "smooth" }); });
  $("send").addEventListener("click", send);
  wireCorners();
  try {
    const r = await fetch("frames/frames.json");
    state.frames = (await r.json()).frames;
  } catch {
    say($("who"), "The game's pictures did not load. Reload the page.", "error");
    show("none");
    return;
  }
  show(await hello() ? "kinds" : "none");
}

main();

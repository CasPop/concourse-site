// The art desk's pixel work (the art desk for everyone, 2026-11-10). No DOM in
// here: plain width, height and byte arrays in and out, so the page (a classic
// script, window.ArtPixels) and the server's tests (vm.runInThisContext,
// globalThis.ArtPixels) run the very same code.
//
// An image is {width, height, data}: data is RGBA bytes, row by row, which is
// what a canvas's ImageData already is. Corners are [[x, y] x4] in the
// photo's pixels: top left, top right, bottom right, bottom left of the piece.
//
// Three ways in:
//   paper  a drawing with bare paper round it: find the sheet, straighten it,
//          divide by the paper's light so the paper turns white, levels.
//   paint  colour covers the surface: find the piece from the table inward,
//          straighten it, then one even grade (linear light, one gain, never
//          a per-pixel divide) whose middle is "as shot".
//   screen a picture file: no corners, no clean-up; the artist frames it.
// Then the guard (does a paper photo read as a painting?) and the photo
// checks. Every threshold is in T, each set by measuring the fixtures
// (server/tests/art_pixels.test.ts; the As built in
// docs/slices/2026-11-10-art-desk-for-everyone.md has the numbers).
"use strict";

(function (root) {
  const T = {
    // The guard: the share of the sheet's outer band that reads as bare paper,
    // and the share of the whole sheet. Under both: painted.
    guardRing: 0.35,
    guardAll: 0.5,
    // dark: the piece's 95th percentile light, 0..255, under this.
    dark: 105,
    // uneven: the dimmest side's light over the brightest's, under this.
    uneven: 0.63,
    // shine: clipped white cells, at least this share of the piece in one
    // patch, its edge soft (the next cells out still this far from the
    // piece's middle light toward white), and not most of the piece.
    shineLum: 250,
    shineArea: 0.0012,
    shineHalo: 0.45,
    shineMaxShare: 0.3,
    // blur: the sharpest edges' fine slope over their coarse slope, under this.
    blur: 1.6,
    // angle: a corner's angle this far from square, or opposite sides this unequal.
    angleDeg: 16,
    angleSide: 0.72,
    // small: the piece's area in the photo under this share of the canvas, or of the photo.
    smallCanvas: 0.5,
    smallShare: 0.1,
    // cut: a corner this close to the photo's edge (a share of its size).
    cutEdge: 0.004,
    // The painted piece finder: a pixel differs from the table by this much
    // (0..441 in RGB) at least, or this many of the table's own spreads.
    pieceMin: 26,
    pieceSpread: 4,
    // Warmth: at least this much log gain between red and blue at the slider's end.
    warmMin: 0.12,
    // Brightness: stops of gain at the slider's ends; the shoulder starts here (linear light).
    brightStops: 1,
    knee: 0.72,
  };

  const clamp01 = (v) => (v < 0 ? 0 : v > 1 ? 1 : v);
  const lumOf = (r, g, b) => 0.299 * r + 0.587 * g + 0.114 * b;

  function hexRgb(h) {
    const n = parseInt(h.slice(1), 16);
    return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
  }

  function makeImage(w, h) {
    return { width: w, height: h, data: new Uint8ClampedArray(w * h * 4) };
  }

  // ---- geometry: the square-to-quad homography (Heckbert) ------------------

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

  // Bilinear RGBA sample of img at (x, y) into out[0..3], 0..255.
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

  function dist2(a, b) {
    return Math.hypot(a[0] - b[0], a[1] - b[1]);
  }

  function sheetAspect(c) {
    return (dist2(c[0], c[1]) + dist2(c[3], c[2])) / 2 / Math.max(1, (dist2(c[0], c[3]) + dist2(c[1], c[2])) / 2);
  }

  function quadArea(c) {
    let a = 0;
    for (let i = 0; i < 4; i++) {
      const p = c[i], q = c[(i + 1) % 4];
      a += p[0] * q[1] - q[0] * p[1];
    }
    return Math.abs(a) / 2;
  }

  function wholePhoto(img) {
    return [[0, 0], [img.width, 0], [img.width, img.height], [0, img.height]];
  }

  function isWhole(img, c) {
    const w = wholePhoto(img);
    return c.every((p, i) => Math.abs(p[0] - w[i][0]) < 1 && Math.abs(p[1] - w[i][1]) < 1);
  }

  // The size the corners' picture takes on a W x H canvas: [sw, sh, ox, oy].
  // "whole" fits it inside (margins), "fill" covers the canvas (cut evenly).
  function fitBox(aspect, W, H, fit) {
    let sw, sh;
    if (fit === "fill" ? aspect > W / H : aspect < W / H) {
      sh = H;
      sw = H * aspect;
    } else {
      sw = W;
      sh = W / aspect;
    }
    return [sw, sh, (W - sw) / 2, (H - sh) / 2];
  }

  // A small grid over the corners' quad: lum, chroma (max - min) and the
  // photo position of each cell, n cells on the long side.
  function quadGrid(src, corners, n) {
    const m = squareToQuad(corners);
    const a = sheetAspect(corners);
    const w = Math.max(8, Math.round(a >= 1 ? n : n * a)), h = Math.max(8, Math.round(a >= 1 ? n / a : n));
    const lum = new Float32Array(w * h), chroma = new Float32Array(w * h), rgb = new Float32Array(w * h * 3);
    const px = [0, 0, 0, 0];
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const [sx, sy] = apply3(m, (x + 0.5) / w, (y + 0.5) / h);
        sample(src, sx, sy, px);
        const i = y * w + x;
        lum[i] = lumOf(px[0], px[1], px[2]);
        chroma[i] = Math.max(px[0], px[1], px[2]) - Math.min(px[0], px[1], px[2]);
        rgb[i * 3] = px[0];
        rgb[i * 3 + 1] = px[1];
        rgb[i * 3 + 2] = px[2];
      }
    }
    return { w, h, lum, chroma, rgb };
  }

  function pct(arr, p) {
    const s = Float32Array.from(arr).sort();
    return s.length ? s[Math.min(s.length - 1, Math.floor(s.length * p))] : 0;
  }

  // ---- 1. finding the piece --------------------------------------------------

  // The paper: the largest bright patch of a small copy (Otsu's threshold), its
  // corners the extremes of x + y and x - y. A sheet that fills the photo, or
  // no clear sheet, falls back to the photo's own corners. `touches` is the
  // share of the photo's border the sheet runs into (the cut check).
  function findPaperInfo(img) {
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
    const full = wholePhoto(img);
    // A sheet down to 3 percent of the photo is still a sheet (it was 12 before
    // the small check: the check needs the sheet found to say "move closer").
    if (!bestPix || bestPix.length < n * 0.03 || bestPix.length > n * 0.97) return { corners: full, found: false, touches: 0 };
    let tl = [1e9, 0, 0], br = [-1e9, 0, 0], tr = [-1e9, 0, 0], bl = [1e9, 0, 0];
    let edge = 0;
    for (const i of bestPix) {
      const x = i % w, y = (i / w) | 0;
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) edge++;
      if (x + y < tl[0]) tl = [x + y, x, y];
      if (x + y > br[0]) br = [x + y, x, y];
      if (x - y > tr[0]) tr = [x - y, x, y];
      if (x - y < bl[0]) bl = [x - y, x, y];
    }
    // Pull each corner a little inside the sheet, off its shadowed edge.
    const pts = [tl, tr, br, bl].map((c) => [(c[1] + 0.5) / s, (c[2] + 0.5) / s]);
    const cx = pts.reduce((a, p) => a + p[0], 0) / 4, cy = pts.reduce((a, p) => a + p[1], 0) / 4;
    return { corners: pts.map(([x, y]) => [x + (cx - x) * 0.012, y + (cy - y) * 0.012]), found: true, touches: edge / (2 * (w + h)) };
  }

  function findPaper(img) {
    return findPaperInfo(img).corners;
  }

  // A painted piece, from the table inward: the table is what the photo's
  // border shows (a plane fitted to a band round the edge, per channel, so a
  // light falling off across the table is still table); the piece is the
  // largest patch that differs from it. A table that is not plain, or a
  // piece that runs off the photo on most sides, falls back to the whole
  // photo (found false: the page says "Drag the dots to the corners of your
  // piece.").
  function findPiece(img) {
    const s = Math.min(1, 260 / Math.max(img.width, img.height));
    const w = Math.max(8, Math.round(img.width * s)), h = Math.max(8, Math.round(img.height * s));
    const rgb = new Float32Array(w * h * 3);
    const px = [0, 0, 0, 0];
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        sample(img, (x + 0.5) / s - 0.5, (y + 0.5) / s - 0.5, px);
        const i = (y * w + x) * 3;
        rgb[i] = px[0];
        rgb[i + 1] = px[1];
        rgb[i + 2] = px[2];
      }
    }
    // A dark photo is brought up to a usual exposure first, so the table and
    // the piece differ by as much as they would in good light.
    const ls = new Float32Array(w * h);
    for (let i = 0; i < w * h; i++) ls[i] = lumOf(rgb[i * 3], rgb[i * 3 + 1], rgb[i * 3 + 2]);
    const top = pct(ls, 0.95);
    if (top < 200) {
      const gain = 200 / Math.max(20, top);
      for (let i = 0; i < rgb.length; i++) rgb[i] *= gain;
    }
    const full = { corners: wholePhoto(img), found: false, touches: 0 };
    const band = Math.max(2, Math.round(Math.min(w, h) * 0.04));
    const bandPts = [];
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        if (x < band || y < band || x >= w - band || y >= h - band) bandPts.push(y * w + x);
      }
    }
    // A robust fit: first to the band's closest half (a piece running off an
    // edge is in the band too), then to whatever is within a few of the
    // table's own spreads of it.
    let model = fitPlanes(rgb, w, h, bandPts);
    if (!model) return full;
    let res = bandPts.map((i) => resid(rgb, w, model, i));
    const half = pct(res, 0.5);
    let pts = bandPts.filter((_, k) => res[k] <= half);
    let spread = 0;
    for (let pass = 0; pass < 3; pass++) {
      model = fitPlanes(rgb, w, h, pts);
      if (!model) return full;
      res = bandPts.map((i) => resid(rgb, w, model, i));
      const inl = pts.map((i) => resid(rgb, w, model, i));
      spread = pct(inl, 0.5) * 1.4826 + 1;
      pts = bandPts.filter((_, k) => res[k] < Math.max(T.pieceMin, spread * T.pieceSpread));
      if (pts.length < 20) return full;
    }
    const plain = pts.length / bandPts.length;
    const thr = Math.max(T.pieceMin, spread * T.pieceSpread);
    const mask = new Uint8Array(w * h);
    for (let i = 0; i < w * h; i++) mask[i] = resid(rgb, w, model, i) > thr ? 1 : 0;
    const opened = dilate(erode(mask, w, h), w, h);
    const comp = largestComponent(opened, w, h);
    if (!comp || comp.length < w * h * 0.03 || comp.length > w * h * 0.97 || plain < 0.45) return full;
    let tl = [1e9, 0, 0], br = [-1e9, 0, 0], tr = [-1e9, 0, 0], bl = [1e9, 0, 0];
    let edge = 0;
    for (const i of comp) {
      const x = i % w, y = (i / w) | 0;
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) edge++;
      if (x + y < tl[0]) tl = [x + y, x, y];
      if (x + y > br[0]) br = [x + y, x, y];
      if (x - y > tr[0]) tr = [x - y, x, y];
      if (x - y < bl[0]) bl = [x - y, x, y];
    }
    const quad = [tl, tr, br, bl].map((c) => [(c[1] + 0.5) / s, (c[2] + 0.5) / s]);
    // A patch that is far from its own quad (a blob, not a piece) is not trusted.
    if (comp.length / (quadArea(quad) * s * s) < 0.6) return full;
    const cx = quad.reduce((a, p) => a + p[0], 0) / 4, cy = quad.reduce((a, p) => a + p[1], 0) / 4;
    return { corners: quad.map(([x, y]) => [x + (cx - x) * 0.008, y + (cy - y) * 0.008]), found: true, touches: edge / (2 * (w + h)) };
  }

  const surf = (x, y) => [1, x, y, x * x, x * y, y * y];

  // Per channel, a smooth surface (a quadratic in x and y) through the table's samples.
  function fitPlanes(rgb, w, h, pts) {
    const N = 6;
    const A = Array.from({ length: N }, () => new Array(N).fill(0));
    const rhs = [new Array(N).fill(0), new Array(N).fill(0), new Array(N).fill(0)];
    for (const i of pts) {
      const t = surf((i % w) / w, ((i / w) | 0) / h);
      for (let a = 0; a < N; a++) {
        for (let b = 0; b < N; b++) A[a][b] += t[a] * t[b];
        for (let k = 0; k < 3; k++) rhs[k][a] += t[a] * rgb[i * 3 + k];
      }
    }
    for (let a = 0; a < N; a++) A[a][a] += 1e-6;
    const out = [];
    for (let k = 0; k < 3; k++) {
      const c = solve(A, rhs[k]);
      if (!c) return null;
      out.push(c);
    }
    return { coef: out, w, h };
  }

  function resid(rgb, w, model, i) {
    const t = surf((i % w) / model.w, ((i / w) | 0) / model.h);
    let s = 0;
    for (let k = 0; k < 3; k++) {
      const c = model.coef[k];
      let v = 0;
      for (let j = 0; j < 6; j++) v += c[j] * t[j];
      const d = rgb[i * 3 + k] - v;
      s += d * d;
    }
    return Math.sqrt(s);
  }

  function erode(m, w, h) {
    const o = new Uint8Array(w * h);
    for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) {
      const i = y * w + x;
      o[i] = m[i] && m[i - 1] && m[i + 1] && m[i - w] && m[i + w] ? 1 : 0;
    }
    return o;
  }

  function dilate(m, w, h) {
    const o = new Uint8Array(w * h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const i = y * w + x;
      o[i] = m[i] || (x > 0 && m[i - 1]) || (x < w - 1 && m[i + 1]) || (y > 0 && m[i - w]) || (y < h - 1 && m[i + w]) ? 1 : 0;
    }
    return o;
  }

  function components(m, w, h) {
    const seen = new Uint8Array(w * h);
    const out = [];
    for (let start = 0; start < w * h; start++) {
      if (seen[start] || !m[start]) continue;
      const comp = [];
      const stack = [start];
      seen[start] = 1;
      while (stack.length) {
        const i = stack.pop();
        comp.push(i);
        const x = i % w, y = (i / w) | 0;
        if (x > 0 && !seen[i - 1] && m[i - 1]) { seen[i - 1] = 1; stack.push(i - 1); }
        if (x < w - 1 && !seen[i + 1] && m[i + 1]) { seen[i + 1] = 1; stack.push(i + 1); }
        if (y > 0 && !seen[i - w] && m[i - w]) { seen[i - w] = 1; stack.push(i - w); }
        if (y < h - 1 && !seen[i + w] && m[i + w]) { seen[i + w] = 1; stack.push(i + w); }
      }
      out.push(comp);
    }
    return out;
  }

  function largestComponent(m, w, h) {
    let best = null;
    for (const c of components(m, w, h)) if (!best || c.length > best.length) best = c;
    return best;
  }

  // ---- 2. the paper mode: straighten, level the paper, levels ---------------

  // How bright the paper is anywhere in the photo: a smooth surface (a
  // quadratic in the photo's x and y) fitted to the paper alone, the bright,
  // grey cells of a grid over the whole sheet, and the paper's tint. A drawing
  // that fills a region (a sky, a sea) is not paper and does not pull it: its
  // cells are coloured or darker than the paper and are left out. Light falls
  // off smoothly across a sheet, so the surface carries it under the drawing.
  function paperModel(src, corners) {
    const m = squareToQuad(corners);
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
            sample(src, sx, sy, px);
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
    const sw = src.width, sh = src.height;
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
    const raw = (sx, sy) => {
      if (!coef) return level;
      const t = terms(sx / sw, sy / sh);
      let v = 0;
      for (let i = 0; i < 6; i++) v += coef[i] * t[i];
      return v;
    };
    return {
      tint,
      level,
      fitted: !!coef,
      samples: ok.length,
      raw,
      at: (sx, sy) => (coef ? Math.max(floor, Math.min(255, raw(sx, sy))) : level),
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

  // The drawing's box on the sheet, in the sheet's own 0..1 coordinates: where a
  // small straightened copy, its paper levelled, is darker or more coloured than
  // paper. A margin of blank paper round a drawing is left out of the piece.
  function drawingBox(src, corners) {
    const m = squareToQuad(corners);
    const a = sheetAspect(corners);
    const n = 160, w = Math.max(8, Math.round(a >= 1 ? n : n * a)), h = Math.max(8, Math.round(a >= 1 ? n / a : n));
    const lum = new Float32Array(w * h), sat = new Float32Array(w * h);
    const px = [0, 0, 0, 0];
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const [sx, sy] = apply3(m, (x + 0.5) / w, (y + 0.5) / h);
        sample(src, sx, sy, px);
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

  function trimmedCorners(src, corners, trim) {
    if (!trim) return corners;
    const [u0, v0, u1, v1] = drawingBox(src, corners);
    const m = squareToQuad(corners);
    return [apply3(m, u0, v0), apply3(m, u1, v0), apply3(m, u1, v1), apply3(m, u0, v1)];
  }

  // The straightened sheet at the kind's canvas, its whites levelled: each
  // pixel divided by the paper's brightness and tint where it was in the photo
  // (paperModel), so shade and a phone's uneven light fall away. Returns the
  // levelled sheet (Float32Array rgb, paper about 1) before levels.
  function straightenPaper(src, corners, canvasWH, fit, trim) {
    const [W, H] = canvasWH;
    const cs = trimmedCorners(src, corners, trim);
    const m = squareToQuad(cs);
    const [sw, sh, ox, oy] = fitBox(sheetAspect(cs), W, H, fit);
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
        sample(src, sx, sy, px);
        srcXY[i * 2] = sx;
        srcXY[i * 2 + 1] = sy;
        rgb[i * 3] = px[0];
        rgb[i * 3 + 1] = px[1];
        rgb[i * 3 + 2] = px[2];
        inside[i] = 1;
      }
    }
    // The paper model reads the whole sheet the corners name, never the trimmed box.
    const paper = paperModel(src, corners);
    const flat = new Float32Array(W * H * 3);
    for (let i = 0; i < W * H; i++) {
      if (!inside[i]) {
        flat[i * 3] = flat[i * 3 + 1] = flat[i * 3 + 2] = 1;
        continue;
      }
      const bg = paper.at(srcXY[i * 2], srcXY[i * 2 + 1]);
      for (let k = 0; k < 3; k++) flat[i * 3 + k] = rgb[i * 3 + k] / (bg * paper.tint[k]);
    }
    return flat;
  }

  // ---- the game's colours ------------------------------------------------------

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

  // The nearest palette colour in Lab, cached on a 32-step cube.
  function makeSnapper(ramps) {
    const rgb = [];
    for (const ramp of Object.values(ramps)) for (const h of ramp) rgb.push(hexRgb(h));
    const lab = rgb.map((c) => toLab(c[0], c[1], c[2]));
    const cache = new Int16Array(32768).fill(-1);
    return (r, g, b) => {
      const key = ((r >> 3) << 10) | ((g >> 3) << 5) | (b >> 3);
      let idx = cache[key];
      if (idx < 0) {
        const L = toLab((r & 248) + 4, (g & 248) + 4, (b & 248) + 4);
        let best = 1e9;
        for (let i = 0; i < lab.length; i++) {
          const p = lab[i];
          const d = (p[0] - L[0]) ** 2 + (p[1] - L[1]) ** 2 + (p[2] - L[2]) ** 2;
          if (d < best) {
            best = d;
            idx = i;
          }
        }
        cache[key] = idx;
      }
      return rgb[idx];
    };
  }

  // The levelled sheet to the piece: Whites and Lines levels, the lift to
  // alpha, the snap. opts {whites, lines, lift}; snapper null or makeSnapper's.
  function finishPaper(flat, W, H, opts, snapper) {
    const out = makeImage(W, H);
    const d = out.data, f = flat;
    const lo = opts.lines, hi = Math.max(lo + 0.05, opts.whites);
    for (let i = 0; i < W * H; i++) {
      let r = clamp01((f[i * 3] - lo) / (hi - lo));
      let g = clamp01((f[i * 3 + 1] - lo) / (hi - lo));
      let b = clamp01((f[i * 3 + 2] - lo) / (hi - lo));
      let a = 1;
      if (opts.lift) {
        a = 1 - Math.min(r, g, b);
        if (a < 0.06) a = 0;
        if (a > 0) {
          r = clamp01(1 - (1 - r) / a);
          g = clamp01(1 - (1 - g) / a);
          b = clamp01(1 - (1 - b) / a);
        }
      }
      let R = r * 255, G = g * 255, B = b * 255;
      if (snapper) {
        if (opts.lift) a = a >= 0.45 ? 1 : 0;
        if (a > 0) [R, G, B] = snapper(R | 0, G | 0, B | 0);
      }
      d[i * 4] = R;
      d[i * 4 + 1] = G;
      d[i * 4 + 2] = B;
      d[i * 4 + 3] = a * 255;
    }
    return out;
  }

  // ---- 3. the painted mode: straighten only, then one even grade ------------

  // The corners' picture at the kind's canvas, nothing else done to it: rgb
  // 0..255 (Float32Array), white where the fit leaves a margin. Each canvas
  // pixel averages up to 3 x 3 bilinear samples when the photo holds several
  // pixels to it, so a big photo does not alias.
  function straightenPhoto(src, corners, canvasWH, fit) {
    const [W, H] = canvasWH;
    const m = squareToQuad(corners);
    const [sw, sh, ox, oy] = fitBox(sheetAspect(corners), W, H, fit);
    const foot = Math.sqrt(quadArea(corners) / Math.max(1, sw * sh));
    const k = Math.max(1, Math.min(3, Math.round(foot)));
    const rgb = new Float32Array(W * H * 3);
    const inside = new Uint8Array(W * H);
    const px = [0, 0, 0, 0];
    for (let y = 0; y < H; y++) {
      for (let x = 0; x < W; x++) {
        const i = y * W + x;
        const uc = (x + 0.5 - ox) / sw, vc = (y + 0.5 - oy) / sh;
        if (uc < 0 || uc > 1 || vc < 0 || vc > 1) {
          rgb[i * 3] = rgb[i * 3 + 1] = rgb[i * 3 + 2] = 255;
          continue;
        }
        let r = 0, g = 0, b = 0;
        for (let sy = 0; sy < k; sy++) {
          for (let sx = 0; sx < k; sx++) {
            const u = (x + (sx + 0.5) / k - ox) / sw, v = (y + (sy + 0.5) / k - oy) / sh;
            const [qx, qy] = apply3(m, u, v);
            sample(src, qx - 0.5, qy - 0.5, px);
            r += px[0];
            g += px[1];
            b += px[2];
          }
        }
        const kk = k * k;
        rgb[i * 3] = r / kk;
        rgb[i * 3 + 1] = g / kk;
        rgb[i * 3 + 2] = b / kk;
        inside[i] = 1;
      }
    }
    return { rgb, inside, W, H };
  }

  const toLin = (c) => (c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4));
  const toSrgb = (l) => (l <= 0.0031308 ? l * 12.92 : 1.055 * Math.pow(l, 1 / 2.4) - 0.055);
  let LIN_LUT = null, SRGB_LUT = null;
  const SRGB_N = 8192;
  function luts() {
    if (LIN_LUT) return;
    LIN_LUT = new Float32Array(1025);
    for (let i = 0; i <= 1024; i++) LIN_LUT[i] = toLin(i / 1024);
    SRGB_LUT = new Float32Array(SRGB_N + 1);
    for (let i = 0; i <= SRGB_N; i++) SRGB_LUT[i] = toSrgb(i / SRGB_N);
  }
  // 0..255 to linear light 0..1, and linear back to 0..1 encoded, by table.
  function lin255(v) {
    const x = Math.max(0, Math.min(1024, v * (1024 / 255)));
    const i = x | 0;
    return i >= 1024 ? LIN_LUT[1024] : LIN_LUT[i] + (LIN_LUT[i + 1] - LIN_LUT[i]) * (x - i);
  }
  function enc(l) {
    if (l <= 0) return 0;
    if (l >= 1) return 1;
    if (l < 0.0031308) return l * 12.92;
    const x = l * SRGB_N, i = x | 0;
    return SRGB_LUT[i] + (SRGB_LUT[i + 1] - SRGB_LUT[i]) * (x - i);
  }

  // The room light's cast: the lightest 3 percent of the piece (by linear
  // light) averaged, in linear light. art_repaint.py reads it the same way.
  function castOf(base) {
    luts();
    const { rgb, inside, W, H } = base;
    const ls = [];
    for (let i = 0; i < W * H; i++) if (inside[i]) ls.push((lin255(rgb[i * 3]) + lin255(rgb[i * 3 + 1]) + lin255(rgb[i * 3 + 2])) / 3);
    if (!ls.length) return [1, 1, 1];
    const cut = pct(ls, 0.97);
    let r = 0, g = 0, b = 0, n = 0;
    for (let i = 0; i < W * H; i++) {
      if (!inside[i]) continue;
      const R = lin255(rgb[i * 3]), G = lin255(rgb[i * 3 + 1]), B = lin255(rgb[i * 3 + 2]);
      if ((R + G + B) / 3 >= cut) {
        r += R;
        g += G;
        b += B;
        n++;
      }
    }
    return n ? [r / n, g / n, b / n] : [1, 1, 1];
  }

  // The three sliders as numbers: each -1..1, 0 is "as I shot it".
  //   bright  one gain in linear light, 2^(brightStops * bright); a brighter
  //           picture rolls its lightest paint into white on a shoulder
  //           instead of clipping it.
  //   colour  saturation about the light (Rec. 601 luma), 0.2x to 1.7x.
  //   warm    a red-to-blue gain in linear light. One end takes the room
  //           light's cast (castOf) out along that axis; the step is at
  //           least warmMin so a neutral photo still moves.
  function gradeParams(cast, opts) {
    const b = opts.bright || 0, c = opts.colour || 0, w = opts.warm || 0;
    const step = Math.max(T.warmMin, 0.5 * Math.log(Math.max(1e-4, cast[0]) / Math.max(1e-4, cast[2])));
    const t = w * step;
    let gR = Math.exp(t), gB = Math.exp(-t);
    const norm = 1 / (0.2126 * gR + 0.7152 + 0.0722 * gB);
    const G = Math.pow(2, T.brightStops * b);
    // Darkening is the gain on the channels; brightening applies it through the shoulder (gradePaint).
    const lo = G < 1 ? G : 1;
    return { gains: [gR * norm * lo, norm * lo, gB * norm * lo], G, S: c >= 0 ? 1 + 0.7 * c : 1 + 0.8 * c, identity: !b && !c && !w };
  }

  function shoulder(y, G) {
    if (G <= 1 || y <= T.knee) return y;
    const k = T.knee;
    const a = (G - 1) / ((1 - k) * (G - k));
    return k + (y - k) / (1 + a * (y - k));
  }

  // The straightened photo to the piece. opts {bright, colour, warm}; cast
  // from castOf; snapper null or makeSnapper's. All three at 0: the photo as
  // shot, byte for byte (rounded).
  function gradePaint(base, opts, cast, snapper) {
    luts();
    const { rgb, W, H } = base;
    const out = makeImage(W, H);
    const d = out.data;
    const p = gradeParams(cast, opts);
    for (let i = 0; i < W * H; i++) {
      let R, G, B;
      if (p.identity) {
        R = rgb[i * 3];
        G = rgb[i * 3 + 1];
        B = rgb[i * 3 + 2];
      } else {
        // The gain and its shoulder act on the light (linear luminance) and
        // scale the three channels together, so brightening keeps the colour;
        // a channel that would pass white is drawn back toward the light.
        let lr = lin255(rgb[i * 3]) * p.gains[0], lg = lin255(rgb[i * 3 + 1]) * p.gains[1], lb = lin255(rgb[i * 3 + 2]) * p.gains[2];
        const Y = 0.2126 * lr + 0.7152 * lg + 0.0722 * lb;
        if (Y > 1e-6 && p.G > 1) {
          const k = shoulder(Y * p.G, p.G) / Y;
          lr *= k;
          lg *= k;
          lb *= k;
          const Y2 = Y * k, mx = Math.max(lr, lg, lb);
          if (mx > 1 && Y2 < 1) {
            const t = (1 - Y2) / (mx - Y2);
            lr = Y2 + (lr - Y2) * t;
            lg = Y2 + (lg - Y2) * t;
            lb = Y2 + (lb - Y2) * t;
          }
        }
        let r = enc(lr), g = enc(lg), b = enc(lb);
        if (p.S !== 1) {
          const l = lumOf(r, g, b);
          r = clamp01(l + (r - l) * p.S);
          g = clamp01(l + (g - l) * p.S);
          b = clamp01(l + (b - l) * p.S);
        }
        R = r * 255;
        G = g * 255;
        B = b * 255;
      }
      if (snapper) [R, G, B] = snapper(Math.round(R), Math.round(G), Math.round(B));
      d[i * 4] = Math.round(R);
      d[i * 4 + 1] = Math.round(G);
      d[i * 4 + 2] = Math.round(B);
      d[i * 4 + 3] = 255;
    }
    return out;
  }

  // ---- 4. the screen mode: frame the picture, nothing else -------------------

  // The scale (canvas pixels per picture pixel) that covers the canvas, and
  // the one that shows the whole picture inside it.
  function coverScale(sw, sh, W, H) {
    return Math.max(W / sw, H / sh);
  }
  function wholeScale(sw, sh, W, H) {
    return Math.min(W / sw, H / sh);
  }

  // The view: centre (cx, cy) in the picture's pixels and a scale s. Returns
  // the crop {x, y, w, h} in the picture's pixels (it may run past the
  // picture: that part is margin). In an axis where the crop fits inside the
  // picture it is kept inside; where it does not, the picture is centred.
  function viewCrop(sw, sh, W, H, view) {
    const w = W / view.s, h = H / view.s;
    let x = view.cx - w / 2, y = view.cy - h / 2;
    x = w <= sw ? Math.max(0, Math.min(sw - w, x)) : (sw - w) / 2;
    y = h <= sh ? Math.max(0, Math.min(sh - h, y)) : (sh - h) / 2;
    return { x, y, w, h };
  }

  // One axis of an area (box) resample: for each of n outputs, the source
  // span [o + j * step, o + (j + 1) * step) as (index, weight) pairs over
  // 0..len. Weights are shares of the span; the part of a span outside the
  // picture has no pair (it is margin).
  function spans(o, step, n, len) {
    const idx = [], wts = [], start = new Int32Array(n + 1);
    for (let j = 0; j < n; j++) {
      start[j] = idx.length;
      const a = o + j * step, b = a + step;
      const lo = Math.max(0, Math.floor(a)), hi = Math.min(len, Math.ceil(b));
      for (let k = lo; k < hi; k++) {
        const wgt = (Math.min(b, k + 1) - Math.max(a, k)) / step;
        if (wgt > 0) {
          idx.push(k);
          wts.push(wgt);
        }
      }
    }
    start[n] = idx.length;
    return { idx: Int32Array.from(idx), wts: Float32Array.from(wts), start };
  }

  // The picture in the crop to a W x H piece. Reducing averages every
  // picture pixel under each piece pixel (premultiplied by alpha, so no dark
  // fringes), which is what keeps a big painting from shimmering. Enlarging
  // is bilinear (smooth) or whole-pixel blocks (blocky, for pixel art).
  // opts {smooth, ground: [r,g,b] or null, cutout}: a cutout keeps
  // see-through parts and the margin see-through; anything else is laid on
  // the ground colour.
  function screenRender(src, W, H, crop, opts) {
    const sw = src.width, sh = src.height, d = src.data;
    const out = makeImage(W, H);
    const o = out.data;
    const s = W / crop.w;
    if (s <= 1) {
      const hx = spans(crop.x, crop.w / W, W, sw), hy = spans(crop.y, crop.h / H, H, sh);
      const y0 = Math.max(0, Math.floor(crop.y)), y1 = Math.min(sh, Math.ceil(crop.y + crop.h));
      const rows = new Float32Array(Math.max(0, y1 - y0) * W * 4);
      for (let y = y0; y < y1; y++) {
        const ro = (y - y0) * W * 4, so = y * sw * 4;
        for (let j = 0; j < W; j++) {
          let r = 0, g = 0, b = 0, a = 0;
          for (let t = hx.start[j]; t < hx.start[j + 1]; t++) {
            const i = so + hx.idx[t] * 4, wgt = hx.wts[t] * d[i + 3];
            r += d[i] * wgt;
            g += d[i + 1] * wgt;
            b += d[i + 2] * wgt;
            a += wgt;
          }
          rows[ro + j * 4] = r;
          rows[ro + j * 4 + 1] = g;
          rows[ro + j * 4 + 2] = b;
          rows[ro + j * 4 + 3] = a;
        }
      }
      for (let i2 = 0; i2 < H; i2++) {
        for (let j = 0; j < W; j++) {
          let r = 0, g = 0, b = 0, a = 0;
          for (let t = hy.start[i2]; t < hy.start[i2 + 1]; t++) {
            const ri = ((hy.idx[t] - y0) * W + j) * 4, wgt = hy.wts[t];
            r += rows[ri] * wgt;
            g += rows[ri + 1] * wgt;
            b += rows[ri + 2] * wgt;
            a += rows[ri + 3] * wgt;
          }
          const oi = (i2 * W + j) * 4;
          if (a > 0) {
            o[oi] = Math.round(r / a);
            o[oi + 1] = Math.round(g / a);
            o[oi + 2] = Math.round(b / a);
          }
          o[oi + 3] = Math.round(a);
        }
      }
    } else {
      for (let y = 0; y < H; y++) {
        for (let x = 0; x < W; x++) {
          const fx = crop.x + (x + 0.5) / s, fy = crop.y + (y + 0.5) / s;
          const oi = (y * W + x) * 4;
          if (!opts.smooth) {
            const ix = Math.floor(fx), iy = Math.floor(fy);
            if (ix < 0 || iy < 0 || ix >= sw || iy >= sh) continue;
            const i = (iy * sw + ix) * 4;
            o[oi] = d[i];
            o[oi + 1] = d[i + 1];
            o[oi + 2] = d[i + 2];
            o[oi + 3] = d[i + 3];
            continue;
          }
          if (fx < 0 || fy < 0 || fx > sw || fy > sh) continue;
          // Bilinear, premultiplied, the picture's edge pixels held to its edge.
          const gx = Math.max(0, Math.min(sw - 1, fx - 0.5)), gy = Math.max(0, Math.min(sh - 1, fy - 0.5));
          const x0 = Math.min(sw - 2, gx | 0) < 0 ? 0 : Math.min(sw - 2, gx | 0), y0 = Math.min(sh - 2, gy | 0) < 0 ? 0 : Math.min(sh - 2, gy | 0);
          const x1 = Math.min(sw - 1, x0 + 1), y1 = Math.min(sh - 1, y0 + 1);
          const tx = Math.min(1, gx - x0), ty = Math.min(1, gy - y0);
          let r = 0, g = 0, b = 0, a = 0;
          for (const [xx, yy, wgt] of [[x0, y0, (1 - tx) * (1 - ty)], [x1, y0, tx * (1 - ty)], [x0, y1, (1 - tx) * ty], [x1, y1, tx * ty]]) {
            const i = (yy * sw + xx) * 4, al = d[i + 3] * wgt;
            r += d[i] * al;
            g += d[i + 1] * al;
            b += d[i + 2] * al;
            a += al;
          }
          if (a > 0) {
            o[oi] = Math.round(r / a);
            o[oi + 1] = Math.round(g / a);
            o[oi + 2] = Math.round(b / a);
          }
          o[oi + 3] = Math.round(a);
        }
      }
    }
    if (!opts.cutout) {
      const g = opts.ground || [255, 255, 255];
      for (let i = 0; i < W * H * 4; i += 4) {
        const a = o[i + 3] / 255;
        if (a >= 1) continue;
        o[i] = Math.round(o[i] * a + g[0] * (1 - a));
        o[i + 1] = Math.round(o[i + 1] * a + g[1] * (1 - a));
        o[i + 2] = Math.round(o[i + 2] * a + g[2] * (1 - a));
        o[i + 3] = 255;
      }
    }
    return out;
  }

  function hasAlpha(img) {
    const d = img.data;
    for (let i = 3; i < d.length; i += 4) if (d[i] < 250) return true;
    return false;
  }

  // How many distinct colours the picture has, up to cap (pixel art has few).
  function distinctColours(img, cap) {
    const seen = new Set();
    const d = img.data;
    for (let i = 0; i < d.length; i += 4) {
      seen.add(((d[i] << 16) | (d[i + 1] << 8) | d[i + 2]) * 2 + (d[i + 3] > 127 ? 1 : 0));
      if (seen.size > cap) return cap + 1;
    }
    return seen.size;
  }

  // A few ground colours read from the picture's own edge: the commonest
  // solid colours along its four sides, at most n, each distinct.
  function edgeSwatches(img, n) {
    const { width: w, height: h, data: d } = img;
    const counts = new Map();
    const add = (x, y) => {
      const i = (y * w + x) * 4;
      if (d[i + 3] < 200) return;
      const key = ((d[i] >> 4) << 8) | ((d[i + 1] >> 4) << 4) | (d[i + 2] >> 4);
      const c = counts.get(key) || [0, 0, 0, 0];
      c[0] += d[i];
      c[1] += d[i + 1];
      c[2] += d[i + 2];
      c[3]++;
      counts.set(key, c);
    };
    const step = Math.max(1, Math.floor(Math.max(w, h) / 400));
    for (let x = 0; x < w; x += step) {
      add(x, 0);
      add(x, h - 1);
    }
    for (let y = 0; y < h; y += step) {
      add(0, y);
      add(w - 1, y);
    }
    const all = [...counts.values()].sort((a, b) => b[3] - a[3]).map((c) => [Math.round(c[0] / c[3]), Math.round(c[1] / c[3]), Math.round(c[2] / c[3])]);
    const out = [];
    for (const c of all) {
      if (out.every((o) => Math.abs(o[0] - c[0]) + Math.abs(o[1] - c[1]) + Math.abs(o[2] - c[2]) > 60)) out.push(c);
      if (out.length >= n) break;
    }
    return out;
  }

  // ---- 5. the guard and the photo checks -------------------------------------

  // Does a photo, inside the corners, read as a painting? Measured on the
  // photo, never on the cleaned piece: the share of cells that look like bare
  // paper (near-neutral and near the brightest light in the piece), over the
  // whole piece and in its outer band (a tenth of the way in from each side).
  function paperShare(src, corners) {
    const g = quadGrid(src, corners, 96);
    const top = pct(g.lum, 0.95);
    let all = 0, ring = 0, nRing = 0;
    for (let y = 0; y < g.h; y++) {
      for (let x = 0; x < g.w; x++) {
        const i = y * g.w + x;
        const l = g.lum[i];
        const paper = g.chroma[i] < 0.12 * l + 6 && l >= top * 0.8 && l >= 25;
        if (paper) all++;
        const u = (x + 0.5) / g.w, v = (y + 0.5) / g.h;
        if (u < 0.1 || u > 0.9 || v < 0.1 || v > 0.9) {
          nRing++;
          if (paper) ring++;
        }
      }
    }
    return { all: all / (g.w * g.h), ring: ring / Math.max(1, nRing) };
  }

  function guard(src, corners) {
    const p = paperShare(src, corners);
    return { painted: p.ring < T.guardRing && p.all < T.guardAll, ring: p.ring, all: p.all };
  }

  // The checks, run on the photo once the piece is found. ctx {mode: "paper"
  // or "paint", canvas: [W, H], found (the finder's own corners, not a
  // fallback), touches (the finder's border share)}. Returns every check
  // that fired, worst first: {id, score (how far past its line, 0..),
  // where: [x, y] in the photo or null}, and the measurements.
  function checkPhoto(src, corners, ctx) {
    const fired = [];
    const m = {};
    const g = quadGrid(src, corners, 200);
    const whole = isWhole(src, corners);

    // dark
    m.light95 = pct(g.lum, 0.95);
    if (m.light95 < T.dark) fired.push({ id: "dark", score: 1 - m.light95 / T.dark, where: null });

    // uneven: paper from the paper fit; paint from the table round the piece.
    const un = unevenness(src, corners, ctx.mode, whole);
    m.uneven = un.ratio;
    if (un.ratio !== null && un.ratio < T.uneven) fired.push({ id: "uneven", score: (T.uneven - un.ratio) / T.uneven, where: un.where });

    // shine
    const sh = shine(g, corners, ctx.mode);
    m.shine = sh.area;
    m.shineHalo = sh.halo;
    if (sh.fired) fired.push({ id: "shine", score: Math.min(1, sh.area / T.shineArea / 10), where: sh.where });

    // blur
    m.sharp = sharpness(src, corners);
    if (m.sharp !== null && m.sharp < T.blur) fired.push({ id: "blur", score: (T.blur - m.sharp) / T.blur, where: null });

    // angle
    const an = angleOf(corners);
    m.angle = an.deg;
    m.sides = an.side;
    if (!whole && (an.deg > T.angleDeg || an.side < T.angleSide)) fired.push({ id: "angle", score: Math.max(an.deg / T.angleDeg - 1, 1 - an.side / T.angleSide), where: null });

    // small
    const [W, H] = ctx.canvas;
    const area = quadArea(corners);
    m.canvasShare = area / (W * H);
    m.photoShare = area / (src.width * src.height);
    if (m.canvasShare < T.smallCanvas || m.photoShare < T.smallShare) {
      fired.push({ id: "small", score: Math.max(1 - m.canvasShare / T.smallCanvas, 1 - m.photoShare / T.smallShare), where: null });
    }

    // cut
    const e = T.cutEdge * Math.max(src.width, src.height);
    let near = null;
    for (const c of corners) if (c[0] <= e || c[1] <= e || c[0] >= src.width - e || c[1] >= src.height - e) near = near || c;
    m.touches = ctx.touches || 0;
    if (!whole && (near || (ctx.found && m.touches > 0.02))) fired.push({ id: "cut", score: 1, where: near ? [near[0], near[1]] : null });

    fired.sort((a, b) => b.score - a.score);
    return { fired, m };
  }

  function unevenness(src, corners, mode, whole) {
    if (mode === "paper") {
      const p = paperModel(src, corners);
      if (p.fitted && p.samples >= 20) {
        const mq = squareToQuad(corners);
        let lo = 1e9, hi = -1e9, where = null;
        for (let v = 0.1; v <= 0.91; v += 0.2) {
          for (let u = 0.1; u <= 0.91; u += 0.2) {
            const [sx, sy] = apply3(mq, u, v);
            const l = p.raw(sx, sy);
            if (l < lo) {
              lo = l;
              where = [sx, sy];
            }
            hi = Math.max(hi, l);
          }
        }
        return { ratio: Math.max(0, lo) / Math.max(1, hi), where };
      }
    }
    if (whole) return { ratio: null, where: null };
    // The table round the piece: a band outside each side, its median light.
    const cx = corners.reduce((a, p) => a + p[0], 0) / 4, cy = corners.reduce((a, p) => a + p[1], 0) / 4;
    const out = corners.map(([x, y]) => [cx + (x - cx) * 1.12, cy + (y - cy) * 1.12]);
    const mid = corners.map(([x, y]) => [cx + (x - cx) * 1.05, cy + (y - cy) * 1.05]);
    const px = [0, 0, 0, 0];
    const sides = [];
    for (let k = 0; k < 4; k++) {
      const a0 = mid[k], a1 = mid[(k + 1) % 4], b0 = out[k], b1 = out[(k + 1) % 4];
      const vals = [];
      let sxm = 0, sym = 0;
      for (let t = 0.1; t <= 0.9; t += 0.05) {
        for (let r = 0; r <= 1; r += 0.25) {
          const x = a0[0] + (a1[0] - a0[0]) * t + ((b0[0] + (b1[0] - b0[0]) * t) - (a0[0] + (a1[0] - a0[0]) * t)) * r;
          const y = a0[1] + (a1[1] - a0[1]) * t + ((b0[1] + (b1[1] - b0[1]) * t) - (a0[1] + (a1[1] - a0[1]) * t)) * r;
          if (x < 0 || y < 0 || x >= src.width || y >= src.height) continue;
          sample(src, x, y, px);
          vals.push(lumOf(px[0], px[1], px[2]));
          sxm += x;
          sym += y;
        }
      }
      if (vals.length >= 30) sides.push({ l: pct(vals, 0.5), where: [sxm / vals.length, sym / vals.length] });
    }
    if (sides.length < 2) return { ratio: null, where: null };
    sides.sort((a, b) => a.l - b.l);
    return { ratio: sides[0].l / Math.max(1, sides[sides.length - 1].l), where: sides[0].where };
  }

  // A patch of clipped white with a soft edge: on a grid of the piece, the
  // largest patch of cells at full light, whose next cells out are still
  // most of the way from the piece's middle light to white (a glare fades;
  // a white shape painted on stops).
  const HALO_RING = 0;
  function shine(g, corners, mode) {
    const { w, h, lum } = g;
    // On paper, bright paper is not a shine: a shine is brighter than the paper itself.
    const line = mode === "paper" ? Math.max(T.shineLum, Math.min(254, pct(lum, 0.9) + 4)) : T.shineLum;
    const mask = new Uint8Array(w * h);
    let nClip = 0;
    for (let i = 0; i < w * h; i++) if (lum[i] >= line) { mask[i] = 1; nClip++; }
    const res = { fired: false, area: 0, halo: 0, where: null };
    if (!nClip || nClip / (w * h) > T.shineMaxShare) return res;
    const mid = pct(lum, 0.5);
    const m = squareToQuad(corners);
    for (const comp of components(mask, w, h)) {
      const area = comp.length / (w * h);
      if (area < res.area) continue;
      // The ring two and three cells out from the patch.
      const inC = new Uint8Array(w * h);
      for (const i of comp) inC[i] = 1;
      let d1 = inC;
      const rings = [];
      for (let r = 0; r < 3; r++) {
        const d2 = dilate(d1, w, h);
        const ring = [];
        for (let i = 0; i < w * h; i++) if (d2[i] && !d1[i]) ring.push(i);
        rings.push(ring);
        d1 = d2;
      }
      const ringL = rings[HALO_RING].length ? rings[HALO_RING].reduce((a, i) => a + lum[i], 0) / rings[HALO_RING].length : mid;
      const halo = (ringL - mid) / Math.max(1, 255 - mid);
      let sx = 0, sy = 0;
      for (const i of comp) {
        sx += ((i % w) + 0.5) / w;
        sy += (((i / w) | 0) + 0.5) / h;
      }
      res.area = area;
      res.halo = halo;
      res.where = apply3(m, sx / comp.length, sy / comp.length);
      res.fired = area >= T.shineArea && halo >= T.shineHalo;
    }
    return res;
  }

  // How sharp the piece's sharpest edges are: on the piece straightened at
  // about the photo's own resolution (at most 900 px), lightly smoothed, the
  // strongest 1 percent of edges' slope over 1 pixel against their slope
  // over 4. A sharp edge is steep over 1 pixel (about 2 to 3); a soft photo's
  // edges are as gentle close up as far off (about 1).
  function sharpness(src, corners) {
    const foot = Math.sqrt(quadArea(corners));
    const a = sheetAspect(corners);
    const long = Math.min(900, Math.round(foot * Math.sqrt(Math.max(a, 1 / a))));
    const w = Math.max(16, Math.round(a >= 1 ? long : long * a)), h = Math.max(16, Math.round(a >= 1 ? long / a : long));
    const m = squareToQuad(corners);
    const L = new Float32Array(w * h);
    const px = [0, 0, 0, 0];
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const [sx, sy] = apply3(m, (x + 0.5) / w, (y + 0.5) / h);
      sample(src, sx - 0.5, sy - 0.5, px);
      L[y * w + x] = lumOf(px[0], px[1], px[2]);
    }
    const S = new Float32Array(w * h);
    for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) {
      let s = 0;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) s += L[(y + dy) * w + x + dx];
      S[y * w + x] = s / 9;
    }
    const g1 = [], g4 = [];
    const mg = Math.max(6, Math.round(Math.min(w, h) * 0.04));
    for (let y = mg; y < h - mg; y += 1) {
      for (let x = mg; x < w - mg; x += 1) {
        const i = y * w + x;
        g4.push(Math.hypot((S[i + 4] - S[i - 4]) / 8, (S[i + 4 * w] - S[i - 4 * w]) / 8));
        g1.push(Math.hypot((S[i + 1] - S[i - 1]) / 2, (S[i + w] - S[i - w]) / 2));
      }
    }
    const coarse = pct(g4, 0.995);
    if (g1.length < 400 || coarse < 1.5) return null;
    return pct(g1, 0.995) / coarse;
  }

  function angleOf(c) {
    let worst = 0;
    for (let i = 0; i < 4; i++) {
      const p = c[i], a = c[(i + 3) % 4], b = c[(i + 1) % 4];
      const v1 = [a[0] - p[0], a[1] - p[1]], v2 = [b[0] - p[0], b[1] - p[1]];
      const cos = (v1[0] * v2[0] + v1[1] * v2[1]) / Math.max(1e-9, Math.hypot(...v1) * Math.hypot(...v2));
      worst = Math.max(worst, Math.abs(Math.acos(Math.max(-1, Math.min(1, cos))) * 180 / Math.PI - 90));
    }
    const s = [dist2(c[0], c[1]), dist2(c[1], c[2]), dist2(c[2], c[3]), dist2(c[3], c[0])];
    const side = Math.min(Math.min(s[0], s[2]) / Math.max(s[0], s[2]), Math.min(s[1], s[3]) / Math.max(s[1], s[3]));
    return { deg: worst, side };
  }

  // ---- measures (the tests, the proof, the intake) -----------------------------

  // Mean saturation ((max - min) / max) and the middle light (the median of
  // the channels' mean), both 0..1, over an image or rgb, and the share at
  // full white.
  function stats(img, mask) {
    const d = img.data, n = img.width * img.height;
    let sat = 0, cnt = 0, white = 0;
    const light = [];
    for (let i = 0; i < n; i++) {
      if (mask && !mask[i]) continue;
      const r = d[i * 4], g = d[i * 4 + 1], b = d[i * 4 + 2];
      const mx = Math.max(r, g, b), mn = Math.min(r, g, b);
      sat += mx > 0 ? (mx - mn) / mx : 0;
      light.push((r + g + b) / 765);
      if (mn >= 254) white++;
      cnt++;
    }
    return { sat: sat / Math.max(1, cnt), mid: pct(light, 0.5), white: white / Math.max(1, cnt), n: cnt };
  }

  // rgb (straightenPhoto's) as an image, ungraded: "Show my photo".
  function baseImage(base) {
    const { rgb, W, H } = base;
    const out = makeImage(W, H);
    for (let i = 0; i < W * H; i++) {
      out.data[i * 4] = Math.round(rgb[i * 3]);
      out.data[i * 4 + 1] = Math.round(rgb[i * 3 + 1]);
      out.data[i * 4 + 2] = Math.round(rgb[i * 3 + 2]);
      out.data[i * 4 + 3] = 255;
    }
    return out;
  }

  root.ArtPixels = {
    T,
    clamp01,
    hexRgb,
    makeImage,
    squareToQuad,
    invert3,
    apply3,
    sample,
    sheetAspect,
    quadArea,
    wholePhoto,
    isWhole,
    fitBox,
    findPaperInfo,
    findPaper,
    findPiece,
    paperModel,
    drawingBox,
    trimmedCorners,
    straightenPaper,
    finishPaper,
    makeSnapper,
    toLab,
    straightenPhoto,
    castOf,
    gradeParams,
    gradePaint,
    baseImage,
    coverScale,
    wholeScale,
    viewCrop,
    screenRender,
    hasAlpha,
    distinctColours,
    edgeSwatches,
    paperShare,
    guard,
    checkPhoto,
    sharpness,
    angleOf,
    stats,
  };
})(typeof globalThis !== "undefined" ? globalThis : this);

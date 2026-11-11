// The artist's tool (the hand-made art lane, 2026-11-10; the art desk for
// everyone, the same day). One static page: pick the kind, say how it was
// made (on paper, painted, on a screen), photograph it or choose the file,
// see it in the game, send it. The pixel work is in art_pixels.js (no DOM,
// shared with the server's tests); this file is the page: the screens, the
// editors, the preview in real renders of the game (frames.json) and the
// one call that sends. Only "Send it" and the greeting talk to a server: the
// pages function, with the artist's token from the link's #t= fragment. No
// AI image service is called, ever. No cookies, no analytics.
"use strict";

const CFG = window.ART_CONFIG;
const PX = window.ArtPixels;
const $ = (id) => document.getElementById(id);
const state = {
  token: "",
  artist: "",
  kind: null,
  frames: null,
  mode: "paper", // paper, paint or screen
  file: null,
  src: null, // the picture at work size, {width, height, data}
  natural: null, // [w, h] of the picture as decoded
  srcCanvas: null,
  corners: null,
  found: false,
  touches: 0,
  byHand: false,
  fit: "whole",
  whites: 0.95,
  lines: 0.04,
  lift: false,
  snap: false,
  trim: true,
  showBefore: false,
  showPhoto: false,
  bright: 0,
  colour: 0,
  warm: 0,
  flat: null,
  base: null,
  cast: null,
  view: null, // screen: {cx, cy, s}
  smooth: true,
  ground: [255, 255, 255],
  swatches: [],
  checks: [],
  anyway: false,
  guardSeen: false,
  piece: null,
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

function store(key, value) {
  try {
    if (value === undefined) return localStorage.getItem(key);
    localStorage.setItem(key, value);
  } catch {
    // private mode or blocked storage: the page works without it
  }
  return null;
}

function toImageData(img) {
  return new ImageData(img.data, img.width, img.height);
}

function pieceCanvas(piece) {
  const c = canvas(piece.width, piece.height);
  c.getContext("2d").putImageData(toImageData(piece), 0, 0);
  return c;
}

const hex = (c) => "#" + c.map((v) => v.toString(16).padStart(2, "0")).join("");

let snapper = null;
function snapFn() {
  if (!snapper) snapper = PX.makeSnapper(CFG.palette.ramps);
  return snapper;
}

const SVGNS = "http://www.w3.org/2000/svg";
function svgEl(name, attrs, parent) {
  const e = document.createElementNS(SVGNS, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, String(v));
  if (parent) parent.append(e);
  return e;
}

// ---- the kind: what it is, drawn ---------------------------------------------

// A small outline of the kind's shape, with what matters drawn on it: the
// repeat for a tile, the see-through paper for a cutout, the pass's calm
// middle, the splash's quiet top.
function kindShape(k) {
  const [W, H] = k.canvas;
  const s = 110 / Math.max(W, H);
  const w = Math.round(W * s), h = Math.round(H * s);
  const svg = svgEl("svg", { viewBox: `0 0 150 ${h + 40}`, role: "img", "aria-label": `${k.label}: its shape` });
  const x0 = Math.round((150 - w) / 2), y0 = 8;
  if (k.tile) {
    for (const [dx, dy] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) svgEl("rect", { class: "o-faint", x: x0 + dx * w, y: y0 + dy * h, width: w, height: h }, svg);
  }
  if (k.cutout) {
    svgEl("rect", { class: "o-check", x: x0, y: y0, width: w, height: h }, svg);
    svgEl("rect", { class: "o-dash", x: x0, y: y0, width: w, height: h }, svg);
    svgEl("circle", { class: "o-blob", cx: x0 + w / 2, cy: y0 + h / 2, r: Math.min(w, h) * 0.28 }, svg);
  } else {
    svgEl("rect", { class: "o-sheet", x: x0, y: y0, width: w, height: h }, svg);
  }
  if (k.id === "pass") svgEl("rect", { class: "o-band", x: x0 + w * 0.3, y: y0 + h * 0.25, width: w * 0.4, height: h * 0.5 }, svg);
  if (k.id === "splash") svgEl("rect", { class: "o-band", x: x0 + 2, y: y0 + 2, width: w - 4, height: h / 3 }, svg);
  if (k.tile) {
    svgEl("path", { class: "o-arrow", d: `M${x0 - 6} ${y0 + h / 2} l-8 0 M${x0 + w + 6} ${y0 + h / 2} l8 0` }, svg);
  }
  const t = svgEl("text", { class: "o-text", x: 75, y: h + 30, "text-anchor": "middle" }, svg);
  t.textContent = W > H ? "wider than tall" : W < H ? "taller than wide" : "square";
  return svg;
}

// ---- 1. the picture -------------------------------------------------------------

async function decode(file) {
  let bmp = null;
  try {
    bmp = await createImageBitmap(file, { imageOrientation: "from-image" });
  } catch {
    bmp = await new Promise((ok, bad) => {
      const im = new Image();
      const url = URL.createObjectURL(file);
      im.onload = () => ok(im);
      im.onerror = () => bad(new Error("not an image"));
      im.src = url;
    });
  }
  let w = bmp.naturalWidth || bmp.width, h = bmp.naturalHeight || bmp.height;
  // A drawing file (SVG) with no size of its own is drawn at a good size.
  if (!w || !h || /svg/i.test(file.type)) {
    const a = w && h ? w / h : 1;
    w = a >= 1 ? 2048 : Math.round(2048 * a);
    h = a >= 1 ? Math.round(2048 / a) : 2048;
  }
  return { bmp, w, h };
}

async function loadPicture(file) {
  const { bmp, w, h } = await decode(file);
  const s = Math.min(1, CFG.upload.work_px / Math.max(w, h));
  const c = canvas(Math.max(1, Math.round(w * s)), Math.max(1, Math.round(h * s)));
  const g = c.getContext("2d");
  g.imageSmoothingQuality = "high";
  g.drawImage(bmp, 0, 0, c.width, c.height);
  const d = g.getImageData(0, 0, c.width, c.height);
  return { img: { width: d.width, height: d.height, data: d.data }, natural: [w, h], canvas: c };
}

function headOf(bytes) {
  return String.fromCharCode(...bytes.slice(0, 16));
}

function servable(bytes) {
  const b = bytes;
  if (b[0] === 0xff && b[1] === 0xd8 && b[2] === 0xff) return true;
  if (b[0] === 0x89 && b[1] === 0x50 && b[2] === 0x4e && b[3] === 0x47) return true;
  const h = headOf(b);
  return h.startsWith("RIFF") && h.slice(8, 12) === "WEBP";
}

// A file that will not open: what it is (by its name and first bytes), and
// the steps in the app that made it. Each app's steps were checked against
// its own help pages (docs/slices/2026-11-10-art-desk-for-everyone.md).
const HELP = {
  procreate: ["a Procreate drawing", "In Procreate, open the drawing, tap Actions (the spanner), then Share, then PNG, and save the image. Then choose that PNG here."],
  psd: ["a Photoshop file", "In Photoshop, choose File, then Export, then Quick Export as PNG. Then choose that PNG here."],
  clip: ["a Clip Studio Paint file", "In Clip Studio Paint, choose File, then Export (single layer), then .png. Then choose that PNG here."],
  kra: ["a Krita file", "In Krita, choose File, then Export, and pick PNG as the type. Then choose that PNG here."],
  ipv: ["an ibisPaint file", "In ibisPaint, open the drawing, tap the Back button, then Save Image, and pick PNG. Then choose it from your photos here."],
  xcf: ["a GIMP file", "In GIMP, choose File, then Export As, give the name .png at the end, and tap Export. Then choose that PNG here."],
  ai: ["an Illustrator file", "In Illustrator, choose File, then Export, then Export As, and pick PNG. Then choose that PNG here."],
  affinity: ["an Affinity file", "In Affinity, choose File, then Export, and pick PNG at the top. Then choose that PNG here."],
  pdf: ["a PDF", "A PDF does not open here. If you made it in an app, export it from there as PNG or JPEG instead."],
  heic: ["an iPhone photo in HEIC", "This browser cannot open HEIC. To have your iPhone save photos this page can open: Settings, then Camera, then Formats, then Most Compatible."],
  tiff: ["a TIFF picture", "This browser cannot open TIFF. Open it in the app that made it and save or export it as PNG or JPEG."],
  svg: ["a drawing file (SVG)", "This one did not open here. Export it from your app as PNG instead."],
};

function fileKind(name, b) {
  const ext = (name.split(".").pop() || "").toLowerCase();
  const h = headOf(b);
  const zip = b[0] === 0x50 && b[1] === 0x4b;
  if (ext === "procreate") return "procreate";
  if (ext === "psd" || ext === "psb" || h.startsWith("8BPS")) return "psd";
  if (ext === "clip" || h.startsWith("CSFCHUNK")) return "clip";
  if (ext === "kra") return "kra";
  if (ext === "ipv") return "ipv";
  if (ext === "xcf" || h.startsWith("gimp xcf")) return "xcf";
  if (ext === "ai" || ext === "eps") return "ai";
  if (/^af(photo|design|pub)?$/.test(ext)) return "affinity";
  if (ext === "pdf" || h.startsWith("%PDF")) return "pdf";
  if (ext === "heic" || ext === "heif" || /ftyp(heic|heix|heim|heis|mif1|msf1)/.test(h)) return "heic";
  if (ext === "tif" || ext === "tiff" || h.startsWith("II*\u0000") || h.startsWith("MM\u0000*")) return "tiff";
  if (ext === "svg") return "svg";
  if (zip) return "procreate";
  return "";
}

function fileHelp(name, bytes) {
  const box = $("file-help");
  const k = fileKind(name, bytes);
  const parts = [];
  if (k) {
    parts.push(["b", `That file is ${HELP[k][0]}, and it does not open in a web page.`]);
    parts.push(["", HELP[k][1]]);
  } else {
    parts.push(["b", "This browser cannot open that picture."]);
  }
  parts.push(["", "Or open your picture so it fills the screen, take a screenshot, and choose the screenshot here. You can crop it on the next step."]);
  box.replaceChildren(...parts.map(([tag, text]) => {
    const p = document.createElement("p");
    if (tag) {
      const b = document.createElement("b");
      b.textContent = text;
      p.append(b);
    } else p.textContent = text;
    return p;
  }));
  box.className = "note error";
  box.hidden = false;
}

// ---- 2. the preview: the piece in the game's own renders -----------------------

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
  const inv = PX.invert3(PX.squareToQuad(pts));
  const W = dst.width, d = dst.data;
  const keys = (q.keys || []).map((k) => [k[0], k[1], k[2], 0.299 * k[0] + 0.587 * k[1] + 0.114 * k[2]]);
  const tol = q.tol ?? 40;
  const reps = q.repeat || [1, 1];
  const minX = Math.max(0, Math.floor(Math.min(...pts.map((p) => p[0])))), maxX = Math.min(W - 1, Math.ceil(Math.max(...pts.map((p) => p[0]))));
  const minY = Math.max(0, Math.floor(Math.min(...pts.map((p) => p[1])))), maxY = Math.min(dst.height - 1, Math.ceil(Math.max(...pts.map((p) => p[1]))));
  const px = [0, 0, 0, 0];
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      let [u, v] = PX.apply3(inv, x + 0.5, y + 0.5);
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
      PX.sample(piece, u * piece.width - 0.5, v * piece.height - 0.5, px);
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

// ---- 3. making the piece ------------------------------------------------------------

function screenCrop() {
  const [W, H] = state.kind.canvas;
  return PX.viewCrop(state.src.width, state.src.height, W, H, state.view);
}

// Builds the piece the current settings make. geometry: the corners, fit or
// framing changed, so the slow part (straightening) runs again.
function makePiece(geometry) {
  const [W, H] = state.kind.canvas;
  if (state.mode === "paper") {
    if (geometry || !state.flat) state.flat = PX.straightenPaper(state.src, state.corners, state.kind.canvas, state.fit, state.trim);
    const opts = { whites: state.whites, lines: state.lines, lift: state.lift };
    const piece = PX.finishPaper(state.flat, W, H, opts, state.snap ? snapFn() : null);
    const shown = state.snap && state.showBefore ? PX.finishPaper(state.flat, W, H, opts, null) : piece;
    return { piece, shown };
  }
  if (state.mode === "paint") {
    if (geometry || !state.base) {
      state.base = PX.straightenPhoto(state.src, state.corners, state.kind.canvas, state.fit);
      state.cast = PX.castOf(state.base);
    }
    const opts = { bright: state.bright, colour: state.colour, warm: state.warm };
    const piece = PX.gradePaint(state.base, opts, state.cast, state.snap ? snapFn() : null);
    let shown = piece;
    if (state.showPhoto) shown = PX.baseImage(state.base);
    else if (state.snap && state.showBefore) shown = PX.gradePaint(state.base, opts, state.cast, null);
    return { piece, shown };
  }
  const piece = PX.screenRender(state.src, W, H, screenCrop(), { smooth: state.smooth, ground: state.ground, cutout: !!state.kind.cutout });
  return { piece, shown: piece };
}

function drawPiece(shown) {
  const p = $("piece");
  const [W, H] = state.kind.canvas;
  p.width = W;
  p.height = H;
  const g = p.getContext("2d");
  g.drawImage(checker(W, H), 0, 0);
  g.drawImage(pieceCanvas(shown), 0, 0);
  let cap = `The piece itself, ${W} by ${H} pixels`;
  if (state.mode === "paint" && state.showPhoto) cap = "Your photo, only straightened: nothing else changed.";
  else if (shown.data.some((v, i) => i % 4 === 3 && v < 255)) cap += ". The squares show through where it is see-through.";
  else cap += ".";
  $("piece-cap").textContent = cap;
}

let renderGen = 0;

// Builds the preview off the page and swaps it in only if no newer edit has
// started meanwhile, so quick slider moves never leave two previews behind.
async function render(geometry) {
  if (!state.src) return;
  const gen = ++renderGen;
  const { piece, shown } = makePiece(geometry);
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
  drawPiece(shown);
  $("before").hidden = !state.snap;
  $("before").textContent = state.showBefore ? "Show the game's colours" : "Show before the colours changed";
  $("show-photo").hidden = state.mode !== "paint";
  $("show-photo").setAttribute("aria-pressed", String(state.showPhoto));
  $("show-photo").textContent = state.showPhoto ? "Show the piece" : "Show my photo";
}

// While a slider is dragged only the piece itself is redrawn (fast); the
// frames follow on release.
function quick() {
  if (!state.src) return;
  const { piece, shown } = makePiece(false);
  state.piece = piece;
  drawPiece(shown);
}

let pending = null;
function rework(geometry) {
  clearTimeout(pending);
  pending = setTimeout(async () => {
    $("working").hidden = false;
    await new Promise((r) => requestAnimationFrame(() => setTimeout(r, 0)));
    await render(geometry);
    $("working").hidden = true;
  }, 30);
}

// ---- the corner editor ------------------------------------------------------------

function drawCorners() {
  const c = $("paper");
  const img = state.src;
  const s = Math.min(1, 900 / Math.max(img.width, img.height));
  c.width = Math.round(img.width * s);
  c.height = Math.round(img.height * s);
  c.dataset.scale = String(s);
  const g = c.getContext("2d");
  g.drawImage(state.srcCanvas, 0, 0, c.width, c.height);
  const p = state.corners.map(([x, y]) => [x * s, y * s]);
  g.lineWidth = Math.max(2, c.width / 220);
  g.strokeStyle = "#e4572e";
  g.beginPath();
  p.forEach(([x, y], i) => (i ? g.lineTo(x, y) : g.moveTo(x, y)));
  g.closePath();
  g.stroke();
  if (state.mode === "paper" && state.trim) {
    const t = PX.trimmedCorners(state.src, state.corners, true).map(([x, y]) => [x * s, y * s]);
    g.setLineDash([g.lineWidth * 3, g.lineWidth * 2]);
    g.strokeStyle = "#1f5fae";
    g.beginPath();
    t.forEach(([x, y], i) => (i ? g.lineTo(x, y) : g.moveTo(x, y)));
    g.closePath();
    g.stroke();
    g.setLineDash([]);
  }
  const r = Math.max(12, c.width / 36);
  p.forEach(([x, y], i) => {
    g.fillStyle = i === 0 ? "#ffd23f" : "#fff";
    g.strokeStyle = "#2a1e14";
    g.lineWidth = Math.max(2, c.width / 300);
    g.beginPath();
    g.arc(x, y, r, 0, Math.PI * 2);
    g.fill();
    g.stroke();
  });
}

function setTrim(on) {
  state.trim = on;
  $("trim").checked = on;
}

function wireCorners() {
  const c = $("paper");
  let drag = -1;
  let moved = false;
  const at = (e) => {
    const b = c.getBoundingClientRect();
    const s = Number(c.dataset.scale);
    return [((e.clientX - b.left) / b.width) * c.width / s, ((e.clientY - b.top) / b.height) * c.height / s];
  };
  c.addEventListener("pointerdown", (e) => {
    const [x, y] = at(e);
    moved = false;
    const b = c.getBoundingClientRect();
    // A thumb's reach: 48 px on the screen, whatever the photo's size.
    const reach = (48 / b.width) * c.width / Number(c.dataset.scale);
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
    moved = true;
    state.byHand = true;
    // A dot set by hand is the frame: the blue trim steps aside so what is kept is exactly the dots.
    if (state.trim) setTrim(false);
    drawCorners();
  });
  const end = () => {
    if (drag < 0) return;
    drag = -1;
    if (moved) rework(true);
    moved = false;
  };
  c.addEventListener("pointerup", end);
  c.addEventListener("pointercancel", end);
}

// ---- the screen framing editor -------------------------------------------------------

function scaleRange() {
  const [W, H] = state.kind.canvas;
  const sw = state.src.width, sh = state.src.height;
  const cover = PX.coverScale(sw, sh, W, H), whole = PX.wholeScale(sw, sh, W, H);
  const lo = Math.min(cover, whole), hi = Math.max(cover * 4, whole * 1.01);
  return { lo, hi, cover, whole };
}

function setScale(s) {
  const { lo, hi } = scaleRange();
  s = Math.max(lo, Math.min(hi, s));
  if (!state.smooth && s >= 1) s = Math.max(1, Math.round(s));
  state.view.s = s;
  $("zoom").value = String(Math.round((100 * Math.log(s / lo)) / Math.log(hi / lo)));
  const { cover } = scaleRange();
  $("zoom-v").textContent = Math.abs(s - cover) / cover < 0.02 ? "fills the frame" : s < cover ? "the whole picture shows" : "zoomed in";
}

function drawFrameEditor() {
  const c = $("frame-ed");
  const [W, H] = state.kind.canvas;
  const dw = 360, dh = Math.round((360 * H) / W);
  c.width = dw;
  c.height = dh;
  const g = c.getContext("2d");
  if (state.kind.cutout) g.drawImage(checker(dw, dh), 0, 0);
  else {
    g.fillStyle = hex(state.ground);
    g.fillRect(0, 0, dw, dh);
  }
  const cr = screenCrop();
  const k = dw / cr.w;
  g.imageSmoothingEnabled = state.smooth;
  g.imageSmoothingQuality = "high";
  // The picture's own rectangle, placed in the frame.
  g.drawImage(state.srcCanvas, -cr.x * k, -cr.y * k, state.src.width * k, state.src.height * k);
}

// What the screen mode needs to show: the ground colours (a solid kind with
// see-through parts or a margin), the cutout line, Smooth or Blocky.
function screenOptions() {
  const [W, H] = state.kind.canvas;
  const cr = screenCrop();
  const margin = cr.x < -0.5 || cr.y < -0.5 || cr.x + cr.w > state.src.width + 0.5 || cr.y + cr.h > state.src.height + 0.5;
  const alpha = PX.hasAlpha(state.src);
  const needGround = !state.kind.cutout && (alpha || margin);
  $("ground-row").hidden = !needGround;
  if (needGround) {
    $("ground-line").textContent = alpha
      ? "This kind needs a solid background. The see-through parts of your picture, and any edge left round it, get the colour you pick here."
      : "This kind needs a solid background. The edge left round your picture gets the colour you pick here.";
  }
  $("cutout-line").hidden = !state.kind.cutout;
  $("cutout-line").textContent = "See-through parts stay see-through. In the game only your picture shows, with nothing round it.";
  const { cover } = scaleRange();
  $("smooth-row").hidden = !(cover > 2);
  void W;
  void H;
}

function drawSwatches() {
  const box = $("swatches");
  const all = [...state.swatches, [255, 255, 255]].filter((c, i, a) => a.findIndex((d) => hex(d) === hex(c)) === i);
  box.replaceChildren(...all.map((c) => {
    const b = document.createElement("button");
    b.type = "button";
    b.className = "swatch";
    b.setAttribute("role", "radio");
    b.setAttribute("aria-checked", String(hex(c) === hex(state.ground)));
    b.setAttribute("aria-label", hex(c) === "#ffffff" ? "White" : `A colour from your picture's edge, ${hex(c)}`);
    b.style.background = hex(c);
    b.addEventListener("click", () => {
      state.ground = c;
      drawSwatches();
      drawFrameEditor();
      rework(true);
    });
    return b;
  }));
}

function wireFrameEditor() {
  const c = $("frame-ed");
  const pts = new Map();
  let pinch = 0;
  c.addEventListener("pointerdown", (e) => {
    c.setPointerCapture(e.pointerId);
    pts.set(e.pointerId, [e.clientX, e.clientY]);
    if (pts.size === 2) {
      const [a, b] = [...pts.values()];
      pinch = Math.hypot(a[0] - b[0], a[1] - b[1]);
    }
    e.preventDefault();
  });
  c.addEventListener("pointermove", (e) => {
    if (!pts.has(e.pointerId)) return;
    const prev = pts.get(e.pointerId);
    pts.set(e.pointerId, [e.clientX, e.clientY]);
    const b = c.getBoundingClientRect();
    const cr = screenCrop();
    if (pts.size === 1) {
      const k = cr.w / b.width;
      state.view.cx = cr.x + cr.w / 2 - (e.clientX - prev[0]) * k;
      state.view.cy = cr.y + cr.h / 2 - (e.clientY - prev[1]) * k;
    } else if (pts.size === 2) {
      const [a, d] = [...pts.values()];
      const dist = Math.hypot(a[0] - d[0], a[1] - d[1]);
      if (pinch > 0) setScale(state.view.s * (dist / pinch));
      pinch = dist;
    }
    drawFrameEditor();
  });
  const end = (e) => {
    if (!pts.has(e.pointerId)) return;
    pts.delete(e.pointerId);
    pinch = 0;
    // Keep the centre where the crop now is (it may have been held inside the picture).
    const cr = screenCrop();
    state.view.cx = cr.x + cr.w / 2;
    state.view.cy = cr.y + cr.h / 2;
    if (pts.size === 0) {
      screenOptions();
      rework(true);
    }
  };
  c.addEventListener("pointerup", end);
  c.addEventListener("pointercancel", end);
}

// ---- the checks ------------------------------------------------------------------------

const CHECK_TEXT = {
  dark: "The photo is dark. Move next to a window and take it again.",
  uneven: "One side is in shadow. Turn so the light falls evenly, and keep your own shadow off it.",
  shine: "There is a bright shine here. Turn the piece or step to the side until it goes.",
  blur: "The photo is soft. Tap the piece on your screen to focus, hold still, and take it again.",
  angle: "This was taken from the side. Hold the phone flat above the piece.",
  small: "The piece is small in this photo. Move closer so it nearly fills the picture.",
  cut: "A corner is cut off. Step back so the whole piece and a little table are in the picture.",
};

function runChecks() {
  const r = PX.checkPhoto(state.src, state.corners, { mode: state.mode, canvas: state.kind.canvas, found: state.found, touches: state.touches });
  return r.fired;
}

function checkThumb(fault) {
  const img = state.src;
  const s = 280 / Math.max(img.width, img.height);
  const c = canvas(Math.round(img.width * s), Math.round(img.height * s));
  const g = c.getContext("2d");
  g.drawImage(state.srcCanvas, 0, 0, c.width, c.height);
  g.strokeStyle = "#e4572e";
  g.lineWidth = 3;
  g.beginPath();
  state.corners.forEach(([x, y], i) => (i ? g.lineTo(x * s, y * s) : g.moveTo(x * s, y * s)));
  g.closePath();
  g.stroke();
  if (fault.where) {
    g.strokeStyle = "#ffd23f";
    g.lineWidth = 5;
    g.beginPath();
    g.arc(fault.where[0] * s, fault.where[1] * s, 22, 0, Math.PI * 2);
    g.stroke();
  }
  c.setAttribute("aria-hidden", "true");
  return c;
}

function showChecks(fired) {
  const list = $("check-list");
  list.replaceChildren(...fired.slice(0, 2).map((f) => {
    const d = document.createElement("div");
    d.className = "check-item";
    const p = document.createElement("p");
    p.textContent = CHECK_TEXT[f.id];
    d.append(checkThumb(f), p);
    return d;
  }));
  show("check");
}

// ---- the flow --------------------------------------------------------------------------

function pickKind(k) {
  state.kind = k;
  $("kind-name").textContent = k.label;
  $("kind-shape").replaceChildren(kindShape(k));
  $("kind-tips").replaceChildren(...(k.tips || [k.hint]).map((t) => {
    const li = document.createElement("li");
    li.textContent = t;
    return li;
  }));
  $("kind-where").textContent = k.object
    ? "We build it in 3D from your drawing, by hand. You get a picture of it to approve before it goes in."
    : k.in_game
      ? "It is in the game now: it shows as you made it."
      : "It shows in the game as you made it. Its place in the game gets set up the first time one arrives, so this one takes a little longer.";
  show("mode");
}

function pickMode(mode) {
  state.mode = mode;
  const titles = { paper: "Your drawing on paper", paint: "Your painted or coloured piece", screen: "Your picture file" };
  $("pic-title").textContent = titles[mode];
  $("pic-now").textContent = mode === "screen"
    ? "Next: choose the file. Then you see it in the game and can frame it."
    : "Next: take a photo of it, or choose one you took. Then the desk finds the piece, straightens it and shows it in the game.";
  $("photo-in").hidden = mode === "screen";
  $("screen-in").hidden = mode !== "screen";
  $("paint-more").hidden = mode !== "paint";
  $("table-line").textContent = mode === "paint" ? "Anything plain that is not your piece's own colour." : "Darker than the paper for a drawing.";
  $("take-label").hidden = false;
  for (const id of ["take-input", "choose-input", "file-input"]) $(id).value = "";
  say($("photo-msg"), "", "");
  $("file-help").hidden = true;
  show("picture");
}

function resetSettings() {
  state.piece = null;
  state.flat = null;
  state.base = null;
  state.snap = false;
  state.showBefore = false;
  state.showPhoto = false;
  state.bright = state.colour = state.warm = 0;
  state.whites = 0.95;
  state.lines = 0.04;
  state.lift = !!state.kind.cutout;
  state.anyway = false;
  state.guardSeen = false;
  state.byHand = false;
  $("frames").replaceChildren();
  $("name").value = "";
  $("note").value = "";
  say($("send-msg"), "", "");
}

// The finder for the mode, the fit and trim it starts with.
function findFor(mode) {
  const f = mode === "paint" ? PX.findPiece(state.src) : PX.findPaperInfo(state.src);
  return f;
}

function modeDefaults() {
  if (state.mode === "paint") {
    state.fit = "fill";
    setTrim(false);
  } else {
    state.fit = "whole";
    setTrim(!state.kind.tile);
  }
  $(state.fit === "fill" ? "fit-fill" : "fit-whole").checked = true;
}

async function takePhoto(file) {
  if (!file) return;
  state.file = file;
  say($("photo-msg"), "Reading the photo...", "");
  let pic;
  try {
    pic = await loadPicture(file);
  } catch {
    say($("photo-msg"), "That file did not open as a picture. Try a photo from your camera (JPEG), or take a screenshot of it and choose that.", "error");
    return;
  }
  say($("photo-msg"), "Looking at the photo...", "");
  await new Promise((r) => requestAnimationFrame(() => setTimeout(r, 0)));
  state.src = pic.img;
  state.natural = pic.natural;
  state.srcCanvas = pic.canvas;
  resetSettings();
  const f = findFor(state.mode);
  state.corners = f.corners;
  state.found = f.found;
  state.touches = f.touches;
  modeDefaults();
  const fired = runChecks();
  state.checks = fired.map((x) => x.id);
  say($("photo-msg"), "", "");
  if (fired.length) showChecks(fired);
  else openPreview(true);
}

async function takeFile(file) {
  if (!file) return;
  state.file = file;
  $("file-help").hidden = true;
  const head = new Uint8Array(await file.slice(0, 64).arrayBuffer());
  let pic;
  try {
    pic = await loadPicture(file);
  } catch {
    fileHelp(file.name || "", head);
    return;
  }
  state.src = pic.img;
  state.natural = pic.natural;
  state.srcCanvas = pic.canvas;
  resetSettings();
  state.checks = [];
  const [W, H] = state.kind.canvas;
  state.view = { cx: state.src.width / 2, cy: state.src.height / 2, s: PX.coverScale(state.src.width, state.src.height, W, H) };
  state.smooth = PX.distinctColours(state.src, 64) > 64;
  $(state.smooth ? "sm-smooth" : "sm-blocky").checked = true;
  state.swatches = PX.edgeSwatches(state.src, 3);
  state.ground = PX.hasAlpha(state.src) && state.swatches.length ? state.swatches[0] : [255, 255, 255];
  setScale(state.view.s);
  openPreview(false);
}

function openPreview(good) {
  show("preview");
  $("pv-kind").textContent = state.kind.label;
  const screen = state.mode === "screen";
  $("mode-switch").hidden = screen;
  $("sw-paper").checked = state.mode === "paper";
  $("sw-paint").checked = state.mode === "paint";
  $("good").hidden = !good;
  $("ed-photo").hidden = screen;
  $("ed-paper").hidden = state.mode !== "paper";
  $("ed-paint").hidden = state.mode !== "paint";
  $("ed-screen").hidden = !screen;
  $("trim-row").hidden = state.mode !== "paper";
  $("dots-line").textContent = state.found || screen
    ? "Drag the four dots to the corners of your piece. The yellow dot is its top left."
    : "Drag the dots to the corners of your piece.";
  $("lift").checked = state.lift;
  $("snap").checked = false;
  $("whites").value = String(state.whites);
  $("lines").value = String(state.lines);
  for (const k of ["bright", "colour", "warm"]) $(k).value = "0";
  sliderWords();
  guardCheck();
  // The details are open the first time someone uses the desk on this device.
  const seen = store("art_desk_seen") === "1";
  $("edit").open = !seen || (!state.found && !screen);
  store("art_desk_seen", "1");
  if (screen) {
    screenOptions();
    drawSwatches();
    drawFrameEditor();
  } else drawCorners();
  rework(true);
}

function guardCheck() {
  let painted = false;
  if (state.mode === "paper" && !state.guardSeen) painted = PX.guard(state.src, state.corners).painted;
  $("guard").hidden = !painted;
}

function switchMode(mode) {
  if (mode === state.mode) return;
  const old = { corners: state.corners, found: state.found, touches: state.touches };
  state.mode = mode;
  if (!state.byHand) {
    const f = findFor(mode);
    if (f.found || !old.found) {
      state.corners = f.corners;
      state.found = f.found;
      state.touches = f.touches;
    }
  }
  state.flat = null;
  state.base = null;
  state.showPhoto = false;
  state.checks = runChecks().map((x) => x.id);
  modeDefaults();
  state.lift = mode === "paper" && !!state.kind.cutout;
  openPreview(false);
}

const WORDS = {
  bright: ["much darker", "a bit darker", "as you shot it", "a bit brighter", "much brighter"],
  colour: ["much less colour", "a bit less colour", "as you shot it", "a bit more colour", "much more colour"],
  warm: ["much cooler", "a bit cooler", "as you shot it", "a bit warmer", "much warmer"],
};

function word(list, v) {
  return list[v < -0.6 ? 0 : v < -0.12 ? 1 : v <= 0.12 ? 2 : v <= 0.6 ? 3 : 4];
}

function sliderWords() {
  for (const k of ["bright", "colour", "warm"]) $(k + "-v").textContent = word(WORDS[k], state[k]);
  $("whites-v").textContent = state.whites >= 0.98 ? "a little" : state.whites >= 0.85 ? "some" : "a lot";
  $("lines-v").textContent = state.lines <= 0.05 ? "a little" : state.lines <= 0.25 ? "some" : "a lot";
}

function blob(c, type, q) {
  return new Promise((ok) => c.toBlob(ok, type, q));
}

// The photo CasPop keeps: the original file when the server takes it as it
// is (JPEG, PNG or WebP by its first bytes, inside the limit), else a copy
// the page makes: PNG when the picture has see-through parts, JPEG when not.
async function photoBlob() {
  const f = state.file;
  const head = new Uint8Array(await f.slice(0, 16).arrayBuffer());
  if (servable(head) && f.size <= CFG.upload.photo_max_bytes) return f;
  const png = state.mode === "screen" && PX.hasAlpha(state.src);
  let c = state.srcCanvas;
  for (let i = 0; i < 6; i++) {
    const b = await blob(c, png ? "image/png" : "image/jpeg", 0.9);
    if (b && b.size <= CFG.upload.photo_max_bytes) return b;
    const smaller = canvas(Math.round(c.width * 0.75), Math.round(c.height * 0.75));
    smaller.getContext("2d").drawImage(c, 0, 0, smaller.width, smaller.height);
    c = smaller;
  }
  throw new Error("The picture is too large to send, even made smaller. Try a screenshot of it.");
}

function settings() {
  const base = { mode: state.mode, checks: state.checks, anyway: state.anyway };
  if (state.mode === "screen") {
    const cr = screenCrop();
    const k = state.natural[0] / state.src.width;
    return {
      ...base,
      crop: [cr.x, cr.y, cr.w, cr.h].map((v) => Math.round(v * k)),
      source: state.natural,
      ground: state.kind.cutout ? null : hex(state.ground),
      smooth: state.smooth,
    };
  }
  const common = {
    ...base,
    corners: state.corners.map(([x, y]) => [Math.round(x), Math.round(y)]),
    work: [state.src.width, state.src.height],
    fit: state.fit,
    snap: state.snap,
  };
  if (state.mode === "paint") return { ...common, bright: state.bright, colour: state.colour, warm: state.warm };
  return { ...common, trim: state.trim, whites: state.whites, lines: state.lines, lift: state.lift };
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
    form.append("settings", JSON.stringify(settings()));
    form.append("png", png, "clean.png");
    form.append("photo", await photoBlob(), "photo");
    form.append("preview", preview, "preview.jpg");
    let r;
    try {
      r = await fetch(CFG.functionUrl + "/art/submit", { method: "POST", body: form });
    } catch {
      throw new Error("The page could not reach the art desk. Check your signal (wifi or mobile data), then tap Send again.");
    }
    const body = await r.json().catch(() => ({}));
    if (!r.ok) {
      if (r.status === 413) throw new Error((body.message || "The upload is too large.") + " Tap Send again: the page makes the photo smaller.");
      throw new Error(body.message || "The art desk did not take it this time. Please tap Send again in a moment.");
    }
    $("sent-name").textContent = name;
    const keep = $("sent-preview");
    keep.width = prev.width;
    keep.height = prev.height;
    keep.getContext("2d").drawImage(prev, 0, 0);
    show("sent");
  } catch (e) {
    say($("send-msg"), (e && e.message) || "Something went wrong. Please tap Send again.", "error");
  } finally {
    state.busy = false;
    $("send").disabled = false;
  }
}

async function hello() {
  const t = new URLSearchParams(location.hash.slice(1)).get("t") || (() => {
    try {
      return sessionStorage.getItem("art_t");
    } catch {
      return "";
    }
  })() || "";
  if (!t) {
    say($("who"), "This page needs your invite link. Ask CasPop for it.", "error");
    return false;
  }
  try {
    const r = await fetch(CFG.functionUrl + "/art/hello", { method: "POST", headers: { "content-type": "text/plain" }, body: JSON.stringify({ token: t }) });
    const body = await r.json().catch(() => ({}));
    if (!r.ok) {
      say($("who"), body.message || "This invite link is not active. Ask CasPop for a new one.", "error");
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
    say($("who"), "The art desk could not be reached. Check your signal and reload the page.", "error");
    return false;
  }
}

function slider(id, key) {
  $(id).addEventListener("input", (e) => {
    state[key] = Number(e.target.value);
    sliderWords();
    quick();
  });
  $(id).addEventListener("change", () => rework(false));
}

async function main() {
  if (!PX || !window.createImageBitmap && !window.Image) {
    say($("who"), "This browser cannot run the art desk. Try the newest Safari or Chrome.", "error");
    return;
  }
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
    const tag = document.createElement("em");
    tag.textContent = k.in_game ? "in the game now" : k.object ? "built in 3D by hand" : "its place is set up when one arrives";
    if (!k.in_game) tag.className = "later";
    b.append(tag);
    b.addEventListener("click", () => pickKind(k));
    grid.append(b);
  }
  $("mode-paper").addEventListener("click", () => pickMode("paper"));
  $("mode-paint").addEventListener("click", () => pickMode("paint"));
  $("mode-screen").addEventListener("click", () => pickMode("screen"));
  $("take-label").addEventListener("click", () => $("take-input").click());
  $("choose-label").addEventListener("click", () => $("choose-input").click());
  $("file-label").addEventListener("click", () => $("file-input").click());
  $("take-input").addEventListener("change", (e) => takePhoto(e.target.files[0]));
  $("choose-input").addEventListener("change", (e) => takePhoto(e.target.files[0]));
  $("file-input").addEventListener("change", (e) => takeFile(e.target.files[0]));
  $("back-kinds").addEventListener("click", () => show("kinds"));
  $("back-mode").addEventListener("click", () => show("mode"));
  $("back-picture").addEventListener("click", () => pickMode(state.mode));
  $("again").addEventListener("click", () => show("kinds"));
  $("check-again").addEventListener("click", () => pickMode(state.mode));
  $("check-anyway").addEventListener("click", () => {
    state.anyway = true;
    openPreview(false);
  });
  $("sw-paper").addEventListener("change", () => switchMode("paper"));
  $("sw-paint").addEventListener("change", () => switchMode("paint"));
  $("guard-keep").addEventListener("click", () => switchMode("paint"));
  $("guard-drawing").addEventListener("click", () => {
    state.guardSeen = true;
    $("guard").hidden = true;
  });
  $("fit-fill").addEventListener("change", () => { state.fit = "fill"; rework(true); });
  $("fit-whole").addEventListener("change", () => { state.fit = "whole"; rework(true); });
  slider("whites", "whites");
  slider("lines", "lines");
  slider("bright", "bright");
  slider("colour", "colour");
  slider("warm", "warm");
  $("reset-grade").addEventListener("click", () => {
    state.bright = state.colour = state.warm = 0;
    for (const k of ["bright", "colour", "warm"]) $(k).value = "0";
    sliderWords();
    rework(false);
  });
  $("show-photo").addEventListener("click", () => { state.showPhoto = !state.showPhoto; rework(false); });
  $("lift").addEventListener("change", (e) => { state.lift = e.target.checked; rework(false); });
  $("trim").addEventListener("change", (e) => { state.trim = e.target.checked; drawCorners(); rework(true); });
  $("snap").addEventListener("change", (e) => { state.snap = e.target.checked; state.showBefore = false; rework(false); });
  $("before").addEventListener("click", () => { state.showBefore = !state.showBefore; rework(false); });
  $("turn").addEventListener("click", () => { state.corners = [state.corners[3], state.corners[0], state.corners[1], state.corners[2]]; drawCorners(); rework(true); });
  $("refind").addEventListener("click", () => {
    const f = findFor(state.mode);
    state.corners = f.corners;
    state.found = f.found;
    state.touches = f.touches;
    state.byHand = false;
    modeDefaults();
    drawCorners();
    rework(true);
  });
  $("whole-photo").addEventListener("click", () => {
    state.corners = PX.wholePhoto(state.src);
    state.byHand = true;
    if (state.mode === "paper") setTrim(!state.kind.tile);
    drawCorners();
    rework(true);
  });
  $("zoom").addEventListener("input", (e) => {
    const { lo, hi } = scaleRange();
    setScale(lo * Math.pow(hi / lo, Number(e.target.value) / 100));
    drawFrameEditor();
  });
  $("zoom").addEventListener("change", () => { screenOptions(); rework(true); });
  $("show-whole").addEventListener("click", () => {
    const { whole } = scaleRange();
    state.view.cx = state.src.width / 2;
    state.view.cy = state.src.height / 2;
    setScale(whole);
    screenOptions();
    drawSwatches();
    drawFrameEditor();
    rework(true);
  });
  $("fill-frame").addEventListener("click", () => {
    const { cover } = scaleRange();
    setScale(cover);
    screenOptions();
    drawFrameEditor();
    rework(true);
  });
  $("sm-smooth").addEventListener("change", () => { state.smooth = true; drawFrameEditor(); rework(true); });
  $("sm-blocky").addEventListener("change", () => { state.smooth = false; setScale(state.view.s); drawFrameEditor(); rework(true); });
  $("send").addEventListener("click", send);
  wireCorners();
  wireFrameEditor();
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

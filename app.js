/* Frame Jockey — a timeline-free video instrument.
   A Maybe Machine by Ravi Popat.

   The video is read into a buffer of small frames so it can be played in any
   direction at any speed. Gestures on the picture are the edit:
     ← →   scratch (position follows the hand, let go to throw it)
     ↑     flick to slice a fragment into the tray
     ↓     pull to stutter (distance = loop length, sideways = where)
     ◯     circle to loop (radius = length, counter-clockwise bounces)
     hold  freeze, the frame melts outward from the finger
     shake shuffle nearby frames
     tap   pause / let go of a loop
*/
(() => {
'use strict';

const CFG = {
  W: 1280,         // preferred frame width in the buffer
  // bytes of decoded frames kept for clip A (clip B gets half): more on
  // machines that report plenty of memory, so short clips stay sharp
  MEM: (navigator.deviceMemory || 4) >= 8 ? 1100e6 : (navigator.deviceMemory || 4) >= 4 ? 700e6 : 420e6,
  MAXDUR: 60,      // seconds read from the start of a clip
  MAXFPS: 24,
  SPAN: 4,         // seconds across the full width when scratching
  TRAIL: 1.6,      // seconds a gesture trace stays visible
  BRUSH: 30,       // time brush radius in buffer px
  SLIT: 3,         // seconds of slit-scan spread for a full-width diagonal drag
  BANDS: 56,       // slit-scan bands
  LAYERS: 8,       // painted moments kept
};

// one colour per tool family, so the hand tells you what it is doing
const GROUP_RGB = {
  time: '45,91,255',     // electric blue  #2D5BFF
  colour: '0,184,107',   // green          #00B86B
  space: '255,122,0',    // orange         #FF7A00
  mash: '150,64,255',    // violet         #9640FF
};
const ACCENT_RGB = GROUP_RGB.time;
const rgbOf = (t) => GROUP_RGB[(t && t.group) || 'time'] || ACCENT_RGB;
const $ = (s) => document.querySelector(s);
const stage = $('#stage');
const surface = $('#surface');
const screen = $('#screen');
const ctx = screen.getContext('2d', { willReadFrequently: true });
const overlay = $('#overlay');
const octx = overlay.getContext('2d');
const intro = $('#intro');
const statusEl = $('#status');
const modeEl = $('#mode');
const timeEl = $('#time');
const chipsEl = $('#chips') || document.createElement('div'); // the take tray is gone; kept detached so old paths stay harmless
const fileIn = $('#file');
const btnNew = $('#btn-new');
const btnRec = $('#btn-rec');
const btnSeq = $('#btn-seq') || document.createElement('button'); // sequence preview lives on the s key
const btnReplay = $('#btn-replay') || document.createElement('button'); // no longer in the footer; p still replays the trace
const btnCatch = $('#btn-catch') || document.createElement('button');
const setLbl = (b, t) => { const l = b.querySelector('.lbl'); (l || b).textContent = t; b.setAttribute('aria-label', t); };
const btnWipe = $('#btn-wipe') || { disabled: true };
const btnFit = $('#btn-fit');
const btnTool = $('#btn-tool');
const btnGrid = $('#btn-grid');
const btnReset = $('#btn-reset');
const btnSound = $('#btn-sound');
const btnDemo = $('#btn-demo') || document.createElement('button');
const hudEl = $('#hud') || document.createElement('div');
const stackEl = $('#stack');
const wheelEl = $('#wheel');
const wheelList = $('#wheel-list');
const info = $('#info');
const btnInfo = $('#btn-info');

const fb = document.createElement('canvas');   // feedback buffer (last output)
const fctx = fb.getContext('2d');
const tmp = document.createElement('canvas');  // scratch canvas for masking painted layers
const tctx = tmp.getContext('2d');
const tmp2 = document.createElement('canvas'); // snapshot for zoom / kaleido
const t2ctx = tmp2.getContext('2d');

const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const now = () => performance.now();
const TAU = Math.PI * 2;

/* ---------------------------------------------------------------- state */

let clip = null;              // { frames, fps, N, W, H, dur, name }
let pos = 0;                  // playhead in seconds (unwrapped)
let rate = 1;                 // seconds of video per second
let playing = true;
let loop = null;              // { start, len, boom, t, ring?, chip? }
let seq = null;               // { i, t }
let slit = null;              // { span, ux, uy, held }  diagonal slit-scan
let layers = [];              // [{ t, mask, mctx }]  time brush: painted moments
let fx = {};                  // latched effects: echo, grade, hue, duo, crush, zoom, kal, smear, blend
let speedHold = null;         // { target, wob } while the Speed tool is held
let clipB = null;             // second clip for Blend B
let loadTokenB = 0;
let fileTarget = 'A';
let stut = null;              // { start, len, t }
let fz = null;                // { pos, t }
let replay = null;            // { frames, len, t0, i, loop, chip, trail }  playing back a take or a trace
let saved = null;             // the live look, kept while a take plays so it can come back after
let liveFx = {};              // effects changed on top of a playing take
let tape = [];                // the last few seconds of what was played, for catching takes
let lastCatchT = 0;
let scratchPos = 0;
let persist = 0;              // feedback amount 0..1
let shuffle = 0;              // shuffle amount 0..1
let anchor = { x: 180, y: 100 }; // canvas px, origin of melt
let chips = [];
let chipSeq = 0;
let trail = [];
let flashes = [];
let recState = null;
let score = null;
let loadToken = 0;
let toastTimer = 0;
const S = { w: 0, h: 0 };     // surface size in css px
const H = { x: 0, y: 0, in: false }; // hover position for the circle cursor
const V = { vpos: 0 };        // what the screen shows this frame

const G = {
  down: false, id: null, mode: 'idle',
  sx: 0, sy: 0, st: 0, x: 0, y: 0, px: 0, py: 0,
  samples: [], turn: 0, head: null, hx: 0, hy: 0,
  sgnX: 0, sgnY: 0, revs: [], hold: 0, anchorPos: 0, serial: 0,
};

// sizes tuned on a 360px-wide picture scale with the real buffer width
const PX = () => (clip ? clip.W / 360 : 1);
const brushR = () => CFG.BRUSH * PX();

const wrapT = (t) => {
  const d = clip ? clip.dur : 1;
  return ((t % d) + d) % d;
};

/* ---------------------------------------------------------------- audio */

// Plays the clip's decoded audio from a read head that chases the playhead,
// so scratching, reversing and looping sound like a record under a hand.
const DSP_SRC = `
class ScratchDSP {
  constructor() {
    this.L = null; this.R = null; this.len = 0; this.sr = 44100;
    this.head = 0; this.target = 0; this.trate = 0; this.step = 0;
    this.old = 0; this.xf = 0; this.g = 0; this.vol = 0;
  }
  msg(d) {
    if (d.type === 'buf') {
      this.L = d.L; this.R = d.R; this.len = d.L ? d.L.length : 0; this.sr = d.sr;
      this.head = this.target = this.old = 0; this.step = 0; this.xf = 0; this.g = 0;
      return;
    }
    if (!this.len) return;
    const p = d.pos * this.sr;
    this.trate = d.rate; this.vol = d.vol;
    if (d.jump) { this.old = this.head; this.xf = 1; this.head = p; this.target = p; return; }
    const L = this.len;
    let h = this.head % L; if (h < 0) h += L;
    let dt = p - h;
    if (dt > L / 2) dt -= L; else if (dt < -L / 2) dt += L;
    this.target = this.head + dt;
  }
  render(oL, oR) {
    const n = oL.length;
    if (!this.len) { for (let i = 0; i < n; i++) { oL[i] = 0; if (oR !== oL) oR[i] = 0; } return; }
    const L = this.len, A = this.L, B = this.R;
    for (let i = 0; i < n; i++) {
      this.target += this.trate;
      const want = this.trate + (this.target - this.head) * 0.0025;
      this.step += (want - this.step) * 0.012;
      this.head += this.step;
      const sp = this.step < 0 ? -this.step : this.step;
      const gt = this.vol * (sp > 0.33 ? 1 : sp * 3);
      this.g += (gt - this.g) * 0.003;
      let x = this.head % L; if (x < 0) x += L;
      const k = x | 0, f = x - k; let k2 = k + 1; if (k2 >= L) k2 = 0;
      let l = A[k] + (A[k2] - A[k]) * f;
      let r = B[k] + (B[k2] - B[k]) * f;
      if (this.xf > 0) {
        this.old += this.step;
        let y = this.old % L; if (y < 0) y += L;
        const j = y | 0, g = y - j; let j2 = j + 1; if (j2 >= L) j2 = 0;
        const w = this.xf;
        l = l * (1 - w) + (A[j] + (A[j2] - A[j]) * g) * w;
        r = r * (1 - w) + (B[j] + (B[j2] - B[j]) * g) * w;
        this.xf -= 1 / 256;
      }
      oL[i] = l * this.g;
      if (oR !== oL) oR[i] = r * this.g;
    }
    if (this.head > L * 8 || this.head < -L * 8) {
      const s = Math.floor(this.head / L) * L;
      this.head -= s; this.target -= s; this.old -= s;
    }
  }
}`;

const A = { ctx: null, node: null, gain: null, dest: null, post: null, ready: null, hasBuf: false, lastPos: 0, lastRate: 1 };

function ensureAudio() {
  if (A.ready) return A.ready;
  A.ready = (async () => {
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    A.ctx = new AC();
    A.gain = A.ctx.createGain();
    A.gain.gain.value = muted ? 0 : 0.9;
    A.gain.connect(A.ctx.destination);
    try { A.dest = A.ctx.createMediaStreamDestination(); A.gain.connect(A.dest); } catch (e) { A.dest = null; }
    try {
      const mod = DSP_SRC + `
class VMScratch extends AudioWorkletProcessor {
  constructor() { super(); this.d = new ScratchDSP(); this.port.onmessage = (e) => this.d.msg(e.data); }
  process(i, o) { const c = o[0]; this.d.render(c[0], c[1] || c[0]); return true; }
}
registerProcessor('vm-scratch', VMScratch);`;
      const url = URL.createObjectURL(new Blob([mod], { type: 'application/javascript' }));
      await A.ctx.audioWorklet.addModule(url);
      A.node = new AudioWorkletNode(A.ctx, 'vm-scratch', { numberOfInputs: 0, outputChannelCount: [2] });
      A.post = (m, tr) => A.node.port.postMessage(m, tr || []);
    } catch (e) {
      // fallback for contexts where worklets can't load (e.g. some file:// setups)
      const DSP = new Function(DSP_SRC + '\nreturn ScratchDSP;')();
      const d = new DSP();
      A.node = A.ctx.createScriptProcessor(1024, 1, 2);
      A.node.onaudioprocess = (ev) => {
        const b = ev.outputBuffer;
        d.render(b.getChannelData(0), b.getChannelData(1));
      };
      A.post = (m) => d.msg(m);
    }
    A.node.connect(A.gain);
  })();
  return A.ready;
}

function wakeAudio() {
  ensureAudio().then(() => { if (A.ctx && A.ctx.state !== 'running') A.ctx.resume(); });
}

async function loadAudio(file, dur, token) {
  await ensureAudio();
  if (!A.ctx) return false;
  try {
    const ab = await file.arrayBuffer();
    const buf = await new Promise((res, rej) => {
      const p = A.ctx.decodeAudioData(ab, res, rej);
      if (p && p.catch) p.catch(rej);
    });
    if (token !== loadToken) return false;
    const sr = buf.sampleRate;
    const len = Math.max(1, Math.round(dur * sr));
    const L = new Float32Array(len), R = new Float32Array(len);
    const c0 = buf.getChannelData(0);
    const c1 = buf.numberOfChannels > 1 ? buf.getChannelData(1) : c0;
    L.set(c0.subarray(0, Math.min(len, c0.length)));
    R.set(c1.subarray(0, Math.min(len, c1.length)));
    A.post({ type: 'buf', L, R, sr }, [L.buffer, R.buffer]);
    A.hasBuf = true;
    return true;
  } catch (e) {
    if (A.post) A.post({ type: 'buf', L: null, R: null, sr: 44100 });
    A.hasBuf = false;
    return false;
  }
}

function sendAudio(apos, arate, vol, allowJump, dt) {
  if (!A.post || !A.hasBuf) return;
  const d = clip.dur;
  let diff = (apos - (A.lastPos + A.lastRate * dt)) % d;
  if (diff > d / 2) diff -= d; else if (diff < -d / 2) diff += d;
  const jump = allowJump && Math.abs(diff) > 0.045;
  A.post({ type: 'ctl', pos: wrapT(apos), rate: arate, vol, jump });
  A.lastPos = apos;
  A.lastRate = arate;
}

/* ---------------------------------------------------------------- loading */

function once(el, ok, bad, ms) {
  return new Promise((res, rej) => {
    let to = 0;
    const a = () => { done(); res(); };
    const b = () => { done(); rej(new Error(bad)); };
    const done = () => {
      clearTimeout(to);
      el.removeEventListener(ok, a);
      if (bad) el.removeEventListener(bad, b);
    };
    el.addEventListener(ok, a);
    if (bad) el.addEventListener(bad, b);
    if (ms) to = setTimeout(a, ms);
  });
}

function seekTo(v, t) {
  return new Promise((res) => {
    let to = 0;
    const h = () => { clearTimeout(to); v.removeEventListener('seeked', h); res(); };
    v.addEventListener('seeked', h);
    to = setTimeout(h, 2000);
    v.currentTime = t;
  });
}

// Size the buffer to fit the memory budget: keep 640px frames and drop the
// frame rate towards 15fps first, then step the width down, then the rate.
function bufferSize(vw, vh, dur, mem) {
  const asp = vh / vw;
  const hOf = (w) => Math.max(2, Math.round((w * asp) / 2) * 2);
  const fpsFor = (w) => Math.floor(mem / (w * hOf(w) * 4) / dur);
  for (const w0 of [CFG.W, 960, 800, 640, 480, 400]) {
    const w = Math.min(w0, Math.floor(vw / 2) * 2 || w0);
    const f = Math.min(CFG.MAXFPS, fpsFor(w));
    if (f >= 15) return { W: w, H: hOf(w), fps: f };
  }
  const w = Math.min(400, vw);
  return { W: w, H: hOf(w), fps: clamp(fpsFor(w), 8, CFG.MAXFPS) };
}

async function captureFrames(v, dur, onProg, cancelled, mem) {
  const { W, H, fps } = bufferSize(v.videoWidth, v.videoHeight, dur, mem || CFG.MEM);
  const N = Math.max(1, Math.ceil(dur * fps));
  const c = document.createElement('canvas');
  c.width = W; c.height = H;
  const cx = c.getContext('2d');
  const frames = new Array(N).fill(null);
  const pending = [];

  const snap = (i) => {
    cx.drawImage(v, 0, 0, W, H);
    frames[i] = 1; // placeholder until the bitmap resolves
    pending.push(createImageBitmap(c).then((b) => { frames[i] = b; }));
  };

  await seekTo(v, 0);

  // pass 1: play it through quickly and grab what the decoder hands us
  await new Promise((resolve) => {
    let done = false;
    const finish = () => { if (done) return; done = true; v.pause(); resolve(); };
    const rv = 'requestVideoFrameCallback' in v;
    const next = () => (rv ? v.requestVideoFrameCallback(tick) : requestAnimationFrame(() => tick()));
    const tick = (_, meta) => {
      if (done) return;
      if (cancelled()) return finish();
      const t = meta ? meta.mediaTime : v.currentTime;
      const i = Math.floor(t * fps);
      if (i >= 0 && i < N && !frames[i]) snap(i);
      onProg(Math.min(1, t / dur) * 0.85);
      if (t >= dur - 0.5 / fps || v.ended) return finish();
      next();
    };
    v.addEventListener('ended', finish, { once: true });
    v.playbackRate = clamp(55 / fps, 1, 3);
    v.play().then(next, finish);
    let lastT = -1, still = 0;
    const wd = setInterval(() => {
      if (done) { clearInterval(wd); return; }
      if (v.currentTime === lastT) { if (++still > 8) { clearInterval(wd); finish(); } }
      else { still = 0; lastT = v.currentTime; }
    }, 500);
  });
  await Promise.all(pending);

  // pass 2: seek into the holes the fast pass skipped
  const holes = [];
  for (let i = 0; i < N; i++) if (!frames[i]) holes.push(i);
  const deadline = now() + 12000;
  for (let k = 0; k < holes.length; k++) {
    if (cancelled() || now() > deadline) break;
    const i = holes[k];
    await seekTo(v, Math.min(v.duration - 0.001, (i + 0.5) / fps));
    cx.drawImage(v, 0, 0, W, H);
    frames[i] = await createImageBitmap(c);
    onProg(0.85 + (0.15 * (k + 1)) / holes.length);
  }

  // anything still missing borrows its neighbour
  let prev = null;
  for (let i = 0; i < N; i++) { if (frames[i]) prev = frames[i]; else frames[i] = prev; }
  const first = frames.find(Boolean);
  if (!first) throw new Error('no frames');
  for (let i = 0; i < N && !frames[i]; i++) frames[i] = first;

  return { frames, fps, N, W, H };
}

function releaseFrames(c) {
  if (!c) return;
  const seen = new Set(c.frames);
  seen.forEach((b) => { if (b && b.close) b.close(); });
}

async function loadFile(file, slot) {
  if (!file) return;
  if (slot === 'B') return loadB(file);
  const token = ++loadToken;
  if (recState) stopRec();
  replay = null; seq = null; loop = null; stut = null; fz = null; saved = null; liveFx = {};
  const old = clip;
  clip = null;
  releaseFrames(old);
  intro.hidden = true;
  showStatus('opening ' + file.name);

  const url = URL.createObjectURL(file);
  const v = document.createElement('video');
  v.muted = true;
  v.playsInline = true;
  v.preload = 'auto';
  v.style.cssText = 'position:fixed;left:-9999px;top:0;width:2px;height:2px;opacity:0;pointer-events:none';
  document.body.appendChild(v);
  v.src = url;

  try {
    await once(v, 'loadedmetadata', 'error');
    if (!isFinite(v.duration)) {           // some recorded webm files report Infinity
      v.currentTime = 1e7;
      await once(v, 'durationchange', null, 3000);
    }
    if (!v.videoWidth || !isFinite(v.duration) || v.duration <= 0) throw new Error('no video');
    const dur = Math.min(v.duration, CFG.MAXDUR);
    const audioP = loadAudio(file, dur, token);
    const res = await captureFrames(
      v, dur,
      (p) => { if (token === loadToken) showStatus('reading frames ' + Math.round(p * 100) + '%'); },
      () => token !== loadToken,
    );
    if (token !== loadToken) { releaseFrames(res); return; }
    showStatus('listening for sound');
    const hasAudio = await audioP;
    if (token !== loadToken) { releaseFrames(res); return; }
    installClip(res, dur, file.name);
    const notes = [];
    if (v.duration > CFG.MAXDUR) notes.push('using the first ' + CFG.MAXDUR + 's');
    notes.unshift(res.W + 'px · ' + res.fps + 'fps');
    if (!hasAudio) notes.push('no sound found');
    else if (A.ctx && A.ctx.state !== 'running') notes.push('press space or touch the picture to wake the sound');
    if (notes.length) toast(notes.join(' · '));
  } catch (err) {
    if (token === loadToken) {
      showStatus("couldn't read that one, try an mp4 or webm");
      setTimeout(() => { if (token === loadToken && !clip) { hideStatus(); intro.hidden = false; surface.hidden = true; } }, 2600);
    }
  } finally {
    v.pause();
    v.removeAttribute('src');
    v.load();
    v.remove();
    URL.revokeObjectURL(url);
  }
}

async function loadB(file) {
  if (!clip) return;
  const tok = ++loadTokenB;
  showStatus('opening clip B');
  const url = URL.createObjectURL(file);
  const v = document.createElement('video');
  v.muted = true; v.playsInline = true; v.preload = 'auto';
  v.style.cssText = 'position:fixed;left:-9999px;top:0;width:2px;height:2px;opacity:0;pointer-events:none';
  document.body.appendChild(v);
  v.src = url;
  try {
    await once(v, 'loadedmetadata', 'error');
    if (!isFinite(v.duration)) { v.currentTime = 1e7; await once(v, 'durationchange', null, 3000); }
    if (!v.videoWidth || !isFinite(v.duration) || v.duration <= 0) throw new Error('no video');
    const dur = Math.min(v.duration, CFG.MAXDUR);
    const res = await captureFrames(v, dur,
      (p) => { if (tok === loadTokenB) showStatus('reading clip B ' + Math.round(p * 100) + '%'); },
      () => tok !== loadTokenB, CFG.MEM * 0.5);
    if (tok !== loadTokenB) { releaseFrames(res); return; }
    releaseFrames(clipB);
    clipB = { ...res, dur, name: file.name };
    tool = TOOL[afterB] || TOOL.blend;
    if (tool.id === 'key') { if (!fx.key) fx.key = { th: 90, soft: 30 }; }
    else if (!fx.blend) fx.blend = { mix: 0.5, mode: 'screen' };
    afterB = 'blend';
    toast('clip B is in. drag on the video to ' + (tool.id === 'key' ? 'key it' : 'blend it'));
  } catch (err) {
    if (tok === loadTokenB) toast("Couldn't read clip B, try an mp4 or webm");
  } finally {
    v.pause(); v.removeAttribute('src'); v.load(); v.remove();
    URL.revokeObjectURL(url);
  }
}

function frameAtB(t) {
  const b = clipB;
  let i = Math.floor((((t % b.dur) + b.dur) % b.dur) * b.fps);
  if (i >= b.N) i = b.N - 1;
  return b.frames[i];
}

function installClip(res, dur, name) {
  clip = { ...res, dur, name };
  screen.width = clip.W; screen.height = clip.H;
  fb.width = clip.W; fb.height = clip.H;
  ctx.imageSmoothingEnabled = true;
  ctx.imageSmoothingQuality = 'high';
  pos = 0; rate = 1; playing = true; tape = []; lastCatchT = 0;
  persist = 0; shuffle = 0;
  anchor = { x: clip.W / 2, y: clip.H / 2 };
  A.lastPos = 0; A.lastRate = 1;
  chips = [];
  renderChips();
  wipePaint();
  slit = null;
  fx = {};
  speedHold = null;
  surface.hidden = false;
  hudEl.hidden = false;
  document.body.classList.add('loaded');
  intro.hidden = true;
  hideStatus();
  layout();
  btnRec.disabled = false;
  btnReplay.disabled = !score;
}

/* ---------------------------------------------------------------- demo clip */

// A 12 second clip drawn in code, with a synthesized beat, so there is
// something to play with before you have a video at hand.
function drawDemoFrame(g, t, W, Hh, beat, dur) {
  g.fillStyle = '#f2f1ee';
  g.fillRect(0, 0, W, Hh);
  // rippling dot field
  g.fillStyle = '#c9c7c1';
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 16; c++) {
      const rad = 0.8 + 2.4 * Math.max(0, Math.sin(c * 0.6 + r * 0.35 - t * 4));
      g.beginPath();
      g.arc(12 + c * 22.4, 14 + r * 22, rad, 0, TAU);
      g.fill();
    }
  }
  // beat ring
  const ph = (t % beat) / beat;
  g.strokeStyle = 'rgba(20,20,20,' + (1 - ph).toFixed(3) + ')';
  g.lineWidth = 2;
  g.beginPath();
  g.arc(W / 2, Hh / 2, 24 + ph * 110, 0, TAU);
  g.stroke();
  // clock
  g.fillStyle = '#141414';
  g.font = '700 58px "JetBrains Mono", ui-monospace, monospace';
  g.textAlign = 'center';
  g.textBaseline = 'middle';
  g.fillText(t.toFixed(2).padStart(5, '0'), W / 2, Hh / 2);
  g.font = '400 12px "JetBrains Mono", ui-monospace, monospace';
  g.textAlign = 'left';
  g.fillText('beat ' + ((Math.floor(t / beat) % 4) + 1) + '/4', 10, 16);
  g.textAlign = 'right';
  g.fillText('demo', W - 10, 16);
  // bouncing ball
  const bx = W * (0.08 + 0.84 * Math.abs(((t / 3) % 2) - 1));
  const by = Hh * 0.86 - Math.abs(Math.sin((t * Math.PI) / beat)) * 46;
  g.fillStyle = '#e5372b';
  g.beginPath();
  g.arc(bx, by, 7, 0, TAU);
  g.fill();
  // progress
  g.fillStyle = '#141414';
  g.fillRect(0, Hh - 3, (t / dur) * W, 3);
}

function synthDemo(dur, sr, beat) {
  const n = Math.round(dur * sr);
  const L = new Float32Array(n), R = new Float32Array(n);
  const add = (i, v, pan) => { if (i < n) { L[i] += v * (1 - pan); R[i] += v * (1 + pan); } };
  const beats = Math.floor(dur / beat);
  for (let k = 0; k < beats; k++) {
    // kick
    let s = Math.round(k * beat * sr), p = 0;
    for (let j = 0; j < 0.35 * sr; j++) {
      const tt = j / sr;
      p += (TAU * (48 + 95 * Math.exp(-tt * 30))) / sr;
      add(s + j, Math.sin(p) * Math.exp(-tt * 9) * 0.8, 0);
    }
    // hat on the offbeat
    s = Math.round((k + 0.5) * beat * sr);
    for (let j = 0; j < 0.05 * sr; j++) add(s + j, (Math.random() * 2 - 1) * Math.exp((-j / sr) * 70) * 0.22, 0.4);
  }
  // arpeggio in eighths
  const notes = [220, 261.63, 293.66, 329.63, 392, 440, 523.25, 392];
  const eighths = Math.floor(dur / (beat / 2));
  for (let m = 0; m < eighths; m++) {
    const f = notes[(m * 3 + Math.floor(m / 8)) % notes.length];
    const s = Math.round(m * (beat / 2) * sr);
    const pan = m % 2 ? 0.35 : -0.35;
    let p = 0;
    for (let j = 0; j < 0.2 * sr; j++) {
      const tt = j / sr;
      p += (TAU * f) / sr;
      add(s + j, (2 / Math.PI) * Math.asin(Math.sin(p)) * Math.exp(-tt * 9) * 0.2, pan);
    }
  }
  let peak = 0;
  for (let i = 0; i < n; i++) peak = Math.max(peak, Math.abs(L[i]), Math.abs(R[i]));
  const k = peak > 0 ? 0.9 / peak : 1;
  for (let i = 0; i < n; i++) { L[i] *= k; R[i] *= k; }
  return { L, R };
}

async function loadDemo() {
  const token = ++loadToken;
  if (recState) stopRec();
  replay = null; seq = null; loop = null; stut = null; fz = null; saved = null; liveFx = {};
  const old = clip;
  clip = null;
  releaseFrames(old);
  intro.hidden = true;
  wakeAudio();
  showStatus('drawing the demo clip');
  try { await Promise.all([document.fonts.load('700 58px "JetBrains Mono"'), document.fonts.load('400 12px "JetBrains Mono"')]); } catch (e) { /* fallback font is fine */ }
  const dur = 12, fps = 15, N = dur * fps, W = 960, Hh = 540;
  const c = document.createElement('canvas');
  c.width = W; c.height = Hh;
  const g = c.getContext('2d');
  const beat = 0.5;
  const frames = [];
  for (let i = 0; i < N; i++) {
    g.setTransform(W / 360, 0, 0, W / 360, 0, 0);
    drawDemoFrame(g, i / fps, 360, 202.5, beat, dur);
    frames.push(await createImageBitmap(c));
    if (token !== loadToken) { frames.forEach((b) => b.close()); return; }
  }
  await ensureAudio();
  if (A.ctx) {
    const sr = A.ctx.sampleRate;
    const { L, R } = synthDemo(dur, sr, beat);
    A.post({ type: 'buf', L, R, sr }, [L.buffer, R.buffer]);
    A.hasBuf = true;
  }
  if (token !== loadToken) return;
  installClip({ frames, fps, N, W, H: Hh }, dur, 'demo');
  if (A.ctx && A.ctx.state !== 'running') toast('tap the picture once to wake the sound');
}

/* ---------------------------------------------------------------- ui bits */

function showStatus(t) { statusEl.textContent = t; statusEl.hidden = false; }
function hideStatus() { statusEl.hidden = true; }
function toast(t) {
  clearTimeout(toastTimer);
  showStatus(t);
  toastTimer = setTimeout(hideStatus, 3200);
}

// The surface is the visible picture. In fill mode it is the whole stage and
// the frame is scaled to cover it (cropping the overflow); in fit mode it is
// the frame's own shape, letterboxed. `view` is where the frame sits inside
// the surface, so screen points map to frame pixels.
let fitMode = 'auto';   // 'auto' | 'fill' | 'fit'
const view = { ox: 0, oy: 0, dw: 1, dh: 1 };
const toCX = (x) => ((x - view.ox) / view.dw) * clip.W;
const toCY = (y) => ((y - view.oy) / view.dh) * clip.H;

function layout() {
  const st = stage.getBoundingClientRect();
  const sw = Math.max(40, Math.floor(st.width)), sh = Math.max(24, Math.floor(st.height));
  const ar = clip ? clip.W / clip.H : 16 / 9;
  const sar = sw / sh;
  const fill = fitMode === 'fill' || (fitMode === 'auto' && Math.abs(Math.log(ar / sar)) < Math.log(1.35));
  let w = sw, h = sh;
  if (!fill) { if (sar > ar) w = Math.round(sh * ar); else h = Math.round(sw / ar); }
  let dw, dh;
  if (w / h > ar) { dw = w; dh = w / ar; } else { dh = h; dw = h * ar; }
  Object.assign(view, { ox: (w - dw) / 2, oy: (h - dh) / 2, dw, dh });
  surface.style.width = w + 'px';
  surface.style.height = h + 'px';
  screen.style.left = view.ox + 'px';
  screen.style.top = view.oy + 'px';
  screen.style.width = dw + 'px';
  screen.style.height = dh + 'px';
  const dpr = Math.min(2, window.devicePixelRatio || 1);
  overlay.width = Math.round(w * dpr);
  overlay.height = Math.round(h * dpr);
  octx.setTransform(dpr, 0, 0, dpr, 0, 0);
  S.w = w; S.h = h;
  if (btnFit) { btnFit.dataset.fill = fill ? '1' : '0'; setLbl(btnFit, fill ? 'Fit' : 'Fill'); }
  if (clip) renderChips();
}

const fmt = (t) => {
  const m = Math.floor(t / 60), s = t - m * 60;
  return String(m).padStart(2, '0') + ':' + s.toFixed(1).padStart(4, '0');
};

function modeLabel() {
  if (replay) {
    const what = seq ? 'sequence ' + (seq.i + 1) + '/' + chips.length : replay.chip != null ? 'looping take' : 'replaying trace';
    return what + (tool.id !== 'hand' ? ' · ' + tool.name.toLowerCase() + (liveFx[tool.id] ? ' on top' : ': drag to change the look') : '');
  }
  if (tool.id !== 'hand') return tool.name.toLowerCase() + (G.down && G.mode === 'tool' && tool.info ? ' · ' + tool.info() : ' · double-tap for tools');
  let s;
  switch (G.mode) {
    case 'scratch': s = 'scratch ' + (rate >= 0 ? '→ ' : '← ') + Math.abs(rate).toFixed(1) + 'x'; break;
    case 'up': s = 'fast ' + rate.toFixed(1) + 'x'; break;
    case 'stutter': s = 'stutter ' + stut.len.toFixed(2) + 's'; break;
    case 'freeze': s = 'freeze · melt ' + Math.round(persist * 100) + '%'; break;
    case 'circle': s = 'loop ' + (loop.boom ? 'bounce ' : '') + loop.len.toFixed(2) + 's · radius sets length'; break;
    case 'slit': s = 'slit-scan ' + slit.span.toFixed(2) + 's across · let go to spring back'; break;
    case 'brush': s = 'time brush · painting ' + fmt(wrapT(G.brush ? G.brush.t : pos)); break;
    default:
      if (loop) s = 'loop ' + (loop.boom ? 'bounce ' : '') + loop.len.toFixed(2) + 's';
      else if (Math.abs(rate - (playing ? 1 : 0)) > 0.06) s = 'drift ' + rate.toFixed(2) + 'x';
      else s = (playing ? 'scratch' : 'scratch · paused') + ' · double-tap for tools';
  }
  if (shuffle > 0.08) s += ' + shuffle';
  return s;
}

function hud() {
  modeEl.textContent = clip ? modeLabel() : '';
  const tt = clip ? fmt(wrapT(V.vpos)) + ' / ' + fmt(clip.dur) : '';
  const rt = clip && recState ? 'rec ' + fmt((now() - recState.t0) / 1000) : '';
  if (tt + rt !== timeEl.dataset.v) {
    timeEl.dataset.v = tt + rt;
    timeEl.textContent = tt;
    if (rt) { const r = document.createElement('span'); r.className = 'rec'; r.textContent = rt; timeEl.append(r); }   // while recording, its time in red
  }
  const activeId = replay && replay.chip != null ? replay.chip : null;
  btnTool.disabled = !clip;
  // nothing to play with until a clip is in
  btnSound.disabled = !clip;
  btnFit.disabled = !clip;
  btnGrid.disabled = !clip;
  for (const el of chipsEl.children) el.classList.toggle('on', +el.dataset.id === activeId);
  btnSeq.classList.toggle('on', !!seq);
  btnSeq.textContent = seq ? 'Stop sequence' : 'Sequence';
  const tracing = !!replay && replay.chip == null && !seq;
  btnReplay.classList.toggle('on', tracing);
  btnReplay.textContent = tracing ? 'Stop replay' : 'Replay trace';
  renderStack();
}

/* ---------------------------------------------------------------- fragments */

function frameAt(t) {
  let i = Math.floor(wrapT(t) * clip.fps);
  if (i >= clip.N) i = clip.N - 1;
  return clip.frames[i];
}

/* takes: catch what you just played (since the last catch, 1 to 8 seconds),
   with its scratches, loops and look. A take loops on click, and the sequence
   plays the takes in order. Effects changed while a take plays sit on top, so
   catching again makes a new take with the new look. */

function catchSpan() {
  const t = now();
  let from = Math.max(lastCatchT, t - 8000, tape.length ? tape[0].t : t);
  if (t - from < 1000) from = Math.max(t - 3000, tape.length ? tape[0].t : t);
  return { from, len: t - from };
}

function catchTake(x) {
  if (!clip) return;
  const { from } = catchSpan();
  const fr = tape.filter((f) => f.t >= from);
  if (fr.length < 5) return;
  const t0 = fr[0].t;
  const frames = fr.map((f) => Object.assign({}, f, { t: f.t - t0, cx: null, cy: null }));
  const thumb = document.createElement('canvas');
  thumb.width = 120;
  thumb.height = Math.max(2, Math.round((120 * clip.H) / clip.W));
  thumb.getContext('2d').drawImage(screen, 0, 0, thumb.width, thumb.height);
  chips.push({ id: chipSeq++, frames, len: frames[frames.length - 1].t, thumb });
  lastCatchT = now();
  flashes.push({ x: x == null ? S.w / 2 : x, t: now() });
  renderChips();
  chipsEl.scrollLeft = chipsEl.scrollWidth;
}

function startPlayback(frames, opts) {
  if (!frames || frames.length < 2) return;
  if (!saved) saved = { fx: Object.assign({}, fx), slit };
  loop = null;
  replay = { frames, len: frames[frames.length - 1].t, t0: now(), i: 0, loop: !!opts.loop, chip: opts.chip, trail: !!opts.trail };
}

function endPlayback() {
  replay = null;
  if (saved) {
    fx = Object.assign({}, saved.fx, liveFx);
    slit = saved.slit;
    saved = null;
  }
  liveFx = {};
  rate = 1;
  playing = true;
}

function nextInSeq() {
  seq.i++;
  if (seq.i >= chips.length) {
    if (seq.once) { seq = null; endPlayback(); if (recState) stopRec(); return; }
    seq.i = 0;
  }
  const c = chips[seq.i];
  replay = { frames: c.frames, len: c.len, t0: now(), i: 0, loop: false, chip: c.id };
}

function removeChip(id) {
  const k = chips.findIndex((c) => c.id === id);
  if (k < 0) return;
  chips.splice(k, 1);
  if (seq) { if (!chips.length) { seq = null; endPlayback(); } else if (seq.i >= k) seq.i = Math.max(-1, seq.i - 1); }
  else if (replay && replay.chip === id) endPlayback();
  renderChips();
}

function playChip(c) {
  wakeAudio();
  if (replay && replay.chip === c.id && !seq) { endPlayback(); return; }
  seq = null;
  startPlayback(c.frames, { loop: true, chip: c.id });
}

// a tool used while a take plays changes the take's look live
function noteLive() {
  if (replay && G.tool && G.tool.latch) liveFx[G.tool.id] = fx[G.tool.id];
}

let dragK = -1;
function renderChips() {
  chipsEl.innerHTML = '';
  chipsEl.classList.toggle('empty', chips.length === 0);
  btnSeq.disabled = chips.length === 0;
  if (!clip) return;
  chips.forEach((c, k) => {
    const el = document.createElement('div');
    el.className = 'chip';
    el.draggable = true;
    el.dataset.id = c.id;
    el.title = 'click to loop this take, click again to stop · drag to reorder · right-click to remove';
    const cv = document.createElement('canvas');
    cv.width = c.thumb.width;
    cv.height = c.thumb.height;
    cv.getContext('2d').drawImage(c.thumb, 0, 0);
    const lab = document.createElement('span');
    lab.textContent = (c.len / 1000).toFixed(1) + 's';
    const x = document.createElement('button');
    x.className = 'x';
    x.type = 'button';
    x.textContent = '×';
    x.onclick = (ev) => { ev.stopPropagation(); removeChip(c.id); };
    el.append(cv, lab, x);
    el.onclick = () => playChip(c);
    el.oncontextmenu = (ev) => { ev.preventDefault(); removeChip(c.id); };
    el.ondragstart = (ev) => { dragK = k; ev.dataTransfer.effectAllowed = 'move'; ev.dataTransfer.setData('text/plain', 'chip'); };
    el.ondragover = (ev) => { if (dragK < 0) return; ev.preventDefault(); el.classList.add('over'); };
    el.ondragleave = () => el.classList.remove('over');
    el.ondrop = (ev) => {
      ev.preventDefault(); ev.stopPropagation();
      el.classList.remove('over');
      if (dragK < 0 || dragK === k) return;
      const [m] = chips.splice(dragK, 1);
      chips.splice(k, 0, m);
      dragK = -1;
      renderChips();
    };
    el.ondragend = () => { dragK = -1; };
    chipsEl.append(el);
  });
}

/* ---------------------------------------------------------------- gestures */

function pushTrail(x, y, m, brk) {
  trail.push({ x, y, t: now(), m, brk, c: handColour() });
  if (trail.length > 800) trail.shift();
}

const spp = () => Math.min(clip.dur, CFG.SPAN) / S.w;
const lenFromRad = (r) => clamp((r / (Math.min(S.w, S.h) * 0.5)) * 3, 0.06, 4);

function local(e) {
  const r = surface.getBoundingClientRect();
  return { x: e.clientX - r.left, y: e.clientY - r.top };
}

function setAnchor(x, y) {
  if (!clip) return;
  anchor = { x: toCX(x), y: toCY(y) };
}

surface.addEventListener('pointerdown', (e) => {
  if (!clip) return;
  if (G.down) { if (e.pointerId !== G.id && e.pointerType !== 'mouse') secondDown(e); return; }
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  e.preventDefault();
  wakeAudio();
  surface.setPointerCapture(e.pointerId);
  const { x, y } = local(e);
  if (WH.open) { wheelDown(e, x, y); return; }
  if (replay && tool.id === 'hand') { seq = null; endPlayback(); }
  Object.assign(G, {
    down: true, id: e.pointerId, mode: 'pending', tool,
    sx: x, sy: y, ox: x, oy: y, lockT: 0, lockMode: '', st: now(), x, y, px: x, py: y,
    samples: [{ x, y, t: now() }], turn: 0, head: null, hx: x, hy: y,
    sgnX: 0, sgnY: 0, anchorPos: pos,
  });
  G.serial++;
  G.touch = e.pointerType === 'touch';
  setAnchor(x, y);
  pushTrail(x, y, 'pending', true);
  clearTimeout(G.hold);
  if (tool.id === 'hand') {
    G.hold = setTimeout(() => {
      if (G.down && G.mode === 'pending') { G.mode = 'freeze'; fz = { pos, t: 0 }; lock(); }
    }, 280);
  } else {
    // other tools start after a short press or a small move, so a tap stays a tap
    G.hold = setTimeout(() => { if (G.down && G.mode === 'pending') beginTool(); }, 200);
  }
});

function lock() { G.lockT = now(); G.lockMode = G.mode; }

surface.addEventListener('pointerleave', () => { H.in = false; });
surface.addEventListener('pointermove', (e) => {
  const { x, y } = local(e);
  H.x = x; H.y = y; H.in = true;
  if (P2 && e.pointerId === P2.id) { secondMove(x, y); return; }
  if (TT && G.down && e.pointerId === G.id && Math.hypot(x - G.ox, y - G.oy) > 10) TT = null;
  if (WH.drag) { if (e.pointerId === WH.drag.id) wheelMove(x, y); return; }
  if (!G.down || e.pointerId !== G.id) return;
  const t = now();
  G.x = x; G.y = y;
  G.samples.push({ x, y, t });
  while (G.samples.length && t - G.samples[0].t > 1500) G.samples.shift();
  setAnchor(x, y);

  if (G.tool.id !== 'hand') {
    if (G.mode === 'pending' && Math.hypot(x - G.ox, y - G.oy) > 6) { clearTimeout(G.hold); beginTool(); }
    else if (G.mode === 'tool' && G.tool.move) { G.tool.move(toolPoint(x, y)); noteLive(); }
    if (G.tool.id !== 'brush') pushTrail(x, y, 'tool', false);
    return;
  }

  // direction reversals feed the shuffle
  const mdx = x - G.px, mdy = y - G.py;
  if (G.mode === 'brush') { G.sgnX = 0; G.sgnY = 0; } // scribbling paint shouldn't shuffle
  else if (Math.abs(mdx) > 3) { const s = Math.sign(mdx); if (G.sgnX && s !== G.sgnX) G.revs.push(t); G.sgnX = s; }
  if (G.mode !== 'brush' && Math.abs(mdy) > 3) { const s = Math.sign(mdy); if (G.sgnY && s !== G.sgnY) G.revs.push(t); G.sgnY = s; }
  G.px = x; G.py = y;

  // accumulated turning angle detects circles (sharp reversals don't count)
  const hx = x - G.hx, hy = y - G.hy;
  if (hx * hx + hy * hy >= 36) {
    const h = Math.atan2(hy, hx);
    if (G.head !== null) {
      let d = h - G.head;
      while (d > Math.PI) d -= TAU;
      while (d < -Math.PI) d += TAU;
      if (Math.abs(d) < 2.2) G.turn += d;
    }
    G.head = h; G.hx = x; G.hy = y;
  }

  const dx = x - G.sx, dy = y - G.sy;

  if (G.mode !== 'freeze' && G.mode !== 'circle' && G.mode !== 'brush' && Math.abs(G.turn) > Math.PI * 1.75) {
    startCircle();
  }

  switch (G.mode) {
    case 'pending':
      if (dx * dx + dy * dy > 100) {
        clearTimeout(G.hold);
        const adx = Math.abs(dx), ady = Math.abs(dy);
        if (Math.min(adx, ady) / Math.max(adx, ady) > 0.55) {
          G.mode = 'slit';                     // diagonal
          slit = { span: 0, ux: Math.sign(dx) || 1, uy: 0, held: true };
        } else if (adx >= ady) {
          G.mode = 'scratch';
          loop = null; seq = null;
          G.sx = x; G.anchorPos = pos; scratchPos = pos;
        } else if (dy < 0) {
          G.mode = 'up';
          speedHold = { target: 1, wob: 0 };   // drag up: fast-forward
        } else {
          G.mode = 'stutter';
          G.sx = x; G.anchorPos = pos;
          stut = { start: pos, len: 0.03, t: 0 };
        }
        lock();
      }
      break;
    case 'scratch':
      scratchPos = G.anchorPos + (x - G.sx) * spp();
      break;
    case 'up':
      speedHold = { target: 1 + clamp((G.sy - y) / (S.h * 0.5), 0, 1) * 5, wob: 0 };
      break;
    case 'stutter':
      stut.len = clamp(((y - G.sy) / S.h) * 2.2, 0.03, 2.2);
      stut.start = G.anchorPos + (x - G.sx) * spp() * 0.5;
      break;
    case 'circle': {
      const r = loop.ring;
      const d = Math.hypot(x - r.cx, y - r.cy);
      r.rad = r.rad * 0.85 + d * 0.15;
      loop.len = lenFromRad(r.rad);
      break;
    }
    case 'slit': {
      // the drag vector from the press point sets the direction and the spread
      const sx = x - G.ox, sy = y - G.oy;
      const len = Math.hypot(sx, sy) || 1;
      slit.ux = sx / len; slit.uy = sy / len;
      slit.span = clamp((len / S.w) * CFG.SLIT, 0, 4);
      break;
    }
    case 'freeze':
      if (Math.hypot(x - G.ox, y - G.oy) > 14) startBrush(x, y);
      break;
    case 'brush':
      paintTo(x, y);
      break;
  }
  if (G.mode !== 'brush') pushTrail(x, y, G.mode, false);
});

/* time brush: hold to catch a moment, then move to paint it onto the picture.
   Each dab is a soft radial falloff at low strength, so edges feather out and
   repeated passes build the paint up instead of cutting a hard edge. */

function startBrush(x, y) {
  const m = document.createElement('canvas');
  m.width = clip.W; m.height = clip.H;
  const L = { t: fz ? fz.pos : pos, mask: m, mctx: m.getContext('2d') };
  layers.push(L);
  if (layers.length > CFG.LAYERS) layers.shift();
  G.mode = 'brush';
  G.brush = L;
  G.lastDab = null;
  fz = null;
  lock();
  paintTo(G.ox, G.oy);
  paintTo(x, y);
  btnWipe.disabled = false;
}

function dab(L, cx, cy) {
  const r = brushR();
  const g = L.mctx.createRadialGradient(cx, cy, 0, cx, cy, r);
  g.addColorStop(0, 'rgba(0,0,0,0.30)');
  g.addColorStop(0.35, 'rgba(0,0,0,0.24)');
  g.addColorStop(0.7, 'rgba(0,0,0,0.08)');
  g.addColorStop(1, 'rgba(0,0,0,0)');
  L.mctx.fillStyle = g;
  L.mctx.beginPath();
  L.mctx.arc(cx, cy, r, 0, TAU);
  L.mctx.fill();
}

function paintTo(x, y) {
  const L = G.brush;
  if (!L) return;
  const c = { x: toCX(x), y: toCY(y) };
  if (!G.lastDab) { dab(L, c.x, c.y); G.lastDab = c; return; }
  const d = Math.hypot(c.x - G.lastDab.x, c.y - G.lastDab.y);
  const sp = brushR() * 0.22;
  if (d < sp) return;
  const n = Math.floor(d / sp);
  const ax = G.lastDab.x, ay = G.lastDab.y;
  for (let i = 1; i <= n; i++) {
    const k = (i * sp) / d;
    dab(L, ax + (c.x - ax) * k, ay + (c.y - ay) * k);
  }
  const k = (n * sp) / d;
  G.lastDab = { x: ax + (c.x - ax) * k, y: ay + (c.y - ay) * k };
}

function wipePaint() {
  layers = [];
  btnWipe.disabled = true;
}

function startCircle() {
  const pts = G.samples.filter((p) => G.samples[G.samples.length - 1].t - p.t < 1200);
  let cx = 0, cy = 0;
  pts.forEach((p) => { cx += p.x; cy += p.y; });
  cx /= pts.length; cy /= pts.length;
  let rad = 0;
  pts.forEach((p) => { rad += Math.hypot(p.x - cx, p.y - cy); });
  rad /= pts.length;
  const cw = G.turn > 0; // screen y points down, so positive turning is clockwise
  // keep the stroke as drawn: the loop replays it, wobbles and all
  const t0 = pts[0].t, dur = Math.max(1, pts[pts.length - 1].t - t0);
  const path = pts.map((p) => ({ x: p.x, y: p.y, u: (p.t - t0) / dur }));
  loop = { start: pos, len: lenFromRad(rad), boom: !cw, t: 0, ring: { cx, cy, rad, cw, path } };
  seq = null; stut = null;
  rate = 1;
  G.mode = 'circle';
  lock();
}

/* two thumbs: a second finger on the picture takes the other role. If the
   first finger runs a tool, the second scratches; if the first is scratching,
   the second plays the last tool you used. Two quick fingers together, lifted
   without moving, open the tool wheel. */
let P2 = null;        // { id, x0, y0, x, y, moved, role, tool, pos, anchor, hist }
let TT = null;        // a two-finger tap in progress { t0, p1up, p2up }
let lastTool = null;
const PAD_OK = (t) => t && !['hand', 'brush', 'zoom', 'smear', 'loadb'].includes(t.id);

function secondDown(e) {
  if (P2) return;
  e.preventDefault();
  surface.setPointerCapture(e.pointerId);
  const { x, y } = local(e);
  P2 = { id: e.pointerId, x0: x, y0: y, x, y, moved: false, role: null, tool: null, pos: 0, anchor: 0, hist: [{ x, t: now() }] };
  if (G.mode === 'pending' && now() - G.st < 250) {
    TT = { t0: G.st, p1up: false, p2up: false };
    clearTimeout(G.hold);   // two fingers down together: not a hold
  }
}

function secondMove(x, y) {
  P2.x = x; P2.y = y;
  const t = now();
  P2.hist.push({ x, t });
  while (P2.hist.length > 2 && t - P2.hist[0].t > 90) P2.hist.shift();
  if (!P2.moved) {
    if (Math.hypot(x - P2.x0, y - P2.y0) < 8) return;
    P2.moved = true;
    TT = null;
    if (G.tool && G.tool.id !== 'hand') {
      P2.role = 'scratch';
      loop = null; seq = null;
      if (replay) endPlayback();
      P2.anchor = pos; P2.x0 = x; P2.pos = pos;
    } else if (PAD_OK(lastTool)) {
      P2.role = 'tool';
      P2.tool = lastTool;
      if (P2.tool.down) P2.tool.down(toolPoint(x, y));
    } else {
      P2.role = null;   // nothing to pair with yet: pick a tool once, then it works
      toast('pick a tool first, then a second thumb plays it');
      return;
    }
  }
  if (P2.role === 'scratch') P2.pos = P2.anchor + (x - P2.x0) * spp();
  else if (P2.role === 'tool') {
    P2.tool.move(toolPoint(x, y));
    if (replay && P2.tool.latch) liveFx[P2.tool.id] = fx[P2.tool.id];
  }
}

function secondUp(e) {
  const p = P2;
  P2 = null;
  if (p.role === 'scratch') {
    // throw, like a one-finger scratch
    const h = p.hist, a = h[0], b = h[h.length - 1];
    const dtt = (b.t - a.t) / 1000;
    rate = dtt > 0.008 && now() - b.t < 80 ? clamp(((b.x - a.x) / dtt) * spp(), -16, 16) : 0;
  } else if (p.role === 'tool' && p.tool.up) p.tool.up();
  if (TT && !p.moved) { TT.p2up = true; checkTwoTap(); }
}

function checkTwoTap() {
  if (!TT || !TT.p1up || !TT.p2up) return;
  const quick = now() - TT.t0 < 500;
  TT = null;
  if (quick) openWheel(S.w / 2, S.h / 2);
}

const TAP = { t: 0, x: 0, y: 0, timer: 0 };
let playFlash = 0;

function endGesture(e) {
  if (P2 && e && e.pointerId === P2.id) { secondUp(e); return; }
  if (WH.drag) { if (!e || e.pointerId === WH.drag.id) wheelUp(e); return; }
  if (!G.down || (e && e.pointerId !== G.id)) return;
  clearTimeout(G.hold);
  const t = now();
  if (TT) {
    // first finger of a possible two-finger tap: no play/pause, wait for the other
    G.down = false; G.lastUp = t; G.mode = 'idle';
    TT.p1up = true;
    checkTwoTap();
    return;
  }
  if (G.mode === 'pending' && t - G.st < 260) {
    // single tap plays / pauses, double tap opens the tool wheel
    G.down = false; G.lastUp = t; G.mode = 'idle';
    if (TAP.timer && t - TAP.t < 320 && Math.hypot(G.x - TAP.x, G.y - TAP.y) < 40) {
      clearTimeout(TAP.timer); TAP.timer = 0;
      openWheel(G.x, G.y);
    } else {
      TAP.t = t; TAP.x = G.x; TAP.y = G.y;
      TAP.timer = setTimeout(() => { TAP.timer = 0; playing = !playing; playFlash = now(); }, 260);
    }
    return;
  }
  if (G.tool.id !== 'hand') {
    if (G.mode === 'tool' && G.tool.up) G.tool.up();
    G.down = false; G.lastUp = t; G.mode = 'idle';
    return;
  }
  switch (G.mode) {
    case 'pending':
      break;
    case 'scratch': {
      const s = G.samples, last = s[s.length - 1];
      let k = s.length - 1;
      while (k > 0 && last.t - s[k - 1].t < 90) k--;
      const first = s[k];
      const dtt = (last.t - first.t) / 1000;
      const v = dtt > 0.008 && t - last.t < 80 ? (last.x - first.x) / dtt : 0;
      rate = clamp(v * spp(), -16, 16);
      break;
    }
    case 'up':
      speedHold = null;   // springs back to normal speed
      break;
    case 'stutter':
      stut = null;
      rate = 1;
      break;
    case 'freeze':
      fz = null;
      break;
    case 'slit':
      if (slit) slit.held = false; // springs back
      break;
    case 'brush':
      G.brush = null;
      break;
  }
  G.down = false;
  G.lastUp = now();
  G.mode = 'idle';
}
surface.addEventListener('pointerup', endGesture);
surface.addEventListener('pointercancel', endGesture);
// a two-finger tap on a trackpad (a right-click) opens the effects wheel too;
// a long press on a touch screen stays the hold gesture
surface.addEventListener('contextmenu', (e) => {
  e.preventDefault();
  if (!clip || (e.pointerType && e.pointerType !== 'mouse') || G.down) return;
  if (WH.open) closeWheel(false); else openWheel();
});

/* ---------------------------------------------------------------- tools */

// Every tool turns the picture into an XY pad. A tool says what X and Y do
// (edge labels L/R/T/B), and what happens on down / move / up. Latched tools
// write into `fx`, so their effect stays after you let go and shows as a chip.

const SEGMENTS = [2, 4, 6, 8, 10, 12];
const MODES = ['screen', 'lighten', 'overlay', 'multiply', 'difference', 'exclusion'];

function toolPoint(x, y) {
  return { x, y, nx: clamp(x / S.w, 0, 1), ny: clamp(y / S.h, 0, 1), cx: toCX(x), cy: toCY(y) };
}

function beginTool() {
  G.mode = 'tool';
  lock();
  const p = toolPoint(G.x, G.y);
  if (G.tool.down) G.tool.down(p);
  if (G.tool.move) G.tool.move(p);
  noteLive();
}

const TOOLS = [
  { id: 'hand', group: 'time', name: 'Scratch' },
  {
    id: 'speed', group: 'time', name: 'Speed', T: 'faster', B: 'reverse', L: 'steady', R: 'wobble',
    down() { speedHold = { target: 1, wob: 0 }; },
    move(p) {
      const v = 1 - p.ny;
      speedHold = { target: v < 0.5 ? -2 + 3 * (v / 0.5) : 1 + 3 * ((v - 0.5) / 0.5), wob: p.nx };
    },
    up() { speedHold = null; },
    info: () => rate.toFixed(2) + '×',
  },
  {
    id: 'echo', group: 'time', name: 'Echo', L: 'short', R: 'long', T: 'strong', B: 'faint', latch: true,
    move(p) { fx.echo = { delay: 0.05 + p.nx * 1.95, amt: (1 - p.ny) * 0.85 }; },
    info: () => fx.echo ? fx.echo.delay.toFixed(2) + 's · ' + Math.round(fx.echo.amt * 100) + '%' : '',
  },
  {
    id: 'slit', group: 'time', name: 'Slit-scan', L: 'angle', R: 'angle', T: 'more time', B: 'flat', latch: true,
    move(p) {
      const a = p.nx * Math.PI;
      slit = { span: (1 - p.ny) * 4, ux: Math.cos(a), uy: Math.sin(a), held: true };
    },
    info: () => slit ? slit.span.toFixed(2) + 's across' : '',
  },
  {
    id: 'brush', group: 'time', name: 'Time brush', hint: 'press to catch this moment, drag to paint it',
    down(p) { startBrush(p.x, p.y); G.mode = 'tool'; },
    move(p) { paintTo(p.x, p.y); },
    up() { G.brush = null; },
    info: () => 'painting ' + fmt(wrapT(G.brush ? G.brush.t : pos)),
  },
  {
    id: 'step', group: 'time', name: 'Stop-motion', L: '2 fps', R: '12 fps', T: 'jitter', B: 'steady', latch: true,
    move(p) { fx.step = { fps: Math.round(2 + p.nx * 10), jit: 1 - p.ny }; },
    info: () => fx.step ? fx.step.fps + ' fps' + (fx.step.jit > 0.05 ? ' · jitter ' + Math.round(fx.step.jit * 100) + '%' : '') : '',
  },
  {
    id: 'ripple', group: 'time', name: 'Ripple', L: 'few waves', R: 'many waves', T: 'deep', B: 'shallow', latch: true,
    move(p) { fx.ripple = { freq: 0.5 + p.nx * 6, amp: (1 - p.ny) * 1.5 }; },
    info: () => fx.ripple ? fx.ripple.freq.toFixed(1) + ' waves · ' + fx.ripple.amp.toFixed(2) + 's deep' : '',
  },
  {
    id: 'rgbtime', group: 'time', name: 'RGB time', L: 'tight', R: 'far apart', T: 'full', B: 'subtle', latch: true,
    move(p) { fx.rgbtime = { delay: 0.03 + Math.pow(p.nx, 1.5), mix: 1 - p.ny }; },
    info: () => fx.rgbtime ? 'channels ' + fx.rgbtime.delay.toFixed(2) + 's apart' : '',
  },
  {
    id: 'lexp', group: 'time', name: 'Long exposure', L: 'short', R: 'long', T: 'strong', B: 'light', latch: true,
    move(p) { fx.lexp = { n: Math.round(2 + p.nx * 38), amt: 0.2 + (1 - p.ny) * 0.8 }; },
    info: () => fx.lexp ? fx.lexp.n + ' frames' : '',
  },
  {
    id: 'grade', group: 'colour', name: 'Grade', L: 'warm', R: 'cool', T: 'contrast', B: 'flat', latch: true,
    move(p) { fx.grade = { temp: 1 - 2 * p.nx, con: 0.4 + (1 - p.ny) * 1.6 }; },
    info: () => fx.grade ? (fx.grade.temp >= 0 ? 'warm ' : 'cool ') + Math.abs(fx.grade.temp).toFixed(2) + ' · contrast ' + fx.grade.con.toFixed(2) : '',
  },
  {
    id: 'hue', group: 'colour', name: 'Hue', L: 'hue', R: 'hue', T: 'vivid', B: 'grey', latch: true,
    move(p) { fx.hue = { rot: p.nx * TAU, sat: (1 - p.ny) * 2.2 }; },
    info: () => fx.hue ? Math.round((fx.hue.rot / TAU) * 360) + '° · saturation ' + fx.hue.sat.toFixed(2) : '',
  },
  {
    id: 'duo', group: 'colour', name: 'Duotone', L: 'shadow hue', R: 'shadow hue', T: 'light hue', B: 'light hue', latch: true,
    move(p) { fx.duo = { a: p.nx * 360, b: (1 - p.ny) * 360 }; },
    info: () => fx.duo ? 'shadows ' + Math.round(fx.duo.a) + '° · lights ' + Math.round(fx.duo.b) + '°' : '',
  },
  {
    id: 'crush', group: 'colour', name: 'Crush', L: 'few colours', R: 'smooth', T: 'split', B: 'clean', latch: true,
    move(p) { fx.crush = { levels: Math.round(2 + Math.pow(p.nx, 1.5) * 30), split: (1 - p.ny) * 12 * PX() }; },
    info: () => fx.crush ? (fx.crush.levels >= 32 ? 'smooth' : fx.crush.levels + ' levels') + ' · split ' + fx.crush.split.toFixed(0) + 'px' : '',
  },
  {
    id: 'sol', group: 'colour', name: 'Solarize', L: 'flip darks', R: 'flip lights', T: 'full', B: 'subtle', latch: true,
    move(p) { fx.sol = { th: 20 + p.nx * 220, mix: 1 - p.ny }; },
    info: () => fx.sol ? 'above ' + Math.round(fx.sol.th) + ' · ' + Math.round(fx.sol.mix * 100) + '%' : '',
  },
  {
    id: 'bit', group: 'colour', name: '1-bit', L: 'lighter', R: 'darker', T: 'dither', B: 'hard', latch: true,
    move(p) { fx.bit = { th: 40 + p.nx * 180, dither: 1 - p.ny }; },
    info: () => fx.bit ? 'threshold ' + Math.round(fx.bit.th) + ' · dither ' + Math.round(fx.bit.dither * 100) + '%' : '',
  },
  {
    id: 'thermal', group: 'colour', name: 'Thermal', L: 'shift', R: 'shift', T: 'full', B: 'subtle', latch: true,
    move(p) { fx.thermal = { shift: p.nx, mix: 1 - p.ny }; },
    info: () => fx.thermal ? 'shift ' + Math.round(fx.thermal.shift * 100) + '%' : '',
  },
  {
    id: 'vhs', group: 'colour', name: 'VHS', L: 'clean', R: 'worn', T: 'tracking', B: 'steady', latch: true,
    move(p) { fx.vhs = { wear: p.nx, track: 1 - p.ny }; },
    info: () => fx.vhs ? 'wear ' + Math.round(fx.vhs.wear * 100) + '% · tracking ' + Math.round(fx.vhs.track * 100) + '%' : '',
  },
  {
    id: 'outline', group: 'colour', name: 'Outline', L: 'few lines', R: 'many lines', T: 'lines only', B: 'over picture', latch: true,
    move(p) { fx.outline = { th: 260 - p.nx * 230, mix: 1 - p.ny }; },
    info: () => fx.outline ? 'edges above ' + Math.round(fx.outline.th) : '',
  },
  {
    id: 'zoom', group: 'space', name: 'Zoom', T: 'closer', B: 'back out', hint: 'press where to zoom', latch: true,
    down(p) { G.z0 = fx.zoom ? fx.zoom.z : 1; G.zc = { cx: p.cx, cy: p.cy }; },
    move(p) {
      const z = clamp(G.z0 * Math.pow(2, -(p.y - G.oy) / (S.h * 0.3)), 1, 10);
      fx.zoom = { cx: G.zc.cx, cy: G.zc.cy, z };
    },
    info: () => fx.zoom ? fx.zoom.z.toFixed(1) + '×' : '',
  },
  {
    id: 'kal', group: 'space', name: 'Kaleido', L: 'mirror', R: '12 segments', T: 'turn', B: 'turn', latch: true,
    move(p) { fx.kal = { n: SEGMENTS[Math.min(SEGMENTS.length - 1, Math.floor(p.nx * SEGMENTS.length))], rot: p.ny * TAU }; },
    info: () => fx.kal ? fx.kal.n + ' segments' : '',
  },
  {
    id: 'smear', group: 'space', name: 'Smear', hint: 'drag the way the picture should flow', latch: true,
    move(p) {
      const dx = p.x - G.ox, dy = p.y - G.oy, len = Math.hypot(dx, dy);
      if (len < 4) return;
      const k = Math.min(3, len / 50) * PX();
      fx.smear = { vx: (dx / len) * k, vy: (dy / len) * k, amt: clamp(len / (S.w * 0.35), 0, 0.94) };
    },
    info: () => fx.smear ? Math.round(fx.smear.amt * 100) + '%' : '',
  },
  {
    id: 'pix', group: 'space', name: 'Pixelate', L: 'fine', R: 'blocky', T: 'scanlines', B: 'clean', latch: true,
    move(p) { fx.pix = { size: Math.round(2 + Math.pow(p.nx, 1.4) * 30), lines: (1 - p.ny) * 0.6 }; },
    info: () => fx.pix ? fx.pix.size + 'px blocks' : '',
  },
  {
    id: 'tile', group: 'space', name: 'Tile', L: '1', R: '6 × 6', T: 'scroll', B: 'still', latch: true,
    move(p) { fx.tile = { n: 1 + Math.floor(p.nx * 5.99), speed: 1 - p.ny }; },
    info: () => fx.tile ? fx.tile.n + ' × ' + fx.tile.n + (fx.tile.speed > 0.05 ? ' · scrolling' : '') : '',
  },
  {
    id: 'wave', group: 'space', name: 'Wave', L: 'long', R: 'tight', T: 'strong', B: 'calm', latch: true,
    move(p) { fx.wave = { freq: 0.5 + p.nx * 12, amp: (1 - p.ny) * 30 }; },
    info: () => fx.wave ? fx.wave.freq.toFixed(1) + ' waves · ' + Math.round(fx.wave.amp) + 'px' : '',
  },
  {
    id: 'tunnel', group: 'space', name: 'Tunnel', L: 'turn left', R: 'turn right', T: 'fall in', B: 'pull out', latch: true,
    move(p) { fx.tunnel = { rot: (p.nx - 0.5) * 0.12, zoom: 1 + (0.5 - p.ny) * 0.12 }; },
    info: () => fx.tunnel ? 'turn ' + (fx.tunnel.rot * 180 / Math.PI).toFixed(1) + '° · zoom ' + fx.tunnel.zoom.toFixed(3) : '',
  },
  {
    id: 'psort', group: 'space', name: 'Pixel sort', L: 'sort more', R: 'sort less', T: 'vertical', B: 'horizontal', latch: true,
    move(p) { fx.psort = { th: 20 + p.nx * 200, vertical: p.ny < 0.5 }; },
    info: () => fx.psort ? (fx.psort.vertical ? 'vertical' : 'horizontal') + ' · above ' + Math.round(fx.psort.th) : '',
  },
  {
    id: 'rutt', group: 'space', name: 'Rutt-Etra', L: 'few lines', R: 'many lines', T: 'tall', B: 'flat', latch: true,
    move(p) { fx.rutt = { lines: Math.round(12 + p.nx * 88), amp: (1 - p.ny) * 0.3 }; },
    info: () => fx.rutt ? fx.rutt.lines + ' lines' : '',
  },
  {
    id: 'half', group: 'space', name: 'Halftone', L: 'fine', R: 'coarse', T: 'colour', B: 'ink', latch: true,
    move(p) { fx.half = { cell: 3 + p.nx * 21, colour: p.ny < 0.5 }; },
    info: () => fx.half ? (fx.half.colour ? 'colour' : 'ink') + ' · ' + fx.half.cell.toFixed(0) + 'px dots' : '',
  },
  {
    id: 'blend', group: 'mash', name: 'Blend B', L: 'A', R: 'B', T: 'screen', B: 'exclusion', latch: true, needsB: true,
    move(p) { fx.blend = { mix: p.nx, mode: MODES[Math.min(MODES.length - 1, Math.floor(p.ny * MODES.length))] }; },
    info: () => fx.blend ? fx.blend.mode + ' · ' + Math.round(fx.blend.mix * 100) + '% B' : '',
  },
  {
    id: 'motion', group: 'mash', name: 'Motion only', L: '1 frame', R: '½ second', T: 'bright', B: 'dim', latch: true,
    move(p) { fx.motion = { delay: 1 / clip.fps + p.nx * 0.5, gain: Math.round((1 - p.ny) * 3) }; },
    info: () => fx.motion ? 'against ' + fx.motion.delay.toFixed(2) + 's ago · gain ' + (1 << fx.motion.gain) + '×' : '',
  },
  {
    id: 'mosh', group: 'mash', name: 'Datamosh', L: 'small blocks', R: 'big blocks', T: 'sticky', B: 'loose', latch: true,
    move(p) { fx.mosh = { block: 4 + Math.round(p.nx * 20), th: 10 + (1 - p.ny) * 160 }; },
    info: () => fx.mosh ? 'blocks ' + fx.mosh.block + ' · holds below ' + Math.round(fx.mosh.th) : '',
  },
  {
    id: 'key', group: 'mash', name: 'Key B', L: 'shadows', R: 'most', T: 'soft', B: 'hard', latch: true, needsB: true,
    move(p) { fx.key = { th: 20 + p.nx * 220, soft: 4 + (1 - p.ny) * 80 }; },
    info: () => fx.key ? 'B shows below ' + Math.round(fx.key.th) : '',
  },
  { id: 'loadb', group: 'mash', name: 'Load clip B', action() { pickB(); } },
];
const TOOL = Object.fromEntries(TOOLS.map((t) => [t.id, t]));
let tool = TOOL.hand;
G.tool = tool;
let toolFlash = 0;

let afterB = 'blend';
function pickB() { fileTarget = 'B'; fileIn.click(); }

function selectTool(t) {
  if (!t.action && t.id !== 'hand') lastTool = t;
  if (t.action) { t.action(); return; }
  if (t.needsB && !clipB) { afterB = t.id; pickB(); return; }
  if (t.id === 'blend' && !fx.blend) fx.blend = { mix: 0.5, mode: 'screen' };
  if (t.id === 'key' && !fx.key) fx.key = { th: 90, soft: 30 };
  tool = t;
  toolFlash = now();
}

/* ---------------------------------------------------------------- wheel */

// A drum picker like the iOS alarm wheel. Items sit on a cylinder; the one
// facing you is selected. The drum follows the finger 1:1, coasts after a
// flick with exponential friction, then a critically damped spring settles
// it on the nearest item. Past either end it stretches like rubber.

const ITEM = 46;                   // px between items at the front of the drum
const STEP = 0.34;                 // radians between items around the drum
const RADIUS = ITEM / STEP;
const WH = {
  open: false, x: 0, y: 0, pos: 0, vel: 0, target: 0,
  mode: 'idle', drag: null, closeAfter: false, closeT: 0, wheelT: 0, idleT: 0,
};
const maxIdx = () => TOOLS.length - 1;

TOOLS.forEach((t) => {
  const el = document.createElement('div');
  el.className = 'wi';
  // the group label hangs off the right of the name, so the name stays centred
  el.innerHTML = '<span><small></small></span>';
  el.firstChild.prepend(t.name);
  el.querySelector('small').textContent = t.group;
  el.querySelector('small').style.color = 'rgb(' + rgbOf(t) + ')';
  wheelList.append(el);
});

function rubber(p) {
  const m = maxIdx();
  if (p < 0) return p * 0.3;
  if (p > m) return m + (p - m) * 0.3;
  return p;
}

function renderWheel() {
  const on = clamp(Math.round(WH.pos), 0, maxIdx());
  const kids = wheelList.children;
  for (let i = 0; i < kids.length; i++) {
    const el = kids[i];
    const a = (i - WH.pos) * STEP;
    if (Math.abs(a) > 1.45) { el.style.visibility = 'hidden'; continue; }
    el.style.visibility = 'visible';
    const y = Math.sin(a) * RADIUS;
    const z = (Math.cos(a) - 1) * RADIUS;
    el.style.transform = 'translate3d(0,' + y.toFixed(2) + 'px,' + z.toFixed(2) + 'px) rotateX(' + (-a).toFixed(4) + 'rad)';
    el.style.opacity = Math.pow(Math.max(0, Math.cos(a)), 2.2).toFixed(3);
    const g = Math.round(17 + Math.min(1, Math.abs(i - WH.pos) / 2.5) * 140);   // ink fading to grey
    el.style.color = 'rgb(' + g + ',' + g + ',' + g + ')';
    el.classList.toggle('on', i === on);
  }
}

// the wheel keeps the same share of the picture on any screen
function sizeWheel() {
  WH.s = clamp(Math.min(S.w / 790, S.h / 445), 0.62, 2.4);
  wheelEl.style.setProperty('--ws', WH.s.toFixed(3));
}
function openWheel(x, y) {
  if (!clip) return;
  clearTimeout(toastTimer); hideStatus();   // nothing sits over the selected tool
  WH.open = true;
  WH.pos = WH.target = TOOLS.indexOf(tool);
  WH.vel = 0;
  WH.mode = 'idle';
  WH.closeAfter = false;
  WH.x = S.w / 2;   // the wheel always opens in the middle of the picture
  WH.y = S.h / 2;
  sizeWheel();
  wheelEl.style.left = WH.x + 'px';
  wheelEl.style.top = WH.y + 'px';
  wheelEl.hidden = false;
  wheelEl.classList.remove('out');
  renderWheel();
  clearTimeout(WH.closeT);
}

function closeWheel(apply) {
  if (!WH.open) return;
  clearTimeout(WH.closeT); clearTimeout(WH.wheelT); clearTimeout(WH.idleT);
  WH.open = false;
  WH.drag = null;
  WH.mode = 'idle';
  wheelEl.hidden = true;
  if (apply) selectTool(TOOLS[clamp(Math.round(WH.pos), 0, maxIdx())]);
}

function settleTo(target, thenClose) {
  WH.target = clamp(target, 0, maxIdx());
  WH.mode = 'snap';
  WH.closeAfter = thenClose;
}

function wheelTick(dt) {
  if (!WH.open) return;
  if (WH.mode === 'coast') {
    WH.vel *= Math.exp(-dt * 3.4);
    if (WH.pos < 0 || WH.pos > maxIdx()) WH.vel *= Math.exp(-dt * 18);
    WH.pos += WH.vel * dt;
    if (Math.abs(WH.vel) < 3.5 || WH.pos < -0.6 || WH.pos > maxIdx() + 0.6) {
      settleTo(Math.round(WH.pos + WH.vel * 0.06), true);
    }
  }
  if (WH.mode === 'snap') {
    const w = 15;                                  // spring stiffness (rad/s)
    for (let k = 0; k < 4; k++) {                  // a few substeps keep it stable
      const h = dt / 4;
      const acc = -w * w * (WH.pos - WH.target) - 2 * w * WH.vel;
      WH.vel += acc * h;
      WH.pos += WH.vel * h;
    }
    if (Math.abs(WH.pos - WH.target) < 0.002 && Math.abs(WH.vel) < 0.03) {
      WH.pos = WH.target; WH.vel = 0; WH.mode = 'idle';
      if (WH.closeAfter) { WH.closeAfter = false; WH.closeT = setTimeout(() => closeWheel(true), 220); }
    }
  }
  renderWheel();
}

function wheelDown(e, x, y) {
  clearTimeout(WH.closeT); clearTimeout(WH.idleT);
  WH.mode = 'drag';
  WH.vel = 0;
  WH.drag = { id: e.pointerId, x0: x, y0: y, pos0: WH.pos, moved: false, hist: [{ t: now(), p: WH.pos }] };
}

function wheelMove(x, y) {
  const d = WH.drag;
  const dy = y - d.y0;
  if (Math.abs(dy) > 3) d.moved = true;
  WH.pos = rubber(d.pos0 - dy / (ITEM * (WH.s || 1)));
  const t = now();
  d.hist.push({ t, p: WH.pos });
  while (d.hist.length > 2 && t - d.hist[0].t > 90) d.hist.shift();
}

function wheelUp(e) {
  const d = WH.drag;
  WH.drag = null;
  if (!d) return;
  if (!d.moved) {
    // a tap: on a row picks that row, outside the wheel closes it unchanged
    const { x, y } = e ? local(e) : { x: WH.x, y: WH.y };
    const ws = WH.s || 1;
    if (Math.abs(x - WH.x) > 180 * ws || Math.abs(y - WH.y) > 170 * ws) { closeWheel(false); return; }
    const rel = clamp((y - WH.y) / (RADIUS * ws), -0.99, 0.99);
    settleTo(Math.round(WH.pos) + Math.round(Math.asin(rel) / STEP), true);
    return;
  }
  const h = d.hist, a = h[0], b = h[h.length - 1];
  const dtt = (b.t - a.t) / 1000;
  WH.vel = dtt > 0.01 && now() - b.t < 80 ? clamp((b.p - a.p) / dtt, -60, 60) : 0;
  if (Math.abs(WH.vel) > 3.5 && WH.pos >= 0 && WH.pos <= maxIdx()) WH.mode = 'coast';
  else settleTo(Math.round(WH.pos + WH.vel * 0.06), true);
}

surface.addEventListener('wheel', (e) => {
  if (!clip) return;
  e.preventDefault();
  if (!WH.open) openWheel(H.in ? H.x : S.w / 2, H.in ? H.y : S.h / 2);
  clearTimeout(WH.closeT); clearTimeout(WH.idleT);
  const notch = e.deltaMode === 1 || (Math.abs(e.deltaY) >= 50 && Number.isInteger(e.deltaY));
  if (notch) {
    // a mouse wheel click moves exactly one item, springing there
    settleTo(Math.round(WH.target) + Math.sign(e.deltaY), false);
  } else {
    // trackpad: the drum rides the scroll directly, then settles
    WH.mode = 'drag';
    WH.vel = 0;
    WH.pos = rubber(WH.pos + e.deltaY / ITEM);
    clearTimeout(WH.wheelT);
    WH.wheelT = setTimeout(() => settleTo(Math.round(WH.pos), false), 90);
  }
  WH.idleT = setTimeout(() => closeWheel(true), 1100);
}, { passive: false });

document.addEventListener('pointerdown', (e) => {
  if (WH.open && !surface.contains(e.target) && e.target !== btnTool) closeWheel(false);
});

/* ---------------------------------------------------------------- effect chips */

let stackSig = '';
function renderStack() {
  const items = [];
  if (loop) items.push(['loop', 'Loop ' + loop.len.toFixed(1) + 's', () => { loop = null; }]);
  if (slit && slit.held && G.mode !== 'slit') items.push(['slit', 'Slit-scan', () => { slit.held = false; }]);
  if (layers.length) items.push(['paint', 'Paint ' + layers.length, wipePaint]);
  for (const k of Object.keys(fx)) {
    if (!fx[k]) continue;
    items.push([k, TOOL[k] ? TOOL[k].name : k, () => { if (replay) liveFx[k] = undefined; delete fx[k]; }]);
  }
  const sig = items.map((i) => i[1]).join('|');
  btnReset.hidden = !items.length;
  if (sig === stackSig) return;
  stackSig = sig;
  stackEl.innerHTML = '';
  for (const [, name, off] of items) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'fxchip';
    b.title = 'Remove ' + name;
    b.textContent = name;
    const x = document.createElement('span');
    x.className = 'x';
    x.textContent = '×';
    b.append(x);
    b.onclick = () => { off(); stackSig = null; renderStack(); };
    stackEl.append(b);
  }
}

/* ---------------------------------------------------------------- colour */

const BAYER = [0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5];

function hsl2rgb(h, s, l) {
  h = (((h % 360) + 360) % 360) / 360;
  const f = (n) => {
    const k = (n + h * 12) % 12;
    return 255 * (l - s * Math.min(l, 1 - l) * Math.max(-1, Math.min(k - 3, 9 - k, 1)));
  };
  return [f(0), f(8), f(4)];
}

function mul3(a, b) {
  const r = new Array(9);
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
    r[i * 3 + j] = a[i * 3] * b[j] + a[i * 3 + 1] * b[3 + j] + a[i * 3 + 2] * b[6 + j];
  }
  return r;
}

function hueMatrix(a) {
  const c = Math.cos(a), s = Math.sin(a);
  return [
    0.213 + c * 0.787 - s * 0.213, 0.715 - c * 0.715 - s * 0.715, 0.072 - c * 0.072 + s * 0.928,
    0.213 - c * 0.213 + s * 0.143, 0.715 + c * 0.285 + s * 0.140, 0.072 - c * 0.072 - s * 0.283,
    0.213 - c * 0.213 - s * 0.787, 0.715 - c * 0.715 + s * 0.715, 0.072 + c * 0.928 + s * 0.072,
  ];
}

function satMatrix(s) {
  return [
    0.213 + 0.787 * s, 0.715 - 0.715 * s, 0.072 - 0.072 * s,
    0.213 - 0.213 * s, 0.715 + 0.285 * s, 0.072 - 0.072 * s,
    0.213 - 0.213 * s, 0.715 - 0.715 * s, 0.072 + 0.928 * s,
  ];
}

// One pass over the pixels: hue/saturation and grade as a single matrix, then
// duotone, posterize and an RGB split. The buffer is small, so this is cheap.
function colour(c) {
  const g = fx.grade, h = fx.hue, d = fx.duo, k = fx.crush, so = fx.sol, bt = fx.bit, th = fx.thermal;
  if (!g && !h && !d && !k && !so && !bt && !th) return;
  const TL = th ? thermalTable(th.shift) : null;
  const img = ctx.getImageData(0, 0, c.W, c.H);
  const p = img.data;
  let m = [1, 0, 0, 0, 1, 0, 0, 0, 1], o = [0, 0, 0];
  if (h) m = mul3(satMatrix(h.sat), hueMatrix(h.rot));
  if (g) {
    m = m.map((v) => v * g.con);
    const off = 128 * (1 - g.con);
    o = [off + g.temp * 28, off + g.temp * 6, off - g.temp * 28];
  }
  const lin = !!(g || h);
  const split = k ? Math.round(k.split) : 0;
  const src = split ? new Uint8ClampedArray(p) : p;
  const step = k && k.levels < 32 ? 255 / (k.levels - 1) : 0;
  const A = d ? hsl2rgb(d.a, 0.7, 0.16) : null;
  const B = d ? hsl2rgb(d.b, 0.9, 0.8) : null;
  const W = c.W;
  for (let i = 0, n = p.length; i < n; i += 4) {
    let r, gg, b;
    if (split) {
      const x = (i >> 2) % W;
      const xr = Math.min(W - 1, x + split) - x;
      const xb = Math.max(0, x - split) - x;
      r = src[i + xr * 4]; gg = src[i + 1]; b = src[i + 2 + xb * 4];
    } else { r = p[i]; gg = p[i + 1]; b = p[i + 2]; }
    if (lin) {
      const R = m[0] * r + m[1] * gg + m[2] * b + o[0];
      const Gc = m[3] * r + m[4] * gg + m[5] * b + o[1];
      const Bc = m[6] * r + m[7] * gg + m[8] * b + o[2];
      r = R; gg = Gc; b = Bc;
    }
    if (TL) {
      let l = (0.299 * r + 0.587 * gg + 0.114 * b) | 0;
      l = l < 0 ? 0 : l > 255 ? 255 : l;
      const q = l * 3, mx = th.mix;
      r += (TL[q] - r) * mx; gg += (TL[q + 1] - gg) * mx; b += (TL[q + 2] - b) * mx;
    }
    if (d) {
      let l = (0.299 * r + 0.587 * gg + 0.114 * b) / 255;
      l = l < 0 ? 0 : l > 1 ? 1 : l;
      r = A[0] + (B[0] - A[0]) * l; gg = A[1] + (B[1] - A[1]) * l; b = A[2] + (B[2] - A[2]) * l;
    }
    if (step) { r = Math.round(r / step) * step; gg = Math.round(gg / step) * step; b = Math.round(b / step) * step; }
    if (so) {
      if (r > so.th) r += (255 - 2 * r) * so.mix;
      if (gg > so.th) gg += (255 - 2 * gg) * so.mix;
      if (b > so.th) b += (255 - 2 * b) * so.mix;
    }
    if (bt) {
      const px = i >> 2, x = px % W, y = (px / W) | 0;
      const dz = (BAYER[((y & 3) << 2) | (x & 3)] / 16 - 0.5) * 255 * bt.dither;
      const v = 0.299 * r + 0.587 * gg + 0.114 * b + dz > bt.th ? 255 : 0;
      r = gg = b = v;
    }
    p[i] = r; p[i + 1] = gg; p[i + 2] = b;
  }
  ctx.putImageData(img, 0, 0);
}

/* ---------------------------------------------------------------- more looks */

// Small helper canvases. `work` holds a downscaled copy for effects that read
// pixels (outline, pixel sort, rutt-etra); `grid` holds one pixel per block.
const work = document.createElement('canvas');
const wctx = work.getContext('2d', { willReadFrequently: true });
const grid = document.createElement('canvas');
const gctx = grid.getContext('2d', { willReadFrequently: true });
const acc = document.createElement('canvas');      // long exposure
const actx = acc.getContext('2d');
const mosh = document.createElement('canvas');     // datamosh's held picture
const mctx = mosh.getContext('2d');
let accReady = false, moshPrev = null;

function sizeTo(cv, w, h) { if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; return true; } return false; }
const luma = (d, i) => 0.299 * d[i] + 0.587 * d[i + 1] + 0.114 * d[i + 2];

function workCopy(c, maxW) {
  const w = Math.min(c.W, maxW), h = Math.max(2, Math.round((w * c.H) / c.W));
  sizeTo(work, w, h);
  wctx.drawImage(screen, 0, 0, w, h);
  return { w, h, img: wctx.getImageData(0, 0, w, h) };
}

function blocks(c, cols, rows) {
  sizeTo(grid, cols, rows);
  gctx.drawImage(screen, 0, 0, cols, rows);
  return gctx.getImageData(0, 0, cols, rows).data;
}

// RGB time: red shows now, green a moment ago, blue further back.
function rgbTime(c) {
  const r = fx.rgbtime;
  if (!r) return;
  sizeTo(tmp, c.W, c.H); sizeTo(tmp2, c.W, c.H);
  if (r.mix < 0.999) t2ctx.drawImage(screen, 0, 0);
  ctx.globalCompositeOperation = 'multiply';
  ctx.fillStyle = 'rgb(255,0,0)';
  ctx.fillRect(0, 0, c.W, c.H);
  for (const [k, col] of [[1, 'rgb(0,255,0)'], [2, 'rgb(0,0,255)']]) {
    tctx.globalCompositeOperation = 'copy';
    tctx.drawImage(frameAt(V.vpos - r.delay * k), 0, 0, c.W, c.H);
    tctx.globalCompositeOperation = 'multiply';
    tctx.fillStyle = col;
    tctx.fillRect(0, 0, c.W, c.H);
    tctx.globalCompositeOperation = 'source-over';
    ctx.globalCompositeOperation = 'lighter';
    ctx.drawImage(tmp, 0, 0);
  }
  ctx.globalCompositeOperation = 'source-over';
  if (r.mix < 0.999) { ctx.globalAlpha = 1 - r.mix; ctx.drawImage(tmp2, 0, 0); ctx.globalAlpha = 1; }
}

// Long exposure: frames pile up like an open shutter.
function longExposure(c) {
  const L = fx.lexp;
  if (!L) { accReady = false; return; }
  if (sizeTo(acc, c.W, c.H)) accReady = false;
  actx.globalAlpha = accReady ? 1 / L.n : 1;
  actx.drawImage(screen, 0, 0);
  actx.globalAlpha = 1;
  accReady = true;
  ctx.globalAlpha = L.amt;
  ctx.drawImage(acc, 0, 0);
  ctx.globalAlpha = 1;
}

// Datamosh: hold the picture and only let blocks through where things move,
// the way a video looks when its keyframes are dropped.
function datamosh(c) {
  const m = fx.mosh;
  if (!m) { moshPrev = null; return; }
  const bs = Math.max(4, Math.round(m.block * PX()));
  const cols = Math.ceil(c.W / bs), rows = Math.ceil(c.H / bs);
  const d = blocks(c, cols, rows);
  if (sizeTo(mosh, c.W, c.H) || !moshPrev || moshPrev.length !== d.length) {
    mctx.drawImage(screen, 0, 0);
    moshPrev = new Uint8ClampedArray(d);
    return;
  }
  for (let r = 0; r < rows; r++) {
    for (let q = 0; q < cols; q++) {
      const i = (r * cols + q) * 4;
      const diff = Math.abs(d[i] - moshPrev[i]) + Math.abs(d[i + 1] - moshPrev[i + 1]) + Math.abs(d[i + 2] - moshPrev[i + 2]);
      if (diff > m.th) mctx.drawImage(screen, q * bs, r * bs, bs, bs, q * bs, r * bs, bs, bs);
    }
  }
  moshPrev.set(d);
  ctx.drawImage(mosh, 0, 0);
}

// Outline: edges only (Sobel), as light lines on black or over the picture.
function outline(c) {
  const o = fx.outline;
  if (!o) return;
  const { w, h, img } = workCopy(c, 640);
  const s = img.data;
  const L = new Float32Array(w * h);
  for (let i = 0; i < w * h; i++) L[i] = luma(s, i * 4);
  const out = wctx.createImageData(w, h);
  const p = out.data;
  for (let y = 1; y < h - 1; y++) {
    for (let x = 1; x < w - 1; x++) {
      const i = y * w + x;
      const gx = L[i - w + 1] + 2 * L[i + 1] + L[i + w + 1] - L[i - w - 1] - 2 * L[i - 1] - L[i + w - 1];
      const gy = L[i + w - 1] + 2 * L[i + w] + L[i + w + 1] - L[i - w - 1] - 2 * L[i - w] - L[i - w + 1];
      const v = Math.min(255, Math.max(0, (Math.abs(gx) + Math.abs(gy) - o.th) * 3));
      const j = i * 4;
      p[j] = p[j + 1] = p[j + 2] = v; p[j + 3] = 255;
    }
  }
  wctx.putImageData(out, 0, 0);
  ctx.globalAlpha = o.mix;
  ctx.fillStyle = '#000';
  ctx.fillRect(0, 0, c.W, c.H);
  ctx.globalAlpha = 1;
  ctx.globalCompositeOperation = 'lighter';
  ctx.drawImage(work, 0, 0, c.W, c.H);
  ctx.globalCompositeOperation = 'source-over';
}

// Pixel sort: runs of pixels brighter than the threshold get sorted by
// brightness, so light areas melt into streaks.
function pixelSort(c) {
  const ps = fx.psort;
  if (!ps) return;
  const { w, h, img } = workCopy(c, 480);
  const d = img.data;
  const vert = ps.vertical;
  const lines = vert ? w : h, len = vert ? h : w;
  const idx = (a, b) => 4 * (vert ? b * w + a : a * w + b);
  for (let a = 0; a < lines; a++) {
    let start = -1;
    for (let b = 0; b <= len; b++) {
      const on = b < len && luma(d, idx(a, b)) > ps.th;
      if (on && start < 0) start = b;
      if (!on && start >= 0) {
        if (b - start > 2) {
          const run = [];
          for (let k = start; k < b; k++) { const j = idx(a, k); run.push([luma(d, j), d[j], d[j + 1], d[j + 2]]); }
          run.sort((u, v) => u[0] - v[0]);
          for (let k = start; k < b; k++) { const j = idx(a, k), P = run[k - start]; d[j] = P[1]; d[j + 1] = P[2]; d[j + 2] = P[3]; }
        }
        start = -1;
      }
    }
  }
  wctx.putImageData(img, 0, 0);
  ctx.drawImage(work, 0, 0, c.W, c.H);
}

// Rutt-Etra: the 1970s scan processor. Horizontal lines on black, lifted by
// the brightness underneath, so the picture becomes a relief of lines.
function ruttEtra(c) {
  const r = fx.rutt;
  if (!r) return;
  const { w, h, img } = workCopy(c, 240);
  const d = img.data;
  ctx.fillStyle = '#000';
  ctx.fillRect(0, 0, c.W, c.H);
  ctx.strokeStyle = 'rgba(255,255,255,.92)';
  ctx.lineWidth = Math.max(1, 0.7 * PX());
  ctx.lineJoin = 'round';
  const sx = c.W / (w - 1);
  ctx.beginPath();
  for (let k = 0; k < r.lines; k++) {
    const yy = Math.min(h - 1, Math.floor(((k + 0.5) / r.lines) * h));
    const base = ((k + 0.5) / r.lines) * c.H;
    for (let x = 0; x < w; x++) {
      const y = base - (luma(d, 4 * (yy * w + x)) / 255) * r.amp * c.H;
      if (x === 0) ctx.moveTo(0, y); else ctx.lineTo(x * sx, y);
    }
  }
  ctx.stroke();
}

// Halftone: print dots, sized by brightness.
function halftone(c) {
  const ht = fx.half;
  if (!ht) return;
  const cell = Math.max(3, ht.cell * PX());
  const cols = Math.ceil(c.W / cell), rows = Math.ceil(c.H / cell);
  const d = blocks(c, cols, rows);
  ctx.fillStyle = ht.colour ? '#000' : '#fff';
  ctx.fillRect(0, 0, c.W, c.H);
  if (!ht.colour) { ctx.fillStyle = '#111'; ctx.beginPath(); }
  for (let r = 0; r < rows; r++) {
    for (let q = 0; q < cols; q++) {
      const i = (r * cols + q) * 4;
      const l = luma(d, i) / 255;
      const rad = cell * 0.56 * (ht.colour ? Math.sqrt(l) : Math.sqrt(1 - l));
      if (rad < 0.4) continue;
      const x = (q + 0.5) * cell, y = (r + 0.5) * cell;
      if (ht.colour) {
        ctx.fillStyle = 'rgb(' + d[i] + ',' + d[i + 1] + ',' + d[i + 2] + ')';
        ctx.beginPath(); ctx.arc(x, y, rad, 0, TAU); ctx.fill();
      } else { ctx.moveTo(x + rad, y); ctx.arc(x, y, rad, 0, TAU); }
    }
  }
  if (!ht.colour) ctx.fill();
}

// VHS: red slips sideways, the picture smears, tape noise, a rolling tracking band.
function vhs(c) {
  const v = fx.vhs;
  if (!v) return;
  const k = PX(), T = now() / 1000;
  sizeTo(tmp, c.W, c.H);
  tctx.globalCompositeOperation = 'copy';
  tctx.drawImage(screen, 0, 0);
  tctx.globalCompositeOperation = 'multiply';
  tctx.fillStyle = 'rgb(255,0,0)';
  tctx.fillRect(0, 0, c.W, c.H);
  tctx.globalCompositeOperation = 'source-over';
  ctx.globalCompositeOperation = 'multiply';
  ctx.fillStyle = 'rgb(0,255,255)';
  ctx.fillRect(0, 0, c.W, c.H);
  ctx.globalCompositeOperation = 'lighter';
  ctx.drawImage(tmp, (2 + v.wear * 8) * k, 0);
  ctx.globalCompositeOperation = 'source-over';
  ctx.globalAlpha = 0.2 + v.wear * 0.3;
  ctx.drawImage(screen, 2 * k, 0);
  ctx.globalAlpha = 1;
  const n = Math.round(v.wear * 14);
  for (let i = 0; i < n; i++) {
    ctx.fillStyle = 'rgba(255,255,255,' + (0.08 + Math.random() * 0.25).toFixed(3) + ')';
    ctx.fillRect(0, Math.random() * c.H, c.W, Math.max(1, k));
  }
  if (v.track > 0.03) {
    const bandH = (14 + v.track * 60) * k;
    const y0 = ((T * 70 * (0.3 + v.track)) % (c.H + bandH)) - bandH;
    const step = Math.max(2, Math.round(2 * k));
    for (let y = Math.max(0, y0); y < Math.min(c.H, y0 + bandH); y += step) {
      ctx.drawImage(screen, 0, y, c.W, step, (Math.random() - 0.5) * v.track * 50 * k, y, c.W, step);
    }
    ctx.fillStyle = 'rgba(255,255,255,' + (0.1 * v.track).toFixed(3) + ')';
    ctx.fillRect(0, y0, c.W, bandH);
  }
}

// Thermal palette, as a lookup table built once per setting.
const THERMAL = [[0, 0, 0], [30, 0, 90], [120, 0, 170], [220, 30, 70], [255, 140, 0], [255, 230, 60], [255, 255, 255]];
let thermalLUT = null, thermalKey = '';
function thermalTable(shift) {
  const key = shift.toFixed(3);
  if (key === thermalKey) return thermalLUT;
  const lut = new Uint8ClampedArray(256 * 3);
  for (let i = 0; i < 256; i++) {
    const t = (((i / 255) + shift) % 1) * (THERMAL.length - 1);
    const a = Math.floor(t), f = t - a, A = THERMAL[a], B = THERMAL[Math.min(THERMAL.length - 1, a + 1)];
    for (let ch = 0; ch < 3; ch++) lut[i * 3 + ch] = A[ch] + (B[ch] - A[ch]) * f;
  }
  thermalLUT = lut; thermalKey = key;
  return lut;
}

/* ---------------------------------------------------------------- space */

function spatial(c) {
  const z = fx.zoom, k = fx.kal;
  if (!(z && z.z > 1.01) && !k && !fx.tile && !fx.wave && !fx.pix) return;
  if (tmp2.width !== c.W || tmp2.height !== c.H) { tmp2.width = c.W; tmp2.height = c.H; }
  if (z && z.z > 1.01) {
    t2ctx.drawImage(screen, 0, 0);
    ctx.save();
    ctx.translate(z.cx, z.cy);
    ctx.scale(z.z, z.z);
    ctx.translate(-z.cx, -z.cy);
    ctx.drawImage(tmp2, 0, 0);
    ctx.restore();
  }
  if (k) {
    // every segment shows the same wedge of the picture, mirrored on alternate segments
    t2ctx.drawImage(screen, 0, 0);
    const n = k.n, a = TAU / n, R = Math.hypot(c.W, c.H);
    ctx.fillStyle = '#000';
    ctx.fillRect(0, 0, c.W, c.H);
    for (let i = 0; i < n; i++) {
      ctx.save();
      ctx.translate(c.W / 2, c.H / 2);
      ctx.rotate(i * a);
      if (i % 2) ctx.scale(1, -1);
      ctx.beginPath();
      ctx.moveTo(0, 0);
      ctx.arc(0, 0, R, -a / 2 - 0.01, a / 2 + 0.01);
      ctx.closePath();
      ctx.clip();
      ctx.rotate(-k.rot);
      ctx.scale(1.9, 1.9); // oversample so turning never shows the frame's corners
      ctx.drawImage(tmp2, -c.W / 2, -c.H / 2);
      ctx.restore();
    }
  }
  if (fx.tile) {
    t2ctx.drawImage(screen, 0, 0);
    const n = fx.tile.n, tw = c.W / n, th = c.H / n;
    const off = (((now() / 1000) * fx.tile.speed * 0.3) % 1) * tw;
    for (let r = 0; r < n; r++) for (let q = 0; q <= n; q++) ctx.drawImage(tmp2, q * tw - off, r * th, tw + 0.5, th + 0.5);
  }
  if (fx.wave && fx.wave.amp > 0.3) {
    t2ctx.drawImage(screen, 0, 0);
    const sh = Math.max(2, Math.round(2 * PX())), T = now() / 1000;
    for (let y = 0; y < c.H; y += sh) {
      const dx = fx.wave.amp * PX() * Math.sin((y / c.H) * fx.wave.freq * TAU + T * 3);
      ctx.drawImage(tmp2, 0, y, c.W, sh, dx, y, c.W, sh);
    }
  }
  if (fx.pix && fx.pix.size > 1) {
    const sz = fx.pix.size * PX() * 0.5;
    const w = Math.max(1, Math.round(c.W / sz)), h = Math.max(1, Math.round(c.H / sz));
    t2ctx.drawImage(screen, 0, 0, w, h);
    ctx.imageSmoothingEnabled = false;
    ctx.drawImage(tmp2, 0, 0, w, h, 0, 0, c.W, c.H);
    ctx.imageSmoothingEnabled = true;
    if (fx.pix.lines > 0.02) {
      ctx.fillStyle = 'rgba(0,0,0,' + fx.pix.lines.toFixed(3) + ')';
      const bh = c.H / h;
      for (let y = 0; y < h; y++) ctx.fillRect(0, y * bh + bh * 0.65, c.W, Math.max(1, bh * 0.35));
    }
  }
}

/* ---------------------------------------------------------------- engine */

function step(dt, t) {
  let apos, arate = 1, vol = 0.9, aj = true;

  // paused: a playing take or trace holds its place
  if (replay && !playing) replay.t0 += dt * 1000;
  if (replay && t - replay.t0 > replay.len) {
    if (replay.loop) { replay.t0 = t; replay.i = 0; }
    else if (seq && chips.length) nextInSeq();
    else endPlayback();
  }

  if (replay) {
    const fr = replay.frames;
    const el = t - replay.t0;
    while (replay.i < fr.length - 1 && fr[replay.i + 1].t <= el) {
      replay.i++;
      const f = fr[replay.i];
      if (replay.trail && f.cx != null) pushTrail(f.cx * S.w, f.cy * S.h, f.m, f.brk);
    }
    const f = fr[replay.i];
    pos = f.pos; rate = f.r; persist = f.p; shuffle = f.sh;
    anchor = { x: f.ax * clip.W, y: f.ay * clip.H };
    apos = f.ap; arate = playing ? f.ar : 0; vol = f.v; aj = f.aj && replay.i > 0;
    if (!playing) rate = 0;
    slit = f.sl > 0.005 ? { span: f.sl, ux: f.su, uy: f.sv, held: true } : null;
    // the take's own look, with anything you've changed on top
    fx = Object.assign({}, f.fx || {}, liveFx);
  } else {
    const gm = G.mode;
    if (gm === 'scratch' || (P2 && P2.role === 'scratch')) {
      const target = gm === 'scratch' ? scratchPos : P2.pos;
      const raw = (target - pos) / Math.max(dt, 1e-3);
      rate += (raw - rate) * 0.5;
      pos = target;
      apos = pos; arate = rate; aj = false;
    } else if (gm === 'freeze' && fz) {
      fz.t += dt;
      pos = fz.pos; rate = 0;
      apos = fz.pos + (fz.t % 0.075); arate = 1; vol = 0.55; // a held grain hums under the frozen frame
    } else if (gm === 'stutter' && stut) {
      stut.t += dt;
      pos = stut.start + (stut.t % stut.len); rate = 1;
      apos = pos;
    } else if (loop) {
      if (playing) loop.t += dt;
      const L = loop.len;
      if (loop.boom) {
        const ph = loop.t % (2 * L);
        pos = loop.start + (ph < L ? ph : 2 * L - ph);
        rate = ph < L ? 1 : -1;
      } else {
        pos = loop.start + (loop.t % L);
        rate = 1;
      }
      if (!playing) rate = 0;
      apos = pos; arate = rate;
    } else {
      let target = playing ? 1 : 0;
      if (speedHold) target = speedHold.target + (speedHold.wob > 0.05 ? (Math.sin(t * 0.008) * 1.2 + (Math.random() - 0.5)) * speedHold.wob : 0);
      rate += (target - rate) * (1 - Math.exp(-dt / (speedHold ? 0.12 : 0.45)));
      pos += rate * dt;
      apos = pos; arate = rate;
    }

    // feedback: fast motion blurs, holding melts
    let pt = Math.min(0.55, Math.max(0, Math.abs(rate) - 1.5) * 0.05);
    if (gm === 'freeze' && fz) pt = Math.max(pt, Math.min(0.95, 0.55 + fz.t * 0.2));
    persist += (pt - persist) * (1 - Math.exp(-dt / (pt > persist ? 0.25 : 0.5)));

    // shake energy
    G.revs = G.revs.filter((r) => t - r < 450);
    const energy = G.down ? clamp((G.revs.length - 3) / 5, 0, 1) : 0;
    shuffle = Math.max(energy, shuffle - dt * 1.1);

    // a released slit-scan springs back to a flat picture
    if (slit && !slit.held) {
      slit.span *= Math.exp(-dt / 0.3);
      if (slit.span < 0.005) slit = null;
    }
  }

  // every frame of what is played goes on a short tape (for catching takes)
  // and, while recording, into the trace
  const down = G.down && !replay;
  const fr = {
    t, pos, r: rate, ap: apos, ar: arate, v: vol, aj,
    p: persist, sh: shuffle, ax: anchor.x / clip.W, ay: anchor.y / clip.H,
    cx: down ? G.x / S.w : null, cy: down ? G.y / S.h : null, m: G.mode,
    brk: false,
    sl: slit ? slit.span : 0, su: slit ? slit.ux : 1, sv: slit ? slit.uy : 0,
    fx: Object.assign({}, fx),
  };
  tape.push(fr);
  while (tape.length && t - tape[0].t > 10000) tape.shift();
  if (recState && score) {
    score.frames.push(Object.assign({}, fr, { t: t - recState.t0, brk: down && score.lastSerial !== G.serial }));
    if (down) score.lastSerial = G.serial;
  }

  // shuffle picks nearby frames at random, and drags the sound with it
  V.vpos = pos;
  if (fx.step) {
    // hold each picture for 1/fps, optionally nudged by a stable per-step jitter
    const q = 1 / fx.step.fps, k = Math.floor(pos / q);
    V.vpos = k * q;
    if (fx.step.jit > 0.05) { const r = Math.sin(k * 127.1) * 43758.5453; V.vpos += (r - Math.floor(r) - 0.5) * fx.step.jit * 0.6; }
  }
  if (shuffle > 0.05 && Math.random() < shuffle * 0.7) {
    const off = (Math.random() * 2 - 1) * shuffle * 1.2;
    V.vpos += off;
    apos += off;
  }

  sendAudio(apos, arate, vol, aj, dt);
}

// Slit-scan: the picture is cut into thin bands across the drag direction.
// The band at the leading edge shows now; each band behind it shows a little
// earlier, so motion smears and bends along the diagonal.
function drawSlit(c) {
  const ux = slit.ux, uy = slit.uy;
  const vx = -uy, vy = ux;
  const ps = [0, c.W * ux, c.H * uy, c.W * ux + c.H * uy];
  const pmin = Math.min(...ps), pmax = Math.max(...ps);
  const bw = (pmax - pmin) / CFG.BANDS;
  const Lx = c.W + c.H;
  for (let i = 0; i < CFG.BANDS; i++) {
    const p0 = pmin + i * bw, p1 = p0 + bw + 0.75; // slight overlap hides seams
    const frac = (pmax - (p0 + bw / 2)) / (pmax - pmin);
    const fr = frameAt(V.vpos - slit.span * frac);
    ctx.save();
    ctx.beginPath();
    ctx.moveTo(ux * p0 - vx * Lx, uy * p0 - vy * Lx);
    ctx.lineTo(ux * p0 + vx * Lx, uy * p0 + vy * Lx);
    ctx.lineTo(ux * p1 + vx * Lx, uy * p1 + vy * Lx);
    ctx.lineTo(ux * p1 - vx * Lx, uy * p1 - vy * Lx);
    ctx.closePath();
    ctx.clip();
    ctx.drawImage(fr, 0, 0);
    ctx.restore();
  }
}

// Painted moments: each layer is its frozen frame shown through a soft mask.
function drawLayers(c) {
  if (!layers.length) return;
  if (tmp.width !== c.W || tmp.height !== c.H) { tmp.width = c.W; tmp.height = c.H; }
  for (const L of layers) {
    tctx.globalCompositeOperation = 'copy';
    tctx.drawImage(frameAt(L.t), 0, 0);
    tctx.globalCompositeOperation = 'destination-in';
    tctx.drawImage(L.mask, 0, 0);
    tctx.globalCompositeOperation = 'source-over';
    ctx.drawImage(tmp, 0, 0);
  }
}

// Order: picture (or slit-scan) → clip B → echo → painted moments → smear and
// melt feedback → zoom / kaleido → [feedback copy] → colour → shuffle bands.
// Feedback is copied before colour so colour never compounds on itself.
// Ripple: horizontal bands each look back a different amount, on a moving sine.
function drawRipple(c) {
  const B = 64, bh = c.H / B, T = now() / 1000, r = fx.ripple;
  for (let i = 0; i < B; i++) {
    const y = Math.floor(i * bh);
    const tt = V.vpos - r.amp * (0.5 + 0.5 * Math.sin((y / c.H) * r.freq * TAU + T * 2));
    ctx.drawImage(frameAt(tt), 0, y, c.W, Math.ceil(bh) + 1, 0, y, c.W, Math.ceil(bh) + 1);
  }
}

// Key B: clip B shows through wherever A is darker than the threshold.
function keyB(c) {
  const k = fx.key;
  if (!k || !clipB) return;
  if (tmp.width !== c.W || tmp.height !== c.H) { tmp.width = c.W; tmp.height = c.H; }
  tctx.globalCompositeOperation = 'copy';
  tctx.drawImage(frameAtB(V.vpos), 0, 0, c.W, c.H);
  tctx.globalCompositeOperation = 'source-over';
  const a = ctx.getImageData(0, 0, c.W, c.H), b = tctx.getImageData(0, 0, c.W, c.H);
  const pa = a.data, pb = b.data;
  for (let i = 0, n = pa.length; i < n; i += 4) {
    const l = 0.299 * pa[i] + 0.587 * pa[i + 1] + 0.114 * pa[i + 2];
    let m = (k.th - l) / k.soft + 0.5;
    if (m <= 0) continue;
    if (m > 1) m = 1;
    pa[i] += (pb[i] - pa[i]) * m; pa[i + 1] += (pb[i + 1] - pa[i + 1]) * m; pa[i + 2] += (pb[i + 2] - pa[i + 2]) * m;
  }
  ctx.putImageData(a, 0, 0);
}

function render() {
  const c = clip;
  ctx.globalAlpha = 1;
  ctx.globalCompositeOperation = 'source-over';
  if (slit && slit.span > 0.01) drawSlit(c);
  else if (fx.ripple && fx.ripple.amp > 0.01) drawRipple(c);
  else ctx.drawImage(frameAt(V.vpos), 0, 0);
  if (fx.motion) {
    // subtract the recent past: only what moved stays lit
    ctx.globalCompositeOperation = 'difference';
    ctx.drawImage(frameAt(V.vpos - fx.motion.delay), 0, 0);
    ctx.globalCompositeOperation = 'lighter';
    for (let g = 0; g < fx.motion.gain; g++) ctx.drawImage(screen, 0, 0);
    ctx.globalCompositeOperation = 'source-over';
  }
  if (fx.blend && clipB) {
    ctx.globalCompositeOperation = fx.blend.mode;
    ctx.globalAlpha = fx.blend.mix;
    ctx.drawImage(frameAtB(V.vpos), 0, 0, c.W, c.H);
    ctx.globalCompositeOperation = 'source-over';
    ctx.globalAlpha = 1;
  }
  rgbTime(c);
  if (fx.echo && fx.echo.amt > 0.01) {
    ctx.globalAlpha = fx.echo.amt * 0.6;
    ctx.drawImage(frameAt(V.vpos - fx.echo.delay), 0, 0);
    ctx.globalAlpha = fx.echo.amt * 0.35;
    ctx.drawImage(frameAt(V.vpos - fx.echo.delay * 2), 0, 0);
    ctx.globalAlpha = 1;
  }
  keyB(c);
  datamosh(c);
  drawLayers(c);
  if (fx.tunnel) {
    ctx.save();
    ctx.globalAlpha = 0.78;
    ctx.translate(c.W / 2, c.H / 2);
    ctx.rotate(fx.tunnel.rot);
    ctx.scale(fx.tunnel.zoom, fx.tunnel.zoom);
    ctx.translate(-c.W / 2, -c.H / 2);
    ctx.drawImage(fb, 0, 0);
    ctx.restore();
  }
  if (fx.smear && fx.smear.amt > 0.01) {
    ctx.globalAlpha = fx.smear.amt;
    ctx.drawImage(fb, fx.smear.vx, fx.smear.vy);
    ctx.globalAlpha = 1;
  }
  if (persist > 0.01) {
    const s = 1.012 + persist * 0.025;
    ctx.globalAlpha = persist * 0.92;
    ctx.drawImage(fb, anchor.x * (1 - s), anchor.y * (1 - s) + persist * 1.2 * PX(), c.W * s, c.H * s);
    ctx.globalAlpha = 1;
  }
  longExposure(c);
  spatial(c);
  fctx.drawImage(screen, 0, 0);
  pixelSort(c);
  ruttEtra(c);
  halftone(c);
  outline(c);
  colour(c);
  vhs(c);
  if (shuffle > 0.05) {
    const n = Math.round(shuffle * 9);
    for (let k = 0; k < n; k++) {
      const y = Math.random() * c.H;
      const h = 2 + Math.random() * c.H * 0.12;
      const dx = (Math.random() * 2 - 1) * shuffle * 40 * PX();
      ctx.drawImage(screen, 0, y, c.W, h, dx, y, c.W, h);
    }
  }
  if (recState) recState.rctx.drawImage(screen, 0, 0, recState.rc.width, recState.rc.height);
}

function drawOverlay(t) {
  const w = S.w, h = S.h;
  octx.clearRect(0, 0, w, h);
  if (!clip) return;
  const life = CFG.TRAIL * 1000;
  while (trail.length && t - trail[0].t > life) trail.shift();

  // The hand leaves a trail as wide as the dot. Each run is stroked in a few
  // alpha bands, one stroke per band, so overlapping segments never stack up.
  octx.lineCap = 'round';
  octx.lineJoin = 'round';
  octx.lineWidth = DOT_R * 2;
  const BANDS = 6;
  const colours = [...new Set(trail.map((p) => p.c))];
  for (const col of colours) {
    for (let band = 0; band < BANDS; band++) {
      octx.beginPath();
      let open = false;
      for (let i = 1; i < trail.length; i++) {
        const p0 = trail[i - 1], p1 = trail[i];
        const k = 1 - (t - p1.t) / life;
        if (p1.brk || p1.c !== col || Math.min(BANDS - 1, Math.floor(k * BANDS)) !== band) { open = false; continue; }
        if (!open) { octx.moveTo(p0.x, p0.y); open = true; }
        octx.lineTo(p1.x, p1.y);
      }
      octx.strokeStyle = 'rgba(' + col + ',' + (((band + 0.5) / BANDS) * 0.32).toFixed(3) + ')';
      octx.stroke();
    }
  }

  octx.fillStyle = 'rgba(20,20,20,.9)';
  octx.strokeStyle = 'rgba(20,20,20,.7)';
  octx.lineWidth = 1;

  if (loop && loop.ring) {
    const r = loop.ring;
    // the loop replays the stroke you drew, as the hand's own trail: a dot
    // running along it with the same banded tail, a little stronger than the finger's
    const L = loop.len, P = r.path, col = GROUP_RGB.time;
    let ph, back = 1;
    if (loop.boom) { const q = loop.t % (2 * L); ph = (q < L ? q : 2 * L - q) / L; back = q < L ? 1 : -1; }
    else ph = (loop.t % L) / L;
    if (P && P.length > 1) {
      const TAIL = 0.45, BB = 6;
      const age = (u) => (loop.boom ? (ph - u) * back : ((ph - u) % 1 + 1) % 1);   // how far behind the head
      octx.save();
      octx.lineCap = 'round'; octx.lineJoin = 'round'; octx.lineWidth = DOT_R * 2;
      for (let band = 0; band < BB; band++) {
        octx.beginPath();
        let open = false;
        for (let i = 1; i < P.length; i++) {
          const g = age(P[i].u), g0 = age(P[i - 1].u);
          const k = 1 - g / TAIL;
          if (g < 0 || g > TAIL || g0 < 0 || Math.abs(g - g0) > 0.5 || Math.min(BB - 1, Math.floor(k * BB)) !== band) { open = false; continue; }
          if (!open) { octx.moveTo(P[i - 1].x, P[i - 1].y); open = true; }
          octx.lineTo(P[i].x, P[i].y);
        }
        octx.strokeStyle = 'rgba(' + col + ',' + (((band + 0.5) / BB) * 0.5).toFixed(3) + ')';
        octx.stroke();
      }
      octx.restore();
      let n = 1;
      while (n < P.length - 1 && P[n].u < ph) n++;
      const a = P[n - 1], b = P[n], f = clamp((ph - a.u) / Math.max(1e-6, b.u - a.u), 0, 1);
      dot(a.x + (b.x - a.x) * f, a.y + (b.y - a.y) * f, DOT_R, col);
    }
  }

  if (G.mode === 'stutter' && stut) {
    octx.beginPath();
    octx.moveTo(G.x, G.sy);
    octx.lineTo(G.x, G.y);
    octx.moveTo(G.x - 5, G.sy); octx.lineTo(G.x + 5, G.sy);
    octx.moveTo(G.x - 5, G.y); octx.lineTo(G.x + 5, G.y);
    octx.stroke();
  }

  if (G.mode === 'freeze' && fz) {
    const k = (fz.t * 0.9) % 1;
    octx.strokeStyle = 'rgba(255,255,255,' + (0.9 * (1 - k)).toFixed(3) + ')';
    octx.beginPath();
    octx.arc(G.x, G.y, 6 + k * 40, 0, TAU);
    octx.stroke();
  }

  for (let i = flashes.length - 1; i >= 0; i--) {
    const f = flashes[i];
    const k = 1 - (t - f.t) / 600;
    if (k <= 0) { flashes.splice(i, 1); continue; }
    octx.strokeStyle = 'rgba(229,55,43,' + k.toFixed(3) + ')';
    octx.lineWidth = 2;
    octx.beginPath();
    octx.moveTo(f.x, 0);
    octx.lineTo(f.x, h);
    octx.stroke();
    octx.lineWidth = 1;
    label('cut', f.x + 6, 16, 'left', k, true);
  }

  drawGrid();
  drawHints(t);
  drawCursor(t);
  if (P2) {
    dot(P2.x, P2.y, DOT_R + 2, P2.role === 'tool' ? rgbOf(P2.tool) : GROUP_RGB.time);
    const txt = P2.role === 'scratch' ? 'scratch' : P2.role === 'tool' && P2.tool.info ? P2.tool.info() : '';
    if (txt) label(txt, clamp(P2.x, 60, S.w - 60), Math.max(EDGE + 9, P2.y - 28), 'center', 0.95);
  }
}

// Quiet direction hints on the edges of the picture, shown while the cursor
// rests over the video (or after a pause on touch screens).
let hintA = 0;
function drawHints(t) {
  const idle = clip && !G.down && !replay && info.hidden && !WH.open &&
    (H.in || (G.touch && t - G.lastUp > 2500));
  const using = G.down && G.mode === 'tool' && tool.id !== 'hand';
  hintA += ((clip && gridMode !== 'none' ? 1 : 0) - hintA) * 0.2;   // edge labels stay up as long as the axes are on

  // just picked a tool: name it in the middle for a moment
  const pf = 1 - (t - playFlash) / 700;
  if (pf > 0) label(playing ? '▶ play' : '❚❚ pause', S.w / 2, S.h / 2, 'center', Math.min(1, pf * 2));
  const fl = 1 - (t - toolFlash) / 1400;
  if (fl > 0 && !G.down) label(tool.name, S.w / 2, S.h / 2, 'center', Math.min(1, fl * 2));

  if (hintA < 0.02 || gridMode === 'none') return;   // the edge labels go with the axes
  // one margin for everything on the picture: labels sit EDGE px from the edge,
  // the same inset as the time and effect tags
  const w = S.w, h = S.h, a = hintA;
  const M = EDGE, top = M + LABEL_H / 2, bot = h - M - LABEL_H / 2;
  // with a grid on, the lines carry direction, so the labels drop their arrows
  const ar = false;   // labels never carry arrows
  const up = (txt) => (ar ? '↑ ' : '') + txt, dn = (txt) => (ar ? '↓ ' : '') + txt;
  const lf = (txt) => (ar ? '← ' : '') + txt, rt = (txt) => txt + (ar ? ' →' : '');
  // the labels the hand is driving take the tool's colour: a tool reads
  // where the hand is on the picture, the scratch hand reads its gesture
  const hc = rgbOf(G.down ? G.tool : tool);
  const lit = { L: 0, R: 0, T: 0, B: 0, fast: 0, stutter: 0, scratch: 0, tl: 0, tr: 0, bl: 0, br: 0 };
  const hx = G.down ? G.x : H.x, hy = G.down ? G.y : H.y;
  if (tool.id !== 'hand' && (H.in || G.down)) {
    const nx = hx / w - 0.5, ny = hy / h - 0.5, k = (v) => clamp((Math.abs(v) - 0.02) / 0.48, 0, 1);   // 0 at the middle, 1 at the edge
    lit[nx < 0 ? 'L' : 'R'] = k(nx);
    lit[ny < 0 ? 'T' : 'B'] = k(ny);
  } else if (G.down) {
    const m = G.mode;
    if (m === 'up') lit.fast = 1;
    else if (m === 'stutter') lit.stutter = 1;
    else if (m === 'scratch') lit.scratch = 1;
    else if (m === 'slit') lit[(G.y < G.oy ? 't' : 'b') + (G.x < G.ox ? 'l' : 'r')] = 1;
  }
  if (tool.id !== 'hand') {
    // the tool's axes, on the edges they belong to
    if (tool.T) label(up(tool.T), w / 2, top, 'center', a, false, hc, lit.T);
    if (tool.B) label(dn(tool.B), w / 2, bot, 'center', a, false, hc, lit.B);
    if (tool.L) label(lf(tool.L), M, h / 2, 'left', a, false, hc, lit.L);
    if (tool.R) label(rt(tool.R), w - M, h / 2, 'right', a, false, hc, lit.R);
    if (tool.hint) label(tool.hint, w / 2, tool.B ? bot - LABEL_H - 6 : bot, 'center', a);
    return;
  }
  label(up('fast'), w / 2, top, 'center', a, false, hc, lit.fast);
  label(dn('stutter'), w / 2, bot, 'center', a, false, hc, lit.stutter);
  label(lf('scratch'), M, h / 2, 'left', a, false, hc, lit.scratch);
  label(rt('scratch'), w - M, h / 2, 'right', a, false, hc, lit.scratch);
  // diagonals: one tag in each corner, on the same margin as everything else
  const qa = a;
  label((ar ? '↖ ' : '') + 'slit', M, top, 'left', qa, false, hc, lit.tl);
  label('slit' + (ar ? ' ↗' : ''), w - M, top, 'right', qa, false, hc, lit.tr);
  label((ar ? '↙ ' : '') + 'slit', M, bot, 'left', qa, false, hc, lit.bl);
  label('slit' + (ar ? ' ↘' : ''), w - M, bot, 'right', qa, false, hc, lit.br);
}

const EDGE = 12;      // margin between anything on the picture and its edge
const LABEL_H = 16;   // height of an on-picture label
// overlay colours follow the background: white tags and lines on white, black on black
const UI = { fill: '#ffffff', ink: '#111111', line: '#ffffff' };
function readUI() {
  const cs = getComputedStyle(document.body);
  UI.fill = cs.getPropertyValue('--cell').trim() || '#fff';
  UI.ink = cs.getPropertyValue('--cell-ink').trim() || '#111';
  UI.line = UI.fill;
  UI.dark = document.body.classList.contains('dark');
}

// Guide lines over the picture: none, the two axes through the middle, or thirds.
let gridMode = 'axes';   // axes and their edge labels, on from the start; the button toggles both
// guide lines stay up for as long as they are switched on; a single hairline
// that inverts what is under it, so it reads on any picture with no outline
function drawGrid() {
  if (gridMode === 'none' || !clip) return;
  const w = S.w, h = S.h;
  const xs = [w / 2], ys = [h / 2];
  octx.save();
  octx.strokeStyle = UI.line;   // the axes take the background colour, like the labels
  octx.lineWidth = 1;
  octx.beginPath();
  for (const x of xs) { octx.moveTo(Math.round(x) + 0.5, 0); octx.lineTo(Math.round(x) + 0.5, h); }
  for (const y of ys) { octx.moveTo(0, Math.round(y) + 0.5); octx.lineTo(w, Math.round(y) + 0.5); }
  octx.stroke();
  octx.restore();
}
function cycleGrid() {
  gridMode = gridMode === 'none' ? 'axes' : 'none';
  btnGrid.classList.toggle('on', gridMode !== 'none');
  hintA = Math.max(hintA, 0.6);
}

// On-video labels are small white tags, readable on any footage.
// Arrows are drawn, not typed, so every direction has the same weight and
// sits at the height of the text beside it.
const ARROW = { '←': Math.PI, '→': 0, '↑': -Math.PI / 2, '↓': Math.PI / 2, '↖': -3 * Math.PI / 4, '↗': -Math.PI / 4, '↙': 3 * Math.PI / 4, '↘': Math.PI / 4 };

function drawArrow(cx, cy, size, ang) {
  const h = size / 2;
  const c = Math.cos(ang), s2 = Math.sin(ang);
  const tx = cx + c * h, ty = cy + s2 * h;           // tip
  const head = size * 0.5, spread = 0.75;
  octx.beginPath();
  octx.moveTo(cx - c * h, cy - s2 * h);
  octx.lineTo(tx, ty);
  octx.moveTo(tx - Math.cos(ang - spread) * head, ty - Math.sin(ang - spread) * head);
  octx.lineTo(tx, ty);
  octx.lineTo(tx - Math.cos(ang + spread) * head, ty - Math.sin(ang + spread) * head);
  octx.stroke();
}

function label(txt, x, y, align, a, red, hl, hk) {
  if (a <= 0.01) return;
  let lead = null, trail = null;
  if (ARROW[txt[0]] !== undefined && txt[1] === ' ') { lead = ARROW[txt[0]]; txt = txt.slice(2); }
  else if (ARROW[txt[txt.length - 1]] !== undefined && txt[txt.length - 2] === ' ') { trail = ARROW[txt[txt.length - 1]]; txt = txt.slice(0, -2); }
  octx.font = '400 10px "JetBrains Mono", ui-monospace, monospace';
  const AW = 8, GAP = 5;                              // arrow box ≈ cap height of 12px mono
  const tw = Math.ceil(octx.measureText(txt).width);
  const w = tw + 10 + (lead !== null || trail !== null ? AW + GAP : 0), h = LABEL_H;
  const lx = Math.round(align === 'left' ? x : align === 'right' ? x - w : x - w / 2);
  const ly = Math.round(y - h / 2);
  let ink = red ? '#fff' : UI.ink;
  let fill = red ? '#e5372b' : UI.fill;
  if (hl && hk > 0 && !red) {
    // driven: the further the hand pushes that way, the more the text takes the
    // tool's colour and the tag a wash of it (no switch, a gradient). On black
    // the colour is lifted toward white so it keeps its contrast.
    const k = clamp(hk, 0, 1), rgb = hl.split(',').map(Number);
    const col = UI.dark ? rgb.map((v) => v + (255 - v) * 0.4) : rgb;
    const inkBase = UI.dark ? [238, 238, 238] : [17, 17, 17], base = UI.dark ? [17, 17, 17] : [255, 255, 255];
    const wash = UI.dark ? 0.3 : 0.2;
    ink = 'rgb(' + inkBase.map((b, i) => Math.round(b + (col[i] - b) * k)).join(',') + ')';
    fill = 'rgb(' + base.map((b, i) => Math.round(b + (rgb[i] - b) * wash * k)).join(',') + ')';
  }   // driven: the text takes the tool's colour
  octx.globalAlpha = a;
  octx.fillStyle = fill;
  octx.fillRect(lx, ly, w, h);
  octx.fillStyle = ink;
  octx.strokeStyle = ink;
  octx.lineWidth = 1.5;
  octx.lineCap = 'square';
  octx.lineJoin = 'miter';
  octx.textAlign = 'left';
  octx.textBaseline = 'middle';
  let tx = lx + 5;
  if (lead !== null) { drawArrow(tx + AW / 2, ly + h / 2, AW, lead); tx += AW + GAP; }
  octx.fillText(txt, tx, ly + h / 2 + 0.5);
  if (trail !== null) drawArrow(tx + tw + GAP + AW / 2, ly + h / 2, AW, trail);
  octx.lineCap = 'round';
  octx.textBaseline = 'alphabetic';
  octx.globalAlpha = 1;
}

// the hand: one accent colour for the dot and its trail
function handColour() { return rgbOf(G.down ? G.tool : tool); }
const DOT_R = 10;
function dot(x, y, r, rgb) {
  octx.fillStyle = 'rgba(' + (rgb || handColour()) + ',.8)';
  octx.beginPath();
  octx.arc(x, y, r, 0, TAU);
  octx.fill();
}

// arcs around the hand (hold, circling, brush size): one flat stroke in the
// hand's own colour, no outline, square ends, like every other line here
function ring(x, y, r, a, from, to, w) {
  octx.lineWidth = w || 2;
  octx.lineCap = 'butt';
  octx.strokeStyle = 'rgba(' + handColour() + ',' + Math.min(1, a).toFixed(3) + ')';
  octx.beginPath(); octx.arc(x, y, r, from, to); octx.stroke();
  octx.lineCap = 'round';
}

// The cursor is a circle. While pressed it teaches the grammar: a compass of
// directions around the press point, a filling arc for hold (freeze) and for
// circling (loop), and the chosen direction stays lit for a moment.
function drawCursor(t) {
  if (!(H.in || G.down)) return;
  const x = G.down ? G.x : H.x, y = G.down ? G.y : H.y;
  const top = -Math.PI / 2;

  if (!G.down) {
    if (WH.open) return;
    dot(x, y, DOT_R);
    return;
  }

  if (G.tool.id !== 'hand') {
    if (G.tool.id === 'brush') {
      const brr = (brushR() * view.dw) / clip.W;
      ring(x, y, brr, 0.8, 0, TAU, 1);
    }
    dot(x, y, DOT_R + 2);
    if (G.mode === 'tool' && G.tool.info) label(G.tool.info(), x, y - 28, 'center', 0.95);
    return;
  }

  const br = (brushR() * view.dw) / clip.W; // brush radius on screen
  if (G.mode === 'brush') {
    ring(x, y, br, 0.8, 0, TAU, 1);
    dot(x, y, 5);
    label('painting ' + fmt(wrapT(G.brush ? G.brush.t : pos)), x, y + br + 14, 'center', 0.85);
    return;
  }

  dot(x, y, DOT_R + 2);

  // compass around where the press started
  const since = t - G.st;
  const R = 58, ox = G.ox, oy = G.oy;
  const base = G.mode === 'pending' ? Math.min(1, since / 120) * 0.85 : 0;
  const after = (m) => {
    if (G.mode === 'pending') return base;
    if (G.lockMode !== m) return Math.max(0, 0.85 - (t - G.lockT) / 250);
    return Math.max(0, 1 - (t - G.lockT) / 900);
  };
  if (replay == null) {
    const sc = after('scratch');
    label('scratch >', ox + R, oy, 'left', sc);
    label('< scratch', ox - R, oy, 'right', sc);
    label('fast', ox, oy - R, 'center', after('up'));
    label('stutter', ox, oy + R, 'center', after('stutter'));
    const sa = after('slit') * 0.75, d = R * 0.78;
    label('slit', ox + d, oy - d, 'left', sa);
    label('slit', ox - d, oy - d, 'right', sa);
    label('slit', ox + d, oy + d, 'left', sa);
    label('slit', ox - d, oy + d, 'right', sa);
  }

  // slit-scan: a line from the press point, "now" at the hand, the past behind
  if (G.mode === 'slit' && slit) {
    label('-' + slit.span.toFixed(2) + 's', ox - slit.ux * 14, oy - slit.uy * 14, 'center', 0.85);
    label('now', x + slit.ux * 22, y + slit.uy * 22, 'center', 0.85);
  }

  // hold → freeze
  if (G.mode === 'pending') {
    const k = clamp((since - 60) / 220, 0, 1);
    if (k > 0) {
      ring(x, y, 17, 0.9, top, top + k * TAU, 2);
      label('hold: freeze', x, y + 28, 'center', Math.min(1, k * 2) * 0.85);
    }
  }
  if (G.mode === 'freeze') {
    ring(x, y, br, 0.45, 0, TAU, 1);
    label('freeze', x, y + 28, 'center', 0.9);
    label('move to paint this moment', x, y + 44, 'center', clamp((t - G.lockT - 500) / 400, 0, 0.75));
  }

  // circling → loop
  if (G.mode !== 'circle' && G.mode !== 'freeze') {
    const k = clamp(Math.abs(G.turn) / (Math.PI * 1.75), 0, 1);
    if (k > 0.3) {
      const dir = G.turn > 0 ? 1 : -1;
      ring(x, y, 17, 0.9, top, top + dir * k * TAU, 2);
      label(G.turn > 0 ? 'keep circling: loop' : 'keep circling: bounce loop', x, y + 28, 'center', 0.9);
    }
  }
  if (G.mode === 'circle') label(loop.boom ? 'bounce loop' : 'loop', x, y + 28, 'center', Math.max(0, 1 - (t - G.lockT) / 900));
  if (shuffle > 0.15) label('shuffle', x, y + 28, 'center', Math.min(1, shuffle));
}

let lastT = now();
function frame() {
  requestAnimationFrame(frame);
  const t = now();
  let dt = (t - lastT) / 1000;
  lastT = t;
  if (dt > 0.1) dt = 0.1;
  if (clip) {
    step(dt, t);
    render();
  }
  wheelTick(dt);
  drawOverlay(t);
  hud();
}

/* ---------------------------------------------------------------- record / replay */

function pickMime() {
  if (!window.MediaRecorder) return null;
  const list = [
    'video/mp4;codecs=avc1.42E01E,mp4a.40.2',
    'video/mp4',
    'video/webm;codecs=vp9,opus',
    'video/webm;codecs=vp8,opus',
    'video/webm',
  ];
  for (const m of list) if (MediaRecorder.isTypeSupported(m)) return m;
  return '';
}

// Hand a finished video to the viewer. Inside claude.ai the page asks through
// the downloads capability (the viewer confirms); anywhere else it is a
// plain browser download.
let lastRec = null;   // { blob, name, secs } the last finished recording

async function saveFile(blob, name) {
  let dl = null;
  try { if (window.claude && window.claude.use) dl = await window.claude.use('downloads'); } catch (e) { dl = null; }
  if (dl) {
    try { await dl.save({ filename: name, data: blob }); toast('saved ' + name); }
    catch (err) {
      if (err && err.code === 'declined') toast('not saved');
      else if (err && err.code === 'rate_limited') toast('a save is already waiting, try again in a moment');
      else toast("couldn't save the video here");
    }
    return;
  }
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = name;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 10000);
}

function startRec() {
  if (!clip) return;
  if (window.VM_TRACE_ONLY) {           // hosts that can't save files: record the trace only
    recState = { mr: null, rc: { width: 1, height: 1 }, rctx: { drawImage() {} }, t0: now() };
    score = { frames: [], lastSerial: -1 };
    btnRec.classList.add('on');
    setLbl(btnRec, 'Stop');
    return;
  }
  const mime = pickMime();
  if (mime === null || !screen.captureStream) { toast('recording is not supported in this browser'); return; }
  wakeAudio();
  const k = Math.max(1, Math.round(1080 / clip.W));
  const rc = document.createElement('canvas');
  rc.width = clip.W * k; rc.height = clip.H * k;
  const rctx = rc.getContext('2d');
  rctx.imageSmoothingEnabled = true;
  rctx.drawImage(screen, 0, 0, rc.width, rc.height);
  const vs = rc.captureStream(30);
  const tracks = [...vs.getVideoTracks()];
  if (A.dest) tracks.push(...A.dest.stream.getAudioTracks());
  let mr;
  try { mr = new MediaRecorder(new MediaStream(tracks), mime ? { mimeType: mime, videoBitsPerSecond: 8e6 } : {}); }
  catch (e) { mr = new MediaRecorder(new MediaStream(tracks)); }
  const chunks = [];
  mr.ondataavailable = (e) => { if (e.data && e.data.size) chunks.push(e.data); };
  mr.onstop = () => {
    const type = mr.mimeType || mime || 'video/webm';
    const blob = new Blob(chunks, { type });
    const ext = type.includes('mp4') ? 'mp4' : 'webm';
    // keep the recording; Download saves it when you ask
    lastRec = { blob, name: 'frame-jockey-' + new Date().toISOString().slice(0, 19).replace(/[:T]/g, '-') + '.' + ext, secs: (now() - t0rec) / 1000 };
    askSave();
    vs.getVideoTracks().forEach((tr) => tr.stop());
  };
  const t0rec = now();
  mr.start(500);
  recState = { mr, rc, rctx, t0: now() };
  score = { frames: [], lastSerial: -1, nextScore: true };
  btnRec.classList.add('on');
  setLbl(btnRec, 'Stop');
}

function stopRec() {
  if (!recState) return;
  try { if (recState.mr) recState.mr.stop(); } catch (e) { /* already stopped */ }
  recState = null;
  btnRec.classList.remove('on');
  setLbl(btnRec, 'Rec');
  if (score && score.frames.length < 10) score = null;
  btnReplay.disabled = !score || !clip;

}

function toggleReplay() {
  if (replay && replay.chip == null) { endPlayback(); return; }
  if (!score || !clip) return;
  wakeAudio();
  seq = null;
  startPlayback(score.frames.slice(), { trail: true });
}

function toggleSeq() {
  if (seq) { seq = null; endPlayback(); return; }
  if (!chips.length) return;
  wakeAudio();
  seq = { i: 0 };
  startPlayback(chips[0].frames, { chip: chips[0].id });
}

// play the sequence once through while recording, then save the video
function exportSeq() {
  if (!chips.length || recState) return;
  startRec();
  if (!recState) return;
  seq = { i: 0, once: true };
  startPlayback(chips[0].frames, { chip: chips[0].id });
}

/* ---------------------------------------------------------------- wiring */

intro.addEventListener('click', () => { wakeAudio(); fileIn.click(); });
const demoBtn = $('#demo');
demoBtn.addEventListener('click', (e) => { e.stopPropagation(); loadDemo(); });
demoBtn.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); e.stopPropagation(); loadDemo(); } });
btnNew.addEventListener('click', () => { wakeAudio(); fileIn.click(); });
btnRec.addEventListener('click', () => (recState ? stopRec() : startRec()));
btnSeq.addEventListener('click', toggleSeq);
// after a recording stops: a small box asks whether to keep it
const recDlg = $('#recdlg');
function askSave() {
  if (!lastRec) return;
  const sv = $('#rd-save'); sv.textContent = 'Download '; const d = document.createElement('span'); d.className = 'dim'; d.textContent = '(' + lastRec.secs.toFixed(1) + 's)'; sv.append(d);
  recDlg.hidden = false;
}
function closeSave() { recDlg.hidden = true; }
$('#rd-save').addEventListener('click', () => { closeSave(); if (lastRec) saveFile(lastRec.blob, lastRec.name); });
$('#rd-drop').addEventListener('click', () => { closeSave(); lastRec = null; toast('recording discarded'); });
recDlg.addEventListener('pointerdown', (e) => e.stopPropagation());
btnReplay.addEventListener('click', toggleReplay);
if (btnWipe.addEventListener) btnWipe.addEventListener('click', wipePaint);

// back to the plain clip: every effect, loop, paint and slit-scan off
function resetAll() {
  if (replay) { seq = null; endPlayback(); }
  fx = {}; liveFx = {};
  loop = null; stut = null; fz = null; speedHold = null;
  if (slit) slit.held = false;
  wipePaint();
  shuffle = 0;
  playing = true;
  stackSig = null;
  toast('reset');
}
btnReset.addEventListener('click', resetAll);
btnGrid.addEventListener('click', cycleGrid);

// white or black around the picture, remembered on this device
const btnBg = $('#btn-bg');
function setDark(on) {
  document.body.classList.toggle('dark', on);
  btnBg.setAttribute('aria-label', on ? 'Switch to a white background' : 'Switch to a black background');
  try { localStorage.setItem('vm-dark', on ? '1' : '0'); } catch (e) { /* storage may be blocked */ }
  readUI();
}
btnBg.addEventListener('click', () => setDark(!document.body.classList.contains('dark')));
try { if (localStorage.getItem('vm-dark') === '1') setDark(true); } catch (e) { /* default white */ }
readUI();
// footer buttons act on click but never keep focus, so space and enter stay with the video
document.querySelectorAll('footer button, #topbar button').forEach((b) => b.addEventListener('mousedown', (e) => e.preventDefault()));

btnTool.addEventListener('click', () => {
  if (WH.open) closeWheel(false);
  else openWheel(S.w / 2, S.h / 2);
});

let muted = false;
function toggleSound() {
  muted = !muted;
  if (A.gain) A.gain.gain.setTargetAtTime(muted ? 0 : 0.9, A.ctx.currentTime, 0.02);
  // black means on, like Axes: a muted Sound button goes white
  btnSound.classList.toggle('on', !muted);
  btnSound.setAttribute('aria-pressed', String(!muted));
}
btnSound.addEventListener('click', () => { wakeAudio(); toggleSound(); });


btnDemo.addEventListener('click', () => loadDemo());
btnFit.addEventListener('click', () => {
  fitMode = btnFit.dataset.fill === '1' ? 'fit' : 'fill';
  layout();
});
// the panel sits between the bars; the Info button becomes its close
function measureBars() {
  const r = document.documentElement.style;
  r.setProperty('--bar-top', $('#topbar').getBoundingClientRect().bottom + 'px');
  r.setProperty('--bar-bot', (window.innerHeight - $('footer').getBoundingClientRect().top) + 'px');
}
const openInfo = () => { measureBars(); info.hidden = false; btnInfo.classList.add('open'); setLbl(btnInfo, 'Close'); $('#info .card').focus(); };   // focus the panel, so esc and scrolling work without lighting up a button
const closeInfo = () => { info.hidden = true; btnInfo.classList.remove('open'); setLbl(btnInfo, 'Info'); };
btnInfo.addEventListener('click', () => (info.hidden ? openInfo() : closeInfo()));
window.addEventListener('resize', () => { if (!info.hidden) measureBars(); });
fileIn.addEventListener('change', () => {
  const f = fileIn.files && fileIn.files[0];
  fileIn.value = '';
  const slot = fileTarget;
  fileTarget = 'A';
  loadFile(f, slot);
});

let dragDepth = 0;
const hasFiles = (e) => e.dataTransfer && [...(e.dataTransfer.types || [])].includes('Files');
window.addEventListener('dragenter', (e) => { if (!hasFiles(e)) return; dragDepth++; document.body.classList.add('dragging'); });
window.addEventListener('dragleave', (e) => { if (!hasFiles(e)) return; if (--dragDepth <= 0) { dragDepth = 0; document.body.classList.remove('dragging'); } });
window.addEventListener('dragover', (e) => { if (hasFiles(e)) e.preventDefault(); });
window.addEventListener('drop', (e) => {
  if (!hasFiles(e)) return;
  e.preventDefault();
  dragDepth = 0;
  document.body.classList.remove('dragging');
  const f = [...e.dataTransfer.files].find((x) => x.type.startsWith('video')) || e.dataTransfer.files[0];
  loadFile(f);
});

window.addEventListener('keydown', (e) => {
  if (e.target && e.target.tagName === 'INPUT') return;
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const k = e.key.toLowerCase();
  if (!info.hidden) { if (k === 'escape' || k === 'i') closeInfo(); return; }
  if (!recDlg.hidden) { if (k === 'escape') $('#rd-drop').click(); return; }
  if (WH.open) {
    if (k === 'arrowdown') settleTo(Math.round(WH.target) + 1, false);
    else if (k === 'arrowup') settleTo(Math.round(WH.target) - 1, false);
    else if (k === 'enter' || k === ' ') closeWheel(true);
    else if (k === 'escape') closeWheel(false);
    e.preventDefault();
    return;
  }
  if (k === 't' && clip) { openWheel(S.w / 2, S.h / 2); return; }
  if (k === 'i' || k === '?') { info.hidden ? openInfo() : closeInfo(); return; }
  if (k === 'o') { fileIn.click(); return; }
  if (k === 'd') { loadDemo(); return; }
  if (k === 'b') { btnBg.click(); return; }
  if (!clip) return;
  wakeAudio();
  if (k === ' ') { e.preventDefault(); playing = !playing; }
  else if (k === 'r') { recState ? stopRec() : startRec(); }
  else if (k === 'p') toggleReplay();
  else if (k === 'w') wipePaint();
  else if (k === 'f') btnFit.click();
  else if (k === 'x') resetAll();
  else if (k === 'm') toggleSound();
  else if (k === 'g') cycleGrid();
  else if (k === 'escape') { loop = null; seq = null; endPlayback(); }
  else if (k === 'backspace' || k === 'delete') { if (chips.length) removeChip(chips[chips.length - 1].id); }
});

// Re-fit whenever the stage changes size: window resizes, panels, phone
// rotation, browser toolbars sliding in and out. Phones report the new size
// late after rotating, so rotation also re-fits once things have settled.
let relayoutRaf = 0;
function relayout() {
  cancelAnimationFrame(relayoutRaf);
  relayoutRaf = requestAnimationFrame(() => {
    if (!clip) return;
    layout();
    if (WH.open) {   // keep the wheel in the middle of the new picture
      WH.x = S.w / 2; WH.y = S.h / 2;
      sizeWheel();
      wheelEl.style.left = WH.x + 'px';
      wheelEl.style.top = WH.y + 'px';
    }
    trail = [];
  });
}
window.addEventListener('resize', relayout);
window.addEventListener('orientationchange', () => { relayout(); setTimeout(relayout, 250); setTimeout(relayout, 600); });
if (window.visualViewport) window.visualViewport.addEventListener('resize', relayout);
if (window.ResizeObserver) new ResizeObserver(relayout).observe(stage);

// expose a tiny hook for automated testing
window.__vm = { pick: (id) => selectTool(TOOL[id]), tools: () => TOOLS.map((t) => t.id), wheel: () => ({ open: WH.open, pos: WH.pos, mode: WH.mode }), get clip() { return clip; }, get state() { return { pos, rate, mode: G.mode, loop, seq, chips: chips.length, persist, shuffle, playing }; } };

requestAnimationFrame(frame);
})();

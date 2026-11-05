import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

/* =========================================================
   RENDERER / SCENE / CAMERA
   (no preserveDrawingBuffer: it forces an extra copy every frame;
    snapshots are taken right after rendering instead)
   ========================================================= */
const BASE_PR = Math.min(window.devicePixelRatio || 1, 1.5);
let curPR = BASE_PR;
const renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: 'high-performance' });
renderer.setPixelRatio(curPR);
renderer.setSize(innerWidth, innerHeight);
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFSoftShadowMap;
renderer.toneMapping = THREE.ACESFilmicToneMapping;
renderer.toneMappingExposure = 1.15;
renderer.autoClear = false;
document.body.appendChild(renderer.domElement);
const canvas = renderer.domElement;

const scene = new THREE.Scene();
scene.background = new THREE.Color(0x87c8ff);
scene.fog = new THREE.Fog(0x87c8ff, 26, 85);

const camera = new THREE.PerspectiveCamera(50, innerWidth / innerHeight, 0.1, 1000);
camera.position.set(9, 4, 9);

const controls = new OrbitControls(camera, canvas);
controls.enableDamping = true;
controls.dampingFactor = 0.08;
controls.autoRotate = true;
controls.autoRotateSpeed = 0.6;
controls.minDistance = 3;
controls.maxDistance = 30;
controls.target.set(0, 1, 0);

/* Lights */
const hemi = new THREE.HemisphereLight(0x87c8ff, 0x55627f, 0.9);
scene.add(hemi);
const sun = new THREE.DirectionalLight(0xffffff, 1.8);
sun.castShadow = true;
sun.shadow.mapSize.set(1024, 1024);
const sc = sun.shadow.camera;
sc.left = -14; sc.right = 14; sc.top = 14; sc.bottom = -14; sc.near = 1; sc.far = 80;
scene.add(sun, sun.target);


/* Stars */
const stars = (() => {
  const n = 1500, pos = new Float32Array(n * 3);
  for (let i = 0; i < n; i++) {
    const u = Math.random() * 2 - 1, th = Math.random() * Math.PI * 2, r = 300;
    const s = Math.sqrt(1 - u * u);
    pos[i*3] = r * s * Math.cos(th); pos[i*3+1] = r * Math.abs(u) * 0.9 + 20; pos[i*3+2] = r * s * Math.sin(th);
  }
  const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.BufferAttribute(pos, 3));
  const m = new THREE.PointsMaterial({ color: 0xffffff, size: 1.4, sizeAttenuation: true, transparent: true, opacity: 0, fog: false, depthWrite: false });
  const p = new THREE.Points(g, m); scene.add(p); return p;
})();

/* =========================================================
   HELPERS
   ========================================================= */
const UP = new THREE.Vector3(0, 1, 0);
const _a = new THREE.Vector3(), _b = new THREE.Vector3(), _dir = new THREE.Vector3();
const _t1 = new THREE.Vector3();
const clamp = THREE.MathUtils.clamp, lerp = THREE.MathUtils.lerp;
const easeInOut = x => x < 0.5 ? 4 * x * x * x : 1 - Math.pow(-2 * x + 2, 3) / 2;
const smooth01 = x => { x = clamp(x, 0, 1); return x * x * (3 - 2 * x); };
const TAU = Math.PI * 2;
function hash3(a, b, c) {                                    // small integer hash -> [0, 1)
  let h = Math.imul(a | 0, 374761393) + Math.imul(b | 0, 668265263) + Math.imul(c | 0, 2246822519);
  h = Math.imul(h ^ (h >>> 13), 1274126177); h ^= h >>> 16;
  return (h >>> 0) / 4294967296;
}
let loopMode = false;                                        // world functions read this: the loop uses a periodic path

/* =========================================================
   DOMINO CITY WORLD — every object is a pure function of time t

   Life of one domino, in seconds relative to the moment the wave reaches it (tau):
     tau < -LSTAND            it is still flying in from the old, fallen track (or rising from the ground at the start)
     -LSTAND .. 0             standing and waiting
     0 .. FALL                toppling forward onto the next one
     FALL .. TLIE             lying flat: this is the "track" the marble has already crossed
     after TLIE               it lifts off, arcs over the marble, and lands as domino k + NDOM far ahead
   The marble hops along the tops of the dominoes and lands on every 4th one just as it begins to fall.
   ========================================================= */
const RHO = 12;                        // dominoes toppled per second
const DS = 0.55;                       // spacing along the path
const VM = RHO * DS;                   // speed of the wave and of the marble, units / s
const DOM_H = 1.0, DOM_W = 0.56, DOM_T = 0.14;
const FALL = 0.30, FALL_A = THREE.MathUtils.degToRad(80);
const LSTAND = 2.0, TFLY = 1.6, TCYC = 5.0, TLIE = TCYC - LSTAND - TFLY;
const NDOM = Math.round(TCYC * RHO);   // 60 dominoes alive at once
const DOM_MAX = NDOM + 6;
const HOP = 4, HOP_T = HOP / RHO, HAPEX = 0.9, R_M = 0.30;
const ARC_H = 5.2;                     // how high the ribbon of re-launched dominoes flies
const SPIN_RATE = TAU * 35 / 10;       // whole number of marble turns per 10 s (matches rolling speed) so the loop is seamless
let simT = -0.9, loopU = 0, loopT = 0; // endless time, loop time (unwrapped / wrapped)

/* ---- the winding path -------------------------------------------------------------------------------------- */
const pathN = { xs: [0], zs: [], fx: [], fz: [] };           // endless path, generated as far as needed, by arc length
const zEnd = x => 4.6 * Math.sin(x / 9.3 + 0.6) + 2.7 * Math.sin(x / 4.1 + 1.9) + 1.1 * Math.sin(x / 2.05 + 0.3);
const dzEnd = x => 4.6 / 9.3 * Math.cos(x / 9.3 + 0.6) + 2.7 / 4.1 * Math.cos(x / 4.1 + 1.9) + 1.1 / 2.05 * Math.cos(x / 2.05 + 0.3);
(function () { pathN.zs[0] = zEnd(0); const sl = dzEnd(0), l = Math.hypot(1, sl); pathN.fx[0] = 1 / l; pathN.fz[0] = sl / l; })();
function extendEndless(n) {
  while (pathN.xs.length <= n) {
    const i = pathN.xs.length, px = pathN.xs[i - 1];
    let dx = DS;
    for (let it = 0; it < 4; it++) { const sl = dzEnd(px + dx / 2); dx = DS / Math.sqrt(1 + sl * sl); }
    const x = px + dx; pathN.xs.push(x); pathN.zs.push(zEnd(x));
    const sl = dzEnd(x), l = Math.hypot(1, sl); pathN.fx.push(1 / l); pathN.fz.push(sl / l);
  }
}

/* Loop path: translation-periodic. 60 dominoes per period; the shape repeats every LP_PX units along x. */
const LP_N = 60, LP_PX = 28;
const LP = { A: 0, xs: new Float64Array(LP_N), zs: new Float64Array(LP_N), fx: new Float64Array(LP_N), fz: new Float64Array(LP_N) };
const zLoop = (x, A) => A * (Math.sin(TAU * x / LP_PX) + 0.35 * Math.sin(2 * TAU * x / LP_PX + 1.1));
const dzLoop = (x, A) => A * (Math.cos(TAU * x / LP_PX) + 0.7 * Math.cos(2 * TAU * x / LP_PX + 1.1)) * TAU / LP_PX;
(function buildLoopTable() {
  const arc = A => { const N = 4000; let s = 0; for (let i = 0; i < N; i++) { const d = dzLoop((i + 0.5) * LP_PX / N, A); s += Math.sqrt(1 + d * d); } return s * LP_PX / N; };
  const target = LP_N * DS; let lo = 0, hi = 9;
  for (let it = 0; it < 60; it++) { const mid = (lo + hi) / 2; if (arc(mid) < target) lo = mid; else hi = mid; }
  LP.A = (lo + hi) / 2;
  const M = 8000, S = new Float64Array(M + 1);
  for (let i = 0; i < M; i++) {
    const xa = i * LP_PX / M, xb = (i + 1) * LP_PX / M, da = dzLoop(xa, LP.A), db = dzLoop(xb, LP.A);
    S[i + 1] = S[i] + (Math.sqrt(1 + da * da) + Math.sqrt(1 + db * db)) * 0.5 * (xb - xa);
  }
  const step = S[M] / LP_N; let j = 0;
  for (let i = 0; i < LP_N; i++) {
    const want = i * step; while (S[j + 1] < want) j++;
    const x = (j + (want - S[j]) / (S[j + 1] - S[j])) * LP_PX / M, sl = dzLoop(x, LP.A), l = Math.hypot(1, sl);
    LP.xs[i] = x; LP.zs[i] = zLoop(x, LP.A); LP.fx[i] = 1 / l; LP.fz[i] = sl / l;
  }
})();

function pathPt(k, o) {                                      // position and heading of domino number k
  if (loopMode) { const n = Math.floor(k / LP_N), r = k - n * LP_N; o.x = LP.xs[r] + n * LP_PX; o.z = LP.zs[r]; o.fx = LP.fx[r]; o.fz = LP.fz[r]; }
  else if (k < 0) { o.x = pathN.xs[0] + k * DS * pathN.fx[0]; o.z = pathN.zs[0] + k * DS * pathN.fz[0]; o.fx = pathN.fx[0]; o.fz = pathN.fz[0]; }
  else { extendEndless(k); o.x = pathN.xs[k]; o.z = pathN.zs[k]; o.fx = pathN.fx[k]; o.fz = pathN.fz[k]; }
  return o;
}
const _pa = { x: 0, z: 0, fx: 1, fz: 0 }, _pb = { x: 0, z: 0, fx: 1, fz: 0 };
function posOnPath(q, o) {                                   // same, at a fractional domino index
  const i = Math.floor(q), f = q - i;
  pathPt(i, _pa); pathPt(i + 1, _pb);
  o.x = _pa.x + (_pb.x - _pa.x) * f; o.z = _pa.z + (_pb.z - _pa.z) * f;
  const fx = _pa.fx + (_pb.fx - _pa.fx) * f, fz = _pa.fz + (_pb.fz - _pa.fz) * f, l = Math.hypot(fx, fz) || 1;
  o.fx = fx / l; o.fz = fz / l; return o;
}

/* ---- ground and city blocks ---------------------------------------------------------------------------------- */
const BC = 7;                                                // city block size (a whole loop is exactly 8 blocks long)
const ground = (() => {
  const c = document.createElement('canvas'); c.width = c.height = 128; const x = c.getContext('2d');
  x.fillStyle = '#3b4252'; x.fillRect(0, 0, 128, 128);
  for (let i = 0; i < 260; i++) { x.fillStyle = `rgba(255,255,255,${Math.random() * 0.035})`; x.fillRect(Math.random() * 128, Math.random() * 128, 2, 2); }
  x.fillStyle = '#4d566a'; x.fillRect(0, 0, 128, 3); x.fillRect(0, 0, 3, 128);
  x.fillStyle = '#2f3644'; x.fillRect(0, 3, 128, 2); x.fillRect(3, 0, 2, 128);
  const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.repeat.set(63, 63); t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = 4;
  const m = new THREE.Mesh(new THREE.PlaneGeometry(441, 441), new THREE.MeshStandardMaterial({ map: t, roughness: 0.95 }));
  m.rotation.x = -Math.PI / 2; m.receiveShadow = true; scene.add(m); return m;
})();

const FLOORS = [5, 9, 15], FLOOR_H = 0.75, ZC = 11.5, BCOLS = 15, BROWS = 5;
const bMats = [], bMeshes = [];
(function makeCity() {
  const mk = (lit) => {
    const c = document.createElement('canvas'); c.width = c.height = 128; const x = c.getContext('2d');
    x.fillStyle = lit ? '#000' : '#dfe4f0'; x.fillRect(0, 0, 128, 128);
    for (let r = 0; r < 4; r++) for (let q = 0; q < 4; q++) {
      const on = hash3(q, r, 5) > 0.38;
      x.fillStyle = lit ? (on ? '#ffd58a' : '#000') : '#26314a';
      x.fillRect(q * 32 + 6, r * 32 + 7, 20, 18);
    }
    const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.colorSpace = THREE.SRGBColorSpace; return t;
  };
  const wall = mk(false), glow = mk(true);
  FLOORS.forEach((f, ci) => {
    const w = wall.clone(), g = glow.clone(); w.needsUpdate = g.needsUpdate = true;
    w.repeat.set(1, f / 4); g.repeat.set(1, f / 4);
    const mat = new THREE.MeshStandardMaterial({ color: 0xffffff, map: w, emissive: 0xffffff, emissiveMap: g, emissiveIntensity: 0, roughness: 0.85 });
    const mesh = new THREE.InstancedMesh(new THREE.BoxGeometry(1, f * FLOOR_H, 1), mat, BCOLS * BROWS * 2);
    mesh.frustumCulled = false; mesh.setColorAt(0, new THREE.Color(1, 1, 1)); scene.add(mesh);
    bMats.push(mat); bMeshes.push(mesh);
  });
})();
const _bm = new THREE.Matrix4(), _bq = new THREE.Quaternion(), _bp = new THREE.Vector3(), _bs = new THREE.Vector3(), _col = new THREE.Color();
function updateCity(camX) {
  const ix0 = Math.floor(camX / BC) - 7, cnt = [0, 0, 0];
  for (let side = 0; side < 2; side++) for (let r = 0; r < BROWS; r++) for (let c = 0; c < BCOLS; c++) {
    const ix = ix0 + c, ixh = loopMode ? ((ix % 8) + 8) % 8 : ix;       // the loop repeats every 8 blocks
    const h1 = hash3(ixh, r, side), h2 = hash3(ixh, r + 17, side + 5), h3 = hash3(ixh, r + 31, side + 9), h4 = hash3(ixh, r + 7, side + 2);
    if (h1 < 0.14) continue;                                              // an occasional open plaza
    const cls = (r >= 3 && h2 > 0.3) || h2 > 0.82 ? 2 : (h2 < 0.42 ? 0 : 1);
    const ci = cnt[cls]++;
    _bp.set((ix + 0.5) * BC + (h3 - 0.5), FLOORS[cls] * FLOOR_H / 2, (side ? 1 : -1) * (ZC + 3.5 + r * BC) + (h1 - 0.5));
    _bs.set(3.2 + h3 * 2.4, 1, 3.2 + h4 * 2.4);
    _bm.compose(_bp, _bq.identity(), _bs); bMeshes[cls].setMatrixAt(ci, _bm);
    _col.setHSL(0.56 + h3 * 0.14, 0.16 + h1 * 0.2, 0.34 + h2 * 0.22); bMeshes[cls].setColorAt(ci, _col);
  }
  for (let i = 0; i < 3; i++) { bMeshes[i].count = cnt[i]; bMeshes[i].instanceMatrix.needsUpdate = true; bMeshes[i].instanceColor.needsUpdate = true; }
  ground.position.set(Math.floor(camX / BC) * BC, 0, 0);
}

/* ---- the dominoes (one InstancedMesh) ------------------------------------------------------------------------- */
const pipTex = (() => {
  const c = document.createElement('canvas'); c.width = 112; c.height = 200; const x = c.getContext('2d');
  x.fillStyle = '#f6f3ec'; x.fillRect(0, 0, 112, 200);
  x.fillStyle = '#cfcabd'; x.fillRect(8, 97, 96, 6);
  x.fillStyle = '#1b2030';
  [[30, 28], [82, 28], [56, 50], [30, 72], [82, 72], [30, 126], [56, 150], [82, 174]].forEach(([px, py]) => { x.beginPath(); x.arc(px, py, 9, 0, TAU); x.fill(); });
  const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = 4; return t;
})();
const domEdge = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.45 });
const domFace = new THREE.MeshStandardMaterial({ color: 0xffffff, roughness: 0.35, map: pipTex });
const domMesh = new THREE.InstancedMesh(new THREE.BoxGeometry(DOM_W, DOM_H, DOM_T), [domEdge, domEdge, domEdge, domEdge, domFace, domFace], DOM_MAX);
domMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
domMesh.castShadow = true; domMesh.receiveShadow = true; domMesh.frustumCulled = false;
domMesh.setColorAt(0, new THREE.Color(1, 1, 1)); scene.add(domMesh);

const _m4 = new THREE.Matrix4(), _dP = { x: 0, z: 0, fx: 1, fz: 0 }, _dO = { x: 0, z: 0, fx: 1, fz: 0 }, _dF = { x: 0, z: 0, fx: 1, fz: 0 };
const domHue = k => loopMode ? (((k % LP_N) + LP_N) % LP_N) / LP_N : (((k * 0.0042) % 1) + 1) % 1;
const SIN_A = Math.sin(FALL_A), COS_A = Math.cos(FALL_A);
const LY_CU = DOM_T / 2 * SIN_A + DOM_H / 2 * COS_A, LY_CF = -DOM_T / 2 * COS_A + DOM_H / 2 * SIN_A;   // centre of a lying domino
function writeDomino(idx, F, th, cx, cy, cz) {
  const c = Math.cos(th), s = Math.sin(th);                   // tilt about the lateral axis; columns = lateral, tilted-up, tilted-forward
  _m4.set(F.fz, F.fx * s, F.fx * c, cx,
          0,    c,        -s,       cy,
          -F.fx, F.fz * s, F.fz * c, cz,
          0, 0, 0, 1);
  domMesh.setMatrixAt(idx, _m4);
}
function setDomino(idx, k, t) {
  const tau = t - k / RHO;
  pathPt(k, _dP);
  let F = _dP, th = 0, cx = _dP.x, cy = DOM_H / 2, cz = _dP.z, lit = 0, dim = 0;
  if (tau < -LSTAND) {
    const e = smooth01((tau + LSTAND + TFLY) / TFLY);
    if (!loopMode && k - NDOM < 0) { cy = DOM_H / 2 - (1 - e) * (DOM_H + 0.15); }                 // very first ones simply rise from the ground
    else {                                                                                       // a fallen domino from the old track, flying over the marble
      posOnPath((k - NDOM) + NDOM * e, _dF); F = _dF;
      th = FALL_A * (1 - e) - TAU * e;
      const off = LY_CF * (1 - e);
      cx = _dF.x + _dF.fx * off; cz = _dF.z + _dF.fz * off;
      cy = lerp(LY_CU, DOM_H / 2, e) + ARC_H * Math.sin(Math.PI * e);
    }
  } else if (tau < 0) {
    lit = tau < -LSTAND + 0.4 ? 1 - (tau + LSTAND) / 0.4 : 0;                                    // little flash as it lands
  } else {
    let u = tau / FALL;
    if (u < 1) th = FALL_A * Math.pow(u, 1.25);
    else { const w = tau - FALL; th = FALL_A - 0.06 * Math.exp(-w * 13) * Math.sin(w * 32); dim = smooth01(w / 1.0); }
    const c = Math.cos(th), s = Math.sin(th), cf = -DOM_T / 2 * c + DOM_H / 2 * s;
    cx = _dP.x + _dP.fx * cf; cz = _dP.z + _dP.fz * cf; cy = DOM_T / 2 * s + DOM_H / 2 * c;
  }
  writeDomino(idx, F, th, cx, cy, cz);
  _col.setHSL(domHue(k), 0.8, 0.55 - dim * 0.2 + lit * 0.28); domMesh.setColorAt(idx, _col);
}

/* ---- the marble ----------------------------------------------------------------------------------------------- */
const marbleTex = (() => {
  const c = document.createElement('canvas'); c.width = 256; c.height = 128; const x = c.getContext('2d');
  x.fillStyle = '#f2f6ff'; x.fillRect(0, 0, 256, 128);
  const cols = ['#2f6df6', '#ff5a4f', '#ffc83d', '#2fc7a4'];
  for (let i = 0; i < 4; i++) {
    x.strokeStyle = cols[i]; x.lineWidth = 15; x.lineCap = 'round'; x.beginPath();
    for (let q = 0; q <= 256; q += 8) { const yy = 20 + i * 28 + Math.sin(q / 256 * TAU * 2 + i * 1.3) * 14; q ? x.lineTo(q, yy) : x.moveTo(q, yy); }
    x.stroke();
  }
  const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.wrapS = THREE.RepeatWrapping; return t;
})();
const marbleG = new THREE.Group();                           // yaw + squash (squash stays vertical in the world)
const marble = new THREE.Mesh(new THREE.SphereGeometry(R_M, 40, 28), new THREE.MeshStandardMaterial({ map: marbleTex, roughness: 0.12, metalness: 0.12 }));
marble.castShadow = true; marbleG.add(marble); scene.add(marbleG);
const marbleLight = new THREE.PointLight(0xffc680, 1.6, 12); scene.add(marbleLight);
const _mp = { x: 0, z: 0, fx: 1, fz: 0 }, _mp2 = { x: 0, z: 0, fx: 1, fz: 0 };
const _mbasis = new THREE.Matrix4(), _mr = new THREE.Vector3(), _mf = new THREE.Vector3(), _mspin = new THREE.Quaternion(), X_AXIS = new THREE.Vector3(1, 0, 0);
function updateMarble(t) {
  let q, y, sy = 1, base = 1;
  if (t < 0) { q = 0; y = 0.5 * 40 * t * t; sy = 1 + Math.min(40 * -t * 0.012, 0.18); }          // intro: it drops onto the first domino
  else {
    const j = Math.floor(t / HOP_T), u = t - j * HOP_T, x = u / HOP_T;
    q = HOP * (j + x); y = 4 * HAPEX * x * (1 - x);
    const vy = 4 * HAPEX * (1 - 2 * x) / HOP_T;
    const sq = u < 0.07 ? 1 - 0.30 * Math.sin(Math.PI * u / 0.07) : 1;                        // squash as it lands on a domino
    sy = sq * (u < 0.07 ? 1 : 1 + Math.min(Math.abs(vy) * 0.012, 0.18));
  }
  posOnPath(q, _mp);
  marbleG.position.set(_mp.x, base + y + R_M * sy, _mp.z);
  const sxz = 1 / Math.sqrt(sy); marbleG.scale.set(sxz, sy, sxz);
  _mbasis.makeBasis(_mr.set(_mp.fz, 0, -_mp.fx), UP, _mf.set(_mp.fx, 0, _mp.fz));
  marbleG.quaternion.setFromRotationMatrix(_mbasis);
  marble.quaternion.copy(_mspin.setFromAxisAngle(X_AXIS, SPIN_RATE * t));
}

/* ---- sparks at every landing, dust motes ---------------------------------------------------------------------- */
let _seed = 20261105;
const rnd = () => (_seed = (_seed * 1664525 + 1013904223) % 4294967296) / 4294967296;
const LS = 16, SPARKS = 64;
const spPos = new Float32Array(SPARKS * 3).fill(-9999), spCol = new Float32Array(SPARKS * 3);
const spGeo = new THREE.BufferGeometry();
spGeo.setAttribute('position', new THREE.BufferAttribute(spPos, 3));
spGeo.setAttribute('color', new THREE.BufferAttribute(spCol, 3));
const sparks = new THREE.Points(spGeo, new THREE.PointsMaterial({ size: 0.13, vertexColors: true, transparent: true, blending: THREE.AdditiveBlending, depthWrite: false }));
sparks.frustumCulled = false; scene.add(sparks);
const sparkColors = [new THREE.Color(0xffe08a), new THREE.Color(0x9fe7ff), new THREE.Color(0xffffff)];
const lsA = [], lsS = [], lsV = [], lsL = [], lsC = [];
for (let i = 0; i < LS; i++) { lsA.push(rnd() * TAU); lsS.push(0.8 + rnd() * 2.2); lsV.push(1.5 + rnd() * 2.8); lsL.push(0.6 + rnd() * 0.4); lsC.push(sparkColors[(rnd() * 3) | 0]); }
const _sp = { x: 0, z: 0, fx: 1, fz: 0 };
function updateSparksAt(t) {
  const j0 = Math.floor(t / HOP_T);
  for (let bi = 0; bi < 3; bi++) {
    const jj = j0 - bi, tau = t - jj * HOP_T, valid = loopMode || jj >= 0;
    posOnPath(HOP * jj, _sp);
    for (let i = 0; i < LS; i++) {
      const idx = (bi * LS + i) * 3, life = lsL[i];
      if (!valid || tau >= life) { spPos[idx + 1] = -9999; spCol[idx] = spCol[idx + 1] = spCol[idx + 2] = 0; continue; }
      spPos[idx] = _sp.x + Math.cos(lsA[i]) * lsS[i] * tau;
      spPos[idx + 1] = 1.02 + lsV[i] * tau - 3 * tau * tau;
      spPos[idx + 2] = _sp.z + Math.sin(lsA[i]) * lsS[i] * tau;
      const f = Math.min((life - tau) / 0.5, 1), c = lsC[i];
      spCol[idx] = c.r * f; spCol[idx + 1] = c.g * f; spCol[idx + 2] = c.b * f;
    }
  }
  spGeo.attributes.position.needsUpdate = true; spGeo.attributes.color.needsUpdate = true;
}
const LM = 50, MT = 6, LXM = 14, POLLEN = LM * MT;           // dust lattice: repeats every 14 units along x (4 of them per loop)
const poPos = new Float32Array(POLLEN * 3);
const mx = [], mz = [], my = [], mph = [];
for (let i = 0; i < LM; i++) { mx.push(rnd() * LXM); mz.push((rnd() - 0.5) * 34); my.push(0.3 + rnd() * 8.5); mph.push(rnd()); }
const poGeo = new THREE.BufferGeometry(); poGeo.setAttribute('position', new THREE.BufferAttribute(poPos, 3));
const pollen = new THREE.Points(poGeo, new THREE.PointsMaterial({ size: 0.08, color: 0xfff1b0, transparent: true, opacity: 0.75, blending: THREE.AdditiveBlending, depthWrite: false }));
pollen.frustumCulled = false; scene.add(pollen);
function updateMotes(camX, t) {
  const base = Math.floor((camX - 42) / LXM), u = t / 10;
  for (let tile = 0; tile < MT; tile++) for (let i = 0; i < LM; i++) {
    const n = (tile * LM + i) * 3, a = TAU * (2 * u + mph[i]);
    poPos[n] = (base + tile) * LXM + mx[i] + 0.3 * Math.sin(a);
    poPos[n + 1] = my[i] + 0.25 * Math.cos(a);
    poPos[n + 2] = mz[i] + 0.3 * Math.cos(a + 1.7);
  }
  poGeo.attributes.position.needsUpdate = true;
}

/* ---- one frame of the world at time t -------------------------------------------------------------------------- */
const followGoal = new THREE.Vector3(), fwdVec = new THREE.Vector3(1, 0, 0), aheadPt = new THREE.Vector3();
let bGlow = 0;
function worldFrame(t) {
  const kmin = Math.max(loopMode ? -1e9 : 0, Math.ceil((t - TLIE) * RHO)), kmax = Math.floor((t + LSTAND + TFLY) * RHO);
  let n = 0;
  for (let k = kmin; k <= kmax && n < DOM_MAX; k++) setDomino(n++, k, t);
  domMesh.count = n; domMesh.instanceMatrix.needsUpdate = true; domMesh.instanceColor.needsUpdate = true;
  updateMarble(t);
  const q = Math.max(t, 0) * RHO;
  posOnPath(q, _mp); followGoal.set(_mp.x, 0.9, _mp.z); fwdVec.set(_mp.fx, 0, _mp.fz);   // smooth point the camera follows
  posOnPath(q + 26, _mp2); aheadPt.set(_mp2.x, 0.6, _mp2.z);
  updateSparksAt(t); updateMotes(followGoal.x, t); updateCity(followGoal.x);
  marbleLight.position.copy(marbleG.position); marbleLight.position.y += 0.5;
  for (const m of bMats) m.emissiveIntensity = 0.1 + bGlow * 1.7;
  sun.position.copy(marbleG.position).add(_t1.set(10, 20, 8));
  sun.target.position.copy(marbleG.position);
}

/* =========================================================
   SKY CYCLE (repeats every 320 m of height → truly endless)
   ========================================================= */
const SKY = [[0, 0x87c8ff], [0.32, 0x87c8ff], [0.45, 0xffa96b], [0.55, 0x7a5a9a], [0.65, 0x2a3f7a], [0.86, 0x2a3f7a], [0.93, 0xff9fb0], [1.0, 0x87c8ff]]
  .map(([p, c]) => [p, new THREE.Color(c)]);
const NIGHT = [[0, 0], [0.5, 0], [0.62, 1], [0.88, 1], [0.95, 0], [1, 0]];
const skyCol = new THREE.Color(), white = new THREE.Color(0xffffff);
function keyLerp(keys, p) {
  for (let i = 0; i < keys.length - 1; i++) if (p >= keys[i][0] && p <= keys[i+1][0]) return [i, (p - keys[i][0]) / (keys[i+1][0] - keys[i][0])];
  return [keys.length - 2, 1];
}
let nightness = 0;
function updateSky(h) {
  const p = ((h % 320) + 320) % 320 / 320;
  const [i, f] = keyLerp(SKY, p);
  skyCol.copy(SKY[i][1]).lerp(SKY[i+1][1], f);
  const [j, g] = keyLerp(NIGHT, p);
  nightness = lerp(NIGHT[j][1], NIGHT[j+1][1], g);
  scene.background.copy(skyCol); scene.fog.color.copy(skyCol);
  hemi.color.copy(skyCol); hemi.intensity = lerp(0.9, 0.85, nightness);
  sun.color.copy(white).lerp(skyCol, 0.45);
  sun.intensity = lerp(1.8, 1.0, nightness);
  stars.material.opacity = nightness;
}

/* =========================================================
   OVERLAY: vignette + fade (drawn INTO the canvas → recorded)
   The recorded frame itself is exactly 9:16 or 16:9, edge to edge.
   Only rendered when something is actually visible.
   ========================================================= */
const overlay = new THREE.Scene();
const orthoCam = new THREE.OrthographicCamera(-1, 1, 1, -1, 0, 1);
const vignetteTex = (() => {
  const c = document.createElement('canvas'); c.width = c.height = 256;
  const x = c.getContext('2d');
  const g = x.createRadialGradient(128, 128, 60, 128, 128, 182);
  g.addColorStop(0, 'rgba(0,0,0,0)'); g.addColorStop(1, 'rgba(0,0,0,0.6)');
  x.fillStyle = g; x.fillRect(0, 0, 256, 256);
  return new THREE.CanvasTexture(c);
})();
const vignette = new THREE.Mesh(new THREE.PlaneGeometry(2, 2), new THREE.MeshBasicMaterial({ map: vignetteTex, transparent: true, opacity: 0, depthTest: false, depthWrite: false }));
const fadeQuad = new THREE.Mesh(new THREE.PlaneGeometry(2, 2), new THREE.MeshBasicMaterial({ color: 0x000000, transparent: true, opacity: 0, depthTest: false, depthWrite: false }));
overlay.add(vignette, fadeQuad);
let vigAmt = 0, fade = 0, fadeTarget = 0;
function updateOverlay(dt) {
  const want = proChk.checked ? 1 : 0;
  vigAmt += (want - vigAmt) * (1 - Math.exp(-dt * 4));
  vignette.material.opacity = vigAmt; vignette.visible = vigAmt > 0.01;
  const fs = 1.3 * dt;
  fade = fade < fadeTarget ? Math.min(fadeTarget, fade + fs) : Math.max(fadeTarget, fade - fs);
  fadeQuad.material.opacity = fade; fadeQuad.visible = fade > 0.001;
  return vignette.visible || fadeQuad.visible;
}

/* =========================================================
   AUTO PROFESSIONAL CAMERA DIRECTOR
   - aspect-aware framing (portrait gets pulled back so the action stays in frame)
   - intro: wide establishing shot, then a close tracking shot
   - outro: smooth crane-up during the last seconds of a timed recording
   ========================================================= */
const DUR = { establishing: [5, 7], tracking: [4, 6], lowHero: [3.5, 5], orbit: [5, 7], dollyIn: [4, 5.5], craneUp: [4.5, 6], topDown: [3.5, 5], reveal: [4.5, 6], side: [4, 5.5] };
const POOL = ['tracking', 'tracking', 'lowHero', 'lowHero', 'orbit', 'dollyIn', 'craneUp', 'topDown', 'reveal', 'establishing', 'side'];
const NAMES = { establishing: 'Wide establishing', tracking: 'Close tracking', lowHero: 'Ground-level hero', orbit: 'Orbit sweep', dollyIn: 'Dolly-in', craneUp: 'Crane up', topDown: 'Top-down', reveal: 'Look-ahead reveal', side: 'Side tracking' };
const director = {
  type: null, last: null, t: 0, dur: 5, angle: 0, side: 1, cut: true, snap: false, outro: false, queue: [],
  camPos: new THREE.Vector3(), look: new THREE.Vector3(), fov: 50,
  P: new THREE.Vector3(), L: new THREE.Vector3(), C: new THREE.Vector3(), d: new THREE.Vector3(), T: new THREE.Vector3(),
  start() {
    this.camPos.copy(camera.position); this.look.copy(controls.target); this.fov = camera.fov;
    this.outro = false; this.queue = [];
    this.next('establishing');
  },
  next(force, opt = {}) {
    const pick = () => POOL[(Math.random() * POOL.length) | 0];
    let ty = force;
    if (!ty && this.queue.length) ty = this.queue.shift();
    if (!ty) { ty = pick(); while (ty === this.last) ty = pick(); }
    this.type = ty; this.last = ty; this.t = 0;
    const [a, b] = DUR[ty]; this.dur = opt.dur || (a + Math.random() * (b - a));
    this.angle = Math.random() * Math.PI * 2;
    this.side = Math.random() < 0.5 ? -1 : 1;
    this.cut = opt.cut !== undefined ? opt.cut : (force ? true : Math.random() < 0.6);   // mix of hard cuts and smooth glides
    this.snap = this.cut;
  },
  rot(v, a) { const c = Math.cos(a), s = Math.sin(a); return this.d.set(c * v.x - s * v.z, 0, s * v.x + c * v.z); },
  update(dt, B, ahead, advance) {
    if (advance) { this.t += dt; if (this.t > this.dur && !this.outro) this.next(); }
    const s = clamp(this.t / this.dur, 0, 1), e = easeInOut(s);
    const C = this.C.copy(B);
    const hd = _dir.set(-fwdVec.x, 0, -fwdVec.z);                    // "behind the marble" direction
    if (hd.lengthSq() < 1e-4) hd.set(-1, 0, 0); hd.normalize();
    const fit = camera.aspect < 1 ? Math.pow(1 / camera.aspect, 0.5) : 1;
    const P = this.P, L = this.L; let fov = 50, a, r, d;
    switch (this.type) {
      case 'establishing': a = this.angle + s * 0.35 * this.side;
        P.set(C.x + Math.cos(a) * 15 * fit, 6 + s * 2, C.z + Math.sin(a) * 15 * fit); L.copy(C).addScaledVector(fwdVec, 4); L.y = 0.8; fov = 40; break;
      case 'tracking': d = this.rot(hd, this.side * (0.6 + s * 0.3));
        P.copy(C).addScaledVector(d, 4.4 * fit); P.y = 1.7; L.copy(C).addScaledVector(fwdVec, 1.6); L.y = 0.7; fov = 52; break;
      case 'lowHero': d = this.rot(hd, this.side * 0.55);
        P.copy(C).addScaledVector(d, 3.6 * fit); P.y = 0.3; L.copy(C).addScaledVector(fwdVec, 1.2); L.y = 1.1; fov = 64; break;
      case 'orbit': a = this.angle + e * 2.4 * this.side;
        P.set(C.x + Math.cos(a) * 6.5 * fit, 2.1, C.z + Math.sin(a) * 6.5 * fit); L.copy(C); L.y = 0.7; fov = 46; break;
      case 'dollyIn': r = lerp(13, 4.4, e) * fit; d = this.rot(hd, this.side * 0.9);
        P.copy(C).addScaledVector(d, r); P.y = lerp(4, 1.3, e); L.copy(C); L.y = 0.7; fov = 40; break;
      case 'craneUp': a = this.angle;
        P.set(C.x + Math.cos(a) * 7.5 * fit, 0.7 + e * 9, C.z + Math.sin(a) * 7.5 * fit); L.copy(C); L.y = 0.5; fov = 46; break;
      case 'topDown': a = this.angle + s * 0.6;
        P.set(C.x + Math.cos(a) * 1.8, 10 - e * 2.5, C.z + Math.sin(a) * 1.8); L.copy(C).addScaledVector(fwdVec, 2.5); L.y = 0; fov = 55; break;
      case 'reveal': d = this.rot(hd, this.side * 1.1);
        P.copy(C).addScaledVector(d, 7 * fit); P.y = 1.2 + e * 1.4;
        this.T.copy(ahead); L.copy(C).lerp(this.T, e * 0.8); L.y = 0.7; fov = 44; break;
      case 'side': d = this.d.set(fwdVec.z, 0, -fwdVec.x).multiplyScalar(this.side);
        P.copy(C).addScaledVector(d, 4.8 * fit).addScaledVector(fwdVec, -1.0 + s * 2.0); P.y = 1.3; L.copy(C).addScaledVector(fwdVec, 0.8); L.y = 0.6; fov = 50; break;
    }
    if (this.snap) { this.camPos.copy(P); this.look.copy(L); this.fov = fov; this.snap = false; }
    else {
      const k = this.cut ? 6 : lerp(1.2, 6, clamp(this.t / 1.8, 0, 1));
      const al = 1 - Math.exp(-k * dt);
      this.camPos.lerp(P, al); this.look.lerp(L, al); this.fov += (fov - this.fov) * al;
    }
    const T = performance.now() / 1000;
    const amp = (this.type === 'tracking' || this.type === 'lowHero' || this.type === 'side') ? 0.05 : 0.02;  // subtle handheld feel
    camera.position.copy(this.camPos);
    camera.position.x += (Math.sin(T * 1.7) * 0.6 + Math.sin(T * 3.1) * 0.4) * amp;
    camera.position.y += (Math.sin(T * 1.3 + 1) * 0.6 + Math.sin(T * 2.7) * 0.4) * amp;
    if (camera.position.y < 0.15) camera.position.y = 0.15;
    camera.lookAt(this.look);
    if (Math.abs(camera.fov - this.fov) > 0.01) { camera.fov = this.fov; camera.updateProjectionMatrix(); }
  }
};

/* =========================================================
   AUDIO – soft domino clicks + a little "twik" where the marble lands (no melody, no beat)

   SYNC MODEL
   Every contact time is known in advance (domino k is hit at exactly k / RHO seconds), so each
   click is scheduled slightly ahead on the audio clock instead of being fired when a frame is drawn:
     speakers : contact time + display lag - device output latency + user offset
     recording: contact time + user offset   (the recorder taps the audio before the speakers)
   ========================================================= */
let actx = null, master, recMix, sfxBus, recSfxBus, windGain, windFilter, recDest, noiseBuf;
let muted = false, volume = 0.7;
const LOOKAHEAD = 0.7;          // seconds before a contact at which its sound is scheduled
const DISPLAY_LAG = 0.025;      // ~1.5 frames between simulating a frame and seeing it
let syncMs = 0;                 // user offset: negative = earlier, positive = later
try { const v = parseInt(localStorage.getItem('dominoCity.syncMs'), 10); if (!isNaN(v)) syncMs = clamp(v, -200, 300); } catch (e) {}
let pendingVoices = [];
let soundK = 0;                 // next domino whose click has not been scheduled yet

function initAudio() {
  if (actx) { actx.resume(); return; }
  const AC = window.AudioContext || window.webkitAudioContext;
  try { actx = new AC({ latencyHint: 'interactive' }); } catch (e) { actx = new AC(); }
  master = actx.createGain(); master.gain.value = muted ? 0 : volume;
  master.connect(actx.destination);
  recMix = actx.createGain(); recMix.gain.value = master.gain.value;
  recDest = actx.createMediaStreamDestination();
  recMix.connect(recDest);
  sfxBus = actx.createGain(); sfxBus.connect(master);
  recSfxBus = actx.createGain(); recSfxBus.connect(recMix);

  noiseBuf = actx.createBuffer(1, actx.sampleRate * 2, actx.sampleRate);
  const d = noiseBuf.getChannelData(0);
  for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;

  // Soft, steady city hum
  const src = actx.createBufferSource(); src.buffer = noiseBuf; src.loop = true;
  windFilter = actx.createBiquadFilter(); windFilter.type = 'bandpass'; windFilter.frequency.value = 500; windFilter.Q.value = 0.6;
  const lp = actx.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 1200;
  windGain = actx.createGain(); windGain.gain.value = 0;
  src.connect(windFilter); windFilter.connect(lp); lp.connect(windGain);
  windGain.connect(master); windGain.connect(recMix);
  src.start();
  updateLatencyHint();
}
function deviceLatency() {
  if (!actx) return 0;
  return clamp((actx.outputLatency || 0) + (actx.baseLatency || 0), 0, 0.35);
}
/* The marble's landing: a tiny upward chirp + a little click ("twik"). */
function playTwikAt(t, vol, bus, ctx = actx, nbuf = noiseBuf, fMul = null, nOff = null) {
  const vg = ctx.createGain(); vg.connect(bus);
  const f = 2300 * (fMul !== null ? fMul : 1 + (Math.random() - 0.5) * 0.05);
  const o = ctx.createOscillator(); o.type = 'sine';
  o.frequency.setValueAtTime(f * 0.62, t);
  o.frequency.exponentialRampToValueAtTime(f * 1.18, t + 0.028);
  o.frequency.exponentialRampToValueAtTime(f * 1.05, t + 0.07);
  const g = ctx.createGain();
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(vol, t + 0.004);
  g.gain.exponentialRampToValueAtTime(0.0001, t + 0.085);
  o.connect(g); g.connect(vg); o.start(t); o.stop(t + 0.1);

  const n = ctx.createBufferSource(); n.buffer = nbuf;
  const hp = ctx.createBiquadFilter(); hp.type = 'highpass'; hp.frequency.value = 4000;
  const ng = ctx.createGain();
  ng.gain.setValueAtTime(vol * 0.5, t); ng.gain.exponentialRampToValueAtTime(0.0001, t + 0.018);
  n.connect(hp); hp.connect(ng); ng.connect(vg);
  n.start(t, nOff !== null ? nOff : Math.random() * 1.5, 0.03);
  if (ctx === actx) pendingVoices.push({ vg, end: t + 0.15 });
}
/* One domino being hit: a short woody "tk" (band-passed noise + a tiny body tone). Pitch varies a little per domino,
   but always the same for the same domino number, so the loop sounds identical every time round. */
function playClackAt(t, k, bus, ctx = actx, nbuf = noiseBuf) {
  const kk = ((k % LP_N) + LP_N) % LP_N, h = hash3(kk, 7, 3), big = (k % HOP === 0), v = big ? 0.11 : 0.055;
  const vg = ctx.createGain(); vg.connect(bus);
  const n = ctx.createBufferSource(); n.buffer = nbuf;
  const bp = ctx.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = 1700 + h * 1500; bp.Q.value = 2.2;
  const ng = ctx.createGain();
  ng.gain.setValueAtTime(v, t); ng.gain.exponentialRampToValueAtTime(0.0001, t + 0.035);
  n.connect(bp); bp.connect(ng); ng.connect(vg); n.start(t, (h * 1.7) % 1.6, 0.05);
  const o = ctx.createOscillator(); o.type = 'triangle';
  o.frequency.setValueAtTime(320 + h * 120, t); o.frequency.exponentialRampToValueAtTime(140, t + 0.03);
  const og = ctx.createGain();
  og.gain.setValueAtTime(v * 0.7, t); og.gain.exponentialRampToValueAtTime(0.0001, t + 0.04);
  o.connect(og); og.connect(vg); o.start(t); o.stop(t + 0.06);
  if (ctx === actx) pendingVoices.push({ vg, end: t + 0.1 });
  if (big) playTwikAt(t, 0.10, bus, ctx, nbuf, 1 + (hash3(kk, 11, 4) - 0.5) * 0.05, (kk * 0.37) % 1.5);
}
/* delaySec = real seconds from now until domino k is hit on screen. */
function scheduleClack(delaySec, k) {
  if (!actx || actx.state !== 'running') return;    // a suspended context would queue sounds and burst them out on resume
  const now = actx.currentTime;
  pendingVoices = pendingVoices.filter(v => v.end > now);
  const off = syncMs / 1000;
  const tLive = Math.max(now + 0.002, now + delaySec + DISPLAY_LAG + off - deviceLatency());
  playClackAt(tLive, k, sfxBus);
  if (recording && recSoundChk.checked) {
    const tRec = Math.max(now + 0.002, now + delaySec + off);
    playClackAt(tRec, k, recSfxBus);
  }
}
function cancelTwiks() {
  for (const v of pendingVoices) { try { v.vg.disconnect(); } catch (e) {} }
  pendingVoices = [];
}
/* Forget what was scheduled and start again from the current moment (pause, speed change, sync change, restart...). */
function resetSounds() {
  cancelTwiks();
  soundK = loopMode ? Math.ceil(loopU * RHO) : Math.max(0, Math.ceil(simT * RHO));
}
/* Called once per frame: schedule every click that falls inside the look-ahead window. */
function scheduleSoundsLive(tU, spd) {
  if (!actx || actx.state !== 'running' || paused) return;
  const horizon = tU + LOOKAHEAD * spd;
  for (let guard = 0; soundK / RHO <= horizon && guard < 40; guard++) {
    const k = soundK++, delay = (k / RHO - tU) / spd;
    if (delay >= -0.02) scheduleClack(Math.max(0, delay), k);
  }
}
function applyVolume() {
  if (!master) return;
  const v = muted ? 0 : volume;
  master.gain.setTargetAtTime(v, actx.currentTime, 0.03);
  recMix.gain.setTargetAtTime(v, actx.currentTime, 0.03);
}
let windT = 0;
function updateWind(h, dt) {
  if (!actx) return;
  windT += dt; if (windT < 0.1) return;             // 10 Hz is plenty; per-frame automation events add up
  windT = 0;
  const T = actx.currentTime;
  // Loop mode: steady hum, no slow drifting, so the audio has nothing that could reveal the seam
  const base = windChk.checked && !paused ? (loopMode ? 0.06 : 0.04 + Math.min(h / 600, 1) * 0.05) : 0;
  const mod = loopMode ? 1 : 0.7 + 0.2 * Math.sin(T * 0.31) + 0.1 * Math.sin(T * 0.77 + 2);
  windGain.gain.setTargetAtTime(base * mod, T, 0.4);
  windFilter.frequency.setTargetAtTime(loopMode ? 450 : 420 + 180 * Math.sin(T * 0.23), T, 0.5);
}

/* =========================================================
   SEAMLESS LOOP
   The world above is already a pure function of time, so a seamless loop only needs three things:
     1. the path is translation-periodic (60 dominoes per period; 120 dominoes = exactly 10 s = 2 periods),
     2. every look (colour, pips, city blocks, dust) repeats with the same period, and
     3. the camera is a periodic function of the loop time too.
   At t = 10 s everything is the picture at t = 0, shifted along x by exactly 2 periods.
   ========================================================= */
const LOOP_T = 10;                                           // seconds per cycle (120 dominoes, 30 marble hops)
const LOOP_PHASE = 0.2;                                      // recordings start 0.2 s into the cycle so no landing sits on the seam
const LOOP_FOG_NEAR = 22, LOOP_FOG_FAR = 80;
const LOOP_SKY = new THREE.Color(0x6f86cf), LOOP_NIGHT = 0.55;
let offlineRender = false;        // true while the frame-exact exporter drives the scene
let exporting = false, exportCancel = false;

function loopCamera(t) {
  const u = t / LOOP_T;
  const fit = camera.aspect < 1 ? Math.pow(1 / camera.aspect, 0.5) : 1;
  const D = 6.6 * fit, pm = followGoal;
  if (loopCam.value === 'sway') {                            // chase from behind, swinging gently from side to side
    const sw = 0.55 * Math.sin(TAU * 2 * u), c = Math.cos(sw), s = Math.sin(sw), bx = -fwdVec.x, bz = -fwdVec.z;
    camera.position.set(pm.x + (bx * c - bz * s) * D, 2.4 + 0.5 * Math.sin(TAU * u), pm.z + (bx * s + bz * c) * D);
    camera.lookAt(pm.x + fwdVec.x * 2.2, 0.7, pm.z + fwdVec.z * 2.2);
  } else {                                                   // one full orbit per cycle
    const az = 0.6 + TAU * u;
    camera.position.set(pm.x + Math.cos(az) * D, 2.6, pm.z + Math.sin(az) * D);
    camera.lookAt(pm.x, 0.7, pm.z);
  }
}
/* Draw one loop frame at exactly time t (used by the frame-exact exporter and the seam tests). */
function drawLoopAt(t) {
  worldFrame(t);
  camera.fov = 50; camera.updateProjectionMatrix();
  loopCamera(t);
  vigAmt = 1; fade = 0; fadeTarget = 0;
  const overlayOn = updateOverlay(0);
  renderer.clear();
  renderer.render(scene, camera);
  if (overlayOn) { renderer.clearDepth(); renderer.render(overlay, orthoCam); }
}
function setLoopWorld(on) {
  loopMode = on;
  stars.visible = !on;
  scene.fog.near = on ? LOOP_FOG_NEAR : 26; scene.fog.far = on ? LOOP_FOG_FAR : 85;
  if (on) {
    scene.background.copy(LOOP_SKY); scene.fog.color.copy(LOOP_SKY);
    hemi.color.copy(LOOP_SKY); hemi.intensity = 0.95;
    sun.color.copy(white).lerp(LOOP_SKY, 0.45); sun.intensity = 1.5;
    nightness = LOOP_NIGHT; bGlow = LOOP_NIGHT;
    camera.fov = 50; camera.updateProjectionMatrix();
    loopU = 0; loopT = 0;
  } else {
    restart();
  }
  resetSounds();
}

/* =========================================================
   RECORDING
   ========================================================= */
const recBtn = document.getElementById('recBtn'), recBadge = document.getElementById('recBadge');
const recTimeEl = document.getElementById('recTime'), recTag = document.getElementById('recTag');
const cdEl = document.getElementById('countdown'), cdNum = document.getElementById('cdNum');
const modal = document.getElementById('modal'), preview = document.getElementById('preview');
const dlBtn = document.getElementById('dlBtn'), vidInfo = document.getElementById('vidInfo');
let recorder = null, chunks = [], recording = false, stopping = false, countingDown = false;
let recElapsed = 0, recIsPro = false, recLimit = 0, lastUrl = null, lastName = '', recMime = '';
let recAspect = '', recWidth = 0, recHeight = 0, recFps = 30, loopRec = false;
let recStart = 0, recPausedAt = 0, recPausedTotal = 0;     // wall-clock timing, so lag can't stretch a timed recording

const QUALITY = {
  smooth: { short: 720,  fps: 30, mbps: 6 },
  high:   { short: 1080, fps: 30, mbps: 10 },
  ultra:  { short: 1080, fps: 60, mbps: 16 }
};

function pickMime() {
  // MP4/H.264 first: usually hardware-encoded (least lag) and plays everywhere. Falls back to WebM.
  const list = ['video/mp4;codecs=avc1,mp4a.40.2', 'video/mp4;codecs=avc1', 'video/webm;codecs=vp8,opus', 'video/webm;codecs=vp9,opus', 'video/webm', 'video/mp4'];
  for (const m of list) if (window.MediaRecorder && MediaRecorder.isTypeSupported(m)) return m;
  return '';
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
function recNow() {
  const ref = recPausedAt || performance.now();
  return Math.max(0, (ref - recStart - recPausedTotal) / 1000);
}

async function startRecording() {
  if (recording || countingDown || exporting) return;
  if (proChk.checked && loopMode && canExportLoop()) { await exportLoopVideo(); return; }   // frame-exact path
  if (!window.MediaRecorder || !canvas.captureStream) { alert('Sorry, your browser does not support canvas recording.'); return; }
  initAudio();
  if (isSmallScreen()) setPanel(false);             // clear the scene while recording on phones
  recIsPro = proChk.checked;
  if (recIsPro) {
    countingDown = true; recBtn.disabled = true; recBtn.textContent = '⏳ Get ready…';
    lockProfessionalSettings(true);
    applyRendererOutput();                         // switch from half-size preview to the full recording size
    if (!loopMode) { director.start(); fadeTarget = 1; }   // a loop must not fade to black
    cdEl.style.display = 'flex';
    for (const n of [3, 2, 1]) {
      cdNum.textContent = n; cdNum.style.animation = 'none'; void cdNum.offsetWidth; cdNum.style.animation = '';
      await sleep(1000);
    }
    cdEl.style.display = 'none';
    countingDown = false; recBtn.disabled = false;
    if (paused) togglePause();
  }
  beginRecorder();
}
function beginRecorder() {
  lockProfessionalSettings(true);
  const q = QUALITY[proQuality.value] || QUALITY.high;
  recAspect = recIsPro ? proAspect.value : 'viewport';
  recWidth = canvas.width;
  recHeight = canvas.height;
  recFps = recIsPro ? q.fps : (recWidth * recHeight > 1.3e6 ? 30 : 60);
  const bitrate = recIsPro ? q.mbps * 1e6 : (recFps === 60 ? 8e6 : 6e6);
  const stream = canvas.captureStream(recFps);
  if (recSoundChk.checked && recDest) {
    const at = recDest.stream.getAudioTracks()[0];
    if (at) stream.addTrack(at);
  }
  recMime = pickMime();
  const opts = { videoBitsPerSecond: bitrate };
  if (recMime) opts.mimeType = recMime;
  try { recorder = new MediaRecorder(stream, opts); }
  catch (e) { recorder = new MediaRecorder(stream); }
  chunks = [];
  recorder.ondataavailable = e => { if (e.data && e.data.size) chunks.push(e.data); };
  recorder.onstop = showPreview;
  resetSounds();   // re-schedule so the recording gets its own timing
  recorder.start(500);
  recording = true; stopping = false; recElapsed = 0;
  recStart = performance.now(); recPausedAt = 0; recPausedTotal = 0;
  loopRec = recIsPro && loopMode;
  recLimit = loopRec ? parseInt(loopCycles.value, 10) * LOOP_T : (recIsPro ? parseInt(proLen.value, 10) : 0);
  if (recIsPro && !loopRec) {
    director.outro = false;
    director.queue = ['tracking'];                 // wide establishing intro → close tracking shot
    director.next('establishing');
    fadeTarget = 0;                                // fade in from black
  }
  recBtn.textContent = '⏹ Stop Recording'; recBtn.classList.add('recording');
  recBadge.style.display = 'flex'; recTag.style.display = recIsPro ? 'inline' : 'none';
}
function requestStop() {
  if (!recording || stopping) return;
  if (recIsPro && !loopRec) { stopping = true; fadeTarget = 1; recBtn.disabled = true; }   // fade out, then stop (loops stop instantly)
  else finalizeStop();
}
function finalizeStop() {
  if (!recorder) return;
  recElapsed = recNow();
  if (recorder.state !== 'inactive') recorder.stop();
  recording = false; stopping = false;
  recBtn.disabled = false; recBtn.textContent = '⏺ Start Recording'; recBtn.classList.remove('recording');
  recBadge.style.display = 'none';
  lockProfessionalSettings(false);
  applyRendererOutput();                           // back to the lighter preview size
  fadeTarget = 0;
}
function showPreview() {
  const type = recMime ? recMime.split(';')[0] : (chunks[0] && chunks[0].type) || 'video/webm';
  presentBlob(new Blob(chunks, { type }), type);
}
function presentBlob(blob, type) {
  if (lastUrl) URL.revokeObjectURL(lastUrl);
  lastUrl = URL.createObjectURL(blob);
  const ext = type.includes('mp4') ? 'mp4' : 'webm';
  const d = new Date(), p = n => String(n).padStart(2, '0');
  const formatSuffix = recIsPro ? (recAspect === '9:16' ? '-9x16' : '-16x9') : '';
  lastName = `domino-city${recIsPro ? (loopRec ? '-loop' : '-pro') : ''}${formatSuffix}-${d.getFullYear()}${p(d.getMonth()+1)}${p(d.getDate())}-${p(d.getHours())}${p(d.getMinutes())}${p(d.getSeconds())}.${ext}`;
  preview.src = lastUrl;
  preview.loop = loopRec;                          // loop recordings replay on repeat so you can check the seam
  const formatInfo = recIsPro ? ` · ${recAspect} · ${recWidth}×${recHeight} · ${recFps}fps` : ` · ${recWidth}×${recHeight}`;
  vidInfo.textContent = `${fmt(recElapsed)} · ${(blob.size / 1048576).toFixed(1)} MB · .${ext}${recIsPro ? (loopRec ? ' · Seamless loop' : ' · Pro cinematic') : ''}${formatInfo}`;
  modal.style.display = 'flex';
  preview.play().catch(() => {});
}
function fmt(s) { s = Math.floor(s); return `${String(Math.floor(s / 60)).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`; }
dlBtn.onclick = () => { if (!lastUrl) return; const a = document.createElement('a'); a.href = lastUrl; a.download = lastName; document.body.appendChild(a); a.click(); a.remove(); };
document.getElementById('closeBtn').onclick = () => { preview.pause(); modal.style.display = 'none'; };
function toggleRecord() {
  if (exporting) exportCancel = true;
  else if (recording) requestStop();
  else startRecording();
}
recBtn.onclick = toggleRecord;

/* =========================================================
   FRAME-EXACT LOOP EXPORT
   The live recorder (MediaRecorder) stamps every frame with the moment the browser happened to
   deliver it, so any hiccup nudges the loop by a few milliseconds and shows up as a stutter at the
   seam. Here each frame is rendered for an exact time (frame i = i / fps), encoded with a fixed
   timestamp and muxed directly. The video is exactly N x 10 s, and the audio is built offline so
   it also wraps around cleanly. Rendering runs as fast as the device allows, not in real time.
   ========================================================= */
const MUXERS = {
  mp4: 'https://cdn.jsdelivr.net/npm/mp4-muxer@5.2.2/build/mp4-muxer.mjs',
  webm: 'https://cdn.jsdelivr.net/npm/webm-muxer@5.1.4/build/webm-muxer.mjs'
};
const canExportLoop = () => !!(window.VideoEncoder && window.VideoFrame && window.OfflineAudioContext);
/* Let the browser breathe between frames. One reusable MessageChannel (not throttled in background tabs, unlike setTimeout);
   creating a new channel per call, as a busy-wait would, floods the renderer with ports and eats gigabytes of memory. */
const _yc = new MessageChannel(); let _yr = null;
_yc.port1.onmessage = () => { const r = _yr; _yr = null; if (r) r(); };
const yieldUI = () => new Promise(r => { _yr = r; _yc.port2.postMessage(0); });
/* Wait until the encoder has worked its queue down (event-driven; the timeout is only a safety net). */
function waitEncoder(enc, max) {
  return new Promise(res => {
    if (enc.encodeQueueSize <= max) return res();
    const done = () => { clearTimeout(tm); enc.removeEventListener('dequeue', check); res(); };
    const check = () => { if (enc.encodeQueueSize <= max) done(); };
    const tm = setTimeout(done, 250);
    enc.addEventListener('dequeue', check);
  });
}

async function pickVideoConfig(w, h, fps, bitrate) {
  const tries = [
    { mux: 'mp4', codec: 'avc1.640034' }, { mux: 'mp4', codec: 'avc1.4d0034' }, { mux: 'mp4', codec: 'avc1.42003e' },
    { mux: 'webm', codec: 'vp09.00.40.08' }, { mux: 'webm', codec: 'vp8' }
  ];
  for (const c of tries) {
    const cfg = { codec: c.codec, width: w, height: h, bitrate, framerate: fps };
    if (c.mux === 'mp4') cfg.avc = { format: 'avc' };
    try { const r = await VideoEncoder.isConfigSupported(cfg); if (r && r.supported) return { mux: c.mux, cfg }; } catch (e) {}
  }
  return null;
}
async function pickAudioConfig(mux, sr, ch) {
  const tries = mux === 'mp4' ? [{ codec: 'mp4a.40.2', mc: 'aac' }, { codec: 'opus', mc: 'opus' }] : [{ codec: 'opus', mc: 'opus' }];
  if (!window.AudioEncoder || !window.AudioData) return null;
  for (const c of tries) {
    const cfg = { codec: c.codec, sampleRate: sr, numberOfChannels: ch, bitrate: 160000 };
    try { const r = await AudioEncoder.isConfigSupported(cfg); if (r && r.supported) return { cfg, mc: c.mc }; } catch (e) {}
  }
  return null;
}

/* One cycle of audio (a click per domino + steady hum), built offline, as stereo Float32 arrays.
   Click tails that run past the end are folded back onto the start; the wind is cross-faded with itself,
   so the last sample leads straight into the first with nothing to hear at the seam. */
async function renderLoopAudio(sr) {
  const n = Math.round(LOOP_T * sr), TAIL = 0.5, nt = Math.round(TAIL * sr);
  let s = 987654321;
  const lcg = () => (s = (s * 1664525 + 1013904223) % 4294967296) / 4294967296;
  const mkNoise = ctx => { const b = ctx.createBuffer(1, ctx.sampleRate * 2, ctx.sampleRate), d = b.getChannelData(0); for (let i = 0; i < d.length; i++) d[i] = lcg() * 2 - 1; return b; };
  const vol = volume, off = syncMs / 1000;

  // clicks: domino k is hit at video time k / RHO - LOOP_PHASE
  const tc = new OfflineAudioContext(2, n + nt, sr);
  const tb = tc.createGain(); tb.gain.value = vol; tb.connect(tc.destination);
  const tn = mkNoise(tc);
  for (let k = 0; k < Math.round(LOOP_T * RHO); k++) {
    const v = k / RHO - LOOP_PHASE;
    const when = (((v + off) % LOOP_T) + LOOP_T) % LOOP_T;
    playClackAt(when, k, tb, tc, tn);
  }
  const tw = await tc.startRendering();

  // wind
  let wind = null;
  if (windChk.checked) {
    const nx = Math.round(0.6 * sr);
    const wc = new OfflineAudioContext(2, n + nx, sr);
    const src = wc.createBufferSource(); src.buffer = mkNoise(wc); src.loop = true;
    const bp = wc.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = 450; bp.Q.value = 0.6;
    const lp = wc.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 1200;
    const wg = wc.createGain(); wg.gain.value = 0.06 * vol;
    src.connect(bp); bp.connect(lp); lp.connect(wg); wg.connect(wc.destination); src.start();
    wind = { buf: await wc.startRendering(), nx };
  }

  const out = [new Float32Array(n), new Float32Array(n)];
  for (let c = 0; c < 2; c++) {
    const T = tw.getChannelData(c), o = out[c];
    for (let i = 0; i < n; i++) o[i] = T[i];
    for (let i = 0; i < nt; i++) o[i] += T[n + i];               // fold the tail back onto the start
    if (wind) {
      const W = wind.buf.getChannelData(c), nx = wind.nx;
      for (let i = 0; i < n; i++) {
        if (i < nx) { const a = (i / nx) * Math.PI / 2; o[i] += W[i] * Math.sin(a) + W[n + i] * Math.cos(a); }
        else o[i] += W[i];
      }
    }
  }
  return out;
}

async function exportLoopVideo() {
  const q = QUALITY[proQuality.value] || QUALITY.high;
  const fps = q.fps, cycles = parseInt(loopCycles.value, 10);
  const total = Math.round(cycles * LOOP_T * fps);
  exporting = true; exportCancel = false; offlineRender = true;
  initAudio();
  if (isSmallScreen()) setPanel(false);
  lockProfessionalSettings(true);
  recBtn.textContent = '⏹ Cancel'; recBtn.classList.add('recording');
  recBadge.style.display = 'flex'; recTag.style.display = 'inline'; recTag.textContent = 'LOOP';
  recTimeEl.textContent = 'Preparing…';
  cancelTwiks();
  applyRendererOutput();                                          // full recording size
  await yieldUI();
  let venc = null, aenc = null, ok = false;
  try {
    const W = canvas.width, H = canvas.height;
    const vc = await pickVideoConfig(W, H, fps, q.mbps * 1e6);
    if (!vc) throw new Error('This browser cannot encode ' + W + '×' + H + ' video.');
    const lib = await import(MUXERS[vc.mux]);
    const SR = 48000;
    const wantAudio = recSoundChk.checked && !muted;
    const ac = wantAudio ? await pickAudioConfig(vc.mux, SR, 2) : null;
    const target = new lib.ArrayBufferTarget();
    const mopts = { target, video: { codec: vc.mux === 'mp4' ? 'avc' : (vc.cfg.codec.startsWith('vp09') ? 'V_VP9' : 'V_VP8'), width: W, height: H, frameRate: fps }, firstTimestampBehavior: 'offset' };
    if (vc.mux === 'mp4') mopts.fastStart = 'in-memory';
    if (ac) mopts.audio = { codec: vc.mux === 'mp4' ? ac.mc : 'A_OPUS', sampleRate: SR, numberOfChannels: 2 };
    const muxer = new lib.Muxer(mopts);
    let encErr = null;
    venc = new VideoEncoder({ output: (c, m) => muxer.addVideoChunk(c, m), error: e => { encErr = e; } });
    venc.configure(vc.cfg);

    // audio first (fast): one cycle, tiled
    if (ac) {
      recTimeEl.textContent = 'Building audio…'; await yieldUI();
      const cyc = await renderLoopAudio(SR);
      // the encoder pads the end by one packet; drop it so the audio is exactly as long as the video
      const endUs = Math.round(total / fps * 1e6) - 1000;
      aenc = new AudioEncoder({ output: (c, m) => { if (c.timestamp < endUs) muxer.addAudioChunk(c, m); }, error: e => { encErr = e; } });
      aenc.configure(ac.cfg);
      const per = cyc[0].length, all = per * cycles, CH = 4800;
      for (let p = 0; p < all; p += CH) {
        const len = Math.min(CH, all - p), data = new Float32Array(len * 2);
        for (let i = 0; i < len; i++) { data[i] = cyc[0][(p + i) % per]; data[len + i] = cyc[1][(p + i) % per]; }
        const ad = new AudioData({ format: 'f32-planar', sampleRate: SR, numberOfFrames: len, numberOfChannels: 2, timestamp: Math.round(p * 1e6 / SR), data });
        aenc.encode(ad); ad.close();
      }
    }

    // video: frame i is the scene at exactly LOOP_PHASE + i / fps
    const t0 = performance.now();
    for (let i = 0; i < total; i++) {
      if (exportCancel || encErr) break;
      drawLoopAt((LOOP_PHASE + i / fps) % LOOP_T);
      const vf = new VideoFrame(canvas, { timestamp: Math.round(i * 1e6 / fps), duration: Math.round(1e6 / fps) });
      venc.encode(vf, { keyFrame: i % (fps * 2) === 0 });
      vf.close();
      if (i % 3 === 2) {
        recTimeEl.textContent = `Rendering ${Math.round(100 * (i + 1) / total)}%`;
        await yieldUI();
        while (venc.encodeQueueSize > 8 && !exportCancel) await waitEncoder(venc, 8);
      }
    }
    if (encErr) throw encErr;
    if (!exportCancel) {
      recTimeEl.textContent = 'Finishing…'; await yieldUI();
      await venc.flush(); if (aenc) await aenc.flush();
      if (encErr) throw encErr;
      muxer.finalize();
      const type = vc.mux === 'mp4' ? 'video/mp4' : 'video/webm';
      recIsPro = true; loopRec = true; recAspect = proAspect.value; recWidth = W; recHeight = H; recFps = fps; recElapsed = total / fps;
      presentBlob(new Blob([target.buffer], { type }), type);
      ok = true;
    }
  } catch (e) {
    console.error(e);
    alert('Loop export failed: ' + (e && e.message ? e.message : e));
  } finally {
    try { if (venc && venc.state !== 'closed') venc.close(); } catch (e) {}
    try { if (aenc && aenc.state !== 'closed') aenc.close(); } catch (e) {}
    exporting = false; offlineRender = false; exportCancel = false;
    recBtn.textContent = '⏺ Start Recording'; recBtn.classList.remove('recording');
    recBadge.style.display = 'none'; recTag.textContent = 'PRO';
    lockProfessionalSettings(false);
    applyRendererOutput();
    loopT = 0; loopU = 0; resetSounds();
  }
  return ok;
}

let snapRequested = false;
function snapshot() { snapRequested = true; }       // taken in animate(), right after the frame is drawn
function doSnapshot() {
  snapRequested = false;
  const a = document.createElement('a');
  a.href = canvas.toDataURL('image/png');
  a.download = `domino-city-${Date.now()}.png`;
  document.body.appendChild(a); a.click(); a.remove();
}

/* =========================================================
   UI
   ========================================================= */
const pauseBtn = document.getElementById('pauseBtn'), speedEl = document.getElementById('speed'), speedVal = document.getElementById('speedVal');
const muteBtn = document.getElementById('muteBtn'), volEl = document.getElementById('vol');
const windChk = document.getElementById('windChk'), recSoundChk = document.getElementById('recSoundChk');
const proChk = document.getElementById('proChk'), proLen = document.getElementById('proLen');
const proAspect = document.getElementById('proAspect'), proQuality = document.getElementById('proQuality');
const proStyle = document.getElementById('proStyle'), loopCycles = document.getElementById('loopCycles'), loopCam = document.getElementById('loopCam');
const loopOpts = document.getElementById('loopOpts'), loopHint = document.getElementById('loopHint');
const syncEl = document.getElementById('syncMs'), syncVal = document.getElementById('syncVal'), latHint = document.getElementById('latHint');
const sBall = document.getElementById('sBall'), sTree = document.getElementById('sTree'), sJumps = document.getElementById('sJumps'), sCam = document.getElementById('sCam'), sFps = document.getElementById('sFps');
let paused = false, speed = 1;
let activeOutputWidth = innerWidth, activeOutputHeight = innerHeight;

function proDims() {
  const q = QUALITY[proQuality.value] || QUALITY.high;
  const s = q.short, l = Math.round(s * 16 / 9);
  return proAspect.value === '9:16' ? [s, l] : [l, s];
}
function applyRendererOutput() {
  if (proChk.checked) {
    const [W, H] = proDims();
    const full = recording || countingDown || exporting;         // recording at full size; the live preview at half size to save GPU
    const k = full ? 1 : 0.5;
    activeOutputWidth = Math.round(W * k);
    activeOutputHeight = Math.round(H * k);
    renderer.setPixelRatio(1);
    renderer.setSize(activeOutputWidth, activeOutputHeight, false);
    // The canvas is fitted to the viewport with CSS while its buffer keeps the exact aspect ratio.
    canvas.style.width = innerWidth + 'px';
    canvas.style.height = innerHeight + 'px';
    camera.aspect = W / H;
  } else {
    activeOutputWidth = innerWidth;
    activeOutputHeight = innerHeight;
    renderer.setPixelRatio(curPR);
    renderer.setSize(innerWidth, innerHeight);
    camera.aspect = innerWidth / innerHeight;
  }
  camera.updateProjectionMatrix();
}

function lockProfessionalSettings(locked) {
  proChk.disabled = locked;
  const off = locked || !proChk.checked;
  proAspect.disabled = off; proQuality.disabled = off; proStyle.disabled = off;
  proLen.disabled = off || proStyle.value === 'loop';        // loops have their own length (repeats × 5 s)
  loopCycles.disabled = locked; loopCam.disabled = locked;
}

function togglePause() {
  paused = !paused;
  pauseBtn.textContent = paused ? '▶ Play' : '⏸ Pause';
  if (recorder && recording) {
    const now = performance.now();
    if (paused) { if (recorder.state === 'recording') recorder.pause(); recPausedAt = now; }
    else {
      if (recorder.state === 'paused') recorder.resume();
      if (recPausedAt) { recPausedTotal += now - recPausedAt; recPausedAt = 0; }
    }
  }
  if (paused) resetSounds();   // nothing stale plays after pausing
}
pauseBtn.onclick = togglePause;
speedEl.oninput = () => {
  speed = parseFloat(speedEl.value); speedVal.textContent = speed.toFixed(1) + '×';
  resetSounds();                   // re-time the pending clicks
};
function toggleMute() { muted = !muted; muteBtn.textContent = muted ? '🔇 Unmute' : '🔊 Mute'; applyVolume(); }
muteBtn.onclick = toggleMute;
volEl.oninput = () => { volume = parseFloat(volEl.value); applyVolume(); };

function setSync(ms) {
  syncMs = clamp(Math.round(ms / 5) * 5, -200, 300);
  syncEl.value = syncMs;
  syncVal.textContent = (syncMs > 0 ? '+' : '') + syncMs + ' ms';
  try { localStorage.setItem('dominoCity.syncMs', String(syncMs)); } catch (e) {}
  resetSounds();                   // apply immediately
}
syncEl.oninput = () => setSync(parseInt(syncEl.value, 10));
document.getElementById('syncReset').onclick = () => setSync(0);
setSync(syncMs);
let lastLatTxt = '';
function updateLatencyHint() {
  if (!actx) return;
  const txt = `Auto-compensating ~${Math.round(deviceLatency() * 1000)} ms device latency · negative = sound earlier, positive = later (keys , and .)`;
  if (txt !== lastLatTxt) { lastLatTxt = txt; latHint.textContent = txt; }
}

proChk.onchange = () => {
  lockProfessionalSettings(false);
  controls.enabled = !proChk.checked;
  applyRendererOutput();
  if (proChk.checked) director.start();
  else { controls.target.copy(followTarget); camera.fov = 50; camera.updateProjectionMatrix(); }
  refreshLoopMode();
};
const refreshProOutput = () => { if (proChk.checked && !recording && !countingDown) applyRendererOutput(); };
proAspect.onchange = refreshProOutput;
proQuality.onchange = refreshProOutput;
function refreshLoopMode() {
  const want = proChk.checked && proStyle.value === 'loop';
  loopOpts.hidden = !want; loopHint.hidden = !want;
  if (want !== loopMode) setLoopWorld(want);
}
proStyle.onchange = () => { lockProfessionalSettings(false); refreshLoopMode(); };
document.getElementById('snapBtn').onclick = snapshot;
document.getElementById('restartBtn').onclick = restart;

/* No start screen: the audio engine is created immediately and unlocked by the first tap, click or key press
   (browsers don't allow sound before some user interaction). */
const UNLOCK_EVENTS = ['pointerup', 'touchend', 'click', 'keydown'];
function unlockAudio() {
  initAudio();
  if (!actx) return;
  actx.resume().then(() => {
    if (actx.state === 'running') UNLOCK_EVENTS.forEach(ev => removeEventListener(ev, unlockAudio));
  }).catch(() => {});
}
UNLOCK_EVENTS.forEach(ev => addEventListener(ev, unlockAudio));
try { initAudio(); } catch (e) {}

/* Controls sheet + quick buttons */
const panelEl = document.getElementById('panel'), panelToggle = document.getElementById('panelToggle');
const quickPause = document.getElementById('quickPause'), quickRec = document.getElementById('quickRec');
const isSmallScreen = () => matchMedia('(max-width: 700px), (pointer: coarse)').matches;
function setPanel(open) { panelEl.classList.toggle('open', open); panelToggle.textContent = open ? '✕' : '⚙'; }
panelToggle.onclick = () => setPanel(!panelEl.classList.contains('open'));
quickPause.onclick = () => pauseBtn.click();
quickRec.onclick = () => recBtn.click();
setPanel(!isSmallScreen());                        // open on desktop, hidden on phones so the scene is clear

addEventListener('keydown', e => {
  if (e.target.tagName === 'SELECT') return;
  const k = e.key.toLowerCase();
  if (k === ' ') { e.preventDefault(); togglePause(); }
  else if (k === 'r') toggleRecord();
  else if (k === 'm') toggleMute();
  else if (k === 'p') snapshot();
  else if (k === ',') setSync(syncMs - 5);
  else if (k === '.') setSync(syncMs + 5);
});
addEventListener('resize', () => {
  if (exporting) return;
  if (recording && !recIsPro) return;               // never change the canvas size while a normal recording is running
  applyRendererOutput();
});
// A hidden tab stops drawing frames; pause so the recording doesn't contain a frozen stretch.
document.addEventListener('visibilitychange', () => { if (document.hidden && recording && !paused) togglePause(); });

/* =========================================================
   RESET / RESTART
   ========================================================= */
const followTarget = new THREE.Vector3(0, 0.9, 0);
function restart() {
  if (loopMode) { loopU = 0; loopT = 0; resetSounds(); return; }   // loop world: just rewind the cycle
  simT = -0.9; resetSounds();
  worldFrame(simT);
  followTarget.copy(followGoal);
  sparksClear();
  if (!proChk.checked) { camera.position.set(followTarget.x - 8.5, 5, followTarget.z + 8.5); controls.target.copy(followTarget); }
  else director.start();
}
function sparksClear() { spPos.fill(-9999); spCol.fill(0); }

/* =========================================================
   MAIN LOOP
   ========================================================= */
/* Adaptive resolution (live view only): if the frame rate stays low, render fewer pixels. */
let emaMs = 16.7, slowFrames = 0, frameNo = 0;
function adaptQuality(rawDt) {
  emaMs += (Math.min(rawDt, 0.25) * 1000 - emaMs) * 0.05;
  if (proChk.checked || recording || countingDown || paused || document.hidden) { slowFrames = 0; return; }
  if (emaMs > 28 && curPR > 0.75) slowFrames++; else slowFrames = 0;
  if (slowFrames > 90) {
    curPR = Math.max(0.75, curPR - 0.25);
    renderer.setPixelRatio(curPR); renderer.setSize(innerWidth, innerHeight);
    slowFrames = 0; emaMs = 16.7;
  }
}

function runLoop(dt) {
  if (recording) loopU = recNow() + LOOP_PHASE;               // fallback recorder only: wall clock, so dropped frames can't shift the loop
  else if (!paused) loopU += dt * speed;
  loopT = loopU % LOOP_T;
  worldFrame(loopT);
  loopCamera(loopT);
  scheduleSoundsLive(loopU, recording ? 1 : speed);
  sCam.textContent = 'Seamless loop';
}

const clock = new THREE.Clock();
let statTimer = 0, latTimer = 0;
restart();

function animate() {
  requestAnimationFrame(animate);
  if (exporting) return;                           // the exporter owns the renderer while it runs
  const rawDt = clock.getDelta();
  const dt = Math.min(rawDt, 0.05);
  adaptQuality(rawDt);
  frameNo++;

  if (loopMode) {
    runLoop(dt);
  } else {
    if (!paused) simT += dt * speed;
    bGlow = nightness;
    worldFrame(simT);
    scheduleSoundsLive(simT, speed);
    followTarget.copy(followGoal);

    if (proChk.checked) {
      director.update(dt, followTarget, aheadPt, !paused);
      sCam.textContent = NAMES[director.type] || 'Auto';
    } else {
      // keep the free camera riding along with the marble
      const delta = _b.subVectors(followTarget, controls.target);
      camera.position.add(delta); controls.target.add(delta);
      controls.autoRotate = !paused;
      controls.update();
      sCam.textContent = 'Free orbit';
    }
    updateSky(Math.max(simT, 0) * VM * (320 / 600));            // day / dusk / night / dawn, about every 90 s
  }

  stars.position.copy(camera.position);
  updateWind(0, dt);
  const overlayOn = updateOverlay(dt);

  // recording clock (wall time) / auto stop / outro
  if (recording) {
    recElapsed = recNow();
    if (loopRec) {
      // stop half a frame before the next cycle would begin, so the last frame leads straight back into the first
      if (!stopping && recElapsed >= recLimit - 0.5 / recFps) requestStop();
    } else if (recIsPro && recLimit > 0 && !stopping) {
      if (!director.outro && recLimit >= 12 && recElapsed >= recLimit - 5.2) {
        director.outro = true;
        director.next('craneUp', { cut: false, dur: 4.4 });   // smooth closing crane shot
      }
      if (recElapsed >= recLimit - 0.8) requestStop();
    }
    recTimeEl.textContent = `REC ${fmt(recElapsed)}${recIsPro && recLimit ? ' / ' + fmt(recLimit) : ''}`;
  }
  if (stopping && fade >= 0.999) finalizeStop();

  statTimer += dt; latTimer += dt;
  if (statTimer > 0.25) {
    statTimer = 0;
    if (loopMode) {
      sBall.textContent = 'looping'; sTree.textContent = '∞';
      sJumps.textContent = (Math.floor(loopT / HOP_T) + 1) + '/' + (LOOP_T / HOP_T);
    } else {
      sBall.textContent = (Math.max(0, simT) * VM).toFixed(0) + ' m';
      sTree.textContent = Math.max(0, Math.floor(simT * RHO));
      sJumps.textContent = Math.max(0, Math.floor(simT / HOP_T) + 1);
    }
    quickRec.classList.toggle('recording', recording);
    quickRec.textContent = recording ? '⏹' : '⏺';
    quickPause.textContent = paused ? '▶' : '⏸';
    sFps.textContent = Math.round(1000 / emaMs) + (curPR < BASE_PR && !proChk.checked ? ' · res ' + Math.round(curPR * 100) + '%' : '');
  }
  if (latTimer > 1) { latTimer = 0; updateLatencyHint(); }

  renderer.clear();
  renderer.render(scene, camera);
  if (overlayOn) { renderer.clearDepth(); renderer.render(overlay, orthoCam); }
  if (snapRequested) doSnapshot();
}
animate();
window.__endlessLoop = { drawLoopAt, canvas, LOOP_T, LOOP_PHASE, full() { exporting = true; applyRendererOutput(); } };   // small hook used for automated seam tests

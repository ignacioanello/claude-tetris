'use strict';

const COLS = 10;
const ROWS = 20;
const BLOCK = 30;

const COLORS = [
  null,
  '#4dd0e1', // I - cyan
  '#ffd54f', // O - yellow
  '#ba68c8', // T - purple
  '#81c784', // S - green
  '#e57373', // Z - red
  '#bbdefb', // J - pale blue
  '#ffb74d', // L - orange
  '#9e9e9e', // N - tuerca (gris metálico)
];

const PIECES = [
  null,
  [[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]], // I
  [[2,2],[2,2]],                               // O
  [[0,3,0],[3,3,3],[0,0,0]],                  // T
  [[0,4,4],[4,4,0],[0,0,0]],                  // S
  [[5,5,0],[0,5,5],[0,0,0]],                  // Z
  [[6,0,0],[6,6,6],[0,0,0]],                  // J
  [[0,0,7],[7,7,7],[0,0,0]],                  // L
  [[8,8,8],[8,0,8],[8,8,8]],                  // N (tuerca)
];

const LINE_SCORES = [0, 100, 300, 500, 800];

const ENERGY_PER_LINE = 25;   // 4 líneas sueltas (o un Tetris) llenan la barra
const SLOW_FACTOR = 2.5;      // multiplicador del intervalo de caída con "Ralentizar"
const PREVIEW_COUNT = 5;      // piezas en cola / piezas mostradas con "Ver siguientes 5"
const NEXT_BOX_H = 120;       // alto del canvas NEXT en modo normal (1 pieza)
const NEXT_BOX_H_EXPANDED = 400; // alto del canvas NEXT mostrando las 5 siguientes

const canvas = document.getElementById('board');
const ctx = canvas.getContext('2d');
const nextCanvas = document.getElementById('next-canvas');
const nextCtx = nextCanvas.getContext('2d');
const holdCanvas = document.getElementById('hold-canvas');
const holdCtx = holdCanvas.getContext('2d');
const holdSection = document.getElementById('hold-section');
const energySection = document.getElementById('energy-section');
const energyFill = document.getElementById('energy-fill');
const abilityOverlay = document.getElementById('ability-overlay');
const abilityGrid = document.getElementById('ability-grid');
const undoCard = abilityGrid.querySelector('[data-ability="undo"]');
const scoreEl = document.getElementById('score');
const linesEl = document.getElementById('lines');
const levelEl = document.getElementById('level');
const overlay = document.getElementById('overlay');
const overlayTitle = document.getElementById('overlay-title');
const overlayScore = document.getElementById('overlay-score');
const restartBtn = document.getElementById('restart-btn');
const pauseOverlay = document.getElementById('pause-overlay');
const resumeBtn = document.getElementById('resume-btn');
const pauseRestartBtn = document.getElementById('pause-restart-btn');
const toggleControlsBtn = document.getElementById('toggle-controls-btn');
const pauseControls = document.getElementById('pause-controls');
const startLevelSelect = document.getElementById('start-level');
const overlayRecords = document.getElementById('overlay-records');
const overlayRecordsBody = document.getElementById('overlay-records-body');
const overlayRecordsStats = document.getElementById('overlay-records-stats');
const overlayRecordEntry = document.getElementById('overlay-record-entry');
const playerNameInput = document.getElementById('player-name');
const saveRecordBtn = document.getElementById('save-record-btn');
const startOverlay = document.getElementById('start-overlay');
const startRecordsBody = document.getElementById('start-records-body');
const startRecordsStats = document.getElementById('start-records-stats');
const playBtn = document.getElementById('play-btn');
const resetRecordsBtn = document.getElementById('reset-records-btn');

const RECORDS_KEY = 'tetris-records';
const MAX_RECORDS = 5;

let board, current, nextQueue, score, lines, level, paused, gameOver, lastTime, dropAccum, dropInterval, animId;
let hold, holdLocked, energy, undoSnapshot, preview5Remaining, slowUntil, abilityMenuOpen;
let startLevel = 1;      // nivel elegido en el selector para la PRÓXIMA partida
let runStartLevel = 1;   // nivel base de la partida en curso (lo fija init())
let combo, maxCombo;
let gameStarted = false;
let recordSaved = false;

// Curva de velocidad compartida por init() y clearLines().
function speedForLevel(lv) {
  return Math.max(100, 1000 - (lv - 1) * 90);
}

function createBoard() {
  return Array.from({ length: ROWS }, () => new Array(COLS).fill(0));
}

function resetPiecePosition(piece) {
  piece.x = Math.floor(COLS / 2) - Math.floor(piece.shape[0].length / 2);
  piece.y = 0;
}

function makePiece(type) {
  const shape = PIECES[type].map(row => [...row]);
  const piece = { type, shape, x: 0, y: 0 };
  resetPiecePosition(piece);
  return piece;
}

function randomPiece() {
  return makePiece(Math.floor(Math.random() * 8) + 1);
}

function clonePiece(p) {
  return { type: p.type, x: p.x, y: p.y, shape: p.shape.map(row => [...row]) };
}

function fillQueue() {
  while (nextQueue.length < PREVIEW_COUNT) nextQueue.push(randomPiece());
}

function collide(shape, ox, oy) {
  for (let r = 0; r < shape.length; r++) {
    for (let c = 0; c < shape[r].length; c++) {
      if (!shape[r][c]) continue;
      const nx = ox + c;
      const ny = oy + r;
      if (nx < 0 || nx >= COLS || ny >= ROWS) return true;
      if (ny >= 0 && board[ny][nx]) return true;
    }
  }
  return false;
}

function rotateCW(shape) {
  const rows = shape.length, cols = shape[0].length;
  const result = Array.from({ length: cols }, () => new Array(rows).fill(0));
  for (let r = 0; r < rows; r++)
    for (let c = 0; c < cols; c++)
      result[c][rows - 1 - r] = shape[r][c];
  return result;
}

function tryRotate() {
  const rotated = rotateCW(current.shape);
  const kicks = [0, -1, 1, -2, 2];
  for (const kick of kicks) {
    if (!collide(rotated, current.x + kick, current.y)) {
      current.shape = rotated;
      current.x += kick;
      return;
    }
  }
}

function merge() {
  for (let r = 0; r < current.shape.length; r++)
    for (let c = 0; c < current.shape[r].length; c++)
      if (current.shape[r][c])
        board[current.y + r][current.x + c] = current.shape[r][c];
}

function clearLines() {
  let cleared = 0;
  for (let r = ROWS - 1; r >= 0; r--) {
    if (board[r].every(v => v !== 0)) {
      board.splice(r, 1);
      board.unshift(new Array(COLS).fill(0));
      cleared++;
      r++;
    }
  }
  if (cleared) {
    lines += cleared;
    score += (LINE_SCORES[cleared] || 0) * level;
    level = runStartLevel + Math.floor(lines / 10);
    dropInterval = speedForLevel(level);
    energy = Math.min(100, energy + cleared * ENERGY_PER_LINE);
    combo++;
    maxCombo = Math.max(maxCombo, combo);
    updateHUD();
    updateEnergy();
  }
  return cleared;
}

function ghostY() {
  let gy = current.y;
  while (!collide(current.shape, current.x, gy + 1)) gy++;
  return gy;
}

function hardDrop() {
  const gy = ghostY();
  score += (gy - current.y) * 2;
  current.y = gy;
  lockPiece();
}

function softDrop() {
  if (!collide(current.shape, current.x, current.y + 1)) {
    current.y++;
    score += 1;
    updateHUD();
  } else {
    lockPiece();
  }
}

function lockPiece() {
  // Snapshot previo a la colocación, para "Deshacer última colocación".
  undoSnapshot = {
    board: board.map(r => [...r]),
    score, lines, level, dropInterval, energy,
    current: clonePiece(current),
    nextQueue: nextQueue.map(clonePiece),
    hold: hold ? clonePiece(hold) : null,
    holdLocked,
    combo, maxCombo,
  };
  merge();
  // La pieza recién fijada no limpió líneas: se rompe la racha de combos.
  if (clearLines() === 0) combo = 0;
  spawn();
}

function spawn() {
  current = nextQueue.shift();
  fillQueue();
  resetPiecePosition(current);
  holdLocked = false;
  updateHoldLockIndicator();
  if (preview5Remaining > 0) {
    preview5Remaining--;
  }
  if (collide(current.shape, current.x, current.y)) {
    endGame();
  }
  drawNext();
}

function updateHUD() {
  scoreEl.textContent = score.toLocaleString();
  linesEl.textContent = lines;
  levelEl.textContent = level;
}

function drawBlock(context, x, y, colorIndex, size, alpha) {
  if (!colorIndex) return;
  const color = COLORS[colorIndex];
  context.globalAlpha = alpha ?? 1;
  context.fillStyle = color;
  context.fillRect(x * size + 1, y * size + 1, size - 2, size - 2);
  // highlight
  context.fillStyle = 'rgba(255,255,255,0.12)';
  context.fillRect(x * size + 1, y * size + 1, size - 2, 4);
  context.globalAlpha = 1;
}

function drawGrid() {
  ctx.strokeStyle = getComputedStyle(document.body).getPropertyValue('--grid-line').trim();
  ctx.lineWidth = 0.5;
  for (let c = 1; c < COLS; c++) {
    ctx.beginPath();
    ctx.moveTo(c * BLOCK, 0);
    ctx.lineTo(c * BLOCK, ROWS * BLOCK);
    ctx.stroke();
  }
  for (let r = 1; r < ROWS; r++) {
    ctx.beginPath();
    ctx.moveTo(0, r * BLOCK);
    ctx.lineTo(COLS * BLOCK, r * BLOCK);
    ctx.stroke();
  }
}

function draw() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  drawGrid();

  // board
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      drawBlock(ctx, c, r, board[r][c], BLOCK);

  // ghost
  const gy = ghostY();
  for (let r = 0; r < current.shape.length; r++)
    for (let c = 0; c < current.shape[r].length; c++)
      if (current.shape[r][c])
        drawBlock(ctx, current.x + c, gy + r, current.shape[r][c], BLOCK, 0.2);

  // current piece
  for (let r = 0; r < current.shape.length; r++)
    for (let c = 0; c < current.shape[r].length; c++)
      drawBlock(ctx, current.x + c, current.y + r, current.shape[r][c], BLOCK);
}

// Dibuja una pieza centrada horizontalmente en una franja de 4 celdas de ancho,
// con su esquina superior en la fila `rowOffset` (en unidades de `blockSize`).
function drawPieceInBox(context, shape, rowOffset, blockSize) {
  const offX = Math.floor((4 - shape[0].length) / 2);
  for (let r = 0; r < shape.length; r++)
    for (let c = 0; c < shape[r].length; c++)
      drawBlock(context, offX + c, rowOffset + r, shape[r][c], blockSize);
}

function drawNext() {
  const expanded = preview5Remaining > 0;
  const targetH = expanded ? NEXT_BOX_H_EXPANDED : NEXT_BOX_H;
  if (nextCanvas.height !== targetH) nextCanvas.height = targetH;
  nextCtx.clearRect(0, 0, nextCanvas.width, nextCanvas.height);

  if (expanded) {
    const NB = 20;
    nextQueue.forEach((piece, i) => {
      drawPieceInBox(nextCtx, piece.shape, i * 4 + 0.5, NB);
    });
  } else {
    const NB = 30;
    const shape = nextQueue[0].shape;
    const offY = Math.floor((4 - shape.length) / 2);
    drawPieceInBox(nextCtx, shape, offY, NB);
  }
}

function drawHold() {
  const NB = 30;
  holdCtx.clearRect(0, 0, holdCanvas.width, holdCanvas.height);
  if (!hold) return;
  const offY = Math.floor((4 - hold.shape.length) / 2);
  drawPieceInBox(holdCtx, hold.shape, offY, NB);
}

function updateHoldLockIndicator() {
  holdSection.classList.toggle('locked', holdLocked);
}

function updateEnergy() {
  energyFill.style.width = energy + '%';
  energySection.classList.toggle('ready', energy >= 100 && !gameOver);
}

function doHold() {
  if (holdLocked || paused || gameOver || abilityMenuOpen) return;
  const stored = makePiece(current.type); // forma base, sin rotaciones
  if (hold === null) {
    hold = stored;
    spawn();
  } else {
    const incoming = hold;
    resetPiecePosition(incoming);
    hold = stored;
    current = incoming;
    if (collide(current.shape, current.x, current.y)) endGame();
  }
  holdLocked = true;
  updateHoldLockIndicator();
  drawHold();
}

function tryOpenAbilityMenu() {
  if (!gameStarted || energy < 100 || paused || gameOver || abilityMenuOpen) return;
  openAbilityMenu();
}

function openAbilityMenu() {
  abilityMenuOpen = true;
  cancelAnimationFrame(animId);
  undoCard.disabled = undoSnapshot === null;
  abilityOverlay.classList.remove('hidden');
}

function closeAbilityMenu() {
  abilityMenuOpen = false;
  abilityOverlay.classList.add('hidden');
  if (gameOver) return;
  // Sin este reset, el primer dt del loop incluiría todo el tiempo con el menú
  // abierto y la pieza caería de golpe (mismo patrón que togglePause).
  lastTime = performance.now();
  dropAccum = 0;
  animId = requestAnimationFrame(loop);
}

function useAbility(id) {
  if (id === 'undo' && undoSnapshot === null) return; // no gasta energía

  switch (id) {
    case 'preview':
      preview5Remaining = PREVIEW_COUNT;
      drawNext();
      break;
    case 'swap': {
      const swapped = randomPiece();
      while (swapped.type === current.type) {
        swapped.type = Math.floor(Math.random() * 8) + 1;
        swapped.shape = PIECES[swapped.type].map(row => [...row]);
      }
      resetPiecePosition(swapped);
      if (!collide(swapped.shape, swapped.x, swapped.y)) current = swapped;
      break;
    }
    case 'slow':
      slowUntil = performance.now() + 10000;
      break;
    case 'undo':
      restoreSnapshot(undoSnapshot);
      undoSnapshot = null;
      break;
  }

  energy = 0;
  updateEnergy();
  closeAbilityMenu();
}

function restoreSnapshot(s) {
  board = s.board.map(r => [...r]);
  score = s.score;
  lines = s.lines;
  level = s.level;
  dropInterval = s.dropInterval;
  energy = s.energy;
  current = clonePiece(s.current);
  nextQueue = s.nextQueue.map(clonePiece);
  hold = s.hold ? clonePiece(s.hold) : null;
  holdLocked = s.holdLocked;
  combo = s.combo;
  maxCombo = s.maxCombo;
  updateHUD();
  updateEnergy();
  updateHoldLockIndicator();
  drawNext();
  drawHold();
}

abilityGrid.addEventListener('click', e => {
  const card = e.target.closest('[data-ability]');
  if (!card || card.disabled) return;
  useAbility(card.dataset.ability);
});

energySection.addEventListener('click', tryOpenAbilityMenu);

/* ---- Records locales ---- */

function loadRecords() {
  const fallback = { scores: [], bestCombo: 0, maxLines: 0 };
  try {
    const raw = localStorage.getItem(RECORDS_KEY);
    if (!raw) return fallback;
    const obj = JSON.parse(raw);
    return {
      scores: Array.isArray(obj.scores) ? obj.scores : [],
      bestCombo: Number(obj.bestCombo) || 0,
      maxLines: Number(obj.maxLines) || 0,
    };
  } catch (e) {
    return fallback;
  }
}

function saveRecords(obj) {
  try {
    localStorage.setItem(RECORDS_KEY, JSON.stringify(obj));
  } catch (e) {
    /* almacenamiento no disponible: se ignora */
  }
}

function renderRecordsTable(tbody, scores, newIndex) {
  tbody.textContent = '';
  if (!scores.length) {
    const tr = document.createElement('tr');
    const td = document.createElement('td');
    td.colSpan = 3;
    td.className = 'records-empty';
    td.textContent = 'Sin récords todavía';
    tr.appendChild(td);
    tbody.appendChild(tr);
    return;
  }
  scores.forEach((s, i) => {
    const tr = document.createElement('tr');
    if (i === newIndex) tr.className = 'record-new';
    const pos = document.createElement('td');
    pos.className = 'record-pos';
    pos.textContent = (i + 1) + '.';
    const name = document.createElement('td');
    name.className = 'record-name';
    name.textContent = s.name;
    const sc = document.createElement('td');
    sc.className = 'record-score';
    sc.textContent = (Number(s.score) || 0).toLocaleString();
    tr.append(pos, name, sc);
    tbody.appendChild(tr);
  });
}

function renderRecordsStats(el, rec) {
  el.textContent = `Mejor combo: ${rec.bestCombo} · Líneas máximas: ${rec.maxLines}`;
}

function refreshStartOverlay() {
  const rec = loadRecords();
  renderRecordsTable(startRecordsBody, rec.scores, -1);
  renderRecordsStats(startRecordsStats, rec);
}

function showStartOverlay() {
  disarmResetButton();
  refreshStartOverlay();
  startOverlay.classList.remove('hidden');
}

function qualifiesForTop(rec, value) {
  return rec.scores.length < MAX_RECORDS ||
    value > rec.scores[rec.scores.length - 1].score;
}

function saveCurrentRecord() {
  if (recordSaved) return;
  recordSaved = true;
  const rec = loadRecords();
  const name = (playerNameInput.value.trim() || 'Jugador').slice(0, 12);
  const entry = {
    name,
    score,
    lines,
    level,
    combo: maxCombo,
    date: new Date().toISOString(),
  };
  rec.scores.push(entry);
  rec.scores.sort((a, b) => b.score - a.score);
  rec.scores = rec.scores.slice(0, MAX_RECORDS);
  rec.bestCombo = Math.max(rec.bestCombo, maxCombo);
  rec.maxLines = Math.max(rec.maxLines, lines);
  saveRecords(rec);
  renderRecordsTable(overlayRecordsBody, rec.scores, rec.scores.indexOf(entry));
  renderRecordsStats(overlayRecordsStats, rec);
  overlayRecordEntry.classList.add('hidden');
}

function disarmResetButton() {
  resetRecordsBtn.dataset.armed = '';
  resetRecordsBtn.classList.remove('confirm');
  resetRecordsBtn.textContent = 'Resetear records';
}

playBtn.addEventListener('click', () => {
  startOverlay.classList.add('hidden');
  init();
});

resetRecordsBtn.addEventListener('click', () => {
  if (!resetRecordsBtn.dataset.armed) {
    resetRecordsBtn.dataset.armed = '1';
    resetRecordsBtn.classList.add('confirm');
    resetRecordsBtn.textContent = '¿Seguro?';
    return;
  }
  saveRecords({ scores: [], bestCombo: 0, maxLines: 0 });
  disarmResetButton();
  refreshStartOverlay();
});

saveRecordBtn.addEventListener('click', saveCurrentRecord);
playerNameInput.addEventListener('keydown', e => {
  if (e.key === 'Enter') saveCurrentRecord();
});

function endGame() {
  gameOver = true;
  cancelAnimationFrame(animId);
  updateEnergy();
  overlayTitle.textContent = 'GAME OVER';
  overlayScore.textContent = `Puntuación: ${score.toLocaleString()}`;

  recordSaved = false;
  const rec = loadRecords();
  // Los agregados se persisten siempre, entre o no la puntuación al top 5,
  // para no perderlos si el jugador reinicia sin pulsar "Guardar".
  rec.bestCombo = Math.max(rec.bestCombo, maxCombo);
  rec.maxLines = Math.max(rec.maxLines, lines);
  saveRecords(rec);

  overlayRecords.classList.remove('hidden');

  if (qualifiesForTop(rec, score)) {
    playerNameInput.value = 'Jugador';
    overlayRecordEntry.classList.remove('hidden');
    // Tabla actual; la fila nueva se resalta al pulsar "Guardar".
    renderRecordsTable(overlayRecordsBody, rec.scores, -1);
    renderRecordsStats(overlayRecordsStats, rec);
  } else {
    overlayRecordEntry.classList.add('hidden');
    renderRecordsTable(overlayRecordsBody, rec.scores, -1);
    renderRecordsStats(overlayRecordsStats, rec);
  }
  overlay.classList.remove('hidden');
}

function togglePause() {
  if (gameOver || abilityMenuOpen) return;
  paused = !paused;
  if (paused) {
    cancelAnimationFrame(animId);
    pauseOverlay.classList.remove('hidden');
  } else {
    pauseOverlay.classList.add('hidden');
    pauseControls.classList.add('hidden');
    // Evita que Space/Enter "reactive" el botón enfocado y mueva la pieza.
    if (document.activeElement) document.activeElement.blur();
    // Mismo patrón que closeAbilityMenu(): sin este reset el primer dt del loop
    // incluiría todo el tiempo en pausa y la pieza caería de golpe.
    lastTime = performance.now();
    dropAccum = 0;
    animId = requestAnimationFrame(loop);
  }
}

function loop(ts) {
  const dt = ts - lastTime;
  lastTime = ts;
  dropAccum += dt;
  const effectiveInterval = ts < slowUntil ? dropInterval * SLOW_FACTOR : dropInterval;
  if (dropAccum >= effectiveInterval) {
    dropAccum = 0;
    if (!collide(current.shape, current.x, current.y + 1)) {
      current.y++;
    } else {
      lockPiece();
    }
  }
  if (gameOver) return;
  draw();
  animId = requestAnimationFrame(loop);
}

function init(lvl = startLevel) {
  startLevel = Math.min(15, Math.max(1, lvl | 0));
  runStartLevel = startLevel;
  board = createBoard();
  score = 0;
  lines = 0;
  level = runStartLevel;
  paused = false;
  gameOver = false;
  dropInterval = speedForLevel(level);
  dropAccum = 0;
  lastTime = performance.now();
  hold = null;
  holdLocked = false;
  energy = 0;
  undoSnapshot = null;
  preview5Remaining = 0;
  slowUntil = 0;
  abilityMenuOpen = false;
  combo = 0;
  maxCombo = 0;
  gameStarted = true;
  nextQueue = [];
  fillQueue();
  spawn();
  updateHUD();
  updateEnergy();
  updateHoldLockIndicator();
  drawHold();
  overlay.classList.add('hidden');
  overlayRecords.classList.add('hidden');
  overlayRecordEntry.classList.add('hidden');
  abilityOverlay.classList.add('hidden');
  pauseOverlay.classList.add('hidden');
  pauseControls.classList.add('hidden');
  cancelAnimationFrame(animId);
  animId = requestAnimationFrame(loop);
}

document.addEventListener('keydown', e => {
  // El input de nombre de récord no debe disparar atajos del juego.
  if (e.target.tagName === 'INPUT') return;
  // El juego aún no ha arrancado (pantalla de inicio visible).
  if (!gameStarted) return;
  if (abilityMenuOpen) {
    if (e.code === 'Escape') closeAbilityMenu();
    return;
  }
  // Escape sobre el <select> de nivel cierra su desplegable: no togglear pausa.
  if (e.code === 'Escape' && e.target === startLevelSelect) return;
  if (e.code === 'KeyP' || e.code === 'Escape') { togglePause(); return; }
  // Con el menú de pausa abierto ningún input de juego llega a la pieza.
  if (paused || gameOver) return;
  if (e.code === 'KeyE') { tryOpenAbilityMenu(); return; }
  switch (e.code) {
    case 'KeyC':
    case 'ShiftLeft':
    case 'ShiftRight':
      doHold();
      break;
    case 'ArrowLeft':
      if (!collide(current.shape, current.x - 1, current.y)) current.x--;
      break;
    case 'ArrowRight':
      if (!collide(current.shape, current.x + 1, current.y)) current.x++;
      break;
    case 'ArrowDown':
      softDrop();
      break;
    case 'ArrowUp':
    case 'KeyX':
      tryRotate();
      break;
    case 'Space':
      e.preventDefault();
      hardDrop();
      break;
  }
  updateHUD();
});

restartBtn.addEventListener('click', () => init(startLevel));

// ---- Menú de pausa ----
resumeBtn.addEventListener('click', () => { if (paused) togglePause(); });
pauseRestartBtn.addEventListener('click', () => init(startLevel));
toggleControlsBtn.addEventListener('click', () => {
  pauseControls.classList.toggle('hidden');
});
startLevelSelect.addEventListener('change', () => {
  startLevel = Math.min(15, Math.max(1, parseInt(startLevelSelect.value, 10) || 1));
  localStorage.setItem('tetris-start-level', startLevel);
});

const savedStartLevel = parseInt(localStorage.getItem('tetris-start-level'), 10);
if (savedStartLevel >= 1 && savedStartLevel <= 15) {
  startLevel = savedStartLevel;
}
startLevelSelect.value = String(startLevel);

const themeToggle = document.getElementById('theme-toggle');
const toggleIcon = themeToggle.querySelector('.toggle-icon');
const toggleLabel = themeToggle.querySelector('.toggle-label');

function applyTheme(isLight) {
  if (isLight) {
    document.body.classList.add('light-mode');
    toggleIcon.textContent = '☀';
    toggleLabel.textContent = 'DARK';
  } else {
    document.body.classList.remove('light-mode');
    toggleIcon.textContent = '☾';
    toggleLabel.textContent = 'LIGHT';
  }
}

const savedTheme = localStorage.getItem('tetris-theme');
applyTheme(savedTheme === 'light');

themeToggle.addEventListener('click', () => {
  const isLight = !document.body.classList.contains('light-mode');
  applyTheme(isLight);
  localStorage.setItem('tetris-theme', isLight ? 'light' : 'dark');
});

// El juego ya no arranca solo: primero se muestra la pantalla de inicio.
showStartOverlay();

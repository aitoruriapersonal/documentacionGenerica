#!/usr/bin/env python3
"""
genera_torneo.py — Generate documentation for Lichess Arena chess tournaments.

Usage:
    python3 genera_torneo.py --pgn FILE [--url URL] [--out DIR] [--name NAME] [--no-pdf]
    python3 genera_torneo.py        (launches an interactive dialog window)
"""

import argparse
import json
import math
import os
import re
import subprocess
import sys
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import urllib.request
import urllib.error
from collections import defaultdict
from html import escape as _esc

# ── Chess engine JS (embedded from erandioArenaCompleto.html) ─────────────────
CHESS_ENGINE_JS = r"""// ─────────────────────────────────────────────
// PIECE UNICODE MAP
// ─────────────────────────────────────────────
const UNICODE = {
  K:'♔', Q:'♕', R:'♖', B:'♗', N:'♘', P:'♙',
  k:'♚', q:'♛', r:'♜', b:'♝', n:'♞', p:'♟'
};

// ─────────────────────────────────────────────
// CHESS ENGINE
// ─────────────────────────────────────────────

function initBoard() {
  return [
    ['r','n','b','q','k','b','n','r'],
    ['p','p','p','p','p','p','p','p'],
    [null,null,null,null,null,null,null,null],
    [null,null,null,null,null,null,null,null],
    [null,null,null,null,null,null,null,null],
    [null,null,null,null,null,null,null,null],
    ['P','P','P','P','P','P','P','P'],
    ['R','N','B','Q','K','B','N','R']
  ];
}

function cloneBoard(b) {
  return b.map(r => r.slice());
}

function initialState() {
  return {
    board: initBoard(),
    turn: 'w',
    castling: { wK: true, wQ: true, bK: true, bQ: true },
    ep: null,
    lastFrom: null,
    lastTo: null,
    halfMove: 0,
    fullMove: 1
  };
}

function cloneState(s) {
  return {
    board: cloneBoard(s.board),
    turn: s.turn,
    castling: Object.assign({}, s.castling),
    ep: s.ep ? s.ep.slice() : null,
    lastFrom: s.lastFrom ? s.lastFrom.slice() : null,
    lastTo: s.lastTo ? s.lastTo.slice() : null,
    halfMove: s.halfMove,
    fullMove: s.fullMove
  };
}

function sqToRF(sq) {
  const f = sq.charCodeAt(0) - 97;
  const r = 8 - parseInt(sq[1]);
  return [r, f];
}

function isPathClear(board, r1, f1, r2, f2) {
  const dr = Math.sign(r2 - r1);
  const df = Math.sign(f2 - f1);
  let r = r1 + dr, f = f1 + df;
  while (r !== r2 || f !== f2) {
    if (board[r][f] !== null) return false;
    r += dr; f += df;
  }
  return true;
}

function canReach(piece, board, r1, f1, r2, f2, ep, turn) {
  const p = piece.toUpperCase();
  const dr = r2 - r1, df = f2 - f1;

  if (p === 'N') {
    return (Math.abs(dr) === 2 && Math.abs(df) === 1) ||
           (Math.abs(dr) === 1 && Math.abs(df) === 2);
  }
  if (p === 'B') {
    return Math.abs(dr) === Math.abs(df) && dr !== 0 && isPathClear(board, r1, f1, r2, f2);
  }
  if (p === 'R') {
    return (dr === 0 || df === 0) && (dr !== 0 || df !== 0) && isPathClear(board, r1, f1, r2, f2);
  }
  if (p === 'Q') {
    return (Math.abs(dr) === Math.abs(df) || dr === 0 || df === 0) && (dr !== 0 || df !== 0) &&
           isPathClear(board, r1, f1, r2, f2);
  }
  if (p === 'K') {
    return Math.abs(dr) <= 1 && Math.abs(df) <= 1 && (dr !== 0 || df !== 0);
  }
  if (p === 'P') {
    const dir = (turn === 'w') ? -1 : 1;
    const startRow = (turn === 'w') ? 6 : 1;
    const target = board[r2][f2];
    if (df === 0 && dr === dir && target === null) return true;
    if (df === 0 && dr === 2 * dir && r1 === startRow && target === null &&
        board[r1 + dir][f1] === null) return true;
    if (Math.abs(df) === 1 && dr === dir) {
      if (target !== null) return true;
      if (ep && ep[0] === r2 && ep[1] === f2) return true;
    }
    return false;
  }
  return false;
}

function parseSAN(san) {
  san = san.replace(/[+#!?]/g, '').replace(/\s/g, '');

  if (san === 'O-O-O' || san === '0-0-0') return { isCastle: true, isLong: true };
  if (san === 'O-O'   || san === '0-0')   return { isCastle: true, isLong: false };

  let piece = 'P', s = san;
  if ('KQRBN'.includes(s[0])) { piece = s[0]; s = s.slice(1); }

  let promotion = null;
  const promMatch = s.match(/=([QRBN])$/);
  if (promMatch) {
    promotion = promMatch[1];
    s = s.slice(0, s.length - 2);
  }

  s = s.replace('x', '');

  const toSq = s.slice(-2);
  const [toR, toF] = sqToRF(toSq);
  const disambig = s.slice(0, s.length - 2);

  let fromFile = null, fromRank = null;
  for (const ch of disambig) {
    if (ch >= 'a' && ch <= 'h') fromFile = ch.charCodeAt(0) - 97;
    if (ch >= '1' && ch <= '8') fromRank = 8 - parseInt(ch);
  }

  return { piece, fromFile, fromRank, toR, toF, promotion, isCastle: false };
}

function applyMove(state, san) {
  const st = cloneState(state);
  const board = st.board;
  const parsed = parseSAN(san);

  if (parsed.isCastle) {
    if (st.turn === 'w') {
      const row = 7;
      if (parsed.isLong) {
        board[row][4] = null; board[row][0] = null;
        board[row][2] = 'K'; board[row][3] = 'R';
        st.lastFrom = [row, 4]; st.lastTo = [row, 2];
      } else {
        board[row][4] = null; board[row][7] = null;
        board[row][6] = 'K'; board[row][5] = 'R';
        st.lastFrom = [row, 4]; st.lastTo = [row, 6];
      }
      st.castling.wK = false; st.castling.wQ = false;
    } else {
      const row = 0;
      if (parsed.isLong) {
        board[row][4] = null; board[row][0] = null;
        board[row][2] = 'k'; board[row][3] = 'r';
        st.lastFrom = [row, 4]; st.lastTo = [row, 2];
      } else {
        board[row][4] = null; board[row][7] = null;
        board[row][6] = 'k'; board[row][5] = 'r';
        st.lastFrom = [row, 4]; st.lastTo = [row, 6];
      }
      st.castling.bK = false; st.castling.bQ = false;
    }
    st.ep = null;
    st.turn = st.turn === 'w' ? 'b' : 'w';
    if (st.turn === 'w') st.fullMove++;
    return st;
  }

  const { piece, fromFile, fromRank, toR, toF, promotion } = parsed;
  const colorPiece = st.turn === 'w' ? piece.toUpperCase() : piece.toLowerCase();

  let srcR = -1, srcF = -1;
  outer:
  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      const p = board[r][f];
      if (p === null) continue;
      if (p !== colorPiece) continue;
      if (fromFile !== null && f !== fromFile) continue;
      if (fromRank !== null && r !== fromRank) continue;
      if (canReach(piece, board, r, f, toR, toF, st.ep, st.turn)) {
        srcR = r; srcF = f;
        break outer;
      }
    }
  }

  if (srcR === -1) {
    console.warn('Could not find source for', san, 'turn', st.turn);
    st.ep = null;
    st.turn = st.turn === 'w' ? 'b' : 'w';
    return st;
  }

  if (piece === 'P' && st.ep && toR === st.ep[0] && toF === st.ep[1]) {
    const capR = st.turn === 'w' ? toR + 1 : toR - 1;
    board[capR][toF] = null;
  }

  const movingPiece = board[srcR][srcF];
  board[srcR][srcF] = null;
  board[toR][toF] = promotion
    ? (st.turn === 'w' ? promotion.toUpperCase() : promotion.toLowerCase())
    : movingPiece;

  st.lastFrom = [srcR, srcF];
  st.lastTo   = [toR, toF];

  if (piece === 'P' && Math.abs(toR - srcR) === 2) {
    st.ep = [(srcR + toR) / 2, toF];
  } else {
    st.ep = null;
  }

  if (piece === 'K') {
    if (st.turn === 'w') { st.castling.wK = false; st.castling.wQ = false; }
    else                 { st.castling.bK = false; st.castling.bQ = false; }
  }
  if (piece === 'R') {
    if (st.turn === 'w') {
      if (srcR === 7 && srcF === 0) st.castling.wQ = false;
      if (srcR === 7 && srcF === 7) st.castling.wK = false;
    } else {
      if (srcR === 0 && srcF === 0) st.castling.bQ = false;
      if (srcR === 0 && srcF === 7) st.castling.bK = false;
    }
  }
  if (toR === 0 && toF === 0) st.castling.bQ = false;
  if (toR === 0 && toF === 7) st.castling.bK = false;
  if (toR === 7 && toF === 0) st.castling.wQ = false;
  if (toR === 7 && toF === 7) st.castling.wK = false;

  if (st.turn === 'b') st.fullMove++;
  st.turn = st.turn === 'w' ? 'b' : 'w';
  return st;
}

// ─────────────────────────────────────────────
// PGN PARSER
// ─────────────────────────────────────────────

function parsePGN(text) {
  text = text.replace(/\r\n/g, '\n').replace(/\r/g, '\n');

  const games = [];
  const chunks = text.split(/\n(?=\[Event )/).filter(s => s.trim());

  for (const chunk of chunks) {
    const game = { meta: {}, moves: [], positions: [] };

    const headerRe = /\[([A-Za-z]+)\s+"([^"]*)"\]/g;
    let m;
    while ((m = headerRe.exec(chunk)) !== null) {
      game.meta[m[1]] = m[2];
    }

    const lines = chunk.split('\n');
    let movesText = '';
    let inMoves = false;
    for (const line of lines) {
      if (line.startsWith('[')) { inMoves = false; continue; }
      if (line.trim() === '') {
        if (movesText) inMoves = true;
        continue;
      }
      inMoves = true;
      if (inMoves) movesText += ' ' + line.trim();
    }

    movesText = movesText.replace(/\s*(1-0|0-1|1\/2-1\/2|\*)\s*$/, '').trim();

    const tokens = movesText
      .replace(/\{[^}]*\}/g, '')
      .replace(/\([^)]*\)/g, '')
      .replace(/\d+\.+/g, '')
      .split(/\s+/)
      .filter(t => t.length > 0 && !['1-0','0-1','1/2-1/2','*'].includes(t));

    game.moves = tokens;

    let st = initialState();
    game.positions = [cloneState(st)];
    for (const san of tokens) {
      try {
        st = applyMove(st, san);
        game.positions.push(cloneState(st));
      } catch(e) {
        console.error('Error applying move', san, e);
        game.positions.push(cloneState(st));
      }
    }

    games.push(game);
  }

  return games;
}

// ─────────────────────────────────────────────
// UI STATE
// ─────────────────────────────────────────────

let games = [];
let currentGame = 0;
let currentPly  = 0;

// ─────────────────────────────────────────────
// RENDER
// ─────────────────────────────────────────────

function renderBoard(state) {
  const boardEl = document.getElementById('board');
  boardEl.innerHTML = '';
  const { board, lastFrom, lastTo } = state;

  for (let r = 0; r < 8; r++) {
    for (let f = 0; f < 8; f++) {
      const sq = document.createElement('div');
      const isLight = (r + f) % 2 === 0;
      sq.className = 'sq ' + (isLight ? 'light' : 'dark');

      const isFrom = lastFrom && lastFrom[0] === r && lastFrom[1] === f;
      const isTo   = lastTo   && lastTo[0]   === r && lastTo[1]   === f;
      if (isFrom) sq.classList.add('hl-from');
      if (isTo)   sq.classList.add('hl-to');

      const piece = board[r][f];
      if (piece) {
        const span = document.createElement('span');
        span.textContent = UNICODE[piece] || '';
        span.className = piece === piece.toUpperCase() ? 'piece-white' : 'piece-black';
        sq.appendChild(span);
      }
      boardEl.appendChild(sq);
    }
  }
}

function renderMetadata(game) {
  const m = game.meta;
  const el = document.getElementById('metadata');
  const wr = m.White + (m.WhiteElo ? ` (${m.WhiteElo})` : '');
  const br = m.Black + (m.BlackElo ? ` (${m.BlackElo})` : '');
  el.innerHTML = `
    <span><span class="label">White: </span><span class="val">${wr}</span></span>
    <span><span class="label">Black: </span><span class="val">${br}</span></span>
    <span><span class="label">Date: </span><span class="val">${m.Date||'?'}</span></span>
    <span><span class="label">Event: </span><span class="val">${m.Event||'?'}</span></span>
    <span><span class="label">ECO: </span><span class="val">${m.ECO||'?'}</span></span>
    <span><span class="label">Result: </span><span class="val">${m.Result||'?'}</span></span>
  `;
}

function renderMoveList(game, ply) {
  const ml = document.getElementById('moveList');
  const rb = document.getElementById('resultBadge');
  ml.innerHTML = '';

  const moves = game.moves;
  for (let i = 0; i < moves.length; i += 2) {
    const row = document.createElement('div');
    row.className = 'move-row';

    const numSpan = document.createElement('span');
    numSpan.className = 'move-num';
    numSpan.textContent = (Math.floor(i / 2) + 1) + '.';
    row.appendChild(numSpan);

    for (let j = 0; j <= 1; j++) {
      const idx = i + j;
      if (idx >= moves.length) break;
      const span = document.createElement('span');
      span.className = 'move-san' + (idx + 1 === ply ? ' active' : '');
      span.textContent = moves[idx];
      span.dataset.ply = idx + 1;
      span.addEventListener('click', () => {
        currentPly = parseInt(span.dataset.ply);
        refresh();
      });
      row.appendChild(span);
    }
    ml.appendChild(row);
  }

  rb.textContent = game.meta.Result || '';

  const active = ml.querySelector('.active');
  if (active) active.scrollIntoView({ block: 'nearest' });
}

function renderPlyInfo(game, ply) {
  const total = game.moves.length;
  document.getElementById('plyInfo').textContent = `${ply} / ${total}`;
}

function refresh() {
  const game = games[currentGame];
  const state = game.positions[currentPly];
  renderBoard(state);
  renderMoveList(game, currentPly);
  renderPlyInfo(game, currentPly);
}

// ─────────────────────────────────────────────
// GAME SELECTOR
// ─────────────────────────────────────────────

function buildGameSelector() {
  const sel = document.getElementById('gameSelect');
  sel.innerHTML = '';
  games.forEach((g, i) => {
    const opt = document.createElement('option');
    opt.value = i;
    const white = g.meta.White || '?';
    const black = g.meta.Black || '?';
    const result = g.meta.Result || '?';
    opt.textContent = `${i+1}. ${white} vs ${black}  (${result})`;
    sel.appendChild(opt);
  });
  sel.addEventListener('change', () => {
    currentGame = parseInt(sel.value);
    currentPly = 0;
    renderMetadata(games[currentGame]);
    refresh();
  });
}

// ─────────────────────────────────────────────
// CONTROLS
// ─────────────────────────────────────────────

function goFirst()  { currentPly = 0; refresh(); }
function goPrev()   { if (currentPly > 0) { currentPly--; refresh(); } }
function goNext()   { if (currentPly < games[currentGame].moves.length) { currentPly++; refresh(); } }
function goLast()   { currentPly = games[currentGame].moves.length; refresh(); }

document.getElementById('btnFirst').addEventListener('click', goFirst);
document.getElementById('btnPrev').addEventListener('click', goPrev);
document.getElementById('btnNext').addEventListener('click', goNext);
document.getElementById('btnLast').addEventListener('click', goLast);

document.addEventListener('keydown', e => {
  if (e.key === 'ArrowLeft')  { goPrev(); e.preventDefault(); }
  if (e.key === 'ArrowRight') { goNext(); e.preventDefault(); }
  if (e.key === 'Home')       { goFirst(); e.preventDefault(); }
  if (e.key === 'End')        { goLast(); e.preventDefault(); }
});

// ─────────────────────────────────────────────
// INIT
// ─────────────────────────────────────────────

games = parsePGN(PGN_DATA);
console.log('Loaded', games.length, 'games');
buildGameSelector();
if (games.length > 0) {
  renderMetadata(games[0]);
  refresh();
}
"""

# ── CSS constants ─────────────────────────────────────────────────────────────
MAIN_CSS = """
:root {
  --bg: #1a1a2e; --surface: #16213e; --card: #0f3460; --accent: #e94560;
  --gold: #f5a623; --silver: #b0b0b0; --bronze: #cd7f32; --text: #eaeaea;
  --muted: #a0a0b0; --win: #4caf50; --lose: #f44336; --draw: #ff9800;
  --border: #2a3a5a;
}
* { box-sizing: border-box; margin: 0; padding: 0; }
body { font-family: 'Segoe UI', system-ui, sans-serif; background: var(--bg); color: var(--text); line-height: 1.5; }
header { background: linear-gradient(135deg, #0f3460 0%, #1a1a2e 60%, #e94560 100%); padding: 2.5rem 2rem 2rem; text-align: center; border-bottom: 3px solid var(--accent); }
header h1 { font-size: 2.4rem; font-weight: 800; letter-spacing: 1px; }
header .meta { color: var(--muted); margin-top: 0.4rem; font-size: 0.95rem; }
header a { color: var(--gold); text-decoration: none; }
header a:hover { text-decoration: underline; }
.container { max-width: 1400px; margin: 0 auto; padding: 2rem 1rem; }
.notice { background: #1e2d4a; border-left: 4px solid var(--gold); border-radius: 6px; padding: 0.8rem 1.2rem; margin-bottom: 1.5rem; font-size: 0.88rem; color: var(--muted); }
h2 { font-size: 1.4rem; color: var(--gold); margin: 2.5rem 0 1rem; padding-bottom: 0.4rem; border-bottom: 2px solid var(--border); }
h3 { font-size: 1.1rem; color: var(--accent); margin: 1.5rem 0 0.6rem; }
.table-wrap { overflow-x: auto; margin-bottom: 1.5rem; border-radius: 8px; border: 1px solid var(--border); }
table { width: 100%; border-collapse: collapse; font-size: 0.875rem; }
thead tr { background: var(--card); }
thead th { padding: 0.75rem 0.9rem; text-align: left; font-weight: 700; color: var(--gold); white-space: nowrap; border-bottom: 2px solid var(--border); }
tbody tr { border-bottom: 1px solid var(--border); transition: background 0.15s; }
tbody tr:hover { background: #1c2d4a; }
tbody tr:nth-child(even) { background: #111827; }
tbody tr:nth-child(even):hover { background: #1c2d4a; }
td { padding: 0.65rem 0.9rem; vertical-align: middle; white-space: nowrap; }
.rank-1 { color: var(--gold); font-weight: 800; }
.rank-2 { color: var(--silver); font-weight: 700; }
.rank-3 { color: var(--bronze); font-weight: 700; }
.pill { display: inline-block; border-radius: 12px; padding: 2px 10px; font-size: 0.78rem; font-weight: 700; margin: 1px; }
.pill-win { background: #1b3a1f; color: var(--win); }
.pill-lose { background: #3a1b1b; color: #ef9a9a; }
.pill-draw { background: #3a2d00; color: var(--draw); }
.pts { font-weight: 800; color: var(--gold); font-size: 1rem; }
.elo-up { color: var(--win); } .elo-down { color: var(--lose); } .elo-same { color: var(--muted); }
.error-low { color: #81c784; } .error-mid { color: #ffb74d; } .error-high { color: #ef9a9a; }
.section-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 1.2rem; margin-bottom: 1.5rem; }
.stat-card { background: var(--surface); border: 1px solid var(--border); border-radius: 10px; padding: 1.2rem 1.5rem; }
.stat-card .big { font-size: 2.2rem; font-weight: 800; color: var(--accent); }
.stat-card .label { font-size: 0.85rem; color: var(--muted); margin-top: 0.2rem; }
.encounter-cell { font-size: 0.78rem; white-space: nowrap; padding: 0.4rem 0.5rem; }
.ec-win { color: var(--win); } .ec-lose { color: #ef9a9a; } .ec-draw { color: var(--draw); } .ec-none { color: var(--border); }
.player-section { background: var(--surface); border: 1px solid var(--border); border-radius: 10px; padding: 1.5rem; margin-bottom: 1.5rem; }
.player-header { display: flex; align-items: center; gap: 1rem; margin-bottom: 1rem; border-bottom: 1px solid var(--border); padding-bottom: 0.8rem; }
.player-name { font-size: 1.3rem; font-weight: 800; }
.player-elo { font-size: 0.9rem; color: var(--muted); }
.mini-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 0.6rem; margin-bottom: 1rem; }
.mini-stat { background: var(--card); border-radius: 6px; padding: 0.5rem 0.8rem; font-size: 0.82rem; }
.mini-stat .val { font-size: 1.05rem; font-weight: 700; color: var(--gold); }
.lichess-pts { font-weight: 800; color: #a78bfa; font-size: 0.92rem; }
.berserk-icon { color: #f97316; font-size: 0.88rem; }
.enc-pts { font-size: 0.72rem; color: var(--muted); display: block; margin-top: 1px; }
footer { text-align: center; padding: 2rem; color: var(--muted); font-size: 0.82rem; border-top: 1px solid var(--border); margin-top: 3rem; }
.tab-nav { display: flex; gap: 0; background: var(--surface); border-bottom: 2px solid var(--border); padding: 0 1rem; }
.tab-btn { background: none; border: none; border-bottom: 3px solid transparent; color: var(--muted); cursor: pointer; font-size: 1rem; font-weight: 600; padding: 0.9rem 1.5rem; margin-bottom: -2px; transition: color 0.2s, border-color 0.2s; font-family: inherit; }
.tab-btn:hover { color: var(--text); }
.tab-btn.active { color: var(--gold); border-bottom-color: var(--accent); }
.tab-pane { display: none; }
.tab-pane.active { display: block; }
#tab-partidas { padding: 16px; min-height: 100vh; font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; background: #1a1a2e; color: #e0e0e0; }
"""

BOARD_CSS = """
#header { max-width: 960px; margin: 0 auto 12px auto; }
#gameSelect { width: 100%; padding: 8px 10px; background: #16213e; color: #e0e0e0; border: 1px solid #444; border-radius: 6px; font-size: 0.95em; cursor: pointer; margin-bottom: 8px; }
#metadata { background: #16213e; border: 1px solid #333; border-radius: 6px; padding: 8px 12px; font-size: 0.85em; display: flex; flex-wrap: wrap; gap: 6px 20px; color: #ccc; }
#metadata span { white-space: nowrap; }
#metadata .label { color: #aaa; }
#metadata .val { color: #f0e0a0; font-weight: 600; }
#main { display: flex; gap: 16px; max-width: 960px; margin: 0 auto; align-items: flex-start; }
#boardSection { flex: 0 0 auto; display: flex; flex-direction: column; align-items: center; gap: 10px; }
#boardWrapper { display: flex; align-items: center; gap: 4px; }
#rankLabels { display: flex; flex-direction: column; width: 18px; }
#rankLabels span, #fileLabels span { font-size: 0.7em; color: #888; text-align: center; }
#rankLabels span { height: 64px; line-height: 64px; }
#fileLabels { display: flex; width: 512px; padding-left: 22px; }
#fileLabels span { width: 64px; text-align: center; }
#board { display: grid; grid-template-columns: repeat(8, 64px); grid-template-rows: repeat(8, 64px); border: 3px solid #555; border-radius: 2px; overflow: hidden; box-shadow: 0 8px 32px rgba(0,0,0,0.5); }
.sq { width: 64px; height: 64px; display: flex; align-items: center; justify-content: center; font-size: 2.6em; cursor: pointer; position: relative; user-select: none; transition: background 0.1s; }
.sq.light { background: #f0d9b5; }
.sq.dark  { background: #b58863; }
.sq.hl-from.light { background: #cdd26a; }
.sq.hl-from.dark  { background: #aaa23a; }
.sq.hl-to.light   { background: #cdd26a; }
.sq.hl-to.dark    { background: #aaa23a; }
.piece-white { color: #fff; text-shadow: 0 0 2px #000, 0 0 4px #000, 1px 1px 0 #333; }
.piece-black { color: #1a1a1a; text-shadow: 0 0 2px #666; }
#controls { display: flex; gap: 8px; }
#controls button { background: #16213e; color: #e0e0e0; border: 1px solid #444; border-radius: 6px; padding: 8px 16px; font-size: 1.2em; cursor: pointer; transition: background 0.15s; min-width: 52px; }
#controls button:hover { background: #0f3460; }
#controls button:active { background: #e94560; }
#plyInfo { font-size: 0.85em; color: #aaa; min-width: 80px; text-align: center; line-height: 38px; }
#moveListPanel { flex: 1; min-width: 240px; max-width: 360px; display: flex; flex-direction: column; gap: 8px; }
#moveListTitle { font-size: 0.9em; color: #aaa; text-transform: uppercase; letter-spacing: 1px; }
#moveList { background: #16213e; border: 1px solid #333; border-radius: 6px; padding: 8px; overflow-y: auto; max-height: 560px; font-size: 0.88em; line-height: 1.6; }
.move-row { display: flex; align-items: baseline; gap: 4px; padding: 1px 2px; border-radius: 3px; }
.move-row:hover { background: #1e2d50; }
.move-num { color: #777; min-width: 28px; text-align: right; flex-shrink: 0; }
.move-san { padding: 2px 6px; border-radius: 4px; cursor: pointer; min-width: 52px; }
.move-san:hover { background: #2a4080; color: #fff; }
.move-san.active { background: #e94560; color: #fff; font-weight: 700; }
#resultBadge { text-align: center; font-size: 1em; font-weight: 700; padding: 4px 8px; margin-top: 4px; border-radius: 4px; background: #1e2d50; color: #f0c060; }
@media (max-width: 700px) {
  #main { flex-direction: column; align-items: center; }
  #moveListPanel { max-width: 512px; width: 100%; }
  #board { grid-template-columns: repeat(8, 48px); grid-template-rows: repeat(8, 48px); }
  .sq { width: 48px; height: 48px; font-size: 2em; }
  #rankLabels span { height: 48px; line-height: 48px; }
  #fileLabels { width: 384px; }
  #fileLabels span { width: 48px; }
}
"""

PRINT_CSS = """
@media print {
  @page { size: A4 landscape; margin: 12mm 15mm; }
  body { background: #fff !important; color: #000 !important; }
  header, footer, .tab-nav, .notice { display: none; }
  #portada { break-after: page; min-height: unset; padding: 20mm 30mm; background: #fff !important; color: #000 !important; }
  #indice { break-after: page; }
  h2 { break-before: avoid; color: #1a1a2e !important; }
  h3 { color: #e94560 !important; }
  table { font-size: 0.7rem; }
  td, th { padding: 0.3rem 0.4rem; }
  .player-section + .player-section { break-before: page; }
  .pgn-block { font-size: 0.6rem; white-space: pre-wrap; font-family: monospace; }
}
"""

# ── PGN Parsing ───────────────────────────────────────────────────────────────

def _parse_int(val):
    """Safely parse int from string, return None on failure."""
    if val is None:
        return None
    try:
        return int(val)
    except (ValueError, TypeError):
        return None


def _parse_float(val):
    """Safely parse float from string, return None on failure."""
    if val is None:
        return None
    try:
        return float(val)
    except (ValueError, TypeError):
        return None


def remove_variations(text):
    """Remove nested parenthetical variations."""
    result = []
    depth = 0
    for ch in text:
        if ch == '(':
            depth += 1
        elif ch == ')':
            if depth > 0:
                depth -= 1
        elif depth == 0:
            result.append(ch)
    return ''.join(result)


def clean_moves_text(text):
    """Strip comments, variations, NAG annotations from PGN moves text."""
    # Remove comments (single-level, non-nested as per standard PGN)
    text = re.sub(r'\{[^}]*\}', ' ', text, flags=re.DOTALL)
    # Remove variations (handle nesting)
    text = remove_variations(text)
    # Remove NAG annotations
    text = re.sub(r'\$\d+', '', text)
    # Remove ! and ? annotations
    text = re.sub(r'[!?]+', '', text)
    # Normalize whitespace
    text = re.sub(r'\s+', ' ', text).strip()
    return text


def parse_pgn_file(filepath):
    """Parse a PGN file and return list of game dicts."""
    with open(filepath, 'r', encoding='utf-8-sig') as f:
        content = f.read()
    # Normalize line endings
    content = content.replace('\r\n', '\n').replace('\r', '\n')

    # Split into game blocks at each [Event header
    blocks = re.split(r'\n(?=\[Event )', content.strip())
    games = []
    for i, block in enumerate(blocks):
        block = block.strip()
        if not block:
            continue
        game = _parse_single_game(block, i + 1)
        if game:
            games.append(game)
    return games


def _parse_single_game(block, game_num):
    """Parse one PGN game block."""
    headers = {}
    header_re = re.compile(r'\[(\w+)\s+"([^"]*)"\]')
    for m in header_re.finditer(block):
        headers[m.group(1)] = m.group(2)

    if 'White' not in headers or 'Black' not in headers:
        return None

    # Find moves section: lines after the last true PGN header line
    # A proper header is [Word "value"] — avoid matching eval comments like [%wdl ...]
    true_header_re = re.compile(r'^\[([A-Z][A-Za-z]*)\s+"[^"]*"\]\s*$')
    lines = block.split('\n')
    last_header_idx = -1
    for j, line in enumerate(lines):
        if true_header_re.match(line.strip()):
            last_header_idx = j

    moves_lines = lines[last_header_idx + 1:]
    moves_text = '\n'.join(moves_lines).strip()

    # Extract error index from comments
    err_match = re.search(
        r'Gravedad del error:\s*Blancas=([\d.]+)[^/]*/Negras=([\d.]+)',
        moves_text
    )
    err_white = _parse_float(err_match.group(1)) if err_match else None
    err_black = _parse_float(err_match.group(2)) if err_match else None

    # Build clean moves
    clean = clean_moves_text(moves_text)

    # Check for actual moves (tokens that aren't move numbers or results)
    result_tokens = {'1-0', '0-1', '1/2-1/2', '*'}
    move_tokens = [
        t for t in clean.split()
        if t not in result_tokens and not re.match(r'^\d+\.+$', t)
    ]

    ply_count_str = headers.get('PlyCount', '')
    ply_count = int(ply_count_str) if ply_count_str.isdigit() else None
    result = headers.get('Result', '*')

    is_forfeit = (
        (ply_count is not None and ply_count == 0) or len(move_tokens) == 0
    ) and result in ('1-0', '0-1')

    return {
        'game_num': game_num,
        'event': headers.get('Event', ''),
        'site': headers.get('Site', ''),
        'date': headers.get('Date', ''),
        'white': headers.get('White', ''),
        'black': headers.get('Black', ''),
        'result': result,
        'white_elo': _parse_int(headers.get('WhiteElo')),
        'black_elo': _parse_int(headers.get('BlackElo')),
        'eco': headers.get('ECO'),
        'ply_count': ply_count,
        'err_white': err_white,
        'err_black': err_black,
        'is_forfeit': is_forfeit,
        'clean_moves': clean,
        'headers': headers,
        'moves_text': moves_text,
    }


def build_clean_pgn(games):
    """Build clean PGN string for the chess viewer."""
    parts = []
    keep_headers = ['Event', 'Site', 'Date', 'Round', 'White', 'Black',
                    'Result', 'ECO', 'WhiteElo', 'BlackElo', 'PlyCount', 'EventDate']
    for game in games:
        h = game['headers']
        header_lines = []
        for key in keep_headers:
            if key in h:
                val = h[key].replace('\\', '\\\\').replace('`', '\\`')
                header_lines.append(f'[{key} "{val}"]')

        moves = game['clean_moves'].strip()
        if not moves:
            moves = game['result']

        parts.append('\n'.join(header_lines) + '\n\n' + moves)
    return '\n\n'.join(parts)


# ── Lichess API ───────────────────────────────────────────────────────────────

def extract_tournament_id(url):
    """Extract tournament ID from Lichess URL."""
    m = re.search(r'lichess\.org/tournament/([A-Za-z0-9]+)', url)
    return m.group(1) if m else None


def _fetch_url(url, accept=None):
    """Fetch URL content, return bytes."""
    req = urllib.request.Request(url)
    req.add_header('User-Agent', 'genera-torneo/1.0')
    if accept:
        req.add_header('Accept', accept)
    with urllib.request.urlopen(req, timeout=30) as resp:
        return resp.read()


def fetch_lichess_data(tournament_id):
    """Fetch tournament data from Lichess API. Returns dict or None."""
    if not tournament_id:
        return None
    try:
        base = 'https://lichess.org'

        # Tournament metadata
        meta_raw = _fetch_url(f'{base}/api/tournament/{tournament_id}')
        meta = json.loads(meta_raw)

        # Standings (NDJSON)
        results_raw = _fetch_url(
            f'{base}/api/tournament/{tournament_id}/results',
            accept='application/x-ndjson'
        )
        standings = []
        for line in results_raw.decode('utf-8').splitlines():
            line = line.strip()
            if line:
                standings.append(json.loads(line))

        # Games (NDJSON) for berserk tags
        games_raw = _fetch_url(
            f'{base}/api/tournament/{tournament_id}/games?moves=false&tags=true',
            accept='application/x-ndjson'
        )
        api_games = []
        for line in games_raw.decode('utf-8').splitlines():
            line = line.strip()
            if line:
                api_games.append(json.loads(line))

        return {
            'meta': meta,
            'standings': standings,
            'games': api_games,
        }
    except Exception as e:
        print(f'WARNING: Could not fetch Lichess API data: {e}', file=sys.stderr)
        return None


# ── Arena Scoring ─────────────────────────────────────────────────────────────

def compute_arena_score(game_results, berserk_wins=0):
    """
    Compute Lichess Arena score.
    game_results: list of 'win'/'draw'/'loss' in chronological order.
    Returns total score.

    Rules:
    - Normal: win=2, draw=1, loss=0
    - Streak active (from 3rd+ consecutive win): win=4, draw=2
    - Streak activates AFTER 2 consecutive wins (2nd win itself scores normally)
    - A loss breaks the streak AND resets the win counter
    - A draw breaks the activation counter (resets to 0) but does NOT break active streak
    - Draws give +2 if streak is active, +1 otherwise
    """
    score = 0
    streak_active = False
    consecutive_wins = 0
    for r in game_results:
        if r == 'win':
            score += 4 if streak_active else 2
            consecutive_wins += 1
            if consecutive_wins >= 2:
                streak_active = True
        elif r == 'draw':
            score += 2 if streak_active else 1
            consecutive_wins = 0  # draws reset activation counter
        else:  # loss
            streak_active = False
            consecutive_wins = 0
    score += berserk_wins
    return score


def compute_arena_gains(game_results, berserk_per_game=None):
    """
    Returns list of (pts_gained, cumulative_score) per game.
    berserk_per_game: optional list of booleans (True if berserk win).
    """
    gains = []
    score = 0
    streak_active = False
    consecutive_wins = 0
    for i, r in enumerate(game_results):
        is_bw = berserk_per_game[i] if berserk_per_game else False
        if r == 'win':
            pts = 4 if streak_active else 2
            if is_bw:
                pts += 1
            consecutive_wins += 1
            if consecutive_wins >= 2:
                streak_active = True
        elif r == 'draw':
            pts = 2 if streak_active else 1
            consecutive_wins = 0  # reset activation counter
        else:
            streak_active = False
            consecutive_wins = 0
            pts = 0
        score += pts
        gains.append((pts, score))
    return gains


# ── Statistics Computation ────────────────────────────────────────────────────

def compute_player_stats(games, api_data=None):
    """
    Compute per-player stats from games list.
    Returns (players_dict, players_sorted_list, warnings_list).
    """
    # Build per-player game lists (in PGN order = chronological)
    player_games = defaultdict(list)

    for game in games:
        white = game['white']
        black = game['black']
        result = game['result']

        if result == '1-0':
            w_res, b_res = 'win', 'loss'
        elif result == '0-1':
            w_res, b_res = 'loss', 'win'
        elif result == '1/2-1/2':
            w_res, b_res = 'draw', 'draw'
        else:
            continue  # skip unknown results

        w_list = player_games[white]
        b_list = player_games[black]

        w_list.append({
            'game_idx': len(w_list) + 1,
            'global_game_num': game['game_num'],
            'rival': black,
            'color': 'W',
            'result': w_res,
            'own_elo': game['white_elo'],
            'rival_elo': game['black_elo'],
            'err_white': game['err_white'],
            'err_black': game['err_black'],
            'is_forfeit': game['is_forfeit'],
            'berserk': False,
        })
        b_list.append({
            'game_idx': len(b_list) + 1,
            'global_game_num': game['game_num'],
            'rival': white,
            'color': 'B',
            'result': b_res,
            'own_elo': game['black_elo'],
            'rival_elo': game['white_elo'],
            'err_white': game['err_white'],
            'err_black': game['err_black'],
            'is_forfeit': game['is_forfeit'],
            'berserk': False,
        })

    # Lichess API overrides
    api_scores = {}   # username -> official score
    api_ranks = {}    # username -> official rank
    api_berserks = {} # username -> berserk count
    if api_data:
        for entry in api_data.get('standings', []):
            name = entry.get('username', '')
            api_scores[name] = entry.get('score', 0)
            api_ranks[name] = entry.get('rank', 0)
            api_berserks[name] = entry.get('berserk', 0)

    # Build player stats
    players = {}
    for name, pgames in player_games.items():
        game_results = [g['result'] for g in pgames]
        berserk_count = api_berserks.get(name, 0)

        computed_score = compute_arena_score(game_results, berserk_wins=berserk_count)
        lichess_pts = api_scores.get(name, computed_score)

        # ELO tracking
        elo_list = [(g['own_elo'],) for g in pgames if g['own_elo'] is not None]
        elo_start = elo_list[0][0] if elo_list else None
        elo_end = elo_list[-1][0] if elo_list else None
        elo_delta = (elo_end - elo_start) if (elo_start is not None and elo_end is not None) else None

        # Win/draw/loss counts
        wins = sum(1 for r in game_results if r == 'win')
        draws = sum(1 for r in game_results if r == 'draw')
        losses = sum(1 for r in game_results if r == 'loss')
        total = len(game_results)

        wins_w = sum(1 for g in pgames if g['color'] == 'W' and g['result'] == 'win')
        draws_w = sum(1 for g in pgames if g['color'] == 'W' and g['result'] == 'draw')
        losses_w = sum(1 for g in pgames if g['color'] == 'W' and g['result'] == 'loss')
        games_w = wins_w + draws_w + losses_w

        wins_b = sum(1 for g in pgames if g['color'] == 'B' and g['result'] == 'win')
        draws_b = sum(1 for g in pgames if g['color'] == 'B' and g['result'] == 'draw')
        losses_b = sum(1 for g in pgames if g['color'] == 'B' and g['result'] == 'loss')
        games_b = wins_b + draws_b + losses_b

        # Performance
        rival_elos = [g['rival_elo'] for g in pgames if g['rival_elo'] is not None]
        if rival_elos and total > 0:
            avg_opp = sum(rival_elos) / len(rival_elos)
            perf = avg_opp + 400 * (wins - losses) / total
            performance = max(100, min(3500, round(perf)))
        else:
            performance = elo_start or 1500

        # Error averages
        err_as_white = [g['err_white'] for g in pgames if g['color'] == 'W' and g['err_white'] is not None]
        err_as_black = [g['err_black'] for g in pgames if g['color'] == 'B' and g['err_black'] is not None]
        avg_err_white = sum(err_as_white) / len(err_as_white) if err_as_white else None
        avg_err_black = sum(err_as_black) / len(err_as_black) if err_as_black else None

        # Per-game arena gains
        gains = compute_arena_gains(game_results)

        # Annotate game history with gains
        for i, g in enumerate(pgames):
            pts_gained, pts_cumul = gains[i]
            g['pts_gained'] = pts_gained
            g['pts_cumul'] = pts_cumul

        players[name] = {
            'name': name,
            'elo_start': elo_start,
            'elo_end': elo_end,
            'elo_delta': elo_delta,
            'games': total,
            'wins': wins,
            'draws': draws,
            'losses': losses,
            'wins_white': wins_w,
            'draws_white': draws_w,
            'losses_white': losses_w,
            'games_white': games_w,
            'wins_black': wins_b,
            'draws_black': draws_b,
            'losses_black': losses_b,
            'games_black': games_b,
            'lichess_pts': lichess_pts,
            'performance': performance,
            'avg_err_as_white': avg_err_white,
            'avg_err_as_black': avg_err_black,
            'berserk_count': berserk_count,
            'lichess_rank': api_ranks.get(name, 0),
            'game_results': game_results,
            'game_history': pgames,
        }

    # Sort: by lichess_pts desc, then performance desc
    players_sorted = sorted(
        players.values(),
        key=lambda p: (-p['lichess_pts'], -p['performance'])
    )

    # Assign display rank
    for rank, p in enumerate(players_sorted, 1):
        p['rank'] = rank
        if not p['lichess_rank']:
            p['lichess_rank'] = rank

    # Collect warnings
    warnings = []
    forfeit_games = [g for g in games if g['is_forfeit']]
    if forfeit_games:
        fg_desc = ' y '.join(
            f"g{g['game_num']}: {g['white']}–{g['black']}"
            for g in forfeit_games
        )
        warnings.append(
            f"⚠️ {len(forfeit_games)} partida(s) abandonada(s) sin jugadas "
            f"({fg_desc}): contabilizadas con índice de error = 0."
        )

    no_error = [
        g for g in games
        if not g['is_forfeit'] and g['err_white'] is None and g['err_black'] is None
    ]
    if no_error:
        g_list = ', '.join(f"g{g['game_num']}" for g in no_error)
        warnings.append(
            f"⚠️ Partidas sin índice de error: **{g_list}**: excluidas de los promedios de error."
        )

    warnings.append(
        "⚠️ El **Score** oficial de Lichess incluye bonificaciones por racha y berserk."
    )

    return players, players_sorted, warnings


def compute_global_stats(games, players):
    """Compute global tournament statistics."""
    valid = [g for g in games if g['result'] in ('1-0', '0-1', '1/2-1/2')]
    total = len(valid)
    white_wins = sum(1 for g in valid if g['result'] == '1-0')
    black_wins = sum(1 for g in valid if g['result'] == '0-1')
    draws = sum(1 for g in valid if g['result'] == '1/2-1/2')

    all_elos = [p['elo_start'] for p in players.values() if p['elo_start'] is not None]
    avg_elo = round(sum(all_elos) / len(all_elos)) if all_elos else 0

    def _avg(lst):
        clean = [x for x in lst if x is not None]
        return round(sum(clean) / len(clean), 2) if clean else None

    def _stats_for(game_list):
        """Compute avg error and avg elo for a list of games."""
        return {
            'avg_err_white': _avg([g['err_white'] for g in game_list]),
            'avg_err_black': _avg([g['err_black'] for g in game_list]),
            'avg_elo_white': _avg([g['white_elo'] for g in game_list]),
            'avg_elo_black': _avg([g['black_elo'] for g in game_list]),
            'count': len(game_list),
        }

    ww_games = [g for g in valid if g['result'] == '1-0']
    bw_games = [g for g in valid if g['result'] == '0-1']
    dr_games = [g for g in valid if g['result'] == '1/2-1/2']

    return {
        'total_games': total,
        'white_wins': white_wins,
        'black_wins': black_wins,
        'draws': draws,
        'avg_elo': avg_elo,
        'when_white_wins': _stats_for(ww_games),
        'when_black_wins': _stats_for(bw_games),
        'when_draw': _stats_for(dr_games),
        'draw_games': dr_games,
    }


# ── HTML helpers ──────────────────────────────────────────────────────────────

def h(text):
    """HTML-escape a string."""
    return _esc(str(text)) if text is not None else ''


def fmt_elo_delta(delta):
    if delta is None:
        return '<span class="elo-same">—</span>'
    if delta > 0:
        return f'<span class="elo-up">+{delta}</span>'
    if delta < 0:
        return f'<span class="elo-down">{delta}</span>'
    return f'<span class="elo-same">0</span>'


def fmt_error(val):
    if val is None:
        return '—'
    cls = 'error-low' if val < 0.5 else ('error-mid' if val <= 1.0 else 'error-high')
    return f'<span class="{cls}">{val:.2f}</span>'


def rank_badge(rank):
    if rank == 1:
        return '🥇'
    if rank == 2:
        return '🥈'
    if rank == 3:
        return '🥉'
    return str(rank)


def result_icon(result):
    if result == 'win':
        return '✅'
    if result == 'draw':
        return '🟡'
    return '❌'


def result_label(result):
    if result == 'win':
        return 'Victoria'
    if result == 'draw':
        return 'Tablas'
    return 'Derrota'


# ── HTML sections ─────────────────────────────────────────────────────────────

def build_notice_html(warnings):
    if not warnings:
        return ''
    items = ''.join(f'<p>{h(w)}</p>' for w in warnings)
    return f'<div class="notice">{items}</div>'


def build_section0_html(tournament_info):
    """Section 0: scoring guide (static)."""
    name = h(tournament_info.get('name', 'Torneo'))
    return f"""
<h2>0. Guía de Lectura y Aclaraciones</h2>
<h3>0.1 Sistema de Puntuación Arena Lichess</h3>
<p style="color:var(--muted);margin-bottom:1rem;font-size:0.9rem;">
En los torneos Arena de Lichess la puntuación <strong>no</strong> equivale a 1 punto por victoria.
El sistema es el siguiente:
</p>
<div class="table-wrap">
<table>
<thead><tr>
  <th>Resultado</th><th>Puntos (normal)</th><th>Puntos (racha doble 🔥)</th>
</tr></thead>
<tbody>
<tr><td>✅ Victoria</td><td>2</td><td>4</td></tr>
<tr><td>🟡 Tablas</td><td>1</td><td>2</td></tr>
<tr><td>❌ Derrota</td><td>0</td><td>0 (rompe la racha)</td></tr>
<tr><td>⚡ Berserk + Victoria</td><td>3</td><td>5</td></tr>
</tbody>
</table>
</div>
<h3>0.2 La Racha de Puntuación Doble 🔥</h3>
<p style="color:var(--muted);margin-bottom:1rem;font-size:0.9rem;">
Tras ganar <strong>2 partidas consecutivas</strong> se activa la racha doble.
A partir de ese momento cada victoria vale 4 y cada tablas 2.
Una derrota rompe la racha. Las tablas no rompen la racha pero tampoco cuentan para activarla.
</p>
<div class="table-wrap">
<table>
<thead><tr><th>Secuencia</th><th>Desglose</th><th>Total</th></tr></thead>
<tbody>
<tr><td>3 victorias seguidas</td><td>2 + 2 + (2×2)</td><td>8</td></tr>
<tr><td>2 victorias + tablas</td><td>2 + 2 + (1×2)</td><td>6</td></tr>
<tr><td>2 victorias + derrota + tablas</td><td>2 + 2 + 0 + 1</td><td>5</td></tr>
</tbody>
</table>
</div>
<h3>0.3 Modo Berserk ⚡</h3>
<p style="color:var(--muted);font-size:0.9rem;">
⚡ <strong>Modo Berserk:</strong> Al pulsar Berserk al inicio de la partida, el jugador pierde
la mitad de su tiempo pero la victoria vale <strong>+1 punto extra</strong>.
</p>
"""


def build_section1_html(players_sorted):
    """Section 1: player standings table."""
    rows = []
    for p in players_sorted:
        rank = p['rank']
        badge = rank_badge(rank)
        rc = f'rank-{rank}' if rank <= 3 else ''
        name = h(p['name'])
        perf = p['performance']
        elo_s = p['elo_start'] or '—'
        elo_e = p['elo_end'] or '—'
        delta = fmt_elo_delta(p['elo_delta'])
        g = p['games']
        gw = p['games_white']
        gb = p['games_black']
        vb = p['wins_white']
        db = p['draws_white']
        tb = p['losses_white']
        vn = p['wins_black']
        dn = p['draws_black']
        tn = p['losses_black']
        pts_str = f"{p['wins'] + p['draws'] * 0.5:.1f}"
        lpts = p['lichess_pts']

        rows.append(f"""
<tr>
  <td class="{rc}">{badge}</td>
  <td class="{rc}">{p['lichess_rank']}</td>
  <td class="{rc}"><strong>{name}</strong></td>
  <td>{perf}</td>
  <td>{elo_s}</td>
  <td>{elo_e}</td>
  <td>{delta}</td>
  <td>{g}</td>
  <td>{gw}</td><td>{gb}</td>
  <td>{vb}</td><td>{db}</td><td>{tb}</td>
  <td>{vn}</td><td>{dn}</td><td>{tn}</td>
  <td class="pts"><strong>{pts_str}</strong></td>
  <td class="lichess-pts"><strong>{lpts}</strong></td>
</tr>""")

    return f"""
<h2>1. Listado General de Participantes</h2>
<div class="table-wrap">
<table>
<thead><tr>
  <th>#</th><th>Rank</th><th>Jugador</th><th>Performance</th>
  <th>Elo Ini.</th><th>Elo Fin.</th><th>Δ Elo</th>
  <th>Part.</th><th>♟ B</th><th>♟ N</th>
  <th>V-B</th><th>D-B</th><th>T-B</th>
  <th>V-N</th><th>D-N</th><th>T-N</th>
  <th>Pts</th><th>Lichess Pts</th>
</tr></thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
</div>
<p style="color:var(--muted);font-size:0.82rem;">
V = Victorias · D = Tablas · T = Derrotas · -B = con Blancas · -N = con Negras ·
Performance = ELO de rendimiento · Lichess Pts = puntuación oficial (rachas + berserk)
</p>
"""


def build_section2_html(global_stats, games):
    """Section 2: global stats."""
    t = global_stats['total_games']
    ww = global_stats['white_wins']
    bw = global_stats['black_wins']
    dr = global_stats['draws']
    ae = global_stats['avg_elo']
    wp = f'{100*ww//t if t else 0}%'
    bp = f'{100*bw//t if t else 0}%'
    dp = f'{100*dr//t if t else 0}%'

    def _stats_block(label, stats, extra=''):
        if stats['count'] == 0:
            return f'<p style="color:var(--muted)">Sin datos.</p>'
        ew = f"{stats['avg_err_white']:.2f}" if stats['avg_err_white'] is not None else '—'
        eb = f"{stats['avg_err_black']:.2f}" if stats['avg_err_black'] is not None else '—'
        ew_elo = round(stats['avg_elo_white']) if stats['avg_elo_white'] else '—'
        eb_elo = round(stats['avg_elo_black']) if stats['avg_elo_black'] else '—'
        return f"""
<div class="table-wrap">
<table>
<thead><tr><th>Métrica</th><th>♟ Blancas</th><th>♛ Negras</th></tr></thead>
<tbody>
<tr><td><strong>Índice de error promedio</strong></td><td><strong>{ew}</strong></td><td><strong>{eb}</strong></td></tr>
<tr><td><strong>Elo medio</strong></td><td><strong>{ew_elo}</strong></td><td><strong>{eb_elo}</strong></td></tr>
</tbody>
</table>
</div>{extra}"""

    # Draw details
    draw_extra = ''
    draw_games = global_stats['draw_games']
    if draw_games:
        def _dr(v):
            return f'{v:.2f}' if v is not None else '—'
        draw_rows = ''.join(
            f'<tr><td>g{g["game_num"]}</td><td>{h(g["white"])}</td><td>{h(g["black"])}</td>'
            f'<td>{_dr(g["err_white"])}</td>'
            f'<td>{_dr(g["err_black"])}</td>'
            f'<td>{g["white_elo"] or "—"}</td><td>{g["black_elo"] or "—"}</td></tr>'
            for g in draw_games
        )
        draw_extra = f"""
<div class="table-wrap"><table>
<thead><tr><th>#</th><th>Blancas</th><th>Negras</th>
<th>Err. B.</th><th>Err. N.</th><th>Elo B.</th><th>Elo N.</th></tr></thead>
<tbody>{draw_rows}</tbody>
</table></div>"""

    return f"""
<h2>2. Estadísticas Generales</h2>
<div class="section-grid">
  <div class="stat-card"><div class="big">{t}</div><div class="label">Total de partidas</div></div>
  <div class="stat-card"><div class="big">{ae}</div><div class="label">Elo medio del torneo</div></div>
  <div class="stat-card"><div class="big">{ww} ({wp})</div><div class="label">Victorias Blancas</div></div>
  <div class="stat-card"><div class="big">{bw} ({bp})</div><div class="label">Victorias Negras</div></div>
  <div class="stat-card"><div class="big">{dr} ({dp})</div><div class="label">Tablas</div></div>
</div>
<h3>2.1 Cuando Ganan las Blancas ({ww} partidas)</h3>
{_stats_block('Blancas ganan', global_stats['when_white_wins'])}
<h3>2.2 Cuando Ganan las Negras ({bw} partidas)</h3>
{_stats_block('Negras ganan', global_stats['when_black_wins'])}
<h3>2.3 Tablas ({dr} partida(s))</h3>
{_stats_block('Tablas', global_stats['when_draw'], draw_extra)}
"""


def build_section3_html(players_sorted):
    """Section 3: encounter table."""
    max_games = max((p['games'] for p in players_sorted), default=0)

    # Header row
    th_cols = ''.join(f'<th>g{i}</th>' for i in range(1, max_games + 1))
    header = f'<tr><th>Jugador</th>{th_cols}<th>Pts</th><th>⭐ Pts L.</th></tr>'

    rows = []
    for p in players_sorted:
        name = h(p['name'])
        cells = []
        for g in p['game_history']:
            rival = h(g['rival'][:10])
            color = 'W' if g['color'] == 'W' else 'N'
            icon = result_icon(g['result'])
            cls = f"ec-{'win' if g['result']=='win' else ('draw' if g['result']=='draw' else 'lose')}"
            pts = g.get('pts_gained', 0)
            berserk = '⚡' if g.get('berserk') else ''
            cells.append(
                f'<td class="encounter-cell {cls}">'
                f'{rival}·{color} {icon}'
                f'<span class="enc-pts">+{pts}{berserk}</span>'
                f'</td>'
            )
        # Pad with empty cells
        for _ in range(max_games - len(cells)):
            cells.append('<td class="encounter-cell ec-none">—</td>')

        pts_str = f"{p['wins'] + p['draws'] * 0.5:.1f}"
        rows.append(
            f'<tr><td><strong>{name}</strong></td>'
            + ''.join(cells)
            + f'<td class="pts">{pts_str}</td>'
            + f'<td class="lichess-pts">{p["lichess_pts"]}</td>'
            + '</tr>'
        )

    return f"""
<h2>3. Tabla de Encuentros por Participante</h2>
<p style="color:var(--muted);font-size:0.82rem;margin-bottom:1rem;">
<strong>Formato:</strong> Rival·Color Resultado +PtsLichess[⚡] ·
<strong>W</strong> = Blancas · <strong>N</strong> = Negras ·
⚡ = Berserk del jugador de la fila
</p>
<div class="table-wrap">
<table>
<thead>{header}</thead>
<tbody>{''.join(rows)}</tbody>
</table>
</div>
"""


def build_section4_html(players_sorted):
    """Section 4: per-player analysis."""
    parts = []
    for p in players_sorted:
        name = h(p['name'])
        elo_s = p['elo_start'] or '—'
        elo_e = p['elo_end'] or '—'
        delta_str = ''
        if p['elo_delta'] is not None:
            sign = '+' if p['elo_delta'] >= 0 else ''
            delta_str = f'{sign}{p["elo_delta"]}'
        else:
            delta_str = '—'

        g = p['games']
        wins = p['wins']
        draws = p['draws']
        losses = p['losses']
        wpc = f'{100*wins/g:.1f}' if g else '0'
        dpc = f'{100*draws/g:.1f}' if g else '0'
        lpc = f'{100*losses/g:.1f}' if g else '0'

        # Rival elo averages per result
        hist = p['game_history']
        rival_elos_w = [gh['rival_elo'] for gh in hist if gh['result'] == 'win' and gh['rival_elo']]
        rival_elos_l = [gh['rival_elo'] for gh in hist if gh['result'] == 'loss' and gh['rival_elo']]
        rival_elos_d = [gh['rival_elo'] for gh in hist if gh['result'] == 'draw' and gh['rival_elo']]
        avg_rival_w = round(sum(rival_elos_w)/len(rival_elos_w)) if rival_elos_w else None
        avg_rival_l = round(sum(rival_elos_l)/len(rival_elos_l)) if rival_elos_l else None
        avg_rival_d = round(sum(rival_elos_d)/len(rival_elos_d)) if rival_elos_d else None

        # Best win, worst loss, best draw
        wins_list = [(gh['rival_elo'] or 0, gh) for gh in hist if gh['result'] == 'win' and gh['rival_elo']]
        best_win = max(wins_list, key=lambda x: x[0])[1] if wins_list else None
        losses_list = [(gh['rival_elo'] or 9999, gh) for gh in hist if gh['result'] == 'loss' and gh['rival_elo']]
        worst_loss = min(losses_list, key=lambda x: x[0])[1] if losses_list else None
        best_draw_list = [(gh['rival_elo'] or 0, gh) for gh in hist if gh['result'] == 'draw']
        best_draw = max(best_draw_list, key=lambda x: x[0])[1] if best_draw_list else None

        def _notable(label, gh):
            if not gh:
                return f'<tr><td>{label}</td><td>—</td></tr>'
            icon = result_icon(gh['result'])
            rival = h(gh['rival'])
            elo = gh['rival_elo'] or '—'
            color = 'Blancas' if gh['color'] == 'W' else 'Negras'
            return (f'<tr><td>{label}</td>'
                    f'<td>{icon} vs <strong>{rival}</strong> ({elo}) — '
                    f'g{gh["global_game_num"]}: como {color}</td></tr>')

        notable_table = f"""
<div class="table-wrap"><table>
<thead><tr><th>Concepto</th><th>Detalle</th></tr></thead>
<tbody>
{_notable('Mejor victoria', best_win)}
{_notable('Peor derrota', worst_loss)}
{_notable('Mejores tablas', best_draw)}
</tbody>
</table></div>"""

        mini_stats = f"""
<div class="mini-grid">
  <div class="mini-stat"><div class="val">{g}</div>Partidas</div>
  <div class="mini-stat"><div class="val">{wins} ({wpc}%)</div>Victorias</div>
  <div class="mini-stat"><div class="val">{losses} ({lpc}%)</div>Derrotas</div>
  <div class="mini-stat"><div class="val">{draws} ({dpc}%)</div>Tablas</div>
  <div class="mini-stat"><div class="val">{avg_rival_w or '—'}</div>Elo med. rival (victorias)</div>
  <div class="mini-stat"><div class="val">{avg_rival_l or '—'}</div>Elo med. rival (derrotas)</div>
  <div class="mini-stat"><div class="val">{avg_rival_d or '—'}</div>Elo med. rival (tablas)</div>
  <div class="mini-stat"><div class="val">{p['berserk_count']} ({round(100*p['berserk_count']/g) if g else 0}%)</div>Partidas Berserk</div>
  <div class="mini-stat"><div class="val">{p['performance']}</div>Performance</div>
  <div class="mini-stat"><div class="val lichess-pts">{p['lichess_pts']}</div>Lichess Pts</div>
</div>"""

        # Chronological game table
        game_rows = []
        for gh in hist:
            ri = result_icon(gh['result'])
            rl = result_label(gh['result'])
            color_label = 'B (Blancas)' if gh['color'] == 'W' else 'N (Negras)'
            own_elo = gh['own_elo'] or '—'
            rival_elo = gh['rival_elo'] or '—'
            ew = fmt_error(gh['err_white'])
            eb = fmt_error(gh['err_black'])
            berk = '⚡' if gh.get('berserk') else '—'
            cum = gh.get('pts_cumul', '—')
            game_rows.append(f"""
<tr>
  <td>{gh['game_idx']}</td>
  <td>{h(gh['rival'])}</td>
  <td>{color_label}</td>
  <td>{ri} {rl}</td>
  <td>{rival_elo}</td>
  <td>{own_elo}</td>
  <td>{ew}</td>
  <td>{eb}</td>
  <td>{berk}</td>
  <td class="lichess-pts">{cum}</td>
</tr>""")

        chron_table = f"""
<h3>Progreso cronológico</h3>
<div class="table-wrap"><table>
<thead><tr>
  <th>#</th><th>Rival</th><th>Color</th><th>Resultado</th>
  <th>Elo rival</th><th>Elo propio</th>
  <th>Error B.</th><th>Error N.</th>
  <th>⚡ Berserk</th><th>♟ Pts Lichess</th>
</tr></thead>
<tbody>{''.join(game_rows)}</tbody>
</table></div>"""

        parts.append(f"""
<div class="player-section">
  <div class="player-header">
    <div>
      <div class="player-name">♟ {name} <span style="color:var(--muted);font-size:0.75rem">#{p['rank']}</span></div>
      <div class="player-elo">Elo inicial: {elo_s} · Elo final: {elo_e} · Δ Elo: {delta_str}</div>
    </div>
  </div>
  {mini_stats}
  {notable_table}
  {chron_table}
</div>""")

    return f'<h2>4. Análisis Individual por Participante</h2>\n' + '\n'.join(parts)


def build_stats_html(games, players_sorted, global_stats, tournament_info, warnings):
    """Build the full stats HTML fragment (sections 0–4)."""
    notice = build_notice_html(warnings)
    s0 = build_section0_html(tournament_info)
    s1 = build_section1_html(players_sorted)
    s2 = build_section2_html(global_stats, games)
    s3 = build_section3_html(players_sorted)
    s4 = build_section4_html(players_sorted)
    return notice + s0 + s1 + s2 + s3 + s4


def build_chess_viewer_html(clean_pgn):
    """Build the chess viewer tab content."""
    escaped_pgn = clean_pgn.replace('\\', '\\\\').replace('`', '\\`')
    return f"""
<div id="tab-partidas" class="tab-pane">
  <div id="header">
    <select id="gameSelect"></select>
    <div id="metadata"></div>
  </div>
  <div id="main">
    <div id="boardSection">
      <div id="fileLabels">
        <span>a</span><span>b</span><span>c</span><span>d</span>
        <span>e</span><span>f</span><span>g</span><span>h</span>
      </div>
      <div id="boardWrapper">
        <div id="rankLabels">
          <span>8</span><span>7</span><span>6</span><span>5</span>
          <span>4</span><span>3</span><span>2</span><span>1</span>
        </div>
        <div id="board"></div>
      </div>
      <div id="controls">
        <button id="btnFirst">⏮</button>
        <button id="btnPrev">◀</button>
        <span id="plyInfo">0 / 0</span>
        <button id="btnNext">▶</button>
        <button id="btnLast">⏭</button>
      </div>
    </div>
    <div id="moveListPanel">
      <div id="moveListTitle">Moves</div>
      <div id="moveList"></div>
      <div id="resultBadge"></div>
    </div>
  </div>
</div>
<script>
const PGN_DATA = `{escaped_pgn}`;
{CHESS_ENGINE_JS}
</script>
"""


# ── HTML file generation ──────────────────────────────────────────────────────

def _format_date_display(date_str):
    """Format date string for display."""
    if not date_str or date_str == '?':
        return date_str
    # Try YYYY.MM.DD format
    m = re.match(r'(\d{4})\.(\d{2})\.(\d{2})', date_str)
    if m:
        months = ['', 'enero', 'febrero', 'marzo', 'abril', 'mayo', 'junio',
                  'julio', 'agosto', 'septiembre', 'octubre', 'noviembre', 'diciembre']
        y, mo, d = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if 1 <= mo <= 12:
            return f'{d:02d} de {months[mo]} de {y}'
    return date_str


def generate_html_completo(games, players_sorted, global_stats, tournament_info,
                           warnings, output_path):
    """Generate the interactive _completo.html with tabs."""
    name = tournament_info.get('name', 'Torneo')
    date_display = _format_date_display(tournament_info.get('date', ''))
    url = tournament_info.get('url', '')
    player_count = tournament_info.get('player_count', len(players_sorted))
    total_games = global_stats['total_games']

    url_link = f'<a href="{h(url)}" target="_blank">Ver torneo en Lichess</a>' if url else ''

    clean_pgn = build_clean_pgn(games)
    chess_viewer = build_chess_viewer_html(clean_pgn)
    stats_html = build_stats_html(games, players_sorted, global_stats,
                                   tournament_info, warnings)

    html = f"""<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{h(name)}</title>
<style>
{MAIN_CSS}
{BOARD_CSS}
</style>
</head>
<body>
<header>
  <h1>♟ {h(name)}</h1>
  <div class="meta">
    Lichess · {h(date_display)} &nbsp;|&nbsp; {player_count} participantes · {total_games} partidas
    {(' &nbsp;|&nbsp; ' + url_link) if url_link else ''}
  </div>
</header>

<nav class="tab-nav">
  <button class="tab-btn active" data-tab="informe" onclick="switchTab('informe')">📊 Informe</button>
  <button class="tab-btn" data-tab="partidas" onclick="switchTab('partidas')">♟ Partidas</button>
</nav>

<div id="tab-informe" class="tab-pane active">
  <div class="container">
    {stats_html}
  </div>
</div>

{chess_viewer}

<footer>
  Generado con genera_torneo.py · {h(name)} · {h(date_display)}
</footer>

<script>
function switchTab(name) {{
  document.querySelectorAll('.tab-pane').forEach(p => p.classList.remove('active'));
  document.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
  document.getElementById('tab-' + name).classList.add('active');
  document.querySelector('.tab-btn[data-tab="' + name + '"]').classList.add('active');
}}
</script>
</body>
</html>
"""
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(html)
    print(f'Generated: {output_path}')


def generate_html_final(games, players_sorted, global_stats, tournament_info,
                        warnings, output_path):
    """Generate the print-ready _final.html."""
    name = tournament_info.get('name', 'Torneo')
    date_display = _format_date_display(tournament_info.get('date', ''))
    url = tournament_info.get('url', '')
    player_count = tournament_info.get('player_count', len(players_sorted))
    total_games = global_stats['total_games']

    url_link = f'<a href="{h(url)}" target="_blank">{h(url)}</a>' if url else '—'

    stats_html = build_stats_html(games, players_sorted, global_stats,
                                   tournament_info, warnings)

    # PGN section
    pgn_blocks = []
    for game in games:
        white = h(game['white'])
        black = h(game['black'])
        result = h(game['result'])
        eco = h(game.get('eco') or '')
        date = h(game.get('date') or '')
        raw = _esc(game['moves_text'])
        pgn_blocks.append(f"""
<div style="margin-bottom:1.5rem;">
  <div style="font-weight:700;margin-bottom:0.3rem;">
    g{game['game_num']}: {white} vs {black} — {result}
    {f'({eco})' if eco else ''} {date}
  </div>
  <pre class="pgn-block">{raw}</pre>
</div>""")

    # TOC
    toc_entries = [
        ('<a href="#estadisticas">0. Guía de Lectura</a>', ''),
        ('<a href="#sec1">1. Participantes</a>', ''),
        ('<a href="#sec2">2. Estadísticas Generales</a>', ''),
        ('<a href="#sec3">3. Tabla de Encuentros</a>', ''),
        ('<a href="#sec4">4. Análisis Individual</a>', ''),
        ('<a href="#pgn-section">5. Partidas PGN</a>', ''),
    ]
    toc_html = '<ul>' + ''.join(f'<li>{e[0]}</li>' for e in toc_entries) + '</ul>'

    html = f"""<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{h(name)} — Documento Final</title>
<style>
{MAIN_CSS}
{BOARD_CSS}
{PRINT_CSS}
.pgn-block {{
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: 6px;
  padding: 1rem;
  font-family: 'Courier New', monospace;
  font-size: 0.78rem;
  white-space: pre-wrap;
  word-break: break-word;
  color: var(--text);
  margin-bottom: 1rem;
}}
#portada {{
  min-height: 80vh;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  text-align: center;
  padding: 4rem 2rem;
}}
#portada .trophy {{ font-size: 5rem; margin-bottom: 1rem; }}
#portada h1 {{ font-size: 3rem; font-weight: 900; }}
#portada .sub {{ font-size: 1.1rem; color: var(--muted); margin-top: 0.5rem; }}
#portada a {{ color: var(--gold); }}
#indice {{ padding: 2rem; }}
#indice ul {{ list-style: none; padding: 0; }}
#indice li {{ padding: 0.4rem 0; font-size: 1.1rem; border-bottom: 1px solid var(--border); }}
#indice a {{ color: var(--gold); text-decoration: none; }}
</style>
</head>
<body>

<section id="portada">
  <div class="trophy">🏆</div>
  <h1>{h(name)}</h1>
  <div class="sub">Torneo Lichess Arena</div>
  <div class="sub">{h(date_display)}</div>
  <div class="sub">{url_link}</div>
  <div class="sub" style="margin-top:1rem;">
    <strong>{player_count}</strong> participantes · <strong>{total_games}</strong> partidas
  </div>
</section>

<section id="indice">
  <div class="container">
    <h2>Índice</h2>
    {toc_html}
  </div>
</section>

<section id="estadisticas">
  <div class="container">
    {stats_html}
  </div>
</section>

<section id="pgn-section">
  <div class="container">
    <h2>5. Partidas PGN</h2>
    {''.join(pgn_blocks)}
  </div>
</section>

<footer>
  Generado con genera_torneo.py · {h(name)} · {h(date_display)}
</footer>
</body>
</html>
"""
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(html)
    print(f'Generated: {output_path}')


# ── PDF Generation ────────────────────────────────────────────────────────────

def generate_pdf(html_path, pdf_path):
    """Generate PDF via Firefox headless. Returns True on success."""
    for cmd in ['firefox', 'firefox-esr']:
        try:
            subprocess.run(
                [
                    cmd, '--headless', '--no-sandbox',
                    f'--print-to-pdf={pdf_path}',
                    f'file://{os.path.abspath(html_path)}'
                ],
                check=True, timeout=60, capture_output=True
            )
            print(f'Generated PDF: {pdf_path}')
            return True
        except (subprocess.CalledProcessError, FileNotFoundError):
            continue
    print('WARNING: Firefox not found; skipping PDF generation', file=sys.stderr)
    return False


# ── Markdown Generation ───────────────────────────────────────────────────────

def _md_err(val):
    if val is None:
        return '—'
    return f'{val:.2f}'


def _md_avg(lst):
    clean = [x for x in lst if x is not None]
    if not clean:
        return '—'
    return f'{sum(clean)/len(clean):.2f}'


def generate_markdown(games, players_sorted, global_stats, tournament_info,
                      warnings, output_path):
    """Generate Markdown statistics file."""
    name = tournament_info.get('name', 'Torneo')
    date_display = _format_date_display(tournament_info.get('date', ''))
    url = tournament_info.get('url', '')
    player_count = tournament_info.get('player_count', len(players_sorted))
    total_games = global_stats['total_games']
    url_link = f'[Ver torneo]({url})' if url else ''

    lines = []
    lines.append(f'# 🏆 {name} — Estadísticas Completas')
    lines.append(f'### Torneo Lichess | {date_display} | {url_link}')
    lines.append('')
    lines.append(
        f'> **{total_games} partidas** · **{player_count} participantes**'
    )
    for w in warnings:
        lines.append(f'> {w}')
    lines.append('')
    lines.append('---')
    lines.append('')

    # Section 0
    lines.append('## 0. Guía de Lectura y Aclaraciones')
    lines.append('')
    lines.append('### 0.1 Advertencias del Torneo')
    lines.append('')
    for w in warnings:
        lines.append(f'- {w}')
    lines.append('')
    lines.append('### 0.2 Sistema de Puntuación Arena Lichess')
    lines.append('')
    lines.append('En los torneos Arena de Lichess la puntuación **no** equivale a 1 punto por victoria.')
    lines.append('')
    lines.append('| Resultado | Puntos (normal) | Puntos (racha doble 🔥) |')
    lines.append('|-----------|-----------------|------------------------|')
    lines.append('| ✅ Victoria | 2 | 4 |')
    lines.append('| 🟡 Tablas | 1 | 2 |')
    lines.append('| ❌ Derrota | 0 | 0 (rompe la racha) |')
    lines.append('| ⚡ Berserk + Victoria | 3 | 5 |')
    lines.append('')
    lines.append('### 0.3 La Racha de Puntuación Doble 🔥')
    lines.append('')
    lines.append('Tras ganar **2 partidas consecutivas** se activa la racha doble (icono de llama 🔥). '
                 'A partir de ese momento, cada victoria vale 4 puntos y cada tablas 2 puntos. '
                 'Una derrota rompe la racha y se vuelve a la puntuación normal. '
                 'Las tablas no rompen la racha pero tampoco cuentan para activarla.')
    lines.append('')
    lines.append('| Secuencia | Desglose | Total |')
    lines.append('|-----------|----------|-------|')
    lines.append('| 3 victorias seguidas | 2 + 2 + (2×2) | 8 |')
    lines.append('| 2 victorias + tablas | 2 + 2 + (1×2) | 6 |')
    lines.append('| 2 victorias + derrota + tablas | 2 + 2 + 0 + 1 | 5 |')
    lines.append('')
    lines.append('### 0.4 Modo Berserk ⚡')
    lines.append('')
    lines.append('⚡ **Modo Berserk:** Cuando un jugador pulsa el botón Berserk, pierde la mitad '
                 'de su tiempo, pero la victoria vale **+1 punto extra**.')
    lines.append('')
    lines.append('---')
    lines.append('')

    # Section 1
    lines.append('## 1. Listado General de Participantes')
    lines.append('')
    lines.append('| # | Rank | Jugador | Performance | Elo Inicial | Elo Final | Δ Elo | '
                 'Partidas | ♟ B | ♟ N | V-B | D-B | T-B | V-N | D-N | T-N | Pts | Lichess Pts |')
    lines.append('|---|------|---------|------------|------------|----------|-------|'
                 '----------|-----|-----|-----|-----|-----|-----|-----|-----|-----|-------------|')

    medals = {1: '🥇', 2: '🥈', 3: '🥉'}
    for p in players_sorted:
        r = p['rank']
        badge = medals.get(r, '')
        name_col = f'**{p["name"]}**' if r <= 3 else p['name']
        elo_s = p['elo_start'] or '—'
        elo_e = p['elo_end'] or '—'
        delta = ''
        if p['elo_delta'] is not None:
            delta = f'+{p["elo_delta"]}' if p['elo_delta'] >= 0 else str(p['elo_delta'])
        else:
            delta = '—'
        pts_str = f'**{p["wins"] + p["draws"]*0.5:.1f}**'
        lpts = f'**{p["lichess_pts"]}**'
        lines.append(
            f'| {badge} | {p["lichess_rank"]} | {name_col} | {p["performance"]} | '
            f'{elo_s} | {elo_e} | {delta} | {p["games"]} | '
            f'{p["games_white"]} | {p["games_black"]} | '
            f'{p["wins_white"]} | {p["draws_white"]} | {p["losses_white"]} | '
            f'{p["wins_black"]} | {p["draws_black"]} | {p["losses_black"]} | '
            f'{pts_str} | {lpts} |'
        )
    lines.append('')
    lines.append('> **V** = Victorias · **D** = Tablas · **T** = Derrotas · '
                 '**-B** = con Blancas · **-N** = con Negras')
    lines.append('')
    lines.append('---')
    lines.append('')

    # Section 2
    gs = global_stats
    t = gs['total_games']
    ww = gs['white_wins']
    bw = gs['black_wins']
    dr = gs['draws']
    ae = gs['avg_elo']
    wp = f'{100*ww//t if t else 0}%'
    bp = f'{100*bw//t if t else 0}%'
    dp = f'{100*dr//t if t else 0}%'

    lines.append('## 2. Estadísticas Generales')
    lines.append('')
    lines.append('| Concepto | Valor |')
    lines.append('|----------|-------|')
    lines.append(f'| **Total de partidas** | {t} |')
    lines.append(f'| **Elo medio del torneo** | {ae} |')
    lines.append(f'| **Victorias Blancas** | {ww} ({wp}) |')
    lines.append(f'| **Victorias Negras** | {bw} ({bp}) |')
    lines.append(f'| **Tablas** | {dr} ({dp}) |')
    lines.append('')

    def _md_when_block(header, stats):
        c = stats['count']
        lines.append(f'### {header} ({c} partidas)')
        lines.append('')
        if c == 0:
            lines.append('_Sin datos._')
            lines.append('')
            return
        ew = _md_err(stats['avg_err_white'])
        eb = _md_err(stats['avg_err_black'])
        ew_elo = round(stats['avg_elo_white']) if stats['avg_elo_white'] else '—'
        eb_elo = round(stats['avg_elo_black']) if stats['avg_elo_black'] else '—'
        lines.append('| Métrica | ♟ Blancas | ♛ Negras |')
        lines.append('|---------|-----------|----------|')
        lines.append(f'| **Índice de error promedio** | **{ew}** | **{eb}** |')
        lines.append(f'| **Elo medio** | **{ew_elo}** | **{eb_elo}** |')
        lines.append('')

    _md_when_block('2.1 Cuando Ganan las Blancas', gs['when_white_wins'])
    _md_when_block('2.2 Cuando Ganan las Negras', gs['when_black_wins'])

    draw_stats = gs['when_draw']
    lines.append(f'### 2.3 Tablas ({dr} partida(s))')
    lines.append('')
    if gs['draw_games']:
        for dg in gs['draw_games']:
            ew = _md_err(dg['err_white'])
            eb = _md_err(dg['err_black'])
            we = dg['white_elo'] or '—'
            be = dg['black_elo'] or '—'
            lines.append(f'| Métrica | ♟ Blancas ({dg["white"]}) | ♛ Negras ({dg["black"]}) |')
            lines.append('|---------|----------------------|-------------------|')
            lines.append(f'| **Índice de error** | **{ew}** | **{eb}** |')
            lines.append(f'| **Elo** | **{we}** | **{be}** |')
            lines.append('')
    else:
        lines.append('_Sin tablas._')
        lines.append('')

    lines.append('---')
    lines.append('')

    # Section 3: Encounter table
    max_games = max((p['games'] for p in players_sorted), default=0)
    g_headers = ' | '.join(f'g{i}' for i in range(1, max_games + 1))
    lines.append('## 3. Tabla de Encuentros por Participante')
    lines.append('')
    lines.append('> **Formato de cada celda:** `Rival·Color Resultado +PtsLichess[⚡]`')
    lines.append('> **W** = Blancas · **N** = Negras (desde el punto de vista del jugador de la fila)')
    lines.append('')
    header_line = f'| Jugador | {g_headers} | Pts | ⭐ Pts L. |'
    sep_line = '|---------|' + ''.join('----|-' for _ in range(max_games)) + '-----|---------|'
    lines.append(header_line)
    lines.append(sep_line)

    for p in players_sorted:
        cells = []
        for gh in p['game_history']:
            rival = gh['rival'][:10]
            color = 'W' if gh['color'] == 'W' else 'N'
            icon = result_icon(gh['result'])
            pts = gh.get('pts_gained', 0)
            berk = '⚡' if gh.get('berserk') else ''
            cells.append(f'{rival}·{color} {icon} +{pts}{berk}')
        while len(cells) < max_games:
            cells.append('—')
        cells_str = ' | '.join(cells)
        pts_str = f'{p["wins"] + p["draws"]*0.5:.1f}'
        lines.append(f'| **{p["name"]}** | {cells_str} | {pts_str} | {p["lichess_pts"]} |')

    lines.append('')
    lines.append('---')
    lines.append('')

    # Section 4: Per-player
    lines.append('## 4. Análisis Individual por Participante')
    lines.append('')

    for p in players_sorted:
        elo_s = p['elo_start'] or '—'
        elo_e = p['elo_end'] or '—'
        if p['elo_delta'] is not None:
            delta_str = f'+{p["elo_delta"]}' if p['elo_delta'] >= 0 else str(p['elo_delta'])
        else:
            delta_str = '—'

        lines.append(f"### ♟ {p['name']}")
        lines.append(f'**Elo inicial:** {elo_s} · **Elo final:** {elo_e} · **Δ Elo:** {delta_str}')
        lines.append('')

        g = p['games']
        wins = p['wins']
        draws = p['draws']
        losses = p['losses']
        hist = p['game_history']

        rival_elos_w = [gh['rival_elo'] for gh in hist if gh['result'] == 'win' and gh['rival_elo']]
        rival_elos_l = [gh['rival_elo'] for gh in hist if gh['result'] == 'loss' and gh['rival_elo']]
        rival_elos_d = [gh['rival_elo'] for gh in hist if gh['result'] == 'draw' and gh['rival_elo']]
        avg_rival_w = round(sum(rival_elos_w)/len(rival_elos_w)) if rival_elos_w else '—'
        avg_rival_l = round(sum(rival_elos_l)/len(rival_elos_l)) if rival_elos_l else '—'
        avg_rival_d = round(sum(rival_elos_d)/len(rival_elos_d)) if rival_elos_d else '—'

        wpc = f'{100*wins/g:.1f}' if g else '0'
        dpc = f'{100*draws/g:.1f}' if g else '0'
        lpc = f'{100*losses/g:.1f}' if g else '0'

        lines.append('| Stat | Valor |')
        lines.append('|------|-------|')
        lines.append(f'| Partidas | {g} |')
        lines.append(f'| Victorias | {wins} ({wpc}%) |')
        lines.append(f'| Derrotas | {losses} ({lpc}%) |')
        lines.append(f'| Tablas | {draws} ({dpc}%) |')
        lines.append(f'| Elo med. rival (victorias) | {avg_rival_w} |')
        lines.append(f'| Elo med. rival (derrotas) | {avg_rival_l} |')
        lines.append(f'| Elo med. rival (tablas) | {avg_rival_d} |')
        lines.append(f'| Partidas Berserk | {p["berserk_count"]} |')
        lines.append('')

        # Notable games
        wins_list = [(gh['rival_elo'] or 0, gh) for gh in hist if gh['result'] == 'win' and gh['rival_elo']]
        best_win = max(wins_list, key=lambda x: x[0])[1] if wins_list else None
        losses_list = [(gh['rival_elo'] or 9999, gh) for gh in hist if gh['result'] == 'loss' and gh['rival_elo']]
        worst_loss = min(losses_list, key=lambda x: x[0])[1] if losses_list else None
        best_draw_list = [(gh['rival_elo'] or 0, gh) for gh in hist if gh['result'] == 'draw']
        best_draw = max(best_draw_list, key=lambda x: x[0])[1] if best_draw_list else None

        def _md_notable(label, gh):
            if not gh:
                return f'| {label} | — (ninguna) |'
            icon = result_icon(gh['result'])
            color = 'B' if gh['color'] == 'W' else 'N'
            rival = gh['rival']
            elo = gh['rival_elo'] or '—'
            return f'| {label} | {icon} vs **{rival}** ({elo}) — g{gh["global_game_num"]}: como {color} |'

        lines.append('| Concepto | Detalle |')
        lines.append('|----------|---------|')
        lines.append(_md_notable('Mejor victoria', best_win))
        lines.append(_md_notable('Peor derrota', worst_loss))
        lines.append(_md_notable('Mejores tablas', best_draw))
        lines.append('')
        lines.append('#### Progreso cronológico')
        lines.append('')
        lines.append('| # | Rival | Color | Resultado | Elo rival | Elo propio | '
                     'Error B | Error N | ⚡ Berserk | ♟ Pts Lichess |')
        lines.append('|---|-------|-------|-----------|-----------|-----------|'
                     '---------|---------|-----------|--------------|')

        for gh in hist:
            color_label = 'B' if gh['color'] == 'W' else 'N'
            icon = result_icon(gh['result'])
            rl = result_label(gh['result'])
            rival_elo = gh['rival_elo'] or '—'
            own_elo = gh['own_elo'] or '—'
            ew = _md_err(gh['err_white'])
            eb = _md_err(gh['err_black'])
            berk = '⚡' if gh.get('berserk') else '—'
            cum = gh.get('pts_cumul', '—')
            lines.append(
                f'| {gh["game_idx"]} | {gh["rival"]} | {color_label} | '
                f'{icon} {rl} | {rival_elo} | {own_elo} | '
                f'{ew} | {eb} | {berk} | {cum} |'
            )

        lines.append('')
        lines.append('---')
        lines.append('')

    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f'Generated: {output_path}')


# ── Main ──────────────────────────────────────────────────────────────────────

def show_input_dialog():
    """Show a GUI dialog to collect input parameters. Returns an argparse.Namespace."""

    result = {}

    root = tk.Tk()
    root.title('Genera Torneo — Parámetros de entrada')
    root.resizable(False, False)

    pad = {'padx': 8, 'pady': 4}

    # ── PGN file ──────────────────────────────────────────────────────────────
    tk.Label(root, text='Archivo PGN *:', anchor='w').grid(
        row=0, column=0, sticky='w', **pad)
    pgn_var = tk.StringVar()
    pgn_entry = tk.Entry(root, textvariable=pgn_var, width=50)
    pgn_entry.grid(row=0, column=1, **pad)

    def browse_pgn():
        path = filedialog.askopenfilename(
            title='Seleccionar archivo PGN',
            filetypes=[('PGN files', '*.pgn'), ('All files', '*.*')]
        )
        if path:
            pgn_var.set(path)

    tk.Button(root, text='Examinar…', command=browse_pgn).grid(
        row=0, column=2, **pad)

    # ── Lichess URL ───────────────────────────────────────────────────────────
    tk.Label(root, text='URL Lichess:', anchor='w').grid(
        row=1, column=0, sticky='w', **pad)
    url_var = tk.StringVar()
    tk.Entry(root, textvariable=url_var, width=50).grid(row=1, column=1, **pad)

    # ── Output directory ──────────────────────────────────────────────────────
    tk.Label(root, text='Directorio de salida:', anchor='w').grid(
        row=2, column=0, sticky='w', **pad)
    out_var = tk.StringVar()
    tk.Entry(root, textvariable=out_var, width=50).grid(row=2, column=1, **pad)

    def browse_out():
        path = filedialog.askdirectory(title='Seleccionar directorio de salida')
        if path:
            out_var.set(path)

    tk.Button(root, text='Examinar…', command=browse_out).grid(
        row=2, column=2, **pad)

    # ── Base name ─────────────────────────────────────────────────────────────
    tk.Label(root, text='Nombre base:', anchor='w').grid(
        row=3, column=0, sticky='w', **pad)
    name_var = tk.StringVar()
    tk.Entry(root, textvariable=name_var, width=50).grid(row=3, column=1, **pad)

    # ── No PDF checkbox ───────────────────────────────────────────────────────
    no_pdf_var = tk.BooleanVar(value=False)
    tk.Checkbutton(root, text='No generar PDF (--no-pdf)', variable=no_pdf_var).grid(
        row=4, column=1, sticky='w', **pad)

    # ── Separator & buttons ───────────────────────────────────────────────────
    ttk.Separator(root, orient='horizontal').grid(
        row=5, column=0, columnspan=3, sticky='ew', pady=6)

    def on_ok():
        pgn = pgn_var.get().strip()
        if not pgn:
            messagebox.showerror('Error', 'El archivo PGN es obligatorio.')
            return
        if not os.path.exists(pgn):
            messagebox.showerror('Error', f'Archivo PGN no encontrado:\n{pgn}')
            return
        result['pgn'] = pgn
        result['url'] = url_var.get().strip() or None
        result['out'] = out_var.get().strip() or None
        result['name'] = name_var.get().strip() or None
        result['no_pdf'] = no_pdf_var.get()
        root.destroy()

    def on_cancel():
        root.destroy()

    btn_frame = tk.Frame(root)
    btn_frame.grid(row=6, column=0, columnspan=3, pady=6)
    tk.Button(btn_frame, text='Aceptar', width=12, command=on_ok).pack(
        side='left', padx=6)
    tk.Button(btn_frame, text='Cancelar', width=12, command=on_cancel).pack(
        side='left', padx=6)

    root.mainloop()

    if not result:
        print('Operación cancelada por el usuario.', file=sys.stderr)
        sys.exit(0)

    import argparse as _ap
    return _ap.Namespace(
        pgn=result['pgn'],
        url=result['url'],
        out=result['out'],
        name=result['name'],
        no_pdf=result['no_pdf'],
    )


def main():
    # If the user provides CLI arguments, use argparse; otherwise show the GUI dialog.
    if len(sys.argv) > 1:
        parser = argparse.ArgumentParser(
            description='Generate chess tournament documentation from a PGN file.'
        )
        parser.add_argument('--pgn', required=True, help='Path to annotated PGN file')
        parser.add_argument('--url', default=None,
                            help='Lichess tournament URL (e.g. https://lichess.org/tournament/2wCiE6DW)')
        parser.add_argument('--out', default=None,
                            help='Output directory (default: same as PGN directory)')
        parser.add_argument('--name', default=None,
                            help='Base name for output files (default: PGN filename without extension)')
        parser.add_argument('--no-pdf', action='store_true', help='Skip PDF generation')
        args = parser.parse_args()
    else:
        args = show_input_dialog()

    pgn_path = os.path.abspath(args.pgn)
    if not os.path.exists(pgn_path):
        print(f'ERROR: PGN file not found: {pgn_path}', file=sys.stderr)
        sys.exit(1)

    pgn_dir = os.path.dirname(pgn_path)
    pgn_base = os.path.splitext(os.path.basename(pgn_path))[0]

    out_dir = os.path.abspath(args.out) if args.out else pgn_dir
    os.makedirs(out_dir, exist_ok=True)

    base_name = args.name or pgn_base

    print(f'Parsing PGN: {pgn_path}')
    games = parse_pgn_file(pgn_path)
    if not games:
        print('ERROR: No games found in PGN file.', file=sys.stderr)
        sys.exit(1)
    print(f'Found {len(games)} games.')

    # Fetch Lichess API data (optional)
    api_data = None
    if args.url:
        tid = extract_tournament_id(args.url)
        if tid:
            print(f'Fetching Lichess API data for tournament: {tid}')
            api_data = fetch_lichess_data(tid)
        else:
            print(f'WARNING: Could not extract tournament ID from URL: {args.url}',
                  file=sys.stderr)

    # Compute stats
    players, players_sorted, warnings = compute_player_stats(games, api_data)
    global_stats = compute_global_stats(games, players)

    # Build tournament info
    first_game = games[0]
    event_name = first_game.get('event') or 'Torneo'
    game_date = first_game.get('date') or ''

    if api_data and api_data.get('meta'):
        meta = api_data['meta']
        event_name = meta.get('fullName', event_name)
        nb_players = meta.get('nbPlayers', len(players_sorted))
    else:
        nb_players = len(players_sorted)

    tournament_info = {
        'name': event_name,
        'date': game_date,
        'url': args.url or '',
        'player_count': nb_players,
    }

    # Output paths
    completo_path = os.path.join(out_dir, f'{base_name}_completo.html')
    final_path = os.path.join(out_dir, f'{base_name}_final.html')
    stats_path = os.path.join(out_dir, f'{base_name}_estadisticas.md')
    pdf_path = os.path.join(out_dir, f'{base_name}.pdf')

    # Generate files
    generate_html_completo(games, players_sorted, global_stats,
                           tournament_info, warnings, completo_path)
    generate_html_final(games, players_sorted, global_stats,
                        tournament_info, warnings, final_path)
    generate_markdown(games, players_sorted, global_stats,
                      tournament_info, warnings, stats_path)

    if not args.no_pdf:
        generate_pdf(final_path, pdf_path)

    print('\nDone!')


if __name__ == '__main__':
    main()

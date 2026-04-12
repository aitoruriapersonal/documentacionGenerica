#!/usr/bin/env python3
"""
unificarPgn.py — Unifica dos archivos PGN en uno solo.

El primer archivo contiene las tasas de error (partidas anotadas/comentadas).
El segundo archivo contiene los movimientos limpios (sin comentarios).
El resultado es un PGN con los movimientos limpios más la tasa de error al
final de cada partida.

Uso por consola:
    python3 unificarPgn.py --errores FICHERO1 --partidas FICHERO2 --salida FICHERO_SALIDA

Uso con ventana (sin argumentos):
    python3 unificarPgn.py

Extensiones admitidas para los archivos de entrada: .pgn, .txt
"""

import argparse
import os
import re
import sys
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

# ── PGN helpers ───────────────────────────────────────────────────────────────

_ALLOWED_EXT = ('.pgn', '.txt')


def _allowed(path: str) -> bool:
    return os.path.splitext(path)[1].lower() in _ALLOWED_EXT


def _split_games(text: str) -> list:
    """Split a PGN text into individual game strings."""
    parts = re.split(r'(?=^\[Event )', text, flags=re.MULTILINE)
    return [p.strip() for p in parts if p.strip()]


def _parse_headers(game_text: str) -> dict:
    """Extract PGN tag pairs from a game block."""
    headers = {}
    for m in re.finditer(r'^\[(\w+)\s+"((?:[^"\\]|\\.)*)"\]', game_text, re.MULTILINE):
        headers[m.group(1)] = m.group(2)
    return headers


def _get_movetext(game_text: str) -> str:
    """Extract only the movetext (lines after the header tags)."""
    lines = game_text.split('\n')
    movetext_lines = []
    in_movetext = False
    for line in lines:
        stripped = line.strip()
        if not in_movetext:
            if stripped and not stripped.startswith('['):
                in_movetext = True
                movetext_lines.append(line)
        else:
            movetext_lines.append(line)
    return '\n'.join(movetext_lines).strip()


def _headers_text(headers: dict) -> str:
    """Reconstruct PGN header lines from an ordered dict."""
    return '\n'.join(f'[{k} "{v}"]' for k, v in headers.items())


def _extract_error_comment(game_text: str) -> str:
    """
    Return the 'Gravedad del error' part from an annotated game, or None.

    The comment may span multiple lines and may appear inside a larger comment
    block together with eval data. Only the 'Gravedad del error: ...' portion
    is returned.
    """
    collapsed = game_text.replace('\n', ' ')
    # Find any {...} comment that contains "Gravedad del error"
    for m in re.finditer(r'\{([^{}]*Gravedad\s+del\s+error[^{}]*)\}', collapsed):
        content = m.group(1)
        idx = content.find('Gravedad del error')
        # Trim from "Gravedad del error" to end of comment content
        error_part = content[idx:].strip()
        # Normalise internal whitespace
        error_part = re.sub(r'\s+', ' ', error_part)
        return error_part
    return None


def _strip_moves(annotated_text: str) -> str:
    """
    Extract the main-line moves from an annotated movetext, stripping all
    comments {…} and variations (…).  Used for move-based game matching.
    """
    collapsed = annotated_text.replace('\n', ' ')
    # Remove variations (may be nested)
    depth = 0
    result = []
    i = 0
    while i < len(collapsed):
        c = collapsed[i]
        if c == '(':
            depth += 1
        elif c == ')':
            if depth > 0:
                depth -= 1
        elif c == '{':
            # skip to closing }
            j = collapsed.find('}', i + 1)
            i = j if j != -1 else len(collapsed)
        elif depth == 0:
            result.append(c)
        i += 1
    # Remove annotation glyphs ($N) and extra whitespace
    cleaned = re.sub(r'\$\d+', '', ''.join(result))
    return re.sub(r'\s+', ' ', cleaned).strip()


def _moves_signature(game_text: str) -> str:
    """First 10 half-moves as a fingerprint for matching."""
    movetext = _get_movetext(game_text)
    bare = _strip_moves(movetext)
    # Tokenise
    tokens = bare.split()
    # Drop result token and move numbers
    moves = [t for t in tokens if not re.match(r'^\d+\.+$', t)
             and t not in ('1-0', '0-1', '1/2-1/2', '*')]
    return ' '.join(moves[:10])


def _add_error_to_movetext(movetext: str, error_comment: str) -> str:
    """Insert an error comment just before the final result token."""
    result_re = re.compile(r'(1-0|0-1|1/2-1/2|\*)\s*$')
    m = result_re.search(movetext)
    if m:
        before = movetext[:m.start()].rstrip()
        return f'{before} {{{error_comment}}} {m.group(1)}'
    # No result found — append comment at the end
    return movetext + f' {{{error_comment}}}'


_DRAW_RESULTS = {'1/2-1/2', '0.5-0.5'}
_BERSERK_TAGS = ('WhiteBerserk', 'BlackBerserk')


def _has_moves(movetext: str) -> bool:
    """Return True if the movetext contains at least one actual move."""
    stripped = re.sub(r'(1-0|0-1|1/2-1/2|0\.5-0\.5|\*)\s*$', '', movetext).strip()
    # Remove comments
    stripped = re.sub(r'\{[^{}]*\}', '', stripped).strip()
    return bool(stripped)


def _fallback_error_comment(result: str, has_moves: bool) -> str:
    """
    Build a default 'Gravedad del error' comment when no annotation is found.

    Rules:
      Has moves:
        1-0  → Blancas=0.20 / Negras=1.00
        0-1  → Blancas=1.00 / Negras=0.20
        draw → Blancas=0.50 / Negras=0.50
      No moves (forfeit / connectivity issue):
        1-0  → Blancas=0.00 / Negras=2.00
        0-1  → Blancas=2.00 / Negras=0.00
        draw → Blancas=0.50 / Negras=0.50
    """
    if result in _DRAW_RESULTS:
        w, b = 0.50, 0.50
        note = ' (estimado)'
    elif result == '1-0':
        w, b = (0.20, 1.00) if has_moves else (0.00, 2.00)
        note = ' (estimado)' if has_moves else ' (abandono)'
    elif result == '0-1':
        w, b = (1.00, 0.20) if has_moves else (2.00, 0.00)
        note = ' (estimado)' if has_moves else ' (abandono)'
    else:
        w, b = 0.50, 0.50
        note = ' (estimado)'

    return f'Gravedad del error: Blancas={w:.2f}/Negras={b:.2f}{note}'


# ── Core merging logic ────────────────────────────────────────────────────────

def unificar(errores_path: str, partidas_path: str, salida_path: str) -> int:
    """
    Merge two PGN files.

    *errores_path*  — PGN with annotations (and 'Gravedad del error' comments)
    *partidas_path* — PGN with clean moves (no comments)
    *salida_path*   — output file

    Returns the number of games written.
    """
    for label, path in [('errores', errores_path), ('partidas', partidas_path)]:
        if not _allowed(path):
            raise ValueError(
                f'El archivo "{path}" no tiene una extensión válida. '
                f'Solo se admiten: {", ".join(_ALLOWED_EXT)}'
            )
        if not os.path.exists(path):
            raise FileNotFoundError(f'Archivo no encontrado: {path}')

    errores_text = open(errores_path, encoding='utf-8', errors='replace').read()
    partidas_text = open(partidas_path, encoding='utf-8', errors='replace').read()

    err_games = _split_games(errores_text)
    prt_games = _split_games(partidas_text)

    print(f'  Partidas en archivo de errores:  {len(err_games)}')
    print(f'  Partidas en archivo de partidas: {len(prt_games)}')

    # Build two indices of annotated games for fallback matching:
    #   1. by (white, black) — works when pairs are unique
    #   2. by move signature — more robust for repeated pairs
    err_by_pos = err_games  # primary: positional
    err_by_sig: dict = {}
    for g in err_games:
        sig = _moves_signature(g)
        if sig:
            err_by_sig.setdefault(sig, []).append(g)

    output_parts = []
    matched = 0
    unmatched = 0

    for idx, prt_game in enumerate(prt_games):
        prt_headers = _parse_headers(prt_game)
        prt_movetext = _get_movetext(prt_game)
        prt_white = prt_headers.get('White', '?')
        prt_black = prt_headers.get('Black', '?')

        error_comment = None
        err_candidate = None  # keep reference to merge Berserk headers if needed

        # ── Strategy 1: positional match ──────────────────────────────────
        if idx < len(err_by_pos):
            candidate = err_by_pos[idx]
            cand_h = _parse_headers(candidate)
            if (cand_h.get('White', '').lower() == prt_white.lower() and
                    cand_h.get('Black', '').lower() == prt_black.lower()):
                error_comment = _extract_error_comment(candidate)
                err_candidate = candidate

        # ── Strategy 2: move-signature fallback ───────────────────────────
        if error_comment is None:
            sig = _moves_signature(prt_game)
            if sig in err_by_sig:
                candidates = err_by_sig[sig]
                for cand in candidates:
                    ec = _extract_error_comment(cand)
                    if ec:
                        error_comment = ec
                        err_candidate = cand
                        break

        # ── Merge Berserk headers from annotated file when absent in clean ──
        if err_candidate is not None:
            cand_headers = _parse_headers(err_candidate)
            for tag in _BERSERK_TAGS:
                if tag not in prt_headers and tag in cand_headers:
                    prt_headers[tag] = cand_headers[tag]

        # ── Build error comment (annotation or fallback) ───────────────────
        if error_comment:
            matched += 1
        else:
            result_tag = prt_headers.get('Result', '*')
            has_moves = _has_moves(prt_movetext)
            error_comment = _fallback_error_comment(result_tag, has_moves)
            unmatched += 1
            reason = 'sin jugadas (abandono)' if not has_moves else 'sin anotación'
            print(
                f'  AVISO: tasa de error estimada para la partida '
                f'{idx + 1} ({prt_white} vs {prt_black}) [{reason}]',
                file=sys.stderr,
            )

        merged_movetext = _add_error_to_movetext(prt_movetext, error_comment)
        output_parts.append(_headers_text(prt_headers) + '\n\n' + merged_movetext)

    result_text = '\n\n\n'.join(output_parts) + '\n'
    os.makedirs(os.path.dirname(os.path.abspath(salida_path)), exist_ok=True)
    with open(salida_path, 'w', encoding='utf-8') as f:
        f.write(result_text)

    print(f'  Con tasa de error anotada:  {matched}')
    print(f'  Con tasa de error estimada: {unmatched}')
    print(f'  Archivo generado:           {salida_path}')
    return len(prt_games)


# ── GUI ───────────────────────────────────────────────────────────────────────

def _browse_pgn(title: str, var: tk.StringVar) -> None:
    path = filedialog.askopenfilename(
        title=title,
        filetypes=[
            ('PGN / TXT', '*.pgn *.txt'),
            ('PGN files', '*.pgn'),
            ('Text files', '*.txt'),
        ],
    )
    if path:
        var.set(path)


def show_input_dialog() -> argparse.Namespace:
    """Show a GUI dialog to collect parameters. Returns an argparse.Namespace."""

    result: dict = {}

    root = tk.Tk()
    root.title('Unificar PGN — Parámetros de entrada')
    root.resizable(False, False)

    pad = {'padx': 8, 'pady': 4}

    # ── File 1: annotated PGN (with error rates) ──────────────────────────
    tk.Label(root, text='Archivo con tasas de error *:', anchor='w').grid(
        row=0, column=0, sticky='w', **pad)
    errores_var = tk.StringVar()
    tk.Entry(root, textvariable=errores_var, width=55).grid(row=0, column=1, **pad)
    tk.Button(
        root, text='Examinar…',
        command=lambda: _browse_pgn('Seleccionar archivo con tasas de error', errores_var),
    ).grid(row=0, column=2, **pad)

    # ── File 2: clean PGN (moves without comments) ────────────────────────
    tk.Label(root, text='Archivo con partidas (sin comentarios) *:', anchor='w').grid(
        row=1, column=0, sticky='w', **pad)
    partidas_var = tk.StringVar()
    tk.Entry(root, textvariable=partidas_var, width=55).grid(row=1, column=1, **pad)
    tk.Button(
        root, text='Examinar…',
        command=lambda: _browse_pgn('Seleccionar archivo con partidas', partidas_var),
    ).grid(row=1, column=2, **pad)

    # ── Output file ───────────────────────────────────────────────────────
    tk.Label(root, text='Archivo de salida *:', anchor='w').grid(
        row=2, column=0, sticky='w', **pad)
    salida_var = tk.StringVar()
    tk.Entry(root, textvariable=salida_var, width=55).grid(row=2, column=1, **pad)

    def browse_salida():
        path = filedialog.asksaveasfilename(
            title='Guardar archivo PGN unificado',
            defaultextension='.pgn',
            filetypes=[('PGN files', '*.pgn'), ('Text files', '*.txt')],
        )
        if path:
            salida_var.set(path)

    tk.Button(root, text='Guardar como…', command=browse_salida).grid(
        row=2, column=2, **pad)

    # ── Separator & buttons ───────────────────────────────────────────────
    ttk.Separator(root, orient='horizontal').grid(
        row=3, column=0, columnspan=3, sticky='ew', pady=6)

    def on_ok():
        errores = errores_var.get().strip()
        partidas = partidas_var.get().strip()
        salida = salida_var.get().strip()

        if not errores or not partidas or not salida:
            messagebox.showerror('Error', 'Todos los campos son obligatorios.')
            return

        for label, path in [('tasas de error', errores), ('partidas', partidas)]:
            ext = os.path.splitext(path)[1].lower()
            if ext not in _ALLOWED_EXT:
                messagebox.showerror(
                    'Error',
                    f'El archivo de {label} debe tener extensión .pgn o .txt.\n'
                    f'Archivo indicado: {path}',
                )
                return
            if not os.path.exists(path):
                messagebox.showerror('Error', f'Archivo no encontrado:\n{path}')
                return

        result['errores'] = errores
        result['partidas'] = partidas
        result['salida'] = salida
        root.destroy()

    def on_cancel():
        root.destroy()

    btn_frame = tk.Frame(root)
    btn_frame.grid(row=4, column=0, columnspan=3, pady=6)
    tk.Button(btn_frame, text='Unificar', width=14, command=on_ok).pack(
        side='left', padx=6)
    tk.Button(btn_frame, text='Cancelar', width=14, command=on_cancel).pack(
        side='left', padx=6)

    root.mainloop()

    if not result:
        print('Operación cancelada por el usuario.', file=sys.stderr)
        sys.exit(0)

    return argparse.Namespace(
        errores=result['errores'],
        partidas=result['partidas'],
        salida=result['salida'],
    )


# ── CLI ───────────────────────────────────────────────────────────────────────

def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            'Unifica dos archivos PGN: uno con tasas de error (anotado) y otro '
            'con los movimientos limpios (sin comentarios). '
            'Genera un único PGN con los movimientos limpios más la tasa de error '
            'al final de cada partida.'
        )
    )
    parser.add_argument(
        '--errores',
        required=True,
        metavar='FICHERO',
        help='Archivo PGN/TXT con tasas de error (partidas anotadas)',
    )
    parser.add_argument(
        '--partidas',
        required=True,
        metavar='FICHERO',
        help='Archivo PGN/TXT con los movimientos limpios (sin comentarios)',
    )
    parser.add_argument(
        '--salida',
        required=True,
        metavar='FICHERO',
        help='Nombre del archivo PGN de salida',
    )
    return parser


# ── Entry point ───────────────────────────────────────────────────────────────

def main() -> None:
    if len(sys.argv) > 1:
        args = _build_parser().parse_args()
        # Validate extensions in CLI mode
        for label, path in [('errores', args.errores), ('partidas', args.partidas)]:
            ext = os.path.splitext(path)[1].lower()
            if ext not in _ALLOWED_EXT:
                print(
                    f'ERROR: El archivo de {label} debe tener extensión .pgn o .txt. '
                    f'Recibido: {path}',
                    file=sys.stderr,
                )
                sys.exit(1)
    else:
        args = show_input_dialog()

    print('Unificando archivos PGN…')
    try:
        n = unificar(
            errores_path=os.path.abspath(args.errores),
            partidas_path=os.path.abspath(args.partidas),
            salida_path=os.path.abspath(args.salida),
        )
    except (ValueError, FileNotFoundError) as exc:
        print(f'ERROR: {exc}', file=sys.stderr)
        sys.exit(1)

    print(f'\nListo! {n} partidas escritas en "{args.salida}".')


if __name__ == '__main__':
    main()

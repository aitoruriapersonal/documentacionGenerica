#!/usr/bin/env python3
"""
generarDossierTorneoCompleto.py — Programa unificado para generar el dossier completo
de un torneo Lichess Arena.

Combina los dos pasos en uno:
  1. Unificar dos archivos PGN (tasas de error + movimientos limpios) → PGN unificado.
  2. Generar la documentación HTML/Markdown/PDF del torneo a partir del PGN unificado.

Uso por consola:
    python3 generarDossierTorneoCompleto.py
        --errores FICHERO_ERRORES
        --partidas FICHERO_PARTIDAS
        --salida-pgn FICHERO_PGN_UNIFICADO
        [--url URL_LICHESS]
        [--out DIRECTORIO_SALIDA]
        [--name NOMBRE_BASE]
        [--no-pdf]

Uso con ventana (sin argumentos):
    python3 generarDossierTorneoCompleto.py
"""

import argparse
import os
import sys
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

# ── Import logic from the two sub-programs ────────────────────────────────────

from unificarPgn import unificar as _unificar

from generar_documentos_torneo import (
    parse_pgn_file,
    compute_player_stats,
    compute_global_stats,
    generate_html_completo,
    generate_html_final,
    generate_markdown,
    generate_pdf,
    extract_tournament_id,
    fetch_lichess_data,
)

# ── Allowed extensions ────────────────────────────────────────────────────────

_ALLOWED_EXT = ('.pgn', '.txt')


def _allowed(path: str) -> bool:
    return os.path.splitext(path)[1].lower() in _ALLOWED_EXT


# ── Combined GUI ──────────────────────────────────────────────────────────────

def show_input_dialog() -> argparse.Namespace:
    """Show a combined GUI dialog for all parameters. Returns argparse.Namespace."""

    result: dict = {}

    root = tk.Tk()
    root.title('Dossier Torneo Completo — Parámetros de entrada')
    root.resizable(False, False)

    pad = {'padx': 8, 'pady': 4}

    # ── Section 1: Unificar PGN ───────────────────────────────────────────────
    tk.Label(
        root,
        text='── Paso 1: Unificar PGN ──────────────────────────────',
        anchor='w', fg='#336699', font=('', 9, 'bold'),
    ).grid(row=0, column=0, columnspan=3, sticky='w', padx=8, pady=(10, 2))

    # File 1: annotated PGN with error rates
    tk.Label(root, text='Archivo con tasas de error *:', anchor='w').grid(
        row=1, column=0, sticky='w', **pad)
    errores_var = tk.StringVar()
    tk.Entry(root, textvariable=errores_var, width=55).grid(row=1, column=1, **pad)

    def _browse_pgn(title, var):
        path = filedialog.askopenfilename(
            title=title,
            filetypes=[('PGN / TXT', '*.pgn *.txt'), ('PGN files', '*.pgn'), ('Text files', '*.txt')],
        )
        if path:
            var.set(path)

    tk.Button(root, text='Examinar…',
              command=lambda: _browse_pgn('Archivo con tasas de error', errores_var)
              ).grid(row=1, column=2, **pad)

    # File 2: clean PGN without comments
    tk.Label(root, text='Archivo con partidas (sin comentarios) *:', anchor='w').grid(
        row=2, column=0, sticky='w', **pad)
    partidas_var = tk.StringVar()
    tk.Entry(root, textvariable=partidas_var, width=55).grid(row=2, column=1, **pad)
    tk.Button(root, text='Examinar…',
              command=lambda: _browse_pgn('Archivo con partidas (sin comentarios)', partidas_var)
              ).grid(row=2, column=2, **pad)

    # Output unified PGN
    tk.Label(root, text='Archivo PGN unificado (salida) *:', anchor='w').grid(
        row=3, column=0, sticky='w', **pad)
    salida_pgn_var = tk.StringVar()
    tk.Entry(root, textvariable=salida_pgn_var, width=55).grid(row=3, column=1, **pad)

    def _browse_salida_pgn():
        path = filedialog.asksaveasfilename(
            title='Guardar PGN unificado',
            defaultextension='.pgn',
            filetypes=[('PGN files', '*.pgn'), ('Text files', '*.txt')],
        )
        if path:
            salida_pgn_var.set(path)

    tk.Button(root, text='Guardar como…', command=_browse_salida_pgn).grid(
        row=3, column=2, **pad)

    ttk.Separator(root, orient='horizontal').grid(
        row=4, column=0, columnspan=3, sticky='ew', pady=4)

    # ── Section 2: Generar documentos torneo ──────────────────────────────────
    tk.Label(
        root,
        text='── Paso 2: Generar documentación del torneo ──────────',
        anchor='w', fg='#336699', font=('', 9, 'bold'),
    ).grid(row=5, column=0, columnspan=3, sticky='w', padx=8, pady=(6, 2))

    # Lichess URL
    tk.Label(root, text='URL Lichess (opcional):', anchor='w').grid(
        row=6, column=0, sticky='w', **pad)
    url_var = tk.StringVar()
    tk.Entry(root, textvariable=url_var, width=55).grid(row=6, column=1, **pad)

    # Output directory
    tk.Label(root, text='Directorio de salida (opcional):', anchor='w').grid(
        row=7, column=0, sticky='w', **pad)
    out_var = tk.StringVar()
    tk.Entry(root, textvariable=out_var, width=55).grid(row=7, column=1, **pad)

    def _browse_out():
        path = filedialog.askdirectory(title='Seleccionar directorio de salida')
        if path:
            out_var.set(path)

    tk.Button(root, text='Examinar…', command=_browse_out).grid(row=7, column=2, **pad)

    # Base name
    tk.Label(root, text='Nombre base (opcional):', anchor='w').grid(
        row=8, column=0, sticky='w', **pad)
    name_var = tk.StringVar()
    tk.Entry(root, textvariable=name_var, width=55).grid(row=8, column=1, **pad)

    # No PDF
    no_pdf_var = tk.BooleanVar(value=False)
    tk.Checkbutton(root, text='No generar PDF (--no-pdf)', variable=no_pdf_var).grid(
        row=9, column=1, sticky='w', **pad)

    # ── Buttons ───────────────────────────────────────────────────────────────
    ttk.Separator(root, orient='horizontal').grid(
        row=10, column=0, columnspan=3, sticky='ew', pady=6)

    def on_ok():
        errores = errores_var.get().strip()
        partidas = partidas_var.get().strip()
        salida_pgn = salida_pgn_var.get().strip()

        if not errores or not partidas or not salida_pgn:
            messagebox.showerror('Error', 'Los campos del Paso 1 son obligatorios.')
            return

        for label, path in [('tasas de error', errores), ('partidas', partidas)]:
            if not _allowed(path):
                messagebox.showerror(
                    'Error',
                    f'El archivo de {label} debe tener extensión .pgn o .txt.\nArchivo: {path}',
                )
                return
            if not os.path.exists(path):
                messagebox.showerror('Error', f'Archivo no encontrado:\n{path}')
                return

        result['errores'] = errores
        result['partidas'] = partidas
        result['salida_pgn'] = salida_pgn
        result['url'] = url_var.get().strip() or None
        result['out'] = out_var.get().strip() or None
        result['name'] = name_var.get().strip() or None
        result['no_pdf'] = no_pdf_var.get()
        root.destroy()

    def on_cancel():
        root.destroy()

    btn_frame = tk.Frame(root)
    btn_frame.grid(row=11, column=0, columnspan=3, pady=6)
    tk.Button(btn_frame, text='Generar Dossier', width=18, command=on_ok).pack(
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
        salida_pgn=result['salida_pgn'],
        url=result['url'],
        out=result['out'],
        name=result['name'],
        no_pdf=result['no_pdf'],
    )


# ── CLI parser ────────────────────────────────────────────────────────────────

def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            'Genera el dossier completo de un torneo Lichess Arena en dos pasos:\n'
            '  1. Unifica dos archivos PGN (tasas de error + movimientos limpios).\n'
            '  2. Genera la documentación HTML/Markdown/PDF del torneo.'
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    # Step 1 params
    parser.add_argument(
        '--errores', required=True, metavar='FICHERO',
        help='Archivo PGN/TXT con tasas de error (partidas anotadas)',
    )
    parser.add_argument(
        '--partidas', required=True, metavar='FICHERO',
        help='Archivo PGN/TXT con los movimientos limpios (sin comentarios)',
    )
    parser.add_argument(
        '--salida-pgn', required=True, metavar='FICHERO', dest='salida_pgn',
        help='Archivo PGN de salida del paso 1 (entrada del paso 2)',
    )
    # Step 2 params
    parser.add_argument(
        '--url', default=None,
        help='URL del torneo en Lichess (opcional)',
    )
    parser.add_argument(
        '--out', default=None,
        help='Directorio de salida para los documentos generados',
    )
    parser.add_argument(
        '--name', default=None,
        help='Nombre base para los archivos de salida',
    )
    parser.add_argument(
        '--no-pdf', action='store_true',
        help='Omitir la generación del PDF',
    )
    return parser


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    if len(sys.argv) > 1:
        args = _build_parser().parse_args()
        # Validate extensions in CLI mode
        for label, path in [('errores', args.errores), ('partidas', args.partidas)]:
            if not _allowed(path):
                print(
                    f'ERROR: El archivo de {label} debe tener extensión .pgn o .txt. '
                    f'Recibido: {path}',
                    file=sys.stderr,
                )
                sys.exit(1)
            if not os.path.exists(path):
                print(f'ERROR: Archivo no encontrado: {path}', file=sys.stderr)
                sys.exit(1)
    else:
        args = show_input_dialog()

    # ── Paso 1: Unificar PGN ─────────────────────────────────────────────────
    print('=' * 60)
    print('PASO 1: Unificando archivos PGN…')
    print('=' * 60)
    try:
        n = _unificar(
            errores_path=os.path.abspath(args.errores),
            partidas_path=os.path.abspath(args.partidas),
            salida_path=os.path.abspath(args.salida_pgn),
        )
    except (ValueError, FileNotFoundError) as exc:
        print(f'ERROR en Paso 1: {exc}', file=sys.stderr)
        sys.exit(1)
    print(f'Paso 1 completado: {n} partidas escritas en "{args.salida_pgn}".\n')

    # ── Paso 2: Generar documentación ────────────────────────────────────────
    print('=' * 60)
    print('PASO 2: Generando documentación del torneo…')
    print('=' * 60)

    pgn_path = os.path.abspath(args.salida_pgn)
    pgn_ext = os.path.splitext(pgn_path)[1].lower()
    if pgn_ext not in _ALLOWED_EXT:
        print(
            f'ERROR: El archivo PGN unificado debe tener extensión .pgn o .txt. '
            f'Recibido: {pgn_path}',
            file=sys.stderr,
        )
        sys.exit(1)
    if not os.path.exists(pgn_path):
        print(f'ERROR: Archivo PGN no encontrado: {pgn_path}', file=sys.stderr)
        sys.exit(1)

    pgn_dir = os.path.dirname(pgn_path)
    pgn_base = os.path.splitext(os.path.basename(pgn_path))[0]

    out_dir = os.path.abspath(args.out) if args.out else pgn_dir
    os.makedirs(out_dir, exist_ok=True)

    base_name = args.name or pgn_base

    print(f'Procesando PGN: {pgn_path}')
    games = parse_pgn_file(pgn_path)
    if not games:
        print('ERROR: No se encontraron partidas en el PGN.', file=sys.stderr)
        sys.exit(1)
    print(f'Partidas encontradas: {len(games)}')

    # Fetch Lichess API data (optional)
    api_data = None
    if args.url:
        tid = extract_tournament_id(args.url)
        if tid:
            print(f'Obteniendo datos de Lichess para el torneo: {tid}')
            api_data = fetch_lichess_data(tid)
        else:
            print(
                f'AVISO: No se pudo extraer el ID del torneo de la URL: {args.url}',
                file=sys.stderr,
            )

    players, players_sorted, warnings = compute_player_stats(games, api_data)
    global_stats = compute_global_stats(games, players)

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

    completo_path = os.path.join(out_dir, f'{base_name}_completo.html')
    final_path = os.path.join(out_dir, f'{base_name}_final.html')
    stats_path = os.path.join(out_dir, f'{base_name}_estadisticas.md')
    pdf_path = os.path.join(out_dir, f'{base_name}.pdf')

    generate_html_completo(games, players_sorted, global_stats,
                           tournament_info, warnings, completo_path)
    generate_html_final(games, players_sorted, global_stats,
                        tournament_info, warnings, final_path)
    generate_markdown(games, players_sorted, global_stats,
                      tournament_info, warnings, stats_path)

    if not args.no_pdf:
        generate_pdf(final_path, pdf_path)

    print('\n¡Dossier generado con éxito!')


if __name__ == '__main__':
    main()

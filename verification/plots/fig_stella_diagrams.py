#!/usr/bin/env python3
"""
Stella Diagrams: A Diagrammatic Language for Interactions on dS
===============================================================

Defines visual "Feynman rules" for the stella octangula, where:
- Vertices = color charges (R,G,B on T+; Rbar,Gbar,Bbar on T-)
- Directed edges = phase evolution (each carrying omega = e^{2pi i/3})
- Closed loops = color-neutral physical states (confinement)
- Chirality = rotation direction (R->G->B fixed by <Q> > 0)

Physics references:
  Def 0.1.2   -- Color field phases {0, 2pi/3, 4pi/3}
  Thm 0.2.1   -- Total field superposition
  Thm 1.1.1   -- SU(3) <-> Stella isomorphism
  Thm 1.1.2   -- Charge conjugation as point reflection
  Thm 2.2.1   -- Phase-locked oscillation
  Thm 2.2.2   -- Limit cycle (R->G->B)
  Thm 2.2.4   -- Anomaly-driven chirality selection
  Prop 2.5.2a  -- Wilson loop area law

Output: verification/plots/fig_stella_diagrams.{png,pdf}
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import os

# ---------------------------------------------------------------------------
# Path setup
# ---------------------------------------------------------------------------
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PLOT_DIR = os.path.join(SCRIPT_DIR, "plots")
os.makedirs(PLOT_DIR, exist_ok=True)

# ---------------------------------------------------------------------------
# rcParams
# ---------------------------------------------------------------------------
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# ---------------------------------------------------------------------------
# Color palette
# ---------------------------------------------------------------------------
CLR = {
    'R':     '#D03030',
    'G':     '#209020',
    'B':     '#2050D0',
    'Rb':    '#00AAAA',   # anti-red (cyan)
    'Gb':    '#AA00AA',   # anti-green (magenta)
    'Bb':    '#AAAA00',   # anti-blue (yellow)
    'edge':  '#BBBBBB',
    'conj':  '#999999',
    'forbid': '#CC2222',
    'singlet': '#555555',
    'gluon':  '#FF8C00',  # dark orange for gluon/adjoint
    'wilson': '#7B2D8E',  # purple for Wilson loops
    'ok':     '#228B22',  # green checkmark
}

# ---------------------------------------------------------------------------
# Vertex layout: Star of David projection
# T+ = upward equilateral triangle; T- = downward
# ---------------------------------------------------------------------------
R_TRI = 0.85


def _tri_verts(r, up=True):
    """Equilateral triangle vertices."""
    base = np.pi / 2 if up else -np.pi / 2
    return np.array([[r * np.cos(base + i * 2 * np.pi / 3),
                       r * np.sin(base + i * 2 * np.pi / 3)]
                      for i in range(3)])


VP = _tri_verts(R_TRI, up=True)    # R(top), G(bot-left), B(bot-right)
VM = _tri_verts(R_TRI, up=False)   # Rb(bot), Gb(top-right), Bb(top-left)

VERT = {
    'R': VP[0], 'G': VP[1], 'B': VP[2],
    'Rb': VM[0], 'Gb': VM[1], 'Bb': VM[2],
}

# Display labels
LABELS = {
    'R': 'R', 'G': 'G', 'B': 'B',
    'Rb': r'$\bar{R}$', 'Gb': r'$\bar{G}$', 'Bb': r'$\bar{B}$',
}


# ===========================================================================
# Drawing helpers
# ===========================================================================

def draw_graph(ax, show_labels=True, alpha_e=0.25, show_conj=False,
               vert_size=300, dim_set=None, label_offset=0.20):
    """Draw the stella graph skeleton.

    dim_set: optional set of vertex keys to draw dimmed (smaller, faded).
    """
    dim_set = dim_set or set()

    # Edges within each tetrahedron
    for verts, col in [(VP, CLR['edge']), (VM, CLR['edge'])]:
        for i in range(3):
            j = (i + 1) % 3
            ax.plot([verts[i, 0], verts[j, 0]],
                    [verts[i, 1], verts[j, 1]],
                    '-', color=col, lw=1.5, alpha=alpha_e, zorder=1)

    # Conjugation dashes
    if show_conj:
        for p, m in [('R', 'Rb'), ('G', 'Gb'), ('B', 'Bb')]:
            ax.plot([VERT[p][0], VERT[m][0]],
                    [VERT[p][1], VERT[m][1]],
                    ':', color=CLR['conj'], lw=1.2, alpha=0.5, zorder=0)

    # Vertices
    for key in VERT:
        pos = VERT[key]
        dim = key in dim_set
        sz = vert_size * (0.5 if dim else 1.0)
        al = 0.35 if dim else 1.0
        ax.scatter(*pos, c=CLR[key], s=sz, zorder=5,
                   edgecolors='white', linewidths=1.5, alpha=al)
        if show_labels:
            d = pos / (np.linalg.norm(pos) + 1e-10)
            off = d * label_offset
            ax.text(pos[0] + off[0], pos[1] + off[1], LABELS[key],
                    fontsize=11, fontweight='bold', ha='center', va='center',
                    color=CLR[key], alpha=al, zorder=6)

    ax.set_xlim(-1.35, 1.35)
    ax.set_ylim(-1.35, 1.35)
    ax.set_aspect('equal')
    ax.axis('off')


def arrow(ax, start, end, color='black', lw=2.5, rad=0.0,
          shrink=0.14, zorder=4, alpha=1.0, ls='-'):
    """Curved directed arrow between two points."""
    d = end - start
    length = np.linalg.norm(d)
    u = d / length
    p0 = start + shrink * u
    p1 = end - shrink * u
    style = f'arc3,rad={rad}'
    ax.annotate('', xy=p1, xytext=p0,
                arrowprops=dict(arrowstyle='->,head_width=0.12,head_length=0.14',
                                color=color, lw=lw,
                                connectionstyle=style,
                                alpha=alpha, linestyle=ls),
                zorder=zorder)


def edge_label(ax, start, end, text, color='black', rad=0.0,
               offset=0.14, fontsize=9):
    """Place a label along an edge."""
    d = end - start
    u = d / np.linalg.norm(d)
    mid = (start + end) / 2
    perp = np.array([-u[1], u[0]])
    sign = 1 if rad >= 0 else -1
    pos = mid + (offset * sign + abs(rad) * 0.3) * perp
    ax.text(*pos, text, fontsize=fontsize, ha='center', va='center',
            color=color, fontstyle='italic', zorder=5)


def wavy_line(ax, start, end, color='black', lw=2, n_waves=6,
              amplitude=0.06, shrink=0.14, zorder=3):
    """Draw a wavy/coiled line (gluon propagator style)."""
    d = end - start
    length = np.linalg.norm(d)
    u = d / length
    perp = np.array([-u[1], u[0]])

    p0 = start + shrink * u
    p1 = end - shrink * u
    seg = p1 - p0
    seg_len = np.linalg.norm(seg)

    ts = np.linspace(0, 1, 200)
    wave = amplitude * np.sin(2 * np.pi * n_waves * ts)
    xs = p0[0] + seg[0] * ts + perp[0] * wave
    ys = p0[1] + seg[1] * ts + perp[1] * wave
    ax.plot(xs, ys, '-', color=color, lw=lw, zorder=zorder)

    # Arrowhead at 75% along
    idx = 150
    dx, dy = xs[idx+1] - xs[idx-1], ys[idx+1] - ys[idx-1]
    ax.annotate('', xy=(xs[idx+2], ys[idx+2]),
                xytext=(xs[idx-2], ys[idx-2]),
                arrowprops=dict(arrowstyle='->,head_width=0.10,head_length=0.12',
                                color=color, lw=0),
                zorder=zorder+1)


def draw_chirality_arc(ax, cx, cy, r, start_deg, end_deg, color='#444444',
                       lw=1.5, zorder=3):
    """Draw a curved arrow arc (chirality indicator)."""
    theta = np.linspace(np.deg2rad(start_deg), np.deg2rad(end_deg), 60)
    ax.plot(cx + r * np.cos(theta), cy + r * np.sin(theta),
            '-', color=color, lw=lw, zorder=zorder)
    t_end = theta[-1]
    ax.annotate('', xy=(cx + r * np.cos(t_end),
                        cy + r * np.sin(t_end)),
                xytext=(cx + r * np.cos(theta[-4]),
                        cy + r * np.sin(theta[-4])),
                arrowprops=dict(arrowstyle='->', color=color, lw=lw),
                zorder=zorder)


# ===========================================================================
# Panels
# ===========================================================================

def panel_graph(ax):
    """(a) Full stella graph with conjugation lines."""
    draw_graph(ax, show_conj=True)

    ax.text(0, 0.42, r'$T_+$', fontsize=14, fontweight='bold',
            ha='center', va='center', color='#666666')
    ax.text(0, -0.42, r'$T_-$', fontsize=14, fontweight='bold',
            ha='center', va='center', color='#666666')

    ax.set_title(r'(a) Stella graph $\partial\mathcal{S}$',
                 fontsize=12, fontweight='bold', pad=10)


def panel_cycle(ax):
    """(b) R->G->B->R color cycle with phase labels."""
    draw_graph(ax, show_conj=False, alpha_e=0.12,
               dim_set={'Rb', 'Gb', 'Bb'})

    cycle = ['R', 'G', 'B']
    for i in range(3):
        j = (i + 1) % 3
        s, e = VERT[cycle[i]], VERT[cycle[j]]
        arrow(ax, s, e, color=CLR[cycle[i]], lw=3, rad=0.15)
        edge_label(ax, s, e, r'$\omega$', color=CLR[cycle[i]], rad=0.15)

    draw_chirality_arc(ax, 0, 0, 0.16, 30, 300)

    ax.set_title(r'(b) Color cycle $R \to G \to B \to R$',
                 fontsize=12, fontweight='bold', pad=10)
    ax.text(0, -1.22, r'$\omega = e^{2\pi i/3}$  |  one cycle = one $\lambda$-period',
            fontsize=9, ha='center', color='#555555')


def panel_chirality(ax):
    """(c) Chirality selection: R->G->B allowed, R->B->G suppressed."""
    draw_graph(ax, show_conj=False, alpha_e=0.08,
               dim_set={'Rb', 'Gb', 'Bb'}, vert_size=250)

    cycle_fwd = ['R', 'G', 'B']   # R->G->B (right-handed, allowed)
    cycle_rev = ['R', 'B', 'G']   # R->B->G (left-handed, suppressed)

    # Draw reverse (suppressed) cycle FIRST — dashed, faded, larger arc
    for i in range(3):
        j = (i + 1) % 3
        s, e = VERT[cycle_rev[i]], VERT[cycle_rev[j]]
        arrow(ax, s, e, color=CLR['forbid'], lw=2.0, rad=-0.40,
              alpha=0.35, zorder=3, ls='--')

    # Draw forward (allowed) cycle — solid, bold, tight arc
    for i in range(3):
        j = (i + 1) % 3
        s, e = VERT[cycle_fwd[i]], VERT[cycle_fwd[j]]
        arrow(ax, s, e, color=CLR[cycle_fwd[i]], lw=3.5, rad=0.18, zorder=5)

    # Checkmark and X with background boxes for readability
    ax.text(-0.62, 0.12, r'$\checkmark$', fontsize=24, fontweight='bold',
            ha='center', va='center', color=CLR['ok'], zorder=7,
            bbox=dict(boxstyle='round,pad=0.1', facecolor='white',
                      edgecolor='none', alpha=0.8))
    ax.text(0.62, 0.12, r'$\times$', fontsize=24, fontweight='bold',
            ha='center', va='center', color=CLR['forbid'], zorder=7,
            bbox=dict(boxstyle='round,pad=0.1', facecolor='white',
                      edgecolor='none', alpha=0.8))

    # Labels below symbols
    ax.text(-0.62, -0.15, r'$R{\to}G{\to}B$', fontsize=10,
            ha='center', va='center', color=CLR['ok'], fontweight='bold')
    ax.text(0.62, -0.15, r'$R{\to}B{\to}G$', fontsize=10,
            ha='center', va='center', color=CLR['forbid'], alpha=0.6)

    ax.set_title(r'(c) Chirality: $\langle Q \rangle > 0$ selects direction',
                 fontsize=12, fontweight='bold', pad=10)
    ax.text(0, -1.22,
            r'Thm 2.2.4: instanton bias fixes $R \to G \to B$',
            fontsize=9, ha='center', color='#555555')


def panel_meson(ax):
    """(d) Meson: quark-antiquark pair connected through center."""
    draw_graph(ax, show_conj=False, alpha_e=0.12,
               dim_set={'G', 'B', 'Gb', 'Bb'})

    # R -> Rb (quark to antiquark)
    arrow(ax, VERT['R'], VERT['Rb'], color=CLR['R'], lw=3, rad=0.0)

    # Label
    ax.text(0.25, 0.05, r'$q_R \bar{q}_{\bar{R}}$', fontsize=12,
            fontweight='bold', ha='center', va='center', color='#333333',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='white',
                      edgecolor='#AAAAAA', alpha=0.9), zorder=6)

    ax.text(0, -1.22,
            r'Color-neutral: $\omega^0 \cdot (\omega^0)^* = 1$',
            fontsize=9, ha='center', color='#555555')

    ax.set_title(r'(d) Meson: $q_c \bar{q}_{\bar{c}}$',
                 fontsize=12, fontweight='bold', pad=10)


def panel_baryon(ax):
    """(e) Baryon: R + G + B meeting at color singlet."""
    draw_graph(ax, show_conj=False, alpha_e=0.12,
               dim_set={'Rb', 'Gb', 'Bb'})

    center = np.array([0.0, 0.0])

    for name in ['R', 'G', 'B']:
        arrow(ax, VERT[name], center, color=CLR[name], lw=3, shrink=0.10)

    # Singlet marker
    ax.scatter(*center, c='white', s=180, zorder=6,
               edgecolors='black', linewidths=2)
    ax.text(0.0, 0.0, r'$\mathbf{1}$', fontsize=11, fontweight='bold',
            ha='center', va='center', color=CLR['singlet'], zorder=7)

    ax.set_title(r'(e) Baryon: $R + G + B \to \mathbf{1}$',
                 fontsize=12, fontweight='bold', pad=10)
    ax.text(0, -1.22,
            r'$\omega^0 + \omega^1 + \omega^2 = 0$  (color singlet)',
            fontsize=9, ha='center', color='#555555')


def panel_wilson(ax):
    """(f) Wilson loop: closed triangular path on one face of T+."""
    draw_graph(ax, show_conj=False, alpha_e=0.10,
               dim_set={'Rb', 'Gb', 'Bb'}, vert_size=250)

    # Draw the Wilson loop as a filled triangular path on T+ face
    # with thick purple arrows tracing the boundary
    tri = np.vstack([VP, VP[0]])  # close the triangle

    # Filled triangle (very light purple)
    from matplotlib.patches import Polygon
    face = Polygon(VP, closed=True, facecolor=CLR['wilson'],
                   alpha=0.08, edgecolor='none', zorder=2)
    ax.add_patch(face)

    # Directed edges around the face
    cycle = ['R', 'G', 'B']
    for i in range(3):
        j = (i + 1) % 3
        s, e = VERT[cycle[i]], VERT[cycle[j]]
        arrow(ax, s, e, color=CLR['wilson'], lw=3.0, rad=0.08, zorder=4)

    # Area label inside triangle
    ax.text(0, 0.0, r'$A$', fontsize=16, fontweight='bold',
            ha='center', va='center', color=CLR['wilson'], alpha=0.6,
            zorder=3)

    # Wilson loop formula
    ax.text(0, -1.22,
            r'$W(\triangle) = \mathrm{tr}\,\mathcal{P}\exp\!\oint A_\mu dx^\mu'
            r' \sim e^{-\sigma A}$',
            fontsize=9, ha='center', color='#555555')

    ax.set_title(r'(f) Wilson loop on $T_+$ face',
                 fontsize=12, fontweight='bold', pad=10)


def panel_gluon(ax):
    """(g) Gluon exchange: color rotation via adjoint representation."""
    draw_graph(ax, show_conj=False, alpha_e=0.10,
               dim_set={'Rb', 'Gb', 'Bb'}, vert_size=250)

    # Gluon exchange: R emits gluon, becomes G; G absorbs, becomes R
    # Show as: R vertex -> wavy line -> G vertex, with color flow arrows

    # Wavy gluon propagator between R and G
    wavy_line(ax, VERT['R'], VERT['G'], color=CLR['gluon'], lw=2.5,
              n_waves=5, amplitude=0.07, shrink=0.16)

    # Color flow indicators (small arrows near vertices)
    # R becomes G (at R vertex, small arrow showing color change)
    r_pos = VERT['R']
    g_pos = VERT['G']
    mid = (r_pos + g_pos) / 2

    # Label the gluon
    d = g_pos - r_pos
    u = d / np.linalg.norm(d)
    perp = np.array([-u[1], u[0]])
    label_pos = mid + 0.20 * perp
    ax.text(*label_pos, r'$g_{RG}$', fontsize=11, fontweight='bold',
            ha='center', va='center', color=CLR['gluon'],
            bbox=dict(boxstyle='round,pad=0.2', facecolor='white',
                      edgecolor=CLR['gluon'], alpha=0.9), zorder=6)

    # Show color transformation at each vertex with boxed labels
    ax.text(r_pos[0] + 0.12, r_pos[1] - 0.28, r'$R \!\to\! G$',
            fontsize=9, ha='center', color=CLR['R'], fontweight='bold',
            bbox=dict(boxstyle='round,pad=0.15', facecolor='white',
                      edgecolor=CLR['R'], alpha=0.85, lw=0.8))
    ax.text(g_pos[0] + 0.32, g_pos[1] + 0.10, r'$G \!\to\! R$',
            fontsize=9, ha='center', color=CLR['G'], fontweight='bold',
            bbox=dict(boxstyle='round,pad=0.15', facecolor='white',
                      edgecolor=CLR['G'], alpha=0.85, lw=0.8))

    ax.set_title(r'(g) Gluon: adjoint $\mathbf{8}$ exchange',
                 fontsize=12, fontweight='bold', pad=10)
    ax.text(0, -1.22,
            r'$g_{cc\prime} \in \mathbf{8}$: edge = color rotation on $\partial\mathcal{S}$',
            fontsize=9, ha='center', color='#555555')


def panel_forbidden(ax):
    """(h) Forbidden open path: not color-neutral."""
    draw_graph(ax, show_conj=False, alpha_e=0.12,
               dim_set={'Rb', 'Gb', 'Bb', 'B'})

    arrow(ax, VERT['R'], VERT['G'], color=CLR['forbid'], lw=3, rad=0.0)

    # Red X
    for sign in [(1, 1), (1, -1)]:
        ax.plot([-0.5 * sign[0], 0.5 * sign[0]],
                [-0.5 * sign[1], 0.5 * sign[1]],
                '-', color=CLR['forbid'], lw=5, alpha=0.25, zorder=7)

    ax.set_title(r'(h) Forbidden: open $R \to G$',
                 fontsize=12, fontweight='bold', pad=10)
    ax.text(0, -1.22, r'Net color charge $\neq 0$ $\Rightarrow$ confined',
            fontsize=9, ha='center', color=CLR['forbid'])


def panel_rules(ax):
    """(i) Stella diagram rules summary."""
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')
    ax.set_title('(i) Stella diagram rules', fontsize=12, fontweight='bold',
                 pad=10)

    rows = [
        ('Element',          'Symbol',                        'Rule / Physics'),
        ('Color vertex',     r'$\bullet_c$',                  r'$c \in \{R,G,B,\bar{R},\bar{G},\bar{B}\}$'),
        ('Directed edge',    r'$c_1 \to c_2$',                r'Phase factor $\omega^{\Delta c}$'),
        ('Wavy line',        r'$\sim\!\sim$',                  r'Gluon ($\mathbf{8}$): color rotation'),
        ('Closed loop',      r'$\circlearrowleft$',            'Color-neutral (physical)'),
        ('Open path',        r'$c_1 \to c_2$',                'Confined (unphysical)'),
        ('Chirality',        r'$R{\to}G{\to}B$',              r'Fixed by $\langle Q \rangle > 0$'),
        ('Conjugation',      r'$c \leftrightarrow \bar{c}$',   r'$T_+ \leftrightarrow T_-$ (reflection)'),
        ('Wilson loop',      r'$\triangle$ on face',           r'Area law $W \sim e^{-\sigma A}$'),
        ('Face area',        r'$A$',                           r'$\propto R_{\mathrm{stella}}^2$'),
    ]

    y0, dy = 0.95, 0.09
    cols = [0.01, 0.27, 0.52]

    for i, (c1, c2, c3) in enumerate(rows):
        y = y0 - i * dy
        w = 'bold' if i == 0 else 'normal'
        s = 10 if i == 0 else 8.5
        ax.text(cols[0], y, c1, fontsize=s, fontweight=w,
                va='center', ha='left')
        ax.text(cols[1], y, c2, fontsize=s, fontweight=w,
                va='center', ha='left')
        ax.text(cols[2], y, c3, fontsize=s, fontweight=w,
                va='center', ha='left')

    ax.plot([0.01, 0.99], [y0 - 0.5 * dy] * 2, '-', color='gray', lw=0.5)

    ax.text(0.01, 0.03,
            'Refs: Def 0.1.2, Thm 0.2.1, 1.1.1\u20132, 2.2.1\u20134, Prop 2.5.2a',
            fontsize=7.5, color='#777777', va='center')


# ===========================================================================
# Main
# ===========================================================================

def main():
    fig = plt.figure(figsize=(18, 18), facecolor='white')
    gs = GridSpec(3, 3, figure=fig, hspace=0.30, wspace=0.20)

    axes = [fig.add_subplot(gs[r, c]) for r in range(3) for c in range(3)]

    # Row 1: Foundations
    panel_graph(axes[0])        # (a) Stella graph
    panel_cycle(axes[1])        # (b) Color cycle
    panel_chirality(axes[2])    # (c) Chirality selection

    # Row 2: Physical states
    panel_meson(axes[3])        # (d) Meson
    panel_baryon(axes[4])       # (e) Baryon
    panel_wilson(axes[5])       # (f) Wilson loop

    # Row 3: Interactions & constraints
    panel_gluon(axes[6])        # (g) Gluon exchange
    panel_forbidden(axes[7])    # (h) Forbidden
    panel_rules(axes[8])        # (i) Rules table

    fig.suptitle(
        r'Stella Diagrams: Interactions on $\partial\mathcal{S}$',
        fontsize=16, fontweight='bold', y=0.99)

    base = os.path.join(PLOT_DIR, "fig_stella_diagrams")
    fig.savefig(base + ".png", dpi=300, bbox_inches='tight', facecolor='white')
    fig.savefig(base + ".pdf", bbox_inches='tight', facecolor='white')
    print(f"Saved: {base}.png")
    print(f"Saved: {base}.pdf")
    plt.close('all')


if __name__ == "__main__":
    main()

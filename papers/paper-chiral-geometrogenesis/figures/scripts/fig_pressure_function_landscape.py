#!/usr/bin/env python3
"""
Figure: Pressure Function Landscape (Definition 0.1.4 / Section 9.3)

Two-panel visualization of the pressure functions P_c(x) on the stella octangula:
(a) 2D heatmap of total pressure on z=0 slice with Voronoi domain boundaries
(b) 1D profile along the path from v_R to -v_R showing all three pressure functions

Key physics:
- P_c(x) = 1/(|x - v_c|^2 + eps^2) models the pressure source at each T+ vertex
- Voronoi domains emerge naturally as regions where one color dominates
- Cross-over points between domains define the pressure-depression boundaries

Proof Document: docs/proofs/Phase0/Definition-0.1.4-Color-Field-Domains.md
Paper Section: Section 9.3 (Pressure Function Landscape)
Output: fig_pressure_function_landscape.pdf, fig_pressure_function_landscape.png
"""

import numpy as np
import matplotlib.pyplot as plt
import os

# Paths
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style
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

# Colors (no purple)
CC = {
    'R': (0.91, 0.15, 0.15),
    'G': (0.15, 0.68, 0.15),
    'B': (0.20, 0.40, 0.86),
    'W': (0.55, 0.55, 0.55),
}

# Geometry: T+ vertices (normalized)
s3 = np.sqrt(3)
V = {
    'R': np.array([ 1, -1, -1]) / s3,
    'G': np.array([-1,  1, -1]) / s3,
    'B': np.array([-1, -1,  1]) / s3,
    'W': np.array([ 1,  1,  1]) / s3,
}

EPS = 0.05  # Regularization parameter


def pressure(x, y, z, v, eps=EPS):
    """Pressure function P_c(x) = 1/(|x - v_c|^2 + eps^2)."""
    return 1.0 / ((x - v[0])**2 + (y - v[1])**2 + (z - v[2])**2 + eps**2)


def main():
    fig, axes = plt.subplots(1, 2, figsize=(12, 5.5),
                             gridspec_kw={'width_ratios': [1.1, 1]})

    # ==============================================================
    # (a) Pressure Landscape: z=0 slice
    # ==============================================================
    ax = axes[0]

    N = 300
    x = np.linspace(-1.0, 1.0, N)
    y = np.linspace(-1.0, 1.0, N)
    X, Y = np.meshgrid(x, y)
    z_slice = 0.0

    # Compute individual pressures
    P = {}
    for c in ['R', 'G', 'B', 'W']:
        P[c] = pressure(X, Y, z_slice, V[c])

    # Total pressure
    P_total = P['R'] + P['G'] + P['B'] + P['W']

    # Dominant color at each point (for Voronoi overlay)
    color_keys = ['R', 'G', 'B', 'W']
    P_stack = np.stack([P[c] for c in color_keys], axis=-1)
    dominant = np.argmax(P_stack, axis=-1)

    # Heatmap of total pressure (log scale for visibility)
    im = ax.pcolormesh(X, Y, np.log10(P_total), cmap='hot', shading='auto',
                       rasterized=True)
    cbar = plt.colorbar(im, ax=ax, shrink=0.85, pad=0.02)
    cbar.set_label(r'$\log_{10}\,\Sigma\, P_c(\mathbf{x})$', fontsize=10)

    # Draw Voronoi domain boundaries
    # Boundaries where dominant color changes
    boundary = np.zeros_like(dominant, dtype=bool)
    boundary[1:, :] |= (dominant[1:, :] != dominant[:-1, :])
    boundary[:, 1:] |= (dominant[:, 1:] != dominant[:, :-1])
    bx, by = X[boundary], Y[boundary]
    ax.scatter(bx, by, c='white', s=0.15, alpha=0.5, rasterized=True)

    # Vertex dots on z=0 projection
    for c in color_keys:
        v = V[c]
        ax.plot(v[0], v[1], 'o', color=CC[c], markersize=10,
                markeredgecolor='white', markeredgewidth=1.5, zorder=10)
        # Label
        offset = np.array([v[0], v[1]])
        offset = offset / (np.linalg.norm(offset) + 1e-8) * 0.12
        ax.text(v[0] + offset[0], v[1] + offset[1],
                f'$v_{{{c}}}$', fontsize=11, fontweight='bold',
                color='white', ha='center', va='center', zorder=11)

    ax.set_xlabel(r'$x$')
    ax.set_ylabel(r'$y$')
    ax.set_aspect('equal')
    ax.set_title(r'(a) Pressure Landscape ($z = 0$ slice)', fontsize=11,
                 fontweight='bold')

    # ==============================================================
    # (b) Pressure Profile: v_R -> -v_R
    # ==============================================================
    ax = axes[1]

    # Path from v_R to -v_R (antipodal vertex)
    v_start = V['R']
    v_end = -V['R']
    t_param = np.linspace(0, 1, 500)
    path = v_start[None, :] + t_param[:, None] * (v_end - v_start)[None, :]

    for c in ['R', 'G', 'B']:
        P_line = pressure(path[:, 0], path[:, 1], path[:, 2], V[c])
        ax.plot(t_param, P_line, color=CC[c], lw=2.5,
                label=rf'$P_{{{c}}}$')

    # Mark crossover points (domain boundaries)
    P_R = pressure(path[:, 0], path[:, 1], path[:, 2], V['R'])
    P_G = pressure(path[:, 0], path[:, 1], path[:, 2], V['G'])
    P_B = pressure(path[:, 0], path[:, 1], path[:, 2], V['B'])

    # Find crossings: only P_R = P_G and P_R = P_B (physically meaningful)
    # Skip P_G = P_B — G and B are nearly degenerate along this path,
    # producing spurious floating-point crossings.
    for Pa, Pb, ca, cb in [(P_R, P_G, 'R', 'G'), (P_R, P_B, 'R', 'B')]:
        diff = Pa - Pb
        sign_changes = np.where(np.diff(np.sign(diff)))[0]
        for idx in sign_changes:
            # Linear interpolation for exact crossing
            frac = abs(diff[idx]) / (abs(diff[idx]) + abs(diff[idx + 1]))
            t_cross = t_param[idx] + frac * (t_param[idx + 1] - t_param[idx])
            y_cross = Pa[idx] + frac * (Pa[idx + 1] - Pa[idx])
            ax.axvline(t_cross, color=(0.5, 0.5, 0.5), ls=':', lw=1.0,
                       alpha=0.6, zorder=0)
            ax.plot(t_cross, y_cross, 'o', color='black', markersize=5,
                    zorder=5)

    # Legend entry for domain boundaries
    ax.plot([], [], 'o', color='black', markersize=5,
            label=r'Domain boundary ($P_c = P_{c^\prime}$)')

    ax.set_xlabel(r'Path parameter $t$: $\mathbf{v}_R \to \bar{\mathbf{v}}_R$')
    ax.set_ylabel(r'$P_c(\mathbf{x}(t))$')
    ax.set_yscale('log')
    ax.legend(loc='upper right', fontsize=9, framealpha=0.9)
    ax.set_title(r'(b) Pressure Profile: $v_R \to \bar{v}_R$', fontsize=11,
                 fontweight='bold')

    # Annotate domain regions
    ax.text(0.08, 0.85, r'$\mathcal{D}_R$', transform=ax.transAxes,
            fontsize=13, fontweight='bold', color=CC['R'], alpha=0.7)
    ax.text(0.88, 0.85, r'$\bar{\mathcal{D}}_R$', transform=ax.transAxes,
            fontsize=13, fontweight='bold', color=CC['R'], alpha=0.5)

    plt.tight_layout()

    # Save
    for ext in ['pdf', 'png']:
        path_out = os.path.join(OUTPUT_DIR, f'fig_pressure_function_landscape.{ext}')
        fig.savefig(path_out, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path_out}")
    plt.close('all')


if __name__ == '__main__':
    main()

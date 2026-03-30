#!/usr/bin/env python3
"""
Figure: Fisher Information Stability (Section 4.2)

Three-panel visualization of why N=3 color fields is uniquely selected:
(a) Fisher stability S(N): unstable for N<=2, stable for N>=3, N=3 highlighted
(b) Per-DOF Fisher information I_DOF(N) = 1/(2N), maximum among stable configs at N=3
(c) Interference patterns: N=2 (destructive, flat) vs N=3 (positive-definite, 3-lobed)

Key physics:
- Fisher information stability requires N >= 3 fields
- Per-DOF information is maximized at the smallest stable N
- Three-field superposition produces positive-definite interference
- The intersection {N>=3} cap {N<=4} cap {3|N} = {3} is unique

Proof Document: docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md
Paper Section: Section 4.2 (Fisher Information Stability)
Output: fig_fisher_information_stability.pdf, fig_fisher_information_stability.png
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

# Colors
C_UNSTABLE = (0.70, 0.70, 0.70)   # Gray for unstable
C_STABLE = (0.15, 0.68, 0.15)     # Green for stable
C_HIGHLIGHT = (0.91, 0.15, 0.15)  # Red for N=3 highlight
C_BLUE = (0.20, 0.40, 0.86)
C_RED = (0.91, 0.15, 0.15)
C_GREEN = (0.15, 0.68, 0.15)


def fisher_stability(N):
    """
    Fisher stability indicator S(N).
    S(N) = 1 for N >= 3 (stable), S(N) = 0 for N < 3 (unstable).
    This is the discrete stability criterion from the three-bounds intersection.
    """
    return 1 if N >= 3 else 0


def fisher_per_dof(N):
    """Per-DOF Fisher information I_DOF(N) = 1/(2N)."""
    return 1.0 / (2.0 * N)


def angular_coverage(theta, N, kappa=4.0):
    """
    Angular coverage pattern for N equally-spaced sources.

    Uses von Mises kernel: rho(theta) = sum_k exp(kappa * cos(theta - 2*pi*k/N))

    For N=2: deep valleys near zero between sources (poor angular coverage)
    For N=3: shallow valleys, always well above zero (positive-definite coverage)

    The ratio min/max decreases exponentially with kappa for N=2 but only
    polynomially for N=3, reflecting the Fisher stability transition.
    """
    rho = np.zeros_like(theta)
    for k in range(N):
        rho += np.exp(kappa * np.cos(theta - 2 * np.pi * k / N))
    return rho


def main():
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.5))

    # ==============================================================
    # (a) Fisher Stability Transition
    # ==============================================================
    ax = axes[0]
    N_vals = np.arange(1, 9)
    S_vals = [fisher_stability(N) for N in N_vals]

    colors = []
    for N, S in zip(N_vals, S_vals):
        if N == 3:
            colors.append(C_HIGHLIGHT)
        elif S == 1:
            colors.append(C_STABLE)
        else:
            colors.append(C_UNSTABLE)

    bars = ax.bar(N_vals, S_vals, color=colors, edgecolor='black', linewidth=0.8,
                  width=0.7)

    # Threshold line
    ax.axhline(y=0.5, color='black', ls='--', lw=1.0, alpha=0.4)

    # Labels
    ax.set_xlabel(r'Number of fields $N$')
    ax.set_ylabel(r'Stability $S(N)$')
    ax.set_title(r'(a) Fisher Stability Transition', fontsize=11,
                 fontweight='bold')
    ax.set_xticks(N_vals)
    ax.set_yticks([0, 1])
    ax.set_yticklabels(['Unstable', 'Stable'])
    ax.set_ylim(-0.1, 1.3)

    # Annotate N=3
    ax.annotate(r'$N = 3$', xy=(3, 1.0), xytext=(3, 1.15),
                fontsize=11, fontweight='bold', color=C_HIGHLIGHT,
                ha='center', va='bottom')

    # Bracket for stable region
    ax.axvspan(2.5, 8.5, alpha=0.06, color=C_STABLE, zorder=0)
    ax.text(5.5, 1.2, r'$N \geq 3$: stable', fontsize=9, color=C_STABLE,
            ha='center', style='italic')

    # ==============================================================
    # (b) Per-DOF Fisher Information
    # ==============================================================
    ax = axes[1]
    N_cont = np.linspace(2, 8, 200)
    I_cont = fisher_per_dof(N_cont)

    # Continuous curve
    ax.plot(N_cont, I_cont, '-', color=(0.5, 0.5, 0.5), lw=1.5, alpha=0.5,
            zorder=1)

    # Discrete points
    for N in range(2, 9):
        I_val = fisher_per_dof(N)
        if N == 3:
            ax.plot(N, I_val, 'o', color=C_HIGHLIGHT, markersize=12,
                    markeredgecolor='black', markeredgewidth=1.5, zorder=10)
            ax.annotate(rf'$N=3$: $I = 1/6$', xy=(N, I_val),
                        xytext=(N + 0.6, I_val + 0.02),
                        fontsize=10, fontweight='bold', color=C_HIGHLIGHT,
                        arrowprops=dict(arrowstyle='->', color=C_HIGHLIGHT,
                                        lw=1.5),
                        zorder=11)
        elif N < 3:
            ax.plot(N, I_val, 's', color=C_UNSTABLE, markersize=8,
                    markeredgecolor='black', markeredgewidth=1.0, zorder=5)
        else:
            ax.plot(N, I_val, 'o', color=C_STABLE, markersize=8,
                    markeredgecolor='black', markeredgewidth=1.0, zorder=5)

    # Mark the stable region boundary
    ax.axvline(x=3, color=C_HIGHLIGHT, ls=':', lw=1.0, alpha=0.5)

    ax.set_xlabel(r'Number of fields $N$')
    ax.set_ylabel(r'$I_{\mathrm{DOF}}(N) = 1/(2N)$')
    ax.set_title(r'(b) Per-DOF Fisher Information', fontsize=11,
                 fontweight='bold')
    ax.set_xticks(range(2, 9))
    ax.set_xlim(1.5, 8.5)

    # ==============================================================
    # (c) Angular Coverage: N=2 vs N=3
    # ==============================================================
    ax = axes[2]

    theta = np.linspace(0, 2 * np.pi, 500)

    rho_2 = angular_coverage(theta, 2, kappa=4.0)
    rho_3 = angular_coverage(theta, 3, kappa=4.0)

    # Normalize each to its max for fair comparison
    rho_2_norm = rho_2 / np.max(rho_2)
    rho_3_norm = rho_3 / np.max(rho_3)

    # Polar-like plot in Cartesian coordinates
    for rho_norm, color, ls, lw, label in [
        (rho_2_norm, C_BLUE, '--', 2.0, r'$N=2$: deep valleys'),
        (rho_3_norm, C_RED, '-', 2.5, r'$N=3$: positive-definite'),
    ]:
        r = rho_norm  # Radial coordinate = normalized coverage
        x = r * np.cos(theta)
        y = r * np.sin(theta)
        ax.plot(x, y, ls, color=color, lw=lw, label=label)

    # Minimum-radius circle for N=3 (showing positive-definiteness)
    min_3 = np.min(rho_3_norm)
    circle_theta = np.linspace(0, 2 * np.pi, 200)
    ax.plot(min_3 * np.cos(circle_theta), min_3 * np.sin(circle_theta),
            ':', color=C_RED, lw=1.0, alpha=0.5)
    ax.text(min_3 * 0.7, -min_3 * 0.15, r'$\min > 0$',
            fontsize=9, color=C_RED, ha='center', style='italic')

    # Phase markers for N=3 sources
    for k in range(3):
        angle = k * 2 * np.pi / 3
        ax.plot([0, 1.05 * np.cos(angle)], [0, 1.05 * np.sin(angle)],
                '-', color=(0.5, 0.5, 0.5), lw=0.8, alpha=0.4)
        ax.plot(1.08 * np.cos(angle), 1.08 * np.sin(angle), 'o',
                color=C_RED, markersize=5, zorder=5)

    # Phase markers for N=2 sources
    for k in range(2):
        angle = k * np.pi
        ax.plot(1.08 * np.cos(angle), 1.08 * np.sin(angle), 's',
                color=C_BLUE, markersize=5, zorder=5)

    ax.set_aspect('equal')
    ax.set_xlim(-1.25, 1.25)
    ax.set_ylim(-1.25, 1.25)
    ax.axhline(0, color='gray', lw=0.5, alpha=0.3)
    ax.axvline(0, color='gray', lw=0.5, alpha=0.3)
    ax.legend(loc='lower left', fontsize=9, framealpha=0.9)
    ax.set_xlabel(r'$\rho(\theta)\cos\theta$')
    ax.set_ylabel(r'$\rho(\theta)\sin\theta$')
    ax.set_title(r'(c) Angular Coverage: $N = 2$ vs $N = 3$', fontsize=11,
                 fontweight='bold')

    plt.tight_layout()

    # Save
    for ext in ['pdf', 'png']:
        path = os.path.join(OUTPUT_DIR, f'fig_fisher_information_stability.{ext}')
        fig.savefig(path, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Saved: {path}")
    plt.close('all')


if __name__ == '__main__':
    main()

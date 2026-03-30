#!/usr/bin/env python3
"""
Figure: D=4 Stability Analysis (Theorem 0.0.1)

Generates publication-quality figure showing why D=4 spacetime is unique for
stable atomic structures.

Two-panel figure:
(a) Effective potential for orbital motion in different dimensions
(b) Dimensional selection: Four constraints table

Lean 4 Reference: Theorem_0_0_1.lean - stability_requires_D4
Proof Document: docs/proofs/foundations/Theorem-0.0.1-D4-From-Observer-Existence.md
Source: verification/foundations/theorem_0_0_1_verification.py

Output: fig_thm_0_0_1_d4_stability.pdf, fig_thm_0_0_1_d4_stability.png
"""

import numpy as np
import matplotlib.pyplot as plt
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 11,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# =============================================================================
# Combined plot matching LaTeX figure style (Fig. D4-stability)
# Two-panel figure: (a) Effective potential, (b) Constraint intersection diagram
# =============================================================================
fig, axes = plt.subplots(1, 2, figsize=(14, 5.5))

# Panel (a): Effective potential plot
ax = axes[0]
r_range = np.linspace(0.5, 6.5, 200)

# D=4 (n=3): Stable minimum - the good case
V_D4 = [-2/r + 1.5/(r**2) for r in r_range]
ax.plot(r_range, V_D4, color='#2060B0', linewidth=2.5, linestyle='-', label='$D=4$')
# Mark the stable minimum
r_min_D4 = 1.5
V_min_D4 = -2/r_min_D4 + 1.5/(r_min_D4**2)
ax.plot(r_min_D4, V_min_D4, 'o', color='#2060B0', markersize=8)
ax.annotate('stable', xy=(r_min_D4, V_min_D4), xytext=(r_min_D4, V_min_D4 + 0.4),
            fontsize=10, ha='center', color='#2060B0')

# D=5 (n=4): Unstable
V_D5 = [-2.5/(r**2) + 1.8/(r**2) for r in r_range]
ax.plot(r_range, V_D5, color='#B03030', linewidth=2, linestyle='--', label='$D=5$')

# D>=6 (n>=5): No minimum
V_D6 = [-3/(r**3) + 2/(r**2) for r in r_range]
ax.plot(r_range, V_D6, color='#D07000', linewidth=2, linestyle=':', label='$D \geq 6$')

# D=3 (n=2): Logarithmic
V_D3 = [0.8*np.log(r) - 1.5 + 1.2/(r**2) for r in r_range]
ax.plot(r_range, V_D3, color='#308030', linewidth=2, linestyle='-.', label='$D=3$')

ax.set_xlabel('$r$', fontsize=14)
ax.set_ylabel('$V_{\\mathrm{eff}}(r)$', fontsize=14)
ax.set_xlim(0, 7)
ax.set_ylim(-2.5, 3)
ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
ax.annotate('bound state', xy=(2.2, -0.9), xytext=(3, -1.5),
            fontsize=10, arrowprops=dict(arrowstyle='->', color='black', lw=0.8))
ax.text(0.3, 2.7, '$V_{\\mathrm{eff}} = V(r) + \\frac{L^2}{2mr^2}$\n$V(r) \\propto r^{-(n-2)}$, $n = D-1$',
        fontsize=10, verticalalignment='top',
        bbox=dict(boxstyle='round', facecolor='white', alpha=0.8, edgecolor='gray'))
ax.legend(loc='lower right', fontsize=11, framealpha=0.9)
ax.set_title('(a) Effective Potential for Orbital Motion', fontsize=12)

# Panel (b): Constraint intersection diagram (table style)
ax2 = axes[1]
ax2.axis('off')

# Create a table showing which dimensions satisfy which constraints
dimensions = [2, 3, 4, 5, 6, 7]
constraints = ['P1: Gravity\n$n \\leq 3$', 'P2: Atoms\n$n = 3$',
               'P3: Huygens\n$n \\geq 3$, odd', 'P4: Knots\n$n = 3$']

# Build constraint satisfaction matrix
# P1: Gravitational stability requires n <= 3 (D <= 4)
# P2: Atomic stability requires n = 3 (D = 4)
# P3: Huygens principle requires n odd AND n >= 3 (D = 4, 6, 8, ...)
# P4: Topological complexity (knots) requires n = 3 (D = 4)
satisfaction = {
    2: [True, False, False, False],  # D=2: n=1 (odd but < 3, fails P3)
    3: [True, False, False, False],  # D=3: n=2
    4: [True, True, True, True],     # D=4: n=3 - ALL SATISFIED
    5: [False, False, False, False], # D=5: n=4
    6: [False, False, True, False],  # D=6: n=5 (odd and >= 3, passes P3)
    7: [False, False, False, False], # D=7: n=6
}

# Create visual table
cell_width = 0.12
cell_height = 0.1
start_x = 0.18
start_y = 0.85

# Header row - Constraints
ax2.text(start_x - 0.05, start_y + 0.08, '$D$', fontsize=12, fontweight='bold', ha='center')
for i, constraint in enumerate(constraints):
    ax2.text(start_x + (i + 0.5) * cell_width + 0.05, start_y + 0.08, constraint,
             fontsize=9, ha='center', va='bottom')

# Data rows
for row_idx, D in enumerate(dimensions):
    y = start_y - row_idx * cell_height
    n = D - 1

    # Dimension label
    if D == 4:
        ax2.text(start_x - 0.05, y, f'$D={D}$', fontsize=11, fontweight='bold',
                ha='center', va='center', color='#2060B0')
    else:
        ax2.text(start_x - 0.05, y, f'$D={D}$', fontsize=11, ha='center', va='center')

    # Constraint satisfaction cells
    for col_idx, satisfied in enumerate(satisfaction[D]):
        x = start_x + (col_idx + 0.5) * cell_width + 0.05

        if satisfied:
            color = '#90EE90'  # light green
            symbol = '✓'
            text_color = 'darkgreen'
        else:
            color = '#FFB0B0'  # light red
            symbol = '✗'
            text_color = 'darkred'

        # Highlight D=4 row
        if D == 4:
            color = '#40A040' if satisfied else '#FFB0B0'
            text_color = 'white' if satisfied else 'darkred'

        rect = plt.Rectangle((x - cell_width/2, y - cell_height/2),
                             cell_width, cell_height,
                             facecolor=color, edgecolor='gray', linewidth=1)
        ax2.add_patch(rect)
        ax2.text(x, y, symbol, fontsize=14, ha='center', va='center',
                color=text_color, fontweight='bold')

# Add "Result" column
result_x = start_x + 4.5 * cell_width + 0.05
ax2.text(result_x, start_y + 0.08, 'Result', fontsize=10, fontweight='bold', ha='center')

for row_idx, D in enumerate(dimensions):
    y = start_y - row_idx * cell_height
    all_satisfied = all(satisfaction[D])

    if all_satisfied:
        color = '#FFD700'  # gold
        text = 'D = 4\nUNIQUE'
        text_color = 'black'
        fontweight = 'bold'
    else:
        color = 'lightgray'
        text = '—'
        text_color = 'gray'
        fontweight = 'normal'

    rect = plt.Rectangle((result_x - cell_width/2, y - cell_height/2),
                         cell_width * 1.2, cell_height,
                         facecolor=color, edgecolor='gray', linewidth=1)
    ax2.add_patch(rect)
    ax2.text(result_x + 0.01, y, text, fontsize=9, ha='center', va='center',
            color=text_color, fontweight=fontweight)

# Conclusion box - positioned below the table, above the descriptions
conclusion_text = '$\\{n \\leq 3\\} \\cap \\{n = 3\\} \\cap \\{n \\geq 3,\\ \\mathrm{odd}\\} \\cap \\{n = 3\\} = \\{3\\}$\n$\\Rightarrow D = n + 1 = 4$'
ax2.text(0.5, 0.22, conclusion_text, fontsize=11, ha='center', va='top',
        transform=ax2.transAxes,
        bbox=dict(boxstyle='round', facecolor='#E8E8FF', edgecolor='#2060B0', linewidth=2))

# Add constraint descriptions at bottom
descriptions = [
    '(P1) Gravitational stability: stable orbits require $D \\leq 4$',
    '(P2) Atomic stability: discrete spectrum requires $D = 4$',
    '(P3) Huygens principle: sharp wave propagation for $D = 4, 6, 8, ...$ (odd $n \\geq 3$)',
    '(P4) Topological complexity: non-trivial knots require $D = 4$'
]

for i, desc in enumerate(descriptions):
    ax2.text(0.05, 0.08 - i * 0.045, desc, fontsize=8, ha='left', va='top',
            transform=ax2.transAxes)

ax2.set_xlim(0, 1)
ax2.set_ylim(0, 1)
ax2.set_title('(b) Dimensional Selection: Four Constraints', fontsize=12)

plt.tight_layout()

# Save figures
plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_1_d4_stability.png', dpi=300, bbox_inches='tight')
plt.savefig(f'{OUTPUT_DIR}/fig_thm_0_0_1_d4_stability.pdf', bbox_inches='tight')
plt.close()

print("Figure saved successfully!")
print("Key physics illustrated:")
print("  - Panel (a): Effective potentials show only D=4 has stable bound orbits")
print("  - Panel (b): Four independent constraints uniquely select D=4")
print("    P1: Gravitational stability (n ≤ 3)")
print("    P2: Atomic stability (n = 3)")
print("    P3: Huygens principle (n odd)")
print("    P4: Topological complexity/knots (n = 3)")
print("  - Result: Only D=4 satisfies all constraints")

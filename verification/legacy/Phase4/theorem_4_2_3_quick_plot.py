#!/usr/bin/env python3
"""
Quick plot for Theorem 4.2.3: v(T_c)/T_c = 1.2 ± 0.1
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt

# Set up plot style
plt.rcParams.update({
    'font.size': 12,
    'figure.figsize': (10, 7),
    'figure.dpi': 150,
})

# Data from theorem verification
kappa_values = [0.50, 0.75, 1.00, 1.25, 1.50, 2.00]
v_T_values = [1.17, 1.22, 1.24, 1.26, 1.27, 1.29]

# Extended range for plotting
kappa_extended = np.linspace(0.3, 2.5, 50)
# Linear interpolation/extrapolation
v_T_extended = 1.10 + 0.09 * (kappa_extended - 0.3)

fig, ax = plt.subplots()

# Main line
ax.plot(kappa_extended, v_T_extended, 'b-', linewidth=2.5, label='CG prediction')

# Data points
ax.scatter(kappa_values, v_T_values, s=100, c='blue', zorder=5, edgecolors='black')

# Baryogenesis threshold
ax.axhline(y=1.0, color='red', linestyle='--', linewidth=2, label='Baryogenesis threshold ($v/T_c = 1$)')

# SM prediction
ax.axhline(y=0.15, color='gray', linestyle=':', linewidth=2, label='SM prediction (~0.15)')

# Highlight CG result region
ax.axhspan(1.1, 1.3, alpha=0.25, color='green', label='CG result: $1.2 \\pm 0.1$')

# Labels and styling
ax.set_xlabel('Geometric coupling parameter $\\kappa$', fontsize=14)
ax.set_ylabel('$v(T_c)/T_c$', fontsize=14)
ax.set_title('Theorem 4.2.3: First-Order Phase Transition Strength\nChiral Geometrogenesis vs Standard Model', fontsize=14)
ax.legend(loc='lower right', fontsize=11)
ax.set_xlim(0.3, 2.5)
ax.set_ylim(0, 1.6)
ax.grid(True, alpha=0.3)

# Annotations
ax.annotate('CG: Strong first-order\n(baryogenesis viable)',
            xy=(1.5, 1.25), fontsize=11, ha='center',
            bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))
ax.annotate('SM: Crossover\n(no baryogenesis)',
            xy=(1.5, 0.25), fontsize=11, ha='center',
            bbox=dict(boxstyle='round', facecolor='lightcoral', alpha=0.8))

# Result box
ax.text(0.5, 1.45, r'$\mathbf{v(T_c)/T_c = 1.2 \pm 0.1}$',
        fontsize=14, fontweight='bold',
        bbox=dict(boxstyle='round', facecolor='white', edgecolor='blue', linewidth=2))

plt.tight_layout()
plt.savefig('theorem_4_2_3_phase_transition_strength.png', dpi=200)
print("✓ Saved: theorem_4_2_3_phase_transition_strength.png")

# Also create a summary figure
fig2, axes = plt.subplots(1, 2, figsize=(14, 6))

# Left: Phase transition strength
ax1 = axes[0]
ax1.plot(kappa_extended, v_T_extended, 'b-', linewidth=2.5)
ax1.scatter(kappa_values, v_T_values, s=80, c='blue', zorder=5, edgecolors='black')
ax1.axhline(y=1.0, color='red', linestyle='--', linewidth=2)
ax1.axhspan(1.1, 1.3, alpha=0.25, color='green')
ax1.set_xlabel('$\\kappa$', fontsize=14)
ax1.set_ylabel('$v(T_c)/T_c$', fontsize=14)
ax1.set_title('(A) Phase Transition Strength', fontsize=13)
ax1.set_xlim(0.3, 2.5)
ax1.set_ylim(0.8, 1.5)
ax1.grid(True, alpha=0.3)
ax1.annotate(r'$\mathbf{1.2 \pm 0.1}$', xy=(1.5, 1.2), fontsize=16,
            ha='center', fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.9))

# Right: Key results summary
ax2 = axes[1]
ax2.axis('off')

results_text = """
THEOREM 4.2.3 KEY RESULTS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Phase Transition Strength:
    v(Tc)/Tc = 1.2 ± 0.1   ✓ Baryogenesis viable

Critical Temperature:
    Tc ≈ 124 GeV

Geometric Coupling (from S₄ group theory):
    κgeo ≈ 0.06 λH
    Range: [0.015, 0.15] λH

Gravitational Waves:
    Ω h² ≈ 5 × 10⁻¹⁰
    fpeak ≈ 8 mHz
    SNRLISA ≈ 49   ✓ Detectable

Bubble Wall Velocity:
    vw ≈ 0.20   (deflagration)
    ✓ Optimal for baryogenesis

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
All Sakharov conditions satisfied.
"""
ax2.text(0.1, 0.95, results_text, transform=ax2.transAxes,
         fontsize=12, verticalalignment='top', fontfamily='monospace',
         bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))
ax2.set_title('(B) Summary of Results', fontsize=13)

plt.suptitle('Theorem 4.2.3: First-Order Electroweak Phase Transition from CG Geometry',
             fontsize=15, fontweight='bold', y=1.02)

plt.tight_layout()
plt.savefig('theorem_4_2_3_summary.png', dpi=200)
print("✓ Saved: theorem_4_2_3_summary.png")

print("\nDone!")

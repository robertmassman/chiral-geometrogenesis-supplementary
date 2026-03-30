#!/usr/bin/env python3
"""
Figure: Strong CP Resolution - Combined Two-Panel Figure (Theorem 4.3)

Panel (a): Vacuum energy V(θ) = -χ_top cos(θ) with Z₃ discrete points vs continuous.
Panel (b): Circle diagram comparing Peccei-Quinn mechanism vs Chiral Geometrogenesis.

Proof Document: docs/proofs/foundations/Proposition-0.0.17i-Z3-Measurement-Extension.md
Paper Section: Section 4, Theorem 4.3 (Strong CP Resolution)

Output: fig_strong_cp_z3_vacuum.pdf, fig_strong_cp_z3_vacuum.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, Arc
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
    'axes.labelsize': 12,
    'axes.titlesize': 13,
    'legend.fontsize': 9,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# Colors
COLOR_Z3_0 = '#2060B0'        # Blue for θ = 0 (global minimum)
COLOR_Z3_OTHER = '#B03030'    # Red for θ = 2π/3, 4π/3
COLOR_CONTINUOUS = '#808080'  # Gray for continuous θ
COLOR_HIGHLIGHT = '#FFD700'   # Gold for highlighting selection
COLOR_PQ = '#D07000'          # Orange for PQ mechanism
COLOR_CG = '#308030'          # Green for CG mechanism

# =============================================================================
# Create two-panel figure
# =============================================================================
fig = plt.figure(figsize=(14, 6))

# Panel (a): Vacuum energy V(θ)
ax1 = fig.add_subplot(121)

# Continuous vacuum energy curve
theta = np.linspace(0, 2*np.pi, 500)
V_theta = -np.cos(theta)  # V(θ)/χ_top = -cos(θ)

# Plot continuous curve (light gray background)
ax1.plot(theta, V_theta, color=COLOR_CONTINUOUS, linewidth=2.5, linestyle='-',
         alpha=0.5, label='Continuous $\\theta$ (Standard QCD)')

# Z₃ discrete points
theta_z3 = np.array([0, 2*np.pi/3, 4*np.pi/3])
V_z3 = -np.cos(theta_z3)  # [-1, 0.5, 0.5]

# Plot Z₃ points with different colors for minimum vs others
# θ = 0 (global minimum)
ax1.scatter([0], [-1], color=COLOR_Z3_0, s=200, zorder=5, edgecolors='black',
            linewidths=2, marker='o')
ax1.scatter([2*np.pi], [-1], color=COLOR_Z3_0, s=200, zorder=5, edgecolors='black',
            linewidths=2, marker='o')  # Periodic copy

# θ = 2π/3 and 4π/3 (local maxima within Z₃)
ax1.scatter([2*np.pi/3, 4*np.pi/3], [0.5, 0.5], color=COLOR_Z3_OTHER, s=140,
            zorder=5, edgecolors='black', linewidths=1.5, marker='o')

# Annotations for Z₃ points
ax1.annotate('$\\theta = 0$\n(selected)', xy=(0, -0.85), xytext=(0, -0.35),
             fontsize=10, ha='center', color=COLOR_Z3_0, fontweight='bold',
             arrowprops=dict(arrowstyle='->', color=COLOR_Z3_0, lw=1.5))

ax1.annotate('$\\theta = 2\\pi/3$', xy=(2*np.pi/3, 0.65), xytext=(2*np.pi/3, 1.05),
             fontsize=9, ha='center', color=COLOR_Z3_OTHER,
             arrowprops=dict(arrowstyle='->', color=COLOR_Z3_OTHER, lw=1.2))

ax1.annotate('$\\theta = 4\\pi/3$', xy=(4*np.pi/3, 0.65), xytext=(4*np.pi/3, 1.05),
             fontsize=9, ha='center', color=COLOR_Z3_OTHER,
             arrowprops=dict(arrowstyle='->', color=COLOR_Z3_OTHER, lw=1.2))

# Mark the global minimum region
ax1.axhline(y=-1, color=COLOR_Z3_0, linestyle='--', alpha=0.5, linewidth=1.5)
ax1.text(np.pi, -0.82, 'Global minimum: $V = -\\chi_{\\rm top}$',
         fontsize=9, ha='center', color=COLOR_Z3_0)

# Axes formatting
ax1.set_xlabel('$\\theta$', fontsize=13)
ax1.set_ylabel('$V(\\theta)/\\chi_{\\rm top}$', fontsize=13)
ax1.set_xlim(-0.5, 2*np.pi + 0.5)
ax1.set_ylim(-1.3, 1.3)

# Custom x-ticks at key values
ax1.set_xticks([0, 2*np.pi/3, np.pi, 4*np.pi/3, 2*np.pi])
ax1.set_xticklabels(['$0$', '$\\frac{2\\pi}{3}$', '$\\pi$', '$\\frac{4\\pi}{3}$', '$2\\pi$'])

ax1.axhline(y=0, color='gray', linestyle='-', alpha=0.3, linewidth=0.5)
ax1.set_title('(a) Vacuum Energy: $V(\\theta) = -\\chi_{\\rm top}\\cos\\theta$', fontsize=12)

# Legend for panel (a)
legend_elements = [
    Line2D([0], [0], color=COLOR_CONTINUOUS, linewidth=2.5, alpha=0.5,
           label='Continuous $\\theta$'),
    Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_Z3_0,
           markersize=10, markeredgecolor='black', markeredgewidth=2,
           label='$\\mathbb{Z}_3$: $\\theta = 0$'),
    Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_Z3_OTHER,
           markersize=9, markeredgecolor='black', markeredgewidth=1.5,
           label='$\\mathbb{Z}_3$: $\\theta \\neq 0$'),
]
ax1.legend(handles=legend_elements, loc='upper right', fontsize=9, framealpha=0.95)

# =============================================================================
# Panel (b): Circle diagram comparing PQ vs CG
# =============================================================================
ax2 = fig.add_subplot(122)
ax2.set_aspect('equal')
ax2.axis('off')

# Draw two circles side by side
circle_radius = 1.2
center_pq = (-1.8, 0.3)  # PQ circle center (left)
center_cg = (1.8, 0.3)   # CG circle center (right)

# --- Left circle: Standard QCD / PQ mechanism (continuous θ) ---
circle_pq = Circle(center_pq, circle_radius, fill=False, color=COLOR_PQ, linewidth=3)
ax2.add_patch(circle_pq)

# Fill with light shading
circle_pq_fill = Circle(center_pq, circle_radius, facecolor=COLOR_PQ, alpha=0.1, edgecolor='none')
ax2.add_patch(circle_pq_fill)

# Label above circle
ax2.text(center_pq[0], center_pq[1] + circle_radius + 0.7,
         'Standard QCD\n(continuous $\\theta$)',
         fontsize=10, ha='center', fontweight='bold', color=COLOR_PQ, va='bottom')

# Mark a generic θ point
theta_generic = np.pi/4
x_gen = center_pq[0] + circle_radius * np.cos(theta_generic)
y_gen = center_pq[1] + circle_radius * np.sin(theta_generic)
ax2.scatter([x_gen], [y_gen], color=COLOR_PQ, s=100, zorder=5)
ax2.annotate('$\\bar{\\theta}$', xy=(x_gen, y_gen),
             xytext=(x_gen + 0.35, y_gen + 0.35),
             fontsize=12, color=COLOR_PQ)

# Arrow showing continuous variation
arc_arrow = Arc(center_pq, 2*circle_radius*0.55, 2*circle_radius*0.55,
                angle=0, theta1=20, theta2=150, color=COLOR_PQ, linewidth=1.5)
ax2.add_patch(arc_arrow)

# Text inside circle
ax2.text(center_pq[0], center_pq[1] - 0.25,
         '$\\theta \\in [0, 2\\pi)$',
         fontsize=10, ha='center', color=COLOR_PQ)
ax2.text(center_pq[0], center_pq[1] - 0.6,
         'why $\\bar{\\theta} \\approx 0$?',
         fontsize=9, ha='center', style='italic', color='#666666')

# --- Right circle: CG mechanism (discrete Z₃) ---
circle_cg = Circle(center_cg, circle_radius, fill=False, color=COLOR_CG, linewidth=3)
ax2.add_patch(circle_cg)

# Label above circle
ax2.text(center_cg[0], center_cg[1] + circle_radius + 0.7,
         'Chiral Geometrogenesis\n(discrete $\\mathbb{Z}_3$)',
         fontsize=10, ha='center', fontweight='bold', color=COLOR_CG, va='bottom')

# Z₃ discrete points on circle - starting from top
theta_z3_angles = [np.pi/2, np.pi/2 + 2*np.pi/3, np.pi/2 + 4*np.pi/3]
z3_labels = ['$\\theta = 0$', '$\\theta = \\frac{2\\pi}{3}$', '$\\theta = \\frac{4\\pi}{3}$']
z3_colors = [COLOR_Z3_0, COLOR_Z3_OTHER, COLOR_Z3_OTHER]
z3_sizes = [200, 130, 130]

for i, (angle, label, color, size) in enumerate(zip(theta_z3_angles, z3_labels, z3_colors, z3_sizes)):
    x = center_cg[0] + circle_radius * np.cos(angle)
    y = center_cg[1] + circle_radius * np.sin(angle)
    ax2.scatter([x], [y], color=color, s=size, zorder=5,
                edgecolors='black', linewidths=2.5 if i == 0 else 1.5)

    # Position labels outside the circle
    label_offset = 0.4
    lx = center_cg[0] + (circle_radius + label_offset) * np.cos(angle)
    ly = center_cg[1] + (circle_radius + label_offset) * np.sin(angle)

    if i == 0:  # θ = 0 (selected) - at top
        ax2.text(lx + 0.5, ly, label + ' (selected)',
                 fontsize=10, ha='left', va='center', color=color, fontweight='bold')
    elif i == 1:  # θ = 2π/3 - bottom left
        ax2.text(lx - 0.05, ly, label, fontsize=9, ha='right', va='center', color=color)
    else:  # θ = 4π/3 - bottom right
        ax2.text(lx + 0.05, ly, label, fontsize=9, ha='left', va='center', color=color)

# Draw Z₃ symmetry lines (connecting through center)
for angle in theta_z3_angles:
    x1 = center_cg[0] + circle_radius * np.cos(angle)
    y1 = center_cg[1] + circle_radius * np.sin(angle)
    x2 = center_cg[0] + circle_radius * np.cos(angle + np.pi)
    y2 = center_cg[1] + circle_radius * np.sin(angle + np.pi)
    ax2.plot([x1, x2], [y1, y2], color='gray', linewidth=1, alpha=0.3, linestyle='--')

# Text inside circle
ax2.text(center_cg[0], center_cg[1] - 0.15,
         '$\\theta \\in \\{0, \\frac{2\\pi}{3}, \\frac{4\\pi}{3}\\}$',
         fontsize=9, ha='center', color=COLOR_CG)
ax2.text(center_cg[0], center_cg[1] - 0.5,
         '$V(0) < V(\\frac{2\\pi}{3})$',
         fontsize=9, ha='center', color=COLOR_Z3_0)

# Highlight ring around θ = 0 point
highlight_x = center_cg[0] + circle_radius * np.cos(np.pi/2)
highlight_y = center_cg[1] + circle_radius * np.sin(np.pi/2)
highlight = Circle((highlight_x, highlight_y), 0.28, fill=False,
                   color=COLOR_HIGHLIGHT, linewidth=3)
ax2.add_patch(highlight)

# Arrow between circles showing the conceptual transition
ax2.annotate('', xy=(center_cg[0] - circle_radius - 0.25, 0.3),
             xytext=(center_pq[0] + circle_radius + 0.25, 0.3),
             arrowprops=dict(arrowstyle='->', color='#555555', lw=2,
                           connectionstyle='arc3,rad=0'))
ax2.text(0, 0.65, 'discretization', fontsize=9, ha='center', color='#555555', style='italic')

# Key insight annotation at top
ax2.text(0, circle_radius + 1.6, 'No fine-tuning: geometric quantization',
         fontsize=11, ha='center', va='bottom', fontweight='bold', color='#2060B0',
         bbox=dict(boxstyle='round', facecolor='#E8E8FF', edgecolor='#2060B0', linewidth=2))

# Comparison text boxes at bottom
box_y = -1.8

# PQ box (full text from original)
pq_text = ('Peccei–Quinn Mechanism:\n'
           '• Introduces axion field $a(x)$\n'
           '• $\\theta_{\\rm eff} = \\theta + a/f_a$\n'
           '• Axion relaxes to minimum\n'
           '• Requires new particle (axion)')
ax2.text(center_pq[0], box_y, pq_text, fontsize=9, ha='center', va='top',
         bbox=dict(boxstyle='round', facecolor='#FFF5E0', edgecolor=COLOR_PQ, linewidth=1.5))

# CG box (full text from original)
cg_text = ('Chiral Geometrogenesis:\n'
           '• $\\mathbb{Z}_3$ from stella geometry\n'
           '• $\\bar{\\theta}$ quantized ab initio\n'
           '• Vacuum selects $\\theta = 0$\n'
           '• No new particles needed')
ax2.text(center_cg[0], box_y, cg_text, fontsize=9, ha='center', va='top',
         bbox=dict(boxstyle='round', facecolor='#E8FFE8', edgecolor=COLOR_CG, linewidth=1.5))

# Title for panel (b)
ax2.set_title('(b) $\\mathbb{Z}_3$ Discretization vs Continuous $\\theta$', fontsize=12, pad=10)

# Set axis limits for panel (b)
ax2.set_xlim(-4, 4)
ax2.set_ylim(-3, 3.2)

plt.tight_layout()

# Save figures
plt.savefig(f'{OUTPUT_DIR}/fig_strong_cp_z3_vacuum.png', dpi=300, bbox_inches='tight')
plt.savefig(f'{OUTPUT_DIR}/fig_strong_cp_z3_vacuum.pdf', bbox_inches='tight')
plt.close()

print("Combined figure saved successfully!")
print("Output files:")
print(f"  - {OUTPUT_DIR}/fig_strong_cp_z3_vacuum.png")
print(f"  - {OUTPUT_DIR}/fig_strong_cp_z3_vacuum.pdf")
print()
print("Key physics illustrated:")
print("  Panel (a): Vacuum energy V(θ) = -χ_top cos(θ)")
print("    - Continuous curve shows standard QCD parameter space")
print("    - Z₃ discretizes to only three allowed values: {0, 2π/3, 4π/3}")
print("    - Vacuum uniquely selects θ = 0")
print()
print("  Panel (b): Comparison of resolution mechanisms")
print("    - PQ: continuous θ → axion field relaxes to minimum")
print("    - CG: discrete Z₃ from stella geometry → no continuous parameter")
print("    - Key insight: geometric quantization eliminates fine-tuning")

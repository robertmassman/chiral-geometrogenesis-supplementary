#!/usr/bin/env python3
"""
Figure: Soliton Topology - π₃(SU(2)) = ℤ Winding Number Visualization

Shows how Skyrme solitons (baryons and W-condensate dark matter) are topologically
protected by the homotopy group π₃(SU(2)) = ℤ.

The key physics:
- Chiral field U(x): S³ (spatial infinity) → SU(2) ≅ S³ (group manifold)
- Winding number Q ∈ ℤ counts how many times space "wraps" around the target
- Q = 0: vacuum (trivial map)
- Q = 1: single soliton (hedgehog configuration)
- Both baryons (RGB sector) and W-solitons (singlet sector) share this topology

Panel (a): Schematic showing S³ → S³ mapping for Q=0 and Q=1
Panel (b): Topological protection - energy landscape showing stability

Proof Document: docs/proofs/Phase4/Proposition-4.1.2-Soliton-Fermion-Number.md
Paper Section: Section 4.9.6 (W-Condensate Dark Matter)

Output: fig_soliton_topology.pdf, fig_soliton_topology.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, FancyArrowPatch, Arc, Wedge
import matplotlib.patches as mpatches
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

# Colors - consistent with other figures
COLOR_BARYON = '#3498db'      # Blue for baryons (matches fundamental rep)
COLOR_W_SOLITON = '#9b59b6'   # Purple for W-solitons (dark sector)
COLOR_VACUUM = '#95a5a6'      # Gray for vacuum
COLOR_FIELD_COLD = '#2060B0'  # Blue for cold (north pole)
COLOR_FIELD_HOT = '#B03030'   # Red for hot (south pole)
COLOR_SPACE = '#27ae60'       # Green for spatial domain
COLOR_TARGET = '#f39c12'      # Orange for target manifold
COLOR_BARRIER = '#c0392b'     # Dark red for energy barrier
COLOR_HIGHLIGHT = '#FFD700'   # Gold for highlighting


# =============================================================================
# Create two-panel figure
# =============================================================================
fig = plt.figure(figsize=(14, 6))

# =============================================================================
# Panel (a): Schematic - S³ → S³ Mapping (Winding Number Concept)
# =============================================================================
ax1 = fig.add_subplot(121)
ax1.set_aspect('equal')
ax1.axis('off')

# Layout: Two rows showing Q=0 (top) and Q=1 (bottom)
# Each row has: Source sphere → Arrow → Target sphere

sphere_radius = 0.8
row_spacing = 2.8
col_spacing = 3.0

# --- Row 1: Q = 0 (Vacuum - trivial map) ---
row1_y = 1.2
source1_center = (-col_spacing/2 - 0.5, row1_y)
target1_center = (col_spacing/2 + 0.5, row1_y)

# Source sphere (spatial S³, represented as circle)
circle_source1 = Circle(source1_center, sphere_radius, fill=False,
                        color=COLOR_SPACE, linewidth=3)
ax1.add_patch(circle_source1)
# Light fill
circle_source1_fill = Circle(source1_center, sphere_radius, facecolor=COLOR_SPACE,
                              alpha=0.1, edgecolor='none')
ax1.add_patch(circle_source1_fill)

# Target sphere (SU(2) ≅ S³)
circle_target1 = Circle(target1_center, sphere_radius, fill=False,
                        color=COLOR_TARGET, linewidth=3)
ax1.add_patch(circle_target1)
circle_target1_fill = Circle(target1_center, sphere_radius, facecolor=COLOR_TARGET,
                              alpha=0.1, edgecolor='none')
ax1.add_patch(circle_target1_fill)

# For Q=0: All points map to a single point (north pole)
# Show this by drawing multiple points on source mapping to one point on target
n_points = 8
for i in range(n_points):
    angle = 2 * np.pi * i / n_points
    # Points distributed around source
    px = source1_center[0] + 0.5 * sphere_radius * np.cos(angle)
    py = source1_center[1] + 0.5 * sphere_radius * np.sin(angle)
    ax1.scatter([px], [py], color=COLOR_VACUUM, s=40, zorder=5)

# Single point on target (all map here)
target_point1 = (target1_center[0], target1_center[1] + 0.5 * sphere_radius)
ax1.scatter([target_point1[0]], [target_point1[1]], color=COLOR_VACUUM, s=100,
            zorder=5, edgecolors='black', linewidths=1.5)

# Dashed lines showing the trivial mapping (all to one point)
for i in range(n_points):
    angle = 2 * np.pi * i / n_points
    px = source1_center[0] + 0.5 * sphere_radius * np.cos(angle)
    py = source1_center[1] + 0.5 * sphere_radius * np.sin(angle)
    ax1.annotate('', xy=target_point1, xytext=(px, py),
                 arrowprops=dict(arrowstyle='->', color=COLOR_VACUUM, lw=1,
                               alpha=0.4, connectionstyle='arc3,rad=0.1'))

# Arrow between spheres
ax1.annotate('', xy=(target1_center[0] - sphere_radius - 0.15, row1_y),
             xytext=(source1_center[0] + sphere_radius + 0.15, row1_y),
             arrowprops=dict(arrowstyle='->', color='black', lw=2))
ax1.text(0, row1_y + 0.25, '$U(x)$', fontsize=11, ha='center', va='bottom')

# Labels
ax1.text(source1_center[0], source1_center[1] - sphere_radius - 0.35,
         '$S^3$ (space)', fontsize=10, ha='center', color=COLOR_SPACE, fontweight='bold')
ax1.text(target1_center[0], target1_center[1] - sphere_radius - 0.35,
         '$S^3$ (SU(2))', fontsize=10, ha='center', color=COLOR_TARGET, fontweight='bold')

# Q=0 label
ax1.text(-col_spacing - 1.0, row1_y, '$Q = 0$\n(vacuum)', fontsize=11, ha='center',
         va='center', fontweight='bold', color=COLOR_VACUUM,
         bbox=dict(boxstyle='round,pad=0.3', facecolor='white', edgecolor=COLOR_VACUUM, linewidth=1.5))

# Explanation
ax1.text(target1_center[0] + sphere_radius + 0.4, row1_y,
         'All points\nmap to one', fontsize=9, ha='left', va='center',
         color='#555555', style='italic')


# --- Row 2: Q = 1 (Soliton - wraps once) ---
row2_y = -1.6
source2_center = (-col_spacing/2 - 0.5, row2_y)
target2_center = (col_spacing/2 + 0.5, row2_y)

# Source sphere
circle_source2 = Circle(source2_center, sphere_radius, fill=False,
                        color=COLOR_SPACE, linewidth=3)
ax1.add_patch(circle_source2)
circle_source2_fill = Circle(source2_center, sphere_radius, facecolor=COLOR_SPACE,
                              alpha=0.1, edgecolor='none')
ax1.add_patch(circle_source2_fill)

# Target sphere
circle_target2 = Circle(target2_center, sphere_radius, fill=False,
                        color=COLOR_TARGET, linewidth=3)
ax1.add_patch(circle_target2)
circle_target2_fill = Circle(target2_center, sphere_radius, facecolor=COLOR_TARGET,
                              alpha=0.1, edgecolor='none')
ax1.add_patch(circle_target2_fill)

# For Q=1: Points wrap around - use color gradient to show correspondence
n_wrap_points = 8
for i in range(n_wrap_points):
    angle = 2 * np.pi * i / n_wrap_points
    # Source point
    px_s = source2_center[0] + 0.6 * sphere_radius * np.cos(angle)
    py_s = source2_center[1] + 0.6 * sphere_radius * np.sin(angle)
    # Target point (same angle - shows 1-to-1 wrapping)
    px_t = target2_center[0] + 0.6 * sphere_radius * np.cos(angle)
    py_t = target2_center[1] + 0.6 * sphere_radius * np.sin(angle)

    # Color by angle (shows the wrapping correspondence)
    color = plt.cm.coolwarm(i / n_wrap_points)

    ax1.scatter([px_s], [py_s], color=color, s=50, zorder=5, edgecolors='black', linewidths=0.5)
    ax1.scatter([px_t], [py_t], color=color, s=50, zorder=5, edgecolors='black', linewidths=0.5)

    # Curved arrows showing the mapping
    ax1.annotate('', xy=(px_t, py_t), xytext=(px_s, py_s),
                 arrowprops=dict(arrowstyle='->', color=color, lw=1.2,
                               alpha=0.6, connectionstyle='arc3,rad=0.15'))

# Arrow between spheres
ax1.annotate('', xy=(target2_center[0] - sphere_radius - 0.15, row2_y),
             xytext=(source2_center[0] + sphere_radius + 0.15, row2_y),
             arrowprops=dict(arrowstyle='->', color='black', lw=2))
ax1.text(0, row2_y + 0.25, '$U(x)$', fontsize=11, ha='center', va='bottom')

# Labels
ax1.text(source2_center[0], source2_center[1] - sphere_radius - 0.35,
         '$S^3$ (space)', fontsize=10, ha='center', color=COLOR_SPACE, fontweight='bold')
ax1.text(target2_center[0], target2_center[1] - sphere_radius - 0.35,
         '$S^3$ (SU(2))', fontsize=10, ha='center', color=COLOR_TARGET, fontweight='bold')

# Q=1 label
ax1.text(-col_spacing - 1.0, row2_y, '$Q = 1$\n(soliton)', fontsize=11, ha='center',
         va='center', fontweight='bold', color=COLOR_BARYON,
         bbox=dict(boxstyle='round,pad=0.3', facecolor='white', edgecolor=COLOR_BARYON, linewidth=1.5))

# Explanation
ax1.text(target2_center[0] + sphere_radius + 0.4, row2_y,
         'Wraps once\naround target', fontsize=9, ha='left', va='center',
         color='#555555', style='italic')


# Title
ax1.set_title('(a) Winding Number: $\\pi_3(\\mathrm{SU}(2)) = \\mathbb{Z}$', fontsize=12, pad=15)

# Key insight box at top
ax1.text(0, 3.0, 'Topological charge $Q$ = number of times space wraps around target',
         fontsize=10, ha='center', va='center',
         bbox=dict(boxstyle='round,pad=0.4', facecolor='#E8F4E8',
                   edgecolor=COLOR_SPACE, linewidth=2))

# Set axis limits
ax1.set_xlim(-5, 5)
ax1.set_ylim(-3.5, 3.8)


# =============================================================================
# Panel (b): Topological Protection - Energy Landscape
# =============================================================================
ax2 = fig.add_subplot(122)

# Configuration space coordinate (representing topological sector)
q_config = np.linspace(-0.5, 3.5, 200)

# Energy landscape with barriers between integer sectors
# Physical scale: soliton mass M_B ~ 940 MeV (proton), barrier is infinite
# We show E/M_B so the soliton rest mass is at 1.0
def energy_landscape(q):
    # Cosine potential with minima at integers
    # Minima at E/M_B = 1 (soliton mass), maxima represent infinite barrier
    E_base = 1.0  # Soliton rest mass
    E_periodic = 0.5 * (1 - np.cos(2 * np.pi * q))
    # Add slight linear tilt to show increasing energy for higher Q
    E_tilt = 0.15 * q
    return E_base + E_periodic + E_tilt

E_config = energy_landscape(q_config)

# Plot energy curve
ax2.plot(q_config, E_config, color='black', linewidth=2.5)
ax2.fill_between(q_config, 0, E_config, alpha=0.08, color='gray')

# Mark the integer sectors (topological charge values)
Q_values = [0, 1, 2, 3]
Q_labels = ['$Q = 0$\n(vacuum)', '$Q = 1$\n(baryon)', '$Q = 2$', '$Q = 3$']
Q_colors = [COLOR_VACUUM, COLOR_BARYON, COLOR_BARYON, COLOR_BARYON]

for Q, label, color in zip(Q_values, Q_labels, Q_colors):
    E_Q = energy_landscape(Q)
    ax2.scatter([Q], [E_Q], color=color, s=150, zorder=10,
                edgecolors='black', linewidths=2)
    ax2.text(Q, 0.35, label, ha='center', va='top', fontsize=9)

# Mark W-soliton at Q=1 (same topology as baryon)
# Draw it slightly offset to show both occupy same sector
E_W = energy_landscape(1) + 0.08
ax2.scatter([1.0], [E_W], color=COLOR_W_SOLITON, s=120,
            zorder=11, edgecolors='black', linewidths=2, marker='s')
ax2.annotate('$M_W = 1.6$ TeV', xy=(1.0, E_W),
             xytext=(1.2, E_W), fontsize=9, color=COLOR_W_SOLITON,
             arrowprops=dict(arrowstyle='->', color=COLOR_W_SOLITON, lw=1.5))

# Draw barrier annotation between Q=0 and Q=1
barrier_x = 0.5
barrier_bottom = energy_landscape(0) + 0.05
barrier_top = energy_landscape(0.5)
ax2.annotate('', xy=(barrier_x, barrier_top), xytext=(barrier_x, barrier_bottom),
             arrowprops=dict(arrowstyle='<->', color=COLOR_BARRIER, lw=2))
ax2.text(barrier_x + 0.08, (barrier_top + barrier_bottom)/2 + 0.05, '$\\infty$',
         fontsize=14, color=COLOR_BARRIER, fontweight='bold')
ax2.text(barrier_x, barrier_top + 0.08, 'barrier',
         fontsize=8, color=COLOR_BARRIER, style='italic', ha='center')

# Arrow showing soliton trapped in Q=1 well
# Draw attempted escape path that fails
escape_start = (1.0, energy_landscape(1) + 0.03)
escape_peak = (0.65, 1.55)
ax2.annotate('', xy=escape_peak, xytext=escape_start,
             arrowprops=dict(arrowstyle='->', color=COLOR_BARYON, lw=1.5,
                           connectionstyle='arc3,rad=0.3', linestyle='--', alpha=0.6))
ax2.text(0.44, 1.62, '$\\times$', fontsize=18, color=COLOR_BARRIER, fontweight='bold')

# Axis labels and formatting
ax2.set_xlabel('Topological Charge $Q$', fontsize=12)
ax2.set_ylabel('Energy $E/M_B$', fontsize=12)
ax2.set_xlim(-0.5, 3.5)
ax2.set_ylim(0, 2.4)

# Custom x-ticks
ax2.set_xticks([0, 1, 2, 3])
ax2.set_xticklabels(['0', '1', '2', '3'])

# Y-axis ticks with physical meaning
ax2.set_yticks([0, 0.5, 1.0, 1.5, 2.0])
ax2.set_yticklabels(['0', '0.5', '1.0', '1.5', '2.0'])

# Add horizontal lines at key energies
ax2.axhline(y=0, color='gray', linestyle='-', alpha=0.3, linewidth=1)
ax2.axhline(y=1.0, color='gray', linestyle='--', alpha=0.4, linewidth=1)
ax2.text(3.3, 1.0, '$M_B$', fontsize=9, color='gray', va='center')

ax2.set_title('(b) Energy Landscape: $\\pi_3(\\mathrm{SU}(2)) = \\mathbb{Z}$',
              fontsize=12)

# Create legend
legend_elements_2 = [
    Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_VACUUM,
           markersize=10, markeredgecolor='black', markeredgewidth=1.5,
           label='Vacuum ($Q = 0$)'),
    Line2D([0], [0], marker='o', color='w', markerfacecolor=COLOR_BARYON,
           markersize=10, markeredgecolor='black', markeredgewidth=1.5,
           label='Baryon ($Q = 1$)'),
    Line2D([0], [0], marker='s', color='w', markerfacecolor=COLOR_W_SOLITON,
           markersize=9, markeredgecolor='black', markeredgewidth=1.5,
           label='W-soliton ($Q = 1$)'),
]
ax2.legend(handles=legend_elements_2, loc='upper right', fontsize=8, framealpha=0.95)


# =============================================================================
# Final layout and save
# =============================================================================
plt.tight_layout()

# Save figures
plt.savefig(f'{OUTPUT_DIR}/fig_soliton_topology.png', dpi=300, bbox_inches='tight',
            facecolor='white')
plt.savefig(f'{OUTPUT_DIR}/fig_soliton_topology.pdf', bbox_inches='tight')
plt.close()

print("Soliton topology figure saved successfully!")
print("Output files:")
print(f"  - {OUTPUT_DIR}/fig_soliton_topology.png")
print(f"  - {OUTPUT_DIR}/fig_soliton_topology.pdf")
print()
print("Key physics illustrated:")
print("  Panel (a): Winding number schematic")
print("    - Shows S³ → S³ mapping for Q=0 (vacuum) and Q=1 (soliton)")
print("    - Q=0: All points map to single point (trivial, no wrapping)")
print("    - Q=1: Points wrap once around target (topologically nontrivial)")
print("    - Color correspondence shows the 1-to-1 mapping structure")
print()
print("  Panel (b): Topological protection")
print("    - Energy has discrete minima at integer Q values")
print("    - Infinite barrier between sectors (cannot tunnel)")
print("    - Both baryons and W-solitons have Q = 1 (same topology)")
print("    - This explains why both are absolutely stable")

#!/usr/bin/env python3
"""
Figure: Bootstrap-then-Verify Methodology Diagram

Generates publication-quality figure showing the two-stage logical structure
of the bootstrap-then-verify methodology with inputs, outputs, and failure modes.

Proof Document: docs/proofs/reference/Challenge-Resolutions.md (Challenge 1)
Related: docs/proofs/Phase0/Theorem-0.2.2-Internal-Time-Emergence.md

Output: fig_methodology_bootstrap.pdf, fig_methodology_bootstrap.png
"""

import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Set up figure - wider to accommodate text
fig, ax = plt.subplots(figsize=(4.5, 4.0), dpi=300)
ax.set_xlim(0, 13)
ax.set_ylim(0, 12)
ax.axis('off')

# Colors
stage_a_color = '#E8F4FD'  # Light blue
stage_b_color = '#FDF4E8'  # Light orange
arrow_color = '#555555'
text_color = '#222222'

# Stage A box - wider
stage_a = FancyBboxPatch((0.5, 7.5), 12, 4,
                          boxstyle="round,pad=0.05,rounding_size=0.3",
                          facecolor=stage_a_color, edgecolor='#4A90D9', linewidth=1.5)
ax.add_patch(stage_a)

# Stage A content
ax.text(6.5, 11.0, 'Stage A: Bootstrap', fontsize=10, fontweight='bold',
        ha='center', va='center', color='#2D5F8B')
ax.text(6.5, 10.2, '(Geometric Selection)', fontsize=7, style='italic',
        ha='center', va='center', color='#4A7BA7')

# Stage A: Uses
ax.text(1.0, 9.3, 'Uses:', fontsize=7, fontweight='bold', ha='left', color=text_color)
ax.text(1.0, 8.7, 'GR + QM as', fontsize=6.5, ha='left', color=text_color)
ax.text(1.0, 8.2, 'selection criteria', fontsize=6.5, ha='left', color=text_color)

# Stage A: Derives
ax.text(4.5, 9.3, 'Derives:', fontsize=7, fontweight='bold', ha='left', color=text_color)
ax.text(4.5, 8.7, 'Stella uniqueness', fontsize=6.5, ha='left', color=text_color)
ax.text(4.5, 8.2, 'D = 4, SU(3) embedding', fontsize=6.5, ha='left', color=text_color)

# Stage A: Failure mode
ax.text(9.0, 9.3, 'Failure:', fontsize=7, fontweight='bold', ha='left', color=text_color)
ax.text(9.0, 8.7, 'N/A', fontsize=6.5, ha='left', color='#666666')
ax.text(9.0, 8.2, '(selection only)', fontsize=5.5, style='italic', ha='left', color='#888888')

# Arrow between stages
arrow = FancyArrowPatch((6.5, 7.4), (6.5, 6.1),
                         arrowstyle='-|>', mutation_scale=12,
                         color=arrow_color, linewidth=1.5)
ax.add_patch(arrow)
ax.text(6.8, 6.75, 'geometry', fontsize=6, style='italic', ha='left', va='center', color='#666666')

# Stage B box - wider
stage_b = FancyBboxPatch((0.5, 1.0), 12, 5,
                          boxstyle="round,pad=0.05,rounding_size=0.3",
                          facecolor=stage_b_color, edgecolor='#D98B4A', linewidth=1.5)
ax.add_patch(stage_b)

# Stage B content
ax.text(6.5, 5.5, 'Stage B: Verification', fontsize=10, fontweight='bold',
        ha='center', va='center', color='#8B5A2D')
ax.text(6.5, 4.8, '(Physical Derivation)', fontsize=7, style='italic',
        ha='center', va='center', color='#A77B4A')

# Stage B: Uses
ax.text(1.0, 4.0, 'Uses:', fontsize=7, fontweight='bold', ha='left', color=text_color)
ax.text(1.0, 3.5, 'Stella geometry', fontsize=6.5, ha='left', color=text_color)
ax.text(1.0, 3.0, '(Layers 1–4)', fontsize=6.5, ha='left', color=text_color)

# Stage B: Derives
ax.text(4.5, 4.0, 'Derives:', fontsize=7, fontweight='bold', ha='left', color=text_color)
ax.text(4.5, 3.5, 'QM, Lorentz', fontsize=6.5, ha='left', color=text_color)
ax.text(4.5, 3.0, 'invariance, GR', fontsize=6.5, ha='left', color=text_color)

# Stage B: Failure modes (in box)
ax.text(8.5, 4.0, 'Failure modes:', fontsize=7, fontweight='bold', ha='left', color=text_color)
ax.text(8.5, 3.5, '(i) Wightman violation', fontsize=5.5, ha='left', color='#8B4A4A')
ax.text(8.5, 3.05, '(ii) ω ≠ c|k| at low E', fontsize=5.5, ha='left', color='#8B4A4A')
ax.text(8.5, 2.6, '(iii) ∇μTμν ≠ 0', fontsize=5.5, ha='left', color='#8B4A4A')

# Key insight text at bottom
ax.text(6.5, 0.5, 'Stage A selects geometry; Stage B derives physics from it.',
        fontsize=6, style='italic', ha='center', va='center', color='#555555')

# Dividing lines within boxes
ax.plot([4.0, 4.0], [7.8, 9.5], color='#CCCCCC', linewidth=0.5, linestyle='--')
ax.plot([8.3, 8.3], [7.8, 9.5], color='#CCCCCC', linewidth=0.5, linestyle='--')
ax.plot([4.0, 4.0], [2.4, 4.2], color='#CCCCCC', linewidth=0.5, linestyle='--')
ax.plot([8.0, 8.0], [2.4, 4.2], color='#CCCCCC', linewidth=0.5, linestyle='--')

plt.tight_layout()

# Save to parent figures directory
pdf_path = os.path.join(OUTPUT_DIR, 'fig_methodology_bootstrap.pdf')
png_path = os.path.join(OUTPUT_DIR, 'fig_methodology_bootstrap.png')
plt.savefig(pdf_path, bbox_inches='tight', pad_inches=0.05)
plt.savefig(png_path, bbox_inches='tight', pad_inches=0.05)
print(f"Generated: {pdf_path}")
print(f"Generated: {png_path}")

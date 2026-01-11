#!/usr/bin/env python3
"""
Figure: Honeycomb Time Flow

Single-panel visualization of time arrows in honeycomb structure.

Shows how the internal time parameter λ generates a consistent
arrow of time along [1,1,1] across the tetrahedral-octahedral honeycomb.

Source: Extracted from papers/paper-2-dynamics/figures/paper_2_publication_plots.py
Originally derived from verification/foundations/theorem_0_0_6_time_arrow.py
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from pathlib import Path

# Output directory (parent of scripts folder = figures folder)
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'serif',
    'font.serif': ['Times New Roman', 'DejaVu Serif'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'figure.dpi': 300,
})


def generate_fcc_lattice_for_honeycomb(n_max=1):
    """Generate FCC lattice points for honeycomb visualization."""
    points = []
    for n1 in range(-n_max, n_max + 1):
        for n2 in range(-n_max, n_max + 1):
            for n3 in range(-n_max, n_max + 1):
                if (n1 + n2 + n3) % 2 == 0:
                    points.append([n1, n2, n3])
    return np.array(points)


def create_fig_thm_4_1_1_time_flow():
    """
    Single-panel visualization of time arrows in honeycomb structure.

    Shows how the internal time parameter λ generates a consistent
    arrow of time along [1,1,1] across the tetrahedral-octahedral honeycomb.
    """
    fig = plt.figure(figsize=(8, 8))
    ax = fig.add_subplot(111, projection='3d')

    # Get a few FCC lattice points
    fcc = generate_fcc_lattice_for_honeycomb(n_max=1)
    w_axis = np.array([1, 1, 1]) / np.sqrt(3)

    # Draw time arrows at each FCC vertex
    arrow_scale = 0.5
    for pt in fcc:
        # Small stella indicator at each point
        ax.scatter([pt[0]], [pt[1]], [pt[2]], c='gold', s=50, alpha=0.7)

        # Time arrow pointing along W
        ax.quiver(pt[0], pt[1], pt[2],
                  w_axis[0]*arrow_scale, w_axis[1]*arrow_scale, w_axis[2]*arrow_scale,
                  color='green', arrow_length_ratio=0.2, linewidth=1.5, alpha=0.8)

    # Draw FCC edges (nearest neighbors)
    sqrt2 = np.sqrt(2)
    for i, p1 in enumerate(fcc):
        for j, p2 in enumerate(fcc):
            if i < j:
                d = np.linalg.norm(p1 - p2)
                if abs(d - sqrt2) < 0.1:
                    ax.plot([p1[0], p2[0]], [p1[1], p2[1]], [p1[2], p2[2]],
                            'b-', alpha=0.2, linewidth=0.5)

    # Draw the global W-axis through center
    ax.quiver(-2*w_axis[0], -2*w_axis[1], -2*w_axis[2],
              4*w_axis[0], 4*w_axis[1], 4*w_axis[2],
              color='darkgreen', arrow_length_ratio=0.05, linewidth=3,
              label='Global time axis')

    ax.set_xlabel('X')
    ax.set_ylabel('Y')
    ax.set_zlabel('Z')
    ax.set_title('Time Arrows in Honeycomb\n(All point along [1,1,1])')
    ax.legend()
    ax.set_xlim(-2, 2)
    ax.set_ylim(-2, 2)
    ax.set_zlim(-2, 2)

    plt.tight_layout()

    for ext in ['pdf', 'png']:
        plt.savefig(output_dir / f'fig_thm_4_1_1_time_flow.{ext}', dpi=150)
    plt.close()
    print(f"Figure: Honeycomb time flow - saved to {output_dir}")


if __name__ == '__main__':
    create_fig_thm_4_1_1_time_flow()

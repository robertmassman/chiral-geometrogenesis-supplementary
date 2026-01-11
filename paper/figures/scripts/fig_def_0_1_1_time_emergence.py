#!/usr/bin/env python3
"""
Figure: Time Emergence from Definition 0.1.1

This script generates a figure showing the time emergence mechanism based ONLY
on the vertex coordinates documented in Definition-0.1.1-Stella-Octangula-Boundary-Topology.md.

PURPOSE: Verify coordinate conventions across three sources:
1. Markdown proof document (Definition 0.1.1)
2. Lean formalization (StellaOctangula.lean)
3. Existing Python code (paper_2_publication_plots.py)

AUTHORITATIVE SOURCE: Definition 0.1.1 (Section 2.2)

Author: Verification script for coordinate convention analysis
Date: 2025-01-10
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
import os

# =============================================================================
# SECTION 1: DOCUMENT THE COORDINATE CONVENTIONS FROM ALL THREE SOURCES
# =============================================================================

def print_convention_comparison():
    """
    Print a detailed comparison of vertex coordinate conventions from all three sources.
    """
    print("=" * 80)
    print("VERTEX COORDINATE CONVENTION COMPARISON")
    print("=" * 80)

    print("\n" + "=" * 80)
    print("SOURCE 1: Definition 0.1.1 (Markdown) - Section 2.2")
    print("=" * 80)
    print("""
From Definition-0.1.1-Stella-Octangula-Boundary-Topology.md, Section 2.2:

Tetrahedron T+ (Color Vertices R, G, B, W):
    v_R = (1, 1, 1) / sqrt(3)
    v_G = (1, -1, -1) / sqrt(3)
    v_B = (-1, 1, -1) / sqrt(3)
    v_W = (-1, -1, 1) / sqrt(3)

Tetrahedron T- (Anti-Color Vertices):
    v_R_bar = -v_R = (-1, -1, -1) / sqrt(3)
    v_G_bar = -v_G = (-1, 1, 1) / sqrt(3)
    v_B_bar = -v_B = (1, -1, 1) / sqrt(3)
    v_W_bar = -v_W = (1, 1, -1) / sqrt(3)

PHASES (from Definition 0.1.2):
    Phase_R = 0
    Phase_G = 2*pi/3
    Phase_B = 4*pi/3
""")

    print("\n" + "=" * 80)
    print("SOURCE 2: StellaOctangula.lean (Lean Formalization)")
    print("=" * 80)
    print("""
From lean/ChiralGeometrogenesis/PureMath/Polyhedra/StellaOctangula.lean:

Tetrahedron UP (v_up_0 through v_up_3):
    v_up_0 = (1, 1, 1)      -- corresponds to index 0
    v_up_1 = (1, -1, -1)    -- corresponds to index 1
    v_up_2 = (-1, 1, -1)    -- corresponds to index 2
    v_up_3 = (-1, -1, 1)    -- corresponds to index 3

Tetrahedron DOWN (v_down_0 through v_down_3):
    v_down_0 = (-1, -1, -1) = -v_up_0
    v_down_1 = (-1, 1, 1)   = -v_up_1
    v_down_2 = (1, -1, 1)   = -v_up_2
    v_down_3 = (1, 1, -1)   = -v_up_3

NOTE: Lean uses unit edge length = 2, vertices at |v|^2 = 3 (i.e., |v| = sqrt(3)).
      The markdown normalizes to unit sphere (|v| = 1) by dividing by sqrt(3).

COLOR ASSIGNMENT (implicit from index naming):
    v_up_0 = (1,1,1)     -> This is where Def 0.1.1 puts R
    v_up_1 = (1,-1,-1)   -> This is where Def 0.1.1 puts G
    v_up_2 = (-1,1,-1)   -> This is where Def 0.1.1 puts B
    v_up_3 = (-1,-1,1)   -> This is where Def 0.1.1 puts W
""")

    print("\n" + "=" * 80)
    print("SOURCE 3: paper_2_publication_plots.py (Existing Python)")
    print("=" * 80)
    print("""
From create_figure_time_emergence() in paper_2_publication_plots.py:

STELLA_VERTICES = {
    'W': np.array([1, 1, 1]) / np.sqrt(3),      # Singlet apex
    'R': np.array([1, -1, -1]) / np.sqrt(3),    # Red vertex
    'G': np.array([-1, 1, -1]) / np.sqrt(3),    # Green vertex
    'B': np.array([-1, -1, 1]) / np.sqrt(3)     # Blue vertex
}

PHASES = {'R': 0, 'G': 2*np.pi/3, 'B': 4*np.pi/3}

This corresponds to:
    W at (1, 1, 1) / sqrt(3)
    R at (1, -1, -1) / sqrt(3)
    G at (-1, 1, -1) / sqrt(3)
    B at (-1, -1, 1) / sqrt(3)
""")

    print("\n" + "=" * 80)
    print("COMPARISON TABLE")
    print("=" * 80)
    print("""
| Vertex | Definition 0.1.1          | Lean (v_up_*)    | Existing Python |
|--------|---------------------------|------------------|-----------------|
| R      | (1, 1, 1) / sqrt(3)       | v_up_0 = (1,1,1) | (1,-1,-1)/sqrt3 |
| G      | (1, -1, -1) / sqrt(3)     | v_up_1 = (1,-1,-1)| (-1,1,-1)/sqrt3|
| B      | (-1, 1, -1) / sqrt(3)     | v_up_2 = (-1,1,-1)| (-1,-1,1)/sqrt3|
| W      | (-1, -1, 1) / sqrt(3)     | v_up_3 = (-1,-1,1)| (1,1,1)/sqrt3  |

CRITICAL FINDING:
=================
The EXISTING PYTHON CODE SWAPS R AND W relative to Definition 0.1.1!

In Definition 0.1.1:
    - R (red) is at (1, 1, 1) / sqrt(3)
    - W (white/singlet) is at (-1, -1, 1) / sqrt(3)

In the existing Python:
    - W (white/singlet) is at (1, 1, 1) / sqrt(3)  <-- SWAPPED!
    - R (red) is at (1, -1, -1) / sqrt(3)          <-- SWAPPED!

The Lean formalization uses indices (v_up_0, v_up_1, etc.) without color labels,
so it is consistent with Definition 0.1.1 if we apply the mapping:
    v_up_0 = v_R
    v_up_1 = v_G
    v_up_2 = v_B
    v_up_3 = v_W
""")

    print("\n" + "=" * 80)
    print("PHASES")
    print("=" * 80)
    print("""
All sources agree on phases:
    Phase_R = 0
    Phase_G = 2*pi/3
    Phase_B = 4*pi/3

These come from Definition 0.1.2 (Three Color Fields with Relative Phases).
""")


# =============================================================================
# SECTION 2: DEFINE VERTICES ACCORDING TO DEFINITION 0.1.1 (AUTHORITATIVE)
# =============================================================================

# Normalization: vertices on unit sphere
SQRT3_INV = 1.0 / np.sqrt(3.0)

# From Definition 0.1.1, Section 2.2:
# Tetrahedron T+ (Color Vertices R, G, B, W):
VERTICES_DEF_0_1_1 = {
    'R': np.array([1, 1, 1]) * SQRT3_INV,      # v_R
    'G': np.array([1, -1, -1]) * SQRT3_INV,    # v_G
    'B': np.array([-1, 1, -1]) * SQRT3_INV,    # v_B
    'W': np.array([-1, -1, 1]) * SQRT3_INV,    # v_W
}

# Anti-vertices (T-): v_bar = -v
ANTI_VERTICES_DEF_0_1_1 = {
    'R_bar': -VERTICES_DEF_0_1_1['R'],
    'G_bar': -VERTICES_DEF_0_1_1['G'],
    'B_bar': -VERTICES_DEF_0_1_1['B'],
    'W_bar': -VERTICES_DEF_0_1_1['W'],
}

# Phases from Definition 0.1.2
PHASES = {
    'R': 0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

# Regularization parameter from Definition 0.1.3
EPSILON = 0.5  # default value

# Amplitude scale
A0 = 1.0


# =============================================================================
# SECTION 3: PHYSICAL FUNCTIONS
# =============================================================================

def pressure_function(x, vertex, epsilon=EPSILON):
    """
    Pressure function P_c(x) from Definition 0.1.3.

    P_c(x) = 1 / (|x - v_c|^2 + epsilon^2)

    Parameters:
        x: Position vector (3D)
        vertex: Vertex position vector (3D)
        epsilon: Regularization parameter

    Returns:
        Pressure value at position x for the given vertex
    """
    r_sq = np.sum((x - vertex)**2)
    return 1.0 / (r_sq + epsilon**2)


def chi_total(x, vertices=VERTICES_DEF_0_1_1, phases=PHASES, A0=A0, epsilon=EPSILON):
    """
    Total coherent field chi_total from Theorem 0.2.1.

    chi_total(x) = sum_{c in {R,G,B}} a_c * exp(i * phi_c)

    where a_c = A0 * P_c(x) is the amplitude from each color field.

    Parameters:
        x: Position vector (3D)
        vertices: Dictionary of vertex positions
        phases: Dictionary of phases for each color
        A0: Base amplitude
        epsilon: Regularization parameter

    Returns:
        Complex total field value at position x
    """
    result = 0j
    for color in ['R', 'G', 'B']:
        P_c = pressure_function(x, vertices[color], epsilon)
        a_c = A0 * P_c
        result += a_c * np.exp(1j * phases[color])
    return result


def chi_amplitude(x, vertices=VERTICES_DEF_0_1_1, phases=PHASES, A0=A0, epsilon=EPSILON):
    """
    Amplitude |chi_total(x)|.
    """
    return np.abs(chi_total(x, vertices, phases, A0, epsilon))


# =============================================================================
# SECTION 4: CREATE THE FIGURE
# =============================================================================

def create_fig_def_0_1_1_time_emergence(output_dir=None):
    """
    Create the time emergence figure based ONLY on Definition 0.1.1 coordinates.

    Shows:
    - Diagonal slice (x=y plane) through the stella octangula
    - Color field amplitude |chi_total|
    - R, G, B, W vertex positions according to Definition 0.1.1
    - Internal time direction lambda pointing toward W vertex
    - Color-neutral nodal surface where |chi| ~ 0

    Parameters:
        output_dir: Output directory for figures (defaults to script directory)

    Returns:
        Dictionary with figure metadata
    """
    if output_dir is None:
        output_dir = os.path.dirname(os.path.abspath(__file__))

    # Compute field amplitude on diagonal slice (x=y plane)
    n_points = 200
    extent = 1.5
    x_range = np.linspace(-extent, extent, n_points)
    z_range = np.linspace(-extent, extent, n_points)

    chi_grid = np.zeros((n_points, n_points))
    for i, x_val in enumerate(x_range):
        for j, z_val in enumerate(z_range):
            pos = np.array([x_val, x_val, z_val])  # x = y plane
            chi_grid[j, i] = chi_amplitude(pos)

    # Create figure
    fig, ax = plt.subplots(figsize=(8, 7))

    # Plot field amplitude with inverted grayscale (dark = high amplitude)
    im = ax.imshow(chi_grid, extent=[-extent, extent, -extent, extent],
                   origin='lower', cmap='gray_r', aspect='equal')

    # Add contour lines
    X, Z = np.meshgrid(x_range, z_range)
    contours = ax.contour(X, Z, chi_grid, levels=8, colors='#aaaaaa', alpha=0.5, linewidths=0.5)

    # Highlight the nodal surface (chi ~ 0)
    nodal_contour = ax.contour(X, Z, chi_grid, levels=[0.1], colors='black',
                               linewidths=2.5, linestyles='--')

    # Add colorbar
    cbar = plt.colorbar(im, ax=ax, shrink=0.8, pad=0.02)
    cbar.set_label(r'$|\chi_{\mathrm{total}}|$ (field amplitude)', fontsize=11)

    # Vertex colors
    vertex_colors = {
        'R': '#e74c3c',   # red
        'G': '#27ae60',   # green
        'B': '#3498db',   # blue
        'W': '#f39c12'    # gold/orange for white/singlet
    }

    # Mark vertices
    for name, vertex in VERTICES_DEF_0_1_1.items():
        on_diagonal = abs(vertex[0] - vertex[1]) < 0.01
        color = vertex_colors[name]

        if on_diagonal:
            # Filled marker for vertices on the slice
            ax.scatter(vertex[0], vertex[2], s=250, c=color,
                      edgecolors='black', linewidths=2, zorder=10)
        else:
            # Open marker for vertices off the slice (projected)
            ax.scatter(vertex[0], vertex[2], s=220, facecolors='none',
                      edgecolors=color, linewidths=3, zorder=10)

        # Label with offset
        offset_x = 0.12 if vertex[0] >= 0 else -0.25
        offset_z = 0.12
        ax.text(vertex[0] + offset_x, vertex[2] + offset_z, name,
                fontsize=14, fontweight='bold', color=color,
                ha='left' if vertex[0] >= 0 else 'right', va='bottom')

    # Mark center with star
    ax.scatter(0, 0, s=250, c='white', marker='*', edgecolors='black',
               linewidths=1.5, zorder=12)

    # Draw internal time arrow from center toward W vertex
    # According to Definition 0.1.1: W is at (-1, -1, 1) / sqrt(3)
    W = VERTICES_DEF_0_1_1['W']
    arrow_start = np.array([0, 0])  # Center in (x, z) projection
    arrow_end = np.array([W[0], W[2]])  # W position in (x, z)
    arrow_vec = arrow_end - arrow_start
    arrow_len = 0.75  # Draw 75% of the way toward W

    ax.annotate('', xy=(arrow_start[0] + arrow_len * arrow_vec[0],
                        arrow_start[1] + arrow_len * arrow_vec[1]),
                xytext=(arrow_start[0] + 0.12 * arrow_vec[0],
                        arrow_start[1] + 0.12 * arrow_vec[1]),
                arrowprops=dict(arrowstyle='->', color='#e67e22', lw=3,
                               mutation_scale=18),
                zorder=15)

    # Label for time direction (left side of arrow)
    mid_x = arrow_start[0] + 0.5 * arrow_vec[0] - 0.22
    mid_z = arrow_start[1] + 0.5 * arrow_vec[1] + 0.08
    ax.text(mid_x, mid_z, r'$\tau$ (internal time)',
            fontsize=11, fontweight='bold', color='#e67e22',
            ha='right',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='white',
                     edgecolor='#e67e22', alpha=0.95))

    # Add annotation for nodal surface (lower right)
    ax.text(1.44, -1.4, r'$|\chi| \approx 0$' + '\n(color neutral)',
            fontsize=10, color='black', style='italic',
            ha='right', va='bottom',
            bbox=dict(boxstyle='round,pad=0.3', facecolor='white',
                     edgecolor='gray', alpha=0.95))

    # Add vertex coordinate annotation box (top of graph)
    coord_text = (
        "Vertex Coordinates (Def. 0.1.1):\n"
        f"R = (1, 1, 1) / sqrt(3)\n"
        f"G = (1, -1, -1) / sqrt(3)\n"
        f"B = (-1, 1, -1) / sqrt(3)\n"
        f"W = (-1, -1, 1) / sqrt(3)"
    )
    ax.text(-1.45, 1.45, coord_text, fontsize=8, fontfamily='monospace',
            verticalalignment='top',
            bbox=dict(boxstyle='round,pad=0.4', facecolor='lightyellow',
                     edgecolor='orange', alpha=0.95))

    # Axis labels
    ax.set_xlabel(r'$x / R_{\mathrm{stella}}$', fontsize=12)
    ax.set_ylabel(r'$z / R_{\mathrm{stella}}$', fontsize=12)
    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)

    # Title
    ax.set_title(r'Color Field Amplitude on Diagonal Slice ($x = y$)' + '\n'
                 r'Time direction $\tau$ toward W (singlet vertex)',
                 fontsize=12, pad=10)

    plt.tight_layout()

    # Save figures
    for ext in ['pdf', 'png']:
        filepath = os.path.join(output_dir, f'fig_def_0_1_1_time_emergence.{ext}')
        plt.savefig(filepath, dpi=200, bbox_inches='tight')
        print(f"Saved: {filepath}")

    plt.close()

    return {
        'W_position': VERTICES_DEF_0_1_1['W'].tolist(),
        'R_position': VERTICES_DEF_0_1_1['R'].tolist(),
        'G_position': VERTICES_DEF_0_1_1['G'].tolist(),
        'B_position': VERTICES_DEF_0_1_1['B'].tolist(),
        'time_direction': 'Toward W at (-1, -1, 1) / sqrt(3)',
    }


# =============================================================================
# SECTION 5: DISCREPANCY ANALYSIS
# =============================================================================

def analyze_discrepancy():
    """
    Detailed analysis of the discrepancy between sources.
    """
    print("\n" + "=" * 80)
    print("DISCREPANCY ANALYSIS")
    print("=" * 80)

    # Define both conventions
    # Convention 1: Definition 0.1.1 (authoritative)
    def_0_1_1 = {
        'R': np.array([1, 1, 1]) / np.sqrt(3),
        'G': np.array([1, -1, -1]) / np.sqrt(3),
        'B': np.array([-1, 1, -1]) / np.sqrt(3),
        'W': np.array([-1, -1, 1]) / np.sqrt(3),
    }

    # Convention 2: Existing Python (paper_2_publication_plots.py)
    existing_python = {
        'W': np.array([1, 1, 1]) / np.sqrt(3),
        'R': np.array([1, -1, -1]) / np.sqrt(3),
        'G': np.array([-1, 1, -1]) / np.sqrt(3),
        'B': np.array([-1, -1, 1]) / np.sqrt(3),
    }

    print("\n1. COORDINATE COMPARISON:")
    print("-" * 60)
    print(f"{'Vertex':<8} {'Def 0.1.1':<30} {'Existing Python':<30}")
    print("-" * 60)
    for vertex in ['R', 'G', 'B', 'W']:
        v1 = def_0_1_1[vertex]
        v2 = existing_python[vertex]
        v1_str = f"({v1[0]:.4f}, {v1[1]:.4f}, {v1[2]:.4f})"
        v2_str = f"({v2[0]:.4f}, {v2[1]:.4f}, {v2[2]:.4f})"
        match = "MATCH" if np.allclose(v1, v2) else "DIFFER"
        print(f"{vertex:<8} {v1_str:<30} {v2_str:<30} {match}")

    print("\n2. MAPPING BETWEEN CONVENTIONS:")
    print("-" * 60)
    print("The existing Python code has relabeled the vertices:")
    print("  Def 0.1.1  ->  Existing Python")
    print("  R (1,1,1)  ->  W (1,1,1)")
    print("  G (1,-1,-1) -> R (1,-1,-1)")
    print("  B (-1,1,-1) -> G (-1,1,-1)")
    print("  W (-1,-1,1) -> B (-1,-1,1)")
    print("\nThis is a CYCLIC RELABELING: R->W, G->R, B->G, W->B")

    print("\n3. PHYSICAL IMPLICATIONS:")
    print("-" * 60)
    print("In Definition 0.1.1:")
    print("  - R (1,1,1) is the color vertex at the 'positive' direction")
    print("  - W (-1,-1,1) is the singlet (white) vertex")
    print("  - Internal time lambda flows toward W")
    print()
    print("In the existing Python:")
    print("  - W (1,1,1) is labeled as the singlet vertex")
    print("  - Internal time flows toward (1,1,1)")
    print()
    print("This means the PHYSICAL INTERPRETATION is different!")
    print("The time direction in the existing code points toward (1,1,1),")
    print("but according to Definition 0.1.1, this is the R (red) vertex!")

    print("\n4. PHASE ASSIGNMENT:")
    print("-" * 60)
    print("Both sources agree that:")
    print("  Phase_R = 0")
    print("  Phase_G = 2*pi/3")
    print("  Phase_B = 4*pi/3")
    print()
    print("However, since the vertex positions are relabeled, the existing")
    print("Python code assigns phases to different physical locations:")
    print()
    print("  Location (1,1,1)/sqrt(3):")
    print("    - Def 0.1.1: R vertex, phase = 0")
    print("    - Existing Python: W vertex, no phase (not R/G/B)")
    print()
    print("  Location (1,-1,-1)/sqrt(3):")
    print("    - Def 0.1.1: G vertex, phase = 2*pi/3")
    print("    - Existing Python: R vertex, phase = 0")

    print("\n5. CONCLUSION:")
    print("-" * 60)
    print("The existing Python code has a DIFFERENT convention than")
    print("Definition 0.1.1. This is a significant inconsistency that")
    print("affects the physical interpretation of the time emergence figure.")
    print()
    print("RECOMMENDATION: Update the existing Python code to match")
    print("Definition 0.1.1, or document the convention difference clearly.")

    return {
        'discrepancy_found': True,
        'type': 'cyclic_relabeling',
        'mapping': 'R->W, G->R, B->G, W->B (existing Python vs Def 0.1.1)',
        'time_direction_def_0_1_1': '(-1,-1,1)/sqrt(3) (W vertex)',
        'time_direction_existing_python': '(1,1,1)/sqrt(3) (labeled W but is R in Def 0.1.1)',
    }


# =============================================================================
# MAIN EXECUTION
# =============================================================================

if __name__ == "__main__":
    # Print the convention comparison
    print_convention_comparison()

    # Analyze the discrepancy
    discrepancy = analyze_discrepancy()

    # Create the figure based on Definition 0.1.1
    print("\n" + "=" * 80)
    print("GENERATING FIGURE FROM DEFINITION 0.1.1")
    print("=" * 80)

    # Output to parent directory (figures/)
    output_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    metadata = create_fig_def_0_1_1_time_emergence(output_dir)

    print("\n" + "=" * 80)
    print("FIGURE GENERATION COMPLETE")
    print("=" * 80)
    print(f"\nFigure metadata:")
    for key, value in metadata.items():
        print(f"  {key}: {value}")

    print("\n" + "=" * 80)
    print("SUMMARY OF FINDINGS")
    print("=" * 80)
    print("""
1. CONSISTENCY ACROSS SOURCES:
   - Lean and Definition 0.1.1: CONSISTENT
     (Lean uses indices that map correctly to the color labels)

   - Existing Python and Definition 0.1.1: INCONSISTENT
     (R and W are swapped, along with G and B relabeling)

2. SPECIFIC DISCREPANCIES:
   - The existing Python code places W at (1,1,1)/sqrt(3)
   - Definition 0.1.1 places R at (1,1,1)/sqrt(3)
   - This is a cyclic relabeling, NOT a simple swap

3. PHYSICAL IMPACT:
   - The internal time direction lambda should point toward the W vertex
   - In Definition 0.1.1: lambda points toward (-1,-1,1)/sqrt(3)
   - In existing Python: lambda points toward (1,1,1)/sqrt(3)
   - These are DIFFERENT physical directions!

4. NEW FIGURE:
   - The new figure generated by this script uses Definition 0.1.1 coordinates
   - W is correctly placed at (-1,-1,1)/sqrt(3)
   - Time arrow points in the correct direction

5. RECOMMENDATION:
   - Update paper_2_publication_plots.py to match Definition 0.1.1
   - Or document the convention difference in the paper
""")

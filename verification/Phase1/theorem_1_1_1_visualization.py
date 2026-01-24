#!/usr/bin/env python3
"""
Visualization for Theorem 1.1.1: SU(3) Weight Diagram ↔ Stella Octangula Isomorphism

This script creates publication-quality visualizations showing:
1. SU(3) weight diagram (quarks and antiquarks as triangles)
2. The two interlocked tetrahedra (stella octangula) in 3D
3. Projection from stella octangula to weight space
4. Linear transformation mapping tetrahedron → weights
5. Weyl group (S_3) action visualization

Dependencies: numpy, matplotlib
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import os

# Set publication-quality defaults
plt.rcParams.update({
    'font.size': 12,
    'axes.labelsize': 14,
    'axes.titlesize': 14,
    'legend.fontsize': 10,
    'xtick.labelsize': 11,
    'ytick.labelsize': 11,
    'figure.figsize': (10, 8),
    'figure.dpi': 150,
    'savefig.dpi': 200,
    'savefig.bbox': 'tight',
    'lines.linewidth': 2,
    'text.usetex': False,  # Set True if LaTeX is available
})

# Create output directory
PLOT_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'plots')
os.makedirs(PLOT_DIR, exist_ok=True)

# =============================================================================
# SU(3) Weight Vectors
# =============================================================================

# Quark weights in (T_3, Y) coordinates
W_R = np.array([0.5, 1/3])      # Red
W_G = np.array([-0.5, 1/3])     # Green
W_B = np.array([0.0, -2/3])     # Blue

# Antiquark weights (antipodal)
W_RBAR = np.array([-0.5, -1/3]) # Anti-Red
W_GBAR = np.array([0.5, -1/3])  # Anti-Green
W_BBAR = np.array([0.0, 2/3])   # Anti-Blue

# =============================================================================
# Tetrahedron vertices (centered at origin)
# =============================================================================

# First tetrahedron T_+ (represents quarks)
V_0 = np.array([0, 0, 1])                                    # apex (W - singlet)
V_1 = np.array([2*np.sqrt(2)/3, 0, -1/3])                    # R
V_2 = np.array([-np.sqrt(2)/3, np.sqrt(2/3), -1/3])         # G
V_3 = np.array([-np.sqrt(2)/3, -np.sqrt(2/3), -1/3])        # B

# Second tetrahedron T_- = -T_+ (represents antiquarks)
V_0_BAR = -V_0  # apex (W̄ - anti-singlet)
V_1_BAR = -V_1  # R̄
V_2_BAR = -V_2  # Ḡ
V_3_BAR = -V_3  # B̄

# =============================================================================
# Visualization Functions
# =============================================================================

def plot_weight_diagram():
    """
    Figure 1: SU(3) Weight Diagram
    Shows the hexagonal arrangement of quark and antiquark weights.
    """
    fig, ax = plt.subplots(figsize=(10, 9))
    
    # Plot quark triangle
    quark_colors = ['red', 'green', 'blue']
    quark_labels = ['R', 'G', 'B']
    quark_weights = [W_R, W_G, W_B]
    
    for w, c, label in zip(quark_weights, quark_colors, quark_labels):
        ax.scatter(w[0], w[1], c=c, s=200, zorder=5, edgecolors='black', linewidths=1.5)
        ax.annotate(label, (w[0], w[1]), xytext=(10, 10), textcoords='offset points',
                   fontsize=14, fontweight='bold')
    
    # Connect quark triangle
    quark_x = [W_R[0], W_G[0], W_B[0], W_R[0]]
    quark_y = [W_R[1], W_G[1], W_B[1], W_R[1]]
    ax.plot(quark_x, quark_y, 'k-', linewidth=2, label='Quarks (3)')
    
    # Plot antiquark triangle
    antiquark_labels = [r'$\bar{R}$', r'$\bar{G}$', r'$\bar{B}$']
    antiquark_weights = [W_RBAR, W_GBAR, W_BBAR]
    antiquark_colors = ['darkred', 'darkgreen', 'darkblue']
    
    for w, c, label in zip(antiquark_weights, antiquark_colors, antiquark_labels):
        ax.scatter(w[0], w[1], c=c, s=200, zorder=5, edgecolors='black', linewidths=1.5,
                  marker='s')
        ax.annotate(label, (w[0], w[1]), xytext=(10, -15), textcoords='offset points',
                   fontsize=14, fontweight='bold')
    
    # Connect antiquark triangle
    antiquark_x = [W_RBAR[0], W_GBAR[0], W_BBAR[0], W_RBAR[0]]
    antiquark_y = [W_RBAR[1], W_GBAR[1], W_BBAR[1], W_RBAR[1]]
    ax.plot(antiquark_x, antiquark_y, 'k--', linewidth=2, label=r'Antiquarks ($\bar{3}$)')
    
    # Draw antipodal lines
    for w, wbar in [(W_R, W_RBAR), (W_G, W_GBAR), (W_B, W_BBAR)]:
        ax.plot([w[0], wbar[0]], [w[1], wbar[1]], 'gray', linestyle=':', 
               linewidth=1, alpha=0.5)
    
    # Mark the origin
    ax.scatter(0, 0, c='gold', s=150, marker='*', zorder=6, edgecolors='black',
              label='Color singlet')
    
    # Axes
    ax.axhline(y=0, color='gray', linewidth=0.5, linestyle='-')
    ax.axvline(x=0, color='gray', linewidth=0.5, linestyle='-')
    
    ax.set_xlabel(r'$T_3$ (Isospin)', fontsize=14)
    ax.set_ylabel(r'$Y$ (Hypercharge)', fontsize=14)
    ax.set_title('SU(3) Weight Diagram: Fundamental Representations\n' + 
                r'$\mathbf{3}$ (quarks) $\oplus$ $\mathbf{\bar{3}}$ (antiquarks)', fontsize=14)
    
    ax.set_xlim(-0.8, 0.8)
    ax.set_ylim(-0.9, 0.9)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)
    ax.legend(loc='upper right')
    
    # Add annotations
    ax.text(0.05, -0.82, r'$\vec{w}_R + \vec{w}_G + \vec{w}_B = \vec{0}$',
           fontsize=12, bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_weight_diagram.png'))
    plt.close()
    print("Saved: theorem_1_1_1_weight_diagram.png")


def plot_stella_octangula_3d():
    """
    Figure 2: 3D Stella Octangula (Two Interlocked Tetrahedra)
    Shows the dual tetrahedra and their color correspondence.
    """
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # First tetrahedron T_+ (quarks) - transparent blue
    verts_plus = [
        [V_0, V_1, V_2],
        [V_0, V_2, V_3],
        [V_0, V_3, V_1],
        [V_1, V_2, V_3]
    ]
    
    face_colors_plus = ['red', 'green', 'blue', 'lightgray']
    
    # Plot faces with transparency
    for face, fc in zip(verts_plus, face_colors_plus):
        poly = Poly3DCollection([face], alpha=0.3, facecolor=fc, 
                                edgecolor='black', linewidth=1)
        ax.add_collection3d(poly)
    
    # Second tetrahedron T_- (antiquarks) - transparent red
    verts_minus = [
        [V_0_BAR, V_1_BAR, V_2_BAR],
        [V_0_BAR, V_2_BAR, V_3_BAR],
        [V_0_BAR, V_3_BAR, V_1_BAR],
        [V_1_BAR, V_2_BAR, V_3_BAR]
    ]
    
    face_colors_minus = ['darkred', 'darkgreen', 'darkblue', 'gray']
    
    for face, fc in zip(verts_minus, face_colors_minus):
        poly = Poly3DCollection([face], alpha=0.3, facecolor=fc, 
                                edgecolor='black', linewidth=1, linestyle='--')
        ax.add_collection3d(poly)
    
    # Plot vertices for T_+
    ax.scatter(*V_0, c='gold', s=200, marker='*', label='Apex W (singlet)')
    ax.scatter(*V_1, c='red', s=150, marker='o', label='R (Red)')
    ax.scatter(*V_2, c='green', s=150, marker='o', label='G (Green)')
    ax.scatter(*V_3, c='blue', s=150, marker='o', label='B (Blue)')
    
    # Plot vertices for T_-
    ax.scatter(*V_0_BAR, c='purple', s=200, marker='*')
    ax.scatter(*V_1_BAR, c='darkred', s=150, marker='s')
    ax.scatter(*V_2_BAR, c='darkgreen', s=150, marker='s')
    ax.scatter(*V_3_BAR, c='darkblue', s=150, marker='s')
    
    # Add vertex labels
    offset = 0.15
    ax.text(V_0[0], V_0[1], V_0[2]+offset, 'W', fontsize=12, fontweight='bold')
    ax.text(V_1[0]+offset, V_1[1], V_1[2], 'R', fontsize=12, fontweight='bold', color='red')
    ax.text(V_2[0]-offset, V_2[1]+offset, V_2[2], 'G', fontsize=12, fontweight='bold', color='green')
    ax.text(V_3[0]-offset, V_3[1]-offset, V_3[2], 'B', fontsize=12, fontweight='bold', color='blue')
    
    ax.text(V_0_BAR[0], V_0_BAR[1], V_0_BAR[2]-offset, r'$\bar{W}$', fontsize=12, fontweight='bold')
    ax.text(V_1_BAR[0]-offset, V_1_BAR[1], V_1_BAR[2], r'$\bar{R}$', fontsize=12, fontweight='bold', color='darkred')
    ax.text(V_2_BAR[0]+offset, V_2_BAR[1]-offset, V_2_BAR[2], r'$\bar{G}$', fontsize=12, fontweight='bold', color='darkgreen')
    ax.text(V_3_BAR[0]+offset, V_3_BAR[1]+offset, V_3_BAR[2], r'$\bar{B}$', fontsize=12, fontweight='bold', color='darkblue')
    
    # Draw [1,1,1] direction (color-singlet axis)
    ax.plot([0, 0.6], [0, 0.6], [0, 0.6], 'gold', linewidth=2, linestyle='-.')
    ax.text(0.65, 0.65, 0.65, '[1,1,1]\n(singlet)', fontsize=10)
    
    ax.set_xlabel('X', fontsize=12)
    ax.set_ylabel('Y', fontsize=12)
    ax.set_zlabel('Z', fontsize=12)
    ax.set_title('Stella Octangula: Two Interlocked Tetrahedra\n' +
                r'$T_+$ (quarks, solid) and $T_-$ (antiquarks, dashed)', fontsize=14)
    
    ax.set_xlim(-1.2, 1.2)
    ax.set_ylim(-1.2, 1.2)
    ax.set_zlim(-1.2, 1.2)
    
    ax.legend(loc='upper left', fontsize=10)
    
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_stella_octangula_3d.png'))
    plt.close()
    print("Saved: theorem_1_1_1_stella_octangula_3d.png")


def plot_projection_transformation():
    """
    Figure 3: Projection and Linear Transformation
    Shows how tetrahedron vertices project to weight space.
    """
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    
    # Panel A: Projected tetrahedron (raw)
    ax1 = axes[0]
    
    # Project vertices (drop z-coordinate)
    pi_v1 = V_1[:2]
    pi_v2 = V_2[:2]
    pi_v3 = V_3[:2]
    
    # Plot projected triangle
    proj_x = [pi_v1[0], pi_v2[0], pi_v3[0], pi_v1[0]]
    proj_y = [pi_v1[1], pi_v2[1], pi_v3[1], pi_v1[1]]
    
    ax1.plot(proj_x, proj_y, 'b-', linewidth=2, label='Projected tetrahedron')
    ax1.scatter([pi_v1[0], pi_v2[0], pi_v3[0]], [pi_v1[1], pi_v2[1], pi_v3[1]],
               c=['red', 'green', 'blue'], s=150, zorder=5, edgecolors='black')
    ax1.scatter(0, 0, c='gold', s=100, marker='*', label='Apex projects to origin')
    
    ax1.annotate(r'$\pi(v_R)$', pi_v1, xytext=(5, 5), textcoords='offset points', fontsize=11)
    ax1.annotate(r'$\pi(v_G)$', pi_v2, xytext=(-25, 5), textcoords='offset points', fontsize=11)
    ax1.annotate(r'$\pi(v_B)$', pi_v3, xytext=(-25, -15), textcoords='offset points', fontsize=11)
    
    ax1.axhline(y=0, color='gray', linewidth=0.5)
    ax1.axvline(x=0, color='gray', linewidth=0.5)
    ax1.set_xlabel('x', fontsize=12)
    ax1.set_ylabel('y', fontsize=12)
    ax1.set_title('(A) Projected Vertices\n' + r'$\pi(v) = (x, y)$', fontsize=12)
    ax1.set_aspect('equal')
    ax1.grid(True, alpha=0.3)
    ax1.legend(loc='lower right', fontsize=9)
    
    # Panel B: Linear transformation (arrow diagram)
    ax2 = axes[1]
    
    # Compute transformation matrix
    V_matrix = np.column_stack([pi_v1, pi_v2])
    W_matrix = np.column_stack([W_R, W_G])
    A = W_matrix @ np.linalg.inv(V_matrix)
    
    # Show before and after
    ax2.plot(proj_x, proj_y, 'b--', linewidth=1.5, alpha=0.5, label='Before A')
    
    # Transform all points
    A_v1 = A @ pi_v1
    A_v2 = A @ pi_v2
    A_v3 = A @ pi_v3
    
    trans_x = [A_v1[0], A_v2[0], A_v3[0], A_v1[0]]
    trans_y = [A_v1[1], A_v2[1], A_v3[1], A_v1[1]]
    
    ax2.plot(trans_x, trans_y, 'r-', linewidth=2, label='After A')
    ax2.scatter([A_v1[0], A_v2[0], A_v3[0]], [A_v1[1], A_v2[1], A_v3[1]],
               c=['red', 'green', 'blue'], s=150, zorder=5, edgecolors='black')
    
    # Draw transformation arrows
    for pv, av in [(pi_v1, A_v1), (pi_v2, A_v2), (pi_v3, A_v3)]:
        ax2.annotate('', xy=av, xytext=pv,
                    arrowprops=dict(arrowstyle='->', color='gray', lw=1.5))
    
    ax2.axhline(y=0, color='gray', linewidth=0.5)
    ax2.axvline(x=0, color='gray', linewidth=0.5)
    ax2.set_xlabel(r'$T_3$', fontsize=12)
    ax2.set_ylabel('Y', fontsize=12)
    ax2.set_title('(B) Linear Transformation\n' + 
                 r'$\mathbf{A} \cdot \pi(v) = \vec{w}$', fontsize=12)
    ax2.set_aspect('equal')
    ax2.grid(True, alpha=0.3)
    ax2.legend(loc='upper right', fontsize=9)
    
    # Add transformation matrix text
    ax2.text(0.02, 0.02, f'A = [{A[0,0]:.3f}, {A[0,1]:.3f}]\n    [{A[1,0]:.3f}, {A[1,1]:.3f}]',
            transform=ax2.transAxes, fontsize=10, verticalalignment='bottom',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.7))
    
    # Panel C: Final weight diagram match
    ax3 = axes[2]
    
    # Plot SU(3) weights
    ax3.scatter([W_R[0], W_G[0], W_B[0]], [W_R[1], W_G[1], W_B[1]],
               c=['red', 'green', 'blue'], s=200, marker='o', zorder=5,
               edgecolors='black', linewidths=1.5, label='SU(3) weights')
    
    # Plot transformed vertices (should match exactly)
    ax3.scatter([A_v1[0], A_v2[0], A_v3[0]], [A_v1[1], A_v2[1], A_v3[1]],
               c=['red', 'green', 'blue'], s=100, marker='x', zorder=6,
               linewidths=2, label='Transformed vertices')
    
    # Connect triangle
    weight_x = [W_R[0], W_G[0], W_B[0], W_R[0]]
    weight_y = [W_R[1], W_G[1], W_B[1], W_R[1]]
    ax3.plot(weight_x, weight_y, 'k-', linewidth=2)
    
    # Labels
    for w, label in zip([W_R, W_G, W_B], ['R', 'G', 'B']):
        ax3.annotate(label, w, xytext=(8, 8), textcoords='offset points',
                    fontsize=14, fontweight='bold')
    
    ax3.scatter(0, 0, c='gold', s=100, marker='*')
    ax3.axhline(y=0, color='gray', linewidth=0.5)
    ax3.axvline(x=0, color='gray', linewidth=0.5)
    ax3.set_xlabel(r'$T_3$', fontsize=12)
    ax3.set_ylabel('Y', fontsize=12)
    ax3.set_title('(C) Exact Match\n(○ = weights, × = transformed)', fontsize=12)
    ax3.set_aspect('equal')
    ax3.grid(True, alpha=0.3)
    ax3.legend(loc='upper right', fontsize=9)
    
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_projection_transformation.png'))
    plt.close()
    print("Saved: theorem_1_1_1_projection_transformation.png")


def plot_weyl_group_action():
    """
    Figure 4: Weyl Group (S_3) Action on Weights
    Shows how the 6 elements of S_3 permute the color weights.
    """
    fig, axes = plt.subplots(2, 3, figsize=(14, 10))
    
    # Define all 6 elements of S_3 as permutations
    s3_elements = [
        ('Identity', [0, 1, 2]),           # e
        (r'$s_1$ (R↔G)', [1, 0, 2]),       # (12)
        (r'$s_2$ (G↔B)', [0, 2, 1]),       # (23)
        (r'$s_1 s_2 s_1$ (R↔B)', [2, 1, 0]),  # (13)
        (r'$s_1 s_2$ (R→G→B)', [1, 2, 0]), # (123)
        (r'$s_2 s_1$ (R→B→G)', [2, 0, 1])  # (132)
    ]
    
    weights = [W_R, W_G, W_B]
    colors = ['red', 'green', 'blue']
    labels = ['R', 'G', 'B']
    
    for idx, ((name, perm), ax) in enumerate(zip(s3_elements, axes.flat)):
        # Apply permutation
        permuted_weights = [weights[i] for i in perm]
        permuted_colors = [colors[i] for i in perm]
        permuted_labels = [labels[i] for i in perm]
        
        # Plot original triangle (light)
        orig_x = [W_R[0], W_G[0], W_B[0], W_R[0]]
        orig_y = [W_R[1], W_G[1], W_B[1], W_R[1]]
        ax.plot(orig_x, orig_y, 'gray', linewidth=1, linestyle='--', alpha=0.5)
        
        # Plot permuted triangle
        perm_x = [permuted_weights[0][0], permuted_weights[1][0], 
                 permuted_weights[2][0], permuted_weights[0][0]]
        perm_y = [permuted_weights[0][1], permuted_weights[1][1], 
                 permuted_weights[2][1], permuted_weights[0][1]]
        ax.plot(perm_x, perm_y, 'k-', linewidth=2)
        
        # Plot vertices with colors
        for w, pc, pl in zip([W_R, W_G, W_B], permuted_colors, permuted_labels):
            ax.scatter(w[0], w[1], c=pc, s=200, zorder=5, edgecolors='black', linewidths=1.5)
            ax.annotate(pl, w, xytext=(8, 8), textcoords='offset points',
                       fontsize=12, fontweight='bold')
        
        ax.scatter(0, 0, c='gold', s=80, marker='*')
        ax.axhline(y=0, color='gray', linewidth=0.3)
        ax.axvline(x=0, color='gray', linewidth=0.3)
        ax.set_xlim(-0.75, 0.75)
        ax.set_ylim(-0.85, 0.55)
        ax.set_aspect('equal')
        ax.set_title(name, fontsize=12)
        ax.grid(True, alpha=0.2)
        
        # Add permutation notation
        perm_str = f'[{perm[0]}, {perm[1]}, {perm[2]}]'
        ax.text(0.02, 0.98, perm_str, transform=ax.transAxes, fontsize=10,
               verticalalignment='top', bbox=dict(boxstyle='round', facecolor='white', alpha=0.7))
    
    fig.suptitle('Weyl Group $S_3$ Action on SU(3) Weight Space\n' +
                'Colors show where each weight maps to under the permutation', 
                fontsize=14, y=1.02)
    
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_weyl_group.png'))
    plt.close()
    print("Saved: theorem_1_1_1_weyl_group.png")


def plot_killing_vs_euclidean():
    """
    Figure 5: Comparison of Killing Form vs Euclidean Metric
    Shows why the triangle is equilateral in Killing metric but isosceles in Euclidean.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Panel A: Euclidean metric (isosceles)
    ax1 = axes[0]
    
    # Plot triangle
    x = [W_R[0], W_G[0], W_B[0], W_R[0]]
    y = [W_R[1], W_G[1], W_B[1], W_R[1]]
    ax1.plot(x, y, 'b-', linewidth=2)
    
    # Plot vertices
    ax1.scatter([W_R[0], W_G[0], W_B[0]], [W_R[1], W_G[1], W_B[1]],
               c=['red', 'green', 'blue'], s=200, zorder=5, edgecolors='black', linewidths=1.5)
    
    # Labels
    ax1.annotate('R', W_R, xytext=(10, 5), textcoords='offset points', fontsize=14, fontweight='bold')
    ax1.annotate('G', W_G, xytext=(-20, 5), textcoords='offset points', fontsize=14, fontweight='bold')
    ax1.annotate('B', W_B, xytext=(5, -15), textcoords='offset points', fontsize=14, fontweight='bold')
    
    # Calculate and display Euclidean distances
    d_RG = np.linalg.norm(W_R - W_G)
    d_GB = np.linalg.norm(W_G - W_B)
    d_BR = np.linalg.norm(W_B - W_R)
    
    # Add distance labels on edges
    mid_RG = (W_R + W_G) / 2
    mid_GB = (W_G + W_B) / 2
    mid_BR = (W_B + W_R) / 2
    
    ax1.annotate(f'd={d_RG:.3f}', mid_RG, xytext=(0, 8), textcoords='offset points',
                fontsize=10, ha='center', color='blue')
    ax1.annotate(f'd={d_GB:.3f}', mid_GB, xytext=(-25, 0), textcoords='offset points',
                fontsize=10, ha='center', color='blue')
    ax1.annotate(f'd={d_BR:.3f}', mid_BR, xytext=(25, 0), textcoords='offset points',
                fontsize=10, ha='center', color='blue')
    
    ax1.axhline(y=0, color='gray', linewidth=0.5)
    ax1.axvline(x=0, color='gray', linewidth=0.5)
    ax1.set_xlabel(r'$T_3$', fontsize=14)
    ax1.set_ylabel('Y', fontsize=14)
    ax1.set_title('(A) Euclidean Metric $(T_3, Y)$\n' +
                 f'ISOSCELES: d(RG)={d_RG:.3f} ≠ d(GB)=d(BR)={d_GB:.3f}', fontsize=12)
    ax1.set_aspect('equal')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(-0.7, 0.7)
    ax1.set_ylim(-0.85, 0.55)
    
    # Panel B: Killing metric (equilateral)
    ax2 = axes[1]
    
    # Transform to Killing-orthonormal basis
    sqrt12 = np.sqrt(12)
    sqrt3 = np.sqrt(3)
    
    w_R_k = np.array([1, 1/sqrt3]) / sqrt12
    w_G_k = np.array([-1, 1/sqrt3]) / sqrt12
    w_B_k = np.array([0, -2/sqrt3]) / sqrt12
    
    # Scale up for visibility
    scale = 5
    w_R_k *= scale
    w_G_k *= scale
    w_B_k *= scale
    
    # Plot triangle
    x_k = [w_R_k[0], w_G_k[0], w_B_k[0], w_R_k[0]]
    y_k = [w_R_k[1], w_G_k[1], w_B_k[1], w_R_k[0]]
    ax2.plot(x_k, y_k, 'r-', linewidth=2)
    
    # Plot vertices
    ax2.scatter([w_R_k[0], w_G_k[0], w_B_k[0]], [w_R_k[1], w_G_k[1], w_B_k[1]],
               c=['red', 'green', 'blue'], s=200, zorder=5, edgecolors='black', linewidths=1.5)
    
    # Labels
    ax2.annotate('R', w_R_k, xytext=(10, 5), textcoords='offset points', fontsize=14, fontweight='bold')
    ax2.annotate('G', w_G_k, xytext=(-20, 5), textcoords='offset points', fontsize=14, fontweight='bold')
    ax2.annotate('B', w_B_k, xytext=(5, -15), textcoords='offset points', fontsize=14, fontweight='bold')
    
    # Calculate Killing distances
    d_RG_k = np.linalg.norm(w_R_k - w_G_k)
    d_GB_k = np.linalg.norm(w_G_k - w_B_k)
    d_BR_k = np.linalg.norm(w_B_k - w_R_k)
    
    # Add distance labels
    mid_RG_k = (w_R_k + w_G_k) / 2
    mid_GB_k = (w_G_k + w_B_k) / 2
    mid_BR_k = (w_B_k + w_R_k) / 2
    
    ax2.annotate(f'd={d_RG_k:.3f}', mid_RG_k, xytext=(0, 8), textcoords='offset points',
                fontsize=10, ha='center', color='red')
    ax2.annotate(f'd={d_GB_k:.3f}', mid_GB_k, xytext=(-25, 0), textcoords='offset points',
                fontsize=10, ha='center', color='red')
    ax2.annotate(f'd={d_BR_k:.3f}', mid_BR_k, xytext=(25, 0), textcoords='offset points',
                fontsize=10, ha='center', color='red')
    
    ax2.axhline(y=0, color='gray', linewidth=0.5)
    ax2.axvline(x=0, color='gray', linewidth=0.5)
    ax2.set_xlabel(r'$\tilde{T}_3$ (Killing orthonormal)', fontsize=14)
    ax2.set_ylabel(r'$\tilde{Y}$ (Killing orthonormal)', fontsize=14)
    ax2.set_title('(B) Killing Form Metric\n' +
                 f'EQUILATERAL: All sides = {d_RG_k:.3f}', fontsize=12)
    ax2.set_aspect('equal')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_killing_vs_euclidean.png'))
    plt.close()
    print("Saved: theorem_1_1_1_killing_vs_euclidean.png")


def plot_6_plus_2_structure():
    """
    Figure 6: The 6+2 Structure
    Shows how 8 vertices map to 6 weights plus 2 singlet projections.
    """
    fig = plt.figure(figsize=(16, 6))
    
    # Panel A: 3D view of stella octangula
    ax1 = fig.add_subplot(131, projection='3d')
    
    # Draw both tetrahedra
    vertices_plus = [V_0, V_1, V_2, V_3]
    vertices_minus = [V_0_BAR, V_1_BAR, V_2_BAR, V_3_BAR]
    
    # Color vertices
    colors_plus = ['gold', 'red', 'green', 'blue']
    labels_plus = ['W', 'R', 'G', 'B']
    
    for v, c, l in zip(vertices_plus, colors_plus, labels_plus):
        ax1.scatter(*v, c=c, s=150, edgecolors='black')
        ax1.text(v[0], v[1], v[2]+0.1, l, fontsize=11, fontweight='bold')
    
    colors_minus = ['purple', 'darkred', 'darkgreen', 'darkblue']
    labels_minus = [r'$\bar{W}$', r'$\bar{R}$', r'$\bar{G}$', r'$\bar{B}$']
    
    for v, c, l in zip(vertices_minus, colors_minus, labels_minus):
        ax1.scatter(*v, c=c, s=150, marker='s', edgecolors='black')
        ax1.text(v[0], v[1], v[2]-0.15, l, fontsize=11, fontweight='bold')
    
    # Draw edges
    edges_plus = [(0,1), (0,2), (0,3), (1,2), (2,3), (3,1)]
    for i, j in edges_plus:
        ax1.plot([vertices_plus[i][0], vertices_plus[j][0]],
                [vertices_plus[i][1], vertices_plus[j][1]],
                [vertices_plus[i][2], vertices_plus[j][2]], 'b-', alpha=0.5)
    
    for i, j in edges_plus:
        ax1.plot([vertices_minus[i][0], vertices_minus[j][0]],
                [vertices_minus[i][1], vertices_minus[j][1]],
                [vertices_minus[i][2], vertices_minus[j][2]], 'r--', alpha=0.5)
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('(A) Stella Octangula\n8 vertices total', fontsize=12)
    
    # Panel B: Projection diagram
    ax2 = fig.add_subplot(132)
    
    # Draw projection arrows
    ax2.set_xlim(-0.2, 1.2)
    ax2.set_ylim(-0.1, 1.1)
    ax2.axis('off')
    
    # 3D side
    ax2.text(0.05, 0.95, '3D Vertices', fontsize=14, fontweight='bold')
    ax2.text(0.02, 0.85, '• W, R, G, B (T₊)', fontsize=11)
    ax2.text(0.02, 0.75, r'• $\bar{W}$, $\bar{R}$, $\bar{G}$, $\bar{B}$ (T₋)', fontsize=11)
    ax2.text(0.02, 0.60, '8 vertices total', fontsize=12, style='italic')
    
    # Arrow
    ax2.annotate('', xy=(0.95, 0.5), xytext=(0.55, 0.5),
                arrowprops=dict(arrowstyle='->', lw=3, color='black'))
    ax2.text(0.75, 0.55, r'$\pi: z \to 0$', fontsize=12, ha='center')
    
    # 2D side
    ax2.text(0.55, 0.95, '2D Weight Space', fontsize=14, fontweight='bold')
    ax2.text(0.55, 0.85, '• R, G, B → weights', fontsize=11, color='blue')
    ax2.text(0.55, 0.75, r'• $\bar{R}$, $\bar{G}$, $\bar{B}$ → anti-weights', fontsize=11, color='red')
    ax2.text(0.55, 0.60, r'• W, $\bar{W}$ → origin (0,0)', fontsize=11, color='gold')
    ax2.text(0.55, 0.45, '6 distinct points', fontsize=12, style='italic', color='blue')
    ax2.text(0.55, 0.35, '+ 2 singlet projections', fontsize=12, style='italic', color='gold')
    
    # Summary box
    box_text = '6 + 2 = 8\n6 color weights\n2 singlet directions'
    ax2.text(0.75, 0.12, box_text, fontsize=12, ha='center',
            bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.7))
    
    ax2.set_title('(B) Projection Map', fontsize=12)
    
    # Panel C: Weight space with singlet marker
    ax3 = fig.add_subplot(133)
    
    # Plot all 6 weights
    weights_all = [W_R, W_G, W_B, W_RBAR, W_GBAR, W_BBAR]
    colors_all = ['red', 'green', 'blue', 'darkred', 'darkgreen', 'darkblue']
    labels_all = ['R', 'G', 'B', r'$\bar{R}$', r'$\bar{G}$', r'$\bar{B}$']
    
    for w, c, l in zip(weights_all, colors_all, labels_all):
        ax3.scatter(w[0], w[1], c=c, s=200, edgecolors='black', linewidths=1.5, zorder=5)
        offset = (10, 5) if w[1] > 0 else (10, -15)
        ax3.annotate(l, w, xytext=offset, textcoords='offset points',
                    fontsize=12, fontweight='bold')
    
    # Mark singlet (origin) prominently
    ax3.scatter(0, 0, c='gold', s=300, marker='*', zorder=6, edgecolors='black',
               linewidths=1.5, label=r'Singlet ($\pi(W) = \pi(\bar{W})$)')
    
    # Draw triangles
    q_x = [W_R[0], W_G[0], W_B[0], W_R[0]]
    q_y = [W_R[1], W_G[1], W_B[1], W_R[1]]
    ax3.plot(q_x, q_y, 'b-', linewidth=2, label='Quarks (3)')
    
    aq_x = [W_RBAR[0], W_GBAR[0], W_BBAR[0], W_RBAR[0]]
    aq_y = [W_RBAR[1], W_GBAR[1], W_BBAR[1], W_RBAR[1]]
    ax3.plot(aq_x, aq_y, 'r--', linewidth=2, label=r'Antiquarks ($\bar{3}$)')
    
    ax3.axhline(y=0, color='gray', linewidth=0.5)
    ax3.axvline(x=0, color='gray', linewidth=0.5)
    ax3.set_xlabel(r'$T_3$', fontsize=14)
    ax3.set_ylabel('Y', fontsize=14)
    ax3.set_title('(C) Weight Space\n6 weights + singlet origin', fontsize=12)
    ax3.set_aspect('equal')
    ax3.grid(True, alpha=0.3)
    ax3.legend(loc='lower right', fontsize=9)
    ax3.set_xlim(-0.75, 0.75)
    ax3.set_ylim(-0.85, 0.85)
    
    plt.tight_layout()
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_6_plus_2_structure.png'))
    plt.close()
    print("Saved: theorem_1_1_1_6_plus_2_structure.png")


def plot_summary():
    """
    Figure 7: Summary Diagram
    A single comprehensive visualization of the key isomorphism.
    """
    fig = plt.figure(figsize=(16, 10))
    
    # Create a 2x2 grid with the left column for 3D and right for 2D
    gs = fig.add_gridspec(2, 2, width_ratios=[1.2, 1], height_ratios=[1, 1],
                          hspace=0.25, wspace=0.3)
    
    # Panel A: 3D Stella Octangula (top-left)
    ax1 = fig.add_subplot(gs[0, 0], projection='3d')
    
    # Draw tetrahedra with nice colors
    vertices_plus = [V_0, V_1, V_2, V_3]
    vertices_minus = [V_0_BAR, V_1_BAR, V_2_BAR, V_3_BAR]
    
    # T_+ faces
    faces_plus = [
        [V_0, V_1, V_2],
        [V_0, V_2, V_3],
        [V_0, V_3, V_1],
        [V_1, V_2, V_3]
    ]
    for face in faces_plus:
        poly = Poly3DCollection([face], alpha=0.25, facecolor='cyan', 
                                edgecolor='blue', linewidth=1)
        ax1.add_collection3d(poly)
    
    # T_- faces
    faces_minus = [
        [V_0_BAR, V_1_BAR, V_2_BAR],
        [V_0_BAR, V_2_BAR, V_3_BAR],
        [V_0_BAR, V_3_BAR, V_1_BAR],
        [V_1_BAR, V_2_BAR, V_3_BAR]
    ]
    for face in faces_minus:
        poly = Poly3DCollection([face], alpha=0.25, facecolor='pink', 
                                edgecolor='red', linewidth=1)
        ax1.add_collection3d(poly)
    
    # Vertices
    colors_v = ['gold', 'red', 'green', 'blue', 'purple', 'darkred', 'darkgreen', 'darkblue']
    all_v = vertices_plus + vertices_minus
    labels_v = ['W', 'R', 'G', 'B', r'$\bar{W}$', r'$\bar{R}$', r'$\bar{G}$', r'$\bar{B}$']
    
    for v, c in zip(all_v, colors_v):
        ax1.scatter(*v, c=c, s=100, edgecolors='black', zorder=5)
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title(r'Stella Octangula: $T_+$ ∪ $T_-$', fontsize=14)
    ax1.set_xlim(-1.1, 1.1)
    ax1.set_ylim(-1.1, 1.1)
    ax1.set_zlim(-1.1, 1.1)
    
    # Panel B: Weight diagram (top-right)
    ax2 = fig.add_subplot(gs[0, 1])
    
    weights_all = [W_R, W_G, W_B, W_RBAR, W_GBAR, W_BBAR]
    colors_w = ['red', 'green', 'blue', 'darkred', 'darkgreen', 'darkblue']
    labels_w = ['R', 'G', 'B', r'$\bar{R}$', r'$\bar{G}$', r'$\bar{B}$']
    
    for w, c, l in zip(weights_all, colors_w, labels_w):
        ax2.scatter(w[0], w[1], c=c, s=150, edgecolors='black', zorder=5)
        offset = (8, 5) if 'bar' not in l else (8, -12)
        ax2.annotate(l, w, xytext=offset, textcoords='offset points',
                    fontsize=11, fontweight='bold')
    
    # Triangles
    q_x = [W_R[0], W_G[0], W_B[0], W_R[0]]
    q_y = [W_R[1], W_G[1], W_B[1], W_R[1]]
    ax2.plot(q_x, q_y, 'b-', linewidth=2)
    
    aq_x = [W_RBAR[0], W_GBAR[0], W_BBAR[0], W_RBAR[0]]
    aq_y = [W_RBAR[1], W_GBAR[1], W_BBAR[1], W_RBAR[1]]
    ax2.plot(aq_x, aq_y, 'r--', linewidth=2)
    
    ax2.scatter(0, 0, c='gold', s=150, marker='*', zorder=6, edgecolors='black')
    ax2.axhline(y=0, color='gray', linewidth=0.5)
    ax2.axvline(x=0, color='gray', linewidth=0.5)
    ax2.set_xlabel(r'$T_3$ (Isospin)', fontsize=12)
    ax2.set_ylabel('Y (Hypercharge)', fontsize=12)
    ax2.set_title('SU(3) Weight Diagram: 3 ⊕ 3̄', fontsize=14)
    ax2.set_aspect('equal')
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(-0.7, 0.7)
    ax2.set_ylim(-0.8, 0.8)
    
    # Panel C: The isomorphism (bottom, spanning both columns)
    ax3 = fig.add_subplot(gs[1, :])
    ax3.axis('off')
    
    # Create a nice table/diagram showing the bijection
    ax3.text(0.5, 0.95, 'Theorem 1.1.1: SU(3) ↔ Stella Octangula Isomorphism', 
            fontsize=16, fontweight='bold', ha='center', transform=ax3.transAxes)
    
    # Bijection table
    table_text = """
    ┌─────────────────────────────────────────────────────────────────────────────┐
    │  Stella Octangula                  │  SU(3) Weight Space                    │
    ├─────────────────────────────────────────────────────────────────────────────┤
    │  6 color vertices (R,G,B,R̄,Ḡ,B̄)   ↔  6 weight vectors (3 ⊕ 3̄)             │
    │  2 apex vertices (W, W̄)            ↔  2 singlet projections (origin)       │
    │  T₊ tetrahedron (solid)            ↔  Quark representation 3               │
    │  T₋ tetrahedron (dual)             ↔  Antiquark representation 3̄            │
    │  Point reflection T₋ = -T₊         ↔  Charge conjugation (w → -w)          │
    │  Stab(apex) ≅ S₃                   ↔  Weyl group W(su(3)) ≅ S₃             │
    │  Sum of base vertices = 0          ↔  Color confinement (w_R+w_G+w_B = 0)  │
    └─────────────────────────────────────────────────────────────────────────────┘
    """
    ax3.text(0.5, 0.5, table_text, fontsize=11, ha='center', va='center',
            family='monospace', transform=ax3.transAxes,
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))
    
    # Key equations
    ax3.text(0.5, 0.08, 
            r'Linear Map: $\mathbf{A} \cdot \pi(v_c) = \vec{w}_c$  |  ' +
            r'Symmetry: Stab$_{S_4}$(apex) $\cong$ W(su(3)) $\cong$ $S_3$',
            fontsize=12, ha='center', transform=ax3.transAxes,
            bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.5))
    
    plt.savefig(os.path.join(PLOT_DIR, 'theorem_1_1_1_summary.png'))
    plt.close()
    print("Saved: theorem_1_1_1_summary.png")


# =============================================================================
# Main
# =============================================================================

def main():
    """Generate all visualization figures for Theorem 1.1.1."""
    print("=" * 70)
    print("Generating Visualizations for Theorem 1.1.1")
    print("SU(3) Weight Diagram ↔ Stella Octangula Isomorphism")
    print("=" * 70)
    print()
    print(f"Output directory: {PLOT_DIR}")
    print()
    
    print("Generating figures...")
    print()
    
    # Generate all figures
    plot_weight_diagram()
    plot_stella_octangula_3d()
    plot_projection_transformation()
    plot_weyl_group_action()
    plot_killing_vs_euclidean()
    plot_6_plus_2_structure()
    plot_summary()
    
    print()
    print("=" * 70)
    print("All visualizations generated successfully!")
    print("=" * 70)


if __name__ == "__main__":
    main()

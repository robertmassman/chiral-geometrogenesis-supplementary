#!/usr/bin/env python3
"""
Visualizations for Theorem 0.3.1: W-Direction Correspondence

This module generates plots to visualize the key geometric aspects of Theorem 0.3.1:
1. Stella octangula (two interlocked tetrahedra) with W-direction highlighted
2. R-G-B plane and perpendicular W-axis
3. 24-cell projection showing structure preservation
4. W(F₄) rotation correspondence diagram
5. Embedding chain visualization
6. Tetrahedral angle geometry

Reference: docs/proofs/Phase0/Theorem-0.3.1-W-Direction-Correspondence.md

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.colors import Normalize
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection
from pathlib import Path
import warnings

# Suppress some matplotlib warnings
warnings.filterwarnings('ignore', category=UserWarning)

# Import from verification module
from theorem_0_3_1_w_direction_correspondence_verification import (
    STELLA_VERTICES, W, R, G, B, W_hat, R_hat, G_hat, B_hat,
    VERTICES_16CELL, VERTICES_TESSERACT, VERTICES_24CELL,
    get_alternative_wf4_rotation, PARAMS
)

# Output directory for plots
PLOT_DIR = Path(__file__).parent.parent / 'plots'
PLOT_DIR.mkdir(exist_ok=True)


def set_plot_style():
    """Set consistent plot style."""
    plt.rcParams.update({
        'font.size': 12,
        'axes.titlesize': 14,
        'axes.labelsize': 12,
        'xtick.labelsize': 10,
        'ytick.labelsize': 10,
        'legend.fontsize': 10,
        'figure.figsize': (12, 10),
        'figure.dpi': 150,
        'savefig.dpi': 150,
        'savefig.bbox': 'tight'
    })


def plot_stella_octangula_with_w_axis():
    """
    Plot the stella octangula (two interlocked tetrahedra) highlighting
    the W-direction perpendicular to the R-G-B plane.
    """
    fig = plt.figure(figsize=(14, 6))
    
    # Plot 1: Full stella octangula
    ax1 = fig.add_subplot(121, projection='3d')
    
    # Tetrahedron T+ vertices
    t_plus = np.array([W, R, G, B])
    t_minus = np.array([
        STELLA_VERTICES['W_bar'],
        STELLA_VERTICES['R_bar'],
        STELLA_VERTICES['G_bar'],
        STELLA_VERTICES['B_bar']
    ])
    
    # Plot T+ tetrahedron faces
    faces_plus = [
        [t_plus[0], t_plus[1], t_plus[2]],  # W-R-G
        [t_plus[0], t_plus[2], t_plus[3]],  # W-G-B
        [t_plus[0], t_plus[3], t_plus[1]],  # W-B-R
        [t_plus[1], t_plus[2], t_plus[3]],  # R-G-B
    ]
    
    faces_minus = [
        [t_minus[0], t_minus[1], t_minus[2]],
        [t_minus[0], t_minus[2], t_minus[3]],
        [t_minus[0], t_minus[3], t_minus[1]],
        [t_minus[1], t_minus[2], t_minus[3]],
    ]
    
    # Plot T+ with blue faces
    poly_plus = Poly3DCollection(faces_plus, alpha=0.3, facecolor='blue', edgecolor='blue')
    ax1.add_collection3d(poly_plus)
    
    # Plot T- with red faces
    poly_minus = Poly3DCollection(faces_minus, alpha=0.3, facecolor='red', edgecolor='red')
    ax1.add_collection3d(poly_minus)
    
    # Plot vertices
    colors_plus = ['gold', 'red', 'green', 'blue']
    labels_plus = ['W (1,1,1)', 'R (1,-1,-1)', 'G (-1,1,-1)', 'B (-1,-1,1)']
    for v, c, l in zip(t_plus, colors_plus, labels_plus):
        ax1.scatter(*v, c=c, s=200, edgecolor='black', linewidth=2, label=l, zorder=5)
    
    # Plot T- vertices (smaller)
    for v in t_minus:
        ax1.scatter(*v, c='gray', s=100, alpha=0.6, zorder=4)
    
    # Draw W-axis direction
    scale = 2.5
    ax1.quiver(0, 0, 0, W_hat[0]*scale, W_hat[1]*scale, W_hat[2]*scale,
               color='gold', linewidth=3, arrow_length_ratio=0.1, label='W-axis')
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Stella Octangula: Two Interlocked Tetrahedra\n(T+ in blue, T- in red)')
    ax1.legend(loc='upper left', fontsize=8)
    ax1.set_box_aspect([1, 1, 1])
    
    # Plot 2: W perpendicular to R-G-B plane
    ax2 = fig.add_subplot(122, projection='3d')
    
    # Plot R-G-B plane
    rgb_vertices = np.array([R, G, B])
    rgb_plane = [[R, G, B]]
    poly_rgb = Poly3DCollection(rgb_plane, alpha=0.4, facecolor='cyan', edgecolor='black')
    ax2.add_collection3d(poly_rgb)
    
    # Plot R, G, B vertices
    ax2.scatter(*R, c='red', s=200, edgecolor='black', linewidth=2, label='R (1,-1,-1)')
    ax2.scatter(*G, c='green', s=200, edgecolor='black', linewidth=2, label='G (-1,1,-1)')
    ax2.scatter(*B, c='blue', s=200, edgecolor='black', linewidth=2, label='B (-1,-1,1)')
    ax2.scatter(*W, c='gold', s=200, edgecolor='black', linewidth=2, label='W (1,1,1)')
    ax2.scatter(0, 0, 0, c='black', s=100, marker='x', label='Origin')
    
    # Draw W-axis (normal to R-G-B plane)
    ax2.quiver(0, 0, 0, W[0]*1.2, W[1]*1.2, W[2]*1.2,
               color='gold', linewidth=3, arrow_length_ratio=0.1)
    
    # Draw vectors in R-G-B plane
    ax2.quiver(R[0], R[1], R[2], (G-R)[0], (G-R)[1], (G-R)[2],
               color='purple', linewidth=2, arrow_length_ratio=0.1, label='v₁ = G-R')
    ax2.quiver(R[0], R[1], R[2], (B-R)[0], (B-R)[1], (B-R)[2],
               color='orange', linewidth=2, arrow_length_ratio=0.1, label='v₂ = B-R')
    
    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title('W-Direction Perpendicular to R-G-B Plane\nW = (1,1,1)/√3 ⊥ plane')
    ax2.legend(loc='upper left', fontsize=8)
    ax2.set_box_aspect([1, 1, 1])
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_3_1_stella_octangula.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_3_1_stella_octangula.png'}")


def plot_projection_correspondence():
    """
    Visualize how the 24-cell projects to 3D, preserving the stella structure.
    """
    fig = plt.figure(figsize=(16, 6))
    
    # Plot 1: 4D → 3D projection of 24-cell (shown via projections)
    ax1 = fig.add_subplot(131, projection='3d')
    
    # Project tesseract vertices to 3D
    tesseract_3d = np.array([v[:3] for v in VERTICES_TESSERACT])
    
    # Project 16-cell vertices to 3D
    sixteencell_3d = np.array([v[:3] for v in VERTICES_16CELL])
    
    # Plot tesseract projection (forms cube)
    ax1.scatter(tesseract_3d[:, 0], tesseract_3d[:, 1], tesseract_3d[:, 2],
                c='blue', s=100, label='Tesseract → Cube', alpha=0.8)
    
    # Draw cube edges
    cube_edges = []
    for i, v1 in enumerate(tesseract_3d):
        for j, v2 in enumerate(tesseract_3d):
            if i < j and np.sum(np.abs(v1 - v2) > 0) == 1:  # Adjacent if differ in 1 coord
                cube_edges.append([v1, v2])
    
    if cube_edges:
        edge_collection = Line3DCollection(cube_edges, colors='blue', alpha=0.3)
        ax1.add_collection3d(edge_collection)
    
    # Plot 16-cell projection (forms octahedron + origin)
    # Separate origin points
    non_origin = [v for v in sixteencell_3d if not np.allclose(v, np.zeros(3))]
    origin_pts = [v for v in sixteencell_3d if np.allclose(v, np.zeros(3))]
    
    if non_origin:
        non_origin = np.array(non_origin)
        ax1.scatter(non_origin[:, 0], non_origin[:, 1], non_origin[:, 2],
                    c='red', s=100, marker='^', label='16-cell → Octahedron', alpha=0.8)
    
    # Mark origin (where ±w vertices collapse)
    ax1.scatter(0, 0, 0, c='black', s=200, marker='x', 
                label='±w → Origin', linewidth=3)
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('24-Cell Projection to 3D\nπ(x,y,z,w) = (x,y,z)')
    ax1.legend(fontsize=8)
    ax1.set_box_aspect([1, 1, 1])
    
    # Plot 2: W(F₄) rotation mapping ê_w to W direction
    ax2 = fig.add_subplot(132, projection='3d')
    
    R_mat = get_alternative_wf4_rotation()
    e_w = np.array([0, 0, 0, 1])
    rotated = R_mat @ e_w  # = (1,1,1,1)/2
    projected = rotated[:3]  # = (1/2, 1/2, 1/2)
    
    # Draw coordinate axes
    for i, (color, label) in enumerate(zip(['red', 'green', 'blue'], ['X', 'Y', 'Z'])):
        ax2.quiver(0, 0, 0, 1.5*(i==0), 1.5*(i==1), 1.5*(i==2),
                   color=color, linewidth=2, arrow_length_ratio=0.1)
    
    # Draw the projected vector (proportional to W)
    ax2.quiver(0, 0, 0, projected[0]*2, projected[1]*2, projected[2]*2,
               color='gold', linewidth=4, arrow_length_ratio=0.1,
               label=f'π(R·ê_w) = {projected}')
    
    # Draw W direction for comparison
    ax2.quiver(0, 0, 0, W_hat[0]*1.2, W_hat[1]*1.2, W_hat[2]*1.2,
               color='purple', linewidth=2, arrow_length_ratio=0.1,
               label=f'Ŵ = (1,1,1)/√3', linestyle='--')
    
    # Add annotation
    ax2.text(0.7, 0.7, 0.7, 'R·ê_w = (1,1,1,1)/2\n→ projects to W direction',
             fontsize=9, ha='center')
    
    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title('W(F₄) Rotation Correspondence\nR·ê_w → π → W direction')
    ax2.legend(fontsize=8)
    ax2.set_box_aspect([1, 1, 1])
    
    # Plot 3: Equidistance visualization
    ax3 = fig.add_subplot(133, projection='3d')
    
    # Unit sphere (partial)
    u = np.linspace(0, 2 * np.pi, 30)
    v = np.linspace(0, np.pi, 20)
    x = np.outer(np.cos(u), np.sin(v))
    y = np.outer(np.sin(u), np.sin(v))
    z = np.outer(np.ones(np.size(u)), np.cos(v))
    ax3.plot_surface(x, y, z, alpha=0.1, color='gray')
    
    # Plot normalized vertices on sphere
    ax3.scatter(*W_hat, c='gold', s=200, edgecolor='black', linewidth=2, label='Ŵ')
    ax3.scatter(*R_hat, c='red', s=200, edgecolor='black', linewidth=2, label='R̂')
    ax3.scatter(*G_hat, c='green', s=200, edgecolor='black', linewidth=2, label='Ĝ')
    ax3.scatter(*B_hat, c='blue', s=200, edgecolor='black', linewidth=2, label='B̂')
    
    # Draw equal-length chords from W to R, G, B
    dist = np.sqrt(8/3)
    for v_hat, color in [(R_hat, 'red'), (G_hat, 'green'), (B_hat, 'blue')]:
        ax3.plot([W_hat[0], v_hat[0]], [W_hat[1], v_hat[1]], [W_hat[2], v_hat[2]],
                 color=color, linewidth=2, linestyle='--')
    
    ax3.text(0, 0, -1.3, f'|Ŵ - R̂| = |Ŵ - Ĝ| = |Ŵ - B̂| = √(8/3) ≈ {dist:.3f}',
             fontsize=9, ha='center')
    
    ax3.set_xlabel('X')
    ax3.set_ylabel('Y')
    ax3.set_zlabel('Z')
    ax3.set_title('Equidistance: W Equidistant from R, G, B\n(On unit sphere)')
    ax3.legend(fontsize=8)
    ax3.set_box_aspect([1, 1, 1])
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_3_1_projection_correspondence.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_3_1_projection_correspondence.png'}")


def plot_tetrahedral_angles():
    """
    Visualize the tetrahedral angle geometry.
    """
    fig = plt.figure(figsize=(14, 6))
    
    # Plot 1: Tetrahedral dot products
    ax1 = fig.add_subplot(121, projection='3d')
    
    # Draw tetrahedron T+
    vertices = np.array([W_hat, R_hat, G_hat, B_hat])
    
    # Draw edges
    edges = [[0,1], [0,2], [0,3], [1,2], [1,3], [2,3]]
    for i, j in edges:
        ax1.plot([vertices[i,0], vertices[j,0]],
                 [vertices[i,1], vertices[j,1]],
                 [vertices[i,2], vertices[j,2]],
                 'k-', linewidth=1.5, alpha=0.6)
    
    # Plot vertices
    ax1.scatter(*W_hat, c='gold', s=200, edgecolor='black', linewidth=2, label='Ŵ')
    ax1.scatter(*R_hat, c='red', s=200, edgecolor='black', linewidth=2, label='R̂')
    ax1.scatter(*G_hat, c='green', s=200, edgecolor='black', linewidth=2, label='Ĝ')
    ax1.scatter(*B_hat, c='blue', s=200, edgecolor='black', linewidth=2, label='B̂')
    ax1.scatter(0, 0, 0, c='black', s=100, marker='x', label='Origin')
    
    # Draw lines from origin to vertices
    for v, c in [(W_hat, 'gold'), (R_hat, 'red'), (G_hat, 'green'), (B_hat, 'blue')]:
        ax1.plot([0, v[0]], [0, v[1]], [0, v[2]], c=c, linewidth=2, alpha=0.5)
    
    # Annotate angle
    angle_deg = np.degrees(np.arccos(-1/3))
    ax1.text(0, 0, -0.8, f'All angles = {angle_deg:.2f}°\ncos⁻¹(-1/3)', 
             fontsize=10, ha='center')
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Tetrahedral Angles\nAll vertex-origin-vertex angles = 109.47°')
    ax1.legend(fontsize=9)
    ax1.set_box_aspect([1, 1, 1])
    
    # Plot 2: Dot product matrix visualization
    ax2 = fig.add_subplot(122)
    
    labels = ['Ŵ', 'R̂', 'Ĝ', 'B̂']
    vecs = [W_hat, R_hat, G_hat, B_hat]
    
    dot_matrix = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            dot_matrix[i, j] = np.dot(vecs[i], vecs[j])
    
    im = ax2.imshow(dot_matrix, cmap='RdBu', vmin=-1, vmax=1)
    
    # Add text annotations
    for i in range(4):
        for j in range(4):
            text_color = 'white' if abs(dot_matrix[i, j]) > 0.5 else 'black'
            ax2.text(j, i, f'{dot_matrix[i, j]:.3f}', ha='center', va='center',
                     fontsize=11, color=text_color)
    
    ax2.set_xticks(range(4))
    ax2.set_yticks(range(4))
    ax2.set_xticklabels(labels)
    ax2.set_yticklabels(labels)
    ax2.set_title('Dot Product Matrix\nDiagonal = 1, Off-diagonal = -1/3')
    
    cbar = plt.colorbar(im, ax=ax2)
    cbar.set_label('Dot Product')
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_3_1_tetrahedral_angles.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_3_1_tetrahedral_angles.png'}")


def plot_symmetry_factorization():
    """
    Visualize the symmetry group factorization |W(F₄)| = 1152 = 24 × 48.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Plot 1: Symmetry hierarchy
    ax1 = axes[0]
    
    groups = ['Stella\nS₄×Z₂', '16-cell\nB₄', '24-cell\nW(F₄)']
    orders = [48, 384, 1152]
    colors = ['lightblue', 'lightgreen', 'lightyellow']
    
    bars = ax1.bar(groups, orders, color=colors, edgecolor='black', linewidth=2)
    
    # Add order labels
    for bar, order in zip(bars, orders):
        ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 30,
                 str(order), ha='center', fontsize=14, fontweight='bold')
    
    # Add factorization annotations
    ax1.text(0, 48/2, '24×2', ha='center', va='center', fontsize=12)
    ax1.text(1, 384/2, '16×24', ha='center', va='center', fontsize=12)
    ax1.text(2, 1152/2, '24×48', ha='center', va='center', fontsize=12, fontweight='bold')
    
    ax1.set_ylabel('Group Order')
    ax1.set_title('Symmetry Group Orders\nEmbedding Chain: Stella ⊂ 16-cell ⊂ 24-cell')
    ax1.set_ylim(0, 1300)
    
    # Plot 2: Factorization interpretation
    ax2 = axes[1]
    
    # Create a diagram showing the factorization
    ax2.axis('off')
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 10)
    
    # Main equation
    ax2.text(5, 9, '|W(F₄)| = 1152 = 24 × 48', fontsize=20, ha='center', 
             fontweight='bold', bbox=dict(boxstyle='round', facecolor='lightyellow'))
    
    # Left factor
    ax2.annotate('', xy=(2.5, 6), xytext=(4, 7.5),
                 arrowprops=dict(arrowstyle='->', color='blue', lw=2))
    ax2.text(1.5, 5, '24', fontsize=24, ha='center', color='blue', fontweight='bold')
    ax2.text(1.5, 4, '# of 24-cell\nvertices', fontsize=11, ha='center')
    ax2.text(1.5, 3, '(Temporal\nenhancement)', fontsize=10, ha='center', style='italic')
    
    # Right factor
    ax2.annotate('', xy=(7.5, 6), xytext=(6, 7.5),
                 arrowprops=dict(arrowstyle='->', color='red', lw=2))
    ax2.text(8.5, 5, '48', fontsize=24, ha='center', color='red', fontweight='bold')
    ax2.text(8.5, 4, 'Stella octangula\nsymmetry', fontsize=11, ha='center')
    ax2.text(8.5, 3, '(Spatial\npreserved)', fontsize=10, ha='center', style='italic')
    
    # Physical interpretation
    ax2.text(5, 1.5, 'Physical Interpretation:', fontsize=12, ha='center', fontweight='bold')
    ax2.text(5, 0.8, 'The 24-fold factor corresponds to transformations\nthat permute temporal phases while preserving spatial (stella) structure',
             fontsize=10, ha='center', style='italic')
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_3_1_symmetry_factorization.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_3_1_symmetry_factorization.png'}")


def plot_wf4_rotation_visualization():
    """
    Visualize the W(F₄) rotation matrix and its action.
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Plot 1: Rotation matrix as heatmap
    ax1 = axes[0]
    
    R = get_alternative_wf4_rotation()
    
    im = ax1.imshow(R, cmap='RdBu', vmin=-0.5, vmax=0.5)
    
    # Add text annotations
    for i in range(4):
        for j in range(4):
            text_color = 'white' if abs(R[i, j]) > 0.3 else 'black'
            ax1.text(j, i, f'{R[i, j]:.2f}', ha='center', va='center',
                     fontsize=14, color=text_color)
    
    ax1.set_xticks(range(4))
    ax1.set_yticks(range(4))
    ax1.set_xticklabels(['x', 'y', 'z', 'w'])
    ax1.set_yticklabels(['x', 'y', 'z', 'w'])
    ax1.set_title('W(F₄) Rotation Matrix R\n(Each entry = ±1/2)')
    
    cbar = plt.colorbar(im, ax=ax1)
    cbar.set_label('Matrix Entry')
    
    # Plot 2: Action on basis vectors
    ax2 = axes[1]
    ax2.axis('off')
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 10)
    
    ax2.text(5, 9.5, 'W(F₄) Rotation Action', fontsize=16, ha='center', fontweight='bold')
    
    # Show mappings
    mappings = [
        ('ê_x = (1,0,0,0)', '(1,1,1,1)/2', 'Type A → Type B'),
        ('ê_y = (0,1,0,0)', '(1,1,-1,-1)/2', 'Type A → Type B'),
        ('ê_z = (0,0,1,0)', '(1,-1,1,-1)/2', 'Type A → Type B'),
        ('ê_w = (0,0,0,1)', '(1,-1,-1,1)/2', 'Type A → Type B'),
    ]
    
    y_pos = 8
    for src, dst, note in mappings:
        ax2.text(1, y_pos, src, fontsize=11, ha='left', family='monospace')
        ax2.annotate('', xy=(5.5, y_pos), xytext=(4.5, y_pos),
                     arrowprops=dict(arrowstyle='->', color='blue', lw=2))
        ax2.text(6, y_pos, dst, fontsize=11, ha='left', family='monospace')
        ax2.text(9.5, y_pos, note, fontsize=9, ha='right', style='italic', color='gray')
        y_pos -= 1.5
    
    # Key insight box
    ax2.text(5, 2.5, 'Key Correspondence:', fontsize=12, ha='center', fontweight='bold',
             bbox=dict(boxstyle='round', facecolor='lightyellow'))
    ax2.text(5, 1.5, 'R · ê_w = (1,-1,-1,1)/2  or  R · ê_w = (1,1,1,1)/2',
             fontsize=11, ha='center', family='monospace')
    ax2.text(5, 0.8, 'Projects to: π(R·ê_w) ∝ (1,1,1) = W direction',
             fontsize=11, ha='center')
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_3_1_wf4_rotation.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_3_1_wf4_rotation.png'}")


def plot_embedding_chain():
    """
    Visualize the embedding chain: Stella ⊂ 16-cell ⊂ 24-cell.
    """
    fig = plt.figure(figsize=(16, 5))
    
    # Plot 1: Stella octangula (3D)
    ax1 = fig.add_subplot(131, projection='3d')
    
    # Draw two tetrahedra
    t_plus = np.array([W, R, G, B]) / np.sqrt(3)  # Normalized
    t_minus = np.array([
        STELLA_VERTICES['W_bar'],
        STELLA_VERTICES['R_bar'],
        STELLA_VERTICES['G_bar'],
        STELLA_VERTICES['B_bar']
    ]) / np.sqrt(3)
    
    # Draw edges
    edges_plus = [[0,1], [0,2], [0,3], [1,2], [1,3], [2,3]]
    for i, j in edges_plus:
        ax1.plot([t_plus[i,0], t_plus[j,0]],
                 [t_plus[i,1], t_plus[j,1]],
                 [t_plus[i,2], t_plus[j,2]],
                 'b-', linewidth=2, alpha=0.8)
        ax1.plot([t_minus[i,0], t_minus[j,0]],
                 [t_minus[i,1], t_minus[j,1]],
                 [t_minus[i,2], t_minus[j,2]],
                 'r-', linewidth=2, alpha=0.8)
    
    # Plot vertices
    for v in t_plus:
        ax1.scatter(*v, c='blue', s=100, edgecolor='black')
    for v in t_minus:
        ax1.scatter(*v, c='red', s=100, edgecolor='black')
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('Stella Octangula\n8 vertices (3D)')
    ax1.set_box_aspect([1, 1, 1])
    
    # Plot 2: 16-cell projection
    ax2 = fig.add_subplot(132, projection='3d')
    
    # Project 16-cell to 3D
    sixteencell_3d = np.array([v[:3] for v in VERTICES_16CELL])
    
    # Draw octahedron edges (axis-aligned vertices)
    for v in sixteencell_3d:
        if not np.allclose(v, np.zeros(3)):
            ax2.scatter(*v, c='green', s=100, edgecolor='black')
    
    # Draw edges between adjacent octahedron vertices
    octa_verts = [v for v in sixteencell_3d if not np.allclose(v, np.zeros(3))]
    for i, v1 in enumerate(octa_verts):
        for j, v2 in enumerate(octa_verts):
            if i < j and np.isclose(np.dot(v1, v2), 0):  # Perpendicular = adjacent
                ax2.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
                         'g-', linewidth=2, alpha=0.6)
    
    # Mark origin (collapsed w-vertices)
    ax2.scatter(0, 0, 0, c='black', s=200, marker='x', label='±w → 0')
    
    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title('16-Cell → Octahedron\n8 vertices (4D) → 6+origin (3D)')
    ax2.set_box_aspect([1, 1, 1])
    ax2.legend()
    
    # Plot 3: 24-cell projection
    ax3 = fig.add_subplot(133, projection='3d')
    
    # Project tesseract (cube) and 16-cell (octahedron)
    tesseract_3d = np.array([v[:3] for v in VERTICES_TESSERACT])
    
    # Draw cube
    for v in tesseract_3d:
        ax3.scatter(*v, c='blue', s=80, alpha=0.8)
    
    # Draw cube edges
    for i, v1 in enumerate(tesseract_3d):
        for j, v2 in enumerate(tesseract_3d):
            if i < j:
                diff = np.abs(v1 - v2)
                if np.sum(diff > 0.01) == 1 and np.max(diff) < 1.1:  # Adjacent
                    ax3.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
                             'b-', linewidth=1, alpha=0.4)
    
    # Draw octahedron vertices
    for v in octa_verts:
        ax3.scatter(*v, c='green', s=80, marker='^', alpha=0.8)
    
    # Draw octahedron edges
    for i, v1 in enumerate(octa_verts):
        for j, v2 in enumerate(octa_verts):
            if i < j and np.isclose(np.dot(v1, v2), 0):
                ax3.plot([v1[0], v2[0]], [v1[1], v2[1]], [v1[2], v2[2]],
                         'g-', linewidth=1, alpha=0.4)
    
    ax3.set_xlabel('X')
    ax3.set_ylabel('Y')
    ax3.set_zlabel('Z')
    ax3.set_title('24-Cell Projection\n24 vertices (4D) → Cube + Octahedron (3D)')
    ax3.set_box_aspect([1, 1, 1])
    
    plt.tight_layout()
    plt.savefig(PLOT_DIR / 'theorem_0_3_1_embedding_chain.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_3_1_embedding_chain.png'}")


def plot_summary():
    """
    Create a summary visualization of Theorem 0.3.1.
    """
    fig = plt.figure(figsize=(16, 12))
    
    # Main title
    fig.suptitle('Theorem 0.3.1: W-Direction Correspondence\n'
                 'The W-axis in 3D corresponds to the 4th dimension of the 24-cell',
                 fontsize=16, fontweight='bold', y=0.98)
    
    # Plot 1: Stella with W-axis (top-left)
    ax1 = fig.add_subplot(221, projection='3d')
    
    # Draw tetrahedron T+
    t_plus = np.array([W, R, G, B])
    edges = [[0,1], [0,2], [0,3], [1,2], [1,3], [2,3]]
    for i, j in edges:
        ax1.plot([t_plus[i,0], t_plus[j,0]],
                 [t_plus[i,1], t_plus[j,1]],
                 [t_plus[i,2], t_plus[j,2]],
                 'b-', linewidth=2, alpha=0.7)
    
    # Vertices
    ax1.scatter(*W, c='gold', s=200, edgecolor='black', label='W (1,1,1)')
    ax1.scatter(*R, c='red', s=200, edgecolor='black', label='R')
    ax1.scatter(*G, c='green', s=200, edgecolor='black', label='G')
    ax1.scatter(*B, c='blue', s=200, edgecolor='black', label='B')
    
    # W-axis
    ax1.quiver(0, 0, 0, W[0]*1.3, W[1]*1.3, W[2]*1.3,
               color='gold', linewidth=3, arrow_length_ratio=0.1)
    
    # R-G-B plane
    rgb_plane = [[R, G, B]]
    poly = Poly3DCollection(rgb_plane, alpha=0.2, facecolor='cyan')
    ax1.add_collection3d(poly)
    
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title('W ⊥ R-G-B Plane')
    ax1.legend(fontsize=8)
    ax1.set_box_aspect([1, 1, 1])
    
    # Plot 2: Key results (top-right)
    ax2 = fig.add_subplot(222)
    ax2.axis('off')
    
    results = [
        ('✓', 'Cross product: n = (G-R) × (B-R) = (4,4,4) ∝ (1,1,1)'),
        ('✓', 'Perpendicularity: W·(G-R) = W·(B-R) = 0'),
        ('✓', 'Equidistance: |Ŵ-R̂| = |Ŵ-Ĝ| = |Ŵ-B̂| = √(8/3)'),
        ('✓', 'Tetrahedral angles: all dot products = -1/3'),
        ('✓', 'W(F₄) rotation: R·ê_w → projects to W direction'),
        ('✓', 'Symmetry: |W(F₄)| = 1152 = 24 × 48'),
    ]
    
    ax2.text(0.5, 0.95, 'Verified Claims', fontsize=14, fontweight='bold',
             ha='center', transform=ax2.transAxes)
    
    for i, (check, text) in enumerate(results):
        y = 0.85 - i * 0.12
        ax2.text(0.05, y, check, fontsize=16, color='green', transform=ax2.transAxes)
        ax2.text(0.12, y, text, fontsize=11, transform=ax2.transAxes)
    
    ax2.set_title('Computational Verification')
    
    # Plot 3: Projection diagram (bottom-left)
    ax3 = fig.add_subplot(223)
    ax3.axis('off')
    ax3.set_xlim(0, 10)
    ax3.set_ylim(0, 10)
    
    # 4D box
    ax3.add_patch(plt.Rectangle((0.5, 5), 3, 4, fill=True, facecolor='lightyellow',
                                  edgecolor='black', linewidth=2))
    ax3.text(2, 8.5, '4D', fontsize=12, ha='center', fontweight='bold')
    ax3.text(2, 7.5, '24-cell', fontsize=11, ha='center')
    ax3.text(2, 6.5, 'w-coordinate', fontsize=10, ha='center')
    ax3.text(2, 5.5, 'ê_w = (0,0,0,1)', fontsize=9, ha='center', family='monospace')
    
    # Arrow
    ax3.annotate('', xy=(6.5, 7), xytext=(3.5, 7),
                 arrowprops=dict(arrowstyle='->', color='blue', lw=3))
    ax3.text(5, 7.5, 'W(F₄) rotation\n+ projection', fontsize=10, ha='center')
    
    # 3D box
    ax3.add_patch(plt.Rectangle((6.5, 5), 3, 4, fill=True, facecolor='lightblue',
                                  edgecolor='black', linewidth=2))
    ax3.text(8, 8.5, '3D', fontsize=12, ha='center', fontweight='bold')
    ax3.text(8, 7.5, 'Stella octangula', fontsize=11, ha='center')
    ax3.text(8, 6.5, 'W-direction', fontsize=10, ha='center')
    ax3.text(8, 5.5, 'Ŵ = (1,1,1)/√3', fontsize=9, ha='center', family='monospace')
    
    # Key equation
    ax3.text(5, 3.5, 'Key Result:', fontsize=12, ha='center', fontweight='bold')
    ax3.text(5, 2.5, 'π(R · ê_w) ∝ Ŵ', fontsize=14, ha='center', family='monospace',
             bbox=dict(boxstyle='round', facecolor='white'))
    ax3.text(5, 1.5, 'The 4th dimension becomes the W-axis direction',
             fontsize=10, ha='center', style='italic')
    
    ax3.set_title('W-Direction Correspondence')
    
    # Plot 4: Physical significance (bottom-right)
    ax4 = fig.add_subplot(224)
    ax4.axis('off')
    
    ax4.text(0.5, 0.95, 'Physical Significance', fontsize=14, fontweight='bold',
             ha='center', transform=ax4.transAxes)
    
    significance = [
        'The W-axis direction identified here becomes:',
        '',
        '• The nodal line where VEV vanishes (Theorem 3.0.1)',
        '• The temporal fiber where λ propagates (Theorem 3.0.3)',
        '• The time direction after metric emergence (Theorem 5.2.1)',
        '',
        'This provides geometric foundation for D = N + 1 = 4:',
        '  N = 3: R-G-B color space → 3 spatial dimensions',
        '  +1: W-direction (⊥ to color space) → temporal dimension',
    ]
    
    for i, line in enumerate(significance):
        y = 0.85 - i * 0.08
        ax4.text(0.1, y, line, fontsize=10, transform=ax4.transAxes)
    
    ax4.set_title('Downstream Impact')
    
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    plt.savefig(PLOT_DIR / 'theorem_0_3_1_summary.png')
    plt.close()
    print(f"Saved: {PLOT_DIR / 'theorem_0_3_1_summary.png'}")


def generate_all_plots():
    """Generate all visualization plots."""
    set_plot_style()
    
    print("=" * 60)
    print("Generating Theorem 0.3.1 Visualizations")
    print("=" * 60)
    print()
    
    plot_stella_octangula_with_w_axis()
    plot_projection_correspondence()
    plot_tetrahedral_angles()
    plot_symmetry_factorization()
    plot_wf4_rotation_visualization()
    plot_embedding_chain()
    plot_summary()
    
    print()
    print("=" * 60)
    print(f"All plots saved to: {PLOT_DIR}")
    print("=" * 60)


if __name__ == "__main__":
    generate_all_plots()

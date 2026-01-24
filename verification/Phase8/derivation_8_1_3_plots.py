#!/usr/bin/env python3
"""
Prediction 8.1.3: Three-Generation Necessity — Visualization

This script generates plots for the four proofs of N_gen = 3:
1. Radial wavefunction profiles for three generations
2. Symmetry breaking chain diagram
3. Energy level diagram with confinement cutoff
4. Empirical constraints visualization

The stella octangula refers to two interlocked tetrahedra.

Author: Chiral Geometrogenesis Verification
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.special import spherical_jn
from mpl_toolkits.mplot3d import Axes3D
import os

# Set up plot style
plt.rcParams['figure.figsize'] = (12, 8)
plt.rcParams['font.size'] = 11
plt.rcParams['axes.labelsize'] = 12
plt.rcParams['axes.titlesize'] = 14
plt.rcParams['legend.fontsize'] = 10
plt.rcParams['figure.dpi'] = 150

# Golden ratio
PHI = (1 + np.sqrt(5)) / 2


def plot_radial_wavefunctions(save_path=None):
    """
    Plot radial wavefunctions for the three T_d-invariant modes.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    R = 1.0  # Cavity radius
    r = np.linspace(1e-6, R, 500)
    
    # Wave numbers from boundary conditions
    k_values = {
        0: np.pi / R,           # j_0 zero at π
        4: 7.725252 / R,        # First zero of j_4
        6: 10.417119 / R        # First zero of j_6
    }
    
    # Colors for generations
    colors = {1: '#2196F3', 2: '#4CAF50', 3: '#F44336'}  # Blue, Green, Red
    labels = {1: 'Gen 1 (l=6, lightest)', 2: 'Gen 2 (l=4, intermediate)', 
              3: 'Gen 3 (l=0, heaviest)'}
    
    # Calculate wavefunctions
    wavefunctions = {}
    for gen, l in [(3, 0), (2, 4), (1, 6)]:
        k = k_values[l]
        psi = np.array([spherical_jn(l, k*ri) if ri > 0 else 
                       (1 if l == 0 else 0) for ri in r])
        
        # Normalize
        norm_sq = np.trapz(psi**2 * r**2, r)
        if norm_sq > 0:
            psi = psi / np.sqrt(norm_sq)
        
        wavefunctions[gen] = {
            'l': l,
            'psi': psi,
            'prob': psi**2 * r**2
        }
    
    # Plot 1: Wavefunctions ψ(r)
    ax1 = axes[0, 0]
    for gen in [3, 2, 1]:
        wf = wavefunctions[gen]
        ax1.plot(r, wf['psi'], color=colors[gen], linewidth=2, label=labels[gen])
    
    ax1.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
    ax1.set_xlabel('r/R (normalized radius)')
    ax1.set_ylabel('ψ(r) (wavefunction)')
    ax1.set_title('Radial Wavefunctions for Three Generations')
    ax1.legend(loc='upper right')
    ax1.set_xlim(0, 1)
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Probability density r²|ψ|²
    ax2 = axes[0, 1]
    for gen in [3, 2, 1]:
        wf = wavefunctions[gen]
        ax2.fill_between(r, 0, wf['prob'], color=colors[gen], alpha=0.3)
        ax2.plot(r, wf['prob'], color=colors[gen], linewidth=2, label=labels[gen])
    
    ax2.set_xlabel('r/R (normalized radius)')
    ax2.set_ylabel('r²|ψ(r)|² (probability density)')
    ax2.set_title('Probability Distribution: Generation Localization')
    ax2.legend(loc='upper right')
    ax2.set_xlim(0, 1)
    ax2.set_ylim(0, None)
    ax2.grid(True, alpha=0.3)
    
    # Annotation for interpretation
    ax2.annotate('Heavy (3rd gen)\nnear center', xy=(0.15, 2.5), fontsize=10,
                ha='center', color=colors[3])
    ax2.annotate('Light (1st gen)\nnear boundary', xy=(0.75, 1.5), fontsize=10,
                ha='center', color=colors[1])
    
    # Plot 3: Energy levels
    ax3 = axes[1, 0]
    
    # A₁ content in Y_l
    l_values = [0, 4, 6, 8, 10, 12]
    energies = [l*(l+1) for l in l_values]
    E_confine = 50
    
    # Draw energy levels
    for i, (l, E) in enumerate(zip(l_values, energies)):
        color = '#4CAF50' if E < E_confine else '#9E9E9E'
        linestyle = '-' if E < E_confine else '--'
        ax3.hlines(E, 0.2, 0.8, colors=color, linewidth=3, linestyle=linestyle)
        ax3.text(0.85, E, f'l={l}, E={E}', va='center', fontsize=10, color=color)
    
    # Confinement line
    ax3.axhline(y=E_confine, color='#F44336', linestyle=':', linewidth=2,
                label=f'Confinement cutoff E_c = {E_confine}')
    ax3.fill_between([0, 1], E_confine, max(energies)+10, color='#F44336', alpha=0.1)
    
    ax3.set_xlim(0, 1.2)
    ax3.set_ylim(-5, max(energies)+20)
    ax3.set_ylabel('Energy E_l = l(l+1)')
    ax3.set_title('T_d-Invariant (A₁) Mode Energies')
    ax3.set_xticks([])
    ax3.legend(loc='upper left')
    
    # Count stable modes
    n_stable = sum(1 for E in energies if E < E_confine)
    ax3.text(0.5, E_confine + 15, f'3 stable modes\nbelow cutoff', ha='center',
            fontsize=12, fontweight='bold', color='#4CAF50',
            bbox=dict(boxstyle='round', facecolor='white', edgecolor='#4CAF50'))
    
    ax3.text(0.5, max(energies)+5, 'Unstable modes\n(above cutoff)', ha='center',
            fontsize=10, color='#9E9E9E', style='italic')
    
    # Plot 4: Generation assignment schematic
    ax4 = axes[1, 1]
    ax4.axis('off')
    
    # Create schematic
    ax4.text(0.5, 0.95, 'Generation Assignment from Radial Shells', 
            ha='center', va='top', fontsize=14, fontweight='bold')
    
    # Table-like structure
    table_data = [
        ('Angular Mode', 'Generation', 'Mass', 'Radial Position'),
        ('l = 0 (ground)', '3rd (τ, t, b)', 'Heaviest', 'Center'),
        ('l = 4 (1st excited)', '2nd (μ, c, s)', 'Intermediate', 'Middle shell'),
        ('l = 6 (2nd excited)', '1st (e, u, d)', 'Lightest', 'Outer shell'),
    ]
    
    y_pos = 0.75
    for i, row in enumerate(table_data):
        x_positions = [0.15, 0.38, 0.62, 0.85]
        fontweight = 'bold' if i == 0 else 'normal'
        color = 'black' if i == 0 else colors.get(4-i, 'black')
        for j, (x, text) in enumerate(zip(x_positions, row)):
            ax4.text(x, y_pos, text, ha='center', va='center', 
                    fontsize=10, fontweight=fontweight, color=color)
        y_pos -= 0.12
    
    # Key insight box
    ax4.text(0.5, 0.25, 
            'Key Insight: Higher angular momentum → wavefunction pushed outward\n'
            '→ less overlap with chiral field → lower mass',
            ha='center', va='center', fontsize=11,
            bbox=dict(boxstyle='round', facecolor='#E3F2FD', edgecolor='#2196F3'))
    
    # Result box
    ax4.text(0.5, 0.08, 
            'RESULT: T_d symmetry + confinement cutoff → exactly 3 generations',
            ha='center', va='center', fontsize=12, fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='#E8F5E9', edgecolor='#4CAF50'))
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    
    return fig


def plot_a4_symmetry_breaking(save_path=None):
    """
    Visualize the symmetry breaking chain O_h → T_d → A₄.
    """
    fig, axes = plt.subplots(1, 3, figsize=(16, 6))
    
    # =========================================================================
    # Plot 1: Symmetry breaking chain
    # =========================================================================
    ax1 = axes[0]
    ax1.axis('off')
    
    # Group boxes
    groups = [
        {'name': 'O_h', 'order': 48, 'y': 0.85, 'desc': 'Full octahedral\n(2 interlocked tetrahedra)'},
        {'name': 'T_d', 'order': 24, 'y': 0.50, 'desc': 'Tetrahedral\n(after parity breaking)'},
        {'name': 'A₄', 'order': 12, 'y': 0.15, 'desc': 'Alternating group\n(after CP breaking)'}
    ]
    
    for g in groups:
        rect = plt.Rectangle((0.25, g['y']-0.08), 0.5, 0.16, 
                             fill=True, facecolor='#E3F2FD', edgecolor='#1976D2', linewidth=2)
        ax1.add_patch(rect)
        ax1.text(0.5, g['y'], f"{g['name']}  (|G| = {g['order']})", 
                ha='center', va='center', fontsize=14, fontweight='bold')
        ax1.text(0.85, g['y'], g['desc'], ha='left', va='center', fontsize=10)
    
    # Arrows with labels
    ax1.annotate('', xy=(0.5, 0.58), xytext=(0.5, 0.77),
                arrowprops=dict(arrowstyle='->', lw=2, color='#F44336'))
    ax1.text(0.52, 0.67, 'Parity violation\n(Wu experiment 1957)', fontsize=9,
            color='#F44336', ha='left')
    
    ax1.annotate('', xy=(0.5, 0.23), xytext=(0.5, 0.42),
                arrowprops=dict(arrowstyle='->', lw=2, color='#F44336'))
    ax1.text(0.52, 0.32, 'CP violation\n(Cronin-Fitch 1964)', fontsize=9,
            color='#F44336', ha='left')
    
    ax1.set_xlim(0, 1.3)
    ax1.set_ylim(0, 1)
    ax1.set_title('Symmetry Breaking Chain', fontsize=14, fontweight='bold')
    
    # =========================================================================
    # Plot 2: A₄ irreducible representations
    # =========================================================================
    ax2 = axes[1]
    
    # Irrep dimensions
    irreps = {'1': 1, "1'": 1, "1''": 1, '3': 3}
    colors_irrep = {'1': '#F44336', "1'": '#4CAF50', "1''": '#2196F3', '3': '#9C27B0'}
    
    # Bar chart
    x = np.arange(len(irreps))
    bars = ax2.bar(x, list(irreps.values()), color=[colors_irrep[k] for k in irreps.keys()],
                   edgecolor='black', linewidth=1.5)
    
    ax2.set_xticks(x)
    ax2.set_xticklabels(list(irreps.keys()), fontsize=12)
    ax2.set_ylabel('Dimension', fontsize=12)
    ax2.set_title('A₄ Irreducible Representations', fontsize=14, fontweight='bold')
    ax2.set_ylim(0, 4)
    
    # Annotate
    for i, (name, dim) in enumerate(irreps.items()):
        ax2.text(i, dim + 0.1, f'd={dim}', ha='center', fontsize=10)
    
    # Dimension equation
    ax2.text(1.5, 3.5, r'$\sum d_i^2 = 1^2+1^2+1^2+3^2 = 12 = |A_4|$ ✓',
            ha='center', fontsize=11, bbox=dict(boxstyle='round', facecolor='white'))
    
    # Generation assignment
    assignments = [
        (0, '3rd gen\n(τ, t, b)'),
        (1, '2nd gen\n(μ, c, s)'),
        (2, '1st gen\n(e, u, d)')
    ]
    for i, label in assignments:
        ax2.text(i, -0.5, label, ha='center', fontsize=9, style='italic')
    
    ax2.text(3, -0.5, 'Triplets\n(colors)', ha='center', fontsize=9, style='italic')
    
    # =========================================================================
    # Plot 3: Comparison with other groups
    # =========================================================================
    ax3 = axes[2]
    
    groups = [
        ('S₄', 24, 2, False),
        ('A₄', 12, 3, True),
        ('S₃', 6, 2, False),
        ('Z₃', 3, 3, False),
        ('D₄', 8, 4, False)
    ]
    
    x = np.arange(len(groups))
    names = [g[0] for g in groups]
    n_1d = [g[2] for g in groups]
    colors_bar = ['#4CAF50' if g[3] else '#9E9E9E' for g in groups]
    
    bars = ax3.bar(x, n_1d, color=colors_bar, edgecolor='black', linewidth=1.5)
    
    # Highlight A₄
    for i, g in enumerate(groups):
        if g[3]:  # A₄
            bars[i].set_edgecolor('#F44336')
            bars[i].set_linewidth(3)
    
    ax3.axhline(y=3, color='#F44336', linestyle='--', linewidth=2, 
                label='Required: 3 one-dim irreps')
    
    ax3.set_xticks(x)
    ax3.set_xticklabels(names, fontsize=11)
    ax3.set_ylabel('Number of 1D Irreps', fontsize=12)
    ax3.set_title('Group Comparison: Why A₄?', fontsize=14, fontweight='bold')
    ax3.set_ylim(0, 5)
    ax3.legend(loc='upper right')
    
    # Add annotations
    for i, g in enumerate(groups):
        status = '✓' if g[3] else '✗'
        ax3.text(i, n_1d[i] + 0.15, status, ha='center', fontsize=14,
                color='#4CAF50' if g[3] else '#F44336')
        ax3.text(i, -0.4, f'|G|={g[1]}', ha='center', fontsize=9)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    
    return fig


def plot_topological_analysis(save_path=None):
    """
    Visualize topological aspects: Euler characteristic, Betti numbers, cohomology.
    Enhanced version with 3D visualization of two interlocked tetrahedra.
    """
    fig = plt.figure(figsize=(16, 14))
    
    # Create grid layout: 3D plot on left, other panels on right
    gs = fig.add_gridspec(3, 2, width_ratios=[1.2, 1], height_ratios=[1, 1, 1],
                          hspace=0.3, wspace=0.25)
    
    # =========================================================================
    # Plot 1: 3D Two Interlocked Tetrahedra (Stella Octangula)
    # =========================================================================
    ax_3d = fig.add_subplot(gs[:2, 0], projection='3d')
    
    # Tetrahedron vertices (two interlocked tetrahedra)
    # T+ (matter tetrahedron) - upward pointing
    T_plus = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ]) / np.sqrt(3)
    
    # T- (antimatter tetrahedron) - downward pointing (inverted)
    T_minus = -T_plus
    
    # Draw tetrahedra
    def draw_tetrahedron(ax, vertices, color, alpha=0.3, label=None):
        """Draw a tetrahedron with faces and edges."""
        from mpl_toolkits.mplot3d.art3d import Poly3DCollection
        
        # Define faces (indices into vertices)
        faces = [
            [vertices[0], vertices[1], vertices[2]],
            [vertices[0], vertices[1], vertices[3]],
            [vertices[0], vertices[2], vertices[3]],
            [vertices[1], vertices[2], vertices[3]]
        ]
        
        # Draw faces
        poly = Poly3DCollection(faces, alpha=alpha, facecolor=color, 
                                edgecolor=color, linewidth=1.5)
        ax.add_collection3d(poly)
        
        # Draw vertices
        ax.scatter(vertices[:, 0], vertices[:, 1], vertices[:, 2], 
                  s=80, c=color, edgecolors='black', linewidth=1, zorder=5)
        
        # Draw edges explicitly for visibility
        edges = [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
        for i, j in edges:
            ax.plot([vertices[i,0], vertices[j,0]], 
                   [vertices[i,1], vertices[j,1]], 
                   [vertices[i,2], vertices[j,2]], 
                   color=color, linewidth=2, alpha=0.8)
    
    # Draw both tetrahedra
    draw_tetrahedron(ax_3d, T_plus, '#2196F3', alpha=0.25, label='T₊ (Matter)')
    draw_tetrahedron(ax_3d, T_minus, '#F44336', alpha=0.25, label='T₋ (Antimatter)')
    
    # Labels for vertices
    vertex_labels_plus = ['R', 'G', 'B', 'W']
    vertex_labels_minus = ['R̄', 'Ḡ', 'B̄', 'W̄']
    
    for i, (v, label) in enumerate(zip(T_plus, vertex_labels_plus)):
        ax_3d.text(v[0]*1.15, v[1]*1.15, v[2]*1.15, label, fontsize=10, 
                  color='#1565C0', fontweight='bold', ha='center')
    
    for i, (v, label) in enumerate(zip(T_minus, vertex_labels_minus)):
        ax_3d.text(v[0]*1.15, v[1]*1.15, v[2]*1.15, label, fontsize=10, 
                  color='#C62828', fontweight='bold', ha='center')
    
    ax_3d.set_xlim([-1, 1])
    ax_3d.set_ylim([-1, 1])
    ax_3d.set_zlim([-1, 1])
    ax_3d.set_xlabel('X', fontsize=10)
    ax_3d.set_ylabel('Y', fontsize=10)
    ax_3d.set_zlabel('Z', fontsize=10)
    ax_3d.set_title('Two Interlocked Tetrahedra\n(Stella Octangula)', 
                    fontsize=14, fontweight='bold', pad=10)
    
    # Add legend manually
    from matplotlib.patches import Patch
    legend_elements = [Patch(facecolor='#2196F3', alpha=0.5, edgecolor='#1565C0',
                            label='T₊ (Matter, S²)'),
                      Patch(facecolor='#F44336', alpha=0.5, edgecolor='#C62828',
                            label='T₋ (Antimatter, S²)')]
    ax_3d.legend(handles=legend_elements, loc='upper left', fontsize=10)
    
    # Set viewing angle
    ax_3d.view_init(elev=20, azim=45)
    
    # =========================================================================
    # Plot 2: Euler Characteristic Panel
    # =========================================================================
    ax_euler = fig.add_subplot(gs[0, 1])
    ax_euler.axis('off')
    
    # Title
    ax_euler.text(0.5, 0.95, 'Euler Characteristic', ha='center', va='top',
                 fontsize=14, fontweight='bold')
    
    # Draw boxes for tetrahedra
    # Single tetrahedron box
    rect1 = plt.Rectangle((0.02, 0.45), 0.45, 0.40, fill=True,
                          facecolor='#E3F2FD', edgecolor='#1976D2', linewidth=2)
    ax_euler.add_patch(rect1)
    ax_euler.text(0.245, 0.78, 'Single Tetrahedron', ha='center', fontsize=11, fontweight='bold')
    ax_euler.text(0.245, 0.68, 'Boundary ≅ S²', ha='center', fontsize=10, style='italic')
    ax_euler.text(0.245, 0.55, 'V=4  E=6  F=4', ha='center', fontsize=11)
    ax_euler.text(0.245, 0.48, 'χ = 4−6+4 = 2', ha='center', fontsize=12, 
                 color='#1565C0', fontweight='bold')
    
    # Stella Octangula box
    rect2 = plt.Rectangle((0.53, 0.45), 0.45, 0.40, fill=True,
                          facecolor='#FFEBEE', edgecolor='#C62828', linewidth=2)
    ax_euler.add_patch(rect2)
    ax_euler.text(0.755, 0.78, 'Stella Octangula', ha='center', fontsize=11, fontweight='bold')
    ax_euler.text(0.755, 0.68, 'Boundary = S² ⊔ S²', ha='center', fontsize=10, style='italic')
    ax_euler.text(0.755, 0.55, 'V=8  E=12  F=8', ha='center', fontsize=11)
    ax_euler.text(0.755, 0.48, 'χ = 8−12+8 = 4', ha='center', fontsize=12,
                 color='#C62828', fontweight='bold')
    
    # Arrow between them
    ax_euler.annotate('', xy=(0.50, 0.65), xytext=(0.50, 0.65),
                     arrowprops=dict(arrowstyle='<->', lw=2, color='#4CAF50'))
    ax_euler.text(0.50, 0.70, '+', fontsize=16, ha='center', color='#4CAF50', fontweight='bold')
    
    # Additivity formula
    ax_euler.add_patch(plt.Rectangle((0.10, 0.08), 0.80, 0.25, fill=True,
                      facecolor='#E8F5E9', edgecolor='#4CAF50', linewidth=2))
    ax_euler.text(0.50, 0.27, 'Additivity: χ(A ⊔ B) = χ(A) + χ(B)', 
                 ha='center', fontsize=11, fontweight='bold')
    ax_euler.text(0.50, 0.18, 'χ(S² ⊔ S²) = 2 + 2 = 4', ha='center', fontsize=12,
                 color='#2E7D32', fontweight='bold')
    ax_euler.text(0.50, 0.10, '(Two disjoint closed surfaces)', ha='center', 
                 fontsize=10, style='italic')
    
    ax_euler.set_xlim(0, 1)
    ax_euler.set_ylim(0, 1)
    
    # =========================================================================
    # Plot 3: Betti Numbers
    # =========================================================================
    ax_betti = fig.add_subplot(gs[1, 1])
    
    betti = [2, 0, 2]
    x = np.arange(3)
    colors_betti = ['#F44336', '#9E9E9E', '#2196F3']
    
    bars = ax_betti.bar(x, betti, color=colors_betti, edgecolor='black', linewidth=2, width=0.6)
    
    ax_betti.set_xticks(x)
    ax_betti.set_xticklabels(['b₀', 'b₁', 'b₂'], fontsize=14, fontweight='bold')
    ax_betti.set_ylabel('Betti Number', fontsize=12)
    ax_betti.set_title('Betti Numbers of ∂S = S² ⊔ S²', fontsize=14, fontweight='bold')
    ax_betti.set_ylim(0, 3.5)
    
    # Value labels on bars
    for i, b in enumerate(betti):
        ax_betti.text(i, b + 0.12, str(b), ha='center', fontsize=16, fontweight='bold',
                     color=colors_betti[i])
    
    # Interpretations below
    interpretations = [
        'Connected\ncomponents\n(2 spheres)',
        '1-cycles\n(simply\nconnected)',
        'Independent\n2-cycles\n(2 volumes)'
    ]
    for i, interp in enumerate(interpretations):
        ax_betti.text(i, -0.65, interp, ha='center', fontsize=9, va='top')
    
    # Euler formula box
    ax_betti.text(1, 3.1, 'χ = b₀ − b₁ + b₂ = 2 − 0 + 2 = 4 ✓', ha='center', fontsize=11,
                 bbox=dict(boxstyle='round', facecolor='#E8F5E9', edgecolor='#4CAF50', linewidth=2))
    
    ax_betti.spines['top'].set_visible(False)
    ax_betti.spines['right'].set_visible(False)
    
    # =========================================================================
    # Plot 4: Connection Chain (χ=4 → N_gen=3)
    # =========================================================================
    ax_chain = fig.add_subplot(gs[2, :])
    ax_chain.axis('off')
    
    ax_chain.text(0.5, 0.98, 'Derivation Chain: χ = 4  →  N_gen = 3', 
                 ha='center', va='top', fontsize=16, fontweight='bold')
    ax_chain.text(0.5, 0.90, '(χ ≠ 3 directly — requires full chain)', 
                 ha='center', va='top', fontsize=11, style='italic', color='#666')
    
    # Chain steps with better layout
    steps = [
        ('χ(∂S) = 4', 'Euler-\nPoincaré'),
        ('Betti (2,0,2)', 'de Rham'),
        ('H^k(∂S)', 'Hodge'),
        ('Harmonic\nforms', 'T_d proj.'),
        ('A₁ modes\n(l=0,4,6,8...)', 'E cutoff'),
        ('3 modes\n(l=0,4,6)', None)
    ]
    
    # Draw the chain horizontally
    n_steps = len(steps)
    box_width = 0.11
    spacing = (0.92 - n_steps * box_width) / (n_steps - 1)
    
    x_start = 0.04
    y_center = 0.55
    box_height = 0.25
    
    colors_chain = ['#E3F2FD', '#E8F5E9', '#FFF3E0', '#F3E5F5', '#FFEBEE', '#C8E6C9']
    edge_colors = ['#1976D2', '#388E3C', '#F57C00', '#7B1FA2', '#D32F2F', '#2E7D32']
    
    for i, (label, mechanism) in enumerate(steps):
        x_pos = x_start + i * (box_width + spacing)
        
        # Draw box
        rect = plt.Rectangle((x_pos, y_center - box_height/2), box_width, box_height,
                             fill=True, facecolor=colors_chain[i], 
                             edgecolor=edge_colors[i], linewidth=2, zorder=2)
        ax_chain.add_patch(rect)
        
        # Label
        ax_chain.text(x_pos + box_width/2, y_center, label, ha='center', va='center',
                     fontsize=10, fontweight='bold', zorder=3)
        
        # Arrow to next step (skip for last item)
        if i < n_steps - 1 and mechanism is not None:
            arrow_start = x_pos + box_width + 0.005
            arrow_end = x_pos + box_width + spacing - 0.005
            ax_chain.annotate('', xy=(arrow_end, y_center), xytext=(arrow_start, y_center),
                            arrowprops=dict(arrowstyle='->', lw=2.5, color='#4CAF50'),
                            zorder=1)
            
            # Mechanism label above arrow
            ax_chain.text((arrow_start + arrow_end)/2, y_center + 0.18, mechanism,
                         ha='center', va='bottom', fontsize=9, color='#4CAF50',
                         fontweight='bold')
    
    # Final result box
    ax_chain.add_patch(plt.Rectangle((0.25, 0.05), 0.50, 0.18, fill=True,
                      facecolor='#C8E6C9', edgecolor='#2E7D32', linewidth=3))
    ax_chain.text(0.50, 0.14, 'RESULT: N_gen = 3 (Geometric Necessity)', 
                 ha='center', va='center', fontsize=13, fontweight='bold', color='#1B5E20')
    ax_chain.text(0.50, 0.08, 'Three stable T_d-invariant modes below confinement', 
                 ha='center', va='center', fontsize=10, style='italic')
    
    # de Rham cohomology table in lower left
    ax_chain.text(0.08, 0.32, 'de Rham Cohomology:', ha='left', fontsize=11, fontweight='bold')
    cohom_text = ('H⁰(∂S) = ℝ²  (constant functions)\n'
                  'H¹(∂S) = 0    (no 1-forms)\n'
                  'H²(∂S) = ℝ²  (volume forms)')
    ax_chain.text(0.08, 0.08, cohom_text, ha='left', va='bottom', fontsize=9,
                 family='monospace', bbox=dict(boxstyle='round', facecolor='white', 
                                               edgecolor='#9E9E9E', alpha=0.9))
    
    # Key insight in lower right
    ax_chain.text(0.92, 0.32, 'Key Insight:', ha='right', fontsize=11, fontweight='bold')
    insight_text = ('Hodge: dim(Harmonic k-forms) = bₖ\n'
                    'Harmonic forms = Laplacian zero modes\n'
                    '→ Physical field configurations')
    ax_chain.text(0.92, 0.08, insight_text, ha='right', va='bottom', fontsize=9,
                 family='monospace', bbox=dict(boxstyle='round', facecolor='white',
                                               edgecolor='#9E9E9E', alpha=0.9))
    
    ax_chain.set_xlim(0, 1)
    ax_chain.set_ylim(0, 1)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    
    return fig


def plot_empirical_constraints(save_path=None):
    """
    Visualize empirical constraints on generation number.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    
    # =========================================================================
    # Plot 1: CKM phases vs generations
    # =========================================================================
    ax1 = axes[0, 0]
    
    n_gen = np.arange(1, 7)
    n_angles = [n*(n-1)//2 for n in n_gen]
    n_phases = [(n-1)*(n-2)//2 for n in n_gen]
    
    x = np.arange(len(n_gen))
    width = 0.35
    
    bars1 = ax1.bar(x - width/2, n_angles, width, label='Mixing angles', color='#2196F3')
    bars2 = ax1.bar(x + width/2, n_phases, width, label='CP phases', color='#F44336')
    
    ax1.set_xticks(x)
    ax1.set_xticklabels([f'N={n}' for n in n_gen])
    ax1.set_ylabel('Number of Parameters')
    ax1.set_title('CKM Matrix Parameters vs Generation Number', fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.set_ylim(0, max(n_angles) + 2)
    
    # Mark CP violation requirement
    ax1.axhline(y=1, color='#F44336', linestyle='--', alpha=0.5, label='Min for CP violation')
    
    # Annotate
    for i, n in enumerate(n_gen):
        if n_phases[i] == 0:
            ax1.text(i + width/2, n_phases[i] + 0.3, 'No CP!', ha='center', fontsize=9,
                    color='#F44336', fontweight='bold')
        elif n == 3:
            ax1.text(i + width/2, n_phases[i] + 0.3, '1 phase ✓', ha='center', fontsize=9,
                    color='#4CAF50', fontweight='bold')
    
    # Lower bound box
    ax1.text(3.5, 8, 'CP violation observed\n→ N_gen ≥ 3', ha='center', fontsize=11,
            bbox=dict(boxstyle='round', facecolor='#E8F5E9', edgecolor='#4CAF50'))
    
    # =========================================================================
    # Plot 2: Z-width measurement
    # =========================================================================
    ax2 = axes[0, 1]
    
    # Measurement
    n_nu_central = 2.984
    n_nu_error = 0.008
    
    # Range to plot
    n_values = np.linspace(2.8, 4.2, 100)
    
    # Gaussian likelihood
    likelihood = np.exp(-0.5 * ((n_values - n_nu_central) / n_nu_error)**2)
    ax2.fill_between(n_values, 0, likelihood, color='#2196F3', alpha=0.3)
    ax2.plot(n_values, likelihood, color='#1976D2', linewidth=2)
    
    # Mark integer values
    for n in [2, 3, 4]:
        ax2.axvline(x=n, color='gray', linestyle='--', alpha=0.5)
        sigma = abs(n - n_nu_central) / n_nu_error
        color = '#4CAF50' if n == 3 else '#F44336'
        ax2.text(n, 1.05, f'N={n}\n({sigma:.0f}σ)', ha='center', fontsize=10, color=color)
    
    ax2.set_xlabel('Number of Neutrino Species')
    ax2.set_ylabel('Relative Likelihood')
    ax2.set_title('LEP Z-Width Measurement', fontsize=14, fontweight='bold')
    ax2.set_ylim(0, 1.2)
    ax2.set_xlim(2.8, 4.2)
    
    # Result box
    ax2.text(3.5, 0.5, f'N_ν = {n_nu_central} ± {n_nu_error}\n'
                       f'N=4 excluded at {abs(4-n_nu_central)/n_nu_error:.0f}σ',
            ha='center', fontsize=11,
            bbox=dict(boxstyle='round', facecolor='#FFEBEE', edgecolor='#F44336'))
    
    # =========================================================================
    # Plot 3: Higgs signal strength
    # =========================================================================
    ax3 = axes[1, 0]
    
    # Data
    categories = ['Observed', '4th Gen\nPrediction']
    values = [1.02, 9.0]
    errors = [0.07, 0]
    colors_bar = ['#4CAF50', '#F44336']
    
    x = np.arange(len(categories))
    bars = ax3.bar(x, values, color=colors_bar, edgecolor='black', linewidth=1.5)
    ax3.errorbar(x[0], values[0], yerr=errors[0], fmt='none', color='black', capsize=5, linewidth=2)
    
    ax3.set_xticks(x)
    ax3.set_xticklabels(categories, fontsize=12)
    ax3.set_ylabel('Higgs Signal Strength μ')
    ax3.set_title('Higgs Production: gg → H', fontsize=14, fontweight='bold')
    ax3.set_ylim(0, 11)
    
    # SM expectation
    ax3.axhline(y=1, color='#1976D2', linestyle='--', linewidth=2, label='SM expectation')
    ax3.legend()
    
    # Annotations
    ax3.text(0, 1.02 + 0.5, f'{values[0]} ± {errors[0]}', ha='center', fontsize=11)
    ax3.text(1, 9.0 + 0.3, '× 9 enhancement!', ha='center', fontsize=10, color='#F44336')
    
    deviation = abs(values[1] - values[0]) / errors[0]
    ax3.text(0.5, 5.5, f'4th gen excluded\nat {deviation:.0f}σ',
            ha='center', fontsize=12, fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='#FFEBEE', edgecolor='#F44336'))
    
    # =========================================================================
    # Plot 4: Combined constraint summary
    # =========================================================================
    ax4 = axes[1, 1]
    ax4.axis('off')
    
    ax4.text(0.5, 0.95, 'Combined Empirical Constraints', ha='center', va='top',
            fontsize=16, fontweight='bold')
    
    # Visual summary
    constraints = [
        ('CP Violation', 'N_gen ≥ 3', '#4CAF50', 'Kobayashi-Maskawa mechanism\nJ = 3×10⁻⁵ ≠ 0'),
        ('Z-Width', 'N_gen ≤ 3', '#F44336', 'LEP measurement\nN_ν = 2.984 ± 0.008'),
        ('Higgs', 'No heavy 4th gen', '#FF9800', 'LHC signal strength\nμ = 1.02 ± 0.07'),
    ]
    
    y = 0.75
    for name, constraint, color, detail in constraints:
        # Name box
        ax4.text(0.15, y, name, ha='center', va='center', fontsize=12, fontweight='bold',
                bbox=dict(boxstyle='round', facecolor=color, edgecolor='black', alpha=0.3))
        
        # Arrow
        ax4.annotate('', xy=(0.38, y), xytext=(0.28, y),
                    arrowprops=dict(arrowstyle='->', lw=2, color=color))
        
        # Constraint
        ax4.text(0.50, y, constraint, ha='center', va='center', fontsize=12, fontweight='bold')
        
        # Detail
        ax4.text(0.80, y, detail, ha='center', va='center', fontsize=9, style='italic')
        
        y -= 0.18
    
    # Combined result
    ax4.add_patch(plt.Rectangle((0.15, 0.10), 0.70, 0.15, fill=True,
                                facecolor='#E8F5E9', edgecolor='#4CAF50', linewidth=3))
    ax4.text(0.5, 0.175, 'COMBINED RESULT: N_gen = 3 exactly',
            ha='center', va='center', fontsize=14, fontweight='bold', color='#2E7D32')
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    
    return fig


def plot_summary_diagram(save_path=None):
    """
    Create a summary diagram showing all four proofs converging on N_gen = 3.
    """
    fig, ax = plt.subplots(figsize=(14, 10))
    ax.axis('off')
    
    # Title
    ax.text(0.5, 0.95, 'Prediction 8.1.3: Three-Generation Necessity',
           ha='center', va='top', fontsize=18, fontweight='bold')
    ax.text(0.5, 0.90, 'Four Independent Proofs → N_gen = 3',
           ha='center', va='top', fontsize=14, style='italic')
    
    # Central result box
    center_x, center_y = 0.5, 0.45
    box_width, box_height = 0.25, 0.12
    
    ax.add_patch(plt.Rectangle((center_x - box_width/2, center_y - box_height/2),
                                box_width, box_height, fill=True,
                                facecolor='#E8F5E9', edgecolor='#4CAF50', linewidth=4))
    ax.text(center_x, center_y, 'N_gen = 3\nGEOMETRIC NECESSITY',
           ha='center', va='center', fontsize=16, fontweight='bold', color='#2E7D32')
    
    # Four proof boxes
    proofs = [
        {
            'name': 'Proof 1:\nRadial Shells',
            'detail': 'T_d symmetry\n+ confinement\n→ 3 modes',
            'color': '#2196F3',
            'position': (0.15, 0.75)
        },
        {
            'name': 'Proof 2:\nA₄ Emergence',
            'detail': 'O_h → T_d → A₄\n→ 3 one-dim\nirreps',
            'color': '#4CAF50',
            'position': (0.85, 0.75)
        },
        {
            'name': 'Proof 3:\nTopology',
            'detail': 'χ = 4\n→ cohomology\n→ 3 modes',
            'color': '#FF9800',
            'position': (0.15, 0.15)
        },
        {
            'name': 'Proof 4:\nEmpirical',
            'detail': 'CP ≥ 3\nZ ≤ 3\n→ exactly 3',
            'color': '#F44336',
            'position': (0.85, 0.15)
        }
    ]
    
    for proof in proofs:
        x, y = proof['position']
        
        # Main box
        ax.add_patch(plt.Rectangle((x - 0.10, y - 0.08), 0.20, 0.16,
                                    fill=True, facecolor=proof['color'], 
                                    edgecolor='black', linewidth=2, alpha=0.3))
        
        # Title
        ax.text(x, y + 0.03, proof['name'], ha='center', va='center',
               fontsize=12, fontweight='bold')
        
        # Detail
        ax.text(x, y - 0.04, proof['detail'], ha='center', va='center',
               fontsize=9)
        
        # Arrow to center
        ax.annotate('', xy=(center_x + (x - center_x) * 0.35, 
                           center_y + (y - center_y) * 0.35),
                   xytext=(x + (center_x - x) * 0.15, 
                          y + (center_y - y) * 0.15),
                   arrowprops=dict(arrowstyle='->', lw=2, color=proof['color']))
    
    # Mass hierarchy connection (bottom)
    ax.add_patch(plt.Rectangle((0.25, 0.02), 0.50, 0.08,
                                fill=True, facecolor='#E3F2FD', 
                                edgecolor='#1976D2', linewidth=2))
    ax.text(0.5, 0.06, 'Mass Hierarchy Connection: λ = (1/φ³)×sin(72°) = 0.2245',
           ha='center', va='center', fontsize=11, fontweight='bold', color='#1565C0')
    ax.text(0.5, 0.03, '(0.88% agreement with PDG λ = 0.2265)',
           ha='center', va='center', fontsize=9, color='#1976D2')
    
    # Arrow from center to mass hierarchy
    ax.annotate('', xy=(0.5, 0.10), xytext=(0.5, center_y - box_height/2 - 0.02),
               arrowprops=dict(arrowstyle='->', lw=2, color='#1976D2'))
    
    # Checkmarks for each proof
    for i, proof in enumerate(proofs):
        x, y = proof['position']
        ax.text(x + 0.08, y + 0.06, '✓', fontsize=20, color='#4CAF50', fontweight='bold')
    
    # Footer
    ax.text(0.5, -0.02, 'Verified: January 2026 | Four independent proofs all yield N_gen = 3',
           ha='center', va='center', fontsize=10, style='italic', color='gray')
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    
    return fig


def generate_all_plots(output_dir=None):
    """Generate all verification plots."""
    if output_dir is None:
        output_dir = os.path.join(os.path.dirname(__file__), 'plots')
    
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating Prediction 8.1.3 verification plots...")
    print("=" * 60)
    
    # Generate each plot
    plot_radial_wavefunctions(os.path.join(output_dir, 'derivation_8_1_3_radial_wavefunctions.png'))
    plot_a4_symmetry_breaking(os.path.join(output_dir, 'derivation_8_1_3_a4_symmetry.png'))
    plot_topological_analysis(os.path.join(output_dir, 'derivation_8_1_3_topology.png'))
    plot_empirical_constraints(os.path.join(output_dir, 'derivation_8_1_3_empirical.png'))
    plot_summary_diagram(os.path.join(output_dir, 'derivation_8_1_3_summary.png'))
    
    print("=" * 60)
    print(f"All plots saved to: {output_dir}")
    
    return output_dir


###############################################################################
# MAIN
###############################################################################

if __name__ == '__main__':
    generate_all_plots()

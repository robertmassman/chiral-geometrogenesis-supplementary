#!/usr/bin/env python3
"""
Visualizations for Definition 0.1.2: Three Color Fields with Relative Phases

This script generates visualization plots for:
1. Cube roots of unity in the complex plane
2. SU(3) weight diagram with color assignments
3. Phase diagram showing the equilateral triangle
4. Color field amplitude and phase structure on the stella octangula boundary
5. Baryon and meson color neutrality diagrams

Note: The "stella octangula" refers to two interlocked tetrahedra forming an 8-vertex
structure with 6 color vertices and 2 singlet vertices.

Author: Verification Suite
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import os
from typing import Dict, List, Tuple, Optional

# Set up plotting style
plt.style.use('seaborn-v0_8-whitegrid')
plt.rcParams['figure.figsize'] = (10, 8)
plt.rcParams['font.size'] = 12
plt.rcParams['axes.labelsize'] = 14
plt.rcParams['axes.titlesize'] = 16

# =============================================================================
# CONSTANTS
# =============================================================================

# Primitive cube root of unity
OMEGA = np.exp(2j * np.pi / 3)

# Color phases (Definition 0.1.2)
PHASES = {
    'R': 0.0,
    'G': 2 * np.pi / 3,
    'B': 4 * np.pi / 3,
}

# Color RGB values for plotting
COLORS = {
    'R': '#FF0000',
    'G': '#00AA00',
    'B': '#0000FF',
    'R_bar': '#880000',
    'G_bar': '#005500',
    'B_bar': '#000088',
}

# SU(3) Weight vectors
WEIGHT_VECTORS = {
    'R': np.array([0.5, 1 / (2 * np.sqrt(3))]),
    'G': np.array([-0.5, 1 / (2 * np.sqrt(3))]),
    'B': np.array([0.0, -1 / np.sqrt(3)]),
}

# Stella octangula vertices (two interlocked tetrahedra)
TETRAHEDRON_PLUS = {
    'R': np.array([1, 1, 1]) / np.sqrt(3),
    'G': np.array([1, -1, -1]) / np.sqrt(3),
    'B': np.array([-1, 1, -1]) / np.sqrt(3),
    'W': np.array([-1, -1, 1]) / np.sqrt(3),
}

TETRAHEDRON_MINUS = {
    'R_bar': np.array([-1, -1, -1]) / np.sqrt(3),
    'G_bar': np.array([-1, 1, 1]) / np.sqrt(3),
    'B_bar': np.array([1, -1, 1]) / np.sqrt(3),
    'W_bar': np.array([1, 1, -1]) / np.sqrt(3),
}


# =============================================================================
# VISUALIZATION FUNCTIONS
# =============================================================================

def plot_cube_roots_of_unity(save_path: Optional[str] = None) -> None:
    """
    Plot the three cube roots of unity in the complex plane.
    
    Shows:
    - Unit circle
    - Three roots at 0°, 120°, 240°
    - Equilateral triangle connecting them
    - Vector sum showing color neutrality
    """
    fig, ax = plt.subplots(figsize=(10, 10))
    
    # Unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1, label='Unit circle')
    
    # Plot the three roots
    roots = [1, OMEGA, OMEGA**2]
    root_labels = ['1 = e^{i·0}', 'ω = e^{i·2π/3}', 'ω² = e^{i·4π/3}']
    color_labels = ['R', 'G', 'B']
    
    for i, (root, label, color) in enumerate(zip(roots, root_labels, color_labels)):
        x, y = root.real, root.imag
        ax.plot(x, y, 'o', color=COLORS[color], markersize=15)
        
        # Add vector from origin
        ax.annotate('', xy=(x, y), xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=COLORS[color], lw=2))
        
        # Label
        offset = 0.15
        ax.annotate(f'${label}$\n({color})', 
                    xy=(x + offset * np.cos(PHASES[color]), 
                        y + offset * np.sin(PHASES[color])),
                    fontsize=12, ha='center', color=COLORS[color], fontweight='bold')
    
    # Draw the triangle
    triangle_x = [r.real for r in roots] + [roots[0].real]
    triangle_y = [r.imag for r in roots] + [roots[0].imag]
    ax.plot(triangle_x, triangle_y, 'k-', linewidth=2, alpha=0.5)
    ax.fill(triangle_x, triangle_y, alpha=0.1, color='gray')
    
    # Show vector sum = 0
    sum_point = sum(roots)
    ax.plot(sum_point.real, sum_point.imag, 'kx', markersize=15, mew=3)
    ax.annotate('Sum = 0\n(Color Neutrality)', 
                xy=(0.15, 0.15), fontsize=11, style='italic')
    
    # Mark angles
    for i, phi in enumerate([0, 2*np.pi/3, 4*np.pi/3]):
        arc_theta = np.linspace(0, phi, 30)
        arc_r = 0.3
        ax.plot(arc_r * np.cos(arc_theta), arc_r * np.sin(arc_theta), 
                '-', color=COLORS[color_labels[i]], alpha=0.5, linewidth=2)
    
    # Axis settings
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)
    ax.set_aspect('equal')
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.axvline(x=0, color='k', linewidth=0.5)
    ax.set_xlabel('Real', fontsize=14)
    ax.set_ylabel('Imaginary', fontsize=14)
    ax.set_title('Definition 0.1.2: Cube Roots of Unity (Color Phases)', fontsize=16)
    
    # Add mathematical identity box
    textstr = r'$1 + \omega + \omega^2 = 0$' + '\n' + r'(Color Neutrality Condition)'
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8)
    ax.text(0.02, 0.98, textstr, transform=ax.transAxes, fontsize=12,
            verticalalignment='top', bbox=props)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_weight_diagram(save_path: Optional[str] = None) -> None:
    """
    Plot the SU(3) weight diagram showing the fundamental representation.
    
    Shows:
    - Three weight vectors in (T₃, T₈) space
    - Equilateral triangle structure
    - 120° angular separation
    """
    fig, ax = plt.subplots(figsize=(10, 10))
    
    # Plot weight vectors
    for color, w in WEIGHT_VECTORS.items():
        ax.plot(w[0], w[1], 'o', color=COLORS[color], markersize=15)
        ax.annotate('', xy=(w[0], w[1]), xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=COLORS[color], lw=2))
        
        # Label with eigenvalues
        offset = 0.08
        direction = w / np.linalg.norm(w)
        label = f'|{color}⟩\n({w[0]:.3f}, {w[1]:.3f})'
        ax.annotate(label, 
                    xy=(w[0] + offset * direction[0], w[1] + offset * direction[1]),
                    fontsize=10, ha='center', color=COLORS[color], fontweight='bold')
    
    # Draw triangle
    vertices = list(WEIGHT_VECTORS.values())
    triangle_x = [v[0] for v in vertices] + [vertices[0][0]]
    triangle_y = [v[1] for v in vertices] + [vertices[0][1]]
    ax.plot(triangle_x, triangle_y, 'k-', linewidth=2, alpha=0.5)
    ax.fill(triangle_x, triangle_y, alpha=0.1, color='gray')
    
    # Mark 120° angles
    def draw_angle_arc(ax, v1, v2, radius=0.15, color='gray'):
        """Draw arc between two vectors."""
        angle1 = np.arctan2(v1[1], v1[0])
        angle2 = np.arctan2(v2[1], v2[0])
        if angle2 < angle1:
            angle2 += 2 * np.pi
        theta = np.linspace(angle1, angle2, 30)
        ax.plot(radius * np.cos(theta), radius * np.sin(theta), 
                '--', color=color, alpha=0.5, linewidth=1.5)
    
    # Origin marker
    ax.plot(0, 0, 'ko', markersize=8)
    ax.annotate('Origin', xy=(0.02, -0.06), fontsize=10)
    
    # Add circle showing equal magnitudes
    mag = 1 / np.sqrt(3)
    theta = np.linspace(0, 2*np.pi, 100)
    ax.plot(mag * np.cos(theta), mag * np.sin(theta), 'k:', alpha=0.3, linewidth=1)
    ax.annotate(f'|w| = 1/√3', xy=(mag * 0.9, 0.02), fontsize=10, alpha=0.7)
    
    # Axis settings
    lim = 0.8
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.set_aspect('equal')
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.axvline(x=0, color='k', linewidth=0.5)
    ax.set_xlabel('$T_3$ eigenvalue', fontsize=14)
    ax.set_ylabel('$T_8$ eigenvalue', fontsize=14)
    ax.set_title('SU(3) Weight Diagram: Fundamental Representation (3)', fontsize=16)
    
    # Add info box
    textstr = 'Weight vectors form\nequilateral triangle\n\n' + \
              r'$\cos(\theta_{RG}) = -\frac{1}{2}$' + '\n' + \
              r'$\theta = 120°$'
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8)
    ax.text(0.02, 0.98, textstr, transform=ax.transAxes, fontsize=11,
            verticalalignment='top', bbox=props)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_phase_diagram(save_path: Optional[str] = None) -> None:
    """
    Plot the phase diagram showing both colors and anti-colors.
    
    Shows:
    - Six phase positions on unit circle
    - Color and anti-color relationships
    - Complex conjugate pairs
    """
    fig, ax = plt.subplots(figsize=(12, 10))
    
    # Unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1)
    
    # Color phases
    colors = ['R', 'G', 'B']
    for c in colors:
        phi = PHASES[c]
        x, y = np.cos(phi), np.sin(phi)
        ax.plot(x, y, 'o', color=COLORS[c], markersize=18)
        ax.annotate('', xy=(x, y), xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=COLORS[c], lw=2))
        
        # Label
        offset = 0.2
        ax.annotate(f'{c}\n$\\phi={phi:.2f}$', 
                    xy=(x * (1 + offset), y * (1 + offset)),
                    fontsize=11, ha='center', va='center', 
                    color=COLORS[c], fontweight='bold')
    
    # Anti-color phases (shown with different markers)
    anti_phases = {
        'R_bar': 0.0,
        'G_bar': 4 * np.pi / 3,
        'B_bar': 2 * np.pi / 3,
    }
    
    for c, phi in anti_phases.items():
        x, y = np.cos(phi), np.sin(phi)
        # Plot slightly offset from colors
        offset = 0.1
        ax.plot(x * (1 - offset), y * (1 - offset), 's', 
                color=COLORS[c], markersize=12, markerfacecolor='none', markeredgewidth=2)
        
        # Label
        base_color = c.replace('_bar', '')
        ax.annotate(f'$\\bar{{{base_color}}}$', 
                    xy=(x * (1 - 2*offset), y * (1 - 2*offset)),
                    fontsize=10, ha='center', va='center', color=COLORS[c])
    
    # Draw triangles
    # Color triangle (solid)
    color_pts = [np.exp(1j * PHASES[c]) for c in colors]
    tri_x = [p.real for p in color_pts] + [color_pts[0].real]
    tri_y = [p.imag for p in color_pts] + [color_pts[0].imag]
    ax.plot(tri_x, tri_y, 'k-', linewidth=2, alpha=0.6)
    ax.fill(tri_x, tri_y, alpha=0.1, color='blue')
    
    # Mark the center
    ax.plot(0, 0, 'ko', markersize=6)
    
    # Axis settings
    ax.set_xlim(-1.6, 1.6)
    ax.set_ylim(-1.6, 1.6)
    ax.set_aspect('equal')
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.axvline(x=0, color='k', linewidth=0.5)
    ax.set_xlabel('Real', fontsize=14)
    ax.set_ylabel('Imaginary', fontsize=14)
    ax.set_title('Definition 0.1.2: Color and Anti-Color Phases', fontsize=16)
    
    # Legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='gray', markersize=10, label='Color (quark)'),
        Line2D([0], [0], marker='s', color='gray', markerfacecolor='none', markersize=10, markeredgewidth=2, label='Anti-color (antiquark)'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=10)
    
    # Info box
    textstr = 'Colors: $\\phi_c \\in \\{0, 2\\pi/3, 4\\pi/3\\}$\n' + \
              'Anti-colors: $\\phi_{\\bar{c}} = -\\phi_c$\n\n' + \
              'Note: $\\bar{G}$ has same phase as $B$\n' + \
              '          $\\bar{B}$ has same phase as $G$'
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8)
    ax.text(0.02, 0.98, textstr, transform=ax.transAxes, fontsize=11,
            verticalalignment='top', bbox=props)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_stella_octangula_3d(save_path: Optional[str] = None) -> None:
    """
    Plot the stella octangula (two interlocked tetrahedra) in 3D.
    
    Shows:
    - Matter tetrahedron (R, G, B, W vertices)
    - Antimatter tetrahedron (R̄, Ḡ, B̄, W̄ vertices)
    - Color coding of vertices
    """
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Plot vertices of both tetrahedra
    all_vertices = {**TETRAHEDRON_PLUS, **TETRAHEDRON_MINUS}
    
    for name, pos in all_vertices.items():
        if name == 'W':
            color = 'gray'
            marker = 'o'
            size = 100
            label = 'Singlet'
        elif name == 'W_bar':
            color = 'darkgray'
            marker = 's'
            size = 100
            label = 'Anti-singlet'
        elif '_bar' in name:
            base = name.replace('_bar', '')
            color = COLORS.get(name, COLORS.get(base, 'black'))
            marker = 's'
            size = 150
            label = f'$\\bar{{{base}}}$'
        else:
            color = COLORS.get(name, 'black')
            marker = 'o'
            size = 150
            label = name
        
        ax.scatter(*pos, c=color, marker=marker, s=size, edgecolors='black', linewidth=1)
        ax.text(pos[0]*1.15, pos[1]*1.15, pos[2]*1.15, label, fontsize=10, ha='center')
    
    # Draw tetrahedron edges
    def draw_tetrahedron(ax, vertices, color='blue', alpha=0.3, linestyle='-'):
        """Draw the edges of a tetrahedron."""
        names = list(vertices.keys())
        for i in range(len(names)):
            for j in range(i+1, len(names)):
                p1 = vertices[names[i]]
                p2 = vertices[names[j]]
                ax.plot3D([p1[0], p2[0]], [p1[1], p2[1]], [p1[2], p2[2]], 
                         linestyle, color=color, linewidth=1.5, alpha=0.7)
    
    draw_tetrahedron(ax, TETRAHEDRON_PLUS, color='blue')
    draw_tetrahedron(ax, TETRAHEDRON_MINUS, color='red')
    
    # Draw faces with transparency
    def add_tetrahedron_faces(ax, vertices, color='blue', alpha=0.1):
        """Add faces of tetrahedron."""
        verts = list(vertices.values())
        faces = [
            [verts[0], verts[1], verts[2]],
            [verts[0], verts[1], verts[3]],
            [verts[0], verts[2], verts[3]],
            [verts[1], verts[2], verts[3]],
        ]
        collection = Poly3DCollection(faces, alpha=alpha, facecolor=color, edgecolor=color)
        ax.add_collection3d(collection)
    
    add_tetrahedron_faces(ax, TETRAHEDRON_PLUS, color='blue', alpha=0.1)
    add_tetrahedron_faces(ax, TETRAHEDRON_MINUS, color='red', alpha=0.1)
    
    # Set axis properties
    ax.set_xlim([-1, 1])
    ax.set_ylim([-1, 1])
    ax.set_zlim([-1, 1])
    ax.set_xlabel('X')
    ax.set_ylabel('Y')
    ax.set_zlabel('Z')
    ax.set_title('Stella Octangula: Color Field Vertices', fontsize=16)
    
    # Add legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='blue', linewidth=2, label='Matter tetrahedron (T⁺)'),
        Line2D([0], [0], color='red', linewidth=2, label='Antimatter tetrahedron (T⁻)'),
    ]
    ax.legend(handles=legend_elements, loc='upper left')
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_color_neutrality_diagrams(save_path: Optional[str] = None) -> None:
    """
    Plot diagrams showing color neutrality for baryons and mesons.
    
    Shows:
    - Baryon: Three quarks with phases summing to zero
    - Meson: Quark-antiquark with phase cancellation
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Panel 1: Baryon (qqq)
    ax1 = axes[0]
    
    # Unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1)
    
    # Three quark phases
    for c in ['R', 'G', 'B']:
        phi = PHASES[c]
        x, y = np.cos(phi), np.sin(phi)
        ax1.plot(x, y, 'o', color=COLORS[c], markersize=15)
        ax1.annotate('', xy=(x, y), xytext=(0, 0),
                    arrowprops=dict(arrowstyle='->', color=COLORS[c], lw=2))
        ax1.annotate(c, xy=(x*1.15, y*1.15), fontsize=12, ha='center', 
                    color=COLORS[c], fontweight='bold')
    
    # Show sum = 0
    ax1.plot(0, 0, 'kx', markersize=20, mew=3)
    ax1.annotate('$R + G + B = 0$', xy=(0.1, -0.2), fontsize=12)
    
    ax1.set_xlim(-1.4, 1.4)
    ax1.set_ylim(-1.4, 1.4)
    ax1.set_aspect('equal')
    ax1.set_title('Baryon (qqq): Color Singlet', fontsize=14)
    ax1.set_xlabel('Real')
    ax1.set_ylabel('Imaginary')
    
    # Info
    textstr = r'$e^{i\phi_R} + e^{i\phi_G} + e^{i\phi_B} = 0$' + '\n' + \
              r'$1 + \omega + \omega^2 = 0$'
    props = dict(boxstyle='round', facecolor='lightgreen', alpha=0.8)
    ax1.text(0.02, 0.98, textstr, transform=ax1.transAxes, fontsize=11,
            verticalalignment='top', bbox=props)
    
    # Panel 2: Meson (qq̄)
    ax2 = axes[1]
    
    # Show three meson configurations
    y_positions = [0.7, 0, -0.7]
    colors = ['R', 'G', 'B']
    
    for i, (ypos, c) in enumerate(zip(y_positions, colors)):
        # Quark
        ax2.annotate('', xy=(0.3, ypos), xytext=(-0.5, ypos),
                    arrowprops=dict(arrowstyle='->', color=COLORS[c], lw=3))
        ax2.plot(-0.5, ypos, 'o', color=COLORS[c], markersize=15)
        ax2.annotate(f'$q_{c}$\n$e^{{i\\phi_{c}}}$', xy=(-0.7, ypos), fontsize=10, 
                    ha='center', va='center', color=COLORS[c])
        
        # Antiquark (opposite direction)
        ax2.annotate('', xy=(-0.3, ypos), xytext=(0.5, ypos),
                    arrowprops=dict(arrowstyle='->', color=COLORS[c], lw=3, ls='--'))
        ax2.plot(0.5, ypos, 's', color=COLORS[c], markersize=12, 
                markerfacecolor='white', markeredgewidth=2)
        ax2.annotate(f'$\\bar{{q}}_{c}$\n$e^{{-i\\phi_{c}}}$', xy=(0.7, ypos), fontsize=10,
                    ha='center', va='center', color=COLORS[c])
        
        # Result
        ax2.annotate('= 1', xy=(1.0, ypos), fontsize=12, ha='left', va='center')
    
    ax2.set_xlim(-1.2, 1.5)
    ax2.set_ylim(-1.2, 1.2)
    ax2.set_aspect('equal')
    ax2.axis('off')
    ax2.set_title('Meson ($q\\bar{q}$): Phase Cancellation', fontsize=14)
    
    # Info
    textstr = r'Each $|c\bar{c}\rangle$:' + '\n' + \
              r'$e^{i\phi_c} \cdot e^{-i\phi_c} = 1$' + '\n\n' + \
              'Singlet state:\n' + \
              r'$\frac{1}{\sqrt{3}}(|R\bar{R}\rangle + |G\bar{G}\rangle + |B\bar{B}\rangle)$'
    props = dict(boxstyle='round', facecolor='lightyellow', alpha=0.8)
    ax2.text(0.02, 0.98, textstr, transform=ax2.transAxes, fontsize=10,
            verticalalignment='top', bbox=props)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_z3_center_symmetry(save_path: Optional[str] = None) -> None:
    """
    Visualize the Z₃ center symmetry of SU(3).
    
    Shows:
    - The three center elements as rotations
    - How they act on color states
    - The cyclic structure
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Panel 1: Z₃ as rotations in complex plane
    ax1 = axes[0]
    
    # Unit circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1)
    
    # Center elements as points
    for k in range(3):
        z_k = np.exp(2j * np.pi * k / 3)
        x, y = z_k.real, z_k.imag
        ax1.plot(x, y, 'ko', markersize=15)
        ax1.annotate(f'$z_{k} = \\omega^{k}$', xy=(x*1.2, y*1.2), fontsize=12, 
                    ha='center', va='center')
        
        # Draw arc showing rotation
        if k > 0:
            arc_theta = np.linspace(0, 2*np.pi*k/3, 30)
            arc_r = 0.6
            ax1.plot(arc_r * np.cos(arc_theta), arc_r * np.sin(arc_theta), 
                    '-', color=f'C{k}', alpha=0.5, linewidth=2)
            ax1.annotate(f'{k}×120°', xy=(0.4*np.cos(np.pi*k/3), 0.4*np.sin(np.pi*k/3)),
                        fontsize=10, alpha=0.7)
    
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.axhline(y=0, color='k', linewidth=0.5)
    ax1.axvline(x=0, color='k', linewidth=0.5)
    ax1.set_title('$\\mathbb{Z}_3$ Center Elements', fontsize=14)
    ax1.set_xlabel('Real')
    ax1.set_ylabel('Imaginary')
    
    textstr = r'$Z(SU(3)) = \{\omega^k I : k=0,1,2\}$' + '\n' + \
              r'$\omega = e^{2\pi i/3}$' + '\n\n' + \
              'Center commutes with all\ngroup elements'
    props = dict(boxstyle='round', facecolor='lavender', alpha=0.8)
    ax1.text(0.02, 0.98, textstr, transform=ax1.transAxes, fontsize=11,
            verticalalignment='top', bbox=props)
    
    # Panel 2: Action on color states
    ax2 = axes[1]
    
    # Draw the three color states as a cycle
    colors = ['R', 'G', 'B']
    positions = {
        'R': (0, 0.8),
        'G': (-0.7, -0.4),
        'B': (0.7, -0.4),
    }
    
    for c in colors:
        x, y = positions[c]
        ax2.plot(x, y, 'o', color=COLORS[c], markersize=40)
        ax2.annotate(f'|{c}⟩', xy=(x, y), fontsize=14, ha='center', va='center',
                    color='white', fontweight='bold')
    
    # Draw arrows showing z₁ action (rotation by ω)
    from matplotlib.patches import FancyArrowPatch
    import matplotlib.patches as mpatches
    
    # R → G → B → R cycle
    arrow_style = "Simple, tail_width=0.5, head_width=4, head_length=8"
    kw = dict(arrowstyle=arrow_style, color="gray", alpha=0.7)
    
    # Curved arrows
    for start, end in [('R', 'G'), ('G', 'B'), ('B', 'R')]:
        p1 = np.array(positions[start])
        p2 = np.array(positions[end])
        mid = (p1 + p2) / 2
        # Offset midpoint outward
        center = np.array([0, 0])
        direction = mid - center
        direction = direction / np.linalg.norm(direction)
        mid_offset = mid + 0.2 * direction
        
        ax2.annotate('', xy=p2, xytext=p1,
                    arrowprops=dict(arrowstyle='->', color='gray', 
                                   connectionstyle='arc3,rad=0.3', lw=2))
    
    ax2.annotate('$z_1$: multiply by $\\omega$', xy=(0, 0), fontsize=12, 
                ha='center', va='center', style='italic')
    
    ax2.set_xlim(-1.2, 1.2)
    ax2.set_ylim(-0.8, 1.2)
    ax2.set_aspect('equal')
    ax2.axis('off')
    ax2.set_title('$z_1$ Action: $|c⟩ → \\omega|c⟩$', fontsize=14)
    
    textstr = r'Under $z_k \in Z(SU(3))$:' + '\n\n' + \
              r'$\chi_c \to \omega^k \chi_c$' + '\n\n' + \
              'All colors get same phase\n(triality symmetry)'
    props = dict(boxstyle='round', facecolor='lightcyan', alpha=0.8)
    ax2.text(0.02, 0.98, textstr, transform=ax2.transAxes, fontsize=11,
            verticalalignment='top', bbox=props)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def plot_chirality_orientation(save_path: Optional[str] = None) -> None:
    """
    Visualize chirality as phase ordering orientation.
    
    Shows:
    - R→G→B (counterclockwise) vs R→B→G (clockwise)
    - Connection to physical chirality convention
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Unit circle for both panels
    theta = np.linspace(0, 2*np.pi, 100)
    
    # Panel 1: R→G→B (Counterclockwise = "Right-handed" by convention)
    ax1 = axes[0]
    ax1.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1)
    
    colors = ['R', 'G', 'B']
    for c in colors:
        phi = PHASES[c]
        x, y = np.cos(phi), np.sin(phi)
        ax1.plot(x, y, 'o', color=COLORS[c], markersize=15)
        ax1.annotate(c, xy=(x*1.15, y*1.15), fontsize=14, ha='center', 
                    color=COLORS[c], fontweight='bold')
    
    # Draw counterclockwise arrows
    for i, c in enumerate(colors):
        next_c = colors[(i+1) % 3]
        phi1, phi2 = PHASES[c], PHASES[next_c]
        if phi2 < phi1:
            phi2 += 2*np.pi
        arc = np.linspace(phi1, phi2, 20)
        r = 0.85
        ax1.plot(r*np.cos(arc), r*np.sin(arc), '-', color='darkgreen', lw=2)
        # Arrow at end
        mid_angle = (phi1 + phi2) / 2
        ax1.annotate('', xy=(r*np.cos(mid_angle+0.1), r*np.sin(mid_angle+0.1)),
                    xytext=(r*np.cos(mid_angle), r*np.sin(mid_angle)),
                    arrowprops=dict(arrowstyle='->', color='darkgreen', lw=2))
    
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')
    ax1.set_title('R→G→B: Counterclockwise\n(Selected by QCD anomaly)', fontsize=14)
    
    textstr = 'Physical chirality:\n' + \
              r'$f^{RGB} = f^{123} = +1$' + '\n\n' + \
              'Selected by CP violation\n(matter over antimatter)'
    props = dict(boxstyle='round', facecolor='lightgreen', alpha=0.8)
    ax1.text(0.02, 0.02, textstr, transform=ax1.transAxes, fontsize=10,
            verticalalignment='bottom', bbox=props)
    
    # Panel 2: R→B→G (Clockwise = "Left-handed")
    ax2 = axes[1]
    ax2.plot(np.cos(theta), np.sin(theta), 'k--', alpha=0.3, linewidth=1)
    
    # Reversed order
    colors_rev = ['R', 'B', 'G']
    phases_rev = [0, 4*np.pi/3, 2*np.pi/3]
    
    for c in colors:
        phi = PHASES[c]
        x, y = np.cos(phi), np.sin(phi)
        ax2.plot(x, y, 'o', color=COLORS[c], markersize=15, alpha=0.5)
        ax2.annotate(c, xy=(x*1.15, y*1.15), fontsize=14, ha='center', 
                    color=COLORS[c], fontweight='bold', alpha=0.5)
    
    # Draw clockwise arrows
    for i in range(3):
        phi1 = phases_rev[i]
        phi2 = phases_rev[(i+1) % 3]
        if phi2 > phi1:
            phi2 -= 2*np.pi
        arc = np.linspace(phi1, phi2, 20)
        r = 0.85
        ax2.plot(r*np.cos(arc), r*np.sin(arc), '-', color='darkred', lw=2)
        mid_angle = (phi1 + phi2) / 2
        ax2.annotate('', xy=(r*np.cos(mid_angle-0.1), r*np.sin(mid_angle-0.1)),
                    xytext=(r*np.cos(mid_angle), r*np.sin(mid_angle)),
                    arrowprops=dict(arrowstyle='->', color='darkred', lw=2))
    
    ax2.set_xlim(-1.5, 1.5)
    ax2.set_ylim(-1.5, 1.5)
    ax2.set_aspect('equal')
    ax2.set_title('R→B→G: Clockwise\n(Not selected)', fontsize=14)
    
    textstr = 'Opposite chirality:\n' + \
              r'$f^{RBG} = -f^{RGB} = -1$' + '\n\n' + \
              'Would give antimatter\nover matter (rejected)'
    props = dict(boxstyle='round', facecolor='lightcoral', alpha=0.8)
    ax2.text(0.02, 0.02, textstr, transform=ax2.transAxes, fontsize=10,
            verticalalignment='bottom', bbox=props)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {save_path}")
    plt.close()


def generate_all_visualizations(output_dir: str) -> None:
    """Generate all visualizations and save to output directory."""
    
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating visualizations for Definition 0.1.2...")
    
    # Generate each plot
    plot_cube_roots_of_unity(os.path.join(output_dir, 'def_0_1_2_cube_roots_of_unity.png'))
    plot_weight_diagram(os.path.join(output_dir, 'def_0_1_2_weight_diagram.png'))
    plot_phase_diagram(os.path.join(output_dir, 'def_0_1_2_phase_diagram.png'))
    plot_stella_octangula_3d(os.path.join(output_dir, 'def_0_1_2_stella_octangula_3d.png'))
    plot_color_neutrality_diagrams(os.path.join(output_dir, 'def_0_1_2_color_neutrality.png'))
    plot_z3_center_symmetry(os.path.join(output_dir, 'def_0_1_2_z3_center_symmetry.png'))
    plot_chirality_orientation(os.path.join(output_dir, 'def_0_1_2_chirality_orientation.png'))
    
    print(f"\nAll visualizations saved to: {output_dir}")


if __name__ == '__main__':
    # Determine output directory
    script_dir = os.path.dirname(os.path.abspath(__file__))
    plots_dir = os.path.join(os.path.dirname(script_dir), 'plots')
    
    generate_all_visualizations(plots_dir)

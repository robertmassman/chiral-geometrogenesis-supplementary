#!/usr/bin/env python3
"""
Visual Image: Bootstrap & QCD Scale Determination
==================================================

Pure visual representation - no text, just geometry showing
the derivation chain from stella to QCD scale.
"""

import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import os

def create_visual():
    """Create a pure visual representation."""

    fig = plt.figure(figsize=(16, 9), facecolor='#0a0a1a')
    ax = fig.add_axes([0, 0, 1, 1], projection='3d', facecolor='#0a0a1a')

    # =========================================================================
    # STELLA OCTANGULA (center-left, large)
    # =========================================================================
    a = 2.0
    t1_verts = np.array([[a,a,a], [-a,-a,a], [-a,a,-a], [a,-a,-a]])
    t2_verts = np.array([[-a,-a,-a], [a,a,-a], [a,-a,a], [-a,a,a]])

    t1_faces = [[t1_verts[0], t1_verts[1], t1_verts[2]],
                [t1_verts[0], t1_verts[1], t1_verts[3]],
                [t1_verts[0], t1_verts[2], t1_verts[3]],
                [t1_verts[1], t1_verts[2], t1_verts[3]]]
    t2_faces = [[t2_verts[0], t2_verts[1], t2_verts[2]],
                [t2_verts[0], t2_verts[1], t2_verts[3]],
                [t2_verts[0], t2_verts[2], t2_verts[3]],
                [t2_verts[1], t2_verts[2], t2_verts[3]]]

    # Glowing tetrahedra
    ax.add_collection3d(Poly3DCollection(t1_faces, alpha=0.85,
                        facecolor='#00BCD4', edgecolor='#4DD0E1', linewidth=2))
    ax.add_collection3d(Poly3DCollection(t2_faces, alpha=0.85,
                        facecolor='#FF5722', edgecolor='#FF8A65', linewidth=2))

    # =========================================================================
    # EMANATING WAVES / ENERGY (representing √σ = ℏc/R)
    # =========================================================================
    # Concentric spherical shells emanating from stella
    for r, alpha in [(3.0, 0.15), (4.0, 0.12), (5.0, 0.08), (6.5, 0.05), (8.0, 0.03)]:
        u = np.linspace(0, 2 * np.pi, 50)
        v = np.linspace(0, np.pi, 30)
        x = r * np.outer(np.cos(u), np.sin(v))
        y = r * np.outer(np.sin(u), np.sin(v))
        z = r * np.outer(np.ones(np.size(u)), np.cos(v))
        ax.plot_surface(x, y, z, alpha=alpha, color='#7C4DFF',
                       linewidth=0, antialiased=True)

    # =========================================================================
    # SCALE HIERARCHY SPIRAL (representing exp(128π/9))
    # =========================================================================
    # Golden spiral emanating outward - representing the 19 orders of magnitude
    t = np.linspace(0, 6*np.pi, 500)
    spiral_scale = 0.08
    r_spiral = spiral_scale * np.exp(0.15 * t)

    # Position spiral to the right
    x_offset = 6
    y_offset = 0
    z_offset = 0

    x_spiral = r_spiral * np.cos(t) + x_offset
    y_spiral = r_spiral * np.sin(t) + y_offset
    z_spiral = t * 0.3 - 3 + z_offset

    # Color gradient from purple (Planck) to gold (QCD)
    colors = plt.cm.plasma(np.linspace(0, 1, len(t)))
    for i in range(len(t)-1):
        ax.plot(x_spiral[i:i+2], y_spiral[i:i+2], z_spiral[i:i+2],
               color=colors[i], linewidth=3, alpha=0.9)

    # =========================================================================
    # CONNECTING FLOW LINES (topology → QCD)
    # =========================================================================
    # Curved lines from stella vertices to the spiral
    for vert in t1_verts:
        t_flow = np.linspace(0, 1, 50)
        # Bezier-like curve
        start = vert
        end = np.array([x_offset - 2, 0, 0])
        mid = (start + end) / 2 + np.array([0, 0, 2])

        x_flow = (1-t_flow)**2 * start[0] + 2*(1-t_flow)*t_flow * mid[0] + t_flow**2 * end[0]
        y_flow = (1-t_flow)**2 * start[1] + 2*(1-t_flow)*t_flow * mid[1] + t_flow**2 * end[1]
        z_flow = (1-t_flow)**2 * start[2] + 2*(1-t_flow)*t_flow * mid[2] + t_flow**2 * end[2]

        ax.plot(x_flow, y_flow, z_flow, color='#4DD0E1', alpha=0.4, linewidth=1.5)

    for vert in t2_verts:
        t_flow = np.linspace(0, 1, 50)
        start = vert
        end = np.array([x_offset - 2, 0, 0])
        mid = (start + end) / 2 + np.array([0, 0, -2])

        x_flow = (1-t_flow)**2 * start[0] + 2*(1-t_flow)*t_flow * mid[0] + t_flow**2 * end[0]
        y_flow = (1-t_flow)**2 * start[1] + 2*(1-t_flow)*t_flow * mid[1] + t_flow**2 * end[1]
        z_flow = (1-t_flow)**2 * start[2] + 2*(1-t_flow)*t_flow * mid[2] + t_flow**2 * end[2]

        ax.plot(x_flow, y_flow, z_flow, color='#FF8A65', alpha=0.4, linewidth=1.5)

    # =========================================================================
    # GLUON-LIKE HELICES (representing color fields)
    # =========================================================================
    t_helix = np.linspace(0, 4*np.pi, 200)
    helix_r = 0.3
    for offset_angle, color in [(0, '#F44336'), (2*np.pi/3, '#4CAF50'), (4*np.pi/3, '#2196F3')]:
        x_h = helix_r * np.cos(t_helix + offset_angle)
        y_h = helix_r * np.sin(t_helix + offset_angle)
        z_h = t_helix * 0.15 - 1
        ax.plot(x_h, y_h, z_h, color=color, linewidth=2.5, alpha=0.7)

    # =========================================================================
    # FINAL RESULT: GLOWING ORB (representing observed √σ)
    # =========================================================================
    # Golden sphere at end of spiral representing the QCD scale
    u = np.linspace(0, 2 * np.pi, 30)
    v = np.linspace(0, np.pi, 20)
    orb_r = 0.8
    orb_x = orb_r * np.outer(np.cos(u), np.sin(v)) + x_spiral[-1]
    orb_y = orb_r * np.outer(np.sin(u), np.sin(v)) + y_spiral[-1]
    orb_z = orb_r * np.outer(np.ones(np.size(u)), np.cos(v)) + z_spiral[-1]
    ax.plot_surface(orb_x, orb_y, orb_z, alpha=0.9, color='#FFD700',
                   linewidth=0, antialiased=True)

    # Glow around orb
    for glow_r, glow_alpha in [(1.0, 0.3), (1.3, 0.15), (1.6, 0.08)]:
        glow_x = glow_r * np.outer(np.cos(u), np.sin(v)) + x_spiral[-1]
        glow_y = glow_r * np.outer(np.sin(u), np.sin(v)) + y_spiral[-1]
        glow_z = glow_r * np.outer(np.ones(np.size(u)), np.cos(v)) + z_spiral[-1]
        ax.plot_surface(glow_x, glow_y, glow_z, alpha=glow_alpha, color='#FFC107',
                       linewidth=0, antialiased=True)

    # =========================================================================
    # SETTINGS
    # =========================================================================
    ax.set_xlim(-8, 12)
    ax.set_ylim(-8, 8)
    ax.set_zlim(-6, 6)
    ax.set_box_aspect([1.2, 1, 0.75])
    ax.axis('off')
    ax.view_init(elev=15, azim=-60)

    # =========================================================================
    # SAVE
    # =========================================================================
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_dir = os.path.join(script_dir, '..', 'plots')
    os.makedirs(output_dir, exist_ok=True)

    png_path = os.path.join(output_dir, 'bootstrap_qcd_visual.png')
    plt.savefig(png_path, dpi=250, bbox_inches='tight', facecolor='#0a0a1a',
                pad_inches=0.1)
    print(f"Saved: {png_path}")
    plt.close()

if __name__ == "__main__":
    create_visual()

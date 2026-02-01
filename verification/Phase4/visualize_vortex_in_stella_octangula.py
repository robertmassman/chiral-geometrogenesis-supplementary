#!/usr/bin/env python3
"""
3D Visualization: Chiral Vortex within Stella Octangula
========================================================

Shows the chiral vortex (particle) embedded within the stella octangula
geometry - two interpenetrating tetrahedra that form the boundary ∂S
where the chiral field χ lives.

The vortex is a topological defect in the chiral condensate that exists
on this pre-geometric structure.

Physical Justification (from proof documents):
- Theorem 0.2.1: At center of stella octangula, χ_total(0) = 0 due to
  phase cancellation (1 + ω + ω² = 0 where ω = e^{i2π/3})
- The center is a NODE where destructive interference creates a defect
- Energy ρ(0) ≠ 0 even though χ_total(0) = 0 (energy redistributed, not destroyed)
- Theorem 4.1.1: Solitons (skyrmions) are spherically symmetric about center
  with hedgehog ansatz f(0) = π, f(∞) = 0
- The vortex core is at r=0 where phase is undefined - exactly the stella center

Reference:
- Definition 0.1.1 (Stella Octangula Boundary Topology)
- Theorem 0.2.1 (Total Field Superposition) - χ_total(0) = 0
- Theorem 4.1.1 (Existence of Solitons) - Hedgehog ansatz
- Theorem 5.3.1 (Torsion from Chiral Current)
"""

import numpy as np
import plotly.graph_objects as go
from colorsys import hsv_to_rgb

def create_tetrahedron_vertices(scale=1.0):
    """
    Create vertices of T₊ tetrahedron per Definition 0.1.1.

    Vertex coordinates (from Definition 0.1.1 §2.2):
    - v_R = (1, 1, 1)/√3     (Red)
    - v_G = (1, -1, -1)/√3   (Green)
    - v_B = (-1, 1, -1)/√3   (Blue)
    - v_W = (-1, -1, 1)/√3   (White/singlet)
    """
    vertices = np.array([
        [1, 1, 1],      # R (Red)
        [1, -1, -1],    # G (Green)
        [-1, 1, -1],    # B (Blue)
        [-1, -1, 1]     # W (White/singlet)
    ]) * scale / np.sqrt(3)
    return vertices

# Vertex labels per Definition 0.1.1
T_PLUS_LABELS = ['R', 'G', 'B', 'W']
T_MINUS_LABELS = ['R̄', 'Ḡ', 'B̄', 'W̄']

def create_stella_octangula_vertices(scale=1.0):
    """
    Create the 8 vertices of the stella octangula.
    Two interpenetrating tetrahedra T₊ and T₋.
    """
    # T₊: upward pointing tetrahedron
    t_plus = create_tetrahedron_vertices(scale)

    # T₋: downward pointing (inverted) - rotate 90° around z and invert
    t_minus = -t_plus  # Dual tetrahedron

    return t_plus, t_minus

def main():
    fig = go.Figure()

    scale = 2.0
    t_plus, t_minus = create_stella_octangula_vertices(scale)

    # =========================================================================
    # STELLA OCTANGULA - Two interpenetrating tetrahedra
    # =========================================================================

    # Define faces for each tetrahedron (vertex indices)
    faces = [
        [0, 1, 2],
        [0, 1, 3],
        [0, 2, 3],
        [1, 2, 3]
    ]

    # T₊ (first tetrahedron) - semi-transparent blue
    for face in faces:
        v = t_plus[face]
        fig.add_trace(go.Mesh3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            i=[0], j=[1], k=[2],
            color='rgba(100, 149, 237, 0.25)',
            flatshading=True,
            showlegend=False,
            hoverinfo='skip',
        ))

    # T₋ (second tetrahedron) - semi-transparent orange
    for face in faces:
        v = t_minus[face]
        fig.add_trace(go.Mesh3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            i=[0], j=[1], k=[2],
            color='rgba(255, 140, 0, 0.25)',
            flatshading=True,
            showlegend=False,
            hoverinfo='skip',
        ))

    # Edges for T₊
    edges = [[0,1], [0,2], [0,3], [1,2], [1,3], [2,3]]
    for edge in edges:
        v = t_plus[edge]
        fig.add_trace(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines',
            line=dict(color='cornflowerblue', width=4),
            showlegend=False,
            hoverinfo='skip',
        ))

    # Edges for T₋
    for edge in edges:
        v = t_minus[edge]
        fig.add_trace(go.Scatter3d(
            x=v[:, 0], y=v[:, 1], z=v[:, 2],
            mode='lines',
            line=dict(color='darkorange', width=4),
            showlegend=False,
            hoverinfo='skip',
        ))

    # Vertices with labels (Definition 0.1.1 §2.2)
    # T₊ vertices: R, G, B, W
    vertex_colors_plus = ['red', 'green', 'blue', 'white']
    for i, (label, color) in enumerate(zip(T_PLUS_LABELS, vertex_colors_plus)):
        fig.add_trace(go.Scatter3d(
            x=[t_plus[i, 0]], y=[t_plus[i, 1]], z=[t_plus[i, 2]],
            mode='markers+text',
            marker=dict(size=10, color=color, line=dict(color='black', width=2)),
            text=[label],
            textposition='top center',
            textfont=dict(size=14, color='black', family='Arial Black'),
            name=f'T₊: {label}',
            hovertemplate=f'T₊ vertex: {label}<br>Color charge<extra></extra>',
            showlegend=False,
        ))

    # T₋ vertices: R̄, Ḡ, B̄, W̄ (antipodal)
    vertex_colors_minus = ['darkred', 'darkgreen', 'darkblue', 'gray']
    for i, (label, color) in enumerate(zip(T_MINUS_LABELS, vertex_colors_minus)):
        fig.add_trace(go.Scatter3d(
            x=[t_minus[i, 0]], y=[t_minus[i, 1]], z=[t_minus[i, 2]],
            mode='markers+text',
            marker=dict(size=10, color=color, line=dict(color='black', width=2)),
            text=[label],
            textposition='bottom center',
            textfont=dict(size=14, color='black', family='Arial Black'),
            name=f'T₋: {label}',
            hovertemplate=f'T₋ vertex: {label}<br>Anti-color charge<extra></extra>',
            showlegend=False,
        ))

    # Add legend entries for the two tetrahedra
    fig.add_trace(go.Scatter3d(
        x=[None], y=[None], z=[None],
        mode='markers',
        marker=dict(size=8, color='cornflowerblue'),
        name='T₊ (R,G,B,W)',
    ))
    fig.add_trace(go.Scatter3d(
        x=[None], y=[None], z=[None],
        mode='markers',
        marker=dict(size=8, color='darkorange'),
        name='T₋ (R̄,Ḡ,B̄,W̄)',
    ))

    # =========================================================================
    # CHIRAL VORTEX - Along W-W̄ axis where χ_total = 0
    # =========================================================================
    # From the proof documents:
    # - χ_total = 0 requires P_R = P_G = P_B
    # - This occurs along the line (t, t, -t), i.e., the W̄-W direction
    # - W̄ = (1, 1, -1)/√3, W = (-1, -1, 1)/√3

    # W-W̄ axis direction (normalized)
    w_axis = np.array([1, 1, -1]) / np.sqrt(3)  # Points from W toward W̄

    # Perpendicular basis vectors for the helicoid plane
    # Chosen so that e1 × e2 = +w_axis (counterclockwise when viewed from W̄)
    # This matches the physical phase winding: R(0) → B(4π/3) → G(2π/3) counterclockwise
    e1 = np.array([1, 1, 2]) / np.sqrt(6)   # was e2
    e2 = np.array([1, -1, 0]) / np.sqrt(2)  # was e1

    # Create the vortex helicoid around W-W̄ axis
    # Keep it small and clear to show the spiral structure
    nr, nphi = 50, 100
    r_max = 0.6  # Smaller radius for clearer spiral visualization
    r = np.linspace(0.06, r_max, nr)
    phi = np.linspace(0, 2 * np.pi, nphi)
    R, PHI = np.meshgrid(r, phi)

    # Phase winding with amplitude profile (funnel shape: |χ| → 0 at core)
    xi = 0.12  # Coherence length
    amplitude = np.tanh(R / xi)
    THETA = PHI

    # Height along W-W̄ axis - one full turn of the helix
    height_scale = 0.25  # Compact helix centered at origin
    height = THETA * amplitude * height_scale
    height = height - np.pi * height_scale  # Center at origin

    # No tapering - keep the helicoid shape clear
    R_tapered = R

    # Convert to 3D coordinates using tapered radius
    # Position = height * w_axis + r_tapered * (cos(φ)*e1 + sin(φ)*e2)
    X_vortex = height * w_axis[0] + R_tapered * (np.cos(PHI) * e1[0] + np.sin(PHI) * e2[0])
    Y_vortex = height * w_axis[1] + R_tapered * (np.cos(PHI) * e1[1] + np.sin(PHI) * e2[1])
    Z_vortex = height * w_axis[2] + R_tapered * (np.cos(PHI) * e1[2] + np.sin(PHI) * e2[2])

    # Current magnitude for brightness
    current_mag_norm = 1.0 - (R - 0.06) / (r_max - 0.06)
    current_mag_norm = np.clip(current_mag_norm, 0, 1)

    # Phase for hue
    hue = (THETA / (2 * np.pi)) % 1.0

    # Create colors
    colors = np.zeros((nphi, nr, 3))
    for i in range(nphi):
        for j in range(nr):
            h = hue[i, j]
            c = current_mag_norm[i, j]
            s = 1.0 - c
            v = c
            rgb = hsv_to_rgb(h, s, v)
            colors[i, j] = rgb

    def rgb_to_str(rgb):
        return f'rgb({int(rgb[0]*255)},{int(rgb[1]*255)},{int(rgb[2]*255)})'

    # Flatten for mesh3d
    x_flat = X_vortex.flatten()
    y_flat = Y_vortex.flatten()
    z_flat = Z_vortex.flatten()
    colors_flat = colors.reshape(-1, 3)

    # Create triangular mesh
    i_indices, j_indices, k_indices = [], [], []
    for i in range(nphi - 1):
        for j in range(nr - 1):
            idx = i * nr + j
            idx_right = i * nr + (j + 1)
            idx_up = (i + 1) * nr + j
            idx_diag = (i + 1) * nr + (j + 1)
            i_indices.extend([idx, idx_right])
            j_indices.extend([idx_right, idx_diag])
            k_indices.extend([idx_up, idx_up])

    vertex_colors = [rgb_to_str(c) for c in colors_flat]

    fig.add_trace(go.Mesh3d(
        x=x_flat, y=y_flat, z=z_flat,
        i=i_indices, j=j_indices, k=k_indices,
        vertexcolor=vertex_colors,
        opacity=0.95,
        name='Chiral vortex (particle)',
        hovertemplate='Chiral field χ<br>Vortex = topological defect<extra></extra>',
        flatshading=False,
    ))

    # Vortex core along W-W̄ axis (particle location)
    # The core lies along the line where P_R = P_G = P_B, i.e., χ_total = 0
    # Extends from W (t=-2) to W̄ (t=+2) in scaled coordinates
    t_W = -2.0  # Position of W along w_axis
    t_Wbar = 2.0  # Position of W̄ along w_axis
    t_core = np.linspace(t_W, t_Wbar, 50)
    x_core = t_core * w_axis[0]
    y_core = t_core * w_axis[1]
    z_core = t_core * w_axis[2]

    fig.add_trace(go.Scatter3d(
        x=x_core, y=y_core, z=z_core,
        mode='lines',
        line=dict(color='red', width=8),
        name='Vortex core (W-W̄ axis)',
        hovertemplate='Topological defect along W-W̄ axis<br>P_R = P_G = P_B here<br>χ_total = 0 (phase cancellation)<extra></extra>',
    ))

    # Core markers at W, center, and W̄
    core_t_positions = [t_W, 0, t_Wbar]
    # Don't add markers at W and W̄ since the vertices are already there

    # Center point of stella octangula (origin)
    fig.add_trace(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=12, color='yellow', symbol='diamond',
                    line=dict(color='black', width=2)),
        name='Center (origin)',
        hovertemplate='Center of stella octangula<br>x = (0, 0, 0)<br>Equidistant from all 8 vertices<br>χ_total(0) = 0<extra></extra>',
    ))

    # =========================================================================
    # TOPOLOGICAL WINDING LOOP (perpendicular to W-W̄ axis)
    # =========================================================================
    r_loop = 0.35  # Radius of the demonstration loop
    n_loop = 80
    phi_loop = np.linspace(0, 2*np.pi, n_loop)
    amplitude_loop = np.tanh(r_loop / xi)
    height_loop = phi_loop * amplitude_loop * height_scale - np.pi * height_scale

    # Loop in plane perpendicular to W-W̄ axis (no tapering)
    x_loop = height_loop * w_axis[0] + r_loop * (np.cos(phi_loop) * e1[0] + np.sin(phi_loop) * e2[0])
    y_loop = height_loop * w_axis[1] + r_loop * (np.cos(phi_loop) * e1[1] + np.sin(phi_loop) * e2[1])
    z_loop = height_loop * w_axis[2] + r_loop * (np.cos(phi_loop) * e1[2] + np.sin(phi_loop) * e2[2])

    fig.add_trace(go.Scatter3d(
        x=x_loop, y=y_loop, z=z_loop,
        mode='lines',
        line=dict(color='white', width=5),
        name='Winding loop (2π)',
        hovertemplate='Phase winds 2π around W-W̄ axis<extra></extra>',
    ))

    # =========================================================================
    # Layout
    # =========================================================================
    fig.update_layout(
        title=dict(
            text='Chiral Vortex along W-W̄ Axis: χ_total = 0 Where P_R = P_G = P_B',
            font=dict(size=13),
            x=0.5,
        ),
        scene=dict(
            xaxis=dict(title='', showticklabels=False, showgrid=False, zeroline=False),
            yaxis=dict(title='', showticklabels=False, showgrid=False, zeroline=False),
            zaxis=dict(title='', showticklabels=False, showgrid=False, zeroline=False),
            camera=dict(eye=dict(x=1.8, y=1.8, z=1.2)),
            aspectmode='cube',
            bgcolor='rgba(240,240,245,1)',
        ),
        legend=dict(
            x=0.02, y=0.98,
            bgcolor='rgba(255,255,255,0.9)',
            bordercolor='gray', borderwidth=1,
        ),
        margin=dict(l=0, r=0, t=50, b=0),
        annotations=[
            dict(
                text='<b>Stella Octangula ∂S (Def 0.1.1):</b><br>'
                     'T₊ (blue): R, G, B, W vertices<br>'
                     'T₋ (orange): R̄, Ḡ, B̄, W̄ (antipodal)<br>'
                     'v_c̄ = −v_c for all colors',
                x=0.98, y=0.98,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=10),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=6,
                align='left',
                xanchor='right',
            ),
            dict(
                text='<b>Vortex along W-W̄ axis:</b><br>'
                     'χ_total = 0 where P_R = P_G = P_B<br>'
                     'This is the line (t,t,-t) ∝ W-W̄<br>'
                     'Phase cancellation: 1 + ω + ω² = 0',
                x=0.02, y=0.18,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=10),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=6,
                align='left',
            ),
            dict(
                text='<b>W-W̄ axis (singlet direction):</b><br>'
                     'W = (-1,-1,1)/√3 (white vertex)<br>'
                     'W̄ = (1,1,-1)/√3 (anti-white)<br>'
                     'Perpendicular to R-G-B plane',
                x=0.02, y=0.05,
                xref='paper', yref='paper',
                showarrow=False,
                font=dict(size=9),
                bgcolor='rgba(255,255,255,0.95)',
                bordercolor='gray', borderwidth=1, borderpad=4,
                align='left',
            ),
        ],
    )

    # Save
    fig.write_html('plots/vortex_in_stella_octangula.html')
    fig.write_image('plots/vortex_in_stella_octangula.png', width=1200, height=900, scale=2)
    fig.write_image('plots/vortex_in_stella_octangula.pdf', width=1200, height=900)

    print("Saved: plots/vortex_in_stella_octangula.html (interactive)")
    print("Saved: plots/vortex_in_stella_octangula.png")
    print("Saved: plots/vortex_in_stella_octangula.pdf")

if __name__ == '__main__':
    main()

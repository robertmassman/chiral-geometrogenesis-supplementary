#!/usr/bin/env python3
"""
Visual Image: Bootstrap & QCD Scale Determination (Plotly)
===========================================================

Interactive 3D visualization showing the derivation chain from
stella octangula to QCD scale - no text, pure geometry.
"""

import plotly.graph_objects as go
import numpy as np
import os

def create_tetrahedron_mesh(vertices, color, opacity=0.85):
    """Create a mesh3d for a tetrahedron."""
    # Faces: each row is indices of 3 vertices forming a face
    i = [0, 0, 0, 1]
    j = [1, 1, 2, 2]
    k = [2, 3, 3, 3]

    return go.Mesh3d(
        x=vertices[:, 0],
        y=vertices[:, 1],
        z=vertices[:, 2],
        i=i, j=j, k=k,
        color=color,
        opacity=opacity,
        flatshading=True,
        lighting=dict(ambient=0.6, diffuse=0.8, specular=0.3),
        lightposition=dict(x=100, y=200, z=300)
    )

def create_tetrahedron_edges(vertices, color, width=3):
    """Create edges for a tetrahedron."""
    edges = [
        (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)
    ]

    x_lines, y_lines, z_lines = [], [], []
    for e in edges:
        x_lines.extend([vertices[e[0], 0], vertices[e[1], 0], None])
        y_lines.extend([vertices[e[0], 1], vertices[e[1], 1], None])
        z_lines.extend([vertices[e[0], 2], vertices[e[1], 2], None])

    return go.Scatter3d(
        x=x_lines, y=y_lines, z=z_lines,
        mode='lines',
        line=dict(color=color, width=width),
        hoverinfo='skip'
    )

def create_sphere_wireframe(center, radius, color, opacity=0.15, n_lines=20):
    """Create a wireframe sphere for emanating waves."""
    traces = []

    # Latitude lines
    for phi in np.linspace(0, np.pi, n_lines//2):
        theta = np.linspace(0, 2*np.pi, 50)
        x = center[0] + radius * np.sin(phi) * np.cos(theta)
        y = center[1] + radius * np.sin(phi) * np.sin(theta)
        z = center[2] + radius * np.cos(phi) * np.ones_like(theta)
        traces.append(go.Scatter3d(
            x=x, y=y, z=z,
            mode='lines',
            line=dict(color=color, width=1),
            opacity=opacity,
            hoverinfo='skip'
        ))

    # Longitude lines
    for theta in np.linspace(0, 2*np.pi, n_lines):
        phi = np.linspace(0, np.pi, 30)
        x = center[0] + radius * np.sin(phi) * np.cos(theta)
        y = center[1] + radius * np.sin(phi) * np.sin(theta)
        z = center[2] + radius * np.cos(phi)
        traces.append(go.Scatter3d(
            x=x, y=y, z=z,
            mode='lines',
            line=dict(color=color, width=1),
            opacity=opacity,
            hoverinfo='skip'
        ))

    return traces

def create_visual():
    """Create interactive Plotly visualization."""

    fig = go.Figure()

    # =========================================================================
    # STELLA OCTANGULA (center-left)
    # =========================================================================
    a = 2.0
    t1_verts = np.array([[a,a,a], [-a,-a,a], [-a,a,-a], [a,-a,-a]])
    t2_verts = np.array([[-a,-a,-a], [a,a,-a], [a,-a,a], [-a,a,a]])

    # Add tetrahedra meshes
    fig.add_trace(create_tetrahedron_mesh(t1_verts, '#00BCD4', opacity=0.75))
    fig.add_trace(create_tetrahedron_mesh(t2_verts, '#FF5722', opacity=0.75))

    # Add tetrahedra edges
    fig.add_trace(create_tetrahedron_edges(t1_verts, '#4DD0E1', width=4))
    fig.add_trace(create_tetrahedron_edges(t2_verts, '#FF8A65', width=4))

    # =========================================================================
    # EMANATING WAVES (Casimir vacuum energy)
    # =========================================================================
    wave_colors = ['#7C4DFF', '#9575CD', '#B39DDB', '#D1C4E9', '#EDE7F6']
    for r, color, op in zip([3.0, 4.0, 5.0, 6.5, 8.0], wave_colors, [0.25, 0.20, 0.15, 0.10, 0.06]):
        for trace in create_sphere_wireframe([0, 0, 0], r, color, opacity=op, n_lines=16):
            fig.add_trace(trace)

    # =========================================================================
    # SCALE HIERARCHY SPIRAL (exp(128π/9) - 19 orders of magnitude)
    # =========================================================================
    t = np.linspace(0, 6*np.pi, 500)
    spiral_scale = 0.08
    r_spiral = spiral_scale * np.exp(0.15 * t)

    x_offset = 6
    x_spiral = r_spiral * np.cos(t) + x_offset
    y_spiral = r_spiral * np.sin(t)
    z_spiral = t * 0.3 - 3

    # Color gradient: purple (Planck) to gold (QCD)
    colors = np.linspace(0, 1, len(t))

    fig.add_trace(go.Scatter3d(
        x=x_spiral, y=y_spiral, z=z_spiral,
        mode='lines',
        line=dict(
            color=colors,
            colorscale='Plasma',
            width=8
        ),
        hoverinfo='skip'
    ))

    # =========================================================================
    # CONNECTING FLOW LINES (topology → QCD)
    # =========================================================================
    for vert in t1_verts:
        t_flow = np.linspace(0, 1, 50)
        start = vert
        end = np.array([x_offset - 2, 0, 0])
        mid = (start + end) / 2 + np.array([0, 0, 2])

        x_flow = (1-t_flow)**2 * start[0] + 2*(1-t_flow)*t_flow * mid[0] + t_flow**2 * end[0]
        y_flow = (1-t_flow)**2 * start[1] + 2*(1-t_flow)*t_flow * mid[1] + t_flow**2 * end[1]
        z_flow = (1-t_flow)**2 * start[2] + 2*(1-t_flow)*t_flow * mid[2] + t_flow**2 * end[2]

        fig.add_trace(go.Scatter3d(
            x=x_flow, y=y_flow, z=z_flow,
            mode='lines',
            line=dict(color='#4DD0E1', width=2),
            opacity=0.4,
            hoverinfo='skip'
        ))

    for vert in t2_verts:
        t_flow = np.linspace(0, 1, 50)
        start = vert
        end = np.array([x_offset - 2, 0, 0])
        mid = (start + end) / 2 + np.array([0, 0, -2])

        x_flow = (1-t_flow)**2 * start[0] + 2*(1-t_flow)*t_flow * mid[0] + t_flow**2 * end[0]
        y_flow = (1-t_flow)**2 * start[1] + 2*(1-t_flow)*t_flow * mid[1] + t_flow**2 * end[1]
        z_flow = (1-t_flow)**2 * start[2] + 2*(1-t_flow)*t_flow * mid[2] + t_flow**2 * end[2]

        fig.add_trace(go.Scatter3d(
            x=x_flow, y=y_flow, z=z_flow,
            mode='lines',
            line=dict(color='#FF8A65', width=2),
            opacity=0.4,
            hoverinfo='skip'
        ))

    # =========================================================================
    # THREE COLOR HELICES (RGB color fields)
    # =========================================================================
    t_helix = np.linspace(0, 4*np.pi, 200)
    helix_r = 0.4
    helix_colors = ['#F44336', '#4CAF50', '#2196F3']  # Red, Green, Blue

    for offset_angle, color in zip([0, 2*np.pi/3, 4*np.pi/3], helix_colors):
        x_h = helix_r * np.cos(t_helix + offset_angle)
        y_h = helix_r * np.sin(t_helix + offset_angle)
        z_h = t_helix * 0.15 - 1

        fig.add_trace(go.Scatter3d(
            x=x_h, y=y_h, z=z_h,
            mode='lines',
            line=dict(color=color, width=5),
            opacity=0.8,
            hoverinfo='skip'
        ))

    # =========================================================================
    # GOLDEN ORB (emergent QCD scale √σ)
    # =========================================================================
    orb_center = [x_spiral[-1], y_spiral[-1], z_spiral[-1]]

    # Create sphere mesh for the orb
    u = np.linspace(0, 2*np.pi, 30)
    v = np.linspace(0, np.pi, 20)
    orb_r = 0.8

    x_orb = orb_r * np.outer(np.cos(u), np.sin(v)) + orb_center[0]
    y_orb = orb_r * np.outer(np.sin(u), np.sin(v)) + orb_center[1]
    z_orb = orb_r * np.outer(np.ones(np.size(u)), np.cos(v)) + orb_center[2]

    fig.add_trace(go.Surface(
        x=x_orb, y=y_orb, z=z_orb,
        colorscale=[[0, '#FFD700'], [1, '#FFC107']],
        showscale=False,
        opacity=0.95,
        lighting=dict(ambient=0.7, diffuse=0.8, specular=0.5),
        lightposition=dict(x=100, y=200, z=300),
        hoverinfo='skip'
    ))

    # Glow layers around orb
    for glow_r, glow_op in [(1.0, 0.3), (1.3, 0.15), (1.6, 0.08)]:
        x_glow = glow_r * np.outer(np.cos(u), np.sin(v)) + orb_center[0]
        y_glow = glow_r * np.outer(np.sin(u), np.sin(v)) + orb_center[1]
        z_glow = glow_r * np.outer(np.ones(np.size(u)), np.cos(v)) + orb_center[2]

        fig.add_trace(go.Surface(
            x=x_glow, y=y_glow, z=z_glow,
            colorscale=[[0, '#FFC107'], [1, '#FFEB3B']],
            showscale=False,
            opacity=glow_op,
            hoverinfo='skip'
        ))

    # =========================================================================
    # LAYOUT
    # =========================================================================
    fig.update_layout(
        scene=dict(
            xaxis=dict(visible=False, range=[-10, 14]),
            yaxis=dict(visible=False, range=[-10, 10]),
            zaxis=dict(visible=False, range=[-8, 8]),
            bgcolor='#0a0a1a',
            camera=dict(
                eye=dict(x=1.5, y=1.2, z=0.6),
                center=dict(x=0.15, y=0, z=0)
            ),
            aspectmode='manual',
            aspectratio=dict(x=1.4, y=1, z=0.8)
        ),
        paper_bgcolor='#0a0a1a',
        margin=dict(l=0, r=0, t=0, b=0),
        showlegend=False,
        width=1400,
        height=800
    )

    # =========================================================================
    # SAVE
    # =========================================================================
    script_dir = os.path.dirname(os.path.abspath(__file__))
    output_dir = os.path.join(script_dir, '..', 'plots')
    os.makedirs(output_dir, exist_ok=True)

    html_path = os.path.join(output_dir, 'bootstrap_qcd_visual.html')
    fig.write_html(html_path, include_plotlyjs=True, full_html=True)
    print(f"Saved: {html_path}")

    # Also save as static image if kaleido is available
    try:
        png_path = os.path.join(output_dir, 'bootstrap_qcd_visual_plotly.png')
        fig.write_image(png_path, width=1400, height=800, scale=2)
        print(f"Saved: {png_path}")
    except Exception as e:
        print(f"Note: Could not save PNG (install kaleido for static export): {e}")

    return fig

if __name__ == "__main__":
    fig = create_visual()
    fig.show()

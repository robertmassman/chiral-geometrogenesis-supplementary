#!/usr/bin/env python3
"""
Figure: Stella Octangula as 2D Weight Space + 1D Radial Direction

Plotly 3D visualization matching fig_vertex_face_duality.py style:
  - Clean axes-off presentation with faint bounding cube
  - T+ (fundamental) with colored faces and black edges
  - T- (anti-fundamental) as faint red wireframe
  - Weight plane (semi-transparent, perpendicular to [1,1,1])
  - Singlet axis (green arrow from W̄ to W)
  - Projection lines from 3D vertices onto weight plane

Visualizes Proposition 0.0.40: d_embed = rank(SU(3)) + 1 = 2 + 1 = 3.

Proof Document: docs/proofs/foundations/Proposition-0.0.40-Embedding-Dimension-From-Confinement.md
Paper Section: Paper 1, Proposition 0.0.40

Output: fig_stella_dimension_decomposition.pdf, fig_stella_dimension_decomposition.png
"""

import numpy as np
import plotly.graph_objects as go
from pathlib import Path

# Output directory
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

s3 = np.sqrt(3)

# ── Vertices (matching fig_vertex_face_duality.py convention) ────────────

TP = {
    'R': np.array([1, -1, -1]) / s3,
    'G': np.array([-1, 1, -1]) / s3,
    'B': np.array([-1, -1, 1]) / s3,
    'W': np.array([1, 1, 1]) / s3,
}

TM = {
    'aR': np.array([-1, 1, 1]) / s3,
    'aG': np.array([1, -1, 1]) / s3,
    'aB': np.array([1, 1, -1]) / s3,
    'aW': np.array([-1, -1, -1]) / s3,
}

# Singlet axis direction
n_hat = np.array([1, 1, 1]) / s3
# Projection matrix onto weight plane (perpendicular to [1,1,1])
P_weight = np.eye(3) - np.outer(n_hat, n_hat)

# Orthonormal basis vectors in the weight plane
e1 = np.array([1, -1, 0]) / np.sqrt(2)
e2 = np.array([1, 1, -2]) / np.sqrt(6)

# Colors (matching reference)
CC = {
    'R': 'rgb(232, 38, 38)',
    'G': 'rgb(38, 174, 38)',
    'B': 'rgb(51, 102, 220)',
    'W': 'rgb(140, 140, 140)',
}
CC_dark = {
    'aR': 'rgb(192, 57, 43)',
    'aG': 'rgb(30, 132, 73)',
    'aB': 'rgb(40, 116, 166)',
    'aW': 'rgb(140, 140, 140)',
}

CUBE_HALF = 1.0 / s3


def make_tet_mesh(verts_dict, keys, color, opacity=0.15):
    """Create a Mesh3d tetrahedron from 4 named vertices."""
    pts = np.array([verts_dict[k] for k in keys])
    return go.Mesh3d(
        x=pts[:, 0], y=pts[:, 1], z=pts[:, 2],
        i=[0, 0, 0, 1], j=[1, 1, 2, 2], k=[2, 3, 3, 3],
        color=color, opacity=opacity,
        flatshading=True, showlegend=False,
    )


def make_tet_edges(verts_dict, keys, color, width=2.5, dash=None):
    """Create edge lines for a tetrahedron."""
    pts = np.array([verts_dict[k] for k in keys])
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    traces = []
    for i, j in edges:
        traces.append(go.Scatter3d(
            x=[pts[i, 0], pts[j, 0], None],
            y=[pts[i, 1], pts[j, 1], None],
            z=[pts[i, 2], pts[j, 2], None],
            mode='lines',
            line=dict(color=color, width=width, dash=dash),
            showlegend=False, hoverinfo='skip',
        ))
    return traces


def make_cube_wireframe(half, color='rgba(160,160,160,0.2)', width=1):
    """Faint bounding cube wireframe."""
    h = half
    c = np.array([
        [-h, -h, -h], [h, -h, -h], [h, h, -h], [-h, h, -h],
        [-h, -h, h], [h, -h, h], [h, h, h], [-h, h, h],
    ])
    edges = [(0, 1), (1, 2), (2, 3), (3, 0),
             (4, 5), (5, 6), (6, 7), (7, 4),
             (0, 4), (1, 5), (2, 6), (3, 7)]
    x, y, z = [], [], []
    for i, j in edges:
        x += [c[i, 0], c[j, 0], None]
        y += [c[i, 1], c[j, 1], None]
        z += [c[i, 2], c[j, 2], None]
    return go.Scatter3d(
        x=x, y=y, z=z, mode='lines',
        line=dict(color=color, width=width),
        showlegend=False, hoverinfo='skip',
    )


def make_weight_plane(radius=2 * np.sqrt(2) / 3):
    """Semi-transparent hexagonal weight plane perpendicular to [1,1,1].

    Radius = 2√2/3 ≈ 0.9428, the exact projection distance of color vertices.
    Rotated 30° so hexagon vertices align with projected T+/T- vertices:
      R→30°, G→150°, B→-90°, R̄→-150°, Ḡ→-30°, B̄→90°
    """
    n_seg = 6
    # Offset by 30° so vertices align with projected tet vertices
    theta = np.linspace(0, 2 * np.pi, n_seg + 1) + np.radians(30)
    pts = np.array([radius * (np.cos(t) * e1 + np.sin(t) * e2) for t in theta])

    # Fan triangulation from center
    all_pts = np.vstack([[0, 0, 0], pts[:n_seg]])
    i_arr = [0] * n_seg
    j_arr = list(range(1, n_seg + 1))
    k_arr = list(range(2, n_seg + 1)) + [1]

    traces = [
        go.Mesh3d(
            x=all_pts[:, 0], y=all_pts[:, 1], z=all_pts[:, 2],
            i=i_arr, j=j_arr, k=k_arr,
            color='rgba(100,160,220,0.25)', opacity=0.25,
            flatshading=True, showlegend=False, hoverinfo='skip',
        )
    ]

    # Hexagon edge outline (solid, visible)
    traces.append(go.Scatter3d(
        x=list(pts[:, 0]) + [pts[0, 0]],
        y=list(pts[:, 1]) + [pts[0, 1]],
        z=list(pts[:, 2]) + [pts[0, 2]],
        mode='lines',
        line=dict(color='rgba(50,100,180,0.6)', width=3, dash='dash'),
        showlegend=False, hoverinfo='skip',
    ))
    return traces


def make_projection_line(v3d, v_proj, color, width=1.5):
    """Dashed projection line from 3D vertex to weight plane."""
    return go.Scatter3d(
        x=[v3d[0], v_proj[0]],
        y=[v3d[1], v_proj[1]],
        z=[v3d[2], v_proj[2]],
        mode='lines',
        line=dict(color=color, width=width, dash='dot'),
        showlegend=False, hoverinfo='skip',
    )


def make_cone_arrow(start, end, color='green', size=0.06):
    """Arrow as a cone at the tip of a line."""
    direction = end - start
    return go.Cone(
        x=[end[0]], y=[end[1]], z=[end[2]],
        u=[direction[0]], v=[direction[1]], w=[direction[2]],
        sizemode='absolute', sizeref=size,
        colorscale=[[0, color], [1, color]],
        showscale=False, showlegend=False, hoverinfo='skip',
    )


def create_figure():
    """Build the full decomposition figure."""
    fig = go.Figure()

    # ── Bounding cube (faint) ────────────────────────────────────────
    fig.add_trace(make_cube_wireframe(CUBE_HALF))

    # ── Weight plane ─────────────────────────────────────────────────
    for tr in make_weight_plane():
        fig.add_trace(tr)

    # ── T- mesh and edges (semi-transparent red background) ────────────
    tm_keys = list(TM.keys())
    fig.add_trace(make_tet_mesh(TM, tm_keys, 'rgba(220,80,60,0.25)', opacity=0.25))
    for tr in make_tet_edges(TM, tm_keys, 'rgba(220,80,60,0.45)', width=2, dash='dash'):
        fig.add_trace(tr)

    # ── T+ with vertex-color gradients ───────────────────────────────
    # R→red, G→green, B→blue, W→white: faces containing W gradient
    # toward white (confinement into color singlet).
    # Matching fig_vertex_face_duality.py colors.
    tp_keys = ['R', 'G', 'B', 'W']
    tp_pts = np.array([TP[k] for k in tp_keys])
    tp_vertex_colors = [
        'rgb(232, 38, 38)',    # R — red
        'rgb(38, 174, 38)',    # G — green
        'rgb(51, 102, 220)',   # B — blue
        'rgb(255, 255, 255)',  # W — white (singlet)
    ]
    fig.add_trace(go.Mesh3d(
        x=tp_pts[:, 0], y=tp_pts[:, 1], z=tp_pts[:, 2],
        i=[0, 0, 0, 1], j=[1, 1, 2, 2], k=[2, 3, 3, 3],
        vertexcolor=tp_vertex_colors,
        opacity=0.85,
        flatshading=False,  # smooth interpolation for gradients
        lighting=dict(ambient=0.95, diffuse=0.05, specular=0.0),
        showlegend=False,
    ))
    for tr in make_tet_edges(TP, tp_keys, 'black', width=3.5):
        fig.add_trace(tr)

    # ── Singlet axis (green line W̄ → W) ─────────────────────────────
    W = TP['W']
    Wbar = TM['aW']
    extend = 0.15
    axis_start = Wbar - extend * n_hat
    axis_end = W + extend * n_hat

    fig.add_trace(go.Scatter3d(
        x=[axis_start[0], axis_end[0]],
        y=[axis_start[1], axis_end[1]],
        z=[axis_start[2], axis_end[2]],
        mode='lines',
        line=dict(color='green', width=6),
        showlegend=False, hoverinfo='skip',
    ))
    fig.add_trace(make_cone_arrow(Wbar, W, color='green', size=0.05))

    # ── Projection lines (vertex → weight plane) ────────────────────
    for c_name, color in [('R', 'rgba(232,38,38,0.4)'),
                          ('G', 'rgba(38,174,38,0.4)'),
                          ('B', 'rgba(51,102,220,0.4)')]:
        v = TP[c_name]
        vp = P_weight @ v
        fig.add_trace(make_projection_line(v, vp, color))
        # Projected dot on weight plane
        fig.add_trace(go.Scatter3d(
            x=[vp[0]], y=[vp[1]], z=[vp[2]],
            mode='markers',
            marker=dict(size=5, color=CC[c_name], opacity=0.5,
                        line=dict(color='black', width=1)),
            showlegend=False, hoverinfo='skip',
        ))

    for tm_name, color in [('aR', 'rgba(192,57,43,0.4)'),
                           ('aG', 'rgba(30,132,73,0.4)'),
                           ('aB', 'rgba(40,116,166,0.4)')]:
        v = TM[tm_name]
        vp = P_weight @ v
        fig.add_trace(make_projection_line(v, vp, color))
        fig.add_trace(go.Scatter3d(
            x=[vp[0]], y=[vp[1]], z=[vp[2]],
            mode='markers',
            marker=dict(size=4, color=CC_dark[tm_name], opacity=0.4,
                        symbol='square',
                        line=dict(color='black', width=0.5)),
            showlegend=False, hoverinfo='skip',
        ))

    # Apex projection lines to origin
    for apex in [W, Wbar]:
        fig.add_trace(go.Scatter3d(
            x=[apex[0], 0], y=[apex[1], 0], z=[apex[2], 0],
            mode='lines',
            line=dict(color='rgba(180,160,50,0.4)', width=2, dash='dot'),
            showlegend=False, hoverinfo='skip',
        ))

    # ── Vertex markers ───────────────────────────────────────────────
    # T+ color vertices (large circles)
    for c_name in ['R', 'G', 'B']:
        v = TP[c_name]
        fig.add_trace(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers+text',
            marker=dict(size=12, color=CC[c_name],
                        line=dict(color='black', width=2)),
            text=[f'v<sub>{c_name}</sub>'],
            textposition='top center',
            textfont=dict(size=13, color=CC[c_name], family='Arial Black'),
            showlegend=False, hoverinfo='skip',
        ))

    # T- color vertices (smaller squares)
    tm_labels = {'aR': 'R̄', 'aG': 'Ḡ', 'aB': 'B̄'}
    for tm_name in ['aR', 'aG', 'aB']:
        v = TM[tm_name]
        fig.add_trace(go.Scatter3d(
            x=[v[0]], y=[v[1]], z=[v[2]],
            mode='markers+text',
            marker=dict(size=8, color=CC_dark[tm_name], symbol='square',
                        line=dict(color='black', width=1.5)),
            text=[tm_labels[tm_name]],
            textposition='top center',
            textfont=dict(size=11, color=CC_dark[tm_name]),
            showlegend=False, hoverinfo='skip',
        ))

    # Apex vertices W, W̄ (gold stars → gold diamonds in plotly)
    for apex, label in [(W, 'W'), (Wbar, 'W̄')]:
        fig.add_trace(go.Scatter3d(
            x=[apex[0]], y=[apex[1]], z=[apex[2]],
            mode='markers+text',
            marker=dict(size=10, color='gold', symbol='diamond',
                        line=dict(color='black', width=2)),
            text=[label],
            textposition='top center',
            textfont=dict(size=14, color='rgb(150,120,30)',
                          family='Arial Black'),
            showlegend=False, hoverinfo='skip',
        ))

    # Center marker
    fig.add_trace(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers',
        marker=dict(size=5, color='black'),
        showlegend=False, hoverinfo='skip',
    ))

    # ── Annotation labels ────────────────────────────────────────────
    # Weight plane label (bottom of the weight plane, clear of edges)
    plane_pos = 0.70 * e2  # toward bottom of visible region
    fig.add_trace(go.Scatter3d(
        x=[plane_pos[0]], y=[plane_pos[1]], z=[plane_pos[2] - 0.06],
        mode='text',
        text=['𝔥* (2D weight plane)'],
        textfont=dict(size=11, color='rgb(34,85,170)', family='Arial Black'),
        showlegend=False, hoverinfo='skip',
    ))

    # Radial axis label (offset from W to avoid overlap)
    axis_label_pos = W + 0.18 * n_hat + np.array([0.15, 0.0, 0.0])
    fig.add_trace(go.Scatter3d(
        x=[axis_label_pos[0]], y=[axis_label_pos[1]], z=[axis_label_pos[2]],
        mode='text',
        text=['1D radial<br>(singlet)'],
        textfont=dict(size=11, color='green', family='Arial Black'),
        showlegend=False, hoverinfo='skip',
    ))

    # ── Layout (matching reference: clean, no axes, elev=28 azim=39) ──
    lim = 0.85

    # Camera position: match matplotlib view_init(elev=28, azim=39)
    # In Plotly, camera eye is the position looking toward origin.
    # We use a direct placement that reproduces the reference angle.
    r_cam = 2.2
    camera = dict(
        eye=dict(x=1.3, y=1.1, z=1.4),  # W vertex faces camera
        up=dict(x=0, y=0, z=1),
    )

    fig.update_layout(
        title=dict(
            text=('Stella Octangula: Dimension Decomposition (Prop. 0.0.40)<br>'
                  '<i>d</i><sub>embed</sub> = rank(SU(3)) + 1 '
                  '= 2 (weight) + 1 (radial) = 3'),
            font=dict(size=16, family='Arial'),
            x=0.5, xanchor='center',
        ),
        scene=dict(
            xaxis=dict(visible=False, range=[-lim, lim]),
            yaxis=dict(visible=False, range=[-lim, lim]),
            zaxis=dict(visible=False, range=[-lim, lim]),
            aspectmode='cube',
            camera=camera,
        ),
        width=900, height=800,
        margin=dict(l=10, r=10, t=70, b=10),
        paper_bgcolor='white',
        plot_bgcolor='white',
    )

    return fig


def main():
    print("Creating stella dimension decomposition figure (Plotly)...")

    fig = create_figure()

    # Save static images
    for ext in ['pdf', 'png']:
        filepath = output_dir / f'fig_stella_dimension_decomposition.{ext}'
        fig.write_image(str(filepath), scale=3 if ext == 'png' else 1)
        print(f"Saved: {filepath}")

    # Also save interactive HTML
    html_path = output_dir / 'fig_stella_dimension_decomposition.html'
    fig.write_html(str(html_path), include_plotlyjs='cdn')
    print(f"Saved: {html_path}")

    print("Done!")


if __name__ == "__main__":
    main()

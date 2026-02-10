#!/usr/bin/env python3
"""
Simple wireframe visualization of stella octangula.
Two interpenetrating tetrahedra.
"""

import numpy as np
import plotly.graph_objects as go

# Stella octangula vertices
# T+ tetrahedron
V_PLUS = np.array([
    [+1, +1, +1],
    [+1, -1, -1],
    [-1, +1, -1],
    [-1, -1, +1],
]) / np.sqrt(3)

# T- tetrahedron
V_MINUS = np.array([
    [-1, -1, -1],
    [-1, +1, +1],
    [+1, -1, +1],
    [+1, +1, -1],
]) / np.sqrt(3)

# Edges (vertex index pairs)
EDGES = [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

fig = go.Figure()

# T+ edges (cyan)
for i, j in EDGES:
    fig.add_trace(go.Scatter3d(
        x=[V_PLUS[i,0], V_PLUS[j,0]],
        y=[V_PLUS[i,1], V_PLUS[j,1]],
        z=[V_PLUS[i,2], V_PLUS[j,2]],
        mode='lines',
        line=dict(color='cyan', width=6),
        showlegend=False
    ))

# T- edges (magenta)
for i, j in EDGES:
    fig.add_trace(go.Scatter3d(
        x=[V_MINUS[i,0], V_MINUS[j,0]],
        y=[V_MINUS[i,1], V_MINUS[j,1]],
        z=[V_MINUS[i,2], V_MINUS[j,2]],
        mode='lines',
        line=dict(color='magenta', width=6),
        showlegend=False
    ))

# T+ vertices
fig.add_trace(go.Scatter3d(
    x=V_PLUS[:,0], y=V_PLUS[:,1], z=V_PLUS[:,2],
    mode='markers',
    marker=dict(size=8, color='cyan'),
    name='T+ vertices'
))

# T- vertices
fig.add_trace(go.Scatter3d(
    x=V_MINUS[:,0], y=V_MINUS[:,1], z=V_MINUS[:,2],
    mode='markers',
    marker=dict(size=8, color='magenta'),
    name='T- vertices'
))

# Center
fig.add_trace(go.Scatter3d(
    x=[0], y=[0], z=[0],
    mode='markers',
    marker=dict(size=10, color='yellow'),
    name='Center'
))

fig.update_layout(
    title='Stella Octangula Wireframe',
    scene=dict(
        xaxis=dict(title='X'),
        yaxis=dict(title='Y'),
        zaxis=dict(title='Z'),
        aspectmode='cube',
        camera=dict(eye=dict(x=1.5, y=1.5, z=1.2))
    ),
    width=800,
    height=700
)

# Save and open
html_path = '/tmp/stella_wireframe.html'
fig.write_html(html_path)
print(f"Saved: {html_path}")

import webbrowser
webbrowser.open(f'file://{html_path}')

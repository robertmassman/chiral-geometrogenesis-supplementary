#!/usr/bin/env python3
"""
Prop 0.0.39: Stella Adjoint Decomposition -- Interactive Visualization
=====================================================================
Interactive 3D Plotly visualization showing:
  1. Vertex-Face Duality: quarks on vertices, gluons on faces
  2. Quark -> Gluon Radiation: opposite-vertex rule
  3. 8+1 Decomposition: 8 corner tets (octet) + 1 central oct (singlet)
  4. Two Singlets Disambiguated: W vertex != central octahedron

Output: verification/plots/prop_0_0_39_adjoint_decomposition.html

Related Documents:
- Proof: docs/proofs/foundations/Proposition-0.0.39-Stella-Adjoint-Decomposition.md
"""

import numpy as np
import plotly.graph_objects as go

# ============================================================
# HELPER FUNCTIONS
# ============================================================

def wireframe_trace(vertices, edges, color='black', width=2, name='',
                    visible=True, legendgroup=None):
    """Create a 3D wireframe trace from vertices and edge index pairs."""
    v = np.array(vertices, dtype=float)
    x, y, z = [], [], []
    for i, j in edges:
        x += [v[i, 0], v[j, 0], None]
        y += [v[i, 1], v[j, 1], None]
        z += [v[i, 2], v[j, 2], None]
    return go.Scatter3d(
        x=x, y=y, z=z, mode='lines',
        line=dict(color=color, width=width),
        name=name, visible=visible, showlegend=bool(name),
        legendgroup=legendgroup,
    )


def tet_traces(vertices, color, opacity=0.3, edge_color=None, edge_width=2,
               name='', visible=True, legendgroup=None):
    """Mesh + wireframe for a single tetrahedron (4 vertices)."""
    v = np.array(vertices, dtype=float)
    if edge_color is None:
        edge_color = color
    mesh = go.Mesh3d(
        x=v[:, 0], y=v[:, 1], z=v[:, 2],
        i=[0, 0, 0, 1], j=[1, 1, 2, 2], k=[2, 3, 3, 3],
        color=color, opacity=opacity,
        name=name, visible=visible, showlegend=bool(name),
        flatshading=True, legendgroup=legendgroup,
    )
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    wire = wireframe_trace(v, edges, color=edge_color, width=edge_width,
                           name='', visible=visible, legendgroup=legendgroup)
    return [mesh, wire]


def oct_traces(vertices, color, opacity=0.3, edge_color=None, edge_width=2,
               name='', visible=True, legendgroup=None):
    """Mesh + wireframe for a single octahedron (6 vertices, opposite pairs 0-1, 2-3, 4-5)."""
    v = np.array(vertices, dtype=float)
    if edge_color is None:
        edge_color = color
    opp = {(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4)}
    # 8 triangular faces: one vertex from each opposite pair
    fi, fj, fk = [], [], []
    for a in [0, 1]:
        for b in [2, 3]:
            for c in [4, 5]:
                fi.append(a)
                fj.append(b)
                fk.append(c)
    mesh = go.Mesh3d(
        x=v[:, 0], y=v[:, 1], z=v[:, 2],
        i=fi, j=fj, k=fk,
        color=color, opacity=opacity,
        name=name, visible=visible, showlegend=bool(name),
        flatshading=True, legendgroup=legendgroup,
    )
    # 12 edges (all non-opposite pairs)
    edges = [(i, j) for i in range(6) for j in range(i + 1, 6) if (i, j) not in opp]
    wire = wireframe_trace(v, edges, color=edge_color, width=edge_width,
                           name='', visible=visible, legendgroup=legendgroup)
    return [mesh, wire]


def face_mesh(verts, color, opacity=0.35, name='', visible=True,
              legendgroup=None, showlegend=True):
    """Single triangular face as Mesh3d."""
    v = np.array(verts, dtype=float)
    return go.Mesh3d(
        x=v[:, 0], y=v[:, 1], z=v[:, 2],
        i=[0], j=[1], k=[2],
        color=color, opacity=opacity,
        name=name, visible=visible, showlegend=showlegend,
        flatshading=True, legendgroup=legendgroup,
    )


def text_trace(pos, text, color='#333', size=10, visible=True, name=''):
    """Text annotation at a 3D position."""
    return go.Scatter3d(
        x=[pos[0]], y=[pos[1]], z=[pos[2]],
        mode='text', text=[text],
        textfont=dict(size=size, color=color, family='Arial'),
        showlegend=False, visible=visible, name=name,
    )


def arrow_traces(start, end, color, width=4, cone_size=0.18, opacity=1.0,
                 name='', visible=True, legendgroup=None):
    """Line + cone arrowhead from start to end."""
    d = end - start
    d_norm = d / np.linalg.norm(d)
    traces = []
    # Line
    traces.append(go.Scatter3d(
        x=[start[0], end[0]], y=[start[1], end[1]], z=[start[2], end[2]],
        mode='lines', line=dict(color=color, width=width),
        opacity=opacity, showlegend=False, visible=visible,
        legendgroup=legendgroup,
    ))
    # Cone arrowhead
    traces.append(go.Cone(
        x=[end[0]], y=[end[1]], z=[end[2]],
        u=[d_norm[0]], v=[d_norm[1]], w=[d_norm[2]],
        sizemode='absolute', sizeref=cone_size,
        colorscale=[[0, color], [1, color]],
        showscale=False, opacity=opacity,
        name=name, showlegend=bool(name), visible=visible,
        legendgroup=legendgroup,
    ))
    return traces


# ============================================================
# GEOMETRY: Stella Octangula in +/-1 coordinates
# ============================================================

# T+ vertices: quarks + W (Cartan)
V_W = np.array([1, 1, 1], dtype=float)
V_R = np.array([1, -1, -1], dtype=float)
V_G = np.array([-1, 1, -1], dtype=float)
V_B = np.array([-1, -1, 1], dtype=float)

# T- vertices: antiquarks + Wbar (Cartan)
V_Wb = np.array([-1, -1, -1], dtype=float)
V_Rb = np.array([-1, 1, 1], dtype=float)
V_Gb = np.array([1, -1, 1], dtype=float)
V_Bb = np.array([1, 1, -1], dtype=float)

T_plus = np.array([V_W, V_R, V_G, V_B])
T_minus = np.array([V_Wb, V_Rb, V_Gb, V_Bb])

TET_EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

# Central octahedron vertices (face centers of cube [-1,1]^3)
# Ordered as opposite pairs: (x+,x-), (y+,y-), (z+,z-)
OCT_V = np.array([
    [1, 0, 0], [-1, 0, 0],
    [0, 1, 0], [0, -1, 0],
    [0, 0, 1], [0, 0, -1],
], dtype=float)


def adjacent_face_centers(corner):
    """3 face centers of cube [-1,1]^3 adjacent to a given corner."""
    cx, cy, cz = corner
    return np.array([[cx, 0, 0], [0, cy, 0], [0, 0, cz]], dtype=float)


# 8 corner tetrahedra (cube corner + 3 adjacent face centers)
# T+ corner tets
tau_W = np.vstack([V_W, adjacent_face_centers(V_W)])
tau_R = np.vstack([V_R, adjacent_face_centers(V_R)])
tau_G = np.vstack([V_G, adjacent_face_centers(V_G)])
tau_B = np.vstack([V_B, adjacent_face_centers(V_B)])
# T- corner tets
tau_Wb = np.vstack([V_Wb, adjacent_face_centers(V_Wb)])
tau_Rb = np.vstack([V_Rb, adjacent_face_centers(V_Rb)])
tau_Gb = np.vstack([V_Gb, adjacent_face_centers(V_Gb)])
tau_Bb = np.vstack([V_Bb, adjacent_face_centers(V_Bb)])


# ============================================================
# BUILD ALL TRACES
# ============================================================

all_traces = []
trace_groups = {}

# ----------------------------------------------------------------
# SCENE 1: Vertices = Quarks, Faces = Gluons
# ----------------------------------------------------------------
s1 = []

# Stella wireframe
s1.append(wireframe_trace(T_plus, TET_EDGES, color='rgba(80,80,80,0.6)',
                          width=2.5, name='T+ edges', legendgroup='s1_wire'))
s1.append(wireframe_trace(T_minus, TET_EDGES, color='rgba(80,80,80,0.6)',
                          width=2.5, name='T- edges', legendgroup='s1_wire'))

# Quark/antiquark vertex spheres
v_all = np.vstack([V_R, V_G, V_B, V_Rb, V_Gb, V_Bb])
s1.append(go.Scatter3d(
    x=v_all[:, 0], y=v_all[:, 1], z=v_all[:, 2],
    mode='markers',
    marker=dict(size=[14] * 6,
                color=['red', '#00AA00', '#0066FF', 'salmon', 'lightgreen', 'lightblue'],
                line=dict(width=2, color='black')),
    name='Color vertices (quarks)', showlegend=True, legendgroup='s1_quarks',
))

# W / Wbar vertex spheres (white with black outline)
v_w = np.vstack([V_W, V_Wb])
s1.append(go.Scatter3d(
    x=v_w[:, 0], y=v_w[:, 1], z=v_w[:, 2],
    mode='markers',
    marker=dict(size=[12, 12], color='white',
                line=dict(width=2, color='black')),
    name='W / W-bar (Cartan)', showlegend=True, legendgroup='s1_cartan',
))

# Vertex labels
labels = [
    (V_R, 'R', 'red'), (V_G, 'G', '#006600'), (V_B, 'B', '#0044CC'),
    (V_Rb, 'R-bar', '#CC6666'), (V_Gb, 'G-bar', '#44AA44'), (V_Bb, 'B-bar', '#6688CC'),
    (V_W, 'W (Cartan)', '#555'), (V_Wb, 'W-bar (Cartan)', '#555'),
]
for pos, txt, col in labels:
    offset = pos * 1.15  # push label outward
    s1.append(text_trace(offset, txt, color=col, size=11))

# 6 charged gluon faces (orange)
charged_faces = [
    (np.array([V_G, V_B, V_W]), 'F1+ (opp R): E_{a2}'),
    (np.array([V_R, V_B, V_W]), 'F2+ (opp G): E_{-(a1+a2)}'),
    (np.array([V_R, V_G, V_W]), 'F3+ (opp B): E_{a1}'),
    (np.array([V_Gb, V_Bb, V_Wb]), 'F1- (opp R-bar): E_{-a2}'),
    (np.array([V_Rb, V_Bb, V_Wb]), 'F2- (opp G-bar): E_{a1+a2}'),
    (np.array([V_Rb, V_Gb, V_Wb]), 'F3- (opp B-bar): E_{-a1}'),
]
for i, (fv, fn) in enumerate(charged_faces):
    s1.append(face_mesh(fv, 'rgba(255,160,50,0.30)', opacity=0.30, name=fn if i == 0 else '',
                        legendgroup='s1_charged', showlegend=(i == 0)))

# Label one charged face set
s1.append(text_trace(np.array([V_G, V_B, V_W]).mean(0) * 0.9,
                     '6 charged gluon faces', color='#CC6600', size=9))

# 2 neutral gluon faces (yellow-gold)
neutral_faces = [
    (np.array([V_R, V_G, V_B]), 'F4+ (opp W): H1 = T3'),
    (np.array([V_Rb, V_Gb, V_Bb]), 'F4- (opp W-bar): H2 = T8'),
]
for i, (fv, fn) in enumerate(neutral_faces):
    s1.append(face_mesh(fv, 'rgba(255,215,0,0.35)', opacity=0.35, name=fn if i == 0 else '',
                        legendgroup='s1_neutral', showlegend=(i == 0)))

# Label neutral faces
for fv, fn in neutral_faces:
    c = fv.mean(axis=0)
    short = fn.split(': ')[1] if ': ' in fn else fn
    s1.append(text_trace(c * 0.8, short, color='#8B6914', size=9))

trace_groups['scene1'] = list(range(len(all_traces), len(all_traces) + len(s1)))
all_traces += s1

# ----------------------------------------------------------------
# SCENE 2: Quark -> Gluon Radiation (opposite-vertex rule)
# ----------------------------------------------------------------
s2 = []

# T+ wireframe (bold)
s2.append(wireframe_trace(T_plus, TET_EDGES, color='rgba(40,40,40,0.8)',
                          width=3, name='T+', legendgroup='s2_tp'))
# T- wireframe (dim)
s2.append(wireframe_trace(T_minus, TET_EDGES, color='rgba(180,180,180,0.25)',
                          width=1.5, name='T- (context)', legendgroup='s2_tm'))

# Radiation configs: (vertex, opposite_face_verts, color, label, is_primary)
radiations = [
    (V_R, np.array([V_G, V_B, V_W]), 'red',
     'R emits G<->B gluon (E_{a2})', True),
    (V_G, np.array([V_R, V_B, V_W]), '#00AA00',
     'G emits R<->B gluon (E_{-(a1+a2)})', False),
    (V_B, np.array([V_R, V_G, V_W]), '#0066FF',
     'B emits R<->G gluon (E_{a1})', False),
    (V_W, np.array([V_R, V_G, V_B]), 'goldenrod',
     'W emits neutral gluon (H1)', False),
]

for vert, face_v, col, label, primary in radiations:
    centroid = face_v.mean(axis=0)
    opac = 1.0 if primary else 0.4
    sz = 16 if primary else 10
    lw = 5 if primary else 3
    csz = 0.22 if primary else 0.14

    # Vertex sphere
    s2.append(go.Scatter3d(
        x=[vert[0]], y=[vert[1]], z=[vert[2]],
        mode='markers',
        marker=dict(size=sz, color=col, line=dict(width=2, color='black'),
                    opacity=opac),
        showlegend=False, visible=False,
    ))

    # Arrow from vertex through face centroid (extend 40% beyond)
    direction = centroid - vert
    endpoint = centroid + 0.4 * direction
    s2 += arrow_traces(vert, endpoint, col, width=lw, cone_size=csz,
                       opacity=opac, name=label if primary else '',
                       visible=False)

    # Face highlight
    face_opac = 0.35 if primary else 0.15
    s2.append(face_mesh(face_v, col, opacity=face_opac,
                        name='', visible=False, showlegend=False))

    # Label at face centroid
    if primary:
        s2.append(text_trace(centroid + np.array([0, 0, 0.25]),
                             'R emits G<->B gluon', color='red', size=11,
                             visible=False))

# Vertex name labels on T+
for v, n, c in [(V_R, 'v_R', 'red'), (V_G, 'v_G', '#006600'),
                (V_B, 'v_B', '#0044CC'), (V_W, 'v_W', '#666')]:
    s2.append(text_trace(v * 1.18, n, color=c, size=11, visible=False))

trace_groups['scene2'] = list(range(len(all_traces), len(all_traces) + len(s2)))
all_traces += s2

# ----------------------------------------------------------------
# SCENE 3: 8 Corner Tets + 1 Central Octahedron (8+1)
# ----------------------------------------------------------------
s3 = []

# Transparent stella wireframe for context
s3.append(wireframe_trace(T_plus, TET_EDGES, color='rgba(120,120,120,0.3)',
                          width=1.5, name='', visible=False))
s3.append(wireframe_trace(T_minus, TET_EDGES, color='rgba(120,120,120,0.3)',
                          width=1.5, name='', visible=False))

# 6 root corner tets (charged gluons) - color-coded by +/- alpha pairs
root_configs = [
    # +alpha_2 / -alpha_2 pair (red shades)
    (tau_R,  'rgba(230,70,70,0.40)',  '#CC0000', 'tau_R: E_{+a2}'),
    (tau_Rb, 'rgba(255,140,140,0.40)', '#FF6666', 'tau_R-bar: E_{-a2}'),
    # -(alpha1+alpha2) / +(alpha1+alpha2) pair (green shades)
    (tau_G,  'rgba(60,180,60,0.40)',  '#008800', 'tau_G: E_{-(a1+a2)}'),
    (tau_Gb, 'rgba(140,220,140,0.40)', '#66CC66', 'tau_G-bar: E_{a1+a2}'),
    # +alpha_1 / -alpha_1 pair (blue shades)
    (tau_B,  'rgba(70,120,230,0.40)', '#0044CC', 'tau_B: E_{+a1}'),
    (tau_Bb, 'rgba(140,170,255,0.40)', '#6688FF', 'tau_B-bar: E_{-a1}'),
]

for tv, tc, ec, tn in root_configs:
    s3 += tet_traces(tv, color=tc, edge_color=ec, opacity=0.40,
                     edge_width=2, name=tn, visible=False, legendgroup='s3_root')

# 2 Cartan corner tets (neutral gluons) - yellow/gold
cartan_configs = [
    (tau_W,  'rgba(255,200,0,0.45)', '#B8860B', 'tau_W: H1 (T3)'),
    (tau_Wb, 'rgba(255,230,80,0.45)', '#DAA520', 'tau_W-bar: H2 (T8)'),
]

for tv, tc, ec, tn in cartan_configs:
    s3 += tet_traces(tv, color=tc, edge_color=ec, opacity=0.45,
                     edge_width=2, name=tn, visible=False, legendgroup='s3_cartan')

# Central octahedron (true singlet) - green
s3 += oct_traces(OCT_V, color='rgba(0,200,100,0.35)', edge_color='#009050',
                 opacity=0.35, edge_width=3, name='Central oct: Singlet (1)',
                 visible=False, legendgroup='s3_oct')

# Label: 8 corner tets = octet
s3.append(text_trace(np.array([1.5, -1.5, 0]),
                     '8 corner tets = Adjoint (8)', color='#333', size=12,
                     visible=False))
# Label: central oct = singlet
s3.append(text_trace(np.array([0, 0, 0]),
                     '1', color='#006030', size=14, visible=False))

# Cube wireframe for reference
cube_v = np.array([[-1, -1, -1], [1, -1, -1], [1, 1, -1], [-1, 1, -1],
                   [-1, -1, 1], [1, -1, 1], [1, 1, 1], [-1, 1, 1]], dtype=float)
cube_e = [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6),
          (6, 7), (7, 4), (0, 4), (1, 5), (2, 6), (3, 7)]
s3.append(wireframe_trace(cube_v, cube_e, color='rgba(180,180,180,0.25)',
                          width=1, name='', visible=False))

trace_groups['scene3'] = list(range(len(all_traces), len(all_traces) + len(s3)))
all_traces += s3

# ----------------------------------------------------------------
# SCENE 4: The Two Singlets Disambiguated
# ----------------------------------------------------------------
s4 = []

# Transparent stella wireframes
s4.append(wireframe_trace(T_plus, TET_EDGES, color='rgba(100,100,100,0.35)',
                          width=2, name='T+', visible=False, legendgroup='s4_tp'))
s4.append(wireframe_trace(T_minus, TET_EDGES, color='rgba(100,100,100,0.35)',
                          width=2, name='T-', visible=False, legendgroup='s4_tm'))

# W vertex (large, gold, highlighted) -- NOT a singlet
s4.append(go.Scatter3d(
    x=[V_W[0], V_Wb[0]], y=[V_W[1], V_Wb[1]], z=[V_W[2], V_Wb[2]],
    mode='markers',
    marker=dict(size=[18, 18], color='gold',
                line=dict(width=3, color='#8B6914'),
                symbol='diamond'),
    name='W, W-bar: Cartan (part of 8)', showlegend=True, visible=False,
    legendgroup='s4_w',
))

# W vertex glowing ring (emphasis)
theta = np.linspace(0, 2 * np.pi, 40)
for vw, lbl in [(V_W, 'W'), (V_Wb, 'W-bar')]:
    ring_r = 0.15
    # Ring in the plane perpendicular to (1,1,1) direction for V_W
    n = vw / np.linalg.norm(vw)
    # Find two orthogonal vectors in the plane perp to n
    if abs(n[0]) < 0.9:
        u = np.cross(n, [1, 0, 0])
    else:
        u = np.cross(n, [0, 1, 0])
    u = u / np.linalg.norm(u)
    v = np.cross(n, u)
    ring = vw + ring_r * (np.outer(np.cos(theta), u) + np.outer(np.sin(theta), v))
    s4.append(go.Scatter3d(
        x=ring[:, 0], y=ring[:, 1], z=ring[:, 2],
        mode='lines', line=dict(color='gold', width=4),
        showlegend=False, visible=False, legendgroup='s4_w',
    ))

# W labels with explanation
s4.append(text_trace(V_W * 1.35,
                     'W: weight (0,0)', color='#8B6914', size=11, visible=False))
s4.append(text_trace(V_W * 1.35 + np.array([0, 0, -0.3]),
                     'Cartan direction', color='#8B6914', size=10, visible=False))
s4.append(text_trace(V_W * 1.35 + np.array([0, 0, -0.55]),
                     'Part of OCTET (8)', color='#CC0000', size=11, visible=False))

s4.append(text_trace(V_Wb * 1.35,
                     'W-bar: weight (0,0)', color='#8B6914', size=11, visible=False))
s4.append(text_trace(V_Wb * 1.35 + np.array([0, 0, 0.3]),
                     'Neutral gluon H2', color='#8B6914', size=10, visible=False))
s4.append(text_trace(V_Wb * 1.35 + np.array([0, 0, 0.55]),
                     'Part of OCTET (8)', color='#CC0000', size=11, visible=False))

# Central octahedron (highlighted green) -- TRUE singlet
s4 += oct_traces(OCT_V, color='rgba(0,200,100,0.45)', edge_color='#00AA55',
                 opacity=0.45, edge_width=3.5,
                 name='Central oct: TRUE Singlet (1)',
                 visible=False, legendgroup='s4_oct')

# Singlet label at center
s4.append(text_trace(np.array([0, 0, 0]),
                     'TRUE SINGLET', color='#006030', size=13, visible=False))
s4.append(text_trace(np.array([0, 0, -0.3]),
                     'T+ intersection T-', color='#006030', size=10, visible=False))
s4.append(text_trace(np.array([0, 0, -0.55]),
                     'All colors cancel: P(1+w+w^2)=0', color='#006030', size=10,
                     visible=False))

# Cartan corner tets (faint, to show they're part of octet not singlet)
for tv, tc, ec, tn in cartan_configs:
    s4 += tet_traces(tv, color=tc.replace('0.45', '0.15'), edge_color='rgba(184,134,11,0.3)',
                     opacity=0.15, edge_width=1.5, name='', visible=False,
                     legendgroup='s4_cartan_tet')

# Color vertices for spatial context
s4.append(go.Scatter3d(
    x=[V_R[0], V_G[0], V_B[0], V_Rb[0], V_Gb[0], V_Bb[0]],
    y=[V_R[1], V_G[1], V_B[1], V_Rb[1], V_Gb[1], V_Bb[1]],
    z=[V_R[2], V_G[2], V_B[2], V_Rb[2], V_Gb[2], V_Bb[2]],
    mode='markers',
    marker=dict(size=8,
                color=['red', '#00AA00', '#0066FF', 'salmon', 'lightgreen', 'lightblue'],
                line=dict(width=1, color='black'), opacity=0.5),
    name='Color vertices', showlegend=True, visible=False, legendgroup='s4_cv',
))

# "NOT EQUAL" visual connector between W and center
mid_w_center = V_W * 0.5
s4.append(text_trace(mid_w_center + np.array([0.15, 0.15, 0]),
                     '=/=', color='#CC0000', size=16, visible=False))

# Cube wireframe
s4.append(wireframe_trace(cube_v, cube_e, color='rgba(180,180,180,0.2)',
                          width=1, name='', visible=False))

trace_groups['scene4'] = list(range(len(all_traces), len(all_traces) + len(s4)))
all_traces += s4


# ============================================================
# FIGURE LAYOUT WITH TOGGLE BUTTONS
# ============================================================

n_traces = len(all_traces)


def visibility(groups):
    vis = [False] * n_traces
    for g in groups:
        for idx in trace_groups[g]:
            vis[idx] = True
    return vis


scene_config = {
    'scene1': {
        'text': ("Prop 0.0.39 Scene 1: <b>Vertex-Face Duality</b><br>"
                 "8 vertices = quarks/antiquarks (3 + 3-bar + 2 Cartan)<br>"
                 "8 faces = gluon generators (6 charged + 2 neutral)"),
        'range': [-1.7, 1.7],
    },
    'scene2': {
        'text': ("Prop 0.0.39 Scene 2: <b>Quark -> Gluon Radiation</b><br>"
                 "Each vertex radiates through its opposite face (\"opposite-vertex rule\")<br>"
                 "v_R -> face {G,B,W} carrying E_{a2}: the G<->B transition gluon"),
        'range': [-1.7, 1.7],
    },
    'scene3': {
        'text': ("Prop 0.0.39 Scene 3: <b>8 Corner Tets + 1 Central Octahedron</b><br>"
                 "3 x 3-bar = 8 + 1 : 6 root tets (charged gluons) + 2 Cartan tets (neutral gluons) + 1 singlet oct"),
        'range': [-1.7, 1.7],
    },
    'scene4': {
        'text': ("Prop 0.0.39 Scene 4: <b>Two \"Singlets\" Disambiguated</b><br>"
                 "W vertex: weight (0,0) but part of adjoint OCTET (neutral gluon direction)<br>"
                 "Central octahedron: TRUE singlet (1) where all color fields cancel"),
        'range': [-1.7, 1.7],
    },
}


def make_layout_update(key):
    cfg = scene_config[key]
    r = cfg['range']
    return {
        "annotations": [dict(
            text=cfg['text'],
            xref="paper", yref="paper",
            x=0.5, y=0.01, showarrow=False,
            font=dict(size=11, color='#444'),
            bgcolor='rgba(255,255,255,0.85)',
            bordercolor='rgba(200,200,200,0.5)',
            borderwidth=1,
            align='center',
        )],
        "scene.xaxis.range": r,
        "scene.yaxis.range": r,
        "scene.zaxis.range": r,
    }


fig = go.Figure(data=all_traces)

fig.update_layout(
    title=dict(
        text=("Prop 0.0.39: Stella Octangula Adjoint Decomposition"
              "<br><sup>3 x 3-bar = 8 + 1 : polyhedral decomposition <-> SU(3) representation</sup>"),
        x=0.5,
        font=dict(size=16),
    ),
    updatemenus=[dict(
        type="buttons",
        direction="right",
        x=0.5, xanchor="center",
        y=1.02, yanchor="bottom",
        bgcolor='rgba(240,240,240,0.95)',
        buttons=[
            dict(label="1: Vertex-Face Duality",
                 method="update",
                 args=[{"visible": visibility(['scene1'])},
                       make_layout_update('scene1')]),
            dict(label="2: Quark Radiation",
                 method="update",
                 args=[{"visible": visibility(['scene2'])},
                       make_layout_update('scene2')]),
            dict(label="3: 8+1 Decomposition",
                 method="update",
                 args=[{"visible": visibility(['scene3'])},
                       make_layout_update('scene3')]),
            dict(label="4: Two Singlets",
                 method="update",
                 args=[{"visible": visibility(['scene4'])},
                       make_layout_update('scene4')]),
        ],
    )],
    annotations=make_layout_update('scene1')['annotations'],
    scene=dict(
        xaxis=dict(title='', range=[-1.7, 1.7], showticklabels=False,
                   showgrid=False, zeroline=False,
                   backgroundcolor='white'),
        yaxis=dict(title='', range=[-1.7, 1.7], showticklabels=False,
                   showgrid=False, zeroline=False,
                   backgroundcolor='white'),
        zaxis=dict(title='', range=[-1.7, 1.7], showticklabels=False,
                   showgrid=False, zeroline=False,
                   backgroundcolor='white'),
        aspectmode='cube',
        camera=dict(eye=dict(x=1.6, y=1.6, z=1.1)),
        bgcolor='white',
    ),
    width=1050, height=780,
    legend=dict(x=0.01, y=0.99, bgcolor='rgba(255,255,255,0.85)',
                bordercolor='rgba(200,200,200,0.5)', borderwidth=1),
    margin=dict(t=100, b=80),
    paper_bgcolor='white',
)

# Save
output_path = "verification/plots/prop_0_0_39_adjoint_decomposition.html"
fig.write_html(output_path, include_plotlyjs=True)
print(f"Saved interactive visualization to {output_path}")
print(f"  Scene 1 (Vertex-Face Duality): {len(trace_groups['scene1'])} traces")
print(f"  Scene 2 (Quark Radiation):     {len(trace_groups['scene2'])} traces")
print(f"  Scene 3 (8+1 Decomposition):   {len(trace_groups['scene3'])} traces")
print(f"  Scene 4 (Two Singlets):        {len(trace_groups['scene4'])} traces")
print(f"  Total: {n_traces} traces")

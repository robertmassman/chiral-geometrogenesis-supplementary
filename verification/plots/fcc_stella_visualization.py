#!/usr/bin/env python3
"""
FCC Lattice, Stella Octangula & Tetrahedral-Octahedral Honeycomb
================================================================
Interactive 3D Plotly visualization showing:
  1. Stella Octangula (two interpenetrating tetrahedra)
  2. Decomposition: how the stella breaks into 8 small tets + 1 octahedron
  3. Stella Pair: how 2 adjacent stellae interlock at cube boundaries
  4. Stella Grid: 2x2x2 lattice showing full 3D interlocking pattern
  5. Full FCC honeycomb (2x2x2 conventional cells)

Output: verification/plots/fcc_stella_visualization.html
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


def combine_tet_meshes(tet_list, color, edge_color, opacity=0.25,
                       edge_width=1.5, name='', visible=True, legendgroup=None):
    """Combine many tetrahedra into one Mesh3d + one wireframe trace."""
    if not tet_list:
        return []
    all_v, all_i, all_j, all_k = [], [], [], []
    wx, wy, wz = [], [], []
    offset = 0
    tet_faces = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
    tet_edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    for verts in tet_list:
        v = np.array(verts, dtype=float)
        all_v.append(v)
        for fi, fj, fk in tet_faces:
            all_i.append(fi + offset)
            all_j.append(fj + offset)
            all_k.append(fk + offset)
        for a, b in tet_edges:
            wx += [v[a, 0], v[b, 0], None]
            wy += [v[a, 1], v[b, 1], None]
            wz += [v[a, 2], v[b, 2], None]
        offset += 4
    all_v = np.vstack(all_v)
    mesh = go.Mesh3d(
        x=all_v[:, 0], y=all_v[:, 1], z=all_v[:, 2],
        i=all_i, j=all_j, k=all_k,
        color=color, opacity=opacity,
        name=name, visible=visible, showlegend=True,
        flatshading=True, legendgroup=legendgroup,
    )
    wire = go.Scatter3d(
        x=wx, y=wy, z=wz, mode='lines',
        line=dict(color=edge_color, width=edge_width),
        name='', visible=visible, showlegend=False, legendgroup=legendgroup,
    )
    return [mesh, wire]


def combine_oct_meshes(oct_list, color, edge_color, opacity=0.25,
                       edge_width=1.5, name='', visible=True, legendgroup=None):
    """Combine many octahedra into one Mesh3d + one wireframe trace.
    Each oct: 6 vertices with opposite pairs (0,1), (2,3), (4,5)."""
    if not oct_list:
        return []
    all_v, all_i, all_j, all_k = [], [], [], []
    wx, wy, wz = [], [], []
    opp = {(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 4)}
    offset = 0
    for verts in oct_list:
        v = np.array(verts, dtype=float)
        all_v.append(v)
        # 8 triangular faces: one vertex from each opposite pair
        for a in [0, 1]:
            for b in [2, 3]:
                for c in [4, 5]:
                    all_i.append(a + offset)
                    all_j.append(b + offset)
                    all_k.append(c + offset)
        # 12 edges (all non-opposite pairs)
        for ii in range(6):
            for jj in range(ii + 1, 6):
                if (ii, jj) not in opp:
                    wx += [v[ii, 0], v[jj, 0], None]
                    wy += [v[ii, 1], v[jj, 1], None]
                    wz += [v[ii, 2], v[jj, 2], None]
        offset += 6
    all_v = np.vstack(all_v)
    mesh = go.Mesh3d(
        x=all_v[:, 0], y=all_v[:, 1], z=all_v[:, 2],
        i=all_i, j=all_j, k=all_k,
        color=color, opacity=opacity,
        name=name, visible=visible, showlegend=True,
        flatshading=True, legendgroup=legendgroup,
    )
    wire = go.Scatter3d(
        x=wx, y=wy, z=wz, mode='lines',
        line=dict(color=edge_color, width=edge_width),
        name='', visible=visible, showlegend=False, legendgroup=legendgroup,
    )
    return [mesh, wire]


# ============================================================
# GEOMETRY GENERATORS
# ============================================================

a = 1.0  # Conventional FCC cube side


def corner_tet(cx, cy, cz, dx, dy, dz):
    """4 vertices of the small tet at corner (cx+dx, cy+dy, cz+dz) of cube (cx,cy,cz).
    Each cube has 8 such tets (one per corner)."""
    return np.array([
        [cx + dx * a, cy + dy * a, cz + dz * a],       # corner
        [cx + dx * a, cy + 0.5 * a, cz + 0.5 * a],     # face center (yz face)
        [cx + 0.5 * a, cy + dy * a, cz + 0.5 * a],     # face center (xz face)
        [cx + 0.5 * a, cy + 0.5 * a, cz + dz * a],     # face center (xy face)
    ])


def center_oct(cx, cy, cz):
    """6 vertices of the octahedron at center of cube (cx,cy,cz).
    Ordered as 3 opposite pairs: z-pair, y-pair, x-pair."""
    return np.array([
        [cx + 0.5 * a, cy + 0.5 * a, cz],              # z low
        [cx + 0.5 * a, cy + 0.5 * a, cz + a],           # z high
        [cx + 0.5 * a, cy,            cz + 0.5 * a],    # y low
        [cx + 0.5 * a, cy + a,        cz + 0.5 * a],    # y high
        [cx,            cy + 0.5 * a, cz + 0.5 * a],    # x low
        [cx + a,        cy + 0.5 * a, cz + 0.5 * a],    # x high
    ])


def edge_oct_x(i, j, k):
    """Oct on x-edge from (i,j,k) to (i+1,j,k). Poles on the edge, equator on face centers."""
    return np.array([
        [i * a,       j * a,       k * a],
        [(i + 1) * a, j * a,       k * a],
        [(i + 0.5) * a, (j + 0.5) * a, k * a],
        [(i + 0.5) * a, (j - 0.5) * a, k * a],
        [(i + 0.5) * a, j * a, (k + 0.5) * a],
        [(i + 0.5) * a, j * a, (k - 0.5) * a],
    ])


def edge_oct_y(i, j, k):
    """Oct on y-edge from (i,j,k) to (i,j+1,k)."""
    return np.array([
        [i * a, j * a,       k * a],
        [i * a, (j + 1) * a, k * a],
        [(i + 0.5) * a, (j + 0.5) * a, k * a],
        [(i - 0.5) * a, (j + 0.5) * a, k * a],
        [i * a, (j + 0.5) * a, (k + 0.5) * a],
        [i * a, (j + 0.5) * a, (k - 0.5) * a],
    ])


def edge_oct_z(i, j, k):
    """Oct on z-edge from (i,j,k) to (i,j,k+1)."""
    return np.array([
        [i * a, j * a, k * a],
        [i * a, j * a, (k + 1) * a],
        [(i + 0.5) * a, j * a, (k + 0.5) * a],
        [(i - 0.5) * a, j * a, (k + 0.5) * a],
        [i * a, (j + 0.5) * a, (k + 0.5) * a],
        [i * a, (j - 0.5) * a, (k + 0.5) * a],
    ])


def fcc_lattice_points(n=2):
    """Generate FCC lattice points for n conventional cells in each direction."""
    pts = set()
    for i in range(n + 1):
        for j in range(n + 1):
            for k in range(n + 1):
                pts.add((i * a, j * a, k * a))
    for i in range(n):
        for j in range(n):
            for k in range(n + 1):
                pts.add(((i + 0.5) * a, (j + 0.5) * a, k * a))
    for i in range(n):
        for j in range(n + 1):
            for k in range(n):
                pts.add(((i + 0.5) * a, j * a, (k + 0.5) * a))
    for i in range(n + 1):
        for j in range(n):
            for k in range(n):
                pts.add((i * a, (j + 0.5) * a, (k + 0.5) * a))
    return np.array(sorted(pts))


# ============================================================
# BUILD ALL TRACES
# ============================================================

all_traces = []
trace_groups = {}  # group_name -> list of trace indices

# ---- SCENE 1: Stella Octangula ----
T_plus = np.array([[0, 0, 0], [a, a, 0], [a, 0, a], [0, a, a]])
T_minus = np.array([[a, 0, 0], [0, a, 0], [0, 0, a], [a, a, a]])

stella_traces = []
stella_traces += tet_traces(T_plus, color='rgba(100,181,246,0.45)', edge_color='#1565C0',
                            edge_width=2.5, name='T\u208A (tetrahedron 1)',
                            legendgroup='Tplus')
stella_traces += tet_traces(T_minus, color='rgba(206,147,216,0.45)', edge_color='#7B1FA2',
                            edge_width=2.5, name='T\u208B (tetrahedron 2)',
                            legendgroup='Tminus')

# Enclosing cube wireframe
cube_v = np.array([[0, 0, 0], [1, 0, 0], [1, 1, 0], [0, 1, 0],
                   [0, 0, 1], [1, 0, 1], [1, 1, 1], [0, 1, 1]], dtype=float) * a
cube_e = [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6),
          (6, 7), (7, 4), (0, 4), (1, 5), (2, 6), (3, 7)]
stella_traces.append(wireframe_trace(cube_v, cube_e, color='rgba(150,150,150,0.3)',
                                     width=1, name='Enclosing cube'))

# Vertex markers
sv = np.vstack([T_plus, T_minus])
stella_traces.append(go.Scatter3d(
    x=sv[:, 0], y=sv[:, 1], z=sv[:, 2], mode='markers',
    marker=dict(size=4, color=['#1565C0'] * 4 + ['#7B1FA2'] * 4,
                line=dict(width=1, color='black')),
    name='Stella vertices', showlegend=True,
))

trace_groups['stella'] = list(range(len(all_traces), len(all_traces) + len(stella_traces)))
all_traces += stella_traces

# ---- SCENE 2: Decomposition (1 cube → 8 tets + 1 oct) ----
decomp_traces = []

# T+ corner tets (at T+ vertices: even-sum corners)
tplus_tets = [corner_tet(0, 0, 0, dx, dy, dz)
              for dx, dy, dz in [(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)]]
decomp_traces += combine_tet_meshes(tplus_tets, color='rgba(100,181,246,0.45)',
                                    edge_color='#1565C0', opacity=0.45, edge_width=2.5,
                                    name='T\u208A small tets (4)', visible=False,
                                    legendgroup='dtplus')

# T- corner tets (at T- vertices: odd-sum corners)
tminus_tets = [corner_tet(0, 0, 0, dx, dy, dz)
               for dx, dy, dz in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1)]]
decomp_traces += combine_tet_meshes(tminus_tets, color='rgba(206,147,216,0.45)',
                                    edge_color='#7B1FA2', opacity=0.45, edge_width=2.5,
                                    name='T\u208B small tets (4)', visible=False,
                                    legendgroup='dtminus')

# Central octahedron
oct_v = center_oct(0, 0, 0)
decomp_traces += combine_oct_meshes([oct_v], color='rgba(239,83,80,0.45)',
                                    edge_color='#C62828', opacity=0.45, edge_width=2.5,
                                    name='Central octahedron', visible=False,
                                    legendgroup='doct')

# Faint stella outline
decomp_traces += tet_traces(T_plus, color='rgba(255,215,0,0.08)', edge_color='rgba(184,134,11,0.35)',
                            edge_width=2, name='T\u208A outline', visible=False,
                            legendgroup='doutline1')
decomp_traces += tet_traces(T_minus, color='rgba(147,112,219,0.08)', edge_color='rgba(106,13,173,0.35)',
                            edge_width=2, name='T\u208B outline', visible=False,
                            legendgroup='doutline2')

# Cube wireframe
decomp_traces.append(wireframe_trace(cube_v, cube_e, color='rgba(150,150,150,0.3)',
                                     width=1, name='', visible=False))

# Midpoint vertices (face centers)
fc = np.array([
    [0.5, 0.5, 0], [0.5, 0.5, 1], [0.5, 0, 0.5],
    [0.5, 1, 0.5], [0, 0.5, 0.5], [1, 0.5, 0.5],
]) * a
all_pts = np.vstack([sv, fc])
decomp_traces.append(go.Scatter3d(
    x=all_pts[:, 0], y=all_pts[:, 1], z=all_pts[:, 2], mode='markers',
    marker=dict(size=4, color=['#B8860B'] * 4 + ['#6A0DAD'] * 4 + ['#C62828'] * 6,
                line=dict(width=1, color='black')),
    name='Vertices', visible=False, showlegend=True,
))

trace_groups['decomp'] = list(range(len(all_traces), len(all_traces) + len(decomp_traces)))
all_traces += decomp_traces

# ---- SCENE 3: Neighbors (center stella + 4 adjacent stellae) ----
pair_traces = []

# Center stella at cube (1,1,1)
center_tp = np.array([[1, 1, 1], [2, 2, 1], [2, 1, 2], [1, 2, 2]], dtype=float) * a
center_tm = np.array([[2, 1, 1], [1, 2, 1], [1, 1, 2], [2, 2, 2]], dtype=float) * a

pair_traces += tet_traces(center_tp, color='rgba(100,181,246,0.45)', edge_color='#1565C0',
                          edge_width=2.5, name='Center T\u208A',
                          visible=False, legendgroup='pCTp')
pair_traces += tet_traces(center_tm, color='rgba(206,147,216,0.45)', edge_color='#7B1FA2',
                          edge_width=2.5, name='Center T\u208B',
                          visible=False, legendgroup='pCTm')

# 4 neighbor stellae: right(+x), left(-x), back(-y), bottom(-z)
# Front(+y) and top(+z) left open for viewing into the structure
neighbor_cubes = [(0, 1, 1), (1, 0, 1), (1, 1, 0)]
nbr_tplus = []
nbr_tminus = []
for ncx, ncy, ncz in neighbor_cubes:
    nbr_tplus.append(np.array([
        [ncx, ncy, ncz], [ncx + 1, ncy + 1, ncz],
        [ncx + 1, ncy, ncz + 1], [ncx, ncy + 1, ncz + 1],
    ], dtype=float) * a)
    nbr_tminus.append(np.array([
        [ncx + 1, ncy, ncz], [ncx, ncy + 1, ncz],
        [ncx, ncy, ncz + 1], [ncx + 1, ncy + 1, ncz + 1],
    ], dtype=float) * a)

pair_traces += combine_tet_meshes(nbr_tplus, color='rgba(100,181,246,0.35)',
                                  edge_color='rgba(21,101,192,0.7)', opacity=0.35,
                                  edge_width=2.5, name='Neighbor T\u208A (4)',
                                  visible=False, legendgroup='pNTp')
pair_traces += combine_tet_meshes(nbr_tminus, color='rgba(206,147,216,0.35)',
                                  edge_color='rgba(123,31,162,0.7)', opacity=0.35,
                                  edge_width=2.5, name='Neighbor T\u208B (4)',
                                  visible=False, legendgroup='pNTm')

# Center cube wireframe (bold)
center_cube_v = np.array([[1, 1, 1], [2, 1, 1], [2, 2, 1], [1, 2, 1],
                           [1, 1, 2], [2, 1, 2], [2, 2, 2], [1, 2, 2]], dtype=float) * a
pair_traces.append(wireframe_trace(center_cube_v, cube_e, color='rgba(50,50,50,0.8)',
                                   width=2.5, name='Center cube', visible=False))

# Neighbor cube wireframes (light)
for ncx, ncy, ncz in neighbor_cubes:
    nv = np.array([[ncx, ncy, ncz], [ncx+1, ncy, ncz], [ncx+1, ncy+1, ncz], [ncx, ncy+1, ncz],
                   [ncx, ncy, ncz+1], [ncx+1, ncy, ncz+1], [ncx+1, ncy+1, ncz+1],
                   [ncx, ncy+1, ncz+1]], dtype=float) * a
    pair_traces.append(wireframe_trace(nv, cube_e, color='rgba(150,150,150,0.3)',
                                       width=1, name='', visible=False))

# Shared vertices at all 4 interfaces (green diamonds)
shared_set = set()
for ncx, ncy, ncz in neighbor_cubes:
    if ncx != 1:
        fx = min(ncx, 1) + 1
        for j in [1, 2]:
            for k in [1, 2]:
                shared_set.add((fx, j, k))
    elif ncy != 1:
        fy = min(ncy, 1) + 1
        for i in [1, 2]:
            for k in [1, 2]:
                shared_set.add((i, fy, k))
    else:
        fz = min(ncz, 1) + 1
        for i in [1, 2]:
            for j in [1, 2]:
                shared_set.add((i, j, fz))
shared_verts = np.array(sorted(shared_set), dtype=float) * a
pair_traces.append(go.Scatter3d(
    x=shared_verts[:, 0], y=shared_verts[:, 1], z=shared_verts[:, 2],
    mode='markers',
    marker=dict(size=8, color='#00E676', symbol='diamond',
                line=dict(width=2, color='black')),
    name=f'Shared vertices ({len(shared_verts)})', visible=False, showlegend=True,
))

# Edge octs on the 4 shared faces (unique set)
eoct_specs = set()
for ncx, ncy, ncz in neighbor_cubes:
    if ncx != 1:
        fx = min(ncx, 1) + 1
        eoct_specs.update([('y', fx, 1, 1), ('y', fx, 1, 2),
                           ('z', fx, 1, 1), ('z', fx, 2, 1)])
    elif ncy != 1:
        fy = min(ncy, 1) + 1
        eoct_specs.update([('x', 1, fy, 1), ('x', 1, fy, 2),
                           ('z', 1, fy, 1), ('z', 2, fy, 1)])
    else:
        fz = min(ncz, 1) + 1
        eoct_specs.update([('x', 1, 1, fz), ('x', 1, 2, fz),
                           ('y', 1, 1, fz), ('y', 2, 1, fz)])
pair_eocts = []
for axis, i, j, k in eoct_specs:
    if axis == 'x':
        pair_eocts.append(edge_oct_x(i, j, k))
    elif axis == 'y':
        pair_eocts.append(edge_oct_y(i, j, k))
    else:
        pair_eocts.append(edge_oct_z(i, j, k))

pair_traces += combine_oct_meshes(pair_eocts, color='rgba(255,167,38,0.20)',
                                  edge_color='rgba(0,0,0,0)', opacity=0.20,
                                  edge_width=2.5,
                                  name=f'Edge octahedra ({len(pair_eocts)})',
                                  visible=False, legendgroup='pair_eocts')

trace_groups['pair'] = list(range(len(all_traces), len(all_traces) + len(pair_traces)))
all_traces += pair_traces

# ---- SCENE 4: Stella Grid (3x3x3 with center stella highlighted) ----
grid_traces = []
ng = 3  # 3x3x3 grid

# Separate center cube (1,1,1) from surrounding 26 cubes
center_tplus = []
center_tminus = []
surr_tplus = []
surr_tminus = []
for cx in range(ng):
    for cy in range(ng):
        for cz in range(ng):
            tp = np.array([
                [cx, cy, cz], [cx + 1, cy + 1, cz],
                [cx + 1, cy, cz + 1], [cx, cy + 1, cz + 1],
            ], dtype=float) * a
            tm = np.array([
                [cx + 1, cy, cz], [cx, cy + 1, cz],
                [cx, cy, cz + 1], [cx + 1, cy + 1, cz + 1],
            ], dtype=float) * a
            if cx == 1 and cy == 1 and cz == 1:
                center_tplus.append(tp)
                center_tminus.append(tm)
            else:
                surr_tplus.append(tp)
                surr_tminus.append(tm)

# Center stella at full opacity
grid_traces += combine_tet_meshes(center_tplus, color='rgba(100,181,246,0.45)',
                                  edge_color='#1565C0', opacity=0.45,
                                  edge_width=2.5, name='Center T\u208A',
                                  visible=False, legendgroup='grid_ctp')
grid_traces += combine_tet_meshes(center_tminus, color='rgba(206,147,216,0.45)',
                                  edge_color='#7B1FA2', opacity=0.45,
                                  edge_width=2.5, name='Center T\u208B',
                                  visible=False, legendgroup='grid_ctm')

# Surrounding 26 stellae at lower opacity
grid_traces += combine_tet_meshes(surr_tplus, color='rgba(100,181,246,0.18)',
                                  edge_color='rgba(21,101,192,0.35)', opacity=0.18,
                                  edge_width=1.5, name='T\u208A surround (26)',
                                  visible=False, legendgroup='grid_stp')
grid_traces += combine_tet_meshes(surr_tminus, color='rgba(206,147,216,0.18)',
                                  edge_color='rgba(123,31,162,0.35)', opacity=0.18,
                                  edge_width=1.5, name='T\u208B surround (26)',
                                  visible=False, legendgroup='grid_stm')

# Edge octs for 3x3x3 grid
grid_edge_octs = []
for i in range(ng):
    for j in range(ng + 1):
        for k in range(ng + 1):
            v = edge_oct_x(i, j, k)
            if np.all(v >= -0.5 * a) and np.all(v <= (ng + 0.5) * a):
                grid_edge_octs.append(v)
for i in range(ng + 1):
    for j in range(ng):
        for k in range(ng + 1):
            v = edge_oct_y(i, j, k)
            if np.all(v >= -0.5 * a) and np.all(v <= (ng + 0.5) * a):
                grid_edge_octs.append(v)
for i in range(ng + 1):
    for j in range(ng + 1):
        for k in range(ng):
            v = edge_oct_z(i, j, k)
            if np.all(v >= -0.5 * a) and np.all(v <= (ng + 0.5) * a):
                grid_edge_octs.append(v)

grid_traces += combine_oct_meshes(grid_edge_octs, color='rgba(255,167,38,0.20)',
                                  edge_color='rgba(0,0,0,0)', opacity=0.20,
                                  edge_width=2.5,
                                  name=f'Edge octahedra ({len(grid_edge_octs)})',
                                  visible=False, legendgroup='grid_eocts')

# 3x3x3 cube grid wireframe
gwx, gwy, gwz = [], [], []
for i in range(ng + 1):
    for j in range(ng + 1):
        for k in range(ng + 1):
            if i < ng:
                gwx += [i * a, (i + 1) * a, None]
                gwy += [j * a, j * a, None]
                gwz += [k * a, k * a, None]
            if j < ng:
                gwx += [i * a, i * a, None]
                gwy += [j * a, (j + 1) * a, None]
                gwz += [k * a, k * a, None]
            if k < ng:
                gwx += [i * a, i * a, None]
                gwy += [j * a, j * a, None]
                gwz += [k * a, (k + 1) * a, None]

grid_traces.append(go.Scatter3d(
    x=gwx, y=gwy, z=gwz, mode='lines',
    line=dict(color='rgba(150,150,150,0.3)', width=1),
    name='Cube grid', visible=False, showlegend=True,
))

# Highlighted center cube wireframe
cc = np.array([[1, 1, 1], [2, 1, 1], [2, 2, 1], [1, 2, 1],
               [1, 1, 2], [2, 1, 2], [2, 2, 2], [1, 2, 2]], dtype=float) * a
grid_traces.append(wireframe_trace(cc, cube_e, color='rgba(50,50,50,0.8)',
                                   width=2.5, name='Center cube', visible=False))

# All 64 cube-corner vertices
grid_verts = np.array([[i * a, j * a, k * a]
                        for i in range(ng + 1) for j in range(ng + 1)
                        for k in range(ng + 1)])
grid_traces.append(go.Scatter3d(
    x=grid_verts[:, 0], y=grid_verts[:, 1], z=grid_verts[:, 2],
    mode='markers',
    marker=dict(size=3, color='#00E676', line=dict(width=0.5, color='black')),
    name=f'Cube vertices ({len(grid_verts)})', visible=False, showlegend=True,
))

trace_groups['grid'] = list(range(len(all_traces), len(all_traces) + len(grid_traces)))
all_traces += grid_traces

# ---- SCENE 5: Full FCC Honeycomb (3x3x3 with center highlighted) ----
fcc_traces = []
nf = 3  # 3x3x3 to match grid scene

# Separate center cube (1,1,1) decomposition from surrounding cubes
center_tplus_tets = [corner_tet(1, 1, 1, dx, dy, dz)
                     for dx, dy, dz in [(0, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)]]
center_tminus_tets = [corner_tet(1, 1, 1, dx, dy, dz)
                      for dx, dy, dz in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1)]]
center_coct = [center_oct(1, 1, 1)]

surr_tets = []
surr_cocts = []
for cx in range(nf):
    for cy in range(nf):
        for cz in range(nf):
            if cx == 1 and cy == 1 and cz == 1:
                continue
            for dx in range(2):
                for dy in range(2):
                    for dz in range(2):
                        surr_tets.append(corner_tet(cx, cy, cz, dx, dy, dz))
            surr_cocts.append(center_oct(cx, cy, cz))

# Center cube: T+ corner tets at full opacity
fcc_traces += combine_tet_meshes(center_tplus_tets, color='rgba(100,181,246,0.45)',
                                 edge_color='#1565C0', opacity=0.45,
                                 edge_width=2.5, name='Center T\u208A tets (4)',
                                 visible=False, legendgroup='fcc_ctp')

# Center cube: T- corner tets at full opacity
fcc_traces += combine_tet_meshes(center_tminus_tets, color='rgba(206,147,216,0.45)',
                                 edge_color='#7B1FA2', opacity=0.45,
                                 edge_width=2.5, name='Center T\u208B tets (4)',
                                 visible=False, legendgroup='fcc_ctm')

# Center cube: central octahedron at full opacity
fcc_traces += combine_oct_meshes(center_coct, color='rgba(239,83,80,0.45)',
                                 edge_color='#C62828', opacity=0.45,
                                 edge_width=2.5, name='Center octahedron',
                                 visible=False, legendgroup='fcc_coct')

# Surrounding 26 cubes: corner tets at low opacity
fcc_traces += combine_tet_meshes(surr_tets, color='rgba(100,181,246,0.12)',
                                 edge_color='rgba(21,101,192,0.25)', opacity=0.12,
                                 edge_width=1, name=f'Surround tets ({len(surr_tets)})',
                                 visible=False, legendgroup='fcc_stets')

# Surrounding 26 cubes: center octs at low opacity
fcc_traces += combine_oct_meshes(surr_cocts, color='rgba(239,83,80,0.12)',
                                 edge_color='rgba(198,40,40,0.25)', opacity=0.12,
                                 edge_width=1, name=f'Surround octs ({len(surr_cocts)})',
                                 visible=False, legendgroup='fcc_socts')

# All edge octahedra for 3x3x3 grid
all_edge_octs = []
for i in range(nf):
    for j in range(nf + 1):
        for k in range(nf + 1):
            v = edge_oct_x(i, j, k)
            if np.all(v >= -0.5 * a) and np.all(v <= (nf + 0.5) * a):
                all_edge_octs.append(v)
for i in range(nf + 1):
    for j in range(nf):
        for k in range(nf + 1):
            v = edge_oct_y(i, j, k)
            if np.all(v >= -0.5 * a) and np.all(v <= (nf + 0.5) * a):
                all_edge_octs.append(v)
for i in range(nf + 1):
    for j in range(nf + 1):
        for k in range(nf):
            v = edge_oct_z(i, j, k)
            if np.all(v >= -0.5 * a) and np.all(v <= (nf + 0.5) * a):
                all_edge_octs.append(v)

fcc_traces += combine_oct_meshes(all_edge_octs, color='rgba(255,167,38,0.20)',
                                 edge_color='rgba(0,0,0,0)', opacity=0.20,
                                 edge_width=2.5,
                                 name=f'Edge octahedra ({len(all_edge_octs)})',
                                 visible=False, legendgroup='fcc_eocts')

# Highlighted center cube wireframe
fcc_cc = np.array([[1, 1, 1], [2, 1, 1], [2, 2, 1], [1, 2, 1],
                    [1, 1, 2], [2, 1, 2], [2, 2, 2], [1, 2, 2]], dtype=float) * a
fcc_traces.append(wireframe_trace(fcc_cc, cube_e, color='rgba(50,50,50,0.8)',
                                  width=2.5, name='Center cube', visible=False))

# FCC lattice points
pts = fcc_lattice_points(nf)
fcc_traces.append(go.Scatter3d(
    x=pts[:, 0], y=pts[:, 1], z=pts[:, 2], mode='markers',
    marker=dict(size=2.5, color='#333333'),
    name='FCC lattice points', visible=False, showlegend=True,
))

trace_groups['fcc'] = list(range(len(all_traces), len(all_traces) + len(fcc_traces)))
all_traces += fcc_traces

# ============================================================
# FIGURE WITH TOGGLE BUTTONS
# ============================================================

n_traces = len(all_traces)


def visibility(groups):
    vis = [False] * n_traces
    for g in groups:
        for idx in trace_groups[g]:
            vis[idx] = True
    return vis


# Per-scene configuration: annotation text and axis range
scene_config = {
    'stella': {
        'text': ("The stella octangula: two interpenetrating tetrahedra T\u208A \u222A T\u208B<br>"
                 "inscribed in a cube. 8 vertices, 2 connected components, \u03C7 = 4."),
        'range': [-0.3, 1.3],
    },
    'decomp': {
        'text': ("Each stella decomposes into 8 small tetrahedra + 1 central<br>"
                 "octahedron \u2014 the building blocks of the FCC honeycomb."),
        'range': [-0.3, 1.3],
    },
    'pair': {
        'text': ("Center stella (solid) + 4 neighbors (right, left, back, bottom).<br>"
                 "Green diamonds: shared vertices where T\u208A meets T\u208B across cube faces."),
        'range': [-0.5, 3.5],
    },
    'grid': {
        'text': ("3\u00D73\u00D73 lattice: center stella (solid) surrounded by 26 neighbors.<br>"
                 "T\u208A (blue) and T\u208B (purple) interlock at every face."),
        'range': [-0.5, 3.5],
    },
    'fcc': {
        'text': ("The complete tetrahedral-octahedral honeycomb: center cube decomposed<br>"
                 "into 8 corner tets (blue/purple) + 1 central oct (red) + edge octs (orange)."),
        'range': [-0.5, 3.5],
    },
}


def make_layout_update(key):
    cfg = scene_config[key]
    r = cfg['range']
    return {
        "annotations": [dict(
            text=cfg['text'],
            xref="paper", yref="paper",
            x=0.98, y=0.02, showarrow=False,
            font=dict(size=11, color='#555'),
            bgcolor='rgba(255,255,255,0.7)',
            align='right',
        )],
        "scene.xaxis.range": r,
        "scene.yaxis.range": r,
        "scene.zaxis.range": r,
    }


fig = go.Figure(data=all_traces)

fig.update_layout(
    title=dict(
        text=("Stella Octangula \u2194 FCC Tetrahedral-Octahedral Honeycomb"
              "<br><sup>Chiral Geometrogenesis: from pre-geometric boundary to spatial lattice</sup>"),
        x=0.5,
    ),
    updatemenus=[dict(
        type="buttons",
        direction="right",
        x=0.5, xanchor="center",
        y=1.02, yanchor="bottom",
        bgcolor='rgba(240,240,240,0.9)',
        buttons=[
            dict(label="\u2B50 Stella",
                 method="update",
                 args=[{"visible": visibility(['stella'])},
                       make_layout_update('stella')]),
            dict(label="\U0001F52C Decompose",
                 method="update",
                 args=[{"visible": visibility(['decomp'])},
                       make_layout_update('decomp')]),
            dict(label="\U0001F517 Neighbors",
                 method="update",
                 args=[{"visible": visibility(['pair'])},
                       make_layout_update('pair')]),
            dict(label="\U0001F9CA Stella Grid",
                 method="update",
                 args=[{"visible": visibility(['grid'])},
                       make_layout_update('grid')]),
            dict(label="\U0001F30D FCC Honeycomb",
                 method="update",
                 args=[{"visible": visibility(['fcc'])},
                       make_layout_update('fcc')]),
        ],
    )],
    annotations=make_layout_update('stella')['annotations'],
    scene=dict(
        xaxis=dict(title='x', range=[-0.3, 1.3],
                   backgroundcolor='rgba(245,245,245,0.8)'),
        yaxis=dict(title='y', range=[-0.3, 1.3],
                   backgroundcolor='rgba(245,245,245,0.8)'),
        zaxis=dict(title='z', range=[-0.3, 1.3],
                   backgroundcolor='rgba(245,245,245,0.8)'),
        aspectmode='cube',
        camera=dict(eye=dict(x=1.8, y=1.8, z=1.2)),
    ),
    width=1000, height=750,
    legend=dict(x=0.01, y=0.99, bgcolor='rgba(255,255,255,0.8)'),
    margin=dict(t=100),
)

# Annotations are now set dynamically by buttons (see scene_annotations above)

# Save
output_path = "verification/plots/fcc_stella_visualization.html"
fig.write_html(output_path, include_plotlyjs=True)
print(f"Saved interactive visualization to {output_path}")
print(f"  Stella: {len(trace_groups['stella'])} traces")
print(f"  Decomposition: {len(trace_groups['decomp'])} traces")
print(f"  Stella Pair: {len(trace_groups['pair'])} traces")
print(f"  Stella Grid: {len(trace_groups['grid'])} traces")
print(f"  FCC Honeycomb: {len(trace_groups['fcc'])} traces")
print(f"  Total: {n_traces} traces")
print(f"  FCC: Center tets: {len(center_tplus_tets)+len(center_tminus_tets)}, "
      f"Surround tets: {len(surr_tets)}, Surround octs: {len(surr_cocts)}, "
      f"Edge octs: {len(all_edge_octs)}")

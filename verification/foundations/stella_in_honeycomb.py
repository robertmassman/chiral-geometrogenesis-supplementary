#!/usr/bin/env python3
"""
Stella Octangula in the Tetrahedral-Octahedral Honeycomb
========================================================

Properly visualizes the stella octangula (two interpenetrating tetrahedra)
as it appears at each vertex of the octet truss.

From Theorem 0.0.6:
    "At each vertex of the honeycomb, 8 tetrahedra meet. These 8 tetrahedra
    partition into two groups of four that form two interpenetrating
    tetrahedra (the stella octangula)."

The stella octangula T₊ ∪ T₋ has:
    - 8 vertices forming a cube
    - T₊: 4 vertices at (±1, ±1, ±1) with EVEN parity (product of signs = +1)
    - T₋: 4 vertices at (±1, ±1, ±1) with ODD parity (product of signs = -1)

At the central vertex V=(0,0,0) of the honeycomb:
    - 8 small tetrahedra of the honeycomb share V
    - The OTHER vertices of these 8 tets (not V) are the 8 vertices of the stella
    - Grouped by orientation → T₊ and T₋

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-03
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Dict
from pathlib import Path
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from dataclasses import dataclass
from itertools import combinations

# ============================================================================
# STELLA OCTANGULA GEOMETRY
# ============================================================================

class StellaOctangulaInHoneycomb:
    """
    The stella octangula as it appears at a vertex of the octet truss.

    Centered at origin, the 8 vertices form a cube with vertices at (±1, ±1, ±1).

    T₊ (even parity - product of coordinate signs = +1):
        (+1, +1, +1), (+1, -1, -1), (-1, +1, -1), (-1, -1, +1)

    T₋ (odd parity - product of coordinate signs = -1):
        (+1, +1, -1), (+1, -1, +1), (-1, +1, +1), (-1, -1, -1)
    """

    def __init__(self, center=np.zeros(3), scale=1.0):
        self.center = np.array(center)
        self.scale = scale

        # CORRECTED GEOMETRY:
        # The stella vertices are at the CENTROIDS of the 8 triangular faces
        # of the cuboctahedron (formed by the 12 FCC neighbors).
        # These centroids are at (±2/3, ±2/3, ±2/3) × scale.
        #
        # The 8 triangular faces correspond to the 8 honeycomb tets meeting at V.
        # The centroid of each triangular face is the "center" of that tet.

        # T₊ vertices (even parity: xyz product = +1)
        # These are centroids of the 4 triangular faces pointing into even-parity octants
        self.T_plus_vertices = scale * (2/3) * np.array([
            [+1, +1, +1],  # centroid of face with FCC verts (1,1,0), (1,0,1), (0,1,1)
            [+1, -1, -1],  # centroid of face with FCC verts (1,-1,0), (1,0,-1), (0,-1,-1)
            [-1, +1, -1],  # centroid of face with FCC verts (-1,1,0), (-1,0,-1), (0,1,-1)
            [-1, -1, +1]   # centroid of face with FCC verts (-1,-1,0), (-1,0,1), (0,-1,1)
        ], dtype=float) + center

        # T₋ vertices (odd parity: xyz product = -1)
        # These are centroids of the 4 triangular faces pointing into odd-parity octants
        self.T_minus_vertices = scale * (2/3) * np.array([
            [+1, +1, -1],  # centroid of face with FCC verts (1,1,0), (1,0,-1), (0,1,-1)
            [+1, -1, +1],  # centroid of face with FCC verts (1,-1,0), (1,0,1), (0,-1,1)
            [-1, +1, +1],  # centroid of face with FCC verts (-1,1,0), (-1,0,1), (0,1,1)
            [-1, -1, -1]   # centroid of face with FCC verts (-1,-1,0), (-1,0,-1), (0,-1,-1)
        ], dtype=float) + center

        # All 8 vertices
        self.vertices = np.vstack([self.T_plus_vertices, self.T_minus_vertices])

        # T₊ edges (complete graph K₄ on vertices 0-3)
        self.T_plus_edges = [(i, j) for i in range(4) for j in range(i+1, 4)]

        # T₋ edges (complete graph K₄ on vertices 4-7)
        self.T_minus_edges = [(i+4, j+4) for i in range(4) for j in range(i+1, 4)]

        # All 12 edges
        self.edges = self.T_plus_edges + self.T_minus_edges

        # T₊ faces
        self.T_plus_faces = [(0,1,2), (0,1,3), (0,2,3), (1,2,3)]

        # T₋ faces
        self.T_minus_faces = [(4,5,6), (4,5,7), (4,6,7), (5,6,7)]

        # All 8 faces
        self.faces = self.T_plus_faces + self.T_minus_faces

        # The 12 nearest neighbors in FCC (at distance √2 from center)
        # These are the midpoints of the cube edges
        self.fcc_neighbors = scale * np.array([
            [+1, +1, 0], [+1, -1, 0], [-1, +1, 0], [-1, -1, 0],
            [+1, 0, +1], [+1, 0, -1], [-1, 0, +1], [-1, 0, -1],
            [0, +1, +1], [0, +1, -1], [0, -1, +1], [0, -1, -1]
        ], dtype=float) + center


class TetrahedralOctahedralHoneycomb:
    """
    The tetrahedral-octahedral honeycomb (octet truss) surrounding a stella octangula.

    At the central vertex V=(0,0,0):
    - 8 small tetrahedra of the honeycomb meet (forming the stella)
    - 6 octahedra meet (providing transition regions)

    The 8 honeycomb tetrahedra have:
    - One vertex at V=(0,0,0)
    - Three vertices on the FCC neighbors (at distance √2 from V)

    The FCC neighbors are at positions like (1,1,0), (1,0,1), etc.
    """

    def __init__(self, center=np.zeros(3), scale=1.0):
        self.center = np.array(center)
        self.scale = scale

        # The stella at the center
        self.stella = StellaOctangulaInHoneycomb(center, scale)

        # FCC lattice neighbors (12 points at distance √2)
        # These form the vertices of a cuboctahedron around the center
        self.fcc_neighbors = scale * np.array([
            [+1, +1, 0], [+1, -1, 0], [-1, +1, 0], [-1, -1, 0],
            [+1, 0, +1], [+1, 0, -1], [-1, 0, +1], [-1, 0, -1],
            [0, +1, +1], [0, +1, -1], [0, -1, +1], [0, -1, -1]
        ], dtype=float) + center

        # The 8 honeycomb tetrahedra that meet at V
        # Each connects V to 3 of the FCC neighbors that form a triangle
        # These are the 8 triangular faces of the cuboctahedron
        #
        # FCC neighbor indices:
        # 0:(1,1,0), 1:(1,-1,0), 2:(-1,1,0), 3:(-1,-1,0)
        # 4:(1,0,1), 5:(1,0,-1), 6:(-1,0,1), 7:(-1,0,-1)
        # 8:(0,1,1), 9:(0,1,-1), 10:(0,-1,1), 11:(0,-1,-1)
        #
        # T₊ faces (even parity octants, xyz product = +1):
        self.honeycomb_tet_faces = [
            (0, 4, 8),   # (+1,+1,0), (+1,0,+1), (0,+1,+1) → octant (+,+,+)
            (1, 5, 11),  # (+1,-1,0), (+1,0,-1), (0,-1,-1) → octant (+,-,-)
            (2, 7, 9),   # (-1,+1,0), (-1,0,-1), (0,+1,-1) → octant (-,+,-)
            (3, 6, 10),  # (-1,-1,0), (-1,0,+1), (0,-1,+1) → octant (-,-,+)
            # T₋ faces (odd parity octants, xyz product = -1):
            (0, 5, 9),   # (+1,+1,0), (+1,0,-1), (0,+1,-1) → octant (+,+,-)
            (1, 4, 10),  # (+1,-1,0), (+1,0,+1), (0,-1,+1) → octant (+,-,+)
            (2, 6, 8),   # (-1,+1,0), (-1,0,+1), (0,+1,+1) → octant (-,+,+)
            (3, 7, 11),  # (-1,-1,0), (-1,0,-1), (0,-1,-1) → octant (-,-,-)
        ]

        # Classify into T₊ and T₋ groups (by parity of direction)
        self.T_plus_tets = [0, 1, 2, 3]  # Even parity octants
        self.T_minus_tets = [4, 5, 6, 7]  # Odd parity octants

        # The 6 octahedra that meet at V
        # Each octahedron has 6 vertices: V and 4 FCC neighbors forming a square
        # Plus 1 vertex from the extended lattice (at distance 2 from V)
        # The square faces of the cuboctahedron indicate octahedra
        self.octahedra_squares = [
            # Square faces of cuboctahedron (6 total, one per axis-pair)
            (0, 4, 1, 5),   # +x face: (+1,+1,0), (+1,0,+1), (+1,-1,0), (+1,0,-1)
            (2, 6, 3, 7),   # -x face: (-1,+1,0), (-1,0,+1), (-1,-1,0), (-1,0,-1)
            (0, 8, 2, 9),   # +y face: (+1,+1,0), (0,+1,+1), (-1,+1,0), (0,+1,-1)
            (1, 10, 3, 11), # -y face: (+1,-1,0), (0,-1,+1), (-1,-1,0), (0,-1,-1)
            (4, 8, 6, 10),  # +z face: (+1,0,+1), (0,+1,+1), (-1,0,+1), (0,-1,+1)
            (5, 9, 7, 11),  # -z face: (+1,0,-1), (0,+1,-1), (-1,0,-1), (0,-1,-1)
        ]

        # Extended FCC vertices (the "far" vertices of the octahedra)
        # At distance 2 from center along axes
        self.extended_vertices = scale * np.array([
            [+2, 0, 0], [-2, 0, 0],
            [0, +2, 0], [0, -2, 0],
            [0, 0, +2], [0, 0, -2]
        ], dtype=float) + center

    def get_honeycomb_edges(self):
        """Get all edges of the honeycomb structure around the center."""
        edges = []

        # Edges from center to FCC neighbors
        for i in range(12):
            edges.append(('center', i))

        # Edges between adjacent FCC neighbors (cuboctahedron edges)
        cuboctahedron_edges = [
            # Edges of the 8 triangular faces
            (0, 4), (4, 8), (8, 0),
            (1, 5), (5, 10), (10, 1),
            (2, 6), (6, 9), (9, 2),
            (3, 7), (7, 11), (11, 3),
            (0, 5), (5, 9), (9, 0),
            (1, 4), (4, 10), (10, 1),
            (2, 7), (7, 8), (8, 2),
            (3, 6), (6, 11), (11, 3),
            # Edges of the 6 square faces (shared with triangles, already included)
        ]
        # Remove duplicates
        seen = set()
        for e in cuboctahedron_edges:
            key = tuple(sorted(e))
            if key not in seen:
                edges.append(('fcc', e[0], e[1]))
                seen.add(key)

        # Edges from FCC neighbors to extended vertices (octahedra far edges)
        oct_to_ext = [
            # +x octahedron to (+2,0,0)
            (0, 0), (4, 0), (1, 0), (5, 0),
            # -x octahedron to (-2,0,0)
            (2, 1), (6, 1), (3, 1), (7, 1),
            # +y octahedron to (0,+2,0)
            (0, 2), (8, 2), (2, 2), (9, 2),
            # -y octahedron to (0,-2,0)
            (1, 3), (10, 3), (3, 3), (11, 3),
            # +z octahedron to (0,0,+2)
            (4, 4), (8, 4), (6, 4), (10, 4),
            # -z octahedron to (0,0,-2)
            (5, 5), (9, 5), (7, 5), (11, 5),
        ]
        for fcc_idx, ext_idx in oct_to_ext:
            edges.append(('ext', fcc_idx, ext_idx))

        return edges


# ============================================================================
# SU(2) GAUGE FIELD ON STELLA
# ============================================================================

def quaternion_to_su2(a):
    return np.array([
        [a[0] + 1j*a[3], a[2] + 1j*a[1]],
        [-a[2] + 1j*a[1], a[0] - 1j*a[3]]
    ], dtype=complex)

def su2_random():
    a = np.random.randn(4)
    a /= np.linalg.norm(a)
    return quaternion_to_su2(a)

def su2_near_identity(eps=0.01):
    a = np.array([1.0, eps*np.random.randn(), eps*np.random.randn(), eps*np.random.randn()])
    a /= np.linalg.norm(a)
    return quaternion_to_su2(a)

def su2_exp(H):
    h = np.array([np.imag(H[0,1]+H[1,0])/2, np.real(H[0,1]-H[1,0])/2, np.imag(H[0,0]-H[1,1])/2])
    h_norm = np.linalg.norm(h)
    if h_norm < 1e-10:
        return np.eye(2, dtype=complex) + H
    return np.cos(h_norm)*np.eye(2, dtype=complex) + np.sin(h_norm)/h_norm * H

def su2_project(U):
    u, s, vh = np.linalg.svd(U)
    W = u @ vh
    return W / np.sqrt(np.linalg.det(W))


class StellaGaugeField:
    """SU(2) gauge field on the stella octangula edges."""

    def __init__(self, stella: StellaOctangulaInHoneycomb):
        self.stella = stella
        self.n_edges = 12
        self.links = [np.eye(2, dtype=complex) for _ in range(12)]

    def get_link(self, edge_idx: int) -> np.ndarray:
        return self.links[edge_idx].copy()

    def plaquette_trace(self, face: Tuple[int,int,int]) -> float:
        """Compute (1/2) Re Tr(U_ab U_bc U_ca)."""
        a, b, c = face

        # Find edge indices
        def find_edge(i, j):
            for idx, (p, q) in enumerate(self.stella.edges):
                if (p, q) == (i, j) or (p, q) == (j, i):
                    return idx, (p == i)  # True if same direction
            return None, None

        idx_ab, fwd_ab = find_edge(a, b)
        idx_bc, fwd_bc = find_edge(b, c)
        idx_ca, fwd_ca = find_edge(c, a)

        U_ab = self.links[idx_ab] if fwd_ab else self.links[idx_ab].conj().T
        U_bc = self.links[idx_bc] if fwd_bc else self.links[idx_bc].conj().T
        U_ca = self.links[idx_ca] if fwd_ca else self.links[idx_ca].conj().T

        P = U_ab @ U_bc @ U_ca
        return 0.5 * np.real(np.trace(P))

    def T_plus_plaquette(self) -> float:
        return np.mean([self.plaquette_trace(f) for f in self.stella.T_plus_faces])

    def T_minus_plaquette(self) -> float:
        return np.mean([self.plaquette_trace(f) for f in self.stella.T_minus_faces])

    def average_plaquette(self) -> float:
        return np.mean([self.plaquette_trace(f) for f in self.stella.faces])

    def wilson_action(self, beta: float) -> float:
        return beta * sum(1 - self.plaquette_trace(f) for f in self.stella.faces)

    def edge_plaquettes(self) -> np.ndarray:
        """Average plaquette for faces touching each edge."""
        values = np.zeros(12)
        for e_idx, (i, j) in enumerate(self.stella.edges):
            face_vals = []
            for face in self.stella.faces:
                if i in face and j in face:
                    face_vals.append(self.plaquette_trace(face))
            values[e_idx] = np.mean(face_vals) if face_vals else 0.5
        return values

    def hot_start(self):
        self.links = [su2_random() for _ in range(12)]

    def cold_start(self):
        self.links = [su2_near_identity(0.01) for _ in range(12)]

    def copy(self):
        new = StellaGaugeField(self.stella)
        new.links = [l.copy() for l in self.links]
        return new


# ============================================================================
# HMC
# ============================================================================

@dataclass
class Frame:
    trajectory: int
    avg_plaquette: float
    T_plus_plaq: float
    T_minus_plaq: float
    edge_plaquettes: np.ndarray


class StellaHMC:
    def __init__(self, beta=2.2, n_leapfrog=15, dt=0.08):
        self.stella = StellaOctangulaInHoneycomb()
        self.gauge = StellaGaugeField(self.stella)
        self.beta = beta
        self.n_leapfrog = n_leapfrog
        self.dt = dt
        self.n_accepted = 0
        self.n_total = 0
        self.frames: List[Frame] = []

    def _random_momentum(self):
        a = np.random.randn(3)
        sigma = [np.array([[0,1],[1,0]], dtype=complex),
                 np.array([[0,-1j],[1j,0]], dtype=complex),
                 np.array([[1,0],[0,-1]], dtype=complex)]
        return 1j * sum(a[i]*sigma[i] for i in range(3))

    def _kinetic_energy(self, pi):
        return sum(-0.5 * np.real(np.trace(p @ p)) for p in pi)

    def _force(self, e_idx):
        i, j = self.stella.edges[e_idx]
        U = self.gauge.links[e_idx]

        staple = np.zeros((2,2), dtype=complex)
        for face in self.stella.faces:
            if i in face and j in face:
                k = [v for v in face if v != i and v != j][0]
                # Find links j->k and k->i
                def get_link(a, b):
                    for idx, (p, q) in enumerate(self.stella.edges):
                        if (p, q) == (a, b):
                            return self.gauge.links[idx]
                        elif (p, q) == (b, a):
                            return self.gauge.links[idx].conj().T
                    return np.eye(2, dtype=complex)

                staple += get_link(j, k) @ get_link(k, i)

        X = (self.beta / 2) * U @ staple
        F = 0.5 * (X - X.conj().T)
        F = F - np.trace(F)/2 * np.eye(2)
        return F

    def _leapfrog(self, pi):
        for _ in range(self.n_leapfrog):
            for e in range(12):
                pi[e] = pi[e] - 0.5 * self.dt * self._force(e)
            for e in range(12):
                U = self.gauge.links[e]
                self.gauge.links[e] = su2_project(su2_exp(self.dt * pi[e]) @ U)
            for e in range(12):
                pi[e] = pi[e] - 0.5 * self.dt * self._force(e)
        return pi

    def trajectory(self):
        gauge_old = self.gauge.copy()
        pi = [self._random_momentum() for _ in range(12)]

        H_old = self._kinetic_energy(pi) + self.gauge.wilson_action(self.beta)
        pi = self._leapfrog(pi)
        H_new = self._kinetic_energy(pi) + self.gauge.wilson_action(self.beta)

        dH = H_new - H_old
        if dH < 0 or np.random.rand() < np.exp(-min(dH, 700)):
            self.n_accepted += 1
            accept = True
        else:
            self.gauge = gauge_old
            accept = False

        self.n_total += 1
        return accept

    def get_frame(self, traj):
        return Frame(
            trajectory=traj,
            avg_plaquette=self.gauge.average_plaquette(),
            T_plus_plaq=self.gauge.T_plus_plaquette(),
            T_minus_plaq=self.gauge.T_minus_plaquette(),
            edge_plaquettes=self.gauge.edge_plaquettes()
        )

    def run(self, n_traj, n_therm, start='hot', record_interval=1, verbose=True):
        if start == 'hot':
            self.gauge.hot_start()
        else:
            self.gauge.cold_start()

        self.frames = [self.get_frame(0)]

        if verbose:
            print(f"Stella HMC: β={self.beta}, start={start}")
            print(f"Initial ⟨P⟩={self.frames[0].avg_plaquette:.4f}")

        for i in range(n_therm):
            self.trajectory()
            if (i+1) % record_interval == 0:
                self.frames.append(self.get_frame(i+1))
            if verbose and (i+1) % 25 == 0:
                print(f"  Therm {i+1}/{n_therm}: ⟨P⟩={self.gauge.average_plaquette():.4f}, acc={self.n_accepted/self.n_total:.1%}")

        prod_acc, prod_tot = 0, 0
        for i in range(n_traj):
            acc = self.trajectory()
            prod_acc += int(acc)
            prod_tot += 1
            if (i+1) % record_interval == 0:
                self.frames.append(self.get_frame(n_therm + i + 1))
            if verbose and (i+1) % 50 == 0:
                print(f"  Prod {i+1}/{n_traj}: ⟨P⟩={self.gauge.average_plaquette():.4f}, acc={prod_acc/prod_tot:.1%}")

        if verbose:
            print(f"Recorded {len(self.frames)} frames")
        return self.frames


# ============================================================================
# VISUALIZATION
# ============================================================================

def create_stella_animation(hmc: StellaHMC, frames: List[Frame],
                            title: str, output_html: str):
    """Create 3D animation with stella embedded in honeycomb structure."""

    stella = hmc.stella

    # Create the honeycomb structure
    honeycomb = TetrahedralOctahedralHoneycomb(stella.center, stella.scale)

    # Plaquette history
    plaq_hist = [f.avg_plaquette for f in frames]
    traj_hist = [f.trajectory for f in frames]
    Tp_hist = [f.T_plus_plaq for f in frames]
    Tm_hist = [f.T_minus_plaq for f in frames]

    window = 10
    running_avg = [np.mean(plaq_hist[max(0,i-window+1):i+1]) for i in range(len(plaq_hist))]
    equil = np.mean(plaq_hist[len(plaq_hist)//2:])

    fig = make_subplots(
        rows=1, cols=2,
        specs=[[{"type": "scene"}, {"type": "xy"}]],
        subplot_titles=("Stella Octangula in Tetrahedral-Octahedral Honeycomb", "Plaquette Evolution"),
        column_widths=[0.6, 0.4],
        horizontal_spacing=0.08
    )

    animation_frames = []

    for frame_idx, frame in enumerate(frames):
        frame_data = []

        # ========== HONEYCOMB STRUCTURE (background) ==========

        # Draw the 8 honeycomb tetrahedra as wireframes
        # Each connects center to 3 FCC neighbors
        for tet_idx, face_idxs in enumerate(honeycomb.honeycomb_tet_faces):
            # Get the 3 FCC neighbor vertices for this tet
            v0 = honeycomb.center
            v1 = honeycomb.fcc_neighbors[face_idxs[0]]
            v2 = honeycomb.fcc_neighbors[face_idxs[1]]
            v3 = honeycomb.fcc_neighbors[face_idxs[2]]

            # Color based on T₊ or T₋ group (dim versions)
            if tet_idx in honeycomb.T_plus_tets:
                color = 'rgba(255, 100, 100, 0.15)'
                edge_color = 'rgba(255, 150, 150, 0.4)'
            else:
                color = 'rgba(100, 100, 255, 0.15)'
                edge_color = 'rgba(150, 150, 255, 0.4)'

            # Draw the triangular face (outer face, away from center)
            verts = np.array([v1, v2, v3])
            face_mesh = go.Mesh3d(
                x=verts[:, 0], y=verts[:, 1], z=verts[:, 2],
                i=[0], j=[1], k=[2],
                color=color,
                opacity=0.2,
                showlegend=False,
                hoverinfo='skip'
            )
            frame_data.append(face_mesh)

            # Draw edges of this honeycomb tet (thin lines)
            for va, vb in [(v0, v1), (v0, v2), (v0, v3), (v1, v2), (v2, v3), (v3, v1)]:
                edge_trace = go.Scatter3d(
                    x=[va[0], vb[0]], y=[va[1], vb[1]], z=[va[2], vb[2]],
                    mode='lines',
                    line=dict(color=edge_color, width=2),
                    showlegend=False,
                    hoverinfo='skip'
                )
                frame_data.append(edge_trace)

        # Draw octahedra outlines (square faces at the 6 axis directions)
        for sq_idx, sq in enumerate(honeycomb.octahedra_squares):
            # Get the 4 FCC neighbors forming the square
            sq_verts = np.array([honeycomb.fcc_neighbors[i] for i in sq])
            # The "far" vertex of the octahedron
            ext_v = honeycomb.extended_vertices[sq_idx]

            # Draw edges from square vertices to extended vertex
            for i in range(4):
                va = sq_verts[i]
                vb = ext_v
                edge_trace = go.Scatter3d(
                    x=[va[0], vb[0]], y=[va[1], vb[1]], z=[va[2], vb[2]],
                    mode='lines',
                    line=dict(color='rgba(100, 255, 100, 0.3)', width=1.5),
                    showlegend=False,
                    hoverinfo='skip'
                )
                frame_data.append(edge_trace)

            # Draw the square outline
            for i in range(4):
                va = sq_verts[i]
                vb = sq_verts[(i+1) % 4]
                edge_trace = go.Scatter3d(
                    x=[va[0], vb[0]], y=[va[1], vb[1]], z=[va[2], vb[2]],
                    mode='lines',
                    line=dict(color='rgba(100, 255, 100, 0.3)', width=1.5),
                    showlegend=False,
                    hoverinfo='skip'
                )
                frame_data.append(edge_trace)

        # Draw FCC neighbor vertices (cuboctahedron vertices)
        fcc_trace = go.Scatter3d(
            x=honeycomb.fcc_neighbors[:, 0],
            y=honeycomb.fcc_neighbors[:, 1],
            z=honeycomb.fcc_neighbors[:, 2],
            mode='markers',
            marker=dict(size=5, color='white', symbol='circle',
                       line=dict(width=1, color='gray')),
            name='FCC neighbors',
            hovertemplate="FCC neighbor<br>12-coordination<extra></extra>"
        )
        frame_data.append(fcc_trace)

        # Draw extended vertices (octahedra far vertices)
        ext_trace = go.Scatter3d(
            x=honeycomb.extended_vertices[:, 0],
            y=honeycomb.extended_vertices[:, 1],
            z=honeycomb.extended_vertices[:, 2],
            mode='markers',
            marker=dict(size=4, color='lightgreen', symbol='circle',
                       line=dict(width=1, color='green')),
            name='Octahedra vertices',
            hovertemplate="Octahedron far vertex<extra></extra>"
        )
        frame_data.append(ext_trace)

        # ========== T₊ TETRAHEDRON (RED) - THE STELLA ==========
        # Draw T₊ faces as filled triangles (brighter than honeycomb)
        for face in stella.T_plus_faces:
            verts = stella.vertices[list(face)]
            face_mesh = go.Mesh3d(
                x=verts[:, 0], y=verts[:, 1], z=verts[:, 2],
                i=[0], j=[1], k=[2],
                color='red',
                opacity=0.4,
                showlegend=False,
                hoverinfo='skip'
            )
            frame_data.append(face_mesh)

        # T₊ edges (thick red lines)
        for (i, j) in stella.T_plus_edges:
            v1, v2 = stella.vertices[i], stella.vertices[j]
            plaq_val = np.clip(frame.edge_plaquettes[stella.edges.index((i,j))], 0, 1)
            intensity = int(180 + 75 * plaq_val)
            color = f'rgb({intensity}, 50, 50)'
            width = 8 + 4 * plaq_val

            edge_trace = go.Scatter3d(
                x=[v1[0], v2[0]], y=[v1[1], v2[1]], z=[v1[2], v2[2]],
                mode='lines',
                line=dict(color=color, width=width),
                showlegend=False,
                hovertemplate=f"T₊ edge<br>Plaq={plaq_val:.3f}<extra></extra>"
            )
            frame_data.append(edge_trace)

        # T₊ vertices (red diamonds)
        T_plus_verts = go.Scatter3d(
            x=stella.T_plus_vertices[:, 0],
            y=stella.T_plus_vertices[:, 1],
            z=stella.T_plus_vertices[:, 2],
            mode='markers+text',
            marker=dict(size=12, color='red', symbol='diamond',
                       line=dict(width=2, color='white')),
            text=['T₊₀', 'T₊₁', 'T₊₂', 'T₊₃'],
            textposition='top center',
            textfont=dict(size=10, color='red'),
            name='T₊ vertices'
        )
        frame_data.append(T_plus_verts)

        # ========== T₋ TETRAHEDRON (BLUE) - THE STELLA ==========
        for face in stella.T_minus_faces:
            verts = stella.vertices[list(face)]
            face_mesh = go.Mesh3d(
                x=verts[:, 0], y=verts[:, 1], z=verts[:, 2],
                i=[0], j=[1], k=[2],
                color='blue',
                opacity=0.4,
                showlegend=False,
                hoverinfo='skip'
            )
            frame_data.append(face_mesh)

        # T₋ edges (thick blue lines)
        for (i, j) in stella.T_minus_edges:
            v1, v2 = stella.vertices[i], stella.vertices[j]
            e_idx = stella.edges.index((i, j))
            plaq_val = np.clip(frame.edge_plaquettes[e_idx], 0, 1)
            intensity = int(180 + 75 * plaq_val)
            color = f'rgb(50, 50, {intensity})'
            width = 8 + 4 * plaq_val

            edge_trace = go.Scatter3d(
                x=[v1[0], v2[0]], y=[v1[1], v2[1]], z=[v1[2], v2[2]],
                mode='lines',
                line=dict(color=color, width=width),
                showlegend=False,
                hovertemplate=f"T₋ edge<br>Plaq={plaq_val:.3f}<extra></extra>"
            )
            frame_data.append(edge_trace)

        # T₋ vertices (blue diamonds)
        T_minus_verts = go.Scatter3d(
            x=stella.T_minus_vertices[:, 0],
            y=stella.T_minus_vertices[:, 1],
            z=stella.T_minus_vertices[:, 2],
            mode='markers+text',
            marker=dict(size=12, color='blue', symbol='diamond',
                       line=dict(width=2, color='white')),
            text=['T₋₀', 'T₋₁', 'T₋₂', 'T₋₃'],
            textposition='top center',
            textfont=dict(size=10, color='blue'),
            name='T₋ vertices'
        )
        frame_data.append(T_minus_verts)

        # ========== CENTRAL VERTEX (where stella appears) ==========
        center_trace = go.Scatter3d(
            x=[stella.center[0]], y=[stella.center[1]], z=[stella.center[2]],
            mode='markers',
            marker=dict(size=10, color='yellow', symbol='circle',
                       line=dict(width=2, color='orange')),
            name='Center V',
            hovertemplate="Central vertex V<br>8 tets + 6 octs meet here<extra></extra>"
        )
        frame_data.append(center_trace)

        # ========== PLAQUETTE EVOLUTION ==========
        plaq_raw = go.Scatter(
            x=traj_hist[:frame_idx+1], y=plaq_hist[:frame_idx+1],
            mode='lines', line=dict(color='rgba(200,200,200,0.3)', width=1),
            showlegend=False
        )
        frame_data.append(plaq_raw)

        Tp_trace = go.Scatter(
            x=traj_hist[:frame_idx+1], y=Tp_hist[:frame_idx+1],
            mode='lines', line=dict(color='red', width=2),
            name='T₊ plaq'
        )
        frame_data.append(Tp_trace)

        Tm_trace = go.Scatter(
            x=traj_hist[:frame_idx+1], y=Tm_hist[:frame_idx+1],
            mode='lines', line=dict(color='blue', width=2),
            name='T₋ plaq'
        )
        frame_data.append(Tm_trace)

        avg_trace = go.Scatter(
            x=traj_hist[:frame_idx+1], y=running_avg[:frame_idx+1],
            mode='lines', line=dict(color='yellow', width=3),
            name='Average'
        )
        frame_data.append(avg_trace)

        current = go.Scatter(
            x=[traj_hist[frame_idx]], y=[plaq_hist[frame_idx]],
            mode='markers', marker=dict(size=10, color='white'),
            showlegend=False
        )
        frame_data.append(current)

        equil_line = go.Scatter(
            x=[0, max(traj_hist)], y=[equil, equil],
            mode='lines', line=dict(color='lime', width=2, dash='dot'),
            name=f'Eq: {equil:.3f}'
        )
        frame_data.append(equil_line)

        animation_frames.append(go.Frame(data=frame_data, name=str(frame_idx)))

    fig.add_traces(animation_frames[0].data)
    fig.frames = animation_frames

    fig.update_layout(
        title=dict(
            text=f"<b>{title}</b><br><sup>Stella octangula (T₊ red, T₋ blue) embedded in tetrahedral-octahedral honeycomb</sup>",
            x=0.5, font=dict(size=16)
        ),
        scene=dict(
            xaxis=dict(title='X', range=[-2.5, 2.5], showbackground=True,
                      backgroundcolor='rgb(15,15,25)'),
            yaxis=dict(title='Y', range=[-2.5, 2.5], showbackground=True,
                      backgroundcolor='rgb(15,15,25)'),
            zaxis=dict(title='Z', range=[-2.5, 2.5], showbackground=True,
                      backgroundcolor='rgb(15,15,25)'),
            camera=dict(eye=dict(x=2.2, y=2.2, z=1.8)),
            aspectmode='cube'
        ),
        xaxis=dict(title='Trajectory', domain=[0.62, 1.0], gridcolor='rgba(100,100,100,0.3)'),
        yaxis=dict(title='⟨P⟩', range=[0, 1.05], gridcolor='rgba(100,100,100,0.3)'),
        paper_bgcolor='rgb(10,10,20)',
        plot_bgcolor='rgb(20,20,35)',
        font=dict(color='white', size=11),
        showlegend=True,
        legend=dict(x=0.65, y=0.98, bgcolor='rgba(0,0,0,0.5)', font=dict(size=9)),
        updatemenus=[dict(
            type='buttons', showactive=False, y=1.12, x=0.5, xanchor='center',
            buttons=[
                dict(label='▶ Play', method='animate',
                     args=[None, dict(frame=dict(duration=100, redraw=True),
                                     fromcurrent=True, mode='immediate')]),
                dict(label='⏸ Pause', method='animate',
                     args=[[None], dict(frame=dict(duration=0, redraw=False),
                                       mode='immediate')])
            ]
        )],
        sliders=[dict(
            active=0, yanchor='top', xanchor='left',
            currentvalue=dict(prefix='Traj: ', visible=True, font=dict(size=12)),
            pad=dict(b=10, t=50), len=0.9, x=0.05, y=0,
            steps=[dict(args=[[str(i)], dict(frame=dict(duration=100, redraw=True), mode='immediate')],
                       label=str(frames[i].trajectory), method='animate')
                   for i in range(0, len(frames), max(1, len(frames)//50))]
        )]
    )

    fig.write_html(output_html, include_plotlyjs=True, full_html=True)
    print(f"Saved: {output_html}")
    return fig


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 70)
    print("STELLA OCTANGULA IN TETRAHEDRAL-OCTAHEDRAL HONEYCOMB")
    print("=" * 70)
    print("""
From Theorem 0.0.6:
  - At each vertex V of the honeycomb, 8 tetrahedra meet
  - These 8 tets partition into T₊ (red, 4 tets) and T₋ (blue, 4 tets)
  - T₊ ∪ T₋ form the stella octangula (two interpenetrating tetrahedra)
  - 6 octahedra (green) also meet at V, providing transition regions
  - The vertices of T₊ and T₋ are the "outer" vertices of the 8 honeycomb tets

Structure shown:
  - Central vertex V (yellow) where 8 tets + 6 octs meet
  - 12 FCC neighbors (white) at distance √2 from V
  - 6 extended vertices (light green) at distance 2 from V
  - Honeycomb tetrahedra (faint red/blue) connecting V to FCC neighbors
  - Stella T₊ (bright red) and T₋ (bright blue) highlighted
  - Octahedra outlines (green) connecting to extended vertices
""")

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    # Hot start
    print("-" * 50)
    print("HOT START")
    print("-" * 50)
    hmc_hot = StellaHMC(beta=2.2, n_leapfrog=15, dt=0.08)
    frames_hot = hmc_hot.run(n_traj=250, n_therm=80, start='hot', record_interval=2, verbose=True)

    print("\nCreating animation...")
    create_stella_animation(hmc_hot, frames_hot,
                           "Stella in Honeycomb: Hot Start",
                           str(output_dir / "stella_honeycomb_hot.html"))

    # Cold start
    print("\n" + "-" * 50)
    print("COLD START")
    print("-" * 50)
    hmc_cold = StellaHMC(beta=2.2, n_leapfrog=15, dt=0.08)
    frames_cold = hmc_cold.run(n_traj=250, n_therm=80, start='cold', record_interval=2, verbose=True)

    print("\nCreating animation...")
    create_stella_animation(hmc_cold, frames_cold,
                           "Stella in Honeycomb: Cold Start",
                           str(output_dir / "stella_honeycomb_cold.html"))

    # Summary
    print("\n" + "=" * 70)
    print("COMPLETE")
    print("=" * 70)
    equil_hot = np.mean([f.avg_plaquette for f in frames_hot[len(frames_hot)//2:]])
    equil_cold = np.mean([f.avg_plaquette for f in frames_cold[len(frames_cold)//2:]])
    print(f"\nHot start:  ⟨P⟩ = {equil_hot:.4f}")
    print(f"Cold start: ⟨P⟩ = {equil_cold:.4f}")
    print(f"\nOutputs:")
    print(f"  {output_dir}/stella_honeycomb_hot.html")
    print(f"  {output_dir}/stella_honeycomb_cold.html")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Tetrahedral-Octahedral Honeycomb (Octet Truss) HMC Visualization
================================================================

Visualizes the CORRECT lattice structure from Theorem 0.0.6:

The tetrahedral-octahedral honeycomb where:
    - Vertices form the FCC lattice (coordination number 12)
    - At each vertex, 8 tetrahedra meet → form stella octangula (T₊ ∪ T₋)
    - Octahedra fill gaps as color-neutral transition regions
    - Edge constraint: 2 tetrahedra + 2 octahedra = 360° (dihedral angles)

The stella octangula is NOT a standalone unit - it appears at EACH VERTEX
of the honeycomb as the local configuration of 8 meeting tetrahedra.

FCC Lattice:
    Λ_FCC = {(n₁, n₂, n₃) ∈ Z³ : n₁ + n₂ + n₃ ≡ 0 (mod 2)}
    Basis: a₁ = (1,1,0), a₂ = (1,0,1), a₃ = (0,1,1)

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-03
Reference: Theorem 0.0.6-Spatial-Extension-From-Octet-Truss.md
"""

import numpy as np
from scipy import linalg
from typing import List, Tuple, Dict, Set
from pathlib import Path
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from dataclasses import dataclass
from itertools import combinations

# ============================================================================
# FCC LATTICE AND OCTET TRUSS GEOMETRY
# ============================================================================

class FCCLattice:
    """
    Face-Centered Cubic lattice - the vertex set of the octet truss.

    Λ_FCC = {(n₁, n₂, n₃) ∈ Z³ : n₁ + n₂ + n₃ ≡ 0 (mod 2)}

    Each vertex has 12 nearest neighbors (coordination number 12).
    """

    def __init__(self, extent: int = 2):
        """
        Create FCC lattice within a cube of given extent.

        Parameters
        ----------
        extent : int
            Generate vertices with coordinates in [-extent, extent]
        """
        self.extent = extent

        # Generate all FCC vertices within extent
        self.vertices = []
        self.vertex_to_idx = {}

        for n1 in range(-extent, extent + 1):
            for n2 in range(-extent, extent + 1):
                for n3 in range(-extent, extent + 1):
                    # FCC parity constraint
                    if (n1 + n2 + n3) % 2 == 0:
                        v = (n1, n2, n3)
                        self.vertex_to_idx[v] = len(self.vertices)
                        self.vertices.append(np.array(v, dtype=float))

        self.vertices = np.array(self.vertices)
        self.n_vertices = len(self.vertices)

        # Find edges (nearest neighbors at distance √2)
        self.edges = []
        self.edge_to_idx = {}

        # FCC nearest neighbors: 12 neighbors at distance √2
        # Directions: (±1, ±1, 0), (±1, 0, ±1), (0, ±1, ±1)
        self.nn_directions = [
            (1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0),
            (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1),
            (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)
        ]

        for i, v1 in enumerate(self.vertices):
            v1_tuple = tuple(v1.astype(int))
            for d in self.nn_directions:
                v2_tuple = (v1_tuple[0] + d[0], v1_tuple[1] + d[1], v1_tuple[2] + d[2])
                if v2_tuple in self.vertex_to_idx:
                    j = self.vertex_to_idx[v2_tuple]
                    if i < j:  # Avoid duplicates
                        edge = (i, j)
                        self.edge_to_idx[edge] = len(self.edges)
                        self.edges.append(edge)

        self.n_edges = len(self.edges)

        # Find tetrahedra and octahedra
        self._find_cells()

    def _find_cells(self):
        """Find all tetrahedra and octahedra in the honeycomb."""

        # Tetrahedra: 4 mutually adjacent FCC vertices forming a regular tetrahedron
        # In the octet truss, tetrahedra have vertices at:
        # - "Up" tetrahedra: centered at (n₁+½, n₂+½, n₃+½) where n₁+n₂+n₃ even
        # - "Down" tetrahedra: centered at (n₁+½, n₂+½, n₃+½) where n₁+n₂+n₃ odd

        self.tetrahedra = []
        self.octahedra = []

        # Find tetrahedra by looking for complete K₄ subgraphs
        # Each tetrahedron has 4 vertices all pairwise at distance √2

        # Build adjacency for faster lookup
        adj = {i: set() for i in range(self.n_vertices)}
        for (i, j) in self.edges:
            adj[i].add(j)
            adj[j].add(i)

        # Find tetrahedra (complete K₄ subgraphs)
        found_tets = set()
        for i in range(self.n_vertices):
            neighbors_i = adj[i]
            for j in neighbors_i:
                if j <= i:
                    continue
                neighbors_ij = neighbors_i & adj[j]
                for k in neighbors_ij:
                    if k <= j:
                        continue
                    neighbors_ijk = neighbors_ij & adj[k]
                    for l in neighbors_ijk:
                        if l <= k:
                            continue
                        # (i,j,k,l) form a tetrahedron
                        tet = tuple(sorted([i, j, k, l]))
                        if tet not in found_tets:
                            found_tets.add(tet)
                            self.tetrahedra.append(tet)

        # Classify tetrahedra into T₊ and T₋ based on parity
        self.T_plus_tets = []
        self.T_minus_tets = []

        for tet in self.tetrahedra:
            # Compute centroid
            centroid = np.mean([self.vertices[i] for i in tet], axis=0)
            # Parity based on centroid position
            # T₊: centroid has even parity sum, T₋: odd
            parity_sum = int(round(centroid[0] + centroid[1] + centroid[2]))
            if parity_sum % 2 == 0:
                self.T_plus_tets.append(tet)
            else:
                self.T_minus_tets.append(tet)

        # Find octahedra (6 vertices forming regular octahedron)
        # Octahedra are centered at integer points (n₁, n₂, n₃) with n₁+n₂+n₃ odd
        found_octs = set()

        # Octahedron centers
        for n1 in range(-self.extent, self.extent + 1):
            for n2 in range(-self.extent, self.extent + 1):
                for n3 in range(-self.extent, self.extent + 1):
                    if (n1 + n2 + n3) % 2 == 1:  # Octahedron center parity
                        center = np.array([n1, n2, n3], dtype=float)
                        # Octahedron vertices at distance 1 from center
                        oct_vertices = []
                        for d in [(1,0,0), (-1,0,0), (0,1,0), (0,-1,0), (0,0,1), (0,0,-1)]:
                            v = (n1 + d[0], n2 + d[1], n3 + d[2])
                            if v in self.vertex_to_idx:
                                oct_vertices.append(self.vertex_to_idx[v])

                        if len(oct_vertices) == 6:
                            oct = tuple(sorted(oct_vertices))
                            if oct not in found_octs:
                                found_octs.add(oct)
                                self.octahedra.append(oct)

        self.n_tetrahedra = len(self.tetrahedra)
        self.n_octahedra = len(self.octahedra)


class OctetTrussGaugeField:
    """SU(2) gauge field on the octet truss edges."""

    def __init__(self, lattice: FCCLattice):
        self.lattice = lattice
        self.n_colors = 2

        # One SU(2) matrix per edge
        self.links = [np.eye(2, dtype=complex) for _ in range(lattice.n_edges)]

    def get_link(self, i: int, j: int) -> np.ndarray:
        """Get U_ij."""
        if i > j:
            i, j = j, i
            return self.links[self.lattice.edge_to_idx[(i, j)]].conj().T
        return self.links[self.lattice.edge_to_idx[(i, j)]].copy()

    def set_link(self, i: int, j: int, U: np.ndarray):
        """Set U_ij."""
        if i > j:
            i, j = j, i
            U = U.conj().T
        idx = self.lattice.edge_to_idx[(i, j)]
        self.links[idx] = U.copy()

    def tet_plaquette(self, tet: Tuple[int, int, int, int]) -> float:
        """
        Compute average plaquette for a tetrahedron.
        A tetrahedron has 4 triangular faces.
        """
        i, j, k, l = tet
        faces = [(i, j, k), (i, j, l), (i, k, l), (j, k, l)]

        total = 0.0
        for (a, b, c) in faces:
            # Plaquette = Tr(U_ab U_bc U_ca) / 2
            P = self.get_link(a, b) @ self.get_link(b, c) @ self.get_link(c, a)
            total += 0.5 * np.real(np.trace(P))

        return total / 4

    def average_plaquette(self) -> float:
        """Average over all tetrahedra."""
        if not self.lattice.tetrahedra:
            return 0.5
        return np.mean([self.tet_plaquette(t) for t in self.lattice.tetrahedra])

    def edge_plaquette_values(self) -> np.ndarray:
        """Compute average plaquette for faces touching each edge."""
        values = np.zeros(self.lattice.n_edges)

        for e_idx, (i, j) in enumerate(self.lattice.edges):
            # Find tetrahedra containing this edge
            face_vals = []
            for tet in self.lattice.tetrahedra:
                if i in tet and j in tet:
                    # Find the two faces containing edge (i,j)
                    others = [v for v in tet if v != i and v != j]
                    for k in others:
                        P = self.get_link(i, j) @ self.get_link(j, k) @ self.get_link(k, i)
                        face_vals.append(0.5 * np.real(np.trace(P)))

            values[e_idx] = np.mean(face_vals) if face_vals else 0.5

        return values

    def wilson_action(self, beta: float) -> float:
        """Wilson gauge action."""
        total = 0.0
        for tet in self.lattice.tetrahedra:
            i, j, k, l = tet
            for (a, b, c) in [(i,j,k), (i,j,l), (i,k,l), (j,k,l)]:
                P = self.get_link(a, b) @ self.get_link(b, c) @ self.get_link(c, a)
                total += 1 - 0.5 * np.real(np.trace(P))
        return beta * total

    def hot_start(self):
        """Random configuration."""
        for idx in range(self.lattice.n_edges):
            a = np.random.randn(4)
            a = a / np.linalg.norm(a)
            self.links[idx] = self._quaternion_to_su2(a)

    def cold_start(self):
        """Near-identity configuration."""
        for idx in range(self.lattice.n_edges):
            a = np.array([1.0, 0.01*np.random.randn(),
                          0.01*np.random.randn(), 0.01*np.random.randn()])
            a = a / np.linalg.norm(a)
            self.links[idx] = self._quaternion_to_su2(a)

    def _quaternion_to_su2(self, a):
        return np.array([
            [a[0] + 1j*a[3], a[2] + 1j*a[1]],
            [-a[2] + 1j*a[1], a[0] - 1j*a[3]]
        ], dtype=complex)

    def copy(self):
        new = OctetTrussGaugeField(self.lattice)
        new.links = [link.copy() for link in self.links]
        return new


# ============================================================================
# HMC ON OCTET TRUSS
# ============================================================================

@dataclass
class OctetFrame:
    trajectory: int
    avg_plaquette: float
    T_plus_plaquette: float
    T_minus_plaquette: float
    edge_plaquettes: np.ndarray


class OctetHMC:
    """HMC on the tetrahedral-octahedral honeycomb."""

    def __init__(self, extent: int = 2, beta: float = 2.2,
                 n_leapfrog: int = 12, dt: float = 0.1):
        self.lattice = FCCLattice(extent)
        self.beta = beta
        self.n_leapfrog = n_leapfrog
        self.dt = dt

        self.gauge = OctetTrussGaugeField(self.lattice)

        self.n_accepted = 0
        self.n_total = 0
        self.frames: List[OctetFrame] = []

        print(f"Octet Truss: {self.lattice.n_vertices} FCC vertices, "
              f"{self.lattice.n_edges} edges, "
              f"{self.lattice.n_tetrahedra} tetrahedra "
              f"({len(self.lattice.T_plus_tets)} T₊, {len(self.lattice.T_minus_tets)} T₋), "
              f"{self.lattice.n_octahedra} octahedra")

    def _su2_exp(self, H):
        h1 = np.imag(H[0, 1] + H[1, 0]) / 2
        h2 = np.real(H[0, 1] - H[1, 0]) / 2
        h3 = np.imag(H[0, 0] - H[1, 1]) / 2
        h_norm = np.sqrt(h1**2 + h2**2 + h3**2)
        if h_norm < 1e-10:
            return np.eye(2, dtype=complex) + H
        return np.cos(h_norm) * np.eye(2, dtype=complex) + np.sin(h_norm) / h_norm * H

    def _su2_project(self, U):
        u, s, vh = np.linalg.svd(U)
        W = u @ vh
        return W / np.sqrt(np.linalg.det(W))

    def _random_momentum(self):
        a = np.random.randn(3)
        sigma = [
            np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex)
        ]
        return 1j * sum(a[i] * sigma[i] for i in range(3))

    def _kinetic_energy(self, pi):
        return sum(-0.5 * np.real(np.trace(p @ p)) for p in pi)

    def _force(self, edge_idx):
        """Compute force on edge from all touching plaquettes."""
        i, j = self.lattice.edges[edge_idx]
        U = self.gauge.links[edge_idx]

        staple = np.zeros((2, 2), dtype=complex)

        # Find all tetrahedra containing this edge
        for tet in self.lattice.tetrahedra:
            if i in tet and j in tet:
                others = [v for v in tet if v != i and v != j]
                for k in others:
                    # Staple contribution: U_jk U_ki
                    staple += self.gauge.get_link(j, k) @ self.gauge.get_link(k, i)

        X = (self.beta / 2) * U @ staple
        F = 0.5 * (X - X.conj().T)
        F = F - np.trace(F) / 2 * np.eye(2)
        return F

    def _leapfrog(self, pi):
        dt = self.dt
        for _ in range(self.n_leapfrog):
            # Half step momenta
            for e_idx in range(self.lattice.n_edges):
                F = self._force(e_idx)
                pi[e_idx] = pi[e_idx] - 0.5 * dt * F

            # Full step positions
            for e_idx in range(self.lattice.n_edges):
                U_old = self.gauge.links[e_idx]
                self.gauge.links[e_idx] = self._su2_project(
                    self._su2_exp(dt * pi[e_idx]) @ U_old
                )

            # Half step momenta
            for e_idx in range(self.lattice.n_edges):
                F = self._force(e_idx)
                pi[e_idx] = pi[e_idx] - 0.5 * dt * F

        return pi

    def trajectory(self):
        gauge_old = self.gauge.copy()

        pi = [self._random_momentum() for _ in range(self.lattice.n_edges)]

        K_old = self._kinetic_energy(pi)
        S_old = self.gauge.wilson_action(self.beta)
        H_old = K_old + S_old

        pi = self._leapfrog(pi)

        K_new = self._kinetic_energy(pi)
        S_new = self.gauge.wilson_action(self.beta)
        H_new = K_new + S_new

        dH = H_new - H_old

        if dH < 0 or np.random.rand() < np.exp(-min(dH, 700)):
            accept = True
            self.n_accepted += 1
        else:
            accept = False
            self.gauge = gauge_old

        self.n_total += 1
        return accept

    def get_frame(self, traj: int) -> OctetFrame:
        T_plus_plaq = np.mean([self.gauge.tet_plaquette(t)
                              for t in self.lattice.T_plus_tets]) if self.lattice.T_plus_tets else 0.5
        T_minus_plaq = np.mean([self.gauge.tet_plaquette(t)
                               for t in self.lattice.T_minus_tets]) if self.lattice.T_minus_tets else 0.5

        return OctetFrame(
            trajectory=traj,
            avg_plaquette=self.gauge.average_plaquette(),
            T_plus_plaquette=T_plus_plaq,
            T_minus_plaquette=T_minus_plaq,
            edge_plaquettes=self.gauge.edge_plaquette_values()
        )

    def run(self, n_traj: int, n_therm: int, start: str = 'hot',
            record_interval: int = 2, verbose: bool = True):

        if start == 'hot':
            self.gauge.hot_start()
        else:
            self.gauge.cold_start()

        self.frames = [self.get_frame(0)]

        if verbose:
            print(f"β={self.beta}, start={start}")
            print(f"Initial ⟨P⟩ = {self.frames[0].avg_plaquette:.4f}")

        # Thermalization
        for i in range(n_therm):
            self.trajectory()
            if (i + 1) % record_interval == 0:
                self.frames.append(self.get_frame(i + 1))
            if verbose and (i + 1) % 20 == 0:
                plaq = self.gauge.average_plaquette()
                rate = self.n_accepted / self.n_total
                print(f"  Therm {i+1}/{n_therm}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Production
        prod_acc, prod_tot = 0, 0
        for i in range(n_traj):
            acc = self.trajectory()
            prod_acc += int(acc)
            prod_tot += 1
            traj = n_therm + i + 1
            if (i + 1) % record_interval == 0:
                self.frames.append(self.get_frame(traj))
            if verbose and (i + 1) % 40 == 0:
                plaq = self.gauge.average_plaquette()
                rate = prod_acc / prod_tot
                print(f"  Prod {i+1}/{n_traj}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        if verbose:
            print(f"Recorded {len(self.frames)} frames")

        return self.frames


# ============================================================================
# VISUALIZATION
# ============================================================================

def create_octet_animation(hmc: OctetHMC, frames: List[OctetFrame],
                           title: str, output_html: str) -> go.Figure:
    """Create 3D animated visualization of the octet truss."""

    lattice = hmc.lattice
    vertices = lattice.vertices

    # Plaquette history
    plaq_history = [f.avg_plaquette for f in frames]
    traj_history = [f.trajectory for f in frames]
    T_plus_history = [f.T_plus_plaquette for f in frames]
    T_minus_history = [f.T_minus_plaquette for f in frames]

    # Running average and equilibrium
    window = 10
    running_avg = [np.mean(plaq_history[max(0, i-window+1):i+1]) for i in range(len(plaq_history))]
    equil = np.mean(plaq_history[len(plaq_history)//2:])

    # Create figure
    fig = make_subplots(
        rows=1, cols=2,
        specs=[[{"type": "scene"}, {"type": "xy"}]],
        subplot_titles=("Tetrahedral-Octahedral Honeycomb", "Plaquette Evolution"),
        column_widths=[0.6, 0.4],
        horizontal_spacing=0.08
    )

    # Build animation frames
    animation_frames = []

    for frame_idx, frame in enumerate(frames):
        frame_data = []

        # --- 3D Octet Truss ---

        # FCC vertices
        vertex_trace = go.Scatter3d(
            x=vertices[:, 0], y=vertices[:, 1], z=vertices[:, 2],
            mode='markers',
            marker=dict(size=5, color='white', opacity=0.7,
                       line=dict(width=1, color='gray')),
            name='FCC vertices',
            hovertemplate="FCC vertex<extra></extra>"
        )
        frame_data.append(vertex_trace)

        # Edges colored by plaquette
        edge_plaq = frame.edge_plaquettes

        for e_idx, (i, j) in enumerate(lattice.edges):
            plaq_val = np.clip(edge_plaq[e_idx], 0, 1)

            # Color gradient: red (disordered) → green (ordered)
            if plaq_val < 0.5:
                r, g, b = 255, int(255 * plaq_val * 2), 50
            else:
                r, g, b = int(255 * (1 - (plaq_val - 0.5) * 2)), 255, 50

            color = f'rgb({r},{g},{b})'
            width = 2 + 4 * plaq_val

            edge_trace = go.Scatter3d(
                x=[vertices[i, 0], vertices[j, 0]],
                y=[vertices[i, 1], vertices[j, 1]],
                z=[vertices[i, 2], vertices[j, 2]],
                mode='lines',
                line=dict(color=color, width=width),
                showlegend=False,
                hovertemplate=f"Edge ({i},{j})<br>Plaq={plaq_val:.3f}<extra></extra>"
            )
            frame_data.append(edge_trace)

        # Highlight T₊ tetrahedra (red, semi-transparent)
        for tet in lattice.T_plus_tets[:3]:  # Show first few to avoid clutter
            tet_verts = vertices[list(tet)]
            # Draw tetrahedron edges
            for a, b in combinations(range(4), 2):
                edge_trace = go.Scatter3d(
                    x=[tet_verts[a, 0], tet_verts[b, 0]],
                    y=[tet_verts[a, 1], tet_verts[b, 1]],
                    z=[tet_verts[a, 2], tet_verts[b, 2]],
                    mode='lines',
                    line=dict(color='rgba(255,50,50,0.6)', width=4),
                    showlegend=False,
                    hoverinfo='skip'
                )
                frame_data.append(edge_trace)

        # Highlight T₋ tetrahedra (blue, semi-transparent)
        for tet in lattice.T_minus_tets[:3]:
            tet_verts = vertices[list(tet)]
            for a, b in combinations(range(4), 2):
                edge_trace = go.Scatter3d(
                    x=[tet_verts[a, 0], tet_verts[b, 0]],
                    y=[tet_verts[a, 1], tet_verts[b, 1]],
                    z=[tet_verts[a, 2], tet_verts[b, 2]],
                    mode='lines',
                    line=dict(color='rgba(50,50,255,0.6)', width=4),
                    showlegend=False,
                    hoverinfo='skip'
                )
                frame_data.append(edge_trace)

        # --- Plaquette evolution ---

        plaq_raw = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=plaq_history[:frame_idx+1],
            mode='lines',
            line=dict(color='rgba(200,200,200,0.3)', width=1),
            name='Raw', showlegend=False
        )
        frame_data.append(plaq_raw)

        T_plus_trace = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=T_plus_history[:frame_idx+1],
            mode='lines',
            line=dict(color='red', width=2),
            name='T₊'
        )
        frame_data.append(T_plus_trace)

        T_minus_trace = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=T_minus_history[:frame_idx+1],
            mode='lines',
            line=dict(color='blue', width=2),
            name='T₋'
        )
        frame_data.append(T_minus_trace)

        avg_trace = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=running_avg[:frame_idx+1],
            mode='lines',
            line=dict(color='yellow', width=3),
            name='Average'
        )
        frame_data.append(avg_trace)

        current = go.Scatter(
            x=[traj_history[frame_idx]],
            y=[plaq_history[frame_idx]],
            mode='markers',
            marker=dict(size=10, color='white'),
            showlegend=False
        )
        frame_data.append(current)

        equil_line = go.Scatter(
            x=[0, max(traj_history)],
            y=[equil, equil],
            mode='lines',
            line=dict(color='lime', width=2, dash='dot'),
            name=f'Eq: {equil:.3f}'
        )
        frame_data.append(equil_line)

        animation_frames.append(go.Frame(data=frame_data, name=str(frame_idx)))

    # Add initial traces
    fig.add_traces(animation_frames[0].data)
    fig.frames = animation_frames

    # Layout
    max_coord = lattice.extent + 0.5
    fig.update_layout(
        title=dict(
            text=f"<b>{title}</b><br><sup>FCC vertices, T₊ (red) and T₋ (blue) tetrahedra form stella at each vertex</sup>",
            x=0.5, font=dict(size=16)
        ),
        scene=dict(
            xaxis=dict(title='X', range=[-max_coord, max_coord], showbackground=True,
                      backgroundcolor='rgb(15,15,25)', gridcolor='rgba(100,100,100,0.2)'),
            yaxis=dict(title='Y', range=[-max_coord, max_coord], showbackground=True,
                      backgroundcolor='rgb(15,15,25)', gridcolor='rgba(100,100,100,0.2)'),
            zaxis=dict(title='Z', range=[-max_coord, max_coord], showbackground=True,
                      backgroundcolor='rgb(15,15,25)', gridcolor='rgba(100,100,100,0.2)'),
            camera=dict(eye=dict(x=1.8, y=1.8, z=1.2)),
            aspectmode='cube'
        ),
        xaxis=dict(title='Trajectory', domain=[0.62, 1.0], gridcolor='rgba(100,100,100,0.3)'),
        yaxis=dict(title='⟨P⟩', range=[0, 1.05], gridcolor='rgba(100,100,100,0.3)'),
        paper_bgcolor='rgb(10,10,20)',
        plot_bgcolor='rgb(20,20,35)',
        font=dict(color='white', size=11),
        showlegend=True,
        legend=dict(x=0.65, y=0.98, bgcolor='rgba(0,0,0,0.5)', font=dict(size=10)),
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
    print("TETRAHEDRAL-OCTAHEDRAL HONEYCOMB (OCTET TRUSS) HMC")
    print("From Theorem 0.0.6: Spatial Extension from Octet Truss")
    print("=" * 70)

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    # Use extent=1 for cleaner visualization (smaller lattice)
    extent = 1
    beta = 2.0
    n_therm = 60
    n_prod = 150

    # Hot start
    print("\n" + "-" * 50)
    print("HOT START")
    print("-" * 50)
    hmc_hot = OctetHMC(extent=extent, beta=beta, n_leapfrog=10, dt=0.12)
    frames_hot = hmc_hot.run(n_prod, n_therm, start='hot', record_interval=2, verbose=True)

    print("\nCreating animation...")
    create_octet_animation(hmc_hot, frames_hot,
                          "Octet Truss: Hot Start",
                          str(output_dir / "octet_truss_hot.html"))

    # Cold start
    print("\n" + "-" * 50)
    print("COLD START")
    print("-" * 50)
    hmc_cold = OctetHMC(extent=extent, beta=beta, n_leapfrog=10, dt=0.12)
    frames_cold = hmc_cold.run(n_prod, n_therm, start='cold', record_interval=2, verbose=True)

    print("\nCreating animation...")
    create_octet_animation(hmc_cold, frames_cold,
                          "Octet Truss: Cold Start",
                          str(output_dir / "octet_truss_cold.html"))

    # Summary
    print("\n" + "=" * 70)
    print("COMPLETE")
    print("=" * 70)
    equil_hot = np.mean([f.avg_plaquette for f in frames_hot[len(frames_hot)//2:]])
    equil_cold = np.mean([f.avg_plaquette for f in frames_cold[len(frames_cold)//2:]])
    print(f"\nHot start:  ⟨P⟩ = {equil_hot:.4f}")
    print(f"Cold start: ⟨P⟩ = {equil_cold:.4f}")
    print(f"\nOutputs in {output_dir}/:")
    print("  - octet_truss_hot.html")
    print("  - octet_truss_cold.html")


if __name__ == "__main__":
    main()

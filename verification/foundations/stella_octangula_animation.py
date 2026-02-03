#!/usr/bin/env python3
"""
Stella Octangula HMC Visualization
==================================

Visualizes HMC evolution on the ACTUAL stella octangula geometry:
Two interpenetrating tetrahedra (T₊ and T₋) with:
    - 8 vertices (4 + 4)
    - 12 edges (6 + 6)
    - 8 faces (4 + 4)

This is the fundamental lattice of the Chiral Geometrogenesis framework,
NOT a standard hypercubic lattice.

Vertex embedding:
    T₊: (±1, ±1, ±1) with even parity (product of signs = +1)
    T₋: (±1, ±1, ±1) with odd parity (product of signs = -1)

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

# ============================================================================
# STELLA OCTANGULA GEOMETRY
# ============================================================================

class StellaOctangula:
    """
    The stella octangula: two interpenetrating tetrahedra.

    T₊ vertices (even parity - product of signs = +1):
        v0 = (+1, +1, +1)
        v1 = (+1, -1, -1)
        v2 = (-1, +1, -1)
        v3 = (-1, -1, +1)

    T₋ vertices (odd parity - product of signs = -1):
        v4 = (-1, -1, -1)
        v5 = (-1, +1, +1)
        v6 = (+1, -1, +1)
        v7 = (+1, +1, -1)
    """

    def __init__(self):
        # T₊ vertices (even parity)
        self.T_plus_vertices = np.array([
            [+1, +1, +1],   # v0
            [+1, -1, -1],   # v1
            [-1, +1, -1],   # v2
            [-1, -1, +1],   # v3
        ], dtype=float)

        # T₋ vertices (odd parity)
        self.T_minus_vertices = np.array([
            [-1, -1, -1],   # v4
            [-1, +1, +1],   # v5
            [+1, -1, +1],   # v6
            [+1, +1, -1],   # v7
        ], dtype=float)

        # All 8 vertices
        self.vertices = np.vstack([self.T_plus_vertices, self.T_minus_vertices])
        self.n_vertices = 8

        # T₊ edges (complete graph K₄ on vertices 0,1,2,3)
        self.T_plus_edges = [
            (0, 1), (0, 2), (0, 3),
            (1, 2), (1, 3), (2, 3)
        ]

        # T₋ edges (complete graph K₄ on vertices 4,5,6,7)
        self.T_minus_edges = [
            (4, 5), (4, 6), (4, 7),
            (5, 6), (5, 7), (6, 7)
        ]

        # All 12 edges
        self.edges = self.T_plus_edges + self.T_minus_edges
        self.n_edges = 12

        # T₊ faces (4 triangular faces)
        self.T_plus_faces = [
            (0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)
        ]

        # T₋ faces (4 triangular faces)
        self.T_minus_faces = [
            (4, 5, 6), (4, 5, 7), (4, 6, 7), (5, 6, 7)
        ]

        # All 8 faces
        self.faces = self.T_plus_faces + self.T_minus_faces
        self.n_faces = 8

        # Edge to index mapping
        self.edge_to_idx = {e: i for i, e in enumerate(self.edges)}

        # Which tetrahedron each edge belongs to
        self.edge_tetrahedron = ['T+'] * 6 + ['T-'] * 6


# ============================================================================
# SU(2) UTILITIES
# ============================================================================

def quaternion_to_su2(a):
    return np.array([
        [a[0] + 1j*a[3], a[2] + 1j*a[1]],
        [-a[2] + 1j*a[1], a[0] - 1j*a[3]]
    ], dtype=complex)

def su2_random():
    a = np.random.randn(4)
    a = a / np.linalg.norm(a)
    return quaternion_to_su2(a)

def su2_exp(H):
    h1 = np.imag(H[0, 1] + H[1, 0]) / 2
    h2 = np.real(H[0, 1] - H[1, 0]) / 2
    h3 = np.imag(H[0, 0] - H[1, 1]) / 2
    h_norm = np.sqrt(h1**2 + h2**2 + h3**2)
    if h_norm < 1e-10:
        return np.eye(2, dtype=complex) + H
    return np.cos(h_norm) * np.eye(2, dtype=complex) + np.sin(h_norm) / h_norm * H

def su2_project(U):
    u, s, vh = np.linalg.svd(U)
    W = u @ vh
    return W / np.sqrt(np.linalg.det(W))


# ============================================================================
# GAUGE FIELD ON STELLA
# ============================================================================

class StellaGaugeField:
    """SU(2) gauge field on the stella octangula edges."""

    def __init__(self, stella: StellaOctangula):
        self.stella = stella
        self.n_colors = 2

        # One SU(2) matrix per edge
        self.links = [np.eye(2, dtype=complex) for _ in range(stella.n_edges)]

    def get_link(self, i: int, j: int) -> np.ndarray:
        """Get U_ij. Returns U† if edge stored in opposite direction."""
        if (i, j) in self.stella.edge_to_idx:
            return self.links[self.stella.edge_to_idx[(i, j)]].copy()
        elif (j, i) in self.stella.edge_to_idx:
            return self.links[self.stella.edge_to_idx[(j, i)]].conj().T
        else:
            raise ValueError(f"Edge ({i},{j}) not in stella")

    def set_link(self, i: int, j: int, U: np.ndarray):
        if (i, j) in self.stella.edge_to_idx:
            self.links[self.stella.edge_to_idx[(i, j)]] = U.copy()
        elif (j, i) in self.stella.edge_to_idx:
            self.links[self.stella.edge_to_idx[(j, i)]] = U.conj().T

    def plaquette_trace(self, face: Tuple[int, int, int]) -> float:
        """Compute (1/2) Re Tr(U_ij U_jk U_ki) for triangular face."""
        i, j, k = face
        P = self.get_link(i, j) @ self.get_link(j, k) @ self.get_link(k, i)
        return 0.5 * np.real(np.trace(P))

    def average_plaquette(self) -> float:
        """Average over all 8 faces."""
        return sum(self.plaquette_trace(f) for f in self.stella.faces) / self.stella.n_faces

    def wilson_action(self, beta: float) -> float:
        """S = β Σ_f (1 - P_f)."""
        return beta * sum(1 - self.plaquette_trace(f) for f in self.stella.faces)

    def edge_plaquette_values(self) -> np.ndarray:
        """Average plaquette value for faces touching each edge."""
        values = np.zeros(self.stella.n_edges)
        for e_idx, (i, j) in enumerate(self.stella.edges):
            # Find faces containing this edge
            face_vals = []
            for face in self.stella.faces:
                if i in face and j in face:
                    face_vals.append(self.plaquette_trace(face))
            values[e_idx] = np.mean(face_vals) if face_vals else 0.5
        return values

    def staple(self, edge_idx: int) -> np.ndarray:
        """Compute staple sum for given edge."""
        i, j = self.stella.edges[edge_idx]
        staple_sum = np.zeros((2, 2), dtype=complex)

        for face in self.stella.faces:
            if i in face and j in face:
                # Find third vertex
                k = [v for v in face if v != i and v != j][0]
                # Staple: U_jk U_ki
                staple_sum += self.get_link(j, k) @ self.get_link(k, i)

        return staple_sum

    def hot_start(self):
        """Random initial configuration."""
        self.links = [su2_random() for _ in range(self.stella.n_edges)]

    def cold_start(self):
        """Near-identity with small perturbation."""
        for idx in range(self.stella.n_edges):
            a = np.array([1.0, 0.01*np.random.randn(),
                          0.01*np.random.randn(), 0.01*np.random.randn()])
            a = a / np.linalg.norm(a)
            self.links[idx] = quaternion_to_su2(a)

    def copy(self):
        new = StellaGaugeField(self.stella)
        new.links = [link.copy() for link in self.links]
        return new


# ============================================================================
# SCALAR FIELD ON STELLA
# ============================================================================

class StellaScalarField:
    """Complex scalar field on stella vertices."""

    def __init__(self, stella: StellaOctangula):
        self.stella = stella
        self.phi = np.zeros(8, dtype=complex)

    def randomize(self, scale=1.0):
        self.phi = scale * (np.random.randn(8) + 1j * np.random.randn(8))

    def magnitude_squared(self) -> np.ndarray:
        return np.abs(self.phi) ** 2

    def copy(self):
        new = StellaScalarField(self.stella)
        new.phi = self.phi.copy()
        return new


# ============================================================================
# HMC ON STELLA
# ============================================================================

@dataclass
class StellaFrame:
    """Snapshot for animation."""
    trajectory: int
    avg_plaquette: float
    T_plus_plaquette: float  # Average for T₊ faces
    T_minus_plaquette: float  # Average for T₋ faces
    edge_plaquettes: np.ndarray
    scalar_magnitudes: np.ndarray


class StellaHMC:
    """HMC on the stella octangula."""

    def __init__(self, beta: float = 2.2, m2: float = -0.1,
                 lambda_4: float = 0.125, n_leapfrog: int = 15, dt: float = 0.08):
        self.stella = StellaOctangula()
        self.beta = beta
        self.m2 = m2
        self.lambda_4 = lambda_4
        self.n_leapfrog = n_leapfrog
        self.dt = dt

        self.gauge = StellaGaugeField(self.stella)
        self.scalar = StellaScalarField(self.stella)

        self.n_accepted = 0
        self.n_total = 0
        self.frames: List[StellaFrame] = []

    def _random_momentum_gauge(self):
        """su(2) Lie algebra element."""
        a = np.random.randn(3)
        sigma = [
            np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex)
        ]
        return 1j * sum(a[i] * sigma[i] for i in range(3))

    def _kinetic_energy(self, pi_gauge, pi_scalar):
        K = 0.0
        for pi in pi_gauge:
            K -= 0.5 * np.real(np.trace(pi @ pi))
        K += 0.5 * np.sum(np.abs(pi_scalar) ** 2)
        return K

    def _gauge_force(self, edge_idx):
        U = self.gauge.links[edge_idx]
        staple = self.gauge.staple(edge_idx)
        X = (self.beta / 2) * U @ staple
        F = 0.5 * (X - X.conj().T)
        F = F - np.trace(F) / 2 * np.eye(2)
        return F

    def _scalar_action(self):
        """Scalar field action with kinetic and potential terms."""
        # Kinetic: Σ_edges |φ_j - U_ij φ_i|²
        kinetic = 0.0
        for e_idx, (i, j) in enumerate(self.stella.edges):
            U_ij = self.gauge.links[e_idx][0, 0]  # Scalar is color singlet
            diff = self.scalar.phi[j] - U_ij * self.scalar.phi[i]
            kinetic += np.abs(diff) ** 2

        # Potential: Σ_v (m² |φ|² + λ |φ|⁴)
        phi_sq = np.abs(self.scalar.phi) ** 2
        potential = np.sum(self.m2 * phi_sq + self.lambda_4 * phi_sq ** 2)

        return kinetic + potential

    def _scalar_force(self):
        """Force on scalar field."""
        forces = np.zeros(8, dtype=complex)

        # Kinetic contribution
        for e_idx, (i, j) in enumerate(self.stella.edges):
            U_ij = self.gauge.links[e_idx][0, 0]
            diff = self.scalar.phi[j] - U_ij * self.scalar.phi[i]
            forces[i] += -np.conj(U_ij) * diff
            forces[j] += diff

        # Potential contribution
        forces += self.m2 * self.scalar.phi
        forces += 2 * self.lambda_4 * np.abs(self.scalar.phi) ** 2 * self.scalar.phi

        return forces

    def _total_action(self):
        return self.gauge.wilson_action(self.beta) + self._scalar_action()

    def _leapfrog(self, pi_gauge, pi_scalar):
        dt = self.dt

        for _ in range(self.n_leapfrog):
            # Half step momenta
            for e_idx in range(self.stella.n_edges):
                F = self._gauge_force(e_idx)
                pi_gauge[e_idx] = pi_gauge[e_idx] - 0.5 * dt * F

            F_scalar = self._scalar_force()
            pi_scalar = pi_scalar - 0.5 * dt * F_scalar

            # Full step positions
            for e_idx in range(self.stella.n_edges):
                U_old = self.gauge.links[e_idx]
                self.gauge.links[e_idx] = su2_project(su2_exp(dt * pi_gauge[e_idx]) @ U_old)

            self.scalar.phi = self.scalar.phi + dt * pi_scalar

            # Half step momenta
            for e_idx in range(self.stella.n_edges):
                F = self._gauge_force(e_idx)
                pi_gauge[e_idx] = pi_gauge[e_idx] - 0.5 * dt * F

            F_scalar = self._scalar_force()
            pi_scalar = pi_scalar - 0.5 * dt * F_scalar

        return pi_gauge, pi_scalar

    def trajectory(self):
        gauge_old = self.gauge.copy()
        scalar_old = self.scalar.copy()

        pi_gauge = [self._random_momentum_gauge() for _ in range(self.stella.n_edges)]
        pi_scalar = np.random.randn(8) + 1j * np.random.randn(8)

        K_old = self._kinetic_energy(pi_gauge, pi_scalar)
        S_old = self._total_action()
        H_old = K_old + S_old

        pi_gauge, pi_scalar = self._leapfrog(pi_gauge, pi_scalar)

        K_new = self._kinetic_energy(pi_gauge, pi_scalar)
        S_new = self._total_action()
        H_new = K_new + S_new

        dH = H_new - H_old

        if dH < 0 or np.random.rand() < np.exp(-min(dH, 700)):
            accept = True
            self.n_accepted += 1
        else:
            accept = False
            self.gauge = gauge_old
            self.scalar = scalar_old

        self.n_total += 1
        return accept

    def get_frame(self, traj: int) -> StellaFrame:
        # Separate plaquettes for T₊ and T₋
        T_plus_plaq = np.mean([self.gauge.plaquette_trace(f) for f in self.stella.T_plus_faces])
        T_minus_plaq = np.mean([self.gauge.plaquette_trace(f) for f in self.stella.T_minus_faces])

        return StellaFrame(
            trajectory=traj,
            avg_plaquette=self.gauge.average_plaquette(),
            T_plus_plaquette=T_plus_plaq,
            T_minus_plaquette=T_minus_plaq,
            edge_plaquettes=self.gauge.edge_plaquette_values(),
            scalar_magnitudes=self.scalar.magnitude_squared()
        )

    def run(self, n_traj: int, n_therm: int, start: str = 'hot',
            record_interval: int = 1, verbose: bool = True):

        if start == 'hot':
            self.gauge.hot_start()
            self.scalar.randomize(scale=0.5)
        else:
            self.gauge.cold_start()
            self.scalar.phi = 0.1 * np.ones(8, dtype=complex)

        self.frames = [self.get_frame(0)]

        if verbose:
            print(f"Stella Octangula HMC: β={self.beta}, start={start}")
            print(f"Initial ⟨P⟩ = {self.frames[0].avg_plaquette:.4f}")

        # Thermalization
        for i in range(n_therm):
            self.trajectory()
            if (i + 1) % record_interval == 0:
                self.frames.append(self.get_frame(i + 1))
            if verbose and (i + 1) % 25 == 0:
                plaq = self.gauge.average_plaquette()
                rate = self.n_accepted / self.n_total
                print(f"  Therm {i+1}/{n_therm}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Production
        prod_acc = 0
        prod_tot = 0
        for i in range(n_traj):
            acc = self.trajectory()
            prod_acc += int(acc)
            prod_tot += 1
            traj = n_therm + i + 1
            if (i + 1) % record_interval == 0:
                self.frames.append(self.get_frame(traj))
            if verbose and (i + 1) % 50 == 0:
                plaq = self.gauge.average_plaquette()
                rate = prod_acc / prod_tot
                print(f"  Prod {i+1}/{n_traj}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        if verbose:
            print(f"Recorded {len(self.frames)} frames")

        return self.frames


# ============================================================================
# VISUALIZATION
# ============================================================================

def create_stella_animation(frames: List[StellaFrame], stella: StellaOctangula,
                            title: str, output_html: str) -> go.Figure:
    """Create 3D animated visualization of the stella octangula."""

    vertices = stella.vertices

    # Vertex labels
    labels = [f'T₊[{i}]' for i in range(4)] + [f'T₋[{i}]' for i in range(4)]

    # Colors for tetrahedra
    T_plus_color = 'rgba(255, 100, 100, 0.9)'  # Red-ish
    T_minus_color = 'rgba(100, 100, 255, 0.9)'  # Blue-ish

    # Plaquette history
    plaq_history = [f.avg_plaquette for f in frames]
    traj_history = [f.trajectory for f in frames]
    T_plus_history = [f.T_plus_plaquette for f in frames]
    T_minus_history = [f.T_minus_plaquette for f in frames]

    # Running average
    window = 10
    running_avg = [np.mean(plaq_history[max(0, i-window+1):i+1]) for i in range(len(plaq_history))]

    # Equilibrium
    equil = np.mean(plaq_history[len(plaq_history)//2:])

    # Create figure with subplots
    fig = make_subplots(
        rows=2, cols=2,
        specs=[[{"type": "scene", "rowspan": 2}, {"type": "xy"}],
               [None, {"type": "xy"}]],
        subplot_titles=("Stella Octangula (T₊ ∪ T₋)", "Plaquette Evolution", "Scalar Field |φ|²"),
        column_widths=[0.6, 0.4],
        row_heights=[0.5, 0.5],
        horizontal_spacing=0.08,
        vertical_spacing=0.12
    )

    # Build animation frames
    animation_frames = []

    for frame_idx, frame in enumerate(frames):
        frame_data = []

        # --- 3D Stella Octangula ---

        # T₊ vertices
        T_plus_verts = go.Scatter3d(
            x=vertices[:4, 0], y=vertices[:4, 1], z=vertices[:4, 2],
            mode='markers+text',
            marker=dict(size=12, color='red', symbol='diamond',
                       line=dict(width=2, color='white')),
            text=labels[:4],
            textposition='top center',
            textfont=dict(size=10, color='white'),
            name='T₊ vertices',
            hovertemplate="<b>%{text}</b><br>|φ|²=%{customdata:.3f}<extra></extra>",
            customdata=frame.scalar_magnitudes[:4]
        )
        frame_data.append(T_plus_verts)

        # T₋ vertices
        T_minus_verts = go.Scatter3d(
            x=vertices[4:, 0], y=vertices[4:, 1], z=vertices[4:, 2],
            mode='markers+text',
            marker=dict(size=12, color='blue', symbol='diamond',
                       line=dict(width=2, color='white')),
            text=labels[4:],
            textposition='top center',
            textfont=dict(size=10, color='white'),
            name='T₋ vertices',
            hovertemplate="<b>%{text}</b><br>|φ|²=%{customdata:.3f}<extra></extra>",
            customdata=frame.scalar_magnitudes[4:]
        )
        frame_data.append(T_minus_verts)

        # T₊ edges (first 6)
        for e_idx in range(6):
            i, j = stella.edges[e_idx]
            plaq_val = np.clip(frame.edge_plaquettes[e_idx], 0, 1)

            # Color: dark red (disordered) -> bright red (ordered)
            intensity = int(100 + 155 * plaq_val)
            color = f'rgb({intensity}, {int(50 + 50*plaq_val)}, {int(50 + 50*plaq_val)})'
            width = 4 + 6 * plaq_val

            edge_trace = go.Scatter3d(
                x=[vertices[i, 0], vertices[j, 0]],
                y=[vertices[i, 1], vertices[j, 1]],
                z=[vertices[i, 2], vertices[j, 2]],
                mode='lines',
                line=dict(color=color, width=width),
                name=f'T₊ edge {i}-{j}',
                showlegend=False,
                hovertemplate=f"T₊ edge ({i},{j})<br>Plaq={plaq_val:.3f}<extra></extra>"
            )
            frame_data.append(edge_trace)

        # T₋ edges (last 6)
        for e_idx in range(6, 12):
            i, j = stella.edges[e_idx]
            plaq_val = np.clip(frame.edge_plaquettes[e_idx], 0, 1)

            # Color: dark blue (disordered) -> bright blue (ordered)
            intensity = int(100 + 155 * plaq_val)
            color = f'rgb({int(50 + 50*plaq_val)}, {int(50 + 50*plaq_val)}, {intensity})'
            width = 4 + 6 * plaq_val

            edge_trace = go.Scatter3d(
                x=[vertices[i, 0], vertices[j, 0]],
                y=[vertices[i, 1], vertices[j, 1]],
                z=[vertices[i, 2], vertices[j, 2]],
                mode='lines',
                line=dict(color=color, width=width),
                name=f'T₋ edge {i}-{j}',
                showlegend=False,
                hovertemplate=f"T₋ edge ({i},{j})<br>Plaq={plaq_val:.3f}<extra></extra>"
            )
            frame_data.append(edge_trace)

        # --- Plaquette evolution ---

        # Raw
        plaq_raw = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=plaq_history[:frame_idx+1],
            mode='lines',
            line=dict(color='rgba(200,200,200,0.3)', width=1),
            name='Raw', showlegend=False
        )
        frame_data.append(plaq_raw)

        # T₊ and T₋ separately
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

        # Running average
        avg_trace = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=running_avg[:frame_idx+1],
            mode='lines',
            line=dict(color='yellow', width=3),
            name='Average'
        )
        frame_data.append(avg_trace)

        # Current point
        current = go.Scatter(
            x=[traj_history[frame_idx]],
            y=[plaq_history[frame_idx]],
            mode='markers',
            marker=dict(size=10, color='white', symbol='circle'),
            showlegend=False
        )
        frame_data.append(current)

        # Equilibrium
        equil_line = go.Scatter(
            x=[0, max(traj_history)],
            y=[equil, equil],
            mode='lines',
            line=dict(color='lime', width=2, dash='dot'),
            name=f'Eq: {equil:.3f}'
        )
        frame_data.append(equil_line)

        # --- Scalar field bar chart ---
        scalar_bar = go.Bar(
            x=labels,
            y=frame.scalar_magnitudes,
            marker=dict(
                color=['red']*4 + ['blue']*4,
                opacity=0.7
            ),
            name='|φ|²'
        )
        frame_data.append(scalar_bar)

        animation_frames.append(go.Frame(data=frame_data, name=str(frame_idx)))

    # Add initial traces
    fig.add_traces(animation_frames[0].data)
    fig.frames = animation_frames

    # Layout
    fig.update_layout(
        title=dict(
            text=f"<b>{title}</b><br><sup>Two interpenetrating tetrahedra: T₊ (red) and T₋ (blue)</sup>",
            x=0.5, font=dict(size=18)
        ),
        scene=dict(
            xaxis=dict(title='X', range=[-1.5, 1.5], showbackground=True,
                      backgroundcolor='rgb(15,15,25)', gridcolor='rgba(100,100,100,0.2)'),
            yaxis=dict(title='Y', range=[-1.5, 1.5], showbackground=True,
                      backgroundcolor='rgb(15,15,25)', gridcolor='rgba(100,100,100,0.2)'),
            zaxis=dict(title='Z', range=[-1.5, 1.5], showbackground=True,
                      backgroundcolor='rgb(15,15,25)', gridcolor='rgba(100,100,100,0.2)'),
            camera=dict(eye=dict(x=2.0, y=2.0, z=1.5)),
            aspectmode='cube'
        ),
        xaxis=dict(title='Trajectory', domain=[0.62, 1.0], gridcolor='rgba(100,100,100,0.3)'),
        yaxis=dict(title='⟨P⟩', range=[0, 1.05], domain=[0.55, 1.0], gridcolor='rgba(100,100,100,0.3)'),
        xaxis2=dict(title='Vertex', domain=[0.62, 1.0]),
        yaxis2=dict(title='|φ|²', domain=[0, 0.4]),
        paper_bgcolor='rgb(10,10,20)',
        plot_bgcolor='rgb(20,20,35)',
        font=dict(color='white', size=11),
        showlegend=True,
        legend=dict(x=0.65, y=0.52, bgcolor='rgba(0,0,0,0.5)', font=dict(size=10)),
        updatemenus=[dict(
            type='buttons', showactive=False, y=1.12, x=0.5, xanchor='center',
            buttons=[
                dict(label='▶ Play', method='animate',
                     args=[None, dict(frame=dict(duration=80, redraw=True),
                                     fromcurrent=True, mode='immediate')]),
                dict(label='⏸ Pause', method='animate',
                     args=[[None], dict(frame=dict(duration=0, redraw=False),
                                       mode='immediate')])
            ]
        )],
        sliders=[dict(
            active=0, yanchor='top', xanchor='left',
            currentvalue=dict(prefix='Trajectory: ', visible=True, font=dict(size=12)),
            pad=dict(b=10, t=50), len=0.9, x=0.05, y=0,
            steps=[dict(args=[[str(i)], dict(frame=dict(duration=80, redraw=True), mode='immediate')],
                       label=str(frames[i].trajectory), method='animate')
                   for i in range(0, len(frames), max(1, len(frames)//60))]
        )]
    )

    fig.write_html(output_html, include_plotlyjs=True, full_html=True)
    print(f"Saved: {output_html}")

    return fig


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 60)
    print("STELLA OCTANGULA HMC SIMULATION")
    print("Two Interpenetrating Tetrahedra (T₊ ∪ T₋)")
    print("=" * 60)

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    # Hot start
    print("\n" + "-" * 40)
    print("HOT START")
    print("-" * 40)
    hmc_hot = StellaHMC(beta=2.2, m2=-0.15, lambda_4=0.125,
                        n_leapfrog=15, dt=0.08)
    frames_hot = hmc_hot.run(n_traj=300, n_therm=100, start='hot',
                             record_interval=2, verbose=True)

    print("\nCreating animation...")
    create_stella_animation(frames_hot, hmc_hot.stella,
                           "Stella Octangula: Hot Start",
                           str(output_dir / "stella_octangula_hot.html"))

    # Cold start
    print("\n" + "-" * 40)
    print("COLD START")
    print("-" * 40)
    hmc_cold = StellaHMC(beta=2.2, m2=-0.15, lambda_4=0.125,
                         n_leapfrog=15, dt=0.08)
    frames_cold = hmc_cold.run(n_traj=300, n_therm=100, start='cold',
                               record_interval=2, verbose=True)

    print("\nCreating animation...")
    create_stella_animation(frames_cold, hmc_cold.stella,
                           "Stella Octangula: Cold Start",
                           str(output_dir / "stella_octangula_cold.html"))

    # Summary
    print("\n" + "=" * 60)
    print("COMPLETE")
    print("=" * 60)
    equil_hot = np.mean([f.avg_plaquette for f in frames_hot[len(frames_hot)//2:]])
    equil_cold = np.mean([f.avg_plaquette for f in frames_cold[len(frames_cold)//2:]])
    print(f"\nHot start equilibrium:  ⟨P⟩ = {equil_hot:.4f}")
    print(f"Cold start equilibrium: ⟨P⟩ = {equil_cold:.4f}")
    print(f"\nOutput files in {output_dir}/:")
    print("  - stella_octangula_hot.html")
    print("  - stella_octangula_cold.html")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Stella Octangula HMC Trajectory Animation
==========================================

Visualizes the Hybrid Monte Carlo trajectory evolution on the K₄ tetrahedron
lattice using Plotly for interactive 3D animation.

Shows:
    1. K₄ tetrahedron with gauge links colored by plaquette values
    2. Vertices sized/colored by scalar field magnitude |φ|²
    3. Evolution through HMC trajectories (thermalization → equilibrium)

Target: Proposition 0.0.27 - Visual verification of field dynamics

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-03
"""

import numpy as np
from scipy import linalg
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from pathlib import Path
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import json

# ============================================================================
# GEOMETRIC PARAMETERS
# ============================================================================

LAMBDA_HIGGS = 1 / 8          # Higgs quartic coupling
C_SW = 2 / 3                  # Clover coefficient
R_WILSON = 3 / 2              # Wilson parameter


# ============================================================================
# K₄ LATTICE STRUCTURE
# ============================================================================

class K4Lattice:
    """Complete graph K₄ representing a single tetrahedron."""

    def __init__(self):
        # Vertex positions - regular tetrahedron inscribed in unit sphere
        self.vertices = np.array([
            [1, 1, 1],
            [1, -1, -1],
            [-1, 1, -1],
            [-1, -1, 1]
        ], dtype=float) / np.sqrt(3)

        # Edge list
        self.edges = [(i, j) for i in range(4) for j in range(i + 1, 4)]
        self.n_edges = len(self.edges)

        # Face list (triangles)
        self.faces = [
            (0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)
        ]

        # Edge to index mapping
        self.edge_to_idx = {e: i for i, e in enumerate(self.edges)}

    def edge_index(self, i: int, j: int) -> Tuple[int, int]:
        """Get canonical edge index and sign."""
        if i < j:
            return self.edge_to_idx[(i, j)], 1
        else:
            return self.edge_to_idx[(j, i)], -1


# ============================================================================
# GAUGE FIELD
# ============================================================================

class GaugeField:
    """SU(N) gauge field on K₄ edges."""

    def __init__(self, lattice: K4Lattice, n_colors: int = 2):
        self.lattice = lattice
        self.n_colors = n_colors
        self.links = [np.eye(n_colors, dtype=complex) for _ in range(lattice.n_edges)]

    def get_link(self, i: int, j: int) -> np.ndarray:
        idx, sign = self.lattice.edge_index(i, j)
        return self.links[idx].copy() if sign == 1 else self.links[idx].conj().T

    def set_link(self, i: int, j: int, U: np.ndarray):
        idx, sign = self.lattice.edge_index(i, j)
        self.links[idx] = U.copy() if sign == 1 else U.conj().T

    def plaquette_trace(self, face: Tuple[int, int, int]) -> float:
        """Compute (1/N_c) Re Tr(P_f)."""
        i, j, k = face
        P = self.get_link(i, j) @ self.get_link(j, k) @ self.get_link(k, i)
        return np.real(np.trace(P)) / self.n_colors

    def average_plaquette(self) -> float:
        return sum(self.plaquette_trace(f) for f in self.lattice.faces) / len(self.lattice.faces)

    def gauge_action(self, beta: float) -> float:
        return beta * sum(1.0 - self.plaquette_trace(f) for f in self.lattice.faces)

    def randomize(self, epsilon: float = 0.1):
        for idx in range(self.lattice.n_edges):
            self.links[idx] = self._random_su_n(epsilon)

    def _random_su_n(self, epsilon: float) -> np.ndarray:
        n = self.n_colors
        A = epsilon * (np.random.randn(n, n) + 1j * np.random.randn(n, n))
        A = 0.5 * (A - A.conj().T)
        A = A - np.trace(A) / n * np.eye(n)
        U = linalg.expm(A)
        return self._project_to_sun(U)

    def _project_to_sun(self, U: np.ndarray) -> np.ndarray:
        u, s, vh = np.linalg.svd(U)
        U = u @ vh
        det = np.linalg.det(U)
        return U / (det ** (1.0 / self.n_colors))

    def copy(self) -> 'GaugeField':
        new = GaugeField(self.lattice, self.n_colors)
        new.links = [link.copy() for link in self.links]
        return new


# ============================================================================
# SCALAR FIELD
# ============================================================================

class ScalarField:
    """Complex scalar field on K₄ vertices."""

    def __init__(self, lattice: K4Lattice):
        self.lattice = lattice
        self.phi = np.zeros(4, dtype=complex)

    def randomize(self, scale: float = 1.0):
        self.phi = scale * (np.random.randn(4) + 1j * np.random.randn(4))

    def kinetic_term(self, gauge: GaugeField) -> float:
        total = 0.0
        for (i, j) in self.lattice.edges:
            U_ij = gauge.get_link(i, j)[0, 0]
            diff = self.phi[j] - U_ij * self.phi[i]
            total += np.abs(diff)**2
        return total

    def potential_term(self, m2: float, lambda_4: float) -> float:
        phi_sq = np.abs(self.phi)**2
        return np.sum(m2 * phi_sq + lambda_4 * phi_sq**2)

    def scalar_action(self, gauge: GaugeField, m2: float, lambda_4: float) -> float:
        return self.kinetic_term(gauge) + self.potential_term(m2, lambda_4)

    def copy(self) -> 'ScalarField':
        new = ScalarField(self.lattice)
        new.phi = self.phi.copy()
        return new


# ============================================================================
# HMC WITH TRAJECTORY RECORDING
# ============================================================================

@dataclass
class TrajectoryFrame:
    """Single frame of trajectory data for visualization."""
    trajectory_idx: int
    plaquette: float
    scalar_magnitudes: np.ndarray  # |φ|² at each vertex
    scalar_phases: np.ndarray      # arg(φ) at each vertex
    edge_plaquettes: np.ndarray    # Plaquette value for edges
    gauge_action: float
    scalar_action: float
    accepted: bool = True


class HMCWithRecording:
    """HMC simulation that records trajectory data for animation."""

    def __init__(self, n_colors: int = 2, beta: float = 2.5,
                 m2: float = -0.1, lambda_scalar: float = LAMBDA_HIGGS):
        self.lattice = K4Lattice()
        self.n_colors = n_colors
        self.beta = beta
        self.m2 = m2
        self.lambda_scalar = lambda_scalar

        self.gauge = GaugeField(self.lattice, n_colors)
        self.scalar = ScalarField(self.lattice)

        # Recording
        self.frames: List[TrajectoryFrame] = []
        self.n_accepted = 0
        self.n_total = 0

    def _compute_edge_plaquettes(self) -> np.ndarray:
        """Compute effective plaquette value for each edge (average of adjacent faces)."""
        edge_plaq = np.zeros(self.lattice.n_edges)

        for e_idx, (i, j) in enumerate(self.lattice.edges):
            # Find faces containing this edge
            face_values = []
            for face in self.lattice.faces:
                if i in face and j in face:
                    face_values.append(self.gauge.plaquette_trace(face))
            edge_plaq[e_idx] = np.mean(face_values) if face_values else 0.5

        return edge_plaq

    def record_frame(self, traj_idx: int, accepted: bool = True):
        """Record current configuration as a frame."""
        frame = TrajectoryFrame(
            trajectory_idx=traj_idx,
            plaquette=self.gauge.average_plaquette(),
            scalar_magnitudes=np.abs(self.scalar.phi)**2,
            scalar_phases=np.angle(self.scalar.phi),
            edge_plaquettes=self._compute_edge_plaquettes(),
            gauge_action=self.gauge.gauge_action(self.beta),
            scalar_action=self.scalar.scalar_action(self.gauge, self.m2, self.lambda_scalar),
            accepted=accepted
        )
        self.frames.append(frame)

    def _gauge_force(self) -> List[np.ndarray]:
        """Compute force on gauge links."""
        forces = []
        for e_idx, (i, j) in enumerate(self.lattice.edges):
            staple = np.zeros((self.n_colors, self.n_colors), dtype=complex)
            for face in self.lattice.faces:
                if i in face and j in face:
                    k = [v for v in face if v != i and v != j][0]
                    staple += self.gauge.get_link(j, k) @ self.gauge.get_link(k, i)

            U_ij = self.gauge.get_link(i, j)
            F = (self.beta / self.n_colors) * (U_ij @ staple - staple.conj().T @ U_ij.conj().T)
            F = 0.5 * (F - F.conj().T)
            F = F - np.trace(F) / self.n_colors * np.eye(self.n_colors)
            forces.append(F)
        return forces

    def _scalar_force(self) -> np.ndarray:
        """Compute force on scalar field."""
        forces = np.zeros(4, dtype=complex)
        for (i, j) in self.lattice.edges:
            U_ij = self.gauge.get_link(i, j)[0, 0]
            forces[i] += -np.conj(U_ij) * (self.scalar.phi[j] - U_ij * self.scalar.phi[i])
            forces[j] += self.scalar.phi[j] - U_ij * self.scalar.phi[i]

        forces += self.m2 * self.scalar.phi
        forces += 2 * self.lambda_scalar * np.abs(self.scalar.phi)**2 * self.scalar.phi
        return forces

    def total_action(self) -> float:
        return (self.gauge.gauge_action(self.beta) +
                self.scalar.scalar_action(self.gauge, self.m2, self.lambda_scalar))

    def kinetic_energy(self, pi_gauge: List[np.ndarray], pi_scalar: np.ndarray) -> float:
        K = sum(0.5 * np.real(np.trace(p.conj().T @ p)) for p in pi_gauge)
        K += 0.5 * np.sum(np.abs(pi_scalar)**2)
        return K

    def hmc_trajectory(self, n_leapfrog: int = 30, dt: float = 0.035) -> bool:
        """Execute one HMC trajectory."""
        gauge_old = self.gauge.copy()
        scalar_old = self.scalar.copy()

        # Random momenta
        pi_gauge = []
        for _ in range(self.lattice.n_edges):
            A = np.random.randn(self.n_colors, self.n_colors) + 1j * np.random.randn(self.n_colors, self.n_colors)
            A = 0.5 * (A - A.conj().T)
            A = A - np.trace(A) / self.n_colors * np.eye(self.n_colors)
            pi_gauge.append(A)
        pi_scalar = np.random.randn(4) + 1j * np.random.randn(4)

        H_old = self.total_action() + self.kinetic_energy(pi_gauge, pi_scalar)

        # Leapfrog integration
        for _ in range(n_leapfrog):
            # Half step momenta
            F_gauge = self._gauge_force()
            F_scalar = self._scalar_force()
            pi_gauge = [p - 0.5 * dt * f for p, f in zip(pi_gauge, F_gauge)]
            pi_scalar = pi_scalar - 0.5 * dt * F_scalar

            # Full step positions
            for e_idx in range(self.lattice.n_edges):
                U = self.gauge.links[e_idx]
                self.gauge.links[e_idx] = linalg.expm(dt * pi_gauge[e_idx]) @ U
                self.gauge.links[e_idx] = self.gauge._project_to_sun(self.gauge.links[e_idx])
            self.scalar.phi = self.scalar.phi + dt * pi_scalar

            # Half step momenta
            F_gauge = self._gauge_force()
            F_scalar = self._scalar_force()
            pi_gauge = [p - 0.5 * dt * f for p, f in zip(pi_gauge, F_gauge)]
            pi_scalar = pi_scalar - 0.5 * dt * F_scalar

        H_new = self.total_action() + self.kinetic_energy(pi_gauge, pi_scalar)

        # Metropolis
        dH = H_new - H_old
        accept = (dH < 0) or (np.random.rand() < np.exp(-dH))

        if accept:
            self.n_accepted += 1
        else:
            self.gauge = gauge_old
            self.scalar = scalar_old

        self.n_total += 1
        return accept

    def run_simulation(self, n_trajectories: int = 200,
                       n_thermalization: int = 50,
                       record_interval: int = 1,
                       verbose: bool = True) -> List[TrajectoryFrame]:
        """Run simulation and record frames."""

        # Initialize random
        self.gauge.randomize(epsilon=0.8)
        self.scalar.randomize(scale=1.0)

        if verbose:
            print(f"Running {n_thermalization} thermalization + {n_trajectories} production trajectories...")

        # Record initial state
        self.record_frame(0)

        # Thermalization
        for i in range(n_thermalization):
            accepted = self.hmc_trajectory()
            if (i + 1) % record_interval == 0:
                self.record_frame(i + 1, accepted)

            if verbose and (i + 1) % 50 == 0:
                plaq = self.gauge.average_plaquette()
                rate = self.n_accepted / self.n_total
                print(f"  Thermalization {i+1}/{n_thermalization}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Reset counters for production
        self.n_accepted = 0
        self.n_total = 0

        # Production
        for i in range(n_trajectories):
            accepted = self.hmc_trajectory()
            traj_num = n_thermalization + i + 1
            if (i + 1) % record_interval == 0:
                self.record_frame(traj_num, accepted)

            if verbose and (i + 1) % 100 == 0:
                plaq = self.gauge.average_plaquette()
                rate = self.n_accepted / self.n_total
                print(f"  Production {i+1}/{n_trajectories}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        if verbose:
            print(f"Recorded {len(self.frames)} frames")

        return self.frames


# ============================================================================
# PLOTLY ANIMATION
# ============================================================================

def create_tetrahedron_animation(frames: List[TrajectoryFrame],
                                  title: str = "Stella Octangula HMC Evolution",
                                  output_html: Optional[str] = None) -> go.Figure:
    """
    Create interactive Plotly animation of HMC trajectory evolution.

    Parameters
    ----------
    frames : List[TrajectoryFrame]
        Recorded trajectory frames from simulation
    title : str
        Plot title
    output_html : str, optional
        Path to save HTML file

    Returns
    -------
    go.Figure
        Plotly figure object
    """

    lattice = K4Lattice()
    vertices = lattice.vertices

    # Vertex labels
    vertex_labels = ['v₀', 'v₁', 'v₂', 'v₃']

    # Color scales
    edge_colorscale = 'RdYlGn'  # Red (disordered) -> Green (ordered)
    vertex_colorscale = 'Plasma'

    # Create figure with subplots
    fig = make_subplots(
        rows=2, cols=2,
        specs=[
            [{"type": "scene", "rowspan": 2}, {"type": "xy"}],
            [None, {"type": "xy"}]
        ],
        subplot_titles=("3D Tetrahedron", "Plaquette Evolution", "Scalar Field |φ|²"),
        column_widths=[0.6, 0.4],
        row_heights=[0.5, 0.5],
        horizontal_spacing=0.1,
        vertical_spacing=0.12
    )

    # Pre-compute edge midpoints for edge coloring
    edge_midpoints = []
    for (i, j) in lattice.edges:
        mid = (vertices[i] + vertices[j]) / 2
        edge_midpoints.append(mid)
    edge_midpoints = np.array(edge_midpoints)

    # Compute equilibrium plaquette from production frames (after thermalization)
    # Assuming thermalization ends at trajectory 200
    production_frames = [f for f in frames if f.trajectory_idx > 200]
    if production_frames:
        equilibrium_plaq = np.mean([f.plaquette for f in production_frames])
    else:
        equilibrium_plaq = np.mean([f.plaquette for f in frames])

    # Build animation frames
    animation_frames = []

    for frame_idx, frame in enumerate(frames):
        frame_data = []

        # --- 3D Tetrahedron ---

        # Vertices (scatter3d)
        scalar_mags = frame.scalar_magnitudes
        max_mag = max(np.max(scalar_mags), 0.1)
        vertex_sizes = 15 + 25 * scalar_mags / max_mag

        vertex_trace = go.Scatter3d(
            x=vertices[:, 0],
            y=vertices[:, 1],
            z=vertices[:, 2],
            mode='markers+text',
            marker=dict(
                size=vertex_sizes,
                color=scalar_mags,
                colorscale=vertex_colorscale,
                cmin=0,
                cmax=max(2, np.max([f.scalar_magnitudes.max() for f in frames])),
                colorbar=dict(
                    title="|φ|²",
                    x=0.45,
                    len=0.4,
                    y=0.8
                ),
                line=dict(width=2, color='white')
            ),
            text=vertex_labels,
            textposition='top center',
            textfont=dict(size=12, color='white'),
            hovertemplate="<b>%{text}</b><br>|φ|² = %{marker.color:.3f}<extra></extra>",
            name='Vertices'
        )
        frame_data.append(vertex_trace)

        # Edges as individual line segments with colors
        edge_plaq = frame.edge_plaquettes

        for e_idx, (i, j) in enumerate(lattice.edges):
            # Color based on plaquette (0=disordered/red, 1=ordered/green)
            plaq_val = np.clip(edge_plaq[e_idx], 0, 1)  # Ensure in [0,1]

            # Map to RGB: red (disordered) -> yellow -> green (ordered)
            if plaq_val < 0.5:
                r = 255
                g = int(255 * (plaq_val / 0.5))
                b = 50
            else:
                r = int(255 * (1 - (plaq_val - 0.5) / 0.5))
                g = 255
                b = 50

            # Clamp RGB values
            r = max(0, min(255, r))
            g = max(0, min(255, g))
            b = max(0, min(255, b))

            edge_color = f'rgb({r},{g},{b})'

            # Line width based on plaquette
            width = 3 + 5 * plaq_val

            edge_trace = go.Scatter3d(
                x=[vertices[i, 0], vertices[j, 0]],
                y=[vertices[i, 1], vertices[j, 1]],
                z=[vertices[i, 2], vertices[j, 2]],
                mode='lines',
                line=dict(color=edge_color, width=width),
                hovertemplate=f"Edge ({i},{j})<br>Plaq = {plaq_val:.3f}<extra></extra>",
                showlegend=False
            )
            frame_data.append(edge_trace)

        # --- Time series plots ---

        # Plaquette history up to current frame
        traj_indices = [f.trajectory_idx for f in frames[:frame_idx + 1]]
        plaq_values = [f.plaquette for f in frames[:frame_idx + 1]]

        # Compute running average (window of 20 frames)
        window = 20
        running_avg = []
        for k in range(len(plaq_values)):
            start = max(0, k - window + 1)
            running_avg.append(np.mean(plaq_values[start:k+1]))

        plaq_trace = go.Scatter(
            x=traj_indices,
            y=plaq_values,
            mode='lines',
            line=dict(color='rgba(100,150,255,0.4)', width=1),
            name='⟨P⟩ raw',
            xaxis='x2',
            yaxis='y2'
        )
        frame_data.append(plaq_trace)

        # Running average trace
        avg_trace = go.Scatter(
            x=traj_indices,
            y=running_avg,
            mode='lines',
            line=dict(color='yellow', width=3),
            name='⟨P⟩ avg',
            xaxis='x2',
            yaxis='y2'
        )
        frame_data.append(avg_trace)

        # Current point marker
        current_plaq = go.Scatter(
            x=[frame.trajectory_idx],
            y=[frame.plaquette],
            mode='markers',
            marker=dict(size=10, color='red', symbol='circle'),
            name='Current',
            xaxis='x2',
            yaxis='y2',
            showlegend=False
        )
        frame_data.append(current_plaq)

        # Thermalization boundary (vertical line at trajectory 200)
        therm_line = go.Scatter(
            x=[200, 200],
            y=[0, 1.05],
            mode='lines',
            line=dict(color='rgba(255,100,100,0.5)', width=2, dash='dash'),
            name='Therm end',
            xaxis='x2',
            yaxis='y2',
            showlegend=False
        )
        frame_data.append(therm_line)

        # Equilibrium reference line (horizontal)
        equil_line = go.Scatter(
            x=[0, max(f.trajectory_idx for f in frames)],
            y=[equilibrium_plaq, equilibrium_plaq],
            mode='lines',
            line=dict(color='rgba(100,255,100,0.6)', width=2, dash='dot'),
            name=f'Equil: {equilibrium_plaq:.3f}',
            xaxis='x2',
            yaxis='y2',
            showlegend=False
        )
        frame_data.append(equil_line)

        # Scalar field bar chart
        scalar_bar = go.Bar(
            x=vertex_labels,
            y=frame.scalar_magnitudes,
            marker=dict(
                color=frame.scalar_magnitudes,
                colorscale=vertex_colorscale,
                cmin=0,
                cmax=max(2, np.max([f.scalar_magnitudes.max() for f in frames]))
            ),
            name='|φ|²',
            xaxis='x3',
            yaxis='y3'
        )
        frame_data.append(scalar_bar)

        animation_frames.append(go.Frame(
            data=frame_data,
            name=str(frame_idx),
            traces=list(range(len(frame_data)))
        ))

    # Initial frame data
    fig.add_traces(animation_frames[0].data)

    # Update layout
    fig.update_layout(
        title=dict(
            text=f"<b>{title}</b><br><sup>Gauge links colored by plaquette (red→green = disordered→ordered)</sup>",
            x=0.5,
            font=dict(size=18)
        ),
        scene=dict(
            xaxis=dict(title='X', range=[-1.2, 1.2], showbackground=True, backgroundcolor='rgb(20,20,30)'),
            yaxis=dict(title='Y', range=[-1.2, 1.2], showbackground=True, backgroundcolor='rgb(20,20,30)'),
            zaxis=dict(title='Z', range=[-1.2, 1.2], showbackground=True, backgroundcolor='rgb(20,20,30)'),
            camera=dict(
                eye=dict(x=1.5, y=1.5, z=1.2),
                up=dict(x=0, y=0, z=1)
            ),
            aspectmode='cube'
        ),
        xaxis2=dict(title='Trajectory', domain=[0.65, 1.0]),
        yaxis2=dict(title='⟨Plaquette⟩', range=[0, 1.05], domain=[0.55, 1.0]),
        xaxis3=dict(title='Vertex', domain=[0.65, 1.0]),
        yaxis3=dict(title='|φ|²', range=[0, max(3, np.max([f.scalar_magnitudes.max() for f in frames]) * 1.1)], domain=[0, 0.4]),
        paper_bgcolor='rgb(10,10,20)',
        plot_bgcolor='rgb(30,30,40)',
        font=dict(color='white'),
        showlegend=False,
        updatemenus=[
            dict(
                type='buttons',
                showactive=False,
                y=0,
                x=0.1,
                xanchor='right',
                yanchor='top',
                buttons=[
                    dict(
                        label='▶ Play',
                        method='animate',
                        args=[
                            None,
                            dict(
                                frame=dict(duration=100, redraw=True),
                                fromcurrent=True,
                                mode='immediate',
                                transition=dict(duration=50)
                            )
                        ]
                    ),
                    dict(
                        label='⏸ Pause',
                        method='animate',
                        args=[
                            [None],
                            dict(
                                frame=dict(duration=0, redraw=False),
                                mode='immediate',
                                transition=dict(duration=0)
                            )
                        ]
                    )
                ]
            )
        ],
        sliders=[
            dict(
                active=0,
                yanchor='top',
                xanchor='left',
                currentvalue=dict(
                    font=dict(size=14),
                    prefix='Trajectory: ',
                    visible=True,
                    xanchor='right'
                ),
                transition=dict(duration=50),
                pad=dict(b=10, t=50),
                len=0.9,
                x=0.05,
                y=0,
                steps=[
                    dict(
                        args=[
                            [str(i)],
                            dict(
                                frame=dict(duration=100, redraw=True),
                                mode='immediate',
                                transition=dict(duration=50)
                            )
                        ],
                        label=str(frames[i].trajectory_idx),
                        method='animate'
                    )
                    for i in range(len(frames))
                ]
            )
        ]
    )

    # Add frames to figure
    fig.frames = animation_frames

    # Save if requested
    if output_html:
        fig.write_html(output_html, include_plotlyjs=True, full_html=True)
        print(f"Animation saved to: {output_html}")

    return fig


def create_phase_space_animation(frames: List[TrajectoryFrame],
                                  output_html: Optional[str] = None) -> go.Figure:
    """
    Create animation showing phase space evolution (plaquette vs scalar VEV).
    """

    plaquettes = [f.plaquette for f in frames]
    scalar_vevs = [np.mean(f.scalar_magnitudes) for f in frames]
    traj_indices = [f.trajectory_idx for f in frames]

    fig = go.Figure()

    # Full trajectory path (faded)
    fig.add_trace(go.Scatter(
        x=plaquettes,
        y=scalar_vevs,
        mode='lines',
        line=dict(color='rgba(100,100,255,0.3)', width=1),
        name='Full trajectory',
        hoverinfo='skip'
    ))

    # Animation frames
    animation_frames = []
    for i in range(len(frames)):
        # Path up to current point
        path_trace = go.Scatter(
            x=plaquettes[:i+1],
            y=scalar_vevs[:i+1],
            mode='lines',
            line=dict(color='royalblue', width=2),
            name='Path'
        )

        # Current point
        current_trace = go.Scatter(
            x=[plaquettes[i]],
            y=[scalar_vevs[i]],
            mode='markers',
            marker=dict(size=15, color='red', symbol='circle',
                       line=dict(width=2, color='white')),
            name='Current',
            hovertemplate=f"Traj {traj_indices[i]}<br>⟨P⟩={plaquettes[i]:.3f}<br>⟨|φ|²⟩={scalar_vevs[i]:.3f}<extra></extra>"
        )

        animation_frames.append(go.Frame(
            data=[path_trace, current_trace],
            name=str(i)
        ))

    fig.frames = animation_frames

    # Add initial traces
    fig.add_trace(go.Scatter(
        x=plaquettes[:1],
        y=scalar_vevs[:1],
        mode='lines',
        line=dict(color='royalblue', width=2),
        name='Path'
    ))
    fig.add_trace(go.Scatter(
        x=[plaquettes[0]],
        y=[scalar_vevs[0]],
        mode='markers',
        marker=dict(size=15, color='red', symbol='circle',
                   line=dict(width=2, color='white')),
        name='Current'
    ))

    fig.update_layout(
        title=dict(
            text="<b>Phase Space Evolution</b><br><sup>Thermalization → Equilibrium</sup>",
            x=0.5,
            font=dict(size=18)
        ),
        xaxis=dict(title='Average Plaquette ⟨P⟩', range=[0, 1.05]),
        yaxis=dict(title='Scalar VEV ⟨|φ|²⟩', range=[0, max(scalar_vevs) * 1.2]),
        paper_bgcolor='rgb(10,10,20)',
        plot_bgcolor='rgb(30,30,40)',
        font=dict(color='white'),
        showlegend=False,
        updatemenus=[
            dict(
                type='buttons',
                showactive=False,
                y=1.15,
                x=0.5,
                xanchor='center',
                buttons=[
                    dict(label='▶ Play', method='animate',
                         args=[None, dict(frame=dict(duration=80, redraw=True),
                                         fromcurrent=True, mode='immediate')]),
                    dict(label='⏸ Pause', method='animate',
                         args=[[None], dict(frame=dict(duration=0, redraw=False),
                                           mode='immediate')])
                ]
            )
        ],
        sliders=[
            dict(
                active=0,
                currentvalue=dict(prefix='Frame: ', visible=True),
                pad=dict(t=50),
                steps=[
                    dict(args=[[str(i)], dict(frame=dict(duration=80, redraw=True),
                                              mode='immediate')],
                         label=str(i), method='animate')
                    for i in range(len(frames))
                ]
            )
        ]
    )

    if output_html:
        fig.write_html(output_html, include_plotlyjs=True, full_html=True)
        print(f"Phase space animation saved to: {output_html}")

    return fig


# ============================================================================
# MAIN
# ============================================================================

def main():
    """Run simulation and create animations."""

    print("=" * 70)
    print("STELLA OCTANGULA HMC TRAJECTORY ANIMATION")
    print("=" * 70)

    # Run simulation with longer thermalization and production
    hmc = HMCWithRecording(
        n_colors=2,
        beta=2.2,         # Slightly lower beta for faster thermalization
        m2=-0.2,          # More negative for clearer symmetry breaking
        lambda_scalar=LAMBDA_HIGGS
    )

    frames = hmc.run_simulation(
        n_trajectories=800,      # Much longer production run
        n_thermalization=200,    # Longer thermalization
        record_interval=2,       # Record every 2nd trajectory to keep file size reasonable
        verbose=True
    )

    # Output directory
    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    # Create main animation
    print("\nCreating 3D tetrahedron animation...")
    fig_3d = create_tetrahedron_animation(
        frames,
        title="Stella Octangula HMC Evolution",
        output_html=str(output_dir / "stella_hmc_animation.html")
    )

    # Create phase space animation
    print("Creating phase space animation...")
    fig_phase = create_phase_space_animation(
        frames,
        output_html=str(output_dir / "stella_phase_space.html")
    )

    # Summary
    print("\n" + "=" * 70)
    print("ANIMATION COMPLETE")
    print("=" * 70)
    print(f"\nOutputs saved to: {output_dir}/")
    print("  - stella_hmc_animation.html  (3D tetrahedron)")
    print("  - stella_phase_space.html    (phase space)")
    print("\nOpen the HTML files in a browser to view the interactive animations.")

    # Show in browser if possible
    try:
        fig_3d.show()
    except Exception:
        print("(Could not open browser automatically)")

    return frames, fig_3d, fig_phase


if __name__ == "__main__":
    main()

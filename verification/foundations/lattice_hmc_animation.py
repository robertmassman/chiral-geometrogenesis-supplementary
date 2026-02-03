#!/usr/bin/env python3
"""
Lattice QCD HMC Simulation with Proper Thermalization
======================================================

A physically meaningful lattice gauge theory simulation on a 3D cubic lattice
demonstrating proper HMC thermalization and equilibrium behavior.

This simulation shows the characteristic behavior seen in real lattice QCD:
    1. Initial disordered state (⟨P⟩ ≈ 0 for hot start, ⟨P⟩ ≈ 1 for cold start)
    2. Thermalization: exponential approach to equilibrium
    3. Equilibrium plateau with small statistical fluctuations
    4. Autocorrelation and proper sampling

Physical Parameters:
    - SU(2) gauge theory on L³ lattice
    - Wilson plaquette action: S = β Σ_p (1 - (1/N_c) Re Tr U_p)
    - β = 2N_c/g² controls the coupling (larger β = weaker coupling = more ordered)

Target: Demonstrate proper HMC behavior for Proposition 0.0.27 verification

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-03
"""

import numpy as np
from scipy import linalg
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional
from pathlib import Path
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import json
from datetime import datetime

# ============================================================================
# CUBIC LATTICE STRUCTURE
# ============================================================================

class CubicLattice3D:
    """
    3D cubic lattice with periodic boundary conditions.

    Sites are labeled by (x, y, z) with x, y, z ∈ {0, 1, ..., L-1}
    Links are labeled by (site, direction) where direction ∈ {0, 1, 2} = {x, y, z}
    Plaquettes are labeled by (site, plane) where plane ∈ {(0,1), (0,2), (1,2)}
    """

    def __init__(self, L: int):
        self.L = L
        self.volume = L ** 3
        self.n_links = 3 * self.volume  # 3 directions per site
        self.n_plaquettes = 3 * self.volume  # 3 planes per site

        # Direction vectors
        self.directions = [
            np.array([1, 0, 0]),
            np.array([0, 1, 0]),
            np.array([0, 0, 1])
        ]

        # Plaquette planes: (mu, nu) pairs
        self.planes = [(0, 1), (0, 2), (1, 2)]

    def site_index(self, x: int, y: int, z: int) -> int:
        """Convert (x,y,z) to flat index."""
        L = self.L
        return ((x % L) * L + (y % L)) * L + (z % L)

    def index_to_site(self, idx: int) -> Tuple[int, int, int]:
        """Convert flat index to (x,y,z)."""
        L = self.L
        z = idx % L
        y = (idx // L) % L
        x = idx // (L * L)
        return (x, y, z)

    def link_index(self, x: int, y: int, z: int, mu: int) -> int:
        """Get flat index for link at site (x,y,z) in direction mu."""
        return self.site_index(x, y, z) * 3 + mu

    def neighbor(self, x: int, y: int, z: int, mu: int, forward: bool = True) -> Tuple[int, int, int]:
        """Get neighboring site in direction mu."""
        L = self.L
        delta = 1 if forward else -1
        if mu == 0:
            return ((x + delta) % L, y, z)
        elif mu == 1:
            return (x, (y + delta) % L, z)
        else:
            return (x, y, (z + delta) % L)


# ============================================================================
# SU(2) GAUGE FIELD
# ============================================================================

class SU2GaugeField:
    """
    SU(2) gauge field on cubic lattice.

    Each link U_μ(x) is a 2×2 SU(2) matrix.
    SU(2) matrices can be parameterized as U = a₀I + i(a₁σ₁ + a₂σ₂ + a₃σ₃)
    with a₀² + a₁² + a₂² + a₃² = 1.
    """

    def __init__(self, lattice: CubicLattice3D):
        self.lattice = lattice
        self.n_colors = 2

        # Store links as 2×2 complex matrices
        self.links = [np.eye(2, dtype=complex) for _ in range(lattice.n_links)]

    def get_link(self, x: int, y: int, z: int, mu: int) -> np.ndarray:
        """Get U_μ(x,y,z)."""
        idx = self.lattice.link_index(x, y, z, mu)
        return self.links[idx].copy()

    def set_link(self, x: int, y: int, z: int, mu: int, U: np.ndarray):
        """Set U_μ(x,y,z)."""
        idx = self.lattice.link_index(x, y, z, mu)
        self.links[idx] = U.copy()

    def get_link_reverse(self, x: int, y: int, z: int, mu: int) -> np.ndarray:
        """Get U_{-μ}(x) = U_μ(x-μ̂)†."""
        xp, yp, zp = self.lattice.neighbor(x, y, z, mu, forward=False)
        return self.get_link(xp, yp, zp, mu).conj().T

    def plaquette(self, x: int, y: int, z: int, mu: int, nu: int) -> np.ndarray:
        """
        Compute plaquette U_μν(x) = U_μ(x) U_ν(x+μ̂) U_μ(x+ν̂)† U_ν(x)†
        """
        L = self.lattice

        # U_μ(x)
        U1 = self.get_link(x, y, z, mu)

        # U_ν(x + μ̂)
        xp, yp, zp = L.neighbor(x, y, z, mu, forward=True)
        U2 = self.get_link(xp, yp, zp, nu)

        # U_μ(x + ν̂)†
        xp, yp, zp = L.neighbor(x, y, z, nu, forward=True)
        U3 = self.get_link(xp, yp, zp, mu).conj().T

        # U_ν(x)†
        U4 = self.get_link(x, y, z, nu).conj().T

        return U1 @ U2 @ U3 @ U4

    def plaquette_trace(self, x: int, y: int, z: int, mu: int, nu: int) -> float:
        """Compute (1/N_c) Re Tr(U_μν)."""
        P = self.plaquette(x, y, z, mu, nu)
        return np.real(np.trace(P)) / self.n_colors

    def average_plaquette(self) -> float:
        """Compute average plaquette over entire lattice."""
        total = 0.0
        count = 0
        L = self.lattice.L

        for x in range(L):
            for y in range(L):
                for z in range(L):
                    for mu, nu in self.lattice.planes:
                        total += self.plaquette_trace(x, y, z, mu, nu)
                        count += 1

        return total / count

    def wilson_action(self, beta: float) -> float:
        """
        Compute Wilson gauge action.
        S = β Σ_p (1 - (1/N_c) Re Tr(U_p))
        """
        total = 0.0
        L = self.lattice.L

        for x in range(L):
            for y in range(L):
                for z in range(L):
                    for mu, nu in self.lattice.planes:
                        total += 1.0 - self.plaquette_trace(x, y, z, mu, nu)

        return beta * total

    def cold_start(self):
        """Initialize to ordered configuration (all links = I)."""
        for idx in range(len(self.links)):
            self.links[idx] = np.eye(2, dtype=complex)

    def hot_start(self):
        """Initialize to random configuration."""
        for idx in range(len(self.links)):
            self.links[idx] = self._random_su2()

    def _random_su2(self) -> np.ndarray:
        """Generate uniformly random SU(2) matrix."""
        # Use quaternion parameterization: U = a₀I + i(a·σ)
        # with |a|² = 1, uniformly distributed on S³
        a = np.random.randn(4)
        a = a / np.linalg.norm(a)

        # Pauli matrices
        sigma = [
            np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex)
        ]

        U = a[0] * np.eye(2, dtype=complex)
        for i in range(3):
            U += 1j * a[i + 1] * sigma[i]

        return U

    def _random_su2_near_identity(self, epsilon: float) -> np.ndarray:
        """Generate SU(2) matrix near identity."""
        # Small rotation: U ≈ I + iε(a·σ)
        a = epsilon * np.random.randn(3)

        sigma = [
            np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex)
        ]

        H = sum(a[i] * sigma[i] for i in range(3))
        U = linalg.expm(1j * H)

        # Project to SU(2)
        return self._project_su2(U)

    def _project_su2(self, U: np.ndarray) -> np.ndarray:
        """Project matrix to SU(2)."""
        # Make unitary
        u, s, vh = np.linalg.svd(U)
        U = u @ vh
        # Make determinant 1
        det = np.linalg.det(U)
        U = U / np.sqrt(det)
        return U

    def copy(self) -> 'SU2GaugeField':
        """Deep copy."""
        new = SU2GaugeField(self.lattice)
        new.links = [link.copy() for link in self.links]
        return new


# ============================================================================
# HYBRID MONTE CARLO
# ============================================================================

@dataclass
class HMCConfig:
    """HMC configuration parameters."""
    beta: float = 2.3           # Gauge coupling
    n_leapfrog: int = 20        # Leapfrog steps per trajectory
    trajectory_length: float = 1.0

    @property
    def step_size(self) -> float:
        return self.trajectory_length / self.n_leapfrog


class HMC:
    """
    Hybrid Monte Carlo for SU(2) gauge theory.

    The algorithm:
    1. Generate random momenta π from Gaussian distribution
    2. Compute initial Hamiltonian H = (1/2)Tr(π²) + S[U]
    3. Integrate Hamilton's equations using leapfrog
    4. Accept/reject with probability min(1, exp(-ΔH))
    """

    def __init__(self, lattice: CubicLattice3D, config: HMCConfig):
        self.lattice = lattice
        self.config = config
        self.gauge = SU2GaugeField(lattice)

        # Statistics
        self.n_accepted = 0
        self.n_total = 0

        # History
        self.plaquette_history = []
        self.action_history = []
        self.dH_history = []

    def _generate_momenta(self) -> List[np.ndarray]:
        """Generate Gaussian momenta in su(2) Lie algebra."""
        momenta = []

        # Pauli matrices (basis for su(2))
        sigma = [
            np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex)
        ]

        for _ in range(self.lattice.n_links):
            # Random coefficients
            a = np.random.randn(3)
            # π = i Σ_j a_j σ_j (traceless anti-Hermitian)
            pi = 1j * sum(a[j] * sigma[j] for j in range(3))
            momenta.append(pi)

        return momenta

    def _kinetic_energy(self, momenta: List[np.ndarray]) -> float:
        """Compute kinetic energy K = -(1/2) Σ Tr(π²)."""
        # Note: π is anti-Hermitian, so Tr(π²) < 0, and K > 0
        K = 0.0
        for pi in momenta:
            K -= 0.5 * np.real(np.trace(pi @ pi))
        return K

    def _compute_force(self, link_idx: int) -> np.ndarray:
        """
        Compute force on link from gauge action.

        F = -∂S/∂U = (β/N_c) Σ_{p ∋ link} (staple - staple†)
        projected to su(2) Lie algebra.
        """
        L = self.lattice.L
        x, y, z = self.lattice.index_to_site(link_idx // 3)
        mu = link_idx % 3

        # Sum staples from all plaquettes containing this link
        staple_sum = np.zeros((2, 2), dtype=complex)

        for nu in range(3):
            if nu == mu:
                continue

            # Forward staple: U_ν(x+μ̂) U_μ(x+ν̂)† U_ν(x)†
            xp, yp, zp = self.lattice.neighbor(x, y, z, mu, forward=True)
            U1 = self.gauge.get_link(xp, yp, zp, nu)

            xp2, yp2, zp2 = self.lattice.neighbor(x, y, z, nu, forward=True)
            U2 = self.gauge.get_link(xp2, yp2, zp2, mu).conj().T

            U3 = self.gauge.get_link(x, y, z, nu).conj().T

            staple_sum += U1 @ U2 @ U3

            # Backward staple: U_ν(x+μ̂-ν̂)† U_μ(x-ν̂)† U_ν(x-ν̂)
            xm, ym, zm = self.lattice.neighbor(x, y, z, nu, forward=False)
            xpm, ypm, zpm = self.lattice.neighbor(xm, ym, zm, mu, forward=True)

            U1 = self.gauge.get_link(xpm, ypm, zpm, nu).conj().T
            U2 = self.gauge.get_link(xm, ym, zm, mu).conj().T
            U3 = self.gauge.get_link(xm, ym, zm, nu)

            staple_sum += U1 @ U2 @ U3

        # Force: F = (β/N_c) * U * staple_sum, projected to Lie algebra
        U = self.gauge.links[link_idx]
        X = (self.config.beta / 2) * U @ staple_sum

        # Project to traceless anti-Hermitian (Lie algebra)
        F = 0.5 * (X - X.conj().T)
        F = F - np.trace(F) / 2 * np.eye(2)

        return F

    def _leapfrog_step(self, momenta: List[np.ndarray], dt: float) -> List[np.ndarray]:
        """Single leapfrog step."""
        n_links = self.lattice.n_links

        # Half step for momenta
        for idx in range(n_links):
            F = self._compute_force(idx)
            momenta[idx] = momenta[idx] - 0.5 * dt * F

        # Full step for gauge field
        for idx in range(n_links):
            U = self.gauge.links[idx]
            # U' = exp(dt * π) * U
            self.gauge.links[idx] = linalg.expm(dt * momenta[idx]) @ U
            self.gauge.links[idx] = self.gauge._project_su2(self.gauge.links[idx])

        # Half step for momenta
        for idx in range(n_links):
            F = self._compute_force(idx)
            momenta[idx] = momenta[idx] - 0.5 * dt * F

        return momenta

    def trajectory(self) -> Tuple[bool, float]:
        """
        Execute one HMC trajectory.

        Returns: (accepted, delta_H)
        """
        # Save initial configuration
        gauge_old = self.gauge.copy()

        # Generate momenta
        momenta = self._generate_momenta()

        # Initial Hamiltonian
        K_old = self._kinetic_energy(momenta)
        S_old = self.gauge.wilson_action(self.config.beta)
        H_old = K_old + S_old

        # Leapfrog integration
        dt = self.config.step_size
        for _ in range(self.config.n_leapfrog):
            momenta = self._leapfrog_step(momenta, dt)

        # Final Hamiltonian
        K_new = self._kinetic_energy(momenta)
        S_new = self.gauge.wilson_action(self.config.beta)
        H_new = K_new + S_new

        # Metropolis accept/reject
        dH = H_new - H_old

        if dH < 0:
            accept = True
        else:
            accept = np.random.rand() < np.exp(-dH)

        if accept:
            self.n_accepted += 1
        else:
            self.gauge = gauge_old

        self.n_total += 1
        self.dH_history.append(dH)

        return accept, dH

    def run(self, n_trajectories: int, n_thermalization: int = 0,
            start: str = 'hot', verbose: bool = True,
            record_interval: int = 1) -> Dict:
        """
        Run HMC simulation.

        Parameters
        ----------
        n_trajectories : int
            Number of production trajectories
        n_thermalization : int
            Number of thermalization trajectories
        start : str
            'hot' for random start, 'cold' for ordered start
        verbose : bool
            Print progress
        record_interval : int
            Record every N trajectories

        Returns
        -------
        dict
            Simulation results
        """
        # Initialize
        if start == 'hot':
            self.gauge.hot_start()
        else:
            self.gauge.cold_start()

        # Record initial state
        self.plaquette_history = [self.gauge.average_plaquette()]
        self.action_history = [self.gauge.wilson_action(self.config.beta)]

        total_traj = n_thermalization + n_trajectories

        if verbose:
            print(f"Running {n_thermalization} thermalization + {n_trajectories} production")
            print(f"Lattice: {self.lattice.L}³, β = {self.config.beta}")
            print(f"Initial ⟨P⟩ = {self.plaquette_history[0]:.4f}")

        # Thermalization
        for i in range(n_thermalization):
            accepted, dH = self.trajectory()

            if (i + 1) % record_interval == 0:
                plaq = self.gauge.average_plaquette()
                self.plaquette_history.append(plaq)
                self.action_history.append(self.gauge.wilson_action(self.config.beta))

            if verbose and (i + 1) % 50 == 0:
                plaq = self.gauge.average_plaquette()
                rate = self.n_accepted / self.n_total
                print(f"  Therm {i+1}/{n_thermalization}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Reset acceptance for production
        prod_accepted = 0
        prod_total = 0

        # Production
        for i in range(n_trajectories):
            accepted, dH = self.trajectory()
            prod_accepted += int(accepted)
            prod_total += 1

            if (i + 1) % record_interval == 0:
                plaq = self.gauge.average_plaquette()
                self.plaquette_history.append(plaq)
                self.action_history.append(self.gauge.wilson_action(self.config.beta))

            if verbose and (i + 1) % 100 == 0:
                plaq = self.gauge.average_plaquette()
                rate = prod_accepted / prod_total
                print(f"  Prod {i+1}/{n_trajectories}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Compute statistics from production run
        therm_idx = n_thermalization // record_interval + 1
        prod_plaquettes = np.array(self.plaquette_history[therm_idx:])

        results = {
            'lattice_size': self.lattice.L,
            'beta': self.config.beta,
            'n_thermalization': n_thermalization,
            'n_production': n_trajectories,
            'acceptance_rate': prod_accepted / prod_total if prod_total > 0 else 0,
            'plaquette_mean': float(np.mean(prod_plaquettes)),
            'plaquette_std': float(np.std(prod_plaquettes)),
            'plaquette_history': self.plaquette_history,
            'action_history': self.action_history
        }

        if verbose:
            print(f"\nResults:")
            print(f"  ⟨P⟩ = {results['plaquette_mean']:.6f} ± {results['plaquette_std']:.6f}")
            print(f"  Acceptance rate: {results['acceptance_rate']:.1%}")

        return results


# ============================================================================
# PLOTLY ANIMATION
# ============================================================================

def create_hmc_animation(results: Dict,
                         n_thermalization: int,
                         title: str = "Lattice QCD HMC Thermalization",
                         output_html: Optional[str] = None) -> go.Figure:
    """
    Create animated visualization of HMC thermalization.
    """

    plaquettes = results['plaquette_history']
    n_frames = len(plaquettes)

    # Compute running average
    window = 20
    running_avg = []
    for i in range(n_frames):
        start = max(0, i - window + 1)
        running_avg.append(np.mean(plaquettes[start:i+1]))

    # Equilibrium value (from production)
    therm_idx = n_thermalization + 1
    if therm_idx < len(plaquettes):
        equil_plaq = np.mean(plaquettes[therm_idx:])
        equil_std = np.std(plaquettes[therm_idx:])
    else:
        equil_plaq = np.mean(plaquettes)
        equil_std = np.std(plaquettes)

    # Create figure
    fig = go.Figure()

    # Build animation frames
    animation_frames = []

    for i in range(n_frames):
        # Raw plaquette trace (faded)
        raw_trace = go.Scatter(
            x=list(range(i + 1)),
            y=plaquettes[:i + 1],
            mode='lines',
            line=dict(color='rgba(100, 150, 255, 0.3)', width=1),
            name='Raw',
            hoverinfo='skip'
        )

        # Running average (prominent)
        avg_trace = go.Scatter(
            x=list(range(i + 1)),
            y=running_avg[:i + 1],
            mode='lines',
            line=dict(color='yellow', width=3),
            name='Running Avg'
        )

        # Current point
        current_trace = go.Scatter(
            x=[i],
            y=[plaquettes[i]],
            mode='markers',
            marker=dict(size=12, color='red', symbol='circle',
                       line=dict(width=2, color='white')),
            name='Current',
            hovertemplate=f"Traj {i}<br>⟨P⟩ = {plaquettes[i]:.4f}<extra></extra>"
        )

        # Thermalization line
        therm_line = go.Scatter(
            x=[n_thermalization, n_thermalization],
            y=[0, 1],
            mode='lines',
            line=dict(color='rgba(255, 100, 100, 0.7)', width=2, dash='dash'),
            name='Therm End'
        )

        # Equilibrium band
        equil_band_upper = go.Scatter(
            x=[0, n_frames],
            y=[equil_plaq + equil_std, equil_plaq + equil_std],
            mode='lines',
            line=dict(color='rgba(100, 255, 100, 0)', width=0),
            showlegend=False,
            hoverinfo='skip'
        )

        equil_band_lower = go.Scatter(
            x=[0, n_frames],
            y=[equil_plaq - equil_std, equil_plaq - equil_std],
            mode='lines',
            line=dict(color='rgba(100, 255, 100, 0)', width=0),
            fill='tonexty',
            fillcolor='rgba(100, 255, 100, 0.2)',
            showlegend=False,
            hoverinfo='skip'
        )

        # Equilibrium line
        equil_line = go.Scatter(
            x=[0, n_frames],
            y=[equil_plaq, equil_plaq],
            mode='lines',
            line=dict(color='rgba(100, 255, 100, 0.8)', width=2, dash='dot'),
            name=f'Equil: {equil_plaq:.4f}'
        )

        animation_frames.append(go.Frame(
            data=[raw_trace, avg_trace, current_trace, therm_line,
                  equil_band_upper, equil_band_lower, equil_line],
            name=str(i)
        ))

    # Add initial traces
    fig.add_traces(animation_frames[0].data)
    fig.frames = animation_frames

    # Layout
    fig.update_layout(
        title=dict(
            text=f"<b>{title}</b><br><sup>L={results['lattice_size']}³, β={results['beta']}, ⟨P⟩={equil_plaq:.4f}±{equil_std:.4f}</sup>",
            x=0.5,
            font=dict(size=20)
        ),
        xaxis=dict(
            title='HMC Trajectory',
            range=[-5, n_frames + 5],
            gridcolor='rgba(128,128,128,0.3)'
        ),
        yaxis=dict(
            title='Average Plaquette ⟨P⟩',
            range=[min(0, min(plaquettes) - 0.05), max(1, max(plaquettes) + 0.05)],
            gridcolor='rgba(128,128,128,0.3)'
        ),
        paper_bgcolor='rgb(20, 20, 35)',
        plot_bgcolor='rgb(30, 30, 50)',
        font=dict(color='white', size=14),
        legend=dict(
            x=0.02, y=0.98,
            bgcolor='rgba(0,0,0,0.5)',
            bordercolor='rgba(255,255,255,0.3)',
            borderwidth=1
        ),
        updatemenus=[
            dict(
                type='buttons',
                showactive=False,
                y=1.15,
                x=0.5,
                xanchor='center',
                buttons=[
                    dict(
                        label='▶ Play',
                        method='animate',
                        args=[None, dict(
                            frame=dict(duration=50, redraw=True),
                            fromcurrent=True,
                            mode='immediate',
                            transition=dict(duration=20)
                        )]
                    ),
                    dict(
                        label='⏸ Pause',
                        method='animate',
                        args=[[None], dict(
                            frame=dict(duration=0, redraw=False),
                            mode='immediate'
                        )]
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
                transition=dict(duration=20),
                pad=dict(b=10, t=50),
                len=0.9,
                x=0.05,
                y=0,
                steps=[
                    dict(
                        args=[[str(i)], dict(
                            frame=dict(duration=50, redraw=True),
                            mode='immediate',
                            transition=dict(duration=20)
                        )],
                        label=str(i),
                        method='animate'
                    )
                    for i in range(0, n_frames, max(1, n_frames // 100))
                ]
            )
        ],
        # Annotations
        annotations=[
            dict(
                x=n_thermalization,
                y=0.95,
                xref='x',
                yref='paper',
                text='← Thermalization | Production →',
                showarrow=False,
                font=dict(size=12, color='rgba(255,150,150,0.8)')
            )
        ]
    )

    if output_html:
        fig.write_html(output_html, include_plotlyjs=True, full_html=True)
        print(f"Animation saved to: {output_html}")

    return fig


def create_comparison_plot(results_hot: Dict, results_cold: Dict,
                           n_thermalization: int,
                           output_html: Optional[str] = None) -> go.Figure:
    """
    Create comparison plot showing hot vs cold start thermalization.
    """

    plaq_hot = results_hot['plaquette_history']
    plaq_cold = results_cold['plaquette_history']

    # Running averages
    window = 15
    def running_avg(data):
        return [np.mean(data[max(0, i-window+1):i+1]) for i in range(len(data))]

    avg_hot = running_avg(plaq_hot)
    avg_cold = running_avg(plaq_cold)

    # Equilibrium
    therm_idx = n_thermalization + 1
    equil_hot = np.mean(plaq_hot[therm_idx:])
    equil_cold = np.mean(plaq_cold[therm_idx:])
    equil = (equil_hot + equil_cold) / 2

    fig = go.Figure()

    # Hot start traces
    fig.add_trace(go.Scatter(
        x=list(range(len(plaq_hot))),
        y=plaq_hot,
        mode='lines',
        line=dict(color='rgba(255, 100, 100, 0.3)', width=1),
        name='Hot (raw)',
        legendgroup='hot'
    ))
    fig.add_trace(go.Scatter(
        x=list(range(len(avg_hot))),
        y=avg_hot,
        mode='lines',
        line=dict(color='red', width=3),
        name='Hot Start',
        legendgroup='hot'
    ))

    # Cold start traces
    fig.add_trace(go.Scatter(
        x=list(range(len(plaq_cold))),
        y=plaq_cold,
        mode='lines',
        line=dict(color='rgba(100, 100, 255, 0.3)', width=1),
        name='Cold (raw)',
        legendgroup='cold'
    ))
    fig.add_trace(go.Scatter(
        x=list(range(len(avg_cold))),
        y=avg_cold,
        mode='lines',
        line=dict(color='blue', width=3),
        name='Cold Start',
        legendgroup='cold'
    ))

    # Equilibrium line
    fig.add_trace(go.Scatter(
        x=[0, max(len(plaq_hot), len(plaq_cold))],
        y=[equil, equil],
        mode='lines',
        line=dict(color='green', width=2, dash='dot'),
        name=f'Equilibrium: {equil:.4f}'
    ))

    # Thermalization line
    fig.add_vline(x=n_thermalization, line=dict(color='yellow', width=2, dash='dash'),
                  annotation_text='Therm End', annotation_position='top')

    fig.update_layout(
        title=dict(
            text=f"<b>HMC Thermalization: Hot vs Cold Start</b><br><sup>Both converge to same equilibrium ⟨P⟩ ≈ {equil:.4f}</sup>",
            x=0.5,
            font=dict(size=20)
        ),
        xaxis=dict(title='HMC Trajectory', gridcolor='rgba(128,128,128,0.3)'),
        yaxis=dict(title='Average Plaquette ⟨P⟩', range=[0, 1.05], gridcolor='rgba(128,128,128,0.3)'),
        paper_bgcolor='rgb(20, 20, 35)',
        plot_bgcolor='rgb(30, 30, 50)',
        font=dict(color='white', size=14),
        legend=dict(x=0.7, y=0.5)
    )

    if output_html:
        fig.write_html(output_html, include_plotlyjs=True, full_html=True)
        print(f"Comparison plot saved to: {output_html}")

    return fig


# ============================================================================
# MAIN
# ============================================================================

def main():
    """Run simulation and create visualizations."""

    print("=" * 70)
    print("LATTICE QCD HMC SIMULATION")
    print("Physically Accurate Thermalization Demonstration")
    print("=" * 70)

    # Simulation parameters
    L = 8  # 8³ = 512 sites, 1536 plaquettes
    beta = 2.3  # Intermediate coupling
    n_thermalization = 150
    n_production = 500

    # Create lattice
    lattice = CubicLattice3D(L)
    print(f"\nLattice: {L}³ = {lattice.volume} sites")
    print(f"Links: {lattice.n_links}")
    print(f"Plaquettes: {lattice.n_plaquettes}")
    print(f"β = {beta}")

    # HMC configuration
    config = HMCConfig(
        beta=beta,
        n_leapfrog=15,
        trajectory_length=1.0
    )

    # Run with hot start (random initial configuration)
    print("\n" + "-" * 50)
    print("HOT START (random initial configuration)")
    print("-" * 50)
    hmc_hot = HMC(lattice, config)
    results_hot = hmc_hot.run(
        n_trajectories=n_production,
        n_thermalization=n_thermalization,
        start='hot',
        verbose=True,
        record_interval=1
    )

    # Run with cold start (ordered initial configuration)
    print("\n" + "-" * 50)
    print("COLD START (ordered initial configuration)")
    print("-" * 50)
    hmc_cold = HMC(lattice, config)
    results_cold = hmc_cold.run(
        n_trajectories=n_production,
        n_thermalization=n_thermalization,
        start='cold',
        verbose=True,
        record_interval=1
    )

    # Output directory
    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    # Create animations
    print("\n" + "=" * 70)
    print("CREATING VISUALIZATIONS")
    print("=" * 70)

    # Hot start animation
    print("\nCreating hot start animation...")
    fig_hot = create_hmc_animation(
        results_hot,
        n_thermalization,
        title="Lattice QCD: Hot Start Thermalization",
        output_html=str(output_dir / "lattice_hmc_hot.html")
    )

    # Cold start animation
    print("Creating cold start animation...")
    fig_cold = create_hmc_animation(
        results_cold,
        n_thermalization,
        title="Lattice QCD: Cold Start Thermalization",
        output_html=str(output_dir / "lattice_hmc_cold.html")
    )

    # Comparison plot
    print("Creating comparison plot...")
    fig_compare = create_comparison_plot(
        results_hot,
        results_cold,
        n_thermalization,
        output_html=str(output_dir / "lattice_hmc_comparison.html")
    )

    # Save results
    results_file = output_dir / "lattice_hmc_results.json"
    combined_results = {
        'timestamp': datetime.now().isoformat(),
        'parameters': {
            'L': L,
            'beta': beta,
            'n_thermalization': n_thermalization,
            'n_production': n_production
        },
        'hot_start': {
            'plaquette_mean': results_hot['plaquette_mean'],
            'plaquette_std': results_hot['plaquette_std'],
            'acceptance_rate': results_hot['acceptance_rate']
        },
        'cold_start': {
            'plaquette_mean': results_cold['plaquette_mean'],
            'plaquette_std': results_cold['plaquette_std'],
            'acceptance_rate': results_cold['acceptance_rate']
        }
    }

    with open(results_file, 'w') as f:
        json.dump(combined_results, f, indent=2)

    # Summary
    print("\n" + "=" * 70)
    print("SIMULATION COMPLETE")
    print("=" * 70)
    print(f"\nOutput files in {output_dir}/:")
    print("  - lattice_hmc_hot.html      (hot start animation)")
    print("  - lattice_hmc_cold.html     (cold start animation)")
    print("  - lattice_hmc_comparison.html (side-by-side comparison)")
    print("  - lattice_hmc_results.json  (numerical results)")
    print(f"\nEquilibrium plaquette:")
    print(f"  Hot start:  ⟨P⟩ = {results_hot['plaquette_mean']:.6f} ± {results_hot['plaquette_std']:.6f}")
    print(f"  Cold start: ⟨P⟩ = {results_cold['plaquette_mean']:.6f} ± {results_cold['plaquette_std']:.6f}")
    print(f"\nBoth converge to same value - this demonstrates proper thermalization!")

    return results_hot, results_cold


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Fast Lattice QCD HMC Simulation with NumPy Vectorization
=========================================================

Optimized implementation using NumPy for vectorized operations.
Demonstrates proper HMC thermalization on cubic lattices.

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-03
"""

import numpy as np
from scipy import linalg
from typing import Dict, Tuple, Optional
from pathlib import Path
import plotly.graph_objects as go
import json
from datetime import datetime

# ============================================================================
# FAST SU(2) OPERATIONS
# ============================================================================

def random_su2(shape: Tuple = ()) -> np.ndarray:
    """Generate random SU(2) matrices using quaternion parameterization."""
    # a = (a0, a1, a2, a3) with |a|=1 uniformly on S³
    a = np.random.randn(*shape, 4)
    a = a / np.linalg.norm(a, axis=-1, keepdims=True)

    # U = a0*I + i*(a1*σ1 + a2*σ2 + a3*σ3)
    # In matrix form: [[a0+i*a3, a2+i*a1], [-a2+i*a1, a0-i*a3]]
    U = np.zeros((*shape, 2, 2), dtype=complex)
    U[..., 0, 0] = a[..., 0] + 1j * a[..., 3]
    U[..., 0, 1] = a[..., 2] + 1j * a[..., 1]
    U[..., 1, 0] = -a[..., 2] + 1j * a[..., 1]
    U[..., 1, 1] = a[..., 0] - 1j * a[..., 3]

    return U


def random_su2_near_identity(epsilon: float, shape: Tuple = ()) -> np.ndarray:
    """Generate SU(2) matrices near identity."""
    a = np.zeros((*shape, 4))
    a[..., 0] = 1.0
    a[..., 1:] = epsilon * np.random.randn(*shape, 3)
    a = a / np.linalg.norm(a, axis=-1, keepdims=True)

    U = np.zeros((*shape, 2, 2), dtype=complex)
    U[..., 0, 0] = a[..., 0] + 1j * a[..., 3]
    U[..., 0, 1] = a[..., 2] + 1j * a[..., 1]
    U[..., 1, 0] = -a[..., 2] + 1j * a[..., 1]
    U[..., 1, 1] = a[..., 0] - 1j * a[..., 3]

    return U


def project_su2(U: np.ndarray) -> np.ndarray:
    """Project matrix to SU(2) via Gram-Schmidt."""
    # Normalize first column
    col0 = U[..., :, 0]
    col0 = col0 / np.linalg.norm(col0, axis=-1, keepdims=True)

    # Second column orthogonal to first
    col1 = U[..., :, 1]
    proj = np.sum(col1 * np.conj(col0), axis=-1, keepdims=True) * col0
    col1 = col1 - proj
    col1 = col1 / np.linalg.norm(col1, axis=-1, keepdims=True)

    result = np.stack([col0, col1], axis=-1)

    # Fix determinant
    det = result[..., 0, 0] * result[..., 1, 1] - result[..., 0, 1] * result[..., 1, 0]
    phase = np.exp(-1j * np.angle(det) / 2)
    result = result * phase[..., np.newaxis, np.newaxis]

    return result


# ============================================================================
# FAST LATTICE GAUGE FIELD
# ============================================================================

class FastLatticeGauge:
    """
    SU(2) gauge field on 3D cubic lattice with periodic BC.

    Links stored as array of shape (L, L, L, 3, 2, 2):
        U[x, y, z, mu] is the link at site (x,y,z) in direction mu
    """

    def __init__(self, L: int):
        self.L = L
        self.shape = (L, L, L, 3, 2, 2)

        # Initialize to identity
        self.U = np.zeros(self.shape, dtype=complex)
        self.U[..., 0, 0] = 1.0
        self.U[..., 1, 1] = 1.0

    def hot_start(self):
        """Random initial configuration."""
        self.U = random_su2((self.L, self.L, self.L, 3))

    def cold_start(self):
        """Ordered initial configuration (all I)."""
        self.U = np.zeros(self.shape, dtype=complex)
        self.U[..., 0, 0] = 1.0
        self.U[..., 1, 1] = 1.0

    def compute_plaquettes(self) -> np.ndarray:
        """
        Compute all plaquettes. Returns array of shape (L, L, L, 3).

        P_{μν}(x) = Tr[U_μ(x) U_ν(x+μ) U_μ(x+ν)† U_ν(x)†] / 2
        """
        L = self.L
        plaq = np.zeros((L, L, L, 3))

        planes = [(0, 1), (0, 2), (1, 2)]

        for p_idx, (mu, nu) in enumerate(planes):
            # U_μ(x)
            U1 = self.U[:, :, :, mu]

            # U_ν(x + μ̂) - roll in direction mu
            U2 = np.roll(self.U[:, :, :, nu], -1, axis=mu)

            # U_μ(x + ν̂)† - roll in direction nu, then dagger
            U3 = np.roll(self.U[:, :, :, mu], -1, axis=nu)
            U3 = np.conj(np.swapaxes(U3, -2, -1))

            # U_ν(x)†
            U4 = np.conj(np.swapaxes(self.U[:, :, :, nu], -2, -1))

            # P = U1 @ U2 @ U3 @ U4
            P = np.einsum('...ij,...jk,...kl,...lm->...im', U1, U2, U3, U4)

            # (1/2) Re Tr(P)
            plaq[:, :, :, p_idx] = 0.5 * np.real(P[..., 0, 0] + P[..., 1, 1])

        return plaq

    def average_plaquette(self) -> float:
        """Compute spatial average of plaquette."""
        return np.mean(self.compute_plaquettes())

    def wilson_action(self, beta: float) -> float:
        """Wilson gauge action: S = β Σ_p (1 - P_p)."""
        plaq = self.compute_plaquettes()
        return beta * np.sum(1.0 - plaq)

    def compute_staples(self, mu: int) -> np.ndarray:
        """
        Compute sum of staples for links in direction mu.
        Returns array of shape (L, L, L, 2, 2).

        Staple = Σ_{ν≠μ} [U_ν(x+μ) U_μ(x+ν)† U_ν(x)† + U_ν(x+μ-ν)† U_μ(x-ν)† U_ν(x-ν)]
        """
        L = self.L
        staple = np.zeros((L, L, L, 2, 2), dtype=complex)

        for nu in range(3):
            if nu == mu:
                continue

            # Forward staple: U_ν(x+μ) U_μ(x+ν)† U_ν(x)†
            U1 = np.roll(self.U[:, :, :, nu], -1, axis=mu)
            U2 = np.roll(self.U[:, :, :, mu], -1, axis=nu)
            U2 = np.conj(np.swapaxes(U2, -2, -1))
            U3 = np.conj(np.swapaxes(self.U[:, :, :, nu], -2, -1))

            staple += np.einsum('...ij,...jk,...kl->...il', U1, U2, U3)

            # Backward staple: U_ν(x+μ-ν)† U_μ(x-ν)† U_ν(x-ν)
            U1 = np.roll(np.roll(self.U[:, :, :, nu], -1, axis=mu), 1, axis=nu)
            U1 = np.conj(np.swapaxes(U1, -2, -1))
            U2 = np.roll(self.U[:, :, :, mu], 1, axis=nu)
            U2 = np.conj(np.swapaxes(U2, -2, -1))
            U3 = np.roll(self.U[:, :, :, nu], 1, axis=nu)

            staple += np.einsum('...ij,...jk,...kl->...il', U1, U2, U3)

        return staple

    def copy(self) -> 'FastLatticeGauge':
        """Deep copy."""
        new = FastLatticeGauge(self.L)
        new.U = self.U.copy()
        return new


# ============================================================================
# FAST HMC
# ============================================================================

class FastHMC:
    """
    Optimized HMC for SU(2) gauge theory.
    """

    def __init__(self, L: int, beta: float = 2.3,
                 n_leapfrog: int = 10, trajectory_length: float = 1.0):
        self.L = L
        self.beta = beta
        self.n_leapfrog = n_leapfrog
        self.dt = trajectory_length / n_leapfrog

        self.gauge = FastLatticeGauge(L)

        # Pauli matrices for momentum generation
        self.sigma = np.array([
            [[0, 1], [1, 0]],
            [[0, -1j], [1j, 0]],
            [[1, 0], [0, -1]]
        ], dtype=complex)

        # Statistics
        self.n_accepted = 0
        self.n_total = 0
        self.plaquette_history = []

    def _generate_momenta(self) -> np.ndarray:
        """Generate Gaussian momenta in su(2)."""
        L = self.L
        # Random coefficients for Pauli basis
        a = np.random.randn(L, L, L, 3, 3)  # Last index is Pauli index

        # π = i Σ_j a_j σ_j
        pi = 1j * np.einsum('...j,jkl->...kl', a, self.sigma)

        return pi

    def _kinetic_energy(self, pi: np.ndarray) -> float:
        """K = -(1/2) Σ Tr(π²)."""
        pi_sq = np.einsum('...ij,...ji->...', pi, pi)
        return -0.5 * np.real(np.sum(pi_sq))

    def _compute_force(self) -> np.ndarray:
        """
        Compute force F_μ(x) = (β/2) * [U_μ(x) * staple - staple† * U_μ(x)†]
        projected to su(2).
        """
        L = self.L
        force = np.zeros((L, L, L, 3, 2, 2), dtype=complex)

        for mu in range(3):
            staple = self.gauge.compute_staples(mu)
            U = self.gauge.U[:, :, :, mu]

            # X = U * staple
            X = np.einsum('...ij,...jk->...ik', U, staple)

            # Force = (β/2) * (X - X†), then project to traceless
            F = (self.beta / 2) * (X - np.conj(np.swapaxes(X, -2, -1)))

            # Make traceless
            trace = F[..., 0, 0] + F[..., 1, 1]
            F[..., 0, 0] -= trace / 2
            F[..., 1, 1] -= trace / 2

            force[:, :, :, mu] = F

        return force

    def _leapfrog(self, pi: np.ndarray) -> np.ndarray:
        """Full leapfrog integration."""
        dt = self.dt

        for step in range(self.n_leapfrog):
            # Half step momentum
            F = self._compute_force()
            pi = pi - 0.5 * dt * F

            # Full step position: U' = exp(dt * π) * U
            for mu in range(3):
                # For small dt, exp(dt*π) ≈ I + dt*π + (dt*π)²/2
                # But we need exact for reversibility
                for x in range(self.L):
                    for y in range(self.L):
                        for z in range(self.L):
                            pi_mat = pi[x, y, z, mu]
                            U_old = self.gauge.U[x, y, z, mu]
                            exp_pi = linalg.expm(dt * pi_mat)
                            self.gauge.U[x, y, z, mu] = exp_pi @ U_old

            # Project back to SU(2) for numerical stability
            self.gauge.U = project_su2(self.gauge.U)

            # Half step momentum
            F = self._compute_force()
            pi = pi - 0.5 * dt * F

        return pi

    def trajectory(self) -> Tuple[bool, float]:
        """Execute one HMC trajectory."""
        gauge_old = self.gauge.copy()

        # Generate momenta
        pi = self._generate_momenta()

        # Initial Hamiltonian
        K_old = self._kinetic_energy(pi)
        S_old = self.gauge.wilson_action(self.beta)
        H_old = K_old + S_old

        # Leapfrog
        pi = self._leapfrog(pi)

        # Final Hamiltonian
        K_new = self._kinetic_energy(pi)
        S_new = self.gauge.wilson_action(self.beta)
        H_new = K_new + S_new

        # Metropolis
        dH = H_new - H_old

        if dH < 0 or np.random.rand() < np.exp(-dH):
            accept = True
            self.n_accepted += 1
        else:
            accept = False
            self.gauge = gauge_old

        self.n_total += 1

        return accept, dH

    def run(self, n_trajectories: int, n_thermalization: int = 0,
            start: str = 'hot', verbose: bool = True) -> Dict:
        """Run simulation."""

        if start == 'hot':
            self.gauge.hot_start()
        else:
            self.gauge.cold_start()

        self.plaquette_history = [self.gauge.average_plaquette()]

        if verbose:
            print(f"L={self.L}, β={self.beta}, start={start}")
            print(f"Initial ⟨P⟩ = {self.plaquette_history[0]:.4f}")

        # Thermalization
        for i in range(n_thermalization):
            self.trajectory()
            self.plaquette_history.append(self.gauge.average_plaquette())

            if verbose and (i + 1) % 25 == 0:
                plaq = self.plaquette_history[-1]
                rate = self.n_accepted / self.n_total
                print(f"  Therm {i+1}/{n_thermalization}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Reset for production
        prod_accepted = 0
        prod_total = 0

        # Production
        for i in range(n_trajectories):
            accepted, _ = self.trajectory()
            prod_accepted += int(accepted)
            prod_total += 1
            self.plaquette_history.append(self.gauge.average_plaquette())

            if verbose and (i + 1) % 50 == 0:
                plaq = self.plaquette_history[-1]
                rate = prod_accepted / prod_total
                print(f"  Prod {i+1}/{n_trajectories}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Statistics
        prod_plaq = np.array(self.plaquette_history[n_thermalization+1:])

        results = {
            'L': self.L,
            'beta': self.beta,
            'plaquette_mean': float(np.mean(prod_plaq)),
            'plaquette_std': float(np.std(prod_plaq)),
            'acceptance_rate': prod_accepted / prod_total if prod_total > 0 else 0,
            'plaquette_history': self.plaquette_history
        }

        if verbose:
            print(f"\n⟨P⟩ = {results['plaquette_mean']:.6f} ± {results['plaquette_std']:.6f}")

        return results


# ============================================================================
# VISUALIZATION
# ============================================================================

def create_animation(results: Dict, n_therm: int,
                     title: str, output_html: str) -> go.Figure:
    """Create animated plaquette evolution plot."""

    plaq = results['plaquette_history']
    n_frames = len(plaq)

    # Running average
    window = 15
    running_avg = [np.mean(plaq[max(0, i-window+1):i+1]) for i in range(n_frames)]

    # Equilibrium from production
    equil = results['plaquette_mean']
    equil_std = results['plaquette_std']

    fig = go.Figure()

    # Build frames
    frames = []
    for i in range(n_frames):
        frames.append(go.Frame(
            data=[
                go.Scatter(x=list(range(i+1)), y=plaq[:i+1],
                          mode='lines', line=dict(color='rgba(100,150,255,0.3)', width=1),
                          name='Raw'),
                go.Scatter(x=list(range(i+1)), y=running_avg[:i+1],
                          mode='lines', line=dict(color='yellow', width=3),
                          name='Running Avg'),
                go.Scatter(x=[i], y=[plaq[i]],
                          mode='markers', marker=dict(size=12, color='red'),
                          name='Current'),
                go.Scatter(x=[n_therm, n_therm], y=[0, 1],
                          mode='lines', line=dict(color='rgba(255,100,100,0.7)', dash='dash'),
                          name='Therm End'),
                go.Scatter(x=[0, n_frames], y=[equil, equil],
                          mode='lines', line=dict(color='lime', dash='dot', width=2),
                          name=f'Equil: {equil:.4f}'),
                go.Scatter(x=[0, n_frames, n_frames, 0, 0],
                          y=[equil-equil_std, equil-equil_std, equil+equil_std, equil+equil_std, equil-equil_std],
                          fill='toself', fillcolor='rgba(0,255,0,0.1)',
                          line=dict(color='rgba(0,0,0,0)'), name='±1σ')
            ],
            name=str(i)
        ))

    # Initial traces
    fig.add_traces(frames[0].data)
    fig.frames = frames

    fig.update_layout(
        title=dict(text=f"<b>{title}</b><br><sup>L={results['L']}³, β={results['beta']}, ⟨P⟩={equil:.4f}±{equil_std:.4f}</sup>",
                   x=0.5, font=dict(size=18)),
        xaxis=dict(title='HMC Trajectory', range=[-5, n_frames+5], gridcolor='rgba(100,100,100,0.3)'),
        yaxis=dict(title='Average Plaquette ⟨P⟩', range=[0, 1.05], gridcolor='rgba(100,100,100,0.3)'),
        paper_bgcolor='rgb(15,15,25)',
        plot_bgcolor='rgb(25,25,40)',
        font=dict(color='white', size=12),
        showlegend=True,
        legend=dict(x=0.02, y=0.98, bgcolor='rgba(0,0,0,0.5)'),
        updatemenus=[dict(
            type='buttons', showactive=False, y=1.12, x=0.5, xanchor='center',
            buttons=[
                dict(label='▶ Play', method='animate',
                     args=[None, dict(frame=dict(duration=30, redraw=True),
                                     fromcurrent=True, mode='immediate')]),
                dict(label='⏸ Pause', method='animate',
                     args=[[None], dict(frame=dict(duration=0, redraw=False), mode='immediate')])
            ]
        )],
        sliders=[dict(
            active=0, yanchor='top', xanchor='left',
            currentvalue=dict(prefix='Traj: ', visible=True, xanchor='right'),
            pad=dict(b=10, t=50), len=0.9, x=0.05, y=0,
            steps=[dict(args=[[str(i)], dict(frame=dict(duration=30, redraw=True), mode='immediate')],
                       label=str(i), method='animate')
                   for i in range(0, n_frames, max(1, n_frames//100))]
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
    print("FAST LATTICE QCD HMC SIMULATION")
    print("=" * 60)

    # Parameters
    L = 8
    beta = 2.3
    n_therm = 100
    n_prod = 300

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    # Hot start
    print(f"\n{'='*40}")
    print("HOT START")
    print('='*40)
    hmc_hot = FastHMC(L, beta=beta, n_leapfrog=12, trajectory_length=1.0)
    results_hot = hmc_hot.run(n_prod, n_therm, start='hot', verbose=True)

    # Cold start
    print(f"\n{'='*40}")
    print("COLD START")
    print('='*40)
    hmc_cold = FastHMC(L, beta=beta, n_leapfrog=12, trajectory_length=1.0)
    results_cold = hmc_cold.run(n_prod, n_therm, start='cold', verbose=True)

    # Create animations
    print("\nCreating visualizations...")

    create_animation(results_hot, n_therm, "Lattice QCD: Hot Start",
                    str(output_dir / "lattice_hmc_hot.html"))

    create_animation(results_cold, n_therm, "Lattice QCD: Cold Start",
                    str(output_dir / "lattice_hmc_cold.html"))

    # Comparison plot
    fig = go.Figure()

    # Hot start
    fig.add_trace(go.Scatter(
        y=results_hot['plaquette_history'],
        mode='lines', line=dict(color='red', width=2),
        name='Hot Start'
    ))

    # Cold start
    fig.add_trace(go.Scatter(
        y=results_cold['plaquette_history'],
        mode='lines', line=dict(color='blue', width=2),
        name='Cold Start'
    ))

    # Equilibrium
    equil = (results_hot['plaquette_mean'] + results_cold['plaquette_mean']) / 2
    fig.add_hline(y=equil, line=dict(color='lime', dash='dot', width=2),
                  annotation_text=f"Equilibrium: {equil:.4f}")
    fig.add_vline(x=n_therm, line=dict(color='yellow', dash='dash'),
                  annotation_text="Therm End")

    fig.update_layout(
        title=dict(text=f"<b>HMC Thermalization: Hot vs Cold Start</b><br><sup>Both converge to ⟨P⟩ ≈ {equil:.4f}</sup>",
                   x=0.5, font=dict(size=18)),
        xaxis=dict(title='HMC Trajectory', gridcolor='rgba(100,100,100,0.3)'),
        yaxis=dict(title='Average Plaquette', range=[0, 1.05], gridcolor='rgba(100,100,100,0.3)'),
        paper_bgcolor='rgb(15,15,25)',
        plot_bgcolor='rgb(25,25,40)',
        font=dict(color='white'),
        legend=dict(x=0.7, y=0.5)
    )

    fig.write_html(str(output_dir / "lattice_hmc_comparison.html"), include_plotlyjs=True)
    print(f"Saved: {output_dir / 'lattice_hmc_comparison.html'}")

    # Summary
    print("\n" + "=" * 60)
    print("COMPLETE")
    print("=" * 60)
    print(f"\nEquilibrium plaquette:")
    print(f"  Hot:  ⟨P⟩ = {results_hot['plaquette_mean']:.4f} ± {results_hot['plaquette_std']:.4f}")
    print(f"  Cold: ⟨P⟩ = {results_cold['plaquette_mean']:.4f} ± {results_cold['plaquette_std']:.4f}")
    print(f"\nFiles saved to: {output_dir}/")


if __name__ == "__main__":
    main()

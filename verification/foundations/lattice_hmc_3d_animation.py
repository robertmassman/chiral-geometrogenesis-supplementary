#!/usr/bin/env python3
"""
Lattice QCD HMC with 3D Visualization
=====================================

Shows the cubic lattice structure with links colored by local plaquette values,
animated alongside the plaquette evolution time series.

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-03
"""

import numpy as np
from scipy import linalg
from typing import Dict, Tuple, List
from pathlib import Path
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from dataclasses import dataclass

# ============================================================================
# SU(2) UTILITIES
# ============================================================================

def quaternion_to_su2(a: np.ndarray) -> np.ndarray:
    """Convert quaternion to SU(2) matrix."""
    return np.array([
        [a[0] + 1j*a[3], a[2] + 1j*a[1]],
        [-a[2] + 1j*a[1], a[0] - 1j*a[3]]
    ], dtype=complex)


def su2_random() -> np.ndarray:
    """Random SU(2) matrix."""
    a = np.random.randn(4)
    a = a / np.linalg.norm(a)
    return quaternion_to_su2(a)


def su2_exp(H: np.ndarray) -> np.ndarray:
    """Exponential of traceless anti-Hermitian matrix."""
    h1 = np.imag(H[0, 1] + H[1, 0]) / 2
    h2 = np.real(H[0, 1] - H[1, 0]) / 2
    h3 = np.imag(H[0, 0] - H[1, 1]) / 2
    h_norm = np.sqrt(h1**2 + h2**2 + h3**2)
    if h_norm < 1e-10:
        return np.eye(2, dtype=complex) + H
    c = np.cos(h_norm)
    s = np.sin(h_norm) / h_norm
    return c * np.eye(2, dtype=complex) + s * H


def su2_project(U: np.ndarray) -> np.ndarray:
    """Project to SU(2)."""
    u, s, vh = np.linalg.svd(U)
    W = u @ vh
    det = np.linalg.det(W)
    return W / np.sqrt(det)


# ============================================================================
# LATTICE WITH FRAME RECORDING
# ============================================================================

@dataclass
class LatticeFrame:
    """Snapshot of lattice configuration for visualization."""
    trajectory: int
    avg_plaquette: float
    link_plaquettes: np.ndarray  # Local plaquette value for each link
    site_coords: np.ndarray      # (N, 3) site positions
    link_endpoints: List[Tuple[np.ndarray, np.ndarray]]  # Start/end for each link


class VisualLattice:
    """Lattice gauge field with visualization support."""

    def __init__(self, L: int):
        self.L = L
        self.n_sites = L**3
        self.U = np.zeros((self.n_sites, 3, 2, 2), dtype=complex)
        self.cold_start()

        # Precompute site coordinates for visualization
        self.site_coords = np.array([self._coords(i) for i in range(self.n_sites)])

        # Precompute link endpoints
        self.link_endpoints = []
        for idx in range(self.n_sites):
            for mu in range(3):
                start = self.site_coords[idx]
                end = self.site_coords[self._neighbor(idx, mu)]
                # Handle periodic wrapping for visualization
                if end[mu] < start[mu]:
                    end = start + np.eye(3)[mu]  # Extend in direction mu
                self.link_endpoints.append((start.copy(), end.copy()))

    def _idx(self, x, y, z):
        L = self.L
        return ((x % L) * L + (y % L)) * L + (z % L)

    def _coords(self, idx):
        L = self.L
        z = idx % L
        y = (idx // L) % L
        x = idx // (L * L)
        return np.array([x, y, z], dtype=float)

    def _neighbor(self, idx, mu, forward=True):
        x, y, z = self._coords(idx).astype(int)
        L = self.L
        d = 1 if forward else -1
        if mu == 0:
            return self._idx((x + d) % L, y, z)
        elif mu == 1:
            return self._idx(x, (y + d) % L, z)
        else:
            return self._idx(x, y, (z + d) % L)

    def cold_start(self):
        for i in range(self.n_sites):
            for mu in range(3):
                a = np.array([1.0, 0.001*np.random.randn(),
                              0.001*np.random.randn(), 0.001*np.random.randn()])
                a = a / np.linalg.norm(a)
                self.U[i, mu] = quaternion_to_su2(a)

    def hot_start(self):
        for i in range(self.n_sites):
            for mu in range(3):
                self.U[i, mu] = su2_random()

    def plaquette(self, idx, mu, nu):
        U1 = self.U[idx, mu]
        idx_mu = self._neighbor(idx, mu)
        U2 = self.U[idx_mu, nu]
        idx_nu = self._neighbor(idx, nu)
        U3 = self.U[idx_nu, mu].conj().T
        U4 = self.U[idx, nu].conj().T
        P = U1 @ U2 @ U3 @ U4
        return 0.5 * np.real(np.trace(P))

    def average_plaquette(self):
        total = 0.0
        count = 0
        for idx in range(self.n_sites):
            for mu in range(3):
                for nu in range(mu + 1, 3):
                    total += self.plaquette(idx, mu, nu)
                    count += 1
        return total / count

    def link_plaquette_values(self) -> np.ndarray:
        """Compute average plaquette value touching each link."""
        values = []
        for idx in range(self.n_sites):
            for mu in range(3):
                # Average plaquettes containing this link
                plaq_sum = 0.0
                count = 0
                for nu in range(3):
                    if nu != mu:
                        plaq_sum += self.plaquette(idx, mu, nu)
                        count += 1
                values.append(plaq_sum / count if count > 0 else 0.5)
        return np.array(values)

    def staple(self, idx, mu):
        staple_sum = np.zeros((2, 2), dtype=complex)
        for nu in range(3):
            if nu == mu:
                continue
            idx_mu = self._neighbor(idx, mu)
            idx_nu = self._neighbor(idx, nu)
            U1 = self.U[idx_mu, nu]
            U2 = self.U[idx_nu, mu].conj().T
            U3 = self.U[idx, nu].conj().T
            staple_sum += U1 @ U2 @ U3

            idx_nu_back = self._neighbor(idx, nu, forward=False)
            idx_mu_nu_back = self._neighbor(idx_mu, nu, forward=False)
            U1 = self.U[idx_mu_nu_back, nu].conj().T
            U2 = self.U[idx_nu_back, mu].conj().T
            U3 = self.U[idx_nu_back, nu]
            staple_sum += U1 @ U2 @ U3
        return staple_sum

    def wilson_action(self, beta):
        total = 0.0
        for idx in range(self.n_sites):
            for mu in range(3):
                for nu in range(mu + 1, 3):
                    total += 1.0 - self.plaquette(idx, mu, nu)
        return beta * total

    def copy(self):
        new = VisualLattice(self.L)
        new.U = self.U.copy()
        return new

    def get_frame(self, trajectory: int) -> LatticeFrame:
        """Capture current state as a frame."""
        return LatticeFrame(
            trajectory=trajectory,
            avg_plaquette=self.average_plaquette(),
            link_plaquettes=self.link_plaquette_values(),
            site_coords=self.site_coords.copy(),
            link_endpoints=self.link_endpoints.copy()
        )


# ============================================================================
# HMC WITH RECORDING
# ============================================================================

class VisualHMC:
    """HMC with frame recording for animation."""

    def __init__(self, L: int, beta: float = 2.2,
                 n_leapfrog: int = 20, dt: float = 0.05):
        self.L = L
        self.beta = beta
        self.n_leapfrog = n_leapfrog
        self.dt = dt
        self.gauge = VisualLattice(L)
        self.n_accepted = 0
        self.n_total = 0
        self.frames: List[LatticeFrame] = []

    def _random_momentum(self):
        a = np.random.randn(3)
        sigma = [
            np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex)
        ]
        return 1j * sum(a[i] * sigma[i] for i in range(3))

    def _kinetic_energy(self, pi):
        K = 0.0
        for idx in range(self.gauge.n_sites):
            for mu in range(3):
                K -= 0.5 * np.real(np.trace(pi[idx][mu] @ pi[idx][mu]))
        return K

    def _force(self, idx, mu):
        U = self.gauge.U[idx, mu]
        staple = self.gauge.staple(idx, mu)
        X = (self.beta / 2) * U @ staple
        F = 0.5 * (X - X.conj().T)
        F = F - np.trace(F) / 2 * np.eye(2)
        return F

    def _leapfrog(self, pi):
        dt = self.dt
        for _ in range(self.n_leapfrog):
            for idx in range(self.gauge.n_sites):
                for mu in range(3):
                    F = self._force(idx, mu)
                    pi[idx][mu] = pi[idx][mu] - 0.5 * dt * F

            for idx in range(self.gauge.n_sites):
                for mu in range(3):
                    U_old = self.gauge.U[idx, mu]
                    exp_pi = su2_exp(dt * pi[idx][mu])
                    self.gauge.U[idx, mu] = su2_project(exp_pi @ U_old)

            for idx in range(self.gauge.n_sites):
                for mu in range(3):
                    F = self._force(idx, mu)
                    pi[idx][mu] = pi[idx][mu] - 0.5 * dt * F

    def trajectory(self):
        gauge_old = self.gauge.copy()
        pi = [[self._random_momentum() for _ in range(3)]
              for _ in range(self.gauge.n_sites)]

        K_old = self._kinetic_energy(pi)
        S_old = self.gauge.wilson_action(self.beta)
        H_old = K_old + S_old

        self._leapfrog(pi)

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

    def run(self, n_traj: int, n_therm: int, start: str = 'hot',
            record_interval: int = 2, verbose: bool = True):
        """Run simulation and record frames."""

        if start == 'hot':
            self.gauge.hot_start()
        else:
            self.gauge.cold_start()

        # Record initial frame
        self.frames = [self.gauge.get_frame(0)]

        if verbose:
            print(f"L={self.L}³, β={self.beta}, start={start}")
            print(f"Initial ⟨P⟩ = {self.frames[0].avg_plaquette:.4f}")

        # Thermalization
        for i in range(n_therm):
            self.trajectory()
            if (i + 1) % record_interval == 0:
                self.frames.append(self.gauge.get_frame(i + 1))
            if verbose and (i + 1) % 20 == 0:
                rate = self.n_accepted / self.n_total
                plaq = self.gauge.average_plaquette()
                print(f"  Therm {i+1}/{n_therm}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        # Production
        prod_acc = 0
        prod_tot = 0
        for i in range(n_traj):
            acc = self.trajectory()
            prod_acc += int(acc)
            prod_tot += 1
            traj_num = n_therm + i + 1
            if (i + 1) % record_interval == 0:
                self.frames.append(self.gauge.get_frame(traj_num))
            if verbose and (i + 1) % 50 == 0:
                rate = prod_acc / prod_tot
                plaq = self.gauge.average_plaquette()
                print(f"  Prod {i+1}/{n_traj}: ⟨P⟩={plaq:.4f}, acc={rate:.1%}")

        if verbose:
            print(f"Recorded {len(self.frames)} frames")

        return self.frames


# ============================================================================
# 3D VISUALIZATION
# ============================================================================

def create_3d_animation(frames: List[LatticeFrame], L: int,
                        title: str, output_html: str) -> go.Figure:
    """Create 3D animated visualization of the lattice."""

    # Use a slice of the lattice for clarity (show one z-plane)
    z_slice = L // 2

    # Create figure with subplots
    fig = make_subplots(
        rows=1, cols=2,
        specs=[[{"type": "scene"}, {"type": "xy"}]],
        subplot_titles=("3D Lattice (z-slice)", "Plaquette Evolution"),
        column_widths=[0.55, 0.45],
        horizontal_spacing=0.08
    )

    # Precompute plaquette history
    plaq_history = [f.avg_plaquette for f in frames]
    traj_history = [f.trajectory for f in frames]

    # Running average
    window = 10
    running_avg = [np.mean(plaq_history[max(0, i-window+1):i+1])
                   for i in range(len(plaq_history))]

    # Equilibrium (from second half)
    equil = np.mean(plaq_history[len(plaq_history)//2:])

    # Build animation frames
    animation_frames = []

    for frame_idx, frame in enumerate(frames):
        frame_data = []

        # --- 3D Lattice visualization ---

        # Filter links in the z-slice
        link_x, link_y, link_z = [], [], []
        link_colors = []

        n_sites = L ** 3
        link_idx = 0
        for idx in range(n_sites):
            coords = frame.site_coords[idx]
            for mu in range(3):
                start, end = frame.link_endpoints[link_idx]

                # Only show links in or near the z-slice
                if abs(start[2] - z_slice) < 0.5 or abs(end[2] - z_slice) < 0.5:
                    # Add line segment with None separator
                    link_x.extend([start[0], end[0], None])
                    link_y.extend([start[1], end[1], None])
                    link_z.extend([start[2], end[2], None])

                    # Color based on plaquette value
                    plaq_val = np.clip(frame.link_plaquettes[link_idx], 0, 1)
                    link_colors.extend([plaq_val, plaq_val, None])

                link_idx += 1

        # Create link traces with color gradient
        # We need to create individual segments for proper coloring
        link_segments = []
        seg_idx = 0
        temp_x, temp_y, temp_z = [], [], []
        temp_colors = []

        for i in range(0, len(link_x), 3):
            if link_x[i] is not None:
                plaq_val = link_colors[i] if link_colors[i] is not None else 0.5

                # Color mapping: red (0) -> yellow (0.5) -> green (1)
                if plaq_val < 0.5:
                    r, g, b = 255, int(255 * plaq_val * 2), 50
                else:
                    r, g, b = int(255 * (1 - (plaq_val - 0.5) * 2)), 255, 50

                color = f'rgb({r},{g},{b})'
                width = 3 + 4 * plaq_val

                seg_trace = go.Scatter3d(
                    x=[link_x[i], link_x[i+1]],
                    y=[link_y[i], link_y[i+1]],
                    z=[link_z[i], link_z[i+1]],
                    mode='lines',
                    line=dict(color=color, width=width),
                    showlegend=False,
                    hoverinfo='skip'
                )
                frame_data.append(seg_trace)

        # Add site markers
        slice_mask = np.abs(frame.site_coords[:, 2] - z_slice) < 0.5
        slice_coords = frame.site_coords[slice_mask]

        site_trace = go.Scatter3d(
            x=slice_coords[:, 0],
            y=slice_coords[:, 1],
            z=slice_coords[:, 2],
            mode='markers',
            marker=dict(size=6, color='white', opacity=0.8,
                       line=dict(width=1, color='gray')),
            showlegend=False,
            hoverinfo='skip'
        )
        frame_data.append(site_trace)

        # --- Plaquette evolution plot ---

        # Raw plaquette (faded)
        plaq_raw = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=plaq_history[:frame_idx+1],
            mode='lines',
            line=dict(color='rgba(100,150,255,0.3)', width=1),
            name='Raw',
            showlegend=False
        )
        frame_data.append(plaq_raw)

        # Running average
        plaq_avg = go.Scatter(
            x=traj_history[:frame_idx+1],
            y=running_avg[:frame_idx+1],
            mode='lines',
            line=dict(color='yellow', width=3),
            name='Running Avg'
        )
        frame_data.append(plaq_avg)

        # Current point
        current = go.Scatter(
            x=[traj_history[frame_idx]],
            y=[plaq_history[frame_idx]],
            mode='markers',
            marker=dict(size=12, color='red', symbol='circle'),
            name='Current'
        )
        frame_data.append(current)

        # Equilibrium line
        equil_line = go.Scatter(
            x=[0, max(traj_history)],
            y=[equil, equil],
            mode='lines',
            line=dict(color='lime', width=2, dash='dot'),
            name=f'Equil: {equil:.3f}'
        )
        frame_data.append(equil_line)

        animation_frames.append(go.Frame(data=frame_data, name=str(frame_idx)))

    # Add initial traces
    fig.add_traces(animation_frames[0].data)
    fig.frames = animation_frames

    # Layout
    fig.update_layout(
        title=dict(
            text=f"<b>{title}</b><br><sup>Links colored by plaquette: red=disordered, green=ordered</sup>",
            x=0.5, font=dict(size=18)
        ),
        scene=dict(
            xaxis=dict(title='X', range=[-0.5, L-0.5], showbackground=True,
                      backgroundcolor='rgb(20,20,35)', gridcolor='rgba(100,100,100,0.3)'),
            yaxis=dict(title='Y', range=[-0.5, L-0.5], showbackground=True,
                      backgroundcolor='rgb(20,20,35)', gridcolor='rgba(100,100,100,0.3)'),
            zaxis=dict(title='Z', range=[-0.5, L-0.5], showbackground=True,
                      backgroundcolor='rgb(20,20,35)', gridcolor='rgba(100,100,100,0.3)'),
            camera=dict(eye=dict(x=1.8, y=1.8, z=1.2)),
            aspectmode='cube'
        ),
        xaxis=dict(title='Trajectory', domain=[0.58, 1.0], gridcolor='rgba(100,100,100,0.3)'),
        yaxis=dict(title='⟨Plaquette⟩', range=[0, 1.05], domain=[0.1, 0.9],
                   gridcolor='rgba(100,100,100,0.3)'),
        paper_bgcolor='rgb(15,15,30)',
        plot_bgcolor='rgb(25,25,45)',
        font=dict(color='white', size=12),
        showlegend=False,
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
            currentvalue=dict(prefix='Trajectory: ', visible=True, xanchor='right',
                             font=dict(size=14)),
            pad=dict(b=10, t=50), len=0.9, x=0.05, y=0,
            steps=[dict(args=[[str(i)], dict(frame=dict(duration=100, redraw=True),
                                            mode='immediate')],
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
    print("=" * 60)
    print("LATTICE QCD HMC - 3D VISUALIZATION")
    print("=" * 60)

    # Parameters - use smaller lattice for clearer 3D viz
    L = 4  # 4³ = 64 sites, cleaner visualization
    beta = 2.2
    n_therm = 80
    n_prod = 200

    output_dir = Path(__file__).parent / "plots"
    output_dir.mkdir(exist_ok=True)

    # Hot start simulation
    print("\n" + "-" * 40)
    print("HOT START")
    print("-" * 40)
    hmc_hot = VisualHMC(L, beta=beta, n_leapfrog=15, dt=0.07)
    frames_hot = hmc_hot.run(n_prod, n_therm, start='hot',
                             record_interval=2, verbose=True)

    print("\nCreating 3D animation...")
    create_3d_animation(frames_hot, L, "Lattice QCD: Hot Start Thermalization",
                       str(output_dir / "lattice_3d_hot.html"))

    # Cold start simulation
    print("\n" + "-" * 40)
    print("COLD START")
    print("-" * 40)
    hmc_cold = VisualHMC(L, beta=beta, n_leapfrog=15, dt=0.07)
    frames_cold = hmc_cold.run(n_prod, n_therm, start='cold',
                               record_interval=2, verbose=True)

    print("\nCreating 3D animation...")
    create_3d_animation(frames_cold, L, "Lattice QCD: Cold Start Thermalization",
                       str(output_dir / "lattice_3d_cold.html"))

    # Summary
    print("\n" + "=" * 60)
    print("COMPLETE")
    print("=" * 60)
    print(f"\nOutput files in {output_dir}/:")
    print("  - lattice_3d_hot.html   (hot start 3D animation)")
    print("  - lattice_3d_cold.html  (cold start 3D animation)")
    print("\nOpen in browser to view interactive 3D animations!")


if __name__ == "__main__":
    main()

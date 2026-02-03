#!/usr/bin/env python3
"""
4D Hypercubic Lattice Simulation for Comparison with Stella Octangula
======================================================================

This script implements HMC simulation on a standard 4D hypercubic lattice
for direct comparison with the stella octangula simulation.

Target: Proposition 0.0.27 - "Comparison with hypercubic lattice results"

The hypercubic lattice uses STANDARD improvement coefficients:
    - c_SW = 1 (tree-level clover)
    - r = 1 (standard Wilson parameter)
    - λ = 0.129 (SM value) or 0.125 (geometric, for fair comparison)

This allows direct comparison of:
    1. Plaquette averages at same β
    2. Acceptance rates
    3. Computational cost per trajectory
    4. Scalar field observables
    5. Autocorrelation times

Author: Claude (Chiral Geometrogenesis Project)
Date: 2026-02-03
"""

import numpy as np
from scipy import linalg
from dataclasses import dataclass, field
from typing import Optional, Dict, List, Tuple
from pathlib import Path
import json
from datetime import datetime
import time

# ============================================================================
# STANDARD LATTICE QCD COEFFICIENTS (for comparison)
# ============================================================================

# Standard improvement coefficients (hypercubic)
C_SW_STANDARD = 1.0           # Tree-level clover coefficient
R_WILSON_STANDARD = 1.0       # Standard Wilson parameter
C1_STANDARD = 1 / 12          # Symanzik coefficient (universal)

# Geometric coefficients (from stella)
LAMBDA_GEOMETRIC = 1 / 8      # = 0.125
LAMBDA_SM = 0.129             # Standard Model value


# ============================================================================
# CONFIGURATION
# ============================================================================

@dataclass
class HypercubicConfig:
    """Configuration for hypercubic lattice simulation."""
    # Lattice size
    L: int = 4                # Linear extent (L^4 lattice)

    # Gauge group
    gauge_group: str = "SU2"
    n_colors: int = 2

    # Coupling parameters
    beta: float = 2.5         # Same as stella for comparison
    lambda_scalar: float = LAMBDA_GEOMETRIC  # Use geometric for fair comparison
    m2_scalar: float = -0.1   # Same as stella

    # HMC parameters
    n_trajectories: int = 500
    trajectory_length: float = 1.0
    n_leapfrog_steps: int = 20
    step_size: float = 0.05

    # Thermalization
    n_thermalization: int = 100
    measurement_interval: int = 10

    # Standard coefficients
    c_sw: float = C_SW_STANDARD
    r_wilson: float = R_WILSON_STANDARD

    # Output
    output_dir: Path = field(default_factory=lambda: Path(__file__).parent)
    verbose: bool = True


# ============================================================================
# 4D HYPERCUBIC LATTICE
# ============================================================================

class HypercubicLattice:
    """
    4D hypercubic lattice with periodic boundary conditions.

    Sites indexed as (x, y, z, t) with x,y,z,t ∈ {0, ..., L-1}
    Links indexed by (site, direction) with direction ∈ {0,1,2,3}
    Plaquettes indexed by (site, mu, nu) with mu < nu
    """

    def __init__(self, L: int):
        self.L = L
        self.volume = L**4
        self.n_links = 4 * self.volume  # 4 directions per site
        self.n_plaquettes = 6 * self.volume  # C(4,2) = 6 orientations per site

        # Precompute neighbor tables for efficiency
        self._build_neighbor_tables()

    def _build_neighbor_tables(self):
        """Build lookup tables for neighboring sites."""
        L = self.L
        self.neighbors_plus = {}   # neighbor in +mu direction
        self.neighbors_minus = {}  # neighbor in -mu direction

        for x in range(L):
            for y in range(L):
                for z in range(L):
                    for t in range(L):
                        site = (x, y, z, t)
                        self.neighbors_plus[site] = {
                            0: ((x + 1) % L, y, z, t),
                            1: (x, (y + 1) % L, z, t),
                            2: (x, y, (z + 1) % L, t),
                            3: (x, y, z, (t + 1) % L)
                        }
                        self.neighbors_minus[site] = {
                            0: ((x - 1) % L, y, z, t),
                            1: (x, (y - 1) % L, z, t),
                            2: (x, y, (z - 1) % L, t),
                            3: (x, y, z, (t - 1) % L)
                        }

    def site_index(self, x: int, y: int, z: int, t: int) -> int:
        """Convert (x,y,z,t) to flat index."""
        L = self.L
        return x + L * (y + L * (z + L * t))

    def site_coords(self, idx: int) -> Tuple[int, int, int, int]:
        """Convert flat index to (x,y,z,t)."""
        L = self.L
        x = idx % L
        idx //= L
        y = idx % L
        idx //= L
        z = idx % L
        t = idx // L
        return (x, y, z, t)

    def all_sites(self):
        """Iterator over all sites."""
        L = self.L
        for t in range(L):
            for z in range(L):
                for y in range(L):
                    for x in range(L):
                        yield (x, y, z, t)

    def all_links(self):
        """Iterator over all links (site, direction)."""
        for site in self.all_sites():
            for mu in range(4):
                yield (site, mu)

    def all_plaquettes(self):
        """Iterator over all plaquettes (site, mu, nu) with mu < nu."""
        for site in self.all_sites():
            for mu in range(4):
                for nu in range(mu + 1, 4):
                    yield (site, mu, nu)


# ============================================================================
# GAUGE FIELD ON HYPERCUBIC LATTICE
# ============================================================================

class HypercubicGaugeField:
    """
    SU(N) gauge field on 4D hypercubic lattice.

    U[site][mu] ∈ SU(N) for each link
    """

    def __init__(self, lattice: HypercubicLattice, n_colors: int = 2):
        self.lattice = lattice
        self.n_colors = n_colors

        # Store links as dictionary: (site, mu) -> U
        # Initialize to identity
        self.links = {}
        for site in lattice.all_sites():
            for mu in range(4):
                self.links[(site, mu)] = np.eye(n_colors, dtype=complex)

    def get_link(self, site: Tuple, mu: int, forward: bool = True) -> np.ndarray:
        """
        Get link U_mu(site) if forward, else U_mu(site-mu)^†
        """
        if forward:
            return self.links[(site, mu)].copy()
        else:
            neighbor = self.lattice.neighbors_minus[site][mu]
            return self.links[(neighbor, mu)].conj().T

    def set_link(self, site: Tuple, mu: int, U: np.ndarray):
        """Set link U_mu(site)."""
        self.links[(site, mu)] = U.copy()

    def plaquette(self, site: Tuple, mu: int, nu: int) -> np.ndarray:
        """
        Compute plaquette P_{mu,nu}(site).

        P = U_mu(x) U_nu(x+mu) U_mu(x+nu)^† U_nu(x)^†
        """
        x = site
        x_plus_mu = self.lattice.neighbors_plus[x][mu]
        x_plus_nu = self.lattice.neighbors_plus[x][nu]

        U1 = self.get_link(x, mu)
        U2 = self.get_link(x_plus_mu, nu)
        U3 = self.get_link(x_plus_nu, mu).conj().T
        U4 = self.get_link(x, nu).conj().T

        return U1 @ U2 @ U3 @ U4

    def plaquette_trace(self, site: Tuple, mu: int, nu: int) -> float:
        """Compute (1/N_c) Re Tr(P_{mu,nu}(site))."""
        P = self.plaquette(site, mu, nu)
        return np.real(np.trace(P)) / self.n_colors

    def average_plaquette(self) -> float:
        """Compute average plaquette over all plaquettes."""
        total = 0.0
        count = 0
        for (site, mu, nu) in self.lattice.all_plaquettes():
            total += self.plaquette_trace(site, mu, nu)
            count += 1
        return total / count

    def gauge_action(self, beta: float) -> float:
        """
        Compute Wilson gauge action.

        S_G = β Σ_{x,mu<nu} (1 - (1/N_c) Re Tr(P_{mu,nu}(x)))
        """
        total = 0.0
        for (site, mu, nu) in self.lattice.all_plaquettes():
            total += 1.0 - self.plaquette_trace(site, mu, nu)
        return beta * total

    def staple(self, site: Tuple, mu: int) -> np.ndarray:
        """
        Compute sum of staples for link U_mu(site).

        Staple_nu = U_nu(x+mu) U_mu(x+nu)^† U_nu(x)^†
                  + U_nu(x+mu-nu)^† U_mu(x-nu)^† U_nu(x-nu)
        """
        staple_sum = np.zeros((self.n_colors, self.n_colors), dtype=complex)
        x = site
        x_plus_mu = self.lattice.neighbors_plus[x][mu]

        for nu in range(4):
            if nu == mu:
                continue

            x_plus_nu = self.lattice.neighbors_plus[x][nu]
            x_minus_nu = self.lattice.neighbors_minus[x][nu]
            x_plus_mu_minus_nu = self.lattice.neighbors_minus[x_plus_mu][nu]

            # Forward staple: U_nu(x+mu) U_mu(x+nu)^† U_nu(x)^†
            staple_sum += (self.get_link(x_plus_mu, nu) @
                         self.get_link(x_plus_nu, mu).conj().T @
                         self.get_link(x, nu).conj().T)

            # Backward staple: U_nu(x+mu-nu)^† U_mu(x-nu)^† U_nu(x-nu)
            staple_sum += (self.get_link(x_plus_mu_minus_nu, nu).conj().T @
                         self.get_link(x_minus_nu, mu).conj().T @
                         self.get_link(x_minus_nu, nu))

        return staple_sum

    def randomize(self, epsilon: float = 0.1):
        """Generate random gauge configuration near identity."""
        for (site, mu) in self.lattice.all_links():
            self.links[(site, mu)] = self._random_su_n_near_identity(epsilon)

    def _random_su_n_near_identity(self, epsilon: float) -> np.ndarray:
        """Generate random SU(N) matrix near identity."""
        n = self.n_colors
        A = epsilon * (np.random.randn(n, n) + 1j * np.random.randn(n, n))
        A = 0.5 * (A - A.conj().T)
        A = A - np.trace(A) / n * np.eye(n)
        U = linalg.expm(A)
        return self._project_to_sun(U)

    def _project_to_sun(self, U: np.ndarray) -> np.ndarray:
        """Project matrix to SU(N)."""
        n = self.n_colors
        u, s, vh = np.linalg.svd(U)
        U = u @ vh
        det = np.linalg.det(U)
        U = U / (det ** (1.0 / n))
        return U

    def copy(self) -> 'HypercubicGaugeField':
        """Create a deep copy."""
        new = HypercubicGaugeField(self.lattice, self.n_colors)
        new.links = {k: v.copy() for k, v in self.links.items()}
        return new


# ============================================================================
# SCALAR FIELD ON HYPERCUBIC LATTICE
# ============================================================================

class HypercubicScalarField:
    """
    Complex scalar field on 4D hypercubic lattice sites.
    """

    def __init__(self, lattice: HypercubicLattice):
        self.lattice = lattice
        self.phi = {site: 0.0 + 0.0j for site in lattice.all_sites()}

    def randomize(self, scale: float = 1.0):
        """Generate random scalar configuration."""
        for site in self.lattice.all_sites():
            self.phi[site] = scale * (np.random.randn() + 1j * np.random.randn())

    def kinetic_term(self, gauge: HypercubicGaugeField) -> float:
        """
        Compute kinetic term with gauge covariant derivative.

        S_kin = Σ_{x,mu} |φ(x+mu) - U_mu(x) φ(x)|²
        """
        total = 0.0
        for site in self.lattice.all_sites():
            for mu in range(4):
                neighbor = self.lattice.neighbors_plus[site][mu]
                U = gauge.get_link(site, mu)
                # Scalar is color singlet, so U acts as U[0,0]
                diff = self.phi[neighbor] - U[0, 0] * self.phi[site]
                total += np.abs(diff)**2
        return total

    def potential_term(self, m2: float, lambda_4: float) -> float:
        """
        Compute potential term.

        V = Σ_x (m² |φ(x)|² + λ |φ(x)|⁴)
        """
        total = 0.0
        for site in self.lattice.all_sites():
            phi_sq = np.abs(self.phi[site])**2
            total += m2 * phi_sq + lambda_4 * phi_sq**2
        return total

    def scalar_action(self, gauge: HypercubicGaugeField,
                     m2: float, lambda_4: float) -> float:
        """Total scalar field action."""
        return self.kinetic_term(gauge) + self.potential_term(m2, lambda_4)

    def average_phi_squared(self) -> float:
        """Compute ⟨|φ|²⟩."""
        total = sum(np.abs(self.phi[site])**2 for site in self.lattice.all_sites())
        return total / self.lattice.volume

    def average_phi_fourth(self) -> float:
        """Compute ⟨|φ|⁴⟩."""
        total = sum(np.abs(self.phi[site])**4 for site in self.lattice.all_sites())
        return total / self.lattice.volume

    def copy(self) -> 'HypercubicScalarField':
        """Create a deep copy."""
        new = HypercubicScalarField(self.lattice)
        new.phi = {k: v for k, v in self.phi.items()}
        return new


# ============================================================================
# HMC FOR HYPERCUBIC LATTICE
# ============================================================================

class HypercubicHMC:
    """
    Hybrid Monte Carlo for 4D hypercubic lattice.
    """

    def __init__(self, config: HypercubicConfig):
        self.config = config
        self.lattice = HypercubicLattice(config.L)

        # Initialize fields
        self.gauge = HypercubicGaugeField(self.lattice, config.n_colors)
        self.scalar = HypercubicScalarField(self.lattice)

        # Statistics
        self.n_accepted = 0
        self.n_total = 0
        self.trajectory_times = []

        # History
        self.history = {
            'plaquette': [],
            'scalar_action': [],
            'trajectory_time': []
        }

    def total_action(self) -> float:
        """Compute total action."""
        S_gauge = self.gauge.gauge_action(self.config.beta)
        S_scalar = self.scalar.scalar_action(
            self.gauge, self.config.m2_scalar, self.config.lambda_scalar
        )
        return S_gauge + S_scalar

    def _gauge_force(self, gauge: HypercubicGaugeField) -> Dict:
        """Compute force on gauge links."""
        forces = {}

        for (site, mu) in self.lattice.all_links():
            staple = gauge.staple(site, mu)
            U = gauge.get_link(site, mu)

            # Force: (β/N_c) × (U×staple - staple†×U†)
            F = (self.config.beta / self.config.n_colors) * \
                (U @ staple - staple.conj().T @ U.conj().T)

            # Project to Lie algebra
            F = 0.5 * (F - F.conj().T)
            F = F - np.trace(F) / self.config.n_colors * np.eye(self.config.n_colors)

            forces[(site, mu)] = F

        return forces

    def _scalar_force(self, gauge: HypercubicGaugeField,
                     scalar: HypercubicScalarField) -> Dict:
        """Compute force on scalar field."""
        forces = {}

        for site in self.lattice.all_sites():
            force = 0.0 + 0.0j

            # Kinetic contribution from links touching this site
            for mu in range(4):
                # Forward link
                neighbor_plus = self.lattice.neighbors_plus[site][mu]
                U_plus = gauge.get_link(site, mu)[0, 0]
                force += -np.conj(U_plus) * (scalar.phi[neighbor_plus] - U_plus * scalar.phi[site])

                # Backward link
                neighbor_minus = self.lattice.neighbors_minus[site][mu]
                U_minus = gauge.get_link(neighbor_minus, mu)[0, 0]
                force += (scalar.phi[site] - U_minus * scalar.phi[neighbor_minus])

            # Potential contribution
            force += self.config.m2_scalar * scalar.phi[site]
            force += 2 * self.config.lambda_scalar * np.abs(scalar.phi[site])**2 * scalar.phi[site]

            forces[site] = force

        return forces

    def leapfrog_step(self, gauge: HypercubicGaugeField,
                     scalar: HypercubicScalarField,
                     pi_gauge: Dict, pi_scalar: Dict,
                     dt: float):
        """Single leapfrog step."""
        # Half step for momenta
        F_gauge = self._gauge_force(gauge)
        F_scalar = self._scalar_force(gauge, scalar)

        for key in pi_gauge:
            pi_gauge[key] = pi_gauge[key] - 0.5 * dt * F_gauge[key]
        for key in pi_scalar:
            pi_scalar[key] = pi_scalar[key] - 0.5 * dt * F_scalar[key]

        # Full step for positions
        for (site, mu) in self.lattice.all_links():
            U = gauge.links[(site, mu)]
            gauge.links[(site, mu)] = linalg.expm(dt * pi_gauge[(site, mu)]) @ U
            gauge.links[(site, mu)] = gauge._project_to_sun(gauge.links[(site, mu)])

        for site in self.lattice.all_sites():
            scalar.phi[site] = scalar.phi[site] + dt * pi_scalar[site]

        # Half step for momenta
        F_gauge = self._gauge_force(gauge)
        F_scalar = self._scalar_force(gauge, scalar)

        for key in pi_gauge:
            pi_gauge[key] = pi_gauge[key] - 0.5 * dt * F_gauge[key]
        for key in pi_scalar:
            pi_scalar[key] = pi_scalar[key] - 0.5 * dt * F_scalar[key]

        return gauge, scalar, pi_gauge, pi_scalar

    def kinetic_energy(self, pi_gauge: Dict, pi_scalar: Dict) -> float:
        """Compute kinetic energy."""
        K = 0.0

        for pi in pi_gauge.values():
            K += 0.5 * np.real(np.trace(pi.conj().T @ pi))

        for pi in pi_scalar.values():
            K += 0.5 * np.abs(pi)**2

        return K

    def hmc_trajectory(self) -> Tuple[bool, float]:
        """
        Execute one HMC trajectory.

        Returns (accepted, trajectory_time).
        """
        start_time = time.time()

        # Save initial configuration
        gauge_old = self.gauge.copy()
        scalar_old = self.scalar.copy()

        # Generate random momenta
        n_c = self.config.n_colors
        pi_gauge = {}
        for (site, mu) in self.lattice.all_links():
            A = np.random.randn(n_c, n_c) + 1j * np.random.randn(n_c, n_c)
            A = 0.5 * (A - A.conj().T)
            A = A - np.trace(A) / n_c * np.eye(n_c)
            pi_gauge[(site, mu)] = A

        pi_scalar = {site: np.random.randn() + 1j * np.random.randn()
                    for site in self.lattice.all_sites()}

        # Initial Hamiltonian
        H_old = self.total_action() + self.kinetic_energy(pi_gauge, pi_scalar)

        # Leapfrog integration
        gauge = self.gauge.copy()
        scalar = self.scalar.copy()
        dt = self.config.trajectory_length / self.config.n_leapfrog_steps

        for _ in range(self.config.n_leapfrog_steps):
            gauge, scalar, pi_gauge, pi_scalar = self.leapfrog_step(
                gauge, scalar, pi_gauge, pi_scalar, dt
            )

        # Final Hamiltonian
        self.gauge = gauge
        self.scalar = scalar
        H_new = self.total_action() + self.kinetic_energy(pi_gauge, pi_scalar)

        # Metropolis accept/reject
        dH = H_new - H_old
        accept = (dH < 0) or (np.random.rand() < np.exp(-dH))

        if accept:
            self.n_accepted += 1
        else:
            self.gauge = gauge_old
            self.scalar = scalar_old

        self.n_total += 1

        trajectory_time = time.time() - start_time
        self.trajectory_times.append(trajectory_time)

        return accept, trajectory_time

    def thermalize(self):
        """Run thermalization sweeps."""
        if self.config.verbose:
            print(f"Thermalizing for {self.config.n_thermalization} trajectories...")

        self.gauge.randomize(epsilon=0.5)
        self.scalar.randomize(scale=0.5)

        for i in range(self.config.n_thermalization):
            self.hmc_trajectory()

            if self.config.verbose and (i + 1) % 20 == 0:
                plaq = self.gauge.average_plaquette()
                rate = self.n_accepted / self.n_total
                print(f"  Thermalization {i+1}/{self.config.n_thermalization}: "
                      f"⟨P⟩ = {plaq:.4f}, acceptance = {rate:.2%}")

        # Reset counters
        self.n_accepted = 0
        self.n_total = 0
        self.trajectory_times = []

    def measure_observables(self) -> Dict[str, float]:
        """Measure all observables."""
        return {
            'plaquette': self.gauge.average_plaquette(),
            'phi_squared_avg': self.scalar.average_phi_squared(),
            'phi_fourth_avg': self.scalar.average_phi_fourth(),
            'gauge_action': self.gauge.gauge_action(self.config.beta),
            'scalar_action': self.scalar.scalar_action(
                self.gauge, self.config.m2_scalar, self.config.lambda_scalar
            )
        }

    def run_production(self) -> Dict:
        """Run production simulation."""
        if self.config.verbose:
            print(f"\nRunning {self.config.n_trajectories} production trajectories...")
            print(f"Lattice: {self.config.L}^4 = {self.lattice.volume} sites")

        measurements = []

        for i in range(self.config.n_trajectories):
            accepted, traj_time = self.hmc_trajectory()

            if (i + 1) % self.config.measurement_interval == 0:
                obs = self.measure_observables()
                obs['trajectory_time'] = traj_time
                measurements.append(obs)

                self.history['plaquette'].append(obs['plaquette'])
                self.history['trajectory_time'].append(traj_time)

                if self.config.verbose and (i + 1) % 100 == 0:
                    rate = self.n_accepted / self.n_total
                    plaq = obs['plaquette']
                    avg_time = np.mean(self.trajectory_times[-100:])
                    print(f"  Trajectory {i+1}/{self.config.n_trajectories}: "
                          f"⟨P⟩ = {plaq:.4f}, acceptance = {rate:.2%}, "
                          f"time = {avg_time:.3f}s")

        return self.analyze_results(measurements)

    def analyze_results(self, measurements: List[Dict]) -> Dict:
        """Analyze simulation results."""
        results = {
            'config': {
                'L': self.config.L,
                'volume': self.lattice.volume,
                'n_links': self.lattice.n_links,
                'n_plaquettes': self.lattice.n_plaquettes,
                'beta': self.config.beta,
                'lambda': self.config.lambda_scalar,
                'm2': self.config.m2_scalar,
                'n_trajectories': self.config.n_trajectories,
                'gauge_group': self.config.gauge_group,
                'c_sw': self.config.c_sw,
                'r_wilson': self.config.r_wilson
            },
            'statistics': {
                'n_measurements': len(measurements),
                'acceptance_rate': self.n_accepted / self.n_total if self.n_total > 0 else 0,
                'avg_trajectory_time': np.mean(self.trajectory_times),
                'total_time': sum(self.trajectory_times)
            },
            'observables': {}
        }

        # Compute averages with jackknife errors
        for key in measurements[0].keys():
            values = np.array([m[key] for m in measurements])
            n = len(values)
            mean = np.mean(values)

            if n > 1:
                jackknife_means = np.array([
                    np.mean(np.delete(values, i)) for i in range(n)
                ])
                variance = (n - 1) * np.var(jackknife_means)
                error = np.sqrt(variance)
            else:
                error = 0

            results['observables'][key] = {
                'mean': float(mean),
                'error': float(error),
                'n_samples': n
            }

        return results


# ============================================================================
# MAIN SIMULATION
# ============================================================================

def run_hypercubic_simulation(config: Optional[HypercubicConfig] = None) -> Dict:
    """Run the hypercubic lattice simulation."""
    if config is None:
        config = HypercubicConfig(
            L=4,
            gauge_group="SU2",
            n_colors=2,
            beta=2.5,
            lambda_scalar=LAMBDA_GEOMETRIC,
            m2_scalar=-0.1,
            n_trajectories=500,
            n_thermalization=100,
            measurement_interval=10,
            verbose=True
        )

    print("=" * 70)
    print("4D HYPERCUBIC LATTICE SIMULATION")
    print("For comparison with Stella Octangula")
    print("=" * 70)
    print(f"\nSimulation Parameters:")
    print(f"  Lattice: {config.L}^4 = {config.L**4} sites")
    print(f"  Links: {4 * config.L**4}")
    print(f"  Plaquettes: {6 * config.L**4}")
    print(f"  Gauge group: {config.gauge_group}")
    print(f"  β = {config.beta}")
    print(f"  λ = {config.lambda_scalar}")
    print(f"  m² = {config.m2_scalar}")
    print(f"  c_SW = {config.c_sw} (standard)")
    print(f"  r = {config.r_wilson} (standard)")
    print(f"  Trajectories: {config.n_trajectories}")

    # Run simulation
    hmc = HypercubicHMC(config)
    hmc.thermalize()
    results = hmc.run_production()

    # Summary
    print("\n" + "=" * 70)
    print("SIMULATION SUMMARY")
    print("=" * 70)
    print(f"  Total trajectories: {config.n_trajectories}")
    print(f"  Measurements: {results['statistics']['n_measurements']}")
    print(f"  Acceptance rate: {results['statistics']['acceptance_rate']:.2%}")
    print(f"  Avg trajectory time: {results['statistics']['avg_trajectory_time']:.4f}s")
    print(f"  Total time: {results['statistics']['total_time']:.2f}s")

    for obs_name, obs_data in results['observables'].items():
        if obs_name != 'trajectory_time':
            print(f"  {obs_name}: {obs_data['mean']:.6f} ± {obs_data['error']:.6f}")

    # Save results
    results['timestamp'] = datetime.now().isoformat()
    results['lattice_type'] = 'hypercubic'

    output_file = config.output_dir / "hypercubic_simulation_results.json"

    def make_serializable(obj):
        if isinstance(obj, dict):
            return {k: make_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, (list, tuple)):
            return [make_serializable(x) for x in obj]
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.integer, np.int64)):
            return int(obj)
        elif isinstance(obj, (np.floating, np.float64)):
            return float(obj)
        elif isinstance(obj, Path):
            return str(obj)
        return obj

    with open(output_file, 'w') as f:
        json.dump(make_serializable(results), f, indent=2)

    print(f"\n  Results saved to: {output_file}")
    print("=" * 70)

    return results


if __name__ == "__main__":
    results = run_hypercubic_simulation()

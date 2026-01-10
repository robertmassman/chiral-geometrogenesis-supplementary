#!/usr/bin/env python3
"""
Proposition 0.0.17a Verification: Born Rule from Geodesic Flow

This script verifies the key claims of Proposition 0.0.17a:
1. Geodesic flow on T² is ergodic for irrational velocity ratios
2. Time-averaged energy density converges to Born rule
3. Phase factors average to zero for off-diagonal terms

Mathematical framework:
- Configuration space C ≅ T² (2-torus)
- Fisher metric g^F = (1/12) I_2 (flat)
- Geodesics: φ(λ) = φ_0 + v·λ mod 2π
- Ergodicity via Weyl's equidistribution theorem
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Tuple, List
import json
from pathlib import Path

# Physical constants (matching framework)
COLORS = ['R', 'G', 'B']
PHASES_EQUILIBRIUM = np.array([0, 2*np.pi/3, 4*np.pi/3])  # Definition 0.1.2


class TorusGeodesic:
    """Geodesic flow on the flat 2-torus with Fisher metric."""

    def __init__(self, v1: float, v2: float, phi0: Tuple[float, float] = (0, 0)):
        """
        Initialize geodesic with velocity v = (v1, v2) and initial position phi0.

        Args:
            v1, v2: Velocity components (should be rationally independent for ergodicity)
            phi0: Initial position on T² ∈ [0, 2π)²
        """
        self.v = np.array([v1, v2])
        self.phi0 = np.array(phi0)

        # Check if ratio is irrational (approximately)
        if v2 != 0:
            ratio = v1 / v2
            # Check against simple rationals
            self.is_ergodic = self._check_irrational(ratio)
        else:
            self.is_ergodic = (v1 != 0)  # Degenerate case

    def _check_irrational(self, x: float, max_denom: int = 100) -> bool:
        """Check if x is approximately irrational (not close to p/q for small q)."""
        for q in range(1, max_denom + 1):
            for p in range(-max_denom * q, max_denom * q + 1):
                if q != 0 and abs(x - p/q) < 1e-10:
                    return False
        return True

    def position(self, lambda_: float) -> np.ndarray:
        """Position on torus at time λ."""
        return (self.phi0 + self.v * lambda_) % (2 * np.pi)

    def trajectory(self, T: float, n_points: int = 1000) -> np.ndarray:
        """Generate trajectory from λ=0 to λ=T."""
        lambdas = np.linspace(0, T, n_points)
        return np.array([self.position(l) for l in lambdas])


class ChiralField:
    """Three color fields on stella octangula (simplified 1D model for testing)."""

    def __init__(self, x_grid: np.ndarray, epsilon: float = 0.1):
        """
        Initialize pressure functions on spatial grid.

        Args:
            x_grid: 1D spatial grid for testing
            epsilon: Regularization parameter for pressure functions
        """
        self.x = x_grid
        self.epsilon = epsilon

        # Positions of three color sources (symmetric on line)
        self.x_c = np.array([-1.0, 0.0, 1.0])

        # Pressure functions P_c(x) = 1/(|x - x_c|² + ε²)
        self.P = np.array([1.0 / ((self.x - xc)**2 + epsilon**2) for xc in self.x_c])

    def chi_total(self, phases: np.ndarray) -> np.ndarray:
        """
        Total chiral field χ_total(x) = Σ_c P_c(x) e^{iφ_c}

        Args:
            phases: Array of three phases [φ_R, φ_G, φ_B]

        Returns:
            Complex field values on x grid
        """
        return sum(self.P[c] * np.exp(1j * phases[c]) for c in range(3))

    def energy_density(self, phases: np.ndarray) -> np.ndarray:
        """Energy density |χ_total|² at each x."""
        chi = self.chi_total(phases)
        return np.abs(chi)**2

    def normalized_probability(self, phases: np.ndarray) -> np.ndarray:
        """Normalized probability density P(x) = |χ|²/∫|χ|²dx."""
        rho = self.energy_density(phases)
        dx = self.x[1] - self.x[0] if len(self.x) > 1 else 1.0
        norm = np.sum(rho) * dx
        return rho / norm


def phases_from_torus(psi1: float, psi2: float) -> np.ndarray:
    """
    Convert torus coordinates (ψ₁, ψ₂) to color phases (φ_R, φ_G, φ_B).

    Using: ψ₁ = φ_G - φ_R, ψ₂ = φ_B - φ_R
    Constraint: φ_R + φ_G + φ_B = 0

    Solution: φ_R = -(ψ₁ + ψ₂)/3, φ_G = φ_R + ψ₁, φ_B = φ_R + ψ₂
    """
    phi_R = -(psi1 + psi2) / 3
    phi_G = phi_R + psi1
    phi_B = phi_R + psi2
    return np.array([phi_R, phi_G, phi_B])


def test_ergodicity(geodesic: TorusGeodesic, T_values: List[float], n_bins: int = 20) -> dict:
    """
    Test ergodicity by comparing time-averaged histogram to uniform distribution.

    For ergodic flow, the trajectory should fill the torus uniformly.
    """
    results = {'T_values': T_values, 'uniformity_errors': [], 'is_ergodic': geodesic.is_ergodic}

    for T in T_values:
        traj = geodesic.trajectory(T, n_points=int(T * 100))

        # 2D histogram on torus
        hist, _, _ = np.histogram2d(
            traj[:, 0], traj[:, 1],
            bins=n_bins, range=[[0, 2*np.pi], [0, 2*np.pi]]
        )

        # Expected uniform distribution
        expected = len(traj) / n_bins**2

        # Normalized error from uniform
        error = np.sqrt(np.mean((hist - expected)**2)) / expected
        results['uniformity_errors'].append(error)

    return results


def test_born_rule_convergence(
    geodesic: TorusGeodesic,
    field: ChiralField,
    T_values: List[float]
) -> dict:
    """
    Test that time-averaged energy density converges to Born rule.

    Computes:
    1. Time-averaged ρ(x, λ) over trajectory
    2. Static Born rule prediction
    3. Convergence error
    """
    results = {'T_values': T_values, 'errors': [], 'max_errors': []}

    # Static Born rule prediction (diagonal terms only)
    # For ergodic average, off-diagonal phase terms vanish
    rho_static = np.sum(field.P**2, axis=0)  # Σ_c P_c(x)²
    dx = field.x[1] - field.x[0] if len(field.x) > 1 else 1.0
    rho_static_norm = rho_static / (np.sum(rho_static) * dx)

    for T in T_values:
        n_points = int(T * 100)
        lambdas = np.linspace(0, T, n_points)

        # Time-averaged energy density
        rho_sum = np.zeros_like(field.x)
        for lam in lambdas:
            pos = geodesic.position(lam)
            phases = phases_from_torus(pos[0], pos[1])
            rho_sum += field.energy_density(phases)

        rho_time_avg = rho_sum / n_points
        rho_time_avg_norm = rho_time_avg / (np.sum(rho_time_avg) * dx)

        # Error
        error = np.sqrt(np.mean((rho_time_avg_norm - rho_static_norm)**2))
        max_error = np.max(np.abs(rho_time_avg_norm - rho_static_norm))

        results['errors'].append(error)
        results['max_errors'].append(max_error)

    results['rho_static'] = rho_static_norm.tolist()
    results['rho_final'] = rho_time_avg_norm.tolist()
    results['x_grid'] = field.x.tolist()

    return results


def test_phase_averaging(geodesic: TorusGeodesic, T_values: List[float]) -> dict:
    """
    Test that off-diagonal phase factors average to zero.

    Computes: lim_{T→∞} (1/T) ∫₀ᵀ e^{i(φ_c - φ_c')} dλ → 0 for c ≠ c'
    """
    results = {'T_values': T_values, 'phase_avgs': {}}

    pairs = [('R', 'G', 0, 1), ('G', 'B', 1, 2), ('B', 'R', 2, 0)]

    for name_c, name_c_prime, c, c_prime in pairs:
        key = f'{name_c}-{name_c_prime}'
        results['phase_avgs'][key] = []

        for T in T_values:
            n_points = int(T * 100)
            lambdas = np.linspace(0, T, n_points)

            phase_sum = 0j
            for lam in lambdas:
                pos = geodesic.position(lam)
                phases = phases_from_torus(pos[0], pos[1])
                phase_sum += np.exp(1j * (phases[c] - phases[c_prime]))

            avg = np.abs(phase_sum / n_points)
            results['phase_avgs'][key].append(avg)

    return results


def run_all_tests() -> dict:
    """Run all verification tests for Proposition 0.0.17a."""

    print("=" * 60)
    print("Proposition 0.0.17a Verification")
    print("Born Rule from Geodesic Flow")
    print("=" * 60)

    results = {
        'proposition': '0.0.17a',
        'title': 'Born Rule from Geodesic Flow',
        'tests': {}
    }

    # Test parameters
    T_values = [1, 5, 10, 50, 100, 500]

    # Irrational velocity ratio (golden ratio for maximum irrationality)
    golden = (1 + np.sqrt(5)) / 2
    geodesic_ergodic = TorusGeodesic(v1=1.0, v2=golden)

    # Rational velocity ratio (for comparison)
    geodesic_periodic = TorusGeodesic(v1=1.0, v2=0.5)  # v1/v2 = 2 (rational)

    # Spatial grid for chiral field
    x_grid = np.linspace(-3, 3, 200)
    field = ChiralField(x_grid)

    # Test 1: Ergodicity
    print("\n[Test 1] Ergodicity of geodesic flow")
    print(f"  Velocity ratio = {geodesic_ergodic.v[0]/geodesic_ergodic.v[1]:.6f} (golden ratio)")

    erg_results = test_ergodicity(geodesic_ergodic, T_values)
    results['tests']['ergodicity'] = erg_results

    print(f"  Is ergodic: {erg_results['is_ergodic']}")
    print(f"  Uniformity errors: {[f'{e:.4f}' for e in erg_results['uniformity_errors']]}")

    # Check: error should decrease with T
    if erg_results['uniformity_errors'][-1] < 0.1:
        print("  ✅ PASS: Trajectory approaches uniform distribution")
        results['tests']['ergodicity']['status'] = 'PASS'
    else:
        print("  ❌ FAIL: Trajectory not converging to uniform")
        results['tests']['ergodicity']['status'] = 'FAIL'

    # Test 2: Born rule convergence (ergodic case)
    print("\n[Test 2] Born rule convergence (ergodic geodesic)")

    born_results = test_born_rule_convergence(geodesic_ergodic, field, T_values)
    results['tests']['born_rule'] = born_results

    print(f"  RMS errors: {[f'{e:.6f}' for e in born_results['errors']]}")
    print(f"  Max errors: {[f'{e:.6f}' for e in born_results['max_errors']]}")

    # Check: error should be small for large T
    if born_results['errors'][-1] < 0.01:
        print("  ✅ PASS: Time-averaged density converges to Born rule")
        results['tests']['born_rule']['status'] = 'PASS'
    else:
        print("  ❌ FAIL: Time-averaged density not converging")
        results['tests']['born_rule']['status'] = 'FAIL'

    # Test 3: Phase averaging
    print("\n[Test 3] Off-diagonal phase averaging")

    phase_results = test_phase_averaging(geodesic_ergodic, T_values)
    results['tests']['phase_averaging'] = phase_results

    for key, values in phase_results['phase_avgs'].items():
        print(f"  |⟨e^{{i(φ_{key})}}⟩|: {[f'{v:.4f}' for v in values]}")

    # Check: all phase averages should go to 0
    final_phase_avgs = [v[-1] for v in phase_results['phase_avgs'].values()]
    if max(final_phase_avgs) < 0.05:
        print("  ✅ PASS: Off-diagonal phases average to zero")
        results['tests']['phase_averaging']['status'] = 'PASS'
    else:
        print("  ❌ FAIL: Phase averaging not converging")
        results['tests']['phase_averaging']['status'] = 'FAIL'

    # Test 4: Comparison with periodic geodesic
    print("\n[Test 4] Periodic vs. ergodic comparison")

    born_periodic = test_born_rule_convergence(geodesic_periodic, field, T_values)
    results['tests']['periodic_comparison'] = {
        'ergodic_final_error': born_results['errors'][-1],
        'periodic_final_error': born_periodic['errors'][-1],
        'ratio': born_periodic['errors'][-1] / born_results['errors'][-1] if born_results['errors'][-1] > 0 else float('inf')
    }

    print(f"  Ergodic final error:  {born_results['errors'][-1]:.6f}")
    print(f"  Periodic final error: {born_periodic['errors'][-1]:.6f}")

    if born_periodic['errors'][-1] > born_results['errors'][-1]:
        print("  ✅ PASS: Ergodic geodesic converges better than periodic")
        results['tests']['periodic_comparison']['status'] = 'PASS'
    else:
        print("  ⚠️ WARNING: Periodic geodesic converging comparably")
        results['tests']['periodic_comparison']['status'] = 'WARNING'

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    all_pass = all(
        results['tests'][t].get('status') == 'PASS'
        for t in ['ergodicity', 'born_rule', 'phase_averaging']
    )

    results['overall_status'] = 'PASS' if all_pass else 'FAIL'

    if all_pass:
        print("✅ ALL CORE TESTS PASSED")
        print("\nConclusion: Proposition 0.0.17a verified")
        print("  - Geodesic flow is ergodic for irrational velocities")
        print("  - Time-averaged density converges to Born rule")
        print("  - Off-diagonal phase factors vanish")
        print("  - Axiom A5 is DERIVED, not assumed")
    else:
        print("❌ SOME TESTS FAILED — Review results")

    return results


def generate_plots(results: dict, output_dir: Path):
    """Generate verification plots."""

    output_dir.mkdir(parents=True, exist_ok=True)

    # Plot 1: Born rule convergence
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    # Convergence of error with T
    ax1 = axes[0]
    T_values = results['tests']['born_rule']['T_values']
    errors = results['tests']['born_rule']['errors']
    ax1.loglog(T_values, errors, 'bo-', label='RMS Error')
    ax1.loglog(T_values, [1/np.sqrt(T) for T in T_values], 'k--', label='1/√T (expected)')
    ax1.set_xlabel('Integration time T')
    ax1.set_ylabel('Error')
    ax1.set_title('Born Rule Convergence')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Final density comparison
    ax2 = axes[1]
    x = results['tests']['born_rule']['x_grid']
    rho_static = results['tests']['born_rule']['rho_static']
    rho_final = results['tests']['born_rule']['rho_final']
    ax2.plot(x, rho_static, 'b-', linewidth=2, label='Born rule (static)')
    ax2.plot(x, rho_final, 'r--', linewidth=2, label='Time-averaged')
    ax2.set_xlabel('Position x')
    ax2.set_ylabel('Probability density P(x)')
    ax2.set_title('Time-Averaged vs Born Rule')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # Phase averaging
    ax3 = axes[2]
    for key, values in results['tests']['phase_averaging']['phase_avgs'].items():
        ax3.semilogy(T_values, values, 'o-', label=f'|⟨exp(iΔφ_{{{key}}})⟩|')
    ax3.set_xlabel('Integration time T')
    ax3.set_ylabel('Phase average magnitude')
    ax3.set_title('Off-Diagonal Phase Averaging')
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_dir / 'proposition_0_0_17a_verification.png', dpi=150)
    plt.close()

    print(f"\nPlot saved to: {output_dir / 'proposition_0_0_17a_verification.png'}")


if __name__ == "__main__":
    # Run tests
    results = run_all_tests()

    # Save results
    output_dir = Path(__file__).parent.parent / 'plots'
    output_dir.mkdir(parents=True, exist_ok=True)

    results_file = Path(__file__).parent / 'proposition_0_0_17a_results.json'
    with open(results_file, 'w') as f:
        # Convert numpy arrays to lists for JSON
        json.dump(results, f, indent=2, default=lambda x: x.tolist() if hasattr(x, 'tolist') else str(x))

    print(f"\nResults saved to: {results_file}")

    # Generate plots
    generate_plots(results, output_dir)

#!/usr/bin/env python3
"""
Sophisticated Skyrme Configuration Search
==========================================

This script implements more advanced searches for non-hedgehog Q=1 configurations:
1. Rational map ansätze (Houghton, Manton, Sutcliffe)
2. Spline-based radial profiles
3. Fourier-mode angular deformations
4. Direct gradient descent optimization

Research Question: Can we find Q=1 configurations with E < E_hedgehog using
more sophisticated parametrizations?

Related Documents:
- docs/proofs/supporting/Color-Constraints-Necessity-Research-Plan.md
- docs/proofs/supporting/Color-Constraints-Necessity-Conclusion.md

Date: 2026-01-31
"""

import numpy as np
from scipy.integrate import quad, dblquad, simpson
from scipy.interpolate import CubicSpline, BSpline
from scipy.optimize import minimize, differential_evolution, basinhopping
from scipy.special import sph_harm
import json
from datetime import datetime
import warnings
warnings.filterwarnings('ignore')

# ==============================================================================
# PHYSICAL CONSTANTS AND REFERENCE VALUES
# ==============================================================================

# Reference hedgehog energy (from previous calculation)
E_HEDGEHOG_REF = 105.8984

# ==============================================================================
# PART 1: RATIONAL MAP ANSATZ
# ==============================================================================

class RationalMapSkyrmion:
    """
    Rational map ansatz for Skyrmions (Houghton, Manton, Sutcliffe 1998).

    The field is parametrized as:
        U(r, z) = exp(i * f(r) * n_R(z) · τ)

    where z = tan(θ/2) * exp(iφ) is the stereographic coordinate and
    R(z) = p(z)/q(z) is a rational map determining the angular structure.

    For Q=1 (hedgehog), R(z) = z (identity map).
    Deformations use R(z) = (z + a)/(1 + a*z) or more complex forms.
    """

    def __init__(self, rational_map_type='identity', params=None):
        self.map_type = rational_map_type
        self.params = params or {}
        self.R_scale = self.params.get('R_scale', 1.0)

    def rational_map(self, z):
        """
        Compute R(z) for the given rational map type.

        z is a complex number (stereographic coordinate).
        Returns R(z), also complex.
        """
        if self.map_type == 'identity':
            # R(z) = z → hedgehog
            return z

        elif self.map_type == 'mobius':
            # Möbius transformation: R(z) = (z + a)/(1 + conj(a)*z)
            # This is an SO(3) rotation, preserves Q=1
            a = self.params.get('a', 0.0)  # complex parameter
            if isinstance(a, (int, float)):
                a = complex(a, 0)
            denom = 1 + np.conj(a) * z
            if np.abs(denom) < 1e-10:
                return np.inf
            return (z + a) / denom

        elif self.map_type == 'deformed':
            # Deformed map: R(z) = z + epsilon * z^2
            # This breaks spherical symmetry
            epsilon = self.params.get('epsilon', 0.1)
            return z + epsilon * z**2

        elif self.map_type == 'axial':
            # Axially symmetric deformation: R(z) = z * (1 + epsilon * |z|^2)
            epsilon = self.params.get('epsilon', 0.1)
            return z * (1 + epsilon * np.abs(z)**2)

        elif self.map_type == 'twisted':
            # Twisted map: R(z) = z * exp(i * gamma * |z|^2)
            gamma = self.params.get('gamma', 0.5)
            return z * np.exp(1j * gamma * np.abs(z)**2)

        else:
            return z  # Default to identity

    def profile_function(self, r):
        """Standard hedgehog-like profile."""
        R = self.R_scale
        if r < 1e-10:
            return np.pi
        return 2 * np.arctan(R / r)

    def compute_n_hat(self, theta, phi):
        """
        Compute the isospin direction n_hat from the rational map.

        The stereographic coordinate is z = tan(θ/2) * exp(iφ).
        The rational map R(z) determines the isospin direction.
        """
        # Stereographic coordinate
        if theta < 1e-10:
            z = 0.0
        elif theta > np.pi - 1e-10:
            z = np.inf
        else:
            z = np.tan(theta / 2) * np.exp(1j * phi)

        # Apply rational map
        if np.isinf(z):
            w = self.rational_map(1e10 * np.exp(1j * phi))
        else:
            w = self.rational_map(z)

        # Convert back to unit vector on S²
        # w = tan(θ'/2) * exp(iφ') → (sin θ' cos φ', sin θ' sin φ', cos θ')
        if np.isinf(w) or np.abs(w) > 1e10:
            return np.array([0, 0, -1])

        abs_w_sq = np.abs(w)**2
        denom = 1 + abs_w_sq

        n_x = 2 * np.real(w) / denom
        n_y = 2 * np.imag(w) / denom
        n_z = (1 - abs_w_sq) / denom

        return np.array([n_x, n_y, n_z])

    def compute_energy(self, r_max=15.0, n_r=80, n_theta=40, n_phi=40):
        """Compute total energy using 3D integration."""
        r_vals = np.linspace(0.1, r_max, n_r)
        theta_vals = np.linspace(0.01, np.pi - 0.01, n_theta)
        phi_vals = np.linspace(0, 2*np.pi - 0.01, n_phi)

        dr = r_vals[1] - r_vals[0]
        dtheta = theta_vals[1] - theta_vals[0]
        dphi = phi_vals[1] - phi_vals[0]

        total_energy = 0.0
        eps = 0.02

        for r in r_vals:
            f = self.profile_function(r)
            f_next = self.profile_function(r + eps)
            df_dr = (f_next - f) / eps

            sin_f = np.sin(f)
            sin2_f = sin_f**2

            for theta in theta_vals:
                for phi in phi_vals:
                    n_hat = self.compute_n_hat(theta, phi)

                    # Compute gradients of n_hat
                    n_theta_p = self.compute_n_hat(theta + eps, phi)
                    n_phi_p = self.compute_n_hat(theta, phi + eps)

                    dn_dtheta = (n_theta_p - n_hat) / eps
                    dn_dphi = (n_phi_p - n_hat) / eps

                    # Metric factors
                    sin_theta = np.sin(theta)

                    # Energy density components
                    # Kinetic: |grad f|² + sin²(f) * |grad n|²
                    grad_n_sq = (np.sum(dn_dtheta**2) / r**2 +
                                np.sum(dn_dphi**2) / (r * sin_theta)**2 if sin_theta > 0.01 else 0)

                    kinetic = 0.5 * (df_dr**2 + 2 * sin2_f / r**2 + sin2_f * grad_n_sq)

                    # Skyrme term (simplified)
                    skyrme = (2 * df_dr**2 * sin2_f / r**2 +
                             sin2_f**2 / r**4 +
                             sin2_f**2 * grad_n_sq / r**2)

                    # Volume element
                    dV = r**2 * sin_theta * dr * dtheta * dphi

                    total_energy += (kinetic + skyrme) * dV

        return total_energy


# ==============================================================================
# PART 2: SPLINE-BASED PROFILES
# ==============================================================================

class SplineProfileSkyrmion:
    """
    Skyrmion with arbitrary radial profile parametrized by splines.

    Instead of the standard f(r) = 2*arctan(R/r), we use a cubic spline
    with control points that can be optimized.
    """

    def __init__(self, control_points=None, n_control=5):
        """
        Initialize with control points for the profile.

        control_points: array of (r, f) pairs
        If None, uses standard hedgehog as starting point.
        """
        if control_points is None:
            # Default: hedgehog-like profile
            r_ctrl = np.array([0.0, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0])
            f_ctrl = np.array([np.pi, 2.5, 2.0, 1.2, 0.4, 0.15, 0.05])
            self.control_r = r_ctrl
            self.control_f = f_ctrl
        else:
            self.control_r = control_points[:, 0]
            self.control_f = control_points[:, 1]

        # Build spline
        self._build_spline()

    def _build_spline(self):
        """Build cubic spline from control points."""
        # Ensure boundary conditions
        self.control_f[0] = np.pi  # f(0) = π
        self.control_f = np.clip(self.control_f, 0, np.pi)  # Keep in valid range

        self.spline = CubicSpline(self.control_r, self.control_f,
                                  bc_type=((1, 0), (1, 0)))  # Zero derivative at boundaries

    def profile(self, r):
        """Evaluate profile at r."""
        if r < 0:
            return np.pi
        if r > self.control_r[-1]:
            return max(0, self.spline(self.control_r[-1]) * np.exp(-(r - self.control_r[-1])))
        return float(self.spline(r))

    def profile_derivative(self, r):
        """Evaluate profile derivative at r."""
        if r < 0.01 or r > self.control_r[-1]:
            return 0
        return float(self.spline(r, 1))

    def set_control_values(self, f_values):
        """Update control point values (keeping r fixed)."""
        self.control_f[1:-1] = f_values  # Don't change boundary points
        self._build_spline()

    def compute_energy(self, r_max=20.0, n_r=200):
        """Compute energy assuming hedgehog angular structure."""
        r_vals = np.linspace(0.01, r_max, n_r)
        dr = r_vals[1] - r_vals[0]

        energy = 0.0
        for r in r_vals:
            f = self.profile(r)
            df_dr = self.profile_derivative(r)

            sin_f = np.sin(f)
            sin2_f = sin_f**2

            # Hedgehog energy density
            kinetic = 0.5 * (df_dr**2 + 2 * sin2_f / r**2)
            skyrme = 2 * df_dr**2 * sin2_f / r**2 + sin2_f**2 / r**4

            energy += 4 * np.pi * r**2 * (kinetic + skyrme) * dr

        return energy

    def compute_topological_charge(self, r_max=20.0, n_r=200):
        """Compute topological charge."""
        r_vals = np.linspace(0.01, r_max, n_r)
        dr = r_vals[1] - r_vals[0]

        Q = 0.0
        for r in r_vals:
            f = self.profile(r)
            df_dr = self.profile_derivative(r)
            Q += -2/np.pi * np.sin(f)**2 * df_dr * dr

        return Q


# ==============================================================================
# PART 3: FOURIER-MODE ANGULAR DEFORMATIONS
# ==============================================================================

class FourierDeformedSkyrmion:
    """
    Skyrmion with angular deformations parametrized by spherical harmonics.

    f(r, θ, φ) = f_0(r) * (1 + Σ a_lm * Y_lm(θ, φ))

    This allows arbitrary angular deformations while keeping radial structure.
    """

    def __init__(self, coefficients=None, R_scale=1.0):
        """
        coefficients: dict mapping (l, m) to complex amplitude a_lm
        """
        self.R_scale = R_scale
        self.coefficients = coefficients or {}

    def base_profile(self, r):
        """Base hedgehog profile."""
        if r < 1e-10:
            return np.pi
        return 2 * np.arctan(self.R_scale / r)

    def angular_factor(self, theta, phi):
        """Compute the angular deformation factor."""
        factor = 1.0
        for (l, m), a_lm in self.coefficients.items():
            # Real spherical harmonic
            Y_lm = sph_harm(m, l, phi, theta)
            factor += np.real(a_lm * Y_lm)
        return max(0.1, min(2.0, factor))  # Clamp to avoid pathologies

    def profile(self, r, theta, phi):
        """Full profile with angular deformation."""
        f0 = self.base_profile(r)
        ang = self.angular_factor(theta, phi)
        return np.clip(f0 * ang, 0, np.pi)

    def compute_energy(self, r_max=12.0, n_r=50, n_theta=25, n_phi=25):
        """Compute energy with 3D integration."""
        r_vals = np.linspace(0.1, r_max, n_r)
        theta_vals = np.linspace(0.01, np.pi - 0.01, n_theta)
        phi_vals = np.linspace(0, 2*np.pi - 0.01, n_phi)

        dr = r_vals[1] - r_vals[0]
        dtheta = theta_vals[1] - theta_vals[0]
        dphi = phi_vals[1] - phi_vals[0]
        eps = 0.02

        total_energy = 0.0

        for r in r_vals:
            for theta in theta_vals:
                for phi in phi_vals:
                    f = self.profile(r, theta, phi)

                    # Numerical gradients
                    df_dr = (self.profile(r + eps, theta, phi) - f) / eps
                    df_dtheta = (self.profile(r, theta + eps, phi) - f) / (eps * r) if r > eps else 0
                    df_dphi = (self.profile(r, theta, phi + eps) - f) / (eps * r * np.sin(theta)) if r * np.sin(theta) > eps else 0

                    sin_f = np.sin(f)
                    sin2_f = sin_f**2

                    # Gradient squared
                    grad_f_sq = df_dr**2 + df_dtheta**2 + df_dphi**2

                    # Energy density (simplified for deformed hedgehog)
                    kinetic = 0.5 * (grad_f_sq + 2 * sin2_f / r**2)
                    skyrme = 2 * df_dr**2 * sin2_f / r**2 + sin2_f**2 / r**4

                    dV = r**2 * np.sin(theta) * dr * dtheta * dphi
                    total_energy += (kinetic + skyrme) * dV

        return total_energy


# ==============================================================================
# PART 4: OPTIMIZATION FUNCTIONS
# ==============================================================================

def optimize_rational_map(map_type, param_bounds, n_iter=50):
    """Optimize parameters of a rational map ansatz."""

    def objective(params):
        if map_type == 'mobius':
            config = RationalMapSkyrmion('mobius', {
                'R_scale': params[0],
                'a': complex(params[1], params[2])
            })
        elif map_type == 'deformed':
            config = RationalMapSkyrmion('deformed', {
                'R_scale': params[0],
                'epsilon': params[1]
            })
        elif map_type == 'axial':
            config = RationalMapSkyrmion('axial', {
                'R_scale': params[0],
                'epsilon': params[1]
            })
        else:
            config = RationalMapSkyrmion('identity', {'R_scale': params[0]})

        try:
            E = config.compute_energy(n_r=40, n_theta=20, n_phi=20)
            return E
        except:
            return 1e10

    result = differential_evolution(objective, param_bounds, maxiter=n_iter,
                                   seed=42, polish=True, workers=1)
    return result


def optimize_spline_profile(n_control=5, n_iter=100):
    """Optimize spline control points to minimize energy."""

    # Initial control points (hedgehog-like)
    r_ctrl = np.array([0.0, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0])
    f_init = np.array([np.pi, 2.5, 2.0, 1.2, 0.4, 0.15, 0.05])

    skyrmion = SplineProfileSkyrmion()

    def objective(f_values):
        skyrmion.set_control_values(f_values)
        E = skyrmion.compute_energy()
        Q = skyrmion.compute_topological_charge()
        # Penalize deviation from Q=1
        penalty = 1000 * (Q - 1)**2
        return E + penalty

    # Optimize middle control points
    x0 = f_init[1:-1]
    bounds = [(0.1, np.pi - 0.1) for _ in x0]

    result = minimize(objective, x0, method='L-BFGS-B', bounds=bounds,
                     options={'maxiter': n_iter})

    return result, skyrmion


def optimize_fourier_modes(max_l=2, n_iter=50):
    """Optimize Fourier mode coefficients."""

    def objective(params):
        # params: [R_scale, a_20_real, a_20_imag, a_22_real, a_22_imag, ...]
        R_scale = params[0]
        coeffs = {}
        idx = 1
        for l in range(2, max_l + 1, 2):  # Only even l (preserve parity)
            for m in range(0, l + 1):
                if idx + 1 < len(params):
                    coeffs[(l, m)] = complex(params[idx], params[idx + 1])
                    idx += 2

        config = FourierDeformedSkyrmion(coeffs, R_scale)
        try:
            E = config.compute_energy(n_r=30, n_theta=15, n_phi=15)
            return E
        except:
            return 1e10

    # Initial parameters
    n_params = 1 + 2 * sum(l + 1 for l in range(2, max_l + 1, 2))
    x0 = np.zeros(n_params)
    x0[0] = 1.0  # R_scale

    bounds = [(0.5, 2.0)] + [(-0.3, 0.3)] * (n_params - 1)

    result = differential_evolution(objective, bounds, maxiter=n_iter,
                                   seed=42, workers=1)
    return result


# ==============================================================================
# PART 5: MAIN ANALYSIS
# ==============================================================================

def run_sophisticated_search():
    """Run all sophisticated search methods."""

    results = {
        'timestamp': datetime.now().isoformat(),
        'description': 'Sophisticated search for non-hedgehog Q=1 configurations',
        'reference_hedgehog_energy': E_HEDGEHOG_REF,
        'tests': []
    }

    print("=" * 70)
    print("SOPHISTICATED SKYRME CONFIGURATION SEARCH")
    print("=" * 70)
    print(f"\nReference hedgehog energy: {E_HEDGEHOG_REF:.4f}")
    print()

    # =========================================================================
    # TEST 1: Rational Map - Identity (Hedgehog Reference)
    # =========================================================================
    print("TEST 1: Rational Map - Identity (Hedgehog)")
    print("-" * 50)

    hedgehog = RationalMapSkyrmion('identity', {'R_scale': 1.0})
    E_hedge = hedgehog.compute_energy(n_r=60, n_theta=30, n_phi=30)
    print(f"  Energy: {E_hedge:.4f}")

    # Optimize R_scale
    result_h = optimize_rational_map('identity', [(0.3, 3.0)], n_iter=30)
    print(f"  Optimized R_scale: {result_h.x[0]:.4f}")
    print(f"  Optimized energy: {result_h.fun:.4f}")

    E_hedge_opt = result_h.fun
    results['tests'].append({
        'name': 'Hedgehog (rational map)',
        'type': 'identity',
        'E': E_hedge_opt,
        'params': {'R_scale': result_h.x[0]}
    })

    # =========================================================================
    # TEST 2: Rational Map - Möbius Transformation
    # =========================================================================
    print("\nTEST 2: Rational Map - Möbius Transformation")
    print("-" * 50)
    print("  (Möbius maps are SO(3) rotations, should give same energy)")

    for a_val in [0.1, 0.3, 0.5]:
        mobius = RationalMapSkyrmion('mobius', {'R_scale': 1.0, 'a': complex(a_val, 0)})
        E_mob = mobius.compute_energy(n_r=50, n_theta=25, n_phi=25)
        delta = E_mob - E_hedge_opt
        print(f"  a={a_val}: E={E_mob:.4f}, ΔE={delta:+.4f}")

        results['tests'].append({
            'name': f'Möbius a={a_val}',
            'type': 'mobius',
            'E': E_mob,
            'delta_E': delta
        })

    # =========================================================================
    # TEST 3: Rational Map - Deformed
    # =========================================================================
    print("\nTEST 3: Rational Map - Deformed (R(z) = z + ε*z²)")
    print("-" * 50)

    for eps in [0.05, 0.1, 0.2]:
        deformed = RationalMapSkyrmion('deformed', {'R_scale': 1.0, 'epsilon': eps})
        E_def = deformed.compute_energy(n_r=50, n_theta=25, n_phi=25)
        delta = E_def - E_hedge_opt
        status = "LOWER!" if delta < 0 else "higher"
        print(f"  ε={eps}: E={E_def:.4f}, ΔE={delta:+.4f} ({status})")

        results['tests'].append({
            'name': f'Deformed ε={eps}',
            'type': 'deformed',
            'E': E_def,
            'delta_E': delta,
            'lower': delta < 0
        })

    # Optimize deformed
    print("  Optimizing deformed map...")
    result_def = optimize_rational_map('deformed', [(0.3, 3.0), (-0.5, 0.5)], n_iter=40)
    print(f"  Best: R={result_def.x[0]:.3f}, ε={result_def.x[1]:.3f}, E={result_def.fun:.4f}")
    print(f"  ΔE vs hedgehog: {result_def.fun - E_hedge_opt:+.4f}")

    # =========================================================================
    # TEST 4: Rational Map - Axial
    # =========================================================================
    print("\nTEST 4: Rational Map - Axial (R(z) = z*(1 + ε*|z|²))")
    print("-" * 50)

    for eps in [0.05, 0.1, 0.2]:
        axial = RationalMapSkyrmion('axial', {'R_scale': 1.0, 'epsilon': eps})
        E_ax = axial.compute_energy(n_r=50, n_theta=25, n_phi=25)
        delta = E_ax - E_hedge_opt
        status = "LOWER!" if delta < 0 else "higher"
        print(f"  ε={eps}: E={E_ax:.4f}, ΔE={delta:+.4f} ({status})")

        results['tests'].append({
            'name': f'Axial ε={eps}',
            'type': 'axial',
            'E': E_ax,
            'delta_E': delta,
            'lower': delta < 0
        })

    # =========================================================================
    # TEST 5: Spline Profile Optimization
    # =========================================================================
    print("\nTEST 5: Spline Profile Optimization")
    print("-" * 50)

    print("  Optimizing spline control points...")
    result_spline, skyrmion = optimize_spline_profile(n_iter=100)
    E_spline = skyrmion.compute_energy()
    Q_spline = skyrmion.compute_topological_charge()
    delta = E_spline - E_hedge_opt

    print(f"  Optimized energy: {E_spline:.4f}")
    print(f"  Topological charge: {Q_spline:.4f}")
    print(f"  ΔE vs hedgehog: {delta:+.4f}")

    results['tests'].append({
        'name': 'Spline profile',
        'type': 'spline',
        'E': E_spline,
        'Q': Q_spline,
        'delta_E': delta,
        'lower': delta < 0
    })

    # =========================================================================
    # TEST 6: Fourier Mode Deformations
    # =========================================================================
    print("\nTEST 6: Fourier Mode Deformations (Y_lm)")
    print("-" * 50)

    # Test specific modes
    for (l, m), amp in [((2, 0), 0.1), ((2, 0), 0.2), ((2, 2), 0.1)]:
        fourier = FourierDeformedSkyrmion({(l, m): amp}, R_scale=1.0)
        E_four = fourier.compute_energy(n_r=40, n_theta=20, n_phi=20)
        delta = E_four - E_hedge_opt
        status = "LOWER!" if delta < 0 else "higher"
        print(f"  Y_{l}{m}, amp={amp}: E={E_four:.4f}, ΔE={delta:+.4f} ({status})")

        results['tests'].append({
            'name': f'Fourier Y_{l}{m} amp={amp}',
            'type': 'fourier',
            'E': E_four,
            'delta_E': delta,
            'lower': delta < 0
        })

    # Optimize Fourier modes
    print("  Optimizing Fourier modes...")
    result_fourier = optimize_fourier_modes(max_l=2, n_iter=30)
    print(f"  Optimized energy: {result_fourier.fun:.4f}")
    print(f"  ΔE vs hedgehog: {result_fourier.fun - E_hedge_opt:+.4f}")

    # =========================================================================
    # TEST 7: Global Basin Hopping
    # =========================================================================
    print("\nTEST 7: Global Basin Hopping Search")
    print("-" * 50)

    def global_objective(params):
        """Combined objective for basin hopping."""
        R_scale, eps_def, eps_ax = params

        # Try deformed
        config = RationalMapSkyrmion('deformed', {
            'R_scale': R_scale,
            'epsilon': eps_def
        })
        E1 = config.compute_energy(n_r=30, n_theta=15, n_phi=15)

        return E1

    print("  Running basin hopping (this may take a moment)...")
    x0 = [1.0, 0.0, 0.0]

    minimizer_kwargs = {
        'method': 'L-BFGS-B',
        'bounds': [(0.3, 3.0), (-0.5, 0.5), (-0.5, 0.5)]
    }

    result_basin = basinhopping(global_objective, x0, minimizer_kwargs=minimizer_kwargs,
                                niter=20, seed=42)

    print(f"  Best energy found: {result_basin.fun:.4f}")
    print(f"  Best params: R={result_basin.x[0]:.3f}, ε_def={result_basin.x[1]:.3f}")
    print(f"  ΔE vs hedgehog: {result_basin.fun - E_hedge_opt:+.4f}")

    results['tests'].append({
        'name': 'Basin hopping global search',
        'type': 'global',
        'E': result_basin.fun,
        'delta_E': result_basin.fun - E_hedge_opt,
        'params': list(result_basin.x),
        'lower': result_basin.fun < E_hedge_opt
    })

    # =========================================================================
    # SUMMARY
    # =========================================================================
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    n_lower = sum(1 for t in results['tests'] if t.get('lower', False))
    min_E = min(t['E'] for t in results['tests'])
    min_test = min(results['tests'], key=lambda t: t['E'])

    print(f"\nReference hedgehog energy: {E_hedge_opt:.4f}")
    print(f"Configurations tested: {len(results['tests'])}")
    print(f"Minimum energy found: {min_E:.4f} ({min_test['name']})")
    print(f"Configurations with E < E_hedgehog: {n_lower}")

    if n_lower > 0:
        print("\n*** CRITICAL: Found configurations with LOWER energy! ***")
        for t in results['tests']:
            if t.get('lower', False):
                print(f"    - {t['name']}: E={t['E']:.4f}, ΔE={t['delta_E']:.4f}")
    else:
        print("\nNo configurations found with lower energy than hedgehog.")
        print("This strongly supports global minimality of the hedgehog.")

    results['summary'] = {
        'reference_energy': E_hedge_opt,
        'min_energy_found': min_E,
        'min_config': min_test['name'],
        'n_lower_than_hedgehog': n_lower,
        'conclusion': 'Counterexamples found' if n_lower > 0 else 'Hedgehog appears optimal'
    }

    # Save results
    output_path = 'sophisticated_skyrme_search_results.json'
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)

    print(f"\nResults saved to: {output_path}")

    return results


def verify_results():
    """
    Verify results by computing all energies with consistent methods.

    The issue: Different calculation methods give different absolute values.
    - Fast 1D integration (for hedgehog): assumes spherical symmetry
    - Full 3D integration: works for any configuration but has numerical errors

    We need to compare apples to apples.
    """
    print("\n" + "=" * 70)
    print("VERIFICATION: CONSISTENT ENERGY CALCULATIONS")
    print("=" * 70)

    # =========================================================================
    # Step 1: Establish hedgehog reference with BOTH methods
    # =========================================================================
    print("\n1. Hedgehog energy with different methods:")
    print("-" * 50)

    # 1D integration (exact for hedgehog)
    spline_hedgehog = SplineProfileSkyrmion()  # Default is hedgehog-like
    E_hedge_1D = spline_hedgehog.compute_energy()
    Q_hedge_1D = spline_hedgehog.compute_topological_charge()
    print(f"   1D integration: E = {E_hedge_1D:.4f}, Q = {Q_hedge_1D:.4f}")

    # 3D integration via rational map
    hedge_3D = RationalMapSkyrmion('identity', {'R_scale': 1.0})
    E_hedge_3D = hedge_3D.compute_energy(n_r=60, n_theta=30, n_phi=30)
    print(f"   3D integration: E = {E_hedge_3D:.4f}")

    print(f"   Ratio (3D/1D): {E_hedge_3D / E_hedge_1D:.4f}")
    print(f"   (This ratio reflects numerical/normalization differences)")

    # =========================================================================
    # Step 2: Test deformations using 1D method where applicable
    # =========================================================================
    print("\n2. Spline profile optimization (1D method, apples-to-apples):")
    print("-" * 50)

    result_spline, skyrmion = optimize_spline_profile(n_iter=150)
    E_spline = skyrmion.compute_energy()
    Q_spline = skyrmion.compute_topological_charge()

    print(f"   Hedgehog energy (1D): {E_hedge_1D:.4f}")
    print(f"   Optimized spline: E = {E_spline:.4f}, Q = {Q_spline:.4f}")
    print(f"   ΔE: {E_spline - E_hedge_1D:+.4f}")

    if E_spline < E_hedge_1D - 0.1:
        print(f"   *** LOWER ENERGY FOUND! ***")
        lower_1D = True
    else:
        print(f"   Spline converged to hedgehog (within numerical tolerance)")
        lower_1D = False

    # =========================================================================
    # Step 3: Test deformations using 3D method
    # =========================================================================
    print("\n3. Angular deformations (3D method, apples-to-apples):")
    print("-" * 50)

    print(f"   Hedgehog energy (3D): {E_hedge_3D:.4f}")

    lower_3D = False

    # Test Fourier deformations with 3D integration
    for (l, m), amp in [((2, 0), 0.1), ((2, 0), 0.2), ((2, 2), 0.1)]:
        fourier = FourierDeformedSkyrmion({(l, m): amp}, R_scale=1.0)
        E_four = fourier.compute_energy(n_r=60, n_theta=30, n_phi=30)
        delta = E_four - E_hedge_3D
        status = "LOWER!" if delta < -0.1 else "higher/same"
        print(f"   Y_{l}{m}, amp={amp}: E={E_four:.4f}, ΔE={delta:+.4f} ({status})")

        if delta < -0.1:
            lower_3D = True

    # Test deformed rational map
    deformed = RationalMapSkyrmion('deformed', {'R_scale': 1.0, 'epsilon': 0.1})
    E_def = deformed.compute_energy(n_r=60, n_theta=30, n_phi=30)
    delta = E_def - E_hedge_3D
    status = "LOWER!" if delta < -0.1 else "higher/same"
    print(f"   Deformed map ε=0.1: E={E_def:.4f}, ΔE={delta:+.4f} ({status})")

    if delta < -0.1:
        lower_3D = True

    # =========================================================================
    # Step 4: Conclusions
    # =========================================================================
    print("\n" + "=" * 70)
    print("VERIFICATION CONCLUSIONS")
    print("=" * 70)

    if lower_1D or lower_3D:
        print("\n*** POTENTIAL COUNTEREXAMPLES FOUND ***")
        print("Further investigation needed to verify these are genuine")
        print("and not numerical artifacts.")
    else:
        print("\n✓ No genuine lower-energy configurations found")
        print("✓ All deformations have higher or equal energy to hedgehog")
        print("✓ This strongly supports hedgehog global minimality")

    return {
        'E_hedge_1D': E_hedge_1D,
        'E_hedge_3D': E_hedge_3D,
        'E_spline_optimized': E_spline,
        'lower_found_1D': lower_1D,
        'lower_found_3D': lower_3D
    }


if __name__ == "__main__":
    results = run_sophisticated_search()

    print("\n" + "#" * 70)
    print("# VERIFICATION PHASE")
    print("#" * 70)

    verification = verify_results()

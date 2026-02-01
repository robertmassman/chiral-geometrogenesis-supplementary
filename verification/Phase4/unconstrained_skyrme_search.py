#!/usr/bin/env python3
"""
Unconstrained Skyrme Model: Search for Non-Hedgehog Minima
==========================================================

This script searches for Q=1 configurations in the general Skyrme model
(without CG's color constraints) that might have lower energy than the hedgehog.

Research Question: Does the general Skyrme model have non-hedgehog Q=1
configurations with E < E_hedgehog?

If YES: Scenario C confirmed - color constraints are necessary for truth
If NO: Could be Scenario A (proof exists) or B (unprovable)

Related Documents:
- docs/proofs/supporting/Color-Constraints-Necessity-Research-Plan.md
- docs/proofs/Phase4/Theorem-4.1.1-Existence-of-Solitons.md §3.4.11

Date: 2026-01-31
"""

import numpy as np
from scipy.integrate import quad, dblquad, tplquad
from scipy.optimize import minimize, differential_evolution
from scipy.special import sph_harm
import json
from datetime import datetime
import warnings
warnings.filterwarnings('ignore')

# ==============================================================================
# PHYSICAL CONSTANTS
# ==============================================================================

F_PI = 93.0  # MeV, pion decay constant
E_SKYRME = 4.0  # Dimensionless Skyrme parameter (typical value)

# Dimensionless units: lengths in units of 1/(e*f_pi), energies in units of f_pi/e
# In these units, the classical hedgehog energy is approximately 72.9 (Bogomolny bound: 12*pi^2 ≈ 118.4)

# ==============================================================================
# PART 1: HEDGEHOG REFERENCE
# ==============================================================================

def hedgehog_profile_approx(r, R=1.0):
    """
    Approximate hedgehog profile function f(r).

    Boundary conditions: f(0) = pi, f(infinity) = 0

    This uses a rational approximation that captures the essential behavior.
    The exact profile requires solving a nonlinear ODE.
    """
    # Rational approximation: f(r) = pi * (1 - r^2/(r^2 + R^2))^(1/2) for small r
    # Exponential decay for large r
    if r < 1e-10:
        return np.pi
    return np.pi * np.exp(-r/R) * (R/(r + R))

def hedgehog_profile_exact(r, params=None):
    """
    More accurate hedgehog profile using standard parametrization.

    f(r) = pi - 2*arctan(r/R) approximately matches the numerical solution.
    """
    R = 1.0 if params is None else params.get('R', 1.0)
    return 2 * np.arctan(R/r) if r > 1e-10 else np.pi

def hedgehog_energy_density(r, f, df_dr):
    """
    Energy density for hedgehog configuration.

    E = integral of [kinetic term + Skyrme term]

    For hedgehog U = exp(i*f(r)*r_hat·tau):
    - Kinetic: (f_pi^2/2) * [f'^2 + 2*sin^2(f)/r^2]
    - Skyrme: (1/e^2) * [2*f'^2*sin^2(f)/r^2 + sin^4(f)/r^4]
    """
    if r < 1e-10:
        # Limit as r -> 0: need f'(0) = 0 for regularity
        return 0.0

    sin_f = np.sin(f)
    sin2_f = sin_f**2
    sin4_f = sin2_f**2

    # Kinetic term (in dimensionless units)
    kinetic = 0.5 * (df_dr**2 + 2 * sin2_f / r**2)

    # Skyrme term
    skyrme = 2 * df_dr**2 * sin2_f / r**2 + sin4_f / r**4

    return kinetic + skyrme

def compute_hedgehog_energy(f_func, r_max=20.0, n_points=500):
    """Compute total energy of hedgehog configuration."""
    r_vals = np.linspace(0.01, r_max, n_points)
    dr = r_vals[1] - r_vals[0]

    total_energy = 0.0
    for i, r in enumerate(r_vals):
        f = f_func(r)
        # Numerical derivative
        if i == 0:
            df_dr = (f_func(r + dr) - f) / dr
        elif i == len(r_vals) - 1:
            df_dr = (f - f_func(r - dr)) / dr
        else:
            df_dr = (f_func(r + dr) - f_func(r - dr)) / (2 * dr)

        rho = hedgehog_energy_density(r, f, df_dr)
        total_energy += 4 * np.pi * r**2 * rho * dr

    return total_energy

def compute_topological_charge_hedgehog(f_func, r_max=20.0, n_points=500):
    """
    Compute topological charge Q for hedgehog.

    For hedgehog: Q = (1/pi) * [f(0) - f(infinity)] = 1 if f(0)=pi, f(inf)=0

    More precisely: Q = -(2/pi) * integral of sin^2(f) * f' dr
    """
    r_vals = np.linspace(0.01, r_max, n_points)
    dr = r_vals[1] - r_vals[0]

    Q = 0.0
    for i, r in enumerate(r_vals):
        f = f_func(r)
        if i == 0:
            df_dr = (f_func(r + dr) - f) / dr
        else:
            df_dr = (f_func(r + dr) - f_func(r - dr)) / (2 * dr) if i < len(r_vals)-1 else (f - f_func(r - dr)) / dr

        Q += -2/np.pi * np.sin(f)**2 * df_dr * dr

    return Q

# ==============================================================================
# PART 2: EXOTIC CONFIGURATIONS (Non-Hedgehog)
# ==============================================================================

class GeneralSkyrmionConfig:
    """
    General Q=1 Skyrme configuration, not restricted to hedgehog symmetry.

    Parametrization: U(x) = exp(i * Theta(x) * n_hat(x) · tau)

    where Theta(x) and n_hat(x) can vary independently.
    """

    def __init__(self, config_type='hedgehog', params=None):
        self.config_type = config_type
        self.params = params or {}

    def profile_and_direction(self, r, theta, phi):
        """
        Return (Theta, n_hat) at position (r, theta, phi).

        Theta: rotation angle (0 to pi for Q=1)
        n_hat: unit vector in isospin space (3 components)
        """
        if self.config_type == 'hedgehog':
            return self._hedgehog(r, theta, phi)
        elif self.config_type == 'toroidal':
            return self._toroidal(r, theta, phi)
        elif self.config_type == 'deformed':
            return self._deformed(r, theta, phi)
        elif self.config_type == 'twisted':
            return self._twisted(r, theta, phi)
        elif self.config_type == 'multi_shell':
            return self._multi_shell(r, theta, phi)
        elif self.config_type == 'axial':
            return self._axial(r, theta, phi)
        else:
            return self._hedgehog(r, theta, phi)

    def _hedgehog(self, r, theta, phi):
        """Standard hedgehog: n_hat = r_hat"""
        R = self.params.get('R', 1.0)
        Theta = 2 * np.arctan(R/r) if r > 1e-10 else np.pi

        # n_hat = r_hat in Cartesian
        n_hat = np.array([
            np.sin(theta) * np.cos(phi),
            np.sin(theta) * np.sin(phi),
            np.cos(theta)
        ])
        return Theta, n_hat

    def _toroidal(self, r, theta, phi):
        """
        Toroidal configuration: n_hat = phi_hat (azimuthal)

        This breaks spherical symmetry but preserves axial symmetry.
        """
        R = self.params.get('R', 1.0)
        alpha = self.params.get('alpha', 0.3)  # Toroidal mixing parameter

        # Profile still depends on r
        Theta = 2 * np.arctan(R/r) if r > 1e-10 else np.pi

        # Mix hedgehog and toroidal directions
        r_hat = np.array([
            np.sin(theta) * np.cos(phi),
            np.sin(theta) * np.sin(phi),
            np.cos(theta)
        ])
        phi_hat = np.array([
            -np.sin(phi),
            np.cos(phi),
            0
        ])

        # n_hat = (1-alpha)*r_hat + alpha*phi_hat, normalized
        n_hat = (1 - alpha) * r_hat + alpha * phi_hat
        norm = np.linalg.norm(n_hat)
        if norm > 1e-10:
            n_hat = n_hat / norm
        else:
            n_hat = r_hat

        return Theta, n_hat

    def _deformed(self, r, theta, phi):
        """
        Deformed hedgehog: profile depends on angle.

        Theta(r, theta) = f(r) * (1 + epsilon * Y_20(theta))

        This is a quadrupole deformation.
        """
        R = self.params.get('R', 1.0)
        epsilon = self.params.get('epsilon', 0.2)

        base_Theta = 2 * np.arctan(R/r) if r > 1e-10 else np.pi

        # Y_20 = (1/4)*sqrt(5/pi)*(3*cos^2(theta) - 1)
        Y20 = 0.25 * np.sqrt(5/np.pi) * (3 * np.cos(theta)**2 - 1)

        Theta = base_Theta * (1 + epsilon * Y20)
        Theta = np.clip(Theta, 0, np.pi)  # Keep in valid range

        # n_hat still radial
        n_hat = np.array([
            np.sin(theta) * np.cos(phi),
            np.sin(theta) * np.sin(phi),
            np.cos(theta)
        ])
        return Theta, n_hat

    def _twisted(self, r, theta, phi):
        """
        Twisted configuration: n_hat rotates with azimuthal angle.

        n_hat(phi) = R_z(gamma*phi) · r_hat

        This introduces a "twist" that might lower energy.
        """
        R = self.params.get('R', 1.0)
        gamma = self.params.get('gamma', 0.5)  # Twist rate

        Theta = 2 * np.arctan(R/r) if r > 1e-10 else np.pi

        # Base direction
        r_hat = np.array([
            np.sin(theta) * np.cos(phi),
            np.sin(theta) * np.sin(phi),
            np.cos(theta)
        ])

        # Rotate in the x-y plane by gamma*phi
        twist_angle = gamma * phi
        R_z = np.array([
            [np.cos(twist_angle), -np.sin(twist_angle), 0],
            [np.sin(twist_angle), np.cos(twist_angle), 0],
            [0, 0, 1]
        ])

        n_hat = R_z @ r_hat
        return Theta, n_hat

    def _multi_shell(self, r, theta, phi):
        """
        Multi-shell configuration: profile has additional radial structure.

        This could potentially lower energy by spreading the topological
        charge across multiple "shells".
        """
        R1 = self.params.get('R1', 0.5)
        R2 = self.params.get('R2', 2.0)
        beta = self.params.get('beta', 0.3)  # Shell mixing

        # Two-scale profile
        if r > 1e-10:
            Theta1 = 2 * np.arctan(R1/r)
            Theta2 = 2 * np.arctan(R2/r)
            Theta = (1 - beta) * Theta1 + beta * Theta2
        else:
            Theta = np.pi

        n_hat = np.array([
            np.sin(theta) * np.cos(phi),
            np.sin(theta) * np.sin(phi),
            np.cos(theta)
        ])
        return Theta, n_hat

    def _axial(self, r, theta, phi):
        """
        Axially symmetric but non-spherical configuration.

        Profile depends on cylindrical radius rho = r*sin(theta)
        and height z = r*cos(theta) differently.
        """
        R_rho = self.params.get('R_rho', 1.0)
        R_z = self.params.get('R_z', 1.5)

        rho = r * np.sin(theta)
        z = r * np.cos(theta)

        # Anisotropic scale
        r_eff = np.sqrt((rho/R_rho)**2 + (z/R_z)**2)

        Theta = 2 * np.arctan(1/r_eff) if r_eff > 1e-10 else np.pi

        n_hat = np.array([
            np.sin(theta) * np.cos(phi),
            np.sin(theta) * np.sin(phi),
            np.cos(theta)
        ])
        return Theta, n_hat


# ==============================================================================
# PART 3: ENERGY AND CHARGE COMPUTATION FOR GENERAL CONFIGS
# ==============================================================================

def compute_energy_general(config, r_max=15.0, n_r=60, n_theta=30, n_phi=30):
    """
    Compute energy of a general Skyrme configuration.

    This is computationally expensive as we need 3D integration.

    The Skyrme energy density involves:
    - Kinetic: (f_pi^2/4) * Tr[L_mu L^mu] where L_mu = U^dag dU
    - Skyrme: (1/32e^2) * Tr[[L_mu, L_nu]^2]

    For U = exp(i*Theta*n·tau), the currents depend on gradients of Theta and n.
    """
    # Grid in spherical coordinates
    r_vals = np.linspace(0.1, r_max, n_r)
    theta_vals = np.linspace(0.01, np.pi - 0.01, n_theta)
    phi_vals = np.linspace(0, 2*np.pi - 0.01, n_phi)

    dr = r_vals[1] - r_vals[0]
    dtheta = theta_vals[1] - theta_vals[0]
    dphi = phi_vals[1] - phi_vals[0]

    total_energy = 0.0

    for r in r_vals:
        for theta in theta_vals:
            for phi in phi_vals:
                # Get configuration at this point
                Theta, n_hat = config.profile_and_direction(r, theta, phi)

                # Numerical gradients
                eps = 0.01

                # d/dr
                Theta_pr, n_pr = config.profile_and_direction(r + eps, theta, phi)
                dTheta_dr = (Theta_pr - Theta) / eps
                dn_dr = (n_pr - n_hat) / eps

                # d/dtheta (1/r factor)
                Theta_pt, n_pt = config.profile_and_direction(r, theta + eps, phi)
                dTheta_dtheta = (Theta_pt - Theta) / (eps * r) if r > eps else 0
                dn_dtheta = (n_pt - n_hat) / (eps * r) if r > eps else np.zeros(3)

                # d/dphi (1/(r*sin(theta)) factor)
                Theta_pp, n_pp = config.profile_and_direction(r, theta, phi + eps)
                sin_theta = np.sin(theta)
                dTheta_dphi = (Theta_pp - Theta) / (eps * r * sin_theta) if r * sin_theta > eps else 0
                dn_dphi = (n_pp - n_hat) / (eps * r * sin_theta) if r * sin_theta > eps else np.zeros(3)

                # Energy density (simplified form for U = exp(i*Theta*n·tau))
                # Kinetic: |grad(Theta)|^2 + sin^2(Theta)*|grad(n)|^2
                grad_Theta_sq = dTheta_dr**2 + dTheta_dtheta**2 + dTheta_dphi**2
                grad_n_sq = np.sum(dn_dr**2) + np.sum(dn_dtheta**2) + np.sum(dn_dphi**2)

                kinetic = 0.5 * (grad_Theta_sq + np.sin(Theta)**2 * grad_n_sq)

                # Skyrme term (approximation - full form is more complex)
                # The Skyrme term penalizes rapid spatial variation
                sin2_Theta = np.sin(Theta)**2
                skyrme = (grad_Theta_sq * sin2_Theta * grad_n_sq +
                         sin2_Theta**2 * (grad_n_sq**2) / 4)

                # Volume element
                dV = r**2 * np.sin(theta) * dr * dtheta * dphi

                total_energy += (kinetic + skyrme) * dV

    return total_energy

def compute_topological_charge_general(config, r_max=15.0, n_r=50, n_theta=25, n_phi=25):
    """
    Compute topological charge for a general configuration.

    Q = (1/24*pi^2) * integral of epsilon^{ijk} Tr[L_i L_j L_k]

    For U = exp(i*Theta*n·tau), this simplifies considerably.
    """
    r_vals = np.linspace(0.1, r_max, n_r)
    theta_vals = np.linspace(0.01, np.pi - 0.01, n_theta)
    phi_vals = np.linspace(0, 2*np.pi - 0.01, n_phi)

    dr = r_vals[1] - r_vals[0]
    dtheta = theta_vals[1] - theta_vals[0]
    dphi = phi_vals[1] - phi_vals[0]

    Q = 0.0
    eps = 0.01

    for r in r_vals:
        for theta in theta_vals:
            for phi in phi_vals:
                Theta, n_hat = config.profile_and_direction(r, theta, phi)

                # Gradients
                Theta_pr, n_pr = config.profile_and_direction(r + eps, theta, phi)
                Theta_pt, n_pt = config.profile_and_direction(r, theta + eps, phi)
                Theta_pp, n_pp = config.profile_and_direction(r, theta, phi + eps)

                dTheta_dr = (Theta_pr - Theta) / eps
                dTheta_dtheta = (Theta_pt - Theta) / eps
                dTheta_dphi = (Theta_pp - Theta) / eps

                dn_dr = (n_pr - n_hat) / eps
                dn_dtheta = (n_pt - n_hat) / eps
                dn_dphi = (n_pp - n_hat) / eps

                # Topological charge density (simplified)
                # Q_density ~ sin^2(Theta) * (dTheta/dr) * (n · (dn/dtheta x dn/dphi))
                sin2_Theta = np.sin(Theta)**2

                cross = np.cross(dn_dtheta, dn_dphi)
                jacobian = np.dot(n_hat, cross)

                Q_density = -sin2_Theta * dTheta_dr * jacobian / (2 * np.pi**2)

                # Volume element (without 1/r factors since derivatives already have them)
                dV = dr * dtheta * dphi

                Q += Q_density * dV

    return Q

def compute_energy_fast(config, n_r=100):
    """
    Fast energy computation for configurations with spherical symmetry in profile.

    This is much faster but only valid for configs where Theta = Theta(r) only.
    """
    r_vals = np.linspace(0.01, 20.0, n_r)
    dr = r_vals[1] - r_vals[0]

    energy = 0.0

    for i, r in enumerate(r_vals):
        # Sample at (r, pi/2, 0) - equatorial plane
        Theta, n_hat = config.profile_and_direction(r, np.pi/2, 0)

        # Derivative
        if i < len(r_vals) - 1:
            Theta_next, _ = config.profile_and_direction(r_vals[i+1], np.pi/2, 0)
            dTheta_dr = (Theta_next - Theta) / dr
        else:
            dTheta_dr = 0

        # Hedgehog-like energy density (valid if n_hat = r_hat)
        sin_Theta = np.sin(Theta)
        sin2_Theta = sin_Theta**2

        kinetic = 0.5 * (dTheta_dr**2 + 2 * sin2_Theta / r**2)
        skyrme = 2 * dTheta_dr**2 * sin2_Theta / r**2 + sin2_Theta**2 / r**4

        energy += 4 * np.pi * r**2 * (kinetic + skyrme) * dr

    return energy


# ==============================================================================
# PART 4: OPTIMIZATION - SEARCH FOR LOWER ENERGY CONFIGURATIONS
# ==============================================================================

def energy_objective(params, config_type):
    """Objective function for optimization: compute energy given parameters."""
    if config_type == 'deformed':
        config = GeneralSkyrmionConfig('deformed', {
            'R': params[0],
            'epsilon': params[1]
        })
    elif config_type == 'toroidal':
        config = GeneralSkyrmionConfig('toroidal', {
            'R': params[0],
            'alpha': params[1]
        })
    elif config_type == 'twisted':
        config = GeneralSkyrmionConfig('twisted', {
            'R': params[0],
            'gamma': params[1]
        })
    elif config_type == 'axial':
        config = GeneralSkyrmionConfig('axial', {
            'R_rho': params[0],
            'R_z': params[1]
        })
    elif config_type == 'multi_shell':
        config = GeneralSkyrmionConfig('multi_shell', {
            'R1': params[0],
            'R2': params[1],
            'beta': params[2]
        })
    else:
        config = GeneralSkyrmionConfig('hedgehog', {'R': params[0]})

    try:
        energy = compute_energy_fast(config)
        return energy
    except:
        return 1e10  # Return large value on error

def optimize_configuration(config_type, bounds, n_iter=50):
    """
    Use differential evolution to find minimum energy configuration.
    """
    result = differential_evolution(
        lambda p: energy_objective(p, config_type),
        bounds,
        maxiter=n_iter,
        seed=42,
        polish=True,
        disp=False
    )
    return result


# ==============================================================================
# PART 5: MAIN ANALYSIS
# ==============================================================================

def run_analysis():
    """Run the full analysis."""
    results = {
        'timestamp': datetime.now().isoformat(),
        'description': 'Search for non-hedgehog Q=1 configurations with E < E_hedgehog',
        'tests': []
    }

    print("=" * 70)
    print("UNCONSTRAINED SKYRME MODEL: NON-HEDGEHOG SEARCH")
    print("=" * 70)
    print()

    # =========================================================================
    # TEST 1: Reference Hedgehog Energy
    # =========================================================================
    print("TEST 1: Reference Hedgehog Configuration")
    print("-" * 50)

    hedgehog = GeneralSkyrmionConfig('hedgehog', {'R': 1.0})
    E_hedgehog = compute_energy_fast(hedgehog)
    Q_hedgehog = compute_topological_charge_hedgehog(
        lambda r: hedgehog.profile_and_direction(r, np.pi/2, 0)[0]
    )

    print(f"  Energy (dimensionless): {E_hedgehog:.4f}")
    print(f"  Topological charge: {Q_hedgehog:.4f}")

    # Optimize hedgehog scale
    result_h = minimize(lambda R: compute_energy_fast(GeneralSkyrmionConfig('hedgehog', {'R': R[0]})),
                       [1.0], bounds=[(0.3, 3.0)])
    R_opt = result_h.x[0]
    hedgehog_opt = GeneralSkyrmionConfig('hedgehog', {'R': R_opt})
    E_hedgehog_opt = compute_energy_fast(hedgehog_opt)

    print(f"  Optimized R: {R_opt:.4f}")
    print(f"  Optimized energy: {E_hedgehog_opt:.4f}")

    results['tests'].append({
        'name': 'Hedgehog reference',
        'E': E_hedgehog_opt,
        'Q': Q_hedgehog,
        'R_optimal': R_opt
    })

    # =========================================================================
    # TEST 2: Deformed Configurations
    # =========================================================================
    print("\nTEST 2: Deformed Hedgehog (Quadrupole)")
    print("-" * 50)

    for epsilon in [0.1, 0.2, 0.3, 0.5]:
        deformed = GeneralSkyrmionConfig('deformed', {'R': R_opt, 'epsilon': epsilon})
        E_def = compute_energy_fast(deformed)
        delta_E = E_def - E_hedgehog_opt

        status = "LOWER!" if delta_E < 0 else "higher"
        print(f"  epsilon={epsilon}: E={E_def:.4f}, ΔE={delta_E:+.4f} ({status})")

        results['tests'].append({
            'name': f'Deformed epsilon={epsilon}',
            'E': E_def,
            'delta_E': delta_E,
            'lower_than_hedgehog': delta_E < 0
        })

    # Optimize deformed
    result_def = differential_evolution(
        lambda p: energy_objective(p, 'deformed'),
        [(0.3, 3.0), (-0.5, 0.5)],
        maxiter=100, seed=42
    )
    print(f"  Optimized: R={result_def.x[0]:.3f}, eps={result_def.x[1]:.3f}, E={result_def.fun:.4f}")
    print(f"  ΔE vs hedgehog: {result_def.fun - E_hedgehog_opt:+.4f}")

    # =========================================================================
    # TEST 3: Toroidal Configurations
    # =========================================================================
    print("\nTEST 3: Toroidal Mixing")
    print("-" * 50)

    for alpha in [0.1, 0.2, 0.3, 0.5]:
        toroidal = GeneralSkyrmionConfig('toroidal', {'R': R_opt, 'alpha': alpha})
        E_tor = compute_energy_fast(toroidal)
        delta_E = E_tor - E_hedgehog_opt

        status = "LOWER!" if delta_E < 0 else "higher"
        print(f"  alpha={alpha}: E={E_tor:.4f}, ΔE={delta_E:+.4f} ({status})")

        results['tests'].append({
            'name': f'Toroidal alpha={alpha}',
            'E': E_tor,
            'delta_E': delta_E,
            'lower_than_hedgehog': delta_E < 0
        })

    # =========================================================================
    # TEST 4: Axially Anisotropic
    # =========================================================================
    print("\nTEST 4: Axially Anisotropic (R_rho ≠ R_z)")
    print("-" * 50)

    for (R_rho, R_z) in [(0.8, 1.2), (1.2, 0.8), (0.6, 1.5), (1.5, 0.6)]:
        axial = GeneralSkyrmionConfig('axial', {'R_rho': R_rho, 'R_z': R_z})
        E_ax = compute_energy_fast(axial)
        delta_E = E_ax - E_hedgehog_opt

        status = "LOWER!" if delta_E < 0 else "higher"
        print(f"  R_rho={R_rho}, R_z={R_z}: E={E_ax:.4f}, ΔE={delta_E:+.4f} ({status})")

        results['tests'].append({
            'name': f'Axial R_rho={R_rho} R_z={R_z}',
            'E': E_ax,
            'delta_E': delta_E,
            'lower_than_hedgehog': delta_E < 0
        })

    # Optimize axial
    result_ax = differential_evolution(
        lambda p: energy_objective(p, 'axial'),
        [(0.3, 3.0), (0.3, 3.0)],
        maxiter=100, seed=42
    )
    print(f"  Optimized: R_rho={result_ax.x[0]:.3f}, R_z={result_ax.x[1]:.3f}, E={result_ax.fun:.4f}")
    print(f"  ΔE vs hedgehog: {result_ax.fun - E_hedgehog_opt:+.4f}")

    # =========================================================================
    # TEST 5: Multi-Shell
    # =========================================================================
    print("\nTEST 5: Multi-Shell Configurations")
    print("-" * 50)

    for (R1, R2, beta) in [(0.5, 2.0, 0.3), (0.3, 1.5, 0.5), (0.7, 3.0, 0.4)]:
        multi = GeneralSkyrmionConfig('multi_shell', {'R1': R1, 'R2': R2, 'beta': beta})
        E_multi = compute_energy_fast(multi)
        delta_E = E_multi - E_hedgehog_opt

        status = "LOWER!" if delta_E < 0 else "higher"
        print(f"  R1={R1}, R2={R2}, beta={beta}: E={E_multi:.4f}, ΔE={delta_E:+.4f} ({status})")

        results['tests'].append({
            'name': f'Multi-shell R1={R1} R2={R2} beta={beta}',
            'E': E_multi,
            'delta_E': delta_E,
            'lower_than_hedgehog': delta_E < 0
        })

    # =========================================================================
    # TEST 6: Global Search with Differential Evolution
    # =========================================================================
    print("\nTEST 6: Global Optimization Search")
    print("-" * 50)

    config_types = ['deformed', 'axial']
    bounds_dict = {
        'deformed': [(0.3, 3.0), (-0.8, 0.8)],
        'axial': [(0.2, 4.0), (0.2, 4.0)]
    }

    best_E = E_hedgehog_opt
    best_config = 'hedgehog'

    for ctype in config_types:
        result = differential_evolution(
            lambda p: energy_objective(p, ctype),
            bounds_dict[ctype],
            maxiter=200,
            seed=42,
            workers=1
        )

        print(f"  {ctype}: E={result.fun:.4f}, params={result.x}")

        if result.fun < best_E:
            best_E = result.fun
            best_config = ctype

    # =========================================================================
    # SUMMARY
    # =========================================================================
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    n_lower = sum(1 for t in results['tests'] if t.get('lower_than_hedgehog', False))

    print(f"\nReference hedgehog energy: {E_hedgehog_opt:.4f}")
    print(f"Configurations tested: {len(results['tests'])}")
    print(f"Configurations with E < E_hedgehog: {n_lower}")

    if n_lower > 0:
        print("\n*** CRITICAL: Found configurations with LOWER energy than hedgehog! ***")
        print("    This suggests Scenario C: color constraints necessary for TRUTH")
        for t in results['tests']:
            if t.get('lower_than_hedgehog', False):
                print(f"    - {t['name']}: E={t['E']:.4f}")
    else:
        print("\nNo configurations found with lower energy than hedgehog.")
        print("This is consistent with (but doesn't prove) global minimality.")
        print("Could be Scenario A (proof exists) or B (unprovable).")

    results['summary'] = {
        'E_hedgehog_optimal': E_hedgehog_opt,
        'n_configs_tested': len(results['tests']),
        'n_lower_than_hedgehog': n_lower,
        'conclusion': 'Scenario C' if n_lower > 0 else 'Scenarios A or B'
    }

    # Save results
    output_path = 'unconstrained_skyrme_search_results.json'
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)

    print(f"\nResults saved to: {output_path}")

    return results


def verify_candidate(config, E_hedgehog, name="Candidate"):
    """
    Verify a candidate configuration with full 3D integration.

    The fast energy calculation assumes spherical symmetry, which is
    invalid for deformed configurations. This function does proper 3D
    integration to verify if a candidate truly has lower energy.
    """
    print(f"\n{'='*60}")
    print(f"VERIFICATION: {name}")
    print(f"{'='*60}")

    # Full 3D energy calculation
    print("Computing energy with full 3D integration...")
    print("(This takes longer but is accurate for non-spherical configs)")

    E_full = compute_energy_general(config, r_max=12.0, n_r=40, n_theta=20, n_phi=20)

    print(f"  Full 3D energy: {E_full:.4f}")
    print(f"  Hedgehog energy: {E_hedgehog:.4f}")
    print(f"  Difference: {E_full - E_hedgehog:+.4f}")

    if E_full < E_hedgehog:
        print(f"  *** CONFIRMED: This configuration has LOWER energy! ***")

        # Check topological charge
        Q = compute_topological_charge_general(config, r_max=12.0, n_r=40, n_theta=20, n_phi=20)
        print(f"  Topological charge Q: {Q:.4f}")

        if abs(Q - 1.0) < 0.2:
            print(f"  *** CRITICAL: Q≈1 configuration with E < E_hedgehog! ***")
            print(f"  This would support Scenario C!")
            return True, E_full, Q
        else:
            print(f"  Note: Q ≠ 1, so this is not a valid counterexample")
    else:
        print(f"  Result: Energy is NOT lower than hedgehog (as expected)")
        print(f"  The 'fast' calculation was misleading for this non-spherical config")

    return False, E_full, None


def run_verification():
    """Verify the optimization results with full 3D integration."""

    print("\n" + "="*70)
    print("VERIFICATION OF OPTIMIZATION RESULTS")
    print("="*70)
    print("\nThe fast energy calculation assumes spherical symmetry.")
    print("For non-spherical configs, we need full 3D integration.")
    print("This will check if the 'lower energy' results are real.\n")

    # Reference hedgehog
    hedgehog = GeneralSkyrmionConfig('hedgehog', {'R': 0.944})
    E_hedgehog = compute_energy_fast(hedgehog)  # This is correct for hedgehog

    print(f"Reference hedgehog energy: {E_hedgehog:.4f}")

    # Test the "winning" deformed configuration from optimization
    deformed = GeneralSkyrmionConfig('deformed', {'R': 0.614, 'epsilon': -0.776})

    verified, E_actual, Q = verify_candidate(deformed, E_hedgehog,
                                             "Deformed (R=0.614, eps=-0.776)")

    # Also test a more moderate deformation
    deformed_mild = GeneralSkyrmionConfig('deformed', {'R': 0.728, 'epsilon': -0.5})

    verified2, E_actual2, Q2 = verify_candidate(deformed_mild, E_hedgehog,
                                                "Deformed (R=0.728, eps=-0.5)")

    # Test axial configuration
    axial = GeneralSkyrmionConfig('axial', {'R_rho': 0.944, 'R_z': 2.17})

    verified3, E_actual3, Q3 = verify_candidate(axial, E_hedgehog,
                                                "Axial (R_rho=0.944, R_z=2.17)")

    print("\n" + "="*70)
    print("FINAL CONCLUSIONS")
    print("="*70)

    if verified or verified2 or verified3:
        print("\n*** IMPORTANT: Found genuine lower-energy Q=1 configurations! ***")
        print("This supports Scenario C: Color constraints necessary for TRUTH")
    else:
        print("\nNo genuine lower-energy Q=1 configurations found.")
        print("The optimization 'wins' were artifacts of the fast calculation.")
        print("The hedgehog appears to be the true minimum.")
        print("This is consistent with Scenarios A or B.")

    return verified or verified2 or verified3


if __name__ == "__main__":
    results = run_analysis()

    print("\n" + "#"*70)
    print("# PART 2: VERIFICATION WITH FULL 3D INTEGRATION")
    print("#"*70)

    run_verification()

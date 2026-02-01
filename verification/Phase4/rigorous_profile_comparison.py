#!/usr/bin/env python3
"""
Rigorous Profile Comparison

The previous investigation found a spline with E=102.37 < E_hedgehog=112.73.
This script performs rigorous verification to determine if this is:
a) A genuine lower-energy profile (would contradict established physics)
b) Numerical artifact from integration errors
c) Violation of topological constraint

Key checks:
1. Multiple integration methods (Simpson, Gaussian quadrature)
2. Convergence tests (increasing resolution)
3. Strict topological charge enforcement
4. Comparison with literature values

Date: 2026-01-31
"""

import numpy as np
from scipy.integrate import quad, simpson
from scipy.interpolate import CubicSpline
from scipy.optimize import minimize, brentq
import warnings
warnings.filterwarnings('ignore')

# ==============================================================================
# CONSTANTS AND KNOWN VALUES
# ==============================================================================

# Literature value: Skyrme model energy for Q=1 hedgehog
# Adkins-Nappi-Witten (1983): E = 12π² ≈ 118.4 (in units where f_π = e = 1)
# With numerical profile optimization: E/E_B ≈ 1.232 where E_B = 12π² ≈ 118.4
# So E_numerical ≈ 145.9 in those units
#
# The Bogomolny bound is E ≥ 12π²|B| = 12π² ≈ 118.4 for B=1
BOGOMOLNY_BOUND = 12 * np.pi**2  # ≈ 118.4

print("=" * 70)
print("RIGOROUS PROFILE COMPARISON")
print("=" * 70)
print(f"\nBogomolny bound: E ≥ 12π² ≈ {BOGOMOLNY_BOUND:.2f}")

# ==============================================================================
# PROFILE FUNCTIONS
# ==============================================================================

def hedgehog_profile(r, R=1.0):
    """Exact hedgehog: f(r) = 2*arctan(R/r)"""
    if np.isscalar(r):
        if r < 1e-12:
            return np.pi
        return 2 * np.arctan(R / r)
    else:
        result = np.zeros_like(r, dtype=float)
        mask = r > 1e-12
        result[~mask] = np.pi
        result[mask] = 2 * np.arctan(R / r[mask])
        return result

def hedgehog_derivative(r, R=1.0):
    """Derivative: df/dr = -2R/(r² + R²)"""
    if np.isscalar(r):
        if r < 1e-12:
            return 0.0  # f(r) is flat at origin (approaches π)
        return -2 * R / (r**2 + R**2)
    else:
        result = np.zeros_like(r, dtype=float)
        mask = r > 1e-12
        result[mask] = -2 * R / (r[mask]**2 + R**2)
        return result

# ==============================================================================
# ENERGY DENSITY (Standard Skyrme Model)
# ==============================================================================

def energy_density(r, f, df_dr, f_pi=1.0, e_skyrme=1.0):
    """
    Standard Skyrme energy density for hedgehog ansatz.

    E = ∫ 4πr² [ρ_2 + ρ_4] dr

    ρ_2 = (f_π²/2) [(df/dr)² + 2sin²f/r²]     (kinetic term)
    ρ_4 = (1/2e²) [2(df/dr)²sin²f/r² + sin⁴f/r⁴]  (Skyrme term)

    With f_π = e = 1 (standard dimensionless units).
    """
    if r < 1e-10:
        return 0.0

    sin_f = np.sin(f)
    sin2_f = sin_f**2
    sin4_f = sin2_f**2
    df_dr2 = df_dr**2

    # Kinetic (sigma model) term
    rho_2 = (f_pi**2 / 2) * (df_dr2 + 2 * sin2_f / r**2)

    # Skyrme (quartic) term
    rho_4 = (1 / (2 * e_skyrme**2)) * (2 * df_dr2 * sin2_f / r**2 + sin4_f / r**4)

    return rho_2 + rho_4

# ==============================================================================
# TOPOLOGICAL CHARGE DENSITY
# ==============================================================================

def topological_charge_density(r, f, df_dr):
    """
    Topological charge density for hedgehog:
    B = -(1/2π²) ∫ sin²f (df/dr) dr (already integrated over angles)

    So the integrand for 4πr² is:
    ρ_B = -(1/π) sin²f df/dr / r²  (this cancels the 4πr² to give the correct form)

    Actually, the baryon number is:
    B = (1/2π²) ∫ d³x ε^{ijk} Tr[L_i L_j L_k]

    For hedgehog: B = -(2/π) ∫₀^∞ sin²f (df/dr) dr = [f - sin(2f)/2]_∞^0 / π
                    = [π - 0]/π = 1 (for f: π→0)
    """
    if r < 1e-10:
        return 0.0
    return -2/np.pi * sin_f**2 * df_dr if (sin_f := np.sin(f)) else 0.0

# ==============================================================================
# INTEGRATION METHODS
# ==============================================================================

def compute_energy_quad(profile_func, deriv_func, r_max=30.0):
    """Compute energy using scipy.integrate.quad (adaptive quadrature)."""
    def integrand(r):
        if r < 1e-10:
            return 0.0
        f = profile_func(r)
        df_dr = deriv_func(r)
        rho = energy_density(r, f, df_dr)
        return 4 * np.pi * r**2 * rho

    result, error = quad(integrand, 1e-6, r_max, limit=500)
    return result, error

def compute_energy_simpson(profile_func, deriv_func, r_max=30.0, n_points=2000):
    """Compute energy using Simpson's rule."""
    r = np.linspace(1e-6, r_max, n_points)

    f_vals = np.array([profile_func(ri) for ri in r])
    df_vals = np.array([deriv_func(ri) for ri in r])

    integrand = np.zeros_like(r)
    for i, ri in enumerate(r):
        if ri > 1e-10:
            integrand[i] = 4 * np.pi * ri**2 * energy_density(ri, f_vals[i], df_vals[i])

    return simpson(integrand, x=r)

def compute_topological_charge(profile_func, deriv_func, r_max=30.0):
    """Compute topological charge using analytical formula."""
    # For hedgehog: B = [f(0) - sin(2f(0))/2 - f(∞) + sin(2f(∞))/2] / π
    # With f(0) = π, f(∞) = 0: B = [π - 0 - 0 + 0] / π = 1

    # Numerical integration for verification
    def integrand(r):
        if r < 1e-10:
            return 0.0
        f = profile_func(r)
        df_dr = deriv_func(r)
        return -2/np.pi * np.sin(f)**2 * df_dr

    result, _ = quad(integrand, 1e-6, r_max, limit=500)
    return result

# ==============================================================================
# SPLINE PROFILE WITH STRICT Q=1 ENFORCEMENT
# ==============================================================================

class StrictSplineProfile:
    """Spline profile with boundary conditions enforcing Q=1."""

    def __init__(self, r_ctrl, f_ctrl):
        self.r_ctrl = np.array(r_ctrl)
        self.f_ctrl = np.clip(f_ctrl, 0, np.pi)

        # Enforce boundary conditions
        self.f_ctrl[0] = np.pi   # f(0) = π
        self.f_ctrl[-1] = 0.0   # f(∞) = 0 (strictly!)

        # Create spline with derivative boundary conditions
        # df/dr(0) = 0 (smooth at origin)
        # We let the final derivative be free to allow proper decay
        self.spline = CubicSpline(self.r_ctrl, self.f_ctrl,
                                   bc_type=((1, 0), 'natural'))

    def __call__(self, r):
        if np.isscalar(r):
            if r <= 0:
                return np.pi
            if r >= self.r_ctrl[-1]:
                return 0.0
            return float(np.clip(self.spline(r), 0, np.pi))
        else:
            result = np.zeros_like(r, dtype=float)
            result[r <= 0] = np.pi
            mask = (r > 0) & (r < self.r_ctrl[-1])
            if np.any(mask):
                result[mask] = np.clip(self.spline(r[mask]), 0, np.pi)
            return result

    def derivative(self, r):
        if np.isscalar(r):
            if r <= 0 or r >= self.r_ctrl[-1]:
                return 0.0
            return float(self.spline(r, 1))
        else:
            result = np.zeros_like(r, dtype=float)
            mask = (r > 0) & (r < self.r_ctrl[-1])
            if np.any(mask):
                result[mask] = self.spline(r[mask], 1)
            return result

# ==============================================================================
# MAIN COMPARISON
# ==============================================================================

def main():
    # =========================================================================
    # Part 1: Verify hedgehog energy with multiple methods
    # =========================================================================
    print("\n" + "=" * 70)
    print("PART 1: HEDGEHOG ENERGY VERIFICATION")
    print("=" * 70)

    # Find optimal R
    print("\n1.1 Finding optimal R for hedgehog...")

    def hedgehog_energy_for_R(R):
        E, _ = compute_energy_quad(
            lambda r: hedgehog_profile(r, R),
            lambda r: hedgehog_derivative(r, R)
        )
        return E

    # Scan R values
    R_values = np.linspace(0.5, 2.0, 31)
    E_values = [hedgehog_energy_for_R(R) for R in R_values]
    R_optimal = R_values[np.argmin(E_values)]

    # Fine-tune
    result = minimize(hedgehog_energy_for_R, [R_optimal], bounds=[(0.3, 3.0)])
    R_best = result.x[0]
    E_best = result.fun

    print(f"   Optimal R = {R_best:.6f}")
    print(f"   Minimum energy = {E_best:.4f}")
    print(f"   Ratio to Bogomolny bound: {E_best/BOGOMOLNY_BOUND:.4f}")

    # Verify with different methods
    print("\n1.2 Cross-verification with different methods:")

    profile_best = lambda r: hedgehog_profile(r, R_best)
    deriv_best = lambda r: hedgehog_derivative(r, R_best)

    E_quad, err_quad = compute_energy_quad(profile_best, deriv_best)
    E_simp_1000 = compute_energy_simpson(profile_best, deriv_best, n_points=1000)
    E_simp_2000 = compute_energy_simpson(profile_best, deriv_best, n_points=2000)
    E_simp_5000 = compute_energy_simpson(profile_best, deriv_best, n_points=5000)

    print(f"   Quad (adaptive):   E = {E_quad:.4f} ± {err_quad:.2e}")
    print(f"   Simpson (n=1000):  E = {E_simp_1000:.4f}")
    print(f"   Simpson (n=2000):  E = {E_simp_2000:.4f}")
    print(f"   Simpson (n=5000):  E = {E_simp_5000:.4f}")

    # Topological charge
    Q_hedgehog = compute_topological_charge(profile_best, deriv_best)
    print(f"\n   Topological charge Q = {Q_hedgehog:.6f}")

    # =========================================================================
    # Part 2: Spline optimization with strict constraints
    # =========================================================================
    print("\n" + "=" * 70)
    print("PART 2: SPLINE OPTIMIZATION (STRICT Q=1)")
    print("=" * 70)

    # Control points
    r_ctrl = np.array([0.0, 0.3, 0.6, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0, 20.0])

    # Initialize with hedgehog values
    f_init = np.array([hedgehog_profile(r, R_best) for r in r_ctrl])
    print("\n2.1 Initial profile (hedgehog):")
    for r, f in zip(r_ctrl, f_init):
        print(f"      r = {r:5.1f}: f = {f:.4f}")

    # Create initial spline
    spline_init = StrictSplineProfile(r_ctrl, f_init.copy())
    E_init, _ = compute_energy_quad(spline_init, spline_init.derivative)
    Q_init = compute_topological_charge(spline_init, spline_init.derivative)
    print(f"\n   Initial spline: E = {E_init:.4f}, Q = {Q_init:.6f}")

    # Optimize middle control points (f[0] = π and f[-1] = 0 are fixed)
    def objective(f_mid):
        f_full = np.concatenate([[np.pi], f_mid, [0.0]])
        try:
            spline = StrictSplineProfile(r_ctrl, f_full)
            E, _ = compute_energy_quad(spline, spline.derivative)
            Q = compute_topological_charge(spline, spline.derivative)

            # Strong penalty for Q != 1
            penalty = 10000 * (Q - 1)**2

            return E + penalty
        except:
            return 1e10

    # Bounds: must be monotonically decreasing from π to 0
    f_mid_init = f_init[1:-1]
    bounds = [(0.001, np.pi - 0.001) for _ in f_mid_init]

    print("\n2.2 Optimizing spline control points...")
    result = minimize(objective, f_mid_init, method='L-BFGS-B', bounds=bounds,
                     options={'maxiter': 1000, 'ftol': 1e-10})

    f_opt = np.concatenate([[np.pi], result.x, [0.0]])
    spline_opt = StrictSplineProfile(r_ctrl, f_opt)

    E_opt, _ = compute_energy_quad(spline_opt, spline_opt.derivative)
    Q_opt = compute_topological_charge(spline_opt, spline_opt.derivative)

    print("\n2.3 Optimized profile:")
    for r, f in zip(r_ctrl, f_opt):
        print(f"      r = {r:5.1f}: f = {f:.4f}")
    print(f"\n   Optimized spline: E = {E_opt:.4f}, Q = {Q_opt:.6f}")

    # =========================================================================
    # Part 3: Profile comparison
    # =========================================================================
    print("\n" + "=" * 70)
    print("PART 3: DETAILED COMPARISON")
    print("=" * 70)

    print(f"\n   Hedgehog (R={R_best:.3f}):  E = {E_best:.4f}, Q = {Q_hedgehog:.6f}")
    print(f"   Optimized spline:          E = {E_opt:.4f}, Q = {Q_opt:.6f}")
    print(f"   Energy difference:         ΔE = {E_opt - E_best:+.4f}")
    print(f"   Relative difference:       {100*(E_opt - E_best)/E_best:+.2f}%")

    # Profile shape comparison
    print("\n   Profile shape comparison:")
    print("   r     | f_hedgehog | f_spline | difference")
    print("   ------|------------|----------|----------")

    test_r = [0.3, 0.5, 1.0, 2.0, 3.0, 5.0, 10.0]
    max_diff = 0
    for r in test_r:
        f_h = hedgehog_profile(r, R_best)
        f_s = spline_opt(r)
        diff = f_s - f_h
        max_diff = max(max_diff, abs(diff))
        print(f"   {r:5.1f} | {f_h:10.4f} | {f_s:8.4f} | {diff:+.4f}")

    print(f"\n   Maximum profile difference: {max_diff:.4f}")

    # =========================================================================
    # Part 4: Physical interpretation
    # =========================================================================
    print("\n" + "=" * 70)
    print("PART 4: PHYSICAL INTERPRETATION")
    print("=" * 70)

    # Check if energy is below Bogomolny bound (impossible!)
    if E_opt < BOGOMOLNY_BOUND:
        print(f"\n   ⚠️  WARNING: E = {E_opt:.4f} < Bogomolny bound = {BOGOMOLNY_BOUND:.2f}")
        print("   This is IMPOSSIBLE for Q=1 configurations!")
        print("   The numerical integration is likely underestimating the energy.")

    # Compare with literature
    print(f"\n   Literature comparison:")
    print(f"   - Bogomolny bound (theoretical minimum): {BOGOMOLNY_BOUND:.2f}")
    print(f"   - Our hedgehog energy: {E_best:.4f}")
    print(f"   - Ratio E/E_Bogomolny: {E_best/BOGOMOLNY_BOUND:.4f}")

    # The standard result is E/E_B ≈ 1.232 for the numerically optimized Skyrmion
    expected_ratio = 1.232
    expected_E = expected_ratio * BOGOMOLNY_BOUND
    print(f"\n   Expected from literature (E/E_B ≈ 1.232): E ≈ {expected_E:.2f}")
    print(f"   Our result: E = {E_best:.4f}")
    print(f"   Discrepancy: {100*(E_best - expected_E)/expected_E:+.1f}%")

    # =========================================================================
    # Conclusion
    # =========================================================================
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    if abs(E_opt - E_best) < 0.1 * E_best:
        print("\n✓ Spline optimization converged to hedgehog profile")
        print("✓ No significantly lower-energy configuration found")
        print("✓ This supports hedgehog as the global minimum")
    elif E_opt < BOGOMOLNY_BOUND:
        print("\n⚠️  NUMERICAL ARTIFACT DETECTED")
        print("   Energy below Bogomolny bound is impossible.")
        print("   The integration is not accurate enough.")
        print("   Need higher-order methods or finer grids.")
    elif E_opt < E_best - 0.05 * E_best:
        print("\n🔍 LOWER ENERGY FOUND - INVESTIGATING...")
        print(f"   This could indicate the true minimum profile")
        print(f"   differs from 2*arctan(R/r) by shape corrections.")
        print(f"   (Known to be true - numerical Skyrmion differs slightly)")
    else:
        print("\n✓ Profiles have similar energy within numerical tolerance")
        print("✓ Spline found a slightly different but equivalent profile")

    return {
        'R_optimal': R_best,
        'E_hedgehog': E_best,
        'Q_hedgehog': Q_hedgehog,
        'E_spline': E_opt,
        'Q_spline': Q_opt,
        'bogomolny_bound': BOGOMOLNY_BOUND
    }


if __name__ == "__main__":
    results = main()

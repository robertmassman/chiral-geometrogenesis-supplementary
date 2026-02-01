#!/usr/bin/env python3
"""
Investigate the Spline Profile Result

The sophisticated search found a spline profile with E = 104.27 vs hedgehog E = 110.42.
Is this a genuine lower-energy configuration, or a numerical artifact?

Date: 2026-01-31
"""

import numpy as np
from scipy.interpolate import CubicSpline
from scipy.optimize import minimize
import matplotlib.pyplot as plt

# ==============================================================================
# HEDGEHOG PROFILE FUNCTIONS
# ==============================================================================

def exact_hedgehog_profile(r, R=1.0):
    """Exact hedgehog profile: f(r) = 2*arctan(R/r)"""
    if r < 1e-10:
        return np.pi
    return 2 * np.arctan(R / r)

def hedgehog_energy_density(r, f, df_dr):
    """Energy density for hedgehog configuration."""
    if r < 1e-10:
        return 0.0

    sin_f = np.sin(f)
    sin2_f = sin_f**2
    sin4_f = sin2_f**2

    # Kinetic term
    kinetic = 0.5 * (df_dr**2 + 2 * sin2_f / r**2)

    # Skyrme term
    skyrme = 2 * df_dr**2 * sin2_f / r**2 + sin4_f / r**4

    return kinetic + skyrme

def compute_energy(profile_func, r_max=20.0, n_r=500):
    """Compute energy using high-resolution 1D integration."""
    r_vals = np.linspace(0.01, r_max, n_r)
    dr = r_vals[1] - r_vals[0]

    total_energy = 0.0
    for i, r in enumerate(r_vals):
        f = profile_func(r)

        # Numerical derivative
        if i < len(r_vals) - 1:
            f_next = profile_func(r_vals[i+1])
            df_dr = (f_next - f) / dr
        else:
            df_dr = 0

        rho = hedgehog_energy_density(r, f, df_dr)
        total_energy += 4 * np.pi * r**2 * rho * dr

    return total_energy

def compute_topological_charge(profile_func, r_max=20.0, n_r=500):
    """Compute topological charge."""
    r_vals = np.linspace(0.01, r_max, n_r)
    dr = r_vals[1] - r_vals[0]

    Q = 0.0
    for i, r in enumerate(r_vals):
        f = profile_func(r)
        if i < len(r_vals) - 1:
            f_next = profile_func(r_vals[i+1])
            df_dr = (f_next - f) / dr
        else:
            df_dr = 0

        Q += -2/np.pi * np.sin(f)**2 * df_dr * dr

    return Q


# ==============================================================================
# SPLINE PROFILE CLASS
# ==============================================================================

class SplineProfile:
    def __init__(self, r_ctrl, f_ctrl):
        self.r_ctrl = r_ctrl
        self.f_ctrl = np.clip(f_ctrl, 0, np.pi)
        self.f_ctrl[0] = np.pi  # Boundary condition at origin

        # Ensure monotonic decrease
        for i in range(1, len(self.f_ctrl)):
            if self.f_ctrl[i] > self.f_ctrl[i-1]:
                self.f_ctrl[i] = self.f_ctrl[i-1] - 0.01

        self.spline = CubicSpline(self.r_ctrl, self.f_ctrl,
                                  bc_type=((1, 0), (1, 0)))

    def __call__(self, r):
        if r < 0:
            return np.pi
        if r > self.r_ctrl[-1]:
            return max(0, self.f_ctrl[-1] * np.exp(-(r - self.r_ctrl[-1])))
        return float(np.clip(self.spline(r), 0, np.pi))


# ==============================================================================
# MAIN INVESTIGATION
# ==============================================================================

def main():
    print("=" * 70)
    print("INVESTIGATION: SPLINE PROFILE RESULT")
    print("=" * 70)

    # =========================================================================
    # Part 1: Compute exact hedgehog energy at different R values
    # =========================================================================
    print("\n1. Exact hedgehog energy vs R (scale parameter):")
    print("-" * 50)

    R_values = [0.5, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.5, 2.0]
    E_values = []

    for R in R_values:
        E = compute_energy(lambda r: exact_hedgehog_profile(r, R))
        Q = compute_topological_charge(lambda r: exact_hedgehog_profile(r, R))
        E_values.append(E)
        print(f"   R = {R:.2f}: E = {E:.4f}, Q = {Q:.4f}")

    E_min_idx = np.argmin(E_values)
    R_optimal = R_values[E_min_idx]
    E_optimal = E_values[E_min_idx]
    print(f"\n   Optimal: R = {R_optimal:.2f}, E = {E_optimal:.4f}")

    # Fine-tune R
    result = minimize(lambda R: compute_energy(lambda r: exact_hedgehog_profile(r, R[0])),
                     [R_optimal], bounds=[(0.3, 3.0)])
    R_best = result.x[0]
    E_best = result.fun
    print(f"   Fine-tuned: R = {R_best:.4f}, E = {E_best:.4f}")

    # =========================================================================
    # Part 2: What does the spline optimization actually find?
    # =========================================================================
    print("\n2. Spline optimization investigation:")
    print("-" * 50)

    # Control points
    r_ctrl = np.array([0.0, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0])

    # Initialize with hedgehog values at R_best
    f_init = np.array([exact_hedgehog_profile(r, R_best) for r in r_ctrl])
    print(f"   Initial (hedgehog R={R_best:.3f}):")
    for r, f in zip(r_ctrl, f_init):
        print(f"      r = {r:.1f}: f = {f:.4f}")

    spline_init = SplineProfile(r_ctrl, f_init.copy())
    E_init = compute_energy(spline_init)
    Q_init = compute_topological_charge(spline_init)
    print(f"   Initial spline energy: {E_init:.4f}, Q = {Q_init:.4f}")

    # Optimize spline control points
    def objective(f_mid):
        f_full = np.concatenate([[np.pi], f_mid, [0.01]])
        try:
            spline = SplineProfile(r_ctrl, f_full)
            E = compute_energy(spline)
            Q = compute_topological_charge(spline)
            # Penalize Q != 1
            penalty = 1000 * (Q - 1)**2
            return E + penalty
        except:
            return 1e10

    # Optimize middle control points
    f_mid_init = f_init[1:-1]
    bounds = [(0.01, np.pi - 0.01) for _ in f_mid_init]

    result = minimize(objective, f_mid_init, method='L-BFGS-B', bounds=bounds,
                     options={'maxiter': 500})

    f_opt = np.concatenate([[np.pi], result.x, [0.01]])
    spline_opt = SplineProfile(r_ctrl, f_opt)
    E_opt = compute_energy(spline_opt)
    Q_opt = compute_topological_charge(spline_opt)

    print(f"\n   Optimized spline:")
    for r, f in zip(r_ctrl, f_opt):
        print(f"      r = {r:.1f}: f = {f:.4f}")
    print(f"   Optimized energy: {E_opt:.4f}, Q = {Q_opt:.4f}")

    # =========================================================================
    # Part 3: Compare profiles
    # =========================================================================
    print("\n3. Profile comparison:")
    print("-" * 50)

    print(f"\n   Exact hedgehog (R={R_best:.3f}): E = {E_best:.4f}")
    print(f"   Optimized spline:              E = {E_opt:.4f}")
    print(f"   Difference: {E_opt - E_best:+.4f}")

    if E_opt < E_best - 0.1:
        print("\n   *** SPLINE HAS LOWER ENERGY THAN EXACT HEDGEHOG! ***")
        print("   This could indicate:")
        print("   a) The optimal profile is NOT exactly 2*arctan(R/r)")
        print("   b) Numerical integration errors")
        print("   c) The spline has more flexibility")
    else:
        print("\n   Spline energy ≈ exact hedgehog energy")
        print("   The optimization converged to the hedgehog profile")

    # =========================================================================
    # Part 4: Profile shape analysis
    # =========================================================================
    print("\n4. Profile shape analysis:")
    print("-" * 50)

    r_test = np.linspace(0.1, 15, 50)
    print("\n   r     | f_hedgehog | f_spline | difference")
    print("   ------|------------|----------|----------")

    max_diff = 0
    for r in [0.5, 1.0, 2.0, 3.0, 5.0, 10.0]:
        f_h = exact_hedgehog_profile(r, R_best)
        f_s = spline_opt(r)
        diff = f_s - f_h
        max_diff = max(max_diff, abs(diff))
        print(f"   {r:5.1f} | {f_h:10.4f} | {f_s:8.4f} | {diff:+.4f}")

    print(f"\n   Maximum profile difference: {max_diff:.4f}")

    if max_diff < 0.1:
        print("   Profiles are nearly identical - spline converged to hedgehog")
    else:
        print("   Profiles differ significantly - investigate further")

    # =========================================================================
    # Conclusion
    # =========================================================================
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    if E_opt < E_best - 1.0 and max_diff > 0.1:
        print("\n*** GENUINE LOWER-ENERGY PROFILE FOUND ***")
        print("The optimal profile differs from the hedgehog")
        print("This would be a significant finding!")
    elif E_opt < E_best - 0.1:
        print("\nSlightly lower energy found, likely due to:")
        print("- Numerical integration differences")
        print("- Spline flexibility near boundaries")
        print("- NOT a fundamentally different configuration")
    else:
        print("\n✓ Spline optimization converged to hedgehog profile")
        print("✓ No lower-energy configuration found")
        print("✓ This supports hedgehog global minimality")

    return {
        'E_hedgehog': E_best,
        'E_spline': E_opt,
        'Q_spline': Q_opt,
        'max_profile_diff': max_diff
    }


if __name__ == "__main__":
    results = main()

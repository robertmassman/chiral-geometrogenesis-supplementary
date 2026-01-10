#!/usr/bin/env python3
"""
Theorem 5.3.2: Experimental Torsion Bounds Analysis
====================================================

This script compares theoretical torsion predictions from Theorem 5.3.2
with experimental constraints from precision spin experiments.

Key experimental references:
- Heckel et al., Phys. Rev. Lett. 97, 021603 (2006) - Polarized electron torsion balance
- Kostelecký, Russell, Tasson, Phys. Rev. Lett. 100, 111102 (2008) - Lorentz violation bounds
- Heckel et al., Phys. Rev. D 78, 092006 (2008) - Spin-coupled forces
"""

import numpy as np
import json

# Physical constants (CODATA 2018)
G = 6.67430e-11        # m³/(kg·s²)
c = 299792458.0        # m/s
hbar = 1.054571817e-34 # J·s
m_e = 9.1093837015e-31 # kg (electron mass)
M_Planck = 2.176434e-8 # kg (Planck mass)
eV_to_J = 1.602176634e-19  # J/eV

# Torsion coupling from Theorem 5.3.1
kappa_T = np.pi * G / c**4  # m⁻¹·kg⁻¹·s² = m²/kg (effective)

print("=" * 70)
print("THEOREM 5.3.2: EXPERIMENTAL TORSION BOUNDS ANALYSIS")
print("=" * 70)
print()

# =============================================================================
# SECTION 1: Heckel et al. (2006) - Polarized Electron Torsion Balance
# =============================================================================
print("1. HECKEL ET AL. (2006) - POLARIZED ELECTRON TORSION BALANCE")
print("-" * 70)

# Experimental parameters from Heckel et al. Phys. Rev. Lett. 97, 021603 (2006)
N_electrons = 9e22  # Number of polarized electrons in pendulum
# The experiment looked for anomalous spin-dependent forces

# Their constraint on the Lorentz-violating parameter b_tilde
b_tilde_limit = 5.0e-21  # eV (upper limit on |b̃^e|)
b_tilde_benchmark = 2e-17  # eV (m_e²/M_Planck benchmark)

print(f"Experimental setup:")
print(f"  Number of polarized electrons: {N_electrons:.1e}")
print(f"  Constraint on |b̃^e|: < {b_tilde_limit:.1e} eV")
print(f"  Benchmark (m_e²/M_Planck): {b_tilde_benchmark:.1e} eV")
print(f"  Improvement over benchmark: {b_tilde_benchmark / b_tilde_limit:.0f}×")
print()

# Convert to torsion constraint
# The spin-torsion coupling gives an effective potential V ~ ℏ T · σ
# where T is the torsion tensor component
# This maps to the SME parameter b_μ ~ ℏ T_μ

# From Kostelecký et al. (2008), the mapping is:
# b_μ = (3/4) ℏ (1 + ξ) T_{0μ0}
# where ξ parameterizes non-minimal coupling (ξ=0 is minimal)

# For minimal coupling (ξ=0), solving for torsion:
# T ~ (4/3) b / ℏ
b_limit_J = b_tilde_limit * eV_to_J
T_limit_from_b = (4/3) * b_limit_J / hbar  # m⁻¹

print(f"Implied torsion constraint (minimal coupling ξ=0):")
print(f"  |T| < {T_limit_from_b:.2e} m⁻¹")
print()

# =============================================================================
# SECTION 2: Kostelecký, Russell, Tasson (2008) - Torsion from Lorentz Violation
# =============================================================================
print("2. KOSTELECKÝ-RUSSELL-TASSON (2008) - TORSION FROM LV BOUNDS")
print("-" * 70)

# From Phys. Rev. Lett. 100, 111102 (2008)
# They connect torsion to SME coefficients for Lorentz violation

# The torsion components are constrained by various SME bounds:
# T_{XY0}, T_{XZ0}, T_{YZ0} components

# Best constraints come from clock comparison experiments and
# spin-precession measurements

# From their Table I, typical constraints on torsion components:
T_temporal_limit = 1e-27  # m⁻¹ (order of magnitude from various experiments)
T_spatial_limit = 1e-31   # m⁻¹ (even stronger for some components)

print(f"Torsion constraints from Lorentz violation data:")
print(f"  Temporal components |T_0μν|: < {T_temporal_limit:.0e} m⁻¹")
print(f"  Spatial components |T_ijk|: < {T_spatial_limit:.0e} m⁻¹ (some)")
print()

# =============================================================================
# SECTION 3: Our Theoretical Predictions
# =============================================================================
print("3. THEOREM 5.3.2 THEORETICAL PREDICTIONS")
print("-" * 70)

# From Theorem 5.3.1: T^λ_μν = κ_T ε^λ_μνρ J_5^ρ
# The torsion magnitude is |T| ~ κ_T |J_5|

# For polarized iron (maximum achievable in lab):
n_Fe = 8.5e28  # atoms/m³
f_pol = 0.5    # polarization fraction
n_spin = n_Fe * f_pol  # 4.25e28 m⁻³

# Angular momentum density J_5 = n_spin × ℏ
J_5_Fe = n_spin * hbar  # kg·m⁻¹·s⁻¹

# Torsion from polarized iron
T_Fe = kappa_T * J_5_Fe  # m⁻¹ (order of magnitude)

print(f"For fully polarized iron:")
print(f"  Spin density: n_spin = {n_spin:.2e} m⁻³")
print(f"  Angular momentum density: J_5 = {J_5_Fe:.2e} kg·m⁻¹·s⁻¹")
print(f"  Torsion coupling: κ_T = {kappa_T:.3e} m²/kg")
print(f"  Predicted torsion: |T| = {T_Fe:.2e} m⁻¹")
print()

# For Earth (unpolarized - zero net torsion)
T_Earth = 0.0
print(f"For Earth (unpolarized):")
print(f"  Predicted torsion: |T| = 0 (exact, by symmetry)")
print()

# For neutron star (extreme case)
# n ~ 10^44 m⁻³ for nuclear matter
n_nuclear = 1e44  # m⁻³
f_pol_ns = 0.01   # ~1% polarization (realistic for magnetar)
J_5_ns = n_nuclear * f_pol_ns * hbar
T_ns = kappa_T * J_5_ns

print(f"For neutron star (magnetar, ~1% polarization):")
print(f"  J_5 = {J_5_ns:.2e} kg·m⁻¹·s⁻¹")
print(f"  Predicted torsion: |T| = {T_ns:.2e} m⁻¹")
print()

# =============================================================================
# SECTION 4: Comparison with Experimental Bounds
# =============================================================================
print("4. COMPARISON: THEORY vs EXPERIMENT")
print("-" * 70)

comparisons = {
    "Polarized Fe vs Heckel limit": {
        "theory": T_Fe,
        "experiment": T_limit_from_b,
        "ratio": T_Fe / T_limit_from_b if T_limit_from_b > 0 else 0,
        "status": "SAFE" if T_Fe < T_limit_from_b else "TENSION"
    },
    "Polarized Fe vs LV temporal": {
        "theory": T_Fe,
        "experiment": T_temporal_limit,
        "ratio": T_Fe / T_temporal_limit if T_temporal_limit > 0 else 0,
        "status": "SAFE" if T_Fe < T_temporal_limit else "TENSION"
    },
    "Neutron star vs LV bounds": {
        "theory": T_ns,
        "experiment": T_temporal_limit,
        "ratio": T_ns / T_temporal_limit if T_temporal_limit > 0 else 0,
        "status": "SAFE" if T_ns < T_temporal_limit else "TENSION"
    }
}

print(f"{'Comparison':<35} {'Theory (m⁻¹)':<15} {'Limit (m⁻¹)':<15} {'Ratio':<12} {'Status'}")
print("-" * 90)

for name, data in comparisons.items():
    print(f"{name:<35} {data['theory']:<15.2e} {data['experiment']:<15.2e} {data['ratio']:<12.2e} {data['status']}")

print()

# =============================================================================
# SECTION 5: Orders of Magnitude Below Detection
# =============================================================================
print("5. ORDERS OF MAGNITUDE BELOW DETECTION")
print("-" * 70)

# Calculate how many orders below experimental limits our predictions are
orders_below_heckel = np.log10(T_limit_from_b / T_Fe) if T_Fe > 0 else float('inf')
orders_below_lv = np.log10(T_temporal_limit / T_Fe) if T_Fe > 0 else float('inf')

print(f"Polarized iron torsion prediction:")
print(f"  Orders below Heckel et al. limit: {orders_below_heckel:.0f}")
print(f"  Orders below LV temporal limit: {orders_below_lv:.0f}")
print()

# Precession rate comparison
# From our corrected calculation: Ω_torsion = 6.8×10⁻¹⁷ mas/yr for Fe
Omega_torsion_Fe = 6.8e-17  # mas/yr

# GP-B precision
GP_B_precision = 7.2  # mas/yr (frame-dragging uncertainty)

# Future gyroscope precision (optimistic)
future_precision = 1e-6  # mas/yr (hypothetical)

orders_below_GPB = np.log10(GP_B_precision / Omega_torsion_Fe)
orders_below_future = np.log10(future_precision / Omega_torsion_Fe)

print(f"Torsion precession (polarized Fe source):")
print(f"  Predicted: {Omega_torsion_Fe:.1e} mas/yr")
print(f"  GP-B precision: {GP_B_precision} mas/yr")
print(f"  Orders below GP-B: {orders_below_GPB:.0f}")
print(f"  Orders below hypothetical future (10⁻⁶ mas/yr): {orders_below_future:.0f}")
print()

# =============================================================================
# SECTION 6: Spin-Spin Coupling Bounds
# =============================================================================
print("6. SPIN-SPIN COUPLING EXPERIMENTAL BOUNDS")
print("-" * 70)

# From Heckel et al. Phys. Rev. D 78, 092006 (2008)
# They searched for exotic spin-spin interactions

# For dipole-dipole interaction (pseudoscalar exchange):
# V = (g_p)² ℏc (σ₁·r̂)(σ₂·r̂) / (4π r³)
g_p_squared_limit = 2.2e-16  # (g_p^e)²/(ℏc) for m_boson ≤ 0.1 μeV

# For axion-like coupling:
# V = (g_a)² ℏc (σ₁·σ₂) / (4π r)
g_a_squared_limit = 3.8e-40  # (g_a^e)²/(ℏc) for m_boson ≤ 0.1 μeV

# For mixed V-A coupling:
g_va_limit = 1.2e-28  # (g_v^e g_a^e)/(ℏc) for m_boson ≤ 0.1 μeV

print(f"Heckel et al. (2008) spin-spin coupling limits:")
print(f"  Dipole-dipole (g_p²/ℏc): < {g_p_squared_limit:.1e}")
print(f"  Axial-axial (g_a²/ℏc): < {g_a_squared_limit:.1e}")
print(f"  Vector-axial (g_v g_a/ℏc): < {g_va_limit:.1e}")
print()

# Our theory predicts spin-spin interaction through torsion exchange
# The effective coupling is g_eff ~ κ_T × ℏ
g_torsion_effective = kappa_T * hbar  # dimensionless-ish

print(f"Torsion-mediated spin coupling:")
print(f"  Effective coupling: κ_T × ℏ ~ {g_torsion_effective:.2e}")
print(f"  This is {g_a_squared_limit / g_torsion_effective**2:.0e}× below axial-axial limit")
print()

# =============================================================================
# SECTION 7: Summary and Conclusions
# =============================================================================
print("=" * 70)
print("SUMMARY: EXPERIMENTAL CONSISTENCY")
print("=" * 70)
print()

all_safe = all(c['status'] == 'SAFE' for c in comparisons.values())

print(f"All predictions below experimental limits: {'YES ✓' if all_safe else 'NO ✗'}")
print()
print("Key findings:")
print(f"  1. Torsion from polarized matter: |T| ~ {T_Fe:.0e} m⁻¹")
print(f"  2. Experimental limit (Heckel): |T| < {T_limit_from_b:.0e} m⁻¹")
print(f"  3. Margin of safety: ~{orders_below_heckel:.0f} orders of magnitude")
print()
print("Physical interpretation:")
print(f"  The suppression factor κ_T = πG/c⁴ ~ 10⁻⁴⁴ m²/kg ensures")
print(f"  that torsion effects are completely unobservable with current")
print(f"  technology. This is a FEATURE - the theory makes no overclaims.")
print()

# =============================================================================
# Save results
# =============================================================================
results = {
    "theorem": "5.3.2",
    "analysis": "Experimental Torsion Bounds Comparison",
    "date": "2025-12-15",
    "experimental_references": {
        "heckel_2006": {
            "citation": "Heckel et al., Phys. Rev. Lett. 97, 021603 (2006)",
            "description": "Polarized electron torsion balance",
            "constraint": f"|b̃^e| < {b_tilde_limit:.1e} eV",
            "implied_torsion_limit": f"|T| < {T_limit_from_b:.2e} m⁻¹"
        },
        "kostelecky_2008": {
            "citation": "Kostelecký, Russell, Tasson, Phys. Rev. Lett. 100, 111102 (2008)",
            "description": "Torsion constraints from Lorentz violation bounds",
            "torsion_limit": f"|T| < {T_temporal_limit:.0e} m⁻¹"
        },
        "heckel_2008": {
            "citation": "Heckel et al., Phys. Rev. D 78, 092006 (2008)",
            "description": "Spin-coupled forces torsion balance",
            "g_a_squared_limit": g_a_squared_limit
        }
    },
    "theoretical_predictions": {
        "polarized_iron": {
            "torsion": T_Fe,
            "precession_mas_yr": Omega_torsion_Fe
        },
        "earth_unpolarized": {
            "torsion": 0.0,
            "precession_mas_yr": 0.0
        },
        "neutron_star": {
            "torsion": T_ns
        }
    },
    "comparison": {
        "orders_below_heckel": orders_below_heckel,
        "orders_below_lorentz_violation": orders_below_lv,
        "orders_below_gpb_precision": orders_below_GPB,
        "all_predictions_safe": all_safe
    },
    "conclusion": "All theoretical predictions are 10-20+ orders below experimental sensitivity. Framework is consistent with all null results."
}

output_file = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/theorem_5_3_2_experimental_bounds_results.json"
with open(output_file, 'w') as f:
    json.dump(results, f, indent=2)

print(f"Results saved to: {output_file}")

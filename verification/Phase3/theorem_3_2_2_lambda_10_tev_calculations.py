#!/usr/bin/env python3
"""
Theorem 3.2.2: Complete calculations at Λ = 10 TeV

This script calculates ALL numerical values that need to be updated
when changing from Λ = 5 TeV to Λ = 10 TeV in the document.

Key insight: Most deviations scale as (v/Λ)² = (246/Λ)²
So when Λ doubles (5→10 TeV), deviations reduce by factor of 4.

Date: 2025-12-14
"""

import numpy as np

print("=" * 70)
print("THEOREM 3.2.2: NUMERICAL VALUES AT Λ = 10 TeV")
print("=" * 70)

# =============================================================================
# PHYSICAL CONSTANTS
# =============================================================================
v_EW = 246  # GeV, electroweak VEV
m_H = 125.11  # GeV, Higgs mass (PDG 2024)
m_W_SM = 80.357  # GeV, SM tree-level W mass
m_Z = 91.1876  # GeV, Z mass
alpha_em = 1/137.036  # Fine structure constant
sin2_theta_W = 0.23122  # Weinberg angle squared
cos2_theta_W = 1 - sin2_theta_W

# Coupling constants
g_weak = 0.652  # SU(2) coupling
g_prime = 0.357  # U(1)_Y coupling
g_chi = 1.0  # Chiral coupling (order 1)

# Higgs quartic
lambda_SM = m_H**2 / (2 * v_EW**2)  # ~ 0.129

# Cutoff scales to compare
Lambda_old = 5000  # GeV (old examples)
Lambda_new = 10000  # GeV (new examples)

print("\n" + "=" * 70)
print("SECTION 3.2: PERTURBATIVITY CHECK")
print("=" * 70)

# From the document (Section 3.2):
# y_t^eff = sqrt(2) * g_chi * omega * eta_f / Lambda
# For top quark: m_t = (g_chi * omega / Lambda) * v_chi * eta_t
# With m_t = 173 GeV, v_chi = v = 246 GeV, eta_t ~ 1:
# g_chi * omega / Lambda = m_t / (v_chi * eta_t) = 173/246 ≈ 0.70

m_t = 173  # GeV
eta_t = 1.0
g_chi_omega_over_Lambda = m_t / (v_EW * eta_t)
y_t_eff = np.sqrt(2) * g_chi_omega_over_Lambda

print(f"\nPerturbativity check:")
print(f"  g_χ·ω/Λ = m_t/(v_χ·η_t) = {m_t}/{v_EW}×{eta_t} = {g_chi_omega_over_Lambda:.2f}")
print(f"  y_t^eff = √2 × {g_chi_omega_over_Lambda:.2f} = {y_t_eff:.2f}")
print(f"  Perturbative bound: y_t^eff << 4π ≈ {4*np.pi:.1f}")
print(f"  Status: {'✓ SATISFIED' if y_t_eff < 4*np.pi else '✗ VIOLATED'}")

print("\n" + "=" * 70)
print("SECTION 4: WILSON COEFFICIENTS (independent of Λ)")
print("=" * 70)

# Wilson coefficients are dimensionless and independent of Λ
c_H = lambda_SM  # ~ 0.129
c_box = g_chi**2  # ~ 1.0
c_HW = g_weak**2 * g_chi**2  # ~ 0.43
c_HB = g_prime**2 * g_chi**2  # ~ 0.13
c_T = sin2_theta_W * g_chi**2  # ~ 0.23

print(f"\nWilson coefficients (dimensionless, Λ-independent):")
print(f"  c_H = λ_χ = {c_H:.4f}")
print(f"  c_□ = g_χ² = {c_box:.4f}")
print(f"  c_HW = g²·g_χ² = {c_HW:.4f}")
print(f"  c_HB = g'²·g_χ² = {c_HB:.4f}")
print(f"  c_T = sin²θ_W·g_χ² = {c_T:.4f}")

# Combined coefficient for Z
c_HZ = c_HW * cos2_theta_W + c_HB * sin2_theta_W
print(f"  c_HZ = c_HW·cos²θ + c_HB·sin²θ = {c_HZ:.4f}")

print("\n" + "=" * 70)
print("SECTION 5.1: W BOSON MASS CORRECTION")
print("=" * 70)

def calc_w_mass_correction(Lambda):
    """Calculate W mass correction at given Lambda (in GeV)."""
    # δm_W / m_W = c_HW * v² / (2 * Λ²)
    delta_mW_over_mW = c_HW * v_EW**2 / (2 * Lambda**2)
    delta_mW_GeV = delta_mW_over_mW * m_W_SM
    delta_mW_MeV = delta_mW_GeV * 1000
    m_W_CG = m_W_SM + delta_mW_GeV
    return delta_mW_over_mW, delta_mW_MeV, m_W_CG

print(f"\nW mass correction formula: δm_W/m_W = c_HW·v²/(2Λ²)")
print(f"\nComparison at different Λ:")

for Lambda, label in [(5000, "OLD"), (10000, "NEW")]:
    ratio, delta_MeV, m_W = calc_w_mass_correction(Lambda)
    print(f"\n  Λ = {Lambda/1000:.0f} TeV ({label}):")
    print(f"    δm_W/m_W = {c_HW:.3f} × ({v_EW})² / (2 × ({Lambda})²)")
    print(f"            = {c_HW:.3f} × {v_EW**2} / {2 * Lambda**2}")
    print(f"            = {ratio:.6f} = {ratio*100:.4f}%")
    print(f"    δm_W = {delta_MeV:.2f} MeV")
    print(f"    m_W(CG) = {m_W_SM:.3f} + {delta_MeV/1000:.4f} = {m_W:.4f} GeV")

# Calculate scaling
scaling = (Lambda_old / Lambda_new)**2
print(f"\n  Scaling factor: (5/10)² = {scaling}")
print(f"  Verification: {calc_w_mass_correction(5000)[1]:.2f} × {scaling} = {calc_w_mass_correction(5000)[1] * scaling:.2f} MeV")
print(f"  Direct calc at 10 TeV: {calc_w_mass_correction(10000)[1]:.2f} MeV ✓")

print("\n" + "=" * 70)
print("SECTION 5.2: Z BOSON MASS CORRECTION")
print("=" * 70)

def calc_z_mass_correction(Lambda):
    """Calculate Z mass correction at given Lambda (in GeV)."""
    # δm_Z / m_Z = c_HZ * v² / (2 * Λ²)
    delta_mZ_over_mZ = c_HZ * v_EW**2 / (2 * Lambda**2)
    delta_mZ_GeV = delta_mZ_over_mZ * m_Z
    delta_mZ_MeV = delta_mZ_GeV * 1000
    return delta_mZ_over_mZ, delta_mZ_MeV

print(f"\nZ mass correction formula: δm_Z/m_Z = c_HZ·v²/(2Λ²)")
print(f"  c_HZ = {c_HZ:.4f}")

for Lambda, label in [(5000, "OLD"), (10000, "NEW")]:
    ratio, delta_MeV = calc_z_mass_correction(Lambda)
    print(f"\n  Λ = {Lambda/1000:.0f} TeV ({label}):")
    print(f"    δm_Z ≈ {delta_MeV:.1f} MeV")

print("\n" + "=" * 70)
print("SECTION 5.3: RHO PARAMETER")
print("=" * 70)

def calc_rho_correction(Lambda):
    """Calculate rho parameter correction."""
    # δρ = c_T * v² / Λ²
    delta_rho = c_T * v_EW**2 / Lambda**2
    return delta_rho

print(f"\nρ parameter correction: δρ = c_T·v²/Λ²")

for Lambda, label in [(5000, "OLD"), (10000, "NEW")]:
    delta_rho = calc_rho_correction(Lambda)
    print(f"\n  Λ = {Lambda/1000:.0f} TeV ({label}):")
    print(f"    δρ = {c_T:.3f} × ({v_EW})² / ({Lambda})²")
    print(f"       = {delta_rho:.2e}")

print("\n" + "=" * 70)
print("SECTION 5.4: OBLIQUE PARAMETERS S, T, U")
print("=" * 70)

def calc_oblique_parameters(Lambda):
    """Calculate S, T, U oblique parameters."""
    # S = (4*sin²θ_W/α) * (c_HW - c_HB)/Λ² * v²
    S = (4 * sin2_theta_W / alpha_em) * (c_HW - c_HB) / Lambda**2 * v_EW**2

    # T = (1/α) * c_T/Λ² * v²
    T = (1 / alpha_em) * c_T / Lambda**2 * v_EW**2

    # U ≈ 0 in CG
    U = 0.0

    return S, T, U

print(f"\nOblique parameter formulas:")
print(f"  S = (4sin²θ_W/α) × (c_HW - c_HB)/Λ² × v²")
print(f"  T = (1/α) × c_T/Λ² × v²")
print(f"  U ≈ 0")

print(f"\nNumerical prefactors:")
print(f"  4sin²θ_W/α = 4 × {sin2_theta_W:.4f} / {alpha_em:.6f} = {4*sin2_theta_W/alpha_em:.2f}")
print(f"  1/α = {1/alpha_em:.2f}")
print(f"  c_HW - c_HB = {c_HW:.4f} - {c_HB:.4f} = {c_HW - c_HB:.4f}")

for Lambda, label in [(5000, "OLD"), (10000, "NEW")]:
    S, T, U = calc_oblique_parameters(Lambda)
    print(f"\n  Λ = {Lambda/1000:.0f} TeV ({label}):")
    print(f"    S = {S:.4f}")
    print(f"    T = {T:.4f}")
    print(f"    U = {U:.4f}")

# PDG bounds
S_PDG, S_err = -0.01, 0.10
T_PDG, T_err = 0.03, 0.12

S_10, T_10, _ = calc_oblique_parameters(10000)
print(f"\n  Tension at Λ = 10 TeV:")
print(f"    S: |{S_10:.4f} - ({S_PDG})| / {S_err} = {abs(S_10 - S_PDG)/S_err:.2f}σ")
print(f"    T: |{T_10:.4f} - {T_PDG}| / {T_err} = {abs(T_10 - T_PDG)/T_err:.2f}σ")

print("\n" + "=" * 70)
print("SECTION 6: HIGGS TRILINEAR COUPLING κ_λ")
print("=" * 70)

def calc_kappa_lambda(Lambda):
    """Calculate Higgs trilinear modification."""
    # κ_λ = 1 + 6*c_H*v⁴/(Λ²*m_H²)
    delta_kappa = 6 * c_H * v_EW**4 / (Lambda**2 * m_H**2)
    kappa = 1 + delta_kappa
    return kappa, delta_kappa

print(f"\nκ_λ formula: κ_λ = 1 + 6·c_H·v⁴/(Λ²·m_H²)")
print(f"  c_H = {c_H:.4f}")
print(f"  v⁴ = ({v_EW})⁴ = {v_EW**4:.2e} GeV⁴")
print(f"  m_H² = ({m_H})² = {m_H**2:.2f} GeV²")

for Lambda, label in [(5000, "OLD"), (10000, "NEW")]:
    kappa, delta = calc_kappa_lambda(Lambda)
    print(f"\n  Λ = {Lambda/1000:.0f} TeV ({label}):")
    print(f"    Numerator: 6 × {c_H:.4f} × {v_EW**4:.2e} = {6*c_H*v_EW**4:.2e}")
    print(f"    Denominator: ({Lambda})² × {m_H**2:.2f} = {Lambda**2 * m_H**2:.2e}")
    print(f"    δκ_λ = {delta:.5f} = {delta*100:.3f}%")
    print(f"    κ_λ = {kappa:.5f}")

print("\n" + "=" * 70)
print("SECTION 8: FORM FACTOR EFFECTS")
print("=" * 70)

def calc_form_factor(E, Lambda, n=1):
    """Calculate form factor F(E²/Λ²)."""
    x = E**2 / Lambda**2
    F = 1 / (1 + x)**n
    return F, x

print(f"\nForm factor: F(q²) = 1/(1 + q²/Λ²)^n with n ~ 1")

energies = [500, 1000]  # GeV

for Lambda, label in [(5000, "OLD"), (10000, "NEW")]:
    print(f"\n  Λ = {Lambda/1000:.0f} TeV ({label}):")
    for E in energies:
        F, x = calc_form_factor(E, Lambda)
        print(f"    E = {E} GeV: x = ({E})²/({Lambda})² = {x:.4f}, F = {F:.4f}")

print("\n" + "=" * 70)
print("SUMMARY: VALUES TO UPDATE IN DOCUMENT")
print("=" * 70)

print(f"""
SECTION 5.1 (W mass) - Lines ~320-335:
  OLD (Λ = 5 TeV):
    δm_W/m_W ≈ 5 × 10⁻⁴
    δm_W ≈ 40 MeV
    m_W(CG) = 80.357 + 0.040 = 80.397 GeV

  NEW (Λ = 10 TeV):
    δm_W/m_W ≈ 1.3 × 10⁻⁴ = 0.013%
    δm_W ≈ 10 MeV
    m_W(CG) = 80.357 + 0.010 = 80.367 GeV

SECTION 5.2 (Z mass) - Lines ~346-348:
  OLD: δm_Z ≈ 37 MeV
  NEW: δm_Z ≈ 9 MeV

SECTION 5.3 (ρ parameter) - Lines ~366-368:
  OLD: δρ ≈ 5.5 × 10⁻⁴
  NEW: δρ ≈ 1.4 × 10⁻⁴

SECTION 5.4 (S, T parameters) - Lines ~380-398:
  OLD (Λ = 5 TeV):
    S ≈ 0.092 (1.0σ)
    T ≈ 0.076 (0.4σ)

  NEW (Λ = 10 TeV):
    S ≈ 0.023 (0.3σ)
    T ≈ 0.019 (0.1σ)

SECTION 6.2 (κ_λ) - Lines ~423-438:
  OLD (Λ = 5 TeV):
    κ_λ ≈ 1.007 (0.7% deviation)

  NEW (Λ = 10 TeV):
    κ_λ ≈ 1.002 (0.2% deviation)

SECTION 6.4 (Di-Higgs) - Lines ~470-475:
  OLD: σ(HH)/σ_SM ≈ 0.984 (for κ_λ = 1.01)
  NEW: σ(HH)/σ_SM ≈ 0.997 (for κ_λ = 1.002)

SECTION 8.2-8.4 (Form factors) - Lines ~619-654:
  Form factor values change with Λ:
  OLD (Λ = 5 TeV, E = 500 GeV): F ≈ 0.99
  NEW (Λ = 10 TeV, E = 500 GeV): F ≈ 0.9975

  OLD (Λ = 5 TeV, E = 1 TeV): F ≈ 0.96
  NEW (Λ = 10 TeV, E = 1 TeV): F ≈ 0.99

GENERAL SCALING:
  All deviations scale as (v/Λ)²
  Going from 5 TeV → 10 TeV reduces deviations by factor of 4
""")

# Save key values for reference
results = {
    "Lambda_TeV": 10,
    "Wilson_coefficients": {
        "c_H": round(c_H, 4),
        "c_box": round(c_box, 4),
        "c_HW": round(c_HW, 4),
        "c_HB": round(c_HB, 4),
        "c_T": round(c_T, 4),
        "c_HZ": round(c_HZ, 4)
    },
    "W_mass": {
        "delta_mW_MeV": round(calc_w_mass_correction(10000)[1], 1),
        "mW_CG_GeV": round(calc_w_mass_correction(10000)[2], 4)
    },
    "Z_mass": {
        "delta_mZ_MeV": round(calc_z_mass_correction(10000)[1], 1)
    },
    "rho_parameter": {
        "delta_rho": round(calc_rho_correction(10000), 6)
    },
    "oblique_parameters": {
        "S": round(calc_oblique_parameters(10000)[0], 4),
        "T": round(calc_oblique_parameters(10000)[1], 4),
        "U": 0.0
    },
    "kappa_lambda": {
        "value": round(calc_kappa_lambda(10000)[0], 5),
        "deviation_percent": round(calc_kappa_lambda(10000)[1] * 100, 3)
    },
    "form_factors_10TeV": {
        "E_500GeV": round(calc_form_factor(500, 10000)[0], 4),
        "E_1000GeV": round(calc_form_factor(1000, 10000)[0], 4)
    }
}

import json
from pathlib import Path

output_path = Path(__file__).parent / "theorem_3_2_2_lambda_10_tev_values.json"
with open(output_path, 'w') as f:
    json.dump(results, f, indent=2)

print(f"\nResults saved to: {output_path}")

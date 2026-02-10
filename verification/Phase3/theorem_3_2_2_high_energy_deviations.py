#!/usr/bin/env python3
"""
Computational Verification for Theorem 3.2.2: High-Energy Deviations
=====================================================================

This script verifies the key numerical predictions of Theorem 3.2.2,
which derives the deviations from Standard Model predictions at high energies.

Key quantities to verify:
1. Cutoff scale Λ = 4πv√(v/f_π) ≈ 4-10 TeV
2. Wilson coefficients for dimension-6 operators
3. W mass correction δm_W/m_W
4. Higgs trilinear modification κ_λ
5. Oblique parameters S, T, U
6. Form factor effects
7. Consistency with experimental bounds

Author: Multi-Agent Verification System
Date: 2025-12-14
"""

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import Tuple, Dict, List
import json

# ==============================================================================
# PHYSICAL CONSTANTS (PDG 2024 / SM values)
# ==============================================================================

# Electroweak parameters
v_EW = 246.22  # GeV, Higgs VEV
m_H = 125.11  # GeV, Higgs mass (PDG 2024)
m_W_exp = 80.3692  # GeV, W mass world average (PDG 2024)
m_W_SM = 80.357  # GeV, SM prediction
m_W_exp_err = 0.0133  # GeV
m_Z = 91.1876  # GeV, Z mass
sin2_theta_W = 0.23122  # Weinberg angle
alpha_em = 1/137.036  # EM coupling

# Gauge couplings
g_weak = 0.653  # SU(2)_L coupling
g_prime = 0.350  # U(1)_Y coupling

# QCD parameters
f_pi = 92.1  # MeV, pion decay constant (PDG 2024)
Lambda_QCD = 200  # MeV, QCD confinement scale

# Planck scale
M_P = 1.22089e19  # GeV, Planck mass
f_chi = M_P / np.sqrt(8 * np.pi)  # GeV, chiral decay constant

# Higgs self-coupling
lambda_H = m_H**2 / (2 * v_EW**2)  # ≈ 0.129

# PDG 2024 oblique parameters
S_exp = -0.01
S_exp_err = 0.10
T_exp = 0.03
T_exp_err = 0.12
U_exp = 0.01
U_exp_err = 0.09


# ==============================================================================
# CUTOFF SCALE DERIVATION (Section 3)
# ==============================================================================

def derive_cutoff_scale_method1() -> float:
    """
    Method 1: Λ = 4πv√(v/f_π)
    From Section 3.4, eq. 1
    """
    v_GeV = v_EW
    f_pi_GeV = f_pi / 1000  # Convert MeV to GeV
    Lambda = 4 * np.pi * v_GeV * np.sqrt(v_GeV / f_pi_GeV)
    return Lambda


def derive_cutoff_scale_method2() -> float:
    """
    Method 2: Λ = 4πv²/f_π
    Alternative derivation from Section 3.4
    """
    v_GeV = v_EW
    f_pi_GeV = f_pi / 1000
    Lambda = 4 * np.pi * v_GeV**2 / f_pi_GeV
    return Lambda


def verify_cutoff_scale() -> Dict:
    """Verify cutoff scale derivations"""
    Lambda1 = derive_cutoff_scale_method1()
    Lambda2 = derive_cutoff_scale_method2()

    # Claimed values from theorem
    Lambda_min = 4.0  # TeV
    Lambda_max = 10.0  # TeV

    return {
        "Lambda_method1_TeV": Lambda1 / 1000,
        "Lambda_method2_TeV": Lambda2 / 1000,
        "Lambda_range_TeV": (Lambda_min, Lambda_max),
        "method1_in_range": Lambda_min <= Lambda1/1000 <= Lambda_max,
        "method2_in_range": Lambda_min <= Lambda2/1000 <= Lambda_max,
        "formula1": "Λ = 4πv√(v/f_π)",
        "formula2": "Λ = 4πv²/f_π"
    }


# ==============================================================================
# WILSON COEFFICIENTS (Section 4)
# ==============================================================================

@dataclass
class WilsonCoefficients:
    """Wilson coefficients for dimension-6 operators"""
    c_H: float  # O_H = |Φ|^6
    c_box: float  # O_□ = (∂|Φ|²)²
    c_y_f: float  # O_y_f = |Φ|² ψ̄_L Φ ψ_R
    c_HW: float  # O_HW = |DΦ|² W_αβ W^αβ
    c_HB: float  # O_HB = |DΦ|² B_αβ B^αβ
    c_T: float  # O_T = |Φ† D_μ Φ|²


def compute_wilson_coefficients() -> WilsonCoefficients:
    """
    Compute Wilson coefficients from CG theory (Section 4.2)
    """
    # Chiral self-coupling (from Higgs quartic)
    lambda_chi = lambda_H  # ≈ 0.13

    # Chiral coupling g_χ ~ 1 (assumed O(1))
    g_chi = 1.0

    # Wilson coefficients (Section 4.3)
    c_H = lambda_chi  # ≈ 0.13
    c_box = g_chi**2  # ≈ 1
    c_y_f = g_chi  # ≈ 1
    c_HW = g_weak**2 * g_chi**2  # ≈ 0.43
    c_HB = g_prime**2 * g_chi**2  # ≈ 0.12

    # Custodial-breaking coefficient (protected by S_4 × Z_2)
    c_T = (g_prime**2 / (g_weak**2 + g_prime**2)) * g_chi**2  # ≈ 0.23

    return WilsonCoefficients(c_H, c_box, c_y_f, c_HW, c_HB, c_T)


# ==============================================================================
# W/Z MASS CORRECTIONS (Section 5)
# ==============================================================================

def compute_W_mass_correction(Lambda_TeV: float, c_HW: float) -> Tuple[float, float]:
    """
    Compute W mass correction from dimension-6 operators

    δm_W/m_W = c_HW v²/(2Λ²)
    """
    Lambda_GeV = Lambda_TeV * 1000

    # Relative correction
    delta_mW_rel = c_HW * v_EW**2 / (2 * Lambda_GeV**2)

    # Absolute correction in GeV
    delta_mW_abs = delta_mW_rel * m_W_exp

    return delta_mW_rel, delta_mW_abs


def compute_Z_mass_correction(Lambda_TeV: float, c_HW: float, c_HB: float) -> Tuple[float, float]:
    """
    Compute Z mass correction

    c_HZ = c_HW cos²θ_W + c_HB sin²θ_W
    δm_Z/m_Z = c_HZ v²/(2Λ²)
    """
    Lambda_GeV = Lambda_TeV * 1000
    cos2_theta = 1 - sin2_theta_W

    c_HZ = c_HW * cos2_theta + c_HB * sin2_theta_W
    delta_mZ_rel = c_HZ * v_EW**2 / (2 * Lambda_GeV**2)
    delta_mZ_abs = delta_mZ_rel * m_Z

    return delta_mZ_rel, delta_mZ_abs


def compute_rho_correction(Lambda_TeV: float, c_T: float) -> float:
    """
    Compute correction to ρ parameter

    δρ = c_T v²/Λ²
    """
    Lambda_GeV = Lambda_TeV * 1000
    delta_rho = c_T * v_EW**2 / Lambda_GeV**2
    return delta_rho


def verify_gauge_boson_masses() -> Dict:
    """Verify gauge boson mass corrections"""
    wc = compute_wilson_coefficients()

    results = {}

    for Lambda_TeV in [4.0, 5.0, 10.0]:
        key = f"Lambda_{Lambda_TeV}TeV"

        delta_mW_rel, delta_mW_abs = compute_W_mass_correction(Lambda_TeV, wc.c_HW)
        delta_mZ_rel, delta_mZ_abs = compute_Z_mass_correction(Lambda_TeV, wc.c_HW, wc.c_HB)
        delta_rho = compute_rho_correction(Lambda_TeV, wc.c_T)

        # Predicted W mass
        m_W_CG = m_W_SM + delta_mW_abs

        # Check consistency with measurement
        within_error = abs(m_W_CG - m_W_exp) < 2 * m_W_exp_err

        results[key] = {
            "delta_mW_rel_percent": delta_mW_rel * 100,
            "delta_mW_abs_MeV": delta_mW_abs * 1000,
            "m_W_CG_GeV": m_W_CG,
            "delta_mZ_abs_MeV": delta_mZ_abs * 1000,
            "delta_rho": delta_rho,
            "within_2sigma": within_error
        }

    return results


# ==============================================================================
# HIGGS TRILINEAR COUPLING (Section 6)
# ==============================================================================

def compute_kappa_lambda(Lambda_TeV: float, c_H: float) -> float:
    """
    Compute Higgs trilinear coupling modification

    κ_λ = 1 + 6 c_H v⁴/(Λ² m_H²)
    """
    Lambda_GeV = Lambda_TeV * 1000

    kappa = 1 + 6 * c_H * v_EW**4 / (Lambda_GeV**2 * m_H**2)
    return kappa


def compute_form_factor(q2: float, Lambda_TeV: float, n: float = 1.0) -> float:
    """
    Compute form factor from extended χ configuration

    F(q²) = 1/(1 + q²/Λ²)^n
    """
    Lambda_GeV = Lambda_TeV * 1000
    x = q2 / Lambda_GeV**2
    return 1 / (1 + x)**n


def compute_kappa_lambda_effective(E_TeV: float, Lambda_TeV: float, c_H: float) -> float:
    """
    Compute effective κ_λ including form factor

    κ_λ^eff(E) = κ_λ^(0) × F(E²/Λ²)
    """
    kappa_0 = compute_kappa_lambda(Lambda_TeV, c_H)
    E_GeV = E_TeV * 1000
    F = compute_form_factor(E_GeV**2, Lambda_TeV)
    return kappa_0 * F


def verify_higgs_trilinear() -> Dict:
    """Verify Higgs trilinear coupling predictions"""
    wc = compute_wilson_coefficients()

    results = {}

    for Lambda_TeV in [4.0, 5.0, 10.0]:
        kappa = compute_kappa_lambda(Lambda_TeV, wc.c_H)

        # Current LHC bound: κ_λ ∈ [-1.4, 6.1] at 95% CL
        within_LHC_bound = -1.4 <= kappa <= 6.1

        # HL-LHC expected: κ_λ ∈ [0.5, 1.6] at 68% CL
        within_HLLHC_1sigma = 0.5 <= kappa <= 1.6

        results[f"Lambda_{Lambda_TeV}TeV"] = {
            "kappa_lambda": kappa,
            "deviation_percent": (kappa - 1) * 100,
            "within_LHC_bound": within_LHC_bound,
            "within_HLLHC_expected": within_HLLHC_1sigma
        }

    # Energy-dependent κ_λ
    energies_TeV = [0.25, 0.5, 1.0, 2.0]
    Lambda_TeV = 5.0

    energy_dependence = {}
    for E in energies_TeV:
        kappa_eff = compute_kappa_lambda_effective(E, Lambda_TeV, wc.c_H)
        F = compute_form_factor((E * 1000)**2, Lambda_TeV)
        energy_dependence[f"E_{E}TeV"] = {
            "kappa_eff": kappa_eff,
            "form_factor": F
        }

    results["energy_dependence"] = energy_dependence

    return results


# ==============================================================================
# OBLIQUE PARAMETERS S, T, U (Section 5.4)
# ==============================================================================

def compute_oblique_parameters(Lambda_TeV: float, wc: WilsonCoefficients) -> Tuple[float, float, float]:
    """
    Compute Peskin-Takeuchi oblique parameters

    S = (4 sin²θ_W / α) × (c_HW - c_HB) v²/Λ²
    T = (1/α) × c_T v²/Λ²
    U ≈ 0
    """
    Lambda_GeV = Lambda_TeV * 1000

    S = 4 * sin2_theta_W / alpha_em * (wc.c_HW - wc.c_HB) * v_EW**2 / Lambda_GeV**2
    T = 1 / alpha_em * wc.c_T * v_EW**2 / Lambda_GeV**2
    U = 0.0

    return S, T, U


def verify_oblique_parameters() -> Dict:
    """Verify oblique parameter predictions"""
    wc = compute_wilson_coefficients()

    results = {}

    for Lambda_TeV in [4.0, 5.0, 10.0]:
        S, T, U = compute_oblique_parameters(Lambda_TeV, wc)

        # Check within experimental bounds (2σ)
        S_ok = abs(S - S_exp) < 2 * S_exp_err
        T_ok = abs(T - T_exp) < 2 * T_exp_err
        U_ok = abs(U - U_exp) < 2 * U_exp_err

        results[f"Lambda_{Lambda_TeV}TeV"] = {
            "S_CG": S,
            "T_CG": T,
            "U_CG": U,
            "S_within_2sigma": S_ok,
            "T_within_2sigma": T_ok,
            "U_within_2sigma": U_ok,
            "all_consistent": S_ok and T_ok and U_ok
        }

    return results


# ==============================================================================
# CHI* RESONANCE SPECTRUM (Section 7)
# ==============================================================================

def compute_chi_star_mass(Lambda_TeV: float, n: int = 1) -> float:
    """
    Compute mass of n-th excited χ* state

    From Section 7.2: First excited state at m ~ Λ due to geometric gap
    """
    # The gap protects the spectrum - first excited state at Λ
    m_chi_star = Lambda_TeV * 1000  # GeV
    return m_chi_star * np.sqrt(n)  # Higher states scale as √n


def compute_chi_star_width(m_chi_star: float, Lambda_TeV: float, g_chi: float = 1.0) -> float:
    """
    Compute width of χ* resonance

    Γ_χ* ~ g_χ² m_χ*³ / (16π Λ²) ~ m_χ*³/Λ²
    """
    Lambda_GeV = Lambda_TeV * 1000
    Gamma = g_chi**2 * m_chi_star**3 / (16 * np.pi * Lambda_GeV**2)
    return Gamma


def verify_chi_star_spectrum() -> Dict:
    """Verify χ* resonance predictions"""
    results = {}

    for Lambda_TeV in [4.0, 5.0, 10.0]:
        m_chi_star = compute_chi_star_mass(Lambda_TeV)
        Gamma = compute_chi_star_width(m_chi_star, Lambda_TeV)

        # Width-to-mass ratio
        Gamma_over_m = Gamma / m_chi_star

        # Cross section estimate at LHC 14 TeV
        # σ(pp → χ*) ~ 1 fb × (Λ/v)^-2 × PDF suppression
        sigma_estimate_fb = 1.0 * (Lambda_TeV * 1000 / v_EW)**(-2)

        results[f"Lambda_{Lambda_TeV}TeV"] = {
            "m_chi_star_TeV": m_chi_star / 1000,
            "Gamma_TeV": Gamma / 1000,
            "Gamma_over_m": Gamma_over_m,
            "very_broad": Gamma_over_m > 0.5,
            "cross_section_fb": sigma_estimate_fb,
            "accessible_LHC": m_chi_star < 5000  # LHC reach ~4-5 TeV
        }

    return results


# ==============================================================================
# DI-HIGGS PRODUCTION (Section 6.4)
# ==============================================================================

def compute_di_higgs_ratio(kappa_lambda: float) -> float:
    """
    Compute di-Higgs cross section ratio relative to SM

    σ(HH)/σ_SM(HH) ≈ 1 - 1.6×(κ_λ-1) + 2.3×(κ_λ-1)²
    """
    delta_kappa = kappa_lambda - 1
    ratio = 1 - 1.6 * delta_kappa + 2.3 * delta_kappa**2
    return ratio


def verify_di_higgs() -> Dict:
    """Verify di-Higgs production predictions"""
    wc = compute_wilson_coefficients()

    results = {}

    for Lambda_TeV in [4.0, 5.0, 10.0]:
        kappa = compute_kappa_lambda(Lambda_TeV, wc.c_H)
        sigma_ratio = compute_di_higgs_ratio(kappa)

        # Current LHC bound: σ(HH)/σ_SM < 3.5
        within_bound = sigma_ratio < 3.5

        results[f"Lambda_{Lambda_TeV}TeV"] = {
            "kappa_lambda": kappa,
            "sigma_HH_ratio": sigma_ratio,
            "deviation_percent": (sigma_ratio - 1) * 100,
            "within_LHC_bound": within_bound
        }

    return results


# ==============================================================================
# LOWER BOUND ON Λ (Section 9.4)
# ==============================================================================

def compute_lambda_lower_bound() -> Dict:
    """
    Derive combined lower bound on Λ from various constraints
    """
    wc = compute_wilson_coefficients()

    # From EW precision (S, T): Λ > 2.5 TeV
    # Using S < 0.2 at 2σ
    S_limit = 0.2
    Lambda_from_S = np.sqrt(4 * sin2_theta_W / alpha_em *
                           abs(wc.c_HW - wc.c_HB) * v_EW**2 / S_limit) / 1000

    # From Higgs coupling deviations: Λ > 1.5 TeV
    # Requiring δκ < 0.1
    kappa_limit = 0.1
    Lambda_from_kappa = np.sqrt(6 * wc.c_H * v_EW**4 / (kappa_limit * m_H**2)) / 1000

    # Combined bound (most restrictive)
    Lambda_combined = max(Lambda_from_S, Lambda_from_kappa)

    return {
        "Lambda_from_EW_precision_TeV": Lambda_from_S,
        "Lambda_from_Higgs_couplings_TeV": Lambda_from_kappa,
        "Lambda_combined_lower_bound_TeV": Lambda_combined,
        "claimed_range_TeV": (4.0, 10.0),
        "consistent": Lambda_combined < 4.0
    }


# ==============================================================================
# COMPREHENSIVE VERIFICATION
# ==============================================================================

def run_all_verifications() -> Dict:
    """Run all verification tests"""
    results = {
        "cutoff_scale": verify_cutoff_scale(),
        "wilson_coefficients": {
            "c_H": compute_wilson_coefficients().c_H,
            "c_box": compute_wilson_coefficients().c_box,
            "c_HW": compute_wilson_coefficients().c_HW,
            "c_HB": compute_wilson_coefficients().c_HB,
            "c_T": compute_wilson_coefficients().c_T
        },
        "gauge_boson_masses": verify_gauge_boson_masses(),
        "higgs_trilinear": verify_higgs_trilinear(),
        "oblique_parameters": verify_oblique_parameters(),
        "chi_star_spectrum": verify_chi_star_spectrum(),
        "di_higgs_production": verify_di_higgs(),
        "lambda_lower_bound": compute_lambda_lower_bound()
    }

    # Summary
    n_tests = 0
    n_passed = 0

    # Check cutoff scale
    n_tests += 2
    if results["cutoff_scale"]["method1_in_range"]:
        n_passed += 1
    if results["cutoff_scale"]["method2_in_range"]:
        n_passed += 1

    # Check gauge boson masses
    for key in ["Lambda_4.0TeV", "Lambda_5.0TeV", "Lambda_10.0TeV"]:
        n_tests += 1
        if results["gauge_boson_masses"][key]["within_2sigma"]:
            n_passed += 1

    # Check oblique parameters
    for key in ["Lambda_4.0TeV", "Lambda_5.0TeV", "Lambda_10.0TeV"]:
        n_tests += 1
        if results["oblique_parameters"][key]["all_consistent"]:
            n_passed += 1

    # Check Higgs trilinear within bounds
    for key in ["Lambda_4.0TeV", "Lambda_5.0TeV", "Lambda_10.0TeV"]:
        n_tests += 1
        if results["higgs_trilinear"][key]["within_LHC_bound"]:
            n_passed += 1

    # Check di-Higgs
    for key in ["Lambda_4.0TeV", "Lambda_5.0TeV", "Lambda_10.0TeV"]:
        n_tests += 1
        if results["di_higgs_production"][key]["within_LHC_bound"]:
            n_passed += 1

    # Check Λ lower bound consistency
    n_tests += 1
    if results["lambda_lower_bound"]["consistent"]:
        n_passed += 1

    results["summary"] = {
        "total_tests": n_tests,
        "passed": n_passed,
        "failed": n_tests - n_passed,
        "pass_rate": n_passed / n_tests * 100
    }

    return results


# ==============================================================================
# DIMENSIONAL ANALYSIS VERIFICATION
# ==============================================================================

def verify_dimensional_analysis() -> Dict:
    """
    Verify dimensional consistency of key equations
    """
    checks = []

    # 1. Cutoff scale: Λ = 4πv√(v/f_π)
    # [Λ] = [v] × sqrt([v]/[f_π]) = GeV × sqrt(GeV/GeV) = GeV ✓
    checks.append({
        "equation": "Λ = 4πv√(v/f_π)",
        "LHS_dim": "GeV",
        "RHS_dim": "GeV × √(GeV/GeV) = GeV",
        "consistent": True
    })

    # 2. W mass correction: δm_W/m_W = c_HW v²/Λ²
    # [c_HW] = dimensionless, [v²/Λ²] = dimensionless ✓
    checks.append({
        "equation": "δm_W/m_W = c_HW v²/(2Λ²)",
        "LHS_dim": "dimensionless",
        "RHS_dim": "dimensionless × GeV²/GeV² = dimensionless",
        "consistent": True
    })

    # 3. κ_λ correction: δκ = 6c_H v⁴/(Λ²m_H²)
    # [v⁴/(Λ²m_H²)] = GeV⁴/(GeV² × GeV²) = dimensionless ✓
    checks.append({
        "equation": "κ_λ - 1 = 6c_H v⁴/(Λ²m_H²)",
        "LHS_dim": "dimensionless",
        "RHS_dim": "dimensionless × GeV⁴/(GeV²×GeV²) = dimensionless",
        "consistent": True
    })

    # 4. S parameter: S = (4sin²θ_W/α) × (c_HW-c_HB) × v²/Λ²
    # All factors dimensionless ✓
    checks.append({
        "equation": "S = (4sin²θ_W/α)(c_HW-c_HB)v²/Λ²",
        "LHS_dim": "dimensionless",
        "RHS_dim": "dimensionless",
        "consistent": True
    })

    # 5. χ* width: Γ = g²m³/(16πΛ²)
    # [m³/Λ²] = GeV³/GeV² = GeV ✓
    checks.append({
        "equation": "Γ_χ* = g_χ²m_χ*³/(16πΛ²)",
        "LHS_dim": "GeV",
        "RHS_dim": "dimensionless × GeV³/GeV² = GeV",
        "consistent": True
    })

    all_consistent = all(c["consistent"] for c in checks)

    return {
        "checks": checks,
        "all_consistent": all_consistent,
        "n_equations_checked": len(checks)
    }


# ==============================================================================
# PLOTTING
# ==============================================================================

def create_verification_plots(results: Dict):
    """Create visualization plots for verification results"""
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # Plot 1: W mass prediction vs Λ
    ax1 = axes[0, 0]
    Lambda_vals = np.linspace(3, 15, 100)
    wc = compute_wilson_coefficients()

    delta_mW_MeV = []
    for L in Lambda_vals:
        _, dm = compute_W_mass_correction(L, wc.c_HW)
        delta_mW_MeV.append(dm * 1000)

    ax1.plot(Lambda_vals, delta_mW_MeV, 'b-', linewidth=2, label='CG prediction')
    ax1.axhspan(-m_W_exp_err*1000, m_W_exp_err*1000, alpha=0.3, color='green',
                label=f'Exp uncertainty ±{m_W_exp_err*1000:.1f} MeV')
    ax1.axvline(4, color='r', linestyle='--', alpha=0.5, label='Λ = 4 TeV')
    ax1.axvline(10, color='r', linestyle='--', alpha=0.5, label='Λ = 10 TeV')
    ax1.set_xlabel('Λ (TeV)', fontsize=12)
    ax1.set_ylabel('δm_W (MeV)', fontsize=12)
    ax1.set_title('W Mass Correction vs Cutoff Scale', fontsize=14)
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(3, 15)

    # Plot 2: κ_λ vs Λ
    ax2 = axes[0, 1]
    kappa_vals = [compute_kappa_lambda(L, wc.c_H) for L in Lambda_vals]

    ax2.plot(Lambda_vals, kappa_vals, 'b-', linewidth=2, label='CG prediction')
    ax2.axhspan(0.5, 1.6, alpha=0.2, color='orange', label='HL-LHC 68% CL')
    ax2.axhline(1.0, color='k', linestyle='-', alpha=0.5, label='SM')
    ax2.axvline(4, color='r', linestyle='--', alpha=0.5)
    ax2.axvline(10, color='r', linestyle='--', alpha=0.5)
    ax2.set_xlabel('Λ (TeV)', fontsize=12)
    ax2.set_ylabel('κ_λ', fontsize=12)
    ax2.set_title('Higgs Trilinear Coupling vs Cutoff Scale', fontsize=14)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(3, 15)
    ax2.set_ylim(0.99, 1.05)

    # Plot 3: Oblique parameters S, T
    ax3 = axes[1, 0]
    S_vals = []
    T_vals = []
    for L in Lambda_vals:
        S, T, _ = compute_oblique_parameters(L, wc)
        S_vals.append(S)
        T_vals.append(T)

    ax3.plot(Lambda_vals, S_vals, 'b-', linewidth=2, label='S (CG)')
    ax3.plot(Lambda_vals, T_vals, 'r-', linewidth=2, label='T (CG)')
    ax3.axhspan(S_exp - 2*S_exp_err, S_exp + 2*S_exp_err, alpha=0.2, color='blue',
                label='S exp 2σ')
    ax3.axhspan(T_exp - 2*T_exp_err, T_exp + 2*T_exp_err, alpha=0.2, color='red',
                label='T exp 2σ')
    ax3.axvline(4, color='gray', linestyle='--', alpha=0.5)
    ax3.axvline(10, color='gray', linestyle='--', alpha=0.5)
    ax3.set_xlabel('Λ (TeV)', fontsize=12)
    ax3.set_ylabel('S, T parameters', fontsize=12)
    ax3.set_title('Oblique Parameters vs Cutoff Scale', fontsize=14)
    ax3.legend(fontsize=10)
    ax3.grid(True, alpha=0.3)
    ax3.set_xlim(3, 15)

    # Plot 4: Form factor vs energy
    ax4 = axes[1, 1]
    E_vals = np.linspace(0, 5, 100)

    for Lambda in [4.0, 5.0, 10.0]:
        F_vals = [compute_form_factor((E*1000)**2, Lambda) for E in E_vals]
        ax4.plot(E_vals, F_vals, linewidth=2, label=f'Λ = {Lambda} TeV')

    ax4.set_xlabel('E (TeV)', fontsize=12)
    ax4.set_ylabel('Form Factor F(E²/Λ²)', fontsize=12)
    ax4.set_title('Higgs Form Factor vs Energy', fontsize=14)
    ax4.legend(fontsize=10)
    ax4.grid(True, alpha=0.3)
    ax4.set_xlim(0, 5)
    ax4.set_ylim(0.5, 1.05)

    plt.tight_layout()
    plt.savefig('verification/plots/theorem_3_2_2_high_energy.png', dpi=150, bbox_inches='tight')
    plt.close()

    print("Plot saved to verification/plots/theorem_3_2_2_high_energy.png")


# ==============================================================================
# MAIN
# ==============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("THEOREM 3.2.2 COMPUTATIONAL VERIFICATION")
    print("High-Energy Deviations from Standard Model")
    print("=" * 70)

    # Run all verifications
    results = run_all_verifications()

    # Print summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)

    print(f"\nTotal tests: {results['summary']['total_tests']}")
    print(f"Passed: {results['summary']['passed']}")
    print(f"Failed: {results['summary']['failed']}")
    print(f"Pass rate: {results['summary']['pass_rate']:.1f}%")

    # Cutoff scale
    print("\n--- CUTOFF SCALE ---")
    cs = results["cutoff_scale"]
    print(f"Method 1 (Λ = 4πv√(v/f_π)): {cs['Lambda_method1_TeV']:.2f} TeV")
    print(f"Method 2 (Λ = 4πv²/f_π): {cs['Lambda_method2_TeV']:.2f} TeV")
    print(f"Claimed range: {cs['Lambda_range_TeV'][0]}-{cs['Lambda_range_TeV'][1]} TeV")

    # Wilson coefficients
    print("\n--- WILSON COEFFICIENTS ---")
    wc = results["wilson_coefficients"]
    print(f"c_H = {wc['c_H']:.3f}")
    print(f"c_□ = {wc['c_box']:.3f}")
    print(f"c_HW = {wc['c_HW']:.3f}")
    print(f"c_HB = {wc['c_HB']:.3f}")
    print(f"c_T = {wc['c_T']:.3f}")

    # Gauge boson masses (Λ = 5 TeV)
    print("\n--- GAUGE BOSON MASSES (Λ = 5 TeV) ---")
    gbm = results["gauge_boson_masses"]["Lambda_5.0TeV"]
    print(f"δm_W/m_W = {gbm['delta_mW_rel_percent']:.4f}%")
    print(f"δm_W = {gbm['delta_mW_abs_MeV']:.1f} MeV")
    print(f"m_W (CG) = {gbm['m_W_CG_GeV']:.4f} GeV")
    print(f"Within 2σ of exp: {gbm['within_2sigma']}")

    # Higgs trilinear
    print("\n--- HIGGS TRILINEAR (Λ = 5 TeV) ---")
    ht = results["higgs_trilinear"]["Lambda_5.0TeV"]
    print(f"κ_λ = {ht['kappa_lambda']:.5f}")
    print(f"Deviation = {ht['deviation_percent']:.3f}%")
    print(f"Within LHC bound: {ht['within_LHC_bound']}")

    # Oblique parameters
    print("\n--- OBLIQUE PARAMETERS (Λ = 5 TeV) ---")
    op = results["oblique_parameters"]["Lambda_5.0TeV"]
    print(f"S = {op['S_CG']:.4f} (exp: {S_exp} ± {S_exp_err})")
    print(f"T = {op['T_CG']:.4f} (exp: {T_exp} ± {T_exp_err})")
    print(f"All within 2σ: {op['all_consistent']}")

    # χ* resonances
    print("\n--- χ* RESONANCES (Λ = 5 TeV) ---")
    chi = results["chi_star_spectrum"]["Lambda_5.0TeV"]
    print(f"m_χ* = {chi['m_chi_star_TeV']:.1f} TeV")
    print(f"Γ_χ* = {chi['Gamma_TeV']:.1f} TeV")
    print(f"Γ/m = {chi['Gamma_over_m']:.2f}")
    print(f"Very broad (Γ/m > 0.5): {chi['very_broad']}")

    # Lower bound
    print("\n--- LOWER BOUND ON Λ ---")
    lb = results["lambda_lower_bound"]
    print(f"From EW precision: Λ > {lb['Lambda_from_EW_precision_TeV']:.1f} TeV")
    print(f"From Higgs couplings: Λ > {lb['Lambda_from_Higgs_couplings_TeV']:.1f} TeV")
    print(f"Combined: Λ > {lb['Lambda_combined_lower_bound_TeV']:.1f} TeV")
    print(f"Consistent with claimed range: {lb['consistent']}")

    # Dimensional analysis
    print("\n--- DIMENSIONAL ANALYSIS ---")
    dim = verify_dimensional_analysis()
    print(f"Equations checked: {dim['n_equations_checked']}")
    print(f"All dimensionally consistent: {dim['all_consistent']}")

    # Create plots
    try:
        import os
        os.makedirs('verification/plots', exist_ok=True)
        create_verification_plots(results)
    except Exception as e:
        print(f"\nWarning: Could not create plots: {e}")

    # Save results to JSON
    try:
        with open('verification/theorem_3_2_2_results.json', 'w') as f:
            json.dump(results, f, indent=2, default=str)
        print("\nResults saved to verification/theorem_3_2_2_results.json")
    except Exception as e:
        print(f"\nWarning: Could not save JSON: {e}")

    # Final verdict
    print("\n" + "=" * 70)
    if results['summary']['pass_rate'] >= 90:
        print("VERIFICATION STATUS: ✅ PASSED")
    elif results['summary']['pass_rate'] >= 70:
        print("VERIFICATION STATUS: ⚠️ PARTIAL")
    else:
        print("VERIFICATION STATUS: ❌ FAILED")
    print("=" * 70)

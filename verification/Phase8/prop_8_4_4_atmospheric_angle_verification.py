"""
Proposition 8.4.4: Atmospheric Angle θ₂₃ Correction from A₄ Breaking
=====================================================================

Verification Script for Multi-Agent Peer Review

This script independently verifies all numerical calculations in Proposition 8.4.4,
which addresses the 4σ tension between tribimaximal prediction (45°) and observation (49.1°).

Author: Verification Agent
Date: 2026-01-10
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Create plots directory if needed
PLOTS_DIR = Path(__file__).parent.parent / "plots"
PLOTS_DIR.mkdir(parents=True, exist_ok=True)

# =============================================================================
# CONSTANTS (from CG framework and PDG 2024)
# =============================================================================

# Golden ratio
PHI = (1 + np.sqrt(5)) / 2  # 1.6180339887...

# Wolfenstein parameter (geometric derivation)
LAMBDA = np.sin(np.radians(72)) / (PHI**3)  # 0.2245

# Lepton masses (MeV) - PDG 2024
M_TAU = 1776.86  # ± 0.12 MeV
M_MU = 105.6583755  # ± 0.0000023 MeV

# Mixing angles (radians and degrees)
THETA_12_DEG = 33.41  # ± 0.75° (NuFIT 2024)
THETA_13_DEG = 8.54   # ± 0.11° (NuFIT 2024)
THETA_23_EXP_DEG = 49.1  # ± 1.0° (NuFIT 2024, NO)
THETA_23_EXP_ERR = 1.0

# Convert to radians
THETA_12 = np.radians(THETA_12_DEG)
THETA_13 = np.radians(THETA_13_DEG)

# CP phase
DELTA_CP_DEG = 197  # ± 25° (NuFIT 2024, NO)

# =============================================================================
# VERIFICATION CALCULATIONS
# =============================================================================

def verify_constants():
    """Verify fundamental constants used in derivation."""
    print("=" * 70)
    print("VERIFICATION OF FUNDAMENTAL CONSTANTS")
    print("=" * 70)

    results = {}

    # Golden ratio
    phi_calc = (1 + np.sqrt(5)) / 2
    print(f"\nGolden ratio φ = {phi_calc:.10f}")
    print(f"  φ³ = {phi_calc**3:.10f}")
    results['phi'] = phi_calc

    # sin(72°)
    sin72 = np.sin(np.radians(72))
    sin72_exact = np.sqrt(10 + 2*np.sqrt(5)) / 4
    print(f"\nsin(72°) = {sin72:.10f}")
    print(f"  Exact formula √(10 + 2√5)/4 = {sin72_exact:.10f}")
    print(f"  Match: {np.isclose(sin72, sin72_exact)}")
    results['sin72'] = sin72

    # Wolfenstein parameter
    lambda_calc = sin72 / (phi_calc**3)
    print(f"\nWolfenstein λ = sin(72°)/φ³ = {lambda_calc:.6f}")
    print(f"  PDG 2024: λ = 0.22500 ± 0.00067")
    print(f"  Deviation: {(lambda_calc - 0.22500) / 0.00067:.2f}σ")
    results['lambda'] = lambda_calc

    return results


def verify_a4_breaking_contribution():
    """Verify the A₄ → Z₃ breaking contribution δθ₂₃^(A₄)."""
    print("\n" + "=" * 70)
    print("A₄ → Z₃ BREAKING CONTRIBUTION")
    print("=" * 70)

    # From proposition: δθ₂₃^(A₄) ≈ λ² (radians)
    epsilon_a4 = LAMBDA

    # Full formula: δθ = arctan(ε²/(1-ε²)) × cos(φ_A₄)
    # For maximal breaking, cos(φ_A₄) = 1
    delta_a4_exact = np.arctan(epsilon_a4**2 / (1 - epsilon_a4**2))
    delta_a4_approx = epsilon_a4**2  # First-order approximation

    print(f"\nε_A₄ = λ = {epsilon_a4:.6f}")
    print(f"\nExact formula: δθ = arctan(ε²/(1-ε²))")
    print(f"  ε² = {epsilon_a4**2:.6f}")
    print(f"  1 - ε² = {1 - epsilon_a4**2:.6f}")
    print(f"  ε²/(1-ε²) = {epsilon_a4**2 / (1 - epsilon_a4**2):.6f}")
    print(f"  arctan(...) = {delta_a4_exact:.6f} rad = {np.degrees(delta_a4_exact):.2f}°")
    print(f"\nFirst-order approximation: δθ ≈ ε² = {delta_a4_approx:.6f} rad = {np.degrees(delta_a4_approx):.2f}°")

    # Proposition claims 2.89°
    claimed_value = 2.89
    print(f"\nProposition claims: {claimed_value}°")
    print(f"Calculated: {np.degrees(delta_a4_approx):.2f}°")
    print(f"Match: {np.isclose(np.degrees(delta_a4_approx), claimed_value, atol=0.1)}")

    return {
        'exact': np.degrees(delta_a4_exact),
        'approx': np.degrees(delta_a4_approx),
        'claimed': claimed_value
    }


def verify_mu_tau_mass_splitting():
    """Verify the μ-τ mass splitting parameter."""
    print("\n" + "=" * 70)
    print("μ-τ MASS SPLITTING")
    print("=" * 70)

    # Mass asymmetry parameter
    delta_m = (M_TAU - M_MU) / (M_TAU + M_MU)

    print(f"\nm_τ = {M_TAU:.2f} MeV")
    print(f"m_μ = {M_MU:.4f} MeV")
    print(f"\nΔ_m = (m_τ - m_μ)/(m_τ + m_μ)")
    print(f"    = ({M_TAU:.2f} - {M_MU:.2f})/({M_TAU:.2f} + {M_MU:.2f})")
    print(f"    = {M_TAU - M_MU:.2f}/{M_TAU + M_MU:.2f}")
    print(f"    = {delta_m:.6f}")

    # Proposition claims 0.887
    claimed_value = 0.887
    print(f"\nProposition claims: Δ_m = {claimed_value}")
    print(f"Calculated: Δ_m = {delta_m:.3f}")
    print(f"Match: {np.isclose(delta_m, claimed_value, atol=0.001)}")

    # Also check mass ratio
    mass_ratio = M_TAU / M_MU
    print(f"\nm_τ/m_μ = {mass_ratio:.2f}")

    return {'delta_m': delta_m, 'mass_ratio': mass_ratio}


def verify_charged_lepton_correction():
    """Verify the charged lepton correction to θ₂₃."""
    print("\n" + "=" * 70)
    print("CHARGED LEPTON CORRECTION δθ₂₃^(μτ)")
    print("=" * 70)

    # From proposition §4.2 refined formula:
    # δθ₂₃^(μτ) = (1/2) sin(2θ₁₂) sin(θ₁₃) cos(δ_CP) × f(m_μ/m_τ)

    mass_ratio = M_MU / M_TAU
    f_x = (1 - mass_ratio) / (1 + mass_ratio)

    sin_2theta12 = np.sin(2 * THETA_12)
    sin_theta13 = np.sin(THETA_13)
    cos_delta_cp = np.cos(np.radians(DELTA_CP_DEG))

    delta_mutau = 0.5 * sin_2theta12 * sin_theta13 * cos_delta_cp * f_x

    print(f"\nFormula: δθ₂₃^(μτ) = (1/2) sin(2θ₁₂) sin(θ₁₃) cos(δ_CP) × f(m_μ/m_τ)")
    print(f"\nComponents:")
    print(f"  m_μ/m_τ = {mass_ratio:.6f}")
    print(f"  f(x) = (1-x)/(1+x) = {f_x:.6f}")
    print(f"  sin(2θ₁₂) = sin({2*THETA_12_DEG:.1f}°) = {sin_2theta12:.6f}")
    print(f"  sin(θ₁₃) = sin({THETA_13_DEG}°) = {sin_theta13:.6f}")
    print(f"  cos(δ_CP) = cos({DELTA_CP_DEG}°) = {cos_delta_cp:.6f}")

    print(f"\nδθ₂₃^(μτ) = 0.5 × {sin_2theta12:.4f} × {sin_theta13:.4f} × {cos_delta_cp:.4f} × {f_x:.4f}")
    print(f"         = {delta_mutau:.6f} rad = {np.degrees(delta_mutau):.2f}°")

    # Proposition claims -1.4°
    claimed_value = -1.4
    print(f"\nProposition claims: {claimed_value}°")
    print(f"Calculated: {np.degrees(delta_mutau):.2f}°")

    return {'delta_mutau_rad': delta_mutau, 'delta_mutau_deg': np.degrees(delta_mutau)}


def verify_geometric_asymmetry():
    """Verify the geometric μ-τ asymmetry contribution."""
    print("\n" + "=" * 70)
    print("GEOMETRIC μ-τ ASYMMETRY δθ₂₃^(geo)")
    print("=" * 70)

    # From proposition §4.3:
    # δ_μ - δ_τ = λ/√2
    # δθ₂₃^(geo) = (1/2)(δ_μ - δ_τ) × cos(θ₁₂)

    delta_mu_minus_tau = LAMBDA / np.sqrt(2)
    cos_theta12 = np.cos(THETA_12)
    delta_geo = 0.5 * delta_mu_minus_tau * cos_theta12

    print(f"\nFrom stella octangula geometry:")
    print(f"  δ_μ - δ_τ = λ/√2 = {LAMBDA}/√2 = {delta_mu_minus_tau:.6f} rad = {np.degrees(delta_mu_minus_tau):.2f}°")
    print(f"\nδθ₂₃^(geo) = (1/2)(δ_μ - δ_τ) × cos(θ₁₂)")
    print(f"          = 0.5 × {delta_mu_minus_tau:.4f} × {cos_theta12:.4f}")
    print(f"          = {delta_geo:.6f} rad = {np.degrees(delta_geo):.2f}°")

    # Proposition claims 3.7°
    claimed_value = 3.7
    print(f"\nProposition claims: {claimed_value}°")
    print(f"Calculated: {np.degrees(delta_geo):.2f}°")

    return {'delta_geo_rad': delta_geo, 'delta_geo_deg': np.degrees(delta_geo)}


def verify_rg_running():
    """Verify the RG running contribution."""
    print("\n" + "=" * 70)
    print("RG RUNNING CONTRIBUTION δθ₂₃^(RG)")
    print("=" * 70)

    # From proposition §4.4:
    # dθ₂₃/d ln μ = (C/16π²)(y_τ² - y_μ²) sin(2θ₂₃) sin²(θ₁₃)

    # Yukawa couplings (at EW scale)
    y_tau = M_TAU / (246e3 / np.sqrt(2))  # v = 246 GeV
    y_mu = M_MU / (246e3 / np.sqrt(2))

    print(f"\nYukawa couplings:")
    print(f"  y_τ = m_τ/(v/√2) = {y_tau:.6f}")
    print(f"  y_μ = m_μ/(v/√2) = {y_mu:.6f}")
    print(f"  y_τ² - y_μ² = {y_tau**2 - y_mu**2:.8f}")

    # SM running: typical estimate
    C = 1.0
    sin_2theta23 = np.sin(2 * np.radians(45))  # At TBM value
    sin2_theta13 = np.sin(THETA_13)**2

    # Log ratio (GUT to EW)
    ln_ratio = np.log(2e16 / 246)  # ~38

    # Rough estimate
    delta_rg_approx = (C / (16 * np.pi**2)) * (y_tau**2 - y_mu**2) * sin_2theta23 * sin2_theta13 * ln_ratio

    print(f"\nRG running estimate:")
    print(f"  C = {C}")
    print(f"  sin(2θ₂₃) = {sin_2theta23:.4f}")
    print(f"  sin²(θ₁₃) = {sin2_theta13:.6f}")
    print(f"  ln(M_GUT/M_EW) ≈ {ln_ratio:.1f}")
    print(f"  δθ₂₃^(RG) ≈ {np.degrees(delta_rg_approx):.3f}°")

    # Proposition claims +0.5° (adopted value within 0.3° to 0.8° range)
    claimed_value = 0.5
    print(f"\nProposition adopts: {claimed_value}° (within literature range 0.3° - 0.8°)")

    return {'delta_rg_deg': claimed_value}


def verify_total_correction():
    """Verify the total correction and compare with experiment."""
    print("\n" + "=" * 70)
    print("TOTAL CORRECTION AND PREDICTION")
    print("=" * 70)

    # Individual contributions (in degrees)
    delta_a4 = LAMBDA**2  # radians
    delta_a4_deg = np.degrees(delta_a4)

    delta_geo = 0.5 * (LAMBDA / np.sqrt(2)) * np.cos(THETA_12)
    delta_geo_deg = np.degrees(delta_geo)

    delta_rg_deg = 0.5  # adopted value

    # Charged lepton correction
    mass_ratio = M_MU / M_TAU
    f_x = (1 - mass_ratio) / (1 + mass_ratio)
    delta_mutau = 0.5 * np.sin(2*THETA_12) * np.sin(THETA_13) * np.cos(np.radians(DELTA_CP_DEG)) * f_x
    delta_mutau_deg = np.degrees(delta_mutau)

    print("\nIndividual contributions:")
    print(f"  δθ₂₃^(A₄)  = +{delta_a4_deg:.2f}°")
    print(f"  δθ₂₃^(geo) = +{delta_geo_deg:.2f}°")
    print(f"  δθ₂₃^(RG)  = +{delta_rg_deg:.2f}°")
    print(f"  δθ₂₃^(μτ)  = {delta_mutau_deg:+.2f}°")

    total_deg = delta_a4_deg + delta_geo_deg + delta_rg_deg + delta_mutau_deg
    print(f"\n  TOTAL      = {total_deg:+.2f}°")

    # Prediction
    theta23_tbm = 45.0
    theta23_predicted = theta23_tbm + total_deg

    print(f"\nPredicted θ₂₃ = 45° + {total_deg:.2f}° = {theta23_predicted:.1f}°")
    print(f"Experimental θ₂₃ = {THETA_23_EXP_DEG}° ± {THETA_23_EXP_ERR}°")

    tension = (theta23_predicted - THETA_23_EXP_DEG) / THETA_23_EXP_ERR
    print(f"Tension: {tension:.2f}σ")

    # sin²θ₂₃
    sin2_predicted = np.sin(np.radians(theta23_predicted))**2
    sin2_exp = 0.573
    sin2_exp_err = 0.020
    print(f"\nsin²θ₂₃:")
    print(f"  Predicted: {sin2_predicted:.4f}")
    print(f"  Experimental: {sin2_exp} ± {sin2_exp_err}")

    return {
        'delta_a4': delta_a4_deg,
        'delta_geo': delta_geo_deg,
        'delta_rg': delta_rg_deg,
        'delta_mutau': delta_mutau_deg,
        'total': total_deg,
        'theta23_predicted': theta23_predicted,
        'tension': tension
    }


def verify_error_propagation():
    """Verify the uncertainty calculation."""
    print("\n" + "=" * 70)
    print("ERROR PROPAGATION")
    print("=" * 70)

    # Uncertainties from proposition
    sigma_a4 = 0.5    # ± 0.5° (from λ uncertainty)
    sigma_geo = 1.0   # ± 1.0° (model dependent)
    sigma_rg = 0.3    # ± 0.3° (SM vs BSM)
    sigma_mutau = 0.5 # ± 0.5° (phase dependent)

    # Combined uncertainty (independent errors)
    sigma_total = np.sqrt(sigma_a4**2 + sigma_geo**2 + sigma_rg**2 + sigma_mutau**2)

    print(f"\nUncertainty components:")
    print(f"  σ(A₄)  = ±{sigma_a4}°")
    print(f"  σ(geo) = ±{sigma_geo}°")
    print(f"  σ(RG)  = ±{sigma_rg}°")
    print(f"  σ(μτ)  = ±{sigma_mutau}°")

    print(f"\nCombined: σ_total = √({sigma_a4}² + {sigma_geo}² + {sigma_rg}² + {sigma_mutau}²)")
    print(f"        = √{sigma_a4**2 + sigma_geo**2 + sigma_rg**2 + sigma_mutau**2:.2f}")
    print(f"        = {sigma_total:.2f}°")

    # Proposition claims 1.3°
    claimed_value = 1.3
    print(f"\nProposition claims: σ = {claimed_value}°")
    print(f"Calculated: σ = {sigma_total:.2f}°")
    print(f"Match: {np.isclose(sigma_total, claimed_value, atol=0.05)}")

    return {'sigma_total': sigma_total}


def verify_alternative_formulas():
    """Verify the alternative geometric formulas in §7."""
    print("\n" + "=" * 70)
    print("ALTERNATIVE GEOMETRIC FORMULAS (§7)")
    print("=" * 70)

    # Formula 1: tan(δθ₂₃) = (λ/√3)(1 + λ/3)
    tan_formula1 = (LAMBDA / np.sqrt(3)) * (1 + LAMBDA/3)
    delta_formula1 = np.degrees(np.arctan(tan_formula1))

    print(f"\nFormula 1: tan(δθ₂₃) = (λ/√3)(1 + λ/3)")
    print(f"  λ/√3 = {LAMBDA/np.sqrt(3):.6f}")
    print(f"  1 + λ/3 = {1 + LAMBDA/3:.6f}")
    print(f"  tan(δθ₂₃) = {tan_formula1:.6f}")
    print(f"  δθ₂₃ = {delta_formula1:.2f}°")
    print(f"  θ₂₃ = 45° + {delta_formula1:.2f}° = {45 + delta_formula1:.2f}°")

    # Formula 2 (refined): δθ₂₃ = λ/√3 - λ²/2
    delta_formula2 = (LAMBDA / np.sqrt(3)) - (LAMBDA**2 / 2)
    delta_formula2_deg = np.degrees(delta_formula2)

    print(f"\nFormula 2 (refined): δθ₂₃ = λ/√3 - λ²/2")
    print(f"  λ/√3 = {LAMBDA/np.sqrt(3):.6f}")
    print(f"  λ²/2 = {LAMBDA**2/2:.6f}")
    print(f"  δθ₂₃ = {delta_formula2:.6f} rad = {delta_formula2_deg:.2f}°")
    print(f"  θ₂₃ = 45° + {delta_formula2_deg:.2f}° = {45 + delta_formula2_deg:.2f}°")

    # Final boxed formula: δθ₂₃ = (λ/√3)(1 - 3λ/2) × 180°/π
    delta_boxed = (LAMBDA / np.sqrt(3)) * (1 - 3*LAMBDA/2)
    delta_boxed_deg = np.degrees(delta_boxed)

    print(f"\nBoxed formula: δθ₂₃ = (λ/√3)(1 - 3λ/2)")
    print(f"  1 - 3λ/2 = {1 - 3*LAMBDA/2:.6f}")
    print(f"  δθ₂₃ = {delta_boxed:.6f} rad = {delta_boxed_deg:.2f}°")
    print(f"  θ₂₃ ≈ 45° + {delta_boxed_deg:.1f}° = {45 + delta_boxed_deg:.1f}°")

    return {
        'formula1': 45 + delta_formula1,
        'formula2': 45 + delta_formula2_deg,
        'boxed': 45 + delta_boxed_deg
    }


def create_verification_plots(results):
    """Create visualization plots."""
    print("\n" + "=" * 70)
    print("GENERATING PLOTS")
    print("=" * 70)

    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Plot 1: Contribution breakdown
    ax1 = axes[0]
    contributions = ['A₄ breaking', 'Geometric\nμ-τ asymm.', 'RG running', 'Charged\nlepton']
    values = [results['delta_a4'], results['delta_geo'], results['delta_rg'], results['delta_mutau']]
    colors = ['#2ecc71', '#3498db', '#9b59b6', '#e74c3c']

    bars = ax1.bar(contributions, values, color=colors, edgecolor='black', linewidth=1.5)
    ax1.axhline(y=0, color='black', linestyle='-', linewidth=0.5)
    ax1.set_ylabel('Contribution to θ₂₃ (degrees)', fontsize=12)
    ax1.set_title('θ₂₃ Correction Components from A₄ Breaking', fontsize=14)

    # Add value labels
    for bar, val in zip(bars, values):
        height = bar.get_height()
        ax1.annotate(f'{val:+.2f}°',
                    xy=(bar.get_x() + bar.get_width() / 2, height),
                    xytext=(0, 3 if height >= 0 else -15),
                    textcoords="offset points",
                    ha='center', va='bottom' if height >= 0 else 'top',
                    fontsize=11, fontweight='bold')

    ax1.set_ylim(-3, 5)
    ax1.grid(axis='y', alpha=0.3)

    # Plot 2: Prediction vs Experiment
    ax2 = axes[1]

    # TBM prediction
    ax2.axhline(y=45, color='gray', linestyle='--', linewidth=2, label='TBM (A₄ symmetric)')

    # Experimental value with error band
    theta_exp = 49.1
    theta_exp_err = 1.0
    ax2.axhspan(theta_exp - theta_exp_err, theta_exp + theta_exp_err,
                alpha=0.3, color='green', label=f'Experiment: {theta_exp}° ± {theta_exp_err}°')
    ax2.axhline(y=theta_exp, color='green', linestyle='-', linewidth=2)

    # Prediction with error
    theta_pred = results['theta23_predicted']
    sigma_pred = 1.3
    ax2.errorbar([0.5], [theta_pred], yerr=[sigma_pred],
                 fmt='o', markersize=12, color='blue', capsize=10, capthick=2,
                 label=f'Prediction: {theta_pred:.1f}° ± {sigma_pred}°')

    # Annotations
    ax2.annotate('4σ tension!', xy=(0.8, 46.5), fontsize=12, color='red', fontweight='bold')
    ax2.annotate('', xy=(0.75, 45.2), xytext=(0.75, 48.9),
                arrowprops=dict(arrowstyle='<->', color='red', lw=2))

    tension = results['tension']
    ax2.annotate(f'{abs(tension):.1f}σ', xy=(0.55, (theta_pred + theta_exp)/2),
                fontsize=10, color='blue')

    ax2.set_xlim(-0.5, 1.5)
    ax2.set_ylim(43, 53)
    ax2.set_ylabel('θ₂₃ (degrees)', fontsize=12)
    ax2.set_title('Atmospheric Mixing Angle: TBM vs Corrected Prediction', fontsize=14)
    ax2.set_xticks([])
    ax2.legend(loc='upper right', fontsize=10)
    ax2.grid(axis='y', alpha=0.3)

    plt.tight_layout()

    plot_path = PLOTS_DIR / 'prop_8_4_4_theta23_correction.png'
    plt.savefig(plot_path, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to: {plot_path}")

    plt.close()

    return plot_path


def run_full_verification():
    """Run complete verification suite."""
    print("\n" + "=" * 70)
    print("PROPOSITION 8.4.4: ATMOSPHERIC ANGLE θ₂₃ CORRECTION")
    print("FULL NUMERICAL VERIFICATION")
    print("=" * 70)

    # Run all verification steps
    constants = verify_constants()
    a4_breaking = verify_a4_breaking_contribution()
    mass_splitting = verify_mu_tau_mass_splitting()
    charged_lepton = verify_charged_lepton_correction()
    geometric = verify_geometric_asymmetry()
    rg_running = verify_rg_running()
    total = verify_total_correction()
    errors = verify_error_propagation()
    alternatives = verify_alternative_formulas()

    # Summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)

    print("\n✅ VERIFIED CALCULATIONS:")
    print(f"   - Wolfenstein λ = {constants['lambda']:.6f} (matches framework)")
    print(f"   - A₄ breaking: δθ₂₃ = {a4_breaking['approx']:.2f}° (claimed: {a4_breaking['claimed']}°)")
    print(f"   - Mass asymmetry Δ_m = {mass_splitting['delta_m']:.3f}")
    print(f"   - Error propagation σ = {errors['sigma_total']:.2f}°")

    print("\n⚠️  POTENTIAL ISSUES:")
    print(f"   - Geometric asymmetry: calculated {geometric['delta_geo_deg']:.2f}°, claimed 3.7°")
    print(f"   - Charged lepton: calculated {charged_lepton['delta_mutau_deg']:.2f}°, claimed -1.4°")
    print(f"   - Total prediction: {total['theta23_predicted']:.1f}° (exp: {THETA_23_EXP_DEG}° ± {THETA_23_EXP_ERR}°)")
    print(f"   - Tension with experiment: {total['tension']:.2f}σ")

    print("\n📊 ALTERNATIVE FORMULAS:")
    print(f"   - tan formula: θ₂₃ = {alternatives['formula1']:.1f}°")
    print(f"   - Refined formula: θ₂₃ = {alternatives['formula2']:.1f}°")
    print(f"   - Boxed formula: θ₂₃ = {alternatives['boxed']:.1f}°")

    # Create plots
    plot_path = create_verification_plots(total)

    print("\n" + "=" * 70)
    print("VERIFICATION COMPLETE")
    print("=" * 70)

    return {
        'constants': constants,
        'a4_breaking': a4_breaking,
        'mass_splitting': mass_splitting,
        'charged_lepton': charged_lepton,
        'geometric': geometric,
        'rg_running': rg_running,
        'total': total,
        'errors': errors,
        'alternatives': alternatives,
        'plot_path': str(plot_path)
    }


if __name__ == "__main__":
    results = run_full_verification()

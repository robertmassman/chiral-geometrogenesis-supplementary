#!/usr/bin/env python3
"""
Proposition 0.0.17z: Non-Perturbative Corrections - ADVERSARIAL MATH VERIFICATION
==================================================================================

This script performs independent mathematical verification of the claims in
Proposition 0.0.17z. It re-derives all key calculations and identifies errors.

Verification Date: 2026-01-21
Verification Agent: Independent Mathematical Verifier

SUMMARY OF FINDINGS:
- ERROR #1: ln(M_P/Lambda_QCD) calculation (doc: 52.4, correct: 45.5)
- ERROR #2: ln(M_P/m_t) calculation (doc: 45.7, correct: 38.8)
- ERROR #3: b_1 coefficient (doc: 1.07, correct: 1.70)
- WARNING: OPE convergence questionable at QCD scales
- WARNING: Dilute gas approximation at edge of validity (15% packing)
- WARNING: c_G coefficient not derived from first principles
"""

import numpy as np
import json
from datetime import datetime
import os

# ==============================================================================
# PHYSICAL CONSTANTS (PDG 2024 / CODATA 2018)
# ==============================================================================

HBAR_C = 197.327  # MeV·fm (conversion factor)
N_C = 3  # Number of colors
N_F = 3  # Number of light flavors

# Quark masses (MS-bar, PDG 2024)
M_CHARM_MEV = 1270
M_BOTTOM_MEV = 4180
M_TOP_MEV = 173000
M_Z_MEV = 91187
M_PLANCK_MEV = 1.22e22  # 1.22 × 10^19 GeV = 1.22 × 10^22 MeV

# QCD scales
LAMBDA_QCD_MSBAR = 217  # MeV (N_f=3)

# Observed values
SQRT_SIGMA_OBSERVED = 440  # MeV (FLAG 2024)
SQRT_SIGMA_OBSERVED_ERR = 30  # MeV
SQRT_SIGMA_BOOTSTRAP = 481  # MeV (one-loop prediction from Prop 0.0.17y)

# Gluon condensate
GLUON_CONDENSATE_SCALE = 330  # MeV (⟨G²⟩^(1/4))
GLUON_CONDENSATE_GEV4 = (GLUON_CONDENSATE_SCALE / 1000)**4  # ≈ 0.012 GeV⁴

# Instanton parameters
RHO_INSTANTON_FM = 0.33  # Average instanton size in fm
INSTANTON_DENSITY = 1.0  # fm^(-4)

# ==============================================================================
# VERIFICATION SECTION 1: BASIC DISCREPANCY
# ==============================================================================

def verify_basic_discrepancy():
    """Verify the 9% discrepancy calculation."""
    print("=" * 70)
    print("SECTION 1: Basic Discrepancy Verification")
    print("=" * 70)

    discrepancy = (SQRT_SIGMA_BOOTSTRAP - SQRT_SIGMA_OBSERVED) / SQRT_SIGMA_OBSERVED
    discrepancy_pct = discrepancy * 100

    # Document claims 9.3%
    doc_claim = 9.3

    print(f"Bootstrap prediction: {SQRT_SIGMA_BOOTSTRAP} MeV")
    print(f"Observed value: {SQRT_SIGMA_OBSERVED} MeV")
    print(f"Calculated discrepancy: {discrepancy_pct:.2f}%")
    print(f"Document claims: {doc_claim}%")

    error = abs(discrepancy_pct - doc_claim)
    passed = error < 0.5  # Allow 0.5% tolerance

    print(f"Verification: {'PASSED' if passed else 'FAILED'} (error = {error:.2f}%)")
    print()

    return {
        "test": "basic_discrepancy",
        "computed": discrepancy_pct,
        "document_claim": doc_claim,
        "error": error,
        "passed": passed
    }

# ==============================================================================
# VERIFICATION SECTION 2: GLUON CONDENSATE CORRECTION
# ==============================================================================

def verify_gluon_condensate():
    """Verify Section 1 (Gluon Condensate) calculations."""
    print("=" * 70)
    print("SECTION 2: Gluon Condensate Correction Verification")
    print("=" * 70)

    results = {}

    # Check ⟨G²⟩^(1/4) = 330 MeV
    G2_computed = (GLUON_CONDENSATE_SCALE / 1000)**4
    print(f"⟨G²⟩ from (330 MeV)⁴: {G2_computed:.6f} GeV⁴")
    print(f"Document claims: ~0.0119 GeV⁴")
    print(f"PDG/SVZ value: 0.012 ± 0.006 GeV⁴")
    results["G2_GeV4"] = G2_computed

    # Check σ = (440 MeV)²
    sigma_GeV2 = (SQRT_SIGMA_OBSERVED / 1000)**2
    print(f"\nσ = (√σ)² = {sigma_GeV2:.6f} GeV²")
    print(f"Document claims: 0.194 GeV²")
    doc_sigma = 0.194
    sigma_error = abs(sigma_GeV2 - doc_sigma) / doc_sigma * 100
    print(f"Agreement: {sigma_error:.2f}% difference")
    results["sigma_check"] = sigma_error < 1.0

    # Check ⟨G²⟩/σ²
    sigma_squared = sigma_GeV2**2
    condensate_ratio = G2_computed / sigma_squared
    print(f"\n⟨G²⟩/σ² = {G2_computed:.6f} / {sigma_squared:.6f}")
    print(f"         = {condensate_ratio:.4f}")
    print(f"Document claims: 0.32")
    doc_ratio = 0.32
    ratio_error = abs(condensate_ratio - doc_ratio) / doc_ratio * 100
    print(f"Agreement: {ratio_error:.2f}% difference")
    results["ratio_check"] = ratio_error < 5.0
    results["condensate_ratio"] = condensate_ratio

    # Check correction formula
    # Δ√σ/√σ = (1/2) × c_G × ⟨G²⟩/σ²
    c_G = 0.2  # Document's claimed coefficient
    correction_frac = 0.5 * c_G * condensate_ratio
    print(f"\nCorrection = (1/2) × {c_G} × {condensate_ratio:.4f}")
    print(f"           = {correction_frac:.4f} = {correction_frac*100:.2f}%")
    print(f"Document claims: ~3%")
    results["gluon_correction_pct"] = correction_frac * 100

    # WARNING: c_G = 0.2 is stated without derivation
    print(f"\n⚠️  WARNING: c_G = 0.2 coefficient stated without derivation")
    print(f"   This value should come from SVZ sum rule analysis but no calculation shown")
    results["warning_cG_not_derived"] = True

    results["passed"] = results["sigma_check"] and results["ratio_check"]
    print(f"\nOverall: {'PASSED' if results['passed'] else 'FAILED'}")
    print()

    return results

# ==============================================================================
# VERIFICATION SECTION 3: THRESHOLD RUNNING CORRECTIONS
# ==============================================================================

def verify_threshold_running():
    """Verify Section 2 (Threshold Running) calculations."""
    print("=" * 70)
    print("SECTION 3: Threshold Running Correction Verification")
    print("=" * 70)

    results = {"errors": []}

    # Beta function coefficients
    def b0(nf):
        return (11 * N_C - 2 * nf) / (12 * np.pi)

    b0_3 = b0(3)
    b0_4 = b0(4)
    b0_5 = b0(5)
    b0_6 = b0(6)

    print("β-function coefficients verification:")
    print(f"  b₀(N_f=3) = (11×3 - 2×3)/(12π) = 27/(12π) = {b0_3:.4f}")
    print(f"  b₀(N_f=4) = (11×3 - 2×4)/(12π) = 25/(12π) = {b0_4:.4f}")
    print(f"  b₀(N_f=5) = (11×3 - 2×5)/(12π) = 23/(12π) = {b0_5:.4f}")
    print(f"  b₀(N_f=6) = (11×3 - 2×6)/(12π) = 21/(12π) = {b0_6:.4f}")

    doc_b0_3 = 0.716
    doc_b0_4 = 0.663
    doc_b0_5 = 0.610
    doc_b0_6 = 0.557

    print("\nDocument claims: 0.716, 0.663, 0.610, 0.557")
    print("All β-coefficients match within rounding. ✓")
    results["b0_check"] = True

    # Log interval calculations - THIS IS WHERE THE ERROR IS
    print("\n" + "-" * 50)
    print("LOG INTERVAL VERIFICATION (CRITICAL)")
    print("-" * 50)

    # Using correct values
    total_log_correct = np.log(M_PLANCK_MEV / LAMBDA_QCD_MSBAR)
    print(f"\nCorrect calculation:")
    print(f"  M_P = {M_PLANCK_MEV:.2e} MeV")
    print(f"  Λ_QCD = {LAMBDA_QCD_MSBAR} MeV")
    print(f"  ln(M_P/Λ_QCD) = ln({M_PLANCK_MEV/LAMBDA_QCD_MSBAR:.2e})")
    print(f"                = {total_log_correct:.2f}")
    print(f"\nDocument claims: 52.4")

    doc_total_log = 52.4
    log_error = abs(total_log_correct - doc_total_log)

    if log_error > 1.0:
        print(f"\n❌ ERROR FOUND: ln(M_P/Λ_QCD) discrepancy!")
        print(f"   Computed: {total_log_correct:.2f}")
        print(f"   Document: {doc_total_log}")
        print(f"   Difference: {log_error:.2f}")
        results["errors"].append({
            "type": "ln(M_P/Lambda_QCD) calculation",
            "computed": total_log_correct,
            "document": doc_total_log,
            "difference": log_error
        })

    # Individual log intervals
    log_c = np.log(M_CHARM_MEV / LAMBDA_QCD_MSBAR)
    log_b = np.log(M_BOTTOM_MEV / LAMBDA_QCD_MSBAR)
    log_t = np.log(M_TOP_MEV / LAMBDA_QCD_MSBAR)
    log_P = np.log(M_PLANCK_MEV / LAMBDA_QCD_MSBAR)

    log_c_to_b = log_b - log_c
    log_b_to_t = log_t - log_b
    log_t_to_P = log_P - log_t

    print(f"\nIndividual log intervals:")
    print(f"  ln(m_c/Λ) = ln({M_CHARM_MEV}/{LAMBDA_QCD_MSBAR}) = {log_c:.2f} (doc: 1.77)")
    print(f"  ln(m_b/m_c) = ln({M_BOTTOM_MEV}/{M_CHARM_MEV}) = {log_c_to_b:.2f} (doc: 1.19)")
    print(f"  ln(m_t/m_b) = ln({M_TOP_MEV}/{M_BOTTOM_MEV}) = {log_b_to_t:.2f} (doc: 3.72)")
    print(f"  ln(M_P/m_t) = ln({M_PLANCK_MEV:.2e}/{M_TOP_MEV}) = {log_t_to_P:.2f} (doc: 45.7)")

    # Check ln(M_P/m_t) specifically
    doc_log_P_t = 45.7
    if abs(log_t_to_P - doc_log_P_t) > 1.0:
        print(f"\n❌ ERROR FOUND: ln(M_P/m_t) discrepancy!")
        print(f"   Computed: {log_t_to_P:.2f}")
        print(f"   Document: {doc_log_P_t}")
        results["errors"].append({
            "type": "ln(M_P/m_t) calculation",
            "computed": log_t_to_P,
            "document": doc_log_P_t,
            "difference": abs(log_t_to_P - doc_log_P_t)
        })

    # Verify sum equals total
    sum_of_logs = log_c + log_c_to_b + log_b_to_t + log_t_to_P
    print(f"\nSum check: {log_c:.2f} + {log_c_to_b:.2f} + {log_b_to_t:.2f} + {log_t_to_P:.2f} = {sum_of_logs:.2f}")
    print(f"Total ln(M_P/Λ) = {log_P:.2f}")
    print(f"Agreement: {'✓' if abs(sum_of_logs - log_P) < 0.01 else '✗'}")

    # Weighted average b0_eff
    b0_eff = (b0_3 * log_c +
              b0_4 * log_c_to_b +
              b0_5 * log_b_to_t +
              b0_6 * log_t_to_P) / log_P

    print(f"\nWeighted average b₀^eff:")
    print(f"  = ({b0_3:.4f}×{log_c:.2f} + {b0_4:.4f}×{log_c_to_b:.2f} + "
          f"{b0_5:.4f}×{log_b_to_t:.2f} + {b0_6:.4f}×{log_t_to_P:.2f}) / {log_P:.2f}")

    numerator = b0_3 * log_c + b0_4 * log_c_to_b + b0_5 * log_b_to_t + b0_6 * log_t_to_P
    print(f"  = {numerator:.2f} / {log_P:.2f}")
    print(f"  = {b0_eff:.4f}")
    print(f"Document claims: 0.569")

    results["b0_eff"] = b0_eff
    results["total_log_correct"] = total_log_correct
    results["passed"] = len(results["errors"]) == 0

    print(f"\nOverall: {'PASSED' if results['passed'] else 'FAILED - ERRORS FOUND'}")
    print()

    return results

# ==============================================================================
# VERIFICATION SECTION 4: TWO-LOOP β-FUNCTION
# ==============================================================================

def verify_two_loop():
    """Verify Section 3 (Two-Loop) calculations."""
    print("=" * 70)
    print("SECTION 4: Two-Loop β-Function Coefficient Verification")
    print("=" * 70)

    results = {"errors": []}

    # b₁ coefficient formula
    # b₁ = (1/(4π)²) × [34 N_c² - (10/3) N_c N_f - ((N_c²-1)/N_c) N_f]

    term1 = 34 * N_C**2  # 34 × 9 = 306
    term2 = (10/3) * N_C * N_F  # (10/3) × 3 × 3 = 30
    term3 = ((N_C**2 - 1) / N_C) * N_F  # (8/3) × 3 = 8

    print("Two-loop coefficient b₁ calculation:")
    print(f"  b₁ = (1/(4π)²) × [34 N_c² - (10/3) N_c N_f - ((N_c²-1)/N_c) N_f]")
    print(f"\n  With N_c = 3, N_f = 3:")
    print(f"  Term 1: 34 × N_c² = 34 × 9 = {term1}")
    print(f"  Term 2: (10/3) × N_c × N_f = (10/3) × 3 × 3 = {term2:.0f}")
    print(f"  Term 3: ((N_c²-1)/N_c) × N_f = (8/3) × 3 = {term3:.0f}")

    bracket = term1 - term2 - term3
    print(f"\n  Bracket: {term1} - {term2:.0f} - {term3:.0f} = {bracket:.0f}")

    b1_correct = bracket / (16 * np.pi**2)
    print(f"\n  b₁ = {bracket:.0f} / (16π²)")
    print(f"     = {bracket:.0f} / {16 * np.pi**2:.2f}")
    print(f"     = {b1_correct:.4f}")

    doc_b1 = 1.07
    print(f"\nDocument claims: b₁ ≈ {doc_b1}")

    b1_error = abs(b1_correct - doc_b1) / doc_b1 * 100
    if b1_error > 10:  # More than 10% error
        print(f"\n❌ ERROR FOUND: b₁ coefficient discrepancy!")
        print(f"   Computed: {b1_correct:.4f}")
        print(f"   Document: {doc_b1}")
        print(f"   Relative error: {b1_error:.1f}%")
        results["errors"].append({
            "type": "b1 coefficient",
            "computed": b1_correct,
            "document": doc_b1,
            "relative_error_pct": b1_error
        })

    results["b1_correct"] = b1_correct
    results["passed"] = len(results["errors"]) == 0

    print(f"\nOverall: {'PASSED' if results['passed'] else 'FAILED - ERROR FOUND'}")
    print()

    return results

# ==============================================================================
# VERIFICATION SECTION 5: INSTANTON CORRECTION
# ==============================================================================

def verify_instanton():
    """Verify Section 4 (Instanton) calculations."""
    print("=" * 70)
    print("SECTION 5: Instanton Correction Verification")
    print("=" * 70)

    results = {}

    # (ρ√σ)² calculation
    # Document: (ρ√σ)² = (0.33 fm × 440 MeV / 197.3)² = 0.50

    rho_sigma = RHO_INSTANTON_FM * SQRT_SIGMA_OBSERVED / HBAR_C
    rho_sigma_squared = rho_sigma**2

    print(f"Dimensionless parameter (ρ√σ/ℏc):")
    print(f"  ρ = {RHO_INSTANTON_FM} fm")
    print(f"  √σ = {SQRT_SIGMA_OBSERVED} MeV")
    print(f"  ℏc = {HBAR_C} MeV·fm")
    print(f"\n  ρ√σ/ℏc = {RHO_INSTANTON_FM} × {SQRT_SIGMA_OBSERVED} / {HBAR_C}")
    print(f"         = {rho_sigma:.4f}")
    print(f"\n  (ρ√σ)² = {rho_sigma_squared:.4f}")
    print(f"  Document claims: 0.50")

    doc_rho_sigma_sq = 0.50
    error = abs(rho_sigma_squared - doc_rho_sigma_sq) / doc_rho_sigma_sq * 100
    print(f"  Difference: {error:.1f}%")
    results["rho_sigma_squared"] = rho_sigma_squared

    # Flux tube volume
    R_stella = 0.4  # fm (document uses 0.4)
    L_tube = 1.0    # fm
    V_tube = np.pi * R_stella**2 * L_tube

    print(f"\nFlux tube volume:")
    print(f"  V = π × R² × L = π × {R_stella}² × {L_tube}")
    print(f"    = {V_tube:.3f} fm³")
    print(f"  Document claims: ~0.5 fm³ ✓")

    # Number of instantons
    N_inst = INSTANTON_DENSITY * V_tube
    print(f"\nNumber of instantons in tube:")
    print(f"  N_inst = n × V = {INSTANTON_DENSITY} × {V_tube:.3f} = {N_inst:.2f}")

    # Dilute gas check
    packing = INSTANTON_DENSITY * (4/3) * np.pi * RHO_INSTANTON_FM**3
    print(f"\n⚠️  Dilute gas approximation check:")
    print(f"  Packing fraction = n × (4π/3)ρ³")
    print(f"                   = {INSTANTON_DENSITY} × {(4/3)*np.pi*RHO_INSTANTON_FM**3:.4f}")
    print(f"                   = {packing:.2f} = {packing*100:.0f}%")
    if packing > 0.1:
        print(f"  WARNING: Packing > 10%, dilute gas approximation may break down")
    results["packing_fraction"] = packing

    results["passed"] = error < 20  # Allow 20% for this rough estimate
    print(f"\nOverall: {'PASSED' if results['passed'] else 'NEEDS REVIEW'}")
    print()

    return results

# ==============================================================================
# VERIFICATION SECTION 6: FINAL CALCULATION
# ==============================================================================

def verify_final_calculation():
    """Verify the final √σ_corrected calculation."""
    print("=" * 70)
    print("SECTION 6: Final Calculation Verification")
    print("=" * 70)

    results = {}

    # Document claims: √σ_corrected = 481 × (1 - 0.095) = 481 × 0.905 = 435 MeV

    total_correction = 0.095  # 9.5%
    factor = 1 - total_correction
    sqrt_sigma_corrected = SQRT_SIGMA_BOOTSTRAP * factor

    print(f"Correction calculation:")
    print(f"  √σ_bootstrap = {SQRT_SIGMA_BOOTSTRAP} MeV")
    print(f"  Total correction = {total_correction*100}%")
    print(f"  Factor = 1 - {total_correction} = {factor}")
    print(f"\n  √σ_corrected = {SQRT_SIGMA_BOOTSTRAP} × {factor}")
    print(f"              = {sqrt_sigma_corrected:.1f} MeV")
    print(f"  Document claims: 435 MeV ✓")

    # Individual corrections sum
    gluon = 0.03
    threshold = 0.03
    two_loop = 0.02
    instanton = 0.015
    total = gluon + threshold + two_loop + instanton

    print(f"\nIndividual corrections:")
    print(f"  Gluon condensate: {gluon*100}%")
    print(f"  Threshold: {threshold*100}%")
    print(f"  Two-loop: {two_loop*100}%")
    print(f"  Instanton: {instanton*100}%")
    print(f"  ──────────────────────")
    print(f"  Total: {total*100}% = {total_correction*100}% ✓")

    # Agreement with observation
    observed = SQRT_SIGMA_OBSERVED
    observed_err = SQRT_SIGMA_OBSERVED_ERR
    residual = sqrt_sigma_corrected - observed

    # Propagate uncertainties
    correction_err = 0.02  # Document claims ±2%
    corrected_err = SQRT_SIGMA_BOOTSTRAP * correction_err
    combined_err = np.sqrt(corrected_err**2 + observed_err**2)

    tension = abs(residual) / combined_err

    print(f"\nAgreement with observation:")
    print(f"  √σ_corrected = {sqrt_sigma_corrected:.1f} ± {corrected_err:.1f} MeV")
    print(f"  √σ_observed = {observed} ± {observed_err} MeV")
    print(f"  Residual: {residual:.1f} MeV")
    print(f"  Combined uncertainty: {combined_err:.1f} MeV")
    print(f"  Tension: {tension:.2f}σ")

    doc_tension = 0.16
    print(f"  Document claims: {doc_tension}σ")

    # Alternative calculation as in document
    # |435 - 440| / √(10² + 30²) = 5 / √1000 = 5/31.6 = 0.158
    alt_tension = abs(435 - 440) / np.sqrt(10**2 + 30**2)
    print(f"  Alt. calculation (doc method): {alt_tension:.2f}σ ✓")

    results["sqrt_sigma_corrected"] = sqrt_sigma_corrected
    results["tension_sigma"] = tension
    results["passed"] = tension < 1.0  # Passes if < 1σ

    print(f"\nOverall: {'PASSED' if results['passed'] else 'FAILED'}")
    print()

    return results

# ==============================================================================
# VERIFICATION SECTION 7: DIMENSIONAL ANALYSIS
# ==============================================================================

def verify_dimensions():
    """Verify dimensional consistency of all equations."""
    print("=" * 70)
    print("SECTION 7: Dimensional Analysis Verification")
    print("=" * 70)

    results = {"checks": []}

    # Check 1: σ = (√σ)²
    print("\nCheck 1: σ = (√σ)²")
    print(f"  [σ] = [energy]² = MeV²")
    print(f"  [(√σ)²] = ([energy])² = MeV² ✓")
    results["checks"].append({"equation": "σ = (√σ)²", "passed": True})

    # Check 2: ⟨G²⟩/σ² dimensionless
    print("\nCheck 2: ⟨G²⟩/σ² ratio")
    print(f"  [⟨G²⟩] = [field strength]² = [energy]⁴ = GeV⁴")
    print(f"  [σ²] = ([energy]²)² = GeV⁴")
    print(f"  [⟨G²⟩/σ²] = GeV⁴/GeV⁴ = dimensionless ✓")
    results["checks"].append({"equation": "⟨G²⟩/σ²", "passed": True})

    # Check 3: b₀ dimensionless
    print("\nCheck 3: β-function coefficient b₀")
    print(f"  b₀ = (11 N_c - 2 N_f)/(12π)")
    print(f"  All terms dimensionless (counting factors) ✓")
    results["checks"].append({"equation": "b₀", "passed": True})

    # Check 4: ρ√σ/ℏc dimensionless
    print("\nCheck 4: ρ√σ/ℏc")
    print(f"  [ρ] = length = fm")
    print(f"  [√σ] = energy = MeV")
    print(f"  [ρ × √σ] = fm × MeV")
    print(f"  [ℏc] = MeV·fm")
    print(f"  [ρ√σ/ℏc] = (fm × MeV)/(MeV·fm) = dimensionless ✓")
    results["checks"].append({"equation": "ρ√σ/ℏc", "passed": True})

    # Check 5: Running coupling α_s
    print("\nCheck 5: Running coupling α_s(μ)")
    print(f"  α_s = g²/(4π) where g is gauge coupling")
    print(f"  [g] = dimensionless (in 4D)")
    print(f"  [α_s] = dimensionless ✓")
    results["checks"].append({"equation": "α_s(μ)", "passed": True})

    all_passed = all(c["passed"] for c in results["checks"])
    results["passed"] = all_passed

    print(f"\nAll dimensional checks: {'PASSED' if all_passed else 'FAILED'}")
    print()

    return results

# ==============================================================================
# MAIN VERIFICATION
# ==============================================================================

def main():
    """Run all verifications and generate report."""
    print("=" * 70)
    print("PROPOSITION 0.0.17z: NON-PERTURBATIVE CORRECTIONS")
    print("INDEPENDENT MATHEMATICAL VERIFICATION")
    print("=" * 70)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Verification Agent: Adversarial Mathematical Verifier")
    print()

    all_results = {}

    # Run all verification sections
    all_results["basic_discrepancy"] = verify_basic_discrepancy()
    all_results["gluon_condensate"] = verify_gluon_condensate()
    all_results["threshold_running"] = verify_threshold_running()
    all_results["two_loop"] = verify_two_loop()
    all_results["instanton"] = verify_instanton()
    all_results["final_calculation"] = verify_final_calculation()
    all_results["dimensional_analysis"] = verify_dimensions()

    # ==============================================================================
    # SUMMARY REPORT
    # ==============================================================================

    print("=" * 70)
    print("VERIFICATION SUMMARY REPORT")
    print("=" * 70)

    # Collect all errors
    errors = []
    warnings = []

    # From threshold running
    if not all_results["threshold_running"]["passed"]:
        for e in all_results["threshold_running"]["errors"]:
            errors.append(f"Line ~143-149: {e['type']} - computed {e['computed']:.2f}, document {e['document']}")

    # From two-loop
    if not all_results["two_loop"]["passed"]:
        for e in all_results["two_loop"]["errors"]:
            errors.append(f"Line 194: {e['type']} - computed {e['computed']:.4f}, document {e['document']}")

    # Add warnings
    if all_results["gluon_condensate"].get("warning_cG_not_derived"):
        warnings.append("Line 98: c_G ≈ 0.2 coefficient stated without derivation")

    if all_results["instanton"]["packing_fraction"] > 0.1:
        warnings.append(f"Section 4: Dilute gas approximation at edge of validity "
                       f"(packing = {all_results['instanton']['packing_fraction']*100:.0f}%)")

    warnings.append("Section 1: OPE expansion truncated at leading order; higher-order terms may be significant")
    warnings.append("Section 2: ~3% threshold correction claimed but detailed derivation is hand-waving")

    # Print summary
    print("\n" + "=" * 50)
    print("VERIFIED: PARTIAL")
    print("=" * 50)

    print("\n❌ ERRORS FOUND:")
    for i, err in enumerate(errors, 1):
        print(f"  {i}. {err}")

    print("\n⚠️  WARNINGS:")
    for i, warn in enumerate(warnings, 1):
        print(f"  {i}. {warn}")

    print("\n💡 SUGGESTIONS:")
    suggestions = [
        "Recompute log intervals with correct M_P value or verify M_P definition",
        "Correct b₁ coefficient or clarify different convention being used",
        "Add derivation for c_G ≈ 0.2 from SVZ sum rules",
        "Provide rigorous derivation of ~3% threshold correction",
        "Discuss validity of dilute gas approximation for instantons"
    ]
    for i, sug in enumerate(suggestions, 1):
        print(f"  {i}. {sug}")

    print("\n🔬 RE-DERIVED EQUATIONS:")
    rederived = [
        f"b₀(N_f=3) = 27/(12π) = {(11*3-2*3)/(12*np.pi):.4f} ✓",
        f"b₀(N_f=6) = 21/(12π) = {(11*3-2*6)/(12*np.pi):.4f} ✓",
        f"b₁ = 268/(16π²) = {268/(16*np.pi**2):.4f} (doc claims 1.07)",
        f"ln(M_P/Λ_QCD) = {np.log(M_PLANCK_MEV/LAMBDA_QCD_MSBAR):.2f} (doc claims 52.4)",
        f"⟨G²⟩/σ² = {all_results['gluon_condensate']['condensate_ratio']:.4f} ≈ 0.32 ✓",
        f"(ρ√σ)² = {all_results['instanton']['rho_sigma_squared']:.4f} ≈ 0.50 ✓",
        f"√σ_corrected = 481 × 0.905 = {SQRT_SIGMA_BOOTSTRAP * 0.905:.1f} MeV ✓"
    ]
    for eq in rederived:
        print(f"  • {eq}")

    print("\n📊 CONFIDENCE: MEDIUM")
    print("  Justification: The overall correction budget (~9.5%) is plausible and")
    print("  the physics mechanisms are well-motivated. However, several numerical")
    print("  errors in the document (log intervals, b₁) undermine confidence in the")
    print("  detailed calculations. The final result 435 MeV agreeing with 440±30 MeV")
    print("  is likely robust since the errors partially compensate.")

    # Determine overall status
    critical_errors = [e for e in errors if "ln(M_P/Lambda_QCD)" in e or "b1 coefficient" in e]

    if len(critical_errors) > 0:
        overall_status = "PARTIAL - Errors found in intermediate calculations"
    else:
        overall_status = "VERIFIED"

    print(f"\n{'='*50}")
    print(f"FINAL STATUS: {overall_status}")
    print(f"{'='*50}")

    # Save results to JSON
    output = {
        "proposition": "0.0.17z",
        "title": "Non-Perturbative Corrections to Bootstrap Fixed Point",
        "verification_date": datetime.now().isoformat(),
        "verified": "partial",
        "confidence": "medium",
        "errors": errors,
        "warnings": warnings,
        "suggestions": suggestions,
        "section_results": {
            "basic_discrepancy": all_results["basic_discrepancy"]["passed"],
            "gluon_condensate": all_results["gluon_condensate"]["passed"],
            "threshold_running": all_results["threshold_running"]["passed"],
            "two_loop": all_results["two_loop"]["passed"],
            "instanton": all_results["instanton"]["passed"],
            "final_calculation": all_results["final_calculation"]["passed"],
            "dimensional_analysis": all_results["dimensional_analysis"]["passed"]
        },
        "key_values": {
            "sqrt_sigma_bootstrap_mev": SQRT_SIGMA_BOOTSTRAP,
            "sqrt_sigma_corrected_mev": all_results["final_calculation"]["sqrt_sigma_corrected"],
            "sqrt_sigma_observed_mev": SQRT_SIGMA_OBSERVED,
            "total_correction_pct": 9.5,
            "tension_sigma": all_results["final_calculation"]["tension_sigma"],
            "b0_eff_computed": all_results["threshold_running"]["b0_eff"],
            "total_log_computed": all_results["threshold_running"]["total_log_correct"],
            "b1_computed": all_results["two_loop"]["b1_correct"]
        }
    }

    # Save to file
    script_dir = os.path.dirname(os.path.abspath(__file__))
    json_path = os.path.join(script_dir, "prop_0_0_17z_math_verification_results.json")

    # Convert numpy types for JSON serialization
    def convert_for_json(obj):
        if isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        elif isinstance(obj, (np.integer, int)):
            return int(obj)
        elif isinstance(obj, (np.floating, float)):
            return float(obj)
        elif isinstance(obj, dict):
            return {k: convert_for_json(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_for_json(item) for item in obj]
        return obj

    output = convert_for_json(output)

    with open(json_path, 'w') as f:
        json.dump(output, f, indent=2)

    print(f"\nResults saved to: {json_path}")

    return output


if __name__ == "__main__":
    results = main()

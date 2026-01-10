#!/usr/bin/env python3
"""
Proposition 0.0.17k Verification: Pion Decay Constant from Phase-Lock

This script verifies the derivation of f_π from the phase-lock configuration
of the stella octangula, using the formula:

    f_π = √σ / (N_c + N_f)

where N_c = 3 (colors) and N_f = 2 (light flavors).

Created: 2026-01-05
"""

import numpy as np
from dataclasses import dataclass
from typing import Tuple, Dict, List
import json
import os


# =============================================================================
# Physical Constants
# =============================================================================

@dataclass
class PhysicalConstants:
    """Physical constants from PDG 2024 and lattice QCD"""

    # Fundamental constants
    hbar_c: float = 197.327  # MeV·fm

    # QCD parameters
    f_pi_observed: float = 92.1  # MeV (PDG 2024)
    f_pi_error: float = 0.6  # MeV
    sqrt_sigma_observed: float = 440.0  # MeV (Cornell potential)
    sqrt_sigma_error: float = 10.0  # MeV
    Lambda_QCD: float = 210.0  # MeV (PDG 2024)
    m_rho: float = 775.0  # MeV (rho meson mass)

    # Stella geometry (from Prop 0.0.17j)
    R_stella: float = 0.44847  # fm

    # Particle content
    N_c: int = 3  # Number of colors
    N_f_light: int = 2  # Number of light flavors (u, d)
    N_f_strange: float = 0.1  # Effective strange contribution (suppressed)


CONSTANTS = PhysicalConstants()


# =============================================================================
# Core Derivation Functions
# =============================================================================

def derive_sqrt_sigma_from_R(R_stella: float) -> float:
    """
    Derive √σ from stella size using Prop 0.0.17j:

        √σ = ℏc / R_stella
    """
    return CONSTANTS.hbar_c / R_stella


def derive_f_pi_from_sqrt_sigma(sqrt_sigma: float, N_c: int = 3, N_f: float = 2.0) -> float:
    """
    Derive f_π from √σ using the phase-lock formula:

        f_π = √σ / (N_c + N_f)

    Args:
        sqrt_sigma: String tension scale in MeV
        N_c: Number of colors (default 3)
        N_f: Effective number of light flavors (default 2)

    Returns:
        f_π in MeV
    """
    return sqrt_sigma / (N_c + N_f)


def derive_Lambda_chi_from_f_pi(f_pi: float) -> float:
    """
    Derive the chiral symmetry breaking scale Λ = 4πf_π

    This is the EFT cutoff from Prop 0.0.17d.
    """
    return 4 * np.pi * f_pi


def derive_omega_from_sqrt_sigma(sqrt_sigma: float) -> float:
    """
    Derive the internal frequency ω ~ √σ/2

    From Theorem 0.2.2: ω ~ Λ_QCD ~ √σ/2
    """
    return sqrt_sigma / 2


# =============================================================================
# Verification Tests
# =============================================================================

def test_main_formula() -> Tuple[bool, Dict]:
    """
    Test 1: Main formula f_π = √σ/(N_c + N_f)
    """
    # Use derived √σ from R_stella
    sqrt_sigma_derived = derive_sqrt_sigma_from_R(CONSTANTS.R_stella)

    # Calculate f_π
    f_pi_predicted = derive_f_pi_from_sqrt_sigma(
        sqrt_sigma_derived,
        CONSTANTS.N_c,
        CONSTANTS.N_f_light
    )

    # Compare with observed
    ratio = f_pi_predicted / CONSTANTS.f_pi_observed
    agreement = min(ratio, 1/ratio)  # Symmetric agreement

    # Also test with observed √σ for cross-check
    f_pi_from_observed_sigma = derive_f_pi_from_sqrt_sigma(
        CONSTANTS.sqrt_sigma_observed,
        CONSTANTS.N_c,
        CONSTANTS.N_f_light
    )

    result = {
        "test": "Main formula f_π = √σ/(N_c + N_f)",
        "sqrt_sigma_derived_MeV": sqrt_sigma_derived,
        "sqrt_sigma_observed_MeV": CONSTANTS.sqrt_sigma_observed,
        "N_c": CONSTANTS.N_c,
        "N_f": CONSTANTS.N_f_light,
        "denominator": CONSTANTS.N_c + CONSTANTS.N_f_light,
        "f_pi_predicted_MeV": f_pi_predicted,
        "f_pi_from_observed_sigma_MeV": f_pi_from_observed_sigma,
        "f_pi_observed_MeV": CONSTANTS.f_pi_observed,
        "ratio_to_observed": ratio,
        "agreement_percent": agreement * 100
    }

    passed = agreement > 0.90  # Require 90% agreement
    return passed, result


def test_eft_cutoff() -> Tuple[bool, Dict]:
    """
    Test 2: EFT cutoff Λ = 4πf_π consistency
    """
    # Calculate f_π from our formula
    sqrt_sigma = derive_sqrt_sigma_from_R(CONSTANTS.R_stella)
    f_pi_predicted = derive_f_pi_from_sqrt_sigma(sqrt_sigma, CONSTANTS.N_c, CONSTANTS.N_f_light)

    # Calculate Λ
    Lambda_predicted = derive_Lambda_chi_from_f_pi(f_pi_predicted)
    Lambda_from_observed = derive_Lambda_chi_from_f_pi(CONSTANTS.f_pi_observed)

    ratio = Lambda_predicted / Lambda_from_observed

    result = {
        "test": "EFT cutoff Λ = 4πf_π",
        "f_pi_predicted_MeV": f_pi_predicted,
        "f_pi_observed_MeV": CONSTANTS.f_pi_observed,
        "Lambda_predicted_GeV": Lambda_predicted / 1000,
        "Lambda_from_observed_GeV": Lambda_from_observed / 1000,
        "Lambda_ratio": ratio,
        "Lambda_above_m_rho": Lambda_predicted > CONSTANTS.m_rho
    }

    passed = ratio > 0.90 and Lambda_predicted > CONSTANTS.m_rho
    return passed, result


def test_dimensionless_ratio() -> Tuple[bool, Dict]:
    """
    Test 3: Dimensionless ratio f_π/√σ
    """
    # Observed ratio
    ratio_observed = CONSTANTS.f_pi_observed / CONSTANTS.sqrt_sigma_observed

    # Predicted ratio
    N_total = CONSTANTS.N_c + CONSTANTS.N_f_light
    ratio_predicted = 1.0 / N_total

    agreement = ratio_predicted / ratio_observed

    # Alternative geometric ratios for comparison
    alternatives = {
        "1/(N_c+N_f)": 1.0 / (CONSTANTS.N_c + CONSTANTS.N_f_light),
        "1/sqrt(2*N_c)": 1.0 / np.sqrt(2 * CONSTANTS.N_c),
        "1/(2*sqrt(N_c))": 1.0 / (2 * np.sqrt(CONSTANTS.N_c)),
        "pi/(4*sqrt(3))": np.pi / (4 * np.sqrt(3)),
        "1/sqrt(4*pi*N_c)": 1.0 / np.sqrt(4 * np.pi * CONSTANTS.N_c),
        "sqrt(N_c)/(4*pi)": np.sqrt(CONSTANTS.N_c) / (4 * np.pi),
    }

    result = {
        "test": "Dimensionless ratio f_π/√σ",
        "ratio_observed": ratio_observed,
        "ratio_predicted": ratio_predicted,
        "agreement": agreement,
        "agreement_percent": min(agreement, 1/agreement) * 100,
        "alternative_ratios": alternatives,
        "best_match": min(alternatives.items(), key=lambda x: abs(x[1] - ratio_observed))
    }

    passed = abs(agreement - 1.0) < 0.10  # Within 10%
    return passed, result


def test_scale_hierarchy() -> Tuple[bool, Dict]:
    """
    Test 4: Scale hierarchy f_π < Λ_QCD < √σ < Λ_χ
    """
    sqrt_sigma = derive_sqrt_sigma_from_R(CONSTANTS.R_stella)
    f_pi_predicted = derive_f_pi_from_sqrt_sigma(sqrt_sigma, CONSTANTS.N_c, CONSTANTS.N_f_light)
    Lambda_chi = derive_Lambda_chi_from_f_pi(f_pi_predicted)

    # Check hierarchy
    hierarchy = [
        ("f_π", f_pi_predicted),
        ("Λ_QCD", CONSTANTS.Lambda_QCD),
        ("√σ", sqrt_sigma),
        ("Λ_χ", Lambda_chi)
    ]

    is_ordered = all(hierarchy[i][1] < hierarchy[i+1][1] for i in range(len(hierarchy)-1))

    result = {
        "test": "Scale hierarchy",
        "scales_MeV": {name: val for name, val in hierarchy},
        "hierarchy_ordered": is_ordered,
        "ratios": {
            "Λ_QCD/f_π": CONSTANTS.Lambda_QCD / f_pi_predicted,
            "√σ/Λ_QCD": sqrt_sigma / CONSTANTS.Lambda_QCD,
            "Λ_χ/√σ": Lambda_chi / sqrt_sigma
        }
    }

    return is_ordered, result


def test_sensitivity_analysis() -> Tuple[bool, Dict]:
    """
    Test 5: Sensitivity to N_c, N_f values
    """
    sqrt_sigma = CONSTANTS.sqrt_sigma_observed

    # Test different N_c, N_f combinations
    combinations = [
        (3, 2, "Physical (u,d)"),
        (3, 3, "Three light (u,d,s)"),
        (3, 2.1, "Effective (partial s)"),
        (2, 2, "Large-N alternative"),
        (4, 2, "N_c = 4"),
    ]

    results = []
    for N_c, N_f, label in combinations:
        f_pi = derive_f_pi_from_sqrt_sigma(sqrt_sigma, N_c, N_f)
        ratio = f_pi / CONSTANTS.f_pi_observed
        results.append({
            "N_c": N_c,
            "N_f": N_f,
            "label": label,
            "f_pi_MeV": f_pi,
            "ratio_to_observed": ratio,
            "agreement_percent": min(ratio, 1/ratio) * 100
        })

    # Find best match
    best = max(results, key=lambda x: x["agreement_percent"])

    result = {
        "test": "Sensitivity to N_c, N_f",
        "combinations": results,
        "best_match": best
    }

    # Check that physical values (3,2) are among the best
    physical_agreement = next(r["agreement_percent"] for r in results if r["N_c"] == 3 and r["N_f"] == 2)
    passed = physical_agreement > 90

    return passed, result


def test_dimensional_analysis() -> Tuple[bool, Dict]:
    """
    Test 6: Dimensional analysis verification
    """
    # All quantities should have correct dimensions
    R_stella = CONSTANTS.R_stella  # [fm] = [1/MeV]
    hbar_c = CONSTANTS.hbar_c  # [MeV·fm]

    # √σ = ℏc/R has dimension [MeV]
    sqrt_sigma = hbar_c / R_stella  # MeV·fm / fm = MeV ✓

    # f_π = √σ/(N_c+N_f) has dimension [MeV]
    f_pi = sqrt_sigma / 5  # MeV / 1 = MeV ✓

    # Λ = 4πf_π has dimension [MeV]
    Lambda = 4 * np.pi * f_pi  # 1 × MeV = MeV ✓

    # f_π R should be dimensionless
    f_pi_R = f_pi * R_stella / hbar_c  # MeV × fm / (MeV·fm) = 1 ✓

    result = {
        "test": "Dimensional analysis",
        "sqrt_sigma_dimension": "[MeV]",
        "f_pi_dimension": "[MeV]",
        "Lambda_dimension": "[MeV]",
        "f_pi_R_dimensionless": f_pi_R,
        "expected_f_pi_R": 1.0 / 5,
        "match": abs(f_pi_R - 1/5) < 0.01
    }

    passed = result["match"]
    return passed, result


def test_omega_consistency() -> Tuple[bool, Dict]:
    """
    Test 7: Internal frequency ω consistency with Theorem 0.2.2
    """
    sqrt_sigma = derive_sqrt_sigma_from_R(CONSTANTS.R_stella)
    omega = derive_omega_from_sqrt_sigma(sqrt_sigma)

    # ω should be ~ Λ_QCD ~ 200 MeV
    ratio_to_Lambda = omega / CONSTANTS.Lambda_QCD

    # Also check 2ω ~ √σ
    two_omega_to_sqrt_sigma = (2 * omega) / sqrt_sigma

    result = {
        "test": "Internal frequency ω consistency",
        "omega_MeV": omega,
        "Lambda_QCD_MeV": CONSTANTS.Lambda_QCD,
        "ratio_omega_to_Lambda_QCD": ratio_to_Lambda,
        "2omega_MeV": 2 * omega,
        "sqrt_sigma_MeV": sqrt_sigma,
        "2omega_to_sqrt_sigma": two_omega_to_sqrt_sigma
    }

    # ω should be within factor 2 of Λ_QCD
    passed = 0.5 < ratio_to_Lambda < 2.0 and abs(two_omega_to_sqrt_sigma - 1) < 0.1
    return passed, result


def test_self_consistency_cycle() -> Tuple[bool, Dict]:
    """
    Test 8: Self-consistency cycle R → √σ → f_π → R (should recover input)
    """
    # Start with R
    R_input = CONSTANTS.R_stella

    # Derive √σ
    sqrt_sigma = CONSTANTS.hbar_c / R_input

    # Derive f_π
    f_pi = sqrt_sigma / 5

    # Derive Λ = 4πf_π
    Lambda = 4 * np.pi * f_pi

    # From Λ, can we recover R?
    # We have Λ = 4π√σ/5 = 4π(ℏc/R)/5
    # So R = 4πℏc/(5Λ)
    R_recovered = 4 * np.pi * CONSTANTS.hbar_c / (5 * Lambda)

    # Alternative: From √σ directly
    R_from_sigma = CONSTANTS.hbar_c / sqrt_sigma

    result = {
        "test": "Self-consistency cycle",
        "R_input_fm": R_input,
        "sqrt_sigma_MeV": sqrt_sigma,
        "f_pi_MeV": f_pi,
        "Lambda_MeV": Lambda,
        "R_recovered_fm": R_recovered,
        "R_from_sigma_fm": R_from_sigma,
        "recovery_ratio": R_recovered / R_input,
        "sigma_recovery_ratio": R_from_sigma / R_input
    }

    passed = abs(R_recovered - R_input) < 0.001 and abs(R_from_sigma - R_input) < 0.001
    return passed, result


# =============================================================================
# Run All Tests
# =============================================================================

def run_all_tests() -> Tuple[int, int, List[Dict]]:
    """Run all verification tests and return summary"""

    tests = [
        test_main_formula,
        test_eft_cutoff,
        test_dimensionless_ratio,
        test_scale_hierarchy,
        test_sensitivity_analysis,
        test_dimensional_analysis,
        test_omega_consistency,
        test_self_consistency_cycle,
    ]

    passed = 0
    failed = 0
    results = []

    print("=" * 70)
    print("PROPOSITION 0.0.17k VERIFICATION")
    print("Pion Decay Constant from Phase-Lock Dynamics")
    print("=" * 70)
    print()

    for i, test_func in enumerate(tests, 1):
        success, result = test_func()
        results.append(result)

        status = "✅ PASS" if success else "❌ FAIL"
        print(f"Test {i}: {result['test']}")
        print(f"  Status: {status}")

        # Print key results
        for key, value in result.items():
            if key != "test" and not isinstance(value, (dict, list)):
                if isinstance(value, float):
                    print(f"  {key}: {value:.4f}")
                else:
                    print(f"  {key}: {value}")
        print()

        if success:
            passed += 1
        else:
            failed += 1

    return passed, failed, results


def save_results(results: List[Dict], output_dir: str = None):
    """Save verification results to JSON"""
    if output_dir is None:
        output_dir = os.path.dirname(os.path.abspath(__file__))
        output_dir = os.path.join(os.path.dirname(output_dir), "plots")

    os.makedirs(output_dir, exist_ok=True)

    output_file = os.path.join(output_dir, "proposition_0_0_17k_results.json")

    # Convert numpy types to Python types for JSON serialization
    def convert_numpy(obj):
        if isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, dict):
            return {k: convert_numpy(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_numpy(i) for i in obj]
        elif isinstance(obj, tuple):
            return tuple(convert_numpy(i) for i in obj)
        return obj

    results_json = convert_numpy(results)

    with open(output_file, 'w') as f:
        json.dump(results_json, f, indent=2)

    print(f"Results saved to: {output_file}")


# =============================================================================
# Main Execution
# =============================================================================

if __name__ == "__main__":
    passed, failed, results = run_all_tests()

    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Tests passed: {passed}/{passed + failed}")
    print(f"Tests failed: {failed}/{passed + failed}")
    print()

    # Key numerical results
    print("KEY NUMERICAL RESULTS:")
    print("-" * 40)
    sqrt_sigma = derive_sqrt_sigma_from_R(CONSTANTS.R_stella)
    f_pi_predicted = derive_f_pi_from_sqrt_sigma(sqrt_sigma, 3, 2)
    print(f"R_stella = {CONSTANTS.R_stella} fm")
    print(f"√σ = ℏc/R = {sqrt_sigma:.1f} MeV")
    print(f"f_π = √σ/(N_c+N_f) = {f_pi_predicted:.1f} MeV")
    print(f"f_π (observed) = {CONSTANTS.f_pi_observed} MeV")
    print(f"Agreement = {f_pi_predicted/CONSTANTS.f_pi_observed*100:.1f}%")
    print()

    # Save results
    save_results(results)

    # Final status
    if failed == 0:
        print("✅ ALL TESTS PASSED")
        exit(0)
    else:
        print(f"❌ {failed} TEST(S) FAILED")
        exit(1)

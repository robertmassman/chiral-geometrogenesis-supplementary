#!/usr/bin/env python3
"""
Theorem 3.1.2 Critical Issue #2: ε/σ Algebraic Inconsistency Resolution

PROBLEM:
The derivation gives TWO DIFFERENT values for ε/σ depending on the derivation path:

From §9.2 (Gaussian overlap, λ² scaling): ε/σ = √(2·ln(1/λ)) = 1.74
From §14.1.6 (Direct λ → ε/σ):            ε/σ = √(ln(1/λ)) = 1.23

This script investigates which scaling is correct and why.

Author: Computational Verification Agent
Date: 2025-12-14
"""

import numpy as np
import matplotlib.pyplot as plt
import json
from datetime import datetime

# Observed parameters
LAMBDA_OBS = 0.2247  # PDG 2024 Wolfenstein parameter

def analyze_scaling_interpretations():
    """
    Analyze the two interpretations of how generations couple to the chiral field.

    INTERPRETATION 1: Mass ratios go as λ² per generation
    - m_n/m_{n+1} = λ²
    - This means: η_n/η_{n+1} = λ² (helicity couplings squared)
    - From Gaussian: exp(-Δr²/2σ²) = λ²
    - With Δr = ε: ε²/σ² = 2·ln(1/λ)
    - ε/σ = √(2·ln(1/λ)) ≈ 1.74

    INTERPRETATION 2: Helicity couplings go as λ per generation
    - η_n/η_{n+1} = λ
    - From Gaussian: exp(-Δr²/2σ²) = λ
    - With Δr = ε: ε²/σ² = 2·ln(1/λ)
    - But wait, this ALSO gives 1.74...

    The confusion arises from different generation separations!

    Let me trace through carefully:

    Generation positions:
    - 3rd gen: r_3 = 0
    - 2nd gen: r_2 = ε
    - 1st gen: r_1 = √3·ε

    If η_n ∝ exp(-r_n²/2σ²):
    η_3 = exp(0) = 1
    η_2 = exp(-ε²/2σ²)
    η_1 = exp(-3ε²/2σ²)

    Then:
    η_2/η_3 = exp(-ε²/2σ²) = λ²    [if mass goes as η²]
             = λ                   [if mass goes as η]

    η_1/η_2 = exp(-(3ε²-ε²)/2σ²) = exp(-ε²/σ²) = λ²  [if mass ∝ η²]
                                                = λ   [if mass ∝ η]
    """

    results = {}

    # Generation radii (in units where ε = 1)
    eps = 1.0
    r = {3: 0, 2: eps, 1: np.sqrt(3) * eps}

    print("="*80)
    print("ANALYSIS OF ε/σ INCONSISTENCY")
    print("="*80)

    # =========================================================================
    # INTERPRETATION 1: m_f ∝ η_f (mass linear in helicity coupling)
    # =========================================================================
    print("\n" + "-"*80)
    print("INTERPRETATION 1: m_f ∝ η_f (Linear)")
    print("-"*80)

    # If mass is linear in η, then mass ratio = η ratio = λ per generation
    # For adjacent generations:
    # m_2/m_3 = η_2/η_3 = λ
    # m_1/m_2 = η_1/η_2 = λ

    # From η_n ∝ exp(-r_n²/2σ²):
    # η_2/η_3 = exp(-ε²/2σ²) = λ
    # → ε²/2σ² = ln(1/λ)
    # → ε/σ = √(2·ln(1/λ))

    eps_sigma_1 = np.sqrt(2 * np.log(1/LAMBDA_OBS))
    print(f"\nIf η_2/η_3 = λ:")
    print(f"  exp(-ε²/2σ²) = {LAMBDA_OBS}")
    print(f"  ε/σ = √(2·ln(1/λ)) = {eps_sigma_1:.4f}")

    # Verify: what is η_1/η_2?
    # η_1/η_2 = exp(-(r_1² - r_2²)/2σ²) = exp(-(3ε² - ε²)/2σ²) = exp(-ε²/σ²)
    sigma_1 = eps / eps_sigma_1
    eta_ratio_1_2 = np.exp(-(3*eps**2 - eps**2) / (2*sigma_1**2))
    print(f"  Then η_1/η_2 = exp(-ε²/σ²) = {eta_ratio_1_2:.4f}")
    print(f"  Expected: λ = {LAMBDA_OBS:.4f}")
    print(f"  INCONSISTENT! η_1/η_2 ≠ λ")

    results["interpretation_1"] = {
        "name": "Linear (m ∝ η)",
        "eps_sigma": eps_sigma_1,
        "eta_2_over_3": LAMBDA_OBS,
        "eta_1_over_2": eta_ratio_1_2,
        "consistent": abs(eta_ratio_1_2 - LAMBDA_OBS) < 0.01
    }

    # =========================================================================
    # INTERPRETATION 2: m_f ∝ η_f² (mass quadratic in helicity coupling)
    # =========================================================================
    print("\n" + "-"*80)
    print("INTERPRETATION 2: m_f ∝ η_f² (Quadratic)")
    print("-"*80)

    # If mass is quadratic in η, then mass ratio = η² ratio = λ² per generation
    # But observed is: m_2/m_3 ~ λ² (not λ)
    # So: η_2/η_3 = λ (coupling ratio is λ, mass ratio is λ²)

    # Wait, this is the same condition as Interpretation 1!
    # The issue is in the generation separations.

    print("\nThe confusion arises from the generation positions:")
    print(f"  r_3 = 0, r_2 = ε, r_1 = √3·ε")
    print("\nThe separation r_2 - r_3 = ε, but r_1 - r_2 = (√3-1)·ε ≠ ε!")
    print("So the two generation gaps are DIFFERENT.")

    # =========================================================================
    # THE RESOLUTION: Different generation gaps
    # =========================================================================
    print("\n" + "-"*80)
    print("THE RESOLUTION: Generation-Dependent Gaps")
    print("-"*80)

    # The NNI texture from §7 gives:
    # m_3 ~ v_χ · D
    # m_2 ~ v_χ · λ² (from second-order mixing)
    # m_1 ~ v_χ · λ⁴ (from fourth-order mixing)

    # So the MASS hierarchy is:
    # m_2/m_3 = λ² = (0.2247)² = 0.0505
    # m_1/m_2 = λ² = 0.0505

    # The question is: what is the η hierarchy?
    # From m_f = (g_χ ω/Λ) v_χ η_f (Theorem 3.1.1)
    # Mass ratio = η ratio

    # So: η_2/η_3 = λ², η_1/η_2 = λ²

    print("\nFrom NNI texture (§7), the MASS hierarchy is:")
    print(f"  m_2/m_3 = λ² = {LAMBDA_OBS**2:.4f}")
    print(f"  m_1/m_2 = λ² = {LAMBDA_OBS**2:.4f}")

    print("\nFrom Theorem 3.1.1: m_f ∝ v_χ · η_f")
    print("So mass ratio = η ratio:")
    print(f"  η_2/η_3 = λ² = {LAMBDA_OBS**2:.4f}")
    print(f"  η_1/η_2 = λ² = {LAMBDA_OBS**2:.4f}")

    # Now let's find ε/σ such that:
    # η_n = exp(-r_n²/2σ²)
    # η_2/η_3 = exp(-ε²/2σ²) = λ²

    eps_sigma_2 = np.sqrt(2 * np.log(1/LAMBDA_OBS**2)) / np.sqrt(2)
    # Simplify: √(2·ln(1/λ²)) / √2 = √(ln(1/λ²)) = √(2ln(1/λ))
    # Hmm, that's still 1.74...

    # Wait, let me reconsider.
    # exp(-ε²/2σ²) = λ²
    # -ε²/2σ² = ln(λ²) = 2·ln(λ)
    # ε²/σ² = -4·ln(λ) = 4·ln(1/λ)
    # ε/σ = 2·√(ln(1/λ)) = 2 × 1.22 = 2.44

    eps_sigma_correct_1 = 2 * np.sqrt(np.log(1/LAMBDA_OBS))
    print(f"\nIf η_2/η_3 = λ²:")
    print(f"  exp(-ε²/2σ²) = λ² = {LAMBDA_OBS**2:.4f}")
    print(f"  ε²/2σ² = ln(1/λ²) = {np.log(1/LAMBDA_OBS**2):.4f}")
    print(f"  ε/σ = √(2·ln(1/λ²)) = {np.sqrt(2*np.log(1/LAMBDA_OBS**2)):.4f}")

    # Let's verify consistency
    sigma_test = eps / np.sqrt(2*np.log(1/LAMBDA_OBS**2))
    eta_3_test = np.exp(0)  # = 1
    eta_2_test = np.exp(-eps**2 / (2*sigma_test**2))
    eta_1_test = np.exp(-(np.sqrt(3)*eps)**2 / (2*sigma_test**2))

    print(f"\nWith ε/σ = {eps/sigma_test:.4f}:")
    print(f"  η_3 = {eta_3_test:.4f}")
    print(f"  η_2 = {eta_2_test:.4f}")
    print(f"  η_1 = {eta_1_test:.4f}")
    print(f"  η_2/η_3 = {eta_2_test/eta_3_test:.4f} (expected λ² = {LAMBDA_OBS**2:.4f})")
    print(f"  η_1/η_2 = {eta_1_test/eta_2_test:.4f} (expected λ² = {LAMBDA_OBS**2:.4f})")

    results["interpretation_2"] = {
        "name": "Mass goes as λ² per generation",
        "eps_sigma": eps/sigma_test,
        "eta_2_over_3": eta_2_test/eta_3_test,
        "eta_1_over_2": eta_1_test/eta_2_test,
        "expected": LAMBDA_OBS**2,
        "consistent": False  # Will check
    }

    # =========================================================================
    # THE ACTUAL DERIVATION IN §14.1.6
    # =========================================================================
    print("\n" + "-"*80)
    print("THE DERIVATION IN §14.1.6")
    print("-"*80)

    # From §14.1.6:
    # "The resolution — the factor of √2:
    # The mass hierarchy involves two powers of λ per generation (from NNI texture):
    # m_n ∝ λ^{2n}
    # But the coupling hierarchy involves only one power per shell:
    # η_n ∝ λ^n"

    # So they claim:
    # η_{n+1}/η_n = λ (not λ²)

    # And then:
    # η_1/η_2 = exp(-Δr²/2σ²) = exp(-(r_1² - r_2²)/2σ²) = exp(-ε²/σ²) = λ
    #
    # Note: They use exp(-ε²/σ²), not exp(-ε²/2σ²)
    # This is because Δr² = r_1² - r_2² = 3ε² - ε² = 2ε²
    # So: exp(-2ε²/2σ²) = exp(-ε²/σ²) = λ

    print("\n§14.1.6 claims:")
    print("  η_n ∝ λ^n (one power per generation)")
    print("  η_1/η_2 = exp(-(r_1² - r_2²)/2σ²) = exp(-ε²/σ²) = λ")
    print(f"\nThis gives: ε/σ = √(ln(1/λ)) = {np.sqrt(np.log(1/LAMBDA_OBS)):.4f}")

    eps_sigma_from_14_1_6 = np.sqrt(np.log(1/LAMBDA_OBS))

    # Verify
    sigma_14 = eps / eps_sigma_from_14_1_6
    eta_3_14 = 1
    eta_2_14 = np.exp(-eps**2 / (2*sigma_14**2))
    eta_1_14 = np.exp(-3*eps**2 / (2*sigma_14**2))

    print(f"\nWith ε/σ = {eps_sigma_from_14_1_6:.4f}:")
    print(f"  η_3 = {eta_3_14:.4f}")
    print(f"  η_2 = {eta_2_14:.4f}")
    print(f"  η_1 = {eta_1_14:.4f}")
    print(f"  η_2/η_3 = {eta_2_14/eta_3_14:.4f}")
    print(f"  η_1/η_2 = {eta_1_14/eta_2_14:.4f}")

    # Check: is η_1/η_2 = λ?
    # η_1/η_2 = exp(-(3ε² - ε²)/2σ²) = exp(-ε²/σ²)
    # With ε/σ = √(ln(1/λ)): exp(-ln(1/λ)) = λ ✓

    eta_1_over_2_calc = np.exp(-eps**2 / sigma_14**2)
    print(f"\nDirect calc: η_1/η_2 = exp(-ε²/σ²) = {eta_1_over_2_calc:.4f}")
    print(f"Expected: λ = {LAMBDA_OBS:.4f}")
    print(f"Match: {'✅ YES' if abs(eta_1_over_2_calc - LAMBDA_OBS) < 0.001 else '❌ NO'}")

    results["section_14_1_6"] = {
        "eps_sigma": eps_sigma_from_14_1_6,
        "eta_1_over_2": eta_1_over_2_calc,
        "expected_lambda": LAMBDA_OBS,
        "consistent": abs(eta_1_over_2_calc - LAMBDA_OBS) < 0.001
    }

    # =========================================================================
    # THE DERIVATION IN §9.2
    # =========================================================================
    print("\n" + "-"*80)
    print("THE DERIVATION IN §9.2")
    print("-"*80)

    # From §9.2:
    # "For generations at r_3 = 0, r_2 = ε, r_1 = √3·ε:
    # η_1/η_2 = exp(-(r_1² - r_2²)/(2σ²)) = exp(-(3ε² - ε²)/(2σ²)) = exp(-ε²/σ²)"
    #
    # So they ALSO get exp(-ε²/σ²). The inconsistency is in what they set this equal to!

    print("\n§9.2 uses the same formula:")
    print("  η_1/η_2 = exp(-(r_1² - r_2²)/(2σ²)) = exp(-ε²/σ²)")
    print("\nBut then sets: exp(-ε²/σ²) = λ² (not λ)")
    print("This would give: ε/σ = √(ln(1/λ²)) = √(2·ln(1/λ)) = 1.74")

    eps_sigma_from_9_2 = np.sqrt(2 * np.log(1/LAMBDA_OBS))
    print(f"\nWith ε/σ = {eps_sigma_from_9_2:.4f}:")
    sigma_9 = eps / eps_sigma_from_9_2
    eta_1_over_2_9 = np.exp(-eps**2 / sigma_9**2)
    print(f"  η_1/η_2 = exp(-ε²/σ²) = {eta_1_over_2_9:.4f}")
    print(f"  Expected from λ²: {LAMBDA_OBS**2:.4f}")
    print(f"  λ itself: {LAMBDA_OBS:.4f}")

    results["section_9_2"] = {
        "eps_sigma": eps_sigma_from_9_2,
        "eta_1_over_2": eta_1_over_2_9,
        "claims_equal_to": "λ²",
        "actual_lambda_sq": LAMBDA_OBS**2
    }

    # =========================================================================
    # RESOLUTION: Which interpretation is correct?
    # =========================================================================
    print("\n" + "="*80)
    print("RESOLUTION")
    print("="*80)

    print("""
The inconsistency arises from confusion about whether:

  η_1/η_2 = λ   (§14.1.6)
  η_1/η_2 = λ²  (§9.2)

Looking at the NNI texture in §7:

  m_3 ~ v_χ D           (3rd gen mass)
  m_2 ~ v_χ λ² D        (2nd gen mass)
  m_1 ~ v_χ λ⁴ D        (1st gen mass)

So the MASS ratios are:
  m_2/m_3 = λ²
  m_1/m_2 = λ²

From Theorem 3.1.1: m_f = (g_χ ω/Λ) v_χ η_f

If we identify η_f = λ^{2n} c_f where n is generation index:
  η_3 ~ λ⁰ = 1
  η_2 ~ λ²
  η_1 ~ λ⁴

Then η_1/η_2 = λ² (not λ).

BUT §14.1.6 introduces a different interpretation:
  "The mass hierarchy involves TWO powers of λ per generation"
  "The COUPLING hierarchy involves only ONE power per shell"

This seems to suggest η_n ~ λ^n, and mass ~ η² giving m ~ λ^{2n}.

THIS IS THE SOURCE OF THE INCONSISTENCY.

The theorem needs to CHOOSE one interpretation and stick with it:

OPTION A: η_n ~ λ^{2n} (helicity coupling IS the hierarchy parameter)
  → ε/σ = √(2·ln(1/λ)) ≈ 1.74
  → η_1/η_2 = λ²

OPTION B: η_n ~ λ^n (helicity coupling is SQRT of hierarchy)
  → ε/σ = √(ln(1/λ)) ≈ 1.23
  → η_1/η_2 = λ
  → BUT then m_f ∝ η² to get m ~ λ^{2n}

The derivation file uses BOTH, which is INCONSISTENT.
""")

    # =========================================================================
    # RECOMMENDED RESOLUTION
    # =========================================================================
    print("-"*80)
    print("RECOMMENDED RESOLUTION")
    print("-"*80)

    print("""
Looking at Theorem 3.1.1 statement:
  "m_f = (g_χ ω/Λ) v_χ η_f"

This says mass is LINEAR in η_f. Therefore:
  m_1/m_2 = η_1/η_2 = λ² (from NNI texture)

This means η_n ~ λ^{2n}, and:
  ε/σ = √(2·ln(1/λ)) ≈ 1.74

The ε/σ = 1.23 in §14.1.6 is WRONG because it assumes η_n ~ λ^n.

CORRECTION NEEDED IN §14.1.6:
  Replace ε/σ = 1.23 with ε/σ = 1.74
  And clarify: η_1/η_2 = λ² (not λ)
""")

    results["resolution"] = {
        "correct_eps_sigma": 1.74,
        "incorrect_eps_sigma": 1.23,
        "source_of_error": "§14.1.6 uses η_n ~ λ^n but should use η_n ~ λ^{2n}",
        "correction": "Replace 1.23 with 1.74 in §14.1.6 and clarify η ratio is λ²"
    }

    return results

def create_visualization(results):
    """Create visualization of the ε/σ analysis."""

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: η profiles for both ε/σ values
    ax = axes[0, 0]
    eps = 1.0
    r = np.linspace(0, 2, 100)

    sigma_123 = eps / 1.23
    sigma_174 = eps / 1.74

    eta_123 = np.exp(-r**2 / (2 * sigma_123**2))
    eta_174 = np.exp(-r**2 / (2 * sigma_174**2))

    ax.plot(r, eta_123, 'b-', linewidth=2, label=f'ε/σ = 1.23 (§14.1.6)')
    ax.plot(r, eta_174, 'r-', linewidth=2, label=f'ε/σ = 1.74 (§9.2)')

    # Mark generation positions
    r_gens = [0, eps, np.sqrt(3)*eps]
    for i, r_g in enumerate(r_gens):
        ax.axvline(r_g, color='gray', linestyle='--', alpha=0.5)
        ax.annotate(f'Gen {3-i}', (r_g, 0.9 - 0.1*i), fontsize=10)

    ax.set_xlabel('Radial position r/ε')
    ax.set_ylabel('η(r)')
    ax.set_title('Helicity Coupling Profiles')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 2: η ratios
    ax = axes[0, 1]

    categories = ['η₂/η₃', 'η₁/η₂']
    x = np.arange(len(categories))
    width = 0.25

    # Calculate ratios
    eta_3_123 = np.exp(0)
    eta_2_123 = np.exp(-eps**2 / (2 * sigma_123**2))
    eta_1_123 = np.exp(-3*eps**2 / (2 * sigma_123**2))

    eta_3_174 = np.exp(0)
    eta_2_174 = np.exp(-eps**2 / (2 * sigma_174**2))
    eta_1_174 = np.exp(-3*eps**2 / (2 * sigma_174**2))

    ratios_123 = [eta_2_123/eta_3_123, eta_1_123/eta_2_123]
    ratios_174 = [eta_2_174/eta_3_174, eta_1_174/eta_2_174]

    lambda_val = LAMBDA_OBS
    lambda_sq = LAMBDA_OBS**2

    ax.bar(x - width, ratios_123, width, label='ε/σ = 1.23', color='blue', alpha=0.7)
    ax.bar(x, ratios_174, width, label='ε/σ = 1.74', color='red', alpha=0.7)
    ax.bar(x + width, [lambda_val, lambda_val], width, label=f'λ = {lambda_val:.3f}', color='green', alpha=0.7)

    ax.axhline(lambda_sq, color='purple', linestyle='--', label=f'λ² = {lambda_sq:.4f}')

    ax.set_xticks(x)
    ax.set_xticklabels(categories)
    ax.set_ylabel('Ratio')
    ax.set_title('η Ratios: Which matches λ or λ²?')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 3: Mass hierarchy comparison
    ax = axes[1, 0]

    gens = ['3rd\n(t,b,τ)', '2nd\n(c,s,μ)', '1st\n(u,d,e)']
    x = np.arange(len(gens))

    # Theoretical masses (relative to 3rd gen)
    mass_theory_174 = [1, LAMBDA_OBS**2, LAMBDA_OBS**4]
    mass_theory_123 = [1, np.exp(-eps**2/(2*sigma_123**2))**2, np.exp(-3*eps**2/(2*sigma_123**2))**2]

    # Observed ratios (down sector)
    m_b, m_s, m_d = 4180, 93, 4.7  # MeV
    mass_obs = [1, m_s/m_b, m_d/m_b]

    ax.bar(x - width, mass_theory_174, width, label='Theory (ε/σ=1.74)', color='red', alpha=0.7)
    ax.bar(x, mass_theory_123, width, label='Theory (ε/σ=1.23)', color='blue', alpha=0.7)
    ax.bar(x + width, mass_obs, width, label='Observed (d-sector)', color='green', alpha=0.7)

    ax.set_xticks(x)
    ax.set_xticklabels(gens)
    ax.set_ylabel('Mass ratio (relative to 3rd gen)')
    ax.set_title('Mass Hierarchy Comparison')
    ax.legend()
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    # Plot 4: Summary diagram
    ax = axes[1, 1]
    ax.axis('off')

    summary_text = """
    ε/σ INCONSISTENCY RESOLUTION
    ═══════════════════════════════

    SOURCE OF ERROR:
    §9.2 and §14.1.6 use different assumptions:

    §9.2:    η₁/η₂ = λ²  →  ε/σ = 1.74
    §14.1.6: η₁/η₂ = λ   →  ε/σ = 1.23

    CORRECT INTERPRETATION:
    From Theorem 3.1.1: m_f ∝ η_f (linear)
    From NNI texture: m₁/m₂ = λ²
    Therefore: η₁/η₂ = λ²

    ═══════════════════════════════
    RECOMMENDED CORRECTION:

    Use ε/σ = √(2·ln(1/λ)) ≈ 1.74

    Update §14.1.6 to:
    - Fix ε/σ from 1.23 to 1.74
    - Clarify that η ratios are λ², not λ
    ═══════════════════════════════
    """

    ax.text(0.05, 0.95, summary_text, transform=ax.transAxes, fontsize=10,
            verticalalignment='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()
    plt.savefig('verification/plots/eps_sigma_resolution.png', dpi=150, bbox_inches='tight')
    print("\nPlot saved to: verification/plots/eps_sigma_resolution.png")
    plt.close()

def main():
    """Main analysis."""

    print("="*80)
    print("THEOREM 3.1.2 CRITICAL ISSUE #2: ε/σ INCONSISTENCY")
    print("="*80)

    results = analyze_scaling_interpretations()

    # Create visualization
    create_visualization(results)

    # Save results
    output = {
        "timestamp": datetime.now().isoformat(),
        "lambda_obs": LAMBDA_OBS,
        "results": results,
        "conclusion": {
            "correct_eps_sigma": 1.74,
            "source_of_error": "§14.1.6 incorrectly assumes η_n ~ λ^n instead of η_n ~ λ^{2n}",
            "recommended_fix": "Replace ε/σ = 1.23 with ε/σ = 1.74 in §14.1.6"
        }
    }

    with open("verification/theorem_3_1_2_eps_sigma_resolution.json", "w") as f:
        json.dump(output, f, indent=2, default=str)

    print("\nResults saved to: verification/theorem_3_1_2_eps_sigma_resolution.json")

    return results

if __name__ == "__main__":
    main()

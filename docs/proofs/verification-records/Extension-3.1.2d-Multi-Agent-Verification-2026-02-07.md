# Extension 3.1.2d: Complete PMNS Parameter Derivation
# Multi-Agent Adversarial Verification Report

**Date:** 2026-02-07
**Document:** `docs/proofs/Phase3/Extension-3.1.2d-Complete-PMNS-Parameters.md`
**Verification Agents:** Mathematics, Physics, Literature (all adversarial)
**Overall Verdict:** NOT VERIFIED — Multiple critical issues identified

---

## Executive Summary

| Agent | Verdict | Confidence | Critical Issues | Moderate Issues | Warnings |
|-------|---------|------------|-----------------|-----------------|----------|
| **Mathematics** | NOT VERIFIED | High | 3 | 4 | 8 |
| **Physics** | NOT VERIFIED | Low | 4 | 2 | 6 |
| **Literature** | PARTIAL | Medium | 3 | 2 | 5 |

**Consensus:** All three agents independently identified the same fundamental problems:
1. Trial-and-error fitting presented as derivation (16+ failed formulas visible)
2. Incorrect/outdated experimental reference values (NuFIT 5.x labeled as 6.0)
3. Dimensional inconsistency in the θ₁₂ formula
4. Internal contradiction in the δ_CP formula (Section 8.6)
5. A₄ generator presentation error (S³=T²=(ST)³=1 should be S²=T³=(ST)³=1)

---

## 1. Critical Issues (Cross-Agent Consensus)

### Issue 1: Trial-and-Error Fitting, Not Derivation

**Flagged by:** All three agents

The document tries and discards multiple formulas before finding ones that match data:

| Parameter | Failed Formulas | "Successful" Formula | Character |
|-----------|----------------|---------------------|-----------|
| θ₁₂ | 6 (§5.4–5.8) | §5.9: 45° − arcsin(λ) + λ²/2 | QLC + fitted correction |
| δ_CP | 7 (§8.3–8.5) | §8.5: 150° + (λ/φ)×360° | A₄ phase + ad hoc correction |
| Δm²₃₁ | 2 (§9.5) | §9.7: ratio only (λ²/√3) | Stated without derivation |

**Total: 16+ failed formulas before 3 selected.** Phrases like "Wait," "Let's reconsider," "Still not quite right," "too large" appear throughout. This is post-hoc fitting, not first-principles derivation.

**Recommendation:** Either (a) present only the final formulas with rigorous derivation from A₄ representation theory, or (b) relabel the document as "Analysis/Exploration" rather than "Derivation."

### Issue 2: NuFIT 6.0 Values Are Incorrect

**Flagged by:** Physics agent, Literature agent

The document claims to use NuFIT 6.0 but the values match NuFIT 5.x:

| Parameter | Document (claims NuFIT 6.0) | NuFIT 6.0 IC19 (NO) | NuFIT 6.0 IC24 (NO) |
|-----------|---------------------------|---------------------|---------------------|
| sin²θ₁₂ | **0.303** | 0.307 ± 0.012 | 0.308 ± 0.012 |
| sin²θ₂₃ | **0.573** | 0.561 ± 0.014 | 0.470 ± 0.015 |
| δ_CP | **197°** | **177° ± 20°** | **212° ± 34°** |
| Δm²₂₁ | **7.42 × 10⁻⁵** | 7.49 × 10⁻⁵ | 7.49 × 10⁻⁵ |

**Impact:** The claimed "<0.1σ" agreement for θ₁₂ becomes ~0.4σ with correct values. The δ_CP agreement changes from "0.1σ" to 1.2σ (vs IC19) or 0.4σ (vs IC24). The sin²θ₁₂ = 0.303 "0.0% deviation" becomes ~1.3% deviation.

### Issue 3: Dimensional Inconsistency in θ₁₂ Formula

**Flagged by:** Mathematics agent

The boxed formula (line 332):
$$\theta_{12}^{PMNS} = 45° - \arcsin(\lambda) + \frac{\lambda^2}{2}$$

mixes degrees (first two terms) with radians (third term). The λ²/2 = 0.0252 must be in radians (= 1.44°) for the formula to work, but the written formula omits the ×180°/π conversion.

**Correct form:** θ₁₂ = π/4 − arcsin(λ) + λ²/2 (all in radians), or θ₁₂ = 45° − arcsin(λ) + (λ²/2)×(180°/π) (all in degrees).

### Issue 4: Algebraic Error in δ_CP Formula (Section 8.6)

**Flagged by:** Mathematics agent, Physics agent

Line 512 claims:
$$\delta_{CP} = 150° + \frac{\lambda}{\varphi} \times 360° = 150° + \frac{360°}{\varphi^4}$$

But λ/φ × 360° = 49.95° while 360°/φ⁴ = 52.52°. These differ by **2.57°** because λ = sin(72°)/φ³ ≠ 1/φ³. The two expressions are NOT equal.

### Issue 5: A₄ Generator Presentation Error

**Flagged by:** Physics agent, Literature agent

The document states (line 494): "S³ = T² = (ST)³ = 1"

The standard A₄ presentation is **S² = T³ = (ST)³ = 1** (von Dyck type (2,3,3)). The orders of S and T are swapped compared to the conventions used in the cited references (Altarelli-Feruglio 2010, King-Luhn 2013).

---

## 2. Moderate Issues

### Issue 6: Jarlskog Invariant Comparison Error

**Flagged by:** All three agents

The document computes J_PMNS = −0.011 then compares to "observed |J| ≈ 0.033." But |J| = 0.033 is J_max (mixing-angle dependent only), not J_observed. The actual J for δ_CP = 197° is ≈ −0.010, and for the NuFIT 6.0 best-fit δ_CP = 177° (NO), J ≈ +0.002.

The predicted J = −0.011 is actually in reasonable agreement with J(δ_CP = 197°), but the comparison in the document is invalid.

### Issue 7: θ₁₂ Does Not Recover TBM in λ → 0 Limit

**Flagged by:** Physics agent

If λ → 0 (A₄ exact, no breaking), the QLC formula gives θ₁₂ → 45°, NOT the TBM value of 35.26°. This proves the θ₁₂ formula is based on QLC, not A₄ symmetry.

### Issue 8: A₄ Majorana Matrix Has Zero Eigenvalue

**Flagged by:** Mathematics agent

The A₄-invariant M_R has eigenvalues (3M₀, 3M₀, 0). The seesaw requires M_R⁻¹, which diverges. Breaking parameters ε, ε' are introduced but not derived — they are free parameters.

### Issue 9: Section 9.6 Circular Reasoning

**Flagged by:** Mathematics agent

The "Direct Derivation from Holographic Bound" uses hand-picked neutrino masses (m₁ = 0.005, m₂ = 0.010, m₃ = 0.051 eV) that happen to reproduce observed mass differences. The holographic bound only constrains the sum, not individual masses.

### Issue 10: Numerical Error in Section 5.4

**Flagged by:** Mathematics agent

The boxed formula claims δθ₁₂ ≈ 1.50° but the derivation computes 0.83° — a factor-of-2 internal inconsistency.

### Issue 11: Golden Ratio in A₄ Context

**Flagged by:** Literature agent

The golden ratio φ is naturally associated with A₅ (icosahedral symmetry), not A₄ (tetrahedral). Papers by Everett & Stuart (2009) connect φ to neutrino mixing through A₅. The document does not justify why φ appears in an A₄ framework.

---

## 3. Warnings

1. θ₁₂ derivation depends on empirical QLC relation, not pure geometry
2. λ²/2 correction in θ₁₂ has no physical derivation
3. The 150° base phase for δ_CP is weakly justified
4. The (λ/φ)×360° electroweak correction for δ_CP has no derivation
5. Mass ratio formula r = λ²/√3 is stated without derivation
6. Perturbative expansion in λ ≈ 0.22 has limited convergence
7. NuFIT 6.0 (NO, IC19) shows δ_CP consistent with CP conservation within 1σ
8. DESI DR2 (2025) gives Σm_ν < 0.053 eV, potentially tensioning with the prediction of 0.064 eV

---

## 4. Parameter Count Analysis (Physics Agent)

| Category | Count | Items |
|----------|-------|-------|
| **Measured inputs** | 2 | λ = 0.2245, Δm²₃₁ (for ratio) |
| **Mathematical constants** | 1 | φ = (1+√5)/2 |
| **Structural choices** | 5–7 | QLC starting point (45°), 150° base phase, 360° factor, correction coefficients in θ₁₃, formula forms |
| **Outputs** | 5 | θ₁₂, θ₂₃, θ₁₃, δ_CP, r |

Structural choices ≥ outputs → fitting, not prediction.

---

## 5. What Is Correct

Despite the critical issues, the following are verified correct:

- PMNS matrix parameterization and Jarlskog formula (§3)
- Tribimaximal mixing values from A₄ (§4.2)
- A₄ representation content (1, 1', 1'', 3)
- Seesaw mechanism application (order of magnitude)
- Self-consistency with M_R = 2.2 × 10¹⁰ GeV (§10.4)
- DESI DR1 bound: Σm_ν < 0.072 eV (correct for 2024)
- All external paper citations check out (HPS, Altarelli-Feruglio, King-Luhn, Raidal)
- The verification script faithfully implements the intended formulas

---

## 6. Missing References (Literature Agent)

1. Ma (2001) — Foundational A₄ paper for neutrino mixing
2. Everett & Stuart (2009) — Golden ratio in A₅ models
3. Branco et al. (2013) — Geometric CP violation with Δ(27)
4. T2K+NOvA joint analysis (2025, Nature) — Latest δ_CP constraints
5. DESI DR2 (2025) — Updated Σm_ν < 0.0642 eV
6. NuFIT 6.0 (arXiv:2410.05380) — Should be cited with full author list

---

## 7. Recommendations

### Priority 1: Fix Errors
1. Fix θ₁₂ formula dimensional consistency (add ×180°/π or write in radians)
2. Fix δ_CP formula: remove false equality λ/φ × 360° = 360°/φ⁴
3. Fix A₄ generator presentation: S² = T³ = (ST)³ = 1
4. Fix Jarlskog comparison: use J(δ_CP), not J_max
5. Fix numerical error in §5.4 boxed formula (1.50° should be 0.83°)
6. Update ALL experimental values to actual NuFIT 6.0 published values

### Priority 2: Improve Rigor
7. Remove trial-and-error sections or label as "Exploration"
8. Derive the key formulas (λ²/2 correction, 150° base, λ/φ×360°, λ²/√3) from A₄ representation theory
9. Address the λ → 0 TBM recovery failure for θ₁₂
10. Derive the A₄ breaking parameters ε, ε' rather than treating them as free

### Priority 3: Context
11. Add parameter count table showing inputs vs outputs
12. Compare with existing A₄ models from the literature
13. Explain golden ratio presence in A₄ (not A₅) framework
14. Cite missing references (Ma 2001, Everett & Stuart 2009, T2K+NOvA 2025, DESI DR2)
15. Distinguish genuine predictions from semi-predictions and consistency checks

---

## 8. Independent Calculation Summary (Mathematics Agent)

| Quantity | Agent Calculation | Proof Claim | Match? |
|----------|------------------|-------------|--------|
| λ = sin(72°)/φ³ | 0.22451 | 0.2245 | ✅ |
| θ₁₂ (with unit fix) | 33.470° | 33.4° | ✅ |
| sin²θ₁₂ (§5.7) | 0.2888 | 0.289 | ✅ |
| δ_CP = 150 + λ/φ×360 | 199.95° | 200° | ✅ |
| 360/φ⁴ | 52.52° | equated to 49.95° | **❌** |
| r = λ²/√3 | 0.02910 | 0.029 | ✅ |
| Δm²₂₁ from ratio | 7.314 × 10⁻⁵ eV² | 7.31 × 10⁻⁵ | ✅ |
| J_PMNS (predicted) | −0.01131 | −0.011 | ✅ |
| J_PMNS (observed) | −0.00966 | claimed 0.033 | **❌** |
| §5.4 δθ | 0.824° | boxed as 1.50° | **❌** |

---

## Appendix: Verification Files

- **Mathematics report:** `/tmp/math_verification_ext_3_1_2d.md`
- **Physics report:** `/tmp/physics_verification_ext_3_1_2d.md`
- **Literature report:** `/tmp/literature_verification_ext_3_1_2d.md`
- **Adversarial verification script:** `verification/Phase3/extension_3_1_2d_adversarial_physics.py`

---

*Report compiled: 2026-02-07*
*Verification methodology: Multi-agent adversarial review (3 independent agents)*
*Status: NOT VERIFIED — Requires significant revision before peer review*

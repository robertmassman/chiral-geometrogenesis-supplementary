# Multi-Agent Verification Report: Proposition 4.3.5 (Re-Review)

## Skyrme Parameter First-Principles Derivation

**Date:** 2026-02-25 (re-review)
**Target:** `docs/proofs/Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md`
**Agents:** Mathematical (adversarial), Physics (adversarial), Literature (reference verification)
**Overall Verdict:** Partial — analytical machinery verified correct; foundational derivation has significant gaps
**Prior Review:** Initial review (2026-02-25) found 15 issues; all 15 marked resolved in a complete rewrite. This re-review examines the rewritten version.

---

## Executive Summary

Three independent verification agents reviewed the revised Proposition 4.3.5. The **analytical content** — cap integrals, kurtosis formula, Monte Carlo verification, numerical tables, limiting cases, dimensional analysis — is mathematically correct and internally self-consistent. All algebra was independently re-derived. However, **foundational physics claims** that make this a "first-principles derivation" rather than a geometric parameterization have significant remaining gaps. Fifteen issues were identified across three severity levels.

| Agent | Verdict | Confidence | Key Finding |
|-------|---------|------------|-------------|
| Mathematical | Partial | Medium | All algebra verified; e₀ = 1 unjustified; error budget internally inconsistent |
| Physics | Partial | Medium-Low | All limiting cases pass; ε̃ = 0.130 inconsistent with physical ε = 0.50 from Def 0.1.3 |
| Literature | Partial | Medium-High | All numerical values correct; two prior first-principles derivations not cited |

---

## Issue Tracker

| # | Severity | Agent(s) | Section | Issue | Status |
|---|----------|----------|---------|-------|--------|
| 1 | **CRITICAL** | Math+Phys | §3.4 | e₀ = 1 assumption unjustified | RESOLVED — Reframed as explicit Assumption A-e0 (normalization convention) |
| 2 | **CRITICAL** | Physics | §3.5, §5.1 | ε̃ = 0.130 inconsistent with physical ε = 0.50 (Def 0.1.3) | RESOLVED — New §3.5 explains ε̃ vs ε distinction (angular resolution vs core size); honest assessment added |
| 3 | **CRITICAL** | Math+Phys | §5.1, §5.4 | Error budget understates regularization uncertainty (±15% claimed vs ±24% actual) | RESOLVED — Corrected to +29%/−18% (sym. ±24%); total ±27%; e_W = 4.5 ± 1.2 |
| 4 | **CRITICAL** | Math+Phys | §3.3 | P_W⁴ weighting of Skyrme term assumed, not derived | RESOLVED — Flagged as explicit Assumption A-PW4 with physical motivation |
| 5 | **CRITICAL** | Physics | §3.3 | Matching procedure normalization ambiguity | RESOLVED — Added "Normalization logic" paragraph explaining I₂²/Ω_W factor |
| 6 | **CRITICAL** | Literature | §2.2, §8 | Missing prior first-principles derivations (Espriu & de Rafael 1986; Sakai & Sugimoto 2005) | RESOLVED — Both cited and discussed in §2.2 and §8 |
| 7 | MODERATE | Math | §4.6 | Intermediate c = 0.01678 should be c = 0.01703 | RESOLVED — Corrected to c = 0.01703 |
| 8 | MODERATE | Literature | §6.3, §8 | Gudnason & Halcrow (2022) description inaccurate | RESOLVED — Corrected to "standard Skyrme model (E₂+E₄+E₀)" |
| 9 | MODERATE | Literature | §2.2 | ANW range [4.25, 5.45] conflates 1983 and 1984 papers | RESOLVED — Split attribution: ANW 1983 (e=4.25) and Adkins-Nappi 1984 (e=5.45) |
| 10 | MODERATE | Physics | §4.1 | Circumscribed cap solid angle: claims 3.86 sr, actual 4.19 sr | RESOLVED — Corrected to 4π/3 = 4.19 sr |
| 11 | MODERATE | Math+Phys | Title, §1, §7 | "First-principles" designation overstated | RESOLVED — Renamed to "Geometric Determination"; all language softened |
| 12 | MODERATE | Phys+Lit | §2.1, §6.5 | ANW coefficient 72.92 should be 72.96 | RESOLVED — All instances corrected to 72.96 |
| 13 | Minor | Math | Symbol Table | Vertex x̂_W = (1,1,1)/√3 inconsistent with Def 0.1.3 | RESOLVED — Changed to (−1,−1,1)/√3 with tetrahedral symmetry note |
| 14 | Minor | Literature | §2.2 | Lattice QCD claim could note indirect constraints from LECs | RESOLVED — Added note about lattice O(p⁴) LEC constraints |
| 15 | Minor | Literature | §6.3 | Convention note oversimplifies the landscape | RESOLVED — Expanded to cover 3 common convention variants |

---

## Detailed Issue Descriptions

### CRITICAL Issues (6)

**Issue 1: e₀ = 1 assumption unjustified** [Math + Physics]
- **Location:** §3.4 (line 155)
- **Description:** The claim "the unique self-consistent choice is e₀ = 1" is asserted without proof. Direct matching of the microscopic action (§3.3) with the standard Skyrme Lagrangian requires e₀² = I₂²/Ω_W ≈ 10,637, not unity. In standard ChPT, the Skyrme parameter is a Wilson coefficient with no reason to be unity at any scale.
- **Impact:** The boxed kurtosis formula is well-defined and dimensionally correct, but it is a geometrically-motivated definition rather than a first-principles derivation without this assumption.
- **Resolution options:** (a) Derive e₀ = 1 from a self-consistency condition, (b) explicitly state it as a normalization convention, or (c) reformulate to avoid e₀.

**Issue 2: ε̃ = 0.130 inconsistent with physical ε = 0.50** [Physics]
- **Location:** §3.5 (line 175), §5.1 (line 310)
- **Description:** Definition 0.1.3 §10.1 derives the physical regularization parameter as ε = 0.50 (from flux tube penetration depth). Proposition 4.3.5 states "ε̃² = ε² in units where R = 1" then uses ε̃ = 0.130. If ε̃ = ε = 0.50, then e_W = 1.44 — far below the QCD range. The central value is calibrated to match QCD, undermining the "first-principles" claim.
- **Impact:** The regularization is fit, not predicted.
- **Resolution options:** (a) Explain why the effective ε̃ differs from the physical ε (different angular scales, RG running), (b) derive ε̃ = 0.130 independently, or (c) reframe as a consistency check.

**Issue 3: Error budget understates regularization uncertainty** [Math + Physics]
- **Location:** §5.1, §5.4
- **Description:** Claims ±15% for ε̃ ∈ [0.10, 0.16]. Actual variation: e_W ranges from 3.70 to 5.83 over this range — a ±24% variation (asymmetric: +29%/−18% about central 4.52). The linearized δe_W/e_W ≈ δε̃/ε̃ is inadequate. Quadrature total should be ~27%, not 20%.
- **Impact:** Final ±22% partially compensates through rounding, but internal consistency is poor.
- **Resolution:** Recalculate with actual variation, or narrow ε̃ range, or use asymmetric errors.

**Issue 4: P_W⁴ weighting of Skyrme term assumed, not derived** [Math + Physics]
- **Location:** §3.3, lines 133–135
- **Description:** Claims "each power of L_μ carries the local amplitude factor P_W." However, L_μ = U⁻¹∂_μU depends on gradients of U, not amplitude. For the zero-mode U(x) independent of angular position, L_μ carries no P_W factor. A Kaluza-Klein-style reduction would be needed.
- **Impact:** Physically plausible but should be flagged as an explicit assumption.
- **Resolution:** Provide rigorous KK-style derivation or explicitly flag as an assumption.

**Issue 5: Matching procedure normalization ambiguity** [Physics]
- **Location:** §3.3, line 145
- **Description:** The formula for 1/e_W² contains normalization factor (∫P²dΩ)²/Ω_W described as "normalized v_W² by the angular average." This conversion from naive matching to kurtosis is not independently justified.
- **Impact:** Unexplained factor in the derivation chain.
- **Resolution:** Provide explicit physical justification.

**Issue 6: Missing prior first-principles derivations** [Literature]
- **Location:** §2.2, §8
- **Description:** Two prior first-principles derivations are not cited:
  - **Espriu & de Rafael (1986):** Derived Skyrme coefficient from NJL bosonization. *Nucl. Phys. B* 274, 399–428.
  - **Sakai & Sugimoto (2005):** Holographic QCD derivation giving e ∼ 7.3. arXiv:hep-th/0412141, *Prog. Theor. Phys.* 113, 843–882.
- **Impact:** The implicit claim of novelty ("No first-principles derivation exists") is incorrect.
- **Resolution:** Cite and discuss in §2.2 and §8.

---

### MODERATE Issues (6)

**Issue 7: Numerical error in §4.6 Step 2** [Math]
- **Location:** §4.6, line 280
- **Description:** States c = 0.01678 but correct solution of c(1+c) = 0.01732 is c = 0.01703. Also √0.01678 = 0.1295, not 0.1305. Final answer ε̃ = 0.1305 is correct.
- **Resolution:** Replace c = 0.01678 with c = 0.01703.

**Issue 8: Gudnason & Halcrow (2022) description inaccurate** [Literature]
- **Location:** §6.3, §8
- **Description:** The "Smorgasbord" paper (arXiv:2202.01792) studies the standard Skyrme model, not a "Generalized Skyrme with sextic term." The range e ∈ [4.0, 5.0] cannot be confirmed from this paper.
- **Resolution:** Correct description or cite a different paper.

**Issue 9: ANW range conflates 1983 and 1984 papers** [Literature]
- **Location:** §2.2
- **Description:** Attributes e_π ∈ [4.25, 5.45] to ANW (1983). The upper value 5.45 comes from Adkins & Nappi (1984) with massive pions.
- **Resolution:** Clarify the range spans both papers.

**Issue 10: Circumscribed cap solid angle error** [Physics]
- **Location:** §4.1, line 199
- **Description:** States Ω_circ = 3.86 sr for θ_max = 70.53°. Correct: 2π(1 − cos 70.53°) = 4π/3 = 4.19 sr.
- **Resolution:** Correct to 4.19 sr.

**Issue 11: "First-principles" designation overstated** [Math + Physics]
- **Location:** Title, §1, §7
- **Description:** Since ε̃ is calibrated and e₀ = 1 is assumed, "geometric parameterization" or "pressure-kurtosis determination" is more accurate.
- **Resolution:** Soften language.

**Issue 12: ANW coefficient 72.92 → 72.96** [Physics + Literature]
- **Location:** §2.1, §6.5
- **Description:** Standard ANW factor is 1.232; 1.232 × 6π² = 72.96, not 72.92. Difference 0.05%.
- **Resolution:** Correct to 72.96.

---

### MINOR Issues (3)

**Issue 13: Vertex assignment inconsistency** [Math]
- **Location:** Symbol Table (line 58)
- **Description:** Uses x̂_W = (1,1,1)/√3; Definition 0.1.3 uses x̂_W = (−1,−1,1)/√3. By tetrahedral symmetry, kurtosis is identical.
- **Resolution:** Use consistent labels or add a note.

**Issue 14: Lattice QCD claim could be more nuanced** [Literature]
- **Location:** §2.2
- **Description:** Lattice QCD has constrained O(p⁴) LECs (L₁, L₂) which indirectly constrain the Skyrme coefficient.
- **Resolution:** Add a note about indirect constraints.

**Issue 15: Convention note oversimplified** [Literature]
- **Location:** §6.3
- **Description:** Multiple normalization conventions exist beyond just the factor-of-2 rescaling noted.
- **Resolution:** Expand or reference detailed comparison.

---

## Verified Content (Confirmed Correct by All Agents)

### Algebraic Content (Mathematical Agent — all independently re-derived)

| Item | Section | Status |
|------|---------|--------|
| Second moment: ∫P_W² dΩ = π/(c(1+c)) | §4.3 | ✅ Verified analytically + numerically |
| Fourth moment: ∫P_W⁴ dΩ = (π/3)(1/c³ − 1/(1+c)³) | §4.3 | ✅ Verified analytically + numerically |
| Expansion: (1+c)³ − c³ = 1 + 3c + 3c² | §4.3 | ✅ Algebraic identity |
| Factorization: 1 + 3c + 3c² = 1 + 3c(1+c) | §4.3 | ✅ Confirmed |
| Kurtosis formula: e_W² = 1 + 1/(3ε̃²(1+ε̃²)) | §4.3 | ✅ Matches numerical computation |
| Equal-area cap: cos θ₀ = 1/2 → θ₀ = 60° | §4.2 | ✅ 2π(1−cos60°) = π |
| Solid angle: Ω_W = π sr | §4.1 | ✅ MC: 3.1413 ± 0.001 |
| Numerical table (all 9 rows) | §4.6 | ✅ Within rounding tolerance |
| M_FB = 6π²·123/4.5 = 1619 GeV | §6.5 | ✅ Verified |
| M_ANW = 72.92·123/4.5 = 1993 GeV | §6.5 | ✅ Verified |
| Derrick virial E₂ = E₄ | §2.1 | ✅ Standard result |
| Dimensional analysis: kurtosis dimensionless | §3.4, §6.1 | ✅ Verified |
| Domain sweep (4 domains) | §6.4 | ✅ All values match |
| Cap vs Voronoi MC: < 0.3% agreement | §4.5 | ✅ Confirmed independently |

### Limiting Cases (Physics Agent)

| Limit | Expected | Computed | Status |
|-------|----------|----------|--------|
| ε̃ → 0 (sharp vertex) | e_W → ∞ | e_W ∼ 1/(√3 ε̃) → ∞ | ✅ PASS |
| ε̃ → ∞ (uniform) | e_W → 1 | e_W² → 1 | ✅ PASS |
| Uniform pressure | Kurtosis = 1 | Confirmed | ✅ PASS |
| Monotonicity in ε̃ | Decreasing | de_W/dε̃ < 0 | ✅ PASS |
| Hemisphere → larger e_W | Yes | 6.33 > 4.52 | ✅ PASS |
| Small cap → smaller e_W | Yes | 2.44 < 4.52 | ✅ PASS |

### Literature Values (Literature Agent)

| Value | Proposition | Verified | Status |
|-------|-------------|----------|--------|
| 6π² | 59.22 | 59.2176 | ✅ Correct |
| v_W | 123 GeV | 123 ± 15 GeV (Def 4.3.1) | ✅ Correct |
| Skyrme (1961) | Proc. R. Soc. A 260, 127 | Confirmed | ✅ Correct |
| ANW (1983) | Nucl. Phys. B 228, 552 | Confirmed | ✅ Correct |
| Adkins & Nappi (1984) | Nucl. Phys. B 233, 109 | Confirmed | ✅ Correct |
| Holzwarth & Schwesinger (1986) | Rep. Prog. Phys. 49, 825 | Confirmed | ✅ Correct |
| Battye et al. (2005) | hep-th/0507279 | Confirmed | ✅ Correct |
| Naya & Sutcliffe (2018) | arXiv:1811.02064 | Confirmed | ✅ Correct |
| Gudnason & Halcrow (2022) | arXiv:2202.01792 | Confirmed (but description issue) | ⚠️ Issue 8 |
| Derrick virial relation | Standard | Confirmed from multiple sources | ✅ Correct |
| "No lattice QCD determination" | §2.2 | Correct (no direct extraction) | ✅ Correct |
| Pion mass shift ~+1 | §6.2 | Consistent (5.45 − 4.25 ≈ 1.2) | ✅ Plausible |
| Conventions (ANW f_π²/4) | §6.3 | Correct | ✅ Correct |

### Missing References Identified

| Reference | Relevance | Priority |
|-----------|-----------|----------|
| Espriu & de Rafael (1986), *Nucl. Phys. B* 274, 399 | NJL-derived Skyrme coefficient | HIGH |
| Sakai & Sugimoto (2005), arXiv:hep-th/0412141 | Holographic derivation: e ∼ 7.3 | HIGH |
| Gudnason & Halcrow (2024), arXiv:2405.05731 | Confirms hedgehog energy 1.232 × 12π² | MEDIUM |
| Weigel (2025), arXiv:2503.20534 | Most recent chiral soliton review | LOW |

---

## Recommendations (Priority Order)

### Must Fix
1. Resolve ε̃ vs physical ε inconsistency (Issue 2) — most impactful
2. Either derive or explicitly assume e₀ = 1 (Issue 1)
3. Recalculate error budget with correct regularization sensitivity (Issue 3)
4. Add missing prior first-principles derivations (Issue 6)

### Should Fix
5. Correct intermediate c value in §4.6 (Issue 7)
6. Fix Gudnason & Halcrow (2022) description (Issue 8)
7. Clarify ANW range across 1983/1984 papers (Issue 9)
8. Fix circumscribed cap solid angle 3.86 → 4.19 sr (Issue 10)
9. Consider softening "first-principles" language (Issue 11)
10. Fix ANW coefficient 72.92 → 72.96 (Issue 12)

### Optional
11. Reconcile vertex labels with Def 0.1.3 (Issue 13)
12. Add lattice QCD indirect constraint note (Issue 14)
13. Expand convention discussion (Issue 15)

---

## Framework Consistency Cross-References

| Dependency | Checked? | Consistent? | Notes |
|-----------|----------|-------------|-------|
| Definition 0.1.1 (Stella boundary) | Yes | Yes | Two interpenetrating tetrahedra, Ω_W = π |
| Definition 0.1.3 (Pressure functions) | Yes | **NO** | Physical ε = 0.50 vs used ε̃ = 0.130 (Issue 2) |
| Definition 0.1.4 (Color domains) | Yes | Yes | Voronoi cell, equal solid angles |
| Definition 4.3.1 (W-sector) | Yes | Yes | v_W = 123 GeV, φ_W = π |
| Theorem 3.0.1 (Superposition) | Yes | Yes | Pressure-modulated χ_ext form |
| Theorem 4.1.2 (Soliton mass) | Yes | Yes | M = 6π²f/e formula |
| Theorem 4.3.2 (W-soliton) | Yes | Yes | Skyrme Lagrangian, mass 1800 ± 500 GeV |

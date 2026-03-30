# Multi-Agent Verification Report: Proposition 0.0.3b

## Spontaneous Lattice Formation from Z₃ Fields

**Date:** 2026-03-27
**Proof File:** `docs/proofs/foundations/Proposition-0.0.3b-Spontaneous-Lattice-Formation-From-Z3-Fields.md`
**Verification Method:** Three independent adversarial agents (Mathematics, Physics, Literature) + adversarial Python script
**Adversarial Script:** `verification/adversarial_prop_0_0_3b_lattice_formation.py`

---

## Executive Summary

| Agent | Verdict | Confidence | Critical Issues |
|-------|---------|-----------|-----------------|
| **Mathematics** | Partial | Medium | 2 critical, 1 significant, 2 moderate |
| **Physics** | Partial | Medium | 1 significant, 1 minor |
| **Literature** | Partial | Medium | 1 critical, 1 significant |
| **Adversarial Script** | 30/31 PASS | — | 1 critical (same as agents) |

**Overall Verdict: PARTIAL — requires corrections before VERIFIED status**

**Consensus Critical Finding:** All three agents and the adversarial script independently identified the same critical error: **Section 5.1's cubic Fourier coupling argument has the FCC/BCC triangle count swapped**, contradicting Alexander & McTague (1978). The Z₃ stacking argument (§5.2) and A₂ root argument (§5.3) remain valid and independently select FCC.

---

## 1. Mathematics Agent Report

### Verdict: Partial | Confidence: Medium

### Errors Found

**ERROR 1 (CRITICAL): BCC reciprocal closed triangles claim is wrong (§5.1)**

The proof claims (line 198-199) that "BCC reciprocal = FCC: 0 (no closed triangles at k₀)." This contradicts the well-known Alexander-McTague (1978) result. The FCC reciprocal lattice vectors (⟨110⟩ family, 12 vectors) DO form closed triangles: e.g., (1,1,0) + (-1,0,1) + (0,-1,-1) = (0,0,0). Meanwhile, BCC reciprocal vectors (⟨111⟩ family, 8 vectors) CANNOT form closed triangles because each component sum of three ±1 values is always odd.

The proof's table in §5.1 has FCC and BCC rows **swapped** for the triangle count.

**ERROR 2 (SIGNIFICANT): κ_eff derivation has convergence issues (§2.3)**

The formula κ_eff = κ₀ − (α−β)/(4π) ∫₀^∞ dr r⁴ V″(r) is stated without derivation. If V(r) ~ 1/r² (from Prop 0.0.3a §2.1), then V″(r) ~ 6/r⁴, and the integral ∫₀^∞ dr r⁴ · (6/r⁴) = 6 · ∫₀^∞ dr **diverges**. The lower limit is not regulated.

**ERROR 3 (SIGNIFICANT): Z₃ transformation law of ψ is incorrect (§2.1)**

Line 66 claims: "Under a Z₃ transformation χ_c → ω^n χ_c, the order parameter transforms as ψ → ω^n ψ." But since ψ involves |χ_c|², which is invariant under phase rotation, ψ is actually **unchanged**. The correct Z₃ action is a cyclic permutation of color labels (R→G→B→R), under which ψ → ω·ψ.

**ERROR 4 (MODERATE): Notation collision — ω used for both Z₃ root and dispersion**

The symbol ω = e^{2πi/3} (Z₃ root, §2.1) and ω(k) (dispersion relation, §3.1) collide in the same document.

**ERROR 5 (MODERATE): Casimir notation misleading**

C_F(6) = 1/3 and C_F(8) = 1/6 are color factors, not standard Casimir invariants C₂(R). The numerical values are correct but the notation could be misread as standard quadratic Casimirs (C₂(6) = 10/3, C₂(8) = 3).

### Warnings

- Self-energy divergence (§4.1): described as "logarithmic" but is actually 1/√ε in 3D. The fluctuation-induced first-order transition still occurs but via a different mechanism than stated.
- HCP exclusion (§5.1): "period-2, coprime to 3" is imprecisely stated.
- A₃ ⊃ A₂ uniqueness claim (§5.4): B₃ and C₃ also contain A₂ sublattices; uniqueness needs qualification.
- Dimensional analysis table (§8.1) omits [w] and [u] dimensions and may be inconsistent with upstream Definition 0.1.2 (dimensionless χ_c).

### Re-Derived Equations (Confirmed)

- Casimir color factors: C_F(6) = [C₂(6) − 2C₂(3)]/2 = 1/3, C_F(8) = [C₂(8) − 2C₂(3)]/2 = 1/6, ratio = 2 ✅
- Dispersion minimum: k₀ = √(−κ_eff/(2C)), ω(k₀) = r − κ_eff²/(4C) ✅
- BCC reciprocal closed triangle: (1,1,0) + (-1,0,1) + (0,-1,-1) = 0, all |G| = √2 ✅

---

## 2. Physics Agent Report

### Verdict: Partial | Confidence: Medium

### Physical Issues

**ISSUE 1 (SIGNIFICANT): Alexander-McTague argument favors BCC, not FCC**

The standard Alexander-McTague (1978) result is that BCC is generically favored by the cubic Landau invariant in solidification. The table in §5.1 appears to have the lattice selection logic inverted. The Z₃ stacking argument (§5.2) is the strongest independent route to FCC selection and does not suffer from this confusion.

**ISSUE 2 (MINOR): Casimir ratio interpretation**

The selective use of only repulsive color factors to define α/β is a modeling choice inherited from Prop 0.0.3a, not a first-principles derivation. Acceptable given the dependency chain.

**ISSUE 3 (MINOR): w → 0 limit tautology**

§8.2 item 3 distinguishes "cubic Fourier coupling weakens" from "w → 0," but these are the same thing (F₃ is proportional to w).

### Limit Checks

| Limit | Result |
|-------|--------|
| α/β → 1: no instability | PASS |
| α/β → ∞: UV regulated by C > 0 | PASS |
| w → 0: weakly first-order (pure Brazovskii) | PASS |
| Single stella limit: recovers Prop 0.0.3a | PASS (qualitative) |

### Symmetry Verification

- Z₃ stacking: FCC = ABCABC (period 3 = |Z₃|) ✅
- O_h ⊃ W(A₂) ≅ S₃ (48/6 = 8, valid index) ✅
- Translational symmetry breaking pattern: continuous → discrete ✅

### Framework Consistency

| Cross-reference | Status |
|----------------|--------|
| Prop 0.0.3a: α/β = 2 threshold | CONSISTENT |
| Thm 0.0.6: FCC selected | CONSISTENT |
| Thm 0.0.2: ℝ³ from SU(3) | CONSISTENT (no circularity) |
| Prop 0.0.17r: lattice spacing ∝ R_stella | CONSISTENT |

---

## 3. Literature Agent Report

### Verdict: Partial | Confidence: Medium

### Citation Issues

**ISSUE 1 (CRITICAL): §5.1 Table contradicts Alexander & McTague (1978)**

The paper Alexander & McTague (1978) is cited in the References but its central conclusion — that BCC is generically favored by cubic Landau coupling — is directly contradicted by the proof's claim that FCC has nonzero F₃ and BCC has zero F₃. The ⟨111⟩ BCC reciprocal vectors cannot form closed triangles (each component is ±1; three such values never sum to zero).

**ISSUE 2 (SIGNIFICANT): Baxter (1973) misattributed for 3D first-order result**

Lines 162 and 319 cite Baxter (1973, J. Phys. C 6, L445) for the claim that the 3-state Potts transition is first-order. Baxter's 1973 paper addresses the 2D Potts model, where q=3 is actually **second-order** (continuous). The q=3 Potts model is first-order in **3D**, established by later Monte Carlo studies, notably Janke & Villanova (1997, Nucl. Phys. B 489, 679, arXiv:hep-lat/9612008).

The mean-field claim (cubic term makes transition first-order) is correct, but attributing it to Baxter 1973 is misleading.

### Missing References

1. **Janke & Villanova (1997)**, Nucl. Phys. B 489, 679 — Definitive 3D q=3 Potts first-order demonstration
2. **Swift & Hohenberg (1977)**, Phys. Rev. A 15, 319 — Related pattern formation equation
3. Modern soft matter reviews of Brazovskii-to-crystal transitions (block copolymer literature)

### Verified Citations

- Brazovskii (1975), JETP 41, 85 — Correctly described ✅
- Leibler (1980), Macromolecules 13, 1602 — Correctly applied ✅
- Fredrickson & Helfand (1987), J. Chem. Phys. 87, 697 — Correctly described ✅
- Wu (1982), Rev. Mod. Phys. 54, 235 — Comprehensive Potts review, cited appropriately ✅
- A₃ root lattice = FCC — Confirmed by standard references ✅
- W(A₂) ≅ S₃ ⊂ O_h — Standard result, correct ✅

---

## 4. Adversarial Script Results

**Script:** `verification/adversarial_prop_0_0_3b_lattice_formation.py`
**Result:** 30/31 checks PASS, 1 CRITICAL FAIL

### Tests and Results

| Test | Checks | Pass | Key Finding |
|------|--------|------|-------------|
| 1. Brazovskii Dispersion | 4 | 4 | k₀, ω(k₀), r_c all verified algebraically |
| 2. First-Order Transition | 3 | 3 | A_jump = \|w\|/u, hysteresis confirmed |
| 3. FCC Selection | 6 | 5 | **CRITICAL: ⟨111⟩ has 0 triangles, ⟨110⟩ has 8** |
| 4. Dimensional Analysis | 2 | 2 | All terms [L]⁻⁸ consistent |
| 5. Casimir Ratio | 4 | 4 | C_F(6)/C_F(8) = 2 independently verified |
| 6. Limiting Cases | 4 | 4 | All limits behave correctly |
| 7. Circularity | 4 | 4 | No circular dependencies found |
| 8. Self-Energy | 1 | 1 | 1/√ε divergence confirmed (slope = −0.504) |
| 9. Alexander-McTague | 3 | 3 | Z₃ can override A-M; needs explicit derivation |

### Plots Generated

1. `adversarial_3b_test1_dispersion.png` — Dispersion relation vs κ_eff, instability onset, α/β dependence
2. `adversarial_3b_test2_first_order.png` — Z₃ potential, order parameter jump, hysteresis loop
3. `adversarial_3b_test3_fcc_selection.png` — 3D reciprocal lattice vectors showing triangle impossibility for ⟨111⟩
4. `adversarial_3b_test6_limits.png` — Limiting case sweep of α/β
5. `adversarial_3b_test8_self_energy.png` — Self-energy 1/√ε divergence confirmation

---

## 5. Consolidated Findings

### Critical Issues (must fix)

| # | Issue | Found by | Location |
|---|-------|----------|----------|
| C1 | **§5.1 Table: FCC/BCC triangle count is swapped.** ⟨111⟩ BCC vectors cannot form closed triangles (sum of three ±1 values is always odd). Standard Alexander-McTague favors BCC, not FCC. | All 3 agents + script | §5.1, lines 196-203 |
| C2 | **Z₃ transformation law incorrect.** ψ involves \|χ_c\|², invariant under phase rotation. Correct Z₃ action is cyclic permutation of color labels. | Math agent | §2.1, line 66 |

### Significant Issues (should fix)

| # | Issue | Found by | Location |
|---|-------|----------|----------|
| S1 | κ_eff derivation has UV divergence for V(r) ~ 1/r² | Math agent | §2.3, line 90 |
| S2 | Baxter (1973) cited for 3D first-order Potts; Baxter proved 2D results where q=3 is second-order | Literature agent | §4.1, lines 162, 319 |
| S3 | Self-energy described as "logarithmically divergent" but is actually 1/√ε in 3D | Math agent | §4.1, line 160 |

### Moderate Issues (recommend fixing)

| # | Issue | Found by | Location |
|---|-------|----------|----------|
| M1 | ω notation collision (Z₃ root vs dispersion) | Math agent | §2.1, §3.1 |
| M2 | §8.1 dimensional table omits [w] and [u] | Script + Physics agent | §8.1 |
| M3 | A₃ ⊃ A₂ uniqueness: B₃, C₃ also contain A₂ | Math agent | §5.4, line 221 |
| M4 | w → 0 limit is tautological with cubic coupling weakening | Physics agent | §8.2 |

### What Is Correct and Strong

1. **Brazovskii instability mechanism** — well-established physics, correctly applied, algebraically verified
2. **Casimir ratio α/β = 2** — independently derived from SU(3) color factors by all agents
3. **Z₃ stacking argument for FCC** (§5.2) — sound and independent of the Fourier coupling error
4. **A₂ root compatibility argument** (§5.3) — correct group theory
5. **First-order transition** — both Brazovskii fluctuation mechanism and Z₃ cubic term support this
6. **No circularity** — the logical chain SU(3) → ℝ³ → FCC → ℝ³-with-metric is acyclic
7. **Computational verification** (P1-P4b) — internally consistent and supporting all claims
8. **Framework consistency** — matches Prop 0.0.3a, Thm 0.0.6, Prop 0.0.17r

---

## 6. Recommended Corrections

### Priority 1: Fix §5.1 Fourier Coupling Argument

**Option A (preferred):** Rewrite §5.1 to acknowledge that Alexander-McTague generically favors BCC via cubic coupling, then show that the Z₃ constraint (complex ψ³ term with phase structure) changes the analysis. The key insight: for a real scalar order parameter, BCC wins; for a Z₃-symmetric complex order parameter, the phase constraint ψ³ + ψ̄³ imposes additional selection that, combined with the stacking constraint, forces FCC.

**Option B:** Remove the cubic Fourier coupling as an independent argument and present FCC selection as based on two mechanisms (Z₃ stacking + A₂ root compatibility) rather than three.

### Priority 2: Fix Z₃ Transformation (§2.1)

Replace "Under a Z₃ transformation χ_c → ω^n χ_c, the order parameter transforms as ψ → ω^n ψ" with "Under the Z₃ cyclic permutation of color labels (R → G → B → R), the order parameter transforms as ψ → ω ψ."

### Priority 3: Fix Citations

- Replace or supplement Baxter (1973) with Janke & Villanova (1997) for the 3D first-order claim
- Add clarification that Baxter's exact 2D solution gives second-order for q=3

### Priority 4: Regularize κ_eff Derivation (§2.3)

Either derive κ_eff from a UV-regularized pair potential, or state explicitly that the integral requires a short-distance cutoff at the stella radius R_stella.

---

## 7. Verification Artifacts

| Artifact | Location |
|----------|----------|
| This report | `docs/proofs/verification-records/Proposition-0.0.3b-Multi-Agent-Verification-2026-03-27.md` |
| Adversarial script | `verification/adversarial_prop_0_0_3b_lattice_formation.py` |
| JSON results | `verification/adversarial_prop_0_0_3b_results.json` |
| Plot: Dispersion | `verification/plots/adversarial_3b_test1_dispersion.png` |
| Plot: First-order | `verification/plots/adversarial_3b_test2_first_order.png` |
| Plot: FCC selection | `verification/plots/adversarial_3b_test3_fcc_selection.png` |
| Plot: Limits | `verification/plots/adversarial_3b_test6_limits.png` |
| Plot: Self-energy | `verification/plots/adversarial_3b_test8_self_energy.png` |

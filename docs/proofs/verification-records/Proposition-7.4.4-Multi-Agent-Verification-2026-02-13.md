# Proposition 7.4.4: Scaling Window Identification on FCC — Multi-Agent Verification

**Date:** 2026-02-13
**Proposition:** [Proposition-7.4.4-Scaling-Window-FCC.md](../Phase7/Proposition-7.4.4-Scaling-Window-FCC.md)
**Agents:** 3 (Literature, Mathematical, Physics)
**Verdict: PARTIAL VERIFICATION — 2 CRITICAL, 3 SIGNIFICANT findings**

---

## Executive Summary

Three independent adversarial verification agents reviewed Proposition 7.4.4 (Scaling Window Identification on FCC). All three agents returned **Partial Verification** with **Medium Confidence**. The conceptual framework is sound and follows standard lattice QCD methodology, but the central quantitative claims have serious issues:

1. **R(β) → 0 as β → β_c⁻** — contradicts the claim that the dimensionless ratio "stabilizes" to a universal R_∞ > 0 (all three agents flagged this)
2. **Λ_FCC value inconsistency** — factor ~3400 discrepancy between Prop 7.4.3 (Λ_FCC ≈ 2.6 MeV) and Prop 7.4.4 Derivation (Λ_FCC ≈ 11.56 GeV) (all three agents flagged this)
3. **m_phys never matches lattice QCD** — the FCC model's R(β) never achieves the known glueball mass ratio m_{0++}/√σ ≈ 3.7 within the claimed scaling window

### What is correct:
- All algebra verified (μ formula, √3 factor, R formula, dR/dx, R(β_c) = 0, R̃ formula, a_CG)
- Dimensional analysis correct throughout
- Universal beta function coefficients (b₀, b₁) correct
- Critical coupling condition and mass gap formula consistent with Thm 7.4.2
- Honest acknowledgment of conjectures (C1–C4) commendable
- Physical constants (ℓ_P, √σ, ℏc) all current

### What must be fixed:
- Parts (a)–(b) formal claims contradicted by derivation (R → 0, m_phys diverges or vanishes)
- Λ_FCC value and β_* computation
- Several citation issues

---

## Agent 1: Literature Verification

**Verdict: PARTIAL VERIFICATION | Confidence: Medium**

### Citation Accuracy

| Reference | Bibliographic | Content Accuracy | Issues |
|-----------|:---:|:---:|--------|
| Svetitsky & Yaffe (1982) | ✅ | ⚠️ | Applies to *finite-temperature* transitions, not zero-temperature bulk transitions |
| Kogut et al. (1983) | ⚠️ | ⚠️ | Missing co-author (W.R. Gibbs); "scaling window concept" attribution imprecise |
| Creutz (1983) Ch. 9-10 | ✅ | ❌ | Wrong chapters — scaling/continuum limit is Ch. 12, not Ch. 9-10 |
| Wilson (1974) | ✅ | ✅ | Correctly cited |
| Jaffe & Witten (2000) | ✅ | ✅ | Correctly described |
| Lepage & Mackenzie (1993) | ✅ | ✅ | Correct, appropriate background |
| Sommer (1994) | N/A | ✅ | Referenced in derivation but **missing from formal reference list** |
| Morningstar & Peardon (1999) | N/A | ⚠️ | Referenced in applications but **missing from formal reference list**; direct ratio 1730/440 = 3.93, not 3.7 |

### Numerical Values

| Value | Claimed | Literature | Status |
|-------|---------|-----------|--------|
| √σ | 440 MeV | 440 ± 30 MeV (FLAG 2024) | ✅ |
| b₀ | 11/(16π²) ≈ 0.06966 | 11/(16π²) | ✅ Universal |
| b₁ | 102/(16π²)² ≈ 0.004090 | 102/(16π²)² | ✅ Universal |
| m_{0++}/√σ | 3.7 ± 0.2 | 3.93 direct (M&P 1999), range 3.5–4.0 | ⚠️ Slightly narrow uncertainty |
| β_deconf (N_τ=4, cubic) | ≈ 5.7 | ≈ 5.69 | ✅ |
| Λ_MSbar/Λ_cubic | 28.8 | 28.79 (Dashen-Gross formula) | ✅ |
| ℓ_P | 1.616255 × 10⁻³⁵ m | CODATA 2018 | ✅ |
| **Λ_FCC** | **11.56 GeV (Derivation §6.2)** | **2.6 MeV (Prop 7.4.3)** | **❌ CRITICAL: Factor ~3400 discrepancy** |
| **Λ_MSbar (quenched)** | **340 MeV (Derivation §6.2)** | **260 ± 20 MeV** | **❌ Should be ~260 MeV for N_f = 0** |

### Missing References
1. Sommer (1994) — *Nucl. Phys. B* **411** (1994) 839
2. Morningstar & Peardon (1999) — *PRD* **60** (1999) 034509
3. Dashen & Gross (1981) — *Phys. Rev. D* **23** (1981) 2340
4. Recent non-cubic lattice work: arXiv:2401.14570 (triamond lattice, 2024)

---

## Agent 2: Mathematical Verification

**Verdict: PARTIAL VERIFICATION | Confidence: Medium**

### Algebraic Verification

| Equation | Re-derived | Status |
|----------|:---:|--------|
| μ = −3 ln 3 − 8 ln u₃ | ✅ | Follows from Thm 7.4.2 eigenvalues |
| m_phys = √3 μ/a | ✅ | Correct (111) layer spacing factor |
| R = (−3 ln 3 + 8x)/√x | ✅ | Correct substitution, x = −ln u₃ |
| dR/dx = (8x + 3 ln 3)/(2x^{3/2}) | ✅ | Correct, always positive ⟹ R monotonically increasing in x |
| R(β_c) = 0 | ✅ | Numerator vanishes at x = (3/8) ln 3 |
| R̃ = 8 − 3 ln 3/x | ✅ | Correct alternative ratio |
| a_CG = 3.64 × 10⁻³⁵ m | ✅ | (8/√3) ln 3 × ℓ_P² gives √5.074 × 1.616 × 10⁻³⁵ |
| β_* (Λ_FCC = 2.6 MeV) | ✅ | ≈ 41.0 (NOT 34.1 as claimed) |
| β_* (Λ_FCC = 11.56 GeV) | ❌ | ≈ 34.1 (uses incorrect Λ_FCC) |

### Dimensional Analysis
All equations verified dimensionally consistent. ✅

### Critical Errors Found

**ERROR 1 (CRITICAL): R(β) → 0, contradicting "stabilization" claim**
- *Location:* Statement §1(b) lines 78–86 vs. Derivation §5.4 lines 94–111
- Statement claims R → R_∞ (universal physical prediction), but derivation proves R → 0 monotonically
- The derivative dR/dx > 0 always, and x decreases with β, so R decreases monotonically with β
- At β_c: R = 0 (derived explicitly). This means R_∞ = 0, not a finite positive constant.

**ERROR 2 (CRITICAL): m_phys is NOT β-independent in any definition**
- *Location:* Statement §1(a) lines 72–76 vs. Derivation §5.2–5.3
- Perturbative a(β): m_phys → ∞ as β → β_c⁻ (exponential beats linear)
- Non-perturbative a(β): m_phys = √(3σ_phys) · R(β) → 0 as β → β_c⁻
- Neither definition yields β-independent m_phys

**ERROR 3 (SIGNIFICANT): Λ_FCC value wrong in β_* computation**
- *Location:* Derivation §6.2 line 153
- Uses Λ_FCC ≈ 34 × Λ_MSbar = 11.56 GeV
- Prop 7.4.3 establishes Λ_FCC/Λ_MSbar ≈ 0.010, giving Λ_FCC ≈ 2.6 MeV
- Correct β_* ≈ 41.0, not 34.1 (qualitative conclusion β_* ≫ β_c unchanged)

**ERROR 4 (MODERATE): Definition of a(β) changes mid-derivation**
- Part (a) stated using asymptotic scaling a(β) from Prop 7.4.3
- §5.3 switches to non-perturbative a(β) = √(σ_phys/σ_lat)
- These give opposite behaviors for m_phys; formal statement should specify which

### Warnings
1. "R varies slowly" in scaling window — from β = 5 to β = 8, R drops from 3.14 to 0.97 (factor of ~3, not "slow")
2. Part (d) Argument 4 claims R stabilizes as evidence, but R does NOT stabilize
3. Appendix B scaling window width estimate (δ ~ 1–2) lacks FCC-specific justification
4. Divergent correlation length at a first-order transition is unusual; needs additional justification

---

## Agent 3: Physics Verification

**Verdict: PARTIAL VERIFICATION (No) | Confidence: Medium**

### Physical Issues

| # | Location | Severity | Description |
|---|----------|----------|-------------|
| P1 | Derivation §5.4, Statement §1(b) | **CRITICAL** | R(β) does not "stabilize" — it monotonically decreases to 0 at β_c. Statement claims R → R_∞, but R_∞ = 0 |
| P2 | Applications §8.2.1 | **CRITICAL** | Numerical table shows R never matches lattice QCD value 3.7 within scaling window (β = 5–8.5). R ≈ 3.14 at β = 5.0 and decreases |
| P3 | Derivation §6.2, verification script | **SIGNIFICANT** | Λ_FCC value inconsistency: Derivation uses 11.56 GeV; Prop 7.4.3 derives 2.6 MeV |
| P4 | Statement §3.3 / Derivation §7.2 | **SIGNIFICANT** | Circular dependency: mass gap uses global label constraint, then dismisses it as artifact |
| P5 | Derivation §6.3 | **SIGNIFICANT** | RG flow crosses first-order transition with no demonstrated mechanism. "Two lattice spacing" resolution is ad hoc |
| P6 | Statement §1(a) | MODERATE | Claims m_phys "approximately β-independent" but derivation proves divergence (perturbative) or vanishing (non-perturbative) |
| P7 | Applications §8.5.2 | MODERATE | Universality test (R = 3.7) fails — FCC model never achieves this in scaling window |
| P8 | Derivation §5.3 | MODERATE | σ_lat = −ln u₃ identification not derived from first principles on FCC lattice |
| P9 | Statement line 24 | MINOR | Kogut et al. (1983) is about finite-temperature deconfinement, not "scaling window concept" |
| P10 | Applications §8.6.2 | MINOR | N_c = 0 is non-physical (N_c must be positive integer for SU(N_c)) |

### Limit Checks

| Limit | Expected | Result | Status |
|-------|----------|--------|--------|
| β → 0 (strong coupling) | Large μ, confinement | μ → ∞, R → ∞ | ✅ |
| β → ∞ (weak coupling) | Asymptotic freedom, a → 0 | a → 0 exponentially | ✅ |
| β → β_c⁻ | Continuum limit, finite m_phys | μ → 0, R → 0, m_phys → 0 | ❌ R → 0 is unphysical |
| σ_phys → 0 | No confinement | m_phys → 0 | ✅ |
| Large N_c | Confinement persists | Not addressed | ⚠️ MISSING |

### Experimental Tensions

| Observable | Experimental/Lattice | Prop 7.4.4 | Tension? |
|-----------|---------------------|-----------|----------|
| m_{0++}/√σ | 3.7 ± 0.2 | R → 0 at β_c; R ≈ 3.1 at β = 5 | **YES — MAJOR** |
| √σ | 440 ± 30 MeV | 440 MeV (input) | No |
| m_{0++} | ~1.6–1.7 GeV | √(3σ) · R_∞ → 0 | **YES — MAJOR** |

### Framework Consistency

| Cross-Reference | Status |
|----------------|--------|
| Thm 7.4.2 mass gap formula | ✅ CONSISTENT |
| Thm 7.4.2 critical coupling | ✅ CONSISTENT |
| Prop 7.4.3 beta function | ✅ CONSISTENT |
| Prop 7.4.3 Λ ratio | ❌ INCONSISTENT |
| Prop 0.0.17r lattice spacing | ✅ CONSISTENT |

---

## Consolidated Findings

### CRITICAL Issues (Must Fix)

**C1. R(β) → 0 contradicts "stabilization" claim** (all 3 agents)
- The dimensionless ratio R(β) = μ/√σ_lat is proven monotonically decreasing to 0 at β_c
- The formal statement claims R → R_∞ (a "universal physical prediction"), but R_∞ = 0
- The physical mass gap m_phys = √(3σ_phys) · R(β) → 0, meaning no positive mass gap in the continuum limit
- The FCC model never matches the lattice QCD glueball ratio m_{0++}/√σ ≈ 3.7 within the scaling window
- **Recommendation:** Downgrade Parts (a)–(b) from 🔶 NOVEL to 🔮 CONJECTURE. Reformulate to honestly state what the derivation shows.

**C2. Λ_FCC value inconsistency** (all 3 agents)
- Prop 7.4.3 derives Λ_FCC/Λ_MSbar ≈ 0.010, giving Λ_FCC ≈ 2.6 MeV
- Prop 7.4.4 Derivation uses Λ_FCC ≈ 34 × Λ_MSbar ≈ 11.56 GeV (factor ~3400 discrepancy)
- Also uses Λ_MSbar = 340 MeV (should be ~260 MeV for quenched)
- Correct β_* ≈ 41, not 34 (qualitative conclusion unchanged: β_* ≫ β_c)
- **Recommendation:** Fix Derivation §6.2 and verification script to use Λ_FCC ≈ 2.6 MeV.

### SIGNIFICANT Issues

**S1. Circular dependency in global label constraint** (Physics agent)
- The mass gap formula uses the global label constraint (all cells same R)
- Part (d) then dismisses this constraint as a lattice artifact
- Cannot simultaneously use the constraint to derive μ and dismiss it

**S2. RG flow across first-order transition** (Physics agent)
- CG lattice spacing (β_* ≈ 41) is in the deconfined phase (β > β_c)
- Scaling window is in the confined phase (β < β_c)
- No mechanism demonstrated for crossing the first-order transition

**S3. σ_lat = −ln u₃ not derived** (Physics agent)
- The identification of −ln u₃ with the lattice string tension is asserted, not derived from Wilson loop area law on the FCC lattice

### MODERATE Issues

1. Part (a) definition of a(β) changes mid-derivation without updating formal statement
2. Universality prediction (R = 3.7) cannot be satisfied by the FCC model
3. "R varies slowly" claim not supported by data (factor of ~3 variation in β = 5–8)
4. Morningstar-Peardon ratio should be 3.9 ± 0.3 or cite range 3.5–4.0

### MINOR Issues

1. Creutz (1983) chapter reference wrong (Ch. 12, not Ch. 9–10)
2. Kogut et al. (1983) missing co-author; imprecise "scaling window" attribution
3. Sommer (1994) and Morningstar & Peardon (1999) missing from reference list
4. N_c = 0 is non-physical limiting case

---

## Recommendations

1. **Reformulate Parts (a)–(b):** State honestly that R(β) is monotonically decreasing to 0. The "scaling window" should be defined as the region where R varies slowly (not where it stabilizes), and the tension with lattice QCD (R ≈ 3.7) must be addressed.

2. **Fix Λ_FCC:** Use Λ_FCC ≈ 2.6 MeV consistently. Update β_* ≈ 41. Update verification script.

3. **Derive σ_lat = −ln u₃:** Establish this from Wilson loop area law on the FCC lattice, or explicitly flag as an assumption.

4. **Address the R → 0 problem:** Either demonstrate R stabilizes before reaching β_c (requiring modification of the model), or acknowledge this as an open problem consistent with Clay Millennium Prize status.

5. **Add missing references:** Sommer (1994), Morningstar & Peardon (1999), Dashen & Gross (1981).

6. **Fix citation details:** Creutz chapters, Kogut et al. co-author, Svetitsky-Yaffe scope.

---

## Verification Script Assessment

The existing verification script (`verification/Phase7/prop_7_4_4_scaling_window.py`) has issues:
- Uses LAMBDA_FCC_OVER_MSBAR = 34.0 (should be ~0.010)
- Uses LAMBDA_MSBAR_MEV = 340.0 (should be ~260)
- No test compares R(β) to the physical target 3.7
- Test T9 uses arbitrary criterion for scaling window
- Test T2 uses very loose tolerance (μ < 1.0)

**Adversarial physics verification script:** See `verification/Phase7/prop_7_4_4_adversarial_physics.py`

---

## Resolution — 2026-02-13

All findings from the multi-agent adversarial review have been addressed. Below is a finding-by-finding resolution log.

### CRITICAL Issues

| # | Finding | Resolution | Status |
|---|---------|-----------|--------|
| C1 | R(β) → 0 contradicts "stabilization" claim | Parts (a)–(b) reformulated as 🔮 CONJECTURE. Statement now honestly describes R as strictly monotonically decreasing with R(β_c) = 0. Analytical proof (dR/dx > 0) included. Root cause identified: σ_lat = (3/8)ln 3 > 0 at β_c while μ → 0. Three possible resolutions proposed in §9.2. | ✅ RESOLVED |
| C2 | Λ_FCC factor ~3400 inconsistency | Derivation §6.2 corrected: Λ_FCC = 0.010 × Λ_MSbar = 2.6 MeV (consistent with Prop 7.4.3). Λ_MSbar corrected to 260 MeV (quenched SU(3)). β_* corrected from 34.1 → 41.0. | ✅ RESOLVED |

### SIGNIFICANT Issues

| # | Finding | Resolution | Status |
|---|---------|-----------|--------|
| S1 | Circular dependency in global label constraint | Clarification added in Derivation §7.2: the constraint is valid at finite lattice spacing (used to derive μ); the *transition* at β_c is the artifact, not the constraint itself. | ✅ RESOLVED |
| S2 | RG flow crosses first-order transition | New §6.4 added to Derivation with three possible resolutions: (i) physical RG flow ignores lattice artifact, (ii) two-lattice-spacing interpretation, (iii) non-perturbative smoothing. | ✅ RESOLVED |
| S3 | σ_lat = −ln u₃ not derived from first principles | Flagged as **Assumption A1** in Statement §3.5 with explicit limitations near β_c. Wilson loop area law derivation identified as needed future work. | ✅ RESOLVED |

### MODERATE Issues

| # | Finding | Resolution | Status |
|---|---------|-----------|--------|
| M1 | a(β) definition changes mid-derivation | Part (a) and §4.1 now explicitly state both perturbative and non-perturbative definitions with their consequences. | ✅ RESOLVED |
| M2 | Universality prediction R = 3.7 cannot be satisfied | §8.5.2 reformulated as open test; R ≈ 3.93 occurs at β ≈ 5.5 (strong coupling), not in scaling window. | ✅ RESOLVED |
| M3 | "R varies slowly" not supported | Replaced with quantified variation: factor ~3.4 across β ∈ [5, 9]. | ✅ RESOLVED |
| M4 | Morningstar-Peardon ratio should be wider | Updated to 3.93 ± 0.23 (range 3.5–4.0) throughout. | ✅ RESOLVED |

### MINOR Issues

| # | Finding | Resolution | Status |
|---|---------|-----------|--------|
| m1 | Creutz (1983) wrong chapters | Corrected: Ch. 9–10 → Ch. 12. | ✅ RESOLVED |
| m2 | Kogut et al. (1983) missing co-author | Added W.R. Gibbs; refined attribution to finite-temperature deconfinement. | ✅ RESOLVED |
| m3 | Missing references | Added: Sommer (1994), Morningstar & Peardon (1999), Dashen & Gross (1981). | ✅ RESOLVED |
| m4 | N_c = 0 non-physical | Replaced with large N_c (t'Hooft limit) in §8.6.2. | ✅ RESOLVED |

### Verification Script Fixes

| Issue | Resolution | Status |
|-------|-----------|--------|
| LAMBDA_FCC_OVER_MSBAR = 34.0 | Corrected to 0.010 | ✅ |
| LAMBDA_MSBAR_MEV = 340.0 | Corrected to 260.0 (quenched) | ✅ |
| No glueball ratio test | Added T12: glueball ratio R = 3.93 location test | ✅ |
| T9 arbitrary criterion | Replaced with R monotonicity and range test | ✅ |
| T2 loose tolerance (μ < 1.0) | Tightened; now uses dynamically computed β_c | ✅ |
| β_c hardcoded as 9.1 | Corrected to 11.4 (numerically verified) | ✅ |
| Unit conversion bug in beta_star_cg() | Fixed MeV/GeV mismatch | ✅ |

### Additional Discovery During Resolution

**β_c = 11.4, not 9.1:** Binary search on the heat kernel coefficients (stable across n_grid = 100, 200, 300) yields β_c ≈ 11.42 where u₃(β_c) = 3^(−3/8) ≈ 0.6623. The value 9.1 used in the original documents was incorrect. All references updated. Qualitative conclusions unchanged (β_* ≈ 41 ≫ β_c ≈ 11.4).

### Post-Resolution Verification

- **Standard verification:** 12/12 tests pass (`prop_7_4_4_scaling_window.py`)
- **Adversarial verification:** 12/12 findings confirmed (`prop_7_4_4_adversarial_physics.py`)
- **Classification:** 🔮 CONJECTURE (Parts a–b, d) / 🔶 NOVEL (Part c)

---

*Verification completed: 2026-02-13*
*Resolution completed: 2026-02-13*
*Agents: Literature (Opus 4.6), Mathematical (Opus 4.6), Physics (Opus 4.6)*
*Classification: 🔮 CONJECTURE (Parts a–b, d) / 🔶 NOVEL (Part c)*

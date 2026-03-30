# Proposition 0.1.3a — Multi-Agent Verification Report

**Date:** 2026-02-23
**Target:** Proposition 0.1.3a (Pressure Function Form-Independence)
**File:** `docs/proofs/Phase0/Proposition-0.1.3a-Pressure-Function-Form-Independence.md`
**Method:** Three-agent adversarial peer review (Literature, Mathematics, Physics)

---

## Overall Verdict: PARTIAL VERIFICATION

The core claim — that qualitative downstream predictions depend only on abstract axioms (P1)–(P7), not on the specific 1/r² realization — is **sound and well-argued**. However, the agents identified **4 concrete mathematical errors**, **2 moderate physical issues**, and several **warnings** that should be addressed before the proposition is marked ✅ VERIFIED.

---

## 1. Literature Verification Agent

### Verdict: VERIFIED (Partial) | Confidence: HIGH

### Citation Accuracy

| Citation | Status | Notes |
|----------|--------|-------|
| Cea et al. 2012 (arXiv:1208.1362) | ✅ Publication details correct | Content claim needs nuance (see below) |
| Cea et al. 2014 (arXiv:1404.1172) | ✅ Publication details correct | Full title includes "London penetration depth and coherence length" |
| √σ = 440 ± 30 MeV (FLAG 2024) | ✅ Value reasonable | FLAG is not the primary source for string tension; attribution imprecise |
| f_π = 88.0 MeV (95.6% of PDG) | ✅ Calculation correct | PDG 2024: f_π = 92.1 ± 0.6 MeV (PS convention); 88.0/92.1 = 95.6% |

### Issues Found

**L1. Lattice QCD profile claim overstated (LOW severity)**
Section 5.3 claims the 1/r² profile is "consistent with chromoelectric flux tube measurements." The actual lattice QCD profiles (Cea et al.) use a Clem/dual-superconductor ansatz with modified Bessel functions (K₀, K₁), which have **exponential** decay at large distances, not 1/r² power-law decay. The proposition correctly labels this as "illustrative" but the word "consistent" overstates the match.

**L2. Divergence type mislabeled (LOW severity)**
Section 4.3 describes the divergence of ∫[1/(1+|x|)]² d³x as "logarithmic" — it is actually **linear** (integrand → 4π as r → ∞). The conclusion (integral diverges) is correct.

**L3. FLAG 2024 attribution imprecise (LOW severity)**
FLAG primarily averages flavor physics quantities; the string tension is not one of their headline results. The value 440 MeV is within the accepted range but the attribution should cite a more specific lattice source.

### Missing References

1. Baker, Cea, Chelnokov, Cosmai, Cuteri, Papa (2019), EPJC 79, 478 — "Isolating the Confining Color Field in the SU(3) Flux Tube"
2. Cosmai et al. (2024), arXiv:2409.20168 — "Unveiling the flux tube structure in full QCD" (2+1 dynamical fermions)
3. A standard computational geometry reference (e.g., de Berg et al. 2008) for the Voronoi equivalence
4. An effective field theory reference for model/scheme independence (e.g., Georgi 1993)

### Suggestions

- Soften the "consistent with" language: "The 1/r² profile captures the short-distance Coulombic behavior seen in lattice QCD, though full transverse profiles use Bessel-function fits from the dual superconductor model"
- Note that lattice QCD profiles (Clem ansatz) are themselves members of the equivalence class (P1)–(P7)

---

## 2. Mathematical Verification Agent

### Verdict: VERIFIED (Partial) | Confidence: MEDIUM-HIGH

### Errors Found

**M1. Integral in §2.3 wrong by factor of 2 (MODERATE severity)**

Line 71 claims:
$$\int_0^\infty \frac{4\pi r^2 \, dr}{(r^2 + \epsilon^2)^2} = \frac{\pi^2}{2\epsilon}$$

**Correct value:** π²/ε. The radial integral ∫₀^∞ r²/(r²+ε²)² dr = π/(4ε) is correct (per §5.2 table), but multiplying by 4π gives π²/ε, not π²/(2ε).

**M2. Gaussian L² integral wrong by factor of √2 (MODERATE severity)**

Line 81 claims ∫(P_c^(A))² d³x = π^(3/2)σ³/(2ε⁴).

**Correct value:** π^(3/2)σ³/(2√2 ε⁴). The standard integral with a = 2/σ² introduces a^(3/2) = 2√2/σ³. The §5.2 table entry is also incorrect.

**M3. Counterexample in §4.3 is invalid (MODERATE severity)**

The function 1/(1+|x−x_c|) is claimed to be "smooth everywhere" but is NOT differentiable at x = x_c (since |x−x_c| has a gradient singularity at the origin). It fails BOTH (P4) and (P7), so it cannot serve as a counterexample showing (P4) alone doesn't imply (P7).

**Valid counterexample:** P_c(x) = 1/√(|x−x_c|² + ε²), which IS C^∞ on ℝ³ but has ∫P_c² d³x = ∞ since P² ~ 1/r² at large r.

**M4. Power-law L² threshold is wrong (MODERATE severity)**

Section 2.4 claims P_c^(C) = 1/(r^(2α) + ε^(2α))^(1/α) satisfies (P7) for α > 3/4. But for this form, P ~ 1/r² for ALL α > 0 at large r (since (r^(2α))^(1/α) = r²), so the L² integral converges for all α > 0. The threshold α > 3/4 would apply to the different form 1/(r²+ε²)^α. Either the form or the threshold needs correction.

### Warnings

**W1. (P4) silently strengthened from source**
Definition 0.1.1 states (P4) as "P_c is continuous on ∂S" (C⁰ on compact boundary). Proposition 0.1.3a states (P4) as "P_c ∈ C²(ℝ³)". This is a significant strengthening in both regularity (C⁰ → C²) and domain (∂S → ℝ³) that is not acknowledged.

**W2. File count inconsistency: 16 vs 17**
Sections 1 and 3.1 say "16 downstream files" but the classification table has 17 entries and §7 says "17."

**W3. W-axis coordinate description may use different convention**
Section 4.4 describes the W-axis as x₁ = x₂ = x₃. Under Def 0.1.3 coordinates, the W-vertex is at (-1,-1,1)/√3, so the W-axis direction is (1,1,-1), not (1,1,1). The math is correct under Theorem 3.0.1's labeling convention, but mixing conventions without noting the discrepancy is confusing.

**W4. (P2) global minimum claim incompatible with ℝ³ domain**
On ℝ³, for any strictly decreasing f > 0, the infimum as r → ∞ is ≤ 0, which is less than f(2) = P_c(v_c̄). So v_c̄ is NOT the global minimizer on ℝ³. Should say "minimum over vertices."

**W5. Voronoi equivalence needs fixed distance function**
Section 4.2 claims "any P_c = f(|x−x_c|)" gives identical Voronoi cells, but this assumes all realizations use the same distance function d. Different distance functions produce different Voronoi cells.

### Re-Derived Equations

| Equation | Claimed | Correct | Status |
|----------|---------|---------|--------|
| ∫₀^∞ 4πr²dr/(r²+ε²)² | π²/(2ε) | π²/ε | **WRONG** |
| ∫₀^∞ r²dr/(r²+ε²)² | π/(4ε) | π/(4ε) | ✅ |
| Gaussian 3D integral | π^(3/2)σ³/(2ε⁴) | π^(3/2)σ³/(2√2 ε⁴) | **WRONG** |
| 1/(r+ε) fails L² | divergent | divergent | ✅ |
| Step function integral | ε³/3 | ε³/3 | ✅ |
| Power-law threshold | α > 3/4 | All α > 0 (stated form) | **WRONG** |
| Voronoi equivalence under (P6) | identical cells | correct (fixed d) | ✅ |
| Nodal line = W-axis under (P6) | via injectivity | valid | ✅ |

---

## 3. Physics Verification Agent

### Verdict: VERIFIED (Partial) | Confidence: MEDIUM

### Physical Issues

| # | Issue | Severity | Location |
|---|-------|----------|----------|
| P1 | Gradient-sensitive observables (∇θ profile) may not be fully realization-independent | Moderate | §4.1(iii), §4.6 |
| P2 | Near-field curvature (Hessian at convergence point) is realization-dependent | Minor | §4.1 |
| P3 | Asymptotic behavior (power-law vs exponential) cannot be absorbed into two parameters | Moderate | §4.6 |
| P4 | Yukawa screening introduces a third parameter beyond ε and R_stella | Minor | §2.4, Alt B |
| P5 | (P4) axiom inconsistency: continuous (Def 0.1.1) vs C² (Prop 0.1.3a) | Moderate | §2.1 |
| P6 | (P6) claims non-Euclidean distance allowed, but Voronoi proof requires Euclidean | Moderate | §4.2, §6.2 |
| P7 | Domain mismatch: (P1)-(P5) on ∂S but (P7) on ℝ³ | Minor | §2.2 |
| P8 | Universality analogy lacks RG-based justification | Moderate (conceptual) | §5, throughout |

### Limit Checks

| Limit | Result | Status |
|-------|--------|--------|
| ε → 0 (standard form) | (P7) fails — correctly excluded | ✅ PASS |
| ε → 0 (Gaussian) | Peak diverges but L² norm finite — needs discussion | ⚠️ CAUTION |
| R_stella → ∞ | Physics trivializes correctly | ✅ PASS |
| Gaussian vs standard at large r | Qualitatively different tails | ⚠️ ISSUE |
| Yukawa screening | Third scale λ not absorbed into (ε, R_stella) | ⚠️ ISSUE |
| ω₀ = √2 ratio | Form-independent: H/I = 1 by construction | ✅ PASS |

### Symmetry Verification

| Symmetry | Preserved? | Notes |
|----------|-----------|-------|
| S₃ color permutation | ✅ Yes | Automatic from (P3) + identical f |
| Z₂ matter-antimatter | ✅ Yes | Preserved by radial symmetry |
| Different realizations break symmetries? | ✅ No | (P3) prevents this |

### Key Physical Findings

1. **Lattice QCD CAN distinguish realizations:** Flux tube profiles are observable and realization-dependent. The proposition should clarify that "form-independence" applies to *qualitative structural predictions*, not to observable field profile shapes.

2. **Two-parameter absorption is insufficient for all alternatives:** Gaussian (exponential tails) and Yukawa (screening length λ) alternatives cannot map onto inverse-square (power-law tails) with only ε and R_stella. The claim should be narrowed or qualified.

3. **The gauge analogy is apt but imperfect:** Gauge invariance is a local symmetry with precise mathematical content (fiber bundle structure). The realization equivalence is a global statement about functional forms. Useful pedagogically but should not be overloaded.

---

## 4. Consolidated Error Summary

### Must Fix (4 items)

| # | Error | Agent | Action Required |
|---|-------|-------|----------------|
| M1 | Integral π²/(2ε) should be π²/ε | Math | Fix §2.3 line 71 |
| M2 | Gaussian integral wrong by √2 | Math | Fix §2.4 line 81 and §5.2 table |
| M3 | 1/(1+\|x\|) counterexample invalid (not smooth) | Math | Replace with 1/√(r²+ε²) in §4.3 |
| M4 | Power-law threshold α > 3/4 wrong for stated form | Math | Fix form or threshold in §2.4 and §5.2 |

### Should Fix (5 items)

| # | Issue | Agent(s) | Action Required |
|---|-------|----------|----------------|
| W1/P5 | (P4) silently upgraded from C⁰ to C² | Math, Physics | Acknowledge strengthening in §2.1 |
| W2 | File count 16 vs 17 inconsistency | Math | Update §1 and §3.1 to say "17" |
| L2 | "Logarithmic divergence" should be "linear" | Literature | Fix parenthetical in §4.3 |
| P6 | Non-Euclidean distance claim conflicts with Voronoi proof | Physics | Qualify §6.2 or §4.2 |
| W4 | (P2) "global minimum" incompatible with ℝ³ | Math | Clarify "minimum over vertices" |

### Consider Fixing (5 items)

| # | Issue | Agent(s) | Suggestion |
|---|-------|----------|-----------|
| P3 | Asymptotic behavior absorption claim overstated | Physics | Qualify "two-parameter absorption" for different tail behaviors |
| P4 | Yukawa introduces third parameter | Physics | Note that some realizations may need additional matching parameters |
| L1 | Lattice profile claim overstated | Literature | Soften "consistent with" language |
| P1 | Gradient-sensitive observables | Physics | Add note about ∇θ profile realization dependence |
| P8 | Universality analogy lacks RG justification | Physics | Add caveat or cite EFT model-independence |

---

## 5. Recommendations

1. **Fix the four algebraic errors** (M1–M4) — these are straightforward corrections that don't affect the proposition's logical structure
2. **Acknowledge the (P4) strengthening** — add a note in §2.1 explaining that (P4) is upgraded from the original C⁰ to C² for the purposes of this proposition
3. **Qualify the two-parameter absorption claim** — note that some realizations with qualitatively different asymptotics (Gaussian, Yukawa) may require additional matching beyond ε and R_stella
4. **Clarify the Voronoi/distance function tension** — either restrict (P6) to distances compatible with Euclidean equidistant sets or note the Voronoi equivalence is specific to the computational realization
5. **Add missing references** — especially the 2019 and 2024 Cea et al. papers and a computational geometry reference

---

## 6. Verification Metadata

| Property | Value |
|----------|-------|
| Verification date | 2026-02-23 |
| Agents deployed | 3 (Literature, Mathematics, Physics) |
| Model | Claude Opus 4.6 |
| Literature agent confidence | HIGH |
| Math agent confidence | MEDIUM-HIGH |
| Physics agent confidence | MEDIUM |
| Overall assessment | Core thesis sound; algebraic errors need fixing; physical claims need qualification |

---

*Report generated by multi-agent adversarial verification protocol.*
*See: `docs/verification-prompts/agent-prompts.md` for agent specifications.*

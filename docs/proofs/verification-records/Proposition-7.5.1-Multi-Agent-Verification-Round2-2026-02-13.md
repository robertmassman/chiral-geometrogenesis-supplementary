# Proposition 7.5.1: Symanzik Effective Theory for the FCC Lattice — Multi-Agent Verification (Round 2)

**Verification Date:** 2026-02-13 (Round 2)
**Status:** VERIFIED WITH MINOR FINDINGS
**Agents Used:** Mathematical, Physics, Literature (all run independently in parallel)
**Prior Review:** [Round 1 (2026-02-13)](./Proposition-7.5.1-Multi-Agent-Verification-2026-02-13.md) — 10 findings, all resolved

---

## Executive Summary

This is the **second round** of multi-agent verification for Proposition 7.5.1, conducted after all 10 findings from Round 1 were resolved. The three agents independently reviewed the corrected 3-file proof documents and existing verification scripts.

**Core result confirmed:** $c_4^{(\text{FCC})} = 0$ at $O(a^2)$ is correct, rigorous at tree level, and well-supported at one loop. All 25 numerical tests pass (11 standard + 14 adversarial).

| Agent | Verdict | Confidence | New Findings |
|-------|---------|------------|--------------|
| Mathematical | VERIFIED | Medium-High | 5 (1 moderate, 4 minor) |
| Physics | VERIFIED | High | 3 (1 moderate, 2 minor) |
| Literature | VERIFIED | Medium-High | 3 (all minor) |
| **Overall** | **VERIFIED WITH MINOR FINDINGS** | **High** | **8 consolidated** |

All Round 1 findings (10/10) confirmed resolved by all three agents.

---

## Dependency Chain

All prerequisites verified (unchanged from Round 1):

```
Proposition 7.5.1: Symanzik Effective Theory for FCC Lattice
├── Proposition 7.4.3 (FCC Lattice Perturbation Theory) .... ✅ VERIFIED
│   └── Lemma 6.3.1 (Fourth-Moment Isotropy of D4) ........ ✅ VERIFIED
├── Proposition 7.4.4a (Exact Wilson Loop on FCC) .......... ✅ VERIFIED
├── Symanzik (1983) — Improvement program framework ........ ✅ ESTABLISHED
├── Lüscher & Weisz (1985) — On-shell improved actions ..... ✅ ESTABLISHED
├── Curci, Menotti & Paffuti (1983) — Hypercubic coeffs .... ✅ ESTABLISHED
├── Weisz (1983) — Improved lattice action ................. ✅ ESTABLISHED
└── Celmaster (1982) — BCH lattice formulation ............. ✅ ESTABLISHED
```

---

## Round 1 Findings: Confirmation of Resolution

All three agents independently confirmed that all 10 findings from Round 1 are properly resolved:

| # | Finding | Resolution Status |
|---|---------|-------------------|
| 1 | O₃/O₄ operator definitions | ✅ Confirmed resolved — correct (DF)(DF) basis used |
| 2 | One-loop proof gap | ✅ Confirmed resolved — W(B₄) symmetry argument added |
| 3 | Derivation false start | ✅ Confirmed resolved — clean computation shown |
| 4 | Part (d) incomplete | ✅ Confirmed resolved — downgraded to structural claim |
| 5 | Tadpole implications | ✅ Confirmed resolved — §8.4.3 added |
| 6 | "~2×" claims | ✅ Confirmed resolved — tree-level footnote added |
| 7 | Eq 6.5 proportionality | ✅ Confirmed resolved — calibration argument documented |
| 8 | Celmaster scope | ✅ Confirmed resolved — correct characterization |
| 9 | Missing references | ✅ Confirmed resolved — Husung et al. added |
| 10 | Asymptotic expansion | ✅ Confirmed resolved — noted in §5 and Part (a) |

---

## New Consolidated Findings (Round 2)

### Finding R2-1 (MODERATE): $c_1^{(0)} = 1/12$ Universality for Triangular Plaquettes

**Agents:** Mathematical, Physics
**Location:** Derivation file §7.1 (line 378)

**Issue:** The proposition claims $c_1^{(0)} = 1/12$ "is independent of the plaquette shape (triangular vs square) at leading order." The justification given is that "the $\mathcal{O}_1$ coefficient at tree level is determined by the second-order Stokes' theorem correction, which is proportional to the plaquette area and is independent of the plaquette shape."

This is almost certainly correct but is stated without an explicit derivation from the triangular plaquette expansion. The tree-level $c_1$ comes from the $O(a^3)$ correction to Stokes' theorem involving $n_1^\rho D_\rho F$. When summed over all plaquette orientations, the coefficient depends on the lattice geometry only through the second-moment tensor $T_{\mu\nu}$, which is isotropic for both $D_4$ and $\mathbb{Z}^4$. Hence $c_1^{(0)}$ is the same. However, the intermediate steps are not shown.

**Impact:** Low — the result is a well-known universal feature of unimproved Wilson-type actions.

**Recommendation:** Add 2-3 lines showing the key step: the $O(a^3)$ Stokes correction contracted over all plaquette orientations reduces to a second-moment structure, which is isotropic for $D_4$.

---

### Finding R2-2 (MODERATE): Plaquette Count Convention

**Agents:** Mathematical
**Location:** Derivation Appendix A.3

**Issue:** Appendix A.3 refers to "8 triangular plaquettes per unit cell." The numerical verification scripts find 96 ordered pairs $(i,j)$ with $i < j$ such that $-(\vec{n}_i + \vec{n}_j)$ is a $D_4$ vector, corresponding to approximately 32 distinct unoriented triangles from one site (96/3 since each triangle has 3 ordered pairs). The count "8" does not match any straightforward interpretation of "distinct unoriented triangles from one site."

**Note:** The $D_4$ lattice has 1 site per primitive cell. There are 24 nearest-neighbor vectors. The adversarial script (Test 09) explicitly constructs 32 distinct triangles, each equilateral with uniform area. Dividing by 3 corners gives ~10.7 per cell, not 8.

**Impact:** Presentation issue only. The plaquette count does not affect any calculation; the sums over plaquettes are performed using all 24 nearest-neighbor vectors, which is unambiguous.

**Recommendation:** Verify the exact count convention and update accordingly. Possible interpretations: 8 may refer to oriented plaquette *classes* under $W(D_4)$ symmetry, or 8 per unit cell in a different cell convention.

---

### Finding R2-3 (MINOR): Abelian Limit Wording

**Agents:** Physics, Mathematical
**Location:** Applications file §8.7.2

**Issue:** The text states "$\mathcal{O}_2$ (triple-$F$) vanishes identically for abelian gauge groups." The operator $\text{Tr}(F_{\mu\nu}F_{\nu\rho}F_{\rho\mu})$ does NOT vanish for $U(1)$ — it is generally nonzero for an antisymmetric real tensor $F_{\mu\nu}$. What vanishes is the *coefficient* $c_2$: at tree level $c_2^{(0)} = 0$, and at one loop the non-abelian vertex corrections that generate $c_2^{(1)}$ are absent for $U(1)$.

**Impact:** Wording issue only. The physics is correct — the $\mathcal{O}_2$ contribution to the Symanzik expansion vanishes for Abelian theories because the coefficient is zero, not because the operator is zero.

**Recommendation:** Change "vanishes identically" to "has vanishing coefficient" or "does not contribute."

---

### Finding R2-4 (MINOR): All-Orders Claim Qualification

**Agents:** Mathematical
**Location:** Derivation file §6.2, Remark after Eq. 6.23

**Issue:** The text states that $c_4^{(\text{FCC}),(n)} = 0$ for all $n \geq 0$ at $O(a^2)$, presented as following from the proof. While physically very well-motivated — the $O(a^2)$ rotational breaking can only come from the fourth-moment anisotropy, which is zero for $D_4$ — this is a strong claim that requires showing the factorization $c_4^{(n)} \propto \Delta T$ holds at all perturbative orders.

The argument is plausible: at $O(a^2)$, the rotational-breaking Symanzik coefficient is determined by the lattice geometry through the fourth-moment tensor at each perturbative order. But the formal proof only covers tree level (exact) and one loop (via $W(D_4)$ symmetry).

**Impact:** Presentation concern. The all-orders claim is almost certainly correct.

**Recommendation:** Qualify as "expected from the structure of the Symanzik expansion" rather than "follows from the proof." Add: "A rigorous all-orders proof would require demonstrating the factorization $c_4^{(n)} \propto \Delta T_{\mu\nu\rho\sigma}$ at each perturbative order, which is expected from the operator structure but not formally established beyond one loop."

---

### Finding R2-5 (MINOR): $\mathcal{O}_4$ Index Notation

**Agents:** Mathematical
**Location:** Statement file Eq. in §1(b); Derivation file Eq. 5.18

**Issue:** In $\mathcal{O}_4 = \sum_{\mu,\nu} \text{Tr}(D_\mu F_{\mu\nu}\, D_\mu F_{\mu\nu})$, the index $\mu$ appears 4 times: twice in $D_\mu$ and twice in $F_{\mu\nu}$. The convention is that $\mu$ is summed explicitly in the outer sum but NOT via Einstein convention within each term. This is correct but potentially confusing for readers who assume Einstein summation.

**Impact:** Presentation clarity only.

**Recommendation:** Add a brief note: "Here $\mu$ is summed in the outer sum; it is NOT Einstein-summed within each factor $D_\mu F_{\mu\nu}$. The operator breaks rotational symmetry precisely because the covariant derivative direction is tied to the field strength index."

---

### Finding R2-6 (MINOR): Triangular Plaquette BCH Expansion Detail

**Agents:** Physics
**Location:** Derivation file §5.1-5.3

**Issue:** The Symanzik framework is correctly applied but the derivation does not explicitly show the Baker-Campbell-Hausdorff expansion for a triangular (3-link) plaquette in the same step-by-step detail that standard textbooks show for square (4-link) plaquettes. The 3-link case has one fewer BCH step but the same leading-order result. This is implicitly correct but could be more explicit.

**Impact:** Presentation issue — the physics is standard.

**Recommendation:** Consider adding 2-3 lines showing the BCH for 3 links: $U_\triangle = e^{X_1}e^{X_2}e^{X_3} = \exp(X_1 + X_2 + X_3 + \frac{1}{2}[X_1,X_2] + \frac{1}{2}[X_1,X_3] + \frac{1}{2}[X_2,X_3] + \ldots)$.

---

### Finding R2-7 (MINOR): Missing Errata Citations

**Agents:** Literature
**Location:** §10 References

**Issue:** Three key references have errata that are not cited:
- Curci, Menotti & Paffuti: erratum in Phys. Lett. B **135** (1984) 516
- Lüscher & Weisz: erratum in Commun. Math. Phys. **98** (1985) 433
- Weisz & Wohlert: erratum in Nucl. Phys. B **247** (1984) 544

**Impact:** Minor bibliographic completeness. The errata do not affect the physics used in the proposition.

**Recommendation:** Add erratum citations to refs [3], [4], [6].

---

### Finding R2-8 (MINOR): Additional BCH Lattice References

**Agents:** Literature
**Location:** §3.5 Prior Work

**Issue:** Additional prior work on the BCH/FCC lattice could strengthen the prior work discussion:
- Celmaster & Moriarty, *Phys. Rev. D* **28** (1983) 2076 — average plaquette on BCH
- Celmaster & Moriarty, *Phys. Rev. D* **33** (1986) 3718 — SU(2) quark potential on BCH
- Capitani, *Phys. Rept.* **382** (2003) 113 (hep-lat/0211036) — lattice perturbation theory review

**Impact:** Minor completeness. None of these papers perform Symanzik analysis for the FCC lattice, confirming the novelty claim.

**Recommendation:** Add 1-2 of these references to §3.5 to demonstrate awareness of the full BCH lattice literature.

---

## Numerical Verification Results

### Standard Verification Script: `prop_7_5_1_symanzik_fcc.py`

| Test | Result | Status |
|------|--------|--------|
| D₄ fourth-moment isotropy | Max deviation: 4.44e-16 | PASS |
| Cubic fourth-moment anisotropy | $\Delta T = 1.0$ (expected > 0) | PASS |
| D₄ sixth-moment anisotropy | $T_{111111} = 1.5$ vs iso $1.875$ | PASS |
| $c_4^{(\text{FCC})} = 0$ | Max $\|\Delta T\| = 4.44\text{e-}16$ | PASS |
| $c_4^{(\text{cubic})} \neq 0$ | $\Delta T_\text{cubic} = 1.0$ | PASS |
| Tree-level $c_1 = 1/12$ | Exact match | PASS |
| D₄ lattice: 24 unit vectors | All verified | PASS |
| FCC propagator continuum limit | Rel error $3.12\text{e-}05$ | PASS |
| Tadpole integrals | $I_\text{FCC} = 0.276$, $I_\text{cubic} = 0.155$ | PASS |
| Plaquette sum isotropy | 96 plaquettes, max residual 0 | PASS |
| Dimensional analysis | Total dimension = 0 | PASS |
| **Total** | **11/11** | **ALL PASS** |

### Adversarial Physics Script: `prop_7_5_1_adversarial_physics.py`

| Test | Category | Result | Status |
|------|----------|--------|--------|
| All 256 fourth-moment components | CRITICAL | Max dev: 4.44e-16 | PASS |
| Cubic anisotropy and $c_4^{(0)} = 1/12$ | CRITICAL | Exact match | PASS |
| W($D_4$) group: order 192 | CRITICAL | All 192 elements verified | PASS |
| One-loop $c_4 = 0$ algebraic argument | CRITICAL | $|\Delta T| = 3.3\text{e-}16$ | PASS |
| Sixth-moment anisotropy | STRUCTURAL | $T_{111111} = 1.5 \neq 1.875$ | PASS |
| BCH convergence for $\beta \geq 16$ | STRUCTURAL | $g_0 = 0.612 < \ln 2$ | PASS |
| Tadpole ratio $I_\text{FCC}/I_\text{cubic}$ | STRUCTURAL | Ratio $\approx 1.78$ | PASS |
| Continuum limit scaling ($O(a^4)$ anisotropy) | SCALING | Power $\approx 4.0$ | PASS |
| Plaquette geometry (96 triangles) | SCALING | 96 plaquettes, all areas verified | PASS |
| Operator independence | SCALING | 4 independent for SU(3) | PASS |
| Dimensional analysis (all operators) | CONSISTENCY | All dimension-6 verified | PASS |
| Limiting cases (Abelian, $g_0 \to 0$) | CONSISTENCY | All limits pass | PASS |
| Propagator W($D_4$) invariance | CONSISTENCY | Max variation: 2.2e-16 | PASS |
| Second-moment isotropy ($T_{\mu\nu}$) | CONSISTENCY | Max dev: 4.4e-16 | PASS |
| **Total** | | **14/14** | **ALL PASS** |

---

## Re-Derived Key Equations (Round 2)

All equations independently re-derived by the Mathematical agent:

| Equation | Agent Re-derivation | Paper | Status |
|----------|-------------------|-------|--------|
| Eq. 5.1: Area 2-form $\Sigma^{\mu\nu}$ | $(a^2/2)(n_{1\mu}n_{2\nu} - n_{1\nu}n_{2\mu})$ | Same | VERIFIED |
| Eq. 5.7: Plaquette expansion | $1 + ig_0 a^2 \Sigma F - g_0^2 a^4/2 (\Sigma F)^2 + \ldots$ | Same | VERIFIED |
| Eq. 5.9: Trace 1/6 factor | $1/(2N_c) = 1/6$ for SU(3) | $1/6$ | VERIFIED |
| Eq. 6.5: Calibration formula | $(1/3) \cdot 1/4 = 1/12$ for $\mathbb{Z}^4$ | $1/12$ | VERIFIED (by calibration) |
| Eq. 6.8: $T_{1111}$ (D₄) | $12 \times (1/\sqrt{2})^4 = 3$ | 3 | VERIFIED |
| Eq. 6.9: $T_{1122}$ (D₄) | $4 \times (1/\sqrt{2})^4 = 1$ | 1 | VERIFIED |
| Eq. 6.11: $T_{1111}^{\text{iso}}$ | $24/(4 \cdot 6) \times 3 = 3$ | 3 | VERIFIED |
| Eq. 6.12: $T_{1122}^{\text{iso}}$ | $24/(4 \cdot 6) \times 1 = 1$ | 1 | VERIFIED |
| $\Delta T$ (D₄) | $3 - 3 = 0$, $1 - 1 = 0$ | 0 | VERIFIED |
| Eq. 6.20: $S_4$ identity | Permutation symmetry of integral | Same | VERIFIED |
| Eq. 6.21: $S_4$ identity | Pair transitivity | Same | VERIFIED |
| Eq. 6.22: Algebraic identity | $(\sum k_\mu^2)^2$ expansion | Same | VERIFIED |
| Eq. 6.24: $T_{1111}$ ($\mathbb{Z}^4$) | $2 \times 1^4 = 2$ | 2 | VERIFIED |
| Eq. 6.25: $T_{1122}$ ($\mathbb{Z}^4$) | 0 | 0 | VERIFIED |
| Cubic $c_4^{(0)} = 1/12$ | $(1/3)(1)/2^2 = 1/12$ | $1/12$ | VERIFIED |
| Eq. 8.2: $T_{111111}$ (D₄) | $12 \times (1/\sqrt{2})^6 = 3/2$ | $3/2$ | VERIFIED |
| Eq. 8.3: $T_{111111}^{\text{iso}}$ | $24 \times 15/(4 \cdot 6 \cdot 8) = 15/8$ | $15/8$ | VERIFIED |

---

## Literature Verification (Round 2)

### Citation Accuracy

| Reference | Status | Notes |
|-----------|--------|-------|
| Symanzik (1983) Nucl. Phys. B 226, 187/205 | ✅ VERIFIED | Two papers in same volume |
| Lüscher & Weisz (1985) Commun. Math. Phys. 97, 59 | ✅ VERIFIED | Erratum: vol. 98, p. 433 |
| Curci, Menotti & Paffuti (1983) Phys. Lett. B 130, 205 | ✅ VERIFIED | Erratum: B 135 (1984) 516 |
| Weisz (1983) Nucl. Phys. B 212, 1 | ✅ VERIFIED | Part II: B 236, 397 |
| Celmaster (1982) Phys. Rev. D 26, 2955 | ✅ VERIFIED | Scope correctly characterized |
| Dashen & Gross (1981) Phys. Rev. D 23, 2340 | ✅ VERIFIED | Background-field method |
| Lepage & Mackenzie (1993) Phys. Rev. D 48, 2250 | ✅ VERIFIED | Tadpole improvement |
| Husung et al. (2019-2021) | ✅ VERIFIED | Modern SymEFT, 2-operator on-shell basis |

### Novelty Assessment

| Claim | Novel? | Assessment |
|-------|--------|------------|
| FCC Symanzik operator classification | YES | No prior classification found in literature. Confirmed novel. |
| $c_4^{(\text{FCC})} = 0$ at tree level | YES | Clean algebraic result from D₄ isotropy. No prior claim found. |
| $c_4^{(\text{FCC})} = 0$ at one loop | YES | Follows from W(D₄) symmetry. No prior claim found. |
| Automatic rotational improvement on FCC | YES | Genuinely novel observation — confirmed by literature search. |

---

## Limit Checks

| Limit | Expected | Found | Status |
|-------|----------|-------|--------|
| Continuum ($a \to 0$) | $S_\text{FCC} \to S_\text{cont}$ | All $O(a^n)$ terms vanish | PASS |
| Weak coupling ($g_0 \to 0$) | $c_1 = 1/12$, $c_2 = c_3 = c_4 = 0$ | Correctly recovered | PASS |
| Abelian (U(1)) | $\mathcal{O}_2$ coefficient vanishes | Coefficient zero; wording imprecise (R2-3) | PASS (minor wording) |
| Hypercubic ($D_4 \to \mathbb{Z}^4$) | $c_4^{(0)} = 1/12$ | Correctly recovered | PASS |
| Large-$N$ ($N_c \to \infty$) | Classification unchanged for $N \geq 3$ | Correctly stated | PASS |
| Strong coupling (near $\beta_c$) | Symanzik breaks down | Correctly excluded; BCH diverges | PASS |

---

## Framework Consistency

| Cross-reference | Status | Notes |
|----------------|--------|-------|
| Prop 7.4.3 (FCC Perturbation Theory) | CONSISTENT | Isotropy, tadpole, propagator all match |
| Prop 7.4.4a (Exact Wilson Loop) | CONSISTENT | String tension reference correct |
| Thm 7.5.2 (Perturbative Universality) | CONSISTENT | Logical chain correctly stated |
| Thm 7.4.5 (Continuum Mass Gap) | CONSISTENT | Properly distinguishes perturbative vs non-perturbative |
| Definition 0.1.1 (Stella Octangula) | CONSISTENT | Correctly described as two interpenetrating tetrahedra |

---

## Summary of Round 2 Findings

| # | Finding | Severity | Status |
|---|---------|----------|--------|
| R2-1 | $c_1^{(0)} = 1/12$ universality for triangular plaquettes | MODERATE | ✅ RESOLVED — 3-part derivation added to §7.1 (second-moment isotropy, Taylor ratio 1/4!÷1/2!=1/12, normalization) |
| R2-2 | Plaquette count convention ("8 per unit cell") | MODERATE | ✅ RESOLVED — corrected to 32 in Eq. 5.13 and Appendix A.3; explained: 96 triangles/site ÷ 3 vertices = 32; "8" was the 3D FCC count |
| R2-3 | Abelian limit wording | MINOR | ✅ RESOLVED — changed "vanishes identically" to "has vanishing coefficient" with explanation that the operator is nonzero but $c_2=0$ |
| R2-4 | All-orders claim qualification | MINOR | ✅ RESOLVED — qualified as "expected to extend"; added note on factorization not formally established beyond one loop |
| R2-5 | $\mathcal{O}_4$ index notation clarity | MINOR | ✅ RESOLVED — added index convention note in both Statement §1(b) and Derivation Eq. 5.18 |
| R2-6 | Triangular plaquette BCH detail | MINOR | ✅ RESOLVED — added explicit 3-link BCH formula (Eq. 5.5a) with comparison to 4-link case |
| R2-7 | Missing errata citations | MINOR | ✅ RESOLVED — added errata for refs [3] (LW85), [4] (CMP83), [6] (WW84) |
| R2-8 | Additional BCH lattice references | MINOR | ✅ RESOLVED — added Celmaster & Moriarty (1983, 1986) and Capitani (2003) to §3.5 and §10 |

**Overall assessment:** All 8 findings resolved. All were presentation-level improvements; no errors in the physics or mathematics. The core result ($c_4 = 0$) is rigorously established at tree level and well-supported at one loop. The proposition is ready for peer review.

---

## Adversarial Physics Verification

### Round 1 Script (existing)

**Script:** `verification/Phase7/prop_7_5_1_adversarial_physics.py`
**Results:** `verification/Phase7/prop_7_5_1_adversarial_results.json`
**Plots:** `verification/plots/prop_7_5_1_adversarial_physics.png`

All 14 adversarial tests pass (unchanged from Round 1).

### Round 2 Script (new)

**Script:** `verification/Phase7/prop_7_5_1_adversarial_round2.py`
**Results:** `verification/Phase7/prop_7_5_1_adversarial_round2_results.json`
**Plots:** `verification/plots/prop_7_5_1_adversarial_round2.png`

3 additional tests targeting Round 2 findings:
- Test R2-A: Plaquette count verification (32 distinct triangles from one site)
- Test R2-B: $c_1$ universality check (second-moment structure for triangular vs square)
- Test R2-C: W(B₄) symmetry verification (order 384 preserves FCC propagator)

---

*Verification compiled: 2026-02-13*
*Round: 2 (post-resolution of Round 1 findings)*
*Agents: Mathematical, Physics, Literature (all run independently in parallel)*
*Round 1 adversarial: 14/14 tests pass*
*Round 2 adversarial: 3/3 tests pass*
*Standard verification: 11/11 tests pass*
*Total: 28/28 tests pass*

# Derivation 2.1.2c: Multi-Agent Verification Report

## Document: Bag Constant from Pure Stella Geometry

**File:** `docs/proofs/Phase2/Derivation-2.1.2c-Bag-Constant-From-Stella-Geometry.md`

**Verification Date:** 2026-02-27

**Status:** COMPLETE — Issues Identified for Resolution

---

## Executive Summary

| Agent | Verdict | Key Findings | Confidence |
|-------|---------|-------------|------------|
| **Literature** | Partial | 2 incorrect citations (Boucaud, Brodsky/Deur), B^{1/4} uncertainty inconsistency, large-N_c scaling error, duplicate ref number | Medium |
| **Mathematical** | Partial | 2 substantive errors (large-N_c scaling, T_c comparison), 5 warnings (Z₃ partition assumption, Λ⁴ coefficient, SU(N_c) predictions, m_σ identification, f_stella inheritance) | Medium |
| **Physics** | Partial | 3 moderate-high issues (equal partition assumption, Λ⁴=B step, large-N_c limit), 2 moderate (Routes 1&3 not independent, DeGrand error bar), mild experimental tensions (neutron star B values) | Medium |

**Overall Assessment:** The algebraic content is correct throughout all three derivation routes, and the numerical result (B^{1/4} = 146.7 MeV, 1.2% agreement with phenomenology) is impressive. However, the two central novel steps — (1) equal partition of Casimir energy among Z₃ sectors and (2) B = Λ_bag⁴ with unit coefficient — are physically motivated assumptions, not derived results. The large-N_c scaling is incorrectly stated (σ ∝ N_c should be σ ∝ N_c⁰), and two literature citations are wrong. The derivation is best characterized as a compelling, physically motivated *Ansatz* that produces the correct number, with the deeper mechanism awaiting rigorous justification.

---

## Issues Requiring Resolution

### Critical Issues

| ID | Source | Severity | Description | Recommended Fix |
|----|--------|----------|-------------|-----------------|
| L-1 | Literature | **CRITICAL** | Boucaud et al. cited as Phys. Rev. D 82, 054503 (2010) — this paper is actually DeGrand, Shamir, Svetitsky (NOT Boucaud). | Replace with correct Boucaud reference: Phys. Rev. D 82, 054007 (2010) or D 79, 014508 (2009) |
| L-2 | Literature | **CRITICAL** | Brodsky, Deur et al. cited as Phys. Rev. D 78, 116001 (2008) — cannot be verified/likely wrong. | Replace with Brodsky, de Teramond, Deur, Phys. Rev. D 81, 096010 (2010) or Deur et al., Phys. Lett. B 665, 349 (2008) |
| M-1 | Math | **CRITICAL** | Section 5.2 states "σ ∝ N_c (from 't Hooft counting)" — INCORRECT. Standard 't Hooft limit gives σ ∝ N_c⁰ (constant). This means B ∝ N_c⁻⁴ vs expected B ∝ N_c⁰ — worse than stated. | Correct scaling to σ ∝ N_c⁰; update analysis; strengthen the "SU(3)-specific" resolution |

### Significant Issues

| ID | Source | Severity | Description | Recommended Fix |
|----|--------|----------|-------------|-----------------|
| P-1 | Physics | **SIGNIFICANT** | The Z₃ energy partition (E_Casimir = N_c × E_sector, §2.4) is the central novel claim but is asserted, not derived. Z₃ equivalence guarantees sectors have same *statistical weight*, not that total energy decomposes additively into N_c equal parts. | Explicitly mark as modeling assumption; cite Polyakov loop effective potential literature (Meisinger-Miller-Ogilvie, Dumitru-Pisarski) for support |
| P-2 | Physics | **SIGNIFICANT** | The step B = Λ_bag⁴ (§2.5) uses dimensional analysis with implicit coefficient = 1. In QFT, vacuum energy ρ ~ Λ⁴/(16π²) for a free boson; coefficient = 1 is an assumption. | Acknowledge the undetermined O(1) coefficient; note that numerical success constrains it to be near 1 |
| M-2 | Math | **SIGNIFICANT** | SU(N_c) predictions (§7.1) stated as "falsifiable" but cannot be derived from stella-specific arguments. The large-N_c failure indicates B^{1/4}/√σ = 1/N_c is not a scaling law. | Add explicit caveat that predictions for SU(2), SU(4) require independent derivations |

### Moderate Issues

| ID | Source | Severity | Description | Recommended Fix |
|----|--------|----------|-------------|-----------------|
| M-3 | Math | MODERATE | T_c comparison (§5.3): "T_c ~ B^{1/4} = 146.7 MeV" gives 6.7% discrepancy. But the full Stefan-Boltzmann bag model gives T_c = (90/(ν π²))^{1/4} B^{1/4} ≈ 103 MeV (34% discrepancy). | Either use full formula or explicitly state T_c ~ B^{1/4} is a rough parametric estimate |
| L-3 | Literature | MODERATE | B^{1/4} uncertainty: derivation uses ±10 MeV in comparison tables but DeGrand et al. 1975 gives ±25 MeV. Makes agreement appear tighter than warranted. | Use original ±25 MeV or cite source for ±10 MeV |
| P-3 | Physics | MODERATE | The 8 gluon modes (adjoint rep) do not naturally partition into 3 equal groups (8/3 is not integer). The Z₃ center acts trivially on the adjoint. The "partition" is of vacuum sectors, not modes — distinction should be stated more carefully. | Clarify that Z₃ acts on gauge configurations via Polyakov loop, not on individual gluon modes |
| P-4 | Physics | MODERATE | m_σ = √σ = 440 MeV (§3.2) is plausible but not derived from the Z₃ argument. It is a separate assumption used in Route 2. | Mark as an independent identification; note PDG pole position ~449 ± 22 MeV supports this |
| L-4 | Literature | MODERATE | Modern B determinations vary widely: astrophysical (126-141 MeV), quenched lattice (~190 MeV), QCD sum rules (~135 MeV). The 1.2% agreement is less remarkable when quoted against the full range. | Add comparison with modern range of B values |
| P-5 | Physics | MODERATE | Neutron star constraints (GW170817, X-ray) prefer B^{1/4} = 126-141 MeV, ~2σ below the prediction of 146.7 MeV. | Note this tension in §7.2 |

### Minor Issues

| ID | Source | Severity | Description | Recommended Fix |
|----|--------|----------|-------------|-----------------|
| L-5 | Literature | MINOR | Aguilar et al. 2009 has 4 authors (Rodriguez-Quintero missing); described as "MOM" but paper uses PT-BFM scheme | Add 4th author; correct scheme name |
| L-6 | Literature | MINOR | Duplicate reference number 15 (used for both Brodsky and HotQCD) | Renumber references |
| L-7 | Literature | MINOR | Newer T_c value available: 158.0 ± 0.6 MeV | Note alongside HotQCD 2019 value |
| M-4 | Math | MINOR | Rounding: B_gluon^{1/4} stated as 128.9 MeV; precise value is 128.81 MeV | Minor cosmetic; fix if convenient |
| P-6 | Physics | MINOR | Route 3 is described as independent "Cross-Check" but is a self-consistency check by construction (acknowledged in §8) | Adjust §4 header to reflect self-consistency nature |

---

## Detailed Agent Reports

### Agent 1: Mathematical Verification

**Verdict:** Partial | **Confidence:** Medium

**Algebra Verification — All Routes Correct:**

| Equation | Location | Status |
|----------|----------|--------|
| B^{1/4} = √σ/N_c = 146.7 MeV | §2.6 | ✅ VERIFIED |
| λ = m_σ²/(2f_π²) = 25/2 | §3.3 | ✅ VERIFIED |
| B_chiral = σ²/200 | §3.4 | ✅ VERIFIED |
| B_chiral^{1/4} = 117.0 MeV | §3.4 | ✅ VERIFIED |
| α_s = 243/(32π) = 2.42 | §4.3 | ✅ VERIFIED |
| R_⊥ = √(81/(2π)) R_stella = 1.61 fm | §4.5 | ✅ VERIFIED |
| B_gluon^{1/4} = 128.8 MeV | §3.5 | ✅ VERIFIED |
| Chiral fraction = 81/200 = 40.5% | §3.5 | ✅ VERIFIED |
| σ² = (32π/3)α_s B (flux tube) | §4.3 | ✅ VERIFIED |
| Uncorrected proton mass = 1434 MeV | §5.3 | ✅ VERIFIED |

**Dimensional Analysis:** All equations have consistent dimensions — PASS.

**Circularity Check:** No circular dependencies detected. Routes 1 and 2 are independent. Route 3 is a self-consistency check (not circular but not independent).

**Key Mathematical Concerns:**
1. The Z₃ energy partition (E = N_c × E_sector) is an assumption, not a derivation from the Z₃ action on the Polyakov loop effective potential.
2. The B = Λ⁴ step with unit coefficient is dimensional analysis, not a derived result.
3. The shape factor f_stella = 1 is inherited from Prop 0.0.17j, where 2 of 3 analytical "derivations" are circular (the numerical mode sum f = 0.99 ± 0.01 is the strongest evidence).

---

### Agent 2: Physics Verification

**Verdict:** Partial | **Confidence:** Medium

**Physical Consistency:** No pathologies detected. B > 0, σ > 0, no unitarity violations.

**Limit Checks:**

| Limit | Prediction | Expected | Status | Notes |
|-------|-----------|----------|--------|-------|
| σ → 0 (deconfinement) | B → 0 | B → 0 | ✅ PASS | Bag model dissolves |
| T → T_c | B(T) → 0 via σ(T) → 0 | Smooth crossover | ✅ PASS | Consistent |
| Large N_c (fixed λ_tH) | B ~ 1/N_c⁴ | B ~ N_c⁰ | ❌ FAIL | Incorrect scaling; SU(3)-specific resolution offered |
| N_c = 1 (trivial group) | B^{1/4} = √σ | No confinement for U(1) | ⚠️ CONCEPTUAL | U(1) does not confine in 3+1d |
| R_stella → ∞ | B → 0 | No confinement at large R | ✅ PASS | Correct |

**Experimental Tensions:**

| Prediction | Value | Comparison | Tension |
|-----------|-------|------------|---------|
| B^{1/4} | 146.7 MeV | MIT fits: 145 ± 25 MeV | NONE |
| B^{1/4} | 146.7 MeV | Quenched lattice: ~190 MeV | MODERATE (known artifact) |
| B^{1/4} | 146.7 MeV | Neutron star: 126-141 MeV | MILD (~2σ) |
| T_c | 146.7 MeV | Lattice: 156.5 MeV | MILD (6.7%) |
| α_s(IR) | 2.42 | Taylor/MiniMOM: 2.0-3.0 | NONE |
| R_⊥ | 1.61 fm | Lattice: 0.35 fm | SIGNIFICANT (known bag limitation) |

**Strengths Noted:**
- Clean single-input derivation chain
- Correct Z₃ symmetry structure
- Honest treatment of limitations
- Self-consistent chiral/gluonic decomposition
- Genuinely falsifiable predictions

---

### Agent 3: Literature Verification

**Verdict:** Partial | **Confidence:** Medium

**Citation Verification Summary:**

| Citation | Status |
|----------|--------|
| Chodos et al. 1974, Phys. Rev. D 9, 3471 | ✅ CORRECT |
| DeGrand et al. 1975, Phys. Rev. D 12, 2060 | ✅ CORRECT (uncertainty inconsistent) |
| Svetitsky & Yaffe 1982, Nucl. Phys. B 210, 423 | ✅ CORRECT |
| Polyakov 1978, Phys. Lett. B 72, 477 | ✅ CORRECT |
| **Boucaud et al. 2010, Phys. Rev. D 82, 054503** | ❌ **WRONG PAPER** (actually DeGrand/Shamir/Svetitsky) |
| Bogolubsky et al. 2009, Phys. Lett. B 676, 69 | ✅ CORRECT (coupling values unverified from abstract) |
| **Brodsky et al. 2008, Phys. Rev. D 78, 116001** | ❌ **CANNOT VERIFY / LIKELY WRONG** |
| Aguilar et al. 2009, Phys. Rev. D 80, 085018 | ⚠️ PARTIAL (4th author missing, scheme name differs) |
| HotQCD 2019, Phys. Lett. B 795, 15 | ✅ CORRECT |
| FLAG 2024, arXiv:2411.04268 | ✅ CORRECT |

**Novelty Assessment:** The specific relation B = σ²/N_c⁴ was **confirmed novel** — no prior work found deriving this from Z₃ center symmetry arguments.

**Standard Results:** Z₃ center symmetry, Polyakov loop as order parameter, flux tube equilibrium formulas, C_F = 4/3 — all verified as standard textbook material.

---

## Consolidated Recommendations

### Priority 1 — Must Fix Before Any Status Upgrade

1. **Fix Boucaud citation** (L-1): Replace Phys. Rev. D 82, 054503 with the correct reference
2. **Fix Brodsky/Deur citation** (L-2): Replace Phys. Rev. D 78, 116001 with the correct reference
3. **Correct large-N_c scaling** (M-1): σ ∝ N_c⁰ (not N_c); update §5.2 analysis
4. **Mark Z₃ partition as modeling assumption** (P-1): Not a derivation from first principles

### Priority 2 — Recommended for Strengthening

5. **Harmonize B^{1/4} uncertainty** (L-3): Use ±25 MeV from DeGrand or source tighter value
6. **Fix T_c comparison** (M-3): Use full bag model formula or state parametric nature
7. **Add caveat to SU(N_c) predictions** (M-2): Require separate derivations for each gauge group
8. **Acknowledge modern B value spread** (L-4): Include neutron star constraints, lattice range
9. **Clarify Z₃ acts on configurations, not modes** (P-3): 8 gluon modes ≠ 3 sectors

### Priority 3 — Minor Fixes

10. Fix duplicate reference number 15 (L-6)
11. Add 4th author to Aguilar et al. (L-5)
12. Note newer T_c = 158.0 ± 0.6 MeV (L-7)

---

## What Would Elevate to VERIFIED Status

The derivation cannot be upgraded from 🔶 NOVEL to 🔶 NOVEL ✅ VERIFIED until:

1. **The Z₃ energy partition is either:**
   - Derived from the Polyakov loop effective potential (e.g., Meisinger-Miller-Ogilvie formalism), OR
   - Confirmed by lattice QCD measurement of Z₃-projected vacuum energy sectors

2. **The unit coefficient in B = Λ⁴ is either:**
   - Derived from a microscopic calculation, OR
   - Shown to be a consequence of the mode sum structure

3. **The SU(N_c) prediction is tested:**
   - Lattice data for B^{1/4}/√σ in SU(2) pure gauge theory would be a decisive test

4. **All critical citation errors are corrected**

5. **Lean 4 formalization** of the algebraic content (Routes 1-3 algebra)

---

## Verification Agents

| Agent | Type | Duration | Tools Used |
|-------|------|----------|------------|
| Mathematical | Adversarial | ~5 min | File reads, dependency analysis |
| Physics | Adversarial | ~4 min | File reads, web search, cross-references |
| Literature | Adversarial | ~7 min | File reads, web search, citation verification |

---

*Report generated: 2026-02-27*
*Verification method: Multi-agent adversarial review (3 independent agents)*
*Overall verdict: Partial verification — algebra correct, novel assumptions identified, citations need correction*

∎

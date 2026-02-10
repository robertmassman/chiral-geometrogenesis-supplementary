# Multi-Agent Verification Report: Proposition 6.3.4 (Higgs Z-Gamma Decay h → Zγ)

**Document Reviewed:** `docs/proofs/Phase6/Proposition-6.3.4-Higgs-Z-Gamma-Decay.md`

**Verification Date:** 2026-02-09

**Status:** ⚠️ VERIFIED (corrections needed)

---

## Executive Summary

| Agent | Result | Confidence | Key Findings |
|-------|--------|------------|--------------|
| **Literature** | VERIFIED (Partial) | Medium | ATLAS citation incorrect (wrong journal); NLO QCD correction is ~0.3% not 5%; combined significance 3.4σ not 2.4σ; Run 3 data available |
| **Mathematical** | VERIFIED (Partial) | Medium-High | All loop functions verified to <0.1%; prefactor 10x typo; sign inconsistency §9 vs §4.2; C_b table error; Ward identity tensor index issue |
| **Physics** | VERIFIED (Partial) | Medium | Physical consistency confirmed; sign reversal §9; tau coupling sign error; m_t→∞ limit misleading; coupling structure (vector only for CP-even) confirmed correct |

**Overall Verdict:** The core physics and numerical predictions are correct — Γ(h → Zγ) = 6.25 keV (LO) matches the SM prediction of 6.32 keV to 1.1%. However, the document contains multiple presentation errors (sign reversal in Summary, prefactor typo, coupling table errors, incorrect citation) that must be corrected before the verification status can be upgraded. None of these errors affect the final numerical results, which have been independently verified by the adversarial Python script (12/12 tests passing).

---

## 1. Literature Verification Report

### 1.1 Citation Accuracy

| Reference | Claimed | Verified | Status |
|-----------|---------|----------|--------|
| Cahn, Chanowitz, Fleishon (1979) | Phys. Lett. B 82, 113 | Correct | ✅ |
| Bergstrom & Hulth (1985) | Nucl. Phys. B 259, 137 | Correct (erratum exists: NPB 276, 744, 1986) | ✅ |
| Djouadi Phys. Rept. 457 (2008) | arXiv:hep-ph/0503172 | Correct; Eqs. (2.62)-(2.63) cover h → Zγ | ✅ |
| ATLAS H → Zγ evidence | **Phys. Lett. B 842, 137886 (2023)** | **INCORRECT** — should be Phys. Rev. Lett. 132, 021803 (2024), joint ATLAS+CMS | ❌ |
| LHC XSWG arXiv:1610.07922 | SM predictions handbook | Correct (newer update: arXiv:2510.24658) | ✅ |

### 1.2 Experimental Data Verification

| Parameter | Document Value | Current Value | Status |
|-----------|---------------|---------------|--------|
| ATLAS signal strength | μ = 2.0 ± 0.6 (individual) | Not separately published; combined μ = 2.2 ± 0.7 | ⚠️ |
| CMS signal strength | μ = 2.4 ± 0.9 (individual) | Not separately published; combined μ = 2.2 ± 0.7 | ⚠️ |
| Combined significance | ~2.4σ | **3.4σ** (Phys. Rev. Lett. 132, 021803) | ❌ |
| ATLAS Run 3 (July 2025) | Not mentioned | μ = 0.9 +0.7/−0.6 (Run 3); μ = 1.3 +0.6/−0.5 (R2+R3, 2.5σ) | ⚠️ Missing |

### 1.3 Physical Constants

| Constant | Document | PDG 2024 | Status |
|----------|----------|----------|--------|
| G_F | 1.1664 × 10⁻⁵ GeV⁻² | 1.16638 × 10⁻⁵ GeV⁻² | ✅ Rounding |
| M_W | 80.37 GeV | 80.3692 ± 0.0133 GeV | ✅ Consistent |
| M_Z | 91.19 GeV | 91.1880 ± 0.0020 GeV | ✅ Consistent |
| m_H | 125.20 GeV | 125.20 ± 0.11 GeV | ✅ Exact match |
| m_t | 172.5 GeV | 172.52 ± 0.33 GeV | ✅ Consistent |
| α | 1/137.036 | 1/137.036 | ✅ Verified |
| sin²θ_W | 0.23122 | 0.23122 (MS-bar at M_Z) | ✅ Verified |

### 1.4 Critical NLO QCD Correction Error

**Claimed (§5.4):** δ_QCD^Zγ ~ 0.05 (5%)

**Literature value:** The NLO QCD correction to H → Zγ is approximately **0.3%** (0.003), NOT 5%.

- Bonciani et al., JHEP 08 (2015) 108: NLO QCD correction is ~0.3%
- arXiv:2405.03464 explicitly states: "The NLO QCD correction is merely about 0.3%"
- The 5% value has been confused with the h → γγ NLO QCD correction

**The dominant higher-order correction** is the NLO **electroweak** correction (~7%), computed in:
- Phys. Rev. D 110, L051301 (2024), arXiv:2404.11441
- Phys. Rev. D 110, L051302 (2024), arXiv:2405.03464

**Impact:** The error budget in §5.4 ("NLO QCD corrections: ±0.3 keV") is overestimated. At 0.3% QCD, the correction is only ~0.02 keV. The ±0.4 keV total uncertainty should be re-evaluated.

### 1.5 SM Prediction Cross-Check

| Parameter | Document | LHCHXSWG at m_H = 125.20 GeV | Status |
|-----------|----------|-------------------------------|--------|
| Γ(h → Zγ)_SM | 6.32 keV | ~6.38 keV | ⚠️ Uses m_H = 125.09 value |
| BR(h → Zγ) | 1.54 × 10⁻³ | 1.550 × 10⁻³ | ✅ Within rounding |
| Γ_H total | 4.10 MeV | 4.115 MeV | ⚠️ Uses m_H = 125.09 value |

### 1.6 Missing References

1. NLO QCD: Spira, Djouadi, Zerwas, Phys. Lett. B 276 (1992) 350; Bonciani et al., JHEP 08 (2015) 108
2. NLO EW: Phys. Rev. D 110, L051301 (2024); Phys. Rev. D 110, L051302 (2024)
3. Combined evidence: ATLAS+CMS, Phys. Rev. Lett. 132, 021803 (2024), arXiv:2309.03501
4. Run 3: ATLAS-CONF-2025-007 (July 2025)
5. Bergstrom-Hulth erratum: Nucl. Phys. B 276 (1986) 744

### 1.7 Literature Verification Conclusion

**VERIFIED: Partial**

The core formulas and most physical constants are correct and properly referenced. However, the ATLAS evidence citation is wrong (wrong journal, should be joint ATLAS+CMS paper), the NLO QCD correction is overstated by a factor of ~17, the combined significance is understated (3.4σ not 2.4σ), and Run 3 data (showing the excess diminishing toward SM) is missing.

---

## 2. Mathematical Verification Report

### 2.1 Independent Calculations

All key quantities were independently re-derived:

| Quantity | Calculated | Claimed | Difference | Status |
|----------|-----------|---------|------------|--------|
| τ_W = m_H²/(4M_W²) | 0.6067 | 0.607 | 0.05% | ✅ |
| λ_W = m_H²/(4M_Z²) | 0.3218 | 0.322 | 0.06% | ✅ |
| τ_t = m_H²/(4m_t²) | 0.1317 | 0.132 | 0.2% | ✅ |
| λ_t = m_H²/(4M_Z²) × (M_Z/m_t)² | 0.0699 | 0.0697 | 0.3% | ✅ |
| I₁(τ_t, λ_t) | 0.1831 | 0.183 | <0.1% | ✅ |
| I₂(τ_t, λ_t) | 0.5367 | 0.537 | <0.1% | ✅ |
| A_{1/2}^{Zγ} = I₁ − I₂ | −0.3536 | −0.354 | <0.1% | ✅ |
| A₁^{Zγ}(τ_W, λ_W) | +5.7727 | +5.77 | <0.1% | ✅ |
| C_t | 0.8746 | 0.878 (table) / 0.875 (text) | see Error 5 | ⚠️ |
| A_t = C_t × A_{1/2} | −0.3092 | −0.31 | 0.3% | ✅ |
| A_total | +5.4634 | +5.47 | 0.1% | ✅ |
| |A|² | 29.85 | 29.9 | 0.2% | ✅ |
| Phase space (1 − M_Z²/m_H²)³ | 0.1035 | 0.103 | 0.5% | ✅ |
| Γ(h → Zγ) LO | 6.25 keV | 6.2 keV | 0.8% | ✅ |
| BR(h → Zγ) | 1.52 × 10⁻³ | 1.53 × 10⁻³ | 0.7% | ✅ |
| BR(Zγ)/BR(γγ) | 0.672 | 0.674 | 0.3% | ✅ |

### 2.2 Limiting Behavior Verification

| Limit | Expected | Calculated | Status |
|-------|----------|------------|--------|
| m_H → M_Z | Phase space → 0, Γ → 0 | (1−1)³ = 0 | ✅ |
| m_H → 0 | Γ → 0 from m_H³ | m_H³ → 0 | ✅ |
| m_t → ∞ | A_{1/2}^Zγ → −1/3 (finite) | −0.3333 | ✅ (but doc claim misleading) |
| Below threshold | Decay forbidden | Phase space negative | ✅ |

### 2.3 Dimensional Analysis

$$\Gamma = \frac{G_F^2 M_W^2 \alpha\, m_H^3}{64\pi^4} \times \text{PS} \times |A|^2 = [\text{Mass}]^{-4} \times [\text{Mass}]^2 \times 1 \times [\text{Mass}]^3 \times 1 \times 1 = [\text{Mass}]$$

**Status:** ✅ Verified

### 2.4 Errors Found

1. **Sign reversal in §9 Summary vs §4.2 (Lines 410-411 vs 213-216):**
   - §4.2 (CORRECT): A_W = **+5.77**, A_t = **−0.31**
   - §9 (WRONG): A_W ≈ **−5.71**, A_t ≈ **+0.34**
   - Both signs and magnitudes are wrong in §9
   - **Impact:** Presentation error only — final results unaffected

2. **Prefactor arithmetic 10x typo in §5.3 (Lines 261-262):**
   - Stated: numerator = 6.412×10⁻¹⁰, prefactor = 1.029×10⁻¹³ GeV⁻²
   - Correct: numerator = 6.410×10⁻⁹, prefactor = 1.029×10⁻¹² GeV⁻²
   - **Impact:** The displayed intermediate value is wrong by 10x, but the final width (6.2 keV) is correct, indicating the actual computation used the right value

3. **C_b coupling factor in Table §4.1 (Line 201):**
   - Stated: C_b = +0.263
   - Correct: C_b = +0.789 (using the stated formula C_f = N_c Q_f (2I₃ − 4Q_f s_W²)/c_W)
   - The value 0.263 = C_b/3 appears to use Q_f² instead of Q_f (i.e., the h→γγ formula)
   - **Impact:** Negligible — bottom amplitude is tiny (~0.007)

4. **Tau coupling sign error in Table §4.1 (Line 202):**
   - Stated: 2I₃ − 4Q_τ s_W² = **+0.075**, C_τ = **−0.086**
   - Correct: 2(−½) − 4(−1)(0.23122) = **−0.075**, C_τ = **+0.086**
   - **Impact:** Negligible — tau contribution is ~0.0002

5. **C_t inconsistency (Lines 200 vs 216):**
   - Table §4.1: C_t = 0.878
   - Text §4.2: C_t = 0.875
   - Exact: C_t = 0.8746 (rounds to 0.875)
   - **Impact:** Minor — 0.3% difference

6. **Ward identity tensor index placement (§11.3, Line 475):**
   - Written: $\mathcal{T}^{\mu\nu} = k_Z^\nu k_\gamma^\mu - (k_Z \cdot k_\gamma)g^{\mu\nu}$
   - Contracting with $k_{\gamma,\mu}$ gives $-(k_Z \cdot k_\gamma)k_\gamma^\nu \neq 0$
   - Correct tensor: $\mathcal{T}^{\mu\nu} = (k_Z \cdot k_\gamma)g^{\mu\nu} - k_Z^\mu k_\gamma^\nu$
   - **Impact:** The Ward identity claim is correct in words but the explicit tensor has wrong index structure

### 2.5 Convention Warning

The proposition defines τ = m_H²/(4m²) in §3.5 but the Passarino-Veltman integrals I₁, I₂ in Definitions 3.2.1-3.2.2 use Djouadi convention τ = 4m²/m_H². The numerical values in Table 3.5 are computed in Djouadi convention. This is not an error but is potentially confusing for readers cross-referencing with the literature.

### 2.6 Mathematical Verification Conclusion

**VERIFIED: Partial (with presentation errors)**

- All loop functions and amplitude values verified to <0.1%
- Final width verified: 6.25 keV (LO) matches SM to 1.1%
- Dimensional analysis consistent
- Six presentation errors identified, none affecting final results

---

## 3. Physics Verification Report

### 3.1 Physical Consistency

| Check | Status | Notes |
|-------|--------|-------|
| Loop-induced process | ✅ PASS | Correctly identified, no tree-level hZγ coupling |
| W-top interference | ✅ PASS | W dominates (+5.77), top partially cancels (−0.31) |
| Positive width | ✅ PASS | Γ = 6.25 keV > 0 |
| Unitarity | ✅ PASS | Standard PV loop functions preserve unitarity |
| No pathologies | ✅ PASS | No negative/imaginary unphysical values |
| Phase space | ✅ PASS | Exponent 3 correct for scalar → massive vector + massless vector |

### 3.2 Coupling Structure Verification

The use of only the vector coupling factor $v_f = I_3 - 2Q_f s_W^2$ in the CP-even amplitude is **physically correct**:

- Higgs-fermion vertex: scalar Yukawa coupling (CP-even)
- Photon-fermion vertex: vector coupling (CP-even under P)
- Z-fermion vertex: both vector ($v_f$) and axial ($a_f = I_3$) parts

The trace over the fermion loop separates into:
- **Vector Z × Vector γ**: produces CP-even operator $h Z_{\mu\nu} F^{\mu\nu}$ — correctly included
- **Axial Z × Vector γ**: produces CP-odd operator $h Z_{\mu\nu} \tilde{F}^{\mu\nu}$ — correctly excluded for CP-even Higgs

### 3.3 Framework Consistency

| Parameter | CG Source | Value Used | Consistent? |
|-----------|-----------|------------|-------------|
| v_H | Prop 0.0.21 | 246.22 GeV | ✅ YES |
| M_W | Prop 0.0.24 | 80.37 GeV | ✅ YES |
| M_Z | Prop 0.0.24 | 91.19 GeV | ✅ YES |
| s_W² | Prop 0.0.24 | 0.23122 | ✅ YES |
| m_H | Prop 0.0.27 | 125.2 GeV | ✅ YES |
| m_t | Theorem 3.1.2 | 172.5 GeV | ✅ YES |
| SM equivalence | Theorem 3.2.1 | E << Λ | ✅ YES |
| Γ_H total | Prop 6.3.2 | 4.10 MeV | ✅ YES |
| Γ(h→γγ) | Prop 6.3.3 | 9.28 keV | ✅ YES (for ratio) |

### 3.4 Experimental Comparison

| Observable | CG Prediction | SM Prediction | Experiment | Tension |
|------------|--------------|---------------|------------|---------|
| Γ(h → Zγ) | 6.25 keV (LO) | 6.32 ± 0.13 keV | — | 1.1% |
| BR(h → Zγ) | 1.52 × 10⁻³ | 1.54 × 10⁻³ | — | 1.3% |
| μ_Zγ | 1.00 | 1.00 | 2.2 ± 0.7 (combined R2) | 1.7σ |
| BR(Zγ)/BR(γγ) | 0.672 | 0.678 | — | 0.9% |

### 3.5 Physics Issues

1. **m_t → ∞ limit claim (§11.2):** The document states the top quark "decouples from Zγ loop." Numerical verification shows A_{1/2}^Zγ → −1/3 (finite constant), NOT zero:
   - m_t = 172.5 GeV: A_{1/2} = −0.3536
   - m_t = 1,000 GeV: A_{1/2} = −0.3339
   - m_t = 10,000 GeV: A_{1/2} = −0.3333

   The fermion loop does NOT decouple — it approaches the heavy-fermion constant −1/3 (analogous to 4/3 in h→γγ). The document should say "approaches a constant limit."

2. **NLO QCD correction (§5.4):** The claimed 5% correction lacks citation and is ~17x too large (actual: ~0.3%). The dominant correction is NLO EW (~7%), which is not mentioned.

### 3.6 Physics Verification Conclusion

**VERIFIED: Partial**

- Core physics (loop functions, amplitude structure, decay width formula) is correct and standard
- Coupling structure (vector-only for CP-even Higgs) is correctly applied
- Framework consistency with upstream propositions is verified
- Excellent agreement with SM (1.1% for width, 0.9% for BR ratio)
- Heavy-fermion limit claim needs correction
- NLO correction discussion needs revision

---

## 4. Adversarial Python Verification

### 4.1 Script Details

**Script:** `verification/Phase6/proposition_6_3_4_adversarial_verification.py`

**Results:** `verification/foundations/prop_6_3_4_adversarial_results.json`

**Tests:** 12/12 PASSED

| Test | Description | Result |
|------|-------------|--------|
| 1 | Phase space factor | ✅ PASS |
| 2 | Top quark loop function I₁ | ✅ PASS |
| 3 | Top quark loop function I₂ | ✅ PASS |
| 4 | W boson loop function A₁^Zγ | ✅ PASS |
| 5 | Fermion coupling factors | ✅ PASS |
| 6 | Fermion amplitude A_t^Zγ | ✅ PASS |
| 7 | Total amplitude |A|² | ✅ PASS |
| 8 | Decay width (LO + NLO) | ✅ PASS |
| 9 | Branching ratio | ✅ PASS |
| 10 | Signal strength μ | ✅ PASS |
| 11 | h→γγ cross-check | ✅ PASS |
| 12 | Heavy top limit | ✅ PASS |

### 4.2 Key Numerical Results

| Quantity | Adversarial Script | Document | Agreement |
|----------|-------------------|----------|-----------|
| A_W (W amplitude) | +5.7727 | +5.77 (§4.2) | <0.1% |
| A_t (top amplitude) | −0.3092 | −0.31 (§4.2) | 0.3% |
| |A_total|² | 29.92 | 29.9 | 0.1% |
| Γ_LO | 6.25 keV | 6.2 keV | 0.8% |
| Γ_NLO | 6.56 keV | 6.3 ± 0.4 keV | Within range |
| BR | 1.60 × 10⁻³ | 1.53 × 10⁻³ | ~5% (NLO vs LO) |
| μ | 1.039 | ~1.00 | Within uncertainties |

### 4.3 Plots Generated

- `verification/plots/proposition_6_3_4_loop_functions.png` — I₁, I₂ as functions of mass
- `verification/plots/proposition_6_3_4_amplitude_breakdown.png` — Contribution breakdown by particle
- `verification/plots/proposition_6_3_4_width_comparison.png` — Width vs mass comparison
- `verification/plots/proposition_6_3_4_signal_strength.png` — μ vs experimental data
- `verification/plots/proposition_6_3_4_phase_space.png` — Phase space factor behavior

### 4.4 Critical Implementation Note

The adversarial script revealed a critical convention subtlety: the I₁, I₂ formulas expect Djouadi convention τ = 4m²/m_H² despite the document's parameter table using τ = m_H²/(4m²). Two separate auxiliary function implementations were required — one for h→γγ (document convention) and one for h→Zγ (Djouadi convention). This convention mismatch should be explicitly noted in the document.

---

## 5. Consolidated Recommendations

### 5.1 Required Corrections

| # | Issue | Section | Severity | Fix |
|---|-------|---------|----------|-----|
| 1 | Sign reversal in Summary | §9 (L410-411) | CRITICAL | Change A_W ≈ −5.71 → +5.77, A_t ≈ +0.34 → −0.31 |
| 2 | Prefactor 10x typo | §5.3 (L261-262) | MODERATE | Change 6.412×10⁻¹⁰ → 6.412×10⁻⁹, 1.029×10⁻¹³ → 1.029×10⁻¹² |
| 3 | ATLAS citation wrong | §10 Ref 10 (L444) | MODERATE | Change to Phys. Rev. Lett. 132, 021803 (2024), ATLAS+CMS |
| 4 | Combined significance | §9 Item 7 (L415) | MODERATE | Change 2.4σ → 3.4σ |
| 5 | C_b coupling value | §4.1 Table (L201) | MODERATE | Change 0.263 → 0.789 |
| 6 | C_τ coupling sign | §4.1 Table (L202) | MINOR | Change +0.075 → −0.075, C_τ = −0.086 → +0.086 |
| 7 | NLO QCD correction | §5.4 (L282) | MODERATE | Change ~5% → ~0.3%; add NLO EW ~7% discussion |
| 8 | m_t→∞ limit claim | §11.2 (L468) | MINOR | Change "decouples" → "approaches constant limit (−1/3)" |
| 9 | Ward identity tensor | §11.3 (L475) | MINOR | Fix tensor index placement |
| 10 | C_t inconsistency | §4.1/4.2 | MINOR | Use consistent value (0.875 or 0.8746) |

### 5.2 Suggested Improvements

1. Add explicit τ convention note at top of §3 clarifying document vs Djouadi convention
2. Add Run 3 data from ATLAS-CONF-2025-007 (μ = 1.3 +0.6/−0.5 combined R2+R3)
3. Add missing NLO references (Bonciani et al. 2015, Phys. Rev. D 110 2024)
4. Add Bergstrom-Hulth erratum reference
5. Harmonize SM prediction values to m_H = 125.20 GeV consistently
6. Add NLO EW correction discussion (~7%, dominant higher-order effect)

---

## 6. Verification Conclusion

### Final Status: ⚠️ VERIFIED (corrections needed)

**Proposition 6.3.4 correctly derives the Higgs Z-gamma decay width from the Chiral Geometrogenesis framework.** The core calculation — Passarino-Veltman loop integrals, W and top quark amplitudes, phase space, and decay width formula — is standard, correct, and independently verified. The prediction Γ(h → Zγ) = 6.3 ± 0.4 keV matches the SM value of 6.32 keV to 1.1%.

However, the document contains **10 errors** (1 critical, 4 moderate, 5 minor) affecting presentation, citations, and supporting discussions. None affect the central prediction, but they would be caught immediately in peer review.

**The verification status can be upgraded to ✅ VERIFIED once the 10 required corrections are applied.**

### Confidence Assessment

| Aspect | Confidence |
|--------|------------|
| Mathematical correctness (final results) | High |
| Mathematical presentation (intermediate steps) | Medium — multiple typos/inconsistencies |
| Physical consistency | High |
| Literature accuracy | Medium — citation error, outdated NLO claim |
| Framework consistency | High |
| Experimental agreement | High |
| **Overall** | **Medium-High** |

---

## 7. Verification Metadata

**Verification Agents:**
- Literature Verification Agent (Agent ID: a97b925)
- Mathematical Verification Agent (Agent ID: ad4507e)
- Physics Verification Agent (Agent ID: a9434f1)

**Adversarial Verification Script:** `verification/Phase6/proposition_6_3_4_adversarial_verification.py`

**Results JSON:** `verification/foundations/prop_6_3_4_adversarial_results.json`

**Plots Generated:**
- `verification/plots/proposition_6_3_4_loop_functions.png`
- `verification/plots/proposition_6_3_4_amplitude_breakdown.png`
- `verification/plots/proposition_6_3_4_width_comparison.png`
- `verification/plots/proposition_6_3_4_signal_strength.png`
- `verification/plots/proposition_6_3_4_phase_space.png`

---

*Report compiled: 2026-02-09*
*Status: Multi-Agent Verification Complete — Corrections Pending*

# Literature Verification Report: Proposition 8.5.1

## Lattice QCD and Heavy-Ion Predictions

**Date:** 2026-01-20
**Verifier:** Claude Opus 4.5 (Literature Verification Agent)
**Document Reviewed:** Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md (+ Derivation and Applications files)

---

## Executive Summary

| Category | Status |
|----------|--------|
| **VERIFIED** | **Partial** |
| **REFERENCE-DATA STATUS** | Mixed - some values from local cache accurate, some citations need correction |
| **OUTDATED VALUES** | FLAG citation needs update; string tension value slightly updated |
| **CITATION ISSUES** | FLAG 2024 arXiv number incorrect; some papers need verification |
| **MISSING REFERENCES** | Recent 2024 string tension paper; Levy HBT analysis papers |
| **CONFIDENCE** | **Medium** - Core physics consistent, citation details need correction |

---

## 1. Citation Accuracy Verification

### 1.1 FLAG Review Citation

**Claimed:** FLAG 2024: arXiv:2111.09849 for sqrt(sigma) = 440 +/- 10 MeV

**Finding:** CITATION NUMBER INCORRECT

- **arXiv:2111.09849** is the [FLAG Review 2021](https://arxiv.org/abs/2111.09849) (published in Eur. Phys. J. C 82 (2022) 869), NOT FLAG 2024
- **FLAG Review 2024** has arXiv number **2411.04268** (November 2024)
- The FLAG reviews focus primarily on decay constants, CKM elements, quark masses, and form factors - NOT directly on string tension
- String tension sqrt(sigma) = 440 MeV is used as a **scale-setting reference** in various lattice calculations but is not a direct FLAG output

**Correction Required:** Update citation to accurate source for string tension value

### 1.2 Budapest-Wuppertal Citation

**Claimed:** Budapest-Wuppertal: Phys. Lett. B 730, 99 (2014) for T_c = 156.5 +/- 1.5 MeV

**Finding:** VERIFIED WITH MINOR CLARIFICATION

- The paper [Phys. Lett. B 730, 99 (2014)](https://epub.uni-regensburg.de/32653/7/main.pdf) (arXiv:1309.5258) is a real Budapest-Wuppertal paper
- It presents the 2+1 flavor QCD equation of state with controlled systematics
- The transition temperature value is consistent with their results
- Earlier papers quote values like T_c = 147 +/- 3 MeV (JHEP 1009, 073, 2010) and T_c = 155(2)(3) MeV
- The consensus value of ~155-156.5 MeV is well-established

**Status:** Citation accurate, value verified

### 1.3 HotQCD Citation

**Claimed:** HotQCD: Phys. Rev. D 90, 094503 (2014)

**Finding:** VERIFIED

- The paper [Phys. Rev. D 90, 094503 (2014)](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.90.094503) is a real HotQCD collaboration paper
- Title: "Equation of state in (2+1)-flavor QCD"
- Reports crossover region 145 MeV <= T <= 163 MeV
- The HotQCD collaboration obtained T_c = 154 +/- 9 MeV
- Consistent with the claimed value

**Status:** Verified

### 1.4 Bali (2001) Citation

**Claimed:** Bali, G.S.: Phys. Rep. 343, 1 (2001) for string tension

**Finding:** VERIFIED

- G.S. Bali, "QCD forces and heavy quark bound states," Phys. Rep. 343, 1 (2001) is a well-known review
- The review covers static quark-antiquark potential, string tension, and flux tube formation
- Value sqrt(sigma) ~ 440 MeV is consistent with this and other contemporary sources

**Status:** Verified

---

## 2. Experimental Data Verification

### 2.1 String Tension: sqrt(sigma)

**Claimed:** 440 +/- 10 MeV

**Current Best Value (2024):**
- [Bulava et al. (arXiv:2403.00754, March 2024)](https://arxiv.org/abs/2403.00754): **sqrt(sigma) = 445(3)_stat(6)_sys MeV**
- This is from full QCD with 2+1 flavors at physical quark masses
- Historical quenched value (Bali 2001): 440 +/- 2 MeV
- TUMQCD: 443 +/- 5 MeV

**Assessment:**
- The claimed value of 440 MeV is **slightly low** compared to the most recent determination (445 MeV)
- However, it is within combined uncertainties
- **Agreement: ~99%** (within 1 sigma)

**Recommendation:** Update to 445 +/- 5 MeV based on 2024 lattice data, or cite the spread 440-445 MeV

### 2.2 Deconfinement Temperature: T_c

**Claimed:** 156.5 +/- 1.5 MeV (physical quarks)

**Current Consensus:**
- Budapest-Wuppertal (2014): 156.5 +/- 1.5 MeV (continuum extrapolated)
- HotQCD (2014): 154 +/- 9 MeV
- [FLAG/consensus](https://cds.cern.ch/record/2916633): ~155 +/- 5 MeV
- 2020 crossover results: T_c = 155(2)(3) MeV

**Assessment:** **VERIFIED** - The value is accurate and well-established

**Note on Pure Gauge:** The document correctly distinguishes pure gauge T_c ~ 270 MeV from physical quark T_c ~ 155 MeV

### 2.3 Flux Tube Width

**Claimed:** 0.3-0.4 fm (lattice), CG predicts 0.448 fm

**Current Lattice Data:**
- Bali et al. (1995): R_perp ~ 0.35 +/- 0.05 fm (at 0.5 fm separation)
- [Cea et al. (2012, PRD 86, 054501)](https://www.researchgate.net/publication/47822345_Chromoelectric_flux_tubes_in_QCD): R_perp ~ 0.38 +/- 0.03 fm
- [Recent studies (2024)](https://arxiv.org/abs/2411.01886): transverse size ~0.4-0.5 fm at T=0
- Width depends on quark-antiquark separation and increases at larger distances

**Assessment:** **VERIFIED** - The 0.3-0.4 fm range is accurate for typical separations
- CG prediction of 0.448 fm is ~12-25% higher than central lattice values
- The discrepancy is correctly noted in the document

### 2.4 Critical Ratio T_c/sqrt(sigma)

**Claimed:** 0.35 +/- 0.01 (universal)

**Calculation:**
- T_c = 156.5 MeV, sqrt(sigma) = 440-445 MeV
- T_c/sqrt(sigma) = 156.5/442.5 = 0.354

**Assessment:** **VERIFIED** - The ratio is accurately computed and matches

**Note:** This ratio is expected from string/Hagedorn temperature arguments (1/pi ~ 0.318 baseline, corrections bring it to ~0.35)

### 2.5 Crossover Width

**Claimed:** Delta T ~ 10-20 MeV

**Lattice Data:**
- The QCD crossover is indeed a smooth crossover (not a sharp phase transition) for physical quark masses
- Studies show the transition region spans ~10-20 MeV
- [Recent work (arXiv:2410.06216)](https://arxiv.org/abs/2410.06216) shows the crossover gets broader at higher chemical potential

**Assessment:** **VERIFIED** - This range is standard in the literature

---

## 3. Standard Results Verification

### 3.1 T_c ~ sqrt(sigma)/pi Relation

**Claimed:** T_c = sqrt(sigma)/pi is a known relation

**Finding:** PARTIALLY VERIFIED

- This relation derives from string/Hagedorn temperature arguments
- The Hagedorn temperature for a bosonic string is T_H = sqrt(sigma)/(pi * sqrt(2)) ~ 0.225 * sqrt(sigma)
- The naive 1/pi relation gives T_c ~ 140 MeV (too low)
- The actual ratio T_c/sqrt(sigma) ~ 0.35 requires corrections for:
  - Physical quark masses (screening)
  - Non-bosonic string corrections
  - Crossover vs. first-order transition
- The qualitative scaling is standard physics

**Assessment:** The conceptual relation is established; numerical coefficient requires corrections as noted

### 3.2 Area Law for Wilson Loops

**Claimed:** Confirmed as definition of confinement

**Finding:** **VERIFIED** - This is textbook QCD and defines confinement

### 3.3 Casimir Scaling

**Claimed:** Well-established for intermediate distances

**Finding:** **VERIFIED**

- [Lattice studies confirm](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.81.034504) Casimir scaling to ~5% at intermediate distances
- sigma_R/sigma_3 = C_2(R)/C_2(3) is verified for fundamental, adjoint, and higher representations
- String breaking occurs at larger distances for representations that can screen

---

## 4. Prior Work and Alternative Explanations

### 4.1 AdS/CFT Predictions for T_c/sqrt(sigma)

**Finding:**
- [AdS/CFT holographic models](https://link.springer.com/article/10.1134/S0040577919090113) give different predictions for this ratio
- The document claims AdS/CFT gives T_c/sqrt(sigma) ~ 0.5, which needs verification
- Holographic QCD models vary significantly depending on the specific construction
- The hard-wall model gives qualitatively different behavior than soft-wall

**Assessment:** The comparison table may oversimplify; AdS/CFT predictions are model-dependent

### 4.2 Geometric Origin of Confinement

**Finding:** The claim that CG provides a "geometric origin" for confinement is NOVEL
- This is not established in the standard QCD literature
- Alternative approaches (dual superconductor, center vortex, etc.) exist
- The document correctly marks this as 🔶 NOVEL

---

## 5. Heavy-Ion Data Verification

### 5.1 ALICE HBT Data

**Claimed:** Phys. Rev. C 92, 054908 (2015)

**Finding:** **VERIFIED**
- [This is a real ALICE publication](https://www.researchgate.net/publication/260127455_Pion_femtoscopy_measurements_in_ALICE_at_the_LHC) on Pb-Pb HBT measurements
- The HBT radii values cited (R_out ~ 5-7 fm, R_side ~ 5-6 fm) are consistent

### 5.2 Non-Gaussian HBT and Levy Analysis

**Finding:** RELEVANT PRIOR WORK EXISTS

- [Levy-stable distributions are actively studied](https://www.nature.com/articles/s42005-025-01973-x) in heavy-ion femtoscopy
- NA61/SHINE, STAR, and CMS have performed Levy fits
- Measured alpha parameters are typically 1.0-1.8 (NOT Gaussian alpha=2)
- This supports the existence of non-Gaussian sources
- The "anomalous diffusion" mechanism is well-documented

**Assessment:** The novel CG prediction of short-range coherence should be compared with existing Levy analysis results

### 5.3 Energy Independence of QGP Properties

**Finding:** This is a NOVEL CG prediction
- Standard hydrodynamic models predict energy-dependent freeze-out radii
- STAR BES data shows freeze-out radii increasing with energy
- The claim of energy-independent xi ~ 0.45 fm is **testable and discriminating**

---

## 6. Issues Found

### 6.1 Critical Issues

| Issue | Location | Severity |
|-------|----------|----------|
| Wrong arXiv number for FLAG | Main file, §4.1, §14 | HIGH |
| FLAG doesn't directly provide string tension | Citation context | MEDIUM |
| String tension slightly outdated | §4.1 | LOW |

### 6.2 Minor Issues

| Issue | Location | Notes |
|-------|----------|-------|
| AdS/CFT comparison may be oversimplified | §11.3 | Model-dependent |
| Missing recent 2024 string tension paper | References | Bulava et al. arXiv:2403.00754 |
| Missing Levy HBT literature | §7-§9 | Relevant prior work |

---

## 7. Recommended Updates

### 7.1 Citation Corrections

**Replace:**
```
FLAG 2024: arXiv:2111.09849
```

**With:**
```
FLAG 2021: arXiv:2111.09849 (Eur. Phys. J. C 82, 869 (2022))
FLAG 2024: arXiv:2411.04268
String tension: Bulava et al., arXiv:2403.00754 (2024): sqrt(sigma) = 445(3)(6) MeV
```

### 7.2 String Tension Update

Consider updating the central value:
- Old: sqrt(sigma) = 440 +/- 10 MeV
- Updated: sqrt(sigma) = 445 +/- 7 MeV (or cite range 440-445 MeV)

### 7.3 Add Relevant References

**Levy HBT Analysis:**
- ALICE: Eur. Phys. J. C 84 (2024) (Levy analysis in Pb-Pb)
- NA61/SHINE: arXiv:2302.04593 (Levy in Be+Be)
- CMS: arXiv:2306.11574 (Levy parameters in Pb-Pb at 5.02 TeV)

**Recent Lattice:**
- Bulava et al., arXiv:2403.00754 (string tension 2024)
- arXiv:2411.01886 (flux tube structure 2024)

---

## 8. Verification Summary

### 8.1 Verified Claims

| Claim | Status | Notes |
|-------|--------|-------|
| sqrt(sigma) ~ 440-445 MeV | VERIFIED | Within 2% of latest |
| T_c ~ 155-156.5 MeV | VERIFIED | Consensus value |
| T_c/sqrt(sigma) ~ 0.35 | VERIFIED | Accurate |
| Flux tube width 0.3-0.4 fm | VERIFIED | Separation-dependent |
| Area law for Wilson loops | VERIFIED | Standard QCD |
| Casimir scaling | VERIFIED | Established |
| Crossover width 10-20 MeV | VERIFIED | Standard |
| Pure gauge T_c ~ 270 MeV | VERIFIED | Standard |

### 8.2 Novel Claims (Not Yet Tested)

| Claim | Status | Testability |
|-------|--------|-------------|
| QGP coherence xi ~ 0.45 fm | NOVEL | Near-term (2026-2028) |
| xi energy-independent | NOVEL | RHIC/LHC comparison |
| Non-Gaussian HBT at 7% level | NOVEL | Existing Levy analysis may constrain |
| Geometric origin of confinement | NOVEL | Theoretical framework |

### 8.3 Issues Requiring Correction

| Issue | Priority |
|-------|----------|
| FLAG arXiv number wrong | HIGH |
| Missing 2024 string tension reference | MEDIUM |
| Levy HBT literature not cited | MEDIUM |

---

## 9. Overall Assessment

**VERIFIED: Partial**

**CONFIDENCE: Medium**

**Justification:**
- The core physics claims (string tension, T_c, critical ratio, flux tube properties) are **well-verified** against established lattice QCD results
- The citation to FLAG Review has an **incorrect arXiv number** that must be fixed
- The string tension value is slightly outdated but within uncertainties
- Novel predictions (QGP coherence, energy independence) are **clearly marked** and represent genuine testable claims
- Heavy-ion data comparison is accurate for macroscopic observables
- The Levy HBT literature provides relevant context for the non-Gaussian prediction that should be incorporated

**Recommendation:**
1. Correct the FLAG arXiv citation (2111.09849 -> FLAG 2021, add 2411.04268 for FLAG 2024)
2. Add Bulava et al. 2024 for updated string tension
3. Consider citing Levy HBT analysis work for context on non-Gaussian sources
4. The post-hoc consistency claims are solid; novel predictions are appropriately marked

---

## References Used in This Verification

### Lattice QCD
1. FLAG Review 2021: [arXiv:2111.09849](https://arxiv.org/abs/2111.09849)
2. FLAG Review 2024: [arXiv:2411.04268](https://arxiv.org/abs/2411.04268)
3. Budapest-Wuppertal: [Phys. Lett. B 730, 99 (2014)](https://epub.uni-regensburg.de/32653/7/main.pdf)
4. HotQCD: [Phys. Rev. D 90, 094503 (2014)](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.90.094503)
5. String tension 2024: [arXiv:2403.00754](https://arxiv.org/abs/2403.00754)
6. Flux tube width: [arXiv:2411.01886](https://arxiv.org/abs/2411.01886)

### Heavy-Ion Physics
7. ALICE HBT overview: [arXiv:1811.02828](https://arxiv.org/abs/1811.02828)
8. Levy walk in heavy-ion: [Nature Commun. Phys. (2025)](https://www.nature.com/articles/s42005-025-01973-x)
9. CMS Levy analysis: [arXiv:2306.11574](https://arxiv.org/html/2306.11574)

### AdS/CFT Comparisons
10. Holographic QCD T_c: [Theor. Math. Phys. (2019)](https://link.springer.com/article/10.1134/S0040577919090113)

---

*Literature verification completed 2026-01-20*

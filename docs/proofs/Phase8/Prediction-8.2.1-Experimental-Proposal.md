# Prediction 8.2.1: Experimental Proposal for QGP Phase Coherence Tests

## Document Type: EXPERIMENTAL PROPOSAL

**Date:** December 21, 2025
**Status:** READY FOR SUBMISSION
**Target Experiments:** ALICE (CERN), STAR (RHIC/BNL)

---

## Executive Summary

This proposal outlines three novel analysis methods to test Prediction 8.2.1 of the Chiral Geometrogenesis framework, which predicts an **energy-independent coherence length** ξ_eff ≈ 0.38 ± 0.05 fm (at T ~ 200 MeV, including Debye screening) in quark-gluon plasma. The key tests can be performed using **existing Run 2/3 data** from ALICE and BES-II data from STAR, requiring only new analysis approaches rather than new experimental runs.

### Key Predictions to Test

| Observable | CG Prediction | Standard QGP | Discrimination |
|------------|---------------|--------------|----------------|
| ξ_eff(RHIC) vs ξ_eff(LHC) | Identical (within 10%) | Scales with √s | ✅ Unique |
| HBT residual shape | Two-component source | Single Gaussian | ✅ Unique |
| Non-Gaussian parameter α | Lévy α ~ 1.5-1.8 | α → 2 (Gaussian) | Partially covered |

---

## Part 1: Proposed Analyses

### Analysis 1: Energy-Independence Test of Coherence Length

**Objective:** Test whether a sub-structure coherence length ξ_eff is independent of collision energy

**Method:**
1. Fit standard Gaussian to pion HBT correlations: C_2(q) = 1 + λ·exp(-R²q²)
2. Extract residuals: δC_2(q) = C_2^data - C_2^Gaussian
3. Fit residuals to coherence term: δC_2(q) = α·exp(-ξ_eff²q²)
4. Compare extracted ξ_eff across energies:
   - STAR BES-II: √s = 7.7, 11.5, 14.5, 19.6, 27, 39, 62.4, 200 GeV
   - ALICE Run 2: √s = 2.76, 5.02 TeV
   - ALICE Run 3: √s = 5.36 TeV

**Expected Result:**
- **CG prediction:** ξ_eff ≈ 0.38 ± 0.05 fm at ALL energies (temperature-dependent: ~0.48 fm at T_c → ~0.38 fm at T=200 MeV)
- **Standard hydro:** ξ_eff ∝ R_HBT ∝ (√s)^0.3

**Data Requirements:**
- Existing published HBT data sufficient for proof-of-concept
- Full precision requires access to correlation functions (not just fitted radii)

---

### Analysis 2: Two-Component Source Fit

**Objective:** Test for chiral coherence sub-structure within freeze-out volume

**Method:**
Fit correlation function to two-component model:

$$C_2(q) = 1 + \lambda \cdot \left[(1-\alpha_{coh})e^{-R_{therm}^2 q^2} + \alpha_{coh} e^{-\xi_{eff}^2 q^2}\right]^2$$

**Parameters to extract:**
- R_therm: Freeze-out radius (expected ~5-6 fm)
- ξ_eff: Coherence length (CG predicts ~0.38 ± 0.05 fm at T=200 MeV)
- α_coh: Coherent fraction (expected ~10-15%)

**Signal Location:**
- Peak sensitivity at q ~ 30-60 MeV (1/6 fm⁻¹)
- Signal magnitude: ~7-8% deviation from single Gaussian
- Limiting factor: Systematic uncertainties (~5%)

**Data Requirements:**
- High-statistics central Pb-Pb or Au-Au collisions
- Fine q-binning in range 0-200 MeV
- Coulomb and track-merging corrections applied

---

### Analysis 3: Lévy-Stable Source Comparison

**Objective:** Compare CG two-component model with existing Lévy-stable analyses

**Context:**
STAR and NA61/SHINE already perform Lévy-stable source fits with:

$$C_2(q) = 1 + \lambda \cdot \exp\left[-(qR)^\alpha\right]$$

where α = 2 is Gaussian, α = 1 is Cauchy.

**CG Prediction:**
The two-component structure should manifest as effective Lévy exponent α ~ 1.5-1.8, with:
- α closer to 2 at small q (freeze-out dominates)
- α decreasing at intermediate q (coherence contribution)

**Comparison Strategy:**
1. Obtain published Lévy fit parameters (α, R) vs √s
2. Compare q-dependence of effective α with CG prediction
3. Test whether α(√s) shows energy-independence signature

---

## Part 2: Contact Information

### ALICE Collaboration (CERN)

**Physics Coordination:**
- **Physics Coordinator:** Andrea Dainese
- **Deputy PCs:** Cvetan Cheshkov, Leticia Cunqueiro Mendez
- **Contact:** Through ALICE Physics Board

**Relevant Working Group:**
- **PWG-CF (Correlations and Flow):** Handles femtoscopy analyses
- Recent conveners (2022-2024): Check ALICE organization page

**Submission Pathway:**
1. Contact PWG-CF conveners with analysis proposal
2. Request access to correlation function data (if external)
3. Submit analysis note for internal review

**Website:** [ALICE Physics Organization](https://alice-collaboration.web.cern.ch/organization/phb/index.html)

---

### STAR Collaboration (BNL/RHIC)

**Spokespersons:**
- **Lijuan Ruan** (Brookhaven National Laboratory)
- **Frank Geurts** (Rice University)

**Femtoscopy Expertise:**
- BulkCorr Physics Analysis Group handles HBT analyses
- Recent femtoscopy work includes Lévy-stable source analyses

**Submission Pathway:**
1. Contact spokespersons or relevant PAG conveners
2. Present at STAR Collaboration Meeting (held twice yearly)
3. Next meeting: Check [STAR Meetings](https://drupal.star.bnl.gov/STAR/meetings/)

**Website:** [STAR Collaboration](https://www.star.bnl.gov/)

---

### Conferences for Presentation

**Primary Target: WPCF 2026**
- **Event:** 18th Workshop on Particle Correlations and Femtoscopy
- **Dates:** May 18-22, 2026
- **Location:** Budapest, Hungary (ELTE Eötvös Loránd University)
- **Website:** [WPCF 2026](https://wpcf2026.elte.hu/)
- **Focus:** Particle correlations and femtoscopy community
- **Submission:** Abstract deadline TBA (check website)

**Secondary Target: Quark Matter 2026**
- **Event:** XXXII International Conference on Ultra-relativistic Nucleus-Nucleus Collisions
- **Dates:** TBA (typically April)
- **Location:** TBA
- **Previous:** QM2025 was held April 6-12, 2025 in Frankfurt
- **Focus:** Broad heavy-ion physics community
- **Contact:** qm2025@itp.uni-frankfurt.de (for QM2025 reference)

**Alternative: FemTUM Workshop**
- **Event:** Femtoscopy Experimentalists Meet the Theorists
- **Host:** Technical University of Munich
- **Website:** Check CERN Indico for future dates
- **Focus:** Focused femtoscopy discussions, smaller community

---

## Part 3: Existing Data and Publications

### Available Data for Analysis

| Experiment | Dataset | √s_NN | Status | Reference |
|------------|---------|-------|--------|-----------|
| ALICE | Pb-Pb Run 2 | 2.76 TeV | Published | PRC 92, 054908 (2015) |
| ALICE | Pb-Pb Run 2 | 5.02 TeV | Published | Multiple papers |
| ALICE | Pb-Pb Run 3 | 5.36 TeV | Analysis ongoing | — |
| STAR | Au-Au | 200 GeV | Published | PRC 89, 044906 (2014) |
| STAR | Au-Au BES-II | 7.7-62.4 GeV | Analysis ongoing | — |
| PHENIX | Au-Au | 200 GeV | Published | Multiple papers |

### Existing Non-Gaussian Analyses

| Group | Method | Key Finding | Reference |
|-------|--------|-------------|-----------|
| STAR | Lévy-stable fits | α ~ 1.2-1.8 (non-Gaussian) | arXiv:2306.13668 |
| NA61/SHINE | Lévy HBT | Power-law tails observed | Universe 5, 154 (2019) |
| PHENIX | Source imaging | Long-range component | Multiple papers |

---

## Part 4: Proposal Letter Template

### For ALICE PWG-CF

```
Subject: Analysis Proposal - Two-Component HBT Source and Energy Independence Test

Dear PWG-CF Conveners,

We propose a novel analysis of existing ALICE femtoscopy data to test a
specific theoretical prediction regarding sub-structure in the HBT source.

Key Points:
1. The analysis uses existing Run 2 pion correlation data
2. We propose fitting residuals after standard Gaussian subtraction
3. The test: is extracted sub-structure scale energy-independent?

The prediction arises from a theoretical framework (Chiral Geometrogenesis)
that predicts a universal coherence length ξ_eff ≈ 0.38 ± 0.05 fm (at T~200 MeV)
independent of collision energy. This is in contrast to standard hydrodynamic
scaling where all scales grow with √s.

We would appreciate the opportunity to:
- Present this analysis concept at a PWG meeting
- Discuss data access requirements
- Collaborate with femtoscopy experts on systematic uncertainties

Attached: Technical summary of the analysis methodology

Best regards,
[Name]
```

### For STAR Collaboration

```
Subject: Proposed BES-II Femtoscopy Analysis - Energy Independence of Coherence Length

Dear Drs. Ruan and Geurts,

We are writing to propose an analysis of STAR BES-II femtoscopy data that
tests a novel theoretical prediction.

The Prediction:
A sub-structure coherence length ξ_eff ≈ 0.38 ± 0.05 fm (at T~200 MeV) should be
INDEPENDENT of collision energy, unlike standard HBT radii that scale with √s.

Proposed Method:
1. Extract non-Gaussian residuals from standard HBT fits
2. Fit residuals to coherence model
3. Compare extracted ξ across BES-II energies (7.7-200 GeV)

This analysis leverages STAR's unique multi-energy dataset to perform a
test that would be impossible at a single-energy facility.

We would welcome the opportunity to present this proposal at an upcoming
STAR Collaboration Meeting.

Best regards,
[Name]
```

---

## Part 5: Timeline and Milestones

### Phase 1: Initial Contact (1-2 months)
- [ ] Send proposals to ALICE PWG-CF and STAR spokespersons
- [ ] Request presentation slot at collaboration meeting
- [ ] Identify internal collaborators with data access

### Phase 2: Feasibility Study (3-6 months)
- [ ] Obtain sample correlation function data
- [ ] Perform proof-of-concept analysis on published data
- [ ] Estimate systematic uncertainties

### Phase 3: Full Analysis (6-12 months)
- [ ] Analyze full Run 2 dataset (ALICE)
- [ ] Analyze BES-II multi-energy dataset (STAR)
- [ ] Cross-check RHIC vs LHC results

### Phase 4: Publication (12-18 months)
- [ ] Present preliminary results at WPCF 2026
- [ ] Submit analysis note for collaboration review
- [ ] Publish results

---

## Part 6: Summary

### What's Unique About This Proposal

1. **Novel Observable:** Energy-independence of sub-structure, not overall HBT radii
2. **Uses Existing Data:** No new experimental runs required
3. **Clear Discrimination:** CG predicts ξ(√s) = constant vs. hydro predicts ξ ∝ √s^0.3
4. **Builds on Lévy Work:** Connects to existing non-Gaussian analyses

### Why This Matters

If confirmed, energy-independent coherence would provide:
- Evidence for a universal QCD oscillation frequency ω₀ ~ 200 MeV
- Support for the internal time mechanism in Chiral Geometrogenesis
- New constraints on QGP dynamics beyond hydrodynamics

### Next Steps

1. Prepare technical proposal document
2. Contact ALICE and STAR collaboration members
3. Submit abstract to WPCF 2026 (deadline TBA)

---

## References

### Framework Documents
1. Prediction-8.2.1-QGP-Phase-Coherence.md (Statement)
2. Prediction-8.2.1-QGP-Phase-Coherence-Derivation.md (Derivation)
3. Prediction-8.2.1-QGP-Phase-Coherence-Applications.md (Applications)

### Key External References
4. ALICE Collaboration, Phys. Rev. C 92, 054908 (2015)
5. STAR Collaboration, Phys. Rev. C 89, 044906 (2014)
6. Lévy HBT at STAR: arXiv:2306.13668
7. Lisa et al., Ann. Rev. Nucl. Part. Sci. 55, 357 (2005)

### Conference Information
8. [WPCF 2026](https://wpcf2026.elte.hu/) - Budapest, May 18-22, 2026
9. [ALICE Organization](https://alice-collaboration.web.cern.ch/organization/phb/index.html)
10. [STAR Collaboration](https://www.star.bnl.gov/)

---

*Document created: December 21, 2025*
*Status: READY FOR SUBMISSION*

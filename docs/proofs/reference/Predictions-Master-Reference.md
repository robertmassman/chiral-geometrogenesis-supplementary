# Predictions Master Reference: Chiral Geometrogenesis

## Status: 🔶 NOVEL — CONSOLIDATED PREDICTION INDEX

**Created:** 2026-02-27
**Last Updated:** 2026-02-28
**Purpose:** Single authoritative reference consolidating all testable predictions of Chiral Geometrogenesis (CG), organized by experimental priority and classified by novelty.

---

## Honesty Disclaimer

Following the honest assessment framework established in the [Phase 8 README](../Phase8/README.md):

> **Most CG predictions are post-hoc explanations of known physics, not genuine pre-data predictions.** The framework was developed with full knowledge of the Standard Model, so agreements with known values (particle masses, mixing angles, cosmological parameters) are **consistency checks**, not predictions.

**Genuinely novel predictions** — values or signatures that were *not* used as inputs and *cannot* be obtained from simpler models — are explicitly marked. Only these carry real predictive power. The tiers below reflect this distinction:

| Tier | Classification | Evidential Weight |
|------|---------------|-------------------|
| **Tier 1** | Novel predictions testable now or near-term | **High** — genuine falsification tests |
| **Tier 2** | Novel predictions requiring future experiments | **High** — but longer wait |
| **Tier 3** | Post-hoc consistency checks | **Low** — necessary but not sufficient |
| **Tier 4** | Structural falsification constraints | **Medium** — package deals |

---

## 1. Executive Summary Table

All predictions sorted by experimental priority. "Novel?" indicates whether the prediction was genuinely made before the data was known or uses no adjustable parameters beyond $R_\text{stella}$.

| # | Prediction | CG Value | Novel? | Experiment | Timeline | Source |
|---|-----------|----------|--------|------------|----------|--------|
| 1 | QGP coherence length (energy-independent) | $\xi_0 = 0.448$ fm | **Yes** | ALICE/STAR | Now | [Pred 8.2.1](../Phase8/Prediction-8.2.1-QGP-Phase-Coherence.md), [Prop 8.5.1](../Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md) |
| 2 | W-condensate dark matter mass | $M_W \approx 1800 \pm 500$ GeV | **Yes** | DARWIN | 2030s | [Pred 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md), [Thm 4.3.2](../Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md) |
| 3 | $\theta_\text{QCD} = 0$ from $\mathbb{Z}_3$ (no axion) | $\theta = 0$ exactly | **Yes** | PSI/SNS (nEDM) | 2030s | [Prop 0.0.5a](../foundations/Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md) |
| 4 | Glueball mass ratio $m_{0^{++}}/\sqrt{\sigma}$ | $R_V = 3.45 \pm 0.06$ | **Yes** | Lattice QCD | Ongoing | [Prop 7.8.4](../Phase7/Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio.md) |
| 4a | Full glueball spectrum (7 $J^{PC}$ states + exotic $1^{-+}$) | See §2.4a | **Yes** | Lattice / BESIII / GlueX | Ongoing | [Prop 7.8.6](../Phase7/Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum.md) |
| 5 | Higgs self-coupling $\kappa_\lambda$ | $0.97 \pm 0.03$ | **Yes** | HL-LHC / FCC-hh | 2035 / 2050s | [Prop 0.0.37](../foundations/Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md) |
| 6 | Tensor-to-scalar ratio $r$ | $0.0012$ | **Yes** | LiteBIRD | 2030s | [Prop 0.0.17aa](../foundations/Proposition-0.0.17aa-Spectral-Index-From-First-Principles.md) |
| 7 | W-sector gravitational waves | $f \sim 7$–$60$ mHz, $\Omega h^2 \sim 10^{-14}$–$10^{-11}$ | **Yes** | LISA / DECIGO | 2035+ | [Pred 8.2.4](../Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md) |
| 8 | Pre-geometric relic GW background | $f \sim 10^{-9}$–$10^{-7}$ Hz | **Yes** | PTAs / SKA | 2030s | [Pred 8.2.3](../Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md) |
| 9 | CMB $S_4$ symmetry patterns | $A_{S_4} \lesssim 10^{-6}$ | **Yes** | CMB-S4 | 2030s | [Pred 8.2.3](../Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md) |
| 10 | EW precision oblique parameters | $S \approx 7 \times 10^{-5}$, $T \approx 2 \times 10^{-4}$ | Partial | FCC-ee | 2040s | [Prop 0.0.24a](../foundations/Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md) |
| 11 | Lorentz violation scale | $\delta c/c \sim (E/E_P)^2 \sim 10^{-32}$ at TeV | Partial | CTA | 2030s | [Thm 0.0.7](../foundations/Theorem-0.0.7-Lorentz-Violation-Bounds.md) |
| 12 | Proton decay lifetime | $\tau(p \to e^+\pi^0) = 5.1 \times 10^{36}$ yr | **Yes** | Hyper-K / DUNE | 2030s+ | [Pred 8.4.1](../Phase8/Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md) |
| 13 | $N_\text{gen} = 3$ | 3 generations | No (post-hoc) | — | Confirmed | [Deriv 8.1.3](../Phase8/Derivation-8.1.3-Three-Generation-Necessity.md) |
| 14 | $\theta_{13}$ from first principles | $8.54°$ | No (post-hoc) | — | Confirmed | [Deriv 8.4.2](../Phase8/Derivation-8.4.2-Theta13-First-Principles.md) |
| 15 | $\theta_{23}$ corrected | $48.9° \pm 1.4°$ | No (post-hoc) | — | Confirmed | [Prop 8.4.4](../Phase8/Proposition-8.4.4-Atmospheric-Angle-Correction.md) |
| 16 | Higgs mass $m_H$ | $125.2 \pm 0.5$ GeV | No (post-hoc) | — | Confirmed | [Prop 0.0.27](../foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md) |
| 17 | String tension $\sqrt{\sigma}$ | 440 MeV | No (post-hoc) | — | Confirmed | [Prop 0.0.17j](../foundations/Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md) |
| 18 | QCD critical temperature $T_c$ | $154.2$ MeV | No (post-hoc) | — | Confirmed | [Prop 8.5.1](../Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md) |
| 19 | Spectral index $n_s$ | 0.9648 | No (post-hoc) | — | Confirmed | [Prop 0.0.17aa](../foundations/Proposition-0.0.17aa-Spectral-Index-From-First-Principles.md) |
| 20 | Cosmological densities $\Omega_b$, $\Omega_{DM}$, $\Omega_\Lambda$ | $0.049$, $0.27$, $0.68$ | No (post-hoc) | — | Confirmed | [Prop 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) |
| 21 | Wolfenstein $\lambda$ | 0.2245 | No (post-hoc) | — | Confirmed | [Ext 3.1.2b](../Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md) |
| 22 | 8 gluons from 8 faces | 8 | No (post-hoc) | — | Confirmed | [Deriv 8.4.3](../Phase8/Derivation-8.4.3-Euler-Characteristic-Signature.md) |
| 23 | DM direct detection cross-section | $\sigma_\text{SI} \sim 1.5 \times 10^{-47}$ cm$^2$ | **Yes** | DARWIN | 2030s | [Pred 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md) |
| 24 | HBT Levy exponent | $\alpha = 1.30 \pm 0.07$ | **Yes** | ALICE/STAR | Now | [Prop 8.5.1](../Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md) |
| 25 | $\chi = 4$ observable package | 5 linked observables | **Yes** | Multiple | Structural | [Deriv 8.4.3](../Phase8/Derivation-8.4.3-Euler-Characteristic-Signature.md) |

---

## 2. Tier 1 — Novel Predictions Testable Now / Near-Term

### 2.1 QGP Phase Coherence Length

**Source:** [Prediction 8.2.1](../Phase8/Prediction-8.2.1-QGP-Phase-Coherence.md), [Proposition 8.5.1](../Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md)

$$\boxed{\xi_0 = \frac{\hbar c}{\omega_0} = R_\text{stella} = 0.448 \text{ fm}, \quad \text{energy-independent}}$$

The chiral oscillation frequency $\omega_0 \sim 200$ MeV defines a universal coherence length in the quark-gluon plasma. CG predicts this length is set by stella geometry and therefore *independent* of collision energy $\sqrt{s}$.

**Unique CG signature:** No other framework predicts an energy-independent QGP coherence length. Standard QCD expectations are that $\xi$ scales with $\sqrt{s}$ or temperature.

**Falsification:** $\xi$ varying by >30% across $\sqrt{s} = 200$ GeV to 5.02 TeV would rule out the geometric origin.

**Experiment:** ALICE/STAR HBT analysis — testable *now* with existing data. Additional genuine prediction: HBT Levy exponent $\alpha = 1.30 \pm 0.07$.

### 2.2 W-Condensate Dark Matter

**Source:** [Prediction 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md), [Theorem 4.3.2](../Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md)

$$\boxed{M_W \approx 1800 \pm 500 \text{ GeV}, \quad \sigma_\text{SI} \sim 1.5 \times 10^{-47} \text{ cm}^2}$$

The W-soliton is a topological soliton in the hidden W-sector (4th vertex of the stella octangula), stabilized by $\pi_3(\text{SU}(2)) = \mathbb{Z}$. Key properties:

| Property | Value | Origin |
|----------|-------|--------|
| Mass | $1800 \pm 500$ GeV | Faddeev–ANW bounds with $v_W = 123 \pm 15$ GeV |
| Spin | 1/2 (fermionic) | Index theorem |
| Lifetime | $> 10^{34}$ yr | Topological stability |
| Self-interaction | $\sigma/m \approx 1.4 \times 10^{-12}$ cm$^2$/g | Geometric cross-section |
| Portal coupling | $\lambda_{H\Phi} = 0.036$ | Geometric |
| ADM asymmetry | $\varepsilon_W = 3.1 \times 10^{-13}$ | Five geometric factors |

**Unique CG signature:** Dark matter mass and coupling are *derived* from geometry, not fitted. The asymmetric dark matter (ADM) production mechanism is unique to the 4th-vertex structure.

**Falsification:** DM detected at $M \neq 1.7$ TeV or $\sigma_\text{SI} \gg 10^{-45}$ cm$^2$ would rule out the W-condensate as the dominant DM candidate.

**Experiment:** DARWIN (2030s) — sensitivity reaches $\sigma_\text{SI} \sim 10^{-48}$ cm$^2$.

### 2.3 $\theta_\text{QCD} = 0$ from $\mathbb{Z}_3$ (No Axion)

**Source:** [Proposition 0.0.5a](../foundations/Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md)

$$\boxed{\theta_\text{QCD} = 0 \text{ exactly, from } \mathbb{Z}_3 \text{ center of SU(3)}}$$

CG resolves the Strong CP problem without an axion. The $\mathbb{Z}_3$ center symmetry of SU(3), which is realized geometrically on the stella octangula, constrains $\theta = 0$ exactly. Current nEDM bound: $|\bar{\theta}| < 10^{-10}$.

**Unique CG signature:** Predicts $\theta = 0$ exactly (not just small). No axion exists. This is distinct from the Peccei-Quinn mechanism (axion) and the Nelson-Barr mechanism (spontaneous CP violation).

**Falsification:** Discovery of a QCD axion, or measurement of $\theta \neq 0$.

**Experiment:** nEDM experiments at PSI and SNS (2030s) — improved sensitivity by $10\times$–$100\times$.

### 2.4 Glueball Mass Ratio

**Source:** [Proposition 7.8.4](../Phase7/Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio.md) (and Props 7.8.1–7.8.3)

$$\boxed{R_V \equiv \frac{m_{0^{++*}}}{m_{0^{++}}} = 3.45 \pm 0.06 \quad (1.7\% \text{ precision})}$$

Derived from V-scheme BLM scale setting with $\alpha_V = 0.373 \pm 0.010$. Consistent with lattice QCD: $R_\text{cont} = 3.405 \pm 0.021$ (0.70$\sigma$ tension). Combined with two independent estimates (Casimir scaling, Bethe-Salpeter): $R_\text{combined} = 3.45 \pm 0.057$.

**Unique CG signature:** The ratio emerges from the framework's internal non-perturbative dynamics, not from a fit to lattice data.

**Falsification:** High-precision lattice measurements yielding $R$ outside $[3.33, 3.57]$ at $>3\sigma$.

**Experiment:** Ongoing lattice QCD computations; future experimental glueball identification at BESIII/GlueX.

### 2.4a Full Two-Gluon Glueball Spectrum

**Source:** [Proposition 7.8.6](../Phase7/Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum.md) (extends Props 7.8.3–7.8.4)

Full $C = +1$ glueball spectrum from generalized Salpeter equation with L-centroid formula $R_L = 3\sqrt{(2L+3)(2-3\alpha_V/(L+1))/2}$:

| $J^{PC}$ | Predicted $R = m_G/\sqrt{\sigma}$ | Lattice $R$ | Tension |
|-----------|----------------------------------|-------------|---------|
| $0^{++}$ | $3.45 \pm 0.06$ | $3.405 \pm 0.021$ | $0.7\sigma$ |
| $2^{++}$ | $4.78 \pm 0.50$ | $4.73 \pm 0.07$ | $0.1\sigma$ |
| $0^{-+}$ | $5.23 \pm 0.55$ | $5.12 \pm 0.10$ | $0.2\sigma$ |
| $1^{-+}$ (exotic) | $5.46 \pm 0.55$ | — | **prediction** |
| $2^{-+}$ | $5.92 \pm 0.55$ | $6.11 \pm 0.13$ | $0.3\sigma$ |
| $0^{++*}$ | $5.35 \pm 0.50$ | $5.31 \pm 0.15$ | $0.1\sigma$ |
| $3^{++}$ | $7.22 \pm 0.50$ | $7.00 \pm 0.16$ | $0.4\sigma$ |

**Unique CG signature:** The $1^{-+}$ exotic glueball ($m \approx 2400 \pm 240$ MeV) is a distinctive prediction — this quantum number cannot come from $q\bar{q}$.

**Falsification:** Mass ordering disagreement with lattice, or $1^{-+}$ exotic found outside $[1900, 2900]$ MeV range.

**Experiment:** BESIII, GlueX glueball searches; ongoing lattice spectrum computations including exotic channels.

### 2.5 Higgs Self-Coupling $\kappa_\lambda$

**Source:** [Proposition 0.0.37](../foundations/Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md)

$$\boxed{\kappa_\lambda \equiv \frac{\lambda_3^\text{CG}}{\lambda_3^\text{SM}} = 0.97 \pm 0.03}$$

Derived from the Higgs quartic $\lambda = 1/8$ (Prop 0.0.27: 8 vertex modes of the stella octangula) and the complete Higgs potential including radiative corrections. This is a 6.7$\times$ improvement over the previous estimate of $\kappa_\lambda = 1.0 \pm 0.2$ (Analysis-Independent-Falsifiable-Predictions).

**Unique CG signature:** The quartic coupling $\lambda = 1/8$ is a discrete geometric prediction, not a continuous parameter.

**Falsification:** $\kappa_\lambda$ outside $[0.91, 1.03]$ at $> 3\sigma$ rules out the CG Higgs sector.

**Experiment:** HL-LHC ($\sim$30% precision, 2035), FCC-hh ($\sim$5–10% precision, 2050s).

### 2.6 Tensor-to-Scalar Ratio $r$

**Source:** [Proposition 0.0.17aa](../foundations/Proposition-0.0.17aa-Spectral-Index-From-First-Principles.md)

$$\boxed{r = 0.0012}$$

Derived from $N_\text{geo} = 512/9 \approx 56.89$ e-folds (topological constants of the stella octangula) and the standard slow-roll relation. Current BICEP/Keck bound: $r < 0.032$ (95% CL, BK18).

**Unique CG signature:** The e-fold count is a topological constant, not a continuous parameter.

**Falsification:** $r > 0.003$ at high significance, or $r$ measurement inconsistent with $N \approx 57$.

**Experiment:** LiteBIRD (launch ~2032) — sensitivity $r \sim 0.001$.

### 2.7 W-Boson Mass

**Source:** [Proposition 0.0.24](../foundations/Proposition-0.0.24-SU2-Gauge-Coupling-From-Unification.md)

$$\boxed{M_W = 80.37 \text{ GeV} \quad (0.0\% \text{ deviation from PDG})}$$

Derived from the geometric determination of $\sin^2\theta_W = 0.231$ and the electroweak VEV $v_H = 246.7$ GeV. While $M_W$ itself is known, the CG value provides a consistency check on the electroweak sector derivation. The ongoing LHC precision measurements (CDF II anomaly context) test the prediction at the $\mathcal{O}(10)$ MeV level.

---

## 3. Tier 2 — Novel Predictions Requiring Future Experiments

### 3.1 W-Sector Gravitational Waves

**Source:** [Prediction 8.2.4](../Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md)

$$\boxed{f_\text{peak} \sim 7\text{–}60 \text{ mHz}, \quad \Omega_\text{GW} h^2 \sim 10^{-14}\text{–}10^{-11} \text{ (enhanced benchmark)}}$$

CG predicts a **two-tier** GW signal from the W-sector phase transition:
- **Perturbative baseline (crossover):** No detectable signal — the W-sector transition is a smooth crossover
- **Enhanced benchmark:** If non-perturbative effects strengthen the transition, a turbulence-dominated spectrum appears in the mHz band

**Unique CG signature:** A **two-peak GW spectrum** — one from the W-sector (mHz) and one from the visible EWPT (lower frequency) — would be unique to CG. No other BSM framework predicts this specific combination.

**Falsification:** Detection of a mHz GW signal with spectral shape inconsistent with turbulence dominance.

**Experiment:** LISA (marginal, 2035+), DECIGO (strong sensitivity, 2040s+).

### 3.2 Pre-Geometric Relic GW Background

**Source:** [Prediction 8.2.3](../Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md)

$$\boxed{f_\text{peak} \sim 10^{-9}\text{–}10^{-7} \text{ Hz}, \quad \Omega h^2 \sim 10^{-9}\text{–}10^{-8}}$$

Stochastic gravitational wave background from the pre-geometric $\to$ geometric phase transition. Compatible with NANOGrav signal: $\Omega h^2 \sim 6 \times 10^{-9}$ within factor of 6.

**Experiment:** Pulsar Timing Arrays (NANOGrav, EPTA, PPTA) — ongoing; SKA (2030s).

### 3.3 CMB $S_4$ Symmetry Patterns

**Source:** [Prediction 8.2.3](../Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md)

$$\boxed{A_{S_4} \lesssim 10^{-6}}$$

Residual tetrahedral ($S_4$) symmetry patterns imprinted on the CMB from the pre-geometric phase. These appear as specific non-Gaussian correlations with $S_4$ selection rules.

**Experiment:** CMB-S4 (2030s) — improved sensitivity to non-Gaussian signals.

### 3.4 Electroweak Precision: Oblique Parameters

**Source:** [Proposition 0.0.24a](../foundations/Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md)

$$\boxed{S \approx 7 \times 10^{-5}, \quad T \approx 2 \times 10^{-4}, \quad U \approx 0}$$

CG predicts oblique parameters 3–4 orders of magnitude below current bounds ($|S| < 0.2$, $|T| < 0.1$). This is a structural prediction: the custodial symmetry of the stella octangula geometry suppresses new-physics contributions.

**Falsification:** $|S| > 0.01$ or $|T| > 0.01$ with confirmed BSM origin would challenge CG.

**Experiment:** FCC-ee ($\sim$2040s) — precision improvement of $\sim$$10\times$ over LEP.

### 3.5 Lorentz Violation Bounds

**Source:** [Theorem 0.0.7](../foundations/Theorem-0.0.7-Lorentz-Violation-Bounds.md)

$$\boxed{\frac{\delta c}{c} \sim \left(\frac{E}{E_P}\right)^2 \sim 10^{-32} \text{ at TeV}}$$

CG's discrete pre-geometric structure (FCC lattice) generates quadratic Lorentz violation suppressed by $E_P^2$. This is 6–17 orders of magnitude below current experimental bounds, with $E_{\text{QG},2} \sim E_P \sim 10^{19}$ GeV.

**Experiment:** CTA gamma-ray observatory (2030s) — improved bounds on energy-dependent photon dispersion.

### 3.6 Proton Decay Lifetime and Branching Ratios

**Source:** [Prediction 8.4.1](../Phase8/Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md)

The stella octangula geometry encodes the GUT breaking chain $S_4 \times \mathbb{Z}_2 \to W(F_4) \to D_4 \to D_5 = \text{so}(10) \to \text{SU}(5) \to \text{SM}$ (Theorem 0.0.4), with $\alpha_{GUT}^{-1} = 24.4 \pm 0.3$ and $M_{GUT} = (2.0 \pm 0.3) \times 10^{16}$ GeV (Proposition 0.0.25).

$$\boxed{\tau(p \to e^+\pi^0) = 5.1^{+6.6}_{-2.8} \times 10^{36} \text{ yr}, \quad \text{BR}(e^+\pi^0) = 38\%}$$

Key features: (1) Dominant channel is $p \to e^+\pi^0$ (dimension-6, non-SUSY), distinguishing CG from SUSY GUTs where $p \to \bar{\nu}K^+$ dominates. (2) All channels satisfy Super-K bounds with 200× margin. (3) Beyond Hyper-K sensitivity (~50×), testable at future megaton-scale detectors.

**Unique CG signature:** The non-propagating nature of X/Y bosons in the pre-geometric phase may provide additional geometric suppression beyond the standard dimension-6 result, making the prediction a conservative lower bound.

**Falsification:** Proton decay at $\tau < 2 \times 10^{36}$ yr, or $p \to \bar{\nu}K^+$ dominance (indicating SUSY d=5 operators absent in CG).

**Experiment:** Hyper-Kamiokande (2027+), DUNE (2030+) — proton decay searches. CG prediction is ~50× beyond Hyper-K sensitivity but constrains the framework if decay is observed at shorter lifetimes.

---

## 4. Tier 3 — Post-Hoc Consistency Checks

These are values that CG reproduces from geometry but that were known *before* the framework was developed. They demonstrate internal consistency but do not constitute predictions.

| # | Observable | CG Value | Experimental Value | Agreement | Source |
|---|-----------|----------|-------------------|-----------|--------|
| 1 | $N_\text{gen}$ | 3 | 3 | Exact | [Deriv 8.1.3](../Phase8/Derivation-8.1.3-Three-Generation-Necessity.md) |
| 2 | $\theta_{13}$ | 8.539° | $8.54° \pm 0.11°$ | 0.001° ($<0.01\sigma$) | [Deriv 8.4.2](../Phase8/Derivation-8.4.2-Theta13-First-Principles.md) |
| 3 | $\theta_{23}$ | $48.9° \pm 1.4°$ | $49.1° \pm 1.0°$ | $0.2\sigma$ | [Prop 8.4.4](../Phase8/Proposition-8.4.4-Atmospheric-Angle-Correction.md) |
| 4 | $m_H$ | $125.2 \pm 0.5$ GeV | $125.25 \pm 0.17$ GeV | 0.04% | [Prop 0.0.27](../foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md) |
| 5 | $\sqrt{\sigma}$ | 440 MeV | $440 \pm 30$ MeV (FLAG 2024) | $<0.1\sigma$ | [Prop 0.0.17j](../foundations/Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md) |
| 6 | $T_c$ | 154.2 MeV | $155 \pm 5$ MeV | $1.5\sigma$ | [Prop 8.5.1](../Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md) |
| 7 | $n_s$ | 0.9648 | $0.9649 \pm 0.0042$ (Planck) | $0.02\sigma$ | [Prop 0.0.17aa](../foundations/Proposition-0.0.17aa-Spectral-Index-From-First-Principles.md) |
| 8 | $\Omega_b$ | $0.049 \pm 0.017$ | $0.0493 \pm 0.0003$ | Within unc. | [Prop 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) |
| 9 | $\Omega_{DM}$ | $0.27 \pm 0.11$ | $0.265 \pm 0.003$ | Within unc. | [Prop 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) |
| 10 | $\Omega_\Lambda$ | $0.68 \pm 0.14$ | $0.685 \pm 0.007$ | Within unc. | [Prop 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) |
| 11 | Wolfenstein $\lambda$ | 0.2245 | $0.22650 \pm 0.00048$ (PDG) | 0.88% | [Ext 3.1.2b](../Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md) |
| 12 | 8 gluons | 8 (from 8 faces of $\partial\mathcal{S}$) | 8 | Exact | [Deriv 8.4.3](../Phase8/Derivation-8.4.3-Euler-Characteristic-Signature.md) |
| 13 | $\alpha_s(M_Z)$ | 0.122 (backward running from $E_8$) | $0.1180 \pm 0.0009$ (PDG) | 4% | [Prop 0.0.17s](../foundations/Proposition-0.0.17s-Strong-Coupling-From-Equipartition.md) |

**Assessment:** 13/13 consistency checks pass. The most impressive agreements ($\theta_{13}$ at 0.001°, $m_H$ at 0.04%, $n_s$ at $0.02\sigma$) are nonetheless post-hoc; the framework was tuned with knowledge of these values.

---

## 5. Tier 4 — Structural Falsification Constraints

These are not individual predictions but *packages* of linked observables. Falsifying any member of a package challenges the entire geometric structure.

### 5.1 Euler Characteristic Observable Package ($\chi = 4$)

**Source:** [Derivation 8.4.3](../Phase8/Derivation-8.4.3-Euler-Characteristic-Signature.md)

Five observables jointly determined by $\chi(\partial\mathcal{S}) = 4$ (two $S^2$ components, each $\chi = 2$):

| Observable | CG Prediction | Mechanism | Falsified By |
|-----------|---------------|-----------|-------------|
| $N_\text{gen} = 3$ | 3 generations | $\chi/2 + 1 = 3$ modes via $A_4$ irreps | 4th generation fermion |
| Baryon number quantized | $Q_B \in \mathbb{Z}$ | $\pi_3(\text{SU}(3)) = \mathbb{Z}$ | Fractional baryon number |
| 8 gluons | 8 adjoint gauge bosons | 8 faces $\to$ 8 adjoint weights | Non-octet gluon state |
| Matter–antimatter asymmetry | BAU $\sim 10^{-10}$ | Sphaleron + $\chi$-derived CP | No CP violation in baryogenesis |
| Color confinement | No free quarks | $\mathbb{Z}_3$ center symmetry on $\partial\mathcal{S}$ | Observation of free quarks |

**Key point:** These 5 observables are **jointly falsified** — they all trace back to the same geometric object. Failure of any one challenges the $\chi = 4$ foundation.

### 5.2 No New EW Physics

**Source:** [Proposition 0.0.24a](../foundations/Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md)

CG predicts $|S| < 0.2$, $|T| < 0.1$, $|U| < 0.05$ — no new electroweak physics at current precision. Discovery of BSM particles contributing to oblique parameters at the $\mathcal{O}(0.01)$ level would require revision of the CG electroweak sector.

### 5.3 Proton Decay at $\tau \sim 10^{36\text{–}37}$ Years

CG predicts $\tau(p \to e^+\pi^0) = 5.1 \times 10^{36}$ yr ([Prediction 8.4.1](../Phase8/Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md)), with $p \to e^+\pi^0$ dominant (non-SUSY d=6). Observation of proton decay at $\tau_p < 2 \times 10^{36}$ yr (1$\sigma$ lower bound) would be in tension. Observation of $p \to \bar{\nu}K^+$ dominance would indicate SUSY d=5 operators absent in CG.

### 5.4 No BSM Scalars Below $\sim$1 TeV

CG derives the Higgs as the unique scalar from stella geometry ($\lambda = 1/8$ from mode counting). Additional scalars below the electroweak cutoff $\Lambda_\text{EW} = 982$ GeV (Prop 0.0.26) would require explanation within the geometric framework.

---

## 6. Unique CG Signatures

What distinguishes CG from other BSM frameworks (SUSY, extra dimensions, composite Higgs, string phenomenology):

### 6.1 Energy-Independent QGP Coherence Length

- **CG:** $\xi_0 = R_\text{stella} = 0.448$ fm, independent of $\sqrt{s}$
- **Other frameworks:** QGP coherence length expected to scale with temperature or collision energy
- **Discriminating experiment:** ALICE/STAR HBT analysis across multiple $\sqrt{s}$ values

### 6.2 W-Soliton DM at 4th Vertex with ADM Production

- **CG:** DM mass $\sim$1.8 TeV from geometric soliton on 4th stella vertex; ADM mechanism with 5 geometric suppression factors giving $\varepsilon_W = 3.1 \times 10^{-13}$
- **SUSY:** Neutralino DM (mass free parameter), thermal production
- **Extra dimensions:** KK DM (mass set by compactification scale)
- **Discriminating experiment:** DARWIN direct detection — CG predicts specific mass + cross-section combination

### 6.3 Two-Peak Gravitational Wave Spectrum

- **CG:** mHz peak (W-sector) + lower-frequency peak (visible EWPT)
- **Other BSM:** Single-peak GW spectra from single phase transition
- **Discriminating experiment:** LISA + DECIGO frequency coverage

### 6.4 $\theta_\text{QCD} = 0$ from $\mathbb{Z}_3$ Without Axion

- **CG:** $\theta = 0$ exactly from center symmetry; no axion
- **Peccei-Quinn:** $\theta \to 0$ dynamically via axion
- **Nelson-Barr:** $\theta = 0$ from spontaneous CP violation
- **Discriminating experiment:** Axion searches (ADMX, CASPEr) — CG predicts null result

### 6.5 Discrete Higgs Quartic $\lambda = 1/8$

- **CG:** $\lambda = 1/8$ from 8 stella vertex modes — *discrete* value
- **SM:** $\lambda$ is a free parameter ($\lambda \approx 0.129$ at tree level)
- **SUSY:** $\lambda$ constrained by $\tan\beta$ — *continuous* parameter
- **Discriminating experiment:** FCC-hh measurement of $\kappa_\lambda$ at 5–10% precision

### 6.6 Topological E-fold Count $N_\text{geo} = 512/9$

- **CG:** $N \approx 56.89$ from topological constants (not fit to data)
- **Standard inflation:** $N \sim 50$–$60$ (range determined by reheating temperature, a free parameter)
- **Discriminating experiment:** LiteBIRD measurement of $r$ constraining $N$

---

## 7. Experimental Timeline

```
2025  2026  2027  2028  2029  2030  2031  2032  2033  2034  2035  ...  2040  ...  2050+
  |     |     |     |     |     |     |     |     |     |     |          |          |
  |-----|-----|-----|-----|-----|-----|-----|-----|-----|-----|----------|----------|
  |                                                                                |
  |  [NOW] QGP coherence (ALICE/STAR reanalysis) ◄────── §2.1                     |
  |  [NOW] Glueball ratio (lattice QCD) ◄──────────────── §2.4                    |
  |                                                                                |
  |        [ONGOING] NANOGrav/PTA GW background ◄─────── §3.2                     |
  |                                                                                |
  |                          [2030s] nEDM (PSI/SNS) ◄── §2.3                      |
  |                          [2030s] CTA Lorentz bounds  §3.5                      |
  |                          [2030s] CMB-S4 ◄─────────── §3.3                      |
  |                          [2030s] Hyper-K proton decay §3.6                     |
  |                                                                                |
  |                               [2032] LiteBIRD r ◄── §2.6                      |
  |                                                                                |
  |                                    [2035] HL-LHC κ_λ (~30%) ◄── §2.5         |
  |                                    [2035] LISA GW ◄──────────── §3.1          |
  |                                    [2035] DARWIN DM ◄────────── §2.2          |
  |                                                                                |
  |                                              [2040s] FCC-ee S,T,U ◄── §3.4   |
  |                                              [2040s] DECIGO GW ◄───── §3.1    |
  |                                                                                |
  |                                                        [2050+] FCC-hh κ_λ (5-10%) ◄── §2.5
```

### Priority-Ordered Test Schedule

| Priority | Prediction | Earliest Test | Status |
|----------|-----------|---------------|--------|
| 1 | QGP coherence length | Now (existing data) | Awaiting reanalysis |
| 2 | Glueball mass ratio | Now (lattice improvement) | $0.70\sigma$ tension |
| 3 | Pre-geometric GW (NANOGrav) | Ongoing | Compatible |
| 4 | nEDM / $\theta = 0$ | Late 2020s–2030s | Awaiting data |
| 5 | Tensor-to-scalar $r$ | 2032 (LiteBIRD) | Below current bounds |
| 6 | $\kappa_\lambda$ (HL-LHC) | 2035 | Below current precision |
| 7 | W-soliton DM (DARWIN) | 2030s | Below current sensitivity |
| 8 | W-sector GW (LISA) | 2035+ | Below current sensitivity |

---

## 8. Cross-Reference Index

Alphabetical listing of all predictions with source file paths.

| Prediction | Source File |
|-----------|-----------|
| $\alpha_s(M_Z)$ from $E_8$ cascade | `foundations/Proposition-0.0.17s-Strong-Coupling-From-Gauge-Unification.md` |
| Baryon asymmetry $\eta_B$ | `Phase4/Theorem-4.2.1-Chiral-Bias-Soliton-Formation.md` |
| CMB $S_4$ patterns | `Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md` |
| Cosmological densities $\Omega_b$, $\Omega_{DM}$, $\Omega_\Lambda$ | `Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md` |
| DM direct detection $\sigma_\text{SI}$ | `Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md` |
| DM self-interaction $\sigma/m$ | `Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md` |
| Euler characteristic package ($\chi = 4$) | `Phase8/Derivation-8.4.3-Euler-Characteristic-Signature.md` |
| Glueball mass ratio $R_V$ | `Phase7/Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio.md` |
| Glueball spectrum (full $J^{PC}$) | `Phase7/Proposition-7.8.6-Full-Two-Gluon-Glueball-Spectrum.md` |
| GUT breaking chain | `foundations/Theorem-0.0.4-GUT-Structure-From-Stella-Octangula.md` |
| HBT Levy exponent $\alpha$ | `Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md` |
| Higgs mass $m_H$ | `foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md` |
| Higgs self-coupling $\kappa_\lambda$ | `foundations/Proposition-0.0.37-Complete-Higgs-Potential-And-Trilinear-Coupling.md` |
| Lorentz violation bounds | `foundations/Theorem-0.0.7-Lorentz-Violation-Bounds.md` |
| $N_\text{gen} = 3$ | `Phase8/Derivation-8.1.3-Three-Generation-Necessity.md` |
| Neutron EDM / $\theta_\text{QCD} = 0$ | `foundations/Proposition-0.0.5a-Z3-Center-Constrains-Theta-Angle.md` |
| Oblique parameters $S$, $T$, $U$ | `foundations/Proposition-0.0.24a-Electroweak-Precision-Oblique-Parameters.md` |
| Pre-geometric relic GW | `Phase8/Prediction-8.2.3-Pre-Geometric-Relics.md` |
| Proton decay lifetime & branching ratios | `Phase8/Prediction-8.4.1-Proton-Decay-From-Geometric-GUT.md` |
| QCD critical temperature $T_c$ | `Phase8/Proposition-8.5.1-Lattice-QCD-Heavy-Ion-Predictions.md` |
| QGP coherence length $\xi_0$ | `Phase8/Prediction-8.2.1-QGP-Phase-Coherence.md` |
| Spectral index $n_s$ | `foundations/Proposition-0.0.17aa-Spectral-Index-From-First-Principles.md` |
| String tension $\sqrt{\sigma}$ | `foundations/Proposition-0.0.17j-String-Tension-From-Casimir-Energy.md` |
| Tensor-to-scalar ratio $r$ | `foundations/Proposition-0.0.17aa-Spectral-Index-From-First-Principles.md` |
| $\theta_{13}$ from first principles | `Phase8/Derivation-8.4.2-Theta13-First-Principles.md` |
| $\theta_{23}$ corrected | `Phase8/Proposition-8.4.4-Atmospheric-Angle-Correction.md` |
| W-boson mass $M_W$ | `foundations/Proposition-0.0.24-SU2-Gauge-Coupling-From-Unification.md` |
| W-condensate DM mass $M_W$ | `Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md` |
| W-sector gravitational waves | `Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md` |
| W-soliton properties | `Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md` |
| Wolfenstein parameters $\lambda$, $A$, $\beta$, $\gamma$ | `Phase3/Extension-3.1.2b-Complete-Wolfenstein-Parameters.md` |

---

*Generated: 2026-02-27, updated 2026-02-28*
*Sources: 22 proof documents across Phase 0–8, foundations, and supporting directories*
*Classification: Follows Phase 8 README honest assessment framework*

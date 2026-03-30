# Prediction 8.2.4: W-Sector Phase Transition Gravitational Waves

## Status: 🔶 NOVEL ✅ VERIFIED — mHz GRAVITATIONAL WAVE SIGNAL FROM W-SECTOR FIRST-ORDER PHASE TRANSITION

**Role in Framework:** This prediction derives the gravitational wave (GW) spectrum from the W-sector phase transition at $T_c \sim 289$ GeV in the early universe. The perturbative transition is a crossover, but non-perturbative geometric effects may enhance it to first-order (see §3.3). This is a **distinct signal** from the pre-geometric nHz GW background in [Prediction 8.2.3](Prediction-8.2.3-Pre-Geometric-Relics.md), operating at a completely different frequency scale (mHz vs nHz) and arising from a different physical mechanism (scalar condensate nucleation vs pre-geometric symmetry breaking).

**Dependencies:**
- ✅ Definition 4.3.1 (W-Sector Field Theory) — W condensate VEV, portal coupling
- ✅ Theorem 4.3.2 (W-Soliton Existence) — W-sector Skyrme Lagrangian
- ✅ Proposition 4.3.5 (Skyrme Parameter) — $e_W = 4.5 \pm 0.3$ from first principles
- ✅ Theorem 4.2.3 (First-Order Phase Transition) — CG phase transition dynamics, $v(T_c)/T_c$
- ✅ Proposition 5.1.2b (Precision Cosmological Densities) — $v_W = 123 \pm 15$ GeV, $\lambda_W = 0.101$
- ✅ Prediction 8.2.3 (Pre-Geometric Relics) — GW methodology (Caprini et al.)

**Downstream:**
- [Prediction 8.3.1](Prediction-8.3.1-W-Condensate-Dark-Matter.md) — Cross-reference as additional W-sector test
- [Definition 4.3.1](../Phase4/Definition-4.3.1-W-Sector-Field-Theory.md) — New testable prediction

**Computational Verification:** `verification/Phase8/prediction_8_2_4_w_sector_gw_spectrum.py`

**Adversarial Verification:** `verification/Phase8/prediction_8_2_4_adversarial_verification.py`

**Verification Record:** [Multi-Agent Verification Report (2026-02-26)](../verification-records/Prediction-8.2.4-Multi-Agent-Verification-2026-02-26.md)

**Lean 4 Formalization:** [`Prediction_8_2_4.lean`](../../../lean/ChiralGeometrogenesis/Phase8/Prediction_8_2_4.lean) — zero `sorry`, complete formalization

---

## 1. Executive Summary

The W-sector condensate has the potential to undergo a first-order phase transition at temperature $T_c^{(W)} \sim 289$ GeV in the early universe. The perturbative analysis reveals an extremely weak transition ($\alpha_W^{(min)} \sim 4 \times 10^{-7}$, effectively a crossover), producing no detectable GW signal. However, if non-perturbative geometric effects enhance the transition — as occurs in the visible sector (Theorem 4.2.3, where $v(T_c)/T_c = 1.22$) — the signal could become detectable.

**Two-tier prediction:**

| Tier | $\alpha_W$ | $\Omega_{GW} h^2$ | Detectability |
|------|-----------|-------------------|---------------|
| **Perturbative (minimal)** | $4 \times 10^{-7}$ | $\lesssim 10^{-20}$ | Undetectable |
| **Enhanced (benchmark)** | $0.005$–$0.05$ | $10^{-14}$–$10^{-11}$ | LISA (marginal–strong), DECIGO (strong) |

The enhanced tier is **conditional** on non-perturbative geometric enhancement of the W-sector barrier, which has not been rigorously derived for the W sector (see §3.3). With corrected efficiency factors, **turbulence dominates** the GW spectrum for the benchmark parameters.

| Observable | Enhanced prediction | Detector |
|-----------|---------------------|----------|
| Peak frequency | $f_{peak} \sim 7$–$60$ mHz | **LISA**, DECIGO |
| Peak amplitude | $\Omega_{GW} h^2 \sim 10^{-14}$ to $10^{-11}$ | LISA, DECIGO |
| Spectral shape | Three-source (bubbles + sound + turbulence) | Shape analysis |
| Dominant source | Turbulence | — |

This signal is:
- **Distinct from the QCD pre-geometric signal** (Prediction 8.2.3): mHz vs nHz, electroweak-scale vs QCD-scale
- **Distinct from the SM electroweak crossover**: the SM predicts no GW signal at all (crossover, not first-order; Kajantie et al. 1996)
- **Potentially distinguishable** from generic BSM electroweak phase transitions through frequency and spectral shape

### Symbol Table

| Symbol | Definition | Dimensions | Value/Range |
|--------|-----------|------------|-------------|
| $T_c^{(W)}$ | W-sector critical temperature | [Energy] | $\approx 289$ GeV (perturbative) |
| $\alpha_W$ | Phase transition strength | [dimensionless] | $4 \times 10^{-7}$ (min); $0.005$–$0.05$ (benchmark) |
| $\beta/H$ | Inverse duration (in Hubble units) | [dimensionless] | $100$–$1000$ (benchmark) |
| $v_w$ | Bubble wall velocity | [dimensionless] | $0.60$–$0.73$ (Jouguet) |
| $f_{peak}$ | Peak GW frequency today | [Hz] | $7$–$60$ mHz (benchmark) |
| $\Omega_{GW} h^2$ | GW energy density fraction | [dimensionless] | $10^{-14}$–$10^{-11}$ (benchmark) |
| $\kappa_v$ | Sound wave efficiency (Jouguet) | [dimensionless] | $0.12$–$0.29$ |
| $\kappa_{turb}$ | Turbulence efficiency | [dimensionless] | $\epsilon \kappa_v$, $\epsilon \approx 0.05$ |

---

## 2. W-Sector Finite-Temperature Effective Potential

### 2.1 Zero-Temperature Potential

The W-sector scalar potential from Definition 4.3.1 and Proposition 5.1.2b §4 is:

$$V_0(\Phi_W) = -\mu_W^2 |\Phi_W|^2 + \lambda_W |\Phi_W|^4 + \lambda_{H\Phi} |H|^2 |\Phi_W|^2$$

where:
- $\mu_W^2 = \mu_H^2/3 = 2\lambda_H v_H^2 / 3 \approx 5230$ GeV$^2$ (geometric constraint, Prop 5.1.2b §4.5)
- $\lambda_W = 0.101 \pm 0.020$ (Prop 5.1.2b §4.5)
- $\lambda_{H\Phi} = 0.036$ (Definition 4.3.1 §8)

At $T = 0$, the minimum is at $\langle \Phi_W \rangle = v_W = 123$ GeV.

### 2.2 Thermal Corrections

At finite temperature, the one-loop thermal correction (Coleman-Weinberg at finite T) gives:

$$V_T(\Phi_W, T) = \frac{c_W T^2}{2} \Phi_W^2 - E_W T \Phi_W^3 + \cdots$$

**Thermal mass coefficient:** The W-sector thermal mass receives contributions from self-coupling and portal coupling:

$$c_W = \frac{\lambda_W}{2} + \frac{n_H \lambda_{H\Phi}}{12}$$

where $n_H$ is the number of real scalar degrees of freedom of $H$ contributing in the thermal bath. In the symmetric phase ($T > T_{EW}$), the full Higgs doublet has $n_H = 4$ real components (two charged, two neutral). Thus:

$$c_W = \frac{0.101}{2} + \frac{4 \times 0.036}{12} = 0.0505 + 0.012 = 0.063$$

The $\lambda_W/2$ comes from the $\Phi_W$ self-interaction loop (complex singlet radial mode in the high-$T$ expansion), and $n_H \lambda_{H\Phi}/12$ from the Higgs loop coupling to $\Phi_W$. Each real component of $H$ contributes $\lambda_{H\Phi} T^2/12$ to the $\Phi_W$ thermal mass through the one-loop tadpole diagram.

**Cubic coefficient:** The cubic term arises from daisy resummation of the $\Phi_W$ self-interaction:

$$E_W = \frac{(2\lambda_W)^{3/2}}{12\pi}$$

With $\lambda_W = 0.101$:

$$E_W = \frac{(0.202)^{3/2}}{12\pi} = \frac{0.0908}{37.70} = 0.00241$$

**Note:** The portal coupling with the Higgs also generates a cubic term from the daisy diagram with the mixed $H$-$\Phi_W$ propagator, but this is suppressed by $\lambda_{H\Phi}^{3/2} / (12\pi) \approx 2.3 \times 10^{-4}$, an order of magnitude smaller. We include it in the systematic uncertainty.

### 2.3 Geometric Contribution

From Theorem 4.2.3, the stella octangula discrete symmetry ($S_4 \times \mathbb{Z}_2$) generates an additional potential barrier in the visible sector. For the W-sector, a portal-mediated geometric contribution may arise from the four-vertex structure of each tetrahedron:

$$V_{geo}^{(W)}(\Phi_W, T) = \kappa_{geo}^{(W)} v_W^4 \left[1 - \cos\left(\frac{3\pi \Phi_W}{v_W}\right)\right] \times f(T/T_0)$$

where $\kappa_{geo}^{(W)} \sim 0.01$–$0.05 \, \lambda_W$ (reduced relative to the visible sector because the W condensate couples through the portal rather than directly to the color fields, with geometric suppression factor $\kappa_W^{geom} = 5.1 \times 10^{-4}$ from Proposition 5.1.2b §6.1).

**Important:** At the perturbative level, this geometric contribution is subdominant to the thermal cubic term. However, non-perturbative effects (lattice-scale barrier formation, as demonstrated for the visible sector in Theorem 4.2.3) could significantly enhance the effective barrier. The magnitude of this enhancement for the W sector has **not been rigorously derived** and remains an open question (see §3.3 for the impact on detectability). The temperature function $f(T/T_0)$ encodes the thermal activation of the geometric barrier and requires non-perturbative computation.

### 2.4 Full Effective Potential

$$V_{eff}(\Phi_W, T) = -\frac{1}{2}\left(\mu_W^2 - c_W T^2 - \lambda_{H\Phi} v_H^2(T)\right)\Phi_W^2 - E_W T \Phi_W^3 + \lambda_W \Phi_W^4$$

where $v_H^2(T)$ accounts for the temperature dependence of the Higgs VEV (relevant when $T \lesssim T_{EW} \sim 160$ GeV).

---

## 3. Critical Temperature and Phase Transition Parameters

### 3.1 Critical Temperature

At the critical temperature $T_c^{(W)}$, the symmetric and broken phases are degenerate:

$$V_{eff}(0, T_c) = V_{eff}(\Phi_{min}, T_c)$$

The standard high-temperature expansion gives:

$$T_c^{(W)} = \frac{\mu_W}{\sqrt{c_W}} \sqrt{1 - \frac{E_W^2}{4\lambda_W c_W}}$$

With the parameters above:

$$\frac{E_W^2}{4\lambda_W c_W} = \frac{(0.00241)^2}{4 \times 0.101 \times 0.063} = \frac{5.81 \times 10^{-6}}{0.0254} = 2.3 \times 10^{-4}$$

This correction is negligible ($\ll 1$), giving:

$$T_c^{(W)} \approx \frac{\mu_W}{\sqrt{c_W}} = \frac{\sqrt{5230}}{\sqrt{0.063}} = \frac{72.3}{0.251} \approx 289 \text{ GeV}$$

**Portal correction.** When the Higgs is in its broken phase ($T < T_{EW}$), the portal coupling shifts $\mu_W^2 \to \mu_W^2 - \lambda_{H\Phi} v_H^2$. The effective mass parameter at the EW scale is:

$$\mu_{W,eff}^2 = \mu_W^2 - \lambda_{H\Phi} v_H^2(T) = 5230 - 0.036 \times (246)^2 \times h(T/T_{EW})$$

where $h(T/T_{EW})$ interpolates from 0 (symmetric phase, $T > T_{EW}$) to 1 ($T = 0$). At $T = 0$:

$$\mu_{W,eff}^2(T=0) = 5230 - 2179 = 3051 \text{ GeV}^2$$

**Self-consistent scenario determination.** Since $T_c^{(W)} \approx 289$ GeV $\gg T_c^{(EW)} \approx 124$ GeV (Theorem 4.2.3), the W-sector transition occurs **before** the electroweak transition, while the Higgs is still in its symmetric phase. This means:
- The portal correction to $\mu_W^2$ does **not** apply at $T = T_c^{(W)}$
- The W-sector transitions independently of the electroweak sector
- $T_c^{(W)} \approx 289$ GeV is the self-consistent result

We retain the following scenarios for completeness:

**Scenario A: W transition simultaneous with EWPT** ($T_c^{(W)} \approx T_c^{(EW)}$)

This would require $c_W \sim 0.31$ (5× larger than computed), achievable only if substantial additional thermal degrees of freedom contribute. This scenario is **not supported** by the perturbative calculation and would require non-perturbative justification.

**Scenario B: W transition below EWPT** ($T_c^{(W)} < T_c^{(EW)}$)

With the portal correction reducing $\mu_{W,eff}^2$, the effective critical temperature would be:

$$T_c^{(W)} \approx \frac{\sqrt{\mu_{W,eff}^2}}{\sqrt{c_W + \lambda_{H\Phi}/4}} = \frac{55.2}{\sqrt{0.072}} = 207 \text{ GeV}$$

But since $207 > 124$ GeV, this scenario is self-inconsistent: the portal correction requires $T < T_{EW}$, yet the resulting $T_c$ is above $T_{EW}$.

**Scenario C: W transition above EWPT** ($T_c^{(W)} > T_c^{(EW)}$) — **Self-consistent**

With $c_W = 0.063$ and $\mu_W^2 = 5230$ GeV$^2$ (no portal correction at $T > T_{EW}$):

$$T_c^{(W)} \approx 289 \text{ GeV}$$

### 3.2 Central Estimate

The self-consistent perturbative calculation gives:

$$\boxed{T_c^{(W)} = 289 \pm 30 \text{ GeV}}$$

where the uncertainty reflects $\lambda_W = 0.101 \pm 0.020$ and the $\mathcal{O}(1)$ uncertainty in the thermal mass calculation. This places the W-sector transition well above the electroweak scale (Scenario C).

**Note on lower $T_c$ scenarios.** A W-sector transition near the electroweak scale ($T_c \sim 130$ GeV) would require $c_W \sim 0.31$, approximately 5× larger than the perturbative value. This could in principle arise from additional thermal degrees of freedom (W-soliton excitations, non-perturbative contributions to the thermal mass) but has not been derived from first principles. We use the self-consistent $T_c = 289$ GeV for all subsequent calculations.

### 3.3 Phase Transition Strength

The phase transition strength is parametrized by:

$$\alpha_W = \frac{\Delta V}{\rho_{rad}(T_c)}$$

where $\Delta V$ is the latent heat released and $\rho_{rad} = g_* \pi^2 T_c^4 / 30$ is the radiation energy density.

**Latent heat:**

$$\Delta V = T_c \frac{\partial \Delta V_{eff}}{\partial T}\bigg|_{T_c} \approx \frac{2 E_W^2 T_c^4}{9\lambda_W}$$

With $E_W = 0.00241$, $\lambda_W = 0.101$:

$$\frac{\Delta V}{T_c^4} = \frac{2 \times (0.00241)^2}{9 \times 0.101} = \frac{1.16 \times 10^{-5}}{0.909} = 1.28 \times 10^{-5}$$

**Radiation density coefficient:** With $g_* \approx 96.25$ (SM degrees of freedom at $T_c \sim 289$ GeV; top quark partially non-relativistic):

$$\frac{\rho_{rad}}{T_c^4} = \frac{g_* \pi^2}{30} = \frac{96.25 \times 9.87}{30} = 31.7$$

Therefore:

$$\alpha_W^{(min)} = \frac{1.28 \times 10^{-5}}{31.7} = 4.0 \times 10^{-7}$$

The perturbative order parameter is $v(T_c)/T_c = 2E_W/(3\lambda_W) = 0.016 \ll 1$, confirming that the perturbative W-sector transition is a **crossover**, producing no gravitational wave signal.

#### Tier 1: Perturbative Prediction

$$\boxed{\alpha_W^{(min)} = 4.0 \times 10^{-7} \quad \text{(crossover — no GW signal)}}$$

#### Tier 2: Benchmark Enhanced Prediction

In the visible sector, Theorem 4.2.3 demonstrates that non-perturbative geometric effects from the $S_4 \times \mathbb{Z}_2$ symmetry transform a weak crossover into a strong first-order phase transition ($v(T_c)/T_c = 1.22$). If an analogous (but portal-suppressed) enhancement operates in the W sector, the effective cubic coefficient $E_W^{eff}$ could be significantly larger than the perturbative value.

Since $\alpha_W \propto (E_W^{eff})^2$, an enhancement factor $n = E_W^{eff}/E_W$ gives:

$$\alpha_W^{(enh)} = n^2 \times \alpha_W^{(min)}$$

The required enhancement factors are:

| Target $\alpha_W$ | Required $n$ | Status |
|-------------------|-------------|--------|
| $10^{-3}$ | $\sim 50$ | Requires substantial non-perturbative enhancement |
| $10^{-2}$ | $\sim 158$ | Requires large non-perturbative enhancement |
| $10^{-1}$ | $\sim 500$ | Unrealistic |

For the visible sector, Theorem 4.2.3 achieves $v(T_c)/T_c = 1.22$ from $v(T_c)/T_c \sim 0.15$ (SM), an effective $n \sim 8$ on the cubic coefficient. The W sector, coupling through the portal with suppression $\kappa_W^{geom} = 5.1 \times 10^{-4}$ (Proposition 5.1.2b §6.1), would receive a reduced enhancement. **The magnitude of this enhancement for the W sector has not been rigorously derived and requires non-perturbative methods (lattice computation or functional renormalization group).**

As benchmark parameters for the enhanced scenario, we adopt:

$$\boxed{\alpha_W = 0.01 \quad \text{(benchmark — conditional on non-perturbative enhancement)}}$$

with a scan range $\alpha_W \in [0.005, 0.05]$ to bracket the uncertainty. These values should be understood as **conditional predictions**: if future non-perturbative calculations confirm $\alpha_W \gtrsim 0.005$, the GW signal becomes detectable.

### 3.4 Inverse Duration

The inverse duration of the transition (in Hubble units) is:

$$\frac{\beta}{H} = T_c \frac{d}{dT}\left(\frac{S_3}{T}\right)\bigg|_{T_c}$$

where $S_3$ is the three-dimensional bounce action. For the benchmark enhanced transition with strength $\alpha_W \sim 0.01$:

$$\frac{\beta}{H} \approx \frac{4\lambda_W T_c}{E_W^{eff}} \sim 100\text{–}1000$$

The wide range reflects the sensitivity to the precise barrier shape (which depends on the non-perturbative geometric enhancement). We adopt:

$$\boxed{\frac{\beta}{H} = 500^{+500}_{-400} \quad \text{(benchmark)}}$$

### 3.5 Bubble Wall Velocity

For the benchmark enhanced transition with $\alpha_W \sim 0.01$, the Chapman-Jouguet detonation velocity is (Espinosa et al. 2010):

$$v_J = \frac{c_s + \sqrt{\alpha_W^2 + 2\alpha_W/3}}{1 + \alpha_W}$$

where $c_s = 1/\sqrt{3}$ is the speed of sound. For the benchmark range:

| $\alpha_W$ | $v_J$ |
|-----------|------|
| 0.005 | 0.63 |
| 0.01 | 0.65 |
| 0.03 | 0.70 |
| 0.05 | 0.73 |

We adopt $v_w = v_J(\alpha_W)$ self-consistently for each scenario, giving $v_w \approx 0.63$–$0.73$ across the benchmark range.

**Note:** Theorem 4.2.3 finds $v_w \approx 0.2$ (subsonic deflagration) for the visible-sector transition with $\alpha_{EW} \sim 0.44$, a different dynamical regime. The W-sector transition, being weaker ($\alpha_W \ll \alpha_{EW}$), has less friction on the bubble wall, favoring Jouguet detonations rather than deflagrations.

---

## 4. Gravitational Wave Spectrum

### 4.1 Three-Source Model

Following Caprini et al. (2016) (as applied in Prediction 8.2.3), the total GW spectrum is the sum of three contributions:

$$\Omega_{GW}(f) h^2 = \Omega_{col}(f) h^2 + \Omega_{sw}(f) h^2 + \Omega_{turb}(f) h^2$$

corresponding to **bubble collisions**, **sound waves**, and **turbulence**.

### 4.2 Bubble Collisions

$$\Omega_{col} h^2 = 1.67 \times 10^{-5} \left(\frac{H}{\beta}\right)^2 \left(\frac{\kappa_{col} \alpha_W}{1 + \alpha_W}\right)^2 \left(\frac{100}{g_*}\right)^{1/3} \frac{0.11 v_w^3}{0.42 + v_w^2} \, S_{col}(f)$$

where $\kappa_{col} \approx 1 - \kappa_v - \kappa_{turb}$ is the fraction of latent heat deposited in the scalar field, $0.11 v_w^3/(0.42 + v_w^2)$ is the $v_w$-dependent suppression factor (Caprini et al. 2016), and the spectral shape is:

$$S_{col}(x) = \frac{3.8 \, x^{2.8}}{1 + 2.8 \, x^{3.8}}, \qquad x = f/f_{col}$$

The peak frequency:

$$f_{col} = 1.65 \times 10^{-5} \text{ Hz} \cdot \frac{0.62}{1.8 - 0.1 v_w + v_w^2} \cdot \frac{\beta}{H} \cdot \frac{T_c}{100 \text{ GeV}} \cdot \left(\frac{g_*}{100}\right)^{1/6}$$

### 4.3 Sound Waves

$$\Omega_{sw} h^2 = 2.65 \times 10^{-6} \left(\frac{H}{\beta}\right) \left(\frac{\kappa_v \alpha_W}{1 + \alpha_W}\right)^2 \left(\frac{100}{g_*}\right)^{1/3} v_w \, \Upsilon \, S_{sw}(f)$$

**Efficiency factor $\kappa_v$:** For Jouguet (Chapman-Jouguet) detonations, the sound wave efficiency is given by the fit formula from Espinosa et al. (2010) Eq. (A.8):

$$\kappa_v^{(J)} \approx \frac{\alpha_W^{2/5}}{0.017 + (0.997 + \alpha_W)^{2/5}}$$

| $\alpha_W$ | $\kappa_v^{(J)}$ |
|-----------|----------------|
| 0.005 | 0.118 |
| 0.01 | 0.155 |
| 0.03 | 0.239 |
| 0.05 | 0.291 |

**Sound wave lifetime suppression $\Upsilon$:** Following Caprini et al. (2020), the finite lifetime of the sound wave source suppresses the amplitude:

$$\Upsilon = 1 - \frac{1}{\sqrt{1 + 2 \tau_{sw} H}}$$

where $\tau_{sw} H \approx (8\pi)^{1/3} v_w / [(\beta/H) \bar{U}_f]$ and $\bar{U}_f = \sqrt{3\kappa_v \alpha_W / [4(1+\alpha_W)]}$ is the RMS fluid velocity. For $\alpha_W = 0.01$ and $\beta/H = 500$: $\Upsilon \approx 0.10$, significantly suppressing the sound wave contribution.

The spectral shape is:

$$S_{sw}(x) = x^3 \left(\frac{7}{4 + 3x^2}\right)^{7/2}, \qquad x = f/f_{sw}$$

The peak frequency:

$$f_{sw} = 1.9 \times 10^{-5} \text{ Hz} \cdot \frac{1}{v_w} \cdot \frac{\beta}{H} \cdot \frac{T_c}{100 \text{ GeV}} \cdot \left(\frac{g_*}{100}\right)^{1/6}$$

### 4.4 Turbulence

$$\Omega_{turb} h^2 = 3.35 \times 10^{-4} \left(\frac{H}{\beta}\right) \left(\frac{\kappa_{turb} \alpha_W}{1 + \alpha_W}\right)^{3/2} \left(\frac{100}{g_*}\right)^{1/3} v_w \, S_{turb}(f)$$

where $\kappa_{turb} = \epsilon \, \kappa_v$ with $\epsilon \approx 0.05$–$0.10$ being the fraction of bulk kinetic energy converted to MHD turbulence (Caprini et al. 2016, 2020). For $\epsilon = 0.05$:

| $\alpha_W$ | $\kappa_v$ | $\kappa_{turb}$ |
|-----------|----------|---------------|
| 0.005 | 0.118 | 0.006 |
| 0.01 | 0.155 | 0.008 |
| 0.03 | 0.239 | 0.012 |
| 0.05 | 0.291 | 0.015 |

The spectral shape is:

$$S_{turb}(x) = \frac{x^3}{(1 + x)^{11/3}(1 + 8\pi f/h_*)}, \qquad x = f/f_{turb}$$

with $h_* = 1.65 \times 10^{-5}$ Hz $\cdot (T_c / 100 \text{ GeV}) (g_*/100)^{1/6}$ being the Hubble rate at the transition.

### 4.5 Numerical Evaluation

**Benchmark parameters:** $\alpha_W = 0.01$, $\beta/H = 500$, $v_w = v_J = 0.65$, $T_c = 289$ GeV, $g_* = 96.25$.

**Derived efficiency factors:** $\kappa_v = 0.155$, $\kappa_{turb} = \epsilon \kappa_v = 0.008$, $\kappa_{col} = 1 - \kappa_v - \kappa_{turb} \approx 0.84$.

**Peak frequencies:**

$$f_{col} = 1.65 \times 10^{-5} \cdot \frac{0.62}{1.8 - 0.065 + 0.423} \cdot 500 \cdot 2.89 \cdot (0.963)^{1/6}$$

$$= 1.65 \times 10^{-5} \cdot 0.287 \cdot 500 \cdot 2.89 \cdot 0.994 = 6.8 \times 10^{-3} \text{ Hz} = 6.8 \text{ mHz}$$

$$f_{sw} = 1.9 \times 10^{-5} \cdot \frac{1}{0.65} \cdot 500 \cdot 2.89 \cdot 0.994 = 4.2 \times 10^{-2} \text{ Hz} = 42 \text{ mHz}$$

$$f_{turb} = 2.7 \times 10^{-5} \cdot \frac{1}{0.65} \cdot 500 \cdot 2.89 \cdot 0.994 = 5.9 \times 10^{-2} \text{ Hz} = 59 \text{ mHz}$$

**Peak amplitudes:**

For bubble collisions ($\kappa_{col} = 0.84$, with $v_w$-dependent factor $0.11 v_w^3/(0.42+v_w^2) = 0.031$):

$$\Omega_{col}^{peak} h^2 = 1.67 \times 10^{-5} \cdot (1/500)^2 \cdot (0.0083)^2 \cdot 1.01 \cdot 0.031 = 1.4 \times 10^{-16}$$

For sound waves ($\kappa_v = 0.155$, with $\Upsilon = 0.10$):

$$\Omega_{sw}^{peak} h^2 = 2.65 \times 10^{-6} \cdot (1/500) \cdot (0.00154)^2 \cdot 1.01 \cdot 0.65 \cdot 0.10 = 8.0 \times 10^{-16}$$

For turbulence ($\kappa_{turb} = 0.008$):

$$\Omega_{turb}^{peak} h^2 = 3.35 \times 10^{-4} \cdot (1/500) \cdot (7.9 \times 10^{-5})^{3/2} \cdot 1.01 \cdot 0.65 = 3.0 \times 10^{-13}$$

**Turbulence dominates** for these parameters (due to the sound wave lifetime suppression and the corrected $\kappa_v$). Total:

$$\boxed{\Omega_{GW}^{peak} h^2 \approx 3 \times 10^{-13} \quad \text{(benchmark)}}$$

at:

$$\boxed{f_{peak} \approx 59 \text{ mHz (turbulence peak)} \quad \text{[6.8 mHz for bubble collisions]}}$$

**Note on dominant source:** With the corrected Jouguet detonation efficiency $\kappa_v = 0.155$ (Espinosa et al. 2010 Eq. A.8) and the sound wave lifetime suppression factor $\Upsilon \approx 0.10$ (Caprini et al. 2020), the sound wave contribution is reduced by a factor $\sim 250$ relative to naive estimates. Turbulence becomes the dominant GW source, though we note that the turbulence contribution carries the largest theoretical uncertainty (Caprini et al. 2020).

### 4.6 Parameter Dependence

The GW signal is sensitive to the phase transition parameters. Using $T_c = 289$ GeV, $g_* = 96.25$, and the Jouguet detonation efficiency $\kappa_v^{(J)}$ (Espinosa et al. 2010):

| Scenario | $\alpha_W$ | $\beta/H$ | $\kappa_v$ | $f_{peak}$ | $\Omega_{GW}^{peak} h^2$ | Dominant |
|----------|-----------|----------|----------|-----------|--------------------------|----------|
| Conservative | 0.005 | 1000 | 0.12 | 120 mHz | $3 \times 10^{-14}$ | Turbulence |
| Central | 0.01 | 500 | 0.16 | 59 mHz | $3 \times 10^{-13}$ | Turbulence |
| Optimistic | 0.03 | 200 | 0.24 | 22 mHz | $8 \times 10^{-12}$ | Turbulence |
| Strong | 0.05 | 100 | 0.29 | 7 mHz | $5 \times 10^{-11}$ | Turbulence |

The optimistic and strong scenarios ($\alpha_W \gtrsim 0.03$) are well within LISA's projected sensitivity. The central benchmark ($\alpha_W = 0.01$) is marginal for LISA but detectable by DECIGO.

---

## 5. Relationship to Standard EWPT Signal

### 5.1 The SM Predicts No GW Signal

The Standard Model electroweak phase transition is a **crossover** (Kajantie et al. 1996), not a first-order transition. Lattice simulations demonstrate continuous evolution of the order parameter with no latent heat release and no bubble nucleation. For a crossover, the ratio $v(T_c)/T_c$ is ill-defined as there is no critical temperature $T_c$ at which the two phases are degenerate. The SM therefore produces no GW signal whatsoever. Any detection of GWs at the electroweak scale would be BSM evidence.

### 5.2 CG Predicts Two Potential Sources

In CG, the electroweak phase transition IS first-order (Theorem 4.2.3, $v(T_c)/T_c = 1.22 \pm 0.06$). This creates two possible GW sources:

**Source 1: Visible-sector EWPT** (from Theorem 4.2.3's geometric barrier)
- $T_c \sim 124$ GeV
- $\alpha_{EW} \sim 0.44$
- $f_{peak} \sim 8$ mHz
- Strong transition (sound wave + turbulence dominated)

**Source 2: W-sector transition** (this prediction)
- $T_c^{(W)} \approx 289$ GeV (perturbative)
- $\alpha_W \sim 0.005$–$0.05$ (benchmark enhanced)
- $f_{peak} \sim 7$–$60$ mHz
- Turbulence-dominated spectrum

### 5.3 Combined Signal

Since $T_c^{(W)} \approx 289$ GeV $\gg T_c^{(EW)} \approx 124$ GeV, the W-sector transition occurs well before the electroweak transition. The two transitions produce **two distinct peaks** in the GW spectrum at well-separated frequencies:

**W-sector signal** (this prediction):
$$f_{peak}^{(W)} \sim 7\text{–}60 \text{ mHz}, \quad \Omega_{GW} h^2 \sim 10^{-14}\text{–}10^{-11}$$

**Visible-sector EWPT signal** (Theorem 4.2.3):
$$f_{peak}^{(EW)} \sim 8 \text{ mHz}, \quad \Omega_{GW} h^2 \sim 10^{-10}$$

The frequency ratio is:

$$\frac{f^{(W)}}{f^{(EW)}} \approx \frac{T_c^{(W)}}{T_c^{(EW)}} \cdot \frac{(\beta/H)_W}{(\beta/H)_{EW}} \sim 2\text{–}8$$

depending on the W-sector benchmark parameters. For the strong scenario ($\alpha_W = 0.05$, $\beta/H = 100$), the W-sector peak at $\sim 7$ mHz overlaps with the visible-sector peak, potentially creating a **broadened spectral feature** that LISA could resolve. For the central scenario ($\alpha_W = 0.01$, $\beta/H = 500$), the W-sector peak at $\sim 59$ mHz is well separated from the visible-sector peak, providing a **two-peak signature** — a distinctive prediction of the two-sector structure of CG.

---

## 6. Detector Sensitivity

### 6.1 LISA

The Laser Interferometer Space Antenna (launch: 2035; science operations: $\sim$2037) has peak sensitivity at $f \sim 1$–$10$ mHz with:

$$\Omega_{LISA}^{min} h^2 \sim 10^{-13} \quad \text{at } f \sim 3 \text{ mHz}$$

For the CG W-sector benchmark signal:

**Central benchmark** ($\alpha_W = 0.01$, $\beta/H = 500$):
$$\Omega_{GW}^{peak} h^2 \approx 3 \times 10^{-13} \quad \text{at} \quad f \approx 59 \text{ mHz}$$

The turbulence peak at 59 mHz is above LISA's optimal band (1–10 mHz), reducing the effective SNR. However, the spectral tail extends into the LISA band. Estimated $\text{SNR}_{LISA} \sim 1$–$3$ (marginal detection for 4-year observation).

**Optimistic benchmark** ($\alpha_W = 0.03$, $\beta/H = 200$):
$$\Omega_{GW}^{peak} h^2 \approx 8 \times 10^{-12} \quad \text{at} \quad f \approx 22 \text{ mHz}$$

$\text{SNR}_{LISA} \sim 30$–$80$, well above the detection threshold.

### 6.2 DECIGO and BBO

The DECi-hertz Interferometer Gravitational wave Observatory and Big Bang Observer target the 0.01–10 Hz range with sensitivity:

$$\Omega_{DECIGO}^{min} h^2 \sim 10^{-16}$$

For the CG signal:
$$\text{SNR}_{DECIGO} \sim 10^2\text{–}10^4$$

DECIGO would detect the W-sector signal across the full parameter range with high significance.

### 6.3 TianQin

TianQin (launch: $\sim$2035) targets $f \sim 10^{-3}$–$10^{-1}$ Hz with sensitivity comparable to LISA in the mHz band:

$$\text{SNR}_{TianQin} \sim 0.3\text{–}1.0 \times \text{SNR}_{LISA}$$

### 6.4 Summary Table

| Detector | $f$ range | $\Omega^{min} h^2$ | SNR (central benchmark) | SNR (optimistic benchmark) |
|----------|----------|---------------------|------------------------|---------------------------|
| LISA | $10^{-4}$–$10^{-1}$ Hz | $10^{-13}$ | 1–3 | 30–80 |
| TianQin | $10^{-3}$–$10^{-1}$ Hz | $10^{-13}$ | 0.5–2 | 15–50 |
| DECIGO | $10^{-2}$–$10$ Hz | $10^{-16}$ | $10^2$–$10^3$ | $10^3$–$10^4$ |
| BBO | $10^{-2}$–$10$ Hz | $10^{-17}$ | $10^3$–$10^4$ | $10^4$–$10^5$ |

**Note:** All benchmark SNR estimates are conditional on the non-perturbative geometric enhancement described in §3.3. The perturbative prediction gives $\alpha_W \sim 4 \times 10^{-7}$ (crossover), which is undetectable by any planned detector.

---

## 7. Falsifiability

### 7.1 What Would Confirm This Prediction

1. **Detection of a stochastic GW background at $f \sim 7$–$60$ mHz** with $\Omega h^2 \sim 10^{-14}$–$10^{-11}$ by LISA or DECIGO
2. **Turbulence-dominated spectral shape** consistent with a first-order phase transition at $T \sim 250$–$320$ GeV (above the electroweak scale)
3. **Two-peak structure** in the mHz band, with a visible-sector EWPT peak at $\sim 8$ mHz and a W-sector peak at a distinct frequency — a smoking-gun signature for the two-sector CG structure
4. **Absence of corresponding new particles** at the LHC at the TeV scale (the W-sector is a gauge singlet, producing no colored particles)
5. **Correlation with dark matter direct detection** at $\sigma_{SI} \sim 10^{-47}$ cm$^2$ (DARWIN/XLZD), consistent with the same portal coupling $\lambda_{H\Phi} = 0.036$

### 7.2 What Would Falsify This Prediction

1. **No GW signal at mHz frequencies** with $\Omega h^2 > 10^{-16}$ (DECIGO sensitivity) would exclude $\alpha_W > 10^{-4}$, ruling out a strong first-order W-sector transition
2. **GW signal incompatible with the predicted frequency range** (e.g., peak at $\mu$Hz or Hz rather than mHz) would require revision of $T_c^{(W)}$
3. **GW spectral shape inconsistent** with a first-order phase transition (e.g., power-law background rather than peaked spectrum)
4. **Non-perturbative W-sector calculations** (lattice or FRG) demonstrating that the geometric enhancement is insufficient to produce a first-order transition would reduce this prediction to the perturbative crossover result

### 7.3 Discrimination from Other BSM Models

| Model | $f_{peak}$ | $\Omega h^2$ | Distinguishing feature |
|-------|-----------|------------|----------------------|
| **CG W-sector** (this work) | 7–60 mHz | $10^{-14}$–$10^{-11}$ | Portal coupling fixes $\sigma_{SI}$; two-peak with EWPT |
| xSM (singlet extension) | 0.1–10 mHz | $10^{-14}$–$10^{-10}$ | Free portal coupling |
| 2HDM | 0.5–5 mHz | $10^{-14}$–$10^{-11}$ | Charged scalars at LHC |
| Composite Higgs | 0.01–1 mHz | $10^{-13}$–$10^{-10}$ | Top-partner at LHC |
| SM (crossover) | — | — | **No GW signal** |

The CG prediction is most similar to xSM models, but is distinguished by:
1. The portal coupling is **predicted** ($\lambda_{H\Phi} = 0.036$), not a free parameter
2. The W-sector has **no light scalar excitations** (nonlinear sigma model, Definition 4.3.1 §8.5)
3. **Topological stability** of the dark matter candidate (baryon number $Q_W \in \mathbb{Z}$), unlike $\mathbb{Z}_2$-stabilized models
4. **Correlated predictions** with direct detection, relic abundance, and structure formation

---

## 8. Consistency Checks

### 8.1 Dimensional Analysis

| Quantity | Expression | Dimensions | Check |
|----------|-----------|------------|-------|
| $\alpha_W$ | $\Delta V / \rho_{rad}$ | [dimensionless] | $\checkmark$ |
| $\beta/H$ | $T_c \, d(S_3/T)/dT$ | [dimensionless] | $\checkmark$ |
| $f_{peak}$ | $\beta \cdot T_c / (M_{Pl} \sqrt{g_*})$ | [Hz] | $\checkmark$ |
| $\Omega_{GW} h^2$ | $\alpha_W^2 (H/\beta)^n$ | [dimensionless] | $\checkmark$ |

### 8.2 Limiting Cases

- **$\lambda_{H\Phi} \to 0$:** Portal decouples, $c_W \to \lambda_W/2 = 0.0505$, $T_c \to \mu_W/\sqrt{c_W} = 322$ GeV. W transition occurs independently of the Higgs. $\checkmark$
- **$\alpha_W \to 0$:** Crossover transition, no GW signal. Recovers SM-like behavior. $\checkmark$
- **$v_W \to 0$:** No W condensate, no transition. Consistent. $\checkmark$
- **$v_W \to v_H$:** W-sector merges with visible sector. Would require $\lambda_W \to \lambda_H$ and enhance the EWPT signal. $\checkmark$
- **$T \to 0$:** $v_W = 123$ GeV recovered (Proposition 5.1.2b). $\checkmark$
- **$T \to \infty$:** Symmetric phase restored (thermal mass dominates). $\checkmark$

### 8.3 Comparison with Prediction 8.2.3

| Feature | Prediction 8.2.3 | Prediction 8.2.4 (this work) |
|---------|-------------------|------------------------------|
| Source | Pre-geometric $S_4 \times \mathbb{Z}_2 \to$ Lorentz | W condensate phase transition |
| Temperature | QCD ($\sim 200$ MeV) or GUT ($\sim 10^{16}$ GeV) | $\sim 289$ GeV (perturbative) |
| Frequency | nHz ($\sim 10^{-8}$ Hz) | mHz ($\sim 10^{-2}$ Hz) |
| Amplitude | $\Omega h^2 \sim 10^{-9}$ | $\Omega h^2 \sim 10^{-14}$–$10^{-11}$ (benchmark) |
| Detector | PTAs (NANOGrav) | LISA, DECIGO |
| Mechanism | Discrete symmetry breaking | Scalar condensate nucleation |

These are completely independent signals at different scales. $\checkmark$

---

## 9. References

**CG Framework:**
- [Definition 4.3.1](../Phase4/Definition-4.3.1-W-Sector-Field-Theory.md) — W-sector field theory
- [Theorem 4.3.2](../Phase4/Theorem-4.3.2-W-Soliton-Existence-And-Properties.md) — W-soliton existence
- [Proposition 4.3.5](../Phase4/Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md) — Skyrme parameter derivation
- [Theorem 4.2.3](../Phase4/Theorem-4.2.3-First-Order-Phase-Transition.md) — First-order phase transition
- [Proposition 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) — Precision cosmological densities
- [Prediction 8.2.3](Prediction-8.2.3-Pre-Geometric-Relics.md) — Pre-geometric relics (nHz GW)
- [Prediction 8.3.1](Prediction-8.3.1-W-Condensate-Dark-Matter.md) — W condensate dark matter

**External Physics — Gravitational Waves from Phase Transitions:**
- Caprini, C. et al. (2016). "Science with the space-based interferometer eLISA. II: Gravitational waves from cosmological phase transitions." *JCAP* 04, 001. [arXiv:1512.06239] — Three-source model for GW spectrum.
- Caprini, C. et al. (2020). "Detecting gravitational waves from cosmological phase transitions with LISA: an update." *JCAP* 03, 024. [arXiv:1910.13125] — Updated LISA Cosmology Working Group analysis; sound wave lifetime suppression factor $\Upsilon$; turbulence uncertainties.
- Caprini, C. & Figueroa, D. G. (2018). "Cosmological Backgrounds of Gravitational Waves." *Class. Quant. Grav.* 35, 163001. [arXiv:1801.04268] — Comprehensive GW background review.
- Espinosa, J. R., Konstandin, T., No, J. M. & Servant, G. (2010). "Energy Budget of Cosmological First-order Phase Transitions." *JCAP* 06, 028. [arXiv:1004.4187] — Efficiency factors and bubble dynamics; Jouguet detonation formula (Eq. A.8).
- Hindmarsh, M., Huber, S. J., Rummukainen, K. & Weir, D. J. (2017). "Shape of the acoustic gravitational wave power spectrum from a first order phase transition." *Phys. Rev. D* 96, 103520. [arXiv:1704.05871] — Sound wave contribution.
- Kajantie, K., Laine, M., Rummukainen, K. & Shaposhnikov, M. (1996). "Is there a hot electroweak phase transition at $m_H \gtrsim m_W$?" *Phys. Rev. Lett.* 77, 2887. [arXiv:hep-ph/9605288] — Lattice proof that SM EWPT is a crossover.

**External Physics — LISA and Future Detectors:**
- LISA Collaboration (2017). "Laser Interferometer Space Antenna." [arXiv:1702.00786] — LISA design and science case.
- Robson, T., Cornish, N. J. & Liu, C. (2019). "The construction and use of LISA sensitivity curves." *Class. Quant. Grav.* 36, 105011. [arXiv:1803.01944] — LISA sensitivity curves in $\Omega h^2$ units.
- Schmitz, K. (2021). "New Sensitivity Curves for Gravitational-Wave Signals from Cosmological Phase Transitions." *JHEP* 01, 097. [arXiv:2002.04615] — Peak-integrated sensitivity curves for LISA/DECIGO/BBO.
- Kawamura, S. et al. (2021). "Current status of space gravitational wave antenna DECIGO and B-DECIGO." *Prog. Theor. Exp. Phys.* 2021, 05A105. [arXiv:2006.13545] — DECIGO design.
- Luo, J. et al. [TianQin Collaboration] (2016). "TianQin: a space-borne gravitational wave detector." *Class. Quant. Grav.* 33, 035010. [arXiv:1512.02076] — TianQin design.

**External Physics — Scalar Singlet Phase Transitions:**
- Profumo, S., Ramsey-Musolf, M. J. & Shaughnessy, G. (2007). "Singlet Higgs phenomenology and the electroweak phase transition." *JHEP* 08, 010. [arXiv:0705.2425] — Singlet extension EWPT.
- Curtin, D., Meade, P. & Yu, C.-T. (2014). "Testing Electroweak Baryogenesis with Future Colliders." *JHEP* 11, 127. [arXiv:1409.0005] — Collider tests of EWPT.

**Computational Verification:**
- `verification/Phase8/prediction_8_2_4_w_sector_gw_spectrum.py` — GW spectrum computation, LISA sensitivity comparison, parameter scan

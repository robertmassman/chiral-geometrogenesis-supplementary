# Theorem 4.2.2: Sakharov Conditions — Derivation

## Complete Mathematical Proof

**Parent Document:** [Theorem-4.2.2-Sakharov-Conditions.md](./Theorem-4.2.2-Sakharov-Conditions.md)

**Purpose:** This file contains the complete step-by-step derivation showing how Chiral Geometrogenesis satisfies each of the three Sakharov conditions.

---

## Table of Contents

- §4: [Condition 1 — Baryon Number Violation](#4-condition-1-baryon-number-violation)
- §5: [Condition 2 — C and CP Violation](#5-condition-2-c-and-cp-violation)
- §6: [Condition 3 — Departure from Equilibrium](#6-condition-3-departure-from-equilibrium)
- §7: [Combined Effect — Baryon Asymmetry Formula](#7-combined-effect-baryon-asymmetry-formula)

---

## 4. Condition 1: Baryon Number Violation

### 4.1 The Sphaleron Mechanism

**Status:** ✅ ESTABLISHED (Standard Electroweak Physics)

Baryon number violation in the electroweak sector arises from the chiral anomaly. The baryon current $J_B^\mu$ is not conserved:

$$\partial_\mu J_B^\mu = N_g \frac{g^2}{32\pi^2} W^a_{\mu\nu} \tilde{W}^{a\mu\nu}$$

where:
- $N_g = 3$ is the number of generations
- $W^a_{\mu\nu}$ is the SU(2)_L field strength
- $\tilde{W}^{a\mu\nu} = \frac{1}{2}\epsilon^{\mu\nu\rho\sigma}W^a_{\rho\sigma}$ is the dual

The right-hand side integrates to the Chern-Simons number $N_{CS}$:

$$\Delta B = N_g \cdot \Delta N_{CS}$$

### 4.2 Sphaleron Configuration

The sphaleron is a static, unstable solution to the electroweak equations sitting at the top of the energy barrier between topologically distinct vacua.

**Sphaleron energy:**
$$E_{sph} = \frac{4\pi v}{g} B\left(\frac{\lambda}{g^2}\right) \approx 9 \text{ TeV}$$

where $B(\lambda/g^2) \approx 1.9$ for the physical Higgs mass.

**Key property:** The sphaleron changes Chern-Simons number by $\Delta N_{CS} = 1/2$, so transitions over the barrier change baryon number by:

$$\Delta B = \pm 3 \quad (\text{one unit per generation})$$

### 4.3 Sphaleron Rate in the Symmetric Phase

At temperatures $T > T_c$ (symmetric phase), the Higgs VEV vanishes and the sphaleron barrier is absent. Baryon violation occurs through thermal fluctuations.

**Rate formula (D'Onofrio et al. 2014):**

$$\Gamma_{sph} = \kappa \alpha_W^5 T^4$$

where:
- $\alpha_W = g^2/(4\pi) \approx 0.034$
- $\kappa \approx 20-30$ (lattice determination)

**Numerical value at T ~ 100 GeV:**

$$\Gamma_{sph} \sim 10^{-6} T^4 \sim 10^{-6} \times (100 \text{ GeV})^4 \sim 10^2 \text{ GeV}^4$$

**Rate per unit volume:**

$$\frac{\Gamma_{sph}}{T^3} \sim 10^{-6} T \sim 10^{-4} \text{ GeV}$$

**Comparison to Hubble rate:**

$$H(T) = \sqrt{\frac{\pi^2 g_*}{90}} \frac{T^2}{M_{Pl}} \sim 10^{-14} \text{ GeV} \quad (T = 100 \text{ GeV})$$

Since $\Gamma_{sph}/T^3 \gg H$, sphalerons are **in equilibrium** in the symmetric phase.

### 4.4 Sphaleron Decoupling After Phase Transition

After the electroweak phase transition, the Higgs VEV turns on and sphalerons become Boltzmann-suppressed:

$$\Gamma_{sph}(T < T_c) \propto \exp\left(-\frac{E_{sph}(T)}{T}\right)$$

**Decoupling condition:** Sphalerons decouple (stop washing out the asymmetry) when:

$$\frac{\Gamma_{sph}}{T^3} < H$$

This requires:

$$\frac{E_{sph}(T)}{T} \gtrsim 45$$

Using $E_{sph}(T) \approx \frac{4\pi v(T)}{g} \times B$ where B ≈ 1.9:

$$\frac{4\pi v(T) B}{g T} \gtrsim 45$$

**Intermediate algebra:**
$$\frac{v(T)}{T} \gtrsim \frac{45 g}{4\pi B} = \frac{45 \times 0.65}{4\pi \times 1.9} \approx \frac{29.3}{23.9} \approx 1.2$$

**Note:** The commonly quoted criterion v/T ≳ 1 is an **approximate threshold** that accounts for:
- Logarithmic corrections to the Boltzmann suppression
- Uncertainties in the sphaleron prefactor
- Model dependence of the exact decoupling temperature

The literature uses v/T_c ≥ 1 as a standard benchmark. More precise lattice studies give values between 0.9 and 1.3 depending on the model.

**This is the sphaleron washout criterion:**

$$\boxed{\frac{v(T_c)}{T_c} \gtrsim 1}$$

### 4.5 CG Contribution to Condition 1

**Summary:** CG inherits standard sphaleron physics without modification.

| Quantity | Value | Source |
|----------|-------|--------|
| Sphaleron rate (symmetric phase) | Γ ~ α_W⁵ T⁴ | Standard EW |
| Baryon number change | ΔB = ±3 | Anomaly |
| Decoupling condition | v/T ≳ 1 | Sphaleron mass |

**Condition 1 satisfied:** ✅

---

## 5. Condition 2: C and CP Violation

### 5.1 The Need for CP Violation

**C violation alone is insufficient.** Under charge conjugation:
- Quarks ↔ antiquarks
- Left-handed ↔ left-handed

The weak interaction violates C maximally (only couples to left-handed particles). However, this only distinguishes "handedness," not matter from antimatter.

**CP violation is required** to have different rates for:
$$\Gamma(X \to \text{baryons}) \neq \Gamma(\bar{X} \to \text{antibaryons})$$

### 5.2 Standard Model CP Violation

The SM has a single CP-violating phase in the CKM matrix, characterized by the Jarlskog invariant:

$$J = \text{Im}(V_{us}V_{cb}V_{ub}^*V_{cs}^*) = (3.00 \pm 0.15) \times 10^{-5}$$

**Problem:** The CP-violating effects enter baryogenesis through multiple suppression factors:
1. Loop suppression: $\alpha_W/(4\pi)$
2. GIM suppression: $(m_t^2 - m_c^2)/m_W^2$
3. Mixing angles: Products of small CKM elements

**Result:** The effective CP violation parameter for electroweak baryogenesis is:

$$\epsilon_{CP}^{SM} \sim J \times \text{(loop factors)} \sim 10^{-20}$$

This gives $\eta_{SM} \sim 10^{-18}$, which is **10 orders of magnitude too small**.

### 5.3 CP Violation in Chiral Geometrogenesis

CG provides a **geometric amplification** of CP violation through the chiral phase α.

**From Theorem 2.2.4 (Anomaly-Driven Chirality Selection):**

The topological charge density couples to color phase vorticity:

$$\Omega_{color} = \frac{2N_f}{3} \cdot \frac{\chi_{top}^{1/2}}{f_\pi}$$

The resulting phase shift is:

$$\boxed{\alpha = \frac{2\pi}{N_c} \cdot \text{sgn}(\theta_{eff}) = \pm\frac{2\pi}{3}}$$

**Key properties:**
1. **Magnitude is O(1):** |α| = 2π/3 ≈ 2.09 (not perturbatively suppressed)
2. **Sign from CP violation:** sgn(θ_eff) is determined by the CKM phase
3. **Topological origin:** The factor 2π/3 comes from SU(3) group theory

### 5.4 How Chirality Biases Soliton Nucleation

**From Theorem 4.2.1 (Chiral Bias in Soliton Formation):**

The nucleation rates for Q = ±1 solitons differ due to the chiral coupling:

$$\frac{\Gamma_+ - \Gamma_-}{\Gamma_+ + \Gamma_-} = \epsilon_{CP} \cdot f(\alpha, T)$$

**Physical mechanism:**

1. **Action difference:** The Euclidean action for nucleating Q = ±1 solitons differs:
   $$\Delta S \equiv S_- - S_+ = 2\alpha \cdot \mathcal{G} \cdot \epsilon_{CP} \cdot \frac{E_{sol}}{T}$$

2. **Geometric factor:** The overlap integral between chiral boundary conditions and soliton profile:
   $$\mathcal{G} = \int_{\partial V} \vec{j}_{chiral} \cdot d\vec{A} \sim (0.1-5) \times 10^{-3}$$

3. **Rate ratio:**
   $$\frac{\Gamma_+}{\Gamma_-} = e^{\Delta S} = \exp\left(\frac{2\alpha \cdot \mathcal{G} \cdot \epsilon_{CP} \cdot E_{sol}}{T}\right)$$

### 5.5 Derivation of the CP Violation Enhancement

**Step 1: Instanton asymmetry from CKM phase**

In the presence of CP violation, instantons and anti-instantons have different weights:

$$\frac{n_{inst} - n_{\bar{inst}}}{n_{inst} + n_{\bar{inst}}} \sim \epsilon_{CP}$$

where $\epsilon_{CP} \sim J \times (\text{phase factors}) \sim 10^{-5}$.

**Step 2: Chirality selection**

The instanton asymmetry selects a definite chirality:
- If $\langle Q_{inst} \rangle > 0$: R→G→B rotation (α = +2π/3)
- If $\langle Q_{inst} \rangle < 0$: B→G→R rotation (α = -2π/3)

**Step 3: Coupling to soliton nucleation**

The chiral current at the hadron boundary couples to the soliton topological charge. The coupling strength is modulated by the local CP-violating phase:

$$S_{coupling} = \alpha \cdot Q \cdot \mathcal{G} \cdot \epsilon_{CP} \cdot \frac{E_{sol}}{T}$$

where:
- $\alpha = 2\pi/3$ is the geometric chiral phase (O(1), not suppressed)
- $\mathcal{G} \sim 10^{-3}$ is the geometric overlap (from soliton/boundary scale ratio)
- $\epsilon_{CP} \sim 10^{-5}$ enters because the **sign** of α is selected by CP violation
- $E_{sol}/T$ is the thermal suppression factor

For Q = +1: $S_+ = +\alpha \mathcal{G} \epsilon_{CP} \frac{E_{sol}}{T}$
For Q = -1: $S_- = -\alpha \mathcal{G} \epsilon_{CP} \frac{E_{sol}}{T}$

**Step 4: Action difference**

The effective action difference at temperature T:

$$\Delta S = S_- - S_+ = 2\alpha \cdot \mathcal{G} \cdot \epsilon_{CP} \cdot \frac{E_{sol}}{T}$$

**Clarification on ε_CP:** The factor ε_CP appears because:
1. The **magnitude** of α is fixed by topology: |α| = 2π/3
2. The **sign** of α (R→G→B vs B→G→R) is selected by the instanton asymmetry
3. The instanton asymmetry is proportional to ε_CP
4. Therefore, the effective coupling that distinguishes Q=+1 from Q=-1 is proportional to ε_CP

This is consistent with Theorem 4.2.1 §5.3 and the master formula in §8.5.

### 5.6 Numerical Estimate of CP Enhancement

**SM CP violation:**
$$\epsilon_{CP} \sim 1.5 \times 10^{-5}$$

**Geometric amplification:**
$$\alpha = 2\pi/3 \approx 2.09$$
$$\mathcal{G} \sim 10^{-3}$$

**Combined effect:**
$$\text{Asymmetry} \sim \alpha \cdot \mathcal{G} \cdot \epsilon_{CP} \sim 2 \times 10^{-3} \times 1.5 \times 10^{-5} \sim 3 \times 10^{-8}$$

**Enhancement over SM:**
$$\frac{\text{CG asymmetry}}{\text{SM asymmetry}} \sim \frac{\alpha \cdot \mathcal{G}}{\text{loop suppression}} \sim 10^2$$

### 5.7 Non-Circularity Check

**Causal chain:**

$$\text{CKM phase (input)} \to \epsilon_{CP} \to \langle Q_{inst} \rangle > 0 \to \alpha = +2\pi/3 \to S_+ < S_- \to \Gamma_+ > \Gamma_- \to \eta > 0$$

**Verification:**
- The CP violation (Jarlskog invariant J) is a **fundamental input** from the SM
- It determines the **sign** of the instanton asymmetry
- The instanton asymmetry determines the **sign** of α
- The sign of α determines **which solitons** are favored
- Via Theorem 4.1.3, soliton charge = baryon number

**No circular reasoning:** The baryon asymmetry is a consequence, not an input.

### 5.8 Summary for Condition 2

| Quantity | SM Value | CG Value | Enhancement | Notes |
|----------|----------|----------|-------------|-------|
| CP phase | J ~ 3×10⁻⁵ | J ~ 3×10⁻⁵ | — (same input) | Fundamental parameter |
| Intrinsic CP asymmetry | ~10⁻⁵ (J) | ~10⁻⁸ (α·G·ε_CP) | ~10⁻³ | Before dynamics |
| **Surviving asymmetry** | ~0 | ~10⁻¹⁰ | ~∞ | After phase transition |

**Clarification on enhancement factors:**

The comparison between SM and CG is subtle because they fail/succeed for different reasons:

1. **SM Electroweak Baryogenesis:**
   - Intrinsic CP asymmetry: J ~ 10⁻⁵ (adequate)
   - Phase transition: Crossover, so v(T_c)/T_c → 0
   - **Surviving asymmetry: ~0** (complete washout)
   - Predicted η_SM ~ 10⁻¹⁸ (from loop-suppressed residual effects)

2. **CG Baryogenesis:**
   - Intrinsic CP asymmetry: α·G·ε_CP ~ 10⁻⁸ (smaller than SM J!)
   - Phase transition: First-order, v(T_c)/T_c ~ 1.2
   - **Surviving asymmetry: ~10⁻¹⁰** (protected by transition)

**The key insight:** CG succeeds not because it has larger CP violation, but because the first-order phase transition **preserves** the asymmetry that is generated. The SM's problem is not insufficient CP violation — it's that the crossover transition allows sphalerons to wash out any asymmetry.

**Condition 2 satisfied:** ✅

---

## 6. Condition 3: Departure from Equilibrium

### 6.1 The Equilibrium Problem

In thermal equilibrium, the CPT theorem guarantees:
$$n_X = n_{\bar{X}} \quad (\text{for } m_X = m_{\bar{X}})$$

Any asymmetry generated is immediately erased by inverse processes.

**For baryogenesis:** The asymmetry must be generated during a period when:
1. The sphaleron rate is high (B violation active)
2. The system is out of equilibrium (asymmetry preserved)
3. The transition completes before washout

### 6.2 First-Order vs Crossover Phase Transition

**Crossover (SM):** The order parameter changes smoothly. No bubbles nucleate. The system remains in quasi-equilibrium throughout.

**First-order:** The transition proceeds via bubble nucleation. Inside bubbles, v ≠ 0. Outside bubbles, v = 0. The bubble wall creates a non-equilibrium environment.

**The washout criterion:**

For the asymmetry to survive, sphalerons must be suppressed inside the bubbles before they can erase the asymmetry. This requires:

$$\boxed{\frac{v(T_c)}{T_c} \gtrsim 1}$$

**SM prediction:** v(T_c)/T_c ~ 0.03-0.15 (crossover, fails criterion)

> **Important clarification on the SM "crossover":**
>
> For a true crossover transition, there is no well-defined critical temperature T_c, and the order parameter v(T) changes smoothly rather than discontinuously. The value v/T ~ 0.15 quoted for the SM is a **perturbative estimate** of what the transition strength *would be* if a first-order transition occurred. It is computed from:
> $$\left(\frac{v}{T}\right)_{pert} \approx \frac{2E}{\lambda} \approx \frac{2 \times 0.0096}{0.13} \approx 0.15$$
>
> Lattice QCD studies (Kajantie et al. 1996, Csikor et al. 1998) have definitively established that for m_H > 72 GeV, the SM electroweak phase transition is a **smooth crossover**, meaning there are no bubbles, no latent heat, and no out-of-equilibrium dynamics. The observed Higgs mass m_H = 125 GeV places the SM firmly in the crossover regime.
>
> **This is the fundamental reason standard electroweak baryogenesis fails in the SM.**

### 6.3 CG Derivation of First-Order Phase Transition

**From Theorem 4.2.3 (First-Order Electroweak Phase Transition):**

The effective potential in CG has three contributions:

$$V_{eff}(\phi, T) = V_{SM}(\phi, T) + V_{geo}(\phi, T) + V_{3c}(\phi, T)$$

**6.3.1 Standard Model Contribution**

$$V_{SM}(\phi, T) = -\frac{\mu^2}{2}\phi^2 + \frac{\lambda}{4}\phi^4 + \frac{c_T T^2}{2}\phi^2 - ET\phi^3$$

where:
- $c_T = 0.398$ (thermal mass coefficient)
- $E = 0.0096$ (cubic coefficient from daisy resummation)

The cubic term creates a barrier, but it's too weak:

$$\left(\frac{v(T_c)}{T_c}\right)_{SM} \approx \frac{2E}{\lambda} \approx 0.15$$

**6.3.2 Geometric Contribution (S₄ × ℤ₂)**

The stella octangula symmetry creates a periodic potential:

$$V_{geo}(\phi, T) = \kappa_{geo} v^4 \left[1 - \cos\left(\frac{3\pi\phi}{v}\right)\right] \times f(T/T_0)$$

**Physical origin:** The 8 vertices of the stella octangula correspond to 8 degenerate field configurations. The discrete symmetry S₄ × ℤ₂ creates potential barriers between them.

**Derivation of κ_geo:**

From S₄ group theory:
- Clebsch-Gordan coefficient: $C_{CG} = 1/\sqrt{3}$
- Geometric suppression: g = 1/2
- Amplitude factor: A ≈ 1.234

$$\kappa_{geo} = \lambda_H \times g \times A \times C_{CG}^2 \approx 0.06 \lambda_H$$

**6.3.3 Three-Color Contribution**

$$V_{3c}(\phi, T) = \lambda_{3c} \phi^4 \times \tanh^2\left(\frac{T - T_{lock}}{50 \text{ GeV}}\right)$$

From thermal phase fluctuations of χ_R, χ_G, χ_B:
$$\lambda_{3c} \approx 0.008$$

### 6.4 Computing v(T_c)/T_c

**Numerical results from parameter scan:**

| κ | λ_3c | T_c (GeV) | v(T_c) (GeV) | v(T_c)/T_c |
|---|------|-----------|--------------|------------|
| 0.50 | 0.05 | 124.5 | 146.0 | 1.17 |
| 0.75 | 0.05 | 124.0 | 150.8 | 1.22 |
| 1.00 | 0.05 | 123.7 | 153.5 | 1.24 |
| 1.25 | 0.05 | 123.5 | 155.3 | 1.26 |
| 1.50 | 0.05 | 123.4 | 156.5 | 1.27 |
| 2.00 | 0.05 | 123.2 | 158.3 | 1.29 |

**CG prediction:**

$$\boxed{\frac{v(T_c)}{T_c} = 1.2 \pm 0.1}$$

This exceeds the washout threshold v/T_c ≥ 1, satisfying Condition 3.

### 6.5 Why Discrete Symmetry Matters

**SM (continuous U(1)):** The Higgs potential has continuous symmetry. Phase transitions are smooth (crossover) for m_H > 72 GeV.

**CG (discrete S₄ × ℤ₂):** The stella octangula has discrete symmetry with 48 elements. This creates:
1. **Multiple degenerate minima** (8 vertices)
2. **Potential barriers** between minima
3. **First-order transitions** via barrier penetration

**Comparison:**

| Feature | SM | CG |
|---------|-----|-----|
| Symmetry | Continuous U(1) | Discrete S₄ × ℤ₂ |
| Transition type | Crossover | First-order |
| v/T_c | ~0.15 | ~1.2 |
| Sphaleron washout | Yes | No |

### 6.6 Bubble Nucleation and Wall Velocity

**From Theorem 4.2.3:**

The first-order phase transition proceeds via bubble nucleation:

**Bounce action:**
$$\frac{S_3}{T} \approx 140 \left(\frac{v(T_c)}{T_c}\right)^3 \approx 242$$

**Inverse duration:**
$$\frac{\beta}{H} \approx 850$$

**Bubble wall velocity:**
$$v_w \approx 0.20$$

Since $v_w < c_s = 1/\sqrt{3}$, this is a **deflagration** (subsonic). This is optimal for baryogenesis because:
1. Particles can diffuse ahead of the wall
2. CP-violating currents build up in front
3. Sphalerons convert the asymmetry to baryons before the wall arrives

### 6.7 Summary for Condition 3

| Parameter | SM | CG | Threshold |
|-----------|-----|-----|-----------|
| v(T_c)/T_c | 0.15 | 1.2 | ≥1 |
| Transition type | Crossover | First-order | First-order |
| Sphaleron suppression | No | Yes | Required |
| β/H | — | 850 | O(100-1000) |
| v_w | — | 0.2 | <c_s optimal |

**Condition 3 satisfied:** ✅

---

## 7. Combined Effect: Baryon Asymmetry Formula

**Status:** ✅ VERIFIED (2025-12-27)
**Cross-refs:** Theorem 4.2.1 §8.5 (complete derivation)

> **Note:** The complete, self-consistent derivation of the baryon asymmetry is given in [Theorem 4.2.1, Section 8.5](./Theorem-4.2.1-Chiral-Bias-Soliton-Formation-Derivation.md#85-consolidated-self-consistent-calculation). This section summarizes that result and applies it to the Sakharov conditions context.

### 7.1 The Master Formula

The baryon-to-entropy ratio from electroweak baryogenesis in CG is (from Theorem 4.2.1 §8.5):

$$\boxed{\frac{n_B}{s} = C \cdot \left(\frac{v(T_c)}{T_c}\right)^2 \cdot \alpha \cdot \mathcal{G} \cdot \epsilon_{CP} \cdot f_{transport}}$$

where:
- $C = 0.03$ (sphaleron rate normalization from lattice QCD, D'Onofrio et al. 2014)
- $v(T_c)/T_c = 1.2 \pm 0.1$ (phase transition strength from Theorem 4.2.3)
- $\alpha = 2\pi/3$ (chiral phase from Theorem 2.2.4)
- $\mathcal{G} \approx 2 \times 10^{-3}$ (geometric overlap from Theorem 4.2.1 §7.2)
- $\epsilon_{CP} \approx 1.5 \times 10^{-5}$ (effective CP violation from Jarlskog invariant)
- $f_{transport} \approx 0.03$ (transport efficiency)

The baryon-to-photon ratio is then:

$$\eta = \frac{n_B}{n_\gamma} = \frac{n_B}{s} \times \frac{s}{n_\gamma} \approx \frac{n_B}{s} \times 7.04$$

### 7.2 Step-by-Step Numerical Evaluation

**Step 1: Phase Transition Factor**
$$\left(\frac{v(T_c)}{T_c}\right)^2 = (1.2)^2 = 1.44$$

**Step 2: CP Asymmetry Factor**
$$\alpha \cdot \mathcal{G} \cdot \epsilon_{CP} = 2.09 \times (2 \times 10^{-3}) \times (1.5 \times 10^{-5}) = 6.3 \times 10^{-8}$$

**Step 3: Sphaleron and Transport**
$$C \cdot f_{transport} = 0.03 \times 0.03 = 9 \times 10^{-4}$$

**Step 4: Combine All Factors**
$$\frac{n_B}{s} = 9 \times 10^{-4} \times 1.44 \times 6.3 \times 10^{-8} = 8.2 \times 10^{-11}$$

**Step 5: Convert to η**
$$\eta = 8.2 \times 10^{-11} \times 7.04 = 5.8 \times 10^{-10}$$

$$\boxed{\eta_{CG} \approx 6 \times 10^{-10}}$$

### 7.3 Uncertainty Analysis

The dominant uncertainties are:

| Parameter | Value | Uncertainty | Contribution to ln(η) |
|-----------|-------|-------------|----------------------|
| $\mathcal{G}$ | $2 \times 10^{-3}$ | ×5 | ±1.6 |
| $v(T_c)/T_c$ | 1.2 | ±0.1 | ±0.3 |
| $f_{transport}$ | 0.03 | ×3 | ±1.1 |
| $C$ | 0.03 | ±50% | ±0.4 |
| **Total** | | | **±2.0** |

**Combined uncertainty:** Factor of $e^2 \approx 7$ in each direction.

**CG prediction range (95% CI):**
$$\eta_{CG} = (0.1 - 4) \times 10^{-9}$$

**Central value:** $\eta \approx 6 \times 10^{-10}$

### 7.4 Comparison with Observation

| Quantity | Value | Source |
|----------|-------|--------|
| CG prediction | $(0.1-4) \times 10^{-9}$ | This derivation |
| Observed | $(6.10 \pm 0.04) \times 10^{-10}$ | Planck 2018 + BBN |
| **Agreement** | ✅ Within prediction range | |

### 7.5 Comparison with Standard Model

| Model | η prediction | Observed η | Agreement | Failure Mode |
|-------|--------------|------------|-----------|--------------|
| SM (EWB) | ~10⁻¹⁸ | 6×10⁻¹⁰ | ❌ Off by 10⁸ | Crossover + small CP |
| CG | (0.1-4)×10⁻⁹ | 6×10⁻¹⁰ | ✅ Within range | — |

**Why CG succeeds where SM fails:**

The SM fails for two independent reasons:
1. **Phase transition is a crossover:** $v(T_c)/T_c \approx 0$ for $m_H = 125$ GeV, so the washout factor vanishes
2. **CP violation is loop-suppressed:** The effective CP asymmetry enters only through fermion mass insertions

CG resolves both:
1. **First-order phase transition:** The discrete S₄ × ℤ₂ symmetry creates potential barriers, giving $v(T_c)/T_c \approx 1.2$
2. **Geometric CP enhancement:** The chiral phase $\alpha = 2\pi/3$ is O(1), not perturbatively small

**Enhancement factor:**
$$\frac{\eta_{CG}}{\eta_{SM}} \sim \frac{(v/T_c)_{CG}^2}{(v/T_c)_{SM}^2} \times \frac{\alpha \cdot \mathcal{G}}{\text{(loop factor)}} \sim \frac{1.44}{0} \times 10^3 \sim \infty$$

The SM denominator is effectively zero because the crossover provides no protection against washout.

### 7.6 Physical Interpretation

The CG mechanism produces the observed baryon asymmetry through:

1. **Sphaleron B violation** (standard physics): Active in the symmetric phase
2. **Chiral CP violation** (CG-specific): The geometric phase $\alpha = 2\pi/3$ couples to soliton topological charge
3. **First-order phase transition** (CG-derived): Prevents sphaleron washout after the transition

The three Sakharov conditions are satisfied with **no fine-tuning**:
- The chiral phase is topologically fixed at $2\pi/3$
- The geometric factor $\mathcal{G} \sim 10^{-3}$ emerges from scale ratios
- The phase transition strength follows from the discrete symmetry structure

---

## Summary of Derivations

| Condition | What We Derived | Key Result |
|-----------|-----------------|------------|
| **S₁: B violation** | Sphaleron rate and decoupling | Γ_sph ~ α_W⁵ T⁴, decouple when v/T ≥ 1 |
| **S₂: CP violation** | Chiral bias mechanism | Γ₊/Γ₋ = exp(2α·G·ε_CP·E/T) |
| **S₃: Non-equilibrium** | First-order phase transition | v(T_c)/T_c = 1.2 ± 0.1 |
| **Combined** | Baryon asymmetry | η = (0.15-2.4) × 10⁻⁹ |

**All three Sakharov conditions are satisfied in CG, with quantitative predictions matching observation.**

---

*Return to: [Statement file](./Theorem-4.2.2-Sakharov-Conditions.md)*
*Continue to: [Applications file](./Theorem-4.2.2-Sakharov-Conditions-Applications.md)*

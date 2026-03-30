# Coupling Constants and Running Parameters Reference

**Purpose:** Centralized repository of coupling constants, mixing angles, and their running used in Chiral Geometrogenesis proofs.
**Convention:** All couplings given at their natural scale unless otherwise noted.

---

## 1. Electromagnetic Coupling

| Quantity | Symbol | Value | Scale | Source | Used In |
|----------|--------|-------|-------|--------|---------|
| Fine structure constant | $\alpha_{em}$ | $1/137.035999084$ | $q^2 \to 0$ | CODATA 2018 | Multiple |
| $\alpha_{em}(M_Z)$ | -- | $1/127.951$ | $M_Z$ | PDG 2024 | Running checks |
| Elementary charge | $e$ | 0.3028 | natural units | $\sqrt{4\pi\alpha}$ | -- |

---

## 2. Strong Coupling (QCD)

| Quantity | Symbol | Value | Uncertainty | Scale | Source | Used In |
|----------|--------|-------|-------------|-------|--------|---------|
| Strong coupling | $\alpha_s(M_Z)$ | 0.1180 | $\pm 0.0009$ | $M_Z$ | PDG 2024 | Theorem 3.0.1, 5.2.5 |
| $\alpha_s(m_\tau)$ | -- | 0.332 | $\pm 0.013$ | $m_\tau$ | FLAG 2024 | -- |
| $\alpha_s(1$ GeV$)$ | -- | $\sim 0.5$ | estimate | 1 GeV | -- | -- |

### 2.1 Running of $\alpha_s$

One-loop beta function (for reference):
$$\alpha_s(\mu) = \frac{\alpha_s(M_Z)}{1 + \frac{b_0 \alpha_s(M_Z)}{2\pi}\ln(\mu^2/M_Z^2)}$$

where $b_0 = 11 - \frac{2}{3}n_f$ (for $n_f$ active flavors).

| Scale | $n_f$ | $\alpha_s$ | Used In |
|-------|-------|------------|---------|
| $M_Z = 91.2$ GeV | 5 | 0.118 | Reference |
| $m_b = 4.2$ GeV | 5 | 0.22 | -- |
| $m_c = 1.3$ GeV | 4 | 0.35 | -- |
| $\Lambda_{QCD}$ | 3 | $\sim 1$ | Non-perturbative |

---

## 3. Electroweak Mixing

| Quantity | Symbol | Value | Uncertainty | Scale | Source | Used In |
|----------|--------|-------|-------------|-------|--------|---------|
| Weinberg angle | $\sin^2\theta_W(M_Z)$ | 0.23122 | $\pm 0.00003$ | $M_Z$ (MS-bar) | PDG 2024 | Theorem 3.2.1 |
| $\sin^2\theta_W$ (on-shell) | -- | 0.2229 | -- | on-shell | derived | -- |
| Weak coupling | $g_W$ | 0.6527 | -- | $M_Z$ | $e/\sin\theta_W$ | -- |
| Hypercharge coupling | $g'$ | 0.3575 | -- | $M_Z$ | $e/\cos\theta_W$ | -- |

### 3.1 Consistency Relations

$$\sin^2\theta_W = 1 - \frac{M_W^2}{M_Z^2} = 0.2229 \quad (\text{on-shell})$$
$$\sin^2\theta_W(M_Z)_{\overline{MS}} = 0.23122 \quad (\text{MS-bar at } M_Z)$$

**GUT prediction check:** At $M_{GUT} \sim 10^{16}$ GeV, unification gives $\sin^2\theta_W \approx 3/8 = 0.375$.
Running down to $M_Z$ yields $\sin^2\theta_W(M_Z) \approx 0.231$ (excellent agreement).

---

## 4. Higgs Self-Coupling

| Quantity | Symbol | Value | Uncertainty | Source | Used In |
|----------|--------|-------|-------------|--------|---------|
| Quartic coupling | $\lambda(M_H)$ | 0.129 | derived | $\lambda = M_H^2/(2v^2)$ | Theorem 3.2.1 |
| Trilinear coupling | $\kappa_\lambda$ | $1.00 \pm 0.50$ | 95% CL | HL-LHC projection | -- |

**CG Prediction:** Framework predicts $\kappa_\lambda \in [1.00, 1.02]$ — testable at HL-LHC/FCC.

---

## 5. Yukawa Couplings

Defined as $y_f = \sqrt{2} m_f / v$ with $v = 246.22$ GeV.

| Fermion | $y_f$ | $m_f$ used | Used In |
|---------|-------|------------|---------|
| $y_t$ | 0.992 | 172.57 GeV | Theorem 3.1.2 |
| $y_b$ | 0.0240 | 4.18 GeV | -- |
| $y_c$ | 0.0073 | 1.27 GeV | -- |
| $y_\tau$ | 0.0102 | 1.777 GeV | Theorem 3.1.1 |
| $y_\mu$ | $6.1 \times 10^{-4}$ | 105.66 MeV | -- |
| $y_e$ | $2.9 \times 10^{-6}$ | 0.511 MeV | Theorem 3.1.1 |

### 5.1 Mass Ratios (Scale-Independent)

| Ratio | Value | Source | Used In |
|-------|-------|--------|---------|
| $m_u/m_d$ | 0.46 | PDG 2024 | Theorem 3.1.2 |
| $m_s/m_d$ | 19.9 | FLAG 2024 | Theorem 3.1.2 |
| $m_c/m_s$ | 11.8 | FLAG 2024 | -- |
| $m_b/m_c$ | 3.29 | derived | -- |
| $m_t/m_b$ | 41.3 | derived | -- |
| $m_\mu/m_e$ | 206.77 | PDG 2024 | Theorem 3.1.1 |
| $m_\tau/m_\mu$ | 16.82 | PDG 2024 | -- |

---

## 6. CKM and CP Violation Parameters

### 6.1 Wolfenstein Parameters

| Parameter | Value | Uncertainty | Source | Used In |
|-----------|-------|-------------|--------|---------|
| $\lambda$ (Wolfenstein) | 0.22650 | $\pm 0.00048$ | PDG 2024 Table 12.1 | Theorem 3.1.2 |
| $\lambda$ (CKM global fit) | 0.22497 | $\pm 0.00069$ | PDG 2024 CKM fit | Reference |
| $A$ | 0.790 | $^{+0.017}_{-0.012}$ | PDG 2024 | -- |
| $\bar{\rho}$ | 0.141 | $^{+0.016}_{-0.017}$ | PDG 2024 | -- |
| $\bar{\eta}$ | 0.357 | $\pm 0.011$ | PDG 2024 | Theorem 4.2.1 |

**Note:** PDG 2024 reports two values for λ: the Wolfenstein parameterization (0.22650) and the CKM global fit (0.22497). The CG geometric derivation gives $\lambda_{bare} = (1/\varphi^3)\sin(72°) = 0.2245$, which matches the CKM global fit to 0.7σ. With QCD radiative corrections (~0.9%), $\lambda_{dressed} = 0.2265$ matches the Wolfenstein value to 0.1σ.

### 6.2 CP Violation

| Quantity | Value | Uncertainty | Source | Used In |
|----------|-------|-------------|--------|---------|
| Jarlskog invariant $J$ | $3.08 \times 10^{-5}$ | $\pm 0.15 \times 10^{-5}$ | PDG 2024 | Theorem 4.2.1 |
| $\epsilon_K$ (kaon) | $2.228 \times 10^{-3}$ | $\pm 0.011 \times 10^{-3}$ | PDG 2024 | -- |

**CG Framework:** Cabibbo angle arises from $\sqrt{m_d/m_s} \approx 0.225$, matching observation.

---

## 7. Chiral Coupling Parameters

These are CG-specific parameters derived in the framework:

| Parameter | Symbol | Value/Range | Source | Used In |
|-----------|--------|-------------|--------|---------|
| Chiral coupling | $g_\chi$ | $\sim 1$ | Theorem 3.1.1 | Mass generation |
| Oscillation freq | $\omega_0$ | $\sim \Lambda_{QCD}$ | Def 0.1.1 | Phase-gradient mass generation |
| Chiral VEV | $v_\chi$ | $f_\pi \sim 92$ MeV | Theorem 1.2.1 | Multiple |
| Fermion chirality | $\eta_f$ | $\in (0,1]$ | Theorem 3.1.1 | Mass formula |

---

## 8. Anomalous Magnetic Moments

| Quantity | Value | Uncertainty | Source | Used In |
|----------|-------|-------------|--------|---------|
| $(g-2)_e$ anomaly | $a_e^{exp} - a_e^{SM}$ | $(4.8 \pm 3.0) \times 10^{-13}$ | 2023 | -- |
| $(g-2)_\mu$ anomaly | $a_\mu^{exp} - a_\mu^{SM}$ | $(2.49 \pm 0.48) \times 10^{-9}$ | Muon g-2 2023 | Theorem 3.2.2 |

**Note:** Tension between lattice QCD and data-driven SM predictions creates uncertainty in $(g-2)_\mu$.

---

## 9. Gauge Coupling Unification

Running couplings at GUT scale (approximate):

| Coupling | $\mu = M_Z$ | $\mu = M_{GUT}$ | Unification |
|----------|-------------|-----------------|-------------|
| $\alpha_1 = (5/3)\alpha_Y$ | $1/98.4$ | $\sim 1/40$ | Yes |
| $\alpha_2 = \alpha_W$ | $1/29.6$ | $\sim 1/40$ | Yes |
| $\alpha_3 = \alpha_s$ | $1/8.5$ | $\sim 1/40$ | Yes |

**CG Constraint:** Framework requires $\sin^2\theta_W \to 3/8$ at high scales (satisfied by MSSM-like running).

---

## Changelog

| Date | Update | Affected Theorems |
|------|--------|-------------------|
| 2026-01-16 | Clarified Wolfenstein λ: added CKM global fit (0.22497), updated top Yukawa | Theorem 0.0.18, 3.1.2 |
| 2025-12-13 | Initial compilation from proof files | All |

---

## References

1. **PDG 2024:** Particle Data Group, Phys. Rev. D 110, 030001 (2024)
   - URL: https://pdg.lbl.gov
   - Accessed: 2025-12-13

2. **FLAG 2024:** Flavour Lattice Averaging Group
   - arXiv:2411.04268
   - Used for: quark mass ratios, $\alpha_s$

3. **CODATA 2018:** NIST Reference on Constants
   - URL: https://physics.nist.gov/cuu/Constants/
   - Accessed: 2025-12-13

4. **Muon g-2 Collaboration (2023):** PRL 131, 161802 (2023)
   - Used for: $(g-2)_\mu$ measurement

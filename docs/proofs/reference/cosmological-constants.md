# Cosmological and Gravitational Constants Reference

**Purpose:** Centralized repository of fundamental constants and cosmological parameters used in Chiral Geometrogenesis proofs.
**Convention:** SI units unless otherwise noted; conversions provided.

---

## 1. Fundamental Constants

### 1.1 Speed of Light and Planck's Constant

| Constant | Symbol | Value | Uncertainty | Source |
|----------|--------|-------|-------------|--------|
| Speed of light | $c$ | $2.99792458 \times 10^8$ m/s | exact | CODATA 2018 |
| Planck constant | $h$ | $6.62607015 \times 10^{-34}$ J·s | exact | CODATA 2018 |
| Reduced Planck | $\hbar$ | $1.054571817 \times 10^{-34}$ J·s | exact | derived |
| $\hbar c$ conversion | $\hbar c$ | 197.3 MeV·fm | -- | derived |

### 1.2 Gravitational Constant

| Constant | Symbol | Value | Uncertainty | Source | Used In |
|----------|--------|-------|-------------|--------|---------|
| Newton's constant | $G$ | $6.67430 \times 10^{-11}$ m$^3$/(kg·s$^2$) | $\pm 0.00015$ | CODATA 2018 | Theorems 5.2.1, 5.2.4, 5.3.1 |

---

## 2. Planck Scale

| Quantity | Symbol | Value (SI) | Value (GeV) | Derivation | Used In |
|----------|--------|------------|-------------|------------|---------|
| Planck mass | $M_P$ | $2.176434 \times 10^{-8}$ kg | $1.220890 \times 10^{19}$ GeV | $\sqrt{\hbar c/G}$ | Theorems 5.2.4, 5.2.5, 5.2.6 |
| Planck length | $\ell_P$ | $1.616255 \times 10^{-35}$ m | -- | $\sqrt{\hbar G/c^3}$ | Theorem 5.2.1 |
| Planck time | $t_P$ | $5.391247 \times 10^{-44}$ s | -- | $\sqrt{\hbar G/c^5}$ | -- |
| Planck energy | $E_P$ | $1.956 \times 10^9$ J | $1.22 \times 10^{19}$ GeV | $\sqrt{\hbar c^5/G}$ | -- |
| Planck density | $\rho_P$ | $5.155 \times 10^{96}$ kg/m$^3$ | -- | $c^5/(\hbar G^2)$ | Theorem 5.3.1 |

---

## 3. Chiral Framework Scales

| Quantity | Symbol | Value | Derivation | Source | Used In |
|----------|--------|-------|------------|--------|---------|
| Chiral decay constant | $f_\chi$ | $2.44 \times 10^{18}$ GeV | $M_P/\sqrt{8\pi}$ | Theorem 5.2.4 | Theorems 5.2.1, 5.2.4, 5.2.5 |
| Gravitational coupling | $\kappa$ | $8\pi G/c^4$ | Einstein eqns | Standard | Theorem 5.2.1 |
| Torsion coupling | $\kappa_T$ | $\pi G/c^4 = \kappa/8$ | Cartan eqn | Theorem 5.3.1 | Theorems 5.3.1, 5.3.2 |

**Numerical value:** $\kappa_T = 2.610 \times 10^{-44}$ m$^2$/kg

---

## 4. QCD Scales

| Quantity | Symbol | Value | Uncertainty | Source | Used In |
|----------|--------|-------|-------------|--------|---------|
| QCD scale | $\Lambda_{QCD}$ | 200-300 MeV | scheme dep. | Lattice QCD | Multiple |
| String tension | $\sqrt{\sigma}$ | 440 MeV | $\pm 30$ MeV | FLAG 2024 | Theorem 5.2.6 |
| Gluon condensate | $\langle\alpha_s G^2/\pi\rangle$ | 0.012 GeV$^4$ | $\pm 0.004$ | QCD sum rules | Equilibrium-Radius |
| Bag constant | $B^{1/4}$ | 145 MeV | $\pm 10$ MeV | MIT bag model | Theorem 2.1.1 |
| QCD critical temp | $T_c$ | 156.5 MeV | $\pm 1.5$ MeV | Budapest-Wuppertal 2014 | Theorems 2.1.2, 5.2.6 |

---

## 5. Cosmological Parameters

### 5.1 Hubble and Dark Energy

| Quantity | Symbol | Value | Uncertainty | Source | Used In |
|----------|--------|-------|-------------|--------|---------|
| Hubble constant | $H_0$ | 67.4 km/s/Mpc | $\pm 0.5$ | Planck 2018 | -- |
| Dark energy density | $\rho_\Lambda$ | $(2.4 \times 10^{-3}$ eV$)^4$ | -- | Planck 2018 | Theorem 5.1.2 |
| Cosmological const | $\Lambda$ | $1.1 \times 10^{-52}$ m$^{-2}$ | -- | Planck 2018 | -- |

### 5.2 Baryon Asymmetry

| Quantity | Symbol | Value | Uncertainty | Source | Used In |
|----------|--------|-------|-------------|--------|---------|
| Baryon-to-photon ratio | $\eta_B$ | $6.12 \times 10^{-10}$ | $\pm 0.04$ | Planck 2018 + BBN | Theorem 4.2.1, Corollary 4.2.3 |

### 5.3 Inflationary Parameters

| Quantity | Symbol | Value | Uncertainty | Source | Used In |
|----------|--------|-------|-------------|--------|---------|
| Scalar spectral index | $n_s$ | 0.9649 | $\pm 0.0042$ | Planck 2018 | Theorem 5.2.1 |
| Tensor-to-scalar ratio | $r$ | $< 0.036$ | 95% CL | BICEP/Keck 2021 | Theorem 5.2.1 |

---

## 6. Electroweak Scale

| Quantity | Symbol | Value | Source | Used In |
|----------|--------|-------|--------|---------|
| Higgs VEV | $v$ | 246.22 GeV | $(\sqrt{2}G_F)^{-1/2}$ | Theorem 3.2.1 |
| Fermi constant | $G_F$ | $1.1663788 \times 10^{-5}$ GeV$^{-2}$ | PDG 2024 | -- |
| EW phase transition temp | $T_{EW}$ | 160 GeV | estimate | Theorem 4.2.1 |

---

## 7. GUT and High-Energy Scales

| Quantity | Symbol | Value | Source | Used In |
|----------|--------|-------|--------|---------|
| GUT scale | $M_{GUT}$ | $\sim 10^{16}$ GeV | gauge unification | Theorem 2.3.1 |
| Right-handed neutrino scale | $M_R$ | $10^{9}-10^{14}$ GeV | seesaw fit | Corollary 3.1.3 |
| Electroweak precision cutoff | $\Lambda_{EW}$ | $> 3.5$ TeV | precision tests | Theorem 3.2.2 |

---

## 8. Unit Conversions

| Conversion | Value |
|------------|-------|
| 1 GeV$^{-1}$ | $1.973 \times 10^{-16}$ m |
| 1 fm | $5.068$ GeV$^{-1}$ |
| 1 kg | $5.61 \times 10^{26}$ GeV/$c^2$ |
| 1 eV | $1.602 \times 10^{-19}$ J |
| 1 GeV$^4$ | $2.085 \times 10^{37}$ J/m$^3$ |

---

## Changelog

| Date | Update | Affected Theorems |
|------|--------|-------------------|
| 2025-12-13 | Initial compilation from proof files | All |

---

## References

1. **CODATA 2018:** NIST Reference on Constants, Units, and Uncertainty
   - URL: https://physics.nist.gov/cuu/Constants/
   - Accessed: 2025-12-13

2. **Planck Collaboration (2018):** Planck 2018 results. VI. Cosmological parameters
   - arXiv:1807.06209
   - Used for: $H_0$, $\eta_B$, $n_s$, $r$

3. **FLAG Collaboration (2024):** FLAG Review 2024
   - arXiv:2411.04268
   - Used for: $\sqrt{\sigma}$, lattice QCD averages

4. **Budapest-Wuppertal Collaboration (2014):** PLB 730, 99 (2014)
   - Used for: $T_c$

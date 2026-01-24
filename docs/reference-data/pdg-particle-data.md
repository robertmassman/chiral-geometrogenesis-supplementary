# PDG Particle Data Reference

**Purpose:** Centralized repository of particle physics data from PDG used in Chiral Geometrogenesis proofs.
**Convention:** Natural units unless otherwise specified.
**Primary Source:** Particle Data Group 2024 (pdg.lbl.gov)

---

## 1. Quark Masses

### 1.1 Light Quarks (MS-bar, $\mu = 2$ GeV)

| Quark | Mass | Uncertainty | Source | Used In |
|-------|------|-------------|--------|---------|
| up ($m_u$) | 2.16 MeV | $^{+0.49}_{-0.26}$ MeV | PDG 2024 | Theorem 3.1.1, 3.0.2 |
| down ($m_d$) | 4.70 MeV | $\pm 0.07$ MeV | PDG 2024 | Theorem 3.1.1, 3.0.2 |
| strange ($m_s$) | 93.5 MeV | $\pm 0.8$ MeV | PDG 2024 (pdgLive) | Theorem 3.1.1 |

**Note:** Text references using approximate values (2.2, 4.7, 93.4 MeV) should cite these exact values with uncertainties.

### 1.2 Heavy Quarks

| Quark | Mass | Scheme | Uncertainty | Source | Used In |
|-------|------|--------|-------------|--------|---------|
| charm ($m_c$) | 1.27 GeV | MS-bar at $m_c$ | $\pm 0.02$ GeV | PDG 2024 | Theorem 3.1.2 |
| bottom ($m_b$) | 4.18 GeV | MS-bar at $m_b$ | $^{+0.04}_{-0.03}$ GeV | PDG 2024 | Theorem 3.1.2 |
| top ($m_t$) | 172.57 GeV | Pole mass | $\pm 0.29$ GeV | PDG 2024 | Theorem 3.1.2, 4.2.1 |

---

## 2. Lepton Masses

| Lepton | Mass | Uncertainty | Source | Used In |
|--------|------|-------------|--------|---------|
| electron ($m_e$) | 0.51099895 MeV | $\pm 0.00000015$ MeV | PDG 2024 | Theorem 3.1.1, 3.1.2 |
| muon ($m_\mu$) | 105.6583755 MeV | $\pm 0.0000023$ MeV | PDG 2024 | Theorem 3.1.1 |
| tau ($m_\tau$) | 1776.93 MeV | $\pm 0.09$ MeV | PDG 2024 | Theorem 3.1.1 |

---

## 3. Meson Masses and Properties

### 3.1 Pion

| Property | Value | Uncertainty | Source | Used In |
|----------|-------|-------------|--------|---------|
| $m_{\pi^\pm}$ | 139.57039 MeV | $\pm 0.00018$ MeV | PDG 2024 | Theorems 3.0.1, 3.0.2, 3.1.1, Def 0.1.1 |
| $m_{\pi^0}$ | 134.9768 MeV | $\pm 0.0005$ MeV | PDG 2024 | Theorem 1.2.2 |
| $f_\pi$ (Peskin-Schroeder) | 92.1 MeV | $\pm 0.6$ MeV | PDG 2024 (130.2/$\sqrt{2}$) | Theorems 3.0.1, 3.1.1, 5.2.4 |
| $f_\pi$ (PDG standard) | 130.2 MeV | $\pm 0.8$ MeV | PDG 2024 | Reference only |
| $\Gamma(\pi^0 \to \gamma\gamma)$ | 7.72 eV | $\pm 0.12$ eV | PDG 2024 | Theorem 1.2.2 |

**Convention Note:** This framework uses the Peskin-Schroeder convention $f_\pi = 92.1$ MeV. The PDG convention ($f_{\pi^\pm} = 130.2$ MeV) differs by $\sqrt{2}$.

### 3.2 Chiral Condensate (QCD Vacuum)

| Property | Value | Uncertainty | Source | Used In |
|----------|-------|-------------|--------|---------|
| $\langle\bar{q}q\rangle^{1/3}$ (MS-bar, 2 GeV) | −272 MeV | ±15 MeV | FLAG 2021 average | Theorems 2.1.2, 3.0.1 |
| $\Sigma^{1/3}$ (chiral limit) | −242 MeV | $^{+19}_{-18}$ MeV | JLQCD 2010 | Theorem 2.1.2 |

**Notation:**
- $\langle\bar{q}q\rangle$ = quark condensate (vacuum expectation value of $\bar{q}q$)
- $\Sigma$ = chiral condensate in the chiral limit ($m_q \to 0$)
- Both are negative, indicating spontaneous chiral symmetry breaking

**Physical interpretation:** The quark condensate characterizes the non-perturbative QCD vacuum. Its suppression inside hadrons (Iritani et al. 2015) provides the mechanism for the MIT bag constant.

**Note:** Values quoted with cube root, i.e., $(−\langle\bar{q}q\rangle)^{1/3}$. The full condensate is:
$$\langle\bar{q}q\rangle \approx -(272 \text{ MeV})^3 \approx -2.0 \times 10^7 \text{ MeV}^3$$

### 3.3 Other Mesons

| Meson | Mass | Source | Used In |
|-------|------|--------|---------|
| $\eta'$ | 957.78 MeV | PDG 2024 | Theorem 2.2.4 |
| $K^\pm$ | 493.677 MeV | PDG 2024 | -- |

---

## 4. Gauge Boson Masses

| Boson | Mass | Uncertainty | Source | Used In |
|-------|------|-------------|--------|---------|
| W ($m_W$) | 80.3692 GeV | $\pm 0.0133$ GeV | PDG 2024 world avg | Theorem 3.2.1, 3.2.2 |
| Z ($m_Z$) | 91.1876 GeV | $\pm 0.0021$ GeV | PDG 2024 | Theorem 3.2.1, 5.2.6 |

**Note on W mass:** The 2022 CDF anomaly (80.4335 GeV) has been effectively resolved by LHC measurements. Current world average is consistent with SM prediction.

---

## 5. Higgs Boson

| Property | Value | Uncertainty | Source | Used In |
|----------|-------|-------------|--------|---------|
| Mass ($m_H$) | 125.11 GeV | $\pm 0.11$ GeV | PDG 2024 | Theorem 3.2.1 |
| Width ($\Gamma_H$) | 4.1 MeV | $\pm 0.5$ MeV | PDG 2024 | Theorem 3.2.1 |
| VEV ($v$) | 246.22 GeV | derived | $(\sqrt{2}G_F)^{-1/2}$ | Theorems 3.2.1, 4.2.1 |

---

## 6. Neutrino Parameters

| Parameter | Value | Source | Used In |
|-----------|-------|--------|---------|
| $\Delta m^2_{atm}$ | $2.5 \times 10^{-3}$ eV$^2$ | PDG 2024 | Theorem 3.1.2, Corollary 3.1.3 |
| $\Delta m^2_{sol}$ | $7.5 \times 10^{-5}$ eV$^2$ | PDG 2024 | Theorem 3.1.2, Corollary 3.1.3 |
| $\sum m_\nu$ | $< 0.12$ eV | Planck 2018 + BAO | Corollary 3.1.3 |
| $\sum m_\nu$ | $< 0.072$ eV (95% CL, $\Sigma m_\nu>0$ prior) | DESI 2024 (arXiv:2404.03002) | Corollary 3.1.3 |

---

## 7. CKM Matrix Parameters

| Parameter | Value | Uncertainty | Source | Used In |
|-----------|-------|-------------|--------|---------|
| $\lambda$ (Wolfenstein) | 0.22650 | $\pm 0.00048$ | PDG 2024 | Theorem 3.1.2 |
| $\sin\theta_C$ | 0.225 | derived | $\sqrt{m_d/m_s}$ check | Theorem 3.1.2 |
| Jarlskog $J$ | $3.08 \times 10^{-5}$ | $\pm 0.15 \times 10^{-5}$ | PDG 2024 | Theorem 4.2.1 |

---

## 8. Decay Rates and Lifetimes

| Process | Value | Uncertainty | Source | Used In |
|---------|-------|-------------|--------|---------|
| $\Gamma(\pi^0 \to \gamma\gamma)$ | 7.72 eV | $\pm 0.12$ eV | PDG 2024 | Theorem 1.2.2 |
| Proton lifetime | $> 2.4 \times 10^{34}$ yr | 90% CL | Super-K | Theorem 4.1.1 |

---

## 9. Baryon Properties

### 9.1 Baryon Masses

| Baryon | Mass | Source | Used In |
|--------|------|--------|---------|
| Proton ($m_p$) | 938.272 MeV | PDG 2024 | Theorems 2.1.1, 5.2.4 |
| Neutron ($m_n$) | 939.565 MeV | PDG 2024 | -- |
| Delta ($m_\Delta$) | 1232 MeV | PDG 2024 | Theorem 2.1.1 |

### 9.2 Proton Charge Radius

| Quantity | Value | Uncertainty | Source | Used In |
|----------|-------|-------------|--------|---------|
| Proton charge radius ($r_p$) | 0.84075 fm | $\pm 0.00064$ fm | CODATA 2022 | Theorem 2.1.1 |

**Note:** The CODATA 2022 value resolves the "proton radius puzzle" that arose from the 5.6σ discrepancy between the 2014 value (0.8751 fm from electronic measurements) and muonic hydrogen results (0.84 fm). The 2022 value agrees with muonic hydrogen spectroscopy.

**Historical values:**
- CODATA 2014: 0.8751(61) fm (electronic only)
- CODATA 2018: 0.8414(19) fm
- CODATA 2022: 0.84075(64) fm (final resolution)

---

## Changelog

| Date | Update | Affected Theorems |
|------|--------|-------------------|
| 2026-01-16 | Updated top mass to 172.57 ± 0.29 GeV (PDG 2024 world average) | Theorem 0.0.18, 3.1.2 |
| 2025-12-13 | Added chiral condensate §3.2: $\langle\bar{q}q\rangle^{1/3} = -272$ MeV (FLAG) | Theorem 2.1.2 |
| 2025-12-13 | Added proton charge radius (CODATA 2022: 0.84075 fm) and Delta mass | Theorem 2.1.1 |
| 2025-12-13 | Initial compilation from proof files | All |

---

## References

1. **PDG 2024:** Particle Data Group, Phys. Rev. D 110, 030001 (2024)
   - URL: https://pdg.lbl.gov
   - Accessed: 2025-12-13

2. **PDG Live (quark masses):** https://pdglive.lbl.gov/DataBlock.action?node=Q123SM
   - Accessed: 2025-12-13

3. **FLAG 2024:** Flavour Lattice Averaging Group, arXiv:2411.04268
   - URL: https://flag.unibe.ch/
   - Used for: Chiral condensate lattice average

4. **JLQCD/TWQCD 2010:** Phys. Rev. Lett. 104, 122002 (2010), arXiv:0911.5555
   - Used for: Chiral condensate in chiral limit

5. **Iritani et al. (2015):** Phys. Rev. D 91, 094501, arXiv:1502.04845
   - Used for: Chiral condensate suppression in flux tubes

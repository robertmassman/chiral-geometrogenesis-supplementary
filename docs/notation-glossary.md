# Unified Notation Glossary for Chiral Geometrogenesis Papers

This document provides consistent notation across all papers in the series.

---

## Core Geometric Objects

| Symbol | LaTeX | Definition | First Use |
|--------|-------|------------|-----------|
| $\mathcal{S}$ | `\mathcal{S}` | Stella octangula (8-vertex compound) | Paper 1 |
| $\partial\mathcal{S}$ | `\partial\mathcal{S}` | Boundary of stella octangula | Paper 1 |
| $T_1, T_2$ | `T_1, T_2` | The two interpenetrating tetrahedra | Paper 1 |
| $\mathcal{P}$ | `\mathcal{P}` | Generic polyhedral complex | Paper 1 |

---

## Lie Groups and Algebras

| Symbol | LaTeX | Definition | Notes |
|--------|-------|------------|-------|
| $\mathrm{SU}(N)$ | `\mathrm{SU}(N)` | Special unitary group | Standard |
| $\mathfrak{su}(N)$ | `\mathfrak{su}(N)` | Lie algebra of SU(N) | Standard |
| $\mathcal{W}$ | `\mathcal{W}` | Weyl group | $\mathcal{W}(\mathrm{SU}(3)) \cong S_3$ |
| $T_3, T_8$ | `T_3, T_8` | Cartan generators of SU(3) | Gell-Mann basis |
| $\lambda_a$ | `\lambda_a` | Gell-Mann matrices ($a = 1, \ldots, 8$) | Standard |

---

## Representations

| Symbol | LaTeX | Dimension | Description |
|--------|-------|-----------|-------------|
| $\mathbf{3}$ | `\mathbf{3}` | 3 | Fundamental representation |
| $\bar{\mathbf{3}}$ | `\bar{\mathbf{3}}` | 3 | Antifundamental representation |
| $\mathbf{8}$ | `\mathbf{8}` | 8 | Adjoint representation |
| $\mathbf{1}$ | `\mathbf{1}` | 1 | Singlet representation |

---

## Weights and Roots

| Symbol | LaTeX | Definition |
|--------|-------|------------|
| $\bm{\mu}$ | `\bm{\mu}` | Weight vector |
| $\bm{\alpha}$ | `\bm{\alpha}` | Root vector |
| $\bm{\mu}_1, \bm{\mu}_2$ | `\bm{\mu}_1, \bm{\mu}_2` | Fundamental weights |
| $\bm{\alpha}_1, \bm{\alpha}_2$ | `\bm{\alpha}_1, \bm{\alpha}_2` | Simple roots |

---

## Color Charges

| Symbol | LaTeX | Position (normalized) | Weight |
|--------|-------|-----------------------|--------|
| $R$ | `R` | $(1, 1, 1)/\sqrt{3}$ | Red quark |
| $G$ | `G` | $(1, -1, -1)/\sqrt{3}$ | Green quark |
| $B$ | `B$ | $(-1, 1, -1)/\sqrt{3}$ | Blue quark |
| $\bar{R}$ | `\bar{R}` | $(-1, -1, -1)/\sqrt{3}$ | Anti-red |
| $\bar{G}$ | `\bar{G}` | $(-1, 1, 1)/\sqrt{3}$ | Anti-green |
| $\bar{B}$ | `\bar{B}` | $(1, -1, 1)/\sqrt{3}$ | Anti-blue |
| $W_+, W_-$ | `W_+, W_-` | Apex vertices | Singlet direction |

---

## Chiral Fields (Papers 2-4)

| Symbol | LaTeX | Definition | Dimension |
|--------|-------|------------|-----------|
| $\chi$ | `\chi` | Chiral scalar field (complex) | [Mass] |
| $\chi_c$ | `\chi_c` | Color component ($c \in \{R, G, B\}$) | [Mass] |
| $v_\chi$ | `v_\chi` | Chiral VEV | $\sim 92$ MeV |
| $a_c(x)$ | `a_c(x)` | Amplitude modulation | [Mass] |
| $\phi_c$ | `\phi_c` | Phase for color $c$ | Dimensionless |

**Phase convention:**
- $\phi_R = 0$
- $\phi_G = 2\pi/3$
- $\phi_B = 4\pi/3$

---

## Pressure Functions

| Symbol | LaTeX | Definition |
|--------|-------|------------|
| $P_c(x)$ | `P_c(x)` | Pressure function for color $c$ |
| $\epsilon$ | `\epsilon` | Regularization parameter |
| $x_c$ | `x_c` | Vertex position for color $c$ |

**Formula:**
$$P_c(x) = \frac{1}{|x - x_c|^2 + \epsilon^2}$$

---

## Time and Evolution

| Symbol | LaTeX | Definition | Notes |
|--------|-------|------------|-------|
| $\lambda$ | `\lambda` | Internal evolution parameter | Dimensionless |
| $t$ | `t` | Emergent physical time | [Time] |
| $\omega_0$ | `\omega_0` | Fundamental oscillation frequency | $\sim 140$ MeV |
| $\omega[\chi]$ | `\omega[\chi]` | Functional frequency | $t = \int d\lambda/\omega$ |

---

## Mass Generation (Paper 3)

| Symbol | LaTeX | Definition | Notes |
|--------|-------|------------|-------|
| $m_f$ | `m_f` | Fermion mass | Flavor $f$ |
| $g_\chi$ | `g_\chi` | Chiral coupling constant | Dimensionless |
| $\Lambda$ | `\Lambda` | UV cutoff scale | $\sim 1$ GeV (QCD) |
| $\eta_f$ | `\eta_f` | Flavor-dependent geometric factor | Dimensionless |

**Mass formula:**
$$m_f = \frac{g_\chi \omega_0}{\Lambda} v_\chi \eta_f$$

---

## Lagrangian Terms

| Symbol | LaTeX | Description |
|--------|-------|-------------|
| $\mathcal{L}_{CG}$ | `\mathcal{L}_{CG}` | Complete Chiral Geometrogenesis Lagrangian |
| $\mathcal{L}_{chiral}$ | `\mathcal{L}_{chiral}` | Chiral kinetic + potential |
| $\mathcal{L}_{drag}$ | `\mathcal{L}_{drag}` | Phase-gradient mass generation (mass generation) |
| $\mathcal{L}_{soliton}$ | `\mathcal{L}_{soliton}` | Skyrme term (soliton stabilization) |
| $\mathcal{L}_{gauge}$ | `\mathcal{L}_{gauge}` | Gauge field kinetic term |

---

## Gravity (Paper 4)

| Symbol | LaTeX | Definition |
|--------|-------|------------|
| $g_{\mu\nu}$ | `g_{\mu\nu}` | Emergent metric tensor |
| $T_{\mu\nu}$ | `T_{\mu\nu}` | Stress-energy tensor |
| $\mathcal{T}^\lambda_{\mu\nu}$ | `\mathcal{T}^\lambda_{\mu\nu}` | Torsion tensor |
| $K^\lambda_{\mu\nu}$ | `K^\lambda_{\mu\nu}` | Contortion tensor |
| $J_5^\mu$ | `J_5^\mu` | Axial (chiral) current |
| $\kappa_T$ | `\kappa_T` | Torsion-current coupling |

**Torsion formula:**
$$\mathcal{T}^\lambda_{\mu\nu} = \kappa_T \epsilon^\lambda_{\mu\nu\rho} J_5^\rho$$

---

## Symmetry Groups

| Symbol | Order | Description |
|--------|-------|-------------|
| $S_4$ | 24 | Symmetric group on 4 elements |
| $A_4$ | 12 | Alternating group on 4 elements |
| $T_d$ | 24 | Tetrahedral point group |
| $O_h$ | 48 | Octahedral point group (stella octangula symmetry) |
| $S_4 \times \mathbb{Z}_2$ | 48 | Full stella octangula symmetry |

---

## CKM Parameters (Paper 2)

| Symbol | LaTeX | Geometric Derivation | PDG Value |
|--------|-------|---------------------|-----------|
| $\lambda$ | `\lambda` | $(1/\phi^3) \sin(72°)$ | $0.22650 \pm 0.00048$ |
| $A$ | `A` | $\sin(36°)/\sin(45°)$ | $0.826 \pm 0.015$ |
| $\bar{\rho}$ | `\bar{\rho}` | — | $0.1581 \pm 0.0092$ |
| $\bar{\eta}$ | `\bar{\eta}` | — | $0.3548 \pm 0.0072$ |

Where $\phi = (1 + \sqrt{5})/2 \approx 1.618$ is the golden ratio.

---

## Physical Constants

| Symbol | Value | Notes |
|--------|-------|-------|
| $f_\pi$ | 92.4 MeV | Pion decay constant |
| $\Lambda_{QCD}$ | $\sim 200$ MeV | QCD scale |
| $M_P$ | $2.44 \times 10^{18}$ GeV | Reduced Planck mass |
| $G$ | $6.674 \times 10^{-11}$ m³/kg·s² | Newton's constant |

---

## Verification Markers

Used in proof documents (not in papers):

| Marker | Meaning |
|--------|---------|
| ✅ ESTABLISHED | Proven or standard physics |
| 🔶 NOVEL | New physics requiring careful derivation |
| 🔸 PARTIAL | Some aspects proven |
| 🔮 CONJECTURE | Hypothesized, needs development |

---

## LaTeX Macros (for papers)

```latex
% Groups
\newcommand{\SU}[1]{\mathrm{SU}(#1)}
\newcommand{\SO}[1]{\mathrm{SO}(#1)}

% Representations
\newcommand{\fund}{\mathbf{3}}
\newcommand{\afund}{\bar{\mathbf{3}}}
\newcommand{\adj}{\mathbf{8}}

% Geometry
\newcommand{\stella}{\mathcal{S}}
\newcommand{\boundary}{\partial\mathcal{S}}
\newcommand{\Td}{T_d}
\newcommand{\Weyl}{\mathcal{W}}

% Vectors
\newcommand{\weight}{\bm{\mu}}
\newcommand{\root}{\bm{\alpha}}

% Fields
\newcommand{\chiral}{\chi}
\newcommand{\vev}{v_\chi}

% Spaces
\newcommand{\R}{\mathbb{R}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\C}{\mathbb{C}}
```

---

## Version History

| Date | Change |
|------|--------|
| 2025-12-28 | Initial creation |

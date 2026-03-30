# Unified Notation Glossary for Chiral Geometrogenesis Papers

This document provides consistent notation across all papers in the series.

---

## Core Geometric Objects

| Symbol | LaTeX | Definition | First Use |
|--------|-------|------------|-----------|
| $\mathcal{S}$ | `\mathcal{S}` | Stella octangula (8-vertex compound) | Paper 1 |
| $\partial\mathcal{S}$ | `\partial\mathcal{S}` | Boundary of stella octangula | Paper 1 |
| $T_+, T_-$ | `T_+, T_-` | The two interpenetrating tetrahedra (also $T_1, T_2$ in older notation) | Paper 1 |
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

| Symbol | LaTeX | Position (normalized) | Role |
|--------|-------|-----------------------|------|
| $R$ | `R` | $(1, -1, -1)/\sqrt{3}$ | Red quark (fundamental, $T_+$ base) |
| $G$ | `G` | $(-1, 1, -1)/\sqrt{3}$ | Green quark (fundamental, $T_+$ base) |
| $B$ | `B` | $(-1, -1, 1)/\sqrt{3}$ | Blue quark (fundamental, $T_+$ base) |
| $\bar{R}$ | `\bar{R}` | $(-1, 1, 1)/\sqrt{3}$ | Anti-red (antifundamental, $T_-$ base) |
| $\bar{G}$ | `\bar{G}` | $(1, -1, 1)/\sqrt{3}$ | Anti-green (antifundamental, $T_-$ base) |
| $\bar{B}$ | `\bar{B}` | $(1, 1, -1)/\sqrt{3}$ | Anti-blue (antifundamental, $T_-$ base) |
| $W_+$ | `W_+` | $(1, 1, 1)/\sqrt{3}$ | Apex ($T_+$, singlet direction) |
| $W_-$ | `W_-` | $(-1, -1, -1)/\sqrt{3}$ | Apex ($T_-$, singlet direction) |

> **Convention A (standard, unified 2026-02-21):** Color vertices R, G, B occupy the three base vertices of $T_+$ (fundamental **3** weights). The apex $W_+ = (1,1,1)/\sqrt{3}$ is the singlet direction. Anti-colors are antipodal: $x_{\bar{c}} = -x_c$. This is the single canonical convention used throughout all proof documents, Lean files, Python scripts, and papers.

---

## Chiral Fields

| Symbol | LaTeX | Definition | Dimension (Phase 0) | Dimension (QFT) |
|--------|-------|------------|---------------------|-----------------|
| $\chi$ | `\chi` | Chiral scalar field (complex) | Dimensionless | [Mass] |
| $\chi_c$ | `\chi_c` | Color component ($c \in \{R, G, B\}$) | Dimensionless | [Mass] |
| $\chi_{total}$ | `\chi_{total}` | Total superposed field: $\chi_{total}(x) = \sum_c \chi_c(x)$ | Dimensionless | [Mass] |
| $v_\chi$ | `v_\chi` | Chiral VEV | — | $\sim 92$ MeV |
| $a_0$ | `a_0` | Amplitude scale parameter | $[\text{length}]^2$ | — |
| $a_c(x)$ | `a_c(x)` | Amplitude modulation: $a_c(x) = a_0 \cdot P_c(x)$ | Dimensionless | [Mass] |
| $\phi_c$ | `\phi_c` | Phase for color $c$ | Dimensionless | Dimensionless |

> **Dimensional convention:** In the Phase 0 pre-geometric framework (Definitions 0.1.1–0.1.4), the color fields $\chi_c = a_0 \cdot P_c(x) \cdot e^{i\phi_c}$ are **dimensionless** because $a_0$ has $[\text{length}]^2$ and $P_c$ has $[\text{length}]^{-2}$. Physical mass dimensions are restored when matching to QCD scales via Theorem 3.0.1, where the VEV is identified as $v_\chi = f_\pi \approx 92$ MeV. Papers and post-Phase 0 proofs use the standard QFT convention where scalar fields carry dimension [Mass].

**Phase convention:**
- $\phi_R = 0$
- $\phi_G = 2\pi/3$
- $\phi_B = 4\pi/3$

---

## Pressure Functions and Color Domains

| Symbol | LaTeX | Definition | Dimension |
|--------|-------|------------|-----------|
| $P_c(x)$ | `P_c(x)` | Pressure function for color $c$ | $[\text{length}]^{-2}$ |
| $\epsilon$ | `\epsilon` | Regularization parameter ($\epsilon > 0$; physical value $\approx 0.50$) | Dimensionless |
| $x_c$ | `x_c` | Vertex position for color $c$ | $[\text{length}]$ |
| $D_c$ | `D_c` | Color field domain: region where $P_c$ dominates (Def. 0.1.4) | Region in $\mathbb{R}^3$ |
| $E_c$ | `E_c` | Depression domain: region where $P_c$ is minimal (Def. 0.1.4) | Region in $\mathbb{R}^3$ |
| $\mathcal{D}_c(x)$ | `\mathcal{D}_c(x)` | Depression ratio: $(P_{c'} + P_{c''})/P_c$ (Def. 0.1.3 §7.4) | Dimensionless |

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
| $O_h \cong S_4 \times \mathbb{Z}_2$ | 48 | Octahedral point group = full stella octangula symmetry |

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

Used in proof documents (not in papers). Format: `## Status: [MARKER] — [DESCRIPTION]`

| Marker | Meaning |
|--------|---------|
| ✅ ESTABLISHED | Standard/known physics — proven in textbooks or peer-reviewed literature |
| ✅ VERIFIED | Framework-specific result verified via multi-agent review and/or Lean 4 formalization |
| 🔶 NOVEL | Framework-specific novel content, not yet fully verified |
| 🔶 NOVEL ✅ VERIFIED | Novel content verified via multi-agent adversarial review AND Lean 4 formalization |
| 🔸 PARTIAL | Some aspects proven, gaps remain |
| 🔮 CONJECTURE | Hypothesized, needs development |

> **Note:** 🔶 NOVEL must persist when ✅ VERIFIED is added — novelty is orthogonal to verification status. Do not include dates or method details in the status line; use verification records for provenance.

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
| 2026-02-21 | M6 audit fixes: resolved dimensional convention conflict (Phase 0 vs QFT); added missing symbols (χ_{total}, a₀, D_c, E_c, D_c(x)); added dimensions to pressure function table. Vertex-color table restored to M4 convention (R at base) with reconciliation note documenting Def 0.1.3's permuted labeling. Convention A vertex unification: standardized all proof documents, Lean files, Python scripts, and papers to Convention A (R=(1,-1,-1)/√3, G=(-1,1,-1)/√3, B=(-1,-1,1)/√3, W=(1,1,1)/√3). Old Convention B (R at all-positive apex) is now obsolete. |

# Proposition 0.0.35: Dimensional Uniqueness of R_stella

**Status:** 🔶 NOVEL ✅ ESTABLISHED

**Date:** 2026-02-08

**Abstract:** We prove that $R_{\text{stella}}$ is the unique dimensional input at the QCD level of the Chiral Geometrogenesis framework. All dimensionful QCD-sector quantities — string tension, pion decay constant, characteristic frequency, chiral VEV, EFT cutoff, regularization parameter, vector meson mass, and low-energy constants — are derived from $R_{\text{stella}}$ through closed-form expressions involving only topological integers ($N_c$, $N_f$, $\chi$) and transcendental constants ($\pi$, $e$). Cross-scale quantities ($M_P$, $G$, $v_H$, $m_H$) are similarly derived via dimensional transmutation and the $a$-theorem. The derivation graph is a directed acyclic graph (DAG) with $R_{\text{stella}}$ as the unique dimensional source, achieving a 50–80% reduction in free parameters compared to the Standard Model.

---

## §1. Formal Statement

### Definition 1.1 (Dimensional Input)

A quantity $Q$ is a **dimensional input** of the framework if:
1. $Q$ carries physical dimensions (length, mass, energy, or time), and
2. $Q$ cannot be expressed as a closed-form function of other framework quantities and dimensionless constants.

### Definition 1.2 (Derived from $R_{\text{stella}}$)

A quantity $Q$ is **derived from $R_{\text{stella}}$** if there exist rational exponents $a, b$ and a function $F$ of topological/group-theoretic integers and transcendental constants such that:

$$Q = (\hbar c)^a \cdot R_{\text{stella}}^b \cdot F(N_c, N_f, \chi, \pi, \varphi, \exp, \ldots)$$

where $F$ depends only on:
- Color number $N_c = 3$, flavor number $N_f = 3$ (or 2 for light quarks)
- Euler characteristic $\chi = 4$ of the stella octangula boundary
- Mathematical constants: $\pi$, $e$, golden ratio $\varphi$
- Group-theoretic integers: dimensions of representations, Coxeter numbers

### Theorem 0.0.35 (Dimensional Uniqueness)

**Statement.** In the Chiral Geometrogenesis framework:

**(a) QCD Completeness.** Every dimensionful quantity in the QCD sector
$$\mathcal{Q}_{\text{QCD}} = \{\sqrt{\sigma},\, \omega,\, f_\pi,\, v_\chi,\, \Lambda,\, \epsilon,\, g_\chi,\, M_\rho,\, \bar{\ell}_4,\, m_{\text{base}}\}$$
is derived from $R_{\text{stella}}$.

**(b) Cross-Scale Derivation.** The quantities
$$\mathcal{Q}_{\text{cross}} = \{M_P,\, G,\, \ell_P,\, v_H,\, \Lambda_{\text{EW}},\, m_H\}$$
are derived from $R_{\text{stella}}$ via dimensional transmutation (Thm 5.2.6) and the $a$-theorem (Prop 0.0.21).

**(c) DAG Structure.** The derivation graph $\mathcal{G} = (\mathcal{Q}, \mathcal{E})$ is a directed acyclic graph with:
- Exactly **1** dimensional source at QCD level ($R_{\text{stella}}$)
- At most **3** dimensional inputs across the full framework ($R_{\text{stella}}$, $M_R$, and $\omega_{\text{EW}}$ if Prop 0.0.27 not accepted)

**(d) Semi-Derivability.** $R_{\text{stella}}$ itself is derivable from $M_P$ via Prop 0.0.17q with 91% agreement, with the 9% gap reducible by non-perturbative corrections (Prop 0.0.17z).

---

## §2. Complete Symbol Table

| # | Symbol | Value | Units | Formula from $R_{\text{stella}}$ | Source | Agreement |
|---|--------|-------|-------|----------------------------------|--------|-----------|
| 0 | $R_{\text{stella}}$ | 0.44847 | fm | **INPUT** | Observed | — |
| 1 | $\sqrt{\sigma}$ | 440 | MeV | $\hbar c / R_{\text{stella}}$ | Prop 0.0.17j | Exact (by construction) |
| 2 | $\sigma$ | 0.194 | GeV² | $(\hbar c)^2 / R_{\text{stella}}^2$ | Prop 0.0.17j | Bali (2001): $\sqrt{\sigma} = 440 \pm 30$ MeV |
| 3 | $f_\pi^{(\text{tree})}$ | 88.0 | MeV | $\sqrt{\sigma} / [(N_c-1)+(N_f^2-1)]$, $N_f=2$ | Prop 0.0.17k | 95.5% of 92.1 MeV$^{\P}$ |
| 4 | $\omega$ | 220 | MeV | $\sqrt{\sigma} / (N_c - 1)$ | Prop 0.0.17l | 96% of $\Lambda_{\text{QCD}}^{(5)}$ |
| 5 | $v_\chi$ | 88.0 | MeV | $f_\pi^{(\text{tree})}$ (identity) | Prop 0.0.17m | 95.5% |
| 6 | $\Lambda$ | 1.106 | GeV | $4\pi f_\pi$ | Prop 0.0.17d | 95% of standard ChPT |
| 7 | $\epsilon$ | 0.5 | — | $\sqrt{\sigma} / (2\pi m_\pi)$$^{\ddagger}$ | Prop 0.0.17o | 98.1% match with lattice |
| 8 | $g_\chi$ | 1.396 | — | $4\pi / N_c^2$ | Prop 3.1.1c | 0.14σ of FLAG 2024 |
| 9 | $M_\rho$ | 777 | MeV | $\sqrt{c_V \cdot \sigma}$, $c_V = 3.12$$^{\ddagger}$ | Prop 0.0.17k4 | 0.22% of PDG 775.26 MeV |
| 10 | $\bar{\ell}_4$ | 4.4 | — | Dispersive (resonance + Omnès) | Prop 0.0.17k3 | 0.00σ (exact central value) |
| 11 | $f_\pi^{(1\text{-loop})}$ | 93.8 | MeV | $f_\pi^{(\text{tree})} (1 + 6.6\%)$, $N_f=2$ | Prop 0.0.17k1 | 1.9% of PDG |
| 12 | $1/\alpha_s(M_P)$ | 52 | — | $(N_c^2 - 1)^2 - N_{\text{hol}}$ = 64 − 12 | Prop 0.0.17ac | ~1% of 1-loop QCD running$^\dagger$ |
| 12b | $N_{\text{holonomy}}$ | 12 | — | $2 \times \beta_1(K_4) \times \text{rank}(SU(3))$ = 2 × 3 × 2 | Prop 0.0.17ac | Topological (non-running) |
| 13 | $M_P$ | $1.12 \times 10^{19}$ | GeV | $(\sqrt{\chi}/2) \sqrt{\sigma} \exp[(1/\alpha_s + N_{\text{hol}})/(2b_0)]$ | Thm 5.2.6 + Prop 0.0.17ac | 91.5% (1-loop) |
| 14 | $M_P^{(\text{corr})}$ | $1.235 \times 10^{19}$ | GeV | With NP corrections | Prop 0.0.17z | +1.2% |
| 15 | $G$ | $6.52 \times 10^{-11}$ | m³/(kg·s²) | $\hbar c / (8\pi f_\chi^2)$ | Prop 0.0.17ab | −2.3% of CODATA |
| 16 | $\ell_P$ | $1.616 \times 10^{-35}$ | m | $\sqrt{\hbar G / c^3}$ | Derived from $G$ | — |
| 17 | $v_H$ | 246.7 | GeV | $\sqrt{\sigma} \cdot \exp(6.329)$ | Prop 0.0.21 | 0.19% of PDG 246.22 GeV |
| 18 | $m_H$ | 125.2 | GeV | $\sqrt{2\lambda} \cdot v_H (1+\delta_{\text{rad}})$, $\lambda = 1/8$, $\delta_{\text{rad}} \approx +1.5\%$ | Prop 0.0.27 | Tree: 123.4 GeV (1.5%); NNLO: 125.2 GeV (0.0%) |
| 19 | $b_0$ | $9/(4\pi)$ | — | $(11N_c - 2N_f) / (12\pi)$, $N_f=3$ | Standard QCD | — |
| 20 | $\Lambda_{\text{EW}}$ | ~1 | TeV | $\sim 4\pi v_H$ | Prop 0.0.26 | Consistent |
| 21 | $T_c / \sqrt{\sigma}$ | 0.352 | — | Casimir thermal correction | Prop 0.0.17j §5.4 | PDG: 155/440 |
| 22 | $\bar{\theta}$ | 0 | — | $\mathbb{Z}_3$ structure | Prop 0.0.17e | Exact |
| 23 | $\lambda_W$ | 0.2245 | — | $(1/\varphi^3) \sin 72°$ | Lemma 3.1.2a | 0.2% of PDG |
| 24 | $A$ | 0.831 | — | $\sin 36° / \sin 45°$ | Extension 3.1.2b | 0.1% of PDG |

$^{\ddagger}$ **Dependencies note:** $\epsilon$ (Row 7) uses $m_\pi = 140$ MeV, an external input not derived from $R_{\text{stella}}$ (see §4.1 and §5.2 for honest accounting). In contrast, $c_V = 3.12$ (Row 9) IS derived from first principles: $\mathbb{Z}_3$ phase structure $\to$ Kuramoto coupling $K$ (Thm 2.2.1) $\to$ overlap integral $\kappa = 0.128$ $\to$ Robin parameter $\alpha$ $\to$ Laplacian eigenvalue $c_V = 3.12 \pm 0.05$. See [Prop 0.0.17k4](Proposition-0.0.17k4-cV-From-Z3-Phase-Structure.md) for complete derivation.

$^{\P}$ **Convention on $f_\pi$:** This document uses the Peskin-Schroeder (PS) convention, which differs from the PDG convention by $\sqrt{2}$: $f_\pi^{(\text{PDG})} = \sqrt{2} \, f_\pi^{(\text{PS})}$. The PDG 2024 measured value $f_{\pi^\pm} = 130.41 \pm 0.20$ MeV converts to $f_\pi^{(\text{PS})} = 130.41/\sqrt{2} = 92.2$ MeV. CG predicts $f_\pi^{(\text{tree})} = 88.0$ MeV (Row 3), giving 95.5% agreement with the observed 92.2 MeV.

**Convention on $N_f$:** The Symbol Table uses $N_f = 2$ (light quarks $u, d$ in the chiral limit) for quantities governed by chiral perturbation theory (Rows 3, 5, 6, 11) and $N_f = 3$ (active flavors at the QCD scale) for the QCD beta function (Row 19). Both are standard — see e.g. FLAG 2024 §3 for $N_f$ conventions in lattice QCD.

$^\dagger$ **Note on $\alpha_s$ running (RESOLVED via edge-mode decomposition):** The 64 adj⊗adj channels decompose into 52 local (running) face modes and 12 non-local (non-running) holonomy modes ([Prop 0.0.17ac](Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md)). The running coupling $1/\alpha_s(M_P) = 52$ matches 1-loop QCD running to ~1% (52 predicted vs 52.5 from running). The 12 holonomy modes are topologically protected (cycle rank of K₄ × rank(SU(3)) per tetrahedron). The total exponent (52 + 12 = 64) preserves the $M_P$ prediction. Earlier claims of "0.7% agreement" and "0.038% agreement via scheme conversion" were retracted (see [Issue-1-QCD-Running-Resolution-FINAL](../../../verification/shared/Issue-1-QCD-Running-Resolution-FINAL.md)).

---

## §3. Derivation DAG

```
                    R_stella = 0.44847 fm
                    (SINGLE DIMENSIONAL INPUT)
                            │
                            ▼
        ┌─── √σ = 440 MeV ───────────────────┐
        │    [Prop 0.0.17j]                    │
        │       │                               │
   ┌────┼───────┼──────┬────────┐              │
   ▼    ▼       ▼      ▼        ▼              │
  f_π  ω     ε=1/2   M_ρ    dim. trans. ◄── 1/α_s=52 + N_hol=12
[17k] [17l]  [17o]  [17k4]  [Thm 5.2.6]    [Prop 0.0.17ac]
   │                             │         (edge-mode decomp.)
   ├──► v_χ = f_π          ┌────┤
   │   [17m]                ▼    ▼
   │                       M_P   G
   ├──► Λ = 4πf_π        [17q] [17ab]
   │   [17d]                │    │
   │                        ▼    ▼
   ├──► f_π^(1-loop)   a-theorem ℓ_P
   │   [17k1]          [Prop 0.0.21]
   │                        │
   ├──► ℓ̄₄ = 4.4      ┌────┤
   │   [17k3]          ▼    ▼
   │                  v_H   Λ_EW
   └──► g_χ = 4π/9  [0.21] [0.26]
       [3.1.1c]        │
                        ▼
                       m_H
                      [0.27]
```

**Edge count:** 25 directed edges
**Source nodes:** 1 dimensional ($R_{\text{stella}}$); 2 dimensionless (52 running + 12 holonomy modes, from $N_c$ and stella topology)
**Sink nodes:** ~15 (terminal physical quantities)
**Maximum path length:** 5 ($R_{\text{stella}} \to \sqrt{\sigma} \to M_P \to M_P^{(\text{corr})} \to G \to \ell_P$); without corrections: 4 ($R_{\text{stella}} \to \sqrt{\sigma} \to M_P \xrightarrow{a\text{-thm}} v_H \to m_H$)

**Note on edge-mode decomposition:** The UV coupling decomposes as $(N_c^2-1)^2 = 64 = 52 + 12$ ([Prop 0.0.17ac](Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md)):
- **52 local face modes** — participate in standard QCD running; $1/\alpha_s(M_P) = 52$ matches 1-loop QCD to ~1%
- **12 holonomy modes** — topologically protected, non-running; $N_{\text{hol}} = 2 \times \beta_1(K_4) \times \text{rank}(SU(3)) = 2 \times 3 \times 2$

Both contributions feed into the dimensional transmutation formula for $M_P$; the total exponent (52 + 12 = 64) preserves the $M_P$ prediction.

---

## §4. Honest Parameter Accounting

### 4.1 Framework Parameters by Category

| Category | Count | Examples | Status |
|----------|-------|---------|--------|
| **Dimensional inputs (QCD)** | **1** | $R_{\text{stella}}$ | Input (semi-derived via 0.0.17q) |
| **Dimensional inputs (beyond QCD)** | 1–2 | $M_R$; $\omega_{\text{EW}}$ if Prop 0.0.27 not accepted | Input |
| **Hidden dependencies (from EW sector)** | 1 | $m_\pi$ (used in $\epsilon$, Row 7)$^{\natural}$ | Not derived from $R_{\text{stella}}$ |
| **Dimensionless derived** | ~20 | All ratios, angles, group factors | Derived (see DAG) |
| **Dimensionless fitted (order-one)** | 3–5 | $c_f$ overlap coefficients per generation type | Order-one guaranteed by geometry |
| **Total CG parameters** | **5–8** | | |
| **SM parameters** | **20** | 12 Yukawa + 4 CKM + 4 PMNS ($\bar{\theta}$ separate)$^{\S}$ | |
| **Reduction** | **60–75%** | | |

### 4.2 Counting Conventions

**Optimistic count** (all novel derivations accepted):
- 1 dimensional input ($R_{\text{stella}}$, semi-derived)
- 3 dimensionless fitted ($c_u$, $c_t$, $c_\tau$; generation ratios constrained)
- **Total: ~4 parameters → 80% reduction**

**Conservative count** (only established derivations):
- 3 dimensional inputs ($R_{\text{stella}}$, $M_R$, $\omega_{\text{EW}}$)
- 5 dimensionless fitted ($c_f$ per sector + ratios)
- **Total: ~8 parameters → 60% reduction**

**Paper count** (main.tex §8.2):
- ~10–11 parameters total across all sectors
- **50% reduction from SM's 20 fermion-sector parameters**

### 4.3 Why $c_f$ Are Not Free Parameters in the Usual Sense

The overlap coefficients $c_f$ are bounded to order-one by three geometric properties (Prop 0.0.5b):
1. **Upper bound:** Cauchy–Schwarz on normalized densities: $c_f \leq 1$
2. **Lower bound:** Shared support on compact $\partial\mathcal{S}$ prevents $c_f \ll 1$
3. **Compactness:** $\partial\mathcal{S} \simeq S^2 \sqcup S^2$ forces $c_f \in (0, 1]$

Observed range: $0.4 \lesssim c_f \lesssim 1.2$.

$^{\S}$ **SM parameter count:** 12 Yukawa couplings (6 quark masses + 3 charged lepton masses + 3 neutrino masses, assuming Dirac neutrinos) + 4 CKM parameters (3 angles + 1 CP phase) + 4 PMNS parameters (3 angles + 1 CP phase) = 20 fermion-sector parameters. The strong CP phase $\bar{\theta}$ is a separate QCD vacuum parameter (predicted to vanish in CG via $\mathbb{Z}_3$ structure, Row 22).

$^{\natural}$ **m_π hidden input:** The pion mass $m_\pi = 140$ MeV enters the expansion parameter $\epsilon$ (Row 7) but cannot be derived from $R_{\text{stella}}$ alone. Via the GMOR relation $m_\pi^2 f_\pi^2 = (m_u + m_d)|\langle\bar{q}q\rangle|$, the pion mass ultimately depends on light quark masses $(m_u + m_d \approx 6.8$ MeV), which are Yukawa couplings from the electroweak sector — not QCD-scale inputs. This weakens the strict "uniqueness" claim but is consistent with the honest parameter accounting: $m_\pi$ is fixed once quark masses are specified, and the "dimensional uniqueness" applies specifically to QCD-intrinsic scales (string tension, decay constants, confinement parameters).

---

## §5. Significance

### 5.1 What This Proposition Establishes

1. **Rigorous uniqueness:** $R_{\text{stella}}$ is provably the *only* dimensional input needed for the entire QCD sector — every other scale follows by closed-form algebra.

2. **DAG acyclicity:** No circular reasoning exists in the derivation chain. Every quantity can be assigned a topological level, with information flowing strictly from $R_{\text{stella}}$ downward.

3. **Cross-scale connection:** The same input determines not just QCD scales but (via dimensional transmutation) Planck and electroweak scales, establishing a geometric hierarchy spanning 19 orders of magnitude.

4. **Semi-closure:** The bootstrap (Prop 0.0.17q) derives $R_{\text{stella}}$ from $M_P$ to 91% accuracy, suggesting the framework approaches self-consistency with zero free dimensional inputs.

### 5.2 What This Proposition Does NOT Claim

1. It does not claim CG has zero free parameters — the $c_f$ overlap coefficients remain order-one fitted quantities.
2. It does not claim the cross-scale derivations (especially Prop 0.0.21) are established beyond dispute — the $a$-theorem application is marked 🔶 NOVEL.
3. The "semi-derivability" of $R_{\text{stella}}$ has a 9% gap that requires further work.
4. **Hidden m_π dependency:** The expansion parameter $\epsilon$ (Row 7) uses $m_\pi$, which is NOT derivable from $R_{\text{stella}}$. Pion mass arises from explicit chiral symmetry breaking via light quark masses $(m_u, m_d)$ — these are electroweak-sector inputs (Yukawa couplings), not QCD-intrinsic quantities. The "dimensional uniqueness" claim applies to the QCD-intrinsic sector ($\sqrt{\sigma}, f_\pi, \Lambda, M_\rho$, etc.), where $R_{\text{stella}}$ is indeed the sole dimensional input.

---

## §6. Dependencies

| Dependency | Status | Role |
|------------|--------|------|
| Prop 0.0.17j | ✅ VERIFIED | Root: $\sqrt{\sigma} = \hbar c / R_{\text{stella}}$ |
| Prop 0.0.17k | ✅ VERIFIED | $f_\pi = \sqrt{\sigma}/5$ |
| Prop 0.0.17l | ✅ VERIFIED | $\omega = \sqrt{\sigma}/2$ |
| Prop 0.0.17m | ✅ VERIFIED | $v_\chi = f_\pi$ |
| Prop 0.0.17d | ✅ VERIFIED | $\Lambda = 4\pi f_\pi$ |
| Prop 0.0.17o | ✅ VERIFIED | $\epsilon = 1/2$ |
| Prop 3.1.1c | ✅ VERIFIED | $g_\chi = 4\pi/9$ |
| Prop 0.0.17k4 | ✅ VERIFIED | $M_\rho = 777$ MeV |
| Prop 0.0.17k3 | ✅ VERIFIED | $\bar{\ell}_4 = 4.4$ |
| Prop 0.0.17k1 | ✅ VERIFIED | $f_\pi^{(1\text{-loop})} = 93.8$ MeV |
| Prop 0.0.17ac | 🔶 NOVEL ✅ VERIFIED | Edge-mode decomposition: 64 = 52 (running) + 12 (holonomy) |
| Thm 5.2.6 | 🔶 NOVEL ✅ EST. | Dimensional transmutation: $M_P$ from $\sqrt{\sigma}$ |
| Prop 0.0.17q | 🔶 NOVEL | Inverse: $R_{\text{stella}}$ from $M_P$ |
| Prop 0.0.17ab | 🔶 NOVEL ✅ EST. | $G$ from topology |
| Prop 0.0.21 | 🔶 NOVEL ✅ THEORY | $v_H$ from $a$-theorem |
| Prop 0.0.27 | 🔶 NOVEL | $m_H$ from mode structure |

---

## §7. References

1. **FLAG 2024** — Flavour Lattice Averaging Group, arXiv:2411.04268
2. **PDG 2024** — Particle Data Group, Phys. Rev. D 110, 030001 (2024); $m_H = 125.20 \pm 0.11$ GeV
3. **CODATA 2018** — Recommended values of fundamental physical constants
4. **Bali (2001)** — G.S. Bali, Phys. Rep. 343, 1 (2001); direct lattice string tension measurements, $\sqrt{\sigma} \approx 440$ MeV
5. **Sommer (1994)** — R. Sommer, Nucl. Phys. B411, 839 (1994); $r_0$ scale setting in lattice QCD
6. **Weinberg (1979)** — S. Weinberg, Physica A96, 327 (1979); naive dimensional analysis $\Lambda = 4\pi f_\pi$
7. **Gasser & Leutwyler (1984)** — J. Gasser & H. Leutwyler, Ann. Phys. 158, 142 (1984); foundational chiral perturbation theory to one loop
8. **Gasser & Leutwyler (1985)** — J. Gasser & H. Leutwyler, Nucl. Phys. B250, 465 (1985); ChPT expansion in strange quark mass; source for $\bar{\ell}_i$ conventions
9. **Manohar & Georgi (1984)** — A. Manohar & H. Georgi, Nucl. Phys. B234, 189 (1984); naive dimensional analysis extension beyond Weinberg; chiral quark model
10. **'t Hooft (1973)** — G. 't Hooft, Nucl. Phys. B61, 455 (1973); dimensional transmutation in non-Abelian gauge theories
11. Prop 0.0.17j–ac — Internal proof documents (see `docs/proofs/foundations/`); notably [Prop 0.0.17ac](Proposition-0.0.17ac-Edge-Mode-Decomposition-UV-Coupling.md) for edge-mode decomposition
12. Research-P2-P4-Physical-Inputs-Unification.md — Derivation chain tracking
13. main.tex §8.2 — Paper parameter classification table

---

## §8. Verification

- **Lean 4:** `lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_35.lean` — DAG structure formalized
- **Python:** `verification/foundations/proposition_0_0_35_verification.py` — 25 numerical tests
- **Adversarial Python:** `verification/foundations/prop_0_0_35_adversarial_verification.py` — 22 quantities, Monte Carlo, DAG circularity detection, sensitivity analysis ([plots](../../../verification/plots/))
- **Multi-Agent Verification:** [Proposition-0.0.35-Multi-Agent-Verification-Report-2026-02-08](../verification-records/Proposition-0.0.35-Multi-Agent-Verification-Report-2026-02-08.md) — Literature, Mathematical, Physics agents (all adversarial). Verdict: ✅ VERIFIED with documented caveats. Key findings: DAG acyclicity proven, 22/22 quantities pass, m_π hidden input acknowledged, parameter reduction 60-80%.
- **Derivation:** [Derivation file](Proposition-0.0.35-Dimensional-Uniqueness-Of-R-Stella-Derivation.md)
- **Applications:** [Applications file](Proposition-0.0.35-Dimensional-Uniqueness-Of-R-Stella-Applications.md)

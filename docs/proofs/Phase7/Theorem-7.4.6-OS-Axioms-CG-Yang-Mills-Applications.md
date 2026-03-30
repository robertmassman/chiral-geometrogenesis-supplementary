# Theorem 7.4.6: Osterwalder-Schrader Axioms for CG Yang-Mills — Applications

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Theorem-7.4.6-OS-Axioms-CG-Yang-Mills.md) | Theorem statement, motivation, symbol table |
| [Derivation](./Theorem-7.4.6-OS-Axioms-CG-Yang-Mills-Derivation.md) | Complete derivation of OS0-OS4 |
| **Applications (this file)** | Verification, numerical checks, physical interpretation |

---

## §8. Physical Interpretation and Verification

### §8.1 What the OS Axioms Give Us

Once all five OS axioms are verified, the Osterwalder-Schrader reconstruction theorem provides the complete mathematical framework for a relativistic quantum field theory:

| OS Axiom | Reconstruction Output | Physical Meaning |
|----------|----------------------|------------------|
| OS0 (Analyticity) | Wightman functions exist as boundary values | QFT correlators are well-defined |
| OS1 (Covariance) | Poincaré group representation on $\mathcal{H}$ | Relativistic invariance |
| OS2 (Reflection RP) | Positive-definite Hilbert space $\mathcal{H}$; $H \geq 0$ | Unitarity; energy bounded below |
| OS3 (Symmetry) | Bose statistics for integer-spin fields | Spin-statistics theorem |
| OS4 (Cluster) | Unique vacuum $|\Omega\rangle$; mass gap $m > 0$ | Confinement; no massless gluons |

**The physical picture:** Starting from the stella octangula geometry ($\partial\mathcal{S}$), through the FCC lattice (Thm 0.0.6), gauge theory with exact partition function (Prop 2.5.2b), and the continuum limit, the OS reconstruction produces a full Wightman QFT — a relativistic quantum theory of SU(3) gluons with a mass gap.

### §8.2 Wightman Reconstruction: From Euclidean to Minkowski

The OS reconstruction proceeds in three steps:

**Step 1: Hilbert space from RP.**
The reflection positivity inner product defines:

$$\langle F, G \rangle = \langle \overline{\Theta F} \cdot G \rangle$$

Quotienting by null vectors and completing gives the physical Hilbert space $\mathcal{H}$. On the FCC lattice, this Hilbert space has a concrete description: states labeled by SU(3) representations $R$, with the transfer matrix providing the dynamics.

**Step 2: Hamiltonian from transfer matrix.**
The transfer matrix $\hat{T}$ (from Prop 2.5.2c) defines the Hamiltonian:

$$H = -\ln \hat{T}$$

On the FCC lattice, $\hat{T}$ is diagonal with eigenvalues $\lambda_R = d_R^{3N_s} a_R^{8N_s}$, so $H$ is also diagonal with eigenvalues $E_R = -\ln \lambda_R$. The vacuum is the trivial representation ($R = \mathbf{1}$), and the mass gap is:

$$m_\text{lat} = E_\mathbf{3} - E_\mathbf{1} = \mu(\beta) = -3\ln 3 - 8\ln u_\mathbf{3}(\beta)$$

in lattice units (per time slice). The physical mass gap includes the $\sqrt{3/2}$ factor from the [111] temporal direction: $m_\text{phys} = \sqrt{3/2}\,\mu/a$ where $a$ is the nearest-neighbor distance (Thm 7.4.5, Part b).

**Step 3: Analytic continuation to Minkowski.**
The Schwinger functions $S_n(x_1^E, \ldots, x_n^E)$ are analytically continued to Wightman functions $W_n(x_1, \ldots, x_n)$ by:

$$x_0^E \to -ix_0 \quad (\text{Euclidean time} \to \text{Minkowski time})$$

The analyticity (OS0) ensures this continuation is well-defined. The result is a Lorentzian QFT satisfying all Wightman axioms.

### §8.3 The Physical Picture: From Stella Octangula to Relativistic QFT

The complete chain from pre-geometry to QFT:

```
Stella octangula (∂S)          — Pre-geometric starting point
    ↓ Thm 0.0.3
SU(3) gauge group               — Geometry determines gauge group
    ↓ Thm 0.0.6
FCC lattice                     — Phase coherence determines lattice
    ↓ Prop 2.5.2b
Z_FCC = Σ d_R^{3N} a_R^{8N}    — Exact partition function
    ↓ Thm 7.4.1
Reflection positivity           — Physical Hilbert space exists
    ↓ Thm 7.4.2
Mass gap μ(β) > 0              — Exponential clustering
    ↓ Thm 7.4.5
Continuum mass gap (cond.)      — m_phys (see §8.3.1 below)
    ↓ Thm 7.4.6 (this theorem)
OS axioms verified              — Full Euclidean QFT framework
    ↓ OS reconstruction
Wightman QFT with mass gap      — Relativistic quantum theory
```

#### §8.3.1 Mass Gap Value and Scale Convention

The physical mass gap depends on the scale-setting convention. The lattice consensus for the lightest $0^{++}$ glueball mass is (Morningstar & Peardon 1999, Athenodorou & Teper 2020):

$$M(0^{++}) \approx 1730 \pm 130 \text{ MeV} \quad (\text{quenched, } \sqrt{\sigma} \approx 485 \text{ MeV})$$

The dimensionless ratio $M(0^{++})/\sqrt{\sigma} \approx 3.57$ is the physically meaningful, scale-independent quantity. The CG framework uses $\sqrt{\sigma} = 440$ MeV (from $R_\text{stella} = 0.44847$ fm, anchored to FLAG 2024), giving:

$$M(0^{++})_\text{CG} \approx 3.57 \times 440 \approx 1570 \text{ MeV} \approx 1.6 \text{ GeV}$$

The difference from the lattice consensus value of $\sim$1.7 GeV is entirely a scale convention difference ($\sqrt{\sigma} = 440$ vs 485 MeV), not a disagreement in the dimensionless physics. The CG transfer matrix gap $\mu = -3\ln 3 - 8\ln u_\mathbf{3}$ gives the gap to the $R = \mathbf{3}$ sector; identifying which transfer matrix eigenvalue corresponds to the physical $0^{++}$ glueball requires careful analysis of the gauge-singlet projection.

**CG-specific contributions at each step:**
- SU(3) is **derived**, not chosen (Thm 0.0.3)
- FCC lattice is **derived**, not chosen (Thm 0.0.6)
- Partition function is **exact**, not numerical (Prop 2.5.2b)
- RP is **analytically proven**, not numerically verified (Thm 7.4.1)
- Mass gap is **exact formula**, not Monte Carlo extraction (Thm 7.4.2)

### §8.4 Numerical Checks: Symmetry Restoration Diagnostics

The following numerical checks verify the approach to $SO(4)$ covariance (OS1):

#### Check 1: Lattice Dispersion Relation Isotropy

The lattice propagator on the FCC lattice has the form:

$$G^{(a)}(p) = \frac{1}{\hat{p}^2_\text{FCC} + m^2}$$

where $\hat{p}^2_\text{FCC} = \sum_\mu \hat{p}_\mu^2 + O(a^4)$ is the FCC lattice momentum. The isotropy measure:

$$\delta_\text{iso}(\mathbf{p}) = \frac{|\hat{p}^2_\text{FCC} - p^2|}{p^2}$$

should scale as $O(a^4 p^4)$. At a representative lattice spacing $a = 0.1$ fm and momentum $p = 1$ GeV:

$$\delta_\text{iso} \sim (0.1 \text{ fm} \times 1 \text{ GeV}/\hbar c)^4 \approx (0.5)^4 \approx 0.06$$

This 6% isotropy violation at coarse lattice spacing decreases as $a^4$ toward the continuum.

**Verification:** `thm_7_4_6_os_axioms.py`, Test C2.

#### Check 2: O(a⁴) vs O(a²) Artifact Scaling

Compare the leading rotational artifact on FCC vs cubic lattices:

| Lattice spacing $a$ (fm) | FCC artifact $\sim a^4$ | Cubic artifact $\sim a^2$ | Improvement factor |
|--------------------------|------------------------|--------------------------|-------------------|
| 0.2 | $1.6 \times 10^{-3}$ | $4.0 \times 10^{-2}$ | 25× |
| 0.1 | $1.0 \times 10^{-4}$ | $1.0 \times 10^{-2}$ | 100× |
| 0.05 | $6.3 \times 10^{-6}$ | $2.5 \times 10^{-3}$ | 400× |

The FCC improvement accelerates dramatically at finer lattice spacings.

**Verification:** `thm_7_4_6_os_axioms.py`, Test C2.

#### Check 3: Schwinger Function Analyticity Radius

The Schwinger functions at finite lattice spacing have analyticity domains that should expand as $a \to 0$. For two-point functions:

$$S_2^{(a)}(x) = \sum_R c_R e^{-E_R |x|}$$

The analyticity radius in $|x|$ is limited by the gap between the first and second excited states. From the exact FCC spectrum:

$$\Delta E_{12} = E_{\mathbf{8}} - E_{\mathbf{3}} = (-3\ln 8 - 8\ln u_\mathbf{8}) - (-3\ln 3 - 8\ln u_\mathbf{3}) = 3\ln(3/8) + 8\ln(u_\mathbf{3}/u_\mathbf{8})$$

Note that the dimension prefactor $3\ln(3/8) \approx -2.94$ is negative and non-negligible — it reduces the gap relative to the pure character-ratio contribution $8\ln(u_\mathbf{3}/u_\mathbf{8})$, reflecting the higher degeneracy ($d_\mathbf{8} = 8 > d_\mathbf{3} = 3$) of the adjoint representation.

**Verification:** `thm_7_4_6_os_axioms.py`, Test C3.

#### Check 4: Cluster Property Exponential Rate

The exponential decay rate equals the mass gap:

$$\text{rate} = \mu(\beta) = -3\ln 3 - 8\ln u_\mathbf{3}(\beta)$$

This should agree with the decay rate extracted from the two-point Schwinger function:

$$S_2(t) \sim e^{-\mu t} \quad \text{for large } t$$

**Verification:** `thm_7_4_6_os_axioms.py`, Test C4.

### §8.5 Status Summary: What's Proven vs Conditional

| Result | Status | Proven On | Continuum? | Conditional On |
|--------|--------|-----------|-----------|----------------|
| RP on FCC lattice | ✅ | Thm 7.4.1 | Seiler compactness | — |
| Clustering on FCC lattice | ✅ (lattice) / 🔮 (continuum) | Thm 7.4.2 | Mass gap survival required | C2 |
| Analyticity on lattice | ✅ | Finite integrals | Uniform bounds | — |
| $SO(4)$ restoration | 🔮 | $O_h$ only | Universality | C1, C3 |
| Permutation symmetry | ✅ | Trivial (commuting observables) | Preserved under limits | — (independent of OS1) |
| OS reconstruction | 🔮 | — | Needs all axioms | OS1 (→ C1) |
| Mass gap from $H$ | 🔮 | Lattice $H$ exact | Needs continuum $H$ | C1, C2 |

**Bottom line:** The OS axioms are established on the lattice (with varying levels of rigor) and carry over to the continuum under standard assumptions (C1-C3). The mathematical core of the problem — proving the continuum limit exists with full $SO(4)$ symmetry — remains open and is part of the Millennium Problem.

### §8.6 Comparison with Standard Lattice QCD Approaches

| Feature | Standard Lattice QCD | CG/FCC (This Work) |
|---------|---------------------|---------------------|
| OS2 (RP) | **Proven** (Osterwalder-Seiler 1978, Wilson action) | **Proven** (Thm 7.4.1, exact eigenvalues) |
| OS4 (Clustering) | Numerical (Monte Carlo) | **Proven** (Thm 7.4.2, exact formula) |
| OS1 (Covariance) | Assumed (universality) | **Same assumption**, but $O(a^4)$ advantage |
| OS0 (Analyticity) | Assumed (standard) | **Same argument**, with explicit bounds |
| Transfer matrix | Dense (numerical) | **Diagonal** (exact, from global label constraint) |
| Mass gap extraction | Monte Carlo + fitting | **Exact formula**: $\mu = -3\ln 3 - 8\ln u_\mathbf{3}$ |
| Continuum limit | Numerical extrapolation | **Conditional on C1-C3** (honest) |

**Note:** Reflection positivity for the Wilson action on hypercubic lattices was rigorously proven by Osterwalder & Seiler (1978) — it is not merely assumed. The CG/FCC advantage for OS2 is not that RP is proven (it is proven in both cases) but that the FCC proof provides **exact closed-form eigenvalues** of the transfer matrix, giving analytical control over the spectrum. The Millennium Problem — proving the continuum limit exists — remains equally hard in both approaches.

### §8.7 OS vs FOS: Dual-Path Comparison

Theorem 7.4.6 now supports two parallel axiomatic paths: the standard Osterwalder-Schrader (OS) framework and the Fröhlich-Osterwalder-Seiler (FOS) framework for gauge-invariant observables. This section compares the two paths and provides guidance on when each is appropriate.

#### §8.7.1 When to Use Which Path

| Goal | Recommended Path | Why |
|------|-----------------|-----|
| Prove mass gap exists (any framework) | **FOS** | Fewer hypotheses; avoids OS1 entirely |
| Prove full Wightman QFT exists | **OS** | Standard axioms; gives Poincaré covariance |
| Lattice mass gap (finite $a$) | Either (equivalent) | Both reconstruct the same $\mathcal{H}$ and $H$ on the lattice |
| Continuum mass gap *existence* | **FOS** | Needs C1 + C2 only (drops C3 for existence) |
| Continuum mass gap *value* ($m \approx 1.5$ GeV) | Either + C3 | Both need imported glueball ratio via universality |
| Millennium Problem solution | **OS + FOS** | FOS for mass gap; OS for Wightman axioms |

**Key insight:** The mass gap and the Wightman axioms are logically separable. The FOS framework makes this separation explicit: the mass gap (spectral gap of $H$) comes from the transfer matrix via RP, not from rotation covariance. The Wightman axioms (Poincaré symmetry, locality, etc.) additionally require OS1.

#### §8.7.2 Summary: What Each Path Achieves

```
                    ┌──────────────────────┐
                    │   Lattice Theory     │
                    │   (Phases A–D)       │
                    │   ✅ All proven      │
                    └──────────┬───────────┘
                               │
                    ┌──────────┴───────────┐
                    │                      │
             ┌──────┴──────┐       ┌───────┴──────┐
             │  OS Path    │       │  FOS Path    │
             │  (§1, §6)   │       │  (§1B, §6B)  │
             └──────┬──────┘       └───────┬──────┘
                    │                      │
            OS1: 🔮 (C3)          FOS1': ✅ (auto)
            OS2: ✅               FOS2: ✅
            OS3: ✅               FOS3: ✅
            OS4: ✅/🔮            FOS4: ✅/🔮
                    │                      │
            ┌───────┴───────┐      ┌───────┴───────┐
            │ Under C1+C2+C3│      │ Under C1+C2   │
            │ → Wightman QFT│      │ → H-space +   │
            │ + mass gap    │      │   mass gap     │
            │ + Poincaré    │      │ (no Poincaré)  │
            └───────┬───────┘      └───────┬───────┘
                    │                      │
                    └──────────┬───────────┘
                               │
                    ┌──────────┴───────────┐
                    │  Under C1+C2+C3:     │
                    │  Both paths give     │
                    │  Wightman QFT +      │
                    │  mass gap ≈ 1.5 GeV  │
                    │  (Millennium Problem)│
                    └──────────────────────┘
```

**Bottom line:** The FOS path provides a *stronger* intermediate result — mass gap existence under weaker hypotheses — while both paths converge at the Millennium Problem. For the specific claim "SU(3) Yang-Mills has a mass gap," the FOS path is more efficient. For the full Millennium Problem (Wightman axioms + mass gap), both paths require C1 + C2 + C3 and give equivalent results.

---

*Document created: 2026-02-13*
*Updated: 2026-02-14 — Added §8.7 (OS vs FOS dual-path comparison)*
*Classification: 🔶 NOVEL / 🔮 CONJECTURE*
*Phase: 7 (Renormalization, unitarity, consistency)*

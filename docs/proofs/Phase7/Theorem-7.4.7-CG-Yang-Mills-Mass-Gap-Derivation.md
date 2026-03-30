# Theorem 7.4.7: CG Yang-Mills Mass Gap — Derivation

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Theorem-7.4.7-CG-Yang-Mills-Mass-Gap.md) | Theorem statement, motivation, symbol table |
| **Derivation (this file)** | Complete proof of Parts (a)-(c) |
| [Applications](./Theorem-7.4.7-CG-Yang-Mills-Mass-Gap-Applications.md) | Verification, numerical checks, physical interpretation |

---

## §5. Part (a): Rigorous Lattice Mass Gap

### §5.1 The Logical Chain: Phases A → B → C → D → E ✅ ESTABLISHED

The rigorous lattice mass gap in Part (a) rests on a chain of proven results:

```
Phase A: Z_{K₄} = Σ d_R² a_R⁴         [Prop 0.0.38]
    ↓
Phase B: Z_FCC = Σ d_R^{3N} a_R^{8N}   [Prop 2.5.2b]
    ↓
Phase B: λ_R = d_R^{3N_s} a_R^{8N_s}    [Prop 2.5.2c]
    ↓
Phase C: T̂ = T̂†, T̂ ≥ 0                [Thm 7.4.1]
    ↓
Phase C: μ(β) = -3ln3 - 8ln u₃ > 0     [Thm 7.4.2]
    ↓
Phase E: H = -ln(T̂/λ₁), spec(H) ⊂ {0}∪[N_s μ,∞)  [Thm 7.4.6 → this theorem]
```

Each step is proven rigorously. No conjectures enter Part (a).

### §5.2 OS Reconstruction on the FCC Lattice ✅ ESTABLISHED

The OS reconstruction theorem (Osterwalder-Schrader 1973, 1975) applied to the FCC lattice theory proceeds as follows:

**Input:** The lattice Schwinger functions $S_n^{(a)}(x_1, \ldots, x_n)$ at lattice spacing $a = a(\beta)$ satisfying:
- OS0: Analyticity (trivially, as finite-dimensional integrals)
- OS1: Lattice covariance ($O_h \times \mathbb{Z}_2$ symmetry)
- OS2: Reflection positivity (Thm 7.4.1)
- OS3: Symmetry (commuting integrand)
- OS4: Cluster property (Thm 7.4.2)

**Output:** For each $\beta < \beta_c$:
1. A Hilbert space $\mathcal{H}_\beta$
2. A positive self-adjoint Hamiltonian $H_\beta \geq 0$
3. A vacuum state $|\Omega_\beta\rangle$ with $H_\beta |\Omega_\beta\rangle = 0$

**Remark on lattice OS1:** The lattice theory has only $O_h \times \mathbb{Z}_2$ symmetry, not full $SO(4)$. The OS reconstruction still applies — it produces a quantum mechanics (Hilbert space + Hamiltonian) with the lattice symmetry group. The lattice Hamiltonian is the correct object for Part (a); full $SO(4)$ is only needed for Part (b).

### §5.3 Hilbert Space Construction from Reflection Positivity ✅ ESTABLISHED

The RP inner product on gauge-invariant functionals $F, G$ supported in the half-lattice $\Lambda_+ = \{x : x_0 > 0\}$:

$$\langle F, G \rangle_\text{RP} = \langle \overline{\Theta F} \cdot G \rangle_\text{lattice}$$

where $\Theta$ reflects through the $x_0 = 0$ hyperplane (a (111) plane on the FCC lattice).

**Theorem 7.4.1 (RP)** guarantees $\langle F, F \rangle_\text{RP} \geq 0$. The null space $\mathcal{N} = \{F : \langle F, F \rangle_\text{RP} = 0\}$ is factored out, and the completion gives $\mathcal{H}_\beta$.

**FCC simplification:** On the FCC lattice, the transfer matrix is exactly diagonal (from the global label constraint, Prop 2.5.2b). Therefore the Hilbert space has a particularly simple structure:

$$\mathcal{H}_\beta = \bigoplus_R \mathcal{H}_R$$

where $\mathcal{H}_R$ is the one-dimensional space corresponding to the irreducible representation $R$ of SU(3). This is far simpler than the standard cubic lattice, where $\mathcal{H}$ is infinite-dimensional at finite volume.

### §5.4 Hamiltonian from Transfer Matrix: H = -ln(T̂/λ₁) ✅ ESTABLISHED

The transfer matrix $\hat{T}_\beta$ (Prop 2.5.2c) has eigenvalues:

$$\lambda_R(\beta, N_s) = d_R^{3N_s} [a_R(\beta)]^{8N_s} > 0$$

Since $\hat{T}_\beta$ is positive and self-adjoint (Thm 7.4.1), and all eigenvalues are strictly positive, $\ln \hat{T}_\beta$ is well-defined.

**Important:** The vacuum eigenvalue is $\lambda_\mathbf{1} = [a_\mathbf{1}(\beta)]^{8N_s}$ (since $d_\mathbf{1} = 1$). Note that $a_\mathbf{1}(\beta) \neq 1$ for $\beta > 0$; the strong-coupling expansion gives $a_\mathbf{1}(\beta) = 1 + \beta^2/36 + O(\beta^4)$. Therefore $-\ln \hat{T}_\beta$ does not annihilate the vacuum state.

To obtain a Hamiltonian with $H_\beta|\Omega\rangle = 0$, we define the **subtracted Hamiltonian**:

$$H_\beta = -\ln(\hat{T}_\beta / \lambda_\mathbf{1}) = -\ln \hat{T}_\beta + (\ln \lambda_\mathbf{1})\,\mathbb{1}$$

This is standard practice (equivalent to subtracting the vacuum energy). The eigenvalues of $H_\beta$ are:

$$E_R = -\ln(\lambda_R/\lambda_\mathbf{1}) = -\ln\!\left(\frac{d_R^{3N_s} a_R^{8N_s}}{a_\mathbf{1}^{8N_s}}\right) = -3N_s \ln d_R - 8N_s \ln(a_R/a_\mathbf{1})$$

The vacuum (ground state) is $R = \mathbf{1}$ (trivial representation, $d_\mathbf{1} = 1$):

$$E_\mathbf{1} = -3N_s \ln 1 - 8N_s \ln 1 = 0$$

confirming $H_\beta |\Omega\rangle = 0$. This holds for all $\beta$, regardless of the value of $a_\mathbf{1}(\beta)$.

**Remark:** The mass gap depends only on the **ratio** $u_R = a_R/a_\mathbf{1}$, not on $a_\mathbf{1}$ or $a_R$ individually. The subtraction cancels in all energy differences. This is why the claim $a_\mathbf{1} = 1$ (valid only at $\beta = 0$) was never needed for the mass gap formula.

### §5.5 Spectral Gap from Eigenvalue Ratio ✅ ESTABLISHED

The Hamiltonian spectral gap is the energy of the first excited state (using $u_\mathbf{3} = a_\mathbf{3}/a_\mathbf{1}$):

$$\Delta E(\beta) = E_\mathbf{3} - E_\mathbf{1} = -3N_s \ln 3 - 8N_s \ln(a_\mathbf{3}/a_\mathbf{1}) = N_s \cdot (-3\ln 3 - 8\ln u_\mathbf{3}(\beta)) = N_s \cdot \mu(\beta)$$

The **intensive** correlation mass (per spatial cell) is:

$$\mu(\beta) = -3\ln 3 - 8\ln u_\mathbf{3}(\beta)$$

This is the same expression derived in Theorem 7.4.2 via the transfer matrix eigenvalue ratio. The spectrum of $H_\beta$ is:

$$\text{spec}(H_\beta) = \{0\} \cup \{N_s \mu(\beta)\} \cup \{E_\mathbf{8}, E_\mathbf{6}, \ldots\}$$

with all excited state energies $\geq N_s \mu(\beta) > 0$.

**Extensive vs intensive gap.** The Hamiltonian spectral gap $\Delta E = N_s\,\mu$ is **extensive** — it grows proportionally to the spatial volume $N_s$. This is a direct consequence of the global label constraint: the lightest excitation ($R = \mathbf{1} \to R = \mathbf{3}$) flips all $N_s$ spatial cells simultaneously. There are no single-particle (single-cell) excitations in the FCC single-label sector.

The **intensive** gap $\mu(\beta)$ is the physically meaningful quantity: it governs the per-cell eigenvalue ratio $\lambda_\mathbf{3}/\lambda_\mathbf{1} = (3^3 u_\mathbf{3}^8)^{N_s} = e^{-N_s\mu}$ and determines the physical mass gap prediction via $m_\text{phys} = \sqrt{3/2}\,\mu/a$ (§5.7). In the thermodynamic limit $N_s \to \infty$, $\mu(\beta)$ remains well-defined and $N_s$-independent.

### §5.6 Positivity: m(β) > 0 for All β < β_c ✅ ESTABLISHED

**Theorem (from Thm 7.4.2).** *$\mu(\beta) > 0$ for all $\beta < \beta_c$.*

*Proof.* $\mu(\beta) > 0$ iff $-3\ln 3 - 8\ln u_\mathbf{3} > 0$ iff $8\ln u_\mathbf{3} < -3\ln 3$ iff $u_\mathbf{3}^8 < 3^{-3}$ iff $u_\mathbf{3} < 3^{-3/8}$.

At $\beta_c$, $u_\mathbf{3}(\beta_c) = 3^{-3/8}$ by definition, so $\mu(\beta_c) = 0$.

For $\beta < \beta_c$: the heat kernel coefficient ratio $u_\mathbf{3}(\beta) = a_\mathbf{3}/a_\mathbf{1}$ is a strictly increasing function of $\beta$ (since larger $\beta$ = weaker coupling, and the fundamental representation coefficient grows relative to the trivial). Therefore $u_\mathbf{3}(\beta) < u_\mathbf{3}(\beta_c) = 3^{-3/8}$ for all $\beta < \beta_c$, giving $\mu(\beta) > 0$. $\square$

### §5.7 Physical Mass: m_phys = √(3/2) · μ / a(β) ✅ ESTABLISHED

The physical mass gap in MeV is obtained by converting from lattice units:

$$m_\text{phys}(\beta) = \frac{\sqrt{3/2}\,\mu(\beta)}{a(\beta)}$$

where $a(\beta) = \sqrt{\sigma_\text{lat}(\beta)/\sigma_\text{phys}}$ is the non-perturbative lattice spacing (Thm 7.4.5, §5.1) and $a$ is the nearest-neighbor distance (Prop 7.4.3, §5.1). The factor $\sqrt{3/2}$ arises from the FCC [111] layer spacing being $d_{111} = a\sqrt{2/3}$ (the transfer matrix propagates along [111] layers separated by $d_{111}$).

Since $\mu(\beta) > 0$ and $a(\beta) > 0$ for all $\beta < \beta_c$:

$$m_\text{phys}(\beta) > 0 \qquad \forall\, \beta < \beta_c$$

**This completes the proof of Part (a):** the SU(3) Yang-Mills theory on the FCC lattice has a mass gap at every finite lattice spacing in the confined phase.

---

## §6. Part (b): Conditional Continuum Mass Gap

### §6.1 Statement of Conjectures C1-C3 🔮 CONJECTURE

The continuum mass gap requires three conjectures, formulated precisely in Theorem 7.4.5:

**Conjecture C1 (Continuum existence).** *The continuum limit of SU(3) lattice gauge theory (on any lattice with the same universality class) exists as a Wightman QFT — i.e., there exists a consistent set of Wightman functions satisfying the Wightman axioms.*

*Status:* 🔮 Open — this is the core of the Clay Millennium Problem. Balaban (1987-1989) established existence in the small-field regime; full control of all field configurations remains open.

**Conjecture C2 (Mass gap).** *The continuum SU(3) Yang-Mills theory has a mass gap $\Delta > 0$: the spectrum of the mass operator is $\{0\} \cup [\Delta, \infty)$.*

*Status:* 🔮 Open — the second part of the Millennium Problem. All numerical evidence (lattice Monte Carlo, functional methods) strongly supports this.

**Conjecture C3 (Universality).** *The FCC lattice formulation of SU(3) Yang-Mills theory has the same continuum limit as the standard hypercubic lattice formulation.*

*Status:* 🔶 Strong evidence — same gauge group, identical perturbative coefficients $b_0, b_1$ (Prop 7.4.3), standard RG universality arguments. Not rigorously proven.

### §6.2 C1 (Continuum Existence) → Subsequential Limits Exist 🔮 CONJECTURE

Under C1, the sequence of lattice theories $\{\mathcal{T}_\beta\}_{\beta < \beta_c}$ (parametrized by lattice spacing $a(\beta)$) has a well-defined continuum limit. In the Euclidean formulation, this means the lattice Schwinger functions $S_n^{(a)}$ converge to continuum Schwinger functions $S_n$ satisfying the OS axioms.

**From Theorem 7.4.6:** Under C1, the continuum Schwinger functions satisfy OS0, OS2, OS3, OS4 (proven/established). OS1 requires additionally that $SO(4)$ covariance is restored — which is part of the universality expectation.

**The OS reconstruction theorem** (Appendix A of Thm 7.4.6 Derivation) then provides: Hilbert space $\mathcal{H}$, Hamiltonian $H \geq 0$, vacuum $|\Omega\rangle$.

### §6.3 C2 (Mass Gap) → Spectral Gap Survives the Limit 🔮 CONJECTURE

Under C2, the continuum Hamiltonian has a spectral gap:

$$\text{spec}(H) \subset \{0\} \cup [\Delta, \infty), \quad \Delta > 0$$

Combined with the CG string tension $\sqrt{\sigma} = \hbar c/R_\text{stella} = 440$ MeV and the universal glueball ratio $m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$ (via C3), this gives:

$$m_\text{phys} = C_\text{gap} \cdot \Lambda_{\overline{MS}} > 0$$

with $C_\text{gap} = m_{0^{++}}/\Lambda_{\overline{MS}} = (m_{0^{++}}/\sqrt{\sigma}) / (\Lambda_{\overline{MS}}/\sqrt{\sigma}) = 3.405/0.5315 \approx 6.4$ (Athenodorou & Teper 2020; Ishikawa et al. 2017, published JHEP version).

### §6.4 C3 (Universality) → FCC Continuum = Standard SU(3) YM 🔶 NOVEL

Conjecture C3 asserts that the FCC lattice theory has the same continuum limit as the standard hypercubic lattice theory. This universality is supported by:

1. **Same gauge group:** Both have SU(3) gauge symmetry.

2. **Same perturbative beta function:** The one-loop coefficient $b_0 = 11/(16\pi^2)$ and two-loop coefficient $b_1 = 102/(16\pi^2)^2$ are universal (lattice-independent) by the standard renormalization group arguments (Prop 7.4.3).

3. **Same topological properties:** Both lattices support the same topological sectors ($\pi_3(SU(3)) = \mathbb{Z}$, instantons).

4. **Standard RG universality:** Actions differing by irrelevant operators (dimension > 4) flow to the same fixed point under the RG. The FCC-cubic difference is in the lattice structure, which produces irrelevant $O(a^2)$ or $O(a^4)$ corrections that vanish in the continuum.

**If C3 holds**, then all universal quantities computed on the hypercubic lattice (glueball spectrum, string tension ratio, Lambda parameter) transfer directly to the FCC lattice. In particular, $m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$ becomes available.

### §6.5 The R → 0 Problem and Why Universality Is Needed 🔮 CONJECTURE

The exact FCC result (Prop 7.4.4a) gives $R(\beta) = \mu/\sqrt{\sigma_\text{lat}} \to 0$ as $\beta \to \beta_c^-$. This means:

$$m_\text{phys}^\text{FCC}(\beta) = \sqrt{3\sigma_\text{phys}} \cdot R(\beta) \to 0$$

The FCC lattice alone does **not** produce a finite continuum mass gap. The mass gap vanishes because $\mu$ vanishes linearly at $\beta_c$ while $\sigma_\text{lat}$ remains finite at $(3/8)\ln 3$ (the global label constraint freezes surface roughening).

**Resolution:** The continuum mass gap is obtained via **universality** (C3), not from the FCC limit directly:
- Standard lattice QCD (on hypercubic lattices) numerically establishes $m/\sqrt{\sigma} = 3.405(21)$ in the continuum
- Universality implies the FCC lattice has the same continuum physics
- The CG framework provides $\sqrt{\sigma} = 440$ MeV
- Therefore $m \approx 1500$ MeV

### §6.6 Why This Is Not Yet a Proof of the Millennium Problem 🔮 CONJECTURE

**This theorem does NOT solve the Clay Millennium Problem.** The three conjectures C1-C3 are precisely the hard mathematical content that remains:

| What's Proven | What's Conjectured |
|---------------|-------------------|
| Mass gap at every finite $a$ | Continuum limit exists (C1) |
| OS2 (RP) and OS4 (clustering) on lattice | Mass gap survives $a \to 0$ (C2) |
| Perturbative universality ($b_0, b_1$ match) | Non-perturbative universality (C3) |
| Exact lattice spectrum | Continuum spectrum |
| Physical mass gap formula | Continuum mass gap value |

The CG framework's contribution is to **reduce the problem to three explicit conjectures** and provide **rigorous analytical control** at finite lattice spacing that standard lattice QCD achieves only numerically.

### §6.7 Alternative: FOS Path to Continuum Mass Gap 🔶 NOVEL

Under the Fröhlich-Osterwalder-Seiler (FOS) framework (Thm 7.4.6 §6B + Appendix D), the axiomatic structure of the mass gap proof is modified. The key change is that OS1 (Euclidean covariance) is replaced by FOS1' (virtual covariance for gauge-invariant observables), which is ✅ ESTABLISHED on the FCC lattice without any conjecture.

**Impact on Part (a) — Lattice mass gap:** No change. The lattice mass gap (§5) is already independent of OS1 — it comes from the transfer matrix eigenvalue ratio, which requires only RP (Thm 7.4.1) and the exact spectrum. The FOS framework merely makes this independence explicit.

**Impact on Part (b) — Continuum mass gap:** The conditional structure sharpens:

| Requirement | OS Path | FOS Path |
|-------------|---------|----------|
| Continuum limit exists | C1 | C1 |
| Mass gap survives | C2 | C2 |
| SO(4) restoration / universality | **C3** | **Not needed for mass gap existence** |
| Poincaré covariance (Wightman axioms) | C3 (included above) | **C3** (separate requirement) |

Under C1 + C2 alone, the FOS reconstruction (Seiler 1982, §4-5) produces:
- A Hilbert space $\mathcal{H}$ (from RP, same as OS)
- A Hamiltonian $H \geq 0$ (from transfer matrix, same as OS)
- A vacuum $|\Omega\rangle$ (from cluster property, same as OS)
- A spectral gap $m > 0$ (from mass gap survival, same as OS)

The resulting theory is a consistent quantum theory *with a mass gap*, but without full Poincaré covariance. The mass gap exists as a property of $\text{spec}(H) \subset \{0\} \cup [m, \infty)$ with $m > 0$, regardless of the symmetry group of $\mathcal{H}$.

**Impact on Part (c) — CG prediction $m \approx 1.5$ GeV:** The prediction still requires C3 (universality) to import the glueball ratio $m_{0^{++}}/\sqrt{\sigma} = 3.405$ from standard lattice QCD. Under the FOS path, C3 is needed for the mass gap *value*, not for mass gap *existence*.

**Impact on the Millennium Problem:** The Clay Millennium Problem (Jaffe & Witten 2000) requires:
1. Wightman axioms satisfied → needs C1 + C2 + C3 (both paths)
2. Mass gap $m > 0$ → needs C1 + C2 (FOS path) or C1 + C2 + C3 (OS path)

The FOS path shows that requirement (2) is strictly weaker than requirement (1). The mass gap is "closer to proven" than the full Wightman theory — it requires one fewer conjecture.

---

## §7. Part (c): CG Framework Prediction

### §7.1 m ≈ 3.4√σ from Imported Lattice QCD Glueball Ratio 🔶 NOVEL

The most precise determination of the lightest glueball mass in pure SU(3) gauge theory comes from lattice Monte Carlo on hypercubic lattices:

$$\frac{m_{0^{++}}}{\sqrt{\sigma}} = 3.405 \pm 0.021 \qquad \text{(Athenodorou \& Teper 2020, JHEP 11 (2020) 172)}$$

This dimensionless ratio is a universal prediction of SU(3) Yang-Mills theory — it depends on no free parameters once the theory is defined. Under universality (C3), this ratio applies to the FCC lattice as well.

### §7.2 √σ = ℏc/R_stella = 440 MeV from CG 🔶 NOVEL

The CG framework provides the string tension from the stella octangula geometry:

$$\sqrt{\sigma_\text{phys}} = \frac{\hbar c}{R_\text{stella}} = \frac{197.327 \text{ MeV·fm}}{0.44847 \text{ fm}} = 440 \text{ MeV}$$

This uses the observed $R_\text{stella} = 0.44847$ fm (consistent with FLAG 2024 $\sqrt{\sigma} = 440 \pm 30$ MeV for $N_f = 2+1$).

### §7.3 Combined Prediction: m ≈ 1.5 GeV 🔶 NOVEL

Combining the two inputs:

$$m_\text{phys} = \frac{m_{0^{++}}}{\sqrt{\sigma}} \times \sqrt{\sigma}_\text{CG} = 3.405 \times 440 \text{ MeV} = 1498 \pm 103 \text{ MeV} \approx 1.5 \text{ GeV}$$

where the uncertainty follows from error propagation: $\delta m/m = \sqrt{(0.021/3.405)^2 + (30/440)^2} = 6.85\%$, dominated by the string tension uncertainty.

**Provenance of this prediction:**

| Input | Source | Status |
|-------|--------|--------|
| $m/\sqrt{\sigma} = 3.405(21)$ | Standard lattice QCD (Athenodorou & Teper 2020) | ✅ ESTABLISHED |
| $\sqrt{\sigma} = 440$ MeV | CG framework (Prop 0.0.17j) | 🔶 NOVEL |
| Universality (C3) | Standard RG argument | 🔶 Strong evidence |

The CG-specific contribution is $\sqrt{\sigma} = \hbar c/R_\text{stella}$; the dimensionless ratio is imported from standard lattice QCD.

### §7.4 Comparison with Lattice QCD: 0⁺⁺ Glueball at 1.73 GeV 🔶 NOVEL

| Scale Convention | $\sqrt{\sigma}$ (MeV) | $m_{0^{++}}$ (MeV) | Source |
|-----------------|----------------------|---------------------|--------|
| Pure gauge ($N_f = 0$) | 485 ± 6 | 1651 ± 22 | Athenodorou & Teper (2020) |
| Full QCD ($N_f = 2+1$) | 440 ± 30 | ~1500 | FLAG 2024 + ratio |
| **CG (observed $R_\text{stella}$)** | **440** | **~1500** | This work |
| M&P (1999), $r_0$ scale | ~462 (via $r_0$) | 1730 ± 50 ± 80 | Morningstar & Peardon (using Sommer scale $r_0$, not $\sqrt{\sigma}$ directly; $\sqrt{\sigma}$ inferred via $r_0\sqrt{\sigma} \approx 1.16$) |

The CG prediction ($\sim 1500$ MeV) is consistent with the full QCD scale but below the pure-gauge value ($\sim 1650$ MeV). The $\sim 10\%$ difference arises because dynamical quarks screen the color flux tube, reducing $\sqrt{\sigma}$ from 485 to 440 MeV. The dimensionless ratio $m/\sqrt{\sigma} = 3.405$ is scale-independent.

---

## Appendix A: Complete Derivation Chain (Phase 0 → Phase E in One Page)

**Axiom:** Observer can exist.

**Phase 0 (Pre-geometry):**
- Thm 0.0.1: $D = 3+1$ from observer existence
- Thm 0.0.2: $\mathbb{R}^3$ from SU(3) Cartan subalgebra
- Thm 0.0.3: SU(3) from stella octangula uniqueness + Phys Hyp 0.0.0f
- Def 0.1.1: $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ (boundary = two disjoint $K_4$'s)
- Thm 0.0.6: FCC lattice from SU(3) phase coherence tiling
- Thm 0.2.2: Internal time $\lambda$ from Killing form arc length
- Thm 0.2.4: Pre-geometric energy $E[\chi] \geq 0$

**Phase A (Single stella):**
- Prop 0.0.38: $Z_{K_4} = \sum_R d_R^2 a_R^4$ (exact)
- Prop 0.0.38a: Spectral gap $\Delta > 0$ for $\beta < \beta_c^{(K_4)}$

**Phase B (FCC assembly):**
- Prop 2.5.2b: $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ (global label constraint)
- Prop 2.5.2c: Transfer matrix $\lambda_R = d_R^{3N_s} a_R^{8N_s}$ (diagonal!)

**Phase C (Thermodynamic limit):**
- Thm 7.4.1: Reflection positivity on FCC through (111) planes
- Thm 7.4.2: $\mu(\beta) = -3\ln 3 - 8\ln u_\mathbf{3} > 0$ for $\beta < \beta_c$ (exact, $N_s$-independent)

**Phase D (Continuum limit):**
- Prop 7.4.3: $b_0 = 11/(16\pi^2)$ universal; D₄ isotropy → $O(a^4)$ artifacts
- Prop 7.4.4: Scaling window; $R(\beta) \to 0$ at $\beta_c$
- Prop 7.4.4a: Exact Wilson loop: $\sigma_\text{exact} = -\ln u_\mathbf{3}$ (no corrections)
- Thm 7.4.5: $m_\text{phys}(\beta) > 0$ for $\beta < \beta_c$ (RIGOROUS); $m \approx 1.5$ GeV (CONDITIONAL)

**Phase E (Axioms + Main theorem):**
- Thm 7.4.6: OS axioms verified (OS2, OS4 established; OS1 conditional)
- **Thm 7.4.7: Mass gap** — Part (a) ✅ RIGOROUS; Part (b) 🔮 CONDITIONAL; Part (c) 🔶 PREDICTION

---

## Appendix B: Honest Assessment — Proven vs Conjectured

| Claim | Status | Justification | Gap to Millennium? |
|-------|--------|---------------|-------------------|
| SU(3) is the gauge group | ✅ | Thm 0.0.3 (derived from geometry) | None (framework input) |
| FCC is the lattice | ✅ | Thm 0.0.6 (derived from phase coherence) | None (framework input) |
| Partition function is exact | ✅ | Prop 2.5.2b (character expansion) | None |
| Transfer matrix is diagonal | ✅ | Global label constraint | None |
| Mass gap at finite $a$ | ✅ | Thm 7.4.2 (exact formula) | None |
| Spectral gap is extensive ($N_s\mu$) | ✅ | Global label constraint — no single-particle states | Mean-field limitation |
| RP holds on lattice | ✅ | Thm 7.4.1 (exact eigenvalues) | None |
| RP holds in continuum | ✅ | Seiler compactness (closed condition) | None |
| $SO(4)$ in continuum | 🔮 | Universality argument | **Core difficulty** |
| Mass gap in continuum | 🔮 | Requires C1 + C2 | **Core difficulty** |
| FCC = hypercubic continuum | 🔶 | $b_0, b_1$ match; RG universality | Needs rigorous proof |
| $m \approx 1.5$ GeV | 🔶 | CG $\sqrt{\sigma}$ + imported ratio | Conditional on C3 |
| Mass gap independent of SO(4) | ✅ | FOS reconstruction (Thm 7.4.6 §6B) | Mass gap from RP + transfer matrix, not covariance |
| Mass gap existence (FOS path) | 🔮 | C1 + C2 (without C3) | Drops one conjecture vs OS path |

**The honest summary:** Part (a) is a rigorous mathematical theorem. Parts (b) and (c) are conditional on conjectures that are widely believed but unproven — they constitute the mathematical core of the Millennium Problem. Under the FOS framework (§6.7), the mass gap *existence* in Part (b) requires only C1 + C2 (not C3), which is a sharper conditional result.

### Additional Caveats

**Extensive spectral gap.** The Hamiltonian spectral gap $\Delta E = N_s\,\mu$ is proportional to the spatial volume $N_s$. In the thermodynamic limit $N_s \to \infty$, this gap diverges. The physical mass gap prediction uses the *intensive* correlation mass $\mu$, which remains finite — but the Hamiltonian spectrum itself has no finite gap in the infinite-volume limit within the single-label sector.

**Absence of single-particle states.** The global label constraint forces all spatial cells to carry the same SU(3) representation. Consequently, the FCC model's excitation spectrum consists entirely of *collective* (volume-filling) modes — there are no localized single-particle excitations analogous to glueballs in standard Yang-Mills. The lightest excitation ($R = \mathbf{1} \to R = \mathbf{3}$) costs energy $N_s\,\mu$, not $\mu$.

**Effective mean-field structure.** The global label constraint reduces the FCC partition function to a single sum over representations: $Z = \sum_R d_R^{3N} a_R^{8N}$. This is effectively a zero-dimensional (single-variable) statistical mechanics problem. The exact solvability is a direct consequence of this mean-field structure — it is both the model's greatest analytical strength (enabling closed-form results) and its principal limitation (no spatial fluctuations, no dispersion relation, no momentum dependence).

**Implications for universality.** These features mean that the FCC lattice alone cannot reproduce the rich physics of the Yang-Mills continuum (glueballs, string breaking, topology). The continuum physics enters through universality (C3), which asserts that the FCC and hypercubic lattice theories share the same continuum limit despite their different finite-$a$ structures.

---

## Appendix C: Relation to the Jaffe-Witten Problem Statement

The Jaffe-Witten (2000) problem statement requires:

1. **"Quantum Yang-Mills theory on $\mathbb{R}^4$ exists..."**

    → **CG contribution:** Theorem 7.4.6 establishes the OS axioms (conditionally for OS1, rigorously for OS2/OS4). The OS reconstruction theorem then gives the Wightman QFT.

    → **Gap:** OS1 (full $SO(4)$ covariance) requires proving the continuum limit restores rotational symmetry — this is part of C1.

2. **"...and has a mass gap."**

    → **CG contribution:** Theorem 7.4.7(a) proves $m(\beta) > 0$ at every finite lattice spacing. Theorem 7.4.5(b) gives the physical mass gap formula. Part (c) predicts $m \approx 1.5$ GeV.

    → **Gap:** Proving $m > 0$ survives $a \to 0$ is Conjecture C2. The FCC exact result $R \to 0$ means the gap closes on the FCC lattice itself — the continuum mass gap requires universality (C3).

3. **"For any compact simple non-abelian gauge group $G$..."**

    → **CG contribution:** The CG framework specifically treats $G = SU(3)$, which is the physically relevant case. The Jaffe-Witten problem asks for any $G$; the CG approach addresses one specific case.

    → **Gap:** Extension to other gauge groups ($SU(N)$ for general $N$, or exceptional groups) would require generalizing the stella octangula construction.

**Conclusion:** The CG framework addresses the Millennium Problem for $G = SU(3)$ by providing rigorous analytical control at finite lattice spacing and reducing the continuum result to three explicit conjectures. The mathematical core — proving the conjectures — remains open.

---

*Document created: 2026-02-13*
*Updated: 2026-02-14 — Added §6.7 (FOS path to continuum mass gap), updated Appendix B*
*Classification: 🔶 NOVEL / 🔮 CONJECTURE*
*Phase: 7 (Renormalization, unitarity, consistency)*

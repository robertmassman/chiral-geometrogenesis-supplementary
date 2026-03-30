# Theorem 7.5.2: Perturbative Universality — Applications

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Theorem-7.5.2-Perturbative-Universality-FCC.md) | Theorem statement, motivation, symbol table |
| [Derivation](./Theorem-7.5.2-Perturbative-Universality-FCC-Derivation.md) | Complete proof of Parts (a)-(d), limitations |
| **Applications (this file)** | Verification, numerical tests, physical interpretation |

---

## §9. Physical Meaning and Applications

### §9.1 What Universality Means for the Mass Gap Program

The perturbative universality theorem has several immediate consequences for the CG Yang-Mills mass gap program:

**1. The FCC lattice probes the same continuum theory as standard lattice QCD.** Since the perturbative expansions agree, any perturbatively computable quantity (running coupling, short-distance Wilson coefficients, asymptotic freedom) is identical on both lattices. This means the FCC lattice is a legitimate regularization of SU(3) Yang-Mills theory.

**2. The R → 0 problem is a non-perturbative lattice artifact.** The vanishing of $R(\beta) = \mu/\sqrt{\sigma}$ at $\beta_c$ on the FCC lattice (Prop 7.4.4a) is invisible in perturbation theory. Perturbative universality cannot distinguish between $R \to 0$ (FCC) and $R \to R_\text{phys}$ (hypercubic). This confirms that the R → 0 behavior is a non-perturbative consequence of the FCC lattice's exact solvability (global label constraint), not a feature of the continuum theory.

**3. The CG prediction $\sqrt{\sigma} = \hbar c/R_\text{stella}$ is universal.** If the continuum theory is unique (Conjecture C3), then the string tension computed on the FCC lattice (in physical units, via the CG geometric input) is the same as on the hypercubic lattice. This justifies the CG prediction $\sqrt{\sigma} \approx 440$ MeV independently of which lattice is used.

**4. The Lambda parameter bridge.** The ratio $\Lambda_\text{FCC}/\Lambda_{\overline{MS}} \approx 0.010$ connects the FCC lattice coupling to the standard continuum coupling. This means FCC lattice data (e.g., the exact mass gap $\mu(\beta)$) can be translated to continuum physics via:

$$m_\text{phys} = \frac{\mu(\beta)}{a(\beta)} = \mu(\beta) \cdot \Lambda_\text{FCC} \cdot f(\beta) \tag{9.1}$$

where $f(\beta)$ is a known function from asymptotic scaling (Prop 7.4.3).

### §9.2 Numerical Tests of Universality

#### §9.2.1 Lambda Parameter Consistency

The Lambda parameter ratio can be tested by comparing physical predictions from the two lattices:

$$\sqrt{\sigma}_\text{FCC} = \Lambda_\text{FCC} \cdot \frac{\sqrt{\sigma}}{\Lambda_\text{FCC}} \stackrel{?}{=} \Lambda_\text{cubic} \cdot \frac{\sqrt{\sigma}}{\Lambda_\text{cubic}} = \sqrt{\sigma}_\text{cubic} \tag{9.2}$$

Using the known ratio $\sqrt{\sigma}/\Lambda_{\overline{MS}} = 1.93 \pm 0.04$ (Ishikawa et al. 2017, for quenched $N_f = 0$ SU(3)):

$$\sqrt{\sigma} = 1.93 \times \Lambda_{\overline{MS}} = 1.93 \times 260\text{ MeV} = 502\text{ MeV} \quad \text{(pure gauge)} \tag{9.3}$$

*Note on $\Lambda_{\overline{MS}}$:* We adopt $\Lambda_{\overline{MS}} = 260 \pm 20$ MeV for quenched ($N_f = 0$) SU(3), consistent with the range of modern determinations: Ishikawa et al. (2017) find $\sqrt{\sigma}/\Lambda_{\overline{MS}} = 1.93 \pm 0.04$, which combined with their $\Lambda_{\overline{MS}} = 251 \pm 6$ MeV gives $\sqrt{\sigma} \approx 485$ MeV. The $260 \pm 20$ MeV central value used throughout this work encompasses these determinations within uncertainties.

Note: This is the pure gauge string tension. The CG framework predicts $\sqrt{\sigma}_\text{CG} = \hbar c/R_\text{stella} = 440$ MeV, which corresponds to the $N_f \neq 0$ effective string tension (FLAG 2024: $\sqrt{\sigma} = 440 \pm 30$ MeV).

#### §9.2.2 Glueball Mass Ratios

If universality holds, the dimensionless glueball mass ratios should be identical:

$$\frac{m_{0^{++}}}{\sqrt{\sigma}}\bigg|_\text{FCC} = \frac{m_{0^{++}}}{\sqrt{\sigma}}\bigg|_\text{cubic} = 3.405 \pm 0.021 \tag{9.4}$$

On the FCC lattice, however, we cannot directly compute this ratio because the lattice mass gap $\mu(\beta)$ is the transfer matrix gap (which differs from the glueball mass). Furthermore, $R(\beta) \to 0$ at $\beta_c$ means the FCC lattice does not yield the continuum glueball ratio directly. The universality theorem allows us to **import** the glueball ratio from the hypercubic lattice to make predictions within the CG framework.

#### §9.2.3 Deconfinement Temperature

The deconfinement temperature in lattice units:

$$T_c/\sqrt{\sigma}\bigg|_\text{cubic} = 0.629 \pm 0.003 \quad \text{(Boyd et al.\ 1996)} \tag{9.5}$$

Under universality, the FCC lattice should give the same ratio (if the deconfinement transition can be defined on the FCC lattice). However, on the FCC lattice the transition at $\beta_c$ is first-order (bulk), not the finite-temperature deconfinement transition. These are different phase transitions.

### §9.3 Connection to Conjecture C3

#### §9.3.1 Status of C3

Conjecture C3 (Thm 7.4.5): "The FCC and standard (hypercubic) lattice formulations have the same continuum limit."

**Evidence for C3:**

| Evidence type | Status | What it shows |
|---------------|--------|---------------|
| Same gauge group SU(3) | ✅ | Necessary condition |
| Same $b_0 = 11/(16\pi^2)$ | ✅ | Perturbative agreement (1-loop) |
| Same $b_1 = 102/(16\pi^2)^2$ | ✅ | Perturbative agreement (2-loop) |
| Same perturbative expansion (all orders) | ✅ (this theorem) | Full perturbative universality |
| Lambda ratio determined | 🔶 (this theorem) | Quantitative connection |
| Same non-perturbative continuum limit | 🔮 CONJECTURE | Unproven |

**Evidence against C3:**

| Concern | Assessment |
|---------|-----------|
| R → 0 on FCC vs R → 3.405 on cubic | Not a contradiction — R is lattice-specific |
| First-order transition on FCC | Lattice artifact (see Thm 7.5.3) |
| Global label constraint | Non-perturbative difference, absent in continuum |

#### §9.3.2 Perturbative Universality as Partial C3 Resolution

This theorem resolves C3 at the perturbative level:

$$C3_\text{pert}: \quad \text{FCC and cubic have the same perturbative continuum limit} \quad ✅\text{ PROVEN}$$

What remains:

$$C3_\text{non-pert}: \quad \text{FCC and cubic have the same non-perturbative continuum limit} \quad 🔮\text{ OPEN}$$

The gap between $C3_\text{pert}$ and $C3_\text{non-pert}$ is precisely the non-perturbative sector: instantons, confinement, mass gap, topological effects. Closing this gap requires Phase G (constructive continuum limit via Balaban RG).

### §9.4 What Remains for Non-Perturbative Universality

The path from perturbative to non-perturbative universality requires:

**Step 1 (Phase F, this session):** Perturbative universality ✅ (Thm 7.5.2)
**Step 2 (Phase F, next session):** Bulk transition terminates → smooth path to weak coupling (Thm 7.5.3)
**Step 3 (Phase F/G):** Balaban RG adaptation to FCC (Research Note)
**Step 4 (Phase G):** Constructive continuum limit on FCC
**Step 5 (Phase G):** Show FCC continuum theory = hypercubic continuum theory
**Step 6 (Phase H):** Complete non-perturbative universality

### §9.5 Practical Implications

#### §9.5.1 For the CG Framework

Perturbative universality means:
- The CG prediction $\sqrt{\sigma} = \hbar c/R_\text{stella}$ is meaningful in the continuum
- FCC lattice computations can be compared with standard lattice QCD results
- The CG mass gap prediction ($\sim 1.5$ GeV) is valid under C3

#### §9.5.2 For Lattice QCD Simulations

If the FCC lattice were used for Monte Carlo simulations (which is technically possible but computationally expensive due to the 24-fold coordination):
- The improved isotropy ($c_4 = 0$ at $O(a^2)$) would reduce rotational artifacts
- Coarser lattice spacings could be used for the same precision in rotationally-sensitive quantities
- The Lambda ratio $\Lambda_\text{FCC}/\Lambda_{\overline{MS}} \approx 0.010$ would need to be accounted for in scale setting

---

## §10. Computational Verification

### §10.1 Verification Strategy

The perturbative universality theorem is verified by:

1. **Beta function universality:** Confirm $b_0$ and $b_1$ are identical on both lattices
2. **Lambda ratio computation:** Compute $\Lambda_\text{FCC}/\Lambda_\text{cubic}$ from the tadpole integral difference
3. **Observable matching:** Compare predictions for physical quantities using the two lattice formulations
4. **Scaling test:** Verify that the approach to the continuum is consistent with Symanzik predictions

### §10.2 Tests Implemented

| Test | Description | Expected result |
|------|-------------|-----------------|
| $b_0$ universality | Verify $b_0 = 11/(16\pi^2)$ on both lattices | Exact match |
| $b_1$ universality | Verify $b_1 = 102/(16\pi^2)^2$ | Exact match |
| Lambda ratio | Compute $\Lambda_\text{FCC}/\Lambda_\text{cubic}$ | $\approx 0.29 \pm 0.03$ |
| $\Lambda_\text{FCC}/\Lambda_{\overline{MS}}$ | End-to-end Lambda ratio | $\approx 0.010 \pm 0.003$ |
| Asymptotic scaling ratio | Compare $a_\text{FCC}(\beta)/a_\text{cubic}(\beta')$ at matched couplings | Consistent |
| Tadpole integrals | Verify $I_\text{FCC} \approx 0.276$, $I_\text{cubic} = 0.15493$ | Match known values |
| Operator difference | Verify all $\Delta c_i$ are for $d_i \geq 6$ operators | No $d = 4$ difference |
| $c_4^{(\text{FCC})} = 0$ | Cross-check with Prop 7.5.1 | Zero |
| Dimensional analysis | All Lambda ratios dimensionless | ✅ |
| Scaling violations | FCC vs cubic discretization error comparison | FCC smaller for rotational |

See `verification/Phase7/thm_7_5_2_perturbative_universality.py` for implementation.

**Monte Carlo multi-lattice study (2026-02-28):** Independent numerical confirmation via `verification/Phase7/thm_7_5_2_mc_universality.py` — runs D4 (triangular plaquettes) and Z^4 (square plaquettes) side-by-side at β = 1–8, comparing plaquettes, Polyakov loops, string tension, and Lambda ratio. **8/8 universality tests PASS.** Results: `verification/Phase7/thm_7_5_2_mc_universality_results.json`. Plot: `verification/plots/multi_lattice_universality.png`.

---

## §11. Self-Consistency Checks

### §11.1 Dimensional Analysis

| Quantity | Dimension | Check |
|----------|-----------|-------|
| $\Lambda_\text{FCC}/\Lambda_\text{cubic}$ | Dimensionless | ✅ (ratio of energies) |
| $\Delta_\text{finite}/(2b_0)$ | Dimensionless | ✅ (both dimensionless) |
| $a^2 \Delta c_i \int d^4x\, \mathcal{O}_i$ | Dimensionless | ✅ |
| $b_0$, $b_1$ | Dimensionless | ✅ |

### §11.2 Limiting Cases

**1. FCC → cubic (hypothetical deformation):** If the FCC lattice were continuously deformed to the hypercubic lattice (e.g., by varying the coordination number from 24 to 8), the Lambda ratio should approach 1 and the Symanzik coefficient differences should vanish. ✅ (Both lattices would become identical.)

**2. Abelian limit (U(1)):** For U(1) gauge theory, perturbative universality is well-established. Our theorem reduces to the known result that different lattice formulations of compact U(1) have the same perturbative expansion. ✅

**3. Large $N_c$ limit:** At large $N_c$, the Lambda ratio becomes exactly $N_c$-independent (subleading corrections are $O(1/N_c^2)$). The numerical value $\Lambda_\text{FCC}/\Lambda_\text{cubic} \approx 0.29$ should be $N_c$-independent to leading order. ✅ (Consistent with Celmaster's SU(2) result.)

**4. $a \to 0$ (continuum):** In this limit, all lattice artifacts vanish and the two theories become identical. This is the content of Part (d). ✅

### §11.3 Consistency with Prior Results

| Prior result | Consistency check | Status |
|-------------|-------------------|--------|
| Prop 7.4.3 Part (a): $b_0 = 11/(16\pi^2)$ | Confirmed by Part (b) | ✅ |
| Prop 7.4.3 Part (d): $\Lambda_\text{FCC}/\Lambda_{\overline{MS}} \approx 0.010$ | Confirmed by Part (c) | ✅ |
| Prop 7.5.1: $c_4^{(\text{FCC})} = 0$ | Used in Part (a) proof | ✅ |
| Thm 7.4.5 Part (c): C3 conjecture | Perturbatively resolved | ✅ |
| Prop 7.4.4a: $R \to 0$ on FCC | Non-perturbative; not contradicted | ✅ |

---

## §12. Summary

### §12.1 Main Achievements

1. **Proven:** FCC and hypercubic lattice theories have identical perturbative expansions to all orders
2. **Computed:** Lambda parameter ratio $\Lambda_\text{FCC}/\Lambda_\text{cubic} \approx 0.29$
3. **Shown:** All lattice differences are in irrelevant operators (dimension $\geq 6$)
4. **Identified:** The precise gap between perturbative and non-perturbative universality

### §12.2 Significance for the Millennium Problem

This theorem establishes that the FCC lattice is a legitimate regularization of the same SU(3) Yang-Mills theory studied on the hypercubic lattice. Combined with the exact mass gap at finite lattice spacing (Thm 7.4.2), this means:

- At any fixed lattice spacing, the mass gap exists (rigorously proven)
- The lattice theory has the same perturbative structure as the continuum theory
- The continuum mass gap depends on the non-perturbative sector, which requires further work (Phases F.4–G)

### §12.3 Next Steps

- **Thm 7.5.3:** Show the bulk transition at $\beta_c$ terminates under modified action → smooth path to weak coupling
- **Research Note:** Begin Balaban RG adaptation to FCC
- **Phase G:** Constructive continuum limit

---

*Document created: 2026-02-13*
*Classification: ✅ ESTABLISHED (methodology) / 🔶 NOVEL (FCC application)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase F (Universality and Transition Analysis)*

# Theorem 7.4.5: Continuum Mass Gap from FCC Scaling

## Status: 🔶 NOVEL / 🔮 CONJECTURE — February 2026

**Role in Framework:** This is the **main Phase D result**. It synthesizes the lattice perturbation theory (Prop 7.4.3) and scaling window analysis (Prop 7.4.4) to establish the physical (continuum) mass gap of SU(3) Yang-Mills theory on the FCC lattice. Part (b) provides a rigorous lower bound; Part (c) gives the full continuum result conditional on explicit conjectures.

**Classification:**
- Part (a): 🔶 NOVEL (formula definition)
- Part (b): ✅ ESTABLISHED (rigorous bound, any fixed $\beta < \beta_c$)
- Part (c): 🔮 CONJECTURE (continuum limit existence, conditional on Conjectures C1-C3)
- Part (d): 🔶 NOVEL (CG framework prediction)

**Key Results:**
- **(a)** Physical mass gap formula: $m_\text{phys} = \lim_{a \to 0}[\sqrt{3/2}\,\mu(\beta(a))/a(\beta)]$
- **(b)** Finite-lattice-spacing positivity (RIGOROUS): $m_\text{phys}(\beta) = \sqrt{3/2}\,\mu(\beta)/a(\beta) > 0$ for any $\beta < \beta_c$ (note: $\inf_{\beta < \beta_c} m_\text{phys}(\beta) = 0$)
- **(c)** Continuum mass gap (CONDITIONAL): under Conjectures C1-C3, $m_\text{phys} = C_\text{gap} \cdot \Lambda_{\overline{MS}} > 0$ (via universality, since $R \to 0$ on FCC)
- **(d)** CG framework prediction: $m_\text{phys} \sim O(\sqrt{\sigma}) \approx 1.5$ GeV (using imported lattice QCD glueball ratio)

**Dependencies:**
- ✅ Proposition 7.4.3 (FCC Lattice Perturbation Theory) — beta function, $\Lambda_\text{FCC}$
- ✅ Proposition 7.4.4 (Scaling Window Identification) — scaling window, conjectures
- ✅ Theorem 7.4.2 (Mass Gap Thermodynamic Limit) — lattice mass gap $\mu(\beta)$
- ✅ Proposition 0.0.17j (String Tension from Stella) — $\sqrt{\sigma} = 440$ MeV
- ✅ Proposition 0.0.17r (Lattice Spacing) — CG lattice spacing
- ✅ External: Jaffe & Witten (2000) — Clay Millennium Problem statement

**Enables:**
- Theorem 7.4.6 (Osterwalder-Schrader Axioms — Phase E)
- Theorem 7.4.7 (CG Yang-Mills Mass Gap — main result)
- Theorem 7.5.2 (Perturbative Universality) — perturbative resolution of Conjecture C3
- Theorem 7.5.3 (Bulk Transition Termination) — resolves Conjecture C2

---

## File Structure

| File | Purpose | Sections | Verification Focus |
|------|---------|----------|-------------------|
| **Theorem-7.4.5-Continuum-Mass-Gap-FCC.md** (this file) | Statement & motivation | §1-4, §9-10, References | Conceptual correctness |
| **[Theorem-7.4.5-Continuum-Mass-Gap-FCC-Derivation.md](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Derivation.md)** | Complete derivation | §5-7, Appendices | Mathematical rigor |
| **[Theorem-7.4.5-Continuum-Mass-Gap-FCC-Applications.md](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Applications.md)** | Verification & physics | §8, Numerical tests | Physical validity |

**Quick Links:**
- [→ See the complete derivation](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Derivation.md)
- [→ See applications and verification](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Applications.md)

---

## Verification Status

**Last Verified:** 2026-02-13
**Status:** 🔶 NOVEL / 🔮 CONJECTURE
**Multi-Agent Review:** PARTIAL VERIFICATION — [Verification Report](../verification-records/Theorem-7.4.5-Multi-Agent-Verification-2026-02-13.md)

### Verification Checklist
- [x] All symbols defined in symbol table
- [x] Dimensional consistency verified
- [x] Dependencies on prerequisite theorems valid
- [x] No circular references
- [x] Finite-lattice-spacing positivity verified — `thm_7_4_5_continuum_mass_gap.py`
- [x] Physical mass gap computed across scaling window — `thm_7_4_5_continuum_mass_gap.py`
- [x] CG prediction vs lattice QCD comparison — `thm_7_4_5_continuum_mass_gap.py`
- [x] Conjectures explicitly labeled and enumerated
- [x] Adversarial physics tests (17/17 pass) — `thm_7_4_5_adversarial_physics.py`
- [x] Multi-agent peer review (3 agents: literature, math, physics) — 2026-02-13
- [x] **RESOLVED:** Conjecture C1 reformulated — original C1 (R_infty > 0) falsified; restructured to C1-C3 (continuum existence, mass gap, universality)
- [x] **RESOLVED:** Lambda_QCD corrected to ~251 MeV (pure gauge, Ishikawa et al. 2017); sqrt(sigma)/Lambda ratio corrected from 2.5 to 1.93
- [x] **RESOLVED:** Glueball ratio standardized — A&T 2020 (3.405 ± 0.021) as primary; M&P 1999 clarified as r_0*m = 4.21
- [x] **RESOLVED:** Lattice spacing formula corrected (a = sqrt(sigma_lat/sigma_phys))
- [x] **RESOLVED:** "Strong-coupling bound" renamed to "Finite-lattice-spacing positivity" with infimum caveat
- [x] **RESOLVED:** "Within 1 sigma" corrected — string tension convention issue identified and discussed
- [x] **RESOLVED:** Part (d) provenance clarified — hybrid prediction (CG sqrt(sigma) + imported lattice ratio)
- [x] **RESOLVED:** Plateau extraction replaced with universality-based argument
- [x] **RESOLVED:** Non-abelian qualifier added to Jaffe-Witten; Athenodorou date corrected to 2020; M&P uncertainty expanded to 1730(50)(80)
- [x] **RESOLVED:** Missing references added (Ishikawa 2017, Lüscher-Weisz, Lucini-Teper-Wenger, A&T 2021 large-N)

### Multi-Agent Review Summary (2026-02-13)

| Agent | Verdict | Key Finding |
|-------|---------|-------------|
| Literature | Partial | Lambda_QCD incorrect for pure gauge; glueball ratio attribution imprecise |
| Mathematical | Partial | C1 falsified (R_infty = 0 proven exactly); lattice spacing formula inverted |
| Physics | Partial | R -> 0 is central structural issue; Part (d) imports standard lattice QCD ratios |

**Critical Issues Identified and Resolved:**
1. ~~Conjecture C1 with R_infty > 0 is falsified by exact results (Prop 7.4.4a)~~ → **RESOLVED:** C1-C4 restructured to C1-C3 (continuum existence, mass gap, universality); R→0 acknowledged as exact result
2. ~~Lambda_QCD = 340 MeV is N_f=3 value; pure gauge (N_f=0) is ~260 MeV~~ → **RESOLVED:** Corrected to ~251 MeV (Ishikawa et al. 2017); ratio corrected from 2.5 to 1.93
3. ~~sqrt(sigma)/Lambda ratio of 2.5 is incorrect~~ → **RESOLVED:** Corrected to 1.93(4)
4. ~~Plateau extraction method lacks mathematical justification~~ → **RESOLVED:** Replaced with universality-based argument

**See:** [Full Multi-Agent Verification Report](../verification-records/Theorem-7.4.5-Multi-Agent-Verification-2026-02-13.md)

### Verification Scripts
- `verification/Phase7/thm_7_4_5_continuum_mass_gap.py` — Standard verification (10/10 pass)
- `verification/Phase7/thm_7_4_5_adversarial_physics.py` — Adversarial verification (17/17 pass)

### Verification Plots
- `verification/plots/thm_7_4_5_adversarial_diagnostics.png` — Mass gap, R(beta), sensitivity, linear vanishing
- `verification/plots/thm_7_4_5_adversarial_multiagent.png` — C1 falsification, glueball ratio sensitivity, Lambda convention, continuum limit failure

---

## §1. Formal Statement

**Theorem 7.4.5** (Continuum Mass Gap from FCC Scaling)

*Let the SU(3) FCC lattice gauge theory be defined as in Theorems 7.4.1-7.4.2 and Propositions 7.4.3-7.4.4, with intensive mass gap $\mu(\beta) = -3\ln 3 - 8\ln u_\mathbf{3}(\beta) > 0$ for $\beta < \beta_c$, and lattice spacing $a(\beta)$ from asymptotic scaling. Then:*

**(a) Physical Mass Gap Formula.** 🔶 NOVEL *The physical mass gap is defined as:*

$$\boxed{m_\text{phys} = \lim_{\beta \to \beta_c^-} \frac{\sqrt{3/2}\,\mu(\beta)}{a(\beta)}}$$

*where the limit is taken through the scaling window (Prop 7.4.4), $a$ is the nearest-neighbor distance (Prop 7.4.3, §5.1), and $a(\beta)$ is defined non-perturbatively through the string tension: $a(\beta) = \sqrt{\sigma_\text{lat}(\beta)/(2\sigma_\text{phys})}$ (from $\sigma_\text{phys} = \sigma_\text{lat}/(2a^2)$; the factor 2 accounts for the FCC plaquette geometry).*

**(b) Finite-Lattice-Spacing Positivity (RIGOROUS).** ✅ ESTABLISHED *For any fixed $\beta < \beta_c$, the mass gap at finite lattice spacing is strictly positive:*

$$\boxed{m_\text{phys}(\beta) = \frac{\sqrt{3/2}\,\mu(\beta)}{a(\beta)} > 0 \qquad \forall\, \beta < \beta_c}$$

*This is an immediate consequence of $\mu(\beta) > 0$ (Thm 7.4.2) and $a(\beta) > 0$. It proves that the mass gap exists at every finite lattice spacing in the confined phase. Note that $\inf_{\beta < \beta_c} m_\text{phys}(\beta) = 0$ (the infimum is not attained); this is pointwise positivity, not a uniform lower bound.*

**(c) Continuum Mass Gap (CONDITIONAL).** 🔮 CONJECTURE *Under Conjectures C1-C3 (enumerated below), the continuum limit exists and gives a finite, positive mass gap:*

$$\boxed{m_\text{phys} = C_\text{gap} \cdot \Lambda_{\overline{MS}} > 0}$$

*where $C_\text{gap} \approx 6.6$ is a dimensionless constant (the mass gap in units of $\Lambda_{\overline{MS}}$, pure gauge $N_f = 0$).*

**Exact FCC result (Prop 7.4.4a):** $R(\beta) = \mu/\sqrt{\sigma_\text{lat}} \to 0$ as $\beta \to \beta_c^-$. The FCC analysis proves mass gap positivity at every finite lattice spacing (Part b), but the exact $R \to 0$ limit means the FCC lattice alone does **not** yield a positive continuum mass gap. The mass gap $\mu$ vanishes linearly at $\beta_c$ while the string tension $\sigma_\text{lat}$ remains finite at $(3/8)\ln 3 \approx 0.412$, so the lattice spacing $a = \sqrt{\sigma_\text{lat}/(2\sigma_\text{phys})}$ also remains finite ($\sim 0.20$ fm). This is a consequence of the FCC lattice's exact solvability: the global label constraint freezes out surface roughening fluctuations that would normally drive $\sigma_\text{lat} \to 0$ at a second-order transition.

*The continuum mass gap is therefore obtained via universality, not from the FCC $R \to 0$ limit directly. The conjectures are:*

| Conjecture | Statement | Status |
|------------|-----------|--------|
| **C1** (Continuum existence) | SU(3) Yang-Mills lattice gauge theory has a well-defined continuum limit as a Wightman QFT | 🔮 Open (Millennium Problem) |
| **C2** (Mass gap) | The continuum SU(3) Yang-Mills theory has mass gap $\Delta > 0$ | 🔮 Open (Millennium Problem) |
| **C3** (Universality) | The FCC and standard (hypercubic) lattice formulations have the same continuum limit | 🔶 Strong evidence (same gauge group, same $b_0$, same $b_1$) |

*Under C1-C3, the glueball-to-string-tension ratio $m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$ (Athenodorou & Teper 2020) is universal, and the CG framework provides $\sqrt{\sigma} = \hbar c/R_\text{stella}$.*

**Comparison with previous formulation:** The original Conjecture C1 (that $R_\infty > 0$) is falsified by the exact FCC result $R(\beta_c) = 0$ (Prop 7.4.4a). The reformulated C1-C3 above are honest about the FCC limitation and make the dependence on universality explicit.

**(d) CG Framework Prediction.** 🔶 NOVEL *Within the Chiral Geometrogenesis framework, the mass gap is predicted to be:*

$$\boxed{m_\text{phys} \sim O(\sqrt{\sigma}) = O\left(\frac{\hbar c}{R_\text{stella}}\right) \sim 440 \text{ MeV}}$$

*using $R_\text{stella} = 0.44847$ fm (observed). More precisely, importing the universal lattice QCD glueball ratio $m_{0^{++}}/\sqrt{\sigma} = 3.405 \pm 0.021$ (Athenodorou & Teper 2020, JHEP 11 (2020) 172):*

$$m_\text{phys} \approx 3.4 \times 440 \text{ MeV} \approx 1500 \text{ MeV} \approx 1.5 \text{ GeV}$$

*Note: The glueball ratio is imported from standard lattice QCD, not derived from the FCC analysis (see §7 in the [Derivation](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Derivation.md) for discussion of string tension conventions). The CG-specific contribution to this prediction is $\sqrt{\sigma} = \hbar c/R_\text{stella}$; the ratio $m/\sqrt{\sigma}$ relies on universality (Conjecture C3).*

---

## §2. Symbol and Dimension Table

| Symbol | Name | Type | Definition / Value |
|--------|------|------|-------------------|
| $m_\text{phys}$ | Physical (continuum) mass gap | Energy | $\lim_{a \to 0} \sqrt{3/2}\,\mu/a$ |
| $m_\text{phys}(\beta)$ | Mass gap at lattice spacing $a(\beta)$ | Energy | $\sqrt{3/2}\,\mu(\beta)/a(\beta)$ |
| $C_\text{gap}$ | Gap constant | Dimensionless | $m_\text{phys}/\Lambda_{\overline{MS}}$ |
| $\Lambda_{\overline{MS}}$ | QCD scale parameter ($\overline{MS}$, $N_f = 0$) | Energy | $\sim 251$ MeV (pure gauge; Ishikawa et al. 2017) |
| $R_\text{stella}$ | Stella octangula radius | Length | 0.44847 fm (observed) |
| $\sqrt{\sigma}$ | String tension (CG) | Energy | $\hbar c/R_\text{stella} = 440$ MeV |
| $\sqrt{\sigma_\text{PG}}$ | String tension (pure gauge lattice) | Energy | $485 \pm 6$ MeV (Athenodorou & Teper 2020) |
| $m_{0^{++}}$ | Lightest glueball mass | Energy | $\approx 1.5-1.7$ GeV (lattice QCD; convention-dependent) |
| $m_{0^{++}}/\sqrt{\sigma}$ | Glueball-to-string-tension ratio | Dimensionless | $3.405 \pm 0.021$ (Athenodorou & Teper 2020) |

---

## §3. Background and Motivation

### §3.1 The Mass Gap Problem

The Yang-Mills mass gap problem (Clay Millennium Prize) asks:

> *For any compact simple non-abelian gauge group $G$, prove that quantum Yang-Mills theory on $\mathbb{R}^4$ exists (satisfying Wightman axioms) and has a mass gap $\Delta > 0$: the spectrum of the mass operator is $\{0\} \cup [\Delta, \infty)$.*

This theorem addresses the mass gap for $G = SU(3)$ using the FCC lattice regularization derived from the stella octangula.

### §3.2 What Is Proven vs Conjectured

**Rigorously proven (Part b):**
- At any fixed lattice spacing $a > 0$ (i.e., any $\beta < \beta_c$), the mass gap exists: $m_\text{phys}(\beta) > 0$
- This is a finite-volume, finite-lattice-spacing result — it does NOT prove the mass gap in the continuum limit

**Conjectured with strong evidence (Part c):**
- The FCC exact result gives $R(\beta) \to 0$ at $\beta_c$ (Prop 7.4.4a), so the FCC lattice alone does not yield a continuum mass gap
- Under three conjectures (continuum existence, mass gap, universality), the mass gap is obtained via universality with standard lattice QCD
- C1 and C2 are aspects of the Millennium Problem; C3 (universality) has strong perturbative evidence

**Novel CG prediction (Part d):**
- The mass gap scale is set by $R_\text{stella}$, giving $m_\text{phys} \sim O(\sqrt{\sigma})$
- The precise value ($\approx 1.5$ GeV using CG scale) uses the imported lattice QCD glueball ratio

### §3.3 Comparison with Existing Approaches

| Approach | Mass gap established? | Rigorous? |
|----------|----------------------|-----------|
| Lattice Monte Carlo (standard) | Yes (numerically) | No (statistical, finite-size) |
| Constructive QFT (Balaban) | Partial (small fields) | Yes (within scope) |
| AdS/CFT (Maldacena) | Dual statement | No (duality unproven for QCD) |
| **CG/FCC (this work)** | **Yes (at finite $a$); conjectured (continuum)** | **Part b: Yes; Part c: No** |

The CG approach advances the state of the art by:
1. Providing an exact (not numerical) mass gap at finite lattice spacing
2. Using a derived (not chosen) lattice, constraining the problem
3. Identifying explicit conjectures needed for the continuum result

### §3.4 Honest Assessment of Scope

**This theorem does NOT solve the Clay Millennium Problem.** The conjectures C1-C3 (continuum existence, mass gap, universality) are precisely the hard parts that remain open. What this theorem does is:

1. **Reduce the problem** to three explicit conjectures — C1 (continuum existence), C2 (mass gap), C3 (universality) — identifying precisely what must be proven
2. **Prove mass gap positivity** at every finite lattice spacing (Part b, rigorous)
3. **Identify a structural limitation** — the exact FCC result $R \to 0$ (Prop 7.4.4a) — and honestly route the continuum limit through universality
4. **Connect the mass gap** to the geometric framework via $\sqrt{\sigma} = \hbar c/R_\text{stella}$
5. **Give a quantitative prediction** for the mass gap value ($\sim 1.5$ GeV)

---

## §4. Structure of the Derivation

### §4.1 Part (a): Physical Mass Gap Formula

**Strategy:** Define $m_\text{phys}$ through the scaling limit using the non-perturbative lattice spacing from string tension matching.

See §5 in the Derivation file.

### §4.2 Part (b): Finite-Lattice-Spacing Positivity

**Strategy:** Direct application of Theorem 7.4.2 (mass gap positivity) at finite $\beta$.

See §5 in the Derivation file.

### §4.3 Part (c): Conditional Continuum Result

**Strategy:** The exact FCC result gives $R(\beta_c) = 0$ (Prop 7.4.4a), so the FCC lattice alone does not yield a continuum mass gap. Under the reformulated Conjectures C1-C3 (continuum existence, mass gap, universality), the mass gap is obtained via universality with standard lattice QCD: $m_\text{phys} = C_\text{gap} \Lambda_{\overline{MS}}$ with $C_\text{gap} \approx 6.6$.

See §6 in the Derivation file.

### §4.4 Part (d): CG Prediction

**Strategy:** Use $\sqrt{\sigma} = \hbar c/R_\text{stella}$ and the lattice QCD glueball ratio.

See §7 in the Derivation file.

---

## §9. Summary and Connections

### §9.1 What This Theorem Establishes

1. **Rigorous:** The mass gap exists at every finite lattice spacing in the confined phase
2. **Conditional:** Under three explicit conjectures (C1-C3), the mass gap survives the continuum limit via universality
3. **Predictive:** The CG framework predicts $m_\text{phys} \approx 1.5$ GeV (using CG $\sqrt{\sigma}$ with imported lattice QCD ratio)

### §9.2 Complete Phase D Assessment

| Result | Status | Significance |
|--------|--------|-------------|
| $b_0 = 11/(16\pi^2)$ universal on FCC | ✅ ESTABLISHED | Perturbative control |
| Asymptotic scaling on FCC | ✅ ESTABLISHED | $a \to 0$ mechanism |
| FCC isotropy improvement | 🔶 NOVEL | $O(a^4)$ rotational artifacts |
| $\Lambda_\text{FCC}/\Lambda_{\overline{MS}} \approx 34$ | 🔶 NOVEL | Lambda ratio |
| Scaling window identified | 🔶 NOVEL | Continuum physics accessible |
| $m_\text{phys}(\beta) > 0$ for $\beta < \beta_c$ | ✅ ESTABLISHED | Pointwise positivity (inf = 0) |
| Continuum mass gap exists | 🔮 CONJECTURE | Millennium Problem territory |
| CG prediction $\sim 1.5$ GeV | 🔶 NOVEL | Testable (uses imported ratio) |

### §9.3 What This Enables

- **Phase E (Thm 7.4.6):** OS axioms + mass gap → Wightman theory
- **Main result (Thm 7.4.7):** Complete statement of CG Yang-Mills mass gap

---

## §10. References

### External References

1. A. Jaffe and E. Witten, "Quantum Yang-Mills Theory," Clay Mathematics Institute Millennium Problem (2000).
2. M. Creutz, *Quarks, Gluons and Lattices*, Cambridge UP (1983).
3. C. Morningstar and M. Peardon, "The glueball spectrum from an anisotropic lattice study," *Phys. Rev. D* **60** (1999) 034509, arXiv:hep-lat/9901004.
4. Y. Chen et al., "Glueball spectrum and matrix elements on anisotropic lattices," *Phys. Rev. D* **73** (2006) 014516, arXiv:hep-lat/0510074.
5. A. Athenodorou and M. Teper, "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions," *JHEP* **11** (2020) 172, arXiv:2007.06422.
6. T. Balaban, "Renormalization group approach to lattice gauge field theories," *Commun. Math. Phys.* **109** (1987) 249; **116** (1988) 1.
7. K.G. Wilson, "Confinement of quarks," *Phys. Rev. D* **10** (1974) 2445.
8. R. Sommer, "A new way to set the energy scale in lattice gauge theories," *Nucl. Phys. B* **411** (1994) 839, arXiv:hep-lat/9310022.
9. T. Ishikawa et al., "Non-perturbative determination of the $\Lambda$-parameter in the pure SU(3) gauge theory from the twisted gradient flow coupling," *JHEP* **12** (2017) 067, arXiv:1702.06289.
10. M. Lüscher and P. Weisz, "Locality and exponential error reduction in numerical lattice gauge theory," *JHEP* **09** (2001) 010, arXiv:hep-lat/0108014.
11. B. Lucini, M. Teper, and U. Wenger, "Glueballs and $k$-strings in SU($N$) gauge theories," *JHEP* **06** (2004) 012, arXiv:hep-lat/0404008.
12. A. Athenodorou and M. Teper, "SU($N$) gauge theories in 3+1 dimensions: glueball spectrum, string tensions and topology," *JHEP* **12** (2021) 082, arXiv:2106.00364.

### Framework References

13. Theorem 7.4.2 — Mass Gap Thermodynamic Limit
14. Proposition 7.4.3 — FCC Lattice Perturbation Theory
15. Proposition 7.4.4 — Scaling Window Identification
16. Proposition 7.4.4a — Exact Wilson Loop on FCC Lattice
17. Proposition 0.0.17j — String Tension from Stella
18. Proposition 0.0.17r — Lattice Spacing from Holographic Self-Consistency

---

*Document created: 2026-02-13*
*Classification: 🔶 NOVEL / 🔮 CONJECTURE*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase D (Continuum Limit)*

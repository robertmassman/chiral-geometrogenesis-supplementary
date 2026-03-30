# Literature Verification Report: Proposition 0.0.XXe

## Continuum Limit of Self-Replicating Fields on dS

**Date:** 2026-03-10
**Reviewer:** Literature Verification Agent (Claude)
**Document:** `docs/proofs/foundations/Proposition-0.0.XXe-Continuum-Self-Replicating-Fields.md`

---

## VERDICT

- **VERIFIED:** Partial
- **REFERENCE-DATA STATUS:** Most values from local cache are current; one value marginally outdated (T_c)
- **OUTDATED VALUES:** T_c ~ 155 MeV should be updated to 156.5-158 MeV per 2024 lattice results
- **CITATION ISSUES:** Two wrong titles (Refs 8, 13); one factual error about Potts transition order (SS5.3)
- **MISSING REFERENCES:** Fisher (1937), Adkins-Nappi-Witten (1983), Baxter (1973/1982), Skyrme (1961), Wu (1982), Huang (2025)
- **SUGGESTED UPDATES:** Six items detailed in Section 7
- **CONFIDENCE:** High -- all key claims independently verified via web searches and computation; remaining uncertainties are minor

---

## 1. Citation-by-Citation Verification

### Reference 1: Kolmogorov, Petrovsky, Piskunov (1937)

**Cited as:** "Study of the diffusion equation with growth of the quantity of matter and its application to a biology problem." Bull. Moscow State Univ. 1(6), 1-25 (1937).

**Verification:** CORRECT with minor notes.
- The original paper is in Russian/French. The standard citation is: Kolmogorov, A., Petrovsky, I., Piskunov, N. "Etude de l'equation de la diffusion avec croissance de la quantite de matiere et son application a un probleme biologique." Bull. Univ. Moscou, Ser. Int., Sect. A, Math. et Mecan. 1(6), 1-25 (1937).
- The English title used in the proposition is a reasonable translation.
- The paper does indeed introduce what is now called the Fisher-KPP equation (independently from R.A. Fisher's 1937 paper in the same year).
- Page range is sometimes cited as 1-26, not 1-25. Minor discrepancy.

**Status:** PASS (minor page count discrepancy)

---

### Reference 2: Aronson & Weinberger (1978)

**Cited as:** "Multidimensional nonlinear diffusion arising in population genetics." Adv. Math. 30, 33-76 (1978).

**Verification:** CORRECT.
- Published in Advances in Mathematics, Volume 30, Issue 1, pages 33-76 (1978). Confirmed via [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0001870878901305).
- The paper does establish the "hair trigger effect" for the Fisher-KPP equation in multiple spatial dimensions.

**Issue with usage in the proposition:**
- The proposition states (SS4.4): "On compact dS, the Fisher-KPP equation satisfies the hair trigger effect (Aronson & Weinberger 1978): any initial condition rho_0 not identically 0 converges to rho*."
- Aronson & Weinberger 1978 work primarily on R^n (unbounded domains), not compact manifolds. The hair trigger effect as originally stated refers to convergence on R^n where any compactly supported initial data leads to spreading at asymptotic speed c* = 2*sqrt(Dk_eff).
- On compact manifolds (like S^2), the convergence to the uniform steady state is actually EASIER to prove than the R^n case, because compactness eliminates the possibility of extinction. The result is correct, but attributing it specifically to Aronson & Weinberger 1978 is imprecise -- their paper addresses unbounded domains. The compact case follows from standard comparison principles and the maximum principle for parabolic PDEs on compact manifolds.
- **Recommendation:** Add a note that the compact-manifold version follows by standard arguments (comparison principle), with Aronson & Weinberger providing the foundational framework.

**Status:** PASS with caveat (correct result, slightly imprecise attribution)

---

### Reference 3: Svetitsky & Yaffe (1982)

**Cited as:** "Critical behavior at finite-temperature confinement transitions." Nucl. Phys. B 210, 423-447 (1982).

**Verification:** CORRECT.
- Published in Nuclear Physics B, Volume 210, Issue 4, pages 423-447 (1982). Confirmed via [ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/0550321382901729).
- The paper does establish the universality mapping between SU(N) deconfinement in (d+1) dimensions and Z_N spin models in d dimensions.
- The proposition correctly describes the Svetitsky-Yaffe conjecture.

**Status:** PASS

---

### Reference 4: Doi (1976)

**Cited as:** "Second quantization representation for classical many-particle system." J. Phys. A 9, 1465 (1976).

**Verification:** CORRECT.
- Published in Journal of Physics A: Mathematical and General, Volume 9, pages 1465-1477 (1976). DOI: 10.1088/0305-4470/9/9/008.
- The paper does introduce the second-quantization formalism for classical many-particle systems, mapping master equations to quantum Hamiltonians via creation/annihilation operators.

**Status:** PASS

---

### Reference 5: Peliti (1985)

**Cited as:** "Path integral approach to birth-death processes on a lattice." J. Physique 46, 1469 (1985).

**Verification:** CORRECT.
- Published in Journal de Physique, Volume 46, pages 1469-1483 (1985).
- The paper extends Doi's formalism into a path integral form for birth-death processes on lattices.
- Together with Doi (1976), this forms the "Doi-Peliti formalism" as cited in the proposition.

**Status:** PASS

---

### Reference 6: Parisi & Wu (1981)

**Cited as:** "Perturbation theory without gauge fixing." Sci. Sin. 24, 483 (1981).

**Verification:** CORRECT.
- Published in Scientia Sinica, Volume 24, page 483 (1981).
- The paper introduces stochastic quantization and demonstrates that gauge fields can be quantized without gauge fixing.

**Status:** PASS

---

### Reference 7: Damgaard & Huffel (1987)

**Cited as:** "Stochastic quantization." Phys. Rep. 152, 227-398 (1987).

**Verification:** CORRECT.
- Published in Physics Reports, Volume 152, Issues 5-6, pages 227-398 (1987).
- Comprehensive review of stochastic quantization methods.
- Note: The author's name should properly have an umlaut (Huffel). The proposition's rendering is acceptable for ASCII contexts.

**Status:** PASS

---

### Reference 8: Fateev & Zamolodchikov (1985)

**Cited as:** "Self-dual solutions of the star-triangle relations in Z_N-models." Sov. Phys. JETP 62, 215 (1985). -- Z3 parafermion CFT with c = 4/5.

**Verification:** FAIL -- WRONG TITLE AND REVERSED AUTHOR ORDER.
- The paper at Sov. Phys. JETP 62, 215-225 (1985) is actually titled: **"Nonlocal (parafermion) currents in two-dimensional conformal quantum field theory and self-dual critical points in Z_N-symmetric statistical systems"** by A.B. Zamolodchikov and V.A. Fateev. Confirmed via [OSTI.GOV](https://www.osti.gov/biblio/5929972), [ADS](https://ui.adsabs.harvard.edu/abs/1985JETP...62..215Z/abstract), and the [JETP archive](http://www.jetp.ras.ru/cgi-bin/dn/e_062_02_0215.pdf).
- The title cited in the proposition ("Self-dual solutions of the star-triangle relations in Z_N-models") appears to be a confusion with a different paper, possibly Fateev & Zamolodchikov's work on star-triangle relations in integrable models.
- The central charge c = 4/5 for Z3 parafermions IS correct: the general formula is c = 2(N-1)/(N+2), giving c = 2(2)/5 = 4/5 for N=3.
- The author order on the original publication is Zamolodchikov & Fateev, not Fateev & Zamolodchikov.

**Status:** FAIL

**Required fix:** Replace the entire reference entry with:

> Zamolodchikov, A.B. & Fateev, V.A. "Nonlocal (parafermion) currents in two-dimensional conformal quantum field theory and self-dual critical points in Z_N-symmetric statistical systems." *Sov. Phys. JETP* **62**, 215-225 (1985).

---

### Reference 9: Wardetzky et al. (2007)

**Cited as:** "Discrete Laplace operators: No free lunch." Symp. Geom. Process. (2007).

**Verification:** CORRECT with usage note.
- The paper was presented at the Fifth Eurographics Symposium on Geometry Processing (SGP 2007). Authors: M. Wardetzky, S. Mathur, F. Kalberer, E. Grinspun.
- The paper proves that no discrete Laplacian on triangulated surfaces can satisfy all desirable properties simultaneously.
- **Note on usage:** The proposition cites this paper for "convergence of discrete Laplacians" (SS3.2). The "No free lunch" paper is about trade-offs between desirable properties, not convergence per se. Wardetzky's 2007 PhD thesis "Discrete Differential Operators on Polyhedral Surfaces -- Convergence and Approximation" (FU Berlin) is a more appropriate reference for convergence results. However, the SGP paper does discuss convergence conditions under specific mesh quality assumptions, so the citation is not incorrect, merely suboptimal.

**Status:** PASS with note

---

### Reference 10: Eigen (1971)

**Cited as:** "Selforganization of matter and the evolution of biological macromolecules." Naturwissenschaften 58, 465-523 (1971).

**Verification:** CORRECT.
- Published in Die Naturwissenschaften, Volume 58, Issue 10, pages 465-523 (1971).
- The paper introduces the error threshold concept in molecular evolution.
- The proposition correctly uses this for the error catastrophe discussion.

**Status:** PASS

---

### Reference 11: Manton & Sutcliffe (2004)

**Cited as:** Topological Solitons. Cambridge University Press (2004).

**Verification:** CORRECT.
- Published by Cambridge University Press in 2004 (Cambridge Monographs on Mathematical Physics). ISBN: 9780521838368.
- Chapter 9 covers Skyrmions (pages 349-415). The book does discuss skyrmion classification and stability as claimed.

**Status:** PASS

---

### Reference 12: Aguera y Arcas et al. (2024)

**Cited as:** "Computational Life: How Well-formed, Self-replicating Programs Emerge from Simple Interaction." arXiv:2406.19108 (2024).

**Verification:** CORRECT.
- Submitted June 27, 2024, revised August 2, 2024. Authors: Blaise Aguera y Arcas, Jyrki Alakuijala, James Evans, Ben Laurie, Alexander Mordvintsev, Eyvind Niklasson, Ettore Randazzo, Luca Versari. Confirmed via [arXiv](https://arxiv.org/abs/2406.19108).
- The paper demonstrates emergence of self-replicating programs from random soups of code -- directly relevant to Prop 0.0.XXd which this proposition builds on.
- As of March 2026, no peer-reviewed journal publication was found. The paper remains an arXiv preprint (v2). The lead author published a related book *What Is Life?* (MIT Press/Penguin Random House) expanding on these ideas.

**Status:** PASS (still arXiv preprint as of search date)

---

### Reference 13: Barandes (2023)

**Cited as:** "The stochastic-quantum theorem." arXiv:2302.10778 (2023).

**Verification:** FAIL -- WRONG TITLE.
- The paper on arXiv:2302.10778 is titled **"The Stochastic-Quantum Correspondence"** (not "The Stochastic-Quantum Theorem"). Confirmed via [arXiv](https://arxiv.org/abs/2302.10778) (v3, revised July 30, 2025).
- The paper was published in *Philosophy of Physics*, DOI:10.31389/pop.186, under the title "The Stochastic-Quantum Correspondence."
- "The Stochastic-Quantum Theorem" may refer to a specific theorem WITHIN the paper, but it is not the paper's title.
- The content description in the proposition ("Indivisible stochastic processes are quantum") correctly captures the paper's central result.

**Status:** FAIL (wrong title)

**Required fix:** Replace the reference with:

> Barandes, J.A. "The Stochastic-Quantum Correspondence." *Philosophy of Physics* (2025). DOI:10.31389/pop.186. [arXiv:2302.10778]

---

### Reference 14: Castelnovo et al. (2005)

**Cited as:** "From quantum mechanics to classical statistical physics: Generalized Rokhsar-Kivelson Hamiltonians and the Stochastic Matrix Form decomposition." Ann. Phys. 318, 316-344 (2005).

**Verification:** CORRECT.
- Published in Annals of Physics, Volume 318, Issue 2, pages 316-344 (2005). DOI: 10.1016/j.aop.2005.01.006. Confirmed via [ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0003491605000096) and [arXiv:cond-mat/0502068](https://arxiv.org/abs/cond-mat/0502068).
- Authors: C. Castelnovo, C. Chamon, C. Mudry, P. Pujol.
- The paper establishes the connection between quantum ground states and classical equilibrium distributions via generalized Rokhsar-Kivelson Hamiltonians, as claimed.

**Status:** PASS

---

## 2. Specific Claims Verification

### Claim: Fisher-KPP hair trigger effect applies on compact manifolds (SS4.4)

**Verdict:** CORRECT RESULT, IMPRECISE ATTRIBUTION.
- The hair trigger effect on R^n is proven by Aronson & Weinberger (1978).
- On compact manifolds, the convergence to the unique positive steady state follows from simpler arguments: the Laplace-Beltrami operator on a compact manifold has a spectral gap, and the comparison principle ensures that any positive initial data grows to the unique nontrivial steady state.
- The proposition's mathematical claim is correct. The attribution could be sharpened by noting that the compact-manifold case is a standard corollary of comparison principles, with Aronson & Weinberger providing the foundational framework for the general theory.

### Claim: Svetitsky-Yaffe universality: SU(3) deconfinement <-> Z3 Potts model (SS5.2)

**Verdict:** CORRECT.
- Svetitsky & Yaffe (1982) establish this mapping for SU(N) in (d+1) dimensions mapping to Z_N spin models in d dimensions.
- The structural mapping table in SS5.2 is reasonable.

### Claim: Z3 Potts transition in 2D is first-order for q >= 3 (SS5.3)

**Verdict:** INCORRECT. This is a significant factual error.

The proposition states: *"The Z3 Potts transition in 2D is first-order (q >= 3), consistent with SU(3) deconfinement being first-order. This is a nontrivial structural match."*

The facts:
- The 2D q-state Potts model has a **second-order** (continuous) phase transition for q <= 4 and a **first-order** (discontinuous) transition for q > 4. This is Baxter's exact result (Baxter, J. Phys. C 6, L445, 1973). Confirmed via multiple sources including [Wu 1982](https://journals.aps.org/rmp/abstract/10.1103/RevModPhys.54.235) and recent computational work ([arXiv:2511.11919](https://arxiv.org/abs/2511.11919)).
- For q = 3 in 2D, the transition is **second-order** with exact critical exponents (alpha = 1/3, nu = 5/6, from Baxter's hard hexagon model).
- The Z3 Potts model in **3D** does have a first-order transition, confirmed by Monte Carlo simulations on 32^3 and 64^3 lattices ([Gavai et al.](https://www.researchgate.net/publication/13293815_Three-dimensional_q_-state_Potts_model_Monte_Carlo_study_near_q_3)).
- The Svetitsky-Yaffe mapping for SU(3) in (3+1)D maps to the **3D** Z3 Potts model, which IS first-order. This is the correct "nontrivial structural match."

**Impact on the proposition:** This error is in a caveat section and does not affect the main claims. However, it undermines the structural argument being made. The actual situation is MORE interesting for the proposition than what is stated:
- The soup lives on 2D surfaces (dS). If the soup's Z3 transition is second-order (as the 2D Potts model predicts), this matches the Svetitsky-Yaffe mapping for SU(3) in (2+1)D, which also predicts a second-order transition.
- The SU(3) deconfinement transition in (3+1)D is first-order, corresponding to the 3D Z3 Potts model.
- The dimensionality question (2D soup surfaces vs 3D or 4D physical spacetime) is an important subtlety that deserves explicit discussion rather than being papered over.

**Required fix:** Replace the sentence "The Z3 Potts transition in 2D is first-order (q >= 3)" with a corrected discussion. Suggested text:

> **First-order vs second-order:** The Z3 Potts model in 3D is first-order, consistent with SU(3) deconfinement in (3+1)D being first-order (Baxter 1973; Wu 1982). In 2D, the q=3 Potts transition is second-order (the first-order regime begins at q > 4). Since the soup lives on the 2D surface dS, the relevant comparison may be SU(3) in (2+1)D, where the transition is also second-order. The correct dimensionality assignment is an open question for the structural mapping.

### Claim: Doi-Peliti formalism: master equation -> quantum Hamiltonian (SS7.3)

**Verdict:** CORRECT.
- This is well-established. Doi (1976) and Peliti (1985) together establish this correspondence.
- The caveat about non-Hermiticity of the resulting Hamiltonian is appropriate and honest.

### Claim: Parisi-Wu stochastic quantization proven for Abelian theories only (SS7.4)

**Verdict:** PARTIALLY CORRECT but OVERSIMPLIFIED.
- Stochastic quantization has been proven perturbatively for both Abelian and non-Abelian gauge theories. The Damgaard & Huffel (1987) review covers both cases, showing that the Langevin approach reproduces standard Faddeev-Popov results without gauge fixing.
- At the perturbative level, non-Abelian theories work correctly.
- The rigorous mathematical proof (non-perturbative) is indeed established primarily for scalar and Abelian theories.
- Non-perturbative extensions to non-Abelian theories face the Gribov-Singer ambiguity.
- **Recommended clarification:** "Proven rigorously (non-perturbatively) only for scalar and Abelian theories; perturbative equivalence has been demonstrated for non-Abelian theories."

### Claim: pi_3(SU(3)) = Z (SS6.1)

**Verdict:** CORRECT.
- Standard result in algebraic topology. pi_3(SU(N)) = Z for all N >= 2. No issues.

### Claim: Skyrme model classical mass formula M = 73 f_pi / e ~ 1180 MeV (SS6.3)

**Verdict:** NOW VERIFIED CORRECT (convention-dependent).

After detailed computation, the coefficient 73 is correct under the "small f" convention:

**Derivation:**
- The B=1 hedgehog skyrmion has classical energy E_cl = (F_pi/(4e)) * tilde{E}_1 in the massless pion limit.
- The dimensionless energy tilde{E}_1 = 1.232 * 12*pi^2 = 145.9 (where 12*pi^2 = 118.4 is the Faddeev-Bogomolny bound and 1.232 is the numerical ratio for the hedgehog solution).
- Therefore: E_cl = 145.9 * F_pi/(4e) = 36.48 * F_pi/e.
- Under the convention F_pi = 2*f_pi (common in chiral perturbation theory, where F_pi ~ 186 MeV is the "big F" and f_pi ~ 93 MeV is the "small f"):
  - E_cl = 36.48 * (2*f_pi)/e = **72.96 * f_pi/e ~ 73 * f_pi/e**
- With the CG value f_pi = 88 MeV and e = 5.45:
  - M_cl = 73 * 88 / 5.45 = **1178 MeV** (matches the proposition's "~1180 MeV")

**The coefficient 73 is correct** provided f_pi is the "small f" convention. The CG framework uses f_pi = 88 MeV from Prop 0.0.17k (sqrt(sigma)/5), which is indeed the small-f convention.

**Recommendation:** Add a brief note specifying the convention: "where f_pi is in the standard chiral perturbation theory convention (f_pi ~ 93 MeV in QCD, here f_pi = 88 MeV from the CG derivation)." Also cite Adkins, Nappi & Witten (1983) as the source of the classical mass calculation.

### Claim: QCD deconfinement temperature T_c ~ 155 MeV (SS5.2)

**Verdict:** APPROXIMATELY CORRECT, marginally outdated.
- Current lattice QCD consensus for the chiral crossover temperature at zero baryon chemical potential:
  - HotQCD: T_c = 156.5 +/- 1.5 MeV
  - Recent 2024 determinations: T_c = 158.0 +/- 0.6 MeV ([arXiv:2410.06216](https://arxiv.org/abs/2410.06216))
- The value 155 MeV is within the range of earlier determinations but slightly below current best values.
- Important subtlety: A 2025 study using centre vortex analysis ([arXiv:2504.08131](https://arxiv.org/abs/2504.08131)) distinguishes the chiral transition temperature (~155-158 MeV) from the "deconfinement" temperature defined by vortex percolation (T_d ~ 321 MeV). The proposition's structural mapping uses "deconfinement" language but the numerical value corresponds to the chiral crossover.
- For the proposition's structural mapping purposes, T_c ~ 155 MeV is adequate. Consider updating to "T_c ~ 155-158 MeV."

### Claim: Eigen error threshold theory (SS5.1)

**Verdict:** CORRECT usage, with one notable and honestly reported deviation.
- The proposition correctly identifies the error catastrophe concept from Eigen (1971).
- The standard Eigen result is mu_c ~ 1/L (error threshold inversely proportional to genome length), giving the well-known product rule mu_c * L ~ 1.
- The proposition notes that mu_c is constant across program lengths in the soup simulation, violating Eigen scaling. This is an interesting and honestly reported deviation that actually strengthens the analysis by demonstrating that the soup's error threshold has a different (VM-intrinsic) origin than Eigen's molecular replication threshold.

---

## 3. Missing References

### Important prior works not cited:

1. **Fisher, R.A. (1937).** "The wave of advance of advantageous genes." *Annals of Eugenics* 7, 355-369.
   - Fisher independently derived the same equation as KPP in the same year. Standard practice in the PDE literature is to cite both Fisher and KPP when referring to the "Fisher-KPP equation."

2. **Adkins, G.S., Nappi, C.R., & Witten, E. (1983).** "Static properties of nucleons in the Skyrme model." *Nucl. Phys.* B228, 552-566. Confirmed via [ADS](https://ui.adsabs.harvard.edu/abs/1983NuPhB.228..552A).
   - This is THE foundational paper for the skyrmion mass calculation used in SS6.3 (M = 73 f_pi/e). The proposition cites only Manton & Sutcliffe (2004) for skyrmion physics, but ANW is the primary source for the B=1 classical mass formula.

3. **Baxter, R.J. (1973).** "Potts model at the critical temperature." *J. Phys. C* 6, L445.
   - Essential for the claim about phase transition order in the Potts model. Without this reference, the (currently incorrect) claim in SS5.3 has no authority. Also consider:
   - Wu, F.Y. (1982). "The Potts model." *Rev. Mod. Phys.* 54, 235-268. -- Standard comprehensive review.

4. **Skyrme, T.H.R. (1961).** "A non-linear field theory." *Proc. R. Soc.* A 260, 127-138.
   - The original paper proposing topological solitons in meson field theory. Given the extensive use of skyrmion physics in SS6, the original paper should be cited.

5. **Eigen, M. & Schuster, P. (1977).** "The Hypercycle." *Naturwissenschaften* 64, 541-565.
   - The quasispecies theory developed jointly with Schuster is more complete than the 1971 paper alone. The "error catastrophe" concept is more precisely formulated in the Eigen-Schuster hypercycle work.

6. **Huang, T. (2025).** "Quantum Vacuum Self-Consistency as the Dynamical Origin of Spacetime and Particle Physics." *arXiv:2511.04170*.
   - A 2025 paper that develops a "quantum vacuum self-consistency principle" where classical backgrounds are macroscopic order parameters sustained by their own fluctuations. This is conceptually closely related to the proposition's bootstrap identification (Phi(T) = T). While the approaches differ significantly in detail, the paper should be cited as related prior/concurrent work on vacuum self-consistency.

---

## 4. Novelty Assessment: Catalytic/Non-Catalytic Dichotomy

**Is the catalytic/non-catalytic dichotomy genuinely novel?**

**Verdict:** The specific framing is novel; the underlying physics is well-established.

**What is standard:**
- The distinction between topologically trivial (Q=0, vacuum sector) and topologically nontrivial (Q != 0, soliton sector) configurations is completely standard in the topological soliton literature (Manton & Sutcliffe 2004; Rajaraman, *Solitons and Instantons*, 1982).
- The identification of vacuum as a "global attractor" in the Q=0 sector is standard Fisher-KPP theory.
- The identification of baryons as topologically protected skyrmions is standard (Skyrme 1961; Adkins, Nappi & Witten 1983).
- The distinction between topological and non-topological solitons has been studied extensively (Lee & Pang, Phys. Rep. 221, 251-350, 1992; Friedberg et al., 1976).

**What is novel:**
- The specific language of "catalytic" vs "non-catalytic" borrowed from the self-replicating soup context.
- The explicit identification of the QCD vacuum as "self-replicating" via Fisher-KPP dynamics -- the vacuum fills space because it is catalytic, not merely because it is the lowest-energy state.
- The connection between Fisher-KPP front propagation and vacuum "replication."
- The explicit table mapping catalytic/non-catalytic to vacuum/matter with protection mechanisms (dynamical vs topological).
- No prior work was found that uses precisely this "catalytic/non-catalytic" framing for the vacuum/matter distinction.

**Related but distinct work:**
- Huang (2025, arXiv:2511.04170) discusses vacuum self-consistency but without the self-replication/catalytic language.
- The "false vacuum decay" literature (Coleman 1977; Coleman & De Luccia 1980) discusses vacuum transitions but in a different context (tunneling between local minima, not self-replication of a global attractor).
- Self-replication in quantum systems (Baskov et al., Sci. Rep. 2021) studies quantum artificial organisms but not in the QFT vacuum context.

**Assessment:** The dichotomy is a novel *framing* of established physics, not a novel physical result. This is appropriately marked as "NOVEL" in the proposition. The framing provides genuine conceptual insight: it explains WHY vacuum fills space (catalytic attractor) and WHY particles are localized (non-catalytic, topologically protected) using a single dynamical principle.

---

## 5. Summary of Issues

### Errors requiring correction:

| # | Section | Issue | Severity |
|---|---------|-------|----------|
| 1 | SS5.3 | "Z3 Potts transition in 2D is first-order (q >= 3)" is wrong. In 2D, q=3 Potts is second-order (Baxter). First-order transition is in 3D. | **HIGH** |
| 2 | Ref 8 | Wrong title for Zamolodchikov & Fateev (1985); author order reversed | MEDIUM |
| 3 | Ref 13 | Wrong title for Barandes paper ("Theorem" should be "Correspondence"); now published in journal | MEDIUM |

### Claims requiring clarification:

| # | Section | Issue | Severity |
|---|---------|-------|----------|
| 4 | SS4.4 | Hair trigger attribution to Aronson-Weinberger imprecise for compact manifolds | LOW |
| 5 | SS7.4 | Parisi-Wu "proven only for Abelian" oversimplifies; perturbative proofs exist for non-Abelian | LOW |
| 6 | SS6.3 | Skyrmion mass formula M = 73 f_pi/e is CORRECT but needs convention note and ANW citation | LOW |
| 7 | SS5.2 | T_c ~ 155 MeV slightly below current best values (156.5-158 MeV) | LOW |

### Missing references:

| # | Reference | Why needed |
|---|-----------|-----------|
| 1 | Fisher (1937) | Co-discoverer of the Fisher-KPP equation |
| 2 | Adkins, Nappi & Witten (1983) | Source of skyrmion mass formula used in SS6.3 |
| 3 | Baxter (1973) | Authority for Potts model phase transition order |
| 4 | Skyrme (1961) | Original skyrmion paper |
| 5 | Wu (1982) | Standard Potts model review |
| 6 | Huang (2025) | Related work on vacuum self-consistency |

---

## 6. Outdated Values

| Value | Used in proposition | Current best value | Source |
|-------|--------------------|--------------------|--------|
| T_c (QCD crossover) | ~155 MeV | 156.5 +/- 1.5 MeV (HotQCD) or 158.0 +/- 0.6 MeV (2024 lattice) | arXiv:2410.06216 and references therein |

All other numerical values (f_pi = 88 MeV from CG, k_eff = 0.22, mu_c = 0.011, etc.) are internal framework parameters derived from soup simulations and are not subject to external verification against published data.

---

## 7. Suggested Updates

### Priority 1 (errors):

1. **Fix the Potts model claim (SS5.3).** Replace:
   > "The Z3 Potts transition in 2D is first-order (q >= 3), consistent with SU(3) deconfinement being first-order."

   With:
   > "The Z3 Potts model in 3D is first-order (Baxter 1973; confirmed by Monte Carlo on 32^3 and 64^3 lattices), consistent with SU(3) deconfinement in (3+1)D being first-order. In 2D, the q=3 Potts transition is second-order (first-order onset at q > 4). Since the soup lives on 2D surfaces, the relevant mapping may be to SU(3) in (2+1)D, where the transition is also second-order. The correct dimensionality assignment is an open question for the structural mapping."

2. **Fix Reference 8.** Replace with: Zamolodchikov, A.B. & Fateev, V.A. "Nonlocal (parafermion) currents in two-dimensional conformal quantum field theory and self-dual critical points in Z_N-symmetric statistical systems." *Sov. Phys. JETP* **62**, 215-225 (1985).

3. **Fix Reference 13.** Replace with: Barandes, J.A. "The Stochastic-Quantum Correspondence." *Philosophy of Physics* (2025). DOI:10.31389/pop.186. [arXiv:2302.10778]

### Priority 2 (improvements):

4. **Add missing references.** At minimum: Fisher (1937), Adkins-Nappi-Witten (1983), Baxter (1973), and Wu (1982).

5. **Add convention note to SS6.3.** After the skyrmion mass formula, note: "Here f_pi is the pion decay constant in the standard ChPT convention (f_pi ~ 93 MeV in QCD; f_pi = 88 MeV in the CG derivation of Prop 0.0.17k). The coefficient 73 = 1.232 * 12*pi^2 / 2 arises from the Faddeev-Bogomolny bound (12*pi^2) times the numerical hedgehog ratio (1.232), converted from the F_pi = 2*f_pi convention of Adkins, Nappi & Witten (1983)."

6. **Clarify Parisi-Wu status (SS7.4).** Revise to: "Stochastic quantization reproduces standard perturbative results for both Abelian and non-Abelian gauge theories (Damgaard & Huffel 1987). Rigorous non-perturbative proofs are established only for scalar and Abelian theories; the non-Abelian extension faces the Gribov-Singer ambiguity."

### Priority 3 (optional enhancements):

7. **Update T_c value.** Change "T_c ~ 155 MeV" to "T_c ~ 155-158 MeV" with a note about the chiral crossover vs deconfinement distinction.

8. **Cite Huang (2025)** in the Discussion/References as related concurrent work on vacuum self-consistency principles.

9. **Strengthen hair trigger attribution (SS4.4).** Add: "The hair trigger effect on R^n is due to Aronson & Weinberger (1978); on compact dS the same conclusion follows a fortiori from the spectral gap of the Laplace-Beltrami operator and the comparison principle for parabolic PDEs."

---

## 8. Overall Assessment

The proposition is a creative and well-structured piece of theoretical work that connects self-replicating dynamics on the stella octangula boundary to established physics. Of the 14 references, 11 are correct, 2 have wrong titles (Refs 8 and 13), and 1 is correctly cited but the claim based on it is factually wrong (Potts model transition order, using Ref 3).

**Scorecard:**

| Category | Score | Details |
|----------|-------|---------|
| Citation accuracy (14 refs) | 11/14 correct | 2 wrong titles, 1 wrong claim |
| Numerical values | 9/10 | T_c marginally outdated |
| Physics claims | 8/9 | Potts 2D first-order is wrong |
| Appropriate caveats | 10/10 | Limitations section (SS8) is exemplary |
| Novelty claims | Fair | Catalytic/non-catalytic framing is genuinely novel |
| Missing references | 6 identified | Most important: ANW (1983), Baxter (1973) |

The main issues are:

1. **A factual error** about the order of the Z3 Potts transition in 2D (HIGH priority). This is a well-known exact result (Baxter 1973) and getting it wrong undermines the structural argument being made. The fix is straightforward and actually strengthens the discussion by introducing the dimensionality subtlety.

2. **Two incorrect reference titles** (MEDIUM priority). The Zamolodchikov-Fateev paper title is simply wrong (probably confused with a different paper). The Barandes paper title was updated between revisions and is now published.

3. **The skyrmion mass coefficient** is verified correct (73 = 1.232 * 12*pi^2 / 2 under the f_pi = F_pi/2 convention), resolving the earlier uncertainty. A convention note and ANW citation should be added.

The novel contributions (catalytic/non-catalytic dichotomy, bootstrap identification, error-catastrophe/deconfinement mapping) are honestly presented with appropriate caveats about their structural (vs. quantitative) nature. The limitations section (SS8) is commendably thorough and does not overstate confidence.

**CONFIDENCE: High.** All 14 references have been independently verified via web searches. The Potts model error is definitive (Baxter's exact solution is unambiguous, confirmed by multiple modern sources). The reference title errors are confirmed by OSTI, ADS, and arXiv records. The skyrmion mass coefficient has been verified by explicit computation.

---

## Sources Consulted

- [Svetitsky & Yaffe 1982 (ScienceDirect)](https://www.sciencedirect.com/science/article/abs/pii/0550321382901729)
- [Aronson & Weinberger 1978 (ScienceDirect)](https://www.sciencedirect.com/science/article/pii/0001870878901305)
- [Zamolodchikov & Fateev 1985 (OSTI)](https://www.osti.gov/biblio/5929972)
- [Zamolodchikov & Fateev 1985 (ADS)](https://ui.adsabs.harvard.edu/abs/1985JETP...62..215Z/abstract)
- [Barandes 2023/2025 (arXiv)](https://arxiv.org/abs/2302.10778)
- [Castelnovo et al. 2005 (arXiv)](https://arxiv.org/abs/cond-mat/0502068)
- [Aguera y Arcas et al. 2024 (arXiv)](https://arxiv.org/abs/2406.19108)
- [Adkins, Nappi & Witten 1983 (ADS)](https://ui.adsabs.harvard.edu/abs/1983NuPhB.228..552A)
- [QCD deconfinement transition 2024 (arXiv)](https://arxiv.org/abs/2410.06216)
- [3D Z3 Potts Monte Carlo (ResearchGate)](https://www.researchgate.net/publication/13293815_Three-dimensional_q_-state_Potts_model_Monte_Carlo_study_near_q_3)
- [Potts model phase transition order (arXiv)](https://arxiv.org/abs/2511.11919)
- [Huang 2025 vacuum self-consistency (arXiv)](https://arxiv.org/abs/2511.04170)
- [Skyrme model parameters (arXiv)](https://ar5iv.labs.arxiv.org/html/1509.04795)

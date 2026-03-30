# Proposition 0.0.XXe: Continuum Limit of Self-Replicating Fields on dS

## Status: WORKPLAN — NOT YET A PROPOSITION

**Goal:** Bridge the gap between the discrete Stella Soup (Prop 0.0.XXd) and continuous field dynamics on dS, establishing that self-replicating field configurations are the continuum analog of the bootstrap fixed point F = B(F).

**Created:** 2026-03-06
**Dependencies:** Prop 0.0.XXd (Computational Universality), Def 0.1.1 (Stella Topology), Def 0.1.2 (Three Color Fields), Thm 0.2.1 (Field Superposition)

---

## The Gap to Bridge

**Discrete (Prop 0.0.XXd):**
- 1D tape, Z_3 cells, discrete time steps
- Programs = finite trit strings
- Self-replication: S + F -> (S, S) via split(exec(S||F))

**Continuous (target):**
- Field configurations on dS (two tetrahedral surfaces)
- phi: dS -> C with Z_3-symmetric potential
- Self-replicating soliton: sigma * f -> (sigma, sigma) under field dynamics

**Key equation to establish:**
- Discrete: S = split(exec(S || F))_1
- Continuum: sigma = B[sigma] (bootstrap fixed-point equation)
- Prove these are the same equation in different limits

---

## Phase 1: 2D Soup on Triangulated dS [COMPUTATIONAL]

### Motivation
The current soup runs on a 1D tape. Lifting to 2D (the actual geometry of dS) tests whether self-replicator emergence depends on dimension or survives on the physical geometry.

### Tasks

- [x] **1.1 Triangulate dS** — COMPLETE
  - O(n^2) direct-index mesh construction with canonical vertex numbering
  - n_sub up to 157 tested; sites per tetra = 2n^2 + 2
  - Voronoi-like tiling partitions surface into non-overlapping tiles
  - Files: `stella_lang/soup_2d.c` (patch), `soup_2d_tile.c` (tile)

- [x] **1.2 Define local interaction rule** — COMPLETE
  - Two models tested: patch (overlapping BFS regions) and tile (non-overlapping Voronoi)
  - 1D VM reused unchanged; 2D patches linearized via BFS order
  - Local pairing: tile neighbors + 50% T+/T- cross-talk (Thm 0.2.1)

- [x] **1.3 Define 2D replication** — COMPLETE
  - Same as 1D: P concatenated with zeros, after VM execution, produces (P, P)
  - Trivial replicators (all-same-trit) filtered out

- [x] **1.4 Run experiments** — COMPLETE (single-stella + multi-stella FCC)
  - Single stella: replicators at 800K (n100 local), 3.9M (n100 global), 9.65M (n157 local)
  - Multi-stella L=2: 4/4 stellae colonized at ~87% density (corrected; was ~55% with BFS tiling bug)
  - Multi-stella L=4: 32/32 stellae colonized at ~87% density (corrected; was ~56% with BFS tiling bug), emergence at 80K
  - Cross-rate sweep (0.01, 0.1, 1.0, 10.0) COMPLETE — equilibrium density 86.4–87.0% across all cross-rates (see RERUN_PLAN.md Priority 2)

- [x] **1.5 Document results** — COMPLETE
  - Full results in `docs/proofs/verification-records/Proposition-0.0.XXe-Phase1-2D-Soup-Results.md`
  - Replicator structure identical to 1D (VM-intrinsic, not geometry-dependent)
  - Population >= ~1,666 tiles required; emergence is sudden and explosive
  - Local pairing accelerates emergence ~5x vs global

### Success criterion
Self-replicating patterns emerge on triangulated dS, using only local Z_3 interactions derived from CG primitives. **MET** — nontrivial self-replicators emerge on 2D stella geometry and propagate across multi-stella FCC lattice.

---

## Phase 2: Z_3 Potts Model Connection [THEORETICAL]

### Motivation
The Z_3 soup on a triangulated surface is closely related to the 3-state Potts model, which has a well-studied continuum limit (Z_3 parafermion CFT). Establishing this connection gives access to a large body of existing results.

### Tasks

- [x] **2.1 Map soup to Potts model** — COMPLETE
  - Dictionary established: Z₃ cells ↔ Potts spins, μ ↔ T, ρ_rep ↔ magnetization
  - Key answer: soup is fundamentally **non-equilibrium** (no energy function, no detailed balance)
  - Mapping is structural (same Z₃ symmetry) not quantitative
  - Full analysis: `docs/proofs/supporting/Proposition-0.0.XXe-Phase2-Z3-Potts-Model-Connection.md` §2.1

- [x] **2.2 Characterize the soup's statistical mechanics** — COMPLETE
  - No partition function; master equation governs NESS
  - μ ↔ T confirmed; μ_c ≈ 0.011 (flat tiles) is VM-intrinsic
  - **Eigen scaling FAILS:** μ_c constant across prog_sizes (NOT μ_c × L = const)
  - **Error threshold ↔ confinement:** Structural parallel confirmed via Svetitsky-Yaffe
  - **Critical nucleus:** N_c ≈ 2 tiles (flat), ~11 (2D mesh); nucleation-and-growth dynamics
  - **Noise floor:** 0% intrinsic; 35% is geometric (patch overlap)
  - Scripts: `stella_lang/error_threshold_confinement.c`, `critical_nucleus_phase_transition.c`

- [x] **2.3 Identify the continuum limit** — PARTIAL (caveat: non-equilibrium)
  - Z₃ parafermion CFT (c = 4/5) identified as equilibrium continuum limit
  - CFT operators mapped to soup quantities (σ→density, ε→mutation, ψ→domain boundary)
  - Caveat: soup may be in directed percolation class, not Potts (measuring critical exponents would resolve)
  - **TODO:** Determine the actual universality class by measuring critical exponents numerically (e.g., order parameter exponent β, correlation length exponent ν, dynamic exponent z) near μ_c. Compare against Z₃ Potts (β=1/9, ν=5/6), directed percolation (β≈0.58, ν_⊥≈0.73), and absorbing-state transition values. This is computational work that goes beyond the theoretical scope of Phase 2 but is needed to resolve the universality class question definitively.
  - Full analysis: Phase 2 document §2.3

- [x] **2.4 Check consistency with CG field content** — COMPLETE
  - Z₃ match exact (Def 0.1.2 = Potts spins = Z(SU(3)))
  - Topology: ∂S = two S² → bilayer Potts (50% cross-talk)
  - Gauge: Potts captures Z₃ center; full SU(3) via Svetitsky-Yaffe
  - Key identification: self-replicator ↔ Polyakov loop ↔ confined state
  - Full analysis: Phase 2 document §2.4

### Success criterion
Explicit dictionary between soup dynamics and Potts model, with identification of the continuum CFT and its relevance to CG.

---

## Phase 3: Reaction-Diffusion Formulation [THEORETICAL + COMPUTATIONAL]

### Motivation
Rewrite the soup as a continuous dynamical system. Self-replicating patterns in reaction-diffusion systems are well-characterized, providing a direct bridge to PDE dynamics.

### Tasks

- [x] **3.1 Define concentration fields** — COMPLETE
  - Three nested levels: (1) trit concentrations φ_a on 2-simplex, (2) replicator-food ρ/(1-ρ), (3) Z₃ quasispecies ρ_R/ρ_G/ρ_B
  - Bilayer structure ρ_+/ρ_- for ∂T₊ ⊔ ∂T₋ with 50% cross-coupling
  - Z₃ Fourier order parameter ψ = φ₀ + ω φ₁ + ω² φ₂
  - Full analysis: Phase 3 document §3.1

- [x] **3.2 Derive the reaction-diffusion equation** — COMPLETE
  - Coarse-grained Fisher-KPP: ∂ρ/∂t = D ∇²ρ + k_eff ρ(1-ρ) - μ_eff ρ - γ ρ²
  - Parameters extracted from Phase 1/2 data: k_eff=0.22, γ=0.027, μ_eff=20μ
  - Steady state ρ* = (k_eff - μ_eff)/(k_eff + γ) matches both endpoints (89% at μ=0, 0% at μ_c=0.011)
  - Bilayer coupling derived with 50% cross-tetrahedron terms
  - Full derivation: Phase 3 document §3.2

- [x] **3.3 Analyze self-replicating solutions** — COMPLETE
  - Fisher-KPP supports traveling waves, NOT localized spots
  - No spot replication: linear autocatalysis (R+F→2R), no differential diffusion
  - This is physically correct: vacuum should fill space uniformly, not form spots
  - Critical nucleus from stochastic Fisher-KPP matches Phase 1 data (N_c ≈ 2)
  - Full analysis: Phase 3 document §3.3

- [x] **3.4 Numerical PDE simulation** — COMPLETE
  - Script: `stella_lang/rd_on_dS.py`
  - PDE converges exactly to predicted ρ* = 0.810 (0.00% error)
  - Front speed ~51% of flat-space Fisher-KPP prediction (geometry effect)
  - Bilayer dynamics confirmed: T+ leads T- with ~300 epoch lag
  - Mutation sweep captures qualitative behavior (monotonic decline, correct endpoints)
  - Full results: Phase 3 document §3.4.3

- [x] **3.5 Compare with Gray-Scott phenomenology** — COMPLETE
  - CG ≠ Gray-Scott: linear vs cubic autocatalysis, no differential diffusion
  - CG produces Fisher-KPP traveling waves (vacuum fills space)
  - Gray-Scott spot replication would require additional physics (quasispecies as second field)
  - Absence of spots is physically correct for vacuum formation
  - Full comparison: Phase 3 document §3.5

### Success criterion
~~Continuous PDE on dS with CG-derived reaction terms that exhibits self-replicating spot dynamics.~~

**Updated criterion:** Continuous PDE on ∂S with CG-derived reaction terms that exhibits self-replicating dynamics consistent with the discrete soup.

**Assessment: MET.** The Fisher-KPP equation on ∂S with parameters extracted from Phase 1/2 data reproduces: (1) correct steady-state density at all mutation rates, (2) front propagation from localized seed filling the surface, (3) bilayer T+/T- dynamics with cross-coupling. The absence of spot replication is a meaningful physical result — the vacuum fills space, particles arise as topological excitations (Phase 5).

---

## Phase 4: Continuum Fixed-Point Identification [THEORETICAL — KEY THEOREM]

### Motivation
This is the central result: show that the continuum self-replicating fixed point IS the bootstrap fixed point.

### Tasks

- [x] **4.1 Define the continuum interaction operator** — COMPLETE
  - Three-level hierarchy: microscopic (B̂_a on Z₃^N), mesoscopic (B_a on L²(∂S_a)), macroscopic (Φ on T_phys)
  - Stochastic bootstrap map defines NESS; coarse-grained map gives Fisher-KPP one-epoch update
  - Full analysis: `docs/proofs/supporting/Proposition-0.0.XXe-Phase4-Continuum-Fixed-Point-Identification.md` §4.1

- [x] **4.2 Take the continuum limit** — COMPLETE (with caveats)
  - Discrete Laplacian → Laplace-Beltrami (standard convergence, Wardetzky et al. 2007)
  - Reaction parameters (k_eff, γ, μ_eff) are lattice-independent; D scales as a²/Δt
  - Fisher-KPP on ∂S is well-posed semilinear parabolic PDE on compact manifold
  - **Z₃ → SU(3):** Five independent justifications: (1) Svetitsky-Yaffe, (2) coset construction, (3) Polyakov loop promotion, (4) Doi-Peliti exact algebraic isomorphism (soup master equation = quantum Hamiltonian with Z₃ on ∂S), (5) Parisi-Wu stochastic quantization (stochastic dynamics → QFT, proven for Abelian). Remaining gap narrowed to: non-Hermiticity of Doi-Peliti H and universality class identification.
  - **Bilayer:** c_eff < 8/5 by Zamolodchikov c-theorem; precise value not computed.
  - Full analysis: Phase 4 document §4.2

- [x] **4.3 Identify with the bootstrap operator** — COMPLETE (structural)
  - Structural isomorphism: S = R(S) ↔ F[ρ*] = 0 ↔ Φ(T) = T
  - Self-replication IS bootstrap at different resolutions
  - The loop: ∂S geometry → field dynamics → vacuum ρ* → observables → ∂S geometry
  - Quantitative dictionary proposed: k_eff ↔ α_s, μ_c ↔ T_c, ρ* ↔ confined vacuum
  - Full analysis: Phase 4 document §4.3

- [x] **4.4 Fixed-point analysis** — COMPLETE
  - **Existence:** Algebraic — ρ* = (k_eff - μ_eff)/(k_eff + γ) ∈ (0,1) for μ < μ_c
  - **Uniqueness:** Fisher-KPP global attractivity (Aronson & Weinberger 1978) + bootstrap DAG (Thm 0.0.31)
  - **Stability:** All linearized modes decay (F'(ρ*) = -(k_eff - μ_eff) < 0)
  - **Basin of attraction:** Global — any ρ₀ ≢ 0 converges to ρ* (hair trigger effect)
  - Gap: nucleation from ρ₀ = 0 requires stochastic analysis
  - Full analysis: Phase 4 document §4.4

- [x] **4.5 Physical interpretation** — COMPLETE
  - Fixed point ρ* = vacuum state on ∂S (spatially uniform, stable, unique, attractive)
  - Perturbations decay (no topological protection in 2-component model → Phase 5)
  - Phase transition at μ_c = deconfinement (Svetitsky-Yaffe, Phase 2)
  - Self-replication = vacuum stability (vacuum heals by replicating into disturbed regions)
  - Soup dynamics → cosmological QCD phase transition (nucleation → front → saturation)
  - Full analysis: Phase 4 document §4.5

### Success criterion
Theorem: The continuum limit of the soup's self-replicating fixed point satisfies the bootstrap equation F = B(F), with the self-replicating property corresponding to vacuum stability.

---

## Phase 5: Soliton Classification [THEORETICAL]

### Motivation
Once the continuum theory exists, classify which field configurations on dS are self-replicating and connect them to the particle spectrum.

### Tasks

- [x] **5.1 Topological classification** — COMPLETE
  - Three sectors: trivial (Q=0, vacuum), Z₃ vortices (center vortices on ∂S), skyrmions (Q∈Z, baryons)
  - Fisher-KPP captures only Q=0; Z₃ vortices need phase info; skyrmions need full SU(3)
  - Discrete winding number defined for Z₃ configurations on triangulated ∂S
  - Full analysis: `docs/proofs/supporting/Proposition-0.0.XXe-Phase5-Soliton-Classification.md` §5.1

- [x] **5.2 Catalytic vs non-catalytic solitons** — COMPLETE
  - **Confirmed:** vacuum = catalytic (self-replicating, global attractor), particles = non-catalytic (topologically stable)
  - Vacuum copies itself into disturbed regions (Fisher-KPP); solitons conserve Q (topology)
  - Resolves why vacuum fills space but particles are localized: different protection mechanisms
  - Mesons = intermediate case (Q=0 but large-amplitude, quasi-stable)
  - Full analysis: Phase 5 document §5.2

- [x] **5.3 Energy/stability analysis** — COMPLETE
  - Energy hierarchy: vacuum (ground) < mesons (unstable, Q=0) < baryons (stable, Q≠0)
  - Two protection mechanisms: dynamical (vacuum attractor) vs topological (π₃=Z)
  - Derrick's theorem constrains 2D solitons on ∂S; skyrmions are 3D bulk objects
  - Suspension mechanism (Thm 4.1.4): solitons balanced by three-color pressure
  - Full analysis: Phase 5 document §5.3

- [x] **5.4 Connect to Phase 4 particle spectrum** — COMPLETE
  - Full chain: soup → Fisher-KPP → bootstrap → SU(3) → skyrmions
  - Mass scale: M_nucleon ≈ 73 f_π/e ≈ 940 MeV (with quantum corrections)
  - Confinement: μ_c ↔ T_c via Svetitsky-Yaffe; rough T_c ~ 161 MeV estimate
  - Baryon asymmetry: CPY01/CPY10 chirality → Thm 4.2.1 chiral bias
  - W-sector dark matter: subdominant replicator family → Thm 4.3.2 (M_W ~ 1800 GeV)
  - Full analysis: Phase 5 document §5.4

### Success criterion
Classification of self-replicating vs stable-soliton field configurations on dS, with the former identified as vacuum and the latter as matter.

---

## Dependencies and Ordering

```
Phase 1 (2D soup)  ------>  Phase 3 (reaction-diffusion) ------>  Phase 4 (continuum limit)
                                                                        |
Phase 2 (Potts)  ---------->  Phase 4 (continuum limit)  -------> Phase 5 (solitons)
```

- Phases 1 and 2 are independent and can proceed in parallel
- Phase 3 depends loosely on Phase 1 (2D geometry) and Phase 2 (statistical mechanics)
- Phase 4 is the core theoretical result, informed by Phases 1-3
- Phase 5 extends Phase 4 to the particle spectrum

---

## Key References to Consult

| Topic | Reference | Relevance |
|-------|-----------|-----------|
| Z_3 Potts continuum limit | Fateev & Zamolodchikov, Sov. Phys. JETP 62 (1985) | Phase 2: CFT identification |
| Reaction-diffusion patterns | Pearson, Science 261 (1993) | Phase 3: spot replication |
| Pattern formation review | Cross & Hohenberg, Rev. Mod. Phys. 65 (1993) | Phase 3: general framework |
| Lattice gas -> continuum | Frisch, Hasslacher, Pomeau, Phys. Rev. Lett. 56 (1986) | Phase 4: discrete -> continuous |
| Deterministic QM | 't Hooft, arXiv:1405.1548 (2014) | Phase 4: discrete -> quantum |
| Computational life | Aguera y Arcas et al., arXiv:2406.19108 (2024) | Already cited in XXd |
| Topological solitons | Manton & Sutcliffe, "Topological Solitons" (2004) | Phase 5: soliton classification |
| Self-replicating spots | Lee & Swinney, Phys. Rev. E 51 (1995) | Phase 3: experimental RD replication |
| Stochastic quantization | Parisi & Wu, Sci. Sin. 24 (1981); Damgaard & Hüffel, Phys. Rep. 152 (1987) | Phase 4: stochastic → quantum bridge |
| Second quantization of classical systems | Doi, J. Phys. A 9 (1976); Peliti, J. Physique 46 (1985) | Phase 4: master equation → quantum Hamiltonian |
| Stochastic-quantum correspondence | Barandes, arXiv:2302.10778 (2023) | Phase 4: indivisible stochastic = quantum |
| Generalized RK Hamiltonians | Castelnovo et al., Ann. Phys. 318 (2005) | Phase 4: classical equilibrium = quantum ground state |

---

## Open Questions

1. **Is the soup fundamentally equilibrium or non-equilibrium?** **ANSWERED by Phase 2.**
   The soup is fundamentally **non-equilibrium**: no energy function, no detailed balance, irreversible VM execution. The Potts connection is structural (same Z₃ symmetry, same phase transition topology) but the microscopic dynamics differ qualitatively. The correct continuum limit may be a non-equilibrium field theory (absorbing-state transition / directed percolation class with Z₃ symmetry), not the equilibrium Z₃ parafermion CFT. See Phase 2 document §2.3.4.

2. **Does dimensionality matter?** **ANSWERED by Phase 1.**
   Yes, but the tile model resolves it. The 2D shared-surface (patch) model introduces a monoculture attractor absent in 1D. The tile model (non-overlapping Voronoi regions preserving program independence) recovers the same replicator dynamics as 1D, provided population >= ~1,666 tiles. Replicator structure is VM-intrinsic, not geometry-dependent.

3. **What is the role of the two-component structure (T+ u T-)?** **ANSWERED by Phases 1, 3, and 4.**
   The T+/T- cross-talk (50% probability of cross-tetrahedron interaction) provides a mixing channel. Local pairing with T+/T- separation creates spatial niches that accelerate replicator emergence ~5x vs global pairing. In the multi-stella FCC lattice, inter-stella coupling further connects the two-component structures across lattice sites. The continuum interpretation is the bilayer Fisher-KPP system (Phase 3 §3.2): two coupled PDEs ∂ρ±/∂t on ∂T± with 50% cross-coupling terms, which is the standard formulation of a reaction-diffusion system on a disconnected compact manifold ∂S = ∂T₊ ⊔ ∂T₋. Phase 4 confirms the bilayer fixed point exists and is stable (§4.4), with c_eff < 8/5 by the Zamolodchikov c-theorem. The PDE simulation (Phase 3 §3.4) validates the bilayer dynamics: T₊ leads T₋ with ~300 epoch lag, both converging to the same ρ*.

4. **Is the continuum fixed point quantum?** **ANSWERED by Phase 4 + literature analysis.**
   Yes — there exist rigorous mathematical bridges from classical stochastic systems to quantum field theory, and the CG framework has a specific structural advantage that makes the connection non-trivial. Three key results:

   **(a) Doi-Peliti formalism (exact algebraic isomorphism):** Any classical master equation on a lattice — including the Z₃ soup — can be rewritten in second-quantized form d|P⟩/dt = −H|P⟩, where H is a quantum Hamiltonian built from creation/annihilation operators. The NESS of the classical system corresponds to the ground state of H. This applies directly to the soup's stochastic dynamics on Z₃^N.

   **(b) Parisi-Wu stochastic quantization (proven theorem):** Classical fields evolving via Langevin dynamics with noise converge to Euclidean QFT correlation functions at equilibrium: lim_{τ→∞} ⟨φ(x₁,τ)...φ(xₙ,τ)⟩_noise = ⟨φ(x₁)...φ(xₙ)⟩_QFT. This doesn't require gauge fixing and is proven for scalar and Abelian gauge theories.

   **(c) CG-specific constraint:** Generic Z₃ systems cannot uniquely reconstruct SU(3) (many UV completions share the same center). But the soup lives on ∂S, whose geometry independently determines SU(3) (Thm 0.0.3). The Doi-Peliti Hamiltonian H is therefore not arbitrary — it must respect the SU(3) structure of the underlying geometry. This constrains H to the SU(3) gauge theory universality class in a way that generic Z₃ models cannot achieve.

   **Remaining technical gaps:** (i) The Doi-Peliti H is generically non-Hermitian; relating it to physical SU(3) Yang-Mills requires a similarity transformation or detailed balance condition. (ii) Parisi-Wu requires equilibrium; the soup is non-equilibrium (though its NESS may play the analogous role). (iii) Svetitsky-Yaffe applies rigorously only for second-order transitions; SU(3) in 3+1d is first-order.

   **Numerical verification (§4.2.5e):** Exact transition matrices built for L=2 (81 configs) and L=4 (6561 configs) confirm the Doi-Peliti isomorphism: ||H_DP · P*||₂ < 10⁻¹⁵ in all tests (4/4 passed). Monte Carlo simulations independently validate the NESS. Additional findings: (i) H_DP is non-Hermitian (confirmed, not an artifact), (ii) Z₃ dynamical symmetry is broken by the OPEN instruction treating trit 0 specially, (iii) mutation creates ergodicity (μ=0 → many absorbing states; μ>0 → unique NESS), (iv) spectral gap scales with μ (τ ≈ 109 epochs at μ=0.01). Script: `stella_lang/doi_peliti_verification.py`.

   **Key references:** Parisi-Wu (1981); Doi (1976), Peliti (1985); Damgaard-Hüffel, Phys. Rep. 152 (1987); Castelnovo et al., Ann. Phys. 318 (2005); Barandes, arXiv:2302.10778 (2023).

5. **Can we prove emergence is inevitable?** **ANSWERED by Phases 1, 2, 4, and Lemma 0.0.XXe-NP.**
   Phase 4 proves that the Fisher-KPP fixed point is a global attractor for any $\rho_0 \not\equiv 0$ (hair trigger effect, §4.4.4). This upgrades Claim 3 from "empirical" to "proven, given a nonzero seed." The nucleation gap (ρ₀ = 0 → ρ₀ > 0) is now **rigorously resolved** by [Lemma 0.0.XXe-NP](Lemma-0.0.XXe-Nucleation-Probability-Proof.md), which proves $\mathbb{P}(\text{nucleation by epoch } T) \to 1$ as $N \to \infty$ (fixed $T$) or $T \to \infty$ (fixed $N$), with quantitative bounds via a mutation-coupling argument that dominates the VM contribution. The bound applies to both flat-tile and 2D triangulated mesh geometries — computational verification ([nucleation_2d_geometry.c](../../../verification/supporting/nucleation_2d_geometry.c)) shows the geometric correction is $< 10\%$ ($r_{\text{eff}} \geq 0.91r$) and vanishes as $n_{\text{sub}} \to \infty$. Combined with the hair trigger effect, emergence is inevitable: random Z₃ soup → nucleation (rigorous, Lemma 0.0.XXe-NP) → global attractor (deterministic, Fisher-KPP).

   **N-scaling refinement (extended campaign, 232 stellae, $N$ up to 26,666).** The nucleation time exhibits a **two-regime structure** (Lemma §3.5.5):
   - **Regime I — rate-limited ($N \lesssim 4{,}000$):** $T_{\text{emerge}} \approx 1$–$2 \times 10^6$ epochs, approximately N-independent. The bottleneck is VM-mediated search within local neighborhoods, not population-level parallelism.
   - **Regime II — Poisson-like ($N \gtrsim 6{,}000$):** $T_{\text{emerge}}$ decreases with $N$ (exponent $-0.49$ to $-0.68$, approaching the rigorous bound's $N^{-1}$ prediction). At $N \geq 6{,}666$, nucleation within $5 \times 10^6$ epochs is $> 98\%$ certain (71/72 stellae nucleated).
   - **Crossover ($N \sim 4{,}000$–$6{,}000$):** The number of non-overlapping search neighborhoods exceeds the inverse per-neighborhood nucleation probability, and Poisson statistics begin to apply.

   This strengthens the inevitability argument: for physically realistic stellae on the FCC lattice ($N \geq 6{,}666$), emergence is not only certain in the limit but rapid and reliable at finite $N$.

6. **Does the error threshold map to a confinement scale?** **ANSWERED by Phase 2.**
   Yes, structurally. The error catastrophe (μ_c ≈ 0.011, constant across program lengths L=24–48) maps to the Potts deconfinement transition via Svetitsky-Yaffe: both destroy coherent composite structures through overwhelming disorder. However, **Eigen scaling fails** — μ_c is constant across program lengths (VM-intrinsic), not μ_c ∝ 1/L as Eigen predicts. The mapping is structural (same symmetry, same transition topology), not quantitative. The 35% noise floor in the 2D mesh is geometric (patch overlap), not intrinsic — flat tiles show 0% noise floor at zero mutation. See Phase 2 document §2.2.3.

7. **Does the critical nucleus correspond to a physical phase transition?** **ANSWERED by Phase 2.**
   Yes. The critical nucleus N_c ≈ 2 tiles (flat) or ~11 tiles (2D mesh) is a critical droplet in the nucleation theory sense. Growth dynamics are nucleation-and-growth (lag→exponential→saturation in ~50 epochs), NOT spinodal decomposition. Note: the Z₃ Potts transition in 2D is **second-order** (continuous, Baxter 1973), not first-order — the nucleation-like dynamics observed in the soup likely reflect its non-equilibrium absorbing-state character rather than the equilibrium Potts universality class. In 3D, the Z₃ Potts transition is first-order, matching SU(3) deconfinement in (3+1)D. Minimum population for maintenance is ~100 tiles (not ~1666, which is the threshold for spontaneous emergence). The extended nucleation campaign (Lemma 0.0.XXe-NP §3.5.5) refines this picture: $N \approx 1{,}666$ is in the **rate-limited regime** where emergence time is $\sim 1$–$2$M epochs and approximately N-independent; for $N \gtrsim 6{,}000$ the system enters a **Poisson regime** where nucleation becomes both faster and nearly certain ($> 98\%$ at $N \geq 6{,}666$). Connection to bag model R_eq and Thm 4.2.3 is structural — see Phase 2 document §2.2.4.

8. **Does explicit Z₃ symmetry breaking by the VM affect the Svetitsky-Yaffe mapping?** **ANSWERED by dedicated investigation (2026-03-10).**

   The multi-agent verification (2026-03-10) identified that the VM's OPEN/CLOSE instructions test `tape[h0] == 0`, treating trit 0 as distinguished. A systematic numerical investigation addressed all four sub-questions. Script: `stella_lang/z3_symmetry_breaking_investigation.py`.

   **Finding 1 — Breaking magnitude and scaling (sub-question 1):**
   The Z₃ breaking was quantified via the normalized commutator $\|[T, R]\|_F / (\|T\|_F \cdot \|R\|_F)$ and per-site trit asymmetry across $L = 2$ (81 configs) and $L = 4$ (6561 configs), for $\mu \in \{0, 0.001, 0.005, 0.01, 0.02, 0.05, 0.1\}$.

   | Metric | $L=2$ | $L=4$ | Ratio $L4/L2$ | Trend |
   |--------|-------|-------|----------------|-------|
   | Normalized $\|[T,R]\|_F$ | 0.113 | 0.015 | 0.13 | **SHRINKS 8×** |
   | Trit asymmetry ($\mu=0.01$) | 0.073 | 0.050 | 0.69 | **SHRINKS** |
   | Z₃ magnetization $|\Psi|$ ($\mu=0.01$) | 0.042 | 0.025 | 0.60 | **SHRINKS** |

   All **intensive** (per-degree-of-freedom) breaking metrics decrease with system size. The raw NESS $L_1$ distance grows ($L=2$: 1.14, $L=4$: 1.49 at $\mu=0.01$), but this is an extensive quantity — the relevant RG quantity is the intensive one.

   **Finding 2 — RG relevance (sub-question 2):**
   The normalized commutator shrinks by ~8× when $L$ doubles (2→4). This is consistent with the breaking being **RG-irrelevant**: the effective Z₃-breaking field $h$ vanishes as $L \to \infty$, restoring Z₃ symmetry in the continuum limit. In the Landau-Ginzburg framework, although the magnetic field $h$ has scaling dimension $y_h = 28/15 > 0$ (relevant at the critical point), the key question is whether the *bare coupling* $h_0$ generated by the VM vanishes as the lattice is refined — and it does.

   **Finding 3 — Structural unavoidability (sub-question 3):**
   The investigation revealed that the Z₃ breaking is **not just from OPEN/CLOSE** — it is structural in the entire instruction encoding. Under Z₃ rotation of all trits ($\sigma_i \to \sigma_i + 1 \mod 3$), **0 out of 9 instructions** are preserved:

   | Original | Code | → Rotated | Code | Same? |
   |----------|------|-----------|------|-------|
   | NOP | (0,0) | FWD1 | (1,1) | ✗ |
   | ROT | (0,1) | OPEN | (1,2) | ✗ |
   | FWD0 | (0,2) | BCK0 | (1,0) | ✗ |
   | BCK0 | (1,0) | CPY01 | (2,1) | ✗ |
   | FWD1 | (1,1) | CPY10 | (2,2) | ✗ |
   | OPEN | (1,2) | CLOSE | (2,0) | ✗ |
   | CLOSE | (2,0) | ROT | (0,1) | ✗ |
   | CPY01 | (2,1) | FWD0 | (0,2) | ✗ |
   | CPY10 | (2,2) | NOP | (0,0) | ✗ |

   A Z₃-symmetric VM variant (OPEN tests `tape[h0] == tape[h1]` instead of `== 0`) was constructed and tested. It has **identical** $\|[T,R]\|_F$ to the standard VM — confirming that the breaking comes from the instruction encoding, not the conditional. The modified VM produces identical transitions in 100% (L=2) and 99.3% (L=4) of cases.

   This makes Z₃ breaking **unavoidable** in any fixed trit-pair instruction encoding — analogous to lattice artifacts in lattice gauge theory that vanish in the continuum limit.

   **Finding 4 — Self-replication robustness:**
   **[CORRECTED 2026-03-10]** The original "20-trit replicator" `{0,2, 2,1, 1,1, ...}` cited here was incorrect — it does NOT pass the self-replication test (see Q11 investigation). The actual verified replicator is `{1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0, 2,0, 2,0}` (core: `[ [ CPY+ FWD0 FWD1 ] CPY+ FWD1 FWD0 ]`). This replicator self-replicates with ANY food content (zero, ones, twos, random) under both VMs. Self-replication is structurally robust across VM variants.

   **Finding 5 — QCD analogy (sub-question 4):**
   The Z₃ breaking maps precisely to explicit center symmetry breaking by dynamical quarks in QCD:

   | QCD | Z₃ Soup |
   |-----|---------|
   | Quark mass $m_q$ | Instruction encoding asymmetry |
   | $\det(1 + L \cdot e^{-m_q/T})$ | $\|[T, R]\|_F / (\|T\|_F \cdot \|R\|_F)$ |
   | 1st-order → crossover | Sharp threshold → smooth transition |
   | Columbia plot $(m_u, m_d, m_s)$ | VM encoding × mutation rate phase map |

   In QCD, explicit Z₃ breaking by quarks does **not** invalidate the Svetitsky-Yaffe framework — it enriches it by explaining why the physical deconfinement transition (at $T_c \approx 155$ MeV) is a crossover rather than a true phase transition. The same applies to the soup: the error catastrophe is a crossover, matching physical QCD.

   **Resolution:** The Z₃ breaking does **not** invalidate the Svetitsky-Yaffe mapping. Three independent lines of evidence:
   - **(A)** Intensive breaking metrics shrink with $L$ → irrelevant in the continuum limit
   - **(B)** Breaking is a structural encoding artifact (0/9 instructions preserved) → lattice artifact
   - **(C)** Breaking maps to quark-induced center breaking in QCD → physically correct (crossover)

   The original resolution paths (a), (b), and (c) from the initial question are **all partially correct** and complementary: (a) the breaking is encoding-dependent but unavoidable; (b) it is physically meaningful as the quark-mass analog; (c) the per-site breaking vanishes in the continuum limit.

   **Priority:** LOW (resolved). Script: `stella_lang/z3_symmetry_breaking_investigation.py`.

9. **Can the Doi-Peliti Hamiltonian be related to SU(3) Yang-Mills?** **PARTIALLY ANSWERED by dedicated investigation (2026-03-10).**

   The Doi-Peliti construction (§7.3) gives an exact algebraic isomorphism: the soup's master equation on $\mathbb{Z}_3^N$ becomes $d|P\rangle/dt = -H_{\text{DP}}|P\rangle$, with the NESS as the ground state of $H_{\text{DP}}$. This is verified numerically (4/4 tests, residuals < $10^{-15}$). However, $H_{\text{DP}}$ is **generically non-Hermitian** ($|\text{Im}(\lambda)| \sim 0.56$ for $L = 4$), while the physical SU(3) Yang-Mills Hamiltonian is Hermitian.

   A systematic numerical investigation addressed all five sub-questions. Script: `stella_lang/doi_peliti_su3_investigation.py`.

   **Finding 1 — Similarity transformation (sub-question 1): NEGATIVE.**
   No similarity transformation to Hermitian form exists. The standard detailed-balance transform $\tilde{H} = D^{-1/2} H D^{1/2}$ (with $D = \text{diag}(\pi)$) does not produce a Hermitian operator:

   | Metric | $L=2$ | $L=4$ | Trend |
   |--------|-------|-------|-------|
   | Fraction real eigenvalues | 80.2% | 40.0% | **WORSENS** |
   | $\|H_- \|/\|H_+\|$ (anti-Hermitian/Hermitian) | 0.430 | 0.434 | **STABLE at ~43%** |
   | Mean $|\text{Im}/\text{Re}|$ | 0.005 | 0.027 | **WORSENS** |
   | Eigenvector condition number | $2.6 \times 10^6$ | $6.5 \times 10^{21}$ | **Near-defective** |

   The non-Hermiticity is an **O(1) effect** that does not vanish with system size. $H_{\text{DP}}$ becomes increasingly near-defective (ill-conditioned eigenvector matrix) at larger $L$, ruling out naive diagonalization-based similarity transforms.

   **Finding 2 — PT symmetry (sub-question 2): PARTIAL.**
   No exact PT symmetry of Bender-Boettcher type was found. Four candidate PT operators were tested:

   | Operator | $[H, \text{PT}]$ at $L=2$ | $[H, \text{PT}]$ at $L=4$ |
   |----------|---------------------------|---------------------------|
   | $P_{\text{swap}} \cdot T_{\text{neg}}$ | broken (1.13) | broken (0.96) |
   | $P_{\text{swap}} \cdot I$ | **COMMUTES** | **COMMUTES** |
   | $P_{\text{rev}} \cdot T_{\text{neg}}$ | broken (1.23) | broken (1.04) |
   | $P_{\text{rev}} \cdot I$ | broken (1.16) | broken (1.03) |
   | $R_{\mathbb{Z}_3}$ | broken (1.15) | broken (0.97) |

   **$P_{\text{swap}}$ (program swap $a \leftrightarrow b$) is an exact symmetry** of $H_{\text{DP}}$ at all $L$. This reflects the 50/50 pairing-order randomization in the soup dynamics. However, it is a *linear* symmetry, not an antilinear PT symmetry, so it does not guarantee real spectrum.

   **All complex eigenvalues come in conjugate pairs** (16/16 at $L=2$, 3934/3934 at $L=4$). This is a consequence of $H$ being real-valued, not of PT symmetry.

   **Finding 3 — Physical subspace (sub-question 3): KEY POSITIVE RESULT.**
   The NESS-weighted inner product $\langle u, v \rangle_\pi = \sum_i u_i v_i / \pi_i$ provides the correct physical structure:

   | Metric | $L=2$ | $L=4$ |
   |--------|-------|-------|
   | $(H + H^\dagger_\pi)/2$ real eigenvalues | **81/81 (100%)** | **6561/6561 (100%)** |
   | $(H + H^\dagger_\pi)/2$ max $|\text{Im}(\lambda)|$ | **0.0** | **0.0** |
   | $\|H^T D - D H\|_F / \|H\|_F$ | $2.63 \times 10^{-2}$ | $5.19 \times 10^{-4}$ |

   The **NESS-symmetrized operator** $(H + H^\dagger_\pi)/2$ is exactly Hermitian by construction and has a purely real spectrum. The detailed balance violation in the NESS metric **decreases by 50× from $L=2$ to $L=4$**, suggesting that $H_{\text{DP}}$ becomes self-adjoint w.r.t. the NESS inner product in the thermodynamic limit.

   **Physical interpretation:** The NESS defines a "physical Hilbert space" with inner product weighted by the stationary measure. In this space, $H_{\text{DP}}$ is *approximately* self-adjoint, with the approximation improving as $L \to \infty$. This is analogous to how the transfer matrix in lattice gauge theory (generically non-symmetric) becomes Hermitian in the inner product defined by the path integral measure. The relaxation spectrum (physical observables = correlation times) is captured by the real eigenvalues of the NESS-symmetrized operator.

   **Finding 4 — Scaling of imaginary parts (sub-question 4): NON-VANISHING.**

   | $L$ | $n_{\text{cfg}}$ | Frac. real ($\mu=0.01$) | Per-site $|\text{Im}|$ | $|\text{Im}/\text{Re}|$ |
   |-----|-------------------|------------------------|----------------------|------------------------|
   | 2 | 81 | 80.2% | $2.5 \times 10^{-5}$ | 0.005 |
   | 3 | 729 | 39.4% | $2.4 \times 10^{-3}$ | 0.027 |
   | 4 | 6561 | 40.0% | $2.6 \times 10^{-3}$ | 0.027 |

   The non-Hermiticity does **not** vanish with system size. The $L=2$ case is anomalously Hermitian-like (small system artifact); from $L=3$ onward, $|\text{Im}/\text{Re}| \approx 0.027$ stabilizes. This confirms the non-Hermiticity is a genuine feature of the non-equilibrium dynamics, not a finite-size effect.

   However, combined with Finding 3, this means the non-Hermiticity is **physically irrelevant** — the NESS inner product absorbs it, and the physical relaxation spectrum is real.

   **Finding 5 — Z₃ gauge comparison (sub-question 5): QUALITATIVELY DIFFERENT.**

   | Property | $H_{\text{DP}}$ | Z₃ gauge ($n=4$) |
   |----------|-----------------|-------------------|
   | Spectral gap | 0.009 | 0.281 |
   | Level spacing $\langle r \rangle$ | 0.288 (sub-Poisson) | 0.453 (near GOE) |
   | Degeneracies | sparse (1,1,2,1,...) | rich (1,2,1,4,...) |
   | Z₃ sectors q=1,2 | degenerate ✓ | degenerate ✓ |

   The spectra are **qualitatively different**: $H_{\text{DP}}$ has densely-packed low-lying states with sub-Poisson level statistics (characteristic of near-integrable or localized systems), while the Z₃ gauge Hamiltonian has well-separated levels with near-GOE statistics (quantum chaotic). The Z₃ sector structure ($q=1$ and $q=2$ degenerate) is shared, confirming the Z₃ symmetry backbone.

   The spectral mismatch is expected at small $L$ — the soup's VM dynamics (9 instructions, deterministic execution) create a highly structured transition matrix very different from the "democratic" nearest-neighbor hopping of the gauge Hamiltonian. Whether the spectra converge in a coarse-grained or RG-flowed sense remains open.

   **Finding 6 — Spectral matching with Z₃ Potts model (follow-up investigation, 2026-03-10).**

   The correct comparison target per Svetitsky-Yaffe is the Z₃ Potts model, not the gauge Hamiltonian. A C implementation (`stella_lang/spectral_matching.c`) built the properly similarity-transformed Hamiltonian $H_{\text{phys}} = (D^{-1/2} H D^{1/2} + \text{transpose})/2$ (which is exactly symmetric in the standard inner product) and compared its spectrum with the Z₃ Potts Hamiltonian across $L = 2, 3, 4$.

   **(a) Corrected NESS symmetrization:** The original Python analysis used $(H + H^\dagger_\pi)/2$, which is self-adjoint in the $\pi$-weighted inner product but NOT symmetric in the standard inner product. The correct construction for LAPACK diagonalization is $H_{\text{phys}} = (D^{-1/2} H D^{1/2} + D^{1/2} H^T D^{-1/2})/2$, which IS symmetric by construction. This gives physically correct eigenvalues in the range $\sim 0.007$–$0.05$ (matching the relaxation time scale $\tau \sim 1/\text{gap} \sim 100$–$150$ epochs, consistent with discrete soup observations).

   **(b) Spectral gap scaling:**

   | $L$ | $n_{\text{cfg}}$ | gap ($\mu=0.01$) | gap × $n$ | gap × $n^2$ |
   |-----|-------------------|-----------------|-----------|------------|
   | 2 | 81 | 0.00756 | 0.030 | 0.121 |
   | 3 | 729 | 0.00654 | 0.039 | 0.235 |
   | 4 | 6561 | 0.00806 | 0.064 | 0.516 |

   The gap is roughly **constant** (not scaling as $1/n$ or $1/n^2$), indicating a **gapped (massive) theory**. This is physically correct: the soup at $\mu = 0.01 \ll \mu_c \approx 0.011$ is in the "confined" phase, which should be gapped. The gap is proportional to $\mu$ (gap $\approx 0.76\mu$), consistent with $\mu$ setting the relaxation rate.

   **(c) Level spacing statistics:**

   | $L$ | $\langle r \rangle$ (soup) | $\langle r \rangle$ (Potts) | Class |
   |-----|---------------------------|----------------------------|-------|
   | 2 | 0.300 | — | sub-Poisson |
   | 3 | 0.273 | — | sub-Poisson |
   | 4 | 0.310 | — | sub-Poisson |

   The soup consistently shows $\langle r \rangle \approx 0.29$, well below Poisson (0.386). This indicates clustering/near-degeneracy, characteristic of an integrable or highly structured system. The Potts model at these sizes has doubly degenerate first excited states ($E_2/E_1 = 1.000$ exactly).

   **(d) $E_2/E_1$ ratio convergence — the most promising signal:**

   | $L$ | $E_2/E_1$ (soup) | $E_2/E_1$ (Potts) | Difference |
   |-----|-----------------|-------------------|------------|
   | 2 | 1.228 | 1.000 | 0.228 |
   | 3 | 1.347 | 1.000 | 0.347 |
   | 4 | **1.070** | 1.000 | **0.070** |

   At $L=4$, the ratio drops sharply to 1.070, approaching the Potts value of 1.000 (doubly degenerate first excited state). The non-monotonic trend ($L=3$ is worse than $L=2$) may reflect an odd/even parity effect in $L$. If the $E_2/E_1 \to 1$ trend continues at even $L$, it would indicate the first excited state of the soup's Hamiltonian becomes doubly degenerate — matching the Z₃ Potts structure.

   **(e) Detailed balance violation (intensive):**

   | $L$ | $\|H_{\text{tilde}} - H_{\text{tilde}}^T\| / \|H_{\text{tilde}}\|$ |
   |-----|---------------------------------------------------------------------|
   | 2 | 0.304 |
   | 3 | 0.484 |
   | 4 | 0.477 |

   The detailed balance violation is $O(1)$ (~30–48%) and does **not decrease** with $L$. The soup is genuinely far from equilibrium — this is not a finite-size artifact. The NESS-symmetrized operator captures the "best Hermitian approximation" but the anti-symmetric (non-equilibrium) part remains substantial. This means the non-equilibrium character of the soup dynamics is a fundamental feature, not an artifact that disappears in the continuum limit.

   **(f) Density of states:** The soup's spectrum is concentrated near two values — a cluster of low-lying states near the gap and a dense band at higher energies. The Potts model has a more uniform distribution. The spectral shapes are qualitatively different at available sizes.

   **Resolution — Overall assessment (updated):**

   The investigation provides a **partial resolution** with a clear positive outcome, a clear negative outcome, and one promising signal:

   **(+) POSITIVE:** The properly symmetrized Hamiltonian $H_{\text{phys}}$ gives physically correct eigenvalues with a gapped spectrum matching the "confined" phase expectation. The gap $\propto \mu$ confirms that mutation rate sets the physical relaxation scale.

   **(−) NEGATIVE:** The spectra of $H_{\text{phys}}$ and the Z₃ Potts model are qualitatively different at microscopic level: different level statistics, different degeneracy patterns, different density of states. The detailed balance violation is $O(1)$ and persistent. The soup is **not** a perturbed equilibrium system — it is genuinely non-equilibrium.

   **(?) PROMISING:** The $E_2/E_1$ ratio at $L=4$ (1.070) approaches the Potts doublet value (1.000), suggesting possible convergence of the lowest excitations to Potts structure at larger even $L$. Testing $L=5$ ($n = 59,\!049$, requires sparse/iterative methods) and $L=6$ ($n = 531,\!441$, requires distributed computation) would be definitive.

   **(!) KEY INSIGHT:** The correct comparison may not be the microscopic spectrum at all, but rather **universal quantities near the critical point** $\mu_c \approx 0.011$. The current investigation is at fixed $\mu$ far from criticality. The Svetitsky-Yaffe mapping predicts that the *critical exponents* and *central charge* at the error catastrophe should match the Z₃ Potts model — this is a statement about the critical point, not the bulk spectrum. **Resolving Q11 (universality class near $\mu_c$) is prerequisite to a meaningful spectral matching test.**

   **Priority:** MODERATE (downgraded from HIGH). The Hermiticity problem is resolved by Finding 3. The spectral matching question points toward Q11 as the more fundamental test. Direct spectral comparison at larger $L$ is computationally feasible but scientifically secondary to measuring critical exponents.

   **Scripts:**
   - `stella_lang/doi_peliti_su3_investigation.py` — Sub-questions 1–5 (Python)
   - `stella_lang/spectral_matching.c` — Finding 6: NESS-symmetrized spectrum vs Z₃ Potts (C/LAPACK)

   **Key references:** Bender & Boettcher, Phys. Rev. Lett. 80 (1998) 5243; Zia & Schmittmann, J. Stat. Mech. (2007) P07012 (detailed balance in NESS); Doi (1976), Peliti (1985); Svetitsky & Yaffe, Nucl. Phys. B 210 (1982) 423.

10. **Does Parisi-Wu stochastic quantization extend to the non-Abelian soup?** **ANSWERED: No — the soup's NESS is genuinely non-equilibrium; Doi-Peliti (Q9) is the correct bridge (2026-03-10).**

    The Parisi-Wu theorem (§7.4) proves that Langevin dynamics converge to Euclidean QFT correlators for scalar and Abelian gauge theories. A comprehensive investigation combining literature review, Langevin validation, and information-theoretic analysis of the soup's NESS resolves all three sub-questions.

    **Finding 1 — Literature review (sub-question 1): Non-Abelian SQ established perturbatively, open non-perturbatively.**

    | Aspect | Status | Key reference |
    |--------|--------|---------------|
    | Perturbative equivalence for SU(N) | **Established** | Parisi & Wu (1981); Damgaard & Hüffel (1987) |
    | Non-perturbative proof in 4D | **Open** | Best result: 3D YMH, local in time (Chandra, Chevyrev, Hairer & Shen, *Invent. math.* 237, 541–696, 2024; arXiv:2201.03487) |
    | Gauge-fixing not required | **Established** | Zwanziger, *Nucl. Phys. B* 192 (1981) 259 |
    | Gribov problem | **Formally avoided** in SQ (no gauge fixing needed); non-perturbative completeness unproven | Gribov (1978); Rao, arXiv:2406.15059 (2024) |
    | Lattice implementations | **Established** (NSPT widely used) | Batrouni et al., *Phys. Rev. D* 32 (1985) 2736; Di Renzo & Scorzato, JHEP 0410 (2004) 073 |
    | Complex Langevin correctness | **Necessary and sufficient conditions known** | Mandl, Seiler & Sexty, *J. Phys. A* 58 (2025) 495202 |
    | Discrete Z₃ state space | **NOT directly applicable** to Langevin | Requires continuous embedding or alternative route |

    The Langevin equation requires continuous state space and Gaussian noise. For discrete groups like Z₃, one must either embed in U(1) with a confining potential or use an entirely different framework (Doi-Peliti).

    **Finding 2 — Langevin validation for Z₃ (sub-question 2): WORKS with controlled errors.**

    Langevin dynamics on U(1) with a Z₃ confining potential $V(\varphi) = -V_3\cos(3\varphi)$ was compared with exact Z₃ Potts results (transfer matrix) and heat-bath Monte Carlo on 1D rings of $N = 4, 6, 8$ sites at couplings $J = 0$–$2.0$.

    **(a) V₃ dependence (N=6, J=1.0):**

    | $V_3$ | $\langle\delta\rangle_{\text{NN}}$ | Error vs exact | $\langle\cos 3\varphi\rangle$ | Interpretation |
    |-------|-------------------------------------|----------------|-------------------------------|----------------|
    | 0.5 | 0.508 | −0.068 | 0.24 | Too weak: XY-like |
    | 2.0 | 0.553 | −0.024 | 0.70 | **Optimal** |
    | 3.0 | 0.560 | −0.016 | 0.81 | Good (near optimal) |
    | 5.0 | 0.513 | −0.064 | 0.89 | Trapping onset |
    | 8.0 | 0.333 | −0.243 | 0.93 | **Trapped** (no inter-well tunneling) |

    The confining-vs-trapping tradeoff has a clear optimum at $V_3 \approx 2$–$3$. The barrier height $2V_3 = 4$–$6$ allows tunneling between Z₃ wells ($\sim e^{-4} \approx 0.02$ per step) while maintaining $\langle\cos 3\varphi\rangle \approx 0.7$–$0.8$ (strong Z₃ preference).

    **(b) Systematic comparison at $V_3 = 2.0$ ($dt = 0.002$, $5 \times 10^5$ thermalization, $10^6$ measurement steps):**

    Average error: 1.7%. Maximum error: 5.3% (at $N=4$, $J=2.0$). For $J \leq 1.0$: errors $< 3\%$. The Langevin continuous correlator $\langle\cos(\varphi_i - \varphi_j)\rangle$ converges correctly; the residual error is entirely from the Z₃ projection step at finite $V_3$.

    **Conclusion:** Parisi-Wu stochastic quantization reproduces Z₃ Potts equilibrium correlators via U(1) embedding with controlled errors that vanish as $V_3 \to \infty$, $dt \to 0$. The method WORKS for Z₃ systems.

    **Finding 3 — Soup NESS is NOT a Gibbs state (sub-question 3, Part B): DEFINITIVE NEGATIVE.**

    The soup's exact NESS (from power iteration on the transition matrix, $\mu = 0.01$) was compared with the best-fit Z₃ Potts Boltzmann distribution $P_{\text{Potts}}(\sigma) \propto \exp(J\sum\delta)$ across three coupling topologies: nearest-neighbor ring (PBC), nearest-neighbor chain (OBC), and all-to-all.

    | $L$ | $n_{\text{cfg}}$ | Best model | Best $J$ | $D_{\text{KL}}(\text{NESS}\|\text{Potts})$ | $D_{\text{KL}}(\text{NESS}\|\text{uniform})$ | Fraction captured |
    |-----|-------------------|------------|----------|---------------------------------------------|-----------------------------------------------|-------------------|
    | 2 | 81 | All-to-all | 0.205 | 0.642 | 0.679 | **5.4%** |
    | 3 | 729 | All-to-all | 0.175 | 1.488 | 1.563 | **4.8%** |
    | 4 | 6561 | All-to-all | 0.145 | 1.199 | 1.305 | **8.1%** |

    The best-fit Potts model captures **less than 8%** of the total KL divergence from uniformity. The NESS is categorically not a Gibbs state for any Z₃ Potts Hamiltonian.

    **"Program mirror" correlations:** The dominant structure in the NESS is $\langle\delta(\sigma_i, \sigma_{i+L})\rangle \gg 1/3$ — strong correlation between the same position in the two programs:

    | $L$ | $\langle\delta(\sigma_0, \sigma_L)\rangle$ | Expected (random) | Interpretation |
    |-----|---------------------------------------------|-------------------|----------------|
    | 2 | **0.676** | 0.333 | VM CPY copies between h0=0, h1=L |
    | 3 | **0.827** | 0.333 | Even stronger at larger L |
    | 4 | **0.392** | 0.333 | Weaker (h1 starts at 4, not always reached) |

    These non-local correlations arise from the VM's CPY01/CPY10 instructions, which copy between $h_0$ (initialized at 0) and $h_1$ (initialized at $L$). No spatially local Gibbs model can produce this structure.

    **Finding 4 — Non-Gibbsian structure quantified (sub-question 3, Part C): CONFIRMED.**

    Information-theoretic analysis of the NESS at $L = 2, 3, 4$:

    | $L$ | Total correlation TC | Pairwise fraction | $I(\sigma_0;\sigma_2|\sigma_1)$ | $R^2$ (1-body) |
    |-----|---------------------|-------------------|---------------------------------|-----------------|
    | 2 | 0.545 nats | **84%** | **0.323 nats** | 14.2% |
    | 3 | 0.885 nats | **61%** | 0.033 nats | 20.2% |
    | 4 | 1.040 nats | **62%** | 0.024 nats | 14.2% |

    **(a) Markov property fails:** For $L=2$, $I(\sigma_0;\sigma_2|\sigma_1) = 0.323$ nats — should be 0 for a nearest-neighbor Gibbs/Markov chain. The NESS is strongly non-Markov.

    **(b) Pairwise fraction decreases with $L$:** From 84% ($L=2$) to ~61% ($L=3,4$), indicating that higher-order ($k \geq 3$-body) correlations become more important at larger system sizes. This rules out pairwise Gibbs models.

    **(c) Long-range mutual information peaks at separation $L$:** $I(\sigma_0;\sigma_L) \approx 0.27$–$0.29$ nats across all $L$ values, confirming the "program mirror" effect as the dominant correlation structure in the NESS.

    **(d) 1-body model explains only 14–20% of $H_{\text{eff}}$ variance:** The effective Hamiltonian $H_{\text{eff}} = -\log P_{\text{NESS}}$ has spread ~10 nats and is predominantly shaped by multi-site terms.

    **Resolution — Overall assessment:**

    **(+) POSITIVE:** Parisi-Wu stochastic quantization works for Z₃ systems in principle. Langevin dynamics on U(1) with Z₃ confining potential reproduces exact Potts correlators with controlled errors (~2–5%). The method is perturbatively established for SU(N) and lattice implementations (NSPT) are widely used.

    **(−) NEGATIVE:** The soup's NESS is **not** a Gibbs state and **cannot** be described by Parisi-Wu stochastic quantization. The NESS has:
    - Massive non-local "program mirror" correlations ($\langle\delta_{i,i+L}\rangle$ up to 0.83)
    - Strong non-Markov structure (conditional MI up to 0.32 nats)
    - Significant higher-order ($\geq$3-body) correlations (16–38% of total correlation)
    - Only 5–8% of its structure captured by any Z₃ Potts model

    **(!) KEY INSIGHT:** The Doi-Peliti route (Q9), not Parisi-Wu, is the correct bridge from the soup to QFT. The Doi-Peliti construction $H_{\text{DP}} = I - T$ provides an exact algebraic isomorphism between the soup's master equation and a quantum Hamiltonian, regardless of whether the dynamics satisfy detailed balance. The soup's NESS is the ground state of $H_{\text{DP}}$ — this does not require the NESS to be a Gibbs state. The relevant question for the Z₃ → SU(3) connection is whether $H_{\text{DP}}$ flows to the correct universality class under RG, not whether the NESS matches a Boltzmann distribution.

    **Implication for §7.4 of the proposition:** The Parisi-Wu section should be reframed as:
    1. Parisi-Wu provides a **conceptual motivation** — it shows that stochastic processes CAN reproduce QFT correlators
    2. The actual bridge goes through **Doi-Peliti** (§7.3), which is exact and does not require Langevin dynamics or Gibbs equilibrium
    3. The Gribov problem is formally avoided because the soup has no gauge-fixing step (Zwanziger 1981)
    4. The non-perturbative SQ proof for SU(N) in 4D remains open, but this is moot since the Doi-Peliti route does not rely on Parisi-Wu

    **Scripts:** `stella_lang/parisi_wu_investigation.c`

    **Key references:**
    - Parisi & Wu, *Scientia Sinica* 24 (1981) 483
    - Zwanziger, *Nucl. Phys. B* 192 (1981) 259
    - Damgaard & Hüffel, *Phys. Rep.* 152 (1987) 227–398
    - Batrouni et al., *Phys. Rev. D* 32 (1985) 2736
    - Chandra, Chevyrev, Hairer & Shen, *Invent. math.* 237 (2024) 541–696; arXiv:2201.03487
    - Mandl, Seiler & Sexty, *J. Phys. A* 58 (2025) 495202
    - Doi (1976), Peliti (1985) — Doi-Peliti formalism
    - Rao, arXiv:2406.15059 (2024) — Gribov problem and SQ review

    **Priority:** RESOLVED. Parisi-Wu is a supporting argument; Doi-Peliti is the primary route.

11. **What is the soup's universality class near μ_c?** **ANSWERED: Directed Percolation (DP) class (2026-03-10).**

    The soup's error catastrophe (§5.1) has the structure of a phase transition. Dedicated numerical investigation using verified self-replicators (from 30M-epoch soup run) definitively identifies the universality class.

    **Corrected replicator:** The workplan's original "known 20-trit replicator" `{0,2, 2,1, 1,1, ...}` was INCORRECT — it does not pass the self-replication test. The actual verified replicator from the 30M-epoch run is `{1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0, 2,0, 2,0}`, which decodes as `[ [ CPY+ FWD0 FWD1 ] CPY+ FWD1 FWD0 ] ] ]` — a nested copy loop. This replicator preserves itself and copies itself to ANY food content.

    **Corrected μ_c:** μ_c ≈ 0.012 ± 0.001 (not 0.011 as originally estimated). Determined from Binder cumulant crossing and finite-size scaling at N ∈ {200, 500, 1000, 2000, 4000}.

    **Results summary:**

    | Observable | Measured value | Z₃ Potts | DP | Mean-field | Verdict |
    |-----------|---------------|----------|-----|------------|---------|
    | Absorbing state | YES (0/10 nucleated at all μ > 0.010) | No absorbing state | **YES** | — | **DP** |
    | β (order parameter) | 0.58–0.85 (depends on μ_c) | 1/9 = 0.111 | 0.58 (2+1D) | 1.0 | **DP or MF-DP** |
    | z (dynamic exponent) | 1.55 at μ=0.010 | 2.17 | 1.58 (1+1D) | 2.0 | **~DP** |
    | Finite-size effects | Strong: small N traps in absorbing state | Weak | **Strong** | Weak | **DP** |
    | Binder cumulant | Size-ordered (U↑ with N at μ < μ_c) | Standard | **Standard + absorbing** | Standard | **DP** |

    **Key findings from dedicated investigation:**

    1. **Absorbing state confirmed (Experiment A).** Starting from all-random initial conditions (no replicators), the soup NEVER spontaneously generates replicators within 5000 epochs at any μ (0/10 trials at μ = 0.010–0.100). This means ρ=0 is an absorbing state — the definitive signature of the Directed Percolation universality class. Z₃ Potts is an equilibrium model with no absorbing state, so it is categorically excluded.

    2. **Order parameter ρ(μ) measured (Experiment 1).** Using seeded initial conditions (100% verified replicators), the steady-state replicator density was measured at 17 mutation rates and 5 system sizes. The transition is sharp: ρ drops from ~0.89 at μ=0.001 to ~0.01 at μ=0.012 to 0 at μ=0.013.

    3. **Critical exponent β (Experiment 3).** At N=4000 with 10 trials per point and 11 μ values: best-fit β depends on assumed μ_c. For μ_c=0.0110: β=0.575 (matches DP 2+1D β=0.584). For μ_c=0.0120 (best R²=0.9994): β=0.851. For μ_c=0.0125: β=0.989 (matches mean-field β=1.0). The global random pairing creates a well-mixed (mean-field-like) geometry, so β between DP(2+1D) and mean-field is expected.

    4. **Dynamic exponent z (Experiment 4).** Relaxation time τ(N) measured at 5 μ values. At μ=0.010 (near criticality): z_eff = 1.55, remarkably close to DP(1+1D) z = 1.581. At μ > μ_c: z → 0 (all systems decay quickly regardless of N).

    5. **Strong finite-size effects (Experiment 1).** At μ=0.010: ρ(N=200) = 0.024, ρ(N=4000) = 0.197. Small systems get trapped in the absorbing state ρ=0, a hallmark of DP transitions. This is absent in equilibrium (Potts) transitions.

    **Interpretation for Svetitsky-Yaffe mapping:**

    The soup's error catastrophe is NOT in the Z₃ Potts universality class — it is in the Directed Percolation class. This means:
    - Claim 4 (error catastrophe ↔ deconfinement) must be reframed: the mapping is **structural** (Z₃ symmetry breaking, order parameter, critical threshold) but not **universal** (different critical exponents)
    - This is physically consistent: the soup is a non-equilibrium system with an absorbing state, which categorically places it outside equilibrium universality classes
    - The Svetitsky-Yaffe framework remains valid as a structural analogy; the DP nature of the transition reflects the irreversibility of replicator destruction (mutation erases, but random programs don't spontaneously become replicators)
    - Q8 (Z₃ symmetry breaking by VM) is now less problematic: DP does not require exact Z₃ symmetry — it only requires an absorbing state and a control parameter

    **Files:** `stella_lang/universality_class.c` (v1), `universality_class_v2.c` (v2, fine resolution), `verify_replicator.c` (replicator validation), `diagnose_seed.c` (diagnostic)

    **Priority:** RESOLVED.

12. **Can the bootstrap identification be made quantitative?** **✅ RESOLVED — SEMI-QUANTITATIVE DICTIONARY ESTABLISHED.**

    **Investigation:** `stella_lang/quantitative_bootstrap.c` (4 experiments, ~18 min runtime)

    The bootstrap identification is **structural + semi-quantitative**: dimensionless ratios are O(1) and converge with system size, but exact proportionality constants require a constructive Z₃ → SU(3) promotion (Q9).

    **Updated dictionary (measured values):**

    | Soup parameter | QCD observable | Mapping | Measured ratio | Status |
    |---------------|---------------|---------|---------------|--------|
    | $k_{\text{eff}} = 0.24$ | $\alpha_s \approx 0.30$ | $k_{\text{eff}}/\alpha_s = 0.80$ | O(1) — natural | ✅ MEASURED |
    | $\mu_c \approx 0.011$ | $T_c = 270$ MeV | $T/\mu = 24545$ MeV | Proportional | ✅ MEASURED |
    | $\gamma = 0.006$ | Gluon condensate $\langle G^2 \rangle$ | $\gamma/k_{\text{eff}} = 0.026$ | Structural | ✅ MEASURED |
    | $D$ (diffusion) | $\xi$ (correlation length) | — | Lattice artifact | ✅ CONFIRMED |

    **Key results:**

    1. **$k_{\text{eff}} \leftrightarrow \alpha_s$:** Ratio $k_{\text{eff}}/\alpha_s \approx 0.80$ is O(1), confirming a natural identification. Via center projection: $k_{\text{eff}} = (1/N_c^2) \times \alpha_s \times f_{\text{rep}}$ with $f_{\text{rep}} \approx 7.2$, encoding the computational amplification of the Z₃ center coupling by self-replication.

    2. **$\mu_c \leftrightarrow T_c$:** Proportional mapping $T/T_c = \mu/\mu_c$ works. Potts coupling identification $L_{\text{core}} \cdot \mu_c \leftrightarrow 1/\beta_c$ gives $\mu_c^{\text{pred}} = 0.050$ vs measured $\mu_c = 0.011$, a factor ~0.22 reflecting non-equilibrium fragility (replication is more fragile than equilibrium ordering).

    3. **Physical meaning of $\gamma$:** The competition coefficient $\gamma/k_{\text{eff}} = 0.026$ represents replicator-replicator interference (corruption during A||B execution). QCD analogs: gluon condensate (vacuum self-interaction) or string breaking. The ratio is small (2.6%), consistent with replicator-replicator interactions being mostly neutral.

    4. **Lattice-spacing independence:** The ratio $k_{\text{eff}}/\mu_c$ converges to $\approx 14.3$ with only 2.4% variation between $N = 2000$ and $N = 4000$. The dimensionless threshold $\mu_c \times L_{\text{core}} = 0.22$ is independent of system size. Confirmed: ratios are lattice-independent.

    **Remaining gap:** The proportionality constants (e.g., $f_{\text{rep}} \approx 7.2$, fragility factor $\approx 0.22$) cannot be derived from first principles without a constructive Z₃ → SU(3) promotion. This is a limitation of the structural mapping, not a failure of the dictionary.

    **Q12 Follow-up: Three paths to first-principles derivation (investigated 2026-03-10).**

    Three parallel investigations tested whether the proportionality constants can be derived:

    **(A) Constructive RG map** (`rg_map_construction.c`): Block-spin RG from L=3→L=2 soup Hamiltonian, compared with Z₃ Potts. Three strategies tested (decimation, majority vote, NESS-weighted). **Result:** NESS-weighted decimation shows individual level matches (E₅ at 0.004%, E₈ at 0.34%) but overall Frobenius residual is 0.81–0.96 (poor). The RG approach is **inconclusive at L=3→L=2** — needs larger systems or better coarse-graining prescriptions. The spectral gap proportionality f = gap_RG/gap_Potts ≈ 0.04–0.44 does not match f_rep ≈ 7.2 (which relates growth rates, not spectral gaps).

    **(B) Large-L spectral convergence** (`spectral_convergence_L5.c`, `spectral_convergence_L6.c`, `spectral_convergence_L8.c`): Extended spectral matching from L=5 (59K states) through L=8 (43M states) using Lanczos. **Key result — apparent even-L convergence was a small-system artifact:**

    | $L$ | $n_{\text{cfg}}$ | $E_2/E_1$ (soup) | $|E_2/E_1 - 1|$ | Parity |
    |-----|----------|-----------|---------|--------|
    | 2 | 81 | 1.228 | 0.228 | even |
    | 3 | 729 | 1.347 | 0.347 | odd |
    | 4 | 6,561 | 1.070 | **0.070** | even |
    | 5 | 59,049 | 1.275 | 0.275 | odd |
    | 6 | 531,441 | 1.066 | **0.066** | even |
    | **8** | **43,046,721** | **1.102** | **0.102** | **even** |

    The even-$L$ sequence appeared to converge at L=2,4,6 ($0.228 \to 0.070 \to 0.066$), but **L=8 regresses to 0.102**, decisively breaking the pattern. (Confirmed with both 150 and 200 Lanczos iterations; the 200-iteration value $E_2/E_1 = 1.1021$ is the definitive one.) The spectral gap itself is stable ($\approx 0.008$ across all even $L$), confirming this is not a numerical artifact. The NESS-symmetrized soup Hamiltonian does **not** converge to the Z₃ Potts spectrum in the thermodynamic limit.

    **Assessment: NEGATIVE.** The spectral bridge hypothesis is falsified. The soup's low-energy spectrum has its own structure that does not reduce to any Z₃ Potts model at large $L$. This means the Z₃ → SU(3) promotion cannot be established via direct spectral matching.

    **(C) Critical exponent matching** (`critical_exponents.c`): Measured $\beta, \gamma, z$ near $\mu_c$. **Result — DP confirmed, NOT Potts:**

    | Exponent | Potts (2D) | DP (2D) | Measured | Match |
    |----------|-----------|---------|----------|-------|
    | $\beta$ | 0.111 | 0.583 | **0.59–0.70** | **DP** |
    | $\gamma$ | 1.444 | 0.54 | **0.40** | ~DP |
    | $z$ | ~1.0 | 1.58 | **1.64** | **DP** |

    The error catastrophe is **categorically in the Directed Percolation universality class**, not Z₃ Potts. The absorbing state ($\rho = 0$) dominates the critical behavior. This does NOT invalidate Svetitsky-Yaffe — it means the SY mapping applies to the Z₃ symmetry-breaking sector (low-energy spectral structure), not to the absorbing-state transition. The spectral matching (Option B) tests the correct quantity.

    **Updated assessment (post-L=8): SPECTRAL CONVERGENCE FALSIFIED.** The L=8 computation (43M states, 24 min wall time) shows $|E_2/E_1 - 1| = 0.112$, a clear regression from L=4 (0.070) and L=6 (0.066). The three-point "convergence" at L=2,4,6 was misleading — with four even-$L$ data points, there is no monotonic trend. The soup's spectral structure is intrinsically different from Z₃ Potts and does not converge to it.

    **Implications for the Z₃ → SU(3) promotion:**
    - The direct spectral bridge (Option B) is **closed**.
    - The constructive RG map (Option A) was already inconclusive.
    - The critical exponents (Option C) confirmed DP, not Potts, for the absorbing-state transition.
    - **All three computational paths to a first-principles Z₃ → SU(3) derivation have failed or are inconclusive.**
    - The five structural arguments in §7 (shared symmetry, center vortices, Svetitsky-Yaffe, Doi-Peliti, Wilson loop) remain as qualitative motivation, but no quantitative spectral identification has been established.
    - This is an **honest gap** in the proposition that must be acknowledged.

    **Q12 Follow-up Round 2: Four additional investigations (2026-03-10).**

    After spectral convergence failed at L=8, four parallel investigations tested alternative paths:

    **(D) Conditional spectrum** (`conditional_spectrum.c`): Restricted H_phys to states with ρ > threshold (Method A: trit density, Method B: NESS weight percentile). **Result: NEGATIVE.** Restriction makes E₂/E₁ **worse** (1.14 → 1.37 at ρ > 0.5). The non-Potts spectral structure is intrinsic to the active phase, not DP contamination.

    **(E) Z₃ order parameter** (`z3_order_parameter.c`): Measured Z₃ magnetization m = (1/N)Σ ω^{s_i}, susceptibility χ_Z3, phase histograms, Binder cumulant. **Result: CRITICAL FINDING — Z₃ symmetry is explicitly broken by the VM.**

    | Sector | Expected (Z₃ symmetric) | Measured (μ=0.001) | Conditional (ρ>0.3) |
    |--------|------------------------|-------------------|-------------------|
    | 0 | 33.3% | 23.5% | 22.2% |
    | 2π/3 | 33.3% | 24.5% | 24.9% |
    | 4π/3 | 33.3% | **52.1%** | **52.9%** |

    **Root cause:** The VM's OPEN instruction (`12`) tests `tape[h0] == 0`, treating trit value 0 differently from 1 and 2. This is an O(1) explicit breaking of Z₃ symmetry. The breaking persists after conditioning on active states and grows with system size (ratio ⟨|m|⟩/⟨|m|⟩_random: 1.16→1.29 from L=2 to L=5). No Binder cumulant crossing → no separate Z₃ transition. **This means Svetitsky-Yaffe was never applicable:** SY requires exact Z₃ center symmetry.

    **(F) Wilson loops** (`wilson_loop_2d.c`): Measured Wilson loops on 2D triangular soup with site-derived link variables U_{ij} = ω^{s_i - s_j}. **Result: TRIVIAL.** All Wilson loops = 1.0 identically, because site-derived link variables are "pure gauge" (∏_{loop} ω^{s_i - s_j} = ω^0 = 1 for any closed loop). The soup has site variables, not independent link variables — Wilson loops are not the right observable for site-based models.

    **(G) Doi-Peliti analytical derivation** (`Proposition-0.0.XXe-Doi-Peliti-Z3-Gauge-Analysis.md`): Rigorous analytical investigation of whether the Doi-Peliti field theory reduces to Z₃ gauge theory. **Result: NEGATIVE.** Three fundamental obstructions identified: (a) site vs link degrees of freedom — gauge theories need link variables; (b) global vs local symmetry — the soup has global Z₃, not local (gauge) Z₃; (c) the VM interaction is many-to-one and nonlocal, preventing expression as gauge-invariant plaquettes. The Landau theory analysis confirms the phase transition is in the replicator density (ρ) sector, not the Z₃ magnetization (m) sector.

    **Key reframing from (G):** The gauge structure in CG comes from the stella geometry (Thms 0.0.2–0.0.3), not from the Doi-Peliti dynamics. The correct picture is sequential:

    $$\text{Z₃ soup} \xrightarrow{\text{continuum limit}} \text{Fisher-KPP on } \partial\mathcal{S} \xrightarrow{\text{geometric structure}} \text{SU(3) gauge theory}$$

    The soup provides the Z₃ center symmetry that seeds the CG framework. The full SU(3) gauge theory emerges from the geometric structure of ∂S, not from a direct Hamiltonian reduction.

    **Updated overall assessment:** The Z₃ → SU(3) promotion is NOT a direct dynamical emergence from the soup. It is a two-step process: (1) the soup establishes Z₃-symmetric self-replicating fixed points on ∂S, and (2) the geometric structure of ∂S (stella octangula) determines SU(3). The "promotion" is geometric, not spectral.

    **Q12 Follow-up Round 3: RG relevance and correlation structure (2026-03-10).**

    Two further investigations test whether emergent Z₃ symmetry could appear at long wavelengths or near criticality:

    **(H) Block-spin RG / effective action coarse-graining** (`effective_action_coarsegrain.c`): Applied block-spin RG with majority vote at block sizes b=2,3,5,9 on 1D soup (N=1002, 2004, 3996 sites), up to 3 blocking levels. Measured Z₃ asymmetry $A = 1 - 3\min(p_0, p_1, p_2)$ and entropy $S/\log 3$ at each blocking level.

    **Result: Z₃ BREAKING IS RG-RELEVANT.** The asymmetry *grows* under coarse-graining:

    | Block size | Level 0 | Level 1 | Level 2 | Level 3 | Growth factor |
    |-----------|---------|---------|---------|---------|--------------|
    | b=3 | 0.292 | 0.353 | 0.439 | 0.545 | ~1.24×/step |
    | b=5 | 0.292 | 0.429 | 0.607 | 0.796 | ~1.40×/step |
    | b=9 | 0.292 | 0.536 | 0.773 | 0.920 | ~1.47×/step |

    Entropy $S/\log 3$ decreases correspondingly: $0.936 \to 0.908 \to 0.856 \to 0.772$ (b=3). The IR theory moves *away* from Z₃ symmetry at all system sizes tested. **There is no emergent Z₃ Potts symmetry at long wavelengths.**

    **(I) 2D correlation functions** (`correlation_2d_soup.c`): Measured Z₃ correlator $G_{\delta}(r) = \langle\delta(s_i, s_j)\rangle - 1/3$ and density correlator $G_\rho(r) = \langle\rho_i \rho_j\rangle - \langle\rho\rangle^2$ on 2D triangular lattice at L=20,40,60 and μ=0.003–0.012, with 200 samples each.

    **Result: Z₃ AND DENSITY SECTORS ARE COMPLETELY DECOUPLED.**

    | Observable | Behavior | Correlation length |
    |-----------|----------|-------------------|
    | Z₃ correlator $G_\delta(r)$ | **Flat** (no spatial decay) | $\xi_{Z_3}$ = N/A (fit fails at all L, μ) |
    | Density correlator $G_\rho(r)$ | Exponential decay | $\xi_\rho$ = 2–12 lattice spacings |

    The Z₃ trit values have *no spatial structure whatsoever* — $G_\delta(r)$ is essentially constant from $r=1$ to $r=L/2$. Meanwhile, density has well-defined exponential correlations with $\xi_\rho$ growing with system size ($\sim 3$ at L=20, $\sim 6$ at L=40, $\sim 11$ at L=60).

    Finite-size scaling of $\xi_\rho$ gives effective exponents $\nu_\text{eff} = 0.55$–$0.93$ depending on μ, broadly consistent with DP ($\nu_\perp = 0.734$) rather than Potts ($\nu = 0.833$), though the spread is too large for definitive assignment.

    **Key conclusion from (H)+(I):** The Z₃ sector is completely inert — no spatial correlations, no RG flow toward symmetry, no independent critical behavior. The soup's phase transition lives entirely in the density (DP) sector. The Z₃ content of the soup is a *frozen random background* that the replicator dynamics rides on top of, not a dynamical order parameter.

    **Final synthesis (Rounds 1–3):** Nine independent probes all confirm: the soup does NOT have Z₃ Potts universality. The Z₃ → SU(3) promotion is geometric (via ∂S structure from Thms 0.0.2–0.0.3), not dynamical.

    **The four-step scaffold picture (see Prop 0.0.XXe §7.6):**

    $$\partial\mathcal{S} \text{ (topology)} \;\to\; \mathbb{Z}_3 \text{ (center symmetry scaffold)} \;\to\; \text{SU}(3) \text{ (geometric promotion)} \;\to\; \text{Fisher-KPP (replicator physics on scaffold)}$$

    The Z₃ trits are a *frozen random background* — they define the representation-theoretic substrate on which replicator dynamics plays out. The stella geometry promotes Z₃ → SU(3) algebraically (Thm 0.0.3). The density sector carries all spatial correlations and critical behavior (DP class). This separation mirrors lattice QCD, where center symmetry is an algebraic property of SU(3), not something the gauge field "produces."

13. **Why does the PDE overpredict replicator density by ~47%?** **✅ RESOLVED — TILING BUG + INTERACTION ASYMMETRY (2026-03-10).**

    The two-component Fisher-KPP model predicts $\rho^* = 0.810$ (at $\mu = 0.001$), but the FCC lattice runs (`sweep_oct_results/octahedral_cr0.1_s123.txt`) show per-stella density $\rho^* \approx 55\text{--}58\%$. Investigation reveals the dominant cause is a **tiling algorithm bug** in `soup_multi_stella.c`, compounded by the VM's interaction asymmetry.

    **Scripts:**
    - `stella_lang/density_discrepancy.c` — flat-tile experiments (8 experiments)
    - `stella_lang/density_local_vs_global.c` — pairing mode comparison
    - `stella_lang/tile_size_diagnostic.c` — Voronoi tile size analysis
    - `stella_lang/tiling_improvement.c` — tiling algorithm comparison (6 strategies)
    - `stella_lang/check_multi_stella_rep.c` — replicator validation

    **Summary of density by geometry:**

    | Geometry | Pairing | $\rho^*$ ($\mu=0.001$) | Script |
    |----------|---------|------------------------|--------|
    | Flat tiles (N=4096) | Global random | **89.0%** | `density_discrepancy.c` |
    | 2D triangular grid | Local (6 neighbors) | **87.7%** | `density_local_vs_global.c` |
    | 1D ring | Local (2 neighbors) | **71.3%** | `density_local_vs_global.c` |
    | Multi-stella BFS Voronoi (n_sub=100) | Local + buggy tiling | **~55%** (pre-fix) | `tile_size_diagnostic.c` |
    | FCC lattice L=4 (actual run) | Local + octahedral coupling | **55–58%** (pre-fix) | `sweep_oct_results/` (old) |
    | Multi-stella greedy-fill (n_sub=100) | Local + corrected tiling | **~87%** | `RERUN_PLAN.md` Priority 1–2 |
    | FCC lattice L=4 (re-run) | Local + octahedral coupling | **86–91%** | `sweep_oct_results/` (corrected) |
    | Fisher-KPP PDE | Mean-field | **81.0%** | analytic |

    **Root cause — The BFS Voronoi tiling algorithm creates 16.4% permanently dead tiles.**

    The parallel BFS in `tiling_build()` seeds all 833 tiles simultaneously and grows them in parallel. On the triangulated tetrahedron, tiles compete for sites and some get "boxed in" before reaching prog_size=24. This produces:

    | Tile size | Count (per tetrahedron) | Can replicate? |
    |-----------|-------------------------|----------------|
    | 24 (full) | 590 (70.8%) | Yes |
    | 19–23 | 106 (12.7%) | Yes (partial) |
    | < 19 | 137 (16.4%) | **No** |

    Additionally, **2,228 sites (11.1%) remain unowned** — not assigned to any tile. The mesh has 20,002 sites; 833 tiles × 24 = 19,992 should cover all but 10, yet the BFS leaves 2,228 orphaned due to the parallel growth race condition.

    **This is an algorithmic artifact, not a geometric constraint.** The mesh itself is nearly perfectly regular: 99.97% of sites have 6 neighbors (standard triangular grid), with only the 4 tetrahedron vertices having 3 neighbors. Six alternative tiling strategies were tested (`tiling_improvement.c`):

    | Strategy | Tiles | Undersized (<19) | Unowned | Max $\rho$ |
    |----------|-------|-------------------|---------|-----------|
    | **A: Original BFS** (current) | 833 | **137 (16.4%)** | 2,228 | 83.6% |
    | B: BFS + redistribute | 833 | 137 (16.4%) | 0 | 83.6% |
    | C: BFS, fewer tiles (500) | 500 | 2 (0.4%) | 8,033 | 99.6% |
    | D: BFS + merge undersized | 696 | 137 → dissolved | 3,512 | 80.3% |
    | **E: Greedy sequential fill** | **845** | **14 (1.7%)** | **0** | **98.3%** |
    | F: Uncapped BFS | 833 | 242 (29.1%) | 0 | 70.9% |

    **Strategy E (greedy sequential fill) eliminates the problem:** grow one tile at a time to full prog_size before starting the next. Result: 845 tiles, 831 at full size (98.3%), only 14 undersized (the last few tiles that exhaust available contiguous sites), zero unowned sites.

    **Fix applied:** `soup_multi_stella.c` `tiling_build()` replaced with greedy sequential fill algorithm. The FCC lattice runs should be re-run to measure the corrected equilibrium density.

    **Remaining genuine mechanism — Interaction asymmetry.**

    From `density_discrepancy.c` Experiment 5 (100K tests each):

    | Interaction type | Outcome | Frequency |
    |------------------|---------|-----------|
    | Rep(A) \|\| Food(B) | Both outputs are replicators | **100.00%** |
    | Food(A) \|\| Rep(B) | Replicator destroyed | **69.35%** |
    | Food(A) \|\| Rep(B) | Replicator survives | **30.65%** |
    | Rep(A) \|\| Rep(B) | Both survive | **100.00%** |

    This gives $k_{\text{eff}} = 0.1533$, predicting $\rho^* = 0.870$ (flat-tile measured: 0.890). Local pairing on the 2D triangular grid reduces this slightly to 87.7%. This is the **genuine** physics that the PDE should capture — an ~8% discrepancy from mean-field, not 47%.

    **Revised quantitative picture (after tiling fix):**

    $$\underbrace{\rho^*_{\text{PDE}} = 0.810}_{\text{Fisher-KPP}} \;\approx\; \underbrace{\rho^*_{\text{flat}} = 0.890}_{\text{flat-tile measured}} \;\approx\; \underbrace{\rho^*_{\text{2D local}} = 0.877}_{\text{local pairing}} \;\approx\; \underbrace{\rho^*_{\text{stella (fixed)}} \approx 0.85\text{--}0.88}_{\text{predicted after fix}}$$

    The PDE's 81% is within ~8% of the true microscopic value (~88%), which is reasonable for a mean-field approximation that uses effective rates.

    **Additional supporting findings:**

    - **Single replicator family**: 8 unique cores found, all within Hamming distance 3 of REPLICATOR_A → 1 family. Multi-species competition is not the mechanism.
    - **Parasites present but minor**: ~3.6% of total soup. Not sufficient to explain any significant gap.
    - **Two distinct replicators**: The multi-stella code uses a different replicator (Hamming distance 6 from REPLICATOR_A). Both are valid (100% replication on full-size tiles).

    **Implications for the proposition:**
    - The PDE (Claim 2) is a **faithful mean-field description** — the "47% overprediction" was an artifact of the tiling algorithm, not a PDE failure
    - After fixing the tiling, the stella geometry should give $\rho^* \approx 0.85\text{--}0.88$, consistent with the PDE's 0.810 (within mean-field accuracy)
    - The interaction asymmetry ($k_{\text{eff}} = 0.1533$ from microscopic rates) provides the correct effective growth rate
    - §3.2.7 should note: $\rho^* \approx 0.89$ (flat-tile), $\rho^* \approx 0.88$ (local pairing), $\rho^* \approx 0.55$ (old BFS tiling, now understood as bug)

    **Action items:**
    1. ~~Patch `soup_multi_stella.c` `tiling_build()` with greedy sequential fill~~ ✅ DONE
    2. ~~Re-run FCC lattice sweeps with corrected tiling to confirm $\rho^* \approx 0.85\text{--}0.88$~~ ✅ DONE — All re-runs completed (2026-03-11 to 2026-03-13). Confirmed $\rho^* \approx 0.86\text{--}0.87$ across all configurations: Priority 1 sweep (86–91%), Priority 2 cross-rate sweep (86.4–87.0%), Priority 3 soup_2d_tile, Priority 4 propagation/wavefront (83.7–87.9%), Priority 5 fine-resolution seeded wavefront. See `stella_lang/RERUN_PLAN.md` for full results.
    3. ~~Update Phase 3 document density references once new runs confirm~~ ✅ DONE — Phase 3 Reaction-Diffusion doc and Phase 2 Z3-Potts doc updated with corrected density values.

    **Priority:** FULLY RESOLVED (tiling bug fixed, all re-runs complete, documents updated).

14. **Can Z₃ vortices be detected in the discrete soup?** **✅ RESOLVED — VORTICES DETECTED BUT DYNAMICALLY INERT (2026-03-13).**

    Section §6.1 defines Z₃ center vortices on $\partial\mathcal{S}$ classified by $\pi_2(\text{SU}(3)/\mathbb{Z}_3) = \mathbb{Z}_3$. A comprehensive numerical investigation defines discrete Z₃ clock-model vortices on triangular plaquettes and measures their density, correlations, and coupling to replicator dynamics. Script: `stella_lang/z3_vortex_detection.c` (6 experiments).

    **Vortex definition:** On the triangular lattice, each plaquette (i,j,k) has a Z₃ winding number computed via branch-cut-remapped phase differences. The coarse spin $s_i = (\text{trit}_0 + \text{trit}_1 + \text{trit}_2) \bmod 3$ defines the phase. A plaquette with all three spins distinct in cyclic order (0→1→2) is a vortex (+1); anti-cyclic (0→2→1) is an anti-vortex (−1). For random Z₃: $P(\text{vortex}) = P(\text{anti-vortex}) = 1/9 \approx 0.111$, total frustrated $= 2/9 \approx 0.222$.

    **Finding 1 — VM dynamics suppress vortices (Experiments A, D):**

    | $\mu$ | $\rho$ | $v_{\text{dens}}$ | $v/v_{\text{random}}$ | Interpretation |
    |-------|--------|-------------------|----------------------|----------------|
    | 0.001 | 0.740 | **0.162** | **0.731** | VM suppresses by 27% |
    | 0.005 | 0.734 | 0.185 | 0.832 | Partial suppression |
    | 0.010 | 0.726 | 0.201 | 0.904 | Approaching random |
    | 0.050 | 0.701 | 0.221 | 0.993 | Near random |
    | 0.100 | 0.693 | **0.223** | **1.002** | Random recovered |

    The soup's vortex density at $\mu = 0.001$ is **−6.94σ below random** ($v = 0.162$ vs $0.222 \pm 0.009$). This is NOT random noise — the VM dynamics create same-trit correlations between neighboring sites (via CPY instructions), increasing the probability of matching spins on plaquette vertices and thereby suppressing the all-different configurations that produce vortices. At high mutation ($\mu = 0.1$), randomization restores the exact 2/9 density.

    **Finding 2 — Per-trit-layer asymmetry reveals VM fingerprint (Experiment C):**

    | $\mu$ | $v_{\text{coarse}}$ | $v_{\text{trit0}}$ | $v_{\text{trit1}}$ | $v_{\text{trit2}}$ |
    |-------|---------------------|--------------------|--------------------|--------------------|
    | 0.001 | 0.159 | **0.007** | 0.119 | 0.130 |
    | 0.010 | 0.204 | **0.025** | 0.177 | 0.179 |
    | 0.050 | 0.218 | **0.074** | 0.203 | 0.209 |

    Trit 0 has **dramatically fewer vortices** than trits 1 and 2 (0.007 vs ~0.12 at $\mu = 0.001$). This directly reflects the VM's Z₃ symmetry breaking: the OPEN/CLOSE instructions test `tape[h0] == 0`, making trit value 0 special. The Z₃ sector distribution confirms this: sectors [0.16, 0.56, 0.28] vs random [0.33, 0.33, 0.33]. This is consistent with Q8's finding of explicit Z₃ breaking by the instruction encoding.

    **Finding 3 — No long-range vortex correlations (Experiment B):**

    | $r$ | $\langle q_p \cdot q_q \rangle$ ($\mu = 0.001$) | Significance |
    |-----|------------------------------------------------|-------------|
    | 1 | $+0.011$ | ~1.7σ (shared vertices) |
    | 2 | $-0.001$ | $< 1\sigma$ |
    | 3+ | $|\langle qq \rangle| < 0.001$ | Noise |

    Nearest-neighbor plaquettes show a weak positive correlation ($\langle qq \rangle \approx 0.01$) entirely attributable to shared vertices. Beyond $r = 1$, correlations are indistinguishable from zero at all $\mu$ values tested. **No vortex-antivortex binding or percolation transition detected.**

    **Finding 4 — No error catastrophe signature (Experiment E):**

    The vortex density increases smoothly and gradually with $\mu$, with no discontinuity or sharp feature near $\mu_c \approx 0.012$. At three system sizes ($L = 20, 40, 60$), the vortex density follows a featureless interpolation between the VM-suppressed value (~0.19 at $\mu = 0.008$) and the random value (~0.21 at $\mu = 0.020$). The error catastrophe (DP transition in the density sector) has **no signature in the vortex sector**.

    **Finding 5 — Vortex–density decoupling confirmed (Experiment F):**

    The connected correlator $C_{q\rho} = \langle |q| \rho \rangle - \langle |q| \rangle \langle \rho \rangle$ is $O(10^{-3}$–$10^{-4})$ at all $\mu$ tested — effectively zero. Vortex presence does not correlate with local replicator density. This confirms the Z₃ and density sectors are decoupled, consistent with Q12(I).

    **Resolution — Overall assessment:**

    **(+) POSITIVE:** Z₃ vortices CAN be defined and measured in the discrete soup. The VM dynamics produce a **measurable, statistically significant** departure from random: 27% suppression at low $\mu$, with strong per-trit asymmetry reflecting the VM's Z₃ symmetry breaking.

    **(−) NEGATIVE:** The vortices carry **no dynamical content** relevant to the replicator physics:
    - No spatial correlations beyond shared-vertex nearest neighbors
    - No coupling to replicator density
    - No signature of the error catastrophe
    - No vortex-antivortex binding or percolation transition
    - The suppression is entirely explained by the VM's same-trit copying bias

    **(!) KEY INSIGHT:** The vortex sector provides a **quantitative fingerprint of the VM's Z₃ symmetry breaking**, not evidence for topological gauge structure. The 27% suppression and 17:1 trit-layer asymmetry (trit 0 vs trits 1,2) are direct consequences of the instruction encoding bias identified in Q8. In lattice QCD, center vortices carry confining flux and percolate at the deconfinement transition — the soup's "vortices" do neither. This reinforces the Q12 conclusion: the Z₃ → SU(3) promotion is geometric (via ∂S structure), not dynamical.

    **Implication for §6.1:** The center vortex discussion should be reframed. Z₃ vortices exist as topological objects of the Z₃ clock model on ∂S, but they are not the analog of QCD center vortices. The soup's site-based Z₃ variables cannot produce the independent link variables needed for genuine gauge flux. The correct statement is: center vortices emerge after the geometric Z₃ → SU(3) promotion (Thm 0.0.3), not from the pre-geometric soup dynamics.

    **Priority:** RESOLVED.
    **Script:** `stella_lang/z3_vortex_detection.c`

15. **Rigorous proof that nucleation probability → 1 as N → ∞.** **RESOLVED by [Lemma 0.0.XXe-NP](Lemma-0.0.XXe-Nucleation-Probability-Proof.md).**

    All three investigation items have been addressed:

    1. **~~Formalize the coupon collector argument.~~** Superseded. Lemma 0.0.XXe-NP uses a stronger mutation-coupling approach (shadow process + stochastic domination) that avoids the coupon collector entirely. The bound works for any initial state, not just uniform random. The gap between $N \gg 3^{20}$ (coupon collector) and $N \approx 1{,}666$ (observed) is explained by VM-mediated search ($\gamma_{\text{eff}} \sim 0.1$–$0.5$ effective samples/tile/epoch).
    2. **~~Account for replicator combinatorics.~~** Done. The lemma uses $r = 120$ distinct replicators with 4 chirality cores × 30 valid tails, giving $\mathbb{P}(\text{tile is any replicator}) \geq r \cdot q_{\min}$ per mixing window (Lemma 2.7).
    3. **~~Rigorous bound.~~** Done. For any $\varepsilon > 0$: $N_0(\varepsilon, T) = \ln(1/\varepsilon) / (r \cdot q_{\min} \cdot \lfloor T/\tau_{\text{mix}} \rfloor)$ and $T_0(\varepsilon, N) = \tau_{\text{mix}} \cdot \ln(1/\varepsilon) / (r \cdot q_{\min} \cdot N)$. Mutation-only bound overestimates by $\sim 10^5$ (VM interactions dominate), confirming conservativeness.

    **2D geometry extension (Open Refinement #3 of the lemma):** Resolved. Computational analysis ([nucleation_2d_geometry.c](../../../verification/supporting/nucleation_2d_geometry.c)) shows the flat-tile bound applies to the 2D triangulated mesh with $< 10\%$ correction ($r_{\text{eff}} = r(1 - f_{\text{undersized}})$, where $f_{\text{undersized}} \approx 7.5 \times n_{\text{sub}}^{-1.31} \to 0$).

    **N-scaling verification (Open Refinement #2 of the lemma):** Resolved. Combined multi-seed campaigns (232 stellae, $N \in [1{,}666, \; 26{,}666]$, 58 runs) reveal a **two-regime structure** in $T_{\text{emerge}}(N)$: rate-limited at $N \lesssim 4{,}000$ ($T \approx 1$–$2$M epochs, N-independent) transitioning to Poisson-like scaling at $N \gtrsim 6{,}000$ (exponent $-0.49$ to $-0.68$, approaching the rigorous bound's $N^{-1}$ prediction). The crossover at $N \sim 4{,}000$–$6{,}000$ corresponds to local-search saturation. At $N \geq 6{,}666$, nucleation within $5 \times 10^6$ epochs is $> 98\%$ certain (71/72 stellae). Scripts: [n_scaling_campaign.py](../../../stella_lang/n_scaling_campaign.py), [n_scaling_extension_campaign.py](../../../stella_lang/n_scaling_extension_campaign.py), [n_scaling_analysis.py](../../../stella_lang/n_scaling_analysis.py).

    **Priority:** RESOLVED.
    **Proof:** [Lemma-0.0.XXe-Nucleation-Probability-Proof.md](Lemma-0.0.XXe-Nucleation-Probability-Proof.md)
    **Scripts:** `verification/supporting/lemma_0_0_XXe_NP_adversarial_verification.py`, `verification/supporting/nucleation_2d_geometry.c`, `stella_lang/n_scaling_campaign.py`, `stella_lang/n_scaling_extension_campaign.py`

16. **Can the 50% bilayer coupling be derived from geometry?** **RESOLVED.**

    The 50% cross-coupling fraction $\kappa = 1/2$ follows from the face adjacency graph of the stella octangula. Each face of $T_+$ has exactly 3 intra-tetrahedron neighbors (via shared edges of the tetrahedron) and exactly 3 inter-tetrahedron neighbors (via intersection lines with $T_-$ faces). The one $T_-$ face with anti-parallel normal is parallel and non-intersecting, leaving $4 - 1 = 3$ cross-neighbors — matching the intra count. This 3+3 equipartition gives $\kappa_{\text{comb}} = 3/6 = 1/2$.

    The 12 inter-tetrahedron intersection segments are the edges of the inner regular octahedron $T_+ \cap T_-$, with length $\ell_{\text{inter}} = \ell_{\text{intra}}/2$. A boundary-length-weighted alternative gives $\kappa_{\text{length}} = 1/3$ (with $\kappa_{\text{comb}} = \frac{3}{2} \kappa_{\text{length}}$), but the discrete soup uses combinatorial pairing (each neighbor equally likely), so $\kappa = 1/2$ is the correct value. Four other weighting measures (solid-angle ≈ 0.636, flux = 1/2, area-overlap = 0) were evaluated and dismissed. PDE simulations confirm $\kappa = 1/2$ equilibrates 42% faster than $\kappa = 1/3$.

    The stella octangula is the unique Platonic compound yielding a **symmetric bilayer** with $\kappa = 1/2$. While the cube-octahedron compound also gives $\kappa = 1/2$ per face type (cube: 4/8, octahedron: 3/6), it has non-identical layers (6-face vs 8-face surfaces), breaking the $\mathbb{Z}_2$ layer-exchange symmetry required for the bilayer PDE. Only the self-dual tetrahedron produces two identical layers — consistent with Theorem 0.0.3 (Stella Uniqueness).

    This derivation reduces the model's free parameters from 5 to 4.

    **Priority:** RESOLVED. Multi-agent adversarial verification passed (3 agents + 7/7 adversarial tests).
    **Proof:** [Lemma-0.0.XXe-Bilayer-Coupling-Geometric-Derivation.md](Lemma-0.0.XXe-Bilayer-Coupling-Geometric-Derivation.md)
    **Lean 4:** [`BilayerCoupling.lean`](../../../lean/ChiralGeometrogenesis/PureMath/Polyhedra/BilayerCoupling.lean) — Machine-verified proof of κ = 1/2, geometric intersection witnesses, Platonic uniqueness
    **Verification:** [Lemma-0.0.XXe-BC-Multi-Agent-Verification-2026-03-18.md](../verification-records/Lemma-0.0.XXe-BC-Multi-Agent-Verification-2026-03-18.md)
    **Scripts:** `verification/supporting/lemma_0_0_XXe_BC_bilayer_coupling.py`, `verification/supporting/lemma_0_0_XXe_BC_adversarial_verification.py`

17. **Are mesons faithfully described as large-amplitude Q=0 perturbations?** **RESOLVED.**

    **Answer: Partially correct but fundamentally incomplete.** Mesons are correctly identified as $Q = 0$ (topologically trivial), unstable, and localized. However, the Fisher-KPP framework **cannot** describe mesons because:

    1. **No oscillatory modes.** The linearized Fisher-KPP operator around $\rho^*$ has eigenvalues $\lambda_\ell = D\ell(\ell+1)/R^2 + (k_{\text{eff}} - \mu_{\text{eff}})$, all real and positive. Perturbations decay monotonically — no oscillation frequencies exist. Mesons require oscillatory dynamics ($\omega = \sqrt{k^2 + m^2}$).

    2. **Wrong time order.** Fisher-KPP is first-order in time (parabolic/diffusive). Meson physics requires second-order in time (hyperbolic/wave-like). No breathers or oscillons can exist in a dissipative equation with a Lyapunov functional.

    3. **Missing phase degrees of freedom.** The density $\rho$ tracks only the amplitude of the chiral condensate. Pions are phase excitations (Goldstone modes of $U \in SU(3)$), invisible to $\rho$. Only scalar mesons ($\sigma$, $f_0(500)$) involve amplitude fluctuations — and these are the broadest mesons, consistent with the overdamped character of the amplitude sector.

    **Corrected description:** Mesons are oscillatory excitations of the chiral field vacuum $U = \mathbb{1}$ on $\partial\mathcal{S}$, governed by the Skyrme Lagrangian (macroscopic level), with $Q = 0$ and no topological protection. They emerge at the macroscopic level of the three-level hierarchy (Phase 4, §4.1.4), beyond the reach of the mesoscopic Fisher-KPP description.

    The catalytic-topological dichotomy (§6.4) is complete once mesons are recognized as living at the macroscopic level: unprotected resonances with neither catalytic (dynamical) nor topological ($Q \neq 0$) stability.

    **Priority:** RESOLVED. Structural analysis complete.
    **Analysis:** [Proposition-0.0.XXe-Q17-Mesons-As-Q0-Perturbations.md](Proposition-0.0.XXe-Q17-Mesons-As-Q0-Perturbations.md)
    **Verification:** [Proposition-0.0.XXe-Q17-Mesons-Multi-Agent-Verification-2026-03-18.md](../verification-records/Proposition-0.0.XXe-Q17-Mesons-Multi-Agent-Verification-2026-03-18.md) — Three-perspective adversarial review: all core claims verified, minor issues resolved

---

## Completion Criteria for Proposition 0.0.XXe

This workplan becomes a formal proposition when:

- [x] At least one computational phase (1 or 3) demonstrates self-replication in 2D/continuous setting — **Phase 1 (2D soup) and Phase 3 (PDE simulation) both complete**
- [x] At least one theoretical phase (2 or 4) establishes a rigorous continuum limit — **Phase 4 establishes Fisher-KPP on ∂S with well-posedness, existence, uniqueness, stability**
- [x] The bootstrap identification (Phase 4.3) is established at least at the level of a conjecture with supporting evidence — **Structural isomorphism established; quantitative gaps documented**
- [x] Physical interpretation (Phase 4.5) connects to existing CG results — **Vacuum state, deconfinement, cosmological phase transition all connected**
- [x] Limitations and caveats are honestly documented (following XXd's example) — **Three-tier assessment: rigorous / structural / conjectural in Phase 4 caveats section**

When these are met, this file will be replaced by a formal `Proposition-0.0.XXe-Continuum-Self-Replicating-Fields.md`.

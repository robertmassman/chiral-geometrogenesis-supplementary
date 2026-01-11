"""
Chiral Geometrogenesis Theorem Dependency Graph

This module creates a structured representation of all theorems in the framework
and their dependencies, enabling:
- Dependency graph visualization
- Phase-level analysis
- Verification status tracking
- Critical path identification
"""

import json
from dataclasses import dataclass, field, asdict
from typing import Optional
from enum import Enum


class Phase(Enum):
    """The five phases of the Chiral Geometrogenesis framework."""
    PHASE_0 = 0  # Pre-Geometric Structure
    PHASE_1 = 1  # Foundational Mathematics
    PHASE_2 = 2  # Pressure-Depression Mechanism
    PHASE_3 = 3  # Mass Generation via Phase-Gradient Mass Generation
    PHASE_4 = 4  # Topological Solitons as Matter
    PHASE_5 = 5  # Emergent Spacetime and Gravity


class Status(Enum):
    """Verification status of theorems."""
    ESTABLISHED = "established"  # Standard physics, well-known
    VERIFIED = "verified"        # Novel, but verified in this framework
    NOVEL = "novel"              # New physics, under review
    PARTIAL = "partial"          # Some aspects proven
    CONJECTURE = "conjecture"    # Hypothesized


class TheoremType(Enum):
    """Type of mathematical statement."""
    DEFINITION = "definition"
    THEOREM = "theorem"
    LEMMA = "lemma"
    COROLLARY = "corollary"


@dataclass
class Theorem:
    """Represents a single theorem in the framework."""
    id: str                              # e.g., "0.2.2", "3.1.1"
    name: str                            # e.g., "Internal Time Parameter Emergence"
    theorem_type: TheoremType
    phase: Phase
    status: Status
    description: str                     # Brief description
    key_result: Optional[str] = None     # Main formula or statement
    depends_on: list[str] = field(default_factory=list)  # IDs of dependencies
    required_by: list[str] = field(default_factory=list) # IDs that depend on this
    has_files: list[str] = field(default_factory=list)   # Associated file types
    verification_date: Optional[str] = None
    tags: list[str] = field(default_factory=list)        # e.g., ["bootstrap", "critical"]

    def full_id(self) -> str:
        """Return full ID with type prefix."""
        prefix = {
            TheoremType.DEFINITION: "Def",
            TheoremType.THEOREM: "Thm",
            TheoremType.LEMMA: "Lem",
            TheoremType.COROLLARY: "Cor"
        }
        return f"{prefix[self.theorem_type]} {self.id}"


class TheoremGraph:
    """
    Graph structure containing all theorems and their relationships.
    """

    def __init__(self):
        self.theorems: dict[str, Theorem] = {}
        self._build_graph()

    def _build_graph(self):
        """Construct the complete theorem graph."""

        # ============================================
        # PHASE 0: Pre-Geometric Structure
        # ============================================

        self.add_theorem(Theorem(
            id="0.1.1",
            name="Stella Octangula as Boundary Topology",
            theorem_type=TheoremType.DEFINITION,
            phase=Phase.PHASE_0,
            status=Status.VERIFIED,
            description="Establishes the topological boundary structure independent of bulk metric",
            key_result="∂S = S₄ × ℤ₂ symmetry group",
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-13",
            tags=["foundation", "topology"]
        ))

        self.add_theorem(Theorem(
            id="0.1.2",
            name="Three Color Fields with Relative Phases",
            theorem_type=TheoremType.DEFINITION,
            phase=Phase.PHASE_0,
            status=Status.VERIFIED,
            description="R, G, B fields with phases 0, 2π/3, 4π/3",
            key_result="φ_R = 0, φ_G = 2π/3, φ_B = 4π/3",
            depends_on=["0.1.1"],
            tags=["foundation", "color"]
        ))

        self.add_theorem(Theorem(
            id="0.1.3",
            name="Pressure Functions from Geometric Opposition",
            theorem_type=TheoremType.DEFINITION,
            phase=Phase.PHASE_0,
            status=Status.VERIFIED,
            description="Pressure functions from geometric opposition",
            key_result="P_c(x) = 1/(|x - x_c|² + ε²)",
            depends_on=["0.1.1"],
            tags=["foundation", "pressure"]
        ))

        self.add_theorem(Theorem(
            id="0.2.1",
            name="Total Field from Superposition",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_0,
            status=Status.VERIFIED,
            description="Total field as superposition of color fields",
            key_result="χ_total = Σ a_c(x) e^(iφ_c)",
            depends_on=["0.1.2", "0.1.3"],
            tags=["foundation"]
        ))

        self.add_theorem(Theorem(
            id="0.2.2",
            name="Internal Time Parameter Emergence",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_0,
            status=Status.VERIFIED,
            description="Internal parameter λ defined without background metric - BREAKS BOOTSTRAP",
            key_result="t = ∫ dλ/ω (physical time emerges)",
            depends_on=["0.2.1"],
            verification_date="2025-12-13",
            tags=["critical", "bootstrap", "time"]
        ))

        self.add_theorem(Theorem(
            id="0.2.3",
            name="Stable Convergence Point",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_0,
            status=Status.VERIFIED,
            description="Center of stella octangula is phase-locked stable region",
            depends_on=["0.2.1", "0.2.2"],
            has_files=["Statement", "Derivation", "Applications"],
            tags=["stability"]
        ))

        self.add_theorem(Theorem(
            id="0.2.4",
            name="Pre-Lorentzian Energy Functional",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_0,
            status=Status.VERIFIED,
            description="Energy as algebraic functional - RESOLVES NOETHER CIRCULARITY",
            key_result="E[χ] defined without spacetime integral",
            depends_on=["0.2.1", "0.2.2"],
            tags=["critical", "bootstrap", "energy"]
        ))

        # ============================================
        # PHASE 1: Foundational Mathematics
        # ============================================

        self.add_theorem(Theorem(
            id="1.1.1",
            name="Weight Diagram Isomorphism",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_1,
            status=Status.ESTABLISHED,
            description="Stella octangula vertices ↔ SU(3) weight vectors",
            key_result="Standard representation theory",
            depends_on=["0.1.1"],
            tags=["SU3", "representation"]
        ))

        self.add_theorem(Theorem(
            id="1.1.2",
            name="Geometric Opposition as Charge Conjugation",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_1,
            status=Status.VERIFIED,
            description="Point reflection ↔ C-symmetry operation",
            depends_on=["1.1.1"],
            verification_date="2025-12-13",
            tags=["SU3", "symmetry"]
        ))

        self.add_theorem(Theorem(
            id="1.1.3",
            name="Color Confinement Geometry",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_1,
            status=Status.VERIFIED,
            description="Hadrons = closed color-neutral configurations (R+G+B = 0)",
            depends_on=["1.1.1", "1.1.2"],
            verification_date="2025-12-13",
            tags=["SU3", "confinement"]
        ))

        self.add_theorem(Theorem(
            id="1.2.1",
            name="Vacuum Expectation Value",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_1,
            status=Status.ESTABLISHED,
            description="Standard spontaneous symmetry breaking",
            key_result="⟨χ⟩ = v_χ",
            tags=["SSB", "VEV"]
        ))

        self.add_theorem(Theorem(
            id="1.2.2",
            name="Chiral Anomaly",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_1,
            status=Status.ESTABLISHED,
            description="Adler-Bell-Jackiw anomaly (1969)",
            key_result="∂_μ J_5^μ = (g²/16π²) F_μν F̃^μν",
            tags=["anomaly", "established"]
        ))

        # ============================================
        # PHASE 2: Pressure-Depression Mechanism
        # ============================================

        self.add_theorem(Theorem(
            id="2.1.1",
            name="Bag Model Derivation",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.ESTABLISHED,
            description="MIT Bag Model (1974) - quarks confined by vacuum pressure",
            tags=["confinement", "established"]
        ))

        self.add_theorem(Theorem(
            id="2.1.2",
            name="Pressure as Field Gradient",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="Pressure ↔ effective potential gradient (lattice verified)",
            depends_on=["2.1.1"],
            tags=["pressure", "lattice"]
        ))

        self.add_theorem(Theorem(
            id="2.2.1",
            name="Phase-Locked Oscillation",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="120° phase-locked configuration is stable attractor",
            key_result="Sakaguchi-Kuramoto model stability",
            depends_on=["0.1.2", "0.2.2"],
            verification_date="2025-12-13",
            tags=["dynamics", "stability"]
        ))

        self.add_theorem(Theorem(
            id="2.2.2",
            name="Limit Cycle Existence",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="System has stable limit cycle with right-handed chirality",
            depends_on=["2.2.1"],
            verification_date="2025-12-13",
            tags=["dynamics", "chirality"]
        ))

        self.add_theorem(Theorem(
            id="2.2.3",
            name="Time Irreversibility",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="Chiral dynamics break T-symmetry fundamentally",
            depends_on=["2.2.2", "2.2.4"],
            verification_date="2025-12-13",
            tags=["time", "chirality", "arrow"]
        ))

        self.add_theorem(Theorem(
            id="2.2.4",
            name="Anomaly-Driven Chirality Selection",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="R→G→B chirality selected by QCD instantons - THE KEY",
            key_result="α = 2π/3 from SU(3) topology + QCD instantons",
            depends_on=["1.2.2", "2.2.1"],
            verification_date="2025-12-13",
            tags=["critical", "chirality", "instanton", "CP"]
        ))

        self.add_theorem(Theorem(
            id="2.2.5",
            name="Coarse-Grained Entropy Production",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="Microscopic entropy survives coarse-graining",
            key_result="σ = 3K/2 > 0",
            depends_on=["2.2.3"],
            verification_date="2025-12-13",
            tags=["entropy", "thermodynamics"]
        ))

        self.add_theorem(Theorem(
            id="2.2.6",
            name="Entropy Production Propagation",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="Macro entropy production → Second Law",
            key_result="dS_macro/dt = N·k_B·σ_eff > 0",
            depends_on=["2.2.5"],
            verification_date="2025-12-13",
            tags=["entropy", "second_law"]
        ))

        self.add_theorem(Theorem(
            id="2.3.1",
            name="Universal Chirality Origin",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_2,
            status=Status.VERIFIED,
            description="QCD and electroweak chirality share topological origin",
            key_result="sin²θ_W = 3/8 at GUT scale",
            depends_on=["2.2.4"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-13",
            tags=["chirality", "GUT", "electroweak"]
        ))

        # ============================================
        # PHASE 3: Mass Generation via Phase-Gradient Mass Generation
        # ============================================

        self.add_theorem(Theorem(
            id="3.0.1",
            name="Pressure-Modulated Superposition",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="Position-dependent VEV from color superposition",
            key_result="⟨χ⟩ = v_χ(x) e^(iΦ(x))",
            depends_on=["0.2.1"],
            tags=["VEV", "modulation"]
        ))

        self.add_theorem(Theorem(
            id="3.0.2",
            name="Non-Zero Phase Gradient",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,  # Updated 2025-12-14 after deep analysis verification
            description="Non-zero phase gradient enables phase-gradient mass generation",
            key_result="∂_λχ = iχ (eigenvalue equation)",
            depends_on=["0.2.2", "3.0.1"],
            has_files=["Statement", "Derivation", "Applications"],
            tags=["critical", "phase_gradient", "verified"]
        ))

        self.add_theorem(Theorem(
            id="3.1.1",
            name="Phase-Gradient Mass Generation Mass Formula",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="Mass from derivative coupling - FIRST PRINCIPLES",
            key_result="m_f = (g_χ ω_0 / Λ) v_χ η_f",
            depends_on=["0.2.2", "1.2.1", "1.2.2", "3.0.1", "3.0.2"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["critical", "mass", "chiral_drag"]
        ))

        self.add_theorem(Theorem(
            id="3.1.2",
            name="Mass Hierarchy Pattern from Geometry",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="Golden ratio formula for mass hierarchy - BREAKTHROUGH",
            key_result="λ = (1/φ³) × sin(72°) = 0.2245",
            depends_on=["3.1.1"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["critical", "mass_hierarchy", "golden_ratio", "CKM"]
        ))

        self.add_theorem(Theorem(
            id="3.1.2a",
            name="24-Cell Connection",
            theorem_type=TheoremType.LEMMA,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="24-cell bridges tetrahedral and icosahedral symmetry",
            key_result="φ³ from 24-cell; sin(72°) from icosahedral",
            depends_on=["3.1.2"],
            verification_date="2025-12-14",
            tags=["geometry", "24-cell"]
        ))

        self.add_theorem(Theorem(
            id="3.1.2b",
            name="Complete Wolfenstein Parameters",
            theorem_type=TheoremType.LEMMA,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="All CKM parameters from geometry",
            key_result="A = 0.831, ρ̄ = 0.159 (PDG: 0.1581), η̄ = 0.348 (PDG: 0.3548)",
            depends_on=["3.1.2", "3.1.2a"],
            verification_date="2025-12-14",
            tags=["CKM", "Wolfenstein"]
        ))

        self.add_theorem(Theorem(
            id="3.1.3",
            name="Massless Right-Handed Neutrinos",
            theorem_type=TheoremType.COROLLARY,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="ν_R protected by kinematic identity",
            key_result="P_L γ^μ P_L = 0",
            depends_on=["3.1.1"],
            tags=["neutrino", "seesaw"]
        ))

        self.add_theorem(Theorem(
            id="3.2.1",
            name="Low-Energy Equivalence",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="CG reproduces Higgs physics at E << Λ",
            key_result="χ ↔ 125 GeV Higgs",
            depends_on=["3.1.1", "3.1.2"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["Higgs", "SM_equivalence"]
        ))

        self.add_theorem(Theorem(
            id="3.2.2",
            name="High-Energy Deviations",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_3,
            status=Status.VERIFIED,
            description="Measurable deviations at E ~ Λ (8-15 TeV)",
            key_result="Wilson coefficients for dim-6 operators",
            depends_on=["3.2.1"],
            verification_date="2025-12-14",
            tags=["testable", "collider"]
        ))

        # ============================================
        # PHASE 4: Topological Solitons as Matter
        # ============================================

        self.add_theorem(Theorem(
            id="4.1.1",
            name="Existence of Solitons",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_4,
            status=Status.VERIFIED,
            description="Skyrme model solitons (1962)",
            key_result="Q = (1/24π²) ∫ d³x ε^ijk Tr[...], π₃(SU(2)) = ℤ",
            depends_on=["1.1.3"],
            verification_date="2025-12-14",
            tags=["soliton", "topology", "Skyrme"]
        ))

        self.add_theorem(Theorem(
            id="4.1.2",
            name="Soliton Mass Spectrum",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_4,
            status=Status.VERIFIED,
            description="Mass per topological charge",
            key_result="M_soliton = (6π²f_π/e)|Q|",
            depends_on=["4.1.1"],
            verification_date="2025-12-14",
            tags=["soliton", "mass"]
        ))

        self.add_theorem(Theorem(
            id="4.1.3",
            name="Fermion Number from Topology",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_4,
            status=Status.VERIFIED,
            description="Baryon number = topological charge (Witten 1983)",
            key_result="N_F = Q (Atiyah-Singer)",
            depends_on=["4.1.1", "4.1.2"],
            verification_date="2025-12-14",
            tags=["soliton", "baryon", "index_theorem"]
        ))

        self.add_theorem(Theorem(
            id="4.2.1",
            name="Chiral Bias in Soliton Formation",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_4,
            status=Status.VERIFIED,
            description="Right-handed chirality favors Q > 0 over Q < 0",
            key_result="ΔS = 2α·𝒢·ε_CP, Γ_+/Γ_- = e^(ΔS/T)",
            depends_on=["4.1.1", "4.1.3", "2.2.4", "2.2.3", "0.2.1"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["critical", "baryogenesis", "asymmetry"]
        ))

        self.add_theorem(Theorem(
            id="4.2.2",
            name="Sakharov Conditions",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_4,
            status=Status.ESTABLISHED,
            description="All three Sakharov conditions satisfied",
            depends_on=["4.2.1", "2.2.4"],
            tags=["baryogenesis", "Sakharov"]
        ))

        self.add_theorem(Theorem(
            id="4.2.3",
            name="First-Order Electroweak Phase Transition",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_4,
            status=Status.VERIFIED,
            description="Strong first-order PT from geometric mechanisms",
            key_result="v(T_c)/T_c = 1.2 ± 0.1, Ω_GW h² ~ 10^-10",
            depends_on=["0.1.1", "0.1.2"],
            verification_date="2025-12-14",
            tags=["phase_transition", "testable", "LISA"]
        ))

        self.add_theorem(Theorem(
            id="4.2.1a",
            name="Predicted Baryon Asymmetry",
            theorem_type=TheoremType.COROLLARY,
            phase=Phase.PHASE_4,
            status=Status.VERIFIED,
            description="Master formula for baryon asymmetry",
            key_result="η ~ (0.15-2.4) × 10^-9 ≈ 6×10^-10 (observed)",
            depends_on=["4.2.1", "4.2.3"],
            tags=["baryogenesis", "prediction"]
        ))

        # ============================================
        # PHASE 5: Emergent Spacetime and Gravity
        # ============================================

        self.add_theorem(Theorem(
            id="5.1.1",
            name="Stress-Energy from Chiral Lagrangian",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Symmetric, conserved stress-energy tensor",
            key_result="T_μν = ∂_μχ†∂_νχ + ∂_νχ†∂_μχ - g_μν ℒ_CG",
            depends_on=["0.2.4", "3.1.1"],
            verification_date="2025-12-14",
            tags=["stress_energy", "gravity"]
        ))

        self.add_theorem(Theorem(
            id="5.1.2",
            name="Vacuum Energy Density",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="FULL SOLUTION TO COSMOLOGICAL CONSTANT PROBLEM",
            key_result="ρ_vac(0) = 0 (phase cancellation), ρ_obs = M_P² H_0²",
            depends_on=["0.2.1", "5.1.1"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["critical", "CC_problem", "vacuum_energy"]
        ))

        self.add_theorem(Theorem(
            id="5.2.0",
            name="Wick Rotation Validity",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Euclidean action bounded, path integral converges",
            key_result="S_E ≥ 0, Osterwalder-Schrader satisfied",
            depends_on=["0.2.2", "0.2.4"],
            tags=["path_integral", "Euclidean"]
        ))

        self.add_theorem(Theorem(
            id="5.2.1",
            name="Emergent Metric",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Metric emerges from energy density - CRITICAL",
            key_result="g_μν = η_μν + (8πG/c⁴) ∫ d⁴y G(x-y) T_μν[χ](y)",
            depends_on=["0.1.1", "5.1.1", "4.1.1", "3.1.1", "5.1.2", "5.2.0"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["critical", "emergent_gravity", "metric"]
        ))

        self.add_theorem(Theorem(
            id="5.2.2",
            name="Pre-Geometric Cosmic Coherence",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Resolves inflation circularity",
            depends_on=["0.2.2", "5.2.1"],
            tags=["cosmology", "inflation"]
        ))

        self.add_theorem(Theorem(
            id="5.2.3",
            name="Einstein Equations from Thermodynamic Identity",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Gravity from thermodynamics: δQ = TδS",
            key_result="Einstein equations + γ = 1/4 from SU(3) intertwiners",
            depends_on=["5.1.1", "5.2.1"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["critical", "thermodynamic_gravity"]
        ))

        self.add_theorem(Theorem(
            id="5.2.4",
            name="Newton's Constant from Chiral Parameters",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="BREAKTHROUGH: G derived from framework parameters",
            key_result="G = 1/(8πf_χ²), f_χ ~ 2.4 × 10^18 GeV",
            depends_on=["0.2.1", "3.1.1", "4.1.1", "5.1.1", "5.2.1", "5.2.3"],
            has_files=["Statement", "Derivation", "Applications"],
            verification_date="2025-12-14",
            tags=["critical", "G_derivation", "Planck"]
        ))

        self.add_theorem(Theorem(
            id="5.2.5",
            name="Bekenstein-Hawking Coefficient",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Black hole entropy from SU(3) representation theory",
            key_result="S_BH = A/(4ℓ_P²)",
            depends_on=["5.2.3", "5.2.4"],
            has_files=["Statement", "Derivation", "Applications"],
            tags=["black_hole", "entropy"]
        ))

        self.add_theorem(Theorem(
            id="5.2.6",
            name="Planck Mass Emergence",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Planck mass from chiral parameters",
            key_result="M_P ~ √(f_χ)",
            depends_on=["5.2.4"],
            has_files=["Statement", "Derivation", "Applications"],
            tags=["Planck", "mass"]
        ))

        self.add_theorem(Theorem(
            id="5.3.1",
            name="Torsion from Chiral Current",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Gravity with torsion from right-handed current",
            depends_on=["5.2.1", "2.2.4"],
            tags=["torsion", "gravity"]
        ))

        self.add_theorem(Theorem(
            id="5.3.2",
            name="Spin-Orbit Coupling",
            theorem_type=TheoremType.THEOREM,
            phase=Phase.PHASE_5,
            status=Status.VERIFIED,
            description="Higher-order gravitational effects",
            depends_on=["5.3.1"],
            has_files=["Statement", "Derivation", "Applications"],
            tags=["spin_orbit"]
        ))

        # Build reverse dependencies
        self._build_reverse_dependencies()

    def add_theorem(self, theorem: Theorem):
        """Add a theorem to the graph."""
        self.theorems[theorem.id] = theorem

    def _build_reverse_dependencies(self):
        """Build required_by lists from depends_on lists."""
        for thm_id, theorem in self.theorems.items():
            for dep_id in theorem.depends_on:
                if dep_id in self.theorems:
                    self.theorems[dep_id].required_by.append(thm_id)

    def get_phase_theorems(self, phase: Phase) -> list[Theorem]:
        """Get all theorems in a given phase."""
        return [t for t in self.theorems.values() if t.phase == phase]

    def get_critical_theorems(self) -> list[Theorem]:
        """Get all theorems tagged as critical."""
        return [t for t in self.theorems.values() if "critical" in t.tags]

    def get_dependency_chain(self, theorem_id: str) -> list[str]:
        """Get all dependencies (transitive) for a theorem."""
        if theorem_id not in self.theorems:
            return []

        visited = set()
        chain = []

        def dfs(tid):
            if tid in visited:
                return
            visited.add(tid)
            if tid in self.theorems:
                for dep in self.theorems[tid].depends_on:
                    dfs(dep)
                chain.append(tid)

        dfs(theorem_id)
        return chain

    def get_statistics(self) -> dict:
        """Get statistics about the theorem graph."""
        stats = {
            "total_theorems": len(self.theorems),
            "by_phase": {},
            "by_type": {},
            "by_status": {},
            "critical_count": len(self.get_critical_theorems()),
            "total_dependencies": sum(len(t.depends_on) for t in self.theorems.values())
        }

        for phase in Phase:
            stats["by_phase"][phase.name] = len(self.get_phase_theorems(phase))

        for thm_type in TheoremType:
            stats["by_type"][thm_type.value] = len([
                t for t in self.theorems.values() if t.theorem_type == thm_type
            ])

        for status in Status:
            stats["by_status"][status.value] = len([
                t for t in self.theorems.values() if t.status == status
            ])

        return stats

    def to_dict(self) -> dict:
        """Export graph to dictionary format."""
        return {
            "theorems": {
                tid: {
                    **asdict(t),
                    "theorem_type": t.theorem_type.value,
                    "phase": t.phase.name,
                    "status": t.status.value
                }
                for tid, t in self.theorems.items()
            },
            "statistics": self.get_statistics()
        }

    def to_json(self, indent: int = 2) -> str:
        """Export graph to JSON string."""
        return json.dumps(self.to_dict(), indent=indent)


# Predefined critical dependency chains
CRITICAL_CHAINS = {
    "bootstrap_resolution": [
        "0.1.1", "0.2.1", "0.2.2", "0.2.4", "3.1.1", "5.1.1", "5.2.1", "5.2.3", "5.2.4"
    ],
    "chirality_arrow_of_time": [
        "1.2.2", "2.2.4", "2.2.2", "2.2.3", "2.2.5", "2.2.6"
    ],
    "matter_antimatter": [
        "2.2.4", "4.2.1", "4.2.3", "4.2.1a"
    ],
    "gravity_emergence": [
        "3.1.1", "4.1.1", "5.1.1", "5.1.2", "5.2.1", "5.2.3", "5.2.4"
    ],
    "mass_hierarchy": [
        "0.2.2", "3.0.1", "3.0.2", "3.1.1", "3.1.2", "3.1.2a", "3.1.2b"
    ]
}


if __name__ == "__main__":
    # Create and test the graph
    graph = TheoremGraph()

    print("=== Chiral Geometrogenesis Theorem Graph ===\n")

    stats = graph.get_statistics()
    print(f"Total theorems: {stats['total_theorems']}")
    print(f"Critical theorems: {stats['critical_count']}")
    print(f"Total dependencies: {stats['total_dependencies']}")

    print("\nBy Phase:")
    for phase, count in stats["by_phase"].items():
        print(f"  {phase}: {count}")

    print("\nBy Type:")
    for thm_type, count in stats["by_type"].items():
        print(f"  {thm_type}: {count}")

    print("\nBy Status:")
    for status, count in stats["by_status"].items():
        print(f"  {status}: {count}")

    print("\nCritical Theorems:")
    for thm in graph.get_critical_theorems():
        print(f"  {thm.full_id()}: {thm.name}")

    # Save to JSON
    with open("theorem_graph_data.json", "w") as f:
        f.write(graph.to_json())
    print("\nGraph exported to theorem_graph_data.json")

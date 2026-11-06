/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBottRepresentation
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The same-carrier Koszul symbol and its equivariant SG comparison

Public module ID: M0015.

ASI I, p.493, uses the full exterior algebra of the original complex space V,
not its dual. The positive Hermitian realization of that Koszul complex is
wedge plus contraction. This realization is the project's explicit expansion
of the complex, rather than a verbatim additional definition in ASI.

The positive symbol below is obtained from the original SG negative-square
symbol by the exact formula `-I * c(I*v)`. Contraction is conjugate-linear in
its vector argument, so this is wedge plus contraction on the same original
even and odd exterior carriers. Its support is still exactly the zero vector.

An actual scalar phase family connects the two symbols. It retains those
carriers and their original induced G actions throughout, and its inverse is
defined off the same zero control. Consequently the comparison does not rely
on forgetting the group action or on an unrecorded duality or determinant
twist. Dimension zero is included. The actual symbols, homotopy and same-carrier class
comparison are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped unitInterval

set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

local notation "Parity" i => CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i

/-- The actual positive Koszul block, on the original SG exterior parity spaces. -/
def koszulSymbolParity (v : V) (i : ZMod 2) : (Parity i) →ₗ[ℂ] (Parity (i + 1)) :=
  (-Complex.I) • cliffordSymbolParity (Complex.I • v) i

/-- The positive off-zero equivalence uses the same rotated SG map and scalar. -/
def koszulSymbolParityEquiv (v : V) (hv : v ≠ 0) (i : ZMod 2) :
    (Parity i) ≃ₗ[ℂ] (Parity (i + 1)) :=
  (cliffordSymbolParityEquiv (Complex.I • v)
    (smul_ne_zero Complex.I_ne_zero hv) i).trans
      (LinearEquiv.smulOfNeZero ℂ (Parity (i + 1)) (-Complex.I)
        (neg_ne_zero.mpr Complex.I_ne_zero))

/-- The explicit rotation family from the negative SG symbol to the positive Koszul symbol. -/
def koszulPhaseSymbolParity (t : unitInterval) (v : V) (i : ZMod 2) :
    (Parity i) →ₗ[ℂ] (Parity (i + 1)) :=
  Complex.exp (-((Real.pi * (t : ℝ) / 2 : ℝ) : ℂ) * Complex.I) •
    cliffordSymbolParity
      (Complex.exp (((Real.pi * (t : ℝ) / 2 : ℝ) : ℂ) * Complex.I) • v) i

/-- The positive symbol and both phase endpoints are the original exterior operators. -/
theorem koszulSymbolParity_formula :
    (∀ (v : V) (i : ZMod 2) (a : Parity i),
      (koszulSymbolParity v i a : ExteriorAlgebra ℂ V) =
        exteriorMultiplication v a.val + contraction v a.val) ∧
    (∀ (v : V) (i : ZMod 2), koszulPhaseSymbolParity 0 v i = cliffordSymbolParity v i) ∧
    (∀ (v : V) (i : ZMod 2), koszulPhaseSymbolParity 1 v i = koszulSymbolParity v i) := by
  /- Stage 1: wedge multiplication is complex-linear in v, whereas
  contraction is conjugate-linear in v under the original Hermitian form.
  Thus c(I*v)=I*(wedge(v)+contraction(v)). Multiplication by -I gives the
  displayed equality after the original parity inclusion.
  Stage 2: the actual phase at time zero is one. At time one its forward
  scalar is exp(I*pi/2)=I and its outer scalar is exp(-I*pi/2)=-I. Substitute
  these two scalar identities into the specified family. Both endpoint
  equalities are equalities of maps on the same original parity spaces;
  neither a dual exterior algebra nor a chosen generator occurs. -/
  constructor
  · intro v i a
    change (-Complex.I) • cliffordSymbol (Complex.I • v) a.val = _
    simp only [cliffordSymbol, LinearMap.sub_apply, exteriorMultiplication, contraction,
      map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_sub,
      smul_smul, Complex.conj_I, neg_mul, mul_neg, Complex.I_mul_I]
    simp
  constructor
  · intro v i
    simp [koszulPhaseSymbolParity]
  · intro v i
    have hp : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
      rw [Complex.exp_mul_I]
      simp
    have hn : Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
      rw [neg_mul, Complex.exp_neg]
      rw [hp]
      simp
    simp only [koszulPhaseSymbolParity, Set.Icc.coe_one, mul_one, hp, hn, koszulSymbolParity]

/-- The original positive boundary and its specified inverse are continuous off zero. -/
theorem koszulBott_boundary_continuity :
    letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
    letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial V (Parity 0)) ({0} : Set V)ᶜ) ↦
        (⟨z.proj, koszulSymbolParityEquiv z.proj.val (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.proj.property)
            0 z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial V (Parity 1)) ({0} : Set V)ᶜ))) ∧
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial V (Parity 1)) ({0} : Set V)ᶜ) ↦
        (⟨z.proj, (koszulSymbolParityEquiv z.proj.val (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.proj.property)
            0).symm z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial V (Parity 0)) ({0} : Set V)ᶜ))) := by
  /- Compose the existing SG boundary and inverse-continuity formulas with
  v -> I*v and the original constant scalar isomorphism on the odd fiber.
  Rotation preserves the nonzero locus. The model-topology product and
  restriction homeomorphisms retain the exact base point and exterior vector.
  No alternative topology or inverse map is selected. -/
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  let A : Set V := ({0} : Set V)ᶜ
  let e₀ : TotalSpace Unit (Bundle.Trivial V (Parity 0)) ≃ₜ V × Parity 0 :=
    (unitTotalHomeomorph (Parity 0) (Bundle.Trivial V (Parity 0))).trans
      (Bundle.Trivial.homeomorphProd V (Parity 0))
  let e₁ : TotalSpace Unit (Bundle.Trivial V (Parity 1)) ≃ₜ V × Parity 1 :=
    (unitTotalHomeomorph (Parity 1) (Bundle.Trivial V (Parity 1))).trans
      (Bundle.Trivial.homeomorphProd V (Parity 1))
  have h₀ := e₀.continuous.comp
    (Pullback.continuous_lift Unit (Bundle.Trivial V (Parity 0)) (Subtype.val : A → V))
  have h₁ := e₁.continuous.comp
    (Pullback.continuous_lift Unit (Bundle.Trivial V (Parity 1)) (Subtype.val : A → V))
  constructor
  · rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V (Parity 1))
      (Subtype.val : A → V)).continuous_iff]
    have hsym := (continuous_cliffordSymbolParity (V := V) 0).comp
      (((continuous_const (y := Complex.I)).smul h₀.fst).prodMk h₀.snd)
    have htotal := e₁.symm.continuous.comp
      (h₀.fst.prodMk ((continuous_const (y := -Complex.I)).smul hsym))
    exact (Pullback.continuous_proj Unit (Bundle.Trivial V (Parity 0))
      (Subtype.val : A → V)).prodMk htotal
  · rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V (Parity 0))
      (Subtype.val : A → V)).continuous_iff]
    have hbase : Continuous (fun z : TotalSpace Unit
        (Restrict (Bundle.Trivial V (Parity 1)) A) ↦
          (⟨Complex.I • z.proj.val, smul_ne_zero Complex.I_ne_zero (by
            simpa only [A, Set.mem_compl_iff, Set.mem_singleton_iff] using z.proj.property)⟩ :
              {v : V // v ≠ 0})) :=
      ((continuous_const (y := Complex.I)).smul h₁.fst).subtype_mk _
    have hsym := (continuous_cliffordSymbolParityEquiv_symm (V := V) 0).comp
      (hbase.prodMk ((continuous_const (y := (-Complex.I)⁻¹)).smul h₁.snd))
    have htotal := e₀.symm.continuous.comp (h₁.fst.prodMk hsym)
    exact (Pullback.continuous_proj Unit (Bundle.Trivial V (Parity 1))
      (Subtype.val : A → V)).prodMk htotal

/-- The positive Koszul support triple retains the original exterior bundles and zero control. -/
def koszulBottTriple :
    letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
    letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
    CompactSupportTriple (Bundle.Trivial V (Parity 0)) (Bundle.Trivial V (Parity 1)) :=
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  { control := {0}
    isCompact_control := isCompact_singleton
    boundary :=
      { linearEquiv := fun v ↦ koszulSymbolParityEquiv v.val (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using v.property) 0
        continuous_total := (koszulBott_boundary_continuity (V := V)).1
        continuous_symm := (koszulBott_boundary_continuity (V := V)).2 } }

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]
  (hunitary : ∀ (g : G) (u v : V), inner ℂ (g • u) (g • v) = inner ℂ u v)

include hunitary in
/-- The positive symbol intertwines exactly the same original exterior actions. -/
theorem koszulBottTriple_isEquivariant :
    letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
    letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
    (koszulBottTriple (V := V)).IsEquivariant
      (exteriorParityEquivariantStructure (G := G) (V := V) 0)
      (exteriorParityEquivariantStructure (G := G) (V := V) 1) := by
  /- The given complex-linear action commutes with rotation by I and fixes
  zero. The existing SG intertwining identity applied at I*v, followed by
  scalar multiplication by -I on the original odd fiber, gives the positive
  boundary square. These are the same parity actions, not their duals. -/
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  refine ⟨?_, ?_⟩
  · intro g x
    change g • x ∈ ({0} : Set V) ↔ x ∈ ({0} : Set V)
    simp only [Set.mem_singleton_iff]
    exact (DistribMulAction.toLinearEquiv ℂ V g).map_eq_zero_iff
  · intro g x a
    change (-Complex.I) • cliffordSymbolParity (Complex.I • (g • x.val)) 0
      (exteriorParityAction g 0 a) =
        exteriorParityAction g 1 ((-Complex.I) • cliffordSymbolParity (Complex.I • x.val) 0 a)
    rw [map_smul, ← smul_comm g Complex.I x.val]
    exact congrArg (fun b ↦ (-Complex.I) • b)
      (LinearMap.congr_fun
        (cliffordSymbolParity_equivariant hunitary g (Complex.I • x.val) 0) a)

/-- The actual same-carrier positive Koszul triple with its original induced G actions. -/
def equivariantKoszulBottTriple : EquivariantSupportBundleTriple G V :=
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  letI := isFiniteRank_model (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := isFiniteRank_model (Parity 1) (Bundle.Trivial V (Parity 1))
  EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily (Bundle.Trivial V (Parity 0)))
    (FiniteBundle.ofFamily (Bundle.Trivial V (Parity 1)))
    (koszulBottTriple (V := V))
    (exteriorParityEquivariantStructure (G := G) (V := V) 0)
    (exteriorParityEquivariantStructure (G := G) (V := V) 1)
    (koszulBottTriple_isEquivariant hunitary)

include hunitary in
/-- The displayed phase family gives an actual equivariant homotopy with the zero control. -/
theorem exists_equivariantKoszulBottHomotopy :
    letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
    letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
    ∃ H : CompactSupportTriple.EquivariantHomotopy
      (exteriorParityEquivariantStructure (G := G) (V := V) 0)
      (exteriorParityEquivariantStructure (G := G) (V := V) 1)
      (exteriorBottTriple V) (koszulBottTriple (V := V)),
      H.control = {0} ∧ ∀ (t : unitInterval) (x : (H.controlᶜ : Set V)) (a : Parity 0),
        H.homotopy.iso.linearEquiv (t, x) a = koszulPhaseSymbolParity t x.val 0 a := by
  /- Stage 1: take exactly the displayed phase-symbol family and the fixed
  zero control. Its rotation and outer scalar are never zero. Compose the
  original SG off-zero equivalence with these scalar maps to obtain its
  actual inverse. Both directions depend jointly continuously on time,
  the original nonzero base vector, and the exterior vector.
  Stage 2: equivalently the full operator is wedge(v) minus
  exp(-I*pi*t)*contraction(v). The existing phase-square identity gives
  -exp(-I*pi*t)*norm(v)^2, which stays nonzero for every nonzero v.
  This also checks the sign and both parity inverse identities throughout.
  Stage 3: the previously recorded endpoints are precisely the two actual
  triples. Complex linearity and unitarity intertwine every intermediate
  rotation with the same induced exterior action. Thus the cylinder is an
  equivariant homotopy with the exact required action formula, including
  the empty nonzero locus in dimension zero. -/
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  let A : Set V := ({0} : Set V)ᶜ
  -- Build the original phase equivalences before testing their cylinder topology.
  let α (t : unitInterval) : ℂ := Complex.exp (((Real.pi * (t : ℝ) / 2 : ℝ) : ℂ) * Complex.I)
  let β (t : unitInterval) : ℂ := Complex.exp (-((Real.pi * (t : ℝ) / 2 : ℝ) : ℂ) * Complex.I)
  have hα : Continuous α := by fun_prop
  have hβ : Continuous β := by fun_prop
  have hαne (t : unitInterval) : α t ≠ 0 := Complex.exp_ne_zero _
  have hβne (t : unitInterval) : β t ≠ 0 := Complex.exp_ne_zero _
  let e (t : unitInterval) (x : A) : (Parity 0) ≃ₗ[ℂ] (Parity 1) :=
    (cliffordSymbolParityEquiv (α t • x.val)
      (smul_ne_zero (hαne t) (by
        simpa only [A, Set.mem_compl_iff, Set.mem_singleton_iff] using x.property)) 0).trans
      (LinearEquiv.smulOfNeZero ℂ (Parity 1) (β t) (hβne t))
  let e₀ : TotalSpace Unit (Bundle.Trivial V (Parity 0)) ≃ₜ V × Parity 0 :=
    (unitTotalHomeomorph (Parity 0) (Bundle.Trivial V (Parity 0))).trans
      (Bundle.Trivial.homeomorphProd V (Parity 0))
  let e₁ : TotalSpace Unit (Bundle.Trivial V (Parity 1)) ≃ₜ V × Parity 1 :=
    (unitTotalHomeomorph (Parity 1) (Bundle.Trivial V (Parity 1))).trans
      (Bundle.Trivial.homeomorphProd V (Parity 1))
  let E₀ := Restrict (Bundle.Trivial V (Parity 0)) A
  let E₁ := Restrict (Bundle.Trivial V (Parity 1)) A
  let p : unitInterval × A → A := Prod.snd
  have hproj₀ := Pullback.continuous_proj Unit E₀ p
  have hproj₁ := Pullback.continuous_proj Unit E₁ p
  have h₀ := e₀.continuous.comp
    ((Pullback.continuous_lift Unit (Bundle.Trivial V (Parity 0)) (Subtype.val : A → V)).comp
      (Pullback.continuous_lift Unit E₀ p))
  have h₁ := e₁.continuous.comp
    ((Pullback.continuous_lift Unit (Bundle.Trivial V (Parity 1)) (Subtype.val : A → V)).comp
      (Pullback.continuous_lift Unit E₁ p))
  -- Both directions are continuous on the same two nested pullback total spaces.
  let f : Iso (p *ᵖ E₀) (p *ᵖ E₁) :=
    { linearEquiv := fun tx ↦ e tx.1 tx.2
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E₁ p).continuous_iff]
        refine hproj₀.prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V (Parity 1))
          (Subtype.val : A → V)).continuous_iff]
        have hsym := (continuous_cliffordSymbolParity (V := V) 0).comp
          (((hα.comp hproj₀.fst).smul h₀.fst).prodMk h₀.snd)
        have htotal := e₁.symm.continuous.comp
          (h₀.fst.prodMk ((hβ.comp hproj₀.fst).smul hsym))
        exact hproj₀.snd.prodMk htotal
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E₀ p).continuous_iff]
        refine hproj₁.prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V (Parity 0))
          (Subtype.val : A → V)).continuous_iff]
        have hbase : Continuous (fun z : TotalSpace Unit (p *ᵖ E₁) ↦
            (⟨α z.proj.1 • z.proj.2.val, smul_ne_zero (hαne z.proj.1) (by
              simpa only [A, Set.mem_compl_iff, Set.mem_singleton_iff]
                using z.proj.2.property)⟩ : {v : V // v ≠ 0})) :=
          ((hα.comp hproj₁.fst).smul h₁.fst).subtype_mk _
        have hsym := (continuous_cliffordSymbolParityEquiv_symm (V := V) 0).comp
          (hbase.prodMk (((hβ.inv₀ hβne).comp hproj₁.fst).smul h₁.snd))
        have htotal := e₀.symm.continuous.comp (h₁.fst.prodMk hsym)
        exact hproj₁.snd.prodMk htotal }
  -- Certify the exact endpoints, invariant control and the same action at each time.
  have hcontrol (g : G) (x : V) : g • x ∈ ({0} : Set V) ↔ x ∈ ({0} : Set V) := by
    simp only [Set.mem_singleton_iff]
    exact (DistribMulAction.toLinearEquiv ℂ V g).map_eq_zero_iff
  refine ⟨{ control := {0}
            isCompact_control := isCompact_singleton
            invariant_control := hcontrol
            left_control := Set.Subset.rfl
            right_control := Set.Subset.rfl
            homotopy := { iso := f, map_zero := ?_, map_one := ?_ }
            intertwines := ?_ }, rfl, ?_⟩
  · intro x a
    rw [CompactSupportTriple.enlarge_apply]
    change koszulPhaseSymbolParity 0 x.val 0 a = cliffordSymbolParity x.val 0 a
    exact LinearMap.congr_fun ((koszulSymbolParity_formula (V := V)).2.1 x.val 0) a
  · intro x a
    rw [CompactSupportTriple.enlarge_apply]
    change koszulPhaseSymbolParity 1 x.val 0 a = koszulSymbolParity x.val 0 a
    exact LinearMap.congr_fun ((koszulSymbolParity_formula (V := V)).2.2 x.val 0) a
  · intro t g x a
    change β t • cliffordSymbolParity (α t • (g • x.val)) 0
      (exteriorParityAction g 0 a) =
        exteriorParityAction g 1 (β t • cliffordSymbolParity (α t • x.val) 0 a)
    rw [map_smul, ← smul_comm g (α t) x.val]
    exact congrArg (fun b ↦ β t • b)
      (LinearMap.congr_fun (cliffordSymbolParity_equivariant hunitary g (α t • x.val) 0) a)
  · intro t x a
    rfl

/-- ASI's positive same-carrier Koszul realization has the original equivariant SG Bott class. -/
theorem equivariantKoszulBottTriple_class :
    (equivariantKoszulBottTriple hunitary).kZeroClass =
      equivariantExteriorBottClass hunitary := by
  /- The scalar unitary I induces F = exterior(I id) on the original carriers.
  Naturality gives c(Iv) F_even = F_odd c(v). Hence the constant global
  maps F_even and -I F_odd intertwine the original SG and positive Koszul
  boundaries. Both commute with the supplied complex-linear G action.
  Use these actual maps and the same zero control in the defining equivariant
  isomorphism relation. This direct square needs no compactness of G,
  cutoff, dual carrier, determinant twist or Bott periodicity. -/
  -- The fixed scalar rotation acts on the same exterior parity spaces.
  let j : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere]⟩
  let F (i : ZMod 2) : (Parity i) ≃ₗ[ℂ] (Parity i) :=
    { exteriorParityAction (G := Circle) j i with
      invFun := exteriorParityAction (G := Circle) j⁻¹ i
      left_inv := by
        intro a
        have h := LinearMap.congr_fun
          ((exteriorParityAction_properties (G := Circle) (V := V) i).2.1 j⁻¹ j) a
        simpa [exteriorParityAction_properties] using h.symm
      right_inv := by
        intro a
        have h := LinearMap.congr_fun
          ((exteriorParityAction_properties (G := Circle) (V := V) i).2.1 j j⁻¹) a
        simpa [exteriorParityAction_properties] using h.symm }
  -- The original Clifford naturality applies to the genuine scalar unitary action.
  have hcircle (z : Circle) (u v : V) : inner ℂ (z • u) (z • v) = inner ℂ u v := by
    change inner ℂ ((z : ℂ) • u) ((z : ℂ) • v) = inner ℂ u v
    rw [inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [Complex.conj_mul', Circle.norm_coe]
    simp
  have hsymbol (v : V) (i : ZMod 2) (a : Parity i) :
      cliffordSymbolParity (Complex.I • v) i (F i a) = F (i + 1) (cliffordSymbolParity v i a) :=
    LinearMap.congr_fun (cliffordSymbolParity_equivariant hcircle j v i) a
  -- Complex linearity makes the scalar exterior rotation commute with G.
  have hcomm (g : G) (i : ZMod 2) (a : Parity i) :
      F i (exteriorParityAction g i a) = exteriorParityAction g i (F i a) := by
    apply Subtype.ext
    let fI := ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V j)
    let fg := ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)
    have hmap : fI.comp fg = fg.comp fI := by
      apply ExteriorAlgebra.hom_ext
      ext v
      simp only [fI, fg, LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        ExteriorAlgebra.map_apply_ι]
      change ExteriorAlgebra.ι ℂ (Complex.I • (g • v)) =
        ExteriorAlgebra.ι ℂ (g • (Complex.I • v))
      rw [smul_comm g Complex.I v]
    exact AlgHom.congr_fun hmap a.val
  letI := modelTopology (Parity 0) (Bundle.Trivial V (Parity 0))
  letI := modelTopology (Parity 1) (Bundle.Trivial V (Parity 1))
  let e₀ : TotalSpace Unit (Bundle.Trivial V (Parity 0)) ≃ₜ V × Parity 0 :=
    (unitTotalHomeomorph (Parity 0) (Bundle.Trivial V (Parity 0))).trans
      (Bundle.Trivial.homeomorphProd V (Parity 0))
  let e₁ : TotalSpace Unit (Bundle.Trivial V (Parity 1)) ≃ₜ V × Parity 1 :=
    (unitTotalHomeomorph (Parity 1) (Bundle.Trivial V (Parity 1))).trans
      (Bundle.Trivial.homeomorphProd V (Parity 1))
  -- Keep the base point fixed and use these continuous constant fiber isomorphisms.
  let u : Iso (Bundle.Trivial V (Parity 0)) (Bundle.Trivial V (Parity 0)) :=
    { linearEquiv := fun _ ↦ F 0
      continuous_total := e₀.symm.continuous.comp
        (e₀.continuous.fst.prodMk ((F 0).toLinearMap.continuous_of_finiteDimensional.comp
          e₀.continuous.snd))
      continuous_symm := e₀.symm.continuous.comp
        (e₀.continuous.fst.prodMk ((F 0).symm.toLinearMap.continuous_of_finiteDimensional.comp
          e₀.continuous.snd)) }
  let w : (Parity 1) ≃ₗ[ℂ] (Parity 1) := (F 1).trans
    (LinearEquiv.smulOfNeZero ℂ (Parity 1) (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero))
  let v : Iso (Bundle.Trivial V (Parity 1)) (Bundle.Trivial V (Parity 1)) :=
    { linearEquiv := fun _ ↦ w
      continuous_total := e₁.symm.continuous.comp
        (e₁.continuous.fst.prodMk (w.toLinearMap.continuous_of_finiteDimensional.comp
          e₁.continuous.snd))
      continuous_symm := e₁.symm.continuous.comp
        (e₁.continuous.fst.prodMk (w.symm.toLinearMap.continuous_of_finiteDimensional.comp
          e₁.continuous.snd)) }
  have hu : u.IsEquivariant (exteriorParityEquivariantStructure (G := G) (V := V) 0)
      (exteriorParityEquivariantStructure (G := G) (V := V) 0) := by
    intro g x a
    exact hcomm g 0 a
  have hv : v.IsEquivariant (exteriorParityEquivariantStructure (G := G) (V := V) 1)
      (exteriorParityEquivariantStructure (G := G) (V := V) 1) := by
    intro g x a
    change (-Complex.I) • F 1 (exteriorParityAction g 1 a) =
      exteriorParityAction g 1 ((-Complex.I) • F 1 a)
    rw [map_smul, hcomm]
  -- The exact zero-controlled boundary square is a defining quotient relation.
  have hiso : (equivariantExteriorBottTriple hunitary).IsIsomorphic
      (equivariantKoszulBottTriple hunitary) := by
    refine ⟨{0}, isCompact_singleton, ?_, Set.Subset.rfl, Set.Subset.rfl, u, v, hu, hv, ?_⟩
    · intro g x
      simp only [Set.mem_singleton_iff]
      exact (DistribMulAction.toLinearEquiv ℂ V g).map_eq_zero_iff
    · intro x a
      rw [CompactSupportTriple.enlarge_apply, CompactSupportTriple.enlarge_apply]
      change (-Complex.I) • F 1 (cliffordSymbolParity x.val 0 a) =
        (-Complex.I) • cliffordSymbolParity (Complex.I • x.val) 0 (F 0 a)
      exact congrArg (fun b ↦ (-Complex.I) • b) (hsymbol x.val 0 a).symm
  exact ((equivariantSupportTripleKZero_generator_relations (G := G) (X := V)).1 _ _ hiso).symm

end AtiyahSinger

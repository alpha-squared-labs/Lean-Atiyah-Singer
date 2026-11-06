/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.EquivariantKoszulSymbol
public import AtiyahSinger.Geometry.SphereComplexifiedTangent
public import AtiyahSinger.Geometry.SphereDeRhamSymbol
public import AtiyahSinger.Geometry.SphereTangentCoordinates
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.ExteriorKoszulContinuity

/-!
# The global sphere exterior symbol and its two-pole deformation

Public module ID: M2160.

AL02. On the original native sphere tangent bundle, the complex vector at (x,v)
is `1 tensor v - I*s tensor grad(height)(x)`. Its exterior multiplication is
the global source Koszul differential. Positive compression uses the explicit
complexified round metric, installed only locally inside the algebraic adapter.
The pullback exterior bundles keep their original induced total topologies.

At s=0 the support is the compact native zero section; for nonzero s it is the
two actual zero tangent vectors at the poles. The same zero section controls
the entire homotopy. An actual equivariant cylinder boundary with that control
compares the exact endpoints. No pointwise family of unrelated K classes or
analytical Hodge index is used to define the de Rham symbol class.

ASI I, pp.499--500, Lemma (3.2), supplies the local Koszul deformation.
This realization uses the original native tangent fibers and derivative action.
The continuity argument retains the varying round metric in native linear
charts, without assuming that those charts are isometries. The actual boundary
and common-control cylinder retain these specified data throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct unitInterval

set_option maxSynthPendingDepth 25

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent sphereComplexifiedTangentTopology
  isFiniteRank_sphereComplexifiedTangent exteriorTopology exteriorParityTopology
  isFiniteRank_exteriorParity

/-- The original continuous tangent projection, used for both exterior pullback bundles. -/
def orthogonalSphereTangentProjection (r : ℕ) :
    C(TangentBundle (𝓡 r) (OrthogonalSphere r), OrthogonalSphere r) :=
  ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj
    (EuclideanSpace ℝ (Fin r)) (fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x)⟩

/-- The original parity exterior bundle pulled to the native tangent base. -/
def sphereDeRhamParityBundle (r : ℕ) (i : ZMod 2) :
    FiniteBundle (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  (FiniteBundle.ofFamily (fun x : OrthogonalSphere r ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i)).pullback
      (orthogonalSphereTangentProjection r)

/-- The original exterior derivative action pulled along the same equivariant projection. -/
def sphereDeRhamParityAction (r : ℕ) (i : ZMod 2) :
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ)
      (sphereDeRhamParityBundle r i).Fiber :=
  (sphereExteriorParityEquivariantStructure r i).pullback
    (orthogonalSphereTangentProjection r) (fun _ _ ↦ rfl)

/-- The global source deformation uses the actual tangent vector and specified height gradient. -/
def sphereDeRhamVector (r : ℕ) (s : ℝ)
    (z : TangentBundle (𝓡 r) (OrthogonalSphere r)) : SphereComplexifiedTangent r z.proj :=
  (1 : ℂ) ⊗ₜ[ℝ] z.snd - ((s : ℂ) * Complex.I) ⊗ₜ[ℝ]
    orthogonalSphereHeightGradient r z.proj

/-- The actual exterior differential on the original complexified native tangent fiber. -/
def sphereDeRhamDifferential (r : ℕ) (s : ℝ)
    (z : TangentBundle (𝓡 r) (OrthogonalSphere r)) :
    ExteriorAlgebra ℂ (SphereComplexifiedTangent r z.proj) →ₗ[ℂ]
      ExteriorAlgebra ℂ (SphereComplexifiedTangent r z.proj) :=
  Algebra.lmul ℂ _ (ExteriorAlgebra.ι ℂ (sphereDeRhamVector r s z))

/-- Positive Koszul compression uses the given round Hermitian form, without changing topology. -/
def sphereDeRhamSymbol (r : ℕ) (s : ℝ)
    (z : TangentBundle (𝓡 r) (OrthogonalSphere r)) :
    (sphereDeRhamParityBundle r 0).Fiber z →ₗ[ℂ]
      (sphereDeRhamParityBundle r 1).Fiber z :=
  let h := (sphereComplexifiedRoundMetric r).toCore z.proj
  letI : NormedAddCommGroup (SphereComplexifiedTangent r z.proj) := h.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (SphereComplexifiedTangent r z.proj) :=
    InnerProductSpace.ofCore h.toCore
  koszulSymbolParity (sphereDeRhamVector r s z) 0

/-- The off-support equivalence is the specified positive Koszul map and its actual inverse. -/
def sphereDeRhamSymbolEquiv (r : ℕ) (s : ℝ)
    (z : TangentBundle (𝓡 r) (OrthogonalSphere r)) (hz : sphereDeRhamVector r s z ≠ 0) :
    (sphereDeRhamParityBundle r 0).Fiber z ≃ₗ[ℂ]
      (sphereDeRhamParityBundle r 1).Fiber z :=
  let h := (sphereComplexifiedRoundMetric r).toCore z.proj
  letI : NormedAddCommGroup (SphereComplexifiedTangent r z.proj) := h.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (SphereComplexifiedTangent r z.proj) :=
    InnerProductSpace.ofCore h.toCore
  koszulSymbolParityEquiv (sphereDeRhamVector r s z) hz 0

/-- The actual deformation has the original compact support and the specified equivariance. -/
theorem sphereDeRhamVector_properties (r : ℕ) :
    (∀ (s : ℝ) (z : TangentBundle (𝓡 r) (OrthogonalSphere r)),
      sphereDeRhamVector r s z = 0 ↔ z.snd = 0 ∧
        (s = 0 ∨ z.proj = orthogonalSpherePole r false ∨
          z.proj = orthogonalSpherePole r true)) ∧
    (∀ s : ℝ, IsCompact {z : TangentBundle (𝓡 r) (OrthogonalSphere r) |
      sphereDeRhamVector r s z = 0}) ∧
    ∀ (s : ℝ) (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (z : TangentBundle (𝓡 r) (OrthogonalSphere r)),
      sphereDeRhamVector r s (A • z) =
        sphereComplexifiedTangentAction r A z.proj (sphereDeRhamVector r s z) := by
  /- Stage 1: the original real/imaginary equivalence sends the displayed
  tensor to (v,-s*Y). Thus it vanishes exactly when v=0 and s=0 or Y=0.
  Apply the specified gradient's exact two-pole zero-set theorem.
  Stage 2: at s=0 the control is the image of the native continuous zero
  section of the compact sphere. At nonzero s it is the two zero tangent
  vectors at the actual poles, a finite compact subset of that section.
  This includes rank zero, where the sphere itself consists of two points.
  Stage 3: the original derivative is real linear, its complex extension
  preserves pure tensors, and the actual gradient is equivariant. These
  three facts give precisely the displayed moving-fiber equality. -/
  -- Real and imaginary components recover the actual tangent vector and height gradient.
  have hcoords (s : ℝ) (z : TangentBundle (𝓡 r) (OrthogonalSphere r)) :
      complexificationReIm (TangentSpace (𝓡 r) z.proj) (sphereDeRhamVector r s z) =
        (z.snd, -(s • orthogonalSphereHeightGradient r z.proj)) := by
    simp [sphereDeRhamVector, map_sub, (complexificationReIm_properties _).1]
  have hzero (s : ℝ) (z : TangentBundle (𝓡 r) (OrthogonalSphere r)) :
      sphereDeRhamVector r s z = 0 ↔ z.snd = 0 ∧
        (s = 0 ∨ z.proj = orthogonalSpherePole r false ∨
          z.proj = orthogonalSpherePole r true) := by
    rw [← (complexificationReIm (TangentSpace (𝓡 r) z.proj)).map_eq_zero_iff, hcoords]
    simp only [Prod.mk_eq_zero, neg_eq_zero, smul_eq_zero,
      orthogonalSphereHeightGradient_eq_zero_iff]
  refine ⟨hzero, ?_, ?_⟩
  · intro s
    by_cases hs : s = 0
    · -- At time zero the support is exactly the original compact zero section.
      subst s
      have hset : {z : TangentBundle (𝓡 r) (OrthogonalSphere r) |
          sphereDeRhamVector r 0 z = 0} =
          Set.range (zeroSection (EuclideanSpace ℝ (Fin r))
            (fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x)) := by
        ext z
        simp only [hzero, true_or, and_true, Set.mem_ofPred_eq, Set.mem_range]
        constructor
        · intro hz
          exact ⟨z.proj, congrArg (TotalSpace.mk z.proj) hz.symm⟩
        · rintro ⟨x, rfl⟩
          rfl
      rw [hset]
      exact isCompact_range (Bundle.Trivialization.continuous_zeroSection ℝ)
    · -- Nonzero time leaves precisely the two zero tangent vectors at the fixed poles.
      let south : TangentBundle (𝓡 r) (OrthogonalSphere r) :=
        ⟨orthogonalSpherePole r false, 0⟩
      let north : TangentBundle (𝓡 r) (OrthogonalSphere r) :=
        ⟨orthogonalSpherePole r true, 0⟩
      have hset : {z : TangentBundle (𝓡 r) (OrthogonalSphere r) |
          sphereDeRhamVector r s z = 0} = {south, north} := by
        ext z
        rw [Set.mem_ofPred_eq, hzero]
        simp only [hs, false_or, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hz, hx | hx⟩
          · left
            cases z with
            | mk x v =>
              dsimp only at hx hz
              subst x
              exact congrArg (TotalSpace.mk _) hz
          · right
            cases z with
            | mk x v =>
              dsimp only at hx hz
              subst x
              exact congrArg (TotalSpace.mk _) hz
        · rintro (rfl | rfl)
          · exact ⟨rfl, Or.inl rfl⟩
          · exact ⟨rfl, Or.inr rfl⟩
      rw [hset]
      exact Set.Finite.isCompact (Set.toFinite _)
  · -- The same real derivative transports both pure tensors and the given gradient.
    intro s A z
    change (1 : ℂ) ⊗ₜ[ℝ] _ - ((s : ℂ) * Complex.I) ⊗ₜ[ℝ] _ = _
    simp only [sphereDeRhamVector, map_sub]
    erw [sphereComplexifiedTangentAction, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, orthogonalSphereHeightGradient_equivariant]
    rfl

set_option maxHeartbeats 800000 in
-- Normalize the original pulled exterior actions and their deformation boundary inverses.
/-- The positive boundary and its inverse are continuous in the original pullback topologies. -/
theorem sphereDeRhamSymbol_boundary_continuity (r : ℕ) (s : ℝ) :
    let K := {z : TangentBundle (𝓡 r) (OrthogonalSphere r) | sphereDeRhamVector r s z = 0}
    Continuous (fun z : TotalSpace Unit
      (Restrict (sphereDeRhamParityBundle r 0).Fiber Kᶜ) ↦
        (⟨z.proj, sphereDeRhamSymbolEquiv r s z.proj.val z.proj.property z.snd⟩ :
          TotalSpace Unit (Restrict (sphereDeRhamParityBundle r 1).Fiber Kᶜ))) ∧
    Continuous (fun z : TotalSpace Unit
      (Restrict (sphereDeRhamParityBundle r 1).Fiber Kᶜ) ↦
        (⟨z.proj, (sphereDeRhamSymbolEquiv r s z.proj.val z.proj.property).symm z.snd⟩ :
          TotalSpace Unit (Restrict (sphereDeRhamParityBundle r 0).Fiber Kᶜ))) := by
  let C := SphereComplexifiedTangent r
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  let K : Set T := {z | sphereDeRhamVector r s z = 0}
  let P₀ (x : OrthogonalSphere r) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C x)) 0
  let P₁ (x : OrthogonalSphere r) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C x)) 1
  let E₀ := Restrict (sphereDeRhamParityBundle r 0).Fiber Kᶜ
  let E₁ := Restrict (sphereDeRhamParityBundle r 1).Fiber Kᶜ
  let : IsFiniteRank E₀ := isFiniteRank_restrict Kᶜ
  let : IsFiniteRank E₁ := isFiniteRank_restrict Kᶜ
  -- The original real/imaginary bundle comparison proves continuity of the deformation vector.
  have hvector : Continuous (fun z : T ↦
      (⟨z.proj, sphereDeRhamVector r s z⟩ : TotalSpace Unit C)) := by
    have hjoint : Continuous (fun z : ℝ × T ↦
        (⟨z.2.proj, sphereDeRhamVector r z.1 z.2⟩ : TotalSpace Unit C)) := by
      let V := EuclideanSpace ℝ (Fin r)
      let E := fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x
      let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
      let hp : C(T, OrthogonalSphere r) := orthogonalSphereTangentProjection r
      have hscale : Continuous (fun z : ℝ × T ↦ (⟨z.2.proj, z.1 • z.2.snd⟩ : T)) := by
        apply continuous_iff_continuousAt.mpr
        intro z
        apply (FiberBundle.continuousAt_totalSpace V _).mpr
        refine ⟨hp.continuous.continuousAt.comp continuousAt_snd, ?_⟩
        let e := trivializationAt V E z.2.proj
        have hc : ContinuousAt (fun w : ℝ × T ↦ (e w.2).2) z :=
          (e.continuousAt (FiberBundle.mem_trivializationAt_proj_source)).snd.comp
            continuousAt_snd
        apply (continuousAt_fst.smul hc).congr_of_eventuallyEq
        have hb : ∀ᶠ w : ℝ × T in nhds z, w.2.proj ∈ e.baseSet :=
          (hp.continuous.comp continuous_snd).continuousAt.eventually
            (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt V E z.2.proj))
        filter_upwards [hb] with w hw
        exact (e.linear ℝ hw).2 w.1 w.2.snd
      let ce := complexificationDoubleTotalHomeomorph V E
      apply ce.isInducing.continuous_iff.mpr
      apply (FiberBundle.Prod.isInducing_diag V E V E).continuous_iff.mpr
      have hgrad : Continuous (fun z : ℝ × T ↦
          (⟨z.2.proj, orthogonalSphereHeightGradient r z.2.proj⟩ : T)) :=
        (continuous_orthogonalSphereHeightGradient r).comp
          (hp.continuous.comp continuous_snd)
      have him : Continuous (fun z : ℝ × T ↦
          (⟨z.2.proj, -(z.1 • orthogonalSphereHeightGradient r z.2.proj)⟩ : T)) := by
        apply (hscale.comp (continuous_fst.neg.prodMk hgrad)).congr
        intro z
        change (⟨z.2.proj, (-z.1) • orthogonalSphereHeightGradient r z.2.proj⟩ : T) = _
        rw [neg_smul]
      apply (continuous_snd.prodMk him).congr
      intro z
      dsimp only [Function.comp_apply]
      change _ = ((⟨z.2.proj,
        (complexificationReIm (E z.2.proj) (sphereDeRhamVector r z.1 z.2)).1⟩ : T),
        (⟨z.2.proj,
        (complexificationReIm (E z.2.proj) (sphereDeRhamVector r z.1 z.2)).2⟩ : T))
      simp only [sphereDeRhamVector, map_sub, (complexificationReIm_properties _).1]
      simp
      rfl
    exact hjoint.comp (continuous_const.prodMk continuous_id)
  let := sumTopology (E := C) (F := fun x ↦ ExteriorAlgebra ℂ (C x))
  let D₀ := TotalSpace Unit E₀
  have hbase : Continuous (fun z : D₀ ↦ z.proj) := continuous_proj (E := E₀)
  have htan : Continuous (fun z : D₀ ↦ z.proj.val) :=
    continuous_subtype_val.comp hbase
  have hrestriction : Continuous (fun z : D₀ ↦
      (⟨z.proj.val, z.snd⟩ : TotalSpace Unit (sphereDeRhamParityBundle r 0).Fiber)) :=
    Pullback.continuous_lift Unit (sphereDeRhamParityBundle r 0).Fiber
      (Subtype.val : (Kᶜ : Set T) → T)
  have hprojection : Continuous (fun z : TotalSpace Unit (sphereDeRhamParityBundle r 0).Fiber ↦
      (⟨z.proj.proj, z.snd⟩ : TotalSpace Unit P₀)) :=
    Pullback.continuous_lift Unit P₀ (orthogonalSphereTangentProjection r)
  have hparity : Continuous (fun z : D₀ ↦
      (⟨z.proj.val.proj, z.snd⟩ : TotalSpace Unit P₀)) := hprojection.comp hrestriction
  have hambient : Continuous (fun z : D₀ ↦
      (⟨z.proj.val.proj, z.snd.val⟩ : TotalSpace Unit
        (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x)))) :=
    continuous_induced_dom.comp hparity
  -- Apply the continuous wedge-plus-contraction operator for exactly the original round form.
  have hpair : Continuous (fun z : D₀ ↦
      (⟨z.proj.val.proj, (sphereDeRhamVector r s z.proj.val, z.snd.val)⟩ :
        TotalSpace Unit (C ×ᵇ (fun x ↦ ExteriorAlgebra ℂ (C x))))) := by
    apply continuous_induced_rng.mpr
    exact (hvector.comp htan).prodMk hambient
  let ell (x : OrthogonalSphere r) (v : C x) : C x →ₗ[ℂ] ℂ :=
    let core := (sphereComplexifiedRoundMetric r).toCore x
    letI : NormedAddCommGroup (C x) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (C x) := InnerProductSpace.ofCore core.toCore
    innerₛₗ ℂ v
  -- Normalize the metric adapter before specializing to the native sphere fibers.
  have hnormalized {X : Type} [TopologicalSpace X]
      (E : X → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      (h : ContinuousHermitianMetric E) :
      let _ := sumTopology (E := E) (F := fun x ↦ ExteriorAlgebra ℂ (E x))
      Continuous (fun z : TotalSpace Unit (E ×ᵇ (fun x ↦ ExteriorAlgebra ℂ (E x))) ↦
        (⟨z.proj, ExteriorAlgebra.ι ℂ z.snd.1 * z.snd.2 +
          CliffordAlgebra.contractLeft
            (let core := h.toCore z.proj
             letI : NormedAddCommGroup (E z.proj) := core.toNormedAddCommGroup
             letI : InnerProductSpace ℂ (E z.proj) := InnerProductSpace.ofCore core.toCore
             innerₛₗ ℂ z.snd.1) z.snd.2⟩ :
              TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
    exact continuous_exteriorMultiplication_add_contraction E h
  -- Fix the original exterior operations explicitly across the pullback type aliases.
  have hpositive : Continuous (fun z : D₀ ↦
      (⟨z.proj.val.proj,
        @Add.add (ExteriorAlgebra ℂ (C z.proj.val.proj)) inferInstance
          (@Mul.mul (ExteriorAlgebra ℂ (C z.proj.val.proj)) inferInstance
            (ExteriorAlgebra.ι ℂ (sphereDeRhamVector r s z.proj.val)) z.snd.val)
          (CliffordAlgebra.contractLeft
            (ell z.proj.val.proj (sphereDeRhamVector r s z.proj.val)) z.snd.val)⟩ :
              TotalSpace Unit (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x)))) :=
    (hnormalized C (sphereComplexifiedRoundMetric r)).comp hpair
  -- Identify this continuous ambient operator with the specified positive symbol.
  have hformula (y : T) (b : P₀ y.proj) :
      (sphereDeRhamSymbol r s y b).val =
        ExteriorAlgebra.ι ℂ (sphereDeRhamVector r s y) * b.val +
          CliffordAlgebra.contractLeft (ell y.proj (sphereDeRhamVector r s y)) b.val := by
    let core := (sphereComplexifiedRoundMetric r).toCore y.proj
    let : NormedAddCommGroup (C y.proj) := core.toNormedAddCommGroup
    let : InnerProductSpace ℂ (C y.proj) := InnerProductSpace.ofCore core.toCore
    exact (koszulSymbolParity_formula (V := C y.proj)).1
      (sphereDeRhamVector r s y) 0 b
  have hsymbol : Continuous (fun z : D₀ ↦
      (⟨z.proj.val.proj, (sphereDeRhamSymbol r s z.proj.val z.snd).val⟩ :
        TotalSpace Unit (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x)))) := by
    apply hpositive.congr
    intro z
    exact congrArg
      (fun b : ExteriorAlgebra ℂ (C z.proj.val.proj) ↦
        (⟨z.proj.val.proj, b⟩ : TotalSpace Unit
          (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x))))
      (hformula z.proj.val z.snd).symm
  -- Recover parity and then both original pullback total topologies.
  have hsymbolParity : Continuous (fun z : D₀ ↦
      (⟨z.proj.val.proj, sphereDeRhamSymbol r s z.proj.val z.snd⟩ :
        TotalSpace Unit P₁)) := continuous_induced_rng.mpr hsymbol
  have hsymbolPullback : Continuous (fun z : D₀ ↦
      (⟨z.proj.val, sphereDeRhamSymbol r s z.proj.val z.snd⟩ :
        TotalSpace Unit (sphereDeRhamParityBundle r 1).Fiber)) :=
    (inducing_pullbackTotalSpaceEmbedding Unit P₁
      (orthogonalSphereTangentProjection r)).continuous_iff.mpr (htan.prodMk hsymbolParity)
  have hforward : Continuous (fun z : D₀ ↦
      (⟨z.proj, sphereDeRhamSymbolEquiv r s z.proj.val z.proj.property z.snd⟩ :
        TotalSpace Unit E₁)) :=
    (inducing_pullbackTotalSpaceEmbedding Unit (sphereDeRhamParityBundle r 1).Fiber
      (Subtype.val : (Kᶜ : Set T) → T)).continuous_iff.mpr (hbase.prodMk hsymbolPullback)
  -- The same forward fiber equivalence determines its inverse; finite rank supplies continuity.
  let f : Hom E₀ E₁ :=
    { linearMap := fun z ↦ (sphereDeRhamSymbolEquiv r s z.val z.property).toLinearMap
      continuous_total := hforward }
  let j := f.toIso (fun z ↦ (sphereDeRhamSymbolEquiv r s z.val z.property).bijective)
  have heq (z : (Kᶜ : Set T)) : j.linearEquiv z = sphereDeRhamSymbolEquiv r s z.val z.property := by
    apply LinearEquiv.ext
    intro a
    rfl
  refine ⟨hforward, ?_⟩
  exact j.continuous_symm.congr (fun z ↦ congrArg (TotalSpace.mk z.proj)
    (congrArg (fun e ↦ e.symm z.snd) (heq z.proj)))

/-- The actual compact-support family of compressed source exterior complexes. -/
def sphereDeRhamTriple (r : ℕ) (s : ℝ) :
    CompactSupportTriple (sphereDeRhamParityBundle r 0).Fiber
      (sphereDeRhamParityBundle r 1).Fiber where
  control := {z | sphereDeRhamVector r s z = 0}
  isCompact_control := (sphereDeRhamVector_properties r).2.1 s
  boundary :=
    { linearEquiv := fun z ↦ sphereDeRhamSymbolEquiv r s z.val z.property
      continuous_total := (sphereDeRhamSymbol_boundary_continuity r s).1
      continuous_symm := (sphereDeRhamSymbol_boundary_continuity r s).2 }

set_option maxHeartbeats 800000 in
-- Normalize the original metric contraction and the same equivariant deformation slice.
set_option backward.isDefEq.respectTransparency.types false in
/-- Every slice intertwines the original pulled exterior actions, with its own invariant control. -/
theorem sphereDeRhamTriple_isEquivariant (r : ℕ) (s : ℝ) :
    (sphereDeRhamTriple r s).IsEquivariant
      (sphereDeRhamParityAction r 0) (sphereDeRhamParityAction r 1) := by
  let h := sphereComplexifiedRoundMetric r
  let ell (x : OrthogonalSphere r) (v : SphereComplexifiedTangent r x) :
      SphereComplexifiedTangent r x →ₗ[ℂ] ℂ :=
    let core := h.toCore x
    letI : NormedAddCommGroup (SphereComplexifiedTangent r x) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (SphereComplexifiedTangent r x) :=
      InnerProductSpace.ofCore core.toCore
    innerₛₗ ℂ v
  refine ⟨?_, ?_⟩
  · -- The actual vector and injective derivative preserve the same zero control.
    intro A z
    change sphereDeRhamVector r s (A • z) = 0 ↔ sphereDeRhamVector r s z = 0
    rw [(sphereDeRhamVector_properties r).2.2]
    have hi : Function.Injective (sphereComplexifiedTangentAction r A z.proj) :=
      ((sphereComplexifiedTangentEquivariantStructure r).linearMap_bijective A z.proj).1
    constructor
    · intro hz
      exact hi (hz.trans (map_zero _).symm)
    · intro hz
      simp only [hz, map_zero]
      rfl
  · -- Both original pullback actions reduce to the same exterior derivative maps.
    intro A z a
    apply Subtype.ext
    change (sphereDeRhamSymbol r s (A • z.val)
      ((sphereExteriorParityEquivariantStructure r 0).linearMap A z.val.proj a)).val =
        ((sphereExteriorParityEquivariantStructure r 1).linearMap A z.val.proj
          (sphereDeRhamSymbol r s z.val a)).val
    have hformula (y : TangentBundle (𝓡 r) (OrthogonalSphere r))
        (b : CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ (SphereComplexifiedTangent r y.proj)) 0) :
        (sphereDeRhamSymbol r s y b).val =
          ExteriorAlgebra.ι ℂ (sphereDeRhamVector r s y) * b.val +
            CliffordAlgebra.contractLeft (ell y.proj (sphereDeRhamVector r s y)) b.val := by
      let core := (sphereComplexifiedRoundMetric r).toCore y.proj
      let : NormedAddCommGroup (SphereComplexifiedTangent r y.proj) :=
        core.toNormedAddCommGroup
      let : InnerProductSpace ℂ (SphereComplexifiedTangent r y.proj) :=
        InnerProductSpace.ofCore core.toCore
      exact (koszulSymbolParity_formula (V := SphereComplexifiedTangent r y.proj)).1
        (sphereDeRhamVector r s y) 0 b
    apply Eq.trans (hformula (A • z.val)
      ((sphereExteriorParityEquivariantStructure r 0).linearMap A z.val.proj a))
    apply Eq.trans _ (sphereExteriorParityEquivariantStructure_apply r 1 A z.val.proj
      (sphereDeRhamSymbol r s z.val a)).symm
    let L := sphereComplexifiedTangentAction r A z.val.proj
    let F := ExteriorAlgebra.map L
    let av : ExteriorAlgebra ℂ (SphereComplexifiedTangent r z.val.proj) := a.val
    have hleft := congrArg₂
      (fun (v : SphereComplexifiedTangent r (A • z.val.proj))
          (b : ExteriorAlgebra ℂ (SphereComplexifiedTangent r (A • z.val.proj))) ↦
        ExteriorAlgebra.ι ℂ v * b + CliffordAlgebra.contractLeft (ell (A • z.val.proj) v) b)
      ((sphereDeRhamVector_properties r).2.2 s A z.val)
      (sphereExteriorParityEquivariantStructure_apply r 0 A z.val.proj a)
    apply Eq.trans hleft
    -- Contraction is natural for maps preserving the specified metric coefficients.
    have hnatural {V W : Type} [AddCommGroup V] [Module ℂ V]
        [AddCommGroup W] [Module ℂ W] (L : V →ₗ[ℂ] W)
        (f : V →ₗ[ℂ] ℂ) (g : W →ₗ[ℂ] ℂ) (hg : ∀ v, g (L v) = f v)
        (b : ExteriorAlgebra ℂ V) :
        CliffordAlgebra.contractLeft g (ExteriorAlgebra.map L b) =
          ExteriorAlgebra.map L (CliffordAlgebra.contractLeft f b) := by
      induction b using CliffordAlgebra.left_induction with
      | algebraMap c => simp
      | add b c hb hc => simp only [map_add, hb, hc]
      | ι_mul b v hb =>
        simp only [map_mul, ExteriorAlgebra.map_apply_ι,
          CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, hg, hb]
    have hcontract (b : ExteriorAlgebra ℂ (SphereComplexifiedTangent r z.val.proj)) :
        CliffordAlgebra.contractLeft (ell (A • z.val.proj) (L (sphereDeRhamVector r s z.val)))
          (F b) = F (CliffordAlgebra.contractLeft
            (ell z.val.proj (sphereDeRhamVector r s z.val)) b) :=
      hnatural L _ _ (fun v ↦ sphereComplexifiedRoundMetric_invariant r A z.val.proj _ v) b
    -- Combine wedge and contraction naturality without choosing replacement maps.
    change ExteriorAlgebra.ι ℂ (L (sphereDeRhamVector r s z.val)) * F av +
      CliffordAlgebra.contractLeft (ell (A • z.val.proj)
        (L (sphereDeRhamVector r s z.val))) (F av) =
          F (sphereDeRhamSymbol r s z.val a).val
    apply Eq.trans (congrArg (fun b ↦
      ExteriorAlgebra.ι ℂ (L (sphereDeRhamVector r s z.val)) * F av + b) (hcontract av))
    apply Eq.trans _ (congrArg F (hformula z.val a)).symm
    have hw : F (ExteriorAlgebra.ι ℂ (sphereDeRhamVector r s z.val) * av) =
        ExteriorAlgebra.ι ℂ (L (sphereDeRhamVector r s z.val)) * F av :=
      (map_mul F _ _).trans (congrArg (fun b ↦ b * F av)
        (ExteriorAlgebra.map_apply_ι L (sphereDeRhamVector r s z.val)))
    exact (congrArg (fun b ↦ b + F (CliffordAlgebra.contractLeft
      (ell z.val.proj (sphereDeRhamVector r s z.val)) av)) hw.symm).trans
        (map_add F _ _).symm

/-- The original supported exterior complex with its precise derivative actions. -/
def equivariantSphereDeRhamTriple (r : ℕ) (s : ℝ) :
    EquivariantSupportBundleTriple (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  EquivariantSupportBundleTriple.ofBoundary
    (sphereDeRhamParityBundle r 0) (sphereDeRhamParityBundle r 1)
    (sphereDeRhamTriple r s) (sphereDeRhamParityAction r 0) (sphereDeRhamParityAction r 1)
    (sphereDeRhamTriple_isEquivariant r s)

/-- The source de Rham symbol class on the original native sphere tangent bundle. -/
def orthogonalSphereDeRhamClass (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  (equivariantSphereDeRhamTriple r 0).kZeroClass

set_option maxHeartbeats 1000000 in
-- Normalize the joint deformation cylinder and its exact original endpoints.
/-- The actual deformation gives one equivariant boundary cylinder with exact endpoints. -/
theorem exists_sphereDeRhamHomotopy (r : ℕ) :
    ∃ H : CompactSupportTriple.EquivariantHomotopy
        (sphereDeRhamParityAction r 0) (sphereDeRhamParityAction r 1)
        (sphereDeRhamTriple r 0) (sphereDeRhamTriple r 1),
      H.control = {z : TangentBundle (𝓡 r) (OrthogonalSphere r) | z.snd = 0} ∧
        ∀ (t : unitInterval)
          (x : (H.controlᶜ : Set (TangentBundle (𝓡 r) (OrthogonalSphere r))))
          (a : (sphereDeRhamParityBundle r 0).Fiber x.val),
          H.homotopy.iso.linearEquiv (t, x) a = sphereDeRhamSymbol r t x.val a := by
  let C := SphereComplexifiedTangent r
  -- The original real and imaginary coordinates give joint continuity in time and base.
  have hvector :
      Continuous (fun z : ℝ × TangentBundle (𝓡 r) (OrthogonalSphere r) ↦
        (⟨z.2.proj, sphereDeRhamVector r z.1 z.2⟩ :
          TotalSpace Unit (SphereComplexifiedTangent r))) := by
    let V := EuclideanSpace ℝ (Fin r)
    let E := fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x
    let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
    let hp : C(T, OrthogonalSphere r) := orthogonalSphereTangentProjection r
    have hscale : Continuous (fun z : ℝ × T ↦ (⟨z.2.proj, z.1 • z.2.snd⟩ : T)) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      apply (FiberBundle.continuousAt_totalSpace V _).mpr
      refine ⟨hp.continuous.continuousAt.comp continuousAt_snd, ?_⟩
      let e := trivializationAt V E z.2.proj
      have hc : ContinuousAt (fun w : ℝ × T ↦ (e w.2).2) z :=
        (e.continuousAt (FiberBundle.mem_trivializationAt_proj_source)).snd.comp
          continuousAt_snd
      apply (continuousAt_fst.smul hc).congr_of_eventuallyEq
      have hb : ∀ᶠ w : ℝ × T in nhds z, w.2.proj ∈ e.baseSet :=
        (hp.continuous.comp continuous_snd).continuousAt.eventually
          (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt V E z.2.proj))
      filter_upwards [hb] with w hw
      exact (e.linear ℝ hw).2 w.1 w.2.snd
    let ce := complexificationDoubleTotalHomeomorph V E
    apply ce.isInducing.continuous_iff.mpr
    apply (FiberBundle.Prod.isInducing_diag V E V E).continuous_iff.mpr
    have hgrad : Continuous (fun z : ℝ × T ↦
        (⟨z.2.proj, orthogonalSphereHeightGradient r z.2.proj⟩ : T)) :=
      (continuous_orthogonalSphereHeightGradient r).comp
        (hp.continuous.comp continuous_snd)
    have him : Continuous (fun z : ℝ × T ↦
        (⟨z.2.proj, -(z.1 • orthogonalSphereHeightGradient r z.2.proj)⟩ : T)) := by
      apply (hscale.comp (continuous_fst.neg.prodMk hgrad)).congr
      intro z
      change (⟨z.2.proj, (-z.1) • orthogonalSphereHeightGradient r z.2.proj⟩ : T) = _
      rw [neg_smul]
    apply (continuous_snd.prodMk him).congr
    intro z
    dsimp only [Function.comp_apply]
    change _ = ((⟨z.2.proj,
      (complexificationReIm (E z.2.proj) (sphereDeRhamVector r z.1 z.2)).1⟩ : T),
      (⟨z.2.proj,
      (complexificationReIm (E z.2.proj) (sphereDeRhamVector r z.1 z.2)).2⟩ : T))
    simp only [sphereDeRhamVector, map_sub, (complexificationReIm_properties _).1]
    simp
    rfl
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  -- The entire native zero section is one compact invariant control for every time.
  let K : Set T := {z | z.snd = 0}
  have hK : IsCompact K := by
    have hset : K = Set.range (zeroSection (EuclideanSpace ℝ (Fin r))
        (fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x)) := by
      ext z
      constructor
      · intro hz
        exact ⟨z.proj, congrArg (TotalSpace.mk z.proj) hz.symm⟩
      · rintro ⟨x, rfl⟩
        rfl
    rw [hset]
    exact isCompact_range (Bundle.Trivialization.continuous_zeroSection ℝ)
  have hzero (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : T)
      (hz : z.snd = 0) : (A • z).snd = 0 := by
    change (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) z.proj) z.snd = 0
    rw [hz, map_zero]
  have hInv (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : T) :
      A • z ∈ K ↔ z ∈ K := by
    constructor
    · intro hz
      change z.snd = 0
      exact Eq.mp (congrArg (fun u : T ↦ u.snd = 0) (inv_smul_smul A z))
        (hzero A⁻¹ (A • z) hz)
    · exact hzero A z
  have hleft : (sphereDeRhamTriple r 0).control ⊆ K := by
    intro z hz
    exact ((sphereDeRhamVector_properties r).1 0 z).mp hz |>.1
  have hright : (sphereDeRhamTriple r 1).control ⊆ K := by
    intro z hz
    exact ((sphereDeRhamVector_properties r).1 1 z).mp hz |>.1
  have hnz (t : ℝ) (x : (Kᶜ : Set T)) : sphereDeRhamVector r t x.val ≠ 0 := by
    intro hz
    exact x.property (((sphereDeRhamVector_properties r).1 t x.val).mp hz).1
  -- Form the original restricted exterior bundles and their cylinder pullbacks.
  let P₀ (x : OrthogonalSphere r) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C x)) 0
  let P₁ (x : OrthogonalSphere r) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C x)) 1
  let E₀ := Restrict (sphereDeRhamParityBundle r 0).Fiber Kᶜ
  let E₁ := Restrict (sphereDeRhamParityBundle r 1).Fiber Kᶜ
  let F₀ := (Prod.snd : I × (Kᶜ : Set T) → (Kᶜ : Set T)) *ᵖ E₀
  let F₁ := (Prod.snd : I × (Kᶜ : Set T) → (Kᶜ : Set T)) *ᵖ E₁
  let : IsFiniteRank E₀ := isFiniteRank_restrict Kᶜ
  let : IsFiniteRank E₁ := isFiniteRank_restrict Kᶜ
  let : IsFiniteRank F₀ := isFiniteRank_pullback (E := E₀)
    (⟨Prod.snd, continuous_snd⟩ : C(I × (Kᶜ : Set T), (Kᶜ : Set T)))
  let : IsFiniteRank F₁ := isFiniteRank_pullback (E := E₁)
    (⟨Prod.snd, continuous_snd⟩ : C(I × (Kᶜ : Set T), (Kᶜ : Set T)))
  let D₀ := TotalSpace Unit F₀
  have hbase : Continuous (fun z : D₀ ↦ z.proj) := continuous_proj (E := F₀)
  have hrestrict : Continuous (fun z : D₀ ↦
      (⟨z.proj.2, z.snd⟩ : TotalSpace Unit E₀)) :=
    Pullback.continuous_lift Unit E₀ Prod.snd
  have htan : Continuous (fun z : D₀ ↦ z.proj.2.val) :=
    continuous_subtype_val.comp hbase.snd
  have htime : Continuous (fun z : D₀ ↦ (z.proj.1 : ℝ)) :=
    continuous_subtype_val.comp hbase.fst
  have hpull : Continuous (fun z : D₀ ↦
      (⟨z.proj.2.val, z.snd⟩ : TotalSpace Unit (sphereDeRhamParityBundle r 0).Fiber)) :=
    (Pullback.continuous_lift Unit (sphereDeRhamParityBundle r 0).Fiber
      (Subtype.val : (Kᶜ : Set T) → T)).comp hrestrict
  have hprojection : Continuous (fun z : TotalSpace Unit (sphereDeRhamParityBundle r 0).Fiber ↦
      (⟨z.proj.proj, z.snd⟩ : TotalSpace Unit P₀)) :=
    Pullback.continuous_lift Unit P₀ (orthogonalSphereTangentProjection r)
  have hparity := hprojection.comp hpull
  have hambient : Continuous (fun z : D₀ ↦
      (⟨z.proj.2.val.proj, z.snd.val⟩ : TotalSpace Unit
        (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x)))) :=
    continuous_induced_dom.comp hparity
  let := sumTopology (E := C) (F := fun x ↦ ExteriorAlgebra ℂ (C x))
  have hpair : Continuous (fun z : D₀ ↦
      (⟨z.proj.2.val.proj,
        (sphereDeRhamVector r z.proj.1 z.proj.2.val, z.snd.val)⟩ :
        TotalSpace Unit (C ×ᵇ (fun x ↦ ExteriorAlgebra ℂ (C x))))) := by
    apply continuous_induced_rng.mpr
    exact (hvector.comp (htime.prodMk htan)).prodMk hambient
  -- Normalize the algebraic adapter before substituting the native sphere fibers.
  let ell (x : OrthogonalSphere r) (v : C x) : C x →ₗ[ℂ] ℂ :=
    let core := (sphereComplexifiedRoundMetric r).toCore x
    letI : NormedAddCommGroup (C x) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (C x) := InnerProductSpace.ofCore core.toCore
    innerₛₗ ℂ v
  have hnormalized {X : Type} [TopologicalSpace X]
      (E : X → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      (h : ContinuousHermitianMetric E) :
      let _ := sumTopology (E := E) (F := fun x ↦ ExteriorAlgebra ℂ (E x))
      Continuous (fun z : TotalSpace Unit (E ×ᵇ (fun x ↦ ExteriorAlgebra ℂ (E x))) ↦
        (⟨z.proj, ExteriorAlgebra.ι ℂ z.snd.1 * z.snd.2 +
          CliffordAlgebra.contractLeft
            (let core := h.toCore z.proj
             letI : NormedAddCommGroup (E z.proj) := core.toNormedAddCommGroup
             letI : InnerProductSpace ℂ (E z.proj) := InnerProductSpace.ofCore core.toCore
             innerₛₗ ℂ z.snd.1) z.snd.2⟩ :
              TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
    exact continuous_exteriorMultiplication_add_contraction E h
  have hpositive : Continuous (fun z : D₀ ↦
      (⟨z.proj.2.val.proj,
        @Add.add (ExteriorAlgebra ℂ (C z.proj.2.val.proj)) inferInstance
          (@Mul.mul (ExteriorAlgebra ℂ (C z.proj.2.val.proj)) inferInstance
            (ExteriorAlgebra.ι ℂ (sphereDeRhamVector r z.proj.1 z.proj.2.val)) z.snd.val)
          (CliffordAlgebra.contractLeft
            (ell z.proj.2.val.proj (sphereDeRhamVector r z.proj.1 z.proj.2.val)) z.snd.val)⟩ :
              TotalSpace Unit (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x)))) :=
    (hnormalized C (sphereComplexifiedRoundMetric r)).comp hpair
  have hformula (t : ℝ) (y : T) (b : P₀ y.proj) :
      (sphereDeRhamSymbol r t y b).val =
        ExteriorAlgebra.ι ℂ (sphereDeRhamVector r t y) * b.val +
          CliffordAlgebra.contractLeft (ell y.proj (sphereDeRhamVector r t y)) b.val := by
    let core := (sphereComplexifiedRoundMetric r).toCore y.proj
    let : NormedAddCommGroup (C y.proj) := core.toNormedAddCommGroup
    let : InnerProductSpace ℂ (C y.proj) := InnerProductSpace.ofCore core.toCore
    exact (koszulSymbolParity_formula (V := C y.proj)).1
      (sphereDeRhamVector r t y) 0 b
  -- Lift the continuous ambient operator through the original induced topologies.
  have hsymbol : Continuous (fun z : D₀ ↦
      (⟨z.proj.2.val.proj, (sphereDeRhamSymbol r z.proj.1 z.proj.2.val z.snd).val⟩ :
        TotalSpace Unit (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x)))) := by
    apply hpositive.congr
    intro z
    exact congrArg
      (fun b : ExteriorAlgebra ℂ (C z.proj.2.val.proj) ↦
        (⟨z.proj.2.val.proj, b⟩ : TotalSpace Unit
          (fun x : OrthogonalSphere r ↦ ExteriorAlgebra ℂ (C x))))
      (hformula z.proj.1 z.proj.2.val z.snd).symm
  have hsymbolParity : Continuous (fun z : D₀ ↦
      (⟨z.proj.2.val.proj, sphereDeRhamSymbol r z.proj.1 z.proj.2.val z.snd⟩ :
        TotalSpace Unit P₁)) := continuous_induced_rng.mpr hsymbol
  have hsymbolPullback : Continuous (fun z : D₀ ↦
      (⟨z.proj.2.val, sphereDeRhamSymbol r z.proj.1 z.proj.2.val z.snd⟩ :
        TotalSpace Unit (sphereDeRhamParityBundle r 1).Fiber)) :=
    (inducing_pullbackTotalSpaceEmbedding Unit P₁
      (orthogonalSphereTangentProjection r)).continuous_iff.mpr (htan.prodMk hsymbolParity)
  have hsymbolRestricted : Continuous (fun z : D₀ ↦
      (⟨z.proj.2, sphereDeRhamSymbol r z.proj.1 z.proj.2.val z.snd⟩ :
        TotalSpace Unit E₁)) :=
    (inducing_pullbackTotalSpaceEmbedding Unit (sphereDeRhamParityBundle r 1).Fiber
      (Subtype.val : (Kᶜ : Set T) → T)).continuous_iff.mpr
        (hbase.snd.prodMk hsymbolPullback)
  have hforward : Continuous (fun z : D₀ ↦
      (⟨z.proj, sphereDeRhamSymbolEquiv r z.proj.1 z.proj.2.val
        (hnz z.proj.1 z.proj.2) z.snd⟩ : TotalSpace Unit F₁)) :=
    (inducing_pullbackTotalSpaceEmbedding Unit E₁
      (Prod.snd : I × (Kᶜ : Set T) → (Kᶜ : Set T))).continuous_iff.mpr
        (hbase.prodMk hsymbolRestricted)
  -- Finite rank supplies joint inverse continuity for this exact forward map.
  let f : Hom F₀ F₁ :=
    { linearMap := fun z ↦ (sphereDeRhamSymbolEquiv r z.1 z.2.val (hnz z.1 z.2)).toLinearMap
      continuous_total := hforward }
  let j := f.toIso (fun z ↦ (sphereDeRhamSymbolEquiv r z.1 z.2.val (hnz z.1 z.2)).bijective)
  -- Preserve the exact endpoints and reuse the equivariance of each actual time slice.
  let H : CompactSupportTriple.EquivariantHomotopy
      (sphereDeRhamParityAction r 0) (sphereDeRhamParityAction r 1)
      (sphereDeRhamTriple r 0) (sphereDeRhamTriple r 1) :=
    { control := K
      isCompact_control := hK
      invariant_control := hInv
      left_control := hleft
      right_control := hright
      homotopy := {
        iso := j
        map_zero := by
          intro x a
          have he := (sphereDeRhamTriple r 0).enlarge_apply K hK hleft x a
          refine Eq.trans ?_ he.symm
          dsimp only [sphereDeRhamTriple]
          change sphereDeRhamSymbolEquiv r ((0 : I) : ℝ) x.val (hnz _ x) a =
            sphereDeRhamSymbolEquiv r 0 x.val (hnz 0 x) a
          rw [Set.Icc.coe_zero]
        map_one := by
          intro x a
          have he := (sphereDeRhamTriple r 1).enlarge_apply K hK hright x a
          refine Eq.trans ?_ he.symm
          dsimp only [sphereDeRhamTriple]
          change sphereDeRhamSymbolEquiv r ((1 : I) : ℝ) x.val (hnz _ x) a =
            sphereDeRhamSymbolEquiv r 1 x.val (hnz 1 x) a
          rw [Set.Icc.coe_one] }
      intertwines := by
        intro t A x a
        let y : (Kᶜ : Set T) :=
          ⟨A • x.val, fun hx ↦ x.property ((hInv A x.val).mp hx)⟩
        change sphereDeRhamSymbolEquiv r (t : ℝ) y.val (hnz t y)
            ((sphereDeRhamParityAction r 0).linearMap A x.val a) =
          (sphereDeRhamParityAction r 1).linearMap A x.val
            (sphereDeRhamSymbolEquiv r (t : ℝ) x.val (hnz t x) a)
        have he := (sphereDeRhamTriple_isEquivariant r (t : ℝ)).boundary_intertwines A
          ⟨x.val, hnz t x⟩ a
        dsimp only [sphereDeRhamTriple] at he
        exact he }
  exact ⟨H, rfl, fun _ _ _ ↦ rfl⟩

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalKernelRealization

/-!
# The coefficient kernel in the associated graded square

A supplied equivariant representation of the sphere kernel yields the full
vertical-kernel equivalences through its evaluation map. Horizontal
intertwining then gives a linear equivalence from the coefficient PDO kernel
to the simultaneous smooth horizontal and vertical kernel.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w w' u' v'

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere
  lieGroup_orthogonalGroup

variable {n r a a' : ℕ} {P : Type u} {B : Type v}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type w) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type w') [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {F : OrthogonalSphere r → Type u'} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type v'} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  {μ : MeasureTheory.Measure B} [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z

set_option maxSynthPendingDepth 30 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The coefficient PDO kernel is linearly equivalent to the simultaneous smooth kernel. -/
theorem PrincipalPseudodifferentialLocalization.exists_coefficient_jointSmoothKernelEquiv
    {m d : ℝ} (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (Q : AtlasPseudodifferentialOperator A A' d)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI : TopologicalSpace (TotalSpace Unit U) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI : TopologicalSpace (TotalSpace Unit U') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let H := C₀.horizontalLift S E A σ E' hσ
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    let Pc := C₀.coefficientOperator S E E' ρ
    ∃ ev : Hom ((πS : Z → B) *ᵖ K) D,
      (∀ (p : P) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
        ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
      ∃ Φ : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
          (associatedOrthogonalRepresentationAtlas S ρ)).smoothSections ≃ₗ[ℂ]
          (associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ).ker,
        ∃ Ψ : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
            (associatedOrthogonalRepresentationAtlas S ρ)).smoothSections ≃ₗ[ℂ]
            (associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ).ker,
          (∀ u z, (Φ u).val.val z =
            TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
          (∀ u z, (Ψ u).val.val z =
            TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
          (∀ u, H (Φ u).val = (Ψ (Pc.toLinearMap u)).val) ∧
          ∃ κ : Pc.toLinearMap.ker ≃ₗ[ℂ] ↥(H.ker ⊓ V.ker),
            ∀ u, (κ u).val = (Φ u.val).val := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let H := C₀.horizontalLift S E A σ E' hσ
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
  let Pc := C₀.coefficientOperator S E E' ρ
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hactual := C₀.exists_horizontalLift_coefficientKernelRealization
    S E E' A σ hσ A' σ' hσ' ρ Q hQ e he
  obtain ⟨ev, hev, Φ, Ψ, hΦ, hΨ, hH⟩ := hactual
  -- Restrict the horizontal intertwining to the simultaneous kernel.
  have hkernel {C₀ : Type (max v u w)} {C₁ : Type (max v u w')}
      {X₀ : Type (max u w u')} {X₁ : Type (max u w' u')}
      {Y₀ : Type (max u w v')} {Y₁ : Type (max u w' v')}
      [AddCommGroup C₀] [Module ℂ C₀] [AddCommGroup C₁] [Module ℂ C₁]
      [AddCommGroup X₀] [Module ℂ X₀] [AddCommGroup X₁] [Module ℂ X₁]
      [AddCommGroup Y₀] [Module ℂ Y₀] [AddCommGroup Y₁] [Module ℂ Y₁]
      (P₀ : C₀ →ₗ[ℂ] C₁) (H : X₀ →ₗ[ℂ] X₁)
      (V : X₀ →ₗ[ℂ] Y₀) (W : X₁ →ₗ[ℂ] Y₁)
      (Φ : C₀ ≃ₗ[ℂ] V.ker) (Ψ : C₁ ≃ₗ[ℂ] W.ker)
      (hcompat : ∀ u, H (Φ u).val = (Ψ (P₀ u)).val) :
      ∃ κ : P₀.ker ≃ₗ[ℂ] ↥(H.ker ⊓ V.ker), ∀ u, (κ u).val = (Φ u.val).val := by
    let f : P₀.ker →ₗ[ℂ] ↥(H.ker ⊓ V.ker) := {
      toFun u := ⟨(Φ u.val).val, by
        refine ⟨?_, (Φ u.val).property⟩
        change H (Φ u.val).val = 0
        rw [hcompat, u.property, Ψ.map_zero]
        rfl⟩
      map_add' u v := by
        apply Subtype.ext
        change (Φ (u.val + v.val)).val = (Φ u.val).val + (Φ v.val).val
        rw [Φ.map_add]
        rfl
      map_smul' c u := by
        apply Subtype.ext
        change (Φ (c • u.val)).val = c • (Φ u.val).val
        rw [Φ.map_smul]
        rfl }
    have hf : Function.Bijective f := by
      constructor
      · intro u v huv
        have hval := congrArg (fun w : ↥(H.ker ⊓ V.ker) ↦ w.val) huv
        apply Subtype.ext
        apply Φ.injective
        exact Subtype.ext hval
      · intro w
        let wV : V.ker := ⟨w.val, w.property.2⟩
        let u := Φ.symm wV
        have hu : P₀ u = 0 := by
          apply Ψ.injective
          apply Subtype.ext
          change (Ψ (P₀ u)).val = (Ψ 0).val
          rw [← hcompat, Ψ.map_zero]
          have hΦu : (Φ u).val = w.val := congrArg Subtype.val (Φ.apply_symm_apply wV)
          rw [hΦu]
          exact w.property.1
        refine ⟨⟨u, hu⟩, ?_⟩
        apply Subtype.ext
        have hval := congrArg (fun v : V.ker ↦ v.val) (Φ.apply_symm_apply wV)
        exact hval
    exact ⟨LinearEquiv.ofBijective f hf, fun _ ↦ rfl⟩
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hκ := hkernel Pc.toLinearMap H V
    (associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' Q hQ)
    Φ Ψ hH
  obtain ⟨κ, hκ⟩ := hκ
  refine ⟨ev, hev, Φ, Ψ, hΦ, hΨ, hH, κ, ?_⟩
  exact hκ

end AtiyahSinger

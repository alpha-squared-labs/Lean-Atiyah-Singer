/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalOperator
public import AtiyahSinger.Analysis.TensorSectionFormalAdjoint

/-!
# Fiberwise adjunction for the associated vertical operators

Public module ID: M0194.

The supplied equivariant sphere operators and their integral adjunction give
the same adjunction along every whole associated sphere fiber, for the
prescribed tensor-product pairings. The proof pulls back these forms along
the quotient tensor identifications, restricts the upstairs sections, and
applies finite tensor adjunction to the complete operator actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z


local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (q z) ⊗[ℂ] D' z

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original adjunction holds on each complete associated sphere fiber. -/
theorem associatedSphereTensorVerticalOperator_integral_fiber_adjoint {m : ℝ}
    (Q : AtlasPseudodifferentialOperator A A' m)
    (J : AtlasPseudodifferentialOperator A' A m)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (hJ : J.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ' σ hσ' hσ)
    (μ : Measure (OrthogonalSphere r))
    (hE : ∀ x, InnerProductSpace.Core ℂ (E x))
    (hF : ∀ y, InnerProductSpace.Core ℂ (F y))
    (hF' : ∀ y, InnerProductSpace.Core ℂ (F' y))
    (l : ∀ z, InnerProductSpace.Core ℂ (T z))
    (l' : ∀ z, InnerProductSpace.Core ℂ (T' z))
    (hpair : ∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F y),
      (l (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
          (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
          (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
        (hE (projection p)).inner u v * (hF y).inner s t)
    (hpair' : ∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F' y),
      (l' (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
          (associatedSphereTensorFiberEquiv S E σ' p y (u ⊗ₜ[ℂ] s))
          (associatedSphereTensorFiberEquiv S E σ' p y (v ⊗ₜ[ℂ] t)) =
        (hE (projection p)).inner u v * (hF' y).inner s t)
    (hInt : ∀ s t : A.smoothSections,
      Integrable (fun y ↦ (hF y).inner (s.val y) (t.val y)) μ)
    (hInt' : ∀ s t : A'.smoothSections,
      Integrable (fun y ↦ (hF' y).inner (s.val y) (t.val y)) μ)
    (hAdj : ∀ (s : A.smoothSections) (t : A'.smoothSections),
      (∫ y, (hF' y).inner ((Q.toLinearMap s).val y) (t.val y) ∂μ) =
        ∫ y, (hF y).inner (s.val y) ((J.toLinearMap t).val y) ∂μ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (s : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
      (t : (associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ').smoothSections)
      (p : P),
      (∫ y, (l' (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
          ((associatedSphereTensorVerticalOperator (a := a)
            S E A σ hσ A' σ' hσ' Q hQ s).val
              (associatedBundleMk G P (OrthogonalSphere r) p y))
          (t.val (associatedBundleMk G P (OrthogonalSphere r) p y)) ∂μ) =
        ∫ y, (l (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
          (s.val (associatedBundleMk G P (OrthogonalSphere r) p y))
          ((associatedSphereTensorVerticalOperator (a := a)
            S E A' σ' hσ' A σ hσ J hJ t).val
              (associatedBundleMk G P (OrthogonalSphere r) p y)) ∂μ := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro s t p
  let : FiniteDimensional ℂ (E (projection p)) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E (projection p)
  let e (y : OrthogonalSphere r) := associatedSphereTensorFiberEquiv S E σ p y
  let e' (y : OrthogonalSphere r) := associatedSphereTensorFiberEquiv S E σ' p y
  -- Pull back the given forms along the exact original tensor identifications.
  let c (y : OrthogonalSphere r) : InnerProductSpace.Core ℂ (E (projection p) ⊗[ℂ] F y) :=
    { inner := fun u v ↦ (l (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
        (e y u) (e y v)
      conj_inner_symm u v := (l _).conj_inner_symm _ _
      re_inner_nonneg u := (l _).re_inner_nonneg _
      add_left u v w := by rw [map_add, (l _).add_left]
      smul_left u v z := by rw [map_smul, (l _).smul_left]
      definite u hu := (e y).injective ((l _).definite _ hu |>.trans (map_zero _).symm) }
  let c' (y : OrthogonalSphere r) : InnerProductSpace.Core ℂ (E (projection p) ⊗[ℂ] F' y) :=
    { inner := fun u v ↦ (l' (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
        (e' y u) (e' y v)
      conj_inner_symm u v := (l' _).conj_inner_symm _ _
      re_inner_nonneg u := (l' _).re_inner_nonneg _
      add_left u v w := by rw [map_add, (l' _).add_left]
      smul_left u v z := by rw [map_smul, (l' _).smul_left]
      definite u hu := (e' y).injective ((l' _).definite _ hu |>.trans (map_zero _).symm) }
  let R := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p s
  let R' := associatedSphereTensorFiberRestriction (a := a) S E A' σ' hσ' p t
  have hadj := tensorSectionOperator_integral_adjoint (E (projection p))
    A.smoothSections A'.smoothSections Q.toLinearMap J.toLinearMap μ
    (hE (projection p)) hF hF' c c'
    (hpair p) (hpair' p) hInt hInt' hAdj R R'
  -- Whole-fiber restriction recovers these same upstairs section values and vertical outputs.
  have hleft (y : OrthogonalSphere r) :
      (c' y).inner ((tensorSectionOperator (E (projection p)) A.smoothSections
        A'.smoothSections Q.toLinearMap R).val y) (R'.val y) =
      (l' (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
        ((associatedSphereTensorVerticalOperator (a := a)
          S E A σ hσ A' σ' hσ' Q hQ s).val
            (associatedBundleMk G P (OrthogonalSphere r) p y))
        (t.val (associatedBundleMk G P (OrthogonalSphere r) p y)) := by
    rw [associatedSphereTensorVerticalOperator_apply]
    change (l' _).inner _ (e' y (R'.val y)) = _
    rw [associatedSphereTensorFiberRestriction_apply]
    rfl
  have hright (y : OrthogonalSphere r) :
      (c y).inner (R.val y) ((tensorSectionOperator (E (projection p)) A'.smoothSections
        A.smoothSections J.toLinearMap R').val y) =
      (l (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
        (s.val (associatedBundleMk G P (OrthogonalSphere r) p y))
        ((associatedSphereTensorVerticalOperator (a := a)
          S E A' σ' hσ' A σ hσ J hJ t).val
            (associatedBundleMk G P (OrthogonalSphere r) p y)) := by
    rw [associatedSphereTensorVerticalOperator_apply]
    change (l _).inner (e y (R.val y)) _ = _
    rw [associatedSphereTensorFiberRestriction_apply]
    rfl
  simpa only [hleft, hright] using hadj

end AtiyahSinger

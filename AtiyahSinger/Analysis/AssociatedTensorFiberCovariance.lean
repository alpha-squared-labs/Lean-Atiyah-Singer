/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorFiberRestriction

/-!
# Covariance of whole associated tensor fiber restrictions

Public module ID: M0141.

Changing a principal representative transports the base coefficient along
its projection equality and acts on the sphere factor by the supplied
equivariant structure. The quotient tensor value is unchanged. This gives
the descent identity for the whole-fiber restriction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

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

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

omit [IsManifold (𝓡 n) ∞ B] in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual quotient tensor identification has the original principal covariance. -/
theorem associatedSphereTensorFiberEquiv_smul (p : P) (g : G) (y : OrthogonalSphere r)
    (v : E (projection (MulOpposite.op g • p)) ⊗[ℂ] F y) :
    (LinearEquiv.cast (R := ℂ) (M := T) (associatedBundleMk_smul p g y))
        (associatedSphereTensorFiberEquiv S E σ (MulOpposite.op g • p) y v) =
      associatedSphereTensorFiberEquiv S E σ p (g • y)
        (TensorProduct.map
          (LinearEquiv.cast (R := ℂ) (M := E) (S.projection_smul g p)).toLinearMap
          (σ.linearMap g y) v) := by
  let := σ.toMulAction
  -- Equality transport respects both tensor factors.
  have hcast {z z' : Z} (h : z = z') (v : E (q z)) (w : D z) :
      (LinearEquiv.cast (R := ℂ) (M := T) h) (v ⊗ₜ[ℂ] w) =
        (LinearEquiv.cast (R := ℂ) (M := E) (congrArg q h)) v ⊗ₜ[ℂ]
          (LinearEquiv.cast (R := ℂ) (M := D) h) w := by
    subst z'
    rfl
  have hmk {z z' : Z} (h : z = z') (p' : P) (y' : OrthogonalSphere r)
      (hz : associatedBundleMk G P (OrthogonalSphere r) p' y' = z) (w : F y') :
      (LinearEquiv.cast (R := ℂ) (M := D) h)
          (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p' y' hz w) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p' y' (hz.trans h) w := by
    subst z'
    rfl
  induction v using TensorProduct.inductionOn with
  | tmul v w =>
    simp only [associatedSphereTensorFiberEquiv_tmul, hcast, hmk,
      TensorProduct.map_tmul, LinearEquiv.coe_coe]
    congr 1
    apply Subtype.ext
    exact associatedBundleMk_smul p g (⟨y, w⟩ : TotalSpace Unit F)
  | add v w hv hw =>
    simpa only [map_add] using congrArg₂ (· + ·) hv hw

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full sphere restriction transforms by the specified action and base transport. -/
theorem associatedSphereTensorFiberRestriction_smul
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (p : P) (g : G) (y : OrthogonalSphere r) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      TensorProduct.map
          (LinearEquiv.cast (R := ℂ) (M := E) (S.projection_smul g p)).toLinearMap
          (σ.linearMap g y)
          ((associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
            (MulOpposite.op g • p) w).val y) =
        (associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w).val (g • y) := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro w
  apply (associatedSphereTensorFiberEquiv S E σ p (g • y)).injective
  rw [← associatedSphereTensorFiberEquiv_smul,
    associatedSphereTensorFiberRestriction_apply, associatedSphereTensorFiberRestriction_apply]
  -- Both representatives name precisely the same point of the original quotient.
  have hvalue {z z' : Z} (h : z = z') :
      (LinearEquiv.cast (R := ℂ) (M := T) h) (w.val z) = w.val z' := by
    subst z'
    rfl
  exact hvalue (associatedBundleMk_smul p g y)

end AtiyahSinger

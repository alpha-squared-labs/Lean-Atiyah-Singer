/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseExtension

/-!
# The value of a principal-chart return at a normalized representative

Public module ID: M0135.

At a normalized principal representative, the return is the tensor fiber
equivalence applied to the whole-family value, with the base factor first.
This formula compares the horizontal and vertical operators at a common
principal representative.
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
/-- At a normalized principal representative, the actual return has the original whole value. -/
theorem associatedSphereTensorBaseExtension_apply_mk
    (b : B) (p : P) (y : OrthogonalSphere r)
    (hp : projection p ∈ (S.trivialization b).baseSet)
    (hg : (S.trivialization b p).2 = 1)
    (u : ∀ y : OrthogonalSphere r, ∀ x : B, F y ⊗[ℂ] E x) :
    associatedSphereTensorBaseExtension S E σ b u
        (associatedBundleMk G P (OrthogonalSphere r) p y) =
      associatedSphereTensorFiberEquiv S E σ p y
        (TensorProduct.comm ℂ (F y) (E (projection p)) (u y (projection p))) := by
  classical
  let t := associatedSphereTrivialization S b
  let z := associatedBundleMk G P (OrthogonalSphere r) p y
  have hbase : t.baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hz : z ∈ (associatedSphereTrivialization S b).source :=
    t.mem_source.mpr (hbase.symm ▸ hp)
  have hcoord : (associatedSphereTrivialization S b z).2 = y := by
    have h := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p y hp
    rw [hg, one_smul] at h
    exact congrArg Prod.snd h
  have hnormalized : (S.trivialization b).toOpenPartialHomeomorph.symm (projection p, 1) = p := by
    have hsource := (S.trivialization b).mem_source.mpr hp
    have hpair : (projection p, 1) = S.trivialization b p :=
      Prod.ext ((S.trivialization b).proj_toFun p hsource).symm hg.symm
    rw [hpair]
    exact (S.trivialization b).toOpenPartialHomeomorph.left_inv hsource
  -- Identify the return after its normalized principal and sphere coordinates are fixed.
  have hvalue (p' : P) (y' : OrthogonalSphere r)
      (hpoint : associatedBundleMk G P (OrthogonalSphere r) p' y' = z)
      (hp' : p' = p) (hy' : y' = y) :
      TensorProduct.map (LinearMap.id : E (projection p) →ₗ[ℂ] E (projection p))
        (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ p' y' hpoint).mk'
          (TensorProduct.comm ℂ (F y') (E (projection p)) (u y' (projection p))) =
        associatedSphereTensorFiberEquiv S E σ p y
          (TensorProduct.comm ℂ (F y) (E (projection p)) (u y (projection p))) := by
    subst p'
    subst y'
    rfl
  change associatedSphereTensorBaseExtension S E σ b u z = _
  simp only [associatedSphereTensorBaseExtension, LinearMap.pi_apply, dite_eq_left hz,
    LinearMap.comp_apply, LinearMap.proj_apply]
  exact hvalue _ _ _ hnormalized hcoord

end AtiyahSinger

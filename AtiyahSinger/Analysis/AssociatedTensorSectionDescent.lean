/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorFiberCovariance

/-!
# Descent of whole covariant tensor families

Public module ID: M0191.

A family on all original principal representatives and all sphere points
satisfying the exact projection-transport covariance defines one unique
section of the original associated tensor bundle. The proof descends the
actual total tensor vector and then extracts its original quotient fiber.
Smoothness remains a separate assertion about the given atlases.
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
/-- Whole covariant tensor families descend uniquely to the original associated bundle. -/
theorem existsUnique_associatedSphereTensorSection_of_covariant
    (u : ∀ p : P, ∀ y : OrthogonalSphere r, E (projection p) ⊗[ℂ] F y)
    (hu : ∀ (p : P) (g : G) (y : OrthogonalSphere r),
      TensorProduct.map
          (LinearEquiv.cast (R := ℂ) (M := E) (S.projection_smul g p)).toLinearMap
          (σ.linearMap g y) (u (MulOpposite.op g • p) y) = u p (g • y)) :
    ∃! s : ∀ z : Z, T z,
      ∀ (p : P) (y : OrthogonalSphere r),
        s (associatedBundleMk G P (OrthogonalSphere r) p y) =
          associatedSphereTensorFiberEquiv S E σ p y (u p y) := by
  let f (p : P) (y : OrthogonalSphere r) : TotalSpace Unit T :=
    ⟨associatedBundleMk G P (OrthogonalSphere r) p y,
      associatedSphereTensorFiberEquiv S E σ p y (u p y)⟩
  -- The original action convention gives equality of actual total tensor vectors.
  have haction (p : P) (g : G) (y : OrthogonalSphere r) :
      f (MulOpposite.op g • p) y = f p (g • y) := by
    let h := associatedBundleMk_smul p g y
    have hvalue := associatedSphereTensorFiberEquiv_smul S E σ p g y
      (u (MulOpposite.op g • p) y)
    rw [hu p g y] at hvalue
    calc
      f (MulOpposite.op g • p) y =
          ⟨associatedBundleMk G P (OrthogonalSphere r) p (g • y),
            (LinearEquiv.cast (R := ℂ) (M := T) h)
              (associatedSphereTensorFiberEquiv S E σ (MulOpposite.op g • p) y
                (u (MulOpposite.op g • p) y))⟩ :=
        (TotalSpace.mk_cast (F := Unit) (E := T) h _).symm
      _ = f p (g • y) := congrArg
        (fun v ↦ (⟨associatedBundleMk G P (OrthogonalSphere r) p (g • y), v⟩ :
          TotalSpace Unit T)) hvalue
  let f' : Z → TotalSpace Unit T := Quotient.lift (fun x : P × OrthogonalSphere r ↦ f x.1 x.2)
    (by
      intro x z h
      obtain ⟨g, rfl⟩ := h
      change f x.1 x.2 = f (MulOpposite.op g • x.1) (g⁻¹ • x.2)
      rw [haction, smul_inv_smul])
  have hproj (z : Z) : (f' z).proj = z := by
    induction z using Quotient.inductionOn
    rfl
  let s (z : Z) : T z := (LinearEquiv.cast (R := ℂ) (M := T) (hproj z)) (f' z).snd
  have hs (p : P) (y : OrthogonalSphere r) :
      s (associatedBundleMk G P (OrthogonalSphere r) p y) =
        associatedSphereTensorFiberEquiv S E σ p y (u p y) := by
    change (LinearEquiv.cast (R := ℂ) (M := T)
      (hproj (associatedBundleMk G P (OrthogonalSphere r) p y)))
      (associatedSphereTensorFiberEquiv S E σ p y (u p y)) = _
    rfl
  refine ⟨s, hs, ?_⟩
  -- Quotient representatives cover every point, so the same values force uniqueness.
  intro t ht
  funext z
  induction z using Quotient.inductionOn with
  | h x => exact (ht x.1 x.2).trans (hs x.1 x.2).symm

end AtiyahSinger

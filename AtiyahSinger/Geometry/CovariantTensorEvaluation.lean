/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SeparatedCovariantDerivatives

/-!
# Evaluation and the full covariant tensor Leibniz formula

Public module ID: M1158.

Evaluate the actual recursive Hom fiber on an ordered list of tangent vectors.
The induced connection differentiates this evaluation and subtracts one tangent
connection term for each old slot. This is the full tensor connection formula
behind the original atlas recursion in SG III.2 (2.1), without antisymmetrization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 40

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace I (M := M)
local notation "V" => CovariantTensorFiber (n := n) (r := r) E
local notation "F" => CovariantTensorModel (n := n) (r := r) E

/-- Evaluate the actual k-fold native Hom fiber on the given ordered tangent vectors.
Linearity here is in the original tensor, with all its tangent arguments fixed. -/
def covariantTensorEvaluation : (k : ℕ) → (x : M) →
    (Fin k → TM x) → V k x →ₗ[ℝ] E x
  | 0, _, _ => LinearMap.id
  | k + 1, x, v =>
    (covariantTensorEvaluation k x (Fin.tail v)).comp
      ({ toFun := fun a : TM x →L[ℝ] V k x ↦ a (v 0)
         map_add' := fun _ _ ↦ rfl
         map_smul' := fun _ _ ↦ rfl } : (TM x →L[ℝ] V k x) →ₗ[ℝ] V k x)

variable {E}

/-- Differentiating tensor evaluation differentiates its value and every supplied tangent field.
The old-slot corrections use exactly the original supplied tangent connection. -/
theorem covariantTensorConnection_evaluation
    (covT : CovariantDerivative I (EuclideanSpace ℝ (Fin n)) TM)
    (covE : CovariantDerivative I (EuclideanSpace ℂ (Fin r)) E) (k : ℕ)
    (σ : ∀ x : M, V k x) (X : ∀ x : M, TM x)
    (Y : Fin k → ∀ x : M, TM x) (x : M)
    (hσ : MDifferentiableAt I ((I).prod 𝓘(ℝ, F k))
      (fun y ↦ (⟨y, σ y⟩ : TotalSpace (F k) (V k))) x)
    (hX : MDifferentiableAt I (I).tangent
      (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : ∀ i : Fin k, MDifferentiableAt I (I).tangent
      (fun y ↦ (⟨y, Y i y⟩ : TangentBundle I M)) x) :
    covariantTensorEvaluation E k x (fun i ↦ Y i x)
        (covariantTensorConnection covT covE k σ x (X x)) =
      covE (fun y ↦ covariantTensorEvaluation E k y (fun i ↦ Y i y) (σ y)) x (X x) -
        ∑ i : Fin k, covariantTensorEvaluation E k x
          (Function.update (fun j ↦ Y j x) i (covT (Y i) x (X x))) (σ x) := by
  classical
  induction k with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    rfl
  | succ k ih =>
    let A : ∀ y : M, TM y →L[ℝ] V k y := σ
    let Z : ∀ y : M, V k y := fun y ↦ A y (Y 0 y)
    have hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] F k))
        (fun y ↦ (⟨y, A y⟩ : TotalSpace (EuclideanSpace ℝ (Fin n) →L[ℝ] F k)
          (fun y ↦ TM y →L[ℝ] V k y))) x := hσ
    have hZ : MDifferentiableAt I ((I).prod 𝓘(ℝ, F k))
        (fun y ↦ (⟨y, Z y⟩ : TotalSpace (F k) (V k))) x :=
      hA.clm_bundle_apply (hY 0)
    -- The first Hom step differentiates the first field and the remaining tensor separately.
    have hfirst := covariantHomConnection_apply covT
      (covariantTensorConnection covT covE k) A X (Y 0) x hA hX (hY 0)
    have htail := ih Z (fun i ↦ Y i.succ) hZ (fun i ↦ hY i.succ)
    change covariantTensorEvaluation E k x (fun i ↦ Y i.succ x)
      (covariantHomConnection covT (covariantTensorConnection covT covE k) A x
        (X x) (Y 0 x)) = _
    rw [hfirst, map_sub, htail]
    -- Splitting the old-slot sum separates the first correction from all tail corrections.
    rw [Fin.sum_univ_succ]
    have hzero : covariantTensorEvaluation E (k + 1) x
        (Function.update (fun j ↦ Y j x) 0 (covT (Y 0) x (X x))) (σ x) =
      covariantTensorEvaluation E k x (fun i ↦ Y i.succ x)
        (A x (covT (Y 0) x (X x))) := by
      simp [covariantTensorEvaluation, Fin.tail_def, Function.update, A]
      rfl
    have hsucc (i : Fin k) : covariantTensorEvaluation E (k + 1) x
        (Function.update (fun j ↦ Y j x) i.succ (covT (Y i.succ) x (X x))) (σ x) =
      covariantTensorEvaluation E k x
        (Function.update (fun j ↦ Y j.succ x) i (covT (Y i.succ) x (X x))) (Z x) := by
      have hizero : (0 : Fin (k + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simp only [covariantTensorEvaluation, Fin.tail_update_succ,
        Function.update_of_ne hizero]
      rfl
    rw [hzero]
    simp_rw [hsucc]
    have hvalue : (fun y ↦ covariantTensorEvaluation E (k + 1) y
        (fun i ↦ Y i y) (σ y)) =
      fun y ↦ covariantTensorEvaluation E k y (fun i ↦ Y i.succ y) (Z y) := rfl
    rw [hvalue]
    abel

end AtiyahSinger

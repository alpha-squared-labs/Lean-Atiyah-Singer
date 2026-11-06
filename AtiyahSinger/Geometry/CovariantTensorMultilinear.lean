/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CovariantTensorEvaluation
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Multilinear and differential properties of native tensor evaluation

Public module ID: M1159.

The recursive Hom fiber evaluates multilinearly in its tangent arguments.
Evaluation of differentiable tensor and tangent sections is differentiable in
the original bundle topology. These standard tensor properties justify the
coordinate expansion of the full connection formula in SG III.2 (2.1).
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

/-- The native Hom tensor determines its usual real multilinear map on tangent vectors. -/
def covariantTensorMultilinearMap : (k : ℕ) → (x : M) →
    V k x →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin k ↦ TM x) (E x)
  | 0, x => (MultilinearMap.constLinearEquivOfIsEmpty
      (R := ℝ) (S := ℝ) (M₁ := fun _ : Fin 0 ↦ TM x) (M₂ := E x)).toLinearMap
  | k + 1, x =>
    { toFun := fun a ↦ ((covariantTensorMultilinearMap k x).comp a.toLinearMap).uncurryLeft
      map_add' := by
        intro a d
        change TM x →L[ℝ] V k x at a d
        ext v
        change (covariantTensorMultilinearMap k x ((a + d) (v 0))) (Fin.tail v) = _
        simp
      map_smul' := by
        intro c a
        change TM x →L[ℝ] V k x at a
        ext v
        change (covariantTensorMultilinearMap k x ((c • a) (v 0))) (Fin.tail v) = _
        simp }

/-- The multilinear tensor map is precisely the original ordered evaluation. -/
theorem covariantTensorMultilinearMap_apply (k : ℕ) (x : M)
    (a : V k x) (v : Fin k → TM x) :
    covariantTensorMultilinearMap E k x a v = covariantTensorEvaluation E k x v a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change TM x →L[ℝ] V k x at a
    change covariantTensorMultilinearMap E k x (a (v 0)) (Fin.tail v) = _
    rw [ih]
    rfl

variable {E}

/-- Evaluating differentiable native tensor and tangent sections preserves differentiability. -/
theorem mdifferentiableAt_covariantTensorEvaluation (k : ℕ)
    (σ : ∀ x : M, V k x) (Y : Fin k → ∀ x : M, TM x) (x : M)
    (hσ : MDifferentiableAt I ((I).prod 𝓘(ℝ, F k))
      (fun y ↦ (⟨y, σ y⟩ : TotalSpace (F k) (V k))) x)
    (hY : ∀ i : Fin k, MDifferentiableAt I (I).tangent
      (fun y ↦ (⟨y, Y i y⟩ : TangentBundle I M)) x) :
    MDifferentiableAt I ((I).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r)))
      (fun y ↦ (⟨y, covariantTensorEvaluation E k y (fun i ↦ Y i y) (σ y)⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x := by
  induction k with
  | zero => exact hσ
  | succ k ih =>
    -- Evaluation at the first field is a differentiable bundle-Hom application.
    let A : ∀ y : M, TM y →L[ℝ] V k y := σ
    have hfirst : MDifferentiableAt I ((I).prod 𝓘(ℝ, F k))
        (fun y ↦ (⟨y, A y (Y 0 y)⟩ : TotalSpace (F k) (V k))) x :=
      hσ.clm_bundle_apply (hY 0)
    exact ih (fun y ↦ A y (Y 0 y)) (fun i ↦ Y i.succ) hfirst (fun i ↦ hY i.succ)

end AtiyahSinger

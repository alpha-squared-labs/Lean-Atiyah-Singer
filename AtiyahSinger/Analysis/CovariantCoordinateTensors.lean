/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Coordinate reconstruction and differentiation of full covariant tensors

Public module ID: M0425.

Finite coordinate arrays determine the usual real multilinear tensor on the
Euclidean model. The coordinate covariant derivative differentiates that tensor,
adds the value-connection action, and subtracts the tangent action in each old
slot. This is the full tensor connection formula used in SG III.2 (2.1).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

variable (n k : ℕ) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reconstruct the standard multilinear tensor from its values on ordered coordinate bases. -/
def tensorFromComponents : ((Fin k → Fin n) → V) →L[ℝ]
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n)) V :=
  ∑ p : Fin k → Fin n,
    (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n)) V
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
        (fun a ↦ EuclideanSpace.proj (p a)))).comp (ContinuousLinearMap.proj p)

/-- Coordinate reconstruction is the finite multilinear expansion in the original ordered basis. -/
theorem tensorFromComponents_apply (v : (Fin k → Fin n) → V)
    (X : Fin k → EuclideanSpace ℝ (Fin n)) :
    tensorFromComponents n k V v X = ∑ p, (∏ a, X a (p a)) • v p := by
  simp [tensorFromComponents]

/-- Reconstruction recovers each original array entry, including the empty tensor order. -/
theorem tensorFromComponents_basis (v : (Fin k → Fin n) → V) (p : Fin k → Fin n) :
    tensorFromComponents n k V v (fun a ↦ EuclideanSpace.single (p a) 1) = v p := by
  classical
  rw [tensorFromComponents_apply]
  have hprod (q : Fin k → Fin n) :
      (∏ a : Fin k, (EuclideanSpace.single (p a) (1 : ℝ)) (q a)) =
        if q = p then 1 else 0 := by
    by_cases h : q = p
    · subst q
      simp
    · rw [ite_eq_right h]
      obtain ⟨a, ha⟩ := Function.ne_iff.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [ha]
  simp only [hprod, ite_smul, one_smul, zero_smul]
  simp

/-- The standard coordinate connection differentiates the tensor and corrects all old slots. -/
def tensorConnectionDerivative
    (R : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n)) V)
    (dR : EuclideanSpace ℝ (Fin n) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n)) V)
    (ΓE : EuclideanSpace ℝ (Fin n) →L[ℝ] V →L[ℝ] V)
    (ΓT : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ EuclideanSpace ℝ (Fin n)) V := by
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let C := ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ H) V
  -- Postcomposition applies the same value connection to the tensor output.
  let post : H →ₗ[ℝ] C := {
    toFun := fun x ↦ (ΓE x).compContinuousMultilinearMap R
    map_add' := by
      intro x y
      ext Y
      change ΓE (x + y) (R Y) = ΓE x (R Y) + ΓE y (R Y)
      rw [map_add]
      rfl
    map_smul' := by
      intro c x
      ext Y
      change ΓE (c • x) (R Y) = c • ΓE x (R Y)
      rw [map_smul]
      rfl }
  let pre (a : Fin k) (Z : H →L[ℝ] H) : C :=
    R.compContinuousLinearMap (Function.update (fun _ ↦ ContinuousLinearMap.id ℝ H) a Z)
  have hpre (a : Fin k) (Z : H →L[ℝ] H) (Y : Fin k → H) :
      pre a Z Y = R (Function.update Y a (Z (Y a))) := by
    change R (fun b ↦ (Function.update (fun _ ↦ ContinuousLinearMap.id ℝ H) a Z) b
      (Y b)) = R (Function.update Y a (Z (Y a)))
    congr 1
    funext b
    by_cases h : b = a
    · subst b
      simp
    · simp [Function.update_of_ne h]
  -- In each old slot, precomposition is linear in the inserted connection map.
  let old (a : Fin k) : H →ₗ[ℝ] C := {
    toFun := fun x ↦ pre a (ΓT x)
    map_add' := by
      intro x y
      ext Y
      change pre a (ΓT (x + y)) Y = pre a (ΓT x) Y + pre a (ΓT y) Y
      rw [hpre, hpre, hpre, map_add, add_apply, R.map_update_add]
    map_smul' := by
      intro c x
      ext Y
      change pre a (ΓT (c • x)) Y = c • pre a (ΓT x) Y
      rw [hpre, hpre, map_smul, smul_apply, R.map_update_smul] }
  -- The derivative direction is the new first slot; the original order is retained.
  exact (dR + post.toContinuousLinearMap - ∑ a : Fin k,
    (old a).toContinuousLinearMap).uncurryLeft

/-- Evaluation is the full tensor Leibniz formula, with the new derivative direction first. -/
theorem tensorConnectionDerivative_apply
    (R : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n)) V)
    (dR : EuclideanSpace ℝ (Fin n) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclideanSpace ℝ (Fin n)) V)
    (ΓE : EuclideanSpace ℝ (Fin n) →L[ℝ] V →L[ℝ] V)
    (ΓT : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) :
    tensorConnectionDerivative n k V R dR ΓE ΓT X =
      dR (X 0) (Fin.tail X) + ΓE (X 0) (R (Fin.tail X)) -
        ∑ a : Fin k, R (Function.update (Fin.tail X) a (ΓT (X 0) (X a.succ))) := by
  classical
  simp only [tensorConnectionDerivative, ContinuousLinearMap.uncurryLeft_apply,
    sub_apply, add_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change R (fun b ↦ (Function.update
    (fun _ ↦ ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) a (ΓT (X 0))) b
      (X b.succ)) = R (Function.update (Fin.tail X) a (ΓT (X 0) (X a.succ)))
  congr 1
  funext b
  by_cases h : b = a
  · subst b
    simp
  · simp [Function.update_of_ne h, Fin.tail_def]

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Covariant differentiation in an arbitrary local tangent frame

Public module ID: M1296.

The native covariant derivative has the ordinary derivative-plus-connection-form
expression in a supplied local frame. The supplied frame fields and
their actual native coefficients are retained. Only germs at the evaluation
point are used; no global smooth extension or separation assumption is needed.

Source: the local connection formula, Spin Geometry II.4. This extends the
project's native-trivialization formula to the lifted orthonormal spin frames.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ, H)
local notation "TM" => TangentSpace I (M := M)

/-- The actual connection differentiates the original coefficients in any supplied local frame. -/
theorem tangentCovariantDerivative_eq_sum_localFrame
    (cov : CovariantDerivative I H TM) (s : Fin n → ∀ y : M, TM y)
    (U : Set M) (hU : IsOpen U) (hs : IsLocalFrameOn I H ∞ s U)
    (σ : ∀ y : M, TM y) (x : M) (hx : x ∈ U)
    (hσ : MDifferentiableAt I (I).tangent
      (fun y ↦ (⟨y, σ y⟩ : TangentBundle I M)) x)
    (hc : ∀ i : Fin n, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ hs.coeff i y (σ y)) x) (X : TM x) :
    cov σ x X = ∑ i : Fin n,
      (hs.coeff i x (σ x) • cov (s i) x X +
        mvfderiv I (fun y ↦ hs.coeff i y (σ y)) x X • s i x) := by
  classical
  let c (i : Fin n) (y : M) := hs.coeff i y (σ y)
  let t (i : Fin n) (y : M) : TM y := c i y • s i y
  have hsi (i : Fin n) : MDifferentiableAt I (I).tangent
      (fun y ↦ (⟨y, s i y⟩ : TangentBundle I M)) x :=
    (hs.contMDiffAt hU hx i).mdifferentiableAt (by simp)
  have hti (i : Fin n) : MDifferentiableAt I (I).tangent
      (fun y ↦ (⟨y, t i y⟩ : TangentBundle I M)) x :=
    (hc i).smul_section (hsi i)
  -- Locality lets us use the exact coefficient expansion without extending the frame.
  have hexpand : cov σ x = cov (fun y ↦ ∑ i : Fin n, t i y) x :=
    (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq hσ
      (.sum_section (fun i _ ↦ hti i)) Filter.univ_mem
      (hs.eventually_eq_sum_coeff_smul σ (hU.mem_nhds hx))
  -- Finite additivity is applied only to the locally differentiable summands.
  have hsum (a : Finset (Fin n)) :
      cov (fun y ↦ ∑ i ∈ a, t i y) x = ∑ i ∈ a, cov (t i) x := by
    induction a using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact cov.isCovariantDerivativeOn.zero
    | @insert i a hi ih =>
      simp only [Finset.sum_insert hi]
      change cov (t i + fun y ↦ ∑ j ∈ a, t j y) x = _
      rw [cov.isCovariantDerivativeOn.add (hti i)
        (.sum_section (fun j _ ↦ hti j)), ih]
  rw [congrArg (fun L ↦ L X) hexpand, hsum]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun L ↦ L X)
    (cov.isCovariantDerivativeOn.leibniz (hsi i) (hc i))
  exact h

/-- Two original local frames give the usual matrix gauge law for the same native connection. -/
theorem tangentCovariantDerivative_localFrame_gauge
    (cov : CovariantDerivative I H TM) (s t : Fin n → ∀ y : M, TM y)
    (U : Set M) (hU : IsOpen U)
    (hs : IsLocalFrameOn I H ∞ s U) (ht : IsLocalFrameOn I H ∞ t U)
    (x : M) (hx : x ∈ U)
    (hT : ∀ i j : Fin n, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ ht.coeff j y (s i y)) x) (i k : Fin n) (X : TM x) :
    (∑ j : Fin n, hs.coeff j x (cov (s i) x X) * ht.coeff k x (s j x)) =
      (∑ j : Fin n, ht.coeff j x (s i x) * ht.coeff k x (cov (t j) x X)) +
        mvfderiv I (fun y ↦ ht.coeff k y (s i y)) x X := by
  classical
  -- Differentiate the same source frame vector in the second frame.
  have h := tangentCovariantDerivative_eq_sum_localFrame cov t U hU ht (s i) x hx
    ((hs.contMDiffAt hU hx i).mdifferentiableAt (by simp)) (hT i) X
  have hcoord := congrArg (ht.coeff k x) h
  rw [map_sum] at hcoord
  simp only [map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib] at hcoord
  have hb (j : Fin n) : ht.coeff k x (t j x) = if j = k then 1 else 0 := by
    rw [ht.coeff_apply_of_mem hx (t j) k]
    have hvec : t j x = ht.toBasisAt hx j := (ht.toBasisAt_coe hx j).symm
    rw [hvec, (ht.toBasisAt hx).repr_self]
    simp [Finsupp.single_apply, eq_comm]
  simp only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at hcoord
  -- Expand that derivative in the first frame, then read its second-frame coordinate.
  have hexpand := congrArg (ht.coeff k x)
    ((hs.toBasisAt hx).sum_repr (cov (s i) x X))
  rw [map_sum] at hexpand
  simp only [map_smul, smul_eq_mul, hs.toBasisAt_coe] at hexpand
  have hc (j : Fin n) :
      (hs.toBasisAt hx).repr (cov (s i) x X) j = hs.coeff j x (cov (s i) x X) := by
    simp only [IsLocalFrameOn.coeff, dite_eq_left hx]
    rfl
  simp only [hc] at hexpand
  exact hexpand.trans hcoord

end AtiyahSinger

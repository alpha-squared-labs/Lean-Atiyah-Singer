/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TensorContraction
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Basis independence of the full multilinear contraction

Public module ID: M1302.

The contraction of two covariant tensors against a dual bilinear form and a
value bilinear form is independent of the tangent basis. Repeatedly curry the
first slot and apply the linear tensor contraction identity. The formula retains
all ordered slots and does not require positivity or an orthonormal basis.
This supplies the algebraic comparison of varying-rank covariant tensor norms
in SG III.2 (2.1), without introducing native norms on the value fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module LinearMap
open scoped BigOperators

universe w

/-- Full contraction of the same two multilinear tensors is independent of the basis. -/
theorem sum_multilinear_pairing_basis_eq
    {K U V : Type*} {ι κ : Type w} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ]
    (b : Basis ι K U) (c : Basis κ K U)
    (g : LinearMap.BilinForm K (Module.Dual K U)) (h : LinearMap.BilinForm K V)
    (k : ℕ) (A B : MultilinearMap K (fun _ : Fin k ↦ U) V) :
    (∑ p : Fin k → ι, ∑ q : Fin k → ι,
      (∏ a : Fin k, g (b.coord (p a)) (b.coord (q a))) *
        h (A (fun a ↦ b (p a))) (B (fun a ↦ b (q a)))) =
      ∑ p : Fin k → κ, ∑ q : Fin k → κ,
        (∏ a : Fin k, g (c.coord (p a)) (c.coord (q a))) *
          h (A (fun a ↦ c (p a))) (B (fun a ↦ c (q a))) := by
  classical
  let value {δ : Type w} [Fintype δ] (d : Basis δ K U) (j : ℕ)
      (F G : MultilinearMap K (fun _ : Fin j ↦ U) V) : K :=
    ∑ p : Fin j → δ, ∑ q : Fin j → δ,
      (∏ a : Fin j, g (d.coord (p a)) (d.coord (q a))) *
        h (F (fun a ↦ d (p a))) (G (fun a ↦ d (q a)))
  -- Isolate the first ordered slot in both tensors; the remaining contraction is bilinear.
  have hstep {δ : Type w} [Fintype δ] (d : Basis δ K U) (j : ℕ)
      (F G : MultilinearMap K (fun _ : Fin (j + 1) ↦ U) V) :
      value d (j + 1) F G = ∑ i : δ, ∑ l : δ, g (d.coord i) (d.coord l) *
        value d j (F.curryLeft (d i)) (G.curryLeft (d l)) := by
    dsimp only [value]
    rw [← (Fin.consEquiv (fun _ : Fin (j + 1) ↦ δ)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply]
    simp_rw [← (Fin.consEquiv (fun _ : Fin (j + 1) ↦ δ)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ, MultilinearMap.curryLeft_apply]
    simp_rw [Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    have hcomp (z : δ) (v : Fin j → δ) :
        (fun a : Fin (j + 1) ↦ d (Fin.cons (α := fun _ : Fin (j + 1) ↦ δ) z v a)) =
          Fin.cons (α := fun _ : Fin (j + 1) ↦ U) (d z) (fun a ↦ d (v a)) := by
      funext a
      refine Fin.cases ?_ (fun i ↦ ?_) a
      · rfl
      · rfl
    rw [hcomp i p, hcomp l q]
  change value b k A B = value c k A B
  induction k with
  | zero =>
    simp only [value, Finset.prod_empty, Finset.univ_eq_empty, one_mul]
    have heq : (fun a : Fin 0 ↦ b ((default : Fin 0 → ι) a)) =
        fun a : Fin 0 ↦ c ((default : Fin 0 → κ) a) :=
      funext (fun a ↦ Fin.elim0 a)
    simpa only [Finset.univ_unique, Finset.sum_singleton] using congrArg₂ (fun x y : V ↦ h x y)
      (congrArg A heq) (congrArg B heq)
  | succ k ih =>
    let H : LinearMap.BilinForm K (MultilinearMap K (fun _ : Fin k ↦ U) V) :=
      LinearMap.mk₂ K (value c k)
        (by
          intro F G J
          simp only [value, _root_.add_apply, map_add, LinearMap.add_apply,
            mul_add, Finset.sum_add_distrib])
        (by
          intro t F G
          simp only [value, _root_.smul_apply, map_smul, LinearMap.smul_apply,
            smul_eq_mul, mul_left_comm _ t, Finset.mul_sum])
        (by
          intro F G J
          simp only [value, _root_.add_apply, map_add, mul_add,
            Finset.sum_add_distrib])
        (by
          intro t F G
          simp only [value, _root_.smul_apply, map_smul, smul_eq_mul,
            mul_left_comm _ t, Finset.mul_sum])
    rw [hstep b, hstep c]
    simp_rw [ih]
    -- One-slot basis independence applies to the same curried maps and tail form.
    exact sum_tensor_pairing_basis_eq b c g H A.curryLeft B.curryLeft

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.IndexDirectSum
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finite additivity of the algebraic Fredholm index

Public module ID: M0757.

A finite family of maps with finite-dimensional kernels and cokernels has an
index equal to the sum of its component indices. The original domain and
codomain spaces can be infinite-dimensional, and the index set can be empty.
This is the finite direct-sum form of the index argument in SG III.13, p.247,
used for the actual diagonal blocks on the compact manifold's clopen components.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {𝕜 ι : Type*} [DivisionRing 𝕜] [Fintype ι]
  {E F : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- Finite direct sums add indices when each summand has finite kernel and cokernel. -/
theorem index_piMap (P : ∀ i, E i →ₗ[𝕜] F i)
    [∀ i, FiniteDimensional 𝕜 (P i).ker]
    [∀ i, FiniteDimensional 𝕜 (F i ⧸ (P i).range)] :
    (LinearMap.piMap P).index = ∑ i, (P i).index := by
  classical
  -- The kernel is the product of the original individual kernels.
  let eKer : (LinearMap.piMap P).ker ≃ₗ[𝕜] (∀ i, (P i).ker) := {
    toFun u i := ⟨u.val i, congrFun u.property i⟩
    invFun v := ⟨fun i ↦ (v i).val, funext (fun i ↦ (v i).property)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hker : Module.finrank 𝕜 (LinearMap.piMap P).ker =
      ∑ i, Module.finrank 𝕜 (P i).ker :=
    eKer.finrank_eq.trans (Module.finrank_pi_fintype 𝕜)
  -- The coordinate quotient maps have the block range as their exact common kernel.
  let Q : (∀ i, F i) →ₗ[𝕜] ∀ i, F i ⧸ (P i).range :=
    LinearMap.piMap (fun i ↦ (P i).range.mkQ)
  have hsurj : Function.Surjective Q := by
    intro y
    choose x hx using fun i ↦ (P i).range.mkQ_surjective (y i)
    exact ⟨x, funext hx⟩
  have hQker : Q.ker = (LinearMap.piMap P).range := by
    ext y
    constructor
    · intro hy
      have hi (i : ι) : y i ∈ (P i).range := by
        have h := congrFun hy i
        exact (Submodule.Quotient.mk_eq_zero (p := (P i).range)).mp h
      choose x hx using hi
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      apply funext
      intro i
      exact (Submodule.Quotient.mk_eq_zero (p := (P i).range)).mpr ⟨x i, rfl⟩
  have hcoker : Module.finrank 𝕜 ((∀ i, F i) ⧸ (LinearMap.piMap P).range) =
      ∑ i, Module.finrank 𝕜 (F i ⧸ (P i).range) := by
    have h := (Q.quotKerEquivOfSurjective hsurj).finrank_eq
    rw [hQker, Module.finrank_pi_fintype] at h
    exact h
  -- Subtract the two finite dimension sums in the original integer-valued index.
  simp only [LinearMap.index_eq_finrank_sub, hker, hcoker, Nat.cast_sum, Finset.sum_sub_distrib]

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationGrothendieckGroup
public import Mathlib.LinearAlgebra.Pi

/-!
# Finite products in the original representation Grothendieck group

Public module ID: M0027.

A finite product of specified finite continuous representations has actual
equivariant finite coordinates and its original class is their sum. The empty
family has zero class. This supplies the full representation-valued finite
kernel and cokernel decomposition needed by the clopen analytic-index argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A finite product has actual finite coordinates and the sum of the original classes. -/
theorem exists_finiteContinuousRepresentation_finPi (n : ℕ)
    (ρ : Fin n → FiniteContinuousRepresentation G) :
    ∃ σ : FiniteContinuousRepresentation G,
      ∃ e : (Fin σ.dimension → ℂ) ≃ₗ[ℂ] (∀ i, Fin (ρ i).dimension → ℂ),
        (∀ g v i, e (σ.representation g v) i = (ρ i).representation g (e v i)) ∧
        finiteRepresentationClass σ = ∑ i, finiteRepresentationClass (ρ i) := by
  induction n with
  | zero =>
    -- The zero-dimensional action is equivalent to its own direct sum, hence has zero class.
    let σ : FiniteContinuousRepresentation G := {
      dimension := 0
      representation := .ofMonoidHom 1
      continuous_action := continuous_snd }
    let e : (Fin σ.dimension → ℂ) ≃ₗ[ℂ] (∀ i, Fin (ρ i).dimension → ℂ) :=
      LinearEquiv.ofSubsingleton _ _
    refine ⟨σ, e, fun _ _ i ↦ Fin.elim0 i, ?_⟩
    have hiso : σ.IsEquivalent (σ.directSum σ) := by
      refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
      intro g
      apply ContinuousLinearMap.ext
      intro v
      funext i
      exact Fin.elim0 (show Fin 0 from i)
    have hclass := finiteRepresentationClass_eq_of_isEquivalent σ (σ.directSum σ) hiso
    rw [finiteRepresentationClass_directSum] at hclass
    have hz : finiteRepresentationClass σ = 0 := by
      have h : finiteRepresentationClass σ + 0 =
          finiteRepresentationClass σ + finiteRepresentationClass σ := by
        simpa only [add_zero] using hclass
      exact (add_left_cancel h).symm
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hz
  | succ n ih =>
    obtain ⟨τ, d, hd, hclass⟩ := ih (fun i ↦ ρ i.succ)
    let σ := (ρ 0).directSum τ
    let a : (Fin ((ρ 0).dimension + τ.dimension) → ℂ) ≃L[ℂ]
        (Fin (ρ 0).dimension → ℂ) × (Fin τ.dimension → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : Fin (ρ 0).dimension ⊕ Fin τ.dimension ↦ ℂ) finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ
          (Fin (ρ 0).dimension) (Fin τ.dimension) (fun _ ↦ ℂ))
    let e := (a.toLinearEquiv.trans ((LinearEquiv.refl ℂ _).prodCongr d)).trans
      (Fin.consLinearEquiv ℂ (fun i ↦ Fin (ρ i).dimension → ℂ))
    have ha (g : G) (v : Fin σ.dimension → ℂ) :
        a (σ.representation g v) =
          ((ρ 0).representation g (a v).1, τ.representation g (a v).2) := by
      change a (a.symm ((ρ 0).representation g (a v).1,
        τ.representation g (a v).2)) = _
      exact a.apply_symm_apply _
    refine ⟨σ, e, ?_, ?_⟩
    · -- Ordered sum coordinates intertwine the head and every coordinate of the tail.
      intro g v i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change (a (σ.representation g v)).1 = (ρ 0).representation g (a v).1
        exact congrArg Prod.fst (ha g v)
      · change d ((a (σ.representation g v)).2) j =
          (ρ j.succ).representation g (d (a v).2 j)
        rw [ha]
        exact hd g (a v).2 j
    · rw [finiteRepresentationClass_directSum, hclass, Fin.sum_univ_succ]

end AtiyahSinger

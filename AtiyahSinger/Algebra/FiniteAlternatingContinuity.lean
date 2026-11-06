/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Algebraic and continuous forms in finite dimension

Public module ID: M0024.

Every complex-valued alternating form on a finite-dimensional real normed vector
space is continuous. The resulting complex linear equivalence preserves the
literal function on tuples; its continuity proof uses a finite basis expansion.

Source: finite-dimensional multilinear algebra. This adapter connects the actual
algebraic exterior pairing with the original continuous differential form fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 600000 in
-- Expand over one finite real basis, keeping the original tuple evaluations unchanged.
set_option backward.isDefEq.respectTransparency false in
/-- Algebraic and continuous complex-valued alternating forms are canonically equivalent. -/
def realAlternatingContinuousEquiv (p : ℕ) :
    (E [⋀^Fin p]→ₗ[ℝ] ℂ) ≃ₗ[ℂ] (E [⋀^Fin p]→L[ℝ] ℂ) := by
  classical
  have hc (a : E [⋀^Fin p]→ₗ[ℝ] ℂ) : Continuous a := by
    let b := Module.finBasis ℝ E
    have hexpand (v : Fin p → E) :
        a v = ∑ j : Fin p → Fin (Module.finrank ℝ E),
          (∏ i, b.repr (v i) (j i)) • a (fun i ↦ b (j i)) := by
      have h (i : Fin p) : v i = ∑ j, b.repr (v i) j • b j := (b.sum_repr (v i)).symm
      calc
        a v = a (fun i ↦ ∑ j, b.repr (v i) j • b j) := congrArg a (funext h)
        _ = ∑ j : Fin p → Fin (Module.finrank ℝ E),
            a (fun i ↦ b.repr (v i) (j i) • b (j i)) :=
          a.toMultilinearMap.map_sum (fun i j ↦ b.repr (v i) j • b j)
        _ = _ := Finset.sum_congr rfl (fun j _ ↦
          a.map_smul_univ (fun i ↦ b.repr (v i) (j i)) (fun i ↦ b (j i)))
    have hs : Continuous (fun v : Fin p → E ↦
        ∑ j : Fin p → Fin (Module.finrank ℝ E),
          (∏ i, b.repr (v i) (j i)) • a (fun i ↦ b (j i))) := by
      apply continuous_finsetSum
      intro j _
      have hp : Continuous (fun v : Fin p → E ↦ ∏ i, b.repr (v i) (j i)) := by
        apply continuous_finsetProd
        intro i _
        exact (continuous_apply (j i)).comp
          (b.continuous_coe_repr.comp (continuous_apply i))
      exact hp.smul (continuous_const (y := a (fun i ↦ b (j i))))
    exact hs.congr (fun v ↦ (hexpand v).symm)
  exact
    { toFun a := { a with cont := hc a }
      invFun a := a.toAlternatingMap
      left_inv a := rfl
      right_inv a := by
        apply ContinuousAlternatingMap.ext
        intro v
        rfl
      map_add' a b := by
        apply ContinuousAlternatingMap.ext
        intro v
        rfl
      map_smul' z a := by
        apply ContinuousAlternatingMap.ext
        intro v
        rfl }

end AtiyahSinger

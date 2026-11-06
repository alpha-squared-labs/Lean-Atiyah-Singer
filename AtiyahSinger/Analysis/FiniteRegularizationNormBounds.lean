/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Paired norm estimates for a fixed finite regularization

Public module ID: M0630.

This project supplement turns the coordinate certificate and operator-norm bound of a
specified finite family into its positive-order pointwise error bound. The original
negative-order estimate controls the same error by changing its sign. All linear maps,
finite pieces, residuals and constants are supplied; no new witness is selected.
-/

@[expose] public section

namespace AtiyahSinger

open scoped BigOperators

/-- A fixed finite regularization inherits the paired bounds of its original residual error. -/
theorem finite_regularization_paired_norm_bounds
    {D E X₁ X₀ Y₀ Yneg ι κ₀ κ₁ : Type*}
    [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup X₀] [NormedSpace ℂ X₀]
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀]
    [NormedAddCommGroup Yneg] [NormedSpace ℂ Yneg]
    [Fintype κ₀] [Fintype κ₁]
    (j₁ : D →ₗ[ℂ] X₁) (j₀ : D →ₗ[ℂ] X₀)
    (out₀ : E →ₗ[ℂ] Y₀) (outNeg : E →ₗ[ℂ] Yneg)
    (T Tbase W : D →ₗ[ℂ] E)
    (P : ι → D →ₗ[ℂ] E)
    (pieces : ι → κ₀ → κ₁ → D →ₗ[ℂ] E)
    (raw : ι → κ₀ → κ₁ → D → E)
    (Rbase : X₁ →L[ℂ] Y₀) (Rcutoff : ι → X₁ →L[ℂ] Y₀)
    (Cp Cn : ℝ) (ε : ι → ℝ)
    (hdecomp : T = Tbase + W)
    (hbase : ∀ u, Rbase (j₁ u) = out₀ (Tbase u))
    (hpieces : ∀ t k j u, pieces t k j u = raw t k j u)
    (hsum : ∀ t, P t = ∑ k, ∑ j, pieces t k j)
    (hcutoff : ∀ t u,
      Rcutoff t (j₁ u) = out₀ (∑ k, ∑ j, pieces t k j u))
    (hbound : ∀ t, ‖Rcutoff t - Rbase‖ ≤ Cp * ε t)
    (hnegative : ∀ t u,
      ‖outNeg (T u - ((∑ k, ∑ j, raw t k j u) + W u))‖ ≤
        Cn * ε t * ‖j₀ u‖)
    (t : ι) (u : D) :
    (‖out₀ (P t u - T u + W u)‖ ≤ Cp * ε t * ‖j₁ u‖) ∧
      (‖outNeg (P t u - T u + W u)‖ ≤ Cn * ε t * ‖j₀ u‖) := by
  classical
  -- Evaluate the given finite operator sum once, keeping every specified piece.
  have hsumEval : P t u = ∑ k, ∑ j, pieces t k j u := by
    calc
      P t u = (∑ k, ∑ j, pieces t k j) u := LinearMap.congr_fun (hsum t) u
      _ = ∑ k, (∑ j, pieces t k j) u :=
        LinearMap.sum_apply Finset.univ (fun k ↦ ∑ j, pieces t k j) u
      _ = ∑ k, ∑ j, pieces t k j u :=
        Finset.sum_congr rfl fun k _ ↦
          LinearMap.sum_apply Finset.univ (pieces t k) u
  have hraw : P t u = ∑ k, ∑ j, raw t k j u := by
    refine hsumEval.trans ?_
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    exact hpieces t k j u
  -- The positive-order error is the fixed cutoff operator minus its fixed base.
  have hcut : Rcutoff t (j₁ u) = out₀ (P t u) :=
    (hcutoff t u).trans (congrArg out₀ hsumEval.symm)
  have hTu : T u = Tbase u + W u := LinearMap.congr_fun hdecomp u
  have hsection : P t u - T u + W u = P t u - Tbase u := by
    rw [hTu, sub_add_eq_sub_sub, sub_add_cancel]
  have hcoordinates : out₀ (P t u - T u + W u) =
      (Rcutoff t - Rbase) (j₁ u) := by
    calc
      out₀ (P t u - T u + W u) = out₀ (P t u - Tbase u) :=
        congrArg out₀ hsection
      _ = out₀ (P t u) - out₀ (Tbase u) := map_sub out₀ _ _
      _ = Rcutoff t (j₁ u) - Rbase (j₁ u) :=
        congrArg₂ (fun x y : Y₀ ↦ x - y) hcut.symm (hbase u).symm
      _ = (Rcutoff t - Rbase) (j₁ u) := rfl
  have hpositive : ‖out₀ (P t u - T u + W u)‖ ≤ Cp * ε t * ‖j₁ u‖ :=
    (congrArg (fun y : Y₀ ↦ ‖y‖) hcoordinates).le.trans
      ((Rcutoff t - Rbase).le_of_opNorm_le (hbound t) (j₁ u))
  -- The negative-order certificate concerns the opposite of this exact same error.
  have hopposite : P t u - T u + W u =
      -(T u - ((∑ k, ∑ j, raw t k j u) + W u)) := by
    calc
      P t u - T u + W u = (P t u + W u) - T u :=
        sub_add_eq_add_sub (P t u) (T u) (W u)
      _ = ((∑ k, ∑ j, raw t k j u) + W u) - T u :=
        congrArg (fun v : E ↦ (v + W u) - T u) hraw
      _ = -(T u - ((∑ k, ∑ j, raw t k j u) + W u)) := (neg_sub _ _).symm
  have hnegativeCoordinates : outNeg (P t u - T u + W u) =
      -outNeg (T u - ((∑ k, ∑ j, raw t k j u) + W u)) :=
    (congrArg outNeg hopposite).trans (map_neg outNeg _)
  have hnegativeNorm : ‖outNeg (P t u - T u + W u)‖ =
      ‖outNeg (T u - ((∑ k, ∑ j, raw t k j u) + W u))‖ :=
    (congrArg (fun y : Yneg ↦ ‖y‖) hnegativeCoordinates).trans (norm_neg _)
  exact ⟨hpositive, hnegativeNorm.le.trans (hnegative t u)⟩

end AtiyahSinger

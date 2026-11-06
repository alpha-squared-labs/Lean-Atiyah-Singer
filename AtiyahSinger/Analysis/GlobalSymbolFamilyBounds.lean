/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbolTopology

/-!
# Closed seminorm sublevels from the original symbol jets

Public module ID: M0680.

Pointwise continuity of the measured mixed derivatives makes sublevels of an
actual global symbol seminorm closed. No continuity in the stronger symbol
seminorm topology is assumed. This is the closed-set input for compact-group
lower-order cocycles, including zero-rank fibers and empty compact test sets.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

attribute [local instance] GlobalSymbolSeminormIndex.input_mem_atlas
  GlobalSymbolSeminormIndex.output_mem_atlas

/-- Continuous measured jets give closed sublevels of the original global symbol seminorm. -/
theorem isClosed_le_globalSymbolSeminorm_of_continuous_jets
    {Y : Type*} [TopologicalSpace Y] (m : ℝ)
    (a : Y → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (J : GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F)
    (hjet : ∀ x ∈ J.localIndex.compactSet, ∀ ξ,
      Continuous (fun y : Y ↦ symbolDerivative
        (globalSymbolInChart E F (a y).val J.chart J.inputFrame J.outputFrame)
        J.localIndex.spatialOrder J.localIndex.frequencyOrder x ξ)) (C : ℝ) :
    IsClosed {y : Y | globalSymbolSeminorm E F m J (a y) ≤ C} := by
  let := J.input_mem_atlas
  let := J.output_mem_atlas
  let I := J.localIndex
  let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  let hU := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
  let b (y : Y) := globalSymbolInChartLinearMap E F m J (a y)
  let D (y : Y) (x ξ : EuclideanSpace ℝ (Fin n)) :=
    symbolDerivative (b y).val I.spatialOrder I.frequencyOrder x ξ
  let w (ξ : EuclideanSpace ℝ (Fin n)) := (1 + ‖ξ‖) ^ (m - (I.frequencyOrder : ℝ))
  have hw (ξ : EuclideanSpace ℝ (Fin n)) : 0 < w ξ :=
    Real.rpow_pos_of_pos (by positivity) _
  -- The exact supremum is bounded precisely when each measured derivative is bounded.
  have hiff (y : Y) : globalSymbolSeminorm E F m J (a y) ≤ C ↔
      0 ≤ C ∧ ∀ x ∈ I.compactSet, ∀ ξ, ‖D y x ξ‖ ≤ C * w ξ := by
    constructor
    · intro h
      refine ⟨(apply_nonneg (globalSymbolSeminorm E F m J) (a y)).trans h, ?_⟩
      intro x hx ξ
      exact (symbolDerivative_norm_le_seminorm hU m I (b y) x hx ξ).trans
        (mul_le_mul_of_nonneg_right h (hw ξ).le)
    · rintro ⟨hC, hbound⟩
      change symbolSeminormValue hU m I (b y) ≤ C
      unfold symbolSeminormValue
      by_cases hK : I.compactSet.Nonempty
      · obtain ⟨x, hx⟩ := hK
        refine csSup_le ⟨‖D y x 0‖ / w 0, x, hx, 0, rfl⟩ ?_
        rintro t ⟨z, hz, ξ, rfl⟩
        exact (div_le_iff₀ (hw ξ)).mpr (hbound z hz ξ)
      · rw [Set.not_nonempty_iff_eq_empty] at hK
        simpa only [hK, Set.mem_empty_iff_false, false_and, exists_false,
          ofPred_false, Real.sSup_empty] using hC
  have hset : {y : Y | globalSymbolSeminorm E F m J (a y) ≤ C} =
      {y : Y | 0 ≤ C} ∩ ⋂ x : I.compactSet, ⋂ ξ : EuclideanSpace ℝ (Fin n),
        {y : Y | ‖D y x.val ξ‖ ≤ C * w ξ} := by
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, hiff]
    constructor
    · rintro ⟨hC, h⟩
      exact ⟨hC, fun x ξ ↦ h x.val x.property ξ⟩
    · rintro ⟨hC, h⟩
      exact ⟨hC, fun x hx ξ ↦ h ⟨x, hx⟩ ξ⟩
  -- Every derivative evaluation is continuous; arbitrary intersections preserve closedness.
  rw [hset]
  apply (isClosed_le continuous_const continuous_const).inter
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro ξ
  exact isClosed_le (hjet x.val x.property ξ).norm continuous_const

end AtiyahSinger

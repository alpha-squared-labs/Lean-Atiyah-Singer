/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateOperator
public import AtiyahSinger.Analysis.NoncompactSymbolIntegral

/-!
# Integrating the original coordinate differential expression

Public module ID: M0406.

Local integrable bounds on the actual spatial jets permit the given coordinate
differential operator to pass through an arbitrary parameter integral. The original
coefficients, ordered coordinate directions, and powers of `-I` are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open Filter MeasureTheory Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 25

/-- Locally dominated jets make the actual differential expression integrable and allow
the same expression to commute with the parameter integral. -/
theorem integrable_apply_and_apply_integral
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) {n r q d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n r q d U)
    (f : Y → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (hf : ∀ y, ContDiffOn ℝ ∞ (f y) U)
    (hmeas : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)), x ∈ U →
      AEStronglyMeasurable (fun y ↦ iteratedFDeriv ℝ k (f y) x) μ)
    (hdom : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)), x ∈ U →
      ∃ t : Set (EuclideanSpace ℝ (Fin n)), t ∈ 𝓝 x ∧ t ⊆ U ∧
        ∃ B : Y → ℝ, Integrable B μ ∧
          ∀ᵐ y ∂μ, ∀ z ∈ t, ‖iteratedFDeriv ℝ k (f y) z‖ ≤ B y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    Integrable (fun y ↦ P.apply (f y) x) μ ∧
      P.apply (fun z ↦ ∫ y, f y z ∂μ) x = ∫ y, P.apply (f y) x ∂μ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  -- Each actual jet is integrable at the point inside its common domination neighborhood.
  have hint (k : ℕ) : Integrable (fun y ↦ iteratedFDeriv ℝ k (f y) x) μ := by
    obtain ⟨t, ht, _, B, hB, hbound⟩ := hdom k x hx
    apply hB.mono' (hmeas k x hx)
    filter_upwards [hbound] with y hy
    exact hy x (mem_of_mem_nhds ht)
  -- Each original summand is a fixed continuous linear map of its specified spatial jet.
  let T (k : Fin (d + 1)) (α : Fin k.val → Fin n) : (X [×k.val]→L[ℝ] V) →L[ℝ] W :=
    (P.coefficient k α x).restrictScalars ℝ |>.comp
      (((-Complex.I) ^ k.val) • ContinuousMultilinearMap.apply ℝ (fun _ : Fin k.val ↦ X) V
        (fun j ↦ EuclideanSpace.single (α j) 1))
  let term (k : Fin (d + 1)) (α : Fin k.val → Fin n) (y : Y) : W :=
    T k α (iteratedFDeriv ℝ k.val (f y) x)
  have hterm (k : Fin (d + 1)) (α : Fin k.val → Fin n) : Integrable (term k α) μ :=
    (T k α).integrable_comp (hint k.val)
  have htermIntegral (k : Fin (d + 1)) (α : Fin k.val → Fin n) :
      (∫ y, term k α y ∂μ) =
        T k α (iteratedFDeriv ℝ k.val (fun z ↦ ∫ y, f y z ∂μ) x) := by
    rw [iteratedFDeriv_integral_of_locally_dominated_jets μ hU hf hmeas hdom k.val hx]
    exact (T k α).integral_comp_comm (hint k.val)
  -- Commute only finite sums; all coefficient maps and normalization factors stay fixed.
  refine ⟨integrable_finsetSum _ (fun k _ ↦
    integrable_finsetSum _ (fun α _ ↦ hterm k α)), ?_⟩
  symm
  change (∫ y, ∑ k : Fin (d + 1), ∑ α : Fin k.val → Fin n, term k α y ∂μ) = _
  calc
    _ = ∑ k : Fin (d + 1), ∫ y, ∑ α : Fin k.val → Fin n, term k α y ∂μ :=
      integral_finsetSum _ (fun k _ ↦ integrable_finsetSum _ (fun α _ ↦ hterm k α))
    _ = ∑ k : Fin (d + 1), ∑ α : Fin k.val → Fin n, ∫ y, term k α y ∂μ := by
      apply Finset.sum_congr rfl
      intro k _
      exact integral_finsetSum _ (fun α _ ↦ hterm k α)
    _ = P.apply (fun z ↦ ∫ y, f y z ∂μ) x := by
      simp_rw [htermIntegral]
      rfl

end AtiyahSinger.CoordinateDifferentialOperator

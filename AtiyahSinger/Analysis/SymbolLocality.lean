/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Symbol

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Locality of the symbol estimates

Public module ID: M1026.

The usual fixed-order symbol condition can be verified on open neighborhoods.
Smoothness is local, and a compact coordinate set admits a finite cover by smaller
compact neighborhoods. Summing their constants gives every required global-on-compact
mixed derivative bound for the same original function and order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff

set_option maxSynthPendingDepth 15

/-- A symbol of one fixed order on neighborhoods is a symbol on their open domain. -/
theorem IsSymbol.of_locally {n r q : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) {m : ℝ}
    {p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))}
    (hlocal : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsSymbol V m p) : IsSymbol U m p := by
  classical
  choose V hV hxV hVU hpV using fun x : U ↦ hlocal x.val x.property
  refine ⟨?_, ?_⟩
  · -- A local smooth representative is smooth at the original point and frequency.
    intro z hz
    have hnhds : (V ⟨z.1, hz.1⟩ ∩ U) ×ˢ Set.univ ∈ nhds z :=
      (((hV ⟨z.1, hz.1⟩).inter hU).prod isOpen_univ).mem_nhds
        ⟨⟨hxV ⟨z.1, hz.1⟩, hz.1⟩, Set.mem_univ z.2⟩
    exact (((hpV ⟨z.1, hz.1⟩).1.mono
      (Set.prod_mono Set.inter_subset_left subset_rfl)).contDiffAt hnhds).contDiffWithinAt
  · intro K hKU hK i j
    -- Shrinking first makes each local estimate available on a compact neighborhood.
    choose L hL hxL hLV using fun x : U ↦ exists_compact_subset (hV x) (hxV x)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : U ↦ interior (L x))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hxL ⟨x, hKU hx⟩⟩)
    choose C hC hbound using fun x : U ↦ (hpV x).2 (L x) (hLV x) (hL x) i j
    refine ⟨∑ x ∈ t, C x, Finset.sum_nonneg (fun x _ ↦ hC x), ?_⟩
    intro x hx ξ
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    -- The finite sum dominates every chosen constant, with the same frequency weight.
    apply (hbound y x (interior_subset hxy) ξ).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun y _ ↦ hC y) hyt

end AtiyahSinger

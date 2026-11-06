/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolLocality
public import AtiyahSinger.Analysis.SymbolQuotient

/-!
# Smoothing symbols with locally bounded frequency support

Public module ID: M0793.

A smooth symbol function has every order when its frequency support is bounded
uniformly over each compact subset of the open base. The bound may depend on
that compact set; a single radius on the entire base is not required.

The proof applies the existing bounded-support criterion on compact neighborhoods,
then uses locality of the original symbol estimates. This is the local symbol
criterion needed for cutoff inverses supplied by a compact exhaustion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff

/-- Smoothness and frequency support bounded on each compact base set imply smoothing. -/
theorem isSmoothingSymbol_of_locally_bounded_frequency_support {n r q : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (a : SymbolFunction n r q)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ))
    (hsupp : ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K →
      ∃ R : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → a x ξ = 0) : IsSmoothingSymbol U a := by
  intro m
  apply IsSymbol.of_locally hU
  intro x hx
  -- A compact neighborhood supplies one radius on an open neighborhood of this point.
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨R, hR⟩ := hsupp K hKU hK
  have hVU : interior K ⊆ U := interior_subset.trans hKU
  refine ⟨interior K, isOpen_interior, hxK, hVU, ?_⟩
  -- The established criterion controls all derivatives on that same neighborhood.
  exact isSmoothingSymbol_of_frequency_support isOpen_interior a R
    (hsmooth.mono (prod_mono hVU subset_rfl))
    (fun y hy ξ hξ ↦ hR y (interior_subset hy) ξ hξ) m

end AtiyahSinger

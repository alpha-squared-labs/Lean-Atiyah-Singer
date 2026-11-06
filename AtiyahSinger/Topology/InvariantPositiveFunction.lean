/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Positive invariant minorants under compact group actions

Public module ID: M1910.

The minimum of a positive continuous function along each compact group orbit
is positive, continuous, invariant, and bounded by the original function.
Continuity follows from the compact-parameter minimum theorem, so the base
needs no compactness, separation, metrizability, or countability assumption.

This elementary orbit-minimum construction supplies invariant local time
steps for equivariant bundle homotopies over noncompact bases.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set

/-- A positive continuous function has a positive continuous invariant minorant
for a continuous action of a compact group. -/
theorem exists_positive_invariant_le
    {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (δ : C(X, ℝ)) (hδ : ∀ x, 0 < δ x) :
    ∃ ε : C(X, ℝ), (∀ x, 0 < ε x) ∧ (∀ x, ε x ≤ δ x) ∧
      ∀ (g : G) (x : X), ε (g • x) = ε x := by
  -- Joint continuity and the compact group parameter make the orbit minimum continuous.
  let ε : C(X, ℝ) :=
    ⟨fun x ↦ sInf ((fun g : G ↦ δ (g • x)) '' univ),
      isCompact_univ.continuous_sInf
        (δ.continuous.comp (continuous_snd.smul continuous_fst))⟩
  have hmin (x : X) :
      ∃ g : G, ε x = δ (g • x) ∧ ∀ h : G, ε x ≤ δ (h • x) := by
    obtain ⟨g, _, hg, hle⟩ := isCompact_univ.exists_sInf_image_eq_and_le
      (univ_nonempty : (univ : Set G).Nonempty)
      (δ.continuous.comp (continuous_id.smul continuous_const)).continuousOn
    exact ⟨g, hg, fun h ↦ hg.trans_le (hle h (mem_univ h))⟩
  refine ⟨ε, ?_, ?_, ?_⟩
  · -- The minimum is attained, so pointwise strict positivity is sufficient.
    intro x
    obtain ⟨g, hg, _⟩ := hmin x
    rw [hg]
    exact hδ (g • x)
  · intro x
    obtain ⟨_, _, hle⟩ := hmin x
    simpa only [one_smul] using hle 1
  · -- Translation permutes the very same compact orbit; compare its two attained minima.
    intro g x
    obtain ⟨a, ha, hale⟩ := hmin (g • x)
    obtain ⟨b, hb, hble⟩ := hmin x
    apply le_antisymm
    · calc
        ε (g • x) ≤ δ ((b * g⁻¹) • (g • x)) := hale (b * g⁻¹)
        _ = δ (b • x) := by rw [mul_smul, inv_smul_smul]
        _ = ε x := hb.symm
    · calc
        ε x ≤ δ ((a * g) • x) := hble (a * g)
        _ = δ (a • (g • x)) := by rw [mul_smul]
        _ = ε (g • x) := ha.symm

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization

/-!
# Sobolev reconstruction from a partition on the section support

Public module ID: M0309.

A finite collection of compact cutoffs in compatible charts need only sum to
one on the support of the section being reconstructed. Plateaus in the same
charts and bundle frames extend its actual localized coordinates back to the
original section. The original finite-atlas Sobolev norm is therefore bounded
by the sum of the given localized Sobolev norms at every real order.

This is the supported version of invariance under a finite smooth partition;
it also applies when the compatible charts do not cover the entire manifold.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {A : SmoothComplexBundleAtlas (n := n) E}

set_option maxSynthPendingDepth 20 in
set_option maxHeartbeats 600000 in

open Classical in
/-- A partition on the actual section support gives a uniform reverse localization bound. -/
theorem exists_sobolev_bound_of_supported_partition
    {ι : Type*} [Fintype ι]
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : ∀ j, c j ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (D : ∀ j, AtlasChartCutoff A (c j)) (L : AtlasBundlePresentation A) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : A.smoothSections)
      (v : ∀ j, 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (D j).frameIndex)))),
      (∀ j z, v j z = (D j).localizedFunction u z) →
      (∀ x, u.val x ≠ 0 →
        (∑ j, if x ∈ (c j).source then (D j).cutoff (c j x) else 0) = 1) →
      ‖L.smoothToSobolev s u‖ ≤ C * ∑ j, ‖schwartzSobolevCoordinate s (v j)‖ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  -- Each original coordinate support has a plateau inside its same chart and frame.
  have hplateau (j : ι) : ∃ ρ : X → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ (c j).target ∩ (c j).symm ⁻¹' (A.chart (D j).frameIndex).baseSet ∧
      ∀ z ∈ tsupport (D j).cutoff, ρ z = 1 := by
    let U := (c j).target ∩ (c j).symm ⁻¹' (A.chart (D j).frameIndex).baseSet
    have hU : IsOpen U := (c j).continuousOn_symm.isOpen_inter_preimage
      (c j).open_target (A.chart (D j).frameIndex).open_baseSet
    obtain ⟨O, _, hKO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure (D j).compact_support hU (D j).support_subset
    obtain ⟨O', hO'o, hOO', hO'U, hO'c⟩ :=
      exists_open_between_and_isCompact_closure hOc hU hOU
    obtain ⟨ρ, hρ, _, hsρ, hρone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
    have hs : tsupport ρ = closure O' := congrArg closure hsρ
    refine ⟨ρ, hρ, ?_, ?_, ?_⟩
    · simpa only [HasCompactSupport, hs] using hO'c
    · rwa [hs]
    · intro z hz
      exact (hρone z).mp (subset_closure (hKO hz))
  choose ρ hρ hcρ hsρ hρone using hplateau
  let D' (j : ι) : AtlasChartCutoff A (c j) := {
    D j with
    cutoff := ρ j
    smooth_cutoff := hρ j
    compact_support := hcρ j
    support_subset := hsρ j }
  have hextend (j : ι) :=
    AtlasChartCutoff.exists_extend_sobolev_of_mem_maximalAtlas (D' j) (hc j) L s
  choose O hO C hC hb using hextend
  let Csum : ℝ := ∑ j, C j
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg fun j _ ↦ hC j
  refine ⟨Csum, hCsum, ?_⟩
  intro u v hv hpartition
  -- The plateau contributes one wherever the original localization can be nonzero.
  have hreturn (j : ι) (x : M) :
      (O j (v j)).val x =
        ((if x ∈ (c j).source then (D j).cutoff (c j x) else 0 : ℝ) : ℂ) • u.val x := by
    rw [hO]
    by_cases hx : x ∈ (c j).source ∩ (A.chart (D j).frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, D', dite_eq_left hx, ite_eq_left hx.1]
      rw [hv, AtlasChartCutoff.localizedFunction, ite_eq_left ((c j).map_source hx.1)]
      by_cases hz : (D j).cutoff (c j x) = 0
      · simp only [hz, Complex.ofReal_zero, zero_smul, map_zero, smul_zero]
      · rw [hρone j _ (subset_tsupport _ hz), Complex.ofReal_one, one_smul, map_smul,
          atlasSectionInChart, (c j).left_inv hx.1, ContinuousLinearEquiv.apply_symm_apply]
        change (A.frameLinearEquiv (D j).frameIndex x hx.2).symm
          (((D j).cutoff (c j x) : ℂ) •
            (A.frameLinearEquiv (D j).frameIndex x hx.2) (u.val x)) = _
        rw [map_smul, LinearEquiv.symm_apply_apply]
    · have hz : (if x ∈ (c j).source then (D j).cutoff (c j x) else 0 : ℝ) = 0 := by
        by_cases hxc : x ∈ (c j).source
        · rw [ite_eq_left hxc]
          by_contra h
          have hf := ((D j).support_subset (subset_tsupport _ h)).2
          change (c j).symm (c j x) ∈ (A.chart (D j).frameIndex).baseSet at hf
          exact hx ⟨hxc, by simpa only [(c j).left_inv hxc] using hf⟩
        · exact ite_eq_right hxc
      simp only [AtlasChartCutoff.extendedFunction, D', dite_eq_right hx, hz,
        Complex.ofReal_zero, zero_smul]
  have hreconstruct : (∑ j, O j (v j)) = u := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply, hreturn]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum]
    by_cases hx : u.val x = 0
    · simp only [hx, smul_zero]
    · rw [hpartition x hx, Complex.ofReal_one, one_smul]
  -- The finite extension bounds are measured in the specified original Sobolev completion.
  calc
    ‖L.smoothToSobolev s u‖ = ‖L.smoothToSobolev s (∑ j, O j (v j))‖ := by
      rw [hreconstruct]
    _ = ‖∑ j, L.smoothToSobolev s (O j (v j))‖ := by rw [map_sum]
    _ ≤ ∑ j, ‖L.smoothToSobolev s (O j (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ j, C j * ‖schwartzSobolevCoordinate s (v j)‖ :=
      Finset.sum_le_sum fun j _ ↦ hb j (v j)
    _ ≤ ∑ j, Csum * ‖schwartzSobolevCoordinate s (v j)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ ↦ hC k) hj)
        (norm_nonneg (schwartzSobolevCoordinate s (v j)))
    _ = Csum * ∑ j, ‖schwartzSobolevCoordinate s (v j)‖ := (Finset.mul_sum _ _ _).symm

end AtiyahSinger

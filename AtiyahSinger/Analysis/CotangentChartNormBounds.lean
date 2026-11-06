/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereRegularity
public import AtiyahSinger.Analysis.GlobalQuantization

/-!
# Uniform cotangent norm comparison in a fixed finite atlas

Public module ID: M0422.

Metric covector length and coordinate frequency norm are uniformly equivalent
on compact chart windows. A single constant works on every active patch of a
fixed quantization presentation. No sign condition on its partition weights is
needed, and zero-dimensional fibers and empty presentations are included.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Positive coordinate norm equivalence is uniform on a compact chart window. -/
theorem SmoothCotangentMetric.exists_length_bounds_on
    (g : SmoothCotangentMetric (n := n) (M := M))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKc : K ⊆ c.target) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ z ∈ K, ∀ η : EuclideanSpace ℝ (Fin n),
      b * ‖η‖ ≤ g.length (c.symm z) (covectorFromChart c (c.symm z) η) ∧
        g.length (c.symm z) (covectorFromChart c (c.symm z) η) ≤ B * ‖η‖ := by
  let L (z η : EuclideanSpace ℝ (Fin n)) :=
    g.length (c.symm z) (covectorFromChart c (c.symm z) η)
  have hcov_smul (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      covectorFromChart c (c.symm z) (t • η) = t • covectorFromChart c (c.symm z) η := by
    ext v
    change inner ℝ (t • η) (mfderiv _ _ c (c.symm z) v) = _
    exact real_inner_smul_left η _ t
  have hcov_ne (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) :
      covectorFromChart c (c.symm z) η ≠ 0 := by
    intro hzero
    have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
    rw [hzero] at h
    have hzero' : covectorInChart c (c.symm z) 0 = 0 := by ext k; rfl
    exact hη (h.symm.trans hzero')
  have hL_smul (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      L z (t • η) = |t| * L z η := by
    dsimp only [L]
    rw [hcov_smul, g.length_smul]
  have hL_zero (z : EuclideanSpace ℝ (Fin n)) : L z 0 = 0 := by
    dsimp only [L]
    have hz : covectorFromChart c (c.symm z) 0 = 0 := by
      ext v
      change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (mfderiv _ _ c (c.symm z) v) = 0
      exact inner_zero_left _
    rw [hz]
    exact (g.length_eq_zero_iff _ _).mpr rfl
  -- Compactness on the coordinate unit sphere gives uniform positive bounds.
  let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hne (η : EuclideanSpace ℝ (Fin n))
      (hη : η ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : η ≠ 0 := by
    intro hz
    simp [hz] at hη
  have hcont : ContinuousOn (Function.uncurry L) S :=
    (g.contDiffOn_length_covectorFromChart c hc).continuousOn.mono
      (fun z hz ↦ ⟨hKc hz.1, hne z.2 hz.2⟩)
  obtain ⟨b, hb, hlow⟩ := hS.exists_forall_le' hcont (a := 0) (by
    intro z hz
    exact g.length_pos _ _ (hcov_ne z.1 (hKc hz.1) z.2 (hne z.2 hz.2)))
  obtain ⟨B, hupper⟩ := (hS.image_of_continuousOn hcont).bddAbove
  refine ⟨b, max B 1, hb, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz η
  change b * ‖η‖ ≤ L z η ∧ L z η ≤ max B 1 * ‖η‖
  -- Positive homogeneity extends the sphere bounds to every frequency.
  by_cases hη : η = 0
  · subst η
    simp only [norm_zero, mul_zero, hL_zero, le_refl, and_self]
  let v := ‖η‖⁻¹ • η
  have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hη
  have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hη]
  have hlen : L z η = ‖η‖ * L z v := by
    conv_lhs => rw [← hscale, hL_smul]
    rw [abs_of_nonneg (norm_nonneg η)]
  rw [hlen]
  constructor
  · simpa only [Function.uncurry, mul_comm] using
      mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hz, hv⟩) (norm_nonneg η)
  · have hbound := (hupper ⟨(z, v), ⟨hz, hv⟩, rfl⟩).trans (le_max_left B 1)
    simpa only [Function.uncurry, mul_comm] using
      mul_le_mul_of_nonneg_left hbound (norm_nonneg η)

variable {r q : ℕ} {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedAddCommGroup (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]

/-- One norm comparison constant works on every nonzero weight of a finite presentation. -/
theorem QuantizationPresentation.exists_covectorInChart_norm_bounds
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i : Fin A.size, ∀ x : M, (A.patch i).weight x ≠ 0 →
      ∀ ξ : CotangentFiber (n := n) x,
        g.length x ξ ≤ C * ‖covectorInChart (A.patch i).chart x ξ‖ ∧
          ‖covectorInChart (A.patch i).chart x ξ‖ ≤ C * g.length x ξ := by
  classical
  choose b B hb hB hbound using fun i : Fin A.size ↦
    g.exists_length_bounds_on (A.patch i).chart (A.patch i).chart_mem_atlas
      (tsupport (A.patch i).input.cutoff) (A.patch i).input.compact_support
      (fun _ hz ↦ ((A.patch i).input.support_subset hz).1)
  let D (i : Fin A.size) : ℝ := B i + (b i)⁻¹
  let C : ℝ := 1 + ∑ i, D i
  have hD (i : Fin A.size) : 0 ≤ D i := add_nonneg (hB i).le (inv_pos.mpr (hb i)).le
  have hC : 1 ≤ C := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hD i))
  have hDC (i : Fin A.size) : D i ≤ C := by
    have hsum : D i ≤ ∑ j, D j := Finset.single_le_sum (fun j _ ↦ hD j) (Finset.mem_univ i)
    exact hsum.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro i x hw ξ
  let Q := A.patch i
  have hx : x ∈ Q.chart.source := by
    by_contra h
    exact hw (by simp [QuantizationPatch.weight, Q, h])
  have hz : Q.chart x ∈ tsupport Q.input.cutoff := by
    apply subset_tsupport
    intro h
    exact hw (by simp [QuantizationPatch.weight, Q, hx, h])
  have h := hbound i (Q.chart x) hz (covectorInChart Q.chart x ξ)
  rw [Q.chart.left_inv hx, covectorFromChart_covectorInChart Q.chart Q.chart_mem_atlas x hx ξ]
    at h
  have hBC : B i ≤ C := (le_add_of_nonneg_right (inv_pos.mpr (hb i)).le).trans (hDC i)
  have hbC : (b i)⁻¹ ≤ C := (le_add_of_nonneg_left (hB i).le).trans (hDC i)
  constructor
  · exact h.2.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _))
  · calc
      ‖covectorInChart Q.chart x ξ‖ = (b i)⁻¹ * (b i * ‖covectorInChart Q.chart x ξ‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (hb i).ne', one_mul]
      _ ≤ (b i)⁻¹ * g.length x ξ := mul_le_mul_of_nonneg_left h.1 (inv_pos.mpr (hb i)).le
      _ ≤ C * g.length x ξ := mul_le_mul_of_nonneg_right hbC (g.length_nonneg x ξ)

end AtiyahSinger

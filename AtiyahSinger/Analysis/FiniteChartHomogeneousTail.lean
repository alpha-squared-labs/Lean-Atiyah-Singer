/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentChartNormBounds

/-!
# Homogeneous tails of a finite supported chart assembly

Public module ID: M0622.

A finite family of fields supported in compact chart windows has a common
homogeneous tail for any specified smooth cotangent metric. Each chart keeps
its original covectors and its own local tail radius. Compact norm comparison
converts a large metric length into a large frequency in every active chart.

This applies to the actual associated-sphere cutoff pieces after their frame
and tensor transports. It requires neither a global product chart nor a
replacement full symbol, and includes empty families and zero covectors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold Set
open scoped Manifold ContDiff

variable {n : ℕ} {ι M : Type*} [Fintype ι] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]

/-- Compact chart tails combine into one metric tail for the original finite sum. -/
theorem exists_sum_homogeneous_of_compact_chart_tails
    (g : SmoothCotangentMetric (n := n) (M := M))
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : ∀ i, c i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (K : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ i, IsCompact (K i)) (hKc : ∀ i, K i ⊆ (c i).target)
    (a : ι → ∀ x : M, CotangentFiber (n := n) x → W x)
    (hzero : ∀ i x, x ∉ (c i).symm '' K i → ∀ ξ, a i x ξ = 0)
    (R₀ : ι → ℝ)
    (hscale : ∀ i x, x ∈ (c i).symm '' K i →
      ∀ (η : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
        R₀ i ≤ ‖η‖ → R₀ i ≤ ‖t • η‖ →
          a i x (covectorFromChart (c i) x (t • η)) =
            (t : ℂ) • a i x (covectorFromChart (c i) x η)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ξ (t : ℝ), 0 < t →
      R ≤ g.length x ξ → R ≤ g.length x (t • ξ) →
        (∑ i, a i x (t • ξ)) = (t : ℂ) • ∑ i, a i x ξ := by
  classical
  -- Use the upper metric bound in each original compact window, then take a finite bound.
  let X := EuclideanSpace ℝ (Fin n)
  let inverse (i : ι) (p : X × X) : CotangentTotalSpace (n := n) (M := M) :=
    ⟨(c i).symm p.1, covectorFromChart (c i) ((c i).symm p.1) p.2⟩
  have hcontinuous (i : ι) : ContinuousOn (inverse i) ((c i).target ×ˢ univ) := by
    intro p hp
    have hbase : ContMDiffAt 𝓘(ℝ, X × X) 𝓘(ℝ, X) ∞
        (fun p ↦ (c i).symm p.1) p :=
      (contMDiffAt_symm_of_mem_maximalAtlas (hc i) hp.1).comp p
        contDiffAt_fst.contMDiffAt
    have hd := ((contMDiffAt_of_mem_maximalAtlas (hc i)
      ((c i).map_target hp.1)).mfderiv_const
        (m := (∞ : WithTop ℕ∞)) (by simp)).comp p hbase
    have hinner : ContMDiffAt 𝓘(ℝ, X × X) 𝓘(ℝ, CotangentModel n) ∞
        (fun p ↦ innerSL ℝ p.2) p :=
      (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp p contDiffAt_snd.contMDiffAt
    have hmap : ContMDiffAt 𝓘(ℝ, X × X)
        (𝓘(ℝ, X).prod 𝓘(ℝ, CotangentModel n)) ∞ (inverse i) p := by
      apply (contMDiffAt_hom_bundle _).mpr
      refine ⟨hbase, ?_⟩
      apply (hinner.clm_comp hd).congr_of_eventuallyEq
      filter_upwards with z
      ext v
      simp [inverse, covectorFromChart, inTangentCoordinates,
        ContinuousLinearMap.inCoordinates, Function.id_def, ContinuousLinearMap.comp_apply]
      rfl
    exact hmap.continuousAt.continuousWithinAt
  have hexists (i : ι) : ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K i, ∀ η : X,
      g.length ((c i).symm z) (covectorFromChart (c i) ((c i).symm z) η) ≤ B * ‖η‖ := by
    let L (z η : X) := g.length ((c i).symm z)
      (covectorFromChart (c i) ((c i).symm z) η)
    have hL_smul (z η : X) (t : ℝ) : L z (t • η) = |t| * L z η := by
      have hcov : covectorFromChart (c i) ((c i).symm z) (t • η) =
          t • covectorFromChart (c i) ((c i).symm z) η := by
        ext v
        exact real_inner_smul_left η _ t
      dsimp only [L]
      rw [hcov, g.length_smul]
    have hL_zero (z : X) : L z 0 = 0 := by
      have h := hL_smul z (0 : X) 0
      simpa only [zero_smul, abs_zero, zero_mul] using h
    let U := K i ×ˢ Metric.sphere (0 : X) 1
    have hU : IsCompact U := (hK i).prod (isCompact_sphere _ _)
    have hcont : ContinuousOn (Function.uncurry L) U :=
      g.continuous_length.comp_continuousOn ((hcontinuous i).mono
        (fun _ hp ↦ ⟨hKc i hp.1, mem_univ _⟩))
    obtain ⟨B, hB⟩ := (hU.image_of_continuousOn hcont).bddAbove
    refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    intro z hz η
    change L z η ≤ max B 1 * ‖η‖
    by_cases hη : η = 0
    · simp only [hη, hL_zero, norm_zero, mul_zero, le_refl]
    let v := ‖η‖⁻¹ • η
    have hv : v ∈ Metric.sphere (0 : X) 1 := by
      simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hη
    have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hη]
    have hlen : L z η = ‖η‖ * L z v := by
      conv_lhs => rw [← hscale, hL_smul]
      rw [abs_of_nonneg (norm_nonneg η)]
    rw [hlen]
    have hbound := (hB ⟨(z, v), ⟨hz, hv⟩, rfl⟩).trans (le_max_left B 1)
    simpa only [Function.uncurry, mul_comm] using
      mul_le_mul_of_nonneg_left hbound (norm_nonneg η)
  choose B hB hbound using hexists
  have hback (i : ι) (x : M) (hx : x ∈ (c i).source)
      (ξ : CotangentFiber (n := n) x) :
      covectorFromChart (c i) x (covectorInChart (c i) x ξ) = ξ := by
    have hcoord : innerSL ℝ (covectorInChart (c i) x ξ) =
        ξ.comp (mfderiv 𝓘(ℝ, X) 𝓘(ℝ, X) (c i).symm (c i x)) := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro j
      simp [covectorInChart, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right]
      rfl
    have hdiff : (c i).MDifferentiable 𝓘(ℝ, X) 𝓘(ℝ, X) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas (hc i)).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas (hc i)).mdifferentiableOn (by simp)⟩
    ext v
    have h := congrArg (fun T : TangentSpace 𝓘(ℝ, X) x →L[ℝ]
      TangentSpace 𝓘(ℝ, X) x ↦ T v) (hdiff.symm_comp_deriv hx)
    change (mfderiv _ _ (c i).symm (c i x)) ((mfderiv _ _ (c i) x) v) = v at h
    calc
      covectorFromChart (c i) x (covectorInChart (c i) x ξ) v =
          ξ ((mfderiv _ _ (c i).symm (c i x)) ((mfderiv _ _ (c i) x) v)) :=
        DFunLike.congr_fun hcoord ((mfderiv _ _ (c i) x) v)
      _ = ξ v := congrArg ξ h
  let D (i : ι) := B i * max (R₀ i) 0
  let R := 1 + ∑ i, D i
  have hD (i : ι) : 0 ≤ D i := mul_nonneg (hB i).le (le_max_right _ _)
  have hR : 0 < R :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ ↦ hD i))
  have hDR (i : ι) : D i ≤ R :=
    (Finset.single_le_sum (fun j _ ↦ hD j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨R, hR, ?_⟩
  intro x ξ t ht hξ htξ
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hxK : x ∈ (c i).symm '' K i
  · obtain ⟨z, hz, hzx⟩ := hxK
    have hx : x ∈ (c i).source := hzx ▸ (c i).map_target (hKc i hz)
    have hcx : (c i) x ∈ K i := by
      rw [← hzx, (c i).right_inv (hKc i hz)]
      exact hz
    -- Recover the same native covector before applying the chart tail identity.
    have hlarge (ν : CotangentFiber (n := n) x) (hν : R ≤ g.length x ν) :
        R₀ i ≤ ‖covectorInChart (c i) x ν‖ := by
      have h := hbound i ((c i) x) hcx (covectorInChart (c i) x ν)
      rw [(c i).left_inv hx, hback i x hx ν] at h
      have hmul : B i * max (R₀ i) 0 ≤ B i * ‖covectorInChart (c i) x ν‖ :=
        (hDR i).trans (hν.trans h)
      exact (le_max_left _ _).trans (le_of_mul_le_mul_left hmul (hB i))
    have hcoord : covectorInChart (c i) x (t • ξ) =
        t • covectorInChart (c i) x ξ := by
      ext j
      rfl
    have hcov : covectorFromChart (c i) x (t • covectorInChart (c i) x ξ) = t • ξ := by
      rw [← hcoord, hback i x hx (t • ξ)]
    have h := hscale i x ⟨z, hz, hzx⟩ (covectorInChart (c i) x ξ) t ht
      (hlarge ξ hξ) (hcoord ▸ hlarge (t • ξ) htξ)
    rwa [hcov, hback i x hx ξ] at h
  · rw [hzero i x hxK (t • ξ), hzero i x hxK ξ, smul_zero]

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereRegularity
public import AtiyahSinger.Topology.BundleIsoAffineHomotopy

/-!
# A metric exterior detected by a finite cotangent chart cover

Public module ID: M0623.

A finite compact chart cover with specified coordinate radii detects every
sufficiently long covector for any fixed smooth cotangent metric. The proof
bounds the metric on the compact images of the original closed coordinate
balls, and recovers each actual covector using that same chart inverse.

This geometric localization criterion supplies a common metric radius for
uniform symbol estimates and supported homotopies. The charts may belong to
the maximal atlas; no change of the original charted space is made.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold Set
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {ι : Type*} [Finite ι]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Cot" => CotangentTotalSpace (n := n) (M := M)

/-- A long metric covector is beyond the prescribed radius in one original covering chart. -/
theorem exists_metric_radius_of_cotangent_chart_cover
    (g : SmoothCotangentMetric (n := n) (M := M))
    (c : ι → OpenPartialHomeomorph M X)
    (hc : ∀ i, c i ∈ maximalAtlas 𝓘(ℝ, X) ∞ M)
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hKc : ∀ i, K i ⊆ (c i).target)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source ∧ c i x ∈ K i)
    (R : ι → ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x (ξ : CotangentFiber (n := n) x), L ≤ g.length x ξ →
      ∃ i, x ∈ (c i).source ∧ c i x ∈ K i ∧
        R i ≤ ‖covectorInChart (c i) x ξ‖ := by
  classical
  let inverse (i : ι) (p : X × X) : Cot :=
    ⟨(c i).symm p.1, covectorFromChart (c i) ((c i).symm p.1) p.2⟩
  -- The actual inverse cotangent chart is continuous even at the zero covector.
  have hcontinuous (i : ι) : ContinuousOn (inverse i) ((c i).target ×ˢ Set.univ) := by
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
  let bad (i : ι) : Set Cot := inverse i '' (K i ×ˢ Metric.closedBall (0 : X) (R i))
  have hbad (i : ι) : IsCompact (bad i) :=
    ((hK i).prod (isCompact_closedBall (0 : X) (R i))).image_of_continuousOn
      ((hcontinuous i).mono (by intro p hp; exact ⟨hKc i hp.1, Set.mem_univ _⟩))
  -- The finite compact union contains all covectors below the selected coordinate radii.
  let badAll : Set Cot := ⋃ i, bad i
  have hbadAll : IsCompact badAll := isCompact_iUnion hbad
  obtain ⟨B, hB⟩ := (hbadAll.image g.continuous_length).bddAbove
  let L := max B 0 + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro x ξ hξ
  obtain ⟨i, hsource, hwindow⟩ := hcover x
  let η := covectorInChart (c i) x ξ
  -- Differentiating the same chart inverse recovers the original total covector.
  have hback : covectorFromChart (c i) x η = ξ := by
    have hcoord : innerSL ℝ η = ξ.comp
        (mfderiv 𝓘(ℝ, X) 𝓘(ℝ, X) (c i).symm (c i x)) := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro j
      simp [η, covectorInChart, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right]
      rfl
    have hdiff : (c i).MDifferentiable 𝓘(ℝ, X) 𝓘(ℝ, X) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas (hc i)).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas (hc i)).mdifferentiableOn (by simp)⟩
    ext v
    have h := congrArg (fun T : TangentSpace 𝓘(ℝ, X) x →L[ℝ]
      TangentSpace 𝓘(ℝ, X) x ↦ T v) (hdiff.symm_comp_deriv hsource)
    change (mfderiv _ _ (c i).symm (c i x))
      ((mfderiv _ _ (c i) x) v) = v at h
    calc
      covectorFromChart (c i) x η v =
          ξ ((mfderiv _ _ (c i).symm (c i x))
            ((mfderiv _ _ (c i) x) v)) :=
        DFunLike.congr_fun hcoord ((mfderiv _ _ (c i) x) v)
      _ = ξ v := congrArg ξ h
  have htotal : inverse i (c i x, η) = (⟨x, ξ⟩ : Cot) := by
    dsimp only [inverse]
    rw [(c i).left_inv hsource, hback]
  refine ⟨i, hsource, hwindow, ?_⟩
  by_contra! hsmall
  have hmem : (⟨x, ξ⟩ : Cot) ∈ badAll :=
    mem_iUnion.mpr ⟨i, ⟨(c i x, η),
      ⟨hwindow, by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmall.le⟩,
      htotal⟩⟩
  have hbound : g.length x ξ ≤ B := hB ⟨⟨x, ξ⟩, hmem, rfl⟩
  have hBL : B < L := lt_of_le_of_lt (le_max_left B 0) (lt_add_one _)
  exact (not_le_of_gt hBL) (hξ.trans hbound)

end AtiyahSinger

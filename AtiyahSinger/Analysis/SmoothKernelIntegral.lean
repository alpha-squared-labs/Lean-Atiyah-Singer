/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.WeightedSmoothIntegral
public import AtiyahSinger.Geometry.SmoothKernel
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Weighted compact integrals of smooth bundle kernels

Public module ID: M0973.

Jointly smooth compact families of kernels can be integrated with continuous
complex parameter weights. The resulting actual kernel has the expected
operator formula, by Bochner integration in the original fibers and Fubini.
The base measure is the specified smooth positive measure; no invariance
assumption or change of fiber metric is involved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {V HY Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HY] (IY : ModelWithCorners ℝ V HY)
  [TopologicalSpace Y] [ChartedSpace HY Y] [IsManifold IY ∞ Y]
  [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (η : Measure Y) [IsFiniteMeasure η]

set_option maxHeartbeats 800000 in
-- The fiber integral, chart smoothness and exact Fubini comparison share one witness.
/-- A weighted compact kernel integral represents the average of its actual operators. -/
theorem SmoothKernel.exists_weighted_integral
    (K : Y → SmoothKernel (n := n) (r := r) (q := q) E F)
    (hK : ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f],
      ContMDiffOn (IY.prod
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun p : Y × (M × M) ↦ kernelInFrames E F (K p.1).toFun e f p.2)
        (univ ×ˢ (f.baseSet ×ˢ e.baseSet)))
    (w : Y → ℂ) (hw : Continuous w) :
    ∃ L : SmoothKernel (n := n) (r := r) (q := q) E F,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (L.toLinearMap μ u).val x = ∫ g, w g • ((K g).toLinearMap μ u).val x ∂η := by
  /- Integrate in each fixed space of fiber maps. In any two original frames,
  the same integral is the integral of the joint smooth matrix family, which
  is smooth by spatial differentiation. Fubini then identifies its action. -/
  classical
  let (x : M) : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  let (x : M) : CompleteSpace (F x) :=
    VectorBundle.completeSpace ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let W := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, W)
  have hcont (x y : M) : Continuous (fun g ↦ (K g).toFun x y) := by
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E y
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have he : y ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hmat : Continuous (fun g ↦ kernelInFrames E F (K g).toFun e f (x, y)) :=
      continuousOn_univ.mp ((hK e f).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun g _ ↦ ⟨mem_univ g, hf, he⟩))
    have hh := ((show Continuous (fun _ : Y ↦ f.symmL ℂ x) from
      continuous_const).clm_comp hmat).clm_comp
      (show Continuous (fun _ : Y ↦ e.continuousLinearMapAt ℂ y) from continuous_const)
    apply hh.congr
    intro g
    apply ContinuousLinearMap.ext
    intro v
    change f.symmL ℂ x (f.continuousLinearMapAt ℂ x
      ((K g).toFun x y (e.symmL ℂ y (e.continuousLinearMapAt ℂ y v)))) = _
    rw [e.symmL_continuousLinearMapAt he, f.symmL_continuousLinearMapAt hf]
  have hint (x y : M) : Integrable (fun g ↦ w g • (K g).toFun x y) η :=
    (hw.smul (hcont x y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L (x y : M) : E y →L[ℂ] F x := ∫ g, w g • (K g).toFun x y ∂η
  have hframe
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f]
      (z : M × M) (hz : z ∈ f.baseSet ×ˢ e.baseSet) :
      kernelInFrames E F L e f z =
        ∫ g, w g • kernelInFrames E F (K g).toFun e f z ∂η := by
    have hmat : Continuous (fun g ↦ kernelInFrames E F (K g).toFun e f z) :=
      continuousOn_univ.mp ((hK e f).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun g _ ↦ ⟨mem_univ g, hz⟩))
    have hmi : Integrable (fun g ↦ w g • kernelInFrames E F (K g).toFun e f z) η :=
      (hw.smul hmat).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    apply ContinuousLinearMap.ext
    intro v
    change f.continuousLinearMapAt ℂ z.1
      ((∫ g, w g • (K g).toFun z.1 z.2 ∂η) (e.symmL ℂ z.2 v)) = _
    rw [ContinuousLinearMap.integral_apply (hint z.1 z.2),
      ContinuousLinearMap.integral_apply hmi]
    have hvint : Integrable
        (fun g ↦ (w g • (K g).toFun z.1 z.2) (e.symmL ℂ z.2 v)) η :=
      (ContinuousLinearMap.apply ℂ (F z.1) (e.symmL ℂ z.2 v)).integrable_comp
        (hint z.1 z.2)
    rw [← (f.continuousLinearMapAt ℂ z.1).integral_comp_comm hvint]
    apply integral_congr_ae
    filter_upwards with g
    exact map_smul (f.continuousLinearMapAt ℂ z.1) (w g) _
  have hL : IsSmoothKernel (n := n) (r := r) (q := q) E F L := by
    intro e f _ _ z hz
    let X := W × W
    let J := 𝓘(ℝ, X)
    let a := chartAt W z.1
    let b := chartAt W z.2
    let s₁ := a.target ∩ a.symm ⁻¹' f.baseSet
    let s₂ := b.target ∩ b.symm ⁻¹' e.baseSet
    let s := s₁ ×ˢ s₂
    have hs₁ : IsOpen s₁ := a.isOpen_inter_preimage_symm f.open_baseSet
    have hs₂ : IsOpen s₂ := b.isOpen_inter_preimage_symm e.open_baseSet
    have hs : IsOpen s := hs₁.prod hs₂
    have ha : a z.1 ∈ s₁ := ⟨a.map_source (mem_chart_source _ z.1), by
      simpa only [mem_preimage, a.left_inv (mem_chart_source _ z.1)] using hz.1⟩
    have hb : b z.2 ∈ s₂ := ⟨b.map_source (mem_chart_source _ z.2), by
      simpa only [mem_preimage, b.left_inv (mem_chart_source _ z.2)] using hz.2⟩
    have hraw : ContMDiffOn (IY.prod J)
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun p : Y × X ↦ kernelInFrames E F (K p.1).toFun e f
          (a.symm p.2.1, b.symm p.2.2)) (univ ×ˢ s) := by
      apply (hK e f).comp
        (contMDiffOn_fst.prodMk
          (((contMDiffOn_chart_symm (I := I) (x := z.1)).comp
            ((ContinuousLinearMap.fst ℝ W W).contMDiff.comp contMDiff_snd).contMDiffOn
            (fun _ hp ↦ hp.2.1.1)).prodMk
            ((contMDiffOn_chart_symm (I := I) (x := z.2)).comp
              ((ContinuousLinearMap.snd ℝ W W).contMDiff.comp contMDiff_snd).contMDiffOn
              (fun _ hp ↦ hp.2.2.1))))
      exact fun p hp ↦ ⟨mem_univ p.1, hp.2.1.2, hp.2.2.2⟩
    have havg := contDiffOn_integral_smul_of_compact_manifold IY η hs hraw w hw
    have hac := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : ℕ∞ω)) z.1) (mem_chart_source _ z.1)
    have hbc := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : ℕ∞ω)) z.2) (mem_chart_source _ z.2)
    have hc : ContMDiffAt (I.prod I) J ∞ (fun p : M × M ↦ (a p.1, b p.2)) z :=
      (hac.comp z contMDiffAt_fst).prodMk_space (hbc.comp z contMDiffAt_snd)
    have hlocal := (havg.contMDiffOn.contMDiffAt (hs.mem_nhds ⟨ha, hb⟩)).comp z hc
    apply ContMDiffAt.contMDiffWithinAt
    apply hlocal.congr_of_eventuallyEq
    have hna := continuous_fst.continuousAt.preimage_mem_nhds
      (a.open_source.mem_nhds (mem_chart_source _ z.1))
    have hnb := continuous_snd.continuousAt.preimage_mem_nhds
      (b.open_source.mem_nhds (mem_chart_source _ z.2))
    filter_upwards [hna, hnb, (f.open_baseSet.prod e.open_baseSet).mem_nhds hz]
      with p hpa hpb hpB
    change kernelInFrames E F L e f p =
      ∫ g, w g • kernelInFrames E F (K g).toFun e f
        (a.symm (a p.1), b.symm (b p.2)) ∂η
    rw [a.left_inv hpa, b.left_inv hpb]
    exact hframe e f p hpB
  refine ⟨⟨L, hL⟩, ?_⟩
  intro u x
  -- Joint continuity in the compact parameter and input base supplies Fubini's integrability.
  have hvalue : Continuous (fun p : Y × M ↦ (K p.1).toFun x p.2 (u.val p.2)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E p.2
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have he : p.2 ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hmat := (hK e f).continuousOn.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      (s := (univ : Set Y) ×ˢ e.baseSet) (fun z hz ↦ ⟨mem_univ _, hf, hz.2⟩)
    have hu := (u.property e inferInstance).continuousOn.comp
      continuous_snd.continuousOn (s := (univ : Set Y) ×ˢ e.baseSet) (fun _ hz ↦ hz.2)
    have hloc := ((f.symmL ℂ x).continuous.comp_continuousOn (hmat.clm_apply hu)).continuousAt
      ((isOpen_univ.prod e.open_baseSet).mem_nhds ⟨mem_univ p.1, he⟩)
    apply hloc.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds he)] with z hz
    change (K z.1).toFun x z.2 (u.val z.2) =
      f.symmL ℂ x (f.continuousLinearMapAt ℂ x
        ((K z.1).toFun x z.2 (e.symmL ℂ z.2 ((e ⟨z.2, u.val z.2⟩).2))))
    rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz,
      e.symmL_continuousLinearMapAt hz, f.symmL_continuousLinearMapAt hf]
  have hprod : Integrable (fun p : Y × M ↦ w p.1 • (K p.1).toFun x p.2 (u.val p.2))
      (η.prod μ) :=
    ((hw.comp continuous_fst).smul hvalue).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ y, L x y (u.val y) ∂μ) = ∫ g, w g • (K g).apply μ u x ∂η
  calc
    _ = ∫ y, ∫ g, w g • (K g).toFun x y (u.val y) ∂η ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      exact ContinuousLinearMap.integral_apply (hint x y) (u.val y)
    _ = ∫ g, ∫ y, w g • (K g).toFun x y (u.val y) ∂μ ∂η :=
      (integral_integral_swap hprod).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with g
      exact integral_smul (w g) (fun y ↦ (K g).toFun x y (u.val y))

end AtiyahSinger

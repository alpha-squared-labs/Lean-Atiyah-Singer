/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator

import all AtiyahSinger.Analysis.SmoothingOperator
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Compact coordinate kernels on a possibly noncompact base

Public module ID: M0352.

Lift a genuine Euclidean kernel through two specified cutoffs and their original
frames. The inverse input density converts Euclidean integration to the supplied
smooth positive measure. Compact cutoff supports give joint smoothness across the
chart boundary and retain the exact localized action without compactness of the base.
This is the coordinate kernel construction used in the open extension argument of
SG III.13.4, with its density and support bookkeeping made explicit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap Topology

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1500000 in

/-- A true coordinate kernel lifts to the exact cutoff action with compact native support. -/
theorem exists_compactKernelLift
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (R : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hR : ∀ (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) z,
      R v z = ∫ w, k z w (v w)) :
    ∃ S : SmoothKernel (n := n) (r := r) (q := q) E F,
      (∀ x y, x ∉ c.symm '' tsupport B.cutoff ∨ y ∉ c.symm '' tsupport A.cutoff →
        S.toFun x y = 0) ∧
      ∀ (u : smoothSections (n := n) (r := r) E) x,
        S.apply μ u x = (B.extend hc (R (A.localize hc u))).val x := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  obtain ⟨ρ, hρ, hρpos, hρmap⟩ :=
    IsSmoothPositiveMeasure.exists_smooth_density (μ := μ) c hc
  let KA := c.symm '' tsupport A.cutoff
  let KB := c.symm '' tsupport B.cutoff
  have hKA : IsCompact KA := A.compact_support.image_of_continuousOn
    (c.continuousOn_symm.mono (fun z hz ↦ (A.support_subset hz).1))
  have hKB : IsCompact KB := B.compact_support.image_of_continuousOn
    (c.continuousOn_symm.mono (fun z hz ↦ (B.support_subset hz).1))
  let J (x y : M) : E y →L[ℂ] F x :=
    if x ∈ c.source then
      if y ∈ c.source then
        (B.cutoff (c x) * (A.cutoff (c y) / ρ (c y))) •
          (B.frame.symmL ℂ x).comp ((k (c x) (c y)).comp
            (A.frame.continuousLinearMapAt ℂ y))
      else 0
    else 0
  have hzero (x y : M) (h : x ∉ KB ∨ y ∉ KA) : J x y = 0 := by
    by_cases hx : x ∈ c.source
    · by_cases hy : y ∈ c.source
      · have hcut : B.cutoff (c x) = 0 ∨ A.cutoff (c y) = 0 := by
          rcases h with h | h
          · exact Or.inl (image_eq_zero_of_notMem_tsupport
              (fun hz ↦ h ⟨c x, hz, c.left_inv hx⟩))
          · exact Or.inr (image_eq_zero_of_notMem_tsupport
              (fun hz ↦ h ⟨c y, hz, c.left_inv hy⟩))
        rcases hcut with hcut | hcut <;> simp [J, hx, hy, hcut]
      · simp [J, hy]
    · simp [J, hx]
  -- On the supported chart, all matrices are written in the same two original frames.
  have hJ : IsSmoothKernel (n := n) (r := r) (q := q) E F J := by
    intro e f _ _ p hp
    by_cases hs : p ∈ KB ×ˢ KA
    · obtain ⟨z, hz, hx⟩ := hs.1
      obtain ⟨w, hw, hy⟩ := hs.2
      have hxc : p.1 ∈ c.source := hx ▸ c.map_target (B.support_subset hz).1
      have hyc : p.2 ∈ c.source := hy ▸ c.map_target (A.support_subset hw).1
      have hxf : p.1 ∈ B.frame.baseSet := hx ▸ (B.support_subset hz).2
      have hyf : p.2 ∈ A.frame.baseSet := hy ▸ (A.support_subset hw).2
      have hchartx := (contMDiffAt_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc) hxc).comp p
          (contMDiffAt_fst (I := I) (J := I))
      have hcharty := (contMDiffAt_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc) hyc).comp p
          (contMDiffAt_snd (I := I) (J := I))
      have hmatrix := hk.comp_contMDiffAt (hchartx.prodMk_space hcharty)
      have hin := ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e A.frame).contMDiffAt
         ((e.open_baseSet.inter A.frame.open_baseSet).mem_nhds
          ⟨hp.2, hyf⟩)).comp p (contMDiffAt_snd (I := I) (J := I))
      have hout := ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) B.frame f).contMDiffAt
         ((B.frame.open_baseSet.inter f.open_baseSet).mem_nhds
          ⟨hxf, hp.1⟩)).comp p (contMDiffAt_fst (I := I) (J := I))
      let comp₁ := (ContinuousLinearMap.compL ℂ V V W).bilinearRestrictScalars ℝ
      let comp₂ := (ContinuousLinearMap.compL ℂ V W W).bilinearRestrictScalars ℝ
      have hfull := (comp₂.contDiff.comp_contMDiffAt hout).clm_apply
        ((comp₁.contDiff.comp_contMDiffAt hmatrix).clm_apply hin)
      have hden : ContMDiffAt (I.prod I) 𝓘(ℝ) ∞
          (fun t : M × M ↦ ρ (c t.2)) p :=
        (hρ.contDiffAt (c.open_target.mem_nhds (c.map_source hyc))).contMDiffAt.comp p hcharty
      have hquot := (A.smooth_cutoff.comp_contMDiffAt hcharty).div₀
        hden (ne_of_gt (hρpos _ (c.map_source hyc)))
      have hweight : ContMDiffAt (I.prod I) 𝓘(ℝ) ∞
          (fun t : M × M ↦ B.cutoff (c t.1) * (A.cutoff (c t.2) / ρ (c t.2))) p :=
        contDiff_mul.comp_contMDiffAt
          ((B.smooth_cutoff.comp_contMDiffAt hchartx).prodMk_space hquot)
      apply ContMDiffAt.contMDiffWithinAt
      apply (hweight.smul hfull).congr_of_eventuallyEq
      filter_upwards [(c.open_source.prod c.open_source).mem_nhds ⟨hxc, hyc⟩,
        ((B.frame.open_baseSet.inter f.open_baseSet).prod
          (e.open_baseSet.inter A.frame.open_baseSet)).mem_nhds
            ⟨⟨hxf, hp.1⟩, ⟨hp.2, hyf⟩⟩] with t htc htf
      apply ContinuousLinearMap.ext
      intro v
      simp only [kernelInFrames, J, ite_eq_left htc.1, ite_eq_left htc.2,
        ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.map_smul_of_tower]
      change (B.cutoff (c t.1) * (A.cutoff (c t.2) / ρ (c t.2))) •
          f.continuousLinearMapAt ℂ t.1 (B.frame.symmL ℂ t.1
            (k (c t.1) (c t.2) (A.frame.continuousLinearMapAt ℂ t.2
              (e.symmL ℂ t.2 v)))) =
        (B.cutoff (c t.1) * (A.cutoff (c t.2) / ρ (c t.2))) •
          B.frame.coordChangeL ℂ f t.1
            (k (c t.1) (c t.2) (e.coordChangeL ℂ A.frame t.2 v))
      rw [B.frame.coordChangeL_apply f htf.1, e.coordChangeL_apply A.frame htf.2,
        ← B.frame.symmL_apply (R := ℂ) htf.1.1,
        ← f.continuousLinearMapAt_apply_of_mem ℂ htf.1.2,
        ← e.symmL_apply (R := ℂ) htf.2.1,
        ← A.frame.continuousLinearMapAt_apply_of_mem ℂ htf.2.2]
    · -- The complement of the compact rectangular support is an open zero neighborhood.
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq
      filter_upwards [(hKB.prod hKA).isClosed.isOpen_compl.mem_nhds hs] with t ht
      have ht' : t.1 ∉ KB ∨ t.2 ∉ KA := not_and_or.mp ht
      simp [kernelInFrames, hzero _ _ ht']
  refine ⟨⟨J, hJ⟩, hzero, ?_⟩
  intro u x
  let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  let : CompleteSpace (F x) := VectorBundle.completeSpace ℂ W F x
  let : FiniteDimensional ℂ (F x) := VectorBundle.finiteDimensional ℂ W F x
  let : MeasurableSpace (F x) := borel (F x)
  let : BorelSpace (F x) := ⟨rfl⟩
  by_cases hx : x ∈ KB
  · obtain ⟨z, hz, he⟩ := hx
    have hxc : x ∈ c.source := he ▸ c.map_target (B.support_subset hz).1
    have hxf : x ∈ B.frame.baseSet := he ▸ (B.support_subset hz).2
    let b := (B.frame.continuousLinearEquivAt ℂ x hxf).symm
    let : SecondCountableTopology (F x) := b.symm.toHomeomorph.secondCountableTopology
    have hb (w : W) : b w = B.frame.symmL ℂ x w :=
      congrFun (B.frame.symm_continuousLinearEquivAt_eq hxf) w
    let v := A.localize hc u
    have hrow : Continuous (fun w ↦ k (c x) w (v w)) :=
      (hk.continuous.comp (continuous_const.prodMk continuous_id)).clm_apply v.continuous
    let t (w : EuclideanSpace ℝ (Fin n)) : F x :=
      (ρ w)⁻¹ • (B.cutoff (c x) • b (k (c x) w (v w)))
    let g := c.target.piecewise t (fun _ ↦ 0)
    have ht : ContinuousOn t c.target :=
      (hρ.continuousOn.inv₀ (fun w hw ↦ ne_of_gt (hρpos w hw))).smul
        (continuous_const.smul (b.continuous.comp hrow)).continuousOn
    have hg : StronglyMeasurable g :=
      (ht.measurable_piecewise continuousOn_const c.open_target.measurableSet).stronglyMeasurable
    have hv (y : M) (hy : y ∈ c.source) :
        v (c y) = A.cutoff (c y) • A.frame.continuousLinearMapAt ℂ y (u.val y) := by
      change A.localizedFunction u (c y) = _
      simp only [BundleChartCutoff.localizedFunction, ite_eq_left (c.map_source hy),
        sectionInChart]
      erw [c.left_inv hy]
      by_cases hs : c y ∈ tsupport A.cutoff
      · have hyf : y ∈ A.frame.baseSet := by
          have h : c.symm (c y) ∈ A.frame.baseSet := (A.support_subset hs).2
          rwa [c.left_inv hy] at h
        rw [A.frame.continuousLinearMapAt_apply_of_mem ℂ hyf]
        exact algebraMap_smul ℂ (A.cutoff (c y)) _
      · simp [image_eq_zero_of_notMem_tsupport hs]
    have hchange : (∫ y, J x y (u.val y) ∂μ) = ∫ w in c.target, ρ w • g w := by
      apply integral_chart_of_smooth_density c μ ρ hρ.continuousOn
        (fun w hw ↦ (hρpos w hw).le) hρmap _ g hg
      · intro y hy
        simp only [g, Set.piecewise_eq_of_mem c.target t (fun _ ↦ 0) (c.map_source hy),
          t, hv y hy, J, ite_eq_left hxc, ite_eq_left hy,
          smul_apply, ContinuousLinearMap.comp_apply]
        rw [hb, ContinuousLinearMap.map_smul_of_tower,
          ContinuousLinearMap.map_smul_of_tower]
        change (ρ (c y))⁻¹ • (B.cutoff (c x) • (A.cutoff (c y) •
          B.frame.symmL ℂ x (k (c x) (c y)
            (A.frame.continuousLinearMapAt ℂ y (u.val y))))) = _
        simp only [smul_smul, div_eq_mul_inv]
        congr 1
        ring
      · intro y hy
        simp [J, hy]
    -- Cancel the original positive density only inside the same chart target.
    change (∫ y, J x y (u.val y) ∂μ) = B.extendedFunction (R v) x
    rw [hchange]
    calc
      _ = ∫ w in c.target, B.cutoff (c x) • b (k (c x) w (v w)) := by
        apply setIntegral_congr_fun c.open_target.measurableSet
        intro w hw
        change ρ w • g w = B.cutoff (c x) • b (k (c x) w (v w))
        rw [show g w = t w from Set.piecewise_eq_of_mem c.target t (fun _ ↦ 0) hw]
        simp only [t, smul_smul]
        rw [mul_inv_cancel_left₀ (ne_of_gt (hρpos w hw))]
      _ = ∫ w, B.cutoff (c x) • b (k (c x) w (v w)) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro w hw
          have hvzero : v w = 0 := by
            change A.localizedFunction u w = 0
            simp [BundleChartCutoff.localizedFunction, hw]
          simp [hvzero])
      _ = B.cutoff (c x) • b (∫ w, k (c x) w (v w)) := by
        rw [integral_smul, b.integral_comp_comm]
      _ = B.extendedFunction (R v) x := by
        rw [← hR v (c x)]
        simp only [BundleChartCutoff.extendedFunction, ite_eq_left hxc]
        rw [hb]
        exact (algebraMap_smul ℂ (B.cutoff (c x)) _).symm
  · change (∫ y, J x y (u.val y) ∂μ) = B.extendedFunction (R (A.localize hc u)) x
    rw [B.extendedFunction_eq_zero _ x hx]
    simp only [hzero x _ (Or.inl hx), zero_apply, integral_zero]

end AtiyahSinger

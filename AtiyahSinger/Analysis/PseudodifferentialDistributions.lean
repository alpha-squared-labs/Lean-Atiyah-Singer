/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DistributionSobolev
public import AtiyahSinger.Analysis.GlobalTranspose

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Global PDOs acting on distribution sections

Public module ID: M0890.

A02/A06: continuous smooth action, followed by the actual bilinear transpose on
covector tests, defines the distribution extension on a compact base. Compatibility
with every original Sobolev extension and with canonical presentation changes is
stated separately. No topology on the distribution carrier itself is needed here.
Sources: SG III.3.17(i),(iv) and (3.18); Taylor II.2 and III.1.4--1.5.
The compact-base extension and its uniqueness are explicit project deductions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 15

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

omit hF hμ [MeasurableSpace M] [BorelSpace M] in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
-- Compare localization and extension in the same smooth section presentations.
/-- Compact cutoff restriction and extension are continuous in the original smooth topology. -/
theorem BundleChartCutoff.continuous_localize_and_extend
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (L : BundleChartCutoff (r := r) E c)
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
    Continuous (fun u : A.SmoothSectionSpace ↦ L.localize hc (A.smoothSectionEquiv u)) ∧
      Continuous (fun v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) ↦
        A.smoothSectionEquiv.symm (L.extend hc v)) := by
  /- Insert one partition weight equal to one near the cutoff support. In that
  presentation restriction is Schwartz multiplication after a defining localization,
  and extension has only one nonzero localized component. The established Ck
  presentation comparison transfers both maps back to the given smooth topology. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let K := c.symm '' tsupport L.cutoff
  let U := c.source ∩ L.frame.baseSet
  have hK : IsCompact K := L.compact_support.image_of_continuousOn
    (c.continuousOn_symm.mono (fun z hz ↦ (L.support_subset hz).1))
  have hU : IsOpen U := c.open_source.inter L.frame.open_baseSet
  have hKU : K ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨c.map_target (L.support_subset hz).1, (L.support_subset hz).2⟩
  obtain ⟨β, hβzero, hβone, hβrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed
      (n := (⊤ : ℕ∞)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) hU.isClosed_compl hK.isClosed
      (Set.disjoint_compl_left_iff_subset.mpr hKU)
  have hβsupport : tsupport (β : M → ℝ) ⊆ U := by
    intro x hx
    by_contra hout
    have hzero : (β : M → ℝ) =ᶠ[nhds x] 0 :=
      (Filter.Eventually.filter_mono (nhds_le_nhdsSet (s := Uᶜ) hout) hβzero)
    have hnot : x ∉ closure (Function.support (β : M → ℝ)) := by
      rw [mem_closure_iff_frequently]
      exact fun hfreq ↦ (hfreq.and_eventually hzero).exists.elim
        (fun y hy ↦ hy.1 hy.2)
    exact hnot hx
  have hβK (x : M) (hx : x ∈ K) : β x = 1 := hβone.self_of_nhdsSet x hx
  -- Adjoin a chart on which the new partition weight is one near the supported maps.
  let C : SmoothBundlePresentation (n := n) (r := r) E :=
    { size := A.size + 1
      chart := Fin.cases c A.chart
      chart_mem_atlas := Fin.cases hc A.chart_mem_atlas
      frame := Fin.cases L.frame A.frame
      frame_mem_atlas := Fin.cases L.frame_mem_atlas A.frame_mem_atlas
      cutoff := Fin.cases (fun x ↦ β x) (fun j x ↦ (1 - β x) * A.cutoff j x)
      smooth_cutoff := Fin.cases β.contMDiff
        (fun j ↦ (show ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (1 - p.1) * p.2) from
          (contDiff_const.sub contDiff_fst).mul contDiff_snd).comp_contMDiff
            (β.contMDiff.prodMk_space (A.smooth_cutoff j)))
      cutoff_nonneg := Fin.cases (fun x ↦ (hβrange x).1)
        (fun j x ↦ mul_nonneg (sub_nonneg.mpr (hβrange x).2) (A.cutoff_nonneg j x))
      compact_support := fun _ ↦ HasCompactSupport.of_compactSpace _
      support_subset := Fin.cases hβsupport
        (fun j ↦ tsupport_mul_subset_right.trans (A.support_subset j))
      sum_cutoff := by
        intro x
        simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
        rw [← Finset.mul_sum, A.sum_cutoff]
        ring }
  have hlocal (Q : SmoothBundlePresentation (n := n) (r := r) E)
      (j : Fin Q.size) :
      Continuous (fun u : Q.SmoothSectionSpace ↦
        Q.localize j (Q.smoothSectionEquiv u)) := by
    let K := (Q.chart j) '' tsupport (Q.cutoff j)
    have hK : IsCompact K :=
      (Q.compact_support j).image_of_continuousOn
        ((Q.chart j).continuousOn.mono (fun x hx ↦ (Q.support_subset j hx).1))
    obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
    let T : Q.SmoothSectionSpace →ₗ[ℂ] SchwartzMap X V :=
      (Q.localizeLinearMap j).comp Q.smoothSectionEquiv.toLinearMap
    apply Q.withSeminorms_smoothSectionTopology.continuous_of_isBounded
      (schwartz_withSeminorms ℂ X V) T
    rintro ⟨a, b⟩
    refine ⟨{b}, ⟨R ^ a, pow_nonneg hRpos.le a⟩, ?_⟩
    intro u
    rw [Finset.sup_singleton]
    change SchwartzMap.seminorm ℂ a b
      (Q.localize j (Q.smoothSectionEquiv u)) ≤
      R ^ a * Q.smoothSectionSeminorm b u
    have hnonneg : 0 ≤ R ^ a * Q.smoothSectionSeminorm b u :=
      mul_nonneg (pow_nonneg hRpos.le a) (apply_nonneg _ u)
    apply SchwartzMap.seminorm_le_bound ℂ a b _ hnonneg
    intro x
    by_cases hx : x ∈ K
    · -- The original C^b supremum controls the identical localized derivative.
      have hderiv :
          ‖iteratedFDeriv ℝ b (Q.localize j (Q.smoothSectionEquiv u)) x‖ ≤
            Q.smoothSectionSeminorm b u := by
        change ‖iteratedFDeriv ℝ b
          (Q.localizedCkFunction b j (Q.smoothToCk b (Q.smoothSectionEquiv u))) x‖ ≤
            Q.ckNorm b (Q.smoothToCk b (Q.smoothSectionEquiv u))
        exact le_csSup (Q.bddAbove_ckNorm_values b _)
          ⟨j, b, le_rfl, x, rfl⟩
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hR x hx) a)
        hderiv (norm_nonneg _) (pow_nonneg hRpos.le a)
    · -- Derivatives vanish off that same support, including near chart boundaries.
      have hzero : iteratedFDeriv ℝ b (Q.localize j (Q.smoothSectionEquiv u)) x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hx (Q.tsupport_localizedFunction_subset j (Q.smoothSectionEquiv u)
          (tsupport_iteratedFDeriv_subset b hmem))
      simpa only [hzero, norm_zero, mul_zero] using hnonneg
  let χ : X → ℂ := fun z ↦ (L.cutoff z : ℂ)
  have hχsmooth : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp L.smooth_cutoff
  have hχcompact : HasCompactSupport χ :=
    L.compact_support.comp_left (show (Complex.ofReal : ℝ → ℂ) 0 = 0 from rfl)
  have hχgrowth : χ.HasTemperateGrowth := hχcompact.hasTemperateGrowth hχsmooth
  let T := SchwartzMap.smulLeftCLM V χ
  have hT (v : SchwartzMap X V) (z : X) : T v z = χ z • v z := by
    exact SchwartzMap.smulLeftCLM_apply_apply hχgrowth v z
  have hinput (u : C.SmoothSectionSpace) :
      L.localize hc (C.smoothSectionEquiv u) = T (C.localize 0 (C.smoothSectionEquiv u)) := by
    apply DFunLike.ext
    intro z
    rw [hT]
    change L.localizedFunction u z = χ z • C.localizedFunction 0 u z
    by_cases hz : z ∈ tsupport L.cutoff
    · have hzt := (L.support_subset hz).1
      have hβ := hβK (c.symm z) ⟨z, hz, rfl⟩
      simp [BundleChartCutoff.localizedFunction, SmoothBundlePresentation.localizedFunction,
        C, hzt, hβ, χ]
    · simp [BundleChartCutoff.localizedFunction, χ, image_eq_zero_of_notMem_tsupport hz]
  have hin : Continuous (fun u : C.SmoothSectionSpace ↦
      L.localize hc (C.smoothSectionEquiv u)) := by
    simp_rw [hinput]
    exact T.continuous.comp (hlocal C 0)
  -- Every old partition weight vanishes on the extension's support.
  have houtput (v : SchwartzMap X V) :
      C.localize 0 (L.extend hc v) = T v := by
    let := L.frame_mem_atlas
    apply DFunLike.ext
    intro z
    rw [hT]
    by_cases hz : z ∈ tsupport L.cutoff
    · have hzt := (L.support_subset hz).1
      have hzf := (L.support_subset hz).2
      have hzs := c.map_target hzt
      have hβ := hβK (c.symm z) ⟨z, hz, rfl⟩
      change C.localizedFunction 0 (L.extend hc v) z = _
      simp only [SmoothBundlePresentation.localizedFunction, C, Fin.cases_zero,
        ite_eq_left hzt, hβ, Complex.ofReal_one, one_smul, sectionInChart]
      change (L.frame.linearEquivAt ℂ (c.symm z) hzf)
        (L.extendedFunction v (c.symm z)) = _
      simp only [BundleChartCutoff.extendedFunction, ite_eq_left hzs,
        c.right_inv hzt, map_smul, L.frame.symmL_apply hzf]
      change χ z • (L.frame.linearEquivAt ℂ (c.symm z) hzf)
        ((L.frame.linearEquivAt ℂ (c.symm z) hzf).symm (v z)) = _
      rw [LinearEquiv.apply_symm_apply]
    · by_cases hzt : z ∈ c.target
      · have hzero : L.extendedFunction v (c.symm z) = 0 := by
          simp [BundleChartCutoff.extendedFunction, c.map_target hzt, c.right_inv hzt,
            image_eq_zero_of_notMem_tsupport hz]
        change C.localizedFunction 0 (L.extend hc v) z = _
        by_cases hb : β (c.symm z) = 0
        · simp [SmoothBundlePresentation.localizedFunction, C, hzt, hb, χ,
            image_eq_zero_of_notMem_tsupport hz]
        · have hf := (hβsupport (subset_tsupport _ hb)).2
          have hfzero := (L.frame.linearEquivAt ℂ (c.symm z) hf).map_zero
          change (L.frame ⟨c.symm z, 0⟩).2 = 0 at hfzero
          simp [SmoothBundlePresentation.localizedFunction, C, hzt, sectionInChart,
            BundleChartCutoff.extend, hzero, hfzero, χ,
            image_eq_zero_of_notMem_tsupport hz]
      · change C.localizedFunction 0 (L.extend hc v) z = _
        simp [SmoothBundlePresentation.localizedFunction, C, hzt, χ,
          image_eq_zero_of_notMem_tsupport hz]
  have hother (v : SchwartzMap X V) (j : Fin A.size) :
      C.localize j.succ (L.extend hc v) = 0 := by
    let := A.frame_mem_atlas j
    apply DFunLike.ext
    intro z
    change C.localizedFunction j.succ (L.extend hc v) z = 0
    by_cases hz : z ∈ (A.chart j).target
    · by_cases hKz : (A.chart j).symm z ∈ K
      · simp [SmoothBundlePresentation.localizedFunction, C, hz, hβK _ hKz]
      · have hzero := L.extendedFunction_eq_zero v ((A.chart j).symm z) hKz
        by_cases ha : A.cutoff j ((A.chart j).symm z) = 0
        · simp [SmoothBundlePresentation.localizedFunction, C, hz, ha]
        · have hf := (A.support_subset j (subset_tsupport _ ha)).2
          have hfzero := ((A.frame j).linearEquivAt ℂ ((A.chart j).symm z) hf).map_zero
          change ((A.frame j) ⟨(A.chart j).symm z, 0⟩).2 = 0 at hfzero
          simp [SmoothBundlePresentation.localizedFunction, C, hz, sectionInChart,
            BundleChartCutoff.extend, hzero, hfzero]
    · simp [SmoothBundlePresentation.localizedFunction, C, hz]
  -- Bound each output Ck seminorm by the finite Schwartz derivative family after T.
  let extMap : SchwartzMap X V →ₗ[ℂ] C.SmoothSectionSpace :=
    C.smoothSectionEquiv.symm.toLinearMap.comp (L.extendLinearMap hc)
  have hout : Continuous extMap := by
    let q : (ℕ × ℕ) → Seminorm ℂ (SchwartzMap X V) :=
      fun ab ↦ SchwartzMap.seminorm ℂ ab.1 ab.2
    let s (k : ℕ) : Finset (ℕ × ℕ) := (Finset.range (k + 1)).image (fun i ↦ (0, i))
    have hbound (k : ℕ) :
        (C.smoothSectionSeminorm k).comp extMap ≤ ((s k).sup q).comp T.toLinearMap := by
      intro v
      change C.ckNorm k (C.smoothToCk k (L.extend hc v)) ≤ (s k).sup q (T v)
      apply csSup_le
      · exact ⟨‖iteratedFDeriv ℝ 0
          (C.localizedCkFunction k 0 (C.smoothToCk k (L.extend hc v))) 0‖,
          0, 0, Nat.zero_le k, 0, rfl⟩
      · rintro a ⟨j, i, hi, x, rfl⟩
        change ‖iteratedFDeriv ℝ i (C.localize j (L.extend hc v)) x‖ ≤ _
        refine Fin.cases ?_ (fun j ↦ ?_) j
        · rw [houtput]
          apply (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (T v) i x).trans
          have hmem : (0, i) ∈ s k := Finset.mem_image.mpr
            ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
          exact (Finset.le_sup (f := q) hmem) (T v)
        · rw [hother]
          simp only [FunLike.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
          exact apply_nonneg _ _
    have : IsTopologicalAddGroup (SchwartzMap X V) := inferInstance
    apply C.withSeminorms_smoothSectionTopology.continuous_of_continuous_comp extMap
    intro k
    apply Seminorm.continuous_of_le _ (hbound k)
    exact (Seminorm.continuous_finsetSup
      (fun ab _ ↦ (schwartz_withSeminorms ℂ X V).continuous_seminorm ab)).comp T.continuous
  constructor
  · rw [A.smoothSectionTopology_eq C]
    exact hin
  · rw [A.smoothSectionTopology_eq C]
    exact hout

open Manifold Set Filter Topology in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
-- Finite-order integration and the closed-graph argument use the same original section norms.
/-- A smooth bundle kernel is bounded on each finite-order section space.
The estimate uses the specified measure, kernel, input presentation and output presentation. -/
theorem SmoothKernel.exists_ck_norm_bound
    (K : SmoothKernel (n := n) (r := r) (q := q) E F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      ‖B.smoothToCk k (K.toLinearMap μ u)‖ ≤ C * ‖A.smoothToCk k u‖ := by
  /- Work first on the complete Ck section spaces. Compact-parameter differentiation
  gives a genuine kernel map there. Its graph is closed because order-zero localization
  bounds both evaluation and each fixed-output kernel integral. The Banach closed-graph
  theorem then gives the bound on the original smooth sections. -/
  classical
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  have hIntegral {H G : Type}
      [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
      [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (k : ℕ) {f : M × H → G} {s : Set H} (hs : IsOpen s)
      (hf : ContMDiffOn (I.prod 𝓘(ℝ, H)) 𝓘(ℝ, G) k f (univ ×ˢ s)) :
      ContDiffOn ℝ k (fun x ↦ ∫ y, f (y, x) ∂μ) s := by
    /- Differentiate only in the open normed-space variable. Joint regularity of those derivatives
    provides a uniform bound on the compact parameter times a small closed ball. Dominated
    differentiation then makes induction on each finite smoothness order possible. -/
    have hpartial {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
        {l : ℕ} {g : M × H → A}
        (hg : ContMDiffOn (I.prod 𝓘(ℝ, H)) 𝓘(ℝ, A) (l + 1) g (univ ×ˢ s)) :
        ContMDiffOn (I.prod 𝓘(ℝ, H)) 𝓘(ℝ, H →L[ℝ] A) l
          (fun p ↦ fderiv ℝ (fun x ↦ g (p.1, x)) p.2) (univ ×ˢ s) := by
      -- Differentiate the variable in the vector space while retaining the manifold parameter.
      intro p hp
      have hlocal := (hg p hp).contMDiffAt ((isOpen_univ.prod hs).mem_nhds hp)
      have hcomp : ContMDiffAt ((I.prod 𝓘(ℝ, H)).prod 𝓘(ℝ, H)) 𝓘(ℝ, A) (l + 1)
          (fun q : (M × H) × H ↦ g (q.1.1, q.2)) (p, p.2) :=
        hlocal.comp_of_eq (contMDiffAt_fst.fst.prodMk contMDiffAt_snd) rfl
      have hd := hcomp.mfderiv (m := l) (fun q : M × H ↦ fun x : H ↦ g (q.1, x))
        (fun q : M × H ↦ q.2) contMDiffAt_snd (by simp)
      -- In a normed model, the tangent-coordinate derivative is the ordinary Fréchet derivative.
      have heq : inTangentCoordinates 𝓘(ℝ, H) 𝓘(ℝ, A)
          (fun q : M × H ↦ q.2) (fun q ↦ g (q.1, q.2))
          (fun q ↦ mfderiv 𝓘(ℝ, H) 𝓘(ℝ, A) (fun x ↦ g (q.1, x)) q.2) p =
          (fun q : M × H ↦ fderiv ℝ (fun x ↦ g (q.1, x)) q.2) := by
        funext q
        simp only [mfderiv_eq_fderiv]
        unfold inTangentCoordinates
        erw [inCoordinates_tangent_bundle_core_model_space]
        rfl
      rw [heq] at hd
      exact hd.contMDiffWithinAt
    have hderiv {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
        [CompleteSpace A] {l : ℕ} {g : M × H → A}
        (hg : ContMDiffOn (I.prod 𝓘(ℝ, H)) 𝓘(ℝ, A) (l + 1) g (univ ×ˢ s))
        {x : H} (hx : x ∈ s) :
        HasFDerivAt (fun x ↦ ∫ y, g (y, x) ∂μ)
          (∫ y, fderiv ℝ (fun x ↦ g (y, x)) x ∂μ) x := by
      let d : M × H → H →L[ℝ] A := fun p ↦ fderiv ℝ (fun x ↦ g (p.1, x)) p.2
      have hd : ContMDiffOn (I.prod 𝓘(ℝ, H)) 𝓘(ℝ, H →L[ℝ] A) l d (univ ×ˢ s) :=
        hpartial hg
      have hc (z : H) (hz : z ∈ s) : Continuous (fun y ↦ g (y, z)) := by
        apply continuousOn_univ.mp
        exact hg.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun y _ ↦ ⟨mem_univ y, hz⟩)
      have hdc (z : H) (hz : z ∈ s) : Continuous (fun y ↦ d (y, z)) := by
        apply continuousOn_univ.mp
        exact hd.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun y _ ↦ ⟨mem_univ y, hz⟩)
      -- Compactness makes the derivative bound uniform in the integration parameter.
      obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
      have hcompact : IsCompact ((univ : Set M) ×ˢ Metric.closedBall x r) :=
        isCompact_univ.prod (isCompact_closedBall x r)
      have hdcompact : ContinuousOn d (univ ×ˢ Metric.closedBall x r) :=
        hd.continuousOn.mono (prod_mono Subset.rfl hrs)
      obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hdcompact
      -- Differentiate under the integral using this constant, hence integrable, majorant.
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun z y ↦ d (y, z)) (bound := fun _ ↦ C) (Metric.closedBall_mem_nhds x hr)
      · filter_upwards [hs.mem_nhds hx] with z hz
        exact ((hc z hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).1
      · exact (hc x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact ((hdc x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).1
      · exact Filter.Eventually.of_forall (fun y z hz ↦ hC (y, z) ⟨mem_univ y, hz⟩)
      · exact integrable_const C
      · apply Filter.Eventually.of_forall
        intro y z hz
        have hlocal := (hg (y, z) ⟨mem_univ y, hrs hz⟩).contMDiffAt
          ((isOpen_univ.prod hs).mem_nhds ⟨mem_univ y, hrs hz⟩)
        have hslice : ContMDiffAt 𝓘(ℝ, H) 𝓘(ℝ, A) (l + 1) (fun z ↦ g (y, z)) z :=
          hlocal.comp_of_eq (contMDiffAt_const.prodMk contMDiffAt_id) rfl
        exact (hslice.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    -- Induct on the required finite order while allowing the derivative codomain to vary.
    induction k generalizing G with
    | zero =>
      -- Compact parameter support supplies continuity of the integral.
      change ContDiffOn ℝ 0 _ _
      rw [contDiffOn_zero]
      apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
      · exact hf.continuousOn.comp continuous_swap.continuousOn
          (fun p hp ↦ ⟨mem_univ p.2, hp.1⟩)
      · intro x y hx hy
        exact (hy (mem_univ y)).elim
    | succ n ih =>
      -- The derivative is another parameter integral, to which the induction hypothesis applies.
      change ContDiffOn ℝ ((n : ℕ∞ω) + 1) (fun x ↦ ∫ y, f (y, x) ∂μ) s
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
      have hder (x : H) (hx : x ∈ s) :=
        hderiv hf hx
      refine ⟨fun x hx ↦ (hder x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have hd := ih (G := H →L[ℝ] G) (hpartial hf)
      apply hd.congr
      intro x hx
      exact (hder x hx).fderiv
  have hJoint (k : ℕ) (u : contMDiffSections (n := n) (r := r) E k)
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f] :
      ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, EuclideanSpace ℂ (Fin q)) k
        (fun p : M × M ↦ f.continuousLinearMapAt ℂ p.2
          (K.toFun p.2 p.1 (u.val p.1))) (Set.univ ×ˢ f.baseSet) := by
    classical
    let Φ (p : M × M) : EuclideanSpace ℂ (Fin q) :=
      f.continuousLinearMapAt ℂ p.2 (K.toFun p.2 p.1 (u.val p.1))
    intro p hp
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E p.1
    have he : p.1 ∈ e.baseSet := mem_baseSet_trivializationAt _ _ p.1
    -- Locally the genuine integrand is the kernel matrix applied to input coordinates.
    have hmatrix := ((K.isSmooth e f).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).comp
      (contMDiffOn_snd.prodMk contMDiffOn_fst)
      (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ ⟨hz.2, hz.1⟩)
    have hu := (u.property e inferInstance).comp
      (contMDiffOn_fst (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
      (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.1)
    have heval : ContDiff ℝ k (fun z :
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          EuclideanSpace ℂ (Fin r) ↦ z.1 z.2) :=
      (show ContDiff ℂ k _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hlocal := heval.contMDiff.comp_contMDiffOn (hmatrix.prodMk_space hu)
    have hactual := hlocal.congr (f₁ := Φ) (by
      intro z hz
      change f.continuousLinearMapAt ℂ z.2 (K.toFun z.2 z.1 (u.val z.1)) =
        f.continuousLinearMapAt ℂ z.2 (K.toFun z.2 z.1
          (e.symmL ℂ z.1 ((e ⟨z.1, u.val z.1⟩).2)))
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.1,
        e.symmL_continuousLinearMapAt hz.1])
    exact (hactual.contMDiffAt ((e.open_baseSet.prod f.open_baseSet).mem_nhds
      ⟨he, hp.2⟩)).contMDiffWithinAt
  have hIntegrable (k : ℕ) (u : contMDiffSections (n := n) (r := r) E k)
      (x : M) : Integrable (fun y ↦ K.toFun x y (u.val y)) μ := by
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hx : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoord : Continuous (fun y ↦ f.continuousLinearMapAt ℂ x
        (K.toFun x y (u.val y))) := by
      apply continuousOn_univ.mp
      exact (hJoint k u f).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun y _ ↦ ⟨Set.mem_univ y, hx⟩)
    have hc := (f.symmL ℂ x).continuous.comp hcoord
    have hcont : Continuous (fun y ↦ K.toFun x y (u.val y)) := by
      apply hc.congr
      intro y
      exact f.symmL_continuousLinearMapAt hx _
    let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRegularity (k : ℕ) (u : contMDiffSections (n := n) (r := r) E k) :
      IsContMDiffSection (n := n) (r := q) F k
        (fun x ↦ ∫ y, K.toFun x y (u.val y) ∂μ) := by
    classical
    intro f hf
    let := hf
    let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
    let Φ (p : M × M) : EuclideanSpace ℂ (Fin q) :=
      f.continuousLinearMapAt ℂ p.2 (K.toFun p.2 p.1 (u.val p.1))
    have hΦ := hJoint k u f
    -- Move only the output variable into a finite-dimensional open coordinate domain.
    intro x hx
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let s := c.target ∩ c.symm ⁻¹' f.baseSet
    have hs : IsOpen s := c.isOpen_inter_preimage_symm f.open_baseSet
    have hcx : c x ∈ s := ⟨c.map_source (mem_chart_source _ x), by
      simpa only [Set.mem_preimage, c, OpenPartialHomeomorph.left_inv _ (mem_chart_source _ x)]
        using hx⟩
    have hchart : ContMDiffOn
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, EuclideanSpace ℂ (Fin q)) k
        (fun p : M × EuclideanSpace ℝ (Fin n) ↦ Φ (p.1, c.symm p.2)) (Set.univ ×ˢ s) := by
      apply hΦ.comp
        (contMDiffOn_fst.prodMk ((contMDiffOn_chart_symm
          (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (x := x)).comp contMDiffOn_snd
            (fun _ hp ↦ hp.2.1)))
      intro p hp
      exact ⟨Set.mem_univ _, hp.2.2⟩
    have hint : ContDiffOn ℝ k
        (fun z : EuclideanSpace ℝ (Fin n) ↦ ∫ y, Φ (y, c.symm z) ∂μ) s :=
      hIntegral k hs hchart
    have hlocal := (hint.contMDiffOn.contMDiffAt (hs.mem_nhds hcx)).comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x) (mem_chart_source _ x))
    -- The same original output frame commutes with the fixed-fiber Bochner integral.
    apply ContMDiffAt.contMDiffWithinAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x),
      f.open_baseSet.mem_nhds hx] with z hzc hzf
    let : NormedSpace ℝ (F z) := NormedSpace.restrictScalars ℝ ℂ (F z)
    change (f ⟨z, ∫ y, K.toFun z y (u.val y) ∂μ⟩).2 = ∫ y, Φ (y, c.symm (c z)) ∂μ
    rw [c.left_inv hzc]
    rw [← f.continuousLinearMapAt_apply_of_mem ℂ hzf]
    let : NormedSpace ℝ (F z) := NormedSpace.restrictScalars ℝ ℂ (F z)
    let : CompleteSpace (F z) := VectorBundle.completeSpace ℂ
      (EuclideanSpace ℂ (Fin q)) F z
    exact ((f.continuousLinearMapAt ℂ z).integral_comp_comm (hIntegrable k u z)).symm
  let Tck (k : ℕ) : A.CkSectionSpace k →ₗ[ℂ] B.CkSectionSpace k :=
    { toFun u := ⟨fun x ↦ ∫ y, K.toFun x y (u.val y) ∂μ, hRegularity k u⟩
      map_add' u v := by
        apply Subtype.ext
        funext x
        change (∫ y, K.toFun x y (u.val y + v.val y) ∂μ) =
          (∫ y, K.toFun x y (u.val y) ∂μ) + ∫ y, K.toFun x y (v.val y) ∂μ
        simp_rw [map_add]
        exact integral_add (hIntegrable k u x) (hIntegrable k v x)
      map_smul' c u := by
        apply Subtype.ext
        funext x
        change (∫ y, K.toFun x y (c • u.val y) ∂μ) =
          c • ∫ y, K.toFun x y (u.val y) ∂μ
        simp_rw [map_smul]
        exact integral_smul c _ }
  have hCoordinateBound (k : ℕ)
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f]
      (x : M) (hx : x ∈ f.baseSet) :
      ∃ C : ℝ, ∀ u : A.CkSectionSpace k,
        ‖∫ y, f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y)) ∂μ‖ ≤ C * ‖u‖ := by
    classical
    let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
    let (j : Fin A.size) : MemTrivializationAtlas (A.frame j) := A.frame_mem_atlas j
    -- Only the compact support of each cutoff is used to bound the kernel matrix.
    have hcoeff (j : Fin A.size) : ∃ C : ℝ, 0 ≤ C ∧
        ∀ y ∈ tsupport (A.cutoff j),
          ‖kernelInFrames E F K.toFun (A.frame j) f (x, y)‖ ≤ C := by
      let := A.frame_mem_atlas j
      have hcont : ContinuousOn
          (fun y ↦ kernelInFrames E F K.toFun (A.frame j) f (x, y))
          (tsupport (A.cutoff j)) :=
        (K.isSmooth (A.frame j) f).continuousOn.comp
          (continuous_const.prodMk continuous_id).continuousOn
          (fun y hy ↦ ⟨hx, (A.support_subset j hy).2⟩)
      obtain ⟨C, hC⟩ := (A.compact_support j).exists_bound_of_continuousOn hcont
      exact ⟨max C 0, le_max_right _ _, fun y hy ↦ (hC y hy).trans (le_max_left _ _)⟩
    choose C hC hcoeff using hcoeff
    refine ⟨(∑ j, C j) * μ.real Set.univ, ?_⟩
    intro u
    have hloc (j : Fin A.size) (y : M) :
        ‖(A.cutoff j y : ℂ) • f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y))‖ ≤
          C j * ‖u‖ := by
      by_cases hy : A.cutoff j y = 0
      · simpa only [hy, Complex.ofReal_zero, zero_smul, norm_zero] using
          mul_nonneg (hC j) (norm_nonneg u)
      have hys := A.support_subset j (subset_tsupport _ hy)
      let := A.frame_mem_atlas j
      have heval : A.localizedCkFunction k j u (A.chart j y) =
          (A.cutoff j y : ℂ) • (A.frame j).continuousLinearMapAt ℂ y (u.val y) := by
        have hpair : (⟨(A.chart j).symm (A.chart j y),
            u.val ((A.chart j).symm (A.chart j y))⟩ :
              TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨y, u.val y⟩ :=
          congrArg (fun z ↦ (⟨z, u.val z⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
            ((A.chart j).left_inv hys.1)
        simp only [SmoothBundlePresentation.localizedCkFunction,
          ite_eq_left ((A.chart j).map_source hys.1), sectionInChart, hpair,
          (A.chart j).left_inv hys.1]
        rw [← (A.frame j).continuousLinearMapAt_apply_of_mem ℂ hys.2]
      have hnorm : ‖A.localizedCkFunction k j u (A.chart j y)‖ ≤ ‖u‖ := by
        have h := le_csSup (A.bddAbove_ckNorm_values k u)
          (show ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j u) (A.chart j y)‖ ∈
            {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
              ∃ z : EuclideanSpace ℝ (Fin n),
                a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) z‖} from
            ⟨j, 0, Nat.zero_le k, A.chart j y, rfl⟩)
        change ‖A.localizedCkFunction k j u (A.chart j y)‖ ≤ A.ckNorm k u
        change ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j u) (A.chart j y)‖ ≤
          A.ckNorm k u at h
        simpa only [norm_iteratedFDeriv_zero] using h
      have hident : (A.cutoff j y : ℂ) •
          f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y)) =
          kernelInFrames E F K.toFun (A.frame j) f (x, y)
            (A.localizedCkFunction k j u (A.chart j y)) := by
        rw [heval, map_smul]
        unfold kernelInFrames
        simp only [ContinuousLinearMap.comp_apply,
          (A.frame j).symmL_continuousLinearMapAt hys.2]
      rw [hident]
      exact ((kernelInFrames E F K.toFun (A.frame j) f (x, y)).le_opNorm _).trans
        (mul_le_mul (hcoeff j y (subset_tsupport _ hy)) hnorm
          (norm_nonneg _) (hC j))
    have hbound (y : M) :
        ‖f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y))‖ ≤ (∑ j, C j) * ‖u‖ := by
      have hpartition : (∑ j, (A.cutoff j y : ℂ)) = 1 := by
        exact_mod_cast A.sum_cutoff y
      calc
        ‖f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y))‖ =
            ‖∑ j, (A.cutoff j y : ℂ) •
              f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y))‖ := by
                rw [← Finset.sum_smul, hpartition, one_smul]
        _ ≤ ∑ j, ‖(A.cutoff j y : ℂ) •
              f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y))‖ := norm_sum_le _ _
        _ ≤ ∑ j, C j * ‖u‖ := Finset.sum_le_sum (fun j _ ↦ hloc j y)
        _ = (∑ j, C j) * ‖u‖ := (Finset.sum_mul _ _ _).symm
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall hbound)
    calc
      ‖∫ y, f.continuousLinearMapAt ℂ x (K.toFun x y (u.val y)) ∂μ‖ ≤
          ((∑ j, C j) * ‖u‖) * μ.real Set.univ := h
      _ = ((∑ j, C j) * μ.real Set.univ) * ‖u‖ := by ring
  have hContinuous (k : ℕ) : Continuous (Tck k) := by
    classical
    have hpoint (P : SmoothBundlePresentation (n := n) (r := q) F)
        (a : ℕ → P.CkSectionSpace k) (u : P.CkSectionSpace k)
        (ha : Filter.Tendsto a Filter.atTop (nhds u))
        (e : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas e]
        (x : M) (hxe : x ∈ e.baseSet) :
        Filter.Tendsto (fun b ↦ (e ⟨x, (a b).val x⟩).2) Filter.atTop
          (nhds ((e ⟨x, u.val x⟩).2)) := by
      have hchoose : ∃ j : Fin P.size, P.cutoff j x ≠ 0 := by
        by_contra! h
        have hsum := P.sum_cutoff x
        simp only [h, Finset.sum_const_zero] at hsum
        exact zero_ne_one hsum
      obtain ⟨j, hj⟩ := hchoose
      have hx := P.support_subset j (subset_tsupport _ hj)
      let := P.frame_mem_atlas j
      let ev : P.CkSectionSpace k →ₗ[ℂ] EuclideanSpace ℂ (Fin q) :=
        { toFun := fun w ↦ (P.cutoff j x : ℂ) •
            ((P.frame j).linearEquivAt ℂ x hx.2) (w.val x)
          map_add' := by
            intro v w
            change (P.cutoff j x : ℂ) •
              ((P.frame j).linearEquivAt ℂ x hx.2) (v.val x + w.val x) = _
            rw [map_add, smul_add]
          map_smul' := by
            intro c w
            change (P.cutoff j x : ℂ) •
              ((P.frame j).linearEquivAt ℂ x hx.2) (c • w.val x) = _
            rw [map_smul, smul_comm]
            rfl }
      have heval (w : P.CkSectionSpace k) :
          ev w = P.localizedCkFunction k j w (P.chart j x) := by
        have hpair : (⟨(P.chart j).symm (P.chart j x),
            w.val ((P.chart j).symm (P.chart j x))⟩ :
              TotalSpace (EuclideanSpace ℂ (Fin q)) F) = ⟨x, w.val x⟩ :=
          congrArg (fun y ↦ (⟨y, w.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin q)) F))
            ((P.chart j).left_inv hx.1)
        simp only [SmoothBundlePresentation.localizedCkFunction,
          ite_eq_left ((P.chart j).map_source hx.1),
          sectionInChart, hpair, (P.chart j).left_inv hx.1]
        rfl
      have hbound (w : P.CkSectionSpace k) : ‖ev w‖ ≤ 1 * ‖w‖ := by
        rw [one_mul, heval]
        change ‖P.localizedCkFunction k j w (P.chart j x)‖ ≤ P.ckNorm k w
        have h := le_csSup (P.bddAbove_ckNorm_values k w)
          (show ‖iteratedFDeriv ℝ 0 (P.localizedCkFunction k j w) (P.chart j x)‖ ∈
            {a : ℝ | ∃ (j : Fin P.size) (i : ℕ), i ≤ k ∧
              ∃ z : EuclideanSpace ℝ (Fin n),
                a = ‖iteratedFDeriv ℝ i (P.localizedCkFunction k j w) z‖} from
            ⟨j, 0, Nat.zero_le k, P.chart j x, rfl⟩)
        change ‖iteratedFDeriv ℝ 0 (P.localizedCkFunction k j w) (P.chart j x)‖ ≤
          P.ckNorm k w at h
        simpa only [norm_iteratedFDeriv_zero] using h
      have hvalues := ((ev.mkContinuous 1 hbound).continuous.tendsto u).comp ha
      -- Divide the nonzero original cutoff and use the finite-dimensional frame transition.
      let T := ((e.linearEquivAt ℂ x hxe).toLinearMap.comp
        ((P.frame j).linearEquivAt ℂ x hx.2).symm.toLinearMap).toContinuousLinearMap
      let ψ : EuclideanSpace ℂ (Fin q) → EuclideanSpace ℂ (Fin q) :=
        fun z ↦ T ((P.cutoff j x : ℂ)⁻¹ • z)
      have hψ : Continuous ψ := by
        change Continuous (fun z : EuclideanSpace ℂ (Fin q) ↦ T ((P.cutoff j x : ℂ)⁻¹ • z))
        have hscale : Continuous (fun z : EuclideanSpace ℂ (Fin q) ↦
            (P.cutoff j x : ℂ)⁻¹ • z) :=
          ((P.cutoff j x : ℂ)⁻¹ • ContinuousLinearMap.id ℂ
            (EuclideanSpace ℂ (Fin q))).continuous
        exact T.continuous.comp hscale
      have hχ : (P.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hj
      have hrecover (w : P.CkSectionSpace k) : ψ (ev w) = (e ⟨x, w.val x⟩).2 := by
        change (e.linearEquivAt ℂ x hxe)
          (((P.frame j).linearEquivAt ℂ x hx.2).symm
            ((P.cutoff j x : ℂ)⁻¹ •
              ((P.cutoff j x : ℂ) • ((P.frame j).linearEquivAt ℂ x hx.2) (w.val x)))) = _
        rw [smul_smul, inv_mul_cancel₀ hχ, one_smul, LinearEquiv.symm_apply_apply]
        rfl
      have hh := (hψ.tendsto _).comp hvalues
      change Filter.Tendsto (fun b ↦ ψ (ev (a b))) Filter.atTop (nhds (ψ (ev u))) at hh
      simpa only [hrecover] using hh
    -- Coordinate integral bounds identify both limits of the same graph.
    let I := Tck k
    apply I.continuous_of_seq_closed_graph
    intro a u v hau hav
    apply Subtype.ext
    funext x
    let e := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    let L : A.CkSectionSpace k →ₗ[ℂ] EuclideanSpace ℂ (Fin q) :=
      { toFun := fun w ↦ e.continuousLinearMapAt ℂ x ((I w).val x)
        map_add' := by
          intro w z
          rw [I.map_add]
          exact (e.continuousLinearMapAt ℂ x).map_add _ _
        map_smul' := by
          intro c w
          rw [I.map_smul]
          exact (e.continuousLinearMapAt ℂ x).map_smul c _ }
    have heval (w : A.CkSectionSpace k) :
        L w = ∫ y, e.continuousLinearMapAt ℂ x (K.toFun x y (w.val y)) ∂μ := by
      let : CompleteSpace (F x) := VectorBundle.completeSpace ℂ
        (EuclideanSpace ℂ (Fin q)) F x
      exact ((e.continuousLinearMapAt ℂ x).integral_comp_comm
        (hIntegrable k w x)).symm
    obtain ⟨C, hC⟩ := hCoordinateBound k e x hx
    have hbound (w : A.CkSectionSpace k) : ‖L w‖ ≤ C * ‖w‖ := by
      rw [heval]
      exact hC w
    have hlimit := ((L.mkContinuous C hbound).continuous.tendsto u).comp hau
    change Filter.Tendsto (fun b ↦ e.continuousLinearMapAt ℂ x ((I (a b)).val x))
      Filter.atTop (nhds (e.continuousLinearMapAt ℂ x ((I u).val x))) at hlimit
    rw [show (fun b ↦ e.continuousLinearMapAt ℂ x ((I (a b)).val x)) =
        (fun b ↦ (e ⟨x, (I (a b)).val x⟩).2) from funext (fun b ↦
          e.continuousLinearMapAt_apply_of_mem ℂ hx _),
      e.continuousLinearMapAt_apply_of_mem ℂ hx] at hlimit
    apply (e.linearEquivAt ℂ x hx).injective
    exact tendsto_nhds_unique (hpoint B (I ∘ a) v hav e x hx) hlimit
  let T : A.CkSectionSpace k →L[ℂ] B.CkSectionSpace k :=
    { toLinearMap := Tck k
      cont := hContinuous k }
  refine ⟨‖T‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg T) zero_lt_one, ?_⟩
  intro u
  calc
    ‖B.smoothToCk k (K.toLinearMap μ u)‖ = ‖T (A.smoothToCk k u)‖ := rfl
    _ ≤ ‖T‖ * ‖A.smoothToCk k u‖ := T.le_opNorm _
    _ ≤ (‖T‖ + 1) * ‖A.smoothToCk k u‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- Each output derivative seminorm of a PDO is bounded by one input derivative seminorm. -/
theorem exists_smoothSectionSeminorm_bound (k : ℕ) :
    ∃ l : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : A.SmoothSectionSpace,
      B.smoothSectionSeminorm k
        (B.smoothSectionEquiv.symm (P.toLinearMap (A.smoothSectionEquiv u))) ≤
          C * A.smoothSectionSeminorm l u := by
  /- Each local PDO is the composition of continuous cutoff restriction,
  the specified Schwartz operator, and cutoff extension. Smooth kernels have
  a finite-order section estimate. Compose these maps into the output Ck space
  and extract one input derivative order from its actual smooth topology. -/
  classical
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  let S := (B.smoothToCk k).comp B.smoothSectionEquiv.toLinearMap
  have hS : Continuous S := (B.continuous_linearMap_iff_exists_bound S).2
    ⟨k, 1, zero_lt_one, fun u ↦ by simp [S, B.smoothSectionSeminorm_apply]⟩
  -- Every local map uses exactly the two frames and cutoffs of its given representative.
  have hpieces (j : Fin N) : Continuous (fun u : A.SmoothSectionSpace ↦
      B.smoothToCk k ((L j).toLinearMap (A.smoothSectionEquiv u))) := by
    have hin := ((L j).input.continuous_localize_and_extend A
      (L j).chart_mem_atlas).1
    have hout := ((L j).output.continuous_localize_and_extend B
      (L j).chart_mem_atlas).2
    exact hS.comp (hout.comp ((L j).operator.continuous.comp hin))
  have hkernel : Continuous (fun u : A.SmoothSectionSpace ↦
      B.smoothToCk k (K.toLinearMap μ (A.smoothSectionEquiv u))) := by
    let R := (B.smoothToCk k).comp
      ((K.toLinearMap μ).comp A.smoothSectionEquiv.toLinearMap)
    apply (A.continuous_linearMap_iff_exists_bound R).2
    obtain ⟨C, hC, hbound⟩ := K.exists_ck_norm_bound (μ := μ) A B k
    exact ⟨k, C, hC, fun u ↦ hbound (A.smoothSectionEquiv u)⟩
  let T := (B.smoothToCk k).comp (P.toLinearMap.comp A.smoothSectionEquiv.toLinearMap)
  have hdecomp : P.toLinearMap = (∑ j, (L j).toLinearMap) + K.toLinearMap μ := by
    exact sub_eq_iff_eq_add.mp hK.symm |>.trans (add_comm _ _)
  have hT : Continuous T := by
    have hsum := (continuous_finsetSum Finset.univ (fun j _ ↦ hpieces j)).add hkernel
    change Continuous (fun u : A.SmoothSectionSpace ↦
      (∑ j, B.smoothToCk k ((L j).toLinearMap (A.smoothSectionEquiv u))) +
        B.smoothToCk k (K.toLinearMap μ (A.smoothSectionEquiv u))) at hsum
    apply hsum.congr
    intro u
    symm
    change (B.smoothToCk k) (P.toLinearMap (A.smoothSectionEquiv u)) = _
    rw [hdecomp, LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum]
  exact (A.continuous_linearMap_iff_exists_bound T).1 hT

/-- The original smooth-section PDO action is continuous for the actual C-infinity topologies. -/
theorem continuous_smoothSectionMap :
    Continuous (fun u : A.SmoothSectionSpace ↦
      B.smoothSectionEquiv.symm (P.toLinearMap (A.smoothSectionEquiv u))) := by
  /- Bound each defining output seminorm by its own finite input order. The
  same derivative order need not control all output seminorms simultaneously. -/
  let T := B.smoothSectionEquiv.symm.toLinearMap.comp
    (P.toLinearMap.comp A.smoothSectionEquiv.toLinearMap)
  apply A.withSeminorms_smoothSectionTopology.continuous_of_isBounded
    B.withSeminorms_smoothSectionTopology T
  intro k
  obtain ⟨l, C, hC, hbound⟩ := P.exists_smoothSectionSeminorm_bound A B k
  refine ⟨{l}, ⟨C, hC.le⟩, ?_⟩
  intro u
  rw [Finset.sup_singleton]
  exact hbound u

/-- The same smooth PDO action packaged with its derivative-topology continuity. -/
def smoothSectionMap : A.SmoothSectionSpace →L[ℂ] B.SmoothSectionSpace where
  toLinearMap := B.smoothSectionEquiv.symm.toLinearMap.comp
    (P.toLinearMap.comp A.smoothSectionEquiv.toLinearMap)
  cont := P.continuous_smoothSectionMap A B

/-- The distribution action is actual precomposition by the smooth formal transpose. -/
def distributionExtension : A.DistributionSection μ →ₗ[ℂ] B.DistributionSection μ where
  toFun D := D.comp (P.formalTranspose.smoothSectionMap B.dualPresentation A.dualPresentation)
  map_add' D G := by
    ext α
    rfl
  map_smul' c D := by
    ext α
    rfl

/-- Distributional evaluation applies the formal transpose to the test, without conjugation. -/
theorem distributionExtension_apply (D : A.DistributionSection μ)
    (α : B.dualPresentation.SmoothSectionSpace) :
    P.distributionExtension A B D α = D
      (A.dualPresentation.smoothSectionEquiv.symm
        (P.formalTranspose.toLinearMap (B.dualPresentation.smoothSectionEquiv α))) := by
  -- Precomposition uses precisely the original bilinear transpose on this test.
  rfl

/-- Every original Sobolev extension represents this same distribution action. -/
theorem distributionExtension_sobolevToDistribution (s : ℝ) (u : A.SobolevSpace s) :
    P.distributionExtension A B (A.sobolevToDistribution μ s u) =
      B.sobolevToDistribution μ (s - m) (P.sobolevExtension A B s u) := by
  /- Evaluate both sides on a smooth covector. The smooth-input specification
  of sobolevTranspose identifies the transposed test in H^(-s). The actual duality
  identity then moves P onto the primal Sobolev vector. This gives equality on
  every test, hence equality of the continuous functionals. No ellipticity is used. -/
  apply ContinuousLinearMap.ext
  intro α
  rw [P.distributionExtension_apply, A.sobolevToDistribution_apply,
    B.sobolevToDistribution_apply, A.dualTestToSobolev_apply, B.dualTestToSobolev_apply]
  simp only [LinearEquiv.apply_symm_apply]
  let β := (dualSectionsEquiv F).symm (B.dualPresentation.smoothSectionEquiv α)
  have htranspose := P.sobolevTranspose_smooth A B s β
  simp only [β, LinearEquiv.apply_symm_apply] at htranspose
  change A.sobolevEvaluationDuality μ s
    (A.dualSmoothToSobolev (-s) ((dualSectionsEquiv E).symm
      (P.formalTranspose.toLinearMap (B.dualPresentation.smoothSectionEquiv α)))) u =
    B.sobolevEvaluationDuality μ (s - m)
      (B.dualSmoothToSobolev (-(s - m)) β) (P.sobolevExtension A B s u)
  rw [← htranspose, P.sobolevEvaluationDuality_transpose]
  rfl

/-- On smooth sections the distribution action is the original section operator. -/
theorem distributionExtension_smoothToDistribution
    (u : smoothSections (n := n) (r := r) E) :
    P.distributionExtension A B (A.smoothToDistribution μ u) =
      B.smoothToDistribution μ (P.toLinearMap u) := by
  /- Express the input through its order-zero Sobolev realization, use the
  compatibility theorem, and apply the smooth-input formula of the Sobolev
  extension. The result is the same integral distribution at the output order. -/
  rw [← A.sobolevToDistribution_smoothToSobolev μ 0 u,
    P.distributionExtension_sobolevToDistribution,
    P.sobolevExtension_smoothToSobolev, B.sobolevToDistribution_smoothToSobolev]

/-- Equal distributions in different Sobolev realizations have identical distributional images. -/
theorem sobolevToDistribution_sobolevExtension_eq (s t : ℝ)
    (u : A.SobolevSpace s) (v : A.SobolevSpace t)
    (huv : A.sobolevToDistribution μ s u = A.sobolevToDistribution μ t v) :
    B.sobolevToDistribution μ (s - m) (P.sobolevExtension A B s u) =
      B.sobolevToDistribution μ (t - m) (P.sobolevExtension A B t v) := by
  /- Apply the single distributionExtension to huv. Rewrite both sides with
  the Sobolev compatibility formula. The ambient orders s and t are arbitrary;
  this proves representative independence without choosing a preferred order. -/
  have h := congrArg (P.distributionExtension A B) huv
  simpa only [P.distributionExtension_sobolevToDistribution] using h

/-- Compatibility on all Sobolev images uniquely determines a linear distribution extension. -/
theorem distributionExtension_unique
    (T : A.DistributionSection μ →ₗ[ℂ] B.DistributionSection μ)
    (hT : ∀ (s : ℝ) (u : A.SobolevSpace s),
      T (A.sobolevToDistribution μ s u) =
        B.sobolevToDistribution μ (s - m) (P.sobolevExtension A B s u)) :
    T = P.distributionExtension A B := by
  /- For each distribution choose the negative-order representative supplied
  by its finite-order theorem. Apply hT and the preceding compatibility formula
  at that order. Agreement only on smooth sections would not suffice for an
  arbitrary linear T without a continuity premise; all Sobolev images are required. -/
  apply LinearMap.ext
  intro D
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu, hT, P.distributionExtension_sobolevToDistribution]

/-- Canonical changes of finite presentations commute with the distribution action. -/
theorem distributionExtension_distributionEquiv
    (A' : SmoothBundlePresentation (n := n) (r := r) E)
    (B' : SmoothBundlePresentation (n := n) (r := q) F) (D : A.DistributionSection μ) :
    B.distributionEquiv μ B' (P.distributionExtension A B D) =
      P.distributionExtension A' B' (A.distributionEquiv μ A' D) := by
  /- Both presentation comparisons retain the same actual covector section.
  Thus the same transpose is applied before evaluation by the same distribution. -/
  apply ContinuousLinearMap.ext
  intro α
  rw [SmoothBundlePresentation.distributionEquiv_apply, distributionExtension_apply,
    distributionExtension_apply, SmoothBundlePresentation.distributionEquiv_apply]
  rfl

/-- The distribution action depends on the actual PDO map, not its chosen order bound. -/
theorem distributionExtension_eq_of_toLinearMap_eq {l : ℝ}
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ l)
    (hPQ : P.toLinearMap = Q.toLinearMap) :
    P.distributionExtension A B = Q.distributionExtension A B := by
  /- Uniqueness among all smooth section maps first identifies the transposes.
  Equality of their test actions then identifies the distribution extensions. -/
  have htranspose : P.formalTranspose.toLinearMap = Q.formalTranspose.toLinearMap := by
    apply IsFormalTranspose.unique P.toLinearMap P.formalTranspose.toLinearMap
      Q.formalTranspose.toLinearMap P.isFormalTranspose_formalTransposeLinearMap
    rw [hPQ]
    exact Q.isFormalTranspose_formalTransposeLinearMap
  apply LinearMap.ext
  intro D
  apply ContinuousLinearMap.ext
  intro α
  rw [distributionExtension_apply, distributionExtension_apply, htranspose]

end PseudodifferentialOperator

end AtiyahSinger

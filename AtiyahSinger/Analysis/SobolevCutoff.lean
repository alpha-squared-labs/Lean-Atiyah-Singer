/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialCutoff
public import AtiyahSinger.Analysis.SobolevLocalComparison
public import AtiyahSinger.Analysis.ZeroOrderBundleMap

/-!
# Smooth cutoffs in actual Sobolev completions

Public module ID: M0993.

Smooth scalar multiplication is an order-zero operator on the original sections.
Compactly supported local regularity gives a higher-order lift after multiplication,
using the same chart extension maps in the two actual Sobolev completions.
These standard localization facts are used in the global PDO local mapping theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 15

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hμ

/-- Smooth scalar multiplication is an order-zero PDO with its original section action. -/
theorem isPseudodifferentialOperator_smoothSectionMul
    (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f) :
    IsPseudodifferentialOperator (n := n) (r := r) (q := r) E E μ 0
      (smoothSectionMul E f hf) := by
  -- In the original frames, the scalar multiplies their smooth transition columns.
  have ha : IsSmoothBundleMap (n := n) (r := r) (q := r)
      (fun x ↦ f x • (LinearMap.id : E x →ₗ[ℂ] E x)) := by
    intro e he g hg j
    let := he
    let := hg
    have hcolumn := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace.single j 1)).restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e g)
    have hsmul : ContDiff ℝ ∞
        (fun z : ℂ × EuclideanSpace ℂ (Fin r) ↦ z.1 • z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
    apply (hsmul.contMDiff.comp_contMDiffOn
      (hf.contMDiffOn.prodMk_space hcolumn)).congr
    intro x hx
    change (g ⟨x, f x • e.symmL ℂ x (EuclideanSpace.single j 1)⟩).2 = _
    rw [(g.linear ℂ hx.2).2]
    congr 1
    change (g ⟨x, e.symmL ℂ x (EuclideanSpace.single j 1)⟩).2 =
      e.coordChangeL ℂ g x (EuclideanSpace.single j 1)
    rw [e.coordChangeL_apply g hx, e.symmL_apply hx.1]
  let D : DifferentialOperator (n := n) (r := r) (q := r) E E 0 :=
    { toLinearMap := smoothSectionMap _ ha
      isDifferentialOperator := isDifferentialOperator_smoothSectionMap _ ha }
  -- The derived differential operator acts by exactly the specified multiplier.
  have hD : D.toLinearMap = smoothSectionMul E f hf := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    rfl
  simpa only [Nat.cast_zero, hD] using D.isPseudodifferentialOperator (μ := μ)


omit hC hμ [MeasurableSpace M] [BorelSpace M] in
/-- A smooth cutoff supported in the regular set has a genuine higher Sobolev lift.
The supplied bounded map is required to act by that same scalar on smooth sections. -/
theorem SmoothBundlePresentation.exists_sobolev_lift_of_cutoff
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (s t : ℝ) (hst : s ≤ t) (u : A.SobolevSpace s) (U : Set M)
    (hu : A.MemSobolevOn s u t U)
    (ψ : M → ℝ) (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (hsψ : tsupport ψ ⊆ U) (T : A.SobolevSpace s →L[ℂ] A.SobolevSpace s)
    (hT : ∀ v : smoothSections (n := n) (r := r) E,
      T (A.smoothToSobolev s v) = A.smoothToSobolev s
        (smoothSectionMul E (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ) v)) :
    ∃! v : A.SobolevSpace t, A.sobolevInclusion t s hst v = T u := by
  /- In each original chart, multiply by the same scalar and a plateau equal to
  one on its fixed localization support. The local hypothesis gives global H^t
  for these compact coordinate distributions. The whole-base lift theorem then
  reconstructs an element of the actual completion, with uniqueness by inclusion. -/
  classical
  apply (A.memSobolevOn_univ_iff_exists_sobolev_lift s t hst (T u)).mp
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let K (j : Fin A.size) := (A.chart j) '' tsupport (A.cutoff j)
  let W (j : Fin A.size) :=
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.frame j).baseSet
  have hK (j : Fin A.size) : IsCompact (K j) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  have hU (j : Fin A.size) : IsOpen (W j) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage
      (A.chart j).open_target (A.frame j).open_baseSet
  have hKU (j : Fin A.size) : K j ⊆ W j := by
    rintro _ ⟨x, hx, rfl⟩
    have hs := (A.support_subset j hx).1
    refine ⟨(A.chart j).map_source hs, ?_⟩
    change (A.chart j).symm ((A.chart j) x) ∈ (A.frame j).baseSet
    rw [(A.chart j).left_inv hs]
    exact (A.support_subset j hx).2
  have hplateau (j : Fin A.size) : ∃ η : X → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ W j ∧
        ∀ z ∈ K j, η z = 1 := by
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure (hK j) (hU j) (hKU j)
    obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo (hK j).isClosed hKO
    have hs : tsupport η = closure O := congrArg closure hsη
    refine ⟨η, hη, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs], ?_⟩
    exact fun z hz ↦ (honeη z).mp hz
  choose η hη hcη hsη honeη using hplateau
  let L (j : Fin A.size) : BundleChartCutoff (r := r) E (A.chart j) :=
    { frame := A.frame j
      frame_mem_atlas := A.frame_mem_atlas j
      cutoff := η j
      smooth_cutoff := hη j
      compact_support := hcη j
      support_subset := hsη j }
  intro j
  let θ := (L j).mulSmooth (A.chart_mem_atlas j) ψ hψ
  -- The multiplied chart cutoff is supported in the requested coordinate open set.
  let Kψ := ((A.chart j).symm '' tsupport (η j)) ∩ tsupport ψ
  have hKbase : IsCompact ((A.chart j).symm '' tsupport (η j)) :=
    (hcη j).image_of_continuousOn ((A.chart j).continuousOn_symm.mono
      (fun z hz ↦ (hsη j hz).1))
  have hKψ : IsCompact Kψ := hKbase.inter_right (isClosed_tsupport _)
  have hKsource : Kψ ⊆ (A.chart j).source := by
    rintro _ ⟨⟨z, hz, rfl⟩, _⟩
    exact (A.chart j).map_target (hsη j hz).1
  have hsupport : tsupport θ.cutoff ⊆ (A.chart j) '' Kψ := by
    apply closure_minimal ?_
      (hKψ.image_of_continuousOn ((A.chart j).continuousOn.mono hKsource)).isClosed
    intro z hz
    change η j z * ψ ((A.chart j).symm z) ≠ 0 at hz
    have hne := mul_ne_zero_iff.mp hz
    have hzη := subset_tsupport (η j) hne.1
    exact ⟨(A.chart j).symm z, ⟨⟨z, hzη, rfl⟩, subset_tsupport ψ hne.2⟩,
      (A.chart j).right_inv (hsη j hzη).1⟩
  have hθU : tsupport θ.cutoff ⊆ (A.chart j) '' (U ∩ (A.chart j).source) := by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := hsupport hz
    exact ⟨x, ⟨hsψ hx.2, hKsource hx⟩, rfl⟩
  have hgrowth : (fun z ↦ (θ.cutoff z : ℂ)).HasTemperateGrowth :=
    (θ.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp θ.smooth_cutoff)
  -- The coordinate multiplier agrees on smooth sections; continuity retains this equality.
  have hlocal (v : smoothSections (n := n) (r := r) E) :
      A.localize j
        (smoothSectionMul E (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ) v) =
      SchwartzMap.smulLeftCLM V (fun z ↦ (θ.cutoff z : ℂ)) (A.localize j v) := by
    apply SchwartzMap.ext
    intro z
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
    by_cases hz : z ∈ (A.chart j).target
    · change A.localizedFunction j _ z = (θ.cutoff z : ℂ) • A.localizedFunction j v z
      simp only [SmoothBundlePresentation.localizedFunction, ite_eq_left hz, sectionInChart]
      by_cases hχ : A.cutoff j ((A.chart j).symm z) = 0
      · simp [hχ]
      · have hx := subset_tsupport (A.cutoff j) hχ
        have hηz : η j z = 1 := honeη j z
          ⟨(A.chart j).symm z, hx, (A.chart j).right_inv hz⟩
        have hθz : θ.cutoff z = ψ ((A.chart j).symm z) := by
          change η j z * ψ ((A.chart j).symm z) = _
          rw [hηz, one_mul]
        let := A.frame_mem_atlas j
        change (A.cutoff j ((A.chart j).symm z) : ℂ) •
          (A.frame j ⟨(A.chart j).symm z,
            (ψ ((A.chart j).symm z) : ℂ) • v.val ((A.chart j).symm z)⟩).2 = _
        rw [((A.frame j).linear ℂ (A.support_subset j hx).2).2, hθz]
        exact smul_comm _ _ _
    · simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction, hz]
  have hdist : A.localDistribution s j (T u) =
      TemperedDistribution.smulLeftCLM V (fun z ↦ (θ.cutoff z : ℂ))
        (A.localDistribution s j u) := by
    have hcont : Continuous (A.localDistribution s j) :=
      (besselRealization n r s).continuous.comp
        ((PiLp.proj (𝕜 := ℂ) 2 _ j).continuous.comp continuous_subtype_val)
    refine (A.denseRange_smoothToSobolev s).induction_on u
      (isClosed_eq (hcont.comp T.continuous)
        ((TemperedDistribution.smulLeftCLM V _).continuous.comp hcont)) ?_
    intro v
    rw [hT, A.localDistribution_smoothToSobolev, A.localDistribution_smoothToSobolev, hlocal]
    ext1 φ
    change (∫ z, φ z • (SchwartzMap.smulLeftCLM V
      (fun z ↦ (θ.cutoff z : ℂ)) (A.localize j v)) z) =
      ∫ z, (SchwartzMap.smulLeftCLM ℂ (fun z ↦ (θ.cutoff z : ℂ)) φ) z • A.localize j v z
    simp only [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
    apply integral_congr_ae
    filter_upwards with z
    rw [smul_smul, smul_eq_mul, mul_comm]
  rw [hdist]
  exact memSobolevOn_of_memSobolev _ t
    (hu j θ.cutoff θ.smooth_cutoff θ.compact_support hθU) _

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSmoothKernel
public import AtiyahSinger.Analysis.DualSobolev
public import AtiyahSinger.Analysis.DualSobolevBridge
public import AtiyahSinger.Analysis.OperatorValuedRegularity
public import AtiyahSinger.Analysis.SobolevLocalRegularity
public import AtiyahSinger.Analysis.SmoothSectionMultiplication
public import AtiyahSinger.Geometry.ChartLocalization
public import AtiyahSinger.Geometry.SmoothKernel

/-!
# Smooth kernels improve every Sobolev order

Public module ID: M0986.

A05, with the smooth-kernel part of D05/A02. On a closed base, integration against
an everywhere smooth kernel has a unique bounded realization H^s(E) -> H^t(F)
for arbitrary real s and t. These realizations agree under the natural inclusions,
have one common actual smooth output and are compact. The proof constructs this
output through the compatible finite-order section embeddings. The geometric
covector-row pairing follows by continuous evaluation and density of smooth inputs.

The standard kernel characterization defines IsSmoothingOperator on smooth sections.
Conversely, improvement of every Sobolev order reconstructs the original smooth kernel
through compatible covector rows and joint operator-valued evaluation regularity.
Comparison with order minus infinity is separate from this kernel
characterization.
Sources: SG III.3 p.186 (3.17) and III.5 p.192; Taylor II.2 and II.6. No Hermitian
metric, ellipticity, or relation between s and t is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

section KernelCoordinates

/- Chart cutoffs transport the partitioned bundle integral to compact Euclidean kernels. -/

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

omit [T2Space M] [SecondCountableTopology M] in
open Classical in
private theorem coordinate_cutoff_exists
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
    (hcompact : HasCompactSupport χ) (hsupp : tsupport χ ⊆ c.source) :
    ∃ b : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ c '' tsupport χ ∧
        ∀ z, b z = if z ∈ c.target then χ (c.symm z) else 0 := by
  classical
  let K := c '' tsupport χ
  let b : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z ↦ if z ∈ c.target then χ (c.symm z) else 0
  have hK : IsCompact K := hcompact.image_of_continuousOn
    (c.continuousOn.mono hsupp)
  have hsub : tsupport b ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    have htarget : z ∈ c.target := by
      by_contra h
      exact hz (by simp [b, h])
    have hx : c.symm z ∈ tsupport χ := by
      by_contra h
      exact hz (by simp [b, htarget, image_eq_zero_of_notMem_tsupport h])
    exact ⟨c.symm z, hx, c.right_inv htarget⟩
  refine ⟨b, ?_, hK.of_isClosed_subset (isClosed_tsupport _) hsub, hsub, fun _ ↦ rfl⟩
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ K
  · obtain ⟨x, hx, rfl⟩ := hz
    have htarget := c.map_source (hsupp hx)
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) htarget
    have hlocal := (hχ.contMDiffAt.comp (c x) hchart).contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds htarget] with y hy
    simp [b, hy]
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hsub h))

private theorem compact_cutoff_one {K U : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧ ∀ x ∈ K, ψ x = 1 := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ψ, hψ, _, hs, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hVo hK.isClosed hKV
  have hts : tsupport ψ = closure V := congrArg closure hs
  refine ⟨ψ, hψ, ?_, ?_, fun x hx ↦ (hone x).mp hx⟩
  · change IsCompact (tsupport ψ)
    rw [hts]
    exact hVc
  · rw [hts]
    exact hVU

private theorem contDiff_smul_of_tsupport_subset
    {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set X} (hU : IsOpen U) (g : X → ℝ) (hg : ContDiff ℝ ∞ g)
    (hsub : tsupport g ⊆ U) (f : X → H) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x ↦ g x • f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport g
  · exact hg.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsub hx)))
  · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] in
private theorem integral_chart_of_smooth_density
    [MeasurableSpace M] [BorelSpace M]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (μ : Measure M)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContinuousOn w c.target)
    (hpos : ∀ z ∈ c.target, 0 ≤ w z)
    (hmap : Measure.map c (μ.restrict c.source) =
      (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
    (f : M → H) (g : EuclideanSpace ℝ (Fin n) → H) (hg : StronglyMeasurable g)
    (heq : ∀ x ∈ c.source, g (c x) = f x)
    (hzero : ∀ x, x ∉ c.source → f x = 0) :
    (∫ x, f x ∂μ) = ∫ z in c.target, w z • g z := by
  have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
    ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
      |>.aemeasurable c.open_target.measurableSet
  calc
    (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in c.source, g (c x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
      exact (heq x hx).symm
    _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
      (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
        hg.aestronglyMeasurable).symm
    _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
      rw [hmap]
      exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
        (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
    _ = ∫ z in c.target, w z • g z := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      rw [ENNReal.toReal_ofReal (hpos z hz)]

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

private theorem exists_kernel_localization
    (K : SmoothKernel (n := n) (r := r) (q := q) E F)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (i : Fin B.size) (j : Fin A.size) :
    ∃ k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q),
      ContDiff ℝ ∞ (Function.uncurry k) ∧ HasCompactSupport (Function.uncurry k) ∧
        ∀ (u : smoothSections (n := n) (r := r) E) (x : EuclideanSpace ℝ (Fin n)),
          B.localize i (K.toLinearMap μ
            (smoothSectionMul E (fun y ↦ (A.cutoff j y : ℂ))
              (Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff j)) u)) x =
            ∫ y, k x y (A.localize j u y) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let c := A.chart j
  let d := B.chart i
  let e := A.frame j
  let f := B.frame i
  let : MemTrivializationAtlas e := A.frame_mem_atlas j
  let : MemTrivializationAtlas f := B.frame_mem_atlas i
  let U := d.target ∩ d.symm ⁻¹' f.baseSet
  let V := c.target ∩ c.symm ⁻¹' e.baseSet
  have hU : IsOpen U := d.isOpen_inter_preimage_symm f.open_baseSet
  have hV : IsOpen V := c.isOpen_inter_preimage_symm e.open_baseSet
  obtain ⟨b, hb, hbc, hbsub, hbval⟩ := coordinate_cutoff_exists d (B.chart_mem_atlas i)
    (B.cutoff i) (B.smooth_cutoff i) (B.compact_support i)
    (fun x hx ↦ (B.support_subset i hx).1)
  have hbU : tsupport b ⊆ U := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hbsub hz
    have hs := B.support_subset i hx
    refine ⟨d.map_source hs.1, ?_⟩
    change d.symm (d x) ∈ f.baseSet
    rw [d.left_inv hs.1]
    exact hs.2
  have hAc : IsCompact (c '' tsupport (A.cutoff j)) :=
    (A.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  have hAV : c '' tsupport (A.cutoff j) ⊆ V := by
    rintro z ⟨x, hx, rfl⟩
    have hs := A.support_subset j hx
    refine ⟨c.map_source hs.1, ?_⟩
    change c.symm (c x) ∈ e.baseSet
    rw [c.left_inv hs.1]
    exact hs.2
  obtain ⟨ψ, hψ, hψc, hψV, hψone⟩ := compact_cutoff_one hAc hV hAV
  obtain ⟨w, hw, hwpos, hwmap⟩ :=
    IsSmoothPositiveMeasure.exists_smooth_density (μ := μ) c (A.chart_mem_atlas j)
  let a : X × X → H := fun z ↦
    kernelInFrames E F K.toFun e f (d.symm z.1, c.symm z.2)
  -- The original kernel is smooth on the exact pair of chart/frame domains.
  have ha : ContDiffOn ℝ ∞ a (U ×ˢ V) := by
    have hd := contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) (B.chart_mem_atlas i))
    have hc := contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) (A.chart_mem_atlas j))
    have hh := (K.isSmooth e f).comp
      ((hd.comp contMDiffOn_fst (fun _ (hz : _ ∈ U ×ˢ V) ↦ hz.1.1)).prodMk
        (hc.comp contMDiffOn_snd (fun _ (hz : _ ∈ U ×ˢ V) ↦ hz.2.1)))
      (fun _ (hz : _ ∈ U ×ˢ V) ↦ ⟨hz.1.2, hz.2.2⟩)
    apply contMDiffOn_iff_contDiffOn.mp
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hh
  let g : X × X → ℝ := fun z ↦ b z.1 * ψ z.2
  have hg : ContDiff ℝ ∞ g := (hb.comp contDiff_fst).mul (hψ.comp contDiff_snd)
  have hgs : tsupport g ⊆ tsupport b ×ˢ tsupport ψ := by
    apply closure_minimal _ ((isClosed_tsupport b).prod (isClosed_tsupport ψ))
    intro z hz
    have hne : b z.1 ≠ 0 ∧ ψ z.2 ≠ 0 := mul_ne_zero_iff.mp hz
    exact ⟨subset_tsupport b hne.1, subset_tsupport ψ hne.2⟩
  let k : X → X → H := fun x y ↦ (b x * ψ y) • (w y • a (x, y))
  have hkd : ContDiff ℝ ∞ (Function.uncurry k) := by
    exact contDiff_smul_of_tsupport_subset (hU.prod hV) g hg
      (hgs.trans (Set.prod_mono hbU hψV)) _
      ((hw.comp contDiffOn_snd (fun _ hz ↦ hz.2.1)).smul ha)
  have hkc : HasCompactSupport (Function.uncurry k) := by
    apply (hbc.prod hψc).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ ((isClosed_tsupport b).prod (isClosed_tsupport ψ))
    intro z hz
    by_contra h
    rcases not_and_or.mp h with h | h
    · exact hz (by simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport h])
    · exact hz (by simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport h])
  refine ⟨k, hkd, hkc, ?_⟩
  intro u x
  let uj := smoothSectionMul E (fun y ↦ (A.cutoff j y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff j)) u
  have huj (y : M) : uj.val y = (A.cutoff j y : ℂ) • u.val y := rfl
  by_cases hbx : b x = 0
  · have hleft : B.localize i (K.toLinearMap μ uj) x = 0 := by
      change (if x ∈ d.target then (B.cutoff i (d.symm x) : ℂ) •
        sectionInChart F d f (K.toLinearMap μ uj).val x else 0) = 0
      by_cases hx : x ∈ d.target
      · have hzero : B.cutoff i (d.symm x) = 0 := by simpa [hbval, hx] using hbx
        simp [hx, hzero]
      · simp [hx]
    change B.localize i (K.toLinearMap μ uj) x = _
    rw [hleft]
    simp [k, hbx]
  have hx : x ∈ U := hbU (subset_tsupport b hbx)
  let : NormedSpace ℝ (F (d.symm x)) := NormedSpace.restrictScalars ℝ ℂ _
  let : CompleteSpace (F (d.symm x)) :=
    VectorBundle.completeSpace ℂ (EuclideanSpace ℂ (Fin q)) F (d.symm x)
  have hout : B.localize i (K.toLinearMap μ uj) x =
      b x • ∫ y, f.continuousLinearMapAt ℂ (d.symm x)
        (K.toFun (d.symm x) y (uj.val y)) ∂μ := by
    change (if x ∈ d.target then (B.cutoff i (d.symm x) : ℂ) •
      sectionInChart F d f (K.toLinearMap μ uj).val x else 0) = _
    rw [ite_eq_left hx.1]
    change (B.cutoff i (d.symm x) : ℂ) •
      (f ⟨d.symm x, K.apply μ uj (d.symm x)⟩).2 = _
    rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx.2]
    have hbvalue : B.cutoff i (d.symm x) = b x := by simpa only [ite_eq_left hx.1] using
      (hbval x).symm
    rw [hbvalue, Complex.coe_smul]
    congr 1
    exact ((f.continuousLinearMapAt ℂ (d.symm x)).integral_comp_comm
      (K.integrable_apply μ uj (d.symm x))).symm
  let G : X → EuclideanSpace ℂ (Fin q) :=
    fun y ↦ ψ y • (b x • a (x, y) (A.localize j u y))
  have hG : ContDiff ℝ ∞ G := by
    have har : ContDiffOn ℝ ∞ (fun y ↦ a (x, y)) V :=
      ha.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy ↦ ⟨hx, hy⟩)
    have hev : ContDiff ℝ ∞ (fun z : H × EuclideanSpace ℂ (Fin r) ↦ z.1 z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    apply contDiff_smul_of_tsupport_subset hV ψ hψ hψV
    exact (hev.comp_contDiffOn (har.prodMk (A.localize j u).smooth'.contDiffOn)).const_smul _
  have hcoords (y : M) (hy : y ∈ c.source) :
      G (c y) = b x • f.continuousLinearMapAt ℂ (d.symm x)
        (K.toFun (d.symm x) y (uj.val y)) := by
    have htarget := c.map_source hy
    have hcy : c.symm (c y) = y := c.left_inv hy
    by_cases hcut : A.cutoff j y = 0
    · have hlocalzero : A.localize j u (c y) = 0 := by
        change (if c y ∈ c.target then (A.cutoff j (c.symm (c y)) : ℂ) •
          sectionInChart E c e u.val (c y) else 0) = 0
        rw [ite_eq_left htarget, hcy, hcut]
        simp
      simp [G, hlocalzero, huj, hcut]
    have hys := A.support_subset j (subset_tsupport _ hcut)
    have hlocal : A.localize j u (c y) =
        (A.cutoff j y : ℂ) • e.continuousLinearMapAt ℂ y (u.val y) := by
      change (if c y ∈ c.target then (A.cutoff j (c.symm (c y)) : ℂ) •
        sectionInChart E c e u.val (c y) else 0) = _
      rw [ite_eq_left htarget]
      have hpair :
          (⟨c.symm (c y), u.val (c.symm (c y))⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨y, u.val y⟩ :=
        congrArg (fun z ↦ (⟨z, u.val z⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin r)) E)) hcy
      simp only [sectionInChart, hpair, hcy]
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hys.2]
    have hψvalue : ψ (c y) = 1 := hψone _ ⟨y, subset_tsupport _ hcut, rfl⟩
    simp only [G, hψvalue, one_smul, hlocal, a, hcy, huj]
    change b x • (f.continuousLinearMapAt ℂ (d.symm x)
      (K.toFun (d.symm x) y (e.symmL ℂ y
        ((A.cutoff j y : ℂ) • e.continuousLinearMapAt ℂ y (u.val y))))) = _
    rw [map_smul, e.symmL_continuousLinearMapAt hys.2]
  have hzero (y : M) (hy : y ∉ c.source) :
      b x • f.continuousLinearMapAt ℂ (d.symm x)
        (K.toFun (d.symm x) y (uj.val y)) = 0 := by
    have hcut : A.cutoff j y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (A.support_subset j h).1)
    simp [huj, hcut]
  change B.localize i (K.toLinearMap μ uj) x = _
  rw [hout, ← integral_smul]
  rw [integral_chart_of_smooth_density c μ w hw.continuousOn
    (fun z hz ↦ (hwpos z hz).le) hwmap _ G hG.continuous.stronglyMeasurable hcoords hzero]
  have houtside (y : X) (hy : y ∉ c.target) : w y • G y = 0 := by
    have hψzero : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hψV h).1)
    simp [G, hψzero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [G, k, smul_apply, smul_smul]
  congr 1
  ring

/-- Two specified chart cutoffs turn the actual smooth kernel action into a compact smooth
Euclidean kernel, with the original input density absorbed into its second variable. -/
theorem SmoothKernel.exists_bundleChartCutoff_kernel
    (K : SmoothKernel (n := n) (r := r) (q := q) E F)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F d) :
    ∃ k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q),
      ContDiff ℝ ∞ (Function.uncurry k) ∧ HasCompactSupport (Function.uncurry k) ∧
        ∀ (u : SchwartzMap (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ (Fin r))) x,
          B.localize hd (K.toLinearMap μ (A.extend hc u)) x = ∫ y, k x y (u y) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let e := A.frame
  let f := B.frame
  let : MemTrivializationAtlas e := A.frame_mem_atlas
  let : MemTrivializationAtlas f := B.frame_mem_atlas
  let U := d.target ∩ d.symm ⁻¹' f.baseSet
  let V := c.target ∩ c.symm ⁻¹' e.baseSet
  have hU : IsOpen U := d.isOpen_inter_preimage_symm f.open_baseSet
  have hV : IsOpen V := c.isOpen_inter_preimage_symm e.open_baseSet
  obtain ⟨w, hw, hwpos, hwmap⟩ :=
    IsSmoothPositiveMeasure.exists_smooth_density (μ := μ) c hc
  let a : X × X → H := fun z ↦
    kernelInFrames E F K.toFun e f (d.symm z.1, c.symm z.2)
  -- Use these exact two charts and frames for the given kernel, with no change of measure.
  have ha : ContDiffOn ℝ ∞ a (U ×ˢ V) := by
    have hd' := contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) hd)
    have hc' := contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) hc)
    have h := (K.isSmooth e f).comp
      ((hd'.comp contMDiffOn_fst (fun _ (hz : _ ∈ U ×ˢ V) ↦ hz.1.1)).prodMk
        (hc'.comp contMDiffOn_snd (fun _ (hz : _ ∈ U ×ˢ V) ↦ hz.2.1)))
      (fun _ (hz : _ ∈ U ×ˢ V) ↦ ⟨hz.1.2, hz.2.2⟩)
    apply contMDiffOn_iff_contDiffOn.mp
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  let g : X × X → ℝ := fun z ↦ B.cutoff z.1 * A.cutoff z.2
  have hg : ContDiff ℝ ∞ g :=
    (B.smooth_cutoff.comp contDiff_fst).mul (A.smooth_cutoff.comp contDiff_snd)
  have hgs : tsupport g ⊆ tsupport B.cutoff ×ˢ tsupport A.cutoff := by
    apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro z hz
    have hne : B.cutoff z.1 ≠ 0 ∧ A.cutoff z.2 ≠ 0 := mul_ne_zero_iff.mp hz
    exact ⟨subset_tsupport _ hne.1, subset_tsupport _ hne.2⟩
  let k : X → X → H := fun x y ↦ (B.cutoff x * A.cutoff y) • (w y • a (x, y))
  have hkd : ContDiff ℝ ∞ (Function.uncurry k) :=
    contDiff_smul_of_tsupport_subset (hU.prod hV) g hg
      (hgs.trans (Set.prod_mono B.support_subset A.support_subset)) _
      ((hw.comp contDiffOn_snd (fun _ hz ↦ hz.2.1)).smul ha)
  have hkc : HasCompactSupport (Function.uncurry k) := by
    apply (B.compact_support.prod A.compact_support).of_isClosed_subset
      (isClosed_tsupport _)
    apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro z hz
    by_contra h
    rcases not_and_or.mp h with h | h
    · exact hz (by simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport h])
    · exact hz (by simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport h])
  refine ⟨k, hkd, hkc, ?_⟩
  intro u x
  let v := A.extend hc u
  by_cases hbx : B.cutoff x = 0
  · have hleft : B.localize hd (K.toLinearMap μ v) x = 0 := by
      change B.localizedFunction (K.toLinearMap μ v) x = 0
      simp [BundleChartCutoff.localizedFunction, hbx]
    rw [hleft]
    simp [k, hbx]
  have hx : x ∈ U := B.support_subset (subset_tsupport _ hbx)
  let : NormedSpace ℝ (F (d.symm x)) := NormedSpace.restrictScalars ℝ ℂ _
  let : CompleteSpace (F (d.symm x)) :=
    VectorBundle.completeSpace ℂ (EuclideanSpace ℂ (Fin q)) F (d.symm x)
  have hout : B.localize hd (K.toLinearMap μ v) x =
      B.cutoff x • ∫ y, f.continuousLinearMapAt ℂ (d.symm x)
        (K.toFun (d.symm x) y (v.val y)) ∂μ := by
    change (if x ∈ d.target then (B.cutoff x : ℂ) •
      sectionInChart F d f (K.toLinearMap μ v).val x else 0) = _
    rw [ite_eq_left hx.1]
    change (B.cutoff x : ℂ) • (f ⟨d.symm x, K.apply μ v (d.symm x)⟩).2 = _
    rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx.2, Complex.coe_smul]
    congr 1
    exact ((f.continuousLinearMapAt ℂ (d.symm x)).integral_comp_comm
      (K.integrable_apply μ v (d.symm x))).symm
  let G : X → EuclideanSpace ℂ (Fin q) :=
    fun y ↦ A.cutoff y • (B.cutoff x • a (x, y) (u y))
  have hG : ContDiff ℝ ∞ G := by
    have har : ContDiffOn ℝ ∞ (fun y ↦ a (x, y)) V :=
      ha.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy ↦ ⟨hx, hy⟩)
    have hev : ContDiff ℝ ∞ (fun z : H × EuclideanSpace ℂ (Fin r) ↦ z.1 z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    exact contDiff_smul_of_tsupport_subset hV A.cutoff A.smooth_cutoff A.support_subset
      _ ((hev.comp_contDiffOn (har.prodMk u.smooth'.contDiffOn)).const_smul _)
  -- Move the actual integral through its chart density. The cutoff extension is zero
  -- outside this source, so no contribution is lost by restricting the integral.
  have hcoords (y : M) (hy : y ∈ c.source) :
      G (c y) = B.cutoff x • f.continuousLinearMapAt ℂ (d.symm x)
        (K.toFun (d.symm x) y (v.val y)) := by
    have hcy : c.symm (c y) = y := c.left_inv hy
    have hv : v.val y = (A.cutoff (c y) : ℂ) • e.symmL ℂ y (u (c y)) := by
      simp only [v, BundleChartCutoff.extend, BundleChartCutoff.extendedFunction,
        ite_eq_left hy]
      rfl
    change A.cutoff (c y) • B.cutoff x • f.continuousLinearMapAt ℂ (d.symm x)
      (K.toFun (d.symm x) (c.symm (c y)) (e.symmL ℂ (c.symm (c y)) (u (c y)))) = _
    rw [hcy, hv, map_smul, map_smul, Complex.coe_smul]
    exact smul_comm _ _ _
  have hzero (y : M) (hy : y ∉ c.source) :
      B.cutoff x • f.continuousLinearMapAt ℂ (d.symm x)
        (K.toFun (d.symm x) y (v.val y)) = 0 := by
    have hv : v.val y = 0 := by
      simp only [v, BundleChartCutoff.extend, BundleChartCutoff.extendedFunction,
        ite_eq_right hy]
    simp [hv]
  rw [hout, ← integral_smul]
  rw [integral_chart_of_smooth_density c μ w hw.continuousOn
    (fun z hz ↦ (hwpos z hz).le) hwmap _ G hG.continuous.stronglyMeasurable hcoords hzero]
  have houtside (y : X) (hy : y ∉ c.target) : w y • G y = 0 := by
    have hyzero : A.cutoff y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hy (A.support_subset h).1)
    simp [G, hyzero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [G, k, smul_apply, smul_smul]
  congr 1
  ring

end KernelCoordinates

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace SmoothKernel

variable (K : SmoothKernel (n := n) (r := r) (q := q) E F)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- A smooth kernel gives estimates between any two real Sobolev orders. -/
theorem exists_norm_smoothToSobolev_apply_le (s t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      ‖B.smoothToSobolev t (K.toLinearMap μ u)‖ ≤ C * ‖A.smoothToSobolev s u‖ := by
  /- Stage 1: insert finite input and output partitions, write the actual kernel
  in frames, and absorb the smooth density into its input variable. The localized
  kernels extend by zero to compactly supported smooth matrices in both variables.
  Stage 2: the Euclidean compact-kernel estimate bounds its differentiated rows
  in H^(-s), uses the exact opposite-order Bessel pairing, and controls the finite
  target Schwartz seminorm family. Sum the original partition pieces and their
  output coordinate bounds in the specified finite Hilbert norm. No presentation
  comparison, inequality between s and t, or ellipticity is used. -/
  classical
  have hlocal : ∀ (i : Fin B.size) (j : Fin A.size), ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖schwartzSobolevCoordinate t (B.localize i (K.toLinearMap μ
          (smoothSectionMul E (fun y ↦ (A.cutoff j y : ℂ))
            (Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff j)) u)))‖ ≤
          C * ‖schwartzSobolevCoordinate s (A.localize j u)‖ := by
    intro i j
    obtain ⟨k, hk, hc, heq⟩ := exists_kernel_localization K μ A B i j
    obtain ⟨C, hC, hbound⟩ := compact_smooth_kernel_sobolev_bound k hk hc s t
    refine ⟨C, hC, ?_⟩
    intro u
    exact hbound (A.localize j u)
      (B.localize i (K.toLinearMap μ (smoothSectionMul E
        (fun y ↦ (A.cutoff j y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff j)) u))) (heq u)
  choose C hC hbound using hlocal
  let D : ℝ := ∑ i, ∑ j, C i j
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hC i j))
  refine ⟨D + 1, by positivity, ?_⟩
  intro u
  let uj (j : Fin A.size) := smoothSectionMul E (fun y ↦ (A.cutoff j y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff j)) u
  -- The pieces use the original partition, hence their sum is the original section.
  have hsum : ∑ j, uj j = u := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ j, (A.cutoff j x : ℂ) • u.val x) = u.val x
    rw [← Finset.sum_smul]
    have hcut : ∑ j, (A.cutoff j x : ℂ) = 1 := by exact_mod_cast A.sum_cutoff x
    rw [hcut, one_smul]
  have hinput (j : Fin A.size) :
      ‖schwartzSobolevCoordinate s (A.localize j u)‖ ≤ ‖A.smoothToSobolev s u‖ :=
    PiLp.norm_apply_le (A.sobolevCoordinates s u) j
  -- Linearity allows each output coordinate to be estimated before the finite sum.
  have hout (i : Fin B.size) :
      ‖schwartzSobolevCoordinate t (B.localize i (K.toLinearMap μ u))‖ ≤
        (∑ j, C i j) * ‖A.smoothToSobolev s u‖ := by
    let L := (schwartzSobolevCoordinateLinearMap n q t).comp
      ((B.localizeLinearMap i).comp (K.toLinearMap μ))
    change ‖L u‖ ≤ _
    have hLu := congrArg L hsum
    rw [map_sum] at hLu
    rw [← hLu]
    calc
      ‖∑ j, L (uj j)‖ ≤ ∑ j, ‖L (uj j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, C i j * ‖A.smoothToSobolev s u‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (hbound i j u).trans (mul_le_mul_of_nonneg_left (hinput j) (hC i j))
      _ = (∑ j, C i j) * ‖A.smoothToSobolev s u‖ := (Finset.sum_mul _ _ _).symm
  -- The finite Hilbert norm is bounded by the sum of its coordinate norms.
  have hnorm : ‖B.smoothToSobolev t (K.toLinearMap μ u)‖ ≤
      ∑ i, ‖schwartzSobolevCoordinate t (B.localize i (K.toLinearMap μ u))‖ := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun (i : Fin B.size) _ ↦ norm_nonneg
        (schwartzSobolevCoordinate t (B.localize i (K.toLinearMap μ u))))
    rw [← B.norm_smoothToSobolev_sq] at hsq
    have hnonneg : 0 ≤ ∑ i, ‖schwartzSobolevCoordinate t
        (B.localize i (K.toLinearMap μ u))‖ := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
    nlinarith [norm_nonneg (B.smoothToSobolev t (K.toLinearMap μ u))]
  calc
    ‖B.smoothToSobolev t (K.toLinearMap μ u)‖ ≤
        ∑ i, ‖schwartzSobolevCoordinate t (B.localize i (K.toLinearMap μ u))‖ := hnorm
    _ ≤ ∑ i, (∑ j, C i j) * ‖A.smoothToSobolev s u‖ :=
      Finset.sum_le_sum (fun i _ ↦ hout i)
    _ = D * ‖A.smoothToSobolev s u‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (D + 1) * ‖A.smoothToSobolev s u‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

/-- The kernel action has a unique bounded extension between the specified actual completions. -/
theorem existsUnique_sobolevExtension (s t : ℝ) :
    ∃! T : A.SobolevSpace s →L[ℂ] B.SobolevSpace t,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) = B.smoothToSobolev t (K.toLinearMap μ u) := by
  /- The preceding norm estimate extends the specified linear map from the dense
  smooth image to the complete target Hilbert space. Input injectivity identifies
  that dense image with actual smooth sections. Two continuous extensions agree on
  the dense image, hence everywhere, giving uniqueness with the displayed action. -/
  -- The bound constructs an extension directly from the original dense linear image.
  obtain ⟨C, _, hC⟩ := K.exists_norm_smoothToSobolev_apply_le μ A B s t
  let f := (B.smoothToSobolev t).comp (K.toLinearMap μ)
  let T : A.SobolevSpace s →L[ℂ] B.SobolevSpace t :=
    f.extendOfNorm (A.smoothToSobolev s)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s u) = B.smoothToSobolev t (K.toLinearMap μ u) :=
    LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s) ⟨C, hC⟩ u
  refine ⟨T, hT, ?_⟩
  -- Equality on the same dense smooth sections determines a continuous extension.
  intro R hR
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer R.continuous T.continuous
  funext u
  exact (hR u).trans (hT u).symm

/-- The uniquely specified bounded realization of this actual smooth kernel. -/
def sobolevExtension (s t : ℝ) : A.SobolevSpace s →L[ℂ] B.SobolevSpace t :=
  Classical.choose (K.existsUnique_sobolevExtension μ A B s t).exists

/-- The selected Sobolev realization agrees with the original smooth integral operator. -/
theorem sobolevExtension_smoothToSobolev (s t : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    K.sobolevExtension μ A B s t (A.smoothToSobolev s u) =
      B.smoothToSobolev t (K.toLinearMap μ u) := by
  /- Apply the specifying property of the uniquely chosen extension. The right
  side uses the concrete integral operator on the original section, not a new map. -/
  exact (Classical.choose_spec (K.existsUnique_sobolevExtension μ A B s t).exists) u

/-- Lowering the target order leaves the represented kernel output unchanged. -/
theorem sobolevInclusion_comp_sobolevExtension (s t t' : ℝ) (htt' : t' ≤ t) :
    (B.sobolevInclusion t t' htt').comp (K.sobolevExtension μ A B s t) =
      K.sobolevExtension μ A B s t' := by
  /- Both continuous maps send each smooth input to the same smooth kernel output
  in H^t'. The natural inclusion preserves smooth sections. Density gives equality
  on H^s, including equality of the represented local distributions. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((B.sobolevInclusion t t' htt').comp (K.sobolevExtension μ A B s t)).continuous
    (K.sobolevExtension μ A B s t').continuous
  funext u
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    K.sobolevExtension_smoothToSobolev, B.sobolevInclusion_smoothToSobolev]

/-- Lowering the input order before applying the kernel gives the same output. -/
theorem sobolevExtension_comp_sobolevInclusion (s s' t : ℝ) (hss' : s' ≤ s) :
    (K.sobolevExtension μ A B s' t).comp (A.sobolevInclusion s s' hss') =
      K.sobolevExtension μ A B s t := by
  /- On a smooth input the inclusion retains the actual input section, so both
  extension specifications give its kernel integral. Continuity and smooth density
  extend that equality to every H^s input; no comparison between t and s is needed. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((K.sobolevExtension μ A B s' t).comp (A.sobolevInclusion s s' hss')).continuous
    (K.sobolevExtension μ A B s t).continuous
  funext u
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    A.sobolevInclusion_smoothToSobolev, K.sobolevExtension_smoothToSobolev]

/-- Every Sobolev input has one actual smooth output representing all target-order realizations. -/
theorem existsUnique_sobolevSmoothOutput (s : ℝ) (u : A.SobolevSpace s) :
    ∃! v : smoothSections (n := n) (r := q) F,
      ∀ t : ℝ, K.sobolevExtension μ A B s t u = B.smoothToSobolev t v := by
  classical
  -- Every high Sobolev realization gives an actual finite-order differentiable section.
  let τ (k : ℕ) : ℝ := (n : ℝ) / 2 + k + 1
  have hτ (k : ℕ) : (n : ℝ) / 2 + k < τ k := by dsimp [τ]; linarith
  let T (k : ℕ) : A.SobolevSpace s →L[ℂ] B.CkSectionSpace k :=
    (B.sobolevToCk k (τ k) (hτ k)).comp (K.sobolevExtension μ A B s (τ k))
  -- Lowering C^k to C^0 retains the same section and decreases its actual atlas norm.
  let L (k : ℕ) : B.CkSectionSpace k →L[ℂ] B.CkSectionSpace 0 := by
    let l : B.CkSectionSpace k →ₗ[ℂ] B.CkSectionSpace 0 :=
      { toFun := fun w ↦ ⟨w.val, fun e he ↦ (w.property e he).of_le (by simp)⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    apply l.mkContinuous 1
    intro w
    change B.ckNorm 0 (l w) ≤ 1 * B.ckNorm k w
    rw [one_mul]
    by_cases hsize : B.size = 0
    · have : IsEmpty (Fin B.size) := Fin.isEmpty_iff.mpr hsize
      simp [SmoothBundlePresentation.ckNorm]
    · let i₀ : Fin B.size := ⟨0, Nat.pos_of_ne_zero hsize⟩
      apply csSup_le_csSup (B.bddAbove_ckNorm_values k w)
      · exact ⟨‖iteratedFDeriv ℝ 0 (B.localizedCkFunction 0 i₀ (l w)) 0‖,
          i₀, 0, le_rfl, 0, rfl⟩
      · rintro a ⟨i, j, hj, x, rfl⟩
        exact ⟨i, j, hj.trans (Nat.zero_le k), x, rfl⟩
  have hsame (k : ℕ) : (L k).comp (T k) = T 0 := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer
      ((L k).comp (T k)).continuous (T 0).continuous
    funext v
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, T,
      K.sobolevExtension_smoothToSobolev, B.sobolevToCk_smoothToSobolev]
    rfl
  -- Equality in C^0 identifies all these underlying sections, not merely their distributions.
  have hsmooth : IsSmoothSection (n := n) (r := q) F (T 0 u).val := by
    intro e he
    apply contMDiffOn_infty.mpr
    intro k
    have hval := congrArg (fun w : B.CkSectionSpace 0 ↦ w.val)
      (DFunLike.congr_fun (hsame k) u)
    change (T k u).val = (T 0 u).val at hval
    rw [← hval]
    exact (T k u).property e he
  let v : smoothSections (n := n) (r := q) F := ⟨(T 0 u).val, hsmooth⟩
  have hv (t : ℝ) : K.sobolevExtension μ A B s t u = B.smoothToSobolev t v := by
    -- Compare at a high order through the injective C^0 embedding, then lower to t.
    let a : ℝ := max t (τ 0)
    have ha : (n : ℝ) / 2 + (0 : ℕ) < a := (hτ 0).trans_le (le_max_right t (τ 0))
    let R : A.SobolevSpace s →L[ℂ] B.CkSectionSpace 0 :=
      (B.sobolevToCk 0 a ha).comp (K.sobolevExtension μ A B s a)
    have hR : R = T 0 := by
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev s).equalizer R.continuous (T 0).continuous
      funext w
      simp only [Function.comp_apply, R, T, ContinuousLinearMap.comp_apply,
        K.sobolevExtension_smoothToSobolev, B.sobolevToCk_smoothToSobolev]
    have hhigh : K.sobolevExtension μ A B s a u = B.smoothToSobolev a v := by
      apply B.sobolevToCk_injective 0 a ha
      rw [B.sobolevToCk_smoothToSobolev]
      change R u = B.smoothToCk 0 v
      rw [hR]
      rfl
    have hta : t ≤ a := le_max_left _ _
    have hcompat := DFunLike.congr_fun
      (K.sobolevInclusion_comp_sobolevExtension μ A B s a t hta) u
    rw [ContinuousLinearMap.comp_apply, hhigh, B.sobolevInclusion_smoothToSobolev] at hcompat
    exact hcompat.symm
  refine ⟨v, hv, ?_⟩
  -- The original smooth embedding at one order suffices for uniqueness of the section.
  intro w hw
  apply B.smoothToSobolev_injective 0
  exact (hw 0).symm.trans (hv 0)

/-- The actual smooth output, specified simultaneously in every Sobolev target order. -/
def sobolevToSmooth (s : ℝ) (u : A.SobolevSpace s) : smoothSections (n := n) (r := q) F :=
  Classical.choose (K.existsUnique_sobolevSmoothOutput μ A B s u).exists

/-- Every Sobolev realization is represented by this same actual smooth output. -/
theorem smoothToSobolev_sobolevToSmooth (s t : ℝ) (u : A.SobolevSpace s) :
    B.smoothToSobolev t (K.sobolevToSmooth μ A B s u) =
      K.sobolevExtension μ A B s t u := by
  /- The unique smooth output was selected by its simultaneous realization property.
  Apply that property at the requested real order t and reverse the equality. -/
  exact ((Classical.choose_spec
    (K.existsUnique_sobolevSmoothOutput μ A B s u).exists) t).symm

/-- On smooth inputs the new section output is exactly the original integral section. -/
theorem sobolevToSmooth_smoothToSobolev (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    K.sobolevToSmooth μ A B s (A.smoothToSobolev s u) = K.toLinearMap μ u := by
  /- The smooth extension formula shows that the original integral section satisfies
  all target-order specifications. Uniqueness of the smooth output identifies it
  with the selected section, preserving actual values in each output fiber. -/
  apply B.smoothToSobolev_injective 0
  rw [K.smoothToSobolev_sobolevToSmooth, K.sobolevExtension_smoothToSobolev]

/-- The output value on a covector is the geometric Sobolev pairing with the actual kernel row. -/
theorem dual_sobolevToSmooth (s : ℝ) (u : A.SobolevSpace s)
    (x : M) (α : DualBundle F x) :
    α ((K.sobolevToSmooth μ A B s u).val x) =
      A.sobolevEvaluationPairing μ s (A.dualSmoothToSobolev (-s) (K.dualRow x α)) u := by
  /- On smooth inputs this is dual_apply and the smooth specification of bilinear
  Sobolev duality. Choose t>n/2 so that H^t embeds continuously in C^0; evaluation
  at x is then continuous. Express the left side through the H^t extension and
  pass to the dense smooth limit. The right side is already a continuous functional. -/
  classical
  -- A nonzero partition weight recovers actual point evaluation from one bounded coordinate.
  have hchoose : ∃ j : Fin B.size, B.cutoff j x ≠ 0 := by
    by_contra! h
    have hsum := B.sum_cutoff x
    simp only [h, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨j, hj⟩ := hchoose
  have hx := B.support_subset j (subset_tsupport _ hj)
  let := B.frame_mem_atlas j
  let ev : B.CkSectionSpace 0 →ₗ[ℂ] EuclideanSpace ℂ (Fin q) :=
    { toFun := fun w ↦ (B.cutoff j x : ℂ) •
        ((B.frame j).linearEquivAt ℂ x hx.2) (w.val x)
      map_add' := by
        intro v w
        change (B.cutoff j x : ℂ) •
          ((B.frame j).linearEquivAt ℂ x hx.2) (v.val x + w.val x) = _
        rw [map_add, smul_add]
      map_smul' := by
        intro c w
        change (B.cutoff j x : ℂ) •
          ((B.frame j).linearEquivAt ℂ x hx.2) (c • w.val x) = _
        rw [map_smul, smul_comm]
        rfl }
  have heval (w : B.CkSectionSpace 0) :
      ev w = B.localizedCkFunction 0 j w (B.chart j x) := by
    have hpair : (⟨(B.chart j).symm (B.chart j x),
        w.val ((B.chart j).symm (B.chart j x))⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin q)) F) = ⟨x, w.val x⟩ :=
      congrArg (fun y ↦ (⟨y, w.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin q)) F))
        ((B.chart j).left_inv hx.1)
    simp only [SmoothBundlePresentation.localizedCkFunction,
      ite_eq_left ((B.chart j).map_source hx.1), sectionInChart, hpair,
      (B.chart j).left_inv hx.1]
    rfl
  have hbound (w : B.CkSectionSpace 0) : ‖ev w‖ ≤ 1 * ‖w‖ := by
    rw [one_mul, heval]
    change ‖B.localizedCkFunction 0 j w (B.chart j x)‖ ≤ B.ckNorm 0 w
    have h := le_csSup (B.bddAbove_ckNorm_values 0 w)
      (show ‖iteratedFDeriv ℝ 0 (B.localizedCkFunction 0 j w) (B.chart j x)‖ ∈
        {a : ℝ | ∃ (j : Fin B.size) (i : ℕ), i ≤ 0 ∧
          ∃ z : EuclideanSpace ℝ (Fin n),
            a = ‖iteratedFDeriv ℝ i (B.localizedCkFunction 0 j w) z‖} from
        ⟨j, 0, le_rfl, B.chart j x, rfl⟩)
    change ‖iteratedFDeriv ℝ 0 (B.localizedCkFunction 0 j w) (B.chart j x)‖ ≤
      B.ckNorm 0 w at h
    simpa only [norm_iteratedFDeriv_zero] using h
  let f := (B.frame j).continuousLinearEquivAt ℂ x hx.2
  let ψ : EuclideanSpace ℂ (Fin q) → ℂ :=
    fun z ↦ α (f.symm ((B.cutoff j x : ℂ)⁻¹ • z))
  have hψ : Continuous ψ :=
    α.continuous.comp (f.symm.continuous.comp
      (((B.cutoff j x : ℂ)⁻¹ • ContinuousLinearMap.id ℂ
        (EuclideanSpace ℂ (Fin q))).continuous))
  have hχ : (B.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hj
  have hrecover (w : B.CkSectionSpace 0) : ψ (ev w) = α (w.val x) := by
    change α (f.symm ((B.cutoff j x : ℂ)⁻¹ • ((B.cutoff j x : ℂ) • f (w.val x)))) = _
    rw [smul_smul, inv_mul_cancel₀ hχ, one_smul, f.symm_apply_apply]
  have hpoint : Continuous (fun w : B.CkSectionSpace 0 ↦ α (w.val x)) :=
    (hψ.comp (ev.mkContinuous 1 hbound).continuous).congr hrecover
  -- Realize the same smooth output in one Sobolev order above the C⁰ threshold.
  let t : ℝ := (n : ℝ) / 2 + 1
  have ht : (n : ℝ) / 2 + (0 : ℕ) < t := by dsimp [t]; norm_num
  have hleft : Continuous
      (fun v : A.SobolevSpace s ↦ α ((K.sobolevToSmooth μ A B s v).val x)) := by
    apply ((hpoint.comp (B.sobolevToCk 0 t ht).continuous).comp
      (K.sobolevExtension μ A B s t).continuous).congr
    intro v
    change α ((B.sobolevToCk 0 t ht (K.sobolevExtension μ A B s t v)).val x) = _
    rw [← K.smoothToSobolev_sobolevToSmooth μ A B s t v,
      B.sobolevToCk_smoothToSobolev]
    rfl
  have hright : Continuous (fun v : A.SobolevSpace s ↦
      A.sobolevEvaluationPairing μ s (A.dualSmoothToSobolev (-s) (K.dualRow x α)) v) :=
    (A.sobolevEvaluationDuality μ s (A.dualSmoothToSobolev (-s) (K.dualRow x α))).continuous
  -- The original integral formula holds on the dense smooth image, hence on all inputs.
  have heq := (A.denseRange_smoothToSobolev s).equalizer hleft hright (by
    funext v
    simp only [Function.comp_apply]
    rw [K.sobolevToSmooth_smoothToSobolev, A.sobolevEvaluationPairing_smooth]
    exact K.dual_apply μ v x α)
  exact congrFun heq u

/-- A05: a smooth kernel is compact between any two real Sobolev orders on the closed base. -/
theorem isCompactOperator_sobolevExtension (s t : ℝ) :
    IsCompactOperator (K.sobolevExtension μ A B s t) := by
  /- First realize the kernel as a bounded map H^s(E)->H^(t+1)(F). The natural
  inclusion H^(t+1)(F)->H^t(F) is compact by global Rellich, with a strict drop of one.
  Their composite is the desired realization by target-order compatibility.
  This uses compactness of the base and does not assert compactness on an open base. -/
  have hdrop : t < t + 1 := lt_add_one t
  have hcompact := (B.isCompactOperator_sobolevInclusion (t + 1) t hdrop).comp_clm
    (K.sobolevExtension μ A B s (t + 1))
  change IsCompactOperator
    ((B.sobolevInclusion (t + 1) t hdrop.le).comp
      (K.sobolevExtension μ A B s (t + 1))) at hcompact
  rw [K.sobolevInclusion_comp_sobolevExtension] at hcompact
  exact hcompact

end SmoothKernel

variable (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- The standard smooth-kernel characterization of a smoothing operator on a closed base.
The fixed positive density trivializes the input density factor of its kernel. -/
def IsSmoothingOperator
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F) : Prop :=
  ∃ K : SmoothKernel (n := n) (r := r) (q := q) E F, K.toLinearMap μ = P

set_option maxHeartbeats 4000000 in
-- The reconstruction compares the same dependent fiber models across all real orders and frames.
open SmoothBundlePresentation in
/-- On a closed base the kernel characterization agrees with SG's all-order mapping property. -/
theorem isSmoothingOperator_iff_sobolevExtensions
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    IsSmoothingOperator μ P ↔
      ∀ s t : ℝ, ∃ T : A.SobolevSpace s →L[ℂ] B.SobolevSpace t,
        ∀ u : smoothSections (n := n) (r := r) E,
          T (A.smoothToSobolev s u) = B.smoothToSobolev t (P u) := by
  /- Forward, extend the given actual smooth kernel between every pair of orders.
  Reverse, recover the covector rows by the original perfect bilinear duality.
  All higher rows lower to one fixed row, so global all-order regularity produces
  one actual smooth dual section. The two operator-valued evaluation families give
  joint regularity. Original frames and the finite output partition assemble the
  smooth kernel, whose integral against the same density recovers P exactly. -/
  constructor
  · rintro ⟨K, rfl⟩ s t
    exact ⟨K.sobolevExtension μ A B s t, K.sobolevExtension_smoothToSobolev μ A B s t⟩
  · intro hP
    classical
    -- Opposite-order evaluation is compatible with the original dual inclusion.
    have pairing_inclusion (s t : ℝ) (hst : s ≤ t) (α : A.dualPresentation.SobolevSpace (-s))
        (u : smoothSections (n := n) (r := r) E) :
        A.sobolevEvaluationDuality μ t ((A.dualSobolevEquiv (-t)).symm
          (A.dualPresentation.sobolevInclusion (-s) (-t) (neg_le_neg hst) α))
            (A.smoothToSobolev t u) =
          A.sobolevEvaluationDuality μ s ((A.dualSobolevEquiv (-s)).symm α)
            (A.smoothToSobolev s u) := by
      refine (A.dualPresentation.denseRange_smoothToSobolev (-s)).induction_on α ?_ ?_
      · exact isClosed_eq
          (((A.sobolevEvaluationDuality μ t).continuous.comp
            ((A.dualSobolevEquiv (-t)).symm.continuous.comp
              (A.dualPresentation.sobolevInclusion (-s) (-t)
                (neg_le_neg hst)).continuous)).clm_apply
              continuous_const)
          (((A.sobolevEvaluationDuality μ s).continuous.comp
            (A.dualSobolevEquiv (-s)).symm.continuous).clm_apply continuous_const)
      · intro β
        obtain ⟨γ, rfl⟩ := (dualSectionsEquiv E).surjective β
        rw [A.dualPresentation.sobolevInclusion_smoothToSobolev,
          ← A.dualSobolevEquiv_smooth (-t), ← A.dualSobolevEquiv_smooth (-s)]
        simp only [LinearIsometryEquiv.symm_apply_apply]
        exact (A.sobolevEvaluationPairing_smooth μ t γ u).trans
          (A.sobolevEvaluationPairing_smooth μ s γ u).symm
    -- Recover a common smooth row before comparing its higher-order realizations.
    have smooth_row (L : ∀ s : ℝ, StrongDual ℂ (A.SobolevSpace s))
        (hL : ∀ (s : ℝ) (u : smoothSections (n := n) (r := r) E),
          L s (A.smoothToSobolev s u) = L 0 (A.smoothToSobolev 0 u)) :
        ∃ α : smoothDualSections (n := n) (r := r) E,
          ∀ s : ℝ, A.dualSmoothToSobolev (-s) α = (A.sobolevEvaluationDuality μ s).symm (L s) := by
      classical
      let row (s : ℝ) : A.dualPresentation.SobolevSpace (-s) :=
        A.dualSobolevEquiv (-s) ((A.sobolevEvaluationDuality μ s).symm (L s))
      have hrow (s : ℝ) (u : A.SobolevSpace s) :
          A.sobolevEvaluationDuality μ s ((A.dualSobolevEquiv (-s)).symm (row s)) u = L s u := by
        simp only [row, LinearIsometryEquiv.symm_apply_apply,
          ContinuousLinearEquiv.apply_symm_apply]
      -- Pairing against the same dense smooth inputs identifies the lowered high-order rows.
      have hcompatible (s t : ℝ) (hst : s ≤ t) :
          A.dualPresentation.sobolevInclusion (-s) (-t) (neg_le_neg hst) (row s) = row t := by
        apply (A.dualSobolevEquiv (-t)).symm.injective
        apply (A.sobolevEvaluationDuality μ t).injective
        apply ContinuousLinearMap.ext
        intro v
        refine (A.denseRange_smoothToSobolev t).induction_on v ?_ ?_
        · exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
        · intro u
          rw [pairing_inclusion s t hst (row s) u, hrow, hrow]
          exact (hL s u).trans (hL t u).symm
      -- All higher global lifts of one fixed vector give all local Sobolev orders.
      have hregular : A.dualPresentation.IsSmoothOn (-0) (row 0) Set.univ := by
        apply (A.dualPresentation.isSmoothOn_iff_forall_memSobolevOn
          (-0) (row 0) Set.univ isOpen_univ).mpr
        intro t
        let q : ℝ := max t 0
        have hq : -q ≤ 0 := by dsimp [q]; linarith [le_max_right t 0]
        have hmem : A.dualPresentation.MemSobolevOn (-0) (row 0) (-(-q)) Set.univ := by
          rw [← hcompatible (-q) 0 hq]
          intro j
          rw [A.dualPresentation.localDistribution_sobolevInclusion]
          exact A.dualPresentation.memSobolevOn_self (-(-q)) (row (-q)) Set.univ j
        exact A.dualPresentation.memSobolevOn_of_le (-0) (-(-q)) t (row 0) Set.univ
          hmem (by dsimp [q]; linarith [le_max_left t 0])
      obtain ⟨β, hβ, _⟩ :=
        (A.dualPresentation.isSmoothOn_univ_iff_exists_smooth_lift (-0) (row 0)).mp hregular
      let α : smoothDualSections (n := n) (r := r) E := (dualSectionsEquiv E).symm β
      have hαzero : A.dualSmoothToSobolev (-0) α =
          (A.sobolevEvaluationDuality μ 0).symm (L 0) := by
        apply (A.dualSobolevEquiv (-0)).injective
        rw [A.dualSobolevEquiv_smooth, LinearEquiv.apply_symm_apply]
        exact hβ
      -- The common smooth representative has the required embedding at every original order.
      refine ⟨α, ?_⟩
      intro s
      apply (A.sobolevEvaluationDuality μ s).injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      apply ContinuousLinearMap.ext
      intro v
      refine (A.denseRange_smoothToSobolev s).induction_on v ?_ ?_
      · exact isClosed_eq (ContinuousLinearMap.continuous _) (L s).continuous
      · intro u
        change A.sobolevEvaluationPairing μ s (A.dualSmoothToSobolev (-s) α)
          (A.smoothToSobolev s u) = _
        rw [A.sobolevEvaluationPairing_smooth]
        have hzero := A.sobolevEvaluationPairing_smooth μ 0 α u
        unfold sobolevEvaluationPairing at hzero
        rw [hαzero, ContinuousLinearEquiv.apply_symm_apply] at hzero
        exact hzero.symm.trans (hL s u).symm
    -- Both localized Sobolev evaluation families give joint regularity of the same rows.
    have localized_rows (j : Fin B.size) :
        ∃ row : EuclideanSpace ℝ (Fin n) → Fin q → smoothDualSections (n := n) (r := r) E,
          (∀ z i u, smoothDualSectionPairing E μ (row z i) u = B.localizedFunction j (P u) z i) ∧
          ∀ (i : Fin q) (l : Fin A.size), ContDiff ℝ ∞ (fun p :
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
            A.dualPresentation.localizedFunction l (dualSectionsEquiv E (row p.1 i)) p.2) := by
      classical
      let X := EuclideanSpace ℝ (Fin n)
      let V := EuclideanSpace ℂ (Fin q)
      let τ (k : ℕ) : ℝ := (n : ℝ) / 2 + ((k + 1 : ℕ) : ℝ) + 1
      have hτ (k : ℕ) : (n : ℝ) / 2 + ((k + 1 : ℕ) : ℝ) < τ k := by dsimp [τ]; linarith
      choose T hT using hP
      choose ev hev hdiff using fun k ↦
        B.exists_contDiff_localizedCkFunction_sobolevToCk k (τ k) (hτ k) j
      have hevsmooth (k : ℕ) (z : X) (u : smoothSections (n := n) (r := q) F) :
          ev k z (B.smoothToSobolev (τ k) u) = B.localizedFunction j u z := by
        rw [hev, B.sobolevToCk_smoothToSobolev]
        rfl
      let coord (i : Fin q) : V →L[ℂ] ℂ := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i
      let L (z : X) (i : Fin q) (s : ℝ) : StrongDual ℂ (A.SobolevSpace s) :=
        (coord i).comp ((ev 0 z).comp (T s (τ 0)))
      have hL (z : X) (i : Fin q) (s : ℝ) (u : smoothSections (n := n) (r := r) E) :
          L z i s (A.smoothToSobolev s u) = B.localizedFunction j (P u) z i := by
        change coord i (ev 0 z (T s (τ 0) (A.smoothToSobolev s u))) = _
        rw [hT, hevsmooth]
        rfl
      choose row hrow using fun z i ↦ smooth_row (L z i)
        (fun s u ↦ (hL z i s u).trans (hL z i 0 u).symm)
      have hpair (z : X) (i : Fin q) (u : smoothSections (n := n) (r := r) E) :
          smoothDualSectionPairing E μ (row z i) u = B.localizedFunction j (P u) z i := by
        rw [← A.sobolevEvaluationPairing_smooth μ 0]
        unfold sobolevEvaluationPairing
        rw [hrow, ContinuousLinearEquiv.apply_symm_apply]
        exact hL z i 0 u
      refine ⟨row, hpair, ?_⟩
      intro i l
      apply contDiff_infty.mpr
      intro k
      -- The same smooth row has a C^k high-order realization from the higher output evaluation.
      let D : (B.SobolevSpace (τ k) →L[ℂ] V) →L[ℂ]
          A.dualPresentation.SobolevSpace (-(-τ k)) :=
        (A.dualSobolevEquiv (-(-τ k))).toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((A.sobolevEvaluationDuality μ (-τ k)).symm.toContinuousLinearMap.comp
            (((ContinuousLinearMap.compL ℂ (A.SobolevSpace (-τ k))
              (B.SobolevSpace (τ k)) ℂ).flip (T (-τ k) (τ k))).comp
                ((ContinuousLinearMap.compL ℂ (B.SobolevSpace (τ k)) V ℂ) (coord i))))
      have hD (z : X) : D (ev k z) = A.dualPresentation.smoothToSobolev (-(-τ k))
          (dualSectionsEquiv E (row z i)) := by
        rw [← A.dualSobolevEquiv_smooth]
        apply (A.dualSobolevEquiv (-(-τ k))).symm.injective
        simp only [D, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.symm_apply_apply,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
        rw [hrow]
        apply congrArg (A.sobolevEvaluationDuality μ (-τ k)).symm
        apply ContinuousLinearMap.ext
        intro v
        refine (A.denseRange_smoothToSobolev (-τ k)).induction_on v ?_ ?_
        · exact isClosed_eq (ContinuousLinearMap.continuous _) (L z i (-τ k)).continuous
        · intro u
          change coord i (ev k z (T (-τ k) (τ k) (A.smoothToSobolev (-τ k) u))) = _
          rw [hT, hevsmooth, hL]
          rfl
      have hreg : ContDiff ℝ k (fun z ↦ D (ev k z)) :=
        D.restrictScalars ℝ |>.contDiff.comp (hdiff k)
      obtain ⟨evInput, hInput, hInputDiff⟩ :=
        A.dualPresentation.exists_contDiff_localizedCkFunction_sobolevToCk
          k (-(-τ k)) (by simpa only [neg_neg] using hτ k) l
      have hjoint : ContDiff ℝ k (fun p : X × X ↦ evInput p.2 (D (ev k p.1))) :=
        ((ContinuousLinearMap.restrictScalarsL ℂ
          (A.dualPresentation.SobolevSpace (-(-τ k))) (EuclideanSpace ℂ (Fin r)) ℝ ℝ).contDiff.comp
          (hInputDiff.comp contDiff_snd)).clm_apply (hreg.comp contDiff_fst)
      convert hjoint using 1
      funext p
      rw [hD, hInput, A.dualPresentation.sobolevToCk_smoothToSobolev]
      rfl
    -- Assemble actual fiber maps in the original frames and recover the original integral map.
    classical
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let W := EuclideanSpace ℂ (Fin q)
    let I := 𝓘(ℝ, X)
    let frameA (l : Fin A.size) : MemTrivializationAtlas (A.frame l) := A.frame_mem_atlas l
    let frameB (j : Fin B.size) : MemTrivializationAtlas (B.frame j) := B.frame_mem_atlas j
    choose row hpair hdiff using localized_rows
    let pack (a : Fin q → V →L[ℂ] ℂ) : V →L[ℂ] W :=
      (EuclideanSpace.equiv (Fin q) ℂ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi a)
    let matrixMap : (Fin q → V) →ₗ[ℂ] (V →L[ℂ] W) :=
      { toFun := fun a ↦ pack (fun i ↦ (dualModelEquiv r).symm (a i))
        map_add' := by
          intro a b
          ext v i
          change (dualModelEquiv r).symm (a i + b i) v =
            (dualModelEquiv r).symm (a i) v + (dualModelEquiv r).symm (b i) v
          rw [map_add, add_apply]
        map_smul' := by
          intro c a
          ext v i
          change (dualModelEquiv r).symm (c • a i) v = c * (dualModelEquiv r).symm (a i) v
          rw [map_smul]
          rfl }
    let C (j : Fin B.size) (l : Fin A.size) (p : X × X) : V →L[ℂ] W :=
      matrixMap (fun i ↦ A.dualPresentation.localizedFunction l
        (dualSectionsEquiv E (row j p.1 i)) p.2)
    have hC (j : Fin B.size) (l : Fin A.size) : ContDiff ℝ ∞ (C j l) :=
      matrixMap.toContinuousLinearMap.restrictScalars ℝ |>.contDiff.comp
        (contDiff_pi.mpr (fun i ↦ hdiff j i l))
    have hCvalue (j : Fin B.size) (l : Fin A.size) (z : X) (y : M)
        (hy : y ∈ (A.chart l).source) (v : V) (i : Fin q) :
        C j l (z, A.chart l y) v i =
          (A.cutoff l y : ℂ) * (row j z i).val y ((A.frame l).symmL ℂ y v) := by
      change (dualModelEquiv r).symm (A.dualPresentation.localizedFunction l
        (dualSectionsEquiv E (row j z i)) (A.chart l y)) v = _
      rw [A.localizedFunction_dualPresentation]
      simp only [localizedDualFunction, ite_eq_left ((A.chart l).map_source hy),
        (A.chart l).left_inv hy]
      have hdual : dualSectionInFrame E (A.frame l) (row j z i).val y =
          dualModelEquiv r ((row j z i).val y |>.comp ((A.frame l).symmL ℂ y)) := by
        ext a
        rw [dualModelEquiv_apply]
        rfl
      rw [hdual, map_smul, ContinuousLinearEquiv.symm_apply_apply]
      rfl
    let packFiber (y : M) (a : Fin q → E y →L[ℂ] ℂ) : E y →L[ℂ] W :=
      (EuclideanSpace.equiv (Fin q) ℂ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi a)
    let Kj (j : Fin B.size) (x y : M) : E y →L[ℂ] F x :=
      if x ∈ (B.chart j).source then
        ((B.frame j).symmL ℂ x).comp (packFiber y (fun i ↦ (row j (B.chart j x) i).val y))
      else 0
    have hzero (j : Fin B.size) (x y : M) (hx : x ∉ tsupport (B.cutoff j)) :
        Kj j x y = 0 := by
      by_cases hsource : x ∈ (B.chart j).source
      · have hrowzero (i : Fin q) : row j (B.chart j x) i = 0 := by
          apply A.dualSmoothToSobolev_injective (-0)
          apply (A.sobolevEvaluationDuality μ 0).injective
          rw [map_zero, map_zero]
          apply ContinuousLinearMap.ext
          intro v
          refine (A.denseRange_smoothToSobolev 0).induction_on v ?_ ?_
          · exact isClosed_eq (ContinuousLinearMap.continuous _) continuous_const
          · intro u
            change A.sobolevEvaluationPairing μ 0 _ _ = 0
            rw [A.sobolevEvaluationPairing_smooth, hpair]
            simp [localizedFunction, (B.chart j).map_source hsource,
              (B.chart j).left_inv hsource, image_eq_zero_of_notMem_tsupport hx]
        ext v
        simp only [Kj, ite_eq_left hsource, hrowzero]
        change (B.frame j).symmL ℂ x 0 = 0
        exact map_zero _
      · simp [Kj, hsource]
    have hsmooth (j : Fin B.size) : IsSmoothKernel (n := n) (r := r) (q := q) E F (Kj j) := by
      let := B.frame_mem_atlas j
      intro e f _ _ p hp
      by_cases hsupp : p.1 ∈ tsupport (B.cutoff j)
      · have hxsource := (B.support_subset j hsupp).1
        have hxframe := (B.support_subset j hsupp).2
        obtain ⟨l, hl⟩ : ∃ l : Fin A.size, A.cutoff l p.2 ≠ 0 := by
          by_contra hn
          push Not at hn
          have h := A.sum_cutoff p.2
          simp [hn] at h
        let := A.frame_mem_atlas l
        have hysupp := subset_tsupport (A.cutoff l) hl
        have hysource := (A.support_subset l hysupp).1
        have hyframe := (A.support_subset l hysupp).2
        have hchartx := contMDiffAt_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (B.chart_mem_atlas j)) hxsource
        have hcharty := contMDiffAt_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (A.chart_mem_atlas l)) hysource
        have hmatrix := (hC j l).comp_contMDiffAt
          ((hchartx.comp p (contMDiffAt_fst (I := I) (J := I))).prodMk_space
            (hcharty.comp p (contMDiffAt_snd (I := I) (J := I))))
        have hinputOn := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e (A.frame l)
        have hinput := (hinputOn.contMDiffAt
          ((e.open_baseSet.inter (A.frame l).open_baseSet).mem_nhds
            ⟨hp.2, hyframe⟩)).comp p (contMDiffAt_snd (I := I) (J := I))
        have houtputOn := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (B.frame j) f
        have houtput := (houtputOn.contMDiffAt
          (((B.frame j).open_baseSet.inter f.open_baseSet).mem_nhds
            ⟨hxframe, hp.1⟩)).comp p (contMDiffAt_fst (I := I) (J := I))
        let comp₁ := (ContinuousLinearMap.compL ℂ V V W).bilinearRestrictScalars ℝ
        let comp₂ := (ContinuousLinearMap.compL ℂ V W W).bilinearRestrictScalars ℝ
        have hinner := (comp₁.contDiff.comp_contMDiffAt hmatrix).clm_apply hinput
        have hfull := (comp₂.contDiff.comp_contMDiffAt houtput).clm_apply hinner
        have hcut := (A.smooth_cutoff l).contMDiffAt (x := p.2)
        have hinvReal := (hcut.comp p (contMDiffAt_snd (I := I) (J := I))).inv₀ hl
        have hinv : ContMDiffAt (I.prod I) 𝓘(ℝ, ℂ) ∞
            (fun z : M × M ↦ (A.cutoff l z.2 : ℂ)⁻¹) p := by
          convert Complex.ofRealCLM.contDiff.comp_contMDiffAt hinvReal using 1
          funext z
          exact (Complex.ofReal_inv (A.cutoff l z.2)).symm
        have hsmul : ContDiff ℝ ∞ (fun a : ℂ × (V →L[ℂ] W) ↦ a.1 • a.2) :=
          (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
        have hlocal := hsmul.comp_contMDiffAt (hinv.prodMk_space hfull)
        apply ContMDiffAt.contMDiffWithinAt
        apply hlocal.congr_of_eventuallyEq
        filter_upwards [((B.chart j).open_source.prod (A.chart l).open_source).mem_nhds
          ⟨hxsource, hysource⟩,
          (((B.frame j).open_baseSet.inter f.open_baseSet).prod
            (e.open_baseSet.inter (A.frame l).open_baseSet)).mem_nhds
              ⟨⟨hxframe, hp.1⟩, ⟨hp.2, hyframe⟩⟩,
          (continuous_snd |>.tendsto p).eventually
            (((A.smooth_cutoff l).continuous.continuousAt.eventually_ne hl))] with z hz hfz hne
        apply ContinuousLinearMap.ext
        intro v
        change f.continuousLinearMapAt ℂ z.1 (Kj j z.1 z.2 (e.symmL ℂ z.2 v)) =
          (A.cutoff l z.2 : ℂ)⁻¹ •
            (B.frame j).coordChangeL ℂ f z.1
              (C j l (B.chart j z.1, A.chart l z.2)
                (e.coordChangeL ℂ (A.frame l) z.2 v))
        simp only [Kj, ite_eq_left hz.1, ContinuousLinearMap.comp_apply]
        rw [(B.frame j).coordChangeL_apply f hfz.1,
          ← (B.frame j).symmL_apply (R := ℂ) hfz.1.1,
          ← f.continuousLinearMapAt_apply_of_mem ℂ hfz.1.2, ← map_smul, ← map_smul]
        congr 1
        congr 1
        ext i
        change (row j (B.chart j z.1) i).val z.2 (e.symmL ℂ z.2 v) = _
        rw [PiLp.smul_apply, smul_eq_mul, hCvalue j l _ _ hz.2]
        have hcoord : (A.frame l).symmL ℂ z.2 (e.coordChangeL ℂ (A.frame l) z.2 v) =
            e.symmL ℂ z.2 v := by
          rw [e.coordChangeL_apply (A.frame l) hfz.2,
            ← (A.frame l).continuousLinearMapAt_apply_of_mem ℂ hfz.2.2,
            (A.frame l).symmL_continuousLinearMapAt hfz.2.2, e.symmL_apply (R := ℂ) hfz.2.1]
        rw [hcoord, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hne), one_mul]
      · apply ContMDiffAt.contMDiffWithinAt
        apply (contMDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq
        filter_upwards [(continuous_fst |>.tendsto p).eventually
          ((isClosed_tsupport (B.cutoff j)).isOpen_compl.mem_nhds hsupp)] with z hz
        simp [kernelInFrames, hzero j z.1 z.2 hz]
    let K : SmoothKernel (n := n) (r := r) (q := q) E F :=
      { toFun := fun x y ↦ ∑ j, Kj j x y
        isSmooth := by
          intro e f _ _
          have hsum : ContMDiffOn (I.prod I) 𝓘(ℝ, V →L[ℂ] W) ∞
              (fun z : M × M ↦ ∑ j, kernelInFrames E F (Kj j) e f z)
              (f.baseSet ×ˢ e.baseSet) := by
            apply contMDiffOn_finsetSum
            intro j _
            exact hsmooth j e f
          apply hsum.congr
          intro z hz
          apply ContinuousLinearMap.ext
          intro v
          simp [kernelInFrames, sum_apply, map_sum] }
    -- Each original output partition piece integrates to its prescribed localized operator.
    let patch (j : Fin B.size) : SmoothKernel (n := n) (r := r) (q := q) E F :=
      ⟨Kj j, hsmooth j⟩
    have hpatch (j : Fin B.size) (u : smoothSections (n := n) (r := r) E) (x : M) :
        (patch j).apply μ u x = (B.cutoff j x : ℂ) • (P u).val x := by
      let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
      let : CompleteSpace (F x) := VectorBundle.completeSpace ℂ W F x
      by_cases hx : x ∈ tsupport (B.cutoff j)
      · have hsource := (B.support_subset j hx).1
        have hframe := (B.support_subset j hx).2
        let := B.frame_mem_atlas j
        let c := (B.frame j).continuousLinearEquivAt ℂ x hframe
        have hc (w : F x) : c w = (B.frame j).continuousLinearMapAt ℂ x w := by
          rw [(B.frame j).continuousLinearMapAt_apply_of_mem ℂ hframe]
          rfl
        apply c.injective
        rw [map_smul]
        ext i
        let coord := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i
        change c ((patch j).apply μ u x) i = (B.cutoff j x : ℂ) * c ((P u).val x) i
        calc
          c ((patch j).apply μ u x) i =
              ∫ y, (row j (B.chart j x) i).val y (u.val y) ∂μ := by
            change (coord.comp c.toContinuousLinearMap) (∫ y, Kj j x y (u.val y) ∂μ) = _
            rw [← ContinuousLinearMap.integral_comp_comm _ ((patch j).integrable_apply μ u x)]
            apply integral_congr_ae
            filter_upwards [] with y
            change c (Kj j x y (u.val y)) i = _
            rw [hc]
            simp only [Kj, ite_eq_left hsource, ContinuousLinearMap.comp_apply]
            change (B.frame j).continuousLinearMapAt ℂ x
              ((B.frame j).symmL ℂ x (packFiber y
                (fun a ↦ (row j (B.chart j x) a).val y) (u.val y))) i = _
            rw [(B.frame j).continuousLinearMapAt_symmL hframe]
            rfl
          _ = B.localizedFunction j (P u) (B.chart j x) i := hpair j _ i u
          _ = (B.cutoff j x : ℂ) * c ((P u).val x) i := by
            simp only [localizedFunction, ite_eq_left ((B.chart j).map_source hsource),
              (B.chart j).left_inv hsource, sectionInChart]
            rw [(B.chart j).left_inv hsource, hc,
              (B.frame j).continuousLinearMapAt_apply_of_mem ℂ hframe]
            rfl
      · change (∫ y, Kj j x y (u.val y) ∂μ) = _
        simp [hzero j x _ hx, image_eq_zero_of_notMem_tsupport hx]
    refine ⟨K, ?_⟩
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
    let : CompleteSpace (F x) := VectorBundle.completeSpace ℂ W F x
    change (∫ y, (∑ j, Kj j x y) (u.val y) ∂μ) = (P u).val x
    simp only [sum_apply]
    rw [integral_finsetSum Finset.univ (fun j _ ↦ (patch j).integrable_apply μ u x)]
    change ∑ j, (patch j).apply μ u x = _
    simp only [hpatch]
    rw [← Finset.sum_smul]
    have hsum : ∑ j, (B.cutoff j x : ℂ) = 1 := by exact_mod_cast B.sum_cutoff x
    rw [hsum, one_smul]

/-- A smoothing operator has a unique bounded realization for every pair of real Sobolev orders. -/
theorem existsUnique_sobolevExtension_of_isSmoothingOperator
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hP : IsSmoothingOperator μ P)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (s t : ℝ) :
    ∃! T : A.SobolevSpace s →L[ℂ] B.SobolevSpace t,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) = B.smoothToSobolev t (P u) := by
  /- Extract the actual smooth-kernel representation from hP. Its unique Sobolev
  extension has the stated action because its smooth section map is P. Any other
  extension agrees with that action on the same dense subspace, giving uniqueness. -/
  obtain ⟨K, hK⟩ := hP
  subst P
  exact K.existsUnique_sobolevExtension μ A B s t

/-- A05 for a smooth-section operator specified by its kernel and its actual bounded extension. -/
theorem isCompactOperator_of_isSmoothingOperator
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hP : IsSmoothingOperator μ P)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (s t : ℝ)
    (T : A.SobolevSpace s →L[ℂ] B.SobolevSpace t)
    (hT : ∀ u : smoothSections (n := n) (r := r) E,
      T (A.smoothToSobolev s u) = B.smoothToSobolev t (P u)) :
    IsCompactOperator T := by
  /- Choose the representing smooth kernel. Density and hT identify T with the
  kernel's uniquely specified Sobolev extension. Apply its compactness theorem,
  which factors through a strictly higher output Sobolev order and global Rellich. -/
  obtain ⟨K, hK⟩ := hP
  subst P
  have heq : T = K.sobolevExtension μ A B s t := by
    apply (K.existsUnique_sobolevExtension μ A B s t).unique hT
    exact K.sobolevExtension_smoothToSobolev μ A B s t
  rw [heq]
  exact K.isCompactOperator_sobolevExtension μ A B s t

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- SG's all-order mapping property implies compactness of the specified Sobolev realization.
This uses one strict gain of derivatives and Rellich, without a kernel representation. -/
theorem isCompactOperator_of_sobolevExtensions
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (hP : ∀ a b : ℝ, ∃ S : A.SobolevSpace a →L[ℂ] B.SobolevSpace b,
      ∀ u : smoothSections (n := n) (r := r) E,
        S (A.smoothToSobolev a u) = B.smoothToSobolev b (P u))
    (s : ℝ) (T : A.SobolevSpace s →L[ℂ] B.SobolevSpace s)
    (hT : ∀ u : smoothSections (n := n) (r := r) E,
      T (A.smoothToSobolev s u) = B.smoothToSobolev s (P u)) :
    IsCompactOperator T := by
  -- Gain one derivative using the same original section map, then apply compact inclusion.
  obtain ⟨R, hR⟩ := hP s (s + 1)
  have hdrop : s < s + 1 := lt_add_one s
  let J := B.sobolevInclusion (s + 1) s hdrop.le
  have hcompact : IsCompactOperator (J.comp R) :=
    (B.isCompactOperator_sobolevInclusion (s + 1) s hdrop).comp_clm R
  -- Both continuous maps agree on the original dense smooth image, hence everywhere.
  have heq : J.comp R = T := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer
      (J.comp R).continuous T.continuous
    funext u
    change J (R (A.smoothToSobolev s u)) = T (A.smoothToSobolev s u)
    rw [hR, hT]
    exact B.sobolevInclusion_smoothToSobolev (s + 1) s hdrop.le (P u)
  rw [heq] at hcompact
  exact hcompact

end AtiyahSinger

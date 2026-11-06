/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DensityDiffeomorph
public import AtiyahSinger.Geometry.SmoothDensityRatio
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth density families under a smooth action

Public module ID: M1186.

The density of the inverse action is jointly smooth in the forward group parameter
and the base point. Its Jacobian involves the forward action, so neither smooth
inversion nor a Lie group structure is required. This is the density factor in
compact averages of geometrically conjugated smooth kernels.

The local argument uses the actual Jacobian change of variables, as in
`EquivariantSmoothDensity`, and retains the original positive measure.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Manifold Set Filter Topology
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 3000000 in
-- The local Jacobian identity and its parameter derivatives are checked in one proof.
/-- The inverse-action chart density is a joint smooth family of actual positive densities. -/
private theorem exists_smooth_inv_smul_chart_density
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
    ∃ w : G → EuclideanSpace ℝ (Fin n) → ℝ,
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℝ) ∞
        (fun p : G × EuclideanSpace ℝ (Fin n) ↦ w p.1 p.2) (univ ×ˢ c.target) ∧
      ∀ g, (∀ z ∈ c.target, 0 < w g z) ∧
        Measure.map c ((Measure.map
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm
            μ).restrict c.source) =
          (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w g z)) := by
  /- The original charts give the forward-Jacobian formula for the
  inverse-action pushforward. Equality of the resulting measures identifies
  the selected chart densities pointwise. Differentiate the forward action
  in the base variable to obtain joint smoothness. -/
  classical
  let W := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, W)
  let : ContinuousSMul G M := ⟨(contMDiff_smul (I := IG) (I' := I) (n := ∞)).continuous⟩
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ := by
    constructor
    have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_mul
    exact hmul.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  let e (g : G) : M ≃ₘ⟮I, I⟯ M := (Diffeomorph.smul IG I ∞ g).symm
  have hpush (g : G) : IsSmoothPositiveMeasure (n := n) (Measure.map (e g) μ) :=
    IsSmoothPositiveMeasure.map_diffeomorph μ (e g)
  have hcM := contMDiffOn_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  have hcS := contMDiffOn_symm_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  choose w hw using fun g : G ↦ (hpush g).exists_smooth_density c hc
  let θ (g : G) := Measure.map c ((Measure.map (e g) μ).restrict c.source)
  let d (x : M) := chartAt W x
  let t (g : G) (x : M) : OpenPartialHomeomorph W W :=
    c.symm.trans ((e g).symm.toHomeomorph.toOpenPartialHomeomorph.trans (d x))
  choose a ha using fun x : M ↦ hμ.exists_smooth_density (d x) (chart_mem_atlas W x)
  have ht (g : G) (x : M) : ContDiffOn ℝ ∞ (t g x) (t g x).source := by
    apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    have hcs := (hcS y hy.1).contMDiffAt (c.open_target.mem_nhds hy.1)
    have hes := (e g).symm.contMDiffAt.comp y hcs
    have hd := (contMDiffOn_chart (I := I) (n := (∞ : ℕ∞ω)) (x := x)
      _ hy.2.2).contMDiffAt ((d x).open_source.mem_nhds hy.2.2)
    exact (hd.comp y hes).contMDiffWithinAt
  have hts (g : G) (x : M) : ContDiffOn ℝ ∞ (t g x).symm (t g x).target := by
    apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    have hds := (contMDiffOn_chart_symm (I := I) (n := (∞ : ℕ∞ω)) (x := x)
      y hy.1.1).contMDiffAt ((d x).open_target.mem_nhds hy.1.1)
    have he := (e g).contMDiffAt.comp y hds
    have hcs := (hcM _ hy.2).contMDiffAt (c.open_source.mem_nhds hy.2)
    exact (hcs.comp y he).contMDiffWithinAt
  -- The derivative of the inverse identity forces the coordinate Jacobian to be nonzero.
  have hdet (g : G) (x : M) (y : W) (hy : y ∈ (t g x).source) :
      (fderiv ℝ (t g x) y).det ≠ 0 := by
    have hf := ((ht g x) y hy).contDiffAt ((t g x).open_source.mem_nhds hy)
    have hg := ((hts g x) ((t g x) y) ((t g x).map_source hy)).contDiffAt
      ((t g x).open_target.mem_nhds ((t g x).map_source hy))
    have hinv : (fderiv ℝ (t g x).symm ((t g x) y)).comp (fderiv ℝ (t g x) y) =
        ContinuousLinearMap.id ℝ W := by
      have hh := (hg.differentiableAt (by simp)).hasFDerivAt.comp y
        (hf.differentiableAt (by simp)).hasFDerivAt
      have hid : HasFDerivAt (fun z : W ↦ z)
          ((fderiv ℝ (t g x).symm ((t g x) y)).comp (fderiv ℝ (t g x) y)) y := by
        apply hh.congr_of_eventuallyEq
        filter_upwards [(t g x).open_source.mem_nhds hy] with z hz
        exact ((t g x).left_inv hz).symm
      exact hid.unique (hasFDerivAt_id y)
    have hd := congrArg ContinuousLinearMap.det hinv
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
    exact right_ne_zero_of_mul_eq_one hd
  let q (g : G) (x : M) (y : W) := |(fderiv ℝ (t g x) y).det| * a x (t g x y)
  have hqpos (g : G) (x : M) (y : W) (hy : y ∈ (t g x).source) : 0 < q g x y := by
    exact mul_pos (abs_pos.mpr (hdet g x y hy))
      ((ha x).2.1 _ ((t g x).map_source hy).1.1)
  have hqsmooth (g : G) (x : M) : ContDiffOn ℝ ∞ (q g x) (t g x).source := by
    intro y hy
    have hf := ((ht g x) y hy).contDiffAt ((t g x).open_source.mem_nhds hy)
    have hfd := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
    have hds : ContDiffAt ℝ ∞ (fun z ↦ (fderiv ℝ (t g x) z).det) y := by
      let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
      apply ContDiffAt.sum
      intro σ hσ
      apply ContDiffAt.mul contDiffAt_const
      apply contDiffAt_prod
      intro i hi
      simp only [LinearMap.toMatrix_apply]
      exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp y
        (hfd.clm_apply contDiffAt_const))
    have has := ((ha x).1 _ ((t g x).map_source hy).1.1).contDiffAt
      ((d x).open_target.mem_nhds ((t g x).map_source hy).1.1)
    exact ((hds.abs (hdet g x y hy)).mul (has.comp y hf)).contDiffWithinAt
  -- Apply the Euclidean Jacobian theorem to the exact restricted pushforward measure.
  have hqmeasure (g : G) (x : M) : (θ g).restrict (t g x).source =
      (volume.restrict (t g x).source).withDensity (fun y ↦ ENNReal.ofReal (q g x y)) := by
    ext A hA
    let A₀ := A ∩ (t g x).source
    have hA₀ : MeasurableSet A₀ := hA.inter (t g x).open_source.measurableSet
    have hpre : MeasurableSet (c ⁻¹' A₀ ∩ c.source) := by
      simpa only [Set.domRestrict_eq, Set.preimage_comp,
        Set.image_preimage_eq_inter_range, Subtype.range_coe] using
        c.open_source.measurableSet.subtype_image
          (hA₀.preimage c.continuousOn.domRestrict.measurable)
    let B := t g x '' A₀
    have hder (y : W) (hy : y ∈ A₀) :
        HasFDerivWithinAt (t g x) (fderiv ℝ (t g x) y) A₀ y :=
      (((ht g x) y hy.2).contDiffAt ((t g x).open_source.mem_nhds hy.2)
        |>.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    have hB : MeasurableSet B := measurable_image_of_fderivWithin hA₀ hder
      ((t g x).injOn.mono Set.inter_subset_right)
    have hBsub : B ⊆ (d x).target := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((t g x).map_source hy.2).1.1
    have hset : (e g) ⁻¹' (c ⁻¹' A₀ ∩ c.source) = d x ⁻¹' B ∩ (d x).source := by
      ext z
      constructor
      · rintro ⟨hy, hcz⟩
        have hdz : z ∈ (d x).source := by
          have hh := hy.2.2.2
          change (e g).symm (c.symm (c (e g z))) ∈ (d x).source at hh
          simpa only [c.left_inv hcz, (e g).symm_apply_apply] using hh
        refine ⟨⟨c (e g z), hy, ?_⟩, hdz⟩
        change d x ((e g).symm (c.symm (c (e g z)))) = d x z
        rw [c.left_inv hcz, (e g).symm_apply_apply]
      · rintro ⟨⟨y, hy, heq⟩, hz⟩
        have hdz : (e g).symm (c.symm y) ∈ (d x).source := hy.2.2.2
        have heq' : (e g).symm (c.symm y) = z := (d x).injOn hdz hz heq
        have hez : e g z = c.symm y := by rw [← heq', (e g).apply_symm_apply]
        have hcy : c (e g z) = y := by rw [hez, c.right_inv hy.2.1]
        constructor
        · change c (e g z) ∈ A₀
          rw [hcy]
          exact hy
        · rw [hez]
          exact c.map_target hy.2.1
    have hleft : ((θ g).restrict (t g x).source) A =
        ∫⁻ y in B, ENNReal.ofReal (a x y) ∂volume := by
      rw [Measure.restrict_apply hA]
      change (Measure.map c ((Measure.map (e g) μ).restrict c.source)) A₀ = _
      rw [Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hA₀,
        Measure.restrict_apply' c.open_source.measurableSet,
        Measure.map_apply (e g).continuous.measurable hpre, hset]
      have hh := congrArg (fun η : Measure W ↦ η B) (ha x).2.2
      rw [Measure.map_apply_of_aemeasurable
        ((d x).continuousOn.aemeasurable (d x).open_source.measurableSet) hB,
        Measure.restrict_apply' (d x).open_source.measurableSet,
        withDensity_apply _ hB] at hh
      rw [hh, Measure.restrict_restrict hB,
        Set.inter_eq_left.mpr hBsub]
    rw [hleft, withDensity_apply _ hA, Measure.restrict_restrict hA]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA₀ hder
      ((t g x).injOn.mono Set.inter_subset_right)]
    apply lintegral_congr
    intro y
    exact (ENNReal.ofReal_mul (abs_nonneg _) (q := a x (t g x y))).symm
  -- The forward-Jacobian formula for the inverse pushforward identifies each density pointwise.
  have hwlocal (g : G) (x : M) : Set.EqOn (w g) (q g x) (t g x).source := by
    have heq : (volume.restrict (t g x).source).withDensity
        (fun y ↦ ENNReal.ofReal (w g y)) =
        (volume.restrict (t g x).source).withDensity
          (fun y ↦ ENNReal.ofReal (q g x y)) := by
      have hh := hqmeasure g x
      change (Measure.map c ((Measure.map (e g) μ).restrict c.source)).restrict _ = _ at hh
      rw [(hw g).2.2, restrict_withDensity (t g x).open_source.measurableSet,
        Measure.restrict_restrict (t g x).open_source.measurableSet,
        Set.inter_eq_left.mpr (show (t g x).source ⊆ c.target from fun _ hy ↦ hy.1)] at hh
      exact hh
    have hwc := (hw g).1.continuousOn.mono
      (show (t g x).source ⊆ c.target from fun _ hy ↦ hy.1)
    have hqc := (hqsmooth g x).continuousOn
    have hae := (withDensity_eq_iff_of_sigmaFinite
      (hwc.aemeasurable (t g x).open_source.measurableSet).ennreal_ofReal
      (hqc.aemeasurable (t g x).open_source.measurableSet).ennreal_ofReal).mp heq
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure W)) _ (t g x).open_source hwc hqc
    filter_upwards [hae, ae_restrict_mem (t g x).open_source.measurableSet] with y hy hyU
    have hh := congrArg ENNReal.toReal hy
    simpa only [ENNReal.toReal_ofReal ((hw g).2.1 y hyU.1).le,
      ENNReal.toReal_ofReal (hqpos g x y hyU).le] using hh
  have hjoint : ContMDiffOn (IG.prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : G × W ↦ w p.1 p.2) (univ ×ˢ c.target) := by
    intro p hp
    let x := p.1 • c.symm p.2
    have hx : p.2 ∈ (t p.1 x).source :=
      ⟨hp.2, mem_univ _, mem_chart_source W x⟩
    let f : G × W → W := fun z ↦ t z.1 x z.2
    have hcsp : ContMDiffAt I I ∞ c.symm p.2 :=
      (hcS p.2 hp.2).contMDiffAt (c.open_target.mem_nhds hp.2)
    have hact : ContMDiffAt (IG.prod I) I ∞
        (fun z : G × W ↦ z.1 • c.symm z.2) p :=
      contMDiffAt_fst.smul (hcsp.comp p contMDiffAt_snd)
    have hdx : ContMDiffAt I I ∞ (d x) x :=
      (contMDiffOn_chart (I := I) (n := (∞ : ℕ∞ω)) x
        (mem_chart_source W x)).contMDiffAt
          ((d x).open_source.mem_nhds (mem_chart_source W x))
    have hf : ContMDiffAt (IG.prod I) I ∞ f p := hdx.comp p hact
    -- Differentiate only in the coordinate variable, retaining the group parameter.
    have hcomp : ContMDiffAt ((IG.prod I).prod I) I ∞
        (fun z : (G × W) × W ↦ f (z.1.1, z.2)) (p, p.2) :=
      hf.comp_of_eq (contMDiffAt_fst.fst.prodMk contMDiffAt_snd) rfl
    have hfd := hcomp.mfderiv (m := ∞)
      (fun z : G × W ↦ fun y : W ↦ f (z.1, y))
      (fun z : G × W ↦ z.2) contMDiffAt_snd (by simp)
    have heq : inTangentCoordinates I I
        (fun z : G × W ↦ z.2) (fun z ↦ f (z.1, z.2))
        (fun z ↦ mfderiv I I (fun y ↦ f (z.1, y)) z.2) p =
        (fun z : G × W ↦ fderiv ℝ (t z.1 x) z.2) := by
      funext z
      dsimp only [I]
      simp only [mfderiv_eq_fderiv]
      unfold inTangentCoordinates
      erw [inCoordinates_tangent_bundle_core_model_space]
      rfl
    rw [heq] at hfd
    have hds : ContMDiffAt (IG.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : G × W ↦ (fderiv ℝ (t z.1 x) z.2).det) p := by
      let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
      apply ContMDiffAt.sum
      intro σ hσ
      apply ContMDiffAt.mul contMDiffAt_const
      apply ContMDiffAt.prod
      intro i hi
      simp only [LinearMap.toMatrix_apply]
      exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contMDiff.contMDiffAt.comp p
        (hfd.clm_apply contMDiffAt_const))
    have habs : ContMDiffAt (IG.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : G × W ↦ |(fderiv ℝ (t z.1 x) z.2).det|) p :=
      ((contDiffAt_id.abs (hdet p.1 x p.2 hx)).contMDiffAt.comp p hds)
    have has := ((ha x).1 _ ((t p.1 x).map_source hx).1.1).contDiffAt
      ((d x).open_target.mem_nhds ((t p.1 x).map_source hx).1.1)
    have hq : ContMDiffAt (IG.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : G × W ↦ q z.1 x z.2) p :=
      habs.mul (has.contMDiffAt.comp p hf)
    apply (hq.congr_of_eventuallyEq ?_).contMDiffWithinAt
    have hcN : ∀ᶠ z : G × W in 𝓝 p, z.2 ∈ c.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds hp.2)
    have hdN : ∀ᶠ z : G × W in 𝓝 p, z.1 • c.symm z.2 ∈ (d x).source :=
      hact.continuousAt.preimage_mem_nhds ((d x).open_source.mem_nhds
        (mem_chart_source W x))
    filter_upwards [hcN, hdN] with z hcz hdz
    exact hwlocal z.1 x ⟨hcz, mem_univ _, hdz⟩
  exact ⟨w, hjoint, fun g ↦ (hw g).2⟩

/-- Inverse-action densities are jointly smooth in the forward parameter, without smooth inversion.
The measure identity specifies the density of the actual inverse pushforward. -/
theorem exists_smooth_inv_smul_density :
    ∃ R : G → M → ℝ,
      ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℝ) ∞
        (fun p : G × M ↦ R p.1 p.2) ∧
      (∀ g x, 0 < R g x) ∧
      ∀ g, Measure.map
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm μ =
          μ.withDensity (fun x ↦ ENNReal.ofReal (R g x)) := by
  /- First choose the canonical positive ratio of each actual pushforward.
  The local Jacobian density proved above identifies every ratio in a fixed
  chart. Its denominator is the fixed original density, which is positive;
  the quotient therefore proves joint smoothness for these same ratios. -/
  classical
  let W := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, W)
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ := by
    constructor
    exact contDiff_mul.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  let e (g : G) : M ≃ₘ⟮I, I⟯ M := (Diffeomorph.smul IG I ∞ g).symm
  let ν (g : G) := Measure.map (e g) μ
  let hν (g : G) : IsSmoothPositiveMeasure (n := n) (ν g) :=
    IsSmoothPositiveMeasure.map_diffeomorph μ (e g)
  let R (g : G) : M → ℝ := by
    letI := hν g
    exact smoothDensityRatio (n := n) μ (ν g)
  have hR (g : G) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (R g) := by
    let := hν g
    exact contMDiff_smoothDensityRatio (n := n) μ (ν g)
  have hpos (g : G) (x : M) : 0 < R g x := by
    let := hν g
    exact smoothDensityRatio_pos (n := n) μ (ν g) x
  have hmeasure (g : G) : ν g = μ.withDensity (fun x ↦ ENNReal.ofReal (R g x)) := by
    let := hν g
    exact (withDensity_smoothDensityRatio (n := n) μ (ν g)).symm
  refine ⟨R, ?_, hpos, hmeasure⟩
  intro p
  let c := chartAt W p.2
  have hc := chart_mem_atlas W p.2
  have hp : p.2 ∈ c.source := mem_chart_source W p.2
  have hcM := contMDiffOn_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  have hcS := contMDiffOn_symm_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  obtain ⟨a, ha, hapos, hameasure⟩ := hμ.exists_smooth_density c hc
  obtain ⟨w, hw, hwm⟩ := exists_smooth_inv_smul_chart_density (G := G) IG μ c hc
  -- Push a target weight through the same chart, retaining the source restriction.
  have hmapDensity (θ : Measure M) (f : M → W) (b : W → ENNReal)
      (hf : AEMeasurable f θ) (hb : AEMeasurable b (Measure.map f θ)) :
      (Measure.map f θ).withDensity b =
        Measure.map f (θ.withDensity (fun x ↦ b (f x))) := by
    ext A hA
    rw [withDensity_apply _ hA,
      Measure.map_apply_of_aemeasurable
        (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hA,
      withDensity_apply₀ _ (hf.nullMeasurable hA),
      ← lintegral_indicator hA, ← lintegral_indicator₀ (hf.nullMeasurable hA)]
    rw [lintegral_map' (hb.indicator hA) hf]
    congr 1
  have hlocal (g : G) : EqOn (fun z ↦ R g (c.symm z))
      (fun z ↦ w g z / a z) c.target := by
    have hr : ContDiffOn ℝ ∞ (fun z ↦ R g (c.symm z)) c.target :=
      ((hR g).comp_contMDiffOn hcS).contDiffOn
    have hwg : ContDiffOn ℝ ∞ (w g) c.target := by
      exact (hw.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun z hz ↦ ⟨mem_univ g, hz⟩)).contDiffOn
    let b (z : W) := ENNReal.ofReal (R g (c.symm z))
    have hb : AEMeasurable b (volume.restrict c.target) :=
      (hr.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
    have hcA := c.continuousOn.aemeasurable (μ := μ) c.open_source.measurableSet
    have hm : Measure.map c ((ν g).restrict c.source) =
        (Measure.map c (μ.restrict c.source)).withDensity b := by
      rw [hmeasure g, restrict_withDensity c.open_source.measurableSet,
        hmapDensity _ c b hcA (by
          rw [hameasure]
          exact hb.mono_ac (withDensity_absolutelyContinuous _ _))]
      congr 1
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
      dsimp only [b]
      rw [c.left_inv hx]
    have heq : (volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w g z)) =
        (volume.restrict c.target).withDensity
          (fun z ↦ ENNReal.ofReal (a z * R g (c.symm z))) := by
      rw [← (hwm g).2]
      change Measure.map c ((ν g).restrict c.source) = _
      rw [hm, hameasure, ← withDensity_mul₀
        (ha.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal hb]
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (ENNReal.ofReal_mul (hapos z hz).le).symm
    have hae := (withDensity_eq_iff_of_sigmaFinite
      (hwg.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
      ((ha.mul hr).continuousOn.aemeasurable
        c.open_target.measurableSet).ennreal_ofReal).mp heq
    have hpoint : EqOn (w g) (fun z ↦ a z * R g (c.symm z)) c.target := by
      apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure W)) _
        c.open_target hwg.continuousOn (ha.mul hr).continuousOn
      filter_upwards [hae, ae_restrict_mem c.open_target.measurableSet] with z hz hzc
      have hh := congrArg ENNReal.toReal hz
      simpa only [ENNReal.toReal_ofReal ((hwm g).1 z hzc).le,
        ENNReal.toReal_ofReal (mul_pos (hapos z hzc) (hpos g (c.symm z))).le] using hh
    intro z hz
    change R g (c.symm z) = w g z / a z
    rw [hpoint hz]
    exact (mul_div_cancel_left₀ _ (hapos z hz).ne').symm
  -- A fixed base chart now exhibits the canonical ratio as a smooth quotient.
  have hj : ContMDiffOn (IG.prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : G × W ↦ w z.1 z.2 / a z.2) (univ ×ˢ c.target) := by
    exact hw.div₀ (ha.contMDiffOn.comp contMDiffOn_snd (fun _ hz ↦ hz.2))
      (fun z hz ↦ (hapos z.2 hz.2).ne')
  have hchart := (hcM p.2 hp).contMDiffAt (c.open_source.mem_nhds hp)
  have hcomp := (hj.contMDiffAt ((isOpen_univ.prod c.open_target).mem_nhds
    ⟨mem_univ p.1, c.map_source hp⟩)).comp p
      (contMDiffAt_fst.prodMk (hchart.comp p contMDiffAt_snd))
  apply hcomp.congr_of_eventuallyEq
  have hN := continuous_snd.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hp)
  filter_upwards [hN] with z hz
  have h := hlocal z.1 (c.map_source hz)
  dsimp only at h
  change R z.1 z.2 = w z.1 (c z.2) / a (c z.2)
  simpa only [c.left_inv hz] using h

end AtiyahSinger

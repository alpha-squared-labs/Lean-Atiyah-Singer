/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Smooth positive densities under diffeomorphisms

Public module ID: M1161.

D02/P02: the actual pushforward measure is again a smooth positive density.
The coordinate formula uses the absolute inverse Jacobian determinant, so there
is no orientation hypothesis. This standard change-of-variables result supplies
the density transport used in SG III.13.4 and analytic-index naturality; it is a
project supplement, not a separately numbered lemma in that proof.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

include hM hN hT hT' hSC hSC'

/-- A smooth diffeomorphism pushes a positive smooth density to a positive smooth density. -/
theorem IsSmoothPositiveMeasure.map_diffeomorph (μ : Measure M)
    [hμ : IsSmoothPositiveMeasure (n := n) μ]
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N) :
    IsSmoothPositiveMeasure (n := n) (Measure.map e μ) := by
  /- Stage 1: on source and target coordinate neighborhoods, change variables
  by the coordinate diffeomorphism g. The new density is
  w(g⁻¹(y)) |det Dg⁻¹(y)|, not w(g⁻¹(y)) alone. The inverse function identity
  makes the determinant nonzero; its absolute value is smooth and positive.
  Stage 2: the local formulas agree on overlaps because they describe the same
  pushed-forward Borel measure. Glue on each target chart, using a countable
  coordinate cover to deduce the measure identity required by the definition.
  No orientation, compactness, or finite total mass is needed. In dimension
  zero the Jacobian factor is the determinant of the empty matrix, namely one. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, V)
  constructor
  intro c hc
  have hcM := contMDiffOn_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  have hcS := contMDiffOn_symm_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  let θ := Measure.map c ((Measure.map e μ).restrict c.source)
  -- Each source chart gives a coordinate Jacobian expression on its actual overlap.
  let d (x : M) := chartAt V x
  let t (x : M) : OpenPartialHomeomorph V V :=
    c.symm.trans (e.symm.toHomeomorph.toOpenPartialHomeomorph.trans (d x))
  choose a ha using fun x : M ↦ hμ.exists_smooth_density (d x) (chart_mem_atlas V x)
  have ht (x : M) : ContDiffOn ℝ ∞ (t x) (t x).source := by
    apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    have hcs := (hcS y hy.1).contMDiffAt (c.open_target.mem_nhds hy.1)
    have hes := e.symm.contMDiffAt.comp y hcs
    have hd := (contMDiffOn_chart (I := I) (n := (∞ : ℕ∞ω)) (x := x)
      _ hy.2.2).contMDiffAt ((d x).open_source.mem_nhds hy.2.2)
    exact (hd.comp y hes).contMDiffWithinAt
  have hts (x : M) : ContDiffOn ℝ ∞ (t x).symm (t x).target := by
    apply contMDiffOn_iff_contDiffOn.mp
    intro y hy
    have hds := (contMDiffOn_chart_symm (I := I) (n := (∞ : ℕ∞ω)) (x := x)
      y hy.1.1).contMDiffAt ((d x).open_target.mem_nhds hy.1.1)
    have he := e.contMDiffAt.comp y hds
    have hcs := (hcM _ hy.2).contMDiffAt (c.open_source.mem_nhds hy.2)
    exact (hcs.comp y he).contMDiffWithinAt
  -- The derivative of the inverse identity forces the coordinate Jacobian to be nonzero.
  have hdet (x : M) (y : V) (hy : y ∈ (t x).source) :
      (fderiv ℝ (t x) y).det ≠ 0 := by
    have hf := ((ht x) y hy).contDiffAt ((t x).open_source.mem_nhds hy)
    have hg := ((hts x) ((t x) y) ((t x).map_source hy)).contDiffAt
      ((t x).open_target.mem_nhds ((t x).map_source hy))
    have hinv : (fderiv ℝ (t x).symm ((t x) y)).comp (fderiv ℝ (t x) y) =
        ContinuousLinearMap.id ℝ V := by
      have hh := (hg.differentiableAt (by simp)).hasFDerivAt.comp y
        (hf.differentiableAt (by simp)).hasFDerivAt
      have hid : HasFDerivAt (fun z : V ↦ z)
          ((fderiv ℝ (t x).symm ((t x) y)).comp (fderiv ℝ (t x) y)) y := by
        apply hh.congr_of_eventuallyEq
        filter_upwards [(t x).open_source.mem_nhds hy] with z hz
        exact ((t x).left_inv hz).symm
      exact hid.unique (hasFDerivAt_id y)
    have hd := congrArg ContinuousLinearMap.det hinv
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
    exact right_ne_zero_of_mul_eq_one hd
  let q (x : M) (y : V) := |(fderiv ℝ (t x) y).det| * a x (t x y)
  have hqpos (x : M) (y : V) (hy : y ∈ (t x).source) : 0 < q x y := by
    exact mul_pos (abs_pos.mpr (hdet x y hy))
      ((ha x).2.1 _ ((t x).map_source hy).1.1)
  have hqsmooth (x : M) : ContDiffOn ℝ ∞ (q x) (t x).source := by
    intro y hy
    have hf := ((ht x) y hy).contDiffAt ((t x).open_source.mem_nhds hy)
    have hfd := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
    have hds : ContDiffAt ℝ ∞ (fun z ↦ (fderiv ℝ (t x) z).det) y := by
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
    have has := ((ha x).1 _ ((t x).map_source hy).1.1).contDiffAt
      ((d x).open_target.mem_nhds ((t x).map_source hy).1.1)
    exact ((hds.abs (hdet x y hy)).mul (has.comp y hf)).contDiffWithinAt
  -- Apply the Euclidean Jacobian theorem to the exact restricted pushforward measure.
  have hqmeasure (x : M) : θ.restrict (t x).source =
      (volume.restrict (t x).source).withDensity (fun y ↦ ENNReal.ofReal (q x y)) := by
    ext A hA
    let A₀ := A ∩ (t x).source
    have hA₀ : MeasurableSet A₀ := hA.inter (t x).open_source.measurableSet
    have hpre : MeasurableSet (c ⁻¹' A₀ ∩ c.source) := by
      simpa only [Set.domRestrict_eq, Set.preimage_comp,
        Set.image_preimage_eq_inter_range, Subtype.range_coe] using
        c.open_source.measurableSet.subtype_image
          (hA₀.preimage c.continuousOn.domRestrict.measurable)
    let B := t x '' A₀
    have hder (y : V) (hy : y ∈ A₀) :
        HasFDerivWithinAt (t x) (fderiv ℝ (t x) y) A₀ y :=
      (((ht x) y hy.2).contDiffAt ((t x).open_source.mem_nhds hy.2)
        |>.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    have hB : MeasurableSet B := measurable_image_of_fderivWithin hA₀ hder
      ((t x).injOn.mono Set.inter_subset_right)
    have hBsub : B ⊆ (d x).target := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((t x).map_source hy.2).1.1
    have hset : e ⁻¹' (c ⁻¹' A₀ ∩ c.source) = d x ⁻¹' B ∩ (d x).source := by
      ext z
      constructor
      · rintro ⟨hy, hcz⟩
        have hdz : z ∈ (d x).source := by
          have hh := hy.2.2.2
          change e.symm (c.symm (c (e z))) ∈ (d x).source at hh
          simpa only [c.left_inv hcz, e.symm_apply_apply] using hh
        refine ⟨⟨c (e z), hy, ?_⟩, hdz⟩
        change d x (e.symm (c.symm (c (e z)))) = d x z
        rw [c.left_inv hcz, e.symm_apply_apply]
      · rintro ⟨⟨y, hy, heq⟩, hz⟩
        have hdz : e.symm (c.symm y) ∈ (d x).source := hy.2.2.2
        have heq' : e.symm (c.symm y) = z := (d x).injOn hdz hz heq
        have hez : e z = c.symm y := by rw [← heq', e.apply_symm_apply]
        have hcy : c (e z) = y := by rw [hez, c.right_inv hy.2.1]
        constructor
        · change c (e z) ∈ A₀
          rw [hcy]
          exact hy
        · rw [hez]
          exact c.map_target hy.2.1
    have hleft : (θ.restrict (t x).source) A =
        ∫⁻ y in B, ENNReal.ofReal (a x y) ∂volume := by
      rw [Measure.restrict_apply hA]
      change (Measure.map c ((Measure.map e μ).restrict c.source)) A₀ = _
      rw [Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hA₀,
        Measure.restrict_apply' c.open_source.measurableSet,
        Measure.map_apply e.continuous.measurable hpre, hset]
      have hh := congrArg (fun η : Measure V ↦ η B) (ha x).2.2
      rw [Measure.map_apply_of_aemeasurable
        ((d x).continuousOn.aemeasurable (d x).open_source.measurableSet) hB,
        Measure.restrict_apply' (d x).open_source.measurableSet,
        withDensity_apply _ hB] at hh
      rw [hh, Measure.restrict_restrict hB,
        Set.inter_eq_left.mpr hBsub]
    rw [hleft, withDensity_apply _ hA, Measure.restrict_restrict hA]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA₀ hder
      ((t x).injOn.mono Set.inter_subset_right)]
    apply lintegral_congr
    intro y
    exact (ENNReal.ofReal_mul (abs_nonneg _) (q := a x (t x y))).symm
  -- Equality of local measures identifies the positive smooth densities on overlaps.
  have hqrestrict (x : M) : θ.restrict (t x).source =
      (volume.withDensity (fun y ↦ ENNReal.ofReal (q x y))).restrict (t x).source := by
    rw [restrict_withDensity (t x).open_source.measurableSet]
    exact hqmeasure x
  have hcompat (x z : M) : Set.EqOn (q x) (q z) ((t x).source ∩ (t z).source) := by
    let U := (t x).source ∩ (t z).source
    have hU : IsOpen U := (t x).open_source.inter (t z).open_source
    have hx := Measure.restrict_congr_mono (s := U) Set.inter_subset_left (hqrestrict x)
    have hz := Measure.restrict_congr_mono (s := U) Set.inter_subset_right (hqrestrict z)
    have heq : (volume.restrict U).withDensity (fun y ↦ ENNReal.ofReal (q x y)) =
        (volume.restrict U).withDensity (fun y ↦ ENNReal.ofReal (q z y)) := by
      simpa only [restrict_withDensity hU.measurableSet] using hx.symm.trans hz
    have hxc := (hqsmooth x).continuousOn.mono (show U ⊆ (t x).source from
      Set.inter_subset_left)
    have hzc := (hqsmooth z).continuousOn.mono (show U ⊆ (t z).source from
      Set.inter_subset_right)
    have hae := (withDensity_eq_iff_of_sigmaFinite
      (hxc.aemeasurable hU.measurableSet).ennreal_ofReal
      (hzc.aemeasurable hU.measurableSet).ennreal_ofReal).mp heq
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure V)) _ hU hxc hzc
    filter_upwards [hae, ae_restrict_mem hU.measurableSet] with y hy hyU
    have hh := congrArg ENNReal.toReal hy
    simpa only [ENNReal.toReal_ofReal (hqpos x y hyU.1).le,
      ENNReal.toReal_ofReal (hqpos z y hyU.2).le] using hh
  let p (y : V) := e.symm (c.symm y)
  let w (y : V) := q (p y) y
  have hp (y : V) (hy : y ∈ c.target) : y ∈ (t (p y)).source :=
    ⟨hy, Set.mem_univ _, mem_chart_source V (p y)⟩
  have hwlocal (x : M) : Set.EqOn w (q x) (t x).source := by
    intro y hy
    exact (hcompat x (p y) ⟨hy, hp y hy.1⟩).symm
  have hwsmooth : ContDiffOn ℝ ∞ w c.target := by
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    exact ⟨(t (p y)).source, (t (p y)).open_source, hp y hy,
      ((hqsmooth (p y)).congr (hwlocal (p y))).mono Set.inter_subset_right⟩
  have hwpos (y : V) (hy : y ∈ c.target) : 0 < w y := hqpos (p y) y (hp y hy)
  refine ⟨w, hwsmooth, hwpos, ?_⟩
  -- A countable overlap cover upgrades the local identities to the full target chart.
  have hcover : ⋃ x : M, (t x).source = c.target := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      exact hx.1
    · intro y hy
      exact Set.mem_iUnion.mpr ⟨p y, hp y hy⟩
  obtain ⟨S, hS, hScov⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : M ↦ (t x).source) (fun x ↦ (t x).open_source)
  have hcover' : ⋃ x : S, (t x.val).source = c.target := by
    simpa only [Set.iUnion_subtype] using hScov.trans hcover
  let : Countable S := hS.to_subtype
  have hmeasure : θ.restrict c.target =
      ((volume.restrict c.target).withDensity (fun y ↦ ENNReal.ofReal (w y))).restrict
        c.target := by
    rw [← hcover', Measure.restrict_iUnion_congr]
    intro x
    rw [hcover', hqmeasure x.val, restrict_withDensity (t x.val).open_source.measurableSet,
      Measure.restrict_restrict (t x.val).open_source.measurableSet,
      Set.inter_eq_left.mpr (show (t x.val).source ⊆ c.target from fun _ hy ↦ hy.1)]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (t x.val).open_source.measurableSet] with y hy
    exact congrArg ENNReal.ofReal ((hwlocal x.val hy).symm)
  have hθ : θ.restrict c.target = θ := by
    dsimp only [θ]
    rw [Measure.restrict_map_of_aemeasurable
      (c.continuousOn.aemeasurable c.open_source.measurableSet) c.open_target.measurableSet,
      Measure.restrict_restrict' c.open_source.measurableSet]
    congr 1
    have hh : c ⁻¹' c.target ∩ c.source = c.source :=
      Set.inter_eq_right.mpr (fun y hy ↦ c.map_source hy)
    rw [hh]
  rw [hθ, restrict_withDensity c.open_target.measurableSet,
    Measure.restrict_restrict c.open_target.measurableSet, Set.inter_self] at hmeasure
  exact hmeasure


end AtiyahSinger

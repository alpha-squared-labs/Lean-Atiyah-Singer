/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Geometry.CotangentMetric

import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Quantization with prescribed compact base support

Public module ID: M0347.

A03/UL03: the compactly supported correction in SG III.13.4, pp.248--249,
using III.3.8 and the local realization argument preceding III.13 Lemma 13.3.
The base need not be compact or of finite topological type. The input is already
specified homogeneous data or a full symbol supported over a compact base set.
This does not construct a relative representative of an arbitrary K class.

The finite pieces are existing actual Schwartz operators transported to smooth
bundle sections. Their globalSymbol sum is a principal representative, not an
exact full symbol of their section action. No new noncompact PDO carrier is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

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

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hE hF


set_option linter.unusedSectionVars false in
/-- Homogeneous data with compact base support admit a supported full-symbol regularization. -/
theorem exists_compactBase_regularization (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a)
    (K : Set M) (hK : IsCompact K)
    (hzero : ∀ x, x ∉ K → ∀ ξ, ξ ≠ 0 → a x ξ = 0)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ b : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
      (∀ x, x ∉ K → ∀ ξ, b.val x ξ = 0) ∧
      (∀ x ξ, 1 ≤ g.length x ξ → b.val x ξ = a x ξ) := by
  /- Cut off the supplied metric length below one half, preserving the original
  symbol whenever that length is at least one. Coordinate smoothness follows from
  the native derivative and cotangent Hom charts; the cutoff kills a whole zero
  neighborhood. On compact coordinate unit spheres the metric has a positive
  minimum. Thus this cutoff differs from the standard homogeneous regularization
  only in a bounded frequency region, which has every symbol order. The original
  compact base support is retained throughout, without compactness of the manifold. -/
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let θ (t : ℝ) := 1 - φ t
  have hθ : ContDiff ℝ ∞ θ := contDiff_const.sub φ.contDiff
  have hθzero (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) : θ t = 0 := by
    change 1 - φ t = 0
    rw [φ.one_of_mem_closedBall (by simpa [φ, Real.dist_eq, abs_of_nonneg ht] using ht')]
    exact sub_self _
  have hθone (t : ℝ) (ht : 1 ≤ t) : θ t = 1 := by
    change 1 - φ t = 1
    rw [φ.zero_of_le_dist (by
      simpa [φ, Real.dist_eq, abs_of_nonneg (show 0 ≤ t by linarith)] using ht)]
    exact sub_zero _
  let b : GlobalSymbolFunction (n := n) E F := fun x ξ ↦ (θ (g.length x ξ) : ℂ) • a x ξ
  have hb : IsGlobalSymbol (n := n) (r := r) (q := q) E F m b := by
    intro c hc e f _ _
    let V := symbolChartDomain E F c e f
    let p := globalSymbolInChart E F a c e f
    let ℓ (z η : H) := g.length (c.symm z) (covectorFromChart c (c.symm z) η)
    have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
    -- The coordinate covector map retains the actual cotangent topology and metric pairing.
    have hquad : ContDiffOn ℝ ∞ (fun z : H × H ↦
        g.inner (c.symm z.1) (covectorFromChart c (c.symm z.1) z.2)
          (covectorFromChart c (c.symm z.1) z.2)) (c.target ×ˢ Set.univ) := by
      let H := EuclideanSpace ℝ (Fin n)
      let I := 𝓘(ℝ, H)
      intro z hz
      have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
      have hb : ContMDiffAt 𝓘(ℝ, H × H) I ∞ (fun y : H × H ↦ c.symm y.1) z :=
        (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1).comp z contDiffAt_fst.contMDiffAt
      have hd := ((contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hz.1)).mfderiv_const
        (m := (∞ : WithTop ℕ∞)) (by simp)).comp z hb
      have hlift : ContMDiffAt 𝓘(ℝ, H × H) (I.prod 𝓘(ℝ, CotangentModel n)) ∞
          (fun y : H × H ↦ (⟨c.symm y.1, covectorFromChart c (c.symm y.1) y.2⟩ :
            CotangentTotalSpace (n := n) (M := M))) z := by
        apply (contMDiffAt_hom_bundle _).mpr
        refine ⟨hb, ?_⟩
        have hi : ContMDiffAt 𝓘(ℝ, H × H) 𝓘(ℝ, H →L[ℝ] ℝ) ∞
            (fun y : H × H ↦ innerSL ℝ y.2) z :=
          (innerSL ℝ).contMDiff.contMDiffAt.comp z contDiffAt_snd.contMDiffAt
        have h := hi.clm_comp hd
        apply h.congr_of_eventuallyEq
        apply Filter.Eventually.of_forall
        intro y
        apply ContinuousLinearMap.ext
        intro v
        have hscalar : (trivializationAt ℝ (fun _ : M ↦ ℝ) (c.symm z.1)).continuousLinearMapAt
            ℝ (c.symm y.1) = ContinuousLinearMap.id ℝ ℝ := by
          change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (c.symm y.1) = _
          exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
        simp only [Function.comp_apply, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
          Function.id_def, TangentBundle.continuousLinearMapAt_model_space,
          ContinuousLinearMap.one_def, hscalar,
          covectorFromChart, ContinuousLinearMap.comp_apply]
        rfl
      have hquad := (g.contMDiff.contMDiffAt.comp z hb).clm_bundle_apply₂
        (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hlift hlift
      have hscalar := (contMDiffAt_totalSpace.mp hquad).2
      exact (show ContDiffAt ℝ ∞ _ z from by simpa using hscalar.contDiffAt).contDiffWithinAt
    have hlen : ContinuousOn (Function.uncurry ℓ) (c.target ×ˢ Set.univ) :=
      hquad.continuousOn.sqrt
    have hne (z η : H) (hz : z ∈ c.target) (hη : η ≠ 0) :
        covectorFromChart c (c.symm z) η ≠ 0 := by
      intro heq
      have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
      rw [heq] at h
      apply hη
      rw [← h]
      ext j
      rfl
    have hlenzero (z : H) : ℓ z 0 = 0 := by
      apply (g.length_eq_zero_iff _ _).mpr
      ext v
      change inner ℝ (0 : H) _ = 0
      exact inner_zero_left _
    have hscale (z η : H) (t : ℝ) : ℓ z (t • η) = |t| * ℓ z η := by
      change g.length (c.symm z) (covectorFromChart c (c.symm z) (t • η)) = _
      rw [← g.length_smul]
      congr 1
      ext v
      change inner ℝ (t • η) _ = t * inner ℝ η _
      exact real_inner_smul_left _ _ _
    have hcoord : globalSymbolInChart E F b c e f =
        fun z η ↦ (θ (ℓ z η) : ℂ) • p z η := by
      ext z η v
      simp [globalSymbolInChart, b, ℓ, p]
    -- Near zero the same radial cutoff vanishes; off zero the metric length is smooth.
    have hreg : ContDiffOn ℝ ∞
        (Function.uncurry (globalSymbolInChart E F b c e f)) (V ×ˢ Set.univ) := by
      rw [hcoord]
      intro z hz
      by_cases hη : z.2 = 0
      · have hsmall : ∀ᶠ y in 𝓝 z, ℓ y.1 y.2 < 1 / 2 :=
          (hlen.continuousAt ((c.open_target.prod isOpen_univ).mem_nhds ⟨hz.1.1.1, trivial⟩))
            (Iio_mem_nhds (by
              change ℓ z.1 z.2 < (1 / 2 : ℝ)
              rw [hη, hlenzero]
              norm_num))
        apply ContDiffAt.contDiffWithinAt
        apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r) →L[ℂ]
          EuclideanSpace ℂ (Fin q)))).congr_of_eventuallyEq
        filter_upwards [hsmall] with y hy
        change (θ (ℓ y.1 y.2) : ℂ) • p y.1 y.2 = 0
        rw [hθzero _ (g.length_nonneg _ _) hy.le, Complex.ofReal_zero, zero_smul]
      · have hl : ContDiffAt ℝ ∞ (Function.uncurry ℓ) z :=
          (Real.contDiffAt_sqrt (ne_of_gt (g.pos _ _ (hne z.1 z.2 hz.1.1.1 hη)))).comp z
            (hquad.contDiffAt ((c.open_target.prod isOpen_univ).mem_nhds ⟨hz.1.1.1, trivial⟩))
        have hfactor := Complex.ofRealCLM.contDiff.contDiffAt.comp z (hθ.contDiffAt.comp z hl)
        have hp := (hs c hc e f).contDiffAt ((hV.prod isOpen_ne).mem_nhds ⟨hz.1, hη⟩)
        exact (hfactor.smul hp).contDiffWithinAt
    refine ⟨hreg, ?_⟩
    intro C hCV hC i j
    obtain ⟨C', hC', hCC', hC'V⟩ := exists_compact_between hC hV hCV
    have hC't : C' ⊆ c.target := fun z hz ↦ (hC'V hz).1.1
    -- A compact coordinate unit sphere gives one positive metric lower bound over C'.
    have hcompact := hC'.prod (isCompact_sphere (0 : H) 1)
    have hcont : ContinuousOn (Function.uncurry ℓ) (C' ×ˢ Metric.sphere (0 : H) 1) :=
      hlen.mono (Set.prod_mono hC't (Set.subset_univ _))
    obtain ⟨δ, hδ, hlow⟩ := hcompact.exists_forall_le' hcont (a := 0) (by
      intro z hz
      exact g.length_pos _ _ (hne z.1 z.2 (hC't hz.1)
        (by intro hz'; simpa [hz'] using hz.2)))
    have hrecovery (z : H) (hz : z ∈ C') (η : H) (hη : δ⁻¹ ≤ ‖η‖) :
        globalSymbolInChart E F b c e f z η = p z η := by
      have hn : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hδ) hη
      let u := ‖η‖⁻¹ • η
      have hu : u ∈ Metric.sphere (0 : H) 1 := by
        simpa [u, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.mp hn)
      have hηeq : ‖η‖ • u = η := by simp [u, smul_smul, hn.ne']
      have hlenη : ℓ z η = ‖η‖ * ℓ z u := by
        conv_lhs => rw [← hηeq]
        rw [hscale, abs_of_nonneg (norm_nonneg _)]
      have hone : 1 ≤ ℓ z η := by
        rw [hlenη]
        calc
          1 = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
          _ ≤ ‖η‖ * δ := mul_le_mul_of_nonneg_right hη hδ.le
          _ ≤ ‖η‖ * ℓ z u := mul_le_mul_of_nonneg_left (hlow (z, u) ⟨hz, hu⟩) hn.le
      rw [hcoord]
      change (θ (ℓ z η) : ℂ) • p z η = p z η
      rw [hθone _ hone, Complex.ofReal_one, one_smul]
    -- The deviation from the standard homogeneous cutoff has bounded frequency support.
    have hint : interior C' ⊆ V := interior_subset.trans hC'V
    have hstandard := isSymbol_frequencyCutoffSymbol V hV m p (hs c hc e f)
      (hh.in_chart c hc e f)
    let d := globalSymbolInChart E F b c e f - frequencyCutoffSymbol p
    have hd : ContDiffOn ℝ ∞ (Function.uncurry d) (interior C' ×ˢ Set.univ) :=
      (hreg.mono (Set.prod_mono hint Set.Subset.rfl)).sub
        (hstandard.1.mono (Set.prod_mono hint Set.Subset.rfl))
    have hsupp : ∀ z ∈ interior C', ∀ η, max δ⁻¹ 1 ≤ ‖η‖ → d z η = 0 := by
      intro z hz η hη
      change globalSymbolInChart E F b c e f z η - frequencyCutoffSymbol p z η = 0
      rw [hrecovery z (interior_subset hz) η ((le_max_left _ _).trans hη),
        frequencyCutoffSymbol_eq_of_one_le_norm p z η ((le_max_right _ _).trans hη)]
      exact sub_self _
    have hdSymbol := isSmoothingSymbol_of_frequency_support isOpen_interior d (max δ⁻¹ 1)
      hd hsupp m
    have hstandardLocal : IsSymbol (interior C') m (frequencyCutoffSymbol p) := by
      refine ⟨hstandard.1.mono (Set.prod_mono hint Set.Subset.rfl), ?_⟩
      intro L hL hLc u v
      exact hstandard.2 L (hL.trans hint) hLc u v
    have hsum := hdSymbol.add isOpen_interior hstandardLocal
    have heq : d + frequencyCutoffSymbol p = globalSymbolInChart E F b c e f :=
      sub_add_cancel _ _
    rw [heq] at hsum
    exact hsum.2 C hCC' hC i j
  -- The closed base support stays inside the original compact K, including frequency zero.
  have hsupport : closure {x | ∃ ξ, b x ξ ≠ 0} ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    rintro x ⟨ξ, hbξ⟩
    by_contra hx
    apply hbξ
    change (θ (g.length x ξ) : ℂ) • a x ξ = 0
    by_cases hξ : ξ = 0
    · rw [hξ, (g.length_eq_zero_iff x 0).mpr rfl, hθzero 0 le_rfl (by norm_num),
        Complex.ofReal_zero, zero_smul]
    · rw [hzero x hx ξ hξ, smul_zero]
  refine ⟨⟨b, hb⟩, ?_, ?_⟩
  · intro x hx ξ
    by_contra h
    exact hx (hsupport (subset_closure ⟨ξ, h⟩))
  · intro x ξ hξ
    change (θ (g.length x ξ) : ℂ) • a x ξ = a x ξ
    rw [hθone _ hξ, Complex.ofReal_one, one_smul]

/-- A compactly base-supported symbol is recovered as the globalSymbol sum of finite pieces
supported in any prescribed neighborhood. -/
theorem exists_supported_quantization_pieces {m : ℝ}
    (b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (K : Set M) (hK : IsCompact K) (hzero : ∀ x, x ∉ K → ∀ ξ, b.val x ξ = 0)
    (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m),
      (∑ j, (L j).globalSymbol) = b ∧
      ∃ C : Set M, IsCompact C ∧ C ⊆ U ∧
        ∀ j, (L j).chart.symm ''
          (tsupport (L j).output.cutoff ∪ tsupport (L j).input.cutoff) ⊆ C := by
  /- Refine the common atlas to relatively compact patches inside the prescribed U.
  A finite smooth partition on K has compact support in those patches. Choose a
  larger output plateau in each common chart, quantize the same localized symbol,
  and retain both actual cutoffs. The partition identity on K and b=0 off K recover
  the globalSymbol sum exactly; the finite transported supports give a compact C. -/
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  -- Choose one finite cover by the common source of the base chart and both frames.
  let c (x : K) := chartAt (EuclideanSpace ℝ (Fin n)) (x : M)
  let e (x : K) := trivializationAt (EuclideanSpace ℂ (Fin r)) E (x : M)
  let f (x : K) := trivializationAt (EuclideanSpace ℂ (Fin q)) F (x : M)
  let O (x : K) := (((c x).source ∩ (e x).baseSet) ∩ (f x).baseSet) ∩ U
  have hopen (x : K) : IsOpen (O x) :=
    (((c x).open_source.inter (e x).open_baseSet).inter (f x).open_baseSet).inter hU
  have hxO (x : K) : (x : M) ∈ O x :=
    ⟨⟨⟨mem_chart_source _ (x : M), mem_baseSet_trivializationAt _ E (x : M)⟩,
      mem_baseSet_trivializationAt _ F (x : M)⟩, hKU x.property⟩
  have hshrink (x : K) : ∃ V : Set M, IsOpen V ∧ (x : M) ∈ V ∧
      closure V ⊆ O x ∧ IsCompact (closure V) := by
    obtain ⟨V, hV, hxV, hVO, hVc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := (x : M))) (hopen x) (Set.singleton_subset_iff.mpr (hxO x))
    exact ⟨V, hV, hxV (Set.mem_singleton _), hVO, hVc⟩
  choose V₀ hV₀ hxV₀ hV₀O hV₀c using hshrink
  have hcover : K ⊆ ⋃ x : K, V₀ x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV₀ ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V₀ hV₀ hcover
  let index : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := V₀ (index j)
  have hfinitecover : K ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) hK.isClosed V
    (fun j ↦ hV₀ (index j)) hfinitecover
  have hρcompact (j : Fin s.card) : HasCompactSupport (ρ j) :=
    (hV₀c (index j)).of_isClosed_subset (isClosed_tsupport _) (fun x hx ↦
      subset_closure (hρ j hx))
  have hρO (j : Fin s.card) : tsupport (ρ j) ⊆ O (index j) :=
    fun x hx ↦ hV₀O (index j) (subset_closure (hρ j hx))
  -- Zero-extend each actual partition weight into its chosen Euclidean chart.
  let χ (j : Fin s.card) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if z ∈ (c (index j)).target then ρ j ((c (index j)).symm z) else 0
  let Kc (j : Fin s.card) := (c (index j)) '' tsupport (ρ j)
  have hKc (j : Fin s.card) : IsCompact (Kc j) :=
    (hρcompact j).image_of_continuousOn
      ((c (index j)).continuousOn.mono (fun x hx ↦ (hρO j hx).1.1.1))
  have hχ (j : Fin s.card) : tsupport (χ j) ⊆ Kc j := by
    apply closure_minimal ?_ (hKc j).isClosed
    intro z hz
    have ht : z ∈ (c (index j)).target := by
      by_contra ht
      exact hz (by simp [χ, ht])
    have hr : (c (index j)).symm z ∈ tsupport (ρ j) := by
      by_contra hr
      exact hz (by simp [χ, ht, image_eq_zero_of_notMem_tsupport hr])
    exact ⟨(c (index j)).symm z, hr, (c (index j)).right_inv ht⟩
  have hχcompact (j : Fin s.card) : HasCompactSupport (χ j) :=
    (hKc j).of_isClosed_subset (isClosed_tsupport _) (hχ j)
  have hχsmooth (j : Fin s.card) : ContDiff ℝ ∞ (χ j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ Kc j
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := (hρO j hx).1.1.1
      have ht := (c (index j)).map_source hxsource
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (chart_mem_atlas _ ((index j : K) : M))) ht
      have hlocal := ((ρ j).contMDiff.contMDiffAt.comp _ hchart).contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(c (index j)).open_target.mem_nhds ht] with y hy
      simp only [χ, ite_eq_left hy]
      rfl
    · -- The compact coordinate support is closed, so the same extension is locally zero outside it.
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hKc j).isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχ j h))
  let D (j : Fin s.card) :=
    (c (index j)).target ∩ (c (index j)).symm ⁻¹'
      ((e (index j)).baseSet ∩ (f (index j)).baseSet ∩ U)
  have hD (j : Fin s.card) : IsOpen (D j) :=
    (c (index j)).continuousOn_symm.isOpen_inter_preimage (c (index j)).open_target
      ((e (index j)).open_baseSet.inter (f (index j)).open_baseSet |>.inter hU)
  have hKD (j : Fin s.card) : Kc j ⊆ D j := by
    rintro z ⟨x, hx, rfl⟩
    have hu := hρO j hx
    refine ⟨(c (index j)).map_source hu.1.1.1, ?_⟩
    change (c (index j)).symm ((c (index j)) x) ∈
      (e (index j)).baseSet ∩ (f (index j)).baseSet ∩ U
    rw [(c (index j)).left_inv hu.1.1.1]
    exact ⟨⟨hu.1.1.2, hu.1.2⟩, hu.2⟩
  -- A relatively compact intermediate open set supplies the output cutoff without changing χ.
  have houtput (j : Fin s.card) :
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ D j ∧ ∀ z ∈ tsupport (χ j), ψ z = 1 := by
    obtain ⟨W, hW, hKW, hWD, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure (hKc j) (hD j) (hKD j)
    obtain ⟨ψ, hψ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW (hKc j).isClosed hKW
    have hts : tsupport ψ = closure W := congrArg closure hsupp
    refine ⟨ψ, hψ, ?_, ?_, ?_⟩
    · change IsCompact (tsupport ψ)
      rwa [hts]
    · rwa [hts]
    · intro z hz
      exact (hone z).mp (hχ j hz)
  choose ψ hψsmooth hψcompact hψsupport hψone using houtput
  let patch (j : Fin s.card) : QuantizationPatch (n := n) (r := r) (q := q) E F :=
    { chart := c (index j)
      chart_mem_atlas := chart_mem_atlas _ ((index j : K) : M)
      input :=
        { frame := e (index j)
          frame_mem_atlas := inferInstance
          cutoff := χ j
          smooth_cutoff := hχsmooth j
          compact_support := hχcompact j
          support_subset := fun z hz ↦ ⟨(hKD j (hχ j hz)).1, (hKD j (hχ j hz)).2.1.1⟩ }
      output :=
        { frame := f (index j)
          frame_mem_atlas := inferInstance
          cutoff := ψ j
          smooth_cutoff := hψsmooth j
          compact_support := hψcompact j
          support_subset := fun z hz ↦ ⟨(hψsupport j hz).1, (hψsupport j hz).2.1.2⟩ }
      input_support_in_output_frame := fun z hz ↦ (hKD j (hχ j hz)).2.1.2
      output_support_in_input_frame := fun z hz ↦ (hψsupport j hz).2.1.1
      output_eq_one := hψone j }
  -- The same weights are recovered exactly, including the zero branch off each chart.
  have hweight (x : M) (j : Fin s.card) : (patch j).weight x = ρ j x := by
    by_cases hx : x ∈ (c (index j)).source
    · simp only [QuantizationPatch.weight, patch, ite_eq_left hx, χ,
        ite_eq_left ((c (index j)).map_source hx), (c (index j)).left_inv hx]
    · have hzero : ρ j x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρO j h).1.1.1)
      simp only [QuantizationPatch.weight, patch, ite_eq_right hx, hzero]
  refine ⟨s.card, fun j ↦ (patch j).toPiece b, ?_, ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_sum]
    change (∑ j, ((patch j).toPiece b).globalSymbolFunction) = b.val
    funext x ξ
    simp only [Finset.sum_apply, QuantizationPatch.globalSymbolFunction_toPiece, hweight]
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      have hsum : ∑ j, ρ j x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hsum, Complex.ofReal_one, one_smul]
    · simp [hzero x hx ξ]
  · -- The same finite union controls both input and output supports inside U.
    let C := ⋃ j : Fin s.card, (c (index j)).symm ''
      (tsupport (ψ j) ∪ tsupport (χ j))
    have hsupports (j : Fin s.card) :
        tsupport (ψ j) ∪ tsupport (χ j) ⊆ D j := by
      intro z hz
      exact hz.elim (fun h ↦ hψsupport j h) (fun h ↦ hKD j (hχ j h))
    refine ⟨C, ?_, ?_, ?_⟩
    · apply isCompact_iUnion
      intro j
      exact ((hψcompact j).union (hχcompact j)).image_of_continuousOn
        ((c (index j)).continuousOn_symm.mono (fun z hz ↦ (hsupports j hz).1))
    · intro x hx
      obtain ⟨j, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
      exact (hsupports j hz).2.2
    · intro j
      exact Set.subset_iUnion (fun j : Fin s.card ↦ (c (index j)).symm ''
        (tsupport (ψ j) ∪ tsupport (χ j))) j

end AtiyahSinger

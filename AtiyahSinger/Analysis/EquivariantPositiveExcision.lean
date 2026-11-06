/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantOpenLocalizedRepresentative
public import AtiyahSinger.Analysis.EquivariantRelativeAnalyticComparison
public import AtiyahSinger.Analysis.EquivariantRelativeExcisionClass
public import AtiyahSinger.Geometry.EquivariantNativeRelativeExtension
public import AtiyahSinger.Geometry.DiffeomorphBundlePullback
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Geometry.OpenEmbeddingBundleIso
public import AtiyahSinger.Geometry.SmoothEquivariantPullback
public import AtiyahSinger.Topology.EquivariantControlledOpenClass
public import AtiyahSinger.Topology.EquivariantPullbackTransport

/-!
# Positive-dimensional equivariant analytic excision

Public module ID: M0553.

An arbitrary common-open class is localized in the original compact ambient manifold.
One finite quantization and one specified relative extension supply the same
kernel comparison and the same controlled K class on the second compact manifold.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace Topology
open scoped Manifold ContDiff Pointwise

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [FiniteDimensional ℝ VG] [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 6000000 in
-- Localize the arbitrary class, then retain one finite correction through all comparisons.
/-- Positive-dimensional common-open extension preserves the original full analytic index. -/
theorem equivariantAnalyticIndexMap_open_excision_of_pos
    (hn : 0 < n) (U : Opens M) (V : Opens N)
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    [MulAction G V] [ContinuousSMul G V]
    [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G V]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hV : ∀ (g : G) (x : V), ((g • x : V) : N) = g • x.val)
    (hUi : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U)
    (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
    (he : ∀ (g : G) (x : U), (e (g • x)).val = g • (e x).val) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let f : C(CotangentTotalSpace (n := n) (M := U),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
    let g : C(CotangentTotalSpace (n := n) (M := U),
        CotangentTotalSpace (n := n) (M := N)) :=
      ⟨fun z ↦ cotangentOpenInclusion V (cotangentDiffeomorph e z),
        (isOpenEmbedding_cotangentOpenInclusion V).continuous.comp
          (cotangentDiffeomorph e).continuous⟩
    ∀ (hfg : ∀ (a : G) (z : CotangentTotalSpace (n := n) (M := U)),
        f (a • z) = a • f z)
      (hgg : ∀ (a : G) (z : CotangentTotalSpace (n := n) (M := U)),
        g (a • z) = a • g z)
      (a : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := U))),
      equivariantAnalyticIndexMap (VG := VG) (G := G) (M := M)
          (equivariantSupportTripleKZeroOpenPushforward f
            (isOpenEmbedding_cotangentOpenInclusion U) hfg a) =
        equivariantAnalyticIndexMap (VG := VG) (G := G) (M := N)
          (equivariantSupportTripleKZeroOpenPushforward g
            ((isOpenEmbedding_cotangentOpenInclusion V).comp
              (cotangentDiffeomorph e).isOpenEmbedding) hgg a) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  dsimp only
  intro hfg hgg a
  let IG := 𝓘(ℝ, VG)
  let X := CotangentTotalSpace (n := n) (M := U)
  let Y := CotangentTotalSpace (n := n) (M := M)
  let Z := CotangentTotalSpace (n := n) (M := N)
  let f : C(X, Y) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  let g : C(X, Z) :=
    ⟨fun z ↦ cotangentOpenInclusion V (cotangentDiffeomorph e z),
      (isOpenEmbedding_cotangentOpenInclusion V).continuous.comp
        (cotangentDiffeomorph e).continuous⟩
  have hf : IsOpenEmbedding f := isOpenEmbedding_cotangentOpenInclusion U
  have hg : IsOpenEmbedding g := (isOpenEmbedding_cotangentOpenInclusion V).comp
    (cotangentDiffeomorph e).isOpenEmbedding
  have hfrange (z : Y) : z ∈ Set.range f ↔ z.proj ∈ U := by
    constructor
    · rintro ⟨w, rfl⟩
      exact w.proj.property
    · intro hz
      exact ⟨⟨⟨z.proj, hz⟩, z.snd⟩, rfl⟩
  -- The stable extension and controlled localization preserve the arbitrary original open class.
  obtain ⟨a₀, ha₀⟩ := equivariantSupportBundleTriple_kZeroClass_surjective (G := G) (X := X) a
  obtain ⟨A, hArange, hAa⟩ := a₀.exists_openExtension f hf hfg
  have hAclass : (A.openRestrict f hf hfg hArange).kZeroClass = a :=
    ((A.openRestrict f hf hfg hArange).kZeroClass_eq_of_isStablyIsomorphic a₀ hAa).trans ha₀
  obtain ⟨K, hK, hKU, hKi, ρ, hT, σE, hσE, hσEvalue, F, hF, σF, hσF,
      c, hc, hcg, hcext, s, hs, hsg, hsext, b, hbcontrol, hbboundary, hb, hbrange,
      hbclass⟩ := exists_equivariant_localized_relative_symbol_of_open
    hn U hUi A f hf hfg hArange hfrange
  let := hT
  let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
  let E : SmoothFiniteComplexBundle (n := n) M := { rank := ρ.dimension, Fiber := T }
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let cL (x : M) : E.Fiber x →L[ℂ] F.Fiber x := (c.linearMap x).toContinuousLinearMap
  obtain ⟨g₀, _hg₀⟩ :=
    exists_invariant_smoothCotangentMetric (G := G) (n := n) (M := M) IG
  obtain ⟨q, _hqzero, hqprincipal, k₀, P, hPq, L₀, hL₀, hKL₀, hL₀U,
      hPpieces, hPsupport, _hPoutside⟩ := exists_relative_quantization_pieces E F s cL hc
    K hK (fun x hx ξ ↦ ContinuousLinearMap.ext (hsext x hx ξ)) U U.isOpen hKU g₀
  let L := (Set.univ : Set G) • L₀
  obtain ⟨hL, hL₀L, hLi⟩ := compact_saturation_properties (G := G) L₀ hL₀
  have hKL : K ⊆ L := hKL₀.trans hL₀L
  have hLU : L ⊆ U := by
    rintro _ ⟨a, _, x, hx, rfl⟩
    exact (hUi a x).mpr (hL₀U hx)
  have hpieces (j : Fin k₀) : (P j).chart.symm ''
      (tsupport (P j).input.cutoff ∪ tsupport (P j).output.cutoff) ⊆ L :=
    (hPpieces j).trans hL₀L
  have hprincipal (x : M) (ξ : CotangentFiber (n := n) x) (hξ : 1 ≤ g₀.length x ξ) :
      (∑ j, (P j).globalSymbol).val x ξ + cL x = s.val x ξ := by
    rw [hPq]
    exact hqprincipal x ξ hξ
  have hsupport : HasSectionOperatorSupport L (∑ j, (P j).toLinearMap) :=
    ⟨fun u ↦ (hPsupport.1 u).trans hL₀L,
      fun u hu ↦ hPsupport.2 u (hu.mono_right hL₀L)⟩
  -- The same source pairings, density and finite representation determine the target geometry.
  obtain ⟨μ, hμ, hμi⟩ := exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨h, hhi⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, hki⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨E', F', _hE', _hF', α, β, hα, hβ, d, hd, hcd, hdext,
      h', k', ν, hν, W, hLW, hWV, hαmetric, hβmetric, hmeasure,
      τE, τF, hτE, hτF, hαg, hβg, hdg⟩ :=
    exists_equivariant_native_relative_excision_data ρ hT F hF U V hU hV e he
      K L hK hL hKL hLU hKi μ σE σF hσE hσF hσEvalue c hc hcg hcext h k
  let := hν
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let j : C(U, N) := (ContinuousMap.subtypeVal (V : Set N)).comp ⟨e, e.continuous⟩
  let LU : Set U := (Subtype.val : U → M) ⁻¹' L
  let LN : Set N := j '' LU
  have hLUc : IsCompact LU := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    hL (fun x hx ↦ ⟨⟨x, hLU hx⟩, rfl⟩)
  have hLN : IsCompact LN := hLUc.image j.continuous
  have hLNV : LN ⊆ V := by
    rintro _ ⟨x, _, rfl⟩
    exact (e x).property
  have hpreimage : e ⁻¹' ((Subtype.val : V → N) ⁻¹' LN) = LU := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (e.injective (Subtype.ext hxy)) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hμν : MeasureTheory.Measure.map e
      ((μ.comap (Subtype.val : U → M)).restrict LU) =
      (ν.comap (Subtype.val : V → N)).restrict ((Subtype.val : V → N) ⁻¹' LN) := by
    have hsub : ((Subtype.val : V → N) ⁻¹' LN) ⊆
        ((Subtype.val : V → N) ⁻¹' (W : Set N)) := fun _ hx ↦ hLW hx
    have hm := congrArg (fun m : MeasureTheory.Measure V ↦
      m.restrict ((Subtype.val : V → N) ⁻¹' LN)) hmeasure
    rw [MeasureTheory.Measure.restrict_restrict_of_subset hsub,
      MeasureTheory.Measure.restrict_restrict_of_subset hsub,
      MeasureTheory.Measure.restrict_map e.continuous.measurable
        (hLN.isClosed.measurableSet.preimage continuous_subtype_val.measurable), hpreimage] at hm
    exact hm.symm
  obtain ⟨t, ht, htg, hindex, hst, _htext, B, hBcontrol, hBboundary, hB⟩ :=
    exists_equivariant_relative_analytic_comparison E F E' F' U V e L LN hL hLN
      hLU hLNV hpreimage α hα β hβ ν μ cL hc d hd hcd IG σE σF τE τF
      hσE hσF hτE hτF hU he hgg hcg hdg hαg hβg s hs hsg
      (fun x hx ↦ hsext x (fun h ↦ hx (hKL h)))
      (fun x hx ↦ hcext x (fun h ↦ hx (hKL h)))
      (fun y hy ↦ hdext y (fun ⟨x, hx, hxy⟩ ↦ hy ⟨x, hKL hx, hxy⟩))
      g₀ k₀ P hpieces hprincipal hsupport h k h' k'
      (fun x hx ↦ hαmetric x (hLW ⟨x, hx, rfl⟩))
      (fun x hx ↦ hβmetric x (hLW ⟨x, hx, rfl⟩)) hhi hki hμi hLi hμν
  -- Enlarge only the raw source control to the same finite-piece support before comparing classes.
  let pM : C(Y, M) := cotangentProjection
  let pN : C(Z, N) := cotangentProjection
  let C : Set Y := cotangentZeroSection '' L
  have hC : IsCompact C := hL.image continuous_cotangentZeroSection
  have hbC : b.control ⊆ C := by rw [hbcontrol]; exact Set.image_mono hKL
  have hCi (a : G) (z : Y) : a • z ∈ C ↔ z ∈ C := by
    have hz (z : Y) : z ∈ C ↔ z.proj ∈ L ∧ z.snd = 0 := by
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, rfl⟩
      · rintro ⟨hx, hξ⟩
        exact ⟨z.proj, hx, TotalSpace.ext rfl (heq_of_eq hξ.symm)⟩
    rw [hz, hz]
    change (a • z.proj ∈ L ∧ (a • z).snd = 0) ↔ (z.proj ∈ L ∧ z.snd = 0)
    rw [hLi]
    constructor
    · rintro ⟨hx, hξ⟩
      refine ⟨hx, ?_⟩
      have hh : a⁻¹ • (a • z) = a⁻¹ • cotangentZeroSection (a • z.proj) :=
        congrArg (fun w : Y ↦ a⁻¹ • w) (TotalSpace.ext rfl (heq_of_eq hξ))
      rw [inv_smul_smul] at hh
      have hv : z.snd = (a⁻¹ • cotangentZeroSection (a • z.proj)).snd :=
        eq_of_heq (TotalSpace.ext_iff.mp hh).2
      change z.snd = (0 : CotangentFiber (n := n) (a • z.proj)).comp _ at hv
      rw [ContinuousLinearMap.zero_comp] at hv
      exact hv
    · rintro ⟨hx, hξ⟩
      refine ⟨hx, ?_⟩
      change z.snd.comp _ = 0
      rw [hξ, ContinuousLinearMap.zero_comp]
  let bL := b.enlarge C hC hbC
  have hbL := hb.enlarge C hC hbC hCi
  have hbLboundary (z : (bL.controlᶜ : Set Y)) (v : E.Fiber z.val.proj) :
      bL.boundary.linearEquiv z v = s.val z.val.proj z.val.snd v :=
    (b.enlarge_apply C hC hbC z v).trans (hbboundary _ v)
  let bM := EquivariantSupportBundleTriple.ofBoundary
    ((FiniteBundle.ofFamily E.Fiber).pullback pM)
    ((FiniteBundle.ofFamily F.Fiber).pullback pM) b
    (σE.pullback pM (fun _ _ ↦ rfl)) (σF.pullback pM (fun _ _ ↦ rfl)) hb
  let bLM := EquivariantSupportBundleTriple.ofBoundary
    ((FiniteBundle.ofFamily E.Fiber).pullback pM)
    ((FiniteBundle.ofFamily F.Fiber).pullback pM) bL
    (σE.pullback pM (fun _ _ ↦ rfl)) (σF.pullback pM (fun _ _ ↦ rfl)) hbL
  have hCrange : C ⊆ Set.range f := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨cotangentZeroSection (⟨x, hLU hx⟩ : U), rfl⟩
  have hLclass : (bLM.openRestrict f hf hfg hCrange).kZeroClass = a := by
    have hh := bLM.kZeroClass_openRestrict_eq_of_boundary bM f hf hfg C hC hCi
      (Set.Subset.refl _) hbC hCrange (Iso.refl _) (Iso.refl _)
      (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
      (fun z hz v ↦ b.enlarge_apply C hC hbC ⟨z, hz⟩ v)
    exact hh.trans (hbclass.trans hAclass)
  obtain ⟨hr, hBclass⟩ :=
    CompactSupportTriple.kZeroClass_eq_openPushforward_restrict_of_transport
      E F E' F' U V hU e α β hα hβ L hLU s.val t.val hst
      hfg hgg σE σF τE τF hαg hβg bL B hbL hB rfl hBcontrol hbLboundary hBboundary
  let bN := EquivariantSupportBundleTriple.ofBoundary
    ((FiniteBundle.ofFamily E'.Fiber).pullback pN)
    ((FiniteBundle.ofFamily F'.Fiber).pullback pN) B
    (τE.pullback pN (fun _ _ ↦ rfl)) (τF.pullback pN (fun _ _ ↦ rfl)) hB
  have hBK : bN.kZeroClass = equivariantSupportTripleKZeroOpenPushforward g hg hgg a := by
    exact hBclass.trans (congrArg (equivariantSupportTripleKZeroOpenPushforward g hg hgg)
      hLclass)
  have hbMK : bM.kZeroClass = equivariantSupportTripleKZeroOpenPushforward f hf hfg a := by
    have hh := equivariantSupportTripleKZeroOpenPushforward_class f hf hfg bM hbrange
    exact hh.symm.trans (congrArg (equivariantSupportTripleKZeroOpenPushforward f hf hfg)
      (hbclass.trans hAclass))
  have hbSymbol := b.kZeroClass_eq_equivariantHomogeneousSymbolKClass IG E F σE σF
    0 s hs hsg hb (by rw [hbcontrol]; rintro _ ⟨x, _, rfl⟩; rfl) hbboundary
  have hBSymbol := B.kZeroClass_eq_equivariantHomogeneousSymbolKClass IG E' F' τE τF
    0 t ht htg hB (by rw [hBcontrol]; rintro _ ⟨x, _, rfl⟩; rfl) hBboundary
  -- Evaluate these two original K classes on their same homogeneous symbols.
  calc
    equivariantAnalyticIndexMap (VG := VG) (G := G) (M := M)
        (equivariantSupportTripleKZeroOpenPushforward f hf hfg a) =
        equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hs hsg := by
      rw [← hbMK, hbSymbol]
      exact equivariantAnalyticIndexMap_symbol σE σF hσE hσF s hs hsg
    _ = equivariantHomogeneousAnalyticIndex IG τE τF hτE hτF t ht htg := hindex
    _ = equivariantAnalyticIndexMap (VG := VG) (G := G) (M := N)
        (equivariantSupportTripleKZeroOpenPushforward g hg hgg a) := by
      rw [← hBK, hBSymbol]
      exact (equivariantAnalyticIndexMap_symbol τE τF hτE hτF t ht htg).symm

end AtiyahSinger

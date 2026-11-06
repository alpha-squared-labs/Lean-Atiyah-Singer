/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactKernelLift
public import AtiyahSinger.Analysis.CompactPieceRefinement
public import AtiyahSinger.Analysis.OpenKernelDensity
public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Analysis.OpenPieceExtension
public import AtiyahSinger.Analysis.OpenPrincipalSymbol
public import AtiyahSinger.Analysis.OpenPieceSymbol
public import AtiyahSinger.Analysis.OpenSymbolCoordinates

/-!
# Principal classes for exact open transport of native pieces

Public module ID: M0833.

A common target cutoff compares the actual transported native symbol with the
specified fiberwise full symbol. Finite refinement over target charts keeps
that principal-class witness attached to the same operator pieces. The exact
compact smooth-kernel remainder then reconstructs the prescribed section action
and proves its principal class. The source is allowed to be noncompact.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold SchwartzMap Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (b x).toLinearMap))

include hK hL hKU hLV hKL ha hb in
omit hSC' in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- All cutoffs are chosen in the common original chart and frame overlap.
private theorem exists_openExtension_piece_with_symbol {m : ℝ}
    (P : PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m)
    (hP : P.chart.symm '' (tsupport P.input.cutoff ∪ tsupport P.output.cutoff) ⊆ K)
    (hKbase : K ⊆ P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet)
    (R : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := H.rank) H.Fiber)
    (hRsupport : HasSectionOperatorSupport L R)
    (hR : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := G.rank) G.Fiber),
      (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) →
      ∀ x : U, (R v).val (e x).val = b x ((P.toLinearMap u).val x.val))
    (J : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m)
    (hJzero : ∀ y, y ∉ L → ∀ η, J.val y η = 0)
    (hJaction : ∀ (x : U) (η : CotangentFiber (n := n) (e x).val) (v : E.Fiber x.val),
      J.val (e x).val η (a x v) =
        b x (P.globalSymbolFunction x.val (η.comp (mfderiv
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v))
    (c : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) N)
    (f : Trivialization (EuclideanSpace ℂ (Fin G.rank))
      (π (EuclideanSpace ℂ (Fin G.rank)) G.Fiber))
    (g : Trivialization (EuclideanSpace ℂ (Fin H.rank))
      (π (EuclideanSpace ℂ (Fin H.rank)) H.Fiber))
    [MemTrivializationAtlas f] [MemTrivializationAtlas g]
    (hLbase : L ⊆ c.source ∩ f.baseSet ∩ g.baseSet)
    (hU : Nonempty U) (hV : Nonempty V) :
    ∃ Q : PseudodifferentialPiece (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber m, Q.toLinearMap = R ∧
        globalPrincipalSymbolClass G.Fiber H.Fiber m Q.globalSymbol =
          globalPrincipalSymbolClass G.Fiber H.Fiber m J := by
  -- Choose a common target plateau inside the image of the original source frames.
  classical
  let D : Set U := (Subtype.val : U → M) ⁻¹'
    (P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet)
  have hD : IsOpen D := ((P.chart.open_source.inter P.input.frame.open_baseSet).inter
    P.output.frame.open_baseSet).preimage continuous_subtype_val
  let W : Set N := (Subtype.val : V → N) '' (e '' D)
  have hW : IsOpen W := V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
    (e.toHomeomorph.isOpenMap _ hD)
  have hLW : L ⊆ W := by
    intro y hy
    let v : V := ⟨y, hLV hy⟩
    let x : U := e.symm v
    have hxK : x.val ∈ K := by
      have hv : e x ∈ (Subtype.val : V → N) ⁻¹' L := by
        change (e (e.symm v)).val ∈ L
        rw [e.apply_symm_apply]
        exact hy
      change x ∈ (Subtype.val : U → M) ⁻¹' K
      rw [← hKL]
      exact hv
    refine ⟨e x, ?_, ?_⟩
    · exact ⟨x, hKbase hxK, rfl⟩
    · exact congrArg Subtype.val (e.apply_symm_apply v)
  let O := W ∩ (c.source ∩ f.baseSet ∩ g.baseSet)
  have hO : IsOpen O := hW.inter ((c.open_source.inter f.open_baseSet).inter g.open_baseSet)
  have hLO : L ⊆ O := fun y hy ↦ ⟨hLW hy, hLbase hy⟩
  let Ω := c.target ∩ c.symm ⁻¹' O
  have hΩ : IsOpen Ω := c.isOpen_inter_preimage_symm hO
  have hcL : IsCompact (c '' L) := hL.image_of_continuousOn
    (c.continuousOn.mono (fun y hy ↦ (hLbase hy).1.1))
  have hcLΩ : c '' L ⊆ Ω := by
    rintro z ⟨y, hy, rfl⟩
    exact ⟨c.map_source (hLbase hy).1.1, by
      change c.symm (c y) ∈ O
      rw [c.left_inv (hLbase hy).1.1]
      exact hLO hy⟩
  obtain ⟨χ, hχ, hcχ, hsχ, hχone⟩ :=
    exists_compact_cutoff_one_near (c '' L) Ω hcL hΩ hcLΩ
  let A : BundleChartCutoff (r := G.rank) G.Fiber c :=
    { frame := f
      frame_mem_atlas := inferInstance
      cutoff := χ
      smooth_cutoff := hχ
      compact_support := hcχ
      support_subset := fun z hz ↦ ⟨(hsχ hz).1, (hsχ hz).2.2.1.2⟩ }
  let B : BundleChartCutoff (r := H.rank) H.Fiber c :=
    { frame := g
      frame_mem_atlas := inferInstance
      cutoff := χ
      smooth_cutoff := hχ
      compact_support := hcχ
      support_subset := fun z hz ↦ ⟨(hsχ hz).1, (hsχ hz).2.2.2⟩ }
  have hoverlap : ∀ z ∈ tsupport A.cutoff, ∃ x : U,
      (e x).val = c.symm z ∧
      x.val ∈ P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet := by
    intro z hz
    obtain ⟨v, ⟨x, hx, hxv⟩, hvz⟩ := (hsχ hz).2.1
    exact ⟨x, (congrArg Subtype.val hxv).trans hvz, hx⟩
  obtain ⟨Q, hQ, hQc, hQin, hQout, hQi, hQo, hprincipal⟩ :=
    exists_openExtension_piece E F G H U V e K L hK hKU hKL a ha b hb
      P hP R hRsupport hR c hc A B rfl hLbase hχone hoverlap hU hV
  refine ⟨Q, hQ, ?_⟩
  let t := (P.chart.subtypeRestr hU).symm.trans
    (e.toHomeomorph.toOpenPartialHomeomorph.trans (c.subtypeRestr hV))
  let x (z : EuclideanSpace ℝ (Fin n)) : U := e.symm ((c.subtypeRestr hV).symm z)
  obtain ⟨ht, hts, hvalues⟩ := contDiff_openChartTransition U V e hU hV
    P.chart c P.chart_mem_atlas hc
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  have hcV : c.subtypeRestr hV ∈ (contDiffGroupoid ∞ I).maximalAtlas V :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hc hV
  have hx : ContMDiffOn I I ∞ x t.target := by
    intro z hz
    exact (e.symm.contMDiffAt.comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hcV hz.1.1)).contMDiffWithinAt
  let D : Set U := {y | y.val ∈ P.input.frame.baseSet ∧ (e y).val ∈ A.frame.baseSet} ∩
    {y | y.val ∈ P.output.frame.baseSet ∧ (e y).val ∈ B.frame.baseSet}
  have hD : IsOpen D :=
    ((P.input.frame.open_baseSet.preimage continuous_subtype_val).inter
      (A.frame.open_baseSet.preimage (continuous_subtype_val.comp e.continuous))).inter
        ((P.output.frame.open_baseSet.preimage continuous_subtype_val).inter
          (B.frame.open_baseSet.preimage (continuous_subtype_val.comp e.continuous)))
  let Ω' := t.target ∩ x ⁻¹' D
  have hΩ' : IsOpen Ω' := hx.continuousOn.isOpen_inter_preimage t.open_target hD
  have hAΩ : tsupport A.cutoff ⊆ Ω' := by
    intro z hz
    obtain ⟨y, hy, hyD⟩ := hoverlap z hz
    have hyc : (e y).val ∈ c.source := by
      rw [hy]
      exact c.map_target (A.support_subset hz).1
    have hycV : e y ∈ (c.subtypeRestr hV).source := by simpa using hyc
    have hzy : c.subtypeRestr hV (e y) = z := by
      change c (e y).val = z
      rw [hy, c.right_inv (A.support_subset hz).1]
    have hxy : x z = y := by
      dsimp only [x]
      rw [← hzy, (c.subtypeRestr hV).left_inv hycV, e.symm_apply_apply]
    refine ⟨⟨⟨?_, Set.mem_univ _⟩, ?_⟩, ?_⟩
    · rw [← hzy]
      exact (c.subtypeRestr hV).map_source hycV
    · change x z ∈ (P.chart.subtypeRestr hU).source
      rw [hxy]
      simpa using hyD.1.1
    · change x z ∈ D
      rw [hxy]
      exact ⟨⟨hyD.1.2, hy.symm ▸ (A.support_subset hz).2⟩,
        ⟨hyD.2, hy.symm ▸ (B.support_subset hz).2⟩⟩
  let := P.input.frame_mem_atlas
  let := P.output.frame_mem_atlas
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let Ain (z : EuclideanSpace ℝ (Fin n)) :=
    ((P.input.frame.linearMapAt ℂ (x z).val).comp
      ((a (x z)).symm.toLinearMap.comp
        (A.frame.symmL ℂ (e (x z)).val).toLinearMap)).toContinuousLinearMap
  let Bout (z : EuclideanSpace ℝ (Fin n)) :=
    ((B.frame.linearMapAt ℂ (e (x z)).val).comp
      ((b (x z)).toLinearMap.comp
        (P.output.frame.symmL ℂ (x z).val).toLinearMap)).toContinuousLinearMap
  have hAin : ContDiffOn ℝ ∞ Ain Ω' :=
    ((contMDiffOn_openBundleMap_matrices E G U V e a ha P.input.frame A.frame).2.comp
      (hx.mono Set.inter_subset_left) (fun _ hz ↦ hz.2.1)).contDiffOn
  have hBout : ContDiffOn ℝ ∞ Bout Ω' :=
    ((contMDiffOn_openBundleMap_matrices F H U V e b hb P.output.frame B.frame).1.comp
      (hx.mono Set.inter_subset_left) (fun _ hz ↦ hz.2.2)).contDiffOn
  have hLQ : L ⊆ Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet := by
    rw [hQin, hQout, hQc]
    exact hLbase
  have hsame : Q.output.cutoff = Q.input.cutoff := by rw [hQo, hQi]
  have hone : ∀ y ∈ L, Q.input.cutoff (Q.chart y) = 1 := by
    intro y hy
    rw [hQi, hQc]
    exact interior_subset (s := {z | χ z = 1}) (hχone ⟨y, hy, rfl⟩)
  apply globalPrincipalSymbolClass_eq_of_openPiece E F G H P Q J L hL hLQ hJzero
    hsame hone t ht hts Ω' hΩ' Set.inter_subset_left
    (by rw [hQi]; exact hAΩ) Bout Ain hBout hAin ?_ ?_
  · rw [hQi]
    exact hprincipal
  · intro z hz η
    simp only [hQin, hQout, hQc]
    have h := globalSymbolInChart_openTransport E F G H U V e a b hU hV
      P.chart c P.chart_mem_atlas hc P.input.frame P.output.frame A.frame B.frame
      P.globalSymbolFunction J.val hJaction z hz.1 hz.2.1.1 hz.2.2.1 η
    rw [h]
    have hxSource : (x z).val ∈ P.chart.source := by
      have hh := hz.1.2
      change x z ∈ (P.chart.subtypeRestr hU).source at hh
      simpa using hh
    have hzOld : t.symm z ∈ symbolChartDomain E.Fiber F.Fiber P.chart
        P.input.frame P.output.frame := by
      change P.chart (x z).val ∈ _
      refine ⟨⟨P.chart.map_source hxSource, ?_⟩, ?_⟩
      · change P.chart.symm (P.chart (x z).val) ∈ P.input.frame.baseSet
        rw [P.chart.left_inv hxSource]
        exact hz.2.1.1
      · change P.chart.symm (P.chart (x z).val) ∈ P.output.frame.baseSet
        rw [P.chart.left_inv hxSource]
        exact hz.2.2.1
    change matrixSymbol Bout Ain
      (cotangentSymbol t (globalSymbolInChart E.Fiber F.Fiber P.globalSymbolFunction
        P.chart P.input.frame P.output.frame)) z η = _
    simp only [matrixSymbol, cotangentSymbol]
    rw [P.globalSymbolInChart_globalSymbolFunction _ _ hzOld]
    simp only [cutoffAmplitude, Complex.coe_smul]

variable [CompactSpace N] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace N] [BorelSpace N]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]

include hK hL hKU hLV hKL ha hb hμ in
omit hL hKL in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
-- Retain one finite native refinement and its exact compact smooth-kernel remainder.
/-- Exact open transport of a native piece preserves the specified principal-symbol class. -/
theorem exists_openExtension_piece_principalSymbol {m : ℝ}
    (P : PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m)
    (hP : P.chart.symm '' (tsupport P.input.cutoff ∪ tsupport P.output.cutoff) ⊆ K)
    (R : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := H.rank) H.Fiber)
    (hRsupport : HasSectionOperatorSupport L R)
    (hR : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := G.rank) G.Fiber),
      (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) →
      ∀ x : U, (R v).val (e x).val = b x ((P.toLinearMap u).val x.val))
    (J : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m)
    (hJzero : ∀ y, y ∉ L → ∀ η, J.val y η = 0)
    (hJaction : ∀ (x : U) (η : CotangentFiber (n := n) (e x).val) (v : E.Fiber x.val),
      J.val (e x).val η (a x v) =
        b x (P.globalSymbolFunction x.val (η.comp (mfderiv
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v))
    (hU : Nonempty U) (hV : Nonempty V) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber ν m,
      Q.toLinearMap = R ∧ Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber m J := by
  /- Refine the original two cutoffs over target chart neighborhoods. Transport
  each refined native piece and the exact smoothing error separately, then use
  one realized input germ to identify their sum with the specified section map. -/
  classical
  let c (x : U) := chartAt (EuclideanSpace ℝ (Fin n)) (e x).val
  let f (x : U) := trivializationAt (EuclideanSpace ℂ (Fin G.rank)) G.Fiber (e x).val
  let g (x : U) := trivializationAt (EuclideanSpace ℂ (Fin H.rank)) H.Fiber (e x).val
  let O (x : U) : Set N := (c x).source ∩ (f x).baseSet ∩ (g x).baseSet
  have hO (x : U) : IsOpen (O x) :=
    ((c x).open_source.inter (f x).open_baseSet).inter (g x).open_baseSet
  let W (x : U) : Set M := (Subtype.val : U → M) ''
    (e ⁻¹' ((Subtype.val : V → N) ⁻¹' O x))
  have hW (x : U) : IsOpen (W x) := U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
    ((hO x).preimage (continuous_subtype_val.comp e.continuous))
  have hcover : P.chart.symm '' (tsupport P.output.cutoff ∪ tsupport P.input.cutoff) ⊆
      ⋃ x : U, W x := by
    intro z hz
    have hzK : z ∈ K := hP (by simpa only [Set.union_comm] using hz)
    let x : U := ⟨z, hKU hzK⟩
    refine Set.mem_iUnion.mpr ⟨x, x, ?_, rfl⟩
    exact ⟨⟨mem_chart_source _ _, mem_baseSet_trivializationAt _ _ _⟩,
      mem_baseSet_trivializationAt _ _ _⟩
  obtain ⟨d, idx, χ, ρ, hχ, hρ, hsymbols, hWsub, hsmooth, herrorSupport⟩ :=
    P.exists_coordinate_refinement W hW hcover
  let T (j : Fin d) := P.coordinateCutoff (χ j) (ρ j) (hχ j) (hρ j)
  let Kj (j : Fin d) := P.chart.symm ''
    (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff)
  have hKj (j : Fin d) : IsCompact (Kj j) :=
    ((T j).input.compact_support.union (T j).output.compact_support).image_of_continuousOn
      (P.chart.continuousOn_symm.mono (fun z hz ↦ hz.elim
        (fun h ↦ ((T j).input.support_subset h).1)
        (fun h ↦ ((T j).output.support_subset h).1)))
  have hKjK (j : Fin d) : Kj j ⊆ K := by
    rintro y ⟨z, hz, rfl⟩
    apply hP
    refine ⟨z, ?_, rfl⟩
    exact hz.elim (fun h ↦ Or.inl (tsupport_mul_subset_left h))
      (fun h ↦ Or.inr (tsupport_mul_subset_left h))
  have hKjU (j : Fin d) : Kj j ⊆ U := (hKjK j).trans hKU
  have hKjbase (j : Fin d) : Kj j ⊆
      (T j).chart.source ∩ (T j).input.frame.baseSet ∩ (T j).output.frame.baseSet := by
    rintro y ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact ⟨⟨P.chart.map_target ((T j).input.support_subset hz).1,
        ((T j).input.support_subset hz).2⟩, (T j).input_support_in_output_frame hz⟩
    · exact ⟨⟨P.chart.map_target ((T j).output.support_subset hz).1,
        (T j).output_support_in_input_frame hz⟩, ((T j).output.support_subset hz).2⟩
  let Lj (j : Fin d) : Set N := Set.range (fun x : Kj j ↦ (e ⟨x.val, hKjU j x.property⟩).val)
  have hLj (j : Fin d) : IsCompact (Lj j) := by
    let : CompactSpace (Kj j) := isCompact_iff_compactSpace.mp (hKj j)
    exact isCompact_range (continuous_subtype_val.comp (e.continuous.comp
      (continuous_subtype_val.subtype_mk (fun x : Kj j ↦ hKjU j x.property))))
  have hLjV (j : Fin d) : Lj j ⊆ V := by
    rintro y ⟨x, rfl⟩
    exact (e ⟨x.val, hKjU j x.property⟩).property
  have hKjLj (j : Fin d) : e ⁻¹' ((Subtype.val : V → N) ⁻¹' Lj j) =
      (Subtype.val : U → M) ⁻¹' Kj j := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have heq : (⟨y.val, hKjU j y.property⟩ : U) = x :=
        e.injective (Subtype.ext hy)
      change x.val ∈ Kj j
      have hyval : y.val = x.val := congrArg Subtype.val heq
      rw [← hyval]
      exact y.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, rfl⟩
  have hLjbase (j : Fin d) : Lj j ⊆ O (idx j) := by
    rintro y ⟨z, rfl⟩
    have hz : (z : M) ∈ (T j).chart.symm ''
        (tsupport (T j).output.cutoff ∪ tsupport (T j).input.cutoff) := by
      change z.val ∈ P.chart.symm '' _
      rw [Set.union_comm]
      exact z.property
    have hzW := hWsub j hz
    obtain ⟨x, hx, hxz⟩ := hzW
    have heq : x = ⟨z.val, hKjU j z.property⟩ := Subtype.ext hxz
    change (e ⟨z.val, hKjU j z.property⟩).val ∈ O (idx j)
    change (e x).val ∈ O (idx j) at hx
    rw [heq] at hx
    exact hx
  -- The same transported symbol is retained alongside each exact native operator.
  have hJj (j : Fin d) : ∃ Jj : globalSymbolSpace
      (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m,
      (∀ (x : U) η (v : E.Fiber x.val),
        Jj.val (e x).val η (a x v) = b x
          ((T j).globalSymbolFunction x.val (η.comp (mfderiv
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v)) ∧
      (∀ y, y ∉ Lj j → ∀ η, Jj.val y η = 0) := by
    apply exists_supported_openGlobalSymbol E F G H U V e (Kj j) (Lj j)
      (hLj j) (hLjV j) (hKjLj j) a ha b hb (T j).globalSymbol
    intro y hy η
    exact (T j).globalSymbolFunction_eq_zero y (fun h ↦ hy (by
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨z, Or.inr hz.1, rfl⟩)) η
  choose Jj hJjaction hJjzero using hJj
  have hQ (j : Fin d) : ∃ Q : PseudodifferentialPiece
      (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m,
      HasSectionOperatorSupport (Lj j) Q.toLinearMap ∧
      (∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
        (v : smoothSections (n := n) (r := G.rank) G.Fiber),
        (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' Kj j),
          v.val (e x).val = a x (u.val x.val)) →
        ∀ x : U, (Q.toLinearMap v).val (e x).val = b x (((T j).toLinearMap u).val x.val)) ∧
      globalPrincipalSymbolClass G.Fiber H.Fiber m Q.globalSymbol =
        globalPrincipalSymbolClass G.Fiber H.Fiber m (Jj j) := by
    have hs := PseudodifferentialPiece.hasSectionOperatorSupport E F (Kj j) (hKj j)
      (T j) Set.Subset.rfl
    obtain ⟨Rj, hRj, _⟩ := existsUnique_supported_openExtension E F G H U V e
      (Kj j) (Lj j) (hKj j) (hLj j) (hKjU j) (hLjV j) (hKjLj j) a ha b hb
      (T j).toLinearMap hs
    obtain ⟨Q, hQ, hQclass⟩ := exists_openExtension_piece_with_symbol E F G H U V e
      (Kj j) (Lj j) (hKj j) (hLj j) (hKjU j) (hLjV j) (hKjLj j) a ha b hb
      (T j) Set.Subset.rfl (hKjbase j) Rj hRj.1 hRj.2 (Jj j) (hJjzero j) (hJjaction j)
      (c (idx j)) (chart_mem_atlas _ _) (f (idx j)) (g (idx j)) (hLjbase j) hU hV
    exact ⟨Q, hQ ▸ hRj.1, hQ ▸ hRj.2, hQclass⟩
  choose Q hQsupport hQaction hQclass using hQ
  -- A common plateau reconstructs both the original piece and every refined summand.
  let K₀ := tsupport P.output.cutoff ∪ tsupport P.input.cutoff
  have hK₀ : IsCompact K₀ := P.output.compact_support.union P.input.compact_support
  let Z := P.chart.target ∩ P.chart.symm ⁻¹'
    (((U : Set M) ∩ P.input.frame.baseSet) ∩ P.output.frame.baseSet)
  have hZ : IsOpen Z := P.chart.isOpen_inter_preimage_symm
    ((U.isOpen.inter P.input.frame.open_baseSet).inter P.output.frame.open_baseSet)
  have hK₀Z : K₀ ⊆ Z := by
    intro z hz
    have hzK : P.chart.symm z ∈ K := hP ⟨z, hz.elim Or.inr Or.inl, rfl⟩
    rcases hz with hz | hz
    · exact ⟨(P.output.support_subset hz).1,
        ⟨hKU hzK, P.output_support_in_input_frame hz⟩, (P.output.support_subset hz).2⟩
    · exact ⟨(P.input.support_subset hz).1,
        ⟨hKU hzK, (P.input.support_subset hz).2⟩, P.input_support_in_output_frame hz⟩
  obtain ⟨δ, hδ, hcδ, hsδ, hδone⟩ := exists_compact_cutoff_one_near K₀ Z hK₀ hZ hK₀Z
  let A : BundleChartCutoff (r := E.rank) E.Fiber P.chart :=
    { frame := P.input.frame
      frame_mem_atlas := P.input.frame_mem_atlas
      cutoff := δ
      smooth_cutoff := hδ
      compact_support := hcδ
      support_subset := fun z hz ↦ ⟨(hsδ hz).1, (hsδ hz).2.1.2⟩ }
  let B : BundleChartCutoff (r := F.rank) F.Fiber P.chart :=
    { frame := P.output.frame
      frame_mem_atlas := P.output.frame_mem_atlas
      cutoff := δ
      smooth_cutoff := hδ
      compact_support := hcδ
      support_subset := fun z hz ↦ ⟨(hsδ hz).1, (hsδ hz).2.2⟩ }
  have hδK₀ (z) (hz : z ∈ K₀) : δ z = 1 :=
    interior_subset (s := {z | δ z = 1}) (hδone hz)
  have hPplateau := P.extend_coordinateOperator_localize A B rfl rfl
    (fun z hz ↦ hδK₀ z (Or.inr hz)) (fun z hz ↦ hδK₀ z (Or.inl hz))
  have hTplateau (j : Fin d) := (T j).extend_coordinateOperator_localize A B rfl rfl
    (fun z hz ↦ hδK₀ z (Or.inr (tsupport_mul_subset_left hz)))
    (fun z hz ↦ hδK₀ z (Or.inl (tsupport_mul_subset_left hz)))
  obtain ⟨k, hk, _, _, hkact⟩ := hsmooth.exists_kernel_supported
    K₀ Z hK₀ hZ hK₀Z herrorSupport
  obtain ⟨S, hSzero, hSact⟩ := exists_compactKernelLift μ P.chart P.chart_mem_atlas
    A B k hk (P.coordinateOperator - ∑ j, (T j).coordinateOperator) hkact
  let C := P.chart.symm '' tsupport δ
  have hC : IsCompact C := hcδ.image_of_continuousOn
    (P.chart.continuousOn_symm.mono (fun z hz ↦ (hsδ hz).1))
  have hCU : C ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsδ hz).2.1.1
  have hSformula (u : smoothSections (n := n) (r := E.rank) E.Fiber) (x : M) :
      S.apply μ u x = ((P.toLinearMap - ∑ j, (T j).toLinearMap) u).val x := by
    rw [hSact]
    have hsec : B.extend P.chart_mem_atlas
        ((P.coordinateOperator - ∑ j, (T j).coordinateOperator)
          (A.localize P.chart_mem_atlas u)) =
        (P.toLinearMap - ∑ j, (T j).toLinearMap) u := by
      change (B.extendLinearMap P.chart_mem_atlas)
        ((P.coordinateOperator - ∑ j, (T j).coordinateOperator)
          ((A.localizeLinearMap P.chart_mem_atlas) u)) = _
      simp only [sub_apply, sum_apply, map_sub, map_sum,
        LinearMap.sub_apply, LinearMap.sum_apply]
      rw [show B.extendLinearMap P.chart_mem_atlas
        (P.coordinateOperator (A.localizeLinearMap P.chart_mem_atlas u)) = P.toLinearMap u from
          congrArg (fun f ↦ f u) hPplateau]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun f ↦ f u) (hTplateau j)
    exact congrArg (fun s ↦ s.val x) hsec
  obtain ⟨R₀, hR₀s, hR₀zero, hR₀act⟩ := S.exists_openIntegralTransport E F G H U V e
    a ha b hb μ ν C hC hCU hSzero
  -- Realize target inputs on one compact neighborhood controlling every summand and kernel.
  obtain ⟨γ, hγ, Tin, _, _, hγone, hTin⟩ := exists_openSectionGermPullback E G U V e
    (K ∪ C) (hK.union hC) (Set.union_subset hKU hCU) a ha
  have hmatch (v : smoothSections (n := n) (r := G.rank) G.Fiber)
      (D : Set M) (hD : D ⊆ K ∪ C) :
      ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' D),
        v.val (e x).val = a x ((Tin v).val x.val) := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    have hn := eventually_nhdsSet_iff_forall.mp hγone x.val (hD hx)
    filter_upwards [(continuous_subtype_val.tendsto x).eventually hn] with y hy
    rw [hTin, hy, Complex.ofReal_one, one_smul, LinearEquiv.apply_symm_apply]
  have hpoint (v : smoothSections (n := n) (r := G.rank) G.Fiber) (x : U)
      (hx : x.val ∈ C) : v.val (e x).val = a x ((Tin v).val x.val) := by
    have hγx : γ x.val = 1 := interior_subset (s := {z | γ z = 1})
      (subset_interior_iff_mem_nhdsSet.mpr hγone (Or.inr hx))
    rw [hTin, hγx, Complex.ofReal_one, one_smul, LinearEquiv.apply_symm_apply]
  have heq : R = (∑ j, (Q j).toLinearMap) + R₀ := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ V
    · let x : U := e.symm ⟨y, hy⟩
      have hex : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      have hlocal : (R v).val (e x).val =
          (((∑ j, (Q j).toLinearMap) + R₀) v).val (e x).val := by
        rw [hR (Tin v) v (hmatch v K Set.subset_union_left)]
        simp only [LinearMap.add_apply, LinearMap.sum_apply,
          Submodule.coe_add, Pi.add_apply, Submodule.coe_sum, Finset.sum_apply]
        simp_rw [hQaction _ (Tin v) v
          (hmatch v _ ((hKjK _).trans Set.subset_union_left))]
        rw [hR₀act (Tin v) v (hpoint v), hSformula]
        change b x ((P.toLinearMap (Tin v)).val x.val) =
          (∑ j, b x (((T j).toLinearMap (Tin v)).val x.val)) +
            b x (((P.toLinearMap - ∑ j, (T j).toLinearMap) (Tin v)).val x.val)
        simp only [LinearMap.sub_apply, LinearMap.sum_apply, Submodule.coe_sub,
          Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply]
        rw [map_sub, map_sum]
        abel
      exact (congrArg (fun z ↦ (R v).val z =
        (((∑ j, (Q j).toLinearMap) + R₀) v).val z) hex).mp hlocal
    · have hleft : (R v).val y = 0 := by
        by_contra hne
        exact hy (hLV (hRsupport.1 v (subset_closure hne)))
      have hright (j : Fin d) : ((Q j).toLinearMap v).val y = 0 := by
        by_contra hne
        exact hy (hLjV j ((hQsupport j).1 v (subset_closure hne)))
      simp only [hleft, LinearMap.add_apply, LinearMap.sum_apply,
        Submodule.coe_add, Pi.add_apply, Submodule.coe_sum, Finset.sum_apply,
        hright, Finset.sum_const_zero, hR₀zero v y hy, add_zero]
  -- The actual representation determines the class; its transported full symbols sum to J.
  have hrepresentation : IsSmoothingOperator ν (R - ∑ j, (Q j).toLinearMap) := by
    rw [heq, add_sub_cancel_left]
    exact hR₀s
  let Q₀ : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber ν m :=
    { toLinearMap := R
      isPseudodifferentialOperator := ⟨d, Q, hrepresentation⟩ }
  refine ⟨Q₀, rfl, ?_⟩
  rw [Q₀.principalSymbol_eq_of_representation d Q hrepresentation, map_sum]
  simp_rw [hQclass]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  funext y η
  by_cases hy : y ∈ V
  · let x : U := e.symm ⟨y, hy⟩
    have hex : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    have hpoint : (∑ j, Jj j).val (e x).val = J.val (e x).val := by
      funext ξ
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨u, rfl⟩ := (a x).surjective v
      simp only [Submodule.coe_sum, Finset.sum_apply, sum_apply]
      simp_rw [hJjaction, hJaction]
      have hsum := congrArg (fun p : globalSymbolSpace E.Fiber F.Fiber m ↦
        p.val x.val (ξ.comp (mfderiv
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) u) hsymbols
      have hsum' : (∑ j, (T j).globalSymbolFunction x.val
          (ξ.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) u) =
          P.globalSymbolFunction x.val (ξ.comp (mfderiv
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) u := by
        simpa only [T, Submodule.coe_sum, Finset.sum_apply, sum_apply,
          PseudodifferentialPiece.globalSymbol] using hsum
      exact (map_sum (b x).toLinearMap _ _).symm.trans (congrArg (b x) hsum')
    have hpoint' : (∑ j, Jj j).val y = J.val y :=
      (congrArg (fun z ↦ (∑ j, Jj j).val z = J.val z) hex).mp hpoint
    exact congrFun hpoint' η
  · have hzero : J.val y η = 0 := hJzero y (fun h ↦ hy (hLV h)) η
    have hzj (j : Fin d) : (Jj j).val y η = 0 :=
      hJjzero j y (fun h ↦ hy (hLjV j h)) η
    simp only [Submodule.coe_sum, Finset.sum_apply, hzj, Finset.sum_const_zero, hzero]

end AtiyahSinger

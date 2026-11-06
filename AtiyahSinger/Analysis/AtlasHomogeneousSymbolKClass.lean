/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Analysis.OperatorSymbolKClass

/-!
# The original support class of atlas homogeneous elliptic data

Public module ID: M0250.

A10: the original off-zero fiber map is a bundle isomorphism on the original
cotangent pullbacks. Its support triple has the actual zero section as compact
control, and gives a class in the existing compact-support K group. Smoothness
supplies continuity; neither a degree nor a regularization metric enters this
topological construction. Fiber ranks may vary across connected components.

The native comparison forgets only continuity certificates of the fiber maps.
It uses the original model-topology transport already present in the atlas
bridge. In dimension zero the empty exterior retains the source-minus-target
bundle class, even though every regularized principal quotient is zero.

Sources: SG III.13 (13.1), (13.5)--(13.7), pp.243--246; SG I.9.26 for support
triples. The explicit atlas/pullback comparisons are project supplements.
The boundary, triple and class retain the supplied original fiber maps. Their
continuity, native comparisons and dimension-zero normalization are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

/-- The original smooth punctured symbol acts continuously on the actual restricted pullbacks. -/
theorem continuous_atlasSymbolTotalMap (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) :
    let p := (cotangentProjection (n := n) (M := M) : _ → M)
    Continuous (fun z : TotalSpace Unit (Restrict (p *ᵖ E) cotangentZeroSetᶜ) ↦
      (⟨z.proj, a z.proj.val.proj z.proj.val.snd z.snd⟩ :
        TotalSpace Unit (Restrict (p *ᵖ F) cotangentZeroSetᶜ))) := by
  /- Stage 1: around a nonzero cotangent vector choose an original base
  chart and the supplied source/target atlas frames. In these coordinates
  the total map is (x,xi,v) -> (x,xi,a(x,xi)v). Off-zero smoothness of the
  coordinate operator and continuity of finite-dimensional evaluation make
  it continuous. Neither original fiber needs a separately selected norm.
  Stage 2: the original chart maps and the actual induced pullback and
  restriction topologies carry these local expressions back to the stated
  total-space map. Locality of continuity covers the entire exterior.
  In dimension zero that exterior is empty, so no rank comparison is imposed. -/
  classical
  let p := (cotangentProjection (n := n) (M := M) : _ → M)
  let S := PuncturedCotangentBundle (n := n) (M := M)
  let D := TotalSpace Unit (Restrict (p *ᵖ E) cotangentZeroSetᶜ)
  have hproj : Continuous (fun z : D ↦ z.proj) :=
    Pullback.continuous_proj Unit (p *ᵖ E) (Subtype.val : S → _)
  have hinput : Continuous (fun z : D ↦ (⟨z.proj.val.proj, z.snd⟩ : TotalSpace Unit E)) :=
    (Pullback.continuous_lift Unit E p).comp
      (Pullback.continuous_lift Unit (p *ᵖ E) (Subtype.val : S → _))
  -- First prove continuity in the original target total space, using only its atlas frames.
  have houtput : Continuous (fun z : D ↦
      (⟨z.proj.val.proj, a z.proj.val.proj z.proj.val.snd z.snd⟩ : TotalSpace Unit F)) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let c := chartAt (EuclideanSpace ℝ (Fin n)) z₀.proj.val.proj
    let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) z₀.proj.val.proj
    obtain ⟨i, hi₀⟩ := A.covers z₀.proj.val.proj
    obtain ⟨j, hj₀⟩ := B.covers z₀.proj.val.proj
    have hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ _
    have hx₀ : z₀.proj.val.proj ∈ c.source := mem_chart_source _ _
    have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : D ↦ z.proj.val) (x₀ := z₀)).mp
        (continuous_subtype_val.comp hproj).continuousAt
    have hbase := hsource.1
    have hchart : ContinuousAt
        (fun z : D ↦ c z.proj.val.proj) z₀ :=
      (c.continuousAt hx₀).comp
        (f := fun z : D ↦ z.proj.val.proj) hbase
    have hξ : ContinuousAt (fun z : D ↦
        z.proj.val.snd.comp (t.symmL ℝ z.proj.val.proj)) z₀ := by
      have h := hsource.2
      change ContinuousAt (fun z : D ↦
        ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj.val.proj).comp
          (z.proj.val.snd.comp (t.symmL ℝ z.proj.val.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    -- The moving covector is evaluated on the inverse chart differential in native coordinates.
    have hcm : c ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.subset_maximalAtlas (I := I) hc
    have hd₀ := ((contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hx₀)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt
    unfold inTangentCoordinates at hd₀
    simp only [c.left_inv hx₀] at hd₀
    have hd := hd₀.comp
      (f := fun z : D ↦ c z.proj.val.proj) hchart
    have hdual (v : EuclideanSpace ℝ (Fin n)) : ContinuousAt
        (fun z : D ↦
          z.proj.val.snd ((mfderiv I I c.symm (c z.proj.val.proj)) v)) z₀ := by
      apply (hξ.clm_apply (hd.clm_apply (continuousAt_const (y := v)))).congr_of_eventuallyEq
      filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
      dsimp only [Function.comp_apply, ContinuousLinearMap.inCoordinates, Function.id_def]
      simp only [TangentBundle.symmL_model_space]
      erw [c.left_inv hz]
      change z.proj.val.snd ((mfderiv I I c.symm (c z.proj.val.proj)) v) =
        z.proj.val.snd (t.symmL ℝ z.proj.val.proj (t.continuousLinearMapAt ℝ z.proj.val.proj
          ((mfderiv I I c.symm (c z.proj.val.proj)) v)))
      exact congrArg z.proj.val.snd
        (t.symmL_continuousLinearMapAt (R := ℝ) hz
          ((mfderiv I I c.symm (c z.proj.val.proj)) v)).symm
    have hcoord : ContinuousAt (fun z : D ↦
        covectorInChart c z.proj.val.proj z.proj.val.snd) z₀ := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp
      apply continuousAt_pi.mpr
      intro j
      exact hdual (EuclideanSpace.single j 1)
    -- The original chartwise smoothness is now composed with these actual cotangent coordinates.
    have hne (z : D) (hz : z.proj.val.proj ∈ c.source) :
        covectorInChart c z.proj.val.proj z.proj.val.snd ≠ 0 := by
      intro hzero
      have hi := covectorFromChart_covectorInChart c hc z.proj.val.proj hz z.proj.val.snd
      rw [hzero] at hi
      have hzero' : covectorFromChart c z.proj.val.proj 0 = 0 := by
        ext v
        simp [covectorFromChart]
        rfl
      exact z.proj.property (hi.symm.trans hzero')
    -- Off-zero coordinate smoothness acts on the coordinates of this very input vector.
    have hdomain : (c z₀.proj.val.proj,
        covectorInChart c z₀.proj.val.proj z₀.proj.val.snd) ∈
        atlasSymbolChartDomain A B c i j ×ˢ {ξ | ξ ≠ 0} := by
      refine ⟨⟨⟨c.map_source hx₀, ?_⟩, ?_⟩, hne z₀ hx₀⟩
      · simpa only [Set.mem_preimage, c.left_inv hx₀] using hi₀
      · simpa only [Set.mem_preimage, c.left_inv hx₀] using hj₀
    have hopen : IsOpen (atlasSymbolChartDomain A B c i j) := by
      simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        c.continuousOn_symm.isOpen_inter_preimage c.open_target
          ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
    have hoperator := ((hs c hc i j).continuousOn.continuousAt
      ((hopen.prod isOpen_ne).mem_nhds hdomain)).comp
        (f := fun z : D ↦ (c z.proj.val.proj,
          covectorInChart c z.proj.val.proj z.proj.val.snd)) (hchart.prodMk hcoord)
    have hcoordinates : ContinuousAt (fun z : D ↦
        WithLp.toLp 2 (A.chart i (⟨z.proj.val.proj, z.snd⟩ : TotalSpace Unit E)).2) z₀ :=
      (PiLp.continuous_toLp 2 (fun _ : Fin (A.rank i) ↦ ℂ)).continuousAt.comp
        (((A.chart i).toOpenPartialHomeomorph.continuousAt
          ((A.chart i).mem_source.mpr hi₀)).comp hinput.continuousAt).snd
    have hvalue := (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).continuous.continuousAt.comp
      (hoperator.clm_apply hcoordinates)
    have hchartFormula (z : EuclideanSpace ℝ (Fin n)) (y : M) (hy : c.symm z = y)
        (hi : y ∈ (A.chart i).baseSet) (hj : y ∈ (B.chart j).baseSet)
        (η : EuclideanSpace ℝ (Fin n)) (v : E y) :
        (B.chart j (⟨y, a y (covectorFromChart c y η) v⟩ : TotalSpace Unit F)).2 =
          (EuclideanSpace.equiv (Fin (B.rank j)) ℂ)
            (atlasGlobalSymbolInChart A B a c i j z η
              (WithLp.toLp 2 (A.chart i (⟨y, v⟩ : TotalSpace Unit E)).2)) := by
      subst y
      dsimp only [atlasGlobalSymbolInChart]
      rw [dite_eq_left ⟨hi, hj⟩]
      change B.frameLinearEquiv j (c.symm z) hj
          (a (c.symm z) (covectorFromChart c (c.symm z) η) v) =
        (EuclideanSpace.equiv (Fin (B.rank j)) ℂ)
          ((EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm
            (B.frameLinearEquiv j (c.symm z) hj
              (a (c.symm z) (covectorFromChart c (c.symm z) η)
                ((A.frameLinearEquiv i (c.symm z) hi).symm
                  (A.frameLinearEquiv i (c.symm z) hi v)))))
      rw [(EuclideanSpace.equiv (Fin (B.rank j)) ℂ).apply_symm_apply,
        (A.frameLinearEquiv i (c.symm z) hi).symm_apply_apply]
    have hformula (x : M) (hx : x ∈ c.source)
        (hi : x ∈ (A.chart i).baseSet) (hj : x ∈ (B.chart j).baseSet)
        (ξ : CotangentFiber (n := n) x) (v : E x) :
        (B.chart j (⟨x, a x ξ v⟩ : TotalSpace Unit F)).2 =
          (EuclideanSpace.equiv (Fin (B.rank j)) ℂ)
            (atlasGlobalSymbolInChart A B a c i j (c x) (covectorInChart c x ξ)
              (WithLp.toLp 2 (A.chart i (⟨x, v⟩ : TotalSpace Unit E)).2)) := by
      simpa only [covectorFromChart_covectorInChart c hc x hx] using
        hchartFormula (c x) x (c.left_inv hx) hi hj (covectorInChart c x ξ) v
    -- Transport the coordinate evaluation back through the same original target frame.
    apply (B.chart j).continuousAt_of_comp_left hbase hj₀
    apply (hbase.prodMk hvalue).congr_of_eventuallyEq
    filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀),
      hbase.preimage_mem_nhds ((A.chart i).open_baseSet.mem_nhds hi₀),
      hbase.preimage_mem_nhds ((B.chart j).open_baseSet.mem_nhds hj₀)] with z hz hi hj
    apply Prod.ext
    · exact (B.chart j).coe_fst' hj
    · exact hformula z.proj.val.proj hz hi hj z.proj.val.snd z.snd
  -- The actual pullback and restriction topologies retain the unchanged cotangent base.
  change Continuous (fun z : D ↦
    (⟨z.proj, a z.proj.val.proj z.proj.val.snd z.snd⟩ :
      TotalSpace Unit (Restrict (p *ᵖ F) cotangentZeroSetᶜ)))
  rw [(inducing_pullbackTotalSpaceEmbedding Unit (p *ᵖ F) (Subtype.val : S → _)).continuous_iff]
  apply hproj.prodMk
  rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
  exact (continuous_subtype_val.comp hproj).prodMk houtput

/-- The given symbol as the actual exterior isomorphism of the original cotangent pullbacks. -/
def atlasEllipticSymbolBoundary (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a) :
    RelativeTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) cotangentZeroSetᶜ :=
  letI := A.isFiniteRank
  letI := B.isFiniteRank
  let p := (cotangentProjection (n := n) (M := M) : _ → M)
  let f : Hom (Restrict (p *ᵖ E) cotangentZeroSetᶜ)
      (Restrict (p *ᵖ F) cotangentZeroSetᶜ) :=
    { linearMap := fun z ↦ a z.val.proj z.val.snd
      continuous_total := continuous_atlasSymbolTotalMap A B a hs }
  f.toIso (fun z ↦ hi z.val.proj z.val.snd z.property)

variable [CompactSpace M]

/-- The raw support triple keeps both original bundles and the entire zero-section control. -/
def atlasEllipticSymbolTriple (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a) :
    CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) where
  control := cotangentZeroSet
  isCompact_control := isCompact_cotangentZeroSet
  boundary := atlasEllipticSymbolBoundary A B a hs hi

/-- The raw triple has the original control and the exact given action on every exterior vector. -/
theorem atlasEllipticSymbolTriple_properties (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a) :
    (atlasEllipticSymbolTriple A B a hs hi).control = cotangentZeroSet ∧
      ∀ (z : PuncturedCotangentBundle (n := n) (M := M)) (v : E z.val.proj),
        (atlasEllipticSymbolTriple A B a hs hi).boundary.linearEquiv z v =
          a z.val.proj z.val.snd v := by
  /- The constructor stores the zero set verbatim. Its boundary is the
  actual linear Hom family converted fiberwise by LinearEquiv.ofBijective;
  that conversion has the same forward linear map. The induced pullbacks
  retain every original fiber vector. Read these two facts from the definition. -/

  exact ⟨rfl, fun _ _ ↦ rfl⟩

variable [T2Space M]

/-- The compact-support K class of the actual off-zero atlas symbol. -/
def atlasSymbolKClass (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  letI := A.isFiniteRank
  letI := B.isFiniteRank
  (atlasEllipticSymbolTriple A B a hs hi).compactSupportClass

/-- Only the original off-zero fiber maps determine the support class. -/
theorem atlasSymbolKClass_congr (a b : AtlasSymbolFunction (n := n) E F)
    (ha : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a)
    (hb : IsSmoothOffZeroAtlasSymbol A B b) (hj : IsEllipticAtlasSymbol b)
    (hab : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → a x ξ = b x ξ) :
    atlasSymbolKClass A B a ha hi = atlasSymbolKClass A B b hb hj := by
  /- The triples have the same two original pullbacks and the same zero
  control. Their boundary equivalences have the same forward action by hab,
  hence agree as linear equivalences. Proof irrelevance identifies their
  continuity certificates. Apply the existing support-class map to the
  equality of these actual triples; zero-section values play no part. -/
  classical
  let := A.isFiniteRank
  let := B.isFiniteRank
  have htriple : atlasEllipticSymbolTriple A B a ha hi =
      atlasEllipticSymbolTriple A B b hb hj := by
    -- The boundaries agree on the same punctured bundle, not merely after taking classes.
    change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
      CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L ↦ L v) (hab z.val.proj z.val.snd z.property)
  exact congrArg CompactSupportTriple.compactSupportClass htriple

/-- Equality of the regularized principal classes gives equality of the actual support classes. -/
theorem atlasSymbolKClass_eq_of_principalClass_eq
    (g k : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a b : AtlasSymbolFunction (n := n) E F)
    (ha : IsSmoothOffZeroAtlasSymbol A B a) (hha : IsHomogeneousAtlasSymbol m a)
    (hi : IsEllipticAtlasSymbol a)
    (hb : IsSmoothOffZeroAtlasSymbol A B b) (hhb : IsHomogeneousAtlasSymbol m b)
    (hj : IsEllipticAtlasSymbol b)
    (hab : atlasGlobalPrincipalSymbolClass A B m (atlasRegularizedSymbol A B g m a ha hha) =
      atlasGlobalPrincipalSymbolClass A B m (atlasRegularizedSymbol A B k m b hb hhb)) :
    atlasSymbolKClass A B a ha hi = atlasSymbolKClass A B b hb hj := by
  /- The fixed-degree principal recovery theorem gives equality of a and b
  at every nonzero cotangent vector, even for different radial metrics.
  Apply the preceding actual support-triple congruence. The original source
  and target bundles remain fixed; this does not assert that a principal
  quotient by itself records the zero-dimensional bundle difference. -/

  exact atlasSymbolKClass_congr A B a b ha hi hb hj
    ((atlasRegularizedSymbol_principalClass_eq_iff A B g k m a b ha hha hb hhb).mp hab)

/-- Empty punctured cotangent fibers retain the original source-minus-target bundle class. -/
theorem atlasSymbolKClass_of_dim_zero (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a) (hn : n = 0) :
    letI := A.isFiniteRank
    letI := B.isFiniteRank
    compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback
        ⟨(cotangentProjectionHomeomorphOfDimZero hn).symm,
          (cotangentProjectionHomeomorphOfDimZero hn).symm.continuous⟩
        (cotangentProjectionHomeomorphOfDimZero hn).symm.isProperMap
        (atlasSymbolKClass A B a hs hi)) =
      (smallBundle E).kZeroClass - (smallBundle F).kZeroClass := by
  /- Stage 1: in dimension zero the actual cotangent projection is the
  stated homeomorphism and its inverse is the zero section. The pulled-back
  raw symbol triple therefore has the original E,F and all of M as control.
  Its exterior is empty, so no bijectivity or common-rank condition remains.
  Stage 2: the compact-support-to-absolute comparison sends that triple to
  the source class minus the target class. Resizing by the existing actual
  smallBundle isomorphisms preserves these classes, including when their
  ranks differ from one connected component to another. -/
  let := A.isFiniteRank
  let := B.isFiniteRank
  let p := cotangentProjection (n := n) (M := M)
  let i : C(M, CotangentTotalSpace (n := n) (M := M)) :=
    ⟨(cotangentProjectionHomeomorphOfDimZero hn).symm,
      (cotangentProjectionHomeomorphOfDimZero hn).symm.continuous⟩
  have hi' : IsProperMap i := (cotangentProjectionHomeomorphOfDimZero hn).symm.isProperMap
  have hpi : p.comp i = ContinuousMap.id M := by
    ext x
    exact (cotangentProjectionHomeomorphOfDimZero_apply hn _).symm.trans
      ((cotangentProjectionHomeomorphOfDimZero hn).apply_symm_apply x)
  -- Pullback reassociation uses the same projection inverse and preserves original vectors.
  let eE : Iso ((i : _ → _) *ᵖ ((p : _ → M) *ᵖ E)) E := by
    have e := pullbackCompIso (E := E) p i
    rw [hpi] at e
    exact e.trans pullbackIdIso
  let eF : Iso ((i : _ → _) *ᵖ ((p : _ → M) *ᵖ F)) F := by
    have e := pullbackCompIso (E := F) p i
    rw [hpi] at e
    exact e.trans pullbackIdIso
  let b := (atlasEllipticSymbolTriple A B a hs hi).pullback i hi'
  have hmodel := b.compactSupportClass_eq_model (smallBundle E) (smallBundle F)
    (eE.trans (smallBundleIso E)) (eF.trans (smallBundleIso F))
  -- Compact-base normalization keeps the source-minus-target class, even for unequal ranks.
  calc
    _ = compactSupportKZeroToAbsolute b.compactSupportClass :=
      congrArg compactSupportKZeroToAbsolute
        ((atlasEllipticSymbolTriple A B a hs hi).compactSupportClass_pullback i hi').symm
    _ = (smallBundle E).kZeroClass - (smallBundle F).kZeroClass := by
      rw [hmodel]
      exact SupportBundleTriple.compactSupportClass_toAbsolute _

end AtiyahSinger

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {F : M → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]


set_option linter.unusedSectionVars false in
/-- The native smooth homogeneous elliptic symbol has exactly the same atlas properties. -/
theorem nativeAtlasSymbolFunction_homogeneous_properties (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a)
    (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsSmoothOffZeroAtlasSymbol
        (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
        (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) (nativeAtlasSymbolFunction a) ∧
      IsHomogeneousAtlasSymbol m (nativeAtlasSymbolFunction a) ∧
        IsEllipticAtlasSymbol (nativeAtlasSymbolFunction a) := by
  /- Stage 1: native atlas indices are the original designated bundle
  frames. The finite-coordinate conversions cancel, so their punctured
  coordinate symbols are exactly the native coordinate symbols. The native
  off-zero smoothness statement therefore supplies the atlas statement.
  Stage 2: forgetting a continuous-linear certificate preserves the actual
  fiber action, positive scaling formula and bijectivity. Both conclusions
  concern the same real cotangent vector and original complex fiber maps. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  -- Compare the original coordinate maps, including both finite-coordinate conversions.
  have hcoord (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      atlasGlobalSymbolInChart A B (nativeAtlasSymbolFunction a) c
          ⟨e, inferInstance⟩ ⟨f, inferInstance⟩ = globalSymbolInChart E F a c e f := by
    funext z η
    apply ContinuousLinearMap.ext
    intro v
    change EuclideanSpace ℂ (Fin r) at v
    have heBase : (A.chart ⟨e, inferInstance⟩).baseSet = e.baseSet := rfl
    have hfBase : (B.chart ⟨f, inferInstance⟩).baseSet = f.baseSet := rfl
    by_cases he : c.symm z ∈ e.baseSet
    · by_cases hf : c.symm z ∈ f.baseSet
      · have heFrame : A.frameLinearEquiv ⟨e, inferInstance⟩ (c.symm z) he =
            (e.continuousLinearEquivAt ℂ (c.symm z) he).toLinearEquiv.trans
              (EuclideanSpace.equiv (Fin r) ℂ).toLinearEquiv := by
          apply LinearEquiv.ext
          intro w
          rfl
        have hfFrame : B.frameLinearEquiv ⟨f, inferInstance⟩ (c.symm z) hf =
            (f.continuousLinearEquivAt ℂ (c.symm z) hf).toLinearEquiv.trans
              (EuclideanSpace.equiv (Fin q) ℂ).toLinearEquiv := by
          apply LinearEquiv.ext
          intro w
          rfl
        simp only [atlasGlobalSymbolInChart, heBase, hfBase, he, hf, and_self, dite_true]
        change (EuclideanSpace.equiv (Fin q) ℂ).symm
          ((B.frameLinearEquiv ⟨f, inferInstance⟩ (c.symm z) hf)
            (a (c.symm z) (covectorFromChart c (c.symm z) η)
              ((A.frameLinearEquiv ⟨e, inferInstance⟩ (c.symm z) he).symm
                ((EuclideanSpace.equiv (Fin r) ℂ) v)))) = _
        rw [heFrame, hfFrame]
        change (EuclideanSpace.equiv (Fin q) ℂ).symm
          ((EuclideanSpace.equiv (Fin q) ℂ)
            ((f.continuousLinearEquivAt ℂ (c.symm z) hf)
              (a (c.symm z) (covectorFromChart c (c.symm z) η)
                ((e.continuousLinearEquivAt ℂ (c.symm z) he).symm
                  ((EuclideanSpace.equiv (Fin r) ℂ).symm
                    ((EuclideanSpace.equiv (Fin r) ℂ) v)))))) =
          f.continuousLinearMapAt ℂ (c.symm z)
            (a (c.symm z) (covectorFromChart c (c.symm z) η)
              (e.symmL ℂ (c.symm z) v))
        rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
        change (f ⟨c.symm z, a (c.symm z) (covectorFromChart c (c.symm z) η)
          (e.symm (c.symm z) v)⟩).2 = _
        rw [e.symmL_apply he]
        exact (Trivialization.continuousLinearMapAt_apply_of_mem ℂ f hf _).symm
      · simp only [atlasGlobalSymbolInChart, heBase, hfBase, hf, and_false, dite_false]
        change (0 : EuclideanSpace ℂ (Fin q)) = f.continuousLinearMapAt ℂ (c.symm z)
          (a (c.symm z) (covectorFromChart c (c.symm z) η) (e.symmL ℂ (c.symm z) v))
        simp [Trivialization.continuousLinearMapAt, Trivialization.coe_linearMapAt, hf]
    · simp only [atlasGlobalSymbolInChart, heBase, hfBase, he, false_and, dite_false]
      change (0 : EuclideanSpace ℂ (Fin q)) = f.continuousLinearMapAt ℂ (c.symm z)
        (a (c.symm z) (covectorFromChart c (c.symm z) η) (e.symmL ℂ (c.symm z) v))
      rw [e.symmL_apply_of_notMem he, map_zero, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro c hc i j
    rcases i with ⟨e, he⟩
    rcases j with ⟨f, hf⟩
    let := he
    let := hf
    change ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart A B (nativeAtlasSymbolFunction a)
        c ⟨e, he⟩ ⟨f, hf⟩)) _
    rw [hcoord]
    exact hs c hc e f
  · -- Forgetting continuity preserves the same positive homogeneity identity.
    intro x ξ hξ t ht
    exact congrArg ContinuousLinearMap.toLinearMap (hh x ξ hξ t ht)
  · exact hi

variable [T2Space M]

/-- Native presentation cutoffs and atlas radial cutoffs give the same actual principal class. -/
theorem atlasRegularizedSymbol_principalClass_native
    (g : SmoothCotangentMetric (n := n) (M := M))
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F) (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a)
    (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    atlasGlobalPrincipalSymbolClass
        (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
        (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m
        (atlasRegularizedSymbol
          (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
          (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) g m
          (nativeAtlasSymbolFunction a)
          (nativeAtlasSymbolFunction_homogeneous_properties
            (n := n) (r := r) (q := q) m a hs hh hi).1
          (nativeAtlasSymbolFunction_homogeneous_properties
            (n := n) (r := r) (q := q) m a hs hh hi).2.1) =
      atlasGlobalPrincipalSymbolClass
        (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
        (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) m
        (nativeAtlasGlobalSymbol m (R.regularizedSymbol m a hs hh)) := by
  /- Stage 1: native coordinate transport retains the original Hom family.
  In every fixed common chart and compact spatial subset, the native finite
  presentation cutoff and the metric radial cutoff are both exactly one
  at sufficiently large coordinate frequency. Both regularizations therefore
  agree there with that same a; their difference has bounded frequency support
  locally uniformly in the base and is smooth across the zero section.
  Stage 2: that difference has every symbol order, hence order m-1. The
  existing atlas principal quotient identifies these two actual symbols.
  Ellipticity is carried with the chosen A10 data to reuse its native predicate
  certificate; it is not used to deduce any stronger regularization equality. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  let Q : GlobalSymbolFunction (n := n) E F := fun x ξ ↦
    (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) • a x ξ
  have hQval : nativeAtlasSymbolFunction Q =
      atlasRegularizedSymbolFunction g (nativeAtlasSymbolFunction a) := rfl
  have hprops := nativeAtlasSymbolFunction_homogeneous_properties m a hs hh hi
  have hQ : IsGlobalSymbol (n := n) (r := r) (q := q) E F m Q := by
    apply (isAtlasGlobalSymbol_native_iff m Q).mp
    rw [hQval]
    exact isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B g m
      (nativeAtlasSymbolFunction a) hprops.1 hprops.2.1
  -- Compare the two actual regularizations on enlarged compact coordinate sets.
  have hdiff : IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
      (Q - R.regularizedSymbolFunction a) := by
    intro c hc e f _ _
    let V := symbolChartDomain E F c e f
    let pa := globalSymbolInChart E F Q c e f
    let pb := globalSymbolInChart E F (R.regularizedSymbolFunction a) c e f
    have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
    have hsub : globalSymbolInChart E F (Q - R.regularizedSymbolFunction a) c e f =
        pa - pb := by
      ext z η v
      simp [globalSymbolInChart, pa, pb]
    rw [hsub]
    have ha := hQ c hc e f
    have hb := R.isGlobalSymbol_regularizedSymbolFunction m a hs hh c hc e f
    have hd : ContDiffOn ℝ ∞ (Function.uncurry (pa - pb)) (V ×ˢ Set.univ) := ha.1.sub hb.1
    refine ⟨hd, ?_⟩
    intro K hKV hK α β
    obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
    have hint : interior K' ⊆ V := interior_subset.trans hK'V
    obtain ⟨RR, hRR, hrecoverR⟩ :=
      R.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e f K' hK' hK'V
    -- Metric length has a uniform positive lower bound on the coordinate unit sphere.
    have hcov_smul (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
        covectorFromChart c (c.symm z) (t • η) = t • covectorFromChart c (c.symm z) η := by
      ext v
      change inner ℝ (t • η) (mfderiv _ _ c (c.symm z) v) =
        t * inner ℝ η (mfderiv _ _ c (c.symm z) v)
      exact real_inner_smul_left η _ t
    have hcov_ne (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
        (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) :
        covectorFromChart c (c.symm z) η ≠ 0 := by
      intro hzero
      have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
      rw [hzero] at h
      have hzero' : covectorInChart c (c.symm z) 0 = 0 := by ext u; rfl
      exact hη (h.symm.trans hzero')
    let L (z η : EuclideanSpace ℝ (Fin n)) :=
      g.length (c.symm z) (covectorFromChart c (c.symm z) η)
    let S := K' ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
    have hS : IsCompact S := hK'.prod (isCompact_sphere _ _)
    have hne (η : EuclideanSpace ℝ (Fin n))
        (hη : η ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : η ≠ 0 := by
      intro hz
      simp [hz] at hη
    have hcont : ContinuousOn (Function.uncurry L) S :=
      (g.contDiffOn_length_covectorFromChart c hc).continuousOn.mono
        (fun z hz ↦ ⟨(hK'V hz.1).1.1, hne z.2 hz.2⟩)
    obtain ⟨d, hdpos, hlow⟩ := hS.exists_forall_le' hcont (a := 0) (by
      intro z hz
      exact g.length_pos _ _ (hcov_ne z.1 (hK'V hz.1).1.1 z.2 (hne z.2 hz.2)))
    have hrecoverQ : ∀ z ∈ K', ∀ η, d⁻¹ ≤ ‖η‖ →
        pa z η = globalSymbolInChart E F a c e f z η := by
      intro z hz η hη
      have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hdpos) hη
      have hηne : η ≠ 0 := norm_pos_iff.mp hηpos
      let v := ‖η‖⁻¹ • η
      have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
      have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
      have hlen : L z η = ‖η‖ * L z v := by
        dsimp [L]
        conv_lhs => rw [← hscale, hcov_smul, g.length_smul]
        rw [abs_of_nonneg (norm_nonneg η)]
      have hlength : 1 ≤ L z η := by
        rw [hlen]
        have h := mul_le_mul_of_nonneg_left hη hdpos.le
        rw [mul_inv_cancel₀ hdpos.ne'] at h
        have hl := mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hz, hv⟩) (norm_nonneg η)
        exact h.trans (by simpa only [Function.uncurry, mul_comm] using hl)
      have hnorm : ‖EuclideanSpace.single (0 : Fin 1) (L z η)‖ = L z η := by
        simp only [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs,
          abs_of_nonneg (le_trans zero_le_one hlength)]
      have hone := highFrequencyCutoff_eq_one
        (EuclideanSpace.single (0 : Fin 1) (L z η)) (by simpa only [hnorm] using hlength)
      dsimp only [L] at hone
      simp only [pa, globalSymbolInChart, Q, hone, Complex.ofReal_one, one_smul]
    have hsupp : ∀ z ∈ interior K', ∀ η, max d⁻¹ RR ≤ ‖η‖ → (pa - pb) z η = 0 := by
      intro z hz η hη
      change pa z η - pb z η = 0
      rw [hrecoverQ z (interior_subset hz) η ((le_max_left _ _).trans hη)]
      dsimp only [pb]
      rw [hrecoverR z (interior_subset hz) η ((le_max_right _ _).trans hη), sub_self]
    -- Bounded frequency support on this neighborhood supplies every real symbol order.
    have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior (pa - pb)
      (max d⁻¹ RR) (hd.mono (Set.prod_mono hint subset_rfl)) hsupp (m - 1)
    exact hlocal.2 K hKK' hK α β
  -- The native coordinate bridge transports this same difference into the atlas quotient.
  apply (atlasGlobalPrincipalSymbolClass_eq_iff A B m _ _).mpr
  change IsAtlasGlobalSymbol A B (m - 1)
    (nativeAtlasSymbolFunction (Q - R.regularizedSymbolFunction a))
  exact (isAtlasGlobalSymbol_native_iff (m - 1) _).mpr hdiff

variable [CompactSpace M]

/-- Native and atlas support classes keep the same two original bundles and exterior map. -/
theorem atlasSymbolKClass_native (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a)
    (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    atlasSymbolKClass
        (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
        (nativeSmoothComplexBundleAtlas (n := n) (r := q) F)
        (nativeAtlasSymbolFunction a)
        (nativeAtlasSymbolFunction_homogeneous_properties
          (n := n) (r := r) (q := q) m a hs hh hi).1
        (nativeAtlasSymbolFunction_homogeneous_properties
          (n := n) (r := r) (q := q) m a hs hh hi).2.2 =
      symbolKClass (n := n) (r := r) (q := q) a hs.continuous hi := by
  /- Stage 1: the two constructions use the same phantom-model topology
  transport on E and F, the same actual cotangent pullbacks and the same
  zero-section control. Their exterior equivalences both act by a x xi
  on the original fiber vector, so these raw support triples agree.
  Stage 2: apply the existing compact-support class construction. The
  finite-rank certificates are propositions, and the support-class resizing
  retains their original isomorphisms. No unrelated K-group equivalence or
  replacement constant-rank bundle is introduced in this comparison. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_pullback (E := E) (cotangentProjection (n := n) (M := M))
  let := isFiniteRank_pullback (E := F) (cotangentProjection (n := n) (M := M))
  let := t2Space_cotangent (n := n) (M := M)
  let := locallyCompactSpace_cotangent (n := n) (M := M)
  have htriple : atlasEllipticSymbolTriple
      (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
      (nativeSmoothComplexBundleAtlas (n := n) (r := q) F)
      (nativeAtlasSymbolFunction a)
      (nativeAtlasSymbolFunction_homogeneous_properties m a hs hh hi).1
      (nativeAtlasSymbolFunction_homogeneous_properties m a hs hh hi).2.2 =
        ellipticSymbolTriple a hs.continuous hi := by
    -- Both raw boundaries apply the same Hom map to each original exterior vector.
    change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
      CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    exact (ellipticSymbolBoundary_apply a hs.continuous hi z v).symm
  exact congrArg CompactSupportTriple.compactSupportClass htriple

end AtiyahSinger

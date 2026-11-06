/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasEllipticRepresentative
public import AtiyahSinger.Analysis.AtlasClopenIndex
public import AtiyahSinger.Analysis.AtlasClopenQuantization
public import AtiyahSinger.Analysis.AtlasNativeIndex
public import AtiyahSinger.Analysis.AtlasOpenRegularization
public import AtiyahSinger.Analysis.AtlasOpenSymbolKClass
public import AtiyahSinger.Analysis.AtlasPseudodifferentialFredholm
public import AtiyahSinger.Analysis.ComponentAnalyticIndex

/-!
# The existing analytic index evaluated on actual atlas operators

Public module ID: M0226.

A10: the already defined analyticIndexOfComponents evaluates the symbol class
of every actual atlas elliptic PDO as its original smooth index and every
critical real-order Sobolev index. All compact-support cotangent K classes have
such representatives of every real order, including variable-rank bundles.

The operator is arbitrary with the stated principal class; it need not be a
chosen quantization or preserve connected components. Its cross-component
smoothing terms are retained. No new analytic-index homomorphism is introduced.
Sources: SG III.13 (13.7)--(13.8), pp.246--247; finite component and smooth-atlas
transport are explicit project supplements. The original component evaluation,
its Sobolev comparison, full-class realization and K-class index invariance are proved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isSmoothPositiveMeasure_comap_opens

variable {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
  (g : SmoothCotangentMetric (n := n) (M := M))
  (a : AtlasSymbolFunction (n := n) E F)
  (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
  (hP : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
    (atlasRegularizedSymbol A B g m a hs hh))
  (hi : IsEllipticAtlasSymbol a)

include g hh hP in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- SG (13.7): the original component index evaluates the actual atlas operator's symbol class. -/
theorem AtlasPseudodifferentialOperator.analyticIndexOfComponents_atlasSymbolKClass :
    analyticIndexOfComponents μ (atlasSymbolKClass A B a hs hi) =
      P.toLinearMap.index := by
  /- Quantize the exact restriction of the original regularized symbol
  separately on each clopen component. Extend these same local Fourier
  patches to obtain one global quantization with that principal symbol.
  Its actual section map is the diagonal block sum. The difference from
  P has one lower order and is compact at the critical Sobolev orders,
  so the smooth indices agree even when P couples different components.
  Finally compare each block with its compatible native model and retain
  the original symbol triple under proper cotangent restriction. This
  keeps the source and target bundles also in dimension zero. -/
  classical
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := Fintype.ofFinite (ConnectedComponents M)
  let U := manifoldComponent (n := n) (M := M)
  have hclosed (c : ConnectedComponents M) : IsClosed (U c : Set M) :=
    isClosed_singleton.preimage ConnectedComponents.continuous_coe
  have hdisjoint : Pairwise (fun c d ↦ Disjoint (U c : Set M) (U d : Set M)) := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    intro x hc hd
    exact hcd (hc.symm.trans hd)
  have hcover : (⋃ c, (U c : Set M)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨ConnectedComponents.mk x, rfl⟩
  let p := atlasRegularizedSymbol A B g m a hs hh
  let aU (c : ConnectedComponents M) : AtlasSymbolFunction (n := n) (M := U c)
      (ComplexBundle.Restrict E (U c)) (ComplexBundle.Restrict F (U c)) :=
    fun x ξ ↦ a x.val ξ
  let hsU (c : ConnectedComponents M) := hs.restrictOpen A B (U c)
  let hhU (c : ConnectedComponents M) : IsHomogeneousAtlasSymbol m (aU c) :=
    fun x ξ ↦ hh x.val ξ
  let hiU (c : ConnectedComponents M) : IsEllipticAtlasSymbol (aU c) :=
    fun x ξ ↦ hi x.val ξ
  let k (c : ConnectedComponents M) :=
    (SmoothCotangentMetric.nonempty (n := n) (M := U c)).some
  let q (c : ConnectedComponents M) :
      atlasGlobalSymbolSpace (A.restrictOpen (U c)) (B.restrictOpen (U c)) m :=
    ⟨fun x ξ ↦ p.val x.val ξ, p.property.restrictOpen A B (U c)⟩
  let R (c : ConnectedComponents M) :=
    (nonempty_atlasQuantizationPresentation (A.restrictOpen (U c)) (B.restrictOpen (U c))).some
  let PU (c : ConnectedComponents M) := (R c).quantize (q c)
  have hpU (c : ConnectedComponents M) : (PU c).principalSymbol =
      atlasGlobalPrincipalSymbolClass (A.restrictOpen (U c)) (B.restrictOpen (U c)) m
        (atlasRegularizedSymbol (A.restrictOpen (U c)) (B.restrictOpen (U c)) (k c) m
          (aU c) (hsU c) (hhU c)) :=
    ((R c).principalSymbol_quantize (q c)).trans
      (atlasRegularizedSymbol_principalClass_restrictOpen A B (U c) g (k c) m a hs hh)
  -- Each exact block is elliptic; its original smooth defects are finite-dimensional.
  have hfinite (c : ConnectedComponents M) :
      FiniteDimensional ℂ (PU c).toLinearMap.ker ∧
      FiniteDimensional ℂ
        ((B.restrictOpen (U c)).smoothSections ⧸ (PU c).toLinearMap.range) := by
    let L := (nonempty_atlasBundlePresentation (A.restrictOpen (U c))).some
    let K := (nonempty_atlasBundlePresentation (B.restrictOpen (U c))).some
    exact ⟨((PU c).index_sobolevExtension_of_homogeneous L K (k c) (aU c)
      (hsU c) (hhU c) (hpU c) (hiU c) 0).1,
      ((PU c).index_sobolevExtension_of_homogeneous L K (k c) (aU c)
        (hsU c) (hhU c) (hpU c) (hiU c) 0).2.1⟩
  let : ∀ c, FiniteDimensional ℂ (PU c).toLinearMap.ker := fun c ↦ (hfinite c).1
  let : ∀ c, FiniteDimensional ℂ
      ((B.restrictOpen (U c)).smoothSections ⧸ (PU c).toLinearMap.range) :=
    fun c ↦ (hfinite c).2
  obtain ⟨C, hC⟩ := exists_atlasClopenQuantization A B U hclosed hdisjoint hcover R
  have hsum : (C.quantize p).toLinearMap.index = ∑ c, (PU c).toLinearMap.index := by
    change (C.toLinearMap p).index = _
    rw [hC m p]
    exact index_atlasClopenBlockSum A B U hclosed hdisjoint hcover
      (fun c ↦ (PU c).toLinearMap)
  have hindex : P.toLinearMap.index = (C.quantize p).toLinearMap.index :=
    P.index_eq_of_principalSymbol_eq_homogeneous (C.quantize p) g a hs hh hP hi
      (hP.trans (C.principalSymbol_quantize p).symm)
  -- Native comparison applies separately at each original locally constant rank.
  have heval (c : ConnectedComponents M) :
      analyticIndex (μ.comap (Subtype.val : U c → M))
        (atlasSymbolKClass (A.restrictOpen (U c)) (B.restrictOpen (U c))
          (aU c) (hsU c) (hiU c)) = (PU c).toLinearMap.index := by
    let := (A.restrictOpen (U c)).isFiniteRank
    let := (B.restrictOpen (U c)).isFiniteRank
    let x₀ : U c := Classical.choice inferInstance
    have hr (x : U c) : Module.finrank ℂ (E x.val) = Module.finrank ℂ (E x₀.val) :=
      IsLocallyConstant.apply_eq_of_preconnectedSpace (X := U c)
        (ComplexBundle.isLocallyConstant_finrank (ComplexBundle.Restrict E (U c))) x x₀
    have hq (x : U c) : Module.finrank ℂ (F x.val) = Module.finrank ℂ (F x₀.val) :=
      IsLocallyConstant.apply_eq_of_preconnectedSpace (X := U c)
        (ComplexBundle.isLocallyConstant_finrank (ComplexBundle.Restrict F (U c))) x x₀
    have h := (PU c).analyticIndexOfComponents_of_constant_rank
      (μ.comap (Subtype.val : U c → M)) _ _ hr hq (k c) (aU c)
      (hsU c) (hhU c) (hiU c) (hpU c)
    rw [analyticIndexOfComponents_eq_analyticIndex] at h
    exact h
  rw [hindex, hsum]
  unfold analyticIndexOfComponents
  rw [AddMonoidHom.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro c _
  change analyticIndex (μ.comap (Subtype.val : U c → M))
    (cotangentKZeroComponents (atlasSymbolKClass A B a hs hi) c) = _
  have hK := atlasSymbolKClass_restrictOpen A B (U c) (hclosed c) a hs hi
  rw [show cotangentKZeroComponents (atlasSymbolKClass A B a hs hi) c =
    atlasSymbolKClass (A.restrictOpen (U c)) (B.restrictOpen (U c))
      (aU c) (hsU c) (hiU c) from hK.symm]
  exact heval c

include g hh hP in
/-- The same K class evaluates every critical Sobolev realization of the original PDO. -/
theorem AtlasPseudodifferentialOperator.analyticIndexOfComponents_sobolevExtension
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) (s : ℝ) :
    analyticIndexOfComponents μ (atlasSymbolKClass A B a hs hi) =
      (P.sobolevExtension L K s).index := by
  /- Evaluate the original symbol class by the preceding theorem for this
  same P. Its actual kernel and cokernel comparisons identify the smooth
  index with the index of the stated L,K completion at s and s-m. This
  allows arbitrary real s and finite presentations, without changing the
  density in the existing index map or selecting a replacement operator. -/
  exact (P.analyticIndexOfComponents_atlasSymbolKClass μ g a hs hh hP hi).trans
    (P.index_sobolevExtension_of_homogeneous L K g a hs hh hP hi s).2.2.symm

/-- Every K class has an actual PDO of the requested order with the existing analytic index. -/
theorem exists_atlas_elliptic_representative_with_index
    (g : SmoothCotangentMetric (n := n) (M := M))
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) (m : ℝ) :
    ∃ E F : ComplexBundle.FiniteBundle M,
      ∃ A : SmoothComplexBundleAtlas (n := n) E.Fiber,
      ∃ B : SmoothComplexBundleAtlas (n := n) F.Fiber,
      ∃ a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber,
      ∃ hs : IsSmoothOffZeroAtlasSymbol A B a,
      ∃ hh : IsHomogeneousAtlasSymbol m a,
      ∃ hi : IsEllipticAtlasSymbol a,
      ∃ P : AtlasPseudodifferentialOperator A B m,
        P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
          (atlasRegularizedSymbol A B g m a hs hh) ∧
        atlasSymbolKClass A B a hs hi = u ∧
        FiniteDimensional ℂ P.toLinearMap.ker ∧
        FiniteDimensional ℂ (B.smoothSections ⧸ P.toLinearMap.range) ∧
        analyticIndexOfComponents μ u = P.toLinearMap.index ∧
        ∀ (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) (s : ℝ),
          (P.sobolevExtension L K s).IsFredholm ∧
          analyticIndexOfComponents μ u = (P.sobolevExtension L K s).index := by
  /- Stage 1: choose the smooth atlas elliptic representative of u of the
  specified real order m, and quantize its actual regularization using g.
  Retain all these same witnesses, including the original finite bundles.
  Stage 2: choose finite presentations to obtain smooth kernel/cokernel
  finiteness by the atlas Fredholm and regularity theorems. Evaluate the
  original component index on the displayed original support class.
  Stage 3: apply the Sobolev conclusions to every L,K,s, keeping the same
  P, a, hs, hh, hi and principal equality. This proves realization on the
  full K group, not just on fixed globally constant-rank representatives. -/
  obtain ⟨E, F, A, B, a, hs, hh, hi, P, hP, hclass⟩ :=
    exists_atlas_elliptic_pseudodifferential_representative g u m
  let L := (nonempty_atlasBundlePresentation A).some
  let K := (nonempty_atlasBundlePresentation B).some
  have hfinite := P.index_sobolevExtension_of_homogeneous L K g a hs hh hP hi 0
  have heval : analyticIndexOfComponents μ u = P.toLinearMap.index := by
    rw [← hclass]
    exact P.analyticIndexOfComponents_atlasSymbolKClass μ g a hs hh hP hi
  refine ⟨E, F, A, B, a, hs, hh, hi, P, hP, hclass, hfinite.1, hfinite.2.1, heval, ?_⟩
  intro L K s
  refine ⟨P.isFredholm_sobolevExtension_of_homogeneous L K g a hs hh hP hi s, ?_⟩
  exact heval.trans (P.index_sobolevExtension_of_homogeneous L K g a hs hh hP hi s).2.2.symm

include g hh hP in
/-- Equal actual symbol K classes give equal indices, across orders and variable-rank bundles. -/
theorem AtlasPseudodifferentialOperator.index_eq_of_atlasSymbolKClass_eq
    {E' : M → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
    [TopologicalSpace (TotalSpace Unit E')]
    {F' : M → Type*} [∀ x, AddCommGroup (F' x)] [∀ x, Module ℂ (F' x)]
    [TopologicalSpace (TotalSpace Unit F')]
    {A' : SmoothComplexBundleAtlas (n := n) E'}
    {B' : SmoothComplexBundleAtlas (n := n) F'} {t : ℝ}
    (Q : AtlasPseudodifferentialOperator A' B' t)
    (k : SmoothCotangentMetric (n := n) (M := M))
    (b : AtlasSymbolFunction (n := n) E' F')
    (hb : IsSmoothOffZeroAtlasSymbol A' B' b) (hhb : IsHomogeneousAtlasSymbol t b)
    (hQ : Q.principalSymbol = atlasGlobalPrincipalSymbolClass A' B' t
      (atlasRegularizedSymbol A' B' k t b hb hhb)) (hj : IsEllipticAtlasSymbol b)
    (hab : atlasSymbolKClass A B a hs hi = atlasSymbolKClass A' B' b hb hj) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  /- Choose any smooth positive density on the compact smooth base.
  Evaluate both actual symbol classes with its one existing component
  homomorphism. Each evaluation is the index of its given PDO by
  the preceding theorem. Rewrite using hab. Source and target bundles,
  orders, radial metrics and atlas choices may differ; equality is in the
  same original compact-support K group, so no transport is suppressed. -/
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  rw [← P.analyticIndexOfComponents_atlasSymbolKClass μ g a hs hh hP hi,
    hab, Q.analyticIndexOfComponents_atlasSymbolKClass μ k b hb hhb hQ hj]

end AtiyahSinger

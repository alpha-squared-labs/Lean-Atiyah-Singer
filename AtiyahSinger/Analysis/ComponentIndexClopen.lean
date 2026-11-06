/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasAnalyticIndex

/-!
# Analytic index under finite clopen partitions

Public module ID: M0378.

The existing component analytic index is additive under any finite clopen
partition, even when the pieces are disconnected and bundle ranks vary.
Represent the original K class by a smooth atlas symbol, quantize its actual
restrictions, and extend those same Fourier patches. The resulting operator
is the exact block sum. Each summand uses the original density restricted
along the specified inclusion and the proper cotangent pullback.
This is a project bridge for finite-disjoint-union functoriality of the
analytic index, using SG III.13 (13.7)--(13.8) and the actual atlas construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff BigOperators

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isSmoothPositiveMeasure_comap_opens

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any finite clopen partition splits the original analytic index by actual K restrictions. -/
theorem analyticIndexOfComponents_eq_sum_clopen {ι : Type*} [Fintype ι]
    (U : ι → Opens M) (hclosed : ∀ i, IsClosed (U i : Set M))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i, (U i : Set M)) = Set.univ)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    analyticIndexOfComponents μ u =
      ∑ i, letI : CompactSpace (U i) := isCompact_iff_compactSpace.mp (hclosed i).isCompact
        analyticIndexOfComponents (μ.comap (Subtype.val : U i → M))
          (compactSupportKZeroPullback
            ⟨cotangentOpenInclusion (U i),
              (isOpenEmbedding_cotangentOpenInclusion (U i)).continuous⟩
            (isProperMap_cotangentOpenInclusion (U i) (hclosed i)) u) := by
  classical
  let : ∀ i, CompactSpace (U i) :=
    fun i ↦ isCompact_iff_compactSpace.mp (hclosed i).isCompact
  -- Keep a single variable-rank representative of the supplied global K class.
  obtain ⟨E, F, A, B, a, hs, hh, hi, hclass⟩ :=
    exists_smooth_atlas_elliptic_representative.{_, 0, 0} u 0
  let g := (SmoothCotangentMetric.nonempty (n := n) (M := M)).some
  let p := atlasRegularizedSymbol A B g 0 a hs hh
  let aU (i : ι) : AtlasSymbolFunction (n := n) (M := U i)
      (ComplexBundle.Restrict E.Fiber (U i)) (ComplexBundle.Restrict F.Fiber (U i)) :=
    fun x ξ ↦ a x.val ξ
  let hsU (i : ι) := hs.restrictOpen A B (U i)
  let hhU (i : ι) : IsHomogeneousAtlasSymbol 0 (aU i) := fun x ξ ↦ hh x.val ξ
  let hiU (i : ι) : IsEllipticAtlasSymbol (aU i) := fun x ξ ↦ hi x.val ξ
  let k (i : ι) := (SmoothCotangentMetric.nonempty (n := n) (M := U i)).some
  -- Use the exact restricted global regularization, retaining each local Fourier patch.
  let q (i : ι) : atlasGlobalSymbolSpace (A.restrictOpen (U i)) (B.restrictOpen (U i)) 0 :=
    ⟨fun x ξ ↦ p.val x.val ξ, p.property.restrictOpen A B (U i)⟩
  let R (i : ι) :=
    (nonempty_atlasQuantizationPresentation (A.restrictOpen (U i)) (B.restrictOpen (U i))).some
  let PU (i : ι) := (R i).quantize (q i)
  have hpU (i : ι) : (PU i).principalSymbol =
      atlasGlobalPrincipalSymbolClass (A.restrictOpen (U i)) (B.restrictOpen (U i)) 0
        (atlasRegularizedSymbol (A.restrictOpen (U i)) (B.restrictOpen (U i)) (k i) 0
          (aU i) (hsU i) (hhU i)) :=
    ((R i).principalSymbol_quantize (q i)).trans
      (atlasRegularizedSymbol_principalClass_restrictOpen A B (U i) g (k i) 0 a hs hh)
  have hfinite (i : ι) :
      FiniteDimensional ℂ (PU i).toLinearMap.ker ∧
      FiniteDimensional ℂ
        ((B.restrictOpen (U i)).smoothSections ⧸ (PU i).toLinearMap.range) := by
    let L := (nonempty_atlasBundlePresentation (A.restrictOpen (U i))).some
    let K := (nonempty_atlasBundlePresentation (B.restrictOpen (U i))).some
    exact ⟨((PU i).index_sobolevExtension_of_homogeneous L K (k i) (aU i)
      (hsU i) (hhU i) (hpU i) (hiU i) 0).1,
      ((PU i).index_sobolevExtension_of_homogeneous L K (k i) (aU i)
        (hsU i) (hhU i) (hpU i) (hiU i) 0).2.1⟩
  let : ∀ i, FiniteDimensional ℂ (PU i).toLinearMap.ker := fun i ↦ (hfinite i).1
  let : ∀ i, FiniteDimensional ℂ
      ((B.restrictOpen (U i)).smoothSections ⧸ (PU i).toLinearMap.range) :=
    fun i ↦ (hfinite i).2
  -- Extend the same patches: the actual global section map is their diagonal block sum.
  obtain ⟨C, hC⟩ := exists_atlasClopenQuantization A B U hclosed hdisjoint hcover R
  have hsum : (C.quantize p).toLinearMap.index = ∑ i, (PU i).toLinearMap.index := by
    change (C.toLinearMap p).index = _
    rw [hC 0 p]
    exact index_atlasClopenBlockSum A B U hclosed hdisjoint hcover
      (fun i ↦ (PU i).toLinearMap)
  rw [← hclass,
    (C.quantize p).analyticIndexOfComponents_atlasSymbolKClass μ g a hs hh
      (C.principalSymbol_quantize p) hi, hsum]
  apply Finset.sum_congr rfl
  intro i _
  -- Evaluate each block with the same restricted density and identify its actual K pullback.
  rw [← atlasSymbolKClass_restrictOpen A B (U i) (hclosed i) a hs hi]
  exact ((PU i).analyticIndexOfComponents_atlasSymbolKClass
    (μ.comap (Subtype.val : U i → M)) (k i) (aU i) (hsU i) (hhU i) (hpU i) (hiU i)).symm

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoPseudodifferential
public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolTransport
public import AtiyahSinger.Analysis.AtlasPrincipalIndex
public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Analysis.IndexIntertwining
public import AtiyahSinger.Analysis.NativeAtlasHomogeneousComparison
public import AtiyahSinger.Geometry.AtlasNativeModel

/-!
# Evaluation of atlas operators on compatible native bundle models

Public module ID: M0262.

A native quantization realizes the same homogeneous symbol. The actual
native-atlas section equivalence and same-principal index invariance compare
it with the supplied atlas operator. Compatible smooth bundle isomorphisms
then extend this calculation to any prescribed constant-rank atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
/-- The existing index evaluates an arbitrary atlas operator on the same native bundles. -/
theorem analyticIndexOfComponents_nativeAtlas
    (E F : SmoothFiniteComplexBundle (n := n) M) (m : ℝ)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
    let B := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
    ∀ (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
      (hi : IsEllipticAtlasSymbol a) (P : AtlasPseudodifferentialOperator A B m),
      P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
        (atlasRegularizedSymbol A B g m a hs hh) →
      analyticIndexOfComponents μ (atlasSymbolKClass A B a hs hi) = P.toLinearMap.index := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
  dsimp only
  intro hs hh hi P hP
  -- Finite-dimensional continuity converts exactly the same original fiber maps.
  let : ∀ x : M, FiniteDimensional ℂ (E.Fiber x) := fun x ↦ by
    obtain ⟨i, hi⟩ := A.covers x
    exact FiniteDimensional.of_injective (A.frameLinearEquiv i x hi).toLinearMap
      (A.frameLinearEquiv i x hi).injective
  let b : GlobalSymbolFunction (n := n) E.Fiber F.Fiber :=
    fun x ξ ↦ (a x ξ).toContinuousLinearMap
  have hb : nativeAtlasSymbolFunction b = a := rfl
  have hsb : IsSmoothOffZeroGlobalSymbol (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber b :=
    (isSmoothOffZeroAtlasSymbol_native_iff b).mp (hb.symm ▸ hs)
  have hhb : IsHomogeneousGlobalSymbol E.Fiber F.Fiber m b := by
    intro x ξ hξ t ht
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) (hh x ξ hξ t ht)
  have hib : IsEllipticGlobalSymbol E.Fiber F.Fiber b := hi
  let b' : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber m := ⟨b, hsb, hhb⟩
  let R := (nonempty_quantizationPresentation (n := n) (r := E.rank) (q := F.rank)
    (E := E.Fiber) (F := F.Fiber)).some
  let q := R.regularizedSymbol m b hsb hhb
  let Q := R.quantize μ q
  have hQ := R.principalSymbol_quantize μ q
  have hiQ : Q.IsElliptic := (Q.isElliptic_iff_homogeneous R b' hQ).mpr hib
  let QA := Q.toAtlasPseudodifferentialOperator
  have hQA : QA.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
      (atlasRegularizedSymbol A B g m a hs hh) := by
    rw [Q.principalSymbol_toAtlasPseudodifferentialOperator q hQ]
    exact (atlasRegularizedSymbol_principalClass_native g R m b hsb hhb hib).symm
  -- Compare this native quantization with P in the original atlas principal quotient.
  have hindex := P.index_eq_of_principalSymbol_eq_homogeneous QA g a hs hh hP hi
    (hP.trans hQA.symm)
  let S := nativeSmoothSectionLinearEquiv (n := n) (r := E.rank) E.Fiber
  let T := nativeSmoothSectionLinearEquiv (n := n) (r := F.rank) F.Fiber
  have hnative : QA.toLinearMap.index = Q.toLinearMap.index :=
    index_eq_of_linearEquiv QA.toLinearMap Q.toLinearMap S T (fun u ↦ by
      change Q.toLinearMap (S u) = T (T.symm (Q.toLinearMap (S u)))
      exact (T.apply_symm_apply _).symm)
  have hclass : atlasSymbolKClass A B a hs hi =
      Q.symbolKClassOfHomogeneous R b' hQ hiQ := by
    exact atlasSymbolKClass_native m b hsb hhb hib
  rw [hclass, Q.analyticIndexOfComponents_symbolKClassOfHomogeneous μ R b' hQ hiQ]
  exact hnative.symm.trans hindex.symm

variable {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
/-- Constant original fiber ranks permit evaluation through compatible smooth native models. -/
theorem AtlasPseudodifferentialOperator.analyticIndexOfComponents_of_constant_rank
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (r q : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r)
    (hq : ∀ x, Module.finrank ℂ (F x) = q)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
    (hi : IsEllipticAtlasSymbol a)
    (hP : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
      (atlasRegularizedSymbol A B g m a hs hh)) :
    analyticIndexOfComponents μ (atlasSymbolKClass A B a hs hi) = P.toLinearMap.index := by
  classical
  obtain ⟨EN, _, hEN⟩ := A.exists_native_model_with_atlasMaps r hr
  obtain ⟨FN, _, hFN⟩ := B.exists_native_model_with_atlasMaps q hq
  let := modelTopology (EuclideanSpace ℂ (Fin EN.rank)) EN.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin FN.rank)) FN.Fiber
  obtain ⟨e, he, hei⟩ := hEN
  obtain ⟨f, hf, hfi⟩ := hFN
  let C := nativeSmoothComplexBundleAtlas (n := n) (r := EN.rank) EN.Fiber
  let D := nativeSmoothComplexBundleAtlas (n := n) (r := FN.rank) FN.Fiber
  -- These same bundle isomorphisms transport both homogeneous data and the actual operator.
  obtain ⟨b, hb, hhb, hib, hvalue⟩ :=
    exists_atlasHomogeneousSymbol_of_bundleIso e f hei hf a hs hh hi
  obtain ⟨hp, Q, _, hQ, hindex⟩ :=
    P.exists_bundleIso_conjugate e f he hei hf hfi (atlasRegularizedSymbol A B g m a hs hh) hP
  have hregular : (⟨fun x ξ ↦ (f.toHom.linearMap x).comp
        (((atlasRegularizedSymbol A B g m a hs hh).val x ξ).comp
          (e.symm.toHom.linearMap x)), hp⟩ : atlasGlobalSymbolSpace C D m) =
      atlasRegularizedSymbol C D g m b hb hhb := by
    apply Subtype.ext
    funext x ξ
    apply LinearMap.ext
    intro v
    change f.linearEquiv x
      ((highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) •
        a x ξ ((e.linearEquiv x).symm v)) =
      (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) • b x ξ v
    rw [map_smul, hvalue]
  have hQ' : Q.principalSymbol = atlasGlobalPrincipalSymbolClass C D m
      (atlasRegularizedSymbol C D g m b hb hhb) :=
    hQ.trans (congrArg (atlasGlobalPrincipalSymbolClass C D m) hregular)
  have hclass : atlasSymbolKClass A B a hs hi = atlasSymbolKClass C D b hb hib := by
    apply atlasSymbolKClass_eq_of_bundleIso e f a b hs hi hb hib
    intro x ξ _ v
    rw [hvalue, LinearEquiv.symm_apply_apply]
  rw [hclass, analyticIndexOfComponents_nativeAtlas μ EN FN m g b hb hhb hib Q hQ']
  exact hindex

end AtiyahSinger

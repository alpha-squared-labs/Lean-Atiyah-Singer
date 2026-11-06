/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoPseudodifferential
public import AtiyahSinger.Analysis.IndexIntertwining
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# The full principal representative in specified native bundle models

Public module ID: M0264.

Smooth conjugation transports the given atlas PDO to the specified native
bundles, retaining its exact section action, full principal representative and
index. The full representative is the literal fiberwise conjugate of the
supplied original symbol. Finite-dimensional continuity changes only its Hom
carrier. The native principal quotient is recovered by comparing the same
lower-order difference through the native-atlas symbol equivalence.

This is the native form of smooth bundle conjugation in SG III.3. It allows
subsequent metric adjunction to use this very representative and these very
bundle maps. It assumes no ellipticity or homogeneous representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified native conjugate retains the same full principal symbol and section action. -/
theorem AtlasPseudodifferentialOperator.exists_native_conjugate_principalSymbol {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m)
    (p : atlasGlobalSymbolSpace A B m)
    (hp : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m p)
    (N₀ N₁ : SmoothFiniteComplexBundle (n := n) M) :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
    let B₀ := nativeSmoothComplexBundleAtlas (n := n) (r := N₀.rank) N₀.Fiber
    let B₁ := nativeSmoothComplexBundleAtlas (n := n) (r := N₁.rank) N₁.Fiber
    ∀ (e : Iso E N₀.Fiber) (f : Iso F N₁.Fiber)
      (he : IsSmoothAtlasBundleMap A B₀ e.toHom.linearMap)
      (hei : IsSmoothAtlasBundleMap B₀ A e.symm.toHom.linearMap)
      (hf : IsSmoothAtlasBundleMap B B₁ f.toHom.linearMap)
      (hfi : IsSmoothAtlasBundleMap B₁ B f.symm.toHom.linearMap),
      let S₀ := (atlasSmoothSectionEquiv A B₀ e he hei).trans
        (nativeSmoothSectionLinearEquiv (n := n) (r := N₀.rank) N₀.Fiber)
      let S₁ := (atlasSmoothSectionEquiv B B₁ f hf hfi).trans
        (nativeSmoothSectionLinearEquiv (n := n) (r := N₁.rank) N₁.Fiber)
      ∃ (pn : globalSymbolSpace (n := n) (r := N₀.rank) (q := N₁.rank)
          N₀.Fiber N₁.Fiber m)
        (Pn : PseudodifferentialOperator (n := n) (r := N₀.rank) (q := N₁.rank)
          N₀.Fiber N₁.Fiber μ m),
        (∀ x ξ, (pn.val x ξ).toLinearMap = (f.toHom.linearMap x).comp
          ((p.val x ξ).comp (e.symm.toHom.linearMap x))) ∧
        Pn.toLinearMap = S₁.toLinearMap.comp (P.toLinearMap.comp S₀.symm.toLinearMap) ∧
        Pn.principalSymbol = globalPrincipalSymbolClass N₀.Fiber N₁.Fiber m pn ∧
        Pn.toLinearMap.index = P.toLinearMap.index := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  intro B₀ B₁ e f he hei hf hfi S₀ S₁
  -- The native quotient is detected by the same lower-order difference in its atlas form.
  have hprincipal_of_atlas
      (R : PseudodifferentialOperator (n := n) (r := N₀.rank) (q := N₁.rank)
        N₀.Fiber N₁.Fiber μ m)
      (r : globalSymbolSpace (n := n) (r := N₀.rank) (q := N₁.rank)
        N₀.Fiber N₁.Fiber m)
      (hR : R.toAtlasPseudodifferentialOperator.principalSymbol =
        atlasGlobalPrincipalSymbolClass B₀ B₁ m (nativeAtlasGlobalSymbol m r)) :
      R.principalSymbol = globalPrincipalSymbolClass N₀.Fiber N₁.Fiber m r := by
    obtain ⟨s, hs⟩ :=
      globalPrincipalSymbolClass_surjective N₀.Fiber N₁.Fiber m R.principalSymbol
    have hRs := R.principalSymbol_toAtlasPseudodifferentialOperator s hs.symm
    have hclass : atlasGlobalPrincipalSymbolClass B₀ B₁ m (nativeAtlasGlobalSymbol m s) =
        atlasGlobalPrincipalSymbolClass B₀ B₁ m (nativeAtlasGlobalSymbol m r) :=
      hRs.symm.trans hR
    have hd : IsGlobalSymbol (n := n) (r := N₀.rank) (q := N₁.rank)
        N₀.Fiber N₁.Fiber (m - 1) (s.val - r.val) := by
      apply (isAtlasGlobalSymbol_native_iff (m - 1) (s.val - r.val)).mp
      have hdiff : nativeAtlasSymbolFunction (s.val - r.val) =
          (nativeAtlasGlobalSymbol m s).val - (nativeAtlasGlobalSymbol m r).val := by
        funext x ξ
        apply LinearMap.ext
        intro v
        rfl
      rw [hdiff]
      exact (atlasGlobalPrincipalSymbolClass_eq_iff B₀ B₁ m _ _).mp hclass
    exact hs.symm.trans
      ((globalPrincipalSymbolClass_eq_iff N₀.Fiber N₁.Fiber m s r).mpr hd)
  -- The strong atlas conjugation keeps the original full representative and both bundle maps.
  obtain ⟨hq, Q, hQ, hQsymbol, _⟩ :=
    P.exists_bundleIso_conjugate e f he hei hf hfi p hp
  let q : atlasGlobalSymbolSpace B₀ B₁ m :=
    ⟨fun x ξ ↦ (f.toHom.linearMap x).comp
      ((p.val x ξ).comp (e.symm.toHom.linearMap x)), hq⟩
  let (x : M) : FiniteDimensional ℂ (N₀.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber x
  let qn : GlobalSymbolFunction (n := n) N₀.Fiber N₁.Fiber :=
    fun x ξ ↦ (q.val x ξ).toContinuousLinearMap
  have hqnNative : nativeAtlasSymbolFunction qn = q.val := by
    funext x ξ
    apply LinearMap.ext
    intro v
    rfl
  have hqn : IsGlobalSymbol (n := n) (r := N₀.rank) (q := N₁.rank)
      N₀.Fiber N₁.Fiber m qn := by
    apply (isAtlasGlobalSymbol_native_iff m qn).mp
    rw [hqnNative]
    exact q.property
  let pn : globalSymbolSpace (n := n) (r := N₀.rank) (q := N₁.rank)
      N₀.Fiber N₁.Fiber m := ⟨qn, hqn⟩
  have hpnNative : nativeAtlasGlobalSymbol m pn = q := Subtype.ext hqnNative
  -- The native section maps are the literal identity on the original fiber values.
  let i₀ := nativeSmoothSectionLinearEquiv (n := n) (r := N₀.rank) N₀.Fiber
  let i₁ := nativeSmoothSectionLinearEquiv (n := n) (r := N₁.rank) N₁.Fiber
  let Pmap := i₁.toLinearMap.comp (Q.toLinearMap.comp i₀.symm.toLinearMap)
  have hmap : i₁.symm.toLinearMap.comp (Pmap.comp i₀.toLinearMap) = Q.toLinearMap := by
    apply LinearMap.ext
    intro u
    change i₁.symm (i₁ (Q.toLinearMap (i₀.symm (i₀ u)))) = Q.toLinearMap u
    rw [i₀.symm_apply_apply, i₁.symm_apply_apply]
  have hnative : IsPseudodifferentialOperator N₀.Fiber N₁.Fiber μ m Pmap := by
    apply (isAtlasPseudodifferentialOperator_native_iff μ m Pmap).mp
    rw [hmap]
    exact Q.isPseudodifferentialOperator
  let Pn : PseudodifferentialOperator (n := n) (r := N₀.rank) (q := N₁.rank)
      N₀.Fiber N₁.Fiber μ m := ⟨Pmap, hnative⟩
  have hPn : Pn.toAtlasPseudodifferentialOperator = Q := by
    have hext (U V : AtlasPseudodifferentialOperator B₀ B₁ m)
        (h : U.toLinearMap = V.toLinearMap) : U = V := by
      cases U with
      | mk U hU =>
        cases V with
        | mk V hV =>
          change U = V at h
          subst V
          rfl
    exact hext _ _ hmap
  -- The retained atlas representative is exactly the native continuous Hom map just constructed.
  have hPnsymbol : Pn.toAtlasPseudodifferentialOperator.principalSymbol =
      atlasGlobalPrincipalSymbolClass B₀ B₁ m (nativeAtlasGlobalSymbol m pn) := by
    rw [hPn, hpnNative]
    exact hQsymbol
  have hprincipal : Pn.principalSymbol = globalPrincipalSymbolClass N₀.Fiber N₁.Fiber m pn :=
    hprincipal_of_atlas Pn pn hPnsymbol
  have haction : Pn.toLinearMap =
      S₁.toLinearMap.comp (P.toLinearMap.comp S₀.symm.toLinearMap) := by
    change i₁.toLinearMap.comp (Q.toLinearMap.comp i₀.symm.toLinearMap) = _
    rw [hQ]
    rfl
  -- The same smooth equivalences identify both the kernel and the quotient cokernel.
  have hindex : P.toLinearMap.index = Pn.toLinearMap.index :=
    index_eq_of_linearEquiv P.toLinearMap Pn.toLinearMap S₀ S₁ (fun u ↦ by
      rw [haction]
      change S₁ (P.toLinearMap (S₀.symm (S₀ u))) = S₁ (P.toLinearMap u)
      rw [S₀.symm_apply_apply])
  exact ⟨pn, Pn, fun _ _ ↦ rfl, haction, hprincipal, hindex.symm⟩

end AtiyahSinger

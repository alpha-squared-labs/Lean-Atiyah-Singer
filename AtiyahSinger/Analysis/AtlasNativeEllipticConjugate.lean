/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoEllipticity

/-!
# The same elliptic PDO in specified native bundle models

Public module ID: M0261.

The actual smooth bundle isomorphisms transport the atlas PDO to the given
native bundles. Both its smooth action and its full-symbol ellipticity use
these same section equivalences. No substitute operator or native model is
chosen. This is the native-model form of smooth bundle conjugation.
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
/-- The actual elliptic atlas PDO has the specified native conjugate with the same action. -/
theorem AtlasPseudodifferentialOperator.exists_elliptic_native_conjugate {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m) (hP : P.IsElliptic)
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
      ∃ Pn : PseudodifferentialOperator (n := n) (r := N₀.rank) (q := N₁.rank)
          N₀.Fiber N₁.Fiber μ m,
        Pn.toLinearMap = S₁.toLinearMap.comp (P.toLinearMap.comp S₀.symm.toLinearMap) ∧
        Pn.IsElliptic := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  intro B₀ B₁ e f he hei hf hfi S₀ S₁
  -- First transport through the exact bundle maps in the atlas calculus.
  obtain ⟨Pa, hPa, hePa⟩ := P.exists_elliptic_bundleIso_conjugate hP e f he hei hf hfi
  let i₀ := nativeSmoothSectionLinearEquiv (n := n) (r := N₀.rank) N₀.Fiber
  let i₁ := nativeSmoothSectionLinearEquiv (n := n) (r := N₁.rank) N₁.Fiber
  let Pmap := i₁.toLinearMap.comp (Pa.toLinearMap.comp i₀.symm.toLinearMap)
  have hmap : i₁.symm.toLinearMap.comp (Pmap.comp i₀.toLinearMap) = Pa.toLinearMap := by
    apply LinearMap.ext
    intro u
    simp only [Pmap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      i₀.symm_apply_apply, i₁.symm_apply_apply]
  have hnative : IsPseudodifferentialOperator N₀.Fiber N₁.Fiber μ m Pmap := by
    apply (isAtlasPseudodifferentialOperator_native_iff μ m Pmap).mp
    rw [hmap]
    exact Pa.isPseudodifferentialOperator
  let Pn : PseudodifferentialOperator (n := n) (r := N₀.rank) (q := N₁.rank)
      N₀.Fiber N₁.Fiber μ m := ⟨Pmap, hnative⟩
  refine ⟨Pn, ?_, ?_⟩
  · change i₁.toLinearMap.comp (Pa.toLinearMap.comp i₀.symm.toLinearMap) = _
    rw [hPa]
    rfl
  · -- Returning to atlas coordinates gives precisely Pa, so its ellipticity transfers back.
    apply (Pn.isElliptic_toAtlas_iff).mp
    have heq : Pn.toAtlasPseudodifferentialOperator = Pa := by
      have hext (Q R : AtlasPseudodifferentialOperator B₀ B₁ m)
          (h : Q.toLinearMap = R.toLinearMap) : Q = R := by
        cases Q with
        | mk Q hQ =>
          cases R with
          | mk R hR =>
            change Q = R at h
            subst R
            rfl
      exact hext _ _ hmap
    rw [heq]
    exact hePa

end AtiyahSinger

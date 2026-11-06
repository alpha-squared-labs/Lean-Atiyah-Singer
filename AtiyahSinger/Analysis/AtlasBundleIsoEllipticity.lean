/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoPseudodifferential
public import AtiyahSinger.Analysis.NativeAtlasFullEllipticity
public import AtiyahSinger.Analysis.OpenFullSymbolEllipticity

/-!
# Full ellipticity under the specified smooth bundle isomorphisms

Public module ID: M0227.

Use the actual input and output isomorphisms in every original frame. Compact
bounds on their inverse-symbol factors preserve the full inverse estimate at
arbitrary real order. Locality supplies the finite compact cover; no global
frame or rank equality is imposed. Source: change of bundle in SG III.3--4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F E' F' : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
  [TopologicalSpace (TotalSpace Unit E')]
  [∀ x, AddCommGroup (F' x)] [∀ x, Module ℂ (F' x)]
  [TopologicalSpace (TotalSpace Unit F')]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {A' : SmoothComplexBundleAtlas (n := n) E'}
  {B' : SmoothComplexBundleAtlas (n := n) F'}

set_option maxSynthPendingDepth 30 in
/-- Conjugating the original full symbol by smooth bundle isomorphisms preserves ellipticity. -/
theorem IsEllipticFullAtlasSymbol.bundleIso {m : ℝ}
    (e : Iso E E') (f : Iso F F')
    (he : IsSmoothAtlasBundleMap A A' e.toHom.linearMap)
    (hfi : IsSmoothAtlasBundleMap B' B f.symm.toHom.linearMap)
    {a : AtlasSymbolFunction (n := n) E F}
    (ha : IsEllipticFullAtlasSymbol A B m a) :
    IsEllipticFullAtlasSymbol A' B' m
      (fun x ξ ↦ (f.toHom.linearMap x).comp
        ((a x ξ).comp (e.symm.toHom.linearMap x))) := by
  classical
  obtain ⟨hu, _, _, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap A A' e.toHom.linearMap he
  obtain ⟨hv, _, _, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap B' B f.symm.toHom.linearMap hfi
  intro c hc i' j'
  apply IsEllipticFullSymbol.of_locally
  intro z hz
  obtain ⟨i, hi⟩ := A.covers (c.symm z)
  obtain ⟨j, hj⟩ := B.covers (c.symm z)
  let Z := atlasSymbolChartDomain A' B' c i' j' ∩
    c.symm ⁻¹' ((A.chart i).baseSet ∩ (B.chart j).baseSet)
  have hZ : IsOpen Z := by
    simpa only [Z, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.isOpen_inter_preimage_symm (((A'.chart i').open_baseSet.inter
        (B'.chart j').open_baseSet).inter
          ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet))
  refine ⟨Z, hZ, ⟨hz, hi, hj⟩, Set.inter_subset_left, ?_⟩
  intro K hKZ hK
  -- Smoothness is used only for the two actual factors of the inverse symbol.
  let U := fun y ↦ atlasGlobalSymbolInChart A A'
    (fun x _ ↦ e.toHom.linearMap x) c i i' y 0
  let V := fun y ↦ atlasGlobalSymbolInChart B' B
    (fun x _ ↦ f.symm.toHom.linearMap x) c j' j y 0
  have hU : ContinuousOn U K := (hu c hc i i').1.continuousOn.comp
    (continuous_id.prodMk (continuous_const (y := (0 : EuclideanSpace ℝ (Fin n))))).continuousOn
      (fun y hy ↦ ⟨⟨⟨(hKZ hy).1.1.1, (hKZ hy).2.1⟩, (hKZ hy).1.1.2⟩, Set.mem_univ _⟩)
  have hV : ContinuousOn V K := (hv c hc j' j).1.continuousOn.comp
    (continuous_id.prodMk (continuous_const (y := (0 : EuclideanSpace ℝ (Fin n))))).continuousOn
      (fun y hy ↦ ⟨⟨⟨(hKZ hy).1.1.1, (hKZ hy).1.2⟩, (hKZ hy).2.2⟩, Set.mem_univ _⟩)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hU
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hV
  obtain ⟨R, C, hR, hC, hbound⟩ := ha c hc i j K
    (fun y hy ↦ ⟨⟨(hKZ hy).1.1.1, (hKZ hy).2.1⟩, (hKZ hy).2.2⟩) hK
  refine ⟨R, max D 0 * C * max L 0, hR, by positivity, ?_⟩
  intro y hy ξ hξ
  have hyA := (hKZ hy).2.1
  have hyB := (hKZ hy).2.2
  have hyA' := (hKZ hy).1.1.2
  have hyB' := (hKZ hy).1.2
  let a₀ := (A.frameLinearEquiv i (c.symm y) hyA).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let a₁ := (A'.frameLinearEquiv i' (c.symm y) hyA').trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let b₀ := (B.frameLinearEquiv j (c.symm y) hyB).trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let b₁ := (B'.frameLinearEquiv j' (c.symm y) hyB').trans
    (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
  let u := ((a₀.symm.trans (e.linearEquiv (c.symm y))).trans a₁).toContinuousLinearEquiv
  let v := ((b₀.symm.trans (f.linearEquiv (c.symm y))).trans b₁).toContinuousLinearEquiv
  let p := atlasGlobalSymbolInChart A B a c i j y ξ
  have hUeq : u.toContinuousLinearMap = U y := by
    apply ContinuousLinearMap.ext
    intro w
    dsimp only [U, atlasGlobalSymbolInChart]
    rw [dite_eq_left ⟨hyA, hyA'⟩]
    rfl
  have hVeq : v.symm.toContinuousLinearMap = V y := by
    apply ContinuousLinearMap.ext
    intro w
    dsimp only [V, atlasGlobalSymbolInChart]
    rw [dite_eq_left ⟨hyB', hyB⟩]
    rfl
  -- The same original fiber maps form the conjugate in these four specified frames.
  have hformula : atlasGlobalSymbolInChart A' B'
      (fun x η ↦ (f.toHom.linearMap x).comp
        ((a x η).comp (e.symm.toHom.linearMap x))) c i' j' y ξ =
      v.toContinuousLinearMap.comp (p.comp u.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro w
    dsimp only [atlasGlobalSymbolInChart, p]
    rw [dite_eq_left ⟨hyA', hyB'⟩, dite_eq_left ⟨hyA, hyB⟩]
    change b₁ (f.linearEquiv (c.symm y)
      (a _ _ ((e.linearEquiv (c.symm y)).symm (a₁.symm w)))) =
      b₁ (f.linearEquiv (c.symm y)
        (b₀.symm (b₀ (a _ _ (a₀.symm (a₀
          ((e.linearEquiv (c.symm y)).symm (a₁.symm w))))))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  obtain ⟨hp, hpnorm⟩ := hbound y hy ξ hξ
  have huinv : u.symm.toContinuousLinearMap.IsInvertible := ⟨u.symm, rfl⟩
  have hvinv : v.toContinuousLinearMap.IsInvertible := ⟨v, rfl⟩
  rw [hformula]
  refine ⟨hvinv.comp (hp.comp huinv), ?_⟩
  rw [hvinv.inverse_comp_of_left, hp.inverse_comp_of_left,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.inverse_equiv]
  change ‖(u.toContinuousLinearMap.comp p.inverse).comp v.symm.toContinuousLinearMap‖ ≤ _
  rw [hUeq, hVeq]
  -- Multiply compact frame bounds with the original order-minus-m inverse estimate.
  calc
    ‖((U y).comp p.inverse).comp (V y)‖ ≤
        (‖U y‖ * ‖p.inverse‖) * ‖V y‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (max D 0 * (C * (1 + ‖ξ‖) ^ (-m))) * max L 0 :=
      mul_le_mul
        (mul_le_mul ((hD y hy).trans (le_max_left _ _)) hpnorm (norm_nonneg _) (by positivity))
        ((hL y hy).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = (max D 0 * C * max L 0) * (1 + ‖ξ‖) ^ (-m) := by ring

set_option maxSynthPendingDepth 30 in
/-- The specified smooth bundle conjugate is elliptic at the same real order. -/
theorem AtlasPseudodifferentialOperator.exists_elliptic_bundleIso_conjugate {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m) (hP : P.IsElliptic)
    (e : Iso E E') (f : Iso F F')
    (he : IsSmoothAtlasBundleMap A A' e.toHom.linearMap)
    (hei : IsSmoothAtlasBundleMap A' A e.symm.toHom.linearMap)
    (hf : IsSmoothAtlasBundleMap B B' f.toHom.linearMap)
    (hfi : IsSmoothAtlasBundleMap B' B f.symm.toHom.linearMap) :
    ∃ Q : AtlasPseudodifferentialOperator A' B' m,
      Q.toLinearMap = (atlasSmoothSectionEquiv B B' f hf hfi).toLinearMap.comp
        (P.toLinearMap.comp (atlasSmoothSectionEquiv A A' e he hei).symm.toLinearMap) ∧
      Q.IsElliptic := by
  obtain ⟨p, hp, hep⟩ := hP
  obtain ⟨hq, Q, hQ, hsymbol, _⟩ := P.exists_bundleIso_conjugate e f he hei hf hfi p hp
  exact ⟨Q, hQ, ⟨_, hsymbol, hep.bundleIso e f he hfi⟩⟩

end AtiyahSinger

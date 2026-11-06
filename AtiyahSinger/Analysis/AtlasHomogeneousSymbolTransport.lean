/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleMapPseudodifferential
public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Analysis.AtlasSymbolComposition

/-!
# Smooth composition and bundle transport of atlas homogeneous symbols

Public module ID: M0252.

Composition uses the same intermediate fiber in a local frame, so smoothness
off the zero section survives even when the atlas ranks vary between components.
Smooth bundle isomorphisms therefore conjugate the actual homogeneous symbols.
The exact boundary square identifies their original compact-support K classes;
no new representative or fixed-rank assumption enters this comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F G H : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]
  [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {C : SmoothComplexBundleAtlas (n := n) G}
  {D : SmoothComplexBundleAtlas (n := n) H}

/-- Composition of the original fiber maps preserves punctured-symbol smoothness. -/
theorem IsSmoothOffZeroAtlasSymbol.atlasSymbolComp
    {a : AtlasSymbolFunction (n := n) E F} {b : AtlasSymbolFunction (n := n) F G}
    (hb : IsSmoothOffZeroAtlasSymbol B C b) (ha : IsSmoothOffZeroAtlasSymbol A B a) :
    IsSmoothOffZeroAtlasSymbol A C (atlasSymbolComp b a) := by
  classical
  intro c hc i k z hz
  -- Choose one middle frame near the current point, preserving its actual rank.
  obtain ⟨j, hj⟩ := B.covers (c.symm z.1)
  let U := atlasSymbolChartDomain A B c i j ∩ atlasSymbolChartDomain B C c j k
  have hleft : IsOpen (atlasSymbolChartDomain A B c i j) := by
    simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.continuousOn_symm.isOpen_inter_preimage c.open_target
        ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
  have hright : IsOpen (atlasSymbolChartDomain B C c j k) := by
    simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.continuousOn_symm.isOpen_inter_preimage c.open_target
        ((B.chart j).open_baseSet.inter (C.chart k).open_baseSet)
  have hU : IsOpen U := hleft.inter hright
  have hzU : z.1 ∈ U := ⟨⟨⟨hz.1.1.1, hz.1.1.2⟩, hj⟩,
    ⟨⟨hz.1.1.1, hj⟩, hz.1.2⟩⟩
  have ha' : ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart A B a c i j))
      (U ×ˢ {ξ | ξ ≠ 0}) :=
    (ha c hc i j).mono (Set.prod_mono Set.inter_subset_left subset_rfl)
  have hb' : ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart B C b c j k))
      (U ×ˢ {ξ | ξ ≠ 0}) :=
    (hb c hc j k).mono (Set.prod_mono Set.inter_subset_right subset_rfl)
  let L := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin (A.rank i)))
    (EuclideanSpace ℂ (Fin (B.rank j)))
    (EuclideanSpace ℂ (Fin (C.rank k)))).bilinearRestrictScalars ℝ
  have hs : ContDiffOn ℝ ∞
      (fun p ↦ (atlasGlobalSymbolInChart B C b c j k p.1 p.2).comp
        (atlasGlobalSymbolInChart A B a c i j p.1 p.2)) (U ×ˢ {ξ | ξ ≠ 0}) :=
    L.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hb' ha'
  -- The forward and inverse middle-frame maps cancel on the same fiber.
  have heq : ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart A C (AtiyahSinger.atlasSymbolComp b a) c i k))
      (U ×ˢ {ξ | ξ ≠ 0}) := hs.congr (by
    intro x hx
    have hA : c.symm x.1 ∈ (A.chart i).baseSet := hx.1.1.1.2
    have hB : c.symm x.1 ∈ (B.chart j).baseSet := hx.1.1.2
    have hC : c.symm x.1 ∈ (C.chart k).baseSet := hx.1.2.2
    ext v
    simp [Function.uncurry, atlasGlobalSymbolInChart, AtiyahSinger.atlasSymbolComp,
      hA, hB, hC, EuclideanSpace.equiv, PiLp.continuousLinearEquiv])
  exact (heq.contDiffAt ((hU.prod isOpen_ne).mem_nhds ⟨hzU, hz.2⟩)).contDiffWithinAt

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

set_option maxSynthPendingDepth 30 in
/-- The specified smooth bundle square conjugates every homogeneous elliptic atlas symbol. -/
theorem exists_atlasHomogeneousSymbol_of_bundleIso {m : ℝ}
    (e : Iso E G) (f : Iso F H)
    (hei : IsSmoothAtlasBundleMap C A e.symm.toHom.linearMap)
    (hf : IsSmoothAtlasBundleMap B D f.toHom.linearMap)
    (a : AtlasSymbolFunction (n := n) E F)
    (ha : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
    (hi : IsEllipticAtlasSymbol a) :
    ∃ b : AtlasSymbolFunction (n := n) G H,
      IsSmoothOffZeroAtlasSymbol C D b ∧ IsHomogeneousAtlasSymbol m b ∧
      IsEllipticAtlasSymbol b ∧
      ∀ (x : M) (ξ : CotangentFiber (n := n) x) (v : G x),
        b x ξ v = f.linearEquiv x (a x ξ ((e.linearEquiv x).symm v)) := by
  -- Multiplication symbols give the same smooth fiber maps, without choosing new frames.
  obtain ⟨hu, _, _, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap C A e.symm.toHom.linearMap hei
  obtain ⟨hv, _, _, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap B D f.toHom.linearMap hf
  have hu' : IsSmoothOffZeroAtlasSymbol C A (fun x _ ↦ e.symm.toHom.linearMap x) := by
    intro c hc i j
    exact (hu c hc i j).1.mono (Set.prod_mono subset_rfl (Set.subset_univ _))
  have hv' : IsSmoothOffZeroAtlasSymbol B D (fun x _ ↦ f.toHom.linearMap x) := by
    intro c hc i j
    exact (hv c hc i j).1.mono (Set.prod_mono subset_rfl (Set.subset_univ _))
  let b : AtlasSymbolFunction (n := n) G H := fun x ξ ↦
    (f.toHom.linearMap x).comp ((a x ξ).comp (e.symm.toHom.linearMap x))
  refine ⟨b, hv'.atlasSymbolComp (ha.atlasSymbolComp hu'), ?_, ?_, fun _ _ _ ↦ rfl⟩
  · intro x ξ hξ t ht
    ext v
    change f.linearEquiv x (a x (t • ξ) ((e.linearEquiv x).symm v)) = _
    rw [hh x ξ hξ t ht]
    exact (f.linearEquiv x).map_smul _ _
  · intro x ξ hξ
    exact (f.linearEquiv x).bijective.comp ((hi x ξ hξ).comp (e.linearEquiv x).symm.bijective)

attribute [local instance] isFiniteRank_pullback t2Space_cotangent locallyCompactSpace_cotangent

omit [SecondCountableTopology M] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original boundary square preserves the compact-support class across arbitrary atlases. -/
theorem atlasSymbolKClass_eq_of_bundleIso (e : Iso E G) (f : Iso F H)
    (a : AtlasSymbolFunction (n := n) E F) (b : AtlasSymbolFunction (n := n) G H)
    (ha : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a)
    (hb : IsSmoothOffZeroAtlasSymbol C D b) (hj : IsEllipticAtlasSymbol b)
    (hab : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → ∀ v : E x,
      f.linearEquiv x (a x ξ v) = b x ξ (e.linearEquiv x v)) :
    atlasSymbolKClass A B a ha hi = atlasSymbolKClass C D b hb hj := by
  let := A.isFiniteRank
  let := B.isFiniteRank
  let := C.isFiniteRank
  let := D.isFiniteRank
  let πM := cotangentProjection (n := n) (M := M)
  let s := atlasEllipticSymbolTriple A B a ha hi
  let t := atlasEllipticSymbolTriple C D b hb hj
  -- Pull back the two actual bundle isomorphisms and compare every original boundary vector.
  have hst : s.congr (e.pullback πM) (f.pullback πM) = t := by
    change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
      CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change G z.val.proj at v
    change f.linearEquiv z.val.proj (a z.val.proj z.val.snd
      ((e.linearEquiv z.val.proj).symm v)) = b z.val.proj z.val.snd v
    rw [hab z.val.proj z.val.snd z.property, LinearEquiv.apply_symm_apply]
  change s.compactSupportClass = t.compactSupportClass
  rw [← hst]
  exact (s.compactSupportClass_congr (e.pullback πM) (f.pullback πM)).symm

end AtiyahSinger

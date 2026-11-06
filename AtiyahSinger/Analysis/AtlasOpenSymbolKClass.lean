/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Analysis.AtlasOpenSymbols
public import AtiyahSinger.Geometry.OpenCotangent

/-!
# The actual atlas symbol class under clopen restriction

Public module ID: M0271.

The canonical reassociation of the original pullback bundles preserves every
fiber vector. The cotangent inclusion preserves the zero covectors and is
proper on a clopen piece. Its pullback therefore gives the original restricted
boundary triple and the same compact-support K class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M] [T2Space M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

attribute [local instance] isFiniteRank_pullback t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

/-- The original restricted symbol realizes the proper cotangent pullback of its K class. -/
theorem atlasSymbolKClass_restrictOpen (U : Opens M) [CompactSpace U]
    (hclosed : IsClosed (U : Set M)) (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a) :
    atlasSymbolKClass (A.restrictOpen U) (B.restrictOpen U) (fun x ξ ↦ a x.val ξ)
        (hs.restrictOpen A B U) (fun x ξ ↦ hi x.val ξ) =
      compactSupportKZeroPullback
        ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
        (isProperMap_cotangentOpenInclusion U hclosed) (atlasSymbolKClass A B a hs hi) := by
  let := A.isFiniteRank
  let := B.isFiniteRank
  let := (A.restrictOpen U).isFiniteRank
  let := (B.restrictOpen U).isFiniteRank
  let f := ContinuousMap.subtypeVal (U : Set M)
  let Φ : C(CotangentTotalSpace (n := n) (M := U),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  let πM := cotangentProjection (n := n) (M := M)
  let πU := cotangentProjection (n := n) (M := U)
  let e := (pullbackCompIso (E := E) πM Φ).trans (pullbackCompIso (E := E) f πU).symm
  let g := (pullbackCompIso (E := F) πM Φ).trans (pullbackCompIso (E := F) f πU).symm
  have he (z : CotangentTotalSpace (n := n) (M := U)) (v : E z.proj.val) :
      e.linearEquiv z v = v := by
    apply ((pullbackCompIso (E := E) f πU).linearEquiv z).injective
    change (pullbackCompIso (E := E) f πU).linearEquiv z
      (((pullbackCompIso (E := E) f πU).linearEquiv z).symm
        ((pullbackCompIso (E := E) πM Φ).linearEquiv z v)) = _
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hg (z : CotangentTotalSpace (n := n) (M := U)) (v : F z.proj.val) :
      g.linearEquiv z v = v := by
    apply ((pullbackCompIso (E := F) f πU).linearEquiv z).injective
    change (pullbackCompIso (E := F) f πU).linearEquiv z
      (((pullbackCompIso (E := F) f πU).linearEquiv z).symm
        ((pullbackCompIso (E := F) πM Φ).linearEquiv z v)) = _
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  let s := atlasEllipticSymbolTriple A B a hs hi
  let t := atlasEllipticSymbolTriple (A.restrictOpen U) (B.restrictOpen U)
    (fun x ξ ↦ a x.val ξ) (hs.restrictOpen A B U) (fun x ξ ↦ hi x.val ξ)
  let hp := isProperMap_cotangentOpenInclusion (n := n) U hclosed
  let r := (s.pullback Φ hp).congr e g
  -- The same covector identifies the controls, and the actual square identifies the boundary maps.
  have hrt : r = t := by
    change CompactSupportTriple.mk cotangentZeroSet _ _ =
      CompactSupportTriple.mk cotangentZeroSet _ _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change E z.val.proj.val at v
    change g.linearEquiv z.val
      ((s.boundary.pullback Φ).linearEquiv z ((e.linearEquiv z.val).symm v)) =
        a z.val.proj.val z.val.snd v
    rw [hg]
    have hev : (e.linearEquiv z.val).symm v = v :=
      (he z.val _).symm.trans ((e.linearEquiv z.val).apply_symm_apply v)
    rw [hev, RelativeTriple.pullback_apply]
    rfl
  change t.compactSupportClass = compactSupportKZeroPullback Φ hp s.compactSupportClass
  rw [← hrt]
  exact ((s.pullback Φ hp).compactSupportClass_congr e g).trans
    (s.compactSupportClass_pullback Φ hp)

end AtiyahSinger

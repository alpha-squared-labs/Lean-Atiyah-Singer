/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolKClass
public import AtiyahSinger.Analysis.AtlasOpenSymbolKClass

/-!
# The original general atlas symbol class under clopen restriction

Public module ID: M2302.

Full-symbol ellipticity restricts in the inherited base charts and the supplied original
frames. On a clopen submanifold, the proper cotangent inclusion pulls back the original
compact-support triple. Canonical pullback reassociation preserves each original fiber
vector and identifies its boundary map with the exact restricted full symbol.

Sources: SG I.9.26 and III.13 (13.1). The explicit finite-component and atlas transport
is a project supplement. No homogeneous symbol or replacement operator is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- The original full-symbol ellipticity restricts to the inherited open-manifold atlas. -/
theorem IsEllipticFullAtlasSymbol.restrictOpen {m : ℝ} {a : AtlasSymbolFunction (n := n) E F}
    (ha : IsEllipticFullAtlasSymbol A B m a) (U : Opens M) :
    IsEllipticFullAtlasSymbol (A.restrictOpen U) (B.restrictOpen U) m
      (fun x ξ ↦ a x.val ξ) := by
  /- Each inherited chart is the restriction of the original chart at the same base point.
  The given atlas frames have identical coordinate matrices there, so the original
  compact-local inverse bound applies to every compact subset of the restricted domain. -/
  intro c hc i j
  have hU : Nonempty U := by
    rcases hc with ⟨_, ⟨x, _⟩, _⟩
    exact ⟨x⟩
  obtain ⟨x, rfl⟩ := Opens.chart_eq hU hc
  let d := chartAt (EuclideanSpace ℝ (Fin n)) x.val
  let D := atlasSymbolChartDomain (A.restrictOpen U) (B.restrictOpen U)
    (d.subtypeRestr hU) i j
  intro K hKD hK
  obtain ⟨R, C, hR, hC, hbound⟩ := ha d (chart_mem_atlas _ x.val) i j K
    (hKD.trans (atlasSymbolChartDomain_restrictOpen_subset A B U hU d i j)) hK
  refine ⟨R, C, hR, hC, ?_⟩
  intro z hz η hη
  rw [atlasGlobalSymbolInChart_restrictOpen A B U hU d (chart_mem_atlas _ x.val)
    a i j z (hKD hz) η]
  exact hbound z hz η hη

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The four nested original pullback topologies use the existing clopen-comparison budget.
/-- Clopen restriction preserves the genuine class of the exact original full atlas symbol. -/
theorem atlasFullSymbolKClass_restrictOpen {m : ℝ} (U : Opens M) [CompactSpace U]
    (hclosed : IsClosed (U : Set M)) (a : atlasGlobalSymbolSpace A B m)
    (ha : IsEllipticFullAtlasSymbol A B m a.val) :
    atlasFullSymbolKClass (A.restrictOpen U) (B.restrictOpen U)
        ⟨fun x ξ ↦ a.val x.val ξ, a.property.restrictOpen A B U⟩ (ha.restrictOpen A B U) =
      compactSupportKZeroPullback
        ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
        (isProperMap_cotangentOpenInclusion U hclosed) (atlasFullSymbolKClass A B a ha) := by
  /- Pull back the original actual triple along the proper cotangent inclusion.
  Its canonical source and target reassociation maps preserve the original vectors.
  On this same compact control the boundary is exactly the restricted full symbol.
  Independence of compact control and the existing proper-pullback class theorem
  give the asserted equality in the original compact-support K group. -/
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
  let aU : atlasGlobalSymbolSpace (A.restrictOpen U) (B.restrictOpen U) m :=
    ⟨fun x ξ ↦ a.val x.val ξ, a.property.restrictOpen A B U⟩
  let haU := ha.restrictOpen A B U
  let s := atlasFullSymbolTriple A B a ha
  let hp := isProperMap_cotangentOpenInclusion (n := n) U hclosed
  let r := (s.pullback Φ hp).congr e g
  have hvalue (z : ↥(r.controlᶜ)) (v : E z.val.proj.val) :
      r.boundary.linearEquiv z v = aU.val z.val.proj z.val.snd v := by
    change g.linearEquiv z.val
      ((s.boundary.pullback Φ).linearEquiv z ((e.linearEquiv z.val).symm v)) =
        a.val z.val.proj.val z.val.snd v
    rw [hg]
    have hev : (e.linearEquiv z.val).symm v = v :=
      (he z.val _).symm.trans ((e.linearEquiv z.val).apply_symm_apply v)
    rw [hev, RelativeTriple.pullback_apply]
    rfl
  have hi : ∀ z : CotangentTotalSpace (n := n) (M := U),
      z ∉ r.control → Function.Bijective (aU.val z.proj z.snd) := by
    intro z hz
    have hmap : ⇑(r.boundary.linearEquiv ⟨z, hz⟩) = ⇑(aU.val z.proj z.snd) :=
      funext (fun v ↦ hvalue ⟨z, hz⟩ v)
    rw [← hmap]
    exact (r.boundary.linearEquiv ⟨z, hz⟩).bijective
  let t := atlasFullSymbolTripleWithControl (A.restrictOpen U) (B.restrictOpen U)
    aU r.control r.isCompact_control hi
  have htr : t = r := by
    change CompactSupportTriple.mk r.control r.isCompact_control _ =
      CompactSupportTriple.mk r.control r.isCompact_control _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    exact (hvalue z v).symm
  change atlasFullSymbolKClass (A.restrictOpen U) (B.restrictOpen U) aU haU =
    compactSupportKZeroPullback Φ hp s.compactSupportClass
  calc
    _ = t.compactSupportClass :=
      atlasFullSymbolKClass_eq_tripleWithControl (A.restrictOpen U) (B.restrictOpen U)
        aU haU r.control r.isCompact_control hi
    _ = r.compactSupportClass := congrArg CompactSupportTriple.compactSupportClass htr
    _ = (s.pullback Φ hp).compactSupportClass :=
      (s.pullback Φ hp).compactSupportClass_congr e g
    _ = compactSupportKZeroPullback Φ hp s.compactSupportClass :=
      s.compactSupportClass_pullback Φ hp

end AtiyahSinger

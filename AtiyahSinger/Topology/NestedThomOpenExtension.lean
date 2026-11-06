/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ThomDirectSum
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.ThomOpenExtension

/-!
# Nested open extensions of the supported Thom operator

Public module ID: M1962.

Given two open embeddings of bundle total spaces and an isomorphism comparing the second
bundle over the first tube with its pullback from the first base, the ordered
sum bundle has an actual nested open embedding. Its Thom-to-open-extension
operator is the composite of the two original operators.

The map retains the supplied bundle comparison and both open maps. The proof
uses the supported direct-sum, bundle-isomorphism and open-extension laws with
these same witnesses. No compact-support class is pulled back along a bundle
projection. Tubular normalization and comparison with a specified composite
embedding require separate geometric comparisons.

Source: the supported Thom transitivity argument in Karoubi IV.5.19--5.22,
expressed through the already proved supported operators on original bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle Topology

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [T2Space X] [T2Space Y] [T2Space Z]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Z]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {G : Y → Type*} [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
  [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A specified nested tube realizes the composite of the original supported Thom extensions. -/
theorem exists_nestedThom_openEmbedding
    (hE : ContinuousHermitianMetric E) (hG : ContinuousHermitianMetric G)
    (j : C(X, Y)) (τE : C(TotalSpace Unit E, Y)) (hτE : IsOpenEmbedding τE)
    (τG : C(TotalSpace Unit G, Z)) (hτG : IsOpenEmbedding τG)
    (e : Iso ((π Unit E) *ᵖ ((j : X → Y) *ᵖ G))
      ((τE : TotalSpace Unit E → Y) *ᵖ G)) :
    ∃ N : C(TotalSpace Unit (E ×ᵇ ((j : X → Y) *ᵖ G)), Z),
      ∃ hN : IsOpenEmbedding N,
        (∀ z, N z = τG ⟨τE ⟨z.proj, z.snd.1⟩,
          e.linearEquiv ⟨z.proj, z.snd.1⟩ z.snd.2⟩) ∧
        (compactSupportKZeroOpenPushforward N hN).comp
            (hE.sum (hG.pullback j)).supportedThomHom =
          ((compactSupportKZeroOpenPushforward τG hτG).comp hG.supportedThomHom).comp
            ((compactSupportKZeroOpenPushforward τE hτE).comp hE.supportedThomHom) := by
  let q : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank ((j : X → Y) *ᵖ G) := isFiniteRank_pullback (E := G) j
  let : IsFiniteRank ((π Unit E) *ᵖ ((j : X → Y) *ᵖ G)) :=
    isFiniteRank_pullback (E := (j : X → Y) *ᵖ G) q
  let a := sumTotalPullbackHomeomorph (E := E) (F := (j : X → Y) *ᵖ G)
  let b := e.totalHomeomorph
  let c := pullbackTotalMap G τE
  let hc := (pullbackTotalMap_properties G τE).2 hτE
  let N := τG.comp (c.comp
    ((⟨b, b.continuous⟩ : C(_, _)).comp ⟨a, a.continuous⟩))
  have hN : IsOpenEmbedding N :=
    hτG.comp (hc.comp (b.isOpenEmbedding.comp a.isOpenEmbedding))
  refine ⟨N, hN, fun _ ↦ rfl, ?_⟩
  -- Compose precisely the reassociation, comparison, pullback lift and second tube.
  have hpush : compactSupportKZeroOpenPushforward N hN =
      (compactSupportKZeroOpenPushforward τG hτG).comp
        ((compactSupportKZeroOpenPushforward c hc).comp
          ((compactSupportKZeroHomeomorph b).comp (compactSupportKZeroHomeomorph a))) := by
    have h₁ := compactSupportKZeroOpenPushforward_comp a a.isOpenEmbedding b b.isOpenEmbedding
    have h₂ := compactSupportKZeroOpenPushforward_comp (b ∘ a)
      (b.isOpenEmbedding.comp a.isOpenEmbedding) c hc
    have h₃ := compactSupportKZeroOpenPushforward_comp (c ∘ (b ∘ a))
      (hc.comp (b.isOpenEmbedding.comp a.isOpenEmbedding)) τG hτG
    rw [compactSupportKZeroOpenPushforward_homeomorph,
      compactSupportKZeroOpenPushforward_homeomorph] at h₁
    rw [h₁] at h₂
    rw [h₂] at h₃
    exact h₃
  have hsum := hE.supportedThomHom_sum (hG.pullback j)
  have hiso := ((hG.pullback j).pullback q).supportedThomHom_iso (hG.pullback τE) e
  have hopen := hG.supportedThomHom_openPushforward τE hτE
  rw [hpush]
  apply DFunLike.ext
  intro u
  -- The three supported identities preserve the original order and the same class u.
  change (compactSupportKZeroOpenPushforward τG hτG)
      ((compactSupportKZeroOpenPushforward c hc)
        ((compactSupportKZeroHomeomorph b)
          ((compactSupportKZeroHomeomorph a) ((hE.sum (hG.pullback j)).supportedThomHom u)))) =
    (compactSupportKZeroOpenPushforward τG hτG)
      (hG.supportedThomHom
        ((compactSupportKZeroOpenPushforward τE hτE) (hE.supportedThomHom u)))
  have hsumu := DFunLike.congr_fun hsum u
  have hisou := DFunLike.congr_fun hiso (hE.supportedThomHom u)
  have hopenu := DFunLike.congr_fun hopen (hE.supportedThomHom u)
  change (compactSupportKZeroHomeomorph a) ((hE.sum (hG.pullback j)).supportedThomHom u) =
    ((hG.pullback j).pullback q).supportedThomHom (hE.supportedThomHom u) at hsumu
  change (compactSupportKZeroHomeomorph b)
      (((hG.pullback j).pullback q).supportedThomHom (hE.supportedThomHom u)) =
    (hG.pullback τE).supportedThomHom (hE.supportedThomHom u) at hisou
  change (compactSupportKZeroOpenPushforward c hc)
      ((hG.pullback τE).supportedThomHom (hE.supportedThomHom u)) =
    hG.supportedThomHom
      ((compactSupportKZeroOpenPushforward τE hτE) (hE.supportedThomHom u)) at hopenu
  rw [hsumu, hisou, hopenu]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

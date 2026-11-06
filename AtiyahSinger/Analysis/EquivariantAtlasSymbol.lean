/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero

/-!
# Equivariant classes of the original atlas symbols

Public module ID: M0469.

The off-zero intertwining equation uses the original inverse-differential
cotangent action and the original two moving-fiber actions. The support datum
is exactly atlasEllipticSymbolTriple, with its entire zero-section control.
Packaging it into the existing equivariant K group does not select another
boundary map, a replacement action, or an unrelated class after forgetting.

Sources: SG III.9 Definition 9.1, III.13 (13.1), (13.5)--(13.7), pp.211,
243--246; the equivariant support-triple presentation of ASI I section 2.
Variable-rank atlas packaging is a project supplement to the same definitions.
No condition is imposed on symbol values at zero. In dimension zero the
empty exterior retains the difference of the original equivariant bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

section OriginalFibers

variable {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- Off-zero intertwining for the original inverse-differential cotangent action. -/
def IsEquivariantAtlasSymbol
    (σE : EquivariantStructure G E) (σF : EquivariantStructure G F)
    (a : AtlasSymbolFunction (n := n) E F) : Prop :=
  ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → ∀ v : E x,
    a (g • x) ((cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
        ⟨x, ξ⟩).snd) (σE.linearMap g x v) =
      σF.linearMap g x (a x ξ v)

variable [CompactSpace M]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- The original atlas symbol triple intertwines the exact pulled-back actions. -/
theorem atlasEllipticSymbolTriple_isEquivariant
    (σE : EquivariantStructure G E) (σF : EquivariantStructure G F)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a)
    (he : IsEquivariantAtlasSymbol IG σE σF a) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    (atlasEllipticSymbolTriple A B a hs hi).IsEquivariant
      (σE.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))
      (σF.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl)) := by
  /- Stage 1: the raw triple has exactly the zero section as its compact
  control. The inverse derivative of a diffeomorphism is a linear
  equivalence, so its dual map preserves and reflects zero. Thus this
  same control, and its complement, are invariant under the native action.
  Stage 2: the raw boundary acts on each exterior vector by the supplied
  a itself. Both actual pullbacks act by the original sigma maps, with
  only the definitional base-projection transport. Therefore their boundary
  intertwining square is precisely he at that same cotangent vector.
  No homogeneity, invariant metric, smooth bundle action, compact group,
  or replacement exterior isomorphism is needed for this packaging. -/
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  -- The same inverse-differential action preserves zero; its group inverse reflects zero.
  have hzero (g : G) (z : CotangentTotalSpace (n := n) (M := M))
      (hz : z.snd = 0) : (g • z).snd = 0 := by
    ext v
    change z.snd _ = 0
    rw [hz]
    rfl
  have hcontrol (g : G) (z : CotangentTotalSpace (n := n) (M := M)) :
      g • z ∈ cotangentZeroSet ↔ z ∈ cotangentZeroSet := by
    change (g • z).snd = 0 ↔ z.snd = 0
    constructor
    · intro hz
      have h : g⁻¹ • (g • z) ∈ cotangentZeroSet := hzero g⁻¹ (g • z) hz
      rw [inv_smul_smul] at h
      exact h
    · exact hzero g z
  refine ⟨hcontrol, ?_⟩
  -- The original pullback actions and boundary forward maps retain each fiber vector.
  intro g z v
  change a (g • z.val.proj) ((cotangentDiffeomorphMap
      (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
      z.val).snd) (σE.linearMap g z.val.proj v) =
    σF.linearMap g z.val.proj (a z.val.proj z.val.snd v)
  exact he g z.val.proj z.val.snd z.property v

end OriginalFibers

attribute [local instance] isFiniteRank_pullback

variable [CompactSpace M] (E F : FiniteBundle M)
  (A : SmoothComplexBundleAtlas (n := n) E.Fiber)
  (B : SmoothComplexBundleAtlas (n := n) F.Fiber)
  (σE : EquivariantStructure G E.Fiber) (σF : EquivariantStructure G F.Fiber)

/-- The actual equivariant zero-control triple of the supplied original atlas symbol. -/
def equivariantAtlasSymbolTriple (a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a)
    (he : IsEquivariantAtlasSymbol IG σE σF a) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportBundleTriple G (CotangentTotalSpace (n := n) (M := M)) :=
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  EquivariantSupportBundleTriple.ofBoundary
    (E.pullback (cotangentProjection (n := n) (M := M)))
    (F.pullback (cotangentProjection (n := n) (M := M)))
    (atlasEllipticSymbolTriple A B a hs hi)
    (σE.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))
    (σF.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))
    (atlasEllipticSymbolTriple_isEquivariant IG A B σE σF a hs hi he)

/-- The class in the original equivariant support group, before forgetting either action. -/
def equivariantAtlasSymbolKClass (a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a)
    (he : IsEquivariantAtlasSymbol IG σE σF a) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) :=
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  (equivariantAtlasSymbolTriple IG E F A B σE σF a hs hi he).kZeroClass

end AtiyahSinger

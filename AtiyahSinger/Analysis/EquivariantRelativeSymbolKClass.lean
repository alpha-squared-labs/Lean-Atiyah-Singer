/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.EquivariantControlledOpenClass

/-!
# Relative controls and the original equivariant homogeneous symbol class

Public module ID: M0566.

The raw relative symbol triple may use only part of the compact zero section
as control. Enlarging to the full zero section compares it with the existing
homogeneous symbol class, retaining the same bundles and actions and the
actual off-zero boundary maps. This also covers dimension zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M] [T2Space M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

omit [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Retain both native cotangent pullbacks while comparing the two original raw boundaries.
/-- A smaller relative zero-section control represents the same equivariant homogeneous class. -/
theorem ComplexBundle.CompactSupportTriple.kZeroClass_eq_equivariantHomogeneousSymbolKClass
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (m : ℝ) (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber m)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (hag : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g a.val x ξ = a.val x ξ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let p := cotangentProjection (n := n) (M := M)
    ∀ (b : CompactSupportTriple ((p : _ → M) *ᵖ E.Fiber) ((p : _ → M) *ᵖ F.Fiber))
      (hb : b.IsEquivariant (σE.pullback p (fun _ _ ↦ rfl))
        (σF.pullback p (fun _ _ ↦ rfl))),
      b.control ⊆ cotangentZeroSet →
      (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
        (v : E.Fiber z.val.proj), b.boundary.linearEquiv z v = a.val z.val.proj z.val.snd v) →
      (EquivariantSupportBundleTriple.ofBoundary
        (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E.Fiber))
        (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F.Fiber)) b
        (σE.pullback p (fun _ _ ↦ rfl)) (σF.pullback p (fun _ _ ↦ rfl)) hb).kZeroClass =
          equivariantHomogeneousSymbolKClass IG σE σF m a ha hag := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  dsimp only
  intro b hb hcontrol hboundary
  let p := cotangentProjection (n := n) (M := M)
  let B := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E.Fiber))
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F.Fiber)) b
    (σE.pullback p (fun _ _ ↦ rfl)) (σF.pullback p (fun _ _ ↦ rfl)) hb
  let A := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E.Fiber))
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F.Fiber))
    (ellipticSymbolTriple a.val a.property.1.continuous ha)
    (σE.pullback p (fun _ _ ↦ rfl)) (σF.pullback p (fun _ _ ↦ rfl))
    (ellipticSymbolTriple_isEquivariant IG σE σF a.val a.property.1.continuous ha hag)
  change B.kZeroClass = A.kZeroClass
  -- The identity fiber maps compare both original triples outside the complete zero section.
  apply equivariantSupportTripleKZero_generator_relations.1 B A
  refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet,
    A.2.isEquivariant.invariant_control, hcontrol, Set.Subset.refl _,
    Iso.refl _, Iso.refl _, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
  intro z v
  change (b.enlarge cotangentZeroSet isCompact_cotangentZeroSet hcontrol).boundary.linearEquiv
      z v =
    (A.1.datum.enlarge cotangentZeroSet isCompact_cotangentZeroSet
      (Set.Subset.refl _)).boundary.linearEquiv z v
  rw [b.enlarge_apply, A.1.datum.enlarge_apply, hboundary]
  exact (ellipticSymbolTriple_boundary_apply a.val a.property.1.continuous ha z v).symm

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Analysis.OperatorSymbolKClass

/-!
# The compact relative control of a homogeneous symbol

Public module ID: M0920.

A symbol equal to a smooth exterior isomorphism has an actual boundary over the
complement of the compact part of the zero section. Enlarging that control
compares it to the ordinary symbol K class without changing the boundary map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Filter Set TopologicalSpace
open scoped ContDiff Manifold Topology

attribute [local instance] isFiniteRank_pullback t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2000000 in
-- The two original pullback reassociations are retained in the actual boundary action.
/-- Exterior bundle isomorphisms sharpen the control of the same homogeneous symbol K class. -/
theorem exists_relativeHomogeneousSymbolTriple {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]
    (E F : SmoothFiniteComplexBundle (n := n) M) (L : Set M) (hL : IsCompact L)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (d : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (hd : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (d x).toLinearMap))
    (haext : ∀ x, x ∉ L → ∀ ξ, a.val x ξ = d x)
    (hdext : ∀ x, x ∉ L → Function.Bijective (d x)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∃ b : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
      b.control = cotangentZeroSection '' L ∧
      (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
        (v : E.Fiber z.val.proj),
        b.boundary.linearEquiv z v = a.val z.val.proj z.val.snd v) ∧
      b.compactSupportClass = homogeneousSymbolKClass 0 a ha := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let X := CotangentTotalSpace (n := n) (M := M)
  let P := cotangentProjection (n := n) (M := M)
  let K : Set X := cotangentZeroSection '' L
  have hK : IsCompact K := hL.image continuous_cotangentZeroSection
  let A (z : X) : TotalSpace
      (EuclideanSpace ℂ (Fin E.rank) →L[ℂ] EuclideanSpace ℂ (Fin F.rank))
      (fun x ↦ E.Fiber x →L[ℂ] F.Fiber x) := ⟨z.proj, a.val z.proj z.snd⟩
  have hAoff : ContinuousOn A cotangentZeroSetᶜ :=
    continuousOn_iff_continuous_domRestrict.mpr a.property.1.continuous
  -- Smoothness of d gives joint Hom-section continuity, including the zero fibers.
  have hdtotal : Continuous (fun x ↦ (⟨x, d x⟩ : TotalSpace
      (EuclideanSpace ℂ (Fin E.rank) →L[ℂ] EuclideanSpace ℂ (Fin F.rank))
      (fun x ↦ E.Fiber x →L[ℂ] F.Fiber x))) := by
    rw [continuous_iff_continuousAt]
    intro x
    let f := trivializationAt (EuclideanSpace ℂ (Fin E.rank)) E.Fiber x
    let g := trivializationAt (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x
    have hx : x ∈ f.baseSet ∩ g.baseSet :=
      ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
    have hmat := (hd.contMDiffOn_matrix (fun x ↦ (d x).toLinearMap) f g).contMDiffAt
      ((f.open_baseSet.inter g.open_baseSet).mem_nhds hx)
    apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
    refine ⟨continuousAt_id, ?_⟩
    exact hmat.continuousAt
  have hzero (z : X) (hz : z ∉ K) (hξ : z.snd = 0) : z.proj ∉ L := by
    intro hzL
    apply hz
    refine ⟨z.proj, hzL, ?_⟩
    cases z with
    | mk x ξ =>
      change ξ = 0 at hξ
      cases hξ
      rfl
  have hA : ContinuousOn A Kᶜ := by
    intro z hz
    by_cases hξ : z.snd = 0
    · have hzL := hzero z hz hξ
      have hlocal := (hdtotal.comp P.continuous).continuousAt (x := z)
      apply (hlocal.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [P.continuous.continuousAt.preimage_mem_nhds
        (hL.isClosed.isOpen_compl.mem_nhds hzL)] with w hw
      change A w = ⟨w.proj, d w.proj⟩
      dsimp only [A]
      rw [haext w.proj hw]
    · apply ContinuousAt.continuousWithinAt
      exact hAoff.continuousAt (isClosed_cotangentZeroSet.isOpen_compl.mem_nhds hξ)
  have hbijective (z : (Kᶜ : Set X)) : Function.Bijective (a.val z.val.proj z.val.snd) := by
    by_cases hξ : z.val.snd = 0
    · rw [haext z.val.proj (hzero z.val z.property hξ)]
      exact hdext z.val.proj (hzero z.val z.property hξ)
    · exact ha z.val.proj z.val.snd hξ
  -- The isomorphism has the original Hom map as its forward action.
  let i : C((Kᶜ : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  let e := modelPullbackIso (EuclideanSpace ℂ (Fin E.rank))
    (EuclideanSpace ℂ (Fin F.rank)) (P.comp i)
    (fun z ↦ a.val z.val.proj z.val.snd)
    (continuousOn_iff_continuous_domRestrict.mp hA) hbijective
  let cE := pullbackCompIso (E := E.Fiber) P i
  let cF := pullbackCompIso (E := F.Fiber) P i
  let b : CompactSupportTriple ((P : X → M) *ᵖ E.Fiber) ((P : X → M) *ᵖ F.Fiber) :=
    { control := K
      isCompact_control := hK
      boundary := cE.trans (e.trans cF.symm) }
  have hb (z : (b.controlᶜ : Set X)) (v : E.Fiber z.val.proj) :
      b.boundary.linearEquiv z v = a.val z.val.proj z.val.snd v := by
    apply (cF.linearEquiv z).injective
    change cF.linearEquiv z ((cF.linearEquiv z).symm
      (e.linearEquiv z (cE.linearEquiv z v))) = _
    rw [LinearEquiv.apply_symm_apply]
    change a.val z.val.proj z.val.snd (cE.linearEquiv z v) =
      cF.linearEquiv z (a.val z.val.proj z.val.snd v)
    rw [pullbackCompIso_apply, pullbackCompIso_apply]
  have hsubset : b.control ⊆ cotangentZeroSet := by
    rintro z ⟨x, _, rfl⟩
    rfl
  -- Enlarging the compact control keeps the same boundary at every nonzero covector.
  have heq : b.enlarge cotangentZeroSet isCompact_cotangentZeroSet hsubset =
      ellipticSymbolTriple a.val a.property.1.continuous ha := by
    change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
      CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    exact (b.enlarge_apply cotangentZeroSet isCompact_cotangentZeroSet hsubset z v).trans
      ((hb ⟨z.val, fun h ↦ z.property (hsubset h)⟩ v).trans
        (ellipticSymbolBoundary_apply a.val a.property.1.continuous ha z v).symm)
  refine ⟨b, rfl, hb, ?_⟩
  change b.compactSupportClass =
    (ellipticSymbolTriple a.val a.property.1.continuous ha).compactSupportClass
  rw [← heq, CompactSupportTriple.compactSupportClass_enlarge]

end AtiyahSinger

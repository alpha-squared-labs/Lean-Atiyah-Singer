/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Analysis.HomogeneousSymbolPullback
public import AtiyahSinger.Topology.EquivariantPullbackTransport
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality

/-!
# Proper equivariant pullback of homogeneous symbol classes

Public module ID: M0526.

The actual cotangent map, the given actions on the native pullback bundles,
and the off-zero symbol square determine the equivariant pullback class.
The total-space compatibility retains the moving-base transports without
assuming that the supplied action was constructed by a particular definition.
This is the equivariant version of the symbol-triple naturality used for
clopen restriction and diffeomorphism transport (SG III.13 and ASI I, Section 2).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N] [CompactSpace N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G N]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent
attribute [local instance 2000] FiberBundle.pullback VectorBundle.pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Reassociate the native modeled pullback bundles while retaining both original actions.
/-- Proper equivariant pullback that preserves and reflects zero covectors preserves
symbol K classes. -/
theorem equivariantHomogeneousSymbolKClass_pullback
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (f : C(N, M))
    (τE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) ((f : N → M) *ᵖ E.Fiber)
      EquivariantStructure G ((f : N → M) *ᵖ E.Fiber))
    (τF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((f : N → M) *ᵖ F.Fiber)
      EquivariantStructure G ((f : N → M) *ᵖ F.Fiber))
    (hE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) ((f : N → M) *ᵖ E.Fiber)
      ∀ g y v, (⟨f (g • y), τE.linearMap g y v⟩ : TotalSpace Unit E.Fiber) =
      ⟨g • f y, σE.linearMap g (f y) v⟩)
    (hF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((f : N → M) *ᵖ F.Fiber)
      ∀ g y v, (⟨f (g • y), τF.linearMap g y v⟩ : TotalSpace Unit F.Fiber) =
      ⟨g • f y, σF.linearMap g (f y) v⟩)
    (d : ∀ y : N, CotangentFiber (n := m) y → CotangentFiber (n := n) (f y))
    (hd : Continuous (fun z : CotangentTotalSpace (n := m) (M := N) ↦
      (⟨f z.proj, d z.proj z.snd⟩ : CotangentTotalSpace (n := n) (M := M))))
    (hp : IsProperMap (fun z : CotangentTotalSpace (n := m) (M := N) ↦
      (⟨f z.proj, d z.proj z.snd⟩ : CotangentTotalSpace (n := n) (M := M))))
    (hzero : ∀ y ξ, d y ξ = 0 ↔ ξ = 0)
    (hΦ : letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      letI := smoothCotangentMulAction (n := m) (G := G) (M := N) IG
      ∀ (g : G) (z : CotangentTotalSpace (n := m) (M := N)),
        (⟨f (g • z).proj, d (g • z).proj (g • z).snd⟩ :
          CotangentTotalSpace (n := n) (M := M)) = g • ⟨f z.proj, d z.proj z.snd⟩)
    (l : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber l)
    (b : homogeneousGlobalSymbolSpace (n := m) (r := E.rank) (q := F.rank)
      ((f : N → M) *ᵖ E.Fiber) ((f : N → M) *ᵖ F.Fiber) l)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (hb : IsEllipticGlobalSymbol ((f : N → M) *ᵖ E.Fiber)
      ((f : N → M) *ᵖ F.Fiber) b.val)
    (hga : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g a.val x ξ = a.val x ξ)
    (hgb : ∀ (g : G) (y : N) (ξ : CotangentFiber (n := m) y), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG τE τF g b.val y ξ = b.val y ξ)
    (hab : ∀ y ξ, ξ ≠ 0 → ∀ v : E.Fiber (f y), b.val y ξ v = a.val (f y) (d y ξ) v) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := m) (G := G) (M := N) IG
    letI := contMDiffSMul_smoothCotangent (n := m) (G := G) (M := N) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
    equivariantHomogeneousSymbolKClass IG τE τF l b hb hgb =
      equivariantSupportTripleKZeroPullback
        ⟨fun z ↦ ⟨f z.proj, d z.proj z.snd⟩, hd⟩ hΦ hp
        (equivariantHomogeneousSymbolKClass IG σE σF l a ha hga) := by
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := m) (G := G) (M := N) IG
  let := contMDiffSMul_smoothCotangent (n := m) (G := G) (M := N) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := m) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
  let Φ : C(CotangentTotalSpace (n := m) (M := N),
      CotangentTotalSpace (n := n) (M := M)) := ⟨fun z ↦ ⟨f z.proj, d z.proj z.snd⟩, hd⟩
  let πM := cotangentProjection (n := n) (M := M)
  let πN := cotangentProjection (n := m) (M := N)
  -- Canonical reassociation keeps each vector and also its native pullback topology.
  have comparison (B : SmoothFiniteComplexBundle (n := n) M) :
      let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
      let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber)
      ∃ e : Iso ((Φ : _ → _) *ᵖ ((πM : _ → M) *ᵖ B.Fiber))
          ((πN : _ → N) *ᵖ ((f : N → M) *ᵖ B.Fiber)),
        ∀ z v, e.linearEquiv z v = v := by
    let tB : TopologicalSpace (TotalSpace Unit B.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
    have htop : modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber) =
        (inferInstance : TopologicalSpace (TotalSpace Unit ((f : N → M) *ᵖ B.Fiber))) := by
      change TopologicalSpace.induced
          (unitTotalEquiv (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber))
          (Pullback.TotalSpace.topologicalSpace (EuclideanSpace ℂ (Fin B.rank)) B.Fiber f) =
        Pullback.TotalSpace.topologicalSpace Unit B.Fiber f
      simp only [Pullback.TotalSpace.topologicalSpace, pullbackTopology_def, tB,
        modelTopology, induced_inf, induced_compose]
      rfl
    let e₀ := (pullbackCompIso (E := B.Fiber) πM Φ).trans
      (pullbackCompIso (E := B.Fiber) f πN).symm
    have he₀ (z : CotangentTotalSpace (n := m) (M := N)) (v : B.Fiber (f z.proj)) :
        e₀.linearEquiv z v = v := by
      apply ((pullbackCompIso (E := B.Fiber) f πN).linearEquiv z).injective
      change (pullbackCompIso (E := B.Fiber) f πN).linearEquiv z
        (((pullbackCompIso (E := B.Fiber) f πN).linearEquiv z).symm
          ((pullbackCompIso (E := B.Fiber) πM Φ).linearEquiv z v)) = _
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    rw [htop]
    exact ⟨e₀, he₀⟩
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) ((f : N → M) *ᵖ E.Fiber)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((f : N → M) *ᵖ F.Fiber)
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) ((f : N → M) *ᵖ E.Fiber)
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) ((f : N → M) *ᵖ F.Fiber)
  obtain ⟨e, he⟩ := comparison E
  obtain ⟨g, hg⟩ := comparison F
  -- Lifting into the original total space proves equivariance of these same comparisons.
  have comparison_equivariant (B : SmoothFiniteComplexBundle (n := n) M)
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
        EquivariantStructure G B.Fiber)
      (τ : letI := modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber)
        EquivariantStructure G ((f : N → M) *ᵖ B.Fiber))
      (hτ : letI := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
        let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber)
        ∀ g y v, (⟨f (g • y), τ.linearMap g y v⟩ : TotalSpace Unit B.Fiber) =
        ⟨g • f y, σ.linearMap g (f y) v⟩) :
      let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
      let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber)
      ∀ (u : Iso ((Φ : _ → _) *ᵖ ((πM : _ → M) *ᵖ B.Fiber))
          ((πN : _ → N) *ᵖ ((f : N → M) *ᵖ B.Fiber))),
        (∀ z v, u.linearEquiv z v = v) →
          u.IsEquivariant ((σ.pullback πM (fun _ _ ↦ rfl)).pullback Φ hΦ)
            (τ.pullback πN (fun _ _ ↦ rfl)) := by
    let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber)
    dsimp only
    intro u hu k z v
    change u.linearEquiv (k • z)
      (((σ.pullback πM (fun _ _ ↦ rfl)).pullback Φ hΦ).linearMap k z v) =
        (τ.pullback πN (fun _ _ ↦ rfl)).linearMap k z (u.linearEquiv z v)
    rw [hu, hu]
    have h := congrArg (Pullback.lift (E := B.Fiber) πM)
      ((σ.pullback πM (fun _ _ ↦ rfl)).pullback_lift_action Φ hΦ k z v)
    exact TotalSpace.mk_injective (f (k • z.proj)) (h.trans (hτ k z.proj v).symm)
  let A := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E.Fiber))
    (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F.Fiber))
    (ellipticSymbolTriple a.val a.property.1.continuous ha)
    (σE.pullback πM (fun _ _ ↦ rfl)) (σF.pullback πM (fun _ _ ↦ rfl))
    (ellipticSymbolTriple_isEquivariant IG σE σF a.val a.property.1.continuous ha hga)
  let B := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((πN : _ → N) *ᵖ ((f : N → M) *ᵖ E.Fiber)))
    (FiniteBundle.ofFamily ((πN : _ → N) *ᵖ ((f : N → M) *ᵖ F.Fiber)))
    (ellipticSymbolTriple b.val b.property.1.continuous hb)
    (τE.pullback πN (fun _ _ ↦ rfl)) (τF.pullback πN (fun _ _ ↦ rfl))
    (ellipticSymbolTriple_isEquivariant IG τE τF b.val b.property.1.continuous hb hgb)
  have hcontrol : (A.pullback Φ hΦ hp).1.datum.control ⊆
      cotangentZeroSet (n := m) (M := N) := by
    intro z hz
    exact (hzero z.proj z.snd).mp hz
  -- The exact off-zero square gives the isomorphism relation with invariant zero control.
  have hIso : (A.pullback Φ hΦ hp).IsIsomorphic B := by
    refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet,
      B.2.isEquivariant.invariant_control, hcontrol, subset_rfl, e, g,
      comparison_equivariant E σE τE hE e he,
      comparison_equivariant F σF τF hF g hg, ?_⟩
    intro z v
    rw [hg, he]
    simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
    let zA : (Φ ⁻¹' A.1.datum.controlᶜ :
        Set (CotangentTotalSpace (n := m) (M := N))) :=
      ⟨z.val, fun h ↦ z.property ((hzero z.val.proj z.val.snd).mp h)⟩
    change (A.1.datum.boundary.pullback Φ).linearEquiv zA v =
      B.1.datum.boundary.linearEquiv z v
    rw [RelativeTriple.pullback_apply]
    change (ellipticSymbolBoundary a.val a.property.1.continuous ha).linearEquiv
      ⟨Φ z.val, zA.property⟩ v =
      (ellipticSymbolBoundary b.val b.property.1.continuous hb).linearEquiv z v
    rw [ellipticSymbolBoundary_apply, ellipticSymbolBoundary_apply]
    exact (hab z.val.proj z.val.snd z.property v).symm
  change B.kZeroClass = equivariantSupportTripleKZeroPullback Φ hΦ hp A.kZeroClass
  rw [equivariantSupportTripleKZeroPullback_apply]
  exact (equivariantSupportTripleKZero_generator_relations.1 _ _ hIso).symm

end AtiyahSinger

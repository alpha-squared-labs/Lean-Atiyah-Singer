/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantBundleSmoothing
public import AtiyahSinger.Geometry.SmoothFiniteRepresentationBundle
public import AtiyahSinger.Topology.EquivariantRelativeCotangentStabilization

/-!
# Native smooth bundles for the same relative stabilization

Public module ID: M1209.

On a compact base in positive dimension, one original equivariant complement
stabilizes both bundles. The source is the
native trivial Euclidean bundle of that same finite representation, while the
target is smoothed through an actual equivariant isomorphism. The resulting
cotangent boundary retains its original compact control and an exact formula
in terms of the original boundary, the same complement, and the selected maps.
These comparisons survive restriction to a common open image in excision.

This combines the complement argument of Karoubi I.9.31 with the relative
representative and smooth bundle constructions used in SG III.13.3--13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial

set_option maxHeartbeats 1400000 in
-- The formula retains the actual sum, native pullback and chosen base isomorphisms.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Smooth the same stabilization with its finite-representation source and exact control. -/
theorem exists_smooth_relative_equivariant_cotangent_stabilization
    (hn : 0 < n) (E F : FiniteBundle M)
    (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber)
    (K : Set M) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ a : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
      a.control = cotangentZeroSection '' K →
      ∀ ha : a.IsEquivariant
          (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
          (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)),
        ∃ (C : FiniteBundle M) (τ : EquivariantStructure G C.Fiber)
          (ρ : FiniteContinuousRepresentation G),
          ∃ hT : IsSmoothComplexBundle (n := n) (r := ρ.dimension)
              (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))),
            letI := hT
            let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
            letI := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
            letI := isFiniteRank_model (EuclideanSpace ℂ (Fin ρ.dimension)) T
            ∃ σT : EquivariantStructure G T,
              σT.IsSmooth (n := n) (r := ρ.dimension) 𝓘(ℝ, VG) ∧
              (∀ (g : G) (x : M) (v : T x), σT.linearMap g x v =
                (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
                  (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v))) ∧
              ∃ F' : SmoothFiniteComplexBundle (n := n) M, F'.rank = ρ.dimension ∧
                letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
                letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
                ∃ σF : EquivariantStructure G F'.Fiber,
                  σF.IsSmooth (n := n) (r := F'.rank) 𝓘(ℝ, VG) ∧
                  ∃ (e : Iso (E.sum C).Fiber T) (f : Iso (F.sum C).Fiber F'.Fiber),
                    e.IsEquivariant (ρE.sum τ) σT ∧ f.IsEquivariant (ρF.sum τ) σF ∧
                    ∃ b : CompactSupportTriple
                        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ T)
                        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F'.Fiber),
                      ∃ hb : b.IsEquivariant
                          (σT.pullback cotangentProjection (fun _ _ ↦ rfl))
                          (σF.pullback cotangentProjection (fun _ _ ↦ rfl)),
                        b.control = a.control ∧
                        (∀ (z : CotangentTotalSpace (n := n) (M := M))
                          (ha' : z ∈ a.controlᶜ) (hb' : z ∈ b.controlᶜ) (v : T z.proj),
                          b.boundary.linearEquiv ⟨z, hb'⟩ v = f.linearEquiv z.proj
                            (a.boundary.linearEquiv ⟨z, ha'⟩
                              (((e.linearEquiv z.proj).symm v).1),
                              ((e.linearEquiv z.proj).symm v).2)) ∧
                        (EquivariantSupportBundleTriple.ofBoundary
                          ((FiniteBundle.ofFamily T).pullback cotangentProjection)
                          ((FiniteBundle.ofFamily F'.Fiber).pullback cotangentProjection) b
                          (σT.pullback cotangentProjection (fun _ _ ↦ rfl))
                          (σF.pullback cotangentProjection (fun _ _ ↦ rfl)) hb).kZeroClass =
                        (EquivariantSupportBundleTriple.ofBoundary
                          (E.pullback cotangentProjection) (F.pullback cotangentProjection) a
                          (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                          (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ha).kZeroClass := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro a haControl ha
  -- Stabilize both sides with one actual complement, retaining the original boundary formula.
  obtain ⟨C, τ, ρ, j, hj, _hErank, hFrank, a₁, ha₁, ha₁Control, ha₁boundary, ha₁class⟩ :=
    exists_relative_equivariant_cotangent_stabilization 𝓘(ℝ, VG) hn E F ρE ρF K
      a haControl ha
  obtain ⟨hT, σT, hσT, eρ, heρ, heρvalue, _hframe⟩ :=
    exists_smooth_finiteRepresentation_bundle (VG := VG) (M := M) (n := n) ρ
  let := hT
  let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
  let := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin ρ.dimension)) T
  obtain ⟨F', hFrank', σF, hσF, f, hf⟩ :=
    (ρF.sum τ).exists_smooth_bundle_iso (VG := VG) (n := n) ρ.dimension hFrank
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let e : Iso (E.sum C).Fiber T := j.trans eρ
  have he : e.IsEquivariant (ρE.sum τ) σT := by
    intro g x v
    exact (congrArg (eρ.linearEquiv (g • x)) (hj g x v)).trans
      (heρ g x (j.linearEquiv x v))
  have hσTvalue (g : G) (x : M) (v : T x) : σT.linearMap g x v =
      (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
        (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)) := by
    have h := heρ g x ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)
    change eρ.linearEquiv (g • x)
        (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)) =
      σT.linearMap g x (eρ.linearEquiv x ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)) at h
    rw [heρvalue, heρvalue, ContinuousLinearEquiv.symm_apply_apply] at h
    exact h.symm
  -- Pull back only the original chosen base isomorphisms; their control is unchanged.
  let p := cotangentProjection (n := n) (M := M)
  let e' := e.pullback p
  let f' := f.pullback p
  let τT := σT.pullback p (fun _ _ ↦ rfl)
  let τF := σF.pullback p (fun _ _ ↦ rfl)
  have he' := ((ρE.sum τ).pullback_maps σT p (fun _ _ ↦ rfl)).2 e he
  have hf' := ((ρF.sum τ).pullback_maps σF p (fun _ _ ↦ rfl)).2 f hf
  let b := a₁.congr e' f'
  have hb : b.IsEquivariant τT τF := by
    refine ⟨ha₁.invariant_control, ?_⟩
    intro g z v
    have hinv : e'.symm.linearEquiv (g • z.val) (τT.linearMap g z.val v) =
        ((ρE.sum τ).pullback p (fun _ _ ↦ rfl)).linearMap g z.val
          (e'.symm.linearEquiv z.val v) := by
      have h := he' g z.val (e'.symm.linearEquiv z.val v)
      change e'.linearEquiv (g • z.val)
        (((ρE.sum τ).pullback p (fun _ _ ↦ rfl)).linearMap g z.val
          ((e'.linearEquiv z.val).symm v)) =
        τT.linearMap g z.val (e'.linearEquiv z.val ((e'.linearEquiv z.val).symm v)) at h
      rw [LinearEquiv.apply_symm_apply] at h
      exact (congrArg (e'.linearEquiv (g • z.val)).symm h).symm.trans
        ((e'.linearEquiv (g • z.val)).symm_apply_apply _)
    let gz : (a₁.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))) :=
      ⟨g • z.val, fun hz ↦ z.property ((ha₁.invariant_control g z.val).mp hz)⟩
    change f'.linearEquiv (g • z.val)
      (a₁.boundary.linearEquiv gz
        (e'.symm.linearEquiv (g • z.val) (τT.linearMap g z.val v))) = _
    rw [hinv]
    exact (congrArg (f'.linearEquiv (g • z.val))
      (ha₁.boundary_intertwines g z _)).trans (hf' g z.val _)
  let A := EquivariantSupportBundleTriple.ofBoundary
    ((E.sum C).pullback p) ((F.sum C).pullback p) a₁
    ((ρE.sum τ).pullback p (fun _ _ ↦ rfl))
    ((ρF.sum τ).pullback p (fun _ _ ↦ rfl)) ha₁
  let B := EquivariantSupportBundleTriple.ofBoundary
    ((FiniteBundle.ofFamily T).pullback p) ((FiniteBundle.ofFamily F'.Fiber).pullback p)
    b τT τF hb
  have hiso : A.IsIsomorphic B := by
    refine ⟨a₁.control, a₁.isCompact_control, ha₁.invariant_control,
      Set.Subset.refl _, Set.Subset.refl _, e', f', he', hf', ?_⟩
    intro z v
    rw [A.1.datum.enlarge_apply a₁.control a₁.isCompact_control (Set.Subset.refl _),
      B.1.datum.enlarge_apply a₁.control a₁.isCompact_control (Set.Subset.refl _)]
    change f'.linearEquiv z (a₁.boundary.linearEquiv z v) =
      f'.linearEquiv z (a₁.boundary.linearEquiv z
        ((e'.linearEquiv z).symm (e'.linearEquiv z v)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨C, τ, ρ, hT, σT, hσT, hσTvalue, F', hFrank', σF, hσF, e, f, he, hf,
    b, hb, ha₁Control, ?_, ?_⟩
  · -- This pointwise equality is available before any ambient K-class comparison.
    intro z ha' hb' v
    change f'.linearEquiv z
      (a₁.boundary.linearEquiv ⟨z, hb'⟩ (e'.symm.linearEquiv z v)) = _
    rw [ha₁boundary z ha' hb' (e'.symm.linearEquiv z v)]
    rfl
  · exact (equivariantSupportTripleKZero_generator_relations.1 A B hiso).symm.trans ha₁class

end AtiyahSinger

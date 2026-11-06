/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundleEmbedding
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero

public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Relative equivariant stabilization on the original cotangent bundles

Public module ID: M1804.

In positive cotangent dimension the original off-zero boundary identifies the
source and target ranks. One actual finite-representation complement therefore
stabilizes both bundles to the same fixed rank. The construction retains the
original compact control and the precise boundary on every exterior covector.
These pointwise comparisons also survive restriction through an open embedding;
no injectivity of compact-support open pushforward is used.

This is the relative form of the standard equivariant complement argument
(Karoubi I.9.31), needed for the arbitrary-source analytic excision construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- The original sum/pullback topologies retain the specified equivariant generator square.
/-- The same complement retains the given control and actual relative boundary. -/
theorem exists_relative_equivariant_cotangent_stabilization (hn : 0 < n)
    (E F : FiniteBundle M)
    (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber)
    (K : Set M) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
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
          ∃ j : Iso (E.sum C).Fiber (Bundle.Trivial M (Fin ρ.dimension → ℂ)),
            j.IsEquivariant (ρE.sum τ) (EquivariantStructure.ofFiniteRepresentation ρ) ∧
            (∀ x, Module.finrank ℂ ((E.sum C).Fiber x) = ρ.dimension) ∧
            (∀ x, Module.finrank ℂ ((F.sum C).Fiber x) = ρ.dimension) ∧
            ∃ b : CompactSupportTriple
                ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ (E.sum C).Fiber)
                ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ (F.sum C).Fiber),
              ∃ hb : b.IsEquivariant
                  ((ρE.sum τ).pullback cotangentProjection (fun _ _ ↦ rfl))
                  ((ρF.sum τ).pullback cotangentProjection (fun _ _ ↦ rfl)),
                b.control = a.control ∧
                (∀ (z : CotangentTotalSpace (n := n) (M := M))
                  (ha' : z ∈ a.controlᶜ) (hb' : z ∈ b.controlᶜ)
                  (v : (E.sum C).Fiber z.proj),
                    b.boundary.linearEquiv ⟨z, hb'⟩ v =
                      (a.boundary.linearEquiv ⟨z, ha'⟩ v.1, v.2)) ∧
                (EquivariantSupportBundleTriple.ofBoundary
                  ((E.sum C).pullback cotangentProjection)
                  ((F.sum C).pullback cotangentProjection) b
                  ((ρE.sum τ).pullback cotangentProjection (fun _ _ ↦ rfl))
                  ((ρF.sum τ).pullback cotangentProjection (fun _ _ ↦ rfl)) hb).kZeroClass =
                    (EquivariantSupportBundleTriple.ofBoundary
                      (E.pullback cotangentProjection) (F.pullback cotangentProjection) a
                      (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                      (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ha).kZeroClass := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro a hControl haEq
  -- A nonzero covector tests equality of the two ranks at each original base point.
  have hrank (x : M) : Module.finrank ℂ (E.Fiber x) = Module.finrank ℂ (F.Fiber x) := by
    let i : Fin n := ⟨0, hn⟩
    let ξ : CotangentFiber (n := n) x := EuclideanSpace.proj i
    have hξ : ξ ≠ 0 := by
      intro h
      have h' := congrArg (fun L : CotangentFiber (n := n) x ↦
        L (EuclideanSpace.single i 1)) h
      change (EuclideanSpace.single i (1 : ℝ)) i = 0 at h'
      simp at h'
    have hz : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := by
      intro hz
      rw [hControl] at hz
      obtain ⟨y, _, hy⟩ := hz
      have hxy : y = x := congrArg (fun z : CotangentTotalSpace ↦ z.proj) hy
      subst y
      exact hξ (TotalSpace.mk_injective x hy).symm
    exact (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hz⟩).finrank_eq
  -- Use one actual representation complement on both sides, never independent stabilizers.
  obtain ⟨C, τ, ρ, j, hj⟩ := ρE.exists_finiteRepresentation_complement
  let P := E.sum C
  let Q := F.sum C
  have hP (x : M) : Module.finrank ℂ (P.Fiber x) = ρ.dimension := by
    exact (j.linearEquiv x).finrank_eq.trans (Module.finrank_fin_fun ℂ)
  have hQ (x : M) : Module.finrank ℂ (Q.Fiber x) = ρ.dimension := by
    let := finite_fiber (E := E.Fiber) x
    let := finite_fiber (E := F.Fiber) x
    let := finite_fiber (E := C.Fiber) x
    change Module.finrank ℂ (F.Fiber x × C.Fiber x) = ρ.dimension
    rw [Module.finrank_prod, ← hrank x, ← Module.finrank_prod]
    exact hP x
  let πM := cotangentProjection (n := n) (M := M)
  -- Pullback and sum carry distinct induced topologies; compare them by the actual identity.
  let compare (J K : FiniteBundle M) :
      Iso ((J.sum K).pullback πM).Fiber ((J.pullback πM).sum (K.pullback πM)).Fiber :=
    { linearEquiv z := LinearEquiv.refl ℂ (J.Fiber (πM z) × K.Fiber (πM z))
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply Continuous.prodMk
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit J.Fiber πM).continuous_iff]
          exact (Pullback.continuous_proj Unit (J.sum K).Fiber πM).prodMk
            (continuous_sum_fst.comp (Pullback.continuous_lift Unit (J.sum K).Fiber πM))
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit K.Fiber πM).continuous_iff]
          exact (Pullback.continuous_proj Unit (J.sum K).Fiber πM).prodMk
            (continuous_sum_snd.comp (Pullback.continuous_lift Unit (J.sum K).Fiber πM))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.sum K).Fiber πM).continuous_iff]
        apply ((Pullback.continuous_proj Unit J.Fiber πM).comp continuous_sum_fst).prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit J.Fiber πM).comp continuous_sum_fst).prodMk
          ((Pullback.continuous_lift Unit K.Fiber πM).comp continuous_sum_snd) }
  let identity := CompactSupportTriple.ofIso (Iso.refl ((πM : _ → M) *ᵖ C.Fiber))
  let ι := EquivariantSupportBundleTriple.identity (C.pullback πM)
    (τ.pullback πM (fun _ _ ↦ rfl))
  have hidentity : identity.IsEquivariant (τ.pullback πM (fun _ _ ↦ rfl))
      (τ.pullback πM (fun _ _ ↦ rfl)) := ι.2.isEquivariant
  have hsum := haEq.sum hidentity
  let b := (a.sum identity).congr (compare E C).symm (compare F C).symm
  have hb : b.control = a.control := by
    change a.control ∪ ∅ = a.control
    exact Set.union_empty _
  have hbEq : b.IsEquivariant ((ρE.sum τ).pullback πM (fun _ _ ↦ rfl))
      ((ρF.sum τ).pullback πM (fun _ _ ↦ rfl)) := by
    refine ⟨hsum.invariant_control, ?_⟩
    intro g x v
    exact hsum.boundary_intertwines g x v
  refine ⟨C, τ, ρ, j, hj, hP, hQ, b, hbEq, hb, ?_, ?_⟩
  · -- The actual product boundary keeps both original vectors, on the same exterior point.
    intro z ha' hb' v
    let a' := a.enlarge _ (a.isCompact_control.union identity.isCompact_control)
      Set.subset_union_left
    let i' := identity.enlarge _ (a.isCompact_control.union identity.isCompact_control)
      Set.subset_union_right
    change (RelativeTriple.sum a'.boundary i'.boundary).linearEquiv ⟨z, hb'⟩ v = _
    exact (RelativeTriple.sum_apply a'.boundary i'.boundary ⟨z, hb'⟩ v).trans
      (Prod.ext (a.enlarge_apply _ _ _ _ _) (identity.enlarge_apply _ _ _ _ _))
  · -- The same equivariant isomorphism square relates the stabilized original generators.
    let A := EquivariantSupportBundleTriple.ofBoundary
      (E.pullback πM) (F.pullback πM) a
      (ρE.pullback πM (fun _ _ ↦ rfl)) (ρF.pullback πM (fun _ _ ↦ rfl)) haEq
    let B := EquivariantSupportBundleTriple.ofBoundary (P.pullback πM) (Q.pullback πM) b
      ((ρE.sum τ).pullback πM (fun _ _ ↦ rfl))
      ((ρF.sum τ).pullback πM (fun _ _ ↦ rfl)) hbEq
    have hiso : (A.sum ι).IsIsomorphic B := by
      refine ⟨(a.sum identity).control, (a.sum identity).isCompact_control,
        hsum.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
        (compare E C).symm, (compare F C).symm,
        (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
      intro x v
      exact ((a.sum identity).enlarge_apply _ (a.sum identity).isCompact_control
        (Set.Subset.refl _) x v).trans
        (b.enlarge_apply _ (a.sum identity).isCompact_control (Set.Subset.refl _) x v).symm
    calc
      B.kZeroClass = (A.sum ι).kZeroClass :=
        (equivariantSupportTripleKZero_generator_relations.1 _ _ hiso).symm
      _ = A.kZeroClass + ι.kZeroClass :=
        equivariantSupportTripleKZero_generator_relations.2.1 A ι
      _ = A.kZeroClass := by
        rw [equivariantSupportTripleKZero_generator_relations.2.2, add_zero]

end AtiyahSinger

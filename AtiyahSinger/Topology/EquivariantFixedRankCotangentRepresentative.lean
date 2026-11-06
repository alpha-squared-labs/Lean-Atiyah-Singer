/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundleEmbedding
public import AtiyahSinger.Topology.EquivariantCotangentRepresentative

import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Fixed-rank equivariant cotangent representatives in positive dimension

Public module ID: M1784.

An original off-zero cotangent isomorphism forces equality of the two fiber
ranks at each base point. Adding the same equivariant complement to both sides
therefore gives a fixed global rank while preserving the original equivariant
support class. This is the equivariant stabilization supplement to SG III.13,
Lemma 13.3, using the finite representation complement of Karoubi I.9.31.
Dimension zero is excluded precisely because its punctured fibers are empty.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial isFiniteRank_pullback

set_option maxHeartbeats 1200000 in
-- The original sum/pullback topologies and specified equivariant generator square are retained.
/-- One common equivariant stabilization gives fixed rank in positive cotangent dimension. -/
theorem exists_fixedRank_equivariant_homogeneous_cotangent_representative (hn : 0 < n) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      ∃ E F : FiniteBundle M, ∃ r : ℕ,
        (∀ x, Module.finrank ℂ (E.Fiber x) = r) ∧
        (∀ x, Module.finrank ℂ (F.Fiber x) = r) ∧
        ∃ (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber),
          ∃ a : CompactSupportTriple
              ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
              ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
            ∃ ha : a.IsEquivariant
                (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)),
              a.control = cotangentZeroSet ∧
              (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
                ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ)
                  (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ),
                  a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
                    a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) ∧
              (EquivariantSupportBundleTriple.ofBoundary
                (E.pullback cotangentProjection) (F.pullback cotangentProjection) a
                (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ha).kZeroClass = z :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro z
  obtain ⟨E, F, ρE, ρF, a, haEq, hControl, hhom, hclass⟩ :=
    exists_equivariant_homogeneous_cotangent_representative IG z
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
      simpa only [hControl, cotangentZeroSet, Set.mem_compl_iff, Set.mem_ofPred_eq] using hξ
    exact (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hz⟩).finrank_eq
  -- Use one actual representation complement on both sides, never independent stabilizers.
  obtain ⟨C, τ, ρ, j, _hj⟩ := ρE.exists_finiteRepresentation_complement
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
  have hb : b.control = cotangentZeroSet := by
    change a.control ∪ ∅ = cotangentZeroSet
    simpa only [Set.union_empty] using hControl
  have hbEq : b.IsEquivariant ((ρE.sum τ).pullback πM (fun _ _ ↦ rfl))
      ((ρF.sum τ).pullback πM (fun _ _ ↦ rfl)) := by
    refine ⟨hsum.invariant_control, ?_⟩
    intro g x v
    exact hsum.boundary_intertwines g x v
  refine ⟨P, Q, ρ.dimension, hP, hQ, ρE.sum τ, ρF.sum τ, b, hbEq, hb, ?_, ?_⟩
  · -- The comparison is fiberwise identity, so the original ray law also fixes the summand.
    intro x ξ t ht hξ htξ
    apply LinearEquiv.ext
    intro v
    have hz : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := by
      simpa only [hControl, ← hb] using hξ
    have htz : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := by
      simpa only [hControl, ← hb] using htξ
    let a' := a.enlarge _ (a.isCompact_control.union identity.isCompact_control)
      Set.subset_union_left
    let i' := identity.enlarge _ (a.isCompact_control.union identity.isCompact_control)
      Set.subset_union_right
    change (RelativeTriple.sum a'.boundary i'.boundary).linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ v =
      (RelativeTriple.sum a'.boundary i'.boundary).linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v
    refine (RelativeTriple.sum_apply a'.boundary i'.boundary ⟨⟨x, t • ξ⟩, htξ⟩ v).trans ?_
    refine Eq.trans ?_
      (RelativeTriple.sum_apply a'.boundary i'.boundary ⟨⟨x, ξ⟩, hξ⟩ v).symm
    have hstep (η : CotangentFiber (n := n) x)
        (hη : (⟨x, η⟩ : CotangentTotalSpace) ∈ a'.controlᶜ) :
        (a'.boundary.linearEquiv ⟨⟨x, η⟩, hη⟩ v.1,
          i'.boundary.linearEquiv ⟨⟨x, η⟩, hη⟩ v.2) =
        (a.boundary.linearEquiv ⟨⟨x, η⟩, fun h ↦ hη (Or.inl h)⟩ v.1, v.2) := by
      exact Prod.ext (a.enlarge_apply _ _ _ _ _)
        (identity.enlarge_apply _ _ _ _ _)
    refine (hstep (t • ξ) htξ).trans (Eq.trans ?_ (hstep ξ hξ).symm)
    rw [hhom x ξ t ht hz htz]
    rfl
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
      _ = z := hclass

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantClopenRefinement

/-!
# Finite invariant clopen partitions with the original subtype actions

Public module ID: M1179.

This implementation record packages an actual finite partition of the base.
Its specified actions agree with the ambient action on the same subsets.
It keeps empty pieces and the empty partition available. It is used to choose
whole families of elliptic symbols and to compare their common refinements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace
open scoped Manifold ContDiff

variable {G M : Type*} [Group G] [TopologicalSpace M] [MulAction G M]

/-- Implementation data for a finite invariant clopen partition of the original base. -/
structure EquivariantClopenPartition where
  /-- Number of pieces, possibly zero. -/
  size : ℕ
  /-- The actual open subsets of the base. -/
  piece : Fin size → Opens M
  /-- Each actual piece is also closed. -/
  isClosed : ∀ i, IsClosed (piece i : Set M)
  /-- Distinct pieces do not overlap. -/
  disjoint : Pairwise (fun i j ↦ Disjoint (piece i : Set M) (piece j : Set M))
  /-- The pieces cover the original base. -/
  cover : (⋃ i, (piece i : Set M)) = Set.univ
  /-- The same ambient action preserves membership in each piece. -/
  invariant : ∀ i (g : G) (x : M), g • x ∈ piece i ↔ x ∈ piece i

  /-- The specified action on each actual piece. -/
  mulAction : ∀ i, MulAction G (piece i)
  /-- Each specified action is the restriction of the original ambient action. -/
  equivariant : ∀ i (g : G) (x : piece i),
    letI := mulAction i
    ((g • x : piece i) : M) = g • x.val

namespace EquivariantClopenPartition

variable (P : EquivariantClopenPartition (G := G) (M := M))

/-- A closed piece of the original compact base is compact. -/
theorem compactSpace [CompactSpace M] (i : Fin P.size) : CompactSpace (P.piece i) :=
  isCompact_iff_compactSpace.mp (P.isClosed i).isCompact

/-- Any supplied subtype action agreeing with the ambient action is this same action. -/
theorem mulAction_eq (i : Fin P.size) (a : MulAction G (P.piece i))
    (heq : ∀ (g : G) (x : P.piece i),
      letI := a
      ((g • x : P.piece i) : M) = g • x.val) : a = P.mulAction i := by
  apply MulAction.ext
  funext g x
  exact Subtype.ext ((heq g x).trans (P.equivariant i g x).symm)

/-- Common intersections, indexed once, with precisely the original ambient action. -/
def refinement (Q : EquivariantClopenPartition (G := G) (M := M)) :
    EquivariantClopenPartition (G := G) (M := M) := by
  classical
  let e := (Fintype.equivFin (Fin P.size × Fin Q.size)).symm
  refine {
    size := Fintype.card (Fin P.size × Fin Q.size)
    piece := fun t ↦ P.piece (e t).1 ⊓ Q.piece (e t).2
    isClosed := fun t ↦ (P.isClosed (e t).1).inter (Q.isClosed (e t).2)
    disjoint := ?_
    cover := ?_
    invariant := ?_
    mulAction := fun t ↦ {
      smul := fun g x ↦ ⟨g • x.val,
        (P.invariant (e t).1 g x.val).mpr x.property.1,
        (Q.invariant (e t).2 g x.val).mpr x.property.2⟩
      one_smul := fun x ↦ Subtype.ext (one_smul G x.val)
      mul_smul := fun g h x ↦ Subtype.ext (mul_smul g h x.val) }
    equivariant := fun _ _ _ ↦ rfl }
  · intro i j hij
    by_cases h : (e i).1 = (e j).1
    · have h' : (e i).2 ≠ (e j).2 := by
        intro h'
        apply hij
        exact e.injective (Prod.ext h h')
      exact (Q.disjoint h').mono Set.inter_subset_right Set.inter_subset_right
    · exact (P.disjoint h).mono Set.inter_subset_left Set.inter_subset_left
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hp : x ∈ ⋃ i, (P.piece i : Set M) := by rw [P.cover]; trivial
    have hq : x ∈ ⋃ i, (Q.piece i : Set M) := by rw [Q.cover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    refine ⟨e.symm (i, j), ?_⟩
    change x ∈ (P.piece (e (e.symm (i, j))).1 : Set M) ∧
      x ∈ (Q.piece (e (e.symm (i, j))).2 : Set M)
    simpa only [e.apply_symm_apply] using And.intro hi hj
  · intro t g x
    exact and_congr (P.invariant (e t).1 g x) (Q.invariant (e t).2 g x)

variable [TopologicalSpace G] [ContinuousSMul G M]

/-- The restricted original action is continuous. -/
theorem continuousSMul (i : Fin P.size) :
    letI := P.mulAction i
    ContinuousSMul G (P.piece i) := by
  let := P.mulAction i
  refine ⟨continuous_induced_rng.mpr ?_⟩
  have h : Continuous (fun p : G × P.piece i ↦ p.1 • p.2.val) :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  exact h.congr (fun p ↦ (P.equivariant i p.1 p.2).symm)

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [ChartedSpace VG G] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

omit [ContinuousSMul G M] in
/-- The native open charts retain joint smoothness of the restricted action. -/
theorem contMDiffSMul (i : Fin P.size) :
    letI := P.mulAction i
    ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (P.piece i) := by
  let := P.mulAction i
  refine ⟨?_⟩
  apply (ContMDiff.subtypeVal_comp_iff (P.piece i)
    (fun p : G × P.piece i ↦ p.1 • p.2)).mp
  change ContMDiff (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (fun p : G × P.piece i ↦ ((p.1 • p.2 : P.piece i) : M))
  simp only [P.equivariant]
  have hsub : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Subtype.val : P.piece i → M) :=
    contMDiff_subtype_val
  exact contMDiff_fst.smul (hsub.comp contMDiff_snd)

end EquivariantClopenPartition

end AtiyahSinger

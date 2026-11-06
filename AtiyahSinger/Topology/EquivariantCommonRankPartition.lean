/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantRankStrata

/-!
# A common finite invariant rank partition for two original bundles

Public module ID: M1771.

Two locally finite-rank equivariant bundles on a compact base have one common
finite partition by their actual simultaneous rank strata. Each piece is an
invariant clopen subset of the original base; it is not an arbitrarily chosen
connected component. The two ranks on a piece may differ. Such pieces must be
retained, even when a compact-support triple forces their exterior to be empty.

The partition uses only occupied rank pairs, so its pieces are nonempty and
an empty base has an empty index set. Compactness is needed for finiteness of
the global range, not for local constancy or invariance. No compactness of the
group, separation of the base or global fixed-rank hypothesis is imposed.
The original topology and actions are not replaced by a new disjoint-union
space; actions on individual pieces are inherited through their inclusions.

Sources: Karoubi I.2.9, printed p.7, and II.1.26--1.29, printed pp.56--57.
The simultaneous equivariant refinement is the direct supplement obtained
from the two locally constant rank functions and the original moving-fiber
linear equivalences. No new rank-pair predicate or partition structure is
introduced. The proof enumerates only the occupied rank pairs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [hC : CompactSpace X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [hF : IsFiniteRank F]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X]

include hC hE hF

/-- Two original equivariant bundles have a common finite invariant clopen rank partition. -/
theorem EquivariantStructure.exists_common_rank_partition
    (σE : EquivariantStructure G E) (σF : EquivariantStructure G F) :
    ∃ (k : ℕ) (U : Fin k → Opens X) (r q : Fin k → ℕ),
      (∀ i, U i = rankStratum E (r i) ⊓ rankStratum F (q i)) ∧
      (∀ i, (U i : Set X).Nonempty) ∧
      Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) ∧
      (⋃ i, (U i : Set X)) = Set.univ ∧
      (∀ i, IsClosed (U i : Set X)) ∧
      ∀ (i : Fin k) (g : G) (x : X), g • x ∈ U i ↔ x ∈ U i := by
  /- Stage 1: use the existing local-constancy theorem for each original
  bundle. Their product is the locally constant function that assigns the
  pair (rank E_x, rank F_x) to x. Its range is finite by compactness of X.
  Enumerate precisely this occupied range by Fin k. Distinct indices have
  distinct rank pairs; no arbitrary empty pieces are appended.
  Stage 2: for the pair indexed by i, take U_i to be the intersection of
  the two original rankStratum opens. Membership is precisely equality to
  that pair. Each piece is nonempty because its pair belongs to the range.
  Equality to two distinct pairs is impossible, giving disjointness. Every
  point supplies an occupied pair, giving the stated cover of the same X.
  Stage 3: each rank fiber is clopen by local constancy, so their intersection
  is closed as well as open. The specified maps σE.linearMap g x and
  σF.linearMap g x are linear equivalences and hence preserve both ranks.
  This gives the exact invariant-membership equivalence for the original
  base action, without assuming that G fixes every connected component.
  Stage 4: retain both rank labels independently. For a support triple,
  unequal labels force the boundary exterior of that piece to be empty;
  they do not justify deleting the piece or equating the two ranks. Adding
  an identity bundle to both sides would preserve their rank difference.
  If X is empty, the occupied range is empty and k=0 makes every condition
  valid. Compact support alone on a noncompact X would not supply this finite
  global partition, so compactness of X is explicitly retained. -/
  classical
  let rankPair (x : X) : ℕ × ℕ := (Module.finrank ℂ (E x), Module.finrank ℂ (F x))
  have hrank : IsLocallyConstant rankPair :=
    (isLocallyConstant_finrank E).prodMk (isLocallyConstant_finrank F)
  let R : Set (ℕ × ℕ) := Set.range rankPair
  let : Fintype R := hrank.range_finite.fintype
  let k := Fintype.card R
  let e : Fin k ≃ R := (Fintype.equivFin R).symm
  let r (i : Fin k) : ℕ := (e i).val.1
  let q (i : Fin k) : ℕ := (e i).val.2
  let U (i : Fin k) : Opens X := rankStratum E (r i) ⊓ rankStratum F (q i)
  -- Membership records equality with an occupied pair, retaining both rank labels.
  have hmem (i : Fin k) (x : X) : x ∈ U i ↔ rankPair x = (e i).val := by
    change (_ = _ ∧ _ = _) ↔ _ = _
    exact (@Prod.ext_iff ℕ ℕ (rankPair x) (e i).val).symm
  refine ⟨k, U, r, q, fun _ ↦ rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨x, hx⟩ := (e i).property
    exact ⟨x, (hmem i x).mpr hx⟩
  · -- Distinct occupied pairs cannot contain a common point.
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    apply hij
    apply e.injective
    apply Subtype.ext
    exact ((hmem i x).mp hxi).symm.trans ((hmem j x).mp hxj)
  · apply Set.eq_univ_of_forall
    intro x
    let a : R := ⟨rankPair x, Set.mem_range_self x⟩
    refine Set.mem_iUnion.mpr ⟨e.symm a, (hmem _ x).mpr ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply a).symm
  · intro i
    change IsClosed ({x | Module.finrank ℂ (E x) = r i} ∩
      {x | Module.finrank ℂ (F x) = q i})
    exact ((isLocallyConstant_finrank E).isClosed_fiber (r i)).inter
      ((isLocallyConstant_finrank F).isClosed_fiber (q i))
  · -- The original moving-fiber equivalences preserve each label independently.
    intro i g x
    rw [hmem, hmem]
    have heq : rankPair (g • x) = rankPair x :=
      Prod.ext (σE.finrank_smul g x) (σF.finrank_smul g x)
    rw [heq]

end AtiyahSinger.ComplexBundle

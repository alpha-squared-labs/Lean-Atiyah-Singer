/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantClopenFamilyRestriction

/-!
# Clopen additivity of the full equivariant analytic index

Public module ID: M0476.

The full original index decomposes over every finite invariant clopen
partition, for arbitrary original K classes. Complete symbol families retain
the varying ranks and the same native restrictions throughout the comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

variable [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

variable [FiniteDimensional ℝ VG]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

private theorem index_family
    (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)) :
    equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G) a.kClass =
      a.index := by
  let P := a.partition
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (n := n) (VG := VG)
  let := P.compactSpace
  exact equivariantAnalyticIndexMap_clopen (n := n) (M := M) (VG := VG) (G := G)
    P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
    (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
    (fun i ↦ (a.symbols i).source) (fun i ↦ (a.symbols i).target)
    (fun i ↦ (a.symbols i).sourceAction) (fun i ↦ (a.symbols i).targetAction)
    (fun i ↦ (a.symbols i).source_smooth) (fun i ↦ (a.symbols i).target_smooth)
    (fun i ↦ (a.symbols i).symbol) (fun i ↦ (a.symbols i).elliptic)
    (fun i ↦ (a.symbols i).equivariant)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full original index of any class is the sum of the indices of its clopen restrictions. -/
theorem equivariantAnalyticIndexMap_eq_sum_clopen
    (Q : EquivariantClopenPartition (G := G) (M := M)) :
    letI := Q.mulAction
    letI := Q.continuousSMul
    letI := Q.contMDiffSMul (n := n) (VG := VG)
    letI := Q.compactSpace
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G) z =
        ∑ j, equivariantAnalyticIndexMap (n := n) (M := Q.piece j) (VG := VG) (G := G)
          (equivariantCotangentClopenRestrict 𝓘(ℝ, VG) Q.piece Q.isClosed Q.equivariant z j) := by
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (n := n) (VG := VG)
  let := Q.compactSpace
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro z
  -- One whole family realizes z; restriction retains exactly that family's local symbols.
  obtain ⟨a, ha⟩ := exists_equivariantClopenSymbolFamily
    (n := n) (M := M) (VG := VG) (G := G) z
  obtain ⟨b, hb, hsum⟩ := a.exists_clopen_restriction Q
  rw [← ha, index_family, ← hsum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hb j]
  exact (index_family (b j)).symm

end AtiyahSinger

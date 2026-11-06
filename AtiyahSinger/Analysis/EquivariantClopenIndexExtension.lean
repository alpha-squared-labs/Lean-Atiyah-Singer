/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenAnalyticIndex
public import AtiyahSinger.Topology.EquivariantCotangentClopenExtension

/-!
# The full index of a native clopen cotangent extension

Public module ID: M0482.

A class supported on one actual clopen piece is the inverse clopen restriction
of a family with that class in one coordinate and zero elsewhere. Native open
reconstruction and full index additivity therefore retain its original index.
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Keep the dependent one-coordinate K class in the specified native clopen decomposition.
/-- Extending a class from one invariant clopen piece preserves its full original index. -/
theorem equivariantAnalyticIndexMap_clopen_openPushforward
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
    letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
      fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := Q.piece i) 𝓘(ℝ, VG)
    letI : ∀ i, ContMDiffSMul 𝓘(ℝ, VG)
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
        (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
      fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := Q.piece i) 𝓘(ℝ, VG)
    letI : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
      fun _ ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (i : Fin Q.size)
      (v : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := Q.piece i))),
      equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G)
        (equivariantSupportTripleKZeroOpenPushforward
          ⟨cotangentOpenInclusion (Q.piece i),
            (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).continuous⟩
          (isOpenEmbedding_cotangentOpenInclusion (Q.piece i))
          (cotangentOpenInclusion_smul 𝓘(ℝ, VG) (Q.piece i) (Q.equivariant i)) v) =
      equivariantAnalyticIndexMap (n := n) (M := Q.piece i) (VG := VG) (G := G) v := by
  classical
  let IG := 𝓘(ℝ, VG)
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (n := n) (VG := VG)
  let := Q.compactSpace
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := Q.piece i) IG
  let : ∀ i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := Q.piece i) IG
  let : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
    fun _i ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro i v
  let Φ := equivariantCotangentClopenEquiv (n := n) IG Q.piece Q.isClosed
    Q.equivariant Q.disjoint Q.cover
  let w : ∀ j : Fin Q.size, EquivariantSupportTripleKZero G
      (CotangentTotalSpace (n := n) (M := Q.piece j)) := Pi.single i v
  -- Reconstruct exactly the one-coordinate class with the original native inclusions.
  have hrec := equivariantCotangentKZero_eq_sum_clopen_openPushforward Q (Φ.symm w)
  change Φ.symm w = ∑ j, equivariantSupportTripleKZeroOpenPushforward
    ⟨cotangentOpenInclusion (Q.piece j),
      (isOpenEmbedding_cotangentOpenInclusion (Q.piece j)).continuous⟩
    (isOpenEmbedding_cotangentOpenInclusion (Q.piece j))
    (cotangentOpenInclusion_smul IG (Q.piece j) (Q.equivariant j))
    (Φ (Φ.symm w) j) at hrec
  rw [Φ.apply_symm_apply] at hrec
  have hsingle : Φ.symm w = equivariantSupportTripleKZeroOpenPushforward
      ⟨cotangentOpenInclusion (Q.piece i),
        (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).continuous⟩
      (isOpenEmbedding_cotangentOpenInclusion (Q.piece i))
      (cotangentOpenInclusion_smul IG (Q.piece i) (Q.equivariant i)) v := by
    rw [hrec, Finset.sum_eq_single i]
    · simp [w]
    · intro j _ hji
      simp [w, Pi.single_eq_of_ne hji]
    · simp
  rw [← hsingle]
  -- All other pieces contribute the index of zero, so the original local index remains.
  have hi := equivariantAnalyticIndexMap_eq_sum_clopen Q (Φ.symm w)
  change equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G) (Φ.symm w) =
    ∑ j, equivariantAnalyticIndexMap (n := n) (M := Q.piece j) (VG := VG) (G := G)
      (Φ (Φ.symm w) j) at hi
  rw [Φ.apply_symm_apply] at hi
  rw [hi, Finset.sum_eq_single i]
  · simp [w]
  · intro j _ hji
    simp [w, Pi.single_eq_of_ne hji]
  · simp

end AtiyahSinger

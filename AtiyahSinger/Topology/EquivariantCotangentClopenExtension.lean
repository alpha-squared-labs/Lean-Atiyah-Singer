/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantClopenPartition
public import AtiyahSinger.Topology.EquivariantCotangentClopen
public import AtiyahSinger.Topology.EquivariantOpenHomeomorph

/-!
# Reconstruction by native clopen cotangent extensions

Public module ID: M1775.

The same original proper cotangent restrictions reconstruct every support
class through the actual open inclusions. The point and covector identify
native cotangent spaces with the corresponding open subsets of the ambient
cotangent space; no alternate K presentation is introduced.
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

variable [T2Space M] [CompactSpace G] [T2Space G]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxHeartbeats 80000 in

set_option maxHeartbeats 1200000 in
-- Compare the original native inclusions through their exact open-subset homeomorphisms.
/-- The native clopen cotangent restrictions reconstruct a class by the same open extensions. -/
theorem equivariantCotangentKZero_eq_sum_clopen_openPushforward
    (Q : EquivariantClopenPartition (G := G) (M := M)) :
    letI := Q.mulAction
    letI := Q.continuousSMul
    letI := Q.contMDiffSMul (n := n) (VG := VG)
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
    ∀ z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      z = ∑ i, equivariantSupportTripleKZeroOpenPushforward
        ⟨cotangentOpenInclusion (Q.piece i),
          (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).continuous⟩
        (isOpenEmbedding_cotangentOpenInclusion (Q.piece i))
        (cotangentOpenInclusion_smul 𝓘(ℝ, VG) (Q.piece i) (Q.equivariant i))
        (equivariantCotangentClopenRestrict 𝓘(ℝ, VG) Q.piece Q.isClosed Q.equivariant z i) := by
  classical
  let IG := 𝓘(ℝ, VG)
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (n := n) (VG := VG)
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
  intro z
  -- Pull the original partition back along the native cotangent projection.
  let P : Fin Q.size → Opens (CotangentTotalSpace (n := n) (M := M)) := fun i ↦
    ⟨{z | z.proj ∈ Q.piece i}, (Q.piece i).isOpen.preimage cotangentProjection.continuous⟩
  have hpclosed (i : Fin Q.size) : IsClosed (P i : Set (CotangentTotalSpace (n := n) (M := M))) :=
    (Q.isClosed i).preimage cotangentProjection.continuous
  have hpinv (i : Fin Q.size) (g : G) (z : P i) : g • z.val ∈ P i := by
    change g • z.val.proj ∈ Q.piece i
    rw [← Q.equivariant i g ⟨z.val.proj, z.property⟩]
    exact (g • (⟨z.val.proj, z.property⟩ : Q.piece i)).property
  let : ∀ i, MulAction G (P i) := fun i ↦
    { smul g z := ⟨g • z.val, hpinv i g z⟩
      one_smul z := Subtype.ext (one_smul G z.val)
      mul_smul g k z := Subtype.ext (mul_smul g k z.val) }
  let : ∀ i, ContinuousSMul G (P i) := fun i ↦
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have hpeq (i : Fin Q.size) (g : G) (z : P i) : ((g • z : P i) :
      CotangentTotalSpace (n := n) (M := M)) = g • z.val := rfl
  have hpdisjoint : Pairwise (fun i j ↦ Disjoint
      (P i : Set (CotangentTotalSpace (n := n) (M := M))) (P j)) := by
    intro i j hij
    exact (Q.disjoint hij).preimage _
  have hpcover : (⋃ i, (P i : Set (CotangentTotalSpace (n := n) (M := M)))) =
      Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hz : z.proj ∈ ⋃ i, (Q.piece i : Set M) := by rw [Q.cover]; trivial
    exact (Set.mem_iUnion.mp hz).imp fun i hi ↦ hi
  -- The identification retains exactly the original base point and covector.
  let e (i : Fin Q.size) : CotangentTotalSpace (n := n) (M := Q.piece i) ≃ₜ P i :=
    { toFun z := ⟨cotangentOpenInclusion (Q.piece i) z, z.proj.property⟩
      invFun z := ⟨⟨z.val.proj, z.property⟩, z.val.snd⟩
      left_inv z := by cases z; rfl
      right_inv z := by cases z; rfl
      continuous_toFun :=
        (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).continuous.subtype_mk _
      continuous_invFun := by
        apply (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).isEmbedding.continuous_iff.mpr
        exact continuous_subtype_val }
  have he (i : Fin Q.size) (g : G) (z : CotangentTotalSpace (n := n) (M := Q.piece i)) :
      e i (g • z) = g • e i z := by
    apply Subtype.ext
    exact cotangentOpenInclusion_smul IG (Q.piece i) (Q.equivariant i) g z
  have hes (i : Fin Q.size) (g : G) (z : P i) : (e i).symm (g • z) = g • (e i).symm z := by
    apply (e i).injective
    rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply]
  -- Proper pullback along each actual homeomorphism has its specified inverse pullback.
  let ef (i : Fin Q.size) : C(CotangentTotalSpace (n := n) (M := Q.piece i), P i) :=
    ⟨e i, (e i).continuous⟩
  let eb (i : Fin Q.size) : C(P i, CotangentTotalSpace (n := n) (M := Q.piece i)) :=
    ⟨(e i).symm, (e i).symm.continuous⟩
  let F (i : Fin Q.size) :=
    equivariantSupportTripleKZeroPullback (ef i) (he i) (e i).isProperMap
  let R := equivariantSupportTripleKZeroClopenRestrict P hpclosed hpeq
  -- Contravariant composition identifies the resulting forward map with the declared restriction.
  have hforward (x : EquivariantSupportTripleKZero G
      (CotangentTotalSpace (n := n) (M := M))) (i : Fin Q.size) :
      equivariantCotangentClopenRestrict IG Q.piece Q.isClosed Q.equivariant x i = F i (R x i) := by
    have hcomp := equivariantSupportTripleKZeroPullback_comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(P i, CotangentTotalSpace (n := n) (M := M)))
      (ef i) (hpeq i) (he i) (hpclosed i).isProperMap_subtypeVal
      (e i).isProperMap
    exact DFunLike.congr_fun hcomp x
  let : ∀ i, LocallyCompactSpace (P i) := fun i ↦ (P i).isOpen.locallyCompactSpace
  have hrec := equivariantSupportTripleKZero_eq_sum_clopen_openPushforward
    P hpclosed hpeq hpdisjoint hpcover z
  apply hrec.trans
  apply Finset.sum_congr rfl
  intro i _
  rw [hforward]
  let j : C(CotangentTotalSpace (n := n) (M := Q.piece i),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentOpenInclusion (Q.piece i),
      (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).continuous⟩
  have hj := isOpenEmbedding_cotangentOpenInclusion (n := n) (Q.piece i)
  have hje := cotangentOpenInclusion_smul (n := n) IG (Q.piece i) (Q.equivariant i)
  have htransport := equivariantSupportTripleKZeroPullback_eq_openPushforward_symm
    (e i) (he i) (hes i)
  have hF : F i = equivariantSupportTripleKZeroOpenPushforward (eb i)
      (e i).symm.isOpenEmbedding (hes i) := htransport
  rw [hF]
  have hcomp := DFunLike.congr_fun (equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    (eb i) (e i).symm.isOpenEmbedding (hes i) j hj hje) (R z i)
  exact hcomp

end AtiyahSinger

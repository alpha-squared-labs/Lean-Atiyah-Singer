/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenSymbolFamily
public import AtiyahSinger.Analysis.EquivariantSymbolDiffeomorphTransport
public import AtiyahSinger.Geometry.OpenRefinementSwap

/-!
# Restricting complete symbol families to a clopen partition

Public module ID: M0480.

Each original local symbol is restricted to the actual intersections. The
same point and cotangent covector identify the two orders of restriction.
The resulting families preserve the original K restrictions and their sum
of full representation-valued indices, including varying ranks.
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

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Both orders of native restriction retain their own charts until the explicit swap.
/-- Restriction to a finite clopen partition preserves the original class and index sum. -/
theorem EquivariantClopenSymbolFamily.exists_clopen_restriction
    (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G))
    (Q : EquivariantClopenPartition (G := G) (M := M)) :
    letI := Q.mulAction
    letI := Q.continuousSMul
    letI := Q.contMDiffSMul (n := n) (VG := VG)
    letI := Q.compactSpace
    ∃ b : ∀ j, EquivariantClopenSymbolFamily
        (n := n) (M := Q.piece j) (VG := VG) (G := G),
      (∀ j, (b j).kClass = equivariantCotangentClopenRestrict 𝓘(ℝ, VG)
        Q.piece Q.isClosed Q.equivariant a.kClass j) ∧
      (∑ j, (b j).index) = a.index := by
  classical
  let IG := 𝓘(ℝ, VG)
  let P := a.partition
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (VG := VG) (n := n)
  let := P.compactSpace
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (VG := VG) (n := n)
  let := Q.compactSpace
  let U (i : Fin P.size) (j : Fin Q.size) := openRefinementPiece (P.piece i) (Q.piece j)
  let V (j : Fin Q.size) (i : Fin P.size) := openRefinementPiece (Q.piece j) (P.piece i)
  let : ∀ i j, MulAction G (U i j) := fun i j ↦
    openRefinementMulAction (P.piece i) (Q.piece j) (P.equivariant i) (Q.equivariant j)
  let : ∀ i j, ContinuousSMul G (U i j) := fun i j ↦
    continuousSMul_openRefinement (P.piece i) (Q.piece j)
      (P.equivariant i) (Q.equivariant j)
  let : ∀ i j, ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (U i j) :=
    fun i j ↦ contMDiffSMul_openRefinement IG (P.piece i) (Q.piece j)
      (P.equivariant i) (Q.equivariant j)
  let : ∀ i j, CompactSpace (U i j) := fun i j ↦
    compactSpace_openRefinementPiece (P.piece i) (Q.piece j) (Q.isClosed j)
  let : ∀ j i, MulAction G (V j i) := fun j i ↦
    openRefinementMulAction (Q.piece j) (P.piece i) (Q.equivariant j) (P.equivariant i)
  let : ∀ j i, ContinuousSMul G (V j i) := fun j i ↦
    continuousSMul_openRefinement (Q.piece j) (P.piece i)
      (Q.equivariant j) (P.equivariant i)
  let : ∀ j i, ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (V j i) :=
    fun j i ↦ contMDiffSMul_openRefinement IG (Q.piece j) (P.piece i)
      (Q.equivariant j) (P.equivariant i)
  let : ∀ j i, CompactSpace (V j i) := fun j i ↦
    compactSpace_openRefinementPiece (Q.piece j) (P.piece i) (P.isClosed i)
  have hclosed (i : Fin P.size) (j : Fin Q.size) : IsClosed (U i j : Set (P.piece i)) :=
    isClosed_openRefinementPiece (P.piece i) (Q.piece j) (Q.isClosed j)
  have hpart (i : Fin P.size) := openRefinementPiece_partition
    (P.piece i) Q.piece Q.disjoint Q.cover
  have heq (i : Fin P.size) (j : Fin Q.size) (g : G) (x : U i j) :
      ((g • x : U i j) : P.piece i) = g • x.val := rfl
  have hvclosed (j : Fin Q.size) (i : Fin P.size) : IsClosed (V j i : Set (Q.piece j)) :=
    isClosed_openRefinementPiece (Q.piece j) (P.piece i) (P.isClosed i)
  have hvpart (j : Fin Q.size) := openRefinementPiece_partition
    (Q.piece j) P.piece P.disjoint P.cover
  have hveq (j : Fin Q.size) (i : Fin P.size) (g : G) (x : V j i) :
      ((g • x : V j i) : Q.piece j) = g • x.val := rfl
  let R (j : Fin Q.size) : EquivariantClopenPartition (G := G) (M := Q.piece j) := {
    size := P.size
    piece := V j
    isClosed := hvclosed j
    disjoint := (hvpart j).1
    cover := (hvpart j).2
    invariant := fun i g x ↦ by
      change (g • x).val ∈ P.piece i ↔ x.val ∈ P.piece i
      rw [Q.equivariant]
      exact P.invariant i g x.val
    mulAction := fun i ↦ inferInstance
    equivariant := hveq j }
  -- Decompose each original symbol before changing the order of the intersections.
  choose c hc hsum using fun i ↦ (a.symbols i).exists_clopen_decomposition
    (U i) (hclosed i) (hpart i).1 (hpart i).2 (heq i)
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := P.piece i) IG
  let : ∀ i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := P.piece i) IG
  let : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ j, MulAction G (CotangentTotalSpace (n := n) (M := Q.piece j)) :=
    fun j ↦ smoothCotangentMulAction (n := n) (G := G) (M := Q.piece j) IG
  let : ∀ j, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := Q.piece j)) :=
    fun j ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := Q.piece j) IG
  let : ∀ j, ContinuousSMul G (CotangentTotalSpace (n := n) (M := Q.piece j)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ i j, MulAction G (CotangentTotalSpace (n := n) (M := U i j)) :=
    fun i j ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i j) IG
  let : ∀ i j, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := U i j)) :=
    fun i j ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i j) IG
  let : ∀ i j, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i j)) :=
    fun _ _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ j i, MulAction G (CotangentTotalSpace (n := n) (M := V j i)) :=
    fun j i ↦ smoothCotangentMulAction (n := n) (G := G) (M := V j i) IG
  let : ∀ j i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := V j i)) :=
    fun j i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := V j i) IG
  let : ∀ j i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := V j i)) :=
    fun _ _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let Φ := equivariantCotangentClopenEquiv (n := n) IG P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  have ha (i : Fin P.size) : (a.symbols i).kClass =
      equivariantCotangentClopenRestrict IG P.piece P.isClosed P.equivariant a.kClass i := by
    change (a.symbols i).kClass = Φ (Φ.symm (fun j ↦ (a.symbols j).kClass)) i
    rw [Φ.apply_symm_apply]
  have hlocal (j : Fin Q.size) (i : Fin P.size) :
      ∃ b : EquivariantEllipticSymbolData (n := n) (M := V j i) (VG := VG) (G := G),
        b.kClass = equivariantCotangentClopenRestrict IG (V j) (hvclosed j) (hveq j)
          (equivariantCotangentClopenRestrict IG Q.piece Q.isClosed Q.equivariant
            a.kClass j) i ∧ b.index = (c i j).index := by
    let d := openRefinementSwapDiffeomorph (n := n) (Q.piece j) (P.piece i)
    let f₁ : C(CotangentTotalSpace (n := n) (M := P.piece i),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion (P.piece i),
        (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).continuous⟩
    let f₂ : C(CotangentTotalSpace (n := n) (M := U i j),
        CotangentTotalSpace (n := n) (M := P.piece i)) :=
      ⟨cotangentOpenInclusion (U i j), (isOpenEmbedding_cotangentOpenInclusion (U i j)).continuous⟩
    let g₁ : C(CotangentTotalSpace (n := n) (M := Q.piece j),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion (Q.piece j),
        (isOpenEmbedding_cotangentOpenInclusion (Q.piece j)).continuous⟩
    let g₂ : C(CotangentTotalSpace (n := n) (M := V j i),
        CotangentTotalSpace (n := n) (M := Q.piece j)) :=
      ⟨cotangentOpenInclusion (V j i), (isOpenEmbedding_cotangentOpenInclusion (V j i)).continuous⟩
    have h₁ (g : G) (z : CotangentTotalSpace (n := n) (M := P.piece i)) :
        f₁ (g • z) = g • f₁ z :=
      cotangentOpenInclusion_smul (n := n) IG (P.piece i) (P.equivariant i) g z
    have h₂ (g : G) (z : CotangentTotalSpace (n := n) (M := U i j)) :
        f₂ (g • z) = g • f₂ z :=
      cotangentOpenInclusion_smul (n := n) IG (U i j) (heq i j) g z
    have hg₁ (g : G) (z : CotangentTotalSpace (n := n) (M := Q.piece j)) :
        g₁ (g • z) = g • g₁ z :=
      cotangentOpenInclusion_smul (n := n) IG (Q.piece j) (Q.equivariant j) g z
    have hg₂ (g : G) (z : CotangentTotalSpace (n := n) (M := V j i)) :
        g₂ (g • z) = g • g₂ z :=
      cotangentOpenInclusion_smul (n := n) IG (V j i) (hveq j i) g z
    have hsquare (z : CotangentTotalSpace (n := n) (M := V j i)) :
        f₁ (f₂ (cotangentDiffeomorph d z)) = g₁ (g₂ z) := by
      have hdz := cotangentDiffeomorph_openRefinementSwap (Q.piece j) (P.piece i) z
      change f₁ (f₂ (cotangentDiffeomorph d z)) = _
      rw [hdz]
      rfl
    have hd (g : G) (z : CotangentTotalSpace (n := n) (M := V j i)) :
        cotangentDiffeomorph d (g • z) = g • cotangentDiffeomorph d z := by
      apply ((isOpenEmbedding_cotangentOpenInclusion (P.piece i)).comp
        (isOpenEmbedding_cotangentOpenInclusion (U i j))).injective
      change f₁ (f₂ (cotangentDiffeomorph d (g • z))) =
        f₁ (f₂ (g • cotangentDiffeomorph d z))
      rw [hsquare, h₂, h₁, hg₂, hg₁, hsquare]
    have hbase (g : G) (x : U i j) : d.symm (g • x) = g • d.symm x := by
      apply Subtype.ext
      apply Subtype.ext
      change (g • x.val : P.piece i).val =
        (g • (⟨x.val.val, x.property⟩ : Q.piece j) : Q.piece j).val
      exact (P.equivariant i g x.val).trans
        (Q.equivariant j g ⟨x.val.val, x.property⟩).symm
    obtain ⟨b, hindex, hclass⟩ := (c i j).exists_diffeomorph_pullback d.symm hbase hd
    refine ⟨b, ?_, hindex⟩
    rw [hclass, hc, ha]
    change (equivariantSupportTripleKZeroPullback
      ⟨cotangentDiffeomorph d, (cotangentDiffeomorph d).continuous⟩ hd
      (cotangentDiffeomorph d).isProperMap)
      ((equivariantSupportTripleKZeroPullback f₂ h₂
        (isProperMap_cotangentOpenInclusion _ (hclosed i j)))
        ((equivariantSupportTripleKZeroPullback f₁ h₁
          (isProperMap_cotangentOpenInclusion _ (P.isClosed i))) a.kClass)) =
      (equivariantSupportTripleKZeroPullback g₂ hg₂
        (isProperMap_cotangentOpenInclusion _ (hvclosed j i)))
        ((equivariantSupportTripleKZeroPullback g₁ hg₁
          (isProperMap_cotangentOpenInclusion _ (Q.isClosed j))) a.kClass)
    have hmaps : f₁.comp (f₂.comp
        ⟨cotangentDiffeomorph d, (cotangentDiffeomorph d).continuous⟩) = g₁.comp g₂ :=
      ContinuousMap.ext hsquare
    rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
      ← equivariantSupportTripleKZeroPullback_comp,
      ← equivariantSupportTripleKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← equivariantSupportTripleKZeroPullback_comp]
    congr 1
    congr 1
  choose b hb hindex using hlocal
  let families (j : Fin Q.size) : EquivariantClopenSymbolFamily
      (n := n) (M := Q.piece j) (VG := VG) (G := G) := ⟨R j, b j⟩
  refine ⟨families, ?_, ?_⟩
  · intro j
    let Ψ := equivariantCotangentClopenEquiv (n := n) IG (V j) (hvclosed j)
      (hveq j) (hvpart j).1 (hvpart j).2
    apply Ψ.injective
    change Ψ (Ψ.symm (fun i ↦ (b j i).kClass)) = _
    rw [Ψ.apply_symm_apply]
    funext i
    exact hb j i
  · change (∑ j, ∑ i, (b j i).index) = ∑ i, (a.symbols i).index
    calc
      (∑ j, ∑ i, (b j i).index) = ∑ j, ∑ i, (c i j).index := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_congr rfl (fun i _ ↦ hindex j i)
      _ = ∑ i, ∑ j, (c i j).index := Finset.sum_comm
      _ = ∑ i, (a.symbols i).index := Finset.sum_congr rfl (fun i _ ↦ (hsum i).symm)

end AtiyahSinger

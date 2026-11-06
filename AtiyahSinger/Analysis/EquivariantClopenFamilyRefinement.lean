/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenSymbolFamily
public import AtiyahSinger.Analysis.EquivariantSymbolDiffeomorphTransport
public import AtiyahSinger.Geometry.OpenIntersectionDiffeomorph

/-!
# Refinement of the actual equivariant clopen symbol families

Public module ID: M0478.

Restrict each actual symbol to its native nested-open pieces, then transport
those same data to the flat intersections. Proper cotangent composition keeps
the original K class, and the same finite defect representations keep the sum
index. No independence of arbitrary symbol choices is presumed.
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
-- Keep the native iterated actions and flat-intersection actions distinct until the actual map.
/-- Common refinement preserves the original class and full representation-valued sum index. -/
theorem EquivariantClopenSymbolFamily.exists_refinement
    (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G))
    (Q : EquivariantClopenPartition (G := G) (M := M)) :
    ∃ b : (a.partition.refinement Q).Symbols (n := n) (VG := VG),
      ({ partition := a.partition.refinement Q, symbols := b } :
        EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)).kClass =
          a.kClass ∧
      ({ partition := a.partition.refinement Q, symbols := b } :
        EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)).index =
          a.index := by
  classical
  let IG := 𝓘(ℝ, VG)
  let P := a.partition
  let W := P.refinement Q
  let e := (Fintype.equivFin (Fin P.size × Fin Q.size)).symm
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (VG := VG) (n := n)
  let := P.compactSpace
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (VG := VG) (n := n)
  let := Q.compactSpace
  let := W.mulAction
  let := W.continuousSMul
  let := W.contMDiffSMul (VG := VG) (n := n)
  let := W.compactSpace
  let U (i : Fin P.size) (j : Fin Q.size) := openRefinementPiece (P.piece i) (Q.piece j)
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
  have hclosed (i : Fin P.size) (j : Fin Q.size) : IsClosed (U i j : Set (P.piece i)) :=
    isClosed_openRefinementPiece (P.piece i) (Q.piece j) (Q.isClosed j)
  have hpart (i : Fin P.size) := openRefinementPiece_partition
    (P.piece i) Q.piece Q.disjoint Q.cover
  have heq (i : Fin P.size) (j : Fin Q.size) (g : G) (x : U i j) :
      ((g • x : U i j) : P.piece i) = g • x.val := rfl
  -- First restrict the actual local symbols, retaining their full indices and K restrictions.
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
  let : ∀ i j, MulAction G (CotangentTotalSpace (n := n) (M := U i j)) :=
    fun i j ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i j) IG
  let : ∀ i j, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := U i j)) :=
    fun i j ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i j) IG
  let : ∀ i j, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i j)) :=
    fun _ _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ t, MulAction G (CotangentTotalSpace (n := n) (M := W.piece t)) :=
    fun t ↦ smoothCotangentMulAction (n := n) (G := G) (M := W.piece t) IG
  let : ∀ t, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := W.piece t)) :=
    fun t ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := W.piece t) IG
  let : ∀ t, ContinuousSMul G (CotangentTotalSpace (n := n) (M := W.piece t)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let Φ := equivariantCotangentClopenEquiv (n := n) IG P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  have ha (i : Fin P.size) : (a.symbols i).kClass =
      equivariantCotangentClopenRestrict IG P.piece P.isClosed P.equivariant a.kClass i := by
    change (a.symbols i).kClass = Φ (Φ.symm (fun j ↦ (a.symbols j).kClass)) i
    rw [Φ.apply_symm_apply]
  -- Flatten the actual nested carriers using the same point and cotangent covector.
  have hflat (t : Fin W.size) :
      ∃ b : EquivariantEllipticSymbolData (n := n) (M := W.piece t) (VG := VG) (G := G),
        b.kClass = equivariantCotangentClopenRestrict IG W.piece W.isClosed
          W.equivariant a.kClass t ∧ b.index = (c (e t).1 (e t).2).index := by
    let i := (e t).1
    let j := (e t).2
    let d : W.piece t ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U i j :=
      openIntersectionDiffeomorph (n := n) (P.piece i) (Q.piece j)
    let f : C(CotangentTotalSpace (n := n) (M := W.piece t),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion (W.piece t),
        (isOpenEmbedding_cotangentOpenInclusion (W.piece t)).continuous⟩
    let f₁ : C(CotangentTotalSpace (n := n) (M := P.piece i),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion (P.piece i),
        (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).continuous⟩
    let f₂ : C(CotangentTotalSpace (n := n) (M := U i j),
        CotangentTotalSpace (n := n) (M := P.piece i)) :=
      ⟨cotangentOpenInclusion (U i j), (isOpenEmbedding_cotangentOpenInclusion (U i j)).continuous⟩
    have h₁ (g : G) (z : CotangentTotalSpace (n := n) (M := P.piece i)) :
        f₁ (g • z) = g • f₁ z :=
      cotangentOpenInclusion_smul IG (P.piece i) (P.equivariant i) g z
    have h₂ (g : G) (z : CotangentTotalSpace (n := n) (M := U i j)) :
        f₂ (g • z) = g • f₂ z := cotangentOpenInclusion_smul IG (U i j) (heq i j) g z
    have hf (g : G) (z : CotangentTotalSpace (n := n) (M := W.piece t)) :
        f (g • z) = g • f z :=
      cotangentOpenInclusion_smul IG (W.piece t) (W.equivariant t) g z
    have hsquare (z : CotangentTotalSpace (n := n) (M := W.piece t)) :
        f₁ (f₂ (cotangentDiffeomorph d z)) = f z := by
      change cotangentOpenInclusion (P.piece i)
        (cotangentOpenInclusion (U i j) (cotangentDiffeomorph d z)) = _
      have hdz : cotangentDiffeomorph d z = ⟨d z.proj, z.snd⟩ :=
        cotangentDiffeomorph_openIntersection (P.piece i) (Q.piece j) z
      rw [hdz]
      rfl
    have hd (g : G) (z : CotangentTotalSpace (n := n) (M := W.piece t)) :
        cotangentDiffeomorph d (g • z) = g • cotangentDiffeomorph d z := by
      apply ((isOpenEmbedding_cotangentOpenInclusion (P.piece i)).comp
        (isOpenEmbedding_cotangentOpenInclusion (U i j))).injective
      change f₁ (f₂ (cotangentDiffeomorph d (g • z))) =
        f₁ (f₂ (g • cotangentDiffeomorph d z))
      rw [hsquare, h₂, h₁, hsquare]
      exact hf g z
    have hbase (g : G) (x : U i j) : d.symm (g • x) = g • d.symm x := by
      apply Subtype.ext
      exact P.equivariant i g x.val
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
      (equivariantSupportTripleKZeroPullback f hf
        (isProperMap_cotangentOpenInclusion _ (W.isClosed t))) a.kClass
    have hmaps : f₁.comp (f₂.comp
        ⟨cotangentDiffeomorph d, (cotangentDiffeomorph d).continuous⟩) = f :=
      ContinuousMap.ext hsquare
    rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
      ← equivariantSupportTripleKZeroPullback_comp,
      ← equivariantSupportTripleKZeroPullback_comp]
    congr 1
    congr 1
  choose b hb hindex using hflat
  refine ⟨b, ?_, ?_⟩
  · let Ψ := equivariantCotangentClopenEquiv (n := n) IG W.piece W.isClosed
      W.equivariant W.disjoint W.cover
    apply Ψ.injective
    change Ψ (Ψ.symm (fun t ↦ (b t).kClass)) = Ψ a.kClass
    rw [Ψ.apply_symm_apply]
    funext t
    exact hb t
  · change (∑ t, (b t).index) = ∑ i, (a.symbols i).index
    calc
      (∑ t, (b t).index) = ∑ t, (c (e t).1 (e t).2).index :=
        Finset.sum_congr rfl (fun t _ ↦ hindex t)
      _ = ∑ i, ∑ j, (c i j).index := by
        rw [← Fintype.sum_prod_type (fun ij : Fin P.size × Fin Q.size ↦ (c ij.1 ij.2).index)]
        exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = ∑ i, (a.symbols i).index := Finset.sum_congr rfl (fun i _ ↦ (hsum i).symm)

end AtiyahSinger

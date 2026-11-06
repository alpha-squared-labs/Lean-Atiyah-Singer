/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenSymbolFamily
public import AtiyahSinger.Analysis.EquivariantSymbolDiffeomorphTransport
public import AtiyahSinger.Geometry.EquivariantClopenDiffeomorph

/-!
# Actual equivariant symbol families under a diffeomorphism

Public module ID: M0477.

The inverse-image partition has the same finite indexing. On each piece the
same diffeomorphism transports the original symbol data and full index. The
actual cotangent inclusion square and proper pullback composition identify the
reconstructed original K class. This permits arbitrary varying ranks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [CompactSpace N] [T2Space N] [SecondCountableTopology N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Preserve each original local operator through the same native cotangent square.
/-- Diffeomorphisms transport whole families with their original class and full sum index. -/
theorem EquivariantClopenSymbolFamily.exists_diffeomorph_pullback
    (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G))
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N)
    (he : ∀ (g : G) (x : M), e (g • x) = g • e x)
    (hcot : letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
      letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
      ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := N)),
        cotangentDiffeomorph e.symm (g • z) = g • cotangentDiffeomorph e.symm z) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∃ b : EquivariantClopenSymbolFamily (n := n) (M := N) (VG := VG) (G := G),
      b.index = a.index ∧ b.kClass = equivariantSupportTripleKZeroPullback
        ⟨cotangentDiffeomorph e.symm, (cotangentDiffeomorph e.symm).continuous⟩
        hcot (cotangentDiffeomorph e.symm).isProperMap a.kClass := by
  classical
  let IG := 𝓘(ℝ, VG)
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let f : C(N, M) := ⟨e.symm, e.symm.continuous⟩
  have hf (g : G) (x : N) : f (g • x) = g • f x := by
    apply e.injective
    change e (e.symm (g • x)) = e (g • e.symm x)
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let P := a.partition
  let Q := P.pullback f hf
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (VG := VG) (n := n)
  let := P.compactSpace
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (VG := VG) (n := n)
  let := Q.compactSpace
  let : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := P.piece i) IG
  let : ∀ i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := P.piece i) IG
  let : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := Q.piece i) IG
  let : ∀ i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := Q.piece i) IG
  let : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let F : C(CotangentTotalSpace (n := n) (M := N),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentDiffeomorph e.symm, (cotangentDiffeomorph e.symm).continuous⟩
  let pull := equivariantSupportTripleKZeroPullback F hcot
    (cotangentDiffeomorph e.symm).isProperMap
  let Φ := equivariantCotangentClopenEquiv (n := n) IG P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  have ha (i : Fin P.size) : (a.symbols i).kClass =
      equivariantCotangentClopenRestrict IG P.piece P.isClosed P.equivariant a.kClass i := by
    change (a.symbols i).kClass = Φ (Φ.symm (fun j ↦ (a.symbols j).kClass)) i
    rw [Φ.apply_symm_apply]
  -- Pull back each original symbol along the same restricted diffeomorphism.
  have hlocal (i : Fin Q.size) :
      ∃ b : EquivariantEllipticSymbolData (n := n) (M := Q.piece i) (VG := VG) (G := G),
        b.index = (a.symbols i).index ∧ b.kClass =
          equivariantCotangentClopenRestrict IG Q.piece Q.isClosed Q.equivariant
            (pull a.kClass) i := by
    let d : Q.piece i ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ P.piece i :=
      openPreimageDiffeomorph e.symm (P.piece i)
    let p : C(CotangentTotalSpace (n := n) (M := P.piece i),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion (P.piece i),
        (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).continuous⟩
    let q : C(CotangentTotalSpace (n := n) (M := Q.piece i),
        CotangentTotalSpace (n := n) (M := N)) :=
      ⟨cotangentOpenInclusion (Q.piece i),
        (isOpenEmbedding_cotangentOpenInclusion (Q.piece i)).continuous⟩
    have hp (g : G) (z : CotangentTotalSpace (n := n) (M := P.piece i)) :
        p (g • z) = g • p z := cotangentOpenInclusion_smul IG _ (P.equivariant i) g z
    have hq (g : G) (z : CotangentTotalSpace (n := n) (M := Q.piece i)) :
        q (g • z) = g • q z := cotangentOpenInclusion_smul IG _ (Q.equivariant i) g z
    have hsquare (z : CotangentTotalSpace (n := n) (M := Q.piece i)) :
        p (cotangentDiffeomorph d z) = F (q z) :=
      cotangentDiffeomorph_openPreimage e.symm (P.piece i) z
    have hd (g : G) (z : CotangentTotalSpace (n := n) (M := Q.piece i)) :
        cotangentDiffeomorph d (g • z) = g • cotangentDiffeomorph d z := by
      apply (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).injective
      change p (cotangentDiffeomorph d (g • z)) = p (g • cotangentDiffeomorph d z)
      rw [hsquare, hp, hsquare, hq]
      exact hcot g (q z)
    have hbase (g : G) (x : P.piece i) : d.symm (g • x) = g • d.symm x := by
      apply Subtype.ext
      change e ((g • x : P.piece i).val) = g • e x.val
      rw [P.equivariant, he]
    obtain ⟨b, hi, hb⟩ := (a.symbols i).exists_diffeomorph_pullback d.symm hbase hd
    refine ⟨b, hi, ?_⟩
    rw [hb, ha]
    change (equivariantSupportTripleKZeroPullback
      ⟨cotangentDiffeomorph d, (cotangentDiffeomorph d).continuous⟩ hd
      (cotangentDiffeomorph d).isProperMap)
      ((equivariantSupportTripleKZeroPullback p hp
        (isProperMap_cotangentOpenInclusion _ (P.isClosed i))) a.kClass) =
      (equivariantSupportTripleKZeroPullback q hq
        (isProperMap_cotangentOpenInclusion _ (Q.isClosed i))) (pull a.kClass)
    have hmaps : p.comp ⟨cotangentDiffeomorph d, (cotangentDiffeomorph d).continuous⟩ =
        F.comp q := ContinuousMap.ext hsquare
    rw [← AddMonoidHom.comp_apply, ← equivariantSupportTripleKZeroPullback_comp]
    change (equivariantSupportTripleKZeroPullback _ _ _) a.kClass =
      ((equivariantSupportTripleKZeroPullback q hq _).comp
        (equivariantSupportTripleKZeroPullback F hcot _)) a.kClass
    rw [← equivariantSupportTripleKZeroPullback_comp]
    congr 1
    congr 1
  choose b hi hb using hlocal
  refine ⟨⟨Q, b⟩, ?_, ?_⟩
  · change (∑ i, (b i).index) = ∑ i, (a.symbols i).index
    exact Finset.sum_congr rfl (fun i _ ↦ hi i)
  · let Ψ := equivariantCotangentClopenEquiv (n := n) IG Q.piece Q.isClosed
      Q.equivariant Q.disjoint Q.cover
    apply Ψ.injective
    change Ψ (Ψ.symm (fun i ↦ (b i).kClass)) = Ψ (pull a.kClass)
    rw [Ψ.apply_symm_apply]
    funext i
    exact hb i

end AtiyahSinger

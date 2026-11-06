/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndexDiffeomorph
public import AtiyahSinger.Analysis.EquivariantClopenIndexExtension
public import AtiyahSinger.Geometry.InvariantOpenAction
public import AtiyahSinger.Topology.EquivariantOpenHomeomorph

/-!
# Equivariant analytic excision with a compact common source

Public module ID: M0489.

A compact source identifies its image as an invariant clopen submanifold.
Clopen extension preserves the full original index on every support K class;
diffeomorphism naturality then compares precisely the specified source and
its native inverse-dual cotangent embedding. No positive dimension or fixed
bundle rank is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [CompactSpace O] [T2Space O] [SecondCountableTopology O]
  [MeasurableSpace O] [BorelSpace O]
  [MulAction G O] [ContinuousSMul G O]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Keep the supplied source map and both native action dictionaries through the clopen comparison.
/-- A compact common source has the same full index after its actual open cotangent embedding. -/
theorem equivariantAnalyticIndexMap_compactSource_openPushforward
    (U : Opens M)
    (f : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (hf : ∀ (g : G) (x : O), (f (g • x) : M) = g • (f x : M)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let j : C(CotangentTotalSpace (n := n) (M := O),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨fun z ↦ cotangentOpenInclusion U (cotangentDiffeomorph f z),
        (isOpenEmbedding_cotangentOpenInclusion U).continuous.comp
          (cotangentDiffeomorph f).continuous⟩
    ∀ (heq : ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := O)), j (g • z) = g • j z)
      (v : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := O))),
      equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G)
        (equivariantSupportTripleKZeroOpenPushforward j
          ((isOpenEmbedding_cotangentOpenInclusion U).comp
            (cotangentDiffeomorph f).isOpenEmbedding) heq v) =
        equivariantAnalyticIndexMap (n := n) (M := O) (VG := VG) (G := G) v := by
  classical
  let IG := 𝓘(ℝ, VG)
  let := smoothCotangentMulAction (n := n) (G := G) (M := O) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let j : C(CotangentTotalSpace (n := n) (M := O),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨fun z ↦ cotangentOpenInclusion U (cotangentDiffeomorph f z),
      (isOpenEmbedding_cotangentOpenInclusion U).continuous.comp
        (cotangentDiffeomorph f).continuous⟩
  dsimp only
  intro heq v
  -- The same compact source makes its invariant open image closed as well.
  have hUi (g : G) (x : U) : g • x.val ∈ U := by
    have h := hf g (f.symm x)
    rw [f.apply_symm_apply] at h
    rw [← h]
    exact (f (g • f.symm x)).property
  have hU (g : G) (x : M) : g • x ∈ U ↔ x ∈ U := by
    constructor
    · intro hx
      simpa only [inv_smul_smul] using hUi g⁻¹ ⟨g • x, hx⟩
    · intro hx
      exact hUi g ⟨x, hx⟩
  let : MulAction G U := invariantOpenMulAction U hU
  let : ContinuousSMul G U := continuousSMul_invariantOpen U hU
  let : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U :=
    contMDiffSMul_invariantOpen IG U hU
  let : CompactSpace U := f.toHomeomorph.compactSpace
  have hclosed : IsClosed (U : Set M) :=
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace U)).isClosed
  let W : Opens M := ⟨(U : Set M)ᶜ, hclosed.isOpen_compl⟩
  let pieces (i : Fin 2) : Opens M := if i = 0 then U else W
  have hinv (i : Fin 2) (g : G) (x : M) : g • x ∈ pieces i ↔ x ∈ pieces i := by
    by_cases hi : i = 0
    · simpa only [pieces, ite_eq_left hi] using hU g x
    · dsimp only [pieces]
      rw [ite_eq_right hi]
      change (g • x ∉ U ↔ x ∉ U)
      exact not_congr (hU g x)
  let Q : EquivariantClopenPartition (G := G) (M := M) := {
    size := 2
    piece := pieces
    isClosed := fun i ↦ by
      by_cases hi : i = 0
      · simpa only [pieces, ite_eq_left hi] using hclosed
      · simpa only [pieces, ite_eq_right hi, W, Opens.coe_mk] using U.isOpen.isClosed_compl
    disjoint := by
      intro i k hik
      fin_cases i <;> fin_cases k
      · exact (hik rfl).elim
      · exact disjoint_compl_right
      · exact disjoint_compl_left
      · exact (hik rfl).elim
    cover := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x ∈ U
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
    invariant := hinv
    mulAction := fun i ↦ invariantOpenMulAction (pieces i) (hinv i)
    equivariant := fun _ _ _ ↦ rfl }
  let := smoothCotangentMulAction (n := n) (G := G) (M := U) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let d := cotangentDiffeomorph f
  let k : C(CotangentTotalSpace (n := n) (M := U),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  have hk := isOpenEmbedding_cotangentOpenInclusion (n := n) U
  have hke (g : G) (z : CotangentTotalSpace (n := n) (M := U)) : k (g • z) = g • k z :=
    cotangentOpenInclusion_smul IG U (fun _ _ ↦ rfl) g z
  have hd (g : G) (z : CotangentTotalSpace (n := n) (M := O)) : d (g • z) = g • d z := by
    apply hk.injective
    change j (g • z) = k (g • d z)
    rw [heq, hke]
    rfl
  have hds (g : G) (z : CotangentTotalSpace (n := n) (M := U)) :
      d.symm (g • z) = g • d.symm z := by
    apply d.injective
    rw [d.apply_symm_apply, hd, d.apply_symm_apply]
  let w := equivariantSupportTripleKZeroOpenPushforward ⟨d, d.continuous⟩
    d.isOpenEmbedding hd v
  have hcompose : equivariantSupportTripleKZeroOpenPushforward j
      (hk.comp d.isOpenEmbedding) heq v =
      equivariantSupportTripleKZeroOpenPushforward k hk hke w :=
    DFunLike.congr_fun (equivariantSupportTripleKZeroOpenPushforward_functoriality.2
      ⟨d, d.continuous⟩ d.isOpenEmbedding hd k hk hke) v
  have hopen : equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G)
      (equivariantSupportTripleKZeroOpenPushforward k hk hke w) =
      equivariantAnalyticIndexMap (n := n) (M := U) (VG := VG) (G := G) w :=
    equivariantAnalyticIndexMap_clopen_openPushforward Q 0 w
  -- Diffeomorphism invariance uses exactly f and the same inverse-dual cotangent map.
  have hpull := equivariantSupportTripleKZeroPullback_eq_openPushforward_symm
    d.symm hds hd
  have hbase (g : G) (x : O) : f (g • x) = g • f x := Subtype.ext (hf g x)
  have hsymm : cotangentDiffeomorph f.symm = d.symm := by
    apply Homeomorph.ext
    intro z
    apply d.injective
    rw [d.apply_symm_apply]
    have hc := congrArg (fun e ↦ e z) (cotangentDiffeomorph_trans f.symm f)
    change cotangentDiffeomorph (f.symm.trans f) z = d (cotangentDiffeomorph f.symm z) at hc
    rw [← hc]
    have he : f.symm.trans f = Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) U ∞ := by
      apply Diffeomorph.ext
      intro x
      exact f.apply_symm_apply x
    rw [he]
    change (⟨z.proj, z.snd.comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        id z.proj)⟩ : CotangentTotalSpace (n := n) (M := U)) = z
    rw [mfderiv_id, ContinuousLinearMap.comp_id]
  have hcot (g : G) (z : CotangentTotalSpace (n := n) (M := U)) :
      cotangentDiffeomorph f.symm (g • z) = g • cotangentDiffeomorph f.symm z := by
    rw [hsymm]
    exact hds g z
  have hindex := equivariantAnalyticIndexMap_diffeomorphPullback f hbase hcot v
  have hvalue : equivariantAnalyticIndexMap (n := n) (M := U) (VG := VG) (G := G) w =
      equivariantAnalyticIndexMap (n := n) (M := O) (VG := VG) (G := G) v := by
    simpa only [hsymm, hpull, Homeomorph.symm_symm, w] using hindex
  exact (congrArg (equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G))
    hcompose).trans (hopen.trans hvalue)

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Topology.EquivariantClopenKZero

/-!
# Equivariant cotangent K theory on an invariant clopen partition

Public module ID: M1774.

The original cotangent inclusion of an invariant open submanifold intertwines
the native inverse-differential lifts of the same base action. A finite clopen
partition then decomposes the original equivariant support K group by actual
proper pullbacks to the native cotangent spaces of its pieces. The additive
equivalence has exactly those pullbacks as its forward map.

Sources: SG III.1 (1.6), III.3 coordinate covariance, and III.13.4 provide the
geometric cotangent identifications; KA II.1.26 gives the ordinary compact-space
finite decomposition. The equivariant compact-support specialization is the original
presentation argument already recorded in EquivariantClopenKZero, combined
with the actual cotangent inclusion. It is a project supplement, not a claim
that those book passages separately state this native-carrier formulation.

Properness follows from closedness of the base pieces, not compactness of the
cotangent fibers. No compactness of the group or base, Lie-group inversion,
Hausdorffness, globally constant rank, or nonempty-piece condition is used.
The supplied actions on the pieces must agree with the original base action.
The original action comparison and finite decomposition are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 20

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hM in
/-- The actual open cotangent inclusion intertwines the native inverse-differential actions. -/
theorem cotangentOpenInclusion_smul (U : Opens M)
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := smoothCotangentMulAction (n := n) (G := G) (M := U) IG
    ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := U)),
      cotangentOpenInclusion U (g • z) = g • cotangentOpenInclusion U z := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let H := EuclideanSpace ℝ (Fin n)
  -- Compare the same action in the inherited charts of the open submanifold.
  have hderiv (k : G) (x : U) :
      mfderiv I I (fun y : U ↦ k • y) x =
        mfderiv I I (fun y : M ↦ k • y) x.val := by
    have hchart : (chartAt H x.val).symm =ᶠ[𝓝 (chartAt H x x)]
        Subtype.val ∘ (chartAt H x).symm := by
      filter_upwards [(chartAt H x).open_target.mem_nhds
        ((chartAt H x).map_source (mem_chart_source H x))] with w hw
      exact ((chartAt H x.val).subtypeRestr_symm_eqOn ⟨x⟩) hw
    have hlocal : writtenInExtChartAt I I x (fun y : U ↦ k • y) =ᶠ[
        𝓝 (extChartAt I x x)]
        writtenInExtChartAt I I x.val (fun y : M ↦ k • y) := by
      filter_upwards [hchart] with w hw
      simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
        I, Function.comp_def]
      change chartAt H (k • x).val ((k • ((chartAt H x).symm w) : U) : M) =
        chartAt H (k • x.val) (k • ((chartAt H x.val).symm w))
      rw [heq, heq, hw]
      rfl
    have hu : MDifferentiableAt I I (fun y : U ↦ k • y) x :=
      (Diffeomorph.smul IG I ∞ k).contMDiff.mdifferentiable (by simp) x
    have hm : MDifferentiableAt I I (fun y : M ↦ k • y) x.val :=
      (Diffeomorph.smul IG I ∞ k).contMDiff.mdifferentiable (by simp) x.val
    exact hu.mfderiv_abuse.trans (hlocal.fderivWithin_eq_of_nhds.trans hm.mfderiv_abuse.symm)
  -- The original covector is precomposed with these equal inverse differentials.
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := smoothCotangentMulAction (n := n) (G := G) (M := U) IG
  intro g z
  apply Bundle.TotalSpace.ext (heq g z.proj)
  apply heq_of_eq
  change z.snd.comp (mfderiv I I (fun y : U ↦ g⁻¹ • y) (g • z.proj)) =
    z.snd.comp (mfderiv I I (fun y : M ↦ g⁻¹ • y) (g • z.proj.val))
  rw [hderiv, heq]
  rfl

variable [hG : IsManifold IG ∞ G]
  {ι : Type*} (U : ι → Opens M)
  [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
  [∀ i, ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (U i)]
  (hclosed : ∀ i : ι, IsClosed (U i : Set M))
  (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : M) = g • (x : M))

/-- Restrict along the actual proper cotangent inclusions with their native lifted actions. -/
def equivariantCotangentClopenRestrict :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
      fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) IG
    letI : ∀ i, ContMDiffSMul IG
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
        (CotangentTotalSpace (n := n) (M := U i)) :=
      fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i) IG
    letI : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i)) :=
      fun _i ↦ ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
      (∀ i : ι, EquivariantSupportTripleKZero G
        (CotangentTotalSpace (n := n) (M := U i))) :=
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) IG
  letI : ∀ i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i) IG
  letI : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun _i ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  AddMonoidHom.pi fun i ↦
    equivariantSupportTripleKZeroPullback
      ⟨cotangentOpenInclusion (U i),
        (isOpenEmbedding_cotangentOpenInclusion (U i)).continuous⟩
      (cotangentOpenInclusion_smul IG (U i) (heq i))
      (isProperMap_cotangentOpenInclusion (U i) (hclosed i))

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 80000 in
/-- A finite invariant clopen partition gives a bijective actual cotangent restriction. -/
theorem equivariantCotangentClopenRestrict_bijective [Finite ι]
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i : ι, (U i : Set M)) = Set.univ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
      fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) IG
    letI : ∀ i, ContMDiffSMul IG
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
        (CotangentTotalSpace (n := n) (M := U i)) :=
      fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i) IG
    letI : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i)) :=
      fun _i ↦ ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    Function.Bijective (equivariantCotangentClopenRestrict (n := n) IG U hclosed heq) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) IG
  let : ∀ i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i) IG
  let : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun _i ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  -- Pull the original partition back along the native cotangent projection.
  let P : ι → Opens (CotangentTotalSpace (n := n) (M := M)) := fun i ↦
    ⟨{z | z.proj ∈ U i}, (U i).isOpen.preimage cotangentProjection.continuous⟩
  have hpclosed (i : ι) : IsClosed (P i : Set (CotangentTotalSpace (n := n) (M := M))) :=
    (hclosed i).preimage cotangentProjection.continuous
  have hpinv (i : ι) (g : G) (z : P i) : g • z.val ∈ P i := by
    change g • z.val.proj ∈ U i
    rw [← heq i g ⟨z.val.proj, z.property⟩]
    exact (g • (⟨z.val.proj, z.property⟩ : U i)).property
  let : ∀ i, MulAction G (P i) := fun i ↦
    { smul g z := ⟨g • z.val, hpinv i g z⟩
      one_smul z := Subtype.ext (one_smul G z.val)
      mul_smul g k z := Subtype.ext (mul_smul g k z.val) }
  let : ∀ i, ContinuousSMul G (P i) := fun i ↦
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have hpeq (i : ι) (g : G) (z : P i) : ((g • z : P i) :
      CotangentTotalSpace (n := n) (M := M)) = g • z.val := rfl
  have hpdisjoint : Pairwise (fun i j ↦ Disjoint
      (P i : Set (CotangentTotalSpace (n := n) (M := M))) (P j)) := by
    intro i j hij
    exact (hdisjoint hij).preimage _
  have hpcover : (⋃ i, (P i : Set (CotangentTotalSpace (n := n) (M := M)))) =
      Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hz : z.proj ∈ ⋃ i, (U i : Set M) := by rw [hcover]; trivial
    exact (Set.mem_iUnion.mp hz).imp fun i hi ↦ hi
  -- The identification retains exactly the original base point and covector.
  let e (i : ι) : CotangentTotalSpace (n := n) (M := U i) ≃ₜ P i :=
    { toFun z := ⟨cotangentOpenInclusion (U i) z, z.proj.property⟩
      invFun z := ⟨⟨z.val.proj, z.property⟩, z.val.snd⟩
      left_inv z := by cases z; rfl
      right_inv z := by cases z; rfl
      continuous_toFun := (isOpenEmbedding_cotangentOpenInclusion (U i)).continuous.subtype_mk _
      continuous_invFun := by
        apply (isOpenEmbedding_cotangentOpenInclusion (U i)).isEmbedding.continuous_iff.mpr
        exact continuous_subtype_val }
  have he (i : ι) (g : G) (z : CotangentTotalSpace (n := n) (M := U i)) :
      e i (g • z) = g • e i z := by
    apply Subtype.ext
    exact cotangentOpenInclusion_smul IG (U i) (heq i) g z
  have hes (i : ι) (g : G) (z : P i) : (e i).symm (g • z) = g • (e i).symm z := by
    apply (e i).injective
    rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply]
  -- Proper pullback along each actual homeomorphism has its specified inverse pullback.
  let ef (i : ι) : C(CotangentTotalSpace (n := n) (M := U i), P i) :=
    ⟨e i, (e i).continuous⟩
  let eb (i : ι) : C(P i, CotangentTotalSpace (n := n) (M := U i)) :=
    ⟨(e i).symm, (e i).symm.continuous⟩
  let F (i : ι) := equivariantSupportTripleKZeroPullback (ef i) (he i) (e i).isProperMap
  let B (i : ι) := equivariantSupportTripleKZeroPullback (eb i) (hes i) (e i).symm.isProperMap
  have hBF (i : ι) : (B i).comp (F i) = AddMonoidHom.id _ := by
    dsimp only [B, F]
    rw [← equivariantSupportTripleKZeroPullback_comp]
    have hid : (ef i).comp (eb i) =
        ContinuousMap.id (P i) := by
      apply ContinuousMap.ext
      intro z
      exact (e i).apply_symm_apply z
    simp only [hid, equivariantSupportTripleKZeroPullback_id]
  have hFB (i : ι) : (F i).comp (B i) = AddMonoidHom.id _ := by
    dsimp only [B, F]
    rw [← equivariantSupportTripleKZeroPullback_comp]
    have hid : (eb i).comp (ef i) =
        ContinuousMap.id (CotangentTotalSpace (n := n) (M := U i)) := by
      apply ContinuousMap.ext
      intro z
      exact (e i).symm_apply_apply z
    simp only [hid, equivariantSupportTripleKZeroPullback_id]
  have hfbij (i : ι) : Function.Bijective (F i) := by
    constructor
    · intro x y hxy
      have h := congrArg (B i) hxy
      simpa only [← AddMonoidHom.comp_apply, hBF, AddMonoidHom.id_apply] using h
    · intro y
      refine ⟨B i y, ?_⟩
      exact DFunLike.congr_fun (hFB i) y
  let R := equivariantSupportTripleKZeroClopenRestrict P hpclosed hpeq
  have hrbij : Function.Bijective R :=
    equivariantSupportTripleKZeroClopenRestrict_bijective P hpclosed hpeq hpdisjoint hpcover
  -- Contravariant composition identifies the resulting forward map with the declared restriction.
  have hforward (x : EquivariantSupportTripleKZero G
      (CotangentTotalSpace (n := n) (M := M))) (i : ι) :
      equivariantCotangentClopenRestrict IG U hclosed heq x i = F i (R x i) := by
    have hcomp := equivariantSupportTripleKZeroPullback_comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(P i, CotangentTotalSpace (n := n) (M := M)))
      (ef i) (hpeq i) (he i) (hpclosed i).isProperMap_subtypeVal
      (e i).isProperMap
    exact DFunLike.congr_fun hcomp x
  constructor
  · intro x y hxy
    apply hrbij.1
    funext i
    apply (hfbij i).1
    rw [← hforward, ← hforward, hxy]
  · intro y
    choose z hz using fun i ↦ (hfbij i).2 (y i)
    obtain ⟨x, hx⟩ := hrbij.2 z
    refine ⟨x, ?_⟩
    funext i
    rw [hforward, hx, hz]

/-- The cotangent decomposition whose forward map is the specified proper restriction. -/
def equivariantCotangentClopenEquiv [Finite ι]
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i : ι, (U i : Set M)) = Set.univ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
      fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) IG
    letI : ∀ i, ContMDiffSMul IG
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
        (CotangentTotalSpace (n := n) (M := U i)) :=
      fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i) IG
    letI : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i)) :=
      fun _i ↦ ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) ≃+
      (∀ i : ι, EquivariantSupportTripleKZero G
        (CotangentTotalSpace (n := n) (M := U i))) :=
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) IG
  letI : ∀ i, ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i) IG
  letI : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun _i ↦ ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  AddEquiv.ofBijective _
    (equivariantCotangentClopenRestrict_bijective (n := n) IG U hclosed heq hdisjoint hcover)

end AtiyahSinger

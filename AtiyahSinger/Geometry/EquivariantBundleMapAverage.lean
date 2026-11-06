/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

import AtiyahSinger.Geometry.CompactParameterIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Haar averaging of original continuous bundle maps

Public module ID: M1175.

For compact Hausdorff G, the normalized Haar integral of
`σF(g) a(g⁻¹x) σE(g⁻¹)` defines a continuous bundle map on the original
source and target bundles. Its values lie in the
fixed original fiber `F x`; the only transport is the equality `g*(g⁻¹*x)=x`.
The average intertwines the same specified actions. Neither compactness nor
smoothness of the base is needed for this continuous construction.

If both original actions are jointly smooth and the original map is smooth,
this same continuous average is smooth. Only base derivatives enter that
argument, so continuous group inversion suffices; no `LieGroup` assumption
is imposed. Fixed ranks may be zero, and no preconnectedness is required.

Sources: the compact-group averaging method of SG III.9, pp.211--215, and the
standard bundle-morphism formulation of equivariant smoothing. The precise
continuous-map and smooth-preservation interfaces are project supplements;
they are not separately numbered statements in SG. This does not construct
smooth structures on arbitrary continuous equivariant bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.Hom

open Bundle MeasureTheory TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {M : Type*} [TopologicalSpace M] [MulAction G M] [ContinuousSMul G M]
  {r q : ℕ} {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    Hom E F)


set_option linter.unusedSectionVars false in
/-- The exact fiberwise Haar integral is realized by a unique original continuous bundle map. -/
theorem existsUnique_equivariantAverage :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃! b : Hom E F, ∀ (x : M) (v : E x),
      b.linearMap x v =
        ∫ g : G, (smul_inv_smul g x) ▸
          (σF.linearMap g (g⁻¹ • x)
            (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)))
          ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : ∀ x, CompleteSpace (F x) := fun x ↦ FiniteDimensional.complete ℂ (F x)
  let : MulAction G (TotalSpace Unit E) := σE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  -- Conjugation is continuous on the original total spaces before any fiber integral.
  let Ψ (p : G × TotalSpace Unit E) : TotalSpace Unit F :=
    p.1 • a.totalMap (p.1⁻¹ • p.2)
  have hΨ : Continuous Ψ := σF.continuous_action.comp
    (continuous_fst.prodMk (a.continuous_total.comp
      (σE.continuous_action.comp (continuous_fst.inv.prodMk continuous_snd))))
  let L (g : G) (x : M) : E x →ₗ[ℂ] F x :=
    (LinearEquiv.cast (R := ℂ) (M := F) (smul_inv_smul g x)).toLinearMap.comp
      ((σF.linearMap g (g⁻¹ • x)).comp
        ((a.linearMap (g⁻¹ • x)).comp (σE.linearMap g⁻¹ x)))
  have hL (g : G) (x : M) (v : E x) :
      (⟨x, L g x v⟩ : TotalSpace Unit F) = Ψ (g, ⟨x, v⟩) := by
    exact TotalSpace.mk_cast (smul_inv_smul g x) _
  have hLc (x : M) (v : E x) : Continuous (fun g ↦ L g x v) := by
    apply (FiberBundle.totalSpaceMk_isEmbedding (EuclideanSpace ℂ (Fin q)) F x).continuous_iff.mpr
    have ht : Continuous (fun g ↦ (⟨x, L g x v⟩ : TotalSpace Unit F)) :=
      (hΨ.comp (continuous_id.prodMk continuous_const)).congr (fun g ↦ (hL g x v).symm)
    exact (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp ht
  have hi (x : M) (v : E x) : Integrable (fun g ↦ L g x v) μ :=
    (hLc x v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let B (x : M) : E x →ₗ[ℂ] F x := {
    toFun := fun v ↦ ∫ g, L g x v ∂μ
    map_add' := by
      intro v w
      simp only [map_add]
      exact integral_add (hi x v) (hi x w)
    map_smul' := by
      intro c v
      simp only [map_smul, RingHom.id_apply]
      exact integral_smul c (fun g ↦ L g x v) }
  have hB : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, B z.proj z.snd⟩ : TotalSpace Unit F)) := by
    -- A fixed output frame is valid for every group parameter, since conjugation returns to x.
    apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(continuous_model_proj (EuclideanSpace ℂ (Fin r)) E).continuousAt, ?_⟩
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z.proj
    let U : Set (TotalSpace Unit E) := {y | y.proj ∈ f.baseSet}
    have hU : IsOpen U := f.open_baseSet.preimage
      (continuous_model_proj (EuclideanSpace ℂ (Fin r)) E)
    have hz : z ∈ U := mem_baseSet_trivializationAt _ _ _
    let Φ (p : G × TotalSpace Unit E) : EuclideanSpace ℂ (Fin q) :=
      (f (unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F (Ψ p))).2
    have hΦ : ContinuousOn Φ (Set.univ ×ˢ U) := by
      apply (f.continuousOn.comp
        (((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp hΨ).continuousOn)
        ?_).snd
      intro p hp
      apply f.mem_source.mpr
      change (Ψ p).proj ∈ f.baseSet
      have hbase : (Ψ p).proj = p.2.proj :=
        congrArg (fun t : TotalSpace Unit F ↦ t.proj) (hL p.1 p.2.proj p.2.snd).symm
      rw [hbase]
      exact hp.2
    have hint : ContinuousOn (fun y : TotalSpace Unit E ↦ ∫ g, Φ (g, y) ∂μ) U :=
      continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
        (hΦ.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩)) (by simp)
    have heq (y : TotalSpace Unit E) (hy : y ∈ U) :
        (f ⟨y.proj, B y.proj y.snd⟩).2 = ∫ g, Φ (g, y) ∂μ := by
      rw [← f.continuousLinearMapAt_apply_of_mem ℂ hy]
      change f.continuousLinearMapAt ℂ y.proj (∫ g, L g y.proj y.snd ∂μ) = _
      rw [← (f.continuousLinearMapAt ℂ y.proj).integral_comp_comm (hi y.proj y.snd)]
      apply integral_congr_ae
      filter_upwards with g
      rw [f.continuousLinearMapAt_apply_of_mem ℂ hy]
      exact congrArg (fun t : TotalSpace Unit F ↦
        (f (unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F t)).2) (hL g y.proj y.snd)
    exact (hint.continuousAt (hU.mem_nhds hz)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy ↦ heq y hy))
  let b : Hom E F := ⟨B, hB⟩
  have hb (x : M) (v : E x) : b.linearMap x v =
      ∫ g : G, (smul_inv_smul g x) ▸
        (σF.linearMap g (g⁻¹ • x)
          (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))) ∂μ := by
    apply integral_congr_ae
    filter_upwards with g
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.cast_apply,
      eqRec_eq_cast]
  refine ⟨b, hb, ?_⟩
  · intro c hc
    apply Hom.ext
    intro x
    apply LinearMap.ext
    intro v
    exact (hc x v).trans (hb x v).symm

/-- The normalized Haar average, as a map between the same original continuous bundles. -/
def equivariantAverage :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    Hom E F := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  exact Classical.choose (a.existsUnique_equivariantAverage σE σF).exists

/-- The average evaluates to the prescribed normalized integral in the original fiber. -/
theorem equivariantAverage_apply (x : M) (v : E x) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (a.equivariantAverage σE σF).linearMap x v =
      ∫ g : G, (smul_inv_smul g x) ▸
        (σF.linearMap g (g⁻¹ • x)
          (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)))
        ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  -- The chosen map retains exactly the integral property of its existence certificate.
  exact (Classical.choose_spec (a.existsUnique_equivariantAverage σE σF).exists) x v

/-- Normalized left Haar averaging intertwines the two specified original actions. -/
theorem isEquivariant_equivariantAverage :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (a.equivariantAverage σE σF).IsEquivariant σE σF := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : MulAction G (TotalSpace Unit E) := σE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let Ψ (p : G × TotalSpace Unit E) : TotalSpace Unit F :=
    p.1 • a.totalMap (p.1⁻¹ • p.2)
  let L (g : G) (x : M) (v : E x) : F x := (smul_inv_smul g x) ▸
    (σF.linearMap g (g⁻¹ • x)
      (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)))
  have hL (g : G) (x : M) (v : E x) :
      (⟨x, L g x v⟩ : TotalSpace Unit F) = Ψ (g, ⟨x, v⟩) := by
    change (⟨x, L g x v⟩ : TotalSpace Unit F) =
      ⟨g • (g⁻¹ • x), σF.linearMap g (g⁻¹ • x)
        (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))⟩
    simpa only [L, eqRec_eq_cast] using
      (TotalSpace.mk_cast (F := Unit) (smul_inv_smul g x)
        (σF.linearMap g (g⁻¹ • x)
          (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))))
  intro g x v
  -- The action identity is proved in total spaces, so every moving-base transport is retained.
  have hconj (k : G) : L (g * k) (g • x) (σE.linearMap g x v) =
      σF.linearMap g x (L k x v) := by
    apply TotalSpace.mk_injective (F := Unit) (g • x)
    rw [hL]
    change Ψ (g * k, g • (⟨x, v⟩ : TotalSpace Unit E)) =
      g • (⟨x, L k x v⟩ : TotalSpace Unit F)
    rw [hL]
    dsimp only [Ψ]
    simp only [mul_inv_rev, mul_smul, inv_smul_smul]
  -- Left Haar translation replaces the integration variable by g*k.
  rw [equivariantAverage_apply, equivariantAverage_apply]
  change (∫ k, L k (g • x) (σE.linearMap g x v) ∂μ) =
    σF.linearMap g x (∫ k, L k x v ∂μ)
  rw [← integral_mul_left_eq_self (μ := μ)
    (fun k ↦ L k (g • x) (σE.linearMap g x v)) g]
  simp_rw [hconj]
  -- The same fiber action is a continuous linear equivalence and commutes with integration.
  let C : F x ≃L[ℂ] F (g • x) :=
    (LinearEquiv.ofBijective (σF.linearMap g x)
      (σF.linearMap_bijective g x)).toContinuousLinearEquiv
  exact C.integral_comp_comm (fun k ↦ L k x v)

variable {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG) [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)


set_option linter.unusedSectionVars false in
set_option maxHeartbeats 3000000 in
-- Local matrix inversion and compact-parameter integration retain one original average.
include hM hE hF hG hAction hσE hσF in
/-- The same Haar average is smooth when the map and both original actions are smooth. -/
theorem isSmoothBundleMap_equivariantAverage
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      IsSmoothBundleMap (n := n) (r := r) (q := q) a.linearMap) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsSmoothBundleMap (n := n) (r := r) (q := q)
      (a.equivariantAverage σE σF).linearMap := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : MulAction G (TotalSpace Unit E) := σE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  let : μ.IsMulRightInvariant := ⟨fun g ↦
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μ.map (· * g)) μ⟩
  let : IsProbabilityMeasure μ.inv := by
    constructor
    change Measure.map Inv.inv μ Set.univ = 1
    rw [Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ, measure_univ]
  let : μ.inv.IsHaarMeasure := ⟨⟩
  let : μ.IsInvInvariant := ⟨Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ.inv μ⟩
  -- Rewrite the average using inverse fiber operators of the forward action.
  -- These inverses are smooth matrices; no differentiability of group inversion is used.
  let C (p : G × M) : F p.2 ≃ₗ[ℂ] F (p.1 • p.2) :=
    LinearEquiv.ofBijective (σF.linearMap p.1 p.2) (σF.linearMap_bijective p.1 p.2)
  let Z (g : G) (x : M) (v : E x) : F x :=
    (C (g, x)).symm (a.linearMap (g • x) (σE.linearMap g x v))
  have hZ (g : G) (x : M) (v : E x) :
      (⟨x, Z g x v⟩ : TotalSpace Unit F) =
        g⁻¹ • a.totalMap (g • (⟨x, v⟩ : TotalSpace Unit E)) := by
    apply (MulAction.injective g)
    change g • (⟨x, Z g x v⟩ : TotalSpace Unit F) =
      g • (g⁻¹ • a.totalMap (g • (⟨x, v⟩ : TotalSpace Unit E)))
    rw [smul_inv_smul]
    change (⟨g • x, (C (g, x)) ((C (g, x)).symm
      (a.linearMap (g • x) (σE.linearMap g x v)))⟩ : TotalSpace Unit F) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  let L (g : G) (x : M) (v : E x) : F x := (smul_inv_smul g x) ▸
    (σF.linearMap g (g⁻¹ • x)
      (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)))
  have hreverse (g : G) (x : M) (v : E x) : L g x v = Z g⁻¹ x v := by
    apply TotalSpace.mk_injective (F := Unit) x
    rw [hZ, inv_inv]
    change (⟨x, L g x v⟩ : TotalSpace Unit F) =
      ⟨g • (g⁻¹ • x), σF.linearMap g (g⁻¹ • x)
        (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))⟩
    simpa only [L, eqRec_eq_cast] using
      (TotalSpace.mk_cast (F := Unit) (smul_inv_smul g x)
        (σF.linearMap g (g⁻¹ • x)
          (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))))
  intro e he f hf j
  let Φ (p : G × M) : EuclideanSpace ℂ (Fin q) :=
    (f ⟨p.2, Z p.1 p.2 (e.symmL ℂ p.2 (EuclideanSpace.single j 1))⟩).2
  have hΦ : ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
      Φ (Set.univ ×ˢ (e.baseSet ∩ f.baseSet)) := by
    intro p hp
    let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E (p.1 • p.2)
    let k := trivializationAt (EuclideanSpace ℂ (Fin q)) F (p.1 • p.2)
    let U : Set (G × M) := {z | z.2 ∈ e.baseSet ∩ f.baseSet ∧
      z.1 • z.2 ∈ d.baseSet ∩ k.baseSet}
    have hU : IsOpen U :=
      ((e.open_baseSet.inter f.open_baseSet).preimage continuous_snd).inter
        ((d.open_baseSet.inter k.open_baseSet).preimage continuous_smul)
    have hpU : p ∈ U := ⟨hp.2, mem_baseSet_trivializationAt _ _ _,
      mem_baseSet_trivializationAt _ _ _⟩
    -- The forward input action and original map give a smooth moving-output column.
    let v (z : G × M) : EuclideanSpace ℂ (Fin q) :=
      (k ⟨z.1 • z.2, a.linearMap (z.1 • z.2)
        (σE.linearMap z.1 z.2 (e.symmL ℂ z.2 (EuclideanSpace.single j 1)))⟩).2
    have hv : ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞ v U := by
      have hsum : ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
          (fun z : G × M ↦ ∑ i : Fin r,
            (d ⟨z.1 • z.2, σE.linearMap z.1 z.2
              (e.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2 i •
            (k ⟨z.1 • z.2, a.linearMap (z.1 • z.2)
              (d.symmL ℂ (z.1 • z.2) (EuclideanSpace.single i 1))⟩).2) U := by
        apply contMDiffOn_finsetSum
        intro i _
        have hcoeff := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ).contMDiff
          |>.comp_contMDiffOn ((hσE e d j).mono (t := U) (fun z hz ↦ ⟨hz.1.1, hz.2.1⟩))
        have hcol := (ha d k i).comp (s := U)
          (contMDiff_smul (I := IG) (I' := I) (n := ∞)).contMDiffOn (fun z hz ↦ hz.2)
        have hsmul : ContDiff ℝ ∞
            (fun z : ℂ × EuclideanSpace ℂ (Fin q) ↦ z.1 • z.2) := contDiff_smul
        exact hsmul.contMDiff.comp_contMDiffOn (hcoeff.prodMk_space hcol)
      apply hsum.congr
      intro z hz
      let T := (k.linearMapAt ℂ (z.1 • z.2)).comp
        ((a.linearMap (z.1 • z.2)).comp (d.symmL ℂ (z.1 • z.2)).toLinearMap)
      have hmap := congrArg T ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr
        (d ⟨z.1 • z.2, σE.linearMap z.1 z.2
          (e.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2)
      simpa [v, T, map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, k.coe_linearMapAt_of_mem hz.2.2,
        d.symmL_apply hz.2.1, d.symm_apply_apply_mk hz.2.1] using hmap.symm
    -- The forward target action is a smooth invertible matrix in the exact chosen frames.
    let S (z : G × M) : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
      ((k.linearMapAt ℂ (z.1 • z.2)).comp ((σF.linearMap z.1 z.2).comp
        (f.symmL ℂ z.2).toLinearMap)).toContinuousLinearMap
    have hS : ContMDiffOn (IG.prod I)
        𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞ S U := by
      have hsum : ContMDiffOn (IG.prod I)
          𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          (fun z : G × M ↦ ∑ i : Fin q,
            ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin q))
              (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin q ↦ ℂ) i)
              ((k ⟨z.1 • z.2, σF.linearMap z.1 z.2
                (f.symmL ℂ z.2 (EuclideanSpace.single i 1))⟩).2)) U := by
        apply contMDiffOn_finsetSum
        intro i _
        exact ((ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin q))
          (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin q ↦ ℂ) i)).restrictScalars
            ℝ).contMDiff.comp_contMDiffOn
              ((hσF f k i).mono (fun z hz ↦ ⟨hz.1.2, hz.2.2⟩))
      apply hsum.congr
      intro z hz
      apply ContinuousLinearMap.ext
      intro w
      have hh := congrArg (S z) ((EuclideanSpace.basisFun (Fin q) ℂ).sum_repr w)
      simpa [S, map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, k.coe_linearMapAt_of_mem hz.2.2] using hh.symm
    let T (z : G × M) (hz : z ∈ U) :
        EuclideanSpace ℂ (Fin q) ≃L[ℂ] EuclideanSpace ℂ (Fin q) :=
      (((f.linearEquivAt ℂ z.2 hz.1.2).symm.trans (C z)).trans
        (k.linearEquivAt ℂ (z.1 • z.2) hz.2.2)).toContinuousLinearEquiv
    have hT (z : G × M) (hz : z ∈ U) : (T z hz).toContinuousLinearMap = S z := by
      apply ContinuousLinearMap.ext
      intro w
      simp [T, S, C, k.coe_linearMapAt_of_mem hz.2.2, f.symmL_apply hz.1.2,
        Bundle.Trivialization.linearEquivAt_symm_apply,
        Bundle.Trivialization.linearEquivAt_apply]
    have hinversion := (contDiffAt_map_inverse (n := ∞) (T p hpU)).restrict_scalars ℝ
    rw [hT p hpU] at hinversion
    have hinv := hinversion.comp_contMDiffAt (hS.contMDiffAt (hU.mem_nhds hpU))
    have happly : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          EuclideanSpace ℂ (Fin q) ↦ z.1 z.2) :=
      (isBoundedBilinearMap_apply (𝕜 := ℂ)).contDiff.restrict_scalars ℝ
    have hlocal := happly.comp_contMDiffAt
      (hinv.prodMk_space (hv.contMDiffAt (hU.mem_nhds hpU)))
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU.mem_nhds hpU] with z hz
    change Φ z = (S z).inverse (v z)
    rw [← hT z hz, ContinuousLinearMap.inverse_equiv]
    simp [T, Φ, Z, v, Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply, k.symm_apply_apply_mk hz.2.2]
  have heval (x : M) (hx : x ∈ e.baseSet ∩ f.baseSet) :
      (f ⟨x, (a.equivariantAverage σE σF).linearMap x
        (e.symmL ℂ x (EuclideanSpace.single j 1))⟩).2 = ∫ g, Φ (g, x) ∂μ := by
    let D := f.continuousLinearEquivAt ℂ x hx.2
    rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx.2, equivariantAverage_apply]
    rw [← f.coe_continuousLinearEquivAt_eq (R := ℂ) hx.2]
    change D (∫ g, L g x (e.symmL ℂ x (EuclideanSpace.single j 1)) ∂μ) = _
    rw [← D.integral_comp_comm]
    calc
      _ = ∫ g, Φ (g⁻¹, x) ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        change (f ⟨x, L g x (e.symmL ℂ x (EuclideanSpace.single j 1))⟩).2 = _
        rw [hreverse]
      _ = _ := integral_inv_eq_self (fun g ↦ Φ (g, x)) μ
  -- Compact-parameter differentiation now applies to the forward-action expression.
  intro x hx
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let s := c.target ∩ c.symm ⁻¹' (e.baseSet ∩ f.baseSet)
  have hs : IsOpen s := c.isOpen_inter_preimage_symm (e.open_baseSet.inter f.open_baseSet)
  have hcx : c x ∈ s := ⟨c.map_source (mem_chart_source _ x), by
    simpa only [Set.mem_preimage, c, OpenPartialHomeomorph.left_inv _ (mem_chart_source _ x)]
      using hx⟩
  have hchart : ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
      (fun z : G × EuclideanSpace ℝ (Fin n) ↦ Φ (z.1, c.symm z.2)) (Set.univ ×ˢ s) := by
    apply hΦ.comp
      (contMDiffOn_fst.prodMk ((contMDiffOn_chart_symm (I := I) (x := x)).comp
        contMDiffOn_snd (fun z hz ↦ hz.2.1)))
    intro z hz
    exact ⟨Set.mem_univ _, hz.2.2⟩
  have hint : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) ↦ ∫ g, Φ (g, c.symm y) ∂μ) s :=
    contDiffOn_integral_of_compact_manifold IG μ hs hchart
  have hlocal := (hint.contMDiffOn.contMDiffAt (hs.mem_nhds hcx)).comp x
    (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := I) x) (mem_chart_source _ x))
  apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x),
    (e.open_baseSet.inter f.open_baseSet).mem_nhds hx] with y hy hyf
  dsimp only [Function.comp_apply]
  rw [c.left_inv hy]
  exact heval y hyf

end AtiyahSinger.ComplexBundle.Hom

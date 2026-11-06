/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantBundleMapAverage

import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Continuous parameter families of original Haar-averaged bundle maps

Public module ID: M1176.

The same normalized Haar average varies jointly continuously with every external
parameter and original bundle vector. The parameter needs only a topology.
The result preserves total-space joint continuity of these families on the
original varying fibers. It is the parameterized form of the compact-group
averaging argument used in SG III.9.
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

/-- Haar averaging fixes an original bundle map intertwining the specified actions. -/
theorem equivariantAverage_eq_of_isEquivariant
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Hom E F)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.IsEquivariant σE σF) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    a.equivariantAverage σE σF = a := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : ∀ x, CompleteSpace (F x) := fun x ↦ FiniteDimensional.complete ℂ (F x)
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let μ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  apply Hom.ext
  intro x
  apply LinearMap.ext
  intro v
  rw [equivariantAverage_apply]
  -- The specified fiber square cancels the two group actions before integration.
  have hterm (g : G) : (smul_inv_smul g x) ▸
      (σF.linearMap g (g⁻¹ • x)
        (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))) = a.linearMap x v := by
    apply TotalSpace.mk_injective (F := Unit) x
    calc
      (⟨x, (smul_inv_smul g x) ▸ (σF.linearMap g (g⁻¹ • x)
        (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)))⟩ : TotalSpace Unit F) =
          g • (⟨g⁻¹ • x, a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)⟩ :
            TotalSpace Unit F) := by
              change (⟨x, (smul_inv_smul g x) ▸ (σF.linearMap g (g⁻¹ • x)
                (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)))⟩ : TotalSpace Unit F) =
                  ⟨g • (g⁻¹ • x), σF.linearMap g (g⁻¹ • x)
                    (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))⟩
              simpa only [eqRec_eq_cast] using (TotalSpace.mk_cast (F := Unit)
                (smul_inv_smul g x) (σF.linearMap g (g⁻¹ • x)
                  (a.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))))
      _ = g • (g⁻¹ • (⟨x, a.linearMap x v⟩ : TotalSpace Unit F)) := by
        rw [ha g⁻¹ x v]
        rfl
      _ = _ := smul_inv_smul g _
  change (∫ g : G, _ ∂μ) = _
  simp_rw [hterm]
  simp

/-- Compact Haar averaging preserves joint continuity of parameterized original bundle maps. -/
theorem continuous_equivariantAverage_family {Z : Type*} [TopologicalSpace Z]
    (a : Z → (letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Hom E F))
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Continuous (fun p : Z × TotalSpace Unit E ↦ (a p.1).totalMap p.2)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    Continuous (fun p : Z × TotalSpace Unit E ↦
      ((a p.1).equivariantAverage σE σF).totalMap p.2) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : ∀ x, CompleteSpace (F x) := fun x ↦ FiniteDimensional.complete ℂ (F x)
  let : MulAction G (TotalSpace Unit E) := σE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let Y := Z × TotalSpace Unit E
  -- Keep the free parameter throughout the same original total-space conjugation.
  let Ψ (p : G × Y) : TotalSpace Unit F :=
    p.1 • (a p.2.1).totalMap (p.1⁻¹ • p.2.2)
  have hΨ : Continuous Ψ := σF.continuous_action.comp
    (continuous_fst.prodMk (ha.comp ((continuous_fst.comp continuous_snd).prodMk
      (σE.continuous_action.comp (continuous_fst.inv.prodMk
        (continuous_snd.comp continuous_snd))))))
  let L (g : G) (y : Y) : F y.2.proj := (smul_inv_smul g y.2.proj) ▸
    (σF.linearMap g (g⁻¹ • y.2.proj)
      ((a y.1).linearMap (g⁻¹ • y.2.proj) (σE.linearMap g⁻¹ y.2.proj y.2.snd)))
  have hL (g : G) (y : Y) :
      (⟨y.2.proj, L g y⟩ : TotalSpace Unit F) = Ψ (g, y) := by
    change (⟨y.2.proj, L g y⟩ : TotalSpace Unit F) =
      ⟨g • (g⁻¹ • y.2.proj), σF.linearMap g (g⁻¹ • y.2.proj)
        ((a y.1).linearMap (g⁻¹ • y.2.proj) (σE.linearMap g⁻¹ y.2.proj y.2.snd))⟩
    simpa only [L, eqRec_eq_cast] using
      (TotalSpace.mk_cast (F := Unit) (smul_inv_smul g y.2.proj)
        (σF.linearMap g (g⁻¹ • y.2.proj)
          ((a y.1).linearMap (g⁻¹ • y.2.proj) (σE.linearMap g⁻¹ y.2.proj y.2.snd))))
  have hi (y : Y) : Integrable (fun g ↦ L g y) μ := by
    have hc : Continuous (fun g ↦ L g y) := by
      apply (FiberBundle.totalSpaceMk_isEmbedding (EuclideanSpace ℂ (Fin q)) F
        y.2.proj).continuous_iff.mpr
      have ht : Continuous (fun g ↦ (⟨y.2.proj, L g y⟩ : TotalSpace Unit F)) :=
        (hΨ.comp (continuous_id.prodMk continuous_const)).congr (fun g ↦ (hL g y).symm)
      exact (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp ht
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- A fixed output frame remains valid for all Haar parameters near the spatial point.
  apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
  apply continuous_iff_continuousAt.mpr
  intro y
  rw [FiberBundle.continuousAt_totalSpace]
  have hb : Continuous (fun y : Y ↦ y.2.proj) :=
    (continuous_model_proj (EuclideanSpace ℂ (Fin r)) E).comp continuous_snd
  refine ⟨hb.continuousAt, ?_⟩
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F y.2.proj
  let U : Set Y := {z | z.2.proj ∈ f.baseSet}
  have hU : IsOpen U := f.open_baseSet.preimage hb
  have hy : y ∈ U := mem_baseSet_trivializationAt _ _ _
  let Φ (p : G × Y) : EuclideanSpace ℂ (Fin q) :=
    (f (unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F (Ψ p))).2
  have hΦ : ContinuousOn Φ (Set.univ ×ˢ U) := by
    apply (f.continuousOn.comp
      (((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp hΨ).continuousOn)
      ?_).snd
    intro p hp
    apply f.mem_source.mpr
    change (Ψ p).proj ∈ f.baseSet
    have hbase : (Ψ p).proj = p.2.2.proj :=
      congrArg (fun t : TotalSpace Unit F ↦ t.proj) (hL p.1 p.2).symm
    rw [hbase]
    exact hp.2
  have hint : ContinuousOn (fun y : Y ↦ ∫ g, Φ (g, y) ∂μ) U :=
    continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
      (hΦ.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩)) (by simp)
  have heq (z : Y) (hz : z ∈ U) :
      (f ⟨z.2.proj, ((a z.1).equivariantAverage σE σF).linearMap z.2.proj z.2.snd⟩).2 =
        ∫ g, Φ (g, z) ∂μ := by
    rw [← f.continuousLinearMapAt_apply_of_mem ℂ hz, equivariantAverage_apply]
    change f.continuousLinearMapAt ℂ z.2.proj (∫ g, L g z ∂μ) = _
    rw [← (f.continuousLinearMapAt ℂ z.2.proj).integral_comp_comm (hi z)]
    apply integral_congr_ae
    filter_upwards with g
    rw [f.continuousLinearMapAt_apply_of_mem ℂ hz]
    exact congrArg (fun t : TotalSpace Unit F ↦
      (f (unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F t)).2) (hL g z)
  exact (hint.continuousAt (hU.mem_nhds hy)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz ↦ heq z hz))

end AtiyahSinger.ComplexBundle.Hom

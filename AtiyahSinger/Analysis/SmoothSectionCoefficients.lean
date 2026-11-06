/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.HermitianMetricL2

import AtiyahSinger.Geometry.SmoothInvariantMetric
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous integral coefficients of geometric section actions

Public module ID: M0978.

Pairing a fixed smooth section with the original geometric orbit is continuous
for any of the original smooth Hermitian metrics and positive densities on a
compact base. Compact-base currying and bounded integration suffice; neither
the metric nor the density needs to be invariant. These coefficients construct
the finite continuous representations on the actual smooth kernel and cokernel.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothHermitianMetric

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  [MeasurableSpace M] [BorelSpace M] (μ : Measure M)
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)

include hM hT2 hSC hC hE hμ hG hAction in
/-- Integral matrix coefficients of the actual smooth action are continuous. -/
theorem continuous_sectionPairing_smoothSectionRepresentation
    (u v : smoothSections (n := n) (r := r) E) :
    Continuous (fun g : G ↦ h.sectionPairing μ v
      (σ.smoothSectionRepresentation IG hσ g u)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let : TopologicalSpace (TotalSpace Unit (E ×ᵇ E)) := sumTopology
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let R := σ.smoothSectionRepresentation IG hσ
  -- Smooth original sections give continuous total-space maps in the original topology.
  have hsection (w : smoothSections (n := n) (r := r) E) :
      Continuous (fun x : M ↦ (⟨x, w.val x⟩ : TotalSpace Unit E)) := by
    apply (continuous_model_section_iff (EuclideanSpace ℂ (Fin r)) E w.val).mpr
    rw [continuous_iff_continuousAt]
    intro x
    apply (FiberBundle.continuousAt_section (EuclideanSpace ℂ (Fin r)) x).mpr
    exact (w.property (trivializationAt (EuclideanSpace ℂ (Fin r)) E x)
      inferInstance).continuousOn.continuousAt
        ((trivializationAt (EuclideanSpace ℂ (Fin r)) E x).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x))
  have horbit : Continuous (fun p : G × M ↦
      (⟨p.2, (R p.1 u).val p.2⟩ : TotalSpace Unit E)) := by
    have hsource : Continuous (fun p : G × M ↦
        (p.1, (⟨p.1⁻¹ • p.2, u.val (p.1⁻¹ • p.2)⟩ : TotalSpace Unit E))) :=
      continuous_fst.prodMk ((hsection u).comp (continuous_fst.inv.smul continuous_snd))
    apply (σ.continuous_action.comp hsource).congr
    intro p
    exact (σ.mk_sectionLinearMap p.1 u.val p.2).symm
  have hpair : Continuous (fun p : G × M ↦
      h.pairing p.2 (v.val p.2) ((R p.1 u).val p.2)) := by
    have hdouble : Continuous (fun p : G × M ↦
        (⟨p.2, (v.val p.2, (R p.1 u).val p.2)⟩ : TotalSpace Unit (E ×ᵇ E))) := by
      apply continuous_induced_rng.mpr
      exact ((hsection v).comp continuous_snd).prodMk horbit
    exact h.continuous_totalPairing.comp hdouble
  -- The same finite measure gives bounded integration on continuous functions.
  have hintegrable (f : C(M, ℂ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let integralMap : C(M, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ x, f x ∂μ
      map_add' := fun f k ↦ integral_add (hintegrable f) (hintegrable k)
      map_smul' := fun c f ↦ integral_smul c f }
  have hbound (f : C(M, ℂ)) : ‖integralMap f‖ ≤ μ.real Set.univ * ‖f‖ := by
    change ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖
    simpa only [mul_comm] using norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall f.norm_coe_le_norm)
  let integralCLM : C(M, ℂ) →L[ℂ] ℂ := integralMap.mkContinuous (μ.real Set.univ) hbound
  let f : G → C(M, ℂ) := fun g ↦
    ⟨fun x ↦ h.pairing x (v.val x) ((R g u).val x),
      hpair.comp (continuous_const.prodMk continuous_id)⟩
  have hf : Continuous f := ContinuousMap.continuous_of_continuous_uncurry f hpair
  exact integralCLM.continuous.comp hf

end AtiyahSinger.SmoothHermitianMetric

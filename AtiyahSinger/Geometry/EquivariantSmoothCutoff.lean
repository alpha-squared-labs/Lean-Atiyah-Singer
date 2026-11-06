/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactParameterIntegral
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Smooth invariant cutoffs inside a prescribed compact window

Public module ID: M1205.

An invariant compact subset of the interior of a second invariant compact set
admits a smooth invariant cutoff with values in the unit interval. Normalized
Haar averaging retains the specified sets and exact values. No compactness of
the ambient manifold or finite CW model is required. This is the localization
step needed to average a relative elliptic realization without moving its
compact support outside the prescribed common open manifold.

Source: the compact-group averaging argument underlying Atiyah--Singer I B1.
The smooth cutoff before averaging is mathlib's manifold Urysohn lemma.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Set Filter MeasureTheory TopologicalSpace Topology
open scoped ContDiff

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [hLie : LieGroup 𝓘(ℝ, VG) ∞ G] [hGC : CompactSpace G]
  [MeasurableSpace G] [hGB : BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MulAction G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ G M]

include hLie hGC hGB hAction

set_option maxHeartbeats 1000000 in
-- Check smooth compact-parameter integration in the original manifold charts.
/-- Averaging a smooth cutoff preserves both specified invariant compact sets. -/
theorem exists_invariant_smooth_cutoff (K L : Set M) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ interior L)
    (hKi : ∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K)
    (hLi : ∀ (g : G) (x : M), g • x ∈ L ↔ x ∈ L) :
    ∃ φ : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), M; 𝓘(ℝ), ℝ⟯,
      EqOn φ 1 K ∧ tsupport φ ⊆ L ∧ (∀ x : M, φ x ∈ Icc 0 1) ∧
        ∀ (g : G) (x : M), φ (g • x) = φ x := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨ψ, hψone, hψzero, hψrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hK.isClosed hKL (n := ⊤)
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  have hμ : μ.real univ = 1 := by
    change (Measure.haarMeasure (⊤ : PositiveCompacts G)
      (⊤ : PositiveCompacts G)).toReal = 1
    rw [Measure.haarMeasure_self, ENNReal.toReal_one]
  let R (g : G) (x : M) : ℝ := ψ (g⁻¹ • x)
  have hR : ContMDiff (𝓘(ℝ, VG).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) 𝓘(ℝ) ∞
      (fun p : G × M ↦ R p.1 p.2) :=
    ψ.property.comp (((contMDiff_inv 𝓘(ℝ, VG) ∞).comp contMDiff_fst).smul contMDiff_snd)
  have hRI (x : M) : Integrable (fun g : G ↦ R g x) μ :=
    (hR.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let φ (x : M) : ℝ := ∫ g : G, R g x ∂μ
  -- Differentiate only the base variable, using compactness of the original group parameter.
  have hφ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ) ∞ φ := by
    intro x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hchart : ContMDiffOn (𝓘(ℝ, VG).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) 𝓘(ℝ) ∞
        (fun p : G × EuclideanSpace ℝ (Fin n) ↦ R p.1 (c.symm p.2))
        (univ ×ˢ c.target) :=
      hR.comp_contMDiffOn (contMDiffOn_fst.prodMk
        ((contMDiffOn_chart_symm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (x := x)).comp
          contMDiffOn_snd
          (fun _ hp ↦ hp.2)))
    have hi := contDiffOn_integral_of_compact_manifold 𝓘(ℝ, VG) μ c.open_target hchart
    have hx := c.map_source (mem_chart_source _ x)
    have hl := (hi.contMDiffOn.contMDiffAt (c.open_target.mem_nhds hx)).comp x
      (contMDiffAt_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x)
        (mem_chart_source _ x))
    apply hl.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x)] with y hy
    dsimp only [Function.comp_apply, φ]
    rw [c.left_inv hy]
  have hφone (x : M) (hx : x ∈ K) : φ x = 1 := by
    have hone (g : G) : R g x = 1 :=
      hψone.self_of_nhdsSet _ ((hKi g⁻¹ x).mpr hx)
    simp only [φ, hone, integral_const, hμ, one_smul]
  have hφzero (x : M) (hx : x ∉ L) : φ x = 0 := by
    have hzero (g : G) : R g x = 0 :=
      hψzero _ (fun h ↦ hx ((hLi g⁻¹ x).mp h))
    simp only [φ, hzero, integral_zero]
  refine ⟨⟨φ, hφ⟩, hφone, ?_, ?_, ?_⟩
  · -- The entire closed support remains inside the prescribed compact window.
    apply closure_minimal ?_ hL.isClosed
    intro x hx
    by_contra hxL
    exact hx (hφzero x hxL)
  · intro x
    constructor
    · exact integral_nonneg (fun g ↦ (hψrange (g⁻¹ • x)).1)
    · change φ x ≤ 1
      have hle := integral_mono (hRI x) (integrable_const (1 : ℝ))
        (fun g ↦ (hψrange (g⁻¹ • x)).2)
      simpa only [φ, integral_const, hμ, one_smul] using hle
  · -- Left translation reindexes the original normalized Haar average.
    intro g x
    change (∫ a : G, R a (g • x) ∂μ) = ∫ a : G, R a x ∂μ
    rw [← integral_mul_left_eq_self (μ := μ) (fun a ↦ R a (g • x)) g]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun a ↦ by
      simp only [R, mul_inv_rev, mul_smul, inv_smul_smul])

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianPairing

/-!
# Restricting a smooth positive density to an open submanifold

Public module ID: M1317.

D02/A10: the measure on U is the actual subtype comap, not the measure
restricted to U while still living on M. In the inherited charts its positive
smooth density is the restriction of the ambient coordinate density.
This is a standard local consequence of the density definition; no compactness,
orientation or connectedness is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [MeasurableSpace M] [BorelSpace M]

/-- Subtype restriction preserves a positive smooth density in the inherited manifold atlas. -/
theorem isSmoothPositiveMeasure_comap_opens (μ : Measure M)
    [hμ : IsSmoothPositiveMeasure (n := n) μ] (U : Opens M) :
    IsSmoothPositiveMeasure (n := n) (μ.comap (Subtype.val : U → M)) := by
  classical
  -- Every inherited chart is the restriction of an actual ambient chart.
  constructor
  intro c hc
  rcases hc with ⟨_, ⟨x, rfl⟩, hc⟩
  obtain rfl := Set.mem_singleton_iff.mp hc
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x.val
  let d := e.subtypeRestr (s := U) ⟨x⟩
  obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density e (chart_mem_atlas _ x.val)
  refine ⟨w, hw.mono (e.subtypeRestr_target_subset ⟨x⟩),
    fun z hz ↦ hwpos z (e.subtypeRestr_target_subset ⟨x⟩ hz), ?_⟩
  -- Compare the actual subtype comap on each measurable coordinate set.
  have hpush : Measure.map d ((μ.comap (Subtype.val : U → M)).restrict d.source) =
      (Measure.map e (μ.restrict e.source)).restrict d.target := by
    apply Measure.ext
    intro t ht
    have hcomap := (MeasurableEmbedding.subtype_coe
      (s := (U : Set M)) U.isOpen.measurableSet).comap_apply μ (d ⁻¹' t ∩ d.source)
    rw [Measure.map_apply_of_aemeasurable
      (d.continuousOn.aemeasurable d.open_source.measurableSet) ht,
      Measure.restrict_apply' d.open_source.measurableSet]
    erw [hcomap]
    rw [Measure.restrict_apply ht,
      Measure.map_apply_of_aemeasurable
        (e.continuousOn.aemeasurable e.open_source.measurableSet)
        (ht.inter d.open_target.measurableSet),
      Measure.restrict_apply' e.open_source.measurableSet]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨hz, hzs⟩, rfl⟩
      exact ⟨⟨hz, d.map_source hzs⟩, by simpa [d] using hzs⟩
    · rintro ⟨⟨hyt, hyd⟩, hys⟩
      have hyU : y ∈ U := by
        have hval : (d.symm (e y)).val = y := by
          exact (e.subtypeRestr_symm_apply ⟨x⟩ hyd).trans
            (e.left_inv hys)
        exact hval ▸ (d.symm (e y)).property
      exact ⟨⟨y, hyU⟩, ⟨hyt, by simpa [d] using hys⟩, rfl⟩
  -- Restrict the same ambient density to the smaller inherited chart target.
  change Measure.map d _ = _
  rw [hpush, hmap, restrict_withDensity d.open_target.measurableSet,
    Measure.restrict_restrict_of_subset (e.subtypeRestr_target_subset ⟨x⟩)]

end AtiyahSinger

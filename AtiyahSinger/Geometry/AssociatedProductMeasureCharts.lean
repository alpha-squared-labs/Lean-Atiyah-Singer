/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedProductMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.PartialHomeomorph.Basic

/-!
# The associated product measure in the original principal charts

Public module ID: M1063.

The actual Riesz measure restricts in every original associated principal
chart to the product of the specified base and invariant fiber measures.
Test functions on the chart target are pulled back through that same chart
and extended by zero. Compact support makes these extensions continuous,
so the already proved whole-fiber Fubini formula identifies the measures.
This is a local measure identity, before introducing any smooth density.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Topology
open scoped CompactlySupported

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [T2Space Y]
  [SecondCountableTopology Y]
  [MeasurableSpace B] [BorelSpace B] [CompactSpace B] [T2Space B]
  [SecondCountableTopology B]
  (hP : IsPrincipalBundle G projection) (μ : Measure B) (ν : Measure Y)
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
  [MeasurableSpace (AssociatedBundle G P Y)] [BorelSpace (AssociatedBundle G P Y)]
  [T2Space (AssociatedBundle G P Y)] [CompactSpace (AssociatedBundle G P Y)]

local notation "Z" => AssociatedBundle G P Y

/-- In each original associated chart the actual measure is the specified product measure. -/
theorem associatedProductMeasure_comap_trivialization
    (e : Trivialization G projection)
    (t : Trivialization Y (associatedBundleProjection (F := Y) hP))
    (hbase : t.baseSet = e.baseSet)
    (hinv : ∀ (b : B) (y : Y), b ∈ e.baseSet →
      t.toOpenPartialHomeomorph.symm (b, y) =
        associatedBundleMk G P Y (e.toOpenPartialHomeomorph.symm (b, 1)) y) :
    (associatedProductMeasure hP μ ν hν).comap
        (fun w : t.target ↦ t.toOpenPartialHomeomorph.symm w.val) =
      (μ.prod ν).comap (Subtype.val : t.target → B × Y) := by
  classical
  let η := associatedProductMeasure hP μ ν hν
  let : Measure.Regular η :=
    inferInstanceAs (Measure.Regular (RealRMK.rieszMeasure
      (associatedProductIntegral hP μ ν hν)))
  let : LocallyCompactSpace t.target := t.open_target.locallyCompactSpace
  let H := t.toOpenPartialHomeomorph.toHomeomorphSourceTarget
  let j (w : t.target) : Z := t.toOpenPartialHomeomorph.symm w.val
  have hj : IsOpenEmbedding j :=
    t.open_source.isOpenEmbedding_subtypeVal.comp H.symm.isOpenEmbedding
  have hrange : Set.range j = t.source := by
    apply Set.ext
    intro z
    constructor
    · rintro ⟨w, rfl⟩
      exact t.toOpenPartialHomeomorph.map_target w.property
    · intro hz
      exact ⟨H ⟨z, hz⟩, t.toOpenPartialHomeomorph.left_inv hz⟩
  let : Measure.Regular (η.comap j) := Measure.Regular.comap' η hj
  let : Measure.Regular ((μ.prod ν).comap (Subtype.val : t.target → B × Y)) :=
    Measure.Regular.comap' (μ.prod ν) t.open_target.isOpenEmbedding_subtypeVal
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  -- The same compactly supported test function extends continuously on both original spaces.
  let g (z : t.source) : ℝ := f (H z)
  have hg : Continuous g := f.continuous.comp H.continuous
  have hgs : HasCompactSupport g := f.hasCompactSupport.comp_homeomorph H
  let F : C(Z, ℝ) := ⟨Subtype.val.extend g 0,
    HasCompactSupport.continuous_extend_zero t.open_source hg hgs⟩
  let f₀ : C(B × Y, ℝ) := ⟨Subtype.val.extend f 0,
    HasCompactSupport.continuous_extend_zero t.open_target f.continuous f.hasCompactSupport⟩
  have hF (z : t.source) : F z.val = f (H z) :=
    Subtype.val_injective.extend_apply g 0 z
  have hf₀ (w : t.target) : f₀ w.val = f w :=
    Subtype.val_injective.extend_apply f 0 w
  have hFzero (z : Z) (hz : z ∉ t.source) : F z = 0 := by
    exact Function.extend_apply' (f := (Subtype.val : t.source → Z)) g 0 z (by simpa using hz)
  have hf₀zero (w : B × Y) (hw : w ∉ t.target) : f₀ w = 0 := by
    exact Function.extend_apply' (f := (Subtype.val : t.target → B × Y)) f 0 w (by simpa using hw)
  have hFj (w : t.target) : F (j w) = f w := by
    have h := hF (H.symm w)
    change F (j w) = f (H (H.symm w)) at h
    exact h.trans (congrArg f (H.apply_symm_apply w))
  -- The local section only enters inside its original base set; outside it both tests vanish.
  have hfiber (b : B) : associatedFiberIntegral hP ν F b = ∫ y, f₀ (b, y) ∂ν := by
    by_cases hb : b ∈ e.baseSet
    · let p := e.toOpenPartialHomeomorph.symm (b, 1)
      have hp : projection p = b := e.proj_symm_apply' hb
      rw [← hp, associatedFiberIntegral_apply hP ν hν F, hp]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      have ht : (b, y) ∈ t.target := t.mem_target.mpr (hbase.symm ▸ hb)
      change F (associatedBundleMk G P Y
        (e.toOpenPartialHomeomorph.symm (b, 1)) y) = f₀ (b, y)
      rw [← hinv b y hb]
      exact (hFj ⟨(b, y), ht⟩).trans (hf₀ ⟨(b, y), ht⟩).symm
    · have hleft : associatedFiberIntegral hP ν F b = 0 := by
        unfold associatedFiberIntegral
        apply integral_eq_zero_of_ae
        apply Filter.Eventually.of_forall
        intro y
        apply hFzero
        rw [t.mem_source, hbase]
        change projection ((hP.projection_properties.2.2 b).choose) ∉ e.baseSet
        simpa only [(hP.projection_properties.2.2 b).choose_spec] using hb
      rw [hleft]
      symm
      apply integral_eq_zero_of_ae
      apply Filter.Eventually.of_forall
      intro y
      exact hf₀zero (b, y) (by simpa only [t.mem_target, hbase] using hb)
  -- Pullback by the actual inverse chart integrates the zero extension over its source.
  have hleft : (∫ w, f w ∂η.comap j) = ∫ z, F z ∂η := by
    calc
      (∫ w, f w ∂η.comap j) = ∫ w, F (j w) ∂η.comap j := by
        simp only [hFj]
      _ = ∫ z, F z ∂Measure.map j (η.comap j) :=
        (hj.measurableEmbedding.integral_map F).symm
      _ = ∫ z in t.source, F z ∂η := by
        rw [hj.measurableEmbedding.map_comap, hrange]
      _ = ∫ z, F z ∂η := setIntegral_eq_integral_of_forall_compl_eq_zero hFzero
  have hright : (∫ w, f w ∂(μ.prod ν).comap (Subtype.val : t.target → B × Y)) =
      ∫ w, f₀ w ∂μ.prod ν := by
    calc
      (∫ w, f w ∂(μ.prod ν).comap (Subtype.val : t.target → B × Y)) =
          ∫ w : t.target, f₀ w.val ∂(μ.prod ν).comap Subtype.val := by
        simp only [hf₀]
      _ = ∫ w in t.target, f₀ w ∂μ.prod ν :=
        integral_subtype_comap t.open_target.measurableSet f₀
      _ = ∫ w, f₀ w ∂μ.prod ν := setIntegral_eq_integral_of_forall_compl_eq_zero hf₀zero
  rw [hleft, hright, integral_associatedProductMeasure hP μ ν hν F]
  have hi : Integrable f₀ (μ.prod ν) :=
    f₀.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_prod f₀ hi]
  exact integral_congr_ae (Filter.Eventually.of_forall hfiber)

end AtiyahSinger

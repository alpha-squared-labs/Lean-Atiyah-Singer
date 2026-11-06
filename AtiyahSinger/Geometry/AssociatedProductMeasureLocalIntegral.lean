/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedProductMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The local integral in an original principal chart

Public module ID: M1064.

A continuous function supported above one principal chart integrates against
the actual associated product measure by first integrating on the base in
that chart and then on the original invariant fiber. The normalized chart
pullback, extended by zero, is measurable and bounded on the finite product
measure; Fubini therefore permits the required reversal of integration.

No global measurable principal section is selected. This is the local
integration formula needed for complete horizontal formal adjoints.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Topology
open scoped CompactlySupported

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [SecondCountableTopology Y]
  [MeasurableSpace B] [BorelSpace B] [CompactSpace B]
  [SecondCountableTopology B]
  (hP : IsPrincipalBundle G projection) (μ : Measure B) (ν : Measure Y)
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
  [MeasurableSpace (AssociatedBundle G P Y)] [BorelSpace (AssociatedBundle G P Y)]
  [T2Space (AssociatedBundle G P Y)] [CompactSpace (AssociatedBundle G P Y)]

local notation "Z" => AssociatedBundle G P Y

open scoped Classical in
/-- A function supported over one chart has exactly its base integral inside the fiber integral. -/
theorem integral_associatedProductMeasure_principal_chart
    (e : Trivialization G projection) (f : C(Z, ℂ))
    (hf : ∀ z : Z, associatedBundleProjection (F := Y) hP z ∉ e.baseSet → f z = 0) :
    (∫ z, f z ∂associatedProductMeasure hP μ ν hν) =
      ∫ y, ∫ b, if b ∈ e.baseSet then
        f (associatedBundleMk G P Y (e.toOpenPartialHomeomorph.symm (b, 1)) y)
      else 0 ∂μ ∂ν := by
  classical
  let U : Set (B × Y) := e.baseSet ×ˢ Set.univ
  let g₀ (z : B × Y) : ℂ :=
    f (associatedBundleMk G P Y (e.toOpenPartialHomeomorph.symm (z.1, 1)) z.2)
  let g (z : B × Y) : ℂ := if z.1 ∈ e.baseSet then g₀ z else 0
  -- Continuity only inside the original chart suffices for measurable extension by zero.
  have hg₀ : ContinuousOn g₀ U := by
    have hp : ContinuousOn (fun z : B × Y ↦ e.toOpenPartialHomeomorph.symm (z.1, 1)) U :=
      e.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_fst.prodMk continuous_const).continuousOn
        (fun z hz ↦ e.mem_target.mpr hz.1)
    exact f.continuous.comp_continuousOn
      (continuous_quot_mk.comp_continuousOn (hp.prodMk continuousOn_snd))
  have hmeas : Measurable g := by
    have h := hg₀.measurable_piecewise (g := fun _ ↦ (0 : ℂ)) continuousOn_const
      (e.open_baseSet.measurableSet.prod MeasurableSet.univ)
    convert h using 1
    funext z
    by_cases hz : z.1 ∈ e.baseSet
    · simp [g, U, hz]
    · simp [g, U, hz]
  have hbound (z : B × Y) : ‖g z‖ ≤ ‖f‖ := by
    by_cases hz : z.1 ∈ e.baseSet
    · simpa only [g, hz, ↓reduceIte] using f.norm_coe_le_norm
        (associatedBundleMk G P Y (e.toOpenPartialHomeomorph.symm (z.1, 1)) z.2)
    · simp only [g, hz, ↓reduceIte, norm_zero, norm_nonneg]
  have hi : Integrable g (μ.prod ν) :=
    (integrable_const (‖f‖ : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  -- Whole-fiber invariance identifies the same normalized representative wherever it exists.
  have hlocal (b : B) : associatedFiberIntegral hP ν f b = ∫ y, g (b, y) ∂ν := by
    by_cases hb : b ∈ e.baseSet
    · let p := e.toOpenPartialHomeomorph.symm (b, 1)
      have hp : projection p = b := e.proj_symm_apply' hb
      rw [← hp, associatedFiberIntegral_apply hP ν hν f, hp]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y ↦ by simp only [g, hb, ↓reduceIte]; rfl)
    · have hz : associatedFiberIntegral hP ν f b = 0 := by
        unfold associatedFiberIntegral
        apply integral_eq_zero_of_ae
        apply Filter.Eventually.of_forall
        intro y
        apply hf
        change projection ((hP.projection_properties.2.2 b).choose) ∉ e.baseSet
        simpa only [(hP.projection_properties.2.2 b).choose_spec] using hb
      rw [hz]
      simp only [g, hb, ↓reduceIte, integral_zero]
  rw [integral_associatedProductMeasure_complex hP μ ν hν f]
  calc
    (∫ b, associatedFiberIntegral hP ν f b ∂μ) = ∫ b, ∫ y, g (b, y) ∂ν ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hlocal)
    _ = ∫ y, ∫ b, g (b, y) ∂μ ∂ν := integral_integral_swap hi

end AtiyahSinger

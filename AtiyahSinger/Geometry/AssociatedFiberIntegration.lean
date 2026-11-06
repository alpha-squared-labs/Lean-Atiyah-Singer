/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundle
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration over the whole fibers of an associated bundle

Public module ID: M1059.

Integrating a continuous function against the specified invariant compact
fiber measure gives a continuous function on the original base. The value
uses any original principal representative. Representative choices are only
used to define the function; continuity follows in each original principal
chart and does not assume a continuous or measurable global principal section.

This is the fiber integration input for constructing the associated product
density and its actual Fubini identity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (hP : IsPrincipalBundle G projection) (ν : Measure Y)
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Integrate over the original fiber at one actual principal representative of the base point. -/
def associatedFiberIntegral (f : C(AssociatedBundle G P Y, V)) (b : B) : V :=
  ∫ y, f (associatedBundleMk G P Y ((hP.projection_properties.2.2 b).choose) y) ∂ν

/-- Invariance gives the same integral at every original principal representative. -/
theorem associatedFiberIntegral_apply
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (f : C(AssociatedBundle G P Y, V)) (p : P) :
    associatedFiberIntegral hP ν f (projection p) =
      ∫ y, f (associatedBundleMk G P Y p y) ∂ν := by
  let p₀ := (hP.projection_properties.2.2 (projection p)).choose
  have hp₀ : projection p₀ = projection p :=
    (hP.projection_properties.2.2 (projection p)).choose_spec
  obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p p₀ hp₀.symm
  change (∫ y, f (associatedBundleMk G P Y p₀ y) ∂ν) = _
  -- The original quotient convention acts on the full fiber by exactly this group element.
  rw [← hg]
  simp_rw [associatedBundleMk_smul]
  have hmap := integral_map_equiv (μ := ν) (MeasurableEquiv.smul g)
    (fun y ↦ f (associatedBundleMk G P Y p y))
  rw [show Measure.map (MeasurableEquiv.smul g) ν = ν from hν g] at hmap
  exact hmap.symm

variable [CompactSpace Y] [IsFiniteMeasure ν]

/-- Integration over the complete compact fiber varies continuously on the original base. -/
theorem continuous_associatedFiberIntegral
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (f : C(AssociatedBundle G P Y, V)) : Continuous (associatedFiberIntegral hP ν f) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  obtain ⟨e, hb, _⟩ := hP.exists_trivialization b
  let p (x : B) : P := e.toOpenPartialHomeomorph.symm (x, 1)
  have hp : ContinuousOn p e.baseSet :=
    e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx ↦ e.mem_target.mpr hx)
  have hfamily : ContinuousOn
      (fun z : B × Y ↦ f (associatedBundleMk G P Y (p z.1) z.2))
      (e.baseSet ×ˢ Set.univ) := by
    apply f.continuous.comp_continuousOn
    apply continuous_quot_mk.comp_continuousOn
    exact (hp.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)).prodMk
      continuous_snd.continuousOn
  -- One original local principal section suffices; compact fiber integration preserves continuity.
  have hi : ContinuousOn (fun x : B ↦ ∫ y, f (associatedBundleMk G P Y (p x) y) ∂ν)
      e.baseSet := continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
        hfamily (by simp)
  have heq (x : B) (hx : x ∈ e.baseSet) :
      (∫ y, f (associatedBundleMk G P Y (p x) y) ∂ν) = associatedFiberIntegral hP ν f x := by
    have h := associatedFiberIntegral_apply hP ν hν f (p x)
    have hpx : projection (p x) = x := e.proj_symm_apply' hx
    rw [hpx] at h
    exact h.symm
  exact (hi.congr (fun x hx ↦ (heq x hx).symm)).continuousAt (e.open_baseSet.mem_nhds hb)

end AtiyahSinger

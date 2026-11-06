/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleRescaling

/-!
# Transfer of rescaling continuity through an actual bundle chart

Public module ID: M1113.

A fiber-saturated chart commuting with scalar dilation identifies coordinate
rescaling with rescaling in the original vector bundle. Joint continuity at
zero scale therefore transfers from the coordinate expression to the native
total-space map. The map need only be continuous at the zero vector; its
coordinate continuity can come from smooth geometry and continuous coefficients.

The chart remains specified, which permits the product frame used in nested
tubular geometry. No smoothness of the full transported map is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology

variable {B F EB G : Type*} [TopologicalSpace B] [TopologicalSpace EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Coordinate rescaling continuity transfers through the same dilation-compatible chart. -/
theorem continuousAt_rescaleBundleMap_of_chart
    (f : TotalSpace F V → TotalSpace F V)
    (c : OpenPartialHomeomorph (TotalSpace F V) (EB × G))
    (hsource : ∀ (t : ℝ) (w : TotalSpace F V),
      bundleFiberScale t w ∈ c.source ↔ w ∈ c.source)
    (hscale : ∀ (t : ℝ) (w : TotalSpace F V), w ∈ c.source →
      c (bundleFiberScale t w) = ((c w).1, t • (c w).2))
    (x : B) (v : V x)
    (hc₀ : (⟨x, 0⟩ : TotalSpace F V) ∈ c.source)
    (hf : ContinuousAt f (⟨x, 0⟩ : TotalSpace F V))
    (hzero : f ⟨x, 0⟩ = ⟨x, 0⟩)
    (hchart : ContinuousAt (rescaleAlongFibers (c ∘ f ∘ c.symm))
      (0, c (⟨x, v⟩ : TotalSpace F V))) :
    ContinuousAt (rescaleBundleMap f) (0, (⟨x, v⟩ : TotalSpace F V)) := by
  let z : TotalSpace F V := ⟨x, v⟩
  have hcz : z ∈ c.source := (hsource 0 z).mp (by
    simpa only [bundleFiberScale, zero_smul, z] using hc₀)
  -- Coordinate rescaling tends to the same vector, so the original inverse chart applies.
  have hcoordinates : ContinuousAt (fun p : ℝ × TotalSpace F V ↦ (p.1, c p.2)) (0, z) :=
    continuous_fst.continuousAt.prodMk
      ((c.continuousAt hcz).comp_of_eq continuous_snd.continuousAt rfl)
  have hcrescale := hchart.comp_of_eq hcoordinates rfl
  have hback := (c.continuousAt_symm (c.map_source hcz)).comp_of_eq hcrescale
    (by simp only [Function.comp_apply, rescaleAlongFibers, ↓reduceIte])
  have hinput : ContinuousAt
      (fun p : ℝ × TotalSpace F V ↦ bundleFiberScale p.1 p.2) (0, z) :=
    continuous_bundleFiberScale_of_vectorBundle.continuousAt
  have hfinput : ContinuousAt
      (fun p : ℝ × TotalSpace F V ↦ f (bundleFiberScale p.1 p.2)) (0, z) :=
    hf.comp_of_eq hinput (by simp only [bundleFiberScale, zero_smul, z])
  -- In a sufficiently small neighborhood, both dilations use this same original chart.
  apply hback.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt (c.open_source.mem_nhds hcz),
    hfinput (by simpa only [bundleFiberScale, zero_smul, z, hzero] using
      c.open_source.mem_nhds hc₀)] with p hp hfp
  by_cases ht : p.1 = 0
  · simp only [Function.comp_apply, rescaleBundleMap, rescaleAlongFibers, ht, ↓reduceIte]
    exact (c.left_inv hp).symm
  · have hd := (hsource p.1 p.2).mpr hp
    have hds := c.left_inv hd
    have hcscale := hscale p.1 p.2 hp
    simp only [rescaleBundleMap, ht, ↓reduceIte, Function.comp_apply]
    change bundleFiberScale p.1⁻¹ (f (bundleFiberScale p.1 p.2)) =
      c.symm (rescaleAlongFibers (c ∘ f ∘ c.symm) (p.1, c p.2))
    rw [rescaleAlongFibers, ite_eq_right ht]
    change _ = c.symm (((c ∘ f ∘ c.symm) ((c p.2).1, p.1 • (c p.2).2)).1,
      p.1⁻¹ • ((c ∘ f ∘ c.symm) ((c p.2).1, p.1 • (c p.2).2)).2)
    rw [← hcscale]
    simp only [Function.comp_apply, hds]
    rw [← hscale p.1⁻¹ _ hfp]
    exact (c.left_inv ((hsource _ _).mpr hfp)).symm

end AtiyahSinger

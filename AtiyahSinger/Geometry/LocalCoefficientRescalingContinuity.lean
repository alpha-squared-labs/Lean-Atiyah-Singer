/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.LocalCoefficientRescaling

/-!
# Joint rescaling continuity for smooth geometry and continuous coefficients

Public module ID: M1293.

A normalized smooth map can be composed on either side with the actual
continuous coefficient shear. Both compositions have jointly continuous
rescaling at zero. The smooth map is only required on an open neighborhood;
a local rectangle supplies the radial domain for Hadamard's formula.

The two orders are needed for a nested tube and its inverse. The original
coefficient family and the prescribed zero value are retained throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology
open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- Smooth normalized geometry and continuous normalized coefficients rescale in either order. -/
theorem continuousAt_rescaleAlongFibers_coefficient_comp
    (A : E × F → G ≃L[ℝ] G) (S : Set (E × F)) (hS : IsOpen S)
    (hA : ContinuousOn (fun p : (E × F) × G ↦ A p.1 p.2) (S ×ˢ univ))
    (hAi : ContinuousOn (fun p : (E × F) × G ↦ (A p.1).symm p.2) (S ×ˢ univ))
    (hzero : ∀ x : E, (x, (0 : F)) ∈ S → A (x, 0) = ContinuousLinearEquiv.refl ℝ G)
    (g : E × (F × G) → E × (F × G)) {U : Set (E × (F × G))}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (hgzero : ∀ x : E, (x, (0 : F × G)) ∈ U → g (x, 0) = (x, 0))
    (x : E) (v : F) (w : G) (hx : (x, (0 : F)) ∈ S) (hxU : (x, (0 : F × G)) ∈ U)
    (hnormal : (fderiv ℝ (fun z ↦ (g z).2) (x, 0)).comp
      (ContinuousLinearMap.inr ℝ E (F × G)) = ContinuousLinearMap.id ℝ (F × G)) :
    ContinuousAt (rescaleAlongFibers (g ∘ continuousCoefficientShear A S hS hA hAi))
        (0, x, v, w) ∧
      ContinuousAt (rescaleAlongFibers (continuousCoefficientShear A S hS hA hAi ∘ g))
        (0, x, v, w) := by
  let C := continuousCoefficientShear A S hS hA hAi
  let J := continuousCoefficientShearCylinder A S hS hA hAi
  -- A local radial rectangle is enough for the original smooth rescaling theorem.
  obtain ⟨W, hW, D, hD, hWD⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hxU)
  obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.mp hW
  obtain ⟨r, hr, hrD⟩ := Metric.mem_nhds_iff.mp hD
  let Q : Set (E × (F × G)) := W' ×ˢ Metric.ball 0 r
  have hQ : IsOpen Q := hW'o.prod Metric.isOpen_ball
  have hQU : Q ⊆ U := (prod_mono hW'W hrD).trans hWD
  have hxQ : (x, (0 : F × G)) ∈ Q := ⟨hxW', by simpa using hr⟩
  have hstar : ∀ z ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1, (z.1, t • z.2) ∈ Q := by
    intro z hz t ht
    refine ⟨hz.1, ?_⟩
    have hv : ‖z.2‖ < r := by simpa using hz.2
    have ht' : ‖t‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul] using
      (mul_le_mul_of_nonneg_right ht' (norm_nonneg z.2)).trans_lt (by simpa using hv)
  have hRg : ContinuousAt (rescaleAlongFibers g) (0, x, v, w) :=
    continuousAt_rescaleAlongFibers_zero g (hg.mono hQU) hQ hstar
      (fun y hy ↦ hgzero y (hQU hy)) x (v, w) hxQ hnormal
  -- The coefficient cylinder is explicit at scale zero, with this same family and inverse.
  have hpJ : ((0 : ℝ), x, v, w) ∈ J.source := by
    change (x, (0 : ℝ) • v) ∈ S
    simpa only [zero_smul] using hx
  have hRJ : ContinuousAt (fun p ↦ (J p).2) (0, x, v, w) := (J.continuousAt hpJ).snd
  have hγ : Continuous (fun p : ℝ × (E × (F × G)) ↦ (p.2.1, p.1 • p.2.2.1)) :=
    continuous_snd.fst.prodMk (continuous_fst.smul continuous_snd.snd.fst)
  have hnear : ∀ᶠ p : ℝ × (E × (F × G)) in 𝓝 ((0 : ℝ), x, v, w),
      (p.2.1, p.1 • p.2.2.1) ∈ S :=
    hγ.continuousAt (by simpa only [zero_smul] using hS.mem_nhds hx)
  have hRC : ContinuousAt (rescaleAlongFibers C) (0, x, v, w) := by
    apply hRJ.congr_of_eventuallyEq
    filter_upwards [hnear] with p hp
    exact congrArg Prod.snd
      (continuousCoefficientShearCylinder_eq_rescaleAlongFibers A S hS hA hAi hzero p hp).symm
  -- Conjugation by dilation preserves composition, and each zero-scale value is identity.
  constructor
  · have h := hRg.comp_of_eq (continuous_fst.continuousAt.prodMk hRC)
      (by simp only [rescaleAlongFibers, ↓reduceIte])
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (rescaleAlongFibers_comp g C)
  · have h := hRC.comp_of_eq (continuous_fst.continuousAt.prodMk hRg)
      (by simp only [rescaleAlongFibers, ↓reduceIte])
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (rescaleAlongFibers_comp C g)

end AtiyahSinger

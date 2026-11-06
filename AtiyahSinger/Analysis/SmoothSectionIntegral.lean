/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactJetIntegral
public import AtiyahSinger.Analysis.SmoothCompositionFamilies
public import AtiyahSinger.Analysis.SmoothSectionFamilies
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Fiber integrals of continuous families of smooth sections

Public module ID: M0981.

Evaluation in a fixed original bundle fiber is continuous for the existing
smooth section topology. A continuous family over a compact parameter has a
smooth section as its pointwise finite-measure integral. The construction uses
the given finite presentation: integrate its original Schwartz localizations,
then recover section coordinates wherever a partition weight is nonzero.
No Bochner integral or artificial norm on the smooth section space is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothBundlePresentation

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- Evaluation in each original normed fiber is continuous in the smooth section topology. -/
theorem continuous_section_evaluation (x : M) :
    Continuous (fun u : A.SmoothSectionSpace ↦ (A.smoothSectionEquiv u).val x) := by
  classical
  -- A nonzero partition weight recovers the original fiber value from one fixed localization.
  obtain ⟨j, hj⟩ : ∃ j : Fin A.size, A.cutoff j x ≠ 0 := by
    by_contra! hall
    have hsum := A.sum_cutoff x
    simp only [hall, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  let := A.frame_mem_atlas j
  have hx := A.support_subset j (subset_tsupport _ hj)
  let L := (A.frame j).continuousLinearEquivAt ℂ x hx.2
  have heval : Continuous (fun u : A.SmoothSectionSpace ↦
      A.localize j (A.smoothSectionEquiv u) (A.chart j x)) :=
    continuous_eval.comp
      (((SchwartzMap.toBoundedContinuousFunctionCLM ℝ
        (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ (Fin r))).continuous.comp
          (A.continuous_localize j)).prodMk continuous_const)
  apply (L.symm.continuous.comp (heval.const_smul (A.cutoff j x : ℂ)⁻¹)).congr
  intro u
  apply L.injective
  change L (L.symm ((A.cutoff j x : ℂ)⁻¹ •
    A.localize j (A.smoothSectionEquiv u) (A.chart j x))) = _
  rw [L.apply_symm_apply]
  have hlocal : A.localize j (A.smoothSectionEquiv u) (A.chart j x) =
      (A.cutoff j x : ℂ) • L ((A.smoothSectionEquiv u).val x) := by
    change A.localizedFunction j (A.smoothSectionEquiv u) (A.chart j x) = _
    simp only [localizedFunction, ite_eq_left ((A.chart j).map_source hx.1),
      sectionInChart, (A.chart j).left_inv hx.1]
    apply congrArg (fun z : TotalSpace (EuclideanSpace ℂ (Fin r)) E ↦
      (A.cutoff j x : ℂ) • (A.frame j z).2)
    exact congrArg (fun z : M ↦
      (⟨z, (A.smoothSectionEquiv u).val z⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
      ((A.chart j).left_inv hx.1)
  rw [hlocal, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hj)]

/-- Pointwise integration of a compact continuous family gives an actual smooth section. -/
theorem isSmoothSection_integral {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    (f : Y → A.SmoothSectionSpace) (hf : Continuous f) :
    IsSmoothSection (n := n) (r := r) E
      (fun x ↦ ∫ y, (A.smoothSectionEquiv (f y)).val x ∂μ) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let I := 𝓘(ℝ, X)
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ V E x
  let w (j : Fin A.size) (y : Y) := A.localize j (A.smoothSectionEquiv (f y))
  have hw (j : Fin A.size) : Continuous (w j) := (A.continuous_localize j).comp hf
  -- Integrate every original localized jet in its complete finite-dimensional coordinate space.
  have hJ (j : Fin A.size) : ContDiff ℝ ∞ (fun z ↦ ∫ y, w j y z ∂μ) := by
    apply contDiffOn_univ.mp
    apply contDiffOn_integral_of_continuous_jets μ isOpen_univ
      (fun y ↦ (w j y).smooth ⊤ |>.contDiffOn)
    intro k
    exact ((continuous_iteratedFDeriv_schwartz k).comp
      (((hw j).comp continuous_fst).prodMk continuous_snd)).continuousOn
  have hi (x : M) : Integrable (fun y ↦ (A.smoothSectionEquiv (f y)).val x) μ :=
    ((A.continuous_section_evaluation x).comp hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  intro e he x hx
  let := he
  obtain ⟨j, hj⟩ : ∃ j : Fin A.size, A.cutoff j x ≠ 0 := by
    by_contra! hall
    have hsum := A.sum_cutoff x
    simp only [hall, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  let c := A.chart j
  let d := A.frame j
  let := A.frame_mem_atlas j
  have hxj := A.support_subset j (subset_tsupport _ hj)
  let U : Set M := ((c.source ∩ d.baseSet) ∩ e.baseSet) ∩ {z | A.cutoff j z ≠ 0}
  have hU : IsOpen U :=
    ((c.open_source.inter d.open_baseSet).inter e.open_baseSet).inter
      (isOpen_ne.preimage (A.smooth_cutoff j).continuous)
  have hxU : x ∈ U := ⟨⟨hxj, hx⟩, hj⟩
  let T (z : M) : V →L[ℂ] V := d.coordChangeL ℂ e z
  let v (z : M) : V := ∫ y, w j y (c z) ∂μ
  have hT : ContMDiffOn I 𝓘(ℝ, V →L[ℂ] V) ∞ T U :=
    (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E) d e).mono
      (fun z hz ↦ ⟨hz.1.1.2, hz.1.2⟩)
  have hv : ContMDiffOn I 𝓘(ℝ, V) ∞ v U :=
    (hJ j).contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (A.chart_mem_atlas j))).mono
          (fun z hz ↦ hz.1.1.1))
  have ha : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ (fun z ↦ (A.cutoff j z : ℂ)⁻¹) U := by
    have hcut : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (A.cutoff j) U :=
      (A.smooth_cutoff j).contMDiffOn
    have hinv := hcut.inv₀ (fun z hz ↦ hz.2)
    convert Complex.ofRealCLM.contMDiff.comp_contMDiffOn hinv using 1
    funext z
    exact (Complex.ofReal_inv (A.cutoff j z)).symm
  have happly : ContDiff ℝ ∞ (fun z : (V →L[ℂ] V) × V ↦ z.1 z.2) :=
    (show ContDiff ℂ ∞ (fun z : (V →L[ℂ] V) × V ↦ z.1 z.2) from
      contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
  have hmodel : ContMDiffOn I 𝓘(ℝ, V) ∞
      (fun z ↦ (A.cutoff j z : ℂ)⁻¹ • T z (v z)) U :=
    (show ContDiff ℝ ∞ (fun z : ℂ × V ↦ z.1 • z.2) from contDiff_smul).contMDiff
      |>.comp_contMDiffOn (ha.prodMk_space
        (happly.contMDiff.comp_contMDiffOn (hT.prodMk_space hv)))
  -- On this neighborhood the same nonzero weight and frame change recover the fiber integral.
  apply ContMDiffAt.contMDiffWithinAt
  apply ((hmodel x hxU).contMDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hxU] with z hz
  let : CompleteSpace (E z) := FiniteDimensional.complete ℂ (E z)
  let L := e.continuousLinearEquivAt ℂ z hz.1.2
  let R : V →L[ℂ] V := (A.cutoff j z : ℂ)⁻¹ • T z
  have hcoord (y : Y) : L ((A.smoothSectionEquiv (f y)).val z) = R (w j y (c z)) := by
    have hlocal : w j y (c z) = (A.cutoff j z : ℂ) •
        (d ⟨z, (A.smoothSectionEquiv (f y)).val z⟩).2 := by
      change (if c z ∈ c.target then
        (A.cutoff j (c.symm (c z)) : ℂ) •
          (d ⟨c.symm (c z), (A.smoothSectionEquiv (f y)).val (c.symm (c z))⟩).2
        else 0) = _
      simp only [ite_eq_left (c.map_source hz.1.1.1), c.left_inv hz.1.1.1]
      apply congrArg (fun v : TotalSpace V E ↦ (A.cutoff j z : ℂ) • (d v).2)
      exact congrArg (fun v : M ↦
        (⟨v, (A.smoothSectionEquiv (f y)).val v⟩ : TotalSpace V E))
        (c.left_inv hz.1.1.1)
    rw [hlocal]
    change L ((A.smoothSectionEquiv (f y)).val z) =
      (A.cutoff j z : ℂ)⁻¹ • (T z ((A.cutoff j z : ℂ) •
        (d ⟨z, (A.smoothSectionEquiv (f y)).val z⟩).2))
    rw [map_smul, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hz.2)]
    change (e ⟨z, (A.smoothSectionEquiv (f y)).val z⟩).2 = _
    change (e ⟨z, (A.smoothSectionEquiv (f y)).val z⟩).2 =
      d.coordChangeL ℂ e z (d ⟨z, (A.smoothSectionEquiv (f y)).val z⟩).2
    rw [d.coordChangeL_apply e ⟨hz.1.1.2, hz.1.2⟩,
      d.symm_apply_apply_mk hz.1.1.2]
  have hwint : Integrable (fun y ↦ w j y (c z)) μ :=
    (continuous_eval.comp
      (((SchwartzMap.toBoundedContinuousFunctionCLM ℝ X V).continuous.comp
        (hw j)).prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change L.toContinuousLinearMap (∫ y, (A.smoothSectionEquiv (f y)).val z ∂μ) =
    R (∫ y, w j y (c z) ∂μ)
  rw [← L.toContinuousLinearMap.integral_comp_comm (hi z),
    ← R.integral_comp_comm hwint]
  exact integral_congr_ae (Eventually.of_forall hcoord)

end AtiyahSinger.SmoothBundlePresentation

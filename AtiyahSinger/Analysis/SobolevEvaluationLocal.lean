/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SobolevLocalization
public import AtiyahSinger.Geometry.DualBundle

/-!
# Local coordinate formulas for geometric Sobolev evaluation

Public module ID: M0996.

The supplied nonnegative coordinate density and induced dual frame transport the
same-point evaluation integral to the Euclidean bilinear dot product. Cutoff
extension in one variable is paired with the identical cutoff localization in
the other. These formulas supply the local reconstruction used in perfect
Sobolev evaluation duality; neither a Hermitian metric nor a chosen Hilbert
identification replaces the original covector evaluation.

The formulas are standard coordinate integration as used in SG III.2.15(2).
The same chart computation also enters the global formal transpose.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] in
private theorem integral_eq_chartIntegral (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (μ : Measure M)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContinuousOn w c.target)
    (hpos : ∀ z ∈ c.target, 0 ≤ w z)
    (hmap : Measure.map c (μ.restrict c.source) =
      (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
    (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
    (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
  classical
  -- Extend the target test by zero outside the prescribed chart target.
  let g : EuclideanSpace ℝ (Fin n) → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
  have hg : Measurable g :=
    (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
      continuousOn_const c.open_target.measurableSet
  have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
    ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
      |>.aemeasurable c.open_target.measurableSet
  calc
    (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
    _ = ∫ x in c.source, g (c x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
      simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
    _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
      (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
        hg.aestronglyMeasurable).symm
    _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
      rw [hmap]
      exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
        (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
    _ = ∫ z in c.target, w z • f (c.symm z) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]

variable {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [IsSmoothComplexBundle (n := n) (r := r) E]

namespace BundleChartCutoff

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (A : BundleChartCutoff (r := r) E c)
  (D : BundleChartCutoff (r := r) (DualBundle E) c)
  (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
  (hframe : D.frame = @dualFrame r M _ E _ _ _ _ _ A.frame A.frame_mem_atlas)
  (hcut : D.cutoff = A.cutoff)
  (μ : Measure M) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
  (hρ : ContinuousOn ρ c.target) (hρpos : ∀ z ∈ c.target, 0 ≤ ρ z)
  (hmap : Measure.map c (μ.restrict c.source) =
    (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (ρ z)))

include hframe hcut hρ hρpos hmap

/-- Covector extension is paired with localization in the same primal frame. -/
theorem integral_dualExtend_eq
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (u : smoothSections (n := n) (r := r) E) :
    (∫ x, (D.extend hc v).val x (u.val x) ∂μ) =
      ∫ z, ρ z • ∑ i, v z i * A.localize hc u z i := by
  classical
  let := A.frame_mem_atlas
  let := D.frame_mem_atlas
  have hpair (x : M) (hx : x ∈ A.frame.baseSet) (α : DualBundle E x) (w : E x) :
      α w = ∑ i, (dualFrame E A.frame ⟨x, α⟩).2 i * (A.frame ⟨x, w⟩).2 i := by
    have hexpand : ∑ i : Fin r, (A.frame ⟨x, w⟩).2 i •
        A.frame.symmL ℂ x (EuclideanSpace.single i 1) = w := by
      have heq := congrArg (A.frame.symmL ℂ x)
        ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((A.frame ⟨x, w⟩).2))
      calc
        _ = A.frame.symmL ℂ x ((A.frame ⟨x, w⟩).2) := by
          simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
        _ = w := by
          rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact A.frame.symmL_continuousLinearMapAt hx w
    have hd := dualFrame_apply_snd E A.frame
      (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
    simp only [dite_true] at hd
    rw [hd]
    conv_lhs => rw [← hexpand, map_sum]
    simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
    exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
  rw [integral_eq_chartIntegral c μ ρ hρ hρpos hmap (fun x ↦ (D.extend hc v).val x (u.val x))
    (by simpa only [dualSectionsEquiv] using
      (contMDiff_dualSection_eval E ⟨(D.extend hc v).val,
        (isSmoothSection_dualBundle_iff E _).1 (D.extend hc v).property⟩ u).continuous)
    (by
      intro x hx
      by_contra hxc
      apply hx
      change (D.extendedFunction v x) (u.val x) = 0
      simp [BundleChartCutoff.extendedFunction, hxc])]
  calc
    _ = ∫ z in c.target, ρ z • ∑ i, v z i * (A.localize hc u) z i := by
      apply setIntegral_congr_fun c.open_target.measurableSet
      intro z hz
      apply congrArg (fun a : ℂ ↦ ρ z • a)
      change (D.extendedFunction v (c.symm z)) (u.val (c.symm z)) =
        ∑ i, v z i * A.localizedFunction u z i
      simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
        c.map_target hz, ite_true, c.right_inv hz, hz]
      by_cases hb : z ∈ tsupport A.cutoff
      · have he := (A.support_subset hb).2
        have hd : c.symm z ∈ D.frame.baseSet := by
          rw [hframe, dualFrame_baseSet]
          exact he
        change (D.cutoff z : ℂ) * (D.frame.symmL ℂ (c.symm z) (v z))
          (u.val (c.symm z)) = _
        rw [hpair _ he, ← hframe]
        rw [← D.frame.continuousLinearMapAt_apply_of_mem ℂ hd,
          D.frame.continuousLinearMapAt_symmL hd]
        simp only [hcut, sectionInChart, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ ↦ by ring)
      · simp [hcut, image_eq_zero_of_notMem_tsupport hb]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro z hz
      change ρ z • ∑ i, v z i * A.localizedFunction u z i = 0
      simp [BundleChartCutoff.localizedFunction, hz])

/-- Primal extension is paired with localization in the induced dual frame. -/
theorem integral_extendDual_eq
    (α : smoothSections (n := n) (r := r) (DualBundle E))
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    (∫ x, α.val x ((A.extend hc v).val x) ∂μ) =
      ∫ z, ρ z • ∑ i, D.localize hc α z i * v z i := by
  classical
  let := A.frame_mem_atlas
  let := D.frame_mem_atlas
  have hpair (x : M) (hx : x ∈ A.frame.baseSet) (α : DualBundle E x) (w : E x) :
      α w = ∑ i, (dualFrame E A.frame ⟨x, α⟩).2 i * (A.frame ⟨x, w⟩).2 i := by
    have hexpand : ∑ i : Fin r, (A.frame ⟨x, w⟩).2 i •
        A.frame.symmL ℂ x (EuclideanSpace.single i 1) = w := by
      have heq := congrArg (A.frame.symmL ℂ x)
        ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((A.frame ⟨x, w⟩).2))
      calc
        _ = A.frame.symmL ℂ x ((A.frame ⟨x, w⟩).2) := by
          simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
        _ = w := by
          rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact A.frame.symmL_continuousLinearMapAt hx w
    have hd := dualFrame_apply_snd E A.frame
      (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
    simp only [dite_true] at hd
    rw [hd]
    conv_lhs => rw [← hexpand, map_sum]
    simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
    exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
  rw [integral_eq_chartIntegral c μ ρ hρ hρpos hmap (fun x ↦ α.val x ((A.extend hc v).val x))
    (by simpa only [dualSectionsEquiv] using
      (contMDiff_dualSection_eval E ⟨α.val, (isSmoothSection_dualBundle_iff E α.val).1 α.property⟩
        (A.extend hc v)).continuous)
    (by
      intro x hx
      by_contra hxc
      apply hx
      change α.val x (A.extendedFunction v x) = 0
      simp [BundleChartCutoff.extendedFunction, hxc])]
  calc
    _ = ∫ z in c.target, ρ z • ∑ i, (D.localize hc α) z i * v z i := by
      apply setIntegral_congr_fun c.open_target.measurableSet
      intro z hz
      apply congrArg (fun a : ℂ ↦ ρ z • a)
      change α.val (c.symm z) (A.extendedFunction v (c.symm z)) =
        ∑ i, D.localizedFunction α z i * v z i
      simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
        c.map_target hz, ite_true, c.right_inv hz, hz]
      by_cases hb : z ∈ tsupport A.cutoff
      · have he := (A.support_subset hb).2
        rw [map_smul, smul_eq_mul, hpair _ he]
        simp only [hframe, hcut, sectionInChart, PiLp.smul_apply, smul_eq_mul]
        rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
          A.frame.continuousLinearMapAt_symmL he]
        simp only [Finset.mul_sum, mul_assoc]
      · simp [hcut, image_eq_zero_of_notMem_tsupport hb]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro z hz
      change ρ z • ∑ i, D.localizedFunction α z i * v z i = 0
      simp [BundleChartCutoff.localizedFunction, hz])

end BundleChartCutoff

end AtiyahSinger

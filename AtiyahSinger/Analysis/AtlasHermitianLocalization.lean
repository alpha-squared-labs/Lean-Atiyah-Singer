/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolevLocalization
public import AtiyahSinger.Geometry.AtlasHermitianCoordinates
public import AtiyahSinger.Geometry.HermitianPairing

/-!
# Local integration for the original atlas Hermitian pairing

Public module ID: M0247.

Compact cutoff extension in an original frame pairs with localization in that
same frame, its original positive chart density and its actual Gram operator.
The finite model rank belongs to that particular frame; no global rank or new
fiber metric is introduced. This is the local coordinate identity used in the
opposite-order Sobolev duality of Spin Geometry III.2, Theorem 2.15(2).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]

variable {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  {A : SmoothComplexBundleAtlas (n := n) E}

namespace AtlasChartCutoff

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
  (D : AtlasChartCutoff A c) (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
  (μ : Measure M) (h : ComplexBundle.ContinuousHermitianMetric E)
  (hh : A.IsSmoothHermitianMetric h) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
  (hρ : ContinuousOn ρ c.target) (hρpos : ∀ z ∈ c.target, 0 ≤ ρ z)
  (hmap : Measure.map c (μ.restrict c.source) =
    (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (ρ z)))

include hM hT hSC hh hρ hρpos hmap

/-- Original cutoff extension and localization preserve the exact metric integral. -/
theorem integral_pairing_extend
    (u : A.smoothSections)
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) :
    (∫ x, (h.toCore x).inner (u.val x) ((D.extend hc v).val x) ∂μ) =
      ∫ z, ρ z • inner ℂ (D.localize hc u z)
        (A.hermitianGramOperator h D.frameIndex (c.symm z) (v z)) := by
  classical
  have hintegral
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
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
  have hsupport : Function.support
      (fun x ↦ (h.toCore x).inner (u.val x) ((D.extend hc v).val x)) ⊆ c.source := by
    intro x hx
    by_contra hxc
    apply hx
    have hz : (D.extend hc v).val x = 0 := by
      simp only [extend, extendedFunction, show ¬(x ∈ c.source ∩
        (A.chart D.frameIndex).baseSet) from fun hx ↦ hxc hx.1, dite_false]
    change (h.toCore x).inner (u.val x) ((D.extend hc v).val x) = 0
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    rw [hz]
    exact InnerProductSpace.Core.inner_zero_right _
  rw [hintegral c μ ρ hρ hρpos hmap
    (fun x ↦ (h.toCore x).inner (u.val x) ((D.extend hc v).val x))
    (A.contMDiff_pairing h hh u (D.extend hc v)).continuous hsupport]
  calc
    _ = ∫ z in c.target, ρ z • inner ℂ (D.localize hc u z)
        (A.hermitianGramOperator h D.frameIndex (c.symm z) (v z)) := by
      apply setIntegral_congr_fun c.open_target.measurableSet
      intro z hz
      apply congrArg (fun a : ℂ ↦ ρ z • a)
      let x := c.symm z
      have hcx : c x = z := c.right_inv hz
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      by_cases hb : z ∈ tsupport D.cutoff
      · have he : x ∈ (A.chart D.frameIndex).baseSet := (D.support_subset hb).2
        have hx : x ∈ c.source ∩ (A.chart D.frameIndex).baseSet := ⟨c.map_target hz, he⟩
        change (h.toCore x).inner (u.val x) (D.extendedFunction v x) = _
        simp only [extendedFunction, dite_eq_left hx, hcx]
        rw [InnerProductSpace.Core.inner_smul_right]
        rw [A.pairing_eq_hermitianGramOperator h D.frameIndex x he]
        simp only [LinearEquiv.apply_symm_apply,
          ContinuousLinearEquiv.symm_apply_apply]
        change (D.cutoff z : ℂ) * inner ℂ
          ((EuclideanSpace.equiv (Fin (A.rank D.frameIndex)) ℂ).symm
            ((A.frameLinearEquiv D.frameIndex x he) (u.val x)))
          (A.hermitianGramOperator h D.frameIndex x (v z)) = _
        change _ = inner ℂ (D.localizedFunction u z)
          (A.hermitianGramOperator h D.frameIndex (c.symm z) (v z))
        rw [localizedFunction, ite_eq_left hz, inner_smul_left, Complex.conj_ofReal]
        rfl
      · have hzero := image_eq_zero_of_notMem_tsupport hb
        have hvzero : D.extendedFunction v x = 0 := by
          unfold extendedFunction
          split_ifs
          · simp [x, c.right_inv hz, hzero]
          · rfl
        change (h.toCore x).inner (u.val x) (D.extendedFunction v x) = _
        rw [hvzero, InnerProductSpace.Core.inner_zero_right]
        simp [localize, localizedFunction, hz, hzero]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro z hz
      simp [localize, localizedFunction, hz])

end AtlasChartCutoff

end AtiyahSinger

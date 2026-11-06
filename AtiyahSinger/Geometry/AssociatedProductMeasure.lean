/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedFiberIntegration
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The actual associated product measure

Public module ID: M1062.

Integrate first over the original invariant compact fiber and then against
the specified base measure. This positive linear functional determines a
finite regular measure on the original compact associated quotient. Its
integral on every continuous real function is exactly that iterated integral.
No global measurable principal section or replacement quotient is assumed.

For the associated sphere, `AssociatedProductDensity` proves smooth
positivity by local change of variables when both specified measures
are smooth positive.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped CompactlySupported

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MeasurableSpace B] [BorelSpace B] [CompactSpace B]
  (hP : IsPrincipalBundle G projection) (μ : Measure B) (ν : Measure Y)
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)

local notation "Z" => AssociatedBundle G P Y

/-- The positive functional obtained by integrating the original whole fibers and original base. -/
def associatedProductIntegral : C_c(Z, ℝ) →ₚ[ℝ] ℝ := by
  let I (f : C_c(Z, ℝ)) (b : B) := associatedFiberIntegral hP ν f.toContinuousMap b
  have hfiber (f : C_c(Z, ℝ)) (p : P) :
      Integrable (fun y ↦ f (associatedBundleMk G P Y p y)) ν := by
    have hf : Continuous (fun y ↦ f (associatedBundleMk G P Y p y)) :=
      f.continuous.comp (continuous_quot_mk.comp (continuous_const.prodMk continuous_id))
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (f : C_c(Z, ℝ)) : Integrable (I f) μ := by
    have hf := continuous_associatedFiberIntegral hP ν hν f.toContinuousMap
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine {
    toFun := fun f ↦ ∫ b, I f b ∂μ
    map_add' := ?_
    map_smul' := ?_
    monotone' := ?_ }
  · intro f g
    have hadd (b : B) : I (f + g) b = I f b + I g b := by
      change (∫ y, f (associatedBundleMk G P Y _ y) + g (associatedBundleMk G P Y _ y) ∂ν) = _
      exact integral_add (hfiber f _) (hfiber g _)
    simp only [hadd]
    exact integral_add (hi f) (hi g)
  · intro c f
    have hsmul (b : B) : I (c • f) b = c • I f b := by
      change (∫ y, c • f (associatedBundleMk G P Y _ y) ∂ν) = _
      exact integral_smul c _
    simp only [hsmul, integral_smul, RingHom.id_apply]
  · intro f g hfg
    apply integral_mono (hi f) (hi g)
    intro b
    apply integral_mono (hfiber f _) (hfiber g _)
    intro y
    exact hfg _

variable [MeasurableSpace (AssociatedBundle G P Y)] [BorelSpace (AssociatedBundle G P Y)]
  [T2Space (AssociatedBundle G P Y)] [CompactSpace (AssociatedBundle G P Y)]

/-- The regular measure on the original associated quotient representing the product integral. -/
def associatedProductMeasure : Measure Z :=
  RealRMK.rieszMeasure (associatedProductIntegral hP μ ν hν)

/-- The original compact associated product measure is finite. -/
instance isFiniteMeasure_associatedProductMeasure :
    IsFiniteMeasure (associatedProductMeasure hP μ ν hν) :=
  inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (associatedProductIntegral hP μ ν hν)))

/-- Each continuous real function has exactly its fiber integral inside the base integral. -/
theorem integral_associatedProductMeasure (f : C(Z, ℝ)) :
    (∫ z, f z ∂associatedProductMeasure hP μ ν hν) =
      ∫ b, associatedFiberIntegral hP ν f b ∂μ := by
  let f' : C_c(Z, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (associatedProductIntegral hP μ ν hν) f'

/-- The same actual product measure satisfies Fubini for continuous complex pairings. -/
theorem integral_associatedProductMeasure_complex (f : C(Z, ℂ)) :
    (∫ z, f z ∂associatedProductMeasure hP μ ν hν) =
      ∫ b, associatedFiberIntegral hP ν f b ∂μ := by
  let fR : C(Z, ℝ) := ⟨fun z ↦ (f z).re, Complex.continuous_re.comp f.continuous⟩
  let fI : C(Z, ℝ) := ⟨fun z ↦ (f z).im, Complex.continuous_im.comp f.continuous⟩
  have hf : Integrable f (associatedProductMeasure hP μ ν hν) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (associatedFiberIntegral hP ν f) μ :=
    (continuous_associatedFiberIntegral hP ν hν f).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfiber (p : P) : Integrable (fun y ↦ f (associatedBundleMk G P Y p y)) ν := by
    have hc : Continuous (fun y ↦ f (associatedBundleMk G P Y p y)) :=
      f.continuous.comp (continuous_quot_mk.comp (continuous_const.prodMk continuous_id))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Real and imaginary parts commute with the same finite fiber and base integrals.
  have hre (b : B) : associatedFiberIntegral hP ν fR b =
      (associatedFiberIntegral hP ν f b).re := integral_re (hfiber _)
  have him (b : B) : associatedFiberIntegral hP ν fI b =
      (associatedFiberIntegral hP ν f b).im := integral_im (hfiber _)
  apply Complex.ext
  · calc
      (∫ z, f z ∂associatedProductMeasure hP μ ν hν).re =
          ∫ z, (f z).re ∂associatedProductMeasure hP μ ν hν := (integral_re hf).symm
      _ = ∫ b, associatedFiberIntegral hP ν fR b ∂μ :=
        integral_associatedProductMeasure hP μ ν hν fR
      _ = ∫ b, (associatedFiberIntegral hP ν f b).re ∂μ := by simp only [hre]
      _ = (∫ b, associatedFiberIntegral hP ν f b ∂μ).re := integral_re hi
  · calc
      (∫ z, f z ∂associatedProductMeasure hP μ ν hν).im =
          ∫ z, (f z).im ∂associatedProductMeasure hP μ ν hν := (integral_im hf).symm
      _ = ∫ b, associatedFiberIntegral hP ν fI b ∂μ :=
        integral_associatedProductMeasure hP μ ν hν fI
      _ = ∫ b, (associatedFiberIntegral hP ν f b).im ∂μ := by simp only [him]
      _ = (∫ b, associatedFiberIntegral hP ν f b ∂μ).im := integral_im hi

end AtiyahSinger

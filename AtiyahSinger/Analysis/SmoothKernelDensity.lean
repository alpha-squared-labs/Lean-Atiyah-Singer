/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothingOperator
public import AtiyahSinger.Geometry.SmoothDensityRatio

/-!
# Changing the density of a smooth integral kernel

Public module ID: M0972.

D02/A05: the same section operator has kernel (dμ/dν)(y) K(x,y) when its
integration measure changes from μ to ν. The weight is in the input variable.
The kernel itself generally changes, whereas the induced smooth-section map does not.
Sources: SG III.3 (3.17), p.186, and the smooth density comparison.
These are explicit project comparisons of the existing integral formulas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ ν : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hT2 hSC hC hE hF hμ hν

namespace SmoothKernel

variable (K : SmoothKernel (n := n) (r := r) (q := q) E F)

/-- Reweighting the input variable by the reciprocal density ratio preserves smoothness. -/
theorem isSmooth_changeMeasure :
    IsSmoothKernel (n := n) (r := r) (q := q) E F
      (fun x y ↦ (smoothDensityRatio (n := n) ν μ y : ℂ) • K.toFun x y) := by
  /- In every pair of frames this multiplies a smooth matrix by a smooth
  scalar depending only on the input point. The product manifold chain rule
  and scalar multiplication give joint smoothness; positivity makes the ratio regular. -/
  intro e f _ _
  -- The ratio is pulled back from the input projection of the same product base.
  have hw : ContMDiff
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, ℂ) ∞ (fun z : M × M ↦ (smoothDensityRatio (n := n) ν μ z.2 : ℂ)) :=
    (contMDiff_complex_smoothDensityRatio (n := n) ν μ).comp contMDiff_snd
  have hsmul : ContDiff ℝ ∞ (fun z : ℂ ×
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ z.1 • z.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
  apply (hsmul.contMDiff.comp_contMDiffOn
    (hw.contMDiffOn.prodMk_space (K.isSmooth e f))).congr
  intro z hz
  simp only [kernelInFrames, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul]
  rfl

/-- The kernel of the identical integral operator when integration uses ν instead of μ. -/
def changeMeasure : SmoothKernel (n := n) (r := r) (q := q) E F where
  toFun x y := (smoothDensityRatio (n := n) ν μ y : ℂ) • K.toFun x y
  isSmooth := K.isSmooth_changeMeasure μ ν

/-- The reweighted kernel uses dμ/dν at the input point, not at the output. -/
theorem changeMeasure_apply (x y : M) (u : E y) :
    (K.changeMeasure μ ν).toFun x y u =
      (smoothDensityRatio (n := n) ν μ y : ℂ) • K.toFun x y u := by
  /- Unfold changeMeasure and scalar multiplication of continuous linear maps.
  The formula fixes both the reciprocal direction and the input-variable dependence. -/
  rfl

/-- Reweighting the kernel exactly preserves its original section-valued integral map. -/
theorem toLinearMap_changeMeasure : (K.changeMeasure μ ν).toLinearMap ν = K.toLinearMap μ := by
  /- For each fixed output point apply the Bochner change-of-density formula
  in that finite-dimensional fiber. Multiplying by dμ/dν exactly compensates
  integration against ν. The smoothness certificates preserve these pointwise values. -/
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  -- Change the integration measure in this fixed original output fiber.
  change (∫ y, (smoothDensityRatio (n := n) ν μ y : ℂ) •
    K.toFun x y (u.val y) ∂ν) = ∫ y, K.toFun x y (u.val y) ∂μ
  conv_rhs => rw [← withDensity_smoothDensityRatio (n := n) ν μ]
  rw [integral_withDensity_eq_integral_toReal_smul
    (contMDiff_smoothDensityRatio (n := n) ν μ).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (smoothDensityRatio_pos (n := n) ν μ y).le]
    exact Complex.coe_smul _ _)

/-- Returning to the first density recovers the actual original kernel. -/
theorem changeMeasure_swap : (K.changeMeasure μ ν).changeMeasure ν μ = K := by
  /- The two scalar ratios in the same input variable multiply to one.
  Hence the fiber maps agree pointwise; structure extensionality and proof
  irrelevance identify the smooth kernels, not merely their induced operators. -/
  -- Equality is of the actual kernels, so the weight is cancelled before integration.
  have hfun : ((K.changeMeasure μ ν).changeMeasure ν μ).toFun = K.toFun := by
    funext x y
    change (smoothDensityRatio (n := n) μ ν y : ℂ) •
      ((smoothDensityRatio (n := n) ν μ y : ℂ) • K.toFun x y) = K.toFun x y
    rw [smul_smul, ← Complex.ofReal_mul, smoothDensityRatio_swap (n := n) μ ν y]
    rw [mul_inv_cancel₀ (smoothDensityRatio_pos (n := n) μ ν y).ne', Complex.ofReal_one,
      one_smul]
  have hext (A B : SmoothKernel (n := n) (r := r) (q := q) E F)
      (h : A.toFun = B.toFun) : A = B := by
    cases A
    cases B
    cases h
    rfl
  exact hext _ _ hfun

/-- Kernel reweighting composes through any third positive smooth density. -/
theorem changeMeasure_trans (κ : Measure M) [IsSmoothPositiveMeasure (n := n) κ] :
    (K.changeMeasure μ ν).changeMeasure ν κ = K.changeMeasure μ κ := by
  /- Multiply dν/dκ by dμ/dν in the input variable and apply the ratio cocycle.
  Both sides then have the identical fiber map, independently of a chosen frame. -/
  -- The same input point carries both consecutive density factors.
  have hfun : ((K.changeMeasure μ ν).changeMeasure ν κ).toFun =
      (K.changeMeasure μ κ).toFun := by
    funext x y
    change (smoothDensityRatio (n := n) κ ν y : ℂ) •
      ((smoothDensityRatio (n := n) ν μ y : ℂ) • K.toFun x y) =
        (smoothDensityRatio (n := n) κ μ y : ℂ) • K.toFun x y
    rw [smul_smul, ← Complex.ofReal_mul, ← smoothDensityRatio_mul κ ν μ y]
  have hext (A B : SmoothKernel (n := n) (r := r) (q := q) E F)
      (h : A.toFun = B.toFun) : A = B := by
    cases A
    cases B
    cases h
    rfl
  exact hext _ _ hfun

end SmoothKernel

/-- Having an actual smooth kernel does not depend on the auxiliary positive smooth density. -/
theorem isSmoothingOperator_measure_iff
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F) :
    IsSmoothingOperator μ P ↔ IsSmoothingOperator ν P := by
  /- In one direction reweight the witnessing kernel by dμ/dν, using exact
  equality of the induced section maps. Reverse the two densities for the other.
  No Sobolev characterization or Schwartz kernel theorem is needed for this bridge. -/
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K.changeMeasure μ ν, (K.toLinearMap_changeMeasure μ ν).trans hK⟩
  · rintro ⟨K, hK⟩
    exact ⟨K.changeMeasure ν μ, (K.toLinearMap_changeMeasure ν μ).trans hK⟩

end AtiyahSinger

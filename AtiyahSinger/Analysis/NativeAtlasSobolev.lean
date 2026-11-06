/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolev
public import AtiyahSinger.Analysis.NativeAtlasDifferentialOperator

/-!
# The original fixed-rank Sobolev completion in the atlas presentation

Public module ID: M0806.

D04: retain the original manifold charts, bundle frames and cutoff functions
when regarding a native finite presentation as an atlas presentation. Every
old frame occurs in the native atlas, so no replacement frame is selected.
The finite-product coordinate conversion and its Euclidean inverse cancel;
the resulting Bessel coordinates agree exactly, with the same finite Hilbert
norm. Equality of the closed ranges therefore gives a linear isometry, not
merely an equivalence of norms or an unspecified completion equivalence.

This is the compatibility of the two coordinate constructions of the Fourier
completion in SG III.2, Definition 2.3 and (2.17). It assumes the same real
order and the same presentation. It neither compares unrelated presentations
nor asserts the integer covariant-derivative comparison assigned to A01.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (L : SmoothBundlePresentation (n := n) (r := r) E)

/-- Retain the exact native charts, frames and cutoffs as a finite atlas presentation. -/
def toAtlasBundlePresentation :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    AtlasBundlePresentation (nativeSmoothComplexBundleAtlas (n := n) (r := r) E) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  { size := L.size
    chart := L.chart
    chart_mem_atlas := L.chart_mem_atlas
    frameIndex := fun j ↦ ⟨L.frame j, L.frame_mem_atlas j⟩
    cutoff := L.cutoff
    smooth_cutoff := L.smooth_cutoff
    cutoff_nonneg := L.cutoff_nonneg
    compact_support := L.compact_support
    support_subset := L.support_subset
    sum_cutoff := L.sum_cutoff }

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- Identity on the original section values gives exactly the original Bessel coordinate map. -/
theorem sobolevCoordinates_toAtlasBundlePresentation (s : ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    (L.toAtlasBundlePresentation.sobolevCoordinates s).comp
        (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm.toLinearMap =
      L.sobolevCoordinates s := by
  /- Stage 1: the smooth-section equivalence preserves every original
  fiber value. Each converted frame uses the same original native chart.
  Its finite-product coordinate equivalence cancels the inverse equivalence
  in atlasSectionInChart, so the local Euclidean coordinate functions agree.
  The same cutoff and chart target give identical zero extensions as well.
  Stage 2: these are equal Schwartz functions, including their original
  Euclidean target norms. Apply the identical Bessel coordinate map at
  order s in each component, then the same finite Hilbert-sum constructor.
  Linearity extensionality gives equality of the entire coordinate maps.
  No density argument or analytic comparison constant is needed here. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  -- Cancel the two model equivalences on every original cutoff localization.
  have hlocal (u : smoothSections (n := n) (r := r) E) (j : Fin L.size) :
      L.toAtlasBundlePresentation.localize j
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) =
        L.localize j u := by
    apply SchwartzMap.ext
    intro z
    change (if z ∈ (L.chart j).target then
      (L.cutoff j ((L.chart j).symm z) : ℂ) •
        (EuclideanSpace.equiv (Fin r) ℂ).symm
          ((EuclideanSpace.equiv (Fin r) ℂ)
            (L.frame j ⟨(L.chart j).symm z, u.val ((L.chart j).symm z)⟩).2)
      else 0) = _
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  -- Apply the same Bessel operator to equal Schwartz functions in each Hilbert component.
  apply LinearMap.ext
  intro u
  apply (WithLp.linearEquiv 2 ℂ _).injective
  funext j
  change schwartzSobolevCoordinate s
    (L.toAtlasBundlePresentation.localize j
      ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u)) =
    schwartzSobolevCoordinate s (L.localize j u)
  exact congrArg (schwartzSobolevCoordinate s) (hlocal u j)

/-- The native and atlas completions are the same closed Hilbert subspace. -/
def nativeAtlasSobolevEquiv (s : ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    L.SobolevSpace s ≃ₗᵢ[ℂ] L.toAtlasBundlePresentation.SobolevSpace s := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  -- Surjectivity of the identity section transport makes the actual ranges equal.
  have hRange : (L.sobolevCoordinates s).range =
      (L.toAtlasBundlePresentation.sobolevCoordinates s).range := by
    rw [← L.sobolevCoordinates_toAtlasBundlePresentation s]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr
        (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm.surjective)
  -- Equality of those closed subspaces preserves their inherited Hilbert norms.
  exact LinearIsometryEquiv.ofEq _ _ (congrArg Submodule.topologicalClosure hRange)

/-- The canonical isometry preserves the inclusion of each original smooth section. -/
theorem nativeAtlasSobolevEquiv_smoothToSobolev (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    L.nativeAtlasSobolevEquiv s (L.smoothToSobolev s u) =
      L.toAtlasBundlePresentation.smoothToSobolev s
        ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) := by
  /- The isometry is identity on the ambient Hilbert tuple. The two
  displayed inclusions have the same tuple by the coordinate-map identity.
  Subtype extensionality gives equality in the same closed range, while
  the section transport on the right retains every original fiber value. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  -- The specified closed-subspace isometry is identity on the actual Hilbert tuple.
  apply Subtype.ext
  change L.sobolevCoordinates s u =
    L.toAtlasBundlePresentation.sobolevCoordinates s
      ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u)
  exact (congrArg (fun T ↦ T u) (L.sobolevCoordinates_toAtlasBundlePresentation s)).symm

end SmoothBundlePresentation

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DualSobolev
public import AtiyahSinger.Geometry.DualBundle

/-!
# Identifying the two concrete Sobolev models of E*

Public module ID: M0446.

D04/A01/SR03. Keep the same manifold charts and cutoff functions, and use the
dual frames constructed in DualBundle. The resulting common SobolevSpace API has
exactly the same Bessel coordinates as the independent DualSobolevSpace construction.
Their closed subspaces are equal, giving a canonical complex-linear isometry.
Isometry is specific to this induced presentation; arbitrary presentations only
have the continuous equivalences already provided by SobolevMaps.

This is a model comparison for SG III.2.14–2.15, with no additional analytic hypothesis.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The induced dual presentation retains the original charts and cutoffs. -/
def dualPresentation : SmoothBundlePresentation (n := n) (r := r) (DualBundle E) where
  size := A.size
  chart := A.chart
  chart_mem_atlas := A.chart_mem_atlas
  frame j := by
    letI := A.frame_mem_atlas j
    exact dualFrame E (A.frame j)
  frame_mem_atlas j := by
    let := A.frame_mem_atlas j
    exact memTrivializationAtlas_dualFrame E (A.frame j)
  cutoff := A.cutoff
  smooth_cutoff := A.smooth_cutoff
  cutoff_nonneg := A.cutoff_nonneg
  compact_support := A.compact_support
  support_subset j := by
    let := A.frame_mem_atlas j
    simpa only [dualFrame_baseSet] using A.support_subset j
  sum_cutoff := A.sum_cutoff

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]


set_option linter.unusedSectionVars false in
/-- The common dual-bundle localization is the earlier actual covector localization. -/
theorem localizedFunction_dualPresentation (j : Fin A.size)
    (α : smoothDualSections (n := n) (r := r) E) :
    A.dualPresentation.localizedFunction j (dualSectionsEquiv E α) =
      A.localizedDualFunction j α := by
  /- Outside the chart target both zero extensions vanish. Inside, if the cutoff
  is nonzero its support condition puts the base point in the primal frame. Apply
  dualFrame_apply_snd there. If the cutoff vanishes both products are zero, so
  no inverse-frame evaluation outside its valid base set is required. -/
  classical
  let := A.frame_mem_atlas j
  funext z
  change (if z ∈ (A.chart j).target then
      (A.cutoff j ((A.chart j).symm z) : ℂ) •
        (dualFrame E (A.frame j)
          ⟨(A.chart j).symm z, α.val ((A.chart j).symm z)⟩).2
      else 0) = A.localizedDualFunction j α z
  by_cases htarget : z ∈ (A.chart j).target
  · -- The original support condition licenses precisely this inverse-frame evaluation.
    by_cases hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j)
    · have hframe := (A.support_subset j hcut).2
      simp only [localizedDualFunction, ite_eq_left htarget]
      rw [dualFrame_apply_snd E (A.frame j) α.val ((A.chart j).symm z) hframe]
    · simp [localizedDualFunction, image_eq_zero_of_notMem_tsupport hcut]
  · simp [localizedDualFunction, htarget]

/-- The two Schwartz localizations package the same coordinate function. -/
theorem localize_dualPresentation (j : Fin A.size)
    (α : smoothDualSections (n := n) (r := r) E) :
    A.dualPresentation.localize j (dualSectionsEquiv E α) = A.localizeDual j α := by
  /- Both Schwartz packages have the functions identified by the previous theorem.
  Extensionality removes the different smoothness and compact-support proof fields. -/
  apply DFunLike.ext
  intro z
  exact congrFun (A.localizedFunction_dualPresentation j α) z

/-- The two models give the same tuple of Bessel L² coordinates on smooth dual sections. -/
theorem sobolevCoordinates_dualPresentation (s : ℝ)
    (α : smoothDualSections (n := n) (r := r) E) :
    A.dualPresentation.sobolevCoordinates s (dualSectionsEquiv E α) =
      A.dualSobolevCoordinates s α := by
  /- The two presentations use identical chart indices. Apply the identical Bessel
  coordinate map to the equal localized Schwartz functions in each coordinate,
  then assemble the finite PiLp tuple. Neither Fourier convention nor norm is changed. -/
  apply PiLp.ext
  intro j
  change schwartzSobolevCoordinate s
      (A.dualPresentation.localize j (dualSectionsEquiv E α)) =
    schwartzSobolevCoordinate s (A.localizeDual j α)
  rw [A.localize_dualPresentation j α]

/-- The two Sobolev completions are equal closed subspaces of the same finite Hilbert sum. -/
theorem dualSobolevClosure_eq (s : ℝ) :
    (A.dualSobolevCoordinates s).range.topologicalClosure =
      (A.dualPresentation.sobolevCoordinates s).range.topologicalClosure := by
  /- The preceding identity and surjectivity of dualSectionsEquiv identify the
  two coordinate ranges. Taking topological closures preserves that equality.
  The ambient finite Hilbert sum is literally the same since the index set is unchanged. -/
  -- Identify the actual coordinate ranges before taking either completion.
  have hrange : (A.dualSobolevCoordinates s).range =
      (A.dualPresentation.sobolevCoordinates s).range := by
    apply Submodule.ext
    intro z
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨dualSectionsEquiv E α, A.sobolevCoordinates_dualPresentation s α⟩
    · rintro ⟨α, rfl⟩
      obtain ⟨β, rfl⟩ := (dualSectionsEquiv E).surjective α
      exact ⟨β, (A.sobolevCoordinates_dualPresentation s β).symm⟩
  exact congrArg Submodule.topologicalClosure hrange

/-- The identity of the common closed subspace gives the canonical isometric model comparison. -/
def dualSobolevEquiv (s : ℝ) :
    A.DualSobolevSpace s ≃ₗᵢ[ℂ] A.dualPresentation.SobolevSpace s :=
  LinearIsometryEquiv.ofEq _ _ (A.dualSobolevClosure_eq s)

/-- The model comparison extends the identity of actual smooth covector sections. -/
theorem dualSobolevEquiv_smooth (s : ℝ)
    (α : smoothDualSections (n := n) (r := r) E) :
    A.dualSobolevEquiv s (A.dualSmoothToSobolev s α) =
      A.dualPresentation.smoothToSobolev s (dualSectionsEquiv E α) := by
  /- The isometry retains the ambient Hilbert tuple. On smooth covectors the tuples
  on both sides coincide by sobolevCoordinates_dualPresentation. Subtype extensionality
  gives equality in the common-model Sobolev completion. -/
  apply Subtype.ext
  exact (A.sobolevCoordinates_dualPresentation s α).symm

/-- The common-model localized distribution is the Bessel realization of the original dual tuple. -/
theorem localDistribution_dualSobolevEquiv (s : ℝ) (j : Fin A.size)
    (α : A.DualSobolevSpace s) :
    A.dualPresentation.localDistribution s j (A.dualSobolevEquiv s α) =
      besselRealization n r s (α.val j) := by
  /- The isometry of equal subspaces leaves every ambient coordinate unchanged.
  The common localDistribution is defined by applying the inverse Bessel weight
  to this j-th coordinate. Thus the represented localized distribution is unchanged. -/
  rfl

end SmoothBundlePresentation

end AtiyahSinger

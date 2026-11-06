/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialAdjoint
public import AtiyahSinger.Analysis.PseudodifferentialDensity
public import AtiyahSinger.Analysis.SmoothSectionMultiplication

/-!
# Exact density conjugation of formal transposes and Hermitian adjoints

Public module ID: M0637.

If dν=w dμ, the actual new formal transpose is w⁻¹ Pᵗ w.
With fixed smooth Hermitian metrics the same formula holds for the adjoint.
Multiplication by w identifies the new smooth weak kernel with the old one.
The formal operators generally differ, while their smooth weak kernels are
canonically linearly equivalent and hence have the same dimension.
Sources: SG III.3 (3.18), III.5 (5.1)--(5.2), pp.194--195.
The conjugation and kernel comparisons are project deductions from the integral identities.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

section

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

namespace PseudodifferentialOperator

variable {μ} {m : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- The actual bilinear transpose changes by reciprocal scalar conjugation. -/
theorem formalTranspose_changeMeasure :
    (P.changeMeasure ν).formalTranspose.toLinearMap =
      (smoothSectionMul (n := n) (r := r) (DualBundle E)
        (fun x ↦ (smoothDensityRatio (n := n) ν μ x : ℂ))
        (contMDiff_complex_smoothDensityRatio ν μ)).comp
        (P.formalTranspose.toLinearMap.comp
          (smoothSectionMul (n := n) (r := q) (DualBundle F)
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν))) := by
  /- Rewrite the ν pairing as the μ pairing with weight w=dν/dμ.
  Apply the original formal pairing identity to w times the test. Multiplication
  by the positive reciprocal moves the result back to the ν convention.
  The real weight has no conjugation change in the Hermitian identity. Uniqueness
  of the specified formal operator identifies the candidate on all smooth tests. -/
  let B := smoothSectionMul (n := n) (r := q) (DualBundle F)
    (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
    (contMDiff_complex_smoothDensityRatio μ ν)
  have hcancel (x : M) : (smoothDensityRatio (n := n) μ ν x : ℂ) *
      (smoothDensityRatio (n := n) ν μ x : ℂ) = 1 := by
    rw [smoothDensityRatio_swap (n := n) μ ν x, Complex.ofReal_inv]
    exact mul_inv_cancel₀ (by exact_mod_cast (smoothDensityRatio_pos (n := n) μ ν x).ne')
  -- The candidate is compared among all smooth-section maps, so no composition theorem is needed.
  apply IsFormalTranspose.unique (μ := ν) (P.changeMeasure ν).toLinearMap
    (P.changeMeasure ν).formalTranspose.toLinearMap _
    (P.changeMeasure ν).isFormalTranspose_formalTransposeLinearMap
  intro α u
  change (∫ x, ((smoothDensityRatio (n := n) ν μ x : ℂ) •
    (P.formalTranspose.toLinearMap (B α)).val x) (u.val x) ∂ν) =
      ∫ x, α.val x ((P.toLinearMap u).val x) ∂ν
  rw [integral_smoothDensityRatio (n := n) μ ν,
    integral_smoothDensityRatio (n := n) μ ν]
  -- Reciprocal density cancels pointwise on the output; the input retains the same multiplier.
  calc
    _ = ∫ x, (P.formalTranspose.toLinearMap (B α)).val x (u.val x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_apply, smul_eq_mul, ← mul_assoc, hcancel, one_mul]
    _ = ∫ x, (B α).val x ((P.toLinearMap u).val x) ∂μ :=
      P.isFormalTranspose_formalTransposeLinearMap (B α) u
    _ = _ := rfl

/-- A new-density kernel vector is exactly an old-density kernel vector after multiplying by w. -/
theorem mem_ker_formalTranspose_changeMeasure_iff
    (u : smoothSections (n := n) (r := q) (DualBundle F)) :
    u ∈ (P.changeMeasure ν).formalTranspose.toLinearMap.ker ↔
      smoothSectionMul (n := n) (r := q) (DualBundle F)
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν) u ∈ P.formalTranspose.toLinearMap.ker := by
  /- Substitute the exact conjugation formula. Multiplication by w⁻¹ on
  the output is injective since w is everywhere positive. Thus its product
  with P's original formal operator vanishes exactly when that operator vanishes. -/
  rw [P.formalTranspose_changeMeasure ν]
  have hinjective := (smoothSectionMul_bijective (n := n) (r := r)
    (DualBundle E)
    (fun x ↦ (smoothDensityRatio (n := n) ν μ x : ℂ))
    (contMDiff_complex_smoothDensityRatio ν μ)
    (fun x ↦ by exact_mod_cast (smoothDensityRatio_pos (n := n) ν μ x).ne')).1
  change _ = 0 ↔ _ = 0
  exact hinjective.eq_iff' (map_zero _)

/-- The canonical kernel isomorphism is uniquely specified by the genuine multiplier w. -/
theorem existsUnique_formalTransposeKerDensityEquiv :
    ∃! T : (P.changeMeasure ν).formalTranspose.toLinearMap.ker ≃ₗ[ℂ]
        P.formalTranspose.toLinearMap.ker,
      ∀ u, (T u).val = smoothSectionMul (n := n) (r := q) (DualBundle F)
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν) u.val := by
  /- Restrict multiplication by w using the preceding kernel criterion.
  Multiplication by w⁻¹ gives its inverse, preserving smoothness and the
  reversed kernel criterion. The displayed underlying section values determine
  every output subtype, so they uniquely determine this linear equivalence. -/
  let B := smoothSectionMul (n := n) (r := q) (DualBundle F)
    (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
    (contMDiff_complex_smoothDensityRatio μ ν)
  have hB : Function.Bijective B := smoothSectionMul_bijective (n := n) (r := q)
    (DualBundle F) _ _ (fun x ↦ by
      exact_mod_cast (smoothDensityRatio_pos (n := n) μ ν x).ne')
  -- Restrict this actual multiplier using the proved equivalence of the two kernel conditions.
  let T : (P.changeMeasure ν).formalTranspose.toLinearMap.ker →ₗ[ℂ]
      P.formalTranspose.toLinearMap.ker :=
    { toFun := fun u ↦
        ⟨B u.val, (P.mem_ker_formalTranspose_changeMeasure_iff ν u.val).mp u.property⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        exact map_add B u.val v.val
      map_smul' := by
        intro a u
        apply Subtype.ext
        exact map_smul B a u.val }
  have hT : Function.Bijective T := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact hB.1 (congrArg Subtype.val huv)
    · intro u
      obtain ⟨v, hv⟩ := hB.2 u.val
      have hvker : v ∈ (P.changeMeasure ν).formalTranspose.toLinearMap.ker :=
        (P.mem_ker_formalTranspose_changeMeasure_iff ν v).mpr (by rw [hv]; exact u.property)
      exact ⟨⟨v, hvker⟩, Subtype.ext hv⟩
  refine ⟨LinearEquiv.ofBijective T hT, fun _ ↦ rfl, ?_⟩
  -- Values in the ambient smooth-section space uniquely determine the restricted equivalence.
  intro R hR
  apply LinearEquiv.ext
  intro u
  exact Subtype.ext (hR u)

/-- The chosen canonical kernel comparison, whose section values are specified by multiplication. -/
def formalTransposeKerDensityEquiv :
    (P.changeMeasure ν).formalTranspose.toLinearMap.ker ≃ₗ[ℂ] P.formalTranspose.toLinearMap.ker :=
  Classical.choose (P.existsUnique_formalTransposeKerDensityEquiv ν).exists

/-- The canonical kernel comparison sends each vector to w times that same section. -/
theorem formalTransposeKerDensityEquiv_apply
    (u : (P.changeMeasure ν).formalTranspose.toLinearMap.ker) :
    (P.formalTransposeKerDensityEquiv ν u).val = smoothSectionMul (n := n) (r := q) (DualBundle F)
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν) u.val := by
  /- Apply the defining witness property of the unique kernel equivalence.
  This retains the actual multiplier rather than merely asserting existence
  of some abstract isomorphism between vector spaces of the same dimension. -/
  exact (P.existsUnique_formalTransposeKerDensityEquiv ν).exists.choose_spec u

/-- Smooth formal-kernel dimension is independent of density even before assuming ellipticity. -/
theorem finrank_ker_formalTranspose_changeMeasure :
    Module.finrank ℂ (P.changeMeasure ν).formalTranspose.toLinearMap.ker =
      Module.finrank ℂ P.formalTranspose.toLinearMap.ker := by
  /- The canonical multiplier is a complex-linear equivalence of these kernels.
  Linear equivalence preserves finrank without a finite-dimensionality assumption.
  Ellipticity is still needed elsewhere to justify the finite-kernel index formula. -/
  exact (P.formalTransposeKerDensityEquiv ν).finrank_eq

end PseudodifferentialOperator

end

section

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
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

variable [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]

include hHE hHF hM hT2 hSC hC hE hF hμ hν

namespace PseudodifferentialOperator

variable {μ} {m : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The actual formalAdjoint changes by reciprocal scalar conjugation, with fixed fiber metrics. -/
theorem formalAdjoint_changeMeasure :
    (P.changeMeasure ν).formalAdjoint.toLinearMap =
      (smoothSectionMul (n := n) (r := r) E
        (fun x ↦ (smoothDensityRatio (n := n) ν μ x : ℂ))
        (contMDiff_complex_smoothDensityRatio ν μ)).comp
        (P.formalAdjoint.toLinearMap.comp
          (smoothSectionMul (n := n) (r := q) F
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν))) := by
  /- Rewrite the ν pairing as the μ pairing with weight w=dν/dμ.
  Apply the original formal pairing identity to w times the test. Multiplication
  by the positive reciprocal moves the result back to the ν convention.
  The real weight has no conjugation change in the Hermitian identity. Uniqueness
  of the specified formal operator identifies the candidate on all smooth tests. -/
  let B := smoothSectionMul (n := n) (r := q) F
    (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
    (contMDiff_complex_smoothDensityRatio μ ν)
  let T := (smoothSectionMul (n := n) (r := r) E
    (fun x ↦ (smoothDensityRatio (n := n) ν μ x : ℂ))
    (contMDiff_complex_smoothDensityRatio ν μ)).comp
      (P.formalAdjoint.toLinearMap.comp B)
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let k := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  have hspec : IsMetricFormalAdjoint h k ν P.toLinearMap
      (P.changeMeasure ν).formalAdjoint.toLinearMap := by
    intro u v
    simpa only [h, k, sectionPairing_ofInnerProduct, toLinearMap_changeMeasure] using
      (P.changeMeasure ν).isFormalAdjoint_formalAdjoint u v
  -- Smooth-map uniqueness permits this exact conjugation without assuming PDO composition.
  apply hspec.unique
  intro u v
  change (∫ x, inner ℂ ((P.toLinearMap u).val x) (v.val x) ∂ν) =
    ∫ x, inner ℂ (u.val x) ((T v).val x) ∂ν
  have hcancel (x : M) : (smoothDensityRatio (n := n) μ ν x : ℂ) *
      (smoothDensityRatio (n := n) ν μ x : ℂ) = 1 := by
    rw [smoothDensityRatio_swap (n := n) μ ν x, Complex.ofReal_inv]
    exact mul_inv_cancel₀ (by exact_mod_cast (smoothDensityRatio_pos (n := n) μ ν x).ne')
  rw [integral_smoothDensityRatio (n := n) μ ν,
    integral_smoothDensityRatio (n := n) μ ν]
  -- The real density acts in the linear input of each Hermitian pairing.
  calc
    _ = ∫ x, inner ℂ ((P.toLinearMap u).val x) ((B v).val x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact (inner_smul_right _ _ _).symm
    _ = ∫ x, inner ℂ (u.val x) ((P.formalAdjoint.toLinearMap (B v)).val x) ∂μ :=
      P.isFormalAdjoint_formalAdjoint u (B v)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      change inner ℂ (u.val x) ((P.formalAdjoint.toLinearMap (B v)).val x) =
        (smoothDensityRatio (n := n) μ ν x : ℂ) *
          inner ℂ (u.val x) ((smoothDensityRatio (n := n) ν μ x : ℂ) •
            (P.formalAdjoint.toLinearMap (B v)).val x)
      rw [inner_smul_right, ← mul_assoc, hcancel, one_mul]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- A new-density kernel vector is exactly an old-density kernel vector after multiplying by w. -/
theorem mem_ker_formalAdjoint_changeMeasure_iff
    (u : smoothSections (n := n) (r := q) F) :
    u ∈ (P.changeMeasure ν).formalAdjoint.toLinearMap.ker ↔
      smoothSectionMul (n := n) (r := q) F
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν) u ∈ P.formalAdjoint.toLinearMap.ker := by
  /- Substitute the exact conjugation formula. Multiplication by w⁻¹ on
  the output is injective since w is everywhere positive. Thus its product
  with P's original formal operator vanishes exactly when that operator vanishes. -/
  rw [P.formalAdjoint_changeMeasure ν]
  have hinjective := (smoothSectionMul_bijective (n := n) (r := r)
    E
    (fun x ↦ (smoothDensityRatio (n := n) ν μ x : ℂ))
    (contMDiff_complex_smoothDensityRatio ν μ)
    (fun x ↦ by exact_mod_cast (smoothDensityRatio_pos (n := n) ν μ x).ne')).1
  change _ = 0 ↔ _ = 0
  exact hinjective.eq_iff' (map_zero _)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The canonical kernel isomorphism is uniquely specified by the genuine multiplier w. -/
theorem existsUnique_formalAdjointKerDensityEquiv :
    ∃! T : (P.changeMeasure ν).formalAdjoint.toLinearMap.ker ≃ₗ[ℂ]
        P.formalAdjoint.toLinearMap.ker,
      ∀ u, (T u).val = smoothSectionMul (n := n) (r := q) F
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν) u.val := by
  /- Restrict multiplication by w using the preceding kernel criterion.
  Multiplication by w⁻¹ gives its inverse, preserving smoothness and the
  reversed kernel criterion. The displayed underlying section values determine
  every output subtype, so they uniquely determine this linear equivalence. -/
  let B := smoothSectionMul (n := n) (r := q) F
    (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
    (contMDiff_complex_smoothDensityRatio μ ν)
  have hB : Function.Bijective B := smoothSectionMul_bijective (n := n) (r := q)
    F _ _ (fun x ↦ by
      exact_mod_cast (smoothDensityRatio_pos (n := n) μ ν x).ne')
  -- Restrict this actual multiplier using the proved equivalence of the two kernel conditions.
  let T : (P.changeMeasure ν).formalAdjoint.toLinearMap.ker →ₗ[ℂ]
      P.formalAdjoint.toLinearMap.ker :=
    { toFun := fun u ↦ ⟨B u.val, (P.mem_ker_formalAdjoint_changeMeasure_iff ν u.val).mp u.property⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        exact map_add B u.val v.val
      map_smul' := by
        intro a u
        apply Subtype.ext
        exact map_smul B a u.val }
  have hT : Function.Bijective T := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact hB.1 (congrArg Subtype.val huv)
    · intro u
      obtain ⟨v, hv⟩ := hB.2 u.val
      have hvker : v ∈ (P.changeMeasure ν).formalAdjoint.toLinearMap.ker :=
        (P.mem_ker_formalAdjoint_changeMeasure_iff ν v).mpr (by rw [hv]; exact u.property)
      exact ⟨⟨v, hvker⟩, Subtype.ext hv⟩
  refine ⟨LinearEquiv.ofBijective T hT, fun _ ↦ rfl, ?_⟩
  -- Values in the ambient smooth-section space uniquely determine the restricted equivalence.
  intro R hR
  apply LinearEquiv.ext
  intro u
  exact Subtype.ext (hR u)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The chosen canonical kernel comparison, whose section values are specified by multiplication. -/
def formalAdjointKerDensityEquiv :
    (P.changeMeasure ν).formalAdjoint.toLinearMap.ker ≃ₗ[ℂ] P.formalAdjoint.toLinearMap.ker :=
  Classical.choose (P.existsUnique_formalAdjointKerDensityEquiv ν).exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The canonical kernel comparison sends each vector to w times that same section. -/
theorem formalAdjointKerDensityEquiv_apply
    (u : (P.changeMeasure ν).formalAdjoint.toLinearMap.ker) :
    (P.formalAdjointKerDensityEquiv ν u).val = smoothSectionMul (n := n) (r := q) F
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν) u.val := by
  /- Apply the defining witness property of the unique kernel equivalence.
  This retains the actual multiplier rather than merely asserting existence
  of some abstract isomorphism between vector spaces of the same dimension. -/
  exact (P.existsUnique_formalAdjointKerDensityEquiv ν).exists.choose_spec u

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Smooth formal-kernel dimension is independent of density even before assuming ellipticity. -/
theorem finrank_ker_formalAdjoint_changeMeasure :
    Module.finrank ℂ (P.changeMeasure ν).formalAdjoint.toLinearMap.ker =
      Module.finrank ℂ P.formalAdjoint.toLinearMap.ker := by
  /- The canonical multiplier is a complex-linear equivalence of these kernels.
  Linear equivalence preserves finrank without a finite-dimensionality assumption.
  Ellipticity is still needed elsewhere to justify the finite-kernel index formula. -/
  exact (P.formalAdjointKerDensityEquiv ν).finrank_eq

end PseudodifferentialOperator

end

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanTopFormIntegralNaturality
public import AtiyahSinger.Geometry.OrthogonalStereographic
public import AtiyahSinger.Geometry.DeRhamComplex

/-!
# Native sphere-chart integration and the orthogonal action

Public module ID: M1442.

The native stereographic frame is related to the explicit horizontal frame by
its actual orthogonal coordinate change. The original sphere action therefore
acts by the conjugate of its original matrix, preserving that matrix's determinant.
The coordinate formula for the specified smooth pullback and signed linear change
of variables give the integral transformation law in the original native chart.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff Manifold Topology

set_option maxHeartbeats 1500000 in
-- The actual native frame, horizontal isometry and tensor pullback are retained throughout.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native top-chart integration transforms by the determinant of the original orthogonal action. -/
theorem euclideanTopFormIntegral_spherePullback (n : ℕ)
    (A : Matrix.orthogonalGroup (Fin n) ℝ)
    (form : SmoothDifferentialForm (n := n) (OrthogonalSphere n) n) :
    euclideanTopFormIntegral n (differentialFormInChart
      (smoothFormPullback (fun x : OrthogonalSphere n ↦ A • x)
        (contMDiff_orthogonalSphere_smul n A) n form).val
      (stereographic' n (orthogonalSphereNorth n))) =
      (A.val.det : ℂ) * euclideanTopFormIntegral n (differentialFormInChart form.val
        (stereographic' n (orthogonalSphereNorth n))) := by
  classical
  let S := OrthogonalSphere n
  let V := EuclideanSpace ℝ (Fin n)
  let north := orthogonalSphereNorth n
  let c := stereographic' n north
  let H := orthogonalSphereHorizontalIsometry n
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    n (ne_zero_of_mem_unit_sphere north)).repr
  let e := U.symm.trans H
  let O := orthogonalEuclideanIsometry n A
  let B := (e.trans (O.trans e.symm)).toContinuousLinearEquiv
  have hc : c ∈ atlas V S := ⟨north, rfl⟩
  have hct : c.target = univ := stereographic'_target north
  -- The horizontal chart and native chart use the very same stereographic projection.
  have hchart (x : S) : orthogonalSphereStereographic n x = e (c x) := by
    simp [orthogonalSphereStereographic, stereographic', e, U, H, c, north]
  have hsource (x : S) (hx : x ∈ c.source) : A • x ∈ c.source := by
    rw [stereographic'_source, mem_compl_iff, mem_singleton_iff] at hx ⊢
    intro h
    have h' := congrArg (fun y : S ↦ A⁻¹ • y) h
    apply hx
    change A⁻¹ • (A • x) = A⁻¹ • orthogonalSphereNorth n at h'
    rw [inv_smul_smul, smul_orthogonalSphereNorth] at h'
    exact h'
  have hcoords : (c ∘ (fun x : S ↦ A • x) ∘ c.symm) = B := by
    funext z
    have hz : c.symm z ∈ c.source := c.map_target (hct.symm ▸ mem_univ z)
    apply e.injective
    change e (c (A • c.symm z)) = e (B z)
    rw [← hchart]
    have h := (orthogonalSphereStereographic_properties n).2.2 A (c.symm z) ?_
    · rw [h, hchart, c.right_inv (hct.symm ▸ mem_univ z)]
      exact (e.apply_symm_apply (O (e z))).symm
    · simpa only [orthogonalSphereStereographic, c, stereographic',
        OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
        preimage_univ, inter_univ] using hz
  -- Conjugation by that specified frame preserves the original matrix determinant.
  have hdetO : LinearMap.det O.toLinearEquiv.toLinearMap = A.val.det := by
    change LinearMap.det (Matrix.toEuclideanLin A.val) = A.val.det
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hdetB : LinearMap.det B.toLinearMap = A.val.det := by
    have h := LinearMap.det_conj O.toLinearEquiv.toLinearMap e.symm.toLinearEquiv
    exact h.trans hdetO
  have habs : |LinearMap.det B.toLinearMap| = 1 := by
    rw [hdetB]
    have hunit := Matrix.det_of_mem_unitary A.property
    have hsquare : A.val.det * A.val.det = 1 := by
      simpa only [star_trivial] using hunit.1
    have h := congrArg abs hsquare
    rw [abs_mul, abs_one] at h
    nlinarith [abs_nonneg A.val.det]
  -- The original smooth pullback has precisely the usual coefficient pullback by B.
  have hcoeff : differentialFormInChart
      (smoothFormPullback (fun x : S ↦ A • x) (contMDiff_orthogonalSphere_smul n A)
        n form).val c = fun z ↦
      (differentialFormInChart form.val c (B z)).compContinuousLinearMap
        B.toContinuousLinearMap := by
    have hraw : (smoothFormPullback (fun x : S ↦ A • x)
        (contMDiff_orthogonalSphere_smul n A) n form).val = fun x ↦
        (form.val (A • x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (fun x : S ↦ A • x) x) := by
      funext x
      exact smoothFormPullback_apply _ _ _ _ _
    rw [hraw]
    funext z
    rw [differentialFormPullback_inChart _ (contMDiff_orthogonalSphere_smul n A)
      form.val c hc c hc z (hct.symm ▸ mem_univ z)
        (hsource (c.symm z) (c.map_target (hct.symm ▸ mem_univ z))), hcoords]
    rw [B.fderiv]
  rw [hcoeff, euclideanTopFormIntegral_pullback n B habs, hdetB]

end AtiyahSinger

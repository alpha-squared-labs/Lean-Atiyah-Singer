/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import AtiyahSinger.Geometry.OrthogonalGroupManifold
public import AtiyahSinger.Geometry.SphereCotangentPoleCoordinates
public import AtiyahSinger.Topology.EquivariantProperHomotopy

/-!
# Reciprocal rescaling in the actual Euclidean cotangent coordinates

The inverse-dual lift of a nonzero real dilation multiplies the real Bott
coordinate by that scalar and the imaginary coordinate by its reciprocal.
For a positive scalar, the original equivariant compact-support pullback is
the identity: the interpolation is a homeomorphism of the entire cylinder.

This keeps the factor-two normalization in the frame-sphere pole comparison
without treating cotangent vectors as tangent vectors. The positive homotopy
uses the original orthogonal representation, including rank zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology
open scoped Manifold ContDiff unitInterval Matrix.Norms.L2Operator

/-- The base coordinate dilates by `c`; its inverse-dual vector coordinate dilates by `c⁻¹`. -/
def euclideanComplexReciprocalScale (r : ℕ) (c : ℝ) (hc : c ≠ 0) :
    EuclideanSpace ℂ (Fin r) ≃ₜ EuclideanSpace ℂ (Fin r) :=
  let R := euclideanComplexRealProductHomeomorph r
  let d := (Homeomorph.smulOfNeZero c hc).prodCongr
    (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc))
  (R.trans d).trans R.symm

set_option maxHeartbeats 600000 in
-- Both native Hom-bundle coordinates are compared with the actual inverse differential.
/-- The inverse-dual cotangent lift of a real dilation is the specified reciprocal rescaling. -/
theorem cotangentDiffeomorph_smul_complex (r : ℕ) (c : ℝ) (hc : c ≠ 0)
    (z : EuclideanSpace ℂ (Fin r)) :
    let d := (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin r)) c hc).toContinuousLinearEquiv
    cotangentDiffeomorph d.toDiffeomorph ((euclideanCotangentComplexHomeomorph r).symm z) =
      (euclideanCotangentComplexHomeomorph r).symm (euclideanComplexReciprocalScale r c hc z) := by
  let E := EuclideanSpace ℝ (Fin r)
  let R := euclideanComplexRealProductHomeomorph r
  let d := (LinearEquiv.smulOfNeZero ℝ E c hc).toContinuousLinearEquiv
  have hD (x : E) : mfderiv (𝓡 r) (𝓡 r) d.toDiffeomorph.symm x =
      d.symm.toContinuousLinearMap := d.symm.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.mfderiv
  have hRiesz (w : EuclideanSpace ℂ (Fin r)) :
      (euclideanCotangentComplexHomeomorph r).symm w =
        (⟨(R w).1, innerSL ℝ (R w).2⟩ : CotangentTotalSpace (n := r) (M := E)) := rfl
  have hscale : R (euclideanComplexReciprocalScale r c hc z) =
      (c • (R z).1, c⁻¹ • (R z).2) := R.apply_symm_apply _
  rw [hRiesz, hRiesz, hscale]
  change (⟨d (R z).1, (innerSL ℝ (R z).2).comp
    (mfderiv (𝓡 r) (𝓡 r) d.toDiffeomorph.symm (d (R z).1))⟩ :
      CotangentTotalSpace (n := r) (M := E)) = _
  rw [hD]
  apply TotalSpace.ext
  · rfl
  · apply heq_of_eq
    ext w
    change inner ℝ (R z).2 (c⁻¹ • w) = inner ℝ (c⁻¹ • (R z).2) w
    exact (real_inner_smul_right ((R z).2) (show E from w) c⁻¹).trans
      (real_inner_smul_left ((R z).2) (show E from w) c⁻¹).symm

set_option maxHeartbeats 1000000 in
-- Coordinate equivariance retains the original real matrix action on both complex components.
/-- Reciprocal real rescaling commutes with the original complexified orthogonal action. -/
theorem euclideanComplexReciprocalScale_equivariant (r : ℕ) (c : ℝ) (hc : c ≠ 0)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)) :
    euclideanComplexReciprocalScale r c hc (orthogonalComplexificationRepresentation r A z) =
      orthogonalComplexificationRepresentation r A (euclideanComplexReciprocalScale r c hc z) := by
  let R := euclideanComplexRealProductHomeomorph r
  let Q := orthogonalEuclideanIsometry r A
  have hcoords (w : EuclideanSpace ℂ (Fin r)) :
      R (orthogonalComplexificationRepresentation r A w) = (Q (R w).1, Q (R w).2) := by
    apply Prod.ext
    · ext i
      change (∑ j, (A.val i j : ℂ) * w j).re = ∑ j, A.val i j * (w j).re
      simp
    · ext i
      change (∑ j, (A.val i j : ℂ) * w j).im = ∑ j, A.val i j * (w j).im
      simp
  have hscale (w : EuclideanSpace ℂ (Fin r)) :
      R (euclideanComplexReciprocalScale r c hc w) =
        (c • (R w).1, c⁻¹ • (R w).2) := R.apply_symm_apply _
  apply R.injective
  rw [hscale, hcoords, hcoords, hscale]
  simp only [Q.map_smul]

attribute [local instance] compactSpace_orthogonalGroup

set_option maxHeartbeats 1200000 in
-- The original equivariant support quotient sees one proper cylinder, not only proper slices.
/-- Positive reciprocal rescaling acts identically on the original equivariant support group. -/
theorem equivariantSupportTripleKZeroPullback_reciprocalScale (r : ℕ) (c : ℝ) (hc : 0 < c) :
    let d := euclideanComplexReciprocalScale r c hc.ne'
    equivariantSupportTripleKZeroPullback ⟨d, d.continuous⟩
      (euclideanComplexReciprocalScale_equivariant r c hc.ne') d.isProperMap =
        AddMonoidHom.id
          (EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
            (EuclideanSpace ℂ (Fin r))) := by
  let E := EuclideanSpace ℝ (Fin r)
  let W := EuclideanSpace ℂ (Fin r)
  let R := euclideanComplexRealProductHomeomorph r
  let s (t : I) : ℝ := (1 - (t : ℝ)) + (t : ℝ) * c
  have hs (t : I) : 0 < s t := by
    dsimp only [s]
    by_cases ht : (t : ℝ) = 0
    · simp only [ht, sub_zero, zero_mul, add_zero, zero_lt_one]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hc)
  have hscont : Continuous s := by fun_prop
  -- The actual inverse keeps time fixed and uses the reciprocal pair in reverse order.
  let A : I × (E × E) ≃ₜ I × (E × E) := {
    toFun z := (z.1, s z.1 • z.2.1, (s z.1)⁻¹ • z.2.2)
    invFun z := (z.1, (s z.1)⁻¹ • z.2.1, s z.1 • z.2.2)
    left_inv z := by
      change (z.1, (s z.1)⁻¹ • (s z.1 • z.2.1),
        s z.1 • ((s z.1)⁻¹ • z.2.2)) = z
      rw [smul_smul, smul_smul, inv_mul_cancel₀ (hs z.1).ne',
        mul_inv_cancel₀ (hs z.1).ne', one_smul, one_smul]
    right_inv z := by
      change (z.1, s z.1 • ((s z.1)⁻¹ • z.2.1),
        (s z.1)⁻¹ • (s z.1 • z.2.2)) = z
      rw [smul_smul, smul_smul, mul_inv_cancel₀ (hs z.1).ne',
        inv_mul_cancel₀ (hs z.1).ne', one_smul, one_smul]
    continuous_toFun := continuous_fst.prodMk
      (((hscont.comp continuous_fst).smul continuous_snd.fst).prodMk
        (((hscont.comp continuous_fst).inv₀ (fun z ↦ (hs z.1).ne')).smul continuous_snd.snd))
    continuous_invFun := continuous_fst.prodMk
      ((((hscont.comp continuous_fst).inv₀ (fun z ↦ (hs z.1).ne')).smul
        continuous_snd.fst).prodMk ((hscont.comp continuous_fst).smul continuous_snd.snd)) }
  let B := (Homeomorph.refl I).prodCongr R
  let C := (B.trans A).trans B.symm
  let d := euclideanComplexReciprocalScale r c hc.ne'
  let H : ContinuousMap.Homotopy (ContinuousMap.id W) (⟨d, d.continuous⟩ : C(W, W)) := {
    toFun z := (C z).2
    continuous_toFun := continuous_snd.comp C.continuous
    map_zero_left z := by
      change R.symm (s 0 • (R z).1, (s 0)⁻¹ • (R z).2) = z
      simp only [s, (show ((0 : I) : ℝ) = 0 from rfl), sub_zero, zero_mul, add_zero,
        inv_one, one_smul]
      exact R.symm_apply_apply z
    map_one_left z := by
      change R.symm (s 1 • (R z).1, (s 1)⁻¹ • (R z).2) = d z
      simp only [s, (show ((1 : I) : ℝ) = 1 from rfl), sub_self, one_mul, zero_add]
      rfl }
  have hproper : IsProperMap H := isProperMap_snd_of_compactSpace.comp C.isProperMap
  have hequiv (t : I) (g : Matrix.orthogonalGroup (Fin r) ℝ) (z : W) :
      H (t, orthogonalComplexificationRepresentation r g z) =
        orthogonalComplexificationRepresentation r g (H (t, z)) :=
    euclideanComplexReciprocalScale_equivariant r (s t) (hs t).ne' g z
  -- Proper homotopy invariance now applies to the original inverse-dual endpoint itself.
  have h := equivariantSupportTripleKZeroPullback_eq_of_proper_homotopy
    (ContinuousMap.id W) ⟨d, d.continuous⟩ (fun _ _ ↦ rfl)
    (euclideanComplexReciprocalScale_equivariant r c hc.ne')
    isProperMap_id d.isProperMap H hequiv hproper
  rw [equivariantSupportTripleKZeroPullback_id] at h
  exact h.symm

end AtiyahSinger

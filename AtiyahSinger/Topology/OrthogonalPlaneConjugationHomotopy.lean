/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalComplexification
public import AtiyahSinger.Topology.CompactSupportHomotopy

/-!
# Proper conjugation homotopy on the complexified real rotation plane

Public module ID: M1983.

Keep the real part fixed and rotate the imaginary part through a half turn.
The actual real two-dimensional special orthogonal matrices commute with this
rotation. Its preservation of the native Euclidean norm controls the whole
cylinder, including all intermediate times. This is the geometric argument
for ASI I, Lemma (2.8), on the complexification of the real plane.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

/-- The actual coordinate conjugation is properly SO(2)-equivariantly homotopic to identity. -/
theorem exists_proper_specialOrthogonalPlaneConjugation_homotopy :
    ∃ H : ContinuousMap.Homotopy (ContinuousMap.id (EuclideanSpace ℂ (Fin 2)))
        (orthogonalComplexificationConjugation 2),
      IsProperMap H ∧ ∀ (t : I) (A : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
        (z : EuclideanSpace ℂ (Fin 2)), H (t, A • z) = A • H (t, z) := by
  let V := EuclideanSpace ℂ (Fin 2)
  let h (t : I) (z : V) : V := WithLp.toLp 2
    ![(z 0).re + Complex.I *
        (Real.cos (Real.pi * t) * (z 0).im - Real.sin (Real.pi * t) * (z 1).im),
      (z 1).re + Complex.I *
        (Real.sin (Real.pi * t) * (z 0).im + Real.cos (Real.pi * t) * (z 1).im)]
  have hc : Continuous (fun p : I × V ↦ h p.1 p.2) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℂ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp only [h, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    all_goals dsimp only [V]
    all_goals fun_prop
  have hzero (z : V) : h 0 z = z := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp [h]
  have hone (z : V) : h 1 z = orthogonalComplexificationConjugation 2 z := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp [h, orthogonalComplexificationConjugation]
  let H : ContinuousMap.Homotopy (ContinuousMap.id V)
      (orthogonalComplexificationConjugation 2) := {
    toFun := h.uncurry
    continuous_toFun := hc
    map_zero_left := hzero
    map_one_left := hone }
  -- The two imaginary coordinates rotate together; their sum of squares is unchanged.
  have hnorm (t : I) (z : V) : ‖h t z‖ = ‖z‖ := by
    have hs : ‖h t z‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_two, ← Complex.normSq_eq_norm_sq]
      have htrig := Real.sin_sq_add_cos_sq (Real.pi * (t : ℝ))
      have heq : (z 0).re ^ 2 +
          (Real.cos (Real.pi * t) * (z 0).im - Real.sin (Real.pi * t) * (z 1).im) ^ 2 +
          ((z 1).re ^ 2 +
            (Real.sin (Real.pi * t) * (z 0).im + Real.cos (Real.pi * t) * (z 1).im) ^ 2) =
          (z 0).re ^ 2 + (z 0).im ^ 2 + ((z 1).re ^ 2 + (z 1).im ^ 2) := by
        linear_combination ((z 0).im ^ 2 + (z 1).im ^ 2) * htrig
      simpa [h, Complex.normSq_apply, pow_two, -Complex.ofReal_mul,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re] using heq
    nlinarith [norm_nonneg (h t z), norm_nonneg z]
  refine ⟨H, ?_, ?_⟩
  · -- A single closed ball controls the inverse image at every time in the compact interval.
    apply (isProperMap_homotopy_iff H).mpr
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : V)
    refine ⟨Metric.closedBall (0 : V) R, isCompact_closedBall _ _, ?_⟩
    intro t z hz
    have hn := hR hz
    change dist (h t z) 0 ≤ R at hn
    change dist z 0 ≤ R
    simpa only [dist_zero_right, hnorm] using hn
  · -- The native determinant-one condition gives exactly the real rotation matrix form.
    intro t A z
    obtain ⟨hdiag, hoff, _⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp A.property
    have haction (w : V) (i : Fin 2) :
        (A • w) i = (A.val i 0 : ℂ) * w 0 + (A.val i 1 : ℂ) * w 1 := by
      change (∑ j, (A.val i j : ℂ) * w j) = _
      rw [Fin.sum_univ_two]
    change h t (A • z) = A • h t z
    ext i
    fin_cases i <;> rw [haction]
    all_goals
      simp only [h, Matrix.cons_val_zero, Matrix.cons_val_one, haction]
      apply Complex.ext <;> simp [hdiag, hoff] <;> ring

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CircleCotangent
public import AtiyahSinger.Topology.BottLine
public import AtiyahSinger.Topology.RelativeSymbolExtension
public import AtiyahSinger.Topology.ScalarSupportHomotopy

/-!
# An affine representative for the circle point symbol

Public module ID: M1611.

In angular cotangent coordinates the scalar `(1-v) - (1+v) x/a` vanishes only
at `(a,0)`. It interpolates between the two Fourier boundary branches, after
a constant phase change. On the prescribed point tube its numerator is
`-i u - 2v`, fixing the negative Bott sign without classifying abstract generators.

This is an explicit version of the boundary comparison in ASI section 8,
Figure 3. Compact controls and the original angular covector are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  trivialTopology isFiniteRank_trivial

local notation "CT" => CotangentTotalSpace (n := 1) (M := Circle)
local notation "L" => Bundle.Trivial CT (Fin 1 → ℂ)

/-- The explicit affine scalar on the original circle cotangent bundle. -/
def circleAffineScalar (a : Circle) : C(CT, ℂ) :=
  ⟨fun z ↦ (1 - (circleCotangentTrivialization z).2 : ℂ) -
      (1 + (circleCotangentTrivialization z).2 : ℂ) *
        ((circleCotangentTrivialization z).1 / a : Circle), by fun_prop⟩

/-- The affine scalar is a line symbol supported at the specified zero covector. -/
def circleAffineSymbol (a : Circle) : CompactSupportTriple L L := by
  let p := circleCotangentTrivialization.symm (a, 0)
  let c : C(({p}ᶜ : Set CT), ℂ) :=
    (circleAffineScalar a).comp ⟨Subtype.val, continuous_subtype_val⟩
  have hc (z : ({p}ᶜ : Set CT)) : c z ≠ 0 := by
    intro hz
    let x := (circleCotangentTrivialization z.val).1
    let v := (circleCotangentTrivialization z.val).2
    have heq : (1 + (v : ℂ)) * (x / a : Circle) = 1 - (v : ℂ) :=
      (sub_eq_zero.mp hz).symm
    -- Equality of the two norms forces the covector coefficient to vanish.
    have hn := congrArg (fun w : ℂ ↦ ‖w‖) heq
    have hn' : |1 + v| = |1 - v| := by
      simpa only [norm_mul, Circle.norm_coe, mul_one, ← Complex.ofReal_add,
        ← Complex.ofReal_sub, ← Complex.ofReal_one, Complex.norm_real,
        Real.norm_eq_abs] using hn
    have hv : v = 0 := by
      have hs := congrArg (fun t : ℝ ↦ t ^ 2) hn'
      rw [sq_abs, sq_abs] at hs
      nlinarith
    have hx : x = a := by
      rw [hv, Complex.ofReal_zero, add_zero, sub_zero, one_mul] at heq
      have hq : x / a = (1 : Circle) := Subtype.ext heq
      exact div_eq_one.mp hq
    apply z.property
    apply Set.mem_singleton_iff.mpr
    apply circleCotangentTrivialization.injective
    change (x, v) = circleCotangentTrivialization p
    rw [show circleCotangentTrivialization p = (a, 0) from
      circleCotangentTrivialization.apply_symm_apply (a, 0), hx, hv]
  exact scalarSupportTriple L {p} isCompact_singleton c hc

set_option maxHeartbeats 1600000 in

/-- The affine symbol is the negative positive point class through the prescribed tube. -/
theorem circleAffineSymbol_compactSupportClass (a : Circle) :
    (circleAffineSymbol a).compactSupportClass =
      -compactSupportKZeroOpenPushforward (circlePointCotangentTube a)
        (isOpenEmbedding_circlePointCotangentTube a) bottLineClass := by
  classical
  let E := Bundle.Trivial ℂ (Fin 1 → ℂ)
  let U := ({0}ᶜ : Set ℂ)
  let tube : C(ℂ, CT) :=
    ⟨circlePointCotangentTube a, (isOpenEmbedding_circlePointCotangentTube a).continuous⟩
  have hcayley (x : ℝ) :
      (1 - (x : ℂ) * Complex.I) * (Circle.exp (2 * Real.arctan x) : ℂ) =
        1 + (x : ℂ) * Complex.I := by
    have hs : Real.sin (Real.arctan x) = x * Real.cos (Real.arctan x) := by
      have ht := Real.tan_arctan x
      rw [Real.tan_eq_sin_div_cos] at ht
      exact (div_eq_iff (Real.cos_arctan_pos x).ne').mp ht
    have hsq : Real.cos (Real.arctan x) ^ 2 * (1 + x ^ 2) = 1 := by
      rw [Real.cos_sq_arctan]
      field_simp
    rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
        mul_zero, sub_zero, add_zero, zero_add, mul_one, one_mul]
    · rw [Real.cos_two_mul, Real.sin_two_mul, hs]
      nlinarith
    · rw [Real.cos_two_mul, Real.sin_two_mul, hs]
      nlinarith
  have hden (x : ℝ) : (1 - (x : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  -- The Cayley coordinate keeps the base displacement before the covector coordinate.
  have htube (w : ℂ) : circleAffineScalar a (tube w) =
      (-Complex.I * (w.re : ℂ) - 2 * (w.im : ℂ)) /
        (1 - (w.re / 2 : ℂ) * Complex.I) := by
    change (1 - (circleCotangentTrivialization (tube w)).2 : ℂ) -
      (1 + (circleCotangentTrivialization (tube w)).2 : ℂ) *
        ((circleCotangentTrivialization (tube w)).1 / a : Circle) = _
    have hcoords : circleCotangentTrivialization (tube w) =
        (a * Circle.exp (2 * Real.arctan (w.re / 2)), w.im) :=
      circleCotangentTrivialization.apply_symm_apply _
    rw [hcoords]
    simp only [mul_div_cancel_left]
    have hd : (1 - (w.re / 2 : ℂ) * Complex.I) ≠ 0 := by
      simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hden (w.re / 2)
    apply (eq_div_iff hd).mpr
    have h := hcayley (w.re / 2)
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
    calc
      _ = (1 - (w.im : ℂ)) * (1 - (w.re / 2 : ℂ) * Complex.I) -
          (1 + (w.im : ℂ)) *
            ((1 - (w.re / 2 : ℂ) * Complex.I) *
              (Circle.exp (2 * Real.arctan (w.re / 2)) : ℂ)) := by ring
      _ = _ := by rw [h]; ring
  let phase : C(unitInterval, ℂ) :=
    ⟨fun t ↦ Complex.exp (((-(1 - (t : ℝ)) * Real.pi / 2 : ℝ) : ℂ) * Complex.I),
      by fun_prop⟩
  have hphase₀ : phase 0 = -Complex.I := by
    change Complex.exp (((-(1 - (0 : ℝ)) * Real.pi / 2 : ℝ) : ℂ) * Complex.I) = _
    simp only [sub_zero, neg_one_mul]
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Complex.ofReal_neg,
      neg_mul, Complex.exp_neg]
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
    exact Complex.inv_I
  have hphase₁ : phase 1 = 1 := by simp [phase]
  let weight (p : unitInterval × U) : ℝ :=
    (1 - (p.1 : ℝ)) + (p.1 : ℝ) * ‖p.2.val‖ ^ 2
  have hweight (p : unitInterval × U) : 0 < weight p := by
    have hw : p.2.val ≠ 0 := by simpa only [U, Set.mem_compl_iff, Set.mem_singleton_iff]
      using p.2.property
    have hn : 0 < ‖p.2.val‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw) 2
    dsimp [weight]
    by_cases ht : (p.1 : ℝ) = 0
    · simp [ht]
    · have htp : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.property.1 (Ne.symm ht)
      have hp := mul_pos htp hn
      linarith [p.1.property.2]
  let denominator (p : unitInterval × U) : ℂ :=
    (1 - (((1 - (p.1 : ℝ)) * p.2.val.re / 2 : ℝ) : ℂ) * Complex.I) * weight p
  have hD (p : unitInterval × U) : denominator p ≠ 0 :=
    mul_ne_zero (hden _) (Complex.ofReal_ne_zero.mpr (hweight p).ne')
  let numerator (p : unitInterval × U) : ℂ :=
    (p.2.val.re : ℂ) - (((2 - (p.1 : ℝ)) * p.2.val.im : ℝ) : ℂ) * Complex.I
  have hN (p : unitInterval × U) : numerator p ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [numerator, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, Complex.zero_re] at hr
    simp only [numerator, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, zero_mul,
      add_zero, Complex.zero_im] at hi
    have hv : p.2.val.im = 0 := by nlinarith [p.1.property.2]
    apply p.2.property
    apply Set.mem_singleton_iff.mpr
    exact Complex.ext hr hv
  let H : C(unitInterval × U, ℂ) :=
    ⟨fun p ↦ phase p.1 * numerator p / denominator p, by
      apply Continuous.div _ _ hD
      · exact (phase.continuous.comp continuous_fst).mul (by dsimp [numerator]; fun_prop)
      · dsimp [denominator, weight]
        fun_prop⟩
  have hH (p : unitInterval × U) : H p ≠ 0 :=
    div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (hN p)) (hD p)
  have hH₀ (w : U) : H (0, w) = circleAffineScalar a (tube w.val) := by
    rw [htube]
    change phase 0 * numerator (0, w) / denominator (0, w) = _
    rw [hphase₀]
    simp only [numerator, denominator, weight, Set.Icc.coe_zero, sub_zero,
      zero_mul, add_zero, one_mul, Complex.ofReal_one, mul_one]
    congr 1
    · push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    · push_cast
      rfl
  have hH₁ (w : U) : H (1, w) = w.val⁻¹ := by
    change phase 1 * numerator (1, w) / denominator (1, w) = _
    rw [hphase₁]
    simp only [numerator, denominator, weight, Set.Icc.coe_one, sub_self,
      zero_mul, zero_div, Complex.ofReal_zero, sub_zero, zero_add,
      one_mul, show (2 : ℝ) - 1 = 1 by norm_num]
    have hconj : (w.val.re : ℂ) - (w.val.im : ℂ) * Complex.I = (starRingEnd ℂ) w.val := by
      apply Complex.ext <;> simp
    rw [hconj, Complex.inv_def, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  let c : C(U, ℂ) := H.comp ⟨fun w ↦ (0, w), continuous_const.prodMk continuous_id⟩
  let b := scalarSupportTriple E {0} isCompact_singleton c (fun w ↦ hH (0, w))
  have hb : b.compactSupportClass = -bottLineClass := by
    have hhom : b.Homotopic bottLineTriple.inverse := by
      apply CompactSupportTriple.homotopic_of_scalar E b bottLineTriple.inverse
        {0} isCompact_singleton (Set.Subset.refl _) (Set.Subset.refl _) H hH
      · intro w v
        rw [CompactSupportTriple.enlarge_apply]
        rfl
      · intro w v
        rw [CompactSupportTriple.enlarge_apply, hH₁]
        rfl
    exact (b.compactSupportClass_eq_of_homotopic bottLineTriple.inverse hhom).trans
      bottLineTriple.compactSupportClass_inverse
  have he : (circleAffineSymbol a).compactSupportClass =
      compactSupportKZeroOpenPushforward tube (isOpenEmbedding_circlePointCotangentTube a)
        b.compactSupportClass := by
    let e := (pullbackTrivialIso tube 1).symm
    refine CompactSupportTriple.compactSupportClass_eq_openPushforward b (circleAffineSymbol a)
      tube (isOpenEmbedding_circlePointCotangentTube a) ?_ e e ?_
    · intro z hz
      change z ∈ {circleCotangentTrivialization.symm (a, 0)} at hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      refine ⟨0, Set.mem_singleton 0, ?_⟩
      simp [tube, circlePointCotangentTube]
    · intro w hw htw v
      change e.linearEquiv w (H (0, ⟨w, hw⟩) • v) =
        circleAffineScalar a (tube w) • e.linearEquiv w v
      rw [map_smul, hH₀]
  rw [he, hb, map_neg]
  rfl

end AtiyahSinger

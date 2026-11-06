/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.IntegerSobolevDerivatives

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# First Sobolev energy of arbitrary product-coordinate slices

For the actual coordinate concatenation, the full joint H¹ energy plus its
zeroth-order energy equals the two integrated directional H¹ energies. The
slices are the original whole Schwartz function restricted to each affine
fiber. No separated expansion is assumed. The derivative normalization is
exactly the period-one Fourier normalization of the original Sobolev spaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1000000 in

/-- The joint H¹ energy plus its L² energy equals the two integrated affine-slice energies. -/
theorem norm_schwartzSobolevCoordinate_one_sq_product_slices
    {n m r : ℕ}
    (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
    (f : EuclideanSpace ℝ (Fin n) →
      𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin r)))
    (g : EuclideanSpace ℝ (Fin m) →
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (hf : ∀ x y, f x y = u (EuclideanSpace.finAddEquivProd.symm (x, y)))
    (hg : ∀ x y, g y x = u (EuclideanSpace.finAddEquivProd.symm (x, y))) :
    ‖schwartzSobolevCoordinate 1 u‖ ^ 2 + ‖u.toLp 2‖ ^ 2 =
      (∫ x, ‖schwartzSobolevCoordinate 1 (f x)‖ ^ 2) +
        ∫ y, ‖schwartzSobolevCoordinate 1 (g y)‖ ^ 2 := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let W := EuclideanSpace ℂ (Fin r)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let D (j : Fin (n + m)) := LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) u
  let c := (2 * Real.pi)⁻¹ ^ 2
  have hzero {d : ℕ} (v : 𝓢(EuclideanSpace ℝ (Fin d), W)) :
      schwartzSobolevCoordinate 0 v = v.toLp 2 := by
    simp only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
      SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
  have hL2 {d : ℕ} (v : 𝓢(EuclideanSpace ℝ (Fin d), W)) :
      ‖v.toLp 2‖ ^ 2 = ∫ z, ‖v z‖ ^ 2 := by
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (integral_nonneg fun z ↦ sq_nonneg _)
  have hH1 {d : ℕ} (v : 𝓢(EuclideanSpace ℝ (Fin d), W)) :
      ‖schwartzSobolevCoordinate 1 v‖ ^ 2 = ‖v.toLp 2‖ ^ 2 +
        c * ∑ j : Fin d,
          ‖(LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) v).toLp 2‖ ^ 2 := by
    simpa only [zero_add, hzero] using
      norm_schwartzSobolevCoordinate_add_one_sq d r 0 v
  -- The original concatenation preserves the Euclidean coordinate volumes.
  have he : MeasurePreserving e :=
    (WithLp.volume_preserving_ofLp X Y).comp
      ((LinearIsometryEquiv.measurePreserving
        (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m ↦ ℝ))).comp
        (LinearIsometryEquiv.measurePreserving
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm)))
  have he' : MeasurePreserving e.toHomeomorph.toMeasurableEquiv
      (volume : Measure Z) ((volume : Measure X).prod (volume : Measure Y)) := he
  have hInt (v : 𝓢(Z, W)) :
      Integrable (fun p : X × Y ↦ ‖v (e.symm p)‖ ^ 2) (volume.prod volume) :=
    by
      exact he'.symm.integrable_comp_of_integrable
        (g := fun z : Z ↦ ‖v z‖ ^ 2) ((v.memLp 2).integrable_norm_pow (by norm_num))
  have hFubini (v : 𝓢(Z, W)) :
      (∫ x : X, ∫ y : Y, ‖v (e.symm (x, y))‖ ^ 2) = ‖v.toLp 2‖ ^ 2 := by
    rw [← integral_prod _ (hInt v), hL2]
    exact he'.symm.integral_comp' (fun z : Z ↦ ‖v z‖ ^ 2)
  have hFubini' (v : 𝓢(Z, W)) :
      (∫ y : Y, ∫ x : X, ‖v (e.symm (x, y))‖ ^ 2) = ‖v.toLp 2‖ ^ 2 := by
    rw [← integral_integral_swap (hInt v)]
    exact hFubini v
  -- Coordinate basis vectors become the two original affine-fiber directions.
  have hbLeft (i : Fin n) :
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
        (EuclideanSpace.single i 1, 0) = EuclideanSpace.single (Fin.castAdd m i) 1 := by
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · ext j
      change (EuclideanSpace.single i (1 : ℝ)) j =
        (EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ)) (Fin.castAdd m j)
      simp
    · ext j
      have hne : Fin.natAdd n j ≠ Fin.castAdd m i := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
        omega
      change (0 : Y) j =
        (EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ)) (Fin.natAdd n j)
      simp [hne]
  have hbRight (i : Fin m) :
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
        (0, EuclideanSpace.single i 1) = EuclideanSpace.single (Fin.natAdd n i) 1 := by
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · ext j
      have hne : Fin.castAdd m j ≠ Fin.natAdd n i := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
        omega
      change (0 : X) j =
        (EuclideanSpace.single (Fin.natAdd n i) (1 : ℝ)) (Fin.castAdd m j)
      simp [hne]
    · ext j
      change (EuclideanSpace.single i (1 : ℝ)) j =
        (EuclideanSpace.single (Fin.natAdd n i) (1 : ℝ)) (Fin.natAdd n j)
      simp
  have hdf (x : X) (y : Y) (j : Fin m) :
      (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (f x)) y =
        D (Fin.natAdd n j) (e.symm (x, y)) := by
    have hs := e.symm.toContinuousLinearMap.hasFDerivAt.comp y
      ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y))
    have hcomp := (u.differentiableAt (x := e.symm (x, y))).hasFDerivAt.comp y hs
    have hfun : (fun z : Y ↦ u (e.symm (x, z))) = f x := funext (fun z ↦ (hf x z).symm)
    change HasFDerivAt (fun z : Y ↦ u (e.symm (x, z))) _ y at hcomp
    rw [hfun] at hcomp
    have h := congrArg (fun L : Y →L[ℝ] W ↦ L (EuclideanSpace.single j 1))
      (hcomp.unique (f x).differentiableAt.hasFDerivAt)
    change fderiv ℝ u (e.symm (x, y)) (e.symm (0, EuclideanSpace.single j 1)) = _ at h
    rw [hbRight] at h
    exact h.symm
  have hdg (x : X) (y : Y) (i : Fin n) :
      (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (g y)) x =
        D (Fin.castAdd m i) (e.symm (x, y)) := by
    have hs := e.symm.toContinuousLinearMap.hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
    have hcomp := (u.differentiableAt (x := e.symm (x, y))).hasFDerivAt.comp x hs
    have hfun : (fun z : X ↦ u (e.symm (z, y))) = g y := funext (fun z ↦ (hg z y).symm)
    change HasFDerivAt (fun z : X ↦ u (e.symm (z, y))) _ x at hcomp
    rw [hfun] at hcomp
    have h := congrArg (fun L : X →L[ℝ] W ↦ L (EuclideanSpace.single i 1))
      (hcomp.unique (g y).differentiableAt.hasFDerivAt)
    change fderiv ℝ u (e.symm (x, y)) (e.symm (EuclideanSpace.single i 1, 0)) = _ at h
    rw [hbLeft] at h
    exact h.symm
  -- Each directional energy is the same integrable squared joint derivative, by Fubini.
  have hright : (∫ x : X, ‖schwartzSobolevCoordinate 1 (f x)‖ ^ 2) =
      ‖u.toLp 2‖ ^ 2 + c * ∑ j : Fin m, ‖(D (Fin.natAdd n j)).toLp 2‖ ^ 2 := by
    have hpoint (x : X) : ‖schwartzSobolevCoordinate 1 (f x)‖ ^ 2 =
        (∫ y : Y, ‖u (e.symm (x, y))‖ ^ 2) +
          c * ∑ j : Fin m, ∫ y : Y, ‖D (Fin.natAdd n j) (e.symm (x, y))‖ ^ 2 := by
      rw [hH1]
      simp_rw [hL2, hf, hdf]
      rfl
    simp_rw [hpoint]
    rw [integral_add (hInt u).integral_prod_left
      ((integrable_finsetSum Finset.univ (fun j _ ↦
        (hInt (D (Fin.natAdd n j))).integral_prod_left)).const_mul c)]
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ ↦
      (hInt (D (Fin.natAdd n j))).integral_prod_left)]
    simp_rw [hFubini]
  have hleft : (∫ y : Y, ‖schwartzSobolevCoordinate 1 (g y)‖ ^ 2) =
      ‖u.toLp 2‖ ^ 2 + c * ∑ i : Fin n, ‖(D (Fin.castAdd m i)).toLp 2‖ ^ 2 := by
    have hpoint (y : Y) : ‖schwartzSobolevCoordinate 1 (g y)‖ ^ 2 =
        (∫ x : X, ‖u (e.symm (x, y))‖ ^ 2) +
          c * ∑ i : Fin n, ∫ x : X, ‖D (Fin.castAdd m i) (e.symm (x, y))‖ ^ 2 := by
      rw [hH1]
      simp_rw [hL2, hg, hdg]
      rfl
    simp_rw [hpoint]
    rw [integral_add (hInt u).integral_prod_right
      ((integrable_finsetSum Finset.univ (fun i _ ↦
        (hInt (D (Fin.castAdd m i))).integral_prod_right)).const_mul c)]
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ ↦
      (hInt (D (Fin.castAdd m i))).integral_prod_right)]
    simp_rw [hFubini']
  rw [hright, hleft, hH1, Fin.sum_univ_add]
  dsimp only [D]
  ring

end AtiyahSinger

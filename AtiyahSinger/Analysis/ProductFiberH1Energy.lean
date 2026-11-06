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
# Vertical energy of the original finite tensor rows

Public module ID: M0878.

The original Euclidean L² norm and its right-coordinate derivative energies
are exactly the integrated first Sobolev energies of the finite tensor rows.
The actual coordinate concatenation, tensor index order and period-one Fourier
normalization are retained. This compares the coordinates used by the low-cone
estimate with the native whole-fiber families; it assumes no separated expansion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in
-- Exact affine differentiation and finite-row Fubini use the same coordinate function.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual vertical energy equals the sum of the original finite row-slice H¹ energies. -/
theorem norm_vertical_energy_eq_sum_integral_fiber
    {n m a r : ℕ}
    (v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (a * r))))
    (f : Fin a → EuclideanSpace ℝ (Fin n) →
      𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin r)))
    (hf : ∀ i x y j, f i x y j =
      v (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (i, j))) :
    ‖v.toLp 2‖ ^ 2 + (2 * Real.pi)⁻¹ ^ 2 *
      ∑ j : Fin m, ‖(LineDeriv.lineDerivOp
        (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ)) v).toLp 2‖ ^ 2 =
        ∑ i : Fin a, ∫ x, ‖schwartzSobolevCoordinate 1 (f i x)‖ ^ 2 := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let W := EuclideanSpace ℂ (Fin r)
  let V := EuclideanSpace ℂ (Fin (a * r))
  let c : ℝ := (2 * Real.pi)⁻¹ ^ 2
  have hslice (u : 𝓢(Z, W)) (f : X → 𝓢(Y, W))
      (hf : ∀ x y, f x y = u (EuclideanSpace.finAddEquivProd.symm (x, y))) :
      ‖u.toLp 2‖ ^ 2 + c * ∑ j : Fin m,
        ‖(LineDeriv.lineDerivOp
          (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ)) u).toLp 2‖ ^ 2 =
        ∫ x, ‖schwartzSobolevCoordinate 1 (f x)‖ ^ 2 := by
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
    -- The right energy is the same integrable squared joint derivative, by Fubini.
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
    exact hright.symm
  let row (i : Fin a) : V →L[ℂ] W := LinearMap.toContinuousLinearMap {
    toFun w := WithLp.toLp 2 (fun j ↦ w (finProdFinEquiv (i, j)))
    map_add' u w := by ext j; rfl
    map_smul' c u := by ext j; rfl }
  let rows (u : 𝓢(Z, V)) (i : Fin a) := SchwartzMap.postcompCLM (row i) u
  have hL2 {q : ℕ} (u : 𝓢(Z, EuclideanSpace ℂ (Fin q))) :
      ‖u.toLp 2‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 := by
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (integral_nonneg fun z ↦ sq_nonneg _)
  -- The original tensor coordinate order is the actual finite product equivalence.
  have hpoint (w : V) : ‖w‖ ^ 2 = ∑ i : Fin a, ‖row i w‖ ^ 2 := by
    calc
      ‖w‖ ^ 2 = ∑ j : Fin (a * r), ‖w j‖ ^ 2 := EuclideanSpace.norm_sq_eq w
      _ = ∑ i : Fin a, ∑ j : Fin r, ‖w (finProdFinEquiv (i, j))‖ ^ 2 := by
        rw [← (finProdFinEquiv : Fin a × Fin r ≃ Fin (a * r)).sum_comp,
          Fintype.sum_prod_type]
      _ = _ := Finset.sum_congr rfl (fun i _ ↦ (EuclideanSpace.norm_sq_eq (row i w)).symm)
  have hrows (u : 𝓢(Z, V)) : ‖u.toLp 2‖ ^ 2 =
      ∑ i : Fin a, ‖(rows u i).toLp 2‖ ^ 2 := by
    rw [hL2]
    simp_rw [hpoint]
    rw [integral_finsetSum Finset.univ (fun i _ ↦
      ((rows u i).memLp 2).integrable_norm_pow (by norm_num))]
    exact Finset.sum_congr rfl (fun i _ ↦ (hL2 (rows u i)).symm)
  have hderiv (u : 𝓢(Z, V)) (i : Fin a) (z : Z) :
      LineDeriv.lineDerivOp z (rows u i) = rows (LineDeriv.lineDerivOp z u) i := by
    apply SchwartzMap.ext
    intro x
    change fderiv ℝ (row i ∘ u) x z = row i (fderiv ℝ u x z)
    have h := (((row i).restrictScalars ℝ).hasFDerivAt.comp x (u.hasFDerivAt x)).fderiv
    exact congrArg (fun L : Z →L[ℝ] W ↦ L z) h
  have hsliceRow (i : Fin a) := hslice (rows v i) (f i) (fun x y ↦ by
    apply PiLp.ext
    intro j
    exact hf i x y j)
  let D (j : Fin m) (u : 𝓢(Z, V)) :=
    LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ)) u
  have hDrow (j : Fin m) (i : Fin a) : rows (D j v) i =
      LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ)) (rows v i) :=
    (hderiv v i (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ))).symm
  have hDrows (j : Fin m) : ‖(D j v).toLp 2‖ ^ 2 =
      ∑ i : Fin a, ‖(LineDeriv.lineDerivOp
        (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ)) (rows v i)).toLp 2‖ ^ 2 := by
    have h := hrows (D j v)
    apply h.trans
    apply Finset.sum_congr rfl
    intro i _
    rw [hDrow]
  -- Regroup finite real energies without unfolding their measure-valued arguments.
  have hcombine (b : Fin a → ℝ) (d : Fin m → Fin a → ℝ) (t : ℝ) :
      (∑ i, b i) + t * ∑ j, ∑ i, d j i = ∑ i, (b i + t * ∑ j, d j i) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_add_distrib]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ ↦ hDrows j)
  have htotal := congrArg₂ (fun x y : ℝ ↦ x + c * y) (hrows v) hsum
  refine htotal.trans ((hcombine _ _ c).trans ?_)
  exact Finset.sum_congr rfl (fun i _ ↦ hsliceRow i)

end AtiyahSinger

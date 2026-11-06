/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteProductFourier
public import AtiyahSinger.Analysis.ProductSymbolCutoff
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier factorization in the original product coordinates

Public module ID: M0879.

The canonical finite-coordinate splitting preserves product volume and splits
the Euclidean inner product. Consequently Fourier transformation preserves
literal separated Schwartz functions. This is the coordinate comparison needed
to identify the unregularized product operator with its factorwise action before
applying the product-frequency cutoff estimate.

The proof uses the original Fourier convention and the actual coordinate map;
no assertion that an unregularized lifted symbol is a standard joint symbol is
needed. The finite-dimensional factorization is the usual Fubini argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped SchwartzMap

set_option maxSynthPendingDepth 30

variable {n m r q : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m)
local notation "Z" => EuclideanSpace ℝ (Fin (n + m))
local notation "U" => EuclideanSpace ℂ (Fin r)

set_option maxHeartbeats 800000 in
-- Unfolding the fixed finite-coordinate maps retains the original Euclidean instances.
/-- The unregularized lift acts on separated tests by the original first-factor operator. -/
theorem quantize_liftedProductSymbol (a : SymbolFunction n r q) (χ : Y → ℝ)
    (u : 𝓢(X, U)) (v : 𝓢(Y, ℂ)) (w : 𝓢(Z, U))
    (hw : ∀ (x : X) (y : Y),
      w (EuclideanSpace.finAddEquivProd.symm (x, y)) = v y • u x) (x : X) (y : Y) :
    quantize (liftedProductSymbol a χ) w (EuclideanSpace.finAddEquivProd.symm (x, y)) =
      ((χ y : ℂ) * v y) • quantize a u x := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let j : Z ≃ₗᵢ[ℝ] WithLp 2 (X × Y) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 _)
  have he : MeasurePreserving e :=
    (WithLp.volume_preserving_ofLp X Y).comp j.measurePreserving
  have he' : MeasurePreserving e.toHomeomorph.toMeasurableEquiv := he
  have hinner (s : X) (t : Y) :
      inner ℝ (e.symm (x, y)) (e.symm (s, t)) = inner ℝ x s + inner ℝ y t := by
    have h := j.inner_map_map (e.symm (x, y)) (e.symm (s, t))
    change inner ℝ (e (e.symm (x, y))).1 (e (e.symm (s, t))).1 +
      inner ℝ (e (e.symm (x, y))).2 (e (e.symm (s, t))).2 = _ at h
    simpa only [e.apply_symm_apply] using h.symm
  -- Rescale SG frequencies first, so the normalization cancels before applying Fubini.
  rw [quantize_rescaled]
  rw [← he'.symm.integral_comp']
  let f (s : X) := Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x s : ℂ)) •
    a x ((2 * Real.pi) • s) ((𝓕 u) s)
  let g (t : Y) := Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y t : ℂ)) * (𝓕 v) t
  have hvalue (s : X) (t : Y) :
      Complex.exp (2 * Real.pi * Complex.I *
          (inner ℝ (e.symm (x, y)) (e.symm (s, t)) : ℂ)) •
        liftedProductSymbol a χ (e.symm (x, y)) ((2 * Real.pi) • e.symm (s, t))
          ((𝓕 w) (e.symm (s, t))) = ((χ y : ℂ) * g t) • f s := by
    rw [fourier_finAdd_smul u v w hw]
    have hcoords : e ((2 * Real.pi) • e.symm (s, t)) =
        ((2 * Real.pi) • s, (2 * Real.pi) • t) := by
      rw [map_smul, e.apply_symm_apply]
      rfl
    change Complex.exp _ • ((χ (e (e.symm (x, y))).2 : ℂ) •
      a (e (e.symm (x, y))).1 (e ((2 * Real.pi) • e.symm (s, t))).1)
        ((𝓕 v) (e (e.symm (s, t))).2 • (𝓕 u) (e (e.symm (s, t))).1) = _
    rw [hcoords, e.apply_symm_apply, e.apply_symm_apply, hinner]
    have hexp : 2 * Real.pi * Complex.I * ((inner ℝ x s + inner ℝ y t : ℝ) : ℂ) =
        2 * Real.pi * Complex.I * (inner ℝ x s : ℂ) +
          2 * Real.pi * Complex.I * (inner ℝ y t : ℂ) := by push_cast; ring
    rw [hexp, Complex.exp_add]
    simp only [f, g, smul_apply, map_smul, smul_smul]
    congr 1
    ring
  change (∫ z : X × Y, Complex.exp (2 * Real.pi * Complex.I *
      (inner ℝ (e.symm (x, y)) (e.symm z) : ℂ)) •
    liftedProductSymbol a χ (e.symm (x, y)) ((2 * Real.pi) • e.symm z)
      ((𝓕 w) (e.symm z))) = _
  simp_rw [hvalue]
  have hinv : (∫ t, g t) = v y := by
    have hv : (𝓕⁻ (𝓕 v : 𝓢(Y, ℂ)) : 𝓢(Y, ℂ)) = v := fourierInv_fourier_eq v
    have h := congrArg (fun z : 𝓢(Y, ℂ) ↦ z y) hv
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [g]
    rw [real_inner_comm t y]
    congr 2
    push_cast
    ring
  -- Fourier inversion in the second factor leaves exactly its original value.
  calc
    (∫ z : X × Y, ((χ y : ℂ) * g z.2) • f z.1) =
        ∫ z : Y × X, ((χ y : ℂ) * g z.1) • f z.2 :=
      (integral_prod_swap (μ := volume) (ν := volume)
        (fun z : X × Y ↦ ((χ y : ℂ) * g z.2) • f z.1)).symm
    _ = (∫ t, (χ y : ℂ) * g t) • ∫ s, f s :=
      integral_prod_smul (fun t : Y ↦ (χ y : ℂ) * g t) f
    _ = _ := by rw [integral_const_mul, hinv, quantize_rescaled]

end AtiyahSinger

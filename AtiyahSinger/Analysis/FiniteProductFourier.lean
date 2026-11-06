/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier factorization in finite product coordinates

Public module ID: M0629.

The canonical finite-coordinate splitting preserves product volume and splits
the Euclidean inner product. Fubini therefore identifies the Fourier transform
of a separated scalar-vector Schwartz function, with its specified original
coordinate map and Fourier convention. The vector values may lie in any
complex normed space, with the existing totalized Bochner integral convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped SchwartzMap

variable {n m : ℕ} {U : Type*}
  [NormedAddCommGroup U] [NormedSpace ℂ U]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m)
local notation "Z" => EuclideanSpace ℝ (Fin (n + m))

/-- Fourier transformation respects the literal scalar-vector product in finite coordinates. -/
theorem fourier_finAdd_smul (u : 𝓢(X, U)) (v : 𝓢(Y, ℂ)) (w : 𝓢(Z, U))
    (hw : ∀ (x : X) (y : Y),
      w (EuclideanSpace.finAddEquivProd.symm (x, y)) = v y • u x) (ξ : Z) :
    (𝓕 w) ξ = (𝓕 v) (EuclideanSpace.finAddEquivProd ξ).2 •
      (𝓕 u) (EuclideanSpace.finAddEquivProd ξ).1 := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let j : Z ≃ₗᵢ[ℝ] WithLp 2 (X × Y) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 _)
  -- The unchanged Euclidean coordinates give both the product measure and the phase split.
  have he : MeasurePreserving e :=
    (WithLp.volume_preserving_ofLp X Y).comp j.measurePreserving
  have he' : MeasurePreserving e.toHomeomorph.toMeasurableEquiv := he
  have hinner (x : X) (y : Y) :
      inner ℝ (e.symm (x, y)) ξ = inner ℝ x (e ξ).1 + inner ℝ y (e ξ).2 := by
    have h := j.inner_map_map (e.symm (x, y)) ξ
    change inner ℝ (e (e.symm (x, y))).1 (e ξ).1 +
      inner ℝ (e (e.symm (x, y))).2 (e ξ).2 = _ at h
    simpa only [e.apply_symm_apply] using h.symm
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  rw [← he'.symm.integral_comp' (fun z : Z ↦
    Complex.exp ((↑(-2 * Real.pi * inner ℝ z ξ)) * Complex.I) • w z)]
  change (∫ z : X × Y,
    Complex.exp ((↑(-2 * Real.pi * inner ℝ (e.symm z) ξ)) * Complex.I) • w (e.symm z)) = _
  let f (x : X) := Complex.exp ((↑(-2 * Real.pi * inner ℝ x (e ξ).1)) * Complex.I) • u x
  let g (y : Y) := Complex.exp ((↑(-2 * Real.pi * inner ℝ y (e ξ).2)) * Complex.I) * v y
  have hphase (x : X) (y : Y) :
      Complex.exp ((↑(-2 * Real.pi * inner ℝ (e.symm (x, y)) ξ)) * Complex.I) •
          w (e.symm (x, y)) = g y • f x := by
    rw [hinner, hw]
    have hexp : (↑(-2 * Real.pi * (inner ℝ x (e ξ).1 + inner ℝ y (e ξ).2)) : ℂ) *
        Complex.I = (↑(-2 * Real.pi * inner ℝ x (e ξ).1)) * Complex.I +
          (↑(-2 * Real.pi * inner ℝ y (e ξ).2)) * Complex.I := by push_cast; ring
    rw [hexp, Complex.exp_add]
    simp only [f, g, smul_smul]
    congr 1
    ring
  simp_rw [hphase]
  -- Swap the integration order to use scalar-vector Fubini without changing either factor.
  calc
    (∫ z : X × Y, g z.2 • f z.1) = ∫ z : Y × X, g z.1 • f z.2 :=
      (integral_prod_swap (μ := volume) (ν := volume) (fun z : X × Y ↦ g z.2 • f z.1)).symm
    _ = (∫ y, g y) • ∫ x, f x := integral_prod_smul g f
    _ = _ := by
      congr 1 <;> rw [SchwartzMap.fourier_coe, Real.fourier_eq']
      rfl

end AtiyahSinger

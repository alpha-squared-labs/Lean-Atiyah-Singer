/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev
public import AtiyahSinger.Analysis.IsometricQuantization
public import AtiyahSinger.Analysis.Pseudolocal

/-!
# Orthogonal transport on the actual Bessel coordinates

Public module ID: M0765.

The real base isometry and complex fiber isometry act on original Schwartz
functions. Their extension gives an isometry of the completed Bessel coordinates
at any fixed real order, with the exact same Schwartz action on the dense core.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped SchwartzMap

variable {n m r q : ℕ}

/-- Simultaneous orthogonal base and coefficient transport of Schwartz functions. -/
def schwartzCoordinateEquiv
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q)) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) ≃ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin q)) := by
  let T := (SchwartzMap.postcompCLM f.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv)
  let S := (SchwartzMap.postcompCLM f.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm.toContinuousLinearEquiv)
  exact {
    T.toLinearMap with
    invFun := S
    left_inv u := by
      apply SchwartzMap.ext
      intro x
      change f.symm (f (u (e (e.symm x)))) = u x
      rw [e.apply_symm_apply, f.symm_apply_apply]
    right_inv u := by
      apply SchwartzMap.ext
      intro x
      change f (f.symm (u (e.symm (e x)))) = u x
      rw [e.symm_apply_apply, f.apply_symm_apply] }

/-- Orthogonal coordinate transport extends isometrically to every Bessel completion. -/
def sobolevCoordinateIsometry
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q)) (s : ℝ) :
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ≃ₗᵢ[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
  (schwartzCoordinateEquiv e f).extendOfIsometry
    (schwartzSobolevCoordinateLinearMap n r s) (schwartzSobolevCoordinateLinearMap m q s)
    (denseRange_schwartzSobolevCoordinate n r s) (denseRange_schwartzSobolevCoordinate m q s)
    (fun u ↦ by
      change ‖schwartzSobolevCoordinate s (SchwartzMap.postcompCLM
        f.toContinuousLinearEquiv.toContinuousLinearMap
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv u))‖ = _
      rw [norm_schwartzSobolevCoordinate_postcomp_linearIsometry,
        norm_schwartzSobolevCoordinate_comp_linearIsometry]
      rfl)

/-- The completion isometry retains the literal orthogonal action on Schwartz coordinates. -/
theorem sobolevCoordinateIsometry_apply
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q)) (s : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    sobolevCoordinateIsometry e f s (schwartzSobolevCoordinate s u) =
      schwartzSobolevCoordinate s (schwartzCoordinateEquiv e f u) := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ u

end AtiyahSinger

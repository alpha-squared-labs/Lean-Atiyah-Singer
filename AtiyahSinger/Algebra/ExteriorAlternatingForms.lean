/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Complex-valued alternating forms and exterior coordinates

Public module ID: M0018.

The determinant of complex-valued real covectors is alternating in both lists.
The usual exterior-power universal property is complex linear in the values,
and an actual real basis gives the corresponding increasing exterior coordinates.
These interfaces retain the determinant normalization of covariant forms.

Source: the exterior-power duality and determinant pairing in standard multilinear
algebra, used for the musical exterior identification in SG II.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The exterior product of complex-valued real covectors, normalized by the determinant. -/
def complexCovectorAlternatingForm {p : ℕ} (f : Fin p → E →ₗ[ℝ] ℂ) :
    E [⋀^Fin p]→ₗ[ℝ] ℂ where
  toFun w := Matrix.det (Matrix.of (fun i j ↦ f i (w j)))
  map_update_add' w j x y := by
    classical
    cases Subsingleton.elim (inferInstance : DecidableEq (Fin p)) (instDecidableEqFin p)
    have hupdate (z : E) : Matrix.of (fun i k ↦ f i (Function.update w j z k)) =
        Matrix.updateCol (Matrix.of (fun i k ↦ f i (w k))) j (fun i ↦ f i z) := by
      ext i k
      by_cases hk : k = j <;> simp [Matrix.updateCol, Matrix.of_apply, Function.update, hk]
    rw [hupdate, hupdate, hupdate]
    have hsum : (fun i ↦ f i (x + y)) = (fun i ↦ f i x) + (fun i ↦ f i y) := by
      ext i
      exact (f i).map_add x y
    rw [hsum]
    exact Matrix.det_updateCol_add (Matrix.of (fun i k ↦ f i (w k))) j
      (fun i ↦ f i x) (fun i ↦ f i y)
  map_update_smul' w j r x := by
    classical
    cases Subsingleton.elim (inferInstance : DecidableEq (Fin p)) (instDecidableEqFin p)
    have hupdate (z : E) : Matrix.of (fun i k ↦ f i (Function.update w j z k)) =
        Matrix.updateCol (Matrix.of (fun i k ↦ f i (w k))) j (fun i ↦ f i z) := by
      ext i k
      by_cases hk : k = j <;> simp [Matrix.updateCol, Matrix.of_apply, Function.update, hk]
    rw [hupdate, hupdate]
    have hsmul : (fun i ↦ f i (r • x)) = (r : ℂ) • (fun i ↦ f i x) := by
      ext i
      simp only [map_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [hsmul]
    simpa only [Complex.real_smul] using
      Matrix.det_updateCol_smul (Matrix.of (fun i k ↦ f i (w k))) j (r : ℂ)
        (fun i ↦ f i x)
  map_eq_zero_of_eq' w i j hij hne :=
    Matrix.det_zero_of_column_eq hne (fun k ↦ congrArg (f k) hij)

/-- The same determinant is a complex alternating function of its covectors. -/
def complexCovectorWedge (p : ℕ) :
    (E →ₗ[ℝ] ℂ) [⋀^Fin p]→ₗ[ℂ] (E [⋀^Fin p]→ₗ[ℝ] ℂ) where
  toFun := complexCovectorAlternatingForm
  map_update_add' f i a b := by
    classical
    cases Subsingleton.elim (inferInstance : DecidableEq (Fin p)) (instDecidableEqFin p)
    apply AlternatingMap.ext
    intro w
    have hupdate (a : E →ₗ[ℝ] ℂ) : Matrix.of (fun k j ↦ Function.update f i a k (w j)) =
        Matrix.updateRow (Matrix.of (fun k j ↦ f k (w j))) i (fun j ↦ a (w j)) := by
      ext k j
      by_cases hk : k = i <;> simp [Matrix.updateRow, Matrix.of_apply, Function.update, hk]
    change Matrix.det (Matrix.of (fun k j ↦ Function.update f i (a + b) k (w j))) = _
    rw [hupdate]
    change Matrix.det (Matrix.updateRow _ i ((fun j ↦ a (w j)) + (fun j ↦ b (w j)))) = _
    rw [Matrix.det_updateRow_add]
    exact congrArg₂ (· + ·) (congrArg Matrix.det (hupdate a).symm)
      (congrArg Matrix.det (hupdate b).symm)
  map_update_smul' f i z a := by
    classical
    cases Subsingleton.elim (inferInstance : DecidableEq (Fin p)) (instDecidableEqFin p)
    apply AlternatingMap.ext
    intro w
    have hupdate (a : E →ₗ[ℝ] ℂ) : Matrix.of (fun k j ↦ Function.update f i a k (w j)) =
        Matrix.updateRow (Matrix.of (fun k j ↦ f k (w j))) i (fun j ↦ a (w j)) := by
      ext k j
      by_cases hk : k = i <;> simp [Matrix.updateRow, Matrix.of_apply, Function.update, hk]
    change Matrix.det (Matrix.of (fun k j ↦ Function.update f i (z • a) k (w j))) = _
    rw [hupdate]
    change Matrix.det (Matrix.updateRow _ i (z • (fun j ↦ a (w j)))) = _
    rw [Matrix.det_updateRow_smul]
    exact congrArg (z * ·) (congrArg Matrix.det (hupdate a).symm)
  map_eq_zero_of_eq' f i j hij hne := by
    apply AlternatingMap.ext
    intro w
    exact Matrix.det_zero_of_row_eq hne (congrArg (fun a : E →ₗ[ℝ] ℂ ↦
      fun k ↦ a (w k)) hij)

/-- The determinant formula retains the original row and column order. -/
theorem complexCovectorWedge_apply (p : ℕ) (f : Fin p → E →ₗ[ℝ] ℂ) (w : Fin p → E) :
    complexCovectorWedge p f w = Matrix.det (Matrix.of (fun i j ↦ f i (w j))) := rfl

/-- The real exterior-power universal property is complex linear in complex-valued forms. -/
def realAlternatingExteriorEquiv (p : ℕ) :
    (E [⋀^Fin p]→ₗ[ℝ] ℂ) ≃ₗ[ℂ] ((⋀[ℝ]^p E) →ₗ[ℝ] ℂ) where
  toFun := exteriorPower.alternatingMapLinearEquiv
  invFun := exteriorPower.alternatingMapLinearEquiv.symm
  left_inv := exteriorPower.alternatingMapLinearEquiv.symm_apply_apply
  right_inv := exteriorPower.alternatingMapLinearEquiv.apply_symm_apply
  map_add' := exteriorPower.alternatingMapLinearEquiv.map_add
  map_smul' z a := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearMap.smul_apply,
      smul_apply, RingHom.id_apply]

/-- Increasing exterior coordinates of complex-valued real alternating forms. -/
def realAlternatingCoordinates {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (p : ℕ) :
    (E [⋀^Fin p]→ₗ[ℝ] ℂ) ≃ₗ[ℂ] (Set.powersetCard (Fin n) p → ℂ) :=
  (realAlternatingExteriorEquiv p).trans ((b.exteriorPower p).constr ℂ).symm

/-- The coordinates are evaluation on the same increasing ordered real basis vectors. -/
theorem realAlternatingCoordinates_apply {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (p : ℕ)
    (a : E [⋀^Fin p]→ₗ[ℝ] ℂ) (s : Set.powersetCard (Fin n) p) :
    realAlternatingCoordinates b p a s =
      a (fun i ↦ b (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
  change exteriorPower.alternatingMapLinearEquiv a ((b.exteriorPower p) s) = _
  rw [exteriorPower.basis_apply]
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti a _

end AtiyahSinger

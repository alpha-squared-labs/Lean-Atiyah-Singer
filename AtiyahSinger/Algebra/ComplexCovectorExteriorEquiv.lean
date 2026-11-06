/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorAlternatingForms

/-!
# Exterior powers of complex-valued real covectors

Public module ID: M0009.

The determinant pairing identifies the complex exterior power of the complex-valued
real dual with the complex-valued real alternating forms. The map itself is canonical;
a real basis is used only to verify its bijectivity with the matching increasing
exterior coordinates. No factorial is inserted into this identification.

Source: exterior-power duality in finite-dimensional multilinear algebra, used in
the metric exterior identification of SG II.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The canonical determinant map from the complex exterior power of the real covectors. -/
def complexCovectorExteriorMap (p : ℕ) :
    (⋀[ℂ]^p (E →ₗ[ℝ] ℂ)) →ₗ[ℂ] (E [⋀^Fin p]→ₗ[ℝ] ℂ) :=
  exteriorPower.alternatingMapLinearEquiv (complexCovectorWedge p)

/-- On a decomposable exterior power this map is the determinant with the same order. -/
theorem complexCovectorExteriorMap_ιMulti (p : ℕ) (f : Fin p → E →ₗ[ℝ] ℂ)
    (w : Fin p → E) :
    complexCovectorExteriorMap p (exteriorPower.ιMulti ℂ p f) w =
      Matrix.det (Matrix.of (fun i j ↦ f i (w j))) := by
  rw [complexCovectorExteriorMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

set_option maxHeartbeats 800000 in
-- Match the two actual exterior bases before passing to their linear coordinates.
/-- Finite-dimensional exterior duality for complex-valued forms on a real vector space. -/
theorem complexCovectorExteriorMap_bijective [FiniteDimensional ℝ E] (p : ℕ) :
    Function.Bijective (complexCovectorExteriorMap (E := E) p) := by
  classical
  let n := Module.finrank ℝ E
  let b : Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let C := E →ₗ[ℝ] ℂ
  let c : Basis (Fin n) ℂ C := (Pi.basisFun ℂ (Fin n)).map (b.constr ℂ)
  let I := Set.powersetCard (Fin n) p
  let d : Basis I ℂ (E [⋀^Fin p]→ₗ[ℝ] ℂ) :=
    (Pi.basisFun ℂ I).map (realAlternatingCoordinates b p).symm
  -- The covector basis evaluates on the original real basis by the same Kronecker matrix.
  have hcoord (i j : Fin n) : c i (b j) = c.coord i (c j) := by
    change ((b.constr ℂ) (Pi.basisFun ℂ (Fin n) i)) (b j) = _
    rw [b.constr_basis]
    by_cases hij : i = j
    · subst j
      simp [Basis.coord_apply]
    · simp [Basis.coord_apply, Pi.basisFun_apply, hij, Ne.symm hij]
  have hmatrix (s t : I) :
      realAlternatingCoordinates b p
          (complexCovectorExteriorMap p ((c.exteriorPower p) s)) t =
        exteriorPower.ιMultiDual ℂ p c s ((c.exteriorPower p) t) := by
    simp only [realAlternatingCoordinates_apply, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, complexCovectorExteriorMap,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, complexCovectorWedge_apply,
      exteriorPower.ιMultiDual_apply_ιMulti]
    rw [← Matrix.det_transpose]
    apply congrArg Matrix.det
    ext i j
    exact hcoord _ _
  have hbasis (s : I) : complexCovectorExteriorMap p ((c.exteriorPower p) s) = d s := by
    apply (realAlternatingCoordinates b p).injective
    funext t
    rw [hmatrix, ← exteriorPower.basis_repr_apply]
    rw [Basis.repr_self]
    change (Finsupp.single t (1 : ℂ)) s =
      realAlternatingCoordinates b p
        ((realAlternatingCoordinates b p).symm (Pi.basisFun ℂ I s)) t
    rw [LinearEquiv.apply_symm_apply]
    by_cases hst : s = t
    · subst t
      simp
    · simp only [Finsupp.single_eq_of_ne hst, Pi.basisFun_apply,
        Pi.single_eq_of_ne (Ne.symm hst)]
  -- The determinant map sends one complete basis to the other, including degree zero.
  have hmap : complexCovectorExteriorMap (E := E) p = (c.exteriorPower p).constr ℂ d := by
    apply (c.exteriorPower p).ext
    intro s
    rw [Basis.constr_basis, hbasis]
  rw [hmap]
  refine ⟨(c.exteriorPower p).injective_constr_of_linearIndependent d.linearIndependent, ?_⟩
  rw [← LinearMap.range_eq_top, Basis.constr_range, d.span_eq]

/-- The canonical exterior identification with complex-valued real alternating forms. -/
def complexCovectorExteriorEquiv [FiniteDimensional ℝ E] (p : ℕ) :
    (⋀[ℂ]^p (E →ₗ[ℝ] ℂ)) ≃ₗ[ℂ] (E [⋀^Fin p]→ₗ[ℝ] ℂ) :=
  LinearEquiv.ofBijective (complexCovectorExteriorMap p)
    (complexCovectorExteriorMap_bijective p)

end AtiyahSinger

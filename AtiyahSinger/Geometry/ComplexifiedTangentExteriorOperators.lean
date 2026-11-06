/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorContractionCoordinates
public import AtiyahSinger.Geometry.ComplexifiedTangentExteriorForms
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Exterior multiplication and contraction under the actual form identification

Public module ID: M1137.

The canonical metric exterior identification carries multiplication by a real
tangent vector to exterior multiplication by its metric covector. The matching
actual Clifford contraction becomes insertion in the first form slot. Both
statements retain the given homogeneous multivectors and the original forms.

Source: Lawson--Michelsohn, Spin Geometry, II.5. The two identities are the
row and column Laplace expansions of the same determinant pairing.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module
open scoped BigOperators Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option maxHeartbeats 1000000 in
-- Compare complex linear maps on decomposable powers using the first-row determinant expansion.
set_option backward.isDefEq.respectTransparency false in
/-- Exterior multiplication becomes multiplication by the original metric covector. -/
theorem complexifiedTangentExteriorEquiv_wedge
    (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ) (x : M)
    (v : EuclideanSpace ℝ (Fin n))
    (a : ⋀[ℂ]^p (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (b : ⋀[ℂ]^(p + 1) (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hb : b.val = ExteriorAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] v) * a.val) :
    complexifiedTangentExteriorEquiv g (p + 1) x b =
      ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin n))
        ((g.inner x v).smulRight (complexifiedTangentExteriorEquiv g p x a)) := by
  let V := EuclideanSpace ℝ (Fin n)
  let C := ℂ ⊗[ℝ] V
  let ξ : V →L[ℝ] ℝ := g.inner x v
  have hξ (w : V) : complexifiedTangentCovectorMap g x ((1 : ℂ) ⊗ₜ[ℝ] v) w = (ξ w : ℂ) :=
    one_mul _
  let T (q : ℕ) : (⋀[ℂ]^q C) ≃ₗ[ℂ] (V [⋀^Fin q]→L[ℝ] ℂ) :=
    complexifiedTangentExteriorEquiv g q x
  have hT (q : ℕ) (u : Fin q → C) (w : Fin q → V) :
      T q (exteriorPower.ιMulti ℂ q u) w =
        Matrix.det (Matrix.of (fun i j ↦ complexifiedTangentCovectorMap g x (u i) (w j))) :=
    complexifiedTangentExteriorEquiv_ιMulti g q x u w
  let W : (⋀[ℂ]^p C) →ₗ[ℂ] (⋀[ℂ]^(p + 1) C) :=
    { toFun a := ⟨ExteriorAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] v) * a.val, by
        change _ ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ)) ^ (p + 1)
        rw [pow_succ']
        exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) a.property⟩
      map_add' a b := Subtype.ext (mul_add _ _ _)
      map_smul' z a := Subtype.ext (mul_smul_comm _ _ _) }
  let R : (V [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ] (V [⋀^Fin (p + 1)]→L[ℝ] ℂ) :=
    { toFun α := ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight α)
      map_add' α β := by
        have hs : ξ.smulRight (α + β) = ξ.smulRight α + ξ.smulRight β := by
          ext w u
          exact smul_add _ _ _
        rw [hs, ContinuousAlternatingMap.alternatizeUncurryFin_add]
      map_smul' z α := by
        have hs : ξ.smulRight (z • α) = z • ξ.smulRight α := by
          ext w u
          exact smul_comm _ _ _
        rw [hs, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        rfl }
  have hW (u : Fin p → C) : W (exteriorPower.ιMulti ℂ p u) =
      exteriorPower.ιMulti ℂ (p + 1) (Matrix.vecCons ((1 : ℂ) ⊗ₜ[ℝ] v) u) := by
    apply Subtype.ext
    change ExteriorAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] v) * ExteriorAlgebra.ιMulti ℂ p u = _
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  have hmaps : (T (p + 1)).toLinearMap.comp W = R.comp (T p).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro u
    change T (p + 1) (W (exteriorPower.ιMulti ℂ p u)) = R (T p (exteriorPower.ιMulti ℂ p u))
    rw [hW]
    apply ContinuousAlternatingMap.ext
    intro w
    rw [hT]
    change Matrix.det (Matrix.of (fun i j ↦ complexifiedTangentCovectorMap g x
      (Matrix.vecCons ((1 : ℂ) ⊗ₜ[ℝ] v) u i) (w j))) =
        ContinuousAlternatingMap.alternatizeUncurryFin
          (ξ.smulRight (T p (exteriorPower.ιMulti ℂ p u))) w
    rw [Matrix.det_succ_row_zero, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
      hT]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, hξ, zsmul_eq_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Complex.real_smul]
    rw [mul_assoc]
    rfl
  have hab : W a = b := Subtype.ext hb.symm
  rw [← hab]
  exact LinearMap.congr_fun hmaps a

set_option maxHeartbeats 1000000 in
-- The same determinant expands along its first column for the contraction comparison.
set_option backward.isDefEq.respectTransparency false in
/-- Contraction by the matching evaluation covector becomes insertion in the first form slot. -/
theorem complexifiedTangentExteriorEquiv_contractLeft
    (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ) (x : M)
    (v : EuclideanSpace ℝ (Fin n))
    (d : Module.Dual ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hd : ∀ z, d z = complexifiedTangentCovectorMap g x z v)
    (a : ⋀[ℂ]^(p + 1) (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (b : ⋀[ℂ]^p (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hb : b.val = CliffordAlgebra.contractLeft (Q := 0) d a.val) :
    complexifiedTangentExteriorEquiv g p x b =
      (complexifiedTangentExteriorEquiv g (p + 1) x a).curryLeft v := by
  let V := EuclideanSpace ℝ (Fin n)
  let C := ℂ ⊗[ℝ] V
  let d₀ : Module.Dual ℂ C := d
  let T (q : ℕ) : (⋀[ℂ]^q C) ≃ₗ[ℂ] (V [⋀^Fin q]→L[ℝ] ℂ) :=
    complexifiedTangentExteriorEquiv g q x
  have hT (q : ℕ) (u : Fin q → C) (w : Fin q → V) :
      T q (exteriorPower.ιMulti ℂ q u) w =
        Matrix.det (Matrix.of (fun i j ↦ complexifiedTangentCovectorMap g x (u i) (w j))) :=
    complexifiedTangentExteriorEquiv_ιMulti g q x u w
  have hd₀ (z : C) : d₀ z = complexifiedTangentCovectorMap g x z v := hd z
  let K : (⋀[ℂ]^(p + 1) C) →ₗ[ℂ] (⋀[ℂ]^p C) :=
    { toFun a := ⟨CliffordAlgebra.contractLeft (Q := 0) d₀ a.val,
        exteriorContractLeft_mem_exteriorPower d₀ p a.val a.property⟩
      map_add' a b := Subtype.ext (map_add _ _ _)
      map_smul' z a := Subtype.ext (map_smul _ _ _) }
  let R : (V [⋀^Fin (p + 1)]→L[ℝ] ℂ) →ₗ[ℂ] (V [⋀^Fin p]→L[ℝ] ℂ) :=
    { toFun α := α.curryLeft v
      map_add' α β := by ext w; rfl
      map_smul' z α := by ext w; rfl }
  have hK (u : Fin (p + 1) → C) : K (exteriorPower.ιMulti ℂ (p + 1) u) =
      ∑ j : Fin (p + 1), ((-1 : ℤ) ^ j.val) •
        (d₀ (u j) • exteriorPower.ιMulti ℂ p (j.removeNth u)) := by
    apply Subtype.ext
    change CliffordAlgebra.contractLeft d₀ (ExteriorAlgebra.ιMulti ℂ (p + 1) u) = _
    rw [exteriorContractLeft_ιMulti]
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hmaps : (T p).toLinearMap.comp K = R.comp (T (p + 1)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro u
    change T p (K (exteriorPower.ιMulti ℂ (p + 1) u)) =
      R (T (p + 1) (exteriorPower.ιMulti ℂ (p + 1) u))
    rw [hK, map_sum]
    simp only [map_zsmul, map_smul]
    apply ContinuousAlternatingMap.ext
    intro w
    change (∑ j : Fin (p + 1), ((-1 : ℤ) ^ j.val) •
      (d₀ (u j) • T p (exteriorPower.ιMulti ℂ p (j.removeNth u)))) w =
        T (p + 1) (exteriorPower.ιMulti ℂ (p + 1) u) (Matrix.vecCons v w)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, hT]
    conv_rhs => rw [Matrix.det_succ_column_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [hd₀]
    simp only [zsmul_eq_mul, smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Matrix.of_apply, Matrix.cons_val_zero]
    rw [mul_assoc]
    rfl
  have hab : K a = b := Subtype.ext hb.symm
  rw [← hab]
  exact LinearMap.congr_fun hmaps a

end AtiyahSinger

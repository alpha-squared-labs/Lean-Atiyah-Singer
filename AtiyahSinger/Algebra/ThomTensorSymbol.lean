/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorParity
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The graded tensor symbol used by the supported Thom map

Public module ID: M0071.

Karoubi IV.1.10 forms the graded tensor sum of a base symbol and the exterior
symbol. We retain SG's exterior convention `c(v)² = -‖v‖²`. A pair of reciprocal
cutoff maps gives a base odd operator with square `-r²`, so both summands have
the same sign. The two displayed blocks are the restrictions of that actual odd
operator; their inverse has the scalar denominator `r² + ‖v‖²`.

The reciprocal pair need not be adjoints for pre-existing metrics. The comparison
with Karoubi's self-adjoint presentation is a homotopy of symbols, not equality
of matrices. These algebraic formulas do not choose any new grading or K-class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable {F G V : Type*} [AddCommGroup F] [Module ℂ F]
  [AddCommGroup G] [Module ℂ G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

local notation "Even" => CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0
local notation "Odd" => CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1

/-- The even-to-odd block of the actual graded tensor sum. -/
def thomTensorSymbol (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F) (v : V) :
    ((F ⊗[ℂ] Even) × (G ⊗[ℂ] Odd)) →ₗ[ℂ]
      ((G ⊗[ℂ] Even) × (F ⊗[ℂ] Odd)) :=
  ((TensorProduct.map d (LinearMap.id : Even →ₗ[ℂ] Even)).coprod
    (-(TensorProduct.map (LinearMap.id : G →ₗ[ℂ] G)
      (cliffordSymbolParity v 1)))).prod
      ((TensorProduct.map (LinearMap.id : F →ₗ[ℂ] F) (cliffordSymbolParity v 0)).coprod
        (-(TensorProduct.map d' (LinearMap.id : Odd →ₗ[ℂ] Odd))))

/-- The odd-to-even block uses the same reciprocal maps and the same exterior symbol. -/
def thomTensorSymbolReverse (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F) (v : V) :
    ((G ⊗[ℂ] Even) × (F ⊗[ℂ] Odd)) →ₗ[ℂ]
      ((F ⊗[ℂ] Even) × (G ⊗[ℂ] Odd)) :=
  ((-(TensorProduct.map d' (LinearMap.id : Even →ₗ[ℂ] Even))).coprod
    (TensorProduct.map (LinearMap.id : F →ₗ[ℂ] F) (cliffordSymbolParity v 1))).prod
      ((-(TensorProduct.map (LinearMap.id : G →ₗ[ℂ] G)
        (cliffordSymbolParity v 0))).coprod
        (TensorProduct.map d (LinearMap.id : Odd →ₗ[ℂ] Odd)))

/-- The graded tensor square is negative the sum of the two nonnegative squares. -/
theorem thomTensorSymbol_square (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F) (r : ℝ) (v : V)
    (h₀ : d'.comp d = (r ^ 2 : ℂ) • LinearMap.id)
    (h₁ : d.comp d' = (r ^ 2 : ℂ) • LinearMap.id) :
    (thomTensorSymbolReverse d d' v).comp (thomTensorSymbol d d' v) =
        -((r ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ) • LinearMap.id ∧
      (thomTensorSymbol d d' v).comp (thomTensorSymbolReverse d d' v) =
        -((r ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ) • LinearMap.id := by
  /- Expand the four block products on pure tensors, then use tensor induction.
  The mixed terms cancel because the base operator anticommutes with its parity
  involution. The remaining base terms are -d'd and -dd', while the exterior
  terms are c(v)^2. Apply the two reciprocal identities and cliffordSymbol_sq.
  Both signs are negative; adding a self-adjoint positive-square base operator
  to the existing skew exterior symbol would not give this assertion. -/
  -- Restrict the ambient Clifford square to the two original parity subspaces.
  have hc₀ (x : Even) : cliffordSymbolParity v 1 (cliffordSymbolParity v 0 x) =
      -(‖v‖ ^ 2 : ℂ) • x := by
    apply Subtype.ext
    exact LinearMap.congr_fun (cliffordSymbol_sq v) x.val
  have hc₁ (x : Odd) : cliffordSymbolParity v 0 (cliffordSymbolParity v 1 x) =
      -(‖v‖ ^ 2 : ℂ) • x := by
    apply Subtype.ext
    exact LinearMap.congr_fun (cliffordSymbol_sq v) x.val
  have hd₀ (x : F) : d' (d x) = (r ^ 2 : ℂ) • x := LinearMap.congr_fun h₀ x
  have hd₁ (x : G) : d (d' x) = (r ^ 2 : ℂ) • x := LinearMap.congr_fun h₁ x
  -- Pure tensors expose the two diagonal squares and cancellation of mixed terms.
  constructor <;> apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
    intro x y <;> apply Prod.ext <;>
    simp only [thomTensorSymbol, thomTensorSymbolReverse, LinearMap.comp_apply,
      LinearMap.prod_apply, Function.prod, LinearMap.coprod_apply, LinearMap.neg_apply,
      LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_neg, map_zero, TensorProduct.map_tmul, hd₀, hd₁, hc₀, hc₁,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_neg,
      Complex.ofReal_add,
      Complex.ofReal_pow, add_smul, neg_smul, Prod.smul_mk,
      LinearMap.add_apply, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      smul_zero, neg_zero, add_zero, zero_add, neg_neg, neg_add,
      add_neg_cancel, neg_add_cancel] <;> exact add_comm _ _

/-- The explicit inverse block whenever the sum of squares is nonzero. -/
def thomTensorSymbolInverse (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F) (r : ℝ) (v : V) :
    ((G ⊗[ℂ] Even) × (F ⊗[ℂ] Odd)) →ₗ[ℂ]
      ((F ⊗[ℂ] Even) × (G ⊗[ℂ] Odd)) :=
  -(((r ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ • thomTensorSymbolReverse d d' v

/-- The reciprocal identities give both inverse laws for the specified tensor blocks. -/
theorem thomTensorSymbol_inverse_laws
    (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F) (r : ℝ) (v : V)
    (h₀ : d'.comp d = (r ^ 2 : ℂ) • LinearMap.id)
    (h₁ : d.comp d' = (r ^ 2 : ℂ) • LinearMap.id)
    (h : r ^ 2 + ‖v‖ ^ 2 ≠ 0) :
    Function.LeftInverse (thomTensorSymbolInverse d d' r v) (thomTensorSymbol d d' v) ∧
      Function.RightInverse (thomTensorSymbolInverse d d' r v) (thomTensorSymbol d d' v) := by
  /- Apply both square identities to the relevant vector. The real nonzero
  hypothesis remains nonzero after casting to complex scalars. Multiplication
  by the displayed negative reciprocal cancels the negative square in each
  order. The two parity spaces and all tensor factors remain unchanged. -/
  obtain ⟨hleft, hright⟩ := thomTensorSymbol_square d d' r v h₀ h₁
  have hcomplex : ((r ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  -- The negative reciprocal cancels the negative scalar square on even vectors.
  constructor
  · intro x
    change -(((r ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ •
      ((thomTensorSymbolReverse d d' v).comp (thomTensorSymbol d d' v)) x = x
    rw [hleft, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      neg_mul_neg, inv_mul_cancel₀ hcomplex, one_smul]
  · intro y
    -- Move the same scalar through the forward map for the odd-vector identity.
    change thomTensorSymbol d d' v
      (-(((r ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ • thomTensorSymbolReverse d d' v y) = y
    rw [map_smul]
    change -(((r ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ •
      ((thomTensorSymbol d d' v).comp (thomTensorSymbolReverse d d' v)) y = y
    rw [hright, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      neg_mul_neg, inv_mul_cancel₀ hcomplex, one_smul]

/-- The off-singular tensor isomorphism has the displayed forward and inverse formulas. -/
def thomTensorSymbolEquiv (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F) (r : ℝ) (v : V)
    (h₀ : d'.comp d = (r ^ 2 : ℂ) • LinearMap.id)
    (h₁ : d.comp d' = (r ^ 2 : ℂ) • LinearMap.id)
    (h : r ^ 2 + ‖v‖ ^ 2 ≠ 0) :
    ((F ⊗[ℂ] Even) × (G ⊗[ℂ] Odd)) ≃ₗ[ℂ]
      ((G ⊗[ℂ] Even) × (F ⊗[ℂ] Odd)) where
  toLinearMap := thomTensorSymbol d d' v
  invFun := thomTensorSymbolInverse d d' r v
  left_inv := (thomTensorSymbol_inverse_laws d d' r v h₀ h₁ h).1
  right_inv := (thomTensorSymbol_inverse_laws d d' r v h₀ h₁ h).2

end AtiyahSinger

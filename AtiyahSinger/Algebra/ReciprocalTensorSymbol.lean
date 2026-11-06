/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The graded tensor symbol of two reciprocal pairs

Public module ID: M0049.

Two maps in each direction, with scalar composites, give a tensor symbol on
the original four tensor factors. The even space is (E0 tensor F0) plus
(E1 tensor F1); the odd space is (E1 tensor F0) plus (E0 tensor F1).
The displayed forward and reverse blocks compose to the sum of the two
composite scalars. When that sum is nonzero, the reciprocal scalar times
the actual reverse block is the specified inverse.

Source: Karoubi II.5.21 for the graded product of relative triples. The matrix
display in II.5.22, p.101, has a target-order mismatch and an ill-typed lower-left
entry. We follow II.5.21: the first target summand is E1 tensor F0, and the
lower-left entry is identity tensor the second forward map. These source
corrections are recorded in the accompanying literature review.
The use of reciprocal pairs, later supplied by a boundary isomorphism and its inverse
with one cutoff, is the project's explicit realization of this construction.
It needs neither adjoints nor metrics, finite dimension, or rank equality.
This algebraic module does not supply a topology, cutoff, support, or K class.

The sign convention here gives a positive sum of scalar composites. The earlier
ThomTensorSymbol is fixed to SG's skew exterior symbol and has a negative
sum-of-squares identity; it is retained unchanged. Comparing the two models
requires the corresponding sign change on a tensor summand, not equality of
their block matrices. The present four-fiber construction does not introduce
another exterior symbol. The composite and inverse identities below are proved
for these actual maps and their specified inverse formulas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable {E₀ E₁ F₀ F₁ : Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [AddCommGroup E₁] [Module ℂ E₁]
  [AddCommGroup F₀] [Module ℂ F₀] [AddCommGroup F₁] [Module ℂ F₁]

/-- The actual even-to-odd tensor block of the two specified reciprocal pairs. -/
def reciprocalTensorSymbol (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀)
    (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀) :
    ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) →ₗ[ℂ]
      ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) :=
  ((TensorProduct.map d (LinearMap.id : F₀ →ₗ[ℂ] F₀)).coprod
    (-(TensorProduct.map (LinearMap.id : E₁ →ₗ[ℂ] E₁) e'))).prod
      ((TensorProduct.map (LinearMap.id : E₀ →ₗ[ℂ] E₀) e).coprod
        (TensorProduct.map d' (LinearMap.id : F₁ →ₗ[ℂ] F₁)))

/-- The actual reverse block retains the same four maps and their prescribed signs. -/
def reciprocalTensorSymbolReverse (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀)
    (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀) :
    ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) →ₗ[ℂ]
      ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) :=
  ((TensorProduct.map d' (LinearMap.id : F₀ →ₗ[ℂ] F₀)).coprod
    (TensorProduct.map (LinearMap.id : E₀ →ₗ[ℂ] E₀) e')).prod
      ((-(TensorProduct.map (LinearMap.id : E₁ →ₗ[ℂ] E₁) e)).coprod
        (TensorProduct.map d (LinearMap.id : F₁ →ₗ[ℂ] F₁)))

/-- Both tensor block composites are the sum of the two original scalar composites. -/
theorem reciprocalTensorSymbol_square
    (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀)
    (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀) (r s : ℂ)
    (h₀ : d'.comp d = r • LinearMap.id) (h₁ : d.comp d' = r • LinearMap.id)
    (k₀ : e'.comp e = s • LinearMap.id) (k₁ : e.comp e' = s • LinearMap.id) :
    (reciprocalTensorSymbolReverse d d' e e').comp (reciprocalTensorSymbol d d' e e') =
        (r + s) • LinearMap.id ∧
      (reciprocalTensorSymbol d d' e e').comp (reciprocalTensorSymbolReverse d d' e e') =
        (r + s) • LinearMap.id := by
  /- Stage 1: expand each composite into its four tensor blocks. In the first
  order the diagonal blocks are d'd tensor id plus id tensor e'e, and
  dd' tensor id plus id tensor ee'. The two off-diagonal blocks vanish:
  maps on separate tensor factors commute, with opposite displayed signs.
  Stage 2: in the opposite order the diagonal combinations are dd' with e'e
  and d'd with ee'; the same tensor functoriality cancels both mixed blocks.
  Apply exactly the four supplied reciprocal identities. Scalar linearity
  of the tensor product gives (r+s) times the identity on each summand.
  Stage 3: tensor induction and product extensionality extend the pure-vector
  calculations to all original vectors. No invertibility of the individual
  maps, positivity of r or s, common dimension, basis, or adjoint is needed. -/
  -- The four original reciprocal identities give pointwise scalar composites.
  have hd₀ (x : E₀) : d' (d x) = r • x := LinearMap.congr_fun h₀ x
  have hd₁ (x : E₁) : d (d' x) = r • x := LinearMap.congr_fun h₁ x
  have he₀ (y : F₀) : e' (e y) = s • y := LinearMap.congr_fun k₀ y
  have he₁ (y : F₁) : e (e' y) = s • y := LinearMap.congr_fun k₁ y
  -- Check each product summand on pure tensors; linearity then covers all vectors.
  constructor <;> apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
    intro x y <;> apply Prod.ext <;>
    simp [reciprocalTensorSymbol, reciprocalTensorSymbolReverse,
      hd₀, hd₁, he₀, he₁, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      add_smul, add_comm]

/-- The prescribed inverse formula is the reciprocal scalar times the original reverse block. -/
def reciprocalTensorSymbolInverse (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀)
    (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀) (r s : ℂ) :
    ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) →ₗ[ℂ]
      ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) :=
  (r + s)⁻¹ • reciprocalTensorSymbolReverse d d' e e'

/-- Nonvanishing of the summed scalar gives both inverse laws for these exact tensor maps. -/
theorem reciprocalTensorSymbol_inverse_laws
    (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀)
    (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀) (r s : ℂ)
    (h₀ : d'.comp d = r • LinearMap.id) (h₁ : d.comp d' = r • LinearMap.id)
    (k₀ : e'.comp e = s • LinearMap.id) (k₁ : e.comp e' = s • LinearMap.id)
    (h : r + s ≠ 0) :
    Function.LeftInverse (reciprocalTensorSymbolInverse d d' e e' r s)
        (reciprocalTensorSymbol d d' e e') ∧
      Function.RightInverse (reciprocalTensorSymbolInverse d d' e e' r s)
        (reciprocalTensorSymbol d d' e e') := by
  /- Stage 1: apply the first square identity to an even vector. The actual
  inverse formula scales the result by (r+s) inverse. Since r+s is nonzero,
  its scalar product with r+s is one, giving the original even vector.
  Stage 2: apply the second square identity to an odd vector. Linearity moves
  the same reciprocal scalar through the forward map, and the same nonzero
  hypothesis gives the original odd vector. No alternative inverse is chosen. -/
  obtain ⟨hleft, hright⟩ := reciprocalTensorSymbol_square d d' e e' r s h₀ h₁ k₀ k₁
  -- On even vectors the reverse composite supplies the summed scalar.
  constructor
  · intro x
    change (r + s)⁻¹ •
      ((reciprocalTensorSymbolReverse d d' e e').comp
        (reciprocalTensorSymbol d d' e e')) x = x
    rw [hleft, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      inv_mul_cancel₀ h, one_smul]
  · intro y
    -- On odd vectors move the reciprocal scalar through the forward linear map.
    change reciprocalTensorSymbol d d' e e'
      ((r + s)⁻¹ • reciprocalTensorSymbolReverse d d' e e' y) = y
    rw [map_smul]
    change (r + s)⁻¹ •
      ((reciprocalTensorSymbol d d' e e').comp
        (reciprocalTensorSymbolReverse d d' e e')) y = y
    rw [hright, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      inv_mul_cancel₀ h, one_smul]

/-- The off-singular tensor equivalence has precisely the displayed forward and inverse blocks. -/
def reciprocalTensorSymbolEquiv (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀)
    (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀) (r s : ℂ)
    (h₀ : d'.comp d = r • LinearMap.id) (h₁ : d.comp d' = r • LinearMap.id)
    (k₀ : e'.comp e = s • LinearMap.id) (k₁ : e.comp e' = s • LinearMap.id)
    (h : r + s ≠ 0) :
    ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) ≃ₗ[ℂ]
      ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) where
  toLinearMap := reciprocalTensorSymbol d d' e e'
  invFun := reciprocalTensorSymbolInverse d d' e e' r s
  left_inv := (reciprocalTensorSymbol_inverse_laws d d' e e' r s h₀ h₁ k₀ k₁ h).1
  right_inv := (reciprocalTensorSymbol_inverse_laws d d' e e' r s h₀ h₁ k₀ k₁ h).2

end AtiyahSinger

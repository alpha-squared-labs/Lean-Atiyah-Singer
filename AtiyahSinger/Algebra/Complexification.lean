/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Real and imaginary coordinates of a complexification

Public module ID: M0011.

K05. The complexification of a real vector space `W` is the actual scalar extension
`ℂ ⊗[ℝ] W`. Its underlying real vector space is canonically `W × W`, in the ordered
real and imaginary coordinates. Multiplication by `I` acts by `(u, v) ↦ (-v, u)`.

Sources: Husemoller, *Fibre Bundles*, Chapter 17, §11, printed p. 259, for the standard
complexification; Lawson--Michelsohn, *Spin Geometry*, III.12, printed p. 241, for the
ordered complex-structure matrix. Husemoller's opposite tensor order is identified
with this scalar-extension order by the tensor symmetry. The computation certificate
below is project-supplied linear algebra, not a separately numbered source theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable (W : Type*) [AddCommGroup W] [Module ℝ W]

/-- The canonical real-linear real/imaginary decomposition of a complexification. -/
def complexificationReIm : (ℂ ⊗[ℝ] W) ≃ₗ[ℝ] W × W :=
  ((TensorProduct.congr Complex.equivRealProdLm (LinearEquiv.refl ℝ W)).trans
    (TensorProduct.prodLeft ℝ ℝ ℝ ℝ W)).trans
      ((TensorProduct.lid ℝ W).prodCongr (TensorProduct.lid ℝ W))

/-- Real/imaginary coordinates, their inverse, and the induced complex structure.
These formulas fix the order and sign used by the bundle complexification. -/
theorem complexificationReIm_properties :
    (∀ (z : ℂ) (v : W),
      complexificationReIm W (z ⊗ₜ[ℝ] v) = (z.re • v, z.im • v)) ∧
    (∀ u v : W, (complexificationReIm W).symm (u, v) =
      (1 : ℂ) ⊗ₜ[ℝ] u + Complex.I ⊗ₜ[ℝ] v) ∧
    (∀ w : ℂ ⊗[ℝ] W, complexificationReIm W (Complex.I • w) =
      (-(complexificationReIm W w).2, (complexificationReIm W w).1)) := by
  -- The three specified tensor equivalences send a pure tensor to its two coordinates.
  have hpure (z : ℂ) (v : W) :
      complexificationReIm W (z ⊗ₜ[ℝ] v) = (z.re • v, z.im • v) := by
    simp [complexificationReIm, Complex.equivRealProdLm_apply]
  refine ⟨hpure, ?_, ?_⟩
  · -- Identify the inverse by applying the same injective forward equivalence.
    intro u v
    apply (complexificationReIm W).injective
    rw [LinearEquiv.apply_symm_apply, map_add, hpure, hpure]
    simp
  · -- Multiplication by I rotates each pure tensor's real and imaginary coordinates.
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul z v =>
      rw [TensorProduct.smul_tmul', hpure, hpure]
      simp [Complex.mul_re, Complex.mul_im]
    | add x y hx hy =>
      -- Additivity extends the rotation formula to every tensor, without a basis choice.
      simp only [smul_add, map_add, hx, hy, Prod.fst_add, Prod.snd_add, neg_add]
      rfl

end AtiyahSinger

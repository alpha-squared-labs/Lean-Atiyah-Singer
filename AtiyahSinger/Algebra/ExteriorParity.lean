/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorSymbol
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.Projection

/-!
# The even and odd exterior symbols

Public module ID: M0020.

The algebraic parity part of D10 uses mathlib's existing `CliffordAlgebra.evenOdd`
submodules at the zero quadratic form. Since `ExteriorAlgebra` is exactly that Clifford
algebra, these are the standard sums of the even and odd exterior powers, with no second
carrier or independently chosen grading.

The restricted symbol is the existing `cliffordSymbol`, with its negative-square convention
and Hermitian contraction. It interchanges parity and is an isomorphism away from the zero
vector. No finite-dimensional or positive-dimensional assumption is needed here; the
off-zero assertion is vacuous for a zero-dimensional space.

This file supplies algebraic maps only. It does not equip the parity spaces with bundle
topologies, construct the exterior-symbol K-class, or compare that class with a Bott class.
These exterior parity spaces are not the half-spin bundles required by the general SC01 node.
The mathematical construction follows Spin Geometry, Appendix C, and the exterior-algebra
model of Karoubi, K-Theory, IV.1.5; the choice of minus contraction is the convention fixed
in `ExteriorSymbol`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The standard even/odd decomposition of the actual complex exterior algebra. -/
def exteriorParityEquiv (V : Type*) [AddCommGroup V] [Module ℂ V] :
    ExteriorAlgebra ℂ V ≃ₗ[ℂ]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0 ×
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1) :=
  (Submodule.prodEquivOfIsCompl
    (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0)
    (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1)
    (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm ℂ V))).symm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Clifford multiplication is odd for the standard parity grading. -/
theorem cliffordSymbol_mem_evenOdd (v : V) (i : ZMod 2) (a : ExteriorAlgebra ℂ V)
    (ha : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i) :
    cliffordSymbol v a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) := by
  /- Stage 1: on a product of k vectors, exterior multiplication adds one factor,
  while the contraction rule expands into terms with k-1 factors. Both degrees
  have parity i+1 when k has parity i; contraction of a scalar is zero.
  Stage 2: extend the statement to the standard span of those products using
  linearity and closure of the target submodule under subtraction. The inner
  product defines a complex-linear functional in its second argument, so each
  contraction term has the required complex scalar coefficient. -/
  -- Contraction changes parity. Induct within the existing Clifford grading,
  -- starting with scalars or vectors and adjoining pairs of vectors.
  have hcontract : contraction v a ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) := by
    induction a, ha using CliffordAlgebra.evenOdd_induction with
    | range_ι_pow x hx =>
      fin_cases i
      · change x ∈ (CliffordAlgebra.ι (0 : QuadraticForm ℂ V)).range ^ (0 : ℕ) at hx
        rw [pow_zero] at hx
        obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
        simp [contraction, CliffordAlgebra.contractLeft_algebraMap]
      · change x ∈ (CliffordAlgebra.ι (0 : QuadraticForm ℂ V)).range ^ (1 : ℕ) at hx
        rw [pow_one] at hx
        obtain ⟨w, rfl⟩ := hx
        change contraction v (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w) ∈
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0
        simpa only [contraction, CliffordAlgebra.contractLeft_ι] using
          (SetLike.algebraMap_mem_graded
            (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)) (innerₛₗ ℂ v w))
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using (CliffordAlgebra.evenOdd _ _).add_mem ihx ihy
    | ι_mul_ι_mul w₁ w₂ x hx ih =>
      -- The two first-order terms and the double-wedge contraction have the same parity.
      have hw₁ := CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm ℂ V) w₁
      have hw₂ := CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm ℂ V) w₂
      have hfirst : CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w₂ * x ∈
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) := by
        simpa [add_comm] using SetLike.mul_mem_graded hw₂ hx
      have hsecond : CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w₁ * x ∈
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) := by
        simpa [add_comm] using SetLike.mul_mem_graded hw₁ hx
      have hlast : CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w₁ *
          CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w₂ * contraction v x ∈
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) := by
        simpa using SetLike.mul_mem_graded
          (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ w₁ w₂) ih
      change CliffordAlgebra.contractLeft (innerₛₗ ℂ v) _ ∈ _
      rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, mul_sub, Algebra.mul_smul_comm, ← mul_assoc]
      exact (CliffordAlgebra.evenOdd _ _).sub_mem
        ((CliffordAlgebra.evenOdd _ _).smul_mem _ hfirst)
        ((CliffordAlgebra.evenOdd _ _).sub_mem
          ((CliffordAlgebra.evenOdd _ _).smul_mem _ hsecond) hlast)
  -- Exterior multiplication adds one vector; the difference is therefore odd too.
  have hwedge : exteriorMultiplication v a ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) := by
    simpa [exteriorMultiplication, add_comm] using SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm ℂ V) v) ha
  exact (CliffordAlgebra.evenOdd _ _).sub_mem hwedge hcontract

/-- The actual Clifford symbol restricted from parity `i` to parity `i + 1`. -/
def cliffordSymbolParity (v : V) (i : ZMod 2) :
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i →ₗ[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) :=
  ((cliffordSymbol v).comp
    (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i).subtype).codRestrict _
      (fun a ↦ cliffordSymbol_mem_evenOdd v i a.val a.property)

/-- The parity-changing Clifford symbol is bijective away from the zero vector. -/
theorem cliffordSymbolParity_bijective (v : V) (hv : v ≠ 0) (i : ZMod 2) :
    Function.Bijective (cliffordSymbolParity v i) := by
  /- Stage 1: cliffordSymbol_sq gives c(v)^2 = -‖v‖² id on the actual exterior
  algebra. Since v is nonzero, the complex scalar ‖v‖² is nonzero.
  Stage 2: on parity i+1 use -‖v‖⁻² c(v) as inverse. The parity theorem places
  its value in degree (i+1)+1=i in ZMod 2; this equality supplies the subtype
  transport. Applying the negative-square identity in both orders gives both
  inverse laws. This argument does not assume finite or positive dimension. -/
  -- The ambient negative-square identity gives the explicit inverse on all multivectors.
  have hinv (x : ExteriorAlgebra ℂ V) :
      -(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbol v (cliffordSymbol v x) = x := by
    have h := LinearMap.congr_fun (cliffordSymbol_inverse v hv) x
    simpa only [Module.End.mul_apply, LinearMap.smul_apply, map_smul,
      Module.End.one_apply] using h
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (Function.LeftInverse.injective (f := cliffordSymbol v)
      (g := fun x ↦ -(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbol v x) hinv)
    exact congrArg Subtype.val hxy
  · intro y
    -- The candidate inverse has parity (i+1)+1=i, including in arbitrary dimension.
    have hparity := cliffordSymbol_mem_evenOdd v (i + 1) y.val y.property
    have htwo : (1 : ZMod 2) + 1 = 0 := rfl
    simp only [add_assoc, htwo, add_zero] at hparity
    refine ⟨⟨-(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbol v y.val,
      (CliffordAlgebra.evenOdd _ _).smul_mem _ hparity⟩, ?_⟩
    apply Subtype.ext
    change cliffordSymbol v (-(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbol v y.val) = y.val
    rw [map_smul, hinv]

/-- The off-zero exterior-symbol isomorphism, with the specified Clifford forward map. -/
def cliffordSymbolParityEquiv (v : V) (hv : v ≠ 0) (i : ZMod 2) :
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i ≃ₗ[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) :=
  LinearEquiv.ofBijective (cliffordSymbolParity v i)
    (cliffordSymbolParity_bijective v hv i)

/-- The inverse parity symbol is the same Clifford action scaled by negative inverse length. -/
theorem cliffordSymbolParityEquiv_symm_apply (v : V) (hv : v ≠ 0) (i : ZMod 2)
    (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1)) :
    ((cliffordSymbolParityEquiv v hv i).symm a : ExteriorAlgebra ℂ V) =
      -(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbol v (a : ExteriorAlgebra ℂ V) := by
  /- Take the inverse image under the already constructed parity equivalence.
  Its forward symbol is the given vector. Applying the ambient inverse identity
  to this inverse image identifies it with the displayed scaled Clifford action.
  The preceding bijectivity proof already supplies the required parity transport. -/
  -- Apply the already proved ambient inverse identity to the actual inverse image.
  let x := (cliffordSymbolParityEquiv v hv i).symm a
  have hforward : cliffordSymbol v (x : ExteriorAlgebra ℂ V) = a.val :=
    congrArg Subtype.val ((cliffordSymbolParityEquiv v hv i).apply_symm_apply a)
  have h := LinearMap.congr_fun (cliffordSymbol_inverse v hv)
    (x : ExteriorAlgebra ℂ V)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    Module.End.one_apply, hforward] at h
  exact h.symm

end AtiyahSinger

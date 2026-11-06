/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.EquivariantKoszulSymbol

/-!
# The exact exterior phase in the sphere Hodge comparison

Public module ID: M2164.

Multiplication by `i` on the original complex vector space induces multiplication
by `i^p` in exterior degree `p`. Its restrictions preserve the original even and
odd exterior carriers. They conjugate wedge plus contraction to `i` times wedge
minus contraction, with the same vector and the original Hermitian contraction.
Naturality under every complex-linear map supplies compatibility with the original
bundle frames and group actions. These algebraic identities alone do not assert
that a supported K class has been realized by a Hodge pseudodifferential operator.

Source: the phase convention in Lawson--Michelsohn, Spin Geometry, II.5 and
III.13, with the explicit degreewise conjugacy as a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

variable (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The standard exterior degree phase, restricted to the original parity carrier. -/
def exteriorHodgePhaseEquiv (i : ZMod 2) :
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i ≃ₗ[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i := by
  let z : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  let U := exteriorParityAction (V := V) z i
  let B := exteriorParityAction (V := V) z⁻¹ i
  have hp := exteriorParityAction_properties (G := ℂˣ) (V := V) i
  refine { U with invFun := B, left_inv := ?_, right_inv := ?_ }
  · intro a
    have h : B.comp U = LinearMap.id := by
      change (exteriorParityAction z⁻¹ i).comp (exteriorParityAction z i) = _
      rw [← hp.2.1, inv_mul_cancel, hp.1]
    exact LinearMap.congr_fun h a
  · intro a
    have h : U.comp B = LinearMap.id := by
      change (exteriorParityAction z i).comp (exteriorParityAction z⁻¹ i) = _
      rw [← hp.2.1, mul_inv_cancel, hp.1]
    exact LinearMap.congr_fun h a

/-- This phase is the actual exterior map of scalar multiplication by `i`. -/
theorem exteriorHodgePhaseEquiv_apply (i : ZMod 2)
    (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i) :
    (exteriorHodgePhaseEquiv V i a : ExteriorAlgebra ℂ V) =
      ExteriorAlgebra.map (Complex.I • (LinearMap.id : V →ₗ[ℂ] V)) a.val := rfl

variable {V}

/-- The same parity phase conjugates the positive Koszul map to the Hodge principal map. -/
theorem exteriorHodgePhaseEquiv_koszulSymbolParity (v : V) (i : ZMod 2)
    (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i) :
    exteriorHodgePhaseEquiv V (i + 1) (koszulSymbolParity v i a) =
      Complex.I • cliffordSymbolParity v i (exteriorHodgePhaseEquiv V i a) := by
  let F := ExteriorAlgebra.map (Complex.I • (LinearMap.id : V →ₗ[ℂ] V))
  have hι (w : V) : F (ExteriorAlgebra.ι ℂ w) = Complex.I • ExteriorAlgebra.ι ℂ w := by
    rw [ExteriorAlgebra.map_apply_ι]
    exact (ExteriorAlgebra.ι ℂ).map_smul Complex.I w
  -- Contraction lowers degree, giving the inverse phase to exterior multiplication.
  have hcontract (b : ExteriorAlgebra ℂ V) :
      contraction v (F b) = Complex.I • F (contraction v b) := by
    induction b using CliffordAlgebra.left_induction with
    | algebraMap c =>
      simp [F, contraction, CliffordAlgebra.contractLeft_algebraMap]
    | add b c hb hc =>
      simp only [map_add, hb, hc, smul_add]
    | ι_mul b w hb =>
      change CliffordAlgebra.contractLeft (innerₛₗ ℂ v)
        (F (ExteriorAlgebra.ι ℂ w * b)) =
          Complex.I • F (CliffordAlgebra.contractLeft (innerₛₗ ℂ v)
            (ExteriorAlgebra.ι ℂ w * b))
      rw [map_mul, hι, smul_mul_assoc, map_smul,
        CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul]
      change Complex.I • ((innerₛₗ ℂ v w) • F b -
        ExteriorAlgebra.ι ℂ w * contraction v (F b)) =
          Complex.I • F ((innerₛₗ ℂ v w) • b -
            ExteriorAlgebra.ι ℂ w * contraction v b)
      rw [hb, map_sub, map_smul, map_mul, hι, smul_mul_assoc, mul_smul_comm]
  have hcontract' (b : ExteriorAlgebra ℂ V) :
      F (contraction v b) = -Complex.I • contraction v (F b) := by
    rw [hcontract, smul_smul]
    simp
  -- Wedge raises degree; combine its `i` with contraction's `-i` on these same fibers.
  apply Subtype.ext
  rw [exteriorHodgePhaseEquiv_apply, (koszulSymbolParity_formula (V := V)).1]
  change F (exteriorMultiplication v a.val + contraction v a.val) =
    Complex.I • cliffordSymbol v (F a.val)
  change F (ExteriorAlgebra.ι ℂ v * a.val + contraction v a.val) =
    Complex.I • (ExteriorAlgebra.ι ℂ v * F a.val - contraction v (F a.val))
  rw [map_add, map_mul, hι, hcontract', smul_mul_assoc]
  simp [sub_eq_add_neg, smul_add]

/-- The canonical degree phase commutes with every original complex-linear exterior map. -/
theorem exteriorHodgePhaseEquiv_naturality {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (f : V →ₗ[ℂ] W)
    (i : ZMod 2) (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i) :
    ExteriorAlgebra.map f (exteriorHodgePhaseEquiv V i a).val =
      ExteriorAlgebra.map (Complex.I • (LinearMap.id : W →ₗ[ℂ] W))
        (ExteriorAlgebra.map f a.val) := by
  rw [exteriorHodgePhaseEquiv_apply]
  have h : (ExteriorAlgebra.map f).comp
      (ExteriorAlgebra.map (Complex.I • (LinearMap.id : V →ₗ[ℂ] V))) =
      (ExteriorAlgebra.map (Complex.I • (LinearMap.id : W →ₗ[ℂ] W))).comp
        (ExteriorAlgebra.map f) := by
    rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map]
    congr 1
    ext v
    exact f.map_smul Complex.I v
  exact AlgHom.congr_fun h a.val

end AtiyahSinger

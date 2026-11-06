/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorParity
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# The finite-dimensional topology on the exterior symbol

Public module ID: M0023.

The actual exterior algebra is given the norm pulled back from its finite exterior-basis
coordinates. This norm is an implementation choice: all norms on a finite-dimensional
complex vector space induce the same vector-space topology. The even and odd parts retain
mathlib's submodule carriers and inherit the subspace topology. No new exterior algebra,
parity grading or symbol map is introduced.

Finite dimensionality is a canonical instance. The chosen norm structures are enabled only
locally. Consumers can activate the same structures with `attribute [local instance]
exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace`.

The continuity statements are the finite-dimensional topology needed for the exterior
symbol triple of Spin Geometry, Appendix C, and Karoubi, K-Theory, IV.1.5. They concern the
existing negative-square Clifford symbol and its specified inverse, not an arbitrary family
of fiberwise isomorphisms. No positive-dimensional assumption is imposed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Finite dimensionality of the actual exterior algebra, from its finite exterior basis. -/
instance exteriorAlgebra_finiteDimensional : FiniteDimensional ℂ (ExteriorAlgebra ℂ V) :=
  Module.Finite.of_basis (Module.finBasis ℂ V).ExteriorAlgebra

/-- A coordinate norm realizing the unique finite-dimensional exterior-algebra topology. -/
@[instance_reducible]
def exteriorAlgebraNormedAddCommGroup : NormedAddCommGroup (ExteriorAlgebra ℂ V) :=
  let e := (Module.finBasis ℂ V).ExteriorAlgebra.equivFun
  NormedAddCommGroup.induced _ _ e e.injective

attribute [local instance] exteriorAlgebraNormedAddCommGroup

/-- Complex scalar multiplication for the same pulled-back exterior coordinate norm. -/
@[instance_reducible]
def exteriorAlgebraNormedSpace : NormedSpace ℂ (ExteriorAlgebra ℂ V) :=
  NormedSpace.induced ℂ _ _ (Module.finBasis ℂ V).ExteriorAlgebra.equivFun

attribute [local instance] exteriorAlgebraNormedSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- Joint continuity of the actual Clifford action between the standard parity subspaces. -/
theorem continuous_cliffordSymbolParity (i : ZMod 2) :
    Continuous (fun p : V × CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i ↦
      cliffordSymbolParity p.1 i p.2) := by
  /- Regard wedge multiplication and contraction as families of continuous linear
  operators on the same finite-dimensional exterior space. The wedge family is
  linear in v; contraction factors through the continuous conjugate-linear inner
  product map. Evaluation of these operator families is jointly continuous.
  Subtraction and the inherited parity subspace topology give the stated map. -/
  -- Finite-dimensional linear maps are continuous for the original coordinate norm.
  let wedge : V →ₗ[ℂ] ExteriorAlgebra ℂ V →L[ℂ] ExteriorAlgebra ℂ V :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((Algebra.lmul ℂ (ExteriorAlgebra ℂ V)).toLinearMap.comp (ExteriorAlgebra.ι ℂ))
  let contract : (V →L[ℂ] ℂ) →ₗ[ℂ] ExteriorAlgebra ℂ V →L[ℂ] ExteriorAlgebra ℂ V :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      (CliffordAlgebra.contractLeft.comp (ContinuousLinearMap.coeLM ℂ))
  have hw : Continuous (fun p : V × ExteriorAlgebra ℂ V ↦ wedge p.1 p.2) :=
    (wedge.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
  have hc : Continuous (fun p : V × ExteriorAlgebra ℂ V ↦ contract (innerSL ℂ p.1) p.2) :=
    (contract.continuous_of_finiteDimensional.comp
      ((innerSL ℂ).continuous.comp continuous_fst)).clm_apply continuous_snd
  -- Restriction changes only the codomain carrier, not the negative-square symbol.
  have hamb : Continuous (fun p : V × ExteriorAlgebra ℂ V ↦ cliffordSymbol p.1 p.2) :=
    hw.sub hc
  apply Continuous.subtype_mk
  change Continuous (fun p : V × CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i ↦
    cliffordSymbol p.1 p.2.val)
  have hinput : Continuous (fun p : V × CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i ↦
      (p.1, (p.2 : ExteriorAlgebra ℂ V))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hcomp := hamb.comp hinput
  apply hcomp.congr
  intro p
  rfl

/-- Joint continuity of the specified inverse symbol on the complement of the zero vector. -/
theorem continuous_cliffordSymbolParityEquiv_symm (i : ZMod 2) :
    Continuous (fun p : {v : V // v ≠ 0} ×
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) ↦
      (cliffordSymbolParityEquiv p.1.val p.1.property i).symm p.2) := by
  /- Stage 1: cliffordSymbolParityEquiv_symm_apply identifies the ambient value of
  this inverse with -‖v‖⁻² times the original Clifford action. The scalar factor
  is continuous on the punctured vector space because the norm never vanishes.
  Stage 2: combine joint continuity of the parity action with continuous scalar
  multiplication and the equality (i+1)+1=i in ZMod 2. The inherited subspace
  topology then proves continuity into parity i. This checks the actual inverse
  chosen by cliffordSymbolParityEquiv, including its negative-square convention. -/
  -- Coerce the specified inverse to the ambient exterior algebra and use its exact formula.
  apply Continuous.subtype_mk
  change Continuous (fun p : {v : V // v ≠ 0} ×
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) ↦
      ((cliffordSymbolParityEquiv p.1.val p.1.property i).symm p.2 : ExteriorAlgebra ℂ V))
  simp_rw [cliffordSymbolParityEquiv_symm_apply]
  have hvec : Continuous (fun p : {v : V // v ≠ 0} ×
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) ↦ p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hnorm : Continuous (fun p : {v : V // v ≠ 0} ×
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1) ↦ (‖p.1.val‖ ^ 2 : ℂ)) :=
    (Complex.continuous_ofReal.comp hvec.norm).pow 2
  have hnonzero (p : {v : V // v ≠ 0} ×
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) (i + 1)) :
      (‖p.1.val‖ ^ 2 : ℂ) ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr p.1.property))
  -- The same parity action is continuous before multiplying by the nonvanishing scalar.
  have haction := (continuous_cliffordSymbolParity (i + 1)).comp
    (hvec.prodMk continuous_snd)
  exact (hnorm.inv₀ hnonzero).neg.smul (continuous_subtype_val.comp haction)

end AtiyahSinger

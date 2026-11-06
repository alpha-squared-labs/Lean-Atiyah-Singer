/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# The two Clifford actions under the original exterior comparison

Public module ID: M0001.

Mathlib's form-change equivalence carries left Clifford multiplication to
creation minus contraction. The graded right action has the opposite
contraction sign. The same comparison respects grading and is natural for
the specified quadratic isometries. These identities identify the actual
doubled spinor symbol with the exterior symbol on the complexification.

Source: the standard Chevalley construction of the Clifford representation
on the exterior algebra; the form-change map is mathlib's existing map.
-/

@[expose] public noncomputable section

namespace CliffordAlgebra

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {Q : QuadraticForm R M}

/-- Contraction is odd for the actual Clifford grading, for every quadratic form. -/
theorem involute_contractLeft (l : Module.Dual R M) (a : CliffordAlgebra Q) :
    involute (contractLeft l a) = -contractLeft l (involute a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]
  | ι_mul a v ha =>
    simp only [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι,
      ha, neg_mul, map_neg]
    simp

/-- The supercommutator of a vector is contraction by its original polar functional. -/
theorem contractLeft_polarBilin (v : M) (a : CliffordAlgebra Q) :
    contractLeft (Q.polarBilin v) a = ι Q v * a - involute a * ι Q v := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap, involute.commutes]
    exact (sub_eq_zero.mpr (Algebra.commutes r (ι Q v)).symm).symm
  | add a b ha hb =>
    simp only [map_add, mul_add, add_mul, ha, hb]
    abel
  | ι_mul a w ha =>
    rw [contractLeft_ι_mul, ha, map_mul, involute_ι]
    rw [Algebra.smul_def, QuadraticMap.polarBilin_apply_apply, ← ι_mul_ι_add_swap]
    noncomm_ring

variable [Invertible (2 : R)]

/-- The existing form-change equivalence retains the actual Clifford grading. -/
theorem equivExterior_involute (a : CliffordAlgebra Q) :
    equivExterior Q (involute a) = involute (equivExterior Q a) := by
  change changeForm changeForm.associated_neg_proof (involute a) =
    involute (changeForm changeForm.associated_neg_proof a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a v ha =>
    rw [map_mul, involute_ι, neg_mul, map_neg, changeForm_ι_mul, ha,
      changeForm_ι_mul, map_sub, map_mul, involute_ι, involute_contractLeft, neg_mul]
    abel

/-- Under the actual exterior comparison, graded right multiplication adds contraction. -/
theorem equivExterior_involute_mul_ι (a : CliffordAlgebra Q) (v : M) :
    equivExterior Q (involute a * ι Q v) =
      ExteriorAlgebra.ι R v * equivExterior Q a +
        contractLeft (QuadraticMap.associated (-Q) v) (equivExterior Q a) := by
  let B := QuadraticMap.associated (-Q)
  have hpolar : Q.polarBilin v = -(B v + B v) := by
    apply LinearMap.ext
    intro w
    have h : B v w + B v w = (-Q).polarBilin v w := by
      simpa only [two_smul, LinearMap.add_apply, B] using
        congrArg (fun b : LinearMap.BilinForm R M ↦ b v w)
          (QuadraticMap.two_nsmul_associated R (-Q))
    change Q.polarBilin v w = -(B v w + B v w)
    rw [h]
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      neg_apply]
    abel
  have hright : involute a * ι Q v = ι Q v * a - contractLeft (Q.polarBilin v) a := by
    rw [contractLeft_polarBilin]
    abel
  rw [hright, map_sub]
  change changeForm changeForm.associated_neg_proof (ι Q v * a) -
    changeForm changeForm.associated_neg_proof (contractLeft (Q.polarBilin v) a) = _
  rw [changeForm_ι_mul, changeForm_contractLeft, hpolar]
  change ExteriorAlgebra.ι R v * equivExterior Q a -
      contractLeft (B v) (equivExterior Q a) -
        contractLeft (-(B v + B v)) (equivExterior Q a) = _
  rw [map_neg, LinearMap.neg_apply, map_add, LinearMap.add_apply]
  abel

/-- The same exterior comparison is natural for every supplied quadratic isometry. -/
theorem equivExterior_map {Q' : QuadraticForm R N} (f : Q →qᵢ Q')
    (a : CliffordAlgebra Q) :
    equivExterior Q' (CliffordAlgebra.map f a) =
      ExteriorAlgebra.map f.toLinearMap (equivExterior Q a) := by
  let B := QuadraticMap.associated (-Q)
  let B' := QuadraticMap.associated (-Q')
  -- Polarization uses the very same quadratic isometry, without a chosen basis or an inverse.
  have hB (v w : M) : B' (f v) (f w) = B v w := by
    change QuadraticMap.associatedHom R (-Q') (f v) (f w) =
      QuadraticMap.associatedHom R (-Q) v w
    simp only [QuadraticMap.associated_apply, neg_apply, ← map_add f,
      QuadraticMap.Isometry.map_app]
  have hcontract (v : M) (b : ExteriorAlgebra R M) :
      contractLeft (B' (f v)) (ExteriorAlgebra.map f.toLinearMap b) =
        ExteriorAlgebra.map f.toLinearMap (contractLeft (B v) b) := by
    induction b using CliffordAlgebra.left_induction with
    | algebraMap r => simp
    | add b c hb hc => simp only [map_add, hb, hc]
    | ι_mul b w hb =>
      rw [map_mul, ExteriorAlgebra.map_apply_ι, contractLeft_ι_mul,
        contractLeft_ι_mul, map_sub, map_smul, map_mul, ExteriorAlgebra.map_apply_ι,
        hb]
      change B' (f v) (f w) • ExteriorAlgebra.map f.toLinearMap b -
        ExteriorAlgebra.ι R (f w) *
          ExteriorAlgebra.map f.toLinearMap (contractLeft (B v) b) = _
      rw [hB]
      rfl
  -- The defining creation/contraction recurrence uniquely determines form change.
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a v ha =>
    rw [map_mul, CliffordAlgebra.map_apply_ι]
    change changeForm changeForm.associated_neg_proof
        (ι Q' (f v) * CliffordAlgebra.map f a) =
      ExteriorAlgebra.map f.toLinearMap
        (changeForm changeForm.associated_neg_proof (ι Q v * a))
    rw [changeForm_ι_mul, changeForm_ι_mul]
    change ExteriorAlgebra.ι R (f v) * equivExterior Q' (CliffordAlgebra.map f a) -
        contractLeft (B' (f v)) (equivExterior Q' (CliffordAlgebra.map f a)) =
      ExteriorAlgebra.map f.toLinearMap
        (ExteriorAlgebra.ι R v * equivExterior Q a - contractLeft (B v) (equivExterior Q a))
    rw [ha, hcontract, map_sub, map_mul, ExteriorAlgebra.map_apply_ι]
    rfl

end CliffordAlgebra

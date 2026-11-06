/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Contraction in decomposable exterior coordinates

Public module ID: M0019.

The actual Clifford contraction at the zero quadratic form is the usual signed
sum which deletes one vector from a decomposable exterior product. This formula
fixes the slot order used in the comparison with insertion on alternating forms.

Source: standard contraction formula in exterior algebra, as used in SG II.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 600000 in
-- Follow the defining contraction rule from the first vector through the finite product.
/-- Contraction of a decomposable exterior product deletes each vector with its usual sign. -/
theorem exteriorContractLeft_ιMulti (d : Module.Dual ℂ V) (p : ℕ)
    (a : Fin (p + 1) → V) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ V)) d
        (ExteriorAlgebra.ιMulti ℂ (p + 1) a) =
      ∑ j : Fin (p + 1), ((-1 : ℤ) ^ j.val) •
        (d (a j) • ExteriorAlgebra.ιMulti ℂ p (j.removeNth a)) := by
  induction p with
  | zero =>
      simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
        CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one]
  | succ p ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, ih]
      conv_rhs => rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero]
      have hremove (j : Fin (p + 1)) :
          ExteriorAlgebra.ιMulti ℂ (p + 1) (j.succ.removeNth a) =
            ExteriorAlgebra.ι ℂ (a 0) *
              ExteriorAlgebra.ιMulti ℂ p (j.removeNth (Matrix.vecTail a)) := by
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        congr 2
        funext k
        simp [Fin.removeNth, Matrix.vecTail]
      simp_rw [hremove]
      rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, mul_smul_comm,
        Matrix.vecTail]
      rfl

/-- The actual contraction lowers the homogeneous exterior degree by one. -/
theorem exteriorContractLeft_mem_exteriorPower (d : Module.Dual ℂ V) (p : ℕ)
    (a : ExteriorAlgebra ℂ V) (ha : a ∈ ⋀[ℂ]^(p + 1) V) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ V)) d a ∈ ⋀[ℂ]^p V := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨v, rfl⟩ := ha
      rw [exteriorContractLeft_ιMulti]
      apply Submodule.sum_mem
      intro j _
      exact (⋀[ℂ]^p V).toAddSubgroup.zsmul_mem
        ((⋀[ℂ]^p V).smul_mem _ (ExteriorAlgebra.ιMulti_range ℂ p (Set.mem_range_self _))) _
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  | smul z a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ z ha

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.Complexification
public import AtiyahSinger.Topology.ComplexBundleRealOrientation
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The sign from ordered real blocks to complex coordinate pairs

Public module ID: M1733.

The real and imaginary parts of a complexification form two ordered real
blocks. Its complex orientation uses interleaved pairs instead. The following
permutation records this actual coordinate change, including dimension zero.
It supplies the sign needed in the original Spin self tensor comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators TensorProduct

/-- Interleave two equally sized consecutive blocks, starting with the first block. -/
def equalBlockInterleave (n : ℕ) : Equiv.Perm (Fin (n + n)) :=
  let e : Fin n ⊕ Fin n ≃ Fin n × Fin 2 := {
    toFun := Sum.elim (fun i ↦ (i, 0)) (fun i ↦ (i, 1))
    invFun := fun x ↦ if x.2 = 0 then Sum.inl x.1 else Sum.inr x.1
    left_inv := by
      intro x
      cases x <;> rfl
    right_inv := by
      rintro ⟨i, k⟩
      fin_cases k <;> rfl }
  (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm.trans
    (e.trans (finProdFinEquiv.trans (finCongr (by omega))))

/-- Interleaving two real blocks contributes one sign for each reversed pair of coordinates. -/
theorem sign_equalBlockInterleave (n : ℕ) :
    Equiv.Perm.sign (equalBlockInterleave n) = (-1) ^ (n * (n - 1) / 2) := by
  classical
  let σ := equalBlockInterleave n
  have hleft (i : Fin n) : (σ (Fin.castAdd n i)).val = 2 * i.val := by
    simp [σ, equalBlockInterleave, finSumFinEquiv_symm_apply_castAdd, Nat.mul_comm]
  have hright (i : Fin n) : (σ (Fin.natAdd n i)).val = 2 * i.val + 1 := by
    simp only [σ, equalBlockInterleave, Equiv.trans_apply,
      finSumFinEquiv_symm_apply_natAdd]
    change 1 + 2 * i.val = 2 * i.val + 1
    omega
  -- Imaginary index j moves ahead of real index i precisely when j < i.
  have hsign : Equiv.Perm.sign σ = ∏ i : Fin n, (-1 : ℤˣ) ^ i.val := by
    rw [Equiv.Perm.sign_eq_prod_prod_Ioi, Fin.prod_univ_add]
    have hfirst (i : Fin n) :
        (∏ j ∈ Finset.Ioi (Fin.castAdd n i),
          (if σ (Fin.castAdd n i) < σ j then (1 : ℤˣ) else -1)) = (-1) ^ i.val := by
      have hprod : (∏ j ∈ Finset.Ioi (Fin.castAdd n i),
          (if σ (Fin.castAdd n i) < σ j then (1 : ℤˣ) else -1)) =
          ∏ j : Fin (n + n), if Fin.castAdd n i < j then
            (if σ (Fin.castAdd n i) < σ j then (1 : ℤˣ) else -1) else 1 := by
        rw [← Finset.prod_filter]
        congr 1
        ext j
        simp
      rw [hprod, Fin.prod_univ_add]
      have hLL (j : Fin n) :
          (if Fin.castAdd n i < Fin.castAdd n j then
            (if σ (Fin.castAdd n i) < σ (Fin.castAdd n j) then (1 : ℤˣ) else -1)
            else 1) = 1 := by
        split_ifs with h hσ
        · rfl
        · have hi := hleft i
          have hj := hleft j
          simp only [Fin.lt_def, Fin.val_castAdd] at h
          simp only [Fin.lt_def, not_lt] at hσ
          omega
        · rfl
      have hLR (j : Fin n) :
          (if Fin.castAdd n i < Fin.natAdd n j then
            (if σ (Fin.castAdd n i) < σ (Fin.natAdd n j) then (1 : ℤˣ) else -1)
            else 1) = if j < i then -1 else 1 := by
        have hi := hleft i
        have hj := hright j
        split_ifs <;> simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at * <;> omega
      simp only [hLL, hLR, Finset.prod_const_one, one_mul]
      rw [← Finset.prod_filter]
      rw [show (Finset.univ.filter fun j : Fin n ↦ j < i) = Finset.Iio i by
        ext j
        simp]
      simp
    have hsecond (i : Fin n) :
        (∏ j ∈ Finset.Ioi (Fin.natAdd n i),
          (if σ (Fin.natAdd n i) < σ j then (1 : ℤˣ) else -1)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      rw [ite_eq_left]
      have hlt : Fin.natAdd n i < j := Finset.mem_Ioi.mp hj
      revert hlt
      refine Fin.addCases (fun k hk ↦ ?_) (fun k hk ↦ ?_) j
      · simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hk
        omega
      · have hi := hright i
        have hkr := hright k
        simp only [Fin.lt_def, Fin.val_natAdd] at hk ⊢
        omega
    simp only [hfirst, hsecond, Finset.prod_const_one, mul_one]
  -- The number of reversed pairs is the triangular number n(n-1)/2.
  rw [hsign, Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) n).trans (Finset.sum_range_id n)

/-- Real/imaginary coordinates identify the complexified basis with the interleaved blocks. -/
theorem complexBasisRealification_baseChange_reIm {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ((complexBasisRealification (b.baseChange ℂ)).map (complexificationReIm V)).reindex
        (finCongr (show 2 * n = n + n by omega)) =
      ((b.prod b).reindex (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))).reindex
        (equalBlockInterleave n) := by
  let ρ : Fin n × Fin 2 ≃ Fin (2 * n) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))
  have hcoord (i : Fin n) (j : Fin 2) :
      complexBasisRealification (b.baseChange ℂ) (ρ (i, j)) =
        Complex.basisOneI j ⊗ₜ[ℝ] b i := by
    rw [complexBasisRealification, Module.Basis.reindex_apply]
    change (Complex.basisOneI.smulTower' (b.baseChange ℂ)) (ρ.symm (ρ (i, j))) = _
    rw [ρ.symm_apply_apply, Module.Basis.smulTower'_apply, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul']
    simp only [smul_eq_mul, mul_one]
  -- Compare the same real vector and its imaginary multiple, using no chosen replacement basis.
  apply DFunLike.ext
  intro k
  obtain ⟨j, rfl⟩ := (equalBlockInterleave n).surjective k
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply, Module.Basis.map_apply, Module.Basis.reindex_apply]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
  · have hidx : (finCongr (show 2 * n = n + n by omega)).symm
        (equalBlockInterleave n (Fin.castAdd n i)) = ρ (i, 0) := by
      simp only [equalBlockInterleave, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
      apply Fin.ext
      rfl
    rw [hidx, hcoord, finSumFinEquiv_symm_apply_castAdd,
      (complexificationReIm_properties V).1]
    simp
  · have hidx : (finCongr (show 2 * n = n + n by omega)).symm
        (equalBlockInterleave n (Fin.natAdd n i)) = ρ (i, 1) := by
      simp only [equalBlockInterleave, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
      apply Fin.ext
      rfl
    rw [hidx, hcoord, finSumFinEquiv_symm_apply_natAdd,
      (complexificationReIm_properties V).1]
    simp

/-- In even real rank the complexified orientation differs from the ordered double by (-1)^m. -/
theorem complexBasisRealification_baseChange_orientation {m : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] (b : Module.Basis (Fin (2 * m)) ℝ V) :
    (((complexBasisRealification (b.baseChange ℂ)).map (complexificationReIm V)).reindex
        (finCongr (show 2 * (2 * m) = 2 * m + 2 * m by omega))).orientation =
      (-1 : ℤˣ) ^ m •
        ((b.prod b).reindex
          (finSumFinEquiv : Fin (2 * m) ⊕ Fin (2 * m) ≃ Fin (2 * m + 2 * m))).orientation := by
  classical
  rw [complexBasisRealification_baseChange_reIm]
  -- Reindexing the determinant multiplies its ray by the sign of this exact permutation.
  have hsign (d : Module.Basis (Fin (2 * m + 2 * m)) ℝ (V × V))
      (σ : Equiv.Perm (Fin (2 * m + 2 * m))) :
      (d.reindex σ).orientation = Equiv.Perm.sign σ • d.orientation := by
    simp only [Module.Basis.orientation, Module.Basis.det_reindex',
      AlternatingMap.domDomCongr_perm, smul_rayOfNeZero]
  rw [hsign, sign_equalBlockInterleave]
  congr 1
  by_cases hm : m = 0
  · simp [hm]
  · have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
    rw [show 2 * m * (2 * m - 1) / 2 = m * (2 * m - 1) by
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)],
      Nat.mul_comm m (2 * m - 1), pow_mul, hodd.neg_one_pow]

end AtiyahSinger

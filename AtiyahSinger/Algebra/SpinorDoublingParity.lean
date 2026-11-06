/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorExteriorDoubling
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The parity blocks of the original spinor doubling equivalence

Public module ID: M0067.

The original exterior parity carriers of both spinor factors are kept.
The full doubling equivalence intertwines their tensor chirality with the
exterior involution shifted by the original half-dimension. Complementary
parity decompositions therefore restrict this exact equivalence to the two
required blocks, with explicit forward maps for the subsequent supported
symbol and associated-bundle comparisons.

Source: SG I.5, the graded self-tensor description of the spin representation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

set_option maxHeartbeats 800000 in
-- The original tensor decomposition is compared on all four pure-tensor blocks.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two actual spinor tensor parity blocks retain the original doubling map and shift. -/
theorem exists_complexSpinorDoublingParity_equiv (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t =
        e s (complexSpinorRepresentation m (star a) t)) :
    let V := EuclideanSpace ℂ (Fin m)
    let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
    let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (V × V))
    ∃ L₀ : ((P 0 ⊗[ℂ] P 0) × (P 1 ⊗[ℂ] P 1)) ≃ₗ[ℂ] PS (m : ZMod 2),
      ∃ L₁ : ((P 1 ⊗[ℂ] P 0) × (P 0 ⊗[ℂ] P 1)) ≃ₗ[ℂ] PS ((m : ZMod 2) + 1),
        (∀ z, (L₀ z).val = complexSpinorDoublingExteriorEquiv m e
          (TensorProduct.map (P 0).subtype (P 0).subtype z.1 +
            TensorProduct.map (P 1).subtype (P 1).subtype z.2)) ∧
        ∀ z, (L₁ z).val = complexSpinorDoublingExteriorEquiv m e
          (TensorProduct.map (P 1).subtype (P 0).subtype z.1 +
            TensorProduct.map (P 0).subtype (P 1).subtype z.2) := by
  classical
  let V := EuclideanSpace ℂ (Fin m)
  let U := V × V
  let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
  let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ U)
  let Φ := complexSpinorDoublingExteriorEquiv m e
  -- In characteristic zero the complementary parity spaces are exactly the two eigenspaces.
  have parity (i : ZMod 2) (x : ExteriorAlgebra ℂ U) :
      CliffordAlgebra.involute x = (-1 : ℂ) ^ i.val • x ↔ x ∈ PS i := by
    have hcompl := CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm ℂ U)
    have hsplit : x ∈ PS 0 ⊔ PS 1 := by
      rw [hcompl.codisjoint.eq_top]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsplit
    have haInv := CliffordAlgebra.involute_eq_of_mem_even ha
    have hbInv := CliffordAlgebra.involute_eq_of_mem_odd hb
    have htwo (y : ExteriorAlgebra ℂ U) (hy : -y = y) : y = 0 := by
      have hz : (2 : ℂ) • y = 0 := by
        calc
          (2 : ℂ) • y = y + y := two_smul _ _
          _ = y + -y := congrArg (y + ·) hy.symm
          _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
    fin_cases i
    · change (CliffordAlgebra.involute x = (-1 : ℂ) ^ (0 : ZMod 2).val • x) ↔ x ∈ PS 0
      simp only [ZMod.val_zero, pow_zero, one_smul]
      constructor
      · intro hx
        have hEq : a - b = a + b := by
          simpa only [← hab, map_add, haInv, hbInv, sub_eq_add_neg] using hx
        have hbzero : b = 0 := by
          apply htwo
          exact add_left_cancel (by simpa only [sub_eq_add_neg] using hEq)
        simpa [← hab, hbzero] using ha
      · exact CliffordAlgebra.involute_eq_of_mem_even
    · change (CliffordAlgebra.involute x = (-1 : ℂ) ^ (1 : ZMod 2).val • x) ↔ x ∈ PS 1
      simp only [ZMod.val_one, pow_one, neg_one_smul]
      constructor
      · intro hx
        have hEq : a - b = -(a + b) := by
          simpa only [← hab, map_add, haInv, hbInv, sub_eq_add_neg] using hx
        have hazero : a = 0 := by
          apply htwo
          symm
          apply add_right_cancel (b := -b)
          simpa only [sub_eq_add_neg, neg_add] using hEq
        simpa [← hab, hazero] using hb
      · exact CliffordAlgebra.involute_eq_of_mem_odd
  let γ := complexSpinorChirality m
  have hγ (i : ZMod 2) (x : P i) : γ x.val = (-1 : ℂ) ^ i.val • x.val := by
    have hx : x.val ∈ complexHalfSpinor m i := by
      simpa only [complexHalfSpinor_eq_evenOdd] using x.property
    exact Module.End.mem_eigenspace_iff.mp hx
  let T (i j : ZMod 2) : (P i ⊗[ℂ] P j) →ₗ[ℂ]
      ComplexSpinor m ⊗[ℂ] ComplexSpinor m :=
    TensorProduct.map (P i).subtype (P j).subtype
  have hT (i j : ZMod 2) (z : P i ⊗[ℂ] P j) :
      TensorProduct.map γ γ (T i j z) = (-1 : ℂ) ^ (i + j).val • T i j z := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, smul_add, hz, hz']
    | tmul a b =>
      simp only [T, TensorProduct.map_tmul, Submodule.subtype_apply, hγ,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
      fin_cases i <;> fin_cases j <;> norm_num [ZMod.val]
  have hsign : (-1 : ℂ) ^ m = (-1 : ℂ) ^ (m : ZMod 2).val := by
    rw [ZMod.val_natCast]
    exact neg_one_pow_eq_pow_mod_two m
  have hgrade (i j : ZMod 2) (z : P i ⊗[ℂ] P j) :
      Φ (T i j z) ∈ PS ((m : ZMod 2) + (i + j)) := by
    apply (parity _ _).mp
    have hc := complexSpinorDoublingExteriorEquiv_chirality m e he (T i j z)
    rw [hT, map_smul, hsign] at hc
    have hh := congrArg (fun y ↦ (-1 : ℂ) ^ (m : ZMod 2).val • y) hc
    have hsq : (-1 : ℂ) ^ (m : ZMod 2).val * (-1 : ℂ) ^ (m : ZMod 2).val = 1 := by
      generalize (m : ZMod 2) = k
      fin_cases k <;> norm_num [ZMod.val]
    have hmul : (-1 : ℂ) ^ (m : ZMod 2).val * (-1 : ℂ) ^ (i + j).val =
        (-1 : ℂ) ^ ((m : ZMod 2) + (i + j)).val := by
      generalize (m : ZMod 2) = k
      fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num [ZMod.val]
    simpa only [smul_smul, hsq, one_smul, hmul, Φ] using hh.symm
  let M₀ := Φ.toLinearMap.comp ((T 0 0).coprod (T 1 1))
  let M₁ := Φ.toLinearMap.comp ((T 1 0).coprod (T 0 1))
  have hM₀ (z : (P 0 ⊗[ℂ] P 0) × (P 1 ⊗[ℂ] P 1)) : M₀ z ∈ PS (m : ZMod 2) := by
    change Φ (T 0 0 z.1 + T 1 1 z.2) ∈ PS (m : ZMod 2)
    rw [map_add]
    apply Submodule.add_mem
    · have hz := hgrade 0 0 z.1
      rw [zero_add, add_zero] at hz
      exact hz
    · have hz := hgrade 1 1 z.2
      rw [show (1 : ZMod 2) + 1 = 0 from rfl, add_zero] at hz
      exact hz
  have hM₁ (z : (P 1 ⊗[ℂ] P 0) × (P 0 ⊗[ℂ] P 1)) :
      M₁ z ∈ PS ((m : ZMod 2) + 1) := by
    change Φ (T 1 0 z.1 + T 0 1 z.2) ∈ PS ((m : ZMod 2) + 1)
    rw [map_add]
    exact (PS ((m : ZMod 2) + 1)).add_mem (hgrade 1 0 z.1) (hgrade 0 1 z.2)
  let J₀ := M₀.codRestrict (PS (m : ZMod 2)) hM₀
  let J₁ := M₁.codRestrict (PS ((m : ZMod 2) + 1)) hM₁
  have hcompl : IsCompl (PS (m : ZMod 2)) (PS ((m : ZMod 2) + 1)) := by
    generalize (m : ZMod 2) = k
    fin_cases k
    · exact CliffordAlgebra.evenOdd_isCompl _
    · exact (CliffordAlgebra.evenOdd_isCompl _).symm
  -- Decompose both original factors, distribute their tensor product, and retain its order.
  let dV : (P 0 × P 1) ≃ₗ[ℂ] ComplexSpinor m :=
    Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
  let dW : (P 0 × P 1) ≃ₗ[ℂ] ComplexSpinor m :=
    Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
  let dS : (PS (m : ZMod 2) × PS ((m : ZMod 2) + 1)) ≃ₗ[ℂ] ExteriorAlgebra ℂ U :=
    Submodule.prodEquivOfIsCompl _ _ hcompl
  let R : (((P 0 ⊗[ℂ] P 0) × (P 1 ⊗[ℂ] P 1)) ×
      ((P 1 ⊗[ℂ] P 0) × (P 0 ⊗[ℂ] P 1))) ≃ₗ[ℂ]
        (((P 0 ⊗[ℂ] P 0) × (P 0 ⊗[ℂ] P 1)) ×
          ((P 1 ⊗[ℂ] P 0) × (P 1 ⊗[ℂ] P 1))) :=
    { toFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
      invFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let D := R.trans
    (((TensorProduct.prodRight ℂ ℂ (P 0) (P 0) (P 1)).symm.prodCongr
        (TensorProduct.prodRight ℂ ℂ (P 1) (P 0) (P 1)).symm).trans
      ((TensorProduct.prodLeft ℂ ℂ (P 0) (P 1) (P 0 × P 1)).symm.trans
        (TensorProduct.congr dV dW)))
  let B := Φ
  have hwhole : dS.toLinearMap.comp (J₀.prodMap J₁) = B.toLinearMap.comp D.toLinearMap := by
    apply LinearMap.prod_ext <;> apply LinearMap.prod_ext <;>
      apply TensorProduct.ext' <;> intro x y
    all_goals
      simp [J₀, J₁, M₀, M₁, T, B, D, R, dV, dW, dS,
        TensorProduct.prodRight, TensorProduct.prodLeft]
  have hjoint : Function.Bijective (J₀.prodMap J₁) := by
    have hcomp := B.bijective.comp D.bijective
    change Function.Bijective (B.toLinearMap.comp D.toLinearMap) at hcomp
    rw [← hwhole] at hcomp
    exact (Function.Bijective.of_comp_iff' dS.bijective (J₀.prodMap J₁)).mp hcomp
  -- The full graded equivalence is block diagonal, so each actual parity map is bijective.
  have h₀ : Function.Bijective J₀ := by
    constructor
    · intro x y h
      have heq : J₀.prodMap J₁ (x, 0) = J₀.prodMap J₁ (y, 0) := Prod.ext h rfl
      exact congrArg Prod.fst (hjoint.injective heq)
    · intro z
      obtain ⟨x, hx⟩ := hjoint.surjective (z, 0)
      exact ⟨x.1, congrArg Prod.fst hx⟩
  have h₁ : Function.Bijective J₁ := by
    constructor
    · intro x y h
      have heq : J₀.prodMap J₁ (0, x) = J₀.prodMap J₁ (0, y) := Prod.ext rfl h
      exact congrArg Prod.snd (hjoint.injective heq)
    · intro z
      obtain ⟨x, hx⟩ := hjoint.surjective (0, z)
      exact ⟨x.2, congrArg Prod.snd hx⟩
  exact ⟨LinearEquiv.ofBijective J₀ h₀, LinearEquiv.ofBijective J₁ h₁,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RightPolynomialCokernel
public import AtiyahSinger.Topology.BottSurjectivity

/-!
# Right-module cokernels of polynomial shifts of Laurent loops

Public module ID: M2111.

For a complex Banach algebra, including noncommutative coefficients,
the actual positive multiplier of z^k sigma has a finite projective right
module cokernel. Increasing k by l adds the free right module A^(n*l).
The right action is expressed as a left action of the opposite ring Aᵐᵒᵖ.
Both quotients use the original PositiveWienerModule carrier and the
specified LaurentMatrixLoop.shift polynomial, without replacing the loop
or changing which side its matrix coefficients multiply on.

Sources: Karoubi, K-Theory, III.1.18, pp.118--119. Finite projectivity uses
the exact finite-bandwidth defect projection from RightPolynomialCokernel.
No positivity or finite-support assumption is imposed on the bilateral
inverse. The shift formula uses the original forward and backward shifts
together with the first l coefficient vectors. Their joint map has kernel
equal to the further shifted multiplier range and maps onto the displayed sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped Matrix.Norms.Operator

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

namespace LaurentMatrixLoop

/-- The actual right-module quotient for multiplication by the specified z^k sigma. -/
abbrev RightShiftedCokernel (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) : Type u :=
  RightWiener.PolynomialCokernel (p.shift (k : ℤ)).polynomial hk

/-- The specified shifted quotient is finitely generated as a right A-module. -/
theorem rightShiftedCokernel_finite (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    Module.Finite Aᵐᵒᵖ (p.RightShiftedCokernel k hk) := by
  /- Use finite-support Wiener inversion and (p.shift k).invertible to
  obtain one bilateral inverse g of the actual shifted polynomial. Retain
  both inverse equations for that same g, then apply
  RightWiener.polynomialCokernel_finite with the original polynomial,
  nonnegative-support certificate hk, g and its two equations. All scalar
  actions are right multiplication on coefficient vectors, expressed
  through Aᵐᵒᵖ. The finite-bandwidth splitting is for this quotient itself,
  not a substitute projective module. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let : CompleteSpace (Matrix (Fin p.size) (Fin p.size) A) :=
      inferInstanceAs (CompleteSpace (Fin p.size → Fin p.size → A))
    let f : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A) :=
      (p.shift (k : ℤ)).polynomial
    have hfinite : (Function.support (fun j : ℤ ↦ laurentPolynomialWiener f j)).Finite := by
      simpa only [Function.HasFiniteSupport, laurentPolynomialWiener_coeff] using
        f.coeff.hasFiniteSupport
    have hunit : IsUnit (laurentPolynomialWiener f) :=
      WienerLoop.isUnit_of_finiteSupport _ hfinite fun z ↦ by
        simpa only [laurentPolynomialWiener_eval] using (p.shift (k : ℤ)).invertible z
    obtain ⟨u, hu⟩ := hunit
    -- Both inverse equations retain this single bilateral inverse of the specified shift.
    let g : WienerLoop (Matrix (Fin p.size) (Fin p.size) A) := ↑(u⁻¹)
    have hgf : g * laurentPolynomialWiener f = 1 := by
      rw [← hu]
      exact Units.inv_mul u
    have hfg : laurentPolynomialWiener f * g = 1 := by
      rw [← hu]
      exact Units.mul_inv u
    exact RightWiener.polynomialCokernel_finite f hk g hgf hfg

/-- The same original quotient is a projective right A-module. -/
theorem rightShiftedCokernel_projective (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    Module.Projective Aᵐᵒᵖ (p.RightShiftedCokernel k hk) := by
  /- Finite-support Wiener inversion applied to this shifted loop supplies
  one bilateral inverse g and both inverse equations. Apply
  RightWiener.polynomialCokernel_projective with the identical shifted
  polynomial, hk and that g. Its actual low-coefficient splitting exhibits
  this range quotient as a direct summand of a finite free right A-module.
  No coefficient commutation or inverse polynomial is needed. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let : CompleteSpace (Matrix (Fin p.size) (Fin p.size) A) :=
      inferInstanceAs (CompleteSpace (Fin p.size → Fin p.size → A))
    let f : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A) :=
      (p.shift (k : ℤ)).polynomial
    have hfinite : (Function.support (fun j : ℤ ↦ laurentPolynomialWiener f j)).Finite := by
      simpa only [Function.HasFiniteSupport, laurentPolynomialWiener_coeff] using
        f.coeff.hasFiniteSupport
    have hunit : IsUnit (laurentPolynomialWiener f) :=
      WienerLoop.isUnit_of_finiteSupport _ hfinite fun z ↦ by
        simpa only [laurentPolynomialWiener_eval] using (p.shift (k : ℤ)).invertible z
    obtain ⟨u, hu⟩ := hunit
    -- Use the same actual inverse in both multiplication orders over the original ring.
    let g : WienerLoop (Matrix (Fin p.size) (Fin p.size) A) := ↑(u⁻¹)
    have hgf : g * laurentPolynomialWiener f = 1 := by
      rw [← hu]
      exact Units.inv_mul u
    have hfg : laurentPolynomialWiener f * g = 1 := by
      rw [← hu]
      exact Units.mul_inv u
    exact RightWiener.polynomialCokernel_projective f hk g hgf hfg

/-- KA III.1.18: a further positive shift adds exactly n*l free right generators. -/
theorem nonempty_rightShiftedCokernel_add_equiv (p : LaurentMatrixLoop A) (k l : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    ∃ hkl : (p.shift ((k + l : ℕ) : ℤ)).IsPolynomial,
      Nonempty (p.RightShiftedCokernel (k + l) hkl ≃ₗ[Aᵐᵒᵖ]
        p.RightShiftedCokernel k hk × (Fin (p.size * l) → A)) := by
  /- Stage 1: multiplication by the central monomial z^l shifts the given
  nonnegative polynomial z^k sigma to the actual polynomial of p.shift (k+l).
  Its coefficients are the original coefficients with the degree shifted by l.
  Stage 2: on the original positive right module let T be multiplication
  by z^k sigma and U multiplication by z^(k+l) sigma. The original forward
  and backward monomial maps Z and H satisfy U=ZT and HZ=id. Let C extract
  the first l vector coefficients and J include them as finite series. Then
  CZ=0, CJ=id, HJ=0 and ZH+JC=id, with all maps right-linear.
  Stage 3: if Q is the original quotient by range T, the map x ↦ (Q(Hx),Cx)
  has kernel exactly range U. One inclusion uses U=ZT; the other uses
  ZH+JC=id and the quotient kernel. It is surjective: a representative x
  of q gives the preimage Zx+Jv of (q,v). Apply the first isomorphism theorem
  and flatten the same finite indices to exactly p.size*l scalar coordinates.
  This gives the displayed equivalence of actual quotients, including l=0
  and p.size=0. Matrices act on columns from the left and scalars act from
  the right; no commutativity of A is needed. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let : CompleteSpace (Matrix (Fin p.size) (Fin p.size) A) :=
      inferInstanceAs (CompleteSpace (Fin p.size → Fin p.size → A))
    have monomial_coeff {n : ℕ} (d : ℤ) (x : PositiveWienerModule A n) (k : ℕ) :
        RightWiener.toeplitz
            (lp.single 1 d (1 : Matrix (Fin n) (Fin n) A)) x k =
          if 0 ≤ (k : ℤ) - d then x ((k : ℤ) - d).toNat else 0 := by
      classical
      change (∑' j : ℕ,
        ((lp.single 1 d (1 : Matrix (Fin n) (Fin n) A) :
          WienerLoop (Matrix (Fin n) (Fin n) A)) ((k : ℤ) - j)).mulVec (x j)) = _
      by_cases h : 0 ≤ (k : ℤ) - d
      · rw [ite_eq_left h]
        have heq : d = (k : ℤ) - ((k : ℤ) - d).toNat := by omega
        rw [tsum_eq_single ((k : ℤ) - d).toNat]
        · simp only [lp.coeFn_single, Pi.single_apply]
          rw [ite_eq_left heq.symm, Matrix.one_mulVec]
        · intro j hj
          have hne : d ≠ (k : ℤ) - j := by omega
          simp only [lp.coeFn_single, Pi.single_apply, Ne.symm hne, ite_false, Matrix.zero_mulVec]
      · rw [ite_eq_right h]
        calc
          _ = ∑' j : ℕ, (0 : Fin n → A) := by
            congr 1
            funext j
            have hne : d ≠ (k : ℤ) - j := by omega
            simp only [lp.coeFn_single, Pi.single_apply, Ne.symm hne, ite_false, Matrix.zero_mulVec]
          _ = 0 := by simp
    -- Identify the same shifted polynomial, coefficient by coefficient.
    let f : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A) :=
      (p.shift (k : ℤ)).polynomial
    let f' : LaurentPolynomial (Matrix (Fin p.size) (Fin p.size) A) :=
      (p.shift ((k + l : ℕ) : ℤ)).polynomial
    have hpositive (j : ℤ) (hj : j < 0) : f.coeff j = 0 := hk j hj
    have hcoeff (j : ℤ) :
        f'.coeff j = f.coeff (j - l) := by
      change (LaurentPolynomial.T ((k + l : ℕ) : ℤ) * p.polynomial).coeff j =
        (LaurentPolynomial.T (k : ℤ) * p.polynomial).coeff (j - l)
      simp only [LaurentPolynomial.T,
        AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
      congr 1
      omega
    have hkl : (p.shift ((k + l : ℕ) : ℤ)).IsPolynomial := by
      intro j hj
      change f'.coeff j = 0
      rw [hcoeff]
      exact hpositive _ (by omega)
    refine ⟨hkl, ?_⟩
    let X := PositiveWienerModule A p.size
    let T : X →ₗ[Aᵐᵒᵖ] X :=
      RightWiener.polynomialMultiplier f hk
    let U : X →ₗ[Aᵐᵒᵖ] X :=
      RightWiener.polynomialMultiplier f' hkl
    let Z : X →ₗ[Aᵐᵒᵖ] X :=
      RightWiener.toeplitz (lp.single 1 (l : ℤ) (1 : Matrix (Fin p.size) (Fin p.size) A))
    let H : X →ₗ[Aᵐᵒᵖ] X :=
      RightWiener.toeplitz (lp.single 1 (-(l : ℤ)) (1 : Matrix (Fin p.size) (Fin p.size) A))
    have hZ (x : X) (j : ℕ) : Z x j = if l ≤ j then x (j - l) else 0 := by
      rw [monomial_coeff]
      have hcast : ((j : ℤ) - (l : ℤ)).toNat = j - l := by omega
      have hle : (0 ≤ (j : ℤ) - l) ↔ l ≤ j := by omega
      simp only [hle, hcast]
    have hH (x : X) (j : ℕ) : H x j = x (j + l) := by
      rw [monomial_coeff, ite_eq_left (show 0 ≤ (j : ℤ) - -(l : ℤ) by omega)]
      apply congrArg (fun r : ℕ ↦ x r)
      omega
    -- Positive and negative monomials give genuine maps of the original ℓ¹ carrier.
    have hHZ (x : X) : H (Z x) = x := by
      apply lp.ext
      funext j
      rw [hH, hZ, ite_eq_left (by omega)]
      apply congrArg (fun r : ℕ ↦ x r)
      omega
    have hU (x : X) : U x = Z (T x) := by
      apply lp.ext
      funext i
      change (∑' j : ℕ,
        (laurentPolynomialWiener f' ((i : ℤ) - j)).mulVec (x j)) = Z (T x) i
      rw [hZ]
      split_ifs with hli
      · change _ = ∑' j : ℕ,
          (laurentPolynomialWiener f (((i - l : ℕ) : ℤ) - j)).mulVec (x j)
        apply tsum_congr
        intro j
        rw [laurentPolynomialWiener_coeff, hcoeff, laurentPolynomialWiener_coeff]
        have heq : (i : ℤ) - j - l = ((i - l : ℕ) : ℤ) - j := by omega
        rw [heq]
      · calc
          _ = ∑' j : ℕ, (0 : Fin p.size → A) := by
            apply tsum_congr
            intro j
            rw [laurentPolynomialWiener_coeff, hcoeff, hpositive _ (by omega),
              Matrix.zero_mulVec]
          _ = 0 := by simp
    let C : X →ₗ[Aᵐᵒᵖ] (Fin l → Fin p.size → A) :=
      LinearMap.pi fun j : Fin l ↦ lp.evalₗ (fun _ : ℕ ↦ Fin p.size → A) 1 (j : ℕ)
    let J : (Fin l → Fin p.size → A) →ₗ[Aᵐᵒᵖ] X :=
      { toFun v := ∑ j : Fin l,
          lp.single (E := fun _ : ℕ ↦ Fin p.size → A) 1 (j : ℕ) (v j)
        map_add' v w := by
          simp only [Pi.add_apply, lp.single_add, Finset.sum_add_distrib]
        map_smul' a v := by
          simp only [Pi.smul_apply, lp.single_smul, Finset.smul_sum, RingHom.id_apply] }
    have hJapply (v : Fin l → Fin p.size → A) :
        J v = ∑ i : Fin l, lp.single (E := fun _ : ℕ ↦ Fin p.size → A) 1 (i : ℕ) (v i) := by
      rfl
    have hJlow (v : Fin l → Fin p.size → A) (j : Fin l) : J v j = v j := by
      rw [hJapply]
      rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i hi hne
        apply lp.single_apply_ne
        intro heq
        exact hne (Fin.ext heq.symm)
      · simp
    have hJhigh (v : Fin l → Fin p.size → A) (j : ℕ) (hj : l ≤ j) : J v j = 0 := by
      rw [hJapply]
      rw [lp.coeFn_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      apply lp.single_apply_ne
      have hil := i.isLt
      omega
    have hCZ (x : X) : C (Z x) = 0 := by
      funext j
      change Z x (j : ℕ) = 0
      rw [hZ, ite_eq_right (by have hj := j.isLt; omega)]
    have hCJ (v : Fin l → Fin p.size → A) : C (J v) = v := by
      funext j
      exact hJlow v j
    have hHJ (v : Fin l → Fin p.size → A) : H (J v) = 0 := by
      apply lp.ext
      funext j
      rw [hH, hJhigh v _ (by omega)]
      rfl
    have hdecomp (x : X) : Z (H x) + J (C x) = x := by
      apply lp.ext
      funext j
      change Z (H x) j + J (C x) j = x j
      rw [hZ]
      split_ifs with hlj
      · rw [hH, hJhigh _ _ hlj, add_zero]
        apply congrArg (fun r : ℕ ↦ x r)
        omega
      · rw [zero_add]
        exact hJlow (C x) ⟨j, by omega⟩
    -- The low-coefficient projection and backward shift give the actual quotient decomposition.
    let Q : X →ₗ[Aᵐᵒᵖ] p.RightShiftedCokernel k hk :=
      RightWiener.polynomialCokernelMk f hk
    let F : X →ₗ[Aᵐᵒᵖ]
        p.RightShiftedCokernel k hk × (Fin l → Fin p.size → A) := (Q.comp H).prod C
    have hQT (x : X) : Q (T x) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨x, rfl⟩
    have hker : LinearMap.range U = LinearMap.ker F := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        change (Q (H (U y)), C (U y)) = 0
        rw [hU, hHZ, hQT, hCZ]
        rfl
      · intro x hx
        have hx₁ : Q (H x) = 0 := congrArg Prod.fst hx
        have hx₂ : C x = 0 := congrArg Prod.snd hx
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx₁
        refine ⟨y, ?_⟩
        rw [hU, show T y = H x from hy]
        simpa only [hx₂, map_zero, add_zero] using hdecomp x
    have hsurj : Function.Surjective F := by
      rintro ⟨q, v⟩
      obtain ⟨x, rfl⟩ := (LinearMap.range T).mkQ_surjective q
      refine ⟨Z x + J v, ?_⟩
      change (Q (H (Z x + J v)), C (Z x + J v)) = (Q x, v)
      rw [map_add, hHZ, hHJ, add_zero, map_add, hCZ, hCJ, zero_add]
    let e := (Submodule.quotEquivOfEq (LinearMap.range U) (LinearMap.ker F) hker).trans
      (F.quotKerEquivOfSurjective hsurj)
    -- Reindex the same first-l vectors to exactly size*l scalar coordinates.
    let efin : (Fin l → Fin p.size → A) ≃ₗ[Aᵐᵒᵖ] (Fin (p.size * l) → A) :=
      { toFun v i := v (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm i).1
        invFun v j i := v (finProdFinEquiv (i, j))
        left_inv v := by funext j i; simp
        right_inv v := by
          funext i
          change v (finProdFinEquiv (finProdFinEquiv.symm i)) = v i
          rw [Equiv.apply_symm_apply]
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    exact ⟨e.trans ((LinearEquiv.refl _ _).prodCongr efin)⟩

end LaurentMatrixLoop

end AtiyahSinger

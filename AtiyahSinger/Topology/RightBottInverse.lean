/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.IdempotentHomotopy
public import AtiyahSinger.Topology.BottInverse
public import AtiyahSinger.Topology.RightBottCokernel
public import AtiyahSinger.Topology.RightBottSurjectivity
public import AtiyahSinger.Topology.RightProjectiveKZero

/-!
# The specified right-module cokernel inverse to the Bott loop map

Public module ID: M2106.

The inverse assigns a Laurent loop its actual positive right-module
cokernel after an admissible nonnegative shift, minus the free right module
of rank size*k. Shift independence, stable homotopy invariance and additivity
refer to that specified quotient. The function descends through the existing
Laurent quotient and its existing comparison with continuous stable loops.
No new loop carrier, inverse chosen from bijectivity, or opposite matrix is used.

The left-inverse identity uses the original p*z+(1-p) loop and its actual
constant-term quotient map onto the same right image of p. Together with
the independently constructed surjectivity this gives an additive equivalence
whose inverse is exactly the corrected cokernel map. For commutative
coefficients the whole inverse and each specified shifted index agree with
the old construction after the existing same-matrix K-zero comparison.

Sources: Karoubi, K-Theory, III.1.19--1.20, pp.119--120. The finite-bandwidth
defect construction produces a continuous finite projector family for the
homotopy argument. Its entries use finitely many original coefficients;
no base-change or flatness assertion for an infinite Wiener quotient is made.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RightKTheory

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The class of the original right multiplier quotient, with its specified free correction. -/
def shiftedCokernelIndex (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) : KZero A := by
  letI := p.rightShiftedCokernel_finite k hk
  letI := p.rightShiftedCokernel_projective k hk
  exact projectiveModuleKZeroClass A (p.RightShiftedCokernel k hk) -
    kZeroClass A (IdempotentMatrix.identity A (p.size * k))

open scoped Matrix Matrix.Norms.Operator unitInterval Topology in
set_option maxHeartbeats 1600000 in

/-- KA III.1.19: the corrected right-cokernel class is independent of shift and stable homotopy. -/
theorem shiftedCokernelIndex_eq_of_stablyHomotopic (p q : LaurentMatrixLoop A)
    (k l : ℕ) (hk : (p.shift (k : ℤ)).IsPolynomial)
    (hl : (q.shift (l : ℤ)).IsPolynomial) (h : p.StablyHomotopic q) :
    shiftedCokernelIndex p k hk = shiftedCokernelIndex q l hl := by
  /- Stage 1: increasing the shift by j adds a free right module of rank n*j
  to the actual shifted cokernel and the same class to its free correction.
  Compare admissible shifts at a common larger shift, retaining the quotient.
  Stage 2: identity-loop stabilization preserves the corrected index. At
  shift zero its multiplier is identity and its cokernel is zero; shift
  independence gives zero corrected class at every admissible shift.
  Stage 3: choose one shift and degree bound d from the finite exponent
  set of the stabilized homotopy. Fourier uniqueness identifies its endpoint
  polynomials with the prescribed stabilized loops and matrix-size transport.
  Regard the family as a polynomial with coefficients in C(I,Matrix_n(A)).
  Its circle values are units by continuous pointwise inversion. Finite-support
  Wiener inversion gives one bilateral inverse over that algebra. Bounded
  time evaluation yields g(t), both ordered inverse equations, and continuous
  inverse-coefficient functions. On the original positive right module set
  T(t)=M_f(t), S(t)=P_+M_g(t)i and E(t)=I-T(t)S(t). The exact defect vanishes
  above the first d coefficient vectors. Include and extract that window by
  J and C, flatten its coefficient-first order, and read CE(t)J on unit columns
  to obtain the finite idempotent matrix P(t), acting from the left.
  Stage 4: each entry of P(t) depends on finitely many coefficients of f(t)
  and g(t), so this is one continuous finite projector family. The same defect
  splitting identifies its image at each time with that time's actual quotient.
  Apply the noncommutative idempotent path theorem to P: its endpoint conjugacy
  identifies the two right image classes. Retain the identical free correction,
  then undo common shifts and stabilizations. The argument uses neither flatness
  nor base change for an infinite Wiener quotient, and never commutes general
  coefficients or substitutes independently chosen endpoint projectors. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let matrixCompleteSpace (n : ℕ) : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
      inferInstanceAs (CompleteSpace (Fin n → Fin n → A))
    let rightColumnFinite (n : ℕ) : Module.Finite Aᵐᵒᵖ (Fin n → A) :=
      (finiteFreeRightModule_finite_projective A n).1
    let rightColumnProjective (n : ℕ) : Module.Projective Aᵐᵒᵖ (Fin n → A) :=
      (finiteFreeRightModule_finite_projective A n).2
    have familyClass_eq {n : ℕ}
        (f : I → LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (hf : ∀ t k, k < 0 → (f t).coeff k = 0)
        (d : ℕ) (hd : ∀ t k, (d : ℤ) < k → (f t).coeff k = 0)
        (g : I → WienerLoop (Matrix (Fin n) (Fin n) A))
        (hgf : ∀ t, g t * laurentPolynomialWiener (f t) = 1)
        (hfg : ∀ t, laurentPolynomialWiener (f t) * g t = 1)
        (hcF : ∀ k, Continuous (fun t ↦ (f t).coeff k))
        (hcG : ∀ k, Continuous (fun t ↦ g t k)) :
        let := RightWiener.polynomialCokernel_finite (f 0) (hf 0) (g 0) (hgf 0) (hfg 0)
        let := RightWiener.polynomialCokernel_projective (f 0) (hf 0) (g 0) (hgf 0) (hfg 0)
        let := RightWiener.polynomialCokernel_finite (f 1) (hf 1) (g 1) (hgf 1) (hfg 1)
        let := RightWiener.polynomialCokernel_projective (f 1) (hf 1) (g 1) (hgf 1) (hfg 1)
        projectiveModuleKZeroClass A (RightWiener.PolynomialCokernel (f 0) (hf 0)) =
          projectiveModuleKZeroClass A (RightWiener.PolynomialCokernel (f 1) (hf 1)) := by
      classical
      let T (t : I) : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
        RightWiener.polynomialMultiplier (f t) (hf t)
      let S (t : I) : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
        RightWiener.toeplitz (g t)
      let E (t : I) : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
        LinearMap.id - (T t).comp (S t)
      have hST (t : I) (x : PositiveWienerModule A n) : S t (T t x) = x :=
        DFunLike.congr_fun (RightWiener.polynomialMultiplier_leftInverse
          (f t) (hf t) (g t) (hgf t)) x
      have hET (t : I) (x : PositiveWienerModule A n) : E t (T t x) = 0 := by
        change T t x - T t (S t (T t x)) = 0
        rw [hST, sub_self]
      have hEE (t : I) (x : PositiveWienerModule A n) : E t (E t x) = E t x := by
        change E t (x - T t (S t x)) = E t x
        rw [map_sub, hET, sub_zero]
      have hsingle (b : WienerLoop (Matrix (Fin n) (Fin n) A))
          (j k : ℕ) (v : Fin n → A) :
          RightWiener.toeplitz b (lp.single 1 j v) k = (b ((k : ℤ) - j)).mulVec v := by
        change (∑' l : ℕ, (b ((k : ℤ) - l)).mulVec
          ((lp.single 1 j v : PositiveWienerModule A n) l)) = _
        simp only [lp.coeFn_single, Pi.single_apply, apply_ite, Matrix.mulVec_zero]
        simp
      -- The exact defect is supported in the same first d coefficient vectors.
      have htail (t : I) (k : ℕ) (hk : d ≤ k) (x : PositiveWienerModule A n) :
          E t x k = 0 := by
        let f := f t
        let hf : ∀ k, k < 0 → f.coeff k = 0 := hf t
        let hd : ∀ k, (d : ℤ) < k → f.coeff k = 0 := hd t
        let g := g t
        have hfg : laurentPolynomialWiener f * g = 1 := hfg t
        let T : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
          RightWiener.polynomialMultiplier f hf
        let S : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
          RightWiener.toeplitz g
        let E : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
          LinearMap.id - T.comp S
        -- Calculate the opposite product on one coefficient vector, in its original order.
        have hproduct (p : ℤ) (v : Fin n → A) :
            ((laurentPolynomialWiener f * g) p).mulVec v =
              ∑' a : ℤ, (f.coeff a).mulVec ((g (p - a)).mulVec v) := by
          change ((∑' a : ℤ, laurentPolynomialWiener f a * g (p - a))).mulVec v = _
          simp only [laurentPolynomialWiener_coeff]
          have hmat : (∑' a : ℤ, f.coeff a * g (p - a)) =
              ∑ a ∈ f.coeff.support, f.coeff a * g (p - a) := by
            apply tsum_eq_sum
            intro a ha
            simp [Finsupp.notMem_support_iff.mp ha]
          have hvec : (∑' a : ℤ, (f.coeff a).mulVec ((g (p - a)).mulVec v)) =
              ∑ a ∈ f.coeff.support, (f.coeff a).mulVec ((g (p - a)).mulVec v) := by
            apply tsum_eq_sum
            intro a ha
            simp [Finsupp.notMem_support_iff.mp ha]
          rw [hmat, hvec, Matrix.sum_mulVec]
          apply Finset.sum_congr rfl
          intro a ha
          exact (Matrix.mulVec_mulVec v (f.coeff a) (g (p - a))).symm
        have htail_single (k : ℕ) (hk : d ≤ k) (j : ℕ) (v : Fin n → A) :
            T (S (lp.single 1 j v)) k = (lp.single 1 j v : PositiveWienerModule A n) k := by
          have hinj : Function.Injective (fun a : ℕ ↦ (a : ℤ)) := by
            intro a b h
            dsimp at h
            omega
          have hs : Function.support
              (fun a : ℤ ↦ (f.coeff a).mulVec ((g ((k : ℤ) - j - a)).mulVec v)) ⊆
              Set.range (fun a : ℕ ↦ (a : ℤ)) := by
            intro a ha
            have ha0 : 0 ≤ a := by
              by_contra h
              simp [Function.mem_support, hf a (by omega)] at ha
            exact ⟨a.toNat, Int.toNat_of_nonneg ha0⟩
          calc
            T (S (lp.single 1 j v)) k =
                ∑ a ∈ Finset.range (k + 1),
                  (f.coeff (a : ℤ)).mulVec ((g ((k : ℤ) - j - a)).mulVec v) := by
              rw [RightWiener.polynomialMultiplier_coeff]
              apply Finset.sum_congr rfl
              intro a ha
              simp only [Finset.mem_range] at ha
              rw [hsingle]
              rw [show ((k - a : ℕ) : ℤ) - j = (k : ℤ) - j - a by omega]
            _ = ∑' a : ℕ, (f.coeff (a : ℤ)).mulVec
                ((g ((k : ℤ) - j - a)).mulVec v) := by
              symm
              apply tsum_eq_sum
              intro a ha
              rw [hd _ (by simp only [Finset.mem_range] at ha; omega), Matrix.zero_mulVec]
            _ = ∑' a : ℤ, (f.coeff a).mulVec ((g ((k : ℤ) - j - a)).mulVec v) :=
              hinj.tsum_eq hs
            _ = ((laurentPolynomialWiener f * g) ((k : ℤ) - j)).mulVec v :=
              (hproduct ((k : ℤ) - j) v).symm
            _ = (lp.single 1 j v : PositiveWienerModule A n) k := by
              rw [hfg]
              change (lp.single (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A)
                1 (0 : ℤ) 1 ((k : ℤ) - j)).mulVec v = _
              by_cases hkj : k = j
              · subst k
                simp
              · have hdiff : (k : ℤ) - j ≠ 0 := by omega
                simp [hdiff, hkj]
        let V : PositiveWienerModule A n →L[Aᵐᵒᵖ] (Fin n → A) :=
          lp.evalCLM Aᵐᵒᵖ (fun _ : ℕ ↦ Fin n → A) 1 k
        have hcomp : V.comp ((RightWiener.toeplitzContinuous (A := A) (n := n)
            (laurentPolynomialWiener f)).comp
              (RightWiener.toeplitzContinuous (A := A) (n := n) g)) =
            V := by
          apply lp.ext_continuousLinearMap (by simp)
          intro j
          ext v : 1
          exact htail_single k hk j v
        have heq : T (S x) k = x k := DFunLike.congr_fun hcomp x
        change x k - T (S x) k = 0
        exact sub_eq_zero.mpr heq.symm
      let C : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] (Fin d → Fin n → A) :=
        LinearMap.pi fun j : Fin d ↦ lp.evalₗ (fun _ : ℕ ↦ Fin n → A) 1 (j : ℕ)
      let J := RightWiener.lowPolynomialEmbedding A n d
      have hJC (t : I) (x : PositiveWienerModule A n) : J (C (E t x)) = E t x := by
        apply lp.ext
        funext k
        simp only [J, RightWiener.lowPolynomialEmbedding, LinearMap.sum_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, lp.lsingle_apply]
        change (∑ j : Fin d,
          lp.single (E := fun _ : ℕ ↦ Fin n → A) 1 (j : ℕ) (E t x j)) k = E t x k
        rw [lp.coeFn_sum, Finset.sum_apply]
        by_cases hkd : k < d
        · rw [Finset.sum_eq_single (⟨k, hkd⟩ : Fin d)]
          · simp
          · intro j hj hne
            apply lp.single_apply_ne
            intro heq
            exact hne (Fin.ext heq.symm)
          · simp
        · rw [htail t k (by omega) x]
          apply Finset.sum_eq_zero
          intro j hj
          apply lp.single_apply_ne
          have hjd := j.isLt
          omega
      -- Flatten only the finite coefficient window, preserving its stated order.
      let e : (Fin d → Fin n → A) ≃ₗ[Aᵐᵒᵖ] (Fin (d * n) → A) :=
        { toFun v i := v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
          invFun v j i := v (finProdFinEquiv (j, i))
          left_inv v := by funext j i; simp
          right_inv v := by
            funext i
            change v (finProdFinEquiv (finProdFinEquiv.symm i)) = v i
            rw [Equiv.apply_symm_apply]
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      let L (t : I) : (Fin (d * n) → A) →ₗ[Aᵐᵒᵖ] (Fin (d * n) → A) :=
        e.toLinearMap.comp (C.comp ((E t).comp (J.comp e.symm.toLinearMap)))
      -- Read right-linear maps on the original unit columns; coefficients never commute.
      let P (t : I) : Matrix (Fin (d * n)) (Fin (d * n)) A :=
        fun i j ↦ L t (Pi.single j 1) i
      have hPL (t : I) (v : Fin (d * n) → A) : (P t).mulVec v = L t v := by
        have hcol : v = ∑ j, MulOpposite.op (v j) • Pi.single j (1 : A) := by
          ext i
          simp [Pi.smul_apply, Pi.single_apply]
        ext i
        change (∑ j, L t (Pi.single j 1) i * v j) = L t v i
        conv_rhs => rw [hcol]
        simp [map_sum]
      have hL (t : I) (v : Fin (d * n) → A) :
          L t v = e (C (E t (J (e.symm v)))) := rfl
      have hP (t : I) : P t * P t = P t := by
        have hLL (v : Fin (d * n) → A) : L t (L t v) = L t v := by
          change e (C (E t (J (e.symm (e (C (E t (J (e.symm v))))))))) =
            e (C (E t (J (e.symm v))))
          rw [e.symm_apply_apply, hJC, hEE]
        have hv (v : Fin (d * n) → A) : (P t * P t).mulVec v = (P t).mulVec v := by
          rw [← Matrix.mulVec_mulVec, hPL, hPL]
          exact hLL v
        ext i j
        have hvj := congrArg (fun v : Fin (d * n) → A ↦ v i) (hv (Pi.single j 1))
        simpa using hvj
      -- Every finite projector entry depends on only finitely many original coefficients.
      have hSJ (t : I) (v : Fin d → Fin n → A) (k : ℕ) :
          S t (J v) k = ∑ j : Fin d, (g t ((k : ℤ) - j)).mulVec (v j) := by
        simp only [J, RightWiener.lowPolynomialEmbedding, LinearMap.sum_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, lp.lsingle_apply, map_sum, lp.coeFn_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        exact hsingle (g t) j k (v j)
      have hcP : Continuous P := by
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        change Continuous (fun t ↦
          E t (J (e.symm (Pi.single j 1))) ((finProdFinEquiv.symm i).1 : ℕ)
            (finProdFinEquiv.symm i).2)
        change Continuous (fun t ↦
          J (e.symm (Pi.single j 1)) ((finProdFinEquiv.symm i).1 : ℕ)
            (finProdFinEquiv.symm i).2 -
          T t (S t (J (e.symm (Pi.single j 1)))) ((finProdFinEquiv.symm i).1 : ℕ)
            (finProdFinEquiv.symm i).2)
        simp only [T, RightWiener.polynomialMultiplier_coeff, hSJ, Matrix.mulVec, dotProduct,
          Finset.sum_apply]
        fun_prop
      -- Each actual quotient is the image of this same finite projector, not a chosen model.
      let p (t : I) : IdempotentMatrix A := ⟨d * n, P t, hP t⟩
      have hquot (t : I) (x : PositiveWienerModule A n) :
          RightWiener.polynomialCokernelMk (f t) (hf t) (E t x) =
            RightWiener.polynomialCokernelMk (f t) (hf t) x := by
        let Q := RightWiener.polynomialCokernelMk (f t) (hf t)
        have hz : Q (T t (S t x)) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          exact ⟨S t x, rfl⟩
        change Q (x - T t (S t x)) = Q x
        rw [map_sub, hz, sub_zero]
      have hmodel (t : I):
          Nonempty ((p t).image ≃ₗ[Aᵐᵒᵖ] RightWiener.PolynomialCokernel (f t) (hf t)) := by
        let Q := RightWiener.polynomialCokernelMk (f t) (hf t)
        let R : (Fin (d * n) → A) →ₗ[Aᵐᵒᵖ] RightWiener.PolynomialCokernel (f t) (hf t) :=
          Q.comp (J.comp e.symm.toLinearMap)
        let K : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] (Fin (d * n) → A) :=
          e.toLinearMap.comp (C.comp (E t))
        have hker : LinearMap.range (T t) ≤ LinearMap.ker K := by
          rintro x ⟨y, rfl⟩
          change e (C (E t (T t y))) = 0
          rw [hET, map_zero, map_zero]
        let s : RightWiener.PolynomialCokernel (f t) (hf t) →ₗ[Aᵐᵒᵖ] (Fin (d * n) → A) :=
          (LinearMap.range (T t)).liftQ K hker
        have hsR (v : Fin (d * n) → A) : s (R v) = (P t).mulVec v := by
          exact (hPL t v).symm
        have hRs (q : RightWiener.PolynomialCokernel (f t) (hf t)) : R (s q) = q := by
          obtain ⟨x, rfl⟩ := (LinearMap.range (T t)).mkQ_surjective q
          change Q (J (e.symm (e (C (E t x))))) = Q x
          rw [e.symm_apply_apply, hJC]
          exact hquot t x
        have hfix (v : (p t).image) : (P t).mulVec v.val = v.val := by
          obtain ⟨w, hw⟩ := v.property
          rw [← hw]
          change (P t).mulVec ((P t).mulVec w) = (P t).mulVec w
          rw [Matrix.mulVec_mulVec, hP]
        let R' := R.comp (p t).image.subtype
        refine ⟨LinearEquiv.ofBijective R' ⟨?_, ?_⟩⟩
        · intro v w hvw
          apply Subtype.ext
          have hvw' := congrArg s hvw
          change s (R v.val) = s (R w.val) at hvw'
          simpa only [hsR, hfix] using hvw'
        · intro q
          have hmem : s q ∈ (p t).image := by
            refine ⟨s q, ?_⟩
            change (P t).mulVec (s q) = s q
            rw [← hsR, hRs]
          exact ⟨⟨s q, hmem⟩, hRs q⟩
      -- Connectedness compares the endpoints of this original finite projector family.
      let cp : C(I, Matrix (Fin (d * n)) (Fin (d * n)) A) := ⟨P, hcP⟩
      obtain ⟨u, hu⟩ := exists_unit_conjugating_idempotent_path cp hP
      let U : Matrix (Fin (d * n)) (Fin (d * n)) A := u
      let V : Matrix (Fin (d * n)) (Fin (d * n)) A := ↑(u⁻¹)
      have hUV : U * V = 1 := Units.mul_inv u
      have hVU : V * U = 1 := Units.inv_mul u
      change P 1 = U * P 0 * V at hu
      have hinter : P 1 * U = U * P 0 := by
        rw [hu]
        simp only [mul_assoc, hVU, mul_one]
      have hsame : kZeroClass A (p 0) = kZeroClass A (p 1) := by
        apply kZeroClass_eq_of_isEquivalent
        refine ⟨P 0 * V, U * P 0, ?_, ?_, ?_, ?_⟩
        · change P 0 * V * (U * P 0) = P 0
          calc
            _ = P 0 * (V * U) * P 0 := by noncomm_ring
            _ = P 0 := by rw [hVU, mul_one, hP]
        · change U * P 0 * (P 0 * V) = P 1
          calc
            _ = U * (P 0 * P 0) * V := by noncomm_ring
            _ = P 1 := by rw [hP]; exact hu.symm
        · change P 0 * (P 0 * V) = P 0 * V
          rw [← mul_assoc, hP]
        · change P 1 * (U * P 0) = U * P 0
          rw [← mul_assoc, hinter, mul_assoc, hP]
      have hclass (t : I) :
          let := RightWiener.polynomialCokernel_finite (f t) (hf t) (g t) (hgf t) (hfg t)
          let := RightWiener.polynomialCokernel_projective (f t) (hf t) (g t) (hgf t) (hfg t)
          projectiveModuleKZeroClass A (RightWiener.PolynomialCokernel (f t) (hf t)) =
            kZeroClass A (p t) := by
        let := RightWiener.polynomialCokernel_finite (f t) (hf t) (g t) (hgf t) (hfg t)
        let := RightWiener.polynomialCokernel_projective (f t) (hf t) (g t) (hgf t) (hfg t)
        let := (p t).finite_image
        let := (p t).projective_image
        obtain ⟨eqv⟩ := hmodel t
        exact (projectiveModuleKZeroClass_eq_of_linearEquiv eqv).symm.trans
          (projectiveModuleKZeroClass_image (p t))
      exact (hclass 0).trans (hsame.trans (hclass 1).symm)
    have uniformInverse {n : ℕ}
        (r : LaurentPolynomial C(I, Matrix (Fin n) (Fin n) A))
        (f : I → LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (hcoeff : ∀ t k, (f t).coeff k = r.coeff k t)
        (hi : ∀ t z, IsUnit (laurentPolynomialCircleValue (f t) z)) :
        ∃ g : I → WienerLoop (Matrix (Fin n) (Fin n) A),
          (∀ t, g t * laurentPolynomialWiener (f t) = 1) ∧
          (∀ t, laurentPolynomialWiener (f t) * g t = 1) ∧
          ∀ k, Continuous (fun t ↦ g t k) := by
      classical
      have hcoeffEq (t : I) : (f t).coeff =
          r.coeff.mapRange (fun a ↦ a t) rfl := by
        apply Finsupp.ext
        intro k
        exact hcoeff t k
      have heval (t : I) (z : Circle) :
          laurentPolynomialCircleValue (f t) z =
            laurentPolynomialCircleValue (A := C(I, Matrix (Fin n) (Fin n) A)) r z t := by
        rw [laurentPolynomialCircleValue, hcoeffEq]
        rw [Finsupp.sum_mapRange_index (fun k ↦ smul_zero ((z : ℂ) ^ k))]
        simp only [laurentPolynomialCircleValue, Finsupp.sum, ContinuousMap.sum_apply,
          ContinuousMap.smul_apply]
      have hfinite : (Function.support (fun k : ℤ ↦ laurentPolynomialWiener r k)).Finite := by
        simpa only [Function.HasFiniteSupport, laurentPolynomialWiener_coeff] using
          r.coeff.hasFiniteSupport
      have hunit : IsUnit (laurentPolynomialWiener r) :=
        WienerLoop.isUnit_of_finiteSupport _ hfinite fun z ↦ by
          rw [laurentPolynomialWiener_eval]
          let F : C(I, Matrix (Fin n) (Fin n) A) :=
            laurentPolynomialCircleValue (A := C(I, Matrix (Fin n) (Fin n) A)) r z
          have hF (t : I) : IsUnit (F t) := by
            change IsUnit (laurentPolynomialCircleValue
              (A := C(I, Matrix (Fin n) (Fin n) A)) r z t)
            rw [← heval]
            exact hi t z
          let V : C(I, Matrix (Fin n) (Fin n) A) :=
            ⟨fun t ↦ Ring.inverse (F t), by
              apply continuous_iff_continuousAt.mpr
              intro t
              have hcont := NormedRing.inverse_continuousAt (hF t).unit
              simp only [IsUnit.unit_spec] at hcont
              exact hcont.comp F.continuous.continuousAt⟩
          refine ⟨⟨F, V, ?_, ?_⟩, rfl⟩
          · apply ContinuousMap.ext
            intro t
            exact Ring.mul_inverse_cancel (F t) (hF t)
          · apply ContinuousMap.ext
            intro t
            exact Ring.inverse_mul_cancel (F t) (hF t)
      let b : WienerLoop C(I, Matrix (Fin n) (Fin n) A) := ↑(hunit.unit⁻¹)
      have hbr : b * laurentPolynomialWiener r = 1 := by
        simpa only [IsUnit.unit_spec] using Units.inv_mul hunit.unit
      have hrb : laurentPolynomialWiener r * b = 1 := by
        simpa only [IsUnit.unit_spec] using Units.mul_inv hunit.unit
      -- Bounded coefficient evaluation retains absolute summability, including zero size.
      have hmem (t : I) : Memℓp (fun k : ℤ ↦ b k t) 1 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_one, Real.rpow_one]
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (fun k ↦ ContinuousMap.norm_coe_le_norm (b k) t)
        simpa only [ENNReal.toReal_one, Real.rpow_one] using b.2.summable (by simp)
      let g (t : I) : WienerLoop (Matrix (Fin n) (Fin n) A) := ⟨fun k ↦ b k t, hmem t⟩
      have hright (k : ℤ) : (b * laurentPolynomialWiener r) k =
          ∑ a ∈ r.coeff.support, b (k - a) * r.coeff a := by
        change (∑' a : ℤ, b a * laurentPolynomialWiener r (k - a)) = _
        rw [← (Equiv.subLeft k).tsum_eq
          (fun a : ℤ ↦ b a * laurentPolynomialWiener r (k - a))]
        simp only [Equiv.subLeft_apply, sub_sub_cancel, laurentPolynomialWiener_coeff]
        apply tsum_eq_sum
        intro a ha
        rw [Finsupp.notMem_support_iff.mp ha, mul_zero]
      have hleft (k : ℤ) : (laurentPolynomialWiener r * b) k =
          ∑ a ∈ r.coeff.support, r.coeff a * b (k - a) := by
        change (∑' a : ℤ, laurentPolynomialWiener r a * b (k - a)) = _
        simp only [laurentPolynomialWiener_coeff]
        apply tsum_eq_sum
        intro a ha
        rw [Finsupp.notMem_support_iff.mp ha, zero_mul]
      refine ⟨g, ?_, ?_, ?_⟩
      · intro t
        apply lp.ext
        funext k
        change (∑' a : ℤ, g t a * laurentPolynomialWiener (f t) (k - a)) =
          (lp.single (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 0 1) k
        rw [← (Equiv.subLeft k).tsum_eq
          (fun a : ℤ ↦ g t a * laurentPolynomialWiener (f t) (k - a))]
        simp only [Equiv.subLeft_apply, sub_sub_cancel, laurentPolynomialWiener_coeff, hcoeff]
        calc
          (∑' a : ℤ, b (k - a) t * r.coeff a t) =
              ∑ a ∈ r.coeff.support, b (k - a) t * r.coeff a t := by
            apply tsum_eq_sum
            intro a ha
            rw [Finsupp.notMem_support_iff.mp ha]
            simp
          _ = (b * laurentPolynomialWiener r) k t := by
            rw [hright]
            simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
          _ = (lp.single (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 0 1) k := by
            rw [hbr]
            change (lp.single (E := fun _ : ℤ ↦ C(I, Matrix (Fin n) (Fin n) A))
              1 (0 : ℤ) 1 k) t = _
            by_cases hk : k = 0 <;> simp [hk]
      · intro t
        apply lp.ext
        funext k
        change (∑' a : ℤ, laurentPolynomialWiener (f t) a * g t (k - a)) =
          (lp.single (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 0 1) k
        simp only [laurentPolynomialWiener_coeff, hcoeff]
        calc
          (∑' a : ℤ, r.coeff a t * b (k - a) t) =
              ∑ a ∈ r.coeff.support, r.coeff a t * b (k - a) t := by
            apply tsum_eq_sum
            intro a ha
            rw [Finsupp.notMem_support_iff.mp ha]
            simp
          _ = (laurentPolynomialWiener r * b) k t := by
            rw [hleft]
            simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
          _ = (lp.single (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A) 1 0 1) k := by
            rw [hrb]
            change (lp.single (E := fun _ : ℤ ↦ C(I, Matrix (Fin n) (Fin n) A))
              1 (0 : ℤ) 1 k) t = _
            by_cases hk : k = 0 <;> simp [hk]
      · intro k
        exact (b k).continuous
    have polynomialBlock
        {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A))
        (b : LaurentPolynomial (Matrix (Fin (n + m)) (Fin (n + m)) A))
        (hf : ∀ k, k < 0 → f.coeff k = 0)
        (hg : ∀ k, k < 0 → g.coeff k = 0)
        (hb : ∀ k, k < 0 → b.coeff k = 0)
        (hcoeff : ∀ k, b.coeff k = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (f.coeff k) 0 0 (g.coeff k))) :
        Nonempty (RightWiener.PolynomialCokernel b hb ≃ₗ[Aᵐᵒᵖ]
          RightWiener.PolynomialCokernel f hf × RightWiener.PolynomialCokernel g hg) := by
      classical
      let c : (Fin (n + m) → A) ≃ₗ[Aᵐᵒᵖ] (Fin n → A) × (Fin m → A) :=
        (LinearEquiv.piCongrLeft' Aᵐᵒᵖ (fun _ : Fin (n + m) ↦ A)
          finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ Aᵐᵒᵖ A)
      have hc (v : Fin (n + m) → A) :
          c v = (v ∘ Fin.castAdd m, v ∘ Fin.natAdd n) := rfl
      have hnorm₁ (v : Fin (n + m) → A) : ‖(c v).1‖ ≤ ‖v‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
        intro i
        exact norm_le_pi_norm v (Fin.castAdd m i)
      have hnorm₂ (v : Fin (n + m) → A) : ‖(c v).2‖ ≤ ‖v‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
        intro i
        exact norm_le_pi_norm v (Fin.natAdd n i)
      have hnorm_inv (v : (Fin n → A) × (Fin m → A)) :
          ‖c.symm v‖ ≤ ‖v.1‖ + ‖v.2‖ := by
        apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        intro i
        obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
        cases a with
        | inl a =>
          have heq : c.symm v (Fin.castAdd m a) = v.1 a :=
            congrArg (fun w : (Fin n → A) × (Fin m → A) ↦ w.1 a)
              (c.apply_symm_apply v)
          change ‖c.symm v (Fin.castAdd m a)‖ ≤ _
          rw [heq]
          exact (norm_le_pi_norm v.1 a).trans (le_add_of_nonneg_right (norm_nonneg _))
        | inr a =>
          have heq : c.symm v (Fin.natAdd n a) = v.2 a :=
            congrArg (fun w : (Fin n → A) × (Fin m → A) ↦ w.2 a)
              (c.apply_symm_apply v)
          change ‖c.symm v (Fin.natAdd n a)‖ ≤ _
          rw [heq]
          exact (norm_le_pi_norm v.2 a).trans (le_add_of_nonneg_left (norm_nonneg _))
      have hmem₁ (x : PositiveWienerModule A (n + m)) :
          Memℓp (fun k : ℕ ↦ (c (x k)).1) 1 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_one, Real.rpow_one]
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hnorm₁ (x k))
        simpa only [ENNReal.toReal_one, Real.rpow_one] using x.2.summable (by simp)
      have hmem₂ (x : PositiveWienerModule A (n + m)) :
          Memℓp (fun k : ℕ ↦ (c (x k)).2) 1 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_one, Real.rpow_one]
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hnorm₂ (x k))
        simpa only [ENNReal.toReal_one, Real.rpow_one] using x.2.summable (by simp)
      have hmem_inv (x : PositiveWienerModule A n × PositiveWienerModule A m) :
          Memℓp (fun k : ℕ ↦ c.symm (x.1 k, x.2 k)) 1 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_one, Real.rpow_one]
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (fun k ↦ hnorm_inv (x.1 k, x.2 k))
        have hx₁ : Summable (fun k : ℕ ↦ ‖x.1 k‖) := by simpa using x.1.2.summable
        have hx₂ : Summable (fun k : ℕ ↦ ‖x.2 k‖) := by simpa using x.2.2.summable
        exact hx₁.add hx₂
      let e : PositiveWienerModule A (n + m) ≃ₗ[Aᵐᵒᵖ]
          PositiveWienerModule A n × PositiveWienerModule A m :=
        { toFun x := (⟨fun k ↦ (c (x k)).1, hmem₁ x⟩, ⟨fun k ↦ (c (x k)).2, hmem₂ x⟩)
          invFun x := ⟨fun k ↦ c.symm (x.1 k, x.2 k), hmem_inv x⟩
          left_inv x := by
            apply lp.ext
            funext k
            exact c.symm_apply_apply (x k)
          right_inv x := by
            apply Prod.ext <;> apply lp.ext <;> funext k
            · exact congrArg Prod.fst (c.apply_symm_apply (x.1 k, x.2 k))
            · exact congrArg Prod.snd (c.apply_symm_apply (x.1 k, x.2 k))
          map_add' x y := by
            apply Prod.ext <;> apply lp.ext <;> funext k
            · exact congrArg Prod.fst (c.map_add (x k) (y k))
            · exact congrArg Prod.snd (c.map_add (x k) (y k))
          map_smul' a x := by
            apply Prod.ext <;> apply lp.ext <;> funext k
            · exact congrArg Prod.fst (c.map_smul a (x k))
            · exact congrArg Prod.snd (c.map_smul a (x k)) }
      have hmatrix (a : Matrix (Fin n) (Fin n) A) (b : Matrix (Fin m) (Fin m) A)
          (v : Fin (n + m) → A) :
          c ((Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks a 0 0 b)).mulVec v) =
            (a.mulVec (c v).1, b.mulVec (c v).2) := by
        change c ((Matrix.fromBlocks a 0 0 b).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ v) = _
        rw [Matrix.submatrix_mulVec_equiv _ _ _ finSumFinEquiv.symm,
          Matrix.fromBlocks_mulVec]
        apply Prod.ext <;> ext i <;> simp [hc, Function.comp_def]
      have hinter (x : PositiveWienerModule A (n + m)) :
          e (RightWiener.polynomialMultiplier b hb x) =
            (RightWiener.polynomialMultiplier f hf (e x).1,
              RightWiener.polynomialMultiplier g hg (e x).2) := by
        have hk (k : ℕ) : c (RightWiener.polynomialMultiplier b hb x k) =
            (RightWiener.polynomialMultiplier f hf (e x).1 k,
              RightWiener.polynomialMultiplier g hg (e x).2 k) := by
          rw [RightWiener.polynomialMultiplier_coeff, map_sum]
          simp_rw [hcoeff, hmatrix]
          apply Prod.ext <;>
            simp only [Prod.fst_sum, Prod.snd_sum, RightWiener.polynomialMultiplier_coeff]
          · rfl
          · rfl
        apply Prod.ext <;> apply lp.ext <;> funext k
        · exact congrArg Prod.fst (hk k)
        · exact congrArg Prod.snd (hk k)
      obtain ⟨q, _⟩ := exists_quotientRange_prod_equiv_of_intertwine e
        (RightWiener.polynomialMultiplier b hb)
        (RightWiener.polynomialMultiplier f hf)
        (RightWiener.polynomialMultiplier g hg) hinter
      exact ⟨q⟩
    have shiftIndependent (p : LaurentMatrixLoop A) (k l : ℕ)
        (hk : (p.shift (k : ℤ)).IsPolynomial)
        (hl : (p.shift (l : ℤ)).IsPolynomial) :
        shiftedCokernelIndex p k hk = shiftedCokernelIndex p l hl := by
      classical
      have hfree (m n : ℕ) :
          kZeroClass A (IdempotentMatrix.identity A (m + n)) =
            kZeroClass A (IdempotentMatrix.identity A m) +
              kZeroClass A (IdempotentMatrix.identity A n) := by
        have hb : (IdempotentMatrix.identity A m).blockSum
            (IdempotentMatrix.identity A n) = IdempotentMatrix.identity A (m + n) := by
          dsimp only [IdempotentMatrix.blockSum, IdempotentMatrix.identity]
          congr 1
          simp [IdempotentMatrix.blockMatrix, Matrix.fromBlocks_one]
        rw [← hb, kZeroClass_blockSum]
      have hstep (k j : ℕ) (hk : (p.shift (k : ℤ)).IsPolynomial) :
          ∃ hkj : (p.shift ((k + j : ℕ) : ℤ)).IsPolynomial,
            shiftedCokernelIndex p (k + j) hkj = shiftedCokernelIndex p k hk := by
        obtain ⟨hkj, ⟨e⟩⟩ := p.nonempty_rightShiftedCokernel_add_equiv k j hk
        refine ⟨hkj, ?_⟩
        let := p.rightShiftedCokernel_finite k hk
        let := p.rightShiftedCokernel_projective k hk
        let := p.rightShiftedCokernel_finite (k + j) hkj
        let := p.rightShiftedCokernel_projective (k + j) hkj
        have hc := projectiveModuleKZeroClass_eq_of_linearEquiv e
        dsimp only [AtiyahSinger.RightKTheory.shiftedCokernelIndex]
        rw [hc, projectiveModuleKZeroClass_prod, projectiveModuleKZeroClass_free,
          Nat.mul_add, hfree]
        abel
      obtain ⟨hkl, heq₁⟩ := hstep k l hk
      obtain ⟨hlk, heq₂⟩ := hstep l k hl
      have heq₂' : shiftedCokernelIndex p (k + l) hkl =
          shiftedCokernelIndex p l hl := by
        simpa only [Nat.add_comm l k] using heq₂
      exact heq₁.symm.trans heq₂'
    let blockLaurentPolynomial {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A)) :
        LaurentPolynomial (Matrix (Fin (n + m)) (Fin (n + m)) A) := by
      let L : Matrix (Fin n) (Fin n) A →ₗ[ℂ]
          Matrix (Fin (n + m)) (Fin (n + m)) A :=
        { toFun a := Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks a 0 0 (0 : Matrix (Fin m) (Fin m) A))
          map_add' a b := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
          map_smul' c a := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj] }
      let R : Matrix (Fin m) (Fin m) A →ₗ[ℂ]
          Matrix (Fin (n + m)) (Fin (n + m)) A :=
        { toFun a := Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) A) 0 0 a)
          map_add' a b := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
          map_smul' c a := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj] }
      exact AddMonoidAlgebra.map L.toAddMonoidHom f + AddMonoidAlgebra.map R.toAddMonoidHom g
    have blockLaurentPolynomial_coeff {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A)) (k : ℤ) :
        (blockLaurentPolynomial f g).coeff k =
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (f.coeff k) 0 0 (g.coeff k)) := by
      dsimp only [blockLaurentPolynomial]
      simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_map]
      ext i j
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
    have blockLaurentPolynomial_value {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A)) (z : Circle) :
        laurentPolynomialCircleValue (blockLaurentPolynomial f g) z =
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (laurentPolynomialCircleValue f z) 0 0
              (laurentPolynomialCircleValue g z)) := by
      classical
      have hmap {a b : ℕ} (L : Matrix (Fin a) (Fin a) A →ₗ[ℂ]
          Matrix (Fin b) (Fin b) A) (p : LaurentPolynomial (Matrix (Fin a) (Fin a) A)) :
          laurentPolynomialCircleValue (AddMonoidAlgebra.map L.toAddMonoidHom p) z =
            L (laurentPolynomialCircleValue p z) := by
        simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_map]
        rw [Finsupp.sum_mapRange_index]
        · rw [map_finsuppSum]
          apply Finsupp.sum_congr
          intro j b
          exact (L.map_smul ((z : ℂ) ^ j) (p.coeff j)).symm
        · intro j
          simp
      have hadd {a : ℕ} (p q : LaurentPolynomial (Matrix (Fin a) (Fin a) A)) :
          laurentPolynomialCircleValue (p + q) z =
            laurentPolynomialCircleValue p z + laurentPolynomialCircleValue q z := by
        simp [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
          Finsupp.sum_add_index, smul_add]
      dsimp only [blockLaurentPolynomial]
      rw [hadd, hmap, hmap]
      ext i j
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
    let blockLaurent (p q : LaurentMatrixLoop A) : LaurentMatrixLoop A :=
      { size := p.size + q.size
        polynomial := blockLaurentPolynomial p.polynomial q.polynomial
        normalized := by
          rw [blockLaurentPolynomial_value, p.normalized, q.normalized]
          simp [Matrix.fromBlocks_one]
        invertible z := by
          rw [blockLaurentPolynomial_value]
          have h := (matrixUnitBlockSum (p.invertible z).unit (q.invertible z).unit).isUnit
          change IsUnit (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks
              ((p.invertible z).unit : Matrix (Fin p.size) (Fin p.size) A) 0 0
              ((q.invertible z).unit : Matrix (Fin q.size) (Fin q.size) A))) at h
          simpa only [IsUnit.unit_spec] using h }
    have blockIndex (p q : LaurentMatrixLoop A) (k : ℕ)
        (hp : (p.shift (k : ℤ)).IsPolynomial) (hq : (q.shift (k : ℤ)).IsPolynomial) :
        ∃ hb : ((blockLaurent p q).shift (k : ℤ)).IsPolynomial,
          shiftedCokernelIndex (blockLaurent p q) k hb =
            shiftedCokernelIndex p k hp + shiftedCokernelIndex q k hq := by
      classical
      have hc (j : ℤ) : (((blockLaurent p q).shift (k : ℤ)).polynomial).coeff j =
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks ((p.shift (k : ℤ)).polynomial.coeff j) 0 0
              ((q.shift (k : ℤ)).polynomial.coeff j)) := by
        simp only [LaurentMatrixLoop.shift, LaurentPolynomial.T,
          AddMonoidAlgebra.coeff_single_mul_apply, one_mul, blockLaurent,
          blockLaurentPolynomial_coeff]
      have hb : ((blockLaurent p q).shift (k : ℤ)).IsPolynomial := by
        intro j hj
        rw [hc, hp j hj, hq j hj]
        simp
      refine ⟨hb, ?_⟩
      obtain ⟨e⟩ := polynomialBlock
        (p.shift (k : ℤ)).polynomial (q.shift (k : ℤ)).polynomial
        ((blockLaurent p q).shift (k : ℤ)).polynomial hp hq hb hc
      let := p.rightShiftedCokernel_finite k hp
      let := p.rightShiftedCokernel_projective k hp
      let := q.rightShiftedCokernel_finite k hq
      let := q.rightShiftedCokernel_projective k hq
      let := (blockLaurent p q).rightShiftedCokernel_finite k hb
      let := (blockLaurent p q).rightShiftedCokernel_projective k hb
      let e' : (blockLaurent p q).RightShiftedCokernel k hb ≃ₗ[Aᵐᵒᵖ]
          p.RightShiftedCokernel k hp × q.RightShiftedCokernel k hq := e
      have heq := projectiveModuleKZeroClass_eq_of_linearEquiv e'
      have hfree (m n : ℕ) :
          kZeroClass A (IdempotentMatrix.identity A (m + n)) =
            kZeroClass A (IdempotentMatrix.identity A m) +
              kZeroClass A (IdempotentMatrix.identity A n) := by
        have h : (IdempotentMatrix.identity A m).blockSum
            (IdempotentMatrix.identity A n) = IdempotentMatrix.identity A (m + n) := by
          dsimp only [IdempotentMatrix.blockSum, IdempotentMatrix.identity]
          congr 1
          simp [IdempotentMatrix.blockMatrix, Matrix.fromBlocks_one]
        rw [← h, kZeroClass_blockSum]
      dsimp only [AtiyahSinger.RightKTheory.shiftedCokernelIndex]
      rw [heq, projectiveModuleKZeroClass_prod]
      change _ - kZeroClass A (IdempotentMatrix.identity A ((p.size + q.size) * k)) = _
      rw [Nat.add_mul, hfree]
      abel
    let constantLaurent (n : ℕ) : LaurentMatrixLoop A :=
      LaurentMatrixLoop.affine (1 : Matrix (Fin n) (Fin n) A) 0
        (by simp) (by intro z; simp)
    have constantIndex (n k : ℕ)
        (hk : ((constantLaurent n).shift (k : ℤ)).IsPolynomial) :
        shiftedCokernelIndex (constantLaurent n) k hk = 0 := by
      classical
      let p := constantLaurent n
      let f := (p.shift (0 : ℤ)).polynomial
      have hf : f = LaurentPolynomial.C 1 := by
        change LaurentPolynomial.T 0 *
          (LaurentPolynomial.C 1 + LaurentPolynomial.C 0 * LaurentPolynomial.T 1) = _
        rw [LaurentPolynomial.T_zero, one_mul, map_zero, zero_mul, add_zero]
        rfl
      have hcoeff (j : ℤ) : f.coeff j = if 0 = j then 1 else 0 := by
        rw [hf, ← LaurentPolynomial.single_eq_C]
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      have hp : (p.shift (0 : ℤ)).IsPolynomial := by
        intro j hj
        change f.coeff j = 0
        rw [hcoeff, ite_eq_right (by omega)]
      have hT (x : PositiveWienerModule A n) : RightWiener.polynomialMultiplier f hp x = x := by
        apply lp.ext
        funext j
        rw [RightWiener.polynomialMultiplier_coeff]
        rw [Finset.sum_eq_single 0]
        · simp [hcoeff]
        · intro a ha hne
          simp only [hcoeff, show (0 : ℤ) ≠ (a : ℤ) by omega, ite_false, Matrix.zero_mulVec]
        · simp
      let := p.rightShiftedCokernel_finite 0 hp
      let := p.rightShiftedCokernel_projective 0 hp
      have hzero (q : RightWiener.PolynomialCokernel f hp) : q = 0 := by
        obtain ⟨x, rfl⟩ :=
          (LinearMap.range (RightWiener.polynomialMultiplier f hp)).mkQ_surjective q
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hT x⟩
      let e : RightWiener.PolynomialCokernel f hp ≃ₗ[Aᵐᵒᵖ] (Fin 0 → A) :=
        LinearEquiv.ofBijective 0 ⟨fun x y _ ↦ (hzero x).trans (hzero y).symm,
          fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
      let e' : p.RightShiftedCokernel 0 hp ≃ₗ[Aᵐᵒᵖ] (Fin 0 → A) := e
      have hclass := projectiveModuleKZeroClass_eq_of_linearEquiv e'
      have hbase : shiftedCokernelIndex p 0 hp = 0 := by
        dsimp only [AtiyahSinger.RightKTheory.shiftedCokernelIndex]
        rw [hclass, projectiveModuleKZeroClass_free]
        simp
      exact (shiftIndependent p k 0 hk hp).trans hbase
    have shiftValue {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
        (f : LaurentPolynomial B) (k : ℤ) (z : Circle) :
        laurentPolynomialCircleValue (LaurentPolynomial.T k * f) z =
          (z : ℂ) ^ k • laurentPolynomialCircleValue f z := by
      classical
      have hadd (a b : LaurentPolynomial B) :
          laurentPolynomialCircleValue (a + b) z =
            laurentPolynomialCircleValue a z + laurentPolynomialCircleValue b z := by
        simp [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
          Finsupp.sum_add_index, smul_add]
      have hterm (a : B) (j : ℤ) :
          laurentPolynomialCircleValue (LaurentPolynomial.C a * LaurentPolynomial.T j) z =
            (z : ℂ) ^ j • a := by
        rw [← LaurentPolynomial.single_eq_C_mul_T]
        simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_single,
          Finsupp.sum_single_index, smul_zero]
      refine f.induction_on' ?_ ?_
      · intro a b ha hb
        rw [mul_add, hadd, ha, hb, hadd, smul_add]
      · intro j a
        rw [← mul_assoc, LaurentPolynomial.T_mul, mul_assoc, ← LaurentPolynomial.T_add]
        rw [hterm, hterm, zpow_add₀ z.coe_ne_zero, mul_smul]
    let evalPolynomial {n : ℕ}
        (r : LaurentPolynomial C(I, Matrix (Fin n) (Fin n) A)) (t : I) :
        LaurentPolynomial (Matrix (Fin n) (Fin n) A) :=
      AddMonoidAlgebra.map
        { toFun a := a t
          map_zero' := rfl
          map_add' _ _ := rfl } r
    have evalPolynomial_coeff {n : ℕ}
        (r : LaurentPolynomial C(I, Matrix (Fin n) (Fin n) A)) (t : I) (j : ℤ) :
        (evalPolynomial r t).coeff j = r.coeff j t := by
      rfl
    have evalPolynomial_value {n : ℕ}
        (r : LaurentPolynomial C(I, Matrix (Fin n) (Fin n) A)) (t : I) (z : Circle) :
        laurentPolynomialCircleValue (evalPolynomial r t) z =
          laurentPolynomialCircleValue (A := C(I, Matrix (Fin n) (Fin n) A)) r z t := by
      rw [laurentPolynomialCircleValue]
      change (r.coeff.mapRange (fun a ↦ a t) rfl).sum (fun j a ↦ (z : ℂ) ^ j • a) = _
      rw [Finsupp.sum_mapRange_index (fun j ↦ smul_zero ((z : ℂ) ^ j))]
      simp only [laurentPolynomialCircleValue, Finsupp.sum, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply]
    have castClass {n m : ℕ} (h : n = m)
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A))
        (hf : ∀ j, j < 0 → f.coeff j = 0)
        (hg : ∀ j, j < 0 → g.coeff j = 0)
        [Module.Finite Aᵐᵒᵖ (RightWiener.PolynomialCokernel f hf)]
        [Module.Projective Aᵐᵒᵖ (RightWiener.PolynomialCokernel f hf)]
        [Module.Finite Aᵐᵒᵖ (RightWiener.PolynomialCokernel g hg)]
        [Module.Projective Aᵐᵒᵖ (RightWiener.PolynomialCokernel g hg)]
        (heq : g = cast (congrArg
          (fun d : ℕ ↦ LaurentPolynomial (Matrix (Fin d) (Fin d) A)) h) f) :
        projectiveModuleKZeroClass A (RightWiener.PolynomialCokernel g hg) =
          projectiveModuleKZeroClass A (RightWiener.PolynomialCokernel f hf) := by
      subst m
      simp only [cast_eq] at heq
      subst g
      rfl
    classical
    obtain ⟨a, b, hab, r, hr₀, hr₁, hrbase, hri⟩ := h
    dsimp only at hr₀ hr₁ hrbase hri
    -- Clear one common finite exponent set without changing either endpoint representative.
    let R : ℕ := r.coeff.support.sup (fun j : ℤ ↦ j.natAbs)
    let K : ℕ := k + (l + R)
    have hrbound (j : ℤ) (hj : j ∈ r.coeff.support) : -(R : ℤ) ≤ j := by
      have habs : j.natAbs ≤ R := Finset.le_sup hj
      by_cases hj0 : 0 ≤ j
      · omega
      · have heq := Int.eq_neg_natAbs_of_nonpos (show j ≤ 0 by omega)
        omega
    let s : LaurentPolynomial C(I, Matrix (Fin (q.size + b)) (Fin (q.size + b)) A) :=
      LaurentPolynomial.T (K : ℤ) * r
    let f (t : I) := evalPolynomial s t
    have hfc (t : I) (j : ℤ) : (f t).coeff j = s.coeff j t := evalPolynomial_coeff s t j
    have hscoeff (j : ℤ) : s.coeff j = r.coeff (j - K) := by
      simp only [s, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
      congr 1
      omega
    have hf (t : I) (j : ℤ) (hj : j < 0) : (f t).coeff j = 0 := by
      rw [hfc, hscoeff]
      have hz : r.coeff (j - K) = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hmem
        have hb := hrbound (j - K) hmem
        dsimp only [K] at hb
        omega
      rw [hz]
      rfl
    have hv (t : I) (z : Circle) : laurentPolynomialCircleValue (f t) z =
        (z : ℂ) ^ (K : ℤ) • r.coeff.sum (fun j a ↦ (z : ℂ) ^ j • a t) := by
      rw [evalPolynomial_value]
      dsimp only [s]
      rw [shiftValue r (K : ℤ) z]
      simp only [ContinuousMap.smul_apply, laurentPolynomialCircleValue,
        Finsupp.sum, ContinuousMap.sum_apply]
    have hi (t : I) (z : Circle) : IsUnit (laurentPolynomialCircleValue (f t) z) := by
      rw [hv, Algebra.smul_def]
      have hz : IsUnit ((z : ℂ) ^ (K : ℤ)) :=
        isUnit_iff_ne_zero.mpr (zpow_ne_zero _ z.coe_ne_zero)
      exact (hz.map (algebraMap ℂ _)).mul (hri t z)
    let d : ℕ := s.coeff.support.sup (fun j : ℤ ↦ j.natAbs)
    have hd (t : I) (j : ℤ) (hj : (d : ℤ) < j) : (f t).coeff j = 0 := by
      rw [hfc]
      have hz : s.coeff j = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hmem
        have habs : j.natAbs ≤ d := Finset.le_sup hmem
        have heq := Int.natAbs_of_nonneg (show 0 ≤ j by omega)
        omega
      rw [hz]
      rfl
    obtain ⟨g, hgf, hfg, hgc⟩ := uniformInverse s f hfc hi
    have hfcCont (j : ℤ) : Continuous (fun t ↦ (f t).coeff j) := by
      simp_rw [hfc]
      exact (s.coeff j).continuous
    have hclasses := familyClass_eq f hf d hd g hgf hfg hfcCont hgc
    -- Build the same original identity stabilizations and their exact quotient decompositions.
    have hconst (m : ℕ) : ((constantLaurent m).shift (K : ℤ)).IsPolynomial := by
      intro j hj
      change (LaurentPolynomial.T (K : ℤ) *
        (LaurentPolynomial.C (1 : Matrix (Fin m) (Fin m) A) +
          LaurentPolynomial.C 0 * LaurentPolynomial.T 1)).coeff j = 0
      simp only [map_zero, zero_mul, add_zero, map_one, mul_one]
      simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
        show (K : ℤ) ≠ j by omega, ite_false]
    obtain ⟨hpK, _⟩ := p.nonempty_rightShiftedCokernel_add_equiv k (l + R) hk
    obtain ⟨hqK', _⟩ := q.nonempty_rightShiftedCokernel_add_equiv l (k + R) hl
    have hqK : (q.shift (K : ℤ)).IsPolynomial := by
      simpa only [K, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hqK'
    let P := blockLaurent p (constantLaurent a)
    let Q := blockLaurent q (constantLaurent b)
    obtain ⟨hPK, hPindex⟩ := blockIndex p (constantLaurent a) K hpK (hconst a)
    obtain ⟨hQK, hQindex⟩ := blockIndex q (constantLaurent b) K hqK (hconst b)
    have hpvalue (z : Circle) : laurentPolynomialCircleValue P.polynomial z =
        (matrixUnitBlockSum (p.invertible z).unit
          (1 : (Matrix (Fin a) (Fin a) A)ˣ) :
            Matrix (Fin (p.size + a)) (Fin (p.size + a)) A) := by
      change laurentPolynomialCircleValue
        (blockLaurentPolynomial p.polynomial (constantLaurent a).polynomial) z = _
      rw [blockLaurentPolynomial_value]
      have hc : laurentPolynomialCircleValue (constantLaurent a).polynomial z = 1 := by
        change laurentPolynomialCircleValue
          (LaurentPolynomial.C 1 + LaurentPolynomial.C 0 * LaurentPolynomial.T 1) z = 1
        rw [map_zero, zero_mul, add_zero, ← LaurentPolynomial.single_eq_C]
        simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_single,
          Finsupp.sum_single_index, smul_zero, zpow_zero, one_smul]
      rw [hc]
      change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (laurentPolynomialCircleValue p.polynomial z) 0 0 1) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks ((p.invertible z).unit : Matrix (Fin p.size) (Fin p.size) A)
            0 0 1)
      rw [IsUnit.unit_spec]
    have hqvalue (z : Circle) : laurentPolynomialCircleValue Q.polynomial z =
        (matrixUnitBlockSum (q.invertible z).unit
          (1 : (Matrix (Fin b) (Fin b) A)ˣ) :
            Matrix (Fin (q.size + b)) (Fin (q.size + b)) A) := by
      change laurentPolynomialCircleValue
        (blockLaurentPolynomial q.polynomial (constantLaurent b).polynomial) z = _
      rw [blockLaurentPolynomial_value]
      have hc : laurentPolynomialCircleValue (constantLaurent b).polynomial z = 1 := by
        change laurentPolynomialCircleValue
          (LaurentPolynomial.C 1 + LaurentPolynomial.C 0 * LaurentPolynomial.T 1) z = 1
        rw [map_zero, zero_mul, add_zero, ← LaurentPolynomial.single_eq_C]
        simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_single,
          Finsupp.sum_single_index, smul_zero, zpow_zero, one_smul]
      rw [hc]
      change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (laurentPolynomialCircleValue q.polynomial z) 0 0 1) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks ((q.invertible z).unit : Matrix (Fin q.size) (Fin q.size) A)
            0 0 1)
      rw [IsUnit.unit_spec]
    have hFourier {n : ℕ} (u v : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (huv : ∀ z, laurentPolynomialCircleValue u z = laurentPolynomialCircleValue v z) :
        u = v := by
      have hw : laurentPolynomialWiener u = laurentPolynomialWiener v := by
        apply WienerLoop.eval_injective
        funext z
        rw [laurentPolynomialWiener_eval, laurentPolynomialWiener_eval, huv]
      apply AddMonoidAlgebra.coeff_injective
      apply Finsupp.ext
      intro j
      simpa only [laurentPolynomialWiener_coeff] using
        congrArg (fun w : WienerLoop (Matrix (Fin n) (Fin n) A) ↦ w j) hw
    have hcastValue {n m : ℕ} (h : n = m)
        (v : LaurentPolynomial (Matrix (Fin n) (Fin n) A)) (z : Circle) :
        laurentPolynomialCircleValue
          (cast (congrArg (fun d : ℕ ↦ LaurentPolynomial (Matrix (Fin d) (Fin d) A)) h) v) z =
        cast (congrArg (fun d : ℕ ↦ Matrix (Fin d) (Fin d) A) h)
          (laurentPolynomialCircleValue v z) := by
      subst m
      rfl
    have hcastSmul {n m : ℕ} (h : n = m) (c : ℂ)
        (v : Matrix (Fin n) (Fin n) A) :
        cast (congrArg (fun d : ℕ ↦ Matrix (Fin d) (Fin d) A) h) (c • v) =
          c • cast (congrArg (fun d : ℕ ↦ Matrix (Fin d) (Fin d) A) h) v := by
      subst m
      rfl
    have he₀ : f 0 = cast (congrArg
        (fun d : ℕ ↦ LaurentPolynomial (Matrix (Fin d) (Fin d) A)) hab)
          (P.shift (K : ℤ)).polynomial := by
      apply hFourier
      intro z
      rw [hv, hr₀, hcastValue hab]
      change _ = cast (congrArg (fun d : ℕ ↦ Matrix (Fin d) (Fin d) A) hab)
        (laurentPolynomialCircleValue (LaurentPolynomial.T (K : ℤ) * P.polynomial) z)
      rw [shiftValue P.polynomial (K : ℤ) z, hcastSmul hab, hpvalue]
    have he₁ : f 1 = (Q.shift (K : ℤ)).polynomial := by
      apply hFourier
      intro z
      rw [hv, hr₁]
      change _ = laurentPolynomialCircleValue (LaurentPolynomial.T (K : ℤ) * Q.polynomial) z
      rw [shiftValue Q.polynomial (K : ℤ) z, hqvalue]
    let := RightWiener.polynomialCokernel_finite (f 0) (hf 0) (g 0) (hgf 0) (hfg 0)
    let := RightWiener.polynomialCokernel_projective (f 0) (hf 0) (g 0) (hgf 0) (hfg 0)
    let := RightWiener.polynomialCokernel_finite (f 1) (hf 1) (g 1) (hgf 1) (hfg 1)
    let := RightWiener.polynomialCokernel_projective (f 1) (hf 1) (g 1) (hgf 1) (hfg 1)
    let := P.rightShiftedCokernel_finite K hPK
    let := P.rightShiftedCokernel_projective K hPK
    let := Q.rightShiftedCokernel_finite K hQK
    let := Q.rightShiftedCokernel_projective K hQK
    have h₀ := castClass hab (P.shift (K : ℤ)).polynomial (f 0) hPK (hf 0)
      he₀
    have h₁ := castClass rfl (Q.shift (K : ℤ)).polynomial (f 1) hQK (hf 1)
      he₁
    have heq : shiftedCokernelIndex P K hPK = shiftedCokernelIndex Q K hQK := by
      dsimp only [AtiyahSinger.RightKTheory.shiftedCokernelIndex]
      have hmodule : projectiveModuleKZeroClass A (P.RightShiftedCokernel K hPK) =
          projectiveModuleKZeroClass A (Q.RightShiftedCokernel K hQK) :=
        h₀.symm.trans (hclasses.trans h₁)
      apply congrArg₂ (fun x y : KZero A ↦ x - y) hmodule
      exact congrArg (fun n ↦ kZeroClass A (IdempotentMatrix.identity A (n * K))) hab
    have hPi : shiftedCokernelIndex P K hPK = shiftedCokernelIndex p K hpK := by
      rw [hPindex, constantIndex, add_zero]
    have hQi : shiftedCokernelIndex Q K hQK = shiftedCokernelIndex q K hqK := by
      rw [hQindex, constantIndex, add_zero]
    exact (shiftIndependent p k K hk hpK).trans
      (hPi.symm.trans (heq.trans (hQi.trans (shiftIndependent q K l hqK hl))))

/-- The actual cokernel index at a support-clearing shift of the original Laurent polynomial. -/
def cokernelIndex (p : LaurentMatrixLoop A) : KZero A :=
  shiftedCokernelIndex p p.exists_polynomial_difference.choose
    p.exists_polynomial_difference.choose_spec.1

/-- The original corrected index descends through the existing stable Laurent quotient. -/
def laurentLoopCokernelIndex : StableLaurentLoopClass A → KZero A :=
  Quotient.lift cokernelIndex (fun p q h ↦
    shiftedCokernelIndex_eq_of_stablyHomotopic p q _ _ _ _ h)

/-- Transport that same index along the existing continuous/Laurent stable comparison. -/
def stableLoopCokernelIndex (x : StableMatrixLoopClass A) : KZero A :=
  laurentLoopCokernelIndex (stableLaurentLoopEquiv.symm x)

open scoped Matrix Matrix.Norms.Operator unitInterval Topology in
set_option maxHeartbeats 800000 in

/-- The actual corrected right-cokernel function respects zero and the original loop addition. -/
theorem stableLoopCokernelIndex_additive :
    stableLoopCokernelIndex (0 : StableMatrixLoopClass A) = 0 ∧
      ∀ x y : StableMatrixLoopClass A,
        stableLoopCokernelIndex (x + y) =
          stableLoopCokernelIndex x + stableLoopCokernelIndex y := by
  /- Stage 1: choose actual Laurent representatives and one admissible
  shift for both. Their shifted block sum acts on the direct sum of the
  original positive right modules, so its range quotient is the product
  of the two actual cokernels. The correction rank (n+m)*k splits as
  n*k+m*k. Apply the projective-module product and free-class formulas.
  Stage 2: at shift zero the identity multiplier has zero cokernel.
  Shift independence makes its corrected class zero at every admissible shift.
  The preceding shift/stable-homotopy
  invariance removes the choices and identifies these calculations with
  the existing stable-loop zero and block-sum operations. The original
  Laurent comparison transports exactly these representatives and classes. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let matrixCompleteSpace (n : ℕ) : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
      inferInstanceAs (CompleteSpace (Fin n → Fin n → A))
    let rightColumnFinite (n : ℕ) : Module.Finite Aᵐᵒᵖ (Fin n → A) :=
      (finiteFreeRightModule_finite_projective A n).1
    let rightColumnProjective (n : ℕ) : Module.Projective Aᵐᵒᵖ (Fin n → A) :=
      (finiteFreeRightModule_finite_projective A n).2
    have shiftIndependent (p : LaurentMatrixLoop A) (k l : ℕ)
        (hk : (p.shift (k : ℤ)).IsPolynomial)
        (hl : (p.shift (l : ℤ)).IsPolynomial) :
        shiftedCokernelIndex p k hk = shiftedCokernelIndex p l hl :=
      shiftedCokernelIndex_eq_of_stablyHomotopic p p k l hk hl
        ((LaurentMatrixLoop.stableSetoid (A := A)).iseqv.refl p)
    have polynomialBlock
        {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A))
        (b : LaurentPolynomial (Matrix (Fin (n + m)) (Fin (n + m)) A))
        (hf : ∀ k, k < 0 → f.coeff k = 0)
        (hg : ∀ k, k < 0 → g.coeff k = 0)
        (hb : ∀ k, k < 0 → b.coeff k = 0)
        (hcoeff : ∀ k, b.coeff k = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (f.coeff k) 0 0 (g.coeff k))) :
        Nonempty (RightWiener.PolynomialCokernel b hb ≃ₗ[Aᵐᵒᵖ]
          RightWiener.PolynomialCokernel f hf × RightWiener.PolynomialCokernel g hg) := by
      classical
      let c : (Fin (n + m) → A) ≃ₗ[Aᵐᵒᵖ] (Fin n → A) × (Fin m → A) :=
        (LinearEquiv.piCongrLeft' Aᵐᵒᵖ (fun _ : Fin (n + m) ↦ A)
          finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ Aᵐᵒᵖ A)
      have hc (v : Fin (n + m) → A) :
          c v = (v ∘ Fin.castAdd m, v ∘ Fin.natAdd n) := rfl
      have hnorm₁ (v : Fin (n + m) → A) : ‖(c v).1‖ ≤ ‖v‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
        intro i
        exact norm_le_pi_norm v (Fin.castAdd m i)
      have hnorm₂ (v : Fin (n + m) → A) : ‖(c v).2‖ ≤ ‖v‖ := by
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
        intro i
        exact norm_le_pi_norm v (Fin.natAdd n i)
      have hnorm_inv (v : (Fin n → A) × (Fin m → A)) :
          ‖c.symm v‖ ≤ ‖v.1‖ + ‖v.2‖ := by
        apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        intro i
        obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
        cases a with
        | inl a =>
          have heq : c.symm v (Fin.castAdd m a) = v.1 a :=
            congrArg (fun w : (Fin n → A) × (Fin m → A) ↦ w.1 a)
              (c.apply_symm_apply v)
          change ‖c.symm v (Fin.castAdd m a)‖ ≤ _
          rw [heq]
          exact (norm_le_pi_norm v.1 a).trans (le_add_of_nonneg_right (norm_nonneg _))
        | inr a =>
          have heq : c.symm v (Fin.natAdd n a) = v.2 a :=
            congrArg (fun w : (Fin n → A) × (Fin m → A) ↦ w.2 a)
              (c.apply_symm_apply v)
          change ‖c.symm v (Fin.natAdd n a)‖ ≤ _
          rw [heq]
          exact (norm_le_pi_norm v.2 a).trans (le_add_of_nonneg_left (norm_nonneg _))
      have hmem₁ (x : PositiveWienerModule A (n + m)) :
          Memℓp (fun k : ℕ ↦ (c (x k)).1) 1 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_one, Real.rpow_one]
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hnorm₁ (x k))
        simpa only [ENNReal.toReal_one, Real.rpow_one] using x.2.summable (by simp)
      have hmem₂ (x : PositiveWienerModule A (n + m)) :
          Memℓp (fun k : ℕ ↦ (c (x k)).2) 1 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_one, Real.rpow_one]
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hnorm₂ (x k))
        simpa only [ENNReal.toReal_one, Real.rpow_one] using x.2.summable (by simp)
      have hmem_inv (x : PositiveWienerModule A n × PositiveWienerModule A m) :
          Memℓp (fun k : ℕ ↦ c.symm (x.1 k, x.2 k)) 1 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_one, Real.rpow_one]
        apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (fun k ↦ hnorm_inv (x.1 k, x.2 k))
        have hx₁ : Summable (fun k : ℕ ↦ ‖x.1 k‖) := by simpa using x.1.2.summable
        have hx₂ : Summable (fun k : ℕ ↦ ‖x.2 k‖) := by simpa using x.2.2.summable
        exact hx₁.add hx₂
      let e : PositiveWienerModule A (n + m) ≃ₗ[Aᵐᵒᵖ]
          PositiveWienerModule A n × PositiveWienerModule A m :=
        { toFun x := (⟨fun k ↦ (c (x k)).1, hmem₁ x⟩, ⟨fun k ↦ (c (x k)).2, hmem₂ x⟩)
          invFun x := ⟨fun k ↦ c.symm (x.1 k, x.2 k), hmem_inv x⟩
          left_inv x := by
            apply lp.ext
            funext k
            exact c.symm_apply_apply (x k)
          right_inv x := by
            apply Prod.ext <;> apply lp.ext <;> funext k
            · exact congrArg Prod.fst (c.apply_symm_apply (x.1 k, x.2 k))
            · exact congrArg Prod.snd (c.apply_symm_apply (x.1 k, x.2 k))
          map_add' x y := by
            apply Prod.ext <;> apply lp.ext <;> funext k
            · exact congrArg Prod.fst (c.map_add (x k) (y k))
            · exact congrArg Prod.snd (c.map_add (x k) (y k))
          map_smul' a x := by
            apply Prod.ext <;> apply lp.ext <;> funext k
            · exact congrArg Prod.fst (c.map_smul a (x k))
            · exact congrArg Prod.snd (c.map_smul a (x k)) }
      have hmatrix (a : Matrix (Fin n) (Fin n) A) (b : Matrix (Fin m) (Fin m) A)
          (v : Fin (n + m) → A) :
          c ((Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks a 0 0 b)).mulVec v) =
            (a.mulVec (c v).1, b.mulVec (c v).2) := by
        change c ((Matrix.fromBlocks a 0 0 b).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ v) = _
        rw [Matrix.submatrix_mulVec_equiv _ _ _ finSumFinEquiv.symm,
          Matrix.fromBlocks_mulVec]
        apply Prod.ext <;> ext i <;> simp [hc, Function.comp_def]
      have hinter (x : PositiveWienerModule A (n + m)) :
          e (RightWiener.polynomialMultiplier b hb x) =
            (RightWiener.polynomialMultiplier f hf (e x).1,
              RightWiener.polynomialMultiplier g hg (e x).2) := by
        have hk (k : ℕ) : c (RightWiener.polynomialMultiplier b hb x k) =
            (RightWiener.polynomialMultiplier f hf (e x).1 k,
              RightWiener.polynomialMultiplier g hg (e x).2 k) := by
          rw [RightWiener.polynomialMultiplier_coeff, map_sum]
          simp_rw [hcoeff, hmatrix]
          apply Prod.ext <;>
            simp only [Prod.fst_sum, Prod.snd_sum, RightWiener.polynomialMultiplier_coeff]
          · rfl
          · rfl
        apply Prod.ext <;> apply lp.ext <;> funext k
        · exact congrArg Prod.fst (hk k)
        · exact congrArg Prod.snd (hk k)
      obtain ⟨q, _⟩ := exists_quotientRange_prod_equiv_of_intertwine e
        (RightWiener.polynomialMultiplier b hb)
        (RightWiener.polynomialMultiplier f hf)
        (RightWiener.polynomialMultiplier g hg) hinter
      exact ⟨q⟩
    let blockLaurentPolynomial {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A)) :
        LaurentPolynomial (Matrix (Fin (n + m)) (Fin (n + m)) A) := by
      let L : Matrix (Fin n) (Fin n) A →ₗ[ℂ]
          Matrix (Fin (n + m)) (Fin (n + m)) A :=
        { toFun a := Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks a 0 0 (0 : Matrix (Fin m) (Fin m) A))
          map_add' a b := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
          map_smul' c a := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj] }
      let R : Matrix (Fin m) (Fin m) A →ₗ[ℂ]
          Matrix (Fin (n + m)) (Fin (n + m)) A :=
        { toFun a := Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) A) 0 0 a)
          map_add' a b := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
          map_smul' c a := by
            ext i j
            cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
              simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj] }
      exact AddMonoidAlgebra.map L.toAddMonoidHom f + AddMonoidAlgebra.map R.toAddMonoidHom g
    have blockLaurentPolynomial_coeff {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A)) (k : ℤ) :
        (blockLaurentPolynomial f g).coeff k =
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (f.coeff k) 0 0 (g.coeff k)) := by
      dsimp only [blockLaurentPolynomial]
      simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_map]
      ext i j
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
    have blockLaurentPolynomial_value {n m : ℕ}
        (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (g : LaurentPolynomial (Matrix (Fin m) (Fin m) A)) (z : Circle) :
        laurentPolynomialCircleValue (blockLaurentPolynomial f g) z =
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (laurentPolynomialCircleValue f z) 0 0
              (laurentPolynomialCircleValue g z)) := by
      classical
      have hmap {a b : ℕ} (L : Matrix (Fin a) (Fin a) A →ₗ[ℂ]
          Matrix (Fin b) (Fin b) A) (p : LaurentPolynomial (Matrix (Fin a) (Fin a) A)) :
          laurentPolynomialCircleValue (AddMonoidAlgebra.map L.toAddMonoidHom p) z =
            L (laurentPolynomialCircleValue p z) := by
        simp only [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_map]
        rw [Finsupp.sum_mapRange_index]
        · rw [map_finsuppSum]
          apply Finsupp.sum_congr
          intro j b
          exact (L.map_smul ((z : ℂ) ^ j) (p.coeff j)).symm
        · intro j
          simp
      have hadd {a : ℕ} (p q : LaurentPolynomial (Matrix (Fin a) (Fin a) A)) :
          laurentPolynomialCircleValue (p + q) z =
            laurentPolynomialCircleValue p z + laurentPolynomialCircleValue q z := by
        simp [laurentPolynomialCircleValue, AddMonoidAlgebra.coeff_add,
          Finsupp.sum_add_index, smul_add]
      dsimp only [blockLaurentPolynomial]
      rw [hadd, hmap, hmap]
      ext i j
      cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
        simp [Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
    let blockLaurent (p q : LaurentMatrixLoop A) : LaurentMatrixLoop A :=
      { size := p.size + q.size
        polynomial := blockLaurentPolynomial p.polynomial q.polynomial
        normalized := by
          rw [blockLaurentPolynomial_value, p.normalized, q.normalized]
          simp [Matrix.fromBlocks_one]
        invertible z := by
          rw [blockLaurentPolynomial_value]
          have h := (matrixUnitBlockSum (p.invertible z).unit (q.invertible z).unit).isUnit
          change IsUnit (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks
              ((p.invertible z).unit : Matrix (Fin p.size) (Fin p.size) A) 0 0
              ((q.invertible z).unit : Matrix (Fin q.size) (Fin q.size) A))) at h
          simpa only [IsUnit.unit_spec] using h }
    have blockIndex (p q : LaurentMatrixLoop A) (k : ℕ)
        (hp : (p.shift (k : ℤ)).IsPolynomial) (hq : (q.shift (k : ℤ)).IsPolynomial) :
        ∃ hb : ((blockLaurent p q).shift (k : ℤ)).IsPolynomial,
          shiftedCokernelIndex (blockLaurent p q) k hb =
            shiftedCokernelIndex p k hp + shiftedCokernelIndex q k hq := by
      classical
      have hc (j : ℤ) : (((blockLaurent p q).shift (k : ℤ)).polynomial).coeff j =
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks ((p.shift (k : ℤ)).polynomial.coeff j) 0 0
              ((q.shift (k : ℤ)).polynomial.coeff j)) := by
        simp only [LaurentMatrixLoop.shift, LaurentPolynomial.T,
          AddMonoidAlgebra.coeff_single_mul_apply, one_mul, blockLaurent,
          blockLaurentPolynomial_coeff]
      have hb : ((blockLaurent p q).shift (k : ℤ)).IsPolynomial := by
        intro j hj
        rw [hc, hp j hj, hq j hj]
        simp
      refine ⟨hb, ?_⟩
      obtain ⟨e⟩ := polynomialBlock
        (p.shift (k : ℤ)).polynomial (q.shift (k : ℤ)).polynomial
        ((blockLaurent p q).shift (k : ℤ)).polynomial hp hq hb hc
      let := p.rightShiftedCokernel_finite k hp
      let := p.rightShiftedCokernel_projective k hp
      let := q.rightShiftedCokernel_finite k hq
      let := q.rightShiftedCokernel_projective k hq
      let := (blockLaurent p q).rightShiftedCokernel_finite k hb
      let := (blockLaurent p q).rightShiftedCokernel_projective k hb
      let e' : (blockLaurent p q).RightShiftedCokernel k hb ≃ₗ[Aᵐᵒᵖ]
          p.RightShiftedCokernel k hp × q.RightShiftedCokernel k hq := e
      have heq := projectiveModuleKZeroClass_eq_of_linearEquiv e'
      have hfree (m n : ℕ) :
          kZeroClass A (IdempotentMatrix.identity A (m + n)) =
            kZeroClass A (IdempotentMatrix.identity A m) +
              kZeroClass A (IdempotentMatrix.identity A n) := by
        have h : (IdempotentMatrix.identity A m).blockSum
            (IdempotentMatrix.identity A n) = IdempotentMatrix.identity A (m + n) := by
          dsimp only [IdempotentMatrix.blockSum, IdempotentMatrix.identity]
          congr 1
          simp [IdempotentMatrix.blockMatrix, Matrix.fromBlocks_one]
        rw [← h, kZeroClass_blockSum]
      dsimp only [AtiyahSinger.RightKTheory.shiftedCokernelIndex]
      rw [heq, projectiveModuleKZeroClass_prod]
      change _ - kZeroClass A (IdempotentMatrix.identity A ((p.size + q.size) * k)) = _
      rw [Nat.add_mul, hfree]
      abel
    let constantLaurent (n : ℕ) : LaurentMatrixLoop A :=
      LaurentMatrixLoop.affine (1 : Matrix (Fin n) (Fin n) A) 0
        (by simp) (by intro z; simp)
    have constantIndex (n k : ℕ)
        (hk : ((constantLaurent n).shift (k : ℤ)).IsPolynomial) :
        shiftedCokernelIndex (constantLaurent n) k hk = 0 := by
      classical
      let p := constantLaurent n
      let f := (p.shift (0 : ℤ)).polynomial
      have hf : f = LaurentPolynomial.C 1 := by
        change LaurentPolynomial.T 0 *
          (LaurentPolynomial.C 1 + LaurentPolynomial.C 0 * LaurentPolynomial.T 1) = _
        rw [LaurentPolynomial.T_zero, one_mul, map_zero, zero_mul, add_zero]
        rfl
      have hcoeff (j : ℤ) : f.coeff j = if 0 = j then 1 else 0 := by
        rw [hf, ← LaurentPolynomial.single_eq_C]
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      have hp : (p.shift (0 : ℤ)).IsPolynomial := by
        intro j hj
        change f.coeff j = 0
        rw [hcoeff, ite_eq_right (by omega)]
      have hT (x : PositiveWienerModule A n) : RightWiener.polynomialMultiplier f hp x = x := by
        apply lp.ext
        funext j
        rw [RightWiener.polynomialMultiplier_coeff]
        rw [Finset.sum_eq_single 0]
        · simp [hcoeff]
        · intro a ha hne
          simp only [hcoeff, show (0 : ℤ) ≠ (a : ℤ) by omega, ite_false, Matrix.zero_mulVec]
        · simp
      let := p.rightShiftedCokernel_finite 0 hp
      let := p.rightShiftedCokernel_projective 0 hp
      have hzero (q : RightWiener.PolynomialCokernel f hp) : q = 0 := by
        obtain ⟨x, rfl⟩ :=
          (LinearMap.range (RightWiener.polynomialMultiplier f hp)).mkQ_surjective q
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hT x⟩
      let e : RightWiener.PolynomialCokernel f hp ≃ₗ[Aᵐᵒᵖ] (Fin 0 → A) :=
        LinearEquiv.ofBijective 0 ⟨fun x y _ ↦ (hzero x).trans (hzero y).symm,
          fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
      let e' : p.RightShiftedCokernel 0 hp ≃ₗ[Aᵐᵒᵖ] (Fin 0 → A) := e
      have hclass := projectiveModuleKZeroClass_eq_of_linearEquiv e'
      have hbase : shiftedCokernelIndex p 0 hp = 0 := by
        dsimp only [AtiyahSinger.RightKTheory.shiftedCokernelIndex]
        rw [hclass, projectiveModuleKZeroClass_free]
        simp
      exact (shiftIndependent p k 0 hk hp).trans hbase
    -- The Laurent comparison returns the same original representative and chosen index.
    have hindex (p : LaurentMatrixLoop A) (k : ℕ)
        (hk : (p.shift (k : ℤ)).IsPolynomial) :
        stableLoopCokernelIndex p.stableClass = shiftedCokernelIndex p k hk := by
      have hc : stableLaurentLoopEquiv (stableLaurentLoopClass p) = p.stableClass := rfl
      change laurentLoopCokernelIndex (stableLaurentLoopEquiv.symm p.stableClass) = _
      rw [← hc, Equiv.symm_apply_apply]
      change cokernelIndex p = _
      exact shiftedCokernelIndex_eq_of_stablyHomotopic p p _ k _ hk
        ((LaurentMatrixLoop.stableSetoid (A := A)).iseqv.refl p)
    have hblockClass (p q : LaurentMatrixLoop A) :
        (blockLaurent p q).stableClass = p.stableClass + q.stableClass := by
      change stableMatrixLoopClass (blockLaurent p q).toFiniteMatrixLoop =
        stableMatrixLoopClass p.toFiniteMatrixLoop + stableMatrixLoopClass q.toFiniteMatrixLoop
      rw [← stableMatrixLoopClass_blockSum]
      apply congrArg stableMatrixLoopClass
      change (⟨p.size + q.size, (blockLaurent p q).toFiniteMatrixLoop.loop⟩ : FiniteMatrixLoop A) =
        ⟨p.size + q.size, (p.toFiniteMatrixLoop.blockSum q.toFiniteMatrixLoop).loop⟩
      congr 1
      apply Path.ext
      funext t
      apply Units.ext
      change (((blockLaurent p q).invertible (Circle.exp (2 * Real.pi * (t : ℝ)))).unit :
        Matrix (Fin (p.size + q.size)) (Fin (p.size + q.size)) A) =
        (matrixUnitBlockSum
          (p.invertible (Circle.exp (2 * Real.pi * (t : ℝ)))).unit
          (q.invertible (Circle.exp (2 * Real.pi * (t : ℝ)))).unit : _)
      rw [IsUnit.unit_spec]
      change laurentPolynomialCircleValue (blockLaurentPolynomial p.polynomial q.polynomial) _ = _
      rw [blockLaurentPolynomial_value]
      change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (laurentPolynomialCircleValue p.polynomial _) 0 0
          (laurentPolynomialCircleValue q.polynomial _)) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks
            ((p.invertible _).unit : Matrix (Fin p.size) (Fin p.size) A) 0 0
            ((q.invertible _).unit : Matrix (Fin q.size) (Fin q.size) A))
      rw [IsUnit.unit_spec, IsUnit.unit_spec]
    constructor
    · -- The original zero-size identity has its actual zero quotient.
      have hz : (constantLaurent 0).stableClass = 0 := by
        change stableMatrixLoopClass (constantLaurent 0).toFiniteMatrixLoop =
          stableMatrixLoopClass (FiniteMatrixLoop.constant 0)
        apply congrArg stableMatrixLoopClass
        change (⟨0, _⟩ : FiniteMatrixLoop A) = ⟨0, _⟩
        congr 1
        apply Path.ext
        funext t
        apply Units.ext
        ext i j
        exact Fin.elim0 i
      have hp : ((constantLaurent 0).shift (0 : ℤ)).IsPolynomial := by
        intro j hj
        ext i j
        exact Fin.elim0 i
      calc
        stableLoopCokernelIndex (0 : StableMatrixLoopClass A) =
            stableLoopCokernelIndex (constantLaurent 0).stableClass :=
          congrArg stableLoopCokernelIndex hz.symm
        _ = shiftedCokernelIndex (constantLaurent 0) 0 hp := hindex _ 0 hp
        _ = 0 := constantIndex 0 0 hp
    · -- Compare the same Laurent block representative at one admissible shift.
      intro x y
      obtain ⟨x', rfl⟩ := (stableLaurentLoopEquiv (A := A)).surjective x
      obtain ⟨y', rfl⟩ := (stableLaurentLoopEquiv (A := A)).surjective y
      refine Quotient.inductionOn₂ x' y' ?_
      intro p q
      change stableLoopCokernelIndex (p.stableClass + q.stableClass) =
        stableLoopCokernelIndex p.stableClass + stableLoopCokernelIndex q.stableClass
      obtain ⟨kp, hp, _⟩ := p.exists_polynomial_difference
      obtain ⟨kq, hq, _⟩ := q.exists_polynomial_difference
      obtain ⟨hpK, _⟩ := p.nonempty_rightShiftedCokernel_add_equiv kp kq hp
      obtain ⟨hqK', _⟩ := q.nonempty_rightShiftedCokernel_add_equiv kq kp hq
      have hqK : (q.shift ((kp + kq : ℕ) : ℤ)).IsPolynomial := by
        simpa only [Nat.add_comm kq kp] using hqK'
      obtain ⟨hb, hbi⟩ := blockIndex p q (kp + kq) hpK hqK
      calc
        stableLoopCokernelIndex (p.stableClass + q.stableClass) =
            stableLoopCokernelIndex (blockLaurent p q).stableClass :=
          congrArg stableLoopCokernelIndex (hblockClass p q).symm
        _ = shiftedCokernelIndex (blockLaurent p q) (kp + kq) hb := hindex _ _ hb
        _ = shiftedCokernelIndex p (kp + kq) hpK +
            shiftedCokernelIndex q (kp + kq) hqK := hbi
        _ = stableLoopCokernelIndex p.stableClass + stableLoopCokernelIndex q.stableClass :=
          congrArg₂ (fun a b : KZero A ↦ a + b) (hindex p _ hpK).symm (hindex q _ hqK).symm

/-- The Bott inverse homomorphism whose values are the actual corrected right-cokernel classes. -/
def stableLoopBottInverse (A : Type u) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] : StableMatrixLoopClass A →+ KZero A where
  toFun := stableLoopCokernelIndex
  map_zero' := stableLoopCokernelIndex_additive.1
  map_add' := stableLoopCokernelIndex_additive.2

/-- This inverse evaluates to the same original quotient class at every admissible shift. -/
theorem stableLoopBottInverse_laurent (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    stableLoopBottInverse A p.stableClass = shiftedCokernelIndex p k hk := by
  /- The continuous/Laurent comparison takes the original Laurent class
  of p to p.stableClass, so its inverse returns that same quotient class.
  Evaluate the actual quotient lift and use the existing stable-homotopy
  equivalence relation with p itself to replace the support-clearing shift
  selected by cokernelIndex with the supplied k and hk. No new quotient,
  Laurent representative or projective model appears in the conclusion. -/
  -- The inverse comparison returns exactly the original Laurent quotient representative.
  have hc : stableLaurentLoopEquiv (stableLaurentLoopClass p) = p.stableClass := rfl
  change laurentLoopCokernelIndex (stableLaurentLoopEquiv.symm p.stableClass) = _
  rw [← hc, Equiv.symm_apply_apply]
  change cokernelIndex p = _
  -- The already proved invariant removes the chosen support-clearing shift.
  exact shiftedCokernelIndex_eq_of_stablyHomotopic p p _ k _ hk
    ((LaurentMatrixLoop.stableSetoid (A := A)).iseqv.refl p)

/-- KA III.1.20: the actual right-cokernel homomorphism is left inverse to the actual Bott map. -/
theorem stableLoopBottInverse_left_inverse :
    Function.LeftInverse (stableLoopBottInverse A) (kZeroBottLoop A) := by
  /- Stage 1: take the actual Laurent representative of z*p+(1-p) for
  each original right-projective presentation p. The established
  bottLaurentLoop comparison retains the same positive circle parameter.
  At shift zero its right multiplier quotient maps onto p.image by
  [x] -> p*x_0, with exactly the displayed original p and coefficient x_0.
  Stage 2: the actual quotient equivalence and the projective-image class
  formula identify this cokernel class with kZeroClass A p. The correction
  is the identity matrix of size p.size*0, whose free module class is zero.
  Stage 3: the original idempotent classes generate the right K-zero
  quotient. Both maps are homomorphisms and the Bott generator formula
  is specified, so extend the identity from those classes to all virtual
  right-projective classes. Neither Bott injectivity nor an arbitrary
  inverse chosen from a bijectivity statement is assumed in this argument. -/
  classical
  -- The zero-dimensional free class vanishes by the original direct-sum relation.
  have hzero : kZeroClass A (IdempotentMatrix.identity A 0) = 0 := by
    let e := IdempotentMatrix.identity A 0
    have he : e.blockSum e = e := by
      dsimp only [e, IdempotentMatrix.blockSum, IdempotentMatrix.identity]
      congr 1
      simp [IdempotentMatrix.blockMatrix, Matrix.fromBlocks_one]
    have hrel : kZeroClass A e = kZeroClass A e + kZeroClass A e :=
      (congrArg (kZeroClass A) he).symm.trans (kZeroClass_blockSum e e)
    exact add_left_cancel (show kZeroClass A e + kZeroClass A e = kZeroClass A e + 0 by
      simpa only [add_zero] using hrel.symm)
  -- Evaluate the actual inverse on the same positively oriented Bott representative.
  have hgenerator (p : IdempotentMatrix A) :
      stableLoopBottInverse A (kZeroBottLoop A (kZeroClass A p)) = kZeroClass A p := by
    rw [kZeroBottLoop_class, ← bottLaurentLoop_stableClass]
    obtain ⟨hp, e, he⟩ := exists_bottLaurentLoop_cokernel_equiv p
    rw [stableLoopBottInverse_laurent _ 0 hp]
    let := (bottLaurentLoop p).rightShiftedCokernel_finite 0 hp
    let := (bottLaurentLoop p).rightShiftedCokernel_projective 0 hp
    let := p.finite_image
    let := p.projective_image
    have hc := projectiveModuleKZeroClass_eq_of_linearEquiv e
    dsimp only [AtiyahSinger.RightKTheory.shiftedCokernelIndex]
    rw [hc, projectiveModuleKZeroClass_image, Nat.mul_zero, hzero, sub_zero]
  -- Generator equality extends through precisely the existing K-zero universal property.
  have hhom : (stableLoopBottInverse A).comp (kZeroBottLoop A) =
      AddMonoidHom.id (KZero A) :=
    (kZero_universal_property (fun p : IdempotentMatrix A ↦ kZeroClass A p)
      (fun p q h ↦ kZeroClass_eq_of_isEquivalent p q h)
      (fun p q ↦ kZeroClass_blockSum p q)).unique hgenerator (fun _ ↦ rfl)
  intro x
  exact DFunLike.congr_fun hhom x

/-- The actual Bott map is bijective for a possibly noncommutative complex Banach algebra. -/
theorem kZeroBottLoop_bijective : Function.Bijective (kZeroBottLoop A) := by
  /- The constructed right-cokernel homomorphism is a left inverse and
  therefore makes the original Bott map injective. Combine this with
  its separately constructed surjectivity from Laurent approximation
  and the same-projector affine contraction. No geometric index theorem
  or commutative-coefficient reduction supplies this bijectivity. -/
  -- The specified cokernel map provides injectivity; the independent reduction gives surjectivity.
  exact ⟨(stableLoopBottInverse_left_inverse (A := A)).injective, kZeroBottLoop_surjective⟩

/-- The equivalence keeps the actual Bott homomorphism and the specified right-cokernel inverse. -/
def kZeroBottLoopEquiv (A : Type u) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] : KZero A ≃+ StableMatrixLoopClass A where
  toFun := kZeroBottLoop A
  invFun := stableLoopBottInverse A
  left_inv := stableLoopBottInverse_left_inverse
  right_inv := by
    intro x
    obtain ⟨y, rfl⟩ := kZeroBottLoop_surjective x
    exact congrArg (kZeroBottLoop A) (stableLoopBottInverse_left_inverse y)
  map_add' := map_add (kZeroBottLoop A)

section CommutativeComparison

variable {R : Type u} [NormedCommRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- The complete inverse commutes with the original same-matrix comparison of K-zero models. -/
theorem stableLoopBottInverse_eq_comm :
    (commKZeroEquiv R).toAddMonoidHom.comp (stableLoopBottInverse R) =
      AtiyahSinger.stableLoopBottInverse R := by
  /- Stage 1: the previous kZeroBottLoop_eq_comm identifies the two
  forward homomorphisms after the actual same-matrix comparison. Given
  a stable loop class, use the surjectivity of the right Bott map to write
  it as the image of a right-projective K-zero class.
  Stage 2: on that class the right inverse returns the original right
  class, then commKZeroEquiv sends it to the corresponding commutative class.
  The same forward-map comparison and the commutative left-inverse theorem
  give that identical result by the other route. Homomorphism extensionality
  proves the displayed equality. No arbitrary identification of left and
  right scalar actions on a separately chosen quotient module is needed. -/
  -- Use the same actual right-projective class furnished by Bott surjectivity.
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := kZeroBottLoop_surjective (A := R) x
  change commKZeroEquiv R (stableLoopBottInverse R (kZeroBottLoop R y)) =
    AtiyahSinger.stableLoopBottInverse R (kZeroBottLoop R y)
  have hf : kZeroBottLoop R y =
      AtiyahSinger.kZeroBottLoop R (commKZeroEquiv R y) :=
    DFunLike.congr_fun (kZeroBottLoop_eq_comm (R := R)) y
  -- The two specified left inverses return that class in their respective models.
  rw [stableLoopBottInverse_left_inverse y, hf,
    AtiyahSinger.stableLoopBottInverse_left_inverse]

/-- Every specified Laurent shift has the same corrected index in the two commutative models. -/
theorem shiftedCokernelIndex_comm (p : LaurentMatrixLoop R) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    commKZeroEquiv R (shiftedCokernelIndex p k hk) =
      AtiyahSinger.LaurentMatrixLoop.shiftedCokernelIndex p k hk := by
  /- Evaluate the preceding equality of inverse homomorphisms on the
  original p.stableClass. On each side apply its Laurent evaluation
  theorem using the identical p, k and hk. The result is precisely the
  two displayed actual corrected quotient classes. Their agreement
  follows through the specified inverse maps, without replacing either
  quotient or silently changing its scalar module structure. -/
  -- Evaluate both specified inverse homomorphisms on the identical Laurent loop.
  have hc := DFunLike.congr_fun (stableLoopBottInverse_eq_comm (R := R)) p.stableClass
  change commKZeroEquiv R (stableLoopBottInverse R p.stableClass) =
    AtiyahSinger.stableLoopBottInverse R p.stableClass at hc
  -- Both evaluations use exactly the supplied nonnegative shift and its certificate.
  rwa [stableLoopBottInverse_laurent p k hk,
    AtiyahSinger.stableLoopBottInverse_laurent p k hk] at hc

end CommutativeComparison

end AtiyahSinger.RightKTheory

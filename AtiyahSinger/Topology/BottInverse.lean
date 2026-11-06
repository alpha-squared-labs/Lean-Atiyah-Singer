/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.IdempotentHomotopy
public import AtiyahSinger.Topology.LaurentCokernel
public import AtiyahSinger.Topology.ProjectiveKZero

/-!
# The shifted-cokernel inverse to the specified Bott loop map

Public module ID: M1566.

Karoubi III.1.19–1.20, pp.119–120. The inverse is constructed from the actual
polynomial multiplier cokernel, with the free rank correction n*k. Independence
of shift, stable homotopy invariance and additivity are proved for this
specified construction. The resulting isomorphism uses the existing Bott map.

The current module and K₀ carriers require commutative complex Banach coefficients.
The source allows noncommutative coefficients. Neither that generalization nor
the relative clutching comparison or the geometric Bott external-product theorem
is supplied here. The specified commutative loop inverse is proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

/-- Standard direct-sum cokernel comparison, with the original representative formula. -/
theorem exists_quotientRange_prod_equiv_of_intertwine
    {R X Y Z : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (e : X ≃ₗ[R] Y × Z) (T : X →ₗ[R] X) (U : Y →ₗ[R] Y) (V : Z →ₗ[R] Z)
    (h : ∀ x : X, e (T x) = (U (e x).1, V (e x).2)) :
    ∃ q : (X ⧸ LinearMap.range T) ≃ₗ[R]
        (Y ⧸ LinearMap.range U) × (Z ⧸ LinearMap.range V),
      ∀ x : X, q (Submodule.Quotient.mk x) =
        (Submodule.Quotient.mk (e x).1, Submodule.Quotient.mk (e x).2) := by
  -- Quotient the two components of the specified direct-sum coordinates.
  let F : X →ₗ[R] (Y ⧸ LinearMap.range U) × (Z ⧸ LinearMap.range V) :=
    (((LinearMap.range U).mkQ.comp (LinearMap.fst R Y Z)).comp e.toLinearMap).prod
      (((LinearMap.range V).mkQ.comp (LinearMap.snd R Y Z)).comp e.toLinearMap)
  have hker : LinearMap.range T = LinearMap.ker F := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      change ((Submodule.Quotient.mk (e (T y)).1 : Y ⧸ LinearMap.range U),
        (Submodule.Quotient.mk (e (T y)).2 : Z ⧸ LinearMap.range V)) = 0
      rw [h]
      apply Prod.ext
      · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(e y).1, rfl⟩
      · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(e y).2, rfl⟩
    · intro x hx
      have hxY : (Submodule.Quotient.mk (e x).1 : Y ⧸ LinearMap.range U) = 0 :=
        congrArg Prod.fst hx
      have hxZ : (Submodule.Quotient.mk (e x).2 : Z ⧸ LinearMap.range V) = 0 :=
        congrArg Prod.snd hx
      obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hxY
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hxZ
      refine ⟨e.symm (y, z), e.injective ?_⟩
      rw [h, e.apply_symm_apply]
      exact Prod.ext hy hz
  have hsurj : Function.Surjective F := by
    rintro ⟨y, z⟩
    obtain ⟨a, rfl⟩ := (LinearMap.range U).mkQ_surjective y
    obtain ⟨b, rfl⟩ := (LinearMap.range V).mkQ_surjective z
    refine ⟨e.symm (a, b), ?_⟩
    change ((Submodule.Quotient.mk (e (e.symm (a, b))).1 : Y ⧸ LinearMap.range U),
      (Submodule.Quotient.mk (e (e.symm (a, b))).2 : Z ⧸ LinearMap.range V)) = _
    rw [e.apply_symm_apply]
    rfl
  -- The first isomorphism theorem gives the actual range quotient, retaining its values.
  let q := (Submodule.quotEquivOfEq (LinearMap.range T) (LinearMap.ker F) hker).trans
    (F.quotKerEquivOfSurjective hsurj)
  exact ⟨q, fun _ ↦ rfl⟩

variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

namespace LaurentMatrixLoop

/-- The corrected class of the actual multiplier cokernel at an admissible shift. -/
def shiftedCokernelIndex (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) : KZero A := by
  letI := p.shiftedCokernel_finite k hk
  letI := p.shiftedCokernel_projective k hk
  exact projectiveModuleKZeroClass A (p.ShiftedCokernel k hk) -
    kZeroClass A (IdempotentMatrix.identity A (p.size * k))

open scoped Matrix Matrix.Norms.Operator unitInterval Topology in
set_option maxHeartbeats 1600000 in

/-- KA III.1.19: the corrected cokernel class depends only on the stable Laurent class,
including independence of the two admissible shifts and their polynomiality certificates. -/
theorem shiftedCokernelIndex_eq_of_stablyHomotopic (p q : LaurentMatrixLoop A)
    (k l : ℕ) (hk : (p.shift (k : ℤ)).IsPolynomial)
    (hl : (q.shift (l : ℤ)).IsPolynomial) (h : p.StablyHomotopic q) :
    p.shiftedCokernelIndex k hk = q.shiftedCokernelIndex l hl := by
  /- Stage 1: the shift-cokernel decomposition adds a free module of rank n*j
  when the shift grows by j. The same rank is added to the subtracted free class,
  so arbitrary admissible shifts can be compared at a common larger shift.
  Stage 2: adding an identity block of size m adds the cokernel of z^k I_m,
  which is the free module of rank m*k. This cancels the change in correction.
  Stage 3: use the single finite exponent set of the specified stable Laurent
  homotopy to choose one shift for the whole family, in the common matrix size.
  Equality of endpoint circle values identifies their finite Laurent coefficients
  by Fourier uniqueness, retaining the prescribed identity blocks and size transport.
  Its continuous coefficients form a polynomial over C(I,A). Pointwise inversion
  is continuous, so each circle value is a unit over this coefficient algebra.
  The finite-support Wiener inverse theorem then applies over C(I,A). For one common
  degree bound d, the exact repair gives E=I-TS with range in the low-degree
  inclusion J. If C extracts those coefficients, P=CEJ is a finite idempotent
  matrix over C(I,A), and its image presents the actual cokernel.
  Bounded endpoint evaluation commutes with the displayed finite products and
  absolutely convergent inverse-coefficient sums. Thus P at each endpoint is the
  corresponding exact cokernel projector for that endpoint multiplier. Apply the
  idempotent path theorem to this same finite matrix family. No flatness assumption,
  arbitrary kernel transport or base-change identity for an infinite Wiener module
  is needed to identify the endpoint cokernels.
  Stage 4: descend their isomorphism to K₀, keep the identical free correction,
  and undo the common shifts and stabilizations. Every change uses the same actual
  multiplier quotient; a pair of unrelated finite projective models is insufficient. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let matrixCompleteSpace (n : ℕ) : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
      inferInstanceAs (CompleteSpace (Fin n → Fin n → A))
    have familyClass_eq {n : ℕ}
        (f : I → LaurentPolynomial (Matrix (Fin n) (Fin n) A))
        (hf : ∀ t k, k < 0 → (f t).coeff k = 0)
        (hi : ∀ t z, IsUnit (laurentPolynomialCircleValue (f t) z))
        (d : ℕ) (hd : ∀ t k, (d : ℤ) < k → (f t).coeff k = 0)
        (g : I → WienerLoop (Matrix (Fin n) (Fin n) A))
        (hgf : ∀ t, g t * laurentPolynomialWiener (f t) = 1)
        (hfg : ∀ t, laurentPolynomialWiener (f t) * g t = 1)
        (hcF : ∀ k, Continuous (fun t ↦ (f t).coeff k))
        (hcG : ∀ k, Continuous (fun t ↦ g t k)) :
        let := polynomialCokernel_finite (f 0) (hf 0) (hi 0)
        let := polynomialCokernel_projective (f 0) (hf 0) (hi 0)
        let := polynomialCokernel_finite (f 1) (hf 1) (hi 1)
        let := polynomialCokernel_projective (f 1) (hf 1) (hi 1)
        projectiveModuleKZeroClass A (PolynomialCokernel (f 0) (hf 0)) =
          projectiveModuleKZeroClass A (PolynomialCokernel (f 1) (hf 1)) := by
      classical
      let T (t : I) : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
        polynomialMultiplier (f t) (hf t)
      let S (t : I) : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
        positiveWienerToeplitz (g t)
      let E (t : I) : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
        LinearMap.id - (T t).comp (S t)
      have hST (t : I) (x : PositiveWienerModule A n) : S t (T t x) = x :=
        DFunLike.congr_fun (polynomialMultiplier_leftInverse (f t) (hf t) (g t) (hgf t)) x
      have hET (t : I) (x : PositiveWienerModule A n) : E t (T t x) = 0 := by
        change T t x - T t (S t (T t x)) = 0
        rw [hST, sub_self]
      have hEE (t : I) (x : PositiveWienerModule A n) : E t (E t x) = E t x := by
        change E t (x - T t (S t x)) = E t x
        rw [map_sub, hET, sub_zero]
      have hsingle (b : WienerLoop (Matrix (Fin n) (Fin n) A))
          (j k : ℕ) (v : Fin n → A) :
          positiveWienerToeplitz b (lp.single 1 j v) k = (b ((k : ℤ) - j)).mulVec v := by
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
        let T : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
          polynomialMultiplier f hf
        let S : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
          positiveWienerToeplitz g
        let E : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
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
              rw [polynomialMultiplier_coeff]
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
        let V : PositiveWienerModule A n →L[A] (Fin n → A) :=
          lp.evalCLM A (fun _ : ℕ ↦ Fin n → A) 1 k
        have hcomp : V.comp ((positiveWienerToeplitzContinuous (A := A) (n := n)
            (laurentPolynomialWiener f)).comp
              (positiveWienerToeplitzContinuous (A := A) (n := n) g)) =
            V := by
          apply lp.ext_continuousLinearMap (by simp)
          intro j
          ext v : 1
          exact htail_single k hk j v
        have heq : T (S x) k = x k := DFunLike.congr_fun hcomp x
        change x k - T (S x) k = 0
        exact sub_eq_zero.mpr heq.symm
      let C : PositiveWienerModule A n →ₗ[A] (Fin d → Fin n → A) :=
        LinearMap.pi fun j : Fin d ↦ lp.evalₗ (fun _ : ℕ ↦ Fin n → A) 1 (j : ℕ)
      let J := lowPolynomialEmbedding A n d
      have hJC (t : I) (x : PositiveWienerModule A n) : J (C (E t x)) = E t x := by
        apply lp.ext
        funext k
        simp only [J, lowPolynomialEmbedding, LinearMap.sum_apply, LinearMap.comp_apply,
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
      let e : (Fin d → Fin n → A) ≃ₗ[A] (Fin (d * n) → A) :=
        { toFun v i := v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
          invFun v j i := v (finProdFinEquiv (j, i))
          left_inv v := by funext j i; simp
          right_inv v := by
            funext i
            change v (finProdFinEquiv (finProdFinEquiv.symm i)) = v i
            rw [Equiv.apply_symm_apply]
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      let L (t : I) : (Fin (d * n) → A) →ₗ[A] (Fin (d * n) → A) :=
        e.toLinearMap.comp (C.comp ((E t).comp (J.comp e.symm.toLinearMap)))
      let P (t : I) : Matrix (Fin (d * n)) (Fin (d * n)) A := LinearMap.toMatrix' (L t)
      have hL (t : I) (v : Fin (d * n) → A) :
          L t v = e (C (E t (J (e.symm v)))) := rfl
      have hP (t : I) : P t * P t = P t := by
        change LinearMap.toMatrix' (L t) * LinearMap.toMatrix' (L t) = _
        rw [← LinearMap.toMatrix'_comp]
        change LinearMap.toMatrix' (L t ∘ₗ L t) = LinearMap.toMatrix' (L t)
        apply congrArg (LinearMap.toMatrix' :
          ((Fin (d * n) → A) →ₗ[A] (Fin (d * n) → A)) → _)
        apply LinearMap.ext
        intro v
        change e (C (E t (J (e.symm (e (C (E t (J (e.symm v))))))))) =
          e (C (E t (J (e.symm v))))
        rw [e.symm_apply_apply, hJC, hEE]
      -- Every finite projector entry depends on only finitely many original coefficients.
      have hSJ (t : I) (v : Fin d → Fin n → A) (k : ℕ) :
          S t (J v) k = ∑ j : Fin d, (g t ((k : ℤ) - j)).mulVec (v j) := by
        simp only [J, lowPolynomialEmbedding, LinearMap.sum_apply, LinearMap.comp_apply,
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
        simp only [T, polynomialMultiplier_coeff, hSJ, Matrix.mulVec, dotProduct,
          Finset.sum_apply]
        fun_prop
      -- Each actual quotient is the image of this same finite projector, not a chosen model.
      let p (t : I) : IdempotentMatrix A := ⟨d * n, P t, hP t⟩
      have hquot (t : I) (x : PositiveWienerModule A n) :
          polynomialCokernelMk (f t) (hf t) (E t x) =
            polynomialCokernelMk (f t) (hf t) x := by
        let Q := polynomialCokernelMk (f t) (hf t)
        have hz : Q (T t (S t x)) = 0 := by
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          exact ⟨S t x, rfl⟩
        change Q (x - T t (S t x)) = Q x
        rw [map_sub, hz, sub_zero]
      have hmodel (t : I) : Nonempty ((p t).image ≃ₗ[A] PolynomialCokernel (f t) (hf t)) := by
        let Q := polynomialCokernelMk (f t) (hf t)
        let R : (Fin (d * n) → A) →ₗ[A] PolynomialCokernel (f t) (hf t) :=
          Q.comp (J.comp e.symm.toLinearMap)
        let K : PositiveWienerModule A n →ₗ[A] (Fin (d * n) → A) :=
          e.toLinearMap.comp (C.comp (E t))
        have hker : LinearMap.range (T t) ≤ LinearMap.ker K := by
          rintro x ⟨y, rfl⟩
          change e (C (E t (T t y))) = 0
          rw [hET, map_zero, map_zero]
        let s : PolynomialCokernel (f t) (hf t) →ₗ[A] (Fin (d * n) → A) :=
          (LinearMap.range (T t)).liftQ K hker
        have hsR (v : Fin (d * n) → A) : s (R v) = (P t).mulVec v := by
          exact (LinearMap.toMatrix'_mulVec (L t) v).symm
        have hRs (q : PolynomialCokernel (f t) (hf t)) : R (s q) = q := by
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
          let := polynomialCokernel_finite (f t) (hf t) (hi t)
          let := polynomialCokernel_projective (f t) (hf t) (hi t)
          projectiveModuleKZeroClass A (PolynomialCokernel (f t) (hf t)) = kZeroClass A (p t) := by
        let := polynomialCokernel_finite (f t) (hf t) (hi t)
        let := polynomialCokernel_projective (f t) (hf t) (hi t)
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
        Nonempty (PolynomialCokernel b hb ≃ₗ[A]
          PolynomialCokernel f hf × PolynomialCokernel g hg) := by
      classical
      let c : (Fin (n + m) → A) ≃ₗ[A] (Fin n → A) × (Fin m → A) :=
        (LinearEquiv.piCongrLeft' A (fun _ : Fin (n + m) ↦ A)
          finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ A A)
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
      let e : PositiveWienerModule A (n + m) ≃ₗ[A]
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
          e (polynomialMultiplier b hb x) =
            (polynomialMultiplier f hf (e x).1, polynomialMultiplier g hg (e x).2) := by
        have hk (k : ℕ) : c (polynomialMultiplier b hb x k) =
            (polynomialMultiplier f hf (e x).1 k, polynomialMultiplier g hg (e x).2 k) := by
          rw [polynomialMultiplier_coeff, map_sum]
          simp_rw [hcoeff, hmatrix]
          apply Prod.ext <;>
            simp only [Prod.fst_sum, Prod.snd_sum, polynomialMultiplier_coeff]
          · rfl
          · rfl
        apply Prod.ext <;> apply lp.ext <;> funext k
        · exact congrArg Prod.fst (hk k)
        · exact congrArg Prod.snd (hk k)
      obtain ⟨q, _⟩ := exists_quotientRange_prod_equiv_of_intertwine e
        (polynomialMultiplier b hb) (polynomialMultiplier f hf) (polynomialMultiplier g hg) hinter
      exact ⟨q⟩
    have shiftIndependent (p : LaurentMatrixLoop A) (k l : ℕ)
        (hk : (p.shift (k : ℤ)).IsPolynomial)
        (hl : (p.shift (l : ℤ)).IsPolynomial) :
        p.shiftedCokernelIndex k hk = p.shiftedCokernelIndex l hl := by
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
            p.shiftedCokernelIndex (k + j) hkj = p.shiftedCokernelIndex k hk := by
        obtain ⟨hkj, ⟨e⟩⟩ := p.nonempty_shiftedCokernel_add_equiv k j hk
        refine ⟨hkj, ?_⟩
        let := p.shiftedCokernel_finite k hk
        let := p.shiftedCokernel_projective k hk
        let := p.shiftedCokernel_finite (k + j) hkj
        let := p.shiftedCokernel_projective (k + j) hkj
        have hc := projectiveModuleKZeroClass_eq_of_linearEquiv e
        dsimp only [LaurentMatrixLoop.shiftedCokernelIndex]
        rw [hc, projectiveModuleKZeroClass_prod, projectiveModuleKZeroClass_free,
          Nat.mul_add, hfree]
        abel
      obtain ⟨hkl, heq₁⟩ := hstep k l hk
      obtain ⟨hlk, heq₂⟩ := hstep l k hl
      have heq₂' : p.shiftedCokernelIndex (k + l) hkl =
          p.shiftedCokernelIndex l hl := by
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
          (blockLaurent p q).shiftedCokernelIndex k hb =
            p.shiftedCokernelIndex k hp + q.shiftedCokernelIndex k hq := by
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
      let := p.shiftedCokernel_finite k hp
      let := p.shiftedCokernel_projective k hp
      let := q.shiftedCokernel_finite k hq
      let := q.shiftedCokernel_projective k hq
      let := (blockLaurent p q).shiftedCokernel_finite k hb
      let := (blockLaurent p q).shiftedCokernel_projective k hb
      let e' : (blockLaurent p q).ShiftedCokernel k hb ≃ₗ[A]
          p.ShiftedCokernel k hp × q.ShiftedCokernel k hq := e
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
      dsimp only [LaurentMatrixLoop.shiftedCokernelIndex]
      rw [heq, projectiveModuleKZeroClass_prod]
      change _ - kZeroClass A (IdempotentMatrix.identity A ((p.size + q.size) * k)) = _
      rw [Nat.add_mul, hfree]
      abel
    let constantLaurent (n : ℕ) : LaurentMatrixLoop A :=
      LaurentMatrixLoop.affine (1 : Matrix (Fin n) (Fin n) A) 0
        (by simp) (by intro z; simp)
    have constantIndex (n k : ℕ)
        (hk : ((constantLaurent n).shift (k : ℤ)).IsPolynomial) :
        (constantLaurent n).shiftedCokernelIndex k hk = 0 := by
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
      have hT (x : PositiveWienerModule A n) : polynomialMultiplier f hp x = x := by
        apply lp.ext
        funext j
        rw [polynomialMultiplier_coeff]
        rw [Finset.sum_eq_single 0]
        · simp [hcoeff]
        · intro a ha hne
          simp only [hcoeff, show (0 : ℤ) ≠ (a : ℤ) by omega, ite_false, Matrix.zero_mulVec]
        · simp
      let := p.shiftedCokernel_finite 0 hp
      let := p.shiftedCokernel_projective 0 hp
      have hzero (q : PolynomialCokernel f hp) : q = 0 := by
        obtain ⟨x, rfl⟩ := (LinearMap.range (polynomialMultiplier f hp)).mkQ_surjective q
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hT x⟩
      let e : PolynomialCokernel f hp ≃ₗ[A] (Fin 0 → A) :=
        LinearEquiv.ofBijective 0 ⟨fun x y _ ↦ (hzero x).trans (hzero y).symm,
          fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
      let e' : p.ShiftedCokernel 0 hp ≃ₗ[A] (Fin 0 → A) := e
      have hclass := projectiveModuleKZeroClass_eq_of_linearEquiv e'
      have hbase : p.shiftedCokernelIndex 0 hp = 0 := by
        dsimp only [LaurentMatrixLoop.shiftedCokernelIndex]
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
        (hi : ∀ z, IsUnit (laurentPolynomialCircleValue f z))
        (hj : ∀ z, IsUnit (laurentPolynomialCircleValue g z))
        (heq : g = cast (congrArg
          (fun d : ℕ ↦ LaurentPolynomial (Matrix (Fin d) (Fin d) A)) h) f) :
        let := polynomialCokernel_finite f hf hi
        let := polynomialCokernel_projective f hf hi
        let := polynomialCokernel_finite g hg hj
        let := polynomialCokernel_projective g hg hj
        projectiveModuleKZeroClass A (PolynomialCokernel g hg) =
          projectiveModuleKZeroClass A (PolynomialCokernel f hf) := by
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
    have hclasses := familyClass_eq f hf hi d hd g hgf hfg hfcCont hgc
    -- Build the same original identity stabilizations and their exact quotient decompositions.
    have hconst (m : ℕ) : ((constantLaurent m).shift (K : ℤ)).IsPolynomial := by
      intro j hj
      change (LaurentPolynomial.T (K : ℤ) *
        (LaurentPolynomial.C (1 : Matrix (Fin m) (Fin m) A) +
          LaurentPolynomial.C 0 * LaurentPolynomial.T 1)).coeff j = 0
      simp only [map_zero, zero_mul, add_zero, map_one, mul_one]
      simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
        show (K : ℤ) ≠ j by omega, ite_false]
    obtain ⟨hpK, _⟩ := p.nonempty_shiftedCokernel_add_equiv k (l + R) hk
    obtain ⟨hqK', _⟩ := q.nonempty_shiftedCokernel_add_equiv l (k + R) hl
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
    let := polynomialCokernel_finite (f 0) (hf 0) (hi 0)
    let := polynomialCokernel_projective (f 0) (hf 0) (hi 0)
    let := polynomialCokernel_finite (f 1) (hf 1) (hi 1)
    let := polynomialCokernel_projective (f 1) (hf 1) (hi 1)
    let := P.shiftedCokernel_finite K hPK
    let := P.shiftedCokernel_projective K hPK
    let := Q.shiftedCokernel_finite K hQK
    let := Q.shiftedCokernel_projective K hQK
    have h₀ := castClass hab (P.shift (K : ℤ)).polynomial (f 0) hPK (hf 0)
      (P.shift (K : ℤ)).invertible (hi 0) he₀
    have h₁ := castClass rfl (Q.shift (K : ℤ)).polynomial (f 1) hQK (hf 1)
      (Q.shift (K : ℤ)).invertible (hi 1) he₁
    have heq : P.shiftedCokernelIndex K hPK = Q.shiftedCokernelIndex K hQK := by
      dsimp only [LaurentMatrixLoop.shiftedCokernelIndex]
      have hmodule : projectiveModuleKZeroClass A (P.ShiftedCokernel K hPK) =
          projectiveModuleKZeroClass A (Q.ShiftedCokernel K hQK) :=
        h₀.symm.trans (hclasses.trans h₁)
      apply congrArg₂ (fun x y : KZero A ↦ x - y) hmodule
      exact congrArg (fun n ↦ kZeroClass A (IdempotentMatrix.identity A (n * K))) hab
    have hPi : P.shiftedCokernelIndex K hPK = p.shiftedCokernelIndex K hpK := by
      rw [hPindex, constantIndex, add_zero]
    have hQi : Q.shiftedCokernelIndex K hQK = q.shiftedCokernelIndex K hqK := by
      rw [hQindex, constantIndex, add_zero]
    exact (shiftIndependent p k K hk hpK).trans
      (hPi.symm.trans (heq.trans (hQi.trans (shiftIndependent q K l hqK hl))))

/-- The cokernel index with a chosen admissible nonnegative shift.
Only the support-clearing part of the existing polynomial-difference lemma is used. -/
def cokernelIndex (p : LaurentMatrixLoop A) : KZero A :=
  p.shiftedCokernelIndex p.exists_polynomial_difference.choose
    p.exists_polynomial_difference.choose_spec.1

end LaurentMatrixLoop

/-- The corrected cokernel construction descends through the actual Laurent homotopy quotient. -/
def laurentLoopCokernelIndex : StableLaurentLoopClass A → KZero A :=
  Quotient.lift LaurentMatrixLoop.cokernelIndex (fun p q h ↦
    p.shiftedCokernelIndex_eq_of_stablyHomotopic q _ _ _ _ h)

/-- The same cokernel index on continuous stable classes, through the specified comparison. -/
def stableLoopCokernelIndex (x : StableMatrixLoopClass A) : KZero A :=
  laurentLoopCokernelIndex (stableLaurentLoopEquiv.symm x)

open scoped Matrix Matrix.Norms.Operator unitInterval Topology in
set_option maxHeartbeats 800000 in

/-- KA III.1.19: the actual corrected cokernel index is additive for stable loop sum. -/
theorem stableLoopCokernelIndex_additive :
    stableLoopCokernelIndex (0 : StableMatrixLoopClass A) = 0 ∧
      ∀ x y : StableMatrixLoopClass A,
        stableLoopCokernelIndex (x + y) =
          stableLoopCokernelIndex x + stableLoopCokernelIndex y := by
  /- Stage 1: choose Laurent representatives and a common admissible shift.
  The shifted block sum acts on the direct sum of the two positive coefficient
  modules. Its actual quotient is the product of their cokernels. The free rank
  correction splits in exactly the same way. This gives additivity for the existing
  block-sum operation. Equivalently, KA uses the split exact sequence of cokernels
  for two injective polynomial multipliers to treat pointwise multiplication.
  Stage 2: the identity loop has corrected cokernel class zero. Apply the preceding
  shift and stable-homotopy invariance theorem to remove choices of representatives.
  The concrete Laurent comparison has these representatives as its values, so the
  descended function satisfies both displayed laws on the continuous stable group. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    have shiftIndependent (p : LaurentMatrixLoop A) (k l : ℕ)
        (hk : (p.shift (k : ℤ)).IsPolynomial)
        (hl : (p.shift (l : ℤ)).IsPolynomial) :
        p.shiftedCokernelIndex k hk = p.shiftedCokernelIndex l hl :=
      p.shiftedCokernelIndex_eq_of_stablyHomotopic p k l hk hl
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
        Nonempty (PolynomialCokernel b hb ≃ₗ[A]
          PolynomialCokernel f hf × PolynomialCokernel g hg) := by
      classical
      let c : (Fin (n + m) → A) ≃ₗ[A] (Fin n → A) × (Fin m → A) :=
        (LinearEquiv.piCongrLeft' A (fun _ : Fin (n + m) ↦ A)
          finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ A A)
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
      let e : PositiveWienerModule A (n + m) ≃ₗ[A]
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
          e (polynomialMultiplier b hb x) =
            (polynomialMultiplier f hf (e x).1, polynomialMultiplier g hg (e x).2) := by
        have hk (k : ℕ) : c (polynomialMultiplier b hb x k) =
            (polynomialMultiplier f hf (e x).1 k, polynomialMultiplier g hg (e x).2 k) := by
          rw [polynomialMultiplier_coeff, map_sum]
          simp_rw [hcoeff, hmatrix]
          apply Prod.ext <;>
            simp only [Prod.fst_sum, Prod.snd_sum, polynomialMultiplier_coeff]
          · rfl
          · rfl
        apply Prod.ext <;> apply lp.ext <;> funext k
        · exact congrArg Prod.fst (hk k)
        · exact congrArg Prod.snd (hk k)
      obtain ⟨q, _⟩ := exists_quotientRange_prod_equiv_of_intertwine e
        (polynomialMultiplier b hb) (polynomialMultiplier f hf) (polynomialMultiplier g hg) hinter
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
          (blockLaurent p q).shiftedCokernelIndex k hb =
            p.shiftedCokernelIndex k hp + q.shiftedCokernelIndex k hq := by
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
      let := p.shiftedCokernel_finite k hp
      let := p.shiftedCokernel_projective k hp
      let := q.shiftedCokernel_finite k hq
      let := q.shiftedCokernel_projective k hq
      let := (blockLaurent p q).shiftedCokernel_finite k hb
      let := (blockLaurent p q).shiftedCokernel_projective k hb
      let e' : (blockLaurent p q).ShiftedCokernel k hb ≃ₗ[A]
          p.ShiftedCokernel k hp × q.ShiftedCokernel k hq := e
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
      dsimp only [LaurentMatrixLoop.shiftedCokernelIndex]
      rw [heq, projectiveModuleKZeroClass_prod]
      change _ - kZeroClass A (IdempotentMatrix.identity A ((p.size + q.size) * k)) = _
      rw [Nat.add_mul, hfree]
      abel
    let constantLaurent (n : ℕ) : LaurentMatrixLoop A :=
      LaurentMatrixLoop.affine (1 : Matrix (Fin n) (Fin n) A) 0
        (by simp) (by intro z; simp)
    have constantIndex (n k : ℕ)
        (hk : ((constantLaurent n).shift (k : ℤ)).IsPolynomial) :
        (constantLaurent n).shiftedCokernelIndex k hk = 0 := by
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
      have hT (x : PositiveWienerModule A n) : polynomialMultiplier f hp x = x := by
        apply lp.ext
        funext j
        rw [polynomialMultiplier_coeff]
        rw [Finset.sum_eq_single 0]
        · simp [hcoeff]
        · intro a ha hne
          simp only [hcoeff, show (0 : ℤ) ≠ (a : ℤ) by omega, ite_false, Matrix.zero_mulVec]
        · simp
      let := p.shiftedCokernel_finite 0 hp
      let := p.shiftedCokernel_projective 0 hp
      have hzero (q : PolynomialCokernel f hp) : q = 0 := by
        obtain ⟨x, rfl⟩ := (LinearMap.range (polynomialMultiplier f hp)).mkQ_surjective q
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hT x⟩
      let e : PolynomialCokernel f hp ≃ₗ[A] (Fin 0 → A) :=
        LinearEquiv.ofBijective 0 ⟨fun x y _ ↦ (hzero x).trans (hzero y).symm,
          fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
      let e' : p.ShiftedCokernel 0 hp ≃ₗ[A] (Fin 0 → A) := e
      have hclass := projectiveModuleKZeroClass_eq_of_linearEquiv e'
      have hbase : p.shiftedCokernelIndex 0 hp = 0 := by
        dsimp only [LaurentMatrixLoop.shiftedCokernelIndex]
        rw [hclass, projectiveModuleKZeroClass_free]
        simp
      exact (shiftIndependent p k 0 hk hp).trans hbase
    -- The Laurent comparison returns the same original representative and chosen index.
    have hindex (p : LaurentMatrixLoop A) (k : ℕ)
        (hk : (p.shift (k : ℤ)).IsPolynomial) :
        stableLoopCokernelIndex p.stableClass = p.shiftedCokernelIndex k hk := by
      have hc : stableLaurentLoopEquiv (stableLaurentLoopClass p) = p.stableClass := rfl
      change laurentLoopCokernelIndex (stableLaurentLoopEquiv.symm p.stableClass) = _
      rw [← hc, Equiv.symm_apply_apply]
      change p.cokernelIndex = _
      exact p.shiftedCokernelIndex_eq_of_stablyHomotopic p _ k _ hk
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
        _ = (constantLaurent 0).shiftedCokernelIndex 0 hp := hindex _ 0 hp
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
      obtain ⟨hpK, _⟩ := p.nonempty_shiftedCokernel_add_equiv kp kq hp
      obtain ⟨hqK', _⟩ := q.nonempty_shiftedCokernel_add_equiv kq kp hq
      have hqK : (q.shift ((kp + kq : ℕ) : ℤ)).IsPolynomial := by
        simpa only [Nat.add_comm kq kp] using hqK'
      obtain ⟨hb, hbi⟩ := blockIndex p q (kp + kq) hpK hqK
      calc
        stableLoopCokernelIndex (p.stableClass + q.stableClass) =
            stableLoopCokernelIndex (blockLaurent p q).stableClass :=
          congrArg stableLoopCokernelIndex (hblockClass p q).symm
        _ = (blockLaurent p q).shiftedCokernelIndex (kp + kq) hb := hindex _ _ hb
        _ = p.shiftedCokernelIndex (kp + kq) hpK +
            q.shiftedCokernelIndex (kp + kq) hqK := hbi
        _ = stableLoopCokernelIndex p.stableClass + stableLoopCokernelIndex q.stableClass :=
          congrArg₂ (fun a b : KZero A ↦ a + b) (hindex p _ hpK).symm (hindex q _ hqK).symm

/-- The Bott inverse homomorphism with the specified shifted-cokernel values. -/
def stableLoopBottInverse (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] : StableMatrixLoopClass A →+ KZero A where
  toFun := stableLoopCokernelIndex
  map_zero' := stableLoopCokernelIndex_additive.1
  map_add' := stableLoopCokernelIndex_additive.2

/-- The inverse evaluates to the same corrected cokernel at every admissible shift. -/
theorem stableLoopBottInverse_laurent (p : LaurentMatrixLoop A) (k : ℕ)
    (hk : (p.shift (k : ℤ)).IsPolynomial) :
    stableLoopBottInverse A p.stableClass = p.shiftedCokernelIndex k hk := by
  /- The concrete comparison sends the Laurent class of p to p.stableClass.
  Its inverse therefore returns that same quotient class. Unfold the two quotient
  constructions, then use shift independence with the reflexive stable homotopy
  of p to replace the chosen support-clearing shift by the specified k. -/
  -- The inverse comparison returns exactly the original Laurent quotient representative.
  have hc : stableLaurentLoopEquiv (stableLaurentLoopClass p) = p.stableClass := rfl
  change laurentLoopCokernelIndex (stableLaurentLoopEquiv.symm p.stableClass) = _
  rw [← hc, Equiv.symm_apply_apply]
  change p.cokernelIndex = _
  -- The already proved invariant removes the chosen support-clearing shift.
  exact p.shiftedCokernelIndex_eq_of_stablyHomotopic p _ k _ hk
    ((LaurentMatrixLoop.stableSetoid (A := A)).iseqv.refl p)

/-- KA III.1.20: the actual cokernel homomorphism is left inverse to the actual Bott map. -/
theorem stableLoopBottInverse_left_inverse :
    Function.LeftInverse (stableLoopBottInverse A) (kZeroBottLoop A) := by
  /- Stage 1: for a specified idempotent p, take its actual Laurent loop
  (1-p)+zp. At shift zero its multiplier cokernel identifies with p.image by
  sending a series x to p*x₀. The complementary summand is acted on identically,
  and multiplication by z on the p-summand leaves precisely its constant term.
  Stage 2: the free correction at k=0 vanishes. The class of this cokernel is
  therefore the original projective generator, by the image-class comparison.
  The Laurent representative has the same positive orientation as bottMatrixLoop.
  Stage 3: both maps are group homomorphisms and the specified idempotent classes
  generate the actual K₀ quotient. Extend the equality from those generators to
  every virtual projective class. No inverse or injectivity is assumed in advance. -/
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
    let := (bottLaurentLoop p).shiftedCokernel_finite 0 hp
    let := (bottLaurentLoop p).shiftedCokernel_projective 0 hp
    let := p.finite_image
    let := p.projective_image
    have hc := projectiveModuleKZeroClass_eq_of_linearEquiv e
    dsimp only [LaurentMatrixLoop.shiftedCokernelIndex]
    rw [hc, projectiveModuleKZeroClass_image, Nat.mul_zero, hzero, sub_zero]
  -- Generator equality extends through precisely the existing K-zero universal property.
  have hhom : (stableLoopBottInverse A).comp (kZeroBottLoop A) =
      AddMonoidHom.id (KZero A) :=
    (kZero_universal_property (fun p : IdempotentMatrix A ↦ kZeroClass A p)
      (fun p q h ↦ kZeroClass_eq_of_isEquivalent p q h)
      (fun p q ↦ kZeroClass_blockSum p q)).unique hgenerator (fun _ ↦ rfl)
  intro x
  exact DFunLike.congr_fun hhom x

/-- The algebraic loop form of complex Bott periodicity in the current commutative model. -/
theorem kZeroBottLoop_bijective : Function.Bijective (kZeroBottLoop A) := by
  /- The constructed cokernel homomorphism is a left inverse, hence the specified
  Bott map is injective. Combine this with the proved surjectivity theorem
  from polynomial reduction and affine factor contraction. The geometric relative
  K-group and Bott-line comparisons are separate statements and are not used here. -/
  -- The specified cokernel map provides injectivity; the independent reduction gives surjectivity.
  exact ⟨(stableLoopBottInverse_left_inverse (A := A)).injective, kZeroBottLoop_surjective⟩

/-- The additive equivalence with the existing Bott map and the actual cokernel inverse. -/
def kZeroBottLoopEquiv (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] : KZero A ≃+ StableMatrixLoopClass A where
  toFun := kZeroBottLoop A
  invFun := stableLoopBottInverse A
  left_inv := stableLoopBottInverse_left_inverse
  right_inv := by
    intro x
    obtain ⟨y, rfl⟩ := kZeroBottLoop_surjective x
    exact congrArg (kZeroBottLoop A) (stableLoopBottInverse_left_inverse y)
  map_add' := map_add (kZeroBottLoop A)

end AtiyahSinger

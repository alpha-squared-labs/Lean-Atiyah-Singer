/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LaurentWiener
public import AtiyahSinger.Analysis.RightWienerModule
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Polynomial Wiener cokernels over a possibly noncommutative Banach algebra

Public module ID: M0929.

UL04: matrices act on the left of the original positive Wiener column module,
while its coefficient scalars act on the right. The latter action is represented
as a left module over Aᵐᵒᵖ. Neither the coefficients nor the matrix factors are
commuted. The actual cokernel is the quotient by this same multiplier's range.

The specified bilateral inverse g is retained in both inverse equations.
The equation gf=1 gives the Toeplitz left inverse; fg=1 gives the exact defect
identity I-TS=P₊M_fP₋M_gi. For degree at most d its image has degrees below d,
so the actual quotient is a retract of the first d column coefficients.
This finite-bandwidth argument repairs the printed splitting diagram without
asserting that g or a Neumann inverse has nonnegative support.

Sources: Karoubi, K-Theory, II.3.10, p.74, for right modules over general
Banach algebras; III.1.17--1.18, pp.117--119, for the polynomial multiplier
and its cokernel. The exact defect argument is a supplement implemented below.
The statement includes d=0 and n=0.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

namespace RightWiener

universe u

open scoped Matrix.Norms.Operator

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
variable {n : ℕ}

local instance : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → A))

/-- The specified polynomial acting on the original positive columns as a right-linear map. -/
def polynomialMultiplier (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (_hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) :
    PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
  toeplitz (laurentPolynomialWiener f)

/-- The right-linear multiplier retains the usual ordered matrix-convolution coefficients. -/
theorem polynomialMultiplier_coeff (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) (x : PositiveWienerModule A n) (k : ℕ) :
    polynomialMultiplier f hf x k =
      ∑ j ∈ Finset.range (k + 1), (f.coeff (j : ℤ)).mulVec (x (k - j)) := by
  /- The Wiener inclusion has the same coefficients as f. Terms of the
  Toeplitz sum whose input degree exceeds k vanish by hf. Reindex the
  remaining finite sum by its polynomial degree. Every matrix coefficient
  remains to the left of the corresponding column entry; no commutation,
  transpose, or reversal of either factor is used. -/
  classical
  change (∑' j : ℕ, (laurentPolynomialWiener f ((k : ℤ) - j)).mulVec (x j)) = _
  simp_rw [laurentPolynomialWiener_coeff]
  -- Negative polynomial degrees remove every input index larger than k.
  calc
    (∑' j : ℕ, (f.coeff ((k : ℤ) - j)).mulVec (x j)) =
        ∑ j ∈ Finset.range (k + 1), (f.coeff ((k : ℤ) - j)).mulVec (x j) := by
      apply tsum_eq_sum
      intro j hj
      rw [hf _ (by simp only [Finset.mem_range] at hj; omega), Matrix.zero_mulVec]
    _ = ∑ j ∈ Finset.range (k + 1), (f.coeff (j : ℤ)).mulVec (x (k - j)) := by
      -- Reflect the finite input range to use the original polynomial degree.
      refine Finset.sum_bij (fun j _ ↦ k - j) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro i hi j hj hij
        simp only [Finset.mem_range] at hi hj
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        exact ⟨k - j, by simp only [Finset.mem_range]; omega, by omega⟩
      · intro j hj
        simp only [Finset.mem_range] at hj
        have hcast : ((k - j : ℕ) : ℤ) = (k : ℤ) - j := by omega
        rw [hcast, show k - (k - j) = j by omega]

/-- The actual range quotient as a right A-module, expressed as a left Aᵐᵒᵖ-module. -/
abbrev PolynomialCokernel (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) : Type u :=
  PositiveWienerModule A n ⧸ LinearMap.range (polynomialMultiplier f hf)

/-- The canonical quotient map for the original polynomial multiplier. -/
def polynomialCokernelMk (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) :
    PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PolynomialCokernel f hf :=
  (LinearMap.range (polynomialMultiplier f hf)).mkQ

/-- The specified left bilateral inverse yields the actual positive Toeplitz left inverse. -/
theorem polynomialMultiplier_leftInverse
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hgf : g * laurentPolynomialWiener f = 1) :
    (toeplitz g).comp (polynomialMultiplier f hf) = LinearMap.id := by
  /- Stage 1: extend a positive input by zero to bilateral coefficients.
  Since f has nonnegative support, its product with that input still has
  nonnegative support. The intermediate positive projection loses nothing.
  Stage 2: absolute convergence reassociates the ordered product g(fx)
  as (gf)x. Apply the given hgf to obtain the original input. Only this
  left inverse equation is needed; g may have infinitely many negative terms. -/
  classical
  -- First compute on one original coefficient vector; no infinite input is truncated.
  have hsingle (b : WienerLoop (Matrix (Fin n) (Fin n) A))
      (j k : ℕ) (v : Fin n → A) :
      toeplitz b (lp.single 1 j v) k = (b ((k : ℤ) - j)).mulVec v := by
    change (∑' l : ℕ, (b ((k : ℤ) - l)).mulVec
      ((lp.single 1 j v : PositiveWienerModule A n) l)) = _
    simp only [lp.coeFn_single, Pi.single_apply, apply_ite, Matrix.mulVec_zero]
    simp
  -- The polynomial factor makes this actual convolution coefficient a finite sum.
  have hproduct (p : ℤ) (v : Fin n → A) :
      ((g * laurentPolynomialWiener f) p).mulVec v =
        ∑' a : ℤ, (g (p - a)).mulVec ((f.coeff a).mulVec v) := by
    change ((∑' a : ℤ, g a * laurentPolynomialWiener f (p - a))).mulVec v = _
    rw [← (Equiv.subLeft p).tsum_eq
      (fun a : ℤ ↦ g a * laurentPolynomialWiener f (p - a))]
    simp only [Equiv.subLeft_apply, sub_sub_cancel, laurentPolynomialWiener_coeff]
    have hmat : (∑' a : ℤ, g (p - a) * f.coeff a) =
        ∑ a ∈ f.coeff.support, g (p - a) * f.coeff a := by
      apply tsum_eq_sum
      intro a ha
      simp [Finsupp.notMem_support_iff.mp ha]
    have hvec : (∑' a : ℤ, (g (p - a)).mulVec ((f.coeff a).mulVec v)) =
        ∑ a ∈ f.coeff.support, (g (p - a)).mulVec ((f.coeff a).mulVec v) := by
      apply tsum_eq_sum
      intro a ha
      simp [Finsupp.notMem_support_iff.mp ha]
    rw [hmat, hvec, Matrix.sum_mulVec]
    apply Finset.sum_congr rfl
    intro a ha
    exact (Matrix.mulVec_mulVec v (g (p - a)) (f.coeff a)).symm
  have hrecover (j : ℕ) (v : Fin n → A) :
      toeplitz g (polynomialMultiplier f hf (lp.single 1 j v)) = lp.single 1 j v := by
    apply lp.ext
    funext k
    have hfirst (l : ℕ) : polynomialMultiplier f hf (lp.single 1 j v) l =
        (f.coeff ((l : ℤ) - j)).mulVec v := by
      simpa only [polynomialMultiplier, laurentPolynomialWiener_coeff] using
        hsingle (laurentPolynomialWiener f) j l v
    change (∑' l : ℕ,
      (g ((k : ℤ) - l)).mulVec (polynomialMultiplier f hf (lp.single 1 j v) l)) = _
    simp_rw [hfirst]
    -- Nonnegative polynomial support justifies extending this sum to all integer degrees.
    have hinj : Function.Injective (fun l : ℕ ↦ (l : ℤ) - j) := by
      intro l l' h
      dsimp at h
      omega
    have hs : Function.support
        (fun a : ℤ ↦ (g ((k : ℤ) - j - a)).mulVec ((f.coeff a).mulVec v)) ⊆
        Set.range (fun l : ℕ ↦ (l : ℤ) - j) := by
      intro a ha
      have ha0 : 0 ≤ a := by
        by_contra h
        simp [Function.mem_support, hf a (by omega)] at ha
      refine ⟨(a + j).toNat, ?_⟩
      dsimp
      omega
    calc
      (∑' l : ℕ, (g ((k : ℤ) - l)).mulVec
          ((f.coeff ((l : ℤ) - j)).mulVec v)) =
          ∑' a : ℤ, (g ((k : ℤ) - j - a)).mulVec ((f.coeff a).mulVec v) := by
        simpa only [show ∀ l : ℕ, (k : ℤ) - j - ((l : ℤ) - j) = k - l by
          intro l; omega] using hinj.tsum_eq hs
      _ = ((g * laurentPolynomialWiener f) ((k : ℤ) - j)).mulVec v :=
        (hproduct ((k : ℤ) - j) v).symm
      _ = (lp.single 1 j v : PositiveWienerModule A n) k := by
        rw [hgf]
        change (lp.single (E := fun _ : ℤ ↦ Matrix (Fin n) (Fin n) A)
          1 (0 : ℤ) 1 ((k : ℤ) - j)).mulVec v = _
        by_cases hkj : k = j
        · subst k
          simp
        · have hdiff : (k : ℤ) - j ≠ 0 := by omega
          simp [hdiff, hkj]
  -- Finite coefficient sums converge in the original ℓ¹ norm, so the bounded maps agree.
  have hcontinuous : (toeplitzContinuous g).comp
      (toeplitzContinuous (laurentPolynomialWiener f)) =
      ContinuousLinearMap.id Aᵐᵒᵖ (PositiveWienerModule A n) := by
    apply lp.ext_continuousLinearMap (by simp)
    intro j
    ext v : 1
    exact hrecover j v
  exact congrArg ContinuousLinearMap.toLinearMap hcontinuous

/-- A specified left bilateral inverse makes the polynomial multiplier injective. -/
theorem polynomialMultiplier_injective
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hgf : g * laurentPolynomialWiener f = 1) :
    Function.Injective (polynomialMultiplier f hf) := by
  /- Apply the preceding left-inverse identity to an equality of multiplier
  outputs. The same toeplitz g recovers both original inputs. No right
  inverse, commutativity or support condition on g is required. -/
  have hleft (x : PositiveWienerModule A n) :
      toeplitz g (polynomialMultiplier f hf x) = x :=
    DFunLike.congr_fun (polynomialMultiplier_leftInverse f hf g hgf) x
  intro x y hxy
  calc
    x = toeplitz g (polynomialMultiplier f hf x) := (hleft x).symm
    _ = toeplitz g (polynomialMultiplier f hf y) := congrArg (toeplitz g) hxy
    _ = y := hleft y

/-- The multiplier range is closed for the original positive Wiener norm. -/
theorem polynomialMultiplier_isClosed_range
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hgf : g * laurentPolynomialWiener f = 1) :
    IsClosed (Set.range (polynomialMultiplier f hf)) := by
  /- Bundle the same T=M_f and S=P₊M_gi using toeplitzContinuous. The
  left-inverse identity ST=I implies that TS is a continuous projection
  onto the actual range of T. That range is therefore the closed kernel
  of I-TS in the original norm topology, before taking the algebraic quotient. -/
  let T : PositiveWienerModule A n →L[Aᵐᵒᵖ] PositiveWienerModule A n :=
    toeplitzContinuous (A := A) (n := n) (laurentPolynomialWiener f)
  let S : PositiveWienerModule A n →L[Aᵐᵒᵖ] PositiveWienerModule A n :=
    toeplitzContinuous (A := A) (n := n) g
  have hleft (x : PositiveWienerModule A n) : S (T x) = x :=
    DFunLike.congr_fun (polynomialMultiplier_leftInverse f hf g hgf) x
  -- The actual range is the fixed set of this same bounded projection.
  have hrange : Set.range (polynomialMultiplier f hf) = {x | T (S x) = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change T (S (T y)) = T y
      rw [hleft]
    · intro hx
      exact ⟨S x, hx⟩
  rw [hrange]
  exact isClosed_eq (T.continuous.comp S.continuous) continuous_id

/-- UL04: the first d columns split-surject onto the actual right-module cokernel. -/
theorem polynomialCokernel_exists_lowDegree_section
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hgf : g * laurentPolynomialWiener f = 1)
    (hfg : laurentPolynomialWiener f * g = 1)
    (d : ℕ) (hd : ∀ k : ℤ, (d : ℤ) < k → f.coeff k = 0) :
    ∃ s : PolynomialCokernel f hf →ₗ[Aᵐᵒᵖ] (Fin d → Fin n → A),
      ((polynomialCokernelMk f hf).comp (lowPolynomialEmbedding A n d)).comp s =
        LinearMap.id := by
  /- Stage 1: use exactly the supplied g. With T=M_f and S=P₊M_gi,
  hgf gives ST=I. Set E=I-TS, so E²=E, ET=0 and [Ex]=[x] in this
  quotient. All these maps are right A-linear by associativity.
  Stage 2: hfg, with its distinct multiplication order, gives
  E=P₊M_fP₋M_gi. A negative input degree multiplied by a polynomial
  supported in degrees 0 through d can only produce nonnegative degrees
  strictly below d. Thus E has exactly the required finite-bandwidth image.
  Stage 3: send [x] to the first d coefficient columns of Ex. ET=0
  makes this well-defined, and associativity makes it right A-linear.
  Embedding these columns returns Ex, whose quotient class is [x].
  For d=0 the defect is zero and so is the quotient; n=0 is also allowed.
  This exact identity refines the truncation/Neumann repair for finite
  polynomials. It never places g or a Neumann inverse in the positive algebra. -/
  classical
  let T : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
    polynomialMultiplier f hf
  let S : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n := toeplitz g
  let E : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] PositiveWienerModule A n :=
    LinearMap.id - T.comp S
  have hST (x : PositiveWienerModule A n) : S (T x) = x :=
    DFunLike.congr_fun (polynomialMultiplier_leftInverse f hf g hgf) x
  have hET (x : PositiveWienerModule A n) : E (T x) = 0 := by
    change T x - T (S (T x)) = 0
    rw [hST, sub_self]
  -- Calculate the opposite product on one coefficient vector, in its original order.
  have hsingle (b : WienerLoop (Matrix (Fin n) (Fin n) A))
      (j k : ℕ) (v : Fin n → A) :
      toeplitz b (lp.single 1 j v) k = (b ((k : ℤ) - j)).mulVec v := by
    change (∑' l : ℕ, (b ((k : ℤ) - l)).mulVec
      ((lp.single 1 j v : PositiveWienerModule A n) l)) = _
    simp only [lp.coeFn_single, Pi.single_apply, apply_ite, Matrix.mulVec_zero]
    simp
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
  -- Boundedness extends the finite-bandwidth identity to every actual ℓ¹ input.
  have htail (k : ℕ) (hk : d ≤ k) (x : PositiveWienerModule A n) : E x k = 0 := by
    let V : PositiveWienerModule A n →L[Aᵐᵒᵖ] (Fin n → A) :=
      lp.evalCLM Aᵐᵒᵖ (fun _ : ℕ ↦ Fin n → A) 1 k
    have hcomp : V.comp ((toeplitzContinuous (A := A) (n := n)
        (laurentPolynomialWiener f)).comp (toeplitzContinuous (A := A) (n := n) g)) =
        V := by
      apply lp.ext_continuousLinearMap (by simp)
      intro j
      ext v : 1
      exact htail_single k hk j v
    have heq : T (S x) k = x k := DFunLike.congr_fun hcomp x
    change x k - T (S x) k = 0
    exact sub_eq_zero.mpr heq.symm
  -- Descend the first d defect coefficients through the original range quotient.
  let C : PositiveWienerModule A n →ₗ[Aᵐᵒᵖ] (Fin d → Fin n → A) :=
    LinearMap.pi fun j : Fin d ↦
      (lp.evalₗ (fun _ : ℕ ↦ Fin n → A) 1 (j : ℕ)).comp E
  have hkernel : LinearMap.range T ≤ LinearMap.ker C := by
    rintro x ⟨y, rfl⟩
    change C (T y) = 0
    ext j i
    change E (T y) (j : ℕ) i = 0
    rw [hET]
    rfl
  let s : PolynomialCokernel f hf →ₗ[Aᵐᵒᵖ] (Fin d → Fin n → A) :=
    (LinearMap.range T).liftQ C hkernel
  have hembed (x : PositiveWienerModule A n) :
      lowPolynomialEmbedding A n d (C x) = E x := by
    apply lp.ext
    funext k
    simp only [lowPolynomialEmbedding, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, lp.lsingle_apply]
    change (∑ j : Fin d,
      lp.single (E := fun _ : ℕ ↦ Fin n → A) 1 (j : ℕ) (E x j)) k = E x k
    rw [lp.coeFn_sum, Finset.sum_apply]
    by_cases hkd : k < d
    · rw [Finset.sum_eq_single (⟨k, hkd⟩ : Fin d)]
      · simp
      · intro j hj hne
        apply lp.single_apply_ne
        intro heq
        exact hne (Fin.ext heq.symm)
      · simp
    · rw [htail k (by omega) x]
      apply Finset.sum_eq_zero
      intro j hj
      apply lp.single_apply_ne
      have hjd := j.isLt
      omega
  -- The defect and the original vector represent exactly the same quotient element.
  let Q := polynomialCokernelMk f hf
  have hquot (x : PositiveWienerModule A n) : Q (E x) = Q x := by
    have hz : Q (T (S x)) = 0 := by
      change (Submodule.Quotient.mk (T (S x)) : PolynomialCokernel f hf) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨S x, rfl⟩
    change Q (x - T (S x)) = Q x
    rw [map_sub, hz, sub_zero]
  refine ⟨s, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (LinearMap.range T).mkQ_surjective q
  change Q (lowPolynomialEmbedding A n d (C x)) = Q x
  rw [hembed, hquot]

/-- The specified invertible polynomial has a finitely generated right-module cokernel. -/
theorem polynomialCokernel_finite
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hgf : g * laurentPolynomialWiener f = 1)
    (hfg : laurentPolynomialWiener f * g = 1) :
    Module.Finite Aᵐᵒᵖ (PolynomialCokernel f hf) := by
  /- Choose a natural upper degree bound from the finite support of f.
  Apply the low-degree section theorem to the same g, hgf and hfg.
  Its quotient map is surjective from the finite free right module
  of d columns, so the actual cokernel is finitely generated. The
  identification of right A with the regular left Aᵐᵒᵖ module uses op;
  it does not replace the underlying coefficient sequences. -/
  classical
  let d := f.coeff.support.sup Int.toNat
  have hd (k : ℤ) (hk : (d : ℤ) < k) : f.coeff k = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hbound : k.toNat ≤ d := Finset.le_sup (f := Int.toNat) hmem
    omega
  obtain ⟨s, hs⟩ := polynomialCokernel_exists_lowDegree_section f hf g hgf hfg d hd
  -- Identify the finite coefficient module with the regular free right module.
  let e₀ : Aᵐᵒᵖ ≃ₗ[Aᵐᵒᵖ] A := {
    toFun := MulOpposite.unop
    invFun := MulOpposite.op
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let e : (Fin d → Fin n → Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ] (Fin d → Fin n → A) :=
    LinearEquiv.piCongrRight fun _ ↦ LinearEquiv.piCongrRight fun _ ↦ e₀
  let : Module.Finite Aᵐᵒᵖ (Fin d → Fin n → A) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  -- The original quotient map, rather than an alternate cokernel, is split surjective.
  apply Module.Finite.of_surjective
    ((polynomialCokernelMk f hf).comp (lowPolynomialEmbedding A n d))
  intro q
  exact ⟨s q, DFunLike.congr_fun hs q⟩

/-- The specified invertible polynomial has a projective right-module cokernel. -/
theorem polynomialCokernel_projective
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hgf : g * laurentPolynomialWiener f = 1)
    (hfg : laurentPolynomialWiener f * g = 1) :
    Module.Projective Aᵐᵒᵖ (PolynomialCokernel f hf) := by
  /- With a finite upper degree bound, the same low-degree quotient map
  and its section display this cokernel as a retract of a finite free
  right A-module. Use the regular left Aᵐᵒᵖ interpretation and the
  projectivity-of-retract theorem for these actual maps. No alternate
  quotient, commutative coefficient algebra or positive inverse is chosen. -/
  classical
  let d := f.coeff.support.sup Int.toNat
  have hd (k : ℤ) (hk : (d : ℤ) < k) : f.coeff k = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hbound : k.toNat ≤ d := Finset.le_sup (f := Int.toNat) hmem
    omega
  obtain ⟨s, hs⟩ := polynomialCokernel_exists_lowDegree_section f hf g hgf hfg d hd
  -- Transfer projectivity only; all original coefficient vectors and scalar actions remain.
  let e₀ : Aᵐᵒᵖ ≃ₗ[Aᵐᵒᵖ] A := {
    toFun := MulOpposite.unop
    invFun := MulOpposite.op
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let e : (Fin d → Fin n → Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ] (Fin d → Fin n → A) :=
    LinearEquiv.piCongrRight fun _ ↦ LinearEquiv.piCongrRight fun _ ↦ e₀
  let : Module.Projective Aᵐᵒᵖ (Fin d → Fin n → A) := Module.Projective.of_equiv' e
  exact Module.Projective.of_split s
    ((polynomialCokernelMk f hf).comp (lowPolynomialEmbedding A n d)) hs

end RightWiener

end AtiyahSinger

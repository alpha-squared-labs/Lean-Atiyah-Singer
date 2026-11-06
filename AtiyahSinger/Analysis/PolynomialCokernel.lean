/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LaurentWiener
public import AtiyahSinger.Analysis.WienerModule
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite projective cokernels of polynomial Wiener multipliers

Public module ID: M0857.

For a matrix polynomial invertible on the circle, its multiplier acts on the actual
positive Wiener module. Its cokernel is the quotient by that multiplier's range.
The finite projective conclusion follows from the exact finite-bandwidth defect
projection associated to the bilateral inverse, not from a polynomial inverse.

Sources: Karoubi, K-Theory, III.1.17--1.18, pp.117--119. The defect projection repairs
the printed finite-free splitting diagram by directly constructing a finite free retract
from the exact defect projection for this finite polynomial scope.
Our result holds for every nonnegative polynomial multiplier invertible on the circle.
The extra truncation-size restriction in the printed proof is unnecessary after this
repair. Coefficients are commutative complex Banach algebras, as in WienerModule.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped Matrix.Norms.Operator

variable {A : Type u} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
variable {n : ℕ}

local instance : CompleteSpace (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → A))

/-- Multiplication by the specified matrix polynomial on its positive Wiener module. -/
def polynomialMultiplier (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (_hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) :
    PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
  positiveWienerToeplitz (laurentPolynomialWiener f)

/-- The multiplier has exactly the usual finite polynomial-convolution coefficients. -/
theorem polynomialMultiplier_coeff (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) (x : PositiveWienerModule A n) (k : ℕ) :
    polynomialMultiplier f hf x k =
      ∑ j ∈ Finset.range (k + 1), (f.coeff (j : ℤ)).mulVec (x (k - j)) := by
  /- Stage 1: replace the Wiener inclusion's coefficients by the coefficients
  of the same polynomial f. Terms of the Toeplitz sum with j>k vanish by hf.
  Stage 2: reindex the remaining finite sum by j ↦ k-j. This is the usual
  nonnegative polynomial product, with matrix coefficients acting on the left. -/
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

/-- The actual algebraic cokernel of the polynomial multiplier. -/
abbrev PolynomialCokernel (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) : Type u :=
  PositiveWienerModule A n ⧸ LinearMap.range (polynomialMultiplier f hf)

/-- The canonical quotient map into the specified multiplier cokernel. -/
def polynomialCokernelMk (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0) :
    PositiveWienerModule A n →ₗ[A] PolynomialCokernel f hf :=
  (LinearMap.range (polynomialMultiplier f hf)).mkQ

/-- A bilateral inverse gives the actual positive Toeplitz left inverse.
No nonnegative-support hypothesis is imposed on the inverse series. -/
theorem polynomialMultiplier_leftInverse
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (g : WienerLoop (Matrix (Fin n) (Fin n) A))
    (hgf : g * laurentPolynomialWiener f = 1) :
    (positiveWienerToeplitz g).comp (polynomialMultiplier f hf) = LinearMap.id := by
  /- Stage 1: extend a positive input by zero. Since f has no negative
  coefficients, multiplying by f still has no negative coefficients. Thus the
  intermediate positive projection discards nothing.
  Stage 2: absolute convergence identifies the composite with P₊M_(gf)i.
  The assumed left inverse equation reduces this to P₊i, the identity. -/
  classical
  -- First compute on one original coefficient vector; no infinite input is truncated.
  have hsingle (b : WienerLoop (Matrix (Fin n) (Fin n) A))
      (j k : ℕ) (v : Fin n → A) :
      positiveWienerToeplitz b (lp.single 1 j v) k = (b ((k : ℤ) - j)).mulVec v := by
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
      positiveWienerToeplitz g (polynomialMultiplier f hf (lp.single 1 j v)) = lp.single 1 j v := by
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
  have hcontinuous : (positiveWienerToeplitzContinuous g).comp
      (positiveWienerToeplitzContinuous (laurentPolynomialWiener f)) =
      ContinuousLinearMap.id A (PositiveWienerModule A n) := by
    apply lp.ext_continuousLinearMap (by simp)
    intro j
    ext v : 1
    exact hrecover j v
  exact congrArg ContinuousLinearMap.toLinearMap hcontinuous

/-- Pointwise circle invertibility makes the positive polynomial multiplier injective. -/
theorem polynomialMultiplier_injective
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (hi : ∀ z : Circle, IsUnit (laurentPolynomialCircleValue f z)) :
    Function.Injective (polynomialMultiplier f hf) := by
  /- Stage 1: apply isUnit_of_finiteSupport to the Wiener inclusion of f.
  Its coefficients have the same finite support and its values agree with f.
  Stage 2: use the inverse unit as the single bilateral inverse g in
  polynomialMultiplier_leftInverse. A map with this left inverse is injective. -/
  classical
  -- Obtain the actual bilateral inverse from the finite Laurent inclusion.
  have hfinite : (Function.support
      (fun k : ℤ ↦ laurentPolynomialWiener f k)).Finite := by
    simpa only [Function.HasFiniteSupport, laurentPolynomialWiener_coeff] using
      f.coeff.hasFiniteSupport
  have hunit : IsUnit (laurentPolynomialWiener f) :=
    WienerLoop.isUnit_of_finiteSupport _ hfinite fun z ↦ by
      simpa only [laurentPolynomialWiener_eval] using hi z
  obtain ⟨u, hu⟩ := hunit
  let g : WienerLoop (Matrix (Fin n) (Fin n) A) := ↑(u⁻¹)
  have hgf : g * laurentPolynomialWiener f = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  have hleft (x : PositiveWienerModule A n) :
      positiveWienerToeplitz g (polynomialMultiplier f hf x) = x :=
    DFunLike.congr_fun (polynomialMultiplier_leftInverse f hf g hgf) x
  intro x y hxy
  calc
    x = positiveWienerToeplitz g (polynomialMultiplier f hf x) := (hleft x).symm
    _ = positiveWienerToeplitz g (polynomialMultiplier f hf y) :=
      congrArg (positiveWienerToeplitz g) hxy
    _ = y := hleft y

/-- The range is closed in the original ℓ¹ norm, before taking the algebraic quotient. -/
theorem polynomialMultiplier_isClosed_range
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (hi : ∀ z : Circle, IsUnit (laurentPolynomialCircleValue f z)) :
    IsClosed (Set.range (polynomialMultiplier f hf)) := by
  /- The same Wiener inverse gives a bounded left inverse S of T=M_f.
  Hence TS is a continuous idempotent, and its range equals the range of T.
  This range is the closed kernel of the continuous map I-TS. -/
  classical
  -- Obtain the actual bilateral inverse from the finite Laurent inclusion.
  have hfinite : (Function.support
      (fun k : ℤ ↦ laurentPolynomialWiener f k)).Finite := by
    simpa only [Function.HasFiniteSupport, laurentPolynomialWiener_coeff] using
      f.coeff.hasFiniteSupport
  have hunit : IsUnit (laurentPolynomialWiener f) :=
    WienerLoop.isUnit_of_finiteSupport _ hfinite fun z ↦ by
      simpa only [laurentPolynomialWiener_eval] using hi z
  obtain ⟨u, hu⟩ := hunit
  let g : WienerLoop (Matrix (Fin n) (Fin n) A) := ↑(u⁻¹)
  have hgf : g * laurentPolynomialWiener f = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  let T : PositiveWienerModule A n →L[A] PositiveWienerModule A n :=
    positiveWienerToeplitzContinuous (A := A) (n := n) (laurentPolynomialWiener f)
  let S : PositiveWienerModule A n →L[A] PositiveWienerModule A n :=
    positiveWienerToeplitzContinuous (A := A) (n := n) g
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

/-- UL04: low-degree polynomials map split-surjectively onto the actual cokernel.
The degree bound permits the zero polynomial and the zero-size matrix algebra. -/
theorem polynomialCokernel_exists_lowDegree_section
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (hi : ∀ z : Circle, IsUnit (laurentPolynomialCircleValue f z))
    (d : ℕ) (hd : ∀ k : ℤ, (d : ℤ) < k → f.coeff k = 0) :
    ∃ s : PolynomialCokernel f hf →ₗ[A] (Fin d → Fin n → A),
      ((polynomialCokernelMk f hf).comp (lowPolynomialEmbedding A n d)).comp s =
        LinearMap.id := by
  /- Stage 1: take the actual bilateral Wiener inverse g. Set T=M_f,
  S=P₊M_gi and E=I-TS. The equation gf=1 gives ST=I, hence E²=E,
  ET=0, and [Ex]=[x] in this very quotient.
  Stage 2: the other inverse equation fg=1 gives the exact identity
  E=P₊M_fP₋M_gi. Every nonnegative degree obtained by multiplying a negative
  input degree by a polynomial of degree at most d is strictly less than d.
  Thus E has image in the first d coefficient vectors even though g is infinite.
  Stage 3: define s([x]) to be these d coefficients of Ex. Since ET=0,
  this is well-defined and A-linear. The displayed embedding J satisfies
  J(s([x]))=Ex, so the quotient of J(s([x])) is exactly [x].
  If d=0, E=0 and the quotient is zero. This exact finite-bandwidth argument
  refines the earlier truncation/Neumann repair: no positivity or finite support
  is attributed to g, and no approximation is needed for a finite polynomial f. -/
  classical
  -- Obtain the actual bilateral inverse from the finite Laurent inclusion.
  have hfinite : (Function.support
      (fun k : ℤ ↦ laurentPolynomialWiener f k)).Finite := by
    simpa only [Function.HasFiniteSupport, laurentPolynomialWiener_coeff] using
      f.coeff.hasFiniteSupport
  have hunit : IsUnit (laurentPolynomialWiener f) :=
    WienerLoop.isUnit_of_finiteSupport _ hfinite fun z ↦ by
      simpa only [laurentPolynomialWiener_eval] using hi z
  obtain ⟨u, hu⟩ := hunit
  let g : WienerLoop (Matrix (Fin n) (Fin n) A) := ↑(u⁻¹)
  have hgf : g * laurentPolynomialWiener f = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  have hfg : laurentPolynomialWiener f * g = 1 := by
    rw [← hu]
    exact Units.mul_inv u
  let T : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
    polynomialMultiplier f hf
  let S : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n := positiveWienerToeplitz g
  let E : PositiveWienerModule A n →ₗ[A] PositiveWienerModule A n :=
    LinearMap.id - T.comp S
  have hST (x : PositiveWienerModule A n) : S (T x) = x :=
    DFunLike.congr_fun (polynomialMultiplier_leftInverse f hf g hgf) x
  have hET (x : PositiveWienerModule A n) : E (T x) = 0 := by
    change T x - T (S (T x)) = 0
    rw [hST, sub_self]
  -- Calculate the opposite product on one coefficient vector, in its original order.
  have hsingle (b : WienerLoop (Matrix (Fin n) (Fin n) A))
      (j k : ℕ) (v : Fin n → A) :
      positiveWienerToeplitz b (lp.single 1 j v) k = (b ((k : ℤ) - j)).mulVec v := by
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
    let V : PositiveWienerModule A n →L[A] (Fin n → A) :=
      lp.evalCLM A (fun _ : ℕ ↦ Fin n → A) 1 k
    have hcomp : V.comp ((positiveWienerToeplitzContinuous (A := A) (n := n)
        (laurentPolynomialWiener f)).comp (positiveWienerToeplitzContinuous (A := A) (n := n) g)) =
        V := by
      apply lp.ext_continuousLinearMap (by simp)
      intro j
      ext v : 1
      exact htail_single k hk j v
    have heq : T (S x) k = x k := DFunLike.congr_fun hcomp x
    change x k - T (S x) k = 0
    exact sub_eq_zero.mpr heq.symm
  -- Descend the first d defect coefficients through the original range quotient.
  let C : PositiveWienerModule A n →ₗ[A] (Fin d → Fin n → A) :=
    LinearMap.pi fun j : Fin d ↦
      (lp.evalₗ (fun _ : ℕ ↦ Fin n → A) 1 (j : ℕ)).comp E
  have hkernel : LinearMap.range T ≤ LinearMap.ker C := by
    rintro x ⟨y, rfl⟩
    change C (T y) = 0
    ext j i
    change E (T y) (j : ℕ) i = 0
    rw [hET]
    rfl
  let s : PolynomialCokernel f hf →ₗ[A] (Fin d → Fin n → A) :=
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

/-- The polynomial multiplier cokernel is a finitely generated A-module. -/
theorem polynomialCokernel_finite (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (hi : ∀ z : Circle, IsUnit (laurentPolynomialCircleValue f z)) :
    Module.Finite A (PolynomialCokernel f hf) := by
  /- Choose a natural upper degree bound from the finite support of f.
  The low-degree section theorem expresses the quotient as a surjective image
  of the finite free module with d vector coefficients. Thus it is finitely generated. -/
  classical
  let d := f.coeff.support.sup Int.toNat
  have hd (k : ℤ) (hk : (d : ℤ) < k) : f.coeff k = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hbound : k.toNat ≤ d := Finset.le_sup (f := Int.toNat) hmem
    omega
  obtain ⟨s, hs⟩ := polynomialCokernel_exists_lowDegree_section f hf hi d hd
  -- The quotient of the original low-degree embedding is split surjective.
  apply Module.Finite.of_surjective
    ((polynomialCokernelMk f hf).comp (lowPolynomialEmbedding A n d))
  intro q
  exact ⟨s q, DFunLike.congr_fun hs q⟩

/-- The polynomial multiplier cokernel is a projective A-module. -/
theorem polynomialCokernel_projective
    (f : LaurentPolynomial (Matrix (Fin n) (Fin n) A))
    (hf : ∀ k : ℤ, k < 0 → f.coeff k = 0)
    (hi : ∀ z : Circle, IsUnit (laurentPolynomialCircleValue f z)) :
    Module.Projective A (PolynomialCokernel f hf) := by
  /- Choose the same kind of finite upper degree bound and apply the
  low-degree section theorem. A retract of the finite free module is projective;
  apply Module.Projective.of_split to that actual section and quotient map. -/
  classical
  let d := f.coeff.support.sup Int.toNat
  have hd (k : ℤ) (hk : (d : ℤ) < k) : f.coeff k = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have hbound : k.toNat ≤ d := Finset.le_sup (f := Int.toNat) hmem
    omega
  obtain ⟨s, hs⟩ := polynomialCokernel_exists_lowDegree_section f hf hi d hd
  -- This section exhibits the same algebraic cokernel as a retract of a finite free module.
  exact Module.Projective.of_split s
    ((polynomialCokernelMk f hf).comp (lowPolynomialEmbedding A n d)) hs

end AtiyahSinger


/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Symbol
public import AtiyahSinger.Analysis.SymbolQuotient
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Differential operators in coordinates

Public module ID: M0412.

D03: a coordinate presentation of an operator of order at most m. Ordered coordinate
derivatives are allowed; presentations need not be unique. The principal symbol
depends only on the resulting operator, as proved below. Coordinate change and
bundle gluing are treated separately in `GlobalDifferentialOperator`.
The convention is D_j = -i ∂_j, so the principal symbol substitutes ξ_j for D_j.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff

variable {n r q m : ℕ}

/-- A smooth finite-order differential expression on an open coordinate domain. -/
structure CoordinateDifferentialOperator (n r q m : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) where
  /-- Coefficient of each ordered coordinate derivative of each degree at most m. -/
  coefficient : ∀ k : Fin (m + 1), (Fin k.val → Fin n) →
    EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
  /-- The coefficients are smooth over the real base, with complex-linear fiber maps. -/
  smooth_coefficient : ∀ k α, ContDiffOn ℝ ∞ (coefficient k α) U

namespace CoordinateDifferentialOperator

variable {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The actual differential expression, including the factors (-i)^k. -/
def apply (P : CoordinateDifferentialOperator n r q m U)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin q) :=
  ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
    P.coefficient k α x (((-Complex.I) ^ k.val) •
      iteratedFDeriv ℝ k.val u x (fun j ↦ EuclideanSpace.single (α j) 1))

/-- The highest-degree coefficient polynomial, with no condition at ξ = 0. -/
def principalSymbol (P : CoordinateDifferentialOperator n r q m U)
    (x ξ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
  ∑ α : Fin m → Fin n, (∏ j, ξ (α j)) •
    P.coefficient ⟨m, Nat.lt_succ_self m⟩ α x

/-- Ellipticity is invertibility of the principal symbol off the zero section. -/
def IsElliptic (P : CoordinateDifferentialOperator n r q m U) : Prop :=
  IsEllipticSymbol U P.principalSymbol

/-- D03: the principal symbol is homogeneous of degree m, even with zero top coefficients. -/
theorem isHomogeneousSymbol_principalSymbol
    (P : CoordinateDifferentialOperator n r q m U) :
    IsHomogeneousSymbol U m P.principalSymbol := by
  /- Each summand contains exactly m covector coordinates. Scaling by a positive real t
  multiplies their product by t^m. Sum the identities, using rpow_natCast. -/
  classical
  intro x hx ξ hξ t ht
  -- Each ordered monomial has exactly the original m covector factors.
  simp only [principalSymbol, PiLp.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.rpow_natCast,
    Finset.smul_sum, smul_smul]

/-- D03: the coordinate symbol satisfies the order-m symbol estimates. -/
theorem isSymbol_principalSymbol (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n r q m U) :
    IsSymbol U m P.principalSymbol := by
  /- The coefficient polynomial is jointly smooth on the open spatial domain.
  Homogeneity supplies symbol estimates outside the unit frequency ball through
  the established homogeneous-symbol theorem. The difference from that symbol
  is smooth with bounded frequency support, hence smoothing. Adding it back
  gives the order-m estimates for the original principal polynomial. -/
  classical
  -- The original polynomial is smooth even at zero frequency, on the given spatial domain.
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry P.principalSymbol)
      (U ×ˢ Set.univ) := by
    unfold principalSymbol Function.uncurry
    apply ContDiffOn.sum
    intro α _
    have hmonomial : ContDiff ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          ∏ j : Fin m, z.2 (α j)) := by
      exact contDiff_prod fun j _ ↦
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) (α j)).contDiff.comp contDiff_snd
    exact hmonomial.contDiffOn.smul
      ((P.smooth_coefficient ⟨m, Nat.lt_succ_self m⟩ α).comp contDiffOn_fst
        (fun z hz ↦ hz.1))
  -- Reuse the established homogeneous estimates away from the zero section.
  obtain ⟨a, ha⟩ := exists_symbol_of_homogeneous_on hU (m : ℝ) P.principalSymbol
    (hsmooth.mono (Set.prod_mono le_rfl (Set.subset_univ _)))
    P.isHomogeneousSymbol_principalSymbol
  -- The difference is smooth and vanishes at high frequency, so has every symbol order.
  have hrem : IsSymbol U (m : ℝ) (P.principalSymbol - a.val) :=
    isSmoothingSymbol_of_frequency_support hU _ 1 (hsmooth.sub a.property.1)
      (by
        intro x hx ξ hξ
        exact sub_eq_zero.mpr (ha x hx ξ hξ).symm) _
  have hsum := a.property.add hU hrem
  have hrecover : a.val + (P.principalSymbol - a.val) = P.principalSymbol := by
    abel
  rwa [hrecover] at hsum

/-- D03: redundant ordered-derivative presentations do not change the principal symbol. -/
theorem principalSymbol_eq_of_apply_eq (hU : IsOpen U)
    (P Q : CoordinateDifferentialOperator n r q m U)
    (hPQ : ∀ u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r),
      ContDiff ℝ ∞ u → ∀ x ∈ U, P.apply u x = Q.apply u x) :
    ∀ x ∈ U, ∀ ξ, P.principalSymbol x ξ = Q.principalSymbol x ξ := by
  /- Fix the base point, frequency and fiber vector. A globally smooth polynomial
  centered at the base point has only its m-th jet nonzero there. This jet is m!
  times the corresponding covector monomial. Evaluating either expression gives
  its principal symbol multiplied by the same nonzero factor (-i)^m m!, so equality
  of actions yields equality of the principal fiber maps. -/
  classical
  -- The polynomial test is global, so no extension from the open domain is needed.
  have _domainOpen : IsOpen U := hU
  intro x hx ξ
  apply ContinuousLinearMap.ext
  intro v
  -- Use a globally smooth homogeneous polynomial centered at the specified base point.
  let B : (EuclideanSpace ℝ (Fin n)) [×m]→L[ℝ] EuclideanSpace ℂ (Fin r) :=
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin m) v).compContinuousLinearMap
      (fun _ ↦ innerSL ℝ ξ)
  let u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r) :=
    fun y ↦ B (fun _ ↦ y - x)
  have hu : ContDiff ℝ ∞ u :=
    B.contDiff.comp (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const)
  -- Its finite Taylor series at x contains only degree m, including the case m = 0.
  let p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℂ (Fin r)) := fun k ↦ if h : m = k then h ▸ B else 0
  have hseries : HasFiniteFPowerSeriesOnBall u p x (m + 1) ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk'
    · intro k hk
      have hmk : m ≠ k := by omega
      simp [p, hmk]
    · exact ENNReal.zero_lt_top
    · intro y _
      rw [Finset.sum_eq_single_of_mem m (Finset.self_mem_range_succ m)]
      · simp [p, u]
      · intro k _ hk
        simp [p, hk.symm]
  have hzero {k : ℕ} (hk : k ≠ m) (a : Fin k → EuclideanSpace ℝ (Fin n)) :
      iteratedFDeriv ℝ k u x a = 0 := by
    rw [hseries.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
    simp [p, hk.symm]
  -- Permuting the scalar factors turns the top jet into m! identical monomials.
  have htop (α : Fin m → Fin n) :
      iteratedFDeriv ℝ m u x (fun j ↦ EuclideanSpace.single (α j) 1) =
        (m.factorial : ℝ) • (∏ j, ξ (α j)) • v := by
    rw [hseries.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
    have hperm (σ : Equiv.Perm (Fin m)) :
        B (fun j ↦ EuclideanSpace.single (α (σ j)) 1) = (∏ j, ξ (α j)) • v := by
      simp only [B, ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiRing_apply, innerSL_apply_apply,
        EuclideanSpace.inner_single_right, one_mul, conj_trivial]
      exact congrArg (fun t : ℝ ↦ t • v) (Equiv.prod_comp σ (fun j ↦ ξ (α j)))
    simp only [p, dite_eq_left rfl, hperm, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  -- In either original expression every degree below m vanishes on the same test.
  let c : ℂ := (-Complex.I) ^ m * (m.factorial : ℂ)
  have happly (R : CoordinateDifferentialOperator n r q m U) :
      R.apply u x = c • R.principalSymbol x ξ v := by
    unfold apply
    rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))]
    · simp only [htop, principalSymbol, sum_apply, smul_apply,
        ← Complex.coe_smul, Complex.ofReal_natCast, map_smul, c,
        mul_smul, Finset.smul_sum]
    · intro k _ hk
      have hkm : k.val ≠ m := by
        intro h
        exact hk (Fin.ext h)
      apply Finset.sum_eq_zero
      intro α _
      simp [hzero hkm]
    · simp
  -- The factor dictated by D_j = -i ∂_j is nonzero, so equality detects the symbol.
  have hc : c ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (by exact_mod_cast Nat.factorial_ne_zero m)
  have heq := hPQ u hu x hx
  rw [happly P, happly Q] at heq
  exact smul_right_injective _ hc heq

end CoordinateDifferentialOperator

end AtiyahSinger

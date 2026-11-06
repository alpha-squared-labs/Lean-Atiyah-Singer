/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinSmoothLift

/-!
# The infinitesimal spin action in the original Clifford algebra

Public module ID: M1454.

An even Clifford element which is skew under reversion is determined by its
commutators with the original Euclidean vectors. When those commutators give
a skew linear map, the element is the standard one-quarter double sum of
Clifford bivectors. This fixes the coefficient and sign needed to differentiate
the original spin transition functions in the Levi-Civita spin lift.

Source: Spin Geometry I.2, the Lie algebra of the spin double cover, and II.4,
the induced spin connection. The quadratic form is the existing negative
Euclidean form; no new spin group or representation is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

/-- A skew even Clifford element inducing a skew vector action has the standard bivector formula. -/
theorem euclideanSpin_eq_bivector_of_commutator (r : ℕ)
    (a : CliffordAlgebra (euclideanSpinQuadraticForm r))
    (A : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
    (hA : ∀ v w : EuclideanSpace ℝ (Fin r), inner ℝ (A v) w = -inner ℝ v (A w))
    (heven : CliffordAlgebra.involute a = a)
    (hreverse : CliffordAlgebra.reverse a = -a)
    (hcomm : ∀ v : EuclideanSpace ℝ (Fin r),
      a * CliffordAlgebra.ι (euclideanSpinQuadraticForm r) v -
        CliffordAlgebra.ι (euclideanSpinQuadraticForm r) v * a =
          CliffordAlgebra.ι (euclideanSpinQuadraticForm r) (A v)) :
    a = (1 / 4 : ℝ) • ∑ i : Fin r, ∑ j : Fin r,
      inner ℝ (A (EuclideanSpace.basisFun (Fin r) ℝ i))
        (EuclideanSpace.basisFun (Fin r) ℝ j) •
          (CliffordAlgebra.ι (euclideanSpinQuadraticForm r)
            (EuclideanSpace.basisFun (Fin r) ℝ i) *
            CliffordAlgebra.ι (euclideanSpinQuadraticForm r)
              (EuclideanSpace.basisFun (Fin r) ℝ j)) := by
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let Q := euclideanSpinQuadraticForm r
  let C := CliffordAlgebra Q
  let b := EuclideanSpace.basisFun (Fin r) ℝ
  let e (i : Fin r) : C := CliffordAlgebra.ι Q (b i)
  let ω (i j : Fin r) : ℝ := inner ℝ (A (b i)) (b j)
  let q : C := (1 / 4 : ℝ) • ∑ i : Fin r, ∑ j : Fin r, ω i j • (e i * e j)
  have hω (i j : Fin r) : ω i j = -ω j i := by
    exact (hA (b i) (b j)).trans
      (congrArg Neg.neg (real_inner_comm (b i) (A (b j))).symm)
  -- The negative quadratic form fixes the signs in the Clifford commutator.
  have hpolar (v w : V) : QuadraticMap.polar Q v w = -2 * inner ℝ v w := by
    change QuadraticMap.polar (-⇑(LinearMap.BilinMap.toQuadraticMap (innerₗ V))) v w = _
    rw [QuadraticMap.polar_neg, LinearMap.BilinMap.polar_toQuadraticMap]
    change -(inner ℝ v w + inner ℝ w v) = _
    rw [real_inner_comm w v]
    ring
  have hpair (i j : Fin r) : e i * e j + e j * e i =
      (-2 * inner ℝ (b i) (b j)) • (1 : C) := by
    change CliffordAlgebra.ι Q (b i) * CliffordAlgebra.ι Q (b j) +
      CliffordAlgebra.ι Q (b j) * CliffordAlgebra.ι Q (b i) = _
    rw [CliffordAlgebra.ι_mul_ι_add_swap, hpolar, Algebra.algebraMap_eq_smul_one]
  have htriple (i j k : Fin r) :
      (e i * e j) * e k - e k * (e i * e j) =
        (if i = k then (2 : ℝ) • e j else 0) -
          (if j = k then (2 : ℝ) • e i else 0) := by
    calc
      (e i * e j) * e k - e k * (e i * e j) =
          e i * (e j * e k + e k * e j) - (e i * e k + e k * e i) * e j := by
            noncomm_ring
      _ = e i * ((-2 * inner ℝ (b j) (b k)) • (1 : C)) -
          ((-2 * inner ℝ (b i) (b k)) • (1 : C)) * e j := by rw [hpair, hpair]
      _ = _ := by
        rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
          b.inner_eq_ite j k, b.inner_eq_ite i k]
        split_ifs <;> simp
        module
  -- The explicit bivector is even and skew under reversion.
  have hqeven : CliffordAlgebra.involute q = q := by
    simp [q, e, map_sum, map_smul, map_mul, CliffordAlgebra.involute_ι]
  have hqreverse : CliffordAlgebra.reverse q = -q := by
    have hrev (i j : Fin r) : CliffordAlgebra.reverse (e i * e j) = e j * e i := by
      exact (CliffordAlgebra.reverse.map_mul (e i) (e j)).trans (by simp [e])
    calc
      CliffordAlgebra.reverse q =
          (1 / 4 : ℝ) • ∑ i : Fin r, ∑ j : Fin r, ω i j • (e j * e i) := by
            simp only [q, map_smul, map_sum, hrev]
      _ = (1 / 4 : ℝ) • ∑ i : Fin r, ∑ j : Fin r, ω j i • (e i * e j) := by
        rw [Finset.sum_comm]
      _ = (1 / 4 : ℝ) • ∑ i : Fin r, ∑ j : Fin r, -(ω i j • (e i * e j)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hω j i, neg_smul]
      _ = -q := by simp [q]
  -- Evaluate the commutator on a basis. The two skew coefficient sums coincide.
  have hqcommBasis (k : Fin r) :
      q * e k - e k * q = CliffordAlgebra.ι Q (A (b k)) := by
    let L : C →ₗ[ℝ] C := (LinearMap.mul ℝ C).flip (e k) - LinearMap.mul ℝ C (e k)
    have hL (i j : Fin r) : L (e i * e j) =
        (if i = k then (2 : ℝ) • e j else 0) -
          (if j = k then (2 : ℝ) • e i else 0) := htriple i j k
    have hleft : (∑ i : Fin r, ∑ j : Fin r,
        ω i j • (if i = k then (2 : ℝ) • e j else 0)) =
          (2 : ℝ) • ∑ j : Fin r, ω k j • e j := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul, smul_smul, mul_comm]
    have hright : (∑ i : Fin r, ∑ j : Fin r,
        ω i j • (if j = k then (2 : ℝ) • e i else 0)) =
          -(2 : ℝ) • ∑ i : Fin r, ω k i • e i := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hω i k]
      module
    have hexpand : (∑ j : Fin r, ω k j • e j) = CliffordAlgebra.ι Q (A (b k)) := by
      have hcoef (j : Fin r) : b.repr (A (b k)) j = ω k j := by
        rw [b.repr_apply_apply]
        exact real_inner_comm _ _
      have h := congrArg (CliffordAlgebra.ι Q) (b.sum_repr (A (b k)))
      simpa only [map_sum, map_smul, hcoef, e] using h
    change L q = _
    dsimp only [q]
    rw [map_smul, map_sum]
    simp only [map_sum, map_smul, hL, smul_sub, Finset.sum_sub_distrib]
    rw [hleft, hright, hexpand]
    module
  have hqcomm (v : V) :
      q * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * q =
        CliffordAlgebra.ι Q (A v) := by
    have hmaps : (LinearMap.mul ℝ C q - (LinearMap.mul ℝ C).flip q).comp
        (CliffordAlgebra.ι Q) = (CliffordAlgebra.ι Q).comp A := by
      apply b.toBasis.ext
      exact hqcommBasis
    exact LinearMap.congr_fun hmaps v
  -- Their difference is an even central scalar; reversion-skewness forces it to vanish.
  have hdiffEven : CliffordAlgebra.involute (a - q) = a - q := by
    rw [map_sub, heven, hqeven]
  have hdiffComm (v : V) :
      CliffordAlgebra.ι Q v * (a - q) = (a - q) * CliffordAlgebra.ι Q v := by
    have hzero : (a - q) * CliffordAlgebra.ι Q v -
        CliffordAlgebra.ι Q v * (a - q) = 0 := by
      calc
        (a - q) * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * (a - q) =
            (a * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * a) -
              (q * CliffordAlgebra.ι Q v - CliffordAlgebra.ι Q v * q) := by noncomm_ring
        _ = 0 := by rw [hcomm v, hqcomm v, sub_self]
    exact (sub_eq_zero.mp hzero).symm
  obtain ⟨t, ht⟩ := euclideanSpin_exists_scalar_of_involute_eq_of_commute r
    (a - q) hdiffEven hdiffComm
  have hzero : t = 0 := by
    have hskew : CliffordAlgebra.reverse (a - q) = -(a - q) := by
      rw [map_sub, hreverse, hqreverse]
      abel
    rw [ht, CliffordAlgebra.reverse.commutes, ← map_neg] at hskew
    have heq : t = -t := (algebraMap ℝ C).injective hskew
    linarith
  have hd : a - q = 0 := by simp [ht, hzero]
  exact sub_eq_zero.mp hd

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Homotopy.Basic

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.PartitionOfUnity

/-!
# Laurent approximation of normalized invertible circle maps

Public module ID: M0778.

KA III.1.12–1.14, pp.116–117. Finite Laurent polynomials are evaluated using their
actual finitely supported coefficients. Uniform approximation is used twice: for a
single invertible loop and for a homotopy with prescribed Laurent endpoints.
The latter has one finite set of exponents for the whole parameter interval.

These statements apply to noncommutative complex Banach algebras. They do not assert
that the inverse of a Laurent polynomial is a Laurent polynomial. The comparison
with the project's stabilized interval-loop quotient is treated separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Topology ComplexConjugate

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

/-- Evaluation of an actual finite Laurent polynomial on the complex unit circle. -/
def laurentPolynomialCircleValue (p : LaurentPolynomial A) (z : Circle) : A :=
  p.coeff.sum (fun k a ↦ (z : ℂ) ^ k • a)

/-- A finite Laurent sum is continuous, including its negative powers on the circle. -/
theorem continuous_laurentPolynomialCircleValue (p : LaurentPolynomial A) :
    Continuous (laurentPolynomialCircleValue p) := by
  -- Finite support leaves only continuous integer powers on the nonzero unit circle.
  classical
  unfold laurentPolynomialCircleValue Finsupp.sum
  apply continuous_finsetSum
  intro k hk
  have hpower : Continuous (fun z : Circle ↦ (z : ℂ) ^ k) := by
    have h : Continuous (fun z : Circle ↦ z ^ k) := continuous_id.zpow k
    exact continuous_subtype_val.comp h
  exact hpower.smul continuous_const

/-- The continuous circle map associated with the specified Laurent polynomial. -/
def laurentPolynomialCircleMap (p : LaurentPolynomial A) : C(Circle, A) :=
  ⟨laurentPolynomialCircleValue p, continuous_laurentPolynomialCircleValue p⟩

variable [CompleteSpace A]

set_option maxHeartbeats 0 in

set_option maxRecDepth 4096 in
set_option linter.unusedSectionVars false in
/-- Banach-valued Laurent polynomials are uniformly dense in continuous circle maps. -/
theorem exists_laurentPolynomial_uniform_approximation
    (f : C(Circle, A)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : LaurentPolynomial A, ∀ z : Circle,
      ‖laurentPolynomialCircleValue p z - f z‖ < ε := by
  /- Scalar Stone–Weierstrass makes the scalar Laurent range dense. A finite
  partition of unity reduces Banach-valued uniform approximation to that
  scalar density, using finite sums of scalar functions times fixed values. -/
  classical
  have hpower (k : ℤ) : Continuous (fun z : Circle ↦ (z : ℂ) ^ k) := by
    exact continuous_subtype_val.comp
      (show Continuous (fun z : Circle ↦ z ^ k) from continuous_id.zpow k)
  -- Finite coefficient evaluation gives the original Laurent map as a linear map.
  let ev : LaurentPolynomial A →ₗ[ℂ] C(Circle, A) :=
    (Finsupp.lsum ℂ (fun k : ℤ ↦
      { toFun := fun b ↦
          ⟨fun z : Circle ↦ (z : ℂ) ^ k • b,
            (hpower k).smul continuous_const⟩
        map_add' := fun a b ↦ by ext z; simp [smul_add]
        map_smul' := fun c b ↦ by ext z; simp [smul_smul, mul_comm] } :
        ℤ → A →ₗ[ℂ] C(Circle, A))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  have hev (p : LaurentPolynomial A) (z : Circle) :
      ev p z = p.coeff.sum (fun k b ↦ (z : ℂ) ^ k • b) := by
    simp only [ev, LinearMap.comp_apply, Finsupp.lsum_apply]
    simp [Finsupp.sum, ContinuousMap.sum_apply]
  have hsingle (k : ℤ) (b : A) :
      ev (AddMonoidAlgebra.single k b) =
        ⟨fun z : Circle ↦ (z : ℂ) ^ k • b,
          (hpower k).smul continuous_const⟩ := by
    ext z
    simp only [hev, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index, smul_zero,
      ContinuousMap.coe_mk]
  let χ : Multiplicative ℤ →* C(Circle, ℂ) :=
    { toFun := fun k ↦ ⟨fun z ↦ (z : ℂ) ^ k.toAdd,
        hpower k.toAdd⟩
      map_one' := by ext z; simp
      map_mul' := fun i j ↦ by ext z; exact zpow_add₀ z.coe_ne_zero i.toAdd j.toAdd }
  let es : LaurentPolynomial ℂ →ₐ[ℂ] C(Circle, ℂ) :=
    AddMonoidAlgebra.lift ℂ C(Circle, ℂ) ℤ χ
  have hes (p : LaurentPolynomial ℂ) (z : Circle) :
      es p z = p.coeff.sum (fun k c ↦ (z : ℂ) ^ k * c) := by
    simp only [es, AddMonoidAlgebra.lift_apply, Finsupp.sum]
    simp [χ, mul_comm]
  have hs (k : ℤ) (c : ℂ) (z : Circle) :
      es (AddMonoidAlgebra.single k c) z = (z : ℂ) ^ k * c := by
    rw [hes]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index, mul_zero]
  -- The scalar range is a separating star algebra: conjugation reverses exponents.
  let P : StarSubalgebra ℂ C(Circle, ℂ) :=
    { es.range with
      star_mem' := by
        rintro g ⟨p, rfl⟩
        refine ⟨p.coeff.sum (fun k c ↦ AddMonoidAlgebra.single (-k) (star c)), ?_⟩
        rw [map_finsuppSum]
        ext z
        change (p.coeff.sum (fun k c ↦ es (AddMonoidAlgebra.single (-k) (star c)))) z =
          (star (es p)) z
        simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.star_apply]
        simp only [hs]
        rw [hes]
        simp only [Finsupp.sum, star_sum, star_mul']
        apply Finset.sum_congr rfl
        intro k hk
        have hz : star (z : ℂ) = (z : ℂ)⁻¹ := by
          exact (Circle.coe_inv_eq_conj z).symm
        simp only [star_zpow₀, hz, zpow_neg, inv_zpow] }
  have hP : P.SeparatesPoints := by
    intro x y hxy
    refine ⟨es (AddMonoidAlgebra.single 1 1),
      ⟨es (AddMonoidAlgebra.single 1 1), ⟨_, rfl⟩, rfl⟩, ?_⟩
    simpa only [hs, mul_one, zpow_one]
      using fun h : (x : ℂ) = (y : ℂ) ↦ hxy (Circle.ext h)
  have hdense : Dense (Set.range es) := by
    have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints P hP
    rw [dense_iff_closure_eq]
    change (P.topologicalClosure : Set C(Circle, ℂ)) = Set.univ
    rw [h]
    rfl
  let W : Submodule ℂ C(Circle, A) := ev.range.topologicalClosure
  have hWclosed : IsClosed (W : Set C(Circle, A)) :=
    ev.range.isClosed_topologicalClosure
  have hW (c : C(Circle, ℂ)) (a : A) :
      (⟨fun z ↦ c z • a, c.continuous.smul continuous_const⟩ : C(Circle, A)) ∈ W := by
    let L : C(Circle, ℂ) → C(Circle, A) := fun c ↦
      ⟨fun z ↦ c z • a, c.continuous.smul continuous_const⟩
    have hL : Continuous L := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact continuous_eval.smul continuous_const
    have hc : c ∈ closure (Set.range es) := hdense c
    apply closure_minimal (s := Set.range es) _ (hWclosed.preimage hL) hc
    intro g hg
    rcases hg with ⟨p, rfl⟩
    apply ev.range.le_topologicalClosure
    refine ⟨p.coeff.sum (fun k b ↦ AddMonoidAlgebra.single k (b • a)), ?_⟩
    rw [map_finsuppSum]
    ext z
    simp only [Finsupp.sum, ContinuousMap.sum_apply]
    simp only [hsingle, ContinuousMap.coe_mk]
    change _ = (es p) z • a
    rw [hes]
    simp [Finsupp.sum, Finset.sum_smul, smul_smul]
  -- A finite partition of unity reduces Banach-valued approximation to scalar density.
  have hf : f ∈ W := by
    change f ∈ (W : Set C(Circle, A))
    rw [← hWclosed.closure_eq]
    apply Metric.mem_closure_iff.2
    intro δ hδ
    let U : Circle → Set Circle := fun x ↦ {y | ‖f x - f y‖ < δ / 2}
    have hU (x : Circle) : IsOpen (U x) :=
      isOpen_lt (continuous_const.sub f.continuous).norm continuous_const
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
      intro x hx
      exact Set.mem_iUnion.2 ⟨x, by simpa [U] using half_pos hδ⟩)
    obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
      (fun x : s ↦ U x) (fun x ↦ hU x) (by
        intro x hx
        rcases Set.mem_iUnion₂.mp (hs hx) with ⟨i, hi, hix⟩
        exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hix⟩)
    let g : C(Circle, A) := ∑ i : s,
      ⟨fun z ↦ ((ρ i z : ℝ) : ℂ) • f i,
        (Complex.continuous_ofReal.comp (ρ i).continuous).smul continuous_const⟩
    have hg : g ∈ W := by
      apply W.sum_mem
      intro i hi
      exact hW ⟨fun z ↦ ((ρ i z : ℝ) : ℂ),
        Complex.continuous_ofReal.comp (ρ i).continuous⟩ (f i)
    refine ⟨g, hg, ?_⟩
    apply lt_of_le_of_lt (b := δ / 2) _ (half_lt_self hδ)
    rw [dist_comm, dist_eq_norm, (g - f).norm_le (half_pos hδ).le]
    intro z
    have hsum : ∑ i : s, ρ i z = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ z)
    have hz : (g - f) z = ∑ i : s, ((ρ i z : ℝ) : ℂ) • (f i - f z) := by
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.coe_mk,
        smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum,
        hsum, Complex.ofReal_one, one_smul]
    rw [hz]
    calc
      ‖∑ i : s, ((ρ i z : ℝ) : ℂ) • (f i - f z)‖ ≤
          ∑ i : s, ‖((ρ i z : ℝ) : ℂ) • (f i - f z)‖ := norm_sum_le _ _
      _ ≤ ∑ i : s, ρ i z * (δ / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i z)]
        by_cases hzero : ρ i z = 0
        · simp [hzero]
        · apply mul_le_mul_of_nonneg_left _ (ρ.nonneg i z)
          exact (hρ i (subset_closure hzero)).le
      _ = δ / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hmem : f ∈ closure (Set.range ev) := hf
  obtain ⟨g, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.mp hmem ε hε
  rw [dist_comm, dist_eq_norm] at hp
  refine ⟨p, fun z ↦ ?_⟩
  rw [laurentPolynomialCircleValue, ← hev]
  exact (ContinuousMap.norm_coe_le_norm (ev p - f) z).trans_lt hp

set_option maxHeartbeats 0 in

set_option maxRecDepth 4096 in
/-- KA III.1.14, surjectivity step: every normalized invertible loop has a normalized
Laurent representative through a homotopy consisting entirely of invertible maps. -/
theorem exists_normalized_laurent_homotopy
    (f : C(Circle, A)) (hbase : f 1 = 1) (hunit : ∀ z : Circle, IsUnit (f z)) :
    ∃ p : LaurentPolynomial A,
      Nonempty (ContinuousMap.HomotopyWith f (laurentPolynomialCircleMap p)
        (fun g ↦ g 1 = 1 ∧ ∀ z : Circle, IsUnit (g z))) := by
  /- A continuous affine correction fixes the base point before choosing the error.
  Openness of units controls the corrected Laurent map in one convex ball around f;
  straight interpolation then stays invertible without commuting any factors. -/
  classical
  -- Laurent evaluation and constant-term correction preserve a finite exponent set.
  let ev : LaurentPolynomial A →+ C(Circle, A) :=
    { toFun := laurentPolynomialCircleMap
      map_zero' := by ext z; simp [laurentPolynomialCircleMap, laurentPolynomialCircleValue]
      map_add' := by
        intro p q
        ext z
        simp [laurentPolynomialCircleMap, laurentPolynomialCircleValue,
          AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index, smul_add] }
  have hsingle (a : A) : ev (AddMonoidAlgebra.single 0 a) = .const Circle a := by
    ext z
    change (AddMonoidAlgebra.single 0 a).coeff.sum
      (fun k b ↦ (z : ℂ) ^ k • b) = a
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index, smul_zero,
      zpow_zero, one_smul]
  let N : C(Circle, A) → C(Circle, A) := fun g ↦
    g + ContinuousMap.const Circle (1 - g 1)
  have hN : Continuous N :=
    continuous_id.add (ContinuousMap.continuous_const'.comp
      (continuous_const.sub (continuous_eval_const 1)))
  have hNf : N f = f := by ext z; simp [N, hbase]
  -- Choose one convex ball of invertible continuous maps around the original loop.
  have hf : IsUnit f := f.isUnit_iff_forall_isUnit.mpr hunit
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    (Units.isOpen : IsOpen {g : C(Circle, A) | IsUnit g}) f hf
  obtain ⟨η, hη, hηN⟩ := Metric.continuousAt_iff.mp hN.continuousAt δ hδ
  obtain ⟨p, hp⟩ := exists_laurentPolynomial_uniform_approximation f (η / 2) (half_pos hη)
  have hpbound : dist (ev p) f < η := by
    rw [dist_eq_norm]
    apply lt_of_le_of_lt (b := η / 2) _ (half_lt_self hη)
    rw [(ev p - f).norm_le (half_pos hη).le]
    intro z
    exact (hp z).le
  let q : LaurentPolynomial A := p + AddMonoidAlgebra.single 0 (1 - ev p 1)
  have hq : ev q = N (ev p) := by
    dsimp only [q]
    rw [map_add, hsingle]
  have hqnear : ‖ev q - f‖ < δ := by
    have h := hηN hpbound
    rw [hNf, ← hq, dist_eq_norm] at h
    exact h
  have hqbase : ev q 1 = 1 := by rw [hq]; dsimp [N]; abel
  -- Affine interpolation stays inside that ball and fixes the base point exactly.
  let K : C(unitInterval, C(Circle, A)) :=
    ⟨fun t ↦ f + ((t : ℝ) : ℂ) • (ev q - f),
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)⟩
  have hKunit (t : unitInterval) : IsUnit (K t) := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖f + ((t : ℝ) : ℂ) • (ev q - f) - f‖ < δ
    rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg t.2.1]
    exact (mul_le_of_le_one_left (norm_nonneg (ev q - f)) t.2.2).trans_lt hqnear
  refine ⟨q, ⟨{
    toFun := fun tz ↦ K tz.1 tz.2
    continuous_toFun := continuous_eval.comp
      ((K.continuous.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := fun z ↦ by simp [K]
    map_one_left := fun z ↦ by
      simpa [K] using (show ev q z = laurentPolynomialCircleMap q z from rfl)
    prop' := fun t ↦ ?_ }⟩⟩
  change K t 1 = 1 ∧ ∀ z, IsUnit (K t z)
  constructor
  · simp [K, hbase, hqbase]
  · exact (K t).isUnit_iff_forall_isUnit.mp (hKunit t)

set_option maxHeartbeats 0 in

set_option maxRecDepth 4096 in
/-- KA III.1.14, injectivity step: a normalized invertible homotopy between specified
Laurent endpoints can be replaced by one Laurent polynomial with continuous coefficients. -/
theorem exists_laurent_homotopy_with_endpoints
    (p q : LaurentPolynomial A)
    (H : ContinuousMap.HomotopyWith (laurentPolynomialCircleMap p)
      (laurentPolynomialCircleMap q)
      (fun g ↦ g 1 = 1 ∧ ∀ z : Circle, IsUnit (g z))) :
    ∃ r : LaurentPolynomial C(unitInterval, A),
      (∀ z : Circle, laurentPolynomialCircleValue r z 0 =
        laurentPolynomialCircleValue p z) ∧
      (∀ z : Circle, laurentPolynomialCircleValue r z 1 =
        laurentPolynomialCircleValue q z) ∧
      (∀ t : unitInterval, laurentPolynomialCircleValue r 1 t = 1) ∧
      (∀ (t : unitInterval) (z : Circle),
        IsUnit (laurentPolynomialCircleValue r z t)) := by
  /- Work in C(Circle,C(I,A)). First normalize the base point, then correct both
  endpoints affinely using interval scalar functions. This continuous correction fixes
  H itself, so openness of units controls the entire corrected cylinder. All corrections
  act on finite Laurent coefficients, preserving a single finite exponent set. -/
  classical
  -- Evaluation is linear over scalar functions of the interval parameter.
  let : ContinuousConstSMul C(unitInterval, ℂ) C(unitInterval, A) :=
    ⟨fun w ↦ ContinuousMap.continuous_of_continuous_uncurry (fun b : C(unitInterval, A) ↦ w • b)
      ((w.continuous.comp continuous_snd).smul continuous_eval)⟩
  have hpower (k : ℤ) : Continuous (fun z : Circle ↦ (z : ℂ) ^ k) :=
    continuous_subtype_val.comp
      (show Continuous (fun z : Circle ↦ z ^ k) from continuous_id.zpow k)
  let ev : LaurentPolynomial C(unitInterval, A) →ₗ[C(unitInterval, ℂ)]
      C(Circle, C(unitInterval, A)) :=
    (Finsupp.lsum C(unitInterval, ℂ) (fun k : ℤ ↦
      { toFun := fun b : C(unitInterval, A) ↦
          ⟨fun z : Circle ↦ (z : ℂ) ^ k • b, (hpower k).smul continuous_const⟩
        map_add' := fun a b ↦ by
          ext z t
          change (z : ℂ) ^ k • (a t + b t) = (z : ℂ) ^ k • a t + (z : ℂ) ^ k • b t
          exact smul_add _ _ _
        map_smul' := fun w b ↦ by
          ext z t
          change (z : ℂ) ^ k • (w t • b t) = w t • ((z : ℂ) ^ k • b t)
          simp [smul_smul, mul_comm] } :
        ℤ → C(unitInterval, A) →ₗ[C(unitInterval, ℂ)] C(Circle, C(unitInterval, A)))).comp
      (AddMonoidAlgebra.coeffLinearEquiv C(unitInterval, ℂ)).toLinearMap
  have hev (v : LaurentPolynomial C(unitInterval, A)) (z : Circle) :
      ev v z = laurentPolynomialCircleValue v z := by
    simp only [ev, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum]
    simp [laurentPolynomialCircleValue, Finsupp.sum, ContinuousMap.sum_apply]
  have hsingle (k : ℤ) (b : C(unitInterval, A)) :
      ev (AddMonoidAlgebra.single k b) =
        ⟨fun z : Circle ↦ (z : ℂ) ^ k • b, (hpower k).smul continuous_const⟩ := by
    ext z
    rw [hev, laurentPolynomialCircleValue]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index, smul_zero,
      ContinuousMap.coe_mk]
  have hzero (b : C(unitInterval, A)) : ev (AddMonoidAlgebra.single 0 b) = .const Circle b := by
    rw [hsingle]
    ext z
    simp
  let liftP (v : LaurentPolynomial A) : LaurentPolynomial C(unitInterval, A) :=
    v.coeff.sum (fun k a ↦ AddMonoidAlgebra.single k (ContinuousMap.const unitInterval a))
  have hlift (v : LaurentPolynomial A) (z : Circle) (t : unitInterval) :
      ev (liftP v) z t = laurentPolynomialCircleValue v z := by
    dsimp only [liftP]
    simp only [Finsupp.sum, map_sum, ContinuousMap.sum_apply, hsingle,
      ContinuousMap.coe_mk, ContinuousMap.smul_apply, ContinuousMap.const_apply]
    rfl
  let atTime (t : unitInterval) : C(C(unitInterval, A), C(unitInterval, A)) :=
    ⟨fun b ↦ ContinuousMap.const unitInterval (b t),
      ContinuousMap.continuous_const'.comp (continuous_eval_const t)⟩
  let R (t : unitInterval) (g : C(Circle, C(unitInterval, A))) :
      C(Circle, C(unitInterval, A)) := (atTime t).comp g
  have hR (t : unitInterval) : Continuous (R t) := (atTime t).continuous_postcomp
  let J (t : unitInterval) (v : LaurentPolynomial C(unitInterval, A)) :
      LaurentPolynomial C(unitInterval, A) :=
    v.coeff.sum (fun k b ↦ AddMonoidAlgebra.single k (ContinuousMap.const unitInterval (b t)))
  have hJ (t : unitInterval) (v : LaurentPolynomial C(unitInterval, A)) :
      ev (J t v) = R t (ev v) := by
    ext z u
    dsimp only [J]
    simp only [Finsupp.sum, map_sum, ContinuousMap.sum_apply, hsingle,
      ContinuousMap.coe_mk, ContinuousMap.smul_apply, ContinuousMap.const_apply]
    change _ = ev v z t
    rw [hev, laurentPolynomialCircleValue]
    simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  -- Curry the same homotopy and correct only its finite coefficient data.
  let F : C(Circle, C(unitInterval, A)) := (⟨fun zt : Circle × unitInterval ↦ H (zt.2, zt.1),
    H.continuous.comp continuous_swap⟩ : C(Circle × unitInterval, A)).curry
  have hFunit : IsUnit F := by
    apply F.isUnit_iff_forall_isUnit.mpr
    intro z
    apply (F z).isUnit_iff_forall_isUnit.mpr
    intro t
    exact (H.prop t).2 z
  have hFbase : F 1 = 1 := by ext t; exact (H.prop t).1
  have hF0 : R 0 F = ev (liftP p) := by
    ext z t
    rw [hlift]
    exact H.map_zero_left z
  have hF1 : R 1 F = ev (liftP q) := by
    ext z t
    rw [hlift]
    exact H.map_one_left z
  let w0 : C(unitInterval, ℂ) := ⟨fun t ↦ 1 - ((t : ℝ) : ℂ),
    continuous_const.sub (Complex.continuous_ofReal.comp continuous_subtype_val)⟩
  let w1 : C(unitInterval, ℂ) := ⟨fun t ↦ ((t : ℝ) : ℂ),
    Complex.continuous_ofReal.comp continuous_subtype_val⟩
  let N : C(Circle, C(unitInterval, A)) → C(Circle, C(unitInterval, A)) := fun g ↦
    g + ContinuousMap.const Circle (1 - g 1)
  have hN : Continuous N :=
    continuous_id.add (ContinuousMap.continuous_const'.comp
      (continuous_const.sub (continuous_eval_const 1)))
  have hNF : N F = F := by ext z t; simp [N, hFbase]
  let Q : C(Circle, C(unitInterval, A)) → C(Circle, C(unitInterval, A)) := fun g ↦
    N g + w0 • (ev (liftP p) - R 0 (N g)) + w1 • (ev (liftP q) - R 1 (N g))
  have hQ : Continuous Q :=
    (hN.add ((continuous_const.sub ((hR 0).comp hN)).const_smul w0)).add
      ((continuous_const.sub ((hR 1).comp hN)).const_smul w1)
  have hQF : Q F = F := by
    dsimp only [Q]
    rw [hNF, hF0, hF1, sub_self, sub_self, smul_zero, smul_zero, add_zero, add_zero]
  -- Openness of units controls the complete cylinder after all endpoint corrections.
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    (Units.isOpen : IsOpen {g : C(Circle, C(unitInterval, A)) | IsUnit g}) F hFunit
  obtain ⟨η, hη, hηQ⟩ := Metric.continuousAt_iff.mp (hQ.continuousAt (x := F)) δ hδ
  obtain ⟨v, hv⟩ := exists_laurentPolynomial_uniform_approximation F (η / 2) (half_pos hη)
  have hvbound : dist (ev v) F < η := by
    rw [dist_eq_norm]
    apply lt_of_le_of_lt (b := η / 2) _ (half_lt_self hη)
    rw [(ev v - F).norm_le (half_pos hη).le]
    intro z
    rw [ContinuousMap.sub_apply, hev]
    exact (hv z).le
  let v' : LaurentPolynomial C(unitInterval, A) := v + AddMonoidAlgebra.single 0 (1 - ev v 1)
  have hv' : ev v' = N (ev v) := by dsimp only [v']; rw [map_add, hzero]
  let r : LaurentPolynomial C(unitInterval, A) :=
    v' + w0 • (liftP p - J 0 v') + w1 • (liftP q - J 1 v')
  have hr : ev r = Q (ev v) := by
    dsimp only [r, Q]
    rw [map_add, map_add, map_smul, map_smul, map_sub, map_sub, hJ, hJ, hv']
  have hrunit : IsUnit (ev r) := by
    apply hball
    rw [Metric.mem_ball, hr]
    simpa only [hQF] using hηQ hvbound
  have hNbase : N (ev v) 1 = 1 := by dsimp [N]; abel
  have hpbase : laurentPolynomialCircleValue p 1 = 1 := by
    exact (H.map_zero_left 1).symm.trans (H.prop 0).1
  have hqbase : laurentPolynomialCircleValue q 1 = 1 := by
    exact (H.map_one_left 1).symm.trans (H.prop 1).1
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [← hev, hr]
    change N (ev v) z 0 + (1 - (0 : ℂ)) •
      (ev (liftP p) z 0 - N (ev v) z 0) + (0 : ℂ) •
        (ev (liftP q) z 0 - N (ev v) z 1) = _
    simp [hlift]
  · intro z
    rw [← hev, hr]
    change N (ev v) z 1 + (1 - (1 : ℂ)) •
      (ev (liftP p) z 1 - N (ev v) z 0) + (1 : ℂ) •
        (ev (liftP q) z 1 - N (ev v) z 1) = _
    simp [hlift]
  · intro t
    rw [← hev, hr]
    change N (ev v) 1 t + w0 t •
      (ev (liftP p) 1 t - N (ev v) 1 0) + w1 t •
        (ev (liftP q) 1 t - N (ev v) 1 1) = 1
    rw [hNbase, hlift, hlift, hpbase, hqbase]
    simp
  · intro t z
    rw [← hev]
    have hz : IsUnit (ev r z) := (ev r).isUnit_iff_forall_isUnit.mp hrunit z
    exact (ev r z).isUnit_iff_forall_isUnit.mp hz t

end AtiyahSinger

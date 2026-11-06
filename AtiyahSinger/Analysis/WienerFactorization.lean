/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.WienerLoop
public import Mathlib.Topology.Homotopy.Basic

/-!
# Factorization and contraction of a normalized affine loop

Public module ID: M1052.

KL06: Karoubi, K-Theory, III.1.24, pp.121–122. For a normalized affine loop
σ = a₀ + a₁z with the specified two-sided Wiener inverse b, the actual element
q = a₀b₀ is idempotent. Its complement p gives the factorization
σ = σ⁺ σ⁻ (q + pz), with σ⁺ and σ⁻ invertible in the respective one-sided
Wiener algebras. All factors below use this same inverse and these same projectors.

The negative factor has inverse q + z b p. The printed p.122 expression
q + z⁻¹ b p is erroneous: σ=z, p=1, q=0 already disproves it. The corrected
formula is checked against both inverse identities, not merely its support.

The explicit normalized radial homotopy is the factor-contraction step of
III.1.25. At radius zero its constant factor commutes with p and q, which is
necessary to identify its normalized endpoint with q+pz. No commutativity of
the ambient complex Banach algebra is assumed.
Both constructions use the same supplied Wiener inverse.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.WienerLoop

open scoped unitInterval

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The negative Wiener algebra consists of series supported in nonpositive degrees. -/
def negativeSubalgebra : Subalgebra ℂ (WienerLoop A) where
  carrier := {f | ∀ n : ℤ, 0 < n → f n = 0}
  mul_mem' := by
    intro f g hf hg n hn
    change (∑' k : ℤ, f k * g (n - k)) = 0
    have hterm : ∀ k : ℤ, f k * g (n - k) = 0 := by
      intro k
      by_cases hk : 0 < k
      · rw [hf k hk, zero_mul]
      · rw [hg (n - k) (by omega), mul_zero]
    simp only [hterm, tsum_zero]
  one_mem' := by
    intro n hn
    change lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) (1 : A) n = 0
    exact lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 1 (ne_of_gt hn)
  add_mem' := by
    intro f g hf hg n hn
    change f n + g n = 0
    rw [hf n hn, hg n hn, add_zero]
  zero_mem' := by
    intro n hn
    rfl
  algebraMap_mem' := by
    intro c n hn
    change c • (lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) (1 : A) n) = 0
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 1 (ne_of_gt hn), smul_zero]

/-- The complementary projector yielding the Bott loop of an affine invertible series. -/
def affineBottIdempotent (a₀ : A) (b : WienerLoop A) : A :=
  1 - a₀ * b 0

/-- KL06: the zero Fourier coefficient of the specified inverse gives Karoubi's projector. -/
theorem affine_complement_isIdempotentElem (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) : IsIdempotentElem (a₀ * b 0) := by
  /- Stage 1: the degree-zero inverse recurrence gives a₀b₀+a₁b₋₁=1.
  Stage 2: multiply by a₀b₀ and use b₀a₁b₋₁=0 from KL05. This gives
  (a₀b₀)²=a₀b₀, preserving the order of every factor in the ambient algebra. -/
  -- The zero recurrence and the opposite-half relation use the same inverse b.
  have hsum : a₀ * b 0 + a₁ * b (-1) = 1 := by
    simpa using (affine_inverse_coefficients a₀ a₁ b hleft hright 0).1
  have hcross : b 0 * a₁ * b (-1) = 0 :=
    (affine_inverse_cross_coefficients a₀ a₁ hbase b hleft hright
      0 (-1) (Or.inr ⟨le_refl _, by norm_num⟩)).2
  have hproduct : (a₀ * b 0) * (a₁ * b (-1)) = 0 := by
    calc
      (a₀ * b 0) * (a₁ * b (-1)) = a₀ * (b 0 * a₁ * b (-1)) := by
        simp only [mul_assoc]
      _ = 0 := by rw [hcross, mul_zero]
  -- Multiplication by the complementary summand vanishes, leaving q² = q.
  change (a₀ * b 0) * (a₀ * b 0) = a₀ * b 0
  calc
    (a₀ * b 0) * (a₀ * b 0) = (a₀ * b 0) * (a₀ * b 0 + a₁ * b (-1)) := by
      rw [mul_add, hproduct, add_zero]
    _ = a₀ * b 0 := by rw [hsum, mul_one]

/-- The projector used in the Bott factor is the complement of Karoubi's q. -/
theorem affineBottIdempotent_isIdempotentElem (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) :
    IsIdempotentElem (affineBottIdempotent a₀ b) := by
  /- The preceding theorem gives q²=q. Expand (1-q)² to obtain (1-q)²=1-q.
  This complementary idempotent, rather than q itself, is the coefficient of z. -/
  -- The complement of an idempotent is idempotent in an arbitrary ring.
  have hq := (affine_complement_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  change (1 - a₀ * b 0) * (1 - a₀ * b 0) = 1 - a₀ * b 0
  simp only [sub_mul, mul_sub, one_mul, mul_one, hq, sub_self, sub_zero]

/-- Karoubi's positive factor p+σq, written as its actual degree-zero and degree-one series. -/
def affinePositiveFactor (a₀ a₁ : A) (b : WienerLoop A) : WienerLoop A :=
  let p := affineBottIdempotent a₀ b
  let q := 1 - p
  affine (p + a₀ * q) (a₁ * q)

/-- Karoubi's negative factor q+z⁻¹σp, retaining the noncommutative coefficient order. -/
def affineNegativeFactor (a₀ a₁ : A) (b : WienerLoop A) : WienerLoop A :=
  let p := affineBottIdempotent a₀ b
  let q := 1 - p
  lp.single 1 0 (q + a₁ * p) + lp.single 1 (-1) (a₀ * p)

/-- The actual positive inverse p+bq; its one-sided support is a consequence of KL05. -/
def affinePositiveInverse (a₀ : A) (b : WienerLoop A) : WienerLoop A :=
  let p := affineBottIdempotent a₀ b
  lp.single 1 0 p + b * lp.single 1 0 (1 - p)

/-- The corrected negative inverse q+zbp; the shift is +1, not -1 as printed on p.122. -/
def affineNegativeInverse (a₀ : A) (b : WienerLoop A) : WienerLoop A :=
  let p := affineBottIdempotent a₀ b
  lp.single 1 0 (1 - p) + shift 1 (b * lp.single 1 0 p)

/-- The positive factor and its inverse belong to the positive algebra and invert each other. -/
theorem affinePositiveFactor_unit_data (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) :
    affinePositiveFactor a₀ a₁ b ∈ positiveSubalgebra ∧
      affinePositiveInverse a₀ b ∈ positiveSubalgebra ∧
      affinePositiveFactor a₀ a₁ b * affinePositiveInverse a₀ b = 1 ∧
      affinePositiveInverse a₀ b * affinePositiveFactor a₀ a₁ b = 1 := by
  /- Stage 1: the factor is supported in degrees 0 and 1. For n<0, the
  inverse coefficient bₙq=bₙa₀b₀ vanishes by the KL05 cross relations.
  Stage 2: KL05 makes p,q commute with σ and b. Their orthogonality and
  the two specified inverse identities give (p+σq)(p+bq)=p+q=1 and the
  reverse product. -/
  classical
  let p : A := affineBottIdempotent a₀ b
  let q : A := 1 - p
  have hq : q = a₀ * b 0 := by simp [q, p, affineBottIdempotent]
  have hp : p = 1 - q := by simp [q]
  have hqq : q * q = q := by
    rw [hq]
    exact (affine_complement_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hpp : p * p = p :=
    (affineBottIdempotent_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hpq : p * q = 0 := by rw [hp, sub_mul, one_mul, hqq, sub_self]
  have hqp : q * p = 0 := by rw [hp, mul_sub, mul_one, hqq, sub_self]
  have hsum : p + q = 1 := by dsimp [q]; abel
  have hqcoeff (n : ℤ) : Commute q (b n) := by
    rw [hq]
    exact (affine_inverse_commute a₀ a₁ hbase b hleft hright n).1.mul_left
      (affine_inverse_coefficients_commute a₀ a₁ hbase b hleft hright 0 n)
  have hqa₀ : Commute q a₀ := by
    rw [hq]
    exact (Commute.refl a₀).mul_left
      (affine_inverse_commute a₀ a₁ hbase b hleft hright 0).1.symm
  have hqa₁ : Commute q a₁ := by
    rw [eq_sub_of_add_eq' hbase]
    exact (Commute.one_right q).sub_right hqa₀
  -- The factor has degrees 0 and 1; the inverse support uses KL05 at (n, 0).
  have hfactor : affinePositiveFactor a₀ a₁ b ∈ positiveSubalgebra := by
    intro n hn
    change lp.single (E := fun _ : ℤ ↦ A) 1 0 (p + a₀ * q) n +
      lp.single (E := fun _ : ℤ ↦ A) 1 1 (a₁ * q) n = 0
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 _ (by omega),
      lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 1 _ (by omega), add_zero]
  have hconstant (f : WienerLoop A) (a : A) (n : ℤ) :
      (f * (lp.single 1 0 a : WienerLoop A) : WienerLoop A) n = f n * a := by
    change (∑' k : ℤ, f k *
      lp.single (E := fun _ : ℤ ↦ A) 1 0 a (n - k)) = f n * a
    rw [tsum_eq_single n]
    · simp
    · intro k hk
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 a (by omega), mul_zero]
  have hinverse : affinePositiveInverse a₀ b ∈ positiveSubalgebra := by
    intro n hn
    change lp.single (E := fun _ : ℤ ↦ A) 1 0 p n +
      (b * (lp.single 1 0 q : WienerLoop A) : WienerLoop A) n = 0
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 p (by omega), zero_add,
      hconstant, hq, ← mul_assoc]
    exact (affine_inverse_cross_coefficients a₀ a₁ hbase b hleft hright
      n 0 (Or.inl ⟨hn, le_refl _⟩)).1
  -- Evaluate the actual factors, then apply the two inverse identities in each corner.
  have hvalues (z : Circle) :
      (affinePositiveFactor a₀ a₁ b * affinePositiveInverse a₀ b).eval z =
        (1 : WienerLoop A).eval z ∧
      (affinePositiveInverse a₀ b * affinePositiveFactor a₀ a₁ b).eval z =
        (1 : WienerLoop A).eval z := by
    have hsingle (k : ℤ) (a : A) :
        eval (lp.single 1 k a : WienerLoop A) z = (z : ℂ) ^ k • a := by
      change (∑' n : ℤ, (z : ℂ) ^ n •
        lp.single (E := fun _ : ℤ ↦ A) 1 k a n) = _
      rw [tsum_eq_single k]
      · simp
      · intro n hn
        rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 k a hn, smul_zero]
    have hadd (f g : WienerLoop A) : (f + g).eval z = f.eval z + g.eval z := by
      have hs (x : WienerLoop A) : Summable (fun n : ℤ ↦ (z : ℂ) ^ n • x n) := by
        have hx : Summable (fun n : ℤ ↦ ‖x n‖) := by simpa using x.2.summable
        apply Summable.of_norm
        simpa only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul] using hx
      change (∑' n : ℤ, (z : ℂ) ^ n • (f n + g n)) = _
      simp_rw [smul_add]
      exact (hs f).tsum_add (hs g)
    let φ : WienerLoop A →+* A :=
      { toFun := fun f ↦ f.eval z
        map_one' := by
          change eval (lp.single 1 0 (1 : A) : WienerLoop A) z = 1
          simp [hsingle]
        map_mul' := fun f g ↦ eval_mul f g z
        map_zero' := by simp [eval]
        map_add' := hadd }
    have hφ (k : ℤ) (a : A) : φ (lp.single 1 k a) = (z : ℂ) ^ k • a := hsingle k a
    have ha (x y : A) : φ (affine x y) = x + (z : ℂ) • y := by
      change φ (lp.single 1 0 x + lp.single 1 1 y) = _
      simp only [map_add, hφ, zpow_zero, one_smul, zpow_one]
    have hfactorValue : φ (affinePositiveFactor a₀ a₁ b) = p + φ (affine a₀ a₁) * q := by
      change φ (affine (p + a₀ * q) (a₁ * q)) = _
      rw [ha, ha, add_mul, smul_mul_assoc, add_assoc]
    have hinverseValue : φ (affinePositiveInverse a₀ b) = p + φ b * q := by
      change φ (lp.single 1 0 p + b * lp.single 1 0 q) = _
      simp only [map_add, map_mul, hφ, zpow_zero, one_smul]
    have hqx : Commute q (φ (affine a₀ a₁)) := by
      rw [ha]
      exact hqa₀.add_right (hqa₁.smul_right (z : ℂ))
    have hqy : Commute q (φ b) :=
      Commute.tsum_right q (fun n ↦ (hqcoeff n).smul_right ((z : ℂ) ^ n))
    have hprod (x y : A) (hqy : Commute q y) (hxy : x * y = 1) :
        (p + x * q) * (p + y * q) = 1 := by
      have hpy : Commute p y := by rw [hp]; exact (Commute.one_left y).sub_left hqy
      have hmix₁ : p * (y * q) = 0 := by rw [hpy.left_comm, hpq, mul_zero]
      have hmix₂ : (x * q) * p = 0 := by rw [mul_assoc, hqp, mul_zero]
      have hcorner : (x * q) * (y * q) = q := by
        calc
          (x * q) * (y * q) = x * (q * y) * q := by simp only [mul_assoc]
          _ = x * (y * q) * q := by rw [hqy.eq]
          _ = (x * y) * (q * q) := by simp only [mul_assoc]
          _ = q := by rw [hxy, hqq, one_mul]
      rw [add_mul, mul_add, mul_add, hpp, hmix₁, hmix₂, hcorner,
        add_zero, zero_add, hsum]
    have hxy : φ (affine a₀ a₁) * φ b = 1 := by
      simpa only [map_mul, map_one] using congrArg φ hleft
    have hyx : φ b * φ (affine a₀ a₁) = 1 := by
      simpa only [map_mul, map_one] using congrArg φ hright
    change φ (affinePositiveFactor a₀ a₁ b * affinePositiveInverse a₀ b) = φ 1 ∧
      φ (affinePositiveInverse a₀ b * affinePositiveFactor a₀ a₁ b) = φ 1
    simp only [map_mul, map_one, hfactorValue, hinverseValue]
    exact ⟨hprod _ _ hqy hxy, hprod _ _ hqx hyx⟩
  exact ⟨hfactor, hinverse, eval_injective (funext fun z ↦ (hvalues z).1),
    eval_injective (funext fun z ↦ (hvalues z).2)⟩

/-- The negative factor and corrected inverse lie in the negative algebra and invert each other. -/
theorem affineNegativeFactor_unit_data (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) :
    affineNegativeFactor a₀ a₁ b ∈ negativeSubalgebra ∧
      affineNegativeInverse a₀ b ∈ negativeSubalgebra ∧
      affineNegativeFactor a₀ a₁ b * affineNegativeInverse a₀ b = 1 ∧
      affineNegativeInverse a₀ b * affineNegativeFactor a₀ a₁ b = 1 := by
  /- Stage 1: the factor has degrees -1 and 0. The degree-zero inverse
  recurrence identifies p with a₁b₋₁. At n>0 the inverse coefficient is
  b(n-1)p=b(n-1)a₁b₋₁=0, including the boundary n=1, by KL05.
  Stage 2: multiply (q+z⁻¹σp)(q+zbp) in both orders. Orthogonality kills
  the mixed terms; z⁻¹z and σb cancel, leaving q+p=1. Using z⁻¹ also
  in the inverse would instead introduce z⁻² and fails already for σ=z. -/
  classical
  let p : A := affineBottIdempotent a₀ b
  let q : A := 1 - p
  have hq : q = a₀ * b 0 := by simp [q, p, affineBottIdempotent]
  have hp : p = 1 - q := by simp [q]
  have hqq : q * q = q := by
    rw [hq]
    exact (affine_complement_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hpp : p * p = p :=
    (affineBottIdempotent_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hpq : p * q = 0 := by rw [hp, sub_mul, one_mul, hqq, sub_self]
  have hqp : q * p = 0 := by rw [hp, mul_sub, mul_one, hqq, sub_self]
  have hsum : p + q = 1 := by dsimp [q]; abel
  have hqcoeff (n : ℤ) : Commute q (b n) := by
    rw [hq]
    exact (affine_inverse_commute a₀ a₁ hbase b hleft hright n).1.mul_left
      (affine_inverse_coefficients_commute a₀ a₁ hbase b hleft hright 0 n)
  have hqa₀ : Commute q a₀ := by
    rw [hq]
    exact (Commute.refl a₀).mul_left
      (affine_inverse_commute a₀ a₁ hbase b hleft hright 0).1.symm
  have hqa₁ : Commute q a₁ := by
    rw [eq_sub_of_add_eq' hbase]
    exact (Commute.one_right q).sub_right hqa₀
  -- The corrected negative inverse has coefficient b(n - 1)p, including n = 1.
  have hpcoeff : p = a₁ * b (-1) := by
    have hzero : a₀ * b 0 + a₁ * b (-1) = 1 := by
      simpa using (affine_inverse_coefficients a₀ a₁ b hleft hright 0).1
    rw [hp, hq]
    exact (eq_sub_of_add_eq' hzero).symm
  have hfactor : affineNegativeFactor a₀ a₁ b ∈ negativeSubalgebra := by
    intro n hn
    change lp.single (E := fun _ : ℤ ↦ A) 1 0 (q + a₁ * p) n +
      lp.single (E := fun _ : ℤ ↦ A) 1 (-1) (a₀ * p) n = 0
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 _ (by omega),
      lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 (-1) _ (by omega), add_zero]
  have hconstant (f : WienerLoop A) (a : A) (n : ℤ) :
      (f * (lp.single 1 0 a : WienerLoop A) : WienerLoop A) n = f n * a := by
    change (∑' k : ℤ, f k *
      lp.single (E := fun _ : ℤ ↦ A) 1 0 a (n - k)) = f n * a
    rw [tsum_eq_single n]
    · simp
    · intro k hk
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 a (by omega), mul_zero]
  have hinverse : affineNegativeInverse a₀ b ∈ negativeSubalgebra := by
    intro n hn
    change lp.single (E := fun _ : ℤ ↦ A) 1 0 q n +
      (b * (lp.single 1 0 p : WienerLoop A) : WienerLoop A) (n - 1) = 0
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 q (by omega), zero_add,
      hconstant, hpcoeff, ← mul_assoc]
    exact (affine_inverse_cross_coefficients a₀ a₁ hbase b hleft hright
      (n - 1) (-1) (Or.inr ⟨by omega, by norm_num⟩)).2
  -- Circle evaluation cancels z⁻¹ against the actual +1 shift in the inverse.
  have hvalues (z : Circle) :
      (affineNegativeFactor a₀ a₁ b * affineNegativeInverse a₀ b).eval z =
        (1 : WienerLoop A).eval z ∧
      (affineNegativeInverse a₀ b * affineNegativeFactor a₀ a₁ b).eval z =
        (1 : WienerLoop A).eval z := by
    have hsingle (k : ℤ) (a : A) :
        eval (lp.single 1 k a : WienerLoop A) z = (z : ℂ) ^ k • a := by
      change (∑' n : ℤ, (z : ℂ) ^ n •
        lp.single (E := fun _ : ℤ ↦ A) 1 k a n) = _
      rw [tsum_eq_single k]
      · simp
      · intro n hn
        rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 k a hn, smul_zero]
    have hadd (f g : WienerLoop A) : (f + g).eval z = f.eval z + g.eval z := by
      have hs (x : WienerLoop A) : Summable (fun n : ℤ ↦ (z : ℂ) ^ n • x n) := by
        have hx : Summable (fun n : ℤ ↦ ‖x n‖) := by simpa using x.2.summable
        apply Summable.of_norm
        simpa only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul] using hx
      change (∑' n : ℤ, (z : ℂ) ^ n • (f n + g n)) = _
      simp_rw [smul_add]
      exact (hs f).tsum_add (hs g)
    let φ : WienerLoop A →+* A :=
      { toFun := fun f ↦ f.eval z
        map_one' := by
          change eval (lp.single 1 0 (1 : A) : WienerLoop A) z = 1
          simp [hsingle]
        map_mul' := fun f g ↦ eval_mul f g z
        map_zero' := by simp [eval]
        map_add' := hadd }
    have hφ (k : ℤ) (a : A) : φ (lp.single 1 k a) = (z : ℂ) ^ k • a := hsingle k a
    have ha (x y : A) : φ (affine x y) = x + (z : ℂ) • y := by
      change φ (lp.single 1 0 x + lp.single 1 1 y) = _
      simp only [map_add, hφ, zpow_zero, one_smul, zpow_one]
    have hshift (k : ℤ) (f : WienerLoop A) : φ (shift k f) = (z : ℂ) ^ k • φ f :=
      shift_eval f k z
    have hfactorValue : φ (affineNegativeFactor a₀ a₁ b) =
        q + ((z : ℂ)⁻¹ • φ (affine a₀ a₁)) * p := by
      change φ (lp.single 1 0 (q + a₁ * p) + lp.single 1 (-1) (a₀ * p)) = _
      simp only [map_add, hφ, zpow_zero, one_smul, zpow_neg_one, ha,
        smul_add, add_mul, smul_mul_assoc, smul_smul]
      rw [inv_mul_cancel₀ (Circle.coe_ne_zero z), one_smul]
      abel
    have hinverseValue : φ (affineNegativeInverse a₀ b) = q + ((z : ℂ) • φ b) * p := by
      change φ (lp.single 1 0 q + shift 1 (b * lp.single 1 0 p)) = _
      simp only [map_add, hφ, zpow_zero, one_smul, hshift, map_mul, zpow_one,
        smul_mul_assoc]
    have hqx : Commute q (φ (affine a₀ a₁)) := by
      rw [ha]
      exact hqa₀.add_right (hqa₁.smul_right (z : ℂ))
    have hqy : Commute q (φ b) :=
      Commute.tsum_right q (fun n ↦ (hqcoeff n).smul_right ((z : ℂ) ^ n))
    have hprod (x y : A) (hqy : Commute q y) (hxy : x * y = 1) :
        (q + x * p) * (q + y * p) = 1 := by
      have hpy : Commute p y := by rw [hp]; exact (Commute.one_left y).sub_left hqy
      have hmix₁ : q * (y * p) = 0 := by rw [hqy.left_comm, hqp, mul_zero]
      have hmix₂ : (x * p) * q = 0 := by rw [mul_assoc, hpq, mul_zero]
      have hcorner : (x * p) * (y * p) = p := by
        calc
          (x * p) * (y * p) = x * (p * y) * p := by simp only [mul_assoc]
          _ = x * (y * p) * p := by rw [hpy.eq]
          _ = (x * y) * (p * p) := by simp only [mul_assoc]
          _ = p := by rw [hxy, hpp, one_mul]
      rw [add_mul, mul_add, mul_add, hqq, hmix₁, hmix₂, hcorner,
        add_zero, zero_add, add_comm q p, hsum]
    have hxy : ((z : ℂ)⁻¹ • φ (affine a₀ a₁)) * ((z : ℂ) • φ b) = 1 := by
      rw [smul_mul_smul_comm, inv_mul_cancel₀ (Circle.coe_ne_zero z), one_smul,
        ← map_mul, hleft, map_one]
    have hyx : ((z : ℂ) • φ b) * ((z : ℂ)⁻¹ • φ (affine a₀ a₁)) = 1 := by
      rw [smul_mul_smul_comm, mul_inv_cancel₀ (Circle.coe_ne_zero z), one_smul,
        ← map_mul, hright, map_one]
    change φ (affineNegativeFactor a₀ a₁ b * affineNegativeInverse a₀ b) = φ 1 ∧
      φ (affineNegativeInverse a₀ b * affineNegativeFactor a₀ a₁ b) = φ 1
    simp only [map_mul, map_one, hfactorValue, hinverseValue]
    exact ⟨hprod _ _ (hqy.smul_right (z : ℂ)) hxy,
      hprod _ _ (hqx.smul_right (z : ℂ)⁻¹) hyx⟩
  exact ⟨hfactor, hinverse, eval_injective (funext fun z ↦ (hvalues z).1),
    eval_injective (funext fun z ↦ (hvalues z).2)⟩

/-- The positive factor as a unit of the positive algebra, with the specified inverse. -/
def affinePositiveFactorUnit (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) : (positiveSubalgebra (A := A))ˣ where
  val := ⟨affinePositiveFactor a₀ a₁ b,
    (affinePositiveFactor_unit_data a₀ a₁ hbase b hleft hright).1⟩
  inv := ⟨affinePositiveInverse a₀ b,
    (affinePositiveFactor_unit_data a₀ a₁ hbase b hleft hright).2.1⟩
  val_inv := Subtype.ext (affinePositiveFactor_unit_data a₀ a₁ hbase b hleft hright).2.2.1
  inv_val := Subtype.ext (affinePositiveFactor_unit_data a₀ a₁ hbase b hleft hright).2.2.2

/-- The negative factor as a unit of the negative algebra, with the corrected inverse. -/
def affineNegativeFactorUnit (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) : (negativeSubalgebra (A := A))ˣ where
  val := ⟨affineNegativeFactor a₀ a₁ b,
    (affineNegativeFactor_unit_data a₀ a₁ hbase b hleft hright).1⟩
  inv := ⟨affineNegativeInverse a₀ b,
    (affineNegativeFactor_unit_data a₀ a₁ hbase b hleft hright).2.1⟩
  val_inv := Subtype.ext (affineNegativeFactor_unit_data a₀ a₁ hbase b hleft hright).2.2.1
  inv_val := Subtype.ext (affineNegativeFactor_unit_data a₀ a₁ hbase b hleft hright).2.2.2

/-- KL06: factor a normalized affine series using the projector from its specified inverse. -/
theorem affine_factorization (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) :
    affine a₀ a₁ = affinePositiveFactor a₀ a₁ b * affineNegativeFactor a₀ a₁ b *
      affine (1 - affineBottIdempotent a₀ b) (affineBottIdempotent a₀ b) := by
  /- Stage 1: use the same q=a₀b₀ and p=1-q as in both one-sided units.
  KL05 gives their commutation with the affine coefficients, and KL06 gives
  orthogonality and p+q=1.
  Stage 2: expand (p+σq)(q+z⁻¹σp)(q+zp). The mixed products vanish, and
  the surviving expression is σq+σp=σ. Coefficient identities or injectivity
  of circle evaluation turn this into the displayed Wiener-algebra equality. -/
  classical
  let p : A := affineBottIdempotent a₀ b
  let q : A := 1 - p
  have hq : q = a₀ * b 0 := by simp [q, p, affineBottIdempotent]
  have hp : p = 1 - q := by simp [q]
  have hqq : q * q = q := by
    rw [hq]
    exact (affine_complement_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hpp : p * p = p :=
    (affineBottIdempotent_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hpq : p * q = 0 := by rw [hp, sub_mul, one_mul, hqq, sub_self]
  have hqp : q * p = 0 := by rw [hp, mul_sub, mul_one, hqq, sub_self]
  have hsum : p + q = 1 := by dsimp [q]; abel
  have hqa₀ : Commute q a₀ := by
    rw [hq]
    exact (Commute.refl a₀).mul_left
      (affine_inverse_commute a₀ a₁ hbase b hleft hright 0).1.symm
  have hqa₁ : Commute q a₁ := by
    rw [eq_sub_of_add_eq' hbase]
    exact (Commute.one_right q).sub_right hqa₀
  -- Fourier uniqueness reduces the actual series equality to its circle values.
  apply eval_injective
  funext z
  have hsingle (k : ℤ) (a : A) :
      eval (lp.single 1 k a : WienerLoop A) z = (z : ℂ) ^ k • a := by
    change (∑' n : ℤ, (z : ℂ) ^ n •
      lp.single (E := fun _ : ℤ ↦ A) 1 k a n) = _
    rw [tsum_eq_single k]
    · simp
    · intro n hn
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 k a hn, smul_zero]
  have hadd (f g : WienerLoop A) : (f + g).eval z = f.eval z + g.eval z := by
    have hs (x : WienerLoop A) : Summable (fun n : ℤ ↦ (z : ℂ) ^ n • x n) := by
      have hx : Summable (fun n : ℤ ↦ ‖x n‖) := by simpa using x.2.summable
      apply Summable.of_norm
      simpa only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul] using hx
    change (∑' n : ℤ, (z : ℂ) ^ n • (f n + g n)) = _
    simp_rw [smul_add]
    exact (hs f).tsum_add (hs g)
  let φ : WienerLoop A →+* A :=
    { toFun := fun f ↦ f.eval z
      map_one' := by
        change eval (lp.single 1 0 (1 : A) : WienerLoop A) z = 1
        simp [hsingle]
      map_mul' := fun f g ↦ eval_mul f g z
      map_zero' := by simp [eval]
      map_add' := hadd }
  have hφ (k : ℤ) (a : A) : φ (lp.single 1 k a) = (z : ℂ) ^ k • a := hsingle k a
  have ha (x y : A) : φ (affine x y) = x + (z : ℂ) • y := by
    change φ (lp.single 1 0 x + lp.single 1 1 y) = _
    simp only [map_add, hφ, zpow_zero, one_smul, zpow_one]
  have hpositive : φ (affinePositiveFactor a₀ a₁ b) = p + φ (affine a₀ a₁) * q := by
    change φ (affine (p + a₀ * q) (a₁ * q)) = _
    rw [ha, ha, add_mul, smul_mul_assoc, add_assoc]
  have hnegative : φ (affineNegativeFactor a₀ a₁ b) =
      q + ((z : ℂ)⁻¹ • φ (affine a₀ a₁)) * p := by
    change φ (lp.single 1 0 (q + a₁ * p) + lp.single 1 (-1) (a₀ * p)) = _
    simp only [map_add, hφ, zpow_zero, one_smul, zpow_neg_one, ha,
      smul_add, add_mul, smul_mul_assoc, smul_smul]
    rw [inv_mul_cancel₀ (Circle.coe_ne_zero z), one_smul]
    abel
  have hbott : φ (affine (1 - affineBottIdempotent a₀ b)
      (affineBottIdempotent a₀ b)) = q + (z : ℂ) • p := ha q p
  let x : A := φ (affine a₀ a₁)
  have hqx : Commute q x := by
    dsimp [x]
    rw [ha]
    exact hqa₀.add_right (hqa₁.smul_right (z : ℂ))
  have hpx : Commute p x := by rw [hp]; exact (Commute.one_left x).sub_left hqx
  -- First cancel the negative Fourier shift against the Bott factor in the p corner.
  have hinner₁ : q * ((z : ℂ) • p) = 0 := by
    rw [mul_smul_comm, hqp, smul_zero]
  have hinner₂ : (((z : ℂ)⁻¹ • x) * p) * q = 0 := by
    rw [mul_assoc, hpq, mul_zero]
  have hinner₃ : (((z : ℂ)⁻¹ • x) * p) * ((z : ℂ) • p) = x * p := by
    rw [smul_mul_assoc, smul_mul_smul_comm, inv_mul_cancel₀ (Circle.coe_ne_zero z),
      one_smul, mul_assoc, hpp]
  have hinner : (q + ((z : ℂ)⁻¹ • x) * p) * (q + (z : ℂ) • p) = q + x * p := by
    rw [add_mul, mul_add, mul_add, hqq, hinner₁, hinner₂, hinner₃,
      add_zero, zero_add]
  -- Orthogonality removes the mixed corners; the surviving sum is x(p + q) = x.
  have houter₁ : p * (x * p) = x * p := by rw [hpx.left_comm, hpp]
  have houter₂ : (x * q) * q = x * q := by rw [mul_assoc, hqq]
  have houter₃ : (x * q) * (x * p) = 0 := by
    calc
      (x * q) * (x * p) = x * (q * x) * p := by simp only [mul_assoc]
      _ = x * (x * q) * p := by rw [hqx.eq]
      _ = (x * x) * (q * p) := by simp only [mul_assoc]
      _ = 0 := by rw [hqp, mul_zero]
  have houter : (p + x * q) * (q + x * p) = x := by
    rw [add_mul, mul_add, mul_add, hpq, houter₁, houter₂, houter₃,
      zero_add, add_zero, ← mul_add, hsum, mul_one]
  change φ (affine a₀ a₁) = φ (affinePositiveFactor a₀ a₁ b *
    affineNegativeFactor a₀ a₁ b *
      affine (1 - affineBottIdempotent a₀ b) (affineBottIdempotent a₀ b))
  simp only [map_mul, hpositive, hnegative, hbott]
  change x = (p + x * q) * (q + ((z : ℂ)⁻¹ • x) * p) * (q + (z : ℂ) • p)
  rw [mul_assoc, hinner, houter]

/-- The radial factor contraction, before right normalization at the circle base point. -/
def affineContraction (a₀ a₁ : A) (b : WienerLoop A)
    (t : unitInterval) (z : Circle) : A :=
  let p := affineBottIdempotent a₀ b
  let q := 1 - p
  (p + a₀ * q + (((t : ℝ) : ℂ) * (z : ℂ)) • (a₁ * q)) *
    (q + a₁ * p + (((t : ℝ) : ℂ) * (↑(z⁻¹) : ℂ)) • (a₀ * p)) *
    ((z : ℂ) • p + q)

/-- One-sided Wiener inverses remain inverse under radial evaluation on the closed disk. -/
theorem isUnit_affineContraction (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) (t : unitInterval) (z : Circle) :
    IsUnit (affineContraction a₀ a₁ b t z) := by
  /- Stage 1: a one-sided absolutely summable series can be evaluated at
  any w with ‖w‖≤1. Absolute convergence permits multiplication of the
  sums, so this evaluation preserves the two inverse identities.
  Stage 2: evaluate the specified positive unit at w=t*z and the specified
  negative unit, considered as a series in z⁻¹, at w=t*z⁻¹. These are
  exactly the first and second displayed factors, and both are units.
  Stage 3: the third factor has inverse z⁻¹p+q by orthogonality. Their
  ordered product is a unit. This also works at t=0 and t=1; no continuation
  beyond the closed disk and no finite-support inverse are assumed. -/
  classical
  -- Closed-disk evaluation is multiplicative on either one-sided coefficient algebra.
  -- Natural absolute degrees avoid an artificial nonzero assumption at radius zero.
  let ev (w : ℂ) (f : WienerLoop A) : A := ∑' n : ℤ, w ^ n.natAbs • f n
  have hsingle (w : ℂ) (k : ℤ) (a : A) :
      ev w (lp.single 1 k a) = w ^ k.natAbs • a := by
    dsimp only [ev]
    rw [tsum_eq_single k]
    · simp
    · intro n hn
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 k a hn, smul_zero]
  have hone (w : ℂ) : ev w 1 = 1 := by
    change ev w (lp.single 1 0 1) = 1
    simp [hsingle]
  have hsum (w : ℂ) (hw : ‖w‖ ≤ 1) (f : WienerLoop A) :
      Summable (fun n : ℤ ↦ w ^ n.natAbs • f n) := by
    have hf : Summable (fun n : ℤ ↦ ‖f n‖) := by simpa using f.2.summable
    apply hf.of_norm_bounded
    intro n
    rw [norm_smul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw)
  have hadd (w : ℂ) (hw : ‖w‖ ≤ 1) (f g : WienerLoop A) :
      ev w (f + g) = ev w f + ev w g := by
    change (∑' n : ℤ, w ^ n.natAbs • (f n + g n)) = _
    simp_rw [smul_add]
    exact (hsum w hw f).tsum_add (hsum w hw g)
  have hmul (w : ℂ) (hw : ‖w‖ ≤ 1) (f g : WienerLoop A)
      (hhalf : ∀ i j : ℤ, f i ≠ 0 → g j ≠ 0 →
        (i + j).natAbs = i.natAbs + j.natAbs) :
      ev w (f * g) = ev w f * ev w g := by
    have hweight (n : ℤ) : ‖w ^ n.natAbs‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hw
    have hf : Summable (fun k : ℤ ↦ ‖f k‖) := by simpa using f.2.summable
    have hg : Summable (fun k : ℤ ↦ ‖g k‖) := by simpa using g.2.summable
    have hmajor : Summable (fun p : ℤ × ℤ ↦ ‖f p.2‖ * ‖g (p.1 - p.2)‖) := by
      apply (hf.mul_of_nonneg hg (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).comp_injective
        (i := fun p : ℤ × ℤ ↦ (p.2, p.1 - p.2))
      intro p q h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp at h₁ h₂
      exact Prod.ext (by omega) h₁
    have hdouble : Summable (fun p : ℤ × ℤ ↦
        w ^ p.1.natAbs • (f p.2 * g (p.1 - p.2))) := by
      apply hmajor.of_norm_bounded
      intro p
      calc
        _ = ‖w ^ p.1.natAbs‖ * ‖f p.2 * g (p.1 - p.2)‖ := norm_smul _ _
        _ ≤ 1 * ‖f p.2 * g (p.1 - p.2)‖ :=
          mul_le_mul_of_nonneg_right (hweight _) (norm_nonneg _)
        _ ≤ ‖f p.2‖ * ‖g (p.1 - p.2)‖ := by
          simpa using _root_.norm_mul_le (f p.2) (g (p.1 - p.2))
    have heval (a : WienerLoop A) : Summable (fun k : ℤ ↦ w ^ k.natAbs • a k) := by
      have ha : Summable (fun k : ℤ ↦ ‖a k‖) := by simpa using a.2.summable
      apply ha.of_norm_bounded
      intro k
      calc
        _ = ‖w ^ k.natAbs‖ * ‖a k‖ := norm_smul _ _
        _ ≤ 1 * ‖a k‖ := mul_le_mul_of_nonneg_right (hweight _) (norm_nonneg _)
        _ = ‖a k‖ := one_mul _
    change (∑' n : ℤ, w ^ n.natAbs • ∑' k : ℤ, f k * g (n - k)) = _
    calc
      _ = ∑' n : ℤ, ∑' k : ℤ, w ^ n.natAbs • (f k * g (n - k)) := by
        apply tsum_congr
        intro n
        exact (tsum_const_smul'' _).symm
      _ = ∑' k : ℤ, ∑' n : ℤ, w ^ n.natAbs • (f k * g (n - k)) :=
        hdouble.tsum_comm.symm
      _ = ∑' k : ℤ, ∑' j : ℤ, (w ^ k.natAbs • f k) * (w ^ j.natAbs • g j) := by
        apply tsum_congr
        intro k
        rw [← (Equiv.addRight k).tsum_eq]
        apply tsum_congr
        intro j
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        by_cases hk : f k = 0
        · simp [hk]
        by_cases hj : g j = 0
        · simp [hj]
        rw [add_comm j k, hhalf k j hk hj, pow_add, mul_smul, smul_mul_assoc,
          mul_smul_comm]
      _ = ∑' k : ℤ, (w ^ k.natAbs • f k) * (∑' j : ℤ, w ^ j.natAbs • g j) := by
        apply tsum_congr
        intro k
        exact (heval g).tsum_mul_left _
      _ = _ := (heval f).tsum_mul_right _
  have hunit (w : ℂ) (hw : ‖w‖ ≤ 1) (f g : WienerLoop A)
      (hside : (∀ n : ℤ, n < 0 → f n = 0 ∧ g n = 0) ∨
        (∀ n : ℤ, 0 < n → f n = 0 ∧ g n = 0))
      (hfg : f * g = 1) (hgf : g * f = 1) : IsUnit (ev w f) := by
    have hhalf (i j : ℤ) (hi : f i ≠ 0) (hj : g j ≠ 0) :
        (i + j).natAbs = i.natAbs + j.natAbs := by
      rcases hside with hpos | hneg
      · exact Int.natAbs_add_of_nonneg
          (by by_contra h; exact hi (hpos i (by omega)).1)
          (by by_contra h; exact hj (hpos j (by omega)).2)
      · exact Int.natAbs_add_of_nonpos
          (by by_contra h; exact hi (hneg i (by omega)).1)
          (by by_contra h; exact hj (hneg j (by omega)).2)
    have hhalf' (i j : ℤ) (hi : g i ≠ 0) (hj : f j ≠ 0) :
        (i + j).natAbs = i.natAbs + j.natAbs := by
      rw [add_comm i j, hhalf j i hj hi, Nat.add_comm]
    refine ⟨⟨ev w f, ev w g, ?_, ?_⟩, rfl⟩
    · rw [← hmul w hw f g hhalf, hfg, hone]
    · rw [← hmul w hw g f hhalf', hgf, hone]
  -- Apply this to the actual positive and negative units, with their supplied inverse b.
  let p : A := affineBottIdempotent a₀ b
  let q : A := 1 - p
  let wpos : ℂ := ((t : ℝ) : ℂ) * (z : ℂ)
  let wneg : ℂ := ((t : ℝ) : ℂ) * (↑(z⁻¹) : ℂ)
  have hw (u : Circle) : ‖((t : ℝ) : ℂ) * (u : ℂ)‖ ≤ 1 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    rw [abs_of_nonneg t.property.1]
    exact t.property.2
  obtain ⟨hfpos, hgpos, hfgpos, hgfpos⟩ :=
    affinePositiveFactor_unit_data a₀ a₁ hbase b hleft hright
  obtain ⟨hfneg, hgneg, hfgneg, hgfneg⟩ :=
    affineNegativeFactor_unit_data a₀ a₁ hbase b hleft hright
  have hpos := hunit wpos (hw z) _ _
    (Or.inl (fun n hn ↦ ⟨hfpos n hn, hgpos n hn⟩)) hfgpos hgfpos
  have hneg := hunit wneg (hw z⁻¹) _ _
    (Or.inr (fun n hn ↦ ⟨hfneg n hn, hgneg n hn⟩)) hfgneg hgfneg
  have hposValue : ev wpos (affinePositiveFactor a₀ a₁ b) =
      p + a₀ * q + wpos • (a₁ * q) := by
    change ev wpos (lp.single 1 0 (p + a₀ * q) + lp.single 1 1 (a₁ * q)) = _
    rw [hadd wpos (hw z), hsingle, hsingle]
    simp
  have hnegValue : ev wneg (affineNegativeFactor a₀ a₁ b) =
      q + a₁ * p + wneg • (a₀ * p) := by
    change ev wneg (lp.single 1 0 (q + a₁ * p) + lp.single 1 (-1) (a₀ * p)) = _
    rw [hadd wneg (hw z⁻¹), hsingle, hsingle]
    simp
  rw [hposValue] at hpos
  rw [hnegValue] at hneg
  -- The same complementary idempotents make the Bott factor a unit on the circle.
  have hpp : p * p = p :=
    (affineBottIdempotent_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hqq : q * q = q := by
    dsimp only [q]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpp, sub_self, sub_zero]
  have hpq : p * q = 0 := by dsimp only [q]; rw [mul_sub, mul_one, hpp, sub_self]
  have hqp : q * p = 0 := by dsimp only [q]; rw [sub_mul, one_mul, hpp, sub_self]
  have hpqsum : p + q = 1 := by dsimp only [q]; abel
  have hprod (c d : ℂ) (hcd : c * d = 1) :
      (c • p + q) * (d • p + q) = 1 := by
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, hcd, one_smul, hpp,
      smul_mul_assoc, hpq, smul_zero, mul_smul_comm, hqp, smul_zero, hqq,
      add_zero, zero_add, hpqsum]
  have hbott : IsUnit ((z : ℂ) • p + q) := by
    exact ⟨⟨(z : ℂ) • p + q, (z : ℂ)⁻¹ • p + q,
      hprod _ _ (mul_inv_cancel₀ (Circle.coe_ne_zero z)),
      hprod _ _ (inv_mul_cancel₀ (Circle.coe_ne_zero z))⟩, rfl⟩
  exact (hpos.mul hneg).mul hbott

/-- The explicit contraction with right normalization, preserving the base point. -/
def affineNormalizedContraction (a₀ a₁ : A) (b : WienerLoop A)
    (t : unitInterval) (z : Circle) : A :=
  affineContraction a₀ a₁ b t z * Ring.inverse (affineContraction a₀ a₁ b t 1)

/-- The normalized family is jointly continuous, including both parameter endpoints. -/
theorem continuous_affineNormalizedContraction (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) :
    Continuous (fun tz : unitInterval × Circle ↦
      affineNormalizedContraction a₀ a₁ b tz.1 tz.2) := by
  /- Stage 1: the unnormalized expression is a finite polynomial in t,z,z⁻¹,
  hence is jointly continuous. Its restriction to z=1 is continuous as well.
  Stage 2: every restricted value is a unit by isUnit_affineContraction.
  Inversion on the open unit group of the Banach algebra is continuous.
  Multiplication gives joint continuity of the displayed right normalization. -/
  -- The actual radial product is a finite continuous expression.
  have hfamily : Continuous (fun tz : unitInterval × Circle ↦
      affineContraction a₀ a₁ b tz.1 tz.2) := by
    unfold affineContraction
    fun_prop
  have hbasepoint : Continuous (fun tz : unitInterval × Circle ↦
      affineContraction a₀ a₁ b tz.1 1) :=
    hfamily.comp (continuous_fst.prodMk continuous_const)
  -- Every base-point value is a unit, so Banach-algebra inversion is continuous there.
  have hinverse : Continuous (fun tz : unitInterval × Circle ↦
      Ring.inverse (affineContraction a₀ a₁ b tz.1 1)) := by
    apply continuous_iff_continuousAt.mpr
    intro tz
    obtain ⟨u, hu⟩ := isUnit_affineContraction a₀ a₁ hbase b hleft hright tz.1 1
    have hi : ContinuousAt Ring.inverse (affineContraction a₀ a₁ b tz.1 1) := by
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact hi.comp (f := fun p : unitInterval × Circle ↦
      affineContraction a₀ a₁ b p.1 1) hbasepoint.continuousAt
  exact hfamily.mul hinverse

/-- The normalized family has the specified endpoints and remains based and invertible. -/
theorem affineNormalizedContraction_spec (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) :
    (∀ z : Circle, affineNormalizedContraction a₀ a₁ b 0 z =
      (affine (1 - affineBottIdempotent a₀ b) (affineBottIdempotent a₀ b)).eval z) ∧
      (∀ z : Circle, affineNormalizedContraction a₀ a₁ b 1 z = (affine a₀ a₁).eval z) ∧
      (∀ t : unitInterval, affineNormalizedContraction a₀ a₁ b t 1 = 1) ∧
      (∀ (t : unitInterval) (z : Circle),
        IsUnit (affineNormalizedContraction a₀ a₁ b t z)) := by
  /- Stage 1: at radius one, the factorization gives σ(z), and hbase gives
  σ(1)=1. Thus right normalization preserves the intended affine endpoint.
  Stage 2: at radius zero the first two factors form a constant unit c.
  KL05 implies that c commutes with p and q; it therefore commutes with
  zp+q. The normalized value c(zp+q)c⁻¹ equals zp+q, not just an unspecified
  conjugate of this Bott loop. The same b determines every occurrence of p.
  Stage 3: throughout the interval the base-point value times its own inverse
  is one. All values remain units by isUnit_affineContraction and closure of
  units under inversion and multiplication, with the displayed factor order. -/
  classical
  let p : A := affineBottIdempotent a₀ b
  let q : A := 1 - p
  have hq : q = a₀ * b 0 := by simp [q, p, affineBottIdempotent]
  have hp : p = 1 - q := by simp [q]
  have hpqsum : p + q = 1 := by dsimp only [q]; abel
  have hpp : p * p = p :=
    (affineBottIdempotent_isIdempotentElem a₀ a₁ hbase b hleft hright).eq
  have hpq : p * q = 0 := by dsimp only [q]; rw [mul_sub, mul_one, hpp, sub_self]
  have hqp : q * p = 0 := by dsimp only [q]; rw [sub_mul, one_mul, hpp, sub_self]
  have hqa₀ : Commute q a₀ := by
    rw [hq]
    exact (Commute.refl a₀).mul_left
      (affine_inverse_commute a₀ a₁ hbase b hleft hright 0).1.symm
  have hqa₁ : Commute q a₁ := by
    rw [eq_sub_of_add_eq' hbase]
    exact (Commute.one_right q).sub_right hqa₀
  -- Circle evaluation identifies the radius-one product with the original factorization.
  have hsingle (z : Circle) (k : ℤ) (a : A) :
      eval (lp.single 1 k a : WienerLoop A) z = (z : ℂ) ^ k • a := by
    change (∑' n : ℤ, (z : ℂ) ^ n •
      lp.single (E := fun _ : ℤ ↦ A) 1 k a n) = _
    rw [tsum_eq_single k]
    · simp
    · intro n hn
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 k a hn, smul_zero]
  have hadd (z : Circle) (f g : WienerLoop A) :
      (f + g).eval z = f.eval z + g.eval z := by
    have hs (x : WienerLoop A) : Summable (fun n : ℤ ↦ (z : ℂ) ^ n • x n) := by
      have hx : Summable (fun n : ℤ ↦ ‖x n‖) := by simpa using x.2.summable
      apply Summable.of_norm
      simpa only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul] using hx
    change (∑' n : ℤ, (z : ℂ) ^ n • (f n + g n)) = _
    simp_rw [smul_add]
    exact (hs f).tsum_add (hs g)
  let φ (z : Circle) : WienerLoop A →+* A :=
    { toFun := fun f ↦ f.eval z
      map_one' := by
        change eval (lp.single 1 0 (1 : A) : WienerLoop A) z = 1
        simp [hsingle]
      map_mul' := fun f g ↦ eval_mul f g z
      map_zero' := by simp [eval]
      map_add' := hadd z }
  have hφ (z : Circle) (k : ℤ) (a : A) :
      φ z (lp.single 1 k a) = (z : ℂ) ^ k • a := hsingle z k a
  have ha (z : Circle) (x y : A) : φ z (affine x y) = x + (z : ℂ) • y := by
    change φ z (lp.single 1 0 x + lp.single 1 1 y) = _
    simp only [map_add, hφ, zpow_zero, one_smul, zpow_one]
  have hpositive (z : Circle) : φ z (affinePositiveFactor a₀ a₁ b) =
      p + a₀ * q + (z : ℂ) • (a₁ * q) := ha z _ _
  have hnegative (z : Circle) : φ z (affineNegativeFactor a₀ a₁ b) =
      q + a₁ * p + (z : ℂ)⁻¹ • (a₀ * p) := by
    change φ z (lp.single 1 0 (q + a₁ * p) + lp.single 1 (-1) (a₀ * p)) = _
    simp only [map_add, hφ, zpow_zero, one_smul, zpow_neg_one]
  have hbott (z : Circle) : φ z (affine q p) = (z : ℂ) • p + q := by
    rw [ha, add_comm]
  have hone (z : Circle) : affineContraction a₀ a₁ b 1 z = (affine a₀ a₁).eval z := by
    have hf := congrArg (φ z) (affine_factorization a₀ a₁ hbase b hleft hright)
    change φ z (affine a₀ a₁) =
      φ z (affinePositiveFactor a₀ a₁ b * affineNegativeFactor a₀ a₁ b * affine q p) at hf
    simp only [map_mul, hpositive, hnegative, hbott] at hf
    simpa [affineContraction, p, q, Circle.coe_inv, φ] using hf.symm
  have honeBase : affineContraction a₀ a₁ b 1 1 = 1 := by
    rw [hone]
    change φ 1 (affine a₀ a₁) = 1
    rw [ha]
    simpa only [Circle.coe_one, one_smul] using hbase
  -- At radius zero, the constant product commutes with the same p and q.
  -- This proves the exact Bott endpoint, not merely a conjugate of it.
  let c : A := (p + a₀ * q) * (q + a₁ * p)
  have hzero (z : Circle) : affineContraction a₀ a₁ b 0 z = c * ((z : ℂ) • p + q) := by
    simp [affineContraction, c, p, q]
  have hzeroBase : affineContraction a₀ a₁ b 0 1 = c := by
    rw [hzero]
    simp only [Circle.coe_one, one_smul, hpqsum, mul_one]
  have hc : IsUnit c := by
    rw [← hzeroBase]
    exact isUnit_affineContraction a₀ a₁ hbase b hleft hright 0 1
  have hpa₀ : Commute p a₀ := by rw [hp]; exact (Commute.one_left a₀).sub_left hqa₀
  have hpa₁ : Commute p a₁ := by rw [hp]; exact (Commute.one_left a₁).sub_left hqa₁
  have hpqcomm : Commute p q := by change p * q = q * p; rw [hpq, hqp]
  have hpc : Commute p c :=
    ((Commute.refl p).add_right (hpa₀.mul_right hpqcomm)).mul_right
      (hpqcomm.add_right (hpa₁.mul_right (Commute.refl p)))
  have hqc : Commute q c := (Commute.one_left c).sub_left hpc
  have hcbott (z : Circle) : Commute c ((z : ℂ) • p + q) :=
    (hpc.symm.smul_right (z : ℂ)).add_right hqc.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    change affineContraction a₀ a₁ b 0 z * Ring.inverse
      (affineContraction a₀ a₁ b 0 1) = φ z (affine q p)
    rw [hzero, hzeroBase, (hcbott z).eq, mul_assoc,
      Ring.mul_inverse_cancel c hc, mul_one]
    exact (hbott z).symm
  · intro z
    unfold affineNormalizedContraction
    rw [honeBase, Ring.inverse_one, mul_one, hone]
  · intro t
    exact Ring.mul_inverse_cancel _
      (isUnit_affineContraction a₀ a₁ hbase b hleft hright t 1)
  · intro t z
    exact (isUnit_affineContraction a₀ a₁ hbase b hleft hright t z).mul
      (isUnit_affineContraction a₀ a₁ hbase b hleft hright t 1).ringInverse

/-- The factor-contraction homotopy from the specified Bott loop to the affine loop. -/
def affineBottHomotopy (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) :
    ContinuousMap.HomotopyWith
      ((affine (1 - affineBottIdempotent a₀ b) (affineBottIdempotent a₀ b)).toContinuousMap)
      ((affine a₀ a₁).toContinuousMap) (fun f ↦ f 1 = 1 ∧ ∀ z : Circle, IsUnit (f z)) where
  toFun tz := affineNormalizedContraction a₀ a₁ b tz.1 tz.2
  continuous_toFun := continuous_affineNormalizedContraction a₀ a₁ hbase b hleft hright
  map_zero_left := (affineNormalizedContraction_spec a₀ a₁ hbase b hleft hright).1
  map_one_left := (affineNormalizedContraction_spec a₀ a₁ hbase b hleft hright).2.1
  prop' t := ⟨(affineNormalizedContraction_spec a₀ a₁ hbase b hleft hright).2.2.1 t,
    (affineNormalizedContraction_spec a₀ a₁ hbase b hleft hright).2.2.2 t⟩

end AtiyahSinger.WienerLoop

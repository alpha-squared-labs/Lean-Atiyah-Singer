/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Absolutely summable Laurent series in a Banach algebra

Public module ID: M1053.

The Wiener algebra is the actual space of bilateral absolutely summable coefficients,
with convolution multiplication. Its positive subalgebra retains exactly the coefficients
of nonnegative degree. No finite Laurent polynomial condition is imposed on an inverse.

Sources: Karoubi, K-Theory, III.1.17--1.18, pp.117--118, and Lemma 1.23, p.121.
The Banach-space and Fourier uniqueness facts are supporting analysis, not separately
numbered results in that passage. The coefficient algebra need not be commutative.
The normalization of an affine loop is stated explicitly as a₀ + a₁ = 1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The standard Wiener coefficient space, with the existing ℓ¹ norm and completeness. -/
abbrev WienerLoop (A : Type*) [NormedAddCommGroup A] : Type _ :=
  lp (fun _ : ℤ ↦ A) 1

namespace WienerLoop

open MeasureTheory

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Absolute summability is preserved by the actual bilateral convolution. -/
theorem memℓp_convolution (f g : WienerLoop A) :
    Memℓp (fun n : ℤ ↦ ∑' k : ℤ, f k * g (n - k)) 1 := by
  -- The change of indices (n, k) ↦ (k, n - k) gives a summable majorant.
  have hf : Summable (fun k : ℤ ↦ ‖f k‖) := by simpa using f.2.summable
  have hg : Summable (fun k : ℤ ↦ ‖g k‖) := by simpa using g.2.summable
  have hdouble : Summable (fun p : ℤ × ℤ ↦ ‖f p.2 * g (p.1 - p.2)‖) := by
    apply (hf.mul_norm hg).comp_injective
      (i := fun p : ℤ × ℤ ↦ (p.2, p.1 - p.2))
    intro p q h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp at h₁ h₂
    exact Prod.ext (by omega) h₁
  -- Each inner sum converges, and the sum of its norms has a summable upper bound.
  apply memℓp_gen
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hdouble.prod
  intro n
  exact norm_tsum_le_tsum_norm (hdouble.prod_factor n)

/-- Convolution of absolutely summable bilateral series, with its actual coefficients. -/
def convolution (f g : WienerLoop A) : WienerLoop A :=
  ⟨fun n ↦ ∑' k : ℤ, f k * g (n - k), memℓp_convolution f g⟩

/-- The multiplication of the Wiener algebra is convolution, not pointwise multiplication. -/
instance instMul : Mul (WienerLoop A) := ⟨convolution⟩

/-- The identity series has its only nonzero coefficient at degree zero. -/
instance instOne : One (WienerLoop A) := ⟨lp.single 1 0 1⟩

/-- Absolutely summable convolution is associative, unital and distributive. -/
theorem convolution_ring_laws :
    (∀ f g h : WienerLoop A, f * g * h = f * (g * h)) ∧
    (∀ f : WienerLoop A, 1 * f = f) ∧
    (∀ f : WienerLoop A, f * 1 = f) ∧
    (∀ f g h : WienerLoop A, f * (g + h) = f * g + f * h) ∧
    (∀ f g h : WienerLoop A, (f + g) * h = f * h + g * h) := by
  -- Absolute convergence justifies every coefficientwise distribution and reindexing.
  have hconv (f g : WienerLoop A) (n : ℤ) :
      Summable (fun k : ℤ ↦ f k * g (n - k)) := by
    have hf : Summable (fun k : ℤ ↦ ‖f k‖) := by simpa using f.2.summable
    have hg : Summable (fun k : ℤ ↦ ‖g k‖) := by simpa using g.2.summable
    exact ((hf.mul_norm hg).comp_injective (i := fun k : ℤ ↦ (k, n - k))
      (fun _ _ h ↦ congrArg Prod.fst h)).of_norm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f g h
    apply lp.ext
    funext n
    -- The double sum is absolutely convergent, bounded by two ℓ¹ factors and ‖h‖.
    have hf : Summable (fun k : ℤ ↦ ‖f k‖) := by simpa using f.2.summable
    have hg : Summable (fun k : ℤ ↦ ‖g k‖) := by simpa using g.2.summable
    have hmajor : Summable (fun p : ℤ × ℤ ↦ ‖f p.2‖ * ‖g (p.1 - p.2)‖ * ‖h‖) := by
      apply ((hf.mul_of_nonneg hg (fun _ ↦ norm_nonneg _)
        (fun _ ↦ norm_nonneg _)).mul_right ‖h‖).comp_injective
        (i := fun p : ℤ × ℤ ↦ (p.2, p.1 - p.2))
      intro p q hpq
      have h₁ := congrArg Prod.fst hpq
      have h₂ := congrArg Prod.snd hpq
      dsimp at h₁ h₂
      exact Prod.ext (by omega) h₁
    have hdouble : Summable (fun p : ℤ × ℤ ↦
        (f p.2 * g (p.1 - p.2)) * h (n - p.1)) := by
      apply hmajor.of_norm_bounded
      intro p
      calc
        ‖f p.2 * g (p.1 - p.2) * h (n - p.1)‖
            ≤ (‖f p.2‖ * ‖g (p.1 - p.2)‖) * ‖h (n - p.1)‖ :=
          (_root_.norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (_root_.norm_mul_le _ _) (norm_nonneg _))
        _ ≤ (‖f p.2‖ * ‖g (p.1 - p.2)‖) * ‖h‖ :=
          mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) h _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    change (∑' j : ℤ, (∑' k : ℤ, f k * g (j - k)) * h (n - j)) =
      ∑' k : ℤ, f k * ∑' j : ℤ, g j * h (n - k - j)
    calc
      _ = ∑' j : ℤ, ∑' k : ℤ, (f k * g (j - k)) * h (n - j) := by
        apply tsum_congr
        intro j
        exact (hconv f g j).tsum_mul_right _ |>.symm
      _ = ∑' k : ℤ, ∑' j : ℤ, (f k * g (j - k)) * h (n - j) :=
        hdouble.tsum_comm.symm
      _ = ∑' k : ℤ, ∑' j : ℤ, (f k * g j) * h (n - k - j) := by
        apply tsum_congr
        intro k
        rw [← (Equiv.addRight k).tsum_eq]
        apply tsum_congr
        intro j
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        exact congrArg (fun m : ℤ ↦ f k * g j * h m) (by omega)
      _ = _ := by
        apply tsum_congr
        intro k
        simpa only [mul_assoc] using (hconv g h (n - k)).tsum_mul_left (f k)
  · intro f
    apply lp.ext
    funext n
    change (∑' k : ℤ, lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) (1 : A) k * f (n - k)) = f n
    rw [tsum_eq_single 0]
    · simp
    · intro k hk
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 1 hk, zero_mul]
  · intro f
    apply lp.ext
    funext n
    change (∑' k : ℤ, f k * lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) (1 : A) (n - k)) = f n
    rw [tsum_eq_single n]
    · simp
    · intro k hk
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 1 (by omega), mul_zero]
  · intro f g h
    apply lp.ext
    funext n
    change (∑' k : ℤ, f k * (g (n - k) + h (n - k))) =
      (∑' k : ℤ, f k * g (n - k)) + ∑' k : ℤ, f k * h (n - k)
    simp_rw [mul_add]
    exact (hconv f g n).tsum_add (hconv f h n)
  · intro f g h
    apply lp.ext
    funext n
    change (∑' k : ℤ, (f k + g k) * h (n - k)) =
      (∑' k : ℤ, f k * h (n - k)) + ∑' k : ℤ, g k * h (n - k)
    simp_rw [add_mul]
    exact (hconv f h n).tsum_add (hconv g h n)

/-- The usual convolution ring structure on the already fixed coefficient space. -/
instance instRing : Ring (WienerLoop A) where
  toAddCommGroup := (inferInstance : AddCommGroup (lp (fun _ : ℤ ↦ A) 1))
  mul_assoc := convolution_ring_laws.1
  one_mul := convolution_ring_laws.2.1
  mul_one := convolution_ring_laws.2.2.1
  left_distrib := convolution_ring_laws.2.2.2.1
  right_distrib := convolution_ring_laws.2.2.2.2
  zero_mul := by
    intro f
    ext n
    change (∑' k : ℤ, (0 : A) * f (n - k)) = 0
    simp
  mul_zero := by
    intro f
    ext n
    change (∑' k : ℤ, f k * (0 : A)) = 0
    simp

/-- The ℓ¹ convolution estimate, valid also for noncommutative coefficient algebras. -/
theorem norm_mul_le (f g : WienerLoop A) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  -- The coefficientwise majorant is a reindexing of the product of the two ℓ¹ sums.
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
  have hcoeff (n : ℤ) : ‖(f * g) n‖ ≤ ∑' k : ℤ, ‖f k‖ * ‖g (n - k)‖ := by
    have hnorm : Summable (fun k : ℤ ↦ ‖f k * g (n - k)‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun k ↦ _root_.norm_mul_le _ _) (hmajor.prod_factor n)
    exact (norm_tsum_le_tsum_norm hnorm).trans
      (hnorm.tsum_le_tsum (fun k ↦ _root_.norm_mul_le _ _) (hmajor.prod_factor n))
  -- Sum the estimate, interchange the nonnegative sums, and translate the inner index.
  have hfg : Summable (fun n : ℤ ↦ ‖(f * g) n‖) := by
    simpa using (f * g).2.summable
  calc
    ‖f * g‖ = ∑' n : ℤ, ‖(f * g) n‖ := by
      simpa using lp.norm_eq_tsum_rpow (by simp) (f * g)
    _ ≤ ∑' n : ℤ, ∑' k : ℤ, ‖f k‖ * ‖g (n - k)‖ :=
      hfg.tsum_le_tsum hcoeff hmajor.prod
    _ = ∑' k : ℤ, ∑' n : ℤ, ‖f k‖ * ‖g (n - k)‖ :=
      hmajor.tsum_comm.symm
    _ = ∑' k : ℤ, ‖f k‖ * ∑' n : ℤ, ‖g n‖ := by
      apply tsum_congr
      intro k
      have hshift : Summable (fun n : ℤ ↦ ‖g (n - k)‖) := by
        simpa [Equiv.subRight, Function.comp_def] using (Equiv.subRight k).summable_iff.mpr hg
      rw [hshift.tsum_mul_left]
      congr 1
      exact (Equiv.subRight k).tsum_eq (fun n : ℤ ↦ ‖g n‖)
    _ = (∑' k : ℤ, ‖f k‖) * ∑' n : ℤ, ‖g n‖ := hf.tsum_mul_right _
    _ = ‖f‖ * ‖g‖ := by
      congr 1
      · simpa using (lp.norm_eq_tsum_rpow (by simp) f).symm
      · simpa using (lp.norm_eq_tsum_rpow (by simp) g).symm

/-- The convolution ring with the original ℓ¹ norm and metric. -/
instance instNormedRing : NormedRing (WienerLoop A) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le

/-- Complex scalar multiplication commutes with convolution in either factor. -/
theorem convolution_smul_laws :
    (∀ (c : ℂ) (f g : WienerLoop A), (c • f) * g = c • (f * g)) ∧
    (∀ (c : ℂ) (f g : WienerLoop A), f * (c • g) = c • (f * g)) := by
  -- For each output index, the coefficient series is absolutely convergent.
  have hconv (f g : WienerLoop A) (n : ℤ) :
      Summable (fun k : ℤ ↦ f k * g (n - k)) := by
    have hf : Summable (fun k : ℤ ↦ ‖f k‖) := by simpa using f.2.summable
    have hg : Summable (fun k : ℤ ↦ ‖g k‖) := by simpa using g.2.summable
    exact ((hf.mul_norm hg).comp_injective (i := fun k : ℤ ↦ (k, n - k))
      (fun _ _ h ↦ congrArg Prod.fst h)).of_norm
  -- Complex scalars are central in A; no coefficient of A is commuted past another.
  constructor
  · intro c f g
    apply lp.ext
    funext n
    change (∑' k : ℤ, (c • f k) * g (n - k)) =
      c • ∑' k : ℤ, f k * g (n - k)
    simp_rw [smul_mul_assoc]
    exact (hconv f g n).tsum_const_smul c
  · intro c f g
    apply lp.ext
    funext n
    change (∑' k : ℤ, f k * (c • g (n - k))) =
      c • ∑' k : ℤ, f k * g (n - k)
    simp_rw [mul_smul_comm]
    exact (hconv f g n).tsum_const_smul c

/-- The standard complex algebra structure on the Wiener convolution algebra. -/
instance instAlgebra : Algebra ℂ (WienerLoop A) :=
  Algebra.ofModule convolution_smul_laws.1 convolution_smul_laws.2

/-- The algebra action has the original normed-space structure of ℓ¹. -/
instance instNormedAlgebra : NormedAlgebra ℂ (WienerLoop A) where
  norm_smul_le := norm_smul_le

/-- Evaluation on the unit circle by the absolutely convergent Laurent series. -/
def eval (f : WienerLoop A) (z : Circle) : A :=
  ∑' n : ℤ, (z : ℂ) ^ n • f n

/-- Circle evaluation is bounded by the coefficient ℓ¹ norm. -/
theorem norm_eval_le (f : WienerLoop A) (z : Circle) : ‖f.eval z‖ ≤ ‖f‖ := by
  -- Circle characters have norm one, so the coefficient norm is the majorant.
  have hf : Summable (fun n : ℤ ↦ ‖f n‖) := by simpa using f.2.summable
  have hterm : ∀ n : ℤ, ‖(z : ℂ) ^ n • f n‖ = ‖f n‖ := by
    intro n
    simp only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul]
  calc
    ‖f.eval z‖ ≤ ∑' n : ℤ, ‖(z : ℂ) ^ n • f n‖ :=
      norm_tsum_le_tsum_norm (by simpa only [hterm] using hf)
    _ = ∑' n : ℤ, ‖f n‖ := tsum_congr hterm
    _ = ‖f‖ := by simpa using (lp.norm_eq_tsum_rpow (by simp) f).symm

/-- The Fourier series defines a continuous loop, by uniform absolute convergence. -/
theorem continuous_eval (f : WienerLoop A) : Continuous f.eval := by
  -- Each circle character is continuous; one common ℓ¹ bound controls all points.
  have hf : Summable (fun n : ℤ ↦ ‖f n‖) := by simpa using f.2.summable
  apply continuous_tsum (fun n ↦ ?_) hf
  · intro n z
    simp only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul, le_refl]
  · exact ((continuous_subtype_val.zpow₀ _ (fun z ↦ Or.inl (Circle.coe_ne_zero z))).smul
      continuous_const)

/-- The actual continuous loop attached to a Wiener series. -/
def toContinuousMap (f : WienerLoop A) : C(Circle, A) :=
  ⟨f.eval, f.continuous_eval⟩

/-- Fourier uniqueness for Banach-valued absolutely summable Laurent series. -/
theorem eval_injective : Function.Injective (eval (A := A)) := by
  -- Recover one coefficient by the normalized Fourier integral on R/Z.
  have recover (f : WienerLoop A) (n : ℤ) :
      fourierCoeff (fun t : UnitAddCircle ↦ f.eval (AddCircle.toCircle t)) n = f n := by
    have hchar (k : ℤ) (t : UnitAddCircle) :
        ((AddCircle.toCircle t : Circle) : ℂ) ^ k = fourier k t := by
      simp only [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
    have hf : Summable (fun k : ℤ ↦ ‖f k‖) := by simpa using f.2.summable
    have hint (k : ℤ) : Integrable
        (fun t : UnitAddCircle ↦ fourier (-n) t • (fourier k t • f k))
        AddCircle.haarAddCircle := by
      exact ((fourier (-n)).continuous.smul
        ((fourier k).continuous.smul continuous_const)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hnorm : Summable (fun k : ℤ ↦ ∫ t : UnitAddCircle,
        ‖fourier (-n) t • (fourier k t • f k)‖ ∂AddCircle.haarAddCircle) := by
      simpa [norm_smul, fourier_apply] using hf
    calc
      _ = ∫ t : UnitAddCircle, ∑' k : ℤ,
          fourier (-n) t • (fourier k t • f k) ∂AddCircle.haarAddCircle := by
        simp only [fourierCoeff, eval, hchar, tsum_const_smul'']
      _ = ∑' k : ℤ, ∫ t : UnitAddCircle,
          fourier (-n) t • (fourier k t • f k) ∂AddCircle.haarAddCircle :=
        (integral_tsum_of_summable_integral_norm hint hnorm).symm
      _ = ∑' k : ℤ, (if k = n then f k else 0) := by
        apply tsum_congr
        intro k
        have hcoeff : (∫ t : UnitAddCircle, (fourier (-n) t) * (fourier k t)
            ∂AddCircle.haarAddCircle) = (if n = k then (1 : ℂ) else 0) := by
          simpa only [fourierCoeff, smul_eq_mul, Pi.single_apply] using
            congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) n
        calc
          _ = (∫ t : UnitAddCircle, (fourier (-n) t) * (fourier k t)
              ∂AddCircle.haarAddCircle) • f k := by
            simp_rw [smul_smul]
            exact integral_smul_const _ _
          _ = _ := by
            rw [hcoeff]
            by_cases hk : k = n
            · simp [hk]
            · simp [hk, Ne.symm hk]
      _ = f n := by simp
  intro f g heval
  apply lp.ext
  funext n
  rw [← recover f n, ← recover g n, heval]

/-- Evaluation respects convolution in the original order of the coefficients. -/
theorem eval_mul (f g : WienerLoop A) (z : Circle) :
    (f * g).eval z = f.eval z * g.eval z := by
  -- Absolute convergence supplies both the coefficientwise and double-sum operations.
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
      (z : ℂ) ^ p.1 • (f p.2 * g (p.1 - p.2))) := by
    apply hmajor.of_norm_bounded
    intro p
    simpa only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul] using
      _root_.norm_mul_le (f p.2) (g (p.1 - p.2))
  have heval (a : WienerLoop A) : Summable (fun k : ℤ ↦ (z : ℂ) ^ k • a k) := by
    have ha : Summable (fun k : ℤ ↦ ‖a k‖) := by simpa using a.2.summable
    apply ha.of_norm_bounded
    intro k
    simp only [norm_smul, norm_zpow, Circle.norm_coe, one_zpow, one_mul, le_refl]
  change (∑' n : ℤ, (z : ℂ) ^ n • ∑' k : ℤ, f k * g (n - k)) = _
  -- Interchange the two sums, then use n = j + k and the character multiplication law.
  calc
    _ = ∑' n : ℤ, ∑' k : ℤ, (z : ℂ) ^ n • (f k * g (n - k)) := by
      apply tsum_congr
      intro n
      exact (tsum_const_smul'' _).symm
    _ = ∑' k : ℤ, ∑' n : ℤ, (z : ℂ) ^ n • (f k * g (n - k)) :=
      hdouble.tsum_comm.symm
    _ = ∑' k : ℤ, ∑' j : ℤ, ((z : ℂ) ^ k • f k) * ((z : ℂ) ^ j • g j) := by
      apply tsum_congr
      intro k
      rw [← (Equiv.addRight k).tsum_eq]
      apply tsum_congr
      intro j
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      rw [zpow_add₀ (Circle.coe_ne_zero z), mul_comm, mul_smul, smul_mul_assoc,
        mul_smul_comm]
    _ = ∑' k : ℤ, ((z : ℂ) ^ k • f k) * g.eval z := by
      apply tsum_congr
      intro k
      exact (heval g).tsum_mul_left _
    _ = f.eval z * g.eval z := (heval f).tsum_mul_right _

/-- The positive Wiener algebra consists of series supported in nonnegative degrees. -/
def positiveSubalgebra : Subalgebra ℂ (WienerLoop A) where
  carrier := {f | ∀ n : ℤ, n < 0 → f n = 0}
  mul_mem' := by
    intro f g hf hg n hn
    change (∑' k : ℤ, f k * g (n - k)) = 0
    have hterm : ∀ k : ℤ, f k * g (n - k) = 0 := by
      intro k
      by_cases hk : k < 0
      · rw [hf k hk, zero_mul]
      · rw [hg (n - k) (by omega), mul_zero]
    simp only [hterm, tsum_zero]
  one_mem' := by
    intro n hn
    change lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) (1 : A) n = 0
    exact lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 1 (ne_of_lt hn)
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
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 1 (ne_of_lt hn), smul_zero]

/-- The bounded Fourier projection discards exactly the coefficients of negative degree. -/
def positivePart : WienerLoop A →L[ℂ] WienerLoop A := by
  let P : WienerLoop A →ₗ[ℂ] WienerLoop A :=
    { toFun := fun f ↦ ⟨fun n ↦ if 0 ≤ n then f n else 0,
        (lp.memℓp f).mono' (by
          intro n
          split_ifs <;> simp)⟩
      map_add' := by
        intro f g
        ext n
        change (if 0 ≤ n then f n + g n else 0) =
          (if 0 ≤ n then f n else 0) + (if 0 ≤ n then g n else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c f
        ext n
        change (if 0 ≤ n then c • f n else 0) = c • (if 0 ≤ n then f n else 0)
        split_ifs <;> simp }
  exact P.mkContinuous 1 (by
    intro f
    rw [one_mul]
    apply lp.norm_mono (by simp)
    intro n
    change ‖if 0 ≤ n then f n else 0‖ ≤ ‖f n‖
    split_ifs <;> simp)

/-- The positive projection has exactly the standard positive Wiener subalgebra as its range. -/
theorem range_positivePart :
    LinearMap.range (positivePart (A := A)).toLinearMap =
      (positiveSubalgebra (A := A)).toSubmodule := by
  -- The image consists exactly of sequences fixed by the coefficient cutoff.
  ext f
  constructor
  · rintro ⟨g, rfl⟩ n hn
    change (if 0 ≤ n then g n else 0) = 0
    simp only [not_le.mpr hn, ↓reduceIte]
  · intro hf
    refine ⟨f, ?_⟩
    apply lp.ext
    funext n
    change (if 0 ≤ n then f n else 0) = f n
    by_cases hn : 0 ≤ n
    · simp only [hn, ↓reduceIte]
    · simp only [hn, ↓reduceIte, hf n (lt_of_not_ge hn)]

/-- The positive subalgebra is closed in the actual ℓ¹ norm topology. -/
theorem isClosed_positiveSubalgebra :
    IsClosed (↑(positiveSubalgebra (A := A)) : Set (WienerLoop A)) := by
  -- Each negative coordinate condition is the kernel of a continuous evaluation.
  change IsClosed {f : WienerLoop A | ∀ n : ℤ, n < 0 → f n = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro hn
  exact isClosed_eq
    (lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℤ ↦ A) (p := 1) n).continuous continuous_const

/-- Translation of coefficient indices preserves absolute summability. -/
theorem memℓp_shift (f : WienerLoop A) (k : ℤ) : Memℓp (fun n ↦ f (n - k)) 1 := by
  -- Translation is a bijection of the coefficient indices.
  have hf : Summable (fun n : ℤ ↦ ‖f n‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using f.2.summable (by simp)
  apply memℓp_gen
  simp only [ENNReal.toReal_one, Real.rpow_one]
  exact (Equiv.subRight k).summable_iff.mpr hf

/-- Multiplication by z^k, expressed as the actual shift of bilateral coefficients. -/
def shift (k : ℤ) (f : WienerLoop A) : WienerLoop A :=
  ⟨fun n ↦ f (n - k), memℓp_shift f k⟩

/-- The standard shift action on Laurent series and its circle evaluation. -/
theorem shift_eval (f : WienerLoop A) (k : ℤ) (z : Circle) :
    (shift k f).eval z = (z : ℂ) ^ k • f.eval z := by
  -- Reindex by n = j + k; the character factor is a central complex scalar.
  change (∑' n : ℤ, (z : ℂ) ^ n • f (n - k)) =
    (z : ℂ) ^ k • ∑' n : ℤ, (z : ℂ) ^ n • f n
  calc
    _ = ∑' j : ℤ, (z : ℂ) ^ (j + k) • f (j + k - k) :=
      ((Equiv.addRight k).tsum_eq (fun n : ℤ ↦ (z : ℂ) ^ n • f (n - k))).symm
    _ = ∑' j : ℤ, (z : ℂ) ^ k • ((z : ℂ) ^ j • f j) := by
      apply tsum_congr
      intro j
      rw [add_sub_cancel_right, zpow_add₀ (Circle.coe_ne_zero z), mul_comm, mul_smul]
    _ = _ := tsum_const_smul'' _

/-- The finite Laurent truncation retaining degrees between -N and N. -/
def truncate (N : ℕ) (f : WienerLoop A) : WienerLoop A :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), lp.single 1 n (f n)

/-- Laurent truncations converge in the coefficient norm, as needed in the KL02 repair. -/
theorem tendsto_truncate (f : WienerLoop A) :
    Filter.Tendsto (fun N : ℕ ↦ truncate N f) Filter.atTop (nhds f) := by
  -- The canonical summable family of single-coordinate vectors converges in ℓ¹.
  have hf := lp.hasSum_single (by simp : (1 : ENNReal) ≠ ⊤) f
  -- The symmetric integer intervals exhaust every finite set of coefficients.
  exact hf.comp Finset.tendsto_Icc_neg

/-- The degree-zero and degree-one series defining an affine loop. -/
def affine (a₀ a₁ : A) : WienerLoop A :=
  lp.single 1 0 a₀ + lp.single 1 1 a₁

/-- Finite Laurent loops that are pointwise invertible have a Wiener inverse. -/
theorem isUnit_of_finiteSupport (f : WienerLoop A)
    (hf : (Function.support (fun n ↦ f n)).Finite)
    (hunit : ∀ z : Circle, IsUnit (f.eval z)) : IsUnit f := by
  /- Stage 1: a finite Laurent series is smooth on the circle. Inversion on
  the open unit group of a Banach algebra makes its pointwise inverse C².
  Stage 2: Banach-valued Fourier coefficients of a C² loop are absolutely
  summable, by integrating twice by parts and bounding the coefficient tail.
  Stage 3: Fourier inversion supplies an inverse Wiener series. Evaluation
  respects multiplication and is injective, so both products equal one.
  This proves only the finite-support case used by KA III.1.17, without
  asserting a general noncommutative Wiener inverse theorem. -/
  classical
  -- The original finite Laurent lift is C², with the original character orientation.
  have hfiniteEval : ContDiff ℝ 2
      (fun t : ℝ ↦ f.eval (AddCircle.toCircle (t : UnitAddCircle))) := by
    -- Replace the actual Laurent evaluation by its finite original coefficient sum.
    have hchar (k : ℤ) (t : UnitAddCircle) :
        ((AddCircle.toCircle t : Circle) : ℂ) ^ k = fourier k t := by
      simp only [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
    have heq (t : ℝ) : f.eval (AddCircle.toCircle (t : UnitAddCircle)) =
        ∑ k ∈ hf.toFinset, fourier k (t : UnitAddCircle) • f k := by
      unfold WienerLoop.eval
      simp_rw [hchar]
      apply tsum_eq_sum
      intro k hk
      have hkzero : f k = 0 := by
        simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hk
      rw [hkzero, smul_zero]
    simp_rw [heq]
    -- Each original integer character is smooth; finite support is the only truncation used.
    apply ContDiff.sum
    intro k hk
    simp only [fourier_coe_apply]
    have hcast : ContDiff ℝ 2 (fun t : ℝ ↦ (t : ℂ)) := Complex.ofRealCLM.contDiff
    fun_prop
  -- Integrate once by parts; periodic endpoints cancel for this exact period.
  have hparts (v : ℝ → A) (hv : ContDiff ℝ 1 v)
      (hperiod : v 1 = v 0) (n : ℤ) (hn : n ≠ 0) :
      (∫ t in (0 : ℝ)..1, fourier (-n) (t : UnitAddCircle) • v t) =
        -(1 / (-2 * Real.pi * Complex.I * n) : ℂ) •
          ∫ t in (0 : ℝ)..1, fourier (-n) (t : UnitAddCircle) • deriv v t := by
    let c : ℂ := 1 / (-2 * Real.pi * Complex.I * n)
    let u : ℝ → ℂ := fun t ↦ c * fourier (-n) (t : UnitAddCircle)
    have hu (t : ℝ) : HasDerivAt u (fourier (-n) (t : UnitAddCircle)) t := by
      simpa only [u, c, Complex.ofReal_one] using
        (has_antideriv_at_fourier_neg (T := (1 : ℝ)) inferInstance hn t)
    have hchar : Continuous (fun t : ℝ ↦ fourier (-n) (t : UnitAddCircle)) :=
      (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' 1)
    have h := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
      (fun t _ ↦ (hu t).continuousAt.continuousWithinAt) hv.continuous.continuousOn
      (fun t _ ↦ hu t) (fun t _ ↦ (hv.differentiable one_ne_zero t).hasDerivAt)
      (hchar.intervalIntegrable 0 1) (hv.continuous_deriv_one.intervalIntegrable 0 1)
    have hend : u 1 • v 1 = u 0 • v 0 := by
      change (c * fourier (-n) ((1 : ℝ) : UnitAddCircle)) • v 1 =
        (c * fourier (-n) ((0 : ℝ) : UnitAddCircle)) • v 0
      rw [AddCircle.coe_period, AddCircle.coe_zero, hperiod]
    rw [hend, sub_self, zero_sub] at h
    have hneg := (congrArg (fun x : A ↦ -x) h).symm
    simpa only [u, mul_smul, intervalIntegral.integral_smul, neg_neg, neg_smul, c]
      using hneg
  -- Two integrations give inverse-square decay; the zero frequency is kept separately.
  have hcoeffSummable (g : C(UnitAddCircle, A))
      (hg : ContDiff ℝ 2 (fun t : ℝ ↦ g (t : UnitAddCircle))) :
      Summable (fun n : ℤ ↦ ‖fourierCoeff g n‖) := by
    classical
    let F : ℝ → A := fun t ↦ g (t : UnitAddCircle)
    have hF : ContDiff ℝ 2 F := hg
    have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
    have hF'' : Continuous (deriv (deriv F)) := hF'.continuous_deriv_one
    have hperiod (t : ℝ) : F (t + 1) = F t := by
      simp [F]
    have hperiod' (t : ℝ) : deriv F (t + 1) = deriv F t := by
      rw [← deriv_comp_add_const]
      exact congrArg (fun f : ℝ → A ↦ deriv f t) (funext hperiod)
    obtain ⟨B, hB, hbound⟩ :=
      ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).image hF'').isBounded.exists_pos_norm_le
    have hdecay (n : ℤ) (hn : n ≠ 0) :
        ‖fourierCoeff g n‖ ≤ (B / (2 * Real.pi) ^ 2) * (1 / (n : ℝ) ^ 2) := by
      let c : ℂ := 1 / (-2 * Real.pi * Complex.I * n)
      have hcoeff : fourierCoeff g n = c • c •
          ∫ t in (0 : ℝ)..1, fourier (-n) (t : UnitAddCircle) • deriv (deriv F) t := by
        rw [fourierCoeff_eq_intervalIntegral g n 0]
        simp only [zero_add, div_one, one_smul]
        change (∫ t in (0 : ℝ)..1, fourier (-n) (t : UnitAddCircle) • F t) = _
        rw [hparts F (hF.of_le (by norm_num)) (by simpa using hperiod 0) n hn]
        rw [hparts (deriv F) hF' (by simpa using hperiod' 0) n hn]
        simp only [c, smul_neg, neg_smul, neg_neg]
      have hI : ‖∫ t in (0 : ℝ)..1,
          fourier (-n) (t : UnitAddCircle) • deriv (deriv F) t‖ ≤ B := by
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := 1) (C := B) (f := fun t ↦
            fourier (-n) (t : UnitAddCircle) • deriv (deriv F) t) (by
            intro t ht
            rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
            apply hbound
            exact ⟨t, Set.Ioc_subset_Icc_self
              (by simpa only [Set.uIoc_of_le zero_le_one] using ht), rfl⟩)
        simpa using hb
      have hc : ‖c‖ = 1 / (2 * Real.pi * |(n : ℝ)|) := by
        simp [c]
      rw [hcoeff, norm_smul, norm_smul, hc]
      calc
        _ ≤ (1 / (2 * Real.pi * |(n : ℝ)|)) *
            ((1 / (2 * Real.pi * |(n : ℝ)|)) * B) := by
          gcongr
        _ = _ := by
          rw [show (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 from (sq_abs _).symm]
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
          ring
    have hp : Summable (fun n : ℤ ↦ (B / (2 * Real.pi) ^ 2) *
        (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _
    have hm := hp.update 0 ‖fourierCoeff g 0‖
    apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg (fourierCoeff g n)) _ hm
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [Function.update_of_ne hn]
      exact hdecay n hn
  -- Continuous complex duals reconstruct the same Banach-valued Fourier series.
  have hfourierReconstruct (g : C(UnitAddCircle, A))
      (hg : Summable (fun n : ℤ ↦ ‖fourierCoeff g n‖)) (x : UnitAddCircle) :
      (∑' n : ℤ, fourier n x • fourierCoeff g n) = g x := by
    have hs : Summable (fun n : ℤ ↦ fourier n x • fourierCoeff g n) := by
      apply hg.of_norm_bounded
      intro n
      simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul, le_refl]
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro L
    let h : C(UnitAddCircle, ℂ) := ⟨fun t ↦ L (g t), L.continuous.comp g.continuous⟩
    have hcoeff (n : ℤ) : fourierCoeff h n = L (fourierCoeff g n) := by
      unfold fourierCoeff
      change (∫ t : UnitAddCircle, fourier (-n) t • L (g t) ∂AddCircle.haarAddCircle) = _
      simp_rw [← map_smul]
      exact L.integral_comp_comm
        ((g.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace g)).fourier_smul (-n))
    have hsum : Summable (fourierCoeff h) := by
      exact (L.summable hg.of_norm).congr (fun n ↦ (hcoeff n).symm)
    rw [L.map_tsum hs]
    simp_rw [map_smul, ← hcoeff]
    have hreconstruct := (has_pointwise_sum_fourier_series_of_summable hsum x).tsum_eq
    simpa only [h, ContinuousMap.coe_mk, smul_eq_mul, mul_comm] using hreconstruct
  have hFourier (g : C(UnitAddCircle, A))
      (hg : ContDiff ℝ 2 (fun t : ℝ ↦ g (t : UnitAddCircle))) :
      Summable (fun n : ℤ ↦ ‖fourierCoeff g n‖) ∧
        ∀ x : UnitAddCircle, (∑' n : ℤ, fourier n x • fourierCoeff g n) = g x := by
    have hs := hcoeffSummable g hg
    exact ⟨hs, hfourierReconstruct g hs⟩
  let p : C(UnitAddCircle, A) :=
    ⟨fun x ↦ f.eval (AddCircle.toCircle x),
      f.continuous_eval.comp AddCircle.continuous_toCircle⟩
  have hu (x : UnitAddCircle) : IsUnit (p x) := hunit (AddCircle.toCircle x)
  -- Take the inverse of the original pointwise unit, without changing multiplication order.
  let g : C(UnitAddCircle, A) :=
    ⟨fun x ↦ Ring.inverse (p x), by
      apply continuous_iff_continuousAt.mpr
      intro x
      have hi : ContinuousAt Ring.inverse (p x) := by
        simpa only [(hu x).unit_spec] using
          (contDiffAt_ringInverse ℂ (hu x).unit (n := 0)).continuousAt
      exact hi.comp p.continuous.continuousAt⟩
  have hgsmooth : ContDiff ℝ 2 (fun t : ℝ ↦ g (t : UnitAddCircle)) := by
    change ContDiff ℝ 2 (fun t : ℝ ↦
      Ring.inverse (f.eval (AddCircle.toCircle (t : UnitAddCircle))))
    apply contDiff_iff_contDiffAt.mpr
    intro t
    have hunitAt := hunit (AddCircle.toCircle (t : UnitAddCircle))
    have hinv : ContDiffAt ℝ 2 Ring.inverse
        (f.eval (AddCircle.toCircle (t : UnitAddCircle))) := by
      simpa only [hunitAt.unit_spec] using
        (contDiffAt_ringInverse ℝ hunitAt.unit (n := 2))
    exact hinv.comp t hfiniteEval.contDiffAt
  obtain ⟨hcoeff, hreconstruct⟩ := hFourier g hgsmooth
  -- The actual Fourier coefficients give an element of the original bilateral ℓ¹ space.
  let b : WienerLoop A := ⟨fourierCoeff g, memℓp_gen (by simpa using hcoeff)⟩
  have hchar (k : ℤ) (t : UnitAddCircle) :
      ((AddCircle.toCircle t : Circle) : ℂ) ^ k = fourier k t := by
    simp only [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  have heval (t : UnitAddCircle) : b.eval (AddCircle.toCircle t) = g t := by
    change (∑' k : ℤ, ((AddCircle.toCircle t : Circle) : ℂ) ^ k • fourierCoeff g k) = g t
    simp_rw [hchar]
    exact hreconstruct t
  have hone (z : Circle) : (1 : WienerLoop A).eval z = 1 := by
    change (∑' n : ℤ,
      (z : ℂ) ^ n • lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) (1 : A) n) = 1
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 1 hn, smul_zero]
  have hsurj : Function.Surjective (AddCircle.toCircle : UnitAddCircle → Circle) := by
    intro z
    obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).surjective z
    exact ⟨t, (AddCircle.homeomorphCircle_apply _ t).symm.trans ht⟩
  -- Evaluation is multiplicative and injective, so both original convolution products are one.
  have hleft : f * b = 1 := by
    apply WienerLoop.eval_injective
    funext z
    obtain ⟨t, rfl⟩ := hsurj z
    rw [WienerLoop.eval_mul, hone, heval]
    exact Ring.mul_inverse_cancel (p t) (hu t)
  have hright : b * f = 1 := by
    apply WienerLoop.eval_injective
    funext z
    obtain ⟨t, rfl⟩ := hsurj z
    rw [WienerLoop.eval_mul, hone, heval]
    exact Ring.inverse_mul_cancel (p t) (hu t)
  exact ⟨⟨f, b, hleft, hright⟩, rfl⟩

/-- KL05: coefficients of the two inverse identities give both affine recurrences. -/
theorem affine_inverse_coefficients (a₀ a₁ : A) (b : WienerLoop A)
    (hleft : affine a₀ a₁ * b = 1) (hright : b * affine a₀ a₁ = 1) (n : ℤ) :
    a₀ * b n + a₁ * b (n - 1) = (if n = 0 then 1 else 0) ∧
    b n * a₀ + b (n - 1) * a₁ = (if n = 0 then 1 else 0) := by
  classical
  have ha (k : ℤ) : affine a₀ a₁ k =
      (if k = 0 then a₀ else 0) + (if k = 1 then a₁ else 0) := by
    change lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) a₀ k +
      lp.single (E := fun _ : ℤ ↦ A) 1 (1 : ℤ) a₁ k = _
    simp only [lp.coeFn_single, Pi.single_apply]
  -- Both sides are the actual nth coefficient of the specified inverse identities.
  have hleftn := congrArg (fun f : WienerLoop A ↦ f n) hleft
  have hrightn := congrArg (fun f : WienerLoop A ↦ f n) hright
  change (∑' k : ℤ, (affine a₀ a₁) k * b (n - k)) =
    lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) 1 n at hleftn
  change (∑' k : ℤ, b k * (affine a₀ a₁) (n - k)) =
    lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) 1 n at hrightn
  have hleftsum : (∑' k : ℤ, (affine a₀ a₁) k * b (n - k)) =
      a₀ * b n + a₁ * b (n - 1) := by
    rw [tsum_eq_sum (s := {0, 1})]
    · simp [ha]
    · intro k hk
      have hk' : k ≠ 0 ∧ k ≠ 1 := by simpa using hk
      obtain ⟨hk0, hk1⟩ := hk'
      simp [ha, hk0, hk1]
  have hrightsum : (∑' k : ℤ, b k * (affine a₀ a₁) (n - k)) =
      b n * a₀ + b (n - 1) * a₁ := by
    rw [tsum_eq_sum (s := {n, n - 1})]
    · simp [ha, show n ≠ n - 1 by omega]
    · intro k hk
      have hk' : k ≠ n ∧ k ≠ n - 1 := by simpa using hk
      have hk0 : n - k ≠ 0 := by omega
      have hk1 : n - k ≠ 1 := by omega
      simp [ha, hk0, hk1]
  constructor
  · simpa only [hleftsum, lp.coeFn_single, Pi.single_apply] using hleftn
  · simpa only [hrightsum, lp.coeFn_single, Pi.single_apply] using hrightn

/-- KL05 (v), (v'): inverse coefficients commute with both normalized affine coefficients. -/
theorem affine_inverse_commute (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) (n : ℤ) :
    Commute a₀ (b n) ∧ Commute a₁ (b n) := by
  -- Subtract the two inverse recurrences: the commutator is constant in the degree.
  let c : ℤ → A := fun m ↦ a₀ * b m - b m * a₀
  have ha₁ : a₁ = 1 - a₀ := eq_sub_of_add_eq' hbase
  have hstep (m : ℤ) : c m = c (m - 1) := by
    obtain ⟨hL, hR⟩ := affine_inverse_coefficients a₀ a₁ b hleft hright m
    rw [ha₁, sub_mul, one_mul] at hL
    rw [ha₁, mul_sub, mul_one] at hR
    dsimp [c]
    linear_combination (norm := abel) hL - hR
  have hconstant (m : ℤ) : c m = c 0 := by
    induction m using Int.induction_on with
    | zero => rfl
    | succ k ih =>
      rw [hstep]
      simpa using ih
    | pred k ih =>
      rw [← hstep]
      simpa using ih
  -- Absolute summability sends the coefficients, hence the commutators, to zero.
  have hb : Filter.Tendsto (fun m : ℤ ↦ b m) Filter.cofinite (nhds 0) :=
    b.2.summable_of_one.tendsto_cofinite_zero
  have hc : Filter.Tendsto c Filter.cofinite (nhds 0) := by
    simpa [c] using (hb.const_mul a₀).sub (hb.mul_const a₀)
  have hc' : Filter.Tendsto (fun m : ℤ ↦ c m) Filter.cofinite (nhds 0) := hc
  simp_rw [hconstant] at hc'
  have hc₀ : c 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hc'
  have hcomm : Commute a₀ (b n) := sub_eq_zero.mp ((hconstant n).trans hc₀)
  refine ⟨hcomm, ?_⟩
  rw [ha₁]
  exact (Commute.one_left (b n)).sub_left hcomm

/-- KL05 (iv): all coefficients of the inverse normalized affine loop commute. -/
theorem affine_inverse_coefficients_commute (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) (i j : ℤ) : Commute (b i) (b j) := by
  -- Constant series act by left and right multiplication on the actual coefficients.
  let c : A → WienerLoop A := fun a ↦ lp.single 1 (0 : ℤ) a
  have hconst (a : A) (f : WienerLoop A) (m : ℤ) :
      (c a * f) m = a * f m ∧ (f * c a) m = f m * a := by
    constructor
    · change (∑' k : ℤ, lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) a k *
        f (m - k)) = a * f m
      rw [tsum_eq_single 0]
      · simp
      · intro k hk
        rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 a hk, zero_mul]
    · change (∑' k : ℤ, f k *
        lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) a (m - k)) = f m * a
      rw [tsum_eq_single m]
      · simp
      · intro k hk
        rw [lp.single_apply_ne (E := fun _ : ℤ ↦ A) 1 0 a (by omega), mul_zero]
  -- The preceding recurrence proof makes every coefficient commute with the affine series.
  obtain ⟨ha₀, ha₁⟩ := affine_inverse_commute a₀ a₁ hbase b hleft hright i
  have hca : Commute (c (b i)) (affine a₀ a₁) := by
    apply lp.ext
    funext m
    rw [(hconst (b i) (affine a₀ a₁) m).1, (hconst (b i) (affine a₀ a₁) m).2]
    have ha (k : ℤ) : affine a₀ a₁ k =
        (if k = 0 then a₀ else 0) + (if k = 1 then a₁ else 0) := by
      change lp.single (E := fun _ : ℤ ↦ A) 1 (0 : ℤ) a₀ k +
        lp.single (E := fun _ : ℤ ↦ A) 1 (1 : ℤ) a₁ k = _
      simp only [lp.coeFn_single, Pi.single_apply]
    rw [ha]
    by_cases hm₀ : m = 0
    · simpa [hm₀] using ha₀.symm.eq
    · by_cases hm₁ : m = 1
      · simpa [hm₁] using ha₁.symm.eq
      · simp [hm₀, hm₁]
  -- Commutation passes to the specified two-sided inverse, without a Fourier exchange.
  let u : (WienerLoop A)ˣ := ⟨affine a₀ a₁, b, hleft, hright⟩
  have hcb : Commute (c (b i)) b := hca.units_inv_right (u := u)
  have hcoeff := congrArg (fun f : WienerLoop A ↦ f j) hcb.eq
  change b i * b j = b j * b i
  simpa only [(hconst (b i) b j).1, (hconst (b i) b j).2] using hcoeff

/-- KL05 (i), (ii): coefficients from opposite Fourier halves annihilate across a₀ or a₁. -/
theorem affine_inverse_cross_coefficients (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) (i j : ℤ)
    (hcross : (i < 0 ∧ 0 ≤ j) ∨ (0 ≤ i ∧ j < 0)) :
    b i * a₀ * b j = 0 ∧ b i * a₁ * b j = 0 := by
  -- Away from degree zero, the two recurrences move the factors into opposite tails.
  have hmove (i j : ℤ) (hi : i < 0) (hj : 0 ≤ j) :
      b i * a₀ * b j = b (i - 1) * a₀ * b (j + 1) := by
    have hL := (affine_inverse_coefficients a₀ a₁ b hleft hright (j + 1)).1
    have hR := (affine_inverse_coefficients a₀ a₁ b hleft hright i).2
    simp only [add_sub_cancel_right, ite_eq_right (show j + 1 ≠ 0 by omega)] at hL
    simp only [ite_eq_right (ne_of_lt hi)] at hR
    linear_combination (norm := noncomm_ring) hR * b j - b (i - 1) * hL
  have hmain (i j : ℤ) (hi : i < 0) (hj : 0 ≤ j) : b i * a₀ * b j = 0 := by
    have hinvariant (r : ℕ) :
        b i * a₀ * b j = b (i - r) * a₀ * b (j + r) := by
      induction r with
      | zero => simp
      | succ r ih =>
        rw [ih]
        simpa [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, add_assoc] using
          hmove (i - r) (j + r) (by omega) (by omega)
    -- Both coefficient tails tend to zero because the bilateral series is absolutely summable.
    have hb : Filter.Tendsto (fun m : ℤ ↦ b m) Filter.cofinite (nhds 0) :=
      b.2.summable_of_one.tendsto_cofinite_zero
    have hneg : Filter.Tendsto (fun r : ℕ ↦ b (i - r)) Filter.atTop (nhds 0) := by
      have hinj : Function.Injective (fun r : ℕ ↦ i - (r : ℤ)) := by
        intro r s hrs
        dsimp at hrs
        omega
      simpa only [Nat.cofinite_eq_atTop, Function.comp_def] using hb.comp hinj.tendsto_cofinite
    have hpos : Filter.Tendsto (fun r : ℕ ↦ b (j + r)) Filter.atTop (nhds 0) := by
      have hinj : Function.Injective (fun r : ℕ ↦ j + (r : ℤ)) := by
        intro r s hrs
        dsimp at hrs
        omega
      simpa only [Nat.cofinite_eq_atTop, Function.comp_def] using hb.comp hinj.tendsto_cofinite
    have hlim : Filter.Tendsto (fun r : ℕ ↦ b (i - r) * a₀ * b (j + r))
        Filter.atTop (nhds 0) := by
      simpa using (hneg.mul_const a₀).mul hpos
    simp_rw [← hinvariant] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  have hsecond (i j : ℤ) (hi : i < 0) (hj : 0 ≤ j) : b i * a₁ * b j = 0 := by
    have hL := (affine_inverse_coefficients a₀ a₁ b hleft hright (j + 1)).1
    simp only [add_sub_cancel_right, ite_eq_right (show j + 1 ≠ 0 by omega)] at hL
    have hzero := hmain i (j + 1) hi (by omega)
    linear_combination (norm := noncomm_ring) b i * hL - hzero
  -- The reversed order follows from the already proved commutation of these specified factors.
  rcases hcross with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact ⟨hmain i j hi hj, hsecond i j hi hj⟩
  · have hswap (a : A) (hai : Commute a (b i)) (haj : Commute a (b j)) :
        b i * a * b j = b j * a * b i := by
      calc
        b i * a * b j = b i * b j * a := by rw [mul_assoc, haj.eq, ← mul_assoc]
        _ = b j * b i * a := congrArg (fun x : A ↦ x * a)
          (affine_inverse_coefficients_commute a₀ a₁ hbase b hleft hright i j).eq
        _ = b j * a * b i := by rw [mul_assoc, ← hai.eq, ← mul_assoc]
    have hi_comm := affine_inverse_commute a₀ a₁ hbase b hleft hright i
    have hj_comm := affine_inverse_commute a₀ a₁ hbase b hleft hright j
    constructor
    · rw [hswap a₀ hi_comm.1 hj_comm.1]
      exact hmain j i hj hi
    · rw [hswap a₁ hi_comm.2 hj_comm.2]
      exact hsecond j i hj hi

/-- KL05 (iii): the negative and nonnegative inverse coefficients annihilate each other. -/
theorem affine_inverse_cross_mul (a₀ a₁ : A) (hbase : a₀ + a₁ = 1)
    (b : WienerLoop A) (hleft : affine a₀ a₁ * b = 1)
    (hright : b * affine a₀ a₁ = 1) (i j : ℤ)
    (hcross : (i < 0 ∧ 0 ≤ j) ∨ (0 ≤ i ∧ j < 0)) : b i * b j = 0 := by
  -- Insert the original affine normalization between the two coefficients.
  obtain ⟨h₀, h₁⟩ := affine_inverse_cross_coefficients a₀ a₁ hbase b hleft hright i j hcross
  calc
    b i * b j = b i * (a₀ + a₁) * b j := by rw [hbase, mul_one]
    _ = b i * a₀ * b j + b i * a₁ * b j := by rw [mul_add, add_mul]
    _ = 0 := by rw [h₀, h₁, add_zero]

end WienerLoop

end AtiyahSinger

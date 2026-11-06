/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local estimates for iterated connection components

Public module ID: M0426.

A connection recursion has the ordinary derivative as its leading term and a
smooth coefficient acting on the preceding tensor as its zeroth-order term.
On a fixed compact subset of the coordinate domain, repeated Leibniz estimates
control the connection components by ordinary jets and recover ordinary jets
from the same components. Constants are selected before the section.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped ContDiff Topology

set_option maxSynthPendingDepth 30

/-- Every ordinary derivative of a connection component is bounded by the corresponding
finite ordinary jet. The constants depend on the fixed coefficients, not on the section. -/
theorem exists_connectionJet_derivative_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : ℕ → Type*} [∀ k, NormedAddCommGroup (V k)] [∀ k, NormedSpace ℝ (V k)]
    (U K : Set X) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (e : (k : ℕ) → (X →L[ℝ] V k) ≃L[ℝ] V (k + 1))
    (Γ : (k : ℕ) → X → V k →L[ℝ] (X →L[ℝ] V k))
    (hΓ : ∀ k, ContDiffOn ℝ ∞ (Γ k) U) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (k : ℕ) → X → V k,
      (∀ k, ContDiffOn ℝ ∞ (f k) U) →
      (∀ k x, x ∈ U → f (k + 1) x = e k (fderiv ℝ (f k) x + Γ k x (f k x))) →
      ∀ x, x ∈ K → ‖iteratedFDeriv ℝ j (f k) x‖ ≤
        C * ∑ l ∈ Finset.range (k + j + 1), ‖iteratedFDeriv ℝ l (f 0) x‖ := by
  -- All coefficient derivatives are bounded on the fixed compact set before f is chosen.
  have hcoeff (k i : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i (Γ k) x‖ ≤ A := by
    have hc : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ i (Γ k) x‖) K := by
      have h := (hΓ k).continuousOn_iteratedFDerivWithin (by simp : (i : ℕ∞ω) ≤ ∞)
        hU.uniqueDiffOn
      apply (h.norm.mono hKU).congr
      intro x hx
      dsimp only
      rw [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)]
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max A 0, le_max_right _ _, ?_⟩
    intro x hx
    have hb : ‖iteratedFDeriv ℝ i (Γ k) x‖ ≤ A := by
      simpa only [norm_norm] using hA x hx
    exact hb.trans (le_max_left _ _)
  have hmono (f : X → V 0) (x : X) (a b : ℕ) (hab : a ≤ b) :
      (∑ l ∈ Finset.range (a + 1), ‖iteratedFDeriv ℝ l f x‖) ≤
        ∑ l ∈ Finset.range (b + 1), ‖iteratedFDeriv ℝ l f x‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hab 1))
      (fun _ _ _ ↦ norm_nonneg _)
  -- Induction on the connection order retains all ordinary derivatives needed at each stage.
  induction k generalizing j with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro f hf hrec x hx
    rw [one_mul]
    simpa only [Nat.zero_add] using Finset.single_le_sum
      (fun l (_ : l ∈ Finset.range (j + 1)) ↦ norm_nonneg (iteratedFDeriv ℝ l (f 0) x))
      (Finset.mem_range.mpr (Nat.lt_succ_self j))
  | succ k ih =>
    choose C hC hCb using ih
    choose A hA hAb using hcoeff k
    let D : ℝ := ‖(e k).toContinuousLinearMap‖ *
      (C (j + 1) + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * C (j - i))
    have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) (add_nonneg (hC _)
      (Finset.sum_nonneg (fun i _ ↦
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hC (j - i)))))
    refine ⟨D, hD, ?_⟩
    intro f hf hrec x hx
    have hxU := hKU hx
    let S : ℝ := ∑ l ∈ Finset.range (k + j + 1 + 1), ‖iteratedFDeriv ℝ l (f 0) x‖
    have hder (a : ℕ) (ha : a ≤ j + 1) :
        ‖iteratedFDeriv ℝ a (f k) x‖ ≤ C a * S := by
      apply (hCb a f hf hrec x hx).trans
      exact mul_le_mul_of_nonneg_left
        (hmono (f 0) x (k + a) (k + j + 1) (by omega)) (hC a)
    have hdf : ContDiffOn ℝ ∞ (fderiv ℝ (f k)) U :=
      (hf k).fderiv_of_isOpen hU (by simp)
    have hprod : ContDiffOn ℝ ∞ (fun y ↦ Γ k y (f k y)) U := (hΓ k).clm_apply (hf k)
    -- Differentiate the leading ordinary derivative and use Leibniz for the coefficient term.
    have heq : f (k + 1) =ᶠ[𝓝 x]
        (e k).toContinuousLinearMap ∘ (fun y ↦ fderiv ℝ (f k) y + Γ k y (f k y)) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact hrec k y hy
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
    have hsumAt : ContDiffAt ℝ ∞ (fun y ↦ fderiv ℝ (f k) y + Γ k y (f k y)) x :=
      (hdf.add hprod).contDiffAt (hU.mem_nhds hxU)
    apply ((e k).toContinuousLinearMap.norm_iteratedFDeriv_comp_left hsumAt (by simp)).trans
    rw [fun_iteratedFDeriv_add_apply
      ((hdf.contDiffAt (hU.mem_nhds hxU)).of_le (by simp))
      ((hprod.contDiffAt (hU.mem_nhds hxU)).of_le (by simp))]
    have hle := norm_iteratedFDerivWithin_clm_apply (hΓ k) (hf k)
      hU.uniqueDiffOn hxU (n := j) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hle
    have hprodBound : ‖iteratedFDeriv ℝ j (fun y ↦ Γ k y (f k y)) x‖ ≤
        (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * C (j - i)) * S := by
      apply hle.trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ (j.choose i : ℝ) * A i * (C (j - i) * S) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hAb i x hx) (Nat.cast_nonneg _))
            (hder (j - i) (by omega)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (hA i))
        _ = _ := by ring
    have hfirst : ‖iteratedFDeriv ℝ j (fderiv ℝ (f k)) x‖ ≤ C (j + 1) * S := by
      rw [norm_iteratedFDeriv_fderiv]
      exact hder (j + 1) le_rfl
    apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add hfirst hprodBound) (norm_nonneg _)).trans_eq
    dsimp only [D, S]
    rw [show k + 1 + j + 1 = k + j + 1 + 1 by omega]
    ring

/-- Solving the same connection recursion recovers every ordinary derivative from
finitely many actual connection components, with constants independent of the section. -/
theorem exists_connectionJet_recovery_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : ℕ → Type*} [∀ k, NormedAddCommGroup (V k)] [∀ k, NormedSpace ℝ (V k)]
    (U K : Set X) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (e : (k : ℕ) → (X →L[ℝ] V k) ≃L[ℝ] V (k + 1))
    (Γ : (k : ℕ) → X → V k →L[ℝ] (X →L[ℝ] V k))
    (hΓ : ∀ k, ContDiffOn ℝ ∞ (Γ k) U) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (k : ℕ) → X → V k,
      (∀ k, ContDiffOn ℝ ∞ (f k) U) →
      (∀ k x, x ∈ U → f (k + 1) x = e k (fderiv ℝ (f k) x + Γ k x (f k x))) →
      ∀ x, x ∈ K → ‖iteratedFDeriv ℝ j (f k) x‖ ≤
        C * ∑ l ∈ Finset.range (k + j + 1), ‖f l x‖ := by
  -- All coefficient derivatives are bounded on the fixed compact set before f is chosen.
  have hcoeff (k i : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i (Γ k) x‖ ≤ A := by
    have hc : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ i (Γ k) x‖) K := by
      have h := (hΓ k).continuousOn_iteratedFDerivWithin (by simp : (i : ℕ∞ω) ≤ ∞)
        hU.uniqueDiffOn
      apply (h.norm.mono hKU).congr
      intro x hx
      dsimp only
      rw [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)]
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max A 0, le_max_right _ _, ?_⟩
    intro x hx
    have hb : ‖iteratedFDeriv ℝ i (Γ k) x‖ ≤ A := by
      simpa only [norm_norm] using hA x hx
    exact hb.trans (le_max_left _ _)
  have hmono (f : (k : ℕ) → X → V k) (x : X) (a b : ℕ) (hab : a ≤ b) :
      (∑ l ∈ Finset.range (a + 1), ‖f l x‖) ≤ ∑ l ∈ Finset.range (b + 1), ‖f l x‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hab 1))
      (fun _ _ _ ↦ norm_nonneg _)
  -- Inverting the leading identification reduces ordinary derivative order at every step.
  induction j using Nat.strong_induction_on generalizing k with
  | h j ih =>
    cases j with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro f hf hrec x hx
      rw [norm_iteratedFDeriv_zero, one_mul]
      simpa only [Nat.add_zero] using Finset.single_le_sum
        (fun l (_ : l ∈ Finset.range (k + 1)) ↦ norm_nonneg (f l x))
        (Finset.mem_range.mpr (Nat.lt_succ_self k))
    | succ j =>
      -- The leading derivative is recovered by inverting the fixed coordinate identification.
      obtain ⟨A₀, hA₀, hA₀b⟩ := ih j (Nat.lt_succ_self j) (k + 1)
      have hi (i : ℕ) := ih (j - i) (by omega : j - i < j + 1) k
      choose C hC hCb using hi
      choose A hA hAb using hcoeff k
      let D : ℝ := ‖(e k).symm.toContinuousLinearMap‖ * A₀ +
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * C i
      have hD : 0 ≤ D := add_nonneg (mul_nonneg (norm_nonneg _) hA₀)
        (Finset.sum_nonneg (fun i _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hC i)))
      refine ⟨D, hD, ?_⟩
      intro f hf hrec x hx
      have hxU := hKU hx
      let S : ℝ := ∑ l ∈ Finset.range (k + j + 1 + 1), ‖f l x‖
      have hder (i : ℕ) : ‖iteratedFDeriv ℝ (j - i) (f k) x‖ ≤ C i * S := by
        apply (hCb i f hf hrec x hx).trans
        exact mul_le_mul_of_nonneg_left (hmono f x (k + (j - i)) (k + j + 1) (by omega))
          (hC i)
      have hnext : ‖iteratedFDeriv ℝ j (f (k + 1)) x‖ ≤ A₀ * S := by
        simpa only [S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hA₀b f hf hrec x hx
      have hprod : ContDiffOn ℝ ∞ (fun y ↦ Γ k y (f k y)) U := (hΓ k).clm_apply (hf k)
      have hinv : ContDiffOn ℝ ∞ (fun y ↦ (e k).symm (f (k + 1) y)) U :=
        (e k).symm.contDiff.comp_contDiffOn (hf (k + 1))
      have heq : fderiv ℝ (f k) =ᶠ[𝓝 x]
          (fun y ↦ (e k).symm (f (k + 1) y) - Γ k y (f k y)) := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        have h := congrArg (e k).symm (hrec k y hy)
        rw [(e k).symm_apply_apply] at h
        exact eq_sub_of_add_eq h.symm
      rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv ℝ j).eq_of_nhds]
      rw [fun_iteratedFDeriv_sub_apply
        ((hinv.contDiffAt (hU.mem_nhds hxU)).of_le (by simp))
        ((hprod.contDiffAt (hU.mem_nhds hxU)).of_le (by simp))]
      have hfirst : ‖iteratedFDeriv ℝ j
          ((e k).symm.toContinuousLinearMap ∘ f (k + 1)) x‖ ≤
            ‖(e k).symm.toContinuousLinearMap‖ * (A₀ * S) :=
        ((e k).symm.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
          ((hf (k + 1)).contDiffAt (hU.mem_nhds hxU)) (by simp)).trans
            (mul_le_mul_of_nonneg_left hnext (norm_nonneg _))
      have hle := norm_iteratedFDerivWithin_clm_apply (hΓ k) (hf k)
        hU.uniqueDiffOn hxU (n := j) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hle
      have hprodBound : ‖iteratedFDeriv ℝ j (fun y ↦ Γ k y (f k y)) x‖ ≤
          (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * C i) * S := by
        apply hle.trans
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ (j.choose i : ℝ) * A i * (C i * S) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hAb i x hx) (Nat.cast_nonneg _))
              (hder i) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
          _ = _ := by ring
      apply (norm_sub_le _ _).trans
      apply (add_le_add hfirst hprodBound).trans_eq
      dsimp only [D, S]
      rw [show k + (j + 1) + 1 = k + j + 1 + 1 by omega]
      ring

/-- Multiplication by one fixed smooth cutoff bounds each derivative by a finite jet,
uniformly over vector-valued functions on the given compact set. -/
theorem exists_iteratedFDeriv_smul_bound
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U K : Set X) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (χ : X → ℝ) (hχ : ContDiffOn ℝ ∞ χ U) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : X → V, ContDiffOn ℝ ∞ f U → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (fun y ↦ χ y • f y) x‖ ≤
        C * ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l f x‖ := by
  -- Compactness bounds every needed derivative of the fixed scalar coefficient.
  have hcoeff (j : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ A := by
    have hc : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j χ x‖) K := by
      have h := hχ.continuousOn_iteratedFDerivWithin (by simp : (j : ℕ∞ω) ≤ ∞)
        hU.uniqueDiffOn
      apply (h.norm.mono hKU).congr
      intro x hx
      dsimp only
      rw [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)]
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max A 0, le_max_right _ _, fun x hx ↦ ?_⟩
    have hb : ‖iteratedFDeriv ℝ j χ x‖ ≤ A := by simpa only [norm_norm] using hA x hx
    exact hb.trans (le_max_left _ _)
  choose A hA hAb using hcoeff
  let C : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A j
  refine ⟨C, Finset.sum_nonneg (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hA j)), ?_⟩
  intro f hf x hx
  -- The ordinary Leibniz estimate retains all orders below k and no derivative of the section
  -- is used in choosing C.
  have hb := norm_iteratedFDerivWithin_smul_le hχ hf hU.uniqueDiffOn (hKU hx)
    (n := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)] at hb
  apply hb.trans
  dsimp only [C]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (hAb j x hx) (Nat.cast_nonneg _)
  · exact Finset.single_le_sum (fun l _ ↦ norm_nonneg (iteratedFDeriv ℝ l f x))
      (Finset.mem_range.mpr (by omega))
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (hA j)

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialSymbol
public import AtiyahSinger.Analysis.LocalComposition
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The finite composition expansion for a second-order differential symbol

Public module ID: M0432.

The first three standard composition terms are identified with the original ordered
coefficients. This retains the two mixed first derivatives and explains the factor
one half in the second standard composition term without assuming symmetric coefficients.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open scoped ContDiff

variable {n r s t : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

set_option maxHeartbeats 2000000 in

/-- The standard finite symbol composition formula agrees with the original ordered
coefficient correction, even if the chosen degree-two coefficients are not symmetric. -/
theorem compositionExpansion_sum_order_two (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n s t 2 U) (a : SymbolFunction n r s)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
    (ξ : EuclideanSpace ℝ (Fin n))
    (ha : ContDiffOn ℝ ∞ (fun y ↦ a y ξ) U) (u : EuclideanSpace ℂ (Fin r)) :
    (∑ j : Fin 3, compositionExpansionTerm P.totalSymbol a j.val) x ξ u =
      P.totalSymbol x ξ (a x ξ u) +
        (∑ α : Fin 1 → Fin n,
          P.coefficient 1 α x ((-Complex.I) •
            fderiv ℝ (fun y ↦ a y ξ u) x (EuclideanSpace.single (α 0) 1))) +
        ∑ α : Fin 2 → Fin n,
          P.coefficient 2 α x
            ((-Complex.I) •
                ((ξ (α 0) : ℂ) •
                    fderiv ℝ (fun y ↦ a y ξ u) x (EuclideanSpace.single (α 1) 1) +
                  (ξ (α 1) : ℂ) •
                    fderiv ℝ (fun y ↦ a y ξ u) x (EuclideanSpace.single (α 0) 1)) -
              iteratedFDeriv ℝ 2 (fun y ↦ a y ξ u) x
                (fun j ↦ EuclideanSpace.single (α j) 1)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin s)
  let W := EuclideanSpace ℂ (Fin t)
  let H := V →L[ℂ] W
  let e (i : Fin n) : X := EuclideanSpace.single i 1
  let pr (i : Fin n) : X →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n ↦ ℝ) i
  have hpr (i : Fin n) (η : X) : pr i η = η i := rfl
  let A₀ (α : Fin 0 → Fin n) : H := P.coefficient 0 α x
  let A₁ (α : Fin 1 → Fin n) : H := P.coefficient 1 α x
  let A₂ (α : Fin 2 → Fin n) : H := P.coefficient 2 α x
  let v : X → V := fun y ↦ a y ξ u
  let ev : (EuclideanSpace ℂ (Fin r) →L[ℂ] V) →L[ℝ] V :=
    (ContinuousLinearMap.apply ℂ V u).restrictScalars ℝ
  have hv : ContDiffOn ℝ ∞ v U := ev.contDiff.comp_contDiffOn ha
  -- Evaluate the two polynomial frequency derivatives with the same coefficients.
  have hp : P.totalSymbol x = fun η ↦
      (∑ α : Fin 0 → Fin n, A₀ α) +
        (∑ α : Fin 1 → Fin n, η (α 0) • A₁ α) +
        ∑ α : Fin 2 → Fin n, (η (α 0) * η (α 1)) • A₂ α := by
    funext η
    unfold totalSymbol
    rw [Fin.sum_univ_three]
    change (∑ α : Fin 0 → Fin n, (∏ j : Fin 0, η (α j)) • A₀ α) +
      (∑ α : Fin 1 → Fin n, (∏ j : Fin 1, η (α j)) • A₁ α) +
      (∑ α : Fin 2 → Fin n, (∏ j : Fin 2, η (α j)) • A₂ α) = _
    simp only [Fin.prod_univ_zero, Fin.prod_univ_one, Fin.prod_univ_two, one_smul]
  let dp (η : X) : X →L[ℝ] H :=
    (∑ α : Fin 1 → Fin n, (pr (α 0)).smulRight (A₁ α)) +
      ∑ α : Fin 2 → Fin n,
        (η (α 0) • pr (α 1) + η (α 1) • pr (α 0)).smulRight (A₂ α)
  have hdp (η : X) : fderiv ℝ (P.totalSymbol x) η = dp η := by
    rw [hp]
    have h₁ := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun α (_ : α ∈ Finset.univ) ↦
        ((pr (α 0)).hasFDerivAt (x := η)).smul_const (A₁ α))
    have h₂ := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun α (_ : α ∈ Finset.univ) ↦
        (((pr (α 0)).hasFDerivAt (x := η)).fun_mul
          ((pr (α 1)).hasFDerivAt (x := η))).smul_const (A₂ α))
    have hsum := ((hasFDerivAt_const (∑ α : Fin 0 → Fin n, A₀ α) η).fun_add h₁).fun_add h₂
    have h := hsum.fderiv
    simpa only [dp, hpr, zero_add] using h
  have hfreq₁ (η d : X) :
      fderiv ℝ (P.totalSymbol x) η d =
        (∑ α : Fin 1 → Fin n, d (α 0) • A₁ α) +
          ∑ α : Fin 2 → Fin n,
            (η (α 0) * d (α 1) + η (α 1) * d (α 0)) • A₂ α := by
    rw [hdp η]
    simp [dp, hpr, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have hfreq₂ (d : Fin 2 → X) :
      iteratedFDeriv ℝ 2 (P.totalSymbol x) ξ d =
        ∑ α : Fin 2 → Fin n,
          (d 0 (α 0) * d 1 (α 1) + d 0 (α 1) * d 1 (α 0)) • A₂ α := by
    let F : X → H := fun η ↦ fderiv ℝ (P.totalSymbol x) η (d 1)
    have hF : F = fun η ↦
        (∑ α : Fin 1 → Fin n, d 1 (α 0) • A₁ α) +
          ∑ α : Fin 2 → Fin n,
            (η (α 0) * d 1 (α 1) + η (α 1) * d 1 (α 0)) • A₂ α := by
      funext η
      exact hfreq₁ η (d 1)
    have hdF : fderiv ℝ F ξ =
        (∑ α : Fin 2 → Fin n,
          (d 1 (α 1) • pr (α 0) + d 1 (α 0) • pr (α 1)).smulRight (A₂ α)) := by
      rw [hF]
      have hsum := HasFDerivAt.fun_sum (u := Finset.univ)
        (fun α (_ : α ∈ Finset.univ) ↦
          ((((pr (α 0)).hasFDerivAt (x := ξ)).mul_const (d 1 (α 1))).fun_add
            (((pr (α 1)).hasFDerivAt (x := ξ)).mul_const (d 1 (α 0)))).smul_const
              (A₂ α))
      have h := ((hasFDerivAt_const
        (∑ α : Fin 1 → Fin n, d 1 (α 0) • A₁ α) ξ).fun_add hsum).fderiv
      simpa only [hpr, zero_add] using h
    have hddp : DifferentiableAt ℝ (fderiv ℝ (P.totalSymbol x)) ξ := by
      have heq : fderiv ℝ (P.totalSymbol x) = dp := funext hdp
      rw [heq]
      have hcoord (i : Fin n) : ContDiff ℝ ∞ (fun η : X ↦ η i) := (pr i).contDiff
      have hs : ContDiff ℝ ∞ dp := by
        change ContDiff ℝ ∞ (fun η : X ↦
          (∑ α : Fin 1 → Fin n, (pr (α 0)).smulRight (A₁ α)) +
            ∑ α : Fin 2 → Fin n,
              (η (α 0) • pr (α 1) + η (α 1) • pr (α 0)).smulRight (A₂ α))
        apply ContDiff.add contDiff_const
        apply ContDiff.sum
        intro α _
        exact (((hcoord (α 0)).smul contDiff_const).add
          ((hcoord (α 1)).smul contDiff_const)).smulRight contDiff_const
      exact hs.differentiable (by simp) ξ
    let eval : (X →L[ℝ] H) →L[ℝ] H := ContinuousLinearMap.apply ℝ H (d 1)
    have heval := congrArg (fun D : X →L[ℝ] H ↦ D (d 0))
      (eval.hasFDerivAt.comp ξ hddp.hasFDerivAt).fderiv
    change fderiv ℝ F ξ (d 0) =
      fderiv ℝ (fderiv ℝ (P.totalSymbol x)) ξ (d 0) (d 1) at heval
    rw [iteratedFDeriv_two_apply, ← heval, hdF]
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, add_apply,
      smul_apply, smul_eq_mul, hpr]
    congr 1
    funext α
    congr 1
    ring
  -- Coordinate contractions are finite Kronecker sums, including dimension zero.
  have hsingle (i j : Fin n) : e i j = if i = j then 1 else 0 := by
    simp [e, PiLp.single_apply, eq_comm]
  have hsum₁ (F : (Fin 1 → Fin n) → W) (i : Fin n) :
      (∑ β : Fin 1 → Fin n, e (β 0) i • F β) = F (fun _ ↦ i) := by
    rw [Finset.sum_eq_single (fun _ ↦ i)]
    · simp [hsingle]
    · intro β _ hβ
      have hne : β 0 ≠ i := by
        intro h
        apply hβ
        funext j
        fin_cases j
        exact h
      simp [hsingle, hne]
    · simp
  have hsum₂ (F : (Fin 2 → Fin n) → W) (i j : Fin n) :
      (∑ β : Fin 2 → Fin n, (e (β 0) i * e (β 1) j) • F β) =
        F ![i, j] := by
    rw [Finset.sum_eq_single ![i, j]]
    · simp [hsingle]
    · intro β _ hβ
      by_cases h₀ : β 0 = i
      · have h₁ : β 1 ≠ j := by
          intro h
          apply hβ
          funext k
          fin_cases k
          · exact h₀
          · exact h
        simp [hsingle, h₁]
      · simp [hsingle, h₀]
    · simp
  -- Constant fiber evaluation commutes with both actual spatial derivatives.
  have hjet (j : ℕ) (β : Fin j → Fin n) :
      iteratedFDeriv ℝ j (fun y ↦ a y ξ) x (fun k ↦ e (β k)) u =
        iteratedFDeriv ℝ j v x (fun k ↦ e (β k)) := by
    have h := ev.iteratedFDeriv_comp_left (ha.contDiffAt (hU.mem_nhds hx))
      (i := j) (by simp)
    exact (congrArg (fun D : X [×j]→L[ℝ] V ↦ D (fun k ↦ e (β k))) h).symm
  have hsymm (i j : Fin n) :
      iteratedFDeriv ℝ 2 v x (fun k ↦ e (![j, i] k)) =
        iteratedFDeriv ℝ 2 v x (fun k ↦ e (![i, j] k)) := by
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    change fderiv ℝ (fderiv ℝ v) x (e j) (e i) =
      fderiv ℝ (fderiv ℝ v) x (e i) (e j)
    exact (hv.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by simp) (e j) (e i)
  -- Degree one contracts each of the two ordered frequency slots separately.
  have hc₁ :
      (∑ β : Fin 1 → Fin n,
        (fderiv ℝ (P.totalSymbol x) ξ (e (β 0)))
          (fderiv ℝ v x (e (β 0)))) =
        (∑ α : Fin 1 → Fin n, A₁ α (fderiv ℝ v x (e (α 0)))) +
          ∑ α : Fin 2 → Fin n,
            A₂ α ((ξ (α 0)) • fderiv ℝ v x (e (α 1)) +
              (ξ (α 1)) • fderiv ℝ v x (e (α 0))) := by
    simp only [hfreq₁, add_apply, sum_apply, smul_apply,
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α _
      exact hsum₁ (fun β ↦ A₁ α (fderiv ℝ v x (e (β 0)))) (α 0)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α _
      simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum]
      rw [hsum₁, hsum₁]
      simp only [← Complex.coe_smul, map_add, map_smul]
  -- Degree two has two identical contractions after symmetry of the spatial Hessian.
  have hc₂ :
      (∑ β : Fin 2 → Fin n,
        (iteratedFDeriv ℝ 2 (P.totalSymbol x) ξ (fun k ↦ e (β k)))
          (iteratedFDeriv ℝ 2 v x (fun k ↦ e (β k)))) =
        (2 : ℂ) • ∑ α : Fin 2 → Fin n,
          A₂ α (iteratedFDeriv ℝ 2 v x (fun k ↦ e (α k))) := by
    simp only [hfreq₂, sum_apply, smul_apply]
    rw [Finset.sum_comm]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α _
    simp only [add_smul, Finset.sum_add_distrib]
    rw [hsum₂, hsum₂, hsymm (α 0) (α 1)]
    have hα : (![α 0, α 1] : Fin 2 → Fin n) = α := by
      funext j
      fin_cases j <;> rfl
    rw [hα, two_smul]
  -- Separate the actual degrees before evaluating their dependent derivative indices.
  have ht₀ : compositionExpansionTerm P.totalSymbol a 0 x ξ u =
      P.totalSymbol x ξ (a x ξ u) := by
    simp [compositionExpansionTerm]
  have ht₁ : compositionExpansionTerm P.totalSymbol a 1 x ξ u =
      (-Complex.I) • ∑ β : Fin 1 → Fin n,
        (fderiv ℝ (P.totalSymbol x) ξ (e (β 0)))
          (fderiv ℝ v x (e (β 0))) := by
    simp only [compositionExpansionTerm, smul_apply, sum_apply,
      ContinuousLinearMap.comp_apply]
    change ((-Complex.I) ^ (1 : ℕ) / ((1 : ℕ).factorial : ℂ)) •
      (∑ β : Fin 1 → Fin n,
        (iteratedFDeriv ℝ 1 (P.totalSymbol x) ξ (fun k ↦ e (β k)))
          (iteratedFDeriv ℝ 1 (fun y ↦ a y ξ) x (fun k ↦ e (β k)) u)) = _
    simp only [hjet]
    simp only [iteratedFDeriv_one_apply, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one]
  have ht₂ : compositionExpansionTerm P.totalSymbol a 2 x ξ u =
      ((-Complex.I) ^ 2 / (2 : ℂ)) • ∑ β : Fin 2 → Fin n,
        (iteratedFDeriv ℝ 2 (P.totalSymbol x) ξ (fun k ↦ e (β k)))
          (iteratedFDeriv ℝ 2 v x (fun k ↦ e (β k))) := by
    simp only [compositionExpansionTerm, smul_apply, sum_apply,
      ContinuousLinearMap.comp_apply]
    change ((-Complex.I) ^ (2 : ℕ) / ((2 : ℕ).factorial : ℂ)) •
      (∑ β : Fin 2 → Fin n,
        (iteratedFDeriv ℝ 2 (P.totalSymbol x) ξ (fun k ↦ e (β k)))
          (iteratedFDeriv ℝ 2 (fun y ↦ a y ξ) x (fun k ↦ e (β k)) u)) = _
    rw [show ((2 : ℕ).factorial : ℂ) = 2 by norm_num]
    simp only [hjet]
  -- Keep the three finite contractions intact while normalizing their scalar factors.
  let C₁ : W := ∑ α : Fin 1 → Fin n, A₁ α (fderiv ℝ v x (e (α 0)))
  let C₂ : W := ∑ α : Fin 2 → Fin n,
    A₂ α (ξ (α 0) • fderiv ℝ v x (e (α 1)) +
      ξ (α 1) • fderiv ℝ v x (e (α 0)))
  let D₂ : W := ∑ α : Fin 2 → Fin n,
    A₂ α (iteratedFDeriv ℝ 2 v x (fun k ↦ e (α k)))
  let R₁ : W := ∑ α : Fin 1 → Fin n,
    A₁ α ((-Complex.I) • fderiv ℝ v x (e (α 0)))
  let R₂ : W := ∑ α : Fin 2 → Fin n,
    A₂ α ((-Complex.I) •
        ((ξ (α 0) : ℂ) • fderiv ℝ v x (e (α 1)) +
          (ξ (α 1) : ℂ) • fderiv ℝ v x (e (α 0))) -
      iteratedFDeriv ℝ 2 v x (fun k ↦ e (α k)))
  have hR₁ : R₁ = (-Complex.I) • C₁ := by
    simp only [R₁, C₁, map_smul, Finset.smul_sum]
  have hR₂ : R₂ = (-Complex.I) • C₂ - D₂ := by
    simp only [R₂, C₂, D₂, Complex.coe_smul, map_sub, map_smul,
      Finset.sum_sub_distrib, Finset.smul_sum]
  -- The factorial two in the standard formula cancels the two Hessian contractions.
  rw [Fin.sum_univ_three]
  change compositionExpansionTerm P.totalSymbol a 0 x ξ u +
    compositionExpansionTerm P.totalSymbol a 1 x ξ u +
    compositionExpansionTerm P.totalSymbol a 2 x ξ u = _
  rw [ht₀, ht₁, ht₂, hc₁, hc₂]
  change P.totalSymbol x ξ (a x ξ u) + (-Complex.I) • (C₁ + C₂) +
    ((-Complex.I) ^ 2 / (2 : ℂ)) • ((2 : ℂ) • D₂) =
      P.totalSymbol x ξ (a x ξ u) + R₁ + R₂
  have hfactor : ((-Complex.I) ^ 2 / (2 : ℂ)) * 2 = -1 := by
    norm_num [neg_sq, Complex.I_sq]
  rw [hR₁, hR₂, smul_smul, hfactor, neg_one_smul]
  simp only [smul_add]
  abel

end AtiyahSinger.CoordinateDifferentialOperator

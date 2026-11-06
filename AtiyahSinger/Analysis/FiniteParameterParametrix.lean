/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.BesselSymbol
public import AtiyahSinger.Analysis.LocalCompositionCoefficient
public import AtiyahSinger.Analysis.ParameterEllipticSymbol

/-!
# Finite parameter parametrices for a positive second-order expression

Public module ID: M0627.

The joint principal inverse is corrected by a finite recursion. All corrections
use the horizontal differential expression; the last frequency is a scalar
parameter, not an additional derivative applied to the unknown function.
The first inverse's low-frequency defect is retained in the exact finite
telescoping identity and contributes only joint smoothing terms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open scoped ContDiff

variable {n r : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The lower-order part of the joint symbolic action of `1 + P` and the scalar parameter. -/
def parameterCorrectionSymbol (P : CoordinateDifferentialOperator n r r 2 U)
    (a : SymbolFunction (n + 1) r r) : SymbolFunction (n + 1) r r :=
  symbolComp (P.firstFactorLift.totalSymbol - P.firstFactorLift.principalSymbol +
    fun _ _ ↦ ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))) a +
    compositionExpansionTerm P.firstFactorLift.totalSymbol a 1 +
    compositionExpansionTerm P.firstFactorLift.totalSymbol a 2

/-- Finite recursive symbols have exact telescoping defects of successively lower joint order. -/
theorem exists_finite_parameter_symbol_sequence
    (hU : IsOpen U) (P : CoordinateDifferentialOperator n r r 2 U)
    (f : SymbolFunction (n + 1) r r)
    (hf : IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' U) 0 f)
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hprincipal : ∀ x ∈ U, ∀ ξ,
      P.principalSymbol x ξ = b x ξ • ContinuousLinearMap.id ℂ _)
    (hnonneg : ∀ x ∈ U, ∀ ξ, 0 ≤ b x ξ)
    (hpos : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → 0 < b x ξ) :
    let W := (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' U
    ∃ a₀ : SymbolFunction (n + 1) r r, ∃ a : ℕ → SymbolFunction (n + 1) r r,
      IsSymbol W (-2) a₀ ∧
      (∀ j : ℕ, IsSymbol W (-2 - (j : ℝ)) (a j)) ∧
      (∀ j : ℕ, tsupport (a j) ⊆ tsupport f) ∧
      (∀ K : Set (EuclideanSpace ℝ (Fin (n + 1))), K ⊆ W → IsCompact K →
        ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ ζ, R ≤ ‖ζ‖ →
          a₀ z ζ = (P.parameterLift.principalSymbol z ζ).inverse) ∧
      a 0 = symbolComp a₀ f ∧
      (∀ j : ℕ, a (j + 1) = (-1 : ℂ) •
        symbolComp a₀ (P.parameterCorrectionSymbol (a j))) ∧
      ∀ N : ℕ, IsSymbol W (-(N : ℝ))
        ((∑ j ∈ Finset.range N,
          (symbolComp P.parameterLift.principalSymbol (a j) +
            P.parameterCorrectionSymbol (a j))) - f) := by
  classical
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let W := (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ (e z).1) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_fst.comp e.continuous)
  let I : SymbolFunction (n + 1) r r := fun _ _ ↦ ContinuousLinearMap.id ℂ _
  let p := P.parameterLift.principalSymbol
  let E := P.parameterCorrectionSymbol
  have hI : IsSymbol W 0 I := by
    have h := isSymbol_besselSymbol (n + 1) r 0
    have hconst : besselSymbol (n + 1) r 0 = I := by
      funext x ξ
      simp [besselSymbol, I]
    rw [hconst] at h
    exact ⟨h.1.mono (Set.prod_mono (Set.subset_univ _) le_rfl),
      fun K _ hK i j ↦ h.2 K (Set.subset_univ _) hK i j⟩
  -- The actual horizontal composition coefficients raise the unknown symbol's order by one.
  have hE (m : ℝ) (a : SymbolFunction (n + 1) r r) (ha : IsSymbol W m a) :
      IsSymbol W (m + 1) (E a) := by
    have htotal : IsSymbol W 2 P.firstFactorLift.totalSymbol :=
      P.firstFactorLift.isSymbol_totalSymbol hW
    have hlower : IsSymbol W 1
        (P.firstFactorLift.totalSymbol - P.firstFactorLift.principalSymbol + I) := by
      have hdiff : IsSymbol W 1
          (P.firstFactorLift.totalSymbol - P.firstFactorLift.principalSymbol) := by
        convert P.firstFactorLift.isSymbol_totalSymbol_sub_principalSymbol hW using 1
        norm_num
      exact hdiff.add hW (hI.mono (by norm_num))
    have h₀ : IsSymbol W (m + 1)
        (symbolComp (P.firstFactorLift.totalSymbol - P.firstFactorLift.principalSymbol + I)
          a) := by
      convert hlower.symbolComp hW ha using 1
      ring
    have h₁ : IsSymbol W (m + 1)
        (compositionExpansionTerm P.firstFactorLift.totalSymbol a 1) := by
      convert isSymbol_compositionExpansionTerm_on W hW 2 m
        P.firstFactorLift.totalSymbol a htotal ha 1 using 1
      norm_num
      ring
    have h₂ : IsSymbol W m
        (compositionExpansionTerm P.firstFactorLift.totalSymbol a 2) := by
      convert isSymbol_compositionExpansionTerm_on W hW 2 m
        P.firstFactorLift.totalSymbol a htotal ha 2 using 1
      norm_num
    exact (h₀.add hW h₁).add hW (h₂.mono (by linarith))
  obtain ⟨a₀, ha₀, hdefect, hinverse⟩ :=
    P.exists_parameter_principal_inverse hU b hprincipal hnonneg hpos
  let d : SymbolFunction (n + 1) r r := symbolComp p a₀ - I
  have hd : IsSmoothingSymbol W d := hdefect
  let a : ℕ → SymbolFunction (n + 1) r r :=
    Nat.rec (symbolComp a₀ f) (fun _ q ↦ (-1 : ℂ) • symbolComp a₀ (E q))
  have ha_zero : a 0 = symbolComp a₀ f := rfl
  have hstart : IsSymbol W (-2) (a 0) := by
    convert ha₀.symbolComp hW hf using 1
    norm_num
  have ha_succ (j : ℕ) : a (j + 1) = (-1 : ℂ) • symbolComp a₀ (E (a j)) := rfl
  have ha (j : ℕ) : IsSymbol W (-2 - (j : ℝ)) (a j) := by
    induction j with
    | zero => simpa only [Nat.cast_zero, sub_zero] using hstart
    | succ j ih =>
      rw [ha_succ]
      convert (ha₀.symbolComp hW (hE (-2 - (j : ℝ)) (a j) ih)).smul hW (-1) using 1
      push_cast
      ring
  -- Horizontal differentiation and multiplication preserve the original output support.
  have hcompSupport (u v : SymbolFunction (n + 1) r r) :
      tsupport (symbolComp u v) ⊆ tsupport v := by
    apply closure_minimal _ (isClosed_tsupport _ )
    intro x hx
    by_contra hzero
    have hv : v x = 0 := image_eq_zero_of_notMem_tsupport hzero
    apply hx
    funext ξ
    simp only [symbolComp, hv, Pi.zero_apply, ContinuousLinearMap.comp_zero]
  have hESupport (q : SymbolFunction (n + 1) r r) : tsupport (E q) ⊆ tsupport q := by
    apply closure_minimal _ (isClosed_tsupport _ )
    intro x hx
    by_contra hzero
    have hnear := notMem_tsupport_iff_eventuallyEq.mp hzero
    have hvalue : q x = 0 := hnear.eq_of_nhds
    apply hx
    funext ξ
    have hjet : (fun y ↦ q y ξ) =ᶠ[nhds x] (fun _ ↦ 0) := by
      filter_upwards [hnear] with y hy
      exact congrFun hy ξ
    have hder (k : ℕ) : iteratedFDeriv ℝ k (fun y ↦ q y ξ) x = 0 := by
      rw [(hjet.iteratedFDeriv ℝ k).eq_of_nhds]
      simpa only [Pi.zero_apply] using
        congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (n := k)) x
    simp [E, parameterCorrectionSymbol, symbolComp, hvalue, compositionExpansionTerm, hder]
  have hasupport (j : ℕ) : tsupport (a j) ⊆ tsupport f := by
    induction j with
    | zero => rw [ha_zero]; exact hcompSupport a₀ f
    | succ j ih =>
      rw [ha_succ]
      exact (tsupport_smul_subset_right (fun _ ↦ (-1 : ℂ))
        (symbolComp a₀ (E (a j)))).trans
          ((hcompSupport a₀ (E (a j))).trans ((hESupport (a j)).trans ih))
  -- Every recursive principal action cancels its predecessor's correction, plus its real defect.
  have hcancel (j : ℕ) : symbolComp p (a (j + 1)) =
      -(E (a j)) - symbolComp d (E (a j)) := by
    rw [ha_succ]
    funext x ξ
    change (p x ξ).comp ((-1 : ℂ) • (a₀ x ξ).comp (E (a j) x ξ)) =
      -(E (a j) x ξ) - ((p x ξ).comp (a₀ x ξ) - ContinuousLinearMap.id ℂ _).comp
        (E (a j) x ξ)
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.id_comp, ← ContinuousLinearMap.comp_assoc]
    module
  have hsum (N : ℕ) :
      (∑ j ∈ Finset.range (N + 1), (symbolComp p (a j) + E (a j))) =
        f + symbolComp d f + E (a N) - ∑ j ∈ Finset.range N, symbolComp d (E (a j)) := by
    induction N with
    | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one, Finset.sum_range_zero, sub_zero,
        ha_zero]
      funext x ξ
      simp only [symbolComp, d, I, Pi.add_apply, Pi.sub_apply,
        ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp,
        ← ContinuousLinearMap.comp_assoc]
      abel
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hcancel N, Finset.sum_range_succ]
      abel
  refine ⟨a₀, a, ha₀, ha, hasupport, hinverse, ha_zero, fun j ↦ ha_succ j, ?_⟩
  intro N
  cases N with
  | zero =>
    have hneg : IsSymbol W 0 ((-1 : ℂ) • f) := hf.smul hW (-1)
    simpa only [Finset.sum_range_zero, zero_sub, neg_one_smul, Nat.cast_zero, neg_zero]
      using hneg
  | succ N =>
    let order : ℝ := -((N + 1 : ℕ) : ℝ)
    have hlast : IsSymbol W order (E (a N)) := by
      convert hE (-2 - (N : ℝ)) (a N) (ha N) using 1
      dsimp [order]
      push_cast
      ring
    have hdefectTerm (j : ℕ) : IsSymbol W order (symbolComp d (E (a j))) := by
      convert (hd (order - (-2 - (j : ℝ) + 1))).symbolComp hW
        (hE (-2 - (j : ℝ)) (a j) (ha j)) using 1
      ring
    have hfinite : IsSymbol W order
        (∑ j ∈ Finset.range N, symbolComp d (E (a j))) := by
      change (∑ j ∈ Finset.range N, symbolComp d (E (a j))) ∈
        symbolSpace W hW order r r
      exact Submodule.sum_mem _ (fun j _ ↦ hdefectTerm j)
    have hfirst : IsSymbol W order (symbolComp d f) := by
      convert (hd order).symbolComp hW hf using 1
      ring
    have hresult : IsSymbol W order
        (symbolComp d f + E (a N) - ∑ j ∈ Finset.range N, symbolComp d (E (a j))) :=
      (symbolSpace W hW order r r).sub_mem (hfirst.add hW hlast) hfinite
    have heq : (∑ j ∈ Finset.range (N + 1), (symbolComp p (a j) + E (a j))) - f =
        symbolComp d f + E (a N) - ∑ j ∈ Finset.range N, symbolComp d (E (a j)) := by
      rw [hsum N]
      abel
    change IsSymbol W order
      ((∑ j ∈ Finset.range (N + 1), (symbolComp p (a j) + E (a j))) - f)
    rwa [heq]

end AtiyahSinger.CoordinateDifferentialOperator

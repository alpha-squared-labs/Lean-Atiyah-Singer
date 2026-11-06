/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateDifferentialProductLift
public import AtiyahSinger.Analysis.FullSymbolEllipticity
public import AtiyahSinger.Analysis.LocallyBoundedFrequencySupport

/-!
# The elliptic principal symbol with a real resolvent parameter

Public module ID: M0847.

Adding the square of one additional coordinate derivative turns a positive
scalar second-order principal symbol into an elliptic symbol in the joint
frequency. The ordinary compact-local inverse theorem then constructs its
order-minus-two inverse. No estimate for a spectral power is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open scoped ContDiff

variable {n r : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- The original horizontal expression plus the square of the additional derivative. -/
def parameterLift (P : CoordinateDifferentialOperator n r r 2 U) :
    CoordinateDifferentialOperator (n + 1) r r 2
      ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' U) := by
  classical
  refine {
    coefficient k α z := P.firstFactorLift.coefficient k α z +
      if k.val = 2 then
        if α = fun _ ↦ Fin.last n then ContinuousLinearMap.id ℂ _ else 0
      else 0
    smooth_coefficient := ?_ }
  intro k α
  exact (P.firstFactorLift.smooth_coefficient k α).add contDiffOn_const

/-- The parameter lift adds precisely the square of the additional frequency to the symbol. -/
theorem parameterLift_totalSymbol (P : CoordinateDifferentialOperator n r r 2 U)
    (z ζ : EuclideanSpace ℝ (Fin (n + 1))) :
    P.parameterLift.totalSymbol z ζ =
      P.totalSymbol (EuclideanSpace.finAddEquivProd z).1
        (EuclideanSpace.finAddEquivProd ζ).1 +
      ζ (Fin.last n) ^ 2 • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r)) := by
  classical
  have hdegree (k : Fin 3) :
      (∑ α : Fin k.val → Fin (n + 1), (∏ j, ζ (α j)) •
        (if k.val = 2 then
          if α = fun _ ↦ Fin.last n then
            ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r)) else 0
        else 0)) =
      if k = 2 then ζ (Fin.last n) ^ 2 • ContinuousLinearMap.id ℂ _ else 0 := by
    by_cases hk : k = 2
    · subst k
      simp [smul_ite, Fin.prod_univ_succ, pow_two]
    · have hkval : k.val ≠ 2 := fun h ↦ hk (Fin.ext h)
      simp [hk, hkval]
  calc
    _ = P.firstFactorLift.totalSymbol z ζ +
        ∑ k : Fin 3, if k = 2 then
          ζ (Fin.last n) ^ 2 • ContinuousLinearMap.id ℂ _ else 0 := by
      simp only [totalSymbol, parameterLift, smul_add, Finset.sum_add_distrib, hdegree]
    _ = _ := by rw [firstFactorLift_totalSymbol]; simp

/-- The joint principal symbol uses the identical horizontal coefficients. -/
theorem parameterLift_principalSymbol (P : CoordinateDifferentialOperator n r r 2 U)
    (z ζ : EuclideanSpace ℝ (Fin (n + 1))) :
    P.parameterLift.principalSymbol z ζ =
      P.principalSymbol (EuclideanSpace.finAddEquivProd z).1
        (EuclideanSpace.finAddEquivProd ζ).1 +
      ζ (Fin.last n) ^ 2 • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r)) := by
  classical
  calc
    _ = P.firstFactorLift.principalSymbol z ζ +
        ζ (Fin.last n) ^ 2 • ContinuousLinearMap.id ℂ _ := by
      simp [principalSymbol, parameterLift, smul_add, Finset.sum_add_distrib,
        smul_ite, Fin.prod_univ_succ, pow_two]
    _ = _ := by rw [firstFactorLift_principalSymbol]

/-- Positive scalar principal data give a compact-local inverse in the joint frequency. -/
theorem exists_parameter_principal_inverse
    (hU : IsOpen U) (P : CoordinateDifferentialOperator n r r 2 U)
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hprincipal : ∀ x ∈ U, ∀ ξ,
      P.principalSymbol x ξ = b x ξ • ContinuousLinearMap.id ℂ _)
    (hnonneg : ∀ x ∈ U, ∀ ξ, 0 ≤ b x ξ)
    (hpos : ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → 0 < b x ξ) :
    let W := (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' U
    ∃ a : SymbolFunction (n + 1) r r,
      IsSymbol W (-2) a ∧
      IsSmoothingSymbol W (symbolComp P.parameterLift.principalSymbol a -
        fun _ _ ↦ ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))) ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin (n + 1))), K ⊆ W → IsCompact K →
        ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ ζ, R ≤ ‖ζ‖ →
          a z ζ = (P.parameterLift.principalSymbol z ζ).inverse := by
  classical
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  let W := (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ (e z).1) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_fst.comp e.continuous)
  let p := P.parameterLift.principalSymbol
  have hp : IsSymbol W 2 p := P.parameterLift.isSymbol_principalSymbol hW
  have hh : IsHomogeneousSymbol W 2 p :=
    P.parameterLift.isHomogeneousSymbol_principalSymbol
  -- In a nonzero joint frequency, either the horizontal covector or the last coordinate is nonzero.
  have hell : IsEllipticSymbol W p := by
    intro z hz ζ hζ
    have hlast : (e ζ).2 0 = ζ (Fin.last n) := rfl
    have hscalar : 0 < b (e z).1 (e ζ).1 + ζ (Fin.last n) ^ 2 := by
      by_cases hξ : (e ζ).1 = 0
      · have ht : ζ (Fin.last n) ≠ 0 := by
          intro ht
          apply hζ
          apply e.injective
          apply Prod.ext
          · simpa only [map_zero, Prod.fst_zero] using hξ
          · have hsecond : (e ζ).2 = 0 := by
              ext i
              have hi : i = 0 := Fin.eq_zero i
              subst i
              change (e ζ).2 0 = 0
              exact hlast.trans ht
            simpa only [map_zero, Prod.snd_zero] using hsecond
        exact add_pos_of_nonneg_of_pos (hnonneg _ hz _) (sq_pos_of_ne_zero ht)
      · exact add_pos_of_pos_of_nonneg (hpos _ hz _ hξ) (sq_nonneg _)
    have heq : p z ζ =
        (b (e z).1 (e ζ).1 + ζ (Fin.last n) ^ 2) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r)) := by
      rw [show p = P.parameterLift.principalSymbol from rfl,
        parameterLift_principalSymbol, hprincipal _ hz, ← add_smul]
    rw [heq]
    change Function.Bijective (fun v : EuclideanSpace ℂ (Fin r) ↦
      (b (e z).1 (e ζ).1 + ζ (Fin.last n) ^ 2) • v)
    simp_rw [← Complex.coe_smul]
    exact (LinearEquiv.smulOfNeZero ℂ (EuclideanSpace ℂ (Fin r))
        ((b (e z).1 (e ζ).1 + ζ (Fin.last n) ^ 2 : ℝ) : ℂ)
        (Complex.ofReal_ne_zero.mpr hscalar.ne')).bijective
  -- Compactness on the unit sphere turns homogeneity into quantitative ellipticity.
  have hcut : IsEllipticFullSymbol W 2 (frequencyCutoffSymbol p) :=
    (isEllipticFullSymbol_frequencyCutoffSymbol_iff hW p
      (hp.1.mono (Set.prod_mono le_rfl (Set.subset_univ _))) hh).mpr hell
  have hcutSymbol : IsSymbol W 2 (frequencyCutoffSymbol p) :=
    isSymbol_frequencyCutoffSymbol W hW 2 p
      (hp.1.mono (Set.prod_mono le_rfl (Set.subset_univ _))) hh
  have hrem : IsSymbol W 1 (p - frequencyCutoffSymbol p) :=
    isSmoothingSymbol_of_frequency_support hW _ 1 (hp.1.sub hcutSymbol.1)
      (fun z hz ζ hζ ↦ sub_eq_zero.mpr
        (frequencyCutoffSymbol_eq_of_one_le_norm p z ζ hζ).symm) 1
  have hfull : IsEllipticFullSymbol W 2 p := by
    have h := hcut.add_lowerOrder 1 (by norm_num)
      (show IsSymbol W (2 - 1) (p - frequencyCutoffSymbol p) from by
        convert hrem using 1
        norm_num)
    have heq : frequencyCutoffSymbol p + (p - frequencyCutoffSymbol p) = p := by abel
    rwa [heq] at h
  -- The inverse is constructed with a radius depending on the compact spatial window.
  obtain ⟨a, ha, hinverse⟩ :=
    exists_inverse_symbol_of_isEllipticFullSymbol hW p hp hfull
  refine ⟨a, ha, ?_, hinverse⟩
  -- The principal inverse defect vanishes above each compact window's frequency radius.
  apply isSmoothingSymbol_of_locally_bounded_frequency_support hW _
  · exact (hp.symbolComp hW ha).1.sub contDiffOn_const
  · intro K hKW hK
    obtain ⟨R, hR, hactual⟩ := hinverse K hKW hK
    obtain ⟨S, C, hS, hC, hbound⟩ := hfull K hKW hK
    refine ⟨max R S, ?_⟩
    intro z hz ζ hζ
    have hinv := (hbound z hz ζ ((le_max_right _ _).trans hζ)).1
    change (p z ζ).comp (a z ζ) - ContinuousLinearMap.id ℂ _ = 0
    rw [hactual z hz ζ ((le_max_left _ _).trans hζ), hinv.self_comp_inverse, sub_self]

end AtiyahSinger.CoordinateDifferentialOperator

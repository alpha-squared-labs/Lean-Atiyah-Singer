/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateDifferentialComposition
public import AtiyahSinger.Analysis.FiniteParameterParametrix
public import AtiyahSinger.Analysis.HorizontalCompositionRestriction
public import AtiyahSinger.Analysis.JointFrequencyQuantizationBound

/-!
# The actual local finite parameter resolvent identity

Public module ID: M0787.

The original differential expression acts on the quantizer of a specified finite
symbol sequence. Its exact residual is the original principal action plus every
horizontal correction, minus the specified right hand symbol. All low frequency
defects remain in this residual; no asymptotic error is silently discarded.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 25

private theorem integrable_local_quantization_integrand
    {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (m : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol U m a)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) ↦
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • a x ξ (fourierSG u ξ)) := by
  -- The zeroth jet has the same integrable majorant as the higher spatial jets.
  obtain ⟨B, hB, hbound⟩ := exists_integrable_bound_quantization_base_jet U hU m a ha
    {x} (Set.singleton_subset_iff.mpr hx) isCompact_singleton 0 u
  have haf : Continuous (a x) := by
    have hs : ContDiffOn ℝ ∞ (a x) Set.univ :=
      ha.1.comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ _ ↦ ⟨hx, Set.mem_univ _⟩)
    exact (contDiffOn_univ.mp hs).continuous
  have hFourier : Continuous (fourierSG u) :=
    (FourierTransform.fourier u).continuous.comp
      (((2 * Real.pi)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).continuous)
  have hphase : Continuous
      (fun ξ : EuclideanSpace ℝ (Fin n) ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) := by
    fun_prop
  apply hB.mono' ((hphase.fun_smul (haf.clm_apply hFourier)).aestronglyMeasurable)
  filter_upwards [] with ξ
  simpa only [norm_iteratedFDeriv_zero] using hbound x (Set.mem_singleton x) ξ

/-- Quantization commutes with a finite sum of local symbols on Schwartz inputs. -/
theorem quantize_finset_sum {ι : Type*} {n r q : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (m : ℝ) (s : Finset ι) (a : ι → SymbolFunction n r q)
    (ha : ∀ j ∈ s, IsSymbol U m (a j))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    quantize (∑ j ∈ s, a j) u x = ∑ j ∈ s, quantize (a j) u x := by
  classical
  have hint (j : ι) (hj : j ∈ s) :=
    integrable_local_quantization_integrand hU m (a j) (ha j hj) u x hx
  simp only [quantize, Finset.sum_apply, sum_apply, Finset.smul_sum]
  rw [integral_finsetSum s hint, Finset.smul_sum]

namespace CoordinateDifferentialOperator

/-- The actual operator `P + (1 + τ) Id` has the exact residual of the specified
finite symbol sequence. This statement does not assume its own operator identity
or an estimate for the residual. -/
theorem apply_quantize_finite_parameter_symbol_sequence
    {n r : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (P : CoordinateDifferentialOperator n r r 2 U)
    (f : SymbolFunction (n + 1) r r)
    (hf : IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' U) 0 f)
    (a : ℕ → SymbolFunction (n + 1) r r)
    (ha : ∀ j : ℕ, IsSymbol ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' U)
        (-2 - (j : ℝ)) (a j))
    (N : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U) :
    P.apply (quantize (jointFrequencySymbolSlice (∑ j ∈ Finset.range N, a j) τ) u) x +
        (1 + τ) • quantize (jointFrequencySymbolSlice (∑ j ∈ Finset.range N, a j) τ) u x =
      quantize (jointFrequencySymbolSlice f τ) u x +
        quantize (jointFrequencySymbolSlice
          ((∑ j ∈ Finset.range N,
            (symbolComp P.parameterLift.principalSymbol (a j) +
              P.parameterCorrectionSymbol (a j))) - f) τ) u x := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let V := EuclideanSpace ℂ (Fin r)
  let split : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let W := (fun z : Y ↦ (split z).1) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_fst.comp split.continuous)
  have hUW (y : X) (hy : y ∈ U) : split.symm (y, 0) ∈ W := by
    simpa only [W, Set.mem_preimage, split.apply_symm_apply] using hy
  let A : SymbolFunction (n + 1) r r := ∑ j ∈ Finset.range N, a j
  let R : SymbolFunction (n + 1) r r :=
    (∑ j ∈ Finset.range N,
      (symbolComp P.parameterLift.principalSymbol (a j) +
        P.parameterCorrectionSymbol (a j))) - f
  have hA : IsSymbol W (-2) A := by
    change A ∈ symbolSpace W hW (-2) r r
    exact Submodule.sum_mem _ (fun j _ ↦ (ha j).mono
      (by linarith [Nat.cast_nonneg (α := ℝ) j]))
  -- Project the actual slice membership already proved by the uniform quantization theorem.
  -- The auxiliary zero cutoff is used only to forget its norm conclusion, not to alter b.
  have hslice (m : ℝ) (hm : m ≤ 0) (b : SymbolFunction (n + 1) r r)
      (hb : IsSymbol W m b) : IsSymbol U m (jointFrequencySymbolSlice b τ) := by
    obtain ⟨hs, _⟩ := exists_uniform_quantizeSobolev_jointFrequencySymbolSlice
      W hW m 0 hm b hb U hU hUW (0 : X → ℝ) contDiff_const
      HasCompactSupport.zero (by simp)
    exact hs τ hτ
  have hAs : IsSymbol U (-2) (jointFrequencySymbolSlice A τ) := hslice _ (by norm_num) A hA
  have hfs : IsSymbol U 0 (jointFrequencySymbolSlice f τ) := hslice _ le_rfl f hf
  let C : SymbolFunction n r r :=
    ∑ k : Fin 3, compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice A τ) k.val
  have hCs : IsSymbol U 0 C := by
    change C ∈ symbolSpace U hU 0 r r
    apply Submodule.sum_mem
    intro k _
    exact (isSymbol_compositionExpansionTerm_on U hU 2 (-2) P.totalSymbol
      (jointFrequencySymbolSlice A τ) (P.isSymbol_totalSymbol hU) hAs k.val).mono
        (by linarith [Nat.cast_nonneg (α := ℝ) k.val])
  have hcompSum (L : V →L[ℂ] V) (g : ℕ → V →L[ℂ] V) :
      L.comp (∑ j ∈ Finset.range N, g j) = ∑ j ∈ Finset.range N, L.comp (g j) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  -- Linearity of the actual horizontal jets retains the originally chosen finite sequence.
  have hterm_sum (z ζ : Y) (hz : z ∈ W) (k : ℕ) :
      compositionExpansionTerm P.firstFactorLift.totalSymbol A k z ζ =
        ∑ j ∈ Finset.range N,
          compositionExpansionTerm P.firstFactorLift.totalSymbol (a j) k z ζ := by
    have hs (j : ℕ) : ContDiffAt ℝ k (fun y ↦ a j y ζ) z := by
      have hlocal : ContDiffOn ℝ ∞ (fun y ↦ a j y ζ) W :=
        (ha j).1.comp (contDiffOn_id.prodMk contDiffOn_const)
          (fun y hy ↦ ⟨hy, Set.mem_univ _⟩)
      exact (hlocal.contDiffAt (hW.mem_nhds hz)).of_le (by simp)
    have hjet : iteratedFDeriv ℝ k (fun y ↦ A y ζ) z =
        ∑ j ∈ Finset.range N, iteratedFDeriv ℝ k (fun y ↦ a j y ζ) z := by
      simpa only [A, Finset.sum_apply] using
        (iteratedFDeriv_fun_sum_apply (fun j (_ : j ∈ Finset.range N) ↦ hs j))
    simp only [compositionExpansionTerm, hjet, sum_apply, hcompSum]
    rw [Finset.sum_comm, Finset.smul_sum]
  have haction_sum (z ζ : Y) (hz : z ∈ W) :
      (P.parameterLift.principalSymbol z ζ).comp (A z ζ) +
          P.parameterCorrectionSymbol A z ζ =
        ∑ j ∈ Finset.range N,
          ((P.parameterLift.principalSymbol z ζ).comp (a j z ζ) +
            P.parameterCorrectionSymbol (a j) z ζ) := by
    simp only [parameterCorrectionSymbol, Pi.add_apply, symbolComp,
      hterm_sum z ζ hz, A, Finset.sum_apply, hcompSum,
      Finset.sum_add_distrib]
  have hsymbol (ξ : X) : C x ξ + (1 + τ) • jointFrequencySymbolSlice A τ x ξ =
      jointFrequencySymbolSlice f τ x ξ + jointFrequencySymbolSlice R τ x ξ := by
    let z := split.symm (x, (0 : EuclideanSpace ℝ (Fin 1)))
    let ζ := split.symm (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ))
    have hz : z ∈ W := hUW x hx
    have hlast : ζ (Fin.last n) = Real.sqrt τ := by
      change (split (split.symm (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ)))).2 0 = _
      rw [split.apply_symm_apply]
    have hrestrict (k : ℕ) :
        compositionExpansionTerm P.firstFactorLift.totalSymbol A k z ζ =
          compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice A τ) k x ξ :=
      compositionExpansionTerm_firstFactorLift_jointFrequencySymbolSlice
        P W hW A hA.1 τ x ξ hz k
    have hp : P.parameterLift.principalSymbol z ζ =
        P.principalSymbol x ξ + τ • ContinuousLinearMap.id ℂ V := by
      rw [parameterLift_principalSymbol, hlast, Real.sq_sqrt hτ.le]
      change P.principalSymbol (split (split.symm (x, 0))).1
        (split (split.symm (ξ, _))).1 + _ = _
      rw [split.apply_symm_apply, split.apply_symm_apply]
    have ht : P.firstFactorLift.totalSymbol z ζ = P.totalSymbol x ξ := by
      rw [firstFactorLift_totalSymbol]
      change P.totalSymbol (split (split.symm (x, 0))).1
        (split (split.symm (ξ, _))).1 = _
      rw [split.apply_symm_apply, split.apply_symm_apply]
    have hpr : P.firstFactorLift.principalSymbol z ζ = P.principalSymbol x ξ := by
      rw [firstFactorLift_principalSymbol]
      change P.principalSymbol (split (split.symm (x, 0))).1
        (split (split.symm (ξ, _))).1 = _
      rw [split.apply_symm_apply, split.apply_symm_apply]
    have hC : C x ξ = (P.totalSymbol x ξ).comp (A z ζ) +
        compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice A τ) 1 x ξ +
        compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice A τ) 2 x ξ := by
      simp only [C, Fin.sum_univ_three, Pi.add_apply]
      change compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice A τ) 0 x ξ +
        compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice A τ) 1 x ξ +
        compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice A τ) 2 x ξ = _
      rw [compositionExpansionTerm_zero]
      rfl
    have haction : (P.parameterLift.principalSymbol z ζ).comp (A z ζ) +
        P.parameterCorrectionSymbol A z ζ = C x ξ + (1 + τ) • A z ζ := by
      simp only [parameterCorrectionSymbol, Pi.add_apply, Pi.sub_apply, symbolComp,
        hp, ht, hpr, hrestrict, hC]
      have hid (v : V) : (ContinuousLinearMap.id ℂ V) v = v := rfl
      ext1 v
      simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, hid]
      rw [add_smul, one_smul]
      abel
    have hraw := haction_sum z ζ hz
    rw [haction] at hraw
    change C x ξ + (1 + τ) • A z ζ = f z ζ + R z ζ
    simp only [R, Pi.sub_apply, Finset.sum_apply, Pi.add_apply, symbolComp]
    rw [← hraw]
    abel
  -- All normalized Fourier integrands are integrable before distributing their integrals.
  let F (b : SymbolFunction n r r) (ξ : X) : V :=
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • b x ξ (fourierSG u ξ)
  have hiA : Integrable (F (jointFrequencySymbolSlice A τ)) :=
    integrable_local_quantization_integrand hU (-2) _ hAs u x hx
  have hif : Integrable (F (jointFrequencySymbolSlice f τ)) :=
    integrable_local_quantization_integrand hU 0 _ hfs u x hx
  have hiC : Integrable (F C) :=
    integrable_local_quantization_integrand hU 0 _ hCs u x hx
  have hFR : F (jointFrequencySymbolSlice R τ) =
      fun ξ ↦ F C ξ + (1 + τ) • F (jointFrequencySymbolSlice A τ) ξ -
        F (jointFrequencySymbolSlice f τ) ξ := by
    funext ξ
    have h := congrArg (fun T : V →L[ℂ] V ↦ T (fourierSG u ξ)) (hsymbol ξ)
    simp only [add_apply, smul_apply] at h
    have hv : jointFrequencySymbolSlice R τ x ξ (fourierSG u ξ) =
        C x ξ (fourierSG u ξ) + (1 + τ) •
          jointFrequencySymbolSlice A τ x ξ (fourierSG u ξ) -
            jointFrequencySymbolSlice f τ x ξ (fourierSG u ξ) := by
      apply eq_sub_iff_add_eq.mpr
      calc
        _ = jointFrequencySymbolSlice f τ x ξ (fourierSG u ξ) +
            jointFrequencySymbolSlice R τ x ξ (fourierSG u ξ) := add_comm _ _
        _ = _ := h.symm
    simp only [F, hv, smul_sub, smul_add, smul_comm (1 + τ)]
  have hquantR : quantize (jointFrequencySymbolSlice R τ) u x =
      quantize C u x + (1 + τ) • quantize (jointFrequencySymbolSlice A τ) u x -
        quantize (jointFrequencySymbolSlice f τ) u x := by
    have hq (b : SymbolFunction n r r) : quantize b u x =
        ((2 * Real.pi) ^ n)⁻¹ • ∫ ξ : X, F b ξ := rfl
    simp only [hq]
    rw [hFR, integral_sub (hiC.fun_add (hiA.fun_smul (1 + τ))) hif,
      integral_add hiC (hiA.fun_smul (1 + τ)), integral_smul]
    simp only [smul_sub, smul_add, smul_comm ((2 * Real.pi) ^ n)⁻¹]
  change P.apply (quantize (jointFrequencySymbolSlice A τ) u) x +
      (1 + τ) • quantize (jointFrequencySymbolSlice A τ) u x =
    quantize (jointFrequencySymbolSlice f τ) u x +
      quantize (jointFrequencySymbolSlice R τ) u x
  rw [apply_quantize_eq_quantize_sum_order_two hU P (-2) _ hAs u x hx, hquantR]
  change quantize C u x + _ = _
  abel

end CoordinateDifferentialOperator

end AtiyahSinger

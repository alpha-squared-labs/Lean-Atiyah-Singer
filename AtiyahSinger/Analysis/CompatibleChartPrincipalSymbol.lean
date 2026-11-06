/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompatibleChartCommonSymbols
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol

import AtiyahSinger.Analysis.AtlasSmoothingKernel
import AtiyahSinger.Analysis.AtlasGlobalSymbolTopology
import AtiyahSinger.Analysis.CompactKernelSymbol
import AtiyahSinger.Analysis.SymbolLocality

/-!
# Principal classes of compatible chart representations

Public module ID: M0372.

The principal class of an actual PDO can be computed from a finite family of
complete Fourier actions in compatible charts. Common localization retains
exact section actions; the actual smoothing remainder then has a full symbol
of every order. Subtracting the local lower-order errors proves equality in
the original principal quotient. Source: SG III.3.18--3.19.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]

set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the finite chart, cutoff and principal-quotient comparison.

open scoped Classical in
/-- A finite compatible-chart representation computes the original PDO principal class. -/
theorem AtlasPseudodifferentialOperator.principalSymbol_eq_of_compatible_representation
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (N' : ℕ)
    (d : Fin N' → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : ∀ j, d j ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : ∀ j, AtlasChartCutoff A (d j)) (Dout : ∀ j, AtlasChartCutoff B (d j))
    (hio : ∀ j, tsupport (Din j).cutoff ⊆ (d j).symm ⁻¹' (B.chart (Dout j).frameIndex).baseSet)
    (hoi : ∀ j, tsupport (Dout j).cutoff ⊆ (d j).symm ⁻¹' (A.chart (Din j).frameIndex).baseSet)
    (T : ∀ j, 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (Din j).frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank (Dout j).frameIndex))))
    (a : ∀ j, SymbolFunction n (A.rank (Din j).frameIndex) (B.rank (Dout j).frameIndex))
    (ha : ∀ j, IsSymbol univ m (a j)) (hT : ∀ j u x, T j u x = quantize (a j) u x)
    (Lin : ∀ j, A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (Din j).frameIndex))))
    (Lout : ∀ j,
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank (Dout j).frameIndex)))
        →ₗ[ℂ] B.smoothSections)
    (hLin : ∀ j u z, Lin j u z = (Din j).localizedFunction u z)
    (hLout : ∀ j v x, (Lout j v).val x = (Dout j).extendedFunction v x)
    (g : Fin N' → atlasGlobalSymbolSpace A B m)
    (hg : ∀ j x ξ, (g j).val x ξ =
      if h : x ∈ (d j).source ∩ (A.chart (Din j).frameIndex).baseSet ∩
          (B.chart (Dout j).frameIndex).baseSet then
        (((Dout j).cutoff (d j x) * (Din j).cutoff (d j x) : ℝ) : ℂ) •
          ((B.frameLinearEquiv (Dout j).frameIndex x h.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (B.rank (Dout j).frameIndex)) ℂ).toLinearMap).comp
            ((a j (d j x) (covectorInChart (d j) x ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (A.rank (Din j).frameIndex)) ℂ).symm.toLinearMap).comp
                (A.frameLinearEquiv (Din j).frameIndex x h.1.2).toLinearMap))
      else 0)
    (hR : IsAtlasSmoothingOperator A B (P.toLinearMap -
      ∑ j, (Lout j).comp ((T j).toLinearMap.comp (Lin j)))) :
    P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m (∑ j, g j) := by
  classical
  obtain ⟨N, L, hL⟩ := P.isPseudodifferentialOperator
  rw [P.principalSymbol_eq_of_representation N L hL]
  let Jmap (j : Fin N') := (Lout j).comp ((T j).toLinearMap.comp (Lin j))
  have h : IsAtlasSmoothingOperator A B
      ((∑ j, (L j).toLinearMap) - ∑ j, Jmap j) := by
    intro D K s t
    obtain ⟨R, hR'⟩ := hR D K s t
    obtain ⟨R', hR''⟩ := hL D K s t
    refine ⟨R - R', fun u ↦ ?_⟩
    rw [sub_apply, hR', hR'', ← map_sub]
    congr 1
    simp only [LinearMap.sub_apply]
    abel
  rw [atlasGlobalPrincipalSymbolClass_eq_iff]
  intro c hc e f
  let X := EuclideanSpace ℝ (Fin n)
  let U := atlasSymbolChartDomain A B c e f
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B c e f
  apply IsSymbol.of_locally hU
  intro z hz
  -- Both representations use one finite family, one chart and the same two cutoffs.
  let dd : Fin N ⊕ Fin N' → OpenPartialHomeomorph M X :=
    Sum.elim (fun j ↦ (L j).chart) d
  have hdd : ∀ j, dd j ∈ maximalAtlas 𝓘(ℝ, X) ∞ M := by
    intro j
    cases j with
    | inl j => exact subset_maximalAtlas (L j).chart_mem_atlas
    | inr j => exact hd j
  let Di : ∀ j, AtlasChartCutoff A (dd j) := fun j ↦ match j with
    | Sum.inl k => (L k).input
    | Sum.inr k => Din k
  let Do : ∀ j, AtlasChartCutoff B (dd j) := fun j ↦ match j with
    | Sum.inl k => (L k).output
    | Sum.inr k => Dout k
  have hio' : ∀ j, tsupport (Di j).cutoff ⊆ (dd j).symm ⁻¹'
      (B.chart (Do j).frameIndex).baseSet := by
    intro j
    cases j with
    | inl j => exact (L j).input_support_in_output_frame
    | inr j => exact hio j
  have hoi' : ∀ j, tsupport (Do j).cutoff ⊆ (dd j).symm ⁻¹'
      (A.chart (Di j).frameIndex).baseSet := by
    intro j
    cases j with
    | inl j => exact (L j).output_support_in_input_frame
    | inr j => exact hoi j
  let TT : ∀ j, 𝓢(X, EuclideanSpace ℂ (Fin (A.rank (Di j).frameIndex))) →L[ℂ]
      𝓢(X, EuclideanSpace ℂ (Fin (B.rank (Do j).frameIndex))) := fun j ↦ match j with
    | Sum.inl k => (L k).operator
    | Sum.inr k => T k
  let aa : ∀ j, SymbolFunction n (A.rank (Di j).frameIndex) (B.rank (Do j).frameIndex) :=
    fun j ↦ match j with
    | Sum.inl k => (L k).symbol
    | Sum.inr k => a k
  have haa : ∀ j, IsSymbol univ m (aa j) := by
    intro j
    cases j with
    | inl j => exact (L j).isSymbol
    | inr j => exact ha j
  have hTT : ∀ j u x, TT j u x = quantize (aa j) u x := by
    intro j
    cases j with
    | inl j => exact (L j).operator_apply
    | inr j => exact hT j
  let II : ∀ j, A.smoothSections →ₗ[ℂ]
      𝓢(X, EuclideanSpace ℂ (Fin (A.rank (Di j).frameIndex))) := fun j ↦ match j with
    | Sum.inl k => (L k).input.localizeLinearMap (L k).chart_mem_atlas
    | Sum.inr k => Lin k
  let OO : ∀ j, 𝓢(X, EuclideanSpace ℂ (Fin (B.rank (Do j).frameIndex))) →ₗ[ℂ]
      B.smoothSections := fun j ↦ match j with
    | Sum.inl k => (L k).output.extendLinearMap (L k).chart_mem_atlas
    | Sum.inr k => Lout k
  have hII : ∀ j u x, II j u x = (Di j).localizedFunction u x := by
    intro j
    cases j with
    | inl j => exact fun _ _ ↦ rfl
    | inr j => exact hLin j
  have hOO : ∀ j v x, (OO j v).val x = (Do j).extendedFunction v x := by
    intro j
    cases j with
    | inl j => exact fun _ _ ↦ rfl
    | inr j => exact hLout j
  let gg : Fin N ⊕ Fin N' → AtlasSymbolFunction (n := n) E F :=
    Sum.elim (fun j ↦ (L j).globalSymbolFunction) (fun j ↦ (g j).val)
  have hgg : ∀ j x ξ, gg j x ξ =
      if h : x ∈ (dd j).source ∩ (A.chart (Di j).frameIndex).baseSet ∩
          (B.chart (Do j).frameIndex).baseSet then
        (((Do j).cutoff (dd j x) * (Di j).cutoff (dd j x) : ℝ) : ℂ) •
          ((B.frameLinearEquiv (Do j).frameIndex x h.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (B.rank (Do j).frameIndex)) ℂ).toLinearMap).comp
            ((aa j (dd j x) (covectorInChart (dd j) x ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (A.rank (Di j).frameIndex)) ℂ).symm.toLinearMap).comp
                (A.frameLinearEquiv (Di j).frameIndex x h.1.2).toLinearMap))
      else 0 := by
    intro j
    cases j with
    | inl j => exact fun _ _ ↦ rfl
    | inr j => exact hg j
  obtain ⟨D₀, K₀, rfl, rfl, V, p, hV, hzV, hVU, hp, hplower, hpaction⟩ :=
    exists_common_local_symbols_of_mem_maximalAtlas A B dd hdd Di Do hio' hoi'
      TT aa haa hTT II OO hII hOO gg hgg c hc e f z hz
  -- The two returned atlas cutoffs include exactly the common scalar multiplier.
  -- Apply the all-order smoothing kernel bridge to this original operator difference.
  obtain ⟨k, hk, hck, hkact⟩ := h.exists_compactKernel _ c hc D₀ K₀
  let r := A.rank D₀.frameIndex
  let q := B.rank K₀.frameIndex
  let a : SymbolFunction n r q := (∑ j : Fin N, p (Sum.inl j)) - ∑ j : Fin N', p (Sum.inr j)
  have ha : IsSymbol Set.univ m a := (symbolSpace Set.univ isOpen_univ m r q).sub_mem
    ((symbolSpace Set.univ isOpen_univ m r q).sum_mem (fun j _ ↦ hp (Sum.inl j)))
    ((symbolSpace Set.univ isOpen_univ m r q).sum_mem (fun j _ ↦ hp (Sum.inr j)))
  -- Frequency integrability makes quantization linear in these full symbols.
  have hInt (b : SymbolFunction n r q) (hb : IsSymbol Set.univ m b)
      (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        b x ξ (fourierSG u ξ)) := by
    let Er := EuclideanSpace ℂ (Fin r)
    let Eq := EuclideanSpace ℂ (Fin q)
    have hg : (b x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry b) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hb.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hb.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have hbound' := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at hbound'
        apply hbound'.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : X ↦
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let d : X ≃L[ℝ] X :=
      (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (Er →L[ℂ] Eq)).flip (hphase.smul hg) w).integrable
  have hquant (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      quantize a u x = (∑ j : Fin N, quantize (p (Sum.inl j)) u x) -
        ∑ j : Fin N', quantize (p (Sum.inr j)) u x := by
    let Q : symbolSpace Set.univ isOpen_univ m r q →ₗ[ℂ] EuclideanSpace ℂ (Fin q) :=
      { toFun := fun b ↦ quantize b.val u x
        map_add' := by
          intro b d
          simp only [quantize, Submodule.coe_add, Pi.add_apply, add_apply, smul_add]
          rw [integral_add (hInt b.val b.property u x) (hInt d.val d.property u x), smul_add]
        map_smul' := by
          intro t b
          simp only [quantize, Submodule.coe_smul, Pi.smul_apply, smul_apply,
            RingHom.id_apply, smul_comm (Complex.exp _), integral_smul]
          exact smul_comm _ _ _ }
    have hQ := map_sub Q
      (∑ j : Fin N, (⟨p (Sum.inl j), hp (Sum.inl j)⟩ :
        symbolSpace Set.univ isOpen_univ m r q))
      (∑ j : Fin N', (⟨p (Sum.inr j), hp (Sum.inr j)⟩ :
        symbolSpace Set.univ isOpen_univ m r q))
    simpa only [map_sum, Q, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_sub, Submodule.coe_sum] using hQ
  have haeq : a = compactKernelSymbol k := by
    apply symbol_eq_of_quantize_eq m m a (compactKernelSymbol k) ha
      (isSmoothingSymbol_compactKernelSymbol k hk hck m)
    intro u x
    rw [hquant, quantize_compactKernelSymbol k hk hck, ← hkact]
    simp_rw [hpaction]
    change (∑ j : Fin N, K₀.localizeLinearMap hc
        ((L j).toLinearMap (D₀.extend hc u)) x) -
      (∑ j : Fin N', K₀.localizeLinearMap hc
        ((Jmap j) (D₀.extend hc u)) x) = K₀.localizeLinearMap hc
      (((∑ j : Fin N, (L j).toLinearMap) -
        ∑ j : Fin N', Jmap j) (D₀.extend hc u)) x
    simp
  -- The exact localized difference is smoothing; its discrepancy from the original
  -- global representatives was already shown to have one lower order on V.
  have halower : IsSymbol V (m - 1) a := by
    rw [haeq]
    exact (isSmoothingSymbol_compactKernelSymbol k hk hck (m - 1)).restrict (Set.subset_univ _)
  let gdiff : SymbolFunction n r q := atlasGlobalSymbolInChart A B
    ((∑ j : Fin N, (L j).globalSymbol).val - (∑ j : Fin N', g j).val)
    c D₀.frameIndex K₀.frameIndex
  have hrem : IsSymbol V (m - 1) (a - gdiff) := by
    have hh : IsSymbol V (m - 1)
        ((∑ j : Fin N, (p (Sum.inl j) -
          atlasGlobalSymbolInChart A B (gg (Sum.inl j)) c
            D₀.frameIndex K₀.frameIndex)) -
        ∑ j : Fin N', (p (Sum.inr j) -
          atlasGlobalSymbolInChart A B (gg (Sum.inr j)) c
            D₀.frameIndex K₀.frameIndex)) :=
      (symbolSpace V hV (m - 1) r q).sub_mem
      ((symbolSpace V hV (m - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inl j)))
      ((symbolSpace V hV (m - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inr j)))
    convert hh using 1
    ext y η v
    by_cases hframes : c.symm y ∈ (A.chart D₀.frameIndex).baseSet ∧
        c.symm y ∈ (B.chart K₀.frameIndex).baseSet
    all_goals
      simp [a, gdiff, gg, atlasGlobalSymbolInChart, AtlasPseudodifferentialPiece.globalSymbol,
        Finset.sum_sub_distrib, hframes]
    all_goals abel
  refine ⟨V, hV, hzV, hVU, ?_⟩
  have hdiff := (symbolSpace V hV (m - 1) r q).sub_mem halower hrem
  change IsSymbol V (m - 1) (a - (a - gdiff)) at hdiff
  change IsSymbol V (m - 1) gdiff
  simpa only [sub_sub_cancel] using hdiff

end AtiyahSinger

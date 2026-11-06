/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialPrincipalSymbol
public import AtiyahSinger.Analysis.RelativeEllipticRealization

import all AtiyahSinger.Analysis.ExcisionLocalization

/-!
# The actual compact realization of a specified relative finite family

Public module ID: M0913.

The sum of a supplied finite family's principal representatives and a smooth
bundle multiplier agrees with the specified degree-zero homogeneous elliptic
symbol at high frequency. Their actual section actions define an elliptic
realization that retains every lower-order cutoff term. The principal-class
comparison uses a uniform lower bound for the specified cotangent metric on
each compact chart cosphere.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The source section operator and its principal regularization use the very same finite family.
/-- A prescribed relative finite quantization gives an elliptic operator on a compact base. -/
theorem exists_relative_compact_realization_of_pieces
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap))
    (g₀ : SmoothCotangentMetric (n := n) (M := M)) (k : ℕ)
    (T : Fin k → PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (hprincipal : ∀ x ξ, 1 ≤ g₀.length x ξ →
      (∑ j, (T j).globalSymbol).val x ξ + c x = a.val x ξ)
    (A : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber) :
    ∃ P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber μ 0,
      P.IsElliptic ∧
      P.toLinearMap = smoothSectionMap (fun x ↦ (c x).toLinearMap) hc +
        ∑ j, (T j).toLinearMap ∧
      P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
        (A.regularizedSymbol 0 a.val a.property.1 a.property.2) := by
  classical
  have hzero : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ]
        smoothSections (n := n) (r := F.rank) F.Fiber) := by
    let K : SmoothKernel (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro i j _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames E.Fiber F.Fiber (fun _ _ ↦ 0) i j z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    ext u x
    change K.apply μ u x = 0
    simp [SmoothKernel.apply, K]
  let S : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0 :=
    ⟨∑ j, (T j).toLinearMap, ⟨k, T, by simpa using hzero⟩⟩
  let p : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 :=
    ∑ j, (T j).globalSymbol
  have hSp : S.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0 p := by
    exact S.principalSymbol_eq_of_representation k T (by simpa [S] using hzero)
  -- The order-zero differential operator has exactly the prescribed multiplier as its symbol.
  let B : DifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 :=
    ⟨smoothSectionMap (fun x ↦ (c x).toLinearMap) hc,
      isDifferentialOperator_smoothSectionMap _ hc⟩
  let bD : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 :=
    ⟨B.principalSymbolFunction, by
      change IsGlobalSymbol E.Fiber F.Fiber 0 B.principalSymbolFunction
      simpa only [Nat.cast_zero] using B.isGlobalSymbol_principalSymbolFunction⟩
  have hbD (x : M) (ξ : CotangentFiber (n := n) x) : bD.val x ξ = c x := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := E.rank) x v
    have hact := zeroOrder_apply_eq_principalSymbol B u x ξ
    change c x (u.val x) = B.principalSymbol x ξ (u.val x) at hact
    change B.principalSymbol x ξ v = c x v
    simpa only [hu] using hact.symm
  let B₀ : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0 :=
    ⟨B.toLinearMap, by simpa only [Nat.cast_zero] using
      B.isPseudodifferentialOperator (μ := μ)⟩
  have hBclass : B₀.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0 bD := by
    have htransport (s : ℝ) (hs : ((0 : ℕ) : ℝ) = s)
        (B' : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
          E.Fiber F.Fiber μ s)
        (b' : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber s)
        (hop : B'.toLinearMap = B.toLinearMap) (hsym : b'.val = B.principalSymbolFunction) :
        B'.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber s b' := by
      subst s
      rw [B'.principalSymbol_eq_of_toLinearMap_eq μ (B.toPseudodifferentialOperator μ) hop,
        B.principalSymbol_toPseudodifferentialOperator μ]
      congr 1
      exact Subtype.ext hsym.symm
    exact htransport 0 Nat.cast_zero B₀ bD rfl rfl
  let P := S.add B₀
  let q := p + bD
  have hPq : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0 q := by
    rw [PseudodifferentialOperator.principalSymbol_add, hSp, hBclass, ← map_add]
  have hhigh (x : M) (ξ : CotangentFiber (n := n) x) (hξ : 1 ≤ g₀.length x ξ) :
      q.val x ξ = a.val x ξ := by
    change p.val x ξ + bD.val x ξ = a.val x ξ
    rw [hbD]
    exact hprincipal x ξ hξ
  -- The actual full representative agrees with the requested regularization at chart infinity.
  have hPa : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
      (A.regularizedSymbol 0 a.val a.property.1 a.property.2) := by
    rw [hPq, globalPrincipalSymbolClass_eq_iff]
    apply isGlobalSymbol_sub_of_high_frequency q
      (A.regularizedSymbol 0 a.val a.property.1 a.property.2)
    intro c hcat i j _ _ C hC hCV
    let X := EuclideanSpace ℝ (Fin n)
    let ℓ (z η : X) := g₀.length (c.symm z) (covectorFromChart c (c.symm z) η)
    have hne (z η : X) (hz : z ∈ C) (hη : η ≠ 0) :
        covectorFromChart c (c.symm z) η ≠ 0 := by
      intro heq
      have h := covectorInChart_covectorFromChart c hcat (c.symm z)
        (c.map_target (hCV hz).1.1) η
      rw [heq] at h
      apply hη
      rw [← h]
      ext v
      rfl
    have hcont : ContinuousOn (Function.uncurry ℓ) (C ×ˢ Metric.sphere (0 : X) 1) :=
      (g₀.contDiffOn_length_covectorFromChart c hcat).continuousOn.mono (by
        intro z hz
        exact ⟨(hCV hz.1).1.1, by intro heq; simpa [heq] using hz.2⟩)
    obtain ⟨δ, hδ, hlow⟩ := (hC.prod (isCompact_sphere (0 : X) 1)).exists_forall_le'
      hcont (a := 0) (by
        intro z hz
        exact g₀.length_pos _ _ (hne z.1 z.2 hz.1 (by
          intro heq
          simpa [heq] using hz.2)))
    obtain ⟨r, _, hr⟩ := A.regularizedSymbolFunction_eq_inChart_at_high_frequency
      a.val c hcat i j C hC hCV
    refine ⟨max δ⁻¹ r, ?_⟩
    intro z hz η hη
    have hl : δ⁻¹ ≤ ‖η‖ := (le_max_left _ _).trans hη
    have hn : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hδ) hl
    let u := ‖η‖⁻¹ • η
    have hu : u ∈ Metric.sphere (0 : X) 1 := by
      simpa [u, mem_sphere_zero_iff_norm] using
        norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.mp hn)
    have hscale : ℓ z η = ‖η‖ * ℓ z u := by
      have hηeq : ‖η‖ • u = η := by simp [u, smul_smul, hn.ne']
      conv_lhs => rw [← hηeq]
      change g₀.length _ (covectorFromChart c _ (‖η‖ • u)) = _
      have hcov : covectorFromChart c (c.symm z) (‖η‖ • u) =
          ‖η‖ • covectorFromChart c (c.symm z) u := by
        ext v
        change inner ℝ (‖η‖ • u) _ = ‖η‖ * inner ℝ u _
        exact real_inner_smul_left _ _ _
      rw [hcov, g₀.length_smul, abs_of_nonneg (norm_nonneg _)]
    have hone : 1 ≤ ℓ z η := by
      rw [hscale]
      calc
        1 = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
        _ ≤ ‖η‖ * δ := mul_le_mul_of_nonneg_right hl hδ.le
        _ ≤ ‖η‖ * ℓ z u := mul_le_mul_of_nonneg_left (hlow (z, u) ⟨hz, hu⟩) hn.le
    change globalSymbolInChart E.Fiber F.Fiber q.val c i j z η =
      globalSymbolInChart E.Fiber F.Fiber (A.regularizedSymbolFunction a.val) c i j z η
    rw [hr z hz η ((le_max_right _ _).trans hη)]
    have hp : q.val (c.symm z) (covectorFromChart c (c.symm z) η) =
        a.val (c.symm z) (covectorFromChart c (c.symm z) η) := by
      exact hhigh (c.symm z) (covectorFromChart c (c.symm z) η) hone
    simp only [globalSymbolInChart, hp]
  refine ⟨P, (P.isElliptic_iff_homogeneous A a hPa).mpr ha, ?_, hPa⟩
  change (∑ j, (T j).toLinearMap) + B.toLinearMap =
    B.toLinearMap + ∑ j, (T j).toLinearMap
  exact add_comm _ _

end AtiyahSinger

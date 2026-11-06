/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductCotangentBounds
public import AtiyahSinger.Analysis.AssociatedProductCotangentSplitting
public import AtiyahSinger.Analysis.SymbolFrequencyLipschitz

/-!
# Actual transverse variation of the pulled lifted symbol

The original uncut product amplitude, transformed through the actual associated
product chart, has a uniform linear bound in its transverse frequency on a
compact overlap window. The proof retains the original full symbol and the
actual mixed cotangent block. It does not assert that the uncut amplitude is
a standard symbol of joint order one.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set
open scoped ContDiff Manifold Topology

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r k l : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

set_option maxSynthPendingDepth 30

set_option maxHeartbeats 2400000 in

/-- The original pulled uncut symbol varies at most linearly in transverse frequency. -/
theorem exists_associatedSphereProductChart_liftedSymbol_transverse_bound
    (b₁ b₂ : B)
    (c₁ c₂ : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc₁ : c₁ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (hc₂ : c₂ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (d₁ d₂ : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
    (hd₁ : d₁ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (hd₂ : d₂ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (a : SymbolFunction n k l) (ha : IsSymbol univ 1 a)
    (χ : EuclideanSpace ℝ (Fin r) → ℝ) (hχ : Continuous χ)
    (K : Set (EuclideanSpace ℝ (Fin (n + r)))) (hK : IsCompact K) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let e := (associatedSphereProductChart S b₁ c₁ d₁).symm.trans
      (associatedSphereProductChart S b₂ c₂ d₂)
    K ⊆ e.target → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
      ∀ (ξ : EuclideanSpace ℝ (Fin n)) (η : EuclideanSpace ℝ (Fin r)),
        ‖cotangentSymbol e (liftedProductSymbol a χ) z (split.symm (ξ, η)) -
          cotangentSymbol e (liftedProductSymbol a χ) z (split.symm (ξ, 0))‖ ≤ C * ‖η‖ := by
  classical
  intro split e hKe
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin r)
  let H := EuclideanSpace ℝ (Fin (n + r))
  let pr : H →L[ℝ] X := (ContinuousLinearMap.fst ℝ X Y).comp split.toContinuousLinearMap
  let qr : H →L[ℝ] Y := (ContinuousLinearMap.snd ℝ X Y).comp split.toContinuousLinearMap
  let inx : X →L[ℝ] H := split.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ X Y)
  let A (z : H) : X →L[ℝ] X := fderiv ℝ (c₁.symm.trans c₂) (pr (e.symm z))
  let B (z : H) : X →L[ℝ] Y := qr.comp ((fderiv ℝ e (e.symm z)).comp inx)
  -- At zero cutoff parameter the specified symbol is exactly the original uncut amplitude.
  have hprofile : productCutoffProfile 0 = 0 := by
    let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    change 1 - φ 0 = 0
    have hzero : (0 : ℝ) ∈ Metric.closedBall 0 φ.rIn := by simp [φ]
    rw [φ.one_of_mem_closedBall hzero, sub_self]
  have hcutoff (ρ σ : ℝ) : productFrequencyCutoff 0 ρ σ = 1 := by
    simp only [productFrequencyCutoff, zero_mul, hprofile, zero_mul, sub_zero]
  have hsymbol : productCutoffSymbol a χ 0 = liftedProductSymbol a χ := by
    funext z ξ
    change (productFrequencyCutoff 0 ‖(split ξ).1‖ ‖(split ξ).2‖ : ℂ) •
      liftedProductSymbol a χ z ξ = liftedProductSymbol a χ z ξ
    rw [hcutoff, Complex.ofReal_one, one_smul]
  have hformula (z : H) (hz : z ∈ K) (ξ : X) (η : Y) :
      cotangentSymbol e (liftedProductSymbol a χ) z (split.symm (ξ, η)) =
        (χ (qr (e.symm z)) : ℂ) • a (pr (e.symm z)) ((A z).adjoint ξ + (B z).adjoint η) := by
    have h := cotangentSymbol_productCutoffSymbol_associatedSphereProductChart_split
      S b₁ b₂ c₁ c₂ hc₁ hc₂ d₁ d₂ hd₁ hd₂ a χ 0 z (hKe hz) ξ η
    simpa only [hsymbol, hcutoff, Complex.ofReal_one, one_smul] using h
  -- The same compact window controls both the original symbol's spatial argument and cutoff.
  have hpr : ContinuousOn (fun z : H ↦ pr (e.symm z)) e.target :=
    pr.continuous.comp_continuousOn e.continuousOn_symm
  let K₀ : Set X := (fun z : H ↦ pr (e.symm z)) '' K
  have hK₀ : IsCompact K₀ := hK.image_of_continuousOn (hpr.mono hKe)
  obtain ⟨L, hL, hlip⟩ := ha.exists_frequency_lipschitz_bound K₀ (subset_univ _) hK₀
  have hχcont : ContinuousOn (fun z : H ↦ χ (qr (e.symm z))) K :=
    ((hχ.comp qr.continuous).comp_continuousOn e.continuousOn_symm).mono hKe
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hχcont
  let W := max M 0
  have hW : 0 ≤ W := le_max_right _ _
  have hweight (z : H) (hz : z ∈ K) : ‖χ (qr (e.symm z))‖ ≤ W :=
    (hM z hz).trans (le_max_left _ _)
  obtain ⟨D, hD, hblocks⟩ := exists_associatedSphereProductChart_cotangent_block_bounds
    S b₁ b₂ c₁ c₂ hc₁ hc₂ d₁ d₂ hd₁ hd₂ K hK hKe
  have hDnonneg : 0 ≤ D := le_trans zero_le_one hD
  refine ⟨W * L * D, by positivity, ?_⟩
  intro z hz ξ η
  rw [hformula z hz ξ η, hformula z hz ξ 0, map_zero, add_zero, ← smul_sub, norm_smul,
    Complex.norm_real]
  have hfreq : ‖a (pr (e.symm z)) ((A z).adjoint ξ + (B z).adjoint η) -
      a (pr (e.symm z)) ((A z).adjoint ξ)‖ ≤ L * ‖(B z).adjoint η‖ := by
    simpa only [add_sub_cancel_left] using hlip (pr (e.symm z)) ⟨z, hz, rfl⟩
      ((A z).adjoint ξ) ((A z).adjoint ξ + (B z).adjoint η)
  have hB : ‖(B z).adjoint η‖ ≤ D * ‖η‖ :=
    ((B z).adjoint.le_opNorm η).trans
      (mul_le_mul_of_nonneg_right (hblocks z hz).2.2.1 (norm_nonneg η))
  calc
    _ ≤ W * (L * ‖(B z).adjoint η‖) :=
      mul_le_mul (hweight z hz) hfreq (norm_nonneg _) hW
    _ ≤ W * (L * (D * ‖η‖)) := by gcongr
    _ = (W * L * D) * ‖η‖ := by ring

end AtiyahSinger

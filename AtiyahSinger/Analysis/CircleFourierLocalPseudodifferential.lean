/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CircleFourierPeriodization
public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Analysis.HomogeneousSymbolTopology
public import AtiyahSinger.Analysis.PeriodicFourierQuantization
public import AtiyahSinger.Analysis.SmoothSectionMultiplication
public import AtiyahSinger.Geometry.CircleAngularChartDerivative
public import AtiyahSinger.Geometry.CircleCotangent
public import AtiyahSinger.Geometry.CirclePeriodOneChart

import all AtiyahSinger.Analysis.CoordinateChange
import all AtiyahSinger.Analysis.OpenPieceSymbol

/-!
# Local PDO realization of the specified circle Fourier projection

Public module ID: M0323.

Compact localization in a native stereographic chart is transported from the
exact period-one Fourier quantizer. All angular cutoffs are retained until the
operator identity, and both coordinate changes use the existing native chart.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory FourierTransform Set
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 20

attribute [local instance] isSmoothComplexBundle_fourierCircleLine
  isSmoothPositiveMeasure_fourierCircleMeasure finrank_real_complex_fact'

set_option maxHeartbeats 1200000 in

/-- The original localized projection has an exact native piece and its two-branch
principal symbol, with the same input and output cutoff weights. -/
theorem exists_circleLocalizedProjection_piece
    (P : smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ]
      smoothSections (n := 1) (r := 1) FourierCircleLine)
    (hP : ∀ u, circleSmoothToFourierL2 (P u) =
      circleNonnegativeFourierProjection (circleSmoothToFourierL2 u))
    (c : OpenPartialHomeomorph Circle (EuclideanSpace ℝ (Fin 1)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle)
    (φ ψ : Circle → ℂ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ ψ)
    (hφc : tsupport φ ⊆ c.source) (hψc : tsupport ψ ⊆ c.source) :
    ∃ L : PseudodifferentialPiece (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine 0,
      L.toLinearMap = (smoothSectionMul FourierCircleLine ψ hψ).comp
        (P.comp (smoothSectionMul FourierCircleLine φ hφ)) ∧
      ∀ (T : QuantizationPresentation (n := 1) (r := 1) (q := 1)
          FourierCircleLine FourierCircleLine)
        (a : homogeneousGlobalSymbolSpace (n := 1) (r := 1) (q := 1)
          FourierCircleLine FourierCircleLine 0),
        (∀ z ξ, a.val z ξ = (ψ z * φ z) •
          (if 0 < circleCovectorCoordinate z ξ then
            ContinuousLinearMap.id ℂ (FourierCircleLine z) else 0)) →
        IsGlobalSymbol (n := 1) (r := 1) (q := 1)
          FourierCircleLine FourierCircleLine (-1)
          (L.globalSymbolFunction - T.regularizedSymbolFunction a.val) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let X := EuclideanSpace ℝ (Fin 1)
  let Y := EuclideanSpace ℂ (Fin 1)
  let l : X ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  let s : Y ≃ₗᵢ[ℂ] ℂ := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm
  have hs (v : Y) : s v = v 0 := by
    simpa only [OrthonormalBasis.singleton_repr] using
      congrArg (fun w : Y ↦ w 0)
        ((OrthonormalBasis.singleton (Fin 1) ℂ).repr.apply_symm_apply v)
  obtain ⟨a, b, hb, hbS, hbT, heS, heT, heval, he, hei⟩ := exists_circlePeriodOneChart c hc
  let e : OpenPartialHomeomorph X X :=
    l.toHomeomorph.toOpenPartialHomeomorph.trans (b.trans c)
  change e.source = l ⁻¹' Ioo a (a + 1) at heS
  change e.target = univ at heT
  change ContDiffOn ℝ ∞ e e.source at he
  change ContDiff ℝ ∞ e.symm at hei
  have hcT : c.target = univ := by
    obtain ⟨v, rfl⟩ := hc
    exact stereographic'_target _
  -- A single compact angular window contains the original input and output supports.
  let K₀ : Set Circle := tsupport φ ∪ tsupport ψ
  have hK₀ : IsCompact K₀ := (isClosed_tsupport φ |>.union (isClosed_tsupport ψ)).isCompact
  have hK₀T : K₀ ⊆ b.target := by
    rw [hbT]
    exact union_subset hφc hψc
  let K₁ : Set ℝ := b.symm '' K₀
  have hK₁ : IsCompact K₁ := hK₀.image_of_continuousOn (b.continuousOn_symm.mono hK₀T)
  have hK₁S : K₁ ⊆ b.source := by
    rintro t ⟨z, hz, rfl⟩
    exact b.map_target (hK₀T hz)
  obtain ⟨χ, hχ, hcχ, hχS, hχone⟩ :=
    show ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ b.source ∧ K₁ ⊆ interior {t | χ t = 1} from by
      obtain ⟨O, hO, hKO, hOS, hOc⟩ :=
        exists_open_between_and_isCompact_closure hK₁ b.open_source hK₁S
      obtain ⟨W, hW, hOW, hWS, hWc⟩ :=
        exists_open_between_and_isCompact_closure hOc b.open_source hOS
      obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
        (n := (⊤ : ℕ∞)) hW hOc.isClosed hOW
      have hts : tsupport χ = closure W := congrArg closure hsχ
      refine ⟨χ, hχ, by simpa only [HasCompactSupport, hts] using hWc,
        hts ▸ hWS, ?_⟩
      intro t ht
      apply mem_interior.mpr
      exact ⟨O, fun u hu ↦ (honeχ u).mp (subset_closure hu), hO, hKO ht⟩
  have hbsm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, X) ∞ b := by
    have hexp := contMDiff_circleExp.comp
      (show ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ 2 * Real.pi * t) from
        (contDiff_const.mul contDiff_id).contMDiff)
    exact hexp.congr hb
  have hφb : ContDiff ℝ ∞ (fun t : ℝ ↦ φ (b t)) :=
    contMDiff_iff_contDiff.mp (hφ.comp hbsm)
  have hψb : ContDiff ℝ ∞ (fun t : ℝ ↦ ψ (b t)) :=
    contMDiff_iff_contDiff.mp (hψ.comp hbsm)
  let φa : 𝓢(ℝ, ℂ) := (hcχ.smul_right (f' := fun t ↦ φ (b t))).toSchwartzMap
    (hχ.smul hφb)
  let ψa : 𝓢(ℝ, ℂ) := (hcχ.smul_right (f' := fun t ↦ ψ (b t))).toSchwartzMap
    (hχ.smul hψb)
  have hφa (t : ℝ) : φa t = (χ t : ℂ) * φ (b t) := rfl
  have hψa (t : ℝ) : ψa t = (χ t : ℂ) * ψ (b t) := rfl
  have hφas : tsupport φa ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport χ)
    intro t ht
    by_contra h
    exact ht (by rw [hφa, image_eq_zero_of_notMem_tsupport h]; simp)
  have hψas : tsupport ψa ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport χ)
    intro t ht
    by_contra h
    exact ht (by rw [hψa, image_eq_zero_of_notMem_tsupport h]; simp)
  have hcψa : HasCompactSupport (ψa : ℝ → ℂ) :=
    hcχ.of_isClosed_subset (isClosed_tsupport ψa) hψas
  have hsep (t : ℝ) (k : ℤ) (hk : k ≠ 0) : ψa t * φa (t + (k : ℝ)) = 0 := by
    by_cases ht : t ∈ tsupport χ
    · by_cases htk : t + (k : ℝ) ∈ tsupport χ
      · have htI := hbS ▸ hχS ht
        have htkI := hbS ▸ hχS htk
        have hkl : (-1 : ℝ) < (k : ℝ) := by linarith [htI.2, htkI.1]
        have hku : (k : ℝ) < 1 := by linarith [htI.1, htkI.2]
        have : (-1 : ℤ) < k ∧ k < 1 := by exact_mod_cast And.intro hkl hku
        omega
      · rw [hφa, image_eq_zero_of_notMem_tsupport htk]
        simp
    · rw [hψa, image_eq_zero_of_notMem_tsupport ht]
      simp
  let p := periodicProjectionMatrixSymbol ψa φa
  have hp : IsSymbol univ 0 p := (periodicProjectionMatrixSymbol_properties ψa φa hcψa hsep).1
  have hcp : HasCompactSupport p := hasCompactSupport_periodicProjectionMatrixSymbol ψa φa hcψa
  let Q : 𝓢(X, Y) →L[ℂ] 𝓢(X, Y) := quantizeSchwartz 0 p hp hcp
  have hQ (u : 𝓢(X, Y)) (x : X) : Q u x = quantize p u x :=
    quantizeSchwartz_apply 0 p hp hcp u x
  let K : Set X := l.symm '' tsupport χ
  have hK : IsCompact K := hcχ.image l.symm.continuous
  have hKS : K ⊆ e.source := by
    rintro x ⟨t, ht, rfl⟩
    rw [heS]
    simpa only [mem_preimage, l.apply_symm_apply] using (hbS ▸ hχS ht)
  have hsub : l ⁻¹' (tsupport ψa ∪ tsupport φa) ⊆ K := by
    intro x hx
    exact ⟨l x, hx.elim (fun h ↦ hψas h) (fun h ↦ hφas h), l.symm_apply_apply x⟩
  have hQK : HasOperatorSupport K Q := by
    have hh := hasOperatorSupport_periodicProjectionQuantization ψa φa Q hQ
    exact ⟨fun u ↦ (hh.1 u).trans hsub, fun u hu ↦ hh.2 u (hu.mono_right hsub)⟩
  -- The original coordinate-change theorem supplies an exact native left symbol.
  obtain ⟨χ₂, hχ₂, hcχ₂, hχ₂S, hχ₂one⟩ :=
    exists_compact_cutoff_one_near K e.source hK e.open_source hKS
  have heK : IsCompact (e '' K) := hK.image_of_continuousOn (he.continuousOn.mono hKS)
  have heKT : e '' K ⊆ e.target := image_subset_iff.mpr (fun _ hx ↦ e.map_source (hKS hx))
  obtain ⟨ρ, hρ, hcρ, hρT, hρone⟩ :=
    exists_compact_cutoff_one_near (e '' K) e.target heK e.open_target heKT
  let R : 𝓢(X, Y) →L[ℂ] 𝓢(X, Y) :=
    coordinatePushforward e he hei.contDiffOn χ₂ ρ hχ₂ hcχ₂ hχ₂S hρ hcρ hρT Q
  obtain ⟨q, hq, hRq, hprincipal⟩ := exists_symbol_coordinatePushforward e he hei.contDiffOn χ₂ ρ
    hχ₂ hcχ₂ hχ₂S hρ hcρ hρT 0 p hp Q hQ K hK hKS hQK hχ₂one hρone
  let A : BundleChartCutoff (r := 1) FourierCircleLine c := {
    frame := Bundle.Trivial.trivialization Circle Y
    frame_mem_atlas := ⟨rfl⟩
    cutoff := ρ
    smooth_cutoff := hρ
    compact_support := hcρ
    support_subset := by simp only [hcT, Bundle.Trivial.trivialization_baseSet,
      preimage_univ, univ_inter, subset_univ] }
  let L : PseudodifferentialPiece (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine 0 := {
    chart := c
    chart_mem_atlas := hc
    input := A
    output := A
    input_support_in_output_frame := by simp [A]
    output_support_in_input_frame := by simp [A]
    operator := R
    symbol := q
    isSymbol := hq
    operator_apply := hRq }
  have heapp (t : ℝ) : e (l.symm t) = c (b t) := by
    simp only [e, OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph,
      l.apply_symm_apply]
  have heSin (t : ℝ) (ht : t ∈ b.source) : l.symm t ∈ e.source := by
    rw [heS]
    simpa only [mem_preimage, l.apply_symm_apply, hbS] using ht
  have hweights (t : ℝ) (ht : t ∈ b.source) (hz : b t ∈ K₀) :
      χ t = 1 ∧ χ₂ (l.symm t) = 1 ∧ ρ (c (b t)) = 1 := by
    have htK₁ : t ∈ K₁ := ⟨b t, hz, b.left_inv ht⟩
    have hχt : χ t = 1 := show t ∈ {x | χ x = 1} from interior_subset (hχone htK₁)
    have htχ : t ∈ tsupport χ := subset_closure (by simp [Function.mem_support, hχt])
    have htK : l.symm t ∈ K := ⟨t, htχ, rfl⟩
    refine ⟨hχt, (show l.symm t ∈ {x | χ₂ x = 1} from
      interior_subset (hχ₂one htK)), ?_⟩
    exact show c (b t) ∈ {x | ρ x = 1} from
      interior_subset (hρone ⟨l.symm t, htK, heapp t⟩)
  have hlocalize (u : smoothSections (n := 1) (r := 1) FourierCircleLine) (y : X) :
      A.localize hc u y = (ρ y : ℂ) • u.val (c.symm y) := by
    change A.localizedFunction u y = _
    simp only [BundleChartCutoff.localizedFunction, hcT, mem_univ, ite_true,
      sectionInChart, A]
    rfl
  have hframe (z : Circle) (w : Y) :
      (Bundle.Trivial.trivialization Circle Y).symmL ℂ z w = w := by
    rw [Bundle.Trivial.symmL_trivialization]
    rfl
  have hL : L.toLinearMap = (smoothSectionMul FourierCircleLine ψ hψ).comp
      (P.comp (smoothSectionMul FourierCircleLine φ hφ)) := by
    apply LinearMap.ext
    intro u
    let u₀ := smoothSectionMul FourierCircleLine φ hφ u
    let U : 𝓢(X, Y) := cutoffPullbackCLM e.source e.open_source e he χ₂ hχ₂ hcχ₂ hχ₂S
      (A.localize hc u)
    let v : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM
      s.toContinuousLinearEquiv.toContinuousLinearMap
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ l.symm.toContinuousLinearEquiv U)
    let f : 𝓢(ℝ, ℂ) := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φa v
    have hv (t : ℝ) : v t = (χ₂ (l.symm t) : ℂ) *
        ((ρ (e (l.symm t)) : ℂ) * u.val (c.symm (e (l.symm t))) 0) := by
      change s (U (l.symm t)) = _
      dsimp only [U]
      rw [cutoffPullbackCLM_apply, hlocalize, hs, PiLp.smul_apply, PiLp.smul_apply]
      rfl
    have hf (t : ℝ) : f t = φa t * v t := rfl
    have hfS : tsupport f ⊆ b.source := by
      apply (closure_minimal _ (isClosed_tsupport φa)).trans (hφas.trans hχS)
      intro t ht
      by_contra htφ
      exact ht (by rw [hf, image_eq_zero_of_notMem_tsupport htφ, zero_mul])
    have hfeq (t : ℝ) (ht : t ∈ b.source) : f t = u₀.val (b t) 0 := by
      have hz : b t ∈ c.source := hbT ▸ b.map_source ht
      rw [hf, hφa, hv, heapp, c.left_inv hz]
      change (χ t : ℂ) * φ (b t) *
        ((χ₂ (l.symm t) : ℂ) * ((ρ (c (b t)) : ℂ) * u.val (b t) 0)) =
          φ (b t) * u.val (b t) 0
      by_cases hφz : φ (b t) = 0
      · simp only [hφz, mul_zero, zero_mul]
      · have hw := hweights t ht (Or.inl (subset_closure hφz))
        simp only [hw.1, hw.2.1, hw.2.2, Complex.ofReal_one, one_mul]
    have hu₀zero (z : Circle) (hz : z ∉ b.target) : u₀.val z 0 = 0 := by
      have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz (hbT.symm ▸ hφc h))
      change φ z * u.val z 0 = 0
      rw [hφz, zero_mul]
    have hperiod : ∀ t : ℝ, u₀.val (Circle.exp (2 * Real.pi * t)) 0 =
        ∑' k : ℤ, f (t + (k : ℝ)) := by
      exact fun t ↦ circle_eq_tsum_of_tsupport_subset_exp_chart b hb f
        (fun z ↦ u₀.val z 0) hfS hfeq hu₀zero t
    have hseries (t : ℝ) : s (Q U (l.symm t)) = ψa t * (P u₀).val (b t) 0 := by
      rw [hQ]
      have h := quantize_periodicProjectionMatrixSymbol ψa φa U (l.symm t)
      change s (quantize p U (l.symm t)) = ψa (l (l.symm t)) *
        ∑' n : ℕ, (Real.fourierChar (l (l.symm t) * (n : ℝ)) : ℂ) * (𝓕 f) (n : ℝ) at h
      rw [l.apply_symm_apply] at h
      rw [h, ← circleFourierProjection_eq_tsum_of_periodization f u₀ (P u₀)
        hperiod (hP u₀) t, ← hb]
    apply Subtype.ext
    funext z
    apply s.injective
    rw [hs]
    change (L.toLinearMap u).val z 0 = ψ z * (P u₀).val z 0
    by_cases hz : z ∈ c.source
    · have hcz : c z ∈ e.target := heT.symm ▸ mem_univ _
      have hzt : b.symm z ∈ b.source := b.map_target (hbT.symm ▸ hz)
      have hecz : e.symm (c z) = l.symm (b.symm z) := by
        calc
          _ = e.symm (e (l.symm (b.symm z))) := by
            rw [heapp, b.right_inv (hbT.symm ▸ hz)]
          _ = _ := e.left_inv (heSin _ hzt)
      have hR : R (A.localize hc u) (c z) = Q U (l.symm (b.symm z)) := by
        dsimp only [R]
        rw [coordinatePushforward_apply e he hei.contDiffOn χ₂ ρ hχ₂ hcχ₂ hχ₂S
          hρ hcρ hρT Q K hKS hQK
          (fun y h ↦ (show y ∈ {x | ρ x = 1} from interior_subset (hρone h))) _ _ hcz, hecz]
      change (A.extendedFunction (R (A.localize hc u)) z) 0 = _
      simp only [BundleChartCutoff.extendedFunction, hz, ite_true, A,
        PiLp.smul_apply, smul_eq_mul]
      rw [hR, ← hs, hframe z (Q U (l.symm (b.symm z))), hseries, hψa,
        b.right_inv (hbT.symm ▸ hz)]
      by_cases hψz : ψ z = 0
      · simp only [hψz, mul_zero, zero_mul]
      · have hw := hweights (b.symm z) hzt
          (by rw [b.right_inv (hbT.symm ▸ hz)]; exact Or.inr (subset_closure hψz))
        have hρz : ρ (c z) = 1 := by simpa only [b.right_inv (hbT.symm ▸ hz)] using hw.2.2
        simp only [hw.1, hρz, Complex.ofReal_one, one_mul]
    · have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hψc h))
      change (A.extendedFunction (R (A.localize hc u)) z) 0 = _
      simp only [BundleChartCutoff.extendedFunction, hz, ite_false, PiLp.zero_apply,
        hψz, zero_mul]
  refine ⟨L, hL, ?_⟩
  intro T a₀ ha₀
  let := A.frame_mem_atlas
  let D := symbolChartDomain FourierCircleLine FourierCircleLine c A.frame A.frame
  have hD : D = univ := by
    simp [D, symbolChartDomain, A, hcT]
  let J := globalSymbolInChart FourierCircleLine FourierCircleLine
    (T.regularizedSymbolFunction a₀.val) c A.frame A.frame
  let aNative := globalSymbolInChart FourierCircleLine FourierCircleLine
    a₀.val c A.frame A.frame
  have hJ : IsSymbol univ 0 J := by
    simpa only [← hD] using
      T.isGlobalSymbol_regularizedSymbolFunction 0 a₀.val a₀.property.1 a₀.property.2
        c hc A.frame A.frame
  let p₀ := frequencyCutoffSymbol (periodicProjectionPrincipalData ψa φa)
  have hrem : IsSmoothingSymbol univ (p - p₀) :=
    (periodicProjectionMatrixSymbol_properties ψa φa hcψa hsep).2
  have hp₀ : IsSymbol univ 0 p₀ := by
    have h := hp.add isOpen_univ (IsSymbol.smul isOpen_univ (-1) (hrem 0))
    have heq : p + (-1 : ℂ) • (p - p₀) = p₀ := by
      rw [neg_one_smul]
      abel
    exact heq ▸ h
  have hpush : IsSymbol univ 0 (cotangentSymbol e p₀) := by
    simpa only [heT] using isSymbol_cotangentSymbol e he hei.contDiffOn 0 p₀
      (hp₀.restrict (subset_univ _))
  have herr : IsSymbol univ (-1) (q - cotangentSymbol e p₀) := by
    have hpr : IsSymbol univ (-1) (q - cotangentSymbol e p) := by
      simpa only [heT, zero_sub] using hprincipal
    have hr : IsSymbol univ (-1) (cotangentSymbol e (p - p₀)) := by
      simpa only [heT] using isSymbol_cotangentSymbol e he hei.contDiffOn (-1) (p - p₀)
        ((hrem (-1)).restrict (subset_univ _))
    convert hpr.add isOpen_univ hr using 1
    ext x ξ v
    simp only [Pi.add_apply, Pi.sub_apply, cotangentSymbol, add_apply,
      sub_apply]
    abel
  let weighted (d : SymbolFunction 1 1 1) : SymbolFunction 1 1 1 :=
    fun x ξ ↦ ((ρ x * ρ x : ℝ) : ℂ) • d x ξ
  have hweighted (m : ℝ) (d : SymbolFunction 1 1 1) (hd : IsSymbol univ m d) :
      IsSymbol univ m (weighted d) := by
    let C (x : X) : Y →L[ℂ] Y := (ρ x : ℂ) • ContinuousLinearMap.id ℂ Y
    have hC : ContDiffOn ℝ ∞ C univ :=
      (Complex.ofRealCLM.contDiff.comp hρ).contDiffOn.smul contDiffOn_const
    convert isSymbol_matrixSymbol univ isOpen_univ m d hd C C hC hC using 1
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    change ((ρ x * ρ x : ℝ) : ℂ) • (d x ξ) v =
      (ρ x : ℂ) • (d x ξ) ((ρ x : ℂ) • v)
    rw [map_smul, Complex.ofReal_mul, mul_smul]
  have hlead (x ξ : X) :
      weighted (cotangentSymbol e (periodicProjectionPrincipalData ψa φa)) x ξ =
        aNative x ξ := by
    let t := l (e.symm x)
    have ht : t ∈ b.source := by
      have h := e.map_target (heT.symm ▸ mem_univ x)
      rw [heS] at h
      change t ∈ Ioo a (a + 1) at h
      rwa [hbS]
    have hcx : c (b t) = x := by
      rw [← heapp, show l.symm t = e.symm x from l.symm_apply_apply _]
      exact e.right_inv (heT.symm ▸ mem_univ _)
    have hbt : b t = c.symm x := by
      rw [← hcx, c.left_inv (hbT ▸ b.map_source ht)]
    have hsign : 0 < l ((fderiv ℝ e (e.symm x)).adjoint ξ) ↔
        0 < circleCovectorCoordinate (c.symm x) (covectorFromChart c (c.symm x) ξ) := by
      have hx : Circle.exp (2 * Real.pi * l (e.symm x)) ∈ c.source := by
        rw [← hb t]
        exact hbT ▸ b.map_source ht
      have h := circlePeriodOne_fderiv_adjoint c hc e heval (e.symm x) ξ hx
      change l ((fderiv ℝ e (e.symm x)).adjoint ξ) = (2 * Real.pi) *
        circleCovectorCoordinate (Circle.exp (2 * Real.pi * t))
          (covectorFromChart c (Circle.exp (2 * Real.pi * t)) ξ) at h
      rw [← hb t, hbt] at h
      rw [h, mul_pos_iff_of_pos_left (mul_pos (by norm_num) Real.pi_pos)]
    have hnative : aNative x ξ = a₀.val (c.symm x)
        (covectorFromChart c (c.symm x) ξ) := by
      dsimp only [aNative, globalSymbolInChart, A]
      rw [Bundle.Trivial.continuousLinearMapAt_trivialization,
        Bundle.Trivial.symmL_trivialization]
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [hnative, ha₀]
    change ((ρ x * ρ x : ℝ) : ℂ) •
      (if 0 < l ((fderiv ℝ e (e.symm x)).adjoint ξ) then
        (ψa t * φa t) • ContinuousLinearMap.id ℂ Y else 0) = _
    simp only [hsign]
    by_cases hpos : 0 < circleCovectorCoordinate (c.symm x)
        (covectorFromChart c (c.symm x) ξ)
    · simp only [hpos, ite_true]
      rw [hψa, hφa, hbt]
      by_cases hφzero : φ (c.symm x) = 0
      · simp only [hφzero, mul_zero, zero_smul, smul_zero]
      · have hw := hweights t ht (by rw [hbt]; exact Or.inl (subset_closure hφzero))
        rw [hcx] at hw
        simp only [hw.1, hw.2.2, mul_one, Complex.ofReal_one, one_mul, one_smul]
        apply ContinuousLinearMap.ext
        intro v
        rfl
    · simp only [hpos, ite_false, smul_zero]
  -- The inverse native derivative uniformly controls the angular frequency on compact sets.
  have hinverse (x : X) :
      (fderiv ℝ e.symm x).adjoint.comp (fderiv ℝ e (e.symm x)).adjoint =
        ContinuousLinearMap.id ℝ X := by
    have hx : x ∈ e.target := heT.symm ▸ mem_univ _
    have hf := (he.contDiffAt (e.open_source.mem_nhds (e.map_target hx))).differentiableAt
      (by simp)
    have hi := hei.differentiable (by simp) x
    have hcomp : (fderiv ℝ e (e.symm x)).comp (fderiv ℝ e.symm x) =
        ContinuousLinearMap.id ℝ X := by
      apply (hf.hasFDerivAt.comp x hi.hasFDerivAt).unique
      apply (hasFDerivAt_id x).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hx] with y hy
      exact e.right_inv hy
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg ContinuousLinearMap.adjoint hcomp
  let δ := weighted (cotangentSymbol e p₀) - J
  have hδ : IsSymbol univ (-1) δ := by
    apply IsSymbol.of_locally isOpen_univ
    intro x _
    obtain ⟨C, hC, hxC, hCU⟩ := exists_compact_subset (isOpen_univ : IsOpen (univ : Set X))
      (mem_univ x)
    have hdinv : Continuous (fun y : X ↦ fderiv ℝ e.symm y) :=
      (hei.fderiv_right (m := ∞) (by simp)).continuous
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hdinv.continuousOn
    obtain ⟨R₀, _hR₀, hrecover⟩ :=
      T.regularizedSymbolFunction_eq_inChart_at_high_frequency a₀.val c hc A.frame A.frame
        C hC (by rw [show symbolChartDomain FourierCircleLine FourierCircleLine
          c A.frame A.frame = univ from hD]; exact subset_univ _)
    refine ⟨interior C, isOpen_interior, hxC, subset_univ _, ?_⟩
    apply isSmoothingSymbol_of_frequency_support isOpen_interior δ (max R₀ (max B 1))
      (((hweighted 0 _ hpush).1.sub hJ.1).mono (prod_mono (subset_univ _) subset_rfl))
    intro y hy ξ hξ
    have hnorm : 1 ≤ ‖(fderiv ℝ e (e.symm y)).adjoint ξ‖ := by
      have hbound : ‖ξ‖ ≤ max B 1 * ‖(fderiv ℝ e (e.symm y)).adjoint ξ‖ := by
        have h := (fderiv ℝ e.symm y).adjoint.le_opNorm
          ((fderiv ℝ e (e.symm y)).adjoint ξ)
        have hinv := congrArg (fun Q : X →L[ℝ] X ↦ Q ξ) (hinverse y)
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hinv
        rw [hinv, ContinuousLinearMap.adjoint.norm_map] at h
        exact h.trans (mul_le_mul_of_nonneg_right
          ((hB y (interior_subset hy)).trans (le_max_left _ _)) (norm_nonneg _))
      have hfreq : max B 1 ≤ ‖ξ‖ := (le_max_right _ _).trans hξ
      have hpos : 0 < max B 1 := zero_lt_one.trans_le (le_max_right _ _)
      nlinarith
    have hfreq := hrecover y (interior_subset hy) ξ ((le_max_left _ _).trans hξ)
    change J y ξ = aNative y ξ at hfreq
    dsimp only [δ, Pi.sub_apply]
    rw [hfreq, ← hlead y ξ]
    dsimp only [weighted, cotangentSymbol, p₀]
    rw [frequencyCutoffSymbol_eq_of_one_le_norm _ _ _ hnorm]
    exact sub_self _
  have hnative : IsSymbol D (-1)
      (globalSymbolInChart FourierCircleLine FourierCircleLine
        (L.globalSymbolFunction - T.regularizedSymbolFunction a₀.val) c A.frame A.frame) := by
    have h := (hweighted (-1) _ herr).add isOpen_univ hδ
    apply (h.restrict (subset_univ D)).congr_on (hD ▸ isOpen_univ)
    intro x hx
    funext ξ
    have hLcoord := L.globalSymbolInChart_globalSymbolFunction x ξ hx
    have hsub : globalSymbolInChart FourierCircleLine FourierCircleLine
        (L.globalSymbolFunction - T.regularizedSymbolFunction a₀.val) c A.frame A.frame x ξ =
        globalSymbolInChart FourierCircleLine FourierCircleLine L.globalSymbolFunction
          c A.frame A.frame x ξ - J x ξ := by
      ext v
      simp [globalSymbolInChart, J]
    rw [hsub, hLcoord]
    change weighted (q - cotangentSymbol e p₀) x ξ + δ x ξ =
      ((ρ x * ρ x : ℝ) : ℂ) • q x ξ - J x ξ
    dsimp only [weighted, δ, Pi.add_apply, Pi.sub_apply]
    rw [smul_sub]
    abel
  -- Both representatives have compact base support in the same native chart.
  let C := c.symm '' tsupport ρ ∪ K₀
  have hC : IsCompact C :=
    (hcρ.image_of_continuousOn (c.continuousOn_symm.mono
      (by rw [hcT]; exact subset_univ _))).union hK₀
  have hCD : C ⊆ c.source ∩ A.frame.baseSet ∩ A.frame.baseSet := by
    intro z hz
    have hzc : z ∈ c.source := by
      rcases hz with ⟨x, _, rfl⟩ | hz
      · exact c.map_target (hcT.symm ▸ mem_univ _)
      · exact hz.elim (fun h ↦ hφc h) (fun h ↦ hψc h)
    simpa only [A, Bundle.Trivial.trivialization_baseSet, inter_univ] using hzc
  apply isGlobalSymbol_of_compactSupportInChart (-1)
    (L.globalSymbolFunction - T.regularizedSymbolFunction a₀.val)
    c hc A.frame A.frame C hC hCD ?_ hnative
  intro z hz ξ
  have hLzero : L.globalSymbolFunction z ξ = 0 :=
    L.globalSymbolFunction_eq_zero z
      (fun h ↦ hz (Or.inl ((image_mono inter_subset_right) h))) ξ
  have hφzero : φ z = 0 := image_eq_zero_of_notMem_tsupport
    (fun h ↦ hz (Or.inr (Or.inl h)))
  simp only [Pi.sub_apply, hLzero, QuantizationPresentation.regularizedSymbolFunction,
    ha₀, hφzero, mul_zero, zero_smul, smul_zero, Finset.sum_const_zero, sub_zero]


/-- The original nonnegative Fourier projection has a native local PDO representation. -/
theorem isPseudodifferentialOperator_circleLocalizedProjection
    (P : smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ]
      smoothSections (n := 1) (r := 1) FourierCircleLine)
    (hP : ∀ u, circleSmoothToFourierL2 (P u) =
      circleNonnegativeFourierProjection (circleSmoothToFourierL2 u))
    (c : OpenPartialHomeomorph Circle (EuclideanSpace ℝ (Fin 1)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle)
    (φ ψ : Circle → ℂ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞ ψ)
    (hφc : tsupport φ ⊆ c.source) (hψc : tsupport ψ ⊆ c.source) :
    IsPseudodifferentialOperator (n := 1) (r := 1) (q := 1)
      FourierCircleLine FourierCircleLine fourierCircleMeasure 0
      ((smoothSectionMul FourierCircleLine ψ hψ).comp
        (P.comp (smoothSectionMul FourierCircleLine φ hφ))) := by
  obtain ⟨L, hL, _⟩ := exists_circleLocalizedProjection_piece P hP c hc φ ψ hφ hψ hφc hψc
  rw [← hL]
  exact L.isPseudodifferentialOperator 0

end AtiyahSinger

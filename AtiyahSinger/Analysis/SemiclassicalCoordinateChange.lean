/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.SemiclassicalGlobalQuantization

import all AtiyahSinger.Analysis.CoordinateChange
import all AtiyahSinger.Analysis.EquivariantLocalizedRemainder
import all AtiyahSinger.Analysis.SemiclassicalComposition

/-!
# The original raw coordinate change at a positive frequency scale

Public module ID: M2307.

Sources: SG III.3.12–3.14 and the quantitative amplitude estimates in M2293
and M2295. SG means H. Blaine Lawson, Jr. and Marie-Louise Michelsohn,
*Spin Geometry* (Princeton University Press, 1989). The exact coordinate
substitution and its absolute Jacobians are those of M0402 CoordinateChange;
the actual multiplier identity is reused from M0537.

The source and target cutoffs are arbitrary fixed smooth compact functions
inside the two coordinate domains. Internal plateaus split the original
localized operator into a near-diagonal amplitude and a retained transported
zero-diagonal amplitude. The near amplitude has the cut-off cotangent symbol
as its actual diagonal. Both actual errors have one Sobolev bound proportional
to the positive contraction parameter, with the constant chosen beforehand.

The estimate applies to the original Fourier quantizers and every real
Sobolev coordinate exponent. Its local input does not include an operator
support certificate or a norm limit at parameter zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set MeasureTheory
open scoped ContDiff SchwartzMap Topology

variable {n r q : ℕ}

set_option maxSynthPendingDepth 15

/-- The fixed cut-off cotangent symbol has its standard global symbol and support properties. -/
private theorem raw_coordinate_leading_symbol_properties
    (p : SymbolFunction n r q) (hp : IsSymbol univ 0 p)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target) :
    IsSymbol univ 0 (zeroExtendedSymbol e.target ρ
      (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e p x ξ)) ∧
    HasCompactSupport (zeroExtendedSymbol e.target ρ
      (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e p x ξ)) := by
  /- Zero-extend the target-local cotangent symbol with the original output
  cutoff. A compact smooth extension of the pulled-back input cutoff is then
  a second multiplier on this same symbol. Its pointwise identity removes all
  dependence on that extension from the displayed leading symbol. -/
  classical
  obtain ⟨σ, hσ, hcσ, hσV, hσspec, _hσsupp⟩ :=
    exists_compactSmooth_coordinatePullback e.symm hψ χ hχ hcχ hχU
  let d₀ := zeroExtendedSymbol e.target ρ (cotangentSymbol e p)
  have hd₀ : IsSymbol univ 0 d₀ :=
    isSymbol_zeroExtendedSymbol e.target e.open_target 0 ρ hρ hcρ hρV
      (cotangentSymbol e p) (isSymbol_cotangentSymbol e he hψ 0 p
        (hp.restrict (subset_univ _)))
  have hsame : zeroExtendedSymbol univ σ d₀ = zeroExtendedSymbol e.target ρ
      (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e p x ξ) := by
    funext x ξ
    by_cases hx : x ∈ e.target
    · simp only [zeroExtendedSymbol, mem_univ, ↓reduceIte, d₀, ite_eq_left hx,
        hσspec x hx, smul_smul, mul_comm]
    · simp only [zeroExtendedSymbol, mem_univ, ↓reduceIte, d₀, ite_eq_right hx,
        smul_zero]
  refine ⟨?_, hasCompactSupport_zeroExtendedSymbol e.target ρ _ hcρ⟩
  have h := isSymbol_zeroExtendedSymbol univ isOpen_univ 0 σ hσ hcσ
    (hσV.trans (subset_univ _)) d₀ hd₀
  rwa [hsame] at h

set_option maxHeartbeats 1500000 in
-- The two fixed amplitudes retain the exact raw operator and its complete transported tail.
/-- Arbitrary original cutoffs admit one fixed near amplitude and one zero-diagonal source tail. -/
private theorem exists_raw_coordinate_frequencyScale_amplitudes
    (p : SymbolFunction n r q) (hp : IsSymbol univ 0 p)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target) :
    ∃ a R : AmplitudeFunction n r q,
      ∃ ha : IsAmplitude 0 a, ∃ hca : HasCompactSupport (Function.uncurry a),
      ∃ hR : IsAmplitude 0 R, ∃ hcR : HasCompactSupport (Function.uncurry R),
        (∀ x ξ, R x x ξ = 0) ∧
        (∀ x ξ, a x x ξ = zeroExtendedSymbol e.target ρ
          (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e p x ξ) x ξ) ∧
        (∀ h : ℝ, ∀ hh : 0 < h, ∀ hh₁ : h ≤ 1,
          ∀ P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
            𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
          (∀ u x, P u x = quantize (frequencyScaleSymbol h p) u x) →
          ∀ u, coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u =
            amplitudeOperator 0 (frequencyScaleAmplitude h a)
              (ha.frequencyScale h hh hh₁) (hasCompactSupport_frequencyScaleAmplitude h hca) u +
            coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV
              (amplitudeOperator 0 (frequencyScaleAmplitude h R)
                (hR.frequencyScale h hh hh₁) (hasCompactSupport_frequencyScaleAmplitude h hcR))
              u) := by
  /- First insert a plateau only around the actual input and pulled-back output
  supports. Split that localized source amplitude using the original coordinate
  neighborhood. Transport the near part by the actual spatial and frequency
  substitutions, folding in both external cutoffs. Keep the whole source tail
  under the same original coordinate pushforward. All choices precede h. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let K : Set X := e.symm '' tsupport ρ ∪ tsupport χ
  have hK : IsCompact K :=
    (hcρ.image_of_continuousOn (e.continuousOn_symm.mono hρV)).union hcχ
  have hKU : K ⊆ e.source := by
    rintro x (⟨y, hy, rfl⟩ | hx)
    · exact e.map_target (hρV hy)
    · exact hχU hx
  have heK : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have heKV : e '' K ⊆ e.target := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_source (hKU hy)
  obtain ⟨κ, hκ, hcκ, hκV, hκone⟩ :=
    exists_compact_cutoff_one_near (e '' K) e.target heK e.open_target heKV
  obtain ⟨W, β, γ, γ₀, hW, hseg, hinv, hβ, hcβ, hβU, hβone, _hβspec,
    hγ, hcγ, hγW, hγ₀, hcγ₀, hγ₀supp, hγ₀spec, hγnear, hoff⟩ :=
    exists_coordinate_decomposition_cutoffs e he hψ K hKU κ hκ hcκ hκV hκone
  have hKβ : K ⊆ tsupport β := by
    intro x hx
    have hβx : β x = 1 := interior_subset (s := {y | β y = 1}) (hβone hx)
    exact subset_tsupport _ (show β x ≠ 0 by rw [hβx]; norm_num)
  obtain ⟨δ, hδ, hcδ, hδU, hδone⟩ :=
    exists_compact_cutoff_one_near (tsupport β) e.source hcβ e.open_source hβU
  have hδγ : Prod.snd '' tsupport γ₀ ⊆ {x | δ x = 1} := by
    rintro x ⟨z, hz, rfl⟩
    exact interior_subset (hδone (hγ₀supp hz).2)
  obtain ⟨σ, hσ, hcσ, _hσV, hσspec, _hσsupp⟩ :=
    exists_compactSmooth_coordinatePullback e.symm hψ χ hχ hcχ hχU
  let Cin : X → EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
    fun y ↦ (σ y : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))
  let Cout : X → EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
    fun x ↦ (ρ x : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q))
  have hCin : ContDiff ℝ ∞ Cin :=
    (Complex.ofRealCLM.contDiff.comp hσ).smul contDiff_const
  have hcCin : HasCompactSupport Cin :=
    hcσ.comp_left (g := fun c : ℝ ↦
      (c : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))) (by simp)
  let Mσ := matrixMultiplierCLM Cin hCin hcCin
  let Lχ := cutoffPullbackCLM (r := r) e.source e.open_source e he χ hχ hcχ hχU
  let Sδ := cutoffPullbackCLM (r := r) e.source e.open_source e he δ hδ hcδ hδU
  have hMσ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (y : X) :
      Mσ u y = σ y • u y := by
    rw [matrixMultiplierCLM_apply]
    simp only [Cin, smul_apply, ContinuousLinearMap.id_apply]
    exact algebraMap_smul ℂ (σ y) (u y)
  have hβχ (x : X) : β x * χ x = χ x := by
    by_cases hx : χ x = 0
    · rw [hx, mul_zero]
    · have hxK : x ∈ K := Or.inr (subset_tsupport _ hx)
      rw [show β x = 1 from interior_subset (s := {y | β y = 1}) (hβone hxK), one_mul]
  have hδχ (x : X) : δ x * χ x = χ x := by
    by_cases hx : χ x = 0
    · rw [hx, mul_zero]
    · have hxK : x ∈ K := Or.inr (subset_tsupport _ hx)
      rw [show δ x = 1 from interior_subset (s := {y | δ y = 1}) (hδone (hKβ hxK)),
        one_mul]
  have hinput (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) : Sδ (Mσ u) = Lχ u := by
    apply SchwartzMap.ext
    intro x
    simp only [Sδ, Lχ, cutoffPullbackCLM_apply, hMσ]
    by_cases hx : x ∈ e.source
    · rw [hσspec (e x) (e.map_source hx), e.left_inv hx, smul_smul, hδχ]
    · have hδx : δ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hδU h))
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hχU h))
      rw [hδx, hχx, zero_smul, zero_smul]
  have hρβ (x : X) : ρ x * β (e.symm x) = ρ x := by
    by_cases hx : ρ x = 0
    · rw [hx, zero_mul]
    · have hxK : e.symm x ∈ K := Or.inl ⟨x, subset_tsupport _ hx, rfl⟩
      rw [show β (e.symm x) = 1 from
        interior_subset (s := {y | β y = 1}) (hβone hxK), mul_one]
  let Mβ := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (β y : ℂ))
  have hβgrowth : (fun y ↦ (β y : ℂ)).HasTemperateGrowth :=
    (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hβ)
  have hMβ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) : Mβ (Lχ u) = Lχ u := by
    apply SchwartzMap.ext
    intro x
    rw [SchwartzMap.smulLeftCLM_apply_apply hβgrowth]
    simp only [Lχ, cutoffPullbackCLM_apply]
    rw [Complex.coe_smul, smul_smul, hβχ]
  -- The fixed source tail vanishes on the whole diagonal, including outside the source domain.
  let A := localizedAmplitude γ₀ p
  let tailCutoff : X × X → ℝ := fun z ↦ β z.1 * β z.2 - γ₀ z
  let R := localizedAmplitude tailCutoff p
  let T := cutoffAmplitude β β p
  have hTailCutoff : ContDiff ℝ ∞ tailCutoff :=
    ((hβ.comp contDiff_fst).mul (hβ.comp contDiff_snd)).sub hγ₀
  have hTailCutoffSupport : tsupport tailCutoff ⊆ tsupport β ×ˢ tsupport β := by
    apply closure_minimal ?_ ((isClosed_tsupport β).prod (isClosed_tsupport β))
    intro z hz
    by_contra hout
    have hγ₀z : γ₀ z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hout (hγ₀supp h))
    rcases not_and_or.mp hout with hx | hy
    · exact hz (by simp [tailCutoff, image_eq_zero_of_notMem_tsupport hx, hγ₀z])
    · exact hz (by simp [tailCutoff, image_eq_zero_of_notMem_tsupport hy, hγ₀z])
  have hcTailCutoff : HasCompactSupport tailCutoff :=
    (hcβ.prod hcβ).of_isClosed_subset (isClosed_tsupport _) hTailCutoffSupport
  have hsupp (ν : X × X → ℝ) :
      tsupport (Function.uncurry (localizedAmplitude ν p)) ⊆ tsupport ν := by
    apply closure_minimal ?_ (isClosed_tsupport ν)
    intro z hz
    by_contra hout
    apply hz
    funext ξ
    simp only [Function.uncurry, localizedAmplitude, Prod.eta,
      image_eq_zero_of_notMem_tsupport hout, zero_smul, Pi.zero_apply]
  have hA : IsAmplitude 0 A := isAmplitude_localizedAmplitude 0 p hp γ₀ hγ₀
  have hcA : HasCompactSupport (Function.uncurry A) :=
    hcγ₀.of_isClosed_subset (isClosed_tsupport _) (hsupp γ₀)
  have hR : IsAmplitude 0 R := isAmplitude_localizedAmplitude 0 p hp tailCutoff hTailCutoff
  have hcR : HasCompactSupport (Function.uncurry R) :=
    hcTailCutoff.of_isClosed_subset (isClosed_tsupport _) (hsupp tailCutoff)
  have hRdiag (x ξ : X) : R x x ξ = 0 := by
    have hTailCutoffDiag : tailCutoff (x, x) = 0 := (hoff x).eq_of_nhds
    simp only [R, localizedAmplitude, hTailCutoffDiag, zero_smul]
  -- Fold the original output cutoff and the genuine pulled-back input cutoff into the near part.
  let η : X × X → ℝ := fun z ↦ ρ z.1 * σ z.2 * γ z
  have hη : ContDiff ℝ ∞ η :=
    ((hρ.comp contDiff_fst).mul (hσ.comp contDiff_snd)).mul hγ
  have hηsupp : tsupport η ⊆ tsupport γ := by
    apply closure_minimal ?_ (isClosed_tsupport γ)
    intro z hz
    exact subset_tsupport _ (right_ne_zero_of_mul hz)
  have hcη : HasCompactSupport η :=
    hcγ.of_isClosed_subset (isClosed_tsupport _) hηsupp
  have hηW : tsupport η ⊆ W := hηsupp.trans hγW
  let a := coordinateAmplitude e η p
  have ha : IsAmplitude 0 a := isAmplitude_coordinateAmplitude e he hψ 0 p
    (hp.restrict (subset_univ _)) W hW hseg hinv η hη hcη hηW
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_coordinateAmplitude e η p hcη
  have hadiag (x ξ : X) : a x x ξ = zeroExtendedSymbol e.target ρ
      (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e p x ξ) x ξ := by
    by_cases hx : x ∈ e.target
    · have hηdiag : η (x, x) = ρ x * χ (e.symm x) := by
        by_cases hρx : ρ x = 0
        · simp only [η, hρx, zero_mul]
        · have hxK : x ∈ e '' K :=
            ⟨e.symm x, Or.inl ⟨x, subset_tsupport _ hρx, rfl⟩, e.right_inv hx⟩
          have hγx : γ (x, x) = 1 := (hγnear x hxK).eq_of_nhds
          simp only [η, hγx, mul_one, hσspec x hx]
      change coordinateAmplitude e η p x x ξ = _
      rw [coordinateAmplitude_diag e he hψ η p x ξ hx]
      simp only [zeroExtendedSymbol, ite_eq_left hx, hηdiag, ← Complex.coe_smul,
        smul_smul, Complex.ofReal_mul]
    · have hρx : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρV h))
      simp only [a, coordinateAmplitude, η, hρx, zero_mul, zero_smul,
        zeroExtendedSymbol, ite_eq_right hx]
  have hscale (ν : X × X → ℝ) (h : ℝ) :
      coordinateAmplitude e ν (frequencyScaleSymbol h p) =
        frequencyScaleAmplitude h (coordinateAmplitude e ν p) := by
    funext x y ξ
    change (ν (x, y) * coordinateJacobianFactor e x y) •
        p (e.symm x) (h • coordinateFrequencyChange e x y ξ) =
      (ν (x, y) * coordinateJacobianFactor e x y) •
        p (e.symm x) (coordinateFrequencyChange e x y (h • ξ))
    rw [(coordinateFrequencyChange e x y).map_smul h ξ]
  have hmatrix (b : SymbolFunction n r q) :
      (fun x y ξ ↦ (Cout x).comp ((coordinateAmplitude e γ b x y ξ).comp (Cin y))) =
        coordinateAmplitude e η b := by
    funext x y ξ
    apply ContinuousLinearMap.ext
    intro v
    simp only [Cout, Cin, coordinateAmplitude, ContinuousLinearMap.comp_apply,
      smul_apply, ContinuousLinearMap.id_apply, map_smul, ← Complex.coe_smul,
      smul_smul, η, Complex.ofReal_mul]
    congr 1
    ring
  refine ⟨a, R, ha, hca, hR, hcR, hRdiag, hadiag, ?_⟩
  intro h hh hh₁ P hP u
  let ph := frequencyScaleSymbol h p
  have hph : IsSymbol univ 0 ph := hp.frequencyScale h hh hh₁
  have hAh : IsAmplitude 0 (frequencyScaleAmplitude h A) := hA.frequencyScale h hh hh₁
  have hcAh := hasCompactSupport_frequencyScaleAmplitude h hcA
  have hRh : IsAmplitude 0 (frequencyScaleAmplitude h R) := hR.frequencyScale h hh hh₁
  have hcRh := hasCompactSupport_frequencyScaleAmplitude h hcR
  have htotal (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      ρ x • amplitudeApply (frequencyScaleAmplitude h T) (Lχ v) (e.symm x) =
        ρ x • P (Lχ v) (e.symm x) := by
    rw [show frequencyScaleAmplitude h T = cutoffAmplitude β β ph from rfl,
      amplitudeApply_cutoffAmplitude 0 ph hph β β hβ hβ hcβ hcβ,
      hMβ, ← hP, smul_smul, hρβ]
  -- The split takes place inside the original integrable iterated amplitude integrals.
  have hsplit (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      amplitudeApply (frequencyScaleAmplitude h T) v x =
        amplitudeApply (frequencyScaleAmplitude h A) v x +
          amplitudeApply (frequencyScaleAmplitude h R) v x := by
    unfold amplitudeApply
    rw [← smul_add, ← integral_add
      (integrable_amplitudeApply_outer 0 _ hAh hcAh v x)
      (integrable_amplitudeApply_outer 0 _ hRh hcRh v x)]
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    rw [← integral_add (integrable_amplitudeApply_inner 0 _ hAh hcAh v x ξ)
      (integrable_amplitudeApply_inner 0 _ hRh hcRh v x ξ)]
    apply integral_congr_ae
    filter_upwards with y
    simp only [T, A, R, cutoffAmplitude, localizedAmplitude, frequencyScaleAmplitude, tailCutoff,
      smul_apply, sub_smul, sub_apply, smul_sub, add_sub_cancel]
  have hnear (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      ρ x • amplitudeApply (frequencyScaleAmplitude h A) (Lχ v) (e.symm x) =
        amplitudeApply (frequencyScaleAmplitude h a) v x := by
    by_cases hx : x ∈ e.target
    · have hid := amplitudeApply_coordinateAmplitude_eq e he hψ 0 ph hph
        W hW hseg hinv γ γ₀ hγ hcγ hγW hγ₀ hcγ₀
        (hγ₀supp.trans (prod_mono hβU hβU)) hγ₀spec δ hδ hcδ hδU hδγ (Mσ v) x hx
      have hγh : IsAmplitude 0 (coordinateAmplitude e γ ph) :=
        isAmplitude_coordinateAmplitude e he hψ 0 ph (hph.restrict (subset_univ _))
          W hW hseg hinv γ hγ hcγ hγW
      have hcγh := hasCompactSupport_coordinateAmplitude e γ ph hcγ
      have hfold := amplitudeApply_comp_multipliers 0 (coordinateAmplitude e γ ph)
        hγh hcγh Cout Cin hCin hcCin v x
      rw [hmatrix] at hfold
      change amplitudeApply (coordinateAmplitude e η ph) v x =
        (ρ x : ℂ) • amplitudeApply (coordinateAmplitude e γ ph) (Mσ v) x at hfold
      rw [Complex.coe_smul] at hfold
      have hsource : amplitudeApply (frequencyScaleAmplitude h A) (Lχ v) (e.symm x) =
          amplitudeApply (coordinateAmplitude e γ ph) (Mσ v) x := by
        change amplitudeApply (localizedAmplitude γ₀ ph) (Lχ v) (e.symm x) = _
        rw [← hinput v]
        exact hid
      rw [hsource, ← hfold, hscale]
    · have hρx : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρV h))
      simp only [zero_smul, amplitudeApply, frequencyScaleAmplitude, a,
        coordinateAmplitude, η, hρx, zero_mul, zero_smul, zero_apply, smul_zero,
        integral_zero]
  apply SchwartzMap.ext
  intro x
  calc
    _ = ρ x • P (Lχ u) (e.symm x) := by
      simp only [coordinatePushforward, ContinuousLinearMap.comp_apply, cutoffPullbackCLM_apply]
      rfl
    _ = ρ x • amplitudeApply (frequencyScaleAmplitude h T) (Lχ u) (e.symm x) :=
      (htotal u x).symm
    _ = ρ x • amplitudeApply (frequencyScaleAmplitude h A) (Lχ u) (e.symm x) +
        ρ x • amplitudeApply (frequencyScaleAmplitude h R) (Lχ u) (e.symm x) := by
      rw [hsplit, smul_add]
    _ = amplitudeApply (frequencyScaleAmplitude h a) u x +
        ρ x • amplitudeApply (frequencyScaleAmplitude h R) (Lχ u) (e.symm x) := by
      rw [hnear]
    _ = _ := by
      simp only [add_apply, amplitudeOperator_apply, coordinatePushforward,
        ContinuousLinearMap.comp_apply, cutoffPullbackCLM_apply]
      rfl

set_option maxHeartbeats 1500000 in
-- The same cut-off cotangent symbol and both actual errors are used in every scale.
/-- The original raw coordinate pushforward has a uniform first-order Sobolev error. -/
theorem exists_frequencyScale_raw_coordinatePushforward_sobolev_bound
    (p : SymbolFunction n r q) (hp : IsSymbol univ 0 p)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ P B : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      (∀ u x, P u x = quantize (frequencyScaleSymbol h p) u x) →
      (∀ u x, B u x = quantize (frequencyScaleSymbol h
        (zeroExtendedSymbol e.target ρ
          (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e p x ξ))) u x) →
      ∀ u, ‖schwartzSobolevCoordinate s
          (coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u - B u)‖ ≤
        C * h * ‖schwartzSobolevCoordinate s u‖ := by
  /- Use the fixed exact near/tail decomposition. The near operator minus the
  original diagonal quantizer is precisely the quantified first remainder.
  Transport the actual zero-diagonal source tail with the fixed original
  pullbacks, and add their two Sobolev bounds. No endpoint limit is used. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let d := zeroExtendedSymbol e.target ρ
    (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e p x ξ)
  obtain ⟨hd, hcd⟩ := raw_coordinate_leading_symbol_properties
    p hp e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV
  obtain ⟨a, R, ha, hca, hR, hcR, hRdiag, hadiag, hsplit⟩ :=
    exists_raw_coordinate_frequencyScale_amplitudes p hp e he hψ χ ρ
      hχ hcχ hχU hρ hcρ hρV
  obtain ⟨Ca, hCa, hCab⟩ := ha.exists_frequencyScale_remainder_operator_bound hca s
  obtain ⟨Cr, hCr, hCrb⟩ := hR.exists_frequencyScale_sobolev_bound_of_diag_eq_zero
    hcR hRdiag s
  let T := {h : ℝ // 0 < h ∧ h ≤ 1}
  let tails : T → 𝓢(X, EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(X, EuclideanSpace ℂ (Fin q)) := fun h ↦
    amplitudeOperator 0 (frequencyScaleAmplitude h.val R)
      (hR.frequencyScale h.val h.property.1 h.property.2)
      (hasCompactSupport_frequencyScaleAmplitude h.val hcR)
  obtain ⟨Ct, hCt, hCtb⟩ := exists_uniform_coordinatePushforward_sobolev_bound
    tails (fun h : T ↦ h.val) (fun h ↦ h.property.1.le) Cr hCr
    e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV s
    (fun h v ↦ hCrb h.val h.property.1 h.property.2 v)
  refine ⟨Ca + Ct, add_nonneg hCa hCt, ?_⟩
  intro h hh hh₁ P B hP hB u
  let ah := frequencyScaleAmplitude h a
  have hah : IsAmplitude 0 ah := ha.frequencyScale h hh hh₁
  have hcah := hasCompactSupport_frequencyScaleAmplitude h hca
  let c := amplitudeSymbol ah
  let δ : SymbolFunction n r q := fun x ξ ↦ ah x x ξ
  have hδscale : δ = frequencyScaleSymbol h d := by
    funext x ξ
    exact hadiag x (h • ξ)
  have hc : IsSymbol univ 0 c := isSymbol_amplitudeSymbol 0 ah hah hcah
  have hcc : HasCompactSupport c := hasCompactSupport_amplitudeSymbol ah hcah
  have hδ : IsSymbol univ 0 δ := by
    rw [hδscale]
    exact hd.frequencyScale h hh hh₁
  have hcδ : HasCompactSupport δ := by
    rw [hδscale]
    exact hcd.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_frequencyScaleSymbol_subset d h)
  let b := c - δ
  have hb : IsSymbol univ 0 b := (symbolSpace univ isOpen_univ 0 r q).sub_mem hc hδ
  have hcb : HasCompactSupport b :=
    (hcc.union hcδ).of_isClosed_subset (isClosed_tsupport _) (tsupport_sub c δ)
  let Aop := amplitudeOperator 0 ah hah hcah
  let Rop := quantizeSchwartz 0 b hb hcb
  let Bop := quantizeSchwartz 0 δ hδ hcδ
  have hsameB : Bop = B := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    rw [quantizeSchwartz_apply, hδscale]
    exact (hB v x).symm
  have hsameA : quantizeSchwartz 0 c hc hcc = Aop := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    exact (quantizeSchwartz_apply 0 c hc hcc v x).trans
      ((congrFun (quantize_amplitudeSymbol 0 ah hah hcah v) x).trans
        (amplitudeOperator_apply 0 ah hah hcah v x).symm)
  have hsum : Aop = Rop + Bop := by
    have hplus : b + δ = c := sub_add_cancel _ _
    have hs := quantizeSchwartz_add 0 b δ hb hδ hcb hcδ
      ((symbolSpace univ isOpen_univ 0 r q).add_mem hb hδ) (hcb.add hcδ)
    simpa only [hplus, hsameA] using hs
  have hRop : Rop = Aop - B := by
    rw [← hsameB]
    exact eq_sub_iff_add_eq.mpr hsum.symm
  have hRbound : ‖schwartzSobolevCoordinate s (Rop u)‖ ≤
      Ca * h * ‖schwartzSobolevCoordinate s u‖ := by
    apply hCab h hh hh₁ Rop
    intro v x
    exact quantizeSchwartz_apply 0 b hb hcb v x
  let z : T := ⟨h, hh, hh₁⟩
  let F := coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV (tails z)
  have herror : coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u - B u =
      Rop u + F u := by
    rw [hsplit h hh hh₁ P hP u, hRop]
    simp only [sub_apply]
    change Aop u + F u - B u = (Aop u - B u) + F u
    abel
  calc
    _ = ‖schwartzSobolevCoordinate s (Rop u + F u)‖ := by rw [herror]
    _ ≤ ‖schwartzSobolevCoordinate s (Rop u)‖ +
        ‖schwartzSobolevCoordinate s (F u)‖ := by
      rw [schwartzSobolevCoordinate_add]
      exact norm_add_le _ _
    _ ≤ Ca * h * ‖schwartzSobolevCoordinate s u‖ +
        Ct * h * ‖schwartzSobolevCoordinate s u‖ :=
      add_le_add hRbound (hCtb z u)
    _ = (Ca + Ct) * h * ‖schwartzSobolevCoordinate s u‖ := by ring

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothingKernelSymbol

import all AtiyahSinger.Analysis.CoordinateChange

/-!
# A fixed near-diagonal amplitude and its smooth kernel remainder

Public module ID: M0633.

The original compactly supported coordinate operator splits using a specified
near-diagonal cutoff. The remainder is the actual smooth kernel of the fixed
original off-diagonal amplitude. Keeping this cutoff fixed before changing
coordinates is essential for compact parameter averaging.

This extracts the fixed-cutoff part of the usual coordinate-change proof,
retaining its original operator, exact amplitude action and two-sided support.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

set_option maxHeartbeats 600000 in
-- The same residual amplitude supplies its support, smoothing kernel and exact splitting.
/-- A specified near-diagonal cutoff leaves one fixed smooth-kernel remainder. -/
theorem exists_fixed_amplitude_kernel_remainder {n r q : ℕ}
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hPK : HasOperatorSupport K P)
    (β : EuclideanSpace ℝ (Fin n) → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hcβ : HasCompactSupport β) (hβone : K ⊆ interior {x | β x = 1})
    (γ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ₀ : ContDiff ℝ ∞ γ₀) (hcγ₀ : HasCompactSupport γ₀)
    (hγ₀supp : tsupport γ₀ ⊆ tsupport β ×ˢ tsupport β)
    (hoff : ∀ x : EuclideanSpace ℝ (Fin n),
      (fun z ↦ β z.1 * β z.2 - γ₀ z) =ᶠ[𝓝 (x, x)] (fun _ ↦ 0)) :
    ∃ (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
      (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))),
      ContDiff ℝ ∞ (Function.uncurry k) ∧ HasCompactSupport (Function.uncurry k) ∧
      (∀ u x, Q u x = ∫ y, k x y (u y)) ∧
      HasOperatorSupport (tsupport β) Q ∧
      ∀ u x, P u x = amplitudeApply (localizedAmplitude γ₀ p) u x + Q u x := by
  /- The plateau makes the total two-sided cutoff operator equal to P. Split
  its integrable amplitude into the prescribed near-diagonal part and its
  complement. The complement vanishes near every diagonal point, hence its
  reduced symbol is smoothing and its actual compact kernel gives the remainder. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let A := localizedAmplitude γ₀ p
  let χR : X × X → ℝ := fun z ↦ β z.1 * β z.2 - γ₀ z
  let R := localizedAmplitude χR p
  let T := cutoffAmplitude β β p
  have hχR : ContDiff ℝ ∞ χR :=
    ((hβ.comp contDiff_fst).mul (hβ.comp contDiff_snd)).sub hγ₀
  have hχRsupp : tsupport χR ⊆ tsupport β ×ˢ tsupport β := by
    apply closure_minimal ?_ ((isClosed_tsupport β).prod (isClosed_tsupport β))
    intro z hz
    by_contra hout
    have hγ₀z : γ₀ z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hout (hγ₀supp h))
    rcases not_and_or.mp hout with hx | hy
    · exact hz (by simp [χR, image_eq_zero_of_notMem_tsupport hx, hγ₀z])
    · exact hz (by simp [χR, image_eq_zero_of_notMem_tsupport hy, hγ₀z])
  have hcχR : HasCompactSupport χR :=
    (hcβ.prod hcβ).of_isClosed_subset (isClosed_tsupport _) hχRsupp
  have hsupp (η : X × X → ℝ) :
      tsupport (Function.uncurry (localizedAmplitude η p)) ⊆ tsupport η := by
    apply closure_minimal ?_ (isClosed_tsupport η)
    intro z hz
    by_contra hout
    apply hz
    funext ξ
    simp only [Function.uncurry, localizedAmplitude, Prod.eta,
      image_eq_zero_of_notMem_tsupport hout, zero_smul, Pi.zero_apply]
  have hA : IsAmplitude m A := isAmplitude_localizedAmplitude m p hp γ₀ hγ₀
  have hcA : HasCompactSupport (Function.uncurry A) :=
    hcγ₀.of_isClosed_subset (isClosed_tsupport _) (hsupp γ₀)
  have hR : IsAmplitude m R := isAmplitude_localizedAmplitude m p hp χR hχR
  have hcR : HasCompactSupport (Function.uncurry R) :=
    hcχR.of_isClosed_subset (isClosed_tsupport _) (hsupp χR)
  have hT : IsAmplitude m T := isAmplitude_cutoffAmplitude m p hp β β hβ hβ
  have hcT : HasCompactSupport (Function.uncurry T) :=
    hasCompactSupport_cutoffAmplitude p β β hcβ hcβ
  -- The original two-sided operator support makes the total cutoff operator equal P.
  have htotal (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      amplitudeApply T u x = P u x := by
    let v : 𝓢(X, EuclideanSpace ℂ (Fin r)) :=
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (β y : ℂ)) u
    have hgrowth : (fun y ↦ (β y : ℂ)).HasTemperateGrowth :=
      (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hβ)
    have hv (y : X) : v y = β y • u y := by
      rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
      exact algebraMap_smul ℂ (β y) (u y)
    have hinput : P v = P u := by
      have hd : Disjoint (tsupport (v - u)) K := by
        apply Set.disjoint_left.mpr
        intro y hy hyK
        apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hy
        filter_upwards [isOpen_interior.mem_nhds (hβone hyK)] with z hz
        have hβz : β z = 1 := interior_subset (s := {x | β x = 1}) hz
        simp only [sub_apply, hv, hβz, one_smul, sub_self, Pi.zero_apply]
      exact sub_eq_zero.mp (by simpa only [map_sub] using hPK.2 (v - u) hd)
    have houtput : β x • P u x = P u x := by
      by_cases hx : x ∈ K
      · rw [show β x = 1 from interior_subset (s := {x | β x = 1}) (hβone hx), one_smul]
      · have hz : P u x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hPK.1 u h))
        rw [hz, smul_zero]
    rw [amplitudeApply_cutoffAmplitude m p hp β β hβ hβ hcβ hcβ u x, ← hP]
    change β x • P v x = P u x
    rw [hinput, houtput]
  -- Addition is performed only inside the already integrable iterated amplitude integrals.
  have hsplit (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      P u x = amplitudeApply A u x + amplitudeApply R u x := by
    rw [← htotal u x]
    unfold amplitudeApply
    rw [← smul_add, ← integral_add (integrable_amplitudeApply_outer m A hA hcA u x)
      (integrable_amplitudeApply_outer m R hR hcR u x)]
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    rw [← integral_add (integrable_amplitudeApply_inner m A hA hcA u x ξ)
      (integrable_amplitudeApply_inner m R hR hcR u x ξ)]
    apply integral_congr_ae
    filter_upwards with y
    simp only [T, A, R, cutoffAmplitude, localizedAmplitude, χR, smul_apply,
      sub_smul, sub_apply, smul_sub, add_sub_cancel]
  let Q := amplitudeOperator m R hR hcR
  have hQK : HasOperatorSupport (tsupport β) Q :=
    hasOperatorSupport_amplitudeOperator m R hR hcR (tsupport β) (isClosed_tsupport β)
      ((hsupp χR).trans hχRsupp)
  let V : Set (X × X) := interior {z | χR z = 0}
  have hVdiag (x : X) : (x, x) ∈ V := mem_interior_iff_mem_nhds.mpr (hoff x)
  have hRzero (z : X × X) (hz : z ∈ V) (ξ : X) : R z.1 z.2 ξ = 0 := by
    have hz0 : χR z = 0 := interior_subset (s := {z | χR z = 0}) hz
    simp only [R, localizedAmplitude, Prod.eta, hz0, zero_smul]
  have hsmoothR : IsSmoothingSymbol univ (amplitudeSymbol R) :=
    isSmoothingSymbol_amplitudeSymbol_of_off_diagonal m R hR hcR V isOpen_interior
      hVdiag hRzero
  have hQ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      Q u x = quantize (amplitudeSymbol R) u x :=
    (amplitudeOperator_apply m R hR hcR u x).trans
      (congrFun (quantize_amplitudeSymbol m R hR hcR u) x).symm
  obtain ⟨k, hk, hck, hkQ⟩ := exists_compactSmoothKernel_of_smoothingSymbol
    (amplitudeSymbol R) hsmoothR Q hQ (tsupport β) hcβ hQK
  refine ⟨Q, k, hk, hck, hkQ, hQK, ?_⟩
  intro u x
  rw [show Q u x = amplitudeApply R u x from amplitudeOperator_apply m R hR hcR u x]
  exact hsplit u x

end AtiyahSinger

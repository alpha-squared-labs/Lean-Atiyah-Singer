/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange

import AtiyahSinger.Analysis.CompactQuantization

/-!
# The full coordinate expansion of the actual transported operator

Public module ID: M0403.

A02: SG III.3.12 and (3.16), pp.183--186. The preceding coordinate theorem
identifies the exact transported symbol only modulo one lower order. Here
one exact symbol has every finite Taylor remainder, with coefficients from
the actual inverse-transpose frequency substitution and absolute Jacobians.
This is a full S^m_(1,0) expansion, not a claim of classical homogeneity.

The coefficient formula differentiates the uncut coordinate amplitude and
then evaluates on the diagonal inside e.target. Its totalized inverse away
from that diagonal is not asserted smooth or uniformly invertible. Compact
operator support permits near-diagonal localization; all cutoff derivatives
disappear from the displayed jets. No global convexity, orientation or
uniform control at infinity is assumed. Source and target ranks are independent.
The proof uses the exact compact amplitude normal form and the same smoothing
remainder at every order, preserving the specified transported operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Filter
open scoped ContDiff SchwartzMap

variable {n r s : ℕ}

/-- SG (3.16): one exact transported symbol has the full coordinate asymptotic expansion. -/
theorem exists_symbol_coordinatePushforward_expansion
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol Set.univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ e.source)
    (hPK : HasOperatorSupport K P) (hχone : K ⊆ interior {x | χ x = 1})
    (hρone : e '' K ⊆ interior {x | ρ x = 1}) :
    ∃ q : SymbolFunction n r s,
      IsSymbol Set.univ m q ∧ HasCompactSupport q ∧ tsupport q ⊆ e '' K ∧
        (∀ u x, coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x =
          quantize q u x) ∧
        HasSymbolExpansion e.target (fun j ↦ m - (j : ℝ)) q
          (amplitudeExpansionTerm (coordinateAmplitude e (fun _ ↦ 1) p)) := by
  -- Retain a single exact symbol from the compact amplitude and smoothing remainder.
  obtain ⟨a, b, ha, hca, hb, hcb, happly, hgerm⟩ :=
    exists_coordinatePushforward_amplitude e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV
      m p hp P hP K hK hKU hPK hχone hρone
  let q := amplitudeSymbol a + b
  have hqa := isSymbol_amplitudeSymbol m a ha hca
  have hcqa := hasCompactSupport_amplitudeSymbol a hca
  have hq : IsSymbol univ m q := hqa.add isOpen_univ (hb m)
  have hcq : HasCompactSupport q := hcqa.add hcb
  have hsum (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) x :
      quantize q u x = amplitudeApply a u x + quantize b u x := by
    have h := congrArg (fun T ↦ T u x)
      (quantizeSchwartz_add m (amplitudeSymbol a) b hqa (hb m) hcqa hcb hq hcq)
    simp only [add_apply, quantizeSchwartz_apply] at h
    rw [quantize_amplitudeSymbol m a ha hca u] at h
    exact h
  have hact (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) x :
      coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x = quantize q u x :=
    (happly u x).trans (hsum u x).symm
  have heK : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hqsupp : tsupport q ⊆ e '' K := tsupport_symbol_subset_of_hasOperatorSupport
    m q hq (coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P)
    hact (e '' K) heK.isClosed
    (hasOperatorSupport_coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV
      P K hK hKU hPK)
  refine ⟨q, hq, hcq, hqsupp, hact, ?_⟩
  -- Equality of the full spatial germ identifies the mixed y/frequency derivatives
  -- before evaluation on the diagonal, for every finite expansion degree.
  have hterm (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) :
      amplitudeExpansionTerm a j x =
        amplitudeExpansionTerm (coordinateAmplitude e (fun _ ↦ 1) p) j x := by
    have hnear := (hgerm x hx).comp_tendsto
      (continuous_const.prodMk continuous_id).continuousAt
    have hder : (fun η ↦ iteratedFDeriv ℝ j (fun y ↦ a x y η) x) =
        (fun η ↦ iteratedFDeriv ℝ j
          (fun y ↦ coordinateAmplitude e (fun _ ↦ 1) p x y η) x) := by
      funext η
      have hnearη : (fun y ↦ a x y η) =ᶠ[nhds x]
          (fun y ↦ coordinateAmplitude e (fun _ ↦ 1) p x y η) := by
        filter_upwards [hnear] with y hy
        exact congrFun hy η
      exact (hnearη.iteratedFDeriv ℝ j).eq_of_nhds
    funext ξ
    simp only [amplitudeExpansionTerm, hder]
  -- The same smoothing symbol belongs to every remainder order, so the exact
  -- symbol chosen above serves all truncation lengths simultaneously.
  intro N
  have hlow : IsSymbol univ (m - (N : ℝ))
      (q - ∑ j ∈ Finset.range N, amplitudeExpansionTerm a j) := by
    convert (hasSymbolExpansion_amplitudeSymbol m a ha hca N).add isOpen_univ
      (hb (m - (N : ℝ))) using 1
    ext x ξ v
    simp only [q, Pi.add_apply, Pi.sub_apply, add_apply, sub_apply]
    abel_nf
  apply (hlow.restrict (subset_univ e.target)).congr_on e.open_target
  intro x hx
  funext ξ
  simp only [Pi.sub_apply, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact congrFun (hterm j x hx) ξ

end AtiyahSinger

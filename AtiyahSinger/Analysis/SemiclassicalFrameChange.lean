/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Analysis.SemiclassicalGlobalQuantization

import all AtiyahSinger.Analysis.SemiclassicalComposition

/-!
# Actual frame multipliers at a positive frequency scale

Public module ID: M2309.

Sources: SG III.3.5, III.3.15 and III.3.18, with the quantitative first
amplitude remainder in M2293 and M2295. SG means H. Blaine Lawson, Jr. and
Marie-Louise Michelsohn, *Spin Geometry* (Princeton University Press, 1989).
The original matrix amplitude and exact multiplier identity are reused from
M0639 FrameChange.

The actual operator with fixed smooth compact matrix factors A and B is
compared to the original quantization of the fixed leading matrixSymbol.
The same fixed matrix amplitude scales exactly, and its actual first
remainder gives one error constant before the positive contraction parameter.
All rectangular ranks and the original matrix order A, p, B are retained.

The shared amplitude-diagonal helper also applies to original native cutoff
amplitudes. Its diagonal symbol facts are supplied as mathematical properties
of that same fixed amplitude. The matrix theorem constructs those properties
from the original p, A and B and assumes only the two pointwise quantizer formulas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff SchwartzMap

variable {n r q k l : ℕ}

set_option maxSynthPendingDepth 15

/-- The same fixed leading matrix symbol has its standard global symbol and support properties. -/
private theorem raw_matrix_leading_symbol_properties
    (p : SymbolFunction n r q) (hp : IsSymbol univ 0 p)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B) :
    IsSymbol univ 0 (matrixSymbol A B p) ∧ HasCompactSupport (matrixSymbol A B p) := by
  /- Reuse the original ordered matrix symbol estimate. Nonzero leading values
  require both original spatial matrices to be nonzero, so its closed spatial
  support lies in the intersection of their two compact supports. -/
  refine ⟨isSymbol_matrixSymbol univ isOpen_univ 0 p hp A B hA.contDiffOn hB.contDiffOn, ?_⟩
  apply (hcA.inter hcB).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ ((isClosed_tsupport A).inter (isClosed_tsupport B))
  intro x hx
  constructor
  · by_contra hxA
    apply hx
    funext ξ
    simp [matrixSymbol, image_eq_zero_of_notMem_tsupport hxA]
  · by_contra hxB
    apply hx
    funext ξ
    simp [matrixSymbol, image_eq_zero_of_notMem_tsupport hxB]

/-- The original scaled amplitude minus its actual diagonal quantizer has one small bound. -/
private theorem IsAmplitude.exists_frequencyScale_diagonal_error_sobolev_bound
    {a : AmplitudeFunction n r q} (ha : IsAmplitude 0 a)
    (hca : HasCompactSupport (Function.uncurry a))
    (d : SymbolFunction n r q) (hd : IsSymbol univ 0 d) (hcd : HasCompactSupport d)
    (hdiag : ∀ x ξ, a x x ξ = d x ξ) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, ∀ hh : 0 < h, ∀ hh₁ : h ≤ 1,
      ∀ B : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      (∀ u x, B u x = quantize (frequencyScaleSymbol h d) u x) →
      ∀ u, ‖schwartzSobolevCoordinate s
          (amplitudeOperator 0 (frequencyScaleAmplitude h a)
            (ha.frequencyScale h hh hh₁)
            (hasCompactSupport_frequencyScaleAmplitude h hca) u - B u)‖ ≤
        C * h * ‖schwartzSobolevCoordinate s u‖ := by
  /- The actual first-remainder estimate chooses its constant before h. Identify
  its quantization with the same amplitude operator minus the given diagonal
  quantizer, using exact compact-symbol additivity and both original formulas. -/
  classical
  obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_remainder_operator_bound hca s
  refine ⟨C, hC, ?_⟩
  intro h hh hh₁ B hB u
  let ah := frequencyScaleAmplitude h a
  have hah : IsAmplitude 0 ah := ha.frequencyScale h hh hh₁
  have hcah := hasCompactSupport_frequencyScaleAmplitude h hca
  let c := amplitudeSymbol ah
  let δ : SymbolFunction n r q := fun x ξ ↦ ah x x ξ
  have hδscale : δ = frequencyScaleSymbol h d := by
    funext x ξ
    exact hdiag x (h • ξ)
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
  -- The supplied B is precisely the original quantization of this same scaled diagonal.
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
  have hvalue : Rop u = Aop u - B u := by rw [hRop, sub_apply]
  -- Apply the actual first-remainder estimate to this same subtraction operator.
  change ‖schwartzSobolevCoordinate s (Aop u - B u)‖ ≤ _
  rw [← hvalue]
  apply hCb h hh hh₁ Rop
  intro v x
  exact quantizeSchwartz_apply 0 b hb hcb v x

/-- Original raw matrix multipliers have a uniform error relative to their leading quantizer. -/
theorem exists_frequencyScale_raw_matrixMultiplier_sobolev_bound
    (p : SymbolFunction n r q) (hp : IsSymbol univ 0 p)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      ∀ Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin k)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin l)),
      (∀ u x, P u x = quantize (frequencyScaleSymbol h p) u x) →
      (∀ u x, Q u x = quantize (frequencyScaleSymbol h (matrixSymbol A B p)) u x) →
      ∀ u, ‖schwartzSobolevCoordinate s
          (((matrixMultiplierCLM A hA hcA).comp
            (P.comp (matrixMultiplierCLM B hB hcB))) u - Q u)‖ ≤
        C * h * ‖schwartzSobolevCoordinate s u‖ := by
  /- First construct the original fixed matrix amplitude and its actual diagonal
  symbol. The shared first-remainder bound then precedes h. Finally the exact
  original matrix-amplitude identity identifies the actual multiplier operator
  on each raw Schwartz input, preserving A, p, B in their original order. -/
  let a := matrixAmplitude A B p
  let d := matrixSymbol A B p
  have ha : IsAmplitude 0 a := isAmplitude_matrixAmplitude 0 p hp A B hA hB
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_matrixAmplitude A B p hcA hcB
  obtain ⟨hd, hcd⟩ := raw_matrix_leading_symbol_properties p hp A B hA hcA hB hcB
  have hdiag (x ξ : EuclideanSpace ℝ (Fin n)) : a x x ξ = d x ξ := rfl
  obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_diagonal_error_sobolev_bound
    hca d hd hcd hdiag s
  refine ⟨C, hC, ?_⟩
  intro h hh hh₁ P Q hP hQ u
  let ph := frequencyScaleSymbol h p
  have hph : IsSymbol univ 0 ph := hp.frequencyScale h hh hh₁
  let ah := frequencyScaleAmplitude h a
  have hah : IsAmplitude 0 ah := ha.frequencyScale h hh hh₁
  have hcah := hasCompactSupport_frequencyScaleAmplitude h hca
  let MA := matrixMultiplierCLM A hA hcA
  let MB := matrixMultiplierCLM B hB hcB
  have hsame : amplitudeOperator 0 ah hah hcah = MA.comp (P.comp MB) := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    calc
      _ = amplitudeApply ah v x := amplitudeOperator_apply 0 ah hah hcah v x
      _ = quantize (amplitudeSymbol ah) v x :=
        (congrFun (quantize_amplitudeSymbol 0 ah hah hcah v) x).symm
      _ = A x (quantize ph (MB v) x) := by
        change quantize (amplitudeSymbol (matrixAmplitude A B ph)) v x = _
        exact quantize_matrixAmplitude 0 ph hph A B hA hcA hB hcB v x
      _ = A x (P (MB v) x) := by rw [← hP]
      _ = _ := by
        change A x (P (MB v) x) = MA (P (MB v)) x
        exact (matrixMultiplierCLM_apply A hA hcA (P (MB v)) x).symm
  have hbound := hCb h hh hh₁ Q hQ u
  change ‖schwartzSobolevCoordinate s (amplitudeOperator 0 ah hah hcah u - Q u)‖ ≤
    C * h * ‖schwartzSobolevCoordinate s u‖ at hbound
  rw [hsame] at hbound
  exact hbound

end AtiyahSinger

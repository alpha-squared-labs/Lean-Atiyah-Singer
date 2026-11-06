/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RawComposition
public import AtiyahSinger.Analysis.SemiclassicalGlobalQuantization

import all AtiyahSinger.Analysis.SemiclassicalComposition
import all AtiyahSinger.Analysis.SemiclassicalGlobalQuantization

/-!
# A uniform estimate for the original raw scaled composition

Public module ID: M2305.

Sources: SG III.3.10 and TA II.4.4, II.6.1, together with the quantitative
supplementary estimates in M2293 and M2295. SG means H. Blaine Lawson, Jr. and
Marie-Louise Michelsohn, *Spin Geometry* (Princeton University Press, 1989).
TA means Michael E. Taylor, *Pseudodifferential Operators* (Princeton
University Press, 1981).

The exact raw composition formula contains an input cutoff. Choose two nested
cutoffs internally, keep its actual off-diagonal error, and combine that error
with the actual two-reduction composition estimate. This proves the original
raw product bound on every Sobolev coordinate space with one constant chosen
before the positive contraction parameter. All realizations retain the same
original Fourier quantization and rectangular product order.

This local estimate supplies neither the global coordinate and frame assembly
nor the final zero-index result. It uses no norm continuity at parameter zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set MeasureTheory
open scoped ContDiff SchwartzMap

variable {n r q k : ℕ}

set_option maxSynthPendingDepth 15

/-- The original finite-seminorm estimate bounds all raw contractions uniformly. -/
private theorem exists_frequencyScale_raw_sobolev_bound {p : SymbolFunction n r q}
    (hp : IsSymbol univ 0 p) (hc : HasCompactSupport p) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      (∀ u x, P u x = quantize (frequencyScaleSymbol h p) u x) →
      ∀ u, ‖schwartzSobolevCoordinate s (P u)‖ ≤
        C * ‖schwartzSobolevCoordinate s u‖ := by
  /- Reuse the accepted all-frequency bounds and the actual finite source seminorms.
  The common support and every chosen derivative constant precede the scale. -/
  let T := {h : ℝ // 0 < h ∧ h ≤ 1}
  let family : T → SymbolFunction n r q := fun h ↦ frequencyScaleSymbol h.val p
  have hfamily (h : T) : IsSymbol univ 0 (family h) :=
    hp.frequencyScale h.val h.property.1 h.property.2
  have hsupp (h : T) : tsupport (family h) ⊆ tsupport p :=
    tsupport_frequencyScaleSymbol_subset p h.val
  have hbound : ∀ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L → ∀ i j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x, x ∈ L → ∀ ξ,
        ‖symbolDerivative (family h) i j x ξ‖ ≤
          C * (1 : ℝ) * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
    intro L hL i j
    obtain ⟨C, hC, hCb⟩ := exists_frequencyScale_all_derivative_bound
      hp L (subset_univ _) hL i j
    exact ⟨C, hC, fun h x hx ξ ↦ by
      simpa only [mul_one] using hCb h.val h.property.1 h.property.2 x hx ξ⟩
  obtain ⟨C, hC, hCb⟩ := exists_uniform_quantizeSchwartz_sobolev_bound
    family hfamily (tsupport p) hc hsupp (fun _ : T ↦ 1) (fun _ ↦ zero_le_one) hbound s
  refine ⟨C, hC, ?_⟩
  intro h hh hh₁ P hP u
  let z : T := ⟨h, hh, hh₁⟩
  have hsame : quantizeSchwartz 0 (family z) (hfamily z)
      (hc.of_isClosed_subset (isClosed_tsupport (family z)) (hsupp z)) = P := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    exact (quantizeSchwartz_apply 0 (family z) (hfamily z)
      (hc.of_isClosed_subset (isClosed_tsupport (family z)) (hsupp z)) v x).trans (hP v x).symm
  have h := hCb z u
  rw [hsame] at h
  simpa only [mul_one] using h

set_option maxHeartbeats 1500000 in
-- Retain the exact raw cutoff error and both original symbol reductions in one estimate.
/-- The original raw scaled product has a uniform first-order Sobolev error. -/
theorem exists_frequencyScale_raw_composition_sobolev_bound
    (p : SymbolFunction n q k) (a : SymbolFunction n r q)
    (hp : IsSymbol univ 0 p) (ha : IsSymbol univ 0 a)
    (hpSupp : HasCompactSupport p) (haSupp : HasCompactSupport a) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin k)),
      ∀ A : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      ∀ B : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin k)),
      (∀ u x, P u x = quantize (frequencyScaleSymbol h p) u x) →
      (∀ u x, A u x = quantize (frequencyScaleSymbol h a) u x) →
      (∀ u x, B u x = quantize
        (symbolComp (frequencyScaleSymbol h p) (frequencyScaleSymbol h a)) u x) →
      ∀ u, ‖schwartzSobolevCoordinate s (P (A u) - B u)‖ ≤
        C * h * ‖schwartzSobolevCoordinate s u‖ := by
  /- First choose σ=1 near the original right-symbol support, then χ=1 near supp σ.
  The actual reduced composition realizes P A Mχ. Its first-remainder norm is small
  by the complete two-reduction estimate. The exact off-diagonal symbol realizes
  A - A Mχ, whose own norm is small. A common raw P bound then includes the whole
  missing input tail in P A - Op(p a), with every constant chosen before h. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let T := {h : ℝ // 0 < h ∧ h ≤ 1}
  obtain ⟨σ, hσ, hcσ, _, hσone⟩ :=
    exists_compact_cutoff_one_near (tsupport a) univ haSupp isOpen_univ (subset_univ _)
  obtain ⟨χ, hχ, hcχ, _, hχone⟩ :=
    exists_compact_cutoff_one_near (tsupport σ) univ hcσ isOpen_univ (subset_univ _)
  have hσpoint (x : V) (hx : x ∈ tsupport a) : σ x = 1 :=
    interior_subset (s := {y | σ y = 1}) (hσone hx)
  have hχpoint : ∀ x ∈ tsupport a, χ x = 1 := by
    intro x hx
    have hxσ : x ∈ tsupport σ := subset_tsupport σ (by
      change σ x ≠ 0
      rw [hσpoint x hx]
      exact one_ne_zero)
    exact interior_subset (s := {y | χ y = 1}) (hχone hxσ)
  let ph : T → SymbolFunction n q k := fun h ↦ frequencyScaleSymbol h.val p
  let ah : T → SymbolFunction n r q := fun h ↦ frequencyScaleSymbol h.val a
  have hph (h : T) : IsSymbol univ 0 (ph h) :=
    hp.frequencyScale h.val h.property.1 h.property.2
  have hah (h : T) : IsSymbol univ 0 (ah h) :=
    ha.frequencyScale h.val h.property.1 h.property.2
  have hcph (h : T) : HasCompactSupport (ph h) :=
    hpSupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_frequencyScaleSymbol_subset p h.val)
  have hcah (h : T) : HasCompactSupport (ah h) :=
    haSupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_frequencyScaleSymbol_subset a h.val)
  let b : T → SymbolFunction n r k := fun h ↦ symbolComp (ph h) (ah h)
  let c : T → SymbolFunction n r k := fun h ↦ compositionSymbol χ (ph h) (ah h)
  let R : T → SymbolFunction n r k := fun h ↦ c h - b h
  have hb (h : T) : IsSymbol univ 0 (b h) := by
    simpa only [zero_add] using (hph h).symbolComp isOpen_univ (hah h)
  have hcbSupp (h : T) : tsupport (b h) ⊆ tsupport p := by
    apply closure_minimal ?_ (isClosed_tsupport p)
    intro x hx
    by_contra hxp
    have hzero : p x = 0 := image_eq_zero_of_notMem_tsupport hxp
    apply hx
    funext ξ
    simp [b, symbolComp, ph, frequencyScaleSymbol, hzero]
  have hcb (h : T) : HasCompactSupport (b h) :=
    hpSupp.of_isClosed_subset (isClosed_tsupport _) (hcbSupp h)
  have hcomp (h : T) : IsSymbol univ 0 (c h) := by
    simpa only [zero_add] using isSymbol_compositionSymbol 0 0 (ph h) (ah h)
      (hph h) (hah h) (hcph h) (hcah h) χ hχ hcχ
  have hcompSupp (h : T) : tsupport (c h) ⊆ tsupport p :=
    (tsupport_compositionSymbol_subset χ (ph h) (ah h)).trans
      (tsupport_frequencyScaleSymbol_subset p h.val)
  have hccomp (h : T) : HasCompactSupport (c h) :=
    hpSupp.of_isClosed_subset (isClosed_tsupport _) (hcompSupp h)
  have hR (h : T) : IsSymbol univ 0 (R h) :=
    (symbolSpace univ isOpen_univ 0 r k).sub_mem (hcomp h) (hb h)
  have hRsupp (h : T) : tsupport (R h) ⊆ tsupport p :=
    (tsupport_sub (c h) (b h)).trans (union_subset (hcompSupp h) (hcbSupp h))
  have hcR (h : T) : HasCompactSupport (R h) :=
    hpSupp.of_isClosed_subset (isClosed_tsupport _) (hRsupp h)
  -- Bound the complete genuine reduced composition before choosing any parameter.
  have hRbound : ∀ L : Set V, IsCompact L → ∀ i j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ h : T, ∀ x, x ∈ L → ∀ ξ,
        ‖symbolDerivative (R h) i j x ξ‖ ≤
          C * h.val * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
    intro L hL i j
    obtain ⟨C, hC, hCb⟩ := exists_compositionSymbol_frequencyScale_sub_bound
      p a hp ha hpSupp haSupp χ hχ hcχ hχpoint L hL i j
    exact ⟨C, hC, fun h x hx ξ ↦ hCb h.val h.property.1 h.property.2 x hx ξ⟩
  obtain ⟨Cr, hCr, hCrb⟩ := exists_uniform_quantizeSchwartz_sobolev_bound
    R hR (tsupport p) hpSupp hRsupp (fun h : T ↦ h.val)
    (fun h ↦ h.property.1.le) hRbound s
  obtain ⟨Cp, hCp, hCpb⟩ := exists_frequencyScale_raw_sobolev_bound hp hpSupp s
  obtain ⟨Cd, hCd, hCdb⟩ :=
    ha.exists_frequencyScale_offDiagonal_sobolev_bound σ χ hσ hcσ hχ hcχ hχone s
  refine ⟨Cr + Cp * Cd, add_nonneg hCr (mul_nonneg hCp hCd), ?_⟩
  intro h hh hh₁ P A B hP hA hB u
  let z : T := ⟨h, hh, hh₁⟩
  let Mχ := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (χ y : ℂ))
  let Rop := quantizeSchwartz 0 (R z) (hR z) (hcR z)
  let Bop := quantizeSchwartz 0 (b z) (hb z) (hcb z)
  let Cop := quantizeSchwartz 0 (c z) (hcomp z) (hccomp z)
  let Aop := quantizeSchwartz 0 (ah z) (hah z) (hcah z)
  let D := quantizeSchwartz 0 (offDiagonalSymbol σ χ (ah z))
    (isSmoothingSymbol_offDiagonalSymbol 0 (ah z) (hah z) σ χ hσ hcσ hχ hcχ hχone 0)
    (hasCompactSupport_offDiagonalSymbol σ χ (ah z) hcσ)
  have hsameA : Aop = A := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    exact (quantizeSchwartz_apply 0 (ah z) (hah z) (hcah z) v x).trans (hA v x).symm
  have hsameB : Bop = B := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    exact (quantizeSchwartz_apply 0 (b z) (hb z) (hcb z) v x).trans (hB v x).symm
  -- The exact raw formula identifies this same Cop with P A Mχ.
  have hCop (v : 𝓢(V, EuclideanSpace ℂ (Fin r))) : Cop v = P (A (Mχ v)) := by
    apply SchwartzMap.ext
    intro x
    rw [quantizeSchwartz_apply,
      quantize_compositionSymbol_mulCutoff 0 0 (ph z) (ah z)
        (hph z) (hah z) (hcph z) (hcah z) χ hχ hcχ]
    change quantize (ph z) (Aop (Mχ v)) x = _
    rw [hsameA]
    exact (hP (A (Mχ v)) x).symm
  have hsum : Cop = Rop + Bop := by
    have hplus : R z + b z = c z := sub_add_cancel _ _
    have h := quantizeSchwartz_add 0 (R z) (b z) (hR z) (hb z) (hcR z) (hcb z)
      ((symbolSpace univ isOpen_univ 0 r k).add_mem (hR z) (hb z))
      ((hcR z).add (hcb z))
    simpa only [hplus] using h
  have hRop : Rop = Cop - Bop := eq_sub_iff_add_eq.mpr hsum.symm
  have hRvalue : Rop u = P (A (Mχ u)) - B u := by
    rw [hRop, sub_apply, hCop, hsameB]
  -- The complementary input multiplier is an actual Schwartz map on every original input.
  have hχgrowth : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hcomplement (v : 𝓢(V, EuclideanSpace ℂ (Fin r))) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun y ↦ (1 - (χ y : ℂ))) v = v - Mχ v := by
    apply SchwartzMap.ext
    intro y
    have hg : (fun y ↦ (1 - (χ y : ℂ))).HasTemperateGrowth :=
      (Function.HasTemperateGrowth.const (1 : ℂ)).sub hχgrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    change (1 - (χ y : ℂ)) • v y = v y - Mχ v y
    rw [show Mχ v y = (χ y : ℂ) • v y from
      SchwartzMap.smulLeftCLM_apply_apply hχgrowth v y, sub_smul, one_smul]
  have hDvalue : D u = A u - A (Mχ u) := by
    apply SchwartzMap.ext
    intro x
    rw [quantizeSchwartz_apply,
      quantize_offDiagonalSymbol 0 (ah z) (hah z) σ χ hσ hcσ hχ hcχ,
      hcomplement, ← hA, map_sub]
    change σ x • (A u x - A (Mχ u) x) = A u x - A (Mχ u) x
    by_cases hx : x ∈ tsupport a
    · rw [hσpoint x hx, one_smul]
    · have hzero : a x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hAzero (v : 𝓢(V, EuclideanSpace ℂ (Fin r))) : A v x = 0 := by
        rw [hA]
        simp [frequencyScaleSymbol, quantize, hzero]
      rw [hAzero, hAzero, sub_self, smul_zero]
  have herror : P (A u) - B u = Rop u + P (D u) := by
    rw [hRvalue, hDvalue, map_sub]
    abel
  -- Sum the complete reduction error and the uniformly bounded left image of the input tail.
  have hRnorm : ‖schwartzSobolevCoordinate s (Rop u)‖ ≤
      Cr * h * ‖schwartzSobolevCoordinate s u‖ := hCrb z u
  have hDnorm : ‖schwartzSobolevCoordinate s (D u)‖ ≤
      Cd * h * ‖schwartzSobolevCoordinate s u‖ := hCdb h hh hh₁ u
  have hPnorm := hCpb h hh hh₁ P hP (D u)
  rw [herror, schwartzSobolevCoordinate_add]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ Cr * h * ‖schwartzSobolevCoordinate s u‖ +
        Cp * ‖schwartzSobolevCoordinate s (D u)‖ := add_le_add hRnorm hPnorm
    _ ≤ Cr * h * ‖schwartzSobolevCoordinate s u‖ +
        Cp * (Cd * h * ‖schwartzSobolevCoordinate s u‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hDnorm hCp)
    _ = _ := by ring

end AtiyahSinger

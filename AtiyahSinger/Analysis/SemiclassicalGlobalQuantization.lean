/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Analysis.FrequencyScalingAmplitude
public import AtiyahSinger.Analysis.FrequencyScalingContinuity
public import AtiyahSinger.Analysis.GlobalSymbolComposition
public import AtiyahSinger.Analysis.Pseudolocal
public import AtiyahSinger.Analysis.QuantizationBounds
public import AtiyahSinger.Analysis.SemiclassicalComposition
public import AtiyahSinger.Analysis.SobolevCoordinateChange
public import AtiyahSinger.Analysis.SobolevMultiplication

import all AtiyahSinger.Analysis.CoordinateChange
import all AtiyahSinger.Analysis.SymbolCoordinateEstimates
import Mathlib.Tactic.Ring

/-!
# Quantitative bounds for the original localized quantization

Public module ID: M2295.

The actual first amplitude remainder retains a uniform factor of the positive frequency
scale. A fixed compact output support then converts these weighted derivative estimates
to estimates for the original quantization in its original Bessel Sobolev coordinates.
For nested cutoffs the off-diagonal symbol is exactly the negative of that same first
remainder. Every cutoff and Fourier normalization remains the one in the original operator.
The native finite presentation keeps the same scaled local symbols and sums the actual
full-symbol leading products. Its Sobolev norm bounds include every original fixed
chart, frame, cutoff and density transport. These bounds do not yet estimate a global
composition remainder.

Sources: Lawson and Michelsohn, Spin Geometry (SG), III.3.5, printed pp.180--182,
for compact amplitude reduction; SG III.3.8--3.10, printed pp.183--184, for the actual
two-sided cutoff action. Taylor, Pseudodifferential Operators (TA), II.6.1, pp.49--50,
supplies finite derivative operator estimates. The common positive-parameter bounds
are project supplements. No zero-parameter convergence or global index result is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff SchwartzMap

variable {n r q : ℕ}

-- The three nested amplitude derivative norms use the original amplitude inference depth.
set_option maxSynthPendingDepth 15 in
/-- Positive scaling gives a uniform small factor in the actual first amplitude remainder. -/
theorem IsAmplitude.exists_frequencyScale_remainder_bound {a : AmplitudeFunction n r q}
    (ha : IsAmplitude 0 a) (hc : HasCompactSupport (Function.uncurry a))
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ L, ∀ ξ,
      ‖symbolDerivative (amplitudeSymbol (frequencyScaleAmplitude t a) -
          (fun x ξ ↦ frequencyScaleAmplitude t a x x ξ)) i k x ξ‖ ≤
        C * t * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- Use the original amplitude's compact spatial support for every parameter.
  The extra frequency jet supplies the factor t before actual amplitude reduction. -/
  let T := {t : ℝ // 0 < t ∧ t ≤ 1}
  let family : T → AmplitudeFunction n r q := fun t ↦ frequencyScaleAmplitude t.val a
  let S := tsupport (Function.uncurry a)
  have hfamily (t : T) : IsAmplitude 0 (family t) :=
    ha.frequencyScale t.val t.property.1 t.property.2
  have hsupp (t : T) : tsupport (Function.uncurry (family t)) ⊆ S := by
    apply closure_minimal ?_ (isClosed_tsupport (Function.uncurry a))
    intro z hz
    by_contra hzS
    have hz0 : Function.uncurry a z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := Function.uncurry a) hzS
    apply hz
    funext ξ
    change a z.1 z.2 (t.val • ξ) = 0
    simpa only [Function.uncurry, Pi.zero_apply] using congrFun hz0 (t.val • ξ)
  have hbound : ∀ u v l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : T, ∀ x y,
      (x, y) ∈ S → ∀ ξ,
        ‖amplitudeDerivative (family t) u v (l + 1) x y ξ‖ ≤
          C * t.val * (1 + ‖ξ‖) ^ (-(l : ℝ)) := by
    intro u v l
    obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_derivative_bound S hc u v l
    exact ⟨C, hC, fun t x y hxy ξ ↦
      hCb t.val t.property.1 t.property.2 x y hxy ξ⟩
  obtain ⟨C, hC, hCb⟩ := exists_uniform_amplitudeSymbol_sub_diagonal_bound
    family hfamily S hc hsupp (fun t : T ↦ t.val) (fun t ↦ t.property.1.le)
    hbound L hL i k
  exact ⟨C, hC, fun t ht ht₁ x hx ξ ↦ hCb ⟨t, ht, ht₁⟩ x hx ξ⟩

/-- Common weighted symbol bounds control the actual operators with one common constant. -/
theorem exists_uniform_quantizeSchwartz_sobolev_bound
    {T : Type*} (a : T → SymbolFunction n r q) (ha : ∀ z, IsSymbol univ 0 (a z))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupp : ∀ z, tsupport (a z) ⊆ K) (w : T → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hbound : ∀ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L → ∀ i k : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z x, x ∈ L → ∀ ξ,
        ‖symbolDerivative (a z) i k x ξ‖ ≤ C * w z * (1 + ‖ξ‖) ^ (-(k : ℝ)))
    (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖schwartzSobolevCoordinate s
          (quantizeSchwartz 0 (a z) (ha z)
            (hK.of_isClosed_subset (isClosed_tsupport (a z)) (hsupp z)) u)‖ ≤
          C * w z * ‖schwartzSobolevCoordinate s u‖ := by
  /- Choose one auxiliary output plateau and its finite quantization seminorms
  before the family parameter. It is one on the common support and changes no operator. -/
  classical
  obtain ⟨δ, hδ, hcδ, hδU, hδone⟩ :=
    exists_compact_cutoff_one_near K univ hK isOpen_univ (subset_univ _)
  obtain ⟨J, c, hc⟩ := exists_quantizeSchwartz_zeroExtendedSymbol_seminorm_bound
    univ isOpen_univ 0 s δ hδ hcδ hδU
  let p (z : T) : symbolSpace univ isOpen_univ 0 r q := ⟨a z, ha z⟩
  have hseminorm (I : SymbolSeminormIndex (univ : Set (EuclideanSpace ℝ (Fin n)))) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z, symbolSeminorm isOpen_univ 0 I (p z) ≤ C * w z := by
    obtain ⟨C, hC, hCb⟩ := hbound I.compactSet I.isCompact I.spatialOrder I.frequencyOrder
    refine ⟨C, hC, ?_⟩
    intro z
    change symbolSeminormValue isOpen_univ 0 I (p z) ≤ C * w z
    by_cases hnonempty : I.compactSet.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hnonempty
      unfold symbolSeminormValue
      refine csSup_le ⟨_, x₀, hx₀, 0, rfl⟩ ?_
      rintro v ⟨x, hx, ξ, rfl⟩
      apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
      simpa only [p, zero_sub] using hCb z x hx ξ
    · have hempty := Set.not_nonempty_iff_eq_empty.mp hnonempty
      simp only [symbolSeminormValue, hempty, Set.mem_empty_iff_false, false_and,
        exists_false, Set.ofPred_false, Real.sSup_empty]
      exact mul_nonneg hC (hw z)
  choose C hC hCb using hseminorm
  let D : ℝ := ∑ I ∈ J, C I
  have hD : 0 ≤ D := Finset.sum_nonneg (fun I _ ↦ hC I)
  have hfinite (z : T) : (J.sup (symbolSeminorm isOpen_univ 0)) (p z) ≤ D * w z := by
    apply Seminorm.finset_sup_apply_le
    · exact mul_nonneg hD (hw z)
    · intro I hI
      have hsum : C I ≤ D := Finset.single_le_sum (fun L _ ↦ hC L) hI
      exact (hCb I z).trans (mul_le_mul_of_nonneg_right hsum (hw z))
  have hcut (z : T) : zeroExtendedSymbol univ δ (a z) = a z := by
    funext x ξ
    by_cases hx : x ∈ K
    · have hδx : δ x = 1 := interior_subset (s := {y | δ y = 1}) (hδone hx)
      simp only [zeroExtendedSymbol, Set.mem_univ, ↓reduceIte, hδx,
        Complex.ofReal_one, one_smul]
    · have hz0 : a z x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx0 ↦ hx (hsupp z hx0))
      simp only [zeroExtendedSymbol, Set.mem_univ, ↓reduceIte, hz0, Pi.zero_apply,
        smul_zero]
  refine ⟨(c : ℝ) * D, mul_nonneg c.coe_nonneg hD, ?_⟩
  intro z u
  have hquant := hc (p z) u
  have hsame :
      quantizeSchwartz 0 (zeroExtendedSymbol univ δ (a z))
          (isSymbol_zeroExtendedSymbol univ isOpen_univ 0 δ hδ hcδ hδU (a z) (ha z))
          (hasCompactSupport_zeroExtendedSymbol univ δ (a z) hcδ) =
        quantizeSchwartz 0 (a z) (ha z)
          (hK.of_isClosed_subset (isClosed_tsupport (a z)) (hsupp z)) := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    calc
      _ = quantize (zeroExtendedSymbol univ δ (a z)) v x :=
        quantizeSchwartz_apply 0 (zeroExtendedSymbol univ δ (a z))
          (isSymbol_zeroExtendedSymbol univ isOpen_univ 0 δ hδ hcδ hδU (a z) (ha z))
          (hasCompactSupport_zeroExtendedSymbol univ δ (a z) hcδ) v x
      _ = quantize (a z) v x := by rw [hcut z]
      _ = _ := (quantizeSchwartz_apply 0 (a z) (ha z)
        (hK.of_isClosed_subset (isClosed_tsupport (a z)) (hsupp z)) v x).symm
  have hquant' :
      ‖schwartzSobolevCoordinate s
        (quantizeSchwartz 0 (a z) (ha z)
          (hK.of_isClosed_subset (isClosed_tsupport (a z)) (hsupp z)) u)‖ ≤
        (c : ℝ) * (J.sup (symbolSeminorm isOpen_univ 0)) (p z) *
          ‖schwartzSobolevCoordinate s u‖ := by
    simpa only [p, sub_zero, hsame] using hquant
  exact hquant'.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hfinite z) c.coe_nonneg) (norm_nonneg _)).trans_eq
      (by ring))

/-- A plateau on the output support gives the small factor in the actual off-diagonal symbol. -/
theorem IsSymbol.exists_frequencyScale_offDiagonal_bound {p : SymbolFunction n r q}
    (hp : IsSymbol univ 0 p) (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hone : tsupport χ ⊆ {x | ρ x = 1})
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ L, ∀ ξ,
      ‖symbolDerivative (offDiagonalSymbol χ ρ (frequencyScaleSymbol t p)) i k x ξ‖ ≤
        C * t * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- Scale the compact two-sided amplitude, rather than a noncompact complementary
  input cutoff. Its actual diagonal is χp_t, so the original off-diagonal symbol is
  exactly the negative of the actual first amplitude remainder. -/
  let a := cutoffAmplitude χ ρ p
  have ha : IsAmplitude 0 a := isAmplitude_cutoffAmplitude 0 p hp χ ρ hχ hρ
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_cutoffAmplitude p χ ρ hcχ hcρ
  obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_remainder_bound hca L hL i k
  have hdiag (t : ℝ) : (fun x ξ ↦ frequencyScaleAmplitude t a x x ξ) =
      (fun x ξ ↦ χ x • frequencyScaleSymbol t p x ξ) := by
    funext x ξ
    by_cases hx : x ∈ tsupport χ
    · have hρx : ρ x = 1 := hone hx
      simp only [frequencyScaleAmplitude, a, cutoffAmplitude, frequencyScaleSymbol, hρx,
        mul_one]
    · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [frequencyScaleAmplitude, a, cutoffAmplitude, frequencyScaleSymbol, hχx,
        zero_mul, zero_smul]
  have heq (t : ℝ) : offDiagonalSymbol χ ρ (frequencyScaleSymbol t p) =
      -(amplitudeSymbol (frequencyScaleAmplitude t a) -
        (fun x ξ ↦ frequencyScaleAmplitude t a x x ξ)) := by
    rw [hdiag]
    change (fun x ξ ↦ χ x • frequencyScaleSymbol t p x ξ) -
        amplitudeSymbol (frequencyScaleAmplitude t a) =
      -(amplitudeSymbol (frequencyScaleAmplitude t a) -
        (fun x ξ ↦ χ x • frequencyScaleSymbol t p x ξ))
    exact (neg_sub _ _).symm
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ x hx ξ
  rw [heq]
  let R : SymbolFunction n r q := amplitudeSymbol (frequencyScaleAmplitude t a) -
    (fun x ξ ↦ frequencyScaleAmplitude t a x x ξ)
  have hnorm : ‖symbolDerivative (-R) i k x ξ‖ = ‖symbolDerivative R i k x ξ‖ := by
    unfold symbolDerivative
    have hfreq (y : EuclideanSpace ℝ (Fin n)) :
        iteratedFDeriv ℝ k ((-R) y) ξ = -iteratedFDeriv ℝ k (R y) ξ :=
      iteratedFDeriv_neg_apply
    simp_rw [hfreq]
    change ‖iteratedFDeriv ℝ i (-(fun y ↦ iteratedFDeriv ℝ k (R y) ξ)) x‖ = _
    rw [iteratedFDeriv_neg_apply, norm_neg]
  change ‖symbolDerivative (-R) i k x ξ‖ ≤ _
  rw [hnorm]
  exact hCb t ht ht₁ x hx ξ

/-- The actual nested-cutoff error has one common small bound in the original Sobolev norm. -/
theorem IsSymbol.exists_frequencyScale_offDiagonal_sobolev_bound
    {p : SymbolFunction n r q} (hp : IsSymbol univ 0 p)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hone : tsupport χ ⊆ interior {x | ρ x = 1}) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht₁ : t ≤ 1,
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖schwartzSobolevCoordinate s
          (quantizeSchwartz 0 (offDiagonalSymbol χ ρ (frequencyScaleSymbol t p))
            (isSmoothingSymbol_offDiagonalSymbol 0 (frequencyScaleSymbol t p)
              (hp.frequencyScale t ht ht₁) χ ρ hχ hcχ hρ hcρ hone 0)
            (hasCompactSupport_offDiagonalSymbol χ ρ (frequencyScaleSymbol t p) hcχ) u)‖ ≤
          C * t * ‖schwartzSobolevCoordinate s u‖ := by
  /- The original output cutoff supplies one fixed compact support for every t.
  Uniform mixed estimates control the original operator without dropping its input tail. -/
  let T := {t : ℝ // 0 < t ∧ t ≤ 1}
  let family : T → SymbolFunction n r q :=
    fun t ↦ offDiagonalSymbol χ ρ (frequencyScaleSymbol t.val p)
  have hfamily (t : T) : IsSymbol univ 0 (family t) :=
    isSmoothingSymbol_offDiagonalSymbol 0 (frequencyScaleSymbol t.val p)
      (hp.frequencyScale t.val t.property.1 t.property.2) χ ρ hχ hcχ hρ hcρ hone 0
  have hsupp (t : T) : tsupport (family t) ⊆ tsupport χ := by
    apply closure_minimal ?_ (isClosed_tsupport χ)
    intro x hx
    by_contra hxχ
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
    apply hx
    funext ξ
    simp [family, offDiagonalSymbol, cutoffSymbol, amplitudeSymbol, cutoffAmplitude, hχx]
  have hpoint : tsupport χ ⊆ {x | ρ x = 1} := hone.trans interior_subset
  have hbound : ∀ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L → ∀ i k : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : T, ∀ x, x ∈ L → ∀ ξ,
        ‖symbolDerivative (family t) i k x ξ‖ ≤
          C * t.val * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    intro L hL i k
    obtain ⟨C, hC, hCb⟩ := hp.exists_frequencyScale_offDiagonal_bound
      χ ρ hχ hcχ hρ hcρ hpoint L hL i k
    exact ⟨C, hC, fun t x hx ξ ↦ hCb t.val t.property.1 t.property.2 x hx ξ⟩
  obtain ⟨C, hC, hCb⟩ := exists_uniform_quantizeSchwartz_sobolev_bound
    family hfamily (tsupport χ) hcχ hsupp (fun t : T ↦ t.val)
    (fun t ↦ t.property.1.le) hbound s
  exact ⟨C, hC, fun t ht ht₁ u ↦ hCb ⟨t, ht, ht₁⟩ u⟩

/-- Frequency scaling keeps the original compact spatial-pair support as a common control. -/
theorem hasCompactSupport_frequencyScaleAmplitude (t : ℝ) {a : AmplitudeFunction n r q}
    (hc : HasCompactSupport (Function.uncurry a)) :
    HasCompactSupport (Function.uncurry (frequencyScaleAmplitude t a)) := by
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ (isClosed_tsupport (Function.uncurry a))
  intro z hz
  by_contra hzS
  have hz0 : Function.uncurry a z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry a) hzS
  apply hz
  funext ξ
  change a z.1 z.2 (t • ξ) = 0
  simpa only [Function.uncurry, Pi.zero_apply] using congrFun hz0 (t • ξ)

/-- A zero diagonal gives a small bound for the actual scaled amplitude operator. -/
theorem IsAmplitude.exists_frequencyScale_sobolev_bound_of_diag_eq_zero
    {a : AmplitudeFunction n r q} (ha : IsAmplitude 0 a)
    (hc : HasCompactSupport (Function.uncurry a))
    (hdiag : ∀ x ξ, a x x ξ = 0) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht₁ : t ≤ 1,
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖schwartzSobolevCoordinate s
          (amplitudeOperator 0 (frequencyScaleAmplitude t a)
            (ha.frequencyScale t ht ht₁) (hasCompactSupport_frequencyScaleAmplitude t hc) u)‖ ≤
          C * t * ‖schwartzSobolevCoordinate s u‖ := by
  /- A vanishing original diagonal remains zero after frequency scaling. Thus the
  actual reduced symbol itself is the first remainder. Its original compact first
  projection is a common output support, and exact reduction retains the same operator. -/
  let T := {t : ℝ // 0 < t ∧ t ≤ 1}
  let family : T → SymbolFunction n r q :=
    fun t ↦ amplitudeSymbol (frequencyScaleAmplitude t.val a)
  let K := Prod.fst '' tsupport (Function.uncurry a)
  have hK : IsCompact K := hc.image continuous_fst
  have hscaled (t : T) : IsAmplitude 0 (frequencyScaleAmplitude t.val a) :=
    ha.frequencyScale t.val t.property.1 t.property.2
  have hcompact (t : T) : HasCompactSupport
      (Function.uncurry (frequencyScaleAmplitude t.val a)) :=
    hasCompactSupport_frequencyScaleAmplitude t.val hc
  have hfamily (t : T) : IsSymbol univ 0 (family t) :=
    isSymbol_amplitudeSymbol 0 _ (hscaled t) (hcompact t)
  have hsupp (t : T) : tsupport (family t) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hzero (y : EuclideanSpace ℝ (Fin n)) : a x y = 0 :=
      image_eq_zero_of_notMem_tsupport (f := Function.uncurry a)
        (fun h ↦ hxK ⟨(x, y), h, rfl⟩)
    apply hx
    funext ξ
    simp [family, amplitudeSymbol, frequencyScaleAmplitude, hzero]
  have hbound : ∀ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L → ∀ i k : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : T, ∀ x, x ∈ L → ∀ ξ,
        ‖symbolDerivative (family t) i k x ξ‖ ≤
          C * t.val * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    intro L hL i k
    obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_remainder_bound hc L hL i k
    refine ⟨C, hC, ?_⟩
    intro t x hx ξ
    have hd : (fun x ξ ↦ frequencyScaleAmplitude t.val a x x ξ) = 0 := by
      funext y η
      exact hdiag y (t.val • η)
    simpa only [family, hd, sub_zero] using
      hCb t.val t.property.1 t.property.2 x hx ξ
  obtain ⟨C, hC, hCb⟩ := exists_uniform_quantizeSchwartz_sobolev_bound
    family hfamily K hK hsupp (fun t : T ↦ t.val) (fun t ↦ t.property.1.le) hbound s
  have hsame (t : T) :
      quantizeSchwartz 0 (family t) (hfamily t)
          (hK.of_isClosed_subset (isClosed_tsupport (family t)) (hsupp t)) =
        amplitudeOperator 0 (frequencyScaleAmplitude t.val a)
          (hscaled t) (hcompact t) := by
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    calc
      _ = quantize (family t) u x := quantizeSchwartz_apply 0 (family t) (hfamily t)
        (hK.of_isClosed_subset (isClosed_tsupport (family t)) (hsupp t)) u x
      _ = amplitudeApply (frequencyScaleAmplitude t.val a) u x :=
        congrFun (quantize_amplitudeSymbol 0 _ (hscaled t) (hcompact t) u) x
      _ = _ := (amplitudeOperator_apply 0 _ (hscaled t) (hcompact t) u x).symm
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ u
  simpa only [hsame] using hCb ⟨t, ht, ht₁⟩ u

/-- Fixed bounded source and target maps retain the original weighted Sobolev bound. -/
private theorem sobolev_norm_comp_le_of_bounds
    {T : Type*} {k l : ℕ}
    (P : T → 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (R : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin l)))
    (L : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin k)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (w : T → ℝ) (hw : ∀ z, 0 ≤ w z) (C : ℝ) (hC : 0 ≤ C)
    (Co Ci : ℝ) (hCo : 0 ≤ Co) (_hCi : 0 ≤ Ci) (s : ℝ)
    (hP : ∀ z u, ‖schwartzSobolevCoordinate s (P z u)‖ ≤
      C * w z * ‖schwartzSobolevCoordinate s u‖)
    (hR : ∀ v, ‖schwartzSobolevCoordinate s (R v)‖ ≤
      Co * ‖schwartzSobolevCoordinate s v‖)
    (hL : ∀ u, ‖schwartzSobolevCoordinate s (L u)‖ ≤
      Ci * ‖schwartzSobolevCoordinate s u‖) :
    ∀ z u, ‖schwartzSobolevCoordinate s (R (P z (L u)))‖ ≤
      (Co * C * Ci) * w z * ‖schwartzSobolevCoordinate s u‖ := by
  intro z u
  calc
    _ ≤ Co * ‖schwartzSobolevCoordinate s (P z (L u))‖ := hR _
    _ ≤ Co * (C * w z * ‖schwartzSobolevCoordinate s (L u)‖) :=
      mul_le_mul_of_nonneg_left (hP z (L u)) hCo
    _ ≤ Co * (C * w z * (Ci * ‖schwartzSobolevCoordinate s u‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hL u) (mul_nonneg hC (hw z))) hCo
    _ = _ := by ring

/-- The original fixed coordinate pushforward retains one common weighted operator bound. -/
theorem exists_uniform_coordinatePushforward_sobolev_bound
    {T : Type*}
    (P : T → 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (w : T → ℝ) (hw : ∀ z, 0 ≤ w z) (C : ℝ) (hC : 0 ≤ C)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (s : ℝ)
    (hP : ∀ z u, ‖schwartzSobolevCoordinate s (P z u)‖ ≤
      C * w z * ‖schwartzSobolevCoordinate s u‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z u,
      ‖schwartzSobolevCoordinate s
        (coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV (P z) u)‖ ≤
        D * w z * ‖schwartzSobolevCoordinate s u‖ := by
  /- The source and target cutoffs and coordinate maps remain fixed. Apply their
  original Sobolev bounds on the two sides of the actual family operator. This
  transports the actual smooth-kernel tail as well as any other bounded remainder. -/
  obtain ⟨Ci, hCi, hinput⟩ := exists_norm_cutoffPullback_sobolev_le (r := r)
    e he hψ χ hχ hcχ hχU s
  obtain ⟨Co, hCo, houtput⟩ := exists_norm_cutoffPullback_sobolev_le (r := q)
    e.symm hψ he ρ hρ hcρ hρV s
  let L : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
    cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχU
  let R : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) :=
    cutoffPullbackCLM e.target e.open_target e.symm hψ ρ hρ hcρ hρV
  refine ⟨Co * C * Ci, mul_nonneg (mul_nonneg hCo hC) hCi, ?_⟩
  intro z u
  change ‖schwartzSobolevCoordinate s (R (P z (L u)))‖ ≤ _
  exact sobolev_norm_comp_le_of_bounds P R L w hw C hC Co Ci hCo hCi s
    hP houtput hinput z u

/-- The original fixed input and output matrix multipliers retain a common weighted bound. -/
theorem exists_uniform_matrixMultiplier_comp_sobolev_bound
    {T : Type*} {k l : ℕ}
    (P : T → 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (w : T → ℝ) (hw : ∀ z, 0 ≤ w z) (C : ℝ) (hC : 0 ≤ C)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B) (s : ℝ)
    (hP : ∀ z u, ‖schwartzSobolevCoordinate s (P z u)‖ ≤
      C * w z * ‖schwartzSobolevCoordinate s u‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z u,
      ‖schwartzSobolevCoordinate s
        ((matrixMultiplierCLM A hA hcA).comp
          ((P z).comp (matrixMultiplierCLM B hB hcB)) u)‖ ≤
        D * w z * ‖schwartzSobolevCoordinate s u‖ := by
  /- Both original frame multipliers are fixed smooth compact functions. Their
  actual matrix action retains the original multiplication order and both ranks. -/
  obtain ⟨Co, hCo, houtput⟩ := exists_norm_matrixMultiplier_sobolev_le A hA hcA s
  obtain ⟨Ci, hCi, hinput⟩ := exists_norm_matrixMultiplier_sobolev_le B hB hcB s
  refine ⟨Co * C * Ci, mul_nonneg (mul_nonneg hCo hC) hCi, ?_⟩
  intro z u
  exact sobolev_norm_comp_le_of_bounds P
    (matrixMultiplierCLM A hA hcA) (matrixMultiplierCLM B hB hcB)
    w hw C hC Co Ci hCo hCi s hP houtput hinput z u

/-- Every actual operator with the scaled first-remainder symbol has its common small bound. -/
theorem IsAmplitude.exists_frequencyScale_remainder_operator_bound
    {a : AmplitudeFunction n r q} (ha : IsAmplitude 0 a)
    (hc : HasCompactSupport (Function.uncurry a)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      (∀ u x, P u x = quantize
        (amplitudeSymbol (frequencyScaleAmplitude t a) -
          (fun x ξ ↦ frequencyScaleAmplitude t a x x ξ)) u x) →
      ∀ u, ‖schwartzSobolevCoordinate s (P u)‖ ≤
        C * t * ‖schwartzSobolevCoordinate s u‖ := by
  /- The actual remainder has the next symbol order, and its support stays in
  the compact first projection of the original amplitude support. Quantization
  bounds that exact symbol. An operator satisfying its original pointwise action
  is equal to this quantization, so no different remainder operator is substituted. -/
  let T := {t : ℝ // 0 < t ∧ t ≤ 1}
  let family : T → SymbolFunction n r q := fun t ↦
    amplitudeSymbol (frequencyScaleAmplitude t.val a) -
      (fun x ξ ↦ frequencyScaleAmplitude t.val a x x ξ)
  let K := Prod.fst '' tsupport (Function.uncurry a)
  have hK : IsCompact K := hc.image continuous_fst
  have hfamily (t : T) : IsSymbol univ 0 (family t) := by
    have hnext : IsSymbol univ (-1) (family t) := by
      simpa only [family, Nat.cast_one, zero_sub, Finset.sum_range_one,
        amplitudeExpansionTerm_zero] using
        (hasSymbolExpansion_amplitudeSymbol 0 (frequencyScaleAmplitude t.val a)
          (ha.frequencyScale t.val t.property.1 t.property.2)
          (hasCompactSupport_frequencyScaleAmplitude t.val hc) 1)
    exact hnext.mono (show (-1 : ℝ) ≤ 0 by norm_num)
  have hsupp (t : T) : tsupport (family t) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hzero (y : EuclideanSpace ℝ (Fin n)) : a x y = 0 :=
      image_eq_zero_of_notMem_tsupport (f := Function.uncurry a)
        (fun h ↦ hxK ⟨(x, y), h, rfl⟩)
    apply hx
    funext ξ
    simp [family, amplitudeSymbol, frequencyScaleAmplitude, hzero]
  have hbound : ∀ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L → ∀ i k : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : T, ∀ x, x ∈ L → ∀ ξ,
        ‖symbolDerivative (family t) i k x ξ‖ ≤
          C * t.val * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    intro L hL i k
    obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_remainder_bound hc L hL i k
    exact ⟨C, hC, fun t x hx ξ ↦ hCb t.val t.property.1 t.property.2 x hx ξ⟩
  obtain ⟨C, hC, hCb⟩ := exists_uniform_quantizeSchwartz_sobolev_bound
    family hfamily K hK hsupp (fun t : T ↦ t.val) (fun t ↦ t.property.1.le) hbound s
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ P hP u
  let z : T := ⟨t, ht, ht₁⟩
  have hsame :
      quantizeSchwartz 0 (family z) (hfamily z)
        (hK.of_isClosed_subset (isClosed_tsupport (family z)) (hsupp z)) = P := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    exact (quantizeSchwartz_apply 0 (family z) (hfamily z)
      (hK.of_isClosed_subset (isClosed_tsupport (family z)) (hsupp z)) v x).trans (hP v x).symm
  have h := hCb z u
  rw [hsame] at h
  exact h

/-- The actual coordinate amplitude keeps the small remainder relative to its cotangent symbol. -/
theorem IsSymbol.exists_frequencyScale_coordinateAmplitude_remainder_bound
    {p : SymbolFunction n r q} (hp : IsSymbol univ 0 p)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (hseg : ∀ z ∈ W, segment ℝ z.2 z.1 ⊆ e.target)
    (hinv : ∀ z ∈ W, (averagedFDeriv e.symm z.1 z.2).IsInvertible)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχW : tsupport χ ⊆ W)
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ L, ∀ ξ,
      ‖symbolDerivative
        (amplitudeSymbol (coordinateAmplitude e χ (frequencyScaleSymbol t p)) -
          (fun x ξ ↦ χ (x, x) • cotangentSymbol e (frequencyScaleSymbol t p) x ξ)) i k x ξ‖ ≤
        C * t * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  /- First transform the unscaled symbol using the original fixed frequency map
  and absolute Jacobians. Linearity commutes with frequency scaling. On the
  diagonal the same Jacobians cancel; outside the chart the supported cutoff is zero. -/
  let a := coordinateAmplitude e χ p
  have ha : IsAmplitude 0 a := isAmplitude_coordinateAmplitude e he hψ 0 p
    (hp.restrict (subset_univ _)) W hW hseg hinv χ hχ hcχ hχW
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_coordinateAmplitude e χ p hcχ
  have hscale (t : ℝ) : coordinateAmplitude e χ (frequencyScaleSymbol t p) =
      frequencyScaleAmplitude t a := by
    funext x y ξ
    change (χ (x, y) * coordinateJacobianFactor e x y) •
        p (e.symm x) (t • coordinateFrequencyChange e x y ξ) =
      (χ (x, y) * coordinateJacobianFactor e x y) •
        p (e.symm x) (coordinateFrequencyChange e x y (t • ξ))
    rw [(coordinateFrequencyChange e x y).map_smul t ξ]
  have hdiag (t : ℝ) : (fun x ξ ↦ frequencyScaleAmplitude t a x x ξ) =
      (fun x ξ ↦ χ (x, x) • cotangentSymbol e (frequencyScaleSymbol t p) x ξ) := by
    rw [← hscale]
    funext x ξ
    by_cases hx : x ∈ e.target
    · exact coordinateAmplitude_diag e he hψ χ (frequencyScaleSymbol t p) x ξ hx
    · have hχx : χ (x, x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hx (hseg (x, x) (hχW h) (right_mem_segment ℝ x x)))
      simp only [coordinateAmplitude, hχx, zero_mul, zero_smul]
  obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_remainder_bound hca L hL i k
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ x hx ξ
  rw [hscale, ← hdiag]
  exact hCb t ht ht₁ x hx ξ

/-- Fixed spatial matrix factors retain the actual small remainder of their frame amplitude. -/
theorem IsSymbol.exists_frequencyScale_matrixAmplitude_remainder_bound
    {k l : ℕ} {p : SymbolFunction n r q} (hp : IsSymbol univ 0 p)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B)
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ L, ∀ ξ,
      ‖symbolDerivative
        (amplitudeSymbol (matrixAmplitude A B (frequencyScaleSymbol t p)) -
          matrixSymbol A B (frequencyScaleSymbol t p)) i j x ξ‖ ≤
        C * t * (1 + ‖ξ‖) ^ (-(j : ℝ)) := by
  /- The original input and output matrices do not depend on frequency. Thus
  scaling the original matrix amplitude is exactly the amplitude of the scaled
  symbol, and its actual diagonal is the original matrixSymbol in the same order. -/
  let a := matrixAmplitude A B p
  have ha : IsAmplitude 0 a := isAmplitude_matrixAmplitude 0 p hp A B hA hB
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_matrixAmplitude A B p hcA hcB
  obtain ⟨C, hC, hCb⟩ := ha.exists_frequencyScale_remainder_bound hca L hL i j
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ x hx ξ
  change ‖symbolDerivative (amplitudeSymbol (frequencyScaleAmplitude t a) -
      (fun x ξ ↦ frequencyScaleAmplitude t a x x ξ)) i j x ξ‖ ≤ _
  exact hCb t ht ht₁ x hx ξ


/-! ## The actual finite native quantization presentation -/

section NativeQuantization

open Bundle MeasureTheory
open scoped Manifold

-- The native chart/frame and seminorm transports use the original quantization inference depth.
set_option maxSynthPendingDepth 15

private theorem exists_frequencyScale_all_derivative_bound
    {U : Set (EuclideanSpace ℝ (Fin n))} {p : SymbolFunction n r q}
    (hp : IsSymbol U 0 p) (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U)
    (hK : IsCompact K) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ K, ∀ ξ,
      ‖symbolDerivative (frequencyScaleSymbol t p) i k x ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := hp.2 K hKU hK i k
  refine ⟨C, hC, ?_⟩
  intro t ht ht₁ x hx ξ
  -- The same original mixed derivative contributes t^k through the linear frequency map.
  have hder : symbolDerivative (frequencyScaleSymbol t p) i k x ξ =
      t ^ k • symbolDerivative p i k x (t • ξ) :=
    mixed_iteratedFDeriv_frequency_smul p t ht.ne' i k x ξ
  have hratio : t ^ k / (1 + t * ‖ξ‖) ^ k ≤ 1 / (1 + ‖ξ‖) ^ k := by
    apply (div_le_div_iff₀ (pow_pos (by positivity) k) (pow_pos (by positivity) k)).mpr
    have hcomparison := pow_le_pow_left₀
      (show 0 ≤ t * (1 + ‖ξ‖) by positivity)
      (show t * (1 + ‖ξ‖) ≤ 1 + t * ‖ξ‖ by nlinarith) k
    simpa only [mul_pow, one_mul] using hcomparison
  have hscaled : ‖symbolDerivative p i k x (t • ξ)‖ ≤
      C * (1 + ‖t • ξ‖) ^ (-(k : ℝ)) := by
    simpa only [zero_sub] using hbound x hx (t • ξ)
  calc
    _ = t ^ k * ‖symbolDerivative p i k x (t • ξ)‖ := by
      rw [hder, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.le k)]
    _ ≤ t ^ k * (C * (1 + ‖t • ξ‖) ^ (-(k : ℝ))) :=
      mul_le_mul_of_nonneg_left hscaled (pow_nonneg ht.le k)
    _ = C * (t ^ k / (1 + t * ‖ξ‖) ^ k) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
    _ ≤ C * (1 / (1 + ‖ξ‖) ^ k) := mul_le_mul_of_nonneg_left hratio hC
    _ = C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The actual local symbol of a fixed patch scales the original frequency variable exactly. -/
theorem QuantizationPatch.localSymbol_frequencyScale
    (Q : QuantizationPatch (n := n) (r := r) (q := q) E F)
    (a : GlobalSymbolFunction (n := n) E F) (t : ℝ) :
    Q.localSymbol (frequencyScaleGlobalSymbol t a) = frequencyScaleSymbol t (Q.localSymbol a) := by
  let := Q.input.frame_mem_atlas
  let := Q.output.frame_mem_atlas
  change zeroExtendedSymbol
      (symbolChartDomain E F Q.chart Q.input.frame Q.output.frame) Q.output.cutoff
      (globalSymbolInChart E F (frequencyScaleGlobalSymbol t a)
        Q.chart Q.input.frame Q.output.frame) = _
  rw [globalSymbolInChart_frequencyScale]
  funext x ξ
  simp only [QuantizationPatch.localSymbol, zeroExtendedSymbol, frequencyScaleSymbol]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- The actual full symbols of all original quantization pieces sum to the input symbol. -/
theorem QuantizationPresentation.sum_globalSymbolFunction_toPiece
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F) {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (∑ j, ((C.patch j).toPiece a).globalSymbolFunction) = a.val := by
  classical
  funext x ξ
  -- Both output cutoffs have already cancelled on the same original input support.
  simp only [Finset.sum_apply, QuantizationPatch.globalSymbolFunction_toPiece]
  rw [← Finset.sum_smul]
  have hweight : (∑ j, ((C.patch j).weight x : ℂ)) = 1 := by
    exact_mod_cast C.sum_weight x
  rw [hweight, one_smul]

section ThreeBundles

variable {k : ℕ} {G : M → Type*}
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin k)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin k)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin k)) G]
  [IsSmoothComplexBundle (n := n) (r := k) G]

/-- Every pair's actual leading full symbol sums to the original fiberwise product. -/
theorem QuantizationPresentation.sum_globalSymbolFunction_comp_toPiece
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := k) F G) {l m : ℝ}
    (b : globalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (∑ i, ∑ j, globalSymbolComp ((D.patch i).toPiece b).globalSymbolFunction
      ((C.patch j).toPiece a).globalSymbolFunction) = globalSymbolComp b.val a.val := by
  classical
  -- Keep the actual middle fiber and multiplication order before using the two finite partitions.
  calc
    _ = globalSymbolComp (∑ i, ((D.patch i).toPiece b).globalSymbolFunction)
        (∑ j, ((C.patch j).toPiece a).globalSymbolFunction) := by
      funext x ξ
      apply ContinuousLinearMap.ext
      intro v
      simp only [globalSymbolComp, Finset.sum_apply, sum_apply,
        ContinuousLinearMap.comp_apply, map_sum]
      exact Finset.sum_comm
    _ = _ := by
      rw [D.sum_globalSymbolFunction_toPiece b, C.sum_globalSymbolFunction_toPiece a]

end ThreeBundles

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] globalSymbolTopology
  GlobalSymbolSeminormIndex.input_mem_atlas GlobalSymbolSeminormIndex.output_mem_atlas

/-- All positive contractions of one symbol have a common norm bound in the original quantizer. -/
theorem QuantizationPresentation.exists_uniform_sobolevQuantization_frequencyScale_bound
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (s : ℝ)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht₁ : t ≤ 1,
      ‖C.sobolevQuantizationCLM μ A B s 0
        (frequencyScaleGlobalSymbolSpace a t ht ht₁)‖ ≤ K := by
  /- Choose the original finite source seminorms and every original symbol bound
  before the parameter. Fixed chart/frame/cutoff and Sobolev transports are already
  included in the actual quantization estimate; no zero endpoint is used. -/
  classical
  obtain ⟨J, c, hc⟩ := C.exists_sobolevQuantization_seminorm_bound μ A B s 0
  have hseminorm (I : GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht₁ : t ≤ 1,
        globalSymbolSeminorm E F 0 I (frequencyScaleGlobalSymbolSpace a t ht ht₁) ≤ K := by
    let hU := isOpen_symbolChartDomain E F I.chart I.inputFrame I.outputFrame
    obtain ⟨K, hK, hKb⟩ := exists_frequencyScale_all_derivative_bound
      (a.property I.chart I.mem_atlas I.inputFrame I.outputFrame)
      I.localIndex.compactSet I.localIndex.subset_domain I.localIndex.isCompact
      I.localIndex.spatialOrder I.localIndex.frequencyOrder
    refine ⟨K, hK, ?_⟩
    intro t ht ht₁
    change symbolSeminormValue hU 0 I.localIndex _ ≤ K
    by_cases hnonempty : I.localIndex.compactSet.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hnonempty
      unfold symbolSeminormValue
      refine csSup_le ⟨_, x₀, hx₀, 0, rfl⟩ ?_
      rintro v ⟨x, hx, ξ, rfl⟩
      apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
      simpa only [globalSymbolInChartLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        globalSymbolInChartSpace, Subtype.coe_mk, frequencyScaleGlobalSymbolSpace,
        globalSymbolInChart_frequencyScale, zero_sub]
        using hKb t ht ht₁ x hx ξ
    · have hempty := Set.not_nonempty_iff_eq_empty.mp hnonempty
      simp only [symbolSeminormValue, hempty, Set.mem_empty_iff_false, false_and,
        exists_false, Set.ofPred_false, Real.sSup_empty]
      exact hK
  choose K hK hKb using hseminorm
  let H : ℝ := ∑ I ∈ J, K I
  have hH : 0 ≤ H := Finset.sum_nonneg (fun I _ ↦ hK I)
  refine ⟨(c : ℝ) * H, mul_nonneg c.coe_nonneg hH, ?_⟩
  intro t ht ht₁
  have hfinite : (J.sup (globalSymbolSeminorm E F 0))
      (frequencyScaleGlobalSymbolSpace a t ht ht₁) ≤ H := by
    apply Seminorm.finset_sup_apply_le hH
    intro I hI
    exact (hKb I t ht ht₁).trans (Finset.single_le_sum (fun L _ ↦ hK L) hI)
  exact (hc (frequencyScaleGlobalSymbolSpace a t ht ht₁)).trans
    (mul_le_mul_of_nonneg_left hfinite c.coe_nonneg)

end NativeQuantization

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Amplitude
public import AtiyahSinger.Analysis.LocalQuantization

/-!
# Two-sided cutoffs and compact operator support

Public module ID: M1041.

D05/A02: SG Corollary 3.8, (3.9), and the unnumbered support definition on p.183.
The original symbol only needs local spatial estimates, with no compact x support.
The two real smooth cutoffs give compact support in both spatial variables.
`HasOperatorSupport` records both output support and annihilation of disjoint inputs.
It is a predicate on an actual continuous Schwartz operator, not a symbol support condition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap

variable {n r q : ℕ}

/-- SG's two support conditions, extended from compact tests to Schwartz inputs. -/
def HasOperatorSupport (K : Set (EuclideanSpace ℝ (Fin n)))
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) : Prop :=
  (∀ u, tsupport (P u) ⊆ K) ∧
    ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
      Disjoint (tsupport u) K → P u = 0

/-- The amplitude of χ₁ P χ₂, with χ₁ on the output and χ₂ on the input. -/
def cutoffAmplitude (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : AmplitudeFunction n r q :=
  fun x y ξ ↦ (χ₁ x * χ₂ y) • p x ξ

/-- The exact reduced left symbol of the two-sided cutoff operator. -/
def cutoffSymbol (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : SymbolFunction n r q :=
  amplitudeSymbol (cutoffAmplitude χ₁ χ₂ p)

/-- Multiplying by smooth spatial cutoffs preserves the amplitude order. -/
theorem isAmplitude_cutoffAmplitude (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂) :
    IsAmplitude m (cutoffAmplitude χ₁ χ₂ p) := by
  /- Apply the product rule to the two scalar factors and p. On each compact pair
  set, all cutoff derivatives are bounded and the x projection is compact.
  Only derivatives in frequency lower the order, exactly as in the symbol estimates.
  Compact support of the original symbol is not used in this argument. -/
  -- The product cutoff is smooth on the original pair of spatial variables.
  exact isAmplitude_localizedAmplitude m p hp
    (fun z ↦ χ₁ z.1 * χ₂ z.2) ((hχ₁.comp contDiff_fst).mul (hχ₂.comp contDiff_snd))

/-- The cutoffs supply uniform compact spatial support, even when p has no compact support. -/
theorem hasCompactSupport_cutoffAmplitude (p : SymbolFunction n r q)
    (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : HasCompactSupport χ₁) (hχ₂ : HasCompactSupport χ₂) :
    HasCompactSupport (Function.uncurry (cutoffAmplitude χ₁ χ₂ p)) := by
  /- The amplitude vanishes outside the product of the two cutoff supports for
  every frequency. Its closed spatial support lies in that compact product.
  Thus no frequency-dependent support or growth condition on p is needed here. -/
  -- The original uniform support is controlled by the compact product of both cutoff supports.
  apply (hχ₁.prod hχ₂).of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ ((isClosed_tsupport χ₁).prod (isClosed_tsupport χ₂))
  intro z hz
  constructor
  · by_contra hχz
    apply hz
    funext ξ
    simp [Function.uncurry, cutoffAmplitude, image_eq_zero_of_notMem_tsupport hχz]
  · by_contra hχz
    apply hz
    funext ξ
    simp [Function.uncurry, cutoffAmplitude, image_eq_zero_of_notMem_tsupport hχz]

-- Preserve the original symbol and outer-cutoff hypotheses in this exact integral identity.
set_option linter.unusedVariables false in
/-- SG (3.9) holds for the actual cutoff multiplication on Schwartz inputs. -/
theorem amplitudeApply_cutoffAmplitude (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hsupp₁ : HasCompactSupport χ₁) (hsupp₂ : HasCompactSupport χ₂)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    amplitudeApply (cutoffAmplitude χ₁ χ₂ p) u x =
      χ₁ x • quantize p
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (χ₂ y : ℂ)) u) x := by
  /- Stage 1: smooth compact support implies temperate growth of the complex-valued
  cutoff, so mathlib's smulLeftCLM really acts by χ₂(y)u(y). Stage 2: in the inner
  y integral, factor out χ₁(x), p(x,ξ), and exp(i<x,ξ>). The remaining integral is
  exactly the unnormalized Fourier transform of χ₂u. The outer integral is quantize
  with its inverse factor (2π)^(-n); this uses iterated integrals, not joint Fubini. -/
  -- The actual input multiplier acts by the original real cutoff.
  let w := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (χ₂ y : ℂ)) u
  have hχgrowth : (fun y ↦ (χ₂ y : ℂ)).HasTemperateGrowth :=
    (hsupp₂.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ₂)
  have hw (y : EuclideanSpace ℝ (Fin n)) : w y = (χ₂ y : ℂ) • u y :=
    SchwartzMap.smulLeftCLM_apply_apply hχgrowth u y
  -- Normalize the Fourier phase at the prescribed rescaled frequency, retaining the sign.
  have hfourier (ξ : EuclideanSpace ℝ (Fin n)) :
      fourierSG w ξ = ∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • w y := by
    unfold fourierSG
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with y
    congr 2
    rw [inner_smul_right]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  -- The unit-modulus Fourier phase preserves integrability of the same Schwartz input.
  have hintegrable (ξ : EuclideanSpace ℝ (Fin n)) :
      MeasureTheory.Integrable (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • w y) := by
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) ↦
        Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • w y) := by
      fun_prop
    apply w.integrable.norm.mono' hcont.aestronglyMeasurable
    filter_upwards [] with y
    simp [norm_smul, Complex.norm_exp, Complex.mul_re]
  -- At each fixed frequency, only integrable vector functions pass through the matrix map.
  have hinner (ξ : EuclideanSpace ℝ (Fin n)) :
      (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          cutoffAmplitude χ₁ χ₂ p x y ξ (u y)) =
        χ₁ x • (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
          p x ξ (fourierSG w ξ)) := by
    rw [hfourier, ← (p x ξ).integral_comp_comm (hintegrable ξ),
      ← MeasureTheory.integral_smul, ← MeasureTheory.integral_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with y
    rw [hw]
    have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
          Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
      rw [← Complex.exp_add, inner_sub_left]
      congr 1
      push_cast
      ring
    simp only [cutoffAmplitude, smul_apply, hphase,
      map_smul, ← Complex.coe_smul, smul_smul, Complex.ofReal_mul]
    congr 1
    ring
  -- The remaining outer integral has the original inverse normalization; no Fubini is used.
  change ((2 * Real.pi) ^ n)⁻¹ • (∫ ξ, _) = _
  simp_rw [hinner]
  rw [MeasureTheory.integral_smul, smul_comm]
  rfl

/-- SG Corollary 3.8: the two-sided cutoff has the original order. -/
theorem isSymbol_cutoffSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hsupp₁ : HasCompactSupport χ₁) (hsupp₂ : HasCompactSupport χ₂) :
    IsSymbol Set.univ m (cutoffSymbol χ₁ χ₂ p) := by
  /- The previous two results verify all hypotheses of the Workhorse Theorem 3.5.
  Apply its symbol reduction theorem to the explicit cutoff amplitude. This is the
  book's entire proof of Corollary 3.8, with the real smooth cutoff hypotheses explicit. -/
  exact isSymbol_amplitudeSymbol m _
    (isAmplitude_cutoffAmplitude m p hp χ₁ χ₂ hχ₁ hχ₂)
    (hasCompactSupport_cutoffAmplitude p χ₁ χ₂ hsupp₁ hsupp₂)

/-- The reduced symbol realizes χ₁ P χ₂ exactly, including smoothing terms. -/
theorem quantize_cutoffSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hsupp₁ : HasCompactSupport χ₁) (hsupp₂ : HasCompactSupport χ₂)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (cutoffSymbol χ₁ χ₂ p) u x =
      χ₁ x • quantize p
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun y ↦ (χ₂ y : ℂ)) u) x := by
  /- First identify the quantization of the reduced symbol with the amplitude integral
  by SG 3.5. Then use the cutoff integral identity. Both equalities hold pointwise
  for every Schwartz input, so the resulting operator identity is exact, not modulo
  smoothing operators or only at the level of principal symbols. -/
  have hreduce := quantize_amplitudeSymbol m (cutoffAmplitude χ₁ χ₂ p)
    (isAmplitude_cutoffAmplitude m p hp χ₁ χ₂ hχ₁ hχ₂)
    (hasCompactSupport_cutoffAmplitude p χ₁ χ₂ hsupp₁ hsupp₂) u
  exact (congrFun hreduce x).trans
    (amplitudeApply_cutoffAmplitude m p hp χ₁ χ₂ hχ₁ hχ₂ hsupp₁ hsupp₂ u x)

/-- The full cutoff expansion is the diagonal mixed-derivative expansion of its amplitude. -/
theorem hasSymbolExpansion_cutoffSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hsupp₁ : HasCompactSupport χ₁) (hsupp₂ : HasCompactSupport χ₂) :
    HasSymbolExpansion Set.univ (fun j ↦ m - (j : ℝ))
      (cutoffSymbol χ₁ χ₂ p) (amplitudeExpansionTerm (cutoffAmplitude χ₁ χ₂ p)) := by
  /- Apply the full amplitude expansion after verifying its smoothness, estimates,
  and uniform compact spatial support. Differentiation in y hits χ₂ alone;
  the zeroth term is χ₁(x)χ₂(x)p(x,ξ). Each term of degree j has j frequency
  derivatives and the remainder after N terms has order m-N, also when N=0. -/
  exact hasSymbolExpansion_amplitudeSymbol m _
    (isAmplitude_cutoffAmplitude m p hp χ₁ χ₂ hχ₁ hχ₂)
    (hasCompactSupport_cutoffAmplitude p χ₁ χ₂ hsupp₁ hsupp₂)

/-- Both support conditions hold in the union of the cutoff supports. -/
theorem hasOperatorSupport_cutoff (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ₁ χ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hsupp₁ : HasCompactSupport χ₁) (hsupp₂ : HasCompactSupport χ₂) :
    HasOperatorSupport (tsupport χ₁ ∪ tsupport χ₂)
      (amplitudeOperator m (cutoffAmplitude χ₁ χ₂ p)
        (isAmplitude_cutoffAmplitude m p hp χ₁ χ₂ hχ₁ hχ₂)
        (hasCompactSupport_cutoffAmplitude p χ₁ χ₂ hsupp₁ hsupp₂)) := by
  /- Stage 1: the output vanishes off tsupport χ₁, a closed set, by the integral
  formula. Stage 2: if the input support is disjoint from the displayed union,
  χ₂u vanishes identically, so the amplitude action is zero. The two compact
  supports have compact union, as required for the compact-support calculus. -/
  -- The output integral vanishes outside the original output cutoff support.
  constructor
  · intro u
    apply closure_minimal ?_ ((isClosed_tsupport χ₁).union (isClosed_tsupport χ₂))
    intro x hx
    by_contra hxK
    have hχ : χ₁ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hxK (Or.inl h))
    apply hx
    rw [amplitudeOperator_apply]
    simp [amplitudeApply, cutoffAmplitude, hχ]
  · intro u hu
    -- Every point of the input cutoff support is disjoint from the input section support.
    have hzero (x y ξ : EuclideanSpace ℝ (Fin n)) :
        cutoffAmplitude χ₁ χ₂ p x y ξ (u y) = 0 := by
      by_cases hy : y ∈ tsupport χ₂
      · have hyu : y ∉ tsupport u := fun h ↦ Set.disjoint_left.mp hu h (Or.inr hy)
        simp [image_eq_zero_of_notMem_tsupport hyu]
      · simp [cutoffAmplitude, image_eq_zero_of_notMem_tsupport hy]
    -- Both iterated integrals are therefore zero for this same Schwartz input.
    ext x
    rw [amplitudeOperator_apply]
    simp [amplitudeApply, hzero]

end AtiyahSinger

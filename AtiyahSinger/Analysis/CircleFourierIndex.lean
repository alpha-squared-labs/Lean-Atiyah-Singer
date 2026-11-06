/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CircleFourierOperator
public import AtiyahSinger.Analysis.Fredholm

/-!
# The actual kernel, cokernel, and index of the circle Fourier operator

Public module ID: M0322.

AR02: Atiyah--Singer I, Section 8, printed pp.525--526. The operator is
`A = e^{ix} Π₊ + (1 - Π₊)` on the actual L² space of `AddCircle (2 * π)`.
It fixes the negative Fourier modes and shifts every nonnegative mode up by one.
Its range is the closed hyperplane with zero constant Fourier coefficient.
The cokernel below is the algebraic quotient by this original range, with the
canonical constant-function map; it is not replaced by an abstract line of
assumed dimension. The integer index is therefore `-1`.

Normalized Haar measure differs from the source's circle length measure by a
positive scalar. This changes neither the Fourier-mode action nor its kernel,
range or index. CircleFourierPseudodifferential identifies the same operator
in the global PDO calculus. The separate negative Thom-class comparison and
CirclePointIndex then give the original AR02 point-pushforward normalization `+1`.
The kernel, actual range, constant-cokernel equivalence, Fredholmness and index
below all retain the original operator and quotient map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ENNReal lp

/-- ASI p.526: the circle Fourier operator has trivial kernel. -/
theorem ker_circleFourierIndexOperator : circleFourierIndexOperator.ker = ⊥ := by
  /- Stage 1: the output coefficient at a negative n is the input coefficient
  at n; the output coefficient at n + 1 for n nonnegative is the input at n.
  Thus a zero output forces all input Fourier coefficients to vanish.
  Stage 2: injectivity of the actual circle Fourier Hilbert-basis representation
  forces the original L² vector to be zero. No pointwise representative is chosen. -/
  -- Compare inputs through the original Fourier isometry.
  apply LinearMap.ker_eq_bot.mpr
  intro f g hfg
  change circleFourierIndexOperator f = circleFourierIndexOperator g at hfg
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  apply lp.ext
  funext n
  have hcoeff (k : ℤ) :
      (if k < 0 then fourierCoeff f k
        else if k = 0 then 0 else fourierCoeff f (k - 1)) =
      (if k < 0 then fourierCoeff g k
        else if k = 0 then 0 else fourierCoeff g (k - 1)) :=
    (circleFourierIndexOperator_fourierCoeff f k).symm.trans
      ((congrArg (fun u : CircleFourierL2 ↦ fourierCoeff u k) hfg).trans
        (circleFourierIndexOperator_fourierCoeff g k))
  simp only [fourierBasis_repr]
  -- Negative outputs retain their input, and positive outputs recover input n at n + 1.
  by_cases hn : n < 0
  · simpa only [ite_eq_left hn] using hcoeff n
  · have hn₁ : ¬n + 1 < 0 := by omega
    have hn₂ : n + 1 ≠ 0 := by omega
    simpa only [ite_eq_right hn₁, ite_eq_right hn₂,
      add_sub_cancel_right] using hcoeff (n + 1)

/-- ASI p.526: the actual range consists precisely of functions with zero constant mode. -/
theorem range_circleFourierIndexOperator :
    (circleFourierIndexOperator.range : Set CircleFourierL2) =
      {f : CircleFourierL2 | fourierCoeff f 0 = 0} := by
  /- Stage 1: the mode action shows that A never produces the constant mode,
  so every output has zero zeroth Fourier coefficient.
  Stage 2: for a target f with coefficient zero at 0, set the preimage
  coefficients to f-hat(n) for n < 0 and f-hat(n + 1) for n >= 0. This sequence
  is square summable because it reindexes exactly the nonzero modes of f.
  The inverse of the same Fourier Hilbert-basis representation gives an actual
  L² preimage. The coefficient formula then proves equality with f, establishing
  the original range itself, without first taking its closure. -/
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    simp [circleFourierIndexOperator_fourierCoeff]
  · intro hf
    -- Pull back the square-summable coefficients along the injective missing-zero index map.
    let r : ℤ → ℤ := fun n ↦ if n < 0 then n else n + 1
    have hr : Function.Injective r := by
      intro n m h
      dsimp only [r] at h
      split_ifs at h <;> omega
    let c := (fourierBasis (T := 2 * Real.pi)).repr f
    have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    have hc : Memℓp (fun n ↦ c (r n)) 2 :=
      (memℓp_gen_iff hp).mpr (c.property.summable hp |>.comp_injective hr)
    let d : lp (fun _ : ℤ ↦ ℂ) 2 := ⟨fun n ↦ c (r n), hc⟩
    -- The inverse of the same Hilbert isometry realizes this sequence as an actual L² vector.
    let g := (fourierBasis (T := 2 * Real.pi)).repr.symm d
    refine ⟨g, ?_⟩
    apply (fourierBasis (T := 2 * Real.pi)).repr.injective
    apply lp.ext
    funext n
    have hg (k : ℤ) : fourierCoeff g k = c (r k) := by
      rw [← fourierBasis_repr]
      exact congrArg (fun u : lp (fun _ : ℤ ↦ ℂ) 2 ↦ u k)
        ((fourierBasis (T := 2 * Real.pi)).repr.apply_symm_apply d)
    simp only [fourierBasis_repr]
    change fourierCoeff (circleFourierIndexOperator g) n = fourierCoeff f n
    rw [circleFourierIndexOperator_fourierCoeff g n]
    -- Check every output coordinate, including the missing constant coordinate.
    by_cases hn : n < 0
    · simp only [hg, r, ite_eq_left hn, c, fourierBasis_repr]
    · by_cases hz : n = 0
      · subst n
        simpa using hf.symm
      · have hn₁ : ¬n - 1 < 0 := by omega
        simp only [ite_eq_right hn, ite_eq_right hz, hg, r, ite_eq_right hn₁, sub_add_cancel,
          c, fourierBasis_repr]

/-- The constant function with value `c` maps to its class in the actual circle cokernel. -/
def circleFourierConstantToCokernel :
    ℂ →ₗ[ℂ] (CircleFourierL2 ⧸ circleFourierIndexOperator.range) :=
  circleFourierIndexOperator.range.mkQ.comp
    (LinearMap.toSpanSingleton ℂ CircleFourierL2 (fourierLp (T := 2 * Real.pi) 2 0))

/-- ASI p.526: the natural constant-function map identifies the full actual cokernel. -/
theorem circleFourierConstantToCokernel_bijective :
    Function.Bijective circleFourierConstantToCokernel := by
  /- Stage 1: the constant Fourier coefficient of c times the zeroth mode is c.
  The range characterization therefore makes its quotient class zero only for
  c = 0, proving injectivity of this specified map.
  Stage 2: for any L² representative f, subtract its zeroth coefficient times
  the constant mode. The difference has zero constant coefficient and hence
  belongs to the actual range. Thus the class of f is represented by a constant,
  proving surjectivity without a separate dimension or cokernel assumption. -/
  -- Identify the actual constant mode through the same Fourier basis.
  have hmode : (fourierBasis (T := 2 * Real.pi)).repr
      (fourierLp (T := 2 * Real.pi) 2 0) = lp.single 2 0 (1 : ℂ) := by
    simpa only [coe_fourierBasis] using (fourierBasis (T := 2 * Real.pi)).repr_self 0
  have hcoeff (c : ℂ) : fourierCoeff
      (c • fourierLp (T := 2 * Real.pi) 2 0) 0 = c := by
    rw [← fourierBasis_repr, map_smul, hmode]
    simp
  constructor
  · -- A constant in the actual range must have zero coefficient and therefore zero value.
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro c hc
    change c = 0
    change circleFourierIndexOperator.range.mkQ
      (c • fourierLp (T := 2 * Real.pi) 2 0) = 0 at hc
    have hr := (Submodule.Quotient.mk_eq_zero _).mp hc
    have hz : fourierCoeff (c • fourierLp (T := 2 * Real.pi) 2 0) 0 = 0 := by
      change c • fourierLp (T := 2 * Real.pi) 2 0 ∈
        (circleFourierIndexOperator.range : Set CircleFourierL2) at hr
      rwa [range_circleFourierIndexOperator] at hr
    exact (hcoeff c).symm.trans hz
  · intro q
    -- Subtract the constant component of an arbitrary representative of the original quotient.
    obtain ⟨f, rfl⟩ := circleFourierIndexOperator.range.mkQ_surjective q
    refine ⟨fourierCoeff f 0, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    change fourierCoeff f 0 • fourierLp (T := 2 * Real.pi) 2 0 - f ∈
      (circleFourierIndexOperator.range : Set CircleFourierL2)
    rw [range_circleFourierIndexOperator]
    change fourierCoeff (fourierCoeff f 0 • fourierLp (T := 2 * Real.pi) 2 0 - f) 0 = 0
    rw [← fourierBasis_repr, map_sub, map_smul, hmode]
    change fourierCoeff f 0 * (lp.single (E := fun _ : ℤ ↦ ℂ) 2 0 (1 : ℂ)) 0 -
      (fourierBasis (T := 2 * Real.pi)).repr f 0 = 0
    simp [fourierBasis_repr]

/-- The canonical constant-line equivalence with the actual circle operator cokernel. -/
def circleFourierConstantCokernelEquiv :
    ℂ ≃ₗ[ℂ] (CircleFourierL2 ⧸ circleFourierIndexOperator.range) :=
  LinearEquiv.ofBijective circleFourierConstantToCokernel
    circleFourierConstantToCokernel_bijective

/-- The concrete circle Fourier operator is Fredholm on its original L² space. -/
theorem isFredholm_circleFourierIndexOperator : circleFourierIndexOperator.IsFredholm := by
  /- Stage 1: the zeroth Fourier coefficient is continuous, since it is the
  coordinate evaluation of the Fourier Hilbert-basis representation. Its kernel
  is the actual range by the range theorem, so the range is closed.
  Stage 2: the kernel theorem gives dimension zero and the specified constant
  quotient equivalence gives a one-dimensional actual cokernel. Apply the
  Hilbert-space characterization of Fredholmness to these same spaces and map. -/
  -- Continuous coordinate evaluation cuts out the original range as a closed hyperplane.
  have hc : Continuous (fun f : CircleFourierL2 ↦ fourierCoeff f 0) := by
    simp_rw [← fourierBasis_repr]
    exact (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 0).continuous.comp
      (fourierBasis (T := 2 * Real.pi)).repr.continuous
  -- The proved kernel and the specified quotient equivalence certify both finite dimensions.
  apply (isFredholm_iff_closed_range_finite circleFourierIndexOperator).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [range_circleFourierIndexOperator]
    exact isClosed_eq hc continuous_const
  · rw [ker_circleFourierIndexOperator]
    infer_instance
  · exact circleFourierConstantCokernelEquiv.finiteDimensional

/-- ASI p.526: the actual circle operator has index `0 - 1 = -1`. -/
theorem index_circleFourierIndexOperator : circleFourierIndexOperator.index = -1 := by
  /- Stage 1: Fredholmness justifies the finite kernel-minus-cokernel index
  formula for the actual operator. Its kernel has dimension zero; the natural
  constant-cokernel equivalence gives cokernel dimension one.
  Stage 2: subtract these dimensions. This is the operator's index -1, before
  the separate negative Thom-class comparison that yields point-pushforward +1. -/
  -- Retain the Fredholm certificates before using the kernel-minus-cokernel formula.
  have hF := isFredholm_circleFourierIndexOperator
  let : FiniteDimensional ℂ circleFourierIndexOperator.ker := hF.finite_ker
  let : FiniteDimensional ℂ (CircleFourierL2 ⧸ circleFourierIndexOperator.range) :=
    hF.finite_coker
  -- Transport the actual cokernel dimension through its specified constant-line equivalence.
  change circleFourierIndexOperator.toLinearMap.index = -1
  rw [LinearMap.index_eq_finrank_sub, ker_circleFourierIndexOperator,
    ← circleFourierConstantCokernelEquiv.finrank_eq]
  simp

end AtiyahSinger

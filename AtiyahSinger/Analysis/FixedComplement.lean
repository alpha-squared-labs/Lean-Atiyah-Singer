/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Fredholm
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Fixed complements under operator perturbation

Public module ID: M0634.

The block operator from SG III.7 Lemma 7.2, equation (7.1), p.202.
Its inverse gives explicit complementary coordinates. All inverse identities
retain membership in the invertibility domain; the totalized library inverse
has no inverse interpretation outside that domain. No Fredholm hypothesis is
needed for this local block calculus. Hilbert hypotheses enter in the later
construction of a chart around a specified Fredholm operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (V : Submodule ℂ E) (W : Submodule ℂ F)

/-- The block operator (w,v) ↦ w + Tv, with fixed complementary spaces. -/
def complementBlock (T : E →L[ℂ] F) : W × V →L[ℂ] F :=
  W.subtypeL.coprod (T.comp V.subtypeL)

/-- The standard invertibility chart determined by the two fixed subspaces. -/
def complementChartDomain : Set (E →L[ℂ] F) :=
  {T | (complementBlock V W T).IsInvertible}

/-- The W coordinate of the inverse block operator, on its invertibility domain. -/
def complementProjection (T : E →L[ℂ] F) : F →L[ℂ] W :=
  (ContinuousLinearMap.fst ℂ W V).comp (complementBlock V W T).inverse

/-- The V coordinate of the inverse block operator, on its invertibility domain. -/
def complementSolution (T : E →L[ℂ] F) : F →L[ℂ] V :=
  (ContinuousLinearMap.snd ℂ W V).comp (complementBlock V W T).inverse

/-- The block formula retains the original operator, without projecting T. -/
theorem complementBlock_apply (T : E →L[ℂ] F) (w : W) (v : V) :
    complementBlock V W T (w, v) = (w : F) + T v := by
  /- Unfold the coproduct of the subtype inclusion and the restriction of T.
  The first summand lies in the fixed W; the second is the actual image Tv. -/
  rfl

/-- The block construction is Lipschitz in the operator norm. -/
theorem norm_complementBlock_sub_le (T S : E →L[ℂ] F) :
    ‖complementBlock V W T - complementBlock V W S‖ ≤ ‖T - S‖ := by
  /- The difference sends (w,v) to (T-S)v. The subtype inclusion has norm
  at most one, and the product norm bounds the V coordinate by the pair norm. -/
  -- The difference loses the W coordinate and is controlled by the V coordinate.
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have happly : (complementBlock V W T - complementBlock V W S) x =
      (T - S) (x.2 : E) := by
    simp [complementBlock, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  rw [happly]
  calc
    ‖(T - S) (x.2 : E)‖ ≤ ‖T - S‖ * ‖(x.2 : E)‖ := (T - S).le_opNorm _
    _ ≤ ‖T - S‖ * ‖x‖ := mul_le_mul_of_nonneg_left (norm_snd_le x) (norm_nonneg _)

/-- The block construction depends continuously on the original operator. -/
theorem continuous_complementBlock : Continuous (complementBlock V W) := by
  /- Apply the preceding Lipschitz estimate to operator differences.
  This is operator-norm continuity, not merely continuity at each vector. -/
  have hLipschitz : LipschitzWith 1 (complementBlock V W) := by
    apply LipschitzWith.of_dist_le_mul
    intro T S
    simpa [dist_eq_norm] using norm_complementBlock_sub_le V W T S
  exact hLipschitz.continuous

section Invertible

variable {V W} {T : E →L[ℂ] F}
  (hT : T ∈ complementChartDomain V W)

include hT

/-- The chosen projection is the identity on the fixed complement. -/
theorem complementProjection_subtype (w : W) : complementProjection V W T w = w := by
  /- The block map sends (w,0) to w. Its inverse therefore sends w back
  to (w,0). Take the first coordinate of this inverse identity. -/
  have hblock : (complementBlock V W T).IsInvertible := hT
  have hinverse := hblock.inverse_apply_self (w, 0)
  have hfirst := congrArg Prod.fst hinverse
  simpa [complementProjection, complementBlock] using hfirst

/-- The chosen projection annihilates the varying image T(V). -/
theorem complementProjection_apply_image (v : V) : complementProjection V W T (T v) = 0 := by
  /- The block map sends (0,v) to Tv. Invert this identity and take its
  first coordinate. Invertibility, rather than a totalized inverse alone, is essential. -/
  have hblock : (complementBlock V W T).IsInvertible := hT
  have hinverse := hblock.inverse_apply_self (0, v)
  have hfirst := congrArg Prod.fst hinverse
  simpa [complementProjection, complementBlock] using hfirst

/-- The second coordinate vanishes on the fixed complement. -/
theorem complementSolution_subtype (w : W) : complementSolution V W T w = 0 := by
  /- Invert the block identity for (w,0) and take the second coordinate. -/
  have hblock : (complementBlock V W T).IsInvertible := hT
  have hinverse := hblock.inverse_apply_self (w, 0)
  have hsecond := congrArg Prod.snd hinverse
  simpa [complementSolution, complementBlock] using hsecond

/-- The second coordinate recovers the original vector in V. -/
theorem complementSolution_apply_image (v : V) : complementSolution V W T (T v) = v := by
  /- Invert the block identity for (0,v) and take the second coordinate. -/
  have hblock : (complementBlock V W T).IsInvertible := hT
  have hinverse := hblock.inverse_apply_self (0, v)
  have hsecond := congrArg Prod.snd hinverse
  simpa [complementSolution, complementBlock] using hsecond

/-- The inverse coordinates decompose every target vector. -/
theorem complementProjection_add_image_solution (y : F) :
    (complementProjection V W T y : F) + T (complementSolution V W T y) = y := by
  /- Apply the block operator to its inverse at y. The two coordinates
  are exactly the projection and solution maps, so the result is y. -/
  have hblock : (complementBlock V W T).IsInvertible := hT
  simpa [complementProjection, complementSolution, complementBlock] using
    hblock.self_apply_inverse y

/-- The image T(V) is precisely the kernel of the complement coordinate. -/
theorem ker_complementProjection :
    (complementProjection V W T).ker = V.map T.toLinearMap := by
  /- Every Tv is annihilated by the first coordinate. Conversely, if that
  coordinate vanishes, the decomposition writes y as T of the second coordinate. -/
  ext y
  constructor
  · intro hy
    -- Vanishing of the complement coordinate leaves an explicit preimage in V.
    have hzero : complementProjection V W T y = 0 := hy
    refine ⟨complementSolution V W T y, (complementSolution V W T y).property, ?_⟩
    simpa [hzero] using complementProjection_add_image_solution hT y
  · rintro ⟨v, hv, rfl⟩
    exact complementProjection_apply_image hT ⟨v, hv⟩

/-- The varying image is closed throughout the invertibility chart. -/
theorem isClosed_image_of_mem_complementChartDomain :
    IsClosed (V.map T.toLinearMap : Set F) := by
  /- Identify T(V) with the kernel of the continuous complement projection.
  The target W is Hausdorff, so this kernel is closed. -/
  rw [← ker_complementProjection hT]
  exact (complementProjection V W T).isClosed_ker

/-- The restriction of T to V remains injective throughout the chart. -/
theorem injective_restrict_of_mem_complementChartDomain :
    Function.Injective (T.comp V.subtypeL) := by
  /- The solution coordinate is a left inverse to the restriction of T.
  Apply it to an equality of images to recover equality in V. -/
  intro v₁ v₂ hsame
  have hcoordinates := congrArg (complementSolution V W T) hsame
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    complementSolution_apply_image hT] using hcoordinates

/-- The varying image and fixed complement form an algebraic direct sum. -/
theorem isCompl_image_of_mem_complementChartDomain :
    IsCompl (V.map T.toLinearMap) W := by
  /- The inverse coordinates give existence of a decomposition of every y.
  If a vector belongs to both summands, its first coordinate is both zero
  and itself. This proves disjointness and that their sum is the full space. -/
  -- A projection onto W splits the target as W plus its kernel.
  have hsplit : IsCompl W (complementProjection V W T).ker :=
    LinearMap.isCompl_of_proj (complementProjection_subtype hT)
  rw [ker_complementProjection hT] at hsplit
  exact hsplit.symm

end Invertible

variable [CompleteSpace V] [CompleteSpace W]

/-- The block invertibility domain is open in operator norm. -/
theorem isOpen_complementChartDomain : IsOpen (complementChartDomain V W) := by
  /- The domain W × V is Banach. Continuous linear equivalences form an
  open subset of its bounded operators; pull that set back by complementBlock. -/
  exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (continuous_complementBlock V W)

/-- The inverse block operator depends continuously on T inside the chart. -/
theorem continuousOn_inverse_complementBlock :
    ContinuousOn (fun T : E →L[ℂ] F ↦ (complementBlock V W T).inverse)
      (complementChartDomain V W) := by
  /- Around each invertible block, conjugate nearby blocks to endomorphisms
  of W × V close to identity. The norm-convergent Neumann series gives
  continuous inversion there. Compose with the continuous block construction. -/
  intro T hT
  obtain ⟨e, he⟩ := hT
  -- Use this one equivalence to identify nearby blocks with endomorphisms.
  have hconjugate : ContinuousAt
      (fun S : E →L[ℂ] F ↦ (e.symm : F →L[ℂ] W × V).comp
        (complementBlock V W S)) T :=
    continuousAt_const.clm_comp (continuous_complementBlock V W).continuousAt
  have hidentity : (e.symm : F →L[ℂ] W × V).comp (complementBlock V W T) =
      (1 : W × V →L[ℂ] W × V) := by
    rw [← he]
    apply ContinuousLinearMap.ext
    intro x
    exact e.symm_apply_apply x
  -- Inversion is continuous at the identity in the Banach algebra of endomorphisms.
  have hinversion : ContinuousAt Ring.inverse
      ((e.symm : F →L[ℂ] W × V).comp (complementBlock V W T)) := by
    rw [hidentity]
    exact NormedRing.inverse_continuousAt (R := W × V →L[ℂ] W × V) 1
  have hinverse := (hinversion.comp
    (f := fun S : E →L[ℂ] F ↦ (e.symm : F →L[ℂ] W × V).comp
      (complementBlock V W S)) hconjugate).clm_comp
    (continuousAt_const (y := (e.symm : F →L[ℂ] W × V)))
  simpa only [Function.comp_apply, ← ContinuousLinearMap.inverse_eq_ringInverse e] using
    hinverse.continuousWithinAt

/-- Complement coordinates depend continuously on T in operator norm. -/
theorem continuousOn_complementProjection :
    ContinuousOn (complementProjection V W) (complementChartDomain V W) := by
  /- Compose the continuously varying inverse block with the fixed first
  coordinate projection. Composition of bounded operators is continuous. -/
  exact continuousOn_const.clm_comp (continuousOn_inverse_complementBlock V W)

/-- Solution coordinates depend continuously on T in operator norm. -/
theorem continuousOn_complementSolution :
    ContinuousOn (complementSolution V W) (complementChartDomain V W) := by
  /- Compose the continuously varying inverse block with the fixed second
  coordinate projection. No parameter-dependent choice of a complement is made. -/
  exact continuousOn_const.clm_comp (continuousOn_inverse_complementBlock V W)

/-- Every operator in the chart has a norm ball contained in the chart. -/
theorem exists_radius_complementChartDomain (T₀ : E →L[ℂ] F)
    (hT₀ : T₀ ∈ complementChartDomain V W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : E →L[ℂ] F,
      ‖T - T₀‖ < ε → T ∈ complementChartDomain V W := by
  /- Use openness at T₀ and the metric ball basis for the operator norm.
  The positive radius controls the entire block chart, including its inverse coordinates. -/
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_complementChartDomain V W) T₀ hT₀
  refine ⟨ε, hε, ?_⟩
  intro T hT
  exact hball (by simpa [Metric.mem_ball, dist_eq_norm] using hT)

end AtiyahSinger

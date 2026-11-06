/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LocalComposition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

import AtiyahSinger.Analysis.AmplitudeRegularization
import AtiyahSinger.Analysis.CompactKernelSymbol
import AtiyahSinger.Analysis.CompactQuantization
import AtiyahSinger.Analysis.SmoothingKernelSymbol
import AtiyahSinger.Analysis.SymbolCoordinateEstimates
import AtiyahSinger.Geometry.CompactParameterIntegral
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Coordinate changes for compactly supported local operators

Public module ID: M0402.

D05/A02: SG Theorem 3.12 and Corollary 3.14, pp.183-186. Coordinate maps are actual
open partial homeomorphisms, with real smoothness of both directions explicit.
Compact cutoffs make pullback a continuous map of Schwartz spaces without imposing
global growth conditions on the coordinate maps. Operator support makes the resulting
conjugation independent of the cutoffs. Symbols are the zero-extended local model.

The averaged derivative is used only where the whole segment lies in the target.
Its inverse transpose is totalized by mathlib outside the invertible locus; analytical
claims require the cutoff support to lie inside that locus. Both Jacobians are absolute
values, including for orientation-reversing maps. No global convexity is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff Manifold SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r s : ℕ}

/-- Compactly supported smooth pullback is a genuine continuous Schwartz operator. -/
theorem existsUnique_cutoffPullbackCLM
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ContDiffOn ℝ ∞ g U) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∃! T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
      ∀ u x, T u x = χ x • u (g x) := by
  /- Stage 1: on U use smooth composition and multiplication. Off tsupport χ the
  product is identically zero on a neighborhood; since tsupport χ lies in U, these
  arguments prove global smoothness even if g is arbitrary off U. Compact support
  then gives a Schwartz function. Stage 2: on the fixed compact support, every
  derivative of g and χ is bounded. The product and chain rules bound each output
  Schwartz seminorm by finitely many input seminorms. This proves continuity and
  complex linearity. Pointwise equality of Schwartz functions gives uniqueness. -/
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  have hzero (x : X) (hx : x ∉ tsupport χ) : χ =ᶠ[nhds x] (fun _ ↦ 0) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  -- Local smoothness on the domain and local vanishing off the cutoff support glue globally.
  have hsmooth (u : 𝓢(X, V)) : ContDiff ℝ ∞ (fun x ↦ χ x • u (g x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.smul
        (((u.smooth ⊤).contDiffAt).comp x (hg.contDiffAt (hU.mem_nhds (hχU hx))))
    · apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      filter_upwards [hzero x hx] with y hy
      change χ y = 0 at hy
      simp only [hy, zero_smul]
  -- All coefficients in the finite chain and product rules are bounded on one fixed support.
  have hχbound (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport χ,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hcχ.image (hχ.continuous_iteratedFDeriv (by simp)).norm).bddAbove
    exact ⟨max B 0, le_max_right _ _, fun x hx ↦
      (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
  have hgbound (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport χ,
      ‖iteratedFDeriv ℝ j g x‖ ≤ B := by
    have hcont := (hg.continuousOn_iteratedFDerivWithin (m := j) (by simp)
      hU.uniqueDiffOn).mono hχU
    obtain ⟨B, hB⟩ := hcχ.exists_bound_of_continuousOn hcont
    refine ⟨max B 0, le_max_right _ _, fun x hx ↦ ?_⟩
    have h := hB x hx
    rw [iteratedFDerivWithin_of_isOpen _ hU (hχU hx)] at h
    exact h.trans (le_max_left _ _)
  choose B hB hχB using hχbound
  choose G hG hgG using hgbound
  obtain ⟨R, hR⟩ := hcχ.exists_bound_of_continuousOn continuousOn_id
  let R' := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  have hbound : ∀ N : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (u : 𝓢(X, V)) (x : X),
        ‖x‖ ^ N.1 * ‖iteratedFDeriv ℝ N.2 (fun y ↦ χ y • u (g y)) x‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ X V) u := by
    rintro ⟨k, l⟩
    let D := 1 + ∑ i ∈ Finset.range (l + 1), G i
    have hD : 1 ≤ D := by
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hG i))
    have hGD (i : ℕ) (hi : i ≤ l) : G i ≤ D := by
      apply le_trans (Finset.single_le_sum (fun j _ ↦ hG j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
      exact le_add_of_nonneg_left zero_le_one
    let C := R' ^ k * ∑ i ∈ Finset.range (l + 1),
      (l.choose i : ℝ) * B i * ((l - i).factorial : ℝ) * D ^ (l - i)
    have hC : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (pow_nonneg hR' _) (Finset.sum_nonneg (fun i _ ↦
        mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i))
          (Nat.cast_nonneg _)) (pow_nonneg (zero_le_one.trans hD) _)))
    refine ⟨Finset.Iic (0, l), C, hC, ?_⟩
    intro u x
    let S := (Finset.Iic (0, l)).sup (schwartzSeminormFamily ℂ X V) u
    have hS : 0 ≤ S := apply_nonneg _ _
    by_cases hx : x ∈ tsupport χ
    · have hxU := hχU hx
      have hcomp (j : ℕ) (hj : j ≤ l) :
          ‖iteratedFDeriv ℝ j (fun y ↦ u (g y)) x‖ ≤ j.factorial * S * D ^ j := by
        have he := norm_iteratedFDerivWithin_comp_le
          (u.smooth ⊤).contDiffOn hg (n := j) (by simp) uniqueDiffOn_univ
          hU.uniqueDiffOn (Set.mapsTo_univ g U) hxU (C := S) (D := D)
        simp only [iteratedFDerivWithin_univ,
          iteratedFDerivWithin_of_isOpen _ hU hxU] at he
        apply he
        · intro i hi
          apply (u.norm_iteratedFDeriv_le_seminorm ℂ i (g x)).trans
          exact (Finset.le_sup (f := schwartzSeminormFamily ℂ X V)
            (show (0, i) ∈ Finset.Iic (0, l) from Finset.mem_Iic.mpr ⟨le_rfl, hi.trans hj⟩)) u
        · intro i hi hij
          exact (hgG i x hx).trans ((hGD i (hij.trans hj)).trans
            (le_self_pow₀ hD (by omega)))
      have hp := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn
        ((u.smooth ⊤).comp_contDiffOn hg) hU.uniqueDiffOn hxU (n := l) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hp
      have hsum : ‖iteratedFDeriv ℝ l (fun y ↦ χ y • u (g y)) x‖ ≤
          (∑ i ∈ Finset.range (l + 1),
            (l.choose i : ℝ) * B i * ((l - i).factorial : ℝ) * D ^ (l - i)) * S := by
        apply hp.trans
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ (l.choose i : ℝ) * B i * ((l - i).factorial * S * D ^ (l - i)) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hχB i x hx)
              (Nat.cast_nonneg _)) (hcomp _ (Nat.sub_le _ _)) (norm_nonneg _)
                (mul_nonneg (Nat.cast_nonneg _) (hB i))
          _ = _ := by ring
      calc
        _ ≤ R' ^ k * ((∑ i ∈ Finset.range (l + 1),
            (l.choose i : ℝ) * B i * ((l - i).factorial : ℝ) * D ^ (l - i)) * S) := by
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
            ((hR x hx).trans (le_max_left _ _)) _) hsum (norm_nonneg _) (pow_nonneg hR' _)
        _ = C * S := by dsimp [C]; ring
    · have heq : (fun y ↦ χ y • u (g y)) =ᶠ[nhds x] (fun _ ↦ (0 : V)) := by
        filter_upwards [hzero x hx] with y hy
        simp only [hy, zero_smul]
      rw [(heq.iteratedFDeriv ℝ l).eq_of_nhds]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using
        mul_nonneg hC hS
  -- The estimates give one continuous linear map with the exact original pointwise action.
  let T : 𝓢(X, V) →L[ℂ] 𝓢(X, V) := SchwartzMap.mkCLM
    (σ := RingHom.id ℂ) (fun u x ↦ χ x • u (g x))
    (by intros; simp [smul_add])
    (by intro a u x; exact smul_comm (χ x) a (u (g x))) hsmooth hbound
  refine ⟨T, fun _ _ ↦ rfl, ?_⟩
  intro T' hT'
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  exact hT' u x

/-- The continuous map u ↦ χ · (u ∘ g), specified by its actual pointwise formula. -/
def cutoffPullbackCLM
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ContDiffOn ℝ ∞ g U) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  (existsUnique_cutoffPullbackCLM U hU g hg χ hχ hcχ hχU).exists.choose

/-- The chosen pullback has the specified value, including outside the coordinate domain. -/
theorem cutoffPullbackCLM_apply
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ContDiffOn ℝ ∞ g U) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    cutoffPullbackCLM U hU g hg χ hχ hcχ hχU u x = χ x • u (g x) := by
  /- Use the specification of the unique continuous map in the existence theorem.
  Outside U the cutoff is zero, so the formula does not require any regularity or
  inverse identities for the arbitrary total extension of g outside its domain. -/
  exact (existsUnique_cutoffPullbackCLM U hU g hg χ hχ hcχ hχU).exists.choose_spec u x

/-- Coordinate conjugation realized by two compactly supported pullbacks. -/
def coordinatePushforward
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s))) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) :=
  (cutoffPullbackCLM e.target e.open_target e.symm hψ ρ hρ hcρ hρV).comp
    (P.comp (cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχU))

/-- SG's cotangent transformation of a symbol; the derivative is of the forward map. -/
def cotangentSymbol
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (p : SymbolFunction n r s) : SymbolFunction n r s :=
  fun x ξ ↦ p (e.symm x) ((fderiv ℝ e (e.symm x)).adjoint ξ)

/-- Restricting the spatial domain preserves the same symbol estimates. -/
theorem IsSymbol.restrict {U V : Set (EuclideanSpace ℝ (Fin n))}
    {m : ℝ} {p : SymbolFunction n r s} (hp : IsSymbol U m p) (hVU : V ⊆ U) :
    IsSymbol V m p := by
  /- Restrict joint smoothness from U times the frequency space to its subset V
  times the frequency space. Every compact subset of V is also a compact subset
  of U, so the same derivative estimates apply without changing the symbol function. -/
  refine ⟨hp.1.mono (Set.prod_mono hVU (Set.Subset.refl _)), ?_⟩
  intro K hKV hK i j
  exact hp.2 K (hKV.trans hVU) hK i j

/-- Smooth cotangent coordinate changes preserve every real symbol order on open domains. -/
theorem isSymbol_cotangentSymbol
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol e.source m p) :
    IsSymbol e.target m (cotangentSymbol e p) := by
  /- Stage 1: differentiate the inverse identities on the open source and target.
  The forward derivative and its transpose are invertible. On a compact target
  set their norms and inverse norms are bounded, so the old and new frequency
  weights are uniformly comparable, also for negative real exponents. Stage 2:
  each spatial derivative hitting the frequency map contributes one factor of ξ
  and one extra frequency derivative of p. These cancel in order; each external
  frequency derivative lowers the order by one. Apply the finite chain rule. -/
  let X := EuclideanSpace ℝ (Fin n)
  let Θ : X → X →L[ℝ] X := fun x ↦ (fderiv ℝ e (e.symm x)).adjoint
  -- The transpose is a real linear isometry on the derivative coefficients.
  let J : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ] (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro c A; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hΘ : ContDiffOn ℝ ∞ Θ e.target := by
    intro x hx
    have hforward := he.contDiffAt (e.open_source.mem_nhds (e.map_target hx))
    have hbackward := hψ.contDiffAt (e.open_target.mem_nhds hx)
    exact (J.contDiff.contDiffAt.comp x
      ((hforward.fderiv_right (m := ∞) (by simp)).comp x hbackward)).contDiffWithinAt
  have hinv (x : X) (hx : x ∈ e.target) : (Θ x).IsInvertible := by
    have hsource : e.symm x ∈ e.source := e.map_target hx
    have hforward := (he.contDiffAt (e.open_source.mem_nhds hsource)).differentiableAt
      (by simp)
    have hbackward := (hψ.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt
      (by simp)
    have hright : (fderiv ℝ e (e.symm x)).comp (fderiv ℝ e.symm x) =
        ContinuousLinearMap.id ℝ X := by
      apply (hforward.hasFDerivAt.comp x hbackward.hasFDerivAt).unique
      apply (hasFDerivAt_id x).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hx] with y hy
      exact e.right_inv hy
    have hleft : (fderiv ℝ e.symm x).comp (fderiv ℝ e (e.symm x)) =
        ContinuousLinearMap.id ℝ X := by
      have hbackward' : HasFDerivAt e.symm (fderiv ℝ e.symm x) (e (e.symm x)) := by
        simpa only [e.right_inv hx] using hbackward.hasFDerivAt
      apply (hbackward'.comp (e.symm x) hforward.hasFDerivAt).unique
      apply (hasFDerivAt_id (e.symm x)).congr_of_eventuallyEq
      filter_upwards [e.open_source.mem_nhds hsource] with y hy
      exact e.left_inv hy
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := (fderiv ℝ e.symm x).adjoint)
    · simpa only [Θ, X, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint hleft
    · simpa only [Θ, X, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint hright
  -- Composition is smooth on the original open domains, with the actual cotangent map.
  refine ⟨?_, ?_⟩
  · intro z hz
    have hbackward := hψ.contDiffAt (e.open_target.mem_nhds hz.1)
    have hcoeff := hΘ.contDiffAt (e.open_target.mem_nhds hz.1)
    have hpAt := hp.1.contDiffAt ((e.open_source.prod isOpen_univ).mem_nhds
      (show (e.symm z.1, Θ z.1 z.2) ∈ e.source ×ˢ Set.univ from
        ⟨e.map_target hz.1, Set.mem_univ _⟩))
    exact (hpAt.comp z ((hbackward.comp z contDiffAt_fst).prodMk
      ((hcoeff.comp z contDiffAt_fst).clm_apply contDiffAt_snd))).contDiffWithinAt
  · intro K hKU hK i j
    exact exists_bound_symbol_comp_linear_frequency e.source e.open_source m p hp
      e.target e.open_target e.symm hψ (fun _ hx ↦ e.map_target hx)
      Θ hΘ hinv K hK hKU i j

/-- SG's averaged derivative along the segment from y to x. -/
def averagedFDeriv (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ g (t • x + (1 - t) • y)

/-- The phase difference factors through the averaged derivative on admissible segments. -/
theorem averagedFDeriv_sub
    (V : Set (EuclideanSpace ℝ (Fin n))) (hV : IsOpen V)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ContDiffOn ℝ ∞ g V) (x y : EuclideanSpace ℝ (Fin n))
    (hseg : segment ℝ y x ⊆ V) : averagedFDeriv g x y (x - y) = g x - g y := by
  /- The segment hypothesis keeps the entire parameter curve inside the open set
  where g is smooth. Differentiate t ↦ g(tx+(1-t)y), then use the fundamental
  theorem of calculus. Evaluation on x-y commutes with the finite-dimensional
  integral. No assertion is made for segments leaving the coordinate domain. -/
  let γ (t : ℝ) : EuclideanSpace ℝ (Fin n) := t • x + (1 - t) • y
  -- The entire integration path stays in the original domain of differentiability.
  have hγ : Set.MapsTo γ (Set.Icc 0 1) V := by
    intro t ht
    apply hseg
    rw [segment_eq_image]
    exact ⟨t, ht, by simp only [γ, add_comm]⟩
  have hcontinuous : ContinuousOn (fun t ↦ fderiv ℝ g (γ t)) (Set.uIcc 0 1) := by
    apply (hg.continuousOn_fderiv_of_isOpen hV (by simp)).comp
      (show ContinuousOn γ (Set.uIcc 0 1) from (by fun_prop : Continuous γ).continuousOn)
    simpa only [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hγ
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc 0 1) :
      HasDerivAt (fun a ↦ g (γ a)) (fderiv ℝ g (γ t) (x - y)) t := by
    have ht' : t ∈ Set.Icc 0 1 := by simpa only [Set.uIcc_of_le zero_le_one] using ht
    have hpath : HasDerivAt γ (x - y) t := by
      dsimp only [γ]
      convert ((hasDerivAt_id t).smul_const x).add
        (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const y) using 1 <;>
        simp [sub_eq_add_neg, Pi.add_def]
    exact ((hg.contDiffAt (hV.mem_nhds (hγ ht'))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t hpath
  -- Evaluate the actual operator integral, then apply the fundamental theorem of calculus.
  rw [averagedFDeriv, ContinuousLinearMap.intervalIntegral_apply hcontinuous.intervalIntegrable]
  simpa only [γ, one_smul, zero_smul, sub_self, sub_zero, zero_add, add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcontinuous.clm_apply continuousOn_const).intervalIntegrable

/-- On the diagonal the averaged derivative is exactly the derivative. -/
theorem averagedFDeriv_diag
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : averagedFDeriv g x x = fderiv ℝ g x := by
  /- The affine point tx+(1-t)x equals x for every real t. Thus the integrand
  is the constant continuous linear map fderiv g x, whose integral over [0,1]
  is itself. This algebraic identity also holds for mathlib's totalized derivative. -/
  have hpoint (t : ℝ) : t • x + (1 - t) • x = x := by
    rw [← add_smul]
    simp
  simp only [averagedFDeriv, hpoint, intervalIntegral.integral_const,
    sub_zero, one_smul]


set_option linter.unusedVariables false in
/-- A compact part of the diagonal has a neighborhood with valid segments and invertibility. -/
theorem exists_coordinateChange_neighborhood
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (hLV : L ⊆ e.target) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ (fun x ↦ (x, x)) '' L ⊆ W ∧
        ∀ z ∈ W, segment ℝ z.2 z.1 ⊆ e.target ∧
          (averagedFDeriv e.symm z.1 z.2).IsInvertible := by
  /- Use the interior of the valid segment-and-invertibility locus. At a specified
  diagonal point, differentiating both coordinate inverse laws gives an invertible
  derivative of the inverse chart. In a small convex ball, the derivatives stay
  close to this fixed map; averaging over the unit interval retains the same bound.
  Both endpoints in that ball therefore lie in the desired locus, proving that the
  diagonal point belongs to its interior. Later cutoffs may use compactness of L. -/
  -- Take the interior of the desired locus and show that every specified diagonal point lies in it.
  let S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {z | segment ℝ z.2 z.1 ⊆ e.target ∧ (averagedFDeriv e.symm z.1 z.2).IsInvertible}
  refine ⟨interior S, isOpen_interior, ?_, fun z hz ↦
    (show z ∈ S from interior_subset hz)⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxV : x ∈ e.target := hLV hx
  have hxU : e.symm x ∈ e.source := e.map_target hxV
  have hforward := (he.contDiffAt (e.open_source.mem_nhds hxU)).differentiableAt
    (by simp)
  have hbackward := (hψ.contDiffAt (e.open_target.mem_nhds hxV)).differentiableAt
    (by simp)
  -- The original inverse maps give two-sided inverses for their actual derivatives.
  have hright : (fderiv ℝ e (e.symm x)).comp (fderiv ℝ e.symm x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply (hforward.hasFDerivAt.comp x hbackward.hasFDerivAt).unique
    apply (hasFDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hxV] with y hy
    exact e.right_inv hy
  have hleft : (fderiv ℝ e.symm x).comp (fderiv ℝ e (e.symm x)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hbackward' : HasFDerivAt e.symm (fderiv ℝ e.symm x) (e (e.symm x)) := by
      simpa only [e.right_inv hxV] using hbackward.hasFDerivAt
    apply (hbackward'.comp (e.symm x) hforward.hasFDerivAt).unique
    apply (hasFDerivAt_id (e.symm x)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hxU] with y hy
    exact e.left_inv hy
  have hinv : (fderiv ℝ e.symm x).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hleft hright
  have hopen : IsOpen {T : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) | T.IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  obtain ⟨ε, hε, hεinv⟩ := Metric.isOpen_iff.mp hopen (fderiv ℝ e.symm x) hinv
  -- In a small convex ball, all derivatives stay close to the same invertible derivative.
  have hderivCont : ContinuousAt (fderiv ℝ e.symm) x :=
    (hψ.contDiffAt (e.open_target.mem_nhds hxV)).continuousAt_fderiv (by simp)
  have hnear : ∀ᶠ y in nhds x, y ∈ e.target ∧
      dist (fderiv ℝ e.symm y) (fderiv ℝ e.symm x) < ε / 2 := by
    filter_upwards [e.open_target.mem_nhds hxV,
      hderivCont (Metric.ball_mem_nhds _ (half_pos hε))] with y hy hclose
    exact ⟨hy, hclose⟩
  obtain ⟨δ, hδ, hδgood⟩ := Metric.eventually_nhds_iff.mp hnear
  apply mem_interior_iff_mem_nhds.mpr
  have hsquare : Metric.ball x δ ×ˢ Metric.ball x δ ∈ nhds (x, x) :=
    (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
      ⟨Metric.mem_ball_self hδ, Metric.mem_ball_self hδ⟩
  filter_upwards [hsquare] with z hz
  have hsegment : segment ℝ z.2 z.1 ⊆ Metric.ball x δ :=
    (convex_ball x δ).segment_subset hz.2 hz.1
  have hsegmentV : segment ℝ z.2 z.1 ⊆ e.target :=
    hsegment.trans (fun _ hy ↦ (hδgood hy).1)
  refine ⟨hsegmentV, ?_⟩
  let γ (t : ℝ) : EuclideanSpace ℝ (Fin n) := t • z.1 + (1 - t) • z.2
  have hγ (t : ℝ) (ht : t ∈ Set.Icc 0 1) : γ t ∈ Metric.ball x δ := by
    apply hsegment
    rw [segment_eq_image]
    exact ⟨t, ht, by simp only [γ, add_comm]⟩
  have hcontinuous : ContinuousOn (fun t ↦ fderiv ℝ e.symm (γ t)) (Set.uIcc 0 1) := by
    apply (hψ.continuousOn_fderiv_of_isOpen e.open_target (by simp)).comp
      (show ContinuousOn γ (Set.uIcc 0 1) from (by fun_prop : Continuous γ).continuousOn)
    intro t ht
    apply (hδgood (hγ t ?_)).1
    simpa only [Set.uIcc_of_le zero_le_one] using ht
  -- Averaging over an interval of length one preserves the same uniform distance bound.
  have hbound : ‖averagedFDeriv e.symm z.1 z.2 - fderiv ℝ e.symm x‖ ≤ ε / 2 := by
    have heq : averagedFDeriv e.symm z.1 z.2 - fderiv ℝ e.symm x =
        ∫ t in (0 : ℝ)..1, fderiv ℝ e.symm (γ t) - fderiv ℝ e.symm x := by
      rw [intervalIntegral.integral_sub hcontinuous.intervalIntegrable
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp only [sub_zero, one_smul]
      rfl
    rw [heq]
    have hnorm (t : ℝ) (ht : t ∈ Set.uIoc 0 1) :
        ‖fderiv ℝ e.symm (γ t) - fderiv ℝ e.symm x‖ ≤ ε / 2 := by
      have ht' : t ∈ Set.Icc 0 1 := by
        simpa only [Set.uIcc_of_le zero_le_one] using Set.uIoc_subset_uIcc ht
      simpa only [dist_eq_norm] using
        (show dist (fderiv ℝ e.symm (γ t)) (fderiv ℝ e.symm x) < ε / 2 from
          (hδgood (hγ t ht')).2).le
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  apply hεinv
  change dist (averagedFDeriv e.symm z.1 z.2) (fderiv ℝ e.symm x) < ε
  simpa only [dist_eq_norm] using hbound.trans_lt (half_lt_self hε)

/-- The inverse transpose used to replace the old frequency by the new one. -/
def coordinateFrequencyChange
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (averagedFDeriv e.symm x y).adjoint.inverse

/-- On the diagonal the inverse transpose of Dψ is the transpose of Dφ. -/
theorem coordinateFrequencyChange_diag
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) :
    coordinateFrequencyChange e x x = (fderiv ℝ e (e.symm x)).adjoint := by
  /- Evaluate the averaged derivative on the diagonal. The chain rule for both
  inverse identities says Dψ(x) and Dφ(ψ(x)) are two-sided inverses. Taking real
  adjoints reverses their products, so the inverse of Dψ(x)^T is Dφ(ψ(x))^T.
  This also fixes the direction of the cotangent transformation. -/
  -- Differentiate the actual two inverse identities at the corresponding points.
  have hsource : e.symm x ∈ e.source := e.map_target hx
  have hforward := (he.contDiffAt (e.open_source.mem_nhds hsource)).differentiableAt
    (by simp)
  have hbackward := (hψ.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt
    (by simp)
  have hright : (fderiv ℝ e (e.symm x)).comp (fderiv ℝ e.symm x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply (hforward.hasFDerivAt.comp x hbackward.hasFDerivAt).unique
    apply (hasFDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    exact e.right_inv hy
  have hleft : (fderiv ℝ e.symm x).comp (fderiv ℝ e (e.symm x)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hbackward' : HasFDerivAt e.symm (fderiv ℝ e.symm x) (e (e.symm x)) := by
      simpa only [e.right_inv hx] using hbackward.hasFDerivAt
    apply (hbackward'.comp (e.symm x) hforward.hasFDerivAt).unique
    apply (hasFDerivAt_id (e.symm x)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hsource] with y hy
    exact e.left_inv hy
  -- Taking real adjoints reverses composition, identifying the totalized inverse.
  rw [coordinateFrequencyChange, averagedFDeriv_diag]
  apply ContinuousLinearMap.inverse_eq
  · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg ContinuousLinearMap.adjoint hright
  · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg ContinuousLinearMap.adjoint hleft

/-- The absolute Jacobian factors from spatial and frequency substitutions. -/
def coordinateJacobianFactor
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  |(fderiv ℝ e.symm y).det| * |(coordinateFrequencyChange e x y).det|

/-- The absolute Jacobians cancel on the diagonal, without an orientation assumption. -/
theorem coordinateJacobianFactor_diag
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) :
    coordinateJacobianFactor e x x = 1 := by
  /- The determinant of the real transpose equals the determinant of the original
  map. Since Dψ is invertible, det(Dψ) is nonzero and the second factor is its
  absolute reciprocal. Their product is one even for orientation-reversing maps;
  using a signed spatial Jacobian would instead introduce a spurious minus sign. -/
  -- In the standard real orthonormal basis, adjoint is matrix transpose.
  have hdet (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      T.adjoint.det = T.det := by
    simp only [ContinuousLinearMap.det, ← ContinuousLinearMap.adjoint_toLinearMap]
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
      LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose, star_trivial,
      LinearMap.det_toMatrix]
  -- Differentiating the inverse identity fixes the product of the two determinants.
  have hsource : e.symm x ∈ e.source := e.map_target hx
  have hforward := (he.contDiffAt (e.open_source.mem_nhds hsource)).differentiableAt
    (by simp)
  have hbackward := (hψ.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt
    (by simp)
  have hright : (fderiv ℝ e (e.symm x)).comp (fderiv ℝ e.symm x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply (hforward.hasFDerivAt.comp x hbackward.hasFDerivAt).unique
    apply (hasFDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    exact e.right_inv hy
  have hproduct : (fderiv ℝ e (e.symm x)).det * (fderiv ℝ e.symm x).det = 1 := by
    have hdetProduct := congrArg ContinuousLinearMap.det hright
    change LinearMap.det ((fderiv ℝ e (e.symm x)).toLinearMap.comp
      (fderiv ℝ e.symm x).toLinearMap) =
        LinearMap.det (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n)) at hdetProduct
    simpa only [LinearMap.det_comp, LinearMap.det_id] using hdetProduct
  -- Absolute values keep the same cancellation for either orientation.
  rw [coordinateJacobianFactor, coordinateFrequencyChange_diag e he hψ x hx,
    hdet, ← abs_mul, mul_comm, hproduct, abs_one]

/-- The near-diagonal amplitude in SG's change-of-coordinates proof. -/
def coordinateAmplitude
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r s) : AmplitudeFunction n r s :=
  fun x y ξ ↦ (χ (x, y) * coordinateJacobianFactor e x y) •
    p (e.symm x) (coordinateFrequencyChange e x y ξ)

/-- A compact cutoff inside a smooth invertible linear-frequency locus preserves symbol order. -/
private theorem isAmplitude_cutoff_linear_frequency
    {n r s : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol U m p)
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hφ : ContDiffOn ℝ ∞ φ W) (hφU : Set.MapsTo φ W U)
    (Θ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hΘ : ContDiffOn ℝ ∞ Θ W) (hinv : ∀ z ∈ W, (Θ z).IsInvertible)
    (γ χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ : ContDiffOn ℝ ∞ γ W) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hχW : tsupport χ ⊆ W) :
    IsAmplitude m (fun x y ξ ↦ (χ (x, y) * γ (x, y)) • p (φ (x, y)) (Θ (x, y) ξ)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)
  let q : (X × X) → X → H := fun z ξ ↦ p (φ z) (Θ z ξ)
  let g : (X × X) → ℝ := fun z ↦ χ z * γ z
  let a : (X × X) → X → H := fun z ξ ↦ g z • q z ξ
  have hg : ContDiffOn ℝ ∞ g W := hχ.contDiffOn.mul hγ
  have hq : ContDiffOn ℝ ∞ (Function.uncurry q) (W ×ˢ Set.univ) := by
    intro z hz
    have hφat := hφ.contDiffAt (hW.mem_nhds hz.1)
    have hΘat := hΘ.contDiffAt (hW.mem_nhds hz.1)
    have hpAt := hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds
      (show (φ z.1, Θ z.1 z.2) ∈ U ×ˢ Set.univ from ⟨hφU hz.1, Set.mem_univ _⟩))
    exact (hpAt.comp z ((hφat.comp z contDiffAt_fst).prodMk
      ((hΘat.comp z contDiffAt_fst).clm_apply contDiffAt_snd))).contDiffWithinAt
  have hzero (z : X × X) (hz : z ∉ tsupport χ) : χ =ᶠ[nhds z] (fun _ ↦ 0) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  -- Local smoothness on W and local vanishing off the closed cutoff support glue globally.
  have ha : ContDiff ℝ ∞ (Function.uncurry a) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 ∈ tsupport χ
    · have hgAt := hg.contDiffAt (hW.mem_nhds (hχW hz))
      exact (hgAt.comp z contDiffAt_fst).smul
        (hq.contDiffAt ((hW.prod isOpen_univ).mem_nhds ⟨hχW hz, Set.mem_univ _⟩))
    · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
      filter_upwards [(hzero z.1 hz).comp_tendsto continuous_fst.continuousAt] with w hw
      change χ w.1 = 0 at hw
      simp only [Function.uncurry, a, g, hw, zero_mul, zero_smul]
  have parametric {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
      (f : P → Q → R) (x : P) (y : Q)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (k : ℕ) :
      ContDiffAt ℝ ∞ (fun z : P × Q ↦ iteratedFDeriv ℝ k (f z.1) z.2) (x, y) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Q R).symm : _ →L[ℝ] Q [×0]→L[ℝ] R)
    | succ k ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun z : P × Q ↦ fun η : Q ↦ iteratedFDeriv ℝ k (f z.1) η))
          ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun z : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) (x, y) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Q) R).symm :
          _ →L[ℝ] Q [×(k + 1)]→L[ℝ] R)
  have hDa (k : ℕ) (ξ : X) :
      ContDiff ℝ ∞ (fun z ↦ iteratedFDeriv ℝ k (a z) ξ) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (parametric a z ξ ha.contDiffAt k).comp z
      (contDiffAt_id.prodMk contDiffAt_const)
  have hDq (k : ℕ) (ξ : X) :
      ContDiffOn ℝ ∞ (fun z ↦ iteratedFDeriv ℝ k (q z) ξ) W := by
    intro z hz
    have hAt := hq.contDiffAt ((hW.prod isOpen_univ).mem_nhds
      (show (z, ξ) ∈ W ×ˢ Set.univ from ⟨hz, Set.mem_univ ξ⟩))
    exact ((parametric q z ξ hAt k).comp z
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hfreq (k : ℕ) (z : X × X) (hz : z ∈ W) (ξ : X) :
      iteratedFDeriv ℝ k (a z) ξ = g z • iteratedFDeriv ℝ k (q z) ξ := by
    have hAt := hq.contDiffAt ((hW.prod isOpen_univ).mem_nhds
      (show (z, ξ) ∈ W ×ˢ Set.univ from ⟨hz, Set.mem_univ ξ⟩))
    exact iteratedFDeriv_const_smul_apply'
      ((hAt.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
  -- Leibniz on the compact spatial support combines smooth coefficient bounds and symbol bounds.
  have hbound (N k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ξ,
      ‖iteratedFDeriv ℝ N (fun w ↦ iteratedFDeriv ℝ k (a w) ξ) z‖ ≤
        C * (1 + ‖ξ‖) ^ (m - (k : ℝ)) := by
    have hgbound (b : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ tsupport χ,
        ‖iteratedFDeriv ℝ b g z‖ ≤ B := by
      obtain ⟨B, hB⟩ := hcχ.exists_bound_of_continuousOn
        ((hg.continuousOn_iteratedFDerivWithin (m := b) (by simp) hW.uniqueDiffOn).mono hχW)
      refine ⟨max B 0, le_max_right _ _, fun z hz ↦ ?_⟩
      have h := hB z hz
      rw [iteratedFDerivWithin_of_isOpen _ hW (hχW hz)] at h
      exact h.trans (le_max_left _ _)
    have hqbound (b : ℕ) := exists_bound_symbol_comp_linear_frequency U hU m p hp W hW
      φ hφ hφU Θ hΘ hinv (tsupport χ) hcχ hχW b k
    choose B hB hgB using hgbound
    choose C hC hqC using hqbound
    let C' := ∑ b ∈ Finset.range (N + 1), (N.choose b : ℝ) * B b * C (N - b)
    have hC' : 0 ≤ C' := Finset.sum_nonneg (fun b _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB b)) (hC (N - b)))
    refine ⟨C', hC', fun z ξ ↦ ?_⟩
    by_cases hz : z ∈ tsupport χ
    · have heq : (fun w ↦ iteratedFDeriv ℝ k (a w) ξ) =ᶠ[nhds z]
          (fun w ↦ g w • iteratedFDeriv ℝ k (q w) ξ) := by
        filter_upwards [hW.mem_nhds (hχW hz)] with w hw
        exact hfreq k w hw ξ
      rw [(heq.iteratedFDeriv ℝ N).eq_of_nhds]
      have hprod := norm_iteratedFDerivWithin_smul_le hg (hDq k ξ)
        hW.uniqueDiffOn (hχW hz) (n := N) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hW (hχW hz)] at hprod
      apply hprod.trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro b hb
      calc
        _ ≤ (N.choose b : ℝ) * B b *
            (C (N - b) * (1 + ‖ξ‖) ^ (m - (k : ℝ))) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hgB b z hz) (Nat.cast_nonneg _))
            (hqC (N - b) z hz ξ) (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (hB b))
        _ = _ := by ring
    · have heq : (fun w ↦ iteratedFDeriv ℝ k (a w) ξ) =ᶠ[nhds z] (fun _ ↦ 0) := by
        filter_upwards [hzero z hz] with w hw
        have ha0 : a w = 0 := by
          funext η
          simp only [a, g, hw, zero_mul, zero_smul, Pi.zero_apply]
        simp only [ha0, iteratedFDeriv_zero, Pi.zero_apply]
      rw [(heq.iteratedFDeriv ℝ N).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg hC' (by positivity)
  refine ⟨ha, ?_⟩
  intro K hK i j k
  obtain ⟨C, hC, hCb⟩ := hbound (i + j) k
  refine ⟨C, hC, fun x y _ ξ ↦ ?_⟩
  exact (norm_mixed_iteratedFDeriv_le (fun x y ↦ iteratedFDeriv ℝ k (a (x, y)) ξ)
    (hDa k ξ) i j x y).trans (hCb (x, y) ξ)


/-- A cutoff supported inside the valid change-of-frequency region gives an order-m amplitude. -/
theorem isAmplitude_coordinateAmplitude
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol e.source m p)
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (hseg : ∀ z ∈ W, segment ℝ z.2 z.1 ⊆ e.target)
    (hinv : ∀ z ∈ W, (averagedFDeriv e.symm z.1 z.2).IsInvertible)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχW : tsupport χ ⊆ W) :
    IsAmplitude m (coordinateAmplitude e χ p) := by
  /- Stage 1: compactness of each segment inside the open target gives smooth
  parameter dependence of its averaged derivative locally on W. Matrix inversion
  and absolute determinant are smooth on the invertible locus. Stage 2: on the
  compact cutoff support, Θ and Θ inverse are uniformly bounded. The chain rule
  gives one compensating frequency derivative whenever a spatial derivative hits
  Θξ, hence the S^m_(1,0) estimates. Off the closed cutoff support the formula is
  locally zero, so arbitrary totalized values outside W cause no loss of smoothness. -/
  let X := EuclideanSpace ℝ (Fin n)
  have hAvg : ContDiffOn ℝ ∞ (fun z ↦ averagedFDeriv e.symm z.1 z.2) W := by
    let X := EuclideanSpace ℝ (Fin n)
    let J := Set.Icc (0 : ℝ) 1
    let f : J × (X × X) → (X →L[ℝ] X) :=
      fun p ↦ fderiv ℝ e.symm ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2)
    -- The interval carries its usual smooth structure with boundary. Thus all parameters,
    -- including the two endpoints, fall under the compact-parameter integral theorem.
    have ht : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ) ∞
        (fun p : J × (X × X) ↦ (p.1 : ℝ)) :=
      contMDiff_subtypeVal_Icc.comp contMDiff_fst
    have hc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X) ∞
        (fun p : J × (X × X) ↦ (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) :=
      (ht.smul (contDiff_fst.contMDiff.comp contMDiff_snd)).add
        (((contDiff_const.sub contDiff_id).contMDiff.comp ht).smul
          (contDiff_snd.contMDiff.comp contMDiff_snd))
    have hf : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X →L[ℝ] X) ∞
        f (Set.univ ×ˢ W) := by
      intro p hp
      have hmem : (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2 ∈ e.target := by
        apply hseg p.2 hp.2
        rw [segment_eq_image]
        exact ⟨(p.1 : ℝ), p.1.property, by simp [add_comm]⟩
      have hd : ContDiffAt ℝ ∞ (fderiv ℝ e.symm)
          ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) :=
        (hψ.contDiffAt (e.open_target.mem_nhds hmem)).fderiv_right (by simp)
      exact (hd.contMDiffAt.comp p (hc p)).contMDiffWithinAt
    have h := contDiffOn_integral_of_compact_manifold (𝓡∂ 1)
      (volume : Measure J) hW hf
    -- The subtype measure is ordinary Lebesgue measure restricted to [0,1]. Endpoints
    -- have zero measure, so this is exactly the original oriented interval integral.
    convert h using 1
    funext z
    dsimp only [f, J, averagedFDeriv]
    have he := unitInterval.measurePreserving_coe.integral_comp
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
      (fun t ↦ fderiv ℝ e.symm (t • z.1 + (1 - t) • z.2))
    rw [integral_Icc_eq_integral_Ioc] at he
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact he.symm
  have hxTarget (z : X × X) (hz : z ∈ W) : z.1 ∈ e.target :=
    hseg z hz (right_mem_segment ℝ z.2 z.1)
  have hyTarget (z : X × X) (hz : z ∈ W) : z.2 ∈ e.target :=
    hseg z hz (left_mem_segment ℝ z.2 z.1)
  let Jadj : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ] (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro c A; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hAdj : ContDiffOn ℝ ∞
      (fun z ↦ (averagedFDeriv e.symm z.1 z.2).adjoint) W :=
    Jadj.contDiff.comp_contDiffOn hAvg
  have hAdjInv (z : X × X) (hz : z ∈ W) :
      (averagedFDeriv e.symm z.1 z.2).adjoint.IsInvertible := by
    let A := averagedFDeriv e.symm z.1 z.2
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := A.inverse.adjoint)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).inverse_comp_self)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).self_comp_inverse)
  have hΘ : ContDiffOn ℝ ∞ (fun z ↦ coordinateFrequencyChange e z.1 z.2) W := by
    intro z hz
    exact ((hAdjInv z hz).contDiffAt_map_inverse.comp z
      (hAdj.contDiffAt (hW.mem_nhds hz))).contDiffWithinAt
  have hΘinv (z : X × X) (hz : z ∈ W) :
      (coordinateFrequencyChange e z.1 z.2).IsInvertible := (hAdjInv z hz).inverse
  have hφ : ContDiffOn ℝ ∞ (fun z : X × X ↦ e.symm z.1) W := by
    intro z hz
    exact ((hψ.contDiffAt (e.open_target.mem_nhds (hxTarget z hz))).comp z
      contDiffAt_fst).contDiffWithinAt
  -- Invertibility makes both absolute Jacobians smooth; orientation is unrestricted.
  have hdetSmooth (D : X × X → X →L[ℝ] X) (z : X × X)
      (hD : ContDiffAt ℝ ∞ D z) : ContDiffAt ℝ ∞ (fun w ↦ (D w).det) z := by
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ hσ
    apply ContDiffAt.mul contDiffAt_const
    apply contDiffAt_prod
    intro i hi
    simp only [LinearMap.toMatrix_apply]
    exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp z
      (hD.clm_apply contDiffAt_const))
  have hγ : ContDiffOn ℝ ∞ (fun z ↦ coordinateJacobianFactor e z.1 z.2) W := by
    intro z hz
    have hyt := hyTarget z hz
    have hψAt := hψ.contDiffAt (e.open_target.mem_nhds hyt)
    have hDψ : ContDiffAt ℝ ∞ (fun w : X × X ↦ fderiv ℝ e.symm w.2) z :=
      (hψAt.fderiv_right (m := ∞) (by simp)).comp z contDiffAt_snd
    have hdetψ : (fderiv ℝ e.symm z.2).det ≠ 0 := by
      have hforward := (he.contDiffAt
        (e.open_source.mem_nhds (e.map_target hyt))).differentiableAt (by simp)
      have hright : (fderiv ℝ e (e.symm z.2)).comp (fderiv ℝ e.symm z.2) =
          ContinuousLinearMap.id ℝ X := by
        apply (hforward.hasFDerivAt.comp z.2
          (hψAt.differentiableAt (by simp)).hasFDerivAt).unique
        apply (hasFDerivAt_id z.2).congr_of_eventuallyEq
        filter_upwards [e.open_target.mem_nhds hyt] with y hy
        exact e.right_inv hy
      have hd := congrArg ContinuousLinearMap.det hright
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
        LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
      exact right_ne_zero_of_mul_eq_one hd
    have hdetΘ : (coordinateFrequencyChange e z.1 z.2).det ≠ 0 := by
      obtain ⟨A, hA⟩ := hΘinv z hz
      rw [← hA]
      exact A.toLinearEquiv.isUnit_det'.ne_zero
    exact ((hdetSmooth _ z hDψ).abs hdetψ).mul
      ((hdetSmooth _ z (hΘ.contDiffAt (hW.mem_nhds hz))).abs hdetΘ) |>.contDiffWithinAt
  exact isAmplitude_cutoff_linear_frequency e.source e.open_source m p hp W hW
    (fun z ↦ e.symm z.1) hφ (fun z hz ↦ e.map_target (hxTarget z hz))
    (fun z ↦ coordinateFrequencyChange e z.1 z.2) hΘ hΘinv
    (fun z ↦ coordinateJacobianFactor e z.1 z.2) χ hγ hχ hcχ hχW

/-- The coordinate amplitude has uniformly compact spatial-pair support. -/
theorem hasCompactSupport_coordinateAmplitude
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r s) (hχ : HasCompactSupport χ) :
    HasCompactSupport (Function.uncurry (coordinateAmplitude e χ p)) := by
  /- If χ(x,y) is zero, the amplitude vanishes at every frequency. Its ordinary
  support is contained in support χ, and its closed support is contained in the
  compact tsupport χ. This support fact needs no symbol estimates or invertibility. -/
  -- The original cutoff controls every frequency simultaneously.
  apply hχ.of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ (isClosed_tsupport χ)
  intro z hz
  by_contra hzχ
  apply hz
  funext ξ
  simp [Function.uncurry, coordinateAmplitude, image_eq_zero_of_notMem_tsupport hzχ]

/-- Diagonal restriction of the transformed amplitude gives the cotangent formula. -/
theorem coordinateAmplitude_diag
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r s) (x ξ : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) :
    coordinateAmplitude e χ p x x ξ = χ (x, x) • cotangentSymbol e p x ξ := by
  /- Substitute the diagonal frequency identity and cancellation of absolute
  Jacobians into the actual amplitude formula. The only remaining scalar is the
  cutoff on the diagonal. It becomes one only where the cutoff is chosen to be one. -/
  simp only [coordinateAmplitude, coordinateJacobianFactor_diag e he hψ x hx,
    coordinateFrequencyChange_diag e he hψ x hx, mul_one, cotangentSymbol]


set_option linter.unusedVariables false in
/-- On the target, admissible cutoffs realize the actual coordinate conjugation. -/
theorem coordinatePushforward_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ e.source)
    (hPK : HasOperatorSupport K P) (hρone : ∀ x ∈ e '' K, ρ x = 1)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) :
    coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x =
      P (cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχU u) (e.symm x) := by
  /- Expand the two cutoff pullbacks. If ψ(x) belongs to K, the inverse identity
  puts x in e(K), where ρ is one. Otherwise the output support condition makes
  the value of P zero. Thus the output cutoff disappears at every point of the
  target. The input remains an actual Schwartz function, not unrestricted u ∘ e. -/
  rw [coordinatePushforward, ContinuousLinearMap.comp_apply, cutoffPullbackCLM_apply]
  by_cases hxK : e.symm x ∈ K
  · have hρx : ρ x = 1 := hρone x ⟨e.symm x, hxK, e.right_inv hx⟩
    simp only [hρx, one_smul, ContinuousLinearMap.comp_apply]
  · have hzero : P (cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχU u)
        (e.symm x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hxK (hPK.1 _ h))
    simp only [ContinuousLinearMap.comp_apply, hzero, smul_zero]

/-- Two-sided operator support is transported to the compact image under coordinates. -/
theorem hasOperatorSupport_coordinatePushforward
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ e.source)
    (hPK : HasOperatorSupport K P) :
    HasOperatorSupport (e '' K)
      (coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P) := by
  /- The image e(K) is compact, hence closed. Outside it the output is zero,
  either from the target cutoff or from support of P after applying ψ. For input
  support disjoint from e(K), its pullback vanishes on a neighborhood of each
  point of K by continuity of e there. The pulled-back Schwartz support is thus
  disjoint from K, so P kills it. No cutoff-equals-one hypothesis is needed here. -/
  let S : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
    cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχU
  have himage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  constructor
  · -- Output vanishing uses the original support of P and the actual inverse chart.
    intro u
    apply closure_minimal ?_ himage.isClosed
    intro x hx
    by_contra hxK
    apply hx
    rw [coordinatePushforward, ContinuousLinearMap.comp_apply, cutoffPullbackCLM_apply]
    by_cases hxV : x ∈ e.target
    · have hnot : e.symm x ∉ K := fun h ↦ hxK ⟨e.symm x, h, e.right_inv hxV⟩
      have hz : P (S u) (e.symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (hPK.1 _ h))
      change ρ x • P (S u) (e.symm x) = 0
      rw [hz, smul_zero]
    · have hz : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxV (hρV h))
      rw [hz, zero_smul]
  · -- Pulling back a test supported away from e(K) gives a test supported away from K.
    intro u hu
    have hdisjoint : Disjoint (tsupport (S u)) K := by
      rw [Set.disjoint_left]
      intro x hx hxK
      have hnot : e x ∉ tsupport u := fun h ↦
        Set.disjoint_left.mp hu h ⟨x, hxK, rfl⟩
      apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
      filter_upwards [(e.continuousAt (hKU hxK))
        ((isClosed_tsupport u).isOpen_compl.mem_nhds hnot)] with y hy
      change S u y = 0
      dsimp only [S]
      rw [cutoffPullbackCLM_apply, image_eq_zero_of_notMem_tsupport hy, smul_zero]
    have hzero := hPK.2 (S u) hdisjoint
    apply SchwartzMap.ext
    intro x
    simp only [coordinatePushforward, ContinuousLinearMap.comp_apply,
      cutoffPullbackCLM_apply, zero_apply]
    change ρ x • P (S u) (e.symm x) = 0
    rw [hzero]
    simp

/-- The operator is independent of the admissible source and target cutoffs. -/
theorem coordinatePushforward_eq
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ₁ χ₂ ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hcχ₁ : HasCompactSupport χ₁)
    (hχ₁U : tsupport χ₁ ⊆ e.source)
    (hχ₂ : ContDiff ℝ ∞ χ₂) (hcχ₂ : HasCompactSupport χ₂)
    (hχ₂U : tsupport χ₂ ⊆ e.source)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hcρ₁ : HasCompactSupport ρ₁)
    (hρ₁V : tsupport ρ₁ ⊆ e.target)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hcρ₂ : HasCompactSupport ρ₂)
    (hρ₂V : tsupport ρ₂ ⊆ e.target)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ e.source)
    (hPK : HasOperatorSupport K P)
    (hχ₁one : K ⊆ interior {x | χ₁ x = 1})
    (hχ₂one : K ⊆ interior {x | χ₂ x = 1})
    (hρ₁one : ∀ x ∈ e '' K, ρ₁ x = 1) (hρ₂one : ∀ x ∈ e '' K, ρ₂ x = 1) :
    coordinatePushforward e he hψ χ₁ ρ₁ hχ₁ hcχ₁ hχ₁U hρ₁ hcρ₁ hρ₁V P =
      coordinatePushforward e he hψ χ₂ ρ₂ hχ₂ hcχ₂ hχ₂U hρ₂ hcρ₂ hρ₂V P := by
  /- The difference of the two input pullbacks is a Schwartz function vanishing
  on a neighborhood of K, so its closed support is disjoint from K and P kills
  it. On the target remove either output cutoff using output support and its
  value one on e(K). Outside the target both outputs vanish. Pointwise equality
  for all inputs gives equality of continuous linear maps, including smoothing terms. -/
  apply ContinuousLinearMap.ext
  intro u
  let S₁ : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
    cutoffPullbackCLM e.source e.open_source e he χ₁ hχ₁ hcχ₁ hχ₁U
  let S₂ : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
    cutoffPullbackCLM e.source e.open_source e he χ₂ hχ₂ hcχ₂ hχ₂U
  -- Both source cutoffs are identically one on neighborhoods of the original support.
  have hdisjoint : Disjoint (tsupport (S₁ u - S₂ u)) K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
    filter_upwards [isOpen_interior.mem_nhds (hχ₁one hxK),
      isOpen_interior.mem_nhds (hχ₂one hxK)] with y hy₁ hy₂
    have h₁ : χ₁ y = 1 := interior_subset (s := {x | χ₁ x = 1}) hy₁
    have h₂ : χ₂ y = 1 := interior_subset (s := {x | χ₂ x = 1}) hy₂
    change S₁ u y - S₂ u y = 0
    dsimp only [S₁, S₂]
    rw [cutoffPullbackCLM_apply, cutoffPullbackCLM_apply, h₁, h₂]
    simp
  have hmaps : P (S₁ u) = P (S₂ u) := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using hPK.2 (S₁ u - S₂ u) hdisjoint
  -- On the target both output cutoffs disappear; outside it both vanish.
  apply SchwartzMap.ext
  intro x
  by_cases hx : x ∈ e.target
  · rw [coordinatePushforward_apply e he hψ χ₁ ρ₁ hχ₁ hcχ₁ hχ₁U hρ₁ hcρ₁
      hρ₁V P K hKU hPK hρ₁one u x hx,
      coordinatePushforward_apply e he hψ χ₂ ρ₂ hχ₂ hcχ₂ hχ₂U hρ₂ hcρ₂
        hρ₂V P K hKU hPK hρ₂one u x hx]
    exact congrArg (fun v ↦ v (e.symm x)) hmaps
  · have h₁ : ρ₁ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ₁V h))
    have h₂ : ρ₂ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ₂V h))
    simp only [coordinatePushforward, ContinuousLinearMap.comp_apply,
      cutoffPullbackCLM_apply, h₁, h₂, zero_smul]

/-! ## Exact coordinate amplitude and its smoothing remainder -/

open Set Filter

set_option maxSynthPendingDepth 20

private theorem contDiffOn_segmentIntegral_fderiv {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U)
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hW : IsOpen W) (hseg : ∀ z ∈ W, segment ℝ z.2 z.1 ⊆ U) :
    ContDiffOn ℝ ∞
      (fun z ↦ ∫ t in (0 : ℝ)..1, fderiv ℝ g (t • z.1 + (1 - t) • z.2)) W := by
  let X := EuclideanSpace ℝ (Fin n)
  let J := Set.Icc (0 : ℝ) 1
  let f : J × (X × X) → (X →L[ℝ] X) :=
    fun p ↦ fderiv ℝ g ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2)
  -- The interval carries its usual smooth structure with boundary. Thus all parameters,
  -- including the two endpoints, fall under the compact-parameter integral theorem.
  have ht : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ) ∞
      (fun p : J × (X × X) ↦ (p.1 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X) ∞
      (fun p : J × (X × X) ↦ (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) :=
    (ht.smul (contDiff_fst.contMDiff.comp contMDiff_snd)).add
      (((contDiff_const.sub contDiff_id).contMDiff.comp ht).smul
        (contDiff_snd.contMDiff.comp contMDiff_snd))
  have hf : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X →L[ℝ] X) ∞
      f (univ ×ˢ W) := by
    intro p hp
    have hmem : (p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2 ∈ U := by
      apply hseg p.2 hp.2
      rw [segment_eq_image]
      exact ⟨(p.1 : ℝ), p.1.property, by simp [add_comm]⟩
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ g)
        ((p.1 : ℝ) • p.2.1 + (1 - (p.1 : ℝ)) • p.2.2) :=
      (hg.contDiffAt (hU.mem_nhds hmem)).fderiv_right (by simp)
    exact (hd.contMDiffAt.comp p (hc p)).contMDiffWithinAt
  have h := contDiffOn_integral_of_compact_manifold (𝓡∂ 1)
    (volume : Measure J) hW hf
  -- The subtype measure is ordinary Lebesgue measure restricted to [0,1]. Endpoints
  -- have zero measure, so this is exactly the original oriented interval integral.
  convert h using 1
  funext z
  dsimp only [f, J]
  have he := unitInterval.measurePreserving_coe.integral_comp
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)
    (fun t ↦ fderiv ℝ g (t • z.1 + (1 - t) • z.2))
  rw [integral_Icc_eq_integral_Ioc] at he
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact he.symm

/-- The inverse transpose of the averaged derivative preserves the actual oscillatory phase. -/
private theorem coordinateFrequencyChange_phase
    {n : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (x y ξ : EuclideanSpace ℝ (Fin n))
    (hseg : segment ℝ y x ⊆ e.target)
    (hinv : (averagedFDeriv e.symm x y).IsInvertible) :
    inner ℝ (e.symm x - e.symm y) (coordinateFrequencyChange e x y ξ) =
      inner ℝ (x - y) ξ := by
  let A := averagedFDeriv e.symm x y
  have hA : A.adjoint.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := A.inverse.adjoint)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint hinv.inverse_comp_self
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint hinv.self_comp_inverse
  rw [← averagedFDeriv_sub e.target e.open_target e.symm hψ x y hseg]
  change inner ℝ (A (x - y)) (A.adjoint.inverse ξ) = _
  rw [← A.adjoint_inner_right, hA.self_apply_inverse]

open Classical in
/-- A compact smooth spatial-pair cutoff in the target has a compact smooth zero-extended
pullback to the source of the original coordinate change. -/
private theorem exists_compactSmooth_coordinateCutoff
    {n : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχV : tsupport χ ⊆ e.target ×ˢ e.target) :
    ∃ χ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ χ₀ ∧ HasCompactSupport χ₀ ∧
      tsupport χ₀ ⊆ e.source ×ˢ e.source ∧
      ∀ z, χ₀ z = if z ∈ e.source ×ˢ e.source then χ (e z.1, e z.2) else 0 := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let χ₀ : X × X → ℝ := fun z ↦
    if z ∈ e.source ×ˢ e.source then χ (e z.1, e z.2) else 0
  let S := (fun z : X × X ↦ (e.symm z.1, e.symm z.2)) '' tsupport χ
  have hback : ContinuousOn (fun z : X × X ↦ (e.symm z.1, e.symm z.2))
      (e.target ×ˢ e.target) :=
    (e.continuousOn_symm.comp continuousOn_fst (fun z hz ↦ hz.1)).prodMk
      (e.continuousOn_symm.comp continuousOn_snd (fun z hz ↦ hz.2))
  have hS : IsCompact S := hcχ.image_of_continuousOn (hback.mono hχV)
  have hSU : S ⊆ e.source ×ˢ e.source := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨e.map_target (hχV hw).1, e.map_target (hχV hw).2⟩
  have hsupp : Function.support χ₀ ⊆ S := by
    intro z hz
    have hzU : z ∈ e.source ×ˢ e.source := by
      by_contra h
      exact hz (ite_eq_right h)
    have hχne : χ (e z.1, e z.2) ≠ 0 := by
      simpa only [Function.mem_support, χ₀, ite_eq_left hzU] using hz
    refine ⟨(e z.1, e z.2), subset_tsupport _ hχne, ?_⟩
    simp only [e.left_inv hzU.1, e.left_inv hzU.2, Prod.eta]
  have hts : tsupport χ₀ ⊆ S := closure_minimal hsupp hS.isClosed
  have hsmooth : ContDiff ℝ ∞ χ₀ := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ S
    · have hzU := hSU hz
      have hcomp : ContDiffAt ℝ ∞ (fun z : X × X ↦ χ (e z.1, e z.2)) z :=
        hχ.contDiffAt.comp z
          (((he.contDiffAt (e.open_source.mem_nhds hzU.1)).comp z contDiffAt_fst).prodMk
            ((he.contDiffAt (e.open_source.mem_nhds hzU.2)).comp z contDiffAt_snd))
      apply hcomp.congr_of_eventuallyEq
      filter_upwards [(e.open_source.prod e.open_source).mem_nhds hzU] with w hw
      exact ite_eq_left hw
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hz] with w hw
      exact Function.notMem_support.mp (fun h ↦ hw (hsupp h))
  exact ⟨χ₀, hsmooth, hS.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hSU, fun _ ↦ rfl⟩


/-- Compactly supported smooth functions pull back through the actual chart by zero extension. -/
private theorem exists_compactSmooth_coordinatePullback
    {n : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχV : tsupport χ ⊆ e.target) :
    ∃ χ₀ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ χ₀ ∧ HasCompactSupport χ₀ ∧
      tsupport χ₀ ⊆ e.source ∧ (∀ x ∈ e.source, χ₀ x = χ (e x)) ∧
      tsupport χ₀ ⊆ e.symm '' tsupport χ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let χ₀ : X → ℝ := fun x ↦ if x ∈ e.source then χ (e x) else 0
  let S := e.symm '' tsupport χ
  have hS : IsCompact S := hcχ.image_of_continuousOn (e.continuousOn_symm.mono hχV)
  have hSU : S ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hχV hy)
  have hsupp : Function.support χ₀ ⊆ S := by
    intro x hx
    have hxU : x ∈ e.source := by
      by_contra h
      exact hx (ite_eq_right h)
    have hχne : χ (e x) ≠ 0 := by
      simpa only [Function.mem_support, χ₀, ite_eq_left hxU] using hx
    exact ⟨e x, subset_tsupport _ hχne, e.left_inv hxU⟩
  have hts : tsupport χ₀ ⊆ S := closure_minimal hsupp hS.isClosed
  have hsmooth : ContDiff ℝ ∞ χ₀ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ S
    · have hxU := hSU hx
      apply (hχ.contDiffAt.comp x
        (he.contDiffAt (e.open_source.mem_nhds hxU))).congr_of_eventuallyEq
      filter_upwards [e.open_source.mem_nhds hxU] with y hy
      exact ite_eq_left hy
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact Function.notMem_support.mp (fun h ↦ hy (hsupp h))
  exact ⟨χ₀, hsmooth, hS.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hSU, fun x hx ↦ ite_eq_left hx, hts⟩

/-- A compact set inside an open Euclidean region admits a cutoff equal to one nearby. -/
private theorem exists_compact_cutoff_one_near
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : X → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ K ⊆ interior {x | χ x = 1} := by
  obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨O', hO'o, hOO', hO'U, hO'c⟩ :=
    exists_open_between_and_isCompact_closure hOc hU hOU
  obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
  have hχsupport : tsupport χ = closure O' := congrArg closure hsχ
  refine ⟨χ, hχ, by simpa [HasCompactSupport, hχsupport] using hO'c,
    by rwa [hχsupport], ?_⟩
  intro x hx
  apply mem_interior.mpr
  refine ⟨O, ?_, hOo, hKO hx⟩
  intro y hy
  exact (honeχ y).mp (subset_closure hy)

/-- The exact compact source and near-diagonal target cutoffs for coordinate transport. -/
private theorem exists_coordinate_decomposition_cutoffs
    {n : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ e.source)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (hρone : e '' K ⊆ interior {x | ρ x = 1}) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (β : EuclideanSpace ℝ (Fin n) → ℝ)
      (χ χ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ),
      IsOpen W ∧
      (∀ z ∈ W, segment ℝ z.2 z.1 ⊆ e.target) ∧
      (∀ z ∈ W, (averagedFDeriv e.symm z.1 z.2).IsInvertible) ∧
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ e.source ∧
      K ⊆ interior {x | β x = 1} ∧ (∀ x ∈ e.source, β x = ρ (e x)) ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ W ∧
      ContDiff ℝ ∞ χ₀ ∧ HasCompactSupport χ₀ ∧
      tsupport χ₀ ⊆ tsupport β ×ˢ tsupport β ∧
      (∀ z ∈ e.source ×ˢ e.source, χ₀ z = χ (e z.1, e z.2)) ∧
      (∀ x ∈ e '' K, χ =ᶠ[nhds (x, x)] (fun _ ↦ 1)) ∧
      (∀ x, (fun z ↦ β z.1 * β z.2 - χ₀ z) =ᶠ[nhds (x, x)] (fun _ ↦ 0)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  obtain ⟨β, hβ, hcβ, hβU, hβspec, hβsupp⟩ :=
    exists_compactSmooth_coordinatePullback e he ρ hρ hcρ hρV
  have hβone : K ⊆ interior {x | β x = 1} := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have hρnear : ∀ᶠ y in nhds (e x), ρ y = 1 :=
      mem_of_superset (isOpen_interior.mem_nhds (hρone ⟨x, hx, rfl⟩))
        (fun _ h ↦ interior_subset h)
    filter_upwards [e.open_source.mem_nhds (hKU hx),
      (e.continuousOn.continuousAt (e.open_source.mem_nhds (hKU hx))) hρnear] with y hy hρy
    exact (hβspec y hy).trans hρy
  obtain ⟨W, hW, hdiag, hWgood⟩ := exists_coordinateChange_neighborhood
    e he hψ (tsupport ρ) hcρ hρV
  have hdiagC : IsCompact ((fun x : X ↦ (x, x)) '' tsupport ρ) :=
    hcρ.image (continuous_id.prodMk continuous_id)
  obtain ⟨ν, hν, hcν, hνW, hνone⟩ := exists_compact_cutoff_one_near
    ((fun x : X ↦ (x, x)) '' tsupport ρ) W hdiagC hW hdiag
  let χ : X × X → ℝ := fun z ↦ ν z * (ρ z.1 * ρ z.2)
  have hχ : ContDiff ℝ ∞ χ := hν.mul
    ((hρ.comp contDiff_fst).mul (hρ.comp contDiff_snd))
  have hχsupp : tsupport χ ⊆ tsupport ν := by
    apply closure_minimal ?_ (isClosed_tsupport ν)
    intro z hz
    exact subset_tsupport ν (left_ne_zero_of_mul hz)
  have hcχ : HasCompactSupport χ := hcν.of_isClosed_subset (isClosed_tsupport _) hχsupp
  have hχW : tsupport χ ⊆ W := hχsupp.trans hνW
  have hχV : tsupport χ ⊆ e.target ×ˢ e.target := by
    intro z hz
    have hs := (hWgood z (hχW hz)).1
    exact ⟨hs (right_mem_segment ℝ z.2 z.1), hs (left_mem_segment ℝ z.2 z.1)⟩
  obtain ⟨χ₀, hχ₀, hcχ₀, hχ₀U, hχ₀all⟩ :=
    exists_compactSmooth_coordinateCutoff e he χ hχ hcχ hχV
  have hχ₀spec (z : X × X) (hz : z ∈ e.source ×ˢ e.source) :
      χ₀ z = χ (e z.1, e z.2) := by rw [hχ₀all, ite_eq_left hz]
  have hχ₀supp : tsupport χ₀ ⊆ tsupport β ×ˢ tsupport β := by
    apply closure_minimal ?_ ((isClosed_tsupport β).prod (isClosed_tsupport β))
    intro z hz
    have hzU := hχ₀U (subset_tsupport _ hz)
    have hχne : χ (e z.1, e z.2) ≠ 0 := by rwa [← hχ₀spec z hzU]
    have hρne : ρ (e z.1) ≠ 0 ∧ ρ (e z.2) ≠ 0 :=
      mul_ne_zero_iff.mp (right_ne_zero_of_mul hχne)
    exact ⟨subset_tsupport _ (show β z.1 ≠ 0 by rw [hβspec z.1 hzU.1]; exact hρne.1),
      subset_tsupport _ (show β z.2 ≠ 0 by rw [hβspec z.2 hzU.2]; exact hρne.2)⟩
  have hνnear (x : X) (hx : x ∈ tsupport ρ) :
      ν =ᶠ[nhds (x, x)] (fun _ ↦ 1) :=
    mem_of_superset (isOpen_interior.mem_nhds (hνone ⟨x, hx, rfl⟩))
      (fun _ h ↦ interior_subset h)
  have hχnear (x : X) (hx : x ∈ e '' K) : χ =ᶠ[nhds (x, x)] (fun _ ↦ 1) := by
    have hρnear : ρ =ᶠ[nhds x] (fun _ ↦ 1) :=
      mem_of_superset (isOpen_interior.mem_nhds (hρone hx)) (fun _ h ↦ interior_subset h)
    have hρx : ρ x = 1 := hρnear.eq_of_nhds
    have hxs : x ∈ tsupport ρ := subset_tsupport _ (show ρ x ≠ 0 by rw [hρx]; norm_num)
    filter_upwards [hνnear x hxs, hρnear.comp_tendsto continuous_fst.continuousAt,
      hρnear.comp_tendsto continuous_snd.continuousAt] with z hz hz₁ hz₂
    change ρ z.1 = 1 at hz₁
    change ρ z.2 = 1 at hz₂
    change ν z * (ρ z.1 * ρ z.2) = 1
    rw [hz, hz₁, hz₂]
    norm_num
  have hoff (x : X) : (fun z : X × X ↦ β z.1 * β z.2 - χ₀ z) =ᶠ[nhds (x, x)]
      (fun _ ↦ 0) := by
    by_cases hx : x ∈ tsupport β
    · have hxU := hβU hx
      have hexs : e x ∈ tsupport ρ := by
        obtain ⟨y, hy, heq⟩ := hβsupp hx
        rw [← heq, e.right_inv (hρV hy)]
        exact hy
      have hmap : ContinuousAt (fun z : X × X ↦ (e z.1, e z.2)) (x, x) :=
        ((e.continuousOn.continuousAt (e.open_source.mem_nhds hxU)).comp
          continuous_fst.continuousAt).prodMk
          ((e.continuousOn.continuousAt (e.open_source.mem_nhds hxU)).comp
            continuous_snd.continuousAt)
      filter_upwards [(e.open_source.prod e.open_source).mem_nhds ⟨hxU, hxU⟩,
        (hνnear (e x) hexs).comp_tendsto hmap] with z hz hνz
      rw [hχ₀spec z hz, hβspec z.1 hz.1, hβspec z.2 hz.2]
      change ν (e z.1, e z.2) = 1 at hνz
      change _ - ν (e z.1, e z.2) * _ = 0
      rw [hνz, one_mul, sub_self]
    · filter_upwards [continuous_fst.continuousAt
        ((isClosed_tsupport β).isOpen_compl.mem_nhds hx)] with z hz
      have hβz : β z.1 = 0 := image_eq_zero_of_notMem_tsupport hz
      have hχ₀z : χ₀ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz (hχ₀supp h).1)
      rw [hβz, hχ₀z, zero_mul, sub_self]
  exact ⟨W, β, χ, χ₀, hW, fun z hz ↦ (hWgood z hz).1,
    fun z hz ↦ (hWgood z hz).2, hβ, hcβ, hβU, hβone, hβspec,
    hχ, hcχ, hχW, hχ₀, hcχ₀, hχ₀supp, hχ₀spec, hχnear, hoff⟩

open Classical in
/-- The actual spatial and frequency substitutions are valid with compact frequency cutoff. -/
private theorem coordinateAmplitude_regularized_integral
    {n r q : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol e.source m p)
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (hseg : ∀ z ∈ W, segment ℝ z.2 z.1 ⊆ e.target)
    (hinv : ∀ z ∈ W, (averagedFDeriv e.symm z.1 z.2).IsInvertible)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχW : tsupport χ ⊆ W)
    (τ : EuclideanSpace ℝ (Fin n) → ℝ) (hτ : Continuous τ) (hcτ : HasCompactSupport τ)
    (ε : ℝ) (hε : ε ≠ 0)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) :
    (∫ η, ∫ v, if v ∈ e.source then
      τ (ε • η) • χ (x, e v) •
        (Complex.exp (Complex.I * (inner ℝ (e.symm x - v) η : ℂ)) •
          p (e.symm x) η (u (e v))) else 0) =
      ∫ ξ, ∫ y, τ (coordinateFrequencyChange e x y (ε • ξ)) •
        (Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          coordinateAmplitude e χ p x y ξ (u y)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin q)
  let Kx : Set X := {y | (x, y) ∈ tsupport χ}
  let Wx : Set X := {y | (x, y) ∈ W}
  have hWx : IsOpen Wx := hW.preimage (continuous_const.prodMk continuous_id)
  have hKx : IsCompact Kx := (hcχ.image continuous_snd).of_isClosed_subset
    ((isClosed_tsupport χ).preimage (continuous_const.prodMk continuous_id))
    (fun y hy ↦ ⟨(x, y), hy, rfl⟩)
  have hKxW : Kx ⊆ Wx := fun y hy ↦ hχW hy
  have hyTarget (y : X) (hy : y ∈ Wx) : y ∈ e.target :=
    hseg (x, y) hy (left_mem_segment ℝ y x)
  have hAvg : ContDiffOn ℝ ∞ (fun z ↦ averagedFDeriv e.symm z.1 z.2) W :=
    contDiffOn_segmentIntegral_fderiv e.symm e.target e.open_target hψ W hW hseg
  let Jadj : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ] (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro c A; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hAdj : ContDiffOn ℝ ∞
      (fun z ↦ (averagedFDeriv e.symm z.1 z.2).adjoint) W :=
    Jadj.contDiff.comp_contDiffOn hAvg
  have hAdjInv (z : X × X) (hz : z ∈ W) :
      (averagedFDeriv e.symm z.1 z.2).adjoint.IsInvertible := by
    let A := averagedFDeriv e.symm z.1 z.2
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := A.inverse.adjoint)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).inverse_comp_self)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).self_comp_inverse)
  have hΘ : ContDiffOn ℝ ∞ (fun y ↦ coordinateFrequencyChange e x y) Wx := by
    intro y hy
    exact ((hAdjInv (x, y) hy).contDiffAt_map_inverse.comp y
      ((hAdj.contDiffAt (hW.mem_nhds hy)).comp y
        (contDiffAt_const.prodMk contDiffAt_id))).contDiffWithinAt
  have hΘinv (y : X) (hy : y ∈ Wx) : (coordinateFrequencyChange e x y).IsInvertible :=
    (hAdjInv (x, y) hy).inverse
  -- Extend the frequency equivalence arbitrarily off the actual compact support.
  -- Its values there never enter the integral, because the same cutoff vanishes.
  let T : X → X ≃L[ℝ] X := fun y ↦ if hy : y ∈ Wx then
    (hΘinv y hy).choose else ContinuousLinearEquiv.refl ℝ X
  have hT (y : X) (hy : y ∈ Wx) : (T y).toContinuousLinearMap =
      coordinateFrequencyChange e x y := by
    dsimp only [T]
    rw [dite_eq_left hy]
    exact (hΘinv y hy).choose_spec
  let f : X → X → F := fun η v ↦ if v ∈ e.source then
    τ (ε • η) • χ (x, e v) •
      (Complex.exp (Complex.I * (inner ℝ (e.symm x - v) η : ℂ)) •
        p (e.symm x) η (u (e v))) else 0
  let f₁ : X × X → F := fun z ↦
    |(fderiv ℝ e.symm z.1).det| • χ (x, z.1) •
      (Complex.exp (Complex.I * (inner ℝ (e.symm x - e.symm z.1) z.2 : ℂ)) •
        p (e.symm x) z.2 (u z.1))
  have hpCont : Continuous (p (e.symm x)) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    exact (hp.1.contDiffAt ((e.open_source.prod isOpen_univ).mem_nhds
      ⟨e.map_target hx, Set.mem_univ ξ⟩)).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt
  have hdet : ContinuousOn (fun y : X ↦ (fderiv ℝ e.symm y).det) e.target := by
    intro y hy
    have hD := (hψ.contDiffAt (e.open_target.mem_nhds hy)).fderiv_right (m := ∞) (by simp)
    have hd : ContDiffAt ℝ ∞ (fun y : X ↦ (fderiv ℝ e.symm y).det) y := by
      let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
      apply ContDiffAt.sum
      intro σ hσ
      apply ContDiffAt.mul contDiffAt_const
      apply contDiffAt_prod
      intro i hi
      simp only [LinearMap.toMatrix_apply]
      exact ((b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp y
        (hD.clm_apply contDiffAt_const))
    exact hd.continuousAt.continuousWithinAt
  have hf₁ : ContinuousOn f₁ (Wx ×ˢ univ) := by
    intro z hz
    have hy := hyTarget z.1 hz.1
    have hψz := (hψ.continuousOn.continuousAt (e.open_target.mem_nhds hy)).comp
      continuous_fst.continuousAt
    have hdetz := (hdet.continuousAt (e.open_target.mem_nhds hy)).comp
      continuous_fst.continuousAt
    have hphase : ContinuousAt (fun z : X × X ↦
        Complex.exp (Complex.I * (inner ℝ (e.symm x - e.symm z.1) z.2 : ℂ))) z := by
      fun_prop
    exact ((hdetz.abs.smul ((hχ.continuous.comp
      (continuous_const.prodMk continuous_fst)).continuousAt.smul
        (hphase.smul ((hpCont.comp continuous_snd).continuousAt.clm_apply
          ((u.continuous.comp continuous_fst).continuousAt)))))).continuousWithinAt
  have hf₁zero (y : X) (hy : y ∉ Kx) (ξ : X) : f₁ (y, ξ) = 0 := by
    have hχ0 : χ (x, y) = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [f₁, hχ0, zero_smul, smul_zero]
  have hI₁ : Integrable (fun z : X × X ↦ τ (ε • z.2) • f₁ z) := by
    convert integrable_frequency_regularization Wx Kx hWx hKx hKxW f₁ hf₁ hf₁zero
        (fun _ ↦ ContinuousLinearMap.id ℝ X) continuousOn_const
        (fun _ _ ↦ ⟨ContinuousLinearEquiv.refl ℝ X, rfl⟩) τ hτ hcτ ε hε using 1
    rfl
  have hF : Integrable (fun z : X × X ↦
      |(fderiv ℝ e.symm z.1).det| • f z.2 (e.symm z.1))
      ((volume.restrict e.target).prod volume) := by
    have hrestr : Integrable (fun z : X × X ↦ τ (ε • z.2) • f₁ z)
        ((volume.restrict e.target).prod volume) :=
      hI₁.mono_measure (by
        rw [Measure.volume_eq_prod]
        exact Measure.prod_mono Measure.restrict_le_self le_rfl)
    apply hrestr.congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem e.open_target.measurableSet)] with z hz
    obtain ⟨y, η⟩ := z
    have hy : y ∈ e.target := hz
    simp only [f, f₁, ite_eq_left (e.map_target hy), e.right_inv hy]
    exact smul_comm _ _ _
  let f₂ : X × X → F := fun z ↦
    Complex.exp (Complex.I * (inner ℝ (x - z.1) z.2 : ℂ)) •
      coordinateAmplitude e χ p x z.1 z.2 (u z.1)
  have ha := isAmplitude_coordinateAmplitude e he hψ m p hp W hW hseg hinv χ hχ hcχ hχW
  have hf₂ : Continuous f₂ := by
    have ha' : Continuous (fun z : X × X ↦ coordinateAmplitude e χ p x z.1 z.2) :=
      ha.1.continuous.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
    exact (by fun_prop : Continuous (fun z : X × X ↦
      Complex.exp (Complex.I * (inner ℝ (x - z.1) z.2 : ℂ)))).smul
      (ha'.clm_apply (u.continuous.comp continuous_fst))
  have hf₂zero (y : X) (hy : y ∉ Kx) (ξ : X) : f₂ (y, ξ) = 0 := by
    have hχ0 : χ (x, y) = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [f₂, coordinateAmplitude, hχ0, zero_mul, zero_smul, zero_apply, smul_zero]
  have hI₂ := integrable_frequency_regularization Wx Kx hWx hKx hKxW f₂
    hf₂.continuousOn hf₂zero (fun y ↦ coordinateFrequencyChange e x y)
    hΘ.continuousOn hΘinv τ hτ hcτ ε hε
  have hmatch (y : X) (hy : y ∈ e.target) (ξ : X) :
      (|(fderiv ℝ e.symm y).det| * |(T y).toContinuousLinearMap.det|) •
        f (T y ξ) (e.symm y) =
          τ (coordinateFrequencyChange e x y (ε • ξ)) • f₂ (y, ξ) := by
    by_cases hyW : y ∈ Wx
    · have hphase := coordinateFrequencyChange_phase e hψ x y ξ
        (hseg (x, y) hyW) (hinv (x, y) hyW)
      have hTapply (η : X) : T y η = coordinateFrequencyChange e x y η :=
        DFunLike.congr_fun (hT y hyW) η
      simp only [f, f₂, ite_eq_left (e.map_target hy), e.right_inv hy, hT y hyW, hTapply,
        ← (coordinateFrequencyChange e x y).map_smul ε ξ, hphase, coordinateAmplitude,
        coordinateJacobianFactor, smul_apply]
      simp only [← Complex.coe_smul, smul_smul]
      congr 1
      push_cast
      ring
    · have hχ0 : χ (x, y) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hyW (hχW h))
      simp only [f, f₂, ite_eq_left (e.map_target hy), e.right_inv hy, hχ0, coordinateAmplitude,
        zero_mul, zero_smul, zero_apply, smul_zero]
  have hG : Integrable (fun z : X × X ↦
      (|(fderiv ℝ e.symm z.1).det| * |(T z.1).toContinuousLinearMap.det|) •
        f (T z.1 z.2) (e.symm z.1)) ((volume.restrict e.target).prod volume) := by
    have hrestr : Integrable (fun z : X × X ↦
        τ (coordinateFrequencyChange e x z.1 (ε • z.2)) • f₂ z)
        ((volume.restrict e.target).prod volume) :=
      hI₂.mono_measure (by
        rw [Measure.volume_eq_prod]
        exact Measure.prod_mono Measure.restrict_le_self le_rfl)
    apply hrestr.congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem e.open_target.measurableSet)] with z hz
    obtain ⟨y, ξ⟩ := z
    have hy : y ∈ e.target := hz
    exact (hmatch y hy ξ).symm
  have hid := integral_spatial_frequency_substitution e hψ T f
    (fun η v hv ↦ ite_eq_right hv) hF hG
  apply hid.trans
  apply integral_congr_ae
  filter_upwards with ξ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := e.target) (f := fun y ↦ τ (coordinateFrequencyChange e x y (ε • ξ)) • f₂ (y, ξ))]
  · apply setIntegral_congr_fun e.open_target.measurableSet
    intro y hy
    exact hmatch y hy ξ
  · intro y hy
    have hχ0 : χ (x, y) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (hyTarget y (hχW h)))
    simp only [f₂, coordinateAmplitude, hχ0, zero_mul, zero_smul, zero_apply, smul_zero]

/-- Removing the frequency cutoff identifies the near-diagonal coordinate amplitude with
its original source amplitude and the specified compactly supported input pullback. -/
private theorem amplitudeApply_coordinateAmplitude_eq
    {n r q : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol univ m p)
    (W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hW : IsOpen W)
    (hseg : ∀ z ∈ W, segment ℝ z.2 z.1 ⊆ e.target)
    (hinv : ∀ z ∈ W, (averagedFDeriv e.symm z.1 z.2).IsInvertible)
    (χ χ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχW : tsupport χ ⊆ W)
    (hχ₀ : ContDiff ℝ ∞ χ₀) (hcχ₀ : HasCompactSupport χ₀)
    (hχ₀U : tsupport χ₀ ⊆ e.source ×ˢ e.source)
    (hspec : ∀ z ∈ e.source ×ˢ e.source, χ₀ z = χ (e z.1, e z.2))
    (δ : EuclideanSpace ℝ (Fin n) → ℝ) (hδ : ContDiff ℝ ∞ δ)
    (hcδ : HasCompactSupport δ) (hδU : tsupport δ ⊆ e.source)
    (hδone : Prod.snd '' tsupport χ₀ ⊆ {v | δ v = 1})
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) :
    amplitudeApply (localizedAmplitude χ₀ p)
      (cutoffPullbackCLM e.source e.open_source e he δ hδ hcδ hδU u) (e.symm x) =
        amplitudeApply (coordinateAmplitude e χ p) u x := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let τ : ContDiffBump (0 : X) := ⟨1, 2, by norm_num, by norm_num⟩
  let ε : ℕ → ℝ := fun N ↦ 1 / ((N : ℝ) + 1)
  have hε : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεne (N : ℕ) : ε N ≠ 0 := by dsimp [ε]; positivity
  have hτzero : τ 0 = 1 := τ.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [τ]))
  let a := localizedAmplitude χ₀ p
  let v := cutoffPullbackCLM e.source e.open_source e he δ hδ hcδ hδU u
  have ha : IsAmplitude m a := isAmplitude_localizedAmplitude m p hp χ₀ hχ₀
  have hcA : HasCompactSupport (Function.uncurry a) := by
    apply hcχ₀.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_tsupport χ₀)
    intro z hz
    by_contra hout
    apply hz
    funext ξ
    simp only [a, localizedAmplitude, Function.uncurry,
      image_eq_zero_of_notMem_tsupport hout, zero_smul, Pi.zero_apply]
  have hOld := tendsto_amplitudeApply_frequency_regularization m a ha hcA univ isOpen_univ
    (Set.subset_univ _) (fun _ ↦ ContinuousLinearMap.id ℝ X) contDiffOn_const
    (fun _ _ ↦ ⟨ContinuousLinearEquiv.refl ℝ X, rfl⟩) τ τ.contDiff τ.hasCompactSupport
    hτzero ε hε v (e.symm x)
  have hAvg : ContDiffOn ℝ ∞ (fun z ↦ averagedFDeriv e.symm z.1 z.2) W :=
    contDiffOn_segmentIntegral_fderiv e.symm e.target e.open_target hψ W hW hseg
  let Jadj : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ] (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro c A; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hAdj : ContDiffOn ℝ ∞
      (fun z ↦ (averagedFDeriv e.symm z.1 z.2).adjoint) W :=
    Jadj.contDiff.comp_contDiffOn hAvg
  have hAdjInv (z : X × X) (hz : z ∈ W) :
      (averagedFDeriv e.symm z.1 z.2).adjoint.IsInvertible := by
    let A := averagedFDeriv e.symm z.1 z.2
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := A.inverse.adjoint)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).inverse_comp_self)
    · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint ((hinv z hz).self_comp_inverse)
  have hΘ : ContDiffOn ℝ ∞ (fun z ↦ coordinateFrequencyChange e z.1 z.2) W := by
    intro z hz
    exact ((hAdjInv z hz).contDiffAt_map_inverse.comp z
      (hAdj.contDiffAt (hW.mem_nhds hz))).contDiffWithinAt
  have hΘinv (z : X × X) (hz : z ∈ W) :
      (coordinateFrequencyChange e z.1 z.2).IsInvertible := (hAdjInv z hz).inverse
  have hca := hasCompactSupport_coordinateAmplitude e χ p hcχ
  have haW : tsupport (Function.uncurry (coordinateAmplitude e χ p)) ⊆ W := by
    apply Set.Subset.trans ?_ hχW
    apply closure_minimal ?_ (isClosed_tsupport χ)
    intro z hz
    by_contra hout
    apply hz
    funext ξ
    simp only [coordinateAmplitude, Function.uncurry,
      image_eq_zero_of_notMem_tsupport hout, zero_mul, zero_smul, Pi.zero_apply]
  have hNew := tendsto_amplitudeApply_frequency_regularization m (coordinateAmplitude e χ p)
    (isAmplitude_coordinateAmplitude e he hψ m p (hp.restrict (subset_univ _))
      W hW hseg hinv χ hχ hcχ hχW) hca W hW haW
    (fun z ↦ coordinateFrequencyChange e z.1 z.2) hΘ hΘinv
    τ τ.contDiff τ.hasCompactSupport hτzero ε hε u x
  -- For each regularization the two actual double integrals are equal, with both
  -- intermediate joint integrals already proved absolutely integrable.
  have hEqual (N : ℕ) : amplitudeApply
      (fun x y ξ ↦ τ ((ContinuousLinearMap.id ℝ X) (ε N • ξ)) • a x y ξ) v (e.symm x) =
      amplitudeApply (fun x y ξ ↦ τ (coordinateFrequencyChange e x y (ε N • ξ)) •
        coordinateAmplitude e χ p x y ξ) u x := by
    unfold amplitudeApply
    congr 1
    have hcomm (y ξ : X) :
        Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
          (τ (coordinateFrequencyChange e x y (ε N • ξ)) •
            coordinateAmplitude e χ p x y ξ (u y)) =
        τ (coordinateFrequencyChange e x y (ε N • ξ)) •
          (Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
            coordinateAmplitude e χ p x y ξ (u y)) := smul_comm _ _ _
    simp_rw [smul_apply, hcomm]
    refine Eq.trans ?_ (coordinateAmplitude_regularized_integral e he hψ m p
      (hp.restrict (subset_univ _)) W hW hseg hinv χ hχ hcχ hχW
      τ (show Continuous τ from (show ContDiff ℝ ∞ τ from τ.contDiff).continuous)
      τ.hasCompactSupport (ε N) (hεne N) u x hx)
    apply integral_congr_ae
    filter_upwards with η
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ e.source
    · have hspec' : χ₀ (e.symm x, y) = χ (x, e y) := by
        simpa only [e.right_inv hx] using hspec (e.symm x, y) ⟨e.map_target hx, hy⟩
      by_cases hcut : χ₀ (e.symm x, y) = 0
      · have hχcut : χ (x, e y) = 0 := hspec'.symm.trans hcut
        simp only [a, localizedAmplitude, hcut, hχcut, zero_smul, smul_zero, zero_apply,
          ite_eq_left hy]
      · have hδy : δ y = 1 := hδone ⟨(e.symm x, y), subset_tsupport _ hcut, rfl⟩
        simp only [a, localizedAmplitude, smul_apply, v, cutoffPullbackCLM_apply, hδy,
          one_smul, hspec', ContinuousLinearMap.id_apply, ite_eq_left hy]
        simp only [← Complex.coe_smul, smul_smul]
        congr 1
        ring
    · have hχ0 : χ₀ (e.symm x, y) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hy (hχ₀U h).2)
      simp only [a, localizedAmplitude, hχ0, zero_smul, smul_zero, zero_apply, ite_eq_right hy]
  -- Uniqueness of limits identifies the original iterated amplitude integrals.
  exact tendsto_nhds_unique hOld (hNew.congr' (Filter.Eventually.of_forall (fun N ↦
    (hEqual N).symm)))

/-- The actual coordinate conjugate of a smooth kernel has a compact smooth kernel.
The two given cutoffs supply compactness, so the original kernel need not be compact. -/
private theorem exists_compactSmoothKernel_coordinatePushforward {n r s : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)))
    (hk : ContDiff ℝ ∞ (Function.uncurry k))
    (hP : ∀ u x, P u x = ∫ y, k x y (u y)) :
    ∃ k' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)),
      ContDiff ℝ ∞ (Function.uncurry k') ∧ HasCompactSupport (Function.uncurry k') ∧
      ∀ u x, coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x =
        ∫ y, k' x y (u y) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)
  let V := e.target ×ˢ e.target
  let S := tsupport ρ ×ˢ (e '' tsupport χ)
  have hS : IsCompact S := hcρ.prod
    (hcχ.image_of_continuousOn (e.continuousOn.mono hχU))
  have hSV : S ⊆ V := by
    rintro z ⟨hz, y, hy, hyz⟩
    exact ⟨hρV hz, hyz ▸ e.map_source (hχU hy)⟩
  let a : X × X → H := fun z ↦
    (ρ z.1 * χ (e.symm z.2) * |(fderiv ℝ e.symm z.2).det|) •
      k (e.symm z.1) (e.symm z.2)
  let k' : X → X → H := fun x y ↦ if (x, y) ∈ V then a (x, y) else 0
  -- The support is controlled by the original output cutoff and the image of the input cutoff.
  have hsupp : Function.support (Function.uncurry k') ⊆ S := by
    intro z hz
    have hzV : z ∈ V := by
      by_contra h
      exact hz (by simp only [Function.uncurry, k', ite_eq_right h])
    have hρz : ρ z.1 ≠ 0 := by
      intro h
      exact hz (by simp only [Function.uncurry, k', ite_eq_left hzV, a, h,
        zero_mul, zero_smul])
    have hχz : χ (e.symm z.2) ≠ 0 := by
      intro h
      exact hz (by simp only [Function.uncurry, k', ite_eq_left hzV, a, h,
        mul_zero, zero_mul, zero_smul])
    exact ⟨subset_tsupport _ hρz, e.symm z.2, subset_tsupport _ hχz,
      e.right_inv hzV.2⟩
  have hts : tsupport (Function.uncurry k') ⊆ S := closure_minimal hsupp hS.isClosed
  -- The absolute spatial Jacobian is smooth because the derivative of this same inverse
  -- chart is invertible. This accommodates either orientation of the coordinate map.
  have hdet (y : X) (hy : y ∈ e.target) :
      ContDiffAt ℝ ∞ (fun w ↦ |(fderiv ℝ e.symm w).det|) y := by
    have hψAt := hψ.contDiffAt (e.open_target.mem_nhds hy)
    have hD := hψAt.fderiv_right (m := ∞) (by simp)
    have hs : ContDiffAt ℝ ∞ (fun w ↦ (fderiv ℝ e.symm w).det) y := by
      let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
      apply ContDiffAt.sum
      intro σ hσ
      apply ContDiffAt.mul contDiffAt_const
      apply contDiffAt_prod
      intro i hi
      simp only [LinearMap.toMatrix_apply]
      exact (b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp y
        (hD.clm_apply contDiffAt_const)
    apply hs.abs
    have hforward := (he.contDiffAt
      (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
    have hright : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
        ContinuousLinearMap.id ℝ X := by
      apply (hforward.hasFDerivAt.comp y
        (hψAt.differentiableAt (by simp)).hasFDerivAt).unique
      apply (hasFDerivAt_id y).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact e.right_inv hz
    have hd := congrArg ContinuousLinearMap.det hright
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
    exact right_ne_zero_of_mul_eq_one hd
  have hsmooth : ContDiff ℝ ∞ (Function.uncurry k') := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ S
    · have hzV := hSV hz
      have hx := (hψ.contDiffAt (e.open_target.mem_nhds hzV.1)).comp z contDiffAt_fst
      have hy := (hψ.contDiffAt (e.open_target.mem_nhds hzV.2)).comp z contDiffAt_snd
      have ha : ContDiffAt ℝ ∞ a z :=
        (((hρ.contDiffAt.comp z contDiffAt_fst).mul (hχ.contDiffAt.comp z hy)).mul
          ((hdet z.2 hzV.2).comp z contDiffAt_snd)).smul
            (hk.contDiffAt.comp z (hx.prodMk hy))
      apply ha.congr_of_eventuallyEq
      filter_upwards [(e.open_target.prod e.open_target).mem_nhds hzV] with w hw
      exact ite_eq_left hw
    · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hz] with w hw
      exact Function.notMem_support.mp (fun h ↦ hw (hsupp h))
  refine ⟨k', hsmooth, hS.of_isClosed_subset (isClosed_tsupport _) hts, ?_⟩
  intro u x
  -- First keep the exact pullback Schwartz input; only then apply the original kernel identity.
  change cutoffPullbackCLM e.target e.open_target e.symm hψ ρ hρ hcρ hρV
    (P (cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχU u)) x = _
  rw [cutoffPullbackCLM_apply, hP]
  simp only [cutoffPullbackCLM_apply]
  have hmap (y : X) : k (e.symm x) y (χ y • u (e y)) =
      χ y • k (e.symm x) y (u (e y)) :=
    ((k (e.symm x) y).restrictScalars ℝ).map_smul _ _
  simp_rw [hmap]
  by_cases hx : x ∈ e.target
  · let f : X → EuclideanSpace ℂ (Fin s) := fun z ↦
      χ z • k (e.symm x) z (u (e z))
    have hzero (z : X) (hz : z ∉ e.source) : f z = 0 := by
      have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hχU h))
      simp only [f, hχz, zero_smul]
    have hchange : (∫ z, f z) =
        ∫ y in e.target, |(fderiv ℝ e.symm y).det| • f (e.symm y) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      exact integral_target_eq_integral_abs_det_fderiv_smul volume (f := e.symm)
        (fun y hy ↦ ((hψ.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
          (by simp)).hasFDerivAt) f
    change ρ x • (∫ z, f z) = _
    rw [hchange, ← integral_smul]
    have hout (y : X) (hy : y ∉ e.target) : k' x y (u y) = 0 := by
      simp only [k', show (x, y) ∉ V from fun h ↦ hy h.2, ↓reduceIte,
        zero_apply]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    apply setIntegral_congr_fun e.open_target.measurableSet
    intro y hy
    simp only [f, k', show (x, y) ∈ V from ⟨hx, hy⟩, ↓reduceIte, a,
      e.right_inv hy, smul_apply, smul_smul]
    congr 1
    ring
  · have hρx : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρV h))
    simp only [hρx, zero_smul]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [] with y
    simp only [k', show (x, y) ∉ V from fun h ↦ hx h.1, ↓reduceIte,
      zero_apply, Pi.zero_apply]

/-- A common closed spatial control for an amplitude controls its actual operator on both sides. -/
private theorem hasOperatorSupport_amplitudeOperator {n r q : ℕ} (m : ℝ)
    (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
    (hsupp : HasCompactSupport (Function.uncurry a))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (hAK : tsupport (Function.uncurry a) ⊆ K ×ˢ K) :
    HasOperatorSupport K (amplitudeOperator m a ha hsupp) := by
  have hzero (x y : EuclideanSpace ℝ (Fin n)) (hxy : (x, y) ∉ K ×ˢ K)
      (ξ : EuclideanSpace ℝ (Fin n)) : a x y ξ = 0 := by
    have hz : Function.uncurry a (x, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hxy (hAK h))
    exact congrFun hz ξ
  constructor
  · -- Outside the output control the amplitude vanishes before either integration.
    intro u
    apply closure_minimal _ hK
    intro x hx
    by_contra hxK
    apply hx
    rw [amplitudeOperator_apply]
    have hz (y ξ : EuclideanSpace ℝ (Fin n)) : a x y ξ = 0 :=
      hzero x y (fun h ↦ hxK h.1) ξ
    simp [amplitudeApply, hz]
  · -- At every input point, either the amplitude or the disjoint Schwartz input vanishes.
    intro u hu
    apply SchwartzMap.ext
    intro x
    rw [amplitudeOperator_apply]
    have hz (y ξ : EuclideanSpace ℝ (Fin n)) : a x y ξ (u y) = 0 := by
      by_cases hy : y ∈ K
      · have huy : u y = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ Set.disjoint_left.mp hu h hy)
        rw [huy, map_zero]
      · rw [hzero x y (fun h ↦ hy h.2) ξ]
        rfl
    change amplitudeApply a u x = 0
    simp [amplitudeApply, hz]

/-- The original coordinate conjugate is a compact amplitude plus a genuine smoothing
symbol, and the amplitude keeps the complete uncut germ along the target diagonal. -/
theorem exists_coordinatePushforward_amplitude
    {n r s : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol univ m p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ e.source)
    (hPK : HasOperatorSupport K P) (hχone : K ⊆ interior {x | χ x = 1})
    (hρone : e '' K ⊆ interior {x | ρ x = 1}) :
    ∃ (a : AmplitudeFunction n r s) (b : SymbolFunction n r s),
      IsAmplitude m a ∧ HasCompactSupport (Function.uncurry a) ∧
      IsSmoothingSymbol univ b ∧ HasCompactSupport b ∧
      (∀ u x, coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x =
        amplitudeApply a u x + quantize b u x) ∧
      (∀ x ∈ e.target, Function.uncurry a =ᶠ[nhds (x, x)]
        Function.uncurry (coordinateAmplitude e (fun _ ↦ 1) p)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  obtain ⟨W, β, γ, γ₀, hW, hseg, hinv, hβ, hcβ, hβU, hβone, hβspec,
    hγ, hcγ, hγW, hγ₀, hcγ₀, hγ₀supp, hγ₀spec, hγnear, hoff⟩ :=
    exists_coordinate_decomposition_cutoffs e he hψ K hKU ρ hρ hcρ hρV hρone
  have hKβ : K ⊆ tsupport β := by
    intro x hx
    have hβx : β x = 1 := interior_subset (s := {x | β x = 1}) (hβone hx)
    exact subset_tsupport _ (show β x ≠ 0 by rw [hβx]; norm_num)
  obtain ⟨δ, hδ, hcδ, hδU, hδone⟩ :=
    exists_compact_cutoff_one_near (tsupport β) e.source hcβ e.open_source hβU
  have hδK : K ⊆ interior {x | δ x = 1} := hKβ.trans hδone
  have hδγ : Prod.snd '' tsupport γ₀ ⊆ {x | δ x = 1} := by
    rintro x ⟨z, hz, rfl⟩
    exact interior_subset (hδone (hγ₀supp hz).2)
  have hρK (x : X) (hx : x ∈ e '' K) : ρ x = 1 := interior_subset (s := {x | ρ x = 1}) (hρone hx)
  have hpsupp : tsupport p ⊆ K :=
    tsupport_symbol_subset_of_hasOperatorSupport m p hp P hP K hK.isClosed hPK
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
  obtain ⟨k, hk, _, hkQ⟩ := exists_compactSmoothKernel_of_smoothingSymbol
    (amplitudeSymbol R) hsmoothR Q hQ (tsupport β) hcβ hQK
  obtain ⟨k', hk', hck', hk'Q⟩ := exists_compactSmoothKernel_coordinatePushforward e he hψ
    δ ρ hδ hcδ hδU hρ hcρ hρV Q k hk hkQ
  let b := compactKernelSymbol k'
  have hb : IsSmoothingSymbol univ b := isSmoothingSymbol_compactKernelSymbol k' hk' hck'
  have hcb : HasCompactSupport b := hasCompactSupport_compactKernelSymbol k' hk' hck'
  have hres (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      coordinatePushforward e he hψ δ ρ hδ hcδ hδU hρ hcρ hρV Q u x = quantize b u x :=
    (hk'Q u x).trans (quantize_compactKernelSymbol k' hk' hck' u x).symm
  let a := coordinateAmplitude e γ p
  have ha : IsAmplitude m a := isAmplitude_coordinateAmplitude e he hψ m p
    (hp.restrict (subset_univ _)) W hW hseg hinv γ hγ hcγ hγW
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_coordinateAmplitude e γ p hcγ
  let S := cutoffPullbackCLM (r := r) e.source e.open_source e he δ hδ hcδ hδU
  have hnear (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      ρ x • amplitudeApply A (S u) (e.symm x) = amplitudeApply a u x := by
    by_cases hx : x ∈ e.target
    · have hid := amplitudeApply_coordinateAmplitude_eq e he hψ m p hp W hW hseg hinv
        γ γ₀ hγ hcγ hγW hγ₀ hcγ₀ (hγ₀supp.trans (prod_mono hβU hβU)) hγ₀spec
        δ hδ hcδ hδU hδγ u x hx
      change amplitudeApply A (S u) (e.symm x) = amplitudeApply a u x at hid
      by_cases hxK : x ∈ e '' K
      · rw [hρK x hxK, one_smul, hid]
      · have hnot : e.symm x ∉ K := fun h ↦ hxK ⟨e.symm x, h, e.right_inv hx⟩
        have hp0 : p (e.symm x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (hpsupp h))
        have hz : amplitudeApply A (S u) (e.symm x) = 0 := by
          simp only [amplitudeApply, A, localizedAmplitude, hp0, Pi.zero_apply,
            smul_zero, zero_apply, integral_zero]
        rw [hz] at hid
        rw [hz, smul_zero]
        exact hid
    · have hρx : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρV h))
      have hγx (y : X) : γ (x, y) = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦
        hx (hseg (x, y) (hγW h) (right_mem_segment ℝ y x)))
      simp only [hρx, zero_smul, amplitudeApply, a, coordinateAmplitude, hγx,
        zero_mul, zero_smul, zero_apply, smul_zero, integral_zero]
  have happly (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x =
        amplitudeApply a u x + quantize b u x := by
    rw [coordinatePushforward_eq e he hψ χ δ ρ ρ hχ hcχ hχU hδ hcδ hδU
      hρ hcρ hρV hρ hcρ hρV P K hKU hPK hχone hδK hρK hρK]
    simp only [coordinatePushforward, ContinuousLinearMap.comp_apply, cutoffPullbackCLM_apply]
    change ρ x • P (S u) (e.symm x) = _
    rw [hsplit, smul_add, hnear]
    congr 1
    rw [← amplitudeOperator_apply m R hR hcR (S u) (e.symm x)]
    change ρ x • Q (S u) (e.symm x) = quantize b u x
    simpa only [coordinatePushforward, ContinuousLinearMap.comp_apply, cutoffPullbackCLM_apply]
      using hres u x
  refine ⟨a, b, ha, hca, hb, hcb, happly, ?_⟩
  -- All cutoff jets are absent from the diagonal germ. Outside the original image
  -- support, the entire original symbol vanishes locally at every frequency.
  intro x hx
  by_cases hxK : x ∈ e '' K
  · filter_upwards [hγnear x hxK] with z hz
    funext ξ
    simp only [Function.uncurry, a, coordinateAmplitude, hz]
  · have hnot : e.symm x ∉ K := fun h ↦ hxK ⟨e.symm x, h, e.right_inv hx⟩
    have hmap : ContinuousAt (fun z : X × X ↦ e.symm z.1) (x, x) :=
      (hψ.continuousOn.continuousAt (e.open_target.mem_nhds hx)).comp
        continuous_fst.continuousAt
    have hpnear : ∀ᶠ z : X × X in nhds (x, x), e.symm z.1 ∉ K :=
      hmap (hK.isClosed.isOpen_compl.mem_nhds hnot)
    filter_upwards [hpnear] with z hz
    have hp0 : p (e.symm z.1) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hpsupp h))
    funext ξ
    simp only [Function.uncurry, a, coordinateAmplitude, hp0, Pi.zero_apply, smul_zero]

/-- On an open spatial domain, equality of the actual symbols preserves every mixed estimate. -/
theorem IsSymbol.congr_on {n r s : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {m : ℝ} {p q : SymbolFunction n r s} (hp : IsSymbol U m p)
    (heq : ∀ x ∈ U, p x = q x) : IsSymbol U m q := by
  refine ⟨hp.1.congr (fun z hz ↦ (congrFun (heq z.1 hz.1) z.2).symm), ?_⟩
  intro K hKU hK i j
  obtain ⟨C, hC, hbound⟩ := hp.2 K hKU hK i j
  refine ⟨C, hC, fun x hx ξ ↦ ?_⟩
  have hnear : (fun y ↦ iteratedFDeriv ℝ j (p y) ξ) =ᶠ[nhds x]
      (fun y ↦ iteratedFDeriv ℝ j (q y) ξ) := by
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    rw [heq y hy]
  change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
  rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hbound x hx ξ

/-- SG 3.12 and (3.16): actual conjugation has an exact symbol with the cotangent leading class. -/
theorem exists_symbol_coordinatePushforward
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
    ∃ q : SymbolFunction n r s, IsSymbol Set.univ m q ∧
      (∀ u x, coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x =
        quantize q u x) ∧ IsSymbol e.target (m - 1) (q - cotangentSymbol e p) := by
  -- Use one exact compact amplitude and its smoothing remainder for the conjugate.
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
  refine ⟨q, hq, fun u x ↦ (happly u x).trans (hsum u x).symm, ?_⟩
  -- The first amplitude remainder and diagonal Jacobian cancellation give the class.
  have hfirst := hasSymbolExpansion_amplitudeSymbol m a ha hca 1
  simp only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero] at hfirst
  have hlow : IsSymbol univ (m - 1) (q - fun x ξ ↦ a x x ξ) := by
    convert hfirst.add isOpen_univ (hb (m - 1)) using 1
    ext x ξ v
    simp only [q, Pi.add_apply, Pi.sub_apply, add_apply, sub_apply]
    abel_nf
  apply (hlow.restrict (subset_univ e.target)).congr_on e.open_target
  intro x hx
  funext ξ
  have hsame : a x x ξ = coordinateAmplitude e (fun _ ↦ 1) p x x ξ :=
    congrFun (hgerm x hx).eq_of_nhds ξ
  simp only [Pi.sub_apply, hsame, coordinateAmplitude_diag e he hψ, hx, one_smul]

open ContinuousLinearMap in
/-- SG 3.14: any exact target symbol of the transported operator has the cotangent class. -/
theorem principalSymbolClass_coordinatePushforward
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
    (hρone : e '' K ⊆ interior {x | ρ x = 1})
    (q : symbolSpace e.target e.open_target m r s)
    (hq : ∀ u x, x ∈ e.target →
      coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P u x =
        quantize q.val u x) :
    principalSymbolClass e.target e.open_target m r s q =
      principalSymbolClass e.target e.open_target m r s
        ⟨cotangentSymbol e p,
          isSymbol_cotangentSymbol e he hψ m p (hp.restrict (Set.subset_univ _))⟩ := by
  classical
  obtain ⟨a, ha, hact, hrem⟩ := exists_symbol_coordinatePushforward
    e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV m p hp P hP K hK hKU hPK hχone hρone
  -- Localize both exact symbols by the same compact spatial cutoff. The existing
  -- global injectivity theorem then identifies their values at every target point.
  have heq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ e.target) : q.val x = a x := by
    obtain ⟨δ, hδV, hcδ, hδ, _, hδx⟩ :=
      exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (e.open_target.mem_nhds hx)
    let b := zeroExtendedSymbol e.target δ q.val
    let c := zeroExtendedSymbol e.target δ a
    have hb : IsSymbol Set.univ m b :=
      isSymbol_zeroExtendedSymbol e.target e.open_target m δ hδ hcδ hδV q.val q.property
    have hc : IsSymbol Set.univ m c :=
      isSymbol_zeroExtendedSymbol e.target e.open_target m δ hδ hcδ hδV a
        (ha.restrict (Set.subset_univ _))
    have hcut (d : SymbolFunction n r s) (u : 𝓢(EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℂ (Fin r))) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.target) :
        quantize (zeroExtendedSymbol e.target δ d) u y =
          (δ y : ℂ) • quantize d u y := by
      simp only [quantize, zeroExtendedSymbol_apply_of_mem _ _ _ _ _ hy, smul_apply]
      simp_rw [smul_comm (Complex.exp _)]
      rw [integral_smul, smul_comm]
    have hbc : b = c := symbol_eq_of_quantize_eq m m b c hb hc (by
      intro u y
      by_cases hy : y ∈ e.target
      · change quantize (zeroExtendedSymbol e.target δ q.val) u y =
          quantize (zeroExtendedSymbol e.target δ a) u y
        rw [hcut _ _ _ hy, hcut _ _ _ hy, ← hq u y hy, ← hact u y]
      · simp [b, c, quantize, zeroExtendedSymbol, hy])
    funext ξ
    have hv := congrArg (fun d : SymbolFunction n r s ↦ d x ξ) hbc
    simpa [b, c, zeroExtendedSymbol, hx, hδx] using hv
  -- Openness upgrades the pointwise identification to equality of every mixed
  -- derivative, so the original lower-order estimate passes to the supplied q.
  apply (principalSymbolClass_eq_iff e.open_target _ _).mpr
  refine ⟨hrem.1.congr (fun z hz ↦ ?_), ?_⟩
  · change q.val z.1 z.2 - _ = a z.1 z.2 - _
    rw [heq z.1 hz.1]
  · intro C hCV hC i j
    obtain ⟨B, hB, hbound⟩ := hrem.2 C hCV hC i j
    refine ⟨B, hB, fun x hx ξ ↦ ?_⟩
    have hnear : (fun y ↦ iteratedFDeriv ℝ j ((q.val - cotangentSymbol e p) y) ξ)
        =ᶠ[nhds x] (fun y ↦ iteratedFDeriv ℝ j ((a - cotangentSymbol e p) y) ξ) := by
      filter_upwards [e.open_target.mem_nhds (hCV hx)] with y hy
      change iteratedFDeriv ℝ j (q.val y - cotangentSymbol e p y) ξ = _
      rw [heq y hy]
      rfl
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [(hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound x hx ξ

end AtiyahSinger

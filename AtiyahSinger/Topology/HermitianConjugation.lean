/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import Mathlib.Algebra.Star.Module

/-!
# A Hermitian metric compatible with a conjugate-linear involution

Public module ID: M1880.

Average the supplied metric with its conjugate pullback along the actual
continuous involution. The resulting metric is positive definite and makes
that same involution antiunitary. This finite averaging requires no compactness
or paracompactness of the base and never assumes a metric exists independently
of the supplied one.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology

/-- A continuous conjugate-linear involution is antiunitary for a conjugate-averaged metric. -/
theorem exists_hermitianMetric_invariant_of_conjugateLinear_involution
    {X : Type*} [TopologicalSpace X] (E : X → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] (h : ContinuousHermitianMetric E)
    (J : ∀ x, E x ≃ₗ⋆[ℂ] E x) (hJ : ∀ x, Function.Involutive (J x))
    (hcontinuous : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, J z.proj z.snd⟩ : TotalSpace Unit E))) :
    ∃ h₀ : ContinuousHermitianMetric E, ∀ x (v w : E x),
      (h₀.toCore x).inner (J x v) (J x w) = star ((h₀.toCore x).inner v w) := by
  have hpair : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (⟨z.proj, (J z.proj z.snd.1, J z.proj z.snd.2)⟩ : TotalSpace Unit (E ×ᵇ E))) := by
    have hi : Topology.IsInducing (fun z : TotalSpace Unit (E ×ᵇ E) ↦
        ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
          (⟨z.proj, z.snd.2⟩ : TotalSpace Unit E))) := ⟨rfl⟩
    exact hi.continuous_iff.mpr
      ((hcontinuous.comp continuous_sum_fst).prodMk (hcontinuous.comp continuous_sum_snd))
  -- Conjugating the pulled-back form restores complex linearity in its second argument.
  let h' : ContinuousHermitianMetric E :=
    { toCore x :=
        { inner := fun v w ↦ star ((h.toCore x).inner (J x v) (J x w))
          conj_inner_symm v w := by
            simpa only [starRingEnd_apply, star_star] using
              ((h.toCore x).conj_inner_symm (J x w) (J x v)).symm
          re_inner_nonneg v := by simpa using (h.toCore x).re_inner_nonneg (J x v)
          add_left v w z := by simp only [map_add, (h.toCore x).add_left, star_add]
          smul_left v w c := by
            simp only [map_smulₛₗ, (h.toCore x).smul_left, starRingEnd_apply, star_star,
              star_mul']
          definite v hv := by
            apply (J x).injective
            rw [(J x).map_zero]
            exact (h.toCore x).definite (J x v) (star_eq_zero.mp hv) }
      continuous_pairing := continuous_star.comp (h.continuous_pairing.comp hpair)
      isFiniteRank := h.isFiniteRank }
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  refine ⟨h.convexCombination h' half, ?_⟩
  intro x v w
  -- The involution exchanges the two summands, and equal real weights preserve their sum.
  change ((1 - (half : ℝ) : ℝ) : ℂ) * (h.toCore x).inner (J x v) (J x w) +
      ((half : ℝ) : ℂ) * star ((h.toCore x).inner (J x (J x v)) (J x (J x w))) =
    star (((1 - (half : ℝ) : ℝ) : ℂ) * (h.toCore x).inner v w +
      ((half : ℝ) : ℂ) * star ((h.toCore x).inner (J x v) (J x w)))
  rw [hJ x v, hJ x w]
  simp only [star_add, star_mul', star_star]
  norm_num [half]
  ring

end AtiyahSinger.ComplexBundle

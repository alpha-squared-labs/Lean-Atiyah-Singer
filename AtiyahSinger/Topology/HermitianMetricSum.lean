/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric

/-!
# The orthogonal sum of continuous Hermitian metrics

Public module ID: M1889.

The ordinary direct-sum bundle has the original fibers `E x × F x` and the
existing induced total topology. Its Hermitian form is the sum of the two
original forms. This does not install the ordinary product supremum norm as
an inner-product norm. The explicit Core can later supply its own local norm
without changing any bundle topology. This is the metric used in the standard
Thom direct-sum formula, KA IV.1.7--1.8 and SG Appendix C.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle
open scoped ComplexConjugate

attribute [local instance] sumTopology

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)

/-- The orthogonal sum pairing is continuous on the original double-sum total space. -/
theorem continuous_sum_pairing :
    Continuous (fun z : TotalSpace Unit ((E ×ᵇ F) ×ᵇ (E ×ᵇ F)) ↦
      (hE.toCore z.proj).inner z.snd.1.1 z.snd.2.1 +
        (hF.toCore z.proj).inner z.snd.1.2 z.snd.2.2) := by
  /- Regroup the four original fiber entries into the E pair and the F pair.
  Each regrouping is continuous for the induced sum topologies, since its
  components are the appropriate original total-space projections. Compose
  these maps with the two given continuous pairings and add their values.
  No local trivialization, rank bound, compactness or metric existence is used. -/
  let pairE : TotalSpace Unit ((E ×ᵇ F) ×ᵇ (E ×ᵇ F)) → TotalSpace Unit (E ×ᵇ E) :=
    fun z ↦ ⟨z.proj, z.snd.1.1, z.snd.2.1⟩
  let pairF : TotalSpace Unit ((E ×ᵇ F) ×ᵇ (E ×ᵇ F)) → TotalSpace Unit (F ×ᵇ F) :=
    fun z ↦ ⟨z.proj, z.snd.1.2, z.snd.2.2⟩
  -- Test each regrouping against the two projections defining the original sum topology.
  have hEpair : Continuous pairE := by
    apply continuous_induced_rng.mpr
    exact ((continuous_sum_fst (E := E) (F := F)).comp
      (continuous_sum_fst (E := E ×ᵇ F) (F := E ×ᵇ F))).prodMk
      ((continuous_sum_fst (E := E) (F := F)).comp
        (continuous_sum_snd (E := E ×ᵇ F) (F := E ×ᵇ F)))
  have hFpair : Continuous pairF := by
    apply continuous_induced_rng.mpr
    exact ((continuous_sum_snd (E := E) (F := F)).comp
      (continuous_sum_fst (E := E ×ᵇ F) (F := E ×ᵇ F))).prodMk
      ((continuous_sum_snd (E := E) (F := F)).comp
        (continuous_sum_snd (E := E ×ᵇ F) (F := E ×ᵇ F)))
  exact (hE.continuous_pairing.comp hEpair).add (hF.continuous_pairing.comp hFpair)

/-- The standard orthogonal direct-sum metric, retaining both original summands. -/
def sum : ContinuousHermitianMetric (E ×ᵇ F) where
  toCore x :=
    { inner := fun u v ↦ (hE.toCore x).inner u.1 v.1 + (hF.toCore x).inner u.2 v.2
      conj_inner_symm u v := by
        simp only [map_add, (hE.toCore x).conj_inner_symm,
          (hF.toCore x).conj_inner_symm]
      re_inner_nonneg v := by
        change 0 ≤ ((hE.toCore x).inner v.1 v.1 + (hF.toCore x).inner v.2 v.2).re
        exact add_nonneg ((hE.toCore x).re_inner_nonneg v.1)
          ((hF.toCore x).re_inner_nonneg v.2)
      add_left u v w := by
        simp only [Prod.fst_add, Prod.snd_add]
        rw [(hE.toCore x).add_left, (hF.toCore x).add_left]
        ring
      smul_left u v c := by
        simp only [Prod.smul_fst, Prod.smul_snd]
        rw [(hE.toCore x).smul_left, (hF.toCore x).smul_left]
        ring
      definite v hv := by
        -- Nonnegative diagonal summands must both vanish.
        have hreal := congrArg Complex.re hv
        have he := (hE.toCore x).re_inner_nonneg v.1
        have hf := (hF.toCore x).re_inner_nonneg v.2
        change 0 ≤ ((hE.toCore x).inner v.1 v.1).re at he
        change 0 ≤ ((hF.toCore x).inner v.2 v.2).re at hf
        simp only [Complex.add_re, Complex.zero_re] at hreal
        apply Prod.ext
        · apply (hE.toCore x).definite v.1
          apply Complex.ext
          · change ((hE.toCore x).inner v.1 v.1).re = 0
            linarith
          · have him := congrArg Complex.im ((hE.toCore x).conj_inner_symm v.1 v.1)
            change -((hE.toCore x).inner v.1 v.1).im =
              ((hE.toCore x).inner v.1 v.1).im at him
            change ((hE.toCore x).inner v.1 v.1).im = 0
            linarith
        · apply (hF.toCore x).definite v.2
          apply Complex.ext
          · change ((hF.toCore x).inner v.2 v.2).re = 0
            linarith
          · have him := congrArg Complex.im ((hF.toCore x).conj_inner_symm v.2 v.2)
            change -((hF.toCore x).inner v.2 v.2).im =
              ((hF.toCore x).inner v.2 v.2).im at him
            change ((hF.toCore x).inner v.2 v.2).im = 0
            linarith }
  continuous_pairing := hE.continuous_sum_pairing hF
  isFiniteRank := by
    let := hE.isFiniteRank
    let := hF.isFiniteRank
    exact isFiniteRank_sum

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

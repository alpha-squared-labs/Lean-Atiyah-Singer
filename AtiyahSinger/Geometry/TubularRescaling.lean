/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FiberwiseHadamard

/-!
# Smooth rescaling normal to a fixed zero section

Public module ID: M1507.

A smooth map fixing the zero section and inducing the identity in the normal
direction has a smooth rescaling through scale zero. Its base coordinate may
depend on the vector coordinate; no fiber-preserving hypothesis is imposed.
The radial segment condition keeps the entire mean derivative in the original
smooth domain. This is the local coordinate step in comparing normalized tubes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Conjugate a map by fiber scaling away from zero and use the identity at zero scale. -/
def rescaleAlongFibers (f : E × F → E × F) (p : ℝ × (E × F)) : E × F :=
  if p.1 = 0 then p.2 else
    ((f (p.2.1, p.1 • p.2.2)).1, p.1⁻¹ • (f (p.2.1, p.1 • p.2.2)).2)

/-- Identity normal derivative gives a smooth joint extension of the rescaled map. -/
theorem contDiffOn_rescaleAlongFibers (f : E × F → E × F) {s : Set (E × F)}
    (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s)
    (hstar : ∀ z ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (z.1, t • z.2) ∈ s)
    (hzero : ∀ x, (x, 0) ∈ s → f (x, 0) = (x, 0))
    (hnormal : ∀ x, (x, 0) ∈ s →
      (fderiv ℝ (fun z ↦ (f z).2) (x, 0)).comp (ContinuousLinearMap.inr ℝ E F) =
        ContinuousLinearMap.id ℝ F) :
    ContDiffOn ℝ ∞ (rescaleAlongFibers f)
      {p : ℝ × (E × F) | (p.2.1, p.1 • p.2.2) ∈ s} := by
  let q : E × F → F := fun z ↦ (f z).2
  let γ : ℝ × (E × F) → E × F := fun p ↦ (p.2.1, p.1 • p.2.2)
  have hγ : ContDiff ℝ ∞ γ :=
    contDiff_snd.fst.prodMk (contDiff_fst.smul contDiff_snd.snd)
  have hq : ContDiffOn ℝ ∞ q s := hf.snd
  -- Hadamard's formula expresses the apparent quotient as a smooth linear map
  -- applied to the original vector, uniformly in scale and the base parameter.
  have hD := contDiffOn_fiberwiseMeanDerivative q hq hs hs hstar
  have hR : ContDiffOn ℝ ∞ (fun p : ℝ × (E × F) ↦
      ((f (γ p)).1, fiberwiseMeanDerivative q (γ p).1 (γ p).2 p.2.2)) (γ ⁻¹' s) :=
    (hf.fst.comp hγ.contDiffOn (fun _ hp ↦ hp)).prodMk
      ((hD.comp hγ.contDiffOn (fun _ hp ↦ hp)).clm_apply contDiff_snd.snd.contDiffOn)
  apply hR.congr
  rintro ⟨t, x, v⟩ hp
  change (x, t • v) ∈ s at hp
  by_cases ht : t = 0
  · subst t
    have hx : (x, (0 : F)) ∈ s := by simpa using hp
    simp only [rescaleAlongFibers, ↓reduceIte, γ, zero_smul,
      hzero x hx, fiberwiseMeanDerivative_zero]
    rw [hnormal x hx]
    rfl
  · have hx : (x, (0 : F)) ∈ s := by
      simpa using hstar (x, t • v) hp 0 (by simp)
    have hqzero : q (x, 0) = 0 := congrArg Prod.snd (hzero x hx)
    have hmean := fiberwiseMeanDerivative_apply q hq hs x (t • v)
      (fun a ha ↦ hstar (x, t • v) hp a ha)
    rw [hqzero, sub_zero, map_smul] at hmean
    simp only [rescaleAlongFibers, ht, ↓reduceIte, γ]
    apply Prod.ext
    · rfl
    change t⁻¹ • q (x, t • v) = fiberwiseMeanDerivative q x (t • v) v
    rw [← hmean, inv_smul_smul₀ ht]

/-- Continuity at zero scale needs normal identity only at the base point under consideration.
This version lets bundle charts vary without transporting a neighborhood of derivative equations. -/
theorem continuousAt_rescaleAlongFibers_zero (f : E × F → E × F) {s : Set (E × F)}
    (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s)
    (hstar : ∀ z ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (z.1, t • z.2) ∈ s)
    (hzero : ∀ x, (x, 0) ∈ s → f (x, 0) = (x, 0))
    (x : E) (v : F) (hx : (x, 0) ∈ s)
    (hnormal :
      (fderiv ℝ (fun z ↦ (f z).2) (x, 0)).comp (ContinuousLinearMap.inr ℝ E F) =
        ContinuousLinearMap.id ℝ F) :
    ContinuousAt (rescaleAlongFibers f) (0, x, v) := by
  let q : E × F → F := fun z ↦ (f z).2
  let γ : ℝ × (E × F) → E × F := fun p ↦ (p.2.1, p.1 • p.2.2)
  let R : ℝ × (E × F) → E × F := fun p ↦
    ((f (γ p)).1, fiberwiseMeanDerivative q (γ p).1 (γ p).2 p.2.2)
  have hγ : ContDiff ℝ ∞ γ :=
    contDiff_snd.fst.prodMk (contDiff_fst.smul contDiff_snd.snd)
  have hq : ContDiffOn ℝ ∞ q s := hf.snd
  have hD := contDiffOn_fiberwiseMeanDerivative q hq hs hs hstar
  have hR : ContDiffOn ℝ ∞ R (γ ⁻¹' s) :=
    (hf.fst.comp hγ.contDiffOn (fun _ hp ↦ hp)).prodMk
      ((hD.comp hγ.contDiffOn (fun _ hp ↦ hp)).clm_apply contDiff_snd.snd.contDiffOn)
  have hp : (0, x, v) ∈ γ ⁻¹' s := by simpa [γ] using hx
  have hvalue : R (0, x, v) = (x, v) := by
    simp only [R, γ, zero_smul, hzero x hx, fiberwiseMeanDerivative_zero]
    rw [hnormal]
    rfl
  have hRc := (hR.contDiffAt ((hs.preimage hγ.continuous).mem_nhds hp)).continuousAt
  rw [ContinuousAt, hvalue] at hRc
  -- Both branches converge to the same value. Away from zero Hadamard's formula
  -- gives the smooth branch; at zero the definition is the original identity.
  have hboth : Filter.Tendsto
      (fun p : ℝ × (E × F) ↦ if p.1 = 0 then p.2 else R p)
      (𝓝 (0, x, v)) (𝓝 (x, v)) := continuous_snd.continuousAt.if' hRc
  have heq : (fun p : ℝ × (E × F) ↦ if p.1 = 0 then p.2 else R p) =ᶠ[𝓝 (0, x, v)]
      rescaleAlongFibers f := by
    filter_upwards [(hs.preimage hγ.continuous).mem_nhds hp] with p hp'
    by_cases ht : p.1 = 0
    · simp [rescaleAlongFibers, ht]
    · have hx' : (p.2.1, (0 : F)) ∈ s := by
        simpa using hstar (γ p) hp' 0 (by simp)
      have hqzero : q (p.2.1, 0) = 0 := congrArg Prod.snd (hzero p.2.1 hx')
      have hm := fiberwiseMeanDerivative_apply q hq hs p.2.1 (p.1 • p.2.2)
        (fun a ha ↦ hstar (γ p) hp' a ha)
      rw [hqzero, sub_zero, map_smul] at hm
      simp only [rescaleAlongFibers, ht, ↓reduceIte, R, γ]
      apply Prod.ext
      · rfl
      change fiberwiseMeanDerivative q p.2.1 (p.1 • p.2.2) p.2.2 =
        p.1⁻¹ • q (p.2.1, p.1 • p.2.2)
      rw [← hm, inv_smul_smul₀ ht]
  simpa only [ContinuousAt, rescaleAlongFibers, ↓reduceIte] using hboth.congr' heq

end AtiyahSinger

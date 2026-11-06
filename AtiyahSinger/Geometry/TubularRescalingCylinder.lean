/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TubularRescaling
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The open cylinder of a normalized local rescaling

Public module ID: M1508.

Rescaling a partial diffeomorphism and its inverse simultaneously gives a
parameter-preserving partial homeomorphism through scale zero. The source and
target are explicit open sets. This provides the joint inverse needed for
tubular comparison; separate openness of time slices would not suffice.

The construction is the local coordinate form of the standard deformation to
the normal derivative. Both maps may move the base coordinate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The rescaled map and inverse define one open cylinder around their common zero section. -/
def rescaleAlongFibersPartialHomeomorph (e : OpenPartialHomeomorph (E × F) (E × F))
    (s : Set (E × F)) (hs : IsOpen s) (hsource : s ⊆ e.source) (htarget : s ⊆ e.target)
    (hstar : ∀ z ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (z.1, t • z.2) ∈ s)
    (he : ContDiffOn ℝ ∞ e s) (hei : ContDiffOn ℝ ∞ e.symm s)
    (hzero : ∀ x, (x, 0) ∈ s → e (x, 0) = (x, 0))
    (hzeroi : ∀ x, (x, 0) ∈ s → e.symm (x, 0) = (x, 0))
    (hnormal : ∀ x, (x, 0) ∈ s →
      (fderiv ℝ (fun z ↦ (e z).2) (x, 0)).comp (ContinuousLinearMap.inr ℝ E F) =
        ContinuousLinearMap.id ℝ F)
    (hnormali : ∀ x, (x, 0) ∈ s →
      (fderiv ℝ (fun z ↦ (e.symm z).2) (x, 0)).comp (ContinuousLinearMap.inr ℝ E F) =
        ContinuousLinearMap.id ℝ F) :
    OpenPartialHomeomorph (ℝ × (E × F)) (ℝ × (E × F)) := by
  let γ : ℝ × (E × F) → E × F := fun p ↦ (p.2.1, p.1 • p.2.2)
  have hγ : Continuous γ := continuous_snd.fst.prodMk
    (continuous_fst.smul continuous_snd.snd)
  -- Scaling back recovers the original map, including the fixed zero section.
  have hscale (k : E × F → E × F)
      (hk : ∀ x, (x, 0) ∈ s → k (x, 0) = (x, 0))
      (p : ℝ × (E × F)) (hp : γ p ∈ s) :
      γ (p.1, rescaleAlongFibers k p) = k (γ p) := by
    rcases p with ⟨t, x, v⟩
    by_cases ht : t = 0
    · subst t
      have hx : (x, (0 : F)) ∈ s := by simpa [γ] using hp
      simp [rescaleAlongFibers, γ, hk x hx]
    · simp [rescaleAlongFibers, γ, ht, smul_inv_smul₀ ht]
  have hR := (contDiffOn_rescaleAlongFibers e he hs hstar hzero hnormal).continuousOn
  have hRi := (contDiffOn_rescaleAlongFibers e.symm hei hs hstar hzeroi hnormali).continuousOn
  refine
    { toFun := fun p ↦ (p.1, rescaleAlongFibers e p)
      invFun := fun p ↦ (p.1, rescaleAlongFibers e.symm p)
      source := γ ⁻¹' (s ∩ e ⁻¹' s)
      target := γ ⁻¹' (s ∩ e.symm ⁻¹' s)
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := (he.continuousOn.isOpen_inter_preimage hs hs).preimage hγ
      open_target := (hei.continuousOn.isOpen_inter_preimage hs hs).preimage hγ
      continuousOn_toFun := continuous_fst.continuousOn.prodMk (hR.mono (fun _ hp ↦ hp.1))
      continuousOn_invFun := continuous_fst.continuousOn.prodMk (hRi.mono (fun _ hp ↦ hp.1)) }
  · intro p hp
    change γ (p.1, rescaleAlongFibers e p) ∈ s ∩ e.symm ⁻¹' s
    rw [hscale e hzero p hp.1]
    exact ⟨hp.2, by simpa only [mem_preimage, e.left_inv (hsource hp.1)] using hp.1⟩
  · intro p hp
    change γ (p.1, rescaleAlongFibers e.symm p) ∈ s ∩ e ⁻¹' s
    rw [hscale e.symm hzeroi p hp.1]
    exact ⟨hp.2, by simpa only [mem_preimage, e.right_inv (htarget hp.1)] using hp.1⟩
  · -- The inverse identities at nonzero scale are conjugations of the original identities.
    intro p hp
    apply Prod.ext
    · rfl
    by_cases ht : p.1 = 0
    · simp [rescaleAlongFibers, ht]
    · change rescaleAlongFibers e.symm (p.1, rescaleAlongFibers e p) = p.2
      rw [rescaleAlongFibers, ite_eq_right ht]
      change ((e.symm (γ (p.1, rescaleAlongFibers e p))).1,
        p.1⁻¹ • (e.symm (γ (p.1, rescaleAlongFibers e p))).2) = p.2
      rw [hscale e hzero p hp.1, e.left_inv (hsource hp.1)]
      simp [γ, inv_smul_smul₀ ht]
  · intro p hp
    apply Prod.ext
    · rfl
    by_cases ht : p.1 = 0
    · simp [rescaleAlongFibers, ht]
    · change rescaleAlongFibers e (p.1, rescaleAlongFibers e.symm p) = p.2
      rw [rescaleAlongFibers, ite_eq_right ht]
      change ((e (γ (p.1, rescaleAlongFibers e.symm p))).1,
        p.1⁻¹ • (e (γ (p.1, rescaleAlongFibers e.symm p))).2) = p.2
      rw [hscale e.symm hzeroi p hp.1, e.right_inv (htarget hp.1)]
      simp [γ, inv_smul_smul₀ ht]

end AtiyahSinger

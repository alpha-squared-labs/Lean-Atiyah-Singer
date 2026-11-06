/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ContinuousCoefficientRescaling

/-!
# Local composition of the original fiber rescaling

Public module ID: M1292.

Conjugation by a nonzero fiber dilation preserves composition. Its prescribed
identity value at scale zero preserves the same law. A local factorization
near the zero section therefore gives an eventual factorization of rescaled
maps at every original fiber vector. For a continuous coefficient shear, the
second factor is precisely its jointly continuous explicit cylinder.

These facts isolate the local topological step in composing the original
tubular maps. They do not supply or assume a global geometric factorization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology

variable {E F : Type*} [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [TopologicalSpace E] in
/-- Original fiber rescaling preserves composition, also at its prescribed zero-scale value. -/
theorem rescaleAlongFibers_comp (f g : E × F → E × F) (p : ℝ × (E × F)) :
    rescaleAlongFibers (f ∘ g) p =
      rescaleAlongFibers f (p.1, rescaleAlongFibers g p) := by
  -- At zero all three rescalings are identity; otherwise the two middle dilations cancel.
  by_cases ht : p.1 = 0
  · simp only [rescaleAlongFibers, ht, ↓reduceIte]
  · simp only [rescaleAlongFibers, ht, ↓reduceIte, Function.comp_apply, smul_inv_smul₀ ht]

/-- Equality near one zero vector gives equality of the rescaled maps near any vector above it. -/
theorem eventuallyEq_rescaleAlongFibers_zero (f g : E × F → E × F) (x : E) (v : F)
    (h : f =ᶠ[𝓝 (x, (0 : F))] g) :
    rescaleAlongFibers f =ᶠ[𝓝 (0, x, v)] rescaleAlongFibers g := by
  -- Simultaneous variation of scale, base and fiber still contracts to the same zero vector.
  have hγ : Continuous (fun p : ℝ × (E × F) ↦ (p.2.1, p.1 • p.2.2)) :=
    continuous_snd.fst.prodMk (continuous_fst.smul continuous_snd.snd)
  have hγ₀ : ContinuousAt (fun p : ℝ × (E × F) ↦ (p.2.1, p.1 • p.2.2))
      ((0 : ℝ), x, v) := hγ.continuousAt
  have hnear : ∀ᶠ p : ℝ × (E × F) in 𝓝 ((0 : ℝ), x, v), f (p.2.1, p.1 • p.2.2) =
      g (p.2.1, p.1 • p.2.2) := by
    exact hγ₀.eventually (by
      simpa only [zero_smul] using
        (show ∀ᶠ y in 𝓝 (x, (0 : F)), f y = g y from h))
  filter_upwards [hnear] with p hp
  by_cases ht : p.1 = 0
  · simp only [rescaleAlongFibers, ht, ↓reduceIte]
  · simp only [rescaleAlongFibers, ht, ↓reduceIte, hp]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An actual local coefficient factorization gives the corresponding rescaled factorization. -/
theorem eventuallyEq_rescaleAlongFibers_coefficient
    (A : E × F → G ≃L[ℝ] G) (S : Set (E × F)) (hS : IsOpen S)
    (hA : ContinuousOn (fun p : (E × F) × G ↦ A p.1 p.2) (S ×ˢ univ))
    (hAi : ContinuousOn (fun p : (E × F) × G ↦ (A p.1).symm p.2) (S ×ˢ univ))
    (hzero : ∀ x : E, (x, (0 : F)) ∈ S → A (x, 0) = ContinuousLinearEquiv.refl ℝ G)
    (f g : E × (F × G) → E × (F × G))
    (x : E) (v : F) (w : G) (hx : (x, (0 : F)) ∈ S)
    (hlocal : f =ᶠ[𝓝 (x, (0 : F × G))]
      g ∘ continuousCoefficientShear A S hS hA hAi) :
    rescaleAlongFibers f =ᶠ[𝓝 (0, x, v, w)]
      (fun p ↦ rescaleAlongFibers g
        (continuousCoefficientShearCylinder A S hS hA hAi p)) := by
  have hlocal' := eventuallyEq_rescaleAlongFibers_zero f
    (g ∘ continuousCoefficientShear A S hS hA hAi) x (v, w) hlocal
  have hγ : Continuous (fun p : ℝ × (E × (F × G)) ↦ (p.2.1, p.1 • p.2.2.1)) :=
    continuous_snd.fst.prodMk (continuous_fst.smul continuous_snd.snd.fst)
  have hγ₀ : ContinuousAt (fun p : ℝ × (E × (F × G)) ↦ (p.2.1, p.1 • p.2.2.1))
      ((0 : ℝ), x, v, w) := hγ.continuousAt
  have hnear : ∀ᶠ p : ℝ × (E × (F × G)) in 𝓝 ((0 : ℝ), x, v, w),
      (p.2.1, p.1 • p.2.2.1) ∈ S :=
    hγ₀ (by simpa only [zero_smul] using hS.mem_nhds hx)
  -- The cylinder uses exactly the same coefficient family as the actual local factorization.
  filter_upwards [hlocal', hnear] with p hp hps
  rw [hp, rescaleAlongFibers_comp,
    continuousCoefficientShearCylinder_eq_rescaleAlongFibers A S hS hA hAi hzero p hps]

end AtiyahSinger

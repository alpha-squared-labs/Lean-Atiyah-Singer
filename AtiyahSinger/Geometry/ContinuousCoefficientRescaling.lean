/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TubularRescaling
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Rescaling a continuous family of fiber isomorphisms

Public module ID: M1145.

A continuous coefficient family acts on the last fiber coordinate while fixing
the base and first fiber coordinate. Both it and its inverse give explicit open
partial homeomorphisms, including a jointly continuous rescaling cylinder.
When the coefficient is identity along the zero section, this cylinder agrees
with the original conjugation by simultaneous dilation of both fiber factors.

This is the local bundle-coordinate comparison needed to compose normalized
tubular maps with continuous bundle transport. Smoothness of the coefficients
and a radial-domain assumption are unnecessary: the coefficient after
rescaling is evaluated at the contracted first fiber vector, without division.
The actual original coefficient family and its fiberwise inverse are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set

variable {E F G : Type*}
  [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (A : E × F → G ≃L[ℝ] G) (S : Set (E × F)) (hS : IsOpen S)
  (hA : ContinuousOn (fun p : (E × F) × G ↦ A p.1 p.2) (S ×ˢ univ))
  (hAi : ContinuousOn (fun p : (E × F) × G ↦ (A p.1).symm p.2) (S ×ˢ univ))

/-- The same continuous coefficients and their inverses give a local fiber shear. -/
def continuousCoefficientShear : OpenPartialHomeomorph (E × (F × G)) (E × (F × G)) := by
  let q : E × (F × G) → (E × F) × G := fun z ↦ ((z.1, z.2.1), z.2.2)
  have hq : Continuous q :=
    (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  refine
    { toFun := fun z ↦ (z.1, z.2.1, A (z.1, z.2.1) z.2.2)
      invFun := fun z ↦ (z.1, z.2.1, (A (z.1, z.2.1)).symm z.2.2)
      source := {z | (z.1, z.2.1) ∈ S}
      target := {z | (z.1, z.2.1) ∈ S}
      map_source' := fun _ hz ↦ hz
      map_target' := fun _ hz ↦ hz
      left_inv' := fun z _ ↦ by simp only [ContinuousLinearEquiv.symm_apply_apply]
      right_inv' := fun z _ ↦ by simp only [ContinuousLinearEquiv.apply_symm_apply]
      open_source := hS.preimage (continuous_fst.prodMk continuous_snd.fst)
      open_target := hS.preimage (continuous_fst.prodMk continuous_snd.fst)
      continuousOn_toFun := continuous_fst.continuousOn.prodMk
        (continuous_snd.fst.continuousOn.prodMk
          (hA.comp hq.continuousOn (fun _ hz ↦ ⟨hz, mem_univ _⟩)))
      continuousOn_invFun := continuous_fst.continuousOn.prodMk
        (continuous_snd.fst.continuousOn.prodMk
          (hAi.comp hq.continuousOn (fun _ hz ↦ ⟨hz, mem_univ _⟩))) }

/-- Evaluating the same coefficients at the contracted first vector gives an open cylinder. -/
def continuousCoefficientShearCylinder :
    OpenPartialHomeomorph (ℝ × (E × (F × G))) (ℝ × (E × (F × G))) := by
  let q : ℝ × (E × (F × G)) → (E × F) × G :=
    fun p ↦ ((p.2.1, p.1 • p.2.2.1), p.2.2.2)
  have hq : Continuous q :=
    (continuous_snd.fst.prodMk (continuous_fst.smul continuous_snd.snd.fst)).prodMk
      continuous_snd.snd.snd
  have hopen : IsOpen {p : ℝ × (E × (F × G)) | (p.2.1, p.1 • p.2.2.1) ∈ S} :=
    hS.preimage (continuous_snd.fst.prodMk (continuous_fst.smul continuous_snd.snd.fst))
  refine
    { toFun := fun p ↦ (p.1, p.2.1, p.2.2.1, A (p.2.1, p.1 • p.2.2.1) p.2.2.2)
      invFun := fun p ↦ (p.1, p.2.1, p.2.2.1, (A (p.2.1, p.1 • p.2.2.1)).symm p.2.2.2)
      source := {p | (p.2.1, p.1 • p.2.2.1) ∈ S}
      target := {p | (p.2.1, p.1 • p.2.2.1) ∈ S}
      map_source' := fun _ hp ↦ hp
      map_target' := fun _ hp ↦ hp
      left_inv' := fun p _ ↦ by simp only [ContinuousLinearEquiv.symm_apply_apply]
      right_inv' := fun p _ ↦ by simp only [ContinuousLinearEquiv.apply_symm_apply]
      open_source := hopen
      open_target := hopen
      continuousOn_toFun := continuous_fst.continuousOn.prodMk
        (continuous_snd.fst.continuousOn.prodMk (continuous_snd.snd.fst.continuousOn.prodMk
          (hA.comp hq.continuousOn (fun _ hp ↦ ⟨hp, mem_univ _⟩))))
      continuousOn_invFun := continuous_fst.continuousOn.prodMk
        (continuous_snd.fst.continuousOn.prodMk (continuous_snd.snd.fst.continuousOn.prodMk
          (hAi.comp hq.continuousOn (fun _ hp ↦ ⟨hp, mem_univ _⟩)))) }

/-- The explicit coefficient cylinder is the original simultaneous fiber rescaling. -/
theorem continuousCoefficientShearCylinder_eq_rescaleAlongFibers
    (hzero : ∀ x : E, (x, (0 : F)) ∈ S → A (x, 0) = ContinuousLinearEquiv.refl ℝ G)
    (p : ℝ × (E × (F × G))) (hp : (p.2.1, p.1 • p.2.2.1) ∈ S) :
    continuousCoefficientShearCylinder A S hS hA hAi p =
      (p.1, rescaleAlongFibers (continuousCoefficientShear A S hS hA hAi) p) := by
  rcases p with ⟨t, x, v, w⟩
  -- At scale zero the prescribed normalization gives the exact original vector identity.
  by_cases ht : t = 0
  · subst t
    have hx : (x, (0 : F)) ∈ S := by simpa only [zero_smul] using hp
    change (0, x, v, A (x, (0 : ℝ) • v) w) =
      (0, rescaleAlongFibers (continuousCoefficientShear A S hS hA hAi) (0, x, v, w))
    rw [zero_smul, hzero x hx]
    simp only [rescaleAlongFibers, ↓reduceIte, ContinuousLinearEquiv.refl_apply]
  · -- Away from zero, linearity cancels the dilation only in the last fiber factor.
    change (t, x, v, A (x, t • v) w) =
      (t, rescaleAlongFibers (continuousCoefficientShear A S hS hA hAi) (t, x, v, w))
    simp only [rescaleAlongFibers, ht, ↓reduceIte, continuousCoefficientShear,
      OpenPartialHomeomorph.coe_mk, Prod.smul_mk, map_smul,
      inv_smul_smul₀ ht]

/-- The same comparison retains the actual inverse coefficient family. -/
theorem continuousCoefficientShearCylinder_symm_eq_rescaleAlongFibers
    (hzero : ∀ x : E, (x, (0 : F)) ∈ S → A (x, 0) = ContinuousLinearEquiv.refl ℝ G)
    (p : ℝ × (E × (F × G))) (hp : (p.2.1, p.1 • p.2.2.1) ∈ S) :
    (continuousCoefficientShearCylinder A S hS hA hAi).symm p =
      (p.1, rescaleAlongFibers (continuousCoefficientShear A S hS hA hAi).symm p) := by
  -- Apply the same argument to the original inverse family, whose zero value is also identity.
  have hzeroi (x : E) (hx : (x, (0 : F)) ∈ S) :
      (A (x, 0)).symm = ContinuousLinearEquiv.refl ℝ G := by
    rw [hzero x hx]
    rfl
  exact continuousCoefficientShearCylinder_eq_rescaleAlongFibers
    (fun q ↦ (A q).symm) S hS hAi hA hzeroi p hp

end AtiyahSinger

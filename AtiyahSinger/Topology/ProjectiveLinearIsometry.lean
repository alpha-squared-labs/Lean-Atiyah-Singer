/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveBundle

/-!
# Isometric changes of the orthogonal projective model

Public module ID: M2017.

A complex linear isometry equivalence conjugates the actual orthogonal
rank-one projectors and gives a homeomorphism of their original subspaces.
This includes explicit universe lifts of a finite projective fiber, needed
when original singular cohomology is taken in the universe of its base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

universe u v

/-- The universe lift retains its original norm and the original complex inner product. -/
instance uliftInnerProductSpace (V : Type u) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] : InnerProductSpace ℂ (ULift.{v} V) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y c := inner_smul_left x.down y.down c

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- Isometric conjugation identifies the original orthogonal-projector projective spaces. -/
def mapLinearIsometryEquiv (e : V ≃ₗᵢ[ℂ] W) :
    HermitianProjectiveSpace V InnerProductSpace.toCore ≃ₜ
      HermitianProjectiveSpace W InnerProductSpace.toCore := by
  let a := e.toContinuousLinearEquiv
  let c := a.conjContinuousAlgEquiv
  have hrank (P : V →L[ℂ] V) :
      Module.finrank ℂ (LinearMap.range (c P).toLinearMap) =
        Module.finrank ℂ (LinearMap.range P.toLinearMap) := by
    change Module.finrank ℂ (LinearMap.range (a.toLinearEquiv.toLinearMap.comp
      (P.toLinearMap.comp a.symm.toLinearEquiv.toLinearMap))) = _
    rw [LinearMap.range_comp, LinearEquiv.range_comp, LinearEquiv.finrank_map_eq]
  have hself (P : V →L[ℂ] V) :
      (∀ v w, inner ℂ (P v) w = inner ℂ v (P w)) ↔
        ∀ v w, inner ℂ (c P v) w = inner ℂ v (c P w) := by
    constructor
    · intro h v w
      have hv : e (e.symm v) = v := e.apply_symm_apply v
      have hw : e (e.symm w) = w := e.apply_symm_apply w
      change inner ℂ (e (P (e.symm v))) w = inner ℂ v (e (P (e.symm w)))
      rw [← hw, ← hv, e.inner_map_map, e.inner_map_map]
      simpa only [e.symm_apply_apply] using h (e.symm v) (e.symm w)
    · intro h v w
      have hp := h (e v) (e w)
      change inner ℂ (e (P (e.symm (e v)))) (e w) =
        inner ℂ (e v) (e (P (e.symm (e w)))) at hp
      simpa only [e.symm_apply_apply, e.inner_map_map] using hp
  have hprojective (P : V →L[ℂ] V) :
      (P.comp P = P ∧ Module.finrank ℂ (LinearMap.range P.toLinearMap) = 1 ∧
        ∀ v w, inner ℂ (P v) w = inner ℂ v (P w)) ↔
      ((c P).comp (c P) = c P ∧ Module.finrank ℂ (LinearMap.range (c P).toLinearMap) = 1 ∧
        ∀ v w, inner ℂ (c P v) w = inner ℂ v (c P w)) := by
    have hid : (c P).comp (c P) = c P ↔ P.comp P = P := by
      simpa only [← ContinuousLinearMap.mul_def, ← map_mul,
        ContinuousAlgEquiv.coe_toAlgEquiv] using c.injective.eq_iff
        (a := P * P) (b := P)
    rw [hid, hrank, hself]
  exact c.toHomeomorph.subtype hprojective

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

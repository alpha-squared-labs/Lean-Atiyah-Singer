/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealComplexification
public import Mathlib.Algebra.Star.Module

/-!
# Canonical conjugation on the original real complexification

Public module ID: M2041.

Conjugating the complex scalar in the actual tensor product is a conjugate-linear
involution. Its total map is a homeomorphism for the specified real/imaginary
complexification topology: it fixes the real component and negates the imaginary
component. No metric, real orientation, or constant rank is assumed.

Source: Milnor--Stasheff, section 15, Lemma 15.1, the self-conjugacy of the genuine
complexification of a real vector bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct

/-- Canonical conjugation acts on the scalar factor of the actual complexification. -/
def complexificationConjugation (V : Type*) [AddCommGroup V] [Module ℝ V] :
    (ℂ ⊗[ℝ] V) ≃ₗ⋆[ℂ] (ℂ ⊗[ℝ] V) := by
  let e := TensorProduct.congr Complex.conjAe.toLinearEquiv (LinearEquiv.refl ℝ V)
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := ?_ }
  intro z w
  induction w using TensorProduct.inductionOn with
  | tmul c v => simp [e, TensorProduct.smul_tmul']
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

/-- The canonical conjugation is an involution on the same tensor carrier. -/
theorem complexificationConjugation_involutive (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Function.Involutive (complexificationConjugation V) := by
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul z v => simp [complexificationConjugation]
  | add a b ha hb => simp only [map_add, ha, hb]

namespace RealBundle

variable {X : Type*} [TopologicalSpace X]
  (G : Type*) (V : X → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)] [IsFiniteRank G V]

/-- Actual tensor conjugation is a homeomorphism for the original complexification topology. -/
def complexificationConjugationTotalHomeomorph :
    letI := ComplexBundle.complexificationTopology G V
    TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] V x) ≃ₜ TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] V x) := by
  let := ComplexBundle.complexificationTopology G V
  let T := TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] V x)
  let H := ComplexBundle.complexificationDoubleTotalHomeomorph G V
  let f : T → T := fun z ↦ ⟨z.proj, complexificationConjugation (V z.proj) z.snd⟩
  have hf : Function.Involutive f := by
    intro z
    exact congrArg (TotalSpace.mk z.proj) (complexificationConjugation_involutive (V z.proj) z.snd)
  -- The given real/imaginary coordinates turn conjugation into the same fiber reflection.
  have hcoords (x : X) (w : ℂ ⊗[ℝ] V x) :
      complexificationReIm (V x) (complexificationConjugation (V x) w) =
        ((complexificationReIm (V x) w).1, -(complexificationReIm (V x) w).2) := by
    induction w using TensorProduct.inductionOn with
    | tmul z v =>
      simp [complexificationConjugation, (complexificationReIm_properties (V x)).1]
    | add a b ha hb =>
      simp only [map_add, ha, hb, Prod.fst_add, Prod.snd_add, neg_add]
      rfl
  have hpair : Topology.IsInducing (fun z : TotalSpace (G × G) (V ×ᵇ V) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace G V), (⟨z.proj, z.snd.2⟩ : TotalSpace G V))) := ⟨rfl⟩
  have hpairCont : Continuous (fun z : T ↦
      ((⟨z.proj, (complexificationReIm (V z.proj) z.snd).1⟩ : TotalSpace G V),
        (⟨z.proj, (complexificationReIm (V z.proj) z.snd).2⟩ : TotalSpace G V))) :=
    hpair.continuous.comp H.continuous
  have hneg : Continuous (fun z : T ↦
      (⟨z.proj, -(complexificationReIm (V z.proj) z.snd).2⟩ : TotalSpace G V)) := by
    simpa only [Function.comp_def, neg_one_smul] using (continuous_scaling G V).comp
      ((continuous_const (y := (-1 : ℝ))).prodMk hpairCont.snd)
  have hreflection : Continuous (fun z : T ↦
      (⟨z.proj, ((complexificationReIm (V z.proj) z.snd).1,
        -(complexificationReIm (V z.proj) z.snd).2)⟩ : TotalSpace (G × G) (V ×ᵇ V))) :=
    hpair.continuous_iff.mpr (hpairCont.fst.prodMk hneg)
  have hcontinuous : Continuous f := by
    apply H.isInducing.continuous_iff.mpr
    change Continuous (fun z : T ↦ (⟨z.proj,
      complexificationReIm (V z.proj) (complexificationConjugation (V z.proj) z.snd)⟩ :
        TotalSpace (G × G) (V ×ᵇ V)))
    simpa only [hcoords] using hreflection
  exact
    { toEquiv := ⟨f, f, hf, hf⟩
      continuous_toFun := hcontinuous
      continuous_invFun := hcontinuous }

end RealBundle

end AtiyahSinger

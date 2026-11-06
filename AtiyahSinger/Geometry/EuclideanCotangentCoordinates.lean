/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Topology.EuclideanTangentKTheory

/-!
# Native Euclidean cotangent coordinates

Public module ID: M1214.

The original Hom-bundle topology on the cotangent of Euclidean space is
identified with its standard base and continuous dual coordinates. The real
Riesz map then gives the ordered base-plus-imaginary-vector complex coordinates.
These are the coordinates used by the common-open pole comparison; neither
complex conjugation nor a different tangent atlas is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- The native Euclidean cotangent bundle in its base and continuous-dual coordinates. -/
def euclideanCotangentProductHomeomorph (r : ℕ) :
    CotangentTotalSpace (n := r) (M := EuclideanSpace ℝ (Fin r)) ≃ₜ
      EuclideanSpace ℝ (Fin r) × CotangentModel r := by
  let E := EuclideanSpace ℝ (Fin r)
  have hcont {X : Type} [TopologicalSpace X]
      (f : X → CotangentTotalSpace (n := r) (M := E)) (x : X) :
      ContinuousAt f x ↔ ContinuousAt (fun y ↦ (f y).proj) x ∧
        ContinuousAt (fun y ↦ (show CotangentModel r from (f y).snd)) x := by
    rw [continuousAt_hom_bundle]
    have hcoord (a b : E) (η : CotangentModel r) :
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E)) ℝ
          (Bundle.Trivial E ℝ) a b a b η = η := by
      change ((Bundle.Trivial.trivialization E ℝ).continuousLinearMapAt ℝ b).comp
        (η.comp ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).symmL ℝ b)) = η
      rw [Bundle.Trivial.continuousLinearMapAt_trivialization,
        TangentBundle.symmL_model_space]
      rfl
    have hcoord' (y : X) : ContinuousLinearMap.inCoordinates
        (EuclideanSpace ℝ (Fin r)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ℝ
        (fun _ : E ↦ ℝ) (f x).proj (f y).proj (f x).proj (f y).proj (f y).snd =
          (f y).snd := hcoord (f x).proj (f y).proj (f y).snd
    simp only [hcoord']
  exact {
    toFun z := (z.proj, z.snd)
    invFun z := ⟨z.1, z.2⟩
    left_inv z := rfl
    right_inv z := rfl
    continuous_toFun := continuous_iff_continuousAt.mpr (fun z ↦
      ((hcont id z).mp continuousAt_id).1.prodMk ((hcont id z).mp continuousAt_id).2)
    continuous_invFun := continuous_iff_continuousAt.mpr (fun z ↦
      (hcont (fun w : E × CotangentModel r ↦ ⟨w.1, w.2⟩) z).mpr
        ⟨continuousAt_fst, continuousAt_snd⟩) }

/-- Real Riesz duality retains the original ordered complex Bott coordinates. -/
def euclideanCotangentComplexHomeomorph (r : ℕ) :
    CotangentTotalSpace (n := r) (M := EuclideanSpace ℝ (Fin r)) ≃ₜ
      EuclideanSpace ℂ (Fin r) := by
  let E := EuclideanSpace ℝ (Fin r)
  let R := (InnerProductSpace.toDual ℝ E).toHomeomorph
  let T := tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)
  let C := euclideanTangentComplexHomeomorph r
  exact ((euclideanCotangentProductHomeomorph r).trans
    ((Homeomorph.refl E).prodCongr R.symm)).trans
      ((T.symm.trans C).trans (PiLp.homeomorph 2 (fun _ : Fin r ↦ ℂ)).symm)

/-- Ordered real and imaginary Euclidean coordinates on the original complex model. -/
def euclideanComplexRealProductHomeomorph (r : ℕ) :
    EuclideanSpace ℂ (Fin r) ≃ₜ
      EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) :=
  ((PiLp.homeomorph 2 (fun _ : Fin r ↦ ℂ)).trans
    (euclideanTangentComplexHomeomorph r).symm).trans
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin r)))

/-- Rescale only the imaginary fiber by a positive continuous function of the real base. -/
def euclideanComplexImaginaryScale (r : ℕ)
    (s : C(EuclideanSpace ℝ (Fin r), ℝ)) (hs : ∀ x, 0 < s x) :
    EuclideanSpace ℂ (Fin r) ≃ₜ EuclideanSpace ℂ (Fin r) := by
  let E := EuclideanSpace ℝ (Fin r)
  let R : E × E ≃ₜ E × E := {
    toFun z := (z.1, s z.1 • z.2)
    invFun z := (z.1, (s z.1)⁻¹ • z.2)
    left_inv z := by
      change (z.1, (s z.1)⁻¹ • (s z.1 • z.2)) = z
      rw [smul_smul, inv_mul_cancel₀ (hs z.1).ne', one_smul]
    right_inv z := by
      change (z.1, s z.1 • ((s z.1)⁻¹ • z.2)) = z
      rw [smul_smul, mul_inv_cancel₀ (hs z.1).ne', one_smul]
    continuous_toFun := continuous_fst.prodMk
      ((s.continuous.comp continuous_fst).smul continuous_snd)
    continuous_invFun := continuous_fst.prodMk
      (((s.continuous.comp continuous_fst).inv₀ (fun z ↦ (hs z.1).ne')).smul continuous_snd) }
  let e := euclideanComplexRealProductHomeomorph r
  exact (e.trans R).trans e.symm

end AtiyahSinger

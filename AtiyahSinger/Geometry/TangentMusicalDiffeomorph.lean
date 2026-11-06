/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleQuotientDescent
public import AtiyahSinger.Geometry.TangentMusical
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smoothness of the original metric musical identification

Public module ID: M1484.

The actual metric flat map is a diffeomorphism of the native tangent and
continuous-dual total spaces. Its inverse is smooth by descent through the
same smooth fiberwise Riesz equivalence, so no replacement bundle topology
or unrelated tangent norm is introduced.

This strengthens the homeomorphism needed for compact-support K transport
to the smooth identification needed for an actual tubular map. The forward
formula remains exactly the supplied metric pairing in every fiber.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1000000 in
-- All maps retain the native tangent topology and the original continuous-dual Hom atlas.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth metric gives the native musical diffeomorphism with its exact flat formula. -/
theorem exists_tangentMusical_diffeomorph
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    ∃ d : TangentBundle 𝓘(ℝ, E) M ≃ₘ⟮𝓘(ℝ, E).prod 𝓘(ℝ, E),
        𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
        TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ),
      ∀ z, d z = ⟨z.proj, g.inner z.proj z.snd⟩ := by
  classical
  let I := 𝓘(ℝ, E)
  let V := TangentSpace I (M := M)
  let W := fun x : M ↦ V x →L[ℝ] ℝ
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let e (x : M) : V x ≃L[ℝ] W x :=
    (InnerProductSpace.toDual ℝ (V x)).toContinuousLinearEquiv
  have hQ : ContMDiff (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun z : TotalSpace E V ↦ (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (E →L[ℝ] ℝ) W)) :=
    (g.contMDiff.comp (Bundle.contMDiff_proj V)).clm_bundle_apply contMDiff_id
  -- Smooth descent applies to the same Riesz maps, which are surjective in every native fiber.
  have hR : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : TotalSpace (E →L[ℝ] ℝ) W ↦
        (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace E V)) := by
    apply contMDiff_bundleMap_of_comp_surjective
      (fun x ↦ (e x).toContinuousLinearMap) (fun x ↦ (e x).symm.toContinuousLinearMap)
      hQ (fun x ↦ (e x).surjective)
    apply contMDiff_id.congr
    intro z
    change (⟨z.proj, (e z.proj).symm (e z.proj z.snd)⟩ : TotalSpace E V) = z
    rw [(e z.proj).symm_apply_apply]
  let d : TotalSpace E V ≃ₘ⟮I.prod 𝓘(ℝ, E), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      TotalSpace (E →L[ℝ] ℝ) W :=
    { toFun := fun z ↦ ⟨z.proj, e z.proj z.snd⟩
      invFun := fun z ↦ ⟨z.proj, (e z.proj).symm z.snd⟩
      left_inv := by
        rintro ⟨x, v⟩
        change (⟨x, (e x).symm (e x v)⟩ : TotalSpace E V) = ⟨x, v⟩
        rw [(e x).symm_apply_apply]
      right_inv := by
        rintro ⟨x, v⟩
        change (⟨x, e x ((e x).symm v)⟩ : TotalSpace (E →L[ℝ] ℝ) W) = ⟨x, v⟩
        rw [(e x).apply_symm_apply]
      contMDiff_toFun := hQ
      contMDiff_invFun := hR }
  exact ⟨d, fun _ ↦ rfl⟩

end AtiyahSinger

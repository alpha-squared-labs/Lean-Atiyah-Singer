/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereOpenDiffeomorph
public import AtiyahSinger.Geometry.ManifoldModelChange

/-!
# Common open coordinates for a tube and the frame sphere

Public module ID: M1254.

Any specified whole-bundle diffeomorphism onto an open set and the original
stereographic inverse define a diffeomorphism between their actual open images. The sphere atlas is
changed by an explicit linear equivalence to the ambient model; its points,
topology, zero section and factor-two stereographic normalization are retained.
This is the common-open geometry needed in compact embedding index excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

set_option backward.isDefEq.respectTransparency false in
/-- A whole-bundle diffeomorphism and the native sphere chart determine a diffeomorphism
between their open images. -/
theorem exists_frameSphere_tubular_diffeomorph
    (l : (EB × R) ≃L[ℝ] F) (U : Opens N)
    (d : TotalSpace R V ≃ₘ⟮(𝓘(ℝ, EB).prod 𝓘(ℝ, R)), 𝓘(ℝ, F)⟯ U) :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    let e := frameSphereStereographic (EB := EB) r V
    let W : Opens Z := ⟨e.source, e.open_source⟩
    letI := linearModelChartedSpace l Z
    ∃ D : U ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ W,
      ∀ v : TotalSpace R V, (D (d v) : Z) = e.symm v := by
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let e := frameSphereStereographic (EB := EB) r V
  let W : Opens Z := ⟨e.source, e.open_source⟩
  let a := frameSphereStereographicDiffeomorph (EB := EB) r V
  let b := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  -- Restrict the identity-of-points model change to the same original open subset.
  let c : W ≃ₘ⟮𝓘(ℝ, EB × R), 𝓘(ℝ, F)⟯ W := {
    toEquiv := Equiv.refl W
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff W _).mp
      exact b.contMDiff.comp contMDiff_subtype_val
    contMDiff_invFun := by
      apply (ContMDiff.subtypeVal_comp_iff W _).mp
      exact b.symm.contMDiff.comp contMDiff_subtype_val }
  -- Composition uses the same whole-bundle point, before and after both open inclusions.
  refine ⟨d.symm.trans (a.trans c), ?_⟩
  intro v
  change (a (d.symm (d v)) : Z) = e.symm v
  rw [d.symm_apply_apply]
  rfl

end AtiyahSinger

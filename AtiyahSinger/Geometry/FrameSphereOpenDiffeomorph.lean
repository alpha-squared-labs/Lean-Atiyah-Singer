/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereStereographic

/-!
# The original stereographic map as a diffeomorphism onto its open image

Public module ID: M1246.

This packages the already proved stereographic homeomorphism and its two
smoothness statements on the same whole vector bundle and the same open
subset of the frame-associated sphere. It is the open embedding used in
analytic excision. The original factor-two normalization is unchanged.
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

/-- The original whole-bundle stereographic inverse, with its actual open sphere image. -/
def frameSphereStereographicDiffeomorph :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    let e := frameSphereStereographic (EB := EB) r V
    let U : Opens Z := ⟨e.source, e.open_source⟩
    TotalSpace R V ≃ₘ⟮(𝓘(ℝ, EB).prod 𝓘(ℝ, R)), 𝓘(ℝ, EB × R)⟯ U := by
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let e := frameSphereStereographic (EB := EB) r V
  let U : Opens Z := ⟨e.source, e.open_source⟩
  have hs := frameSphereStereographic_spec (EB := EB) r V
  have hm (v : TotalSpace R V) : v ∈ e.target := hs.2.1.symm ▸ Set.mem_univ v
  -- Both inverse laws and both smooth maps come from this one specified chart.
  exact {
    toFun v := ⟨e.symm v, e.map_target (hm v)⟩
    invFun z := e z
    left_inv v := e.right_inv (hm v)
    right_inv z := Subtype.ext (e.left_inv z.property)
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff U _).mp
      exact hs.2.2.2.2.2
    contMDiff_invFun := by
      intro z
      exact ((hs.2.2.2.2.1 z z.property).contMDiffAt
        (e.open_source.mem_nhds z.property)).comp z (contMDiff_subtype_val (n := ∞) z) }

end AtiyahSinger

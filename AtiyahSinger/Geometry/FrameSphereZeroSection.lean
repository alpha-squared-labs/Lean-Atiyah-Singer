/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereStereographic
public import AtiyahSinger.Geometry.SmoothSectionEmbedding

/-!
# The south section of the native frame-associated sphere

Public module ID: M1257.

The stereographic inverse carries the original zero section to a smooth
embedding in the same associated sphere atlas. The explicit inverse formula
and the original sphere homeomorphism give a smooth left inverse, including
rank zero. This is the sphere model of a compact embedding's normal neighborhood.
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

/-- The original zero section embeds smoothly as the south section of the frame sphere. -/
theorem isSmoothEmbedding_frameSphere_zeroSection :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EB) 𝓘(ℝ, EB × R) ∞
      (fun b : B ↦ (frameSphereStereographic (EB := EB) r V).symm ⟨b, 0⟩) := by
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let e := frameSphereStereographic (EB := EB) r V
  let c := frameSphereHomeomorph (EB := EB) r V
  have hs := frameSphereStereographic_spec (EB := EB) r V
  have hc := (frameSphereHomeomorph_spec (EB := EB) r V).2
  let f : ContMDiffMap 𝓘(ℝ, EB) 𝓘(ℝ, EB × R) B Z ∞ :=
    ⟨fun b ↦ e.symm ⟨b, 0⟩, hs.2.2.2.2.2.comp (contMDiff_zeroSection ℝ V)⟩
  -- The original sphere homeomorphism followed by the bundle projection is smooth.
  let q : ContMDiffMap 𝓘(ℝ, EB × R) 𝓘(ℝ, EB) Z B ∞ :=
    ⟨fun z ↦ (c z).val.1.proj,
      (contMDiff_proj V).comp (contMDiff_fst.comp hc.contMDiff)⟩
  apply isSmoothEmbedding_of_leftInverse f q
  intro b
  change (c (e.symm ⟨b, 0⟩)).val.1.proj = b
  rw [hs.2.2.2.1]

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereStereographic
public import AtiyahSinger.Geometry.SphereTangentCoordinates

/-!
# The two original frame-sphere stereographic normalizations

Public module ID: M1247.

The original whole-vector-bundle stereographic coordinate is twice the
normalized pole coordinate used by the Bott class. The equality below keeps
the actual frame, original sphere quotient and native bundle point. It is
valid in every rank and does not identify tangent and cotangent rescalings.
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

set_option maxSynthPendingDepth 35 in
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
-- Compare the two supplied formulas in the same original sphere compactification.
/-- The original frame-sphere inverse at twice a frame vector is the normalized pole inverse. -/
theorem frameSphereStereographic_symm_two_smul (p : P) (u : R) :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    (frameSphereStereographic (EB := EB) r V).symm ⟨p.1, (2 : ℝ) • p.2 u⟩ =
      associatedBundleMk G P (OrthogonalSphere r) p
        ((orthogonalSphereNormalizedChart r false).symm u) := by
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let c := frameSphereHomeomorph (EB := EB) r V
  have ha := frameSphereStereographic_spec (EB := EB) r V
  have hc := (frameSphereHomeomorph_spec (EB := EB) r V).1
  -- The same frame is an isometry, so only the explicitly retained scalar two changes the norm.
  have hnorm : ‖(2 : ℝ) • p.2 u‖ ^ 2 = 4 * ‖u‖ ^ 2 := by
    rw [norm_smul, p.2.norm_map]
    norm_num [mul_pow]
  apply c.injective
  apply Subtype.ext
  rw [ha.2.2.2.1, hc]
  have hcoords := orthogonalSphereNormalizedChart_inverse_formula r false u
  change ((⟨p.1, (4 / (‖(2 : ℝ) • p.2 u‖ ^ 2 + 4)) • ((2 : ℝ) • p.2 u)⟩ :
      TotalSpace R V), (‖(2 : ℝ) • p.2 u‖ ^ 2 - 4) /
        (‖(2 : ℝ) • p.2 u‖ ^ 2 + 4)) = _
  rw [hnorm]
  change _ = ((⟨p.1, p.2
    (((orthogonalSphereNormalizedChart r false).symm u).val.fst)⟩ : TotalSpace R V),
      ((orthogonalSphereNormalizedChart r false).symm u).val.snd)
  rw [hcoords]
  change _ = ((⟨p.1, p.2 ((2 / (1 + ‖u‖ ^ 2)) • u)⟩ : TotalSpace R V),
    (‖u‖ ^ 2 - 1) / (1 + ‖u‖ ^ 2))
  -- Both rational coefficients agree before quotient descent; no coordinate choice is discarded.
  rw [map_smul, smul_smul]
  have hfirst : (4 / (4 * ‖u‖ ^ 2 + 4)) * 2 = 2 / (1 + ‖u‖ ^ 2) := by
    field_simp
    ring
  have hlast : (4 * ‖u‖ ^ 2 - 4) / (4 * ‖u‖ ^ 2 + 4) =
      (‖u‖ ^ 2 - 1) / (1 + ‖u‖ ^ 2) := by
    field_simp
    ring
  rw [hfirst, hlast]

end AtiyahSinger

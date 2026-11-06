/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Geometry.SubmersionCotangentSplitting
public import AtiyahSinger.Topology.AssociatedCompactControl

/-!
# A horizontal lift for the original compact associated sphere bundle

Public module ID: M1076.

For a compact Hausdorff principal base, the original associated sphere space
is compact: apply the existing compact-control theorem to the whole compact
sphere. Its existing associated quotient is Hausdorff as well. The standard
smooth horizontal-lift selection therefore applies to the original projection
and the same selected associated sphere atlas.

SG III.13, p.251, obtains a splitting from a metric. The present construction
uses the existing smooth splitting over a Hausdorff paracompact total space;
it need not coincide with a metric-dependent choice. It supplies one lift
for the later cotangent realization without requiring the principal space or
structure group to be compact.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {P B : Type*} [TopologicalSpace P] [TopologicalSpace B] [ChartedSpace E B]
  [IsManifold 𝓘(ℝ, E) ∞ B] [CompactSpace B] [T2Space B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B}
  (S : SmoothOrthogonalPrincipalAtlas r 𝓘(ℝ, E) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

/-- Select one smooth horizontal lift of the original compact associated sphere projection. -/
def associatedSphereHorizontalLift :
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    SmoothHorizontalLift (smoothAssociatedSphereProjection S) := by
  letI := associatedSphereChartedSpace S
  letI := associatedSphereIsManifold S
  -- The entire sphere control is exactly the original quotient, including empty bases.
  have hcontrol : associatedControl G P (OrthogonalSphere r) Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | h v =>
      exact ⟨v, ⟨Set.mem_univ v.1, Set.mem_univ v.2⟩, rfl⟩
  -- Existing compact control and separation apply to these same quotient points and topology.
  letI : CompactSpace Z := ⟨by
    rw [← hcontrol]
    exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
      (fun _ _ ↦ Iff.rfl)⟩
  letI := associatedBundle_t2Space (Y := OrthogonalSphere r) S.toIsPrincipalBundle
  -- Compactness supplies paracompactness; the selected lift splits this actual differential.
  exact smoothHorizontalLift (smoothAssociatedSphereProjection S)
    (associatedSphereProjection_isSubmersion S)

end AtiyahSinger

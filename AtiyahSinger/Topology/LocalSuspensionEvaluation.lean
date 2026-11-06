/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanLocalHomology
public import AtiyahSinger.Topology.SingularConnectingEvaluation
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality

/-!
# Evaluation under the original local suspension

Public module ID: M1945.

The cohomological triple boundary is adjoint to the original homological
suspension when the transverse classes agree on the upper half-axis complement.
The proof uses precisely the existing excision inverse and projection, rather
than choosing a new suspension isomorphism or a new orientation generator.

Source: the Kronecker pairing and naturality of the relative exact sequence,
Hatcher, Algebraic Topology, Sections 2.1 and 3.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual triple coboundary and local homology suspension preserve transverse evaluation. -/
theorem euclideanLocalSuspensionIso_evaluation (R : Type) [CommRing R]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (a : relativeSingularCohomology R {x : E | x ≠ 0} k)
    (b : relativeSingularCohomology R
      ((Subtype.val : {z : ℝ × E | z ≠ 0} → ℝ × E) ⁻¹'
        euclideanPuncturedHalfSpace E (-1)) k)
    (hb : relativeSingularCohomologyPullback R (euclideanLocalSuspensionInclusion E)
        (A := (Subtype.val : euclideanPuncturedHalfSpace E 1 → ℝ × E) ⁻¹'
          euclideanPuncturedHalfSpace E (-1))
        (B := (Subtype.val : {z : ℝ × E | z ≠ 0} → ℝ × E) ⁻¹'
          euclideanPuncturedHalfSpace E (-1)) (fun _ hx ↦ hx) k b =
      relativeSingularCohomologyPullback R (euclideanLocalSuspensionProjection E)
        (euclideanLocalSuspensionProjection_mapsTo E) k a)
    (c : relativeSingularHomology R {z : ℝ × E | z ≠ 0} (k + 1)) :
    singularCochainHomologyEvaluation R
        (relativeSingularChains R {z : ℝ × E | z ≠ 0}) (k + 1)
        ((shortExact_relativeSingularCochainTripleSequence R
          (euclideanPuncturedHalfSpace E (-1)) {z : ℝ × E | z ≠ 0}
          (euclideanPuncturedHalfSpace_subset E (-1))).δ k (k + 1) rfl b) c =
      singularCochainHomologyEvaluation R (relativeSingularChains R {x : E | x ≠ 0}) k a
        ((euclideanLocalSuspensionIso R E k).hom c) := by
  let A := (Subtype.val : euclideanPuncturedHalfSpace E 1 → ℝ × E) ⁻¹'
    euclideanPuncturedHalfSpace E (-1)
  let B := (Subtype.val : {z : ℝ × E | z ≠ 0} → ℝ × E) ⁻¹'
    euclideanPuncturedHalfSpace E (-1)
  let F := relativeSingularChainsMap R (euclideanLocalSuspensionInclusion E)
    (A := A) (B := B) (fun _ hx ↦ hx)
  let G := relativeSingularChainsMap R (euclideanLocalSuspensionProjection E)
    (euclideanLocalSuspensionProjection_mapsTo E)
  let J := homologyMap F k
  let : IsIso J := isIso_euclideanLocalSuspensionExcision R E k
  let d := (euclideanLocalSuspensionBoundaryIso R E k).hom c
  let z := (asIso J).inv d
  have hJz : J z = d := Iso.inv_hom_id_apply (asIso J) d
  -- The actual coboundary first pairs with the actual triple boundary of this same cycle.
  rw [relativeSingularCohomologyTripleBoundary_evaluation]
  change singularCochainHomologyEvaluation R (relativeSingularChains R B) k b d = _
  rw [← hJz]
  -- Excision and projection move across evaluation using their exact original chain maps.
  rw [singularCochainHomologyEvaluation_naturality R _ _ F k b z]
  change singularCochainHomologyEvaluation R (relativeSingularChains R A) k
    (relativeSingularCohomologyPullback R (euclideanLocalSuspensionInclusion E)
      (A := A) (B := B) (fun _ hx ↦ hx) k b) z = _
  rw [hb]
  exact (singularCochainHomologyEvaluation_naturality R _ _ G k a z).symm

end AtiyahSinger

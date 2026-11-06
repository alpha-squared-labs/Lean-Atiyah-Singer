/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactDualityMayerVietoris
public import AtiyahSinger.Topology.CompactPoincareDualityBasic
public import AtiyahSinger.Topology.CompactPoincareDualityInduction
public import AtiyahSinger.Topology.CompactPoincareDualityMayerVietoris

/-!
# Compactly supported Poincare duality on the original singular complexes

Public module ID: M1642.

E03: Hatcher, Algebraic Topology, section 3.3, Lemma 3.27 and Theorem 3.35.
The manifold is Hausdorff, second countable, and has Euclidean charts without
boundary. It need not be compact, connected, nonempty, or positive dimensional.
An integral homological orientation fixes the normalization of every compact
relative fundamental class. Its actual rational image is capped with a relative
cohomology class and then descended through the existing compact-support colimit.

The isomorphism theorem concerns this specified map, not an arbitrary equivalence.
Degrees are expressed by p + q = n; cohomology above the dimension vanishes
separately in the basic module. Euclidean normalization, the actual signed
Mayer--Vietoris cap square, and directed unions prove global bijectivity here.
All patch orientations are pulled back from the same specified ambient orientation.
Comparisons with differential-form integration and Thom-Gysin maps are separate results.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]

/-- Poincare duality for an oriented manifold, including noncompact manifolds. -/
theorem compactPoincareDuality_bijective (O : HomologicalOrientation n M)
    (p q : ℕ) (h : p + q = n) :
    Function.Bijective (compactPoincareDuality O p q h) := by
  -- Euclidean normalization, directed unions and chart induction reduce to two open sets.
  refine compactPoincareDuality_bijective_of_mayerVietoris ?_ O p q h
  intro Y _ _ _ _ U V hcover hU hV hI OY p q h
  -- Local compactness supplies regularity for the same pulled-back patch orientations.
  let : LocallyCompactSpace Y :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) Y
  have hcover' : (U : Set Y) ∪ (V : Set Y) = Set.univ :=
    congrArg (fun W : Opens Y ↦ (W : Set Y)) hcover
  -- The actual exact rows and signed connecting square give the five-lemma step.
  exact compactPoincareDuality_bijective_of_mayerVietoris_square OY U V hcover'
    (fun p q h a ↦ compactPoincareDuality_mayerVietoris OY U V hcover' p q h a)
    hU hV hI p q h

/-- The linear equivalence whose forward map is precisely the constructed cap-duality map. -/
def compactPoincareDualityEquiv (O : HomologicalOrientation n M)
    (p q : ℕ) (h : p + q = n) :
    compactSupportCohomology ℚ M p ≃ₗ[ℚ] singularHomology ℚ M q :=
  LinearEquiv.ofBijective (compactPoincareDuality O p q h).hom
    (compactPoincareDuality_bijective O p q h)

end AtiyahSinger

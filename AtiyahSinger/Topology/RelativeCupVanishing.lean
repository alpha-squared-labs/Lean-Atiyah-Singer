/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyExactness
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup

/-!
# Cup products of classes vanishing on open subspaces

Public module ID: M2077.

If two ordinary singular cohomology classes vanish on two open subspaces,
their cup product vanishes on the union. Pair exactness supplies actual
relative lifts, and the original relative union product multiplies those lifts.
The statement retains arbitrary commutative coefficient rings, degrees and ambient spaces.

This is the relative cup argument in Hatcher, Algebraic Topology, Section 3.2,
and Vector Bundles and K-Theory, proof of Theorem 3.2, pp.79–81. Iteration over
the coordinate opens of a split projective bundle proves its root relation;
no sheaf property of singular cohomology is asserted or used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Classes vanishing on two open subspaces have cup product vanishing on their union. -/
theorem singularCohomologyCup_restrict_union_eq_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (p q : ℕ)
    (a : singularCohomology R X p) (b : singularCohomology R X q)
    (ha : singularCohomologyPullback R (ContinuousMap.subtypeVal U) p a = 0)
    (hb : singularCohomologyPullback R (ContinuousMap.subtypeVal V) q b = 0) :
    singularCohomologyPullback R (ContinuousMap.subtypeVal (U ∪ V)) (p + q)
      (singularCohomologyCup R X p q a b) = 0 := by
  -- Exactness lifts each class to the relative group for its own open subspace.
  obtain ⟨a', ha'⟩ : ∃ a' : relativeSingularCohomology R U p,
      relativeSingularCohomologyToOrdinary R U p a' = a :=
    (ShortComplex.moduleCat_exact_iff _).mp
      ((shortExact_singularSubspaceCochains R U).homology_exact₂ p) a ha
  obtain ⟨b', hb'⟩ : ∃ b' : relativeSingularCohomology R V q,
      relativeSingularCohomologyToOrdinary R V q b' = b :=
    (ShortComplex.moduleCat_exact_iff _).mp
      ((shortExact_singularSubspaceCochains R V).homology_exact₂ q) b hb
  let c := relativeSingularCohomologyUnionCup R U V hU hV p q a' b'
  -- Forgetting the union condition recovers the same ordinary cup product.
  have hforget : relativeSingularCohomologyToOrdinary R (U ∪ V) (p + q) c =
      singularCohomologyCup R X p q a b := by
    have hnat := (relativeSingularCohomologyToOrdinaryNatTrans R X (p + q)).naturality
      (homOfLE (show V ⊆ U ∪ V from fun _ hv ↦ Or.inr hv)).op
    have hvalue := congrArg (fun f ↦ f c) hnat
    change relativeSingularCohomologyToOrdinary R V (p + q)
        (relativeSingularCohomologyRestriction R V (U ∪ V)
          (fun _ hv ↦ Or.inr hv) (p + q) c) =
      relativeSingularCohomologyToOrdinary R (U ∪ V) (p + q) c at hvalue
    rw [← hvalue]
    dsimp only [c]
    rw [relativeSingularCohomologyUnionCup_restrict_right,
      relativeSingularCohomologyToOrdinary_action, ha', hb']
  -- A relative class restricts to zero on its relative subspace, here the union.
  let S := (singularSubspaceCochainsSequence R (U ∪ V)).map
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (p + q))
  have hzero := congrArg (fun f ↦ f c) S.zero
  change singularCohomologyPullback R (ContinuousMap.subtypeVal (U ∪ V)) (p + q)
    (relativeSingularCohomologyToOrdinary R (U ∪ V) (p + q) c) = 0 at hzero
  rw [hforget] at hzero
  exact hzero

end AtiyahSinger

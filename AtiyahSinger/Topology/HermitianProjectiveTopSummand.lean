/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexCoordinateCupGenerator
public import AtiyahSinger.Topology.HermitianProjectiveRelativeThom
public import AtiyahSinger.Topology.ProjectiveChernTopCoefficients
public import AtiyahSinger.Topology.RelativeCohomologyShiftedCup

/-!
# The top projective power as the relative Leray--Hirsch summand

Public module ID: M1903.

The specified tautological top power lifts to the class supported at the
specified projective point. Its actual affine restriction is the coordinate
cup generator. The relative product Thom isomorphism therefore identifies
the full shifted cohomology of any parameter space with this relative term,
and forgetting support gives precisely the original cocycle cup map.

This supplies the top term in the projective hyperplane induction. The
coefficient ring is arbitrary, including the zero ring; no Kunneth flatness
or orientation sign replacement is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open CategoryTheory HomologicalComplex

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]
  (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same top tautological power gives the full relative projective summand. -/
theorem exists_hermitianProjectiveProdTopSummand
    (m : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (b : OrthonormalBasis (Fin m) ℂ (innerSL ℂ e).ker)
    (c : singularCocycles R (X × HermitianProjectiveSpace V InnerProductSpace.toCore) (2 * m))
    (hc : singularCocycleClass R
        (X × HermitianProjectiveSpace V InnerProductSpace.toCore) (2 * m) c =
      singularCohomologyPullback R
        (ContinuousMap.snd : C(X × HermitianProjectiveSpace V InnerProductSpace.toCore,
          HermitianProjectiveSpace V InnerProductSpace.toCore)) (2 * m)
        (singularCohomologyDegreeTwoPow R (HermitianProjectiveSpace V InnerProductSpace.toCore)
          (singularCohomologyChangeCoefficients R
            (HermitianProjectiveSpace V InnerProductSpace.toCore) 2 (tautologicalChernRoot V)) m))
    (n : ℕ) :
    ∃ g : ((singularCochains R X).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) (2 * m))).homology n ⟶
          relativeSingularCohomology R
            {z : X × HermitianProjectiveSpace V InnerProductSpace.toCore |
              z.2 ≠ ofVector e hne} n,
      Function.Bijective g ∧
      ∀ a, homologyMap
          (extendMap ((singularCochainsFunctor R).map (TopCat.ofHom
              (ContinuousMap.fst :
                C(X × HermitianProjectiveSpace V InnerProductSpace.toCore, X))).op)
              (ComplexShape.embeddingUp'Add (1 : ℕ) (2 * m)) ≫
            singularCochainCupMap R
              (X × HermitianProjectiveSpace V InnerProductSpace.toCore) (2 * m) c) n a =
        relativeSingularCohomologyToOrdinary R
          {z : X × HermitianProjectiveSpace V InnerProductSpace.toCore |
            z.2 ≠ ofVector e hne} n (g a) := by
  let P := HermitianProjectiveSpace V InnerProductSpace.toCore
  let K := (innerSL ℂ e).ker
  let B : Set P := {q | q ≠ ofVector e hne}
  let A : Set (X × P) := {z | z.2 ≠ ofVector e hne}
  let τ := relativeSingularCohomologyChangeCoefficients R B (2 * m)
    (projectiveTopSectionClass V m e he hne b)
  let τX := relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × P, P))
    (A := A) (B := B) (fun _ hz ↦ hz) (2 * m) τ
  -- The same orthonormal chart has real dimension twice its complex dimension.
  have hdim : Module.finrank ℝ K = 2 * m := by
    rw [finrank_real_of_complex, b.repr.toLinearEquiv.finrank_eq,
      finrank_euclideanSpace_fin]
  let l : K ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    (LinearEquiv.ofFinrankEq K (EuclideanSpace ℝ (Fin (2 * m)))
      (by simpa using hdim)).toContinuousLinearEquiv
  -- The point-supported class is the specified coordinate generator, without a sign change.
  have hgen : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (chartEmbedding e he)
        (A := {v : K | v ≠ 0}) (B := B)
        (fun v hv hz ↦ hv ((chartEmbedding_eq_ofVector_iff e he hne v).mp hz)) (2 * m) τ) := by
    dsimp only [τ, B]
    rw [projectiveTopSectionClass_changeCoefficients_pullback]
    exact complexCoordinateCup_changeCoefficients_is_generator R m b
  have hτX : relativeSingularCohomologyToOrdinary R A (2 * m) τX =
      singularCocycleClass R (X × P) (2 * m) c := by
    dsimp only [τX]
    rw [← ModuleCat.comp_apply, relativeSingularCohomologyPullback_toOrdinary,
      ModuleCat.comp_apply]
    dsimp only [τ, B]
    rw [projectiveTopSectionClass_changeCoefficients_toOrdinary]
    exact hc.symm
  -- Excision and product Thom identify supported degrees; both terms vanish below the shift.
  apply exists_relativeSingularCohomologyShiftedCupEquiv (X := X) (Y := X × P) R
    (ContinuousMap.fst : C(X × P, X)) A (2 * m) c τX hτX ?_ ?_ n
  · intro p
    exact relativeProjectiveProdAction_bijective R X (2 * m) e he hne l τ hgen p
  · intro k hk
    exact subsingleton_relativeProjectiveProd_below_dim R X (2 * m) e he hne l k hk

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

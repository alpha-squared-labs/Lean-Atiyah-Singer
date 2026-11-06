/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomology
public import AtiyahSinger.Topology.RationalCohomologyOrientation

/-!
# Coefficient inclusion on the original compact-support colimit

Public module ID: M1667.

The actual relative coefficient maps descend through the original diagram
of compact supports. Each compact representative retains its same support
and relative pair. This gives a map to the original rational compactly
supported cohomology, with its scalar action restricted to the integers.
Neither a one-point compactification nor tensoring integral cohomology is
used. No separation, local compactness or finite-generation assumption is
needed for this coefficient map.

Over a compact base, the normalized integral Thom class and zero-section
pushforward commute with coefficient inclusion on that same zero-section
support. The input to the pushforward comparison is an integral class;
the separate geometric self-intersection theorem quantifies all rational
classes, without assuming that they lift to integral classes.

Sources: Hatcher, Algebraic Topology, sections 3.1 and 3.3 for coefficient
maps and the compact-support colimit; Milnor--Stasheff Theorem 10.4 for
normalized Thom coefficient change. The comparisons below use the original Thom theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

local notation "ℚRes" => ModuleCat.restrictScalars (Int.castRingHom ℚ)

/-- Coefficient inclusion descended from the original relative classes at each compact support. -/
def compactSupportCohomologyRationalization (X : Type u) [TopologicalSpace X] (n : ℕ) :
    compactSupportCohomology ℤ X n ⟶ (ℚRes).obj (compactSupportCohomology ℚ X n) :=
  colimit.desc (compactSupportCohomologyFunctor ℤ X n)
    { pt := (ℚRes).obj (compactSupportCohomology ℚ X n)
      ι :=
        { app := fun K ↦ relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n ≫
            (ℚRes).map (compactSupportCohomologyClass ℚ X K n)
          naturality := by
            intro K L f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro a
            -- Both sides keep the same pair inclusion when the compact support is enlarged.
            have hRat := relativeSingularCohomologyRationalization_naturality
              (ContinuousMap.id X)
              (show Set.MapsTo (ContinuousMap.id X) ((L : Set X)ᶜ) ((K : Set X)ᶜ) from
                fun _ hx ↦ (Set.compl_subset_compl.mpr (leOfHom f)) hx) n a
            change compactSupportCohomologyClass ℚ X L n
                (relativeSingularCohomologyRationalization ((L : Set X)ᶜ) n
                  ((compactSupportCohomologyFunctor ℤ X n).map f a)) =
              compactSupportCohomologyClass ℚ X K n
                (relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n a)
            -- Coefficient naturality followed by the original colimit cocone gives the equality.
            exact (congrArg (compactSupportCohomologyClass ℚ X L n) hRat).trans
              (congrArg
                (fun g ↦ g (relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n a))
                (colimit.w (compactSupportCohomologyFunctor ℚ X n) f)) } }

/-- A compact representative is rationalized on its original relative pair and same support. -/
theorem compactSupportCohomologyRationalization_representative
    (X : Type u) [TopologicalSpace X] (K : Compacts X) (n : ℕ)
    (a : relativeSingularCohomology ℤ ((K : Set X)ᶜ) n) :
    compactSupportCohomologyRationalization X n (compactSupportCohomologyClass ℤ X K n a) =
      compactSupportCohomologyClass ℚ X K n
        (relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n a) := by
  /- The defining colimit descent composed with its K-th cocone leg is
  the actual relative coefficient map followed by the rational K-th leg.
  Evaluate that cocone identity on a. No larger support or replacement
  representative is chosen, and no compactification comparison is used. -/
  -- Evaluate the defining descent on the original compact-support cocone leg.
  have hleg : compactSupportCohomologyClass ℤ X K n ≫
      compactSupportCohomologyRationalization X n =
        relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n ≫
          (ℚRes).map (compactSupportCohomologyClass ℚ X K n) :=
    colimit.ι_desc _ K
  exact congrArg (fun f ↦ f a) hleg

/-- Forgetting compact support commutes with the actual coefficient homomorphism. -/
theorem compactSupportCohomologyRationalization_toOrdinary
    (X : Type u) [TopologicalSpace X] (n : ℕ) (a : compactSupportCohomology ℤ X n) :
    singularCohomologyRationalization X n (compactSupportCohomologyToOrdinary ℤ X n a) =
      compactSupportCohomologyToOrdinary ℚ X n
        (compactSupportCohomologyRationalization X n a) := by
  /- Stage 1: represent a at one compact support in the original colimit.
  The forgetful maps there are precisely the original relative-to-ordinary
  maps, while the preceding representative formula retains that support.
  Stage 2: relative coefficient inclusion commutes with the same forgetful
  maps. This gives equality on each representative and hence on the colimit.
  No assertion that rationalization is injective or surjective is needed. -/
  -- Choose one representative in the actual filtered colimit.
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative ℤ X n a
  -- Both forgetful maps evaluate at the same support, before and after coefficient change.
  have hIntegral : compactSupportCohomologyClass ℤ X K n ≫
      compactSupportCohomologyToOrdinary ℤ X n =
        relativeSingularCohomologyToOrdinary ℤ ((K : Set X)ᶜ) n :=
    colimit.ι_desc _ K
  have hRational : compactSupportCohomologyClass ℚ X K n ≫
      compactSupportCohomologyToOrdinary ℚ X n =
        relativeSingularCohomologyToOrdinary ℚ ((K : Set X)ᶜ) n :=
    colimit.ι_desc _ K
  rw [compactSupportCohomologyRationalization_representative]
  rw [show compactSupportCohomologyToOrdinary ℤ X n
      (compactSupportCohomologyClass ℤ X K n b) =
        relativeSingularCohomologyToOrdinary ℤ ((K : Set X)ᶜ) n b from
    congrArg (fun f ↦ f b) hIntegral]
  rw [show compactSupportCohomologyToOrdinary ℚ X n
      (compactSupportCohomologyClass ℚ X K n
        (relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n b)) =
        relativeSingularCohomologyToOrdinary ℚ ((K : Set X)ᶜ) n
          (relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n b) from
    congrArg (fun f ↦ f (relativeSingularCohomologyRationalization ((K : Set X)ᶜ) n b))
      hRational]
  exact relativeSingularCohomologyRationalization_toOrdinary ((K : Set X)ᶜ) n b

variable {r : ℕ} {X : Type u} [TopologicalSpace X] [CompactSpace X]
  {E : X → Type u} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same compactly supported normalized Thom class commutes with coefficient inclusion. -/
theorem compactSupportCohomologyThomClass_rationalization
    (o : CohomologyOrientation ℤ r E) :
    compactSupportCohomologyRationalization (TotalSpace (EuclideanSpace ℝ (Fin r)) E) r
        (compactSupportCohomologyThomClass ℤ r E o) =
      compactSupportCohomologyThomClass ℚ r E o.rationalization := by
  /- The two supported classes use the identical original zero-section
  compact set. Apply the representative formula there and the normalized
  relative Thom-class comparison. The rational orientation is the actual
  coefficient image of o on each fiber, so no generator is rescaled. -/
  -- Both classes use the same original zero-section support.
  unfold compactSupportCohomologyThomClass
  rw [compactSupportCohomologyRationalization_representative]
  exact congrArg (compactSupportCohomologyClass ℚ
    (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (cohomologyZeroSectionSupport r E) r)
    (cohomologyThomClass_rationalization o)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The compact-support Thom pushforward commutes with coefficient inclusion of integral inputs. -/
theorem cohomologyZeroSectionPushforward_rationalization
    (o : CohomologyOrientation ℤ r E) (p : ℕ) (a : singularCohomology ℤ X p) :
    compactSupportCohomologyRationalization (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)
        (cohomologyZeroSectionPushforward ℤ r E o p a) =
      cohomologyZeroSectionPushforward ℚ r E o.rationalization p
        (singularCohomologyRationalization X p a) := by
  /- Stage 1: both pushforwards are the actual Thom multiplication followed
  by the cocone leg for the original zero-section compact support.
  Stage 2: commute coefficient inclusion with that leg, the projection
  pullback and the ordinary-relative cup product. The rational Thom class
  is the coefficient image of the same normalized integral Thom class.
  This establishes the square for integral a. It does not assert that
  every rational class has an integral lift; the general rational
  self-intersection formula is proved directly in rational coefficients. -/
  -- Retain the cocone leg of the same zero-section support and the same Thom map.
  change compactSupportCohomologyRationalization
      (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r)
      (compactSupportCohomologyClass ℤ (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
        (cohomologyZeroSectionSupport r E) (p + r) (cohomologyThomMap ℤ r E o p a)) = _
  rw [compactSupportCohomologyRationalization_representative]
  exact congrArg (compactSupportCohomologyClass ℚ
    (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (cohomologyZeroSectionSupport r E) (p + r))
    (cohomologyThomMap_rationalization o p a)

end AtiyahSinger

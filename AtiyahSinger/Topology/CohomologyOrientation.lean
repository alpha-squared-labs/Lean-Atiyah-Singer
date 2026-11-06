/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Local cohomological orientations of the original real vector bundle

Public module ID: M1623.

C03. The pair is the original total space with the zero section removed.
A cohomological R-orientation specifies generators of the top relative
cohomology of its actual fibers. Local compatibility means that near each
base point these generators are restrictions of one local relative class.
It does not require a global class or assume the Thom isomorphism.

Milnor--Stasheff, Characteristic Classes, Section 9, pp.96--97, derives this
local-generator condition from positively oriented local frames before
Theorem 9.1. Here it is retained as the standard cohomological R-orientation
condition. An R-generator means a basis with one element: scalar
multiplication from R is bijective. This also makes sense for the zero ring.
Arbitrary units of R give more choices than the two signs of an integral
geometric orientation. The converse comparison on a general base and the
coefficient normalization from geometric orientations are not asserted.

Every inclusion and topology below is inherited from the given native vector
bundle. Restriction to an open base subset uses the literal subspace of its
original total space, not a separately selected bundle or cohomology theory.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

universe u

variable (R : Type) [CommRing R]
  (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]

/-- The complement of the zero section in the original total space. -/
def bundleNonzero : Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
  {z | z.snd ≠ 0}

/-- The actual total space over the given subset of the base, with its subspace topology. -/
abbrev BundleTotalOver (U : Set X) : Type u :=
  {z : TotalSpace (EuclideanSpace ℝ (Fin r)) E // z.proj ∈ U}

/-- The nonzero vectors in the original total space restricted over U. -/
def bundleNonzeroOver (U : Set X) : Set (BundleTotalOver r E U) :=
  {z | z.val.snd ≠ 0}

variable [FiberBundle (EuclideanSpace ℝ (Fin r)) E]

/-- Projection to the original base, with the native bundle continuity certificate. -/
def bundleProjection : C(TotalSpace (EuclideanSpace ℝ (Fin r)) E, X) :=
  ⟨π (EuclideanSpace ℝ (Fin r)) E,
    FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin r)) E⟩

/-- Inclusion of the original fiber into the original total space. -/
def bundleFiberInclusion (x : X) : C(E x, TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
  ⟨fun v ↦ ⟨x, v⟩, FiberBundle.continuous_totalSpaceMk (EuclideanSpace ℝ (Fin r)) E x⟩

/-- The same fiber inclusion, with codomain the actual restriction over U. -/
def bundleFiberInclusionOver (U : Set X) (x : X) (hx : x ∈ U) :
    C(E x, BundleTotalOver r E U) :=
  ⟨fun v ↦ ⟨⟨x, v⟩, hx⟩,
    (FiberBundle.continuous_totalSpaceMk (EuclideanSpace ℝ (Fin r)) E x).subtype_mk _⟩

variable [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

/-- The zero section into the original total space, retaining its original topology. -/
def bundleZeroSection : C(X, TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
  ⟨zeroSection (EuclideanSpace ℝ (Fin r)) E, Trivialization.continuous_zeroSection ℝ⟩

/-- A locally compatible family of generators of the actual relative fiber cohomology. -/
structure CohomologyOrientation where
  /-- The chosen top relative class on each original fiber. -/
  fiberClass : ∀ x : X, relativeSingularCohomology R {v : E x | v ≠ 0} r
  /-- Each class freely generates its fiber cohomology as a module over the coefficient ring. -/
  is_generator : ∀ x : X, Function.Bijective (fun a : R ↦ a • fiberClass x)
  /-- On some open neighborhood the prescribed fiber classes have a common local extension. -/
  locally_compatible : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ c : relativeSingularCohomology R (bundleNonzeroOver r E U) r,
      ∀ (y : X) (hy : y ∈ U),
        relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E U y hy)
          (A := {v : E y | v ≠ 0}) (B := bundleNonzeroOver r E U)
          (fun _ hv ↦ hv) r c = fiberClass y

end AtiyahSinger

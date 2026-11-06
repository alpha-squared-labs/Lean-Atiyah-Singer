/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Geometry.SmoothAtlasSections

/-!
# Differential operators on bundles with locally varying rank

Public module ID: M1047.

D03: the usual local definition of a finite-order differential operator, acting
on the actual smooth sections of the specified bundle atlases. The source and
target chart ranks are independent; no global rank, connectedness, fiber norm,
or replacement topology is chosen. Each local formula reuses the existing
CoordinateDifferentialOperator and its convention D_j = -i partial_j.

The principal-symbol predicate compares actual fiber maps with the leading
coordinate polynomials. It assumes neither existence nor uniqueness of those
maps. Existence and uniqueness are separate results in AtlasPrincipalSymbol.

Sources: Spin Geometry III.1.1-1.3, pp.167-168. The locally varying finite-rank
convention is recorded in SmoothComplexBundleAtlas. The fixed-rank DifferentialOperator
is compared by an explicit adapter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- The actual section coordinates in a manifold chart and a specified bundle chart.
The finite coordinate tuple is identified with the existing Euclidean coordinate model. -/
def atlasSectionInChart
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (i : A.Index)
    (s : ∀ x : M, E x) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin (A.rank i)) :=
  fun z ↦ (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
    ((A.chart i ⟨c.symm z, s (c.symm z)⟩).2)

/-- A local differential expression represents the given map of actual smooth sections. -/
def HasAtlasCoordinateExpression (m : ℕ)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (i : A.Index) (j : B.Index) (U : Set M)
    (Q : CoordinateDifferentialOperator n (A.rank i) (B.rank j) m (c '' U)) : Prop :=
  U ⊆ c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet ∧
    ∀ (s : A.smoothSections) (x : M), x ∈ U →
      (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm
          ((B.chart j ⟨x, (P s).val x⟩).2) =
        Q.apply (atlasSectionInChart A c i s.val) (c x)

/-- The standard local finite-order condition, with the rank supplied separately by each chart. -/
def IsAtlasDifferentialOperator (m : ℕ)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) : Prop :=
  ∀ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (i : A.Index) (j : B.Index),
        ∀ x ∈ c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet,
          ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
            ∃ Q : CoordinateDifferentialOperator n (A.rank i) (B.rank j) m (c '' U),
              HasAtlasCoordinateExpression A B m P c i j U Q

/-- A finite-order differential operator between the specified locally finite-rank bundles. -/
structure AtlasDifferentialOperator (m : ℕ) where
  /-- The actual complex-linear action on the original smooth sections. -/
  toLinearMap : A.smoothSections →ₗ[ℂ] B.smoothSections
  /-- In every specified chart the action has a smooth expression of order at most m. -/
  isAtlasDifferentialOperator : IsAtlasDifferentialOperator A B m toLinearMap

/-- The leading polynomial identities characterizing a symbol on the original fibers.
All local expressions for the same section operator must give this same fiber map. -/
def HasAtlasPrincipalSymbol (m : ℕ)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (σ : ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) →
      (E x →ₗ[ℂ] F x)) : Prop :=
  ∀ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (i : A.Index) (j : B.Index) (U : Set M), IsOpen U →
        ∀ Q : CoordinateDifferentialOperator n (A.rank i) (B.rank j) m (c '' U),
          HasAtlasCoordinateExpression A B m P c i j U Q →
            ∀ x ∈ U,
              ∀ (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (v : E x),
                (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm
                    ((B.chart j ⟨x, σ x ξ v⟩).2) =
                  Q.principalSymbol (c x) (covectorInChart c x ξ)
                    ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
                      ((A.chart i ⟨x, v⟩).2))

end AtiyahSinger

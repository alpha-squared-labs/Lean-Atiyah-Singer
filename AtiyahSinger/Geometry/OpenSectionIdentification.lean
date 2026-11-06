/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Geometry.SmoothSectionPullback
public import AtiyahSinger.Geometry.SupportedSectionEquivalence

/-!
# Identification of supported sections through a common open region

Public module ID: M1324.

UL03/P02: restrict to an open submanifold, apply the specified smooth fiber
equivalence, undo a diffeomorphism pullback, and extend by zero in the other
ambient manifold. This is the concrete standard section identification used in
SG III.13.4, pp.248--249, with no operator or adjoint compatibility assumed.
The existing fixed-rank bundle package is used; variable-rank bundles are outside
this interface. Closed ambient supports suffice, without compact ambient spaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

/-- Restriction, specified fiber transport, inverse base change, and zero extension. -/
def supportedSmoothSectionOpenEquiv
    (E : SmoothFiniteComplexBundle (n := n) M) (F : SmoothFiniteComplexBundle (n := m) N)
    (U : Opens M) (V : Opens N)
    (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ V)
    (K : Set M) (L : Set N) (hK : IsClosed K) (hL : IsClosed L)
    (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
    (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
    (a : ∀ x : U,
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
        (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
          ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber)) x)
    (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (a x).toLinearMap)) :
    supportedSmoothSections (n := n) (r := E.rank) E.Fiber K ≃ₗ[ℂ]
      supportedSmoothSections (n := m) (r := F.rank) F.Fiber L := by
  -- Restrict the ambient section and apply the given bundle map on the open region.
  let R := supportedSmoothSectionRestrictionEquiv (n := n) (r := E.rank) E.Fiber U K hK hKU
  let A := supportedSmoothSectionEquiv (M := U) (n := n) (r := E.rank) (q := F.rank)
    (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber))
    (F := (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
      ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber)))
    ((Subtype.val : U → M) ⁻¹' K) a ha
  -- Align the support sets without changing any section values.
  let D := supportedSmoothSectionDiffeomorphEquiv (M := U) (N := V)
    (n := n) (m := m) (r := F.rank)
    ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber) e
    ((Subtype.val : V → N) ⁻¹' L)
  let C := LinearEquiv.ofEq _ _
    (congrArg (supportedSmoothSections (n := n) (r := F.rank)
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber))) hKL.symm)
  -- Undo base pullback and extend by zero in N, using closedness of L in N.
  let S := supportedSmoothSectionRestrictionEquiv (n := m) (r := F.rank) F.Fiber V L hL hLV
  exact ((R.trans A).trans C).trans (D.symm.trans S.symm)

end AtiyahSinger

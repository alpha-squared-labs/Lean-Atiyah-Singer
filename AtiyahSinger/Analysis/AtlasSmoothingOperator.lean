/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolev

/-!
# Smoothing operators on locally finite-rank smooth bundles

Public module ID: M0303.

D05: use the all-order Sobolev definition in Spin Geometry III.3, p.186.
An actual operator on smooth sections is smoothing when it extends boundedly
from every real Sobolev order to every real Sobolev order, using every pair
of finite presentations. The existence of such presentations on the compact
smooth base is supplied independently by nonempty_atlasBundlePresentation.

SG writes the target order as s+t; quantifying both source and target orders
independently is equivalent. No kernel or density is chosen in this definition.
In particular it does not restrict the support of the operator or forbid
maps between different connected components with different fiber ranks.
The comparison with the earlier smooth-kernel predicate is a separate bridge.
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

/-- SG's smoothing condition: bounded extension between every pair of real Sobolev orders.
Compactness ensures that the quantified finite presentations exist. -/
def IsAtlasSmoothingOperator
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) : Prop :=
  ∀ (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) (s t : ℝ),
    ∃ T : L.SobolevSpace s →L[ℂ] K.SobolevSpace t,
      ∀ u : A.smoothSections,
        T (L.smoothToSobolev s u) = K.smoothToSobolev t (P u)

end AtiyahSinger

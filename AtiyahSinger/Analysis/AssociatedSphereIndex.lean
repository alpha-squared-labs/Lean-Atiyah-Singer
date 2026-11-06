/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSpherePositiveIndex

/-!
# The associated-sphere index in all dimensions

Public module ID: M0117.

The twisted-product index formula is obtained from the zero-dimensional base,
zero-dimensional sphere, and positive-dimensional cases.
-/

@[expose] public noncomputable section

set_option Elab.async false

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

open scoped Matrix.Norms.Elementwise

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "OG" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle OG P (OrthogonalSphere r)
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "C" => fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ

variable [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the same associated full coefficient and original sphere product
-- index.
/-- SG III.13.6: the original twisted product is indexed by its associated full coefficient. -/
theorem analyticIndex_associatedSphereTwistedProduct
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero OG SphereCot) :
    associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
      analyticIndexOfComponents μ
        (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle
            (orthogonalSphereAnalyticIndex r v)) u) := by
  /- Split off a zero-dimensional base and a zero-dimensional sphere first.
  The positive-dimensional case uses the intrinsic-to-cutoff, cutoff-to-coordinate,
  coordinate-to-kernel, and kernel-to-coefficient index comparisons with the same
  associated bundle and input K classes. -/
  -- The finite-dimensional branches preserve arbitrary virtual classes and all original poles.
  by_cases hn : n = 0
  · subst n
    exact associatedSphere_zero_base_index_call S μ u v
  by_cases hr : r = 0
  · subst r
    exact associatedSphere_zero_index_call S μ u v
  -- In positive dimensions use the same descended operator, adjoint and supported symbol class.
  exact analyticIndex_associatedSphereTwistedProduct_of_pos S μ
    (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hr) u v

end AtiyahSinger

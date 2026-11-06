/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OrthogonalPointIndex
public import AtiyahSinger.Topology.OrthogonalFixedPointPushforward

/-!
# The index of any specified orthogonal fixed-point inclusion

Public module ID: M0635.

SG III.13, Lemma 13.7, printed p.253. The specified smooth point
inclusion determines its actual Thom/open-extension map. Its full comparison
with the canonical pole map transfers the independently established ASI
normalization to this very inclusion and every representation coefficient.
Both fixed points and dimension zero are covered. The invalid cancellation
in SG's printed proof is not used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphereTangent

set_option maxSynthPendingDepth 30

/-- The original equivariant index recovers every coefficient of the actual fixed-point map. -/
theorem orthogonalSphereTangentAnalyticIndex_fixedPointPushforward {r : ℕ}
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x)
    (a : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) :
    orthogonalSphereTangentAnalyticIndex r
      (orthogonalSphereFixedPointPushforward j hj a) = a := by
  /- Stage 1: apply orthogonalSphereFixedPointPushforward_eq_pole to the
  same j and hj. Its witness supplies both the equality of the specified
  smooth inclusion with an actual pole and the equality of their entire
  R(O(r))-linear pushforward maps. The geometric comparison uses the
  original derivative tube, positive Bott class and actual open extension.
  Stage 2: evaluate that homomorphism equality at this same coefficient a.
  Apply orthogonalSphereTangentAnalyticIndex_polePushforward at the supplied
  pole. The original index and its inverse round musical transport are
  unchanged. The result is equality in R(O(r)), not just after dimension
  or restriction to SO(r). The zero-dimensional normalization follows from
  the established low-dimensional product relations, so r=0 needs no extra premise.
  No Euler class is cancelled and no embedding-index theorem is used. -/
  -- The geometric comparison identifies the entire original point map for this same inclusion.
  obtain ⟨b, _hj, hpush⟩ := orthogonalSphereFixedPointPushforward_eq_pole j hj
  rw [hpush]
  exact orthogonalSphereTangentAnalyticIndex_polePushforward r b a

end AtiyahSinger

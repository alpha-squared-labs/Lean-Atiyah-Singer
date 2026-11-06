/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedTrivialSupport
public import AtiyahSinger.Topology.AssociatedTwistedProduct
public import AtiyahSinger.Topology.CompactSupportProductNaturality

/-!
# The original twisted product for a trivial structure group

Public module ID: M1556.

The proper paired pullback in the original definition becomes the ordinary
external product under the quotient-to-product homeomorphism. The proof keeps
the exact principal pullback and both original K classes. In particular, it
does not require constant bundle ranks on a disconnected fiber.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle

variable {G P B X Y : Type*} [Group G] [Subsingleton G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace P] [TopologicalSpace B] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [hP : IsPrincipalBundle G projection] [CompactSpace B] [T2Space B]
  [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [LocallyCompactSpace Y] [T2Space Y]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The trivial-group twisted product is the original external product in quotient coordinates. -/
theorem exists_associatedSupportTwistedProduct_eq_externalProduct_of_subsingleton
    (f : C(X, B)) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    ∃ e : AssociatedBundle G (PrincipalBundlePullback f projection) Y ≃ₜ X × Y,
      (∀ (p : PrincipalBundlePullback f projection) (y : Y),
        e (associatedBundleMk G (PrincipalBundlePullback f projection) Y p y) =
          (p.val.1, y)) ∧
      ∀ (u : CompactSupportKZero X) (v : EquivariantSupportTripleKZero G Y),
        associatedSupportTwistedProduct (G := G) (projection := projection) f u v =
          compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap
            (compactSupportKZeroExternalProduct u
              (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget v))) := by
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let hQ := isPrincipalBundle_pullback (G := G) (projection := projection) f
  let := associatedBundle_t2Space (Y := Y) hQ
  let := associatedBundle_locallyCompactSpace (Y := Y) hQ
  let Z := AssociatedBundle G P Y
  let W := AssociatedBundle G (PrincipalBundlePullback f projection) Y
  obtain ⟨q, hq, hqmk, hqclass⟩ :=
    exists_associatedSupportKZero_eq_pullback_of_subsingleton (Y := Y) hP
  have hact (g : G) (y : Y) : g • y = y := by
    rw [Subsingleton.elim g 1, one_smul]
  obtain ⟨e, he⟩ := exists_associatedBundle_homeomorph_of_trivial_action hQ hact
  refine ⟨e, he, ?_⟩
  intro u v
  let p : C(W, X × Z) := associatedBundlePullbackProdMap (G := G) (Y := Y) f
  have hp : IsProperMap p := (associatedBundlePullbackProdMap_isClosedEmbedding f).isProperMap
  let j : C(X × Z, X × Y) := (ContinuousMap.id X).prodMap q
  have hj : IsProperMap j := isProperMap_id.prodMap hq
  -- The same principal representative makes the full proper square commute.
  have hsquare : j.comp p = (⟨e, e.continuous⟩ : C(W, X × Y)) := by
    apply ContinuousMap.ext
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      have hpair : (j.comp p) (associatedBundleMk G
          (PrincipalBundlePullback f projection) Y z.1 z.2) = (z.1.val.1, z.2) :=
        Prod.ext rfl (hqmk z.1.val.2 z.2)
      exact hpair.trans (he z.1 z.2).symm
  let b := supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget v)
  have hnat := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) isProperMap_id q hq u b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hnat
  -- Proper product naturality and composition apply before any change of K representatives.
  change compactSupportKZeroPullback p hp
    (compactSupportKZeroExternalProduct u (associatedSupportKZero hP v)) = _
  rw [hqclass, ← hnat]
  have hcomp := DFunLike.congr_fun (compactSupportKZeroPullback_comp p j hp hj)
    (compactSupportKZeroExternalProduct u b)
  simpa only [hsquare, AddMonoidHom.comp_apply] using hcomp.symm

end AtiyahSinger

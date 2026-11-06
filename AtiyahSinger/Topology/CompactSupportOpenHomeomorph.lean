/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyHomeomorph
public import AtiyahSinger.Topology.CompactSupportOpenExtension

/-!
# Open extension along the original homeomorphism

Public module ID: M1682.

Extension by excision along a homeomorphism is the inverse of its specified
compact-support pullback. This identifies the two existing constructions on
the same relative representatives and supports, before passing to the colimit.

Source: functoriality and excision of singular cohomology with compact support.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual open extension along a homeomorphism is the inverse of its actual support pullback. -/
theorem compactSupportCohomologyOpenExtension_homeomorph
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (e : X ≃ₜ Y) (n : ℕ) (a : compactSupportCohomology R X n) :
    compactSupportCohomologyOpenExtension R ⟨e, e.continuous⟩ e.isOpenEmbedding n a =
      (compactSupportCohomologyHomeomorphEquiv R e n).symm a := by
  let E := compactSupportCohomologyHomeomorphEquiv R e n
  apply E.injective
  rw [E.apply_symm_apply]
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X n a
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let L := openEmbeddingCompactImage f K
  let P := openEmbeddingCohomologySupportPullback R f e.isOpenEmbedding K n
  let : IsIso P := isIso_openEmbeddingCohomologySupportPullback R f e.isOpenEmbedding K n
  let β := (asIso P).inv α
  have hβ : P β = α := (asIso P).inv_hom_id_apply α
  have hK : homeomorphCompactPreimage e L = K := by
    apply Compacts.ext
    exact Set.preimage_image_eq _ e.injective
  have hclass (K' : Compacts X) (h : K' = K)
      (hf : Set.MapsTo f ((K' : Set X)ᶜ) ((L : Set Y)ᶜ)) :
      compactSupportCohomologyClass R X K' n
        (relativeSingularCohomologyPullback R f hf n β) =
      compactSupportCohomologyClass R X K n (P β) := by
    subst K'
    rfl
  -- Restriction cancels this very excision inverse at its original image support.
  rw [compactSupportCohomologyOpenExtension_representative]
  change compactSupportCohomologyHomeomorphPullback R e n
    (compactSupportCohomologyClass R Y L n β) = _
  rw [compactSupportCohomologyHomeomorphPullback_representative]
  exact (hclass (homeomorphCompactPreimage e L) hK _).trans
    (congrArg (compactSupportCohomologyClass R X K n) hβ)

end AtiyahSinger

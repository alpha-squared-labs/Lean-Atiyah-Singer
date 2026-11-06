/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyThom
public import AtiyahSinger.Topology.CompactSupportOpenExtension

/-!
# Local restriction and open extension of the same supported Thom class

Public module ID: M2217.

Pulling the specified supported Thom class into a chart gives the two-relative
cup of the pulled-back base class and the restriction of its original Thom
class. The support equality only changes the named relative subset. If an
open embedding contains this support, excision extends that same restriction
back to the original compact-support Thom image.

These formulas retain the given global orientation and Thom class. No new
orientation on a restricted bundle is chosen. They apply in particular to
the singleton supports used in local integral normalization.

Source: naturality of relative cup and open excision, Hatcher, Algebraic
Topology, sections 3.2--3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X] [T2Space X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

local notation "TE" => TotalSpace (EuclideanSpace ℝ (Fin r)) E

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback of the supported Thom class is cup with the restriction of its same Thom factor. -/
theorem supportedCohomologyThomMap_pullback (K : Compacts X) (p : ℕ)
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) p)
    {Y : Type u} [TopologicalSpace Y] (f : C(Y, TE)) :
    let A := (bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)
    let B := bundleNonzero r E
    let hOpen := isOpen_supportedCohomologyThomSubspaces r E K
    relativeSingularCohomologyPullback R f
        (A := (f ⁻¹' A) ∪ (f ⁻¹' B))
        (B := ((supportedCohomologyThomSupport r E K : Set TE)ᶜ))
        (fun _ hz ↦ by
          rw [← supportedCohomologyThomSupport_compl r E K]
          exact hz) (p + r) (supportedCohomologyThomMap R r E o K p a) =
      relativeSingularCohomologyUnionCup R (f ⁻¹' A) (f ⁻¹' B)
        (hOpen.1.preimage f.continuous) (hOpen.2.preimage f.continuous) p r
        (relativeSingularCohomologyPullback R ((bundleProjection r E).comp f)
          (A := f ⁻¹' A) (B := ((K : Set X)ᶜ)) (fun _ hz ↦ hz) p a)
        (relativeSingularCohomologyPullback R f (A := f ⁻¹' B) (B := B)
          (fun _ hz ↦ hz) r (cohomologyThomClass R r E o)) := by
  let A := (bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)
  let B := bundleNonzero r E
  let hOpen := isOpen_supportedCohomologyThomSubspaces r E K
  -- Equality of the target relative subset commutes with this same pair pullback.
  have htransport (S T : Set TE) (h : S = T) (W : Set Y)
      (hfS : Set.MapsTo f W S) (hfT : Set.MapsTo f W T)
      (k : ℕ) (c : relativeSingularCohomology R S k) :
      relativeSingularCohomologyPullback R f hfT k
          ((eqToIso (congrArg (fun V ↦ relativeSingularCohomology R V k) h)).hom c) =
        relativeSingularCohomologyPullback R f hfS k c := by
    subst T
    rfl
  change relativeSingularCohomologyPullback R f _ (p + r)
    ((eqToIso (congrArg (fun V ↦ relativeSingularCohomology R V (p + r))
      (supportedCohomologyThomSupport_compl r E K))).hom
      (relativeSingularCohomologyUnionCup R A B hOpen.1 hOpen.2 p r
        (relativeSingularCohomologyPullback R (bundleProjection r E)
          (A := A) (B := ((K : Set X)ᶜ)) (fun _ hz ↦ hz) p a)
        (cohomologyThomClass R r E o))) = _
  rw [htransport (A ∪ B) ((supportedCohomologyThomSupport r E K : Set TE)ᶜ)
    (supportedCohomologyThomSupport_compl r E K) ((f ⁻¹' A) ∪ (f ⁻¹' B))
    (fun _ hz ↦ hz)]
  -- Both factors are pulled back before cup; their order and original Thom witness stay fixed.
  rw [relativeSingularCohomologyPullback_unionCup R f
    (hOpen.1.preimage f.continuous) (hOpen.2.preimage f.continuous)
    hOpen.1 hOpen.2 (fun _ hz ↦ hz) (fun _ hz ↦ hz)]
  rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original Thom image is the open extension of its actual local two-relative cup. -/
theorem compactSupportCohomologyThomMap_eq_openExtension (K : Compacts X) (p : ℕ)
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) p)
    {Y : Type u} [TopologicalSpace Y] (f : C(Y, TE)) (hf : IsOpenEmbedding f)
    (L : Compacts Y)
    (hL : openEmbeddingCompactImage f L = supportedCohomologyThomSupport r E K) :
    letI : T2Space TE := t2Space_fiberBundleTotal (EuclideanSpace ℝ (Fin r)) E
    let A := f ⁻¹' ((bundleProjection r E) ⁻¹' ((K : Set X)ᶜ))
    let B := f ⁻¹' bundleNonzero r E
    let hOpen := isOpen_supportedCohomologyThomSubspaces r E K
    let hS : A ∪ B = (L : Set Y)ᶜ := by
      change f ⁻¹' (((bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)) ∪ bundleNonzero r E) = _
      rw [supportedCohomologyThomSupport_compl, ← hL, Set.preimage_compl]
      exact congrArg Set.compl (Set.preimage_image_eq _ hf.injective)
    compactSupportCohomologyThomMap R r E o p (compactSupportCohomologyClass R X K p a) =
      compactSupportCohomologyOpenExtension R f hf (p + r)
        (compactSupportCohomologyClass R Y L (p + r)
          ((eqToIso (congrArg (fun V ↦ relativeSingularCohomology R V (p + r)) hS)).hom
            (relativeSingularCohomologyUnionCup R A B
              (hOpen.1.preimage f.continuous) (hOpen.2.preimage f.continuous) p r
              (relativeSingularCohomologyPullback R ((bundleProjection r E).comp f)
                (A := A) (B := ((K : Set X)ᶜ)) (fun _ hz ↦ hz) p a)
              (relativeSingularCohomologyPullback R f (A := B) (B := bundleNonzero r E)
                (fun _ hz ↦ hz) r (cohomologyThomClass R r E o))))) := by
  let : T2Space TE := t2Space_fiberBundleTotal (EuclideanSpace ℝ (Fin r)) E
  let A := f ⁻¹' ((bundleProjection r E) ⁻¹' ((K : Set X)ᶜ))
  let B := f ⁻¹' bundleNonzero r E
  let hOpen := isOpen_supportedCohomologyThomSubspaces r E K
  have hS : A ∪ B = (L : Set Y)ᶜ := by
    change f ⁻¹' (((bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)) ∪ bundleNonzero r E) = _
    rw [supportedCohomologyThomSupport_compl, ← hL, Set.preimage_compl]
    exact congrArg Set.compl (Set.preimage_image_eq _ hf.injective)
  let P := openEmbeddingCohomologySupportPullback R f hf L (p + r)
  let := isIso_openEmbeddingCohomologySupportPullback R f hf L (p + r)
  let c := supportedCohomologyThomMap R r E o K p a
  let c' := (eqToIso (congrArg
    (fun Q : Compacts TE ↦ relativeSingularCohomology R ((Q : Set TE)ᶜ) (p + r))
    hL.symm)).hom c
  -- Identify this actual support restriction with the two-relative chart cup.
  have htransport (S T : Set TE) (h : S = T) (V W : Set Y) (hVW : V = W)
      (hfV : Set.MapsTo f V S) (hfW : Set.MapsTo f W T)
      (d : relativeSingularCohomology R S (p + r)) :
      relativeSingularCohomologyPullback R f hfW (p + r)
          ((eqToIso (congrArg (fun Q ↦ relativeSingularCohomology R Q (p + r)) h)).hom d) =
        (eqToIso (congrArg (fun Q ↦ relativeSingularCohomology R Q (p + r)) hVW)).hom
          (relativeSingularCohomologyPullback R f hfV (p + r) d) := by
    subst T
    subst W
    rfl
  have hrestrict : P c' =
      (eqToIso (congrArg (fun V ↦ relativeSingularCohomology R V (p + r)) hS)).hom
        (relativeSingularCohomologyUnionCup R A B
          (hOpen.1.preimage f.continuous) (hOpen.2.preimage f.continuous) p r
          (relativeSingularCohomologyPullback R ((bundleProjection r E).comp f)
            (A := A) (B := ((K : Set X)ᶜ)) (fun _ hz ↦ hz) p a)
          (relativeSingularCohomologyPullback R f (A := B) (B := bundleNonzero r E)
            (fun _ hz ↦ hz) r (cohomologyThomClass R r E o))) := by
    have hcomp : Set.MapsTo f (A ∪ B)
        ((supportedCohomologyThomSupport r E K : Set TE)ᶜ) := by
      intro z hz
      rw [← supportedCohomologyThomSupport_compl r E K]
      exact hz
    change relativeSingularCohomologyPullback R f _ (p + r)
      ((eqToIso (congrArg
        (fun Q ↦ relativeSingularCohomology R Q (p + r))
        (congrArg (fun Q : Compacts TE ↦ (Q : Set TE)ᶜ) hL.symm))).hom c) = _
    rw [htransport _ _ (congrArg (fun Q : Compacts TE ↦ (Q : Set TE)ᶜ) hL.symm)
      (A ∪ B) ((L : Set Y)ᶜ) hS hcomp]
    exact congrArg
      (eqToIso (congrArg (fun V ↦ relativeSingularCohomology R V (p + r)) hS)).hom
      (supportedCohomologyThomMap_pullback R r E o K p a f)
  -- The specified relative pullback is exactly the inverse used by extension at L.
  change _ = compactSupportCohomologyOpenExtension R f hf (p + r)
    (compactSupportCohomologyClass R Y L (p + r) _)
  rw [← hrestrict, compactSupportCohomologyThomMap_representative,
    compactSupportCohomologyOpenExtension_representative]
  change compactSupportCohomologyClass R TE (supportedCohomologyThomSupport r E K)
    (p + r) c = compactSupportCohomologyClass R TE (openEmbeddingCompactImage f L)
      (p + r) ((asIso P).inv ((asIso P).hom c'))
  rw [Iso.hom_inv_id_apply]
  -- Replacing the equal compact support is only the canonical equality transport.
  have hclass (S T : Compacts TE) (h : S = T)
      (d : relativeSingularCohomology R ((S : Set TE)ᶜ) (p + r)) :
      compactSupportCohomologyClass R TE T (p + r)
          ((eqToIso (congrArg
            (fun Q : Compacts TE ↦ relativeSingularCohomology R ((Q : Set TE)ᶜ) (p + r))
              h)).hom d) = compactSupportCohomologyClass R TE S (p + r) d := by
    subst T
    rfl
  exact (hclass _ _ hL.symm c).symm

end AtiyahSinger

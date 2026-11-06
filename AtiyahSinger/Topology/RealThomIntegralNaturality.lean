/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactBaseCohomologyThom
public import AtiyahSinger.Topology.CohomologyThomNaturality

/-!
# Naturality of the original real Thom integral

Public module ID: M2049.

A specified proper map of equal-rank bundles preserving the actual fiber
orientation classes commutes with the inverse of the original supported Thom
map. The forward Thom naturality theorem supplies the comparison; both inverse
identities cancel the very same normalized cup-product maps.

Source: naturality of oriented Thom isomorphisms, Milnor--Stasheff, Section 9.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

universe u

variable (R : Type) [CommRing R] (r : ℕ)
  {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E]
  (F : Y → Type u) [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℝ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) F)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) F]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) F]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) F]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified real Thom inverse commutes with the same proper oriented bundle map. -/
theorem compactSupportCohomologyFiberIntegral_pullback
    (oE : CohomologyOrientation R r E) (oF : CohomologyOrientation R r F)
    (f : C(X, Y))
    (g : C(TotalSpace (EuclideanSpace ℝ (Fin r)) E,
      TotalSpace (EuclideanSpace ℝ (Fin r)) F))
    (hN : Set.MapsTo g (bundleNonzero r E) (bundleNonzero r F))
    (e : ∀ x, E x ≃L[ℝ] F (f x))
    (hg : ∀ x, g.comp (bundleFiberInclusion r E x) =
      (bundleFiberInclusion r F (f x)).comp ⟨e x, (e x).continuous⟩)
    (ho : ∀ x, relativeSingularCohomologyPullback R
      (⟨e x, (e x).continuous⟩ : C(E x, F (f x)))
        (show Set.MapsTo (e x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
          fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))) r
        (oF.fiberClass (f x)) = oE.fiberClass x)
    (hgProper : IsProperMap g) (p : ℕ)
    (a : compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) F) (p + r)) :
    compactSupportCohomologyFiberIntegral R r E oE p
        (compactSupportCohomologyProperPullback R g hgProper (p + r) a) =
      singularCohomologyPullback R f p (compactSupportCohomologyFiberIntegral R r F oF p a) := by
  -- Recover the original target class by its same Thom map before using oriented naturality.
  have h := cohomologyZeroSectionPushforward_pullback R r E F oE oF f g hN e hg ho hgProper p
    (compactSupportCohomologyFiberIntegral R r F oF p a)
  have hrecover : cohomologyZeroSectionPushforward R r F oF p
      (compactSupportCohomologyFiberIntegral R r F oF p a) = a :=
    (compactBaseCohomologyThomEquiv R r F oF p).apply_symm_apply a
  rw [hrecover] at h
  rw [h]
  -- The source integral cancels only its own original normalized Thom multiplication.
  exact (compactBaseCohomologyThomEquiv R r E oE p).symm_apply_apply _

end AtiyahSinger

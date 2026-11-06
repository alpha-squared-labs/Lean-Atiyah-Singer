/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKMinusOneBoundary
public import AtiyahSinger.Topology.BundleKMinusOneFunctor
public import AtiyahSinger.Topology.TripleKZeroComparison

import Mathlib.Algebra.FiveLemma

/-!
# Compact-pair exactness before the Puppe construction

Public module ID: M1585.

Karoubi II.3.23 gives K^{-1}(X) → K^{-1}(A) → K^0(X,A) → K^0(X) → K^0(A).
Here the first two groups are the actual bundle-automorphism presentation and
the boundary is the complement-and-conjugation construction of II.3.21. The
last exactness position already exists as range_relativeKZeroForget and is not
duplicated. These statements precede the loop/Puppe construction, so no suspended
closed-pair exact sequence is used to establish its own foundation.

The five-lemma application II.3.27 assumes separate homotopy equivalences of the
ambient spaces and the subspaces. Their inverses need not form a map of pairs.
It concerns the existing relative group and its actual quotient pullback.
The original boundary exactness positions, pair naturality and this five-lemma
application are proved without assuming a suspended comparison or a pair inverse.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- KA II.3.23: the kernel of the actual boundary is the image of restriction. -/
theorem range_bundleKMinusOneRestriction (A : Set X) (hA : IsClosed A) :
    (bundleKMinusOneRestriction A).range = (bundleKMinusOneBoundary A hA).ker := by
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hid (J : FiniteBundle A) :
      (BundleAutomorphism.identity J).kMinusOneClass = 0 :=
    (BundleAutomorphism.identity J).kMinusOneClass_eq_zero_of_isElementary
      (IsoHomotopy.nonempty_refl (Iso.refl J.Fiber))
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    change bundleKMinusOneBoundary A hA (bundleKMinusOneRestriction A w) = 0
    obtain ⟨b, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective w
    rw [bundleKMinusOneRestriction, bundleKMinusOnePullback_class]
    change bundleKMinusOneBoundary A hA
      (BundleAutomorphism.kMinusOneClass ⟨b.bundle.restrict A, b.automorphism.restrict A⟩) = 0
    rw [bundleKMinusOneBoundary_restricted]
    -- A globally extending automorphism makes its original relative triple elementary.
    have hi : BundleTriple.IsIsomorphic
        (BundleTriple.ofBoundary b.bundle b.bundle (b.automorphism.restrict A))
        (BundleTriple.identity A b.bundle) := by
      refine ⟨Iso.refl b.bundle.Fiber, b.automorphism.symm, ?_⟩
      intro x v
      exact (b.automorphism.linearEquiv x).symm_apply_apply v
    exact (BundleTriple.relativeClass_eq_of_isIsomorphic hA _ _ hi).trans
      (BundleTriple.relativeClass_identity hA b.bundle)
  · intro z hz
    change bundleKMinusOneBoundary A hA z = 0 at hz
    obtain ⟨a, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective z
    rw [bundleKMinusOneBoundary_class] at hz
    let p := idempotentPresentation (E := a.bundle.Fiber)
    let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
    let e : Iso (a.bundle.sum F).Fiber (FiniteBundle.trivial A p.size).Fiber :=
      (nonempty_presentation_complement_iso (E := a.bundle.Fiber)).some
    let T := FiniteBundle.trivial X p.size
    let t := pullbackTrivialIso i p.size
    let B := a.boundaryTriple A hA
    have hzero : B.relativeClass hA = 0 := hz
    -- The original stable zero criterion supplies an actual global extending automorphism.
    obtain ⟨G, u, hu⟩ := (B.relativeClass_eq_zero_iff hA).mp hzero
    let w : BundleAutomorphism X := ⟨T.sum G, u⟩
    let Q := (a.sum (BundleAutomorphism.identity F)).sum
      (BundleAutomorphism.identity (G.restrict A))
    let S : Iso (w.pullback i).bundle.Fiber Q.bundle.Fiber :=
      (restrictSumIso A).trans
        ((t.trans e.symm).sum (Iso.refl (G.restrict A).Fiber))
    have hS (x : A) (v : (Fin p.size → ℂ) × G.Fiber x) :
        S.linearEquiv x v = ((e.linearEquiv x).symm v.1, v.2) := by
      change ((t.trans e.symm).sum (Iso.refl (G.restrict A).Fiber)).linearEquiv x
        ((restrictSumIso A).linearEquiv x v) = _
      rw [restrictSumIso_apply]
      change ((e.linearEquiv x).symm ((pullbackTrivialIso i p.size).linearEquiv x v.1),
        v.2) = _
      rw [pullbackTrivialIso_apply]
    have hB (x : A) (v : Fin p.size → ℂ) :
        B.boundary.linearEquiv x v =
          e.linearEquiv x ((a.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x
            ((e.linearEquiv x).symm v)) := by
      have ht (v : Fin p.size → ℂ) : (t.linearEquiv x).symm v = v := by
        apply (t.linearEquiv x).injective
        rw [LinearEquiv.apply_symm_apply]
        exact (pullbackTrivialIso_apply i p.size x v).symm
      change (t.linearEquiv x).symm
        (e.linearEquiv x ((a.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x
          ((e.linearEquiv x).symm (t.linearEquiv x v)))) = _
      rw [ht, pullbackTrivialIso_apply]
    have hi : (w.pullback i).IsIsomorphic Q := by
      refine ⟨S, ?_⟩
      intro x v
      change (Fin p.size → ℂ) × G.Fiber x at v
      have huv : (u.restrict A).linearEquiv x v =
          (B.boundary.stabilize G.Fiber).linearEquiv x v :=
        congrArg (fun k ↦ k.linearEquiv x v) hu
      change S.linearEquiv x ((u.restrict A).linearEquiv x v) =
        Q.automorphism.linearEquiv x (S.linearEquiv x v)
      rw [huv]
      change S.linearEquiv x ((RelativeTriple.sum B.boundary
        (RelativeTriple.identity G.Fiber A)).linearEquiv x v) = _
      erw [RelativeTriple.sum_apply, hS, hS, hB]
      rw [LinearEquiv.symm_apply_apply]
      rfl
    -- Remove only the two specified identity stabilizations from the restricted class.
    refine ⟨w.kMinusOneClass, ?_⟩
    change bundleKMinusOnePullback i w.kMinusOneClass = a.kMinusOneClass
    rw [bundleKMinusOnePullback_class]
    calc
      _ = Q.kMinusOneClass :=
        BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hi
      _ = a.kMinusOneClass := by
        simp only [Q, BundleAutomorphism.kMinusOneClass_sum, hid, add_zero]

/-- KA II.3.23: the actual automorphism boundary fills the kernel of relative forgetting. -/
theorem range_bundleKMinusOneBoundary (A : Set X) (hA : IsClosed A) :
    (bundleKMinusOneBoundary A hA).range = (relativeKZeroForget A hA).ker := by
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    change relativeKZeroForget A hA (bundleKMinusOneBoundary A hA w) = 0
    obtain ⟨a, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective w
    rw [bundleKMinusOneBoundary_class]
    -- Forgetting retains two identical trivial bundles, so their difference vanishes.
    change relativeKZeroForget A hA ((a.boundaryTriple A hA).relativeClass hA) = 0
    rw [BundleTriple.relativeClass_forget]
    exact sub_self _
  · intro z hz
    change relativeKZeroForget A hA z = 0 at hz
    obtain ⟨t, rfl⟩ := bundleTriple_relativeClass_surjective A hA z
    rw [BundleTriple.relativeClass_forget] at hz
    have hc : t.source.kZeroClass = t.target.kZeroClass := sub_eq_zero.mp hz
    -- A common finite trivial stabilization supplies the actual global comparison.
    obtain ⟨n, ⟨e⟩⟩ := (kZeroClass_eq_iff_stable_iso
      (E := t.source.Fiber) (F := t.target.Fiber)).mp hc
    let G := FiniteBundle.trivial X n
    let S := t.source.sum G
    let β : RelativeTriple S.Fiber S.Fiber A :=
      (t.boundary.stabilize G.Fiber).trans (e.restrict A).symm
    let a : BundleAutomorphism A := ⟨S.restrict A, β⟩
    refine ⟨a.kMinusOneClass, ?_⟩
    change bundleKMinusOneBoundary A hA
      (BundleAutomorphism.kMinusOneClass ⟨S.restrict A, β⟩) = _
    rw [bundleKMinusOneBoundary_restricted]
    have hi : (BundleTriple.ofBoundary S S β).IsIsomorphic
        (t.sum (BundleTriple.identity A G)) := by
      refine ⟨Iso.refl S.Fiber, e, ?_⟩
      intro x v
      change e.linearEquiv x ((e.linearEquiv x).symm
        ((t.boundary.stabilize G.Fiber).linearEquiv x v)) =
          (t.boundary.stabilize G.Fiber).linearEquiv x v
      exact (e.linearEquiv x).apply_symm_apply _
    -- The same global comparison identifies this boundary with the original stabilized triple.
    have heq := BundleTriple.relativeClass_eq_of_isIsomorphic hA _ _ hi
    rw [BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity, add_zero] at heq
    exact heq

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in
/-- The constructed boundary is natural for the specified continuous map of closed pairs. -/
theorem bundleKMinusOneBoundary_natural (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    let fA : C(A, B) :=
      ⟨fun a ↦ ⟨f a, hf a.property⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
    (relativeKZeroPullback A hA B hB f hf).comp (bundleKMinusOneBoundary B hB) =
      (bundleKMinusOneBoundary A hA).comp (bundleKMinusOnePullback fA) := by
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let := hB.isClosedEmbedding_subtypeVal.compactSpace
  let fA : C(A, B) :=
    ⟨fun a ↦ ⟨f a, hf a.property⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  change (relativeKZeroPullback A hA B hB f hf).comp (bundleKMinusOneBoundary B hB) =
    (bundleKMinusOneBoundary A hA).comp (bundleKMinusOnePullback fA)
  -- General pair naturality retains the closed seam even when A is smaller than f⁻¹(B).
  have hrelative (a : BundleTriple B) :
      (BundleTriple.ofBoundary (a.source.pullback f) (a.target.pullback f)
        ((a.boundary.pullback f).restrict hf)).relativeClass hA =
          relativeKZeroPullback A hA B hB f hf (a.relativeClass hB) := by
    let b := BundleTriple.ofBoundary (a.source.pullback f) (a.target.pullback f)
      ((a.boundary.pullback f).restrict hf)
    let := DoubleSpace.t2Space A hA
    let := DoubleSpace.t2Space B hB
    let Wa := clutchingBundle hB a
    let d := DoubleSpace.mapContinuous A B f hf
    let W := Wa.pullback d
    -- Pull the original left and right clutching charts along the same map of doubles.
    let uL : Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ W.Fiber)
        ((f : X → Y) *ᵖ ((DoubleSpace.leftMap B : Y → DoubleSpace B) *ᵖ Wa.Fiber)) :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap A)).trans
        (pullbackCompIso (E := Wa.Fiber) (DoubleSpace.leftMap B) f).symm
    let uR : Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ W.Fiber)
        ((f : X → Y) *ᵖ ((DoubleSpace.rightMap B : Y → DoubleSpace B) *ᵖ Wa.Fiber)) :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap A)).trans
        (pullbackCompIso (E := Wa.Fiber) (DoubleSpace.rightMap B) f).symm
    have huL (x : X) (v : Wa.Fiber (DoubleSpace.left B (f x))) :
        uL.linearEquiv x v = v := by
      change ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.leftMap B) f).linearEquiv x).symm
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap A)).linearEquiv x v) = v
      apply ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.leftMap B) f).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    have huR (x : X) (v : Wa.Fiber (DoubleSpace.right B (f x))) :
        uR.linearEquiv x v = v := by
      change ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.rightMap B) f).linearEquiv x).symm
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap A)).linearEquiv x v) = v
      apply ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.rightMap B) f).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    let eL := uL.trans ((clutchingLeftIso hB a).pullback f)
    let eR := uR.trans ((clutchingRightIso hB a).pullback f)
    have heL (x : X) (v : Wa.Fiber (DoubleSpace.left B (f x))) :
        eL.linearEquiv x v = (clutchingLeftIso hB a).linearEquiv (f x) v := by
      change (clutchingLeftIso hB a).linearEquiv (f x) (uL.linearEquiv x v) = _
      rw [huL]
    have heR (x : X) (v : Wa.Fiber (DoubleSpace.right B (f x))) :
        eR.linearEquiv x v = (clutchingRightIso hB a).linearEquiv (f x) v := by
      change (clutchingRightIso hB a).linearEquiv (f x) (uR.linearEquiv x v) = _
      rw [huR]
    have hinv (x : X) (v : a.source.Fiber (f x)) :
        (eL.linearEquiv x).symm v = ((clutchingLeftIso hB a).linearEquiv (f x)).symm v := by
      apply (eL.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, heL, LinearEquiv.apply_symm_apply]
    have hseam : ClutchingCompatible b W eL eR := by
      intro x v
      change eR.linearEquiv x
        (cast (congrArg W.Fiber (DoubleSpace.left_eq_right A x))
          ((eL.linearEquiv x).symm v)) = ((a.boundary.pullback f).restrict hf).linearEquiv x v
      erw [heR, hinv, Iso.restrictTo_apply, RelativeTriple.pullback_apply]
      exact clutching_seam_apply hB a ⟨f x, hf x.property⟩ v
    obtain ⟨e⟩ := nonempty_clutching_iso hA b W eL eR hseam
    let := W.isFiniteRank
    let := (clutchingBundle hA b).isFiniteRank
    have hglued := kZeroClass_eq_of_iso e.symm
    change (clutchingBundle hA b).kZeroClass = (Wa.pullback d).kZeroClass at hglued
    rw [FiniteBundle.kZeroClass_pullback] at hglued
    -- Projection pullback subtracts the same original target class on both doubles.
    have hcomp : f.comp (DoubleSpace.projMap A) = (DoubleSpace.projMap B).comp d := by
      ext z
      induction z using Quotient.inductionOn with
      | h z => cases z <;> rfl
    have hprojection : complexKZeroPullback (DoubleSpace.projMap A) b.target.kZeroClass =
        complexKZeroPullback d
          (complexKZeroPullback (DoubleSpace.projMap B) a.target.kZeroClass) := by
      change complexKZeroPullback (DoubleSpace.projMap A)
        (a.target.pullback f).kZeroClass = _
      rw [FiniteBundle.kZeroClass_pullback]
      calc
        _ = complexKZeroPullback (f.comp (DoubleSpace.projMap A)) a.target.kZeroClass :=
          (DFunLike.congr_fun (complexKZeroPullback_comp (DoubleSpace.projMap A) f)
            a.target.kZeroClass).symm
        _ = complexKZeroPullback ((DoubleSpace.projMap B).comp d) a.target.kZeroClass := by
          rw [hcomp]
        _ = _ := DFunLike.congr_fun (complexKZeroPullback_comp d (DoubleSpace.projMap B))
          a.target.kZeroClass
    have hdouble : b.doubleDifference hA = complexKZeroPullback d (a.doubleDifference hB) := by
      change (clutchingBundle hA b).kZeroClass -
        complexKZeroPullback (DoubleSpace.projMap A) b.target.kZeroClass =
          complexKZeroPullback d (_ - _)
      rw [map_sub, hglued, hprojection]
    let RA := DoubleSpace.rightRange A
    let RB := DoubleSpace.rightRange B
    have hRA : IsClosed RA := DoubleSpace.isClosed_rightRange A hA
    have hRB : IsClosed RB := DoubleSpace.isClosed_rightRange B hB
    have hd : Set.MapsTo d RA RB := by
      rintro z ⟨x, rfl⟩
      exact ⟨f x, rfl⟩
    let dPull := relativeKZeroPullback RA hRA RB hRB d hd
    -- Uniqueness is applied only on the source double, whose right side is a retract.
    have hlift : b.differenceLift hA = dPull (a.differenceLift hB) := by
      apply relativeKZeroForget_injective_of_retraction RA hRA
        (DoubleSpace.rightRetraction A) (DoubleSpace.rightRetraction_apply A)
      have hn := relativeKZeroForget_natural RA hRA RB hRB d hd
      calc
        _ = b.doubleDifference hA := b.forget_differenceLift hA
        _ = complexKZeroPullback d (a.doubleDifference hB) := hdouble
        _ = complexKZeroPullback d
            (relativeKZeroForget RB hRB (a.differenceLift hB)) := by
          rw [a.forget_differenceLift hB]
        _ = _ := (DFunLike.congr_fun hn (a.differenceLift hB)).symm
    have hrestriction : (DoubleSpace.relativeRestriction A hA).comp dPull =
        (relativeKZeroPullback A hA B hB f hf).comp
          (DoubleSpace.relativeRestriction B hB) := by
      change (relativeKZeroPullback A hA RA hRA (DoubleSpace.leftMap A)
        (DoubleSpace.left_mapsTo A)).comp (relativeKZeroPullback RA hRA RB hRB d hd) =
          (relativeKZeroPullback A hA B hB f hf).comp
            (relativeKZeroPullback B hB RB hRB (DoubleSpace.leftMap B)
              (DoubleSpace.left_mapsTo B))
      have hleft := relativeKZeroPullback_comp A hA RA hRA RB hRB
        (DoubleSpace.leftMap A) d (DoubleSpace.left_mapsTo A) hd
      have hright := relativeKZeroPullback_comp A hA B hB RB hRB
        f (DoubleSpace.leftMap B) hf (DoubleSpace.left_mapsTo B)
      rw [← hleft, ← hright]
      congr 1
    change DoubleSpace.relativeRestriction A hA (b.differenceLift hA) =
      relativeKZeroPullback A hA B hB f hf
        (DoubleSpace.relativeRestriction B hB (a.differenceLift hB))
    rw [hlift]
    exact DFunLike.congr_fun hrestriction (a.differenceLift hB)
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective z
  obtain ⟨n, β, hrep⟩ := a.exists_trivial_representative
  let TY := FiniteBundle.trivial Y n
  let iB : C(B, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let iA : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let tB := pullbackTrivialIso iB n
  let α : RelativeTriple TY.Fiber TY.Fiber B := (tB.trans β).trans tB.symm
  let c : BundleAutomorphism B := ⟨TY.restrict B, α⟩
  have hc : c.kMinusOneClass =
      (⟨FiniteBundle.trivial B n, β⟩ : BundleAutomorphism B).kMinusOneClass := by
    apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
    refine ⟨tB, ?_⟩
    intro x v
    change tB.linearEquiv x ((tB.linearEquiv x).symm
      (β.linearEquiv x (tB.linearEquiv x v))) = β.linearEquiv x (tB.linearEquiv x v)
    exact (tB.linearEquiv x).apply_symm_apply _
  -- The same finite trivial representative is used on both sides of the desired square.
  simp only [AddMonoidHom.comp_apply]
  rw [← hrep, ← hc, bundleKMinusOnePullback_class]
  change relativeKZeroPullback A hA B hB f hf
    (bundleKMinusOneBoundary B hB
      (BundleAutomorphism.kMinusOneClass ⟨TY.restrict B, α⟩)) =
        bundleKMinusOneBoundary A hA (c.pullback fA).kMinusOneClass
  rw [bundleKMinusOneBoundary_restricted]
  rw [← hrelative (BundleTriple.ofBoundary TY TY α)]
  let E := TY.pullback f
  let γ : RelativeTriple E.Fiber E.Fiber A := (α.pullback f).restrict hf
  let S : Iso (c.pullback fA).bundle.Fiber (E.restrict A).Fiber :=
    (pullbackCompIso (E := TY.Fiber) iB fA).trans
      (pullbackCompIso (E := TY.Fiber) f iA).symm
  have hS (x : A) (v : Fin n → ℂ) : S.linearEquiv x v = v := by
    change ((pullbackCompIso (E := TY.Fiber) f iA).linearEquiv x).symm
      ((pullbackCompIso (E := TY.Fiber) iB fA).linearEquiv x v) = v
    apply ((pullbackCompIso (E := TY.Fiber) f iA).linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hi : (c.pullback fA).IsIsomorphic ⟨E.restrict A, γ⟩ := by
    refine ⟨S, ?_⟩
    intro x v
    change Fin n → ℂ at v
    change S.linearEquiv x (α.linearEquiv (fA x) v) =
      γ.linearEquiv x (S.linearEquiv x v)
    erw [hS, hS]
    exact ((Iso.restrictTo_apply (α.pullback f) hf x v).trans
      (RelativeTriple.pullback_apply α f ⟨x, hf x.property⟩ v)).symm
  -- The comparison fixes each vector and hence intertwines the specified boundary action.
  rw [BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hi,
    bundleKMinusOneBoundary_restricted]

/-- KA II.3.27: separate ambient and subspace homotopy equivalences suffice. -/
theorem relativeKZeroPullback_bijective_of_homotopyEquiv
    (A : Set X) (hA : IsClosed A) (B : Set Y) (hB : IsClosed B)
    (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (he : ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f)
    (heA : ∃ eA : ContinuousMap.HomotopyEquiv A B,
      ∀ a : A, (eA a : Y) = f a) :
    Function.Bijective (relativeKZeroPullback A hA B hB f hf) := by
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let := hB.isClosedEmbedding_subtypeVal.compactSpace
  let fA : C(A, B) :=
    ⟨fun a ↦ ⟨f a, hf a.property⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let iA : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iB : C(B, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  -- Absolute homotopy invariance supplies inverse pullbacks without a pair inverse.
  have hK {U : Type _} {V : Type _} [TopologicalSpace U] [TopologicalSpace V]
      [CompactSpace U] [T2Space U] [CompactSpace V] [T2Space V]
      (e : ContinuousMap.HomotopyEquiv U V) :
      Function.Bijective (complexKZeroPullback e.toFun) := by
    let u := complexKZeroPullback e.toFun
    let v := complexKZeroPullback e.invFun
    have hleft : v.comp u = AddMonoidHom.id (ComplexKZero V) := by
      change (complexKZeroPullback e.invFun).comp (complexKZeroPullback e.toFun) = _
      rw [← complexKZeroPullback_comp]
      obtain ⟨H⟩ := e.right_inv
      rw [complexKZeroPullback_eq_of_homotopy _ _ H]
      exact kZeroMap_id
    have hright : u.comp v = AddMonoidHom.id (ComplexKZero U) := by
      change (complexKZeroPullback e.toFun).comp (complexKZeroPullback e.invFun) = _
      rw [← complexKZeroPullback_comp]
      obtain ⟨H⟩ := e.left_inv
      rw [complexKZeroPullback_eq_of_homotopy _ _ H]
      exact kZeroMap_id
    exact ⟨(show Function.LeftInverse v u from
        fun z ↦ DFunLike.congr_fun hleft z).injective,
      (show Function.RightInverse v u from
        fun z ↦ DFunLike.congr_fun hright z).surjective⟩
  obtain ⟨e, he⟩ := he
  obtain ⟨eA, heA⟩ := heA
  have heA' : eA.toFun = fA := by
    apply ContinuousMap.ext
    intro a
    exact Subtype.ext (heA a)
  have h₁ : Function.Bijective (bundleKMinusOnePullback f) := by
    rw [← he]
    exact bundleKMinusOnePullback_bijective_of_homotopyEquiv e
  have h₂ : Function.Bijective (bundleKMinusOnePullback fA) := by
    rw [← heA']
    exact bundleKMinusOnePullback_bijective_of_homotopyEquiv eA
  have h₄ : Function.Bijective (complexKZeroPullback f) := by
    rw [← he]
    exact hK e
  have h₅ : Function.Bijective (complexKZeroPullback fA) := by
    rw [← heA']
    exact hK eA
  -- The four squares retain the original f and its actual subspace restriction.
  have hc₁ : (bundleKMinusOneRestriction A).comp (bundleKMinusOnePullback f) =
      (bundleKMinusOnePullback fA).comp (bundleKMinusOneRestriction B) := by
    change (bundleKMinusOnePullback iA).comp (bundleKMinusOnePullback f) =
      (bundleKMinusOnePullback fA).comp (bundleKMinusOnePullback iB)
    rw [← bundleKMinusOnePullback_comp, ← bundleKMinusOnePullback_comp]
    rfl
  have hc₄ : (complexKZeroRestriction A hA).comp (complexKZeroPullback f) =
      (complexKZeroPullback fA).comp (complexKZeroRestriction B hB) := by
    change (complexKZeroPullback iA).comp (complexKZeroPullback f) =
      (complexKZeroPullback fA).comp (complexKZeroPullback iB)
    rw [← complexKZeroPullback_comp, ← complexKZeroPullback_comp]
    rfl
  -- Both rows are the established five-term sequence, rather than a suspended substitute.
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (bundleKMinusOneRestriction B) (bundleKMinusOneBoundary B hB)
    (relativeKZeroForget B hB) (complexKZeroRestriction B hB)
    (bundleKMinusOneRestriction A) (bundleKMinusOneBoundary A hA)
    (relativeKZeroForget A hA) (complexKZeroRestriction A hA)
    (bundleKMinusOnePullback f) (bundleKMinusOnePullback fA)
    (relativeKZeroPullback A hA B hB f hf) (complexKZeroPullback f)
    (complexKZeroPullback fA) hc₁ (bundleKMinusOneBoundary_natural A hA B hB f hf).symm
    (relativeKZeroForget_natural A hA B hB f hf) hc₄
    (AddMonoidHom.exact_iff.mpr (range_bundleKMinusOneRestriction B hB).symm)
    (AddMonoidHom.exact_iff.mpr (range_bundleKMinusOneBoundary B hB).symm)
    (AddMonoidHom.exact_iff.mpr (range_relativeKZeroForget B hB).symm)
    (AddMonoidHom.exact_iff.mpr (range_bundleKMinusOneRestriction A hA).symm)
    (AddMonoidHom.exact_iff.mpr (range_bundleKMinusOneBoundary A hA).symm)
    (AddMonoidHom.exact_iff.mpr (range_relativeKZeroForget A hA).symm)
    h₁.surjective h₂ h₄ h₅.injective

/-- The equivalence induced by that same relative pullback, with no replacement map. -/
def relativeKZeroEquivOfHomotopyEquiv
    (A : Set X) (hA : IsClosed A) (B : Set Y) (hB : IsClosed B)
    (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (he : ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f)
    (heA : ∃ eA : ContinuousMap.HomotopyEquiv A B,
      ∀ a : A, (eA a : Y) = f a) : RelativeKZero B hB ≃+ RelativeKZero A hA :=
  AddEquiv.ofBijective (relativeKZeroPullback A hA B hB f hf)
    (relativeKZeroPullback_bijective_of_homotopyEquiv A hA B hB f hf he heA)

end AtiyahSinger.ComplexBundle

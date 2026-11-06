/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleKZero
public import AtiyahSinger.Topology.SupportWindow
public import AtiyahSinger.Topology.TripleKZeroComparison

/-!
# The actual compact-support difference class

Public module ID: M2185.

D07/K02. Restrict to a compact neighborhood, form its boundary-relative difference
class, identify the open complement with the ambient interior, and extend openly.
Independence of the window is stated before making a choice. Neither original
bundle is assumed to extend to the one-point compactification.
Sources: SG I.9.25–9.26; KA II.4.1–4.3. Localization details are project supplements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle OnePoint
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X] [hLX : LocallyCompactSpace X] [hTX : T2Space X]

include hLX hTX

attribute [local instance] sumTopology isFiniteRank_sum

set_option backward.isDefEq.respectTransparency false


/-- Form the relative difference on a compact window and extend its interior class. -/
def SupportBundleTriple.windowClass (a : SupportBundleTriple X) (L : Set X)
    (hL : IsCompact L) (h : a.datum.control ⊆ interior L) : CompactSupportKZero X :=
  letI := isCompact_iff_compactSpace.mp hL
  letI := (isClosed_supportWindowBoundary L).isOpen_compl.locallyCompactSpace
  letI := (isOpen_interior (s := L)).locallyCompactSpace
  compactSupportKZeroOpenExtension (interior L) isOpen_interior
    (compactSupportKZeroHomeomorph (supportWindowInteriorHomeomorph L)
      (relativeKZeroToCompactSupport.{_, 0} (supportWindowBoundary L)
        (isClosed_supportWindowBoundary L)
        ((a.windowTriple L h).relativeClass (isClosed_supportWindowBoundary L))))

set_option maxHeartbeats 4000000 in

set_option backward.isDefEq.respectTransparency false in
/-- Nested compact windows give the same extended difference class. -/
theorem SupportBundleTriple.windowClass_eq_of_subset (a : SupportBundleTriple X)
    (L M : Set X) (hL : IsCompact L) (hM : IsCompact M)
    (haL : a.datum.control ⊆ interior L) (haM : a.datum.control ⊆ interior M)
    (hLM : L ⊆ M) : a.windowClass L hL haL = a.windowClass M hM haM := by
  classical
  let := isCompact_iff_compactSpace.mp hL
  let := isCompact_iff_compactSpace.mp hM
  -- Restrict the original clutching class to a smaller closed boundary.
  have changePair {A B : Set M} (hA : IsClosed A) (hB : IsClosed B) (hBA : B ⊆ A)
      (a : BundleTriple A) :
      (BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)).relativeClass hB =
        relativeKZeroEnlarge B A hB hA hBA (a.relativeClass hA) := by
    let b := BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)
    let := DoubleSpace.t2Space A hA
    let := DoubleSpace.t2Space B hB
    let Wa := clutchingBundle hA a
    let d := DoubleSpace.mapContinuous B A (ContinuousMap.id M) hBA
    let W := Wa.pullback d
    -- The two original charts pull back along the identity on each copy of M.
    let eL : Iso ((DoubleSpace.leftMap B : M → DoubleSpace B) *ᵖ W.Fiber) a.source.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).trans
        (clutchingLeftIso hA a)
    let eR : Iso ((DoubleSpace.rightMap B : M → DoubleSpace B) *ᵖ W.Fiber) a.target.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).trans
        (clutchingRightIso hA a)
    have heL (x : M) (v : Wa.Fiber (DoubleSpace.left A x)) :
        eL.linearEquiv x v = (clutchingLeftIso hA a).linearEquiv x v := by
      change (clutchingLeftIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have heR (x : M) (v : Wa.Fiber (DoubleSpace.right A x)) :
        eR.linearEquiv x v = (clutchingRightIso hA a).linearEquiv x v := by
      change (clutchingRightIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have hinv (x : M) (v : a.source.Fiber x) :
        (eL.linearEquiv x).symm v = ((clutchingLeftIso hA a).linearEquiv x).symm v := by
      apply (eL.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, heL, LinearEquiv.apply_symm_apply]
    have hseam : ClutchingCompatible b W eL eR := by
      intro x v
      change eR.linearEquiv x
        (cast (congrArg W.Fiber (DoubleSpace.left_eq_right B x))
          ((eL.linearEquiv x).symm v)) = (a.boundary.restrict hBA).linearEquiv x v
      rw [heR, hinv]
      exact (clutching_seam_apply hA a ⟨x, hBA x.property⟩ v).trans
        (Iso.restrictTo_apply a.boundary hBA x v).symm
    obtain ⟨e⟩ := nonempty_clutching_iso hB b W eL eR hseam
    let := W.isFiniteRank
    let := (clutchingBundle hB b).isFiniteRank
    have hglued := kZeroClass_eq_of_iso e.symm
    change (clutchingBundle hB b).kZeroClass = (Wa.pullback d).kZeroClass at hglued
    rw [FiniteBundle.kZeroClass_pullback] at hglued
    -- Both sides subtract the pullback of the same target bundle along projection.
    have hproj : (DoubleSpace.projMap A).comp d = DoubleSpace.projMap B := by
      ext z
      induction z using Quotient.inductionOn with
      | h z => cases z <;> rfl
    have hprojection : complexKZeroPullback (DoubleSpace.projMap B) a.target.kZeroClass =
        complexKZeroPullback d
          (complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass) := by
      have h := DFunLike.congr_fun
        (complexKZeroPullback_comp d (DoubleSpace.projMap A)) a.target.kZeroClass
      rw [hproj] at h
      exact h
    have hdouble : b.doubleDifference hB = complexKZeroPullback d (a.doubleDifference hA) := by
      change (clutchingBundle hB b).kZeroClass -
        complexKZeroPullback (DoubleSpace.projMap B) a.target.kZeroClass =
          complexKZeroPullback d
            (Wa.kZeroClass - complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass)
      rw [map_sub, hglued, hprojection]
    let RA := DoubleSpace.rightRange A
    let RB := DoubleSpace.rightRange B
    have hRA : IsClosed RA := DoubleSpace.isClosed_rightRange A hA
    have hRB : IsClosed RB := DoubleSpace.isClosed_rightRange B hB
    have hd : Set.MapsTo d RB RA := by
      rintro z ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    let dPull := relativeKZeroPullback RB hRB RA hRA d hd
    -- Forgetting is used injectively only on the retracting source double.
    have hlift : b.differenceLift hB = dPull (a.differenceLift hA) := by
      apply relativeKZeroForget_injective_of_retraction RB hRB
        (DoubleSpace.rightRetraction B) (DoubleSpace.rightRetraction_apply B)
      have hn := relativeKZeroForget_natural RB hRB RA hRA d hd
      calc
        _ = b.doubleDifference hB := b.forget_differenceLift hB
        _ = complexKZeroPullback d (a.doubleDifference hA) := hdouble
        _ = complexKZeroPullback d
            (relativeKZeroForget RA hRA (a.differenceLift hA)) := by
          rw [a.forget_differenceLift hA]
        _ = _ := (DFunLike.congr_fun hn (a.differenceLift hA)).symm
    have hrestriction : (DoubleSpace.relativeRestriction B hB).comp dPull =
        (relativeKZeroEnlarge B A hB hA hBA).comp
          (DoubleSpace.relativeRestriction A hA) := by
      change (relativeKZeroPullback B hB RB hRB (DoubleSpace.leftMap B)
        (DoubleSpace.left_mapsTo B)).comp (relativeKZeroPullback RB hRB RA hRA d hd) =
          (relativeKZeroPullback B hB A hA (ContinuousMap.id M) hBA).comp
            (relativeKZeroPullback A hA RA hRA (DoubleSpace.leftMap A)
              (DoubleSpace.left_mapsTo A))
      have hleft := relativeKZeroPullback_comp B hB RB hRB RA hRA
        (DoubleSpace.leftMap B) d (DoubleSpace.left_mapsTo B) hd
      have hright := relativeKZeroPullback_comp B hB A hA RA hRA
        (ContinuousMap.id M) (DoubleSpace.leftMap A) hBA (DoubleSpace.left_mapsTo A)
      rw [← hleft, ← hright]
      congr 1
    change DoubleSpace.relativeRestriction B hB (b.differenceLift hB) =
      relativeKZeroEnlarge B A hB hA hBA
        (DoubleSpace.relativeRestriction A hA (a.differenceLift hA))
    rw [hlift]
    exact DFunLike.congr_fun hrestriction (a.differenceLift hA)
  -- The larger relative subspace remembers the exact original exterior action.
  let C : Set M := {x | (x : X) ∉ interior L}
  have hC : IsClosed C := isOpen_interior.isClosed_compl.preimage continuous_subtype_val
  let p : C(M, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcontrol : C ⊆ p ⁻¹' a.datum.controlᶜ := by
    intro x hx hxK
    exact hx (haL hxK)
  let b : BundleTriple C := BundleTriple.ofBoundary (a.source.restrict M) (a.target.restrict M)
    ((a.datum.boundary.pullback p).restrict hcontrol)
  have hb (x : C) (v : a.source.Fiber x.val.val) :
      b.boundary.linearEquiv x v =
        a.datum.boundary.linearEquiv ⟨x.val.val, hcontrol x.property⟩ v := by
    exact (Iso.restrictTo_apply (a.datum.boundary.pullback p) hcontrol x v).trans
      (RelativeTriple.pullback_apply a.datum.boundary p
        ⟨x.val, hcontrol x.property⟩ v)
  let d : RelativeKZero.{_, 0} C hC := b.relativeClass hC
  let i : C(L, M) := ⟨Set.inclusion hLM, continuous_inclusion hLM⟩
  let sL := relativeKZeroPullback (supportWindowBoundary L)
    (isClosed_supportWindowBoundary L) C hC i (fun _ hx ↦ hx)
  have hLi : (b.pullback i).IsIsomorphic (a.windowTriple L haL) := by
    refine ⟨restrictSubsetIso (E := a.source.Fiber) M L hLM,
      restrictSubsetIso (E := a.target.Fiber) M L hLM, ?_⟩
    intro x v
    change (restrictSubsetIso (E := a.target.Fiber) M L hLM).linearEquiv x
      ((b.boundary.pullback i).linearEquiv x v) =
        (a.windowBoundary L haL).linearEquiv x
          ((restrictSubsetIso (E := a.source.Fiber) M L hLM).linearEquiv x v)
    rw [restrictSubsetIso_apply, restrictSubsetIso_apply, RelativeTriple.pullback_apply]
    exact (hb ⟨i x, x.property⟩ v).trans (a.windowBoundary_apply L haL x v).symm
  have hLclass : (a.windowTriple L haL).relativeClass (isClosed_supportWindowBoundary L) =
      sL d := by
    exact (BundleTriple.relativeClass_eq_of_isIsomorphic
      (isClosed_supportWindowBoundary L) (b.pullback i) (a.windowTriple L haL) hLi).symm.trans
        (b.relativeClass_pullback hC i)
  have hMC : supportWindowBoundary M ⊆ C := by
    intro x hx hxL
    exact hx (interior_mono hLM hxL)
  let sM := relativeKZeroEnlarge (supportWindowBoundary M) C
    (isClosed_supportWindowBoundary M) hC hMC
  have hMi : (BundleTriple.ofBoundary b.source b.target (b.boundary.restrict hMC)).IsIsomorphic
      (a.windowTriple M haM) := by
    refine ⟨Iso.refl _, Iso.refl _, ?_⟩
    intro x v
    change (b.boundary.restrict hMC).linearEquiv x v =
      (a.windowBoundary M haM).linearEquiv x v
    exact (Iso.restrictTo_apply b.boundary hMC x v).trans
      ((hb ⟨x.val, hMC x.property⟩ v).trans (a.windowBoundary_apply M haM x v).symm)
  have hMclass : (a.windowTriple M haM).relativeClass (isClosed_supportWindowBoundary M) =
      sM d := by
    exact (BundleTriple.relativeClass_eq_of_isIsomorphic
      (isClosed_supportWindowBoundary M) _ _ hMi).symm.trans
        (changePair hC (isClosed_supportWindowBoundary M) hMC b)
  -- Each window class is pullback along its specified collapse to its boundary quotient.
  let wMap (N : Set X) (hN : IsCompact N) :
      C(OnePoint X, PointedQuotient.{_, 0} (supportWindowBoundary N)) :=
    let := isCompact_iff_compactSpace.mp hN
    let := (isClosed_supportWindowBoundary N).isOpen_compl.locallyCompactSpace
    let := (isOpen_interior (s := N)).locallyCompactSpace
    let e := supportWindowInteriorHomeomorph N
    let q := PointedQuotient.onePointHomeomorph.{_, 0}
      (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
    (⟨q.symm, q.symm.continuous⟩ : C(_, _)).comp
      ((properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap).comp
        ⟨onePointCollapse (interior N), continuous_onePointCollapse (interior N) isOpen_interior⟩)
  have hmapInfinity (N : Set X) (hN : IsCompact N) :
      wMap N hN ∞ = PointedQuotient.basepoint (supportWindowBoundary N) := by
    let := isCompact_iff_compactSpace.mp hN
    exact PointedQuotient.onePointHomeomorph_symm_infty
      (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
  have hmapMem (N : Set X) (hN : IsCompact N) (x : X) (hx : x ∈ interior N) :
      wMap N hN (x : OnePoint X) =
        PointedQuotient.of (supportWindowBoundary N) ⟨x, interior_subset hx⟩ := by
    let := isCompact_iff_compactSpace.mp hN
    let e := supportWindowInteriorHomeomorph N
    let q := PointedQuotient.onePointHomeomorph.{_, 0}
      (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
    change q.symm (OnePoint.map e.symm (onePointCollapse (interior N) (x : OnePoint X))) = _
    rw [onePointCollapse_coe_of_mem (interior N) x hx]
    exact q.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of (supportWindowBoundary N)
        (isClosed_supportWindowBoundary N) (e.symm ⟨x, hx⟩)).symm
  have hmapNotMem (N : Set X) (hN : IsCompact N) (x : X) (hx : x ∉ interior N) :
      wMap N hN (x : OnePoint X) = PointedQuotient.basepoint (supportWindowBoundary N) := by
    let := isCompact_iff_compactSpace.mp hN
    let e := supportWindowInteriorHomeomorph N
    let q := PointedQuotient.onePointHomeomorph.{_, 0}
      (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
    change q.symm (OnePoint.map e.symm (onePointCollapse (interior N) (x : OnePoint X))) = _
    rw [onePointCollapse_coe_of_notMem (interior N) x hx]
    exact PointedQuotient.onePointHomeomorph_symm_infty
      (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
  have hwindow (N : Set X) [CompactSpace N] (hN : IsCompact N)
      (haN : a.datum.control ⊆ interior N) :
      let := PointedQuotient.t2Space (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
      (a.windowClass N hN haN).val = complexKZeroPullback (wMap N hN)
        ((a.windowTriple N haN).relativeClass (isClosed_supportWindowBoundary N)).val := by
    let := isCompact_iff_compactSpace.mp hN
    let := PointedQuotient.t2Space (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
    let := (isClosed_supportWindowBoundary N).isOpen_compl.locallyCompactSpace
    let := (isOpen_interior (s := N)).locallyCompactSpace
    let e := supportWindowInteriorHomeomorph N
    let q := PointedQuotient.onePointHomeomorph.{_, 0}
      (supportWindowBoundary N) (isClosed_supportWindowBoundary N)
    change complexKZeroPullback
      ⟨onePointCollapse (interior N), continuous_onePointCollapse (interior N) isOpen_interior⟩
      (complexKZeroPullback
        (properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap)
        (complexKZeroPullback ⟨q.symm, q.symm.continuous⟩ _)) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  let uL := PointedQuotient.mapContinuous (supportWindowBoundary L) C i (fun _ hx ↦ hx)
  let uM := PointedQuotient.mapContinuous (supportWindowBoundary M) C (ContinuousMap.id M) hMC
  have hsquare : uL.comp (wMap L hL) = uM.comp (wMap M hM) := by
    ext z
    cases z using OnePoint.rec with
    | infty =>
      change uL (wMap L hL ∞) = uM (wMap M hM ∞)
      rw [hmapInfinity L hL, hmapInfinity M hM]
      rfl
    | coe x =>
      change uL (wMap L hL (x : OnePoint X)) = uM (wMap M hM (x : OnePoint X))
      by_cases hxL : x ∈ interior L
      · rw [hmapMem L hL x hxL, hmapMem M hM x (interior_mono hLM hxL)]
        rfl
      · rw [hmapNotMem L hL x hxL]
        by_cases hxM : x ∈ interior M
        · rw [hmapMem M hM x hxM]
          exact ((PointedQuotient.of_eq_basepoint_iff C ⟨x, interior_subset hxM⟩).2 hxL).symm
        · rw [hmapNotMem M hM x hxM]
          rfl
  -- Pull back the same relative class along that equality of actual pointed maps.
  let := PointedQuotient.t2Space (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
  let := PointedQuotient.t2Space (supportWindowBoundary M) (isClosed_supportWindowBoundary M)
  let := PointedQuotient.t2Space C hC
  apply Subtype.ext
  rw [hwindow L hL haL, hwindow M hM haM, hLclass, hMclass]
  change complexKZeroPullback (wMap L hL) (complexKZeroPullback uL d.val) =
    complexKZeroPullback (wMap M hM) (complexKZeroPullback uM d.val)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]

/-- The compact-support difference is independent of every compact window choice. -/
theorem SupportBundleTriple.windowClass_eq (a : SupportBundleTriple X)
    (L M : Set X) (hL : IsCompact L) (hM : IsCompact M)
    (haL : a.datum.control ⊆ interior L) (haM : a.datum.control ⊆ interior M) :
    a.windowClass L hL haL = a.windowClass M hM haM := by
  -- Both original windows lie in the same compact union.
  have haU : a.datum.control ⊆ interior (L ∪ M) :=
    haL.trans (interior_mono Set.subset_union_left)
  exact (a.windowClass_eq_of_subset L (L ∪ M) hL (hL.union hM) haL haU
    Set.subset_union_left).trans
      (a.windowClass_eq_of_subset M (L ∪ M) hM (hL.union hM) haM haU
        Set.subset_union_right).symm

/-- Choose a compact window only after establishing its independence. -/
def SupportBundleTriple.compactSupportClass (a : SupportBundleTriple X) : CompactSupportKZero X :=
  a.windowClass (supportNeighborhood a.datum.control a.datum.isCompact_control)
    (isCompact_supportNeighborhood a.datum.control a.datum.isCompact_control)
    (subset_interior_supportNeighborhood a.datum.control a.datum.isCompact_control)

/-- Every admissible compact window computes the chosen class. -/
theorem SupportBundleTriple.compactSupportClass_eq_windowClass (a : SupportBundleTriple X)
    (L : Set X) (hL : IsCompact L) (h : a.datum.control ⊆ interior L) :
    a.compactSupportClass = a.windowClass L hL h := by
  -- Compare with the exact neighborhood chosen by the original definition.
  exact a.windowClass_eq _ L
    (isCompact_supportNeighborhood a.datum.control a.datum.isCompact_control) hL
    (subset_interior_supportNeighborhood a.datum.control a.datum.isCompact_control) h

/-- Enlarging compact control preserves the actual constructed K class. -/
theorem SupportBundleTriple.compactSupportClass_enlarge (a : SupportBundleTriple X)
    (K : Set X) (hK : IsCompact K) (h : a.datum.control ⊆ K) :
    (a.enlarge K hK h).compactSupportClass = a.compactSupportClass := by
  let L := supportNeighborhood K hK
  have hL : IsCompact L := isCompact_supportNeighborhood K hK
  have hKL : K ⊆ interior L := subset_interior_supportNeighborhood K hK
  -- Keep one window, both restricted bundles and the same exterior action.
  rw [(a.enlarge K hK h).compactSupportClass_eq_windowClass L hL hKL,
    a.compactSupportClass_eq_windowClass L hL (h.trans hKL)]
  let := isCompact_iff_compactSpace.mp hL
  unfold SupportBundleTriple.windowClass
  rw [BundleTriple.relativeClass_eq_of_isIsomorphic
    (isClosed_supportWindowBoundary L) _ _ (a.windowTriple_enlarge K hK h L hKL)]

/-- Isomorphism of germs preserves the constructed compact-support class. -/
theorem SupportBundleTriple.compactSupportClass_eq_of_isIsomorphic (a b : SupportBundleTriple X)
    (h : a.IsIsomorphic b) : a.compactSupportClass = b.compactSupportClass := by
  obtain ⟨K, hK, ha, hb, u, w, huw⟩ := h
  let L := supportNeighborhood K hK
  have hL : IsCompact L := isCompact_supportNeighborhood K hK
  have hKL : K ⊆ interior L := subset_interior_supportNeighborhood K hK
  let := isCompact_iff_compactSpace.mp hL
  -- Restrict the original global square, retaining its common exterior control.
  have hwindow : (a.windowTriple L (ha.trans hKL)).IsIsomorphic
      (b.windowTriple L (hb.trans hKL)) := by
    refine ⟨u.restrict L, w.restrict L, ?_⟩
    intro x v
    let y : (Kᶜ : Set X) :=
      ⟨x.val.val, fun hy ↦ x.property (hKL hy)⟩
    have hs := huw y v
    have heA := a.datum.enlarge_apply K hK ha y v
    have heB := b.datum.enlarge_apply K hK hb y (u.linearEquiv x.val.val v)
    change w.linearEquiv x.val.val ((a.windowBoundary L (ha.trans hKL)).linearEquiv x v) =
      (b.windowBoundary L (hb.trans hKL)).linearEquiv x (u.linearEquiv x.val.val v)
    exact (congrArg (w.linearEquiv x.val.val)
      ((a.windowBoundary_apply L (ha.trans hKL) x v).trans heA.symm)).trans
        (hs.trans (heB.trans
          (b.windowBoundary_apply L (hb.trans hKL) x (u.linearEquiv x.val.val v)).symm))
  -- Apply relative invariance before the same three extension homomorphisms.
  rw [a.compactSupportClass_eq_windowClass L hL (ha.trans hKL),
    b.compactSupportClass_eq_windowClass L hL (hb.trans hKL)]
  unfold SupportBundleTriple.windowClass
  rw [BundleTriple.relativeClass_eq_of_isIsomorphic
    (isClosed_supportWindowBoundary L) _ _ hwindow]

/-- The compact-support class is additive for direct sum. -/
theorem SupportBundleTriple.compactSupportClass_sum (a b : SupportBundleTriple X) :
    (a.sum b).compactSupportClass = a.compactSupportClass + b.compactSupportClass := by
  let K := a.datum.control ∪ b.datum.control
  have hK : IsCompact K := a.datum.isCompact_control.union b.datum.isCompact_control
  let L := supportNeighborhood K hK
  have hL : IsCompact L := isCompact_supportNeighborhood K hK
  have h : K ⊆ interior L := subset_interior_supportNeighborhood K hK
  let := isCompact_iff_compactSpace.mp hL
  -- The canonical restriction/sum square compares the actual window triples.
  rw [(a.sum b).compactSupportClass_eq_windowClass L hL h,
    a.compactSupportClass_eq_windowClass L hL (Set.subset_union_left.trans h),
    b.compactSupportClass_eq_windowClass L hL (Set.subset_union_right.trans h)]
  unfold SupportBundleTriple.windowClass
  rw [BundleTriple.relativeClass_eq_of_isIsomorphic
    (isClosed_supportWindowBoundary L) _ _ (a.windowTriple_sum b L h),
    BundleTriple.relativeClass_sum, map_add, map_add, map_add]

/-- An identity triple has zero compact-support class. -/
theorem SupportBundleTriple.compactSupportClass_identity (E : FiniteBundle X) :
    (SupportBundleTriple.identity E).compactSupportClass = 0 := by
  let L := supportNeighborhood (∅ : Set X) isCompact_empty
  have hL : IsCompact L := isCompact_supportNeighborhood (∅ : Set X) isCompact_empty
  let := isCompact_iff_compactSpace.mp hL
  -- The original global identity remains the identity on this actual boundary.
  rw [(SupportBundleTriple.identity E).compactSupportClass_eq_windowClass L hL
    (Set.empty_subset _)]
  unfold SupportBundleTriple.windowClass
  rw [BundleTriple.relativeClass_eq_of_isIsomorphic
    (isClosed_supportWindowBoundary L) _ _ (supportBundleTriple_windowTriple_identity E L),
    BundleTriple.relativeClass_identity, map_zero, map_zero, map_zero]

/-- Stable isomorphism preserves the constructed class. -/
theorem SupportBundleTriple.compactSupportClass_eq_of_isStablyIsomorphic
    (a b : SupportBundleTriple X) (h : a.IsStablyIsomorphic b) :
    a.compactSupportClass = b.compactSupportClass := by
  obtain ⟨E, F, h⟩ := h
  -- Use exactly the two identity stabilizations supplied by the witness.
  have hs := SupportBundleTriple.compactSupportClass_eq_of_isIsomorphic _ _ h
  simpa only [SupportBundleTriple.compactSupportClass_sum,
    SupportBundleTriple.compactSupportClass_identity, add_zero] using hs

/-- Reversing the boundary isomorphism negates the constructed class. -/
theorem SupportBundleTriple.compactSupportClass_inverse (a : SupportBundleTriple X) :
    a.inverse.compactSupportClass = -a.compactSupportClass := by
  -- The original cutoff isomorphism identifies this sum with its identity triple.
  have hz := SupportBundleTriple.compactSupportClass_eq_of_isIsomorphic _ _
    a.isIsomorphic_sum_inverse
  rw [SupportBundleTriple.compactSupportClass_sum,
    SupportBundleTriple.compactSupportClass_identity] at hz
  exact eq_neg_of_add_eq_zero_right hz

/-- Uniform boundary homotopy preserves the constructed compact-support class. -/
theorem supportBundleTriple_compactSupportClass_eq_of_homotopic (E F : FiniteBundle X)
    (a b : CompactSupportTriple E.Fiber F.Fiber) (H : a.Homotopic b) :
    (SupportBundleTriple.ofBoundary E F a).compactSupportClass =
      (SupportBundleTriple.ofBoundary E F b).compactSupportClass := by
  -- Spatial cutoff uses the same uniform control and the original endpoint maps.
  exact SupportBundleTriple.compactSupportClass_eq_of_isIsomorphic _ _
    (supportBundleTriple_isIsomorphic_of_homotopic E F a b H)

/-- Composition of boundary isomorphisms adds the constructed support classes. -/
theorem supportBundleTriple_compactSupportClass_compose (E F G : FiniteBundle X)
    (a : CompactSupportTriple E.Fiber F.Fiber) (b : CompactSupportTriple F.Fiber G.Fiber) :
    (SupportBundleTriple.ofBoundary E G (a.compose b)).compactSupportClass =
      (SupportBundleTriple.ofBoundary E F a).compactSupportClass +
        (SupportBundleTriple.ofBoundary F G b).compactSupportClass := by
  -- The original composition square supplies the identity on the middle bundle F.
  have hs := SupportBundleTriple.compactSupportClass_eq_of_isIsomorphic _ _
    (supportBundleTriple_isIsomorphic_sum_compose E F G a b)
  rw [SupportBundleTriple.compactSupportClass_sum,
    SupportBundleTriple.compactSupportClass_sum,
    SupportBundleTriple.compactSupportClass_identity, add_zero] at hs
  exact hs.symm

/-- Every globally invertible triple has zero compact-support class. -/
theorem supportBundleTriple_compactSupportClass_ofIso (E F : FiniteBundle X)
    (e : Iso E.Fiber F.Fiber) :
    (SupportBundleTriple.ofBoundary E F (CompactSupportTriple.ofIso e)).compactSupportClass =
      0 := by
  -- The source identity and the specified global e give the exact boundary square.
  have hi : (SupportBundleTriple.identity E).IsIsomorphic
      (SupportBundleTriple.ofBoundary E F (CompactSupportTriple.ofIso e)) := by
    refine ⟨∅, isCompact_empty, Set.empty_subset _, Set.empty_subset _,
      Iso.refl _, e, ?_⟩
    intro x v
    simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
    rfl
  exact (SupportBundleTriple.compactSupportClass_eq_of_isIsomorphic _ _ hi).symm.trans
    (SupportBundleTriple.compactSupportClass_identity E)

/-- A zero relative difference on a window gives a zero extended class. -/
theorem SupportBundleTriple.windowClass_eq_zero (a : SupportBundleTriple X)
    (L : Set X) (hL : IsCompact L) (h : a.datum.control ⊆ interior L)
    (hz : letI := isCompact_iff_compactSpace.mp hL
      (a.windowTriple L h).relativeClass (isClosed_supportWindowBoundary L) = 0) :
    a.windowClass L hL h = 0 := by
  let := isCompact_iff_compactSpace.mp hL
  -- The original hypothesis permits any auxiliary quotient universe.
  -- The extension criterion transfers its vanishing to the small quotient used by windowClass.
  have hsmall : BundleTriple.relativeClass.{_, 0}
      (isClosed_supportWindowBoundary L) (a.windowTriple L h) = 0 :=
    (BundleTriple.relativeClass_eq_zero_iff (isClosed_supportWindowBoundary L) _).mpr
      ((BundleTriple.relativeClass_eq_zero_iff (isClosed_supportWindowBoundary L) _).mp hz)
  -- Each map in the unchanged window construction is additive.
  unfold SupportBundleTriple.windowClass
  rw [hsmall, map_zero, map_zero, map_zero]

/-- On compact bases, forgetting support gives the source-minus-target class. -/
theorem SupportBundleTriple.compactSupportClass_toAbsolute [CompactSpace X]
    (a : SupportBundleTriple X) :
    compactSupportKZeroToAbsolute a.compactSupportClass =
      a.source.kZeroClass - a.target.kZeroClass := by
  classical
  let L : Set X := Set.univ
  have hL : IsCompact L := isCompact_univ
  have haL : a.datum.control ⊆ interior L := by simp [L]
  let := isCompact_iff_compactSpace.mp hL
  let := PointedQuotient.t2Space (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
  let := (isClosed_supportWindowBoundary L).isOpen_compl.locallyCompactSpace
  let := (isOpen_interior (s := L)).locallyCompactSpace
  let e := supportWindowInteriorHomeomorph L
  let q := PointedQuotient.onePointHomeomorph.{_, 0}
    (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
  let d := (a.windowTriple L haL).relativeClass (isClosed_supportWindowBoundary L)
  let i : C(X, OnePoint X) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  let j : C(X, L) := ⟨fun x ↦ ⟨x, Set.mem_univ x⟩,
    continuous_id.subtype_mk _⟩
  let p : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let c : C(OnePoint X, OnePoint (interior L : Set X)) :=
    ⟨onePointCollapse (interior L), continuous_onePointCollapse (interior L) isOpen_interior⟩
  let r := properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap
  let s : C(OnePoint ((supportWindowBoundary L)ᶜ : Set L),
      PointedQuotient.{_, 0} (supportWindowBoundary L)) := ⟨q.symm, q.symm.continuous⟩
  let Q : C(L, PointedQuotient.{_, 0} (supportWindowBoundary L)) :=
    ⟨PointedQuotient.of (supportWindowBoundary L),
      PointedQuotient.continuous_of (supportWindowBoundary L)⟩
  -- The whole-base window keeps every original finite point in the actual quotient.
  have hsquare : s.comp (r.comp (c.comp i)) = Q.comp j := by
    ext x
    have hx : x ∈ interior L := by simp [L]
    change q.symm (OnePoint.map e.symm (onePointCollapse (interior L) (x : OnePoint X))) = _
    rw [onePointCollapse_coe_of_mem (interior L) x hx]
    exact q.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of (supportWindowBoundary L)
        (isClosed_supportWindowBoundary L) (e.symm ⟨x, hx⟩)).symm
  -- Restriction to the whole base and its inverse preserve each original bundle class.
  have hpj : p.comp j = ContinuousMap.id X := by ext x; rfl
  have hbundle (E : FiniteBundle X) : complexKZeroPullback j (E.restrict L).kZeroClass =
      E.kZeroClass := by
    change complexKZeroPullback j (E.pullback p).kZeroClass = _
    rw [FiniteBundle.kZeroClass_pullback, ← AddMonoidHom.comp_apply,
      ← complexKZeroPullback_comp, hpj]
    change kZeroMap (RingHom.id _) E.kZeroClass = E.kZeroClass
    rw [kZeroMap_id]
    rfl
  rw [a.compactSupportClass_eq_windowClass L hL haL]
  change complexKZeroPullback i
    (complexKZeroPullback c (complexKZeroPullback r (complexKZeroPullback s d.val))) = _
  calc
    _ = complexKZeroPullback j (relativeKZeroForget (supportWindowBoundary L)
        (isClosed_supportWindowBoundary L) d) := by
      change complexKZeroPullback i
        (complexKZeroPullback c (complexKZeroPullback r (complexKZeroPullback s d.val))) =
          complexKZeroPullback j (complexKZeroPullback Q d.val)
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
        hsquare, complexKZeroPullback_comp]
      rfl
    _ = complexKZeroPullback j
        ((a.source.restrict L).kZeroClass - (a.target.restrict L).kZeroClass) := by
      rw [BundleTriple.relativeClass_forget]
      rfl
    _ = a.source.kZeroClass - a.target.kZeroClass := by
      rw [map_sub, hbundle, hbundle]

variable {Y : Type*} [TopologicalSpace Y] [hLY : LocallyCompactSpace Y] [hTY : T2Space Y]
include hLY hTY

set_option maxHeartbeats 5000000 in

/-- The constructed class is natural under proper pullback. -/
theorem SupportBundleTriple.compactSupportClass_pullback (a : SupportBundleTriple X)
    (f : C(Y, X)) (hf : IsProperMap f) :
    (a.pullback f hf).compactSupportClass =
      compactSupportKZeroPullback f hf a.compactSupportClass := by
  classical
  let L := supportNeighborhood a.datum.control a.datum.isCompact_control
  have hL : IsCompact L :=
    isCompact_supportNeighborhood a.datum.control a.datum.isCompact_control
  have haL : a.datum.control ⊆ interior L :=
    subset_interior_supportNeighborhood a.datum.control a.datum.isCompact_control
  let K : Set Y := f ⁻¹' L
  have hK : IsCompact K := hf.isCompact_preimage hL
  let := isCompact_iff_compactSpace.mp hL
  let := isCompact_iff_compactSpace.mp hK
  -- Continuity gives only this inclusion; equality of the interiors is not needed.
  have hinterior : f ⁻¹' interior L ⊆ interior K :=
    interior_maximal (Set.preimage_mono interior_subset)
      (isOpen_interior.preimage f.continuous)
  have haK : (a.pullback f hf).datum.control ⊆ interior K :=
    (Set.preimage_mono haL).trans hinterior
  -- Restriction of the boundary retains the exact original clutching bundle.
  have changePair {A B : Set K} (hA : IsClosed A) (hB : IsClosed B) (hBA : B ⊆ A)
      (a : BundleTriple A) :
      (BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)).relativeClass hB =
        relativeKZeroEnlarge B A hB hA hBA (a.relativeClass hA) := by
    let b := BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)
    let := DoubleSpace.t2Space A hA
    let := DoubleSpace.t2Space B hB
    let Wa := clutchingBundle hA a
    let d := DoubleSpace.mapContinuous B A (ContinuousMap.id K) hBA
    let W := Wa.pullback d
    -- The two original charts pull back along the identity on each copy of K.
    let eL : Iso ((DoubleSpace.leftMap B : K → DoubleSpace B) *ᵖ W.Fiber) a.source.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).trans
        (clutchingLeftIso hA a)
    let eR : Iso ((DoubleSpace.rightMap B : K → DoubleSpace B) *ᵖ W.Fiber) a.target.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).trans
        (clutchingRightIso hA a)
    have heL (x : K) (v : Wa.Fiber (DoubleSpace.left A x)) :
        eL.linearEquiv x v = (clutchingLeftIso hA a).linearEquiv x v := by
      change (clutchingLeftIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have heR (x : K) (v : Wa.Fiber (DoubleSpace.right A x)) :
        eR.linearEquiv x v = (clutchingRightIso hA a).linearEquiv x v := by
      change (clutchingRightIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have hinv (x : K) (v : a.source.Fiber x) :
        (eL.linearEquiv x).symm v = ((clutchingLeftIso hA a).linearEquiv x).symm v := by
      apply (eL.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, heL, LinearEquiv.apply_symm_apply]
    have hseam : ClutchingCompatible b W eL eR := by
      intro x v
      change eR.linearEquiv x
        (cast (congrArg W.Fiber (DoubleSpace.left_eq_right B x))
          ((eL.linearEquiv x).symm v)) = (a.boundary.restrict hBA).linearEquiv x v
      rw [heR, hinv]
      exact (clutching_seam_apply hA a ⟨x, hBA x.property⟩ v).trans
        (Iso.restrictTo_apply a.boundary hBA x v).symm
    obtain ⟨e⟩ := nonempty_clutching_iso hB b W eL eR hseam
    let := W.isFiniteRank
    let := (clutchingBundle hB b).isFiniteRank
    have hglued := kZeroClass_eq_of_iso e.symm
    change (clutchingBundle hB b).kZeroClass = (Wa.pullback d).kZeroClass at hglued
    rw [FiniteBundle.kZeroClass_pullback] at hglued
    -- Both sides subtract the pullback of the same target bundle along projection.
    have hproj : (DoubleSpace.projMap A).comp d = DoubleSpace.projMap B := by
      ext z
      induction z using Quotient.inductionOn with
      | h z => cases z <;> rfl
    have hprojection : complexKZeroPullback (DoubleSpace.projMap B) a.target.kZeroClass =
        complexKZeroPullback d
          (complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass) := by
      have h := DFunLike.congr_fun
        (complexKZeroPullback_comp d (DoubleSpace.projMap A)) a.target.kZeroClass
      rw [hproj] at h
      exact h
    have hdouble : b.doubleDifference hB = complexKZeroPullback d (a.doubleDifference hA) := by
      change (clutchingBundle hB b).kZeroClass -
        complexKZeroPullback (DoubleSpace.projMap B) a.target.kZeroClass =
          complexKZeroPullback d
            (Wa.kZeroClass - complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass)
      rw [map_sub, hglued, hprojection]
    let RA := DoubleSpace.rightRange A
    let RB := DoubleSpace.rightRange B
    have hRA : IsClosed RA := DoubleSpace.isClosed_rightRange A hA
    have hRB : IsClosed RB := DoubleSpace.isClosed_rightRange B hB
    have hd : Set.MapsTo d RB RA := by
      rintro z ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    let dPull := relativeKZeroPullback RB hRB RA hRA d hd
    -- Forgetting is used injectively only on the retracting source double.
    have hlift : b.differenceLift hB = dPull (a.differenceLift hA) := by
      apply relativeKZeroForget_injective_of_retraction RB hRB
        (DoubleSpace.rightRetraction B) (DoubleSpace.rightRetraction_apply B)
      have hn := relativeKZeroForget_natural RB hRB RA hRA d hd
      calc
        _ = b.doubleDifference hB := b.forget_differenceLift hB
        _ = complexKZeroPullback d (a.doubleDifference hA) := hdouble
        _ = complexKZeroPullback d
            (relativeKZeroForget RA hRA (a.differenceLift hA)) := by
          rw [a.forget_differenceLift hA]
        _ = _ := (DFunLike.congr_fun hn (a.differenceLift hA)).symm
    have hrestriction : (DoubleSpace.relativeRestriction B hB).comp dPull =
        (relativeKZeroEnlarge B A hB hA hBA).comp
          (DoubleSpace.relativeRestriction A hA) := by
      change (relativeKZeroPullback B hB RB hRB (DoubleSpace.leftMap B)
        (DoubleSpace.left_mapsTo B)).comp (relativeKZeroPullback RB hRB RA hRA d hd) =
          (relativeKZeroPullback B hB A hA (ContinuousMap.id K) hBA).comp
            (relativeKZeroPullback A hA RA hRA (DoubleSpace.leftMap A)
              (DoubleSpace.left_mapsTo A))
      have hleft := relativeKZeroPullback_comp B hB RB hRB RA hRA
        (DoubleSpace.leftMap B) d (DoubleSpace.left_mapsTo B) hd
      have hright := relativeKZeroPullback_comp B hB A hA RA hRA
        (ContinuousMap.id K) (DoubleSpace.leftMap A) hBA (DoubleSpace.left_mapsTo A)
      rw [← hleft, ← hright]
      congr 1
    change DoubleSpace.relativeRestriction B hB (b.differenceLift hB) =
      relativeKZeroEnlarge B A hB hA hBA
        (DoubleSpace.relativeRestriction A hA (a.differenceLift hA))
    rw [hlift]
    exact DFunLike.congr_fun hrestriction (a.differenceLift hA)
  let pL : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let pK : C(K, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(K, L) := preimageSubspaceMap L f
  let A := supportWindowBoundary L
  have hA : IsClosed A := isClosed_supportWindowBoundary L
  let B := supportWindowBoundary K
  have hB : IsClosed B := isClosed_supportWindowBoundary K
  let C : Set K := g ⁻¹' A
  have hC : IsClosed C := hA.preimage g.continuous
  have hBC : B ⊆ C := by
    intro y hy hfin
    exact hy (hinterior hfin)
  let t := a.windowTriple L haL
  let b := t.pullback g
  let d : RelativeKZero.{_, 0} A hA := t.relativeClass hA
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space B hB
  -- Reassociate the two actual pullbacks without changing any fiber vector.
  let u (E : FiniteBundle X) :
      Iso ((E.restrict L).pullback g).Fiber ((E.pullback f).restrict K).Fiber :=
    (pullbackCompIso (E := E.Fiber) pL g).trans
      (pullbackCompIso (E := E.Fiber) f pK).symm
  have hu (E : FiniteBundle X) (y : K) (v : E.Fiber (f y)) :
      (u E).linearEquiv y v = v := by
    change ((pullbackCompIso (E := E.Fiber) f pK).linearEquiv y).symm
      ((pullbackCompIso (E := E.Fiber) pL g).linearEquiv y v) = v
    rw [pullbackCompIso_apply]
    apply ((pullbackCompIso (E := E.Fiber) f pK).linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
  have hi : (BundleTriple.ofBoundary b.source b.target (b.boundary.restrict hBC)).IsIsomorphic
      ((a.pullback f hf).windowTriple K haK) := by
    refine ⟨u a.source, u a.target, ?_⟩
    intro y v
    change (u a.target).linearEquiv y.val ((b.boundary.restrict hBC).linearEquiv y v) =
      ((a.pullback f hf).windowBoundary K haK).linearEquiv y ((u a.source).linearEquiv y.val v)
    rw [hu, hu]
    have hl := (Iso.restrictTo_apply b.boundary hBC y v).trans
      ((RelativeTriple.pullback_apply t.boundary g ⟨y.val, hBC y.property⟩ v).trans
        (a.windowBoundary_apply L haL ⟨g y.val, hBC y.property⟩ v))
    have hr := ((a.pullback f hf).windowBoundary_apply K haK y v).trans
      (RelativeTriple.pullback_apply a.datum.boundary f
        ⟨y.val.val, supportWindowBoundary_subset (f ⁻¹' a.datum.control) K haK y.property⟩ v)
    exact hl.trans hr.symm
  have hclass : ((a.pullback f hf).windowTriple K haK).relativeClass hB =
      relativeKZeroPullback B hB A hA g hBC d := by
    -- First use exact inverse-image naturality, then restrict its boundary to B.
    have hiso := BundleTriple.relativeClass_eq_of_isIsomorphic hB _ _ hi
    rw [← hiso, changePair hC hB hBC b, t.relativeClass_pullback hA g]
    have hcomp := relativeKZeroPullback_comp B hB C hC A hA
      (ContinuousMap.id K) g hBC (fun _ hx ↦ hx)
    exact (DFunLike.congr_fun hcomp d).symm
  -- Retain the exact pointed maps defining each original compact-window class.
  let eL := supportWindowInteriorHomeomorph L
  let qL := PointedQuotient.onePointHomeomorph.{_, 0} A hA
  let eK := supportWindowInteriorHomeomorph K
  let qK := PointedQuotient.onePointHomeomorph.{_, 0} B hB
  let := hA.isOpen_compl.locallyCompactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let := (isOpen_interior (s := L)).locallyCompactSpace
  let := (isOpen_interior (s := K)).locallyCompactSpace
  let wL : C(OnePoint X, PointedQuotient.{_, 0} A) :=
    (⟨qL.symm, qL.symm.continuous⟩ : C(_, _)).comp
      ((properOnePointMap ⟨eL.symm, eL.symm.continuous⟩ eL.symm.isProperMap).comp
        ⟨onePointCollapse (interior L), continuous_onePointCollapse (interior L) isOpen_interior⟩)
  let wK : C(OnePoint Y, PointedQuotient.{_, 0} B) :=
    (⟨qK.symm, qK.symm.continuous⟩ : C(_, _)).comp
      ((properOnePointMap ⟨eK.symm, eK.symm.continuous⟩ eK.symm.isProperMap).comp
        ⟨onePointCollapse (interior K), continuous_onePointCollapse (interior K) isOpen_interior⟩)
  let U := PointedQuotient.mapContinuous B A g hBC
  let F := properOnePointMap f hf
  have hwL (x : X) (hx : x ∈ interior L) :
      wL (x : OnePoint X) = PointedQuotient.of A ⟨x, interior_subset hx⟩ := by
    change qL.symm (OnePoint.map eL.symm (onePointCollapse (interior L) (x : OnePoint X))) = _
    rw [onePointCollapse_coe_of_mem (interior L) x hx]
    exact qL.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of A hA (eL.symm ⟨x, hx⟩)).symm
  have hwK (y : Y) (hy : y ∈ interior K) :
      wK (y : OnePoint Y) = PointedQuotient.of B ⟨y, interior_subset hy⟩ := by
    change qK.symm (OnePoint.map eK.symm (onePointCollapse (interior K) (y : OnePoint Y))) = _
    rw [onePointCollapse_coe_of_mem (interior K) y hy]
    exact qK.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of B hB (eK.symm ⟨y, hy⟩)).symm
  have hwLout (x : X) (hx : x ∉ interior L) :
      wL (x : OnePoint X) = PointedQuotient.basepoint A := by
    change qL.symm (OnePoint.map eL.symm (onePointCollapse (interior L) (x : OnePoint X))) = _
    rw [onePointCollapse_coe_of_notMem (interior L) x hx]
    exact PointedQuotient.onePointHomeomorph_symm_infty A hA
  have hwKout (y : Y) (hy : y ∉ interior K) :
      wK (y : OnePoint Y) = PointedQuotient.basepoint B := by
    change qK.symm (OnePoint.map eK.symm (onePointCollapse (interior K) (y : OnePoint Y))) = _
    rw [onePointCollapse_coe_of_notMem (interior K) y hy]
    exact PointedQuotient.onePointHomeomorph_symm_infty B hB
  have hsquare : U.comp wK = wL.comp F := by
    ext z
    cases z using OnePoint.rec with
    | infty =>
      change U (wK ∞) = wL ∞
      have hKinf : wK ∞ = PointedQuotient.basepoint B :=
        PointedQuotient.onePointHomeomorph_symm_infty B hB
      have hLinf : wL ∞ = PointedQuotient.basepoint A :=
        PointedQuotient.onePointHomeomorph_symm_infty A hA
      rw [hKinf, hLinf]
      rfl
    | coe y =>
      change U (wK (y : OnePoint Y)) = wL (f y : OnePoint X)
      by_cases hyL : f y ∈ interior L
      · rw [hwK y (hinterior hyL), hwL (f y) hyL]
        rfl
      · rw [hwLout (f y) hyL]
        by_cases hyK : y ∈ interior K
        · rw [hwK y hyK]
          -- Extra interior points have image in the original boundary and are collapsed there.
          exact (PointedQuotient.of_eq_basepoint_iff A (g ⟨y, interior_subset hyK⟩)).2 hyL
        · rw [hwKout y hyK]
          rfl
  have hwindowL : (a.windowClass L hL haL).val = complexKZeroPullback wL d.val := by
    change complexKZeroPullback
      ⟨onePointCollapse (interior L), continuous_onePointCollapse (interior L) isOpen_interior⟩
      (complexKZeroPullback
        (properOnePointMap ⟨eL.symm, eL.symm.continuous⟩ eL.symm.isProperMap)
        (complexKZeroPullback ⟨qL.symm, qL.symm.continuous⟩ d.val)) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  have hwindowK : ((a.pullback f hf).windowClass K hK haK).val =
      complexKZeroPullback wK
        (((a.pullback f hf).windowTriple K haK).relativeClass hB).val := by
    change complexKZeroPullback
      ⟨onePointCollapse (interior K), continuous_onePointCollapse (interior K) isOpen_interior⟩
      (complexKZeroPullback
        (properOnePointMap ⟨eK.symm, eK.symm.continuous⟩ eK.symm.isProperMap)
        (complexKZeroPullback ⟨qK.symm, qK.symm.continuous⟩ _)) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  -- Pull back the same original relative class along the verified square.
  rw [(a.pullback f hf).compactSupportClass_eq_windowClass K hK haK,
    a.compactSupportClass_eq_windowClass L hL haL]
  apply Subtype.ext
  change ((a.pullback f hf).windowClass K hK haK).val =
    complexKZeroPullback F (a.windowClass L hL haL).val
  rw [hwindowK, hwindowL, hclass]
  change complexKZeroPullback wK (complexKZeroPullback U d.val) =
    complexKZeroPullback F (complexKZeroPullback wL d.val)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]

/-- Change of coordinates sends a support class to its transported triple class. -/
theorem SupportBundleTriple.compactSupportClass_homeomorph (a : SupportBundleTriple X)
    (e : X ≃ₜ Y) :
    compactSupportKZeroHomeomorph e a.compactSupportClass =
      (a.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap).compactSupportClass := by
  -- The transport uses precisely this inverse homeomorphism as its proper map.
  exact (a.compactSupportClass_pullback
    ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap).symm

end AtiyahSinger.ComplexBundle

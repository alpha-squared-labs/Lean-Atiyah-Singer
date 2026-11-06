/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeKZeroNeighborhood
public import AtiyahSinger.Topology.SupportDifference

/-!
# Compare support triples with the compactification K group

Public module ID: M2186.

D07/K02. The forward map is fixed on every generator by its constructed compact-
window difference. Vanishing is detected on a larger compact window using
KA II.4.22. Complements are taken only on that compact window, so the stabilizer
can be made trivial and extended globally. No complement on the noncompact base
and no compactification extension of an arbitrary original bundle is assumed.
Sources: SG I.9.26; KA II.2.28–2.29 and II.4.21–4.22.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle OnePoint
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X] [hL : LocallyCompactSpace X] [hT : T2Space X]

include hL hT

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial


set_option maxHeartbeats 6000000 in

set_option backward.isDefEq.respectTransparency false in
/-- A zero compact-support class vanishes as a relative class on a sufficiently large window. -/
theorem SupportBundleTriple.exists_window_relativeClass_eq_zero (a : SupportBundleTriple X)
    (ha : a.compactSupportClass = 0) :
    ∃ L : Set X, ∃ hL : IsCompact L, ∃ h : a.datum.control ⊆ interior L,
      letI := isCompact_iff_compactSpace.mp hL
      (a.windowTriple L h).relativeClass (isClosed_supportWindowBoundary L) = 0 := by
  /- Use a compact window to regard its relative difference as a class on the one-point
  compactification relative to a closed neighborhood of infinity, by the complement/quotient
  homeomorphism. The map to the singleton relative group is zero, since singleton forgetting
  is the reduced isomorphism and the constructed support class vanishes. KA II.4.22(b) makes
  it zero on a smaller closed neighborhood of infinity. Choose a larger compact window whose
  exterior is contained in that neighborhood. Excision with the original boundary
  trivialization identifies its window difference with the zero restricted class. This does
  not assume open extension is injective. -/
  classical
  -- Work first in the small quotient universe used by the constructed support class.
  let L := supportNeighborhood a.datum.control a.datum.isCompact_control
  have hL : IsCompact L := isCompact_supportNeighborhood _ _
  have haL : a.datum.control ⊆ interior L := subset_interior_supportNeighborhood _ _
  let := isCompact_iff_compactSpace.mp hL
  let BL := supportWindowBoundary L
  have hBL : IsClosed BL := isClosed_supportWindowBoundary L
  let S : Set (OnePoint X) := ((fun x : X ↦ (x : OnePoint X)) '' interior L)ᶜ
  have hS : IsClosed S := (OnePoint.isOpen_image_coe.mpr isOpen_interior).isClosed_compl
  have hSN : S ∈ 𝓝 (∞ : OnePoint X) := by
    apply Filter.mem_of_superset
      ((OnePoint.isOpen_compl_image_coe.mpr ⟨hL.isClosed, hL⟩).mem_nhds
        (Set.mem_compl OnePoint.infty_notMem_image_coe))
    exact Set.compl_subset_compl.mpr (Set.image_mono interior_subset)
  let fL : C(L, OnePoint X) :=
    ⟨fun x ↦ (x.val : OnePoint X), OnePoint.continuous_coe.comp continuous_subtype_val⟩
  have hLS (x : L) : fL x ∈ S ↔ x ∈ BL := by
    simp [fL, S, BL, supportWindowBoundary]
  let k := PointedQuotient.mapContinuous BL S fL (fun x hx ↦ (hLS x).mpr hx)
  let := PointedQuotient.compactSpace BL
  let := PointedQuotient.t2Space BL hBL
  let := PointedQuotient.compactSpace S
  let := PointedQuotient.t2Space S hS
  -- Collapsing the actual exterior identifies exactly the original window boundary.
  have hk : Function.Bijective k := by
    constructor
    · intro z w hzw
      rcases PointedQuotient.eq_basepoint_or_exists BL z with rfl | ⟨x, rfl⟩ <;>
        rcases PointedQuotient.eq_basepoint_or_exists BL w with rfl | ⟨y, rfl⟩
      · rfl
      · have hy : fL y ∈ S := (PointedQuotient.of_eq_basepoint_iff S (fL y)).mp hzw.symm
        exact ((PointedQuotient.of_eq_basepoint_iff BL y).mpr ((hLS y).mp hy)).symm
      · have hx : fL x ∈ S := (PointedQuotient.of_eq_basepoint_iff S (fL x)).mp hzw
        exact (PointedQuotient.of_eq_basepoint_iff BL x).mpr ((hLS x).mp hx)
      · rcases (PointedQuotient.of_eq_of_iff S (fL x) (fL y)).mp hzw with hxy | ⟨hx, hy⟩
        · exact congrArg (PointedQuotient.of BL)
            (Subtype.ext (OnePoint.coe_injective hxy))
        · exact (PointedQuotient.of_eq_of_iff BL x y).mpr
            (Or.inr ⟨(hLS x).mp hx, (hLS y).mp hy⟩)
    · intro z
      rcases PointedQuotient.eq_basepoint_or_exists S z with rfl | ⟨x, rfl⟩
      · exact ⟨PointedQuotient.basepoint BL, rfl⟩
      cases x using OnePoint.rec with
      | infty =>
        refine ⟨PointedQuotient.basepoint BL, ?_⟩
        exact ((PointedQuotient.of_eq_basepoint_iff S ∞).mpr
          OnePoint.infty_notMem_image_coe).symm
      | coe x =>
        by_cases hx : x ∈ interior L
        · exact ⟨PointedQuotient.of BL ⟨x, interior_subset hx⟩, rfl⟩
        · refine ⟨PointedQuotient.basepoint BL, ?_⟩
          exact ((PointedQuotient.of_eq_basepoint_iff S (x : OnePoint X)).mpr
            (by simpa [S] using hx)).symm
  let e := (Equiv.ofBijective k hk).toHomeomorphOfContinuousClosed
    k.continuous k.continuous.isClosedMap
  let g : C(PointedQuotient S, PointedQuotient BL) := ⟨e.symm, e.symm.continuous⟩
  have hg : g (PointedQuotient.basepoint S) = PointedQuotient.basepoint BL :=
    e.symm_apply_eq.mpr rfl
  let dL : RelativeKZero.{_, 0} BL hBL := (a.windowTriple L haL).relativeClass hBL
  let c : RelativeKZero.{_, 0} S hS :=
    reducedComplexKZeroPullback (PointedQuotient.basepoint S)
      (PointedQuotient.basepoint BL) g hg dL
  have hLc : relativeKZeroPullback BL hBL S hS fL (fun x hx ↦ (hLS x).mpr hx) c = dL := by
    apply Subtype.ext
    change complexKZeroPullback k (complexKZeroPullback g dL.val) = dL.val
    have hid : g.comp k = ContinuousMap.id _ := by
      ext x
      exact e.symm_apply_apply x
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) dL.val = dL.val
    rw [kZeroMap_id]
    rfl
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
  have hcforget : relativeKZeroForget S hS c = a.compactSupportClass.val := by
    have hsquare : k.comp (wMap L hL) =
        (⟨PointedQuotient.of S, PointedQuotient.continuous_of S⟩ : C(_, _)) := by
      ext z
      cases z using OnePoint.rec with
      | infty =>
        change k (wMap L hL ∞) = PointedQuotient.of S ∞
        rw [hmapInfinity L hL]
        exact ((PointedQuotient.of_eq_basepoint_iff S ∞).mpr
          OnePoint.infty_notMem_image_coe).symm
      | coe x =>
        change k (wMap L hL (x : OnePoint X)) = PointedQuotient.of S (x : OnePoint X)
        by_cases hx : x ∈ interior L
        · rw [hmapMem L hL x hx]
          rfl
        · rw [hmapNotMem L hL x hx]
          exact ((PointedQuotient.of_eq_basepoint_iff S (x : OnePoint X)).mpr
            (by simpa [S] using hx)).symm
    have hvalue := congrArg Subtype.val hLc
    change complexKZeroPullback k c.val = dL.val at hvalue
    rw [a.compactSupportClass_eq_windowClass L hL haL, hwindow L hL haL]
    change complexKZeroPullback
      ⟨PointedQuotient.of S, PointedQuotient.continuous_of S⟩ c.val =
        complexKZeroPullback (wMap L hL) dL.val
    rw [← hvalue, ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
  have hc0 : relativeKZeroNeighborhoodToPoint (∞ : OnePoint X) S hS hSN c = 0 := by
    apply relativeKZeroPointToReduced_injective ∞
    apply Subtype.ext
    change relativeKZeroForget ({∞} : Set (OnePoint X)) isClosed_singleton
      (relativeKZeroEnlarge {∞} S isClosed_singleton hS
        (singleton_subset_of_mem_nhds ∞ S hSN) c) = 0
    have he := DFunLike.congr_fun
      (relativeKZeroForget_enlarge {∞} S isClosed_singleton hS
        (singleton_subset_of_mem_nhds ∞ S hSN)) c
    change relativeKZeroForget {∞} isClosed_singleton
      (relativeKZeroEnlarge {∞} S isClosed_singleton hS
        (singleton_subset_of_mem_nhds ∞ S hSN) c) = relativeKZeroForget S hS c at he
    rw [he, hcforget]
    exact congrArg Subtype.val ha
  -- Shrinking the actual infinity neighborhood detects zero before choosing the new window.
  obtain ⟨T, hT, hTN, hTS, hcT⟩ :=
    relativeKZero_neighborhood_eventually_zero (∞ : OnePoint X) S hS hSN c hc0
  obtain ⟨K, ⟨hKclosed, hK⟩, hKT⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hTN
  let M := supportNeighborhood (L ∪ K) (hL.union hK)
  have hM : IsCompact M := isCompact_supportNeighborhood _ _
  have hLKM : L ∪ K ⊆ interior M := subset_interior_supportNeighborhood _ _
  have hLM : L ⊆ M := fun _ hx ↦ interior_subset (hLKM (Or.inl hx))
  have haM : a.datum.control ⊆ interior M :=
    fun _ hx ↦ hLKM (Or.inl (interior_subset (haL hx)))
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
  let pM : C(M, OnePoint X) :=
    ⟨fun x ↦ (x.val : OnePoint X), OnePoint.continuous_coe.comp continuous_subtype_val⟩
  have hCS : Set.MapsTo pM C S := by
    intro x hx
    simpa [pM, S, C] using hx
  -- Closed excision is injective here through the actual window quotient homeomorphism.
  have hsLinj : Function.Injective sL := by
    let u := PointedQuotient.mapContinuous (supportWindowBoundary L) C i (fun _ hx ↦ hx)
    let := PointedQuotient.compactSpace C
    let := PointedQuotient.t2Space C hC
    have hu : Function.Bijective u := by
      constructor
      · intro z w hzw
        rcases PointedQuotient.eq_basepoint_or_exists (supportWindowBoundary L) z
          with rfl | ⟨x, rfl⟩ <;>
          rcases PointedQuotient.eq_basepoint_or_exists (supportWindowBoundary L) w
            with rfl | ⟨y, rfl⟩
        · rfl
        · have hy : i y ∈ C := (PointedQuotient.of_eq_basepoint_iff C (i y)).mp hzw.symm
          exact ((PointedQuotient.of_eq_basepoint_iff (supportWindowBoundary L) y).mpr hy).symm
        · have hx : i x ∈ C := (PointedQuotient.of_eq_basepoint_iff C (i x)).mp hzw
          exact (PointedQuotient.of_eq_basepoint_iff (supportWindowBoundary L) x).mpr hx
        · rcases (PointedQuotient.of_eq_of_iff C (i x) (i y)).mp hzw with hxy | ⟨hx, hy⟩
          · exact congrArg (PointedQuotient.of (supportWindowBoundary L))
              (Subtype.ext (congrArg (fun z : M ↦ (z : X)) hxy))
          · exact (PointedQuotient.of_eq_of_iff (supportWindowBoundary L) x y).mpr
              (Or.inr ⟨hx, hy⟩)
      · intro z
        rcases PointedQuotient.eq_basepoint_or_exists C z with rfl | ⟨x, rfl⟩
        · exact ⟨PointedQuotient.basepoint (supportWindowBoundary L), rfl⟩
        by_cases hx : x.val ∈ interior L
        · exact ⟨PointedQuotient.of (supportWindowBoundary L) ⟨x.val, interior_subset hx⟩, rfl⟩
        · exact ⟨PointedQuotient.basepoint (supportWindowBoundary L),
            ((PointedQuotient.of_eq_basepoint_iff C x).mpr hx).symm⟩
    let v := (Equiv.ofBijective u hu).toHomeomorphOfContinuousClosed
      u.continuous u.continuous.isClosedMap
    let w : C(PointedQuotient C, PointedQuotient (supportWindowBoundary L)) :=
      ⟨v.symm, v.symm.continuous⟩
    have hleft (z : ComplexKZero (PointedQuotient C)) :
        complexKZeroPullback w (complexKZeroPullback u z) = z := by
      have hid : u.comp w = ContinuousMap.id _ := by
        ext y
        exact v.apply_symm_apply y
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
      change kZeroMap (RingHom.id _) z = z
      rw [kZeroMap_id]
      rfl
    intro x y hxy
    apply Subtype.ext
    have hvalue := congrArg Subtype.val hxy
    change complexKZeroPullback u x.val = complexKZeroPullback u y.val at hvalue
    exact (hleft x.val).symm.trans
      ((congrArg (complexKZeroPullback w) hvalue).trans (hleft y.val))
  have hd : d = relativeKZeroPullback C hC S hS pM hCS c := by
    apply hsLinj
    rw [← hLclass]
    have hcomp := DFunLike.congr_fun
      (relativeKZeroPullback_comp (supportWindowBoundary L)
        (isClosed_supportWindowBoundary L) C hC S hS i pM (fun _ hx ↦ hx) hCS) c
    change relativeKZeroPullback (supportWindowBoundary L)
      (isClosed_supportWindowBoundary L) S hS (pM.comp i) _ c =
        sL (relativeKZeroPullback C hC S hS pM hCS c) at hcomp
    rw [← hcomp]
    exact hLc.symm
  have hMT : Set.MapsTo pM (supportWindowBoundary M) T := by
    intro x hx
    have hxK : x.val ∉ K := fun hxK ↦ hx (hLKM (Or.inr hxK))
    exact hKT (Or.inl ⟨x.val, hxK, rfl⟩)
  have hMzero : BundleTriple.relativeClass.{_, 0}
      (isClosed_supportWindowBoundary M) (a.windowTriple M haM) = 0 := by
    rw [hMclass, hd]
    have hcomp₁ := DFunLike.congr_fun
      (relativeKZeroPullback_comp (supportWindowBoundary M)
        (isClosed_supportWindowBoundary M) C hC S hS
        (ContinuousMap.id M) pM hMC hCS) c
    change relativeKZeroPullback (supportWindowBoundary M)
      (isClosed_supportWindowBoundary M) S hS pM _ c =
        sM (relativeKZeroPullback C hC S hS pM hCS c) at hcomp₁
    rw [← hcomp₁]
    have hcomp₂ := DFunLike.congr_fun
      (relativeKZeroPullback_comp (supportWindowBoundary M)
        (isClosed_supportWindowBoundary M) T hT S hS pM
        (ContinuousMap.id (OnePoint X)) hMT hTS) c
    change relativeKZeroPullback (supportWindowBoundary M)
      (isClosed_supportWindowBoundary M) S hS pM _ c =
        relativeKZeroPullback (supportWindowBoundary M)
          (isClosed_supportWindowBoundary M) T hT pM hMT
          (relativeKZeroEnlarge T S hT hS hTS c) at hcomp₂
    rw [hcomp₂, hcT, map_zero]
  -- The original conclusion permits another quotient universe; the extension criterion
  -- transports this same zero class, without changing any bundle or boundary witness.
  refine ⟨M, hM, haM, ?_⟩
  exact (BundleTriple.relativeClass_eq_zero_iff (isClosed_supportWindowBoundary M) _).mpr
    ((BundleTriple.relativeClass_eq_zero_iff (isClosed_supportWindowBoundary M) _).mp hMzero)

set_option maxHeartbeats 4000000 in

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing gives an extension after a finite trivial stabilization and larger control. -/
theorem SupportBundleTriple.compactSupportClass_eq_zero_iff_trivial (a : SupportBundleTriple X) :
    a.compactSupportClass = 0 ↔ ∃ n : ℕ,
      ∃ L : Set X, ∃ hL : IsCompact L, ∃ h : a.datum.control ⊆ L,
        ∃ e : Iso (a.source.sum (FiniteBundle.trivial X n)).Fiber
          (a.target.sum (FiniteBundle.trivial X n)).Fiber,
            e.restrict Lᶜ =
              (a.datum.enlarge L hL h).boundary.stabilize (FiniteBundle.trivial X n).Fiber := by
  /- For a zero class choose a window where its relative difference is zero. The compact-pair
  zero criterion gives a local stabilizing bundle and an extension. Add a complement to this
  stabilizer on the compact window and transport their sum to a finite trivial bundle. Glue
  the stabilized extension on the window to the original stabilized boundary map on the
  closed exterior; they agree on the window boundary, as do their inverses. Conversely such
  a global extension identifies the stabilized germ with identity, whose constructed class
  vanishes. Only the stabilizer on the compact window needs a complement. -/
  classical
  constructor
  · intro ha
    obtain ⟨L, hL, haL, hzero⟩ :=
      SupportBundleTriple.exists_window_relativeClass_eq_zero.{_, 0} a ha
    let := isCompact_iff_compactSpace.mp hL
    let E := a.source.restrict L
    let F := a.target.restrict L
    obtain ⟨G, e₀, he₀⟩ :=
      (BundleTriple.relativeClass_eq_zero_iff (isClosed_supportWindowBoundary L) _).mp hzero
    -- Only the stabilizer on this compact window is replaced by a finite trivial bundle.
    let p := idempotentPresentation (E := G.Fiber)
    let := p.complement.fiberTotalSpaceTopology
    let := p.complement.isFiniteRank_fiber
    let H := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
    obtain ⟨q⟩ := nonempty_presentation_complement_iso (E := G.Fiber)
    let Z := FiniteBundle.trivial X p.size
    let ZL := FiniteBundle.trivial L p.size
    let e₁ : Iso (E.sum ZL).Fiber (F.sum ZL).Fiber :=
      ((Iso.refl E.Fiber).sum q.symm).trans
        ((E.sumAssocIso G H).symm.trans
          ((e₀.sum (Iso.refl H.Fiber)).trans
            ((F.sumAssocIso G H).trans ((Iso.refl F.Fiber).sum q))))
    have assocInv (J K N : FiniteBundle L) (x : L)
        (v : J.Fiber x) (w : K.Fiber x) (z : N.Fiber x) :
        ((J.sumAssocIso K N).linearEquiv x).symm (v, w, z) = ((v, w), z) := by
      apply ((J.sumAssocIso K N).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, FiniteBundle.sumAssocIso_apply]
    have he₁ (x : L) (v : (E.sum ZL).Fiber x) :
        e₁.linearEquiv x v =
          ((e₀.linearEquiv x (v.1, ((q.linearEquiv x).symm v.2).1)).1,
            q.linearEquiv x
              ((e₀.linearEquiv x (v.1, ((q.linearEquiv x).symm v.2).1)).2,
                ((q.linearEquiv x).symm v.2).2)) := by
      change ((Iso.refl F.Fiber).sum q).linearEquiv x
        ((F.sumAssocIso G H).linearEquiv x
          ((e₀.sum (Iso.refl H.Fiber)).linearEquiv x
            (((E.sumAssocIso G H).linearEquiv x).symm
              (v.1, (q.linearEquiv x).symm v.2)))) = _
      rw [assocInv, FiniteBundle.sumAssocIso_apply]
      rfl
    have he₁boundary (x : supportWindowBoundary L) (v : (E.sum ZL).Fiber x.val) :
        e₁.linearEquiv x.val v = ((a.windowBoundary L haL).linearEquiv x v.1, v.2) := by
      let w := (q.linearEquiv x.val).symm v.2
      have he := congrArg (fun b : RelativeTriple (E.sum G).Fiber
        (F.sum G).Fiber (supportWindowBoundary L) ↦ b.linearEquiv x (v.1, w.1)) he₀
      change e₀.linearEquiv x.val (v.1, w.1) =
        ((a.windowBoundary L haL).stabilize G.Fiber).linearEquiv x (v.1, w.1) at he
      have hb := RelativeTriple.sum_apply (a.windowBoundary L haL)
        (RelativeTriple.identity G.Fiber (supportWindowBoundary L)) x (v.1, w.1)
      have hvalue : e₀.linearEquiv x.val (v.1, w.1) =
          ((a.windowBoundary L haL).linearEquiv x v.1, w.1) := he.trans hb
      rw [he₁]
      change ((e₀.linearEquiv x.val (v.1, w.1)).1,
        q.linearEquiv x.val ((e₀.linearEquiv x.val (v.1, w.1)).2, w.2)) = _
      rw [hvalue]
      exact Prod.ext rfl ((q.linearEquiv x.val).apply_symm_apply v.2)
    let j : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let compare (J : FiniteBundle X) :
        Iso (Restrict (J.sum Z).Fiber L) ((J.restrict L).sum ZL).Fiber :=
      (restrictSumIso (E := J.Fiber) (F := Z.Fiber) L).trans
        ((Iso.refl (J.restrict L).Fiber).sum (pullbackTrivialIso j p.size))
    have hcompare (J : FiniteBundle X) (x : L) (v : (J.sum Z).Fiber x.val) :
        (compare J).linearEquiv x v = v := by
      change ((Iso.refl (J.restrict L).Fiber).sum (pullbackTrivialIso j p.size)).linearEquiv x
        ((restrictSumIso (E := J.Fiber) (F := Z.Fiber) L).linearEquiv x v) = v
      rw [restrictSumIso_apply]
      change (v.1, (pullbackTrivialIso j p.size).linearEquiv x v.2) = v
      rw [pullbackTrivialIso_apply]
    have hcompareInv (J : FiniteBundle X) (x : L)
        (v : ((J.restrict L).sum ZL).Fiber x) :
        ((compare J).linearEquiv x).symm v = v := by
      apply ((compare J).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, hcompare]
    let R := a.source.sum Z
    let Q := a.target.sum Z
    let uL : Iso (Restrict R.Fiber L) (Restrict Q.Fiber L) :=
      (compare a.source).trans (e₁.trans (compare a.target).symm)
    let V : Set X := (interior L)ᶜ
    have hV : IsClosed V := isOpen_interior.isClosed_compl
    have hVK : V ⊆ a.datum.controlᶜ := fun _ hx hxK ↦ hx (haL hxK)
    let uV : Iso (Restrict R.Fiber V) (Restrict Q.Fiber V) :=
      (a.datum.boundary.restrict hVK).stabilize Z.Fiber
    have hseam (x : X) (hxL : x ∈ L) (hxV : x ∈ V) :
        uL.linearEquiv ⟨x, hxL⟩ = uV.linearEquiv ⟨x, hxV⟩ := by
      apply LinearEquiv.ext
      intro v
      change ((compare a.target).linearEquiv ⟨x, hxL⟩).symm
        (e₁.linearEquiv ⟨x, hxL⟩ ((compare a.source).linearEquiv ⟨x, hxL⟩ v)) = _
      rw [hcompare, hcompareInv, he₁boundary ⟨⟨x, hxL⟩, hxV⟩]
      have hb := RelativeTriple.sum_apply (a.datum.boundary.restrict hVK)
        (RelativeTriple.identity Z.Fiber V) ⟨x, hxV⟩ v
      have hwin := a.windowBoundary_apply L haL ⟨⟨x, hxL⟩, hxV⟩ v.1
      have hext := Iso.restrictTo_apply a.datum.boundary hVK ⟨x, hxV⟩ v.1
      have hp : ((a.windowBoundary L haL).linearEquiv ⟨⟨x, hxL⟩, hxV⟩ v.1, v.2) =
          ((a.datum.boundary.restrict hVK).linearEquiv ⟨x, hxV⟩ v.1, v.2) :=
        Prod.ext (hwin.trans hext.symm) rfl
      exact hp.trans hb.symm
    -- Paste both directions over the two closed sets, using that same boundary equality.
    let u (x : X) : R.Fiber x ≃ₗ[ℂ] Q.Fiber x :=
      if hx : x ∈ L then uL.linearEquiv ⟨x, hx⟩
      else uV.linearEquiv ⟨x, fun hi ↦ hx (interior_subset hi)⟩
    have huL (x : X) (hx : x ∈ L) : u x = uL.linearEquiv ⟨x, hx⟩ := dite_eq_left hx
    have huV (x : X) (hx : x ∈ V) : u x = uV.linearEquiv ⟨x, hx⟩ := by
      by_cases hxL : x ∈ L
      · exact (huL x hxL).trans (hseam x hxL hx)
      · exact dite_eq_right hxL
    have pasteContinuous (P N : FiniteBundle X)
        (v : ∀ x, P.Fiber x → N.Fiber x)
        (vL : Iso (Restrict P.Fiber L) (Restrict N.Fiber L))
        (vV : Iso (Restrict P.Fiber V) (Restrict N.Fiber V))
        (hvL : ∀ x (hx : x ∈ L) w, v x w = vL.linearEquiv ⟨x, hx⟩ w)
        (hvV : ∀ x (hx : x ∈ V) w, v x w = vV.linearEquiv ⟨x, hx⟩ w) :
        Continuous (fun z : TotalSpace Unit P.Fiber ↦
          (⟨z.proj, v z.proj z.snd⟩ : TotalSpace Unit N.Fiber)) := by
      have onClosed (W : Set X)
          (w : Iso (Restrict P.Fiber W) (Restrict N.Fiber W))
          (hw : ∀ x (hx : x ∈ W) v₀, v x v₀ = w.linearEquiv ⟨x, hx⟩ v₀) :
          ContinuousOn (fun z : TotalSpace Unit P.Fiber ↦
            (⟨z.proj, v z.proj z.snd⟩ : TotalSpace Unit N.Fiber))
            ((π Unit P.Fiber) ⁻¹' W) := by
        rw [continuousOn_iff_continuous_domRestrict]
        let i : C(W, X) := ⟨Subtype.val, continuous_subtype_val⟩
        have hlift : Continuous (fun z : ((π Unit P.Fiber) ⁻¹' W) ↦
            (⟨⟨z.val.proj, z.property⟩, z.val.snd⟩ :
              TotalSpace Unit (Restrict P.Fiber W))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit P.Fiber i).continuous_iff]
          exact (((continuous_proj (E := P.Fiber)).comp continuous_subtype_val).subtype_mk
            (fun z ↦ z.property)).prodMk continuous_subtype_val
        have hmap := (Pullback.continuous_lift Unit N.Fiber i).comp
          (w.continuous_total.comp hlift)
        exact hmap.congr (fun z ↦
          congrArg (fun w : N.Fiber z.val.proj ↦
            (⟨z.val.proj, w⟩ : TotalSpace Unit N.Fiber))
              (hw z.val.proj z.property z.val.snd).symm)
      have hclosedL := hL.isClosed.preimage (continuous_proj (E := P.Fiber))
      have hclosedV := hV.preimage (continuous_proj (E := P.Fiber))
      have hcover : (π Unit P.Fiber) ⁻¹' L ∪ (π Unit P.Fiber) ⁻¹' V = Set.univ := by
        ext z
        simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
        by_cases hz : z.proj ∈ L
        · exact Or.inl hz
        · exact Or.inr (fun hx ↦ hz (interior_subset hx))
      have hc := (onClosed L vL hvL).union_of_isClosed (onClosed V vV hvV) hclosedL hclosedV
      rwa [hcover, continuousOn_univ] at hc
    let e : Iso R.Fiber Q.Fiber :=
      { linearEquiv := u
        continuous_total := pasteContinuous R Q (fun x ↦ u x) uL uV
          (fun x hx w ↦ congrArg (fun t ↦ t w) (huL x hx))
          (fun x hx w ↦ congrArg (fun t ↦ t w) (huV x hx))
        continuous_symm := pasteContinuous Q R (fun x ↦ (u x).symm) uL.symm uV.symm
          (fun x hx w ↦ congrArg (fun t : R.Fiber x ≃ₗ[ℂ] Q.Fiber x ↦ t.symm w) (huL x hx))
          (fun x hx w ↦ congrArg (fun t : R.Fiber x ≃ₗ[ℂ] Q.Fiber x ↦ t.symm w) (huV x hx)) }
    have haL' : a.datum.control ⊆ L := haL.trans interior_subset
    refine ⟨p.size, L, hL, haL', e, ?_⟩
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    change u x.val v = ((a.datum.enlarge L hL haL').boundary.stabilize Z.Fiber).linearEquiv x v
    rw [huV x.val (fun hx ↦ x.property (interior_subset hx))]
    have hl := RelativeTriple.sum_apply (a.datum.boundary.restrict hVK)
      (RelativeTriple.identity Z.Fiber V) ⟨x, fun hx ↦ x.property (interior_subset hx)⟩ v
    have hr := RelativeTriple.sum_apply (a.datum.enlarge L hL haL').boundary
      (RelativeTriple.identity Z.Fiber Lᶜ) x v
    have hp :
        ((a.datum.boundary.restrict hVK).linearEquiv
          ⟨x, fun hx ↦ x.property (interior_subset hx)⟩ v.1, v.2) =
            ((a.datum.enlarge L hL haL').boundary.linearEquiv x v.1, v.2) :=
      by
        have hf : (a.datum.boundary.restrict hVK).linearEquiv
            ⟨x.val, fun hx ↦ x.property (interior_subset hx)⟩ v.1 =
              (a.datum.enlarge L hL haL').boundary.linearEquiv x v.1 := by
          exact (Iso.restrictTo_apply a.datum.boundary hVK
            ⟨x.val, fun hx ↦ x.property (interior_subset hx)⟩ v.1).trans
              (a.datum.enlarge_apply L hL haL' x v.1).symm
        exact Prod.ext hf rfl
    exact hl.trans (hp.trans hr.symm)
  · rintro ⟨n, L, hL, h, e, he⟩
    -- The existing presented-group criterion uses exactly this global extension witness.
    have hk : a.kZeroClass = 0 := a.kZeroClass_eq_zero_iff.mpr
      ⟨FiniteBundle.trivial X n, L, hL, h, e, he⟩
    let Z := FiniteBundle.trivial X 0
    have hs : a.IsStablyIsomorphic (SupportBundleTriple.identity Z) :=
      (a.kZeroClass_eq_iff_stable _).mp (hk.trans (SupportBundleTriple.kZeroClass_identity Z).symm)
    exact (a.compactSupportClass_eq_of_isStablyIsomorphic _ hs).trans
      (SupportBundleTriple.compactSupportClass_identity Z)

/-- The zero criterion also allows an arbitrary global identity stabilizer. -/
theorem SupportBundleTriple.compactSupportClass_eq_zero_iff (a : SupportBundleTriple X) :
    a.compactSupportClass = 0 ↔ ∃ G : FiniteBundle X,
      ∃ L : Set X, ∃ hL : IsCompact L, ∃ h : a.datum.control ⊆ L,
        ∃ e : Iso (a.source.sum G).Fiber (a.target.sum G).Fiber,
          e.restrict Lᶜ = (a.datum.enlarge L hL h).boundary.stabilize G.Fiber := by
  /- A finite trivial stabilizer is one particular global bundle, giving the forward
  implication from the stronger criterion. Any global extension in the converse identifies
  the stabilized germ with identity, so additivity and isomorphism invariance imply zero. -/
  constructor
  · intro ha
    obtain ⟨n, L, hL, h, e, he⟩ := a.compactSupportClass_eq_zero_iff_trivial.mp ha
    exact ⟨FiniteBundle.trivial X n, L, hL, h, e, he⟩
  · intro h
    have hk : a.kZeroClass = 0 := a.kZeroClass_eq_zero_iff.mpr h
    let Z := FiniteBundle.trivial X 0
    have hs : a.IsStablyIsomorphic (SupportBundleTriple.identity Z) :=
      (a.kZeroClass_eq_iff_stable _).mp (hk.trans (SupportBundleTriple.kZeroClass_identity Z).symm)
    exact (a.compactSupportClass_eq_of_isStablyIsomorphic _ hs).trans
      (SupportBundleTriple.compactSupportClass_identity Z)

/-- Descend the actual compact-window class through the explicit presentation. -/
def supportTripleKZeroToCompactSupport : SupportTripleKZero X →+ CompactSupportKZero X :=
  (supportTripleKZero_universal_property X SupportBundleTriple.compactSupportClass
    (fun a b h ↦ a.compactSupportClass_eq_of_isIsomorphic b h)
    SupportBundleTriple.compactSupportClass_sum
    SupportBundleTriple.compactSupportClass_identity).choose

/-- The comparison sends each generator to its specified geometric support class. -/
theorem supportTripleKZeroToCompactSupport_apply (a : SupportBundleTriple X) :
    supportTripleKZeroToCompactSupport a.kZeroClass = a.compactSupportClass := by
  /- The universal-property witness defining the homomorphism includes this equation for every
  original triple generator. Extract that same witness, without choosing a new comparison. -/
  exact (supportTripleKZero_universal_property X SupportBundleTriple.compactSupportClass
    (fun a b h ↦ a.compactSupportClass_eq_of_isIsomorphic b h)
    SupportBundleTriple.compactSupportClass_sum
    SupportBundleTriple.compactSupportClass_identity).choose_spec.1 a

/-- The specified compact-support comparison is injective. -/
theorem supportTripleKZeroToCompactSupport_injective :
    Function.Injective (supportTripleKZeroToCompactSupport (X := X)) := by
  /- Represent any kernel element by one triple. Its constructed class is zero, so the stable
  extension criterion makes its triple-group generator zero. The additive comparison
  therefore has trivial kernel and is injective. -/
  intro x y hxy
  have hzero : supportTripleKZeroToCompactSupport (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, ha⟩ := supportBundleTriple_kZeroClass_surjective (x - y)
  have hac : a.compactSupportClass = 0 := by
    rw [← supportTripleKZeroToCompactSupport_apply, ha]
    exact hzero
  have hak : a.kZeroClass = 0 :=
    a.kZeroClass_eq_zero_iff.mpr (a.compactSupportClass_eq_zero_iff.mp hac)
  exact sub_eq_zero.mp (ha.symm.trans hak)

set_option maxHeartbeats 6000000 in

set_option backward.isDefEq.respectTransparency false in
/-- Every compactification class is the actual difference of a support triple. -/
theorem supportTripleKZeroToCompactSupport_surjective :
    Function.Surjective (supportTripleKZeroToCompactSupport (X := X)) := by
  /- Regard the given reduced class as a singleton-relative class on the compactification.
  KA II.4.22(a) represents it on a closed infinity neighborhood, and the compact-pair triple
  comparison supplies its two actual bundles and boundary isomorphism there. Restrict those
  particular bundles to X, choose the compact exterior control from that same neighborhood,
  and form a support triple. Naturality and the exact window quotient square recover the
  original reduced class. This constructs representatives; it does not extend arbitrary
  bundles from X. -/
  classical
  intro z
  -- Represent this very reduced class on a closed neighborhood of infinity.
  obtain ⟨b, hb⟩ := relativeKZeroPointToReduced_surjective (∞ : OnePoint X) z
  obtain ⟨S, hS, hSN, c, hc⟩ := exists_relativeKZero_neighborhood (∞ : OnePoint X) b
  obtain ⟨t, ht⟩ := bundleTriple_relativeClass_surjective S hS c
  obtain ⟨K, ⟨hKclosed, hK⟩, hKS⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hSN
  let jX : C(X, OnePoint X) := ⟨fun x ↦ (x : OnePoint X), OnePoint.continuous_coe⟩
  have hKoutside : Kᶜ ⊆ jX ⁻¹' S := fun x hx ↦ hKS (Or.inl ⟨x, hx, rfl⟩)
  -- Restrict the specified compactification bundles; no bundle on X is extended to infinity.
  let E := t.source.pullback jX
  let F := t.target.pullback jX
  let a : SupportBundleTriple X := SupportBundleTriple.ofBoundary E F
    { control := K
      isCompact_control := hK
      boundary := (t.boundary.pullback jX).restrict hKoutside }
  let L := supportNeighborhood K hK
  have hL : IsCompact L := isCompact_supportNeighborhood _ _
  have haL : a.datum.control ⊆ interior L := subset_interior_supportNeighborhood _ _
  let := isCompact_iff_compactSpace.mp hL
  let jL : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let fL : C(L, OnePoint X) := jX.comp jL
  let C : Set L := fL ⁻¹' S
  have hC : IsClosed C := hS.preimage fL.continuous
  have hBC : supportWindowBoundary L ⊆ C := by
    intro x hx
    have hxK : x.val ∉ K := fun hxK ↦ hx (haL hxK)
    exact hKoutside hxK
  -- Restrict the original clutching class to a smaller closed boundary.
  have changePair {A B : Set L} (hA : IsClosed A) (hB : IsClosed B) (hBA : B ⊆ A)
      (a : BundleTriple A) :
      (BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)).relativeClass hB =
        relativeKZeroEnlarge B A hB hA hBA (a.relativeClass hA) := by
    let b := BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)
    let := DoubleSpace.t2Space A hA
    let := DoubleSpace.t2Space B hB
    let Wa := clutchingBundle hA a
    let d := DoubleSpace.mapContinuous B A (ContinuousMap.id L) hBA
    let W := Wa.pullback d
    -- The two original charts pull back along the identity on each copy of L.
    let eL : Iso ((DoubleSpace.leftMap B : L → DoubleSpace B) *ᵖ W.Fiber) a.source.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).trans
        (clutchingLeftIso hA a)
    let eR : Iso ((DoubleSpace.rightMap B : L → DoubleSpace B) *ᵖ W.Fiber) a.target.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).trans
        (clutchingRightIso hA a)
    have heL (x : L) (v : Wa.Fiber (DoubleSpace.left A x)) :
        eL.linearEquiv x v = (clutchingLeftIso hA a).linearEquiv x v := by
      change (clutchingLeftIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have heR (x : L) (v : Wa.Fiber (DoubleSpace.right A x)) :
        eR.linearEquiv x v = (clutchingRightIso hA a).linearEquiv x v := by
      change (clutchingRightIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have hinv (x : L) (v : a.source.Fiber x) :
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
          (relativeKZeroPullback B hB A hA (ContinuousMap.id L) hBA).comp
            (relativeKZeroPullback A hA RA hRA (DoubleSpace.leftMap A)
              (DoubleSpace.left_mapsTo A))
      have hleft := relativeKZeroPullback_comp B hB RB hRB RA hRA
        (DoubleSpace.leftMap B) d (DoubleSpace.left_mapsTo B) hd
      have hright := relativeKZeroPullback_comp B hB A hA RA hRA
        (ContinuousMap.id L) (DoubleSpace.leftMap A) hBA (DoubleSpace.left_mapsTo A)
      rw [← hleft, ← hright]
      congr 1
    change DoubleSpace.relativeRestriction B hB (b.differenceLift hB) =
      relativeKZeroEnlarge B A hB hA hBA
        (DoubleSpace.relativeRestriction A hA (a.differenceLift hA))
    rw [hlift]
    exact DFunLike.congr_fun hrestriction (a.differenceLift hA)
  let u := t.pullback fL
  let v := BundleTriple.ofBoundary u.source u.target (u.boundary.restrict hBC)
  have hcompare : (a.windowTriple L haL).IsIsomorphic v := by
    let e := pullbackCompIso (E := t.source.Fiber) jX jL
    let d := pullbackCompIso (E := t.target.Fiber) jX jL
    refine ⟨e, d, ?_⟩
    intro x w
    have hleft := a.windowBoundary_apply L haL x w
    have hp := Iso.restrictTo_apply (t.boundary.pullback jX) hKoutside
      ⟨x.val.val, fun hxK ↦ x.property (haL hxK)⟩ w
    have hq := RelativeTriple.pullback_apply t.boundary jX
      ⟨x.val.val, hKoutside (fun hxK ↦ x.property (haL hxK))⟩ w
    have hr := Iso.restrictTo_apply u.boundary hBC x w
    have hs := RelativeTriple.pullback_apply t.boundary fL
      ⟨x.val, hBC x.property⟩ w
    change d.linearEquiv x.val ((a.windowBoundary L haL).linearEquiv x w) =
      (u.boundary.restrict hBC).linearEquiv x (e.linearEquiv x.val w)
    rw [pullbackCompIso_apply, pullbackCompIso_apply]
    exact (hleft.trans (hp.trans hq)).trans (hr.trans hs).symm
  have hwindowRelative : BundleTriple.relativeClass.{_, 0}
      (isClosed_supportWindowBoundary L) (a.windowTriple L haL) =
        relativeKZeroPullback (supportWindowBoundary L)
          (isClosed_supportWindowBoundary L) S hS fL hBC c := by
    rw [BundleTriple.relativeClass_eq_of_isIsomorphic
      (isClosed_supportWindowBoundary L) (a.windowTriple L haL) v hcompare]
    change BundleTriple.relativeClass (isClosed_supportWindowBoundary L)
      (BundleTriple.ofBoundary u.source u.target (u.boundary.restrict hBC)) = _
    rw [changePair hC (isClosed_supportWindowBoundary L) hBC u,
      BundleTriple.relativeClass_pullback hS t fL, ht]
    have hcomp := DFunLike.congr_fun
      (relativeKZeroPullback_comp (supportWindowBoundary L)
        (isClosed_supportWindowBoundary L) C hC S hS (ContinuousMap.id L) fL hBC
        (fun _ hx ↦ hx)) c
    exact hcomp.symm
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
  let k := PointedQuotient.mapContinuous (supportWindowBoundary L) S fL hBC
  have hsquare : k.comp (wMap L hL) =
      (⟨PointedQuotient.of S, PointedQuotient.continuous_of S⟩ : C(_, _)) := by
    ext x
    cases x using OnePoint.rec with
    | infty =>
      change k (wMap L hL ∞) = PointedQuotient.of S ∞
      rw [hmapInfinity L hL]
      exact ((PointedQuotient.of_eq_basepoint_iff S ∞).mpr (mem_of_mem_nhds hSN)).symm
    | coe x =>
      change k (wMap L hL (x : OnePoint X)) = PointedQuotient.of S (x : OnePoint X)
      by_cases hx : x ∈ interior L
      · rw [hmapMem L hL x hx]
        rfl
      · rw [hmapNotMem L hL x hx]
        have hxK : x ∉ K := fun hxK ↦ hx (haL hxK)
        exact ((PointedQuotient.of_eq_basepoint_iff S (x : OnePoint X)).mpr
          (hKoutside hxK)).symm
  have haClass : a.compactSupportClass.val = relativeKZeroForget S hS c := by
    let := PointedQuotient.t2Space S hS
    let := PointedQuotient.t2Space (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
    rw [a.compactSupportClass_eq_windowClass L hL haL, hwindow L hL haL, hwindowRelative]
    change complexKZeroPullback (wMap L hL) (complexKZeroPullback k c.val) =
      complexKZeroPullback ⟨PointedQuotient.of S, PointedQuotient.continuous_of S⟩ c.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
  have hcforget : relativeKZeroForget S hS c = z.val := by
    have hmap := DFunLike.congr_fun
      (relativeKZeroForget_enlarge ({∞} : Set (OnePoint X)) S isClosed_singleton hS
        (singleton_subset_of_mem_nhds ∞ S hSN)) c
    change relativeKZeroForget {∞} isClosed_singleton
      (relativeKZeroNeighborhoodToPoint ∞ S hS hSN c) = relativeKZeroForget S hS c at hmap
    have hbval := congrArg Subtype.val hb
    change relativeKZeroForget {∞} isClosed_singleton b = z.val at hbval
    exact hmap.symm.trans ((congrArg (relativeKZeroForget {∞} isClosed_singleton) hc).trans hbval)
  -- The named forward homomorphism carries the very representative just constructed to z.
  refine ⟨a.kZeroClass, ?_⟩
  rw [supportTripleKZeroToCompactSupport_apply]
  exact Subtype.ext (haClass.trans hcforget)

/-- SG I.9.26 in degree zero: the specified comparison is bijective. -/
theorem supportTripleKZeroToCompactSupport_bijective :
    Function.Bijective (supportTripleKZeroToCompactSupport (X := X)) := by
  /- Combine the injectivity from the finite-window extension criterion and surjectivity from
  reduced compactification bundles. Both refer to the same generator-wise constructed
  homomorphism. -/
  exact ⟨supportTripleKZeroToCompactSupport_injective,
    supportTripleKZeroToCompactSupport_surjective⟩

/-- Identify the models through the actual compact-window forward map. -/
def supportTripleKZeroCompactSupportEquiv : SupportTripleKZero X ≃+ CompactSupportKZero X :=
  AddEquiv.ofBijective _ supportTripleKZeroToCompactSupport_bijective

/-- The additive equivalence preserves the specified generator formula. -/
theorem supportTripleKZeroCompactSupportEquiv_apply (a : SupportBundleTriple X) :
    supportTripleKZeroCompactSupportEquiv a.kZeroClass = a.compactSupportClass := by
  /- The equivalence uses the original homomorphism as its forward function. Evaluate its
  already specified generator formula. -/
  exact supportTripleKZeroToCompactSupport_apply a

/-- The inverse equivalence recovers the same original triple class. -/
theorem supportTripleKZeroCompactSupportEquiv_symm_apply (a : SupportBundleTriple X) :
    supportTripleKZeroCompactSupportEquiv.symm a.compactSupportClass = a.kZeroClass := by
  /- The forward equivalence sends this generator to its constructed class. Apply the inverse
  function and use its left inverse law. -/
  apply supportTripleKZeroCompactSupportEquiv.injective
  rw [AddEquiv.apply_symm_apply, supportTripleKZeroCompactSupportEquiv_apply]

/-- Equality of geometric support classes is exactly stable isomorphism at infinity. -/
theorem SupportBundleTriple.compactSupportClass_eq_iff_stable (a b : SupportBundleTriple X) :
    a.compactSupportClass = b.compactSupportClass ↔ a.IsStablyIsomorphic b := by
  /- Comparison injectivity identifies equality of the constructed classes with equality of
  their presented-group generators. The latter is exactly stable isomorphism of germs by the
  cutoff-based stable quotient comparison. -/
  constructor
  · intro h
    apply (a.kZeroClass_eq_iff_stable b).mp
    apply supportTripleKZeroToCompactSupport_injective
    simpa only [supportTripleKZeroToCompactSupport_apply] using h
  · exact a.compactSupportClass_eq_of_isStablyIsomorphic b

/-- The original geometric support-class function is surjective. -/
theorem supportBundleTriple_compactSupportClass_surjective :
    Function.Surjective (SupportBundleTriple.compactSupportClass (X := X)) := by
  /- Lift a compact-support class through the surjective group comparison, represent the lift
  by one triple, and apply the comparison generator formula. -/
  intro z
  obtain ⟨x, hx⟩ := supportTripleKZeroToCompactSupport_surjective z
  obtain ⟨a, ha⟩ := supportBundleTriple_kZeroClass_surjective x
  refine ⟨a, ?_⟩
  rw [← supportTripleKZeroToCompactSupport_apply, ha, hx]

/-- Stable support classes map by the same constructed geometric class. -/
def stableSupportTripleClassToCompactSupport :
    StableSupportTripleClass X → CompactSupportKZero X :=
  Quotient.lift SupportBundleTriple.compactSupportClass
    (fun a b h ↦ a.compactSupportClass_eq_of_isStablyIsomorphic b h)

/-- The stable-class map keeps the original support class of each representative. -/
theorem stableSupportTripleClassToCompactSupport_apply (a : SupportBundleTriple X) :
    stableSupportTripleClassToCompactSupport a.stableClass = a.compactSupportClass := by
  /- Quotient evaluation of the actual lift on this representative returns its original
  compact-window class. The quotient proof only establishes representative independence. -/
  rfl

/-- The stable support-class map is bijective. -/
theorem stableSupportTripleClassToCompactSupport_bijective :
    Function.Bijective (stableSupportTripleClassToCompactSupport (X := X)) := by
  /- The exact stable-equality criterion gives injectivity on the quotient, and single-triple
  representation of all compact-support classes gives surjectivity. -/
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b h
    exact (a.stableClass_eq_iff b).mpr ((a.compactSupportClass_eq_iff_stable b).mp h)
  · intro z
    obtain ⟨a, ha⟩ := supportBundleTriple_compactSupportClass_surjective z
    exact ⟨a.stableClass, ha⟩

/-- Identify stable geometric support classes with K of the compactification. -/
def stableSupportTripleClassCompactSupportEquiv :
    StableSupportTripleClass X ≃ CompactSupportKZero X :=
  Equiv.ofBijective _ stableSupportTripleClassToCompactSupport_bijective

set_option linter.unusedSectionVars false in
/-- The compact-base comparison retains the ordinary difference of the original bundles. -/
theorem supportTripleKZeroToCompactSupport_toAbsolute [CompactSpace X] (a : SupportBundleTriple X) :
    compactSupportKZeroToAbsolute (supportTripleKZeroToCompactSupport a.kZeroClass) =
      a.source.kZeroClass - a.target.kZeroClass := by
  /- Evaluate the comparison on its generator, then use the compact-base normalization of the
  constructed support class. The formula concerns the original source and target bundle
  classes. -/
  rw [supportTripleKZeroToCompactSupport_apply, SupportBundleTriple.compactSupportClass_toAbsolute]

end AtiyahSinger.ComplexBundle

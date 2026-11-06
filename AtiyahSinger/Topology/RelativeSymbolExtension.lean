/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.OpenEmbeddingKZero
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Open extension of the actual compact-support symbol class

Public module ID: M2097.

the topological content of SG III.13.4, equation (13.10), stated for the
underlying compact-support triples. An ambient triple has its entire control
inside the open image, and its original boundary agrees with the source boundary
through two specified bundle isomorphisms. Compact-window excision then computes
the ambient class as the specified covariant open extension.

The ambient boundary itself supplies the exterior gluing data. No assertion that
an arbitrary bundle extends across an open embedding is made. Exterior identity
frames in SG (13.9) provide one construction satisfying these hypotheses; literal
identity in chosen coordinates is not required for this more general excision
statement. No properness, global rank bound, or finite CW hypothesis is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  {G : Y → Type*} [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
  [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
  {H : Y → Type*} [∀ y, AddCommGroup (H y)] [∀ y, Module ℂ (H y)]
  [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]

/-- Compact-support excision retains the specified source and ambient boundary maps. -/
theorem CompactSupportTriple.compactSupportClass_eq_openPushforward
    (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (hcontrol : b.control ⊆ f '' a.control)
    (eE : Iso E ((f : X → Y) *ᵖ G)) (eF : Iso F ((f : X → Y) *ᵖ H))
    (hboundary : ∀ (x : X) (hx : x ∉ a.control) (hy : f x ∉ b.control) (v : E x),
      eF.linearEquiv x (a.boundary.linearEquiv ⟨x, hx⟩ v) =
        b.boundary.linearEquiv ⟨f x, hy⟩ (eE.linearEquiv x v)) :
    b.compactSupportClass = compactSupportKZeroOpenPushforward f hf a.compactSupportClass := by
  /- Stage 1: choose one compact window L in X with a.control inside its interior.
  Its image is compact and has interior f '' interior L because f is an open
  embedding. The inclusion hcontrol places b.control inside this same interior.
  Injectivity and hcontrol ensure that f x is outside b.control whenever x is
  outside a.control; thus the boundary comparison is not vacuous there.
  Stage 2: restrict eE and eF to L. On its window boundary the stated square
  identifies the actual source triple with the pullback of the ambient window
  triple on f '' L. Invariance of the relative difference under this square,
  including its boundary trivialization, identifies their relative classes.
  Stage 3: transport through the homeomorphism from L onto its image. Compose
  the associated open extensions with the original compact-window comparison.
  The ambient class is therefore the specified open pushforward of a's class.
  The existing ambient boundary trivializes everything outside the image
  window. No bundle extension is invented, and no Kc pullback along the
  generally nonproper open embedding is used. -/
  classical
  let t := b.toSupportBundleTriple
  let e := eE.trans ((smallBundleIso G).pullback f)
  let w := eF.trans ((smallBundleIso H).pullback f)
  let s := SupportBundleTriple.ofBoundary (t.source.pullback f) (t.target.pullback f)
    (a.congr e w)
  have hmodel : a.compactSupportClass = s.compactSupportClass :=
    a.compactSupportClass_eq_model (t.source.pullback f) (t.target.pullback f) e w
  have hboundarySmall (x : X) (hx : x ∉ a.control) (hy : f x ∉ b.control)
      (v : t.source.Fiber (f x)) :
      s.datum.boundary.linearEquiv ⟨x, hx⟩ v =
        t.datum.boundary.linearEquiv ⟨f x, hy⟩ v := by
    change (smallBundle G).Fiber (f x) at v
    let v₀ := e.symm.linearEquiv x v
    have hsource : eE.linearEquiv x v₀ = (smallBundleIso G).symm.linearEquiv (f x) v := by
      apply ((smallBundleIso G).linearEquiv (f x)).injective
      change e.linearEquiv x v₀ =
        (smallBundleIso G).linearEquiv (f x) ((smallBundleIso G).symm.linearEquiv (f x) v)
      exact ((e.linearEquiv x).apply_symm_apply v).trans
        (((smallBundleIso G).linearEquiv (f x)).apply_symm_apply v).symm
    change (smallBundleIso H).linearEquiv (f x)
      (eF.linearEquiv x (a.boundary.linearEquiv ⟨x, hx⟩ v₀)) =
        (smallBundleIso H).linearEquiv (f x)
          (b.boundary.linearEquiv ⟨f x, hy⟩ ((smallBundleIso G).symm.linearEquiv (f x) v))
    exact congrArg ((smallBundleIso H).linearEquiv (f x))
      ((hboundary x hx hy v₀).trans (congrArg (b.boundary.linearEquiv ⟨f x, hy⟩) hsource))
  -- Choose the same compact neighborhood before taking its image under the open embedding.
  let L := supportNeighborhood a.control a.isCompact_control
  have hL : IsCompact L := isCompact_supportNeighborhood a.control a.isCompact_control
  have hsL : s.datum.control ⊆ interior L :=
    subset_interior_supportNeighborhood a.control a.isCompact_control
  let M := f '' L
  have hM : IsCompact M := hL.image f.continuous
  have hinterior : f ⁻¹' interior M = interior L := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage f.continuous]
    congr 1
    exact hf.injective.preimage_image L
  have hmem (x : X) : f x ∈ interior M ↔ x ∈ interior L := by
    change x ∈ f ⁻¹' interior M ↔ x ∈ interior L
    rw [hinterior]
  have htM : t.datum.control ⊆ interior M := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcontrol hy
    exact (hmem x).mpr (hsL hx)
  let := isCompact_iff_compactSpace.mp hL
  let := isCompact_iff_compactSpace.mp hM
  let iL : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iM : C(M, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(L, M) := ⟨fun x ↦ ⟨f x, ⟨x, x.property, rfl⟩⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hpre : g ⁻¹' supportWindowBoundary M = supportWindowBoundary L := by
    ext x
    change (f x ∉ interior M) ↔ (x : X) ∉ interior L
    exact not_congr (hmem x)
  have hpair : Set.MapsTo g (supportWindowBoundary L) (supportWindowBoundary M) := by
    intro x hx hfx
    exact hx ((hmem x).mp hfx)
  let := PointedQuotient.t2Space (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
  let := PointedQuotient.t2Space (supportWindowBoundary M) (isClosed_supportWindowBoundary M)
  let dL := BundleTriple.relativeClass.{_, 0} (isClosed_supportWindowBoundary L)
    (s.windowTriple L hsL)
  let dM := BundleTriple.relativeClass.{_, 0} (isClosed_supportWindowBoundary M)
    (t.windowTriple M htM)
  let qg := PointedQuotient.mapContinuous (supportWindowBoundary L)
    (supportWindowBoundary M) g hpair
  -- Compare iterated pullbacks by vector-preserving maps, with their original topologies.
  let coord (U : FiniteBundle Y) :
      Iso ((U.pullback f).restrict L).Fiber ((g : L → M) *ᵖ (U.restrict M).Fiber) :=
    (pullbackCompIso (E := U.Fiber) f iL).trans
      (pullbackCompIso (E := U.Fiber) iM g).symm
  have hcoord (U : FiniteBundle Y) (x : L) (v : U.Fiber (f x)) :
      (coord U).linearEquiv x v = v := by
    change ((pullbackCompIso (E := U.Fiber) iM g).linearEquiv x).symm
      ((pullbackCompIso (E := U.Fiber) f iL).linearEquiv x v) = v
    apply ((pullbackCompIso (E := U.Fiber) iM g).linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  -- Generalizing only the pair index makes equality transport explicit and local.
  have windowNaturality (C : Set L) (hC : IsClosed C)
      (hmap : Set.MapsTo g C (supportWindowBoundary M))
      (hCeq : C = g ⁻¹' supportWindowBoundary M) (u : BundleTriple C)
      (eS : Iso u.source.Fiber ((g : L → M) *ᵖ (t.source.restrict M).Fiber))
      (eT : Iso u.target.Fiber ((g : L → M) *ᵖ (t.target.restrict M).Fiber))
      (hsquare : ∀ (x : C) (v : u.source.Fiber x.val),
        eT.linearEquiv x.val (u.boundary.linearEquiv x v) =
          (t.windowBoundary M htM).linearEquiv ⟨g x.val, hmap x.property⟩
            (eS.linearEquiv x.val v)) :
      u.relativeClass hC = relativeKZeroPullback C hC (supportWindowBoundary M)
        (isClosed_supportWindowBoundary M) g hmap dM := by
    subst C
    have hi : u.IsIsomorphic ((t.windowTriple M htM).pullback g) := by
      refine ⟨eS, eT, ?_⟩
      intro x v
      exact (hsquare x v).trans
        (RelativeTriple.pullback_apply (t.windowBoundary M htM) g x
          (eS.linearEquiv x.val v)).symm
    exact (u.relativeClass_eq_of_isIsomorphic hC _ hi).trans
      ((t.windowTriple M htM).relativeClass_pullback (isClosed_supportWindowBoundary M) g)
  have hrelative : dL.val = complexKZeroPullback qg dM.val := by
    have hsquare (x : supportWindowBoundary L) (v : (s.source.restrict L).Fiber x.val) :
        (coord t.target).linearEquiv x.val ((s.windowBoundary L hsL).linearEquiv x v) =
          (t.windowBoundary M htM).linearEquiv ⟨g x.val, hpair x.property⟩
            ((coord t.source).linearEquiv x.val v) := by
      erw [hcoord, hcoord, s.windowBoundary_apply L hsL,
        t.windowBoundary_apply M htM]
      exact hboundarySmall x.val.val _ _ v
    have hc := windowNaturality (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
      hpair hpre.symm (s.windowTriple L hsL) (coord t.source) (coord t.target) hsquare
    exact congrArg Subtype.val hc
  -- Realize both window classes by their actual pointed collapse maps.
  let := (isClosed_supportWindowBoundary L).isOpen_compl.locallyCompactSpace
  let := (isClosed_supportWindowBoundary M).isOpen_compl.locallyCompactSpace
  let := (isOpen_interior (s := L)).locallyCompactSpace
  let := (isOpen_interior (s := M)).locallyCompactSpace
  let eL := supportWindowInteriorHomeomorph L
  let eM := supportWindowInteriorHomeomorph M
  let qL := PointedQuotient.onePointHomeomorph.{_, 0}
    (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
  let qM := PointedQuotient.onePointHomeomorph.{_, 0}
    (supportWindowBoundary M) (isClosed_supportWindowBoundary M)
  let cL : C(OnePoint X, OnePoint (interior L)) :=
    ⟨onePointCollapse (interior L), continuous_onePointCollapse (interior L) isOpen_interior⟩
  let cM : C(OnePoint Y, OnePoint (interior M)) :=
    ⟨onePointCollapse (interior M), continuous_onePointCollapse (interior M) isOpen_interior⟩
  let rL := properOnePointMap ⟨eL.symm, eL.symm.continuous⟩ eL.symm.isProperMap
  let rM := properOnePointMap ⟨eM.symm, eM.symm.continuous⟩ eM.symm.isProperMap
  let wL : C(OnePoint X, PointedQuotient.{_, 0} (supportWindowBoundary L)) :=
    (⟨qL.symm, qL.symm.continuous⟩ : C(_, _)).comp (rL.comp cL)
  let wM : C(OnePoint Y, PointedQuotient.{_, 0} (supportWindowBoundary M)) :=
    (⟨qM.symm, qM.symm.continuous⟩ : C(_, _)).comp (rM.comp cM)
  have hwLInfinity : wL OnePoint.infty = PointedQuotient.basepoint (supportWindowBoundary L) := by
    exact PointedQuotient.onePointHomeomorph_symm_infty
      (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
  have hwMInfinity : wM OnePoint.infty = PointedQuotient.basepoint (supportWindowBoundary M) := by
    exact PointedQuotient.onePointHomeomorph_symm_infty
      (supportWindowBoundary M) (isClosed_supportWindowBoundary M)
  have hwLMem (x : X) (hx : x ∈ interior L) :
      wL (x : OnePoint X) =
        PointedQuotient.of (supportWindowBoundary L) ⟨x, interior_subset hx⟩ := by
    change qL.symm (OnePoint.map eL.symm
      (onePointCollapse (interior L) (x : OnePoint X))) = _
    rw [onePointCollapse_coe_of_mem (interior L) x hx]
    exact qL.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of (supportWindowBoundary L)
        (isClosed_supportWindowBoundary L) (eL.symm ⟨x, hx⟩)).symm
  have hwMMem (y : Y) (hy : y ∈ interior M) :
      wM (y : OnePoint Y) =
        PointedQuotient.of (supportWindowBoundary M) ⟨y, interior_subset hy⟩ := by
    change qM.symm (OnePoint.map eM.symm
      (onePointCollapse (interior M) (y : OnePoint Y))) = _
    rw [onePointCollapse_coe_of_mem (interior M) y hy]
    exact qM.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of (supportWindowBoundary M)
        (isClosed_supportWindowBoundary M) (eM.symm ⟨y, hy⟩)).symm
  have hwLNotMem (x : X) (hx : x ∉ interior L) :
      wL (x : OnePoint X) = PointedQuotient.basepoint (supportWindowBoundary L) := by
    change qL.symm (OnePoint.map eL.symm
      (onePointCollapse (interior L) (x : OnePoint X))) = _
    rw [onePointCollapse_coe_of_notMem (interior L) x hx]
    exact PointedQuotient.onePointHomeomorph_symm_infty
      (supportWindowBoundary L) (isClosed_supportWindowBoundary L)
  have hwMNotMem (y : Y) (hy : y ∉ interior M) :
      wM (y : OnePoint Y) = PointedQuotient.basepoint (supportWindowBoundary M) := by
    change qM.symm (OnePoint.map eM.symm
      (onePointCollapse (interior M) (y : OnePoint Y))) = _
    rw [onePointCollapse_coe_of_notMem (interior M) y hy]
    exact PointedQuotient.onePointHomeomorph_symm_infty
      (supportWindowBoundary M) (isClosed_supportWindowBoundary M)
  have hsClass : s.compactSupportClass.val = complexKZeroPullback wL dL.val := by
    rw [s.compactSupportClass_eq_windowClass L hL hsL]
    change complexKZeroPullback cL
      (complexKZeroPullback rL (complexKZeroPullback ⟨qL.symm, qL.symm.continuous⟩ _)) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  have htClass : t.compactSupportClass.val = complexKZeroPullback wM dM.val := by
    rw [t.compactSupportClass_eq_windowClass M hM htM]
    change complexKZeroPullback cM
      (complexKZeroPullback rM (complexKZeroPullback ⟨qM.symm, qM.symm.continuous⟩ _)) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  -- The open pushforward collapses outside the same image and then uses its exact inverse.
  let := hf.isOpen_range.locallyCompactSpace
  let ef := hf.isEmbedding.toHomeomorph
  let ifn : C(Set.range f, X) := ⟨ef.symm, ef.symm.continuous⟩
  let c : C(OnePoint Y, OnePoint X) :=
    (properOnePointMap ifn ef.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
  have hc (x : X) : c (f x) = (x : OnePoint X) := by
    change OnePoint.map ifn (onePointCollapse (Set.range f) (f x)) = (x : OnePoint X)
    rw [onePointCollapse_coe_of_mem (Set.range f) (f x) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  have hqInfinity : qg (PointedQuotient.basepoint (supportWindowBoundary L)) =
      PointedQuotient.basepoint (supportWindowBoundary M) :=
    PointedQuotient.map_basepoint (supportWindowBoundary L) (supportWindowBoundary M) g hpair
  have hsquare : qg.comp (wL.comp c) = wM := by
    ext z
    cases z using OnePoint.rec with
    | infty =>
      change qg (wL OnePoint.infty) = wM OnePoint.infty
      rw [hwLInfinity, hwMInfinity, hqInfinity]
    | coe y =>
      by_cases hy : y ∈ Set.range f
      · obtain ⟨x, rfl⟩ := hy
        change qg (wL (c (f x))) = wM (f x)
        rw [hc]
        by_cases hx : x ∈ interior L
        · rw [hwLMem x hx, hwMMem (f x) ((hmem x).mpr hx)]
          rfl
        · rw [hwLNotMem x hx, hwMNotMem (f x) (mt (hmem x).mp hx), hqInfinity]
      · have hyM : y ∉ interior M := by
          intro hyM
          obtain ⟨x, _, hxy⟩ := interior_subset hyM
          exact hy ⟨x, hxy⟩
        change qg (wL (OnePoint.map ifn (onePointCollapse (Set.range f) y))) = wM y
        rw [onePointCollapse_coe_of_notMem _ _ hy, OnePoint.map_infty,
          hwLInfinity, hwMNotMem y hyM, hqInfinity]
  -- Pullback along that pointed square identifies the original compact-support classes.
  change t.compactSupportClass = compactSupportKZeroOpenPushforward f hf a.compactSupportClass
  rw [hmodel]
  apply Subtype.ext
  change t.compactSupportClass.val = complexKZeroPullback
    ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
    (complexKZeroPullback (properOnePointMap ifn ef.symm.isProperMap) s.compactSupportClass.val)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  calc
    t.compactSupportClass.val = complexKZeroPullback wM dM.val := htClass
    _ = complexKZeroPullback (qg.comp (wL.comp c)) dM.val := by rw [hsquare]
    _ = complexKZeroPullback c
        (complexKZeroPullback wL (complexKZeroPullback qg dM.val)) := by
      simp only [complexKZeroPullback_comp, AddMonoidHom.comp_apply]
    _ = complexKZeroPullback c s.compactSupportClass.val := by
      rw [← hrelative, ← hsClass]

end AtiyahSinger.ComplexBundle

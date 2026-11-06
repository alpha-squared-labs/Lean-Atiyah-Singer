/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTotalPullback
public import AtiyahSinger.Topology.HermitianMetricPullback
public import AtiyahSinger.Topology.HermitianSupportedThom
public import AtiyahSinger.Topology.OpenEmbeddingKZero
public import AtiyahSinger.Topology.RelativeSymbolExtension

/-!
# Supported Thom maps commute with open extension

Public module ID: M2251.

For an actual open embedding f and a complex bundle E on its target, the
pullback total map sends `(x,v)` to `(f(x),v)`. Both horizontal arrows are
the existing covariant open pushforwards; both vertical arrows are the
previously specified supported tensor Thom maps. The pulled-back Hermitian
form evaluates the original form on those same vectors.

This is the standard open-excision naturality of the construction in SG C.1,
C.13 and III.12. KA IV.1.3's proof, printed pp.181--182 / PDF pp.198--199,
explicitly uses the open-extension Thom square; IV.1.10--1.11 supplies its
noncompact supported operator. The exact formula below is the corresponding
project interface, not a separately numbered source theorem. It applies to
locally compact Hausdorff bases and
given continuous metrics, without requiring the open embedding to be proper
or extending arbitrary input bundles across its image boundary.
Every compact-support class is proved to admit source and ambient representatives
with exactly compatible boundary maps. A common cutoff supported in the open image
proves the displayed square for the actual Thom operators.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle OnePoint Topology

attribute [local instance] isFiniteRank_pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every compact-support class has representatives compatible with a specified open embedding.
This constructs both representatives from compactification data, without extending an arbitrary
bundle already given on the source. -/
theorem exists_supportBundleTriple_openExtension (z : CompactSupportKZero X)
    (f : C(X, Y)) (hf : IsOpenEmbedding f) :
    ∃ b : SupportBundleTriple Y,
      ∃ a : CompactSupportTriple (f *ᵖ b.source.Fiber) (f *ᵖ b.target.Fiber),
        a.compactSupportClass = z ∧ b.datum.control ⊆ f '' a.control ∧
          ∀ (x : X) (hx : x ∉ a.control) (hy : f x ∉ b.datum.control)
            (v : b.source.Fiber (f x)),
            a.boundary.linearEquiv ⟨x, hx⟩ v = b.datum.boundary.linearEquiv ⟨f x, hy⟩ v := by
  /- Choose the actual relative class and its bundles on the one-point compactification.
  The open collapse pulls those bundles back to the target, and a single compact control
  supplies both boundary maps. Identify the source class using excision into its own
  compactification and the compact-base source-minus-target formula. -/
  classical
  obtain ⟨ap, hap⟩ := relativeKZeroPointToReduced_surjective.{_, 0} (∞ : OnePoint X) z
  obtain ⟨S, hS, hN, c, hc⟩ := exists_relativeKZero_neighborhood (∞ : OnePoint X) ap
  obtain ⟨t, ht⟩ := bundleTriple_relativeClass_surjective S hS c
  obtain ⟨K, ⟨_, hK⟩, hKS⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hN
  let jX : C(X, OnePoint X) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  have hKoutside : Kᶜ ⊆ jX ⁻¹' S := fun x hx ↦ hKS (Or.inl ⟨x, hx, rfl⟩)
  have hforget : t.source.kZeroClass - t.target.kZeroClass = z.val := by
    have hcforget : relativeKZeroForget S hS c = z.val := by
      have hmap := DFunLike.congr_fun
        (relativeKZeroForget_enlarge ({∞} : Set (OnePoint X)) S isClosed_singleton hS
          (singleton_subset_of_mem_nhds ∞ S hN)) c
      change relativeKZeroForget {∞} isClosed_singleton
        (relativeKZeroNeighborhoodToPoint ∞ S hS hN c) = relativeKZeroForget S hS c at hmap
      have hapval := congrArg Subtype.val hap
      change relativeKZeroForget {∞} isClosed_singleton ap = z.val at hapval
      exact hmap.symm.trans
        ((congrArg (relativeKZeroForget {∞} isClosed_singleton) hc).trans hapval)
    rw [← ht] at hcforget
    exact (t.relativeClass_forget hS).symm.trans hcforget
  -- The source representative retains the original compactification bundles and boundary.
  let a₀ : SupportBundleTriple X := SupportBundleTriple.ofBoundary
    (t.source.pullback jX) (t.target.pullback jX)
    { control := K
      isCompact_control := hK
      boundary := (t.boundary.pullback jX).restrict hKoutside }
  have hambient : (jX '' K)ᶜ ⊆ S := by
    intro x hx
    cases x using OnePoint.rec with
    | infty => exact mem_of_mem_nhds hN
    | coe x =>
      exact hKoutside (fun hxK ↦ hx ⟨x, hxK, rfl⟩)
  let A : SupportBundleTriple (OnePoint X) := SupportBundleTriple.ofBoundary t.source t.target
    { control := jX '' K
      isCompact_control := hK.image jX.continuous
      boundary := t.boundary.restrict hambient }
  let := a₀.source.isFiniteRank
  let := a₀.target.isFiniteRank
  let := A.source.isFiniteRank
  let := A.target.isFiniteRank
  have hclass : A.compactSupportClass =
      compactSupportKZeroOpenPushforward jX OnePoint.isOpenEmbedding_coe
        a₀.compactSupportClass := by
    have ha := compactSupportTriple_compactSupportClass_ofBoundary
      (t.source.pullback jX) (t.target.pullback jX) a₀.datum
    have hA := compactSupportTriple_compactSupportClass_ofBoundary t.source t.target A.datum
    change a₀.datum.compactSupportClass = a₀.compactSupportClass at ha
    change A.datum.compactSupportClass = A.compactSupportClass at hA
    rw [← ha, ← hA]
    apply CompactSupportTriple.compactSupportClass_eq_openPushforward
      a₀.datum A.datum jX OnePoint.isOpenEmbedding_coe (Set.Subset.refl _)
      (Iso.refl _) (Iso.refl _)
    intro x hx hy v
    change ((t.boundary.pullback jX).restrict hKoutside).linearEquiv ⟨x, hx⟩ v = _
    exact (Iso.restrictTo_apply (t.boundary.pullback jX) hKoutside ⟨x, hx⟩ v).trans
      ((RelativeTriple.pullback_apply t.boundary jX ⟨x, hKoutside hx⟩ v).trans
        (Iso.restrictTo_apply t.boundary hambient ⟨jX x, hy⟩ v).symm)
  have hpush (q : CompactSupportKZero X) :
      compactSupportKZeroToAbsolute
        (compactSupportKZeroOpenPushforward jX OnePoint.isOpenEmbedding_coe q) = q.val := by
    let hj := (OnePoint.isOpenEmbedding_coe : IsOpenEmbedding jX)
    let := hj.isOpen_range.locallyCompactSpace
    let e := hj.isEmbedding.toHomeomorph
    let i : C(Set.range jX, X) := ⟨e.symm, e.symm.continuous⟩
    let collapse : C(OnePoint (OnePoint X), OnePoint X) :=
      (properOnePointMap i e.symm.isProperMap).comp
        ⟨onePointCollapse (Set.range jX), continuous_onePointCollapse _ hj.isOpen_range⟩
    let j : C(OnePoint X, OnePoint (OnePoint X)) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
    have hid : collapse.comp j = ContinuousMap.id (OnePoint X) := by
      ext x
      cases x using OnePoint.rec with
      | infty =>
        change OnePoint.map i (onePointCollapse (Set.range jX) (∞ : OnePoint X)) = ∞
        rw [onePointCollapse_coe_of_notMem]
        · rfl
        · rintro ⟨x, hx⟩
          exact OnePoint.coe_ne_infty x hx
      | coe x =>
        change OnePoint.map i (onePointCollapse (Set.range jX) (jX x)) = (x : OnePoint X)
        rw [onePointCollapse_coe_of_mem (Set.range jX) (jX x) ⟨x, rfl⟩, OnePoint.map_some]
        exact congrArg OnePoint.some (hj.isEmbedding.toHomeomorph_symm_apply x)
    change complexKZeroPullback j
      (complexKZeroPullback
        ⟨onePointCollapse (Set.range jX), continuous_onePointCollapse _ hj.isOpen_range⟩
        (complexKZeroPullback (properOnePointMap i e.symm.isProperMap) q.val)) = q.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    change complexKZeroPullback (collapse.comp j) q.val = q.val
    rw [hid]
    change kZeroMap (RingHom.id C(OnePoint X, ℂ)) q.val = q.val
    rw [kZeroMap_id]
    rfl
  have ha₀ : a₀.compactSupportClass = z := by
    apply Subtype.ext
    calc
      a₀.compactSupportClass.val = compactSupportKZeroToAbsolute A.compactSupportClass := by
        rw [hclass, hpush]
      _ = t.source.kZeroClass - t.target.kZeroClass := A.compactSupportClass_toAbsolute
      _ = z.val := hforget
  -- Pull back the same compactification bundles along the specified open collapse.
  let := hf.isOpen_range.locallyCompactSpace
  let ef := hf.isEmbedding.toHomeomorph
  let ifn : C(Set.range f, X) := ⟨ef.symm, ef.symm.continuous⟩
  let collapse : C(OnePoint Y, OnePoint X) :=
    (properOnePointMap ifn ef.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
  let jY : C(Y, OnePoint Y) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  let g : C(Y, OnePoint X) := collapse.comp jY
  have hg (x : X) : g (f x) = jX x := by
    change OnePoint.map ifn (onePointCollapse (Set.range f) (f x)) = (x : OnePoint X)
    rw [onePointCollapse_coe_of_mem (Set.range f) (f x) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  have hgf : g.comp f = jX := ContinuousMap.ext hg
  have hboutside : (f '' K)ᶜ ⊆ g ⁻¹' S := by
    intro y hy
    by_cases h : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := h
      change g (f x) ∈ S
      rw [hg]
      exact hKoutside (fun hx ↦ hy ⟨x, hx, rfl⟩)
    · change OnePoint.map ifn (onePointCollapse (Set.range f) y) ∈ S
      rw [onePointCollapse_coe_of_notMem _ _ h, OnePoint.map_infty]
      exact mem_of_mem_nhds hN
  let b : SupportBundleTriple Y := SupportBundleTriple.ofBoundary
    (t.source.pullback g) (t.target.pullback g)
    { control := f '' K
      isCompact_control := hK.image f.continuous
      boundary := (t.boundary.pullback g).restrict hboutside }
  have haoutside : Kᶜ ⊆ (g.comp f) ⁻¹' S := by rw [hgf]; exact hKoutside
  let a : SupportBundleTriple X := SupportBundleTriple.ofBoundary
    (t.source.pullback (g.comp f)) (t.target.pullback (g.comp f))
    { control := K
      isCompact_control := hK
      boundary := (t.boundary.pullback (g.comp f)).restrict haoutside }
  have ha : a.compactSupportClass = z := by
    have compare (j : C(X, OnePoint X)) (hj : j = jX) (hout : Kᶜ ⊆ j ⁻¹' S) :
        (SupportBundleTriple.ofBoundary (t.source.pullback j) (t.target.pullback j)
          { control := K, isCompact_control := hK,
            boundary := (t.boundary.pullback j).restrict hout }).compactSupportClass = z := by
      subst j
      exact ha₀
    exact compare (g.comp f) hgf haoutside
  let e := (pullbackCompIso (E := t.source.Fiber) g f).symm
  let d := (pullbackCompIso (E := t.target.Fiber) g f).symm
  have he (x : X) (v : t.source.Fiber (g (f x))) : e.linearEquiv x v = v := by
    exact (pullbackCompIso_apply (E := t.source.Fiber) g f x
      (e.linearEquiv x v)).symm.trans
        (((pullbackCompIso (E := t.source.Fiber) g f).linearEquiv x).apply_symm_apply v)
  have hd (x : X) (v : t.target.Fiber (g (f x))) : d.linearEquiv x v = v := by
    exact (pullbackCompIso_apply (E := t.target.Fiber) g f x
      (d.linearEquiv x v)).symm.trans
        (((pullbackCompIso (E := t.target.Fiber) g f).linearEquiv x).apply_symm_apply v)
  let := a.source.isFiniteRank
  let := a.target.isFiniteRank
  let := b.source.isFiniteRank
  let := b.target.isFiniteRank
  let := isFiniteRank_pullback (E := b.source.Fiber) f
  let := isFiniteRank_pullback (E := b.target.Fiber) f
  let a' := a.datum.congr e d
  have ha' : a'.compactSupportClass = z := by
    change (a.datum.congr e d).compactSupportClass = z
    rw [a.datum.compactSupportClass_congr]
    exact (compactSupportTriple_compactSupportClass_ofBoundary a.source a.target a.datum).trans ha
  refine ⟨b, a', ha', Set.Subset.refl _, ?_⟩
  intro x hx hy v
  have hei : e.symm.linearEquiv x v = v := by
    exact (he x (e.symm.linearEquiv x v)).symm.trans ((e.linearEquiv x).apply_symm_apply v)
  have hb : a.datum.boundary.linearEquiv ⟨x, hx⟩ v =
      b.datum.boundary.linearEquiv ⟨f x, hy⟩ v := by
    change ((t.boundary.pullback (g.comp f)).restrict haoutside).linearEquiv ⟨x, hx⟩ v =
      ((t.boundary.pullback g).restrict hboutside).linearEquiv ⟨f x, hy⟩ v
    exact (Iso.restrictTo_apply (t.boundary.pullback (g.comp f)) haoutside ⟨x, hx⟩ v).trans
      ((RelativeTriple.pullback_apply t.boundary (g.comp f) ⟨x, haoutside hx⟩ v).trans
        ((Iso.restrictTo_apply (t.boundary.pullback g) hboutside ⟨f x, hy⟩ v).trans
          (RelativeTriple.pullback_apply t.boundary g ⟨f x, hboutside hy⟩ v)).symm)
  change (a.datum.congr e d).boundary.linearEquiv ⟨x, hx⟩ v = _
  rw [a.datum.congr_apply, hei, hd]
  exact hb

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle Topology
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 5000000 in
-- Compare the two actual supported Thom representatives along the same open embedding.
/-- Open-extension naturality of the supported Thom operator with specified pairings. -/
private theorem supportedThomHom_openPushforward_of_continuous_pairing
    (E : Y → Type*) [hN : ∀ y, NormedAddCommGroup (E y)]
    [hI : ∀ y, InnerProductSpace ℂ (E y)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (hY : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2))
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (hX : Continuous (fun z : TotalSpace Unit ((f *ᵖ E) ×ᵇ (f *ᵖ E)) ↦
      inner ℂ (show E (f z.proj) from z.snd.1) z.snd.2)) :
    let : ∀ x, NormedAddCommGroup ((f *ᵖ E) x) := fun x ↦ hN (f x)
    let : ∀ x, InnerProductSpace ℂ ((f *ᵖ E) x) := fun x ↦ hI (f x)
    let : ∀ x, AddCommGroup ((f *ᵖ E) x) := fun x ↦ (hN (f x)).toAddCommGroup
    let : ∀ x, AddCommMonoid ((f *ᵖ E) x) := fun x ↦
      (hN (f x)).toAddCommGroup.toAddCommMonoid
    let : ∀ x, Module ℂ ((f *ᵖ E) x) := fun x ↦ (hI (f x)).toModule
    (compactSupportKZeroOpenPushforward (pullbackTotalMap E f)
      ((pullbackTotalMap_properties E f).2 hf)).comp
        (ComplexBundle.supportedThomHom (f *ᵖ E) hX) =
      (ComplexBundle.supportedThomHom E hY).comp
        (compactSupportKZeroOpenPushforward f hf) := by
  let : ∀ x, NormedAddCommGroup ((f *ᵖ E) x) := fun x ↦ hN (f x)
  let : ∀ x, InnerProductSpace ℂ ((f *ᵖ E) x) := fun x ↦ hI (f x)
  let : ∀ x, AddCommGroup ((f *ᵖ E) x) := fun x ↦ (hN (f x)).toAddCommGroup
  let : ∀ x, AddCommMonoid ((f *ᵖ E) x) := fun x ↦
    (hN (f x)).toAddCommGroup.toAddCommMonoid
  let : ∀ x, Module ℂ ((f *ᵖ E) x) := fun x ↦ (hI (f x)).toModule
  change (compactSupportKZeroOpenPushforward (pullbackTotalMap E f)
    ((pullbackTotalMap_properties E f).2 hf)).comp
      (ComplexBundle.supportedThomHom (f *ᵖ E) hX) =
    (ComplexBundle.supportedThomHom E hY).comp
      (compactSupportKZeroOpenPushforward f hf)
  /- Choose a representative whose two bundles are actual pullbacks from the target.
  A bump supported inside the image gives one cutoff on both bases. The original
  exterior and tensor comparisons retain every vector, so the two boundaries and
  compact zero controls agree under the specified total lift. Apply support excision. -/
  have exterior_pullback (i : ZMod 2) :
      ∃ e : Iso (fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) i)
          (f *ᵖ fun y ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) i),
        ∀ x w, e.linearEquiv x w = w := by
    let W := fun y ↦ ExteriorAlgebra ℂ (E y)
    let V := fun x ↦ ExteriorAlgebra ℂ ((f *ᵖ E) x)
    have hlift : Continuous (fun z : TotalSpace Unit V ↦
        (⟨f z.proj, z.snd⟩ : TotalSpace Unit W)) := by
      apply continuous_iSup_dom.mpr
      intro m
      apply continuous_iSup_dom.mpr
      intro k
      apply continuous_coinduced_dom.mpr
      let D := TotalSpace Unit (fun x : X ↦
        (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → (f *ᵖ E) x))
      let D' := TotalSpace Unit (fun y : Y ↦
        (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → E y))
      let : TopologicalSpace D := TopologicalSpace.induced
        (fun z : D ↦ (z.proj, z.snd.1,
          fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit (f *ᵖ E)))) inferInstance
      let : TopologicalSpace D' := TopologicalSpace.induced
        (fun z : D' ↦ (z.proj, z.snd.1,
          fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit E))) inferInstance
      have hd : Continuous (fun z : D ↦ (z.proj, z.snd.1,
          fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit (f *ᵖ E)))) :=
        continuous_induced_dom
      have htuple : Continuous (fun z : D ↦ (⟨f z.proj, z.snd⟩ : D')) := by
        apply continuous_induced_rng.mpr
        exact (f.continuous.comp hd.fst).prodMk (hd.snd.fst.prodMk
          (continuous_pi fun j ↦ continuous_pi fun l ↦
            (Pullback.continuous_lift Unit E f).comp
              ((continuous_apply l).comp ((continuous_apply j).comp hd.snd.snd))))
      have hwedge : Continuous (fun z : D' ↦ (⟨z.proj,
          ∑ j : Fin m, z.snd.1 j • ExteriorAlgebra.ιMulti ℂ (k j) (z.snd.2 j)⟩ :
            TotalSpace Unit W)) :=
        continuous_iSup_rng (i := m) (continuous_iSup_rng (i := k) continuous_coinduced_rng)
      exact hwedge.comp htuple
    let P : Y → Type _ := fun y ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) i
    let Q : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) i
    let : IsFiniteRank (f *ᵖ E) := isFiniteRank_pullback (E := E) f
    let : IsFiniteRank Q := isFiniteRank_exteriorParity (E := f *ᵖ E) i
    let : IsFiniteRank (f *ᵖ P) := isFiniteRank_pullback (E := P) f
    have hparity : Continuous (fun z : TotalSpace Unit Q ↦
        (⟨f z.proj, z.snd⟩ : TotalSpace Unit P)) := by
      apply continuous_induced_rng.mpr
      have hinc : Continuous (fun z : TotalSpace Unit Q ↦
          (⟨z.proj, z.snd.val⟩ : TotalSpace Unit V)) := continuous_induced_dom
      exact hlift.comp hinc
    let H : Hom Q (f *ᵖ P) :=
      { linearMap x := (LinearMap.id : Q x →ₗ[ℂ] (f *ᵖ P) x)
        continuous_total := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit P f).continuous_iff]
          exact continuous_proj.prodMk hparity }
    exact ⟨H.toIso (fun _ ↦ Function.bijective_id), fun _ _ ↦ rfl⟩
  -- Tensor these same-vector parity comparisons with the given coefficient bundles.
  have tensor_pullback (J K : FiniteBundle Y) :
      ∃ e : Iso
        (fun x : X ↦ ((J.pullback f).Fiber x ⊗[ℂ]
            CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 0) ×
          ((K.pullback f).Fiber x ⊗[ℂ]
            CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 1))
        (f *ᵖ fun y : Y ↦ (J.Fiber y ⊗[ℂ]
            CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
          (K.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1)),
        ∀ x w, e.linearEquiv x w = w := by
    have sum_pullback {G H : Y → Type _}
        [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
        [∀ y, AddCommGroup (H y)] [∀ y, Module ℂ (H y)]
        [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
        [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H] (f : C(X, Y)) :
        ∃ e : Iso ((f *ᵖ G) ×ᵇ (f *ᵖ H)) (f *ᵖ (G ×ᵇ H)),
          ∀ x w, e.linearEquiv x w = w := by
      let : IsFiniteRank (f *ᵖ G) := isFiniteRank_pullback (E := G) f
      let : IsFiniteRank (f *ᵖ H) := isFiniteRank_pullback (E := H) f
      let : IsFiniteRank (f *ᵖ (G ×ᵇ H)) := isFiniteRank_pullback (E := G ×ᵇ H) f
      let F : Hom ((f *ᵖ G) ×ᵇ (f *ᵖ H)) (f *ᵖ (G ×ᵇ H)) :=
        { linearMap _ := LinearMap.id
          continuous_total := by
            rw [(inducing_pullbackTotalSpaceEmbedding Unit (G ×ᵇ H) f).continuous_iff]
            apply continuous_proj.prodMk
            apply continuous_induced_rng.mpr
            exact ((Pullback.continuous_lift Unit G f).comp
              (continuous_sum_fst (E := f *ᵖ G) (F := f *ᵖ H))).prodMk
                ((Pullback.continuous_lift Unit H f).comp
                  (continuous_sum_snd (E := f *ᵖ G) (F := f *ᵖ H))) }
      exact ⟨F.toIso (fun _ ↦ Function.bijective_id), fun _ _ ↦ rfl⟩
    let P : ZMod 2 → Y → Type _ := fun i y ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) i
    let Q : ZMod 2 → X → Type _ := fun i x ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) i
    let : IsFiniteRank (f *ᵖ E) := isFiniteRank_pullback (E := E) f
    let (i : ZMod 2) : IsFiniteRank (P i) := isFiniteRank_exteriorParity (E := E) i
    let (i : ZMod 2) : IsFiniteRank (Q i) := isFiniteRank_exteriorParity (E := f *ᵖ E) i
    let (i : ZMod 2) : IsFiniteRank (f *ᵖ (P i)) := isFiniteRank_pullback (E := P i) f
    have htensor (B : FiniteBundle Y) (i : ZMod 2) :
        ∃ e : Iso (fun x : X ↦ (B.pullback f).Fiber x ⊗[ℂ] Q i x)
            (f *ᵖ fun y ↦ B.Fiber y ⊗[ℂ] P i y), ∀ x w, e.linearEquiv x w = w := by
      as_aux_lemma =>
      let : IsFiniteRank (f *ᵖ B.Fiber) := isFiniteRank_pullback (E := B.Fiber) f
      obtain ⟨p, hp⟩ := exterior_pullback i
      let u : Iso (fun x : X ↦ (B.pullback f).Fiber x ⊗[ℂ] Q i x)
          (fun x : X ↦ (f *ᵖ B.Fiber) x ⊗[ℂ] (f *ᵖ (P i)) x) :=
        (Iso.refl (f *ᵖ B.Fiber)).tensor p
      let t : Iso (f *ᵖ fun y ↦ B.Fiber y ⊗[ℂ] P i y)
          (fun x : X ↦ (f *ᵖ B.Fiber) x ⊗[ℂ] (f *ᵖ (P i)) x) :=
        pullbackTensorIso (E := B.Fiber) (F := P i) f
      have hu (x : X) (a : (B.pullback f).Fiber x) (b : Q i x) :
          u.linearEquiv x (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] p.linearEquiv x b := rfl
      have ht (x : X) (w : (f *ᵖ fun y ↦ B.Fiber y ⊗[ℂ] P i y) x) :
          t.linearEquiv x w = w := rfl
      clear_value u t
      let ti := t.symm
      let e := u.trans ti
      refine ⟨e, ?_⟩
      intro x w
      induction w using TensorProduct.inductionOn with
      | tmul a b =>
          change (t.linearEquiv x).symm (u.linearEquiv x (a ⊗ₜ[ℂ] b)) = a ⊗ₜ[ℂ] b
          apply (t.linearEquiv x).symm_apply_eq.mpr
          have h := congrArg (fun b' ↦ a ⊗ₜ[ℂ] b') (hp x b)
          exact (hu x a b).trans (h.trans (ht x (a ⊗ₜ[ℂ] b)).symm)
      | add a b ha hb =>
          exact ((e.linearEquiv x).map_add a b).trans (congrArg₂ (· + ·) ha hb)
    obtain ⟨u, hu⟩ := htensor J 0
    obtain ⟨v, hv⟩ := htensor K 1
    obtain ⟨s, hs⟩ := sum_pullback
      (G := fun y ↦ J.Fiber y ⊗[ℂ] P 0 y)
      (H := fun y ↦ K.Fiber y ⊗[ℂ] P 1 y) f
    refine ⟨(u.sum v).trans s, ?_⟩
    intro x w
    change s.linearEquiv x (u.linearEquiv x w.1, v.linearEquiv x w.2) = w
    exact (hs x _).trans (Prod.ext (hu x w.1) (hv x w.2))
  -- Retain the original two iterated-pullback comparisons on total spaces.
  have tensor_total (J K : FiniteBundle Y) :
      ∃ e : Iso
        ((π Unit (f *ᵖ E)) *ᵖ fun x : X ↦ ((J.pullback f).Fiber x ⊗[ℂ]
            CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 0) ×
          ((K.pullback f).Fiber x ⊗[ℂ]
            CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 1))
        ((pullbackTotalMap E f) *ᵖ ((π Unit E) *ᵖ fun y : Y ↦ (J.Fiber y ⊗[ℂ]
            CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
          (K.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1))),
        ∀ x w, e.linearEquiv x w = w := by
    let pX : C(TotalSpace Unit (f *ᵖ E), X) := ⟨π Unit (f *ᵖ E), continuous_proj⟩
    let pY : C(TotalSpace Unit E, Y) := ⟨π Unit E, continuous_proj⟩
    let q := pullbackTotalMap E f
    let S : Y → Type _ := fun y ↦ (J.Fiber y ⊗[ℂ]
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
      (K.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1)
    obtain ⟨e, he⟩ := tensor_pullback J K
    let u := pullbackCompIso (E := S) f pX
    let v := pullbackCompIso (E := S) pY q
    have hu (z : TotalSpace Unit (f *ᵖ E)) (w) : u.linearEquiv z w = w :=
      pullbackCompIso_apply (E := S) f pX z w
    have hv (z : TotalSpace Unit (f *ᵖ E)) (w) : v.linearEquiv z w = w :=
      pullbackCompIso_apply (E := S) pY q z w
    clear_value u v
    let vi := v.symm
    let uv := u.trans vi
    let ep := e.pullback pX
    let result := ep.trans uv
    refine ⟨result, ?_⟩
    intro z w
    change (v.linearEquiv z).symm (u.linearEquiv z (e.linearEquiv z.proj w)) = w
    apply (v.linearEquiv z).symm_apply_eq.mpr
    exact (hu z _).trans ((he z.proj w).trans (hv z w).symm)
  classical
  let : IsFiniteRank (f *ᵖ E) := isFiniteRank_pullback (E := E) f
  let pX : C(TotalSpace Unit (f *ᵖ E), X) := ⟨π Unit (f *ᵖ E), continuous_proj⟩
  let pY : C(TotalSpace Unit E, Y) := ⟨π Unit E, continuous_proj⟩
  let q := pullbackTotalMap E f
  have hq : IsOpenEmbedding q := ((pullbackTotalMap_properties E f).2 hf)
  apply AddMonoidHom.ext
  intro z
  -- Choose both coefficient bundles from the same compactification representative.
  obtain ⟨b, a, ha, hcontrol, hboundary⟩ := exists_supportBundleTriple_openExtension z f hf
  let := b.source.isFiniteRank
  let := b.target.isFiniteRank
  let a₀ := SupportBundleTriple.ofBoundary (b.source.pullback f) (b.target.pullback f) a
  have ha₀ : a₀.compactSupportClass = z :=
    (compactSupportTriple_compactSupportClass_ofBoundary
      (b.source.pullback f) (b.target.pullback f) a).symm.trans ha
  have hb : b.compactSupportClass =
      compactSupportKZeroOpenPushforward f hf a₀.compactSupportClass := by
    have hb₀ : b.datum.compactSupportClass = b.compactSupportClass :=
      compactSupportTriple_compactSupportClass_ofBoundary b.source b.target b.datum
    rw [← hb₀, ← compactSupportTriple_compactSupportClass_ofBoundary
      (b.source.pullback f) (b.target.pullback f) a]
    exact CompactSupportTriple.compactSupportClass_eq_openPushforward a b.datum f hf
      hcontrol (Iso.refl _) (Iso.refl _) hboundary
  -- A cutoff supported inside the open image has a compact source preimage without properness.
  have hK : IsCompact (f '' a.control) := a.isCompact_control.image f.continuous
  have hKrange : f '' a.control ⊆ Set.range f := Set.image_subset_range _ _
  obtain ⟨C, hC, _, hKC, hCrange⟩ :=
    exists_compact_closed_between hK hf.isOpen_range hKrange
  obtain ⟨g, hg, hgcompact, hgrange, hgr⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hC hf.isOpen_range hCrange
  have hrange (y : Y) : 1 - g y ∈ I := by
    have hy := hgr y
    constructor <;> linarith [hy.1, hy.2]
  let ρ : C(Y, I) := ⟨fun y ↦ ⟨1 - g y, hrange y⟩,
    (continuous_const.sub g.continuous).subtype_mk hrange⟩
  let U : Set Y := interior C
  let L : Set Y := tsupport g
  have hU : IsOpen U := isOpen_interior
  have hL : IsCompact L := hgcompact
  have hzero (y : Y) (hy : y ∈ U) : ρ y = 0 := by
    apply Subtype.ext
    change 1 - g y = 0
    rw [hg (interior_subset hy)]
    exact sub_self (1 : ℝ)
  have hone (y : Y) (hy : y ∉ L) : ρ y = 1 := by
    apply Subtype.ext
    change 1 - g y = 1
    rw [image_eq_zero_of_notMem_tsupport hy, sub_zero]
  have hca : a.control ⊆ f ⁻¹' U := fun x hx ↦ hKC ⟨x, hx, rfl⟩
  have hcb : b.datum.control ⊆ U := hcontrol.trans hKC
  let ρX := ρ.comp f
  have hUX : IsOpen (f ⁻¹' U) := hU.preimage f.continuous
  have hzeroX (x : X) (hx : x ∈ f ⁻¹' U) : ρX x = 0 := hzero (f x) hx
  have hLX : IsCompact (f ⁻¹' L) := hf.isEmbedding.isInducing.isCompact_preimage' hL hgrange
  have honeX (x : X) (hx : x ∉ f ⁻¹' L) : ρX x = 1 := hone (f x) hx
  -- The original reciprocal cutoff maps agree on the original pullback fibers.
  have cutoff_eq (x : X) :
      a.cutoffLinearMap ρX x = b.datum.cutoffLinearMap ρ (f x) ∧
        a.inverse.cutoffLinearMap ρX x = b.datum.inverse.cutoffLinearMap ρ (f x) := by
    by_cases hx : x ∈ a.control
    · have hρ : ρ (f x) = 0 := hzero (f x) (hca hx)
      by_cases hy : f x ∈ b.datum.control <;> constructor <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          ρX, ContinuousMap.comp_apply, hx, hy, dite_true, dite_false,
          hρ, Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul]
    · have hy : f x ∉ b.datum.control := by
        intro hy
        obtain ⟨x', hx', hfx⟩ := hcontrol hy
        exact hx ((hf.injective hfx) ▸ hx')
      have heq : a.boundary.linearEquiv ⟨x, hx⟩ =
          b.datum.boundary.linearEquiv ⟨f x, hy⟩ := LinearEquiv.ext (hboundary x hx hy)
      constructor <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          hx, hy, dite_false, ρX, ContinuousMap.comp_apply, Iso.symm, heq]
  let S : Y → Type _ := fun y ↦ (b.source.Fiber y ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
    (b.target.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1)
  let T : Y → Type _ := fun y ↦ (b.target.Fiber y ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 0) ×
    (b.source.Fiber y ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E y)) 1)
  let SX : X → Type _ := fun x ↦ ((b.source.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 0) ×
    ((b.target.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 1)
  let TX : X → Type _ := fun x ↦ ((b.target.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 0) ×
    ((b.source.pullback f).Fiber x ⊗[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((f *ᵖ E) x)) 1)
  let : IsFiniteRank (pX *ᵖ SX) := isFiniteRank_pullback (E := SX) pX
  let : IsFiniteRank (pX *ᵖ TX) := isFiniteRank_pullback (E := TX) pX
  let : IsFiniteRank (pY *ᵖ S) := isFiniteRank_pullback (E := S) pY
  let : IsFiniteRank (pY *ᵖ T) := isFiniteRank_pullback (E := T) pY
  let : IsFiniteRank (q *ᵖ (pY *ᵖ S)) := isFiniteRank_pullback (E := pY *ᵖ S) q
  let : IsFiniteRank (q *ᵖ (pY *ᵖ T)) := isFiniteRank_pullback (E := pY *ᵖ T) q
  -- Record each forward symbol on its exact inherited coefficient and exterior fibers.
  let phiX (x : TotalSpace Unit (f *ᵖ E)) (w : SX x.proj) : TX x.proj :=
    thomTensorSymbol (F := b.source.Fiber (f x.proj))
      (G := b.target.Fiber (f x.proj)) (V := E (f x.proj))
      (show b.source.Fiber (f x.proj) →ₗ[ℂ] b.target.Fiber (f x.proj) from
        a.cutoffLinearMap ρX x.proj)
      (show b.target.Fiber (f x.proj) →ₗ[ℂ] b.source.Fiber (f x.proj) from
        a.inverse.cutoffLinearMap ρX x.proj)
      (show E (f x.proj) from x.snd) w
  let phiY (x : TotalSpace Unit E) (w : S x.proj) : T x.proj :=
    thomTensorSymbol (F := b.source.Fiber x.proj) (G := b.target.Fiber x.proj)
      (V := E x.proj) (b.datum.cutoffLinearMap ρ x.proj)
      (b.datum.inverse.cutoffLinearMap ρ x.proj) x.snd w
  have hsymbol (x : TotalSpace Unit (f *ᵖ E)) (w : SX x.proj) :
      phiX x w = phiY (q x) w := by
    exact congrArg₂
      (fun (d : b.source.Fiber (f x.proj) →ₗ[ℂ] b.target.Fiber (f x.proj))
        (d' : b.target.Fiber (f x.proj) →ₗ[ℂ] b.source.Fiber (f x.proj)) ↦
        thomTensorSymbol (F := b.source.Fiber (f x.proj))
          (G := b.target.Fiber (f x.proj)) (V := E (f x.proj)) d d'
          (show E (f x.proj) from x.snd) w)
      (cutoff_eq x.proj).1 (cutoff_eq x.proj).2
  let A : CompactSupportTriple (pX *ᵖ SX) (pX *ᵖ TX) :=
    supportedThomTriple (f *ᵖ E) hX a₀ ρX (f ⁻¹' U) hUX hca hzeroX (f ⁻¹' L) hLX honeX
  let B : CompactSupportTriple (pY *ᵖ S) (pY *ᵖ T) :=
    supportedThomTriple E hY b ρ U hU hcb hzero L hL hone
  have hAvalue (x : (A.controlᶜ : Set (TotalSpace Unit (f *ᵖ E))))
      (w : SX x.val.proj) : A.boundary.linearEquiv x w = phiX x.val w := rfl
  have hBvalue (x : (B.controlᶜ : Set (TotalSpace Unit E)))
      (w : S x.val.proj) : B.boundary.linearEquiv x w = phiY x.val w := rfl
  change compactSupportKZeroOpenPushforward q hq (ComplexBundle.supportedThomHom (f *ᵖ E) hX z) =
    ComplexBundle.supportedThomHom E hY (compactSupportKZeroOpenPushforward f hf z)
  rw [← ha₀, ← hb]
  rw [supportedThomHom_class (f *ᵖ E) hX a₀ ρX (f ⁻¹' U) hUX hca hzeroX
    (f ⁻¹' L) hLX honeX,
    supportedThomHom_class E hY b ρ U hU hcb hzero L hL hone]
  change compactSupportKZeroOpenPushforward q hq A.compactSupportClass = B.compactSupportClass
  -- Both boundaries use the same vectors, exterior operator, cutoff and reciprocal map.
  obtain ⟨u, hu⟩ := tensor_total b.source b.target
  obtain ⟨v, hv⟩ := tensor_total b.target b.source
  have hCB : B.control ⊆ q '' A.control := by
    rintro ⟨y, e⟩ ⟨hy, he⟩
    obtain ⟨x, rfl⟩ := hgrange hy
    exact ⟨⟨x, e⟩, ⟨hy, he⟩, rfl⟩
  clear_value A B
  symm
  apply CompactSupportTriple.compactSupportClass_eq_openPushforward A B q hq hCB u v
  intro x hx hy w
  have hraw : A.boundary.linearEquiv ⟨x, hx⟩ w =
      B.boundary.linearEquiv ⟨q x, hy⟩ w :=
    (hAvalue ⟨x, hx⟩ w).trans ((hsymbol x w).trans (hBvalue ⟨q x, hy⟩ w).symm)
  exact (hv x _).trans (hraw.trans
    (congrArg (B.boundary.linearEquiv ⟨q x, hy⟩) (hu x w).symm))

variable {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 500000 in
-- Apply the original-pairing comparison to the same metric and its native pullback.
/-- The actual supported Thom operator commutes with extension along an open embedding. -/
theorem supportedThomHom_openPushforward (h : ContinuousHermitianMetric E)
    (f : C(X, Y)) (hf : IsOpenEmbedding f) :
    letI := isFiniteRank_pullback (E := E) f
    (compactSupportKZeroOpenPushforward (pullbackTotalMap E f)
      ((pullbackTotalMap_properties E f).2 hf)).comp (h.pullback f).supportedThomHom =
      h.supportedThomHom.comp (compactSupportKZeroOpenPushforward f hf) := by
  let : ∀ y, NormedAddCommGroup (E y) := fun y ↦ (h.toCore y).toNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (E y) := fun y ↦
    InnerProductSpace.ofCore (h.toCore y).toCore
  exact supportedThomHom_openPushforward_of_continuous_pairing E h.continuous_pairing
    f hf (h.pullback f).continuous_pairing

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

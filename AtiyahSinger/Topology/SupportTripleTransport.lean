/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTriplePullback

/-!
# Support classes of arbitrary-universe bundle families

Public module ID: M2200.

D07/K02. Resizing conjugates the original exterior isomorphism by actual bundle
isomorphisms. Independence is a commuting-square theorem, not an arbitrary group
identification. Compact support is retained throughout. This is an adapter for
the standard support-triple model of SG I.9.26.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]
  {H : X → Type*} [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)]

/-- Transport both bundles by conjugating the same boundary map. -/
def CompactSupportTriple.congr (a : CompactSupportTriple E F) (e : Iso E G) (f : Iso F H) :
    CompactSupportTriple G H :=
  { control := a.control
    isCompact_control := a.isCompact_control
    boundary := ((e.symm.restrict a.controlᶜ).trans a.boundary).trans
      (f.restrict a.controlᶜ) }

/-- Conjugation retains the original compact control. -/
theorem CompactSupportTriple.congr_control (a : CompactSupportTriple E F)
    (e : Iso E G) (f : Iso F H) : (a.congr e f).control = a.control := by
  /- The constructor copies the control set verbatim. Only the exterior isomorphism is composed
  with the two restricted global isomorphisms. -/
  rfl

/-- The transported exterior action is exactly the stated conjugation. -/
theorem CompactSupportTriple.congr_apply (a : CompactSupportTriple E F)
    (e : Iso E G) (f : Iso F H) (x : (a.controlᶜ : Set X)) (v : G x) :
    (a.congr e f).boundary.linearEquiv x v =
      f.linearEquiv x (a.boundary.linearEquiv x (e.symm.linearEquiv x v)) := by
  /- Expand the two compositions and restriction maps. Their base point stays x, the source
  inverse is applied first, the original boundary second, and the target isomorphism last. -/
  rfl

/-- Conjugation by identities leaves the raw triple unchanged. -/
theorem CompactSupportTriple.congr_refl (a : CompactSupportTriple E F) :
    a.congr (Iso.refl E) (Iso.refl F) = a := by
  /- The compact controls coincide definitionally. Extensionality identifies the boundary
  linear equivalences, whose identity conjugations have the original vector values. -/

  cases a
  congr 1

/-- Conjugation commutes with reversing a triple. -/
theorem CompactSupportTriple.congr_inverse (a : CompactSupportTriple E F)
    (e : Iso E G) (f : Iso F H) :
    (a.congr e f).inverse = a.inverse.congr f e := by
  /- The inverse of f a e⁻¹ is e a⁻¹ f⁻¹ on each exterior fiber. Both triples have the same
  control, so equality follows from this exact action and proof irrelevance. -/

  change CompactSupportTriple.mk a.control a.isCompact_control _ =
    CompactSupportTriple.mk a.control a.isCompact_control _
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
/-- Conjugation respects enlargement of the compact control. -/
theorem CompactSupportTriple.congr_enlarge (a : CompactSupportTriple E F)
    (e : Iso E G) (f : Iso F H) (K : Set X) (hK : IsCompact K) (h : a.control ⊆ K) :
    (a.congr e f).enlarge K hK h = (a.enlarge K hK h).congr e f := by
  /- Both constructions restrict the same three composed maps to the complement of K. Their
  pointwise action is identical, and the controls and compactness data agree. -/

  change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
  congr 1
  apply Iso.ext
  intro x
  apply LinearEquiv.ext
  intro v
  have hl := (a.congr e f).enlarge_apply K hK h x v
  have hp := a.congr_apply e f ⟨x, fun hx ↦ x.property (h hx)⟩ v
  have hr := (a.enlarge K hK h).congr_apply e f x v
  have hq := a.enlarge_apply K hK h x (e.symm.linearEquiv x v)
  exact (hl.trans hp).trans ((hr.trans (congrArg (f.linearEquiv x) hq)).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Conjugation preserves homotopy with one uniform compact control. -/
theorem CompactSupportTriple.Homotopic.congr {a b : CompactSupportTriple E F}
    (hab : a.Homotopic b) (e : Iso E G) (f : Iso F H) :
    (a.congr e f).Homotopic (b.congr e f) := by
  /- Retain the common compact control. Pull the source and target isomorphisms to the
  cylinder, and conjugate the given joint boundary isomorphism by these constant families.
  Endpoint formulas are the required conjugated maps. -/
  obtain ⟨K, hK, ha, hb, ⟨H⟩⟩ := hab

  obtain ⟨He⟩ := IsoHomotopy.nonempty_refl (e.symm.restrict Kᶜ)
  obtain ⟨Hf⟩ := IsoHomotopy.nonempty_refl (f.restrict Kᶜ)
  obtain ⟨HeH⟩ := He.nonempty_comp H
  obtain ⟨J⟩ := HeH.nonempty_comp Hf
  refine ⟨K, hK, ha, hb, ?_⟩
  -- On K's complement, both endpoints use the same conjugated boundary formula.
  have hvalue (d : CompactSupportTriple E F) (hd : d.control ⊆ K)
      (x : (Kᶜ : Set X)) (v : G x) :
      ((d.congr e f).enlarge K hK hd).boundary.linearEquiv x v =
        f.linearEquiv x ((d.enlarge K hK hd).boundary.linearEquiv x
          (e.symm.linearEquiv x v)) := by
    have hl := (d.congr e f).enlarge_apply K hK hd x v
    have hp := d.congr_apply e f ⟨x, fun hx ↦ x.property (hd hx)⟩ v
    have hr := d.enlarge_apply K hK hd x (e.symm.linearEquiv x v)
    exact (hl.trans hp).trans (congrArg (f.linearEquiv x) hr).symm
  refine ⟨{ iso := J.iso, map_zero := ?_, map_one := ?_ }⟩
  · intro x v
    exact (J.map_zero x v).trans (hvalue a ha x v).symm
  · intro x v
    exact (J.map_one x v).trans (hvalue b hb x v).symm

variable [IsFiniteRank E] [IsFiniteRank F] [IsFiniteRank G] [IsFiniteRank H]

/-- Package arbitrary-universe fibers using conjugation to the chosen small models. -/
def CompactSupportTriple.toSupportBundleTriple (a : CompactSupportTriple E F) :
    SupportBundleTriple X :=
  SupportBundleTriple.ofBoundary (smallBundle E) (smallBundle F)
    (a.congr (smallBundleIso E) (smallBundleIso F))

/-- Resizing does not alter the support control. -/
theorem CompactSupportTriple.toSupportBundleTriple_control (a : CompactSupportTriple E F) :
    a.toSupportBundleTriple.datum.control = a.control := by
  /- The packaged triple uses exactly the conjugated raw datum, whose control was copied
  unchanged. Bundling introduces no new region of possible failure of invertibility. -/
  rfl

/-- The resized boundary commutes with the original maps. -/
theorem CompactSupportTriple.toSupportBundleTriple_apply (a : CompactSupportTriple E F)
    (x : (a.controlᶜ : Set X)) (v : E x) :
    a.toSupportBundleTriple.datum.boundary.linearEquiv x
        ((smallBundleIso E).linearEquiv x v) =
      (smallBundleIso F).linearEquiv x (a.boundary.linearEquiv x v) := by
  /- Use the conjugation action formula and cancel the source isomorphism with its inverse.
  This commuting square characterizes how the original boundary is retained in the small
  model. -/

  have h := a.congr_apply (smallBundleIso E) (smallBundleIso F) x
    ((smallBundleIso E).linearEquiv x v)
  have he := ((smallBundleIso E).linearEquiv x).symm_apply_apply v
  exact h.trans (congrArg (fun w ↦ (smallBundleIso F).linearEquiv x
    (a.boundary.linearEquiv x w)) he)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every alternative small model with its specified isomorphisms gives an isomorphic germ. -/
theorem CompactSupportTriple.toSupportBundleTriple_isIsomorphic (a : CompactSupportTriple E F)
    (G H : FiniteBundle X) (e : Iso E G.Fiber) (f : Iso F H.Fiber) :
    a.toSupportBundleTriple.IsIsomorphic
      (SupportBundleTriple.ofBoundary G H (a.congr e f)) := by
  /- Use the original compact control. The source comparison is the chosen small-model inverse
  followed by e, and the target comparison is the corresponding inverse followed by f. The
  conjugation formulas make the exterior square commute. -/
  let e₀ := smallBundleIso E
  let f₀ := smallBundleIso F
  let u := e₀.symm.trans e
  let w := f₀.symm.trans f

  refine ⟨a.control, a.isCompact_control, Set.Subset.refl _, Set.Subset.refl _, u, w, ?_⟩
  intro x v
  have hl := (a.congr e₀ f₀).enlarge_apply a.control a.isCompact_control
    (Set.Subset.refl _) x v
  have hp := a.congr_apply e₀ f₀ x v
  have hr := (a.congr e f).enlarge_apply a.control a.isCompact_control
    (Set.Subset.refl _) x (u.linearEquiv x v)
  have hq := a.congr_apply e f x (u.linearEquiv x v)
  have hleft := congrArg (w.linearEquiv x) (hl.trans hp)
  have hright := hr.trans hq
  -- Each side cancels only its own specified source or target comparison.
  have hcancel₁ : w.linearEquiv x
      (f₀.linearEquiv x (a.boundary.linearEquiv x (e₀.symm.linearEquiv x v))) =
        f.linearEquiv x (a.boundary.linearEquiv x (e₀.symm.linearEquiv x v)) := by
    exact congrArg (f.linearEquiv x) ((f₀.linearEquiv x).symm_apply_apply _)
  have hcancel₂ : e.symm.linearEquiv x (u.linearEquiv x v) =
      e₀.symm.linearEquiv x v := (e.linearEquiv x).symm_apply_apply _
  exact (hleft.trans hcancel₁).trans
    ((hright.trans (congrArg (fun z ↦ f.linearEquiv x (a.boundary.linearEquiv x z))
      hcancel₂)).symm)

variable [hL : LocallyCompactSpace X] [hT : T2Space X]

include hL hT

/-- The actual compact-support K class of the original arbitrary-universe triple. -/
def CompactSupportTriple.compactSupportClass (a : CompactSupportTriple E F) :
    CompactSupportKZero X :=
  a.toSupportBundleTriple.compactSupportClass

/-- The class can be calculated in any specified small model. -/
theorem CompactSupportTriple.compactSupportClass_eq_model (a : CompactSupportTriple E F)
    (G H : FiniteBundle X) (e : Iso E G.Fiber) (f : Iso F H.Fiber) :
    a.compactSupportClass =
      (SupportBundleTriple.ofBoundary G H (a.congr e f)).compactSupportClass := by
  /- Apply invariance of the constructed support class to the commuting-square comparison with
  this small model. This is independent of coordinate choices because the original boundary
  is transported explicitly. -/
  exact a.toSupportBundleTriple.compactSupportClass_eq_of_isIsomorphic _
    (a.toSupportBundleTriple_isIsomorphic G H e f)

/-- Bundling an already small family gives its original geometric class. -/
theorem compactSupportTriple_compactSupportClass_ofBoundary (E F : FiniteBundle X)
    (a : CompactSupportTriple E.Fiber F.Fiber) :
    a.compactSupportClass = (SupportBundleTriple.ofBoundary E F a).compactSupportClass := by
  /- Use the original bundles as the alternative small models and their identity isomorphisms.
  Identity conjugation gives back precisely the original datum. -/
  simpa only [CompactSupportTriple.congr_refl] using
    a.compactSupportClass_eq_model E F (Iso.refl _) (Iso.refl _)

/-- Global bundle isomorphisms do not change a support class. -/
theorem CompactSupportTriple.compactSupportClass_congr (a : CompactSupportTriple E F)
    (e : Iso E G) (f : Iso F H) :
    (a.congr e f).compactSupportClass = a.compactSupportClass := by
  /- Compare both constructions in the chosen small models of G and H. Composite global
  isomorphisms and associativity of conjugation identify the two original boundary squares,
  giving equal constructed classes. -/
  -- Successive conjugations are definitionally the conjugation by the composite isomorphisms.
  exact (a.compactSupportClass_eq_model (smallBundle G) (smallBundle H)
    (e.trans (smallBundleIso G)) (f.trans (smallBundleIso H))).symm

/-- Uniform exterior homotopies give equal compact-support classes. -/
theorem CompactSupportTriple.compactSupportClass_eq_of_homotopic
    (a b : CompactSupportTriple E F) (hab : a.Homotopic b) :
    a.compactSupportClass = b.compactSupportClass := by
  /- Conjugate the given uniform homotopy to the two fixed small models, then apply the bundled
  homotopy theorem. The original common compact control is unchanged. -/
  exact supportBundleTriple_compactSupportClass_eq_of_homotopic (smallBundle E) (smallBundle F)
    (a.congr (smallBundleIso E) (smallBundleIso F))
    (b.congr (smallBundleIso E) (smallBundleIso F))
    (hab.congr (smallBundleIso E) (smallBundleIso F))

/-- Enlarging a compact control preserves the class. -/
theorem CompactSupportTriple.compactSupportClass_enlarge (a : CompactSupportTriple E F)
    (K : Set X) (hK : IsCompact K) (h : a.control ⊆ K) :
    (a.enlarge K hK h).compactSupportClass = a.compactSupportClass := by
  /- The enlargement homotopy uses the same boundary map on the new exterior. Apply homotopy
  invariance to this specified enlargement homotopy. -/
  exact (a.compactSupportClass_eq_of_homotopic _ (a.homotopic_enlarge K hK h)).symm

/-- The class of a globally invertible triple is zero. -/
theorem CompactSupportTriple.compactSupportClass_ofIso (e : Iso E F) :
    (CompactSupportTriple.ofIso e).compactSupportClass = 0 := by
  /- Conjugate the global isomorphism to small models. It remains global, so the bundled triple
  is an elementary class and its actual compact-window difference vanishes. -/
  let e₀ := smallBundleIso E
  let f₀ := smallBundleIso F
  have hboundary : (CompactSupportTriple.ofIso e).congr e₀ f₀ =
      CompactSupportTriple.ofIso ((e₀.symm.trans e).trans f₀) := by
    rfl
  change (SupportBundleTriple.ofBoundary (smallBundle E) (smallBundle F)
    ((CompactSupportTriple.ofIso e).congr e₀ f₀)).compactSupportClass = 0
  rw [hboundary]
  exact supportBundleTriple_compactSupportClass_ofIso _ _ _

/-- Reversing the original boundary negates its class. -/
theorem CompactSupportTriple.compactSupportClass_inverse (a : CompactSupportTriple E F) :
    a.inverse.compactSupportClass = -a.compactSupportClass := by
  /- Conjugation commutes with taking inverse, with the two small models exchanged. Apply the
  inverse formula for the bundled geometric support class. -/
  change (SupportBundleTriple.ofBoundary (smallBundle F) (smallBundle E)
    (a.inverse.congr (smallBundleIso F) (smallBundleIso E))).compactSupportClass = _
  rw [← CompactSupportTriple.congr_inverse]
  exact a.toSupportBundleTriple.compactSupportClass_inverse

/-- Composition of original exterior isomorphisms adds their classes. -/
theorem CompactSupportTriple.compactSupportClass_compose (a : CompactSupportTriple E F)
    (b : CompactSupportTriple F G) :
    (a.compose b).compactSupportClass = a.compactSupportClass + b.compactSupportClass := by
  /- Use the same chosen small model for the middle bundle. In the composite the two middle
  resizing maps cancel. Apply the bundled composition formula outside the union of compact
  controls. -/
  let e₀ := smallBundleIso E
  let f₀ := smallBundleIso F
  let g₀ := smallBundleIso G
  let K := a.control ∪ b.control
  have hK : IsCompact K := a.isCompact_control.union b.isCompact_control
  have hboundary : (a.compose b).congr e₀ g₀ =
      (a.congr e₀ f₀).compose (b.congr f₀ g₀) := by
    change CompactSupportTriple.mk _ _ _ = CompactSupportTriple.mk _ _ _
    congr 1
    dsimp only [CompactSupportTriple.congr, CompactSupportTriple.compose]
    refine @Iso.ext ((a.control ∪ b.control)ᶜ : Set X) _
      (Restrict (smallBundle E).Fiber (a.control ∪ b.control)ᶜ)
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) _
      (Restrict (smallBundle G).Fiber (a.control ∪ b.control)ᶜ)
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) _ _ _ ?_
    intro x
    change ((a.control ∪ b.control)ᶜ : Set X) at x
    refine DFunLike.ext _ _ ?_
    intro v
    change (smallBundle E).Fiber x at v
    -- The same middle resizing and its inverse cancel on the union exterior.
    let xa : (a.controlᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inl hx)⟩
    let xb : (b.controlᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inr hx)⟩
    let w := e₀.symm.linearEquiv x v
    let u := a.boundary.linearEquiv xa w
    have ha := a.enlarge_apply K hK Set.subset_union_left x w
    have hb := b.enlarge_apply K hK Set.subset_union_right x u
    have hleft := (congrArg (fun z ↦ g₀.linearEquiv x
      ((b.enlarge K hK Set.subset_union_right).boundary.linearEquiv x z)) ha).trans
        (congrArg (g₀.linearEquiv x) hb)
    let wa := ((a.congr e₀ f₀).enlarge K hK Set.subset_union_left).boundary.linearEquiv x v
    have ha' := ((a.congr e₀ f₀).enlarge_apply K hK Set.subset_union_left x v).trans
      (a.congr_apply e₀ f₀ xa v)
    have hb' := ((b.congr f₀ g₀).enlarge_apply K hK Set.subset_union_right x wa).trans
      (b.congr_apply f₀ g₀ xb wa)
    have hright := hb'.trans (congrArg (fun z ↦ g₀.linearEquiv x
      (b.boundary.linearEquiv xb (f₀.symm.linearEquiv x z))) ha')
    have hcancel : f₀.symm.linearEquiv x (f₀.linearEquiv x u) = u :=
      (f₀.linearEquiv x).symm_apply_apply u
    exact hleft.trans ((hright.trans (congrArg (fun z ↦ g₀.linearEquiv x
      (b.boundary.linearEquiv xb z)) hcancel)).symm)
  change (SupportBundleTriple.ofBoundary (smallBundle E) (smallBundle G)
    ((a.compose b).congr e₀ g₀)).compactSupportClass = _
  rw [hboundary]
  exact supportBundleTriple_compactSupportClass_compose _ _ _ _ _

attribute [local instance] sumTopology isFiniteRank_sum

/-- Direct sum of arbitrary-universe triples adds the actual support classes. -/
theorem CompactSupportTriple.compactSupportClass_sum (a : CompactSupportTriple E F)
    (b : CompactSupportTriple G H) :
    (a.sum b).compactSupportClass = a.compactSupportClass + b.compactSupportClass := by
  /- Use sums of the two chosen small models as models of the summed fibers. The sum of the
  resizing isomorphisms retains the componentwise original boundary. Apply the bundled sum
  formula and independence of model. -/
  let e₀ := smallBundleIso E
  let f₀ := smallBundleIso F
  let g₀ := smallBundleIso G
  let h₀ := smallBundleIso H
  have hboundary : (a.sum b).congr (e₀.sum g₀) (f₀.sum h₀) =
      (a.congr e₀ f₀).sum (b.congr g₀ h₀) := by
    change CompactSupportTriple.mk _ _ _ = CompactSupportTriple.mk _ _ _
    congr 1
    dsimp only [CompactSupportTriple.congr, CompactSupportTriple.sum]
    refine @Iso.ext ((a.control ∪ b.control)ᶜ : Set X) _
      (Restrict ((smallBundle E).Fiber ×ᵇ (smallBundle G).Fiber) (a.control ∪ b.control)ᶜ)
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) _
      (Restrict ((smallBundle F).Fiber ×ᵇ (smallBundle H).Fiber) (a.control ∪ b.control)ᶜ)
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) _ _ _ ?_
    intro x
    change ((a.control ∪ b.control)ᶜ : Set X) at x
    refine DFunLike.ext _ _ ?_
    intro v
    change (smallBundle E).Fiber x × (smallBundle G).Fiber x at v
    -- Both sum comparisons preserve the ordered pair of original fiber vectors.
    let K := a.control ∪ b.control
    have hK : IsCompact K := a.isCompact_control.union b.isCompact_control
    let xa : (a.controlᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inl hx)⟩
    let xb : (b.controlᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inr hx)⟩
    let w : E x × G x := (e₀.symm.linearEquiv x v.1, g₀.symm.linearEquiv x v.2)
    have hl := (RelativeTriple.sum_apply
      (a.enlarge K hK Set.subset_union_left).boundary
      (b.enlarge K hK Set.subset_union_right).boundary x w).trans
        (congrArg₂ Prod.mk (a.enlarge_apply K hK Set.subset_union_left x w.1)
          (b.enlarge_apply K hK Set.subset_union_right x w.2))
    have ha := ((a.congr e₀ f₀).enlarge_apply K hK Set.subset_union_left x v.1).trans
      (a.congr_apply e₀ f₀ xa v.1)
    have hb := ((b.congr g₀ h₀).enlarge_apply K hK Set.subset_union_right x v.2).trans
      (b.congr_apply g₀ h₀ xb v.2)
    have hr := (RelativeTriple.sum_apply
      ((a.congr e₀ f₀).enlarge K hK Set.subset_union_left).boundary
      ((b.congr g₀ h₀).enlarge K hK Set.subset_union_right).boundary x v).trans
        (congrArg₂ Prod.mk ha hb)
    exact (congrArg ((f₀.sum h₀).linearEquiv x) hl).trans hr.symm
  have hmodel := (a.sum b).compactSupportClass_eq_model
    ((smallBundle E).sum (smallBundle G)) ((smallBundle F).sum (smallBundle H))
    (e₀.sum g₀) (f₀.sum h₀)
  rw [hboundary] at hmodel
  exact hmodel.trans (a.toSupportBundleTriple.compactSupportClass_sum b.toSupportBundleTriple)

variable {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

attribute [local instance] isFiniteRank_pullback

/-- Proper pullback retains the original support-class naturality. -/
theorem CompactSupportTriple.compactSupportClass_pullback (a : CompactSupportTriple E F)
    (f : C(Y, X)) (hf : IsProperMap f) :
    (a.pullback f hf).compactSupportClass =
      compactSupportKZeroPullback f hf a.compactSupportClass := by
  /- Pull the chosen small models and their isomorphisms back by f. They give alternative
  models of the pulled-back original bundles. The inverse-image control is compact by
  properness, and bundled naturality finishes the comparison. -/
  let e₀ := smallBundleIso E
  let f₀ := smallBundleIso F
  have hboundary : (a.pullback f hf).congr (e₀.pullback f) (f₀.pullback f) =
      (a.congr e₀ f₀).pullback f hf := by
    change CompactSupportTriple.mk _ _ _ = CompactSupportTriple.mk _ _ _
    congr 1
    dsimp only [CompactSupportTriple.congr, CompactSupportTriple.pullback]
    refine @Iso.ext (f ⁻¹' a.controlᶜ : Set Y) _
      (Restrict ((f : Y → X) *ᵖ (smallBundle E).Fiber) (f ⁻¹' a.controlᶜ))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) _
      (Restrict ((f : Y → X) *ᵖ (smallBundle F).Fiber) (f ⁻¹' a.controlᶜ))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) _ _ _ ?_
    intro y
    change (f ⁻¹' a.controlᶜ : Set Y) at y
    refine DFunLike.ext _ _ ?_
    intro v
    change (smallBundle E).Fiber (f y) at v
    -- The comparison evaluates the original square at exactly f(y).
    let x : (a.controlᶜ : Set X) := ⟨f y, y.property⟩
    have hl := congrArg (f₀.linearEquiv (f y))
      (RelativeTriple.pullback_apply a.boundary f y (e₀.symm.linearEquiv (f y) v))
    have hr := (RelativeTriple.pullback_apply (a.congr e₀ f₀).boundary f y v).trans
      (a.congr_apply e₀ f₀ x v)
    exact hl.trans hr.symm
  have hmodel := (a.pullback f hf).compactSupportClass_eq_model
    ((smallBundle E).pullback f) ((smallBundle F).pullback f)
    (e₀.pullback f) (f₀.pullback f)
  rw [hboundary] at hmodel
  exact hmodel.trans (a.toSupportBundleTriple.compactSupportClass_pullback f hf)

end AtiyahSinger.ComplexBundle

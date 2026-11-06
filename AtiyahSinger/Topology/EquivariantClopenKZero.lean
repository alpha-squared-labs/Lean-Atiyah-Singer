/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantOpenExtension
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality
public import Mathlib.Topology.Sets.Opens

/-!
# Equivariant compact-support K theory on a finite invariant clopen partition

Public module ID: M1770.

The forward map restricts the original equivariant support class along the
actual proper subtype inclusions. The supplied actions on these open subtypes
are required to agree with the same ambient G action under their inclusions.
For a finite disjoint cover by closed open subspaces, these restrictions give
an additive equivalence with the product of the original support groups.

Sources: Karoubi II.1.26, printed pp.56--57, gives the ordinary compact-space
finite-decomposition theorem; II.1.28--1.29 explain its use for varying ranks.
ASI I, Section 2, printed pp.494--495, gives the equivariant bundle framework.
The compact-support and equivariant version here is the direct presentation
argument: extend each bundle by the zero bundle on the clopen complement and
glue the original actions and boundary maps. This argument uses only finite
unions of the specified compact controls and the three original relations.

Neither compactness of G, local compactness or Hausdorffness of X, nor a stable
comparison theorem is assumed. Empty pieces and an empty index type are allowed.
No general equivariant extension across the boundary of an arbitrary open set,
global fixed-rank realization or invariance of connected components is asserted.
The decomposition is proved by the actual zero-extension and finite-assembly constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open TopologicalSpace

/-! The following private constructions implement zero extension and finite reconstruction. -/

section ClopenExtension

open Bundle

attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X]

/-- Zero extension uses the original fiber on the piece and the unique zero fiber outside it. -/
@[reducible] private def ClopenExtensionFiber (U : Set X) (E : U → Type) (x : X) : Type :=
  ∀ h : PLift (x ∈ U), E ⟨x, h.down⟩

/-- Separate the original total space and the zero fibers over the complement. -/
private def clopenExtensionTotalEquiv (U : Set X) (E : U → Type) :
    TotalSpace Unit (ClopenExtensionFiber U E) ≃ (TotalSpace Unit E ⊕ (Uᶜ : Set X)) where
  toFun z := if h : z.proj ∈ U then .inl ⟨⟨z.proj, h⟩, z.snd ⟨h⟩⟩ else .inr ⟨z.proj, h⟩
  invFun z := match z with
    | .inl z => ⟨z.proj.val, fun _ ↦ z.snd⟩
    | .inr x => ⟨x.val, fun h ↦ False.elim (x.property h.down)⟩
  left_inv z := by
    by_cases h : z.proj ∈ U
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h]
      apply congrArg (fun v : ClopenExtensionFiber U E z.proj ↦
        (⟨z.proj, v⟩ : TotalSpace Unit (ClopenExtensionFiber U E)))
      funext hx
      exact (h hx.down).elim
  right_inv z := by
    cases z with
    | inl z => simp only [dite_eq_left z.proj.property]
    | inr x => simp only [dite_eq_right x.property]

/-- Transport the actual disjoint-sum topology to the extended total space. -/
@[instance_reducible] private def clopenExtensionTopology (U : Set X) (E : U → Type)
    [TopologicalSpace (TotalSpace Unit E)] :
    TopologicalSpace (TotalSpace Unit (ClopenExtensionFiber U E)) :=
  TopologicalSpace.induced (clopenExtensionTotalEquiv U E) inferInstance

attribute [local instance] clopenExtensionTopology

/-- The specified extension topology identifies the two open-and-closed total-space pieces. -/
private def clopenExtensionTotalHomeomorph (U : Set X) (E : U → Type)
    [TopologicalSpace (TotalSpace Unit E)] :
    TotalSpace Unit (ClopenExtensionFiber U E) ≃ₜ (TotalSpace Unit E ⊕ (Uᶜ : Set X)) where
  __ := clopenExtensionTotalEquiv U E
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr <| by
    simpa using (continuous_id : Continuous (id : _ → TotalSpace Unit E ⊕ (Uᶜ : Set X)))

/-- The original projection and complement inclusion give the extended continuous projection. -/
private theorem continuous_clopenExtension_proj (U : Set X) (E : U → Type)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] :
    Continuous (π Unit (ClopenExtensionFiber U E)) := by
  have h := ((continuous_subtype_val.comp (continuous_proj (E := E))).sumElim
    continuous_subtype_val).comp (clopenExtensionTotalHomeomorph U E).continuous
  apply h.congr
  intro z
  by_cases hU : z.proj ∈ U <;>
    simp [clopenExtensionTotalHomeomorph, clopenExtensionTotalEquiv, hU]

/-- Keep the original linear charts on the piece and zero-dimensional charts on its complement. -/
private theorem isFiniteRank_clopenExtension (U : Set X) (hU : IsClopen U) (E : U → Type)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] :
    IsFiniteRank (ClopenExtensionFiber U E) := by
  classical
  -- Work with the actual original total space on each of the two clopen pieces.
  let T := TotalSpace Unit (ClopenExtensionFiber U E)
  have hp := continuous_clopenExtension_proj U E
  let q : (π Unit (ClopenExtensionFiber U E) ⁻¹' U) ≃ₜ TotalSpace Unit E :=
    { toFun z := ⟨⟨z.val.proj, z.property⟩, z.val.snd ⟨z.property⟩⟩
      invFun z := ⟨⟨z.proj.val, fun _ ↦ z.snd⟩, z.proj.property⟩
      left_inv z := by cases z; rfl
      right_inv z := rfl
      continuous_toFun := by
        apply (Topology.IsEmbedding.inl (Y := (Uᶜ : Set X))).continuous_iff.mpr
        apply ((clopenExtensionTotalHomeomorph U E).continuous.comp continuous_subtype_val).congr
        intro z
        have hz : z.val.proj ∈ U := z.property
        simp [clopenExtensionTotalHomeomorph, clopenExtensionTotalEquiv, hz]
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply continuous_induced_rng.mpr
        apply (continuous_inl : Continuous (Sum.inl : TotalSpace Unit E →
          TotalSpace Unit E ⊕ (Uᶜ : Set X))).congr
        intro z
        simp [clopenExtensionTotalEquiv, z.proj.property] }
  let : TopologicalSpace (TotalSpace Unit (Bundle.Trivial (Uᶜ : Set X) (Fin 0 → ℂ))) :=
    trivialTopology 0
  let q₀ : (π Unit (ClopenExtensionFiber U E) ⁻¹' Uᶜ) ≃ₜ
      TotalSpace Unit (Bundle.Trivial (Uᶜ : Set X) (Fin 0 → ℂ)) :=
    { toFun z := ⟨⟨z.val.proj, z.property⟩, 0⟩
      invFun z := ⟨⟨z.proj.val, fun h ↦ False.elim (z.proj.property h.down)⟩, z.proj.property⟩
      left_inv z := by
        apply Subtype.ext
        apply congrArg (fun v : ClopenExtensionFiber U E z.val.proj ↦
          (⟨z.val.proj, v⟩ : T))
        funext h
        exact (z.property h.down).elim
      right_inv z := by
        apply congrArg (fun v : Fin 0 → ℂ ↦
          (⟨z.proj, v⟩ : TotalSpace Unit (Bundle.Trivial (Uᶜ : Set X) (Fin 0 → ℂ))))
        exact Subsingleton.elim _ _
      continuous_toFun := continuous_induced_rng.mpr
        (((hp.comp continuous_subtype_val).subtype_mk _).prodMk continuous_const)
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply continuous_induced_rng.mpr
        have hc : Continuous (fun z :
            TotalSpace Unit (Bundle.Trivial (Uᶜ : Set X) (Fin 0 → ℂ)) ↦ (z.proj, z.snd)) :=
          continuous_induced_dom
        apply (continuous_inr.comp hc.fst).congr
        intro z
        have hz : z.proj.val ∉ U := z.proj.property
        simp [clopenExtensionTotalEquiv, hz] }
  -- Extend a chart only across its own open piece; ranks may vary from point to point.
  constructor
  intro x
  by_cases hx : x ∈ U
  · obtain ⟨r, e, he, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) ⟨x, hx⟩
    let t := ((e.compHomeomorph q).codExtend hU.isOpen ⟨x, hx⟩).domExtend
      (hU.isOpen.preimage hp)
    refine ⟨r, t, ?_, ?_⟩
    · exact ⟨⟨x, hx⟩, he, rfl⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have heval (v : ClopenExtensionFiber U E z.val) :
          (t ⟨z.val, v⟩).2 = (e ⟨z, v ⟨z.property⟩⟩).2 := by
        change ((if h : z.val ∈ U then _ else _) : X × (Fin r → ℂ)).2 = _
        rw [dite_eq_left z.property]
        rfl
      constructor
      · intro v w
        rw [heval, heval, heval]
        exact (hlinear z hz).map_add _ _
      · intro c v
        rw [heval, heval]
        exact (hlinear z hz).map_smul _ _
  · let := isFiniteRank_trivial (X := (Uᶜ : Set X)) 0
    obtain ⟨r, e, he, hlinear⟩ := IsFiniteRank.exists_linear_trivialization
      (E := Bundle.Trivial (Uᶜ : Set X) (Fin 0 → ℂ)) ⟨x, hx⟩
    let t := ((e.compHomeomorph q₀).codExtend hU.isClosed.isOpen_compl ⟨x, hx⟩).domExtend
      (hU.isClosed.isOpen_compl.preimage hp)
    refine ⟨r, t, ?_, ?_⟩
    · exact ⟨⟨x, hx⟩, he, rfl⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have heval (v : ClopenExtensionFiber U E z.val) :
          (t ⟨z.val, v⟩).2 = (e ⟨z, 0⟩).2 := by
        simp only [t, Trivialization.toFun', Trivialization.domExtend,
          Pretrivialization.domExtend]
        rw [dite_eq_left z.property]
        rfl
      have hzero (v : ClopenExtensionFiber U E z.val) : (t ⟨z.val, v⟩).2 = 0 :=
        (heval v).trans (hlinear z hz).map_zero
      constructor
      · intro v w
        simp only [hzero, add_zero]
      · intro c v
        simp only [hzero, smul_zero]

/-- Package zero extension with these original local charts and transported topology. -/
@[reducible] private def clopenExtensionBundle (U : Set X) (hU : IsClopen U)
    (E : FiniteBundle U) : FiniteBundle X where
  Fiber := ClopenExtensionFiber U E.Fiber
  isFiniteRank := isFiniteRank_clopenExtension U hU E.Fiber

/-- Identify native pullback restriction with the corresponding subtype of the original total
space. -/
private def restrictionTotalHomeomorph {B : Type*} [TopologicalSpace B]
    (E : B → Type*) [TopologicalSpace (TotalSpace Unit E)]
    (hp : Continuous (π Unit E)) (A : Set B) :
    TotalSpace Unit (Restrict E A) ≃ₜ {z : TotalSpace Unit E // z.proj ∈ A} where
  toFun z := ⟨⟨z.proj.val, z.snd⟩, z.proj.property⟩
  invFun z := ⟨⟨z.val.proj, z.property⟩, z.val.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (Pullback.continuous_lift Unit E
    (Subtype.val : A → B)).subtype_mk _
  continuous_invFun := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E
      (Subtype.val : A → B)).continuous_iff]
    exact ((hp.comp continuous_subtype_val).subtype_mk _).prodMk continuous_subtype_val

/-- Separate the original exterior and the complementary zero fibers without assuming closed
control. -/
private def clopenExtensionExteriorEquiv (U : Set X) (E : U → Type) (C : Set U) :
    TotalSpace Unit (Restrict (ClopenExtensionFiber U E) (Subtype.val '' C)ᶜ) ≃
      (TotalSpace Unit (Restrict E Cᶜ) ⊕ (Uᶜ : Set X)) where
  toFun z := if h : z.proj.val ∈ U then
    .inl ⟨⟨⟨z.proj.val, h⟩,
      fun hC ↦ z.proj.property ⟨⟨z.proj.val, h⟩, hC, rfl⟩⟩, z.snd ⟨h⟩⟩
    else .inr ⟨z.proj.val, h⟩
  invFun z := match z with
    | .inl z => ⟨⟨z.proj.val.val, by
        rintro ⟨x, hx, heq⟩
        exact z.proj.property ((Subtype.ext heq) ▸ hx)⟩, fun _ ↦ z.snd⟩
    | .inr x => ⟨⟨x.val, by
        rintro ⟨y, _, heq⟩
        exact x.property (heq ▸ y.property)⟩,
          fun h ↦ False.elim (x.property h.down)⟩
  left_inv z := by
    by_cases h : z.proj.val ∈ U
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h]
      apply congrArg (fun v : ClopenExtensionFiber U E z.proj.val ↦
        (⟨z.proj, v⟩ :
          TotalSpace Unit (Restrict (ClopenExtensionFiber U E) (Subtype.val '' C)ᶜ)))
      funext hx
      exact (h hx.down).elim
  right_inv z := by
    cases z with
    | inl z => simp only [dite_eq_left z.proj.val.property]
    | inr x => simp only [dite_eq_right x.property]

/-- The specified exterior decomposition preserves the native restriction topology in both
directions. -/
private def clopenExtensionExteriorHomeomorph (U : Set X) (E : U → Type)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] (C : Set U) :
    TotalSpace Unit (Restrict (ClopenExtensionFiber U E) (Subtype.val '' C)ᶜ) ≃ₜ
      (TotalSpace Unit (Restrict E Cᶜ) ⊕ (Uᶜ : Set X)) where
  __ := clopenExtensionExteriorEquiv U E C
  continuous_toFun := by
    let lift (z : TotalSpace Unit (Restrict E Cᶜ)) : TotalSpace Unit E :=
      ⟨z.proj.val, z.snd⟩
    have hlift : Topology.IsInducing lift :=
      Topology.IsEmbedding.subtypeVal.isInducing.comp
        (restrictionTotalHomeomorph E (continuous_proj (E := E)) Cᶜ).isInducing
    have hleft : Topology.IsInducing (fun z ↦ (Sum.inl (lift z) :
        TotalSpace Unit E ⊕ (Uᶜ : Set X))) :=
      Topology.IsEmbedding.inl.isInducing.comp hlift
    have hright : Topology.IsInducing (Sum.inr : (Uᶜ : Set X) →
        TotalSpace Unit E ⊕ (Uᶜ : Set X)) := Topology.IsEmbedding.inr.isInducing
    have hsep : Disjoint
        (Set.range (Sum.inl : TotalSpace Unit E → TotalSpace Unit E ⊕ (Uᶜ : Set X)))
        (Set.range (Sum.inr : (Uᶜ : Set X) → TotalSpace Unit E ⊕ (Uᶜ : Set X))) :=
      Set.disjoint_left.mpr (by rintro _ ⟨_, rfl⟩ ⟨_, h⟩; cases h)
    have hrange : Set.range (fun z ↦ (Sum.inl (lift z) :
        TotalSpace Unit E ⊕ (Uᶜ : Set X))) ⊆ Set.range Sum.inl := by
      rintro _ ⟨z, rfl⟩
      exact ⟨lift z, rfl⟩
    have hi := hleft.sumElim hright
      (hsep.mono_left ((closure_mono hrange).trans_eq isClosed_range_inl.closure_eq))
      (by simpa only [isClosed_range_inr.closure_eq] using hsep.mono_left hrange)
    apply hi.continuous_iff.mpr
    apply ((clopenExtensionTotalHomeomorph U E).continuous.comp
      (Pullback.continuous_lift Unit (ClopenExtensionFiber U E)
        (Subtype.val : ((Subtype.val '' C)ᶜ : Set X) → X))).congr
    intro z
    by_cases hx : z.proj.val ∈ U <;>
      simp [clopenExtensionTotalHomeomorph, clopenExtensionTotalEquiv,
        clopenExtensionExteriorEquiv, hx, lift, Pullback.lift]
  continuous_invFun := by
    apply continuous_sum_dom.mpr
    constructor
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit (ClopenExtensionFiber U E)
        (Subtype.val : ((Subtype.val '' C)ᶜ : Set X) → X)).continuous_iff]
      apply Continuous.prodMk
      · exact (continuous_subtype_val.comp (continuous_subtype_val.comp
          (Pullback.continuous_proj Unit E (Subtype.val : (Cᶜ : Set U) → U)))).subtype_mk _
      · apply continuous_induced_rng.mpr
        apply (continuous_inl.comp
          (Pullback.continuous_lift Unit E (Subtype.val : (Cᶜ : Set U) → U))).congr
        intro z
        simp [clopenExtensionTotalEquiv, clopenExtensionExteriorEquiv, z.proj.val.property]
        rfl
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit (ClopenExtensionFiber U E)
        (Subtype.val : ((Subtype.val '' C)ᶜ : Set X) → X)).continuous_iff]
      apply Continuous.prodMk
      · exact continuous_subtype_val.subtype_mk _
      · apply continuous_induced_rng.mpr
        apply continuous_inr.congr
        intro x
        have hx : x.val ∉ U := x.property
        simp [clopenExtensionTotalEquiv, clopenExtensionExteriorEquiv, hx]

/-- Extend the same exterior isomorphism pointwise and use the unique maps on zero fibers. -/
private def clopenExtensionExteriorIso (U : Set X) (E F : FiniteBundle U)
    (C : Set U) (e : Iso (Restrict E.Fiber Cᶜ) (Restrict F.Fiber Cᶜ)) :
    Iso (Restrict (ClopenExtensionFiber U E.Fiber) (Subtype.val '' C)ᶜ)
      (Restrict (ClopenExtensionFiber U F.Fiber) (Subtype.val '' C)ᶜ) where
  linearEquiv x := LinearEquiv.piCongrRight fun h : PLift (x.val ∈ U) ↦
    e.linearEquiv ⟨⟨x.val, h.down⟩, fun hC ↦ x.property ⟨⟨x.val, h.down⟩, hC, rfl⟩⟩
  continuous_total := by
    have hc := (clopenExtensionExteriorHomeomorph U F.Fiber C).symm.continuous.comp
      ((e.continuous_total.sumMap continuous_id).comp
        (clopenExtensionExteriorHomeomorph U E.Fiber C).continuous)
    apply hc.congr
    intro z
    by_cases hx : z.proj.val ∈ U
    · simp [clopenExtensionExteriorHomeomorph, clopenExtensionExteriorEquiv, hx]
      rfl
    · simp only [Function.comp_apply]
      change (clopenExtensionExteriorEquiv U F.Fiber C).symm
        (Sum.map _ id ((clopenExtensionExteriorEquiv U E.Fiber C) z)) = _
      simp only [clopenExtensionExteriorEquiv, Equiv.coe_fn_mk, dite_eq_right hx, Sum.map_inr]
      apply congrArg (fun v : ClopenExtensionFiber U F.Fiber z.proj.val ↦
        (⟨z.proj, v⟩ : TotalSpace Unit
          (Restrict (ClopenExtensionFiber U F.Fiber) (Subtype.val '' C)ᶜ)))
      funext h
      exact (hx h.down).elim
  continuous_symm := by
    have hc := (clopenExtensionExteriorHomeomorph U E.Fiber C).symm.continuous.comp
      ((e.continuous_symm.sumMap continuous_id).comp
        (clopenExtensionExteriorHomeomorph U F.Fiber C).continuous)
    apply hc.congr
    intro z
    by_cases hx : z.proj.val ∈ U
    · simp [clopenExtensionExteriorHomeomorph, clopenExtensionExteriorEquiv, hx]
      rfl
    · simp only [Function.comp_apply]
      change (clopenExtensionExteriorEquiv U E.Fiber C).symm
        (Sum.map _ id ((clopenExtensionExteriorEquiv U F.Fiber C) z)) = _
      simp only [clopenExtensionExteriorEquiv, Equiv.coe_fn_mk, dite_eq_right hx, Sum.map_inr]
      apply congrArg (fun v : ClopenExtensionFiber U E.Fiber z.proj.val ↦
        (⟨z.proj, v⟩ : TotalSpace Unit
          (Restrict (ClopenExtensionFiber U E.Fiber) (Subtype.val '' C)ᶜ)))
      funext h
      exact (hx h.down).elim

/-- Zero extension retains exactly the image of the original compact control. -/
@[reducible] private def clopenExtensionSupportTriple (U : Set X)
    (E F : FiniteBundle U) (a : CompactSupportTriple E.Fiber F.Fiber) :
    CompactSupportTriple (ClopenExtensionFiber U E.Fiber) (ClopenExtensionFiber U F.Fiber) where
  control := Subtype.val '' a.control
  isCompact_control := a.isCompact_control.image continuous_subtype_val
  boundary := clopenExtensionExteriorIso U E F a.control a.boundary

/-- Extend an original continuous bundle map by the unique map on the complementary zero fibers. -/
private def clopenExtensionHom (U : Set X) {E F : U → Type}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] (f : Hom E F) :
    Hom (ClopenExtensionFiber U E) (ClopenExtensionFiber U F) where
  linearMap x :=
    { toFun v hx := f.linearMap ⟨x, hx.down⟩ (v hx)
      map_add' v w := by
        funext hx
        exact (f.linearMap ⟨x, hx.down⟩).map_add (v hx) (w hx)
      map_smul' c v := by
        funext hx
        exact (f.linearMap ⟨x, hx.down⟩).map_smul c (v hx) }
  continuous_total := by
    -- On the original summand apply the supplied map, and retain the complement's zero vector.
    have hc := (clopenExtensionTotalHomeomorph U F).symm.continuous.comp
      ((f.continuous_total.sumMap continuous_id).comp
        (clopenExtensionTotalHomeomorph U E).continuous)
    apply hc.congr
    intro z
    by_cases hz : z.proj ∈ U
    · simp [clopenExtensionTotalHomeomorph, clopenExtensionTotalEquiv, hz]
    · simp only [Function.comp_apply]
      change (clopenExtensionTotalEquiv U F).symm
        (Sum.map _ id ((clopenExtensionTotalEquiv U E) z)) = _
      simp only [clopenExtensionTotalEquiv, Equiv.coe_fn_mk, dite_eq_right hz, Sum.map_inr]
      apply congrArg (fun v : ClopenExtensionFiber U F z.proj ↦
        (⟨z.proj, v⟩ : TotalSpace Unit (ClopenExtensionFiber U F)))
      funext hx
      exact (hz hx.down).elim

/-- Extend both directions of the same original bundle isomorphism. -/
private def clopenExtensionIso (U : Set X) {E F : U → Type}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] (e : Iso E F) :
    Iso (ClopenExtensionFiber U E) (ClopenExtensionFiber U F) where
  linearEquiv x :=
    { toFun v hx := e.linearEquiv ⟨x, hx.down⟩ (v hx)
      invFun v hx := (e.linearEquiv ⟨x, hx.down⟩).symm (v hx)
      left_inv v := by
        funext hx
        exact (e.linearEquiv ⟨x, hx.down⟩).symm_apply_apply (v hx)
      right_inv v := by
        funext hx
        exact (e.linearEquiv ⟨x, hx.down⟩).apply_symm_apply (v hx)
      map_add' v w := by
        funext hx
        exact (e.linearEquiv ⟨x, hx.down⟩).map_add (v hx) (w hx)
      map_smul' c v := by
        funext hx
        exact (e.linearEquiv ⟨x, hx.down⟩).map_smul c (v hx) }
  continuous_total := (clopenExtensionHom U e.toHom).continuous_total
  continuous_symm := (clopenExtensionHom U e.symm.toHom).continuous_total

attribute [local instance] sumTopology isFiniteRank_sum

/-- Split original fiber pairs under zero extension, preserving the actual forward coordinates. -/
private def clopenExtensionSumIso (U : Set X) (hU : IsClopen U) (E F : U → Type)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F] :
    Iso (ClopenExtensionFiber U (E ×ᵇ F))
      (ClopenExtensionFiber U E ×ᵇ ClopenExtensionFiber U F) := by
  let := isFiniteRank_clopenExtension U hU E
  let := isFiniteRank_clopenExtension U hU F
  let := isFiniteRank_clopenExtension U hU (E ×ᵇ F)
  -- Split each actual pair on U and retain the unique zero vector on its complement.
  let c (x : X) : ClopenExtensionFiber U (E ×ᵇ F) x ≃ₗ[ℂ]
      (ClopenExtensionFiber U E x × ClopenExtensionFiber U F x) :=
    { toFun v := (fun hx ↦ (v hx).1, fun hx ↦ (v hx).2)
      invFun v hx := (v.1 hx, v.2 hx)
      left_inv v := by
        funext hx
        rfl
      right_inv v := by
        cases v
        rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let f : Hom (ClopenExtensionFiber U (E ×ᵇ F))
      (ClopenExtensionFiber U E ×ᵇ ClopenExtensionFiber U F) :=
    { linearMap x := (c x).toLinearMap
      continuous_total := by
        -- The specified pair of extensions is continuous in the original sum topology.
        exact continuous_induced_rng.mpr
          ((clopenExtensionHom U (sumFst (E := E) (F := F))).continuous_total.prodMk
            (clopenExtensionHom U (sumSnd (E := E) (F := F))).continuous_total) }
  -- The existing inverse theorem preserves this exact forward fiber map.
  exact f.toIso (fun x ↦ (c x).bijective)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X]

omit [TopologicalSpace X] [TopologicalSpace G] [IsTopologicalGroup G]
  [ContinuousSMul G X] in
/-- The subtype action makes membership invariant under the original ambient action. -/
private theorem clopen_smul_mem_iff (U : Set X) [MulAction G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (g : G) (x : X) : g • x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    have ht := (g⁻¹ • (⟨g • x, hx⟩ : U)).property
    rw [heq, inv_smul_smul] at ht
    exact ht
  · intro hx
    have ht := (g • (⟨x, hx⟩ : U)).property
    rw [heq] at ht
    exact ht

/-- The original moving-fiber map, transported only along the supplied inclusion equality. -/
private def clopenExtensionActionLinearMap (U : Set X) [MulAction G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (E : FiniteBundle U) [ContinuousSMul G U] (ρ : EquivariantStructure G E.Fiber)
    (g : G) (x : X) :
    ClopenExtensionFiber U E.Fiber x →ₗ[ℂ] ClopenExtensionFiber U E.Fiber (g • x) :=
  LinearMap.pi fun hy ↦
    let hx := (clopen_smul_mem_iff U heq g x).mp hy.down
    (LinearEquiv.cast (R := ℂ) (M := E.Fiber)
      (show g • (⟨x, hx⟩ : U) = ⟨g • x, hy.down⟩ from
        Subtype.ext (heq g ⟨x, hx⟩))).toLinearMap.comp
          ((ρ.linearMap g ⟨x, hx⟩).comp (LinearMap.proj ⟨hx⟩))

/-- Extend the original action by the unique linear action on the zero fibers. -/
private def clopenExtensionAction (U : Set X) [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (E : FiniteBundle U) (ρ : EquivariantStructure G E.Fiber) :
    EquivariantStructure G (ClopenExtensionFiber U E.Fiber) := by
  classical
  let T := TotalSpace Unit (ClopenExtensionFiber U E.Fiber)
  let q := clopenExtensionTotalHomeomorph U E.Fiber
  let L := clopenExtensionActionLinearMap U heq E ρ
  let act (g : G) : TotalSpace Unit E.Fiber ⊕ (Uᶜ : Set X) →
      TotalSpace Unit E.Fiber ⊕ (Uᶜ : Set X) :=
    Sum.elim (fun z ↦ .inl ⟨g • z.proj, ρ.linearMap g z.proj z.snd⟩)
      (fun x ↦ .inr ⟨g • x.val, fun hx ↦ x.property
        ((clopen_smul_mem_iff U heq g x.val).mp hx)⟩)
  -- The inclusion equality changes the target label, not the original total vector.
  have hcast {x y : U} (hxy : x = y) (v : E.Fiber x) :
      (⟨y, LinearEquiv.cast (R := ℂ) (M := E.Fiber) hxy v⟩ :
        TotalSpace Unit E.Fiber) = ⟨x, v⟩ := by
    subst y
    rfl
  have hlift (g : G) (x : X) (v : ClopenExtensionFiber U E.Fiber x) :
      q (⟨g • x, L g x v⟩ : T) = act g (q ⟨x, v⟩) := by
    change clopenExtensionTotalEquiv U E.Fiber ⟨g • x, L g x v⟩ =
      act g (clopenExtensionTotalEquiv U E.Fiber ⟨x, v⟩)
    by_cases hx : x ∈ U
    · have hgx := (clopen_smul_mem_iff U heq g x).mpr hx
      simp only [clopenExtensionTotalEquiv, Equiv.coe_fn_mk, dite_eq_left hx, dite_eq_left hgx,
        act, Sum.elim_inl]
      congr 1
      exact hcast (show g • (⟨x, hx⟩ : U) = ⟨g • x, hgx⟩ from
        Subtype.ext (heq g ⟨x, hx⟩)) (ρ.linearMap g ⟨x, hx⟩ (v ⟨hx⟩))
    · have hgx : g • x ∉ U := fun h ↦ hx ((clopen_smul_mem_iff U heq g x).mp h)
      simp only [clopenExtensionTotalEquiv, Equiv.coe_fn_mk, dite_eq_right hx, dite_eq_right hgx,
        act, Sum.elim_inr]
  -- Conjugation by the same sum homeomorphism preserves both action laws.
  refine { linearMap := L, one_map := ?_, mul_map := ?_, continuous_action := ?_ }
  · intro x v
    apply q.injective
    rw [hlift]
    cases q (⟨x, v⟩ : T) with
    | inl z => exact congrArg Sum.inl (ρ.one_map z.proj z.snd)
    | inr x => exact congrArg Sum.inr (Subtype.ext (one_smul G x.val))
  · intro g h x v
    apply q.injective
    rw [hlift, hlift, hlift]
    cases q (⟨x, v⟩ : T) with
    | inl z => exact congrArg Sum.inl (ρ.mul_map g h z.proj z.snd)
    | inr x => exact congrArg Sum.inr (Subtype.ext (mul_smul g h x.val))
  · -- Both sum components are jointly continuous; retain the chosen total topology.
    have hact : Continuous (fun p : G × (TotalSpace Unit E.Fiber ⊕ (Uᶜ : Set X)) ↦
        act p.1 p.2) := by
      let d : G × (TotalSpace Unit E.Fiber ⊕ (Uᶜ : Set X)) ≃ₜ
          (G × TotalSpace Unit E.Fiber) ⊕ (G × (Uᶜ : Set X)) := Homeomorph.prodSumDistrib
      have hout : Continuous (fun p : G × (Uᶜ : Set X) ↦
          (⟨p.1 • p.2.val, fun hx ↦ p.2.property
            ((clopen_smul_mem_iff U heq p.1 p.2.val).mp hx)⟩ : (Uᶜ : Set X))) :=
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      have hc : Continuous (Sum.elim
          (fun p : G × TotalSpace Unit E.Fiber ↦
            (Sum.inl ⟨p.1 • p.2.proj, ρ.linearMap p.1 p.2.proj p.2.snd⟩ :
              TotalSpace Unit E.Fiber ⊕ (Uᶜ : Set X)))
          (fun p : G × (Uᶜ : Set X) ↦
            (Sum.inr ⟨p.1 • p.2.val, fun hx ↦ p.2.property
              ((clopen_smul_mem_iff U heq p.1 p.2.val).mp hx)⟩ :
                TotalSpace Unit E.Fiber ⊕ (Uᶜ : Set X)))) :=
        (continuous_inl.comp ρ.continuous_action).sumElim (continuous_inr.comp hout)
      apply (hc.comp d.continuous).congr
      intro p
      rcases p with ⟨g, z | x⟩ <;> rfl
    apply continuous_induced_rng.mpr
    apply (hact.comp (continuous_fst.prodMk (q.continuous.comp continuous_snd))).congr
    intro p
    exact (hlift p.1 p.2.proj p.2.snd).symm

/-- Extend the original triple, actions and exterior square with the same compact image control. -/
private def clopenExtensionEquivariantTriple (U : Set X) (hU : IsClopen U)
    [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (a : EquivariantSupportBundleTriple G U) : EquivariantSupportBundleTriple G X := by
  -- Retain the original bundles, control and two actions inside the specified piece.
  let E := clopenExtensionBundle U hU a.1.source
  let F := clopenExtensionBundle U hU a.1.target
  let b := clopenExtensionSupportTriple U a.1.source a.1.target a.1.datum
  let ρE := clopenExtensionAction U heq a.1.source a.2.sourceAction
  let ρF := clopenExtensionAction U heq a.1.target a.2.targetAction
  have hinv : ∀ (g : G) (x : X), g • x ∈ b.control ↔ x ∈ b.control := by
    intro g x
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨g⁻¹ • y, (a.2.isEquivariant.invariant_control g⁻¹ y).mpr hy, ?_⟩
      rw [heq, hyx, inv_smul_smul]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g • y, (a.2.isEquivariant.invariant_control g y).mpr hy, heq g y⟩
  -- The original boundary square is natural under exactly the same inclusion transport.
  refine EquivariantSupportBundleTriple.ofBoundary E F b ρE ρF ⟨hinv, ?_⟩
  intro g x v
  funext hy
  let hx : x.val ∈ U := (clopen_smul_mem_iff U heq g x.val).mp hy.down
  let xu : U := ⟨x.val, hx⟩
  have hC : xu ∉ a.1.datum.control := fun h ↦ x.property ⟨xu, h, rfl⟩
  have hgC : g • xu ∉ a.1.datum.control := fun h ↦
    hC ((a.2.isEquivariant.invariant_control g xu).mp h)
  have hyC : (⟨g • x.val, hy.down⟩ : U) ∉ a.1.datum.control := fun h ↦
    x.property ((hinv g x.val).mp ⟨⟨g • x.val, hy.down⟩, h, rfl⟩)
  have he : g • xu = (⟨g • x.val, hy.down⟩ : U) := Subtype.ext (heq g xu)
  have htransport {p q : U} (hp : p ∉ a.1.datum.control)
      (hq : q ∉ a.1.datum.control) (hpq : p = q) (w : a.1.source.Fiber p) :
      a.1.datum.boundary.linearEquiv ⟨q, hq⟩
          (LinearEquiv.cast (R := ℂ) (M := a.1.source.Fiber) hpq w) =
        LinearEquiv.cast (R := ℂ) (M := a.1.target.Fiber) hpq
          (a.1.datum.boundary.linearEquiv ⟨p, hp⟩ w) := by
    subst q
    rfl
  change a.1.datum.boundary.linearEquiv ⟨⟨g • x.val, hy.down⟩, hyC⟩
      (LinearEquiv.cast (R := ℂ) (M := a.1.source.Fiber) he
        (a.2.sourceAction.linearMap g xu (v ⟨hx⟩))) =
    LinearEquiv.cast (R := ℂ) (M := a.1.target.Fiber) he
      (a.2.targetAction.linearMap g xu (a.1.datum.boundary.linearEquiv ⟨xu, hC⟩ (v ⟨hx⟩)))
  exact (htransport hgC hyC he _).trans
    (congrArg (LinearEquiv.cast (R := ℂ) (M := a.1.target.Fiber) he)
      (a.2.isEquivariant.boundary_intertwines g ⟨xu, hC⟩ (v ⟨hx⟩)))

/-- The original equivariant square remains equivariant under the same inclusion transports. -/
private theorem clopenExtensionIso_equivariant (U : Set X)
    [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (E F : FiniteBundle U) (ρE : EquivariantStructure G E.Fiber)
    (ρF : EquivariantStructure G F.Fiber) (e : Iso E.Fiber F.Fiber)
    (he : e.IsEquivariant ρE ρF) :
    (clopenExtensionIso U e).IsEquivariant
      (clopenExtensionAction U heq E ρE) (clopenExtensionAction U heq F ρF) := by
  intro g x v
  funext hy
  let hx : x ∈ U := (clopen_smul_mem_iff U heq g x).mp hy.down
  let xu : U := ⟨x, hx⟩
  have hp : g • xu = (⟨g • x, hy.down⟩ : U) := Subtype.ext (heq g xu)
  have htransport {p q : U} (hpq : p = q) (w : E.Fiber p) :
      e.linearEquiv q (LinearEquiv.cast (R := ℂ) (M := E.Fiber) hpq w) =
        LinearEquiv.cast (R := ℂ) (M := F.Fiber) hpq (e.linearEquiv p w) := by
    subst q
    rfl
  change e.linearEquiv ⟨g • x, hy.down⟩
      (LinearEquiv.cast (R := ℂ) (M := E.Fiber) hp (ρE.linearMap g xu (v ⟨hx⟩))) =
    LinearEquiv.cast (R := ℂ) (M := F.Fiber) hp
      (ρF.linearMap g xu (e.linearEquiv xu (v ⟨hx⟩)))
  exact (htransport hp _).trans
    (congrArg (LinearEquiv.cast (R := ℂ) (M := F.Fiber) hp) (he g xu (v ⟨hx⟩)))

/-- The pair comparison commutes with the same transported componentwise actions. -/
private theorem clopenExtensionSumIso_equivariant (U : Set X) (hU : IsClopen U)
    [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (E F : FiniteBundle U) (ρE : EquivariantStructure G E.Fiber)
    (ρF : EquivariantStructure G F.Fiber) :
    (clopenExtensionSumIso U hU E.Fiber F.Fiber).IsEquivariant
      (clopenExtensionAction U heq (E.sum F) (ρE.sum ρF))
      ((clopenExtensionAction U heq E ρE).sum (clopenExtensionAction U heq F ρF)) := by
  intro g x v
  have htransport {p q : U} (hpq : p = q) (w : E.Fiber p × F.Fiber p) :
      LinearEquiv.cast (R := ℂ) (M := fun y ↦ E.Fiber y × F.Fiber y) hpq w =
        (LinearEquiv.cast (R := ℂ) (M := E.Fiber) hpq w.1,
          LinearEquiv.cast (R := ℂ) (M := F.Fiber) hpq w.2) := by
    subst q
    rfl
  apply Prod.ext
  · funext hy
    let hx : x ∈ U := (clopen_smul_mem_iff U heq g x).mp hy.down
    exact congrArg Prod.fst (htransport
      (show g • (⟨x, hx⟩ : U) = ⟨g • x, hy.down⟩ from Subtype.ext (heq g ⟨x, hx⟩))
      ((ρE.linearMap g ⟨x, hx⟩ (v ⟨hx⟩).1), (ρF.linearMap g ⟨x, hx⟩ (v ⟨hx⟩).2)))
  · funext hy
    let hx : x ∈ U := (clopen_smul_mem_iff U heq g x).mp hy.down
    exact congrArg Prod.snd (htransport
      (show g • (⟨x, hx⟩ : U) = ⟨g • x, hy.down⟩ from Subtype.ext (heq g ⟨x, hx⟩))
      ((ρE.linearMap g ⟨x, hx⟩ (v ⟨hx⟩).1), (ρF.linearMap g ⟨x, hx⟩ (v ⟨hx⟩).2)))

/-- Zero extension preserves precisely the three original presentation relations. -/
private theorem clopenExtension_relations (U : Set X) (hU : IsClopen U)
    [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X)) :
    (∀ a b : EquivariantSupportBundleTriple G U, a.IsIsomorphic b →
      (clopenExtensionEquivariantTriple U hU heq a).kZeroClass =
        (clopenExtensionEquivariantTriple U hU heq b).kZeroClass) ∧
    (∀ a b : EquivariantSupportBundleTriple G U,
      (clopenExtensionEquivariantTriple U hU heq (a.sum b)).kZeroClass =
        (clopenExtensionEquivariantTriple U hU heq a).kZeroClass +
          (clopenExtensionEquivariantTriple U hU heq b).kZeroClass) ∧
    (∀ (E : FiniteBundle U) (ρ : EquivariantStructure G E.Fiber),
      (clopenExtensionEquivariantTriple U hU heq
        (EquivariantSupportBundleTriple.identity E ρ)).kZeroClass = 0) := by
  obtain ⟨hi, hs, hz⟩ := equivariantSupportTripleKZero_generator_relations (G := G) (X := X)
  constructor
  · intro a b hab
    obtain ⟨K, hK, hInv, ha, hb, u, v, hu, hv, hsq⟩ := hab
    apply hi
    have hInv' (g : G) (x : X) : g • x ∈ Subtype.val '' K ↔ x ∈ Subtype.val '' K := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        refine ⟨g⁻¹ • y, (hInv g⁻¹ y).mpr hy, ?_⟩
        rw [heq, hyx, inv_smul_smul]
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g • y, (hInv g y).mpr hy, heq g y⟩
    refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, hInv',
      Set.image_mono ha, Set.image_mono hb, clopenExtensionIso U u, clopenExtensionIso U v,
      clopenExtensionIso_equivariant U heq a.1.source b.1.source
        a.2.sourceAction b.2.sourceAction u hu,
      clopenExtensionIso_equivariant U heq a.1.target b.1.target
        a.2.targetAction b.2.targetAction v hv, ?_⟩
    intro x w
    simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
    funext hx
    let xu : (Kᶜ : Set U) :=
      ⟨⟨x.val, hx.down⟩, fun h ↦ x.property ⟨⟨x.val, hx.down⟩, h, rfl⟩⟩
    have h := hsq xu (w hx)
    simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply] at h
    exact h
  constructor
  · intro a b
    let ea := clopenExtensionEquivariantTriple U hU heq a
    let eb := clopenExtensionEquivariantTriple U hU heq b
    let eab := clopenExtensionEquivariantTriple U hU heq (a.sum b)
    let K := eab.1.datum.control
    have hK : IsCompact K := eab.1.datum.isCompact_control
    have hsub : (ea.sum eb).1.datum.control ⊆ K := by
      change (Subtype.val '' a.1.datum.control) ∪ (Subtype.val '' b.1.datum.control) ⊆
        Subtype.val '' (a.1.datum.control ∪ b.1.datum.control)
      rw [Set.image_union]
    have h : eab.IsIsomorphic (ea.sum eb) := by
      refine ⟨K, hK, eab.2.isEquivariant.invariant_control, Set.Subset.refl _, hsub,
        clopenExtensionSumIso U hU a.1.source.Fiber b.1.source.Fiber,
        clopenExtensionSumIso U hU a.1.target.Fiber b.1.target.Fiber,
        clopenExtensionSumIso_equivariant U hU heq a.1.source b.1.source
          a.2.sourceAction b.2.sourceAction,
        clopenExtensionSumIso_equivariant U hU heq a.1.target b.1.target
          a.2.targetAction b.2.targetAction, ?_⟩
      intro x w
      simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
      let xu (hx : PLift (x.val ∈ U)) :
          ((a.1.datum.control ∪ b.1.datum.control)ᶜ : Set U) :=
        ⟨⟨x.val, hx.down⟩, fun h ↦ x.property ⟨⟨x.val, hx.down⟩, h, rfl⟩⟩
      have hleft (hx : PLift (x.val ∈ U)) :
          (a.1.datum.sum b.1.datum).boundary.linearEquiv (xu hx) (w hx) =
            (a.1.datum.boundary.linearEquiv
                ⟨⟨x.val, hx.down⟩, fun h ↦ (xu hx).property (Or.inl h)⟩ (w hx).1,
              b.1.datum.boundary.linearEquiv
                ⟨⟨x.val, hx.down⟩, fun h ↦ (xu hx).property (Or.inr h)⟩ (w hx).2) := by
        let C := a.1.datum.control ∪ b.1.datum.control
        have hC : IsCompact C := a.1.datum.isCompact_control.union b.1.datum.isCompact_control
        exact (RelativeTriple.sum_apply
          (a.1.datum.enlarge C hC Set.subset_union_left).boundary
          (b.1.datum.enlarge C hC Set.subset_union_right).boundary (xu hx) (w hx)).trans
            (Prod.ext (a.1.datum.enlarge_apply C hC Set.subset_union_left (xu hx) (w hx).1)
              (b.1.datum.enlarge_apply C hC Set.subset_union_right (xu hx) (w hx).2))
      have hright := RelativeTriple.sum_apply
        (ea.1.datum.enlarge (ea.1.datum.control ∪ eb.1.datum.control)
          (ea.1.datum.isCompact_control.union eb.1.datum.isCompact_control)
          Set.subset_union_left).boundary
        (eb.1.datum.enlarge (ea.1.datum.control ∪ eb.1.datum.control)
          (ea.1.datum.isCompact_control.union eb.1.datum.isCompact_control)
          Set.subset_union_right).boundary
        (⟨x.val, fun h ↦ x.property (hsub h)⟩ :
          ((ea.1.datum.control ∪ eb.1.datum.control)ᶜ : Set X))
        ((clopenExtensionSumIso U hU a.1.source.Fiber b.1.source.Fiber).linearEquiv x.val w)
      simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply] at hright
      refine Eq.trans ?_ hright.symm
      apply Prod.ext
      · funext hx
        exact congrArg Prod.fst (hleft hx)
      · funext hx
        exact congrArg Prod.snd (hleft hx)
    exact (hi eab (ea.sum eb) h).trans (hs ea eb)
  · intro E ρ
    let b := clopenExtensionEquivariantTriple U hU heq
      (EquivariantSupportBundleTriple.identity E ρ)
    let F := clopenExtensionBundle U hU E
    let σ := clopenExtensionAction U heq E ρ
    have h : b.IsIsomorphic (EquivariantSupportBundleTriple.identity F σ) := by
      refine ⟨∅, isCompact_empty, (fun _ _ ↦ Iff.rfl), ?_, Set.Subset.refl _,
        Iso.refl F.Fiber, Iso.refl F.Fiber, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
      · rintro _ ⟨x, hx, _⟩
        exact hx.elim
      · intro x w
        simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
        funext hx
        rfl
    exact (hi b _ h).trans (hz F σ)

/-- Descend these same extended generators through the original presentation. -/
private def clopenExtensionKZero (U : Set X) (hU : IsClopen U)
    [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X)) :
    EquivariantSupportTripleKZero G U →+ EquivariantSupportTripleKZero G X :=
  (equivariantSupportTripleKZero_universal_property
    (fun a ↦ (clopenExtensionEquivariantTriple U hU heq a).kZeroClass)
    (clopenExtension_relations U hU heq).1
    (clopenExtension_relations U hU heq).2.1
    (clopenExtension_relations U hU heq).2.2).choose

/-- Read the generator equation from the witness defining the extension homomorphism. -/
private theorem clopenExtensionKZero_apply (U : Set X) (hU : IsClopen U)
    [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (a : EquivariantSupportBundleTriple G U) :
    clopenExtensionKZero U hU heq a.kZeroClass =
      (clopenExtensionEquivariantTriple U hU heq a).kZeroClass :=
  (equivariantSupportTripleKZero_universal_property
    (fun a ↦ (clopenExtensionEquivariantTriple U hU heq a).kZeroClass)
    (clopenExtension_relations U hU heq).1
    (clopenExtension_relations U hU heq).2.1
    (clopenExtension_relations U hU heq).2.2).choose_spec.1 a

attribute [local instance] trivialTopology isFiniteRank_trivial

/-- Restricting to the original piece evaluates the membership-indexed fiber at its witness. -/
private def clopenExtensionRestrictIso (U : Set X) (hU : IsClopen U)
    (E : FiniteBundle U) : Iso (Restrict (clopenExtensionBundle U hU E).Fiber U) E.Fiber where
  linearEquiv x :=
    { toFun v := v ⟨x.property⟩
      invFun v := fun _ ↦ v
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  continuous_total := by
    apply (Topology.IsEmbedding.inl (Y := (Uᶜ : Set X))).continuous_iff.mpr
    apply ((clopenExtensionTotalHomeomorph U E.Fiber).continuous.comp
      (Pullback.continuous_lift Unit (ClopenExtensionFiber U E.Fiber)
        (Subtype.val : U → X))).congr
    intro z
    simp [clopenExtensionTotalHomeomorph, clopenExtensionTotalEquiv, z.proj.property]
    rfl
  continuous_symm := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (ClopenExtensionFiber U E.Fiber)
      (Subtype.val : U → X)).continuous_iff]
    apply (continuous_proj (E := E.Fiber)).prodMk
    apply continuous_induced_rng.mpr
    apply continuous_inl.congr
    intro z
    simp [clopenExtensionTotalEquiv, z.proj.property]
    rfl

attribute [local instance] trivialTopology isFiniteRank_trivial

/-- Restriction to a disjoint piece has the original zero-dimensional bundle as its actual fiber
model. -/
private def clopenExtensionDisjointIso (U : Set X) (hU : IsClopen U)
    (E : FiniteBundle U) (V : Set X) (hUV : Disjoint U V) :
    Iso (Restrict (clopenExtensionBundle U hU E).Fiber V) (FiniteBundle.trivial V 0).Fiber where
  linearEquiv x :=
    { toFun _ := 0
      invFun _ := fun h ↦ False.elim (Set.disjoint_left.mp hUV h.down x.property)
      left_inv v := by
        funext h
        exact (Set.disjoint_left.mp hUV h.down x.property).elim
      right_inv _ := Subsingleton.elim _ _
      map_add' _ _ := (zero_add 0).symm
      map_smul' c _ := (smul_zero c).symm }
  continuous_total := by
    apply continuous_induced_rng.mpr
    exact (Pullback.continuous_proj Unit (ClopenExtensionFiber U E.Fiber)
      (Subtype.val : V → X)).prodMk continuous_const
  continuous_symm := by
    have hp : Continuous (π Unit (FiniteBundle.trivial V 0).Fiber) :=
      continuous_proj (E := (FiniteBundle.trivial V 0).Fiber)
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (ClopenExtensionFiber U E.Fiber)
      (Subtype.val : V → X)).continuous_iff]
    apply hp.prodMk
    apply continuous_induced_rng.mpr
    have hbase : Continuous (fun z : TotalSpace Unit (FiniteBundle.trivial V 0).Fiber ↦
        (⟨z.proj.val, fun h ↦ Set.disjoint_left.mp hUV h z.proj.property⟩ : (Uᶜ : Set X))) :=
      (continuous_subtype_val.comp hp).subtype_mk _
    apply (continuous_inr.comp hbase).congr
    intro z
    have hz : z.proj.val ∉ U := fun h ↦ Set.disjoint_left.mp hUV h z.proj.property
    simp [clopenExtensionTotalEquiv, hz]

set_option backward.isDefEq.respectTransparency.types false in
/-- The restriction evaluation cancels the two transports from the same inclusion equality. -/
private theorem clopenExtensionRestrictIso_isEquivariant
    (U : Set X) (hU : IsClopen U) [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (E : FiniteBundle U) (ρ : EquivariantStructure G E.Fiber) :
    (clopenExtensionRestrictIso U hU E).IsEquivariant
      ((clopenExtensionAction U heq E ρ).pullback
        ⟨Subtype.val, continuous_subtype_val⟩ heq) ρ := by
  intro g x v
  have htransport (p q : X) (hpq : p = q) (hp : p ∈ U) (hq : q ∈ U)
      (L : ClopenExtensionFiber U E.Fiber x.val →ₗ[ℂ] ClopenExtensionFiber U E.Fiber q) :
      HEq (((Eq.mpr (congrArg (fun y ↦
        ClopenExtensionFiber U E.Fiber x.val →ₗ[ℂ] ClopenExtensionFiber U E.Fiber y)
          hpq) L) v) ⟨hp⟩) ((L v) ⟨hq⟩) := by
    subst q
    rfl
  have hcast {p q : U} (hpq : p = q) (w : E.Fiber p) :
      HEq (LinearEquiv.cast (R := ℂ) (M := E.Fiber) hpq w) w := by
    subst q
    rfl
  let hgx := (clopen_smul_mem_iff U heq g x.val).mpr x.property
  have hfirst := htransport (g • x : U).val (g • x.val) (heq g x)
    (g • x : U).property hgx ((clopenExtensionAction U heq E ρ).linearMap g x.val)
  apply eq_of_heq
  exact hfirst.trans (hcast (show g • x = (⟨g • x.val, hgx⟩ : U) from
    Subtype.ext (heq g x)) (ρ.linearMap g x (v ⟨x.property⟩)))

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting an extended triple to its original piece gives the original equivariant square. -/
private theorem clopenExtension_same_isIsomorphic
    (U : Set X) (hU : IsClopen U) [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (a : EquivariantSupportBundleTriple G U) :
    ((clopenExtensionEquivariantTriple U hU heq a).pullback
      ⟨Subtype.val, continuous_subtype_val⟩ heq hU.isClosed.isProperMap_subtypeVal).IsIsomorphic
      a := by
  let b := clopenExtensionEquivariantTriple U hU heq a
  let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcontrol : (b.pullback f heq hU.isClosed.isProperMap_subtypeVal).1.datum.control ⊆
      a.1.datum.control := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hx
    exact (Subtype.ext he) ▸ hy
  refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
    a.2.isEquivariant.invariant_control, hcontrol, Set.Subset.refl _,
    clopenExtensionRestrictIso U hU a.1.source,
    clopenExtensionRestrictIso U hU a.1.target,
    clopenExtensionRestrictIso_isEquivariant U hU heq a.1.source a.2.sourceAction,
    clopenExtensionRestrictIso_isEquivariant U hU heq a.1.target a.2.targetAction, ?_⟩
  intro x v
  rw [CompactSupportTriple.enlarge_apply, CompactSupportTriple.enlarge_apply]
  let xp : (f ⁻¹' b.1.datum.controlᶜ) :=
    ⟨x.val, fun h ↦ x.property (hcontrol h)⟩
  exact congrArg ((clopenExtensionRestrictIso U hU a.1.target).linearEquiv x)
    (RelativeTriple.pullback_apply b.1.datum.boundary f xp v)

set_option backward.isDefEq.respectTransparency.types false in
/-- On a disjoint piece, compare with the identity on the same pulled-back zero source bundle. -/
private theorem clopenExtension_disjoint_kZeroClass
    (U : Set X) (hU : IsClopen U) [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (a : EquivariantSupportBundleTriple G U)
    (V : Set X) (hV : IsClosed V) [MulAction G V] [ContinuousSMul G V]
    (heqV : ∀ (g : G) (x : V), ((g • x : V) : X) = g • (x : X))
    (hUV : Disjoint U V) :
    ((clopenExtensionEquivariantTriple U hU heq a).pullback
      ⟨Subtype.val, continuous_subtype_val⟩ heqV hV.isProperMap_subtypeVal).kZeroClass = 0 := by
  let c := (clopenExtensionEquivariantTriple U hU heq a).pullback
    ⟨Subtype.val, continuous_subtype_val⟩ heqV hV.isProperMap_subtypeVal
  let z := EquivariantSupportBundleTriple.identity c.1.source c.2.sourceAction
  let v : Iso c.1.target.Fiber c.1.source.Fiber :=
    (clopenExtensionDisjointIso U hU a.1.target V hUV).trans
      (clopenExtensionDisjointIso U hU a.1.source V hUV).symm
  have hcontrol : c.1.datum.control ⊆ (∅ : Set V) := by
    rintro x ⟨y, _, he⟩
    change (y : X) = (x : X) at he
    exact (Set.disjoint_left.mp hUV (he ▸ y.property) x.property).elim
  have hc : c.IsIsomorphic z := by
    refine ⟨∅, isCompact_empty, fun _ _ ↦ Iff.rfl, hcontrol, Set.Subset.refl _,
      Iso.refl c.1.source.Fiber, v, (fun _ _ _ ↦ rfl), ?_, ?_⟩
    · intro g x w
      funext h
      exact (Set.disjoint_left.mp hUV h.down (g • x).property).elim
    · intro x w
      funext h
      exact (Set.disjoint_left.mp hUV h.down x.val.property).elim
  exact (equivariantSupportTripleKZero_generator_relations.1 c z hc).trans
    (equivariantSupportTripleKZero_generator_relations.2.2 c.1.source c.2.sourceAction)

/-- Equality on the original generators determines additive maps out of their quotient
presentation. -/
private theorem equivariantClopen_hom_ext {A : Type*} [AddCommGroup A]
    (f g : EquivariantSupportTripleKZero G X →+ A)
    (h : ∀ a : EquivariantSupportBundleTriple G X, f a.kZeroClass = g a.kZeroClass) : f = g := by
  have hcomp : f.comp (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) =
      g.comp (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) := by
    apply FreeAbelianGroup.lift_ext
    exact h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G X) x
  exact DFunLike.congr_fun hcomp z

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial
  isFiniteRank_restrict isFiniteRank_pullback sectionModule

set_option backward.isDefEq.respectTransparency.types false

/-- Evaluate the extended restriction on its original piece and use the zero section outside. -/
private def clopenRestrictionCollapse (E : FiniteBundle X) (U : Set X) :
    Hom (ClopenExtensionFiber U (Restrict E.Fiber U)) E.Fiber where
  linearMap x :=
    { toFun v := if hx : x ∈ U then v ⟨hx⟩ else 0
      map_add' _ _ := by
        by_cases hx : x ∈ U
        · simp only [dite_eq_left hx]
          rfl
        · simp [hx]
      map_smul' _ _ := by
        by_cases hx : x ∈ U
        · simp only [dite_eq_left hx]
          rfl
        · simp [hx] }
  continuous_total := by
    have hi := Pullback.continuous_lift Unit E.Fiber (Subtype.val : U → X)
    have ho := (continuous_zero_section E.Fiber).comp
      (continuous_subtype_val : Continuous (Subtype.val : (Uᶜ : Set X) → X))
    have hc := (hi.sumElim ho).comp
      (clopenExtensionTotalHomeomorph U (Restrict E.Fiber U)).continuous
    apply hc.congr
    intro z
    by_cases hx : z.proj ∈ U <;>
      simp [clopenExtensionTotalHomeomorph, clopenExtensionTotalEquiv, hx, Pullback.lift]

/-- Form the actual finite sum of extended restrictions, starting with the zero bundle. -/
@[reducible] private def clopenRestrictedFoldBundle {ι : Type*}
    (E : FiniteBundle X) (U : ι → Set X) (hU : ∀ i, IsClopen (U i)) :
    List ι → FiniteBundle X
  | [] => FiniteBundle.trivial X 0
  | i :: l => (clopenExtensionBundle (U i) (hU i) (E.restrict (U i))).sum
      (clopenRestrictedFoldBundle E U hU l)

/-- Add the original component evaluation maps over the specified finite list. -/
private def clopenRestrictedFoldCollapse {ι : Type*}
    (E : FiniteBundle X) (U : ι → Set X) (hU : ∀ i, IsClopen (U i)) :
    (l : List ι) → Hom (clopenRestrictedFoldBundle E U hU l).Fiber E.Fiber
  | [] =>
    { linearMap _ := 0
      continuous_total := (continuous_zero_section E.Fiber).comp
        (continuous_proj (E := (FiniteBundle.trivial X 0).Fiber)) }
  | i :: l =>
    let A := clopenExtensionBundle (U i) (hU i) (E.restrict (U i))
    let B := clopenRestrictedFoldBundle E U hU l
    let f := clopenRestrictionCollapse E (U i)
    let g := clopenRestrictedFoldCollapse E U hU l
    { linearMap x := (f.linearMap x).coprod (g.linearMap x)
      continuous_total := by
        -- Both original summands map to the same ambient fiber; add their sections there.
        let : IsFiniteRank (A.sum B).Fiber := (A.sum B).isFiniteRank
        let D := TotalSpace Unit (A.sum B).Fiber
        let p : C(D, X) := ⟨fun z ↦ z.proj, continuous_proj⟩
        have hf : Continuous (fun z : D ↦
            (⟨z.proj, f.linearMap z.proj z.snd.1⟩ : TotalSpace Unit E.Fiber)) :=
          f.continuous_total.comp (continuous_sum_fst (E := A.Fiber) (F := B.Fiber))
        have hg : Continuous (fun z : D ↦
            (⟨z.proj, g.linearMap z.proj z.snd.2⟩ : TotalSpace Unit E.Fiber)) :=
          g.continuous_total.comp (continuous_sum_snd (E := A.Fiber) (F := B.Fiber))
        have hfs : Continuous (fun z : D ↦
            (⟨z, f.linearMap z.proj z.snd.1⟩ : TotalSpace Unit ((p : D → X) *ᵖ E.Fiber))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber p).continuous_iff]
          exact continuous_id.prodMk hf
        have hgs : Continuous (fun z : D ↦
            (⟨z, g.linearMap z.proj z.snd.2⟩ : TotalSpace Unit ((p : D → X) *ᵖ E.Fiber))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber p).continuous_iff]
          exact continuous_id.prodMk hg
        exact (Pullback.continuous_lift Unit E.Fiber p).comp
          (continuous_add_section ((p : D → X) *ᵖ E.Fiber)
            (fun z ↦ f.linearMap z.proj z.snd.1) (fun z ↦ g.linearMap z.proj z.snd.2) hfs hgs) }

/-- Disjointness and coverage make the same finite-sum evaluation an actual bundle isomorphism. -/
private def clopenRestrictedFoldIso {ι : Type*}
    (E : FiniteBundle X) (U : ι → Set X) (hU : ∀ i, IsClopen (U i)) (l : List ι)
    (hd : l.Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hc : ∀ x, ∃ i ∈ l, x ∈ U i) :
    Iso (clopenRestrictedFoldBundle E U hU l).Fiber E.Fiber := by
  -- Outside the selected pieces the entire actual finite sum has its unique zero vector.
  have hoff : ∀ (k : List ι) (x : X), (∀ i ∈ k, x ∉ U i) →
      ∀ v : (clopenRestrictedFoldBundle E U hU k).Fiber x, v = 0 := by
    intro k
    induction k with
    | nil =>
      intro x hx v
      exact Subsingleton.elim _ _
    | cons i k ih =>
      intro x hx v
      apply Prod.ext
      · funext h
        exact (hx i (by simp) h.down).elim
      · exact ih x (fun j hj ↦ hx j (by simp [hj])) v.2
  -- On the unique active piece the sum map is exactly evaluation of its original fiber vector.
  have hbij : ∀ k : List ι, k.Pairwise (fun i j ↦ Disjoint (U i) (U j)) →
      ∀ x : X, (∃ i ∈ k, x ∈ U i) →
        Function.Bijective ((clopenRestrictedFoldCollapse E U hU k).linearMap x) := by
    intro k
    induction k with
    | nil =>
      intro hd x hx
      obtain ⟨i, hi, _⟩ := hx
      simp at hi
    | cons i k ih =>
      intro hd x hx
      have hd' := List.pairwise_cons.mp hd
      by_cases hi : x ∈ U i
      · have hk : ∀ j ∈ k, x ∉ U j := by
          intro j hj hxj
          exact Set.disjoint_left.mp (hd'.1 j hj) hi hxj
        have heval (v : (clopenRestrictedFoldBundle E U hU (i :: k)).Fiber x) :
            (clopenRestrictedFoldCollapse E U hU (i :: k)).linearMap x v = v.1 ⟨hi⟩ := by
          change (if h : x ∈ U i then v.1 ⟨h⟩ else 0) +
            (clopenRestrictedFoldCollapse E U hU k).linearMap x v.2 = _
          rw [dite_eq_left hi, hoff k x hk v.2, map_zero, add_zero]
        constructor
        · intro v w hvw
          apply Prod.ext
          · funext h
            exact (heval v).symm.trans (hvw.trans (heval w))
          · exact (hoff k x hk v.2).trans (hoff k x hk w.2).symm
        · intro v
          exact ⟨(fun _ ↦ v, 0), heval _⟩
      · have hk : ∃ j ∈ k, x ∈ U j := by
          obtain ⟨j, hj, hxj⟩ := hx
          rcases List.mem_cons.mp hj with rfl | hj
          · exact (hi hxj).elim
          · exact ⟨j, hj, hxj⟩
        have hb := ih hd'.2 x hk
        have heval (v : (clopenRestrictedFoldBundle E U hU (i :: k)).Fiber x) :
            (clopenRestrictedFoldCollapse E U hU (i :: k)).linearMap x v =
              (clopenRestrictedFoldCollapse E U hU k).linearMap x v.2 := by
          change (if h : x ∈ U i then v.1 ⟨h⟩ else 0) +
            (clopenRestrictedFoldCollapse E U hU k).linearMap x v.2 = _
          rw [dite_eq_right hi, zero_add]
        constructor
        · intro v w hvw
          apply Prod.ext
          · funext h
            exact (hi h.down).elim
          · exact hb.1 ((heval v).symm.trans (hvw.trans (heval w)))
        · intro v
          obtain ⟨w, hw⟩ := hb.2 v
          exact ⟨(0, w), (heval _).trans hw⟩
  exact (clopenRestrictedFoldCollapse E U hU l).toIso (fun x ↦ hbij l hd x (hc x))

/-- Evaluation cancels the same inclusion transports and respects the original ambient action. -/
private theorem clopenRestrictionCollapse_isEquivariant (E : FiniteBundle X)
    (ρ : EquivariantStructure G E.Fiber) (U : Set X)
    [MulAction G U] [ContinuousSMul G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X)) :
    (clopenRestrictionCollapse E U).IsEquivariant
      (clopenExtensionAction U heq (E.restrict U)
        (ρ.pullback ⟨Subtype.val, continuous_subtype_val⟩ heq)) ρ := by
  intro g x v
  by_cases hx : x ∈ U
  · have hgx := (clopen_smul_mem_iff U heq g x).mpr hx
    change (if h : g • x ∈ U then
        clopenExtensionActionLinearMap U heq (E.restrict U)
          (ρ.pullback ⟨Subtype.val, continuous_subtype_val⟩ heq) g x v ⟨h⟩ else 0) =
      ρ.linearMap g x (if h : x ∈ U then v ⟨h⟩ else 0)
    rw [dite_eq_left hx, dite_eq_left hgx]
    let xu : U := ⟨x, hx⟩
    have he : g • xu = (⟨g • x, hgx⟩ : U) := Subtype.ext (heq g xu)
    have hcast {p q : U} (hpq : p = q)
        (L : E.Fiber x →ₗ[ℂ] E.Fiber q.val) (w : E.Fiber x) :
        LinearEquiv.cast (R := ℂ) (M := (E.restrict U).Fiber) hpq
          ((Eq.mpr (congrArg (fun y ↦ E.Fiber x →ₗ[ℂ] E.Fiber y)
            (congrArg Subtype.val hpq)) L) w) = L w := by
      subst q
      rfl
    exact hcast he (ρ.linearMap g x) (v ⟨hx⟩)
  · have hgx : g • x ∉ U := fun h ↦ hx ((clopen_smul_mem_iff U heq g x).mp h)
    change (if h : g • x ∈ U then _ else 0) =
      ρ.linearMap g x (if h : x ∈ U then _ else 0)
    rw [dite_eq_right hgx, dite_eq_right hx, map_zero]

/-- The original component actions on the same finite fold of extended restrictions. -/
private def clopenRestrictedFoldAction {ι : Type*} (E : FiniteBundle X)
    (ρ : EquivariantStructure G E.Fiber) (U : ι → Set X) (hU : ∀ i, IsClopen (U i))
    [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
    (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : X) = g • (x : X)) :
    (l : List ι) → EquivariantStructure G (clopenRestrictedFoldBundle E U hU l).Fiber
  | [] =>
    { linearMap := fun _ _ ↦ LinearMap.id
      one_map := fun x v ↦ congrArg (fun y ↦
        (⟨y, v⟩ : TotalSpace Unit (FiniteBundle.trivial X 0).Fiber)) (one_smul G x)
      mul_map := fun g h x v ↦ congrArg (fun y ↦
        (⟨y, v⟩ : TotalSpace Unit (FiniteBundle.trivial X 0).Fiber)) (mul_smul g h x)
      continuous_action := by
        have hc : Continuous (fun z : TotalSpace Unit (FiniteBundle.trivial X 0).Fiber ↦
            (z.proj, z.snd)) := continuous_induced_dom
        exact continuous_induced_rng.mpr
          ((continuous_fst.smul (hc.fst.comp continuous_snd)).prodMk
            (hc.snd.comp continuous_snd)) }
  | i :: l =>
    (clopenExtensionAction (U i) (heq i) (E.restrict (U i))
      (ρ.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i))).sum
        (clopenRestrictedFoldAction E ρ U hU heq l)

/-- The actual finite sum boundary, retaining the original restricted controls. -/
private def clopenRestrictedFoldDatum {ι : Type*}
    (a : EquivariantSupportBundleTriple G X) (U : ι → Set X) (hU : ∀ i, IsClopen (U i))
    [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
    (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : X) = g • (x : X)) :
    (l : List ι) → CompactSupportTriple (clopenRestrictedFoldBundle a.1.source U hU l).Fiber
      (clopenRestrictedFoldBundle a.1.target U hU l).Fiber
  | [] => CompactSupportTriple.ofIso (Iso.refl (FiniteBundle.trivial X 0).Fiber)
  | i :: l =>
    (clopenExtensionEquivariantTriple (U i) (hU i) (heq i)
      (a.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i)
        (hU i).isClosed.isProperMap_subtypeVal)).1.datum.sum
          (clopenRestrictedFoldDatum a U hU heq l)

/-- Package the specified finite fold with its original source, target and actions. -/
private def clopenRestrictedFoldTriple {ι : Type*}
    (a : EquivariantSupportBundleTriple G X) (U : ι → Set X) (hU : ∀ i, IsClopen (U i))
    [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
    (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : X) = g • (x : X))
    (l : List ι) : EquivariantSupportBundleTriple G X :=
  EquivariantSupportBundleTriple.ofBoundary
    (clopenRestrictedFoldBundle a.1.source U hU l)
    (clopenRestrictedFoldBundle a.1.target U hU l)
    (clopenRestrictedFoldDatum a U hU heq l)
    (clopenRestrictedFoldAction a.1.source a.2.sourceAction U hU heq l)
    (clopenRestrictedFoldAction a.1.target a.2.targetAction U hU heq l) (by
      induction l with
      | nil => exact ⟨fun _ _ ↦ Iff.rfl, fun _ _ _ ↦ rfl⟩
      | cons i l ih =>
        exact (clopenExtensionEquivariantTriple (U i) (hU i) (heq i)
          (a.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i)
            (hU i).isClosed.isProperMap_subtypeVal)).2.isEquivariant.sum ih)

/-- The finite assembly commutes with the original boundary on its original compact exterior. -/
private theorem clopenRestrictedFold_boundary {ι : Type*}
    (a : EquivariantSupportBundleTriple G X) (U : ι → Set X) (hU : ∀ i, IsClopen (U i))
    [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
    (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : X) = g • (x : X))
    (l : List ι) :
    ∃ hc : (clopenRestrictedFoldDatum a U hU heq l).control ⊆ a.1.datum.control,
      ∀ (x : (a.1.datum.controlᶜ : Set X))
        (w : (clopenRestrictedFoldBundle a.1.source U hU l).Fiber x),
        (clopenRestrictedFoldCollapse a.1.target U hU l).linearMap x
          (((clopenRestrictedFoldDatum a U hU heq l).enlarge a.1.datum.control
            a.1.datum.isCompact_control hc).boundary.linearEquiv x w) =
        a.1.datum.boundary.linearEquiv x
          ((clopenRestrictedFoldCollapse a.1.source U hU l).linearMap x w) := by
  -- Every finite partial assembly is controlled by the original compact set.
  induction l with
  | nil =>
    refine ⟨Set.empty_subset _, ?_⟩
    intro x w
    exact (map_zero (a.1.datum.boundary.linearEquiv x)).symm
  | cons i l ih =>
    obtain ⟨hc, hsquare⟩ := ih
    let b := (clopenExtensionEquivariantTriple (U i) (hU i) (heq i)
      (a.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i)
        (hU i).isClosed.isProperMap_subtypeVal)).1.datum
    let d := clopenRestrictedFoldDatum a U hU heq l
    have hb : b.control ⊆ a.1.datum.control := by
      rintro x ⟨y, hy, rfl⟩
      exact hy
    have hbd : (b.sum d).control ⊆ a.1.datum.control := Set.union_subset hb hc
    refine ⟨hbd, ?_⟩
    intro x w
    -- On the common exterior, the direct-sum boundary acts on the two components.
    have hsum : ((b.sum d).enlarge a.1.datum.control
          a.1.datum.isCompact_control hbd).boundary.linearEquiv x w =
        ((b.enlarge a.1.datum.control a.1.datum.isCompact_control hb).boundary.linearEquiv
            x w.1,
          (d.enlarge a.1.datum.control a.1.datum.isCompact_control hc).boundary.linearEquiv
            x w.2) := by
      simp only [CompactSupportTriple.enlarge, CompactSupportTriple.sum,
        Iso.restrictTo_apply, RelativeTriple.sum_apply]
      rfl
    change (clopenRestrictedFoldCollapse a.1.target U hU (i :: l)).linearMap x
      (((b.sum d).enlarge a.1.datum.control a.1.datum.isCompact_control hbd).boundary.linearEquiv
        x w) = _
    rw [hsum]
    change (clopenRestrictionCollapse a.1.target (U i)).linearMap x
        ((b.enlarge a.1.datum.control a.1.datum.isCompact_control hb).boundary.linearEquiv x w.1) +
      (clopenRestrictedFoldCollapse a.1.target U hU l).linearMap x
        ((d.enlarge a.1.datum.control a.1.datum.isCompact_control hc).boundary.linearEquiv x w.2) =
      a.1.datum.boundary.linearEquiv x
        ((clopenRestrictionCollapse a.1.source (U i)).linearMap x w.1 +
          (clopenRestrictedFoldCollapse a.1.source U hU l).linearMap x w.2)
    erw [hsquare x w.2, map_add]
    congr 1
    -- Evaluation of the extended restricted summand reads the same original boundary.
    by_cases hx : x.val ∈ U i
    · change (if h : x.val ∈ U i then
          ((b.enlarge a.1.datum.control a.1.datum.isCompact_control hb).boundary.linearEquiv
            x w.1) ⟨h⟩ else 0) =
        a.1.datum.boundary.linearEquiv x (if h : x.val ∈ U i then w.1 ⟨h⟩ else 0)
      rw [dite_eq_left hx, dite_eq_left hx, CompactSupportTriple.enlarge_apply]
      exact RelativeTriple.pullback_apply a.1.datum.boundary
        ⟨Subtype.val, continuous_subtype_val⟩ ⟨⟨x.val, hx⟩, x.property⟩ (w.1 ⟨hx⟩)
    · change (if h : x.val ∈ U i then _ else 0) =
        a.1.datum.boundary.linearEquiv x (if h : x.val ∈ U i then _ else 0)
      rw [dite_eq_right hx, dite_eq_right hx, map_zero]

/-- A finite disjoint cover reconstructs the original triple class by actual bundle isomorphisms. -/
private theorem clopenRestrictedFold_reconstruction_class {ι : Type*}
    (a : EquivariantSupportBundleTriple G X) (U : ι → Set X) (hU : ∀ i, IsClopen (U i))
    [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
    (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : X) = g • (x : X))
    (l : List ι) (hd : l.Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hcover : ∀ x, ∃ i ∈ l, x ∈ U i) :
    (l.map fun i ↦ (clopenExtensionEquivariantTriple (U i) (hU i) (heq i)
      (a.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i)
        (hU i).isClosed.isProperMap_subtypeVal)).kZeroClass).sum = a.kZeroClass := by
  -- Every summand's evaluation map intertwines the same original ambient action.
  have hequiv (E : FiniteBundle X) (ρ : EquivariantStructure G E.Fiber) :
      ∀ k : List ι, (clopenRestrictedFoldCollapse E U hU k).IsEquivariant
        (clopenRestrictedFoldAction E ρ U hU heq k) ρ := by
    intro k
    induction k with
    | nil =>
      intro g x v
      exact (map_zero (ρ.linearMap g x)).symm
    | cons i k ih =>
      intro g x v
      change (clopenRestrictionCollapse E (U i)).linearMap (g • x)
          ((clopenExtensionAction (U i) (heq i) (E.restrict (U i))
            (ρ.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i))).linearMap g x v.1) +
        (clopenRestrictedFoldCollapse E U hU k).linearMap (g • x)
          ((clopenRestrictedFoldAction E ρ U hU heq k).linearMap g x v.2) =
        ρ.linearMap g x ((clopenRestrictionCollapse E (U i)).linearMap x v.1 +
          (clopenRestrictedFoldCollapse E U hU k).linearMap x v.2)
      rw [clopenRestrictionCollapse_isEquivariant E ρ (U i) (heq i) g x v.1,
        ih g x v.2, map_add]
  -- The original direct-sum relation computes the class of the actual finite assembly.
  have hclass : ∀ k : List ι, (clopenRestrictedFoldTriple a U hU heq k).kZeroClass =
      (k.map fun i ↦ (clopenExtensionEquivariantTriple (U i) (hU i) (heq i)
        (a.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i)
          (hU i).isClosed.isProperMap_subtypeVal)).kZeroClass).sum := by
    intro k
    induction k with
    | nil =>
      exact (equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).2.2
        (FiniteBundle.trivial X 0)
        (clopenRestrictedFoldAction a.1.source a.2.sourceAction U hU heq [])
    | cons i k ih =>
      have hcons : clopenRestrictedFoldTriple a U hU heq (i :: k) =
          (clopenExtensionEquivariantTriple (U i) (hU i) (heq i)
            (a.pullback ⟨Subtype.val, continuous_subtype_val⟩ (heq i)
              (hU i).isClosed.isProperMap_subtypeVal)).sum
                (clopenRestrictedFoldTriple a U hU heq k) := rfl
      rw [hcons, (equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).2.1,
        ih]
      rfl
  -- Disjointness and coverage make each collapse map bijective on the original fibers.
  let e := clopenRestrictedFoldIso a.1.source U hU l hd hcover
  let f := clopenRestrictedFoldIso a.1.target U hU l hd hcover
  obtain ⟨hc, hsquare⟩ := clopenRestrictedFold_boundary a U hU heq l
  have hiso : (clopenRestrictedFoldTriple a U hU heq l).IsIsomorphic a := by
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, hc, Set.Subset.refl _, e, f,
      hequiv a.1.source a.2.sourceAction l, hequiv a.1.target a.2.targetAction l, ?_⟩
    intro x w
    change (clopenRestrictedFoldCollapse a.1.target U hU l).linearMap x
        (((clopenRestrictedFoldDatum a U hU heq l).enlarge
          a.1.datum.control a.1.datum.isCompact_control hc).boundary.linearEquiv x w) =
      (a.1.datum.enlarge a.1.datum.control a.1.datum.isCompact_control
        (Set.Subset.refl _)).boundary.linearEquiv x
          ((clopenRestrictedFoldCollapse a.1.source U hU l).linearMap x w)
    rw [a.1.datum.enlarge_apply]
    exact hsquare x w
  exact (hclass l).symm.trans
    ((equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).1 _ _ hiso)

end ClopenExtension

variable {G X ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  (U : ι → Opens X) [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
  (hclosed : ∀ i : ι, IsClosed (U i : Set X))
  (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : X) = g • (x : X))

/-- Restrict the original equivariant support class along each proper subtype inclusion. -/
def equivariantSupportTripleKZeroClopenRestrict :
    EquivariantSupportTripleKZero G X →+
      (∀ i : ι, EquivariantSupportTripleKZero G (U i)) :=
  AddMonoidHom.pi fun i ↦
    equivariantSupportTripleKZeroPullback
      ⟨(Subtype.val : U i → X), continuous_subtype_val⟩
      (heq i) (hclosed i).isProperMap_subtypeVal

set_option backward.isDefEq.respectTransparency.types false in
/-- A finite invariant clopen partition decomposes the original equivariant support group. -/
theorem equivariantSupportTripleKZeroClopenRestrict_bijective [Finite ι]
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)))
    (hcover : (⋃ i : ι, (U i : Set X)) = Set.univ) :
    Function.Bijective (equivariantSupportTripleKZeroClopenRestrict U hclosed heq) := by
  /- Stage 1: for a triple on U_i, extend its original source and target
  bundles by the zero bundle on the clopen complement. Local trivializations
  are unchanged on U_i and are the zero-dimensional product charts outside.
  Use the original fiber actions on U_i and the unique action on zero fibers.
  The inclusion equality heq makes U_i invariant under the full original G;
  its complement is invariant too, by applying the inverse group element.
  Thus these piecewise actions glue to jointly continuous original G actions.
  The boundary is the old boundary on U_i and the unique zero-fiber isomorphism
  on its complement. Its compact invariant control is exactly the image of
  the old control under the actual inclusion, compact by continuity.
  Stage 2: this clopen extension preserves the three defining relations.
  Extend original equivariant global isomorphism squares by zero outside U_i;
  the direct-sum comparison is the identity on the original fiber pairs; an
  identity triple extends to the identity on the extended bundle. Descend its
  generator map through equivariantSupportTripleKZero_universal_property.
  No completeness of the stable relation or invariant cutoff theorem is used.
  Stage 3: choose a finite enumeration of the index type and sum these
  descended extension maps. Restricting the i-th extension to U_i gives the
  original generator through vector-preserving bundle comparisons. Restricting
  it to a different disjoint U_j gives the identity on zero fibers, hence zero.
  Therefore restricting this finite assembly gives the identity on the
  product of the original groups.
  Stage 4: on an original triple over X, its restrictions extend and sum back
  to the same original triple up to an actual equivariant global isomorphism.
  At each x, the unique partition piece containing x contributes its original
  fiber; all other summands are zero. These coordinate isomorphisms are jointly
  continuous on the open pieces and intertwine the same original actions.
  The exterior maps agree through those isomorphisms. The finite union of the
  restricted controls is the original control because the pieces cover X.
  The isomorphism relation and presentation uniqueness give the other inverse
  identity on all classes. Thus the actual restriction map is bijective.
  Empty pieces contribute zero groups by the same identity relation. An empty
  index set forces X empty by hcover and the construction still applies.
  Arbitrary infinite products are excluded: their chosen controls need not
  have compact union. No global rank bound or rank cancellation is needed. -/
  classical
  let := Fintype.ofFinite ι
  -- Enumerate the partition only to form finite sums of the original compact controls.
  let l : List ι := Finset.univ.toList
  have hd : l.Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) :=
    (Finset.nodup_toList _).pairwise_of_forall_ne (fun i _ j _ hij ↦ hdisjoint hij)
  have hc (x : X) : ∃ i ∈ l, x ∈ (U i : Set X) := by
    have hx : x ∈ ⋃ i : ι, (U i : Set X) := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, by simp [l], hi⟩
  have hrec (a : EquivariantSupportBundleTriple G X) :
      a.kZeroClass = ∑ i, (clopenExtensionEquivariantTriple (U i)
        ⟨hclosed i, (U i).isOpen⟩ (heq i)
          (a.pullback ⟨Subtype.val, continuous_subtype_val⟩
            (heq i) (hclosed i).isProperMap_subtypeVal)).kZeroClass := by
    have h := clopenRestrictedFold_reconstruction_class a (fun i ↦ (U i : Set X))
      (fun i ↦ ⟨hclosed i, (U i).isOpen⟩) heq l hd hc
    simpa only [l, Finset.sum_map_toList] using h.symm
  -- Descend each zero extension and assemble the finite family additively.
  let R := equivariantSupportTripleKZeroClopenRestrict U hclosed heq
  let F (i : ι) : EquivariantSupportTripleKZero G (U i) →+
      EquivariantSupportTripleKZero G X :=
    clopenExtensionKZero (G := G) (X := X) (U i : Set X) ⟨hclosed i, (U i).isOpen⟩ (heq i)
  let assemble : (∀ i : ι, EquivariantSupportTripleKZero G (U i)) →+
      EquivariantSupportTripleKZero G X :=
    { toFun z := ∑ i, F i (z i)
      map_zero' := by simp
      map_add' z w := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib] }
  -- On the original piece the generator comparison is identity; on all others it is zero.
  have hdiag (i : ι) (z : EquivariantSupportTripleKZero G (U i)) :
      R (F i z) i = z := by
    let ri := equivariantSupportTripleKZeroPullback
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
      (heq i) (hclosed i).isProperMap_subtypeVal
    have h : ri.comp (F i) = AddMonoidHom.id _ := by
      apply equivariantClopen_hom_ext
      intro a
      change ri (F i a.kZeroClass) = a.kZeroClass
      exact (congrArg ri (clopenExtensionKZero_apply (G := G) (X := X) (U i : Set X)
        ⟨hclosed i, (U i).isOpen⟩ (heq i) a)).trans
          ((equivariantSupportTripleKZeroPullback_apply (G := G)
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
            (heq i) (hclosed i).isProperMap_subtypeVal _).trans
            ((equivariantSupportTripleKZero_generator_relations (G := G) (X := U i)).1 _ _
              (clopenExtension_same_isIsomorphic (G := G) (X := X) (U i : Set X)
                ⟨hclosed i, (U i).isOpen⟩ (heq i) a)))
    exact DFunLike.congr_fun h z
  have hoff (i j : ι) (hij : i ≠ j) (z : EquivariantSupportTripleKZero G (U i)) :
      R (F i z) j = 0 := by
    let rj := equivariantSupportTripleKZeroPullback
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U j, X))
      (heq j) (hclosed j).isProperMap_subtypeVal
    have h : rj.comp (F i) = 0 := by
      apply equivariantClopen_hom_ext
      intro a
      change rj (F i a.kZeroClass) = 0
      exact (congrArg rj (clopenExtensionKZero_apply (G := G) (X := X) (U i : Set X)
        ⟨hclosed i, (U i).isOpen⟩ (heq i) a)).trans
          ((equivariantSupportTripleKZeroPullback_apply (G := G)
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U j, X))
            (heq j) (hclosed j).isProperMap_subtypeVal _).trans
            (clopenExtension_disjoint_kZeroClass (G := G) (X := X) (U i : Set X)
              ⟨hclosed i, (U i).isOpen⟩ (heq i) a
              (U j) (hclosed j) (heq j) (hdisjoint hij)))
    exact DFunLike.congr_fun h z
  -- These same generator equations determine restriction after finite assembly.
  have hright (z : ∀ i : ι, EquivariantSupportTripleKZero G (U i)) :
      R (assemble z) = z := by
    funext j
    change R (∑ i, F i (z i)) j = z j
    rw [map_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · exact hdiag j (z j)
    · intro i _ hij
      exact hoff i j hij (z i)
    · simp
  -- The actual global reconstruction determines the other identity on the quotient.
  have hleft : assemble.comp R = AddMonoidHom.id _ := by
    apply equivariantClopen_hom_ext
    intro a
    change (∑ i, F i (R a.kZeroClass i)) = a.kZeroClass
    apply Eq.trans ?_ (hrec a).symm
    apply Finset.sum_congr rfl
    intro i _
    change clopenExtensionKZero (G := G) (X := X) (U i : Set X) ⟨hclosed i, (U i).isOpen⟩ (heq i)
      (equivariantSupportTripleKZeroPullback
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
        (heq i) (hclosed i).isProperMap_subtypeVal a.kZeroClass) = _
    exact (congrArg (F i) (equivariantSupportTripleKZeroPullback_apply (G := G)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
      (heq i) (hclosed i).isProperMap_subtypeVal a)).trans
        (clopenExtensionKZero_apply (G := G) (X := X) (U i : Set X)
          ⟨hclosed i, (U i).isOpen⟩ (heq i) _)
  exact ⟨fun x y h ↦ by
    have hx := DFunLike.congr_fun hleft x
    have hy := DFunLike.congr_fun hleft y
    exact hx.symm.trans ((congrArg assemble h).trans hy),
    fun z ↦ ⟨assemble z, hright z⟩⟩

/-- The additive decomposition whose forward map is the specified original restriction. -/
def equivariantSupportTripleKZeroClopenEquiv [Finite ι]
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)))
    (hcover : (⋃ i : ι, (U i : Set X)) = Set.univ) :
    EquivariantSupportTripleKZero G X ≃+
      (∀ i : ι, EquivariantSupportTripleKZero G (U i)) :=
  AddEquiv.ofBijective _
    (equivariantSupportTripleKZeroClopenRestrict_bijective U hclosed heq hdisjoint hcover)

set_option maxHeartbeats 800000 in
-- Compare the original zero extensions with the existing controlled open-extension maps.
/-- A finite invariant clopen cover reconstructs a class by the actual open extensions.
This is the form used after restriction to disjoint open windows around a compact control. -/
theorem equivariantSupportTripleKZero_eq_sum_clopen_openPushforward
    [Fintype ι] [CompactSpace G] [T2Space G] [LocallyCompactSpace X] [T2Space X]
    [∀ i : ι, LocallyCompactSpace (U i)]
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)))
    (hcover : (⋃ i : ι, (U i : Set X)) = Set.univ)
    (a : EquivariantSupportTripleKZero G X) :
    a = ∑ i : ι, equivariantSupportTripleKZeroOpenPushforward
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
      (U i).isOpen.isOpenEmbedding_subtypeVal (heq i)
      (equivariantSupportTripleKZeroClopenRestrict U hclosed heq a i) := by
  classical
  -- The clopen zero-extension representative has all of its control in this same piece.
  have hext (i : ι) (b : EquivariantSupportBundleTriple G (U i)) :
      (clopenExtensionEquivariantTriple (U i) ⟨hclosed i, (U i).isOpen⟩
        (heq i) b).kZeroClass =
      equivariantSupportTripleKZeroOpenPushforward
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
        (U i).isOpen.isOpenEmbedding_subtypeVal (heq i) b.kZeroClass := by
    let c := clopenExtensionEquivariantTriple (G := G) (X := X)
      (U i : Set X) ⟨hclosed i, (U i).isOpen⟩ (heq i) b
    let f : C(U i, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hc : c.1.datum.control ⊆ Set.range f := by
      rintro x ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
    have hsame : (c.openRestrict f (U i).isOpen.isOpenEmbedding_subtypeVal
        (heq i) hc).kZeroClass = b.kZeroClass := by
      apply equivariantSupportTripleKZero_generator_relations.1
      exact clopenExtension_same_isIsomorphic (G := G) (X := X)
        (U i : Set X) ⟨hclosed i, (U i).isOpen⟩ (heq i) b
    have h := equivariantSupportTripleKZeroOpenPushforward_class f
      (U i).isOpen.isOpenEmbedding_subtypeVal (heq i) c hc
    rw [hsame] at h
    exact h.symm
  -- Reconstruct the original representative with the finite disjoint bundle decomposition.
  obtain ⟨b, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
  let l : List ι := Finset.univ.toList
  have hd : l.Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) :=
    (Finset.nodup_toList _).pairwise_of_forall_ne (fun i _ j _ hij ↦ hdisjoint hij)
  have hc (x : X) : ∃ i ∈ l, x ∈ (U i : Set X) := by
    have hx : x ∈ ⋃ i : ι, (U i : Set X) := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, by simp [l], hi⟩
  have h := clopenRestrictedFold_reconstruction_class b (fun i ↦ (U i : Set X))
    (fun i ↦ ⟨hclosed i, (U i).isOpen⟩) heq l hd hc
  simp only [l, Finset.sum_map_toList] at h
  apply h.symm.trans
  apply Finset.sum_congr rfl
  intro i _
  rw [hext]
  congr 1
  exact (equivariantSupportTripleKZeroPullback_apply
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
    (heq i) (hclosed i).isProperMap_subtypeVal b).symm

end AtiyahSinger.ComplexBundle

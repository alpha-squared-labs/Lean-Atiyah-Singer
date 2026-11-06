/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTensorKZero
public import AtiyahSinger.Topology.BundleTensorRestriction
public import AtiyahSinger.Topology.CompactSupportModule
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Actual tensor coefficients for compact-support triples

Public module ID: M2191.

Tensoring on the right keeps the original compact control and applies the
original boundary only to the first tensor factor. The pullback/tensor
comparison is the identity on actual tensor vectors; its two total topologies
are compared using finite-sum generators and finite-rank inverse continuity.

For a compact coefficient base, this actual tensor triple realizes the
existing K(B)-action defined by proper graph pullback of the external product.
That action places coefficients on the left. The comparison uses the ordinary
complex tensor interchange, with no graded sign, since a coefficient bundle
is concentrated in degree zero. The continuous map itself need not be proper.
All ranks may vary locally, and zero coefficient rank is allowed.

Sources: SG Appendix C.1; Karoubi II.5.11 and II.5.14, pp.96--97. The explicit
comparison with the existing compactification graph action is a project
supplement, retaining the original coefficient bundle and support triple.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback isFiniteRank_restrict

section Pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- Pullback tensor charts make the original fiberwise identities continuous in both directions. -/
theorem continuous_pullback_tensor (f : C(Y, X)) :
    Continuous (fun z : TotalSpace Unit ((f : Y → X) *ᵖ (fun x ↦ E x ⊗[ℂ] F x)) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit
        (fun y ↦ ((f : Y → X) *ᵖ E) y ⊗[ℂ] ((f : Y → X) *ᵖ F) y))) ∧
    Continuous (fun z : TotalSpace Unit
        (fun y ↦ ((f : Y → X) *ᵖ E) y ⊗[ℂ] ((f : Y → X) *ᵖ F) y) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit ((f : Y → X) *ᵖ (fun x ↦ E x ⊗[ℂ] F x)))) := by
  /- The map from the tensor of pullbacks to the pullback of the tensor is
  continuous on each original finite-sum generator. Both bundles retain their
  existing locally finite-rank topologies; the inverse-map theorem then proves
  continuity of the inverse of this very identity on tensor vectors. No general
  commutation of arbitrary base change with final topology is used. -/
  let : IsFiniteRank (fun x ↦ E x ⊗[ℂ] F x) := isFiniteRank_tensor
  let : IsFiniteRank (((f : Y → X) *ᵖ E)) := isFiniteRank_pullback f
  let : IsFiniteRank (((f : Y → X) *ᵖ F)) := isFiniteRank_pullback f
  let : IsFiniteRank (fun x : Y ↦ (((f : Y → X) *ᵖ E)) x ⊗[ℂ] (((f : Y → X) *ᵖ F)) x) :=
    isFiniteRank_tensor
  let : IsFiniteRank (((f : Y → X) *ᵖ (fun x ↦ E x ⊗[ℂ] F x))) := isFiniteRank_pullback f
  -- Test the actual tensor final topology on each of its finite-sum generators.
  have hforward : Continuous (fun z : TotalSpace Unit
      (fun x : Y ↦ (((f : Y → X) *ᵖ E)) x ⊗[ℂ] (((f : Y → X) *ᵖ F)) x) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit (((f : Y → X) *ᵖ (fun x ↦ E x ⊗[ℂ] F x))))) := by
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit
      (fun x : Y ↦ (Fin m → ((f : Y → X) *ᵖ E) x) × (Fin m → ((f : Y → X) *ᵖ F) x))
    let D' := TotalSpace Unit (fun x : X ↦ (Fin m → E x) × (Fin m → F x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit (((f : Y → X) *ᵖ E)))),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit (((f : Y → X) *ᵖ F)))))) inferInstance
    let : TopologicalSpace D' := TopologicalSpace.induced
      (fun z : D' ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) inferInstance
    have hd : Continuous (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit (((f : Y → X) *ᵖ E)))),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit (((f : Y → X) *ᵖ F)))))) :=
      continuous_induced_dom
    let liftTuple (z : D) : D' := ⟨f z.proj, z.snd⟩
    have hlift : Continuous liftTuple := by
      apply continuous_induced_rng.mpr
      exact (f.continuous.comp hd.fst).prodMk
        ((continuous_pi fun i ↦ (Pullback.continuous_lift Unit E (f : Y → X)).comp
          ((continuous_apply i).comp hd.snd.fst)).prodMk
        (continuous_pi fun i ↦ (Pullback.continuous_lift Unit F (f : Y → X)).comp
          ((continuous_apply i).comp hd.snd.snd)))
    have hsum : Continuous (fun z : D' ↦
        (⟨z.proj, ∑ i : Fin m, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
          TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x))) :=
      continuous_iSup_rng (i := m) continuous_coinduced_rng
    rw [(inducing_pullbackTotalSpaceEmbedding Unit
      (fun x ↦ E x ⊗[ℂ] F x) (f : Y → X)).continuous_iff]
    exact hd.fst.prodMk (hsum.comp hlift)
  -- Finite local rank supplies inverse continuity for this exact identity map.
  let h : Hom (fun x : Y ↦ (((f : Y → X) *ᵖ E)) x ⊗[ℂ] (((f : Y → X) *ᵖ F)) x)
      (((f : Y → X) *ᵖ (fun x ↦ E x ⊗[ℂ] F x))) :=
    { linearMap := fun x ↦ LinearMap.id, continuous_total := hforward }
  let e := h.toIso (fun _ ↦ Function.bijective_id)
  have hback : Continuous (fun z : TotalSpace Unit (((f : Y → X) *ᵖ (fun x ↦ E x ⊗[ℂ] F x))) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit
        (fun x : Y ↦ (((f : Y → X) *ᵖ E)) x ⊗[ℂ] (((f : Y → X) *ᵖ F)) x))) := by
    refine e.continuous_symm.congr ?_
    intro z
    congr 1
    exact (e.linearEquiv z.proj).apply_symm_apply z.snd
  exact ⟨hback, hforward⟩

/-- The pullback/tensor comparison keeps each original tensor vector literally unchanged. -/
def pullbackTensorIso (f : C(Y, X)) :
    Iso ((f : Y → X) *ᵖ (fun x ↦ E x ⊗[ℂ] F x))
      (fun y ↦ ((f : Y → X) *ᵖ E) y ⊗[ℂ] ((f : Y → X) *ᵖ F) y) where
  linearEquiv y := LinearEquiv.refl ℂ (E (f y) ⊗[ℂ] F (f y))
  continuous_total := (continuous_pullback_tensor (E := E) (F := F) f).1
  continuous_symm := (continuous_pullback_tensor (E := E) (F := F) f).2

end Pullback

section Tensor

variable {Y : Type*} [TopologicalSpace Y]
  {E F : Y → Type*}
  [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (W : Y → Type*) [∀ y, AddCommGroup (W y)] [∀ y, Module ℂ (W y)]
  [TopologicalSpace (TotalSpace Unit W)] [IsFiniteRank W]
  {A : Set Y}

/-- Tensor the actual exterior map by the identity on the original right coefficient bundle. -/
def RelativeTriple.tensorRight (a : RelativeTriple E F A) :
    RelativeTriple (fun y ↦ E y ⊗[ℂ] W y) (fun y ↦ F y ⊗[ℂ] W y) A :=
  (restrictTensorIso (E := E) (F := W) A).trans
    ((a.tensor (Iso.refl (Restrict W A))).trans
      (restrictTensorIso (E := F) (F := W) A).symm)

/-- Right coefficients preserve the original support control and its original boundary action. -/
def CompactSupportTriple.tensorRight (a : CompactSupportTriple E F) :
    CompactSupportTriple (fun y ↦ E y ⊗[ℂ] W y) (fun y ↦ F y ⊗[ℂ] W y) where
  control := a.control
  isCompact_control := a.isCompact_control
  boundary := a.boundary.tensorRight W

end Tensor

section PairAction

open OnePoint Topology

universe u v

attribute [local instance] DoubleSpace.compactSpace


set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
/-- The original relative/complement class sends right tensoring to the graph action.

No properness premise is required for the supplied coefficient map.
Local finite ranks, including zero rank, are retained. This is the compact-pair form
of Karoubi II.5.14; its comparison with the specified graph and clutching models is
proved here rather than assumed from equality after forgetting relative data. -/
theorem BundleTriple.relativeClass_tensorRight_pullback
    {X : Type u} {Z : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    (A : Set Z) (hA : IsClosed A) (a : BundleTriple A) (W : FiniteBundle X) (f : C(Z, X)) :
    letI := hA.isOpen_compl.locallyCompactSpace
    relativeKZeroToCompactSupport.{_, 0} A hA
        ((BundleTriple.ofBoundary (a.source.tensor (W.pullback f))
          (a.target.tensor (W.pullback f))
          (a.boundary.tensorRight (W.pullback f).Fiber)).relativeClass hA) =
      complexKZeroCompactSupportAction (f.comp ⟨Subtype.val, continuous_subtype_val⟩)
        W.kZeroClass (relativeKZeroToCompactSupport.{_, 0} A hA (a.relativeClass hA)) := by
  classical
  -- Phase 1: compare the same graph product with finite points and open extension.
  have compact_action_absolute {Z : Type v} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (f : C(Z, X)) (w : ComplexKZero X)
      (u : CompactSupportKZero Z) :
      compactSupportKZeroToAbsolute (complexKZeroCompactSupportAction f w u) =
        kZeroMul C(Z, ℂ) (complexKZeroPullback f w) (compactSupportKZeroToAbsolute u) := by
    let a := (compactSupportKZeroCompactEquiv X).symm w
    let G := f.prodMk (ContinuousMap.id Z)
    have hG : IsProperMap G :=
      isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
    have hfinite (q : CompactSupportKZero (X × Z)) :
        compactSupportKZeroToAbsolute (compactSupportKZeroPullback G hG q) =
          complexKZeroPullback G (compactSupportKZeroToAbsolute q) := by
      change complexKZeroPullback
          ⟨((↑) : Z → OnePoint Z), OnePoint.continuous_coe⟩
          (complexKZeroPullback (properOnePointMap G hG) q.val) =
        complexKZeroPullback G
          (complexKZeroPullback
            ⟨((↑) : X × Z → OnePoint (X × Z)), OnePoint.continuous_coe⟩ q.val)
      simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      rfl
    change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback G hG (compactSupportKZeroExternalProduct a u)) = _
    rw [hfinite, compactSupportKZeroToAbsolute_externalProduct]
    have ha : compactSupportKZeroToAbsolute a = w :=
      (compactSupportKZeroCompactEquiv X).apply_symm_apply w
    rw [ha]
    change kZeroMap _ (kZeroMul _ _ _) = _
    rw [kZeroMap_mul]
    change kZeroMul C(Z, ℂ)
      (complexKZeroPullback G (complexKZeroPullback ContinuousMap.fst w))
      (complexKZeroPullback G
        (complexKZeroPullback ContinuousMap.snd (compactSupportKZeroToAbsolute u))) = _
    have hfst : (ContinuousMap.fst : C(X × Z, X)).comp G = f := rfl
    have hsnd : (ContinuousMap.snd : C(X × Z, Z)).comp G = ContinuousMap.id Z := rfl
    have hf := DFunLike.congr_fun
      (complexKZeroPullback_comp G (ContinuousMap.fst : C(X × Z, X))) w
    have hs := DFunLike.congr_fun
      (complexKZeroPullback_comp G (ContinuousMap.snd : C(X × Z, Z)))
      (compactSupportKZeroToAbsolute u)
    rw [hfst] at hf
    rw [hsnd] at hs
    have hid : complexKZeroPullback (ContinuousMap.id Z) =
        AddMonoidHom.id (ComplexKZero Z) := kZeroMap_id
    rw [hid, AddMonoidHom.id_apply] at hs
    simp only [AddMonoidHom.comp_apply] at hf hs
    rw [← hf, ← hs]
  have complement_pullback {Z Z' : Type v} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      [TopologicalSpace Z'] [CompactSpace Z'] [T2Space Z']
      (A : Set Z) (hA : IsClosed A) (p : C(Z', Z))
      (c : RelativeKZero.{_, 0} A hA) :
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := (hA.preimage p.continuous).isOpen_compl.locallyCompactSpace
      letI := (hA.isOpen_compl.preimage p.continuous).locallyCompactSpace
      relativeKZeroToCompactSupport (p ⁻¹' A) (hA.preimage p.continuous)
          (relativeKZeroPullback (p ⁻¹' A) (hA.preimage p.continuous) A hA p
            (fun _ hx ↦ hx) c) =
        compactSupportKZeroPullback (preimageSubspaceMap Aᶜ p)
          (isProperMap_preimageSubspaceMap Aᶜ p p.continuous.isProperMap)
          (relativeKZeroToCompactSupport A hA c) := by
    let := hA.isOpen_compl.locallyCompactSpace
    let B := p ⁻¹' A
    have hB : IsClosed B := hA.preimage p.continuous
    let := hB.isOpen_compl.locallyCompactSpace
    let := (hA.isOpen_compl.preimage p.continuous).locallyCompactSpace
    let := PointedQuotient.t2Space.{_, 0} A hA
    let := PointedQuotient.t2Space.{_, 0} B hB
    let eA := PointedQuotient.onePointHomeomorph.{_, 0} A hA
    let eB := PointedQuotient.onePointHomeomorph.{_, 0} B hB
    let q := PointedQuotient.mapContinuous B A p (fun _ hx ↦ hx)
    let P := properOnePointMap (preimageSubspaceMap Aᶜ p)
      (isProperMap_preimageSubspaceMap Aᶜ p p.continuous.isProperMap)
    let iA : C(OnePoint (Aᶜ : Set Z), PointedQuotient A) := ⟨eA.symm, eA.symm.continuous⟩
    let iB : C(OnePoint (Bᶜ : Set Z'), PointedQuotient B) := ⟨eB.symm, eB.symm.continuous⟩
    have hsquare : q.comp iB = iA.comp P := by
      ext z
      cases z using OnePoint.rec with
      | infty =>
        change q (eB.symm OnePoint.infty) = eA.symm OnePoint.infty
        rw [PointedQuotient.onePointHomeomorph_symm_infty,
          PointedQuotient.onePointHomeomorph_symm_infty]
        rfl
      | coe z =>
        have hBz : eB.symm (z : OnePoint (Bᶜ : Set Z')) = PointedQuotient.of B z :=
          eB.symm_apply_eq.mpr
            (PointedQuotient.onePointHomeomorph_of B hB z).symm
        have hAz : eA.symm ((preimageSubspaceMap Aᶜ p z : (Aᶜ : Set Z)) :
            OnePoint (Aᶜ : Set Z)) = PointedQuotient.of A (p z) :=
          eA.symm_apply_eq.mpr
            (PointedQuotient.onePointHomeomorph_of A hA
              (preimageSubspaceMap Aᶜ p z)).symm
        change q (eB.symm (z : OnePoint (Bᶜ : Set Z'))) =
          eA.symm ((preimageSubspaceMap Aᶜ p z : (Aᶜ : Set Z)) :
            OnePoint (Aᶜ : Set Z))
        rw [hBz, hAz]
        rfl
    apply Subtype.ext
    change complexKZeroPullback iB (complexKZeroPullback q c.val) =
      complexKZeroPullback P (complexKZeroPullback iA c.val)
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
    rfl
  have action_open_second {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y]
      [T2Space Y] (U : Set Y) (hU : IsOpen U) (f : C(Y, X))
      (a : CompactSupportKZero X) :
      letI := hU.locallyCompactSpace
      ∀ b : CompactSupportKZero U,
        compactSupportKZeroAction f a (compactSupportKZeroOpenExtension U hU b) =
          compactSupportKZeroOpenExtension U hU
            (compactSupportKZeroAction
              (f.comp ⟨Subtype.val, continuous_subtype_val⟩) a b) := by
    let := hU.locallyCompactSpace
    intro b
    let S : Set (X × Y) := Prod.snd ⁻¹' U
    have hS : IsOpen S := hU.preimage continuous_snd
    let := hS.locallyCompactSpace
    let e : S ≃ₜ X × U := {
      toFun z := (z.val.1, ⟨z.val.2, z.property⟩)
      invFun z := ⟨(z.1, z.2.val), z.2.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
      continuous_invFun :=
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _ }
    let qU : C(OnePoint Y, OnePoint U) :=
      ⟨onePointCollapse U, continuous_onePointCollapse U hU⟩
    let qP : C(OnePoint (X × Y), OnePoint (X × U)) :=
      (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap).comp
        ⟨onePointCollapse S, continuous_onePointCollapse S hS⟩
    have hqP (x : X) (y : Y) (hy : y ∈ U) :
        qP ((x, y) : OnePoint (X × Y)) =
          ((x, ⟨y, hy⟩) : X × U) := by
      change OnePoint.map e (onePointCollapse S ((x, y) : OnePoint (X × Y))) = _
      rw [onePointCollapse_coe_of_mem S (x, y) hy, OnePoint.map_some]
      rfl
    have hqPout (x : X) (y : Y) (hy : y ∉ U) :
        qP ((x, y) : OnePoint (X × Y)) = OnePoint.infty := by
      change OnePoint.map e (onePointCollapse S ((x, y) : OnePoint (X × Y))) = _
      rw [onePointCollapse_coe_of_notMem S (x, y) hy, OnePoint.map_infty]
    -- The same collapse in the second factor commutes with the original smash collapse.
    have hsmash : qP.comp onePointProductCollapseMap =
        onePointProductCollapseMap.comp
          ((ContinuousMap.id (OnePoint X)).prodMap qU) := by
      ext z
      rcases z with ⟨x, y⟩
      cases x using OnePoint.rec with
      | infty => rfl
      | coe x =>
        cases y using OnePoint.rec with
        | infty => rfl
        | coe y =>
          by_cases hy : y ∈ U
          · change qP ((x, y) : OnePoint (X × Y)) =
              onePointProductCollapse (x, onePointCollapse U (y : OnePoint Y))
            rw [hqP x y hy, onePointCollapse_coe_of_mem U y hy]
            rfl
          · change qP ((x, y) : OnePoint (X × Y)) =
              onePointProductCollapse (x, onePointCollapse U (y : OnePoint Y))
            rw [hqPout x y hy, onePointCollapse_coe_of_notMem U y hy]
            rfl
    let c : CompactSupportKZero (X × Y) :=
      reducedComplexKZeroPullback OnePoint.infty OnePoint.infty qP rfl
        (compactSupportKZeroExternalProduct a b)
    have hproduct : c = compactSupportKZeroExternalProduct a
        (compactSupportKZeroOpenExtension U hU b) := by
      apply (existsUnique_compactSupportProduct a
        (compactSupportKZeroOpenExtension U hU b)).unique ?_
          (compactSupportKZeroExternalProduct_pullback _ _)
      change complexKZeroPullback onePointProductCollapseMap
        (complexKZeroPullback qP (compactSupportKZeroExternalProduct a b).val) = _
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsmash,
        complexKZeroPullback_comp, AddMonoidHom.comp_apply,
        compactSupportKZeroExternalProduct_pullback, complexKZeroExternalProduct_natural]
      have hid : complexKZeroPullback (ContinuousMap.id (OnePoint X)) =
          AddMonoidHom.id (ComplexKZero (OnePoint X)) := kZeroMap_id
      rw [hid, AddMonoidHom.id_apply]
      rfl
    let G : C(Y, X × Y) := f.prodMk (ContinuousMap.id Y)
    let GU : C(U, X × U) :=
      (f.comp ⟨Subtype.val, continuous_subtype_val⟩).prodMk (ContinuousMap.id U)
    have hG : IsProperMap G :=
      isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
    have hGU : IsProperMap GU :=
      isProperMap_of_comp_of_t2 GU.continuous continuous_snd isProperMap_id
    have hgraph : qP.comp (properOnePointMap G hG) =
        (properOnePointMap GU hGU).comp qU := by
      ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe y =>
        by_cases hy : y ∈ U
        · change qP ((f y, y) : OnePoint (X × Y)) =
            OnePoint.map GU (onePointCollapse U (y : OnePoint Y))
          rw [hqP (f y) y hy, onePointCollapse_coe_of_mem U y hy, OnePoint.map_some]
          rfl
        · change qP ((f y, y) : OnePoint (X × Y)) =
            OnePoint.map GU (onePointCollapse U (y : OnePoint Y))
          rw [hqPout (f y) y hy, onePointCollapse_coe_of_notMem U y hy,
            OnePoint.map_infty]
    change compactSupportKZeroPullback G hG
        (compactSupportKZeroExternalProduct a (compactSupportKZeroOpenExtension U hU b)) =
      compactSupportKZeroOpenExtension U hU
        (compactSupportKZeroPullback GU hGU (compactSupportKZeroExternalProduct a b))
    rw [← hproduct]
    apply Subtype.ext
    change complexKZeroPullback (properOnePointMap G hG)
        (complexKZeroPullback qP (compactSupportKZeroExternalProduct a b).val) =
      complexKZeroPullback qU
        (complexKZeroPullback (properOnePointMap GU hGU)
          (compactSupportKZeroExternalProduct a b).val)
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hgraph,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply]
  -- Phase 2: use a proof-local action on the original relative/complement model.
  let relativeAction {Z : Type v} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (A : Set Z) (hA : IsClosed A) (g : C(Z, X))
      (w : ComplexKZero X) (c : RelativeKZero.{_, 0} A hA) : RelativeKZero.{_, 0} A hA :=
    letI := hA.isOpen_compl.locallyCompactSpace
    (relativeKZeroCompactSupportEquiv A hA).symm
      (complexKZeroCompactSupportAction (g.comp ⟨Subtype.val, continuous_subtype_val⟩) w
        (relativeKZeroToCompactSupport A hA c))
  have relativeAction_complement {Z : Type v} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (A : Set Z) (hA : IsClosed A) (g : C(Z, X))
      (w : ComplexKZero X) (c : RelativeKZero.{_, 0} A hA) :
      letI := hA.isOpen_compl.locallyCompactSpace
      relativeKZeroToCompactSupport A hA (relativeAction A hA g w c) =
        complexKZeroCompactSupportAction (g.comp ⟨Subtype.val, continuous_subtype_val⟩) w
          (relativeKZeroToCompactSupport A hA c) := by
    let := hA.isOpen_compl.locallyCompactSpace
    exact (relativeKZeroCompactSupportEquiv A hA).apply_symm_apply _
  have relativeAction_forget {Z : Type v} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (A : Set Z) (hA : IsClosed A) (g : C(Z, X))
      (w : ComplexKZero X) (c : RelativeKZero.{_, 0} A hA) :
      relativeKZeroForget A hA (relativeAction A hA g w c) =
        kZeroMul C(Z, ℂ) (complexKZeroPullback g w) (relativeKZeroForget A hA c) := by
    let := hA.isOpen_compl.locallyCompactSpace
    let c₀ := relativeKZeroToCompactSupport A hA c
    have hopen := action_open_second Aᶜ hA.isOpen_compl g
      ((compactSupportKZeroCompactEquiv X).symm w) c₀
    change complexKZeroCompactSupportAction g w
        (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl c₀) =
      compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl
        (complexKZeroCompactSupportAction
          (g.comp ⟨Subtype.val, continuous_subtype_val⟩) w c₀) at hopen
    calc
      _ = compactSupportKZeroToAbsolute
          (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl
            (relativeKZeroToCompactSupport A hA (relativeAction A hA g w c))) :=
        (relativeKZeroToCompactSupport_extension A hA _).symm
      _ = compactSupportKZeroToAbsolute
          (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl
            (complexKZeroCompactSupportAction
              (g.comp ⟨Subtype.val, continuous_subtype_val⟩) w c₀)) := by
        rw [relativeAction_complement]
      _ = compactSupportKZeroToAbsolute
          (complexKZeroCompactSupportAction g w
            (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl c₀)) :=
        congrArg compactSupportKZeroToAbsolute hopen.symm
      _ = kZeroMul C(Z, ℂ) (complexKZeroPullback g w)
          (compactSupportKZeroToAbsolute
            (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl c₀)) :=
        compact_action_absolute g w _
      _ = _ := by rw [relativeKZeroToCompactSupport_extension]
  have relativeAction_pullback {Z Z' : Type v} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      [TopologicalSpace Z'] [CompactSpace Z'] [T2Space Z']
      (A : Set Z) (hA : IsClosed A)
      (B : Set Z') (hB : IsClosed B) (p : C(Z', Z)) (hp : Set.MapsTo p B A)
      (heq : p ⁻¹' A = B) (g : C(Z, X)) (w : ComplexKZero X)
      (c : RelativeKZero.{_, 0} A hA) :
      relativeKZeroPullback B hB A hA p hp (relativeAction A hA g w c) =
        relativeAction B hB (g.comp p) w (relativeKZeroPullback B hB A hA p hp c) := by
    subst B
    let := hA.isOpen_compl.locallyCompactSpace
    let := hB.isOpen_compl.locallyCompactSpace
    let := (hA.isOpen_compl.preimage p.continuous).locallyCompactSpace
    let P := preimageSubspaceMap Aᶜ p
    have hP : IsProperMap P :=
      isProperMap_preimageSubspaceMap Aᶜ p p.continuous.isProperMap
    let i : C((Aᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
    let j : C(((p ⁻¹' A)ᶜ : Set Z'), Z') := ⟨Subtype.val, continuous_subtype_val⟩
    have hmaps : (g.comp i).comp P = (g.comp p).comp j := rfl
    apply (relativeKZeroToCompactSupport_bijective (p ⁻¹' A) hB).injective
    rw [complement_pullback, relativeAction_complement, relativeAction_complement]
    have hnatural := compactSupportKZeroPullback_action (g.comp i) P hP
      ((compactSupportKZeroCompactEquiv X).symm w)
      (relativeKZeroToCompactSupport A hA c)
    change compactSupportKZeroPullback P hP
        (complexKZeroCompactSupportAction (g.comp i) w
          (relativeKZeroToCompactSupport A hA c)) =
      complexKZeroCompactSupportAction ((g.comp i).comp P) w
        (compactSupportKZeroPullback P hP (relativeKZeroToCompactSupport A hA c)) at hnatural
    rw [hnatural, hmaps, complement_pullback]
    rfl
  -- Phase 3: tensor the original two clutching charts and verify their actual seam.
  have double_tensor {Z : Type v} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (A : Set Z) (hA : IsClosed A) (a : BundleTriple A) (W : FiniteBundle Z) :
      letI := DoubleSpace.t2Space A hA
      (BundleTriple.ofBoundary (a.source.tensor W) (a.target.tensor W)
        (a.boundary.tensorRight W.Fiber)).doubleDifference hA =
          kZeroMul C(DoubleSpace A, ℂ) (a.doubleDifference hA)
            ((W.pullback (DoubleSpace.projMap A)).kZeroClass) := by
    classical
    let := DoubleSpace.t2Space A hA
    let b := BundleTriple.ofBoundary (a.source.tensor W) (a.target.tensor W)
      (a.boundary.tensorRight W.Fiber)
    let p := DoubleSpace.projMap A
    let l := DoubleSpace.leftMap A
    let r := DoubleSpace.rightMap A
    let C := clutchingBundle hA a
    let WP := W.pullback p
    let CW := C.tensor WP
    -- Tensor the two original gluing charts with the same projected coefficient bundle.
    let wl : Iso (WP.pullback l).Fiber W.Fiber :=
      (pullbackCompIso (E := W.Fiber) p l).trans (pullbackIdIso (E := W.Fiber))
    let wr : Iso (WP.pullback r).Fiber W.Fiber :=
      (pullbackCompIso (E := W.Fiber) p r).trans (pullbackIdIso (E := W.Fiber))
    let eL : Iso (CW.pullback l).Fiber b.source.Fiber :=
      (pullbackTensorIso l).trans ((clutchingLeftIso hA a).tensor wl)
    let eR : Iso (CW.pullback r).Fiber b.target.Fiber :=
      (pullbackTensorIso r).trans ((clutchingRightIso hA a).tensor wr)
    have hwl (z : Z) (w : WP.Fiber (l z)) : wl.linearEquiv z w = w := by
      change (pullbackIdIso (E := W.Fiber)).linearEquiv z
        ((pullbackCompIso (E := W.Fiber) p l).linearEquiv z w) = w
      rw [pullbackCompIso_apply, pullbackIdIso_apply]
    have hwr (z : Z) (w : WP.Fiber (r z)) : wr.linearEquiv z w = w := by
      change (pullbackIdIso (E := W.Fiber)).linearEquiv z
        ((pullbackCompIso (E := W.Fiber) p r).linearEquiv z w) = w
      rw [pullbackCompIso_apply, pullbackIdIso_apply]
    have heL (z : Z) (v : C.Fiber (l z)) (w : WP.Fiber (l z)) :
        eL.linearEquiv z (v ⊗ₜ[ℂ] w) =
          (clutchingLeftIso hA a).linearEquiv z v ⊗ₜ[ℂ] w := by
      change (TensorProduct.congr ((clutchingLeftIso hA a).linearEquiv z)
        (wl.linearEquiv z)) (v ⊗ₜ[ℂ] w) = _
      simp only [TensorProduct.congr_tmul, hwl]
    have heR (z : Z) (v : C.Fiber (r z)) (w : WP.Fiber (r z)) :
        eR.linearEquiv z (v ⊗ₜ[ℂ] w) =
          (clutchingRightIso hA a).linearEquiv z v ⊗ₜ[ℂ] w := by
      change (TensorProduct.congr ((clutchingRightIso hA a).linearEquiv z)
        (wr.linearEquiv z)) (v ⊗ₜ[ℂ] w) = _
      simp only [TensorProduct.congr_tmul, hwr]
    have heLi (z : Z) (v : a.source.Fiber z) (w : W.Fiber z) :
        (eL.linearEquiv z).symm (v ⊗ₜ[ℂ] w) =
          ((clutchingLeftIso hA a).linearEquiv z).symm v ⊗ₜ[ℂ] w := by
      apply (eL.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply, heL, LinearEquiv.apply_symm_apply]
    have hcast {z z' : DoubleSpace A} (h : z = z') (v : C.Fiber z)
        (w : WP.Fiber z) :
        cast (congrArg CW.Fiber h) (v ⊗ₜ[ℂ] w) =
          cast (congrArg C.Fiber h) v ⊗ₜ[ℂ] cast (congrArg WP.Fiber h) w := by
      cases h
      rfl
    have hcastW (z : A) (w : W.Fiber z) :
        cast (congrArg WP.Fiber (DoubleSpace.left_eq_right A z)) w = w := by
      have hp : congrArg (fun u : DoubleSpace A ↦ W.Fiber (p u))
          (DoubleSpace.left_eq_right A z) = rfl := by
        apply Subsingleton.elim
      exact congrArg (fun h : W.Fiber z = W.Fiber z ↦ cast h w) hp
    have hseam : ClutchingCompatible b CW eL eR := by
      intro z v
      induction v using TensorProduct.inductionOn with
      | tmul v w =>
        change eR.linearEquiv z
          (cast (congrArg CW.Fiber (DoubleSpace.left_eq_right A z))
            ((eL.linearEquiv z).symm (v ⊗ₜ[ℂ] w))) = _
        rw [heLi, hcast (DoubleSpace.left_eq_right A z), hcastW z w, heR,
          clutching_seam_apply]
        rfl
      | add u v hu hv =>
        change eR.linearEquiv z
          (cast (congrArg CW.Fiber (DoubleSpace.left_eq_right A z))
            ((eL.linearEquiv z).symm (u + v))) = _
        simp only [map_add]
        have cast_add {z z' : DoubleSpace A} (h : z = z') (x y : CW.Fiber z) :
            cast (congrArg CW.Fiber h) (x + y) =
              cast (congrArg CW.Fiber h) x + cast (congrArg CW.Fiber h) y := by
          cases h
          rfl
        rw [cast_add (DoubleSpace.left_eq_right A z), map_add, hu, hv]
    obtain ⟨e⟩ := nonempty_clutching_iso hA b CW eL eR hseam
    have hclutch : (clutchingBundle hA b).kZeroClass = CW.kZeroClass :=
      (kZeroClass_eq_of_iso e).symm
    -- Both summands are the prescribed tensor product; subtract in the original order.
    have htarget : complexKZeroPullback p b.target.kZeroClass =
        kZeroMul C(DoubleSpace A, ℂ) (complexKZeroPullback p a.target.kZeroClass)
          WP.kZeroClass := by
      change complexKZeroPullback p
        (AtiyahSinger.ComplexBundle.kZeroClass (fun z ↦ a.target.Fiber z ⊗[ℂ] W.Fiber z)) = _
      rw [kZeroClass_tensor]
      change complexKZeroPullback p
        (kZeroMul C(Z, ℂ) a.target.kZeroClass W.kZeroClass) =
        kZeroMul C(DoubleSpace A, ℂ) (complexKZeroPullback p a.target.kZeroClass)
          (W.pullback p).kZeroClass
      rw [FiniteBundle.kZeroClass_pullback]
      exact kZeroMap_mul _ _ _
    change (clutchingBundle hA b).kZeroClass -
      complexKZeroPullback p b.target.kZeroClass = _
    rw [hclutch, htarget]
    change AtiyahSinger.ComplexBundle.kZeroClass (fun z ↦ C.Fiber z ⊗[ℂ] WP.Fiber z) - _ = _
    rw [kZeroClass_tensor]
    exact (map_sub ((kZeroMul C(DoubleSpace A, ℂ)).flip WP.kZeroClass)
      C.kZeroClass (complexKZeroPullback p a.target.kZeroClass)).symm
  -- Phase 4: use forgetful injectivity only for the specified double retract pair.
  let := hA.isOpen_compl.locallyCompactSpace
  let := DoubleSpace.t2Space A hA
  let WP := W.pullback f
  let b := BundleTriple.ofBoundary (a.source.tensor WP) (a.target.tensor WP)
    (a.boundary.tensorRight WP.Fiber)
  let p := DoubleSpace.projMap A
  let R := DoubleSpace.rightRange A
  have hR : IsClosed R := DoubleSpace.isClosed_rightRange A hA
  have hdouble := double_tensor A hA a WP
  change b.doubleDifference hA = kZeroMul C(DoubleSpace A, ℂ) (a.doubleDifference hA)
    (WP.pullback p).kZeroClass at hdouble
  have hcoefficient : (WP.pullback p).kZeroClass =
      complexKZeroPullback (f.comp p) W.kZeroClass := by
    rw [FiniteBundle.kZeroClass_pullback]
    change complexKZeroPullback p (W.pullback f).kZeroClass = _
    rw [FiniteBundle.kZeroClass_pullback]
    exact (DFunLike.congr_fun (complexKZeroPullback_comp p f) W.kZeroClass).symm
  have hlift : b.differenceLift hA =
      relativeAction R hR (f.comp p) W.kZeroClass (a.differenceLift hA) := by
    apply relativeKZeroForget_injective_of_retraction R hR
      (DoubleSpace.rightRetraction A) (DoubleSpace.rightRetraction_apply A)
    rw [BundleTriple.forget_differenceLift, relativeAction_forget,
      BundleTriple.forget_differenceLift, hdouble, hcoefficient]
    exact kZeroMul_comm _ _
  have hpre : (DoubleSpace.leftMap A) ⁻¹' R = A := by
    ext z
    constructor
    · rintro ⟨y, hy⟩
      exact ((DoubleSpace.left_eq_right_iff A z y).mp hy.symm).2
    · exact fun hz ↦ DoubleSpace.left_mapsTo A hz
  have hnatural := relativeAction_pullback R hR A hA (DoubleSpace.leftMap A)
    (DoubleSpace.left_mapsTo A) hpre (f.comp p) W.kZeroClass (a.differenceLift hA)
  have hmap : (f.comp p).comp (DoubleSpace.leftMap A) = f := rfl
  rw [hmap] at hnatural
  have hclass : b.relativeClass hA = relativeAction A hA f W.kZeroClass
      (a.relativeClass hA) := by
    change DoubleSpace.relativeRestriction A hA (b.differenceLift hA) = _
    rw [hlift]
    exact hnatural
  change relativeKZeroToCompactSupport A hA (b.relativeClass hA) = _
  rw [hclass, relativeAction_complement]


end PairAction

section Action

variable {X Y : Type*}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  {E F : Y → Type*}
  [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (W : X → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)] [IsFiniteRank W]


set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring the actual support triple realizes the original graph action of the bundle class. -/
theorem CompactSupportTriple.compactSupportClass_tensorRight_pullback
    (a : CompactSupportTriple E F) (f : C(Y, X)) :
    (a.tensorRight ((f : Y → X) *ᵖ W)).compactSupportClass =
      complexKZeroCompactSupportAction f (kZeroClass W) a.compactSupportClass := by
  /- Stage 1: compare the proper-graph action with open extension in its
  support factor, using the same compactification collapse maps.
  Stage 2: calculate the original triple and its right tensor in one
  compact window. The restriction/tensor and pullback-composition maps
  fix each pure tensor, giving the actual window boundary square. Apply
  the compact-pair tensor-action theorem proved above. Transport through
  the window's complement homeomorphism and extend openly; the first
  comparison identifies the result with the prescribed graph action.
  Stage 3: conjugate an arbitrary-universe triple and coefficient bundle
  through their specified small-bundle isomorphisms. Tensor induction
  verifies that these preserve the boundary. Class invariance then gives
  the displayed right-tensor identity with the original coefficient class. -/
  classical
  -- Compute open extension using the same compactification collapse and proper graph.
  have action_open_second (U : Set Y) (hU : IsOpen U) (f : C(Y, X))
      (a : CompactSupportKZero X) :
      letI := hU.locallyCompactSpace
      ∀ b : CompactSupportKZero U,
        compactSupportKZeroAction f a (compactSupportKZeroOpenExtension U hU b) =
          compactSupportKZeroOpenExtension U hU
            (compactSupportKZeroAction
              (f.comp ⟨Subtype.val, continuous_subtype_val⟩) a b) := by
    let := hU.locallyCompactSpace
    intro b
    let S : Set (X × Y) := Prod.snd ⁻¹' U
    have hS : IsOpen S := hU.preimage continuous_snd
    let := hS.locallyCompactSpace
    let e : S ≃ₜ X × U := {
      toFun z := (z.val.1, ⟨z.val.2, z.property⟩)
      invFun z := ⟨(z.1, z.2.val), z.2.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
      continuous_invFun :=
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _ }
    let qU : C(OnePoint Y, OnePoint U) :=
      ⟨onePointCollapse U, continuous_onePointCollapse U hU⟩
    let qP : C(OnePoint (X × Y), OnePoint (X × U)) :=
      (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap).comp
        ⟨onePointCollapse S, continuous_onePointCollapse S hS⟩
    have hqP (x : X) (y : Y) (hy : y ∈ U) :
        qP ((x, y) : OnePoint (X × Y)) =
          ((x, ⟨y, hy⟩) : X × U) := by
      change OnePoint.map e (onePointCollapse S ((x, y) : OnePoint (X × Y))) = _
      rw [onePointCollapse_coe_of_mem S (x, y) hy, OnePoint.map_some]
      rfl
    have hqPout (x : X) (y : Y) (hy : y ∉ U) :
        qP ((x, y) : OnePoint (X × Y)) = OnePoint.infty := by
      change OnePoint.map e (onePointCollapse S ((x, y) : OnePoint (X × Y))) = _
      rw [onePointCollapse_coe_of_notMem S (x, y) hy, OnePoint.map_infty]
    -- The same collapse in the second factor commutes with the original smash collapse.
    have hsmash : qP.comp onePointProductCollapseMap =
        onePointProductCollapseMap.comp
          ((ContinuousMap.id (OnePoint X)).prodMap qU) := by
      ext z
      rcases z with ⟨x, y⟩
      cases x using OnePoint.rec with
      | infty => rfl
      | coe x =>
        cases y using OnePoint.rec with
        | infty => rfl
        | coe y =>
          by_cases hy : y ∈ U
          · change qP ((x, y) : OnePoint (X × Y)) =
              onePointProductCollapse (x, onePointCollapse U (y : OnePoint Y))
            rw [hqP x y hy, onePointCollapse_coe_of_mem U y hy]
            rfl
          · change qP ((x, y) : OnePoint (X × Y)) =
              onePointProductCollapse (x, onePointCollapse U (y : OnePoint Y))
            rw [hqPout x y hy, onePointCollapse_coe_of_notMem U y hy]
            rfl
    let c : CompactSupportKZero (X × Y) :=
      reducedComplexKZeroPullback OnePoint.infty OnePoint.infty qP rfl
        (compactSupportKZeroExternalProduct a b)
    have hproduct : c = compactSupportKZeroExternalProduct a
        (compactSupportKZeroOpenExtension U hU b) := by
      apply (existsUnique_compactSupportProduct a
        (compactSupportKZeroOpenExtension U hU b)).unique ?_
          (compactSupportKZeroExternalProduct_pullback _ _)
      change complexKZeroPullback onePointProductCollapseMap
        (complexKZeroPullback qP (compactSupportKZeroExternalProduct a b).val) = _
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsmash,
        complexKZeroPullback_comp, AddMonoidHom.comp_apply,
        compactSupportKZeroExternalProduct_pullback, complexKZeroExternalProduct_natural]
      have hid : complexKZeroPullback (ContinuousMap.id (OnePoint X)) =
          AddMonoidHom.id (ComplexKZero (OnePoint X)) := kZeroMap_id
      rw [hid, AddMonoidHom.id_apply]
      rfl
    let G : C(Y, X × Y) := f.prodMk (ContinuousMap.id Y)
    let GU : C(U, X × U) :=
      (f.comp ⟨Subtype.val, continuous_subtype_val⟩).prodMk (ContinuousMap.id U)
    have hG : IsProperMap G :=
      isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
    have hGU : IsProperMap GU :=
      isProperMap_of_comp_of_t2 GU.continuous continuous_snd isProperMap_id
    have hgraph : qP.comp (properOnePointMap G hG) =
        (properOnePointMap GU hGU).comp qU := by
      ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe y =>
        by_cases hy : y ∈ U
        · change qP ((f y, y) : OnePoint (X × Y)) =
            OnePoint.map GU (onePointCollapse U (y : OnePoint Y))
          rw [hqP (f y) y hy, onePointCollapse_coe_of_mem U y hy, OnePoint.map_some]
          rfl
        · change qP ((f y, y) : OnePoint (X × Y)) =
            OnePoint.map GU (onePointCollapse U (y : OnePoint Y))
          rw [hqPout (f y) y hy, onePointCollapse_coe_of_notMem U y hy,
            OnePoint.map_infty]
    change compactSupportKZeroPullback G hG
        (compactSupportKZeroExternalProduct a (compactSupportKZeroOpenExtension U hU b)) =
      compactSupportKZeroOpenExtension U hU
        (compactSupportKZeroPullback GU hGU (compactSupportKZeroExternalProduct a b))
    rw [← hproduct]
    apply Subtype.ext
    change complexKZeroPullback (properOnePointMap G hG)
        (complexKZeroPullback qP (compactSupportKZeroExternalProduct a b).val) =
      complexKZeroPullback qU
        (complexKZeroPullback (properOnePointMap GU hGU)
          (compactSupportKZeroExternalProduct a b).val)
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hgraph,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply]
  -- Calculate both bundled classes in one common compact support window.
  have support_tensor_finite
      (a : SupportBundleTriple Y) (W : FiniteBundle X) (f : C(Y, X)) :
      (SupportBundleTriple.ofBoundary (a.source.tensor (W.pullback f))
        (a.target.tensor (W.pullback f))
        (a.datum.tensorRight (W.pullback f).Fiber)).compactSupportClass =
          complexKZeroCompactSupportAction f W.kZeroClass a.compactSupportClass := by
    classical
    let WP := W.pullback f
    let b := SupportBundleTriple.ofBoundary (a.source.tensor WP) (a.target.tensor WP)
      (a.datum.tensorRight WP.Fiber)
    let L := supportNeighborhood a.datum.control a.datum.isCompact_control
    have hL : IsCompact L := isCompact_supportNeighborhood _ _
    have haL : a.datum.control ⊆ interior L := subset_interior_supportNeighborhood _ _
    let := isCompact_iff_compactSpace.mp hL
    let A := supportWindowBoundary L
    have hA : IsClosed A := isClosed_supportWindowBoundary L
    let := hA.isOpen_compl.locallyCompactSpace
    let := (isOpen_interior (s := L)).locallyCompactSpace
    let i : C(L, Y) := ⟨Subtype.val, continuous_subtype_val⟩
    let fL := f.comp i
    let t := a.windowTriple L haL
    let tW := BundleTriple.ofBoundary (t.source.tensor (W.pullback fL))
      (t.target.tensor (W.pullback fL)) (t.boundary.tensorRight (W.pullback fL).Fiber)
    -- Restrict the same coefficient pullback and the same original boundary to the chosen window.
    let eS : Iso ((b.windowTriple L haL).source.Fiber) tW.source.Fiber :=
      (restrictTensorIso (E := a.source.Fiber) (F := WP.Fiber) L).trans
        ((Iso.refl (Restrict a.source.Fiber L)).tensor (pullbackCompIso (E := W.Fiber) f i))
    let eT : Iso ((b.windowTriple L haL).target.Fiber) tW.target.Fiber :=
      (restrictTensorIso (E := a.target.Fiber) (F := WP.Fiber) L).trans
        ((Iso.refl (Restrict a.target.Fiber L)).tensor (pullbackCompIso (E := W.Fiber) f i))
    have heS (z : L) (v : a.source.Fiber z.val) (w : WP.Fiber z.val) :
        eS.linearEquiv z (v ⊗ₜ[ℂ] w) = v ⊗ₜ[ℂ] w := by
      change TensorProduct.congr (LinearEquiv.refl ℂ _)
        ((pullbackCompIso (E := W.Fiber) f i).linearEquiv z)
        (v ⊗ₜ[ℂ] w) = _
      rw [TensorProduct.congr_tmul, pullbackCompIso_apply]
      rfl
    have heT (z : L) (v : a.target.Fiber z.val) (w : WP.Fiber z.val) :
        eT.linearEquiv z (v ⊗ₜ[ℂ] w) = v ⊗ₜ[ℂ] w := by
      change TensorProduct.congr (LinearEquiv.refl ℂ _)
        ((pullbackCompIso (E := W.Fiber) f i).linearEquiv z)
        (v ⊗ₜ[ℂ] w) = _
      rw [TensorProduct.congr_tmul, pullbackCompIso_apply]
      rfl
    have htriple : (b.windowTriple L haL).IsIsomorphic tW := by
      refine ⟨eS, eT, ?_⟩
      intro z
      have hmaps : (eT.linearEquiv z).toLinearMap.comp
          ((b.windowTriple L haL).boundary.linearEquiv z).toLinearMap =
          (tW.boundary.linearEquiv z).toLinearMap.comp (eS.linearEquiv z).toLinearMap := by
        apply TensorProduct.ext'
        intro v w
        change eT.linearEquiv z.val ((b.windowBoundary L haL).linearEquiv z (v ⊗ₜ[ℂ] w)) =
          tW.boundary.linearEquiv z (eS.linearEquiv z.val (v ⊗ₜ[ℂ] w))
        rw [heS, b.windowBoundary_apply L haL]
        change eT.linearEquiv z.val
          (TensorProduct.congr (a.datum.boundary.linearEquiv
            ⟨z.val.val, supportWindowBoundary_subset a.datum.control L haL z.property⟩)
            (LinearEquiv.refl ℂ _)
            (v ⊗ₜ[ℂ] w)) =
          TensorProduct.congr (t.boundary.linearEquiv z) (LinearEquiv.refl ℂ _)
            (v ⊗ₜ[ℂ] w)
        rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul]
        simp only [LinearEquiv.refl_apply, heT]
        exact congrArg (fun q : a.target.Fiber z.val.val ↦ q ⊗ₜ[ℂ] w)
          (a.windowBoundary_apply L haL z v).symm
      exact fun v ↦ LinearMap.congr_fun hmaps v
    have hrelative : (b.windowTriple L haL).relativeClass hA = tW.relativeClass hA :=
      BundleTriple.relativeClass_eq_of_isIsomorphic hA _ _ htriple
    let e := supportWindowInteriorHomeomorph L
    let j : C((Aᶜ : Set L), L) := ⟨Subtype.val, continuous_subtype_val⟩
    let g := fL.comp j
    let c := relativeKZeroToCompactSupport.{_, 0} A hA (t.relativeClass hA)
    have hpair : relativeKZeroToCompactSupport.{_, 0} A hA (tW.relativeClass hA) =
        complexKZeroCompactSupportAction g W.kZeroClass c :=
      BundleTriple.relativeClass_tensorRight_pullback A hA t W fL
    have hhomeomorph := compactSupportKZeroPullback_action g
      (⟨e.symm, e.symm.continuous⟩ : C(interior L, (Aᶜ : Set L))) e.symm.isProperMap
      ((compactSupportKZeroCompactEquiv X).symm W.kZeroClass) c
    change compactSupportKZeroHomeomorph e
        (complexKZeroCompactSupportAction g W.kZeroClass c) =
      complexKZeroCompactSupportAction (g.comp ⟨e.symm, e.symm.continuous⟩) W.kZeroClass
        (compactSupportKZeroHomeomorph e c) at hhomeomorph
    have hmap : g.comp ⟨e.symm, e.symm.continuous⟩ =
        f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(interior L, Y)) := rfl
    rw [hmap] at hhomeomorph
    have hopen := action_open_second (interior L) isOpen_interior f
      ((compactSupportKZeroCompactEquiv X).symm W.kZeroClass)
      (compactSupportKZeroHomeomorph e c)
    change complexKZeroCompactSupportAction f W.kZeroClass
        (compactSupportKZeroOpenExtension (interior L) isOpen_interior
          (compactSupportKZeroHomeomorph e c)) =
      compactSupportKZeroOpenExtension (interior L) isOpen_interior
        (complexKZeroCompactSupportAction
          (f.comp ⟨Subtype.val, continuous_subtype_val⟩) W.kZeroClass
          (compactSupportKZeroHomeomorph e c)) at hopen
    change b.compactSupportClass = _
    rw [b.compactSupportClass_eq_windowClass L hL haL,
      a.compactSupportClass_eq_windowClass L hL haL]
    change compactSupportKZeroOpenExtension (interior L) isOpen_interior
        (compactSupportKZeroHomeomorph e
          (relativeKZeroToCompactSupport.{_, 0} A hA
            ((b.windowTriple L haL).relativeClass hA))) = _
    rw [hrelative, hpair, hhomeomorph]
    exact hopen.symm
  -- Compare the actual arbitrary-universe triple through its specified small bundle models.
  let a₀ := a.toSupportBundleTriple
  let W₀ := smallBundle W
  let WP := W₀.pullback f
  let eW : Iso ((f : Y → X) *ᵖ W) WP.Fiber := (smallBundleIso W).pullback f
  let eS := (smallBundleIso E).tensor eW
  let eT := (smallBundleIso F).tensor eW
  have hdatum : (a.tensorRight ((f : Y → X) *ᵖ W)).congr eS eT =
      a₀.datum.tensorRight WP.Fiber := by
    change CompactSupportTriple.mk a.control a.isCompact_control _ =
      CompactSupportTriple.mk a.control a.isCompact_control _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul v w =>
      change TensorProduct.congr ((smallBundleIso F).linearEquiv z)
          (eW.linearEquiv z)
          (TensorProduct.congr (a.boundary.linearEquiv z) (LinearEquiv.refl ℂ _)
            (TensorProduct.congr ((smallBundleIso E).symm.linearEquiv z)
              (eW.symm.linearEquiv z) (v ⊗ₜ[ℂ] w))) =
        TensorProduct.congr (a₀.datum.boundary.linearEquiv z) (LinearEquiv.refl ℂ _)
          (v ⊗ₜ[ℂ] w)
      simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
      exact congrArg (fun q : WP.Fiber z ↦ a₀.datum.boundary.linearEquiv z v ⊗ₜ[ℂ] q)
        ((eW.linearEquiv z).apply_symm_apply w)
    | add v w hv hw => simp only [map_add, hv, hw]
  have hmodel := (a.tensorRight ((f : Y → X) *ᵖ W)).compactSupportClass_eq_model
    (a₀.source.tensor WP) (a₀.target.tensor WP) eS eT
  rw [hdatum] at hmodel
  have hcoefficient : W₀.kZeroClass = kZeroClass W :=
    (kZeroClass_eq_of_iso (smallBundleIso W)).symm
  rw [hmodel, support_tensor_finite, hcoefficient]
  rfl

end Action

end AtiyahSinger.ComplexBundle

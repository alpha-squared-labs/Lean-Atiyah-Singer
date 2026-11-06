/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SuspendedKModule

/-!
# Closed restriction and open extension in suspended compact-support K-theory

Public module ID: M2220.

The maps in every degree -n are the existing degree-zero maps on the actual
product with `Fin n → ℝ`. Closed inclusions are proper and define restriction;
open inclusions define extension through the original one-point collapse.
The explicit subspace-product homeomorphism retains both coordinates.

Multiplication by a fixed class u in Kc⁰(Y) has different support behavior on
closed and open subspaces. Restriction of u to a closed inverse image is proper
pullback. An open inclusion need not be proper, and restricting u to it need not
give a compactly supported class. The open action therefore retains u on Y and
uses the proper graph into (U × ℝⁿ) × Y. This is the base change of the original
proper graph, not pullback of u along an open inclusion.

Sources: SG I.9.26 and Appendix C.1; Karoubi II.4 and IV.1.2--1.3. These are the
standard restriction, extension and product compatibilities used in exact
sequences and closed-cover descent. No connecting homomorphism or exactness
assertion is defined by this module. Proper base change, the zero-degree
coordinate comparison and the action formulas use these same support maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual product-subspace identification, retaining the point and second coordinate. -/
def subspaceProdHomeomorph (A : Set X) (Z : Type*) [TopologicalSpace Z] :
    A × Z ≃ₜ ((Prod.fst : X × Z → X) ⁻¹' A) where
  toEquiv := (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun x ↦ x ∈ A)).symm
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)

variable [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- Homeomorphism transport in degree -n retains every real suspension coordinate. -/
def compactSupportKHomeomorphEquiv (n : ℕ) (e : X ≃ₜ Y) :
    CompactSupportK n X ≃+ CompactSupportK n Y :=
  compactSupportKZeroHomeomorphEquiv (e.prodCongr (Homeomorph.refl (Fin n → ℝ)))

/-- Closed restriction in degree -n is proper pullback along the original inclusion. -/
def compactSupportKClosedRestriction (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    CompactSupportK n X →+ CompactSupportK n A :=
  letI := hA.locallyCompactSpace
  compactSupportKPullback n ⟨Subtype.val, continuous_subtype_val⟩ hA.isProperMap_subtypeVal

/-- Open extension in degree -n uses the original collapse on the same suspended open set. -/
def compactSupportKOpenExtension (n : ℕ) (U : Set X) (hU : IsOpen U) :
    letI := hU.locallyCompactSpace
    CompactSupportK n U →+ CompactSupportK n X :=
  letI := hU.locallyCompactSpace
  let hU' : IsOpen ((Prod.fst : X × (Fin n → ℝ) → X) ⁻¹' U) :=
    hU.preimage continuous_fst
  letI := hU'.locallyCompactSpace
  (compactSupportKZeroOpenExtension (Prod.fst ⁻¹' U) (hU.preimage continuous_fst)).comp
    (compactSupportKZeroHomeomorph (subspaceProdHomeomorph U (Fin n → ℝ)))

/-- Multiplication over an open base retains the original class on Y and its proper graph. -/
def compactSupportKOpenAction (n : ℕ) (U : Set X) (hU : IsOpen U) (f : C(Y, X)) :
    letI := hU.locallyCompactSpace
    letI := (hU.preimage f.continuous).locallyCompactSpace
    CompactSupportK n U →+ CompactSupportKZero Y →+ CompactSupportK n (f ⁻¹' U) :=
  letI := hU.locallyCompactSpace
  letI := (hU.preimage f.continuous).locallyCompactSpace
  let graph : C(Y × (Fin n → ℝ), (X × (Fin n → ℝ)) × Y) :=
    (f.prodMap (ContinuousMap.id (Fin n → ℝ))).prodMk ContinuousMap.fst
  let retract : C((X × (Fin n → ℝ)) × Y, Y × (Fin n → ℝ)) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  let hgraph : IsProperMap graph :=
    isProperMap_of_comp_of_t2 graph.continuous retract.continuous isProperMap_id
  let S : Set ((X × (Fin n → ℝ)) × Y) := (fun z ↦ z.1.1) ⁻¹' U
  let domain := subspaceProdHomeomorph (f ⁻¹' U) (Fin n → ℝ)
  let codomain := ((subspaceProdHomeomorph U (Fin n → ℝ)).prodCongr
    (Homeomorph.refl Y)).trans (subspaceProdHomeomorph (Prod.fst ⁻¹' U) Y)
  let inclusion : C((f ⁻¹' U) × (Fin n → ℝ), graph ⁻¹' S) :=
    ⟨domain, domain.continuous⟩
  let projection : C(S, (U × (Fin n → ℝ)) × Y) :=
    ⟨codomain.symm, codomain.symm.continuous⟩
  compactSupportKZeroExternalProduct.compr₂
    (compactSupportKZeroPullback
      (projection.comp ((preimageSubspaceMap S graph).comp inclusion))
      (codomain.symm.isProperMap.comp
        ((isProperMap_preimageSubspaceMap S graph hgraph).comp domain.isProperMap)))

/-- Proper pullback commutes with closed restriction to the actual inverse-image subset. -/
theorem compactSupportKClosedRestriction_pullback (n : ℕ) (A : Set Y) (hA : IsClosed A)
    (f : C(X, Y)) (hf : IsProperMap f) :
    letI := hA.locallyCompactSpace
    letI := (hA.preimage f.continuous).locallyCompactSpace
    (compactSupportKClosedRestriction n (f ⁻¹' A) (hA.preimage f.continuous)).comp
        (compactSupportKPullback n f hf) =
      (compactSupportKPullback n (preimageSubspaceMap A f)
        (isProperMap_preimageSubspaceMap A f hf)).comp
          (compactSupportKClosedRestriction n A hA) := by
  /- Stage 1: both closed inclusions are proper. Base change restricts the given
  proper map f to its actual inverse-image subspace, with the same point values.
  Stage 2: after adjoining the identical real coordinate, both composites send
  (x,t) to (f(x),t). Apply proper-pullback composition to this commuting square.
  This uses closedness to preserve compact supports on both subspaces. -/
  let := hA.locallyCompactSpace
  let := (hA.preimage f.continuous).locallyCompactSpace
  -- Both proper composites retain the original point and every real coordinate.
  change (compactSupportKPullback n
    (⟨Subtype.val, continuous_subtype_val⟩ : C(f ⁻¹' A, X))
    (hA.preimage f.continuous).isProperMap_subtypeVal).comp
      (compactSupportKPullback n f hf) =
    (compactSupportKPullback n (preimageSubspaceMap A f)
      (isProperMap_preimageSubspaceMap A f hf)).comp
      (compactSupportKPullback n
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)) hA.isProperMap_subtypeVal)
  rw [← compactSupportKPullback_comp, ← compactSupportKPullback_comp]
  rfl

/-- Proper pullback commutes with extension from the inverse-image open subset. -/
theorem compactSupportKPullback_openExtension (n : ℕ) (U : Set Y) (hU : IsOpen U)
    (f : C(X, Y)) (hf : IsProperMap f) :
    letI := hU.locallyCompactSpace
    letI := (hU.preimage f.continuous).locallyCompactSpace
    (compactSupportKPullback n f hf).comp (compactSupportKOpenExtension n U hU) =
      (compactSupportKOpenExtension n (f ⁻¹' U) (hU.preimage f.continuous)).comp
        (compactSupportKPullback n (preimageSubspaceMap U f)
          (isProperMap_preimageSubspaceMap U f hf)) := by
  /- Stage 1: apply the existing degree-zero proper base-change theorem to f×id
  and the open subset U×R^n, represented as the inverse image under projection.
  Stage 2: use the specified subspace-product homeomorphisms on both domains.
  Their vector coordinates are unchanged, so the restricted product map is
  exactly the suspended restriction of f. Naturality of the original one-point
  collapse gives the displayed equality without treating an open inclusion as proper. -/
  let := hU.locallyCompactSpace
  let := (hU.preimage f.continuous).locallyCompactSpace
  let U' : Set (Y × (Fin n → ℝ)) := Prod.fst ⁻¹' U
  let V' : Set (X × (Fin n → ℝ)) := Prod.fst ⁻¹' (f ⁻¹' U)
  let F := f.prodMap (ContinuousMap.id (Fin n → ℝ))
  let hU' : IsOpen U' := hU.preimage continuous_fst
  let hV' : IsOpen V' := (hU.preimage f.continuous).preimage continuous_fst
  let := hU'.locallyCompactSpace
  let := hV'.locallyCompactSpace
  let eY := subspaceProdHomeomorph U (Fin n → ℝ)
  let eX := subspaceProdHomeomorph (f ⁻¹' U) (Fin n → ℝ)
  let jY : C(U', U × (Fin n → ℝ)) := ⟨eY.symm, eY.symm.continuous⟩
  let jX : C(V', (f ⁻¹' U) × (Fin n → ℝ)) := ⟨eX.symm, eX.symm.continuous⟩
  let F' := (preimageSubspaceMap U f).prodMap (ContinuousMap.id (Fin n → ℝ))
  -- Degree-zero base change applies to the actual suspended map and open subset.
  change (compactSupportKZeroPullback F (hf.prodMap isProperMap_id)).comp
      ((compactSupportKZeroOpenExtension U' hU').comp
        (compactSupportKZeroPullback jY eY.symm.isProperMap)) =
    ((compactSupportKZeroOpenExtension V' hV').comp
      (compactSupportKZeroPullback jX eX.symm.isProperMap)).comp
        (compactSupportKZeroPullback F'
          ((isProperMap_preimageSubspaceMap U f hf).prodMap isProperMap_id))
  let := (hU'.preimage F.continuous).locallyCompactSpace
  have hbase := compactSupportKZeroPullback_openExtension U' hU' F
    (hf.prodMap isProperMap_id)
  rw [← AddMonoidHom.comp_assoc, hbase, AddMonoidHom.comp_assoc,
    AddMonoidHom.comp_assoc]
  congr 1
  -- The restricted product map commutes with the vector-preserving subspace charts.
  have hleft := compactSupportKZeroPullback_comp (preimageSubspaceMap U' F) jY
    (isProperMap_preimageSubspaceMap U' F (hf.prodMap isProperMap_id)) eY.symm.isProperMap
  have hright := compactSupportKZeroPullback_comp jX F' eX.symm.isProperMap
    ((isProperMap_preimageSubspaceMap U f hf).prodMap isProperMap_id)
  exact hleft.symm.trans hright

/-- Closed restriction of the graph action restricts the same base class and same Y-class. -/
theorem compactSupportKClosedRestriction_action (n : ℕ) (A : Set X) (hA : IsClosed A)
    (f : C(Y, X)) (a : CompactSupportK n X) (u : CompactSupportKZero Y) :
    letI := hA.locallyCompactSpace
    letI := (hA.preimage f.continuous).locallyCompactSpace
    compactSupportKClosedRestriction n (f ⁻¹' A) (hA.preimage f.continuous)
        (compactSupportKAction n f a u) =
      compactSupportKAction n (preimageSubspaceMap A f)
        (compactSupportKClosedRestriction n A hA a)
        (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
          (hA.preimage f.continuous).isProperMap_subtypeVal u) := by
  /- Stage 1: restrict the graph (y,t) ↦ ((f(y),t),y) to the closed inverse image.
  The closed inclusions on A and on f⁻¹(A) are proper, as are their products
  with the real coordinates. The resulting graph still uses exactly f(y) and t.
  Stage 2: proper naturality of the original external product and pullback
  composition identify its two restricted factors with the displayed proper
  pullbacks. In particular u is restricted along the actual closed inclusion,
  not replaced by a local generator or pulled back along the generally nonproper f. -/
  let := hA.locallyCompactSpace
  let := (hA.preimage f.continuous).locallyCompactSpace
  let T := Fin n → ℝ
  let V : Set Y := f ⁻¹' A
  let iA : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iV : C(V, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let fA := preimageSubspaceMap A f
  let F : C(Y × T, (X × T) × Y) :=
    (f.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let H : C(V × T, (A × T) × V) :=
    (fA.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let rY : C((X × T) × Y, Y × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  let rV : C((A × T) × V, V × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous rY.continuous isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous rV.continuous isProperMap_id
  have hiA : IsProperMap iA := hA.isProperMap_subtypeVal
  have hiV : IsProperMap iV := (hA.preimage f.continuous).isProperMap_subtypeVal
  let JA := iA.prodMap (ContinuousMap.id T)
  let JV := iV.prodMap (ContinuousMap.id T)
  have hJA : IsProperMap JA := hiA.prodMap isProperMap_id
  have hJV : IsProperMap JV := hiV.prodMap isProperMap_id
  -- Both factors restrict by proper maps; this use of closedness preserves supports.
  have hproduct := compactSupportKZeroExternalProduct_properPullback JA hJA iV hiV a u
  change compactSupportKZeroPullback JV hJV
      (compactSupportKZeroPullback F hF (compactSupportKZeroExternalProduct a u)) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroPullback JA hJA a) (compactSupportKZeroPullback iV hiV u))
  rw [← hproduct]
  let L := JA.prodMap iV
  have hL : IsProperMap L := hJA.prodMap hiV
  let t := compactSupportKZeroExternalProduct a u
  -- The same original point and real vector lie in the actual inverse-image subspace.
  calc
    _ = compactSupportKZeroPullback (F.comp JV) (hF.comp hJV) t :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp JV F hJV hF) t).symm
    _ = compactSupportKZeroPullback (L.comp H) (hL.comp hH) t := by rfl
    _ = _ := DFunLike.congr_fun (compactSupportKZeroPullback_comp H L hH hL) t

/-- Open extension commutes with multiplication by the same original degree-zero Y-class. -/
theorem compactSupportKOpenExtension_action (n : ℕ) (U : Set X) (hU : IsOpen U)
    (f : C(Y, X)) (u : CompactSupportKZero Y)
    (a : letI := hU.locallyCompactSpace; CompactSupportK n U) :
    letI := (hU.preimage f.continuous).locallyCompactSpace
    compactSupportKAction n f (compactSupportKOpenExtension n U hU a) u =
      compactSupportKOpenExtension n (f ⁻¹' U) (hU.preimage f.continuous)
        (compactSupportKOpenAction n U hU f a u) := by
  /- Stage 1: external product with u commutes with open extension in the first
  factor; the one-point collapse keeps exactly U×R^n and collapses its complement.
  Compare the same smash-lift characterizations on the two sides.
  Stage 2: apply proper base change to the original suspended graph. Its inverse
  image of (U×R^n)×Y is (f⁻¹(U))×R^n. The coordinate homeomorphisms in the open
  action are the ones identifying these literal subspaces with the displayed products.
  Stage 3: the base-changed graph pullback is exactly compactSupportKOpenAction,
  giving the asserted extension formula. The original u stays on Y throughout;
  no compact-support restriction along an open inclusion is asserted. -/
  let := hU.locallyCompactSpace
  let V : Set Y := f ⁻¹' U
  let hV : IsOpen V := hU.preimage f.continuous
  let := hV.locallyCompactSpace
  let T := Fin n → ℝ
  let := (hV.preimage (continuous_fst : Continuous (Prod.fst : Y × T → Y))).locallyCompactSpace
  let U' : Set (X × T) := Prod.fst ⁻¹' U
  let hU' : IsOpen U' := hU.preimage continuous_fst
  let := hU'.locallyCompactSpace
  let F : C(Y × T, (X × T) × Y) :=
    (f.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let retract : C((X × T) × Y, Y × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous retract.continuous isProperMap_id
  let S : Set ((X × T) × Y) := Prod.fst ⁻¹' U'
  let hS : IsOpen S := hU'.preimage continuous_fst
  let := hS.locallyCompactSpace
  let W : Set (Y × T) := Prod.fst ⁻¹' V
  let hW : IsOpen W := hV.preimage continuous_fst
  let := hW.locallyCompactSpace
  let := (hS.preimage F.continuous).locallyCompactSpace
  let eU := subspaceProdHomeomorph U T
  let eV := subspaceProdHomeomorph V T
  let eS := subspaceProdHomeomorph U' Y
  let eP := eU.prodCongr (Homeomorph.refl Y)
  let e := eP.trans eS
  let jU : U' → X × T := Subtype.val
  let jS : S → (X × T) × Y := Subtype.val
  have hjU : Topology.IsOpenEmbedding jU := hU'.isOpenEmbedding_subtypeVal
  have hjS : Topology.IsOpenEmbedding jS := hS.isOpenEmbedding_subtypeVal
  -- Identify the actual image collapses with the original open extensions.
  have hfirst : compactSupportKZeroOpenPushforward jU hjU =
      compactSupportKZeroOpenExtension U' hU' := by
    let := hU'.locallyCompactSpace
    let j : U' → (X × T) := Subtype.val
    have hj : Topology.IsOpenEmbedding j := hU'.isOpenEmbedding_subtypeVal
    let := hj.isOpen_range.locallyCompactSpace
    let er := hj.isEmbedding.toHomeomorph
    let i : C(Set.range j, U') := ⟨er.symm, er.symm.continuous⟩
    let c : C(OnePoint (X × T), OnePoint (Set.range j)) :=
      ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
    let d : C(OnePoint (X × T), OnePoint U') :=
      ⟨onePointCollapse U', continuous_onePointCollapse _ hU'⟩
    have hmap : (properOnePointMap i er.symm.isProperMap).comp c = d := by
      ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe x =>
        by_cases hx : x ∈ U'
        · have hrange : x ∈ Set.range j := ⟨⟨x, hx⟩, rfl⟩
          change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U' x
          rw [onePointCollapse_coe_of_mem _ _ hrange,
            onePointCollapse_coe_of_mem _ _ hx, OnePoint.map_some]
          apply congrArg OnePoint.some
          apply Subtype.ext
          exact congrArg (fun z : Set.range j ↦ z.val) (er.apply_symm_apply ⟨x, hrange⟩)
        · have hrange : x ∉ Set.range j := by
            rintro ⟨x', rfl⟩
            exact hx x'.property
          change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U' x
          rw [onePointCollapse_coe_of_notMem _ _ hrange,
            onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
    apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    change complexKZeroPullback c
      (complexKZeroPullback (properOnePointMap i er.symm.isProperMap) a.val) =
      complexKZeroPullback d a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  have hsecond : compactSupportKZeroOpenPushforward jS hjS =
      compactSupportKZeroOpenExtension S hS := by
    let := hS.locallyCompactSpace
    let j : S → ((X × T) × Y) := Subtype.val
    have hj : Topology.IsOpenEmbedding j := hS.isOpenEmbedding_subtypeVal
    let := hj.isOpen_range.locallyCompactSpace
    let er := hj.isEmbedding.toHomeomorph
    let i : C(Set.range j, S) := ⟨er.symm, er.symm.continuous⟩
    let c : C(OnePoint ((X × T) × Y), OnePoint (Set.range j)) :=
      ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
    let d : C(OnePoint ((X × T) × Y), OnePoint S) :=
      ⟨onePointCollapse S, continuous_onePointCollapse _ hS⟩
    have hmap : (properOnePointMap i er.symm.isProperMap).comp c = d := by
      ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe x =>
        by_cases hx : x ∈ S
        · have hrange : x ∈ Set.range j := ⟨⟨x, hx⟩, rfl⟩
          change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse S x
          rw [onePointCollapse_coe_of_mem _ _ hrange,
            onePointCollapse_coe_of_mem _ _ hx, OnePoint.map_some]
          apply congrArg OnePoint.some
          apply Subtype.ext
          exact congrArg (fun z : Set.range j ↦ z.val) (er.apply_symm_apply ⟨x, hrange⟩)
        · have hrange : x ∉ Set.range j := by
            rintro ⟨x', rfl⟩
            exact hx x'.property
          change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse S x
          rw [onePointCollapse_coe_of_notMem _ _ hrange,
            onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
    apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    change complexKZeroPullback c
      (complexKZeroPullback (properOnePointMap i er.symm.isProperMap) a.val) =
      complexKZeroPullback d a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  -- Extend the product in the first factor, keeping u on the original full space Y.
  let a' := compactSupportKZeroHomeomorph eU a
  have hprod := compactSupportKZeroExternalProduct_openPushforward jU hjU
    (id : Y → Y) Topology.IsOpenEmbedding.id a' u
  rw [hfirst, compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] at hprod
  have himage := compactSupportKZeroOpenPushforward_comp eS eS.isOpenEmbedding jS hjS
  rw [hsecond, compactSupportKZeroOpenPushforward_homeomorph] at himage
  have hid : compactSupportKZeroHomeomorph (Homeomorph.refl Y) =
      AddMonoidHom.id (CompactSupportKZero Y) := compactSupportKZeroPullback_id
  have hcoords := compactSupportKZeroExternalProduct_homeomorph eU (Homeomorph.refl Y) a u
  rw [hid, AddMonoidHom.id_apply] at hcoords
  have hproduct : compactSupportKZeroExternalProduct
      (compactSupportKZeroOpenExtension U' hU' a') u =
      compactSupportKZeroOpenExtension S hS
        (compactSupportKZeroHomeomorph e (compactSupportKZeroExternalProduct a u)) := by
    rw [← hprod]
    change compactSupportKZeroOpenPushforward (jS ∘ eS) _
      (compactSupportKZeroExternalProduct a' u) = _
    rw [himage, AddMonoidHom.comp_apply]
    change compactSupportKZeroOpenExtension S hS
      (compactSupportKZeroHomeomorph eS
        (compactSupportKZeroExternalProduct (compactSupportKZeroHomeomorph eU a) u)) = _
    rw [← hcoords]
    apply congrArg (compactSupportKZeroOpenExtension S hS)
    change compactSupportKZeroPullback ⟨eS.symm, eS.symm.continuous⟩ eS.symm.isProperMap
      (compactSupportKZeroPullback ⟨eP.symm, eP.symm.continuous⟩ eP.symm.isProperMap
        (compactSupportKZeroExternalProduct a u)) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  -- Proper base change restricts exactly this original graph to its inverse image.
  let F' : C(W, S) := preimageSubspaceMap S F
  have hF' : IsProperMap F' := isProperMap_preimageSubspaceMap S F hF
  let jV : C(V × T, W) := ⟨eV, eV.continuous⟩
  let q : C(S, (U × T) × Y) := ⟨e.symm, e.symm.continuous⟩
  let R := q.comp (F'.comp jV)
  have hR : IsProperMap R := e.symm.isProperMap.comp (hF'.comp eV.isProperMap)
  let t := compactSupportKZeroExternalProduct a u
  change compactSupportKZeroPullback F hF
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroOpenExtension U' hU' a') u) =
    compactSupportKZeroOpenExtension W hW
      (compactSupportKZeroHomeomorph eV (compactSupportKZeroPullback R hR t))
  rw [hproduct]
  have hbase : compactSupportKZeroPullback F hF
      (compactSupportKZeroOpenExtension S hS (compactSupportKZeroHomeomorph e t)) =
      compactSupportKZeroOpenExtension W hW
        (compactSupportKZeroPullback F' hF' (compactSupportKZeroHomeomorph e t)) := by
    exact DFunLike.congr_fun (compactSupportKZeroPullback_openExtension S hS F hF)
      (compactSupportKZeroHomeomorph e t)
  apply hbase.trans
  apply congrArg (compactSupportKZeroOpenExtension W hW)
  -- Undo the subspace chart after the same restricted graph; the finite maps coincide.
  let iV : C(W, V × T) := ⟨eV.symm, eV.symm.continuous⟩
  have hiV : IsProperMap iV := eV.symm.isProperMap
  change compactSupportKZeroPullback F' hF'
      (compactSupportKZeroPullback q e.symm.isProperMap t) =
    compactSupportKZeroPullback iV hiV (compactSupportKZeroPullback R hR t)
  calc
    _ = compactSupportKZeroPullback (q.comp F') (e.symm.isProperMap.comp hF') t :=
      (DFunLike.congr_fun
        (compactSupportKZeroPullback_comp F' q hF' e.symm.isProperMap) t).symm
    _ = compactSupportKZeroPullback (R.comp iV) (hR.comp hiV) t := by rfl
    _ = _ := DFunLike.congr_fun (compactSupportKZeroPullback_comp iV R hiV hR) t

/-- The zero-degree coordinate comparison preserves the original open extension. -/
theorem compactSupportKZeroDegreeEquiv_openExtension (U : Set X) (hU : IsOpen U)
    (a : letI := hU.locallyCompactSpace; CompactSupportK 0 U) :
    letI := hU.locallyCompactSpace
    compactSupportKZeroDegreeEquiv X (compactSupportKOpenExtension 0 U hU a) =
      compactSupportKZeroOpenExtension U hU (compactSupportKZeroDegreeEquiv U a) := by
  /- The empty real coordinate tuple identifies U×R^0 with U and X×R^0 with X.
  The specified subspace-product homeomorphism commutes with these projections.
  Consequently the two one-point collapse maps agree at finite points and infinity.
  Pullback functoriality gives the equality for the original degree-zero extension. -/
  let := hU.locallyCompactSpace
  let U' : Set (X × (Fin 0 → ℝ)) := Prod.fst ⁻¹' U
  let hU' : IsOpen U' := hU.preimage continuous_fst
  let := hU'.locallyCompactSpace
  let eX := Homeomorph.prodUnique X (Fin 0 → ℝ)
  let eU := Homeomorph.prodUnique U (Fin 0 → ℝ)
  let e := subspaceProdHomeomorph U (Fin 0 → ℝ)
  let jX : C(X, X × (Fin 0 → ℝ)) := ⟨eX.symm, eX.symm.continuous⟩
  let jU : C(U, U × (Fin 0 → ℝ)) := ⟨eU.symm, eU.symm.continuous⟩
  let j : C(U', U × (Fin 0 → ℝ)) := ⟨e.symm, e.symm.continuous⟩
  -- Base change by the actual empty-coordinate insertion retains exactly U.
  let := (hU'.preimage jX.continuous).locallyCompactSpace
  have hbase := compactSupportKZeroPullback_openExtension U' hU' jX eX.symm.isProperMap
  have hvalue := DFunLike.congr_fun hbase
    (compactSupportKZeroPullback j e.symm.isProperMap a)
  change compactSupportKZeroPullback jX eX.symm.isProperMap
      (compactSupportKZeroOpenExtension U' hU'
        (compactSupportKZeroPullback j e.symm.isProperMap a)) =
    compactSupportKZeroOpenExtension U hU
      (compactSupportKZeroPullback jU eU.symm.isProperMap a)
  calc
    _ = compactSupportKZeroOpenExtension U hU
        (compactSupportKZeroPullback (preimageSubspaceMap U' jX)
          (isProperMap_preimageSubspaceMap U' jX eX.symm.isProperMap)
          (compactSupportKZeroPullback j e.symm.isProperMap a)) := hvalue
    _ = _ := by
      apply congrArg (compactSupportKZeroOpenExtension U hU)
      -- Both maps insert the unique empty tuple beside the same point of U.
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      rfl

end AtiyahSinger

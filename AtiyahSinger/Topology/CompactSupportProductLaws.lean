/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCompact
public import AtiyahSinger.Topology.CompactSupportProduct

/-!
# Coherence of the compact-support external product

Public module ID: M1684.

K02/P03/K03. The prescribed smash-lift product is natural under change of coordinates,
associative under the actual product associator, symmetric in degree zero, and unital
for the positive rank-one class on a point. These are statements about the existing
product and homeomorphism transport, not a new choice of either operation.

Sources: Hatcher, Vector Bundles and K-Theory, §1.1 (tensor coherence), §2.1,
pp.40–41 (absolute product), and §2.2, pp.53–54 (unique reduced smash lift).
The locally compact Hausdorff formulation applies those compact Hausdorff results
to the actual one-point compactifications. Karoubi III.1.3 uses the same external
product for iteration of Bott periodicity. No compactness, connectedness, CW,
well-pointedness or nonemptiness assumption is imposed on the original bases.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y Z X' Y' : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]
  [TopologicalSpace X'] [LocallyCompactSpace X'] [T2Space X']
  [TopologicalSpace Y'] [LocallyCompactSpace Y'] [T2Space Y']

/-- Change of coordinates preserves the specified compact-support external product. -/
theorem compactSupportKZeroExternalProduct_homeomorph (e : X ≃ₜ X') (f : Y ≃ₜ Y')
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
    compactSupportKZeroHomeomorph (e.prodCongr f) (compactSupportKZeroExternalProduct a b) =
      compactSupportKZeroExternalProduct (compactSupportKZeroHomeomorph e a)
        (compactSupportKZeroHomeomorph f b) := by
  /- Stage 1: the proper one-point extensions of e.symm and f.symm commute with
  the actual product collapse. Finite pairs retain their two inverse coordinates;
  either infinite coordinate is sent to infinity along both routes.
  Stage 2: apply absolute external-product naturality to these same extensions.
  Both displayed classes then satisfy the defining reduced smash-lift identity
  for the transported inputs. Uniqueness of that lift identifies them. This uses
  inverse pullback, precisely the specified covariant homeomorphism transport. -/
  let E := properOnePointMap (⟨e.symm, e.symm.continuous⟩ : C(X', X))
    e.symm.isProperMap
  let F := properOnePointMap (⟨f.symm, f.symm.continuous⟩ : C(Y', Y))
    f.symm.isProperMap
  let EF := properOnePointMap
    (⟨(e.prodCongr f).symm, (e.prodCongr f).symm.continuous⟩ : C(X' × Y', X × Y))
      (e.prodCongr f).symm.isProperMap
  -- The original collapse and the two inverse coordinate changes form one actual square.
  have hsquare : EF.comp (onePointProductCollapseMap (X := X') (Y := Y')) =
      (onePointProductCollapseMap (X := X) (Y := Y)).comp (E.prodMap F) := by
    ext z
    rcases z with ⟨p, q⟩
    cases p using OnePoint.rec <;> cases q using OnePoint.rec <;> rfl
  have hpull : complexKZeroPullback onePointProductCollapseMap
      (compactSupportKZeroHomeomorph (e.prodCongr f)
        (compactSupportKZeroExternalProduct a b)).val =
      complexKZeroExternalProduct (compactSupportKZeroHomeomorph e a).val
        (compactSupportKZeroHomeomorph f b).val := by
    change complexKZeroPullback onePointProductCollapseMap
      (complexKZeroPullback EF (compactSupportKZeroExternalProduct a b).val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply,
      compactSupportKZeroExternalProduct_pullback]
    exact complexKZeroExternalProduct_natural E F a.val b.val
  -- Both classes have the defining pullback for the same pair of transported inputs.
  obtain ⟨u, hu, hunique⟩ := existsUnique_compactSupportProduct
    (compactSupportKZeroHomeomorph e a) (compactSupportKZeroHomeomorph f b)
  exact (hunique _ hpull).trans
    (hunique _ (compactSupportKZeroExternalProduct_pullback _ _)).symm

/-- Associativity uses the standard reassociation of the actual three base factors. -/
theorem compactSupportKZeroExternalProduct_assoc (a : CompactSupportKZero X)
    (b : CompactSupportKZero Y) (c : CompactSupportKZero Z) :
    compactSupportKZeroHomeomorph (Homeomorph.prodAssoc X Y Z)
      (compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) c) =
        compactSupportKZeroExternalProduct a (compactSupportKZeroExternalProduct b c) := by
  /- Stage 1: identify the two iterated smash products by their actual associator.
  Each composite collapse keeps a finite triple (x,y,z) and sends a triple with
  any infinite coordinate to infinity. Reassociation changes only parentheses.
  Stage 2: pull both products back to the same three compactification factors.
  They become the two parenthesizations of three original projection pullbacks;
  kZeroMul_assoc equates them. Ordered finite-automorphism corrections on the
  three infinity faces make restriction surjective. Compact-pair exactness
  then makes the actual three-face collapse pullback injective, so the
  supported products agree for this specific split quotient. -/
  classical
  let T := OnePoint X × (OnePoint Y × OnePoint Z)
  let q : C(T, OnePoint (X × (Y × Z))) :=
    (onePointProductCollapseMap (X := X) (Y := Y × Z)).comp
      ((ContinuousMap.id (OnePoint X)).prodMap
        (onePointProductCollapseMap (X := Y) (Y := Z)))
  -- Establish injectivity for the actual three-face quotient, before comparing products.
  have hinj : Function.Injective ((complexKZeroPullback q).comp
      (reducedComplexKZero (OnePoint.infty : OnePoint (X × (Y × Z)))).subtype) := by
    let W : Set T := {z | z.1 = OnePoint.infty ∨ z.2.1 = OnePoint.infty ∨ z.2.2 = OnePoint.infty}
    have hW : IsClosed W :=
      (isClosed_eq continuous_fst continuous_const).union
        ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).union
          (isClosed_eq (continuous_snd.comp continuous_snd) continuous_const))
    let := hW.isClosedEmbedding_subtypeVal.compactSpace
    -- The finite triples are the exact open complement of the three infinity faces.
    let := hW.isOpen_compl.locallyCompactSpace
    let := PointedQuotient.compactSpace W
    let := PointedQuotient.t2Space W hW
    let i : X × (Y × Z) → T :=
      fun z ↦ ((z.1 : OnePoint X), (z.2.1 : OnePoint Y), (z.2.2 : OnePoint Z))
    have hi : Topology.IsOpenEmbedding i := OnePoint.isOpenEmbedding_coe.prodMap
      (OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe)
    have hrange : Set.range i = Wᶜ := by
      ext z
      change (∃ xyz : X × (Y × Z), i xyz = z) ↔
        ¬(z.1 = OnePoint.infty ∨ z.2.1 = OnePoint.infty ∨ z.2.2 = OnePoint.infty)
      constructor
      · rintro ⟨xyz, rfl⟩ hz
        rcases hz with hx | hy | hz
        · exact OnePoint.coe_ne_infty xyz.1 hx
        · exact OnePoint.coe_ne_infty xyz.2.1 hy
        · exact OnePoint.coe_ne_infty xyz.2.2 hz
      · intro h
        rcases z with ⟨x, y, z⟩
        cases x using OnePoint.rec with
        | infty => exact (h (Or.inl rfl)).elim
        | coe x =>
          cases y using OnePoint.rec with
          | infty => exact (h (Or.inr (Or.inl rfl))).elim
          | coe y =>
            cases z using OnePoint.rec with
            | infty => exact (h (Or.inr (Or.inr rfl))).elim
            | coe z => exact ⟨(x, y, z), rfl⟩
    let e : X × (Y × Z) ≃ₜ (Wᶜ : Set T) :=
      hi.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
    let d := PointedQuotient.onePointHomeomorph.{_, 0} W hW
    let k : C(OnePoint (X × (Y × Z)), PointedQuotient.{_, 0} W) :=
      (⟨d.symm, d.symm.continuous⟩ : C(_, _)).comp
        (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap)
    let L : RelativeKZero.{_, 0} W hW →+ CompactSupportKZero (X × (Y × Z)) :=
      (compactSupportKZeroHomeomorph e.symm).comp (relativeKZeroToCompactSupport W hW)
    have hLbij : Function.Bijective L :=
      (compactSupportKZeroHomeomorph_bijective e.symm).comp
        (relativeKZeroToCompactSupport_bijective W hW)
    have hL (z : RelativeKZero.{_, 0} W hW) :
        (L z).val = complexKZeroPullback k z.val := by
      change complexKZeroPullback (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap)
        (complexKZeroPullback ⟨d.symm, d.symm.continuous⟩ z.val) = _
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hkInfinity : k OnePoint.infty = PointedQuotient.basepoint W :=
      PointedQuotient.onePointHomeomorph_symm_infty W hW
    have hkFinite (x : X) (y : Y) (z : Z) :
        k (((x, y, z) : X × (Y × Z)) : OnePoint (X × (Y × Z))) =
          PointedQuotient.of W ((x : OnePoint X), (y : OnePoint Y), (z : OnePoint Z)) := by
      change d.symm ((e (x, y, z) : (Wᶜ : Set T)) : OnePoint (Wᶜ : Set T)) = _
      exact d.symm_apply_eq.mpr
        (PointedQuotient.onePointHomeomorph_of W hW (e (x, y, z))).symm
    have hboundary (z : T) (hz : z ∈ W) : k OnePoint.infty = PointedQuotient.of W z := by
      rw [hkInfinity]
      exact ((PointedQuotient.of_eq_basepoint_iff W z).mpr hz).symm
    have hsquare : k.comp q =
        (⟨PointedQuotient.of W, PointedQuotient.continuous_of W⟩ : C(T, _)) := by
      ext z
      rcases z with ⟨x, y, z⟩
      cases x using OnePoint.rec with
      | infty => exact hboundary _ (Or.inl rfl)
      | coe x =>
        cases y using OnePoint.rec with
        | infty => exact hboundary _ (Or.inr (Or.inl rfl))
        | coe y =>
          cases z using OnePoint.rec with
          | infty => exact hboundary _ (Or.inr (Or.inr rfl))
          | coe z => exact hkFinite x y z
    have hLformula (z : RelativeKZero.{_, 0} W hW) :
        complexKZeroPullback q (L z).val = relativeKZeroForget W hW z := by
      rw [hL, ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
      rfl
    -- Stabilize on the faces and extend the same automorphism by successive corrections.
    have restrictionSurjective :
        Function.Surjective (ComplexBundle.bundleKMinusOneRestriction W) := by
      intro a
      obtain ⟨A, hA⟩ := ComplexBundle.bundleAutomorphism_kMinusOneClass_surjective a
      obtain ⟨n, β, hβ⟩ := A.exists_trivial_representative
      let := ComplexBundle.trivialTopology (X := T) n
      let := ComplexBundle.trivialTopology (X := W) n
      let r₁₂ : C(T, W) := ⟨fun z ↦ ⟨(z.1, z.2.1, OnePoint.infty), Or.inr (Or.inr rfl)⟩,
        (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
          continuous_const)).subtype_mk _⟩
      let r₁ : C(T, W) := ⟨fun z ↦ ⟨(z.1, OnePoint.infty, OnePoint.infty), Or.inr (Or.inl rfl)⟩,
        (continuous_fst.prodMk (continuous_const.prodMk continuous_const)).subtype_mk _⟩
      let r₁₃ : C(T, W) := ⟨fun z ↦ ⟨(z.1, OnePoint.infty, z.2.2), Or.inr (Or.inl rfl)⟩,
        (continuous_fst.prodMk (continuous_const.prodMk
          (continuous_snd.comp continuous_snd))).subtype_mk _⟩
      let r₂ : C(T, W) := ⟨fun z ↦ ⟨(OnePoint.infty, z.2.1, OnePoint.infty), Or.inl rfl⟩,
        (continuous_const.prodMk ((continuous_fst.comp continuous_snd).prodMk
          continuous_const)).subtype_mk _⟩
      let r₀ : C(T, W) :=
        ContinuousMap.const T ⟨(OnePoint.infty, OnePoint.infty, OnePoint.infty), Or.inl rfl⟩
      let r₃ : C(T, W) := ⟨fun z ↦ ⟨(OnePoint.infty, OnePoint.infty, z.2.2), Or.inl rfl⟩,
        (continuous_const.prodMk (continuous_const.prodMk
          (continuous_snd.comp continuous_snd))).subtype_mk _⟩
      let r₂₃ : C(T, W) := ⟨fun z ↦ ⟨(OnePoint.infty, z.2.1, z.2.2), Or.inl rfl⟩,
        (continuous_const.prodMk continuous_snd).subtype_mk _⟩
      let lift (f : C(T, W)) :
          ComplexBundle.Iso (ComplexBundle.FiniteBundle.trivial T n).Fiber
            (ComplexBundle.FiniteBundle.trivial T n).Fiber :=
        (((ComplexBundle.pullbackTrivialIso f n).symm.trans (β.pullback f)).trans
          (ComplexBundle.pullbackTrivialIso f n))
      have htrivial (f : C(T, W)) (x : T) (v : Fin n → ℂ) :
          ((ComplexBundle.pullbackTrivialIso f n).linearEquiv x).symm v = v := by
        apply ((ComplexBundle.pullbackTrivialIso f n).linearEquiv x).injective
        rw [LinearEquiv.apply_symm_apply, ComplexBundle.pullbackTrivialIso_apply]
      have hlift (f : C(T, W)) (x : T) : (lift f).linearEquiv x = β.linearEquiv (f x) := by
        apply LinearEquiv.ext
        intro v
        change (ComplexBundle.pullbackTrivialIso f n).linearEquiv x
          (β.linearEquiv (f x) (((ComplexBundle.pullbackTrivialIso f n).linearEquiv x).symm v)) = _
        rw [ComplexBundle.pullbackTrivialIso_apply, htrivial]
      -- The first patch agrees on z = infinity and y = infinity.
      -- Its x = infinity restriction is δ; the final correction restores that face.
      -- Keep this order, since the actual matrix automorphisms need not commute.
      let γ₁ := ((lift r₁₃).trans (lift r₁).symm).trans (lift r₁₂)
      let δ := ((lift r₃).trans (lift r₀).symm).trans (lift r₂)
      let γ := ((lift r₂₃).trans δ.symm).trans γ₁
      have hγ (w : W) (v : Fin n → ℂ) : γ.linearEquiv w.val v = β.linearEquiv w v := by
        change (lift r₁₂).linearEquiv w.val
          (((lift r₁).linearEquiv w.val).symm ((lift r₁₃).linearEquiv w.val
            (((lift r₃).linearEquiv w.val).symm ((lift r₀).linearEquiv w.val
              (((lift r₂).linearEquiv w.val).symm ((lift r₂₃).linearEquiv w.val v)))))) = _
        rw [hlift, hlift, hlift, hlift, hlift, hlift, hlift]
        rcases w.property with hx | hy | hz
        · have h₁₂ : r₁₂ w.val = r₂ w.val := by
            apply Subtype.ext
            exact Prod.ext hx rfl
          have h₁ : r₁ w.val = r₀ w.val := Subtype.ext (Prod.ext hx rfl)
          have h₁₃ : r₁₃ w.val = r₃ w.val := Subtype.ext (Prod.ext hx rfl)
          have h₂₃ : r₂₃ w.val = w := Subtype.ext (Prod.ext hx.symm rfl)
          rw [h₁₂, h₁, h₁₃, h₂₃, LinearEquiv.apply_symm_apply,
            LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
        · have h₁₂ : r₁₂ w.val = r₁ w.val :=
            Subtype.ext (Prod.ext rfl (Prod.ext hy rfl))
          have h₁₃ : r₁₃ w.val = w :=
            Subtype.ext (Prod.ext rfl (Prod.ext hy.symm rfl))
          have h₂ : r₂ w.val = r₀ w.val :=
            Subtype.ext (Prod.ext rfl (Prod.ext hy rfl))
          have h₂₃ : r₂₃ w.val = r₃ w.val :=
            Subtype.ext (Prod.ext rfl (Prod.ext hy rfl))
          rw [h₁₂, h₁₃, h₂, h₂₃, LinearEquiv.apply_symm_apply,
            LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
        · have h₁₂ : r₁₂ w.val = w :=
            Subtype.ext (Prod.ext rfl (Prod.ext rfl hz.symm))
          have h₁₃ : r₁₃ w.val = r₁ w.val :=
            Subtype.ext (Prod.ext rfl (Prod.ext rfl hz))
          have h₃ : r₃ w.val = r₀ w.val :=
            Subtype.ext (Prod.ext rfl (Prod.ext rfl hz))
          have h₂₃ : r₂₃ w.val = r₂ w.val :=
            Subtype.ext (Prod.ext rfl (Prod.ext rfl hz))
          rw [h₁₂, h₁₃, h₃, h₂₃, LinearEquiv.symm_apply_apply,
            LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      let Γ : ComplexBundle.BundleAutomorphism T :=
        ⟨ComplexBundle.FiniteBundle.trivial T n, γ⟩
      let j : C(W, T) := ⟨Subtype.val, continuous_subtype_val⟩
      have hIso : (Γ.pullback j).IsIsomorphic ⟨ComplexBundle.FiniteBundle.trivial W n, β⟩ := by
        refine ⟨ComplexBundle.pullbackTrivialIso j n, ?_⟩
        intro w v
        change Fin n → ℂ at v
        change (ComplexBundle.pullbackTrivialIso j n).linearEquiv w (γ.linearEquiv w.val v) =
          β.linearEquiv w ((ComplexBundle.pullbackTrivialIso j n).linearEquiv w v)
        rw [ComplexBundle.pullbackTrivialIso_apply, ComplexBundle.pullbackTrivialIso_apply, hγ]
      refine ⟨Γ.kMinusOneClass, ?_⟩
      change ComplexBundle.bundleKMinusOnePullback j Γ.kMinusOneClass = a
      rw [ComplexBundle.bundleKMinusOnePullback_class]
      exact (ComplexBundle.BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hIso).trans
        (hβ.trans hA)
    -- The preceding actual extension kills the boundary obstruction to injectivity.
    let F : RelativeKZero.{_, 0} W hW →+ ComplexKZero T := relativeKZeroForget W hW
    have hFinj : Function.Injective F := by
      apply (injective_iff_map_eq_zero _).mpr
      intro z hz
      have hexact : (ComplexBundle.bundleKMinusOneBoundary W hW).range = F.ker :=
        ComplexBundle.range_bundleKMinusOneBoundary W hW
      obtain ⟨v, hv⟩ := hexact.ge hz
      obtain ⟨w, hw⟩ := restrictionSurjective v
      have hzero : ComplexBundle.bundleKMinusOneBoundary W hW v = 0 :=
        (ComplexBundle.range_bundleKMinusOneRestriction W hW).le ⟨w, hw⟩
      exact hv.symm.trans hzero
    intro x y hxy
    obtain ⟨z, rfl⟩ := hLbij.2 x
    obtain ⟨w, rfl⟩ := hLbij.2 y
    apply congrArg L
    apply hFinj
    change complexKZeroPullback q (L z).val = complexKZeroPullback q (L w).val at hxy
    simpa only [hLformula] using hxy
  apply hinj
  change complexKZeroPullback q
      (compactSupportKZeroHomeomorph (Homeomorph.prodAssoc X Y Z)
        (compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) c)).val =
    complexKZeroPullback q
      (compactSupportKZeroExternalProduct a (compactSupportKZeroExternalProduct b c)).val
  -- Compare the two parenthesizations on the same three compactification factors.
  let S := (OnePoint X × OnePoint Y) × OnePoint Z
  let A : C(T, S) :=
    ⟨(Homeomorph.prodAssoc (OnePoint X) (OnePoint Y) (OnePoint Z)).symm,
      (Homeomorph.prodAssoc (OnePoint X) (OnePoint Y) (OnePoint Z)).symm.continuous⟩
  let u := (onePointProductCollapseMap (X := X) (Y := Y)).prodMap
    (ContinuousMap.id (OnePoint Z))
  let v := (ContinuousMap.id (OnePoint X)).prodMap
    (onePointProductCollapseMap (X := Y) (Y := Z))
  let qL : C(S, OnePoint ((X × Y) × Z)) :=
    (onePointProductCollapseMap (X := X × Y) (Y := Z)).comp u
  let E := properOnePointMap
    (⟨(Homeomorph.prodAssoc X Y Z).symm, (Homeomorph.prodAssoc X Y Z).symm.continuous⟩ :
      C(X × (Y × Z), (X × Y) × Z)) (Homeomorph.prodAssoc X Y Z).symm.isProperMap
  have hsquare : E.comp q = qL.comp A := by
    ext z
    rcases z with ⟨x, y, z⟩
    cases x using OnePoint.rec <;> cases y using OnePoint.rec <;>
      cases z using OnePoint.rec <;> rfl
  have hIdX : complexKZeroPullback (ContinuousMap.id (OnePoint X)) a.val = a.val := by
    change kZeroMap (RingHom.id C(OnePoint X, ℂ)) a.val = a.val
    rw [kZeroMap_id]
    rfl
  have hIdZ : complexKZeroPullback (ContinuousMap.id (OnePoint Z)) c.val = c.val := by
    change kZeroMap (RingHom.id C(OnePoint Z, ℂ)) c.val = c.val
    rw [kZeroMap_id]
    rfl
  have hleft : complexKZeroPullback qL
      (compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) c).val =
      complexKZeroExternalProduct (complexKZeroExternalProduct a.val b.val) c.val := by
    change complexKZeroPullback
      ((onePointProductCollapseMap (X := X × Y) (Y := Z)).comp u) _ = _
    rw [complexKZeroPullback_comp, AddMonoidHom.comp_apply,
      compactSupportKZeroExternalProduct_pullback]
    change complexKZeroPullback
      ((onePointProductCollapseMap (X := X) (Y := Y)).prodMap
        (ContinuousMap.id (OnePoint Z))) _ = _
    rw [complexKZeroExternalProduct_natural, compactSupportKZeroExternalProduct_pullback,
      hIdZ]
  have hright : complexKZeroPullback q
      (compactSupportKZeroExternalProduct a (compactSupportKZeroExternalProduct b c)).val =
      complexKZeroExternalProduct a.val (complexKZeroExternalProduct b.val c.val) := by
    change complexKZeroPullback
      ((onePointProductCollapseMap (X := X) (Y := Y × Z)).comp v) _ = _
    rw [complexKZeroPullback_comp, AddMonoidHom.comp_apply,
      compactSupportKZeroExternalProduct_pullback]
    change complexKZeroPullback ((ContinuousMap.id (OnePoint X)).prodMap
      (onePointProductCollapseMap (X := Y) (Y := Z))) _ = _
    rw [complexKZeroExternalProduct_natural, hIdX,
      compactSupportKZeroExternalProduct_pullback]
  -- The absolute products are multiplication of the same three projection pullbacks.
  let x : C(T, OnePoint X) := ContinuousMap.fst
  let y : C(T, OnePoint Y) := ContinuousMap.fst.comp ContinuousMap.snd
  let z : C(T, OnePoint Z) := ContinuousMap.snd.comp ContinuousMap.snd
  let xy : C(T, OnePoint X × OnePoint Y) := ContinuousMap.fst.comp A
  let yz : C(T, OnePoint Y × OnePoint Z) := ContinuousMap.snd
  have hxyProduct : complexKZeroPullback xy (complexKZeroExternalProduct a.val b.val) =
      kZeroMul C(T, ℂ) (complexKZeroPullback x a.val) (complexKZeroPullback y b.val) := by
    change kZeroMap _ (kZeroMul _ _ _) = _
    rw [kZeroMap_mul]
    change kZeroMul C(T, ℂ)
      (complexKZeroPullback xy (complexKZeroPullback ContinuousMap.fst a.val))
      (complexKZeroPullback xy (complexKZeroPullback ContinuousMap.snd b.val)) = _
    have hx : complexKZeroPullback xy (complexKZeroPullback ContinuousMap.fst a.val) =
        complexKZeroPullback x a.val := by
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      rfl
    have hy : complexKZeroPullback xy (complexKZeroPullback ContinuousMap.snd b.val) =
        complexKZeroPullback y b.val := by
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      rfl
    rw [hx, hy]
  have hyzProduct : complexKZeroPullback yz (complexKZeroExternalProduct b.val c.val) =
      kZeroMul C(T, ℂ) (complexKZeroPullback y b.val) (complexKZeroPullback z c.val) := by
    change kZeroMap _ (kZeroMul _ _ _) = _
    rw [kZeroMap_mul]
    change kZeroMul C(T, ℂ)
      (complexKZeroPullback yz (complexKZeroPullback ContinuousMap.fst b.val))
      (complexKZeroPullback yz (complexKZeroPullback ContinuousMap.snd c.val)) = _
    have hy : complexKZeroPullback yz (complexKZeroPullback ContinuousMap.fst b.val) =
        complexKZeroPullback y b.val := by
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hz : complexKZeroPullback yz (complexKZeroPullback ContinuousMap.snd c.val) =
        complexKZeroPullback z c.val := by
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rw [hy, hz]
  have habs : complexKZeroPullback A
      (complexKZeroExternalProduct (complexKZeroExternalProduct a.val b.val) c.val) =
      complexKZeroExternalProduct a.val (complexKZeroExternalProduct b.val c.val) := by
    change kZeroMap _ (kZeroMul _ _ _) = _
    rw [kZeroMap_mul]
    change kZeroMul C(T, ℂ)
      (complexKZeroPullback A
        (complexKZeroPullback ContinuousMap.fst (complexKZeroExternalProduct a.val b.val)))
      (complexKZeroPullback A (complexKZeroPullback ContinuousMap.snd c.val)) =
      kZeroMul C(T, ℂ) (complexKZeroPullback x a.val)
        (complexKZeroPullback yz (complexKZeroExternalProduct b.val c.val))
    have hfirst : complexKZeroPullback A
        (complexKZeroPullback ContinuousMap.fst (complexKZeroExternalProduct a.val b.val)) =
        complexKZeroPullback xy (complexKZeroExternalProduct a.val b.val) := by
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hthird : complexKZeroPullback A (complexKZeroPullback ContinuousMap.snd c.val) =
        complexKZeroPullback z c.val := by
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      rfl
    rw [hfirst, hxyProduct, hthird, hyzProduct]
    exact kZeroMul_assoc _ _ _
  change complexKZeroPullback q (complexKZeroPullback E _) = complexKZeroPullback q _
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
    complexKZeroPullback_comp, AddMonoidHom.comp_apply, hleft, hright]
  exact habs

/-- Interchanging factors preserves the even compact-support external product. -/
theorem compactSupportKZeroExternalProduct_swap (a : CompactSupportKZero X)
    (b : CompactSupportKZero Y) :
    compactSupportKZeroHomeomorph (Homeomorph.prodComm X Y)
      (compactSupportKZeroExternalProduct a b) = compactSupportKZeroExternalProduct b a := by
  /- Stage 1: swapping the compactification factors commutes with the product
  collapse and the actual finite-pair swap. Apply absolute product symmetry.
  Stage 2: both classes have the same defining pullback, so uniqueness of the
  reduced smash lift gives equality. Both inputs have degree zero; hence no
  Koszul sign occurs. This statement does not permute any odd K-theory groups. -/
  let S := properOnePointMap
    (⟨(Homeomorph.prodComm X Y).symm, (Homeomorph.prodComm X Y).symm.continuous⟩ :
      C(Y × X, X × Y)) (Homeomorph.prodComm X Y).symm.isProperMap
  -- The inverse finite swap and the compactification swap keep the same coordinates.
  have hsquare : S.comp (onePointProductCollapseMap (X := Y) (Y := X)) =
      (onePointProductCollapseMap (X := X) (Y := Y)).comp ContinuousMap.prodSwap := by
    ext z
    rcases z with ⟨p, q⟩
    cases p using OnePoint.rec <;> cases q using OnePoint.rec <;> rfl
  have hpull : complexKZeroPullback onePointProductCollapseMap
      (compactSupportKZeroHomeomorph (Homeomorph.prodComm X Y)
        (compactSupportKZeroExternalProduct a b)).val =
      complexKZeroExternalProduct b.val a.val := by
    change complexKZeroPullback onePointProductCollapseMap
      (complexKZeroPullback S (compactSupportKZeroExternalProduct a b).val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply,
      compactSupportKZeroExternalProduct_pullback]
    exact complexKZeroExternalProduct_swap b.val a.val
  -- Apply uniqueness to these actual swapped reduced inputs.
  obtain ⟨u, hu, hunique⟩ := existsUnique_compactSupportProduct b a
  exact (hunique _ hpull).trans
    (hunique _ (compactSupportKZeroExternalProduct_pullback b a)).symm

/-- The standard positive rank-one class in compactly supported K⁰ of a point. -/
def compactSupportKZeroPointOne : CompactSupportKZero PUnit.{1} :=
  (compactSupportKZeroCompactEquiv PUnit.{1}).symm
    (kZeroClass C(PUnit.{1}, ℂ) (IdempotentMatrix.identity C(PUnit.{1}, ℂ) 1))

/-- The positive point class is a left unit under the actual projection from point × X. -/
theorem compactSupportKZeroExternalProduct_one_left (a : CompactSupportKZero X) :
    compactSupportKZeroHomeomorph (Homeomorph.uniqueProd PUnit.{1} X)
      (compactSupportKZeroExternalProduct compactSupportKZeroPointOne a) = a := by
  /- Stage 1: finite restriction identifies the point class with the free
  rank-one class. Pull the smash-product equation back along the finite
  point component times X-plus. Its composite collapse is exactly the
  one-point extension of the inverse point-product projection.
  Stage 2: absolute pullback naturality identifies the first tensor
  factor with the rank-one unit and the second with the original a.
  The law kZeroMul_one_left proves equality of underlying absolute
  classes, hence equality in the original evaluation kernel. -/
  let p : PUnit.{1} := PUnit.unit
  let s : C(OnePoint X, OnePoint PUnit.{1} × OnePoint X) :=
    (ContinuousMap.const _ (p : OnePoint PUnit.{1})).prodMk (ContinuousMap.id _)
  let e := Homeomorph.uniqueProd PUnit.{1} X
  let E := properOnePointMap (⟨e.symm, e.symm.continuous⟩ : C(X, PUnit.{1} × X))
    e.symm.isProperMap
  -- Restriction to the finite point component is exactly the inverse projection extension.
  have hsquare : (onePointProductCollapseMap (X := PUnit.{1}) (Y := X)).comp s = E := by
    ext z
    cases z using OnePoint.rec <;> rfl
  have hone : compactSupportKZeroToAbsolute compactSupportKZeroPointOne =
      kZeroClass C(PUnit.{1}, ℂ) (IdempotentMatrix.identity C(PUnit.{1}, ℂ) 1) :=
    (compactSupportKZeroCompactEquiv PUnit.{1}).apply_symm_apply _
  let i : C(PUnit.{1}, OnePoint PUnit.{1}) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  let t : C(OnePoint X, PUnit.{1}) := ContinuousMap.const _ p
  have hfinite : (ContinuousMap.fst : C(OnePoint PUnit.{1} × OnePoint X,
      OnePoint PUnit.{1})).comp s = i.comp t := rfl
  have hfirst : complexKZeroPullback s
      (complexKZeroPullback ContinuousMap.fst compactSupportKZeroPointOne.val) =
        kZeroClass C(OnePoint X, ℂ) (IdempotentMatrix.identity C(OnePoint X, ℂ) 1) := by
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hfinite,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply]
    change complexKZeroPullback t
      (compactSupportKZeroToAbsolute compactSupportKZeroPointOne) = _
    rw [hone]
    change kZeroMap _ (kZeroClass _ _) = _
    rw [kZeroMap_class]
    congr 1
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact (ContinuousMap.compRightAlgHom ℂ ℂ t).toRingHom.mapMatrix.map_one
  have hsecond : complexKZeroPullback s
      (complexKZeroPullback ContinuousMap.snd a.val) = a.val := by
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    change kZeroMap (RingHom.id C(OnePoint X, ℂ)) a.val = a.val
    rw [kZeroMap_id]
    rfl
  -- The product equation on this component is multiplication by the positive rank-one unit.
  have h := congrArg (complexKZeroPullback s)
    (compactSupportKZeroExternalProduct_pullback compactSupportKZeroPointOne a)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare] at h
  apply Subtype.ext
  change complexKZeroPullback E
    (compactSupportKZeroExternalProduct compactSupportKZeroPointOne a).val = a.val
  apply h.trans
  change kZeroMap _ (kZeroMul _ _ _) = _
  rw [kZeroMap_mul]
  change kZeroMul C(OnePoint X, ℂ)
    (complexKZeroPullback s
      (complexKZeroPullback ContinuousMap.fst compactSupportKZeroPointOne.val))
    (complexKZeroPullback s (complexKZeroPullback ContinuousMap.snd a.val)) = _
  rw [hfirst, hsecond]
  exact kZeroMul_one_left a.val

/-- The positive point class is a right unit under the actual projection from X × point. -/
theorem compactSupportKZeroExternalProduct_one_right (a : CompactSupportKZero X) :
    compactSupportKZeroHomeomorph (Homeomorph.prodUnique X PUnit.{1})
      (compactSupportKZeroExternalProduct a compactSupportKZeroPointOne) = a := by
  /- Interchange the two factors using the preceding symmetry statement and
  apply the left unit law. The swap followed by PUnit×X→X is exactly the
  projection X×PUnit→X. Proper pullback composition identifies these actual
  transports, so the conclusion holds for the specified right projection. -/
  let s := Homeomorph.prodComm X PUnit.{1}
  let l := Homeomorph.uniqueProd PUnit.{1} X
  let r := Homeomorph.prodUnique X PUnit.{1}
  have htransport : (compactSupportKZeroHomeomorph l).comp
      (compactSupportKZeroHomeomorph s) = compactSupportKZeroHomeomorph r := by
    change (compactSupportKZeroPullback ⟨l.symm, l.symm.continuous⟩ l.symm.isProperMap).comp
      (compactSupportKZeroPullback ⟨s.symm, s.symm.continuous⟩ s.symm.isProperMap) = _
    rw [← compactSupportKZeroPullback_comp]
    rfl
  -- The two actual transports compose to the prescribed right projection.
  calc
    compactSupportKZeroHomeomorph r
        (compactSupportKZeroExternalProduct a compactSupportKZeroPointOne) =
        compactSupportKZeroHomeomorph l (compactSupportKZeroHomeomorph s
          (compactSupportKZeroExternalProduct a compactSupportKZeroPointOne)) :=
      (DFunLike.congr_fun htransport _).symm
    _ = compactSupportKZeroHomeomorph l
        (compactSupportKZeroExternalProduct compactSupportKZeroPointOne a) := by
      rw [compactSupportKZeroExternalProduct_swap]
    _ = a := compactSupportKZeroExternalProduct_one_left a

end AtiyahSinger

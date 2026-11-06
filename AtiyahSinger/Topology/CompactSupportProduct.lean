/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BottLine
public import AtiyahSinger.Topology.BundleKMinusOneExactness
public import AtiyahSinger.Topology.CompactSupportKZero
public import AtiyahSinger.Topology.KZeroExternalProduct

/-!
# External products with compact supports

Public module ID: M1683.

K02/P03/K03. The collapse X⁺ × Y⁺ → (X × Y)⁺ identifies the smash product with
the one-point compactification of the product. The exterior product is the unique
reduced class whose pullback is the absolute product. Its existence, uniqueness
and biadditivity are proved below for these actual maps.

Source: Hatcher, Vector Bundles and K-Theory, §2.2, pp.51–54 (closed-pair exactness
and reduced external product). The passage to arbitrary locally compact Hausdorff
bases is by their actual one-point compactifications. No properness of the two
projections is asserted. The uniqueness proof uses the split wedge restriction;
the forgetful map for a general closed pair need not be injective.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

variable {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

/-- Collapse both axes at infinity and keep each finite pair as the same finite pair. -/
def onePointProductCollapse : OnePoint X × OnePoint Y → OnePoint (X × Y) :=
  fun z ↦ z.1.elim ∞ (fun x ↦ z.2.elim ∞ (fun y ↦ ((x, y) : OnePoint (X × Y))))

/-- The product collapse is continuous for locally compact Hausdorff bases. -/
theorem continuous_onePointProductCollapse :
    Continuous (onePointProductCollapse (X := X) (Y := Y)) := by
  /- On the open finite-pair locus this is the product open embedding. If K
  is compact in X × Y, its image in X⁺ × Y⁺ is compact and hence closed.
  The inverse image of the complement of K is its open complement, giving
  continuity at both axes, including their intersection (∞,∞). -/
  classical
  let i : X × Y → OnePoint X × OnePoint Y :=
    fun z ↦ ((z.1 : OnePoint X), (z.2 : OnePoint Y))
  have hi : Topology.IsOpenEmbedding i :=
    OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe
  apply continuous_def.mpr
  intro s hs
  by_cases hinfty : (∞ : OnePoint (X × Y)) ∈ s
  · -- A neighborhood of infinity omits a compact set of actual finite pairs.
    have hK := (OnePoint.isOpen_iff_of_mem hinfty).mp hs
    have hcompact : IsCompact (i '' (((↑) : X × Y → OnePoint (X × Y)) ⁻¹' s)ᶜ) :=
      hK.2.image hi.continuous
    have hpre : onePointProductCollapse ⁻¹' s =
        (i '' (((↑) : X × Y → OnePoint (X × Y)) ⁻¹' s)ᶜ)ᶜ := by
      ext z
      rcases z with ⟨p, q⟩
      cases p using OnePoint.rec <;> cases q using OnePoint.rec <;>
        simp [onePointProductCollapse, i, hinfty]
    rw [hpre]
    exact hcompact.isClosed.isOpen_compl
  · -- On finite pairs the original product open embedding gives the inverse image.
    have hopen := (OnePoint.isOpen_iff_of_notMem hinfty).mp hs
    have hpre : onePointProductCollapse ⁻¹' s =
        i '' (((↑) : X × Y → OnePoint (X × Y)) ⁻¹' s) := by
      ext z
      rcases z with ⟨p, q⟩
      cases p using OnePoint.rec <;> cases q using OnePoint.rec <;>
        simp [onePointProductCollapse, i, hinfty]
    rw [hpre]
    exact hi.isOpenMap _ hopen

/-- The bundled quotient map realizing X⁺ smash Y⁺ as (X × Y)⁺. -/
def onePointProductCollapseMap : C(OnePoint X × OnePoint Y, OnePoint (X × Y)) :=
  ⟨onePointProductCollapse, continuous_onePointProductCollapse⟩

/-- Every pair of reduced classes has a unique product lift across the smash collapse. -/
theorem existsUnique_compactSupportProduct (a : CompactSupportKZero X)
    (b : CompactSupportKZero Y) :
    ∃! c : CompactSupportKZero (X × Y),
      complexKZeroPullback onePointProductCollapseMap c.val =
        complexKZeroExternalProduct a.val b.val := by
  /- Stage 1: the absolute external product restricts to zero on each axis,
  since its corresponding factor evaluates to zero at infinity. Closed
  excision and the singleton overlap detect zero on their union.
  Stage 2: compact-pair exactness gives a relative lift on this union.
  The actual quotient/complement homeomorphisms identify its target with
  the prescribed supported group on X times Y and its collapse pullback.
  Stage 3: stabilize an automorphism on the axes to a finite trivial
  representative. Pull it back along the two axis projections and the
  common basepoint; their ordered composition with a basepoint inverse
  extends that exact representative to the product. Thus automorphism
  restriction is surjective, so exactness makes relative forgetting
  injective. This proves uniqueness for the same collapse lift without
  a suspension comparison or a finite-CW hypothesis. -/
  classical
  -- Use the actual two axes; all split-wedge steps stay inside this proof.
  let T := OnePoint X × OnePoint Y
  let W : Set T := {z | z.1 = ∞ ∨ z.2 = ∞}
  have hW : IsClosed W :=
    (isClosed_eq continuous_fst continuous_const).union
      (isClosed_eq continuous_snd continuous_const)
  let := hW.isClosedEmbedding_subtypeVal.compactSpace
  -- Closed excision detects a class on both axes through their singleton overlap.
  have zeroOfClosedCover {S : Type _} [TopologicalSpace S] [CompactSpace S] [T2Space S]
      (A B : Set S) (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = Set.univ)
      (r : B → {b : B | (b : S) ∈ A}) (hrCont : Continuous r)
      (hr : ∀ c : {b : B | (b : S) ∈ A}, r c = c)
      (u : ComplexKZero S)
      (huA : complexKZeroRestriction A hA u = 0)
      (huB : complexKZeroRestriction B hB u = 0) : u = 0 := by
    let := hB.isClosedEmbedding_subtypeVal.compactSpace
    let C : Set B := {b | (b : S) ∈ A}
    have hC : IsClosed C := hA.preimage continuous_subtype_val
    let FA : RelativeKZero.{_, 0} A hA →+ ComplexKZero S :=
      relativeKZeroForget A hA
    let FC : RelativeKZero.{_, 0} C hC →+ ComplexKZero B :=
      relativeKZeroForget C hC
    let RC : RelativeKZero.{_, 0} A hA →+
        RelativeKZero.{_, 0} C hC :=
      relativeKZeroClosedRestriction A B hA hB
    obtain ⟨z, hz⟩ := (range_relativeKZeroForget.{_, 0} A hA).ge huA
    have hsquare : FC (RC z) = complexKZeroRestriction B hB (FA z) :=
      DFunLike.congr_fun
      (relativeKZeroForget_natural C hC A hA
        ⟨Subtype.val, continuous_subtype_val⟩ (fun _ hx ↦ hx)) z
    change FA z = u at hz
    rw [hz, huB] at hsquare
    have hrestricted : RC z = 0 := by
      have hinj : Function.Injective FC :=
        relativeKZeroForget_injective_of_retraction C hC ⟨r, hrCont⟩ hr
      apply hinj
      simpa only [map_zero] using hsquare
    have hz0 : z = 0 := by
      have hinj : Function.Injective RC :=
        (relativeKZeroClosedRestriction_bijective A B hA hB hcover).1
      apply hinj
      simpa only [map_zero] using hrestricted
    rw [← hz, hz0, map_zero]
  -- The given reduced factors force the same absolute product to vanish on each axis.
  have productRestrictsToZero : complexKZeroRestriction W hW
      (complexKZeroExternalProduct a.val b.val) = 0 := by
    let A : Set W := {w | w.val.2 = ∞}
    let B : Set W := {w | w.val.1 = ∞}
    have hA : IsClosed A :=
      isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
    have hB : IsClosed B :=
      isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
    have hcover : A ∪ B = Set.univ := by
      apply Set.eq_univ_of_forall
      intro w
      exact w.property.elim Or.inr Or.inl
    let c₀ : {w : B | (w : W) ∈ A} := ⟨⟨⟨(∞, ∞), Or.inl rfl⟩, rfl⟩, rfl⟩
    have hr : ∀ c : {w : B | (w : W) ∈ A}, c₀ = c := by
      intro c
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext c.val.property.symm c.property.symm
    have constantZeroX {D : Type _} [TopologicalSpace D] [CompactSpace D] [T2Space D] :
        complexKZeroPullback (ContinuousMap.const D (∞ : OnePoint X)) a.val = 0 := by
      have hconst :
          (ContinuousMap.compRightAlgHom ℂ ℂ
            (ContinuousMap.const D (∞ : OnePoint X))).toRingHom =
            (ContinuousMap.C : ℂ →+* C(D, ℂ)).comp
              (ContinuousMap.evalAlgHom ℂ ℂ (∞ : OnePoint X)).toRingHom := by
        ext f x
        rfl
      change kZeroMap _ a.val = 0
      rw [hconst, kZeroMap_comp, AddMonoidHom.comp_apply]
      rw [show kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ (∞ : OnePoint X)).toRingHom a.val = 0
        from a.property, map_zero]
    have constantZeroY {D : Type _} [TopologicalSpace D] [CompactSpace D] [T2Space D] :
        complexKZeroPullback (ContinuousMap.const D (∞ : OnePoint Y)) b.val = 0 := by
      have hconst :
          (ContinuousMap.compRightAlgHom ℂ ℂ
            (ContinuousMap.const D (∞ : OnePoint Y))).toRingHom =
            (ContinuousMap.C : ℂ →+* C(D, ℂ)).comp
              (ContinuousMap.evalAlgHom ℂ ℂ (∞ : OnePoint Y)).toRingHom := by
        ext f x
        rfl
      change kZeroMap _ b.val = 0
      rw [hconst, kZeroMap_comp, AddMonoidHom.comp_apply]
      rw [show kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ (∞ : OnePoint Y)).toRingHom b.val = 0
        from b.property, map_zero]
    let u := complexKZeroExternalProduct a.val b.val
    have zeroOnAxis {D : Type _} [TopologicalSpace D] [CompactSpace D] [T2Space D]
        (f : C(D, T)) (hf : (∀ d, (f d).1 = ∞) ∨ (∀ d, (f d).2 = ∞)) :
        complexKZeroPullback f u = 0 := by
      change kZeroMap _ (kZeroMul _ _ _) = 0
      rw [kZeroMap_mul]
      change kZeroMul C(D, ℂ)
        (complexKZeroPullback f (complexKZeroPullback ContinuousMap.fst a.val))
        (complexKZeroPullback f (complexKZeroPullback ContinuousMap.snd b.val)) = 0
      rcases hf with hf | hf
      · have hfst : (ContinuousMap.fst : C(T, OnePoint X)).comp f =
            ContinuousMap.const D ∞ := by
          ext d
          exact hf d
        have hzero : complexKZeroPullback f
            (complexKZeroPullback ContinuousMap.fst a.val) = 0 := by
          rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hfst]
          exact constantZeroX (D := D)
        rw [hzero]
        simp only [map_zero, AddMonoidHom.zero_apply]
      · have hsnd : (ContinuousMap.snd : C(T, OnePoint Y)).comp f =
            ContinuousMap.const D ∞ := by
          ext d
          exact hf d
        have hzero : complexKZeroPullback f
            (complexKZeroPullback ContinuousMap.snd b.val) = 0 := by
          rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsnd]
          exact constantZeroY (D := D)
        rw [hzero, map_zero]
    let j : C(W, T) := ⟨Subtype.val, continuous_subtype_val⟩
    let := hA.isClosedEmbedding_subtypeVal.compactSpace
    let := hB.isClosedEmbedding_subtypeVal.compactSpace
    apply zeroOfClosedCover A B hA hB hcover (fun _ ↦ c₀) continuous_const hr
    · change complexKZeroPullback (⟨Subtype.val, continuous_subtype_val⟩ : C(A, W))
        (complexKZeroPullback j u) = 0
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      exact zeroOnAxis _ (Or.inr (fun w ↦ w.property))
    · change complexKZeroPullback (⟨Subtype.val, continuous_subtype_val⟩ : C(B, W))
        (complexKZeroPullback j u) = 0
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      exact zeroOnAxis _ (Or.inl (fun w ↦ w.property))
  -- Identify the actual quotient map with the original finite-pair collapse.
  have smashLiftTransport :
      ∃ L : RelativeKZero.{_, 0} W hW →+ CompactSupportKZero (X × Y),
        Function.Bijective L ∧
          ∀ z, complexKZeroPullback onePointProductCollapseMap (L z).val =
            relativeKZeroForget W hW z := by
    let := hW.isOpen_compl.locallyCompactSpace
    let := PointedQuotient.compactSpace W
    let := PointedQuotient.t2Space W hW
    let i : X × Y → T := fun z ↦ ((z.1 : OnePoint X), (z.2 : OnePoint Y))
    have hi : Topology.IsOpenEmbedding i :=
      OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe
    have hrange : Set.range i = Wᶜ := by
      ext z
      change (∃ xy : X × Y, i xy = z) ↔ ¬(z.1 = ∞ ∨ z.2 = ∞)
      constructor
      · rintro ⟨xy, rfl⟩ hz
        rcases hz with hz | hz
        · exact OnePoint.coe_ne_infty xy.1 hz
        · exact OnePoint.coe_ne_infty xy.2 hz
      · intro hz
        rcases z with ⟨p, q⟩
        cases p using OnePoint.rec with
        | infty => exact (hz (Or.inl rfl)).elim
        | coe x =>
          cases q using OnePoint.rec with
          | infty => exact (hz (Or.inr rfl)).elim
          | coe y => exact ⟨(x, y), rfl⟩
    let e : X × Y ≃ₜ (Wᶜ : Set T) :=
      hi.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
    let d := PointedQuotient.onePointHomeomorph.{_, 0} W hW
    let k : C(OnePoint (X × Y), PointedQuotient.{_, 0} W) :=
      (⟨d.symm, d.symm.continuous⟩ : C(_, _)).comp
        (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap)
    let L : RelativeKZero.{_, 0} W hW →+ CompactSupportKZero (X × Y) :=
      (compactSupportKZeroHomeomorph e.symm).comp (relativeKZeroToCompactSupport W hW)
    have hLbij : Function.Bijective L :=
      (compactSupportKZeroHomeomorph_bijective e.symm).comp
        (relativeKZeroToCompactSupport_bijective W hW)
    have hL (z : RelativeKZero.{_, 0} W hW) :
        (L z).val = complexKZeroPullback k z.val := by
      change complexKZeroPullback (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap)
        (complexKZeroPullback ⟨d.symm, d.symm.continuous⟩ z.val) = _
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hkInfinity : k ∞ = PointedQuotient.basepoint W :=
      PointedQuotient.onePointHomeomorph_symm_infty W hW
    have hkFinite (x : X) (y : Y) :
        k (((x, y) : X × Y) : OnePoint (X × Y)) =
          PointedQuotient.of W ((x : OnePoint X), (y : OnePoint Y)) := by
      change d.symm ((e (x, y) : (Wᶜ : Set T)) : OnePoint (Wᶜ : Set T)) = _
      exact d.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of W hW (e (x, y))).symm
    have hsquare : k.comp ⟨onePointProductCollapse, continuous_onePointProductCollapse⟩ =
        (⟨PointedQuotient.of W, PointedQuotient.continuous_of W⟩ : C(T, _)) := by
      ext z
      rcases z with ⟨p, q⟩
      cases p using OnePoint.rec with
      | infty =>
        change k ∞ = PointedQuotient.of W (∞, q)
        rw [hkInfinity]
        exact ((PointedQuotient.of_eq_basepoint_iff W (∞, q)).mpr (Or.inl rfl)).symm
      | coe x =>
        cases q using OnePoint.rec with
        | infty =>
          change k ∞ = PointedQuotient.of W ((x : OnePoint X), ∞)
          rw [hkInfinity]
          exact ((PointedQuotient.of_eq_basepoint_iff W ((x : OnePoint X), ∞)).mpr
            (Or.inr rfl)).symm
        | coe y => exact hkFinite x y
    refine ⟨L, hLbij, ?_⟩
    intro z
    rw [hL]
    change complexKZeroPullback ⟨onePointProductCollapse, continuous_onePointProductCollapse⟩
        (complexKZeroPullback k z.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
    rfl
  -- An actual finite trivial automorphism on the axes extends to the whole product.
  have restrictionSurjective :
      Function.Surjective (ComplexBundle.bundleKMinusOneRestriction W) := by
    intro a
    obtain ⟨A, hA⟩ := ComplexBundle.bundleAutomorphism_kMinusOneClass_surjective a
    obtain ⟨n, β, hβ⟩ := A.exists_trivial_representative
    let := ComplexBundle.trivialTopology (X := T) n
    let := ComplexBundle.trivialTopology (X := W) n
    let r₁ : C(T, W) := ⟨fun z ↦ ⟨(z.1, ∞), Or.inr rfl⟩,
      (continuous_fst.prodMk continuous_const).subtype_mk _⟩
    let r₂ : C(T, W) := ⟨fun z ↦ ⟨(∞, z.2), Or.inl rfl⟩,
      (continuous_const.prodMk continuous_snd).subtype_mk _⟩
    let r₀ : C(T, W) := ContinuousMap.const T ⟨(∞, ∞), Or.inl rfl⟩
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
    let γ := ((lift r₂).trans (lift r₀).symm).trans (lift r₁)
    have hγ (w : W) (v : Fin n → ℂ) : γ.linearEquiv w.val v = β.linearEquiv w v := by
      change (lift r₁).linearEquiv w.val
        (((lift r₀).linearEquiv w.val).symm ((lift r₂).linearEquiv w.val v)) = _
      rw [hlift, hlift, hlift]
      rcases w.property with hw | hw
      · have hr₁ : r₁ w.val = r₀ w.val := Subtype.ext (Prod.ext hw rfl)
        have hr₂ : r₂ w.val = w := Subtype.ext (Prod.ext hw.symm rfl)
        rw [hr₁, hr₂, LinearEquiv.apply_symm_apply]
      · have hr₂ : r₂ w.val = r₀ w.val := Subtype.ext (Prod.ext rfl hw)
        have hr₁ : r₁ w.val = w := Subtype.ext (Prod.ext rfl hw.symm)
        rw [hr₁, hr₂, LinearEquiv.symm_apply_apply]
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
  -- Independent pair exactness gives both existence and injectivity of this same lift.
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
  obtain ⟨L, hL, hLformula⟩ := smashLiftTransport
  have hzero := productRestrictsToZero
  obtain ⟨z, hz⟩ := (range_relativeKZeroForget.{_, 0} W hW).ge hzero
  refine ⟨L z, (hLformula z).trans hz, ?_⟩
  intro c hc
  obtain ⟨w, rfl⟩ := hL.2 c
  apply congrArg L
  apply hFinj
  exact (hLformula w).symm.trans (hc.trans hz.symm)

/-- The actual unique smash lift is biadditive. -/
theorem existsUnique_compactSupportKZeroExternalProduct :
    ∃! μ : CompactSupportKZero X →+ CompactSupportKZero Y →+ CompactSupportKZero (X × Y),
      ∀ a b, complexKZeroPullback onePointProductCollapseMap (μ a b).val =
        complexKZeroExternalProduct a.val b.val := by
  /- Choose the unique lift for each pair by existsUnique_compactSupportProduct.
  Addition and zero in either input have the same pulled-back absolute classes
  as addition and zero of the lifts. Uniqueness identifies them, giving two
  additive structures and a unique biadditive map with precisely this formula. -/
  classical
  -- Fix the original unique lift for each pair before assembling its two additive structures.
  let μ (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
      CompactSupportKZero (X × Y) := (existsUnique_compactSupportProduct a b).choose
  have hμ (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
      complexKZeroPullback onePointProductCollapseMap (μ a b).val =
        complexKZeroExternalProduct a.val b.val :=
    (existsUnique_compactSupportProduct a b).choose_spec.1
  have hμunique (a : CompactSupportKZero X) (b : CompactSupportKZero Y)
      (c : CompactSupportKZero (X × Y))
      (hc : complexKZeroPullback onePointProductCollapseMap c.val =
        complexKZeroExternalProduct a.val b.val) : c = μ a b :=
    (existsUnique_compactSupportProduct a b).choose_spec.2 c hc
  -- Every zero and sum has the prescribed absolute pullback, so uniqueness identifies it.
  have hzeroLeft (b : CompactSupportKZero Y) : μ 0 b = 0 := by
    symm
    apply hμunique 0 b
    change complexKZeroPullback onePointProductCollapseMap 0 =
      complexKZeroExternalProduct 0 b.val
    simp only [map_zero, AddMonoidHom.zero_apply]
  have hzeroRight (a : CompactSupportKZero X) : μ a 0 = 0 := by
    symm
    apply hμunique a 0
    change complexKZeroPullback onePointProductCollapseMap 0 =
      complexKZeroExternalProduct a.val 0
    simp only [map_zero]
  have haddLeft (a₁ a₂ : CompactSupportKZero X) (b : CompactSupportKZero Y) :
      μ (a₁ + a₂) b = μ a₁ b + μ a₂ b := by
    symm
    apply hμunique (a₁ + a₂) b
    change complexKZeroPullback onePointProductCollapseMap
      ((μ a₁ b).val + (μ a₂ b).val) =
        complexKZeroExternalProduct (a₁.val + a₂.val) b.val
    simp only [map_add, AddMonoidHom.add_apply, hμ]
  have haddRight (a : CompactSupportKZero X) (b₁ b₂ : CompactSupportKZero Y) :
      μ a (b₁ + b₂) = μ a b₁ + μ a b₂ := by
    symm
    apply hμunique a (b₁ + b₂)
    change complexKZeroPullback onePointProductCollapseMap
      ((μ a b₁).val + (μ a b₂).val) =
        complexKZeroExternalProduct a.val (b₁.val + b₂.val)
    simp only [map_add, hμ]
  let M : CompactSupportKZero X →+ CompactSupportKZero Y →+ CompactSupportKZero (X × Y) :=
    { toFun := fun a ↦
        { toFun := μ a
          map_zero' := hzeroRight a
          map_add' := haddRight a }
      map_zero' := by
        apply AddMonoidHom.ext
        intro b
        exact hzeroLeft b
      map_add' := by
        intro a₁ a₂
        apply AddMonoidHom.ext
        intro b
        exact haddLeft a₁ a₂ b }
  -- Pointwise uniqueness compares every other biadditive map on the same two inputs.
  refine ⟨M, hμ, ?_⟩
  intro ν hν
  apply AddMonoidHom.ext
  intro a
  apply AddMonoidHom.ext
  intro b
  exact hμunique a b (ν a b) (hν a b)

/-- The standard compact-support exterior product, determined by its smash pullback. -/
def compactSupportKZeroExternalProduct :
    CompactSupportKZero X →+ CompactSupportKZero Y →+ CompactSupportKZero (X × Y) :=
  Classical.choose (existsUnique_compactSupportKZeroExternalProduct (X := X) (Y := Y)).exists

/-- The compact-support product pulls back to the prescribed absolute product. -/
theorem compactSupportKZeroExternalProduct_pullback (a : CompactSupportKZero X)
    (b : CompactSupportKZero Y) :
    complexKZeroPullback onePointProductCollapseMap
      (compactSupportKZeroExternalProduct a b).val =
        complexKZeroExternalProduct a.val b.val := by
  /- Read the defining characterization of the unique biadditive lift. This is
  the link to the concrete matrix tensor product, rather than an arbitrary
  bilinear operation on the compact-support groups. -/
  exact (Classical.choose_spec
    (existsUnique_compactSupportKZeroExternalProduct (X := X) (Y := Y)).exists) a b

/-- On compact bases, the smash construction agrees with the absolute exterior product. -/
theorem compactSupportKZeroToAbsolute_externalProduct [CompactSpace X] [CompactSpace Y]
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
    compactSupportKZeroToAbsolute (compactSupportKZeroExternalProduct a b) =
      complexKZeroExternalProduct (compactSupportKZeroToAbsolute a)
        (compactSupportKZeroToAbsolute b) := by
  /- Restrict the defining collapse identity to X × Y in X⁺ × Y⁺.
  On finite pairs collapse is the finite-point inclusion. Pullback composition
  and naturality of the absolute external product give the displayed equality. -/
  let iX : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
  let iY : C(Y, OnePoint Y) := ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩
  let iXY : C(X × Y, OnePoint (X × Y)) :=
    ⟨((↑) : X × Y → OnePoint (X × Y)), OnePoint.continuous_coe⟩
  -- The original collapse retains each finite pair with precisely its original coordinates.
  have hsquare : onePointProductCollapseMap.comp (iX.prodMap iY) = iXY := rfl
  have h := congrArg (complexKZeroPullback (iX.prodMap iY))
    (compactSupportKZeroExternalProduct_pullback a b)
  change complexKZeroPullback (iX.prodMap iY)
      (complexKZeroPullback onePointProductCollapseMap
        (compactSupportKZeroExternalProduct a b).val) = _ at h
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare] at h
  -- Finite-point restriction is exactly the existing compact-to-absolute comparison.
  exact h.trans (complexKZeroExternalProduct_natural iX iY a.val b.val)

/-- External product with the specified complex-line exterior class, the complex Bott map.
GeometricBott proves its bijectivity; sphere-generator comparison is treated separately. -/
def bottLineExternalProduct : CompactSupportKZero X →+ CompactSupportKZero (X × ℂ) :=
  compactSupportKZeroExternalProduct.flip bottLineClass

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportFunctoriality
public import AtiyahSinger.Topology.CompactSupportProductNaturality
public import AtiyahSinger.Topology.RelativeKZero

/-!
# External products of relative complex K classes

Public module ID: M2083.

Karoubi II.5.21--5.22 gives the relative external product for closed
compact Hausdorff pairs. Its target pair has subspace A times Y union X times B.
The actual complement is the product of the two original complements. Transport
the existing compact-support product through this coordinate homeomorphism and
the existing relative/complement equivalences; no new K-group carrier is used.

Naturality holds for arbitrary continuous maps of pairs. Such a map need not
restrict to a map of the open complements, let alone a proper map. The proof
therefore uses the induced pointed quotient maps and the reduced smash product.
Forgetting relative data gives the absolute product, but that forgetful map
is not assumed injective. Empty subspaces, full subspaces and empty bases are
included; no CW, cofibration, connectedness or nonemptiness is imposed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- The standard subspace of the external product pair: A times Y union X times B. -/
def relativeProductSubset (A : Set X) (B : Set Y) : Set (X × Y) :=
  Prod.fst ⁻¹' A ∪ Prod.snd ⁻¹' B

/-- The subspace of the product pair is closed when both original subspaces are closed. -/
theorem isClosed_relativeProductSubset (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) : IsClosed (relativeProductSubset A B) := by
  -- Each part is a closed inverse image under one of the two original projections.
  exact (hA.preimage continuous_fst).union (hB.preimage continuous_snd)

/-- The complement of the product subspace retains exactly the two original coordinates. -/
def relativeProductComplementHomeomorph (A : Set X) (B : Set Y) :
    ((relativeProductSubset A B)ᶜ : Set (X × Y)) ≃ₜ (Aᶜ : Set X) × (Bᶜ : Set Y) where
  toFun z :=
    (⟨z.val.1, fun h ↦ z.property (Or.inl h)⟩,
      ⟨z.val.2, fun h ↦ z.property (Or.inr h)⟩)
  invFun z := ⟨(z.1.val, z.2.val), fun h ↦ h.elim z.1.property z.2.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk
      (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- The actual biadditive product, transported from compact supports on the open complements. -/
def relativeKZeroExternalProduct (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) :
    RelativeKZero A hA →+ RelativeKZero B hB →+
      RelativeKZero (relativeProductSubset A B) (isClosed_relativeProductSubset A hA B hB) :=
  letI := hA.isOpen_compl.locallyCompactSpace
  letI := hB.isOpen_compl.locallyCompactSpace
  letI := (isClosed_relativeProductSubset A hA B hB).isOpen_compl.locallyCompactSpace
  let source := relativeKZeroCompactSupportEquiv A hA
  let target := relativeKZeroCompactSupportEquiv B hB
  let product := (relativeKZeroCompactSupportEquiv (relativeProductSubset A B)
    (isClosed_relativeProductSubset A hA B hB)).trans
      (compactSupportKZeroHomeomorphEquiv (relativeProductComplementHomeomorph A B))
  ((compactSupportKZeroExternalProduct.compr₂ product.symm.toAddMonoidHom).compl₂
    target.toAddMonoidHom).comp source.toAddMonoidHom

/-- The relative product becomes precisely the prescribed product of the two complement classes. -/
theorem relativeKZeroExternalProduct_complement (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) (a : RelativeKZero A hA) (b : RelativeKZero B hB) :
    letI := hA.isOpen_compl.locallyCompactSpace
    letI := hB.isOpen_compl.locallyCompactSpace
    letI := (isClosed_relativeProductSubset A hA B hB).isOpen_compl.locallyCompactSpace
    compactSupportKZeroHomeomorphEquiv (relativeProductComplementHomeomorph A B)
        (relativeKZeroCompactSupportEquiv (relativeProductSubset A B)
          (isClosed_relativeProductSubset A hA B hB)
          (relativeKZeroExternalProduct A hA B hB a b)) =
      compactSupportKZeroExternalProduct (relativeKZeroCompactSupportEquiv A hA a)
        (relativeKZeroCompactSupportEquiv B hB b) := by
  /- Unfold the transported product. The target relative/complement comparison
  followed by the displayed coordinate homeomorphism cancels its own inverse.
  The remaining two factors are the original input complement comparisons,
  followed by the existing compact-support smash product. Thus the equality
  concerns the specified actual maps, without choosing a second product. -/
  let := hA.isOpen_compl.locallyCompactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let := (isClosed_relativeProductSubset A hA B hB).isOpen_compl.locallyCompactSpace
  -- Cancel the target comparison for this original transported product.
  let e := (relativeKZeroCompactSupportEquiv (relativeProductSubset A B)
    (isClosed_relativeProductSubset A hA B hB)).trans
      (compactSupportKZeroHomeomorphEquiv (relativeProductComplementHomeomorph A B))
  change e (e.symm (compactSupportKZeroExternalProduct
    (relativeKZeroCompactSupportEquiv A hA a)
    (relativeKZeroCompactSupportEquiv B hB b))) = _
  exact e.apply_symm_apply _

/-- Forgetting relative conditions preserves the absolute external tensor product. -/
theorem relativeKZeroForget_externalProduct (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) (a : RelativeKZero A hA) (b : RelativeKZero B hB) :
    relativeKZeroForget (relativeProductSubset A B) (isClosed_relativeProductSubset A hA B hB)
        (relativeKZeroExternalProduct A hA B hB a b) =
      complexKZeroExternalProduct (relativeKZeroForget A hA a) (relativeKZeroForget B hB b) := by
  /- Stage 1: use the specified complement comparisons eA, eB and eP.
  The transported relative product becomes the compact-support product of
  its two complement classes. Compose the original quotient maps with
  eA and eB to obtain the two collapse maps from X and Y.
  Stage 2: their product collapse, followed by eP inverse, is the actual
  quotient map of the product pair. Check separately whether either
  coordinate lies in its closed subspace, including collapsed images at infinity.
  Stage 3: pull back the compact-support product's defining smash equation
  along these two maps. Absolute external-product naturality and the
  exact inverse-homeomorphism identities identify its factors with the
  original relative forgetful images. No injectivity of forgetting is used. -/
  let := hA.isOpen_compl.locallyCompactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let C := relativeProductSubset A B
  have hC : IsClosed C := isClosed_relativeProductSubset A hA B hB
  let := hC.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.compactSpace A
  let := PointedQuotient.compactSpace B
  let := PointedQuotient.compactSpace C
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space B hB
  let := PointedQuotient.t2Space C hC
  -- Keep the original quotient/complement homeomorphisms and their product coordinates.
  let eA := PointedQuotient.onePointHomeomorph A hA
  let eB := PointedQuotient.onePointHomeomorph B hB
  let eC := PointedQuotient.onePointHomeomorph C hC
  let e := relativeProductComplementHomeomorph A B
  let eP := eC.trans e.onePointCongr
  let qA : C(X, PointedQuotient A) :=
    ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
  let qB : C(Y, PointedQuotient B) :=
    ⟨PointedQuotient.of B, PointedQuotient.continuous_of B⟩
  let qC : C(X × Y, PointedQuotient C) :=
    ⟨PointedQuotient.of C, PointedQuotient.continuous_of C⟩
  let PA : C(X, OnePoint (Aᶜ : Set X)) :=
    (⟨eA, eA.continuous⟩ : C(PointedQuotient A, OnePoint (Aᶜ : Set X))).comp qA
  let PB : C(Y, OnePoint (Bᶜ : Set Y)) :=
    (⟨eB, eB.continuous⟩ : C(PointedQuotient B, OnePoint (Bᶜ : Set Y))).comp qB
  let K : C(OnePoint ((Aᶜ : Set X) × (Bᶜ : Set Y)), PointedQuotient C) :=
    ⟨eP.symm, eP.symm.continuous⟩
  let a₀ := relativeKZeroCompactSupportEquiv A hA a
  let b₀ := relativeKZeroCompactSupportEquiv B hB b
  let r := relativeKZeroExternalProduct A hA B hB a b
  let c₀ := compactSupportKZeroHomeomorphEquiv e
    (relativeKZeroCompactSupportEquiv C hC r)
  have hc₀ : c₀ = compactSupportKZeroExternalProduct a₀ b₀ :=
    relativeKZeroExternalProduct_complement A hA B hB a b
  have hvalue : c₀.val = complexKZeroPullback K r.val := by
    change complexKZeroPullback
        (properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap)
        (complexKZeroPullback ⟨eC.symm, eC.symm.continuous⟩ r.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  -- On finite points these collapses are precisely the original quotient maps.
  have hPAin (x : X) (hx : x ∈ A) : PA x = OnePoint.infty := by
    change eA (PointedQuotient.of A x) = OnePoint.infty
    rw [(PointedQuotient.of_eq_basepoint_iff A x).2 hx]
    exact PointedQuotient.onePointHomeomorph_basepoint A hA
  have hPBin (y : Y) (hy : y ∈ B) : PB y = OnePoint.infty := by
    change eB (PointedQuotient.of B y) = OnePoint.infty
    rw [(PointedQuotient.of_eq_basepoint_iff B y).2 hy]
    exact PointedQuotient.onePointHomeomorph_basepoint B hB
  have hPAout (x : X) (hx : x ∉ A) :
      PA x = ((⟨x, hx⟩ : (Aᶜ : Set X)) : OnePoint (Aᶜ : Set X)) :=
    PointedQuotient.onePointHomeomorph_of A hA ⟨x, hx⟩
  have hPBout (y : Y) (hy : y ∉ B) :
      PB y = ((⟨y, hy⟩ : (Bᶜ : Set Y)) : OnePoint (Bᶜ : Set Y)) :=
    PointedQuotient.onePointHomeomorph_of B hB ⟨y, hy⟩
  have hsquare : K.comp (onePointProductCollapseMap.comp (PA.prodMap PB)) = qC := by
    ext z
    rcases z with ⟨x, y⟩
    change eP.symm (onePointProductCollapse (PA x, PB y)) = PointedQuotient.of C (x, y)
    apply eP.injective
    rw [eP.apply_symm_apply]
    by_cases hx : x ∈ A
    · rw [hPAin x hx]
      have hz : (x, y) ∈ C := Or.inl hx
      rw [(PointedQuotient.of_eq_basepoint_iff C (x, y)).2 hz]
      change OnePoint.infty = OnePoint.map e (eC (PointedQuotient.basepoint C))
      rw [PointedQuotient.onePointHomeomorph_basepoint C hC]
      rfl
    · by_cases hy : y ∈ B
      · rw [hPBin y hy]
        have hz : (x, y) ∈ C := Or.inr hy
        rw [(PointedQuotient.of_eq_basepoint_iff C (x, y)).2 hz]
        change onePointProductCollapse (PA x, OnePoint.infty) =
          OnePoint.map e (eC (PointedQuotient.basepoint C))
        rw [PointedQuotient.onePointHomeomorph_basepoint C hC]
        cases PA x using OnePoint.rec <;> rfl
      · rw [hPAout x hx, hPBout y hy]
        let z : (Cᶜ : Set (X × Y)) := ⟨(x, y), fun h ↦ h.elim hx hy⟩
        let w : (Aᶜ : Set X) × (Bᶜ : Set Y) := (⟨x, hx⟩, ⟨y, hy⟩)
        change (w : OnePoint ((Aᶜ : Set X) × (Bᶜ : Set Y))) =
          OnePoint.map e (eC (PointedQuotient.of C z.val))
        rw [PointedQuotient.onePointHomeomorph_of C hC z, OnePoint.map_some]
        rfl
  -- Pullback composition cancels the exact homeomorphisms, with no forgetful injectivity.
  have hAvalue : complexKZeroPullback PA a₀.val = relativeKZeroForget A hA a := by
    change complexKZeroPullback PA
        (complexKZeroPullback ⟨eA.symm, eA.symm.continuous⟩ a.val) =
      complexKZeroPullback qA a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hmap : (⟨eA.symm, eA.symm.continuous⟩ :
        C(OnePoint (Aᶜ : Set X), PointedQuotient A)).comp PA = qA := by
      ext x
      exact eA.symm_apply_apply _
    rw [hmap]
  have hBvalue : complexKZeroPullback PB b₀.val = relativeKZeroForget B hB b := by
    change complexKZeroPullback PB
        (complexKZeroPullback ⟨eB.symm, eB.symm.continuous⟩ b.val) =
      complexKZeroPullback qB b.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hmap : (⟨eB.symm, eB.symm.continuous⟩ :
        C(OnePoint (Bᶜ : Set Y), PointedQuotient B)).comp PB = qB := by
      ext y
      exact eB.symm_apply_apply _
    rw [hmap]
  have hproduct : complexKZeroPullback onePointProductCollapseMap
      (complexKZeroPullback K r.val) = complexKZeroExternalProduct a₀.val b₀.val := by
    rw [← hvalue, hc₀]
    exact compactSupportKZeroExternalProduct_pullback a₀ b₀
  have h := congrArg (complexKZeroPullback (PA.prodMap PB)) hproduct
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
    complexKZeroExternalProduct_natural, hAvalue, hBvalue] at h
  exact h

variable [CompactSpace X'] [T2Space X'] [CompactSpace Y'] [T2Space Y']

/-- Relative external products are natural for arbitrary continuous maps of closed pairs. -/
theorem relativeKZeroExternalProduct_natural
    (A : Set X) (hA : IsClosed A) (B : Set Y) (hB : IsClosed B)
    (A' : Set X') (hA' : IsClosed A') (B' : Set Y') (hB' : IsClosed B')
    (f : C(X, X')) (g : C(Y, Y')) (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (a : RelativeKZero A' hA') (b : RelativeKZero B' hB') :
    relativeKZeroPullback (relativeProductSubset A B) (isClosed_relativeProductSubset A hA B hB)
        (relativeProductSubset A' B') (isClosed_relativeProductSubset A' hA' B' hB')
        (f.prodMap g)
        (by
          intro z hz
          exact hz.elim (fun h ↦ Or.inl (hf h)) (fun h ↦ Or.inr (hg h)))
        (relativeKZeroExternalProduct A' hA' B' hB' a b) =
      relativeKZeroExternalProduct A hA B hB
        (relativeKZeroPullback A hA A' hA' f hf a)
        (relativeKZeroPullback B hB B' hB' g hg b) := by
  /- Stage 1: f and g induce actual basepoint-preserving maps on X/A and Y/B.
  Their smash product agrees with the pointed quotient map induced by f times g
  after identifying the product-pair quotient with the smash. This identity
  includes points outside A whose images enter A', and the analogous B case:
  these points are sent to the distinguished quotient point, not to a nonexistent
  restricted complement map.
  Stage 2: the prescribed relative product is the reduced smash product by
  the complement comparison. Absolute external-product naturality for the
  pointed maps and uniqueness of the reduced smash lift identify its pullbacks.
  This does not assert properness of complement restrictions and does not infer
  equality merely from equality after relativeKZeroForget. -/
  classical
  let := hA.isOpen_compl.locallyCompactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let := hA'.isOpen_compl.locallyCompactSpace
  let := hB'.isOpen_compl.locallyCompactSpace
  let C := relativeProductSubset A B
  let C' := relativeProductSubset A' B'
  have hC : IsClosed C := isClosed_relativeProductSubset A hA B hB
  have hC' : IsClosed C' := isClosed_relativeProductSubset A' hA' B' hB'
  let := hC.isOpen_compl.locallyCompactSpace
  let := hC'.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.compactSpace A
  let := PointedQuotient.compactSpace B
  let := PointedQuotient.compactSpace C
  let := PointedQuotient.compactSpace A'
  let := PointedQuotient.compactSpace B'
  let := PointedQuotient.compactSpace C'
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space B hB
  let := PointedQuotient.t2Space C hC
  let := PointedQuotient.t2Space A' hA'
  let := PointedQuotient.t2Space B' hB'
  let := PointedQuotient.t2Space C' hC'
  -- Express the original pair maps on the same pointed compactifications.
  let eA := PointedQuotient.onePointHomeomorph A hA
  let eB := PointedQuotient.onePointHomeomorph B hB
  let eA' := PointedQuotient.onePointHomeomorph A' hA'
  let eB' := PointedQuotient.onePointHomeomorph B' hB'
  let eC := PointedQuotient.onePointHomeomorph C hC
  let eC' := PointedQuotient.onePointHomeomorph C' hC'
  let e := relativeProductComplementHomeomorph A B
  let e' := relativeProductComplementHomeomorph A' B'
  let eP := eC.trans e.onePointCongr
  let eP' := eC'.trans e'.onePointCongr
  have hfg : Set.MapsTo (f.prodMap g) C C' := by
    intro z hz
    exact hz.elim (fun hx ↦ Or.inl (hf hx)) (fun hy ↦ Or.inr (hg hy))
  let Qf := PointedQuotient.mapContinuous A A' f hf
  let Qg := PointedQuotient.mapContinuous B B' g hg
  let Qfg := PointedQuotient.mapContinuous C C' (f.prodMap g) hfg
  let IA : C(OnePoint (Aᶜ : Set X), PointedQuotient A) :=
    ⟨eA.symm, eA.symm.continuous⟩
  let IB : C(OnePoint (Bᶜ : Set Y), PointedQuotient B) :=
    ⟨eB.symm, eB.symm.continuous⟩
  let IA' : C(OnePoint (A'ᶜ : Set X'), PointedQuotient A') :=
    ⟨eA'.symm, eA'.symm.continuous⟩
  let IB' : C(OnePoint (B'ᶜ : Set Y'), PointedQuotient B') :=
    ⟨eB'.symm, eB'.symm.continuous⟩
  let K : C(OnePoint ((Aᶜ : Set X) × (Bᶜ : Set Y)), PointedQuotient C) :=
    ⟨eP.symm, eP.symm.continuous⟩
  let K' : C(OnePoint ((A'ᶜ : Set X') × (B'ᶜ : Set Y')), PointedQuotient C') :=
    ⟨eP'.symm, eP'.symm.continuous⟩
  let F := (⟨eA', eA'.continuous⟩ :
    C(PointedQuotient A', OnePoint (A'ᶜ : Set X'))).comp (Qf.comp IA)
  let G := (⟨eB', eB'.continuous⟩ :
    C(PointedQuotient B', OnePoint (B'ᶜ : Set Y'))).comp (Qg.comp IB)
  let H := (⟨eP', eP'.continuous⟩ :
    C(PointedQuotient C', OnePoint ((A'ᶜ : Set X') × (B'ᶜ : Set Y')))).comp
      (Qfg.comp K)
  have hFbase : F OnePoint.infty = OnePoint.infty := by
    change eA' (PointedQuotient.map A A' f hf (eA.symm OnePoint.infty)) = _
    rw [PointedQuotient.onePointHomeomorph_symm_infty,
      PointedQuotient.map_basepoint, PointedQuotient.onePointHomeomorph_basepoint]
  have hGbase : G OnePoint.infty = OnePoint.infty := by
    change eB' (PointedQuotient.map B B' g hg (eB.symm OnePoint.infty)) = _
    rw [PointedQuotient.onePointHomeomorph_symm_infty,
      PointedQuotient.map_basepoint, PointedQuotient.onePointHomeomorph_basepoint]
  have hPbase : eP.symm OnePoint.infty = PointedQuotient.basepoint C := by
    apply eP.symm_apply_eq.mpr
    change OnePoint.infty = OnePoint.map e (eC (PointedQuotient.basepoint C))
    rw [PointedQuotient.onePointHomeomorph_basepoint]
    rfl
  have hHbase : H OnePoint.infty = OnePoint.infty := by
    change eP' (PointedQuotient.map C C' (f.prodMap g) hfg
      (eP.symm OnePoint.infty)) = _
    rw [hPbase, PointedQuotient.map_basepoint]
    change OnePoint.map e' (eC' (PointedQuotient.basepoint C')) = OnePoint.infty
    rw [PointedQuotient.onePointHomeomorph_basepoint]
    rfl
  have hAfinite (x : (Aᶜ : Set X)) :
      eA.symm (x : OnePoint (Aᶜ : Set X)) = PointedQuotient.of A x :=
    eA.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of A hA x).symm
  have hBfinite (y : (Bᶜ : Set Y)) :
      eB.symm (y : OnePoint (Bᶜ : Set Y)) = PointedQuotient.of B y :=
    eB.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of B hB y).symm
  have hPfinite (z : (Aᶜ : Set X) × (Bᶜ : Set Y)) :
      eP.symm (z : OnePoint ((Aᶜ : Set X) × (Bᶜ : Set Y))) =
        PointedQuotient.of C (z.1.val, z.2.val) := by
    apply eP.symm_apply_eq.mpr
    let w : (Cᶜ : Set (X × Y)) :=
      ⟨(z.1.val, z.2.val), fun h ↦ h.elim z.1.property z.2.property⟩
    change (z : OnePoint ((Aᶜ : Set X) × (Bᶜ : Set Y))) =
      OnePoint.map e (eC (PointedQuotient.of C w.val))
    rw [PointedQuotient.onePointHomeomorph_of C hC w, OnePoint.map_some]
    rfl
  -- The target quotient formula includes images which enter either closed subset.
  have hcollapse (x : X') (y : Y') :
      onePointProductCollapse
          (eA' (PointedQuotient.of A' x), eB' (PointedQuotient.of B' y)) =
        eP' (PointedQuotient.of C' (x, y)) := by
    by_cases hx : x ∈ A'
    · rw [(PointedQuotient.of_eq_basepoint_iff A' x).2 hx,
        PointedQuotient.onePointHomeomorph_basepoint]
      have hz : (x, y) ∈ C' := Or.inl hx
      rw [(PointedQuotient.of_eq_basepoint_iff C' (x, y)).2 hz]
      change OnePoint.infty = OnePoint.map e' (eC' (PointedQuotient.basepoint C'))
      rw [PointedQuotient.onePointHomeomorph_basepoint]
      rfl
    · by_cases hy : y ∈ B'
      · rw [(PointedQuotient.of_eq_basepoint_iff B' y).2 hy,
          PointedQuotient.onePointHomeomorph_basepoint]
        have hz : (x, y) ∈ C' := Or.inr hy
        rw [(PointedQuotient.of_eq_basepoint_iff C' (x, y)).2 hz]
        change onePointProductCollapse (eA' (PointedQuotient.of A' x), OnePoint.infty) =
          OnePoint.map e' (eC' (PointedQuotient.basepoint C'))
        rw [PointedQuotient.onePointHomeomorph_basepoint]
        cases eA' (PointedQuotient.of A' x) using OnePoint.rec <;> rfl
      · rw [PointedQuotient.onePointHomeomorph_of A' hA' ⟨x, hx⟩,
          PointedQuotient.onePointHomeomorph_of B' hB' ⟨y, hy⟩]
        let z : (C'ᶜ : Set (X' × Y')) := ⟨(x, y), fun h ↦ h.elim hx hy⟩
        let w : (A'ᶜ : Set X') × (B'ᶜ : Set Y') := (⟨x, hx⟩, ⟨y, hy⟩)
        change (w : OnePoint ((A'ᶜ : Set X') × (B'ᶜ : Set Y'))) =
          OnePoint.map e' (eC' (PointedQuotient.of C' z.val))
        rw [PointedQuotient.onePointHomeomorph_of C' hC' z, OnePoint.map_some]
        rfl
  have hsquare :
      (onePointProductCollapseMap (X := (A'ᶜ : Set X')) (Y := (B'ᶜ : Set Y'))).comp
          (F.prodMap G) =
        H.comp (onePointProductCollapseMap (X := (Aᶜ : Set X)) (Y := (Bᶜ : Set Y))) := by
    ext z
    rcases z with ⟨x, y⟩
    cases x using OnePoint.rec with
    | infty =>
      change onePointProductCollapse (F OnePoint.infty, G y) = H OnePoint.infty
      rw [hFbase, hHbase]
      rfl
    | coe x =>
      cases y using OnePoint.rec with
      | infty =>
        change onePointProductCollapse (F x, G OnePoint.infty) = H OnePoint.infty
        rw [hGbase, hHbase]
        cases F x using OnePoint.rec <;> rfl
      | coe y =>
        change onePointProductCollapse (eA' (Qf (eA.symm x)), eB' (Qg (eB.symm y))) =
          eP' (Qfg (eP.symm ((x, y) : OnePoint ((Aᶜ : Set X) × (Bᶜ : Set Y)))))
        rw [hAfinite, hBfinite, hPfinite]
        exact hcollapse (f x.val) (g y.val)
  -- Transported pullbacks use these exact maps, not hypothetical complement restrictions.
  let T := (relativeKZeroCompactSupportEquiv C hC).trans
    (compactSupportKZeroHomeomorphEquiv e)
  let T' := (relativeKZeroCompactSupportEquiv C' hC').trans
    (compactSupportKZeroHomeomorphEquiv e')
  let a₀ := relativeKZeroCompactSupportEquiv A' hA' a
  let b₀ := relativeKZeroCompactSupportEquiv B' hB' b
  let a₁ := relativeKZeroCompactSupportEquiv A hA (relativeKZeroPullback A hA A' hA' f hf a)
  let b₁ := relativeKZeroCompactSupportEquiv B hB (relativeKZeroPullback B hB B' hB' g hg b)
  let r := relativeKZeroExternalProduct A' hA' B' hB' a b
  let c₀ := T' r
  let c₁ := T (relativeKZeroPullback C hC C' hC' (f.prodMap g) hfg r)
  have hAvalue : a₁.val = complexKZeroPullback F a₀.val := by
    change complexKZeroPullback IA (complexKZeroPullback Qf a.val) =
      complexKZeroPullback F (complexKZeroPullback IA' a.val)
    have hmap : Qf.comp IA = IA'.comp F := by
      ext z
      exact (eA'.symm_apply_apply _).symm
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  have hBvalue : b₁.val = complexKZeroPullback G b₀.val := by
    change complexKZeroPullback IB (complexKZeroPullback Qg b.val) =
      complexKZeroPullback G (complexKZeroPullback IB' b.val)
    have hmap : Qg.comp IB = IB'.comp G := by
      ext z
      exact (eB'.symm_apply_apply _).symm
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  have hT (s : RelativeKZero C hC) : (T s).val = complexKZeroPullback K s.val := by
    change complexKZeroPullback
        (properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap)
        (complexKZeroPullback ⟨eC.symm, eC.symm.continuous⟩ s.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hT' (s : RelativeKZero C' hC') : (T' s).val = complexKZeroPullback K' s.val := by
    change complexKZeroPullback
        (properOnePointMap ⟨e'.symm, e'.symm.continuous⟩ e'.symm.isProperMap)
        (complexKZeroPullback ⟨eC'.symm, eC'.symm.continuous⟩ s.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hCvalue : c₁.val = complexKZeroPullback H c₀.val := by
    rw [show c₁ = T (relativeKZeroPullback C hC C' hC' (f.prodMap g) hfg r) from rfl,
      hT, show c₀ = T' r from rfl, hT']
    change complexKZeroPullback K (complexKZeroPullback Qfg r.val) =
      complexKZeroPullback H (complexKZeroPullback K' r.val)
    have hmap : Qfg.comp K = K'.comp H := by
      ext z
      exact (eP'.symm_apply_apply _).symm
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  -- Absolute naturality and the actual commuting smash square identify the unique lift.
  have hc₀ : c₀ = compactSupportKZeroExternalProduct a₀ b₀ :=
    relativeKZeroExternalProduct_complement A' hA' B' hB' a b
  have horiginal : complexKZeroPullback onePointProductCollapseMap c₀.val =
      complexKZeroExternalProduct a₀.val b₀.val := by
    rw [hc₀]
    exact compactSupportKZeroExternalProduct_pullback a₀ b₀
  have hproduct := congrArg (complexKZeroPullback (F.prodMap G)) horiginal
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
    complexKZeroPullback_comp, AddMonoidHom.comp_apply,
    complexKZeroExternalProduct_natural, ← hCvalue, ← hAvalue, ← hBvalue] at hproduct
  have hc₁ : c₁ = compactSupportKZeroExternalProduct a₁ b₁ :=
    (existsUnique_compactSupportProduct a₁ b₁).unique hproduct
      (compactSupportKZeroExternalProduct_pullback a₁ b₁)
  have hright : T (relativeKZeroExternalProduct A hA B hB
      (relativeKZeroPullback A hA A' hA' f hf a)
      (relativeKZeroPullback B hB B' hB' g hg b)) =
        compactSupportKZeroExternalProduct a₁ b₁ :=
    relativeKZeroExternalProduct_complement A hA B hB _ _
  exact T.injective (hc₁.trans hright.symm)

end AtiyahSinger

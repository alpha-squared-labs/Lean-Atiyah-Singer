/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKMinusOneExactness
public import AtiyahSinger.Topology.CompactSupportBundleKMinusOne
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The compactified automorphism boundary for a locally compact closed pair

Public module ID: M1676.

Karoubi II.4.6--4.7 passes the compact-pair sequence of II.3.23 to infinity
evaluation kernels. For a closed subset A of a locally compact Hausdorff X,
the actual proper inclusion extends to A⁺ → X⁺. Its closed image contains
the same infinity as X⁺, and the complement is the original X minus A.

The boundary below restricts the original positive automorphism boundary on
that compact pair. Its subsequent coordinate changes are the specified image
and complement homeomorphisms, not arbitrary isomorphisms of K groups. Exactness
uses the splitting by constant pullback at infinity; it does not require the
automorphism K group of a point to vanish. No real-suspension comparison or
later suspended exact sequence is used. The closed-image and complement geometry,
supported exactness and proper naturality statements are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open OnePoint Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The image of the actual extended inclusion, containing the original infinity. -/
def compactifiedClosedImage (A : Set X) : Set (OnePoint X) :=
  Set.range (OnePoint.map (Subtype.val : A → X))

variable [hLX : LocallyCompactSpace X] [hTX : T2Space X]

/-- A closed inclusion extends by the same point at infinity to a continuous map. -/
def compactifiedClosedInclusion (A : Set X) (hA : IsClosed A) :
    C(OnePoint A, OnePoint X) :=
  letI := hA.locallyCompactSpace
  properOnePointMap ⟨Subtype.val, continuous_subtype_val⟩
    hA.isClosedEmbedding_subtypeVal.isProperMap

include hLX hTX in
/-- Topological certificates for the actual closed image and its original open complement.
These properties supply the image and complement coordinate homeomorphisms. -/
theorem compactifiedClosedInclusion_geometry (A : Set X) (hA : IsClosed A) :
    IsClosedEmbedding (compactifiedClosedInclusion A hA) ∧
      IsOpenEmbedding (fun x : (Aᶜ : Set X) ↦ (x.val : OnePoint X)) ∧
      Set.range (fun x : (Aᶜ : Set X) ↦ (x.val : OnePoint X)) =
        (compactifiedClosedImage A)ᶜ := by
  -- Properness supplies continuity at the original infinity; injectivity is pointwise.
  let := hA.locallyCompactSpace
  have hinj : Function.Injective (compactifiedClosedInclusion A hA) := by
    intro p q hpq
    induction p using OnePoint.rec with
    | infty =>
      induction q using OnePoint.rec with
      | infty => rfl
      | coe q => exact (OnePoint.coe_ne_infty q.val hpq.symm).elim
    | coe p =>
      induction q using OnePoint.rec with
      | infty => exact (OnePoint.coe_ne_infty p.val hpq).elim
      | coe q =>
        exact congrArg (fun x : A ↦ (x : OnePoint A))
          (Subtype.ext (OnePoint.coe_injective hpq))
  have hclosed : IsClosedEmbedding (compactifiedClosedInclusion A hA) :=
    (compactifiedClosedInclusion A hA).continuous.isClosedEmbedding hinj
  -- The finite complement uses the open subtype inclusion followed by X → X⁺.
  have hopen : IsOpenEmbedding (fun x : (Aᶜ : Set X) ↦ (x.val : OnePoint X)) :=
    OnePoint.isOpenEmbedding_coe.comp hA.isOpen_compl.isOpenEmbedding_subtypeVal
  refine ⟨hclosed, hopen, ?_⟩
  -- Infinity is in the closed image; a finite point is in it precisely when it lies in A.
  ext p
  induction p using OnePoint.rec with
  | infty =>
    constructor
    · rintro ⟨x, hx⟩
      exact (OnePoint.coe_ne_infty x.val hx).elim
    · intro hp
      exact (hp ⟨∞, rfl⟩).elim
  | coe x =>
    constructor
    · rintro ⟨y, hy⟩ ⟨z, hz⟩
      have hyx : y.val = x := OnePoint.coe_injective hy
      induction z using OnePoint.rec with
      | infty => exact (OnePoint.coe_ne_infty x hz.symm).elim
      | coe z =>
        have hzx : z.val = x := OnePoint.coe_injective hz
        exact y.property (hyx.trans hzx.symm ▸ z.property)
    · intro hx
      have hxA : x ∉ A := by
        intro hmem
        exact hx ⟨(⟨x, hmem⟩ : A), rfl⟩
      exact ⟨⟨x, hxA⟩, rfl⟩

/-- Identify A⁺ with its actual closed image under the extended inclusion. -/
def compactifiedClosedImageHomeomorph (A : Set X) (hA : IsClosed A) :
    OnePoint A ≃ₜ compactifiedClosedImage A :=
  (compactifiedClosedInclusion_geometry A hA).1.isEmbedding.toHomeomorph

/-- The complement coordinate change retains each original point of X minus A. -/
def compactifiedClosedComplementHomeomorph (A : Set X) (hA : IsClosed A) :
    ((compactifiedClosedImage A)ᶜ : Set (OnePoint X)) ≃ₜ (Aᶜ : Set X) :=
  ((compactifiedClosedInclusion_geometry A hA).2.1.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (compactifiedClosedInclusion_geometry A hA).2.2)).symm

/-- Restrict supported automorphism classes along the actual proper closed inclusion. -/
def compactSupportBundleKMinusOneClosedRestriction (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    CompactSupportBundleKMinusOne X →+ CompactSupportBundleKMinusOne A :=
  letI := hA.locallyCompactSpace
  compactSupportBundleKMinusOnePullback ⟨Subtype.val, continuous_subtype_val⟩
    hA.isClosedEmbedding_subtypeVal.isProperMap

/-- KA II.4.7: the original positive compact-pair boundary on the infinity kernels. -/
def compactSupportBundleKMinusOneBoundary (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    CompactSupportBundleKMinusOne A →+ CompactSupportKZero (Aᶜ : Set X) :=
  letI := hA.locallyCompactSpace
  letI := hA.isOpen_compl.locallyCompactSpace
  let B := compactifiedClosedImage A
  let hB : IsClosed B := (compactifiedClosedInclusion_geometry A hA).1.isClosed_range
  letI := hB.isClosedEmbedding_subtypeVal.compactSpace
  letI := hB.isOpen_compl.locallyCompactSpace
  let e := compactifiedClosedImageHomeomorph A hA
  let toBoundary : CompactSupportBundleKMinusOne A →+ BundleKMinusOne B :=
    (bundleKMinusOnePullback ⟨e.symm, e.symm.continuous⟩).comp
      (reducedBundleKMinusOne (∞ : OnePoint A)).subtype
  let δ : BundleKMinusOne B →+ RelativeKZero.{_, 0} B hB :=
    bundleKMinusOneBoundary B hB
  (compactSupportKZeroHomeomorph (compactifiedClosedComplementHomeomorph A hA)).comp
    ((relativeKZeroToCompactSupport B hB).comp (δ.comp toBoundary))

/-- KA II.4.7: the kernel of the supported boundary is the image of closed restriction. -/
theorem range_compactSupportBundleKMinusOneClosedRestriction
    (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    (compactSupportBundleKMinusOneClosedRestriction A hA).range =
      (compactSupportBundleKMinusOneBoundary A hA).ker := by
  /- Stage 1: use the actual inclusion A⁺ → X⁺ and its image B to identify the
  compact-pair restriction and boundary with the maps in the declaration.
  The image and complement changes are bijective, with the same infinity point.
  Stage 2: apply range_bundleKMinusOneRestriction to the compact closed pair
  (X⁺,B). An ordinary preimage of a reduced kernel element automatically evaluates
  to zero at infinity, since its restriction has zero evaluation there.
  Therefore this preimage lies in the original supported subgroup. The converse
  inclusion follows from ordinary exactness and the same commuting evaluation square. -/
  classical
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let B := compactifiedClosedImage A
  let hB : IsClosed B := (compactifiedClosedInclusion_geometry A hA).1.isClosed_range
  let := hB.isClosedEmbedding_subtypeVal.compactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let e := compactifiedClosedImageHomeomorph A hA
  let i := compactifiedClosedInclusion A hA
  let j : C(B, OnePoint X) := ⟨Subtype.val, continuous_subtype_val⟩
  let ep : C(OnePoint A, B) := ⟨e, e.continuous⟩
  let es : C(B, OnePoint A) := ⟨e.symm, e.symm.continuous⟩
  let J := bundleKMinusOnePullback es
  let T := (compactSupportKZeroHomeomorph
    (compactifiedClosedComplementHomeomorph A hA)).comp
      (relativeKZeroToCompactSupport B hB)
  -- The coordinate changes are the specified homeomorphisms, hence injective on classes.
  have hJleft (w : BundleKMinusOne (OnePoint A)) :
      bundleKMinusOnePullback ep (J w) = w := by
    have hid : es.comp ep = ContinuousMap.id (OnePoint A) := by
      ext p
      exact e.symm_apply_apply p
    change bundleKMinusOnePullback ep (bundleKMinusOnePullback es w) = w
    rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hid,
      bundleKMinusOnePullback_id]
    rfl
  have hJinj : Function.Injective J := Function.LeftInverse.injective hJleft
  have hTinj : Function.Injective T :=
    (compactSupportKZeroHomeomorph_bijective
      (compactifiedClosedComplementHomeomorph A hA)).1.comp
        (relativeKZeroToCompactSupport_bijective B hB).1
  have hi : i.comp es = j := by
    ext p
    change (e (e.symm p)).val = p.val
    exact congrArg Subtype.val (e.apply_symm_apply p)
  have hrestriction (w : BundleKMinusOne (OnePoint X)) :
      J (bundleKMinusOnePullback i w) = bundleKMinusOneRestriction B w := by
    change bundleKMinusOnePullback es (bundleKMinusOnePullback i w) =
      bundleKMinusOnePullback j w
    rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hi]
  apply le_antisymm
  · rintro a ⟨w, rfl⟩
    -- Restriction is killed by the original compact-pair boundary before transport.
    have hzero : bundleKMinusOneBoundary B hB (bundleKMinusOneRestriction B w.val) = 0 :=
      (range_bundleKMinusOneRestriction B hB).le ⟨w.val, rfl⟩
    change T (bundleKMinusOneBoundary B hB (J (bundleKMinusOnePullback i w.val))) = 0
    rw [hrestriction, hzero, map_zero]
  · intro a ha
    change T (bundleKMinusOneBoundary B hB (J a.val)) = 0 at ha
    have hzero : bundleKMinusOneBoundary B hB (J a.val) = 0 :=
      hTinj (ha.trans (map_zero T).symm)
    obtain ⟨w, hw⟩ := (range_bundleKMinusOneRestriction B hB).ge hzero
    have hwa : bundleKMinusOnePullback i w = a.val :=
      hJinj ((hrestriction w).trans hw)
    -- The same infinity belongs to the closed image, so this preimage is already reduced.
    let cA : C(PUnit.{1}, OnePoint A) := ContinuousMap.const PUnit.{1} ∞
    let cX : C(PUnit.{1}, OnePoint X) := ContinuousMap.const PUnit.{1} ∞
    have hpoint : i.comp cA = cX := rfl
    have hwred : w ∈ reducedBundleKMinusOne (∞ : OnePoint X) := by
      change bundleKMinusOnePullback cX w = 0
      calc
        bundleKMinusOnePullback cX w =
            bundleKMinusOnePullback cA (bundleKMinusOnePullback i w) := by
          rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hpoint]
        _ = bundleKMinusOnePullback cA a.val := by rw [hwa]
        _ = 0 := a.property
    refine ⟨⟨w, hwred⟩, ?_⟩
    exact Subtype.ext hwa

/-- KA II.4.7: the supported boundary fills the kernel of extension from the open complement. -/
theorem range_compactSupportBundleKMinusOneBoundary (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    (compactSupportBundleKMinusOneBoundary A hA).range =
      (compactSupportKZeroOpenExtension (Aᶜ : Set X) hA.isOpen_compl).ker := by
  /- Stage 1: relativeKZeroToCompactSupport_extension identifies the ordinary
  relative forgetting map with open extension, after the actual complement
  homeomorphism. On X⁺ the compact-support-to-absolute comparison is actual
  restriction. Both composites keep each finite point of X minus A and collapse
  precisely B, including the same original infinity.
  Stage 2: range_bundleKMinusOneBoundary supplies an ordinary automorphism
  preimage on B of a class killed by this extension. Subtract the restriction
  of the constant class on X⁺ whose value is its evaluation at infinity.
  This correction lies in the kernel of the ordinary boundary and makes the
  chosen preimage reduced. It uses the constant-pullback splitting, not vanishing
  of the automorphism K group of a point. Transport back by the same image map. -/
  classical
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let B := compactifiedClosedImage A
  let hB : IsClosed B := (compactifiedClosedInclusion_geometry A hA).1.isClosed_range
  let := hB.isClosedEmbedding_subtypeVal.compactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.t2Space B hB
  let e := compactifiedClosedImageHomeomorph A hA
  let ec := compactifiedClosedComplementHomeomorph A hA
  let ep : C(OnePoint A, B) := ⟨e, e.continuous⟩
  let es : C(B, OnePoint A) := ⟨e.symm, e.symm.continuous⟩
  let J := bundleKMinusOnePullback es
  let T := (compactSupportKZeroHomeomorph ec).comp (relativeKZeroToCompactSupport B hB)
  have hTbij : Function.Bijective T :=
    (compactSupportKZeroHomeomorph_bijective ec).comp
      (relativeKZeroToCompactSupport_bijective B hB)
  have hJright (w : BundleKMinusOne B) : J (bundleKMinusOnePullback ep w) = w := by
    have hid : ep.comp es = ContinuousMap.id B := by
      apply ContinuousMap.ext
      intro p
      exact e.apply_symm_apply p
    change bundleKMinusOnePullback es (bundleKMinusOnePullback ep w) = w
    rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hid,
      bundleKMinusOnePullback_id]
    rfl
  -- The original complement comparison sends each finite point to its quotient class.
  let q := PointedQuotient.onePointHomeomorph B hB
  let H := properOnePointMap ⟨ec.symm, ec.symm.continuous⟩ ec.symm.isProperMap
  let k : C(OnePoint (Aᶜ : Set X), PointedQuotient B) :=
    (⟨q.symm, q.symm.continuous⟩ : C(_, _)).comp H
  let c : C(OnePoint X, OnePoint (Aᶜ : Set X)) :=
    ⟨onePointCollapse Aᶜ, continuous_onePointCollapse Aᶜ hA.isOpen_compl⟩
  let Q : C(OnePoint X, PointedQuotient B) :=
    ⟨PointedQuotient.of B, PointedQuotient.continuous_of B⟩
  have hkinfty : k ∞ = PointedQuotient.basepoint B :=
    PointedQuotient.onePointHomeomorph_symm_infty B hB
  have hkfinite (p : (Aᶜ : Set X)) :
      k (p : OnePoint (Aᶜ : Set X)) = PointedQuotient.of B (p.val : OnePoint X) := by
    have hec : (ec.symm p).val = (p.val : OnePoint X) := rfl
    change q.symm ((ec.symm p : (Bᶜ : Set (OnePoint X))) :
      OnePoint (Bᶜ : Set (OnePoint X))) = _
    calc
      _ = PointedQuotient.of B (ec.symm p).val :=
        q.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of B hB (ec.symm p)).symm
      _ = PointedQuotient.of B (p.val : OnePoint X) := by rw [hec]
  have hsquare : k.comp c = Q := by
    ext p
    cases p using OnePoint.rec with
    | infty =>
      exact hkinfty.trans
        ((PointedQuotient.of_eq_basepoint_iff B ∞).2 ⟨∞, rfl⟩).symm
    | coe x =>
      change k (onePointCollapse Aᶜ (x : OnePoint X)) = PointedQuotient.of B (x : OnePoint X)
      by_cases hx : x ∈ A
      · have hnot : x ∉ (Aᶜ : Set X) := by simpa using hx
        rw [onePointCollapse_coe_of_notMem Aᶜ x hnot, hkinfty]
        exact ((PointedQuotient.of_eq_basepoint_iff B (x : OnePoint X)).2
          ⟨((⟨x, hx⟩ : A) : OnePoint A), rfl⟩).symm
      · rw [onePointCollapse_coe_of_mem Aᶜ x hx]
        exact hkfinite ⟨x, hx⟩
  have hforget (a : RelativeKZero.{_, 0} B hB) :
      (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl (T a)).val =
        relativeKZeroForget B hB a := by
    change complexKZeroPullback c
      (complexKZeroPullback H (complexKZeroPullback ⟨q.symm, q.symm.continuous⟩ a.val)) =
        complexKZeroPullback Q a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    change complexKZeroPullback (k.comp c) a.val = complexKZeroPullback Q a.val
    rw [hsquare]
  apply le_antisymm
  · rintro a ⟨w, rfl⟩
    -- Extension of the actual supported boundary is ordinary relative forgetting.
    apply Subtype.ext
    change (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl
      (T (bundleKMinusOneBoundary B hB (J w.val)))).val = 0
    rw [hforget]
    exact (range_bundleKMinusOneBoundary B hB).le ⟨J w.val, rfl⟩
  · intro a ha
    change compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl a = 0 at ha
    obtain ⟨u, hu⟩ := hTbij.2 a
    have hzero : relativeKZeroForget B hB u = 0 := by
      rw [← hforget]
      have h : compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl (T u) = 0 := by
        rw [hu]
        exact ha
      exact congrArg Subtype.val h
    obtain ⟨w, hw⟩ := (range_bundleKMinusOneBoundary B hB).ge hzero
    -- Subtract a genuine restriction of a global constant class to remove its infinity value.
    let p₀ : B := e ∞
    let j : C(B, OnePoint X) := ⟨Subtype.val, continuous_subtype_val⟩
    let d : C(OnePoint X, B) := ContinuousMap.const (OnePoint X) p₀
    let cB : C(PUnit.{1}, B) := ContinuousMap.const PUnit.{1} p₀
    let cA : C(PUnit.{1}, OnePoint A) := ContinuousMap.const PUnit.{1} ∞
    have heval (z : BundleKMinusOne B) :
        bundleKMinusOnePullback cB
            (bundleKMinusOneRestriction B (bundleKMinusOnePullback d z)) =
          bundleKMinusOnePullback cB z := by
      change bundleKMinusOnePullback cB
        (bundleKMinusOnePullback j (bundleKMinusOnePullback d z)) = _
      rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp,
        ← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp]
      rfl
    let w' := w - bundleKMinusOneRestriction B (bundleKMinusOnePullback d w)
    have hkill : bundleKMinusOneBoundary B hB
        (bundleKMinusOneRestriction B (bundleKMinusOnePullback d w)) = 0 :=
      (range_bundleKMinusOneRestriction B hB).le ⟨bundleKMinusOnePullback d w, rfl⟩
    have hw' : bundleKMinusOneBoundary B hB w' = u := by
      change bundleKMinusOneBoundary B hB
        (w - bundleKMinusOneRestriction B (bundleKMinusOnePullback d w)) = u
      rw [map_sub, hw, hkill, sub_zero]
    have hpoint : ep.comp cA = cB := rfl
    have hwred : bundleKMinusOnePullback ep w' ∈ reducedBundleKMinusOne (∞ : OnePoint A) := by
      change bundleKMinusOnePullback cA (bundleKMinusOnePullback ep w') = 0
      rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hpoint]
      change bundleKMinusOnePullback cB
        (w - bundleKMinusOneRestriction B (bundleKMinusOnePullback d w)) = 0
      rw [map_sub, heval, sub_self]
    refine ⟨⟨bundleKMinusOnePullback ep w', hwred⟩, ?_⟩
    change T (bundleKMinusOneBoundary B hB (J (bundleKMinusOnePullback ep w'))) = a
    rw [hJright, hw', hu]

/-- KA II.4.7: open extension fills the kernel of actual proper restriction in K⁰. -/
theorem range_compactSupportKZeroOpenExtension (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    (compactSupportKZeroOpenExtension (Aᶜ : Set X) hA.isOpen_compl).range =
      (compactSupportKZeroPullback
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))
        hA.isClosedEmbedding_subtypeVal.isProperMap).ker := by
  /- Stage 1: apply range_relativeKZeroForget to (X⁺,B), then use the specified
  image homeomorphism and complement comparison. Its following restriction is
  precisely proper pullback along the original closed inclusion A → X.
  Stage 2: a supported class whose supported restriction is zero also has zero
  ordinary restriction to B, so ordinary exactness supplies its relative preimage.
  Conversely relative forgetting evaluates to zero at the original infinity,
  because infinity belongs to B. Thus the entire image already lies in the
  required evaluation kernel. Equality of underlying absolute classes gives
  equality in that subgroup, and open extension is the same actual collapse map. -/
  classical
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let B := compactifiedClosedImage A
  let hB : IsClosed B := (compactifiedClosedInclusion_geometry A hA).1.isClosed_range
  let := hB.isClosedEmbedding_subtypeVal.compactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.t2Space B hB
  let e := compactifiedClosedImageHomeomorph A hA
  let ec := compactifiedClosedComplementHomeomorph A hA
  let ep : C(OnePoint A, B) := ⟨e, e.continuous⟩
  let es : C(B, OnePoint A) := ⟨e.symm, e.symm.continuous⟩
  let i := compactifiedClosedInclusion A hA
  let j : C(B, OnePoint X) := ⟨Subtype.val, continuous_subtype_val⟩
  let T := (compactSupportKZeroHomeomorph ec).comp (relativeKZeroToCompactSupport B hB)
  have hTbij : Function.Bijective T :=
    (compactSupportKZeroHomeomorph_bijective ec).comp
      (relativeKZeroToCompactSupport_bijective B hB)
  -- Transport closed restriction by the same image homeomorphism, including infinity.
  have hEinj : Function.Injective (complexKZeroPullback ep) := by
    have hleft : Function.LeftInverse (complexKZeroPullback es) (complexKZeroPullback ep) := by
      intro a
      have hid : ep.comp es = ContinuousMap.id B := by
        apply ContinuousMap.ext
        intro p
        exact e.apply_symm_apply p
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
      change kZeroMap (RingHom.id _) a = a
      rw [kZeroMap_id]
      rfl
    exact hleft.injective
  have hi : j.comp ep = i := rfl
  have hrestriction (a : ComplexKZero (OnePoint X)) :
      complexKZeroPullback ep (complexKZeroRestriction B hB a) =
        complexKZeroPullback i a := by
    change complexKZeroPullback ep (complexKZeroPullback j a) = complexKZeroPullback i a
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hi]
  -- Retain the original quotient class in the extension/forgetting comparison.
  let q := PointedQuotient.onePointHomeomorph B hB
  let H := properOnePointMap ⟨ec.symm, ec.symm.continuous⟩ ec.symm.isProperMap
  let k : C(OnePoint (Aᶜ : Set X), PointedQuotient B) :=
    (⟨q.symm, q.symm.continuous⟩ : C(_, _)).comp H
  let c : C(OnePoint X, OnePoint (Aᶜ : Set X)) :=
    ⟨onePointCollapse Aᶜ, continuous_onePointCollapse Aᶜ hA.isOpen_compl⟩
  let Q : C(OnePoint X, PointedQuotient B) :=
    ⟨PointedQuotient.of B, PointedQuotient.continuous_of B⟩
  have hkinfty : k ∞ = PointedQuotient.basepoint B :=
    PointedQuotient.onePointHomeomorph_symm_infty B hB
  have hkfinite (p : (Aᶜ : Set X)) :
      k (p : OnePoint (Aᶜ : Set X)) = PointedQuotient.of B (p.val : OnePoint X) := by
    have hec : (ec.symm p).val = (p.val : OnePoint X) := rfl
    change q.symm ((ec.symm p : (Bᶜ : Set (OnePoint X))) :
      OnePoint (Bᶜ : Set (OnePoint X))) = _
    calc
      _ = PointedQuotient.of B (ec.symm p).val :=
        q.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of B hB (ec.symm p)).symm
      _ = PointedQuotient.of B (p.val : OnePoint X) := by rw [hec]
  have hsquare : k.comp c = Q := by
    ext p
    cases p using OnePoint.rec with
    | infty =>
      exact hkinfty.trans
        ((PointedQuotient.of_eq_basepoint_iff B ∞).2 ⟨∞, rfl⟩).symm
    | coe x =>
      change k (onePointCollapse Aᶜ (x : OnePoint X)) = PointedQuotient.of B (x : OnePoint X)
      by_cases hx : x ∈ A
      · have hnot : x ∉ (Aᶜ : Set X) := by simpa using hx
        rw [onePointCollapse_coe_of_notMem Aᶜ x hnot, hkinfty]
        exact ((PointedQuotient.of_eq_basepoint_iff B (x : OnePoint X)).2
          ⟨((⟨x, hx⟩ : A) : OnePoint A), rfl⟩).symm
      · rw [onePointCollapse_coe_of_mem Aᶜ x hx]
        exact hkfinite ⟨x, hx⟩
  have hforget (a : RelativeKZero.{_, 0} B hB) :
      (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl (T a)).val =
        relativeKZeroForget B hB a := by
    change complexKZeroPullback c
      (complexKZeroPullback H (complexKZeroPullback ⟨q.symm, q.symm.continuous⟩ a.val)) =
        complexKZeroPullback Q a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    change complexKZeroPullback (k.comp c) a.val = complexKZeroPullback Q a.val
    rw [hsquare]
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    obtain ⟨u, rfl⟩ := hTbij.2 b
    -- Ordinary relative forgetting restricts to zero on the same compactified closed image.
    have hzero : complexKZeroRestriction B hB
        (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl (T u)).val = 0 := by
      rw [hforget]
      exact complexKZeroRestriction_relativeKZeroForget B hB u
    apply Subtype.ext
    change complexKZeroPullback i
      (compactSupportKZeroOpenExtension Aᶜ hA.isOpen_compl (T u)).val = 0
    rw [← hrestriction, hzero, map_zero]
  · intro a ha
    have hzero : complexKZeroRestriction B hB a.val = 0 := by
      apply hEinj
      rw [hrestriction, map_zero]
      exact congrArg Subtype.val ha
    obtain ⟨u, hu⟩ := (range_relativeKZeroForget B hB).ge hzero
    -- The ordinary preimage extends to exactly the original supported class.
    refine ⟨T u, ?_⟩
    apply Subtype.ext
    exact (hforget u).trans hu

variable [LocallyCompactSpace Y] [T2Space Y]

/-- The same supported boundary is natural under proper maps and inverse-image closed pairs. -/
theorem compactSupportBundleKMinusOneBoundary_natural (A : Set Y) (hA : IsClosed A)
    (f : C(X, Y)) (hf : IsProperMap f) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    letI := (hA.preimage f.continuous).locallyCompactSpace
    letI := (hA.preimage f.continuous).isOpen_compl.locallyCompactSpace
    letI := (hA.isOpen_compl.preimage f.continuous).locallyCompactSpace
    (compactSupportKZeroPullback (preimageSubspaceMap (Aᶜ : Set Y) f)
        (isProperMap_preimageSubspaceMap (Aᶜ : Set Y) f hf)).comp
      (compactSupportBundleKMinusOneBoundary A hA) =
    (compactSupportBundleKMinusOneBoundary (f ⁻¹' A) (hA.preimage f.continuous)).comp
      (compactSupportBundleKMinusOnePullback (preimageSubspaceMap A f)
        (isProperMap_preimageSubspaceMap A f hf)) := by
  /- Stage 1: properness extends f to the actual pointed map X⁺ → Y⁺. Its
  restriction to the compactified closed images is the conjugate, by the same
  image homeomorphisms, of the one-point extension of f restricted over A.
  At finite points this is the original f; every infinity stays infinity.
  Stage 2: apply bundleKMinusOneBoundary_natural to these compact pairs.
  The relative-complement comparisons commute with the same quotient pullbacks,
  as is checked on finite representatives and on the collapsed closed images.
  Stage 3: transport the complements back to (f⁻¹'A)ᶜ and Aᶜ. The resulting map
  is exactly preimageSubspaceMap Aᶜ f, whose properness is inherited by base change.
  Restricting the input to the same infinity kernels proves the displayed square.
  No arbitrary map-of-pairs preimage or properness of an open inclusion is assumed. -/
  classical
  let D := f ⁻¹' A
  let hD : IsClosed D := hA.preimage f.continuous
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let := hD.locallyCompactSpace
  let := hD.isOpen_compl.locallyCompactSpace
  let := (hA.isOpen_compl.preimage f.continuous).locallyCompactSpace
  let BX := compactifiedClosedImage D
  let BY := compactifiedClosedImage A
  let hBX : IsClosed BX := (compactifiedClosedInclusion_geometry D hD).1.isClosed_range
  let hBY : IsClosed BY := (compactifiedClosedInclusion_geometry A hA).1.isClosed_range
  let := hBX.isClosedEmbedding_subtypeVal.compactSpace
  let := hBY.isClosedEmbedding_subtypeVal.compactSpace
  let := hBX.isOpen_compl.locallyCompactSpace
  let := hBY.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.t2Space BX hBX
  let := PointedQuotient.t2Space BY hBY
  let eX := compactifiedClosedImageHomeomorph D hD
  let eY := compactifiedClosedImageHomeomorph A hA
  let ecX := compactifiedClosedComplementHomeomorph D hD
  let ecY := compactifiedClosedComplementHomeomorph A hA
  let epX : C(OnePoint D, BX) := ⟨eX, eX.continuous⟩
  let epY : C(OnePoint A, BY) := ⟨eY, eY.continuous⟩
  let esX : C(BX, OnePoint D) := ⟨eX.symm, eX.symm.continuous⟩
  let esY : C(BY, OnePoint A) := ⟨eY.symm, eY.symm.continuous⟩
  let JX := bundleKMinusOnePullback esX
  let JY := bundleKMinusOnePullback esY
  let TX := (compactSupportKZeroHomeomorph ecX).comp (relativeKZeroToCompactSupport BX hBX)
  let TY := (compactSupportKZeroHomeomorph ecY).comp (relativeKZeroToCompactSupport BY hBY)
  let g := properOnePointMap f hf
  let fA := preimageSubspaceMap A f
  let gA := properOnePointMap fA (isProperMap_preimageSubspaceMap A f hf)
  let fC := preimageSubspaceMap (Aᶜ : Set Y) f
  let gC := properOnePointMap fC (isProperMap_preimageSubspaceMap (Aᶜ : Set Y) f hf)
  -- The actual proper extension sends the actual closed image into the target closed image.
  have hmaps : Set.MapsTo g BX BY := by
    intro p hp
    obtain ⟨z, rfl⟩ := hp
    cases z using OnePoint.rec with
    | infty => exact ⟨∞, rfl⟩
    | coe z => exact ⟨((⟨f z.val, z.property⟩ : A) : OnePoint A), rfl⟩
  let gB : C(BX, BY) :=
    ⟨fun p ↦ ⟨g p.val, hmaps p.property⟩,
      (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have himage : gB.comp epX = epY.comp gA := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    cases p using OnePoint.rec <;> rfl
  have hcoords : esY.comp gB = gA.comp esX := by
    apply ContinuousMap.ext
    intro p
    obtain ⟨z, rfl⟩ := eX.surjective p
    change eY.symm (gB (eX z)) = gA (eX.symm (eX z))
    rw [eX.symm_apply_apply]
    have hz := DFunLike.congr_fun himage z
    change gB (eX z) = eY (gA z) at hz
    rw [hz, eY.symm_apply_apply]
  have hJnatural (a : BundleKMinusOne (OnePoint A)) :
      bundleKMinusOnePullback gB (JY a) = JX (bundleKMinusOnePullback gA a) := by
    change bundleKMinusOnePullback gB (bundleKMinusOnePullback esY a) =
      bundleKMinusOnePullback esX (bundleKMinusOnePullback gA a)
    rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp,
      ← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hcoords]
  -- Identify the quotient comparisons on finite points and on the same infinity.
  let qX := PointedQuotient.onePointHomeomorph BX hBX
  let qY := PointedQuotient.onePointHomeomorph BY hBY
  let HX := properOnePointMap ⟨ecX.symm, ecX.symm.continuous⟩ ecX.symm.isProperMap
  let HY := properOnePointMap ⟨ecY.symm, ecY.symm.continuous⟩ ecY.symm.isProperMap
  let kX : C(OnePoint (Dᶜ : Set X), PointedQuotient BX) :=
    (⟨qX.symm, qX.symm.continuous⟩ : C(_, _)).comp HX
  let kY : C(OnePoint (Aᶜ : Set Y), PointedQuotient BY) :=
    (⟨qY.symm, qY.symm.continuous⟩ : C(_, _)).comp HY
  let Qg := PointedQuotient.mapContinuous BX BY g hmaps
  have hkXinfty : kX ∞ = PointedQuotient.basepoint BX :=
    PointedQuotient.onePointHomeomorph_symm_infty BX hBX
  have hkYinfty : kY ∞ = PointedQuotient.basepoint BY :=
    PointedQuotient.onePointHomeomorph_symm_infty BY hBY
  have hkXfinite (p : (Dᶜ : Set X)) :
      kX (p : OnePoint (Dᶜ : Set X)) = PointedQuotient.of BX (p.val : OnePoint X) := by
    have hec : (ecX.symm p).val = (p.val : OnePoint X) := rfl
    change qX.symm ((ecX.symm p : (BXᶜ : Set (OnePoint X))) :
      OnePoint (BXᶜ : Set (OnePoint X))) = _
    calc
      _ = PointedQuotient.of BX (ecX.symm p).val :=
        qX.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of BX hBX (ecX.symm p)).symm
      _ = PointedQuotient.of BX (p.val : OnePoint X) := by rw [hec]
  have hkYfinite (p : (Aᶜ : Set Y)) :
      kY (p : OnePoint (Aᶜ : Set Y)) = PointedQuotient.of BY (p.val : OnePoint Y) := by
    have hec : (ecY.symm p).val = (p.val : OnePoint Y) := rfl
    change qY.symm ((ecY.symm p : (BYᶜ : Set (OnePoint Y))) :
      OnePoint (BYᶜ : Set (OnePoint Y))) = _
    calc
      _ = PointedQuotient.of BY (ecY.symm p).val :=
        qY.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of BY hBY (ecY.symm p)).symm
      _ = PointedQuotient.of BY (p.val : OnePoint Y) := by rw [hec]
  have hquotient : kY.comp gC = Qg.comp kX := by
    apply ContinuousMap.ext
    intro p
    cases p using OnePoint.rec with
    | infty =>
      change kY ∞ = PointedQuotient.map BX BY g hmaps (kX ∞)
      rw [hkXinfty, hkYinfty]
      exact (PointedQuotient.map_basepoint BX BY g hmaps).symm
    | coe p =>
      change kY ((fC p : (Aᶜ : Set Y)) : OnePoint (Aᶜ : Set Y)) =
        PointedQuotient.map BX BY g hmaps
          (kX ((⟨p.val, p.property⟩ : (Dᶜ : Set X)) : OnePoint (Dᶜ : Set X)))
      rw [hkYfinite, hkXfinite, PointedQuotient.map_of]
      rfl
  -- Thus relative pullback and proper complement pullback keep the same original class.
  have hTX (a : RelativeKZero.{_, 0} BX hBX) :
      (TX a).val = complexKZeroPullback kX a.val := by
    change complexKZeroPullback HX
      (complexKZeroPullback ⟨qX.symm, qX.symm.continuous⟩ a.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  have hTY (a : RelativeKZero.{_, 0} BY hBY) :
      (TY a).val = complexKZeroPullback kY a.val := by
    change complexKZeroPullback HY
      (complexKZeroPullback ⟨qY.symm, qY.symm.continuous⟩ a.val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  have hTnatural (a : RelativeKZero.{_, 0} BY hBY) :
      compactSupportKZeroPullback fC (isProperMap_preimageSubspaceMap (Aᶜ : Set Y) f hf)
          (TY a) = TX (relativeKZeroPullback BX hBX BY hBY g hmaps a) := by
    apply Subtype.ext
    change complexKZeroPullback gC (TY a).val =
      (TX (relativeKZeroPullback BX hBX BY hBY g hmaps a)).val
    rw [hTY, hTX]
    change complexKZeroPullback gC (complexKZeroPullback kY a.val) =
      complexKZeroPullback kX (complexKZeroPullback Qg a.val)
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hquotient]
  -- Apply compact-pair naturality before the two specified coordinate transports.
  apply AddMonoidHom.ext
  intro a
  change compactSupportKZeroPullback fC
      (isProperMap_preimageSubspaceMap (Aᶜ : Set Y) f hf)
      (TY (bundleKMinusOneBoundary BY hBY (JY a.val))) =
    TX (bundleKMinusOneBoundary BX hBX (JX (bundleKMinusOnePullback gA a.val)))
  rw [hTnatural]
  have hboundary := DFunLike.congr_fun
    (bundleKMinusOneBoundary_natural BX hBX BY hBY g hmaps) (JY a.val)
  change relativeKZeroPullback BX hBX BY hBY g hmaps
      (bundleKMinusOneBoundary BY hBY (JY a.val)) =
    bundleKMinusOneBoundary BX hBX (bundleKMinusOnePullback gB (JY a.val)) at hboundary
  rw [hboundary, hJnatural]

end AtiyahSinger.ComplexBundle

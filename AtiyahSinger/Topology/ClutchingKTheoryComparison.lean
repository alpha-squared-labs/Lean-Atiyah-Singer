/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BoundaryCylinderSupport
public import AtiyahSinger.Topology.BundleKMinusOneSuspension
public import AtiyahSinger.Topology.KTheoryPairExact
public import AtiyahSinger.Topology.ReducedPuppeSequence
public import AtiyahSinger.Topology.SuspensionClutching
public import AtiyahSinger.Topology.SuspensionCompactification

/-!
# Clutching classes and the two specified connecting maps

Public module ID: M1618.

Karoubi II.1.34 and II.3.19 describe reduced suspension classes by normalized
automorphisms. Here the independent half-ray comparison of II.4.8 is transported
through the actual compactification homeomorphism and meridian collapse. The
generator formula then identifies that specified map with the two-chart bundle
of I.3.14. Bijectivity alone would not establish this formula or its sign.

II.3.30 is stated for the actual top inclusion of the mapping cylinder. Its
relative group is the reduced group of the existing cone. The comparison takes
values in the absolute group of that cone, via the injective subgroup inclusion;
it is not the relative forgetful map to the cylinder. The closed top is opposite
the half-ray's closed zero end. With the original source-to-target triple and
upper-to-lower clutching conventions, this produces an explicit minus sign.
II.4.9 consequently compares the existing alpha-inverse-beta map with the
negative of the positive supported boundary under our half-ray identification.
The textbook diagram is recovered by reversing that suspension identification;
none of the earlier maps or coordinates is silently changed here.
The normalized generator, signed top-cone comparison and specified cylinder/half-ray
boundary comparison are proved below. The last proof uses proper naturality at the
closed attaching seam, preserving the same maps and sign.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

attribute [local instance] UnreducedSuspension.compactSpace UnreducedSuspension.t2Space
  ReducedSuspension.compactSpace ReducedSuspension.t2Space
  MappingCylinder.compactSpace MappingCylinder.t2Space MappingCone.compactSpace MappingCone.t2Space
  ComplexBundle.trivialTopology ComplexBundle.isFiniteRank_trivial

variable (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/-- Pull back through the actual compactification coordinate and then the meridian quotient. -/
def compactSupportKZeroToSuspension :
    CompactSupportKZero (X × ℝ) →+
      reducedComplexKZero (UnreducedSuspension.south (X := OnePoint X)) :=
  (ReducedSuspension.kZeroEquiv (∞ : OnePoint X)).toAddMonoidHom.comp
    (reducedComplexKZeroPullback (ReducedSuspension.basepoint (∞ : OnePoint X)) ∞
      ⟨reducedSuspensionOnePointHomeomorph X, (reducedSuspensionOnePointHomeomorph X).continuous⟩
      (reducedSuspensionOnePointHomeomorph_basepoint X))

/-- Both factors of the specified suspension pullback are bijective. -/
theorem compactSupportKZeroToSuspension_bijective :
    Function.Bijective (compactSupportKZeroToSuspension X) := by
  /- The compactification factor is pullback by the actual pointed homeomorphism,
  with inverse pullback by its inverse. The second factor is exactly the earlier
  meridian-collapse equivalence from independent contractible-collapse invariance.
  Their composite is therefore bijective, including when X is empty. -/
  let e := reducedSuspensionOnePointHomeomorph X
  let b := ReducedSuspension.basepoint (∞ : OnePoint X)
  have he : e b = ∞ := reducedSuspensionOnePointHomeomorph_basepoint X
  let P := reducedComplexKZeroPullback b ∞ ⟨e, e.continuous⟩ he
  let Q := reducedComplexKZeroPullback ∞ b ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_eq.mpr he.symm)
  -- The same pointed homeomorphism supplies inverse pullbacks on the reduced kernels.
  have hinverse (a : reducedComplexKZero (∞ : OnePoint (X × ℝ))) : Q (P a) = a := by
    apply Subtype.ext
    change complexKZeroPullback ⟨e.symm, e.symm.continuous⟩
      (complexKZeroPullback ⟨e, e.continuous⟩ a.val) = a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hid : (⟨e, e.continuous⟩ : C(_, _)).comp ⟨e.symm, e.symm.continuous⟩ =
        ContinuousMap.id (OnePoint (X × ℝ)) := by
      ext p
      exact e.apply_symm_apply p
    rw [hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  have hright (a : reducedComplexKZero b) : P (Q a) = a := by
    apply Subtype.ext
    change complexKZeroPullback ⟨e, e.continuous⟩
      (complexKZeroPullback ⟨e.symm, e.symm.continuous⟩ a.val) = a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hid : (⟨e.symm, e.symm.continuous⟩ : C(_, _)).comp ⟨e, e.continuous⟩ =
        ContinuousMap.id (ReducedSuspension (∞ : OnePoint X)) := by
      ext p
      exact e.symm_apply_apply p
    rw [hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  have hP : Function.Bijective P :=
    ⟨Function.LeftInverse.injective hinverse, Function.RightInverse.surjective hright⟩
  exact (ReducedSuspension.kZeroEquiv (∞ : OnePoint X)).bijective.comp hP

/-- This equivalence retains the two specified geometric pullbacks as its forward map. -/
def compactSupportKZeroSuspensionEquiv :
    CompactSupportKZero (X × ℝ) ≃+
      reducedComplexKZero (UnreducedSuspension.south (X := OnePoint X)) :=
  AddEquiv.ofBijective (compactSupportKZeroToSuspension X)
    (compactSupportKZeroToSuspension_bijective X)

namespace ComplexBundle

/-- The half-ray comparison followed by the specified geometric suspension pullbacks. -/
def compactSupportBundleKMinusOneClutchingEquiv :
    CompactSupportBundleKMinusOne X ≃+
      reducedComplexKZero (UnreducedSuspension.south (X := OnePoint X)) :=
  (compactSupportBundleKMinusOneSuspensionEquiv X).trans
    (compactSupportKZeroSuspensionEquiv X)

variable {B : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]

/-- The standard normalized trivial representative of a reduced automorphism class. -/
theorem reducedBundleKMinusOne_exists_normalized_representative (b₀ : B)
    (a : reducedBundleKMinusOne b₀) :
    ∃ n : ℕ, ∃ α : Iso (FiniteBundle.trivial B n).Fiber (FiniteBundle.trivial B n).Fiber,
      (∀ v : Fin n → ℂ, α.linearEquiv b₀ v = v) ∧
        (⟨FiniteBundle.trivial B n, α⟩ : BundleAutomorphism B).kMinusOneClass = a.val := by
  /- Stage 1: use the single-pair representative and the finite complement on
  compact Hausdorff B to obtain a trivial-bundle automorphism beta for a.val.
  Stage 2: in those fixed coordinates set alpha(b)=beta(b) beta(b0)^(-1).
  This is a continuous automorphism with alpha(b0)=Id. The composition law
  II.3.6 says its class is [beta] minus the constant pullback of [beta(b0)].
  Stage 3: the latter point class is the evaluation of a.val and is zero because
  a belongs to the original reduced kernel. Thus normalization preserves a.val.
  No path from beta(b0) to identity and no vanishing theorem for the point group
  is assumed; the kernel condition supplies exactly the needed equality. -/
  obtain ⟨w, hw⟩ := bundleAutomorphism_kMinusOneClass_surjective a.val
  obtain ⟨n, β, hβ⟩ := w.exists_trivial_representative
  let E := FiniteBundle.trivial B n
  let W : BundleAutomorphism B := ⟨E, β⟩
  have hW : W.kMinusOneClass = a.val := hβ.trans hw
  let c : C(B, B) := ContinuousMap.const B b₀
  let T := pullbackTrivialIso c n
  let C : Iso E.Fiber E.Fiber := (T.symm.trans (β.pullback c)).trans T
  -- The constant automorphism uses the same trivial coordinates in every fiber.
  have hT (x : B) (v : Fin n → ℂ) : T.linearEquiv x v = v :=
    pullbackTrivialIso_apply c n x v
  have hTi (x : B) (v : Fin n → ℂ) : (T.linearEquiv x).symm v = v := by
    apply (T.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, hT]
  have hC (x : B) : C.linearEquiv x = β.linearEquiv b₀ := by
    apply LinearEquiv.ext
    intro v
    change T.linearEquiv x (β.linearEquiv b₀ ((T.linearEquiv x).symm v)) = _
    rw [hT, hTi]
  have hconj : (W.pullback c).IsIsomorphic ⟨E, C⟩ := by
    refine ⟨T, ?_⟩
    intro x v
    change Fin n → ℂ at v
    change T.linearEquiv x (β.linearEquiv b₀ v) = C.linearEquiv x (T.linearEquiv x v)
    rw [hT, hC, hT]
  -- Evaluation of the original reduced class kills this constant pullback.
  let p : C(PUnit.{1}, B) := ContinuousMap.const PUnit.{1} b₀
  let q : C(B, PUnit.{1}) := ContinuousMap.const B PUnit.unit
  have hc : p.comp q = c := rfl
  have hconstant : (⟨E, C⟩ : BundleAutomorphism B).kMinusOneClass = 0 := by
    rw [← BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      (W.pullback c) ⟨E, C⟩ hconj, ← bundleKMinusOnePullback_class, hW, ← hc,
      bundleKMinusOnePullback_comp]
    change bundleKMinusOnePullback q (bundleKMinusOnePullback p a.val) = 0
    rw [show bundleKMinusOnePullback p a.val = 0 from a.property, map_zero]
  let α := C.symm.trans β
  refine ⟨n, α, ?_, ?_⟩
  · intro v
    change β.linearEquiv b₀ ((C.linearEquiv b₀).symm v) = v
    rw [hC]
    exact (β.linearEquiv b₀).apply_symm_apply v
  · -- Composition adds classes, while the inverse constant contributes zero.
    rw [BundleAutomorphism.kMinusOneClass_trans]
    change (⟨E, C⟩ : BundleAutomorphism B).inverse.kMinusOneClass + W.kMinusOneClass = _
    rw [BundleAutomorphism.kMinusOneClass_inverse, hconstant, neg_zero, zero_add, hW]

/-- The prescribed comparison sends a normalized generator to its actual clutching bundle. -/
theorem compactSupportBundleKMinusOneClutchingEquiv_class
    (a : CompactSupportBundleKMinusOne X) (n : ℕ)
    (α : Iso (FiniteBundle.trivial (OnePoint X) n).Fiber
      (FiniteBundle.trivial (OnePoint X) n).Fiber)
    (hα : ∀ v : Fin n → ℂ, α.linearEquiv ∞ v = v)
    (ha : (⟨FiniteBundle.trivial (OnePoint X) n, α⟩ :
      BundleAutomorphism (OnePoint X)).kMinusOneClass = a.val) :
    compactSupportBundleKMinusOneClutchingEquiv X a = suspensionClutchingClass n α := by
  /- Stage 1: evaluate the actual half-ray zero-section boundary on this same
  normalized automorphism. The compactified boundary triple has alpha at the
  finite zero section and identity at infinity; use complement independence and
  the restricted-bundle formula for the original positive compact-pair boundary.
  Stage 2: its relative difference construction provides two trivial cone charts.
  The upper chart retains the source coordinate and the lower chart uses the
  target coordinate, so the upper-to-lower transition is alpha, not its inverse.
  The identity at infinity makes these charts agree along the infinity meridian.
  Stage 3: the half-ray coordinate r has log(r) on the complement. Its compact
  height r/(1+r) equals sigmoid(log(r)), exactly the specified homeomorphism.
  Pulling back through this homeomorphism and then the meridian quotient gives
  the same two-chart descent object as suspensionClutchingBundle. Descent
  uniqueness identifies the bundles, and the same trivial rank is subtracted.
  This verifies the actual map formula, not merely existence of an isomorphism. -/
  classical
  -- Keep the actual compactified zero section and its original complement maps.
  let A := halfRayZeroSection X
  let hA : IsClosed A := isClosed_halfRayZeroSection X
  let H := OnePoint (X × NNReal)
  let C : Set H := ComplexBundle.compactifiedClosedImage A
  have hC : IsClosed C :=
    (ComplexBundle.compactifiedClosedInclusion_geometry A hA).1.isClosed_range
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let := hC.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.t2Space.{_, 0} C hC
  let e0 := halfRayZeroSectionHomeomorph X
  let j : C(OnePoint X, H) := (ComplexBundle.compactifiedClosedInclusion A hA).comp
    (properOnePointMap ⟨e0, e0.continuous⟩ e0.isProperMap)
  let ec := ComplexBundle.compactifiedClosedComplementHomeomorph A hA
  let eray := halfRayComplementHomeomorph X
  let relHome := PointedQuotient.onePointHomeomorph.{_, 0} C hC
  let mapComplement : C(OnePoint (Aᶜ : Set (X × NNReal)), OnePoint (Cᶜ : Set H)) :=
    properOnePointMap ⟨ec.symm, ec.symm.continuous⟩ ec.symm.isProperMap
  let mapRay : C(OnePoint (X × ℝ), OnePoint (Aᶜ : Set (X × NNReal))) :=
    properOnePointMap ⟨eray.symm, eray.symm.continuous⟩ eray.symm.isProperMap
  let mapRelative : C(OnePoint (Cᶜ : Set H), PointedQuotient.{_, 0} C) :=
    ⟨relHome.symm, relHome.symm.continuous⟩
  let mapSuspension : C(UnreducedSuspension (OnePoint X), OnePoint (X × ℝ)) :=
    (⟨reducedSuspensionOnePointHomeomorph X,
      (reducedSuspensionOnePointHomeomorph X).continuous⟩ : C(_, _)).comp
        (ReducedSuspension.quotientMap (∞ : OnePoint X))
  let F : C(UnreducedSuspension (OnePoint X), PointedQuotient.{_, 0} C) :=
    mapRelative.comp (mapComplement.comp (mapRay.comp mapSuspension))
  have htransport (c : RelativeKZero (C) (hC)) :
      (compactSupportKZeroToSuspension X
        (compactSupportKZeroHomeomorph (halfRayComplementHomeomorph X)
          (compactSupportKZeroHomeomorph
            (ComplexBundle.compactifiedClosedComplementHomeomorph (A)
              (isClosed_halfRayZeroSection X))
            (relativeKZeroToCompactSupport (C) (hC) c)))).val =
        complexKZeroPullback (F) c.val := by
    -- Unfold only the specified group transports, leaving the original geometric maps intact.
    change complexKZeroPullback (ReducedSuspension.quotientMap (∞ : OnePoint X))
        (complexKZeroPullback
          ⟨reducedSuspensionOnePointHomeomorph X,
            (reducedSuspensionOnePointHomeomorph X).continuous⟩
          (complexKZeroPullback (mapRay)
            (complexKZeroPullback (mapComplement)
              (complexKZeroPullback (mapRelative) c.val)))) = _
    simp only [F, mapSuspension, complexKZeroPullback_comp, AddMonoidHom.comp_apply]
  have hmeridian (t : unitInterval) :
      F (UnreducedSuspension.of (∞ : OnePoint X) t) =
        PointedQuotient.of (C)
          (halfRayCompactificationContraction X (t, j ∞)) := by
    have hmeridian := ReducedSuspension.quotientMap_meridian (∞ : OnePoint X) t
    change ReducedSuspension.quotientMap ∞ (UnreducedSuspension.of ∞ t) = _ at hmeridian
    change (mapRelative) ((mapComplement) ((mapRay)
      ((reducedSuspensionOnePointHomeomorph X)
        (ReducedSuspension.quotientMap ∞ (UnreducedSuspension.of ∞ t))))) = _
    rw [hmeridian, reducedSuspensionOnePointHomeomorph_basepoint]
    change (PointedQuotient.onePointHomeomorph (C) (hC)).symm ∞ =
      PointedQuotient.of (C) ∞
    rw [PointedQuotient.onePointHomeomorph_symm_infty]
    exact ((PointedQuotient.of_eq_basepoint_iff (C) ∞).mpr ⟨∞, rfl⟩).symm
  have hfinite (x : X) (t : unitInterval) (ht₀ : 0 < t) (ht₁ : t < 1) :
      F (UnreducedSuspension.of (x : OnePoint X) t) =
        PointedQuotient.of (C)
          (halfRayCompactificationContraction X (t, j (x : OnePoint X))) := by
    let r : ℝ := (t : ℝ) / (1 - (t : ℝ))
    have hr : 0 < r := div_pos ht₀ (sub_pos.mpr ht₁)
    let p : ((A)ᶜ : Set (X × NNReal)) :=
      (halfRayComplementHomeomorph X).symm (x, Real.log r)
    let e := ComplexBundle.compactifiedClosedComplementHomeomorph (A)
      (isClosed_halfRayZeroSection X)
    let q : ((C)ᶜ : Set (OnePoint (X × NNReal))) := e.symm p
    have hq : q.val = ((x, ⟨r, hr.le⟩) : X × NNReal) := by
      change (p.val : OnePoint (X × NNReal)) = _
      apply congrArg OnePoint.some
      refine Prod.ext rfl (NNReal.eq ?_)
      exact Real.exp_log hr
    have hrelative : mapRelative (q : OnePoint ((C)ᶜ : Set (OnePoint (X × NNReal)))) =
        PointedQuotient.of (C) q := by
      apply (PointedQuotient.onePointHomeomorph (C) (hC)).injective
      rw [PointedQuotient.onePointHomeomorph_of]
      exact (PointedQuotient.onePointHomeomorph (C) (hC)).apply_symm_apply q
    -- The compactification uses logit; the next original homeomorphism applies exp.
    change (mapRelative) ((mapComplement) ((mapRay)
      ((reducedSuspensionOnePointHomeomorph X)
        (ReducedSuspension.quotientMap ∞ (UnreducedSuspension.of (x : OnePoint X) t))))) = _
    rw [reducedSuspensionOnePointHomeomorph_of X x t ht₀ ht₁]
    change mapRelative (q : OnePoint ((C)ᶜ : Set (OnePoint (X × NNReal)))) = _
    rw [hrelative, hq]
    apply congrArg (PointedQuotient.of (C))
    -- At the zero section, the contraction has exactly radius t/(1-t).
    change (((x, ⟨r, hr.le⟩) : X × NNReal) : OnePoint (X × NNReal)) =
      halfRayCompactificationContraction X
        (t, (((x, 0) : X × NNReal) : OnePoint (X × NNReal)))
    simp only [halfRayCompactificationContraction, OnePoint.elim_some,
      show (t : ℝ) < 1 from ht₁, ite_true]
    apply congrArg OnePoint.some
    refine Prod.ext rfl (NNReal.eq ?_)
    change r = (0 + (t : ℝ)) / (1 - (t : ℝ))
    rw [zero_add]
  have hF (b : OnePoint X) (t : unitInterval) :
      F (UnreducedSuspension.of b t) =
        PointedQuotient.of (C)
          (halfRayCompactificationContraction X (t, j b)) := by
    have hinfty : (∞ : OnePoint (X × NNReal)) ∈ C := ⟨∞, rfl⟩
    have hzero (b : OnePoint X) : j b ∈ C := by
      let hA := isClosed_halfRayZeroSection X
      let := hA.locallyCompactSpace
      exact ⟨properOnePointMap
        ⟨halfRayZeroSectionHomeomorph X, (halfRayZeroSectionHomeomorph X).continuous⟩
        (halfRayZeroSectionHomeomorph X).isProperMap b, rfl⟩
    have hcollapsed (u : unitInterval) : F (UnreducedSuspension.of (∞ : OnePoint X) u) =
        PointedQuotient.basepoint (C) := by
      rw [hmeridian]
      change PointedQuotient.of (C) ∞ = PointedQuotient.basepoint (C)
      exact (PointedQuotient.of_eq_basepoint_iff (C) ∞).mpr hinfty
    by_cases ht₀ : t = 0
    · subst t
      rw [UnreducedSuspension.of_zero, ← UnreducedSuspension.of_zero (∞ : OnePoint X),
        hcollapsed, (halfRayCompactificationContraction_properties X).2.1]
      exact ((PointedQuotient.of_eq_basepoint_iff (C) (j b)).mpr (hzero b)).symm
    by_cases ht₁ : t = 1
    · subst t
      rw [UnreducedSuspension.of_one, ← UnreducedSuspension.of_one (∞ : OnePoint X),
        hcollapsed, (halfRayCompactificationContraction_properties X).2.2.1]
      exact ((PointedQuotient.of_eq_basepoint_iff (C) ∞).mpr hinfty).symm
    -- Away from the poles, the finite and infinity cases were checked in their actual models.
    cases b using OnePoint.rec with
    | infty => exact hmeridian t
    | coe x =>
      exact hfinite x t
        (lt_of_le_of_ne (by exact t.property.1) (Ne.symm ht₀))
        (lt_of_le_of_ne (by exact t.property.2) ht₁)
  let B := OnePoint X
  let S := UnreducedSuspension B
  let D := DoubleSpace C
  let := DoubleSpace.compactSpace C
  let := DoubleSpace.t2Space C hC
  let := hC.isClosedEmbedding_subtypeVal.compactSpace
  let eJ : B ≃ₜ C := e0.onePointCongr.trans (compactifiedClosedImageHomeomorph A hA)
  have hj (b : B) : (eJ b).val = j b := rfl
  have hjmem (b : B) : j b ∈ C := (hj b) ▸ (eJ b).property
  let K := halfRayCompactificationContraction X
  have hK : Continuous K := (halfRayCompactificationContraction_properties X).1
  have hK0 (z : H) : K (0, z) = z :=
    (halfRayCompactificationContraction_properties X).2.1 z
  have hK1 (z : H) : K (1, z) = ∞ :=
    (halfRayCompactificationContraction_properties X).2.2.1 z
  -- Contract from the equator into the left upper cone and the right lower cone.
  let up (t : unitInterval) : unitInterval := ⟨max 0 (2 * (t : ℝ) - 1), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (by linarith [t.property.2])⟩
  let down (t : unitInterval) : unitInterval := ⟨max 0 (1 - 2 * (t : ℝ)), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (by linarith [t.property.1])⟩
  have hup : Continuous up := by
    apply Continuous.subtype_mk
    fun_prop
  have hdown : Continuous down := by
    apply Continuous.subtype_mk
    fun_prop
  let U₀ : Set (B × unitInterval) := {p | 1 / 2 ≤ (p.2 : ℝ)}
  let L₀ : Set (B × unitInterval) := {p | (p.2 : ℝ) ≤ 1 / 2}
  have hU₀ : IsClosed U₀ :=
    isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)
  have hL₀ : IsClosed L₀ :=
    isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
  have hcover : U₀ ∪ L₀ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact le_total (1 / 2 : ℝ) p.2
  let rawU : C(B × unitInterval, D) := (DoubleSpace.leftMap C).comp
    ⟨fun p ↦ K (up p.2, j p.1), hK.comp ((hup.comp continuous_snd).prodMk
      (j.continuous.comp continuous_fst))⟩
  let rawL : C(B × unitInterval, D) := (DoubleSpace.rightMap C).comp
    ⟨fun p ↦ K (down p.2, j p.1), hK.comp ((hdown.comp continuous_snd).prodMk
      (j.continuous.comp continuous_fst))⟩
  have hrawSeam (p : B × unitInterval) (hpU : p ∈ U₀) (hpL : p ∈ L₀) :
      rawU p = rawL p := by
    have ht : (p.2 : ℝ) = 1 / 2 := le_antisymm hpL hpU
    have hu : up p.2 = 0 := Subtype.ext (by norm_num [up, ht])
    have hl : down p.2 = 0 := Subtype.ext (by norm_num [down, ht])
    change DoubleSpace.left C (K (up p.2, j p.1)) =
      DoubleSpace.right C (K (down p.2, j p.1))
    rw [hu, hl, hK0]
    exact DoubleSpace.left_eq_right C ⟨j p.1, hjmem p.1⟩
  let raw (p : B × unitInterval) : D := if p ∈ U₀ then rawU p else rawL p
  have hrawU (p : B × unitInterval) (hp : p ∈ U₀) : raw p = rawU p := by
    simp only [raw, hp, ite_true]
  have hrawL (p : B × unitInterval) (hp : p ∈ L₀) : raw p = rawL p := by
    dsimp only [raw]
    split_ifs with hu
    · exact hrawSeam p hu hp
    · rfl
  have hraw : Continuous raw := by
    rw [← continuousOn_univ, ← hcover]
    apply ContinuousOn.union_of_isClosed _ _ hU₀ hL₀
    · exact rawU.continuous.continuousOn.congr (fun p hp ↦ hrawU p hp)
    · exact rawL.continuous.continuousOn.congr (fun p hp ↦ hrawL p hp)
  let rawMap : C(B × unitInterval, D) := ⟨raw, hraw⟩
  have hrawZero (b : B) : rawMap (b, 0) = DoubleSpace.right C ∞ := by
    change raw (b, 0) = _
    rw [hrawL (b, 0) (by change (0 : ℝ) ≤ 1 / 2; norm_num)]
    change DoubleSpace.right C (K (down 0, j b)) = _
    have ht : down 0 = 1 := Subtype.ext (by norm_num [down])
    rw [ht, hK1]
  have hrawOne (b : B) : rawMap (b, 1) = DoubleSpace.left C ∞ := by
    change raw (b, 1) = _
    rw [hrawU (b, 1) (by change (1 : ℝ) / 2 ≤ 1; norm_num)]
    change DoubleSpace.left C (K (up 1, j b)) = _
    have ht : up 1 = 1 := Subtype.ext (by norm_num [up])
    rw [ht, hK1]
  -- Descend through the two original pointed quotients, retaining both original poles.
  let quotientLift (Z W : Type _) [TopologicalSpace Z] [TopologicalSpace W]
      (T : Set Z) (g : C(Z, W)) (p : W) (h : ∀ z ∈ T, g z = p) :
      C(PointedQuotient.{_, 0} T, W) := by
    let g₀ : Z ⊕ PUnit → W := Sum.elim g (fun _ ↦ p)
    have hr : ∀ x y, PairCollapseRel T x y → g₀ x = g₀ y := by
      intro x y hxy
      rcases hxy with rfl | ⟨hx, hy⟩
      · rfl
      have hc (z : Z ⊕ PUnit) (hz : z ∈ pairCollapsedSet T) : g₀ z = p := by
        cases z with
        | inl b =>
          exact h b (by simpa only [pairCollapsedSet, Set.mem_union,
            Set.mem_image, Set.mem_range, Sum.inl.injEq, exists_eq_right,
            Sum.inr_ne_inl, exists_false, or_false] using hz)
        | inr u => rfl
      exact (hc x hx).trans (hc y hy).symm
    exact ⟨Quotient.lift g₀ hr, (g.continuous.sumElim continuous_const).quotient_lift hr⟩
  let suspensionLift (Z : Type _) [TopologicalSpace Z]
      (g : C(B × unitInterval, Z)) (p₀ p₁ : Z)
      (h₀ : ∀ b : B, g (b, 0) = p₀) (h₁ : ∀ b : B, g (b, 1) = p₁) : C(S, Z) :=
    let l := quotientLift (B × unitInterval) Z (UnreducedSuspension.lowerEnd B) g p₀ (by
      rintro ⟨b, t⟩ ht
      change t = 0 at ht
      subst t
      exact h₀ b)
    quotientLift (UnreducedSuspension.LowerCone B) Z (UnreducedSuspension.upperEnd B) l p₁
      (by rintro z ⟨b, rfl⟩; exact h₁ b)
  let d : C(S, D) := suspensionLift D rawMap (DoubleSpace.right C ∞)
    (DoubleSpace.left C ∞) hrawZero hrawOne
  let U := UnreducedSuspension.upperHemisphere B
  let L := UnreducedSuspension.lowerHemisphere B
  let iU : C(U, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let iL : C(L, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let pU : C(U, H) := (DoubleSpace.projMap C).comp (d.comp iU)
  let pL : C(L, H) := (DoubleSpace.projMap C).comp (d.comp iL)
  have hdU : d.comp iU = (DoubleSpace.leftMap C).comp pU := by
    ext z
    change d z.val = DoubleSpace.left C (DoubleSpace.proj C (d z.val))
    rcases z.property with hz | ⟨b, t, ht, hz⟩
    · rw [hz]
      rfl
    · rw [hz]
      change raw (b, t) = DoubleSpace.left C (DoubleSpace.proj C (raw (b, t)))
      rw [hrawU (b, t) ht]
      rfl
  have hdL : d.comp iL = (DoubleSpace.rightMap C).comp pL := by
    ext z
    change d z.val = DoubleSpace.right C (DoubleSpace.proj C (d z.val))
    rcases z.property with hz | ⟨b, t, ht, hz⟩
    · rw [hz]
      rfl
    · rw [hz]
      change raw (b, t) = DoubleSpace.right C (DoubleSpace.proj C (raw (b, t)))
      rw [hrawL (b, t) ht]
      rfl
  -- Collapse only the right copy of the same actual double.
  let qC : C(H, PointedQuotient.{_, 0} C) :=
    ⟨PointedQuotient.of C, PointedQuotient.continuous_of C⟩
  have hQrel : ∀ p r : H ⊕ H, DoubleRel C p r →
      Sum.elim qC (fun _ ↦ PointedQuotient.basepoint C) p =
        Sum.elim qC (fun _ ↦ PointedQuotient.basepoint C) r := by
    intro p r hpr
    rcases hpr with ⟨hxy, hside⟩
    by_cases hpr : p = r
    · exact congrArg (Sum.elim qC (fun _ ↦ PointedQuotient.basepoint C)) hpr
    have hmem : Sum.elim id id p ∈ C := hside.resolve_left hpr
    cases p with
    | inl x =>
      cases r with
      | inl y =>
        dsimp at hxy
        subst y
        rfl
      | inr y => exact (PointedQuotient.of_eq_basepoint_iff C x).mpr hmem
    | inr x =>
      cases r with
      | inl y =>
        dsimp at hxy
        subst y
        exact ((PointedQuotient.of_eq_basepoint_iff C x).mpr hmem).symm
      | inr y => rfl
  let Q : C(D, PointedQuotient.{_, 0} C) :=
    { toFun := Quotient.lift (Sum.elim qC (fun _ ↦ PointedQuotient.basepoint C)) hQrel
      continuous_toFun := (qC.continuous.sumElim continuous_const).quotient_lift _ }
  have hQleft (z : H) : Q (DoubleSpace.left C z) = PointedQuotient.of C z := rfl
  have hQright (z : H) : Q (DoubleSpace.right C z) = PointedQuotient.basepoint C := rfl
  -- Use the same finite trivial coordinates on the compactified zero section.
  let g : C(C, B) := ⟨eJ.symm, eJ.symm.continuous⟩
  let i : C(C, H) := ⟨Subtype.val, continuous_subtype_val⟩
  let t := pullbackTrivialIso i n
  let u := pullbackTrivialIso g n
  let γ : RelativeTriple (FiniteBundle.trivial H n).Fiber
      (FiniteBundle.trivial H n).Fiber C :=
    t.trans (u.symm.trans ((α.pullback g).trans (u.trans t.symm)))
  let trip := BundleTriple.ofBoundary (FiniteBundle.trivial H n) (FiniteBundle.trivial H n) γ
  have ht (x : C) (v : Fin n → ℂ) : t.linearEquiv x v = v :=
    pullbackTrivialIso_apply i n x v
  have hti (x : C) (v : Fin n → ℂ) : (t.linearEquiv x).symm v = v := by
    apply (t.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, ht]
  have hu (x : C) (v : Fin n → ℂ) : u.linearEquiv x v = v :=
    pullbackTrivialIso_apply g n x v
  have hui (x : C) (v : Fin n → ℂ) : (u.linearEquiv x).symm v = v := by
    apply (u.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, hu]
  have hγ (x : C) (v : Fin n → ℂ) : γ.linearEquiv x v = α.linearEquiv (g x) v := by
    change (t.linearEquiv x).symm
      (u.linearEquiv x (α.linearEquiv (g x) ((u.linearEquiv x).symm (t.linearEquiv x v)))) = _
    rw [ht, hui, hu, hti]
  -- Normalization makes the two fixed coordinates agree along the infinity meridian.
  have hγInfinity (v : Fin n → ℂ) : γ.linearEquiv (eJ ∞) v = v := by
    erw [hγ]
    change α.linearEquiv (eJ.symm (eJ ∞)) v = v
    rw [eJ.symm_apply_apply]
    exact hα v
  let V := clutchingBundle hC trip
  let W := V.pullback d
  let cU := clutchingLeftIso hC trip
  let cL := clutchingRightIso hC trip
  -- Pull back the actual double charts using the specified hemisphere factorizations.
  have isoEq (Z : Set S) (f k : C(Z, D)) (h : f = k) :
      ∃ q : Iso ((f : Z → D) *ᵖ V.Fiber) ((k : Z → D) *ᵖ V.Fiber),
        ∀ z v, q.linearEquiv z v = cast (congrArg V.Fiber (DFunLike.congr_fun h z)) v := by
    subst k
    exact ⟨Iso.refl _, fun _ _ ↦ rfl⟩
  obtain ⟨qU, hqU⟩ := isoEq U (d.comp iU) ((DoubleSpace.leftMap C).comp pU) hdU
  obtain ⟨qL, hqL⟩ := isoEq L (d.comp iL) ((DoubleSpace.rightMap C).comp pL) hdL
  let eU : Iso (W.restrict U).Fiber (FiniteBundle.trivial U n).Fiber :=
    (pullbackCompIso (E := V.Fiber) d iU).trans (qU.trans
      ((pullbackCompIso (E := V.Fiber) (DoubleSpace.leftMap C) pU).symm.trans
        ((cU.pullback pU).trans (pullbackTrivialIso pU n))))
  let eL : Iso (W.restrict L).Fiber (FiniteBundle.trivial L n).Fiber :=
    (pullbackCompIso (E := V.Fiber) d iL).trans (qL.trans
      ((pullbackCompIso (E := V.Fiber) (DoubleSpace.rightMap C) pL).symm.trans
        ((cL.pullback pL).trans (pullbackTrivialIso pL n))))
  have hinvComp (Z : Set S) (f : C(H, D)) (k : C(Z, H))
      (z : Z) (v : V.Fiber (f (k z))) :
      ((pullbackCompIso (E := V.Fiber) f k).linearEquiv z).symm v = v := by
    have hh := pullbackCompIso_apply (E := V.Fiber) f k z
      (((pullbackCompIso (E := V.Fiber) f k).linearEquiv z).symm v)
    exact hh.symm.trans (LinearEquiv.apply_symm_apply _ _)
  have heU (z : U) (v : W.Fiber z) : eU.linearEquiv z v =
      cU.linearEquiv (pU z)
        (cast (congrArg V.Fiber (DFunLike.congr_fun hdU z)) v) := by
    change (pullbackTrivialIso pU n).linearEquiv z
      (cU.linearEquiv (pU z)
        (((pullbackCompIso (E := V.Fiber) (DoubleSpace.leftMap C) pU).linearEquiv z).symm
          (qU.linearEquiv z ((pullbackCompIso (E := V.Fiber) d iU).linearEquiv z v)))) = _
    erw [pullbackTrivialIso_apply, hinvComp, hqU, pullbackCompIso_apply]
    rfl
  have heL (z : L) (v : W.Fiber z) : eL.linearEquiv z v =
      cL.linearEquiv (pL z)
        (cast (congrArg V.Fiber (DFunLike.congr_fun hdL z)) v) := by
    change (pullbackTrivialIso pL n).linearEquiv z
      (cL.linearEquiv (pL z)
        (((pullbackCompIso (E := V.Fiber) (DoubleSpace.rightMap C) pL).linearEquiv z).symm
          (qL.linearEquiv z ((pullbackCompIso (E := V.Fiber) d iL).linearEquiv z v)))) = _
    erw [pullbackTrivialIso_apply, hinvComp, hqL, pullbackCompIso_apply]
    rfl
  have hdEquator (b : B) :
      d (UnreducedSuspension.equator B b) = DoubleSpace.left C (j b) := by
    change raw (b, ⟨1 / 2, by norm_num, by norm_num⟩) = _
    rw [hrawU _ (by change (1 / 2 : ℝ) ≤ 1 / 2; exact le_rfl)]
    change DoubleSpace.left C (K (up ⟨1 / 2, by norm_num, by norm_num⟩, j b)) = _
    have hp : up ⟨1 / 2, by norm_num, by norm_num⟩ = 0 :=
      Subtype.ext (by norm_num [up])
    rw [hp, hK0]
  have seam (b : B) (p q : H) (hp : p = j b) (hq : q = j b)
      (δ : DoubleSpace.left C p = DoubleSpace.right C q) (v : Fin n → ℂ) :
      cL.linearEquiv q (cast (congrArg V.Fiber δ) ((cU.linearEquiv p).symm v)) =
        α.linearEquiv b v := by
    subst p
    subst q
    have hc := clutching_compatible hC trip (eJ b) v
    change cL.linearEquiv (j b)
      (cast (congrArg V.Fiber (DoubleSpace.left_eq_right C (eJ b)))
        ((cU.linearEquiv (j b)).symm v)) = γ.linearEquiv (eJ b) v at hc
    by_cases hb : b = ∞
    · subst b
      exact (hc.trans (hγInfinity v)).trans (hα v).symm
    · erw [hγ] at hc
      exact hc.trans (congrArg (fun z : B ↦ α.linearEquiv z v) (eJ.symm_apply_apply b))
  have hcompatible : SuspensionClutchingCompatible n α W eU eL := by
    intro b v
    let zU : U := ⟨UnreducedSuspension.equator B b, Or.inr ⟨b, _, le_rfl, rfl⟩⟩
    let zL : L := ⟨UnreducedSuspension.equator B b, Or.inr ⟨b, _, le_rfl, rfl⟩⟩
    let w : W.Fiber (UnreducedSuspension.equator B b) := (eU.linearEquiv zU).symm v
    have hpU : pU zU = j b := by
      change DoubleSpace.proj C (d (UnreducedSuspension.equator B b)) = _
      rw [hdEquator]
      rfl
    have hpL : pL zL = j b := by
      change DoubleSpace.proj C (d (UnreducedSuspension.equator B b)) = _
      rw [hdEquator]
      rfl
    have hw : cU.linearEquiv (pU zU)
        (cast (congrArg V.Fiber (DFunLike.congr_fun hdU zU)) w) = v :=
      (heU zU w).symm.trans (LinearEquiv.apply_symm_apply _ _)
    have hc := seam b (pU zU) (pL zL) hpU hpL
      ((DFunLike.congr_fun hdU zU).symm.trans (DFunLike.congr_fun hdL zL))
      (cU.linearEquiv (pU zU)
        (cast (congrArg V.Fiber (DFunLike.congr_fun hdU zU)) w))
    erw [LinearEquiv.symm_apply_apply, hw] at hc
    change eL.linearEquiv zL w = _
    rw [heL]
    convert hc using 1
    exact congrArg (cL.linearEquiv (pL zL)) (cast_cast _ _ w).symm
  obtain ⟨hglue⟩ := nonempty_suspensionClutching_iso n α W eU eL hcompatible
  -- Compare the original boundary input with this same compactified triple.
  let zInverse : C(OnePoint A, B) :=
    properOnePointMap ⟨e0.symm, e0.symm.continuous⟩ e0.symm.isProperMap
  let imageInverse : C(C, OnePoint A) :=
    ⟨(compactifiedClosedImageHomeomorph A hA).symm,
      (compactifiedClosedImageHomeomorph A hA).symm.continuous⟩
  let c : RelativeKZero.{_, 0} C hC := bundleKMinusOneBoundary C hC
    (bundleKMinusOnePullback imageInverse (bundleKMinusOnePullback zInverse a.val))
  have hforward : (compactSupportBundleKMinusOneClutchingEquiv X a).val =
      complexKZeroPullback F c.val := by
    change (compactSupportKZeroToSuspension X
      (compactSupportKZeroHomeomorph eray
        (compactSupportKZeroHomeomorph ec (relativeKZeroToCompactSupport C hC c)))).val = _
    exact htransport c
  have hcoordinate : zInverse.comp imageInverse = g := rfl
  let B₀ : BundleAutomorphism B := ⟨FiniteBundle.trivial B n, α⟩
  have hconjugate : (B₀.pullback g).IsIsomorphic
      ⟨(FiniteBundle.trivial H n).restrict C, γ⟩ := by
    refine ⟨u.trans t.symm, ?_⟩
    intro x v
    change (t.linearEquiv x).symm (u.linearEquiv x (α.linearEquiv (g x) v)) =
      γ.linearEquiv x ((t.linearEquiv x).symm (u.linearEquiv x v))
    erw [hu, hti, hγ, hu, hti]
  have hc : c = trip.relativeClass hC := by
    change bundleKMinusOneBoundary C hC
      (bundleKMinusOnePullback imageInverse (bundleKMinusOnePullback zInverse a.val)) = _
    rw [← ha]
    change bundleKMinusOneBoundary C hC
      (bundleKMinusOnePullback imageInverse
        (bundleKMinusOnePullback zInverse B₀.kMinusOneClass)) = _
    have hinput : bundleKMinusOnePullback imageInverse
        (bundleKMinusOnePullback zInverse B₀.kMinusOneClass) =
        bundleKMinusOnePullback g B₀.kMinusOneClass := by
      rw [← hcoordinate]
      exact (DFunLike.congr_fun (bundleKMinusOnePullback_comp imageInverse zInverse)
        B₀.kMinusOneClass).symm
    rw [hinput, bundleKMinusOnePullback_class,
      BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hconjugate,
      bundleKMinusOneBoundary_restricted]
  -- The right-retract quotient realizes the original relative class on the double.
  let R := DoubleSpace.rightRange C
  have hR : IsClosed R := DoubleSpace.isClosed_rightRange C hC
  let := PointedQuotient.t2Space R hR
  let k : C(PointedQuotient.{_, 0} C, PointedQuotient.{_, 0} R) :=
    PointedQuotient.mapContinuous C R (DoubleSpace.leftMap C) (DoubleSpace.left_mapsTo C)
  let qR : C(D, PointedQuotient.{_, 0} R) :=
    ⟨PointedQuotient.of R, PointedQuotient.continuous_of R⟩
  have hquotient : k.comp Q = qR := by
    ext z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => rfl
      | inr x =>
        exact ((PointedQuotient.of_eq_basepoint_iff R (DoubleSpace.right C x)).mpr
          ⟨x, rfl⟩).symm
  have hdouble : complexKZeroPullback Q c.val = trip.doubleDifference hC := by
    rw [hc]
    change complexKZeroPullback Q (complexKZeroPullback k (trip.differenceLift hC).val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hquotient]
    exact trip.forget_differenceLift hC
  -- Descent uniqueness identifies the actual glued bundle, with the same trivial rank.
  let := isFiniteRank_pullback (E := V.Fiber) d
  let pd : C(S, H) := (DoubleSpace.projMap C).comp d
  let := isFiniteRank_pullback (E := (FiniteBundle.trivial H n).Fiber) pd
  have hV : complexKZeroPullback d V.kZeroClass = (suspensionClutchingBundle n α).kZeroClass := by
    erw [← kZeroClass_pullback]
    exact kZeroClass_eq_of_iso hglue
  have htrivial : complexKZeroPullback pd (FiniteBundle.trivial H n).kZeroClass =
      (FiniteBundle.trivial S n).kZeroClass := by
    erw [← kZeroClass_pullback]
    exact kZeroClass_eq_of_iso (pullbackTrivialIso pd n)
  have hclass : complexKZeroPullback d (trip.doubleDifference hC) =
      (suspensionClutchingClass n α).val := by
    change complexKZeroPullback d
      (V.kZeroClass - complexKZeroPullback (DoubleSpace.projMap C)
        (FiniteBundle.trivial H n).kZeroClass) =
          (suspensionClutchingBundle n α).kZeroClass - (FiniteBundle.trivial S n).kZeroClass
    rw [map_sub, hV, ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rw [show (DoubleSpace.projMap C).comp d = pd from rfl, htrivial]
  -- Interpolate the original height to the upper-half pinching height.
  let pinchTime (u t : unitInterval) : unitInterval :=
    ⟨(1 - (u : ℝ)) * (t : ℝ) + (u : ℝ) * (up t : ℝ), by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) t.property.1)
          (mul_nonneg u.property.1 (up t).property.1)
      · have h₁ := mul_nonneg (sub_nonneg.mpr u.property.2)
          (sub_nonneg.mpr t.property.2)
        have h₂ := mul_nonneg u.property.1 (sub_nonneg.mpr (up t).property.2)
        nlinarith⟩
  have hpinchZero (u : unitInterval) : pinchTime u 0 = 0 := by
    apply Subtype.ext
    norm_num [pinchTime, up]
  have hpinchOne (u : unitInterval) : pinchTime u 1 = 1 := by
    apply Subtype.ext
    dsimp [pinchTime, up]
    norm_num
  have hpinchStart (t : unitInterval) : pinchTime 0 t = t := by
    apply Subtype.ext
    simp [pinchTime]
  have hpinchFinish (t : unitInterval) : pinchTime 1 t = up t := by
    apply Subtype.ext
    simp [pinchTime]
  have hpinch : Continuous (fun p : unitInterval × (B × unitInterval) ↦
      pinchTime p.1 p.2.2) := by
    apply Continuous.subtype_mk
    change Continuous (fun p : unitInterval × (B × unitInterval) ↦
      (1 - (p.1 : ℝ)) * (p.2.2 : ℝ) + (p.1 : ℝ) * (up p.2.2 : ℝ))
    fun_prop
  have hfamily : Continuous (fun p : unitInterval × (B × unitInterval) ↦
      qC (K (pinchTime p.1 p.2.2, j p.2.1))) :=
    qC.continuous.comp (hK.comp (hpinch.prodMk
      (j.continuous.comp (continuous_fst.comp continuous_snd))))
  let family (u : unitInterval) : C(B × unitInterval, PointedQuotient.{_, 0} C) :=
    ⟨fun p ↦ qC (K (pinchTime u p.2, j p.1)),
      hfamily.comp (continuous_const.prodMk continuous_id)⟩
  let pbase : C(unitInterval, PointedQuotient.{_, 0} C) :=
    ContinuousMap.const unitInterval (PointedQuotient.basepoint C)
  have hfamilyZero (u : unitInterval) (b : B) : family u (b, 0) = pbase u := by
    change qC (K (pinchTime u 0, j b)) = PointedQuotient.basepoint C
    rw [hpinchZero, hK0]
    exact (PointedQuotient.of_eq_basepoint_iff C (j b)).mpr (hjmem b)
  have hfamilyOne (u : unitInterval) (b : B) : family u (b, 1) = pbase u := by
    change qC (K (pinchTime u 1, j b)) = PointedQuotient.basepoint C
    rw [hpinchOne, hK1]
    exact (PointedQuotient.of_eq_basepoint_iff C ∞).mpr ⟨∞, rfl⟩
  -- Local compactness of the time parameter preserves joint continuity at each quotient.
  have quotientLiftJoint (Z W : Type _) [TopologicalSpace Z] [TopologicalSpace W]
      (T : Set Z) (g : unitInterval → C(Z, W)) (p : C(unitInterval, W))
      (h : ∀ u : unitInterval, ∀ z ∈ T, g u z = p u)
      (hg : Continuous (fun q : unitInterval × Z ↦ g q.1 q.2)) :
      Continuous (fun q : unitInterval × PointedQuotient.{_, 0} T ↦
        quotientLift Z W T (g q.1) (p q.1) (h q.1) q.2) := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    have hc : Continuous (Sum.elim
        (fun q : unitInterval × Z ↦ g q.1 q.2)
        (fun q : unitInterval × PUnit ↦ p q.1)) :=
      hg.sumElim (p.continuous.comp continuous_fst)
    convert hc.comp
      (Homeomorph.prodSumDistrib (X := unitInterval) (Y := Z) (Z := PUnit)).continuous
        using 1
    funext q
    rcases q with ⟨u, z⟩
    cases z <;> rfl
  let hl (u : unitInterval) (z : B × unitInterval)
      (hz : z ∈ UnreducedSuspension.lowerEnd B) : family u z = pbase u := by
    rcases z with ⟨b, t⟩
    change t = 0 at hz
    subst t
    exact hfamilyZero u b
  let lowerFamily (u : unitInterval) :
      C(UnreducedSuspension.LowerCone B, PointedQuotient.{_, 0} C) :=
    quotientLift (B × unitInterval) (PointedQuotient.{_, 0} C)
      (UnreducedSuspension.lowerEnd B) (family u) (pbase u) (hl u)
  have hu (u : unitInterval) (z : UnreducedSuspension.LowerCone B)
      (hz : z ∈ UnreducedSuspension.upperEnd B) : lowerFamily u z = pbase u := by
    obtain ⟨b, rfl⟩ := hz
    exact hfamilyOne u b
  have hLower : Continuous (fun q : unitInterval × UnreducedSuspension.LowerCone B ↦
      lowerFamily q.1 q.2) :=
    quotientLiftJoint (B × unitInterval) (PointedQuotient.{_, 0} C)
      (UnreducedSuspension.lowerEnd B) family pbase hl hfamily
  have hLift : Continuous (fun q : unitInterval × S ↦
      suspensionLift (PointedQuotient.{_, 0} C) (family q.1) (pbase q.1) (pbase q.1)
        (hfamilyZero q.1) (hfamilyOne q.1) q.2) :=
    quotientLiftJoint (UnreducedSuspension.LowerCone B) (PointedQuotient.{_, 0} C)
      (UnreducedSuspension.upperEnd B) lowerFamily pbase hu hLower
  -- The pinched endpoint is the specified double collapse on both actual hemispheres.
  have hQdof (b : B) (t : unitInterval) :
      (Q.comp d) (UnreducedSuspension.of b t) = qC (K (up t, j b)) := by
    change Q (raw (b, t)) = qC (K (up t, j b))
    by_cases ht : 1 / 2 ≤ (t : ℝ)
    · rw [hrawU (b, t) ht]
      exact hQleft _
    · rw [hrawL (b, t) (le_of_lt (lt_of_not_ge ht))]
      change Q (DoubleSpace.right C (K (down t, j b))) = qC (K (up t, j b))
      rw [hQright]
      have hupZero : up t = 0 := by
        apply Subtype.ext
        change max 0 (2 * (t : ℝ) - 1) = 0
        exact max_eq_left (by linarith)
      rw [hupZero, hK0]
      exact ((PointedQuotient.of_eq_basepoint_iff C (j b)).mpr (hjmem b)).symm
  have suspensionMapsEq (f g : C(S, PointedQuotient.{_, 0} C))
      (hof : ∀ b : B, ∀ t : unitInterval,
        f (UnreducedSuspension.of b t) = g (UnreducedSuspension.of b t)) : f = g := by
    apply ContinuousMap.ext
    intro z
    rcases PointedQuotient.eq_basepoint_or_exists (UnreducedSuspension.upperEnd B) z with
      rfl | ⟨y, rfl⟩
    · change f (UnreducedSuspension.north (X := B)) =
        g (UnreducedSuspension.north (X := B))
      rw [← UnreducedSuspension.of_one (∞ : B)]
      exact hof ∞ 1
    rcases PointedQuotient.eq_basepoint_or_exists (UnreducedSuspension.lowerEnd B) y with
      rfl | ⟨p, rfl⟩
    · change f (UnreducedSuspension.south (X := B)) =
        g (UnreducedSuspension.south (X := B))
      rw [← UnreducedSuspension.of_zero (∞ : B)]
      exact hof ∞ 0
    exact hof p.1 p.2
  have hstart : suspensionLift (PointedQuotient.{_, 0} C) (family 0) (pbase 0) (pbase 0)
      (hfamilyZero 0) (hfamilyOne 0) = F := by
    apply suspensionMapsEq
    intro b t
    change qC (K (pinchTime 0 t, j b)) = F (UnreducedSuspension.of b t)
    rw [hpinchStart, hF]
    rfl
  have hfinish : suspensionLift (PointedQuotient.{_, 0} C) (family 1) (pbase 1) (pbase 1)
      (hfamilyZero 1) (hfamilyOne 1) = Q.comp d := by
    apply suspensionMapsEq
    intro b t
    change qC (K (pinchTime 1 t, j b)) = (Q.comp d) (UnreducedSuspension.of b t)
    rw [hpinchFinish, hQdof]
  let hhomotopy : ContinuousMap.Homotopy F (Q.comp d) :=
    { toFun := fun q ↦ suspensionLift (PointedQuotient.{_, 0} C) (family q.1)
        (pbase q.1) (pbase q.1) (hfamilyZero q.1) (hfamilyOne q.1) q.2
      continuous_toFun := hLift
      map_zero_left := fun z ↦ congrArg (fun g : C(S, PointedQuotient.{_, 0} C) ↦ g z) hstart
      map_one_left := fun z ↦ congrArg (fun g : C(S, PointedQuotient.{_, 0} C) ↦ g z) hfinish }
  apply Subtype.ext
  calc
    (compactSupportBundleKMinusOneClutchingEquiv X a).val =
        complexKZeroPullback F c.val := hforward
    _ = complexKZeroPullback (Q.comp d) c.val :=
      DFunLike.congr_fun (complexKZeroPullback_eq_of_homotopy F (Q.comp d) hhomotopy) c.val
    _ = complexKZeroPullback d (complexKZeroPullback Q c.val) :=
      DFunLike.congr_fun (complexKZeroPullback_comp d Q) c.val
    _ = complexKZeroPullback d (trip.doubleDifference hC) :=
      congrArg (complexKZeroPullback d) hdouble
    _ = (suspensionClutchingClass n α).val := hclass

variable {X} {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

/-- The specified clutching comparison is natural for the original proper base map. -/
theorem compactSupportBundleKMinusOneClutchingEquiv_natural (f : C(X, Y))
    (hf : IsProperMap f) :
    (puppeSuspensionPullback (properOnePointMap f hf)).comp
        (compactSupportBundleKMinusOneClutchingEquiv Y).toAddMonoidHom =
      (compactSupportBundleKMinusOneClutchingEquiv X).toAddMonoidHom.comp
        (compactSupportBundleKMinusOnePullback f hf) := by
  /- Compose the proper naturality square of the same half-ray boundary with
  reducedSuspensionOnePointHomeomorph_natural and the meridian quotient square.
  Contravariance gives the displayed order. Every map preserves the actual
  infinity and uses the same increasing real coordinate. No arbitrary pointed
  compactification map is asserted to arise from a proper finite-space map. -/
  apply AddMonoidHom.ext
  intro a
  have hs := DFunLike.congr_fun (compactSupportBundleKMinusOneSuspension_natural f hf) a
  let F := properOnePointMap f hf
  let R := properOnePointMap (f.prodMap (ContinuousMap.id ℝ))
    (hf.prodMap isProperMap_id)
  let eX : C(ReducedSuspension (∞ : OnePoint X), OnePoint (X × ℝ)) :=
    ⟨reducedSuspensionOnePointHomeomorph X,
      (reducedSuspensionOnePointHomeomorph X).continuous⟩
  let eY : C(ReducedSuspension (∞ : OnePoint Y), OnePoint (Y × ℝ)) :=
    ⟨reducedSuspensionOnePointHomeomorph Y,
      (reducedSuspensionOnePointHomeomorph Y).continuous⟩
  let qX := ReducedSuspension.quotientMap (∞ : OnePoint X)
  let qY := ReducedSuspension.quotientMap (∞ : OnePoint Y)
  -- The compactification square and the actual meridian quotient give one geometric square.
  have hcompact := reducedSuspensionOnePointHomeomorph_natural f hf
  have hmeridian := ReducedSuspension.map_quotientMap F ∞ ∞ rfl
  have hsquare : (eY.comp qY).comp (UnreducedSuspension.map F) =
      R.comp (eX.comp qX) := by
    rw [ContinuousMap.comp_assoc, ← hmeridian, ← ContinuousMap.comp_assoc,
      hcompact, ContinuousMap.comp_assoc]
  apply Subtype.ext
  change complexKZeroPullback (UnreducedSuspension.map F)
      (complexKZeroPullback qY (complexKZeroPullback eY
        (compactSupportBundleKMinusOneSuspension Y a).val)) =
    complexKZeroPullback qX (complexKZeroPullback eX
      (compactSupportBundleKMinusOneSuspension X
        (compactSupportBundleKMinusOnePullback f hf a)).val)
  -- First combine the actual pullbacks, then use the positive half-ray naturality equality.
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← ContinuousMap.comp_assoc, hsquare]
  rw [complexKZeroPullback_comp]
  change complexKZeroPullback (eX.comp qX)
      (compactSupportKZeroPullback (f.prodMap (ContinuousMap.id ℝ))
        (hf.prodMap isProperMap_id) (compactSupportBundleKMinusOneSuspension Y a)).val = _
  rw [show compactSupportKZeroPullback (f.prodMap (ContinuousMap.id ℝ))
      (hf.prodMap isProperMap_id) (compactSupportBundleKMinusOneSuspension Y a) =
      compactSupportBundleKMinusOneSuspension X
        (compactSupportBundleKMinusOnePullback f hf a) from hs]
  rw [complexKZeroPullback_comp]
  rfl

variable (X)

/-- KA II.1.34/II.3.19 in the based compactification model: normalized clutching is onto. -/
theorem exists_normalized_suspensionClutchingClass
    (b : reducedComplexKZero (UnreducedSuspension.south (X := OnePoint X))) :
    ∃ n : ℕ, ∃ α : Iso (FiniteBundle.trivial (OnePoint X) n).Fiber
      (FiniteBundle.trivial (OnePoint X) n).Fiber,
      (∀ v : Fin n → ℂ, α.linearEquiv ∞ v = v) ∧ suspensionClutchingClass n α = b := by
  /- Take the inverse image of b under the specified clutching equivalence.
  Its normalized trivial representative is supplied by the preceding reduced
  representative theorem. The actual generator formula identifies its glued
  class with b. This uses the independently constructed half-ray bijection and
  the verified chart comparison; it does not define the bundle by surjectivity. -/
  let a := (compactSupportBundleKMinusOneClutchingEquiv X).symm b
  obtain ⟨n, α, hα, ha⟩ := reducedBundleKMinusOne_exists_normalized_representative ∞ a
  refine ⟨n, α, hα, ?_⟩
  -- Use the same representative in the actual generator formula and its inverse identity.
  have hgenerator := compactSupportBundleKMinusOneClutchingEquiv_class X a n α hα ha
  exact hgenerator.symm.trans
    ((compactSupportBundleKMinusOneClutchingEquiv X).apply_symm_apply b)

/-- Equality of normalized clutching classes is exactly the original stable zero criterion. -/
theorem suspensionClutchingClass_eq_iff_stable (n m : ℕ)
    (α : Iso (FiniteBundle.trivial (OnePoint X) n).Fiber
      (FiniteBundle.trivial (OnePoint X) n).Fiber)
    (β : Iso (FiniteBundle.trivial (OnePoint X) m).Fiber
      (FiniteBundle.trivial (OnePoint X) m).Fiber)
    (hα : ∀ v : Fin n → ℂ, α.linearEquiv ∞ v = v)
    (hβ : ∀ v : Fin m → ℂ, β.linearEquiv ∞ v = v) :
    suspensionClutchingClass n α = suspensionClutchingClass m β ↔
      ∃ F : FiniteBundle (OnePoint X),
        (((⟨FiniteBundle.trivial (OnePoint X) n, α⟩ : BundleAutomorphism (OnePoint X)).sum
          (⟨FiniteBundle.trivial (OnePoint X) m, β⟩ : BundleAutomorphism (OnePoint X)).inverse).sum
            (BundleAutomorphism.identity F)).IsElementary := by
  /- Normalization puts both automorphism classes in the original infinity
  kernel. The actual generator formula and injectivity of the specified
  comparison identify equality of clutching classes with equality of those
  automorphism classes. Direct-sum and inverse formulas rewrite this as vanishing
  of alpha plus beta inverse. Apply the original II.3.7 stable zero criterion.
  Its stabilizing bundle is arbitrary finite rank. On this compact base a
  complement can make stabilization trivial if desired, but no such coordinate
  choice or a based homotopy is silently imposed in the displayed statement. -/
  let A : BundleAutomorphism (OnePoint X) := ⟨FiniteBundle.trivial (OnePoint X) n, α⟩
  let B : BundleAutomorphism (OnePoint X) := ⟨FiniteBundle.trivial (OnePoint X) m, β⟩
  -- Evaluation of either normalized generator is the actual identity pair at the point.
  have hred (k : ℕ)
      (γ : Iso (FiniteBundle.trivial (OnePoint X) k).Fiber
        (FiniteBundle.trivial (OnePoint X) k).Fiber)
      (hγ : ∀ v : Fin k → ℂ, γ.linearEquiv ∞ v = v) :
      (⟨FiniteBundle.trivial (OnePoint X) k, γ⟩ :
        BundleAutomorphism (OnePoint X)).kMinusOneClass ∈
          reducedBundleKMinusOne (∞ : OnePoint X) := by
    let p : C(PUnit.{1}, OnePoint X) := ContinuousMap.const PUnit.{1} ∞
    let W : BundleAutomorphism (OnePoint X) := ⟨FiniteBundle.trivial (OnePoint X) k, γ⟩
    let T := FiniteBundle.trivial PUnit.{1} k
    have hi : (W.pullback p).IsIsomorphic (BundleAutomorphism.identity T) := by
      refine ⟨pullbackTrivialIso p k, ?_⟩
      intro x v
      change Fin k → ℂ at v
      change (pullbackTrivialIso p k).linearEquiv x (γ.linearEquiv ∞ v) =
        (pullbackTrivialIso p k).linearEquiv x v
      rw [hγ]
    change bundleKMinusOnePullback p W.kMinusOneClass = 0
    rw [bundleKMinusOnePullback_class,
      BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hi]
    exact (BundleAutomorphism.identity T).kMinusOneClass_eq_zero_of_isElementary
      (IsoHomotopy.nonempty_refl (Iso.refl T.Fiber))
  let a : CompactSupportBundleKMinusOne X := ⟨A.kMinusOneClass, hred n α hα⟩
  let b : CompactSupportBundleKMinusOne X := ⟨B.kMinusOneClass, hred m β hβ⟩
  have ha := compactSupportBundleKMinusOneClutchingEquiv_class X a n α hα rfl
  have hb := compactSupportBundleKMinusOneClutchingEquiv_class X b m β hβ rfl
  rw [← ha, ← hb]
  -- Injectivity reduces this to the original automorphism presentation, with arbitrary F.
  constructor
  · intro h
    have hab : A.kMinusOneClass = B.kMinusOneClass :=
      congrArg Subtype.val ((compactSupportBundleKMinusOneClutchingEquiv X).injective h)
    apply ((A.sum B.inverse).kMinusOneClass_eq_zero_iff).mp
    rw [BundleAutomorphism.kMinusOneClass_sum,
      BundleAutomorphism.kMinusOneClass_inverse, hab, add_neg_cancel]
  · intro h
    have hzero := ((A.sum B.inverse).kMinusOneClass_eq_zero_iff).mpr h
    rw [BundleAutomorphism.kMinusOneClass_sum,
      BundleAutomorphism.kMinusOneClass_inverse] at hzero
    have hab : a = b := Subtype.ext (eq_of_sub_eq_zero
      (by simpa only [sub_eq_add_neg] using hzero))
    exact congrArg (compactSupportBundleKMinusOneClutchingEquiv X) hab

section MappingCylinder

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- KA II.3.30 with the sign fixed by the actual upper-to-lower and top-pair conventions. -/
theorem suspensionClutching_puppe_eq_neg_boundary (f : C(Y, X)) (n : ℕ)
    (α : Iso (FiniteBundle.trivial Y n).Fiber (FiniteBundle.trivial Y n).Fiber) :
    let T := Set.range (mappingCylinderTop f)
    let hT : IsClosed T := (mappingCylinder_closedEmbeddings f).2.1.isClosed_range
    letI := hT.isClosedEmbedding_subtypeVal.compactSpace
    let e : Y ≃ₜ T := (mappingCylinder_closedEmbeddings f).2.1.isEmbedding.toHomeomorph
    complexKZeroPullback (puppeConeCollapse f) (suspensionClutchingClass n α).val =
      -(bundleKMinusOneBoundary T hT
        (bundleKMinusOnePullback ⟨e.symm, e.symm.continuous⟩
          (⟨FiniteBundle.trivial Y n, α⟩ : BundleAutomorphism Y).kMinusOneClass)).val := by
  /- Stage 1: the top embedding identifies Y with the actual closed subset T
  of the mapping cylinder. Its pointed quotient is definitionally MappingCone f,
  so the relative group's subtype value belongs to K-zero of this same cone.
  It is not relativeKZeroForget, which would instead land on the cylinder.
  Stage 2: pull back the two clutching charts through the actual cone-collapse
  map. The upper half remains the top half-tube, while the lower chart includes
  the base X. Their transition at height one half is the original alpha.
  Stage 3: following II.3.30 and I.3.3, move this seam to the top using the same
  two trivial cylinder bundles. Here the lower chart is the source coordinate
  in the cylinder interior, and the upper chart is the target coordinate at T.
  Since upper-to-lower is alpha, source-to-target is alpha inverse. Thus the
  relative triple is (trivial,trivial,alpha inverse). The restricted-bundle
  boundary formula and inverse-class law give the displayed negative boundary.
  This sign records the specified local conventions rather than copying the
  source diagram under an unstated orientation identification. Equality is in
  the cone group; no injectivity of the relative forgetful map is used. -/
  classical
  let H := MappingCylinder f
  let T := Set.range (mappingCylinderTop f)
  have hT : IsClosed T := (mappingCylinder_closedEmbeddings f).2.1.isClosed_range
  let := hT.isClosedEmbedding_subtypeVal.compactSpace
  let := DoubleSpace.t2Space T hT
  let := PointedQuotient.t2Space T hT
  let D := DoubleSpace T
  let S := UnreducedSuspension Y
  let e : Y ≃ₜ T := (mappingCylinder_closedEmbeddings f).2.1.isEmbedding.toHomeomorph
  -- A common seam equation descends any two specified maps from the original double.
  have respects (l r : H → S) (h : ∀ x : T, l x = r x) :
      ∀ p q : H ⊕ H, DoubleRel T p q → Sum.elim l r p = Sum.elim l r q := by
    intro p q hpq
    rcases hpq with ⟨hxy, hside⟩
    by_cases hpq : p = q
    · exact congrArg (Sum.elim l r) hpq
    have hmem : Sum.elim id id p ∈ T := hside.resolve_left hpq
    cases p with
    | inl x =>
      cases q with
      | inl y =>
        dsimp at hxy
        subst y
        rfl
      | inr y =>
        dsimp at hxy
        subst y
        exact h ⟨x, hmem⟩
    | inr x =>
      cases q with
      | inl y =>
        dsimp at hxy
        subst y
        exact (h ⟨x, hmem⟩).symm
      | inr y =>
        dsimp at hxy
        subst y
        rfl
  let q : C(H, MappingCone f) := mappingConeQuotient f
  have hqtop (x : T) : q x = mappingConeTip f :=
    (PointedQuotient.of_eq_basepoint_iff T x).mpr x.property
  have hrelQ : ∀ p r : H ⊕ H, DoubleRel T p r →
      Sum.elim q (fun _ ↦ mappingConeTip f) p =
        Sum.elim q (fun _ ↦ mappingConeTip f) r := by
    intro p r hpr
    rcases hpr with ⟨hxy, hside⟩
    by_cases hpr : p = r
    · exact congrArg (Sum.elim q (fun _ ↦ mappingConeTip f)) hpr
    have hmem : Sum.elim id id p ∈ T := hside.resolve_left hpr
    cases p with
    | inl x =>
      cases r with
      | inl y =>
        dsimp at hxy
        subst y
        rfl
      | inr y => exact hqtop ⟨x, hmem⟩
    | inr x =>
      cases r with
      | inl y =>
        dsimp at hxy
        subst y
        exact (hqtop ⟨x, hmem⟩).symm
      | inr y => rfl
  let Q : C(D, MappingCone f) :=
    { toFun := Quotient.lift (Sum.elim q (fun _ ↦ mappingConeTip f))
        hrelQ
      continuous_toFun := (q.continuous.sumElim continuous_const).quotient_lift _ }
  let tL (s t : unitInterval) : unitInterval :=
    ⟨(1 - (s : ℝ) / 2) * (t : ℝ), by
      have hst := mul_le_mul_of_nonneg_right s.property.2 t.property.1
      have hnonneg := mul_nonneg s.property.1 t.property.1
      constructor <;> nlinarith [t.property.1, t.property.2]⟩
  let tR (s t : unitInterval) : unitInterval :=
    ⟨1 - (s : ℝ) * (t : ℝ) / 2, by
      have hst := mul_le_mul_of_nonneg_right s.property.2 t.property.1
      have hnonneg := mul_nonneg s.property.1 t.property.1
      constructor <;> nlinarith [t.property.1, t.property.2]⟩
  have htL : Continuous (fun p : unitInterval × unitInterval ↦ tL p.1 p.2) := by
    apply Continuous.subtype_mk
    fun_prop
  have htR : Continuous (fun p : unitInterval × unitInterval ↦ tR p.1 p.2) := by
    apply Continuous.subtype_mk
    fun_prop
  let lower (s : unitInterval) : C(Y × unitInterval, S) :=
    UnreducedSuspension.ofMap.comp
      ⟨fun p ↦ (p.1, tL s p.2),
        continuous_fst.prodMk (htL.comp (continuous_const.prodMk continuous_snd))⟩
  let upper (s : unitInterval) : C(Y × unitInterval, S) :=
    UnreducedSuspension.ofMap.comp
      ⟨fun p ↦ (p.1, tR s p.2),
        continuous_fst.prodMk (htR.comp (continuous_const.prodMk continuous_snd))⟩
  have hlower (s : unitInterval) (y : Y) :
      lower s (y, 0) = UnreducedSuspension.south := by
    change UnreducedSuspension.of y (tL s 0) = _
    have ht : tL s 0 = 0 := Subtype.ext (by simp [tL])
    rw [ht, UnreducedSuspension.of_zero]
  have hupper (s : unitInterval) (y : Y) :
      upper s (y, 0) = UnreducedSuspension.north := by
    change UnreducedSuspension.of y (tR s 0) = _
    have ht : tR s 0 = 1 := Subtype.ext (by simp [tR])
    rw [ht, UnreducedSuspension.of_one]
  let L (s : unitInterval) : C(H, S) :=
    mappingCylinderLift f (ContinuousMap.const X UnreducedSuspension.south)
      (lower s) (hlower s)
  let R (s : unitInterval) : C(H, S) :=
    mappingCylinderLift f (ContinuousMap.const X UnreducedSuspension.north)
      (upper s) (hupper s)
  have hseam (s : unitInterval) (x : T) : L s x = R s x := by
    obtain ⟨y, hy⟩ := x.property
    change L s x.val = R s x.val
    rw [← hy]
    change UnreducedSuspension.of y (tL s 1) = UnreducedSuspension.of y (tR s 1)
    congr 1
    apply Subtype.ext
    dsimp [tL, tR]
    ring
  let G (s : unitInterval) : C(D, S) :=
    { toFun := Quotient.lift (Sum.elim (L s) (R s)) (respects (L s) (R s) (hseam s))
      continuous_toFun := ((L s).continuous.sumElim (R s).continuous).quotient_lift _ }
  -- Move the same seam from the top to height one half, continuously in both copies.
  have hjoint (side : Bool) : Continuous (fun p : unitInterval × H ↦
      (if side then L p.1 else R p.1) p.2) := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    cases side
    · have hc : Continuous (Sum.elim
          (fun _ : unitInterval × X ↦ (UnreducedSuspension.north : S))
          (fun p : unitInterval × (Y × unitInterval) ↦
            UnreducedSuspension.of p.2.1 (tR p.1 p.2.2))) :=
        continuous_const.sumElim (UnreducedSuspension.ofMap.continuous.comp
          (continuous_snd.fst.prodMk
            (htR.comp (continuous_fst.prodMk continuous_snd.snd))))
      convert hc.comp (Homeomorph.prodSumDistrib
        (X := unitInterval) (Y := X) (Z := Y × unitInterval)).continuous using 1
      funext p
      rcases p with ⟨s, z⟩
      cases z <;> rfl
    · have hc : Continuous (Sum.elim
          (fun _ : unitInterval × X ↦ (UnreducedSuspension.south : S))
          (fun p : unitInterval × (Y × unitInterval) ↦
            UnreducedSuspension.of p.2.1 (tL p.1 p.2.2))) :=
        continuous_const.sumElim (UnreducedSuspension.ofMap.continuous.comp
          (continuous_snd.fst.prodMk
            (htL.comp (continuous_fst.prodMk continuous_snd.snd))))
      convert hc.comp (Homeomorph.prodSumDistrib
        (X := unitInterval) (Y := X) (Z := Y × unitInterval)).continuous using 1
      funext p
      rcases p with ⟨s, z⟩
      cases z <;> rfl
  have hG : Continuous (fun p : unitInterval × D ↦ G p.1 p.2) := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    have hc := (hjoint true).sumElim (hjoint false)
    convert hc.comp (Homeomorph.prodSumDistrib
      (X := unitInterval) (Y := H) (Z := H)).continuous using 1
    funext p
    rcases p with ⟨s, z⟩
    cases z <;> rfl
  have hGzero : G 0 = (puppeConeCollapse f).comp Q := by
    ext z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z with
          | inl x => rfl
          | inr yt =>
            change UnreducedSuspension.of yt.1 (tL 0 yt.2) =
              UnreducedSuspension.of yt.1 yt.2
            congr 1
            exact Subtype.ext (by simp [tL])
      | inr z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z with
          | inl x => rfl
          | inr yt =>
            change UnreducedSuspension.of yt.1 (tR 0 yt.2) = UnreducedSuspension.north
            have ht : tR 0 yt.2 = 1 := Subtype.ext (by simp [tR])
            rw [ht, UnreducedSuspension.of_one]
  let homotopy : ContinuousMap.Homotopy ((puppeConeCollapse f).comp Q) (G 1) :=
    { toFun := fun p ↦ G p.1 p.2
      continuous_toFun := hG
      map_zero_left := fun z ↦ DFunLike.congr_fun hGzero z
      map_one_left := fun _ ↦ rfl }
  let Us := UnreducedSuspension.upperHemisphere Y
  let Ls := UnreducedSuspension.lowerHemisphere Y
  have hLmem (z : H) : L 1 z ∈ Ls := by
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => exact Or.inl rfl
      | inr yt =>
        refine Or.inr ⟨yt.1, tL 1 yt.2, ?_, rfl⟩
        change (1 - (1 : ℝ) / 2) * (yt.2 : ℝ) ≤ 1 / 2
        nlinarith [yt.2.property.2]
  have hRmem (z : H) : R 1 z ∈ Us := by
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => exact Or.inl rfl
      | inr yt =>
        refine Or.inr ⟨yt.1, tR 1 yt.2, ?_, rfl⟩
        change (1 : ℝ) / 2 ≤ 1 - (1 : ℝ) * (yt.2 : ℝ) / 2
        nlinarith [yt.2.property.2]
  let l : C(H, Ls) := ⟨fun z ↦ ⟨L 1 z, hLmem z⟩, (L 1).continuous.subtype_mk _⟩
  let r : C(H, Us) := ⟨fun z ↦ ⟨R 1 z, hRmem z⟩, (R 1).continuous.subtype_mk _⟩
  let iL : C(Ls, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let iU : C(Us, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let d := G 1
  let W := suspensionClutchingBundle n α
  let V := W.pullback d
  let Cₗ := suspensionClutchingLowerIso n α
  let Cᵣ := suspensionClutchingUpperIso n α
  -- Pull back the two original chart witnesses, with lower source and upper target.
  let eL : Iso ((DoubleSpace.leftMap T : H → D) *ᵖ V.Fiber)
      (FiniteBundle.trivial H n).Fiber :=
    (pullbackCompIso (E := W.Fiber) d (DoubleSpace.leftMap T)).trans
      ((pullbackCompIso (E := W.Fiber) iL l).symm.trans
        ((Cₗ.pullback l).trans (pullbackTrivialIso l n)))
  let eR : Iso ((DoubleSpace.rightMap T : H → D) *ᵖ V.Fiber)
      (FiniteBundle.trivial H n).Fiber :=
    (pullbackCompIso (E := W.Fiber) d (DoubleSpace.rightMap T)).trans
      ((pullbackCompIso (E := W.Fiber) iU r).symm.trans
        ((Cᵣ.pullback r).trans (pullbackTrivialIso r n)))
  have hinvComp (Z : Set S) (g : C(Z, S)) (k : C(H, Z))
      (z : H) (v : W.Fiber (g (k z))) :
      ((pullbackCompIso (E := W.Fiber) g k).linearEquiv z).symm v = v := by
    have h := (pullbackCompIso_apply (E := W.Fiber) g k z)
      (((pullbackCompIso (E := W.Fiber) g k).linearEquiv z).symm v)
    exact h.symm.trans (LinearEquiv.apply_symm_apply _ _)
  have heL (z : H) (v : V.Fiber (DoubleSpace.left T z)) :
      eL.linearEquiv z v = Cₗ.linearEquiv (l z) v := by
    change (pullbackTrivialIso l n).linearEquiv z
      (Cₗ.linearEquiv (l z)
        (((pullbackCompIso (E := W.Fiber) iL l).linearEquiv z).symm
          ((pullbackCompIso (E := W.Fiber) d (DoubleSpace.leftMap T)).linearEquiv z v))) = _
    erw [pullbackTrivialIso_apply, pullbackCompIso_apply, hinvComp]
  have heR (z : H) (v : V.Fiber (DoubleSpace.right T z)) :
      eR.linearEquiv z v = Cᵣ.linearEquiv (r z) v := by
    change (pullbackTrivialIso r n).linearEquiv z
      (Cᵣ.linearEquiv (r z)
        (((pullbackCompIso (E := W.Fiber) iU r).linearEquiv z).symm
          ((pullbackCompIso (E := W.Fiber) d (DoubleSpace.rightMap T)).linearEquiv z v))) = _
    erw [pullbackTrivialIso_apply, pullbackCompIso_apply, hinvComp]
  let j : C(T, Y) := ⟨e.symm, e.symm.continuous⟩
  let i : C(T, H) := ⟨Subtype.val, continuous_subtype_val⟩
  let t := pullbackTrivialIso i n
  let u := pullbackTrivialIso j n
  let γ : RelativeTriple (FiniteBundle.trivial H n).Fiber
      (FiniteBundle.trivial H n).Fiber T :=
    t.trans (u.symm.trans ((α.symm.pullback j).trans (u.trans t.symm)))
  let a := BundleTriple.ofBoundary (FiniteBundle.trivial H n) (FiniteBundle.trivial H n) γ
  have ht (x : T) (v : Fin n → ℂ) : t.linearEquiv x v = v :=
    pullbackTrivialIso_apply i n x v
  have hti (x : T) (v : Fin n → ℂ) : (t.linearEquiv x).symm v = v := by
    apply (t.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, ht]
  have hu (x : T) (v : Fin n → ℂ) : u.linearEquiv x v = v :=
    pullbackTrivialIso_apply j n x v
  have hui (x : T) (v : Fin n → ℂ) : (u.linearEquiv x).symm v = v := by
    apply (u.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, hu]
  have hγ (x : T) (v : Fin n → ℂ) :
      γ.linearEquiv x v = (α.linearEquiv (e.symm x)).symm v := by
    change (t.linearEquiv x).symm (u.linearEquiv x
      ((α.linearEquiv (j x)).symm ((u.linearEquiv x).symm (t.linearEquiv x v)))) = _
    rw [ht, hui, hu, hti]
    rfl
  -- At the original top both pulled-back chart points are the same equator point.
  have htop (x : T) : (x : H) = mappingCylinderTop f (e.symm x) := by
    exact (congrArg Subtype.val (e.apply_symm_apply x)).symm
  have hlTop (x : T) : (l x).val = UnreducedSuspension.equator Y (e.symm x) := by
    change L 1 x = _
    rw [htop x]
    change UnreducedSuspension.of (e.symm x) (tL 1 1) = _
    congr 1
    exact Subtype.ext (by norm_num [tL, UnreducedSuspension.equator])
  have hrTop (x : T) : (r x).val = UnreducedSuspension.equator Y (e.symm x) := by
    change R 1 x = _
    rw [htop x]
    change UnreducedSuspension.of (e.symm x) (tR 1 1) = _
    congr 1
    exact Subtype.ext (by norm_num [tR, UnreducedSuspension.equator])
  have inverseSeam (y : Y) (p : Ls) (q : Us)
      (hp : p.val = UnreducedSuspension.equator Y y)
      (hq : q.val = UnreducedSuspension.equator Y y)
      (δ : p.val = q.val) (v : Fin n → ℂ) :
      Cᵣ.linearEquiv q (cast (congrArg W.Fiber δ) ((Cₗ.linearEquiv p).symm v)) =
        (α.linearEquiv y).symm v := by
    let zL : Ls := ⟨UnreducedSuspension.equator Y y, Or.inr ⟨y, _, le_rfl, rfl⟩⟩
    let zU : Us := ⟨UnreducedSuspension.equator Y y, Or.inr ⟨y, _, le_rfl, rfl⟩⟩
    have hp' : p = zL := Subtype.ext hp
    have hq' : q = zU := Subtype.ext hq
    subst p
    subst q
    change Cᵣ.linearEquiv zU ((Cₗ.linearEquiv zL).symm v) = _
    apply (α.linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := suspensionClutching_compatible n α y
      (Cᵣ.linearEquiv zU ((Cₗ.linearEquiv zL).symm v))
    change Cₗ.linearEquiv zL
      ((Cᵣ.linearEquiv zU).symm
        (Cᵣ.linearEquiv zU ((Cₗ.linearEquiv zL).symm v))) = _ at h
    erw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hcompatible : ClutchingCompatible a V eL eR := by
    intro x v
    have he : eL.linearEquiv x = Cₗ.linearEquiv (l x) :=
      LinearEquiv.ext (heL x)
    change eR.linearEquiv x
      (cast (congrArg V.Fiber (DoubleSpace.left_eq_right T x))
        ((eL.linearEquiv x).symm v)) = γ.linearEquiv x v
    erw [heR, hγ, he]
    exact inverseSeam (e.symm x) (l x) (r x) (hlTop x) (hrTop x)
      (congrArg d (DoubleSpace.left_eq_right T x)) v
  obtain ⟨hglue⟩ := nonempty_clutching_iso hT a V eL eR hcompatible
  let := isFiniteRank_pullback (E := W.Fiber) d
  let := isFiniteRank_pullback (E := (FiniteBundle.trivial S n).Fiber) d
  let := isFiniteRank_pullback (E := (FiniteBundle.trivial H n).Fiber)
    (DoubleSpace.projMap T)
  have hdTrivial : complexKZeroPullback d (FiniteBundle.trivial S n).kZeroClass =
      (FiniteBundle.trivial D n).kZeroClass := by
    erw [← kZeroClass_pullback]
    exact kZeroClass_eq_of_iso (pullbackTrivialIso d n)
  have hpTrivial : complexKZeroPullback (DoubleSpace.projMap T)
      (FiniteBundle.trivial H n).kZeroClass = (FiniteBundle.trivial D n).kZeroClass := by
    erw [← kZeroClass_pullback]
    exact kZeroClass_eq_of_iso (pullbackTrivialIso (DoubleSpace.projMap T) n)
  have hclass : complexKZeroPullback d (suspensionClutchingClass n α).val =
      a.doubleDifference hT := by
    change complexKZeroPullback d
      (W.kZeroClass - (FiniteBundle.trivial S n).kZeroClass) =
        (clutchingBundle hT a).kZeroClass -
          complexKZeroPullback (DoubleSpace.projMap T) (FiniteBundle.trivial H n).kZeroClass
    erw [map_sub, hdTrivial, hpTrivial, ← kZeroClass_pullback]
    exact congrArg (fun b : ComplexKZero D ↦ b - (FiniteBundle.trivial D n).kZeroClass)
      (kZeroClass_eq_of_iso hglue)
  -- The original class is also reduced at the north pole, even for an empty Y.
  have hnorth : (suspensionClutchingClass n α).val ∈
      reducedComplexKZero (UnreducedSuspension.north (X := Y)) := by
    let p := UnreducedSuspension.north (X := Y)
    change kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ p).toRingHom
      (W.kZeroClass - (FiniteBundle.trivial S n).kZeroClass) = 0
    apply (kZeroRank_bijective ℂ).1
    rw [map_zero]
    change complexKZeroRankAt p
      (kZeroClass W.Fiber - kZeroClass (Bundle.Trivial S (Fin n → ℂ))) = 0
    rw [map_sub, rankAt_kZeroClass, rankAt_kZeroClass]
    have hdim := (Cᵣ.linearEquiv ⟨p, Or.inl rfl⟩).finrank_eq
    exact sub_eq_zero.mpr (congrArg (fun k : ℕ ↦ (k : ℤ)) hdim)
  let c : RelativeKZero T hT := reducedComplexKZeroPullback
    (mappingConeTip f) (UnreducedSuspension.north (X := Y)) (puppeConeCollapse f) rfl
      ⟨(suspensionClutchingClass n α).val, hnorth⟩
  have hQpull : complexKZeroPullback Q c.val = a.doubleDifference hT := by
    change complexKZeroPullback Q
      (complexKZeroPullback (puppeConeCollapse f) (suspensionClutchingClass n α).val) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      complexKZeroPullback_eq_of_homotopy _ _ homotopy]
    exact hclass
  -- Retain all relative information by excision through the double-right retract pair.
  let R₀ := DoubleSpace.rightRange T
  have hR₀ : IsClosed R₀ := DoubleSpace.isClosed_rightRange T hT
  let := PointedQuotient.t2Space R₀ hR₀
  let k : C(PointedQuotient T, PointedQuotient R₀) :=
    PointedQuotient.mapContinuous T R₀ (DoubleSpace.leftMap T) (DoubleSpace.left_mapsTo T)
  let qR : C(D, PointedQuotient R₀) :=
    ⟨PointedQuotient.of R₀, PointedQuotient.continuous_of R₀⟩
  have hquotient : k.comp Q = qR := by
    ext z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => rfl
      | inr x =>
        exact ((PointedQuotient.of_eq_basepoint_iff R₀ (DoubleSpace.right T x)).mpr
          ⟨x, rfl⟩).symm
  have hlift (v : RelativeKZero T hT) (b : RelativeKZero R₀ hR₀)
      (hb : DoubleSpace.relativeRestriction T hT b = v) :
      complexKZeroPullback Q v.val = relativeKZeroForget R₀ hR₀ b := by
    rw [← hb]
    change complexKZeroPullback Q (complexKZeroPullback k b.val) =
      complexKZeroPullback qR b.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hquotient]
  obtain ⟨b, hb⟩ := (DoubleSpace.relativeRestriction_bijective T hT).surjective c
  have hforgot : relativeKZeroForget R₀ hR₀ b =
      relativeKZeroForget R₀ hR₀ (a.differenceLift hT) := by
    rw [← hlift c b hb, hQpull, a.forget_differenceLift hT]
  have hrelative : c = a.relativeClass hT := by
    have hsame := relativeKZeroForget_injective_of_retraction R₀ hR₀
      (DoubleSpace.rightRetraction T) (DoubleSpace.rightRetraction_apply T) hforgot
    exact hb.symm.trans (congrArg (DoubleSpace.relativeRestriction T hT) hsame)
  -- The boundary generator is the original inverse automorphism in fixed coordinates.
  let B : BundleAutomorphism Y := ⟨FiniteBundle.trivial Y n, α⟩
  have hconjugate : (B.inverse.pullback j).IsIsomorphic
      ⟨(FiniteBundle.trivial H n).restrict T, γ⟩ := by
    refine ⟨u.trans t.symm, ?_⟩
    intro x v
    change (t.linearEquiv x).symm (u.linearEquiv x ((α.linearEquiv (j x)).symm v)) =
      γ.linearEquiv x ((t.linearEquiv x).symm (u.linearEquiv x v))
    erw [hu, hti, hγ, hu, hti]
    rfl
  have hboundary : a.relativeClass hT =
      -bundleKMinusOneBoundary T hT (bundleKMinusOnePullback j B.kMinusOneClass) := by
    change (BundleTriple.ofBoundary (FiniteBundle.trivial H n)
      (FiniteBundle.trivial H n) γ).relativeClass hT = _
    rw [← bundleKMinusOneBoundary_restricted,
      ← BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hconjugate,
      ← bundleKMinusOnePullback_class, BundleAutomorphism.kMinusOneClass_inverse,
      map_neg, map_neg]
  exact congrArg Subtype.val (hrelative.trans hboundary)

end MappingCylinder

variable {X}

/-- KA II.4.9 with the explicit sign between the fixed half-ray and cylinder conventions. -/
theorem compactSupportKBoundary_comp_clutching_eq_neg_boundary
    (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    (compactSupportKZeroDegreeEquiv (Aᶜ : Set X)).toAddMonoidHom.comp
        ((compactSupportKBoundary 0 A hA).comp
          (compactSupportBundleKMinusOneDegreeOneEquiv A).toAddMonoidHom) =
      -compactSupportBundleKMinusOneBoundary A hA := by
  /- Use proper naturality of the supported automorphism boundary at the
  cylinder's closed attaching seam. Its complement splits into clopen base
  and tube pieces. The proper bottom map gives the original boundary on A;
  the proper half-ray map gives the original suspension on the tube. Extend
  the chosen increasing tube parameter to the closed ray and check the same
  map at every positive point, so its orientation is retained exactly.
  Clopen reconstruction identifies the seam-boundary class from those two
  restrictions. Nested pointed collapses identify their global extensions;
  pair exactness says their sum is zero. Finally check the original Fin 0
  and Fin 1 degree coordinates and cancel the bijective base extension.
  The resulting tube-versus-base relation retains the displayed minus sign. -/
  classical

  have parameterExtension (p : ℝ ≃o Set.Ioo (0 : ℝ) 1) :
      ∃ e : NNReal ≃ₜ Set.Ico (0 : ℝ) 1,
        (e 0).val = 0 ∧
          ∀ t : ℝ, (e ⟨Real.exp t, (Real.exp_pos t).le⟩).val = (p t).val := by
    classical
    let F : NNReal → Set.Ico (0 : ℝ) 1 := fun r ↦
      if hr : r = 0 then ⟨0, le_rfl, zero_lt_one⟩
      else ⟨(p (Real.log (r : ℝ))).val,
        (p (Real.log (r : ℝ))).property.1.le,
        (p (Real.log (r : ℝ))).property.2⟩
    have hF : StrictMono F := by
      intro r s hrs
      have hs : s ≠ 0 := ne_of_gt ((show 0 ≤ r from zero_le).trans_lt hrs)
      by_cases hr : r = 0
      · change (F r).val < (F s).val
        simp only [F, hr, hs, ↓reduceDIte]
        exact (p (Real.log (s : ℝ))).property.1
      · change (F r).val < (F s).val
        simp only [F, hr, hs, ↓reduceDIte]
        exact p.strictMono (Real.log_lt_log (by exact_mod_cast pos_iff_ne_zero.mpr hr)
          (by exact_mod_cast hrs))
    let G : Set.Ico (0 : ℝ) 1 → NNReal := fun t ↦
      if ht : t.val = 0 then 0
      else ⟨Real.exp (p.symm ⟨t.val, lt_of_le_of_ne t.property.1 (Ne.symm ht),
        t.property.2⟩), (Real.exp_pos _).le⟩
    have hFG : Function.RightInverse G F := by
      intro t
      by_cases ht : t.val = 0
      · apply Subtype.ext
        simp [G, ht, F]
      · have hexp : (⟨Real.exp (p.symm ⟨t.val, lt_of_le_of_ne t.property.1 (Ne.symm ht),
            t.property.2⟩), (Real.exp_pos _).le⟩ : NNReal) ≠ 0 := by
          exact NNReal.coe_ne_zero.mp (Real.exp_ne_zero _)
        apply Subtype.ext
        simp only [G, ht, ↓reduceDIte]
        dsimp only [F]
        split_ifs with hz
        · exact (hexp hz).elim
        · change (p (Real.log (Real.exp (p.symm
            ⟨t.val, lt_of_le_of_ne t.property.1 (Ne.symm ht), t.property.2⟩)))).val = t.val
          rw [Real.log_exp]
          exact congrArg Subtype.val (p.apply_symm_apply _)
    let e := (StrictMono.orderIsoOfRightInverse F hF G hFG).toHomeomorph
    refine ⟨e, ?_, ?_⟩
    · change (F 0).val = 0
      simp [F]
    · intro t
      have ht : (⟨Real.exp t, (Real.exp_pos t).le⟩ : NNReal) ≠ 0 := by
        exact NNReal.coe_ne_zero.mp (Real.exp_ne_zero _)
      change (F ⟨Real.exp t, (Real.exp_pos t).le⟩).val = (p t).val
      dsimp only [F]
      split_ifs with hz
      · exact (ht hz).elim
      · change (p (Real.log (Real.exp t))).val = (p t).val
        rw [Real.log_exp]
  have boundaryNaturalOfPreimageEq {P Q : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      (A : Set Q) (hA : IsClosed A)
      (f : C(P, Q)) (hf : IsProperMap f) (B : Set P) (hB : IsClosed B)
      (hpre : f ⁻¹' A = B) (g : C(B, A)) (hg : IsProperMap g)
      (j : C((Bᶜ : Set P), (Aᶜ : Set Q))) (hj : IsProperMap j)
      (hgval : ∀ b : B, (g b).val = f b.val)
      (hjval : ∀ b : (Bᶜ : Set P), (j b).val = f b.val) :
      letI := hA.locallyCompactSpace
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := hB.locallyCompactSpace
      letI := hB.isOpen_compl.locallyCompactSpace
      (compactSupportKZeroPullback j hj).comp
          (ComplexBundle.compactSupportBundleKMinusOneBoundary A hA) =
        (ComplexBundle.compactSupportBundleKMinusOneBoundary B hB).comp
          (ComplexBundle.compactSupportBundleKMinusOnePullback g hg) := by
    subst B
    have hg' : g = preimageSubspaceMap A f := by
      ext b
      exact hgval b
    have hj' : j = preimageSubspaceMap (Aᶜ : Set Q) f := by
      ext b
      exact hjval b
    subst g
    subst j
    exact ComplexBundle.compactSupportBundleKMinusOneBoundary_natural A hA f hf
  have clopenReconstruction {P : Type _} [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      (U : Set P) (hUo : IsOpen U) (hUc : IsClosed U) :
      letI := hUo.locallyCompactSpace
      letI := hUc.isOpen_compl.locallyCompactSpace
      ∀ a : CompactSupportKZero P,
        a = compactSupportKZeroOpenExtension U hUo
            (compactSupportKZeroPullback
              (⟨Subtype.val, continuous_subtype_val⟩ : C(U, P))
              hUc.isClosedEmbedding_subtypeVal.isProperMap a) +
          compactSupportKZeroOpenExtension Uᶜ hUc.isOpen_compl
            (compactSupportKZeroPullback
              (⟨Subtype.val, continuous_subtype_val⟩ : C((Uᶜ : Set P), P))
              hUo.isClosed_compl.isClosedEmbedding_subtypeVal.isProperMap a) := by
    classical
    let := hUo.locallyCompactSpace
    let := hUc.isOpen_compl.locallyCompactSpace
    -- A clopen restriction retracts its own actual collapse extension at infinity too.
    have retract (V : Set P) (hVo : IsOpen V) (hVc : IsClosed V) :
        letI := hVo.locallyCompactSpace
        ∀ b : CompactSupportKZero V,
          compactSupportKZeroPullback
            (⟨Subtype.val, continuous_subtype_val⟩ : C(V, P))
            hVc.isClosedEmbedding_subtypeVal.isProperMap
            (compactSupportKZeroOpenExtension V hVo b) = b := by
      let := hVo.locallyCompactSpace
      intro b
      let i : C(V, P) := ⟨Subtype.val, continuous_subtype_val⟩
      let hp := hVc.isClosedEmbedding_subtypeVal.isProperMap
      let j := properOnePointMap i hp
      let c : C(OnePoint P, OnePoint V) :=
        ⟨onePointCollapse V, continuous_onePointCollapse V hVo⟩
      have hci : c.comp j = ContinuousMap.id (OnePoint V) := by
        ext z
        cases z using OnePoint.rec with
        | infty => rfl
        | coe x =>
          change onePointCollapse V (OnePoint.map i x) = (x : OnePoint V)
          rw [OnePoint.map_some]
          change onePointCollapse V (x.val : OnePoint P) = (x : OnePoint V)
          exact onePointCollapse_coe_of_mem V x.val x.property
      apply Subtype.ext
      change complexKZeroPullback j (complexKZeroPullback c b.val) = b.val
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hci]
      change kZeroMap (RingHom.id _) b.val = b.val
      rw [kZeroMap_id]
      rfl
    let eU := compactSupportKZeroOpenExtension U hUo
    let eV := compactSupportKZeroOpenExtension Uᶜ hUc.isOpen_compl
    let rU := compactSupportKZeroPullback
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, P))
      hUc.isClosedEmbedding_subtypeVal.isProperMap
    let rV := compactSupportKZeroPullback
      (⟨Subtype.val, continuous_subtype_val⟩ : C((Uᶜ : Set P), P))
      hUo.isClosed_compl.isClosedEmbedding_subtypeVal.isProperMap
    have hseq : eV.range = rU.ker :=
      ComplexBundle.range_compactSupportKZeroOpenExtension U hUc
    have hseq' : eU.range = rV.ker := by
      have transport (W : Set P) (hW : IsOpen W) (hWU : W = U) :
          (compactSupportKZeroOpenExtension W hW).range = rV.ker →
            eU.range = rV.ker := by
        subst W
        exact id
      exact transport _ _ (compl_compl U)
        (ComplexBundle.range_compactSupportKZeroOpenExtension Uᶜ hUo.isClosed_compl)
    intro a
    -- Subtract the U part. Independent pair exactness puts the remainder on U-complement.
    have hz : rU (a - eU (rU a)) = 0 := by
      rw [map_sub, retract U hUo hUc, sub_self]
    obtain ⟨b, hb⟩ := hseq.ge hz
    -- The other exactness relation kills the crossed restriction; retraction identifies b.
    have hcross : rV (eU (rU a)) = 0 := hseq'.le ⟨rU a, rfl⟩
    have hb' : b = rV a := by
      have h := congrArg rV hb
      rw [map_sub, hcross, sub_zero] at h
      simpa only [rV, eV, retract Uᶜ hUc.isOpen_compl hUo.isClosed_compl] using h
    change a = eU (rU a) + eV (rV a)
    rw [← hb', hb]
    abel
  have nestedExtensionForPiece {P : Type _} [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      (U V : Set P) (hU : IsOpen U) (hV : IsOpen V)
      (C : Set V) (hC : IsOpen C) (hUV : U ⊆ V)
      (hCmem : ∀ v : V, v ∈ C ↔ v.val ∈ U) (e : U ≃ₜ C)
      (he : ∀ c : C, (e.symm c).val = c.val.val) :
      letI := hU.locallyCompactSpace
      letI := hV.locallyCompactSpace
      letI := hC.locallyCompactSpace
      ∀ a : CompactSupportKZero U,
        compactSupportKZeroOpenExtension V hV
          (compactSupportKZeroOpenExtension C hC (compactSupportKZeroHomeomorph e a)) =
          compactSupportKZeroOpenExtension U hU a := by
    classical
    let := hU.locallyCompactSpace
    let := hV.locallyCompactSpace
    let := hC.locallyCompactSpace
    let cU : C(OnePoint P, OnePoint U) :=
      ⟨onePointCollapse U, continuous_onePointCollapse U hU⟩
    let cV : C(OnePoint P, OnePoint V) :=
      ⟨onePointCollapse V, continuous_onePointCollapse V hV⟩
    let cC : C(OnePoint V, OnePoint C) :=
      ⟨onePointCollapse C, continuous_onePointCollapse C hC⟩
    let p := properOnePointMap (⟨e.symm, e.symm.continuous⟩ : C(C, U)) e.symm.isProperMap
    have hmap : p.comp (cC.comp cV) = cU := by
      ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe z =>
        by_cases hzU : z ∈ U
        · have hzV := hUV hzU
          have hzC : (⟨z, hzV⟩ : V) ∈ C := (hCmem _).2 hzU
          change OnePoint.map e.symm (onePointCollapse C (onePointCollapse V (z : OnePoint P))) =
            onePointCollapse U (z : OnePoint P)
          rw [onePointCollapse_coe_of_mem V z hzV,
            onePointCollapse_coe_of_mem C ⟨z, hzV⟩ hzC, OnePoint.map_some,
            onePointCollapse_coe_of_mem U z hzU]
          exact congrArg ((↑) : U → OnePoint U) (Subtype.ext (he ⟨⟨z, hzV⟩, hzC⟩))
        · by_cases hzV : z ∈ V
          · have hzC : (⟨z, hzV⟩ : V) ∉ C := fun hc ↦ hzU ((hCmem _).1 hc)
            change OnePoint.map e.symm
                (onePointCollapse C (onePointCollapse V (z : OnePoint P))) =
              onePointCollapse U (z : OnePoint P)
            rw [onePointCollapse_coe_of_mem V z hzV,
              onePointCollapse_coe_of_notMem C ⟨z, hzV⟩ hzC, OnePoint.map_infty,
              onePointCollapse_coe_of_notMem U z hzU]
          · change OnePoint.map e.symm
                (onePointCollapse C (onePointCollapse V (z : OnePoint P))) =
              onePointCollapse U (z : OnePoint P)
            rw [onePointCollapse_coe_of_notMem V z hzV, onePointCollapse_infty,
              OnePoint.map_infty, onePointCollapse_coe_of_notMem U z hzU]
    intro a
    apply Subtype.ext
    change complexKZeroPullback cV
        (complexKZeroPullback cC (complexKZeroPullback p a.val)) =
      complexKZeroPullback cU a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  have degreeZero_homeomorph {P Q : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      (e : P ≃ₜ Q) (a : CompactSupportK 0 P) :
      compactSupportKZeroDegreeEquiv Q (compactSupportKHomeomorphEquiv 0 e a) =
        compactSupportKZeroHomeomorph e (compactSupportKZeroDegreeEquiv P a) := by
    -- Inverse proper pullback retains exactly the original empty real tuple.
    exact compactSupportKZeroDegreeEquiv_pullback
      (⟨e.symm, e.symm.continuous⟩ : C(Q, P)) e.symm.isProperMap a
  have boundaryBase_zeroDegree (A : Set X) (hA : IsClosed A) :
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      letI := (isOpen_boundaryCylinderBaseOpen A hA).locallyCompactSpace
      ∀ b : CompactSupportK 0 (Aᶜ : Set X),
        compactSupportKZeroDegreeEquiv (BoundaryCylinder A)
            (compactSupportKBoundaryBase 0 A hA b) =
          compactSupportKZeroOpenExtension (boundaryCylinderBaseOpen A)
            (isOpen_boundaryCylinderBaseOpen A hA)
            (compactSupportKZeroHomeomorph (boundaryCylinderBaseHomeomorph A)
              (compactSupportKZeroDegreeEquiv (Aᶜ : Set X) b)) := by
    let := hA.isOpen_compl.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let := (isOpen_boundaryCylinderBaseOpen A hA).locallyCompactSpace
    intro b
    change compactSupportKZeroDegreeEquiv (BoundaryCylinder A)
        (compactSupportKOpenExtension 0 _ (isOpen_boundaryCylinderBaseOpen A hA)
          (compactSupportKHomeomorphEquiv 0 (boundaryCylinderBaseHomeomorph A) b)) = _
    rw [compactSupportKZeroDegreeEquiv_openExtension, degreeZero_homeomorph]
  have coordinate_zeroDegree (A : Set X) (hA : IsClosed A) :
      letI := hA.locallyCompactSpace
      ∀ a : ComplexBundle.CompactSupportBundleKMinusOne A,
        compactSupportKZeroDegreeEquiv (A × ℝ)
            (compactSupportKZeroHomeomorph (suspensionCoordinateHomeomorph A 0).symm
              (ComplexBundle.compactSupportBundleKMinusOneDegreeOneEquiv A a)) =
          ComplexBundle.compactSupportBundleKMinusOneSuspension A a := by
    let := hA.locallyCompactSpace
    intro a
    let p := Homeomorph.prodUnique (A × ℝ) (Fin 0 → ℝ)
    let c := suspensionCoordinateHomeomorph A 0
    let t := (Homeomorph.refl A).prodCongr (Homeomorph.funUnique (Fin 1) ℝ).symm
    let j : C(A × ℝ, (A × ℝ) × (Fin 0 → ℝ)) := ⟨p.symm, p.symm.continuous⟩
    let k : C((A × ℝ) × (Fin 0 → ℝ), A × (Fin 1 → ℝ)) := ⟨c, c.continuous⟩
    let h : C(A × (Fin 1 → ℝ), A × ℝ) := ⟨t.symm, t.symm.continuous⟩
    have hmap : h.comp (k.comp j) = ContinuousMap.id (A × ℝ) := by
      -- vecCons inserts the same scalar as the sole Fin 1 coordinate; no Bott choice enters.
      ext z <;> rfl
    change compactSupportKZeroPullback j p.symm.isProperMap
        (compactSupportKZeroPullback k c.isProperMap
          (compactSupportKZeroPullback h t.symm.isProperMap
            (ComplexBundle.compactSupportBundleKMinusOneSuspension A a))) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    simp only [hmap, compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  have boundaryTube_zeroDegree (A : Set X) (hA : IsClosed A) :
      letI := hA.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      letI := (isOpen_boundaryCylinderTubeOpen A).locallyCompactSpace
      ∀ a : ComplexBundle.CompactSupportBundleKMinusOne A,
        compactSupportKZeroDegreeEquiv (BoundaryCylinder A)
            (compactSupportKBoundaryTube 0 A hA
              (ComplexBundle.compactSupportBundleKMinusOneDegreeOneEquiv A a)) =
          compactSupportKZeroOpenExtension (boundaryCylinderTubeOpen A)
            (isOpen_boundaryCylinderTubeOpen A)
            (compactSupportKZeroHomeomorph (boundaryCylinderTubeHomeomorph A)
              (ComplexBundle.compactSupportBundleKMinusOneSuspension A a)) := by
    let := hA.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let := (isOpen_boundaryCylinderTubeOpen A).locallyCompactSpace
    intro a
    change compactSupportKZeroDegreeEquiv (BoundaryCylinder A)
        (compactSupportKOpenExtension 0 _ (isOpen_boundaryCylinderTubeOpen A)
          (compactSupportKHomeomorphEquiv 0 (boundaryCylinderTubeHomeomorph A)
            (compactSupportKZeroHomeomorph (suspensionCoordinateHomeomorph A 0).symm
              (ComplexBundle.compactSupportBundleKMinusOneDegreeOneEquiv A a)))) = _
    rw [compactSupportKZeroDegreeEquiv_openExtension, degreeZero_homeomorph,
      coordinate_zeroDegree A hA]
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let := locallyCompactSpace_boundaryCylinder A hA
  -- Stage 1: use the closed attaching seam and the actual proper bottom map.
  let Z := BoundaryCylinder A
  let S : Set Z := {z | z.val.1 ∈ A ∧ z.val.2 = 0}
  have hS : IsClosed S := (hA.preimage continuous_subtype_val.fst).inter
    (isClosed_eq continuous_subtype_val.snd continuous_const)
  let W := Sᶜ
  let := hS.locallyCompactSpace
  let := hS.isOpen_compl.locallyCompactSpace
  let eS : A ≃ₜ S := {
    toFun := fun x ↦ ⟨⟨(x.val, 0), le_rfl, zero_lt_one, Or.inl rfl⟩, x.property, rfl⟩
    invFun := fun z ↦ ⟨z.val.val.1, z.property.1⟩
    left_inv := fun _ ↦ rfl
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl z.property.2.symm
    continuous_toFun := by fun_prop
    continuous_invFun :=
      ((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).fst.comp
        continuous_subtype_val).subtype_mk _ }
  let D : Set Z := {z | z.val.2 = 0}
  have hD : IsClosed D := isClosed_eq continuous_subtype_val.snd continuous_const
  let := hD.locallyCompactSpace
  let eD : X ≃ₜ D := {
    toFun := fun x ↦ ⟨⟨(x, 0), le_rfl, zero_lt_one, Or.inl rfl⟩, rfl⟩
    invFun := fun z ↦ z.val.val.1
    left_inv := fun _ ↦ rfl
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl z.property.symm
    continuous_toFun := by fun_prop
    continuous_invFun :=
      (continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).fst.comp
        continuous_subtype_val }
  let bottom : C(X, Z) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(D, Z)).comp ⟨eD, eD.continuous⟩
  have hbottom : IsProperMap bottom := hD.isProperMap_subtypeVal.comp eD.isProperMap
  -- Stage 2: its complement splits into the original base and tube pieces.
  let B : Set W := {w | w.val.val.1 ∉ A}
  have hBo : IsOpen B := (isOpen_boundaryCylinderBaseOpen A hA).preimage
    continuous_subtype_val
  have hBeq : B = {w : W | w.val.val.2 = 0} := by
    ext w
    constructor
    · intro hw
      exact w.val.property.2.2.resolve_right hw
    · intro hw ha
      exact w.property ⟨ha, hw⟩
  have hBc : IsClosed B := by
    rw [hBeq]
    exact isClosed_eq
      ((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).snd.comp
        continuous_subtype_val) continuous_const
  let := hBo.locallyCompactSpace
  let := hBc.isOpen_compl.locallyCompactSpace
  let eB : (Aᶜ : Set X) ≃ₜ B := {
    toFun := fun x ↦ ⟨⟨⟨(x.val, 0), le_rfl, zero_lt_one, Or.inl rfl⟩,
      fun hs ↦ x.property hs.1⟩, x.property⟩
    invFun := fun w ↦ ⟨w.val.val.val.1, w.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := by
      intro w
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl ((Set.ext_iff.mp hBeq w.val).mp w.property).symm
    continuous_toFun := by fun_prop
    continuous_invFun :=
      ((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).fst.comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _ }
  let jB : C((Aᶜ : Set X), W) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(B, W)).comp ⟨eB, eB.continuous⟩
  have hjB : IsProperMap jB := hBc.isProperMap_subtypeVal.comp eB.isProperMap
  have hTubeOfNotBase (w : (Bᶜ : Set W)) :
      w.val.val ∈ boundaryCylinderTubeOpen A := by
    have ha : w.val.val.val.1 ∈ A := by
      have hn : ¬ w.val.val.val.1 ∉ A := w.property
      exact not_not.mp hn
    have hn : w.val.val.val.2 ≠ 0 := fun ht ↦ w.val.property ⟨ha, ht⟩
    exact lt_of_le_of_ne w.val.val.property.1 (Ne.symm hn)
  let eWTube : (boundaryCylinderTubeOpen A) ≃ₜ (Bᶜ : Set W) := {
    toFun := fun z ↦ ⟨⟨z.val, fun hs ↦ (ne_of_gt z.property) hs.2⟩,
      fun hb ↦ hb (z.val.property.2.2.resolve_left (ne_of_gt z.property))⟩
    invFun := fun w ↦ ⟨w.val.val, hTubeOfNotBase w⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      hTubeOfNotBase }
  let := (isOpen_boundaryCylinderTubeOpen A).locallyCompactSpace
  let eT := (boundaryCylinderTubeHomeomorph A).trans eWTube
  let jT : C(A × ℝ, W) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C((Bᶜ : Set W), W)).comp ⟨eT, eT.continuous⟩
  have hjT : IsProperMap jT := hBo.isClosed_compl.isProperMap_subtypeVal.comp eT.isProperMap
  -- Stage 3: proper naturality recovers the original positive base boundary.
  let sMap : C(A, S) := ⟨eS, eS.continuous⟩
  have hpreBottom : bottom ⁻¹' S = A := by
    ext x
    change (x ∈ A ∧ (0 : ℝ) = 0) ↔ x ∈ A
    simp
  have hnB := boundaryNaturalOfPreimageEq S hS bottom hbottom A hA hpreBottom
    sMap eS.isProperMap jB hjB (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hSretract (a : ComplexBundle.CompactSupportBundleKMinusOne A) :
      ComplexBundle.compactSupportBundleKMinusOnePullback sMap eS.isProperMap
          (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a) = a := by
    change ComplexBundle.compactSupportBundleKMinusOnePullback sMap eS.isProperMap
      (ComplexBundle.compactSupportBundleKMinusOnePullback
        ⟨eS.symm, eS.symm.continuous⟩ eS.symm.isProperMap a) = a
    rw [← AddMonoidHom.comp_apply,
      ← ComplexBundle.compactSupportBundleKMinusOnePullback_comp]
    have hid : (⟨eS.symm, eS.symm.continuous⟩ : C(S, A)).comp sMap =
        ContinuousMap.id A := by
      apply ContinuousMap.ext
      intro x
      exact eS.symm_apply_apply x
    simpa only [hid, AddMonoidHom.id_apply] using DFunLike.congr_fun
      (ComplexBundle.compactSupportBundleKMinusOnePullback_id (X := A)) a
  have hbaseBoundary (a : ComplexBundle.CompactSupportBundleKMinusOne A) :
      compactSupportKZeroPullback jB hjB
          (ComplexBundle.compactSupportBundleKMinusOneBoundary S hS
            (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a)) =
        ComplexBundle.compactSupportBundleKMinusOneBoundary A hA a := by
    have hn := DFunLike.congr_fun hnB
      (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a)
    change _ = ComplexBundle.compactSupportBundleKMinusOneBoundary A hA
      (ComplexBundle.compactSupportBundleKMinusOnePullback sMap eS.isProperMap
        (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a)) at hn
    simpa only [AddMonoidHom.comp_apply, hSretract] using hn
  -- Stage 4: extend the original increasing tube parameter along the half-ray.
  let affine := affineHomeomorph (1 / 2 : ℝ) (1 / 2) (by norm_num)
  let interval : Set.Ioo (-1 : ℝ) 1 ≃ₜ Set.Ioo (0 : ℝ) 1 := affine.subtype (by
    intro t
    change (-1 < t ∧ t < 1) ↔ (0 < 1 / 2 * t + 1 / 2 ∧ 1 / 2 * t + 1 / 2 < 1)
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2])
  let p := (orderIsoIooNegOneOne ℝ).toHomeomorph.trans interval
  have hp : StrictMono p := by
    intro x y hxy
    change 1 / 2 * ((orderIsoIooNegOneOne ℝ) x).val + 1 / 2 <
      1 / 2 * ((orderIsoIooNegOneOne ℝ) y).val + 1 / 2
    have ho : ((orderIsoIooNegOneOne ℝ) x).val <
        ((orderIsoIooNegOneOne ℝ) y).val := (orderIsoIooNegOneOne ℝ).strictMono hxy
    linarith [ho]
  let po := StrictMono.orderIsoOfRightInverse p hp p.symm p.apply_symm_apply
  obtain ⟨ray, hray0, hrayexp⟩ := parameterExtension po
  let C : Set Z := {z | z.val.1 ∈ A}
  have hC : IsClosed C := hA.preimage continuous_subtype_val.fst
  let := hC.locallyCompactSpace
  let eRay : (A × NNReal) ≃ₜ C := {
    toFun := fun q ↦ ⟨⟨(q.1.val, (ray q.2).val), (ray q.2).property.1,
      (ray q.2).property.2, Or.inr q.1.property⟩, q.1.property⟩
    invFun := fun z ↦ (⟨z.val.val.1, z.property⟩,
      ray.symm ⟨z.val.val.2, z.val.property.1, z.val.property.2.1⟩)
    left_inv := by
      intro q
      exact Prod.ext rfl (ray.symm_apply_apply q.2)
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (congrArg Subtype.val (ray.apply_symm_apply _))
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (ray.continuous.comp continuous_snd))
    continuous_invFun := by
      apply Continuous.prodMk
      · exact ((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).fst.comp
          continuous_subtype_val).subtype_mk _
      · exact ray.symm.continuous.comp
          (((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).snd.comp
            continuous_subtype_val).subtype_mk _) }
  let F : C(A × NNReal, Z) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(C, Z)).comp ⟨eRay, eRay.continuous⟩
  have hF : IsProperMap F := hC.isProperMap_subtypeVal.comp eRay.isProperMap
  let E := halfRayZeroSection A
  have hE : IsClosed E := isClosed_halfRayZeroSection A
  let := hE.locallyCompactSpace
  let := hE.isOpen_compl.locallyCompactSpace
  let eZero := halfRayZeroSectionHomeomorph A
  let eES := eZero.symm.trans eS
  let g : C(E, S) := ⟨eES, eES.continuous⟩
  let half := halfRayComplementHomeomorph A
  let k : C((Eᶜ : Set (A × NNReal)), W) := jT.comp ⟨half, half.continuous⟩
  have hk : IsProperMap k := hjT.comp half.isProperMap
  have hpreRay : F ⁻¹' S = E := by
    ext q
    change (q.1.val ∈ A ∧ (ray q.2).val = 0) ↔ q.2 = 0
    constructor
    · intro hq
      apply ray.injective
      exact Subtype.ext (hq.2.trans hray0.symm)
    · intro hq
      exact ⟨q.1.property, by rw [hq]; exact hray0⟩
  have hgval (q : E) : (g q).val = F q.val := by
    apply Subtype.ext
    exact Prod.ext rfl (by change 0 = (ray q.val.2).val; rw [q.property]; exact hray0.symm)
  -- At each positive ray point, hrayexp checks the original tube parameter exactly.
  -- This is equality of the chosen maps, including their retained orientation.
  have hkval (q : (Eᶜ : Set (A × NNReal))) : (k q).val = F q.val := by
    have hq : 0 < (q.val.2 : ℝ) := by
      exact lt_of_le_of_ne q.val.2.property (Ne.symm (NNReal.coe_ne_zero.mpr q.property))
    have hre : (⟨Real.exp (Real.log (q.val.2 : ℝ)),
        (Real.exp_pos _).le⟩ : NNReal) = q.val.2 := NNReal.eq (Real.exp_log hq)
    have hh := hrayexp (Real.log (q.val.2 : ℝ))
    rw [hre] at hh
    apply Subtype.ext
    exact Prod.ext rfl hh.symm
  have hnT := boundaryNaturalOfPreimageEq S hS F hF E hE hpreRay g eES.isProperMap k hk
    hgval hkval
  have hzeroSquare (a : ComplexBundle.CompactSupportBundleKMinusOne A) :
      ComplexBundle.compactSupportBundleKMinusOnePullback g eES.isProperMap
          (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a) =
        ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eZero a := by
    change ComplexBundle.compactSupportBundleKMinusOnePullback g eES.isProperMap
      (ComplexBundle.compactSupportBundleKMinusOnePullback
        ⟨eS.symm, eS.symm.continuous⟩ eS.symm.isProperMap a) =
      ComplexBundle.compactSupportBundleKMinusOnePullback
        ⟨eZero.symm, eZero.symm.continuous⟩ eZero.symm.isProperMap a
    rw [← AddMonoidHom.comp_apply,
      ← ComplexBundle.compactSupportBundleKMinusOnePullback_comp]
    have heq : (⟨eS.symm, eS.symm.continuous⟩ : C(S, A)).comp g =
        ⟨eZero.symm, eZero.symm.continuous⟩ := by
      apply ContinuousMap.ext
      intro q
      exact eS.symm_apply_apply (eZero.symm q)
    simp only [heq]
  have htubeBoundary (a : ComplexBundle.CompactSupportBundleKMinusOne A) :
      compactSupportKZeroPullback jT hjT
          (ComplexBundle.compactSupportBundleKMinusOneBoundary S hS
            (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a)) =
        ComplexBundle.compactSupportBundleKMinusOneSuspension A a := by
    apply (compactSupportKZeroHomeomorph_bijective half.symm).1
    have hn := DFunLike.congr_fun hnT
      (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a)
    simp only [AddMonoidHom.comp_apply] at hn
    rw [hzeroSquare] at hn
    change compactSupportKZeroPullback ⟨half, half.continuous⟩ half.isProperMap
      (compactSupportKZeroPullback jT hjT _) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    calc
      _ = ComplexBundle.compactSupportBundleKMinusOneBoundary E hE
          (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eZero a) := hn
      _ = compactSupportKZeroHomeomorph half.symm
          (compactSupportKZeroHomeomorph half
            (ComplexBundle.compactSupportBundleKMinusOneBoundary E hE
              (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eZero a))) :=
        (DFunLike.congr_fun (compactSupportKZeroHomeomorph_symm half) _).symm
      _ = _ := rfl
  -- Stage 5: clopen restrictions reconstruct the same seam-boundary class.
  let rB := compactSupportKZeroPullback
    (⟨Subtype.val, continuous_subtype_val⟩ : C(B, W)) hBc.isProperMap_subtypeVal
  let rT := compactSupportKZeroPullback
    (⟨Subtype.val, continuous_subtype_val⟩ : C((Bᶜ : Set W), W))
      hBo.isClosed_compl.isProperMap_subtypeVal
  have hrestrictB (z : CompactSupportKZero W) :
      compactSupportKZeroHomeomorph eB (compactSupportKZeroPullback jB hjB z) = rB z := by
    change compactSupportKZeroPullback ⟨eB.symm, eB.symm.continuous⟩ eB.symm.isProperMap
      (compactSupportKZeroPullback jB hjB z) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    have heq : jB.comp ⟨eB.symm, eB.symm.continuous⟩ =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(B, W)) := by
      apply ContinuousMap.ext
      intro b
      exact congrArg Subtype.val (eB.apply_symm_apply b)
    simp only [heq]
    rfl
  have hrestrictT (z : CompactSupportKZero W) :
      compactSupportKZeroHomeomorph eT (compactSupportKZeroPullback jT hjT z) = rT z := by
    change compactSupportKZeroPullback ⟨eT.symm, eT.symm.continuous⟩ eT.symm.isProperMap
      (compactSupportKZeroPullback jT hjT z) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    have heq : jT.comp ⟨eT.symm, eT.symm.continuous⟩ =
        (⟨Subtype.val, continuous_subtype_val⟩ : C((Bᶜ : Set W), W)) := by
      apply ContinuousMap.ext
      intro b
      exact congrArg Subtype.val (eT.apply_symm_apply b)
    simp only [heq]
    rfl
  let z := fun a : ComplexBundle.CompactSupportBundleKMinusOne A ↦
    ComplexBundle.compactSupportBundleKMinusOneBoundary S hS
      (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a)
  have hdecompose (a : ComplexBundle.CompactSupportBundleKMinusOne A) :
      z a = compactSupportKZeroOpenExtension B hBo
          (compactSupportKZeroHomeomorph eB
            (ComplexBundle.compactSupportBundleKMinusOneBoundary A hA a)) +
        compactSupportKZeroOpenExtension Bᶜ hBc.isOpen_compl
          (compactSupportKZeroHomeomorph eT
            (ComplexBundle.compactSupportBundleKMinusOneSuspension A a)) := by
    have hr := clopenReconstruction B hBo hBc (z a)
    change z a = compactSupportKZeroOpenExtension B hBo (rB (z a)) +
      compactSupportKZeroOpenExtension Bᶜ hBc.isOpen_compl (rT (z a)) at hr
    rw [← hrestrictB, ← hrestrictT] at hr
    simpa only [z, hbaseBoundary, htubeBoundary] using hr
  -- Stage 6: nested pointed collapses identify the actual global extensions.
  have hbaseSub : boundaryCylinderBaseOpen A ⊆ W := by
    intro b hb hs
    exact hb hs.1
  let := (isOpen_boundaryCylinderBaseOpen A hA).locallyCompactSpace
  let eNestedB : (boundaryCylinderBaseOpen A) ≃ₜ B := {
    toFun := fun b ↦ ⟨⟨b.val, hbaseSub b.property⟩, b.property⟩
    invFun := fun b ↦ ⟨b.val.val, b.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have hnestedB := nestedExtensionForPiece (boundaryCylinderBaseOpen A) W
    (isOpen_boundaryCylinderBaseOpen A hA) hS.isOpen_compl B hBo hbaseSub
    (fun _ ↦ Iff.rfl) eNestedB (fun _ ↦ rfl)
  have hbaseCoords (b : CompactSupportKZero (Aᶜ : Set X)) :
      compactSupportKZeroHomeomorph eNestedB
          (compactSupportKZeroHomeomorph (boundaryCylinderBaseHomeomorph A) b) =
        compactSupportKZeroHomeomorph eB b := by
    change compactSupportKZeroPullback ⟨eNestedB.symm, eNestedB.symm.continuous⟩
      eNestedB.symm.isProperMap
        (compactSupportKZeroPullback
          ⟨(boundaryCylinderBaseHomeomorph A).symm,
            (boundaryCylinderBaseHomeomorph A).symm.continuous⟩
          (boundaryCylinderBaseHomeomorph A).symm.isProperMap b) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  have hbaseGlobal (b : CompactSupportKZero (Aᶜ : Set X)) :
      compactSupportKZeroOpenExtension W hS.isOpen_compl
          (compactSupportKZeroOpenExtension B hBo (compactSupportKZeroHomeomorph eB b)) =
        compactSupportKZeroOpenExtension (boundaryCylinderBaseOpen A)
          (isOpen_boundaryCylinderBaseOpen A hA)
            (compactSupportKZeroHomeomorph (boundaryCylinderBaseHomeomorph A) b) := by
    rw [← hbaseCoords]
    exact hnestedB _
  have htubeSub : boundaryCylinderTubeOpen A ⊆ W := by
    intro b hb hs
    exact (ne_of_gt hb) hs.2
  have htubeMem (w : W) : w ∈ (Bᶜ : Set W) ↔ w.val ∈ boundaryCylinderTubeOpen A := by
    constructor
    · intro hw
      exact (eWTube.symm ⟨w, hw⟩).property
    · intro hw hb
      exact hb (w.val.property.2.2.resolve_left (ne_of_gt hw))
  have hnestedT := nestedExtensionForPiece (boundaryCylinderTubeOpen A) W
    (isOpen_boundaryCylinderTubeOpen A) hS.isOpen_compl Bᶜ hBc.isOpen_compl htubeSub
    htubeMem eWTube (fun _ ↦ rfl)
  have htubeCoords (b : CompactSupportKZero (A × ℝ)) :
      compactSupportKZeroHomeomorph eWTube
          (compactSupportKZeroHomeomorph (boundaryCylinderTubeHomeomorph A) b) =
        compactSupportKZeroHomeomorph eT b := by
    change compactSupportKZeroPullback ⟨eWTube.symm, eWTube.symm.continuous⟩
      eWTube.symm.isProperMap
        (compactSupportKZeroPullback
          ⟨(boundaryCylinderTubeHomeomorph A).symm,
            (boundaryCylinderTubeHomeomorph A).symm.continuous⟩
          (boundaryCylinderTubeHomeomorph A).symm.isProperMap b) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  have htubeGlobal (b : CompactSupportKZero (A × ℝ)) :
      compactSupportKZeroOpenExtension W hS.isOpen_compl
          (compactSupportKZeroOpenExtension Bᶜ hBc.isOpen_compl
            (compactSupportKZeroHomeomorph eT b)) =
        compactSupportKZeroOpenExtension (boundaryCylinderTubeOpen A)
          (isOpen_boundaryCylinderTubeOpen A)
            (compactSupportKZeroHomeomorph (boundaryCylinderTubeHomeomorph A) b) := by
    rw [← htubeCoords]
    exact hnestedT _
  have hsum (a : ComplexBundle.CompactSupportBundleKMinusOne A) :
      compactSupportKZeroOpenExtension (boundaryCylinderBaseOpen A)
          (isOpen_boundaryCylinderBaseOpen A hA)
          (compactSupportKZeroHomeomorph (boundaryCylinderBaseHomeomorph A)
            (ComplexBundle.compactSupportBundleKMinusOneBoundary A hA a)) +
        compactSupportKZeroOpenExtension (boundaryCylinderTubeOpen A)
          (isOpen_boundaryCylinderTubeOpen A)
          (compactSupportKZeroHomeomorph (boundaryCylinderTubeHomeomorph A)
            (ComplexBundle.compactSupportBundleKMinusOneSuspension A a)) = 0 := by
    have hz : compactSupportKZeroOpenExtension W hS.isOpen_compl (z a) = 0 :=
      (ComplexBundle.range_compactSupportBundleKMinusOneBoundary S hS).le
        ⟨ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eS a, rfl⟩
    rw [hdecompose, map_add, hbaseGlobal, htubeGlobal] at hz
    exact hz
  -- Cancel the same alpha after checking the exact Fin 0/Fin 1 coordinate squares.
  let alpha := AddEquiv.ofBijective (compactSupportKBoundaryBase 0 A hA)
    (compactSupportKBoundaryBase_bijective 0 A hA)
  have hcancel (a : CompactSupportK 1 A) :
      alpha (compactSupportKBoundary 0 A hA a) = compactSupportKBoundaryTube 0 A hA a :=
    alpha.apply_symm_apply _
  have hsign (a : ComplexBundle.CompactSupportBundleKMinusOne A) :
      compactSupportKZeroOpenExtension (boundaryCylinderTubeOpen A)
          (isOpen_boundaryCylinderTubeOpen A)
          (compactSupportKZeroHomeomorph (boundaryCylinderTubeHomeomorph A)
            (ComplexBundle.compactSupportBundleKMinusOneSuspension A a)) =
        -compactSupportKZeroOpenExtension (boundaryCylinderBaseOpen A)
          (isOpen_boundaryCylinderBaseOpen A hA)
          (compactSupportKZeroHomeomorph (boundaryCylinderBaseHomeomorph A)
            (ComplexBundle.compactSupportBundleKMinusOneBoundary A hA a)) := by
    have hs := hsum a
    exact eq_neg_of_add_eq_zero_right hs
  apply AddMonoidHom.ext
  intro a
  change compactSupportKZeroDegreeEquiv (Aᶜ : Set X)
      (compactSupportKBoundary 0 A hA
        (ComplexBundle.compactSupportBundleKMinusOneDegreeOneEquiv A a)) =
    -ComplexBundle.compactSupportBundleKMinusOneBoundary A hA a
  apply (compactSupportKZeroDegreeEquiv (Aᶜ : Set X)).symm.injective
  simp only [AddEquiv.symm_apply_apply, map_neg]
  apply alpha.injective
  apply (compactSupportKZeroDegreeEquiv Z).injective
  rw [hcancel, map_neg, map_neg]
  change compactSupportKZeroDegreeEquiv Z
      (compactSupportKBoundaryTube 0 A hA
        (ComplexBundle.compactSupportBundleKMinusOneDegreeOneEquiv A a)) =
    -compactSupportKZeroDegreeEquiv Z
      (compactSupportKBoundaryBase 0 A hA
        ((compactSupportKZeroDegreeEquiv (Aᶜ : Set X)).symm
          (ComplexBundle.compactSupportBundleKMinusOneBoundary A hA a)))
  rw [boundaryTube_zeroDegree A hA, boundaryBase_zeroDegree A hA,
    AddEquiv.apply_symm_apply]
  exact hsign a

end ComplexBundle

end AtiyahSinger

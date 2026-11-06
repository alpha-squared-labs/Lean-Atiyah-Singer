/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ClutchingBundle
public import AtiyahSinger.Topology.TripleKZero

/-!
# The relative difference class determined by a boundary isomorphism

Public module ID: M1752.

D07/K02. Follow the double-space construction in SG I.9.25. The glued bundle
minus projection pullback of the target gives an absolute class on the double.
Its unique relative lift exists because the right copy is a retract. Pull back
that lift along the left inclusion. Forgetting on the original pair is never
assumed injective, and the given boundary map enters through the seam equation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] [hX : CompactSpace X] [hT : T2Space X]
  {A : Set X}

include hX hT

attribute [local instance] DoubleSpace.compactSpace
  sumTopology isFiniteRank_sum isFiniteRank_pullback


/-- The absolute difference on the double, retaining the glued boundary information. -/
def BundleTriple.doubleDifference (hA : IsClosed A) (a : BundleTriple A) :
    letI := DoubleSpace.t2Space A hA
    ComplexKZero (DoubleSpace A) :=
  letI := DoubleSpace.t2Space A hA
  (clutchingBundle hA a).kZeroClass -
    complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass

/-- On the left copy the double difference is the original absolute difference. -/
theorem BundleTriple.doubleDifference_left (hA : IsClosed A) (a : BundleTriple A) :
    letI := DoubleSpace.t2Space A hA
    complexKZeroPullback (DoubleSpace.leftMap A) (a.doubleDifference hA) = a.absoluteClass := by
  /- The left clutching chart identifies the first term with the source
  bundle class. Projection followed by the left inclusion is identity, so the
  second term restricts to the target class. Subtract the two identifications. -/
  let := DoubleSpace.t2Space A hA
  -- Use the original left clutching chart on the same chosen glued bundle.
  have hglued : complexKZeroPullback (DoubleSpace.leftMap A)
      (clutchingBundle hA a).kZeroClass = a.source.kZeroClass := by
    rw [← FiniteBundle.kZeroClass_pullback]
    exact kZeroClass_eq_of_iso (clutchingLeftIso hA a)
  have hprojection : complexKZeroPullback (DoubleSpace.leftMap A)
      (complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass) =
        a.target.kZeroClass := by
    have hcomp : (DoubleSpace.projMap A).comp (DoubleSpace.leftMap A) =
        ContinuousMap.id X := by
      ext x
      exact DoubleSpace.proj_left A x
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hcomp]
    change kZeroMap (RingHom.id _) _ = _
    rw [kZeroMap_id]
    rfl
  -- The actual projection restricts to identity, so the subtraction has the stated sign.
  change complexKZeroPullback (DoubleSpace.leftMap A) (_ - _) = _
  rw [map_sub, hglued, hprojection]
  rfl

/-- On the right copy both terms of the double difference agree. -/
theorem BundleTriple.doubleDifference_right (hA : IsClosed A) (a : BundleTriple A) :
    letI := DoubleSpace.t2Space A hA
    complexKZeroPullback (DoubleSpace.rightMap A) (a.doubleDifference hA) = 0 := by
  /- Use the right clutching chart to identify the glued restriction with
  the target bundle. Projection pullback has the same restriction since the
  right inclusion is a section of projection; their difference is therefore zero. -/
  let := DoubleSpace.t2Space A hA
  -- The original right chart identifies the glued bundle with the target bundle.
  have hglued : complexKZeroPullback (DoubleSpace.rightMap A)
      (clutchingBundle hA a).kZeroClass = a.target.kZeroClass := by
    rw [← FiniteBundle.kZeroClass_pullback]
    exact kZeroClass_eq_of_iso (clutchingRightIso hA a)
  have hprojection : complexKZeroPullback (DoubleSpace.rightMap A)
      (complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass) =
        a.target.kZeroClass := by
    have hcomp : (DoubleSpace.projMap A).comp (DoubleSpace.rightMap A) =
        ContinuousMap.id X := by
      ext x
      exact DoubleSpace.proj_right A x
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hcomp]
    change kZeroMap (RingHom.id _) _ = _
    rw [kZeroMap_id]
    rfl
  -- Both terms refer to that same target, including when either base or rank is empty.
  change complexKZeroPullback (DoubleSpace.rightMap A) (_ - _) = _
  rw [map_sub, hglued, hprojection, sub_self]

/-- The double difference belongs to the actual restriction kernel. -/
theorem BundleTriple.doubleDifference_restriction_zero (hA : IsClosed A) (a : BundleTriple A) :
    letI := DoubleSpace.t2Space A hA
    complexKZeroRestriction (DoubleSpace.rightRange A) (DoubleSpace.isClosed_rightRange A hA)
      (a.doubleDifference hA) = 0 := by
  /- The right closed embedding identifies X with its range. Transport the
  vanishing of pullback along the right inclusion through that homeomorphism.
  This yields zero for restriction to the exact right-range subtype. -/
  let := DoubleSpace.t2Space A hA
  let R := DoubleSpace.rightRange A
  have hR : IsClosed R := DoubleSpace.isClosed_rightRange A hA
  let := hR.isClosedEmbedding_subtypeVal.compactSpace
  let p : C(R, X) := (DoubleSpace.projMap A).comp
    ⟨Subtype.val, continuous_subtype_val⟩
  -- The right inclusion composed with projection on its literal range is the subtype map.
  have hcomp : (DoubleSpace.rightMap A).comp p =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, DoubleSpace A)) := by
    ext z
    obtain ⟨x, hx⟩ := z.property
    change DoubleSpace.right A (DoubleSpace.proj A z.val) = z.val
    rw [← hx, DoubleSpace.proj_right]
  have hzero := congrArg (complexKZeroPullback p) (a.doubleDifference_right hA)
  rw [map_zero, ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hcomp] at hzero
  exact hzero

/-- The retract pair has a unique relative lift of the specified double difference. -/
theorem BundleTriple.exists_unique_differenceLift (hA : IsClosed A) (a : BundleTriple A) :
    letI := DoubleSpace.t2Space A hA
    ∃! c : RelativeKZero (DoubleSpace.rightRange A) (DoubleSpace.isClosed_rightRange A hA),
      relativeKZeroForget (DoubleSpace.rightRange A) (DoubleSpace.isClosed_rightRange A hA) c =
        a.doubleDifference hA := by
  /- The restriction-kernel equation and relative exactness give existence
  of a preimage. The explicit right retraction makes forgetting injective for
  this double pair, hence gives uniqueness. Neither step assumes injectivity
  for the original pair or uses the subsequent triple-comparison theorem. -/
  let := DoubleSpace.t2Space A hA
  let R := DoubleSpace.rightRange A
  have hR : IsClosed R := DoubleSpace.isClosed_rightRange A hA
  -- Exactness supplies a lift in the original reduced quotient group.
  have hmem : a.doubleDifference hA ∈ (relativeKZeroForget R hR).range := by
    rw [range_relativeKZeroForget]
    exact a.doubleDifference_restriction_zero hA
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, hc, ?_⟩
  -- Forgetting is used injectively only on this specified retract pair.
  intro d hd
  exact relativeKZeroForget_injective_of_retraction R hR
    (DoubleSpace.rightRetraction A) (DoubleSpace.rightRetraction_apply A) (hd.trans hc.symm)

/-- Select the uniquely characterized relative difference on the double. -/
def BundleTriple.differenceLift (hA : IsClosed A) (a : BundleTriple A) :
    letI := DoubleSpace.t2Space A hA
    RelativeKZero (DoubleSpace.rightRange A) (DoubleSpace.isClosed_rightRange A hA) :=
  letI := DoubleSpace.t2Space A hA
  (a.exists_unique_differenceLift hA).exists.choose

/-- The chosen relative lift forgets to the specified double difference. -/
theorem BundleTriple.forget_differenceLift (hA : IsClosed A) (a : BundleTriple A) :
    letI := DoubleSpace.t2Space A hA
    relativeKZeroForget (DoubleSpace.rightRange A) (DoubleSpace.isClosed_rightRange A hA)
      (a.differenceLift hA) = a.doubleDifference hA := by
  /- Use the property of the selected existence witness. The uniqueness
  result ensures that subsequent comparisons do not depend on arbitrary choices
  of a preimage, while the glued bundle still carries the boundary information. -/
  let := DoubleSpace.t2Space A hA
  -- The original selected existence witness already carries this exact equation.
  exact (a.exists_unique_differenceLift hA).exists.choose_spec

/-- The actual SG difference class on the original pair. -/
def BundleTriple.relativeClass (hA : IsClosed A) (a : BundleTriple A) : RelativeKZero A hA :=
  DoubleSpace.relativeRestriction A hA (a.differenceLift hA)

/-- Forgetting the difference class gives the original absolute difference. -/
theorem BundleTriple.relativeClass_forget (hA : IsClosed A) (a : BundleTriple A) :
    relativeKZeroForget A hA (a.relativeClass hA) = a.absoluteClass := by
  /- Use naturality of forgetting for the left inclusion. The lift forgets
  to the double difference, whose left restriction is the source class minus
  the target class. This characterizes only the forgotten image, not the relative class. -/
  let := DoubleSpace.t2Space A hA
  -- Naturality uses the same left map of pairs as the original relativeClass definition.
  have hnatural := relativeKZeroForget_natural A hA (DoubleSpace.rightRange A)
    (DoubleSpace.isClosed_rightRange A hA) (DoubleSpace.leftMap A)
    (DoubleSpace.left_mapsTo A)
  calc
    _ = complexKZeroPullback (DoubleSpace.leftMap A)
        (relativeKZeroForget (DoubleSpace.rightRange A)
          (DoubleSpace.isClosed_rightRange A hA) (a.differenceLift hA)) :=
      DFunLike.congr_fun hnatural (a.differenceLift hA)
    _ = a.absoluteClass := by
      rw [a.forget_differenceLift hA, a.doubleDifference_left hA]

/-- The constructed relative class is invariant under isomorphism of triples. -/
theorem BundleTriple.relativeClass_eq_of_isIsomorphic (hA : IsClosed A) (a b : BundleTriple A)
    (h : a.IsIsomorphic b) : a.relativeClass hA = b.relativeClass hA := by
  /- Isomorphic triples give isomorphic glued bundles and isomorphic target
  bundles, so the two absolute double differences agree. Injectivity of forgetting
  on the double retract pair identifies their relative lifts; then restrict left. -/
  let := DoubleSpace.t2Space A hA
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨e⟩ := nonempty_clutching_iso_of_isIsomorphic hA a b ⟨u, v, huv⟩
  have hglued := kZeroClass_eq_of_iso e
  have htarget := kZeroClass_eq_of_iso v
  -- Compare absolute differences of the same two glued triples first.
  have hdouble : a.doubleDifference hA = b.doubleDifference hA := by
    change (clutchingBundle hA a).kZeroClass - _ = (clutchingBundle hA b).kZeroClass - _
    change (clutchingBundle hA a).kZeroClass = (clutchingBundle hA b).kZeroClass at hglued
    change a.target.kZeroClass = b.target.kZeroClass at htarget
    rw [hglued, htarget]
  change DoubleSpace.relativeRestriction A hA (a.differenceLift hA) =
    DoubleSpace.relativeRestriction A hA (b.differenceLift hA)
  apply congrArg (DoubleSpace.relativeRestriction A hA)
  -- Uniqueness of lifts is legitimate on the double's actual right retract pair.
  apply relativeKZeroForget_injective_of_retraction (DoubleSpace.rightRange A)
    (DoubleSpace.isClosed_rightRange A hA) (DoubleSpace.rightRetraction A)
    (DoubleSpace.rightRetraction_apply A)
  rw [a.forget_differenceLift hA, b.forget_differenceLift hA, hdouble]

/-- The constructed difference class is additive for direct sum. -/
theorem BundleTriple.relativeClass_sum (hA : IsClosed A) (a b : BundleTriple A) :
    (a.sum b).relativeClass hA = a.relativeClass hA + b.relativeClass hA := by
  /- Clutching commutes with direct sums by its charts, and bundle classes
  are additive. Thus double differences add. Uniqueness of their relative lifts
  in the retract pair identifies the lift of the sum; left pullback is additive. -/
  let := DoubleSpace.t2Space A hA
  obtain ⟨e⟩ := nonempty_clutching_sum_iso hA a b
  have hglued := kZeroClass_eq_of_iso e
  change (clutchingBundle hA (a.sum b)).kZeroClass =
    ((clutchingBundle hA a).sum (clutchingBundle hA b)).kZeroClass at hglued
  rw [FiniteBundle.kZeroClass_sum] at hglued
  -- Gluing and projection pullback use the same direct-sum order on both terms.
  have hdouble : (a.sum b).doubleDifference hA =
      a.doubleDifference hA + b.doubleDifference hA := by
    change (clutchingBundle hA (a.sum b)).kZeroClass -
      complexKZeroPullback (DoubleSpace.projMap A) (a.target.sum b.target).kZeroClass = _
    rw [hglued, FiniteBundle.kZeroClass_sum, map_add]
    dsimp only [BundleTriple.doubleDifference]
    abel
  rw [BundleTriple.relativeClass, BundleTriple.relativeClass, BundleTriple.relativeClass,
    ← map_add]
  apply congrArg (DoubleSpace.relativeRestriction A hA)
  apply relativeKZeroForget_injective_of_retraction (DoubleSpace.rightRange A)
    (DoubleSpace.isClosed_rightRange A hA) (DoubleSpace.rightRetraction A)
    (DoubleSpace.rightRetraction_apply A)
  rw [map_add, BundleTriple.forget_differenceLift, BundleTriple.forget_differenceLift,
    BundleTriple.forget_differenceLift, hdouble]

/-- An identity boundary triple has zero difference class. -/
theorem BundleTriple.relativeClass_identity (hA : IsClosed A) (E : FiniteBundle X) :
    (BundleTriple.identity A E).relativeClass hA = 0 := by
  /- The identity clutching bundle is projection pullback of E, so its
  double difference is zero. Injectivity of forgetting on the double pair makes
  its relative lift zero. Pullback along the left inclusion preserves zero. -/
  let := DoubleSpace.t2Space A hA
  obtain ⟨e⟩ := nonempty_clutching_identity_iso hA E
  have hglued := kZeroClass_eq_of_iso e
  change (clutchingBundle hA (BundleTriple.identity A E)).kZeroClass =
    (E.pullback (DoubleSpace.projMap A)).kZeroClass at hglued
  rw [FiniteBundle.kZeroClass_pullback] at hglued
  have hdouble : (BundleTriple.identity A E).doubleDifference hA = 0 := by
    change (clutchingBundle hA (BundleTriple.identity A E)).kZeroClass -
      complexKZeroPullback (DoubleSpace.projMap A) E.kZeroClass = 0
    rw [hglued, sub_self]
  -- The identity difference has zero lift because the retract forget map is injective.
  change DoubleSpace.relativeRestriction A hA _ = 0
  rw [← map_zero (DoubleSpace.relativeRestriction A hA)]
  apply congrArg (DoubleSpace.relativeRestriction A hA)
  apply relativeKZeroForget_injective_of_retraction (DoubleSpace.rightRange A)
    (DoubleSpace.isClosed_rightRange A hA) (DoubleSpace.rightRetraction A)
    (DoubleSpace.rightRetraction_apply A)
  rw [BundleTriple.forget_differenceLift, map_zero, hdouble]

/-- Stable isomorphism preserves the constructed relative class. -/
theorem BundleTriple.relativeClass_eq_of_isStablyIsomorphic (hA : IsClosed A)
    (a b : BundleTriple A) (h : a.IsStablyIsomorphic b) :
    a.relativeClass hA = b.relativeClass hA := by
  /- Apply isomorphism invariance to the stabilized triples. Expand direct
  sums and remove the identity-triple classes, which vanish. The remaining
  equality is between the two original constructed difference classes. -/
  obtain ⟨E, F, hEF⟩ := h
  -- Preserve the specified stabilizing bundles and cancel only their identity classes.
  have heq := BundleTriple.relativeClass_eq_of_isIsomorphic hA _ _ hEF
  simpa only [BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity,
    add_zero] using heq

/-- Inverting a triple negates its difference class. -/
theorem BundleTriple.relativeClass_inverse (hA : IsClosed A) (a : BundleTriple A) :
    a.inverse.relativeClass hA = -a.relativeClass hA := by
  /- The existing block-rotation and closed-pair lifting theorem supplies
  an isomorphism from the sum of this triple with its inverse to an
  identity triple. Isomorphism invariance makes its relative class zero;
  additivity then identifies the inverse class with the negative. -/
  -- The existing block-rotation theorem compares this exact triple with its reverse.
  have heq := BundleTriple.relativeClass_eq_of_isIsomorphic hA _ _
    (a.isIsomorphic_sum_inverse A hA)
  rw [BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity] at heq
  exact eq_neg_of_add_eq_zero_right heq

/-- Boundary homotopy does not change the difference class. -/
theorem bundleTriple_relativeClass_eq_of_homotopy (hA : IsClosed A)
    (E F : FiniteBundle X) (a b : RelativeTriple E.Fiber F.Fiber A) (H : IsoHomotopy a b) :
    (BundleTriple.ofBoundary E F a).relativeClass hA =
      (BundleTriple.ofBoundary E F b).relativeClass hA := by
  /- The established isomorphism, direct-sum and identity formulas define
  an additive map from the original triple K group to relative classes.
  Apply that map to the already proved boundary-homotopy relation for
  these same two triples, then evaluate its generator formula. -/
  -- The proved defining relations descend the actual difference classes to the triple group.
  obtain ⟨φ, hφ, _⟩ := tripleKZero_universal_property A
    (fun t ↦ t.relativeClass hA)
    (fun s t h ↦ s.relativeClass_eq_of_isIsomorphic hA t h)
    (fun s t ↦ s.relativeClass_sum hA t)
    (fun V ↦ BundleTriple.relativeClass_identity hA V)
  -- Its known homotopy identity therefore applies to those same original boundary maps.
  have heq := congrArg φ (bundleTriple_kZeroClass_eq_of_homotopy A hA E F a b H)
  simpa only [hφ] using heq

/-- The constructed difference class is natural under inverse-image pullback. -/
theorem BundleTriple.relativeClass_pullback {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] (hA : IsClosed A) (a : BundleTriple A) (f : C(Y, X)) :
    (a.pullback f).relativeClass (hA.preimage f.continuous) =
      relativeKZeroPullback (f ⁻¹' A) (hA.preimage f.continuous) A hA f (fun _ hx ↦ hx)
        (a.relativeClass hA) := by
  /- The map of doubles takes each copy by f. The pulled-back clutching
  charts give the clutching bundle of the pulled-back triple, and projection
  pullbacks commute. Naturality of forgetting and uniqueness on the source
  double identify the relative lifts; commuting left inclusions gives the formula. -/
  let B := f ⁻¹' A
  have hB : IsClosed B := hA.preimage f.continuous
  have hf : Set.MapsTo f B A := fun _ hx ↦ hx
  let := DoubleSpace.t2Space A hA
  let := DoubleSpace.t2Space B hB
  let RA := DoubleSpace.rightRange A
  let RB := DoubleSpace.rightRange B
  have hRA : IsClosed RA := DoubleSpace.isClosed_rightRange A hA
  have hRB : IsClosed RB := DoubleSpace.isClosed_rightRange B hB
  let d := DoubleSpace.mapContinuous B A f hf
  have hd : Set.MapsTo d RB RA := by
    rintro z ⟨y, rfl⟩
    exact ⟨f y, rfl⟩
  let dPull := relativeKZeroPullback RB hRB RA hRA d hd
  -- The same map of doubles intertwines projection and carries the actual glued bundle.
  obtain ⟨e⟩ := nonempty_clutching_pullback_iso hA a f
  have hglued := kZeroClass_eq_of_iso e
  change (clutchingBundle hB (a.pullback f)).kZeroClass =
    ((clutchingBundle hA a).pullback d).kZeroClass at hglued
  rw [FiniteBundle.kZeroClass_pullback] at hglued
  have hprojection : complexKZeroPullback (DoubleSpace.projMap B)
      (a.pullback f).target.kZeroClass =
        complexKZeroPullback d
          (complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass) := by
    have hcomp : f.comp (DoubleSpace.projMap B) = (DoubleSpace.projMap A).comp d := by
      ext z
      induction z using Quotient.inductionOn with
      | h z => cases z <;> rfl
    change complexKZeroPullback (DoubleSpace.projMap B)
      (a.target.pullback f).kZeroClass = _
    rw [FiniteBundle.kZeroClass_pullback]
    calc
      _ = complexKZeroPullback (f.comp (DoubleSpace.projMap B)) a.target.kZeroClass :=
        (DFunLike.congr_fun (complexKZeroPullback_comp (DoubleSpace.projMap B) f)
          a.target.kZeroClass).symm
      _ = complexKZeroPullback ((DoubleSpace.projMap A).comp d) a.target.kZeroClass := by
        rw [hcomp]
      _ = _ := DFunLike.congr_fun (complexKZeroPullback_comp d (DoubleSpace.projMap A))
        a.target.kZeroClass
  have hdouble : (a.pullback f).doubleDifference hB =
      complexKZeroPullback d (a.doubleDifference hA) := by
    change (clutchingBundle hB (a.pullback f)).kZeroClass -
      complexKZeroPullback (DoubleSpace.projMap B) (a.pullback f).target.kZeroClass =
        complexKZeroPullback d (_ - _)
    rw [map_sub, hglued, hprojection]
  -- Naturality of forgetting and the source double's retract identify the chosen lifts.
  have hlift : (a.pullback f).differenceLift hB = dPull (a.differenceLift hA) := by
    apply relativeKZeroForget_injective_of_retraction RB hRB
      (DoubleSpace.rightRetraction B) (DoubleSpace.rightRetraction_apply B)
    have hnatural := relativeKZeroForget_natural RB hRB RA hRA d hd
    calc
      _ = (a.pullback f).doubleDifference hB :=
        BundleTriple.forget_differenceLift hB (a.pullback f)
      _ = complexKZeroPullback d (a.doubleDifference hA) := hdouble
      _ = complexKZeroPullback d
          (relativeKZeroForget RA hRA (a.differenceLift hA)) := by
        rw [a.forget_differenceLift hA]
      _ = _ := (DFunLike.congr_fun hnatural (a.differenceLift hA)).symm
  -- The two left restrictions commute through those very maps of pairs.
  have hrestriction : (DoubleSpace.relativeRestriction B hB).comp dPull =
      (relativeKZeroPullback B hB A hA f hf).comp
        (DoubleSpace.relativeRestriction A hA) := by
    change (relativeKZeroPullback B hB RB hRB (DoubleSpace.leftMap B)
      (DoubleSpace.left_mapsTo B)).comp (relativeKZeroPullback RB hRB RA hRA d hd) =
        (relativeKZeroPullback B hB A hA f hf).comp
          (relativeKZeroPullback A hA RA hRA (DoubleSpace.leftMap A)
            (DoubleSpace.left_mapsTo A))
    have hleft := relativeKZeroPullback_comp B hB RB hRB RA hRA
      (DoubleSpace.leftMap B) d (DoubleSpace.left_mapsTo B) hd
    have hright := relativeKZeroPullback_comp B hB A hA RA hRA
      f (DoubleSpace.leftMap A) hf (DoubleSpace.left_mapsTo A)
    rw [← hleft, ← hright]
    congr 1
  change DoubleSpace.relativeRestriction B hB ((a.pullback f).differenceLift hB) =
    relativeKZeroPullback B hB A hA f hf
      (DoubleSpace.relativeRestriction A hA (a.differenceLift hA))
  rw [hlift]
  exact DFunLike.congr_fun hrestriction (a.differenceLift hA)

end AtiyahSinger.ComplexBundle

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeKZeroExcision

/-!
# The double of a space along a subspace

Public module ID: M1754.

D07/K02. The actual quotient of X ⊕ X identifies the two copies exactly over A.
It carries the quotient topology. Compact Hausdorff X and closed A make its two
copies closed embedded retracts. This is the double used in SG I.9.25; restriction
from the double relative to its right copy recovers the original closed pair.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


/-- Identify the same base point across the two copies only on the seam. -/
def DoubleRel (A : Set X) (x y : X ⊕ X) : Prop :=
  Sum.elim id id x = Sum.elim id id y ∧ (x = y ∨ Sum.elim id id x ∈ A)


set_option linter.unusedSectionVars false in
/-- The seam relation is an equivalence relation. -/
theorem doubleRel_equivalence (A : Set X) : Equivalence (DoubleRel A) := by
  /- The first condition preserves the base point along any chain. Away from A
  the second condition forces equal representatives. Over A both copies of the
  same point are related. These descriptions give reflexivity, symmetry and transitivity. -/
  constructor
  · intro x
    exact ⟨rfl, Or.inl rfl⟩
  · intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hxy | hx
    · exact Or.inl hxy.symm
    · exact Or.inr (h.1 ▸ hx)
  · intro x y z hxy hyz
    refine ⟨hxy.1.trans hyz.1, ?_⟩
    rcases hxy.2 with hxy' | hx
    · rcases hyz.2 with hyz' | hy
      · exact Or.inl (hxy'.trans hyz')
      · exact Or.inr (hxy.1.symm ▸ hy)
    · exact Or.inr hx

/-- The setoid of the explicit seam relation. -/
def doubleSetoid (A : Set X) : Setoid (X ⊕ X) :=
  ⟨DoubleRel A, doubleRel_equivalence A⟩

/-- The doubled space with its inherited quotient topology. -/
abbrev DoubleSpace (A : Set X) : Type _ := Quotient (doubleSetoid A)

/-- Include the first copy in the double. -/
def DoubleSpace.left (A : Set X) (x : X) : DoubleSpace A :=
  Quotient.mk _ (Sum.inl x)

/-- Include the second copy in the double. -/
def DoubleSpace.right (A : Set X) (x : X) : DoubleSpace A :=
  Quotient.mk _ (Sum.inr x)

/-- The first inclusion is continuous for the quotient topology. -/
theorem DoubleSpace.continuous_left (A : Set X) : Continuous (DoubleSpace.left A) := by
  /- Compose the continuous inclusion of the left summand with the quotient
  map. The quotient topology makes that second map continuous by construction. -/
  exact continuous_quot_mk.comp continuous_inl

/-- The second inclusion is continuous for the quotient topology. -/
theorem DoubleSpace.continuous_right (A : Set X) : Continuous (DoubleSpace.right A) := by
  /- Compose the continuous inclusion of the right summand with the quotient
  map. This does not require the seam to be closed or the base to be compact. -/
  exact continuous_quot_mk.comp continuous_inr

/-- The first inclusion as a continuous map. -/
def DoubleSpace.leftMap (A : Set X) : C(X, DoubleSpace A) :=
  ⟨DoubleSpace.left A, DoubleSpace.continuous_left A⟩

/-- The second inclusion as a continuous map. -/
def DoubleSpace.rightMap (A : Set X) : C(X, DoubleSpace A) :=
  ⟨DoubleSpace.right A, DoubleSpace.continuous_right A⟩

/-- Project either copy to its original base point. -/
def DoubleSpace.proj (A : Set X) : DoubleSpace A → X :=
  Quotient.lift (Sum.elim id id) (fun _ _ h ↦ h.1)

/-- Projection from the double is continuous. -/
theorem DoubleSpace.continuous_proj (A : Set X) : Continuous (DoubleSpace.proj A) := by
  /- Before taking the quotient this is the continuous map that is identity
  on each summand. The defining relation preserves this map, so the universal
  property of the quotient topology gives continuity of its descent. -/
  exact continuous_quot_lift _ (continuous_id.sumElim continuous_id)

/-- The projection as a continuous map. -/
def DoubleSpace.projMap (A : Set X) : C(DoubleSpace A, X) :=
  ⟨DoubleSpace.proj A, DoubleSpace.continuous_proj A⟩

/-- Projection recovers the base point on the left copy. -/
theorem DoubleSpace.proj_left (A : Set X) (x : X) :
    DoubleSpace.proj A (DoubleSpace.left A x) = x := by
  /- Evaluate the quotient lift on this representative. The map before
  descent is identity on the chosen summand, giving the stated equality. -/
  rfl

/-- The left copy has no internal identifications. -/
theorem DoubleSpace.left_injective (A : Set X) : Function.Injective (DoubleSpace.left A) := by
  /- Apply the projection to an equality of images. Its composite with the
  inclusion is identity, so the two original points must be equal. -/
  intro x y h
  exact congrArg (DoubleSpace.proj A) h

/-- Projection recovers the base point on the right copy. -/
theorem DoubleSpace.proj_right (A : Set X) (x : X) :
    DoubleSpace.proj A (DoubleSpace.right A x) = x := by
  /- Evaluate the quotient lift on this representative. The map before
  descent is identity on the chosen summand, giving the stated equality. -/
  rfl

/-- The right copy has no internal identifications. -/
theorem DoubleSpace.right_injective (A : Set X) : Function.Injective (DoubleSpace.right A) := by
  /- Apply the projection to an equality of images. Its composite with the
  inclusion is identity, so the two original points must be equal. -/
  intro x y h
  exact congrArg (DoubleSpace.proj A) h

/-- The two copies meet at precisely the seam points. -/
theorem DoubleSpace.left_eq_right_iff (A : Set X) (x y : X) :
    DoubleSpace.left A x = DoubleSpace.right A y ↔ x = y ∧ x ∈ A := by
  /- Effectiveness of the quotient gives exactly the seam relation. The two
  distinct sum constructors cannot be equal, so the second disjunct requires
  membership in A; the first condition in the relation requires the same base point. -/
  constructor
  · intro h
    have hr : DoubleRel A (Sum.inl x) (Sum.inr y) := Quotient.exact h
    exact ⟨hr.1, hr.2.resolve_left (fun h ↦ by cases h)⟩
  · intro h
    exact Quotient.sound ⟨h.1, Or.inr h.2⟩

/-- The two inclusions agree on the seam. -/
theorem DoubleSpace.left_eq_right (A : Set X) (a : A) :
    DoubleSpace.left A a = DoubleSpace.right A a := by
  /- Use the seam-intersection criterion with the two equal base points and
  the membership carried by a. This equality is later used for fiber transport. -/
  exact (DoubleSpace.left_eq_right_iff A a a).mpr ⟨rfl, a.property⟩

/-- Every point lies in one of the two copies. -/
theorem DoubleSpace.range_left_union_range_right (A : Set X) :
    Set.range (DoubleSpace.left A) ∪ Set.range (DoubleSpace.right A) = Set.univ := by
  /- Choose a sum representative for a quotient point. A left representative
  belongs to the first range and a right representative to the second. -/
  apply Set.eq_univ_of_forall
  intro z
  induction z using Quotient.inductionOn with
  | h x =>
    cases x with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr x => exact Or.inr ⟨x, rfl⟩

/-- The double of a compact space is compact. -/
theorem DoubleSpace.compactSpace [CompactSpace X] (A : Set X) : CompactSpace (DoubleSpace A) := by
  /- The sum of two compact spaces is compact. Its continuous surjective
  quotient map transfers compactness to the double, without closedness of A. -/
  exact Quotient.compactSpace

attribute [local instance] DoubleSpace.compactSpace

/-- A closed seam in compact Hausdorff X gives a Hausdorff double. -/
theorem DoubleSpace.t2Space [CompactSpace X] [T2Space X] (A : Set X) (hA : IsClosed A) :
    T2Space (DoubleSpace A) := by
  /- Map the original double into X times the original pointed quotient X/A.
  The first coordinate remembers the base point; the second sends the left
  copy to its quotient class and the right copy to the base point. This map
  is continuous and injective because its identifications are exactly the seam.
  The existing compact closed-pair theorem makes X/A Hausdorff. -/
  let : T2Space (PointedQuotient.{_, 0} A) := PointedQuotient.t2Space A hA
  -- Projection records the base point, and the pointed quotient distinguishes the two sides.
  let f : X ⊕ X → X × PointedQuotient.{_, 0} A :=
    Sum.elim (fun x ↦ (x, PointedQuotient.of A x))
      (fun x ↦ (x, PointedQuotient.basepoint A))
  have hf : Continuous f :=
    (continuous_id.prodMk (PointedQuotient.continuous_of A)).sumElim
      (continuous_id.prodMk continuous_const)
  have hrel (x y : X ⊕ X) (h : DoubleRel A x y) : f x = f y := by
    rcases x with x | x <;> rcases y with y | y
    · exact Prod.ext h.1 (congrArg (PointedQuotient.of A) h.1)
    · exact Prod.ext h.1 ((PointedQuotient.of_eq_basepoint_iff A x).mpr
        (h.2.resolve_left (fun h ↦ by cases h)))
    · have hxy : x = y := h.1
      have hy : y ∈ A := hxy ▸ (h.2.resolve_left (fun h ↦ by cases h))
      exact Prod.ext h.1 ((PointedQuotient.of_eq_basepoint_iff A y).mpr hy).symm
    · exact Prod.ext h.1 rfl
  let g : DoubleSpace A → X × PointedQuotient.{_, 0} A := Quotient.lift f hrel
  have hg : Continuous g := hf.quotient_lift hrel
  -- The two recorded coordinates identify precisely the original seam equivalence.
  have hinj : Function.Injective g := by
    intro z w h
    induction z using Quotient.inductionOn with
    | h x =>
      induction w using Quotient.inductionOn with
      | h y =>
        have hbase := congrArg Prod.fst h
        have hside := congrArg Prod.snd h
        rcases x with x | x <;> rcases y with y | y
        · exact congrArg (DoubleSpace.left A) hbase
        · exact (DoubleSpace.left_eq_right_iff A x y).mpr
            ⟨hbase, (PointedQuotient.of_eq_basepoint_iff A x).mp hside⟩
        · exact ((DoubleSpace.left_eq_right_iff A y x).mpr
            ⟨hbase.symm, (PointedQuotient.of_eq_basepoint_iff A y).mp hside.symm⟩).symm
        · exact congrArg (DoubleSpace.right A) hbase
  exact T2Space.of_injective_continuous hinj hg

/-- The left copy is closed embedded for a compact closed pair. -/
theorem DoubleSpace.isClosedEmbedding_left [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) : Topology.IsClosedEmbedding (DoubleSpace.left A) := by
  /- The inclusion is continuous and injective. Its source is compact and
  the double is Hausdorff under the closed-seam hypothesis, so it is a closed embedding. -/
  let : T2Space (DoubleSpace A) := DoubleSpace.t2Space A hA
  exact (DoubleSpace.continuous_left A).isClosedEmbedding (DoubleSpace.left_injective A)

/-- The right copy is closed embedded for a compact closed pair. -/
theorem DoubleSpace.isClosedEmbedding_right [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) : Topology.IsClosedEmbedding (DoubleSpace.right A) := by
  /- The inclusion is continuous and injective. Its source is compact and
  the double is Hausdorff under the closed-seam hypothesis, so it is a closed embedding. -/
  let : T2Space (DoubleSpace A) := DoubleSpace.t2Space A hA
  exact (DoubleSpace.continuous_right A).isClosedEmbedding (DoubleSpace.right_injective A)

/-- The right copy, used as the relative subspace of the double. -/
def DoubleSpace.rightRange (A : Set X) : Set (DoubleSpace A) :=
  Set.range (DoubleSpace.right A)

/-- The right relative subspace is closed. -/
theorem DoubleSpace.isClosed_rightRange [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) : IsClosed (DoubleSpace.rightRange A) := by
  /- Apply closedness of the range of the right closed embedding. This is
  the exact subset used in the relative K group of the double. -/
  exact (DoubleSpace.isClosedEmbedding_right A hA).isClosed_range

/-- Retract the double onto its right copy through the original base projection. -/
def DoubleSpace.rightRetraction (A : Set X) : C(DoubleSpace A, DoubleSpace.rightRange A) :=
  ⟨fun z ↦ ⟨DoubleSpace.right A (DoubleSpace.proj A z), ⟨_, rfl⟩⟩,
    (DoubleSpace.continuous_right A |>.comp (DoubleSpace.continuous_proj A)).subtype_mk _⟩

/-- The specified map fixes every point of the right copy. -/
theorem DoubleSpace.rightRetraction_apply (A : Set X) (a : DoubleSpace.rightRange A) :
    DoubleSpace.rightRetraction A a = a := by
  /- Write a as the image of a point in the right copy. Projection returns
  that point, and re-inclusion returns a; subtype extensionality gives the equality. -/
  apply Subtype.ext
  obtain ⟨x, hx⟩ := a.property
  change DoubleSpace.right A (DoubleSpace.proj A a.val) = a.val
  rw [← hx, DoubleSpace.proj_right]

/-- The left inclusion is a map from the original pair to the double pair. -/
theorem DoubleSpace.left_mapsTo (A : Set X) :
    Set.MapsTo (DoubleSpace.leftMap A) A (DoubleSpace.rightRange A) := by
  /- On A the two inclusions agree, so each left image there belongs to the
  range of the right inclusion. This verifies the exact map-of-pairs condition. -/
  intro x hx
  exact ⟨x, (DoubleSpace.left_eq_right A ⟨x, hx⟩).symm⟩

/-- Restrict relative classes on the double along its actual left inclusion. -/
def DoubleSpace.relativeRestriction [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    letI := DoubleSpace.t2Space A hA
    RelativeKZero (DoubleSpace.rightRange A) (DoubleSpace.isClosed_rightRange A hA) →+
      RelativeKZero A hA :=
  letI := DoubleSpace.t2Space A hA
  relativeKZeroPullback A hA (DoubleSpace.rightRange A)
    (DoubleSpace.isClosed_rightRange A hA) (DoubleSpace.leftMap A)
    (DoubleSpace.left_mapsTo A)

/-- Closed excision makes restriction from the double pair bijective. -/
theorem DoubleSpace.relativeRestriction_bijective [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) : Function.Bijective (DoubleSpace.relativeRestriction A hA) := by
  /- Use the actual pointed quotient map induced by the left inclusion.
  The two copies cover the double and meet exactly at the seam, so collapsing
  the right copy makes this map bijective. Compactness and Hausdorffness make
  it a pointed homeomorphism. Its inverse pullback is inverse to the specified
  relative restriction. This is closed-cover excision on the original quotients. -/
  let : T2Space (DoubleSpace A) := DoubleSpace.t2Space A hA
  let R := DoubleSpace.rightRange A
  have hR : IsClosed R := DoubleSpace.isClosed_rightRange A hA
  let : CompactSpace (PointedQuotient A) := PointedQuotient.compactSpace A
  let : T2Space (PointedQuotient A) := PointedQuotient.t2Space A hA
  let : CompactSpace (PointedQuotient R) := PointedQuotient.compactSpace R
  let : T2Space (PointedQuotient R) := PointedQuotient.t2Space R hR
  let k : C(PointedQuotient A, PointedQuotient R) :=
    PointedQuotient.mapContinuous A R (DoubleSpace.leftMap A) (DoubleSpace.left_mapsTo A)
  have hmem (x : X) : DoubleSpace.left A x ∈ R ↔ x ∈ A := by
    constructor
    · rintro ⟨y, hy⟩
      exact ((DoubleSpace.left_eq_right_iff A x y).mp hy.symm).2
    · intro hx
      exact DoubleSpace.left_mapsTo A hx
  -- Collapsing the right copy leaves exactly the original pointed quotient X/A.
  have hinj : Function.Injective k := by
    intro z w hzw
    rcases PointedQuotient.eq_basepoint_or_exists A z with rfl | ⟨x, rfl⟩ <;>
      rcases PointedQuotient.eq_basepoint_or_exists A w with rfl | ⟨y, rfl⟩
    · rfl
    · have hy : DoubleSpace.left A y ∈ R :=
        (PointedQuotient.of_eq_basepoint_iff R (DoubleSpace.left A y)).mp hzw.symm
      exact ((PointedQuotient.of_eq_basepoint_iff A y).mpr ((hmem y).mp hy)).symm
    · have hx : DoubleSpace.left A x ∈ R :=
        (PointedQuotient.of_eq_basepoint_iff R (DoubleSpace.left A x)).mp hzw
      exact (PointedQuotient.of_eq_basepoint_iff A x).mpr ((hmem x).mp hx)
    · rcases (PointedQuotient.of_eq_of_iff R _ _).mp hzw with hxy | ⟨hx, hy⟩
      · exact congrArg (PointedQuotient.of A) (DoubleSpace.left_injective A hxy)
      · exact (PointedQuotient.of_eq_of_iff A x y).mpr
          (Or.inr ⟨(hmem x).mp hx, (hmem y).mp hy⟩)
  have hsurj : Function.Surjective k := by
    intro z
    rcases PointedQuotient.eq_basepoint_or_exists R z with rfl | ⟨w, rfl⟩
    · exact ⟨PointedQuotient.basepoint A, rfl⟩
    induction w using Quotient.inductionOn with
    | h t =>
      cases t with
      | inl x => exact ⟨PointedQuotient.of A x, rfl⟩
      | inr x =>
        exact ⟨PointedQuotient.basepoint A,
          ((PointedQuotient.of_eq_basepoint_iff R (DoubleSpace.right A x)).mpr
            ⟨x, rfl⟩).symm⟩
  -- This very quotient map is a pointed homeomorphism by compactness and Hausdorffness.
  let e := (Equiv.ofBijective k ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
    k.continuous k.continuous.isClosedMap
  let g : C(PointedQuotient R, PointedQuotient A) := ⟨e.symm, e.symm.continuous⟩
  have hbase : g (PointedQuotient.basepoint R) = PointedQuotient.basepoint A :=
    e.symm_apply_eq.mpr rfl
  let inv : RelativeKZero A hA →+ RelativeKZero R hR :=
    reducedComplexKZeroPullback (PointedQuotient.basepoint R)
      (PointedQuotient.basepoint A) g hbase
  -- Its inverse pullback is inverse to the original left restriction on the same kernels.
  have hleft : Function.LeftInverse inv (DoubleSpace.relativeRestriction A hA) := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback g (complexKZeroPullback k a.val) = a.val
    have hid : k.comp g = ContinuousMap.id _ := by
      ext z
      exact e.apply_symm_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  have hright : Function.RightInverse inv (DoubleSpace.relativeRestriction A hA) := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback k (complexKZeroPullback g a.val) = a.val
    have hid : g.comp k = ContinuousMap.id _ := by
      ext z
      exact e.symm_apply_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  exact ⟨hleft.injective, hright.surjective⟩

/-- A map of pairs preserves the double relations. -/
theorem DoubleSpace.map_rel (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) (x y : X ⊕ X) (h : DoubleRel A x y) :
    DoubleRel B (Sum.map f f x) (Sum.map f f y) := by
  /- Equal base points have equal f-images. Equal representatives remain
  equal, and a seam point in A is sent into B by the map-of-pairs assumption. -/
  have hbase (z : X ⊕ X) :
      Sum.elim id id (Sum.map f f z) = f (Sum.elim id id z) := by
    cases z <;> rfl
  refine ⟨(hbase x).trans ((congrArg f h.1).trans (hbase y).symm), ?_⟩
  rcases h.2 with hxy | hx
  · exact Or.inl (congrArg (Sum.map f f) hxy)
  · exact Or.inr ((hbase x).symm ▸ hf hx)

/-- The actual map of doubles induced by a map of pairs. -/
def DoubleSpace.map (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) : DoubleSpace A → DoubleSpace B :=
  Quotient.map (Sum.map f f) (DoubleSpace.map_rel A B f hf)

/-- The induced map of doubles is continuous. -/
theorem DoubleSpace.continuous_map (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) : Continuous (DoubleSpace.map A B f hf) := by
  /- The sum of f with itself is continuous. Compose it with the target
  quotient and descend through the source quotient using its universal property. -/
  exact continuous_quot_map (DoubleSpace.map_rel A B f hf)
    (f.continuous.sumMap f.continuous)

/-- The induced map of doubles as a continuous map. -/
def DoubleSpace.mapContinuous (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) : C(DoubleSpace A, DoubleSpace B) :=
  ⟨DoubleSpace.map A B f hf, DoubleSpace.continuous_map A B f hf⟩

/-- The map of doubles applies f on the left copy. -/
theorem DoubleSpace.map_left (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) (x : X) :
    DoubleSpace.map A B f hf (DoubleSpace.left A x) = DoubleSpace.left B (f x) := by
  /- Evaluate the quotient map on the representative in the chosen summand.
  Its prequotient map applies f and preserves the summand, giving this formula. -/
  rfl

/-- The map of doubles applies f on the right copy. -/
theorem DoubleSpace.map_right (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) (x : X) :
    DoubleSpace.map A B f hf (DoubleSpace.right A x) = DoubleSpace.right B (f x) := by
  /- Evaluate the quotient map on the representative in the chosen summand.
  Its prequotient map applies f and preserves the summand, giving this formula. -/
  rfl

end AtiyahSinger

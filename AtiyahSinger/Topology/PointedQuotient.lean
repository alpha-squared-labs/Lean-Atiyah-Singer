/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportKZero

/-!
# Pointed quotient of a pair, including an empty subspace

Public module ID: M1991.

Collapse A together with a disjoint base point in X ⊕ PUnit.
The quotient topology is the actual coinduced topology. For compact Hausdorff X
and closed A it identifies with the one-point compactification of X minus A.
Sources: SG I.9, especially the relative group and I.9.26; Karoubi II.2.29–2.35.
No cofibration assumption is used for this compact Hausdorff quotient model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The subset collapsed to the base point in the disjoint pointed space. -/
def pairCollapsedSet (A : Set X) : Set (X ⊕ PUnit) :=
  Sum.inl '' A ∪ Set.range Sum.inr

/-- Identify equal points and identify all points in the collapsed subset. -/
def PairCollapseRel (A : Set X) (x y : X ⊕ PUnit) : Prop :=
  x = y ∨ (x ∈ pairCollapsedSet A ∧ y ∈ pairCollapsedSet A)


set_option linter.unusedSectionVars false in
/-- Collapsing one subset defines an equivalence relation. -/
theorem pairCollapseRel_equivalence (A : Set X) : Equivalence (PairCollapseRel A) := by
  /- Reflexivity follows from equality and symmetry exchanges the two membership
  conditions. For transitivity, equality cases reduce immediately; in the remaining
  case both endpoints belong to the collapsed subset. -/
  refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
  · intro x y h
    rcases h with h | ⟨hx, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hy, hx⟩
  · intro x y z hxy hyz
    rcases hxy with rfl | ⟨hx, hy⟩
    · exact hyz
    rcases hyz with rfl | ⟨hy, hz⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hz⟩

/-- The setoid identifying exactly the collapsed subset. -/
def pairCollapseSetoid (A : Set X) : Setoid (X ⊕ PUnit) :=
  ⟨PairCollapseRel A, pairCollapseRel_equivalence A⟩

/-- The pointed quotient, with a disjoint base point when A is empty. -/
abbrev PointedQuotient (A : Set X) : Type _ := Quotient (pairCollapseSetoid A)

/-- The distinguished class of the added point. -/
def PointedQuotient.basepoint (A : Set X) : PointedQuotient A :=
  Quotient.mk _ (Sum.inr PUnit.unit)

/-- The quotient map restricted to the original space. -/
def PointedQuotient.of (A : Set X) (x : X) : PointedQuotient A :=
  Quotient.mk _ (Sum.inl x)

/-- The original space maps continuously to its pointed quotient. -/
theorem PointedQuotient.continuous_of (A : Set X) : Continuous (PointedQuotient.of A) := by
  /- Compose the continuous inclusion of the left summand with the quotient map.
  The latter is continuous by the coinduced topology defining the quotient. -/
  exact continuous_quotient_mk'.comp continuous_inl

/-- Exactly the points in A map to the base point. -/
theorem PointedQuotient.of_eq_basepoint_iff (A : Set X) (x : X) :
    PointedQuotient.of A x = PointedQuotient.basepoint A ↔ x ∈ A := by
  /- Equality of quotient classes is precisely the collapse relation. The two sum
  constructors cannot be equal, so their equality in the quotient forces x into A. -/
  change Quotient.mk _ (Sum.inl x) = Quotient.mk _ (Sum.inr PUnit.unit) ↔ _
  rw [Quotient.eq]
  change PairCollapseRel A _ _ ↔ _
  simp [PairCollapseRel, pairCollapsedSet]

/-- Outside A no additional points are identified. -/
theorem PointedQuotient.of_eq_of_iff (A : Set X) (x y : X) :
    PointedQuotient.of A x = PointedQuotient.of A y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) := by
  /- Use effectiveness of the setoid quotient and expand the collapsed subset.
  A point of the left summand is collapsed exactly when its original point lies in A. -/
  change Quotient.mk _ (Sum.inl x) = Quotient.mk _ (Sum.inl y) ↔ _
  rw [Quotient.eq]
  change PairCollapseRel A _ _ ↔ _
  simp [PairCollapseRel, pairCollapsedSet]

/-- Each quotient point is the base point or comes from the original space. -/
theorem PointedQuotient.eq_basepoint_or_exists (A : Set X) (z : PointedQuotient A) :
    z = PointedQuotient.basepoint A ∨ ∃ x, z = PointedQuotient.of A x := by
  /- Choose a representative in the sum. A right-summand representative is the
  base point; a left-summand representative supplies the required original point. -/
  induction z using Quotient.inductionOn with
  | h z =>
    cases z with
    | inl x => exact Or.inr ⟨x, rfl⟩
    | inr u => exact Or.inl rfl

/-- A quotient of the compact pointed sum is compact. -/
theorem PointedQuotient.compactSpace [CompactSpace X] (A : Set X) :
    CompactSpace (PointedQuotient A) := by
  /- The disjoint union of compact X with one point is compact. Its surjective
  continuous quotient map transfers compactness to the quotient, without closedness of A. -/
  infer_instance

attribute [local instance] PointedQuotient.compactSpace

/-- A map of pairs respects the pointed collapse relations. -/
theorem PointedQuotient.map_rel (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) (x y : X ⊕ PUnit) (h : PairCollapseRel A x y) :
    PairCollapseRel B (Sum.map f id x) (Sum.map f id y) := by
  /- Equal representatives have equal images. For collapsed representatives the
  added point stays added and the pair condition carries points of A into B. -/
  rcases h with rfl | ⟨hx, hy⟩
  · exact Or.inl rfl
  have hmap : ∀ z ∈ pairCollapsedSet A, Sum.map f id z ∈ pairCollapsedSet B := by
    intro z hz
    cases z with
    | inl x =>
      have hx : x ∈ A := by simpa [pairCollapsedSet] using hz
      simpa [pairCollapsedSet] using hf hx
    | inr u => simp [pairCollapsedSet]
  exact Or.inr ⟨hmap x hx, hmap y hy⟩

/-- The actual map on pointed quotients induced by a map of pairs. -/
def PointedQuotient.map (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) : PointedQuotient A → PointedQuotient B :=
  Quotient.map (Sum.map f id) (PointedQuotient.map_rel A B f hf)

/-- The quotient map induced by a continuous map of pairs is continuous. -/
theorem PointedQuotient.continuous_map (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) : Continuous (PointedQuotient.map A B f hf) := by
  /- The sum of f and the identity point map is continuous. Compose with the
  target quotient map and apply the universal property of the source quotient topology. -/
  exact continuous_quot_map (PointedQuotient.map_rel A B f hf)
    (f.continuous.sumMap continuous_id)

/-- Bundle the induced pointed quotient map with its continuity certificate. -/
def PointedQuotient.mapContinuous (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) : C(PointedQuotient A, PointedQuotient B) :=
  ⟨PointedQuotient.map A B f hf, PointedQuotient.continuous_map A B f hf⟩

/-- The induced map preserves the added base point. -/
theorem PointedQuotient.map_basepoint (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) :
    PointedQuotient.map A B f hf (PointedQuotient.basepoint A) =
      PointedQuotient.basepoint B := by
  /- Evaluate the quotient map on the right-summand representative. The map
  on that summand is the identity, so the distinguished quotient class is preserved. -/
  rfl

/-- The induced map applies f to representatives from X. -/
theorem PointedQuotient.map_of (A : Set X) (B : Set Y) (f : C(X, Y))
    (hf : Set.MapsTo f A B) (x : X) :
    PointedQuotient.map A B f hf (PointedQuotient.of A x) =
      PointedQuotient.of B (f x) := by
  /- Evaluate Quotient.map on the representative Sum.inl x. The sum map sends
  it to Sum.inl (f x), which is precisely the stated representative in the target. -/
  rfl

/-- The pointed quotient is canonically the compactification of the complement. -/
theorem PointedQuotient.exists_onePoint_homeomorph [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    ∃ e : PointedQuotient A ≃ₜ OnePoint (Aᶜ : Set X),
      e (PointedQuotient.basepoint A) = ∞ ∧
        ∀ x : (Aᶜ : Set X), e (PointedQuotient.of A x) = (x : OnePoint (Aᶜ : Set X)) := by
  /- Send the collapsed class to infinity and each other class to its unique
  complement representative. Compact subsets of the open complement are closed
  in X, which verifies continuity at infinity. This is a continuous bijection
  from a compact space to a Hausdorff space, hence a homeomorphism, also when A is empty. -/
  classical
  let : LocallyCompactSpace (Aᶜ : Set X) := hA.isOpen_compl.locallyCompactSpace
  -- Construct the comparison on the pointed sum using the actual collapse map.
  let f : X ⊕ PUnit → OnePoint (Aᶜ : Set X) :=
    Sum.elim (fun x ↦ onePointCollapse Aᶜ (x : OnePoint X)) (fun _ ↦ ∞)
  have hf : Continuous f :=
    ((continuous_onePointCollapse Aᶜ hA.isOpen_compl).comp
      OnePoint.continuous_coe).sumElim continuous_const
  have hcollapsed : ∀ z ∈ pairCollapsedSet A, f z = ∞ := by
    intro z hz
    cases z with
    | inl x =>
      have hx : x ∈ A := by simpa [pairCollapsedSet] using hz
      simp [f, onePointCollapse, hx]
    | inr u => rfl
  have hrel : ∀ x y, PairCollapseRel A x y → f x = f y := by
    intro x y h
    rcases h with rfl | ⟨hx, hy⟩
    · rfl
    · exact (hcollapsed x hx).trans (hcollapsed y hy).symm
  let g : PointedQuotient A → OnePoint (Aᶜ : Set X) := Quotient.lift f hrel
  have hg : Continuous g := hf.quotient_lift hrel
  have hbase : g (PointedQuotient.basepoint A) = ∞ := rfl
  have hfinite (x : (Aᶜ : Set X)) : g (PointedQuotient.of A x) = ↑x := by
    change onePointCollapse Aᶜ (x.val : OnePoint X) = _
    have hx : (x : X) ∉ A := x.property
    simp [onePointCollapse, hx]
  -- The collapse relation is exactly the fiber relation, including the added point.
  have hrep : ∀ z : PointedQuotient A,
      z = PointedQuotient.basepoint A ∨
        ∃ x : (Aᶜ : Set X), z = PointedQuotient.of A x := by
    intro z
    rcases PointedQuotient.eq_basepoint_or_exists A z with hz | ⟨x, rfl⟩
    · exact Or.inl hz
    by_cases hx : x ∈ A
    · exact Or.inl ((PointedQuotient.of_eq_basepoint_iff A x).2 hx)
    · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  have hinj : Function.Injective g := by
    intro z w h
    rcases hrep z with rfl | ⟨x, rfl⟩ <;>
      rcases hrep w with rfl | ⟨y, rfl⟩
    · rfl
    · simp [hbase, hfinite] at h
    · simp [hbase, hfinite] at h
    · rw [hfinite, hfinite] at h
      have hxy : x = y := OnePoint.coe_injective h
      exact congrArg (fun a : (Aᶜ : Set X) ↦ PointedQuotient.of A a) hxy
  have hsurj : Function.Surjective g := by
    intro z
    induction z using OnePoint.rec with
    | infty => exact ⟨PointedQuotient.basepoint A, hbase⟩
    | coe x => exact ⟨PointedQuotient.of A x, hfinite x⟩
  -- Compactness makes this continuous bijection a homeomorphism.
  let e := (Equiv.ofBijective g ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
    hg hg.isClosedMap
  exact ⟨e, hbase, hfinite⟩

/-- Collapsing a closed subset of compact Hausdorff X gives a Hausdorff quotient. -/
theorem PointedQuotient.t2Space [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) : T2Space (PointedQuotient A) := by
  /- The explicit comparison identifies the quotient with the Hausdorff one-point
  compactification of the open complement, including when the subset is empty. -/
  let : LocallyCompactSpace (Aᶜ : Set X) := hA.isOpen_compl.locallyCompactSpace
  obtain ⟨e, _⟩ := PointedQuotient.exists_onePoint_homeomorph A hA
  exact e.symm.t2Space

/-- The chosen homeomorphism is constrained on every quotient class. -/
def PointedQuotient.onePointHomeomorph [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) : PointedQuotient A ≃ₜ OnePoint (Aᶜ : Set X) :=
  (PointedQuotient.exists_onePoint_homeomorph A hA).choose

/-- The compactification comparison preserves the base point. -/
theorem PointedQuotient.onePointHomeomorph_basepoint [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    PointedQuotient.onePointHomeomorph A hA (PointedQuotient.basepoint A) = ∞ := by
  /- Take the first characterization supplied by the homeomorphism existence
  theorem. It specifies the image of the additional point even for the empty subspace. -/
  exact (PointedQuotient.exists_onePoint_homeomorph A hA).choose_spec.1

/-- The comparison keeps every point of the open complement. -/
theorem PointedQuotient.onePointHomeomorph_of [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) (x : (Aᶜ : Set X)) :
    PointedQuotient.onePointHomeomorph A hA (PointedQuotient.of A x) =
      (x : OnePoint (Aᶜ : Set X)) := by
  /- Take the second characterization of the chosen homeomorphism. Thus later
  K-theory comparisons use the actual complement identification, not an arbitrary equivalence. -/
  exact (PointedQuotient.exists_onePoint_homeomorph A hA).choose_spec.2 x

end AtiyahSinger

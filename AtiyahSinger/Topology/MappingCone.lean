/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.PointedQuotient
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Mapping cylinders and unreduced mapping cones

Public module ID: M1957.

The mapping cylinder of `f : C(Y, X)` is the actual quotient of
`X ⊕ (Y × I)` identifying `(y, 0)` with `f y`. Its top is the image of `Y × {1}`.
The unreduced mapping cone is the pointed quotient of this top, so the cone tip
is retained even when `Y` is empty. This is Karoubi's `C′f`, not the reduced cone.

The quotient lifts specify all maps on representatives. The cylinder homotopy
equivalence uses the stated projection, inclusion, and the actual rescaling
`(y, t) ↦ (y, s * t)`. The cone tip is not declared to be the base point of
subsequent reduced K-groups: a pointed source map uses the image of `x₀ ∈ X`.

Source: Karoubi, *K-Theory*, II.3.28, printed pp. 79–80. Compactness and Hausdorff
certificates and the empty-source convention are explicit implementation details.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology
open scoped unitInterval

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Cylinder representatives are equal, or lie on the glued bottom with equal projections. -/
def MappingCylinderRel (f : C(Y, X)) (a b : X ⊕ (Y × I)) : Prop :=
  a = b ∨
    (Sum.elim (fun _ : X ↦ True) (fun yt : Y × I ↦ yt.2 = 0) a ∧
      Sum.elim (fun _ : X ↦ True) (fun yt : Y × I ↦ yt.2 = 0) b ∧
      Sum.elim id (fun yt : Y × I ↦ f yt.1) a =
        Sum.elim id (fun yt : Y × I ↦ f yt.1) b)

/-- The explicit bottom-gluing relation is an equivalence relation. -/
theorem mappingCylinderRel_equivalence (f : C(Y, X)) :
    Equivalence (MappingCylinderRel f) := by
  /- Equality handles reflexivity and the cases in which adjacent representatives
  coincide. In the remaining transitivity case all three representatives are on
  the bottom, and equality of their projections is transitive. Symmetry exchanges
  the two bottom-membership conditions and reverses the projection equality. -/
  refine ⟨fun _ ↦ Or.inl rfl, ?_, ?_⟩
  · intro a b h
    rcases h with h | ⟨ha, hb, hab⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hb, ha, hab.symm⟩
  · intro a b c hab hbc
    rcases hab with rfl | ⟨ha, hb, hab⟩
    · exact hbc
    rcases hbc with rfl | ⟨hb, hc, hbc⟩
    · exact Or.inr ⟨ha, hb, hab⟩
    · exact Or.inr ⟨ha, hc, hab.trans hbc⟩

/-- The setoid gluing the zero end of the cylinder to `X` along `f`. -/
def mappingCylinderSetoid (f : C(Y, X)) : Setoid (X ⊕ (Y × I)) :=
  ⟨MappingCylinderRel f, mappingCylinderRel_equivalence f⟩

/-- The mapping cylinder, with its coinduced quotient topology. -/
abbrev MappingCylinder (f : C(Y, X)) : Type _ := Quotient (mappingCylinderSetoid f)

/-- The continuous quotient map on the full representative space. -/
def mappingCylinderQuotient (f : C(Y, X)) : C(X ⊕ (Y × I), MappingCylinder f) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

/-- The inclusion of the base `X` into the mapping cylinder. -/
def mappingCylinderIn (f : C(Y, X)) : C(X, MappingCylinder f) :=
  (mappingCylinderQuotient f).comp ⟨Sum.inl, continuous_inl⟩

/-- The continuous map from the whole tube to the mapping cylinder. -/
def mappingCylinderTube (f : C(Y, X)) : C(Y × I, MappingCylinder f) :=
  (mappingCylinderQuotient f).comp ⟨Sum.inr, continuous_inr⟩

/-- The top inclusion uses the endpoint `1`, independently of the gluing map's fibers. -/
def mappingCylinderTop (f : C(Y, X)) : C(Y, MappingCylinder f) :=
  (mappingCylinderTube f).comp ⟨fun y ↦ (y, 1), continuous_id.prodMk continuous_const⟩

/-- Compatible maps on the base and tube descend to the actual mapping-cylinder quotient. -/
def mappingCylinderLift (f : C(Y, X)) (g : C(X, Z)) (h : C(Y × I, Z))
    (hglue : ∀ y : Y, h (y, 0) = g (f y)) : C(MappingCylinder f, Z) :=
  let hrel : ∀ a b, MappingCylinderRel f a b → Sum.elim g h a = Sum.elim g h b := by
    -- Every bottom representative has the prescribed value at its projection to X.
    have hbottom (a : X ⊕ (Y × I))
        (ha : Sum.elim (fun _ : X ↦ True) (fun yt : Y × I ↦ yt.2 = 0) a) :
        Sum.elim g h a = g (Sum.elim id (fun yt : Y × I ↦ f yt.1) a) := by
      cases a with
      | inl x => rfl
      | inr yt =>
        rcases yt with ⟨y, t⟩
        change t = 0 at ha
        subst t
        exact hglue y
    -- Equal representatives agree; glued representatives agree through their common projection.
    intro a b hab
    rcases hab with hab | ⟨ha, hb, hp⟩
    · exact congrArg (Sum.elim g h) hab
    · exact (hbottom a ha).trans ((congrArg g hp).trans (hbottom b hb).symm)
  { toFun := Quotient.lift (Sum.elim g h) hrel
    continuous_toFun := (g.continuous.sumElim h.continuous).quotient_lift hrel }

/-- The canonical cylinder projection is the identity on `X` and `f` on every tube slice. -/
def mappingCylinderProj (f : C(Y, X)) : C(MappingCylinder f, X) :=
  mappingCylinderLift f (ContinuousMap.id X) (f.comp ContinuousMap.fst) (fun _ ↦ rfl)

/-- The zero end is identified with its image under the original map. -/
theorem mappingCylinder_tube_zero (f : C(Y, X)) (y : Y) :
    mappingCylinderTube f (y, 0) = mappingCylinderIn f (f y) := by
  /- The two representatives lie on the glued bottom and have the same
  projection. Descend that explicit relation to equality in the quotient. -/
  exact Quotient.sound (Or.inr ⟨rfl, trivial, rfl⟩)

/-- The mapping cylinder of a map between compact spaces is compact. -/
theorem MappingCylinder.compactSpace [CompactSpace X] [CompactSpace Y] (f : C(Y, X)) :
    CompactSpace (MappingCylinder f) := by
  /- The interval and both source spaces are compact. The representative sum is
  therefore compact, and its continuous surjective quotient transfers compactness. -/
  infer_instance

attribute [local instance] MappingCylinder.compactSpace

/-- The mapping cylinder of a map between compact Hausdorff spaces is Hausdorff. -/
theorem MappingCylinder.t2Space [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (f : C(Y, X)) : T2Space (MappingCylinder f) := by
  /- Map the actual cylinder into X times the pointed quotient of Y × I by
  its bottom. The first coordinate records the original projection and the
  second records the tube point unless it lies on the bottom. Together they
  detect precisely the cylinder relation. This continuous injection into a
  Hausdorff product separates cylinder points without changing its topology. -/
  let A : Set (Y × I) := {p | p.2 = 0}
  have hA : IsClosed A := isClosed_singleton.preimage continuous_snd
  let : CompactSpace (PointedQuotient.{v, 0} A) := PointedQuotient.compactSpace A
  let : T2Space (PointedQuotient.{v, 0} A) := PointedQuotient.t2Space A hA
  let base : C(X, X × PointedQuotient.{v, 0} A) :=
    ⟨fun x ↦ (x, PointedQuotient.basepoint A), continuous_id.prodMk continuous_const⟩
  let tube : C(Y × I, X × PointedQuotient.{v, 0} A) :=
    ⟨fun yt ↦ (f yt.1, PointedQuotient.of A yt),
      (f.continuous.comp continuous_fst).prodMk (PointedQuotient.continuous_of A)⟩
  let k : C(MappingCylinder f, X × PointedQuotient.{v, 0} A) :=
    mappingCylinderLift f base tube (fun y ↦
      Prod.ext rfl ((PointedQuotient.of_eq_basepoint_iff A (y, 0)).2 rfl))
  -- Equality of the two actual coordinates recovers exactly the original gluing relation.
  have hinj : Function.Injective k := by
    intro a b h
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        apply Quotient.sound
        cases a with
        | inl x =>
          cases b with
          | inl y =>
            exact Or.inl (congrArg Sum.inl (congrArg Prod.fst h))
          | inr yt =>
            have hbottom : yt ∈ A :=
              (PointedQuotient.of_eq_basepoint_iff A yt).1 (congrArg Prod.snd h).symm
            exact Or.inr ⟨trivial, hbottom, congrArg Prod.fst h⟩
        | inr yt =>
          cases b with
          | inl x =>
            have hbottom : yt ∈ A :=
              (PointedQuotient.of_eq_basepoint_iff A yt).1 (congrArg Prod.snd h)
            exact Or.inr ⟨hbottom, trivial, congrArg Prod.fst h⟩
          | inr zs =>
            rcases (PointedQuotient.of_eq_of_iff A yt zs).1 (congrArg Prod.snd h) with
              heq | ⟨hy, hz⟩
            · exact Or.inl (congrArg Sum.inr heq)
            · exact Or.inr ⟨hy, hz, congrArg Prod.fst h⟩
  exact T2Space.of_injective_continuous hinj k.continuous

attribute [local instance] MappingCylinder.t2Space

/-- The base and top are disjoint closed embedded copies of their respective spaces. -/
theorem mappingCylinder_closedEmbeddings [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (f : C(Y, X)) :
    IsClosedEmbedding (mappingCylinderIn f) ∧
      IsClosedEmbedding (mappingCylinderTop f) ∧
      Disjoint (Set.range (mappingCylinderIn f)) (Set.range (mappingCylinderTop f)) := by
  /- At the base, the quotient relation preserves the `X` coordinate. At height
  one, it is simply equality, and no top point is related to a base point because
  `0 ≠ 1`. Thus both maps are injective with disjoint images. Compactness of the
  domains and the Hausdorff cylinder upgrade each continuous injection to a closed embedding. -/
  have hbase : Function.Injective (mappingCylinderIn f) := by
    intro x y h
    exact congrArg (mappingCylinderProj f) h
  have htop : Function.Injective (mappingCylinderTop f) := by
    intro y z h
    rcases Quotient.exact h with heq | ⟨hzero, _, _⟩
    · exact congrArg (fun yt : Y × I ↦ yt.1) (Sum.inr.inj heq)
    · exact (one_ne_zero hzero).elim
  refine ⟨(mappingCylinderIn f).continuous.isClosedEmbedding hbase,
    (mappingCylinderTop f).continuous.isClosedEmbedding htop, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  rcases Quotient.exact hy with heq | ⟨hzero, _, _⟩
  · change Sum.inr (y, (1 : I)) = Sum.inl x at heq
    cases heq
  · exact one_ne_zero hzero

/-- Rescale tube height by `s`, keeping the base fixed; at `s = 0` this is the retraction. -/
def mappingCylinderScale (f : C(Y, X)) (s : I) :
    C(MappingCylinder f, MappingCylinder f) :=
  mappingCylinderLift f (mappingCylinderIn f)
    ((mappingCylinderTube f).comp
      ⟨fun yt ↦ (yt.1, s * yt.2), continuous_fst.prodMk (continuous_const.mul continuous_snd)⟩)
    (by
      intro y
      simpa using mappingCylinder_tube_zero f y)

/-- The specified rescaling is a homotopy from inclusion after projection to the identity. -/
theorem mappingCylinder_scale_properties (f : C(Y, X)) :
    Continuous (fun p : I × MappingCylinder f ↦ mappingCylinderScale f p.1 p.2) ∧
      (∀ z : MappingCylinder f,
        mappingCylinderScale f 0 z = mappingCylinderIn f (mappingCylinderProj f z)) ∧
      (∀ z : MappingCylinder f, mappingCylinderScale f 1 z = z) ∧
      (∀ (s : I) (x : X), mappingCylinderScale f s (mappingCylinderIn f x) =
        mappingCylinderIn f x) := by
  /- On representatives the family fixes `X` and sends `(y,t)` to `(y,s*t)`,
  continuously in both variables. It respects the bottom identifications. The
  product of a quotient map with the locally compact interval is a quotient map,
  which supplies joint continuity without compactness assumptions on `X` or `Y`.
  At `s = 0` the tube lies on the glued bottom; at `s = 1` every representative is
  unchanged. The formula on `X` is constant for the entire homotopy. -/
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Descend joint continuity through the quotient in the second variable.
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    have hc : Continuous (Sum.elim
        (fun p : I × X ↦ mappingCylinderIn f p.2)
        (fun p : I × (Y × I) ↦ mappingCylinderTube f (p.2.1, p.1 * p.2.2))) :=
      ((mappingCylinderIn f).continuous.comp continuous_snd).sumElim
        ((mappingCylinderTube f).continuous.comp
          (continuous_snd.fst.prodMk (continuous_fst.mul continuous_snd.snd)))
    convert hc.comp (Homeomorph.prodSumDistrib
      (X := I) (Y := X) (Z := Y × I)).continuous using 1
    funext p
    rcases p with ⟨s, a⟩
    cases a <;> rfl
  · -- At zero every tube representative reaches its original glued base point.
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => rfl
      | inr yt =>
        change mappingCylinderTube f (yt.1, 0 * yt.2) = mappingCylinderIn f (f yt.1)
        simpa using mappingCylinder_tube_zero f yt.1
  · -- At one both sorts of representative are fixed.
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => rfl
      | inr yt =>
        change mappingCylinderTube f (yt.1, 1 * yt.2) = mappingCylinderTube f yt
        simp
  · intro s x
    rfl

/-- The actual zero-end cylinder contraction, traversed from the retraction to the identity. -/
def mappingCylinderHomotopy (f : C(Y, X)) :
    ContinuousMap.Homotopy ((mappingCylinderIn f).comp (mappingCylinderProj f))
      (ContinuousMap.id (MappingCylinder f)) where
  toFun := fun p ↦ mappingCylinderScale f p.1 p.2
  continuous_toFun := (mappingCylinder_scale_properties f).1
  map_zero_left := (mappingCylinder_scale_properties f).2.1
  map_one_left := (mappingCylinder_scale_properties f).2.2.1

/-- The specified projection and base inclusion are the mapping-cylinder homotopy equivalence. -/
def mappingCylinderHomotopyEquiv (f : C(Y, X)) :
    ContinuousMap.HomotopyEquiv (MappingCylinder f) X where
  toFun := mappingCylinderProj f
  invFun := mappingCylinderIn f
  left_inv := ⟨mappingCylinderHomotopy f⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩

/-- The unreduced mapping cone `C′f`, with a cone tip also for empty `Y`. -/
abbrev MappingCone (f : C(Y, X)) : Type (max u v) :=
  PointedQuotient.{max u v, 0} (Set.range (mappingCylinderTop f))

/-- Collapse the cylinder top to obtain the mapping cone. -/
def mappingConeQuotient (f : C(Y, X)) : C(MappingCylinder f, MappingCone f) :=
  ⟨PointedQuotient.of _, PointedQuotient.continuous_of _⟩

/-- The unchanged base `X` includes in the unreduced mapping cone. -/
def mappingConeIn (f : C(Y, X)) : C(X, MappingCone f) :=
  (mappingConeQuotient f).comp (mappingCylinderIn f)

/-- The tube descends to the mapping cone, with its entire top collapsed. -/
def mappingConeTube (f : C(Y, X)) : C(Y × I, MappingCone f) :=
  (mappingConeQuotient f).comp (mappingCylinderTube f)

/-- The cone tip; subsequent pointed K-groups may instead use the image of a base point of `X`. -/
def mappingConeTip (f : C(Y, X)) : MappingCone f :=
  PointedQuotient.basepoint _

/-- Base and tube maps descend to the cone when the tube is constant on its top. -/
def mappingConeLift (f : C(Y, X)) (g : C(X, Z)) (h : C(Y × I, Z)) (z : Z)
    (hglue : ∀ y : Y, h (y, 0) = g (f y)) (htop : ∀ y : Y, h (y, 1) = z) :
    C(MappingCone f, Z) :=
  let m : C(MappingCylinder f, Z) := mappingCylinderLift f g h hglue
  let hrel : ∀ a b, PairCollapseRel (Set.range (mappingCylinderTop f)) a b →
      Sum.elim m (fun _ : PUnit ↦ z) a = Sum.elim m (fun _ : PUnit ↦ z) b := by
    -- Every collapsed representative, including the added tip, has the specified value z.
    have hcollapsed (a : MappingCylinder f ⊕ PUnit)
        (ha : a ∈ pairCollapsedSet (Set.range (mappingCylinderTop f))) :
        Sum.elim m (fun _ : PUnit ↦ z) a = z := by
      rcases ha with ⟨p, hp, rfl⟩ | ⟨u, rfl⟩
      · rcases hp with ⟨y, rfl⟩
        exact htop y
      · rfl
    -- Constancy on the collapsed set is exactly the remaining quotient compatibility.
    intro a b hab
    rcases hab with hab | ⟨ha, hb⟩
    · exact congrArg (Sum.elim m (fun _ : PUnit ↦ z)) hab
    · exact (hcollapsed a ha).trans (hcollapsed b hb).symm
  { toFun := Quotient.lift (Sum.elim m (fun _ : PUnit ↦ z)) hrel
    continuous_toFun := (m.continuous.sumElim continuous_const).quotient_lift hrel }

/-- The cone tube has the original gluing map at zero and the single tip at one. -/
theorem mappingCone_tube_endpoints (f : C(Y, X)) (y : Y) :
    mappingConeTube f (y, 0) = mappingConeIn f (f y) ∧
      mappingConeTube f (y, 1) = mappingConeTip f := by
  /- The zero-end equality is the cylinder gluing equality followed by the cone
  quotient. The one-end representative lies in the top range, which is exactly
  the set collapsed to the added cone tip. -/
  refine ⟨congrArg (mappingConeQuotient f) (mappingCylinder_tube_zero f y), ?_⟩
  exact (PointedQuotient.of_eq_basepoint_iff (Set.range (mappingCylinderTop f))
    (mappingCylinderTop f y)).2 ⟨y, rfl⟩

/-- The unreduced mapping cone of a map between compact spaces is compact. -/
theorem MappingCone.compactSpace [CompactSpace X] [CompactSpace Y] (f : C(Y, X)) :
    CompactSpace (MappingCone f) := by
  /- The cylinder is compact, and its pointed quotient is compact even if the
  top range is empty; the latter case retains the added cone tip. -/
  exact PointedQuotient.compactSpace (Set.range (mappingCylinderTop f))

attribute [local instance] MappingCone.compactSpace

/-- The unreduced mapping cone of a map between compact Hausdorff spaces is Hausdorff. -/
theorem MappingCone.t2Space [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (f : C(Y, X)) : T2Space (MappingCone f) := by
  /- The top is closed in the compact Hausdorff mapping cylinder by its closed
  embedding certificate. Apply the Hausdorff theorem for the pointed quotient
  of a closed subspace. No pointed cofibration assumption is being made. -/
  exact PointedQuotient.t2Space (Set.range (mappingCylinderTop f))
    (mappingCylinder_closedEmbeddings f).2.1.isClosed_range

attribute [local instance] MappingCone.t2Space

/-- The cone retains a closed embedded copy of `X`, disjoint from the cone tip. -/
theorem mappingConeIn_closedEmbedding [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (f : C(Y, X)) :
    IsClosedEmbedding (mappingConeIn f) ∧
      mappingConeTip f ∉ Set.range (mappingConeIn f) := by
  /- The cylinder base is disjoint from the collapsed top, so the pointed
  quotient identifies neither two base points nor a base point with the tip.
  The resulting continuous injection from compact `X` into the Hausdorff cone is
  a closed embedding. This also covers the empty-source convention. -/
  have hdisj := (mappingCylinder_closedEmbeddings f).2.2
  have hnot (x : X) : mappingCylinderIn f x ∉ Set.range (mappingCylinderTop f) := by
    exact Set.disjoint_left.mp hdisj ⟨x, rfl⟩
  have hinj : Function.Injective (mappingConeIn f) := by
    intro x y h
    rcases (PointedQuotient.of_eq_of_iff (Set.range (mappingCylinderTop f))
      (mappingCylinderIn f x) (mappingCylinderIn f y)).1 h with heq | ⟨hx, _⟩
    · exact (mappingCylinder_closedEmbeddings f).1.injective heq
    · exact (hnot x hx).elim
  refine ⟨(mappingConeIn f).continuous.isClosedEmbedding hinj, ?_⟩
  rintro ⟨x, hx⟩
  exact hnot x ((PointedQuotient.of_eq_basepoint_iff
    (Set.range (mappingCylinderTop f)) (mappingCylinderIn f x)).1 hx)

end AtiyahSinger

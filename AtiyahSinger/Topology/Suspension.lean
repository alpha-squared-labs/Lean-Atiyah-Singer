/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.PointedQuotient
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Ordinary and reduced suspensions as actual quotient spaces

Public module ID: M2223.

Karoubi I.3.14 defines the ordinary suspension by collapsing the two ends of
the cylinder to two distinct poles. We use [0,1] instead of [-1,1], with the
lower end at 0. For nonempty spaces the two successive pointed quotients give
exactly that construction. Retaining both poles for the empty space is a
project extension of the convention, not an explicit assertion of I.3.14.
For a specified point, Karoubi II.2.41 defines the reduced suspension by
collapsing its whole meridian, thereby identifying the poles.

The carriers, continuous maps, and base points below are concrete quotient
constructions. The meridian is a closed contractible subspace for compact
Hausdorff inputs; its actual collapse supplies the comparison used in the
Puppe sequence. No equivalence between the ordinary and reduced spaces is
assumed. The proofs below retain the original quotient maps and both poles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

universe u v

namespace UnreducedSuspension

/-- The lower end of the cylinder, used in the first quotient. -/
def lowerEnd (X : Type u) : Set (X × I) := {p | p.2 = 0}

/-- The first quotient collapses the lower end and includes its pole when X is empty. -/
abbrev LowerCone (X : Type u) [TopologicalSpace X] : Type u :=
  PointedQuotient.{u, 0} (lowerEnd X)

/-- The upper end, as its actual image in the first quotient. -/
def upperEnd (X : Type u) [TopologicalSpace X] : Set (LowerCone X) :=
  Set.range (fun x : X ↦ PointedQuotient.of (lowerEnd X) (x, 1))

end UnreducedSuspension

/-- KA I.3.14: the ordinary suspension with two distinct poles. -/
abbrev UnreducedSuspension (X : Type u) [TopologicalSpace X] : Type u :=
  PointedQuotient.{u, 0} (UnreducedSuspension.upperEnd X)

namespace UnreducedSuspension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The lower pole, retained from the first quotient. -/
def south : UnreducedSuspension X :=
  PointedQuotient.of (upperEnd X) (PointedQuotient.basepoint (lowerEnd X))

/-- The upper pole is the distinguished point of the second quotient. -/
def north : UnreducedSuspension X :=
  PointedQuotient.basepoint (upperEnd X)

/-- The class of the cylinder point (x,t) in the ordinary suspension. -/
def of (x : X) (t : I) : UnreducedSuspension X :=
  PointedQuotient.of (upperEnd X) (PointedQuotient.of (lowerEnd X) (x, t))

/-- The actual continuous class map from the cylinder. -/
def ofMap : C(X × I, UnreducedSuspension X) where
  toFun p := of p.1 p.2
  continuous_toFun := (PointedQuotient.continuous_of (upperEnd X)).comp
    (PointedQuotient.continuous_of (lowerEnd X))

/-- The bottom of the cylinder is identified with the lower pole. -/
theorem of_zero (x : X) : of x 0 = south := by
  /- The first quotient identifies (x,0) with its added point because it lies
  in lowerEnd X. Apply the second quotient map to that equality. -/
  exact congrArg (PointedQuotient.of (upperEnd X))
    ((PointedQuotient.of_eq_basepoint_iff (lowerEnd X) (x, 0)).2 rfl)

/-- The top of the cylinder is identified with the upper pole. -/
theorem of_one (x : X) : of x 1 = north := by
  /- The first quotient class of (x,1) belongs to upperEnd X by its displayed
  representative. The second quotient therefore sends it to its added point. -/
  exact (PointedQuotient.of_eq_basepoint_iff (upperEnd X)
    (PointedQuotient.of (lowerEnd X) (x, 1))).2 ⟨x, rfl⟩

/-- The ordinary suspension has distinct poles, including when X is empty. -/
theorem south_ne_north : south (X := X) ≠ north := by
  /- Equality in the second quotient would place the first quotient's added
  point in the image of X × {1}. That would identify some (x,1) with the lower
  end in the first quotient, forcing 1 = 0 in the unit interval. -/
  intro h
  have hupper := (PointedQuotient.of_eq_basepoint_iff (upperEnd X)
    (PointedQuotient.basepoint (lowerEnd X))).1 h
  obtain ⟨x, hx⟩ := hupper
  have hzero := (PointedQuotient.of_eq_basepoint_iff (lowerEnd X) (x, 1)).1 hx
  exact one_ne_zero hzero

/-- The ordinary suspension of a compact space is compact. -/
theorem compactSpace [CompactSpace X] : CompactSpace (UnreducedSuspension X) := by
  /- The cylinder is compact because X and the interval are compact. Apply
  PointedQuotient.compactSpace to the lower-end quotient, then to its upper-end
  quotient. The added poles do not require a nonemptiness assumption. -/
  let : CompactSpace (LowerCone X) := PointedQuotient.compactSpace (lowerEnd X)
  exact PointedQuotient.compactSpace (upperEnd X)

/-- The ordinary suspension of a compact Hausdorff space is Hausdorff. -/
theorem t2Space [CompactSpace X] [T2Space X] : T2Space (UnreducedSuspension X) := by
  /- Stage 1: the lower end is closed, as the inverse image of {0} under the
  continuous second projection. Its pointed quotient is compact Hausdorff.
  Stage 2: the upper end is the continuous image of compact X in that Hausdorff
  quotient, so it is closed. A second application of PointedQuotient.t2Space
  gives the required Hausdorff topology, including when the upper end is empty. -/
  have hlower : IsClosed (lowerEnd X) := isClosed_singleton.preimage continuous_snd
  let : CompactSpace (LowerCone X) := PointedQuotient.compactSpace (lowerEnd X)
  let : T2Space (LowerCone X) := PointedQuotient.t2Space (lowerEnd X) hlower
  have htop : Continuous (fun x : X ↦ PointedQuotient.of (lowerEnd X) (x, 1)) :=
    (PointedQuotient.continuous_of (lowerEnd X)).comp
      (continuous_id.prodMk continuous_const)
  exact PointedQuotient.t2Space (upperEnd X) (isCompact_range htop).isClosed

/-- Suspend a continuous map by applying it to the spatial cylinder coordinate. -/
def map (f : C(X, Y)) : C(UnreducedSuspension X, UnreducedSuspension Y) :=
  let g : C(LowerCone X, LowerCone Y) :=
    PointedQuotient.mapContinuous (lowerEnd X) (lowerEnd Y)
      (f.prodMap (ContinuousMap.id I)) (fun _ h ↦ h)
  PointedQuotient.mapContinuous (upperEnd X) (upperEnd Y) g (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, rfl⟩)

/-- Suspension maps preserve the lower pole used for reduced K-theory. -/
theorem map_south (f : C(X, Y)) : map f south = south := by
  /- The inner quotient map preserves its added point, and the outer quotient
  map sends the class of that point to the corresponding class in the target. -/
  rfl

/-- Suspension maps preserve the upper pole. -/
theorem map_north (f : C(X, Y)) : map f north = north := by
  /- The outer quotient map preserves its own added point. This is the upper
  pole, independently of whether there are any cylinder representatives. -/
  rfl

/-- On cylinder representatives the suspended map acts by f on X. -/
theorem map_of (f : C(X, Y)) (x : X) (t : I) : map f (of x t) = of (f x) t := by
  /- Evaluate the two quotient maps successively on the two left-summand
  representatives. Their spatial map is f and their interval map is the identity. -/
  rfl

/-- The full meridian through a specified point, from the lower to the upper pole. -/
def meridian (x₀ : X) : C(I, UnreducedSuspension X) :=
  ofMap.comp ⟨fun t ↦ (x₀, t), continuous_const.prodMk continuous_id⟩

/-- The lower pole lies on every specified meridian. -/
theorem south_mem_range_meridian (x₀ : X) : south ∈ Set.range (meridian x₀) := by
  /- The parameter 0 supplies the range witness, since the lower endpoint of
  the specified meridian is the lower pole by of_zero. -/
  exact ⟨0, of_zero x₀⟩

attribute [local instance] compactSpace t2Space

/-- A meridian is closed in the ordinary suspension of a compact Hausdorff space. -/
theorem isClosed_range_meridian [CompactSpace X] [T2Space X] (x₀ : X) :
    IsClosed (Set.range (meridian x₀)) := by
  /- The interval is compact and the meridian map is continuous. Its compact
  image is closed in the Hausdorff ordinary suspension. -/
  exact (isCompact_range (meridian x₀).continuous).isClosed

/-- The meridian collapsed in KA II.2.41 is a contractible subspace. -/
theorem contractibleSpace_range_meridian [CompactSpace X] [T2Space X] (x₀ : X) :
    ContractibleSpace (Set.range (meridian x₀)) := by
  /- Stage 1: the meridian is injective. Equality of its two successive quotient
  classes only identifies equal interval parameters: the first quotient affects
  t = 0 and the second affects t = 1, and the two poles remain distinct.
  Stage 2: its continuous bijection from the compact interval onto its image
  in the Hausdorff suspension is a homeomorphism. Transfer the usual interval
  contraction to this image. The point x₀ is essential and makes X nonempty. -/
  -- Only the upper endpoint of a fixed meridian can belong to the upper collapsed set.
  have hupper (t : I)
      (ht : PointedQuotient.of (lowerEnd X) (x₀, t) ∈ upperEnd X) : t = 1 := by
    obtain ⟨x, hx⟩ := ht
    rcases (PointedQuotient.of_eq_of_iff (lowerEnd X) (x, 1) (x₀, t)).1 hx with
      heq | ⟨hzero, _⟩
    · exact (congrArg Prod.snd heq).symm
    · exact (one_ne_zero hzero).elim
  -- The two quotient relations preserve the parameter along this specified meridian.
  have hinj : Function.Injective (meridian x₀) := by
    intro s t h
    change PointedQuotient.of (upperEnd X) (PointedQuotient.of (lowerEnd X) (x₀, s)) =
      PointedQuotient.of (upperEnd X) (PointedQuotient.of (lowerEnd X) (x₀, t)) at h
    rcases (PointedQuotient.of_eq_of_iff (upperEnd X) _ _).1 h with
      hlower | ⟨hs, ht⟩
    · rcases (PointedQuotient.of_eq_of_iff (lowerEnd X) (x₀, s) (x₀, t)).1 hlower with
        heq | ⟨hs, ht⟩
      · exact congrArg Prod.snd heq
      · exact hs.trans ht.symm
    · exact (hupper s hs).trans (hupper t ht).symm
  -- A continuous injection from the compact interval identifies it with the actual range.
  let e := ((meridian x₀).continuous.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace
    ⟨0, le_rfl, zero_le_one⟩
  exact e.symm.contractibleSpace

end UnreducedSuspension

/-- KA II.2.41: collapse the whole distinguished meridian of the ordinary suspension. -/
abbrev ReducedSuspension {X : Type u} [TopologicalSpace X] (x₀ : X) : Type u :=
  PointedQuotient.{u, 0} (Set.range (UnreducedSuspension.meridian x₀))

namespace ReducedSuspension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The class of the distinguished meridian, including both poles. -/
def basepoint (x₀ : X) : ReducedSuspension x₀ :=
  PointedQuotient.basepoint (Set.range (UnreducedSuspension.meridian x₀))

/-- The actual quotient from the ordinary suspension to the reduced suspension. -/
def quotientMap (x₀ : X) : C(UnreducedSuspension X, ReducedSuspension x₀) :=
  ⟨PointedQuotient.of (Set.range (UnreducedSuspension.meridian x₀)),
    PointedQuotient.continuous_of (Set.range (UnreducedSuspension.meridian x₀))⟩

/-- Every point of the distinguished meridian becomes the reduced base point. -/
theorem quotientMap_meridian (x₀ : X) (t : I) :
    quotientMap x₀ (UnreducedSuspension.meridian x₀ t) = basepoint x₀ := by
  /- The meridian point belongs to the collapsed range with witness t. The
  defining pointed-quotient relation identifies its class with the base point. -/
  exact (PointedQuotient.of_eq_basepoint_iff
    (Set.range (UnreducedSuspension.meridian x₀)) _).2 ⟨t, rfl⟩

/-- The quotient is pointed when the ordinary suspension is based at its lower pole. -/
theorem quotientMap_south (x₀ : X) :
    quotientMap x₀ UnreducedSuspension.south = basepoint x₀ := by
  /- The lower pole belongs to the specified meridian. Apply the base-point
  characterization of the pointed quotient to that membership witness. -/
  exact (PointedQuotient.of_eq_basepoint_iff
    (Set.range (UnreducedSuspension.meridian x₀)) _).2
      (UnreducedSuspension.south_mem_range_meridian x₀)

/-- The reduced suspension of a compact space is compact. -/
theorem compactSpace [CompactSpace X] (x₀ : X) : CompactSpace (ReducedSuspension x₀) := by
  /- The ordinary suspension is compact by its two compact quotients. Apply
  PointedQuotient.compactSpace once more to the distinguished meridian. -/
  let : CompactSpace (UnreducedSuspension X) := UnreducedSuspension.compactSpace
  exact PointedQuotient.compactSpace (Set.range (UnreducedSuspension.meridian x₀))

/-- The reduced suspension of a compact Hausdorff space is Hausdorff. -/
theorem t2Space [CompactSpace X] [T2Space X] (x₀ : X) :
    T2Space (ReducedSuspension x₀) := by
  /- The ordinary suspension is compact Hausdorff and the meridian is closed.
  PointedQuotient.t2Space therefore supplies the Hausdorff quotient topology. -/
  let : CompactSpace (UnreducedSuspension X) := UnreducedSuspension.compactSpace
  let : T2Space (UnreducedSuspension X) := UnreducedSuspension.t2Space
  exact PointedQuotient.t2Space (Set.range (UnreducedSuspension.meridian x₀))
    (UnreducedSuspension.isClosed_range_meridian x₀)

/-- A pointed continuous map induces the actual map of reduced suspensions. -/
def map (f : C(X, Y)) (x₀ : X) (y₀ : Y) (hf₀ : f x₀ = y₀) :
    C(ReducedSuspension x₀, ReducedSuspension y₀) :=
  PointedQuotient.mapContinuous (Set.range (UnreducedSuspension.meridian x₀))
    (Set.range (UnreducedSuspension.meridian y₀)) (UnreducedSuspension.map f) (by
      rintro _ ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      change UnreducedSuspension.of y₀ t =
        UnreducedSuspension.map f (UnreducedSuspension.of x₀ t)
      rw [UnreducedSuspension.map_of, hf₀])

/-- The reduced suspension map preserves the collapsed meridian class. -/
theorem map_basepoint (f : C(X, Y)) (x₀ : X) (y₀ : Y) (hf₀ : f x₀ = y₀) :
    map f x₀ y₀ hf₀ (basepoint x₀) = basepoint y₀ := by
  /- The induced pointed-quotient map keeps the right-summand representative
  of the base point. Its value is the target meridian's distinguished class. -/
  rfl

/-- Reduction commutes with suspension of the same specified pointed map. -/
theorem map_quotientMap (f : C(X, Y)) (x₀ : X) (y₀ : Y) (hf₀ : f x₀ = y₀) :
    (map f x₀ y₀ hf₀).comp (quotientMap x₀) =
      (quotientMap y₀).comp (UnreducedSuspension.map f) := by
  /- Both sides send an ordinary suspension class to the class of its suspended
  image. This is the defining computation rule of the actual quotient map;
  the pointedness assumption ensures that the distinguished meridian is mapped
  into the target distinguished meridian. -/
  rfl

end ReducedSuspension

end AtiyahSinger

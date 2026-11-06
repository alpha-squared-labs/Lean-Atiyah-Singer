/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.PuppeSequence

/-!
# The reduced mapping cone and the second Puppe row

Public module ID: M2052.

The reduced cone collapses the actual y₀ meridian in C'f. Its bottom endpoint
is f(y₀), so the original pointed map condition is used when including (X,x₀).
Karoubi II.3.28 prints an x₀ interval here although the cylinder is Y×I; the
domain base point y₀ is the well-typed meridian in that construction.

The comparison maps from the reduced row to the unreduced row in K-theory are
pullbacks along actual quotient maps. Their bijectivity follows from the
independent contractible-collapse theorem. Their commuting squares transport
the first Puppe row to the second, as in II.3.29. These are comparisons between
two reduced K rows, not between reduced and absolute K groups.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual cone line over the chosen point of the domain of f. -/
def mappingConeMeridian (f : C(Y, X)) (y₀ : Y) : C(I, MappingCone f) :=
  ⟨fun t ↦ mappingConeTube f (y₀, t),
    (mappingConeTube f).continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Collapse the domain base-point meridian in the original unreduced mapping cone. -/
abbrev ReducedMappingCone (f : C(Y, X)) (y₀ : Y) : Type (max u v) :=
  PointedQuotient.{max u v, 0} (Set.range (mappingConeMeridian f y₀))

/-- The reduced cone's distinguished point is the collapsed meridian. -/
def ReducedMappingCone.basepoint (f : C(Y, X)) (y₀ : Y) : ReducedMappingCone f y₀ :=
  PointedQuotient.basepoint (Set.range (mappingConeMeridian f y₀))

/-- The bottom inclusion followed by the actual meridian quotient map. -/
def reducedMappingConeIn (f : C(Y, X)) (y₀ : Y) : C(X, ReducedMappingCone f y₀) :=
  (⟨PointedQuotient.of (Set.range (mappingConeMeridian f y₀)),
    PointedQuotient.continuous_of _⟩ : C(MappingCone f, ReducedMappingCone f y₀)).comp
      (mappingConeIn f)

/-- The cone collapse descends along the same meridian to the reduced suspension. -/
def reducedPuppeConeCollapse (f : C(Y, X)) (y₀ : Y) :
    C(ReducedMappingCone f y₀, ReducedSuspension y₀) :=
  PointedQuotient.mapContinuous (Set.range (mappingConeMeridian f y₀))
    (Set.range (UnreducedSuspension.meridian y₀)) (puppeConeCollapse f)
    (fun _ hx ↦ by
      rcases hx with ⟨t, rfl⟩
      exact ⟨t, rfl⟩)

attribute [local instance] MappingCylinder.compactSpace MappingCylinder.t2Space
  MappingCone.compactSpace MappingCone.t2Space
  UnreducedSuspension.compactSpace UnreducedSuspension.t2Space
  ReducedSuspension.compactSpace ReducedSuspension.t2Space PointedQuotient.compactSpace

/-- The specified meridian is a closed interval in the cone, hence contractible. -/
theorem mappingConeMeridian_closed_contractible [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (f : C(Y, X)) (y₀ : Y) :
    IsClosed (Set.range (mappingConeMeridian f y₀)) ∧
      ContractibleSpace (Set.range (mappingConeMeridian f y₀)) := by
  /- Stage 1: the actual cone quotient only identifies the zero end with its
  bottom point and the one end with its apex. Along this fixed y₀ line no two
  distinct times are identified. The continuous meridian is therefore a compact
  interval embedded in the Hausdorff cone, with closed range.
  Stage 2: its inverse on the range is the time coordinate. This coordinate
  itself descends by the cone universal property, taking value zero on X and
  one at the apex. The resulting homeomorphism from the range to I transports
  the usual interval contraction. Neither an arbitrary contractible substitute
  nor a homotopy-equivalence assumption about the quotient space is used. -/
  -- The original cone lift reads height, including zero on the base and one at the apex.
  let height : C(MappingCone f, I) :=
    mappingConeLift f (ContinuousMap.const X 0) ContinuousMap.snd 1
      (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hheight (t : I) : height (mappingConeMeridian f y₀ t) = t := rfl
  have hinj : Function.Injective (mappingConeMeridian f y₀) := by
    intro s t h
    exact (hheight s).symm.trans ((congrArg height h).trans (hheight t))
  -- Its continuous injection identifies the fixed meridian with the actual compact interval.
  have he := (mappingConeMeridian f y₀).continuous.isClosedEmbedding hinj
  let e := he.isEmbedding.toHomeomorph
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace
    ⟨0, le_rfl, zero_le_one⟩
  exact ⟨he.isClosed_range, e.symm.contractibleSpace⟩

/-- The reduced cone is compact as an actual quotient of the compact cone plus one point. -/
theorem ReducedMappingCone.compactSpace [CompactSpace X] [CompactSpace Y]
    (f : C(Y, X)) (y₀ : Y) :
    CompactSpace (ReducedMappingCone f y₀) := by
  /- Apply PointedQuotient.compactSpace to the meridian subset in the compact
  cone. The quotient formula is the already specified ReducedMappingCone. -/
  exact PointedQuotient.compactSpace (Set.range (mappingConeMeridian f y₀))

/-- The reduced cone is Hausdorff because its collapsed meridian is closed. -/
theorem ReducedMappingCone.t2Space [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (f : C(Y, X)) (y₀ : Y) :
    T2Space (ReducedMappingCone f y₀) := by
  /- Use the closedness component of mappingConeMeridian_closed_contractible
  and PointedQuotient.t2Space on the original compact Hausdorff cone. -/
  exact PointedQuotient.t2Space (Set.range (mappingConeMeridian f y₀))
    (mappingConeMeridian_closed_contractible f y₀).1

attribute [local instance] ReducedMappingCone.compactSpace ReducedMappingCone.t2Space

variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- Collapse of the specified suspension meridian induces this exact reduced K equivalence. -/
def ReducedSuspension.kZeroEquiv (x₀ : X) :
    reducedComplexKZero (ReducedSuspension.basepoint x₀) ≃+
      reducedComplexKZero (UnreducedSuspension.south (X := X)) :=
  letI := UnreducedSuspension.contractibleSpace_range_meridian x₀
  reducedComplexKZeroCollapseEquiv (Set.range (UnreducedSuspension.meridian x₀))
    (UnreducedSuspension.isClosed_range_meridian x₀) UnreducedSuspension.south
    (UnreducedSuspension.south_mem_range_meridian x₀)

/-- Collapse of the same cone meridian induces the equivalence at the bottom base point. -/
def ReducedMappingCone.kZeroEquiv (f : C(Y, X)) (y₀ : Y)
    (x₀ : X) (hf₀ : f y₀ = x₀) :
    reducedComplexKZero (ReducedMappingCone.basepoint f y₀) ≃+
      reducedComplexKZero (mappingConeIn f x₀) :=
  letI := (mappingConeMeridian_closed_contractible f y₀).2
  reducedComplexKZeroCollapseEquiv (Set.range (mappingConeMeridian f y₀))
    (mappingConeMeridian_closed_contractible f y₀).1 (mappingConeIn f x₀)
    ⟨0, (mappingCone_tube_endpoints f y₀).1.trans (congrArg (mappingConeIn f) hf₀)⟩

/-- Reduced K pullback along the actual bottom inclusion into the reduced cone. -/
def reducedPuppeConeRestriction (f : C(Y, X)) (y₀ : Y) (x₀ : X) (hf₀ : f y₀ = x₀) :
    reducedComplexKZero (ReducedMappingCone.basepoint f y₀) →+ reducedComplexKZero x₀ :=
  reducedComplexKZeroPullback x₀ (ReducedMappingCone.basepoint f y₀)
    (reducedMappingConeIn f y₀)
    ((PointedQuotient.of_eq_basepoint_iff _ _).2
      ⟨0, (mappingCone_tube_endpoints f y₀).1.trans (congrArg (mappingConeIn f) hf₀)⟩)

/-- Reduced K pullback along the same meridian-induced cone collapse. -/
def reducedPuppeConeCollapsePullback (f : C(Y, X)) (y₀ : Y) :
    reducedComplexKZero (ReducedSuspension.basepoint y₀) →+
      reducedComplexKZero (ReducedMappingCone.basepoint f y₀) :=
  reducedComplexKZeroPullback (ReducedMappingCone.basepoint f y₀)
    (ReducedSuspension.basepoint y₀) (reducedPuppeConeCollapse f y₀) rfl

/-- Reduced K pullback along the pointed reduced suspension of the original map. -/
def reducedPuppeSuspensionPullback (f : C(Y, X)) (y₀ : Y) (x₀ : X) (hf₀ : f y₀ = x₀) :
    reducedComplexKZero (ReducedSuspension.basepoint x₀) →+
      reducedComplexKZero (ReducedSuspension.basepoint y₀) :=
  reducedComplexKZeroPullback (ReducedSuspension.basepoint y₀)
    (ReducedSuspension.basepoint x₀) (ReducedSuspension.map f y₀ x₀ hf₀)
    (ReducedSuspension.map_basepoint f y₀ x₀ hf₀)

/-- The three actual quotient comparisons form the natural diagram of the two Puppe rows. -/
theorem puppe_reduction_natural (f : C(Y, X)) (y₀ : Y) (x₀ : X) (hf₀ : f y₀ = x₀) :
    (puppeConeRestriction f x₀).comp
        (ReducedMappingCone.kZeroEquiv f y₀ x₀ hf₀).toAddMonoidHom =
      reducedPuppeConeRestriction f y₀ x₀ hf₀ ∧
    (ReducedMappingCone.kZeroEquiv f y₀ x₀ hf₀).toAddMonoidHom.comp
        (reducedPuppeConeCollapsePullback f y₀) =
      (puppeConeCollapsePullback f x₀).comp
        (ReducedSuspension.kZeroEquiv y₀).toAddMonoidHom ∧
    (ReducedSuspension.kZeroEquiv y₀).toAddMonoidHom.comp
        (reducedPuppeSuspensionPullback f y₀ x₀ hf₀) =
      (puppeSuspensionPullback f).comp (ReducedSuspension.kZeroEquiv x₀).toAddMonoidHom := by
  /- Stage 1: on points the cone meridian quotient commutes with the bottom
  inclusion. The reduced cone-collapse map was defined by the same quotient
  universal property, so its square with C'f → S'Y commutes on every tube and
  bottom representative and at the apex. The suspension square is the specified
  ReducedSuspension.map_quotientMap identity for the same f and base points.
  Stage 2: contravariant pullback changes these commuting continuous-map squares
  into the displayed three homomorphism equalities. Every kZeroEquiv has exactly
  the quotient pullback as forward map; its inverse is not substituted here.
  Equality in the reduced subgroup follows from equality of absolute classes.
  No interval reversal occurs in these three meridian quotient squares. -/
  constructor
  · apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    let q : C(MappingCone f, ReducedMappingCone f y₀) :=
      ⟨PointedQuotient.of (Set.range (mappingConeMeridian f y₀)),
        PointedQuotient.continuous_of _⟩
    -- The forward equivalence is exactly pullback by this meridian quotient.
    change complexKZeroPullback (mappingConeIn f) (complexKZeroPullback q a.val) =
      complexKZeroPullback (reducedMappingConeIn f y₀) a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  constructor
  · apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    let qC : C(MappingCone f, ReducedMappingCone f y₀) :=
      ⟨PointedQuotient.of (Set.range (mappingConeMeridian f y₀)),
        PointedQuotient.continuous_of _⟩
    let qS := ReducedSuspension.quotientMap y₀
    change complexKZeroPullback qC
      (complexKZeroPullback (reducedPuppeConeCollapse f y₀) a.val) =
        complexKZeroPullback (puppeConeCollapse f) (complexKZeroPullback qS a.val)
    -- The induced cone collapse retains every original quotient representative.
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  · apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    let qX := ReducedSuspension.quotientMap x₀
    let qY := ReducedSuspension.quotientMap y₀
    change complexKZeroPullback qY
      (complexKZeroPullback (ReducedSuspension.map f y₀ x₀ hf₀) a.val) =
        complexKZeroPullback (UnreducedSuspension.map f) (complexKZeroPullback qX a.val)
    -- Suspension and meridian reduction use the same f, so this square has no sign change.
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl

/-- KA II.3.29, reduced row: exactness at reduced K⁰(X). -/
theorem range_reducedPuppeConeRestriction (f : C(Y, X)) (y₀ : Y)
    (x₀ : X) (hf₀ : f y₀ = x₀) :
    (reducedPuppeConeRestriction f y₀ x₀ hf₀).range =
      (reducedComplexKZeroPullback y₀ x₀ f hf₀).ker := by
  /- Use the first commuting square of puppe_reduction_natural. Its cone
  comparison is the bijective pullback along the contractible meridian collapse.
  Therefore its image equals the unreduced-cone restriction image, which is
  the stated kernel by range_puppeConeRestriction. -/
  let eC := ReducedMappingCone.kZeroEquiv f y₀ x₀ hf₀
  have hs := (puppe_reduction_natural f y₀ x₀ hf₀).1
  have hpoint (a : reducedComplexKZero (ReducedMappingCone.basepoint f y₀)) :
      puppeConeRestriction f x₀ (eC a) = reducedPuppeConeRestriction f y₀ x₀ hf₀ a :=
    DFunLike.congr_fun hs a
  -- The same actual cone-quotient equivalence preserves the restriction image.
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    have hz : puppeConeRestriction f x₀ (eC b) ∈ (puppeConeRestriction f x₀).range :=
      ⟨eC b, rfl⟩
    rw [range_puppeConeRestriction f y₀ x₀ hf₀, hpoint b] at hz
    exact hz
  · intro a ha
    rw [← range_puppeConeRestriction f y₀ x₀ hf₀] at ha
    obtain ⟨b, hb⟩ := ha
    refine ⟨eC.symm b, ?_⟩
    calc
      reducedPuppeConeRestriction f y₀ x₀ hf₀ (eC.symm b) =
          puppeConeRestriction f x₀ (eC (eC.symm b)) := (hpoint _).symm
      _ = puppeConeRestriction f x₀ b := congrArg _ (eC.apply_symm_apply b)
      _ = a := hb

/-- KA II.3.29, reduced row: exactness at reduced K⁰ of the reduced cone. -/
theorem range_reducedPuppeConeCollapsePullback (f : C(Y, X)) (y₀ : Y)
    (x₀ : X) (hf₀ : f y₀ = x₀) :
    (reducedPuppeConeCollapsePullback f y₀).range =
      (reducedPuppeConeRestriction f y₀ x₀ hf₀).ker := by
  /- Transport range_puppeConeCollapsePullback through the cone and Y-suspension
  comparison isomorphisms. The first two naturality squares identify both maps
  with these actual reduced-row maps, so the transported image and kernel are
  precisely the displayed subgroups. -/
  let eC := ReducedMappingCone.kZeroEquiv f y₀ x₀ hf₀
  let eY := ReducedSuspension.kZeroEquiv y₀
  have hs := puppe_reduction_natural f y₀ x₀ hf₀
  have hrestriction (a : reducedComplexKZero (ReducedMappingCone.basepoint f y₀)) :
      puppeConeRestriction f x₀ (eC a) = reducedPuppeConeRestriction f y₀ x₀ hf₀ a :=
    DFunLike.congr_fun hs.1 a
  have hcollapse (a : reducedComplexKZero (ReducedSuspension.basepoint y₀)) :
      eC (reducedPuppeConeCollapsePullback f y₀ a) = puppeConeCollapsePullback f x₀ (eY a) :=
    DFunLike.congr_fun hs.2.1 a
  -- Both arrows are compared through their original meridian quotients, at the same points.
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    have hz : puppeConeCollapsePullback f x₀ (eY b) ∈
        (puppeConeCollapsePullback f x₀).range := ⟨eY b, rfl⟩
    rw [range_puppeConeCollapsePullback f y₀ x₀ hf₀] at hz
    change reducedPuppeConeRestriction f y₀ x₀ hf₀
      (reducedPuppeConeCollapsePullback f y₀ b) = 0
    calc
      reducedPuppeConeRestriction f y₀ x₀ hf₀ (reducedPuppeConeCollapsePullback f y₀ b) =
          puppeConeRestriction f x₀ (eC (reducedPuppeConeCollapsePullback f y₀ b)) :=
        (hrestriction _).symm
      _ = puppeConeRestriction f x₀ (puppeConeCollapsePullback f x₀ (eY b)) :=
        congrArg _ (hcollapse b)
      _ = 0 := hz
  · intro a ha
    have hz : eC a ∈ (puppeConeRestriction f x₀).ker := by
      change puppeConeRestriction f x₀ (eC a) = 0
      exact (hrestriction a).trans ha
    rw [← range_puppeConeCollapsePullback f y₀ x₀ hf₀] at hz
    obtain ⟨b, hb⟩ := hz
    refine ⟨eY.symm b, eC.injective ?_⟩
    calc
      eC (reducedPuppeConeCollapsePullback f y₀ (eY.symm b)) =
          puppeConeCollapsePullback f x₀ (eY (eY.symm b)) := hcollapse _
      _ = puppeConeCollapsePullback f x₀ b := congrArg _ (eY.apply_symm_apply b)
      _ = eC a := hb

/-- KA II.3.29, reduced row: exactness at reduced K⁰ of the reduced suspension of Y. -/
theorem range_reducedPuppeSuspensionPullback (f : C(Y, X)) (y₀ : Y)
    (x₀ : X) (hf₀ : f y₀ = x₀) :
    (reducedPuppeSuspensionPullback f y₀ x₀ hf₀).range =
      (reducedPuppeConeCollapsePullback f y₀).ker := by
  /- Use the last two naturality squares and the cone and two suspension
  comparison isomorphisms. They transport range_puppeSuspensionPullback to this
  exactness position. All comparisons are actual meridian collapses with their
  fixed pole convention; no separate sign or arbitrary equivalence is inserted. -/
  let eC := ReducedMappingCone.kZeroEquiv f y₀ x₀ hf₀
  let eX := ReducedSuspension.kZeroEquiv x₀
  let eY := ReducedSuspension.kZeroEquiv y₀
  have hs := puppe_reduction_natural f y₀ x₀ hf₀
  have hcollapse (a : reducedComplexKZero (ReducedSuspension.basepoint y₀)) :
      eC (reducedPuppeConeCollapsePullback f y₀ a) = puppeConeCollapsePullback f x₀ (eY a) :=
    DFunLike.congr_fun hs.2.1 a
  have hsuspension (a : reducedComplexKZero (ReducedSuspension.basepoint x₀)) :
      eY (reducedPuppeSuspensionPullback f y₀ x₀ hf₀ a) = puppeSuspensionPullback f (eX a) :=
    DFunLike.congr_fun hs.2.2 a
  -- The last two commuting squares transport this kernel and its specified suspension lifts.
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    have hz : puppeSuspensionPullback f (eX b) ∈ (puppeSuspensionPullback f).range :=
      ⟨eX b, rfl⟩
    rw [range_puppeSuspensionPullback f y₀ x₀ hf₀] at hz
    change reducedPuppeConeCollapsePullback f y₀
      (reducedPuppeSuspensionPullback f y₀ x₀ hf₀ b) = 0
    apply eC.injective
    calc
      eC (reducedPuppeConeCollapsePullback f y₀
          (reducedPuppeSuspensionPullback f y₀ x₀ hf₀ b)) =
            puppeConeCollapsePullback f x₀ (eY (reducedPuppeSuspensionPullback f y₀ x₀ hf₀ b)) :=
        hcollapse _
      _ = puppeConeCollapsePullback f x₀ (puppeSuspensionPullback f (eX b)) :=
        congrArg _ (hsuspension b)
      _ = 0 := hz
      _ = eC 0 := (map_zero eC).symm
  · intro a ha
    have hz : eY a ∈ (puppeConeCollapsePullback f x₀).ker := by
      change puppeConeCollapsePullback f x₀ (eY a) = 0
      exact (hcollapse a).symm.trans ((congrArg eC ha).trans (map_zero eC))
    rw [← range_puppeSuspensionPullback f y₀ x₀ hf₀] at hz
    obtain ⟨b, hb⟩ := hz
    refine ⟨eX.symm b, eY.injective ?_⟩
    calc
      eY (reducedPuppeSuspensionPullback f y₀ x₀ hf₀ (eX.symm b)) =
          puppeSuspensionPullback f (eX (eX.symm b)) := hsuspension _
      _ = puppeSuspensionPullback f b := congrArg _ (eX.apply_symm_apply b)
      _ = eY a := hb

end AtiyahSinger

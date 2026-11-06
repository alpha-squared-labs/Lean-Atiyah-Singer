/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportHomotopy
public import Mathlib.Topology.LocalAtTarget

/-!
# Change of coordinates and proper base change for compact supports

Public module ID: M1674.

D07/K02. These maps use the actual one-point extensions and open collapses.
Sources: Karoubi II.4.1–4.3 and SG I.9.26. Proper base change retains the properness
of the original map; a general continuous pullback does not preserve compact support.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint
open scoped unitInterval Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


/-- Restrict a continuous map to the inverse image of an open-subspace carrier. -/
def preimageSubspaceMap (U : Set Y) (f : C(X, Y)) : C(f ⁻¹' U, U) :=
  ⟨fun x ↦ ⟨f x, x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Restriction over a subspace preserves properness. -/
theorem isProperMap_preimageSubspaceMap (U : Set Y) (f : C(X, Y)) (hf : IsProperMap f) :
    IsProperMap (preimageSubspaceMap U f) := by
  /- The restriction square is a pullback square of topological spaces. Proper maps are stable
  under base change, so restriction to the inverse-image subspace remains proper. Openness,
  local compactness and separation are not needed for this statement. -/
  exact hf.restrictPreimage U

set_option linter.unusedSectionVars false in
/-- Open collapse sends the original infinity to infinity. -/
theorem onePointCollapse_infty (U : Set X) : onePointCollapse U ∞ = ∞ := by
  /- Evaluate the explicit OnePoint eliminator on infinity. Its infinity branch is the target
  infinity independently of any openness or local compactness hypotheses. -/
  rfl

set_option linter.unusedSectionVars false in
/-- Open collapse keeps a point of its subspace. -/
theorem onePointCollapse_coe_of_mem (U : Set X) (x : X) (hx : x ∈ U) :
    onePointCollapse U (x : OnePoint X) = (⟨x, hx⟩ : U) := by
  /- Evaluate the finite branch of the collapse function. Membership selects the first branch,
  which inserts this same point into the one-point compactification of U. -/
  simp [onePointCollapse, hx]

set_option linter.unusedSectionVars false in
/-- Open collapse sends every point outside its subspace to infinity. -/
theorem onePointCollapse_coe_of_notMem (U : Set X) (x : X) (hx : x ∉ U) :
    onePointCollapse U (x : OnePoint X) = ∞ := by
  /- In the finite branch the membership test is false. The defining formula therefore takes
  its infinity value; no separation or continuity assumption is involved. -/
  simp [onePointCollapse, hx]

variable [hLX : LocallyCompactSpace X] [hTX : T2Space X]
  [hLY : LocallyCompactSpace Y] [hTY : T2Space Y]

include hLX hTX hLY hTY

/-- Transport compactly supported classes by inverse pullback along a homeomorphism. -/
def compactSupportKZeroHomeomorph (e : X ≃ₜ Y) : CompactSupportKZero X →+ CompactSupportKZero Y :=
  compactSupportKZeroPullback ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap

/-- The homeomorphism transport is bijective. -/
theorem compactSupportKZeroHomeomorph_bijective (e : X ≃ₜ Y) :
    Function.Bijective (compactSupportKZeroHomeomorph e) := by
  /- Pullback along e is inverse to pullback along its inverse. Proper pullback composition and
  identity formulas show the two composites are identities on reduced K groups, so the
  specified transport is bijective. -/
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let g : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  have hfg : g.comp f = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  have hgf : f.comp g = ContinuousMap.id Y := by
    ext y
    exact e.apply_symm_apply y
  -- These are the original inverse pullbacks, with the same homeomorphisms as witnesses.
  have hleft : (compactSupportKZeroHomeomorph e.symm).comp
      (compactSupportKZeroHomeomorph e) = AddMonoidHom.id (CompactSupportKZero X) := by
    change (compactSupportKZeroPullback f e.isProperMap).comp
      (compactSupportKZeroPullback g e.symm.isProperMap) = _
    rw [← compactSupportKZeroPullback_comp]
    simpa only [hfg] using (compactSupportKZeroPullback_id (X := X))
  have hright : (compactSupportKZeroHomeomorph e).comp
      (compactSupportKZeroHomeomorph e.symm) = AddMonoidHom.id (CompactSupportKZero Y) := by
    change (compactSupportKZeroPullback g e.symm.isProperMap).comp
      (compactSupportKZeroPullback f e.isProperMap) = _
    rw [← compactSupportKZeroPullback_comp]
    simpa only [hgf] using (compactSupportKZeroPullback_id (X := Y))
  exact ⟨(show Function.LeftInverse (compactSupportKZeroHomeomorph e.symm)
      (compactSupportKZeroHomeomorph e) from
        fun a ↦ DFunLike.congr_fun hleft a).injective,
    (show Function.RightInverse (compactSupportKZeroHomeomorph e.symm)
      (compactSupportKZeroHomeomorph e) from
        fun a ↦ DFunLike.congr_fun hright a).surjective⟩

/-- The equivalence keeps the specified inverse pullback as forward map. -/
def compactSupportKZeroHomeomorphEquiv (e : X ≃ₜ Y) :
    CompactSupportKZero X ≃+ CompactSupportKZero Y :=
  AddEquiv.ofBijective _ (compactSupportKZeroHomeomorph_bijective e)

/-- Homeomorphism transport followed by inverse transport is identity. -/
theorem compactSupportKZeroHomeomorph_symm (e : X ≃ₜ Y) :
    (compactSupportKZeroHomeomorph e.symm).comp (compactSupportKZeroHomeomorph e) =
      AddMonoidHom.id (CompactSupportKZero X) := by
  /- The two inverse homeomorphisms compose to the identity at every finite point and at
  infinity. Apply contravariant functoriality of the actual reduced pullback maps. -/
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let g : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  have hfg : g.comp f = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  change (compactSupportKZeroPullback f e.isProperMap).comp
    (compactSupportKZeroPullback g e.symm.isProperMap) = _
  rw [← compactSupportKZeroPullback_comp]
  simpa only [hfg] using (compactSupportKZeroPullback_id (X := X))

/-- Proper pullback commutes with open extension over the inverse-image subspace. -/
theorem compactSupportKZeroPullback_openExtension (U : Set Y) (hU : IsOpen U)
    (f : C(X, Y)) (hf : IsProperMap f) :
    letI := hU.locallyCompactSpace
    letI := (hU.preimage f.continuous).locallyCompactSpace
    (compactSupportKZeroPullback f hf).comp (compactSupportKZeroOpenExtension U hU) =
      (compactSupportKZeroOpenExtension (f ⁻¹' U) (hU.preimage f.continuous)).comp
        (compactSupportKZeroPullback (preimageSubspaceMap U f)
          (isProperMap_preimageSubspaceMap U f hf)) := by
  /- The compactification square formed by f and the two open collapses commutes: a finite
  point is retained on both routes exactly when its image belongs to U, and infinity maps to
  infinity. Restriction of the proper map is proper, so all four pullbacks are defined.
  Functoriality gives the equality of homomorphisms. -/
  let := hU.locallyCompactSpace
  let := (hU.preimage f.continuous).locallyCompactSpace
  let cY : C(OnePoint Y, OnePoint U) := ⟨onePointCollapse U,
    continuous_onePointCollapse U hU⟩
  let cX : C(OnePoint X, OnePoint (f ⁻¹' U)) := ⟨onePointCollapse (f ⁻¹' U),
    continuous_onePointCollapse (f ⁻¹' U) (hU.preimage f.continuous)⟩
  let F := properOnePointMap f hf
  let G := properOnePointMap (preimageSubspaceMap U f) (isProperMap_preimageSubspaceMap U f hf)
  -- The same finite point is retained exactly when its image lies in U.
  have hsquare : cY.comp F = G.comp cX := by
    ext z
    change onePointCollapse U (OnePoint.map f z) =
      OnePoint.map (preimageSubspaceMap U f) (onePointCollapse (f ⁻¹' U) z)
    cases z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      by_cases hx : f x ∈ U
      · rw [OnePoint.map_some, onePointCollapse_coe_of_mem U (f x) hx,
          onePointCollapse_coe_of_mem (f ⁻¹' U) x hx, OnePoint.map_some]
        rfl
      · rw [OnePoint.map_some, onePointCollapse_coe_of_notMem U (f x) hx,
          onePointCollapse_coe_of_notMem (f ⁻¹' U) x hx, OnePoint.map_infty]
  -- Contravariant pullback along this actual commuting square restricts to the kernels.
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change complexKZeroPullback F (complexKZeroPullback cY a.val) =
    complexKZeroPullback cX (complexKZeroPullback G a.val)
  have h := congrArg complexKZeroPullback hsquare
  rw [complexKZeroPullback_comp, complexKZeroPullback_comp] at h
  exact DFunLike.congr_fun h a.val

end AtiyahSinger

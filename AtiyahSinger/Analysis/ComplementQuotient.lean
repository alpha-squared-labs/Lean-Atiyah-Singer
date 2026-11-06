/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FixedComplement
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Quotient families with a fixed complement

Public module ID: M0375.

SL03: the fibers are the actual quotients F / T(V). The total topology is the
quotient topology of the map (T,y) ↦ (T,[y]), as required in SG III.7 Lemma 7.2(iv).
It is defined before any trivialization. Inverse block coordinates descend to
these quotients and give a homeomorphism over the invertibility chart.
This is not the varying cokernel family F / range(T), whose dimension can jump.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ContinuousLinearMap Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (V : Submodule ℂ E) (W : Submodule ℂ F)

variable {V W} (T : E →L[ℂ] F) (hT : T ∈ complementChartDomain V W)

/-- The first inverse-block coordinate descended to the actual quotient by T(V). -/
def complementQuotientCoordinate : (F ⧸ V.map T.toLinearMap) →L[ℂ] W :=
  (V.map T.toLinearMap).liftQL (complementProjection V W T)
    (le_of_eq (ker_complementProjection hT).symm)

/-- The quotient coordinate is the original projection on representatives. -/
theorem complementQuotientCoordinate_mkQ (y : F) :
    complementQuotientCoordinate T hT ((V.map T.toLinearMap).mkQ y) =
      complementProjection V W T y := by
  /- The continuous quotient lift evaluates on a representative by its
  defining linear map. Its well-definedness uses the previously proved kernel identity. -/
  rfl

/-- Quotient coordinates are a left inverse to the fixed-complement inclusion. -/
theorem complementQuotientCoordinate_subtype (w : W) :
    complementQuotientCoordinate T hT ((V.map T.toLinearMap).mkQ (w : F)) = w := by
  /- Evaluate the quotient lift at w and use that the block projection is
  identity on the fixed complement W. -/
  rw [complementQuotientCoordinate_mkQ]
  exact complementProjection_subtype hT w

/-- Quotient coordinates recover every quotient class by inclusion. -/
theorem mkQ_complementQuotientCoordinate (z : F ⧸ V.map T.toLinearMap) :
    (V.map T.toLinearMap).mkQ (complementQuotientCoordinate T hT z : F) = z := by
  /- Take a representative y. Its difference from the complement coordinate
  is T of the solution coordinate and therefore vanishes in the quotient.
  Quotient induction gives the statement for every class. -/
  obtain ⟨y, rfl⟩ := (V.map T.toLinearMap).mkQ_surjective z
  rw [complementQuotientCoordinate_mkQ]
  -- The solution term lies in T(V), so applying the quotient kills that term.
  have hsolution : (V.map T.toLinearMap).mkQ
      (T (complementSolution V W T y)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨complementSolution V W T y, (complementSolution V W T y).property, rfl⟩
  have hdecomposition := congrArg (V.map T.toLinearMap).mkQ
    (complementProjection_add_image_solution hT y)
  simpa only [map_add, hsolution, add_zero] using hdecomposition

/-- The natural inclusion W → F → F/T(V), with its explicit continuous inverse. -/
def complementQuotientEquiv : W ≃L[ℂ] (F ⧸ V.map T.toLinearMap) where
  toFun w := (V.map T.toLinearMap).mkQ (w : F)
  invFun := complementQuotientCoordinate T hT
  left_inv := complementQuotientCoordinate_subtype T hT
  right_inv := mkQ_complementQuotientCoordinate T hT
  map_add' := ((V.map T.toLinearMap).mkQ.comp W.subtype).map_add
  map_smul' := ((V.map T.toLinearMap).mkQ.comp W.subtype).map_smul
  continuous_toFun := ((V.map T.toLinearMap).mkQL.comp W.subtypeL).continuous
  continuous_invFun := (complementQuotientCoordinate T hT).continuous

/-- The quotient equivalence is the natural inclusion on every vector. -/
theorem complementQuotientEquiv_apply (w : W) :
    complementQuotientEquiv T hT w = (V.map T.toLinearMap).mkQ (w : F) := by
  /- Unfold the forward map of the specified equivalence. It is the natural
  inclusion followed by quotient, not an arbitrary vector-space isomorphism. -/
  rfl

/-- The inverse quotient equivalence has the block-coordinate formula. -/
theorem complementQuotientEquiv_symm_mkQ (y : F) :
    (complementQuotientEquiv T hT).symm ((V.map T.toLinearMap).mkQ y) =
      complementProjection V W T y := by
  /- The inverse is the continuous quotient lift of the block projection.
  Evaluate that lift at the representative y. -/
  exact complementQuotientCoordinate_mkQ T hT y

include hT in
/-- A finite fixed complement gives finite-dimensional quotient fibers. -/
theorem finiteDimensional_complementQuotient [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (F ⧸ V.map T.toLinearMap) := by
  /- Transport finite-dimensionality along the explicitly constructed linear
  equivalence from W to the quotient; no claim about the full cokernel is used. -/
  exact (complementQuotientEquiv T hT).toLinearEquiv.finiteDimensional

include hT in
/-- Every quotient fiber has the dimension of the fixed complement. -/
theorem finrank_complementQuotient :
    Module.finrank ℂ (F ⧸ V.map T.toLinearMap) = Module.finrank ℂ W := by
  /- Use dimension invariance under the natural linear equivalence.
  This finrank equality alone does not assert finite-dimensionality. -/
  exact (complementQuotientEquiv T hT).toLinearEquiv.finrank_eq.symm

variable (V W)

/-- The actual disjoint union of quotient fibers over the block invertibility chart. -/
abbrev ComplementQuotientTotalSpace : Type _ :=
  Bundle.TotalSpace W
    (fun T : complementChartDomain V W ↦ F ⧸ V.map T.val.toLinearMap)

/-- The surjection from parameter-vector pairs to their parameter-indexed quotient classes. -/
def complementQuotientMap (p : complementChartDomain V W × F) :
    ComplementQuotientTotalSpace V W :=
  ⟨p.1, (V.map p.1.val.toLinearMap).mkQ p.2⟩

/-- The standard quotient topology, fixed independently of any trivialization. -/
instance complementQuotientTopology : TopologicalSpace (ComplementQuotientTotalSpace V W) :=
  TopologicalSpace.coinduced (complementQuotientMap V W) inferInstance

/-- The global coordinate map on this quotient chart, using the descended block inverse. -/
def complementQuotientCoordinates (z : ComplementQuotientTotalSpace V W) :
    complementChartDomain V W × W :=
  ⟨z.proj, complementQuotientCoordinate z.proj.val z.proj.property z.snd⟩

/-- Inclusion of the fixed complement, as a map into the actual total quotient space. -/
def complementQuotientInclusion (p : complementChartDomain V W × W) :
    ComplementQuotientTotalSpace V W :=
  complementQuotientMap V W (p.1, (p.2 : F))

/-- The defining map reaches every point of the quotient family. -/
theorem complementQuotientMap_surjective : Function.Surjective (complementQuotientMap V W) := by
  /- Keep the parameter fixed and use surjectivity of the module quotient
  map in that fiber. No representative needs to be chosen continuously. -/
  rintro ⟨T, z⟩
  obtain ⟨y, rfl⟩ := (V.map T.val.toLinearMap).mkQ_surjective z
  exact ⟨(T, y), rfl⟩

/-- The defining surjection is a quotient map for the declared total topology. -/
theorem isQuotientMap_complementQuotientMap : IsQuotientMap (complementQuotientMap V W) := by
  /- Combine surjectivity with the coinduced topology used in the definition.
  The topology is the quotient of chart × F before proving any coordinate theorem. -/
  exact ⟨⟨rfl⟩, complementQuotientMap_surjective V W⟩

/-- Coordinates on a quotient representative have the inverse-block formula. -/
theorem complementQuotientCoordinates_map (p : complementChartDomain V W × F) :
    complementQuotientCoordinates V W (complementQuotientMap V W p) =
      (p.1, complementProjection V W p.1.val p.2) := by
  /- The parameter is unchanged. Evaluate the descended first coordinate
  on the quotient class of the original vector. -/
  rfl

/-- Inclusion followed by quotient coordinates is identity. -/
theorem complementQuotientCoordinates_inclusion (p : complementChartDomain V W × W) :
    complementQuotientCoordinates V W (complementQuotientInclusion V W p) = p := by
  /- The first coordinate is the same parameter, and the second is the
  block projection of a vector in W, hence that vector itself. -/
  rcases p with ⟨T, w⟩
  apply Prod.ext
  · rfl
  · exact complementQuotientCoordinate_subtype T.val T.property w

/-- Coordinates followed by inclusion recover the actual quotient-family point. -/
theorem complementQuotientInclusion_coordinates (z : ComplementQuotientTotalSpace V W) :
    complementQuotientInclusion V W (complementQuotientCoordinates V W z) = z := by
  /- Remain in the original fiber and use the quotient inverse identity.
  The discarded solution coordinate belongs to T(V) and has zero quotient class. -/
  rcases z with ⟨T, z⟩
  apply Bundle.TotalSpace.ext
  · rfl
  · exact heq_of_eq (mkQ_complementQuotientCoordinate T.val T.property z)

/-- The inclusion of the fixed complement is continuous for the quotient topology. -/
theorem continuous_complementQuotientInclusion : Continuous (complementQuotientInclusion V W) := by
  /- Factor through the continuous map (T,w) ↦ (T,w) into chart × F,
  followed by the defining continuous quotient surjection. -/
  apply (isQuotientMap_complementQuotientMap V W).continuous.comp
  exact continuous_fst.prodMk (W.subtypeL.continuous.comp continuous_snd)

variable [CompleteSpace V] [CompleteSpace W]

/-- The coordinate map is continuous for the original quotient topology. -/
theorem continuous_complementQuotientCoordinates :
    Continuous (complementQuotientCoordinates V W) := by
  /- By the quotient-map criterion, it suffices to check after precomposition
  with chart × F. There it is (T,y) ↦ (T, projection(T)y). Operator-norm
  continuity of the projection and continuity of evaluation prove joint continuity. -/
  apply (isQuotientMap_complementQuotientMap V W).continuous_iff.mpr
  -- Pull back to representatives, where the block projection is jointly continuous.
  have hprojection : Continuous (fun p : complementChartDomain V W × F ↦
      complementProjection V W p.1.val) :=
    (continuousOn_complementProjection V W).domRestrict.comp continuous_fst
  have hcoordinates := continuous_fst.prodMk (hprojection.clm_apply continuous_snd)
  exact hcoordinates

/-- The actual quotient family is a trivial bundle over its open block chart. -/
def complementQuotientTrivialization :
    ComplementQuotientTotalSpace V W ≃ₜ (complementChartDomain V W × W) where
  toFun := complementQuotientCoordinates V W
  invFun := complementQuotientInclusion V W
  left_inv := complementQuotientInclusion_coordinates V W
  right_inv := complementQuotientCoordinates_inclusion V W
  continuous_toFun := continuous_complementQuotientCoordinates V W
  continuous_invFun := continuous_complementQuotientInclusion V W

/-- The trivialization lies over the identity of the parameter chart. -/
theorem complementQuotientTrivialization_proj (z : ComplementQuotientTotalSpace V W) :
    (complementQuotientTrivialization V W z).1 = z.proj := by
  /- Its definition retains the original parameter. This base preservation,
  together with the fiberwise linear formula, makes the homeomorphism a bundle comparison. -/
  rfl

/-- The inverse trivialization is precisely the natural quotient inclusion. -/
theorem complementQuotientTrivialization_symm_apply (T : complementChartDomain V W) (w : W) :
    (complementQuotientTrivialization V W).symm (T, w) =
      (⟨T, (V.map T.val.toLinearMap).mkQ (w : F)⟩ : ComplementQuotientTotalSpace V W) := by
  /- Unfold the inverse homeomorphism. On each fiber it is exactly the
  natural linear quotient equivalence constructed before any total-space topology argument. -/
  rfl

/-- The natural projection of the quotient family is continuous. -/
theorem continuous_complementQuotient_proj :
    Continuous (fun z : ComplementQuotientTotalSpace V W ↦ z.proj) := by
  /- Identify this map with first projection after the base-preserving
  homeomorphism. The product projection is continuous. -/
  exact continuous_fst.comp (complementQuotientTrivialization V W).continuous

/-- The natural projection of the quotient family is an open map. -/
theorem isOpenMap_complementQuotient_proj :
    IsOpenMap (fun z : ComplementQuotientTotalSpace V W ↦ z.proj) := by
  /- Under the constructed homeomorphism this is product projection.
  Product projection is open, and composition with a homeomorphism preserves openness. -/
  exact isOpenMap_fst.comp (complementQuotientTrivialization V W).isOpenMap

end AtiyahSinger

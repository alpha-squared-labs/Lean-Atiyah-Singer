/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ZeroSpinCliffordSymbol
public import AtiyahSinger.Topology.FiberBundleTopology
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The original spin-symbol class in real rank zero

Public module ID: M2279.

SC01. The original zero-rank real bundle has only zero vectors, and its
projection is inverse to its native zero section. The zero Clifford map on
the original associated parity bundles therefore gives boundary data on an
empty complement. The compact-support construction uses exactly the same
raw triple, resizing adapter and support class as in positive even rank.

Sources: Lawson--Michelsohn, Spin Geometry, I.2, Definition 2.3, p.14, and
the unit-vector product formulas (2.24)--(2.25), p.18; III.12, equation
(12.13), p.242. The unit-generated rank-zero group has only the empty
product, matching the native group convention. This is the degenerate
case of the Clifford-symbol construction, not an extension of the
positive-rank two-sheeted frame-lift definition in II.1.

The actual principal bundle and both original associated half-spin bundles
are retained. No trivialization of the positive half-spin bundle or
identification of its K class with the unit is assumed. The zero-section
formula gives its original class minus that of the negative half-spin
bundle. `ZeroHalfSpinorCharacter` supplies the separate vacuum
trivialization used to identify these classes with the unit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  isFiniteRank_restrict t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

variable {B P : Type*} [TopologicalSpace B] [TopologicalSpace P]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

local notation "RealModel" => EuclideanSpace ℝ (Fin 0)
local notation "SpinPlus" => HalfSpinorBundle 0 hP (0 : ZMod 2)
local notation "SpinMinus" => HalfSpinorBundle 0 hP (1 : ZMod 2)
local notation "VectorProjection" => (π RealModel E)
local notation "ZeroSet" => Set.range (zeroSection RealModel E)

/-- The actual zero Clifford map restricts to the unique isomorphism off the zero section. -/
def zeroSpinCliffordParityBoundary :
    RelativeTriple (VectorProjection *ᵖ SpinPlus) (VectorProjection *ᵖ SpinMinus) ZeroSetᶜ :=
  letI : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
      (continuous_complexSpinParityRepresentation 0 0)
  letI : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
      (continuous_complexSpinParityRepresentation 0 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  letI : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  letI : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  let a : Hom (VectorProjection *ᵖ SpinPlus) (VectorProjection *ᵖ SpinMinus) :=
    zeroSpinCliffordParityHom E hP 0
  (a.restrict ZeroSetᶜ).toIso fun z ↦ by
    -- Every point of the original total space is its own base point's zero vector.
    have hz : zeroSection RealModel E z.val.proj = z.val :=
      (zeroRankBundleProjectionHomeomorph E).symm_apply_apply z.val
    -- The complement is empty; this does not assert invertibility at the zero vector.
    exact False.elim (z.property ⟨z.val.proj, hz⟩)

variable [CompactSpace B]

/-- The original rank-zero symbol with the actual compact zero section as control. -/
def zeroSpinorSymbolTriple :
    CompactSupportTriple (VectorProjection *ᵖ SpinPlus) (VectorProjection *ᵖ SpinMinus) where
  control := ZeroSet
  isCompact_control := isCompact_range (show Continuous (zeroSection RealModel E) from
    Bundle.Trivialization.continuous_zeroSection ℝ)
  boundary := zeroSpinCliffordParityBoundary E hP

/-- The same rank-zero spin symbol packaged in the existing isomorphic small models. -/
def zeroSpinorSupportTriple : SupportBundleTriple (TotalSpace RealModel E) :=
  letI : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
      (continuous_complexSpinParityRepresentation 0 0)
  letI : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
      (continuous_complexSpinParityRepresentation 0 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  letI : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  letI : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  (zeroSpinorSymbolTriple E hP).toSupportBundleTriple

variable [T2Space B]

/-- The actual compact-support spin-symbol class for the native rank-zero convention. -/
def zeroSpinorThomClass : CompactSupportKZero (TotalSpace RealModel E) :=
  (zeroSpinorSupportTriple E hP).compactSupportClass

/-- Rank-zero restriction still gives the original positive-minus-negative spinor class. -/
theorem zeroSectionPullback_zeroSpinorThomClass :
    letI : IsFiniteRank SpinPlus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
        (continuous_complexSpinParityRepresentation 0 0)
    letI : IsFiniteRank SpinMinus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
        (continuous_complexSpinParityRepresentation 0 1)
    let i : C(B, TotalSpace RealModel E) :=
      ⟨zeroSection RealModel E, Bundle.Trivialization.continuous_zeroSection ℝ⟩
    compactSupportKZeroToAbsolute
        (compactSupportKZeroPullback i i.continuous.isProperMap (zeroSpinorThomClass E hP)) =
      ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus := by
  /- Stage 1: the original zero section is the inverse of the native
  zero-rank projection homeomorphism. It is continuous and proper; compact
  B and the Hausdorff original total space also give this properness.
  Stage 2: proper-pullback naturality restricts the actual support triple
  along that same zero section. Its control is all B, and its boundary is
  empty. The two iterated pullbacks identify with the original half-spin
  bundles through the vector-preserving pullback comparisons.
  Stage 3: the existing compact-base support comparison gives source minus
  target. Isomorphism invariance removes only the specified resizing and
  pullback adapters. Unequal parity dimensions cause no difficulty on an
  empty boundary, and no trivial-line identification is needed. -/
  classical
  let : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
      (continuous_complexSpinParityRepresentation 0 0)
  let : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
      (continuous_complexSpinParityRepresentation 0 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  let i : C(B, TotalSpace RealModel E) :=
    ⟨zeroSection RealModel E, Bundle.Trivialization.continuous_zeroSection ℝ⟩
  let : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  let : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  -- Restrict the same support class along the actual proper zero section.
  change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i i.continuous.isProperMap
        (zeroSpinorSupportTriple E hP).compactSupportClass) = _
  rw [← SupportBundleTriple.compactSupportClass_pullback,
    SupportBundleTriple.compactSupportClass_toAbsolute]
  -- Forgetting support returns the classes of the two actual pulled-back small models.
  -- Their specified resizing, composition and identity comparisons preserve every vector.
  let := ((zeroSpinorSupportTriple E hP).pullback i i.continuous.isProperMap).source.isFiniteRank
  let := ((zeroSpinorSupportTriple E hP).pullback i i.continuous.isProperMap).target.isFiniteRank
  apply congrArg₂ (fun a b : ComplexKZero B ↦ a - b)
  · apply kZeroClass_eq_of_iso
    exact ((smallBundleIso (VectorProjection *ᵖ SpinPlus)).symm.pullback i).trans
      ((pullbackCompIso (E := SpinPlus) p i).trans (pullbackIdIso (E := SpinPlus)))
  · apply kZeroClass_eq_of_iso
    exact ((smallBundleIso (VectorProjection *ᵖ SpinMinus)).symm.pullback i).trans
      ((pullbackCompIso (E := SpinMinus) p i).trans (pullbackIdIso (E := SpinMinus)))

end AtiyahSinger

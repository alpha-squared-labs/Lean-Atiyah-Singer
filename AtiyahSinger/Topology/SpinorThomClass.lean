/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinCliffordSymbol
public import AtiyahSinger.Topology.FiberBundleTopology
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The compact-support class of the original spin Clifford symbol

Public module ID: M2180.

SC01. Over a compact base, the original parity-changing Clifford bundle map
is invertible away from the actual zero section. Its two pulled-back bundles
are the original associated half-spin fibers, with their original quotient
topologies. The standard support-triple construction gives its class in Kc.
Resizing uses only the existing bundle-isomorphism adapter and retains the
same compact control and boundary action.

Sources: Lawson--Michelsohn, Spin Geometry, III.12, p.242, equation (12.13),
and its zero-section restriction formula. The convention is multiplication
by the real vector itself, with even spinors as source and odd spinors as
target; no additional factor of i is inserted. The zero-section formula is
source minus target, as in Construction 11.23. The Chern character and the
Thom isomorphism of Propositions 12.5 and 12.6 are separate conclusions.

The supplied topological spin structure has positive even rank. No rank-zero
spin lift, smooth structure, connection, cotangent identification or Dirac
operator is asserted. Hausdorffness is added only for compact-support K
theory. Proper pullback is taken along the zero section from the compact
base, not along the generally nonproper bundle projection. The zero-section
formula follows by proper naturality and compact-base normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  isFiniteRank_restrict t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

variable {m : ℕ} {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

local notation "RealModel" => EuclideanSpace ℝ (Fin (2 * m))
local notation "SpinPlus" => HalfSpinorBundle m hP (0 : ZMod 2)
local notation "SpinMinus" => HalfSpinorBundle m hP (1 : ZMod 2)
local notation "VectorProjection" => (π RealModel E)
local notation "ZeroSet" => Set.range (zeroSection RealModel E)

/-- The original even-to-odd Clifford symbol is a bundle isomorphism off the zero section. -/
def TopologicalSpinStructure.cliffordParityBoundary
    (S : TopologicalSpinStructure m E o hm hP) :
    RelativeTriple (VectorProjection *ᵖ SpinPlus) (VectorProjection *ᵖ SpinMinus) ZeroSetᶜ :=
  letI : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
      (continuous_complexSpinParityRepresentation m 0)
  letI : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
      (continuous_complexSpinParityRepresentation m 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  letI : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  letI : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  let a : Hom (VectorProjection *ᵖ SpinPlus) (VectorProjection *ᵖ SpinMinus) :=
    S.cliffordParityHom 0
  (a.restrict ZeroSetᶜ).toIso fun z ↦ by
    -- Outside the actual zero-section range the original fiber vector is nonzero.
    have hv : z.val.snd ≠ 0 := by
      intro hz
      apply z.property
      refine ⟨z.val.proj, ?_⟩
      change TotalSpace.mk z.val.proj 0 = z.val
      rw [← hz]
    -- The inverse-continuity theorem uses the same finite pullback bundle charts.
    exact S.cliffordParity_bijective z.val.proj z.val.snd hv 0

variable [CompactSpace B]

/-- The spin symbol with its actual pullback fibers and the compact zero section as control. -/
def TopologicalSpinStructure.spinorSymbolTriple
    (S : TopologicalSpinStructure m E o hm hP) :
    CompactSupportTriple (VectorProjection *ᵖ SpinPlus) (VectorProjection *ᵖ SpinMinus) where
  control := ZeroSet
  isCompact_control := isCompact_range (show Continuous (zeroSection RealModel E) from
    Bundle.Trivialization.continuous_zeroSection ℝ)
  boundary := S.cliffordParityBoundary

/-- Package the same spin symbol using the existing isomorphic small-bundle models. -/
def TopologicalSpinStructure.spinorSupportTriple
    (S : TopologicalSpinStructure m E o hm hP) : SupportBundleTriple (TotalSpace RealModel E) :=
  letI : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
      (continuous_complexSpinParityRepresentation m 0)
  letI : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
      (continuous_complexSpinParityRepresentation m 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  letI : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  letI : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  S.spinorSymbolTriple.toSupportBundleTriple

variable [T2Space B]

/-- SG (12.13): the compact-support K class of the specified positive spin Clifford symbol. -/
def TopologicalSpinStructure.spinorThomClass
    (S : TopologicalSpinStructure m E o hm hP) : CompactSupportKZero (TotalSpace RealModel E) :=
  S.spinorSupportTriple.compactSupportClass

/-- Restriction to the original zero section gives the positive-minus-negative spinor class. -/
theorem TopologicalSpinStructure.zeroSectionPullback_spinorThomClass
    (S : TopologicalSpinStructure m E o hm hP) :
    letI : IsFiniteRank SpinPlus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
        (continuous_complexSpinParityRepresentation m 0)
    letI : IsFiniteRank SpinMinus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
        (continuous_complexSpinParityRepresentation m 1)
    let i : C(B, TotalSpace RealModel E) :=
      ⟨zeroSection RealModel E, Bundle.Trivialization.continuous_zeroSection ℝ⟩
    compactSupportKZeroToAbsolute
        (compactSupportKZeroPullback i i.continuous.isProperMap S.spinorThomClass) =
      ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus := by
  /- Stage 1: the native zero section is continuous and its source B is
  compact; the unchanged real total space is Hausdorff. Thus this specified
  map is proper and support-class proper-pullback naturality applies.
  Stage 2: its inverse image of the original zero-section control is all B.
  The pulled-back parity bundles retain their actual fibers. The original
  pullback-composition and identity isomorphisms identify them with the two
  associated half-spin bundles, preserving each vector and its topology.
  Stage 3: the compact-base support-class comparison forgets the now-empty
  exterior boundary and returns source minus target. Bundle-isomorphism
  invariance removes only the specified small-model and pullback adapters,
  yielding [S+] - [S-]. Neither the Thom isomorphism nor properness of the
  original bundle projection is used. -/
  classical
  let : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
      (continuous_complexSpinParityRepresentation m 0)
  let : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
      (continuous_complexSpinParityRepresentation m 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  let i : C(B, TotalSpace RealModel E) :=
    ⟨zeroSection RealModel E, Bundle.Trivialization.continuous_zeroSection ℝ⟩
  let : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  let : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  -- Restrict the same support class along the actual proper zero section.
  change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i i.continuous.isProperMap
        S.spinorSupportTriple.compactSupportClass) = _
  rw [← SupportBundleTriple.compactSupportClass_pullback S.spinorSupportTriple
      i i.continuous.isProperMap,
    SupportBundleTriple.compactSupportClass_toAbsolute
      (S.spinorSupportTriple.pullback i i.continuous.isProperMap)]
  -- Forgetting support returns the classes of the two actual pulled-back small models.
  -- Their specified resizing, composition and identity comparisons preserve every vector.
  let := (S.spinorSupportTriple.pullback i i.continuous.isProperMap).source.isFiniteRank
  let := (S.spinorSupportTriple.pullback i i.continuous.isProperMap).target.isFiniteRank
  -- Compare an arbitrary original bundle first, before specializing its parity.
  have hclass (V : B → Type _) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
      [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V] :
      letI : IsFiniteRank ((p : TotalSpace RealModel E → B) *ᵖ V) :=
        isFiniteRank_pullback p
      letI : IsFiniteRank ((i : B → TotalSpace RealModel E) *ᵖ
          (smallBundle ((p : TotalSpace RealModel E → B) *ᵖ V)).Fiber) :=
        isFiniteRank_pullback i
      ComplexBundle.kZeroClass ((i : B → TotalSpace RealModel E) *ᵖ
          (smallBundle ((p : TotalSpace RealModel E → B) *ᵖ V)).Fiber) =
        ComplexBundle.kZeroClass V := by
    let : IsFiniteRank ((p : TotalSpace RealModel E → B) *ᵖ V) :=
      isFiniteRank_pullback p
    let : IsFiniteRank ((i : B → TotalSpace RealModel E) *ᵖ
        (smallBundle ((p : TotalSpace RealModel E → B) *ᵖ V)).Fiber) :=
      isFiniteRank_pullback i
    apply kZeroClass_eq_of_iso
    exact ((smallBundleIso ((p : TotalSpace RealModel E → B) *ᵖ V)).symm.pullback i).trans
      ((pullbackCompIso (E := V) p i).trans (pullbackIdIso (E := V)))
  apply congrArg₂ (fun a b : ComplexKZero B ↦ a - b)
  · exact hclass SpinPlus
  · exact hclass SpinMinus

end AtiyahSinger

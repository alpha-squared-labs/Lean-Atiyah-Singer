/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SpinThom
public import AtiyahSinger.Topology.SupportTensorAction
public import AtiyahSinger.Topology.SupportTriplePhase
public import AtiyahSinger.Topology.ZeroSpinThom

/-!
# The original spin symbol with an arbitrary finite bundle coefficient

Public module ID: M2174.

S02. The two bundles are the actual pullbacks of S+ tensor W and S- tensor W,
with the existing tensor and pullback topologies. Their exterior map acts
by the original parity Clifford map on the spinor and identity on the same
coefficient vector. The original zero section is retained as compact control.

Its class is the existing spin Thom homomorphism applied to the class of W.
This follows from the explicit right-tensor support construction and its
comparison with the original proper-graph action. The coefficient bundle
may have different ranks on different components, including rank zero.

Sources: SG III.13.10 and its proof, pp.256--257; SG Appendix C.1 and C.12.
The native rank-zero variant is stated separately as the same degenerate
extension used by ZeroSpinThom. No twofold rank-zero spin lift is asserted.
Smoothness, connections, and the actual Dirac operator are supplied separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology isFiniteRank_tensor isFiniteRank_pullback isFiniteRank_restrict
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

section Positive

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
  [CompactSpace B]
  (W : B → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)] [IsFiniteRank W]

local notation "RealModel" => EuclideanSpace ℝ (Fin (2 * m))
local notation "SpinPlus" => HalfSpinorBundle m hP (0 : ZMod 2)
local notation "SpinMinus" => HalfSpinorBundle m hP (1 : ZMod 2)
local notation "VectorProjection" => (π RealModel E)

/-- The original spin symbol tensored with W, on the actual pullbacks of the twisted bundles. -/
def TopologicalSpinStructure.twistedSpinorSymbolTriple
    (S : TopologicalSpinStructure m E o hm hP) :
    CompactSupportTriple
      (VectorProjection *ᵖ (fun x ↦ SpinPlus x ⊗[ℂ] W x))
      (VectorProjection *ᵖ (fun x ↦ SpinMinus x ⊗[ℂ] W x)) :=
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
  letI : IsFiniteRank (VectorProjection *ᵖ W) := isFiniteRank_pullback p
  (S.spinorSymbolTriple.tensorRight ((p : _ → B) *ᵖ W)).congr
    (pullbackTensorIso (E := SpinPlus) (F := W) p).symm
    (pullbackTensorIso (E := SpinMinus) (F := W) p).symm

/-- The twisted raw triple retains the original zero control and the exact c tensor identity. -/
theorem TopologicalSpinStructure.twistedSpinorSymbolTriple_properties
    (S : TopologicalSpinStructure m E o hm hP) :
    (S.twistedSpinorSymbolTriple W).control = Set.range (zeroSection RealModel E) ∧
      ∀ (z : ((S.twistedSpinorSymbolTriple W).controlᶜ : Set (TotalSpace RealModel E)))
        (s : SpinPlus z.val.proj) (w : W z.val.proj),
        (S.twistedSpinorSymbolTriple W).boundary.linearEquiv z (s ⊗ₜ[ℂ] w) =
          S.cliffordParity z.val.proj z.val.snd 0 s ⊗ₜ[ℂ] w := by
  /- Stage 1: tensorRight and congr copy the existing spin-symbol control
  literally. It is the original zero-section range, even when W has zero
  rank and the actual support is smaller. Stage 2: the pullback/tensor
  comparisons preserve each tensor vector. The middle tensor equivalence
  applies the original spin boundary to s and identity to w. Its spin
  boundary is precisely S.cliffordParity at this same original real vector.
  Thus both parity labels, the spin structure and the coefficient remain
  unchanged throughout the actual pure-tensor formula. -/
  constructor
  · -- Both the right tensor and the specified comparison retain the original control.
    rfl
  · intro z s w
    -- The two comparison maps fix pure tensors; only the original spin boundary acts.
    change (TensorProduct.map (S.cliffordParity z.val.proj z.val.snd 0)
      (LinearMap.id : W z.val.proj →ₗ[ℂ] W z.val.proj)) (s ⊗ₜ[ℂ] w) = _
    rw [TensorProduct.map_tmul]
    rfl

variable [T2Space B]

/-- The actual twisted spin-symbol class is multiplication by the same original spin Thom class. -/
theorem TopologicalSpinStructure.twistedSpinorSymbolTriple_class
    (S : TopologicalSpinStructure m E o hm hP) :
    letI : IsFiniteRank SpinPlus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
        (continuous_complexSpinParityRepresentation m 0)
    letI : IsFiniteRank SpinMinus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
        (continuous_complexSpinParityRepresentation m 1)
    let p : C(TotalSpace RealModel E, B) :=
      ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
    letI : IsFiniteRank (VectorProjection *ᵖ (fun x ↦ SpinPlus x ⊗[ℂ] W x)) :=
      isFiniteRank_pullback p
    letI : IsFiniteRank (VectorProjection *ᵖ (fun x ↦ SpinMinus x ⊗[ℂ] W x)) :=
      isFiniteRank_pullback p
    (S.twistedSpinorSymbolTriple W).compactSupportClass =
      S.spinThomHom (ComplexBundle.kZeroClass W) := by
  /- Stage 1: compactSupportClass_congr removes only the specified actual
  pullback/tensor comparison isomorphisms. Apply the right-tensor graph
  action theorem to the original S.spinorSymbolTriple and the original
  bundle projection. No properness of that projection is required.
  Stage 2: its compactSupportClass is definitionally S.spinorThomClass
  after the same existing small-bundle packaging. The graph-action map
  with that right factor is exactly S.spinThomHom. This proves the stated
  identity without replacing W by its rank or assuming the desired K
  equality. Different component ranks and zero coefficient bundles remain. -/
  let : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
      (continuous_complexSpinParityRepresentation m 0)
  let : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
      (continuous_complexSpinParityRepresentation m 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  let : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  let : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  let : IsFiniteRank (VectorProjection *ᵖ W) := isFiniteRank_pullback p
  -- Remove only the actual vector-preserving pullback/tensor comparisons.
  change ((S.spinorSymbolTriple.tensorRight ((p : _ → B) *ᵖ W)).congr
    (pullbackTensorIso (E := SpinPlus) (F := W) p).symm
    (pullbackTensorIso (E := SpinMinus) (F := W) p).symm).compactSupportClass = _
  rw [CompactSupportTriple.compactSupportClass_congr]
  -- The existing right-tensor formula is precisely the same projection-graph action.
  exact CompactSupportTriple.compactSupportClass_tensorRight_pullback W S.spinorSymbolTriple p

end Positive

section Zero

variable {B P : Type*} [TopologicalSpace B] [TopologicalSpace P] [CompactSpace B]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)
  (W : B → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)] [IsFiniteRank W]

local notation "RealModel" => EuclideanSpace ℝ (Fin 0)
local notation "SpinPlus" => HalfSpinorBundle 0 hP (0 : ZMod 2)
local notation "SpinMinus" => HalfSpinorBundle 0 hP (1 : ZMod 2)
local notation "VectorProjection" => (π RealModel E)

/-- The original native zero-rank spin symbol with the unchanged right coefficient bundle. -/
def zeroTwistedSpinorSymbolTriple :
    CompactSupportTriple
      (VectorProjection *ᵖ (fun x ↦ SpinPlus x ⊗[ℂ] W x))
      (VectorProjection *ᵖ (fun x ↦ SpinMinus x ⊗[ℂ] W x)) :=
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
  letI : IsFiniteRank (VectorProjection *ᵖ W) := isFiniteRank_pullback p
  ((zeroSpinorSymbolTriple E hP).tensorRight ((p : _ → B) *ᵖ W)).congr
    (pullbackTensorIso (E := SpinPlus) (F := W) p).symm
    (pullbackTensorIso (E := SpinMinus) (F := W) p).symm

variable [T2Space B]

/-- The native rank-zero tensor symbol realizes its specified zero-spin Thom action. -/
theorem zeroTwistedSpinorSymbolTriple_class :
    letI : IsFiniteRank SpinPlus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
        (continuous_complexSpinParityRepresentation 0 0)
    letI : IsFiniteRank SpinMinus :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
        (continuous_complexSpinParityRepresentation 0 1)
    let p : C(TotalSpace RealModel E, B) :=
      ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
    letI : IsFiniteRank (VectorProjection *ᵖ (fun x ↦ SpinPlus x ⊗[ℂ] W x)) :=
      isFiniteRank_pullback p
    letI : IsFiniteRank (VectorProjection *ᵖ (fun x ↦ SpinMinus x ⊗[ℂ] W x)) :=
      isFiniteRank_pullback p
    (zeroTwistedSpinorSymbolTriple E hP W).compactSupportClass =
      zeroSpinThomHom E hP (ComplexBundle.kZeroClass W) := by
  /- The exact same right-tensor action and pullback/tensor comparisons
  apply to the existing zeroSpinorSymbolTriple. Its exterior is empty,
  retaining the original positive tensor W minus negative tensor W class.
  The resulting graph action is definitionally zeroSpinThomHom E hP.
  No positive-rank structure or fictitious two-sheeted lift is used, and
  no identification of the positive associated line with a trivial line
  is needed for this equality of the original classes. -/
  let : IsFiniteRank SpinPlus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
      (continuous_complexSpinParityRepresentation 0 0)
  let : IsFiniteRank SpinMinus :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
      (continuous_complexSpinParityRepresentation 0 1)
  let p : C(TotalSpace RealModel E, B) :=
    ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  let : IsFiniteRank (VectorProjection *ᵖ SpinPlus) := isFiniteRank_pullback p
  let : IsFiniteRank (VectorProjection *ᵖ SpinMinus) := isFiniteRank_pullback p
  let : IsFiniteRank (VectorProjection *ᵖ W) := isFiniteRank_pullback p
  -- The original empty-exterior triple uses exactly the same tensor comparison.
  change (((zeroSpinorSymbolTriple E hP).tensorRight ((p : _ → B) *ᵖ W)).congr
    (pullbackTensorIso (E := SpinPlus) (F := W) p).symm
    (pullbackTensorIso (E := SpinMinus) (F := W) p).symm).compactSupportClass = _
  rw [CompactSupportTriple.compactSupportClass_congr]
  -- Its graph action is the original zero-spin Thom homomorphism, with W unchanged.
  exact CompactSupportTriple.compactSupportClass_tensorRight_pullback W
    (zeroSpinorSymbolTriple E hP) p

end Zero

end AtiyahSinger

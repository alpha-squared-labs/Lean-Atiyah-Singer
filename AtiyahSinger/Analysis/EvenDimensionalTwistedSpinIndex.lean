/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.TwistedSpinIndex
public import AtiyahSinger.Analysis.ZeroTwistedSpinIndex
public import AtiyahSinger.Geometry.ZeroSpinCliffordSymbol
public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.ContinuousHermitianMetric

/-!
# The original twisted spin index in every native even dimension

Public module ID: M2303.

The input carrier records the original positive-dimensional spin frame lift, or the
native zero endpoint on the same principal total space and projection. It is an
implementation dispatch carrier, rather than a new definition attributed to a book.
The actual quotient HalfSpinorBundle families and the supplied W are never replaced.

The principal atlas is produced from that same frame lift in positive dimension and
from the same trivial-group principal charts in dimension zero. The actual operator
always contracts the original half-spin connection tensored with the supplied covW.
Its positive specialization equals the original twistedDiracPlus. At zero, the genuine
empty tangent-basis sum proves equality with the original zeroTwistedDiracPlus for
every supplied coefficient connection. The section spaces use those same tensor atlases.

The auxiliary complexified-tangent Hermitian metric is produced internally on the
original complexification topology. No auxiliary atlas, characteristic metric, desired
symbol class, index equality, connectedness or common coefficient rank is a premise.
Every supplied smooth complex coefficient connection is allowed; its unitary book case
is included, and changing the connection changes only lower-order terms. The induced
orientation is the original positive
spin orientation, with the canonical positive empty-frame orientation at native zero.

Sources: SG II.1 Definition 1.3, II.4--5 and III.13.10, formula (13.26). The extension
to arbitrary smooth complex connections uses their unchanged principal symbol. The native
zero endpoint is the explicit project continuation of SG I.2 Definition 2.3 and the
empty-product exterior model; SG II.1 omits rank zero. An independent signed two-sheet
convention is supplementary and is not inserted as a premise or replacement here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped BigOperators Manifold ContDiff TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology ComplexBundle.isFiniteRank_tensor
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_cotangent locallyCompactSpace_cotangent

set_option maxSynthPendingDepth 50

section CharacteristicMetric

variable {m : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))
local notation "TM" => (TangentSpace 𝓘(ℝ, TModel) : M → Type)

/-- A characteristic metric on the original tangent complexification, produced internally. -/
def evenDimensionalTangentHermitianMetric :
    letI := complexificationTopology TModel TM
    ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x) := by
  letI := complexificationTopology TModel TM
  letI : IsFiniteRank (fun x : M ↦ ℂ ⊗[ℝ] TM x) :=
    isFiniteRank_complexification TModel TM
  -- Compact Hausdorff supplies paracompactness; the original fibers and topology stay fixed.
  exact (nonempty_continuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x)).some

end CharacteristicMetric

section OriginalInputs

variable {m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type)
local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))

/-- Implementation dispatch for the original positive spin lift and its native zero endpoint.
The carrier has no smooth-atlas, characteristic-class or desired-index certificate field. -/
inductive EvenDimensionalSpinInput
    [RiemannianBundle TM] [IsContinuousRiemannianBundle TModel TM]
    (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection) where
  /-- The original positive-even spin structure, with its same oriented frame lift. -/
  | positive (hm : 0 < m)
      (o : ∀ x : M, Orientation ℝ (TM x) (Fin (2 * m)))
      (S : TopologicalSpinStructure m TM o hm hP)
  /-- Native rank zero uses the given original trivial-group principal bundle. -/
  | nativeZero (hzero : m = 0)

variable {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))

namespace EvenDimensionalSpinInput

/-- Produce a smooth principal atlas on the same original total space and projection. -/
def smoothPrincipalAtlas :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    EvenDimensionalSpinInput hP → SmoothSpinPrincipalAtlas m I projection := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  cases S with
  | positive hm o S => exact S.smoothPrincipalAtlas I
  | nativeZero hzero =>
    subst m
    exact smoothSpinPrincipalAtlasZero 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) hP

/-- The same spin orientation, with the canonical positive empty-frame orientation at zero. -/
def homologicalOrientation :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    EvenDimensionalSpinInput hP → HomologicalOrientation (2 * m) M := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S
  cases S with
  | positive hm o S => exact S.homologicalOrientation g
  | nativeZero hzero =>
    subst m
    exact zeroTangentHomologicalOrientation g

/-- The actual positive cotangent Clifford map on the original associated quotient fibers. -/
def cotangentCliffordPlus :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    EvenDimensionalSpinInput hP →
      AtlasSymbolFunction (n := 2 * m) (HalfSpinorBundle m hP 0) (HalfSpinorBundle m hP 1) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S
  cases S with
  | positive hm o S => exact S.cotangentCliffordPlus g
  | nativeZero hzero =>
    subst m
    -- zeroSpinCliffordParity is precisely this zero map on the original native fibers.
    exact fun _ _ ↦ 0

set_option maxHeartbeats 3000000 in
-- Infer the original associated atlases and Clifford property maps together.
omit [T2Space M] [SecondCountableTopology M] in
/-- Linearity and smoothness hold for these actual maps in the produced original atlases. -/
theorem cotangentCliffordPlus_properties :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ S : EvenDimensionalSpinInput hP,
      (∀ x : M,
        letI : Module ℝ (HalfSpinorBundle m hP 0 x →ₗ[ℂ] HalfSpinorBundle m hP 1 x) :=
          Module.compHom _ Complex.ofRealHom
        IsLinearMap ℝ (S.cotangentCliffordPlus g x)) ∧
        IsSmoothOffZeroAtlasSymbol
          (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas g) 0)
          (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas g) 1)
          (S.cotangentCliffordPlus g) := by
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  cases S with
  | positive hm o S =>
    exact ⟨S.isLinearMap_cotangentCliffordPlus g, (S.cotangentCliffordPlus_properties g).1⟩
  | nativeZero hzero =>
    subst m
    constructor
    · intro x
      let : Module ℝ (HalfSpinorBundle 0 hP 0 x →ₗ[ℂ] HalfSpinorBundle 0 hP 1 x) :=
        Module.compHom _ Complex.ofRealHom
      constructor
      · intro ξ η
        change (0 : HalfSpinorBundle 0 hP 0 x →ₗ[ℂ] HalfSpinorBundle 0 hP 1 x) = 0 + 0
        exact (zero_add 0).symm
      · intro t ξ
        -- Evaluate the canonical real Hom action through its complex scalar action.
        apply LinearMap.ext
        intro u
        change (0 : HalfSpinorBundle 0 hP 1 x) = (t : ℂ) • (0 : HalfSpinorBundle 0 hP 1 x)
        exact (smul_zero (t : ℂ)).symm
    · -- The off-zero cotangent domain is genuinely empty in native dimension zero.
      intro c hc i j z hz
      have hzero : z.2 = 0 :=
        @Subsingleton.elim (EuclideanSpace ℝ (Fin 0)) inferInstance _ _
      exact (hz.2 hzero).elim

set_option maxHeartbeats 3000000 in
-- Infer the selected original spin connection in its exact associated atlas.
/-- The original Levi-Civita half-spin connection, with its unique zero-dimensional action. -/
def halfSpinorConnection :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ (S : EvenDimensionalSpinInput hP) (i : ZMod 2),
      AtlasComplexConnection (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas g) i) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S i
  cases S with
  | positive hm o S => exact S.halfSpinorConnection g i
  | nativeZero hzero =>
    subst m
    -- Every tangent direction is zero; the existing connection producer keeps the same atlas.
    exact (nonempty_atlasComplexConnection (halfSpinorBundleSmoothAtlas 0 hP
      (smoothSpinPrincipalAtlasZero 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) hP) i)).some

variable {W : M → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 2 * m) W) (covW : AtlasComplexConnection B)

/-- Tensor the original half-spin connection with the very coefficient connection supplied. -/
def twistedHalfSpinorConnection :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ (S : EvenDimensionalSpinInput hP) (i : ZMod 2),
      AtlasComplexConnection
        (tensorSmoothAtlas (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas g) i) B) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S i
  exact atlasTensorConnection (S.halfSpinorConnection g i) covW

set_option maxHeartbeats 3000000 in
-- Infer the original associated tensor atlases, product connection and contraction together.
/-- One actual connection contraction on the original two half-spin tensor section spaces. -/
def twistedDiracPlus :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ S : EvenDimensionalSpinInput hP,
      let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas g)
      AtlasDifferentialOperator (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B) 1 := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas g)
  let c := S.cotangentCliffordPlus g
  have hc := S.cotangentCliffordPlus_properties g
  have h := tensorAtlasSymbol_properties_of_isManifold (H 0) (H 1) B c hc.1 hc.2
  exact atlasConnectionContraction (S.twistedHalfSpinorConnection g B covW 0)
    (tensorAtlasSymbol (W := W) c) h.1 h.2.1

set_option maxHeartbeats 3000000 in
-- Retain that same original tensor connection and its actual section action.
/-- Its action uses the same product covariant derivative and the actual original Clifford map. -/
theorem twistedDiracPlus_apply :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ S : EvenDimensionalSpinInput hP,
      let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas g)
      ∀ (u : (tensorSmoothAtlas (H 0) B).smoothSections) (x : M),
        ((S.twistedDiracPlus g B covW).toLinearMap u).val x =
          ∑ j : Fin (2 * m),
            tensorAtlasSymbol (W := W) (S.cotangentCliffordPlus g) x (EuclideanSpace.proj j)
              ((S.twistedHalfSpinorConnection g B covW 0).covariantDerivative u x
                (EuclideanSpace.single j 1)) := by
  /- Use the action theorem of the same selected contraction. The supplied covW remains
  in its actual tensor connection, including at zero before evaluating the empty sum. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  dsimp only
  intro u x
  unfold twistedDiracPlus
  exact atlasConnectionContraction_apply _ _ _ _ u x

set_option maxHeartbeats 3000000 in
-- Compare the actual original tensor atlases and connection coefficients.
/-- Positive specialization is the original bundled operator on the identical tensor atlases. -/
theorem twistedDiracPlus_positive :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ (hm : 0 < m) (o : ∀ x : M, Orientation ℝ (TM x) (Fin (2 * m)))
      (S : TopologicalSpinStructure m TM o hm hP),
      (EvenDimensionalSpinInput.positive hm o S).twistedDiracPlus g B covW =
        S.twistedDiracPlus g B covW := by
  /- Both definitions use the identical original atlas, spin connection, covW and Clifford
  map. Proof irrelevance identifies only their property certificates, never their data. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro hm o S
  rfl

end EvenDimensionalSpinInput

end OriginalInputs

section NativeZeroComparison

variable {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection}
  (g : SmoothTangentMetric (n := 0) (M := M))
  {W : M → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 0) W) (covW : AtlasComplexConnection B)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
local notation "TM" => (TangentSpace I : M → Type)
local notation "TModel" => EuclideanSpace ℝ (Fin 0)

namespace EvenDimensionalSpinInput

set_option maxHeartbeats 3000000 in
-- Compare the same original native tensor sections and bundled zero contraction.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual zero product contraction equals the original native operator for every covW. -/
theorem twistedDiracPlus_nativeZero :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    let S : EvenDimensionalSpinInput (m := 0) hP := .nativeZero rfl
    EvenDimensionalSpinInput.twistedDiracPlus (m := 0) (M := M) (P := P)
        (projection := projection) (hP := hP) g B covW S =
      zeroTwistedDiracPlus hP (smoothSpinPrincipalAtlasZero I hP) B := by
  /- The original section action is the genuine empty model-basis contraction, for the
  actual product connection containing covW. Uniqueness of the native zero operator
  compares the bundled operators on the same original source and target section spaces. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let S : EvenDimensionalSpinInput (m := 0) hP := .nativeZero rfl
  let A : SmoothSpinPrincipalAtlas 0 I projection := smoothSpinPrincipalAtlasZero I hP
  let H := halfSpinorBundleSmoothAtlas 0 hP A
  let D : AtlasDifferentialOperator (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B) 1 :=
    EvenDimensionalSpinInput.twistedDiracPlus (m := 0) (M := M) (P := P)
      (projection := projection) (hP := hP) g B covW S
  have hzero : D.toLinearMap = 0 := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    have haction :=
      EvenDimensionalSpinInput.twistedDiracPlus_apply (m := 0) (M := M) (P := P)
        (projection := projection) (hP := hP) g B covW S u x
    change (D.toLinearMap u).val x = 0
    refine haction.trans ?_
    -- Every summation index is a Fin 0 element, so the actual product contraction is empty.
    apply Finset.sum_eq_zero
    intro j _
    exact Fin.elim0 (show Fin 0 from j)
  -- The forward action and the identical original atlases determine the bundled operator.
  obtain ⟨Q, _, hunique⟩ := existsUnique_zeroTwistedDiracPlus hP A B
  exact (hunique _ hzero).trans
    (hunique _ (zeroTwistedDiracPlus_properties hP A B).1).symm

end EvenDimensionalSpinInput

end NativeZeroComparison

section CharacteristicFormula

variable {m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))
  {W : M → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 2 * m) W) (covW : AtlasComplexConnection B)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type)
local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))

namespace EvenDimensionalSpinInput

set_option maxHeartbeats 3000000 in
-- Match the finite budget of the original positive characteristic entry.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual twisted index is ch(W) times A-hat in every native even dimension. -/
theorem twistedDiracPlus_index :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := B.isFiniteRank
    ∀ S : EvenDimensionalSpinInput hP,
      (((S.twistedDiracPlus g B covW).toLinearMap.index : ℤ) : ℚ) =
        compactManifoldCohomologyIntegral (S.homologicalOrientation g)
          (spinDiracCharacteristicClass
            (evenDimensionalTangentHermitianMetric (m := m) (M := M))
            (ComplexBundle.kZeroClass W)) := by
  /- The actual operator specifications identify the original positive Dirac or native
  zero contraction, using the same g, W, covW and principal quotient families. The
  internally produced characteristic metric is valid on that same tangent topology.
  Apply the existing positive formula or the direct native finite-dimensional formula
  in precisely the orientation already determined by that same input. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let := B.isFiniteRank
  intro S
  cases S with
  | positive hm o S =>
    rw [twistedDiracPlus_positive g B covW hm o S]
    exact TopologicalSpinStructure.twistedDiracPlus_index g B covW
      (evenDimensionalTangentHermitianMetric (m := m) (M := M)) S
  | nativeZero hzero =>
    subst m
    rw [twistedDiracPlus_nativeZero g B covW]
    exact zeroTwistedDiracPlus_index hP
      (smoothSpinPrincipalAtlasZero 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) hP) B g
      (evenDimensionalTangentHermitianMetric (m := 0) (M := M))

end EvenDimensionalSpinInput

end CharacteristicFormula

end AtiyahSinger

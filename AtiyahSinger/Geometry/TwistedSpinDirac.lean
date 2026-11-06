/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.TensorAtlasSymbolSmooth
public import AtiyahSinger.Geometry.AtlasConnectionContraction
public import AtiyahSinger.Geometry.SmoothSpinCliffordSymbol
public import AtiyahSinger.Geometry.SpinorConnection
public import AtiyahSinger.Geometry.TensorAtlasConnection

/-!
# The canonical twisted chiral Dirac operator on original atlas sections

Public module ID: M1509.

The positive half-spin connection is induced by the specified tangent
metric's actual Levi-Civita connection. Tensor it with the supplied twisting
connection on the original W. Contract that very product derivative with
original Clifford multiplication after the same metric sharp. This defines
D+ on the original S+ tensor W, with values in the original S- tensor W.
The source and target atlases are the specified tensor atlases of S01's
selected half-spin atlases and the given atlas of W, allowing varying ranks.

Sources: SG II.4 Theorem 4.14, II.5 (5.0), Proposition 5.10 and III.13.10.
The definition is valid for any complex connection on W; its unitary version
uses exactly the supplied Hermitian metric, not a separately chosen one.
The symbol is +i times the original Clifford tensor map for D_j=-i partial_j.
No formal-adjoint or index theorem is asserted in this construction. Positive
even dimension is followed separately by the native rank-zero endpoint.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology

set_option maxSynthPendingDepth 40

variable {m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m}
  {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 2 * m) W) (covW : AtlasComplexConnection B)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type _)
local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

/-- The original half-spin connection tensored with the specified connection on W. -/
def twistedHalfSpinorConnection :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ S : TopologicalSpinStructure m TM o hm hP,
    let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
    ∀ i : ZMod 2, AtlasComplexConnection (tensorSmoothAtlas (H i) B) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  dsimp only
  intro i
  exact atlasTensorConnection (S.halfSpinorConnection g i) covW

/-- This same product connection preserves the actual Fock-times-W Hermitian metric. -/
theorem twistedHalfSpinorConnection_isUnitary
    (hW : ComplexBundle.ContinuousHermitianMetric W) (hhW : B.IsSmoothHermitianMetric hW)
    (hcovW : covW.IsUnitary hW) :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ S : TopologicalSpinStructure m TM o hm hP,
    ∀ i : ZMod 2,
      let A := S.smoothPrincipalAtlas I
      (S.twistedHalfSpinorConnection g B covW i).IsUnitary
        (tensorAtlasMetric (halfSpinorHermitianMetric m hP A i)
          (halfSpinorHermitianMetric_properties m hP A i).1 hW hhW) := by
  /- The original half-spin connection preserves the fixed Fock restriction
  by its construction from the same Levi-Civita connection. Apply the tensor
  unitary theorem to that exact connection and hcovW. Its product metric has
  the original pure pairing hS(s,s') hW(w,w'); no new W metric is selected. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S i
  exact atlasTensorConnection_isUnitary (S.halfSpinorConnection g i) covW
    (halfSpinorHermitianMetric m hP (S.smoothPrincipalAtlas I) i)
    (halfSpinorHermitianMetric_properties m hP (S.smoothPrincipalAtlas I) i).1
    hW hhW (S.halfSpinorConnection_properties g i).2 hcovW

set_option maxHeartbeats 1600000 in
-- Normalize the original dependent half-spin tensor atlases in this contraction.
/-- The canonical twisted positive Dirac operator is the actual product-connection contraction. -/
def twistedDiracPlus :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ S : TopologicalSpinStructure m TM o hm hP,
    let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
    AtlasDifferentialOperator (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B) 1 := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
  let c := S.cotangentCliffordPlus g
  have h := tensorAtlasSymbol_properties_of_isManifold (H 0) (H 1) B c
    (S.isLinearMap_cotangentCliffordPlus g) (S.cotangentCliffordPlus_properties g).1
  exact atlasConnectionContraction (S.twistedHalfSpinorConnection g B covW 0)
    (tensorAtlasSymbol (W := W) c) h.1 h.2.1

/-- The selected twisted Dirac operator acts by the same original product derivative and c. -/
theorem twistedDiracPlus_apply :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ S : TopologicalSpinStructure m TM o hm hP,
    let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
    ∀ (u : (tensorSmoothAtlas (H 0) B).smoothSections) (x : M),
      ((S.twistedDiracPlus g B covW).toLinearMap u).val x =
        ∑ j : Fin (2 * m),
          tensorAtlasSymbol (W := W) (S.cotangentCliffordPlus g) x (EuclideanSpace.proj j)
            ((S.twistedHalfSpinorConnection g B covW 0).covariantDerivative u x
              (EuclideanSpace.single j 1)) := by
  /- Unfold the one contraction selected in twistedDiracPlus and use its
  actual action theorem. Both the product connection and tensor symbol are
  the same values used in that definition. The sum is intrinsic by the dual
  basis cancellation in the contraction construction, with fixed chirality. -/
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

/-- The actual twisted chiral principal symbol is +i times c(sharp xi) tensor identity. -/
theorem twistedDiracPlus_principalSymbol :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ S : TopologicalSpinStructure m TM o hm hP,
    ∀ (x : M) (ξ : CotangentFiber (n := 2 * m) x),
      (S.twistedDiracPlus g B covW).principalSymbol x ξ =
        Complex.I • tensorAtlasSymbol (W := W) (S.cotangentCliffordPlus g) x ξ := by
  /- Apply the principal-symbol theorem for the actual connection contraction.
  Its coefficient is exactly the original positive Clifford tensor map, so
  the Fourier convention contributes +i. The local spin and W connection
  terms have order zero and do not contribute to the first-order symbol.
  The equality concerns the selected symbol of the constructed operator;
  it is not a premise asserting that an unrelated operator has that symbol. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S x ξ
  unfold twistedDiracPlus
  exact atlasConnectionContraction_principalSymbol _ _ _ _ x ξ

end TopologicalSpinStructure

end AtiyahSinger

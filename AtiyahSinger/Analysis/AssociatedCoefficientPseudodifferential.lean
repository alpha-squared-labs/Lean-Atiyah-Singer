/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasTensorCoefficientSymbol
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Analysis.PrincipalPseudodifferentialLocalization
public import AtiyahSinger.Geometry.AssociatedOrthogonalRepresentation

/-!
# The coefficient PDO for a fixed principal localization

Public module ID: M0084.

Each original native piece is tensored in its specified principal chart with
the actual associated representation fiber. Their finite sum is the coefficient
PDO, with zero smoothing remainder. The original chart, finite representation,
cutoffs and full local symbols are retained throughout.

Source: the coefficient operator in SG III.13.6. This construction does not
assume the sphere-bundle index formula or replace a coefficient bundle by a
trivial bundle of the same rank.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 30 in
/-- The same native piece with the actual representation frame at its stored principal center. -/
def coefficientPiece {m : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (j : Fin C.size) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    AtlasPseudodifferentialPiece
      (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρ))
      (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
        (associatedOrthogonalRepresentationAtlas S ρ)) m := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  apply (C.piece j).toAtlasPseudodifferentialPiece.tensorCoefficient
    (associatedOrthogonalRepresentationAtlas S ρ) (C.center j)
  · intro x hx
    change (C.piece j).chart.symm x ∈
      (associatedOrthogonalRepresentationChart S ρ (C.center j)).baseSet
    rw [(associatedOrthogonalRepresentationChart_properties S ρ (C.center j)).1]
    exact C.piece_support j ⟨x, Or.inr hx, rfl⟩
  · intro x hx
    change (C.piece j).chart.symm x ∈
      (associatedOrthogonalRepresentationChart S ρ (C.center j)).baseSet
    rw [(associatedOrthogonalRepresentationChart_properties S ρ (C.center j)).1]
    exact C.piece_support j ⟨x, Or.inl hx, rfl⟩

set_option maxSynthPendingDepth 30 in
/-- The coefficient PDO is exactly the sum of the prescribed principal-localized tensor pieces. -/
def coefficientOperator {m : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    AtlasPseudodifferentialOperator
      (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρ))
      (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
        (associatedOrthogonalRepresentationAtlas S ρ)) m := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  refine {
    toLinearMap := ∑ j, (C.coefficientPiece S E E' ρ j).toLinearMap
    isPseudodifferentialOperator := ⟨C.size, C.coefficientPiece S E E' ρ, ?_⟩ }
  rw [sub_self]
  intro L K s t
  exact ⟨0, by intro u; simp only [zero_apply, LinearMap.zero_apply, map_zero]⟩

set_option maxSynthPendingDepth 30 in
/-- Each stored tensor piece has exactly the tensor of the original native cutoff symbol. -/
theorem coefficientPiece_globalSymbolFunction {m : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (j : Fin C.size) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    (C.coefficientPiece S E E' ρ j).globalSymbolFunction =
      tensorAtlasSymbol (W := AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation)
        (nativeAtlasSymbolFunction (C.piece j).globalSymbolFunction) := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  -- The native conversion preserves the original cotangent and fiber maps.
  dsimp only [coefficientPiece]
  erw [AtlasPseudodifferentialPiece.globalSymbolFunction_tensorCoefficient,
    PseudodifferentialPiece.globalSymbolFunction_toAtlasPseudodifferentialPiece]

set_option maxSynthPendingDepth 30 in
/-- The finite-sum tensor symbol represents the principal class of the same coefficient PDO. -/
theorem coefficientOperator_symbol {m : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    ∃ p : atlasGlobalSymbolSpace
        (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
          (associatedOrthogonalRepresentationAtlas S ρ))
        (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
          (associatedOrthogonalRepresentationAtlas S ρ)) m,
      p.val = tensorAtlasSymbol
        (W := AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation)
        (∑ j, nativeAtlasSymbolFunction (C.piece j).globalSymbolFunction) ∧
      (C.coefficientOperator S E E' ρ).principalSymbol =
        atlasGlobalPrincipalSymbolClass _ _ m p := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let p := ∑ j, (C.coefficientPiece S E E' ρ j).globalSymbol
  refine ⟨p, ?_, ?_⟩
  · -- Finite summation commutes with the same tensor identity on actual fibers.
    funext x ξ
    apply TensorProduct.ext'
    intro u w
    change (∑ j, (C.coefficientPiece S E E' ρ j).globalSymbol).val x ξ (u ⊗ₜ[ℂ] w) = _
    simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
    simp_rw [AtlasPseudodifferentialPiece.globalSymbol,
      C.coefficientPiece_globalSymbolFunction S E E' ρ]
    simp only [tensorAtlasSymbol, TensorProduct.map_tmul, LinearMap.id_apply,
      Finset.sum_apply, LinearMap.sum_apply, TensorProduct.sum_tmul]
  · -- The finite representation has the actual zero remainder in every Sobolev order.
    apply (C.coefficientOperator S E E' ρ).principalSymbol_eq_of_representation
      C.size (C.coefficientPiece S E E' ρ)
    change IsAtlasSmoothingOperator _ _ ((∑ j, (C.coefficientPiece S E E' ρ j).toLinearMap) -
      ∑ j, (C.coefficientPiece S E E' ρ j).toLinearMap)
    rw [sub_self]
    intro L K s t
    exact ⟨0, by
      intro u
      simp only [zero_apply, LinearMap.zero_apply, map_zero]⟩

end PrincipalPseudodifferentialLocalization

end AtiyahSinger

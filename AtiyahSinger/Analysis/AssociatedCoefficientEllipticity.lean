/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCoefficientPseudodifferential
public import AtiyahSinger.Analysis.NativeAtlasFullEllipticity
public import AtiyahSinger.Analysis.TensorFullSymbolEllipticity

/-!
# Ellipticity of the specified coefficient operator

Public module ID: M0082.

The actual finite sum of principal-localized coefficient pieces has the tensor
of the original base symbol. Full-symbol ellipticity therefore follows from
the original base operator, without a homogeneous-symbol hypothesis.
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
/-- Ellipticity of the base operator implies ellipticity of its actual coefficient PDO. -/
theorem coefficientOperator_isElliptic {m : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (hC : C.baseOperator.IsElliptic) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    (C.coefficientOperator S E E' ρ).IsElliptic := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let A₀ := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := a') E'
  let p := ∑ j, (C.piece j).globalSymbol
  -- The stored base operator is precisely this sum, so its remainder is the zero kernel.
  have hzero : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := a) E →ₗ[ℂ]
        smoothSections (n := n) (r := a') E') := by
    let K : SmoothKernel (n := n) (r := a) (q := a') E E' := {
      toFun := fun _ _ ↦ 0
      isSmooth := by
        intro f g _ _
        change ContMDiffOn _ _ ∞ (fun z : B × B ↦
          kernelInFrames E E' (fun _ _ ↦ 0) f g z) _
        simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
        exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    ext u x
    change K.apply μ u x = 0
    simp [SmoothKernel.apply, K]
  have hp : C.baseOperator.principalSymbol = globalPrincipalSymbolClass E E' m p :=
    C.baseOperator.principalSymbol_eq_of_representation C.size C.piece (by
      rw [C.baseOperator_eq, sub_self]
      exact hzero)
  have he : IsEllipticFullAtlasSymbol A₀ A₁ m (nativeAtlasSymbolFunction p.val) :=
    (isEllipticFullAtlasSymbol_native_iff m p.val).mpr
      ((C.baseOperator.isElliptic_iff_of_principalSymbol_eq p hp).mp hC)
  have hsum : nativeAtlasSymbolFunction p.val =
      ∑ j, nativeAtlasSymbolFunction (C.piece j).globalSymbolFunction := by
    funext x ξ
    apply LinearMap.ext
    intro v
    simp only [p, nativeAtlasSymbolFunction, Submodule.coe_sum, Finset.sum_apply,
      LinearMap.sum_apply, ContinuousLinearMap.coe_coe, sum_apply]
    rfl
  -- Tensor this same full representative, then use the coefficient operator's actual class.
  obtain ⟨q, hq, hclass⟩ := C.coefficientOperator_symbol S E E' ρ
  refine ⟨q, hclass, ?_⟩
  rw [hq, ← hsum]
  exact he.tensorAtlasSymbol A₀ A₁ (associatedOrthogonalRepresentationAtlas S ρ)

end PrincipalPseudodifferentialLocalization

end AtiyahSinger

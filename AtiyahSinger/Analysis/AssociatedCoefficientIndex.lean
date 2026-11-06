/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCoefficientPseudodifferential
public import AtiyahSinger.Analysis.AtlasNativeIndex
public import AtiyahSinger.Analysis.AtlasTensorGlobalSymbol
public import AtiyahSinger.Analysis.AtlasTensorSymbolKClass
public import AtiyahSinger.Analysis.AtlasTensorSymbolSmooth

/-!
# The index of the actual associated coefficient operator

Public module ID: M0083.

The prescribed principal localization and its original representation bundle
produce the coefficient PDO. Tensoring the actual lower-order difference
identifies its principal class with the same homogeneous coefficient symbol.
The support-triple coefficient comparison then computes its smooth-section
index using the existing constant-rank atlas index theorem.

Source: the coefficient term in SG III.13.6. The actual bundle is retained;
neither its dimension alone nor the associated-sphere index formula is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology
  t2Space_cotangent locallyCompactSpace_cotangent

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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the original coefficient operator and associated symbol-class
-- evaluation.
set_option maxSynthPendingDepth 40 in
/-- The original coefficient PDO computes the index with the actual associated bundle class. -/
theorem coefficientOperator_analyticIndex {m : ℝ}
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (g : SmoothCotangentMetric (n := n) (M := B))
    (b : AtlasSymbolFunction (n := n) E E') :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    let A₀ := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
    let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := a') E'
    let W := AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
    let AC := associatedOrthogonalRepresentationAtlas S ρ
    letI := AC.isFiniteRank
    ∀ (hs : IsSmoothOffZeroAtlasSymbol A₀ A₁ b)
      (hh : IsHomogeneousAtlasSymbol m b) (hi : IsEllipticAtlasSymbol b),
      C.baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
        atlasGlobalPrincipalSymbolClass A₀ A₁ m (atlasRegularizedSymbol A₀ A₁ g m b hs hh) →
      analyticIndexOfComponents μ
          (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
            (ComplexBundle.kZeroClass W) (atlasSymbolKClass A₀ A₁ b hs hi)) =
        (C.coefficientOperator S E E' ρ).toLinearMap.index := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  intro A₀ A₁ W AC
  let := AC.isFiniteRank
  intro hs hh hi hbase
  -- Keep the exact original full symbol sum and its zero operator remainder.
  let p := ∑ j, (C.piece j).globalSymbol
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
  let pA := nativeAtlasGlobalSymbol m p
  let rb := atlasRegularizedSymbol A₀ A₁ g m b hs hh
  have hclass : atlasGlobalPrincipalSymbolClass A₀ A₁ m pA =
      atlasGlobalPrincipalSymbolClass A₀ A₁ m rb :=
    (C.baseOperator.principalSymbol_toAtlasPseudodifferentialOperator p hp).symm.trans hbase
  have hdiff : IsAtlasGlobalSymbol A₀ A₁ (m - 1) (pA.val - rb.val) :=
    (atlasGlobalPrincipalSymbolClass_eq_iff A₀ A₁ m pA rb).mp hclass
  -- The homogeneous coefficient symbol acts on the same fibers, including zero rank.
  let t := tensorAtlasSymbol (W := W) b
  have ht : IsSmoothOffZeroAtlasSymbol (tensorSmoothAtlas A₀ AC)
      (tensorSmoothAtlas A₁ AC) t := hs.tensorAtlasSymbol A₀ A₁ AC b
  have hht : IsHomogeneousAtlasSymbol m t := by
    intro x ξ hξ c hc
    apply TensorProduct.ext'
    intro u w
    simp only [t, tensorAtlasSymbol, hh x ξ hξ c hc, TensorProduct.map_tmul,
      LinearMap.smul_apply, LinearMap.id_apply]
    exact (TensorProduct.smul_tmul' ((c ^ m : ℝ) : ℂ) (b x ξ u) w).symm
  have hit : IsEllipticAtlasSymbol t := by
    intro x ξ hξ
    exact (TensorProduct.congr (LinearEquiv.ofBijective (b x ξ) (hi x ξ hξ))
      (LinearEquiv.refl ℂ (W x))).bijective
  let rt := atlasRegularizedSymbol (tensorSmoothAtlas A₀ AC)
    (tensorSmoothAtlas A₁ AC) g m t ht hht
  obtain ⟨q, hq, hQ⟩ := C.coefficientOperator_symbol S E E' ρ
  have hsum : pA.val = ∑ j, nativeAtlasSymbolFunction (C.piece j).globalSymbolFunction := by
    funext x ξ
    apply LinearMap.ext
    intro u
    simp only [pA, nativeAtlasGlobalSymbol, p, nativeAtlasSymbolFunction,
      Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply,
      ContinuousLinearMap.coe_coe, sum_apply]
    rfl
  have hqval : q.val = tensorAtlasSymbol (W := W) pA.val :=
    hq.trans (congrArg (tensorAtlasSymbol (W := W)) hsum.symm)
  -- Tensor the actual order-(m-1) difference; the same radial cutoff commutes with tensoring.
  have hsub : q.val - rt.val = tensorAtlasSymbol (W := W) (pA.val - rb.val) := by
    rw [hqval]
    funext x ξ
    apply TensorProduct.ext'
    intro u w
    change pA.val x ξ u ⊗ₜ[ℂ] w -
      (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) •
        (b x ξ u ⊗ₜ[ℂ] w) =
      (pA.val x ξ u -
        (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) •
          b x ξ u) ⊗ₜ[ℂ] w
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul']
  have hQclass : (C.coefficientOperator S E E' ρ).principalSymbol =
      atlasGlobalPrincipalSymbolClass (tensorSmoothAtlas A₀ AC)
        (tensorSmoothAtlas A₁ AC) m rt := by
    refine hQ.trans ((atlasGlobalPrincipalSymbolClass_eq_iff _ _ m q rt).mpr ?_)
    rw [hsub]
    exact hdiff.tensorAtlasSymbol A₀ A₁ AC (pA.val - rb.val)
  -- The actual tensor ranks permit native evaluation without replacing the coefficient bundle.
  have hr (x : B) : Module.finrank ℂ (E x ⊗[ℂ] W x) = a * ρ.dimension := by
    rw [Module.finrank_tensorProduct, VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin a)) E x,
      (associatedVectorFiberLinearEquiv S.toIsPrincipalBundle ρ.representation x).finrank_eq]
    simp
  have hr' (x : B) : Module.finrank ℂ (E' x ⊗[ℂ] W x) = a' * ρ.dimension := by
    rw [Module.finrank_tensorProduct,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin a')) E' x,
      (associatedVectorFiberLinearEquiv S.toIsPrincipalBundle ρ.representation x).finrank_eq]
    simp
  have hK := atlasSymbolKClass_tensor A₀ A₁ AC b hs hi ht hit
  rw [← hK]
  exact (C.coefficientOperator S E E' ρ).analyticIndexOfComponents_of_constant_rank μ
    (a * ρ.dimension) (a' * ρ.dimension) hr hr' g t ht hht hit hQclass

end PrincipalPseudodifferentialLocalization

end AtiyahSinger


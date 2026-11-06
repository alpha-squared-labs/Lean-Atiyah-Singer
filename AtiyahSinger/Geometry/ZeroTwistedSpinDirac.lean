/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPrincipalSymbol
public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Geometry.SmoothSpinorBundle
public import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# The native zero-dimensional twisted Dirac endpoint

Public module ID: M1519.

On a zero-dimensional manifold every tangent direction vanishes, so the
connection contraction is the zero operator for every twisting connection.
Its original source is the even associated line tensor W and its target is
the original odd zero bundle tensor W. Both use the specified principal
atlas and the original tensor topology; W may have varying finite ranks.
The symbol vanishes, and ellipticity off the zero section is vacuous.

This is the explicit native rank-zero continuation of the construction in
SG II.5 (5.0) and III.13.10, not a twofold Spin(0) cover attributed to SG.
An empty symbol exterior does not make its K class zero: the original
source-minus-target class remains and is compared in ZeroTwistedSpinSymbolClass.
The operator and symbol certificates are proved below; the selected operator
is fixed by its exact zero action before its symbol is considered.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology

variable {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)
  (A : SmoothSpinPrincipalAtlas 0 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) projection)
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 0) W)

local notation "H" => halfSpinorBundleSmoothAtlas 0 hP A

/-- The native rank-zero contraction is uniquely fixed by its actual zero section action. -/
theorem existsUnique_zeroTwistedDiracPlus :
    ∃! D : AtlasDifferentialOperator (tensorSmoothAtlas (H 0) B)
        (tensorSmoothAtlas (H 1) B) 1, D.toLinearMap = 0 := by
  /- Stage 1: the zero complex-linear map takes smooth source sections
  to the zero section in the specified target atlas. Every coordinate
  expression has zero coefficients, so its differential order is at most one.
  Stage 2: any bundled operator with that same zero section action has
  the same data field. Proof irrelevance identifies its order certificate,
  establishing uniqueness of the bundled zero operator. -/
  classical

  have _baseSmooth : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M := inferInstance
  have _baseHausdorff : T2Space M := inferInstance
  have _baseSecondCountable : SecondCountableTopology M := inferInstance
  -- The zero action has the zero coordinate expression in every original pair of frames.
  refine ⟨⟨0, ?_⟩, rfl, ?_⟩
  · intro c hc i j x hx
    let C := tensorSmoothAtlas (H 0) B
    let D := tensorSmoothAtlas (H 1) B
    let U := c.source ∩ (C.chart i).baseSet ∩ (D.chart j).baseSet
    have hU : IsOpen U :=
      (c.open_source.inter (C.chart i).open_baseSet).inter (D.chart j).open_baseSet
    let Q : CoordinateDifferentialOperator 0 (C.rank i) (D.rank j) 1 (c '' U) :=
      { coefficient := fun _ _ _ ↦ 0
        smooth_coefficient := fun _ _ ↦ contDiffOn_const }
    refine ⟨U, hU, hx, Q, Set.Subset.rfl, ?_⟩
    intro s y hy
    change (EuclideanSpace.equiv (Fin (D.rank j)) ℂ).symm
      ((D.chart j ⟨y, 0⟩).2) = Q.apply _ (c y)
    rw [(D.linear j y hy.2).map_zero]
    simp [Q, CoordinateDifferentialOperator.apply]
  · -- The section action is the sole data field; the order certificate is proof irrelevant.
    intro D hD
    cases D
    cases hD
    rfl

/-- The actual zero-dimensional twisted Dirac operator on the original two tensor bundles. -/
def zeroTwistedDiracPlus :
    AtlasDifferentialOperator (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B) 1 :=
  (existsUnique_zeroTwistedDiracPlus hP A B).exists.choose

/-- The selected zero-dimensional operator has zero action and the actual zero principal symbol. -/
theorem zeroTwistedDiracPlus_properties :
    (zeroTwistedDiracPlus hP A B).toLinearMap = 0 ∧
      ∀ (x : M) (ξ : CotangentFiber (n := 0) x),
        (zeroTwistedDiracPlus hP A B).principalSymbol x ξ = 0 := by
  /- Read the zero action from the selected existence witness. Every
  cotangent vector is zero in dimension zero. The chosen order-one symbol
  is homogeneous of degree one. Applying principalSymbol_smul at scale zero
  forces its value at that covector to vanish. -/
  -- The chosen action is zero; degree-one homogeneity forces the symbol at zero to vanish.
  refine ⟨(existsUnique_zeroTwistedDiracPlus hP A B).exists.choose_spec, ?_⟩
  intro x ξ
  have hξ : ξ = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = 0 := by
      exact @Subsingleton.elim (EuclideanSpace ℝ (Fin 0)) inferInstance v 0
    simp only [hv, map_zero]
  have hsymbol := (zeroTwistedDiracPlus hP A B).principalSymbol_smul x ξ 0
  simpa only [Complex.ofReal_zero, zero_smul, pow_one, hξ] using hsymbol

/-- The same zero symbol is smooth and elliptic on its empty off-zero domain. -/
theorem zeroTwistedDiracPlus_symbol_properties :
    IsSmoothOffZeroAtlasSymbol (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B)
        (zeroTwistedDiracPlus hP A B).principalSymbol ∧
      IsEllipticAtlasSymbol (zeroTwistedDiracPlus hP A B).principalSymbol := by
  /- There are no nonzero cotangent vectors in dimension zero. The
  off-zero smoothness and bijectivity conditions therefore quantify over
  an empty set. This does not assert an isomorphism from the original
  positive line tensor W to the odd zero fiber at the zero covector. -/
  -- Every coordinate cotangent and every original cotangent is zero in dimension zero.
  constructor
  · intro c hc i j z hz
    exact (hz.2 (show z.2 = 0 from Subsingleton.elim _ _)).elim
  · intro x ξ hξ
    apply (hξ ?_).elim
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = 0 := by
      exact @Subsingleton.elim (EuclideanSpace ℝ (Fin 0)) inferInstance v 0
    simp only [hv, map_zero]

end AtiyahSinger

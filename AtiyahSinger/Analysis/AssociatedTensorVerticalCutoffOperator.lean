/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.AtlasTensorCoefficientPiece
public import AtiyahSinger.Analysis.RightProductCutoffRealization
public import AtiyahSinger.Analysis.CompatibleChartGlobalOperator

/-!
# Vertical product cutoffs on the associated tensor bundles

Public module ID: M0199.

The fixed base-first tensor frames and supplied coordinate maps produce an
order-one PDO for each positive regularization parameter. The complete
right-factor symbol retains the base-coordinate exchange and both tensor
coefficient permutations. Its quantization uses the same associated atlas.

Source: SG III.13.5--13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z


local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)] [∀ y, Module ℂ (F' y)]
  [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive vertical regularization realizes its full right-factor symbol on the same bundles. -/
theorem exists_associatedSphereTensorVerticalCutoffOperator
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (Ci Co : BundleChartCutoff (r := a) E c)
    (hi : c.symm '' tsupport Ci.cutoff ⊆ (S.trivialization b).baseSet)
    (ho : c.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : d ∈ atlas Y (OrthogonalSphere r))
    (Ki : AtlasChartCutoff A d) (Ko : AtlasChartCutoff A' d)
    (α : SymbolFunction r (A.rank Ki.frameIndex) (A'.rank Ko.frameIndex))
    (hα : IsSymbol Set.univ 1 α) (hcα : HasCompactSupport α)
    (ρ : X → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) :
    letI := modelTopology V₀ E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let C := associatedSphereProductChart S b c d
    let Din := associatedSphereTensorChartCutoff S E A σ hσ b c Ci hi d Ki
    let Dout := associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co ho d Ko
    let β : SymbolFunction r (A.rank Ki.frameIndex * a) (A'.rank Ko.frameIndex * a) :=
      fun y η ↦ tensorIdentitySymbolMap (A.rank Ki.frameIndex) (A'.rank Ko.frameIndex) a (α y η)
    tsupport Din.cutoff ⊆ C.symm ⁻¹' (AT'.chart Dout.frameIndex).baseSet →
    tsupport Dout.cutoff ⊆ C.symm ⁻¹' (AT.chart Din.frameIndex).baseSet →
    ∀ (I : AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank Ki.frameIndex))))
      (O : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank Ko.frameIndex))) →ₗ[ℂ] AT'.smoothSections),
      (∀ u z, I u z = Din.localizedFunction u z) →
      (∀ v x, (O v).val x = Dout.extendedFunction v x) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (Q : AtlasPseudodifferentialOperator AT AT' 1)
          (U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank Ki.frameIndex))) →L[ℂ]
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank Ko.frameIndex)))),
          Q.toLinearMap = O.comp (U.toLinearMap.comp I) ∧
            ∀ w z, U w z = quantize (rightProductCutoffSymbol β ρ ε) w z := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  dsimp only
  intro hio hoi I O hI hO ε hε
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let C := associatedSphereProductChart S b c d
  let Din : AtlasChartCutoff AT C :=
    associatedSphereTensorChartCutoff S E A σ hσ b c Ci hi d Ki
  let Dout : AtlasChartCutoff AT' C :=
    associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co ho d Ko
  let β : SymbolFunction r (A.rank Ki.frameIndex * a) (A'.rank Ko.frameIndex * a) :=
    fun y η ↦ tensorIdentitySymbolMap (A.rank Ki.frameIndex) (A'.rank Ko.frameIndex) a (α y η)
  have hβ : IsSymbol Set.univ 1 β :=
    isSymbol_continuousLinearMap 1 α hα
      ((tensorIdentitySymbolMap (A.rank Ki.frameIndex) (A'.rank Ko.frameIndex) a).restrictScalars ℝ)
  have hcβ : HasCompactSupport β := by
    apply hcα.of_isClosed_subset (isClosed_tsupport β)
    apply closure_minimal _ (isClosed_tsupport α)
    intro y hy
    by_contra hout
    apply hy
    funext η
    change tensorIdentitySymbolMap _ _ _ (α y η) = 0
    rw [image_eq_zero_of_notMem_tsupport hout]
    exact (tensorIdentitySymbolMap _ _ _).map_zero
  -- The original base and fiber permutations occur inside this very full symbol.
  let p := rightProductCutoffSymbol (n := n) (m := r) (r := a)
    (s := A.rank Ki.frameIndex) (t := A'.rank Ko.frameIndex) β ρ ε
  have hp : IsSymbol Set.univ 1 p := isSymbol_rightProductCutoffSymbol β hβ ρ hρ ε hε
  have hcp : HasCompactSupport p := hasCompactSupport_rightProductCutoffSymbol β hcβ ρ hcρ ε
  let U := quantizeSchwartz 1 p hp hcp
  have hU : ∀ w z, U w z = quantize p w z := quantizeSchwartz_apply 1 p hp hcp
  have hchart : C ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b c hc d hd
  have hPDO : IsAtlasPseudodifferentialOperator AT AT' 1 (O.comp (U.toLinearMap.comp I)) :=
    isAtlasPseudodifferentialOperator_of_mem_maximalAtlas AT AT' C hchart Din Dout
      hio hoi U p hp hU I O hI hO
  exact ⟨⟨O.comp (U.toLinearMap.comp I), hPDO⟩, U, rfl, hU⟩

end AtiyahSinger

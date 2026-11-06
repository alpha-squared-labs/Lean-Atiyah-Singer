/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.AtlasTensorCoefficientPiece
public import AtiyahSinger.Analysis.CompatibleChartGlobalOperator

/-!
# Product cutoffs on the associated tensor bundles for positive parameters

Public module ID: M0189.

The supplied localization and extension maps determine an atlas PDO for each
positive product-frequency regularization parameter. The specified complete
base symbol is amplified with the identity in the same sphere frame. The
conclusion retains the complete quantization and each coordinate-column action.

Chart transport preserves the associated quotient, bundle atlases, input and
output cutoffs, frame ranks, and smooth-section maps. The input and output maps
are supplied before the regularization parameter.
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


variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)
local notation "V₁" => EuclideanSpace ℂ (Fin a')

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive regularization gives the actual associated PDO with its full column action. -/
theorem exists_associatedSphereTensorProductCutoffOperator
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (Ci : BundleChartCutoff (r := a) E c)
    (Co : BundleChartCutoff (r := a') E' c)
    (hi : c.symm '' tsupport Ci.cutoff ⊆ (S.trivialization b).baseSet)
    (ho : c.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : d ∈ atlas Y (OrthogonalSphere r)) (K : AtlasChartCutoff A d)
    (κ : Y → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsκ : tsupport κ ⊆ d.target ∩ d.symm ⁻¹' (A.chart K.frameIndex).baseSet)
    (α : SymbolFunction n a a') (hα : IsSymbol Set.univ 1 α) (hcα : HasCompactSupport α)
    (ρ : Y → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) :
    letI := modelTopology V₀ E
    letI := modelTopology V₁ E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let C := associatedSphereProductChart S b c d
    let Ko : AtlasChartCutoff A d := ⟨K.frameIndex, κ, hκ, hcκ, hsκ⟩
    let Din := associatedSphereTensorChartCutoff S E A σ hσ b c Ci hi d K
    let Dout := associatedSphereTensorChartCutoff S E' A σ hσ b c Co ho d Ko
    tsupport Din.cutoff ⊆ C.symm ⁻¹' (AT'.chart Dout.frameIndex).baseSet →
    tsupport Dout.cutoff ⊆ C.symm ⁻¹' (AT.chart Din.frameIndex).baseSet →
    ∀ (I : AT.smoothSections →ₗ[ℂ] 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank K.frameIndex))))
      (O : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank K.frameIndex))) →ₗ[ℂ] AT'.smoothSections),
      (∀ u z, I u z = Din.localizedFunction u z) →
      (∀ v x, (O v).val x = Dout.extendedFunction v x) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (Q : AtlasPseudodifferentialOperator AT AT' 1)
          (U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank K.frameIndex))) →L[ℂ]
            𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank K.frameIndex)))),
          Q.toLinearMap = O.comp (U.toLinearMap.comp I) ∧
          (∀ w z, U w z = quantize
            (fun y ξ ↦ tensorIdentitySymbolMap a a' (A.rank K.frameIndex)
              (productCutoffSymbol α ρ ε y ξ)) w z) ∧
          ∀ j : Fin (A.rank K.frameIndex),
            ∃ Dcol : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank K.frameIndex))) →L[ℂ]
                𝓢(XY, V₀),
              (∀ w z i, Dcol w z i = w z (finProdFinEquiv (i, j))) ∧
              ∀ w z i, U w z (finProdFinEquiv (i, j)) =
                quantize (productCutoffSymbol α ρ ε) (Dcol w) z i := by
  classical
  let := modelTopology V₀ E
  let := modelTopology V₁ E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  dsimp only
  intro hio hoi I O hI hO ε hε
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let C := associatedSphereProductChart S b c d
  let Ko : AtlasChartCutoff A d := ⟨K.frameIndex, κ, hκ, hcκ, hsκ⟩
  let Din : AtlasChartCutoff AT C :=
    associatedSphereTensorChartCutoff S E A σ hσ b c Ci hi d K
  let Dout : AtlasChartCutoff AT' C :=
    associatedSphereTensorChartCutoff S E' A σ hσ b c Co ho d Ko
  let p := productCutoffSymbol α ρ ε
  have hp : IsSymbol Set.univ 1 p := isSymbol_productCutoffSymbol α hα ρ hρ ε hε
  have hcp : HasCompactSupport p := hasCompactSupport_productCutoffSymbol α hcα ρ hcρ ε
  let P := quantizeSchwartz 1 p hp hcp
  -- Use the established complete finite coefficient amplification in the original column order.
  obtain ⟨U, hU, hcol⟩ := exists_schwartz_tensorCoefficient (A.rank K.frameIndex) 1 p hp P
    (quantizeSchwartz_apply 1 p hp hcp)
  have hfull : IsSymbol Set.univ 1
      (fun y ξ ↦ tensorIdentitySymbolMap a a' (A.rank K.frameIndex) (p y ξ)) :=
    isSymbol_continuousLinearMap 1 p hp
      ((tensorIdentitySymbolMap a a' (A.rank K.frameIndex)).restrictScalars ℝ)
  have hchart : C ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b c hc d hd
  have hPDO : IsAtlasPseudodifferentialOperator AT AT' 1 (O.comp (U.toLinearMap.comp I)) :=
    isAtlasPseudodifferentialOperator_of_mem_maximalAtlas AT AT' C hchart Din Dout
      hio hoi U _ hfull hU I O hI hO
  refine ⟨⟨O.comp (U.toLinearMap.comp I), hPDO⟩, U, rfl, hU, ?_⟩
  intro j
  obtain ⟨Dcol, hDcol, hUcol⟩ := hcol j
  refine ⟨Dcol, hDcol, ?_⟩
  intro w z i
  rw [hUcol]
  exact congrArg (fun v : V₁ ↦ v i) (quantizeSchwartz_apply 1 p hp hcp (Dcol w) z)

end AtiyahSinger

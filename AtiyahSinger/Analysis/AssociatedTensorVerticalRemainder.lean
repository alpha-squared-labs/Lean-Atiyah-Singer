/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalOperator
public import AtiyahSinger.Analysis.NativePresentationChartCutoff
public import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# Exact global vertical decomposition with the original local remainders

Public module ID: M0211.

A native base partition and its specified principal charts combine actual
local smooth operators. Their support and normalized return formulas identify
the literal difference from the full original equivariant sphere operator.
The residuals are actual smooth maps supported over the original base weights,
and their sum restores the whole vertical operator exactly.

If the supplied sphere pieces form PDO representations, their literal sphere
differences are the original smoothing remainders. This theorem proves the
exact gluing and value identities; boundedness of these residuals is separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

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

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Local vertical pieces and their literal supported residuals recover the full original map. -/
theorem exists_associatedSphereTensorVertical_remainders
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
    (Q : AtlasPseudodifferentialOperator A A' 1)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (N : Fin J.size → ℕ) (L : ∀ k : Fin J.size,
      Fin (N k) → AtlasPseudodifferentialPiece A A' 1) :
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
    letI (x : B) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
    ∀ Tj : ∀ k : Fin J.size, Fin (N k) → AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
      (∀ k j (w : AT.smoothSections) z,
        πS z ∉ tsupport (J.cutoff k) → (Tj k j w).val z = 0) →
      (∀ k j (w : AT.smoothSections) x, x ∈ (J.chart k).source →
        x ∈ (S.trivialization (b k)).baseSet → x ∈ (J.frame k).baseSet →
        ∀ y : OrthogonalSphere r,
          let q := (S.trivialization (b k)).toOpenPartialHomeomorph.symm (x, 1)
          (Tj k j w).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
            (J.cutoff k x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
              ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
                (L k j).toLinearMap (associatedSphereTensorFiberRestriction (a := a)
                  S E A σ hσ q w)).val y)) →
      ∃ W : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
        V = (∑ k, ∑ j, Tj k j) + ∑ k, W k ∧
        (∀ k (w : AT.smoothSections) z,
          πS z ∉ tsupport (J.cutoff k) → (W k w).val z = 0) ∧
        ∀ k (w : AT.smoothSections) x, x ∈ (J.chart k).source →
          x ∈ (S.trivialization (b k)).baseSet → x ∈ (J.frame k).baseSet →
          ∀ y : OrthogonalSphere r,
            let q := (S.trivialization (b k)).toOpenPartialHomeomorph.symm (x, 1)
            (W k w).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
              (J.cutoff k x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
                  (Q.toLinearMap - ∑ j, (L k j).toLinearMap)
                  (associatedSphereTensorFiberRestriction (a := a)
                    S E A σ hσ q w)).val y) := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let ef := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let dm := linearModelDiffeomorph ef.symm Z
  let := linearModelChartedSpace ef.symm Z
  let := isManifold_linearModelChartedSpace ef.symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' Q hQ
  dsimp only
  intro Tj hTzero hTreturn
  have hπ : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ πS :=
    (smoothAssociatedSphereProjection S).contMDiff.comp dm.symm.contMDiff
  let M (k : Fin J.size) : AT'.smoothSections →ₗ[ℂ] AT'.smoothSections :=
    atlasSectionMul AT' (fun z ↦ (J.cutoff k (πS z) : ℂ))
      (Complex.ofRealCLM.contMDiff.comp ((J.smooth_cutoff k).comp hπ))
  let W (k : Fin J.size) : AT.smoothSections →ₗ[ℂ] AT'.smoothSections :=
    (M k).comp V - ∑ j, Tj k j
  have hW (k : Fin J.size) (w : AT.smoothSections) (z : Z) :
      (W k w).val z = (J.cutoff k (πS z) : ℂ) • (V w).val z - ∑ j, (Tj k j w).val z := by
    simp only [W, M, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      Submodule.coe_sub, Submodule.coe_sum, Finset.sum_apply, Pi.sub_apply, atlasSectionMul]
    rfl
  refine ⟨W, ?_, ?_, ?_⟩
  · -- The very same native partition restores the full vertical action at every point.
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    funext z
    have hsum (v : T' z) : (∑ k : Fin J.size, (J.cutoff k (πS z) : ℂ) • v) = v := by
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, J.sum_cutoff, Complex.ofReal_one]
      exact one_smul ℂ v
    change (V w).val z = _
    simp only [LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add,
      Submodule.coe_sum, Finset.sum_apply, Pi.add_apply, hW, Finset.sum_sub_distrib, hsum]
    abel
  · intro k w z hz
    rw [hW, image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, zero_smul]
    have hzero : (∑ j, (Tj k j w).val z) = 0 :=
      Finset.sum_eq_zero (fun j _ ↦ hTzero k j w z hz)
    rw [hzero, sub_zero]
  · intro k w x hx hxb hxe y
    let q := (S.trivialization (b k)).toOpenPartialHomeomorph.symm (x, 1)
    let z := associatedBundleMk G P (OrthogonalSphere r) q y
    have hprojection : πS z = x :=
      (S.trivialization (b k)).proj_symm_apply' hxb
    have hwhole : (V w).val z = associatedSphereTensorFiberEquiv S E σ' q y
        ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
          Q.toLinearMap (associatedSphereTensorFiberRestriction (a := a)
            S E A σ hσ q w)).val y) :=
      associatedSphereTensorVerticalOperator_apply (a := a) S E A σ hσ A' σ' hσ' Q hQ w q y
    -- Tensor extension is linear in the same whole sphere operator, before evaluation.
    let u := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ q w
    let U := E (projection q)
    have hsum : (∑ j, (L k j).toLinearMap).lTensor U =
        ∑ j, ((L k j).toLinearMap.lTensor U) :=
      map_sum (LinearMap.lTensorHom U) (fun j ↦ (L k j).toLinearMap) Finset.univ
    have hsplit : tensorSectionOperator U A.smoothSections A'.smoothSections
        (Q.toLinearMap - ∑ j, (L k j).toLinearMap) u =
        tensorSectionOperator U A.smoothSections A'.smoothSections Q.toLinearMap u -
          ∑ j, tensorSectionOperator U A.smoothSections A'.smoothSections
            (L k j).toLinearMap u := by
      simp only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.lTensor_sub, hsum, LinearMap.sub_apply, LinearMap.sum_apply, map_sub, map_sum]
    have hweight : (J.cutoff k (πS z) : ℂ) = (J.cutoff k x : ℂ) :=
      congrArg (fun x ↦ (J.cutoff k x : ℂ)) hprojection
    rw [hW k w z, hweight, hwhole]
    have hpieces : (∑ j, (Tj k j w).val z) =
        ∑ j, (J.cutoff k x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
          ((tensorSectionOperator U A.smoothSections A'.smoothSections (L k j).toLinearMap u).val
            y) :=
      Finset.sum_congr rfl (fun j _ ↦ hTreturn k j w x hx hxb hxe y)
    rw [hpieces]
    change _ = (J.cutoff k x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
      ((tensorSectionOperator U A.smoothSections A'.smoothSections
        (Q.toLinearMap - ∑ j, (L k j).toLinearMap) u).val y)
    rw [hsplit]
    simp only [Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply,
      map_sub, map_sum, smul_sub, Finset.smul_sum]
    rfl

end AtiyahSinger

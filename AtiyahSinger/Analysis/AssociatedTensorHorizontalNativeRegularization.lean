/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalCutoffFactor
public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalDualApproximation
public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalRegularization
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalSymbolFactor
public import AtiyahSinger.Analysis.AtlasNativePrincipalConjugate
public import AtiyahSinger.Analysis.FiniteRegularizationNormBounds

/-!
# Native horizontal regularization with its tensor factor

Public module ID: M0171.

The horizontal lift has a family of native order-one operators with the cutoff
tensor-symbol representative and simultaneous positive and negative Sobolev
error bounds. The bounded limiting horizontal realization and both error
constants are chosen before the regularization parameter.

The caller supplies the native models and smooth equivalences. The estimates
use the canonical transport of this same native family through those fixed
equivalences.
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

variable [T2Space B]

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

variable [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

namespace PrincipalPseudodifferentialLocalization


set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 24000000 in
-- The extended limit accommodates the full dependent native horizontal regularization.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One native horizontal regularization retains the actual tensor factor and
both Sobolev error estimates in the caller's fixed native models. -/
theorem exists_horizontalLift_native_regularization
    (L : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (J : AtlasBundlePresentation A) :
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
    ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT')
      (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η]
      (Nin Nout : SmoothFiniteComplexBundle (n := n + r) Z),
      letI := modelTopology (EuclideanSpace ℂ (Fin Nin.rank)) Nin.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin Nout.rank)) Nout.Fiber
      let Ai := nativeSmoothComplexBundleAtlas (n := n + r) (r := Nin.rank) Nin.Fiber
      let Ao := nativeSmoothComplexBundleAtlas (n := n + r) (r := Nout.rank) Nout.Fiber
      ∀ (ei : Iso T Nin.Fiber) (eo : Iso T' Nout.Fiber)
        (hei : IsSmoothAtlasBundleMap AT Ai ei.toHom.linearMap)
        (hii : IsSmoothAtlasBundleMap Ai AT ei.symm.toHom.linearMap)
        (heo : IsSmoothAtlasBundleMap AT' Ao eo.toHom.linearMap)
        (hio : IsSmoothAtlasBundleMap Ao AT' eo.symm.toHom.linearMap),
        let Si := (atlasSmoothSectionEquiv AT Ai ei hei hii).trans
          (nativeSmoothSectionLinearEquiv (n := n + r) (r := Nin.rank) Nin.Fiber)
        let So := (atlasSmoothSectionEquiv AT' Ao eo heo hio).trans
          (nativeSmoothSectionLinearEquiv (n := n + r) (r := Nout.rank) Nout.Fiber)
        let Eps := {ε : ℝ // 0 < ε ∧ ε ≤ 1}
        ∃ (R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0) (Cp Cn : ℝ)
          (Pn : Eps → PseudodifferentialOperator Nin.Fiber Nout.Fiber η 1)
          (pn : Eps → globalSymbolSpace Nin.Fiber Nout.Fiber 1),
          (∀ u, R (Li.smoothToSobolev 1 u) =
            Lo.smoothToSobolev 0 (L.horizontalLift S E A σ E' hσ u)) ∧
          0 ≤ Cp ∧ 0 ≤ Cn ∧
          (∀ ε, (Pn ε).principalSymbol =
            globalPrincipalSymbolClass Nin.Fiber Nout.Fiber 1 (pn ε)) ∧
          (∀ ε z ξ u v, (pn ε).val z ξ (ei.linearEquiv z (u ⊗ₜ[ℂ] v)) =
            eo.linearEquiv z
              (horizontalCutoffFactor S E A E' L J ε.val z ξ u ⊗ₜ[ℂ] v)) ∧
          (∀ ε u,
            ‖Lo.smoothToSobolev 0
              (So.symm ((Pn ε).toLinearMap (Si u)) - L.horizontalLift S E A σ E' hσ u)‖ ≤
              Cp * ε.val * ‖Li.smoothToSobolev 1 u‖) ∧
          (∀ ε u,
            ‖Lo.smoothToSobolev (-1)
              (So.symm ((Pn ε).toLinearMap (Si u)) - L.horizontalLift S E A σ E' hσ u)‖ ≤
              Cn * ε.val * ‖Li.smoothToSobolev 0 u‖) := by
  classical
  let := modelTopology V₀ E
  let := modelTopology V₁ E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro AT AT' Li Lo η hη Nin Nout
  let := modelTopology (EuclideanSpace ℂ (Fin Nin.rank)) Nin.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin Nout.rank)) Nout.Fiber
  intro Ai Ao ei eo hei hii heo hio Si So Eps
  -- Select the finite chart construction once, before the regularization parameter.
  have hreg := L.exists_horizontalLift_regularization S E A σ E' hσ J Li Lo
  let Co : ∀ i : Fin L.size, BundleChartCutoff (r := a') E' (L.piece i).chart :=
    hreg.choose
  have hCo := hreg.choose_spec.choose
  let κ : Fin L.size → Fin J.size → Y → ℝ := hreg.choose_spec.choose_spec.choose
  have hκ := hreg.choose_spec.choose_spec.choose_spec.choose
  have hκK := hreg.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hκs := hreg.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hrest := hreg.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hCoF := hrest.1
  have hCoI := hrest.2.1
  have hCoOne := hrest.2.2.1
  have hκOne := hrest.2.2.2.1
  have hlocal := hrest.2.2.2.2
  let I := hlocal.choose
  let O := hlocal.choose_spec.choose
  have hmaps := hlocal.choose_spec.choose_spec
  have hI := hmaps.1
  have hO := hmaps.2.1
  let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := hmaps.2.2.choose
  have hRdata := hmaps.2.2.choose_spec
  have hR := hRdata.1
  let Cp : ℝ := hRdata.2.choose
  have hCp := hRdata.2.choose_spec.1
  have hpositive := hRdata.2.choose_spec.2
  have hnegative := L.horizontalLift_error_sobolev_neg_one_bound S E A σ E' hσ J
    Co hCoF hCo hCoOne κ hκ hκK hκs hκOne I O hI hO Li Lo
  let Cn : ℝ := hnegative.choose
  have hCn := hnegative.choose_spec.1
  -- Transport each regularized operator to the fixed native models with its symbol.
  have hone (ε : Eps) :
      ∃ (p : globalSymbolSpace Nin.Fiber Nout.Fiber 1)
        (P : PseudodifferentialOperator Nin.Fiber Nout.Fiber η 1),
        P.principalSymbol = globalPrincipalSymbolClass Nin.Fiber Nout.Fiber 1 p ∧
        (∀ z ξ u v, p.val z ξ (ei.linearEquiv z (u ⊗ₜ[ℂ] v)) =
          eo.linearEquiv z
            (horizontalCutoffFactor S E A E' L J ε.val z ξ u ⊗ₜ[ℂ] v)) ∧
        (∀ u, ‖Lo.smoothToSobolev 0
          (So.symm (P.toLinearMap (Si u)) - L.horizontalLift S E A σ E' hσ u)‖ ≤
          Cp * ε.val * ‖Li.smoothToSobolev 1 u‖) ∧
        (∀ u, ‖Lo.smoothToSobolev (-1)
          (So.symm (P.toLinearMap (Si u)) - L.horizontalLift S E A σ E' hσ u)‖ ≤
          Cn * ε.val * ‖Li.smoothToSobolev 0 u‖) := by
    have hcut := hpositive ε.val ε.property.1 ε.property.2
    let Q := hcut.choose
    let Ulocal := hcut.choose_spec.choose
    let Rε := hcut.choose_spec.choose_spec.choose
    have hdata := hcut.choose_spec.choose_spec.choose_spec
    have hprincipalData := L.exists_horizontalCutoff_principalSymbol
      S E A σ E' hσ J Co hCo κ hκ hκK hκs hCoF hCoI
      I O hI hO ε.val ε.property.1 Q Ulocal hdata.1 hdata.2.1
    let g := hprincipalData.choose
    have hg := hprincipalData.choose_spec.1
    let U := hprincipalData.choose_spec.2.choose
    have hU := hprincipalData.choose_spec.2.choose_spec.1
    have hsU := hprincipalData.choose_spec.2.choose_spec.2
    let s : atlasGlobalSymbolSpace AT AT' 1 := ∑ i, ∑ j, g i j
    have hnative := U.exists_native_conjugate_principalSymbol (μ := η) s hsU
      Nin Nout ei eo hei hii heo hio
    let p := hnative.choose
    let P := hnative.choose_spec.choose
    have hp := hnative.choose_spec.choose_spec.1
    have hP := hnative.choose_spec.choose_spec.2.1
    have hprincipal := hnative.choose_spec.choose_spec.2.2.1
    have hfactor (z : Z) (ξ : CotangentFiber (n := n + r) z) :
        s.val z ξ = TensorProduct.map
          (horizontalCutoffFactor S E A E' L J ε.val z ξ)
          (LinearMap.id : Module.End ℂ (D z)) := by
      let ev : atlasGlobalSymbolSpace AT AT' 1 →ₗ[ℂ] (T z →ₗ[ℂ] T' z) :=
        (LinearMap.proj ξ).comp ((LinearMap.proj z).comp
          (atlasGlobalSymbolSpace AT AT' 1).subtype)
      have heval := (map_sum ev (fun i : Fin L.size ↦ ∑ j : Fin J.size, g i j)
        Finset.univ).trans
          (Finset.sum_congr rfl (fun i _ ↦ map_sum ev
            (fun j : Fin J.size ↦ g i j) Finset.univ))
      refine heval.trans ?_
      have hi (i : Fin L.size) := associatedSphereTensorHorizontalSymbol_eq_finiteTensorFactor
        S E A σ E' (L.piece i) hσ (L.center i)
        (fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support i ⟨x, Or.inr hx, hxy⟩)
        (fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support i ⟨x, Or.inl hx, hxy⟩)
        J (Co i) (hCoF i) (hCo i) (hCoOne i) (κ i) (hκ i) (hκK i)
        (hκs i) (hκOne i) ε.val (fun j ↦ (g i j).val) (hg i) z ξ
      change (∑ i, ∑ j, (g i j).val z ξ) = _
      rw [Finset.sum_congr rfl (fun i _ ↦ hi i)]
      change (∑ j : Fin L.size, (LinearMap.rTensorHom (R := ℂ) (D z)) _) =
        (LinearMap.rTensorHom (R := ℂ) (D z)) _
      exact (map_sum (LinearMap.rTensorHom (R := ℂ) (D z)) _ Finset.univ).symm
    have htensor (z : Z) (ξ : CotangentFiber (n := n + r) z)
        (u : E (πS z)) (v : D z) :
        p.val z ξ (ei.linearEquiv z (u ⊗ₜ[ℂ] v)) = eo.linearEquiv z
          (horizontalCutoffFactor S E A E' L J ε.val z ξ u ⊗ₜ[ℂ] v) := by
      have h := LinearMap.congr_fun (hp z ξ) (ei.linearEquiv z (u ⊗ₜ[ℂ] v))
      change p.val z ξ (ei.linearEquiv z (u ⊗ₜ[ℂ] v)) =
        eo.linearEquiv z (s.val z ξ ((ei.linearEquiv z).symm
          (ei.linearEquiv z (u ⊗ₜ[ℂ] v)))) at h
      rw [LinearEquiv.symm_apply_apply, hfactor z ξ,
        TensorProduct.map_tmul, LinearMap.id_apply] at h
      exact h
    -- Both errors belong to this very same native operator and its chart transport.
    have htransport (w : AT.smoothSections) :
        So.symm (P.toLinearMap (Si w)) = U.toLinearMap w := by
      rw [hP]
      change So.symm (So (U.toLinearMap (Si.symm (Si w)))) = U.toLinearMap w
      rw [Si.symm_apply_apply, So.symm_apply_apply]
    have hpaired (w : AT.smoothSections) :=
      finite_regularization_paired_norm_bounds
        (κ₀ := Fin L.size) (κ₁ := Fin J.size)
        (Li.smoothToSobolev 1) (Li.smoothToSobolev 0)
        (Lo.smoothToSobolev 0) (Lo.smoothToSobolev (-1))
        (L.horizontalLift S E A σ E' hσ) (L.horizontalLift S E A σ E' hσ) 0
        (fun _ : Unit ↦ U.toLinearMap) (fun _ k j ↦ (Q k j).toLinearMap)
        (fun _ k j v ↦ O k j (Ulocal k j (I k j v)))
        R (fun _ ↦ Rε) Cp Cn (fun _ : Unit ↦ ε.val)
        (add_zero (L.horizontalLift S E A σ E' hσ)).symm hR
        (fun _ k j v ↦ congrArg (fun f : AT.smoothSections →ₗ[ℂ] AT'.smoothSections ↦ f v)
          (hdata.1 k j))
        (fun _ ↦ hU) (fun _ v ↦ hdata.2.2.1 v) (fun _ ↦ hdata.2.2.2)
        (fun _ v ↦ by
          have hb := hnegative.choose_spec.2 ε.val ε.property.1 ε.property.2
            Ulocal hdata.2.1 v
          simpa only [LinearMap.zero_apply, add_zero] using hb)
        () w
    refine ⟨p, P, hprincipal, htensor, ?_, ?_⟩
    · intro w
      -- The section-transport identity gives the same Sobolev error norm.
      have heq :
          ‖Lo.smoothToSobolev 0
            (So.symm (P.toLinearMap (Si w)) - L.horizontalLift S E A σ E' hσ w)‖ =
          ‖Lo.smoothToSobolev 0 (U.toLinearMap w - L.horizontalLift S E A σ E' hσ w)‖ :=
        congrArg (fun v : AT'.smoothSections ↦
          ‖Lo.smoothToSobolev 0 (v - L.horizontalLift S E A σ E' hσ w)‖) (htransport w)
      apply heq.le.trans
      simpa only [LinearMap.zero_apply, add_zero] using (hpaired w).1
    · intro w
      have heq :
          ‖Lo.smoothToSobolev (-1)
            (So.symm (P.toLinearMap (Si w)) - L.horizontalLift S E A σ E' hσ w)‖ =
          ‖Lo.smoothToSobolev (-1) (U.toLinearMap w - L.horizontalLift S E A σ E' hσ w)‖ :=
        congrArg (fun v : AT'.smoothSections ↦
          ‖Lo.smoothToSobolev (-1) (v - L.horizontalLift S E A σ E' hσ w)‖) (htransport w)
      apply heq.le.trans
      simpa only [LinearMap.zero_apply, add_zero] using (hpaired w).2
  choose pn Pn hprincipal htensor hpos hneg using hone
  exact ⟨R, Cp, Cn, Pn, pn, hR, hCp, hCn, hprincipal, htensor, hpos, hneg⟩

end PrincipalPseudodifferentialLocalization

end AtiyahSinger

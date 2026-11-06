/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasNativeSumSobolev
public import AtiyahSinger.Analysis.SobolevAdjointCoordinateIndex

/-!
# Sobolev and specified order-zero coordinates of a bundle sum

Public module ID: M0811.

The same specified native direct sum has continuous linear coordinates at
Sobolev orders one and zero. The order-zero coordinates compose with the given
corner equivalences to the prescribed normed spaces. Both coordinate maps retain
the original section-sum formula on smooth cores.

The separate `sobolevCoordinateRealization` definition gives the actual conjugated
order-one PDO realization. It retains the operator, presentations and coordinates
as parameters, so a caller can use the same definition for a PDO and its literal
metric adjoint. These definitions do not select Green models or cutoff families.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

section SumCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {E₁ E₂ : M → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace Unit E₁)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace Unit E₂)]

include μ

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2000000 in
-- Complete both Sobolev orders through the same specified native-sum coordinates.
/-- The same native sum has order-one Sobolev and prescribed order-zero coordinates. -/
theorem exists_sobolev_and_nativeL2_coordinates_of_atlas_native_sum
    (A₁ : SmoothComplexBundleAtlas (n := n) E₁) (L₁ : AtlasBundlePresentation A₁)
    (A₂ : SmoothComplexBundleAtlas (n := n) E₂) (L₂ : AtlasBundlePresentation A₂)
    (N₁ N₂ N : SmoothFiniteComplexBundle (n := n) M)
    (K₁ : SmoothBundlePresentation (n := n) (r := N₁.rank) N₁.Fiber)
    (K₂ : SmoothBundlePresentation (n := n) (r := N₂.rank) N₂.Fiber)
    (K : SmoothBundlePresentation (n := n) (r := N.rank) N.Fiber)
    {X₁ X₂ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂]
    (Θ₁ : L₁.SobolevSpace 0 ≃L[ℂ] X₁) (Θ₂ : L₂.SobolevSpace 0 ≃L[ℂ] X₂)
    (i₁ : A₁.smoothSections →ₗ[ℂ] X₁) (i₂ : A₂.smoothSections →ₗ[ℂ] X₂)
    (hΘ₁ : ∀ u, Θ₁ (L₁.smoothToSobolev 0 u) = i₁ u)
    (hΘ₂ : ∀ u, Θ₂ (L₂.smoothToSobolev 0 u) = i₂ u) :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
    ∀ (e₁ : Iso E₁ N₁.Fiber)
      (he₁ : IsSmoothAtlasBundleMap A₁ (nativeSmoothComplexBundleAtlas N₁.Fiber)
        e₁.toHom.linearMap)
      (hi₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁.Fiber) A₁
        e₁.symm.toHom.linearMap)
      (e₂ : Iso E₂ N₂.Fiber)
      (he₂ : IsSmoothAtlasBundleMap A₂ (nativeSmoothComplexBundleAtlas N₂.Fiber)
        e₂.toHom.linearMap)
      (hi₂ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₂.Fiber) A₂
        e₂.symm.toHom.linearMap)
      (e : ∀ x, (N₁.Fiber x × N₂.Fiber x) ≃ₗ[ℂ] N.Fiber x)
      (h₁ : IsSmoothBundleMap (n := n) (r := N₁.rank) (q := N.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (N₁.Fiber x) (N₂.Fiber x))))
      (h₂ : IsSmoothBundleMap (n := n) (r := N₂.rank) (q := N.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (N₁.Fiber x) (N₂.Fiber x)))),
      let S₁ := (atlasSmoothSectionEquiv A₁ (nativeSmoothComplexBundleAtlas N₁.Fiber)
        e₁ he₁ hi₁).trans (nativeSmoothSectionLinearEquiv N₁.Fiber)
      let S₂ := (atlasSmoothSectionEquiv A₂ (nativeSmoothComplexBundleAtlas N₂.Fiber)
        e₂ he₂ hi₂).trans (nativeSmoothSectionLinearEquiv N₂.Fiber)
      let S := smoothSectionSumEquiv e h₁ h₂
      ∃ (Φ : K.SobolevSpace 1 ≃L[ℂ] WithLp 2 (L₁.SobolevSpace 1 × L₂.SobolevSpace 1))
        (Ψ : K.SobolevSpace 0 ≃L[ℂ] WithLp 2 (X₁ × X₂)),
        (∀ u v, Φ (K.smoothToSobolev 1 (S (S₁ u, S₂ v))) =
          WithLp.toLp 2 (L₁.smoothToSobolev 1 u, L₂.smoothToSobolev 1 v)) ∧
        (∀ u v, Ψ (K.smoothToSobolev 0 (S (S₁ u, S₂ v))) =
          WithLp.toLp 2 (i₁ u, i₂ v)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  intro e₁ he₁ hi₁ e₂ he₂ hi₂ e h₁ h₂ S₁ S₂ S
  -- Complete the same sum in its two required orders, keeping its original presentations.
  obtain ⟨Φ, hΦ⟩ := exists_sobolevEquiv_of_atlas_native_sum (μ := μ)
    A₁ L₁ A₂ L₂ N₁ N₂ N K₁ K₂ K 1 e₁ he₁ hi₁ e₂ he₂ hi₂ e h₁ h₂
  obtain ⟨Φ₀, hΦ₀⟩ := exists_sobolevEquiv_of_atlas_native_sum (μ := μ)
    A₁ L₁ A₂ L₂ N₁ N₂ N K₁ K₂ K 0 e₁ he₁ hi₁ e₂ he₂ hi₂ e h₁ h₂
  -- The order-zero map lands in the prescribed native L² corners through the given Θ maps.
  let c₀ := WithLp.prodContinuousLinearEquiv 2 ℂ (L₁.SobolevSpace 0) (L₂.SobolevSpace 0)
  let cX := WithLp.prodContinuousLinearEquiv 2 ℂ X₁ X₂
  let Ψ := Φ₀.trans (c₀.trans ((Θ₁.prodCongr Θ₂).trans cX.symm))
  refine ⟨Φ, Ψ, hΦ, ?_⟩
  intro u v
  have hsum := congrArg (fun w ↦ cX.symm ((Θ₁.prodCongr Θ₂) (c₀ w))) (hΦ₀ u v)
  have hcorners :
      (Θ₁ (L₁.smoothToSobolev 0 u), Θ₂ (L₂.smoothToSobolev 0 v)) = (i₁ u, i₂ v) :=
    Prod.ext (hΘ₁ u) (hΘ₂ v)
  exact hsum.trans (congrArg cX.symm hcorners)

end SumCoordinates

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

namespace PseudodifferentialOperator

/-- The actual order-one Sobolev realization in two specified continuous linear coordinates. -/
def sobolevCoordinateRealization
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (Φ : A.SobolevSpace 1 ≃L[ℂ] X) (Ψ : B.SobolevSpace 0 ≃L[ℂ] Y) : X →L[ℂ] Y :=
  Ψ.toContinuousLinearMap.comp
    ((P.sobolevRealization A B 1 0 (by norm_num)).comp Φ.symm.toContinuousLinearMap)

end PseudodifferentialOperator

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbol
public import AtiyahSinger.Analysis.AssociatedVerticalCovectorRestriction
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Algebra.HermitianTensorInverseBound
public import AtiyahSinger.Analysis.AssociatedVerticalCutoffInverse
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalCutoffInverse
public import AtiyahSinger.Analysis.AssociatedProductFiniteCotangentBounds
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbolInverse
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbolSaturation
public import AtiyahSinger.Analysis.SplitCotangentCutoffSaturation

/-!
# A quantitative inverse for the actual four finite cutoff factors

Public module ID: M0089.

The horizontal and vertical factors use the original localizations, partitions,
full symbols and chart covectors. Their uniform inverse energy estimates cover
the two complementary cones. The original Hermitian forms identify the supplied
reverse factors with actual adjoints. The resulting four-corner tensor matrix
has a uniform lower norm bound on its original fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology

variable {n r d e : ℕ} {ι P B : Type*} [Fintype ι] [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {F F' : OrthogonalSphere r → Type*}
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin d)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin d)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin d)) F]
  [IsSmoothComplexBundle (n := r) (r := d) F]
  [∀ y, NormedAddCommGroup (F' y)] [∀ y, NormedSpace ℂ (F' y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin e)) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin e)) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin e)) F']
  [IsSmoothComplexBundle (n := r) (r := e) F']
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

local notation "H" => EuclideanSpace ℝ (Fin (n + r))

variable [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable {a a' : ℕ} [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
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
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3200000 in
-- Normalize the original finite cutoff tensor matrix and uniform inverse estimate.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in
open scoped Classical in
/-- The original finite cutoff tensor matrix has a uniform inverse lower bound. -/
theorem exists_associatedSphereCutoffTensorSymbol_inverse_bound
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C.baseOperator.IsElliptic)
    (gB : SmoothCotangentMetric (n := n) (M := B))
    (hE : SmoothHermitianMetric (n := n) (r := a) E)
    (kE : SmoothHermitianMetric (n := n) (r := a') E')
    (q : globalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hq : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g q.val = q.val)
    (hEll : IsEllipticFullGlobalSymbol (r := d) (q := e) F F' 1 q.val)
    (g : SmoothCotangentMetric (n := r) (M := OrthogonalSphere r))
    (h : SmoothHermitianMetric (n := r) (r := d) F)
    (k : SmoothHermitianMetric (n := r) (r := e) F')
    (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
      ∀ (g : G) (y : OrthogonalSphere r) (u v : F y),
      h.pairing (g • y) (σ.linearMap g y u) (σ.linearMap g y v) = h.pairing y u v)
    (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
      ∀ (g : G) (y : OrthogonalSphere r) (u v : F' y),
      k.pairing (g • y) (τ.linearMap g y u) (τ.linearMap g y v) = k.pairing y u v) :
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := associatedSphereChartedSpace S
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := d) F
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := e) F'
    let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
    let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle τ
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle τ z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle τ z
    ∀ (hσ : σ.IsSmoothAtlas IG A) (hτ : τ.IsSmoothAtlas IG A')
      (J : AtlasBundlePresentation A) (R : AtlasQuantizationPresentation A A')
      (b : ι → B) (c : ι → OpenPartialHomeomorph B X) (_hc : ∀ i, c i ∈ atlas X B)
      (θ : ι → X → ℝ) (_hθK : ∀ i, HasCompactSupport (θ i))
      (_hθchart : ∀ i, tsupport (θ i) ⊆ (c i).target)
      (_hθbase : ∀ i, (c i).symm '' tsupport (θ i) ⊆ (S.trivialization (b i)).baseSet)
      (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (_hc₀ : c₀ ∈ atlas X B)
      (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
      (_hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
      (K : Set H) (_hK : IsCompact K)
      (_hKChart : K ⊆ (associatedSphereProductChart S b₀ c₀ d₀).target)
      (e₀ : Trivialization (EuclideanSpace ℂ (Fin d)) (π (EuclideanSpace ℂ (Fin d)) F))
      (f₀ : Trivialization (EuclideanSpace ℂ (Fin e)) (π (EuclideanSpace ℂ (Fin e)) F'))
      [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀]
      (Ky : Set (OrthogonalSphere r)) (_hKy : IsCompact Ky)
      (_hKye : Ky ⊆ d₀.source ∩ e₀.baseSet) (_hKyf : Ky ⊆ d₀.source ∩ f₀.baseSet)
      (_hKfiber : ∀ z ∈ K, (associatedSphereTrivialization S b₀
        ((associatedSphereProductChart S b₀ c₀ d₀).symm z)).2 ∈ Ky)
      (eB : Trivialization (EuclideanSpace ℂ (Fin a)) (π (EuclideanSpace ℂ (Fin a)) E))
      (fB : Trivialization (EuclideanSpace ℂ (Fin a')) (π (EuclideanSpace ℂ (Fin a')) E'))
      [MemTrivializationAtlas eB] [MemTrivializationAtlas fB],
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := linearModelChartedSpace split.symm Z
      let AD := associatedSphereSmoothBundleAtlas S A σ hσ
      let AD' := associatedSphereSmoothBundleAtlas S A' τ hτ
      let CP := associatedSphereProductChart S b₀ c₀ d₀
      let t := fun i ↦ associatedSphereTrivialization S (b i)
      let L := fun j ↦ (R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)
      let Ci := fun i j ↦ associatedSphereProductChart S (b i) (c i) (L j).chart
      let CH := fun i j ↦ associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
      let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
      let x := fun z : H ↦ base (CP.symm z)
      let weight := fun i (z : Z) ↦
        if z ∈ (t i).source ∧ (t i z).1 ∈ (c i).source then θ i (c i (t i z).1) else 0
      (∀ z ∈ K, x z ∈ eB.baseSet ∩ fB.baseSet) →
      (∀ z ∈ K, ∑ i, weight i (CP.symm z) = 1) →
      ∃ ε₀ R₀ M : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R₀ ∧ 0 ≤ M ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z ∈ K, ∀ ξ η, R₀ ≤ ‖ξ‖ + ‖η‖ →
          let coefficient : ℝ := M / (1 + ‖ξ‖ + ‖η‖)
          let pre := CP.symm z
          let Ξ := covectorFromChart CP pre (split.symm (ξ, η))
          let covH := fun i j ↦ split (covectorInChart (CH i j) pre Ξ)
          let P := (∑ i, ∑ j,
            ((J.cutoff j (associatedSphereTrivialization S (C.center i) pre).2 *
              productFrequencyCutoff ε ‖(covH i j).1‖ ‖(covH i j).2‖ : ℝ) : ℂ) •
                (C.piece i).globalSymbolFunction (x z)
                  (covectorFromChart (C.piece i).chart (x z) (covH i j).1)).toLinearMap
          let cov := fun i j ↦ split (covectorInChart (Ci i j) pre Ξ)
          let factor := fun i j ↦
            if hz : pre ∈ (Ci i j).source ∩
                (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
                (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
              let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) pre hz.1.2).trans
                (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
              let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) pre hz.2).trans
                (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
              ((θ i (c i (t i pre).1) * (L j).input.cutoff ((L j).chart (t i pre).2) *
                (L j).output.cutoff ((L j).chart (t i pre).2) *
                productFrequencyCutoff ε ‖(cov i j).2‖ ‖(cov i j).1‖ : ℝ) : ℂ) •
                  (eOut.symm.toLinearMap.comp
                    (((L j).symbol ((L j).chart (t i pre).2) (cov i j).2).toLinearMap.comp
                      eIn.toLinearMap))
            else (0 : D pre →ₗ[ℂ] D' pre)
          let Q := ∑ i, ∑ j, factor i j
          let h₀ := hE.toCore (x z)
          let h₁ := kE.toCore (x z)
          let k₀ := associatedEquivariantMetricCore S.toIsPrincipalBundle σ
            h.toContinuousHermitianMetric pre
          let k₁ := associatedEquivariantMetricCore S.toIsPrincipalBundle τ
            k.toContinuousHermitianMetric pre
          ∀ (pi : E' (x z) →ₗ[ℂ] E (x z)) (qi : D' pre →ₗ[ℂ] D pre),
            (∀ u v, h₁.inner (P u) v = h₀.inner u (pi v)) →
            (∀ u v, k₁.inner (Q u) v = k₀.inner u (qi v)) →
            letI : Module ℂ (E (x z)) := inferInstance
            letI : Module ℂ (E' (x z)) := inferInstance
            letI : InnerProductSpace.Core ℂ (E (x z)) := h₀
            letI : InnerProductSpace.Core ℂ (E' (x z)) := h₁
            letI : InnerProductSpace.Core ℂ (D pre) := k₀
            letI : InnerProductSpace.Core ℂ (D' pre) := k₁
            letI : NormedAddCommGroup (E (x z)) :=
              InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
            letI : NormedAddCommGroup (E' (x z)) :=
              InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
            letI : NormedAddCommGroup (D pre) :=
              InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
            letI : NormedAddCommGroup (D' pre) :=
              InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
            letI : TopologicalSpace (D pre) :=
              (inferInstance : PseudoMetricSpace (D pre)).toUniformSpace.toTopologicalSpace
            letI : TopologicalSpace (D' pre) :=
              (inferInstance : PseudoMetricSpace (D' pre)).toUniformSpace.toTopologicalSpace
            letI : InnerProductSpace ℂ (E (x z)) := InnerProductSpace.ofCore
              (inferInstance : PreInnerProductSpace.Core ℂ _)
            letI : InnerProductSpace ℂ (E' (x z)) := InnerProductSpace.ofCore
              (inferInstance : PreInnerProductSpace.Core ℂ _)
            letI : InnerProductSpace ℂ (D pre) := InnerProductSpace.ofCore
              (inferInstance : PreInnerProductSpace.Core ℂ _)
            letI : InnerProductSpace ℂ (D' pre) := InnerProductSpace.ofCore
              (inferInstance : PreInnerProductSpace.Core ℂ _)
            let T := reciprocalTensorSymbol P pi Q qi
            Function.Bijective T ∧ ∀ u, ‖u‖ ≤ coefficient * ‖T u‖ :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
  intro A A' D D'
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) := associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle τ z
  let (z : Z) : Module ℂ (D' z) := associatedEquivariantFiberModule S.toIsPrincipalBundle τ z
  intro hσ hτ J R b c hc θ hθK hθchart hθbase b₀ c₀ hc₀ d₀ hd₀ K hK hKChart
    e₀ f₀ _ _ Ky hKy hKye hKyf hKfiber eB fB _ _ split
  let := linearModelChartedSpace split.symm Z
  intro AD AD' CP t L Ci CH base x weight hframe hpartition
  -- Choose both cone estimates before the point, the covector or any reverse map.
  obtain ⟨εH, δH, RH, MH, hεH, hεHone, hδH, hRH, hMH, hhorizontal⟩ :=
    C.exists_horizontalCutoffFullSymbol_conic_metric_inverse_bound S E E' A hC J gB hE kE
      b₀ c₀ hc₀ d₀ hd₀ eB fB K hK hKChart hframe
  obtain ⟨δ, εV, RV, MV, hδ, hδle, hεV, hεVone, hRV, hMV, hvertical⟩ :=
    exists_associatedSphereVerticalCutoffFullSymbol_inverse_bound S σ τ q hq hEll g h k
      hInvariant kInvariant hσ hτ R b c hc θ hθK hθchart hθbase
      b₀ c₀ hc₀ d₀ hd₀ K hK hKChart e₀ f₀ Ky hKy hKye hKyf hKfiber δH hδH hpartition
  let ε₀ := min εH εV
  let R₀ := (1 + δ) * RH + (1 + δ⁻¹) * RV + 1
  let M₀ := (MH + 1) * (1 + δ) + (MV + 1) * (1 + δ⁻¹)
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  refine ⟨ε₀, R₀, 2 * M₀, lt_min hεH hεV,
    (min_le_left _ _).trans hεHone, hR₀, by positivity, ?_⟩
  intro ε hε hεle z hz ξ η hlarge coefficient pre Ξ covH P cov factor Q h₀ h₁ k₀ k₁
    pi qi hpi hqi
  let eb := (eB.continuousLinearEquivAt ℂ (x z) (hframe z hz).1).toLinearEquiv
  let fb := (fB.continuousLinearEquivAt ℂ (x z) (hframe z hz).2).toLinearEquiv
  let _ : Module ℂ (E (x z)) := inferInstance
  let _ : Module ℂ (E' (x z)) := inferInstance
  let : InnerProductSpace.Core ℂ (E (x z)) := h₀
  let : InnerProductSpace.Core ℂ (E' (x z)) := h₁
  let : InnerProductSpace.Core ℂ (D pre) := k₀
  let : InnerProductSpace.Core ℂ (D' pre) := k₁
  let : NormedAddCommGroup (E (x z)) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (E' (x z)) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (D pre) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (D' pre) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : TopologicalSpace (D pre) :=
    (inferInstance : PseudoMetricSpace (D pre)).toUniformSpace.toTopologicalSpace
  let : TopologicalSpace (D' pre) :=
    (inferInstance : PseudoMetricSpace (D' pre)).toUniformSpace.toTopologicalSpace
  let : InnerProductSpace ℂ (E (x z)) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : InnerProductSpace ℂ (E' (x z)) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : InnerProductSpace ℂ (D pre) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : InnerProductSpace ℂ (D' pre) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  intro T
  let : FiniteDimensional ℂ (E (x z)) := .of_injective eb.toLinearMap eb.injective
  let : FiniteDimensional ℂ (E' (x z)) := .of_injective fb.toLinearMap fb.injective
  let ef := AD.frameLinearEquiv (AD.covers pre).choose pre (AD.covers pre).choose_spec
  let ff := AD'.frameLinearEquiv (AD'.covers pre).choose pre (AD'.covers pre).choose_spec
  let : FiniteDimensional ℂ (D pre) := .of_injective ef.toLinearMap ef.injective
  let : FiniteDimensional ℂ (D' pre) := .of_injective ff.toLinearMap ff.injective
  let p : E (x z) →L[ℂ] E' (x z) := P.toContinuousLinearMap
  let q₀ : D pre →L[ℂ] D' pre := Q.toContinuousLinearMap
  have hden : 0 < 1 + ‖ξ‖ + ‖η‖ := by positivity
  -- The cone estimates overlap because the vertical threshold is at most the horizontal threshold.
  -- Thus one actual factor controls every ray.
  have hfactor : (p.IsInvertible ∧ ‖p.inverse‖ ≤ M₀ / (1 + ‖ξ‖ + ‖η‖)) ∨
      (q₀.IsInvertible ∧ ‖q₀.inverse‖ ≤ M₀ / (1 + ‖ξ‖ + ‖η‖)) := by
    by_cases hcone : ‖η‖ ≤ δ * ‖ξ‖
    · left
      have hξ : RH ≤ ‖ξ‖ := by
        have hpos : 0 ≤ (1 + δ⁻¹) * RV := by positivity
        dsimp [R₀] at hlarge
        by_contra hnot
        have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) (show 0 < 1 + δ by positivity)
        nlinarith
      have hb := hhorizontal ε hε (hεle.trans (min_le_left _ _)) z hz ξ η hξ
        (hcone.trans (mul_le_mul_of_nonneg_right hδle (norm_nonneg ξ)))
      change Function.Bijective P ∧ ∀ u, (h₀.inner u u).re ≤
        MH / (1 + ‖ξ‖) ^ 2 * (h₁.inner (P u) (P u)).re at hb
      have hp : p.IsInvertible :=
        ⟨(LinearEquiv.ofBijective P hb.1).toContinuousLinearEquiv, rfl⟩
      have hpinv : ‖p.inverse‖ ≤ (MH + 1) / (1 + ‖ξ‖) := by
        apply p.inverse.opNorm_le_bound (by positivity)
        intro u
        have he := hb.2 (p.inverse u)
        change (inner ℂ _ _).re ≤ _ at he
        have hix (v : E (x z)) : (h₀.inner v v).re = ‖v‖ ^ 2 :=
          (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
        have hiy (v : E' (x z)) : (h₁.inner v v).re = ‖v‖ ^ 2 :=
          (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
        rw [hix, hiy] at he
        change ‖p.inverse u‖ ^ 2 ≤ MH / (1 + ‖ξ‖) ^ 2 * ‖p (p.inverse u)‖ ^ 2 at he
        rw [hp.self_apply_inverse] at he
        have hsq : MH ≤ (MH + 1) ^ 2 := by nlinarith
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        calc
          ‖p.inverse u‖ ^ 2 ≤ MH / (1 + ‖ξ‖) ^ 2 * ‖u‖ ^ 2 := he
          _ ≤ (MH + 1) ^ 2 / (1 + ‖ξ‖) ^ 2 * ‖u‖ ^ 2 := by gcongr
          _ = _ := by rw [mul_pow, div_pow]
      refine ⟨hp, hpinv.trans ?_⟩
      apply (div_le_div_iff₀ (by positivity) hden).mpr
      dsimp [M₀]
      nlinarith [mul_nonneg (show 0 ≤ MV + 1 by positivity)
        (show 0 ≤ (1 + δ⁻¹) * (1 + ‖ξ‖) by positivity)]
    · right
      have hcone' : δ * ‖ξ‖ ≤ ‖η‖ := (lt_of_not_ge hcone).le
      have hη : RV ≤ ‖η‖ := by
        have hpos : 0 ≤ (1 + δ) * RH := by positivity
        have hξ : ‖ξ‖ ≤ δ⁻¹ * ‖η‖ := by
          apply (le_inv_mul_iff₀ hδ).mpr
          exact hcone'
        dsimp [R₀] at hlarge
        by_contra hnot
        have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hnot)
          (show 0 < 1 + δ⁻¹ by positivity)
        nlinarith
      have hb := hvertical ε hε (hεle.trans (min_le_right _ _)) z hz ξ η hcone' hη
      change Function.Bijective Q ∧ ∀ u, (k₀.inner u u).re ≤
        MV / (1 + ‖η‖) ^ 2 * (k₁.inner (Q u) (Q u)).re at hb
      have hq₀ : q₀.IsInvertible :=
        ⟨(LinearEquiv.ofBijective Q hb.1).toContinuousLinearEquiv, rfl⟩
      have hqinv : ‖q₀.inverse‖ ≤ (MV + 1) / (1 + ‖η‖) := by
        apply q₀.inverse.opNorm_le_bound (by positivity)
        intro u
        have he := hb.2 (q₀.inverse u)
        have hix (v : D pre) : (k₀.inner v v).re = ‖v‖ ^ 2 :=
          (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
        have hiy (v : D' pre) : (k₁.inner v v).re = ‖v‖ ^ 2 :=
          (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
        rw [hix, hiy] at he
        change ‖q₀.inverse u‖ ^ 2 ≤ MV / (1 + ‖η‖) ^ 2 * ‖q₀ (q₀.inverse u)‖ ^ 2 at he
        rw [hq₀.self_apply_inverse] at he
        have hsq : MV ≤ (MV + 1) ^ 2 := by nlinarith
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        calc
          ‖q₀.inverse u‖ ^ 2 ≤ MV / (1 + ‖η‖) ^ 2 * ‖u‖ ^ 2 := he
          _ ≤ (MV + 1) ^ 2 / (1 + ‖η‖) ^ 2 * ‖u‖ ^ 2 := by gcongr
          _ = _ := by rw [mul_pow, div_pow]
      refine ⟨hq₀, hqinv.trans ?_⟩
      apply (div_le_div_iff₀ (by positivity) hden).mpr
      have hξ : ‖ξ‖ ≤ δ⁻¹ * ‖η‖ := (le_inv_mul_iff₀ hδ).mpr hcone'
      have hd : 1 + ‖ξ‖ + ‖η‖ ≤ (1 + δ⁻¹) * (1 + ‖η‖) := by
        have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
        nlinarith
      calc
        (MV + 1) * (1 + ‖ξ‖ + ‖η‖) ≤
            (MV + 1) * ((1 + δ⁻¹) * (1 + ‖η‖)) := by gcongr
        _ ≤ M₀ * (1 + ‖η‖) := by
          dsimp [M₀]
          nlinarith [mul_nonneg (show 0 ≤ MH + 1 by positivity)
            (show 0 ≤ (1 + δ) * (1 + ‖η‖) by positivity)]
  -- The original pairings identify the same reverse maps, with the prescribed signs.
  have hpi' : pi = P.adjoint := by
    have he : P = pi.adjoint := (LinearMap.eq_adjoint_iff P pi).mpr hpi
    rw [he, LinearMap.adjoint_adjoint]
  have hqi' : qi = Q.adjoint := by
    have he : Q = qi.adjoint := (LinearMap.eq_adjoint_iff Q qi).mpr hqi
    rw [he, LinearMap.adjoint_adjoint]
  have ht := reciprocalTensorSymbol_isInvertible_of_inverse_bound p q₀
    (M₀ / (1 + ‖ξ‖ + ‖η‖)) (div_nonneg hM₀ hden.le) hfactor
  have hT : T = reciprocalTensorSymbol P P.adjoint Q Q.adjoint := by
    simp only [T, hpi', hqi']
  change (reciprocalTensorSymbol P P.adjoint Q Q.adjoint).toContinuousLinearMap.IsInvertible ∧
    ‖(reciprocalTensorSymbol P P.adjoint Q Q.adjoint).toContinuousLinearMap.inverse‖ ≤
      2 * (M₀ / (1 + ‖ξ‖ + ‖η‖)) at ht
  rw [← hT] at ht
  have hcoef : 2 * (M₀ / (1 + ‖ξ‖ + ‖η‖)) = coefficient := by dsimp [coefficient]; ring
  rw [hcoef] at ht
  refine ⟨⟨ht.1.injective, ht.1.surjective⟩, ?_⟩
  intro u
  calc
    ‖u‖ = ‖T.toContinuousLinearMap.inverse (T u)‖ :=
      congrArg norm (ht.1.inverse_apply_self u).symm
    _ ≤ ‖T.toContinuousLinearMap.inverse‖ * ‖T u‖ :=
      T.toContinuousLinearMap.inverse.le_opNorm _
    _ ≤ coefficient * ‖T u‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)

end AtiyahSinger

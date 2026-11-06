/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianCoreTensorSymbol
public import AtiyahSinger.Analysis.AssociatedProductFiniteCotangentBounds
public import AtiyahSinger.Analysis.AssociatedVerticalCovectorRestriction
public import AtiyahSinger.Analysis.AssociatedVerticalCutoffInverse
public import AtiyahSinger.Analysis.AssociatedVerticalCutoffRecovery
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbol
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbolInverse
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbolSaturation
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalAffineInverse
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalCutoffRecovery
public import AtiyahSinger.Analysis.SplitCotangentCutoffSaturation

/-!
# The actual associated-sphere cutoff symbol homotopy

Public module ID: M0088.

The original finite horizontal and vertical factors are compared with the
full Hermitian product fixed by the supplied global horizontal lift. Exact
cutoff recovery and the metric estimate for the horizontal affine path give
one invertible exterior for the entire interval on each compact chart window.
The vertical factor remains the canonical descended symbol on the original
total covector. All four bundles, prescribed pairings and adjoint maps remain
those of the original construction.
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
-- Normalize the original cutoff factors and their specified horizontal affine path.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in
open scoped Classical in
/-- The original cutoff factors and specified horizontal lift have an invertible affine path. -/
theorem exists_associatedSphereCutoffTensorSymbol_affine_bijective
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C.baseOperator.IsElliptic)
    (ℋ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
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
    let vertical := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose
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
      let lift (z : Z) := split.symm.toContinuousLinearMap.comp (ℋ.lift z)
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
      ∃ ε₀ R₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R₀ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (s : unitInterval),
          ∀ z ∈ K, ∀ ξ η, R₀ ≤ ‖ξ‖ + ‖η‖ →
          let pre := CP.symm z
          let Ξ := covectorFromChart CP pre (split.symm (ξ, η))
          let covH := fun i j ↦ split (covectorInChart (CH i j) pre Ξ)
          let Pε := (∑ i, ∑ j,
            ((J.cutoff j (associatedSphereTrivialization S (C.center i) pre).2 *
              productFrequencyCutoff ε ‖(covH i j).1‖ ‖(covH i j).2‖ : ℝ) : ℂ) •
                (C.piece i).globalSymbolFunction (x z)
                  (covectorFromChart (C.piece i).chart (x z) (covH i j).1)).toLinearMap
          let P₀ := ((∑ i, (C.piece i).globalSymbol).val (x z)
            (Ξ.comp (lift pre))).toLinearMap
          let P := (1 - (s : ℂ)) • P₀ + (s : ℂ) • Pε
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
          let Qε := ∑ i, ∑ j, factor i j
          let Q₀ := vertical pre (Ξ.comp split.symm.toContinuousLinearMap)
          let Q := (1 - (s : ℂ)) • Q₀ + (s : ℂ) • Qε
          let h₀ := hE.toCore (x z)
          let h₁ := kE.toCore (x z)
          let k₀ := associatedEquivariantMetricCore S.toIsPrincipalBundle σ
            h.toContinuousHermitianMetric pre
          let k₁ := associatedEquivariantMetricCore S.toIsPrincipalBundle τ
            k.toContinuousHermitianMetric pre
          ∀ (pi : E' (x z) →ₗ[ℂ] E (x z)) (qi : D' pre →ₗ[ℂ] D pre),
            (∀ u v, h₁.inner (P u) v = h₀.inner u (pi v)) →
            (∀ u v, k₁.inner (Q u) v = k₀.inner u (qi v)) →
            Function.Bijective (reciprocalTensorSymbol P pi Q qi) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
  intro vertical A A' D D'
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) := associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle τ z
  let (z : Z) : Module ℂ (D' z) := associatedEquivariantFiberModule S.toIsPrincipalBundle τ z
  intro hσ hτ J R b c hc θ hθK hθchart hθbase b₀ c₀ hc₀ d₀ hd₀ K hK hKChart
    e₀ f₀ _ _ Ky hKy hKye hKyf hKfiber eB fB _ _ split
  let := linearModelChartedSpace split.symm Z
  intro lift AD AD' CP t L Ci CH base x weight hframe hpartition
  -- First fix the affine horizontal cone, then arrange exact recovery inside it.
  obtain ⟨δH, RH, MH, hδH, hRH, _hMH, hhorizontal⟩ :=
    C.exists_horizontalAffineFullSymbol_conic_metric_inverse_bound S E E' A hC J ℋ
      gB hE kE b₀ c₀ hc₀ d₀ hd₀ eB fB K hK hKChart hframe
  obtain ⟨δR, εH, hδR, hδRle, hεH, hεHone, hrecoverH⟩ :=
    C.exists_horizontalCutoffFullSymbol_eq_in_cone S E E' A J
      b₀ c₀ hc₀ d₀ hd₀ K hK hKChart δH hδH
  -- The vertical inverse cone is refined below horizontal recovery.
  obtain ⟨δ, εV, RV, MV, hδ, hδle, hεV, _hεVone, hRV, _hMV, hvertical⟩ :=
    exists_associatedSphereVerticalCutoffFullSymbol_inverse_bound S σ τ q hq hEll g h k
      hInvariant kInvariant hσ hτ R b c hc θ hθK hθchart hθbase
      b₀ c₀ hc₀ d₀ hd₀ K hK hKChart e₀ f₀ Ky hKy hKye hKyf hKfiber δR hδR hpartition
  obtain ⟨δQ, εQ, _hδQ, hδQle, hεQ, _hεQone, hrecoverQ⟩ :=
    exists_associatedSphereVerticalCutoffFullSymbol_eq_in_cone S σ τ q hq
      hσ hτ R b c hc θ hθK hθchart hθbase
      b₀ c₀ hc₀ d₀ hd₀ K hK hKChart δ hδ hpartition
  let ε₀ := min εH (min εV εQ)
  let R₀ := (1 + δ) * RH + (1 + δ⁻¹) * RV + 1
  have hR₀ : 0 < R₀ := by dsimp only [R₀]; positivity
  refine ⟨ε₀, R₀, lt_min hεH (lt_min hεV hεQ),
    (min_le_left _ _).trans hεHone, hR₀, ?_⟩
  intro ε hε hεle s z hz ξ η hlarge pre Ξ covH Pε P₀ P cov factor Qε Q₀ Q
    h₀ h₁ k₀ k₁ pi qi hpi hqi
  have hεHle : ε ≤ εH := hεle.trans (min_le_left _ _)
  have hεVle : ε ≤ εV := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεQle : ε ≤ εQ := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfactor : Function.Bijective P ∨ Function.Bijective Q := by
    by_cases hcone : ‖η‖ ≤ δ * ‖ξ‖
    · left
      have hξ : RH ≤ ‖ξ‖ := by
        have hpos : 0 ≤ (1 + δ⁻¹) * RV := by positivity
        dsimp only [R₀] at hlarge
        nlinarith
      have hconeR := hcone.trans (mul_le_mul_of_nonneg_right hδle (norm_nonneg ξ))
      have hconeH := hconeR.trans (mul_le_mul_of_nonneg_right hδRle (norm_nonneg ξ))
      have heq := hrecoverH ε hε hεHle z hz ξ η hconeR
      let U := ∑ i, ∑ j,
        (J.cutoff j (associatedSphereTrivialization S (C.center i) pre).2 : ℂ) •
          (C.piece i).globalSymbolFunction (x z)
            (covectorFromChart (C.piece i).chart (x z) (covH i j).1)
      have hPε : Pε = U.toLinearMap := congrArg ContinuousLinearMap.toLinearMap heq
      have hP := (hhorizontal s z hz ξ η hξ hconeH).1
      change Function.Bijective
        ((1 - (s : ℂ)) • ((∑ i, (C.piece i).globalSymbol).val (x z)
          (Ξ.comp (lift pre))) + (s : ℂ) • U) at hP
      change Function.Bijective ((1 - (s : ℂ)) • P₀ + (s : ℂ) • Pε)
      rw [hPε]
      exact hP
    · right
      have hcone' : δ * ‖ξ‖ ≤ ‖η‖ := (lt_of_not_ge hcone).le
      have hη : RV ≤ ‖η‖ := by
        have hξ : ‖ξ‖ ≤ δ⁻¹ * ‖η‖ := (le_inv_mul_iff₀ hδ).mpr hcone'
        have hpos : 0 ≤ (1 + δ) * RH := by positivity
        dsimp only [R₀] at hlarge
        by_contra! hnot
        have h := mul_lt_mul_of_pos_left hnot (show 0 < 1 + δ⁻¹ by positivity)
        nlinarith
      have hQε := (hvertical ε hε hεVle z hz ξ η hcone' hη).1
      change Function.Bijective Qε at hQε
      have heq : Qε = Q₀ := hrecoverQ ε hε hεQle z hz ξ η
        ((mul_le_mul_of_nonneg_right hδQle (norm_nonneg ξ)).trans hcone')
      have hQ : Q = Qε := by
        dsimp only [Q]
        rw [← heq]
        module
      rwa [hQ]
  -- In the actual metric fibers, the original reverse maps give the Hermitian tensor matrix.
  let eb := (eB.continuousLinearEquivAt ℂ (x z) (hframe z hz).1).toLinearEquiv
  let fb := (fB.continuousLinearEquivAt ℂ (x z) (hframe z hz).2).toLinearEquiv
  let : FiniteDimensional ℂ (E (x z)) := .of_injective eb.toLinearMap eb.injective
  let : FiniteDimensional ℂ (E' (x z)) := .of_injective fb.toLinearMap fb.injective
  let ef := AD.frameLinearEquiv (AD.covers pre).choose pre (AD.covers pre).choose_spec
  let ff := AD'.frameLinearEquiv (AD'.covers pre).choose pre (AD'.covers pre).choose_spec
  let : FiniteDimensional ℂ (D pre) := .of_injective ef.toLinearMap ef.injective
  let : FiniteDimensional ℂ (D' pre) := .of_injective ff.toLinearMap ff.injective
  simpa only [Complex.ofReal_one, one_smul] using
    reciprocalTensorSymbol_bijective_of_hermitian_adjoint h₀ h₁ k₀ k₁ P pi Q qi
      hpi hqi 1 1 (hfactor.imp (fun h ↦ ⟨one_ne_zero, h⟩) (fun h ↦ ⟨one_ne_zero, h⟩))

end AtiyahSinger

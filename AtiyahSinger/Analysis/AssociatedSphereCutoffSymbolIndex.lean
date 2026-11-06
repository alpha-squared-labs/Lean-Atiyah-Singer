/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereSupportedClass
public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Analysis.ReciprocalHomogeneousPrincipal

/-!
# The index of the specified native cutoff symbol

Public module ID: M0113.

The original geometric factors and fixed native sum maps identify the principal
class of a supplied PDO. Their tail certificate gives ellipticity, and the
supported-class theorem identifies its component analytic index for positive
parameters below one common threshold.

The proof unpacks the adjoints, full symbol and tail radius from the supplied
certificate, then constructs a homogeneous representative. The threshold precedes
all native sums, measures, presentations, parameters and operators. The
supported K-class equality is derived for those same supplied objects.
-/

@[expose] public noncomputable section

set_option Elab.async false

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
  {F F' : OrthogonalSphere r → Type}
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
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
variable [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

local notation "H" => EuclideanSpace ℝ (Fin (n + r))

variable [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable {a a' : ℕ} [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  (E : B → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable [CompactSpace
  (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "Sphere" => OrthogonalSphere r
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := Sphere)

attribute [local instance] continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent tensorTopology sumTopology
  isFiniteRank_tensor isFiniteRank_sum isFiniteRank_pullback isFiniteRank_associatedEquivariant

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 48000000 in
-- The extended limit accommodates instance synthesis over the common cutoff and symbol context.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates instance synthesis over the common cutoff and symbol context.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open scoped Classical in
/-- Below one uniform positive parameter threshold, each supplied native cutoff PDO
has the analytic index of the original twisted product. -/
theorem associated_sphere_cutoff_symbol_index_call
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hCell : C.baseOperator.IsElliptic)
    (ℋ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (p : homogeneousGlobalSymbolSpace (n := n) (r := a) (q := a') E E' 1)
    (hpi : IsEllipticGlobalSymbol E E' p.val)
    (gB : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (pfull : globalSymbolSpace (n := n) (r := a) (q := a') E E' 1)
    (hCsum : ∑ i, (C.piece i).globalSymbol = pfull)
    (hptail : ∀ x ξ, 1 ≤ gB.length x ξ → pfull.val x ξ = p.val x ξ)
    (q : homogeneousGlobalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hqi : IsEllipticGlobalSymbol F F' q.val)
    (hqe : ∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ σ' γ q.val x ξ = q.val x ξ)
    (g : SmoothCotangentMetric (n := r) (M := Sphere))
    (k : SmoothHermitianMetric (n := r) (r := d) F)
    (k' : SmoothHermitianMetric (n := r) (r := e) F')
    (hk : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
      ∀ (γ : G) (x : Sphere) (s t : F x),
        k.pairing (γ • x) (σ.linearMap γ x s) (σ.linearMap γ x t) = k.pairing x s t)
    (hk' : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
      ∀ (γ : G) (x : Sphere) (s t : F' x),
        k'.pairing (γ • x) (σ'.linearMap γ x s) (σ'.linearMap γ x t) = k'.pairing x s t)
    (hlength : ∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x),
      g.length (γ • x) (γ • (⟨x, ξ⟩ : SphereCot)).snd = g.length x ξ)
    (qfull : globalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hqfixed : ∀ γ : G, equivariantGlobalSymbolLinearMap IG σ σ' γ qfull.val = qfull.val)
    (hqtail : ∀ x ξ, 1 ≤ g.length x ξ → qfull.val x ξ = q.val x ξ)
    (hqfull : IsEllipticFullGlobalSymbol (r := d) (q := e) F F' 1 qfull.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin a)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin a')) E'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := d) F
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := e) F'
    let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
    let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
    ∀ (hA : σ.IsSmoothAtlas IG A) (hA' : σ'.IsSmoothAtlas IG A')
      (JH : AtlasBundlePresentation A) (Rq : AtlasQuantizationPresentation A A')
      (b : ι → B) (c : ι → OpenPartialHomeomorph B En) (_hc : ∀ i, c i ∈ atlas En B)
      (θ : ι → En → ℝ) (_hθK : ∀ i, HasCompactSupport (θ i))
      (_hθchart : ∀ i, tsupport (θ i) ⊆ (c i).target)
      (_hθbase : ∀ i, (c i).symm '' tsupport (θ i) ⊆ (S.trivialization (b i)).baseSet),
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := linearModelChartedSpace split.symm Z
      letI := isManifold_linearModelChartedSpace split.symm Z
      letI := (cotangentLinearModelHomeomorph split.symm Z).symm.t2Space
      letI := (cotangentLinearModelHomeomorph split.symm Z).isOpenEmbedding.locallyCompactSpace
      let πS := associatedBundleProjection (F := Sphere) S.toIsPrincipalBundle
      let Lq := fun j ↦ (Rq.patch j).toPiece (nativeAtlasGlobalSymbol 1 qfull)
      let CP := fun i j ↦ associatedSphereProductChart S (C.center i) (C.piece i).chart (JH.chart j)
      let pfFamily (ε : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
        ∑ i, ∑ j,
          let cov := split (covectorInChart (CP i j) z ξ)
          ((JH.cutoff j (associatedSphereTrivialization S (C.center i) z).2 *
            productFrequencyCutoff ε ‖cov.1‖ ‖cov.2‖ : ℝ) : ℂ) •
              ((C.piece i).globalSymbolFunction (πS z)
                (covectorFromChart (C.piece i).chart (πS z) cov.1)).toLinearMap
      let AD := associatedSphereSmoothBundleAtlas S A σ hA
      let AD' := associatedSphereSmoothBundleAtlas S A' σ' hA'
      let CPv := fun i j ↦ associatedSphereProductChart S (b i) (c i) (Lq j).chart
      let qfFamily (ε : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) : D z →ₗ[ℂ] D' z :=
        ∑ i, ∑ j,
          let y := (associatedSphereTrivialization S (b i) z).2
          let cov := split (covectorInChart (CPv i j) z ξ)
          if hz : z ∈ (CPv i j).source ∩
              (AD.chart (b i, (Lq j).input.frameIndex)).baseSet ∩
              (AD'.chart (b i, (Lq j).output.frameIndex)).baseSet then
            let eIn := (AD.frameLinearEquiv (b i, (Lq j).input.frameIndex) z hz.1.2).trans
              (EuclideanSpace.equiv (Fin (A.rank (Lq j).input.frameIndex)) ℂ).symm.toLinearEquiv
            let eOut := (AD'.frameLinearEquiv (b i, (Lq j).output.frameIndex) z hz.2).trans
              (EuclideanSpace.equiv (Fin (A'.rank (Lq j).output.frameIndex)) ℂ).symm.toLinearEquiv
            ((θ i (c i (πS z)) * (Lq j).input.cutoff ((Lq j).chart y) *
              (Lq j).output.cutoff ((Lq j).chart y) *
              productFrequencyCutoff ε ‖cov.2‖ ‖cov.1‖ : ℝ) : ℂ) •
                (eOut.symm.toLinearMap.comp
                  (((Lq j).symbol ((Lq j).chart y) cov.2).toLinearMap.comp eIn.toLinearMap))
          else (0 : D z →ₗ[ℂ] D' z)
      let c₀ (z : Z) := h.toCore (πS z)
      let c₁ (z : Z) := h'.toCore (πS z)
      let d₀ (z : Z) :=
        associatedEquivariantMetricCore S.toIsPrincipalBundle σ k.toContinuousHermitianMetric z
      let d₁ (z : Z) :=
        associatedEquivariantMetricCore S.toIsPrincipalBundle σ' k'.toContinuousHermitianMetric z
      ∀ (gZ : SmoothCotangentMetric (n := n + r) (M := Z)),
        (∀ z : Z, (∑ i, if z ∈ (associatedSphereTrivialization S (b i)).source ∧
            (associatedSphereTrivialization S (b i) z).1 ∈ (c i).source then
          θ i (c i (associatedSphereTrivialization S (b i) z).1) else 0) = 1) →
      letI : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E)) :=
        pullbackTopology Unit E πS
      letI : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E')) :=
        pullbackTopology Unit E' πS
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D z)) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
      letI : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
      letI : TopologicalSpace (TotalSpace Unit
          (fun z : Z ↦ (E (πS z) ⊗[ℂ] D z) × (E' (πS z) ⊗[ℂ] D' z))) :=
        sumTopology (E := fun z : Z ↦ E (πS z) ⊗[ℂ] D z)
          (F := fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)
      letI : TopologicalSpace (TotalSpace Unit
          (fun z : Z ↦ (E' (πS z) ⊗[ℂ] D z) × (E (πS z) ⊗[ℂ] D' z))) :=
        sumTopology (E := fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)
          (F := fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)
      ∃ εPath : ℝ, 0 < εPath ∧ εPath ≤ 1 ∧
        ∀ (Nplus Nminus : SmoothFiniteComplexBundle (n := n + r) Z),
        letI := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
        ∀ (sumSource : Iso
            (fun z : Z ↦ (E (πS z) ⊗[ℂ] D z) × (E' (πS z) ⊗[ℂ] D' z)) Nplus.Fiber)
          (sumTarget : Iso
            (fun z : Z ↦ (E' (πS z) ⊗[ℂ] D z) × (E (πS z) ⊗[ℂ] D' z)) Nminus.Fiber)
          (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η]
          (_Rfinal : QuantizationPresentation (n := n + r)
            (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber)
          (ε : ℝ) (_hεpos : 0 < ε)
          (K : PseudodifferentialOperator (n := n + r)
            (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber η 1),
          (∃ Rtail : ℝ, 0 < Rtail ∧
            (∀ z ξ (s : ℝ), 0 < s → Rtail ≤ gZ.length z ξ →
              Rtail ≤ gZ.length z (s • ξ) →
                pfFamily ε z (s • ξ) = (s : ℂ) • pfFamily ε z ξ) ∧
            (∀ z ξ (s : ℝ), 0 < s → Rtail ≤ gZ.length z ξ →
              Rtail ≤ gZ.length z (s • ξ) →
                qfFamily ε z (s • ξ) = (s : ℂ) • qfFamily ε z ξ) ∧
            ∀ z ξ, Rtail ≤ gZ.length z ξ →
              ∀ (pi : E' (πS z) →ₗ[ℂ] E (πS z)) (qi : D' z →ₗ[ℂ] D z),
                (∀ u v, (c₁ z).inner (pfFamily ε z ξ u) v = (c₀ z).inner u (pi v)) →
                (∀ u v, (d₁ z).inner (qfFamily ε z ξ u) v = (d₀ z).inner u (qi v)) →
                Function.Bijective
                  (reciprocalTensorSymbol (pfFamily ε z ξ) pi (qfFamily ε z ξ) qi)) →
          (∃ (pi : ∀ z, CotangentFiber (n := n + r) z → E' (πS z) →ₗ[ℂ] E (πS z))
            (qi : ∀ z, CotangentFiber (n := n + r) z → D' z →ₗ[ℂ] D z),
            (∀ z ξ u v, (c₁ z).inner (pfFamily ε z ξ u) v =
              (c₀ z).inner u (pi z ξ v)) ∧
            (∀ z ξ u v, (d₁ z).inner (qfFamily ε z ξ u) v =
              (d₀ z).inner u (qi z ξ v)) ∧
            ∃ qK : globalSymbolSpace (n := n + r)
                (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber 1,
              K.principalSymbol = globalPrincipalSymbolClass Nplus.Fiber Nminus.Fiber 1 qK ∧
              ∀ z ξ (u : E (πS z) ⊗[ℂ] D z) (v : E' (πS z) ⊗[ℂ] D' z),
                qK.val z ξ (sumSource.linearEquiv z (u, v)) =
                  sumTarget.linearEquiv z (reciprocalTensorSymbol
                    (pfFamily ε z ξ) (pi z ξ) (qfFamily ε z ξ) (qi z ξ) (u, v))) →
          K.IsElliptic ∧ (ε ≤ εPath →
            analyticIndexOfComponents η
              (compactSupportKZeroPullback
                ⟨(cotangentLinearModelHomeomorph split.symm Z).symm,
                  (cotangentLinearModelHomeomorph split.symm Z).symm.continuous⟩
                (cotangentLinearModelHomeomorph split.symm Z).symm.isProperMap
                (associatedSphereTwistedProduct S (homogeneousSymbolKClass 1 p hpi)
                  (equivariantHomogeneousSymbolKClass IG σ σ' 1 q hqi hqe))) =
              K.toLinearMap.index) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin a)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin a')) E'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  intro A A' D D'
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
  let (z : Z) : Module ℂ (D' z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
  intro hA hA' JH Rq b c hc θ hθK hθchart hθbase split
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  let := (cotangentLinearModelHomeomorph split.symm Z).symm.t2Space
  let := (cotangentLinearModelHomeomorph split.symm Z).isOpenEmbedding.locallyCompactSpace
  intro πS Lq CP pfFamily AD AD' CPv qfFamily c₀ c₁ d₀ d₁ gZ hpartition
  let : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E)) :=
    pullbackTopology Unit E πS
  let : TopologicalSpace (TotalSpace Unit ((πS : Z → B) *ᵖ E')) :=
    pullbackTopology Unit E' πS
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D z)) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit
      (fun z : Z ↦ (E (πS z) ⊗[ℂ] D z) × (E' (πS z) ⊗[ℂ] D' z))) :=
    sumTopology (E := fun z : Z ↦ E (πS z) ⊗[ℂ] D z)
      (F := fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z)
  let : TopologicalSpace (TotalSpace Unit
      (fun z : Z ↦ (E' (πS z) ⊗[ℂ] D z) × (E (πS z) ⊗[ℂ] D' z))) :=
    sumTopology (E := fun z : Z ↦ E' (πS z) ⊗[ℂ] D z)
      (F := fun z : Z ↦ E (πS z) ⊗[ℂ] D' z)
  -- Select the geometric path threshold once, before all native models and operators.
  have hSupportData := associated_sphere_supported_class_call
    (n := n) (r := r) (d := d) (e := e) (ι := ι)
    S σ σ' E E' C hCell ℋ p hpi gB h h' pfull hCsum hptail
    q hqi hqe g k k' hk hk' hlength qfull hqfixed hqtail hqfull
    hA hA' JH Rq b c hc θ hθK hθchart hθbase gZ hpartition
  refine ⟨hSupportData.choose, hSupportData.choose_spec.1,
    hSupportData.choose_spec.2.1, ?_⟩
  intro Nplus Nminus
  let := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
  intro sumSource sumTarget η hη Rfinal ε hεpos K hTail hFactors
  -- Eliminate the actual symbol certificate of this K, retaining its original two sums.
  obtain ⟨Rtail, hRtail, hpf, hqf, hbij⟩ := hTail
  obtain ⟨pi, qi, hpiAdj, hqiAdj, qK, hKprincipal, hKtensor⟩ := hFactors
  have hKpair (z : Z) (ξ : CotangentFiber (n := n + r) z)
      (w : (E (πS z) ⊗[ℂ] D z) × (E' (πS z) ⊗[ℂ] D' z)) :
      qK.val z ξ (sumSource.linearEquiv z w) =
        sumTarget.linearEquiv z (reciprocalTensorSymbol
          (pfFamily ε z ξ) (pi z ξ) (qfFamily ε z ξ) (qi z ξ) w) :=
    hKtensor z ξ w.1 w.2
  have hbijFixed (z : Z) (ξ : CotangentFiber (n := n + r) z)
      (hξ : Rtail ≤ gZ.length z ξ) :
      Function.Bijective (reciprocalTensorSymbol
        (pfFamily ε z ξ) (pi z ξ) (qfFamily ε z ξ) (qi z ξ)) :=
    hbij z ξ hξ (pi z ξ) (qi z ξ) (hpiAdj z ξ) (hqiAdj z ξ)
  -- Extract one homogeneous representative for both the principal and supported classes.
  obtain ⟨qKh, hqKh, hqKhTail, hqKhPrincipal⟩ :=
    specified_reciprocal_fullSymbol_homogeneous_call
      Nplus Nminus (fun z ↦ E (πS z)) (fun z ↦ E' (πS z)) D D'
      c₀ c₁ d₀ d₁ sumSource.linearEquiv sumTarget.linearEquiv
      (pfFamily ε) pi (qfFamily ε) qi hpiAdj hqiAdj qK hKpair
      gZ Rtail hRtail hpf hqf hbijFixed
  have hprincipal := hKprincipal.trans (hqKhPrincipal Rfinal)
  have hell : K.IsElliptic :=
    (K.isElliptic_iff_homogeneous Rfinal qKh hprincipal).mpr hqKh
  refine ⟨hell, ?_⟩
  intro hεPath
  -- The genuine geometric path compares that same representative to the original product.
  have hclass := hSupportData.choose_spec.2.2 Nplus Nminus sumSource sumTarget
    ε hεpos hεPath pi qi hpiAdj hqiAdj qK qKh hqKh Rtail hRtail hqKhTail hKpair
  have hsymbolIndex := K.analyticIndexOfComponents_symbolKClassOfHomogeneous η
    Rfinal qKh hprincipal hell
  exact (congrArg (analyticIndexOfComponents η) hclass).symm.trans hsymbolIndex

end AtiyahSinger

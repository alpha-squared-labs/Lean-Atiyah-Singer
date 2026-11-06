/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedSphereHermitianSumTransport
public import AtiyahSinger.Analysis.EquivariantFullSymbolSupport
public import AtiyahSinger.Analysis.AssociatedCutoffTensorGlobalHomotopy
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.AssociatedSphereCotangentBoundaryTransport
public import AtiyahSinger.Topology.CotangentModelSupportTransport
public import AtiyahSinger.Topology.GlobalAffineHermitianTensorHomotopy
public import AtiyahSinger.Topology.HermitianMetricPullback
public import AtiyahSinger.Topology.AssociatedSphereTwistedProduct

/-!
# The supported class of the same native cutoff matrix

Public module ID: M0131.

The original homogeneous factors and their specified full tails determine the
initial supported product. For positive parameters below a common threshold,
the complete affine factor path identifies this product in its actual cotangent
model with the class of the supplied native homogeneous cutoff symbol.
Both native bundles and both sum isomorphisms are supplied unchanged.
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
-- Normalize the native cutoff symbol and its original positive-parameter supported class.
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open scoped Classical in
/-- Below a common positive-parameter threshold, a compatible native homogeneous cutoff symbol
has the original associated product class. -/
theorem associated_sphere_supported_class_call
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
          (ε : ℝ) (_hεpos : 0 < ε) (_hεPath : ε ≤ εPath)
          (pi : ∀ z : Z, CotangentFiber (n := n + r) z → E' (πS z) →ₗ[ℂ] E (πS z))
          (qi : ∀ z : Z, CotangentFiber (n := n + r) z → D' z →ₗ[ℂ] D z),
          (∀ z ξ u v, (c₁ z).inner (pfFamily ε z ξ u) v = (c₀ z).inner u (pi z ξ v)) →
          (∀ z ξ u v, (d₁ z).inner (qfFamily ε z ξ u) v = (d₀ z).inner u (qi z ξ v)) →
        ∀ (qK : globalSymbolSpace (n := n + r) (r := Nplus.rank) (q := Nminus.rank)
              Nplus.Fiber Nminus.Fiber 1)
          (qKh : homogeneousGlobalSymbolSpace (n := n + r) (r := Nplus.rank) (q := Nminus.rank)
              Nplus.Fiber Nminus.Fiber 1)
          (hqKh : IsEllipticGlobalSymbol Nplus.Fiber Nminus.Fiber qKh.val)
          (Rtail : ℝ), 0 < Rtail →
          (∀ z ξ, Rtail ≤ gZ.length z ξ → qKh.val z ξ = qK.val z ξ) →
          (∀ z ξ w, qK.val z ξ (sumSource.linearEquiv z w) =
            sumTarget.linearEquiv z (reciprocalTensorSymbol
              (pfFamily ε z ξ) (pi z ξ) (qfFamily ε z ξ) (qi z ξ) w)) →
          homogeneousSymbolKClass 1 qKh hqKh =
            compactSupportKZeroPullback
              ⟨(cotangentLinearModelHomeomorph split.symm Z).symm,
                (cotangentLinearModelHomeomorph split.symm Z).symm.continuous⟩
              (cotangentLinearModelHomeomorph split.symm Z).symm.isProperMap
              (associatedSphereTwistedProduct S (homogeneousSymbolKClass 1 p hpi)
                (equivariantHomogeneousSymbolKClass IG σ σ' 1 q hqi hqe)) := by
  classical
  -- Check the four-block affine algebra abstractly, then apply it to the original fibers once.
  have affineMatrix {V₀ : Type _} {V₁ : Type _} {W₀ : Type _} {W₁ : Type _}
      [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
      [AddCommGroup W₀] [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁]
      (a b : ℂ) (p₀ p₁ : V₀ →ₗ[ℂ] V₁) (pi₀ pi₁ : V₁ →ₗ[ℂ] V₀)
      (q₀ q₁ : W₀ →ₗ[ℂ] W₁) (qi₀ qi₁ : W₁ →ₗ[ℂ] W₀) :
      a • reciprocalTensorSymbol p₀ pi₀ q₀ qi₀ +
          b • reciprocalTensorSymbol p₁ pi₁ q₁ qi₁ =
        reciprocalTensorSymbol (a • p₀ + b • p₁) (a • pi₀ + b • pi₁)
          (a • q₀ + b • q₁) (a • qi₀ + b • qi₁) := by
    apply LinearMap.ext
    intro w
    apply Prod.ext
    all_goals
      simp only [reciprocalTensorSymbol, TensorProduct.map_add_left,
        TensorProduct.map_add_right, TensorProduct.map_smul_left,
        TensorProduct.map_smul_right, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.prod_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Function.prod, LinearMap.coprod_apply, LinearMap.neg_apply]
      simp [smul_add, add_comm, add_left_comm, add_assoc]
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
  let u := homogeneousSymbolKClass 1 p hpi
  let v := equivariantHomogeneousSymbolKClass IG σ σ' 1 q hqi hqe
  have hu : homogeneousSymbolKClass 1 p hpi = u := rfl
  have hv : equivariantHomogeneousSymbolKClass IG σ σ' 1 q hqi hqe = v := rfl
  -- Keep the original class on the base while enlarging only its zero-section control.
  let prB := cotangentProjection (n := n) (M := B)
  let prY := cotangentProjection (n := r) (M := Sphere)
  let := isFiniteRank_pullback (E := E) prB
  let := isFiniteRank_pullback (E := E') prB
  let := isFiniteRank_pullback (E := F) prY
  let := isFiniteRank_pullback (E := F') prY
  let aOriginal := ellipticSymbolTriple p.val p.property.1.continuous hpi
  let KB : Set BaseCot := {z | gB.length z.proj z.snd ≤ 1}
  have hKB : IsCompact KB := gB.isCompact_sublevel 1
  have haKB : aOriginal.control ⊆ KB := by
    intro z hz
    change z.snd = 0 at hz
    change gB.length z.proj z.snd ≤ 1
    rw [hz]
    simp only [SmoothCotangentMetric.length, map_zero, Real.sqrt_zero, zero_le_one]
  let aSupport := aOriginal.enlarge KB hKB haKB
  have haSupportClass : aSupport.compactSupportClass = u :=
    (aOriginal.compactSupportClass_enlarge KB hKB haKB).trans hu
  have haSupportBoundary (z : (aSupport.controlᶜ : Set BaseCot)) :
      (aSupport.boundary.linearEquiv z).toLinearMap =
        (fullSymbolBundleHom pfull).linearMap z.val := by
    apply LinearMap.ext
    intro w
    have htail := hptail z.val.proj z.val.snd (le_of_lt (lt_of_not_ge z.property))
    exact (aOriginal.enlarge_apply KB hKB haKB z w).trans
      ((ellipticSymbolTriple_boundary_apply p.val p.property.1.continuous hpi
        ⟨z.val, fun hz ↦ z.property (haKB hz)⟩ w).trans
          (congrArg (fun L : E z.val.proj →L[ℂ] E' z.val.proj ↦ L w)
            htail.symm))
  -- The sphere packet is literally the original equivariant ofBoundary construction.
  obtain ⟨bSupport, hbSupportControl, hbSupportEquivariant, hbSupportBoundary,
      hbSupportClass⟩ :=
    exists_equivariantFullSymbolSupport_of_tail IG σ σ' 1 q hqi hqe g hlength
      1 (by positivity) qfull hqtail
  let sphereSupport := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((prY : SphereCot → Sphere) *ᵖ F))
    (FiniteBundle.ofFamily ((prY : SphereCot → Sphere) *ᵖ F')) bSupport
    (σ.pullback prY (fun _ _ ↦ rfl)) (σ'.pullback prY (fun _ _ ↦ rfl))
    hbSupportEquivariant
  have hsphereSupportClass : sphereSupport.kZeroClass = v := hbSupportClass.trans hv
  -- These are the exact forward full symbols and adjoints for the original metrics.
  let pSupport := fullSymbolBundleHom pfull
  let piSupport := fullSymbolBundleHom (h.symbolSpaceAdjoint h' pfull)
  let qSupport := fullSymbolBundleHom qfull
  let qiSupport := fullSymbolBundleHom (k.symbolSpaceAdjoint k' qfull)
  let hSupport (z : BaseCot) := h.toCore z.proj
  let hSupport' (z : BaseCot) := h'.toCore z.proj
  let kSupport := k.toContinuousHermitianMetric.pullback prY
  let kSupport' := k'.toContinuousHermitianMetric.pullback prY
  have hkSupport (γ : G) (z : SphereCot) (s t : F z.proj) :
      (kSupport.toCore (γ • z)).inner
        ((σ.pullback prY (fun _ _ ↦ rfl)).linearMap γ z s)
        ((σ.pullback prY (fun _ _ ↦ rfl)).linearMap γ z t) =
          (kSupport.toCore z).inner s t := hk γ z.proj s t
  have hkSupport' (γ : G) (z : SphereCot) (s t : F' z.proj) :
      (kSupport'.toCore (γ • z)).inner
        ((σ'.pullback prY (fun _ _ ↦ rfl)).linearMap γ z s)
        ((σ'.pullback prY (fun _ _ ↦ rfl)).linearMap γ z t) =
          (kSupport'.toCore z).inner s t := hk' γ z.proj s t
  have hpSupport (z : BaseCot) (s : E z.proj) (t : E' z.proj) :
      (hSupport' z).inner (pSupport.linearMap z s) t =
        (hSupport z).inner s (piSupport.linearMap z t) :=
    (h.pairing_symbolAdjoint h' pfull.val z.proj z.snd s t).symm
  have hqSupport (z : SphereCot) (s : F z.proj) (t : F' z.proj) :
      (kSupport'.toCore z).inner (qSupport.linearMap z s) t =
        (kSupport.toCore z).inner s (qiSupport.linearMap z t) :=
    (k.pairing_symbolAdjoint k' qfull.val z.proj z.snd s t).symm
  have hqSupportEquivariant := fullSymbolBundleHom_isEquivariant IG σ σ' qfull hqfixed
  have hqiSupportEquivariant := fullSymbolBundleHom_isEquivariant IG σ' σ
    (k.symbolSpaceAdjoint k' qfull)
    (k.symbolAdjoint_fixed IG σ σ' k' hk hk' qfull.val hqfixed)
  -- Retain the complete affine path, using the same finite charts and original horizontal lift.
  have hGlobalPath := exists_associatedSphereCutoffTensorSymbol_global_affine_bijective
    (n := n) (r := r) (d := d) (e := e) (ι := ι)
    S σ σ' E E' C hCell ℋ gB h h' qfull hqfixed hqfull g k k' hk hk'
    hA hA' JH Rq b c hc
    θ
    hθK
    hθchart
    hθbase
    gZ hpartition
  obtain ⟨εPath, RPath, hεPath, hεPathOne, hRPath, hPathAt⟩ := hGlobalPath
  refine ⟨εPath, hεPath, hεPathOne, ?_⟩
  intro Nplus Nminus
  let := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
  intro sumSource sumTarget ε hεpos hεBound pi qi hpiFamily hqiFamily qK qKh hqKh
    Rtail hRtail hqKhTail hKtensorPair
  let eTensor := sumSource.linearEquiv
  let fTensor := sumTarget.linearEquiv
  -- Select the cotangent comparison maps while retaining the supplied native sums.
  have gradedSupport := exists_associatedSphereCotangentGradedTensorIso
    S E E' F F' ℋ σ σ'
  let aS := gradedSupport.choose
  let aT := gradedSupport.choose_spec.choose
  let originalProj : C(
      TotalSpace ((En × Er) →L[ℝ] ℝ)
        (fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ), Z) :=
    ⟨TotalSpace.proj, FiberBundle.continuous_proj ((En × Er) →L[ℝ] ℝ)
      (fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ)⟩
  -- Use the nested pullback topologies carried by the cotangent comparison maps.
  let σY := σ.pullback prY (fun _ _ ↦ rfl)
  let σY' := σ'.pullback prY (fun _ _ ↦ rfl)
  let DY := AssociatedEquivariantFiber S.toIsPrincipalBundle σY
  let DY' := AssociatedEquivariantFiber S.toIsPrincipalBundle σY'
  let A₀ := (ContinuousMap.fst : C(BaseCot × AssociatedBundle G P SphereCot, BaseCot)) *ᵖ
    (prB *ᵖ E)
  let A₁ := (ContinuousMap.fst : C(BaseCot × AssociatedBundle G P SphereCot, BaseCot)) *ᵖ
    (prB *ᵖ E')
  let B₀ := (ContinuousMap.snd :
    C(BaseCot × AssociatedBundle G P SphereCot, AssociatedBundle G P SphereCot)) *ᵖ DY
  let B₁ := (ContinuousMap.snd :
    C(BaseCot × AssociatedBundle G P SphereCot, AssociatedBundle G P SphereCot)) *ᵖ DY'
  let P₀₀ := fun z ↦ A₀ z ⊗[ℂ] B₀ z
  let P₁₁ := fun z ↦ A₁ z ⊗[ℂ] B₁ z
  let P₁₀ := fun z ↦ A₁ z ⊗[ℂ] B₀ z
  let P₀₁ := fun z ↦ A₀ z ⊗[ℂ] B₁ z
  let : TopologicalSpace (TotalSpace Unit P₀₀) := tensorTopology (E := A₀) (F := B₀)
  let : TopologicalSpace (TotalSpace Unit P₁₁) := tensorTopology (E := A₁) (F := B₁)
  let : TopologicalSpace (TotalSpace Unit P₁₀) := tensorTopology (E := A₁) (F := B₀)
  let : TopologicalSpace (TotalSpace Unit P₀₁) := tensorTopology (E := A₀) (F := B₁)
  let Source := P₀₀ ×ᵇ P₁₁
  let Target := P₁₀ ×ᵇ P₀₁
  let : TopologicalSpace (TotalSpace Unit Source) := sumTopology (E := P₀₀) (F := P₁₁)
  let : TopologicalSpace (TotalSpace Unit Target) := sumTopology (E := P₁₀) (F := P₀₁)
  let j := associatedBundlePullbackProdMap
    («G» := G) («Y» := SphereCot) (projection := projection) prB
  let inverse : C(
      TotalSpace ((En × Er) →L[ℝ] ℝ)
        (fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ),
      AssociatedBundle G (PrincipalBundlePullback prB projection) SphereCot) :=
    ⟨(associatedSphereCotangentHomeomorph S ℋ).symm,
      (associatedSphereCotangentHomeomorph S ℋ).symm.continuous⟩
  let := pullbackTopology Unit Source j
  let := pullbackTopology Unit Target j
  let := pullbackTopology Unit (j *ᵖ Source) inverse
  let := pullbackTopology Unit (j *ᵖ Target) inverse
  let sNative := aS.trans (sumSource.pullback originalProj)
  let tNative := aT.trans (sumTarget.pullback originalProj)
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
  let := isFiniteRank_pullback (E := Nplus.Fiber) originalProj
  let := isFiniteRank_pullback (E := Nminus.Fiber) originalProj
  have htransport := exists_associatedSphereHermitianSumTransport S ℋ
    aSupport sphereSupport hSupport hSupport' kSupport kSupport' hkSupport hkSupport'
    pSupport piSupport qSupport qiSupport hpSupport hqSupport
    hqSupportEquivariant hqiSupportEquivariant haSupportBoundary hbSupportBoundary
  have hspecified :=
    htransport (originalProj *ᵖ Nplus.Fiber) (originalProj *ᵖ Nminus.Fiber) sNative tNative
  let dOriginal := hspecified.choose
  have hdOriginalClass := hspecified.choose_spec.1
  have hdOriginalBoundary := hspecified.choose_spec.2
  have hdOriginalClassUV : dOriginal.compactSupportClass =
      associatedSphereTwistedProduct S u v := by
    exact hdOriginalClass.trans
      (congrArg₂ (fun u v ↦ associatedSphereTwistedProduct S u v)
        haSupportClass hsphereSupportClass)
  -- Transport by the actual inverse covector map, preserving these exact source and target sums.
  have hNativeTransport :=
    exists_cotangentLinearModelSupportTriple split.symm Z Nplus.Fiber Nminus.Fiber dOriginal
  dsimp (config := { zeta := true, zetaHave := true }) only at hNativeTransport
  let dNative := hNativeTransport.choose
  have hdNativeControl := hNativeTransport.choose_spec.1
  have hdNativeClass := hNativeTransport.choose_spec.2.1
  have hdNativeBoundary := hNativeTransport.choose_spec.2.2
  have hdNativeClassUV : dNative.compactSupportClass =
      compactSupportKZeroPullback
        ⟨(cotangentLinearModelHomeomorph split.symm Z).symm,
          (cotangentLinearModelHomeomorph split.symm Z).symm.continuous⟩
        (cotangentLinearModelHomeomorph split.symm Z).symm.isProperMap
        (associatedSphereTwistedProduct S u v) := by
    exact hdNativeClass.trans
      (congrArg (compactSupportKZeroPullback
        ⟨(cotangentLinearModelHomeomorph split.symm Z).symm,
          (cotangentLinearModelHomeomorph split.symm Z).symm.continuous⟩
        (cotangentLinearModelHomeomorph split.symm Z).symm.isProperMap) hdOriginalClassUV)
  let verticalOriginal :=
    (existsUnique_associatedSphereVerticalFullSymbol S σ σ' qfull.val hqfixed).choose
  let verticalReverse :=
    (existsUnique_associatedSphereVerticalFullSymbol S σ' σ
      (k.symbolSpaceAdjoint k' qfull).val
      (k.symbolAdjoint_fixed IG σ σ' k' hk hk' qfull.val hqfixed)).choose
  let pOriginal (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    (pfull.val (πS z) (ξ.comp (split.symm.toContinuousLinearMap.comp (ℋ.lift z)))).toLinearMap
  let piOriginal (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    ((h.symbolSpaceAdjoint h' pfull).val (πS z)
      (ξ.comp (split.symm.toContinuousLinearMap.comp (ℋ.lift z)))).toLinearMap
  let qOriginal (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    verticalOriginal z (ξ.comp split.symm.toContinuousLinearMap)
  let qiOriginal (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    verticalReverse z (ξ.comp split.symm.toContinuousLinearMap)
  -- The original reverse factor is the specified metric adjoint before descending the quotient.
  have hpOriginal (z : Z) (ξ : CotangentFiber (n := n + r) z)
      (s : E (πS z)) (t : E' (πS z)) :
      (c₁ z).inner (pOriginal z ξ s) t = (c₀ z).inner s (piOriginal z ξ t) :=
    (h.pairing_symbolAdjoint h' pfull.val (πS z)
      (ξ.comp (split.symm.toContinuousLinearMap.comp (ℋ.lift z))) s t).symm
  have hqOriginal (z : Z) (ξ : CotangentFiber (n := n + r) z)
      (s : D z) (t : D' z) :
      (d₁ z).inner (qOriginal z ξ s) t = (d₀ z).inner s (qiOriginal z ξ t) := by
    let p₀ := (Quotient.out z).1
    let y := (Quotient.out z).2
    have hz : associatedBundleMk G P Sphere p₀ y = z := Quotient.out_eq z
    obtain ⟨s, rfl⟩ := (associatedEquivariantFiberMk_bijective
      S.toIsPrincipalBundle σ p₀ y hz).2 s
    obtain ⟨t, rfl⟩ := (associatedEquivariantFiberMk_bijective
      S.toIsPrincipalBundle σ' p₀ y hz).2 t
    have hforward :=
      (existsUnique_associatedSphereVerticalFullSymbol S σ σ' qfull.val hqfixed).choose_spec.1
        p₀ y hz (ξ.comp split.symm.toContinuousLinearMap) s
    have hreverse :=
      (existsUnique_associatedSphereVerticalFullSymbol S σ' σ
        (k.symbolSpaceAdjoint k' qfull).val
        (k.symbolAdjoint_fixed IG σ σ' k' hk hk' qfull.val hqfixed)).choose_spec.1
        p₀ y hz (ξ.comp split.symm.toContinuousLinearMap) t
    change (d₁ z).inner (verticalOriginal z _ _) _ =
      (d₀ z).inner _ (verticalReverse z _ _)
    rw [hforward, hreverse]
    exact (associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ'
      k'.toContinuousHermitianMetric hk' p₀ y hz _ t).trans
      (((k.pairing_symbolAdjoint k' qfull.val y
        ((ξ.comp split.symm.toContinuousLinearMap).comp
          (mfderiv (𝓡 r) 𝓘(ℝ, En × Er) (associatedBundleMk G P Sphere p₀) y)) s t).symm).trans
        (associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ
          k.toContinuousHermitianMetric hk p₀ y hz s _).symm)
  -- Only the active product-chart guard changes the first trivialization coordinate.
  let qPathRaw (ε : ℝ) (z : Z)
      (ξ : CotangentFiber (n := n + r) z) : D z →ₗ[ℂ] D' z :=
    ∑ k : ι, ∑ j : Fin Rq.size,
      let y := (associatedSphereTrivialization S (b k) z).2
      let cov := split (covectorInChart (CPv k j) z ξ)
      if hz : z ∈ (CPv k j).source ∩
          (AD.chart (b k, (Lq j).input.frameIndex)).baseSet ∩
          (AD'.chart (b k, (Lq j).output.frameIndex)).baseSet then
        let eIn : D z ≃ₗ[ℂ]
            EuclideanSpace ℂ (Fin (A.rank (Lq j).input.frameIndex)) :=
          (AD.frameLinearEquiv (b k, (Lq j).input.frameIndex) z hz.1.2).trans
            (EuclideanSpace.equiv
              (Fin (A.rank (Lq j).input.frameIndex)) ℂ).symm.toLinearEquiv
        let eOut : D' z ≃ₗ[ℂ]
            EuclideanSpace ℂ (Fin (A'.rank (Lq j).output.frameIndex)) :=
          (AD'.frameLinearEquiv (b k, (Lq j).output.frameIndex) z hz.2).trans
            (EuclideanSpace.equiv
              (Fin (A'.rank (Lq j).output.frameIndex)) ℂ).symm.toLinearEquiv
        ((θ k
          (c k (associatedSphereTrivialization S (b k) z).1) *
          (Lq j).input.cutoff ((Lq j).chart y) *
          (Lq j).output.cutoff ((Lq j).chart y) *
          productFrequencyCutoff ε ‖cov.2‖ ‖cov.1‖ : ℝ) : ℂ) •
          (eOut.symm.toLinearMap.comp
            (((Lq j).symbol ((Lq j).chart y) cov.2).toLinearMap.comp eIn.toLinearMap)
              : D z →ₗ[ℂ] D' z)
      else (0 : D z →ₗ[ℂ] D' z)
  have hqPathRaw (ε : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) :
      qPathRaw ε z ξ = qfFamily ε z ξ := by
    dsimp only [qPathRaw, qfFamily]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hz
    · have hsource : z ∈ (associatedSphereTrivialization S (b i)).source := hz.1.1.1.1
      rw [(associatedSphereTrivialization S (b i)).coe_fst hsource]
    · rfl
  have hPathNative (ε : ℝ) (hεpos : 0 < ε) (hε : ε ≤ εPath) (s : unitInterval)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) (hξ : RPath ≤ gZ.length z ξ)
      (pi : E' (πS z) →ₗ[ℂ] E (πS z)) (qi : D' z →ₗ[ℂ] D z)
      (hp : ∀ u v, (c₁ z).inner
        (((1 - (s : ℂ)) • pOriginal z ξ + (s : ℂ) • pfFamily ε z ξ) u) v =
          (c₀ z).inner u (pi v))
      (hq : ∀ u v, (d₁ z).inner
        (((1 - (s : ℂ)) • qOriginal z ξ + (s : ℂ) • qfFamily ε z ξ) u) v =
          (d₀ z).inner u (qi v)) :
      Function.Bijective (reciprocalTensorSymbol
        ((1 - (s : ℂ)) • pOriginal z ξ + (s : ℂ) • pfFamily ε z ξ) pi
        ((1 - (s : ℂ)) • qOriginal z ξ + (s : ℂ) • qfFamily ε z ξ) qi) := by
    have hraw := hPathAt ε hεpos hε s z ξ hξ
    simp only [hCsum, ContinuousLinearMap.toLinearMap_sum,
      ContinuousLinearMap.toLinearMap_smul] at hraw
    change ∀ pi qi,
      (∀ u v, (c₁ z).inner
        (((1 - (s : ℂ)) • pOriginal z ξ + (s : ℂ) • pfFamily ε z ξ) u) v =
          (c₀ z).inner u (pi v)) →
      (∀ u v, (d₁ z).inner
        (((1 - (s : ℂ)) • qOriginal z ξ + (s : ℂ) • qPathRaw ε z ξ) u) v =
          (d₀ z).inner u (qi v)) →
      Function.Bijective (reciprocalTensorSymbol
        ((1 - (s : ℂ)) • pOriginal z ξ + (s : ℂ) • pfFamily ε z ξ) pi
        ((1 - (s : ℂ)) • qOriginal z ξ + (s : ℂ) • qPathRaw ε z ξ) qi) at hraw
    rw [hqPathRaw] at hraw
    exact hraw pi qi hp hq
  -- Compare the entire original boundary with the native four-block matrix on every vector.
  have hdNativeTensor (z : CotangentTotalSpace (n := n + r) (M := Z))
      (hz : z ∉ dNative.control)
      (w : (E (πS z.proj) ⊗[ℂ] D z.proj) ×
        (E' (πS z.proj) ⊗[ℂ] D' z.proj)) :
      dNative.boundary.linearEquiv ⟨z, hz⟩ (eTensor z.proj w) =
        fTensor z.proj (reciprocalTensorSymbol (pOriginal z.proj z.snd)
          (piOriginal z.proj z.snd) (qOriginal z.proj z.snd) (qiOriginal z.proj z.snd) w) := by
    let back : TotalSpace ((En × Er) →L[ℝ] ℝ)
        (fun x : Z ↦ TangentSpace 𝓘(ℝ, En × Er) x →L[ℝ] ℝ) :=
      ⟨z.proj, z.snd.comp split.symm.toContinuousLinearMap⟩
    have hback : back ∉ dOriginal.control := by
      change z ∉ (fun z ↦ ⟨z.proj, z.snd.comp split.symm.toContinuousLinearMap⟩) ⁻¹'
        dOriginal.control
      rw [← hdNativeControl]
      exact hz
    let inverseSupport := (associatedSphereCotangentHomeomorph S ℋ).symm
    let pairedSupport := associatedBundlePullbackProdMap
      («G» := G) («Y» := SphereCot) (projection := projection) prB
    let coord := pairedSupport (inverseSupport back)
    let σY := σ.pullback prY (fun _ _ ↦ rfl)
    let σY' := σ'.pullback prY (fun _ _ ↦ rfl)
    let qAssoc := associatedEquivariantHom S.toIsPrincipalBundle σY σY'
      qSupport hqSupportEquivariant
    let qiAssoc := associatedEquivariantHom S.toIsPrincipalBundle σY' σY
      qiSupport hqiSupportEquivariant
    let p₀ := (Quotient.out z.proj).1
    let y := (Quotient.out z.proj).2
    have hrep : associatedBundleMk G P Sphere p₀ y = z.proj := Quotient.out_eq z.proj
    let η : SphereCot := ⟨y, back.snd.comp
      (mfderiv (𝓡 r) 𝓘(ℝ, En × Er) (associatedBundleMk G P Sphere p₀) y)⟩
    let hη := (congrArg Prod.snd
      (associatedSphereCotangentHomeomorph_symm_paired_apply S ℋ back p₀ y hrep)).symm
    have hqValue (v : F y) :
        qOriginal z.proj z.snd
            (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p₀ y hrep v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ' p₀ y hrep
            (qSupport.linearMap η v) :=
      (existsUnique_associatedSphereVerticalFullSymbol S σ σ' qfull.val hqfixed).choose_spec.1
        p₀ y hrep back.snd v
    have hqiValue (v : F' y) :
        qiOriginal z.proj z.snd
            (associatedEquivariantFiberMk S.toIsPrincipalBundle σ' p₀ y hrep v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p₀ y hrep
            (qiSupport.linearMap η v) :=
      (existsUnique_associatedSphereVerticalFullSymbol S σ' σ
        (k.symbolSpaceAdjoint k' qfull).val
        (k.symbolAdjoint_fixed IG σ σ' k' hk hk' qfull.val hqfixed)).choose_spec.1
        p₀ y hrep back.snd v
    let L : Source coord →ₗ[ℂ]
        ((E' (πS z.proj) ⊗[ℂ] D z.proj) × (E (πS z.proj) ⊗[ℂ] D' z.proj)) :=
      (aT.linearEquiv back).toLinearMap.comp
      (reciprocalTensorSymbol (pSupport.linearMap coord.1) (piSupport.linearMap coord.1)
        (qAssoc.linearMap coord.2) (qiAssoc.linearMap coord.2))
    let R : Source coord →ₗ[ℂ]
        ((E' (πS z.proj) ⊗[ℂ] D z.proj) × (E (πS z.proj) ⊗[ℂ] D' z.proj)) :=
      (reciprocalTensorSymbol (pOriginal z.proj z.snd) (piOriginal z.proj z.snd)
        (qOriginal z.proj z.snd) (qiOriginal z.proj z.snd)).comp
          (aS.linearEquiv back).toLinearMap
    have hpair (u₀ : E (prB coord.1)) (u₁ : E' (prB coord.1))
        (v₀ : F y) (v₁ : F' y) :
        L (u₀ ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY p₀ η hη v₀,
          u₁ ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY' p₀ η hη v₁) =
        R (u₀ ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY p₀ η hη v₀,
          u₁ ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY' p₀ η hη v₁) := by
      have h := gradedSupport.choose_spec.choose_spec.2.2 pSupport piSupport qSupport qiSupport
        hqSupportEquivariant hqiSupportEquivariant back p₀ y hrep u₀ u₁ v₀ v₁
      have hr := congrArg (reciprocalTensorSymbol (pOriginal z.proj z.snd)
        (piOriginal z.proj z.snd) (qOriginal z.proj z.snd) (qiOriginal z.proj z.snd)) h.1
      simp only [reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod,
        LinearMap.coprod_apply, LinearMap.neg_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, hqValue, hqiValue] at hr
      exact h.2.trans hr.symm
    have hLR : L = R := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          apply LinearMap.prod_ext
          · apply TensorProduct.ext'
            intro u v
            obtain ⟨v₀, rfl⟩ :=
              (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σY p₀ η hη).2 v
            have h := hpair u 0 v₀ 0
            simp only [TensorProduct.zero_tmul] at h
            exact h
          · apply TensorProduct.ext'
            intro u v
            obtain ⟨v₁, rfl⟩ :=
              (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σY' p₀ η hη).2 v
            have h := hpair 0 u 0 v₁
            simp only [TensorProduct.zero_tmul] at h
            exact h
    -- Use surjectivity of the same selected source comparison, then the original model boundary.
    obtain ⟨w₀, hw₀⟩ := (aS.linearEquiv back).surjective w
    have hmatrix := LinearMap.congr_fun hLR w₀
    change aT.linearEquiv back
      (reciprocalTensorSymbol (pSupport.linearMap coord.1) (piSupport.linearMap coord.1)
        (qAssoc.linearMap coord.2) (qiAssoc.linearMap coord.2) w₀) =
      reciprocalTensorSymbol (pOriginal z.proj z.snd) (piOriginal z.proj z.snd)
        (qOriginal z.proj z.snd) (qiOriginal z.proj z.snd) (aS.linearEquiv back w₀) at hmatrix
    rw [hw₀] at hmatrix
    have hboundary := hdOriginalBoundary ⟨back, hback⟩ w₀
    change dOriginal.boundary.linearEquiv ⟨back, hback⟩
      (eTensor z.proj (aS.linearEquiv back w₀)) =
      fTensor z.proj (aT.linearEquiv back
        (reciprocalTensorSymbol (pSupport.linearMap coord.1) (piSupport.linearMap coord.1)
          (qAssoc.linearMap coord.2) (qiAssoc.linearMap coord.2) w₀)) at hboundary
    rw [hw₀, hmatrix] at hboundary
    exact (hdNativeBoundary z hback hz (eTensor z.proj w)).trans hboundary
  let symbolSupport := ellipticSymbolTriple qKh.val
    qKh.property.1.continuous hqKh
  let radius : ℝ := max RPath Rtail
  let control : Set (CotangentTotalSpace (n := n + r) (M := Z)) :=
    dNative.control ∪ symbolSupport.control ∪ {z | gZ.length z.proj z.snd ≤ radius}
  have hcontrol : IsCompact control :=
    (dNative.isCompact_control.union symbolSupport.isCompact_control).union
      (gZ.isCompact_sublevel radius)
  have hdControl : dNative.control ⊆ control :=
    Set.subset_union_left.trans Set.subset_union_left
  have hsControl : symbolSupport.control ⊆ control :=
    Set.subset_union_right.trans Set.subset_union_left
  have hradius (z : (controlᶜ : Set (CotangentTotalSpace (n := n + r) (M := Z)))) :
      radius ≤ gZ.length z.val.proj z.val.snd :=
    le_of_lt (lt_of_not_ge (fun h ↦ z.property (Or.inr h)))
  have hNative (z : (controlᶜ : Set (CotangentTotalSpace (n := n + r) (M := Z)))) w :
      (dNative.enlarge control hcontrol hdControl).boundary.linearEquiv z
          (eTensor z.val.proj w) =
        fTensor z.val.proj (reciprocalTensorSymbol (pOriginal z.val.proj z.val.snd)
          (piOriginal z.val.proj z.val.snd) (qOriginal z.val.proj z.val.snd)
          (qiOriginal z.val.proj z.val.snd) w) :=
    (dNative.enlarge_apply control hcontrol hdControl z _).trans
      (hdNativeTensor z.val (fun h ↦ z.property (hdControl h)) w)
  have hSymbol (z : (controlᶜ : Set (CotangentTotalSpace (n := n + r) (M := Z)))) w :
      (symbolSupport.enlarge control hcontrol hsControl).boundary.linearEquiv z
          (eTensor z.val.proj w) =
        fTensor z.val.proj (reciprocalTensorSymbol (pfFamily ε z.val.proj z.val.snd)
          (pi z.val.proj z.val.snd) (qfFamily ε z.val.proj z.val.snd)
          (qi z.val.proj z.val.snd) w) := by
    have htail := hqKhTail z.val.proj z.val.snd
      ((le_max_right _ _).trans (hradius z))
    exact (symbolSupport.enlarge_apply control hcontrol hsControl z _).trans
      ((ellipticSymbolTriple_boundary_apply qKh.val
        qKh.property.1.continuous hqKh
        ⟨z.val, fun h ↦ z.property (hsControl h)⟩ _).trans
        ((congrArg (fun L ↦ L (eTensor z.val.proj w)) htail).trans
          (hKtensorPair z.val.proj z.val.snd w)))
  -- Use the affine cylinder of the actual endpoint boundaries; no intermediate PDO is required.
  have hhomotopy : dNative.Homotopic symbolSupport := by
    apply dNative.homotopic_of_affine symbolSupport control hcontrol hdControl hsControl
    intro s z
    let P₀ := pOriginal z.val.proj z.val.snd
    let PI₀ := piOriginal z.val.proj z.val.snd
    let Q₀ := qOriginal z.val.proj z.val.snd
    let QI₀ := qiOriginal z.val.proj z.val.snd
    let P₁ := pfFamily ε z.val.proj z.val.snd
    let PI₁ := pi z.val.proj z.val.snd
    let Q₁ := qfFamily ε z.val.proj z.val.snd
    let QI₁ := qi z.val.proj z.val.snd
    let P := (1 - (s : ℂ)) • P₀ + (s : ℂ) • P₁
    let PI := (1 - (s : ℂ)) • PI₀ + (s : ℂ) • PI₁
    let Q := (1 - (s : ℂ)) • Q₀ + (s : ℂ) • Q₁
    let QI := (1 - (s : ℂ)) • QI₀ + (s : ℂ) • QI₁
    have hp (u : E (πS z.val.proj)) (v : E' (πS z.val.proj)) :
        (c₁ z.val.proj).inner (P u) v = (c₀ z.val.proj).inner u (PI v) := by
      simp only [P, PI, P₀, PI₀, P₁, PI₁, LinearMap.add_apply, LinearMap.smul_apply,
        (c₁ z.val.proj).add_left, (c₁ z.val.proj).smul_left,
        InnerProductSpace.Core.inner_add_right (c := (c₀ z.val.proj).toCore),
        InnerProductSpace.Core.inner_smul_right (c := (c₀ z.val.proj).toCore),
        map_sub, map_one, Complex.conj_ofReal, hpOriginal, hpiFamily]
    have hq (u : D z.val.proj) (v : D' z.val.proj) :
        (d₁ z.val.proj).inner (Q u) v = (d₀ z.val.proj).inner u (QI v) := by
      simp only [Q, QI, Q₀, QI₀, Q₁, QI₁, LinearMap.add_apply, LinearMap.smul_apply,
        (d₁ z.val.proj).add_left, (d₁ z.val.proj).smul_left,
        InnerProductSpace.Core.inner_add_right (c := (d₀ z.val.proj).toCore),
        InnerProductSpace.Core.inner_smul_right (c := (d₀ z.val.proj).toCore),
        map_sub, map_one, Complex.conj_ofReal, hqOriginal, hqiFamily]
    let matrix := reciprocalTensorSymbol P PI Q QI
    have hmatrix :
        (1 - (s : ℂ)) • reciprocalTensorSymbol P₀ PI₀ Q₀ QI₀ +
          (s : ℂ) • reciprocalTensorSymbol P₁ PI₁ Q₁ QI₁ = matrix := by
      dsimp only [matrix, P, PI, Q, QI]
      exact affineMatrix (1 - (s : ℂ)) (s : ℂ) P₀ P₁ PI₀ PI₁ Q₀ Q₁ QI₀ QI₁
    have hboundary :
        (1 - (s : ℂ)) •
            ((dNative.enlarge control hcontrol hdControl).boundary.linearEquiv z).toLinearMap +
          (s : ℂ) •
            ((symbolSupport.enlarge control hcontrol hsControl).boundary.linearEquiv z).toLinearMap
              =
          (fTensor z.val.proj).toLinearMap.comp
            (matrix.comp (eTensor z.val.proj).symm.toLinearMap) := by
      apply LinearMap.ext
      intro w
      obtain ⟨w, rfl⟩ := (eTensor z.val.proj).surjective w
      change (1 - (s : ℂ)) •
          (dNative.enlarge control hcontrol hdControl).boundary.linearEquiv z
            (eTensor z.val.proj w) +
        (s : ℂ) • (symbolSupport.enlarge control hcontrol hsControl).boundary.linearEquiv z
            (eTensor z.val.proj w) =
          fTensor z.val.proj (matrix ((eTensor z.val.proj).symm (eTensor z.val.proj w)))
      rw [(eTensor z.val.proj).symm_apply_apply, hNative, hSymbol]
      have hmatrixApply :=
        congrArg (fTensor z.val.proj) (LinearMap.congr_fun hmatrix w)
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul] at hmatrixApply
      exact hmatrixApply
    rw [hboundary]
    exact (fTensor z.val.proj).bijective.comp
      ((hPathNative ε hεpos hεBound s z.val.proj z.val.snd
        ((le_max_left _ _).trans (hradius z)) PI QI hp hq).comp
          (eTensor z.val.proj).symm.bijective)
  exact (dNative.compactSupportClass_eq_of_homotopic symbolSupport hhomotopy).symm.trans
    hdNativeClassUV

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.TrivialRepresentationRing
public import AtiyahSinger.Analysis.AssociatedCutoffFactorsHomogeneous
public import AtiyahSinger.Analysis.AssociatedExactAdjointLocalization
public import AtiyahSinger.Analysis.AssociatedJointReverseBound
public import AtiyahSinger.Analysis.AssociatedSphereCommonBasePartition
public import AtiyahSinger.Analysis.AssociatedSphereIndexAssembly
public import AtiyahSinger.Analysis.AssociatedSphereSupportedClass
public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalDualApproximation
public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalRegularization
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalDualApproximation
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalFamilyRegularization
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalSymbolFactor
public import AtiyahSinger.Analysis.AssociatedTensorResidualSmoothing
public import AtiyahSinger.Analysis.AssociatedTensorVerticalSobolevExtension
public import AtiyahSinger.Analysis.AssociatedTensorVerticalSymbolFactor
public import AtiyahSinger.Analysis.AtlasFullSymbolEllipticity
public import AtiyahSinger.Analysis.AtlasGradedCompactApproximationIndex
public import AtiyahSinger.Analysis.AtlasMetricL2Equivalence
public import AtiyahSinger.Analysis.AtlasNativePairedLimit
public import AtiyahSinger.Analysis.AtlasNativePrincipalConjugate
public import AtiyahSinger.Analysis.AtlasNativeSumSobolev
public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantSmoothIndexOrder
public import AtiyahSinger.Analysis.FiniteRegularizationNormBounds
public import AtiyahSinger.Analysis.FullModelAnalyticIndex
public import AtiyahSinger.Analysis.FullModelIndexProduct
public import AtiyahSinger.Analysis.GradedBlockAlgebra
public import AtiyahSinger.Analysis.GradedBlockLimit
public import AtiyahSinger.Analysis.GradedBlockRealization
public import AtiyahSinger.Analysis.HermitianMetricAdjointIndex
public import AtiyahSinger.Analysis.InvariantFullSymbolRegularization
public import AtiyahSinger.Analysis.LinearModelAnalyticIndex
public import AtiyahSinger.Analysis.NativeAtlasFullEllipticity
public import AtiyahSinger.Analysis.NativeEllipticRepresentatives
public import AtiyahSinger.Analysis.NativeGradedTensorFamily
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Analysis.PrincipalLocalizationQuantization
public import AtiyahSinger.Analysis.ReciprocalHomogeneousPrincipal
public import AtiyahSinger.Analysis.SobolevCoordinateIndex
public import AtiyahSinger.Geometry.AssociatedSphereDiscreteCotangent
public import AtiyahSinger.Geometry.AssociatedSphereDiscreteProduct
public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import AtiyahSinger.Geometry.ZeroSphereCotangentProduct
public import AtiyahSinger.Topology.AssociatedGaugeCoefficient
public import AtiyahSinger.Topology.AssociatedGaugeTwistedProduct
public import AtiyahSinger.Topology.AssociatedInvariantMetric
public import AtiyahSinger.Topology.AssociatedSphereTwistedProduct
public import AtiyahSinger.Topology.AssociatedTrivialTwistedProduct
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Index maps, positive representatives, and zero-dimensional sphere-bundle cases

Public module ID: M0120.

P05: the intrinsic associated-sphere analytic index and orthogonal-sphere
equivariant index are defined on their actual cotangent models. Positive
classes admit smooth elliptic representatives, invariant full symbols and
compatible equivariant quantizations. The twisted-product index identity is
proved here when either the base or sphere dimension is zero; the case with
both dimensions positive is proved in the associated-sphere comparison modules.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

section OrthogonalIndex

open scoped Matrix.Norms.L2Operator

/-- The equivariant index for the orthogonal action on the sphere cotangent bundle. -/
def orthogonalSphereAnalyticIndex (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) →+
      RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ) := by
  letI := orthogonalGroupChartedSpace r
  letI := lieGroup_orthogonalGroup r
  letI := compactSpace_orthogonalGroup r
  letI : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin r) ℝ)
  letI : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
  letI : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
  -- The base transformations agree before their inverse differentials are taken.
  have hLift : smoothCotangentMulAction (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r) = orthogonalSphereCotangentMulAction r := by
    apply MulAction.ext
    funext A z
    have he : Diffeomorph.smul (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r) (𝓡 r) ∞ A = orthogonalSphereDiffeomorph r A := by
      apply Diffeomorph.ext
      intro x
      rfl
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) he
  -- Transport only the dependent action parameter, never the original quotient presentation.
  have transport
      (a b : MulAction (Matrix.orthogonalGroup (Fin r) ℝ)
        (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))
      (ha : letI := a
        letI := a.toSMul
        ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
          (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))
      (hb : letI := b
        letI := b.toSMul
        ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
          (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))
      (hab : a = b) :
      (letI := a
       letI := a.toSMul
       letI := ha
       EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
           (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) →+
         RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) →
      (letI := b
       letI := b.toSMul
       letI := hb
       EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
           (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) →+
         RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) := by
    cases hab
    exact id
  letI := smoothCotangentMulAction (n := r)
    (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
    𝓘(ℝ, OrthogonalGroupModel r)
  letI := contMDiffSMul_smoothCotangent (n := r)
    (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
    𝓘(ℝ, OrthogonalGroupModel r)
  letI : ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel r))
      (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
  exact transport
    (smoothCotangentMulAction (n := r) (G := Matrix.orthogonalGroup (Fin r) ℝ)
      (M := OrthogonalSphere r) 𝓘(ℝ, OrthogonalGroupModel r))
    (orthogonalSphereCotangentMulAction r)
    (ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel r))
      (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞)
    (continuousSMul_orthogonalSphereCotangent r) hLift
    (equivariantAnalyticIndexMap (VG := OrthogonalGroupModel r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (n := r) (M := OrthogonalSphere r))

end OrthogonalIndex

open scoped Matrix.Norms.Elementwise

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "OG" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle OG P (OrthogonalSphere r)
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "C" => fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ

/-- The intrinsic analytic index on the associated sphere cotangent bundle. -/
def associatedSphereAnalyticIndex :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := associatedBundle_t2Space (Y := SphereCot)
      (isPrincipalBundle_pullback (G := OG) (projection := projection)
        (cotangentProjection (n := n) (M := B)))
    letI := associatedBundle_locallyCompactSpace (Y := SphereCot)
      (isPrincipalBundle_pullback (G := OG) (projection := projection)
        (cotangentProjection (n := n) (M := B)))
    let e := associatedSphereCotangentHomeomorph S (associatedSphereHorizontalLift S)
    letI := e.t2Space
    letI := e.symm.isOpenEmbedding.locallyCompactSpace
    CompactSupportKZero (TotalSpace ((En × Er) →L[ℝ] ℝ) C) →+ ℤ := by
  letI := S.toIsPrincipalBundle
  letI := associatedSphereChartedSpace S
  letI := associatedSphereIsManifold S
  -- Compactness is proved for the original quotient, not supplied as an extra assumption.
  have hcontrol : associatedControl OG P (OrthogonalSphere r) Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | h v =>
      exact ⟨v, ⟨Set.mem_univ v.1, Set.mem_univ v.2⟩, rfl⟩
  letI : CompactSpace Z := ⟨by
    rw [← hcontrol]
    exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
      (fun _ _ ↦ Iff.rfl)⟩
  letI := associatedBundle_t2Space (Y := OrthogonalSphere r) S.toIsPrincipalBundle
  letI : MeasurableSpace Z := borel Z
  letI : BorelSpace Z := ⟨rfl⟩
  -- The explicit coordinate map preserves the native product norm and bundle topology.
  exact analyticIndexLinearModel
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z


end AtiyahSinger


set_option Elab.async false

section PositiveInputs

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent
  orthogonalGroupChartedSpace lieGroup_orthogonalGroup compactSpace_orthogonalGroup

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "Sphere" => OrthogonalSphere r
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := Sphere)

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the original full-symbol inputs and separate zero-dimensional
-- endpoints.
/-- Select actual full-symbol and equivariant operator inputs for the original positive classes. -/
theorem exists_associatedSphere_positiveIndexInputs (hn : 0 < n) (hr : 0 < r)
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero G SphereCot) :
    ∃ E E' : SmoothFiniteComplexBundle (n := n) B,
      ∃ p : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := E'.rank)
        E.Fiber E'.Fiber 1,
      ∃ hpi : IsEllipticGlobalSymbol E.Fiber E'.Fiber p.val,
        homogeneousSymbolKClass 1 p hpi = u ∧
      ∃ (gB : SmoothCotangentMetric (n := n) (M := B))
        (_h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
        (_h' : SmoothHermitianMetric (n := n) (r := E'.rank) E'.Fiber)
        (pfull : globalSymbolSpace (n := n) (r := E.rank) (q := E'.rank) E.Fiber E'.Fiber 1)
        (Rp : QuantizationPresentation (n := n) (r := E.rank) (q := E'.rank) E.Fiber E'.Fiber)
        (C : PrincipalPseudodifferentialLocalization (a := E.rank) (a' := E'.rank)
          S E.Fiber E'.Fiber μ 1),
        (∀ x ξ, 1 ≤ gB.length x ξ → pfull.val x ξ = p.val x ξ) ∧
        IsEllipticFullGlobalSymbol (r := E.rank) (q := E'.rank) E.Fiber E'.Fiber 1 pfull.val ∧
        (∑ j, (C.piece j).globalSymbol) = pfull ∧
        C.baseOperator.principalSymbol = globalPrincipalSymbolClass E.Fiber E'.Fiber 1 pfull ∧
        C.baseOperator.IsElliptic ∧
        (letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
         letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
         let A₀ := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
         let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := E'.rank) E'.Fiber
         let props := nativeAtlasSymbolFunction_homogeneous_properties 1 p.val
           p.property.1 p.property.2 hpi
         C.baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
           atlasGlobalPrincipalSymbolClass A₀ A₁ 1
             (atlasRegularizedSymbol A₀ A₁ gB 1 (nativeAtlasSymbolFunction p.val)
               props.1 props.2.1)) ∧
        ∃ (index : Fin C.size → Fin Rp.size)
          (χ ρ : Fin C.size → EuclideanSpace ℝ (Fin n) → ℝ)
          (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)),
          (∀ j, C.piece j = ((Rp.patch (index j)).toPiece pfull).coordinateCutoff
            (χ j) (ρ j) (hχ j) (hρ j)) ∧
        ∃ F F' : SmoothFiniteComplexBundle (n := r) Sphere,
          letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
          ∃ (σ : EquivariantStructure G F.Fiber) (σ' : EquivariantStructure G F'.Fiber)
            (hσ : σ.IsSmooth (n := r) (r := F.rank) IG)
            (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) IG)
            (q : homogeneousGlobalSymbolSpace (n := r) (r := F.rank) (q := F'.rank)
              F.Fiber F'.Fiber 1)
            (hqi : IsEllipticGlobalSymbol F.Fiber F'.Fiber q.val)
            (hqe : ∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x), ξ ≠ 0 →
              equivariantGlobalSymbolLinearMap IG σ σ' γ q.val x ξ = q.val x ξ),
            equivariantHomogeneousSymbolKClass IG σ σ' 1 q hqi hqe = v ∧
          ∃ (g : SmoothCotangentMetric (n := r) (M := Sphere))
            (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
            (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber),
            (∀ (γ : G) (x : Sphere) (s t : F.Fiber x),
              k.pairing (γ • x) (σ.linearMap γ x s) (σ.linearMap γ x t) = k.pairing x s t) ∧
            (∀ (γ : G) (x : Sphere) (s t : F'.Fiber x),
              k'.pairing (γ • x) (σ'.linearMap γ x s) (σ'.linearMap γ x t) = k'.pairing x s t) ∧
            (∀ (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x),
              g.length (γ • x) (γ • (⟨x, ξ⟩ : SphereCot)).snd = g.length x ξ) ∧
          ∃ qfull : globalSymbolSpace (n := r) (r := F.rank) (q := F'.rank) F.Fiber F'.Fiber 1,
            (∀ γ : G, equivariantGlobalSymbolLinearMap IG σ σ' γ qfull.val = qfull.val) ∧
            (∀ x ξ, 1 ≤ g.length x ξ → qfull.val x ξ = q.val x ξ) ∧
            IsEllipticFullGlobalSymbol (r := F.rank) (q := F'.rank) F.Fiber F'.Fiber 1 qfull.val ∧
          ∃ (Rq : QuantizationPresentation (n := r) (r := F.rank) (q := F'.rank) F.Fiber F'.Fiber)
            (ν : Measure Sphere) (hν : IsSmoothPositiveMeasure (n := r) ν),
            letI := hν
            ∃ (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
                F.Fiber F'.Fiber ν 1)
              (hQ : Q.IsEquivariant IG σ σ' hσ hσ') (hQell : Q.IsElliptic),
              (∀ γ : G, Measure.map (fun y : Sphere ↦ γ • y) ν = ν) ∧
              Q.principalSymbol = globalPrincipalSymbolClass F.Fiber F'.Fiber 1 qfull ∧
              Q.principalSymbol = globalPrincipalSymbolClass F.Fiber F'.Fiber 1
                (Rq.regularizedSymbol 1 q.val q.property.1 q.property.2) ∧
              Q.smoothEquivariantAnalyticIndex IG σ σ' hσ hσ' hQ hQell =
                orthogonalSphereAnalyticIndex r v := by
  classical
  -- Positive dimension stabilizes each original class by one common complement.
  obtain ⟨E, E', p, hpi, hu⟩ := exists_smooth_elliptic_representative_of_pos hn u 1
  refine ⟨E, E', p, hpi, hu, ?_⟩
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let A₀ := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
  let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := E'.rank) E'.Fiber
  obtain ⟨gB⟩ := SmoothCotangentMetric.nonempty (n := n) (M := B)
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := E.rank) E.Fiber
  obtain ⟨h'⟩ := nonempty_smoothHermitianMetric (n := n) (r := E'.rank) E'.Fiber
  let props := nativeAtlasSymbolFunction_homogeneous_properties 1 p.val
    p.property.1 p.property.2 hpi
  let pA := atlasRegularizedSymbol A₀ A₁ gB 1 (nativeAtlasSymbolFunction p.val)
    props.1 props.2.1
  let pf : GlobalSymbolFunction (n := n) E.Fiber E'.Fiber := fun x ξ ↦
    (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (gB.length x ξ)) : ℂ) • p.val x ξ
  let pfull : globalSymbolSpace (n := n) (r := E.rank) (q := E'.rank) E.Fiber E'.Fiber 1 :=
    ⟨pf, (isAtlasGlobalSymbol_native_iff 1 pf).mp pA.property⟩
  have hpfull : IsEllipticFullGlobalSymbol (r := E.rank) (q := E'.rank)
      E.Fiber E'.Fiber 1 pfull.val :=
    (isEllipticFullAtlasSymbol_native_iff 1 pf).mp
      ((isEllipticFullAtlasSymbol_atlasRegularizedSymbol_iff A₀ A₁ gB 1
        (nativeAtlasSymbolFunction p.val) props.1 props.2.1).mpr props.2.2)
  have hptail (x : B) (ξ : CotangentFiber (n := n) x) (hξ : 1 ≤ gB.length x ξ) :
      pfull.val x ξ = p.val x ξ := by
    ext s
    exact LinearMap.congr_fun
      ((atlasRegularizedSymbolFunction_cutoff gB (nativeAtlasSymbolFunction p.val)).2 x ξ hξ) s
  obtain ⟨Rp⟩ := nonempty_quantizationPresentation (n := n)
    (r := E.rank) (q := E'.rank) (E := E.Fiber) (F := E'.Fiber)
  -- Refine this very quantization, retaining the full-symbol sum and each original source piece.
  obtain ⟨C, hsum, hprincipal, index, χ, ρ, hχ, hρ, hpieces⟩ :=
    Rp.exists_principalLocalization_of_fullSymbol S E.Fiber E'.Fiber μ pfull
  have hCell : C.baseOperator.IsElliptic := ⟨pfull, hprincipal, hpfull⟩
  have hCA : C.baseOperator.toAtlasPseudodifferentialOperator.principalSymbol =
      atlasGlobalPrincipalSymbolClass A₀ A₁ 1 pA :=
    C.baseOperator.principalSymbol_toAtlasPseudodifferentialOperator pfull hprincipal
  refine ⟨gB, h, h', pfull, Rp, C, hptail, hpfull, hsum, hprincipal, hCell, hCA,
    index, χ, ρ, hχ, hρ, hpieces, ?_⟩
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  obtain ⟨F, F', σ, σ', hσ, hσ', q, hqi, hqe, hv⟩ :=
    exists_equivariant_smooth_elliptic_representative_of_pos
      (VG := OrthogonalGroupModel r) («G» := G) (M := Sphere) hr 1 v
  refine ⟨F, F', σ, σ', hσ, hσ', q, hqi, hqe, hv, ?_⟩
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  obtain ⟨g, hg⟩ := exists_invariant_smoothCotangentMetric («G» := G) (n := r) (M := Sphere) IG
  obtain ⟨k, hk⟩ := exists_invariant_smoothHermitianMetric IG σ hσ
  obtain ⟨k', hk'⟩ := exists_invariant_smoothHermitianMetric IG σ' hσ'
  have hlength (γ : G) (x : Sphere) (ξ : CotangentFiber (n := r) x) :
      g.length (γ • x) (γ • (⟨x, ξ⟩ : SphereCot)).snd = g.length x ξ :=
    congrArg Real.sqrt (hg γ x ξ ξ)
  refine ⟨g, k, k', hk, hk', hlength, ?_⟩
  -- The invariant radial field keeps this same homogeneous tail, including its actual action.
  obtain ⟨qfull, _hqformula, hqfixed, hqtail, hqfull, hqclass⟩ :=
    exists_invariant_fullSymbol_regularization IG σ σ' 1 q hqi hqe g hlength
  refine ⟨qfull, hqfixed, hqtail, hqfull, ?_⟩
  obtain ⟨Rq⟩ := nonempty_quantizationPresentation (n := r)
    (r := F.rank) (q := F'.rank) (E := F.Fiber) (F := F'.Fiber)
  obtain ⟨ν, hν, hνinv⟩ := exists_invariant_smoothPositiveMeasure G IG (n := r) (M := Sphere)
  let := hν
  have hfixed (γ : G) : equivariantPrincipalSymbolRepresentation IG σ σ' hσ hσ' 1 γ
      (globalPrincipalSymbolClass F.Fiber F'.Fiber 1 qfull) =
        globalPrincipalSymbolClass F.Fiber F'.Fiber 1 qfull := by
    rw [equivariantPrincipalSymbolRepresentation_class]
    congr 1
    apply Subtype.ext
    exact hqfixed γ
  obtain ⟨Q, hQ, hQpr⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := ν) IG σ σ' hσ hσ' 1 (globalPrincipalSymbolClass F.Fiber F'.Fiber 1 qfull) hfixed
  have hQell : Q.IsElliptic := ⟨qfull, hQpr, hqfull⟩
  have hQreg := hQpr.trans (hqclass Rq)
  refine ⟨Rq, ν, hν, Q, hQ, hQell, hνinv, hQpr, hQreg, ?_⟩
  -- The full original orthogonal representation index is computed by this same Q.
  have hindex := equivariantAnalyticIndexMap_eq_smooth_of_homogeneous
    σ σ' hσ hσ' ν Q hQ Rq q hQreg hqi hqe
  have hmap : orthogonalSphereAnalyticIndex r = equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel r) («G» := G) (n := r) (M := Sphere) := by
    simp only [orthogonalSphereAnalyticIndex, id_eq]
    congr 1
    · exact (BorelSpace.measurable_eq (α := Sphere)).symm
    · exact proof_irrel_heq _ _
  rw [hmap, ← hv]
  exact hindex.symm

end AtiyahSinger

end PositiveInputs

section ZeroSphere

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

variable {n : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin 0) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin 0) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas 0 (𝓡 n) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

local notation "OG" => Matrix.orthogonalGroup (Fin 0) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "E0" => EuclideanSpace ℝ (Fin 0)
local notation "Z" => AssociatedBundle OG P (OrthogonalSphere 0)
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := 0) (M := OrthogonalSphere 0)

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the original full-symbol inputs and separate zero-dimensional
-- endpoints.
/-- The original P05 identity for the zero-dimensional sphere. -/
theorem associatedSphere_zero_index_call
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero OG SphereCot) :
    associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
      analyticIndexOfComponents μ
        (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle
            (orthogonalSphereAnalyticIndex 0 v)) u) := by
  classical
  have hmul (a b : ℤ) : a * b = b • a := by
    simpa only [zsmul_eq_mul, Int.cast_id] using Int.mul_comm a b
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := orthogonalGroupChartedSpace 0
  let := lieGroup_orthogonalGroup 0
  let := compactSpace_orthogonalGroup 0
  let : MeasurableSpace OG := borel OG
  let : BorelSpace OG := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere 0) := borel (OrthogonalSphere 0)
  let : BorelSpace (OrthogonalSphere 0) := ⟨rfl⟩
  -- Choose the auxiliary sphere density before constructing the dependent quotient geometry.
  let ν : Measure (OrthogonalSphere 0) :=
    (exists_smoothPositiveMeasure (n := 0) (M := OrthogonalSphere 0)).choose
  let : IsSmoothPositiveMeasure (n := 0) ν :=
    (exists_smoothPositiveMeasure (n := 0) (M := OrthogonalSphere 0)).choose_spec
  have hcontrol : associatedControl OG P (OrthogonalSphere 0) Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | h w => exact ⟨w, ⟨Set.mem_univ w.1, Set.mem_univ w.2⟩, rfl⟩
  let : CompactSpace Z := ⟨by
    rw [← hcontrol]
    exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
      (fun _ _ ↦ Iff.rfl)⟩
  let := associatedBundle_t2Space (Y := OrthogonalSphere 0) S.toIsPrincipalBundle
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : ChartedSpace (En × E0) (B × OrthogonalSphere 0) :=
    prodChartedSpace En B E0 (OrthogonalSphere 0)
  let : IsManifold 𝓘(ℝ, En × E0) ∞ (B × OrthogonalSphere 0) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓡 0) B (OrthogonalSphere 0)
  let H := associatedSphereHorizontalLift S
  let a := associatedSphereCotangentHomeomorph S H
  let := associatedBundle_t2Space (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  let := associatedBundle_locallyCompactSpace (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  let := a.t2Space
  let := a.symm.isOpenEmbedding.locallyCompactSpace
  let prod := cotangentProductModelHomeomorph (n := n) (m := 0) B (OrthogonalSphere 0)
  let := prod.symm.t2Space
  let := prod.isOpenEmbedding.locallyCompactSpace
  -- The two supplied quotient product maps retain the principal and fiber coordinates.
  have hact (g : OG) (y : OrthogonalSphere 0) : g • y = y := by
    rw [Subsingleton.elim g 1, one_smul]
  obtain ⟨d₀, hd₀⟩ := exists_associatedSphere_productDiffeomorph_of_trivial_action S hact
  let d : Z ≃ₘ⟮𝓘(ℝ, En × E0), 𝓘(ℝ, En × E0)⟯ (B × OrthogonalSphere 0) := {
    d₀.toHomeomorph with
    contMDiff_toFun := by
      let f : Z → B × OrthogonalSphere 0 := d₀
      have h : ContMDiff 𝓘(ℝ, En × E0) ((𝓡 n).prod (𝓡 0)) ∞ f := d₀.contMDiff
      change ContMDiff 𝓘(ℝ, En × E0) 𝓘(ℝ, En × E0) ∞ f
      rw [← modelWithCornersSelf_prod] at h
      exact h
    contMDiff_invFun := by
      let f : B × OrthogonalSphere 0 → Z := d₀.symm
      have h : ContMDiff ((𝓡 n).prod (𝓡 0)) 𝓘(ℝ, En × E0) ∞ f := d₀.symm.contMDiff
      change ContMDiff 𝓘(ℝ, En × E0) 𝓘(ℝ, En × E0) ∞ f
      rw [← modelWithCornersSelf_prod] at h
      exact h }
  obtain ⟨e, he, hproduct⟩ :=
    exists_associatedSupportTwistedProduct_eq_externalProduct_of_subsingleton
      (G := OG) (projection := projection) (Y := SphereCot)
      (cotangentProjection (n := n) (M := B))
  let c := (a.symm.trans e).trans prod.symm
  have hc (z) : c z = ⟨d z.proj,
      z.snd.comp (mfderiv 𝓘(ℝ, En × E0) 𝓘(ℝ, En × E0) d.symm (d z.proj))⟩ :=
    associatedSphereCotangentProduct_inverseDifferential_of_zero S H d hd₀ e he z
  let w := supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget v)
  let b := compactSupportKZeroExternalProduct u w
  let t := compactSupportKZeroPullback ⟨prod, prod.continuous⟩ prod.isProperMap b
  have hclass : associatedSphereTwistedProduct S u v =
      compactSupportKZeroPullback ⟨c, c.continuous⟩ c.isProperMap t := by
    change compactSupportKZeroPullback ⟨a.symm, a.symm.continuous⟩ a.symm.isProperMap
      (associatedSupportTwistedProduct (G := OG) (projection := projection)
        (cotangentProjection (n := n) (M := B)) u v) = _
    rw [hproduct]
    change compactSupportKZeroPullback ⟨a.symm, a.symm.continuous⟩ a.symm.isProperMap
      (compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap b) =
        compactSupportKZeroPullback ⟨c, c.continuous⟩ c.isProperMap
          (compactSupportKZeroPullback ⟨prod, prod.continuous⟩ prod.isProperMap b)
    have hleft := DFunLike.congr_fun (compactSupportKZeroPullback_comp
      ⟨a.symm, a.symm.continuous⟩ ⟨e, e.continuous⟩
      a.symm.isProperMap e.isProperMap) b
    have hright := DFunLike.congr_fun (compactSupportKZeroPullback_comp
      ⟨c, c.continuous⟩ ⟨prod, prod.continuous⟩
      c.isProperMap prod.isProperMap) b
    have heq : (⟨e, e.continuous⟩ : C(_, _)).comp ⟨a.symm, a.symm.continuous⟩ =
        (⟨prod, prod.continuous⟩ : C(_, _)).comp ⟨c, c.continuous⟩ := by
      apply ContinuousMap.ext
      intro z
      exact (prod.apply_symm_apply (e (a.symm z))).symm
    have hmid : compactSupportKZeroPullback
        ((⟨e, e.continuous⟩ : C(_, _)).comp ⟨a.symm, a.symm.continuous⟩)
        (e.isProperMap.comp a.symm.isProperMap) b = compactSupportKZeroPullback
          ((⟨prod, prod.continuous⟩ : C(_, _)).comp ⟨c, c.continuous⟩)
          (prod.isProperMap.comp c.isProperMap) b := by
      congr 2
    exact hleft.symm.trans (hmid.trans hright)
  have htransport : compactSupportKZeroHomeomorph c
      (associatedSphereTwistedProduct S u v) = t := by
    rw [hclass]
    exact DFunLike.congr_fun (compactSupportKZeroHomeomorph_symm c.symm) t
  let em := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 0)).symm
  have hnative : analyticIndexLinearModel em (B × OrthogonalSphere 0)
      (compactSupportKZeroHomeomorph c (associatedSphereTwistedProduct S u v)) =
        analyticIndexLinearModel em Z (associatedSphereTwistedProduct S u v) :=
    DFunLike.congr_fun (analyticIndexLinearModel_diffeomorph em em d c hc)
      (associatedSphereTwistedProduct S u v)
  -- Ordinary product multiplicativity evaluates this same full-model product class.
  have hproductIndex := analyticIndexLinearModel_externalProduct μ ν u w
  have hindex : associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
      analyticIndexOfComponents μ u * analyticIndexOfComponents ν w := by
    change analyticIndexLinearModel em Z (associatedSphereTwistedProduct S u v) = _
    exact hnative.symm.trans
      ((congrArg (analyticIndexLinearModel em (B × OrthogonalSphere 0)) htransport).trans
        hproductIndex)
  -- Only O(0) is reduced to dimension; its original coefficient map remains unchanged.
  have hmap : orthogonalSphereAnalyticIndex 0 = equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel 0) (G := OG) (n := 0) (M := OrthogonalSphere 0) := by
    simp only [orthogonalSphereAnalyticIndex, id_eq]
  have hdim : representationDimension OG (orthogonalSphereAnalyticIndex 0 v) =
      analyticIndexOfComponents ν w := by
    rw [hmap]
    exact DFunLike.congr_fun (representationDimension_equivariantAnalyticIndexMap
      (n := 0) (M := OrthogonalSphere 0) (VG := OrthogonalGroupModel 0) (G := OG) ν) v
  have hcoeff : associatedRepresentationKZero S.toIsPrincipalBundle
      (orthogonalSphereAnalyticIndex 0 v) = (analyticIndexOfComponents ν w : ComplexKZero B) := by
    rw [representation_eq_intCast_dimension_of_subsingleton (orthogonalSphereAnalyticIndex 0 v),
      map_intCast, hdim]
  have haction : complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
      (analyticIndexOfComponents ν w : ComplexKZero B) u =
        analyticIndexOfComponents ν w • u := by
    have hone : complexKZeroCompactSupportAction
        (cotangentProjection (n := n) (M := B)) (1 : ComplexKZero B) u = u :=
      complexKZeroCompactSupportAction_one (cotangentProjection (n := n) (M := B)) u
    rw [← zsmul_one (analyticIndexOfComponents ν w), map_zsmul,
      AddMonoidHom.zsmul_apply, hone]
  have hcoefficientAction : complexKZeroCompactSupportAction
      (cotangentProjection (n := n) (M := B))
        (associatedRepresentationKZero S.toIsPrincipalBundle
          (orthogonalSphereAnalyticIndex 0 v)) u =
          analyticIndexOfComponents ν w • u :=
    (congrArg (fun k : ComplexKZero B ↦ complexKZeroCompactSupportAction
      (cotangentProjection (n := n) (M := B)) k u) hcoeff).trans haction
  calc
    associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
        analyticIndexOfComponents μ u * analyticIndexOfComponents ν w := hindex
    _ = analyticIndexOfComponents ν w • analyticIndexOfComponents μ u :=
      hmul _ _
    _ = analyticIndexOfComponents μ (analyticIndexOfComponents ν w • u) :=
      (map_zsmul (analyticIndexOfComponents μ) (analyticIndexOfComponents ν w) u).symm
    _ = analyticIndexOfComponents μ
        (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle
            (orthogonalSphereAnalyticIndex 0 v)) u) :=
      congrArg (analyticIndexOfComponents μ) hcoefficientAction.symm

end AtiyahSinger

end ZeroSphere

section ZeroBase

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

variable {r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) B] [IsManifold (𝓡 0) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 0) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := 0) μ]

local notation "OG" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "E0" => EuclideanSpace ℝ (Fin 0)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle OG P (OrthogonalSphere r)
local notation "BaseCot" => CotangentTotalSpace (n := 0) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the original full-symbol inputs and separate zero-dimensional
-- endpoints.
/-- The original P05 identity for a zero-dimensional base. -/
theorem associatedSphere_zero_base_index_call
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero OG SphereCot) :
    associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
      analyticIndexOfComponents μ
        (complexKZeroCompactSupportAction (cotangentProjection (n := 0) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle
            (orthogonalSphereAnalyticIndex r v)) u) := by
  classical
  have hmul (a b : ℤ) : a * b = b • a := by
    simpa only [zsmul_eq_mul, Int.cast_id] using Int.mul_comm a b
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := orthogonalGroupChartedSpace r
  let := lieGroup_orthogonalGroup r
  let := compactSpace_orthogonalGroup r
  let : MeasurableSpace OG := borel OG
  let : BorelSpace OG := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
  let : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
  -- Choose the auxiliary sphere density before constructing the dependent quotient geometry.
  let ν : Measure (OrthogonalSphere r) :=
    (exists_smoothPositiveMeasure (n := r) (M := OrthogonalSphere r)).choose
  let : IsSmoothPositiveMeasure (n := r) ν :=
    (exists_smoothPositiveMeasure (n := r) (M := OrthogonalSphere r)).choose_spec
  have hcontrol : associatedControl OG P (OrthogonalSphere r) Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | h w => exact ⟨w, ⟨Set.mem_univ w.1, Set.mem_univ w.2⟩, rfl⟩
  let : CompactSpace Z := ⟨by
    rw [← hcontrol]
    exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
      (fun _ _ ↦ Iff.rfl)⟩
  let := associatedBundle_t2Space (Y := OrthogonalSphere r) S.toIsPrincipalBundle
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : ChartedSpace (E0 × Er) (B × OrthogonalSphere r) :=
    prodChartedSpace E0 B Er (OrthogonalSphere r)
  let : IsManifold 𝓘(ℝ, E0 × Er) ∞ (B × OrthogonalSphere r) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 0) (I' := 𝓡 r) B (OrthogonalSphere r)
  let H := associatedSphereHorizontalLift S
  let a := associatedSphereCotangentHomeomorph S H
  let := associatedBundle_t2Space (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := 0) (M := B)))
  let := associatedBundle_locallyCompactSpace (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := 0) (M := B)))
  let := a.t2Space
  let := a.symm.isOpenEmbedding.locallyCompactSpace
  let prod := cotangentProductModelHomeomorph (n := 0) (m := r) B (OrthogonalSphere r)
  let := prod.symm.t2Space
  let := prod.isOpenEmbedding.locallyCompactSpace
  -- The two supplied quotient product maps retain the principal and fiber coordinates.
  let : DiscreteTopology B := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0)) B
  obtain ⟨θ, hθ, d₀, hd₀⟩ := exists_associatedSphere_productDiffeomorph_of_discreteTopology S
  let d : Z ≃ₘ⟮𝓘(ℝ, E0 × Er), 𝓘(ℝ, E0 × Er)⟯ (B × OrthogonalSphere r) := {
    d₀.toHomeomorph with
    contMDiff_toFun := by
      let f : Z → B × OrthogonalSphere r := d₀
      have h : ContMDiff 𝓘(ℝ, E0 × Er) ((𝓡 0).prod (𝓡 r)) ∞ f := d₀.contMDiff
      change ContMDiff 𝓘(ℝ, E0 × Er) 𝓘(ℝ, E0 × Er) ∞ f
      rw [← modelWithCornersSelf_prod] at h
      exact h
    contMDiff_invFun := by
      let f : B × OrthogonalSphere r → Z := d₀.symm
      have h : ContMDiff ((𝓡 0).prod (𝓡 r)) 𝓘(ℝ, E0 × Er) ∞ f := d₀.symm.contMDiff
      change ContMDiff 𝓘(ℝ, E0 × Er) 𝓘(ℝ, E0 × Er) ∞ f
      rw [← modelWithCornersSelf_prod] at h
      exact h }
  obtain ⟨e, he, hproduct⟩ :=
    exists_associatedSupportTwistedProduct_eq_externalProduct_of_gauge
      (G := OG) (projection := projection) (Y := SphereCot)
      (cotangentProjection (n := 0) (M := B)) θ hθ
  let c := (a.symm.trans e).trans prod.symm
  have hc (z) : c z = ⟨d z.proj,
      z.snd.comp (mfderiv 𝓘(ℝ, E0 × Er) 𝓘(ℝ, E0 × Er) d.symm (d z.proj))⟩ :=
    associatedSphereCotangentProduct_inverseDifferential_of_base_dim_zero S H θ d hd₀ e he z
  let w := supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget v)
  let b := compactSupportKZeroExternalProduct u w
  let t := compactSupportKZeroPullback ⟨prod, prod.continuous⟩ prod.isProperMap b
  have hclass : associatedSphereTwistedProduct S u v =
      compactSupportKZeroPullback ⟨c, c.continuous⟩ c.isProperMap t := by
    change compactSupportKZeroPullback ⟨a.symm, a.symm.continuous⟩ a.symm.isProperMap
      (associatedSupportTwistedProduct (G := OG) (projection := projection)
        (cotangentProjection (n := 0) (M := B)) u v) = _
    rw [hproduct]
    change compactSupportKZeroPullback ⟨a.symm, a.symm.continuous⟩ a.symm.isProperMap
      (compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap b) =
        compactSupportKZeroPullback ⟨c, c.continuous⟩ c.isProperMap
          (compactSupportKZeroPullback ⟨prod, prod.continuous⟩ prod.isProperMap b)
    have hleft := DFunLike.congr_fun (compactSupportKZeroPullback_comp
      ⟨a.symm, a.symm.continuous⟩ ⟨e, e.continuous⟩
      a.symm.isProperMap e.isProperMap) b
    have hright := DFunLike.congr_fun (compactSupportKZeroPullback_comp
      ⟨c, c.continuous⟩ ⟨prod, prod.continuous⟩
      c.isProperMap prod.isProperMap) b
    have heq : (⟨e, e.continuous⟩ : C(_, _)).comp ⟨a.symm, a.symm.continuous⟩ =
        (⟨prod, prod.continuous⟩ : C(_, _)).comp ⟨c, c.continuous⟩ := by
      apply ContinuousMap.ext
      intro z
      exact (prod.apply_symm_apply (e (a.symm z))).symm
    have hmid : compactSupportKZeroPullback
        ((⟨e, e.continuous⟩ : C(_, _)).comp ⟨a.symm, a.symm.continuous⟩)
        (e.isProperMap.comp a.symm.isProperMap) b = compactSupportKZeroPullback
          ((⟨prod, prod.continuous⟩ : C(_, _)).comp ⟨c, c.continuous⟩)
          (prod.isProperMap.comp c.isProperMap) b := by
      congr 2
    exact hleft.symm.trans (hmid.trans hright)
  have htransport : compactSupportKZeroHomeomorph c
      (associatedSphereTwistedProduct S u v) = t := by
    rw [hclass]
    exact DFunLike.congr_fun (compactSupportKZeroHomeomorph_symm c.symm) t
  let em := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 0) (m := r)).symm
  have hnative : analyticIndexLinearModel em (B × OrthogonalSphere r)
      (compactSupportKZeroHomeomorph c (associatedSphereTwistedProduct S u v)) =
        analyticIndexLinearModel em Z (associatedSphereTwistedProduct S u v) :=
    DFunLike.congr_fun (analyticIndexLinearModel_diffeomorph em em d c hc)
      (associatedSphereTwistedProduct S u v)
  -- Ordinary product multiplicativity evaluates this same full-model product class.
  have hproductIndex := analyticIndexLinearModel_externalProduct μ ν u w
  have hindex : associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
      analyticIndexOfComponents μ u * analyticIndexOfComponents ν w := by
    change analyticIndexLinearModel em Z (associatedSphereTwistedProduct S u v) = _
    exact hnative.symm.trans
      ((congrArg (analyticIndexLinearModel em (B × OrthogonalSphere r)) htransport).trans
        hproductIndex)
  -- The original gauge trivializes the actual coefficient bundle before taking its dimension.
  have hmap : orthogonalSphereAnalyticIndex r = equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel r) (G := OG) (n := r) (M := OrthogonalSphere r) := by
    simp only [orthogonalSphereAnalyticIndex, id_eq]
  have hdim : representationDimension OG (orthogonalSphereAnalyticIndex r v) =
      analyticIndexOfComponents ν w := by
    rw [hmap]
    exact DFunLike.congr_fun (representationDimension_equivariantAnalyticIndexMap
      (n := r) (M := OrthogonalSphere r) (VG := OrthogonalGroupModel r) (G := OG) ν) v
  have hcoeff : associatedRepresentationKZero S.toIsPrincipalBundle
      (orthogonalSphereAnalyticIndex r v) = (analyticIndexOfComponents ν w : ComplexKZero B) := by
    exact (associatedRepresentationKZero_eq_dimension_of_gauge S.toIsPrincipalBundle θ hθ
      (orthogonalSphereAnalyticIndex r v)).trans
        (congrArg (fun k : ℤ ↦ (k : ComplexKZero B)) hdim)
  have haction : complexKZeroCompactSupportAction (cotangentProjection (n := 0) (M := B))
      (analyticIndexOfComponents ν w : ComplexKZero B) u =
        analyticIndexOfComponents ν w • u := by
    have hone : complexKZeroCompactSupportAction
        (cotangentProjection (n := 0) (M := B)) (1 : ComplexKZero B) u = u :=
      complexKZeroCompactSupportAction_one (cotangentProjection (n := 0) (M := B)) u
    rw [← zsmul_one (analyticIndexOfComponents ν w), map_zsmul,
      AddMonoidHom.zsmul_apply, hone]
  have hcoefficientAction : complexKZeroCompactSupportAction
      (cotangentProjection (n := 0) (M := B))
        (associatedRepresentationKZero S.toIsPrincipalBundle
          (orthogonalSphereAnalyticIndex r v)) u =
          analyticIndexOfComponents ν w • u :=
    (congrArg (fun k : ComplexKZero B ↦ complexKZeroCompactSupportAction
      (cotangentProjection (n := 0) (M := B)) k u) hcoeff).trans haction
  calc
    associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
        analyticIndexOfComponents μ u * analyticIndexOfComponents ν w := hindex
    _ = analyticIndexOfComponents ν w • analyticIndexOfComponents μ u :=
      hmul _ _
    _ = analyticIndexOfComponents μ (analyticIndexOfComponents ν w • u) :=
      (map_zsmul (analyticIndexOfComponents μ) (analyticIndexOfComponents ν w) u).symm
    _ = analyticIndexOfComponents μ
        (complexKZeroCompactSupportAction (cotangentProjection (n := 0) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle
            (orthogonalSphereAnalyticIndex r v)) u) :=
      congrArg (analyticIndexOfComponents μ) hcoefficientAction.symm

end AtiyahSinger

end ZeroBase


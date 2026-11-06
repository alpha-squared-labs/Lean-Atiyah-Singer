/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SmoothFiniteRepresentation
public import AtiyahSinger.Analysis.EquivariantAnalyticIndexEvaluation
public import AtiyahSinger.Analysis.EquivariantClopenIndexDescent
public import AtiyahSinger.Analysis.EquivariantEllipticSymbolTensor
public import AtiyahSinger.Analysis.EquivariantIndexOperations
public import AtiyahSinger.Analysis.EquivariantIndexTensor
public import AtiyahSinger.Topology.EquivariantRepresentationNaturality

/-!
# Representation linearity of the original equivariant analytic index

Public module ID: M0462.

The full analytic index commutes with the existing representation-ring scalar
action on every original equivariant cotangent support K class. The coefficient
is an arbitrary virtual representation, and the conclusion remains in the full
representation ring. No new K presentation, scalar action or index is introduced.

The finite-representation calculation uses the actual smooth tensor bundles
and the coordinatewise tensor operator. Its group action mixes coordinates by
the original representation matrix. The actual smooth kernels and quotient cokernels
are compared in those same finite coordinates; their original finite representations
give the full index.
Finite invariant clopen assembly then handles arbitrary original K classes,
and additive descent handles virtual coefficients. Both original ranks may
vary independently between pieces; zero ranks and dimension zero are retained.

Sources: SG III.9, pp.211--213, supplies the full representation-valued index
and its equivariant framework; SG III.13, pp.245--247, supplies ordinary index
descent. ASI I Section 2 supplies the original representation-module action.
The exact compatibility of these concrete presentations and tensor realization
is a project supplement; no exact independent source has been identified.
Automatic smoothness of the original finite continuous representation is also
used; an exact independent reference for this step has not been identified.
The proof combines the actual finite tensor calculation, invariant clopen
assembly, and additive descent in the original representation presentation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The full analytic index is linear for the original representation-ring module action. -/
theorem equivariantAnalyticIndexMap_smul :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (r : RepresentationGrothendieckGroup G)
      (z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M))),
      equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M) (r • z) =
        r • equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M) z := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro r z
  let I := equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M)
  have eval (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)) :
      I a.kClass = a.index := by
    let P := a.partition
    let := P.mulAction
    let := P.continuousSMul
    let := P.contMDiffSMul (n := n) (VG := VG)
    let := P.compactSpace
    exact equivariantAnalyticIndexMap_clopen (n := n) (M := M) (VG := VG) (G := G)
      P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
      (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
      (fun i ↦ (a.symbols i).source) (fun i ↦ (a.symbols i).target)
      (fun i ↦ (a.symbols i).sourceAction) (fun i ↦ (a.symbols i).targetAction)
      (fun i ↦ (a.symbols i).source_smooth) (fun i ↦ (a.symbols i).target_smooth)
      (fun i ↦ (a.symbols i).symbol) (fun i ↦ (a.symbols i).elliptic)
      (fun i ↦ (a.symbols i).equivariant)
  have finite (ρ : FiniteContinuousRepresentation G) :
      I (finiteRepresentationClass ρ • z) = finiteRepresentationClass ρ * I z := by
    -- One original invariant partition suffices for both the class and its actual tensor.
    obtain ⟨a, ha⟩ := exists_equivariantClopenSymbolFamily
      (n := n) (M := M) (VG := VG) z
    let P := a.partition
    let := P.mulAction
    let := P.continuousSMul
    let := P.contMDiffSMul (n := n) (VG := VG)
    let := P.compactSpace
    choose b hb hi using fun i ↦ (a.symbols i).exists_tensor ρ
    let c : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G) := ⟨P, b⟩
    let Φ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
      P.equivariant P.disjoint P.cover
    have hc : c.kClass = finiteRepresentationClass ρ • a.kClass := by
      apply Φ.injective
      funext i
      have hleft : Φ c.kClass i = (b i).kClass := by
        change Φ (Φ.symm (fun j ↦ (b j).kClass)) i = _
        rw [Φ.apply_symm_apply]
      have hright : Φ a.kClass i = (a.symbols i).kClass := by
        change Φ (Φ.symm (fun j ↦ (a.symbols j).kClass)) i = _
        rw [Φ.apply_symm_apply]
      rw [hleft, hb]
      let f : C(CotangentTotalSpace (n := n) (M := P.piece i),
          CotangentTotalSpace (n := n) (M := M)) :=
        ⟨cotangentOpenInclusion (P.piece i),
          (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).continuous⟩
      have hf : IsProperMap f := isProperMap_cotangentOpenInclusion (P.piece i) (P.isClosed i)
      let := smoothCotangentMulAction (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
      let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
      let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
        ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      have hfG : ∀ g y, f (g • y) = g • f y :=
        cotangentOpenInclusion_smul 𝓘(ℝ, VG) (P.piece i) (P.equivariant i)
      change finiteRepresentationClass ρ • (a.symbols i).kClass =
        equivariantSupportTripleKZeroPullback f hfG hf (finiteRepresentationClass ρ • a.kClass)
      rw [equivariantSupportTripleKZeroPullback_smul]
      exact congrArg (fun w ↦ finiteRepresentationClass ρ • w) hright.symm
    rw [← ha, ← hc, eval, eval]
    change (∑ i, (b i).index) = finiteRepresentationClass ρ * ∑ i, (a.symbols i).index
    simp_rw [hi]
    exact (Finset.mul_sum _ _ _).symm
  -- Biadditivity extends the full representation formula to arbitrary virtual coefficients.
  let μ := equivariantSupportRepresentationAction
    (G := G) (X := CotangentTotalSpace (n := n) (M := M))
  have h : I.comp (μ.flip z) = (representationMul G).flip (I z) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact finite
  exact DFunLike.congr_fun h r

/-- The existing full analytic index packaged as a linear map over the representation ring. -/
def equivariantAnalyticIndexLinearMap :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →ₗ[
      RepresentationGrothendieckGroup G] RepresentationGrothendieckGroup G :=
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  { toFun := equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M)
    map_add' := (equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M)).map_add
    map_smul' := equivariantAnalyticIndexMap_smul (n := n) (VG := VG) (G := G) (M := M) }

end AtiyahSinger

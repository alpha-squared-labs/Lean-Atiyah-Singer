/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationExternalProduct
public import AtiyahSinger.Analysis.EquivariantClosedKernelRepresentations
public import AtiyahSinger.Analysis.EquivariantExternalTensorL2
public import AtiyahSinger.Analysis.EquivariantGeometricTensorFredholm

/-!
# The actual independent-group tensor index on the native graph

Public module ID: M0542.

The specified factor operators determine their original closed kernel and
adjoint-kernel representations. Their independent actions, transported by
the original external tensor L² unitaries, determine the full geometric
graph index. This retains the actual H¹ domain and computes the external
product in the representation ring, including empty and
zero-dimensional cases.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

/-- Isometric linear component actions induce a jointly continuous action on their ℓ² sum. -/
private theorem exists_contRepresentation_withLp {G V W : Type*}
    [Group G] [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (a : G →* (V ≃ₗᵢ[ℂ] V)) (b : G →* (W ≃ₗᵢ[ℂ] W))
    (ha : Continuous (fun p : G × V ↦ a p.1 p.2))
    (hb : Continuous (fun p : G × W ↦ b p.1 p.2)) :
    ∃ (ρ : ContRepresentation ℂ G (WithLp 2 (V × W)))
      (_hρ : Continuous (fun p : G × WithLp 2 (V × W) ↦ ρ p.1 p.2)),
      ∃ I : G →* (WithLp 2 (V × W) ≃ₗᵢ[ℂ] WithLp 2 (V × W)),
        (∀ g v, I g v = ρ g v) ∧
        (∀ g v, ρ g v = WithLp.toLp 2 (a g (WithLp.ofLp v).1, b g (WithLp.ofLp v).2)) := by
  let I : G →* (WithLp 2 (V × W) ≃ₗᵢ[ℂ] WithLp 2 (V × W)) := {
    toFun := fun g ↦ (a g).withLpProdCongr 2 (b g)
    map_one' := by
      ext v
      apply WithLp.ofLp_injective
      change (a 1 (WithLp.ofLp v).1, b 1 (WithLp.ofLp v).2) = WithLp.ofLp v
      rw [map_one, map_one]
      rfl
    map_mul' := by
      intro g h
      ext v
      apply WithLp.ofLp_injective
      change (a (g * h) (WithLp.ofLp v).1, b (g * h) (WithLp.ofLp v).2) =
        (a g (a h (WithLp.ofLp v).1), b g (b h (WithLp.ofLp v).2))
      rw [map_mul, map_mul]
      rfl }
  let ρ : ContRepresentation ℂ G (WithLp 2 (V × W)) := ⟨{
    toFun := fun g ↦ (I g).toLinearIsometry.toContinuousLinearMap
    map_one' := by
      apply ContinuousLinearMap.ext
      intro v
      change I 1 v = v
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply ContinuousLinearMap.ext
      intro v
      change I (g * h) v = I g (I h v)
      rw [map_mul]
      rfl }⟩
  have hc : Continuous (fun p : G × WithLp 2 (V × W) ↦ ρ p.1 p.2) := by
    have hp : Continuous (fun p : G × WithLp 2 (V × W) ↦ WithLp.ofLp p.2) :=
      (WithLp.prod_continuous_ofLp 2 V W).comp continuous_snd
    exact (WithLp.prod_continuous_toLp 2 V W).comp
      ((ha.comp (continuous_fst.prodMk hp.fst)).prodMk
        (hb.comp (continuous_fst.prodMk hp.snd)))
  exact ⟨ρ, hc, I, (fun _ _ ↦ rfl), fun _ _ ↦ rfl⟩

variable {VG VH G H : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG] [FiniteDimensional ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH] [FiniteDimensional ℝ VH]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [LieGroup 𝓘(ℝ, VH) ∞ H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H]
  {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G M] [ContinuousSMul G M]
  [MulAction H N] [ContinuousSMul H N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N]

variable (E₀ E₁ : SmoothFiniteComplexBundle (n := n) M)
  (F₀ F₁ : SmoothFiniteComplexBundle (n := m) N)
  (σ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    EquivariantStructure G E₀.Fiber)
  (hσ₀ : σ₀.IsSmooth (n := n) (r := E₀.rank) 𝓘(ℝ, VG))
  (σ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    EquivariantStructure G E₁.Fiber)
  (hσ₁ : σ₁.IsSmooth (n := n) (r := E₁.rank) 𝓘(ℝ, VG))
  (τ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    EquivariantStructure H F₀.Fiber)
  (hτ₀ : τ₀.IsSmooth (n := m) (r := F₀.rank) 𝓘(ℝ, VH))
  (τ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    EquivariantStructure H F₁.Fiber)
  (hτ₁ : τ₁.IsSmooth (n := m) (r := F₁.rank) 𝓘(ℝ, VH))
  (h₀ : SmoothHermitianMetric (n := n) (r := E₀.rank) E₀.Fiber)
  (hh₀Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    ∀ (a : G) (x : M) (u v : E₀.Fiber x),
      h₀.pairing (a • x) (σ₀.linearMap a x u) (σ₀.linearMap a x v) =
        h₀.pairing x u v)
  (h₁ : SmoothHermitianMetric (n := n) (r := E₁.rank) E₁.Fiber)
  (hh₁Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    ∀ (a : G) (x : M) (u v : E₁.Fiber x),
      h₁.pairing (a • x) (σ₁.linearMap a x u) (σ₁.linearMap a x v) =
        h₁.pairing x u v)
  (k₀ : SmoothHermitianMetric (n := m) (r := F₀.rank) F₀.Fiber)
  (hk₀Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    ∀ (a : H) (x : N) (u v : F₀.Fiber x),
      k₀.pairing (a • x) (τ₀.linearMap a x u) (τ₀.linearMap a x v) =
        k₀.pairing x u v)
  (k₁ : SmoothHermitianMetric (n := m) (r := F₁.rank) F₁.Fiber)
  (hk₁Invariant : letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    ∀ (a : H) (x : N) (u v : F₁.Fiber x),
      k₁.pairing (a • x) (τ₁.linearMap a x u) (τ₁.linearMap a x v) =
        k₁.pairing x u v)
  (μ : MeasureTheory.Measure M) (ν : MeasureTheory.Measure N)
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := m) ν]
  (hμInvariant : ∀ a : G, MeasureTheory.Measure.map (fun x : M ↦ a • x) μ = μ)
  (hνInvariant : ∀ a : H, MeasureTheory.Measure.map (fun x : N ↦ a • x) ν = ν)
  (P : PseudodifferentialOperator (n := n) (r := E₀.rank) (q := E₁.rank)
    E₀.Fiber E₁.Fiber μ 1)
  (Q : PseudodifferentialOperator (n := m) (r := F₀.rank) (q := F₁.rank)
    F₀.Fiber F₁.Fiber ν 1)
  (hPg : P.IsEquivariant 𝓘(ℝ, VG) σ₀ σ₁ hσ₀ hσ₁)
  (hQg : Q.IsEquivariant 𝓘(ℝ, VH) τ₀ τ₁ hτ₀ hτ₁)

include hμInvariant hνInvariant

omit [FiniteDimensional ℝ VG] [FiniteDimensional ℝ VH]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 28000000 in
-- Use the original four factor actions throughout the completed tensor and H1 comparisons.
/-- The actual native tensor graph has the external product of the original full indices. -/
theorem exists_gradedProductL2Operator_native_index (hP : P.IsElliptic) (hQ : Q.IsElliptic) :
    letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    letI : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G H
    letI := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    letI := externalTensorTopology (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    letI := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    letI := externalTensorTopology (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    letI := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    letI := externalTensorTopology (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    letI := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    letI := externalTensorTopology (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    let θ₀₀ := externalTensorEquivariantStructure E₀.Fiber F₀.Fiber σ₀ τ₀
    let hθ₀₀ := externalTensorEquivariantStructure_isSmooth E₀.Fiber F₀.Fiber σ₀ τ₀ hσ₀ hτ₀
    let g₀₀ := externalTensorMetric h₀ k₀
    let hg₀₀ := externalTensorMetric_invariant E₀.Fiber F₀.Fiber σ₀ τ₀
      h₀ k₀ hh₀Invariant hk₀Invariant
    let θ₁₁ := externalTensorEquivariantStructure E₁.Fiber F₁.Fiber σ₁ τ₁
    let hθ₁₁ := externalTensorEquivariantStructure_isSmooth E₁.Fiber F₁.Fiber σ₁ τ₁ hσ₁ hτ₁
    let g₁₁ := externalTensorMetric h₁ k₁
    let hg₁₁ := externalTensorMetric_invariant E₁.Fiber F₁.Fiber σ₁ τ₁
      h₁ k₁ hh₁Invariant hk₁Invariant
    let θ₁₀ := externalTensorEquivariantStructure E₁.Fiber F₀.Fiber σ₁ τ₀
    let hθ₁₀ := externalTensorEquivariantStructure_isSmooth E₁.Fiber F₀.Fiber σ₁ τ₀ hσ₁ hτ₀
    let g₁₀ := externalTensorMetric h₁ k₀
    let hg₁₀ := externalTensorMetric_invariant E₁.Fiber F₀.Fiber σ₁ τ₀
      h₁ k₀ hh₁Invariant hk₀Invariant
    let θ₀₁ := externalTensorEquivariantStructure E₀.Fiber F₁.Fiber σ₀ τ₁
    let hθ₀₁ := externalTensorEquivariantStructure_isSmooth E₀.Fiber F₁.Fiber σ₀ τ₁ hσ₀ hτ₁
    let g₀₁ := externalTensorMetric h₀ k₁
    let hg₀₁ := externalTensorMetric_invariant E₀.Fiber F₁.Fiber σ₀ τ₁
      h₀ k₁ hh₀Invariant hk₁Invariant
    let EvenG := WithLp 2 (g₀₀.L2SectionSpace (μ.prod ν) × g₁₁.L2SectionSpace (μ.prod ν))
    let OddG := WithLp 2 (g₁₀.L2SectionSpace (μ.prod ν) × g₀₁.L2SectionSpace (μ.prod ν))
    let L := gradedProductL2Operator h₀ h₁ k₀ k₁ P Q
    let Γ := L.graph.comap (WithLp.linearEquiv 2 ℂ (EvenG × OddG)).toLinearMap
    let FΓ := (WithLp.sndL 2 ℂ EvenG OddG).comp Γ.subtypeL
    ∃ hμν : ∀ a : G × H, MeasureTheory.Measure.map (fun z : M × N ↦ a • z) (μ.prod ν) = μ.prod ν,
    let R₀₀ := g₀₀.l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
      θ₀₀ hθ₀₀ hg₀₀ hμν
    let R₁₁ := g₁₁.l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
      θ₁₁ hθ₁₁ hg₁₁ hμν
    let R₁₀ := g₁₀.l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
      θ₁₀ hθ₁₀ hg₁₀ hμν
    let R₀₁ := g₀₁.l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
      θ₀₁ hθ₀₁ hg₀₁ hμν
    ∃ (ρ : ContRepresentation ℂ (G × H) EvenG)
      (τ : ContRepresentation ℂ (G × H) OddG)
      (_hρ : Continuous (fun p : (G × H) × EvenG ↦ ρ p.1 p.2))
      (hτ : Continuous (fun p : (G × H) × OddG ↦ τ p.1 p.2)),
      (∀ a v, ρ a v = WithLp.toLp 2
        (R₀₀ a (WithLp.ofLp v).1, R₁₁ a (WithLp.ofLp v).2)) ∧
      (∀ a v, τ a v = WithLp.toLp 2
        (R₁₀ a (WithLp.ofLp v).1, R₀₁ a (WithLp.ofLp v).2)) ∧
      ∀ (A : SmoothBundlePresentation (n := n + m) (r := E₀.rank * F₀.rank)
        (externalTensorFiber E₀.Fiber F₀.Fiber))
        (B : SmoothBundlePresentation (n := n + m) (r := E₁.rank * F₁.rank)
        (externalTensorFiber E₁.Fiber F₁.Fiber)),
      let J₀ := (g₀₀.sobolevZeroEquivL2 (μ := μ.prod ν) A).toContinuousLinearMap.comp
        (A.sobolevInclusion 1 0 (by norm_num))
      let J₁ := (g₁₁.sobolevZeroEquivL2 (μ := μ.prod ν) B).toContinuousLinearMap.comp
        (B.sobolevInclusion 1 0 (by norm_num))
      let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
        ((J₀.prodMap J₁).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)
      let T := gradedProductH1Extension h₀ h₁ k₀ k₁ P Q A B
      ∃ (γ : ContRepresentation ℂ (G × H) Γ)
        (hγ : Continuous (fun p : (G × H) × Γ ↦ γ p.1 p.2)),
        ∃ γI : (G × H) →* (Γ ≃ₗᵢ[ℂ] Γ), (∀ g v, γI g v = γ g v) ∧
          (∀ g v, (γ g v).val = WithLp.toLp 2
            (ρ g (WithLp.ofLp v.val).1, τ g (WithLp.ofLp v.val).2)) ∧
          ∃ Φ : WithLp 2 (A.SobolevSpace 1 × B.SobolevSpace 1) ≃L[ℂ] Γ,
            (∀ x, (Φ x).val = WithLp.toLp 2 (J x, T x)) ∧
            ∃ hFg : ∀ g, FΓ.comp (γ g) = (τ g).comp FΓ,
              ∃ hF : FΓ.IsFredholm,
                equivariantFredholmIndex γ τ hγ hτ FΓ hFg hF =
                  representationExternalProduct
                    (P.smoothEquivariantAnalyticIndex 𝓘(ℝ, VG) σ₀ σ₁ hσ₀ hσ₁ hPg hP)
                    (Q.smoothEquivariantAnalyticIndex 𝓘(ℝ, VH) τ₀ τ₁ hτ₀ hτ₁ hQg hQ) := by
  as_aux_lemma =>
    classical
    -- Use the actual closed kernel and adjoint-kernel actions of both original operators.
    have hPRepresentations :=
      P.exists_metricL2ClosedKernelRepresentations 𝓘(ℝ, VG) E₀ E₁ σ₀ σ₁ hσ₀ hσ₁
        h₀ h₁ hh₀Invariant hh₁Invariant μ hμInvariant hPg hP
    let κ₀ := hPRepresentations.choose
    have hPSecond := hPRepresentations.choose_spec
    let κ₁ := hPSecond.choose
    have hPEven := hPSecond.choose_spec
    let e₀ := hPEven.choose
    have hPOdd := hPEven.choose_spec
    let e₁ := hPOdd.choose
    have hPProps := hPOdd.choose_spec
    have he₀ := hPProps.1
    have he₁ := hPProps.2.1
    have hPindex := hPProps.2.2
    have hQRepresentations :=
      Q.exists_metricL2ClosedKernelRepresentations 𝓘(ℝ, VH) F₀ F₁ τ₀ τ₁ hτ₀ hτ₁
        k₀ k₁ hk₀Invariant hk₁Invariant ν hνInvariant hQg hQ
    let χ₀ := hQRepresentations.choose
    have hQSecond := hQRepresentations.choose_spec
    let χ₁ := hQSecond.choose
    have hQEven := hQSecond.choose_spec
    let f₀ := hQEven.choose
    have hQOdd := hQEven.choose_spec
    let f₁ := hQOdd.choose
    have hQProps := hQOdd.choose_spec
    have hf₀ := hQProps.1
    have hf₁ := hQProps.2.1
    have hQindex := hQProps.2.2
    have hTensor₀₀ := exists_externalTensorL2Equiv_intertwining
      (VG := VG) (VH := VH) (G := G) (H := H)
      (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber σ₀ τ₀ μ ν h₀ k₀ hσ₀ hτ₀
      hh₀Invariant hk₀Invariant hμInvariant hνInvariant
    dsimp only at hTensor₀₀
    let hμν := hTensor₀₀.choose
    have hU₀₀ := hTensor₀₀.choose_spec
    have hTensor₁₁ := exists_externalTensorL2Equiv_intertwining
      (VG := VG) (VH := VH) (G := G) (H := H)
      (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber σ₁ τ₁ μ ν h₁ k₁ hσ₁ hτ₁
      hh₁Invariant hk₁Invariant hμInvariant hνInvariant
    dsimp only at hTensor₁₁
    have hU₁₁ := hTensor₁₁.choose_spec
    have hTensor₁₀ := exists_externalTensorL2Equiv_intertwining
      (VG := VG) (VH := VH) (G := G) (H := H)
      (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber σ₁ τ₀ μ ν h₁ k₀ hσ₁ hτ₀
      hh₁Invariant hk₀Invariant hμInvariant hνInvariant
    dsimp only at hTensor₁₀
    have hU₁₀ := hTensor₁₀.choose_spec
    have hTensor₀₁ := exists_externalTensorL2Equiv_intertwining
      (VG := VG) (VH := VH) (G := G) (H := H)
      (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber σ₀ τ₁ μ ν h₀ k₁ hσ₀ hτ₁
      hh₀Invariant hk₁Invariant hμInvariant hνInvariant
    dsimp only at hTensor₀₁
    have hU₀₁ := hTensor₀₁.choose_spec
    let : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    let : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    let : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    let : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    let : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    let := euclideanProductChartedSpace (n := n) (m := m) M N
    let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    let := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    let : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G H
    let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    let := externalTensorTopology (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    let := externalTensorTopology (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    let := externalTensorTopology (r := E₁.rank) (s := F₀.rank) E₁.Fiber F₀.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    let := externalTensorTopology (r := E₀.rank) (s := F₁.rank) E₀.Fiber F₁.Fiber
    let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    dsimp only
    let θ₀₀ := externalTensorEquivariantStructure E₀.Fiber F₀.Fiber σ₀ τ₀
    let hθ₀₀ := externalTensorEquivariantStructure_isSmooth E₀.Fiber F₀.Fiber σ₀ τ₀ hσ₀ hτ₀
    let g₀₀ := externalTensorMetric h₀ k₀
    let hg₀₀ := externalTensorMetric_invariant E₀.Fiber F₀.Fiber σ₀ τ₀
      h₀ k₀ hh₀Invariant hk₀Invariant
    let θ₁₁ := externalTensorEquivariantStructure E₁.Fiber F₁.Fiber σ₁ τ₁
    let hθ₁₁ := externalTensorEquivariantStructure_isSmooth E₁.Fiber F₁.Fiber σ₁ τ₁ hσ₁ hτ₁
    let g₁₁ := externalTensorMetric h₁ k₁
    let hg₁₁ := externalTensorMetric_invariant E₁.Fiber F₁.Fiber σ₁ τ₁
      h₁ k₁ hh₁Invariant hk₁Invariant
    let θ₁₀ := externalTensorEquivariantStructure E₁.Fiber F₀.Fiber σ₁ τ₀
    let hθ₁₀ := externalTensorEquivariantStructure_isSmooth E₁.Fiber F₀.Fiber σ₁ τ₀ hσ₁ hτ₀
    let g₁₀ := externalTensorMetric h₁ k₀
    let hg₁₀ := externalTensorMetric_invariant E₁.Fiber F₀.Fiber σ₁ τ₀
      h₁ k₀ hh₁Invariant hk₀Invariant
    let θ₀₁ := externalTensorEquivariantStructure E₀.Fiber F₁.Fiber σ₀ τ₁
    let hθ₀₁ := externalTensorEquivariantStructure_isSmooth E₀.Fiber F₁.Fiber σ₀ τ₁ hσ₀ hτ₁
    let g₀₁ := externalTensorMetric h₀ k₁
    let hg₀₁ := externalTensorMetric_invariant E₀.Fiber F₁.Fiber σ₀ τ₁
      h₀ k₁ hh₀Invariant hk₁Invariant
    -- The two native Hilbert sums carry the actual direct-sum unitary actions.
    have hc₀₀ : Continuous (fun z : (G × H) × g₀₀.L2SectionSpace (μ.prod ν) ↦
        g₀₀.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
          θ₀₀ hθ₀₀ hg₀₀ hμν z.1 z.2) := by
      apply (g₀₀.continuous_l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
        θ₀₀ hθ₀₀ hg₀₀ hμν).congr
      intro z
      rfl
    have hc₁₁ : Continuous (fun z : (G × H) × g₁₁.L2SectionSpace (μ.prod ν) ↦
        g₁₁.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
          θ₁₁ hθ₁₁ hg₁₁ hμν z.1 z.2) := by
      apply (g₁₁.continuous_l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
        θ₁₁ hθ₁₁ hg₁₁ hμν).congr
      intro z
      rfl
    have hc₁₀ : Continuous (fun z : (G × H) × g₁₀.L2SectionSpace (μ.prod ν) ↦
        g₁₀.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
          θ₁₀ hθ₁₀ hg₁₀ hμν z.1 z.2) := by
      apply (g₁₀.continuous_l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
        θ₁₀ hθ₁₀ hg₁₀ hμν).congr
      intro z
      rfl
    have hc₀₁ : Continuous (fun z : (G × H) × g₀₁.L2SectionSpace (μ.prod ν) ↦
        g₀₁.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
          θ₀₁ hθ₀₁ hg₀₁ hμν z.1 z.2) := by
      apply (g₀₁.continuous_l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH)
        θ₀₁ hθ₀₁ hg₀₁ hμν).congr
      intro z
      rfl
    have hEven := exists_contRepresentation_withLp (G := G × H)
      (V := g₀₀.L2SectionSpace (μ.prod ν)) (W := g₁₁.L2SectionSpace (μ.prod ν))
      (g₀₀.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH) θ₀₀ hθ₀₀ hg₀₀ hμν)
      (g₁₁.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH) θ₁₁ hθ₁₁ hg₁₁ hμν)
      hc₀₀ hc₁₁
    let ρ := hEven.choose
    have hEvenContinuous := hEven.choose_spec
    let hρ := hEvenContinuous.choose
    have hEvenUnitary := hEvenContinuous.choose_spec
    let ρI := hEvenUnitary.choose
    have hEvenProps := hEvenUnitary.choose_spec
    have hρI := hEvenProps.1
    have hρapp := hEvenProps.2
    have hOdd := exists_contRepresentation_withLp (G := G × H)
      (V := g₁₀.L2SectionSpace (μ.prod ν)) (W := g₀₁.L2SectionSpace (μ.prod ν))
      (g₁₀.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH) θ₁₀ hθ₁₀ hg₁₀ hμν)
      (g₀₁.l2IsometryRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH) θ₀₁ hθ₀₁ hg₀₁ hμν)
      hc₁₀ hc₀₁
    let τ := hOdd.choose
    have hOddContinuous := hOdd.choose_spec
    let hτ := hOddContinuous.choose
    have hOddUnitary := hOddContinuous.choose_spec
    let τI := hOddUnitary.choose
    have hOddProps := hOddUnitary.choose_spec
    have hτI := hOddProps.1
    have hτapp := hOddProps.2
    refine ⟨hμν, ρ, τ, hρ, hτ, hρapp, hτapp, ?_⟩
    intro A B
    let A₀ := h₀.l2ContRepresentation μ 𝓘(ℝ, VG) σ₀ hσ₀ hh₀Invariant hμInvariant
    let A₁ := h₁.l2ContRepresentation μ 𝓘(ℝ, VG) σ₁ hσ₁ hh₁Invariant hμInvariant
    let B₀ := k₀.l2ContRepresentation ν 𝓘(ℝ, VH) τ₀ hτ₀ hk₀Invariant hνInvariant
    let B₁ := k₁.l2ContRepresentation ν 𝓘(ℝ, VH) τ₁ hτ₁ hk₁Invariant hνInvariant
    have hPcov := P.metricL2ClosedRealization_graph_invariant 𝓘(ℝ, VG) E₀ E₁ σ₀ σ₁ hσ₀ hσ₁
      h₀ h₁ hh₀Invariant hh₁Invariant μ hμInvariant hPg
    have hPacov := P.metricL2ClosedRealization_adjoint_graph_invariant
      𝓘(ℝ, VG) E₀ E₁ σ₀ σ₁ hσ₀ hσ₁ h₀ h₁ hh₀Invariant hh₁Invariant μ hμInvariant hPg hP
    have hQcov := Q.metricL2ClosedRealization_graph_invariant 𝓘(ℝ, VH) F₀ F₁ τ₀ τ₁ hτ₀ hτ₁
      k₀ k₁ hk₀Invariant hk₁Invariant ν hνInvariant hQg
    have hQacov := Q.metricL2ClosedRealization_adjoint_graph_invariant
      𝓘(ℝ, VH) F₀ F₁ τ₀ τ₁ hτ₀ hτ₁ k₀ k₁ hk₀Invariant hk₁Invariant ν hνInvariant hQg hQ
    let Ueven := (externalTensorL2Equiv μ ν h₀ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₁ k₁)
    let Uodd := (externalTensorL2Equiv μ ν h₁ k₀).withLpProdCongr 2
      (externalTensorL2Equiv μ ν h₀ k₁)
    have hUeven (g : G × H) (v : WithLp 2
        (HilbertTensorProduct (h₀.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
          HilbertTensorProduct (h₁.L2SectionSpace μ) (k₁.L2SectionSpace ν))) :
        Ueven (WithLp.toLp 2
          (hilbertTensorMap (A₀ g.1) (B₀ g.2) (WithLp.ofLp v).1,
            hilbertTensorMap (A₁ g.1) (B₁ g.2) (WithLp.ofLp v).2)) = ρ g (Ueven v) := by
      rw [hρapp]
      apply WithLp.ofLp_injective
      exact Prod.ext (hU₀₀ g (WithLp.ofLp v).1) (hU₁₁ g (WithLp.ofLp v).2)
    have hUodd (g : G × H) (v : WithLp 2
        (HilbertTensorProduct (h₁.L2SectionSpace μ) (k₀.L2SectionSpace ν) ×
          HilbertTensorProduct (h₀.L2SectionSpace μ) (k₁.L2SectionSpace ν))) :
        Uodd (WithLp.toLp 2
          (hilbertTensorMap (A₁ g.1) (B₀ g.2) (WithLp.ofLp v).1,
            hilbertTensorMap (A₀ g.1) (B₁ g.2) (WithLp.ofLp v).2)) = τ g (Uodd v) := by
      rw [hτapp]
      apply WithLp.ofLp_injective
      exact Prod.ext (hU₁₀ g (WithLp.ofLp v).1) (hU₀₁ g (WithLp.ofLp v).2)
    -- Inflate precisely the original finite kernel actions along the two product projections.
    have hGraph := exists_gradedProductL2Operator_graph_fredholm
      (G := G × H) (n := n) (m := m)
      (r₀ := E₀.rank) (r₁ := E₁.rank) (s₀ := F₀.rank) (s₁ := F₁.rank)
      h₀ h₁ k₀ k₁ P Q hP hQ
    dsimp only at hGraph
    let κ := ((κ₀.restrict (ContinuousMonoidHom.fst G H)).tensor
      (χ₀.restrict (ContinuousMonoidHom.snd G H))).directSum
        ((κ₁.restrict (ContinuousMonoidHom.fst G H)).tensor
          (χ₁.restrict (ContinuousMonoidHom.snd G H)))
    let χ := ((κ₁.restrict (ContinuousMonoidHom.fst G H)).tensor
      (χ₀.restrict (ContinuousMonoidHom.snd G H))).directSum
        ((κ₀.restrict (ContinuousMonoidHom.fst G H)).tensor
          (χ₁.restrict (ContinuousMonoidHom.snd G H)))
    -- Compute the tensor algebra before transporting the two original index equalities.
    have hKernelClass : finiteRepresentationClass κ - finiteRepresentationClass χ =
        representationExternalProduct
          (finiteRepresentationClass κ₀ - finiteRepresentationClass κ₁)
          (finiteRepresentationClass χ₀ - finiteRepresentationClass χ₁) := by
      dsimp only [κ, χ]
      rw [finiteRepresentationClass_directSum, finiteRepresentationClass_directSum]
      simp only [map_sub, AddMonoidHom.sub_apply, representationExternalProduct_finiteClass]
      abel
    have hclass := hKernelClass.trans
      (congrArg₂ (fun x y ↦ representationExternalProduct x y) hPindex.symm hQindex.symm)
    have hResult := hGraph
        (fun g : G × H ↦ A₀ g.1) (fun g : G × H ↦ A₁ g.1)
        (fun g : G × H ↦ B₀ g.2) (fun g : G × H ↦ B₁ g.2)
        (fun g z hz ↦ (hPcov g.1 z).mpr hz) (fun g z hz ↦ (hPacov g.1 z).mpr hz)
        (fun g z hz ↦ (hQcov g.2 z).mpr hz) (fun g z hz ↦ (hQacov g.2 z).mpr hz)
        ρ τ hρ hτ ρI τI hρI hτI hUeven hUodd
        (κ₀.restrict (ContinuousMonoidHom.fst G H))
        (κ₁.restrict (ContinuousMonoidHom.fst G H))
        (χ₀.restrict (ContinuousMonoidHom.snd G H))
        (χ₁.restrict (ContinuousMonoidHom.snd G H))
        e₀ e₁ f₀ f₁ (fun g v ↦ he₀ g.1 v) (fun g v ↦ he₁ g.1 v)
        (fun g v ↦ hf₀ g.2 v) (fun g v ↦ hf₁ g.2 v) A B
    -- Preserve every graph witness and compose only the final representation-ring equality.
    let γ := hResult.choose
    have hγexists := hResult.choose_spec
    let hγ := hγexists.choose
    have hγresult := hγexists.choose_spec
    let γI := hγresult.choose
    have hγprops := hγresult.choose_spec
    let Φ := hγprops.2.2.choose
    have hΦprops := hγprops.2.2.choose_spec
    let hFg := hΦprops.2.choose
    have hFredexists := hΦprops.2.choose_spec
    let hFred := hFredexists.choose
    have hIndex := hFredexists.choose_spec
    exact ⟨γ, hγ, γI, hγprops.1, hγprops.2.1, Φ, hΦprops.1,
      hFg, hFred, hIndex.trans hclass⟩

end AtiyahSinger

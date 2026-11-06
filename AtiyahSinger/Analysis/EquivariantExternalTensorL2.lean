/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantL2
public import AtiyahSinger.Analysis.ExternalTensorL2
public import AtiyahSinger.Geometry.EquivariantTensorSectionMetric

/-!
# The original geometric L² tensor unitary intertwines the independent actions

Public module ID: M0506.

The two factor metrics, factor densities and native fiber actions determine
the product integral action. Its comparison with the completed Hilbert tensor
map is proved on the same pure smooth tensors and extended by density to the
whole completion. No alternative unitary or Sobolev action is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 45

variable {G H M N : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace M] [TopologicalSpace N]
  [MulAction G M] [ContinuousSMul G M]
  [MulAction H N] [ContinuousSMul H N]
  {r s : ℕ} (E : M → Type*) (F : N → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    EquivariantStructure H F)


variable {VG VH : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [ChartedSpace VG G] [ChartedSpace VH H]
  [IsManifold 𝓘(ℝ, VG) ∞ G] [IsManifold 𝓘(ℝ, VH) ∞ H]
  {n m : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := m) (r := s) F]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  (μ : Measure M) (ν : Measure N)
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := m) ν]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := m) (r := s) F)
  (hσ : σ.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG))
  (hτ : τ.IsSmooth (n := m) (r := s) 𝓘(ℝ, VH))
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (a : G) (x : M) (u v : E x),
      h.pairing (a • x) (σ.linearMap a x u) (σ.linearMap a x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    ∀ (a : H) (x : N) (u v : F x),
      k.pairing (a • x) (τ.linearMap a x u) (τ.linearMap a x v) = k.pairing x u v)
  (hμInvariant : ∀ a : G, Measure.map (fun x : M ↦ a • x) μ = μ)
  (hνInvariant : ∀ a : H, Measure.map (fun y : N ↦ a • y) ν = ν)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Check the same pure smooth tensors, then use their dense linear span in the actual completion.
/-- The product density is invariant and the tensor unitary intertwines the full actions. -/
theorem exists_externalTensorL2Equiv_intertwining :
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
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    letI : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G H
    let θ := externalTensorEquivariantStructure E F σ τ
    let hθ := externalTensorEquivariantStructure_isSmooth E F σ τ hσ hτ
    let l := externalTensorMetric h k
    let hl := externalTensorMetric_invariant E F σ τ h k hInvariant kInvariant
    ∃ hProductInvariant : ∀ a : G × H,
        Measure.map (fun z : M × N ↦ a • z) (μ.prod ν) = μ.prod ν,
      let ρ := h.l2ContRepresentation μ 𝓘(ℝ, VG) σ hσ hInvariant hμInvariant
      let τ' := k.l2ContRepresentation ν 𝓘(ℝ, VH) τ hτ kInvariant hνInvariant
      let ρT := l.l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH) θ hθ hl hProductInvariant
      ∀ (a : G × H) (u : HilbertTensorProduct (h.L2SectionSpace μ) (k.L2SectionSpace ν)),
        externalTensorL2Equiv μ ν h k (hilbertTensorMap (ρ a.1) (τ' a.2) u) =
          ρT a (externalTensorL2Equiv μ ν h k u) := by
  classical
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
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  let : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod G H
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
  let θ := externalTensorEquivariantStructure E F σ τ
  let hθ := externalTensorEquivariantStructure_isSmooth E F σ τ hσ hτ
  let l := externalTensorMetric h k
  let hl := externalTensorMetric_invariant E F σ τ h k hInvariant kInvariant
  have hProductInvariant (a : G × H) :
      Measure.map (fun z : M × N ↦ a • z) (μ.prod ν) = μ.prod ν := by
    let : IsFiniteMeasure ν := isFiniteMeasure_of_smoothPositiveMeasure (n := m) ν
    change Measure.map (Prod.map (fun x : M ↦ a.1 • x) (fun y : N ↦ a.2 • y))
      (μ.prod ν) = μ.prod ν
    rw [← Measure.map_prod_map μ ν (continuous_const_smul a.1).measurable
      (continuous_const_smul a.2).measurable, hμInvariant, hνInvariant]
  refine ⟨hProductInvariant, ?_⟩
  let ρ := h.l2ContRepresentation μ 𝓘(ℝ, VG) σ hσ hInvariant hμInvariant
  let τ' := k.l2ContRepresentation ν 𝓘(ℝ, VH) τ hτ kInvariant hνInvariant
  let ρT := l.l2ContRepresentation (μ.prod ν) 𝓘(ℝ, VG × VH) θ hθ hl hProductInvariant
  let U := externalTensorL2Equiv μ ν h k
  let SE := smoothSections (n := n) (r := r) E
  let SF := smoothSections (n := m) (r := s) F
  let J : SE ⊗[ℂ] SF →ₗ[ℂ] HilbertTensorProduct (h.L2SectionSpace μ) (k.L2SectionSpace ν) :=
    (UniformSpace.Completion.toComplL
      (S := ℂ) (α := h.L2SectionSpace μ ⊗[ℂ] k.L2SectionSpace ν)).toLinearMap.comp
        (TensorProduct.map (h.smoothToL2 μ) (k.smoothToL2 ν))
  have hJ (u : SE) (v : SF) : J (u ⊗ₜ[ℂ] v) =
      (UniformSpace.Completion.toComplL
        (S := ℂ) (α := h.L2SectionSpace μ ⊗[ℂ] k.L2SectionSpace ν))
          (h.smoothToL2 μ u ⊗ₜ[ℂ] k.smoothToL2 ν v) := rfl
  have hJdense : DenseRange J := by
    have hd := dense_span_hilbertTensorProduct
      (Set.range (h.smoothToL2 μ)) (Set.range (k.smoothToL2 ν))
      (h.denseRange_smoothToL2 μ) (k.denseRange_smoothToL2 ν)
    apply hd.mono
    change _ ≤ LinearMap.range J
    apply Submodule.span_le.mpr
    rintro z ⟨⟨u, v⟩, rfl⟩
    obtain ⟨u', hu⟩ := u.property
    obtain ⟨v', hv⟩ := v.property
    refine ⟨(u' : SE) ⊗ₜ[ℂ] (v' : SF), ?_⟩
    rw [hJ, hu, hv]
    rfl
  -- The same original section actions agree on every pointwise smooth pure tensor.
  have hsection (a : G × H) (u : SE) (v : SF) :
      θ.smoothSectionRepresentation 𝓘(ℝ, VG × VH) hθ a (externalTensorSection E F u v) =
        externalTensorSection E F
          (σ.smoothSectionRepresentation 𝓘(ℝ, VG) hσ a.1 u)
          (τ.smoothSectionRepresentation 𝓘(ℝ, VH) hτ a.2 v) := by
    apply Subtype.ext
    exact externalTensorEquivariantStructure_sectionLinearMap E F σ τ a u.val v.val
  dsimp only
  intro a u
  let A := U.toLinearIsometry.toContinuousLinearMap.comp
    (hilbertTensorMap (ρ a.1) (τ' a.2))
  let B := (ρT a).comp U.toLinearIsometry.toContinuousLinearMap
  have hAB : (A : _ → _) = B := by
    apply hJdense.equalizer A.continuous B.continuous
    funext w
    change A (J w) = B (J w)
    induction w using TensorProduct.inductionOn with
    | tmul v w =>
      have hT (x : h.L2SectionSpace μ) (y : k.L2SectionSpace ν) :
          hilbertTensorMap (ρ a.1) (τ' a.2)
              ((UniformSpace.Completion.toComplL (S := ℂ)) (x ⊗ₜ[ℂ] y)) =
            (UniformSpace.Completion.toComplL (S := ℂ))
              (ρ a.1 x ⊗ₜ[ℂ] τ' a.2 y) := by
        change (TensorProduct.mapL (ρ a.1) (τ' a.2)).completion
          ((x ⊗ₜ[ℂ] y) : UniformSpace.Completion _) = _
        rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
        rfl
      change U (hilbertTensorMap (ρ a.1) (τ' a.2) (J (v ⊗ₜ[ℂ] w))) = ρT a (U (J (v ⊗ₜ[ℂ] w)))
      rw [hJ, hT]
      have hρv : ρ a.1 (h.smoothToL2 μ v) =
          h.smoothToL2 μ (σ.smoothSectionRepresentation 𝓘(ℝ, VG) hσ a.1 v) :=
        h.l2IsometryRepresentation_smoothToL2 μ 𝓘(ℝ, VG) σ hσ hInvariant hμInvariant a.1 v
      have hτw : τ' a.2 (k.smoothToL2 ν w) =
          k.smoothToL2 ν (τ.smoothSectionRepresentation 𝓘(ℝ, VH) hτ a.2 w) :=
        k.l2IsometryRepresentation_smoothToL2 ν 𝓘(ℝ, VH) τ hτ kInvariant hνInvariant a.2 w
      have hρT (s : smoothSections (externalTensorFiber E F)) :
          ρT a (l.smoothToL2 (μ.prod ν) s) =
            l.smoothToL2 (μ.prod ν) (θ.smoothSectionRepresentation 𝓘(ℝ, VG × VH) hθ a s) :=
        l.l2IsometryRepresentation_smoothToL2 (μ.prod ν) 𝓘(ℝ, VG × VH) θ hθ hl
          hProductInvariant a s
      rw [hρv, hτw]
      dsimp only [U]
      rw [externalTensorL2Equiv_smooth, externalTensorL2Equiv_smooth,
        hρT, hsection]
    | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw
  exact congrFun hAB u

end AtiyahSinger

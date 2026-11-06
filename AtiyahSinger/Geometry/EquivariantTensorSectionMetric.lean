/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Geometry.EquivariantExternalTensor

/-!
# Tensor sections and invariant native tensor metrics

Public module ID: M1211.

Both formulas use the existing external tensor vectors, topology and native
atlas. The section action is checked at the actual moved point, preserving
its dependent fiber transport. Metric invariance extends from pure tensors
by sesquilinearity on the two original algebraic tensor factors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40

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


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original section action respects the pointwise tensor of the two given sections. -/
theorem externalTensorEquivariantStructure_sectionLinearMap
    (a : G × H) (u : ∀ x : M, E x) (v : ∀ y : N, F y) :
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    (externalTensorEquivariantStructure E F σ τ).sectionLinearMap a
        (fun z ↦ u z.1 ⊗ₜ[ℂ] v z.2) =
      (fun z : M × N ↦ σ.sectionLinearMap a.1 u z.1 ⊗ₜ[ℂ]
        τ.sectionLinearMap a.2 v z.2) := by
  let : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
  let θ := externalTensorEquivariantStructure E F σ τ
  funext z
  obtain ⟨x, rfl⟩ := (MulAction.surjective a) z
  rw [θ.sectionLinearMap_smul]
  change TensorProduct.map (σ.linearMap a.1 x.1) (τ.linearMap a.2 x.2)
      (u x.1 ⊗ₜ[ℂ] v x.2) =
    σ.sectionLinearMap a.1 u (a.1 • x.1) ⊗ₜ[ℂ] τ.sectionLinearMap a.2 v (a.2 • x.2)
  rw [σ.sectionLinearMap_smul, τ.sectionLinearMap_smul, TensorProduct.map_tmul]

variable {n m : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := m) (r := s) F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor of the specified invariant metrics is invariant under the original tensor action. -/
theorem externalTensorMetric_invariant
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := m) (r := s) F)
    (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (a : G) (x : M) (u v : E x),
        h.pairing (a • x) (σ.linearMap a x u) (σ.linearMap a x v) = h.pairing x u v)
    (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
      ∀ (a : H) (x : N) (u v : F x),
        k.pairing (a • x) (τ.linearMap a x u) (τ.linearMap a x v) = k.pairing x u v) :
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
    let θ := externalTensorEquivariantStructure E F σ τ
    let l := externalTensorMetric h k
    ∀ (a : G × H) (z : M × N) (u v : externalTensorFiber E F z),
      l.pairing (a • z) (θ.linearMap a z u) (θ.linearMap a z v) = l.pairing z u v := by
  let : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
  let θ := externalTensorEquivariantStructure E F σ τ
  let l := externalTensorMetric h k
  have haddLeft (z : M × N) (u v w : externalTensorFiber E F z) :
      l.pairing z (u + v) w = l.pairing z u w + l.pairing z v w := (l.toCore z).add_left u v w
  have haddRight (z : M × N) (u v w : externalTensorFiber E F z) :
      l.pairing z u (v + w) = l.pairing z u v + l.pairing z u w := by
    let := l.toCore z
    exact InnerProductSpace.Core.inner_add_right u v w
  dsimp only
  intro a z u v
  change l.pairing (a • z) (θ.linearMap a z u) (θ.linearMap a z v) = l.pairing z u v
  -- Pure tensors carry exactly the original factor pairings and factor action maps.
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | tmul x' y' =>
      change l.pairing (a • z)
          (TensorProduct.map (σ.linearMap a.1 z.1) (τ.linearMap a.2 z.2) (x ⊗ₜ[ℂ] y))
          (TensorProduct.map (σ.linearMap a.1 z.1) (τ.linearMap a.2 z.2) (x' ⊗ₜ[ℂ] y')) = _
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
        externalTensorMetric_pairing, externalTensorMetric_pairing]
      apply congrArg₂ (fun a b : ℂ ↦ a * b)
      · exact hInvariant a.1 z.1 x x'
      · exact kInvariant a.2 z.2 y y'
    | add v w hv hw => rw [map_add, haddRight, haddRight, hv, hw]
  | add u w hu hw => rw [map_add, haddLeft, haddLeft, hu, hw]

end AtiyahSinger

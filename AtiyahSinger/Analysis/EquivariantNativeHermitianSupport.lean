/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantFullSymbolProduct
public import AtiyahSinger.Geometry.CotangentGradedSumIso
public import AtiyahSinger.Geometry.EquivariantCotangentGradedSumIso
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality
public import AtiyahSinger.Topology.EquivariantSupportTransport

/-!
# The original external product in the specified native graded bundles

Public module ID: M0540.

Pull the actual full Hermitian product through the original cotangent product
homeomorphism, then conjugate by the same given smooth graded identifications.
The resulting native support triple has the exact uncut matrix and the original
independent-group external product class, with all original actions retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 50
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {VG VH G H : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [IsManifold 𝓘(ℝ, VG) ∞ G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [IsManifold 𝓘(ℝ, VH) ∞ H]
  {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [MulAction G M] [ContinuousSMul G M] [MulAction H N] [ContinuousSMul H N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N]
  (E₀ E₁ : SmoothFiniteComplexBundle (n := n) M)
  (F₀ F₁ : SmoothFiniteComplexBundle (n := m) N)
  (σ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    EquivariantStructure G E₀.Fiber)
  (σ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    EquivariantStructure G E₁.Fiber)
  (τ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    EquivariantStructure H F₀.Fiber)
  (τ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    EquivariantStructure H F₁.Fiber)


variable [CompactSpace G] [CompactSpace H]
  [T2Space M] [CompactSpace M] [T2Space N] [CompactSpace N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum

set_option maxHeartbeats 9000000 in
-- Compare the original nested pullback, tensor and native sum models without changing witnesses.
/-- The exact native uncut Hermitian boundary has the original cotangent product class. -/
theorem exists_equivariantNativeHermitianSupport_of_tail
    (p₀ : homogeneousGlobalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank)
      E₀.Fiber E₁.Fiber 1)
    (q₀ : homogeneousGlobalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank)
      F₀.Fiber F₁.Fiber 1)
    (hp₀ : IsEllipticGlobalSymbol E₀.Fiber E₁.Fiber p₀.val)
    (hq₀ : IsEllipticGlobalSymbol F₀.Fiber F₁.Fiber q₀.val)
    (hp₀Eq : ∀ (z : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ z p₀.val x ξ = p₀.val x ξ)
    (hq₀Eq : ∀ (z : H) (x : N) (ξ : CotangentFiber (n := m) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ z q₀.val x ξ = q₀.val x ξ)
    (p : globalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber 1)
    (pi : globalSymbolSpace (n := n) (r := E₁.rank) (q := E₀.rank) E₁.Fiber E₀.Fiber 1)
    (q : globalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber 1)
    (qi : globalSymbolSpace (n := m) (r := F₁.rank) (q := F₀.rank) F₁.Fiber F₀.Fiber 1)
    (hp : ∀ z : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ z p.val = p.val)
    (hpi : ∀ z : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₁ σ₀ z pi.val = pi.val)
    (hq : ∀ z : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ z q.val = q.val)
    (hqi : ∀ z : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₁ τ₀ z qi.val = qi.val)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (gInv : ∀ (a : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (a • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M)
        𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ a) ⟨x, ξ⟩).snd = g.length x ξ)
    (kInv : ∀ (a : H) (x : N) (ξ : CotangentFiber (n := m) x),
      k.length (a • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := N)
        𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a) ⟨x, ξ⟩).snd = k.length x ξ)
    (R₁ R₂ : ℝ) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hpTail : ∀ x ξ, R₁ ≤ g.length x ξ → p.val x ξ = p₀.val x ξ)
    (hqTail : ∀ x ξ, R₂ ≤ k.length x ξ → q.val x ξ = q₀.val x ξ)
    (h₀ : SmoothHermitianMetric (n := n) (r := E₀.rank) E₀.Fiber)
    (h₁ : SmoothHermitianMetric (n := n) (r := E₁.rank) E₁.Fiber)
    (k₀ : SmoothHermitianMetric (n := m) (r := F₀.rank) F₀.Fiber)
    (k₁ : SmoothHermitianMetric (n := m) (r := F₁.rank) F₁.Fiber)
    (hpAdj : ∀ x ξ u v, h₁.pairing x (p.val x ξ u) v = h₀.pairing x u (pi.val x ξ v))
    (hqAdj : ∀ x ξ u v, k₁.pairing x (q.val x ξ u) v = k₀.pairing x u (qi.val x ξ v)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    letI : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G H
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
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    letI := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    letI := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H)
      (M := M × N) 𝓘(ℝ, VG × VH)
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
    letI : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorTopology (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorTopology (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorTopology (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
      E₁.Fiber F₀.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorTopology (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
      E₀.Fiber F₁.Fiber
    ∀ (S T : SmoothFiniteComplexBundle (n := n + m) (M × N))
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
        EquivariantStructure (G × H) S.Fiber)
      (τ : letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
        EquivariantStructure (G × H) T.Fiber)
      (e : ∀ x : M × N, ((externalTensorFiber E₀.Fiber F₀.Fiber x) ×
        (externalTensorFiber E₁.Fiber F₁.Fiber x)) ≃ₗ[ℂ] S.Fiber x)
      (f : ∀ x : M × N, ((externalTensorFiber E₁.Fiber F₀.Fiber x) ×
        (externalTensorFiber E₀.Fiber F₁.Fiber x)) ≃ₗ[ℂ] T.Fiber x)
      (_he₀ : IsSmoothBundleMap (n := n + m) (r := E₀.rank * F₀.rank) (q := S.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ
          (externalTensorFiber E₀.Fiber F₀.Fiber x)
          (externalTensorFiber E₁.Fiber F₁.Fiber x))))
      (_he₁ : IsSmoothBundleMap (n := n + m) (r := E₁.rank * F₁.rank) (q := S.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ
          (externalTensorFiber E₀.Fiber F₀.Fiber x)
          (externalTensorFiber E₁.Fiber F₁.Fiber x))))
      (_hf₀ : IsSmoothBundleMap (n := n + m) (r := E₁.rank * F₀.rank) (q := T.rank)
        (fun x ↦ (f x).toLinearMap.comp (LinearMap.inl ℂ
          (externalTensorFiber E₁.Fiber F₀.Fiber x)
          (externalTensorFiber E₀.Fiber F₁.Fiber x))))
      (_hf₁ : IsSmoothBundleMap (n := n + m) (r := E₀.rank * F₁.rank) (q := T.rank)
        (fun x ↦ (f x).toLinearMap.comp (LinearMap.inr ℂ
          (externalTensorFiber E₁.Fiber F₀.Fiber x)
          (externalTensorFiber E₀.Fiber F₁.Fiber x)))),
    letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
    (∀ (z : G × H) (x : M × N) v, σ.linearMap z x (e x v) = e (z • x)
      (TensorProduct.map (σ₀.linearMap z.1 x.1) (τ₀.linearMap z.2 x.2) v.1,
        TensorProduct.map (σ₁.linearMap z.1 x.1) (τ₁.linearMap z.2 x.2) v.2)) →
    (∀ (z : G × H) (x : M × N) v, τ.linearMap z x (f x v) = f (z • x)
      (TensorProduct.map (σ₁.linearMap z.1 x.1) (τ₀.linearMap z.2 x.2) v.1,
        TensorProduct.map (σ₀.linearMap z.1 x.1) (τ₁.linearMap z.2 x.2) v.2)) →
    let pr := cotangentProjection (n := n + m) (M := M × N)
    let c : C(CotangentTotalSpace (n := n + m) (M := M × N),
        CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
      ⟨cotangentProductHomeomorph (n := n) (m := m) M N,
        (cotangentProductHomeomorph (n := n) (m := m) M N).continuous⟩
    let hc := cotangentProductHomeomorph_equivariant (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    let cp := (cotangentProductHomeomorph (n := n) (m := m) M N).isProperMap
    let c₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let l (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
      (ξ.comp c₀.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    let r (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
      (ξ.comp c₀.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    ∃ d : CompactSupportTriple (pr *ᵖ S.Fiber) (pr *ᵖ T.Fiber),
      ∃ hd : d.IsEquivariant (σ.pullback pr (fun _ _ ↦ rfl))
          (τ.pullback pr (fun _ _ ↦ rfl)),
        (∀ (z : (d.controlᶜ : Set (CotangentTotalSpace (n := n + m) (M := M × N)))) v,
          d.boundary.linearEquiv z (e z.val.proj v) = f z.val.proj
            (reciprocalTensorSymbol (p.val z.val.proj.1 (l z.val.snd)).toLinearMap
              (pi.val z.val.proj.1 (l z.val.snd)).toLinearMap
              (q.val z.val.proj.2 (r z.val.snd)).toLinearMap
              (qi.val z.val.proj.2 (r z.val.snd)).toLinearMap v)) ∧
        (EquivariantSupportBundleTriple.ofBoundary
          (FiniteBundle.ofFamily (pr *ᵖ S.Fiber)) (FiniteBundle.ofFamily (pr *ᵖ T.Fiber)) d
          (σ.pullback pr (fun _ _ ↦ rfl)) (τ.pullback pr (fun _ _ ↦ rfl)) hd).kZeroClass =
            equivariantSupportTripleKZeroPullback c hc cp
              (equivariantSupportKZeroDifferentGroupExternalProduct
                (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σ₀ σ₁ 1 p₀ hp₀ hp₀Eq)
                (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VH) τ₀ τ₁ 1 q₀ hq₀ hq₀Eq)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
  let : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod G H
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
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  let := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  let := contMDiffSMul_smoothCotangent (n := n + m) (G := G × H)
    (M := M × N) 𝓘(ℝ, VG × VH)
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
  let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorTopology (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorTopology (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorTopology (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₀.rank)
    E₁.Fiber F₀.Fiber
  let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorTopology (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₁.rank)
    E₀.Fiber F₁.Fiber
  dsimp only
  intro S T σ τ e f he₀ he₁ hf₀ hf₁
  let := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
  intro he hf
  let pr := cotangentProjection (n := n + m) (M := M × N)
  let c₀ := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let l (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
    (ξ.comp c₀.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let r (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
    (ξ.comp c₀.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let c : C(CotangentTotalSpace (n := n + m) (M := M × N),
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
    ⟨cotangentProductHomeomorph (n := n) (m := m) M N,
      (cotangentProductHomeomorph (n := n) (m := m) M N).continuous⟩
  let hc := cotangentProductHomeomorph_equivariant (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  let cp := (cotangentProductHomeomorph (n := n) (m := m) M N).isProperMap
  -- Expose the exact coordinate formula of the same homeomorphism, including its base points.
  let c' : C(CotangentTotalSpace (n := n + m) (M := M × N),
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
    { toFun z := (⟨z.proj.1, l z.snd⟩, ⟨z.proj.2, r z.snd⟩)
      continuous_toFun := c.continuous.congr cotangentProductHomeomorph_apply }
  have hcMap : c = c' := ContinuousMap.ext cotangentProductHomeomorph_apply
  let μProd : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N)) := Prod.mulAction
  have hc' : ∀ (z : G × H)
      (x : CotangentTotalSpace (n := n + m) (M := M × N)),
      c' (z • x) = @SMul.smul (G × H) (CotangentTotalSpace (n := n) (M := M) ×
        CotangentTotalSpace (n := m) (M := N)) μProd.toSMul z (c' x) := by
    rw [← hcMap]
    exact hc
  have cp' : IsProperMap c' := by
    rw [← hcMap]
    exact cp
  let pM := cotangentProjection (n := n) (M := M)
  let pN := cotangentProjection (n := m) (M := N)
  let A₀ := FiniteBundle.ofFamily (pM *ᵖ E₀.Fiber)
  let A₁ := FiniteBundle.ofFamily (pM *ᵖ E₁.Fiber)
  let B₀ := FiniteBundle.ofFamily (pN *ᵖ F₀.Fiber)
  let B₁ := FiniteBundle.ofFamily (pN *ᵖ F₁.Fiber)
  let fM : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := n) (M := M)) :=
    ContinuousMap.fst
  let fN : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := m) (M := N)) :=
    ContinuousMap.snd
  let := ((A₀.pullback fM).tensor (B₀.pullback fN)).totalTopology
  let := ((A₁.pullback fM).tensor (B₁.pullback fN)).totalTopology
  let := ((A₁.pullback fM).tensor (B₀.pullback fN)).totalTopology
  let := ((A₀.pullback fM).tensor (B₁.pullback fN)).totalTopology
  let S₀ := ((A₀.pullback fM).tensor (B₀.pullback fN)).sum
    ((A₁.pullback fM).tensor (B₁.pullback fN))
  let T₀ := ((A₁.pullback fM).tensor (B₀.pullback fN)).sum
    ((A₀.pullback fM).tensor (B₁.pullback fN))
  let := S₀.totalTopology
  let := T₀.totalTopology
  let ρ₀ := (σ₀.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
  let ρ₁ := (σ₁.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
  let κ₀ := (τ₀.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
  let κ₁ := (τ₁.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
  let ρS := ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor
    (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
      ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
  let ρT := ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor
    (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
      ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
  obtain ⟨D, _hDControl, hD, hDFormula, hDClass⟩ :=
    exists_equivariantFullSymbolProduct_of_tail E₀ E₁ F₀ F₁ σ₀ σ₁ τ₀ τ₁
      p₀ q₀ hp₀ hq₀ hp₀Eq hq₀Eq p pi q qi hp hpi hq hqi g k gInv kInv
      R₁ R₂ hR₁ hR₂ hpTail hqTail h₀ h₁ k₀ k₁ hpAdj hqAdj
  -- Both prescribed graded sums use the original tensor and pullback bundle topologies.
  have hU := exists_cotangentGradedSumIso E₀ E₁ F₀ F₁ S e he₀ he₁
  have hV := exists_cotangentGradedSumIso E₁ E₀ F₀ F₁ T f hf₀ hf₁
  change ∃ U : Iso (c *ᵖ S₀.Fiber) (pr *ᵖ S.Fiber),
    ∀ z w, (⟨z.proj, U.linearEquiv z w⟩ : TotalSpace Unit S.Fiber) =
      ⟨((c z).1.proj, (c z).2.proj), e ((c z).1.proj, (c z).2.proj) w⟩ at hU
  change ∃ V : Iso (c *ᵖ T₀.Fiber) (pr *ᵖ T.Fiber),
    ∀ z w, (⟨z.proj, V.linearEquiv z w⟩ : TotalSpace Unit T.Fiber) =
      ⟨((c z).1.proj, (c z).2.proj), f ((c z).1.proj, (c z).2.proj) w⟩ at hV
  rw [hcMap] at hU hV
  obtain ⟨U, hU⟩ := hU
  obtain ⟨V, hV⟩ := hV
  have hUgRaw := cotangentGradedSumIso_isEquivariant (VG := VG) (VH := VH)
    E₀ E₁ F₀ F₁ σ₀ σ₁ τ₀ τ₁ S σ e he
  have hVgRaw := cotangentGradedSumIso_isEquivariant (VG := VG) (VH := VH)
    E₁ E₀ F₀ F₁ σ₁ σ₀ τ₀ τ₁ T τ f hf
  have hUg : ∀ (hc : ∀ (z : G × H)
      (x : CotangentTotalSpace (n := n + m) (M := M × N)),
      c (z • x) = @SMul.smul (G × H) (CotangentTotalSpace (n := n) (M := M) ×
        CotangentTotalSpace (n := m) (M := N)) μProd.toSMul z (c x)),
      ∀ U : Iso (c *ᵖ S₀.Fiber) (pr *ᵖ S.Fiber),
    (∀ z w, (⟨z.proj, U.linearEquiv z w⟩ : TotalSpace Unit S.Fiber) =
      ⟨((c z).1.proj, (c z).2.proj), e ((c z).1.proj, (c z).2.proj) w⟩) →
      U.IsEquivariant (ρS.pullback c hc) (σ.pullback pr (fun _ _ ↦ rfl)) := fun _ ↦ hUgRaw
  have hVg : ∀ (hc : ∀ (z : G × H)
      (x : CotangentTotalSpace (n := n + m) (M := M × N)),
      c (z • x) = @SMul.smul (G × H) (CotangentTotalSpace (n := n) (M := M) ×
        CotangentTotalSpace (n := m) (M := N)) μProd.toSMul z (c x)),
      ∀ V : Iso (c *ᵖ T₀.Fiber) (pr *ᵖ T.Fiber),
    (∀ z w, (⟨z.proj, V.linearEquiv z w⟩ : TotalSpace Unit T.Fiber) =
      ⟨((c z).1.proj, (c z).2.proj), f ((c z).1.proj, (c z).2.proj) w⟩) →
      V.IsEquivariant (ρT.pullback c hc) (τ.pullback pr (fun _ _ ↦ rfl)) := fun _ ↦ hVgRaw
  rw [hcMap] at hUg hVg
  let A := EquivariantSupportBundleTriple.ofBoundary S₀ T₀ D ρS ρT hD
  let A' := A.pullback c' hc' cp'
  obtain ⟨hd, hdClass⟩ := exists_equivariantSupportTransport A'
    (FiniteBundle.ofFamily (pr *ᵖ S.Fiber)) (FiniteBundle.ofFamily (pr *ᵖ T.Fiber))
    (σ.pullback pr (fun _ _ ↦ rfl)) (τ.pullback pr (fun _ _ ↦ rfl))
    U V (hUg hc' U hU) (hVg hc' V hV)
  let d := A'.1.datum.congr U V
  refine ⟨d, hd, ?_, ?_⟩
  · intro z v
    have hu (w) : U.linearEquiv z.val w = e z.val.proj w :=
      TotalSpace.mk_injective (F := Unit) z.val.proj (hU z.val w)
    have hv (w) : V.linearEquiv z.val w = f z.val.proj w :=
      TotalSpace.mk_injective (F := Unit) z.val.proj (hV z.val w)
    have hvinv : (U.linearEquiv z.val).symm (e z.val.proj v) = v := by
      rw [← hu v, LinearEquiv.symm_apply_apply]
    rw [CompactSupportTriple.congr_apply]
    change V.linearEquiv z.val ((D.pullback c' cp').boundary.linearEquiv z
      ((U.linearEquiv z.val).symm (e z.val.proj v))) = _
    apply (congrArg (fun w ↦ V.linearEquiv z.val
      ((D.pullback c' cp').boundary.linearEquiv z w)) hvinv).trans
    have hPB := RelativeTriple.pullback_apply D.boundary c' z v
    apply (congrArg (V.linearEquiv z.val) hPB).trans
    exact (hv _).trans
      (congrArg (f z.val.proj) (LinearMap.congr_fun (hDFormula ⟨c' z.val, z.property⟩) v))
  · -- The exact conjugation and the original proper pullback preserve the prescribed class.
    apply hdClass.trans
    change A'.kZeroClass = equivariantSupportTripleKZeroPullback c hc cp _
    rw [← equivariantSupportTripleKZeroPullback_apply c' hc' cp' A]
    have hclass := congrArg (equivariantSupportTripleKZeroPullback c' hc' cp') hDClass
    apply hclass.trans
    congr 2
    exact hcMap.symm

end AtiyahSinger

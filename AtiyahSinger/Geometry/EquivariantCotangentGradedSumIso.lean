/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentProduct
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.EquivariantBundleTensor
public import AtiyahSinger.Topology.EquivariantPullbackMap
public import AtiyahSinger.Topology.EquivariantRestriction
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# Equivariance of the specified native cotangent graded sum

Public module ID: M1183.

The exact total-vector formula of the native sum isomorphism transports the
original four factor actions. Source actions are the original cotangent
projection pullbacks, independent-group restrictions, external pullbacks,
and tensor sum. The target is the original native action pulled to its
cotangent space. No new equivariant structure is substituted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum
  isFiniteRank_pullback

set_option maxSynthPendingDepth 50
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


set_option maxHeartbeats 2400000 in
-- Normalize the specified nested pullback, restricted, tensor and sum action instances together.
set_option maxRecDepth 4096 in
/-- The specified native sum isomorphism intertwines the original cotangent factor actions. -/
theorem cotangentGradedSumIso_isEquivariant :
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
    ∀ (S : SmoothFiniteComplexBundle (n := n + m) (M × N))
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
        EquivariantStructure (G × H) S.Fiber)
      (e : ∀ x : M × N, ((E₀.Fiber x.1 ⊗[ℂ] F₀.Fiber x.2) ×
        (E₁.Fiber x.1 ⊗[ℂ] F₁.Fiber x.2)) ≃ₗ[ℂ] S.Fiber x),
    letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
    (∀ (g : G × H) (x : M × N) v, σ.linearMap g x (e x v) = e (g • x)
      ((TensorProduct.map (σ₀.linearMap g.1 x.1) (τ₀.linearMap g.2 x.2) v.1,
        TensorProduct.map (σ₁.linearMap g.1 x.1) (τ₁.linearMap g.2 x.2) v.2))) →
    let pM := cotangentProjection (n := n) (M := M)
    let pN := cotangentProjection (n := m) (M := N)
    let p := cotangentProjection (n := n + m) (M := M × N)
    let c : C(CotangentTotalSpace (n := n + m) (M := M × N),
        CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
      ⟨cotangentProductHomeomorph (n := n) (m := m) M N,
        (cotangentProductHomeomorph (n := n) (m := m) M N).continuous⟩
    let hc := cotangentProductHomeomorph_equivariant (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
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
    let A := ((A₀.pullback fM).tensor (B₀.pullback fN)).sum
      ((A₁.pullback fM).tensor (B₁.pullback fN))
    letI := ((A₀.pullback fM).tensor (B₀.pullback fN)).totalTopology
    letI := ((A₁.pullback fM).tensor (B₁.pullback fN)).totalTopology
    letI := A.totalTopology
    let ρ₀ := (σ₀.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
    let ρ₁ := (σ₁.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
    let κ₀ := (τ₀.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
    let κ₁ := (τ₁.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
    let ρ := ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor
      (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
        ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
    ∀ U : Iso (c *ᵖ A.Fiber) (p *ᵖ S.Fiber),
      (∀ z w, (⟨z.proj, U.linearEquiv z w⟩ : TotalSpace Unit S.Fiber) =
        ⟨((c z).1.proj, (c z).2.proj), e ((c z).1.proj, (c z).2.proj) w⟩) →
      U.IsEquivariant (ρ.pullback c hc) (σ.pullback p (fun _ _ ↦ rfl)) := by
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
  dsimp only
  intro S σ e
  let := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  intro he U hU
  let pM := cotangentProjection (n := n) (M := M)
  let pN := cotangentProjection (n := m) (M := N)
  let p := cotangentProjection (n := n + m) (M := M × N)
  let c : C(CotangentTotalSpace (n := n + m) (M := M × N),
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
    ⟨cotangentProductHomeomorph (n := n) (m := m) M N,
      (cotangentProductHomeomorph (n := n) (m := m) M N).continuous⟩
  let hc := cotangentProductHomeomorph_equivariant (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
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
  let A := ((A₀.pullback fM).tensor (B₀.pullback fN)).sum
    ((A₁.pullback fM).tensor (B₁.pullback fN))
  let := ((A₀.pullback fM).tensor (B₀.pullback fN)).totalTopology
  let := ((A₁.pullback fM).tensor (B₁.pullback fN)).totalTopology
  let := A.totalTopology
  let ρ₀ := (σ₀.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
  let ρ₁ := (σ₁.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
  let κ₀ := (τ₀.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
  let κ₁ := (τ₁.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
  let ρ := ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor
    (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
      ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
  -- Lift the source action to the original native total space via the same e.
  refine Iso.isEquivariant_of_lift ρ σ c p hc (fun _ _ ↦ rfl) U
    (fun w ↦ ⟨(w.proj.1.proj, w.proj.2.proj),
      e (w.proj.1.proj, w.proj.2.proj) w.snd⟩) ?_ hU
  intro g w
  apply congrArg (TotalSpace.mk (g • (w.proj.1.proj, w.proj.2.proj)))
  exact (he g (w.proj.1.proj, w.proj.2.proj) w.snd).symm

end AtiyahSinger

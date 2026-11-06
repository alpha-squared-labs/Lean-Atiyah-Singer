/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantGradedSymbolOrbit
public import AtiyahSinger.Geometry.ProductCovectorCoordinates

/-!
# Weighted graded symbols under the original product cotangent action

Public module ID: M0556.

The actual native cotangent splitting transports the four fixed full factor
symbols into the weighted graded orbit formula. All frequencies are included,
so this comparison applies to the invariant smooth full symbols chosen before
forming the original cutoff PDO blocks. Native source and target sum actions
are passed with their exact tensor coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

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

set_option maxHeartbeats 1600000 in
-- The exact product cotangent homeomorphism supplies the four actual factor squares.
/-- Product conjugation moves only the scalar weights of the original four fixed factor symbols. -/
theorem equivariantGlobalSymbolLinearMap_product_weighted_reciprocalTensor
    (p : GlobalSymbolFunction (n := n) E₀.Fiber E₁.Fiber)
    (pi : GlobalSymbolFunction (n := n) E₁.Fiber E₀.Fiber)
    (q : GlobalSymbolFunction (n := m) F₀.Fiber F₁.Fiber)
    (qi : GlobalSymbolFunction (n := m) F₁.Fiber F₀.Fiber)
    (hp : ∀ g : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ g p = p)
    (hpi : ∀ g : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₁ σ₀ g pi = pi)
    (hq : ∀ g : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ g q = q)
    (hqi : ∀ g : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₁ τ₀ g qi = qi) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    let i₀ (g : G × H) (x : M × N) :=
      LinearEquiv.ofBijective (σ₀.linearMap g.1 x.1) (σ₀.linearMap_bijective g.1 x.1)
    let i₁ (g : G × H) (x : M × N) :=
      LinearEquiv.ofBijective (σ₁.linearMap g.1 x.1) (σ₁.linearMap_bijective g.1 x.1)
    let j₀ (g : G × H) (x : M × N) :=
      LinearEquiv.ofBijective (τ₀.linearMap g.2 x.2) (τ₀.linearMap_bijective g.2 x.2)
    let j₁ (g : G × H) (x : M × N) :=
      LinearEquiv.ofBijective (τ₁.linearMap g.2 x.2) (τ₁.linearMap_bijective g.2 x.2)
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
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let l (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
      (ξ.comp c.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    let r (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
      (ξ.comp c.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    ∀ (S T : SmoothFiniteComplexBundle (n := n + m) (M × N))
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
        EquivariantStructure (G × H) S.Fiber)
      (τ : letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
        EquivariantStructure (G × H) T.Fiber)
      (e : ∀ x : M × N, ((E₀.Fiber x.1 ⊗[ℂ] F₀.Fiber x.2) ×
        (E₁.Fiber x.1 ⊗[ℂ] F₁.Fiber x.2)) ≃ₗ[ℂ] S.Fiber x)
      (f : ∀ x : M × N, ((E₁.Fiber x.1 ⊗[ℂ] F₀.Fiber x.2) ×
        (E₀.Fiber x.1 ⊗[ℂ] F₁.Fiber x.2)) ≃ₗ[ℂ] T.Fiber x),
      (letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
       ∀ g x v, σ.linearMap g x (e x v) = e (g • x)
        (((TensorProduct.congr (i₀ g x) (j₀ g x)).prodCongr
          (TensorProduct.congr (i₁ g x) (j₁ g x))) v)) →
      (letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
       ∀ g x v, τ.linearMap g x (f x v) = f (g • x)
        (((TensorProduct.congr (i₁ g x) (j₀ g x)).prodCongr
          (TensorProduct.congr (i₀ g x) (j₁ g x))) v)) →
      ∀ (a : GlobalSymbolFunction (n := n + m) S.Fiber T.Fiber)
        (α β : ∀ x : M × N, CotangentFiber (n := n + m) x → ℝ),
      (∀ x ξ v, a x ξ (e x v) = f x (reciprocalTensorSymbol
        ((α x ξ : ℂ) • (p x.1 (l ξ)).toLinearMap)
        ((α x ξ : ℂ) • (pi x.1 (l ξ)).toLinearMap)
        ((β x ξ : ℂ) • (q x.2 (r ξ)).toLinearMap)
        ((β x ξ : ℂ) • (qi x.2 (r ξ)).toLinearMap) v)) →
      ∀ g x ξ v,
        let η := (cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
          𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ g).symm ⟨x, ξ⟩).snd
        equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ g a x ξ (e x v) =
          f x (reciprocalTensorSymbol
            ((α (g⁻¹ • x) η : ℂ) • (p x.1 (l ξ)).toLinearMap)
            ((α (g⁻¹ • x) η : ℂ) • (pi x.1 (l ξ)).toLinearMap)
            ((β (g⁻¹ • x) η : ℂ) • (q x.2 (r ξ)).toLinearMap)
            ((β (g⁻¹ • x) η : ℂ) • (qi x.2 (r ξ)).toLinearMap) v) := by
  let := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let i₀ (g : G × H) (x : M × N) :=
    LinearEquiv.ofBijective (σ₀.linearMap g.1 x.1) (σ₀.linearMap_bijective g.1 x.1)
  let i₁ (g : G × H) (x : M × N) :=
    LinearEquiv.ofBijective (σ₁.linearMap g.1 x.1) (σ₁.linearMap_bijective g.1 x.1)
  let j₀ (g : G × H) (x : M × N) :=
    LinearEquiv.ofBijective (τ₀.linearMap g.2 x.2) (τ₀.linearMap_bijective g.2 x.2)
  let j₁ (g : G × H) (x : M × N) :=
    LinearEquiv.ofBijective (τ₁.linearMap g.2 x.2) (τ₁.linearMap_bijective g.2 x.2)
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
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let l (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
    (ξ.comp c.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let r (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
    (ξ.comp c.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod G H
  dsimp only
  intro S T σ τ e f he hf a α β ha
  have hpc := (equivariantGlobalSymbolLinearMap_eq_iff_forall 𝓘(ℝ, VG) σ₀ σ₁ p).mp
    (fun g x ξ ↦ congrArg (fun b : GlobalSymbolFunction E₀.Fiber E₁.Fiber ↦ b x ξ) (hp g))
  have hpic := (equivariantGlobalSymbolLinearMap_eq_iff_forall 𝓘(ℝ, VG) σ₁ σ₀ pi).mp
    (fun g x ξ ↦ congrArg (fun b : GlobalSymbolFunction E₁.Fiber E₀.Fiber ↦ b x ξ) (hpi g))
  have hqc := (equivariantGlobalSymbolLinearMap_eq_iff_forall 𝓘(ℝ, VH) τ₀ τ₁ q).mp
    (fun g x ξ ↦ congrArg (fun b : GlobalSymbolFunction F₀.Fiber F₁.Fiber ↦ b x ξ) (hq g))
  have hqic := (equivariantGlobalSymbolLinearMap_eq_iff_forall 𝓘(ℝ, VH) τ₁ τ₀ qi).mp
    (fun g x ξ ↦ congrArg (fun b : GlobalSymbolFunction F₁.Fiber F₀.Fiber ↦ b x ξ) (hqi g))
  apply equivariantGlobalSymbolLinearMap_weighted_reciprocalTensor 𝓘(ℝ, VG × VH)
    S T σ τ i₀ i₁ j₀ j₁ e f he hf
    (fun x ξ ↦ (p x.1 (l ξ)).toLinearMap) (fun x ξ ↦ (pi x.1 (l ξ)).toLinearMap)
    (fun x ξ ↦ (q x.2 (r ξ)).toLinearMap) (fun x ξ ↦ (qi x.2 (r ξ)).toLinearMap)
    _ a α β ha
  intro g x ξ
  let η := (cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
    𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ g) ⟨x, ξ⟩).snd
  have hsplit :
      l η = (cotangentDiffeomorphMap (Diffeomorph.smul (M := M)
        𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g.1) ⟨x.1, l ξ⟩).snd ∧
      r η = (cotangentDiffeomorphMap (Diffeomorph.smul (M := N)
        𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ g.2) ⟨x.2, r ξ⟩).snd := by
    let := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    let := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
    let : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
    have h := cotangentProductHomeomorph_equivariant (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N g ⟨x, ξ⟩
    rw [cotangentProductHomeomorph_apply, cotangentProductHomeomorph_apply] at h
    refine ⟨?_, ?_⟩
    · exact congrArg (fun z ↦ (z.1.snd : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) h
    · exact congrArg (fun z ↦ (z.2.snd : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) h
  dsimp only
  change (p _ (l η)).toLinearMap.comp (i₀ g x).toLinearMap = _ ∧ _
  rw [hsplit.1, hsplit.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext v
    exact hpc g.1 x.1 (l ξ) v
  · ext v
    exact hpic g.1 x.1 (l ξ) v
  · ext v
    exact hqc g.2 x.2 (r ξ) v
  · ext v
    exact hqic g.2 x.2 (r ξ) v

end AtiyahSinger

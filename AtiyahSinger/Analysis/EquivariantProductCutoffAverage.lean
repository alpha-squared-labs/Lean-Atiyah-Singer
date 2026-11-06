/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AveragedGradedTensorSymbol
public import AtiyahSinger.Analysis.EquivariantProductGradedSymbolOrbit
public import AtiyahSinger.Analysis.EquivariantWeightedSymbolIntegral
public import AtiyahSinger.Analysis.FiniteAtlasRightProductCutoff
public import AtiyahSinger.Geometry.ProductCovectorCoordinates

/-!
# Exterior ellipticity of the actual averaged product-cutoff symbol

Public module ID: M0555.

One cutoff parameter and one frequency radius make the actual orbit average
invertible. Invariant factor metrics preserve the dominant branch along the
whole orbit, whose atlas coefficient is exactly one. The other coefficient
may be signed; only the full native Hom-valued orbit is integrated. The
specified full factor symbols and their Hermitian reverse blocks are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
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


variable [CompactSpace G] [CompactSpace H]
  [MeasurableSpace (G × H)] [BorelSpace (G × H)]

set_option maxHeartbeats 2200000 in
-- A single invariant dominant branch survives the whole native Hom-valued average.
/-- The original finite-atlas weighted product symbol remains elliptic after averaging. -/
theorem exists_productCutoff_average_bijective_at_infinity
    (p : GlobalSymbolFunction (n := n) E₀.Fiber E₁.Fiber)
    (pi : GlobalSymbolFunction (n := n) E₁.Fiber E₀.Fiber)
    (q : GlobalSymbolFunction (n := m) F₀.Fiber F₁.Fiber)
    (qi : GlobalSymbolFunction (n := m) F₁.Fiber F₀.Fiber)
    (hp : ∀ g : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ g p = p)
    (hpi : ∀ g : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₁ σ₀ g pi = pi)
    (hq : ∀ g : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ g q = q)
    (hqi : ∀ g : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₁ τ₀ g qi = qi)
    (C : QuantizationPresentation (n := n) (r := E₀.rank) (q := E₁.rank)
      E₀.Fiber E₁.Fiber)
    (D : QuantizationPresentation (n := m) (r := F₀.rank) (q := F₁.rank)
      F₀.Fiber F₁.Fiber)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (gInv : ∀ (a : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (a • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M)
        𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ a) ⟨x, ξ⟩).snd = g.length x ξ)
    (kInv : ∀ (a : H) (y : N) (ξ : CotangentFiber (n := m) y),
      k.length (a • y) (cotangentDiffeomorphMap (Diffeomorph.smul (M := N)
        𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a) ⟨y, ξ⟩).snd = k.length y ξ)
    (h₀ : SmoothHermitianMetric (n := n) (r := E₀.rank) E₀.Fiber)
    (h₁ : SmoothHermitianMetric (n := n) (r := E₁.rank) E₁.Fiber)
    (k₀ : SmoothHermitianMetric (n := m) (r := F₀.rank) F₀.Fiber)
    (k₁ : SmoothHermitianMetric (n := m) (r := F₁.rank) F₁.Fiber)
    (hpAdj : ∀ x ξ u v, h₁.pairing x (p x ξ u) v = h₀.pairing x u (pi x ξ v))
    (hqAdj : ∀ x ξ u v, k₁.pairing x (q x ξ u) v = k₀.pairing x u (qi x ξ v))
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hpBij : ∀ x ξ, R₁ ≤ g.length x ξ → Function.Bijective (p x ξ))
    (hqBij : ∀ x ξ, R₂ ≤ k.length x ξ → Function.Bijective (q x ξ))
    (ν : Measure (G × H)) [IsProbabilityMeasure ν] :
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
    letI : IsManifold 𝓘(ℝ, VG × VH) ∞ (G × H) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod G H
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
      ∀ (hσ : σ.IsSmooth (n := n + m) (r := S.rank) 𝓘(ℝ, VG × VH))
        (hτ : τ.IsSmooth (n := n + m) (r := T.rank) 𝓘(ℝ, VG × VH)),
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧
        ∀ (ε : ℝ) (_hε : 0 < ε), ε ≤ δ →
        let α (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
          ∑ i, ∑ j, (C.patch i).productCutoffWeight (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
        let β (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
          ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
        ∀ a : globalSymbolSpace (n := n + m) (r := S.rank) (q := T.rank) S.Fiber T.Fiber 1,
          (∀ x ξ v, a.val x ξ (e x v) = f x (reciprocalTensorSymbol
            ((α x ξ : ℂ) • (p x.1 (l ξ)).toLinearMap)
            ((α x ξ : ℂ) • (pi x.1 (l ξ)).toLinearMap)
            ((β x ξ : ℂ) • (q x.2 (r ξ)).toLinearMap)
            ((β x ξ : ℂ) • (qi x.2 (r ξ)).toLinearMap) v)) →
          ∀ (x : M × N) (ξ : CotangentFiber (n := n + m) x),
            R ≤ g.length x.1 (l ξ) + k.length x.2 (r ξ) →
              Function.Bijective ((equivariantWeightedSymbolIntegral 𝓘(ℝ, VG × VH) σ τ
                hσ hτ ν (fun _ ↦ 1) continuous_const 1 a).val x ξ) := by
  classical
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
  intro S T σ τ e f he hf hσ hτ
  obtain ⟨δ₁, hδ₁, hδ₁one, hα⟩ :=
    C.exists_productCutoffWeight_sum_eq_one D.inputEndomorphism g k
  obtain ⟨δ₂, hδ₂, _, hβ⟩ :=
    D.exists_rightProductCutoffWeight_sum_eq_one C.inputEndomorphism k g
  let R := 2 * max R₁ R₂
  have hR : 0 < R := mul_pos (by norm_num) (hR₁.trans_le (le_max_left _ _))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁one, R, hR, ?_⟩
  intro ε hε hεδ
  let α (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
    ∑ i, ∑ j, (C.patch i).productCutoffWeight (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
  let β (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
    ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
  intro a ha x ξ hξ
  let (z : M × N) : FiniteDimensional ℂ (S.Fiber z) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin S.rank)) S.Fiber z
  let (z : M × N) : FiniteDimensional ℂ (T.Fiber z) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin T.rank)) T.Fiber z
  let : CompleteSpace (T.Fiber x) := FiniteDimensional.complete ℂ (T.Fiber x)
  let : FiniteDimensional ℂ (E₀.Fiber x.1) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber x.1
  let : FiniteDimensional ℂ (E₁.Fiber x.1) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber x.1
  let : FiniteDimensional ℂ (F₀.Fiber x.2) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber x.2
  let : FiniteDimensional ℂ (F₁.Fiber x.2) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber x.2
  let η (a : G × H) := (cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
    𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ a).symm ⟨x, ξ⟩).snd
  have hlength (a : G × H) :
      g.length (a⁻¹ • x).1 (l (η a)) = g.length x.1 (l ξ) ∧
      k.length (a⁻¹ • x).2 (r (η a)) = k.length x.2 (r ξ) := by
    let := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
    let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    let := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
    let : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
    have h := cotangentProductHomeomorph_equivariant (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N a⁻¹ ⟨x, ξ⟩
    rw [cotangentProductHomeomorph_apply, cotangentProductHomeomorph_apply] at h
    have h₁ := congrArg (fun z ↦ (z.1.snd : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) h
    have h₂ := congrArg (fun z ↦ (z.2.snd : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) h
    dsimp only [η]
    rw [Diffeomorph.smul_symm]
    constructor
    · rw [show l ((cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
        𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ a⁻¹) ⟨x, ξ⟩).snd) =
          (cotangentDiffeomorphMap (Diffeomorph.smul (M := M)
            𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ a.1⁻¹) ⟨x.1, l ξ⟩).snd from h₁]
      exact gInv a.1⁻¹ x.1 (l ξ)
    · rw [show r ((cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
        𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ a⁻¹) ⟨x, ξ⟩).snd) =
          (cotangentDiffeomorphMap (Diffeomorph.smul (M := N)
            𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a.2⁻¹) ⟨x.2, r ξ⟩).snd from h₂]
      exact kInv a.2⁻¹ x.2 (r ξ)
  have horbit := equivariantGlobalSymbolLinearMap_product_weighted_reciprocalTensor
    E₀ E₁ F₀ F₁ σ₀ σ₁ τ₀ τ₁ p pi q qi hp hpi hq hqi S T σ τ e f he hf a.val α β ha
  have hint := (continuous_equivariantGlobalSymbol_apply 𝓘(ℝ, VG × VH) σ τ hσ hτ a x ξ)
    |>.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  simp only [equivariantWeightedSymbolIntegral_apply, one_smul]
  apply integral_reciprocalTensorSymbol_bijective_of_dominant
    (h₀.toCore x.1) (h₁.toCore x.1) (k₀.toCore x.2) (k₁.toCore x.2)
    (p x.1 (l ξ)).toLinearMap (pi x.1 (l ξ)).toLinearMap
    (q x.2 (r ξ)).toLinearMap (qi x.2 (r ξ)).toLinearMap
    (hpAdj x.1 (l ξ)) (hqAdj x.2 (r ξ)) (e x) (f x)
    (fun z ↦ equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ z a.val x ξ) hint
    (fun z ↦ α (z⁻¹ • x) (η z)) (fun z ↦ β (z⁻¹ • x) (η z))
    (fun z v ↦ horbit z x ξ v)
  -- Whichever factor is currently dominant remains dominant at every inverse orbit point.
  rcases le_total (k.length x.2 (r ξ)) (g.length x.1 (l ξ)) with hdom | hdom
  · left
    have hlarge : R₁ ≤ g.length x.1 (l ξ) := by
      have hmax := le_max_left R₁ R₂
      change 2 * max R₁ R₂ ≤ _ at hξ
      nlinarith
    refine ⟨hpBij x.1 (l ξ) hlarge, ?_⟩
    intro z
    apply hα ε hε (hεδ.trans (min_le_left _ _)) (z⁻¹ • x).1 (z⁻¹ • x).2 (η z)
    change k.length (z⁻¹ • x).2 (r (η z)) ≤ g.length (z⁻¹ • x).1 (l (η z))
    rw [(hlength z).1, (hlength z).2]
    exact hdom
  · right
    have hlarge : R₂ ≤ k.length x.2 (r ξ) := by
      have hmax := le_max_right R₁ R₂
      change 2 * max R₁ R₂ ≤ _ at hξ
      nlinarith
    refine ⟨hqBij x.2 (r ξ) hlarge, ?_⟩
    intro z
    apply hβ ε hε (hεδ.trans (min_le_right _ _)) (z⁻¹ • x).2 (z⁻¹ • x).1 (η z)
    change g.length (z⁻¹ • x).1 (l (η z)) ≤ k.length (z⁻¹ • x).2 (r (η z))
    rw [(hlength z).1, (hlength z).2]
    exact hdom

end AtiyahSinger

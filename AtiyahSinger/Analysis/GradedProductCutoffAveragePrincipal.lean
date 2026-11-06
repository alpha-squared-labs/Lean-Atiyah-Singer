/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousAverage
public import AtiyahSinger.Analysis.EquivariantProductCutoffAverage
public import AtiyahSinger.Analysis.GradedFullCutoffHomogeneity
public import AtiyahSinger.Geometry.ProductCotangentMetricBounds

/-!
# Homogeneous elliptic principal data of the same averaged cutoff PDO

Public module ID: M0709.

The actual invariant full factor symbols, their homogeneous tails, and the
finite-atlas graded formula give homogeneous elliptic data for the average
of the specified operator K. The exterior equality is to that actual native
orbit integral, and every regularization represents that same K.average.
No fixedness of the unaveraged cutoff symbol or replacement PDO is assumed.
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


variable [T2Space G] [T2Space H]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {ν : Measure N} [IsSmoothPositiveMeasure (n := m) ν]

set_option maxHeartbeats 2500000 in
-- The extended limit accommodates the actual averaged homogeneous elliptic cutoff principal data.
/-- The specified cutoff PDO has actual homogeneous elliptic principal data after averaging. -/
theorem exists_gradedProductCutoff_ellipticHomogeneous_average
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
    (p : globalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber 1)
    (q : globalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber 1)
    (a₀ : homogeneousGlobalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank)
      E₀.Fiber E₁.Fiber 1)
    (b₀ : homogeneousGlobalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank)
      F₀.Fiber F₁.Fiber 1)
    (ha₀ : IsEllipticGlobalSymbol E₀.Fiber E₁.Fiber a₀.val)
    (hb₀ : IsEllipticGlobalSymbol F₀.Fiber F₁.Fiber b₀.val)
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hpTail : ∀ x ξ, R₁ ≤ g.length x ξ → p.val x ξ = a₀.val x ξ)
    (hqTail : ∀ y ξ, R₂ ≤ k.length y ξ → q.val y ξ = b₀.val y ξ)
    (hp : ∀ a : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ a p.val = p.val)
    (hpi : ∀ a : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₁ σ₀ a
      (h₀.symbolSpaceAdjoint h₁ p).val = (h₀.symbolSpaceAdjoint h₁ p).val)
    (hq : ∀ a : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ a q.val = q.val)
    (hqi : ∀ a : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₁ τ₀ a
      (k₀.symbolSpaceAdjoint k₁ q).val = (k₀.symbolSpaceAdjoint k₁ q).val) :
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
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    let pa := h₀.symbolSpaceAdjoint h₁ p
    let qa := k₀.symbolSpaceAdjoint k₁ q
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
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (ε : ℝ) (_hε : 0 < ε), ε ≤ δ →
        let α (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
          ∑ i, ∑ j, (C.patch i).productCutoffWeight (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
        let β (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
          ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
        ∀ (K : PseudodifferentialOperator (n := n + m) (r := S.rank) (q := T.rank)
            S.Fiber T.Fiber (μ.prod ν) 1)
          (a : globalSymbolSpace (n := n + m) (r := S.rank) (q := T.rank) S.Fiber T.Fiber 1),
          K.principalSymbol = globalPrincipalSymbolClass S.Fiber T.Fiber 1 a →
          (∀ x ξ u v, a.val x ξ (e x (u, v)) = f x (reciprocalTensorSymbol
            ((α x ξ : ℂ) • (p.val x.1 (l ξ)).toLinearMap)
            ((α x ξ : ℂ) • (pa.val x.1 (l ξ)).toLinearMap)
            ((β x ξ : ℂ) • (q.val x.2 (r ξ)).toLinearMap)
            ((β x ξ : ℂ) • (qa.val x.2 (r ξ)).toLinearMap) (u, v))) →
          ∀ h : SmoothCotangentMetric (n := n + m) (M := M × N),
            (∀ (z : G × H) (x : M × N) (ξ : CotangentFiber (n := n + m) x),
              h.length (z • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
                𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ z) ⟨x, ξ⟩).snd =
                  h.length x ξ) →
            ∃ R : ℝ, 0 < R ∧
              ∃ b : homogeneousGlobalSymbolSpace (n := n + m) (r := S.rank) (q := T.rank)
                  S.Fiber T.Fiber 1,
                IsEllipticGlobalSymbol S.Fiber T.Fiber b.val ∧
                (∀ x ξ, R ≤ h.length x ξ → b.val x ξ =
                  ∫ z, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ z a.val x ξ
                    ∂Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (G × H))) ∧
                (∀ (z : G × H) (x : M × N) (ξ : CotangentFiber (n := n + m) x), ξ ≠ 0 →
                  equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ z b.val x ξ = b.val x ξ) ∧
                (∀ L : QuantizationPresentation (n := n + m) (r := S.rank) (q := T.rank)
                    S.Fiber T.Fiber,
                  (K.average 𝓘(ℝ, VG × VH) σ τ hσ hτ).principalSymbol =
                    globalPrincipalSymbolClass S.Fiber T.Fiber 1
                      (L.regularizedSymbol 1 b.val b.property.1 b.property.2)) ∧
                (K.average 𝓘(ℝ, VG × VH) σ τ hσ hτ).IsElliptic := by
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
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  let pa := h₀.symbolSpaceAdjoint h₁ p
  let qa := k₀.symbolSpaceAdjoint k₁ q
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
  let ρ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (G × H))
  let : IsProbabilityMeasure ρ := ⟨Measure.haarMeasure_self⟩
  have hpBij (x : M) (ξ : CotangentFiber (n := n) x) (hξ : R₁ ≤ g.length x ξ) :
      Function.Bijective (p.val x ξ) := by
    rw [hpTail x ξ hξ]
    apply ha₀ x ξ
    intro hz
    have hzero := (g.length_eq_zero_iff x ξ).mpr hz
    linarith
  have hqBij (y : N) (ξ : CotangentFiber (n := m) y) (hξ : R₂ ≤ k.length y ξ) :
      Function.Bijective (q.val y ξ) := by
    rw [hqTail y ξ hξ]
    apply hb₀ y ξ
    intro hz
    have hzero := (k.length_eq_zero_iff y ξ).mpr hz
    linarith
  obtain ⟨δ, hδ, hδone, Rb, hRb, hbij⟩ :=
    exists_productCutoff_average_bijective_at_infinity E₀ E₁ F₀ F₁ σ₀ σ₁ τ₀ τ₁
      p.val pa.val q.val qa.val hp hpi hq hqi C D g k gInv kInv h₀ h₁ k₀ k₁
      (fun x ξ u v ↦ (h₀.pairing_adjoint h₁ x (p.val x ξ) u v).symm)
      (fun y ξ u v ↦ (k₀.pairing_adjoint k₁ y (q.val y ξ) u v).symm)
      R₁ R₂ hR₁ hR₂ hpBij hqBij ρ S T σ τ e f he hf hσ hτ
  refine ⟨δ, hδ, hδone, ?_⟩
  intro ε hε hεδ K a hK ha h hInv
  obtain ⟨Rt, hRt, hscale⟩ := exists_gradedProductCutoff_homogeneous_at_infinity
    E₀ E₁ F₀ F₁ C D g k h₀ h₁ k₀ k₁ p q a₀ b₀ R₁ R₂ hR₁ hR₂ hpTail hqTail ε hε
  obtain ⟨c₀, hc₀, hmetric⟩ := exists_product_cotangent_length_le g k h
  let R := c₀ * max Rt Rb
  have hR : 0 < R := mul_pos hc₀ (hRt.trans_le (le_max_left _ _))
  have hlarge (x : M × N) (ξ : CotangentFiber (n := n + m) x)
      (hξ : R ≤ h.length x ξ) : max Rt Rb ≤ g.length x.1 (l ξ) + k.length x.2 (r ξ) := by
    have hh := hmetric ⟨x, ξ⟩
    rw [cotangentProductHomeomorph_apply] at hh
    change h.length x ξ ≤ c₀ * (g.length x.1 (l ξ) + k.length x.2 (r ξ)) at hh
    dsimp only [R] at hξ
    nlinarith
  have hscale' : ∀ x ξ (t : ℝ), 0 < t → R ≤ h.length x ξ →
      R ≤ h.length x (t • ξ) → a.val x (t • ξ) = (t : ℂ) • a.val x ξ := by
    intro x ξ t ht hξ htξ
    exact hscale S T e f a.val ha x ξ t ht
      ((le_max_left _ _).trans (hlarge x ξ hξ))
      ((le_max_left _ _).trans (hlarge x (t • ξ) htξ))
  have hbij' : ∀ x ξ, R ≤ h.length x ξ → Function.Bijective
      ((∫ z, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ z a.val x ξ ∂ρ) :
        S.Fiber x →L[ℂ] T.Fiber x) := by
    intro x ξ hξ
    have hb := hbij ε hε hεδ a (fun x ξ v ↦ ha x ξ v.1 v.2) x ξ
      ((le_max_right _ _).trans (hlarge x ξ hξ))
    simpa only [equivariantWeightedSymbolIntegral_apply, one_smul] using hb
  obtain ⟨b, hb, hhigh, hfixed, hprincipal⟩ :=
    K.exists_ellipticHomogeneous_principalSymbol_average 𝓘(ℝ, VG × VH) σ τ hσ hτ
      a hK h R hR hInv hscale' hbij'
  refine ⟨R, hR, b, hb, hhigh, hfixed, hprincipal, ?_⟩
  let L : QuantizationPresentation (n := n + m) (r := S.rank) (q := T.rank)
      S.Fiber T.Fiber := Classical.choice
        (nonempty_quantizationPresentation (E := S.Fiber) (F := T.Fiber))
  exact ⟨_, hprincipal L,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff L 1 b.val b.property.1 b.property.2).mpr hb⟩

end AtiyahSinger

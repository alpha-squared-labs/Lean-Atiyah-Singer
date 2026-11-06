/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AveragedGradedSupportHomotopy
public import AtiyahSinger.Analysis.EquivariantProductCutoffAverage
public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Geometry.CotangentMetricCompact
public import AtiyahSinger.Geometry.ProductCotangentMetricBounds

/-!
# The supported class of the averaged graded cutoff symbol

Public module ID: M0696.

The homogeneous tail of the native orbit average represents the same
equivariant supported class as the uncut Hermitian boundary. A compact
invariant control contains the boundary control and a metric sublevel set
covering the specified homogeneous-tail radius. On its complement, the
dominant factor and atlas coefficient remain fixed along inverse orbits,
giving a homotopy between the specified endpoint triples.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 50
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

variable [T2Space M] [CompactSpace M] [T2Space N] [CompactSpace N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback

set_option maxHeartbeats 9000000 in
-- Normalize the averaged homogeneous graded symbol and the original uncut boundary class.
set_option maxRecDepth 4096 in
/-- The actual averaged homogeneous graded symbol has the class of the uncut full boundary. -/
theorem exists_gradedCutoff_average_kClass_eq
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
    (R₁ R₂ : ℝ) (_hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
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
      ∀ (_hσ : σ.IsSmooth (n := n + m) (r := S.rank) 𝓘(ℝ, VG × VH))
        (_hτ : τ.IsSmooth (n := n + m) (r := T.rank) 𝓘(ℝ, VG × VH)),
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (ε : ℝ) (_hε : 0 < ε), ε ≤ δ →
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
        ∀ h : SmoothCotangentMetric (n := n + m) (M := M × N),
          (∀ (z : G × H) (x : M × N) (ξ : CotangentFiber (n := n + m) x),
            h.length (z • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
              𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ z) ⟨x, ξ⟩).snd =
                h.length x ξ) →
        ∀ (Rb : ℝ) (_hRb : 0 < Rb)
          (b : homogeneousGlobalSymbolSpace (n := n + m) (r := S.rank) (q := T.rank)
            S.Fiber T.Fiber 1)
          (hb : IsEllipticGlobalSymbol S.Fiber T.Fiber b.val)
          (hbEq : ∀ (z : G × H) (x : M × N) (ξ : CotangentFiber (n := n + m) x), ξ ≠ 0 →
            equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ z b.val x ξ = b.val x ξ),
          (∀ x ξ, Rb ≤ h.length x ξ → b.val x ξ =
            ∫ z, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ z a.val x ξ ∂ν) →
        letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
        letI := isFiniteRank_model (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
        letI := isFiniteRank_model (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
        letI := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
        letI := contMDiffSMul_smoothCotangent
          (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
        letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
          ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
            (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
        let pr := cotangentProjection (n := n + m) (M := M × N)
        ∀ (d : CompactSupportTriple (pr *ᵖ S.Fiber) (pr *ᵖ T.Fiber))
          (hd : d.IsEquivariant (σ.pullback pr (fun _ _ ↦ rfl))
            (τ.pullback pr (fun _ _ ↦ rfl))),
          (∀ (z : (d.controlᶜ : Set (CotangentTotalSpace (n := n + m) (M := M × N)))) v,
            d.boundary.linearEquiv z (e z.val.proj v) = f z.val.proj
              (reciprocalTensorSymbol (p z.val.proj.1 (l z.val.snd)).toLinearMap
                (pi z.val.proj.1 (l z.val.snd)).toLinearMap
                (q z.val.proj.2 (r z.val.snd)).toLinearMap
                (qi z.val.proj.2 (r z.val.snd)).toLinearMap v)) →
          (EquivariantSupportBundleTriple.ofBoundary
            (FiniteBundle.ofFamily (pr *ᵖ S.Fiber)) (FiniteBundle.ofFamily (pr *ᵖ T.Fiber))
            d (σ.pullback pr (fun _ _ ↦ rfl)) (τ.pullback pr (fun _ _ ↦ rfl)) hd).kZeroClass =
              equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG × VH) σ τ 1 b hb hbEq := by
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
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁one, ?_⟩
  intro ε hε hεδ
  let α (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
    ∑ i, ∑ j, (C.patch i).productCutoffWeight (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
  let β (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
    ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
  intro a ha h hInv Rb hRb b hb hbEq hbAve
  let := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
  let := smoothCotangentMulAction (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  let := contMDiffSMul_smoothCotangent
    (n := n + m) (G := G × H) (M := M × N) 𝓘(ℝ, VG × VH)
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
  let pr := cotangentProjection (n := n + m) (M := M × N)
  intro d hd hdFormula
  let B := ellipticSymbolTriple b.val b.property.1.continuous hb
  have hB := ellipticSymbolTriple_isEquivariant 𝓘(ℝ, VG × VH) σ τ
    b.val b.property.1.continuous hb hbEq
  obtain ⟨c₁, hc₁, hmetric⟩ := exists_product_cotangent_length_le g k h
  let R := max Rb (c₁ * (2 * max R₁ R₂))
  have hR : 0 < R := hRb.trans_le (le_max_left _ _)
  let K := d.control ∪ {z | h.length z.proj z.snd ≤ R}
  have hK : IsCompact K := d.isCompact_control.union (h.isCompact_sublevel R)
  have hKInv : ∀ (g : G × H) (z : CotangentTotalSpace (n := n + m) (M := M × N)),
      g • z ∈ K ↔ z ∈ K := by
    intro g z
    exact (hd.invariant_control g z).or
      (congrArg (fun t : ℝ ↦ t ≤ R) (hInv g z.proj z.snd)).to_iff
  have hBK : B.control ⊆ K := by
    intro z hz
    apply Or.inr
    change z.snd = 0 at hz
    change h.length z.proj z.snd ≤ R
    exact ((h.length_eq_zero_iff _ _).mpr hz).le.trans hR.le
  have hlen (z : (Kᶜ : Set (CotangentTotalSpace (n := n + m) (M := M × N)))) :
      R < h.length z.val.proj z.val.snd := lt_of_not_ge (fun hz ↦ z.property (Or.inr hz))
  have hlarge (z : (Kᶜ : Set (CotangentTotalSpace (n := n + m) (M := M × N)))) :
      2 * max R₁ R₂ ≤ g.length z.val.proj.1 (l z.val.snd) +
        k.length z.val.proj.2 (r z.val.snd) := by
    have hm := hmetric z.val
    rw [cotangentProductHomeomorph_apply] at hm
    change h.length z.val.proj z.val.snd ≤ c₁ *
      (g.length z.val.proj.1 (l z.val.snd) + k.length z.val.proj.2 (r z.val.snd)) at hm
    have hr := le_max_right Rb (c₁ * (2 * max R₁ R₂))
    have hz := hlen z
    dsimp only [R] at hz
    nlinarith
  let η (x : M × N) (ξ : CotangentFiber (n := n + m) x) (a : G × H) :=
    (cotangentDiffeomorphMap (Diffeomorph.smul (M := M × N)
    𝓘(ℝ, VG × VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))) ∞ a).symm ⟨x, ξ⟩).snd
  have hlength (x : M × N) (ξ : CotangentFiber (n := n + m) x) (a : G × H) :
      g.length (a⁻¹ • x).1 (l (η x ξ a)) = g.length x.1 (l ξ) ∧
      k.length (a⁻¹ • x).2 (r (η x ξ a)) = k.length x.2 (r ξ) := by
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
  let (x : M × N) : FiniteDimensional ℂ (S.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin S.rank)) S.Fiber x
  let (x : M × N) : FiniteDimensional ℂ (T.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin T.rank)) T.Fiber x
  let (x : M) : FiniteDimensional ℂ (E₀.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber x
  let (x : M) : FiniteDimensional ℂ (E₁.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber x
  let (x : N) : FiniteDimensional ℂ (F₀.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber x
  let (x : N) : FiniteDimensional ℂ (F₁.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber x
  let : ∀ z, FiniteDimensional ℂ ((pr *ᵖ S.Fiber) z) := fun z ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin S.rank)) S.Fiber z.proj
  let : ∀ z, FiniteDimensional ℂ ((pr *ᵖ T.Fiber) z) := fun z ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin T.rank)) T.Fiber z.proj
  have H : d.EquivariantlyHomotopic B (σ.pullback pr (fun _ _ ↦ rfl))
      (τ.pullback pr (fun _ _ ↦ rfl)) := by
    apply d.equivariantlyHomotopic_of_averagedGradedTensor B
      (σ.pullback pr (fun _ _ ↦ rfl)) (τ.pullback pr (fun _ _ ↦ rfl)) hd hB
      K hK hKInv Set.subset_union_left hBK
      (fun z ↦ e z.proj) (fun z ↦ f z.proj)
      (fun z ↦ h₀.toCore z.proj.1) (fun z ↦ h₁.toCore z.proj.1)
      (fun z ↦ k₀.toCore z.proj.2) (fun z ↦ k₁.toCore z.proj.2)
      (fun z ↦ (p z.proj.1 (l z.snd)).toLinearMap)
      (fun z ↦ (pi z.proj.1 (l z.snd)).toLinearMap)
      (fun z ↦ (q z.proj.2 (r z.snd)).toLinearMap)
      (fun z ↦ (qi z.proj.2 (r z.snd)).toLinearMap)
      (fun z ↦ hpAdj z.proj.1 (l z.snd)) (fun z ↦ hqAdj z.proj.2 (r z.snd))
      (fun z t ↦ equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG × VH) σ τ t a.val
        z.val.proj z.val.snd)
      (fun z ↦ (continuous_equivariantGlobalSymbol_apply 𝓘(ℝ, VG × VH) σ τ hσ hτ
        a z.val.proj z.val.snd).integrable_of_hasCompactSupport (μ := ν)
          (HasCompactSupport.of_compactSpace _))
      (fun z t ↦ α (t⁻¹ • z.val.proj) (η z.val.proj z.val.snd t))
      (fun z t ↦ β (t⁻¹ • z.val.proj) (η z.val.proj z.val.snd t))
    · intro z v
      exact (d.enlarge_apply K hK Set.subset_union_left z (e z.val.proj v)).trans
        (hdFormula ⟨z.val, fun hz ↦ z.property (Or.inl hz)⟩ v)
    · intro z v
      exact (B.enlarge_apply K hK hBK z v).trans
        ((ellipticSymbolTriple_boundary_apply b.val b.property.1.continuous hb
          ⟨z.val, fun hz ↦ z.property (hBK hz)⟩ v).trans
            (congrArg (fun L : S.Fiber z.val.proj →L[ℂ] T.Fiber z.val.proj ↦ L v)
              (hbAve _ _ ((le_max_left _ _).trans (hlen z).le))))
    · intro z t v
      exact horbit t z.val.proj z.val.snd v
    · intro z
      rcases le_total (k.length z.val.proj.2 (r z.val.snd))
          (g.length z.val.proj.1 (l z.val.snd)) with hdom | hdom
      · left
        have hbig : R₁ ≤ g.length z.val.proj.1 (l z.val.snd) := by
          have hm := le_max_left R₁ R₂
          have hz := hlarge z
          nlinarith
        refine ⟨hpBij _ _ hbig, ?_⟩
        intro t
        apply hα ε hε (hεδ.trans (min_le_left _ _))
          (t⁻¹ • z.val.proj).1 (t⁻¹ • z.val.proj).2 (η z.val.proj z.val.snd t)
        change k.length (t⁻¹ • z.val.proj).2 (r (η z.val.proj z.val.snd t)) ≤
          g.length (t⁻¹ • z.val.proj).1 (l (η z.val.proj z.val.snd t))
        rw [(hlength _ _ t).1, (hlength _ _ t).2]
        exact hdom
      · right
        have hbig : R₂ ≤ k.length z.val.proj.2 (r z.val.snd) := by
          have hm := le_max_right R₁ R₂
          have hz := hlarge z
          nlinarith
        refine ⟨hqBij _ _ hbig, ?_⟩
        intro t
        apply hβ ε hε (hεδ.trans (min_le_right _ _))
          (t⁻¹ • z.val.proj).2 (t⁻¹ • z.val.proj).1 (η z.val.proj z.val.snd t)
        change g.length (t⁻¹ • z.val.proj).1 (l (η z.val.proj z.val.snd t)) ≤
          k.length (t⁻¹ • z.val.proj).2 (r (η z.val.proj z.val.snd t))
        rw [(hlength _ _ t).1, (hlength _ _ t).2]
        exact hdom
  exact equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (FiniteBundle.ofFamily (pr *ᵖ S.Fiber)) (FiniteBundle.ofFamily (pr *ᵖ T.Fiber))
    (σ.pullback pr (fun _ _ ↦ rfl)) (τ.pullback pr (fun _ _ ↦ rfl)) d B hd hB H

end AtiyahSinger

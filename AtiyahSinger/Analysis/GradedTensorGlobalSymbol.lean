/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Analysis.GradedBundleGlobalSymbol
public import AtiyahSinger.Analysis.HermitianMetricPseudodifferentialAdjoint
public import AtiyahSinger.Geometry.HermitianTensorAdjointTransport

/-!
# The same native graded operator and its tensor full symbol

Public module ID: M0713.

The four specified forward full representatives factor through the original
tensor maps. The original tensor pairings identify the reverse symbols with
the principal representatives of the actual native metric adjoints. The same
graded operator therefore has the literal reciprocal tensor matrix in the
specified native sum coordinates. This is the full-symbol identification in
SG III.13.6, before ellipticity and the global K-class homotopy.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : Fin 2 → SmoothFiniteComplexBundle (n := n) M)

set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the complete reciprocal tensor representative of the specified
-- native operator.
/-- The specified native graded PDO has the original reciprocal tensor full representative. -/
theorem exists_tensorGlobalSymbol_of_gradedBundlePseudodifferentialOperator
    (e : ∀ x, ((A 0).Fiber x × (A 1).Fiber x) ≃ₗ[ℂ] E.Fiber x)
    (f : ∀ x, ((B 0).Fiber x × (B 1).Fiber x) ≃ₗ[ℂ] F.Fiber x)
    (he₀ : IsSmoothBundleMap (n := n) (r := (A 0).rank) (q := E.rank)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
    (he₁ : IsSmoothBundleMap (n := n) (r := (A 1).rank) (q := E.rank)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
    (hf₀ : IsSmoothBundleMap (n := n) (r := (B 0).rank) (q := F.rank)
      (fun x ↦ (f x).toLinearMap.comp (LinearMap.inl ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
    (hf₁ : IsSmoothBundleMap (n := n) (r := (B 1).rank) (q := F.rank)
      (fun x ↦ (f x).toLinearMap.comp (LinearMap.inr ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
    (hA : ∀ i, SmoothHermitianMetric (n := n) (r := (A i).rank) (A i).Fiber)
    (hB : ∀ i, SmoothHermitianMetric (n := n) (r := (B i).rank) (B i).Fiber)
    {m : ℝ}
    (U₀ : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 0).rank)
      (A 0).Fiber (B 0).Fiber μ m)
    (V₀ : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 1).rank)
      (A 0).Fiber (B 1).Fiber μ m)
    (U₁ : PseudodifferentialOperator (n := n) (r := (B 1).rank) (q := (A 1).rank)
      (B 1).Fiber (A 1).Fiber μ m)
    (V₁ : PseudodifferentialOperator (n := n) (r := (B 0).rank) (q := (A 1).rank)
      (B 0).Fiber (A 1).Fiber μ m)
    (K : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ m)
    (hK : ∀ u v, K.toLinearMap (smoothSectionSumEquiv e he₀ he₁ (u, v)) =
      smoothSectionSumEquiv f hf₀ hf₁
        (U₀.toLinearMap u - (V₁.metricFormalAdjoint (hB 0) (hA 1)).toLinearMap v,
          V₀.toLinearMap u + (U₁.metricFormalAdjoint (hB 1) (hA 1)).toLinearMap v))
    (a₀ : globalSymbolSpace (n := n) (r := (A 0).rank) (q := (B 0).rank)
      (A 0).Fiber (B 0).Fiber m)
    (b₀ : globalSymbolSpace (n := n) (r := (A 0).rank) (q := (B 1).rank)
      (A 0).Fiber (B 1).Fiber m)
    (a₁ : globalSymbolSpace (n := n) (r := (B 1).rank) (q := (A 1).rank)
      (B 1).Fiber (A 1).Fiber m)
    (b₁ : globalSymbolSpace (n := n) (r := (B 0).rank) (q := (A 1).rank)
      (B 0).Fiber (A 1).Fiber m)
    (ha₀ : U₀.principalSymbol = globalPrincipalSymbolClass (A 0).Fiber (B 0).Fiber m a₀)
    (hb₀ : V₀.principalSymbol = globalPrincipalSymbolClass (A 0).Fiber (B 1).Fiber m b₀)
    (ha₁ : U₁.principalSymbol = globalPrincipalSymbolClass (B 1).Fiber (A 1).Fiber m a₁)
    (hb₁ : V₁.principalSymbol = globalPrincipalSymbolClass (B 0).Fiber (A 1).Fiber m b₁)
    {C₀ C₁ D₀ D₁ : M → Type*}
    [∀ x, AddCommGroup (C₀ x)] [∀ x, Module ℂ (C₀ x)]
    [∀ x, AddCommGroup (C₁ x)] [∀ x, Module ℂ (C₁ x)]
    [∀ x, AddCommGroup (D₀ x)] [∀ x, Module ℂ (D₀ x)]
    [∀ x, AddCommGroup (D₁ x)] [∀ x, Module ℂ (D₁ x)]
    (c₀ : ∀ x, InnerProductSpace.Core ℂ (C₀ x))
    (c₁ : ∀ x, InnerProductSpace.Core ℂ (C₁ x))
    (d₀ : ∀ x, InnerProductSpace.Core ℂ (D₀ x))
    (d₁ : ∀ x, InnerProductSpace.Core ℂ (D₁ x))
    (e₀₀ : ∀ x, C₀ x ⊗[ℂ] D₀ x ≃ₗ[ℂ] (A 0).Fiber x)
    (e₁₁ : ∀ x, C₁ x ⊗[ℂ] D₁ x ≃ₗ[ℂ] (A 1).Fiber x)
    (e₁₀ : ∀ x, C₁ x ⊗[ℂ] D₀ x ≃ₗ[ℂ] (B 0).Fiber x)
    (e₀₁ : ∀ x, C₀ x ⊗[ℂ] D₁ x ≃ₗ[ℂ] (B 1).Fiber x)
    (h₁₁ : ∀ x u v a b,
      (hA 1).pairing x (e₁₁ x (u ⊗ₜ[ℂ] a)) (e₁₁ x (v ⊗ₜ[ℂ] b)) =
        (c₁ x).inner u v * (d₁ x).inner a b)
    (h₁₀ : ∀ x u v a b,
      (hB 0).pairing x (e₁₀ x (u ⊗ₜ[ℂ] a)) (e₁₀ x (v ⊗ₜ[ℂ] b)) =
        (c₁ x).inner u v * (d₀ x).inner a b)
    (h₀₁ : ∀ x u v a b,
      (hB 1).pairing x (e₀₁ x (u ⊗ₜ[ℂ] a)) (e₀₁ x (v ⊗ₜ[ℂ] b)) =
        (c₀ x).inner u v * (d₁ x).inner a b)
    (p : ∀ x, CotangentFiber (n := n) x → C₀ x →ₗ[ℂ] C₁ x)
    (pi : ∀ x, CotangentFiber (n := n) x → C₁ x →ₗ[ℂ] C₀ x)
    (q : ∀ x, CotangentFiber (n := n) x → D₀ x →ₗ[ℂ] D₁ x)
    (qi : ∀ x, CotangentFiber (n := n) x → D₁ x →ₗ[ℂ] D₀ x)
    (hp : ∀ x ξ u v, (c₁ x).inner (p x ξ u) v = (c₀ x).inner u (pi x ξ v))
    (hq : ∀ x ξ u v, (d₁ x).inner (q x ξ u) v = (d₀ x).inner u (qi x ξ v))
    (ha₀tensor : ∀ x ξ u v,
      a₀.val x ξ (e₀₀ x (u ⊗ₜ[ℂ] v)) = e₁₀ x (p x ξ u ⊗ₜ[ℂ] v))
    (hb₀tensor : ∀ x ξ u v,
      b₀.val x ξ (e₀₀ x (u ⊗ₜ[ℂ] v)) = e₀₁ x (u ⊗ₜ[ℂ] q x ξ v))
    (ha₁tensor : ∀ x ξ u v,
      a₁.val x ξ (e₀₁ x (u ⊗ₜ[ℂ] v)) = e₁₁ x (p x ξ u ⊗ₜ[ℂ] v))
    (hb₁tensor : ∀ x ξ u v,
      b₁.val x ξ (e₁₀ x (u ⊗ₜ[ℂ] v)) = e₁₁ x (u ⊗ₜ[ℂ] q x ξ v)) :
    ∃ s : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m,
      (∀ x ξ (u : C₀ x ⊗[ℂ] D₀ x) (v : C₁ x ⊗[ℂ] D₁ x),
        let w := reciprocalTensorSymbol (p x ξ) (pi x ξ) (q x ξ) (qi x ξ) (u, v)
        s.val x ξ (e x (e₀₀ x u, e₁₁ x v)) = f x (e₁₀ x w.1, e₀₁ x w.2)) ∧
      K.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber m s := by
  classical
  -- The reverse representatives belong to the actual native adjoints used by K.
  let c := (hB 0).symbolSpaceAdjoint (hA 1) b₁
  let d := (hB 1).symbolSpaceAdjoint (hA 1) a₁
  have hc : (V₁.metricFormalAdjoint (hB 0) (hA 1)).principalSymbol =
      globalPrincipalSymbolClass (A 1).Fiber (B 0).Fiber m c := by
    rw [V₁.principalSymbol_metricFormalAdjoint, hb₁]
    exact (hB 0).principalSymbolAdjoint_class (hA 1) b₁
  have hd : (U₁.metricFormalAdjoint (hB 1) (hA 1)).principalSymbol =
      globalPrincipalSymbolClass (A 1).Fiber (B 1).Fiber m d := by
    rw [U₁.principalSymbol_metricFormalAdjoint, ha₁]
    exact (hB 1).principalSymbolAdjoint_class (hA 1) a₁
  obtain ⟨s, hs, hclass⟩ := exists_globalSymbol_of_gradedBundlePseudodifferentialOperator
    E F A B e f he₀ he₁ hf₀ hf₁ U₀ V₀
      (V₁.metricFormalAdjoint (hB 0) (hA 1)) (U₁.metricFormalAdjoint (hB 1) (hA 1))
      K hK a₀ b₀ c d ha₀ hb₀ hc hd
  refine ⟨s, ?_, hclass⟩
  intro x ξ u v
  -- Tensor induction retains the specified forward maps on every vector.
  have ha (w : C₀ x ⊗[ℂ] D₀ x) :
      a₀.val x ξ (e₀₀ x w) = e₁₀ x (TensorProduct.map (p x ξ) LinearMap.id w) := by
    induction w using TensorProduct.inductionOn with
    | tmul z t => simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using ha₀tensor x ξ z t
    | add z t hz ht => simp only [map_add, hz, ht]
  have hb (w : C₀ x ⊗[ℂ] D₀ x) :
      b₀.val x ξ (e₀₀ x w) = e₀₁ x (TensorProduct.map LinearMap.id (q x ξ) w) := by
    induction w using TensorProduct.inductionOn with
    | tmul z t => simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using hb₀tensor x ξ z t
    | add z t hz ht => simp only [map_add, hz, ht]
  -- The prescribed factor adjoints give exactly the native reverse symbols.
  have hcTensor (w : C₁ x ⊗[ℂ] D₁ x) :
      c.val x ξ (e₁₁ x w) = e₁₀ x (TensorProduct.map LinearMap.id (qi x ξ) w) := by
    exact (hB 0).adjoint_eq_tensorMap (hA 1) (c₁ x) (c₁ x) (d₀ x) (d₁ x)
      x (e₁₀ x) (e₁₁ x) (h₁₀ x) (h₁₁ x) LinearMap.id LinearMap.id (q x ξ) (qi x ξ)
      (fun _ _ ↦ rfl) (hq x ξ) (b₁.val x ξ) (hb₁tensor x ξ) w
  have hdTensor (w : C₁ x ⊗[ℂ] D₁ x) :
      d.val x ξ (e₁₁ x w) = e₀₁ x (TensorProduct.map (pi x ξ) LinearMap.id w) := by
    exact (hB 1).adjoint_eq_tensorMap (hA 1) (c₀ x) (c₁ x) (d₁ x) (d₁ x)
      x (e₀₁ x) (e₁₁ x) (h₀₁ x) (h₁₁ x) (p x ξ) (pi x ξ) LinearMap.id LinearMap.id
      (hp x ξ) (fun _ _ ↦ rfl) (a₁.val x ξ) (ha₁tensor x ξ) w
  -- The original sum isomorphisms preserve both the order and the upper-right minus sign.
  dsimp only
  rw [hs, ha, hb, hcTensor, hdTensor]
  simp [reciprocalTensorSymbol, Function.prod, sub_eq_add_neg]

end AtiyahSinger

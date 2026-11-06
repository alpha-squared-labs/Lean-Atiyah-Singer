/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.NativeAtlasCovariantSobolev
public import AtiyahSinger.Analysis.SymbolFrequencyLipschitz
public import AtiyahSinger.Geometry.CompactFrameMetricBound

/-!
# Uniform frequency variation in the original bundle metrics

Public module ID: M0653.

The first frequency derivative of an order-one full symbol is uniformly
bounded on a compact chart window. The original compact frame comparison
transfers this to the specified source and target Hermitian metrics for the
actual symbol difference. The result does not require a homogeneous symbol
or continuously varying original native fiber norms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {F : M → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

set_option maxSynthPendingDepth 30 in
/-- The actual full symbol has a uniform frequency Lipschitz bound in its given metrics. -/
theorem IsGlobalSymbol.exists_compact_metric_frequency_bound
    (p : GlobalSymbolFunction (n := n) E F)
    (hp : IsGlobalSymbol (r := r) (q := q) E F 1 p)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (K : Set M) (hK : IsCompact K)
    (hKe : K ⊆ c.source ∩ e.baseSet) (hKf : K ⊆ c.source ∩ f.baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (_hx : x ∈ K)
      (ξ η : EuclideanSpace ℝ (Fin n)) (v : E x),
      (k.pairing x ((p x (covectorFromChart c x η) - p x (covectorFromChart c x ξ)) v)
          ((p x (covectorFromChart c x η) - p x (covectorFromChart c x ξ)) v)).re ≤
        C * ‖η - ξ‖ ^ 2 * (h.pairing x v v).re := by
  classical
  -- Apply the actual order-one frequency derivative estimate on the same compact chart image.
  have himage : IsCompact (c '' K) :=
    hK.image_of_continuousOn (c.continuousOn.mono (fun x hx ↦ (hKe hx).1))
  have hwindow : c '' K ⊆ symbolChartDomain E F c e f := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨c.map_source (hKe hx).1, ?_⟩, ?_⟩
    · change c.symm (c x) ∈ e.baseSet
      rw [c.left_inv (hKe hx).1]
      exact (hKe hx).2
    · change c.symm (c x) ∈ f.baseSet
      rw [c.left_inv (hKe hx).1]
      exact (hKf hx).2
  obtain ⟨D, hD, hfreq⟩ := (hp c hc e f).exists_frequency_lipschitz_bound
    (c '' K) hwindow himage
  let : MeasurableSpace M := borel M
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  obtain ⟨C₀, hC₀, hmetric⟩ := B.exists_compact_frame_metric_bound A g
    k.toContinuousHermitianMetric h.toContinuousHermitianMetric
    k.isSmoothHermitianMetric_nativeAtlas h.isSmoothHermitianMetric_nativeAtlas
    c hc ⟨f, inferInstance⟩ ⟨e, inferInstance⟩ K hK hKf hKe
  refine ⟨C₀ * D ^ 2, mul_nonneg hC₀.le (sq_nonneg D), ?_⟩
  intro x hx ξ η v
  let ec := e.continuousLinearEquivAt ℂ x (hKe hx).2
  let fc := f.continuousLinearEquivAt ℂ x (hKf hx).2
  let L := globalSymbolInChart E F p c e f (c x) η -
    globalSymbolInChart E F p c e f (c x) ξ
  have hnorm : ‖L‖ ≤ D * ‖η - ξ‖ := hfreq (c x) ⟨x, hx, rfl⟩ ξ η
  have hcoord (ν : EuclideanSpace ℝ (Fin n)) :
      globalSymbolInChart E F p c e f (c x) ν =
        fc.toContinuousLinearMap.comp
          ((p x (covectorFromChart c x ν)).comp ec.symm.toContinuousLinearMap) := by
    dsimp only [globalSymbolInChart]
    rw [c.left_inv (hKe hx).1]
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) (hKf hx).2,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) (hKe hx).2]
  have htransport : fc.symm (L (ec v)) =
      (p x (covectorFromChart c x η) - p x (covectorFromChart c x ξ)) v := by
    change fc.symm (globalSymbolInChart E F p c e f (c x) η (ec v) -
      globalSymbolInChart E F p c e f (c x) ξ (ec v)) = _
    rw [hcoord η, hcoord ξ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ec.symm_apply_apply, ← map_sub, fc.symm_apply_apply, sub_apply]
  -- The two native atlas frames are exactly the original specified native coordinates.
  have heFrame : (A.frameLinearEquiv ⟨e, inferInstance⟩ x (hKe hx).2).trans
      (EuclideanSpace.equiv (Fin (A.rank ⟨e, inferInstance⟩)) ℂ).symm.toLinearEquiv =
        ec.toLinearEquiv := by
    apply LinearEquiv.ext
    intro u
    exact (EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply (ec u)
  have hfFrame : (B.frameLinearEquiv ⟨f, inferInstance⟩ x (hKf hx).2).trans
      (EuclideanSpace.equiv (Fin (B.rank ⟨f, inferInstance⟩)) ℂ).symm.toLinearEquiv =
        fc.toLinearEquiv := by
    apply LinearEquiv.ext
    intro u
    exact (EuclideanSpace.equiv (Fin q) ℂ).symm_apply_apply (fc u)
  have hm := hmetric x hx L (D * ‖η - ξ‖) (mul_nonneg hD (norm_nonneg _)) hnorm v
  rw [hfFrame, heFrame] at hm
  change (k.pairing x (fc.symm (L (ec v))) (fc.symm (L (ec v)))).re ≤
    C₀ * (D * ‖η - ξ‖) ^ 2 * (h.pairing x v v).re at hm
  rw [htransport] at hm
  calc
    (k.pairing x ((p x (covectorFromChart c x η) - p x (covectorFromChart c x ξ)) v)
        ((p x (covectorFromChart c x η) - p x (covectorFromChart c x ξ)) v)).re
        ≤ C₀ * (D * ‖η - ξ‖) ^ 2 * (h.pairing x v v).re := hm
    _ = (C₀ * D ^ 2) * ‖η - ξ‖ ^ 2 * (h.pairing x v v).re := by ring

end AtiyahSinger

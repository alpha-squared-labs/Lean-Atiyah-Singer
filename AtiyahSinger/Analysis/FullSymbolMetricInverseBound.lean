/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.NativeAtlasCovariantSobolev
public import AtiyahSinger.Analysis.NativeAtlasFullEllipticity
public import AtiyahSinger.Geometry.CompactFrameMetricBound

/-!
# The actual full-symbol inverse in the specified Hermitian metrics

Public module ID: M0654.

Compact-local full-symbol ellipticity in the original native frames gives
one high-frequency radius and a uniform inverse estimate for the same fiber
map. The original smooth metrics convert this coordinate bound to an energy
bound on that compact window. The inverse is the actual inverse of the full
native symbol, and the frequency is the original chart coordinate of the
specified covector. No homogeneous symbol or unrelated fiber norm is substituted.
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
set_option maxHeartbeats 1600000 in
-- Transfer the actual native inverse estimate through the two original frame comparisons.
/-- Full ellipticity controls the actual native fiber inverse in the original smooth metrics. -/
theorem IsEllipticFullGlobalSymbol.exists_compact_metric_inverse_bound
    (p : GlobalSymbolFunction (n := n) E F)
    (hp : IsEllipticFullGlobalSymbol (r := r) (q := q) E F 1 p)
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
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ (x : M) (_hx : x ∈ K)
      (η : CotangentFiber (n := n) x), R ≤ ‖covectorInChart c x η‖ →
      (p x η).IsInvertible ∧ ∀ v : F x,
        (h.pairing x ((p x η).inverse v) ((p x η).inverse v)).re ≤
          C / (1 + ‖covectorInChart c x η‖) ^ 2 * (k.pairing x v v).re := by
  classical
  -- Ellipticity is applied on the compact image of precisely the original base window.
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
  obtain ⟨R, M₀, hR, hM₀, hbound⟩ := hp c hc e f (c '' K) hwindow himage
  let : MeasurableSpace M := borel M
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  obtain ⟨C₀, hC₀, hmetric⟩ := A.exists_compact_frame_metric_bound B g
    h.toContinuousHermitianMetric k.toContinuousHermitianMetric
    h.isSmoothHermitianMetric_nativeAtlas k.isSmoothHermitianMetric_nativeAtlas
    c hc ⟨e, inferInstance⟩ ⟨f, inferInstance⟩ K hK hKe hKf
  refine ⟨R, C₀ * M₀ ^ 2, hR, mul_nonneg hC₀.le (sq_nonneg M₀), ?_⟩
  intro x hx η hη
  let ξ := covectorInChart c x η
  let P := p x η
  let ec := e.continuousLinearEquivAt ℂ x (hKe hx).2
  let fc := f.continuousLinearEquivAt ℂ x (hKf hx).2
  let a := globalSymbolInChart E F p c e f (c x) ξ
  have ha : a = fc.toContinuousLinearMap.comp (P.comp ec.symm.toContinuousLinearMap) := by
    dsimp only [a, globalSymbolInChart]
    rw [c.left_inv (hKe hx).1, covectorFromChart_covectorInChart c hc x (hKe hx).1 η]
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) (hKf hx).2,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) (hKe hx).2]
  obtain ⟨hai, hab⟩ := hbound (c x) ⟨x, hx, rfl⟩ ξ hη
  have hPi : P.IsInvertible := by
    change a.IsInvertible at hai
    rw [ha] at hai
    simpa only [ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv] using hai
  refine ⟨hPi, ?_⟩
  intro v
  have hbinv : ‖a.inverse‖ ≤ M₀ / (1 + ‖ξ‖) := by
    simpa only [a, Real.rpow_neg_one, div_eq_mul_inv] using hab
  have htransport : ec.symm (a.inverse (fc v)) = P.inverse v := by
    rw [ha, ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_symm, fc.symm_apply_apply, ec.symm_apply_apply]
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
  have hm := hmetric x hx a.inverse (M₀ / (1 + ‖ξ‖)) (by positivity) hbinv v
  rw [heFrame, hfFrame] at hm
  change (h.pairing x (ec.symm (a.inverse (fc v))) (ec.symm (a.inverse (fc v)))).re ≤
    C₀ * (M₀ / (1 + ‖ξ‖)) ^ 2 * (k.pairing x v v).re at hm
  rw [htransport] at hm
  calc
    (h.pairing x (P.inverse v) (P.inverse v)).re
        ≤ C₀ * (M₀ / (1 + ‖ξ‖)) ^ 2 * (k.pairing x v v).re := hm
    _ = C₀ * M₀ ^ 2 / (1 + ‖ξ‖) ^ 2 * (k.pairing x v v).re := by
      simp only [div_pow, mul_div_assoc]

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.FullSymbolCompactDeviation
public import AtiyahSinger.Analysis.GlobalFullSymbolEllipticity

/-!
# The actual inverse of a globally invertible full symbol

Public module ID: M2292.

Smoothness of an everywhere invertible full cotangent Hom function gives smoothness of
its actual inverse at every frequency. If the original function is an order-m symbol with
quantitative full ellipticity, that same inverse is a symbol of order -m. The proof reuses
the existing compact-local cutoff inverse, subtracts it from the actual smooth inverse on
a compact neighborhood, and controls the bounded-frequency difference by smoothing.
No order estimate for the desired inverse is assumed, and the two original bundles are
only reversed. No compact base, common model rank or homogeneous leading term is needed.

Sources: SG III.4.2--4.4 and Remark 4.7 for inverse-symbol estimates. The explicit
all-frequency formulation is a project supplement using the existing local estimates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The actual inverse of a smooth full Hom function is smooth wherever every map is invertible. -/
theorem isSmoothFullGlobalSymbol_inverse
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothFullGlobalSymbol (r := r) (q := q) E F a)
    (hi : ∀ x ξ, (a x ξ).IsInvertible) :
    IsSmoothFullGlobalSymbol (r := q) (q := r) F E (globalSymbolInverse a) := by
  /- In each original chart, transport invertibility through the same two frames.
  Smooth inversion on the open space of continuous linear equivalences applies to that
  original matrix function. The existing inverse frame formula returns the native inverse. -/
  intro c hc f e _ _
  let U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    symbolChartDomain E F c e f ×ˢ univ
  let A := Function.uncurry (globalSymbolInChart E F a c e f)
  have hinv (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (hz : z ∈ U) : (A z).IsInvertible := by
    change ((f.continuousLinearMapAt ℂ (c.symm z.1)).comp
      ((a (c.symm z.1) (covectorFromChart c (c.symm z.1) z.2)).comp
        (e.symmL ℂ (c.symm z.1)))).IsInvertible
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hz.1.2,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hz.1.1.2]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      ((hi _ _).comp ContinuousLinearMap.isInvertible_equiv)
  -- Complex smooth inversion is real smooth at every original coordinate value.
  have hInv : ContDiffOn ℝ ∞ (fun z ↦ (A z).inverse) U := by
    intro z hz
    exact ((hinv z hz).contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ
      |>.comp_contDiffWithinAt z (hs c hc e f z hz)
  have hdomain : symbolChartDomain F E c f e ×ˢ univ = U := by
    ext z
    simp only [U, symbolChartDomain, Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hdomain]
  apply hInv.congr
  intro z hz
  exact globalSymbolInChart_globalSymbolInverse a c e f z.1 z.2 hz.1

/-- An everywhere invertible quantitatively elliptic symbol has its actual order-minus-m inverse. -/
theorem isGlobalSymbol_globalSymbolInverse_of_isInvertible {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (he : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (hi : ∀ x ξ, (a.val x ξ).IsInvertible) :
    IsGlobalSymbol (r := q) (q := r) F E (-m) (globalSymbolInverse a.val) := by
  /- First obtain actual inverse smoothness without any inverse growth premise. In each
  chart, the existing cutoff inverse agrees with it beyond a compact-local frequency radius.
  On a compact neighborhood their smooth difference is zero at high frequencies, hence
  smoothing. Add that difference back to recover estimates for the actual original inverse. -/
  have hs := isSmoothFullGlobalSymbol_inverse a.val a.property.isSmoothFull hi
  intro c hc f e _ _
  let U := symbolChartDomain E F c e f
  let p := globalSymbolInChart E F a.val c e f
  let b := globalSymbolInChart F E (globalSymbolInverse a.val) c f e
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have hdomain : symbolChartDomain F E c f e = U := by
    ext z
    simp only [U, symbolChartDomain, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hdomain]
  change IsSymbol U (-m) b
  have hb : ContDiffOn ℝ ∞ (Function.uncurry b) (U ×ˢ univ) := by
    simpa only [b, hdomain] using hs c hc f e
  -- A compact-local comparison symbol supplies high-frequency recovery of the same inverse.
  obtain ⟨v, hv, hrecover⟩ := exists_inverse_symbol_of_isEllipticFullSymbol hU p
    (a.property c hc e f) (he c hc e f)
  refine ⟨hb, ?_⟩
  intro K hKU hK i j
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  have hint : interior K' ⊆ U := interior_subset.trans hK'U
  obtain ⟨R, _hR, heq⟩ := hrecover K' hK'U hK'
  -- On the enlarged open neighborhood the actual difference has bounded frequency support.
  have hdiff : ContDiffOn ℝ ∞ (Function.uncurry (b - v)) (interior K' ×ˢ univ) :=
    (hb.sub hv.1).mono (Set.prod_mono hint subset_rfl)
  have hsupp : ∀ z ∈ interior K', ∀ η, R ≤ ‖η‖ → (b - v) z η = 0 := by
    intro z hz η hη
    have hactual : b z η = (p z η).inverse :=
      globalSymbolInChart_globalSymbolInverse a.val c e f z η (hint hz)
    exact sub_eq_zero.mpr (hactual.trans (heq z (interior_subset hz) η hη).symm)
  have hsmall : IsSymbol (interior K') (-m) (b - v) :=
    isSmoothingSymbol_of_frequency_support isOpen_interior (b - v) R hdiff hsupp (-m)
  have hsum : IsSymbol (interior K') (-m) b := by
    simpa only [sub_add_cancel] using IsSymbol.add isOpen_interior hsmall (hv.restrict hint)
  exact hsum.2 K hKK' hK i j

end AtiyahSinger

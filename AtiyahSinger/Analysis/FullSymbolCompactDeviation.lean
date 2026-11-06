/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.GlobalSymbol

/-!
# Smooth changes at bounded cotangent frequencies

Public module ID: M2290.

A smooth full cotangent Hom function supported in a bounded metric-frequency disk has
every symbol order. The proof converts the metric bound into a coordinate bound on an
enlarged compact chart neighborhood, then uses the existing local smoothing theorem.
Consequently a smooth change at bounded frequencies preserves the order and principal
class of the original symbol. The actual fiber maps and both bundle frames are retained.

Sources: SG III.3, the standard smoothing-symbol consequence of the symbol estimates.
The explicit metric-disk formulation is a project supplement used for radial freezing.
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

/-- Smoothness at every cotangent frequency, with no growth condition. -/
def IsSmoothFullGlobalSymbol (E F : M → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
    [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
    (a : GlobalSymbolFunction (n := n) E F) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E))
        (f : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F))
        [MemTrivializationAtlas e] [MemTrivializationAtlas f],
        ContDiffOn ℝ ∞ (Function.uncurry (globalSymbolInChart E F a c e f))
          (symbolChartDomain E F c e f ×ˢ univ)

/-- A full symbol's defining regularity includes smoothness at zero frequency. -/
theorem IsGlobalSymbol.isSmoothFull {m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsGlobalSymbol (r := r) (q := q) E F m a) :
    IsSmoothFullGlobalSymbol (r := r) (q := q) E F a :=
  fun c hc e f _ _ ↦ (ha c hc e f).1

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Smoothness and bounded metric-frequency support imply every symbol order. -/
theorem isGlobalSymbol_of_metric_frequency_support
    (a : GlobalSymbolFunction (n := n) E F)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ)
    (ha : IsSmoothFullGlobalSymbol (r := r) (q := q) E F a)
    (hsupp : ∀ x ξ, R ≤ g.length x ξ → a x ξ = 0) (m : ℝ) :
    IsGlobalSymbol (r := r) (q := q) E F m a := by
  /- First enlarge each compact base set inside the valid chart/frame domain.
  A positive metric-to-coordinate comparison on that neighborhood gives one frequency
  radius for the zero symbol. The local smoothing theorem then controls all mixed
  derivatives; restricting back to the original compact set retains those estimates. -/
  intro c hc e f _ _
  let V := symbolChartDomain E F c e f
  let p := globalSymbolInChart E F a c e f
  have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
  have hp : ContDiffOn ℝ ∞ (Function.uncurry p) (V ×ˢ univ) := ha c hc e f
  refine ⟨hp, ?_⟩
  intro K hKV hK i j
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  have hint : interior K' ⊆ V := interior_subset.trans hK'V
  have hK'c : K' ⊆ c.target := fun z hz ↦ (hK'V hz).1.1
  obtain ⟨b, B, hb, _hB, hbounds⟩ := g.exists_length_bounds_on c hc K' hK' hK'c
  let L : ℝ := max R 0 / b
  have hsupport : ∀ z ∈ interior K', ∀ η, L ≤ ‖η‖ → p z η = 0 := by
    intro z hz η hη
    have hmetric : R ≤ g.length (c.symm z) (covectorFromChart c (c.symm z) η) := by
      have hcoord : max R 0 ≤ b * ‖η‖ := by
        simpa only [mul_comm] using (div_le_iff₀ hb).mp hη
      exact (le_max_left R 0).trans (hcoord.trans (hbounds z (interior_subset hz) η).1)
    change (f.continuousLinearMapAt ℂ (c.symm z)).comp
      ((a (c.symm z) (covectorFromChart c (c.symm z) η)).comp
        (e.symmL ℂ (c.symm z))) = 0
    rw [hsupp _ _ hmetric]
    simp
  have hsmoothing := isSmoothingSymbol_of_frequency_support isOpen_interior p L
    (hp.mono (Set.prod_mono hint subset_rfl)) hsupport m
  exact hsmoothing.2 K hKK' hK i j

/-- A smooth change confined to a metric-frequency disk preserves the original symbol order. -/
theorem isGlobalSymbol_of_eq_metric_high_frequency {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : GlobalSymbolFunction (n := n) E F)
    (hb : IsSmoothFullGlobalSymbol (r := r) (q := q) E F b)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ)
    (hab : ∀ x ξ, R ≤ g.length x ξ → b x ξ = a.val x ξ) :
    IsGlobalSymbol (r := r) (q := q) E F m b := by
  /- The actual difference is smooth and zero outside the supplied metric disk.
  Its every-order bound, added to the original symbol bound, gives the same order
  for b without a separate growth hypothesis. -/
  have hd : IsSmoothFullGlobalSymbol (r := r) (q := q) E F (b - a.val) := by
    intro c hc e f _ _
    have hsub : globalSymbolInChart E F (b - a.val) c e f =
        globalSymbolInChart E F b c e f - globalSymbolInChart E F a.val c e f := by
      ext z η v
      simp [globalSymbolInChart]
    rw [hsub]
    exact (hb c hc e f).sub (a.property c hc e f).1
  have hsupp : ∀ x ξ, R ≤ g.length x ξ → (b - a.val) x ξ = 0 := by
    intro x ξ hξ
    exact sub_eq_zero.mpr (hab x ξ hξ)
  have hsum := (isGlobalSymbol_of_metric_frequency_support (b - a.val) g R hd hsupp m).add
    a.property
  simpa only [sub_add_cancel] using hsum

/-- Agreement at large metric cotangent frequencies gives equality of principal classes. -/
theorem globalPrincipalSymbolClass_eq_of_eq_metric_high_frequency {m : ℝ}
    (a b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ)
    (hab : ∀ x ξ, R ≤ g.length x ξ → a.val x ξ = b.val x ξ) :
    globalPrincipalSymbolClass E F m a = globalPrincipalSymbolClass E F m b := by
  /- The smooth bounded-frequency difference has order m-1, which is exactly
  the denominator of the original principal quotient. -/
  apply (globalPrincipalSymbolClass_eq_iff E F m a b).mpr
  have hd : IsSmoothFullGlobalSymbol (r := r) (q := q) E F (a.val - b.val) := by
    intro c hc e f _ _
    have hsub : globalSymbolInChart E F (a.val - b.val) c e f =
        globalSymbolInChart E F a.val c e f - globalSymbolInChart E F b.val c e f := by
      ext z η v
      simp [globalSymbolInChart]
    rw [hsub]
    exact (a.property c hc e f).1.sub (b.property c hc e f).1
  have hsupp : ∀ x ξ, R ≤ g.length x ξ → (a.val - b.val) x ξ = 0 := by
    intro x ξ hξ
    exact sub_eq_zero.mpr (hab x ξ hξ)
  exact isGlobalSymbol_of_metric_frequency_support (a.val - b.val) g R hd hsupp (m - 1)

end AtiyahSinger

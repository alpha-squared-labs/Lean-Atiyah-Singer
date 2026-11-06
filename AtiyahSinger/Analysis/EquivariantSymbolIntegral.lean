/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantLowerOrderCocycle
public import AtiyahSinger.Analysis.EquivariantSymbolJetFamilies
public import AtiyahSinger.Analysis.GlobalSymbolIntegral

import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Integration of the original lower-order symbol cocycle

Public module ID: M0596.

Pointwise lower-order geometric orbit differences have uniform lower-order
seminorm bounds by the previously established Baire and cocycle argument.
Their mixed and full coordinate jets are jointly continuous for the original
topological group action. Compact global-symbol integration therefore preserves
the lower order in the same original Hom fibers for every finite measure.

This proves the symbol-integrability step in fixed-principal-class averaging.
The identification with the principal symbol of the actual averaged PDO remains
a separate local-coordinate and finite-partition comparison.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open Bundle MeasureTheory Set Topology
open scoped Manifold ContDiff
set_option maxSynthPendingDepth 20
variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)

variable [hG : IsManifold IG ∞ G]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)


variable [CompactSpace G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G]

set_option maxHeartbeats 1200000 in
-- The two derivative identities retain the original order-m regularity and m-1 estimates.
include hG hM hE hF hσ hτ in
/-- Any finite-measure integral of the original pointwise lower-order orbit cocycle is
an original lower-order global symbol; no stronger symbol-topology continuity is assumed. -/
theorem isGlobalSymbol_integral_lowerOrder_cocycle (ν : Measure G) [IsFiniteMeasure ν]
    (m : ℝ) (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hLower : ∀ g, IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
      (equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val)) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
      (fun x ξ ↦ ∫ g, (equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val) x ξ ∂ν) := by
  let a (g : G) : globalSymbolSpace (n := n) (r := r) (q := q) E F (m - 1) :=
    ⟨equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val, hLower g⟩
  have hone : equivariantGlobalSymbolLinearMap IG σ τ 1 p.val = p.val :=
    congrArg (fun T ↦ T p.val)
      (equivariantGlobalSymbolAction_properties IG σ τ hσ hτ).2.1
  -- The compact-group cocycle supplies the estimates in the stronger lower-order seminorms.
  apply isGlobalSymbol_integral_of_continuous_jets ν a
  · intro c hc e f _ _ i j
    let X := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, X)
    let U := symbolChartDomain E F c e f
    have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
    let b (g : G) := globalSymbolInChart E F
      (equivariantGlobalSymbolLinearMap IG σ τ g p.val) c e f
    let b₀ := globalSymbolInChart E F p.val c e f
    have hb (g : G) : IsSymbol U m (b g) :=
      (equivariantGlobalSymbolRepresentation IG σ τ hσ hτ m g p).property c hc e f
    have hb₀ : IsSymbol U m b₀ := p.property c hc e f
    have hraw := continuousOn_symbolDerivative_equivariantGlobalSymbol IG σ τ hσ hτ
      p c hc e f i j
    have hconst : ContinuousOn (fun z : G × (X × X) ↦
        symbolDerivative b₀ i j z.2.1 z.2.2) (univ ×ˢ (U ×ˢ univ)) := by
      have h := hraw.comp
        (show Continuous (fun z : G × (X × X) ↦ ((1 : G), z.2)) from
          continuous_const.prodMk continuous_snd).continuousOn
        (fun z (hz : z ∈ univ ×ˢ (U ×ˢ univ)) ↦ hz.2.1)
      simpa only [Function.comp_def, hone, b₀] using h
    have hdiff := (hraw.mono (fun _ hz ↦ hz.2.1)).sub hconst
    apply hdiff.congr
    intro z hz
    have hcoord : globalSymbolInChart E F (a z.1).val c e f = b z.1 - b₀ := by
      ext x ξ v
      simp [a, b, b₀, globalSymbolInChart]
    change symbolDerivative (globalSymbolInChart E F (a z.1).val c e f)
      i j z.2.1 z.2.2 = symbolDerivative (b z.1) i j z.2.1 z.2.2 -
        symbolDerivative b₀ i j z.2.1 z.2.2
    rw [hcoord]
    -- Differentiate the difference at the original frequency, then in the base variable.
    have hfreq (s : SymbolFunction n r q) (hs : IsSymbol U m s) :
        ContDiffAt ℝ ∞ (fun x ↦ iteratedFDeriv ℝ j (s x) z.2.2) z.2.1 := by
      have hpair : ContMDiffOn (I.prod I)
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          (Function.uncurry s) (U ×ˢ univ) := by
        intro w hw
        exact ((hs.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds hw)).contMDiffAt.comp w
          (contMDiffAt_fst.prodMk_space contMDiffAt_snd)).contMDiffWithinAt
      have h := (contMDiffOn_iteratedFDeriv_parameter I (hU.prod isOpen_univ)
        hpair j).contMDiffAt (x := z.2)
          ((hU.prod isOpen_univ).mem_nhds ⟨hz.2.1, mem_univ z.2.2⟩)
      exact (h.comp z.2.1 (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
    have hnear : (fun x ↦ iteratedFDeriv ℝ j ((b z.1 - b₀) x) z.2.2) =ᶠ[nhds z.2.1]
        (fun x ↦ iteratedFDeriv ℝ j (b z.1 x) z.2.2 -
          iteratedFDeriv ℝ j (b₀ x) z.2.2) := by
      filter_upwards [hU.mem_nhds hz.2.1] with x hx
      change iteratedFDeriv ℝ j (fun η ↦ b z.1 x η - b₀ x η) z.2.2 = _
      apply iteratedFDeriv_sub_apply
      · exact (((hb z.1).1.contDiffAt (x := (x, z.2.2)) ((hU.prod isOpen_univ).mem_nhds
          ⟨hx, mem_univ z.2.2⟩)).comp z.2.2
            ((contDiffAt_const (c := x)).prodMk contDiffAt_id)).of_le (by simp)
      · exact ((hb₀.1.contDiffAt (x := (x, z.2.2)) ((hU.prod isOpen_univ).mem_nhds
          ⟨hx, mem_univ z.2.2⟩)).comp z.2.2
            ((contDiffAt_const (c := x)).prodMk contDiffAt_id)).of_le (by simp)
    exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_sub_apply ((hfreq (b z.1) (hb z.1)).of_le (by simp))
        ((hfreq b₀ hb₀).of_le (by simp)))
  · intro c hc e f _ _ k
    let X := EuclideanSpace ℝ (Fin n)
    let U := symbolChartDomain E F c e f
    have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
    let b (g : G) := globalSymbolInChart E F
      (equivariantGlobalSymbolLinearMap IG σ τ g p.val) c e f
    let b₀ := globalSymbolInChart E F p.val c e f
    have hraw := continuousOn_iteratedFDeriv_equivariantGlobalSymbol IG σ τ hσ hτ
      p c hc e f k
    have hconst : ContinuousOn (fun z : G × (X × X) ↦
        iteratedFDeriv ℝ k (Function.uncurry b₀) z.2) (univ ×ˢ (U ×ˢ univ)) := by
      have h := hraw.comp
        (show Continuous (fun z : G × (X × X) ↦ ((1 : G), z.2)) from
          continuous_const.prodMk continuous_snd).continuousOn
        (fun z (hz : z ∈ univ ×ˢ (U ×ˢ univ)) ↦ hz.2.1)
      simpa only [Function.comp_def, hone, b₀] using h
    have hdiff := (hraw.mono (fun _ hz ↦ hz.2.1)).sub hconst
    apply hdiff.congr
    intro z hz
    have hcoord : Function.uncurry (globalSymbolInChart E F (a z.1).val c e f) =
        Function.uncurry (b z.1) - Function.uncurry b₀ := by
      funext w
      apply ContinuousLinearMap.ext
      intro v
      simp [Function.uncurry, a, b, b₀, globalSymbolInChart]
    change iteratedFDeriv ℝ k
      (Function.uncurry (globalSymbolInChart E F (a z.1).val c e f)) z.2 =
        iteratedFDeriv ℝ k (Function.uncurry (b z.1)) z.2 -
          iteratedFDeriv ℝ k (Function.uncurry b₀) z.2
    rw [hcoord]
    have hb : IsSymbol U m (b z.1) :=
      (equivariantGlobalSymbolRepresentation IG σ τ hσ hτ m z.1 p).property c hc e f
    have hb₀ : IsSymbol U m b₀ := p.property c hc e f
    exact iteratedFDeriv_sub_apply
      ((hb.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz.2)).of_le (by simp))
      ((hb₀.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz.2)).of_le (by simp))
  · intro J
    exact bddAbove_range_globalSymbolSeminorm_lowerOrder_cocycle IG σ τ hσ hτ m p hLower J


set_option maxHeartbeats 800000 in
-- Fixed fiber evaluation uses the same original frames as the coordinate jet calculation.
include hG hM hE hF hσ hτ in
/-- Integrating a geometric symbol orbit with fixed principal class multiplies that class
by the total mass, while retaining the actual fiberwise integral as its representative. -/
theorem exists_globalSymbol_integral_of_fixed_principalSymbol
    (ν : Measure G) [IsFiniteMeasure ν] (m : ℝ)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hFixed : ∀ g, equivariantPrincipalSymbolRepresentation IG σ τ hσ hτ m g
      (globalPrincipalSymbolClass E F m p) = globalPrincipalSymbolClass E F m p) :
    ∃ pbar : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
      (∀ x ξ, pbar.val x ξ = ∫ g, equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ ∂ν) ∧
      globalPrincipalSymbolClass E F m pbar =
        (ν.real univ : ℂ) • globalPrincipalSymbolClass E F m p := by
  classical
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  let R := equivariantGlobalSymbolRepresentation IG σ τ hσ hτ m
  -- The ordinary orbit integral uses the original order-m estimates and chart jets.
  have horbit : IsGlobalSymbol (n := n) (r := r) (q := q) E F m
      (fun x ξ ↦ ∫ g, equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ ∂ν) := by
    apply isGlobalSymbol_integral_of_continuous_jets ν (fun g ↦ R g p)
    · intro c hc e f _ _ i j
      exact (continuousOn_symbolDerivative_equivariantGlobalSymbol IG σ τ hσ hτ
        p c hc e f i j).mono (fun _ hz ↦ hz.2.1)
    · intro c hc e f _ _ k
      exact (continuousOn_iteratedFDeriv_equivariantGlobalSymbol IG σ τ hσ hτ
        p c hc e f k).mono (fun _ hz ↦ hz.2.1)
    · intro J
      exact bddAbove_range_globalSymbolSeminorm_equivariant IG σ τ hσ hτ m p J
  let pbar : globalSymbolSpace (n := n) (r := r) (q := q) E F m := ⟨_, horbit⟩
  have hLower (g : G) : IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
      (equivariantGlobalSymbolLinearMap IG σ τ g p.val - p.val) :=
    (globalPrincipalSymbolClass_eq_iff E F m (R g p) p).mp (hFixed g)
  have hd := isGlobalSymbol_integral_lowerOrder_cocycle IG σ τ hσ hτ ν m p hLower
  -- In each original fiber, a valid pair of frames recovers continuity and integrability.
  have hint (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      Integrable (fun g ↦ equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ) ν := by
    let X := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let c := chartAt X x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hc := chart_mem_atlas X x
    have hx : x ∈ c.source := mem_chart_source X x
    have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hz : c x ∈ symbolChartDomain E F c e f := by
      refine ⟨⟨c.map_source hx, ?_⟩, ?_⟩
      · simpa only [mem_preimage, c.left_inv hx] using he
      · simpa only [mem_preimage, c.left_inv hx] using hf
    let η := covectorInChart c x ξ
    have hjet := (continuousOn_iteratedFDeriv_equivariantGlobalSymbol IG σ τ hσ hτ
      p c hc e f 0).comp_continuous
        (continuous_id.prodMk (continuous_const (y := (c x, η)))) (fun _ ↦ hz)
    have hvalues : Continuous (fun g : G ↦ globalSymbolInChart E F
        (equivariantGlobalSymbolLinearMap IG σ τ g p.val) c e f (c x) η) := by
      have h := (continuousMultilinearCurryFin0 ℝ (X × X) H).continuous.comp hjet
      change Continuous (fun g : G ↦ (iteratedFDeriv ℝ 0 (Function.uncurry
        (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ g p.val)
          c e f)) (c x, η)).curry0) at h
      simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply,
        Function.comp_def, Function.uncurry, id_eq] using h
    let A := (e.linearEquivAt ℂ x he).toContinuousLinearEquiv
    let B := (f.linearEquivAt ℂ x hf).toContinuousLinearEquiv
    let C := A.arrowCongr B
    have hcoord (g : G) : globalSymbolInChart E F
        (equivariantGlobalSymbolLinearMap IG σ τ g p.val) c e f (c x) η =
          C (equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ) := by
      rw [globalSymbolInChart_covectorInChart E F _ c hc e f x hx ξ]
      apply ContinuousLinearMap.ext
      intro v
      simp only [C, ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearMap.comp_apply]
      change _ = f.linearEquivAt ℂ x hf
        ((equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ)
          ((e.linearEquivAt ℂ x he).symm v))
      rw [Trivialization.linearEquivAt_symm_apply, e.symmL_apply he]
      exact f.continuousLinearMapAt_apply_of_mem ℂ hf _
    have hactual : Continuous (fun g ↦ equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ) := by
      convert C.symm.continuous.comp hvalues using 1
      funext g
      simp only [Function.comp_apply, hcoord, C.symm_apply_apply]
    exact hactual.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨pbar, fun _ _ ↦ rfl, ?_⟩
  rw [← map_smul]
  apply (globalPrincipalSymbolClass_eq_iff E F m pbar ((ν.real univ : ℂ) • p)).mpr
  convert hd using 1
  funext x ξ
  change (∫ g, equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ ∂ν) -
    (ν.real univ : ℂ) • p.val x ξ =
      ∫ g, (equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ - p.val x ξ) ∂ν
  rw [integral_sub (hint x ξ) (integrable_const _), integral_const, Complex.coe_smul]

end AtiyahSinger

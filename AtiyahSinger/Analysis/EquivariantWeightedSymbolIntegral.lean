/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolIntegral

/-!
# Weighted integration on the original principal symbol quotient

Public module ID: M0603.

A continuous scalar weight preserves the uniform orbit estimates on the compact
group. Integrating in the actual Hom fibers therefore defines a linear map on
symbols. The same construction one order lower shows that it descends to the
original principal symbol quotient. These maps compare local averages with the
same global symbol class and assemble over a finite partition of unity.
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


variable [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]

set_option maxHeartbeats 1000000 in
-- Both iterated derivative stages retain the actual chart and two bundle frames.
include hG hM hE hF hσ hτ in
/-- Continuous weights preserve the original order of an integrated geometric symbol orbit. -/
theorem isGlobalSymbol_weighted_equivariant_integral
    (ν : Measure G) [IsFiniteMeasure ν] (w : G → ℂ) (hw : Continuous w)
    {m : ℝ} (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m
      (fun x ξ ↦ ∫ g, w g • equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ ∂ν) := by
  let R := equivariantGlobalSymbolRepresentation IG σ τ hσ hτ m
  apply isGlobalSymbol_integral_of_continuous_jets ν (fun g ↦ w g • R g p)
  · intro c hc e f _ _ i j
    let X := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, X)
    let U := symbolChartDomain E F c e f
    have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
    let b (g : G) := globalSymbolInChart E F (R g p).val c e f
    have hb (g : G) : IsSymbol U m (b g) := (R g p).property c hc e f
    have hraw := (continuousOn_symbolDerivative_equivariantGlobalSymbol IG σ τ hσ hτ
      p c hc e f i j).mono (fun _ (hz : _ ∈ univ ×ˢ (U ×ˢ univ)) ↦ hz.2.1)
    apply ((hw.comp continuous_fst).continuousOn.smul hraw).congr
    intro z hz
    change symbolDerivative
      (globalSymbolInChart E F (w z.1 • (R z.1 p).val) c e f) i j z.2.1 z.2.2 = _
    rw [globalSymbolInChart_smul]
    -- The parameter weight is constant in both the base and frequency variables.
    have hs : ContMDiffOn (I.prod I)
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (Function.uncurry (b z.1)) (U ×ˢ univ) := by
      intro y hy
      exact (((hb z.1).1.contDiffAt ((hU.prod isOpen_univ).mem_nhds hy)).contMDiffAt.comp y
        (contMDiffAt_fst.prodMk_space contMDiffAt_snd)).contMDiffWithinAt
    have hparam := (contMDiffOn_iteratedFDeriv_parameter I (hU.prod isOpen_univ)
      hs j).contMDiffAt (x := z.2) ((hU.prod isOpen_univ).mem_nhds hz.2)
    have hnear : (fun x ↦ iteratedFDeriv ℝ j ((w z.1 • b z.1) x) z.2.2) =ᶠ[𝓝 z.2.1]
        (fun x ↦ w z.1 • iteratedFDeriv ℝ j (b z.1 x) z.2.2) := by
      filter_upwards [hU.mem_nhds hz.2.1] with x hx
      have hf : ContDiffAt ℝ ∞ (b z.1 x) z.2.2 :=
        ((hb z.1).1.contDiffAt (x := (x, z.2.2)) ((hU.prod isOpen_univ).mem_nhds
          ⟨hx, mem_univ z.2.2⟩)).comp z.2.2
          ((contDiffAt_const (c := x)).prodMk contDiffAt_id)
      exact iteratedFDeriv_const_smul_apply (a := w z.1) (hf.of_le (by simp))
    exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_const_smul_apply (a := w z.1)
        ((hparam.comp z.2.1 (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.of_le
          (by simp)))
  · intro c hc e f _ _ k
    let U := symbolChartDomain E F c e f
    have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
    have hraw := (continuousOn_iteratedFDeriv_equivariantGlobalSymbol IG σ τ hσ hτ
      p c hc e f k).mono (fun _ (hz : _ ∈ univ ×ˢ (U ×ˢ univ)) ↦ hz.2.1)
    apply ((hw.comp continuous_fst).continuousOn.smul hraw).congr
    intro z hz
    change iteratedFDeriv ℝ k (Function.uncurry
      (globalSymbolInChart E F (w z.1 • (R z.1 p).val) c e f)) z.2 = _
    rw [globalSymbolInChart_smul]
    exact iteratedFDeriv_const_smul_apply (a := w z.1)
      (((R z.1 p).property c hc e f).1.contDiffAt
        ((hU.prod isOpen_univ).mem_nhds hz.2) |>.of_le (by simp))
  · intro J
    -- Compactness bounds the scalar and the original orbit in each chosen seminorm.
    obtain ⟨C, hC⟩ := bddAbove_range_globalSymbolSeminorm_equivariant IG σ τ hσ hτ m p J
    obtain ⟨D, hD⟩ := isCompact_range hw.norm |>.bddAbove
    refine ⟨max D 0 * max C 0, ?_⟩
    rintro _ ⟨g, rfl⟩
    change globalSymbolSeminorm E F m J (w g • R g p) ≤ _
    rw [map_smul_eq_mul]
    exact mul_le_mul ((hD (mem_range_self g)).trans (le_max_left _ _))
      ((hC (mem_range_self g)).trans (le_max_left _ _))
      (apply_nonneg _ _) (le_max_of_le_right (le_refl 0))

set_option maxHeartbeats 500000 in
-- Recover each genuine fiber map from its zeroth coordinate jet.
include hG hM hσ hτ in
omit hE hF [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- Evaluation of an original geometric symbol orbit is continuous in each genuine Hom fiber. -/
theorem continuous_equivariantGlobalSymbol_apply {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    Continuous (fun g ↦ equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ) := by
  classical
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
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
  exact hactual

variable (ν : Measure G) [IsFiniteMeasure ν] (w : G → ℂ) (hw : Continuous w) (m : ℝ)

/-- The weighted orbit integral as a complex-linear map on the actual symbol module. -/
def equivariantWeightedSymbolIntegral :
    globalSymbolSpace (n := n) (r := r) (q := q) E F m →ₗ[ℂ]
      globalSymbolSpace (n := n) (r := r) (q := q) E F m := by
  classical
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  have hint (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
      (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      Integrable (fun g ↦ w g • equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ) ν :=
    (hw.smul (continuous_equivariantGlobalSymbol_apply IG σ τ hσ hτ p x ξ))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact {
    toFun := fun p ↦ ⟨_, isGlobalSymbol_weighted_equivariant_integral
      IG σ τ hσ hτ ν w hw p⟩
    map_add' := fun p q ↦ by
      apply Subtype.ext
      funext x ξ
      change (∫ g, w g • equivariantGlobalSymbolLinearMap IG σ τ g (p + q).val x ξ ∂ν) = _
      simp only [Submodule.coe_add, map_add, Pi.add_apply, smul_add]
      exact integral_add (hint p x ξ) (hint q x ξ)
    map_smul' := fun c p ↦ by
      apply Subtype.ext
      funext x ξ
      change (∫ g, w g • equivariantGlobalSymbolLinearMap IG σ τ g (c • p).val x ξ ∂ν) = _
      simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_comm (w _)]
      exact integral_smul c _ }

/-- Evaluation of the symbol integral is the original weighted fiberwise integral. -/
theorem equivariantWeightedSymbolIntegral_apply
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    (equivariantWeightedSymbolIntegral IG σ τ hσ hτ ν w hw m p).val x ξ =
      ∫ g, w g • equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ ∂ν := rfl

/-- The same integration one order lower makes the map descend to the original quotient. -/
def equivariantWeightedPrincipalSymbolIntegral :
    GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m →ₗ[ℂ]
      GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  (lowerOrderGlobalSymbols E F m).mapQ (lowerOrderGlobalSymbols E F m)
    (equivariantWeightedSymbolIntegral IG σ τ hσ hτ ν w hw m) (by
      intro p hp
      exact isGlobalSymbol_weighted_equivariant_integral IG σ τ hσ hτ ν w hw
        (⟨p.val, hp⟩ : globalSymbolSpace (n := n) (r := r) (q := q) E F (m - 1)))

/-- The quotient map computes using the same representative as the symbol integral. -/
theorem equivariantWeightedPrincipalSymbolIntegral_class
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    equivariantWeightedPrincipalSymbolIntegral IG σ τ hσ hτ ν w hw m
        (globalPrincipalSymbolClass E F m p) =
      globalPrincipalSymbolClass E F m
        (equivariantWeightedSymbolIntegral IG σ τ hσ hτ ν w hw m p) := rfl

omit w hw in
/-- A finite scalar partition integrates to the unweighted action on each principal class. -/
theorem equivariantWeightedPrincipalSymbolIntegral_sum {ι : Type*} [Fintype ι]
    (w : ι → G → ℂ) (hw : ∀ i, Continuous (w i))
    (hsum : ∀ g, ∑ i, w i g = 1)
    (a : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (∑ i, equivariantWeightedPrincipalSymbolIntegral IG σ τ hσ hτ ν (w i) (hw i) m a) =
      equivariantWeightedPrincipalSymbolIntegral IG σ τ hσ hτ ν (fun _ ↦ 1)
        continuous_const m a := by
  classical
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  obtain ⟨p, rfl⟩ := globalPrincipalSymbolClass_surjective E F m a
  simp only [equivariantWeightedPrincipalSymbolIntegral_class, ← map_sum]
  apply congrArg (globalPrincipalSymbolClass E F m)
  apply Subtype.ext
  funext x ξ
  rw [Submodule.coe_sum]
  simp only [Finset.sum_apply, equivariantWeightedSymbolIntegral_apply]
  have hint (i : ι) : Integrable (fun g ↦
      w i g • equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ) ν :=
    ((hw i).smul (continuous_equivariantGlobalSymbol_apply IG σ τ hσ hτ p x ξ))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ hint i)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g ↦ by
    dsimp only
    rw [← Finset.sum_smul, hsum g])

variable [T2Space G]

omit w hw in
include hE hF in
/-- Unweighted integration acts on a fixed principal class by the measure's total mass. -/
theorem equivariantWeightedPrincipalSymbolIntegral_one_of_fixed
    (a : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hFixed : ∀ g, equivariantPrincipalSymbolRepresentation IG σ τ hσ hτ m g a = a) :
    equivariantWeightedPrincipalSymbolIntegral IG σ τ hσ hτ ν (fun _ ↦ 1)
        continuous_const m a = (ν.real univ : ℂ) • a := by
  obtain ⟨p, rfl⟩ := globalPrincipalSymbolClass_surjective E F m a
  obtain ⟨pbar, hval, hclass⟩ :=
    exists_globalSymbol_integral_of_fixed_principalSymbol IG σ τ hσ hτ ν m p hFixed
  rw [equivariantWeightedPrincipalSymbolIntegral_class]
  convert hclass using 1
  apply congrArg (globalPrincipalSymbolClass E F m)
  apply Subtype.ext
  funext x ξ
  simp only [equivariantWeightedSymbolIntegral_apply, one_smul]
  exact (hval x ξ).symm

end AtiyahSinger

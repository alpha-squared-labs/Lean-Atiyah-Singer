/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductHorizontalCovector
public import AtiyahSinger.Analysis.PrincipalPseudodifferentialLocalization
public import AtiyahSinger.Geometry.AtlasBundlePresentation

/-!
# The actual horizontal finite full symbol on its target axis

Public module ID: M0863.

The original associated product chart identifies a horizontal target
covector with pullback of the same original base covector. Each active
source chart therefore evaluates the same native base piece at that
covector. The original sphere partition then recovers exactly the finite
sum of original native full symbols. No tensor factor is canceled, so
zero-rank coefficient bundles require no exception.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable {V : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℂ (V y)]
  [TopologicalSpace (TotalSpace Unit V)]
  (A : SmoothComplexBundleAtlas (n := r) V)

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))
local notation "Z" => AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- Compare the original target and active source covectors before summing the partition.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in
/-- The actual horizontal finite factor equals the original native full-symbol sum on the axis. -/
theorem horizontalFullSymbol_axis_eq
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (J : AtlasBundlePresentation A)
    (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (hc₀ : c₀ ∈ atlas X B)
    (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r)) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let CP := associatedSphereProductChart S b₀ c₀ d₀
    let Ci (i : Fin C.size) (j : Fin J.size) :=
      associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    ∀ z ∈ CP.source, ∀ ξ : X,
      let Ξ := covectorFromChart CP z (split.symm (ξ, 0))
      let frequency (i : Fin C.size) (j : Fin J.size) :=
        (split (covectorInChart (Ci i j) z Ξ)).1
      (∑ i, ∑ j, (J.cutoff j (associatedSphereTrivialization S (C.center i) z).2 : ℂ) •
        (C.piece i).globalSymbolFunction (base z)
          (covectorFromChart (C.piece i).chart (base z) (frequency i j))) =
        ∑ i, (C.piece i).globalSymbolFunction (base z) (covectorFromChart c₀ (base z) ξ) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro split
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro CP Ci base z hz ξ Ξ frequency
  let ν := covectorFromChart c₀ (base z) ξ
  let νP := ν.comp (mfderiv (𝓡 (n + r)) (𝓡 n) base z)
  have hzBase : base z ∈ c₀.source := by
    let t₀ := associatedSphereTrivialization S b₀
    have ht : z ∈ t₀.source := hz.1.1
    have hc : (t₀ z).1 ∈ c₀.source := hz.1.2.1
    rwa [t₀.coe_fst ht] at hc
  -- The target horizontal covector is pullback along the actual bundle projection.
  have hcoordinates : covectorInChart CP z νP = split.symm (ξ, 0) := by
    apply split.injective
    rw [split.apply_symm_apply]
    have hp := covectorInChart_associatedSphereProductChart_pullback
      S b₀ c₀ hc₀ d₀ hd₀ z hz ν
    change split (covectorInChart CP z νP) =
      (covectorInChart c₀ (base z) (covectorFromChart c₀ (base z) ξ), 0) at hp
    rw [covectorInChart_covectorFromChart c₀ hc₀ (base z) hzBase ξ] at hp
    exact hp
  have hCP := associatedSphereProductChart_mem_maximalAtlas S b₀ c₀ hc₀ d₀ hd₀
  have hdiff : CP.MDifferentiable (𝓡 (n + r)) (𝓡 (n + r)) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hCP).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hCP).mdifferentiableOn (by simp)⟩
  have hcancel : covectorFromChart CP z (covectorInChart CP z νP) = νP := by
    have hcoord : innerSL ℝ (covectorInChart CP z νP) =
        νP.comp (mfderiv (𝓡 (n + r)) (𝓡 (n + r)) CP.symm (CP z)) := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin (n + r)) ℝ).toBasis.ext
      intro j
      simp [covectorInChart, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right]
      rfl
    ext v
    have hinverse := congrArg (fun L : H →L[ℝ] H ↦ L v) (hdiff.symm_comp_deriv hz)
    change (mfderiv _ _ CP.symm (CP z)) ((mfderiv _ _ CP z) v) = v at hinverse
    calc
      covectorFromChart CP z (covectorInChart CP z νP) v =
          νP ((mfderiv _ _ CP.symm (CP z)) ((mfderiv _ _ CP z) v)) :=
        DFunLike.congr_fun hcoord ((mfderiv _ _ CP z) v)
      _ = νP v := congrArg νP hinverse
  have hpull : Ξ = νP := by
    change covectorFromChart CP z (split.symm (ξ, 0)) = νP
    rw [← hcoordinates, hcancel]
  -- An inactive original base piece vanishes at every covector. Active weights give chart access.
  apply Finset.sum_congr rfl
  intro i _
  let L := C.piece i
  let t := associatedSphereTrivialization S (C.center i)
  let y := (t z).2
  have hpoint (j : Fin J.size) :
      (J.cutoff j y : ℂ) • L.globalSymbolFunction (base z)
        (covectorFromChart L.chart (base z) (frequency i j)) =
      (J.cutoff j y : ℂ) • L.globalSymbolFunction (base z) ν := by
    by_cases hj : J.cutoff j y = 0
    · simp only [hj, Complex.ofReal_zero, zero_smul]
    by_cases hx : base z ∈ L.chart.symm '' (tsupport L.output.cutoff ∩ tsupport L.input.cutoff)
    · obtain ⟨x, hx, hxb⟩ := hx
      have hxs : base z ∈ L.chart.source :=
        hxb ▸ L.chart.map_target (L.output.support_subset hx.1).1
      have hprincipal : base z ∈ (S.trivialization (C.center i)).baseSet :=
        C.piece_support i ⟨x, Or.inl hx.1, hxb⟩
      have htBase : t.baseSet = (S.trivialization (C.center i)).baseSet :=
        (exists_associatedBundleTrivialization S.toIsPrincipalBundle
          (S.trivialization (C.center i)) (S.equivariant (C.center i))).choose_spec.1
      have htz : z ∈ t.source := t.mem_source.mpr (htBase.symm ▸ hprincipal)
      have hzs : z ∈ (Ci i j).source := by
        refine ⟨⟨htz, ?_, (J.support_subset j (subset_tsupport _ hj)).1⟩, Set.mem_univ _⟩
        change (t z).1 ∈ L.chart.source
        rwa [t.coe_fst htz]
      have hfrequency : frequency i j = covectorInChart L.chart (base z) ν := by
        have hs := covectorInChart_associatedSphereProductChart_pullback S (C.center i)
          L.chart L.chart_mem_atlas (J.chart j) (J.chart_mem_atlas j) z hzs ν
        change (split (covectorInChart (Ci i j) z Ξ)).1 = _
        rw [hpull]
        exact congrArg Prod.fst hs
      have hcov : covectorFromChart L.chart (base z) (frequency i j) = ν := by
        rw [hfrequency, covectorFromChart_covectorInChart L.chart L.chart_mem_atlas
          (base z) hxs ν]
      rw [hcov]
    · rw [L.globalSymbolFunction_eq_zero (base z) hx,
        L.globalSymbolFunction_eq_zero (base z) hx]
  calc
    _ = ∑ j, (J.cutoff j y : ℂ) • L.globalSymbolFunction (base z) ν :=
      Finset.sum_congr rfl (fun j _ ↦ hpoint j)
    _ = ((∑ j, J.cutoff j y : ℝ) : ℂ) • L.globalSymbolFunction (base z) ν := by
      rw [Complex.ofReal_sum, Finset.sum_smul]
    _ = L.globalSymbolFunction (base z) ν := by
      rw [J.sum_cutoff y, Complex.ofReal_one, one_smul]

end PrincipalPseudodifferentialLocalization

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteChartHomogeneousTail
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalCutoffRecovery

/-!
# Homogeneous tails of the actual associated horizontal cutoff family

Public module ID: M0867.

The original finite factor uses each refined base piece and each supplied
sphere partition weight. Each localized term has compact support inside its
own associated product chart. Local tails combine under one specified
upstairs cotangent metric, without replacing the horizontal family or assuming
that its full symbol was homogeneous at small frequencies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

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
-- Preserve the actual supports and covectors across the associated product charts.
/-- The original horizontal factor has one global metric tail whenever its pieces do. -/
theorem exists_horizontalCutoff_homogeneous_of_piece_tails
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (J : AtlasBundlePresentation A) (ε : ℝ) (R₀ : Fin C.size → ℝ)
    (hpiece : ∀ i (x : B) (ξ : X) (η : Y) (t : ℝ), 0 < t →
      R₀ i ≤ ‖ξ‖ + ‖η‖ → R₀ i ≤ ‖t • ξ‖ + ‖t • η‖ →
        (productFrequencyCutoff ε ‖t • ξ‖ ‖t • η‖ : ℂ) •
            (C.piece i).globalSymbolFunction x
              (covectorFromChart (C.piece i).chart x (t • ξ)) =
          (t : ℂ) • ((productFrequencyCutoff ε ‖ξ‖ ‖η‖ : ℂ) •
            (C.piece i).globalSymbolFunction x
              (covectorFromChart (C.piece i).chart x ξ))) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := linearModelChartedSpace split.symm Z
    letI := isManifold_linearModelChartedSpace split.symm Z
    let Ci (i : Fin C.size) (j : Fin J.size) :=
      associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let factor := fun (z : Z) (ν : CotangentFiber (n := n + r) z) ↦
      ∑ i, ∑ j,
        let frequency := split (covectorInChart (Ci i j) z ν)
        ((J.cutoff j (associatedSphereTrivialization S (C.center i) z).2 *
          productFrequencyCutoff ε ‖frequency.1‖ ‖frequency.2‖ : ℝ) : ℂ) •
            (C.piece i).globalSymbolFunction (base z)
              (covectorFromChart (C.piece i).chart (base z) frequency.1)
    ∀ g : SmoothCotangentMetric (n := n + r) (M := Z),
      ∃ R : ℝ, 0 < R ∧ ∀ z ν (t : ℝ), 0 < t →
        R ≤ g.length z ν → R ≤ g.length z (t • ν) →
          factor z (t • ν) = (t : ℂ) • factor z ν := by
  classical
  intro split
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro Ci base factor g
  let t (i : Fin C.size) := associatedSphereTrivialization S (C.center i)
  let baseSupport (i : Fin C.size) := (C.piece i).chart.symm ''
    (tsupport (C.piece i).output.cutoff ∩ tsupport (C.piece i).input.cutoff)
  have hbCompact (i : Fin C.size) : IsCompact (baseSupport i) :=
    ((C.piece i).output.compact_support.inter
      (C.piece i).input.compact_support).image_of_continuousOn
      ((C.piece i).chart.continuousOn_symm.mono (fun _ hz ↦
        ((C.piece i).output.support_subset hz.1).1))
  have hbChart (i : Fin C.size) (x : B) (hx : x ∈ baseSupport i) :
      x ∈ (C.piece i).chart.source ∧ x ∈ (C.piece i).input.frame.baseSet ∧
        x ∈ (C.piece i).output.frame.baseSet ∧ x ∈ (S.trivialization (C.center i)).baseSet := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(C.piece i).chart.map_target ((C.piece i).output.support_subset hy.1).1,
      ((C.piece i).input.support_subset hy.2).2,
      ((C.piece i).output.support_subset hy.1).2, C.piece_support i ⟨y, Or.inl hy.1, rfl⟩⟩
  have htBase (i : Fin C.size) : (t i).baseSet = (S.trivialization (C.center i)).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization (C.center i)) (S.equivariant (C.center i))).choose_spec.1
  let support (ij : Fin C.size × Fin J.size) :=
    (t ij.1).toOpenPartialHomeomorph.symm '' (baseSupport ij.1 ×ˢ tsupport (J.cutoff ij.2))
  have htTarget (ij : Fin C.size × Fin J.size) :
      baseSupport ij.1 ×ˢ tsupport (J.cutoff ij.2) ⊆ (t ij.1).target := by
    intro xy hxy
    exact (t ij.1).mem_target.mpr (htBase ij.1 ▸ (hbChart ij.1 xy.1 hxy.1).2.2.2)
  have hsCompact (ij : Fin C.size × Fin J.size) : IsCompact (support ij) :=
    ((hbCompact ij.1).prod (J.compact_support ij.2)).image_of_continuousOn
      ((t ij.1).toOpenPartialHomeomorph.continuousOn_symm.mono (htTarget ij))
  have hsChart (ij : Fin C.size × Fin J.size) : support ij ⊆ (Ci ij.1 ij.2).source := by
    rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    have ht := htTarget ij hxy
    have htvalue : (t ij.1) ((t ij.1).toOpenPartialHomeomorph.symm (x, y)) = (x, y) :=
      (t ij.1).toOpenPartialHomeomorph.right_inv ht
    refine ⟨⟨(t ij.1).toOpenPartialHomeomorph.map_target ht, ?_, ?_⟩, Set.mem_univ _⟩
    · change ((t ij.1) ((t ij.1).toOpenPartialHomeomorph.symm (x, y))).1 ∈
        (C.piece ij.1).chart.source
      rw [htvalue]
      exact (hbChart ij.1 x hxy.1).1
    · change ((t ij.1) ((t ij.1).toOpenPartialHomeomorph.symm (x, y))).2 ∈ (J.chart ij.2).source
      rw [htvalue]
      exact (J.support_subset ij.2 hxy.2).1
  let K (ij : Fin C.size × Fin J.size) := (Ci ij.1 ij.2) '' support ij
  have hK (ij : Fin C.size × Fin J.size) : IsCompact (K ij) :=
    (hsCompact ij).image_of_continuousOn ((Ci ij.1 ij.2).continuousOn.mono (hsChart ij))
  have hKc (ij : Fin C.size × Fin J.size) : K ij ⊆ (Ci ij.1 ij.2).target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Ci ij.1 ij.2).map_source (hsChart ij hz)
  have hCi (ij : Fin C.size × Fin J.size) :
      Ci ij.1 ij.2 ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S (C.center ij.1)
      (C.piece ij.1).chart (C.piece ij.1).chart_mem_atlas
      (J.chart ij.2) (J.chart_mem_atlas ij.2)
  let field (ij : Fin C.size × Fin J.size) (z : Z)
      (ν : CotangentFiber (n := n + r) z) :=
    let frequency := split (covectorInChart (Ci ij.1 ij.2) z ν)
    ((J.cutoff ij.2 (t ij.1 z).2 *
      productFrequencyCutoff ε ‖frequency.1‖ ‖frequency.2‖ : ℝ) : ℂ) •
        (C.piece ij.1).globalSymbolFunction (base z)
          (covectorFromChart (C.piece ij.1).chart (base z) frequency.1)
  have hzero (ij : Fin C.size × Fin J.size) (z : Z)
      (hz : z ∉ (Ci ij.1 ij.2).symm '' K ij) (ν : CotangentFiber (n := n + r) z) :
      field ij z ν = 0 := by
    by_cases hw : J.cutoff ij.2 (t ij.1 z).2 = 0
    · simp only [field, hw, zero_mul, Complex.ofReal_zero, zero_smul]
    have hbase : base z ∉ baseSupport ij.1 := by
      intro hx
      have htz : z ∈ (t ij.1).source :=
        (t ij.1).mem_source.mpr (htBase ij.1 ▸ (hbChart ij.1 (base z) hx).2.2.2)
      have hs : z ∈ support ij := by
        refine ⟨t ij.1 z, ⟨?_, subset_tsupport _ hw⟩,
          (t ij.1).toOpenPartialHomeomorph.left_inv htz⟩
        rwa [(t ij.1).coe_fst htz]
      exact hz ⟨Ci ij.1 ij.2 z, ⟨z, hs, rfl⟩,
        (Ci ij.1 ij.2).left_inv (hsChart ij hs)⟩
    dsimp only [field]
    rw [(C.piece ij.1).globalSymbolFunction_eq_zero (base z) hbase, smul_zero]
  -- The Euclidean product equivalence has its actual operator norm, not an assumed isometry.
  let D := 1 + ‖split.symm.toContinuousLinearMap‖
  have hD : 0 < D := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  have hnorm (ν : H) : ‖ν‖ ≤ D * (‖(split ν).1‖ + ‖(split ν).2‖) := by
    have hsum : ‖split ν‖ ≤ ‖(split ν).1‖ + ‖(split ν).2‖ := by
      exact max_le (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _))
    calc
      ‖ν‖ = ‖split.symm (split ν)‖ := congrArg norm (split.symm_apply_apply ν).symm
      _ ≤ ‖split.symm.toContinuousLinearMap‖ * ‖split ν‖ :=
        split.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ D * (‖(split ν).1‖ + ‖(split ν).2‖) :=
        mul_le_mul (le_add_of_nonneg_left zero_le_one) hsum (norm_nonneg _) hD.le
  have htail (ij : Fin C.size × Fin J.size) (z : Z)
      (hz : z ∈ (Ci ij.1 ij.2).symm '' K ij) (ν : H) (s : ℝ) (hs : 0 < s)
      (hν : D * R₀ ij.1 ≤ ‖ν‖) (hsν : D * R₀ ij.1 ≤ ‖s • ν‖) :
      field ij z (covectorFromChart (Ci ij.1 ij.2) z (s • ν)) =
        (s : ℂ) • field ij z (covectorFromChart (Ci ij.1 ij.2) z ν) := by
    obtain ⟨w, hw, hwz⟩ := hz
    have hzC : z ∈ (Ci ij.1 ij.2).source := hwz ▸ (Ci ij.1 ij.2).map_target (hKc ij hw)
    have hcoord (η : H) :
        covectorInChart (Ci ij.1 ij.2) z (covectorFromChart (Ci ij.1 ij.2) z η) = η := by
      have hdiff : (Ci ij.1 ij.2).MDifferentiable (𝓡 (n + r)) (𝓡 (n + r)) :=
        ⟨(contMDiffOn_of_mem_maximalAtlas (hCi ij)).mdifferentiableOn (by simp),
          (contMDiffOn_symm_of_mem_maximalAtlas (hCi ij)).mdifferentiableOn (by simp)⟩
      have hderiv := hdiff.comp_symm_deriv ((Ci ij.1 ij.2).map_source hzC)
      rw [(Ci ij.1 ij.2).left_inv hzC] at hderiv
      ext k
      change inner ℝ η ((mfderiv _ _ (Ci ij.1 ij.2) z)
        ((mfderiv _ _ (Ci ij.1 ij.2).symm (Ci ij.1 ij.2 z))
          (EuclideanSpace.single k 1))) = η k
      have h := congrArg (fun T : H →L[ℝ] H ↦ T (EuclideanSpace.single k 1)) hderiv
      change (mfderiv _ _ (Ci ij.1 ij.2) z)
        ((mfderiv _ _ (Ci ij.1 ij.2).symm (Ci ij.1 ij.2 z))
          (EuclideanSpace.single k 1)) = EuclideanSpace.single k 1 at h
      rw [h]
      simp [EuclideanSpace.inner_single_right]
    have hlarge := le_of_mul_le_mul_left (hν.trans (hnorm ν)) hD
    have hlarge' := le_of_mul_le_mul_left (hsν.trans (hnorm (s • ν))) hD
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd] at hlarge'
    have hp := hpiece ij.1 (base z) (split ν).1 (split ν).2 s hs hlarge hlarge'
    dsimp only [field]
    rw [hcoord (s • ν), hcoord ν]
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd]
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    rw [← smul_smul, ← smul_smul]
    rw [hp]
    exact smul_comm (J.cutoff ij.2 (t ij.1 z).2 : ℂ) (s : ℂ) _
  obtain ⟨R, hR, hscale⟩ := exists_sum_homogeneous_of_compact_chart_tails g
    (fun ij : Fin C.size × Fin J.size ↦ Ci ij.1 ij.2) hCi K hK hKc field hzero
    (fun ij ↦ D * R₀ ij.1) htail
  refine ⟨R, hR, ?_⟩
  intro z ν s hs hν hsν
  have h := hscale z ν s hs hν hsν
  simpa only [Fintype.sum_prod_type, field, factor, t] using h

end PrincipalPseudodifferentialLocalization

end AtiyahSinger

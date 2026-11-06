/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedHorizontalFiniteMetricTransverseBound
public import AtiyahSinger.Analysis.PrincipalPseudodifferentialLocalization
public import AtiyahSinger.Geometry.AtlasBundlePresentation

/-!
# Transverse bound for the original principal-localized horizontal finite sum

Public module ID: M0868.

The actual common base cutoff supports and sphere partition supports give
compact sets inside each original associated product chart. Off each such
set, either its original sphere weight vanishes or its original native full
symbol vanishes at every frequency. Consequently the finite metric bound
applies to the literal double sum with no added support hypothesis.
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
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))
local notation "Z" => AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- Construct the original dependent product supports before applying the full finite estimate.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in
/-- The original principal-localized horizontal double sum has a metric transverse bound. -/
theorem exists_horizontalFullSymbol_metric_transverse_bound
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (J : AtlasBundlePresentation A)
    (g : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') E')
    (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (hc₀ : c₀ ∈ atlas X B)
    (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
    (K : Set H) (hK : IsCompact K)
    (hKChart : K ⊆ (associatedSphereProductChart S b₀ c₀ d₀).target) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let CP := associatedSphereProductChart S b₀ c₀ d₀
    let Ci (i : Fin C.size) (j : Fin J.size) :=
      associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ∀ (ξ : X) (η : Y),
      let coefficient : ℝ := M * ‖η‖ ^ 2
      let z₀ := CP.symm z
      let frequency (i : Fin C.size) (j : Fin J.size) (η : Y) :=
        (split (covectorInChart (Ci i j) z₀
          (covectorFromChart CP z₀ (split.symm (ξ, η))))).1
      let Δ := ∑ i, ∑ j, (J.cutoff j (associatedSphereTrivialization S (C.center i) z₀).2 : ℂ) •
        ((C.piece i).globalSymbolFunction (base z₀)
            (covectorFromChart (C.piece i).chart (base z₀) (frequency i j η)) -
          (C.piece i).globalSymbolFunction (base z₀)
            (covectorFromChart (C.piece i).chart (base z₀) (frequency i j 0)))
      ∀ u : E (base z₀), (k.pairing (base z₀) (Δ u) (Δ u)).re ≤
        coefficient * (h.pairing (base z₀) u u).re :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro split
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace split.symm Z
  intro CP Ci base
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
  have hsFrame (ij : Fin C.size × Fin J.size) (z : Z) (hz : z ∈ support ij) :
      base z ∈ (C.piece ij.1).input.frame.baseSet ∩ (C.piece ij.1).output.frame.baseSet := by
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hz
    have ht := htTarget ij hxy
    have htvalue : (t ij.1) ((t ij.1).toOpenPartialHomeomorph.symm (x, y)) = (x, y) :=
      (t ij.1).toOpenPartialHomeomorph.right_inv ht
    have hx : base ((t ij.1).toOpenPartialHomeomorph.symm (x, y)) = x := by
      rw [← (t ij.1).coe_fst ((t ij.1).toOpenPartialHomeomorph.map_target ht), htvalue]
    rw [hx]
    exact ⟨(hbChart ij.1 x hxy.1).2.1, (hbChart ij.1 x hxy.1).2.2.1⟩
  let weight (ij : Fin C.size × Fin J.size) (z : Z) := J.cutoff ij.2 (t ij.1 z).2
  have hweight (ij : Fin C.size × Fin J.size) (z : Z) : |weight ij z| ≤ 1 := by
    rw [abs_of_nonneg (J.cutoff_nonneg ij.2 (t ij.1 z).2)]
    exact (Finset.single_le_sum (fun j _ ↦ J.cutoff_nonneg j (t ij.1 z).2)
      (Finset.mem_univ ij.2)).trans_eq (J.sum_cutoff _)
  have hsZero (ij : Fin C.size × Fin J.size) (z : Z) (hz : z ∉ support ij) :
      weight ij z = 0 ∨ ∀ ν, (C.piece ij.1).globalSymbol.val (base z) ν = 0 := by
    by_cases hw : weight ij z = 0
    · exact Or.inl hw
    right
    have hx : base z ∉ baseSupport ij.1 := by
      intro hx
      have htz : z ∈ (t ij.1).source :=
        (t ij.1).mem_source.mpr (htBase ij.1 ▸ (hbChart ij.1 (base z) hx).2.2.2)
      apply hz
      refine ⟨t ij.1 z, ⟨?_, subset_tsupport _ hw⟩, (t ij.1).toOpenPartialHomeomorph.left_inv htz⟩
      rwa [(t ij.1).coe_fst htz]
    exact fun ν ↦ (C.piece ij.1).globalSymbolFunction_eq_zero (base z) hx ν
  have hfinite := exists_associatedSphereProductChart_finite_horizontal_metric_transverse_bound S
    (fun ij : Fin C.size × Fin J.size ↦ (C.piece ij.1).globalSymbol) g h k
    (fun ij ↦ C.center ij.1) (fun ij ↦ (C.piece ij.1).chart)
    (fun ij ↦ (C.piece ij.1).chart_mem_atlas) (fun ij ↦ J.chart ij.2)
    (fun ij ↦ J.chart_mem_atlas ij.2) b₀ c₀ hc₀ d₀ hd₀
    (fun ij ↦ (C.piece ij.1).input.frame) (fun ij ↦ (C.piece ij.1).output.frame)
    (fun ij ↦ (C.piece ij.1).input.frame_mem_atlas)
    (fun ij ↦ (C.piece ij.1).output.frame_mem_atlas)
    support hsCompact hsChart K hK hKChart weight hweight hsFrame hsZero
  obtain ⟨M, hM, hb⟩ := hfinite
  refine ⟨M, hM, ?_⟩
  intro z hz ξ η coefficient z₀ frequency Δ u
  have hv := hb z hz ξ η u
  simpa only [weight, t, CP, Ci, base, split, z₀, frequency, Δ, coefficient,
    PseudodifferentialPiece.globalSymbol, Fintype.sum_prod_type] using hv

end PrincipalPseudodifferentialLocalization

end AtiyahSinger

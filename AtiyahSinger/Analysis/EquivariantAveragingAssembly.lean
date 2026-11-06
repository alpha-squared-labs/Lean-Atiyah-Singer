/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAveragingCover
public import AtiyahSinger.Analysis.EquivariantSmoothKernelIntegral
public import AtiyahSinger.Analysis.PseudodifferentialDistributions
public import AtiyahSinger.Analysis.EquivariantSectionTopologyWeak
public import AtiyahSinger.Analysis.SmoothSectionIntegral

/-!
# Assemble local weighted conjugate integrals

Public module ID: M0472.

Local chart-fitting pieces and one fixed smoothing remainder assemble under
continuous parameter weights. A finite group partition of unity then constructs
the original unweighted Haar average. Every refinement uses the same original
positive base density and the actual residual smooth kernel. This isolates the
local analytic realization from its compactness and finite-sum argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  {m : ℝ}

set_option maxHeartbeats 1500000 in
-- Two finite refinements and pointwise fiber integrals use the same linear maps throughout.
/-- Local weighted averages of chart-fitting pieces suffice for the original global Haar average. -/
theorem exists_pseudodifferential_average_of_local
    (hlocal : ∀ (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) (g₀ : G)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (_hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F)),
      [MemTrivializationAtlas e] → [MemTrivializationAtlas f] →
      (fun x : M ↦ g₀ • x) ''
        (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
          c.source ∩ e.baseSet ∩ f.baseSet →
      ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧
        ∀ w : G → ℂ, Continuous w → tsupport w ⊆ U →
        ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
          ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
            (Q.toLinearMap u).val x =
              ∫ g, w g • ((σF.smoothSectionRepresentation IG hσF g)
                (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
                ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)))
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q.toLinearMap u).val x =
          ∫ g, ((σF.smoothSectionRepresentation IG hσF g)
            (P.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
            ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  classical
  let Op := smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F
  let PDO := PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let C (g : G) : Op →ₗ[ℂ] Op :=
    { toFun := fun T ↦ (σF.smoothSectionRepresentation IG hσF g).comp
        (T.comp (σE.smoothSectionRepresentation IG hσE g⁻¹))
      map_add' := fun T S ↦ by simp only [Op, LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun a T ↦ by
        simp only [Op, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply] }
  let Weighted (T : Op) (w : G → ℂ) : Prop :=
    ∃ Q : PDO, ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
      (Q.toLinearMap u).val x = ∫ g, w g • (C g T u).val x ∂ν
  let Local (T : Op) (g₀ : G) : Prop :=
    ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧
      ∀ w : G → ℂ, Continuous w → tsupport w ⊆ U → Weighted T w
  -- Actual smooth-section continuity gives every integrability assertion used in finite sums.
  obtain ⟨AE⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨BF⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  have hint (T : PDO) (w : G → ℂ) (hw : Continuous w)
      (u : smoothSections (n := n) (r := r) E) (x : M) :
      Integrable (fun g ↦ w g • (C g T.toLinearMap u).val x) ν := by
    have hinput : Continuous (fun g : G ↦
        AE.smoothSectionEquiv.symm (σE.smoothSectionRepresentation IG hσE g⁻¹ u)) :=
      (AE.continuous_smoothSectionAction_of_isManifold IG σE hσE).comp
        (continuous_inv.prodMk (continuous_const (y := AE.smoothSectionEquiv.symm u)))
    have hop := (T.continuous_smoothSectionMap AE BF).comp hinput
    have hout := (BF.continuous_smoothSectionAction_of_isManifold IG σF hσF).comp
      (continuous_id.prodMk hop)
    have heval := (BF.continuous_section_evaluation x).comp hout
    exact (hw.smul heval).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Finite local realizations and their one original residual kernel share a group neighborhood.
  have hfinite (T : Op) (g₀ : G) (N : ℕ) (R : Fin N → PDO)
      (hrem : IsSmoothingOperator μ (T - ∑ j, (R j).toLinearMap))
      (hR : ∀ j, Local (R j).toLinearMap g₀) : Local T g₀ := by
    choose U hU hgU hQ using hR
    let U₀ := ⋂ j, U j
    have hU₀ : IsOpen U₀ := isOpen_iInter_of_finite hU
    have hg₀ : g₀ ∈ U₀ := mem_iInter.mpr hgU
    refine ⟨U₀, hU₀, hg₀, ?_⟩
    intro w hw hwsupp
    have hj (j : Fin N) : Weighted (R j).toLinearMap w :=
      hQ j w hw (fun g hg ↦ mem_iInter.mp (hwsupp hg) j)
    choose Q hQeq using hj
    obtain ⟨K, hK⟩ := hrem
    obtain ⟨S, hS⟩ := K.exists_weighted_conjugate_integral (μ := μ) IG σE σF hσE hσF w hw
    let KP : PDO := ⟨K.toLinearMap μ,
      IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨K, rfl⟩⟩
    let Qmap : Op := S.toLinearMap μ + ∑ j, (Q j).toLinearMap
    have hQmap : IsPseudodifferentialOperator E F μ m Qmap :=
      (pseudodifferentialSpace E F μ m).add_mem
        (IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨S, rfl⟩)
        ((pseudodifferentialSpace E F μ m).sum_mem (fun j _ ↦ (Q j).isPseudodifferentialOperator))
    refine ⟨⟨Qmap, hQmap⟩, ?_⟩
    intro u x
    have hdecomp : T = K.toLinearMap μ + ∑ j, (R j).toLinearMap := by
      rw [hK]
      abel
    have hsumInt : Integrable (fun g ↦ ∑ j, w g • (C g (R j).toLinearMap u).val x) ν :=
      integrable_finsetSum _ (fun j _ ↦ hint (R j) w hw u x)
    change (Qmap u).val x = _
    simp only [Qmap, Op, LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add,
      Submodule.coe_sum, Pi.add_apply, Finset.sum_apply]
    rw [hS, show (∑ j, ((Q j).toLinearMap u).val x) =
        ∑ j, ∫ g, w g • (C g (R j).toLinearMap u).val x ∂ν from
      Finset.sum_congr rfl (fun j _ ↦ hQeq j u x)]
    rw [← integral_finsetSum _ (fun j _ ↦ hint (R j) w hw u x)]
    change (∫ g, w g • (C g KP.toLinearMap u).val x ∂ν) +
      (∫ g, ∑ j, w g • (C g (R j).toLinearMap u).val x ∂ν) = _
    rw [← integral_add (hint KP w hw u x) hsumInt]
    apply integral_congr_ae
    filter_upwards with g
    simp only [hdecomp, Op, map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply,
      Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, Finset.sum_apply,
      smul_add, Finset.smul_sum, KP]
  -- Refine a piece into actual charts at g₀, retaining its exact smoothing defect.
  have hpiece (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (g₀ : G) : Local L.toLinearMap g₀ := by
    let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) (g₀ • x)
    let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E (g₀ • x)
    let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F (g₀ • x)
    let U (x : M) := (fun y : M ↦ g₀ • y) ⁻¹'
      ((c x).source ∩ (e x).baseSet ∩ (f x).baseSet)
    have hU (x : M) : IsOpen (U x) :=
      (((c x).open_source.inter (e x).open_baseSet).inter (f x).open_baseSet).preimage
        (continuous_const_smul g₀)
    have hxU (x : M) : x ∈ U x :=
      ⟨⟨mem_chart_source _ _, mem_baseSet_trivializationAt _ _ _⟩,
        mem_baseSet_trivializationAt _ _ _⟩
    obtain ⟨N, a, R, hrem, _, hsupport⟩ := L.exists_refinement (μ := μ) U hU
      (fun x _ ↦ mem_iUnion.mpr ⟨x, hxU x⟩)
    let RP (j : Fin N) : PDO := ⟨(R j).toLinearMap, (R j).isPseudodifferentialOperator m⟩
    apply hfinite L.toLinearMap g₀ N RP hrem
    intro j
    apply hlocal (R j) g₀ (c (a j)) (chart_mem_atlas _ _) (e (a j)) (f (a j))
    rintro x ⟨y, hy, rfl⟩
    exact hsupport j hy
  have hP (g₀ : G) : Local P.toLinearMap g₀ := by
    obtain ⟨N, L, hrem⟩ := P.isPseudodifferentialOperator
    let LP (j : Fin N) : PDO := ⟨(L j).toLinearMap, (L j).isPseudodifferentialOperator m⟩
    exact hfinite P.toLinearMap g₀ N LP hrem (fun j ↦ hpiece (L j) g₀)
  -- A finite continuous partition of unity on G patches these same weighted realizations.
  choose U hU hgU hQ using hP
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun g _ ↦ mem_iUnion.mpr ⟨g, hgU g⟩)
  let enum : Fin s.card ≃ s := s.equivFin.symm
  let O (j : Fin s.card) := U (enum j)
  have hOcover : univ ⊆ ⋃ j, O j := by
    intro g hg
    obtain ⟨a, ha, hga⟩ := mem_iUnion₂.mp (hs hg)
    exact mem_iUnion.mpr ⟨enum.symm ⟨a, ha⟩, by simpa [O] using hga⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ O
    (fun j ↦ hU (enum j)) hOcover
  let w (j : Fin s.card) (g : G) : ℂ := ρ j g
  have hw (j : Fin s.card) : Continuous (w j) := Complex.continuous_ofReal.comp (ρ j).continuous
  have hwsupp (j : Fin s.card) : tsupport (w j) ⊆ O j := by
    apply (closure_mono ?_).trans (hρ j)
    intro g hg
    change (ρ j g : ℂ) ≠ 0 at hg
    change ρ j g ≠ 0
    intro hz
    exact hg (by rw [hz, Complex.ofReal_zero])
  have hj (j : Fin s.card) : Weighted P.toLinearMap (w j) :=
    hQ (enum j) (w j) (hw j) (hwsupp j)
  choose Q hQeq using hj
  let Qmap : Op := ∑ j, (Q j).toLinearMap
  have hQmap : IsPseudodifferentialOperator E F μ m Qmap :=
    (pseudodifferentialSpace E F μ m).sum_mem (fun j _ ↦ (Q j).isPseudodifferentialOperator)
  refine ⟨⟨Qmap, hQmap⟩, ?_⟩
  intro u x
  change (Qmap u).val x = ∫ g, (C g P.toLinearMap u).val x ∂ν
  simp only [Qmap, Op, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  rw [show (∑ j, ((Q j).toLinearMap u).val x) =
      ∑ j, ∫ g, w j g • (C g P.toLinearMap u).val x ∂ν from
    Finset.sum_congr rfl (fun j _ ↦ hQeq j u x)]
  rw [← integral_finsetSum _ (fun j _ ↦ hint P (w j) (hw j) u x)]
  apply integral_congr_ae
  filter_upwards with g
  rw [← Finset.sum_smul]
  have hsum : ∑ j, w j g = 1 := by
    have h := ρ.sum_eq_one (mem_univ g)
    simpa only [finsum_eq_sum_of_fintype, w, ← Complex.ofReal_sum, Complex.ofReal_one] using
      congrArg Complex.ofReal h
  rw [hsum, one_smul]

end AtiyahSinger

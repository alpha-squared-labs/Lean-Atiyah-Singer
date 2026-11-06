/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantCoordinateCutoffs
public import AtiyahSinger.Analysis.EquivariantLocalizedAmplitude
public import Mathlib.Topology.PartitionOfUnity

/-!
# Fixed local witnesses for compact group averaging

Public module ID: M0473.

A compact coordinate piece whose image at one group element fits an original
chart has fixed source and target plateaus and a fixed near-diagonal cutoff
throughout a group neighborhood. The expanded source plateau controls the
smooth remainder as well as the original piece. Tube neighborhoods retain
the original moving charts and frames with no smoothness of group inversion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set Topology
open scoped ContDiff Manifold

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
  [IsManifold IG ∞ G]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1500000 in
-- Nested compact cutoffs and four tube neighborhoods retain one shared family of witnesses.
/-- One fixed set of local cutoffs controls the original piece and its smoothing remainder
throughout a neighborhood of the specified group element. -/
theorem PseudodifferentialPiece.exists_equivariant_averaging_cutoffs {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (g₀ : G) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (hbase : (fun x : M ↦ g₀ • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
        c.source ∩ e.baseSet ∩ f.baseSet) :
    let X := EuclideanSpace ℝ (Fin n)
    let d (g : G) := Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g
    let t (g : G) := L.chart.symm.trans
      ((d g).toHomeomorph.toOpenPartialHomeomorph.trans c)
    ∃ (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
      (β δ : X → ℝ) (γ₀ : X × X → ℝ) (U : Set G) (W : Set (G × (X × X))),
      A.cutoff = B.cutoff ∧
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport L.output.cutoff ∪ tsupport L.input.cutoff ⊆ interior {x | β x = 1} ∧
      ContDiff ℝ ∞ δ ∧ HasCompactSupport δ ∧
      tsupport δ ⊆ symbolChartDomain E F L.chart L.input.frame L.output.frame ∧
      tsupport β ⊆ interior {x | δ x = 1} ∧
      ContDiff ℝ ∞ γ₀ ∧ HasCompactSupport γ₀ ∧
      tsupport γ₀ ⊆ tsupport β ×ˢ tsupport β ∧
      (∀ x : X, (fun z ↦ β z.1 * β z.2 - γ₀ z) =ᶠ[𝓝 (x, x)] (fun _ ↦ 0)) ∧
      IsOpen U ∧ g₀ ∈ U ∧ IsOpen W ∧
      (∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (t p.1).target ∧
        (averagedFDeriv (t p.1).symm p.2.1 p.2.2).IsInvertible) ∧
      ∀ g ∈ U,
        tsupport δ ⊆ (t g).source ∧
        tsupport A.cutoff ⊆ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
          (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet) ∧
        t g '' tsupport β ⊆ interior {z | A.cutoff z = 1} ∧
        ∀ z ∈ tsupport γ₀, z.1 ∈ (t g).source ∧ z.2 ∈ (t g).source ∧
          (g, (t g z.1, t g z.2)) ∈ W := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let t (g : G) := L.chart.symm.trans
    ((Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g).toHomeomorph.toOpenPartialHomeomorph.trans c)
  let K := tsupport L.output.cutoff ∪ tsupport L.input.cutoff
  let D := L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
  let D₀ := symbolChartDomain E F L.chart L.input.frame L.output.frame
  let T := c.source ∩ e.baseSet ∩ f.baseSet
  have hD : IsOpen D :=
    (L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet
  have hD₀ : IsOpen D₀ :=
    isOpen_symbolChartDomain E F L.chart L.input.frame L.output.frame
  have hT : IsOpen T := (c.open_source.inter e.open_baseSet).inter f.open_baseSet
  have hK : IsCompact K := L.output.compact_support.union L.input.compact_support
  have hKD₀ : K ⊆ D₀ := by
    rintro z (hz | hz)
    · exact ⟨⟨(L.output.support_subset hz).1, L.output_support_in_input_frame hz⟩,
        (L.output.support_subset hz).2⟩
    · exact ⟨L.input.support_subset hz, L.input_support_in_output_frame hz⟩
  let S := D₀ ∩ (fun z : X ↦ g₀ • L.chart.symm z) ⁻¹' T
  have hS : IsOpen S :=
    ((continuous_const_smul g₀).comp_continuousOn
      (L.chart.continuousOn_symm.mono (fun _ hz ↦ hz.1.1))).isOpen_inter_preimage hD₀ hT
  have hKS : K ⊆ S := fun z hz ↦
    ⟨hKD₀ hz, hbase ⟨L.chart.symm z, ⟨z, hz, rfl⟩, rfl⟩⟩
  -- Nested compact plateaus keep both the near part and the fixed residual kernel in one chart.
  have hcut (J : Set X) (hJ : IsCompact J) (O : Set X) (hO : IsOpen O)
      (hJO : J ⊆ O) :
      ∃ χ : X → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
        J ⊆ interior {x | χ x = 1} := by
    obtain ⟨V, hV, hJV, hVO, hVc⟩ := exists_open_between_and_isCompact_closure hJ hO hJO
    obtain ⟨V', hV', hVV', hV'O, hV'c⟩ :=
      exists_open_between_and_isCompact_closure hVc hO hVO
    obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hV' hVc.isClosed hVV'
    have htχ : tsupport χ = closure V' := congrArg closure hsχ
    refine ⟨χ, hχ, by simpa only [HasCompactSupport, htχ] using hV'c,
      by simpa only [htχ] using hV'O, ?_⟩
    apply hJV.trans
    exact interior_maximal (fun z hz ↦ (honeχ z).mp (subset_closure hz)) hV
  obtain ⟨β, hβ, hcβ, hβS, hKβ⟩ := hcut K hK S hS hKS
  obtain ⟨δ, hδ, hcδ, hδS, hβδ⟩ := hcut (tsupport β) hcβ S hS hβS
  -- The target cutoff is fixed at g₀ and is one near the entire expanded source support.
  let Vc := symbolChartDomain E F c e f ∩ (fun z : X ↦ g₀⁻¹ • c.symm z) ⁻¹' D
  have hVc : IsOpen Vc :=
    ((continuous_const_smul g₀⁻¹).comp_continuousOn
      (c.continuousOn_symm.mono (fun _ hz ↦ hz.1.1))).isOpen_inter_preimage
        (isOpen_symbolChartDomain E F c e f) hD
  have hβt : tsupport β ⊆ (t g₀).source := fun z hz ↦
    ⟨(hβS hz).1.1.1, mem_univ _, (hβS hz).2.1.1⟩
  have htβ : IsCompact (t g₀ '' tsupport β) :=
    hcβ.image_of_continuousOn ((t g₀).continuousOn.mono hβt)
  have htβVc : t g₀ '' tsupport β ⊆ Vc := by
    rintro _ ⟨z, hz, rfl⟩
    have hs := hβS hz
    have hx := hs.2
    change c (g₀ • L.chart.symm z) ∈ Vc
    simp only [Vc, symbolChartDomain, mem_inter_iff, mem_preimage,
      c.left_inv hx.1.1, inv_smul_smul]
    exact ⟨⟨⟨c.map_source hx.1.1, hx.1.2⟩, hx.2⟩,
      ⟨⟨L.chart.map_target hs.1.1.1, hs.1.1.2⟩, hs.1.2⟩⟩
  obtain ⟨χ, hχ, hcχ, hχVc, htβχ⟩ := hcut _ htβ Vc hVc htβVc
  let A : BundleChartCutoff (r := r) E c :=
    { frame := e
      frame_mem_atlas := inferInstance
      cutoff := χ
      smooth_cutoff := hχ
      compact_support := hcχ
      support_subset := fun _ hz ↦ (hχVc hz).1.1 }
  let B : BundleChartCutoff (r := q) F c :=
    { frame := f
      frame_mem_atlas := inferInstance
      cutoff := χ
      smooth_cutoff := hχ
      compact_support := hcχ
      support_subset := fun _ hz ↦ ⟨(hχVc hz).1.1.1, (hχVc hz).1.2⟩ }
  -- Tube neighborhoods preserve each compact support condition, including inverse-frame overlap.
  have htube (J : Set X) (hJ : IsCompact J) (N : Set (G × X)) (hN : IsOpen N)
      (hN₀ : ∀ z ∈ J, (g₀, z) ∈ N) :
      ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧ ∀ g ∈ U, ∀ z ∈ J, (g, z) ∈ N := by
    have hJN : ({g₀} : Set G) ×ˢ J ⊆ N := by
      rintro ⟨g, z⟩ ⟨hg, hz⟩
      rcases mem_singleton_iff.mp hg with rfl
      exact hN₀ z hz
    obtain ⟨U, O, hU, _, hgU, hJO, hUO⟩ :=
      generalized_tube_lemma isCompact_singleton hJ hN hJN
    exact ⟨U, hU, hgU (mem_singleton g₀), fun g hg z hz ↦ hUO ⟨hg, hJO hz⟩⟩
  let N₀ : Set (G × X) := univ ×ˢ L.chart.target
  let moved (p : G × X) : M := p.1 • L.chart.symm p.2
  have hmoved : ContinuousOn moved N₀ := continuous_fst.continuousOn.smul
    (L.chart.continuousOn_symm.comp continuous_snd.continuousOn (fun _ hz ↦ hz.2))
  let Nδ := N₀ ∩ moved ⁻¹' T
  have hNδ : IsOpen Nδ := hmoved.isOpen_inter_preimage (isOpen_univ.prod L.chart.open_target) hT
  obtain ⟨Uδ, hUδ, hgδ, hδU⟩ := htube _ hcδ Nδ hNδ
    (fun z hz ↦ ⟨⟨mem_univ _, (hδS hz).1.1.1⟩, (hδS hz).2⟩)
  have htcontinuous : ContinuousOn (fun p : G × X ↦ c (moved p)) Nδ :=
    c.continuousOn.comp (hmoved.mono inter_subset_left) (fun _ hp ↦ hp.2.1.1)
  let Nβ := Nδ ∩ (fun p : G × X ↦ c (moved p)) ⁻¹' interior {z | χ z = 1}
  have hNβ : IsOpen Nβ := htcontinuous.isOpen_inter_preimage hNδ isOpen_interior
  obtain ⟨Uβ, hUβ, hgβ, hβU⟩ := htube _ hcβ Nβ hNβ
    (fun z hz ↦ ⟨⟨⟨mem_univ _, (hβS hz).1.1.1⟩, (hβS hz).2⟩, htβχ ⟨z, hz, rfl⟩⟩)
  let movedInv (p : G × X) : M := p.1⁻¹ • c.symm p.2
  have hmovedInv : ContinuousOn movedInv (univ ×ˢ c.target) :=
    continuous_fst.inv.continuousOn.smul
      (c.continuousOn_symm.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2))
  let NA := (univ ×ˢ c.target) ∩ movedInv ⁻¹' D
  have hNA : IsOpen NA :=
    hmovedInv.isOpen_inter_preimage (isOpen_univ.prod c.open_target) hD
  obtain ⟨UA, hUA, hgA, hAU⟩ := htube _ hcχ NA hNA
    (fun z hz ↦ ⟨⟨mem_univ _, (hχVc hz).1.1.1⟩, (hχVc hz).2⟩)
  -- The same original diagonal cutoff controls all transformed frequency changes.
  obtain ⟨Uf, W, hUf, hgf, hW, hvalid, ξ, hξ, hcξ, hξone, hξvalid⟩ :=
    exists_inverse_smul_chart_cutoff IG c L.chart hc L.chart_mem_atlas g₀
      (tsupport β) hcβ hβt
  let γ₀ (z : X × X) : ℝ := (β z.1 * β z.2) * ξ z
  have hγ₀ : ContDiff ℝ ∞ γ₀ :=
    ((hβ.comp contDiff_fst).mul (hβ.comp contDiff_snd)).mul hξ
  have hγξ : tsupport γ₀ ⊆ tsupport ξ := tsupport_mul_subset_right
  have hcγ₀ : HasCompactSupport γ₀ := hcξ.of_isClosed_subset (isClosed_tsupport _) hγξ
  have hγβ : tsupport γ₀ ⊆ tsupport β ×ˢ tsupport β := by
    apply closure_minimal ?_ ((isClosed_tsupport β).prod (isClosed_tsupport β))
    intro z hz
    have hβz : β z.1 * β z.2 ≠ 0 := left_ne_zero_of_mul (show γ₀ z ≠ 0 from hz)
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hβz),
      subset_tsupport _ (right_ne_zero_of_mul hβz)⟩
  have hoff (x : X) :
      (fun z ↦ β z.1 * β z.2 - γ₀ z) =ᶠ[𝓝 (x, x)] (fun _ ↦ 0) := by
    by_cases hx : x ∈ tsupport β
    · filter_upwards [isOpen_interior.mem_nhds (hξone ⟨x, hx, rfl⟩)] with z hz
      have hz' : ξ z = 1 := interior_subset (s := {z | ξ z = 1}) hz
      simp only [γ₀, hz', mul_one, sub_self]
    · have hzero := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
        (continuous_fst.tendsto (x, x))
      filter_upwards [hzero] with z hz
      simp only [γ₀, show β z.1 = 0 from hz, zero_mul, sub_self]
  let U := ((Uδ ∩ Uβ) ∩ UA) ∩ Uf
  refine ⟨A, B, β, δ, γ₀, U, W, rfl, hβ, hcβ, hKβ, hδ, hcδ,
    fun z hz ↦ (hδS hz).1, hβδ, hγ₀, hcγ₀, hγβ, hoff,
    ((hUδ.inter hUβ).inter hUA).inter hUf, ⟨⟨⟨hgδ, hgβ⟩, hgA⟩, hgf⟩,
    hW, hvalid, ?_⟩
  intro g hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := hδU g hg.1.1.1 z hz
    exact ⟨h.1.2, mem_univ _, h.2.1.1⟩
  · intro z hz
    exact (hAU g hg.1.2 z hz).2
  · rintro _ ⟨z, hz, rfl⟩
    exact (hβU g hg.1.1.2 z hz).2
  · intro z hz
    exact hξvalid g hg.2 z (hγξ hz)

end AtiyahSinger

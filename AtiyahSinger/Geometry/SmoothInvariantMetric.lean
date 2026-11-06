/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetric
public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import AtiyahSinger.Topology.EquivariantHermitianMetric
public import AtiyahSinger.Topology.ModelBundleTopology

import AtiyahSinger.Geometry.CompactParameterIntegral

/-!
# Smooth invariant Hermitian metrics on the original equivariant bundle

Public module ID: M1404.

A specified smooth metric gives the same continuous metric on the original
bundle, after the existing phantom-model retyping. The compact-group Haar
average already defined for continuous metrics has smooth Gram entries when
the original moving-fiber action is jointly smooth. Its original averaged
forms, rather than a new family of pairings, therefore define a smooth metric.
No fiber norm, inner-product instance, bundle atlas or topology is replaced.

Sources: SG III.9, pp.211--214, for invariant Hermitian structures in the
smooth equivariant setting, and HU III.9.5 for ordinary metric existence.
Joint smoothness of the average follows from compact-parameter differentiation
applied to the original local Gram expressions. Joint total continuity, smoothness
of the original average, and invariant smooth metric existence are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] sumTopology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

namespace SmoothHermitianMetric

variable (h : SmoothHermitianMetric (n := n) (r := r) E)

set_option maxHeartbeats 1200000 in
-- Glue finite Gram expansions in the original double-bundle topology.
/-- The smooth metric is jointly continuous on the original same-base double bundle. -/
theorem continuous_totalPairing :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      h.pairing z.proj z.snd.1 z.snd.2) := by
  /- Stage 1: in any original bundle frame, expand the pairing as its finite
  Gram sum. Its Gram entries are continuous because they are real-smooth,
  and the two original vector coordinates vary continuously in that frame.
  Stage 2: the induced same-base double topology makes both projections to
  the original total space continuous. Frame neighborhoods cover that double
  bundle, so the local finite sums give joint continuity everywhere.
  Stage 3: modelTopology only retypes the phantom model through the existing
  unitTotalHomeomorph. The base, fiber vectors and original modeled topology
  are unchanged. This is stronger than continuity on each individual fiber;
  no additional norm or inner-product instance is installed. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  -- Retyping and the two same-base projections preserve the original vectors and topology.
  have hfst : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) :=
    (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).comp continuous_sum_fst
  have hsnd : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) :=
    (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).comp continuous_sum_snd
  have hbase : Continuous (π Unit (E ×ᵇ E)) :=
    (FiberBundle.continuous_proj (EuclideanSpace ℂ (Fin r)) E).comp hfst
  rw [continuous_iff_continuousAt]
  intro z
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z.proj
  have hz : z.proj ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  let s := π Unit (E ×ᵇ E) ⁻¹' e.baseSet
  have hs : s ∈ nhds z := (e.open_baseSet.preimage hbase).mem_nhds hz
  -- Both local vector coordinates and all Gram entries are continuous on this frame domain.
  have hu : ContinuousOn (fun w : TotalSpace Unit (E ×ᵇ E) ↦
      (e ⟨w.proj, w.snd.1⟩).2) s :=
    continuous_snd.comp_continuousOn
      (e.toOpenPartialHomeomorph.continuousOn.comp hfst.continuousOn
        (fun w hw ↦ e.mem_source.mpr hw))
  have hv : ContinuousOn (fun w : TotalSpace Unit (E ×ᵇ E) ↦
      (e ⟨w.proj, w.snd.2⟩).2) s :=
    continuous_snd.comp_continuousOn
      (e.toOpenPartialHomeomorph.continuousOn.comp hsnd.continuousOn
        (fun w hw ↦ e.mem_source.mpr hw))
  have hgram (i j : Fin r) : ContinuousOn
      (fun w : TotalSpace Unit (E ×ᵇ E) ↦ h.gramMatrix e w.proj i j) s :=
    (h.contMDiffOn_gram e i j).continuousOn.comp hbase.continuousOn (fun _ hw ↦ hw)
  have hsum : ContinuousOn
      (fun w : TotalSpace Unit (E ×ᵇ E) ↦ ∑ i, ∑ j,
        star ((e ⟨w.proj, w.snd.1⟩).2 i) * h.gramMatrix e w.proj i j *
          (e ⟨w.proj, w.snd.2⟩).2 j) s := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((Complex.continuous_conj.comp_continuousOn
      ((PiLp.continuous_apply 2 _ i).comp_continuousOn hu)).mul (hgram i j)).mul
        ((PiLp.continuous_apply 2 _ j).comp_continuousOn hv)
  -- The original Gram expansion identifies the local formula with the specified pairing.
  exact (hsum.congr (fun w hw ↦ h.pairing_eq_gramMatrix e w.proj hw _ _)).continuousAt hs

/-- The same smooth forms, viewed as continuous forms after the fixed model retyping. -/
def toContinuousHermitianMetric :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  exact
    { toCore := h.toCore
      continuous_pairing := h.continuous_totalPairing
      isFiniteRank := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E }

end SmoothHermitianMetric

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hA : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)

namespace SmoothHermitianMetric

variable (h : SmoothHermitianMetric (n := n) (r := r) E)

set_option maxHeartbeats 2000000 in
-- Control derivatives of the original Haar integrand uniformly over the compact group.
include hG hM hA hσ in
/-- The existing Haar-averaged continuous metric has smooth Gram entries in the original atlas. -/
theorem contMDiffOn_gram_average :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e],
      ∀ i j : Fin r,
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ (((h.toContinuousHermitianMetric).average σ).toCore x).inner
            (e.symmL ℂ x (EuclideanSpace.single i 1))
            (e.symmL ℂ x (EuclideanSpace.single j 1))) e.baseSet := by
  /- Stage 1: keep the actual normalized Haar integrand from the earlier
  continuous construction. Fix a source frame near x. In a target frame near
  g*x, the moved vectors have the jointly smooth columns given by hσ.
  Pairing those columns with the original smooth Gram matrix is jointly smooth
  in (g,x). Target frames cover the entire moving orbit; no single global
  moving frame is assumed.
  Stage 2: express the base variable in one original manifold chart and
  retain the compact group as the parameter manifold. Apply the existing
  contDiffOn_integral_of_compact_manifold theorem to this same jointly smooth
  pairing. Its compact-parameter derivative interchange gives smoothness at
  every order without choosing a global moving frame.
  Stage 3: recover smoothness on each original source-frame base set. The
  positive form and joint continuity certificates are already those of the
  continuous average; they are not proved again here. Joint smoothness is
  essential: continuity in g together with separate smoothness in x would not
  by itself justify the uniform bounds used in this argument. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro e he i j
  -- Local moving frames establish joint regularity of the actual Haar integrand.
  let Φ : G × M → ℂ := fun p ↦ h.pairing (p.1 • p.2)
    (σ.linearMap p.1 p.2 (e.symmL ℂ p.2 (EuclideanSpace.single i 1)))
    (σ.linearMap p.1 p.2 (e.symmL ℂ p.2 (EuclideanSpace.single j 1)))
  have hΦ : ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℂ) ∞
      Φ (Set.univ ×ˢ e.baseSet) := by
    intro p hp
    let f := trivializationAt (EuclideanSpace ℂ (Fin r)) E (p.1 • p.2)
    have hfp : p.1 • p.2 ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    let t := {q : G × M | q.2 ∈ e.baseSet ∧ q.1 • q.2 ∈ f.baseSet}
    have ht : IsOpen t :=
      (e.open_baseSet.preimage continuous_snd).inter (f.open_baseSet.preimage continuous_smul)
    have hpt : p ∈ t := ⟨hp.2, hfp⟩
    have hcoord (k a : Fin r) :
        ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℂ) ∞
          (fun q : G × M ↦
            (f ⟨q.1 • q.2, σ.linearMap q.1 q.2
              (e.symmL ℂ q.2 (EuclideanSpace.single k 1))⟩).2 a) t :=
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a).restrictScalars ℝ).contDiff.contMDiff
        |>.comp_contMDiffOn (hσ e f k)
    have hgram (a b : Fin r) :
        ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℂ) ∞
          (fun q : G × M ↦ h.gramMatrix f (q.1 • q.2) a b) t :=
      (h.contMDiffOn_gram f a b).comp contMDiff_smul.contMDiffOn (fun _ hq ↦ hq.2)
    have hsum :
        ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℂ) ∞
          (fun q : G × M ↦ ∑ a, ∑ b,
            star ((f ⟨q.1 • q.2, σ.linearMap q.1 q.2
              (e.symmL ℂ q.2 (EuclideanSpace.single i 1))⟩).2 a) *
            h.gramMatrix f (q.1 • q.2) a b *
            (f ⟨q.1 • q.2, σ.linearMap q.1 q.2
              (e.symmL ℂ q.2 (EuclideanSpace.single j 1))⟩).2 b) t := by
      apply contMDiffOn_finsetSum
      intro a _
      apply contMDiffOn_finsetSum
      intro b _
      have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcoord i a)
      have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) := contDiff_mul
      exact hmul.contMDiff.comp_contMDiffOn
        ((hmul.contMDiff.comp_contMDiffOn
          (hconj.prodMk_space (hgram a b))).prodMk_space (hcoord j b))
    have hlocal : ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℂ) ∞
        Φ t := hsum.congr (fun q hq ↦ h.pairing_eq_gramMatrix f (q.1 • q.2) hq.2 _ _)
    exact (hlocal.contMDiffAt (ht.mem_nhds hpt)).contMDiffWithinAt
  -- Only the base variable is charted; the compact group keeps its given manifold model.
  let μ := MeasureTheory.Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  change ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
    (fun x ↦ ∫ g : G, Φ (g, x) ∂μ) e.baseSet
  intro x hx
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let s := c.target ∩ c.symm ⁻¹' e.baseSet
  have hs : IsOpen s := c.isOpen_inter_preimage_symm e.open_baseSet
  have hcx : c x ∈ s := ⟨c.map_source (mem_chart_source _ x), by
    simpa only [Set.mem_preimage, c, OpenPartialHomeomorph.left_inv _ (mem_chart_source _ x)]
      using hx⟩
  have hchart : ContMDiffOn
      (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℂ) ∞
      (fun q : G × EuclideanSpace ℝ (Fin n) ↦ Φ (q.1, c.symm q.2)) (Set.univ ×ˢ s) := by
    apply hΦ.comp
      (contMDiffOn_fst.prodMk ((contMDiffOn_chart_symm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (x := x)).comp contMDiffOn_snd (fun _ hq ↦ hq.2.1)))
    intro q hq
    exact ⟨Set.mem_univ _, hq.2.2⟩
  -- Uniform compact-parameter differentiation controls all orders on this open chart domain.
  have hint : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) ↦ ∫ g : G, Φ (g, c.symm y) ∂μ) s := by
    exact contDiffOn_integral_of_compact_manifold IG μ hs hchart
  -- The inverse-chart identity returns the same integral to the original base atlas.
  have hlocal := (hint.contMDiffOn.contMDiffAt (hs.mem_nhds hcx)).comp x
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I :=
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x) (mem_chart_source _ x))
  apply ContMDiffAt.contMDiffWithinAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x)] with y hy
  change (∫ g : G, Φ (g, y) ∂μ) = ∫ g : G, Φ (g, c.symm (c y)) ∂μ
  rw [c.left_inv hy]

/-- The original Haar-averaged forms, now certified smooth in the same bundle atlas. -/
def average : SmoothHermitianMetric (n := n) (r := r) E := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  exact
    { toCore := ((h.toContinuousHermitianMetric).average σ).toCore
      contMDiffOn_gram := h.contMDiffOn_gram_average IG σ hσ
      isSmoothBundle := h.isSmoothBundle }

end SmoothHermitianMetric

variable [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hG hM hA hT2 hSC hE hσ in
/-- A smooth action of a compact Hausdorff group on a smooth finite-rank bundle over a
Hausdorff second-countable smooth base admits an invariant smooth Hermitian metric. -/
theorem exists_invariant_smoothHermitianMetric :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∃ h : SmoothHermitianMetric (n := n) (r := r) E,
      ∀ (g : G) (x : M) (u v : E x),
        h.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x v) =
          h.pairing x u v := by
  /- Stage 1: choose the existing smooth Hermitian metric supplied by
  nonempty_smoothHermitianMetric for the original bundle. Only this step needs
  Hausdorffness and second countability of the base and the smooth bundle
  transition functions; base compactness is unnecessary.
  Stage 2: take its specified smooth average under the original action σ.
  The smoothness certificate upgrades the old normalized Haar average, and
  ContinuousHermitianMetric.average_invariant supplies its existing right-Haar
  invariance on these identical averaged Core fields. All forms
  stay on the original fibers. Zero rank and an empty base require no extra
  hypotheses, and no new norm or inner-product instance is chosen. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  -- Ordinary smooth existence chooses the original forms before applying the fixed Haar average.
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) E
  refine ⟨h.average IG σ hσ, ?_⟩
  intro g x u v
  -- This is the same averaged Core field, so its proved right-Haar invariance applies directly.
  exact h.toContinuousHermitianMetric.average_invariant σ g x u v

end AtiyahSinger

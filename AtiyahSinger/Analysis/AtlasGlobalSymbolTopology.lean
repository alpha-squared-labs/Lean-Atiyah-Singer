/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasGlobalSymbol
public import AtiyahSinger.Analysis.SymbolTopology

/-!
# Weighted derivative topology on atlas symbols

Public module ID: M0245.

A03: pull back the local symbol seminorms through each manifold chart and
pair of atlas frames. Each seminorm tests a mixed derivative on a compact
spatial subset and all frequencies, with its order-dependent weight. The
source and target coordinate ranks are those of the selected frames.

These seminorms generate a topology on atlasGlobalSymbolSpace. Convergence
is equivalent to decay of every difference seminorm; continuity of a
parameter family has the corresponding neighborhood criterion. Reading a
fixed chart is continuous, and the seminorms separate symbols on a smooth
manifold. No compact base, metric or density is required.

Sources: SG III.3.2 and Definition 3.18, pp.178--179 and 187--188.
Locally varying rank uses the same chartwise seminorm construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- The actual common base-chart and two-frame coordinate domain is open. -/
theorem isOpen_atlasSymbolChartDomain
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (i : A.Index) (j : B.Index) : IsOpen (atlasSymbolChartDomain A B c i j) := by
  -- Intersect the inverse image of the two open frame domains with the chart target.
  simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
    c.continuousOn_symm.isOpen_inter_preimage c.open_target
      ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)

/-- The chart, two original frame indices and local weighted derivative being tested. -/
structure AtlasGlobalSymbolSeminormIndex where
  /-- The actual manifold chart. -/
  chart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- Membership in the specified smooth manifold atlas. -/
  mem_atlas : chart ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- The index of the original source frame, retaining its own rank. -/
  inputIndex : A.Index
  /-- The index of the original target frame, retaining its independent rank. -/
  outputIndex : B.Index
  /-- Compact spatial set and mixed derivative orders in the common coordinate region. -/
  localIndex : SymbolSeminormIndex
    (atlasSymbolChartDomain A B chart inputIndex outputIndex)

variable (m : ℝ)

/-- Actual coordinate reading is complex-linear on the existing atlas symbol module. -/
theorem isLinearMap_atlasGlobalSymbolInChart
    (J : AtlasGlobalSymbolSeminormIndex A B) :
    IsLinearMap ℂ (fun p : atlasGlobalSymbolSpace A B m ↦
      (⟨atlasGlobalSymbolInChart A B p.val J.chart J.inputIndex J.outputIndex,
        p.property J.chart J.mem_atlas J.inputIndex J.outputIndex⟩ :
        symbolSpace
          (atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex)
          (isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex)
          m (A.rank J.inputIndex) (B.rank J.outputIndex))) := by
  /- On the valid frame overlap, the original coordinate expression composes
  p with fixed complex-linear input and output frame maps. Composition preserves
  sums and complex scalar multiplication. Outside that overlap all expressions
  are zero by the same branch of atlasGlobalSymbolInChart. Pointwise extensionality
  and subtype extensionality give the two linearity laws without new symbols. -/
  classical
  constructor
  · intro p q
    apply Subtype.ext
    ext z η v
    by_cases h : J.chart.symm z ∈ (A.chart J.inputIndex).baseSet ∧
        J.chart.symm z ∈ (B.chart J.outputIndex).baseSet
    · simp [atlasGlobalSymbolInChart, h]
    · simp [atlasGlobalSymbolInChart, h]
  · intro a p
    apply Subtype.ext
    ext z η v
    by_cases h : J.chart.symm z ∈ (A.chart J.inputIndex).baseSet ∧
        J.chart.symm z ∈ (B.chart J.outputIndex).baseSet
    · simp [atlasGlobalSymbolInChart, h]
    · simp [atlasGlobalSymbolInChart, h]

/-- The original chart expression bundled as a linear map into its local symbol space. -/
def atlasGlobalSymbolInChartLinearMap (J : AtlasGlobalSymbolSeminormIndex A B) :
    atlasGlobalSymbolSpace A B m →ₗ[ℂ]
      symbolSpace
        (atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex)
        (isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex)
        m (A.rank J.inputIndex) (B.rank J.outputIndex) :=
  IsLinearMap.mk'
    (fun p ↦
      ⟨atlasGlobalSymbolInChart A B p.val J.chart J.inputIndex J.outputIndex,
        p.property J.chart J.mem_atlas J.inputIndex J.outputIndex⟩)
    (isLinearMap_atlasGlobalSymbolInChart A B m J)

/-- Pull back the actual local weighted derivative seminorm through the original coordinates. -/
def atlasGlobalSymbolSeminorm (J : AtlasGlobalSymbolSeminormIndex A B) :
    Seminorm ℂ (atlasGlobalSymbolSpace A B m) :=
  (symbolSeminorm
    (isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex)
    m J.localIndex).comp (atlasGlobalSymbolInChartLinearMap A B m J)

/-- The topology generated by every original chartwise weighted derivative seminorm. -/
@[instance_reducible]
def atlasGlobalSymbolTopology : TopologicalSpace (atlasGlobalSymbolSpace A B m) :=
  (SeminormFamily.moduleFilterBasis (atlasGlobalSymbolSeminorm A B m)).topology

-- Both symbol carriers below use these chosen seminorm topologies.
attribute [local instance] atlasGlobalSymbolTopology symbolTopology

/-- The selected topology is generated by the specified actual derivative seminorms. -/
theorem withSeminorms_atlasGlobalSymbolTopology :
    WithSeminorms (atlasGlobalSymbolSeminorm A B m) := by
  /- Unfold the explicit topology. Its module filter basis is generated by the
  displayed pullbacks of the standard local weighted derivative seminorms. This
  identifies the topology actually used in continuity and convergence statements. -/
  exact ⟨rfl⟩

/-- Filter convergence tests uniform weighted derivatives of symbol differences. -/
theorem tendsto_atlasGlobalSymbolTopology_iff {Z : Type*} (l : Filter Z)
    (p : Z → atlasGlobalSymbolSpace A B m) (b : atlasGlobalSymbolSpace A B m) :
    Tendsto p l (𝓝 b) ↔
      ∀ J : AtlasGlobalSymbolSeminormIndex A B, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ z in l, atlasGlobalSymbolSeminorm A B m J (p z - b) < ε := by
  /- Apply the seminorm neighborhood criterion to the preceding WithSeminorms
  certificate. Each test contains the supremum over its compact spatial set and
  all frequencies, after division by the prescribed order-dependent weight.
  Values of individual seminorms or pointwise convergence are insufficient. -/
  exact (withSeminorms_atlasGlobalSymbolTopology A B m).tendsto_nhds p b

/-- A parameter family is continuous exactly when every difference seminorm tends to zero. -/
theorem continuous_atlasGlobalSymbolTopology_iff {Z : Type*} [TopologicalSpace Z]
    (p : Z → atlasGlobalSymbolSpace A B m) :
    Continuous p ↔ ∀ (z : Z) (J : AtlasGlobalSymbolSeminormIndex A B),
      Tendsto (fun w ↦ atlasGlobalSymbolSeminorm A B m J (p w - p z)) (𝓝 z) (𝓝 0) := by
  /- At each parameter z use the filter criterion for convergence to p(z).
  Nonnegative seminorms tend to zero exactly when they are eventually below
  every positive epsilon. The resulting uniform weighted derivative condition
  has the same fixed chart and frame indices on both symbols. No compactness,
  differentiability or finite-dimensionality of the parameter space is used. -/
  -- The symbol topology is an additive group topology; each defining seminorm is continuous.
  have : IsTopologicalAddGroup _ :=
    (withSeminorms_atlasGlobalSymbolTopology A B m).isTopologicalAddGroup
  constructor
  · intro hp z J
    have h := ((withSeminorms_atlasGlobalSymbolTopology A B m).continuous_seminorm J).continuousAt
      |>.tendsto.comp ((hp.continuousAt (x := z)).sub_const (p z))
    rw [sub_self, map_zero] at h
    exact h
  · intro hp
    rw [continuous_iff_continuousAt]
    intro z
    apply (tendsto_atlasGlobalSymbolTopology_iff A B m (𝓝 z) p (p z)).mpr
    intro J ε hε
    exact (hp z J).eventually (Iio_mem_nhds hε)

/-- Reading a fixed original chart is continuous for the two derivative seminorm topologies. -/
theorem continuous_atlasGlobalSymbolInChartLinearMap
    (J : AtlasGlobalSymbolSeminormIndex A B) :
    Continuous (atlasGlobalSymbolInChartLinearMap A B m J) := by
  /- Every seminorm on the local codomain pulls back to the global seminorm
  indexed by these same charts and the new local compact set/derivative orders.
  Thus the seminorm continuity criterion applies directly. Coordinate ranks are
  fixed by this frame pair, not required to agree with ranks elsewhere. -/
  have : IsTopologicalAddGroup _ :=
    (withSeminorms_atlasGlobalSymbolTopology A B m).isTopologicalAddGroup
  apply WithSeminorms.continuous_of_continuous_comp
    (withSeminorms_symbolTopology
      (isOpen_atlasSymbolChartDomain A B J.chart J.inputIndex J.outputIndex) m)
  intro K
  exact (withSeminorms_atlasGlobalSymbolTopology A B m).continuous_seminorm
    { J with localIndex := K }

/-- The atlas seminorms separate genuine original-fiber symbols on a smooth manifold. -/
theorem forall_atlasGlobalSymbolSeminorm_eq_zero_iff
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (p : atlasGlobalSymbolSpace A B m) :
    (∀ J : AtlasGlobalSymbolSeminormIndex A B, atlasGlobalSymbolSeminorm A B m J p = 0) ↔
      p = 0 := by
  /- At any original base point choose a manifold chart and covering frames
  from A and B. The singleton compact spatial set with derivative orders zero
  detects every value of the coordinate symbol. Invert the same frame maps and
  cotangent chart derivative to recover the original fiber map. This covers all
  base points, including dimension zero. Conversely every seminorm vanishes at
  the zero symbol; empty bases and zero-rank frames introduce no extra premise. -/
  classical
  constructor
  · intro hp
    apply Subtype.ext
    funext x ξ
    -- The two covering atlases may have unrelated ranks at the chosen original fiber.
    obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hc := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have hz : c x ∈ atlasSymbolChartDomain A B c i j :=
      ⟨⟨c.map_source hx, by simpa only [Set.mem_preimage, c.left_inv hx] using hi⟩,
        by simpa only [Set.mem_preimage, c.left_inv hx] using hj⟩
    let J : AtlasGlobalSymbolSeminormIndex A B :=
      { chart := c
        mem_atlas := hc
        inputIndex := i
        outputIndex := j
        localIndex :=
          { compactSet := {c x}
            subset_domain := Set.singleton_subset_iff.mpr hz
            isCompact := isCompact_singleton
            spatialOrder := 0
            frequencyOrder := 0 } }
    let a : symbolSpace (atlasSymbolChartDomain A B c i j)
        (isOpen_atlasSymbolChartDomain A B c i j) m (A.rank i) (B.rank j) :=
      ⟨atlasGlobalSymbolInChart A B p.val c i j, p.property c hc i j⟩
    have hlocal : ∀ K : SymbolSeminormIndex (atlasSymbolChartDomain A B c i j),
        symbolSeminorm (isOpen_atlasSymbolChartDomain A B c i j) m K a = 0 := by
      intro K
      exact hp { J with localIndex := K }
    have hmap := (forall_symbolSeminorm_eq_zero_iff
      (isOpen_atlasSymbolChartDomain A B c i j) m a).mp hlocal
      (c x) hz (covectorInChart c x ξ)
    change atlasGlobalSymbolInChart A B p.val c i j (c x) (covectorInChart c x ξ) = 0 at hmap
    -- Undo the frames at the returned base point before transporting the dependent fiber.
    let y := c.symm (c x)
    have hiy : y ∈ (A.chart i).baseSet := by simpa only [y, c.left_inv hx] using hi
    have hjy : y ∈ (B.chart j).baseSet := by simpa only [y, c.left_inv hx] using hj
    let input := (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
      (A.frameLinearEquiv i y hiy).symm
    let output := (B.frameLinearEquiv j y hjy).trans
      (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv
    have hval : p.val y (covectorFromChart c y (covectorInChart c x ξ)) = 0 := by
      unfold atlasGlobalSymbolInChart at hmap
      rw [dite_eq_left (show c.symm (c x) ∈ (A.chart i).baseSet ∧
        c.symm (c x) ∈ (B.chart j).baseSet from ⟨hiy, hjy⟩)] at hmap
      ext v
      have htest := congrArg
        (fun L : EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
            EuclideanSpace ℂ (Fin (B.rank j)) ↦ output.symm (L (input.symm v))) hmap
      change output.symm (output ((p.val y (covectorFromChart c y (covectorInChart c x ξ)))
        (input (input.symm v)))) = output.symm 0 at htest
      simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, map_zero,
        LinearMap.zero_apply] using htest
    have hxval : p.val x (covectorFromChart c x (covectorInChart c x ξ)) = 0 :=
      (congrArg (fun z : M ↦ p.val z (covectorFromChart c z (covectorInChart c x ξ)) = 0)
        (c.left_inv hx)).mp hval
    rw [covectorFromChart_covectorInChart c hc x hx ξ] at hxval
    exact hxval
  · rintro rfl J
    exact map_zero _

end AtiyahSinger

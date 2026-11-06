/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.RelativeMetricDensity

/-!
# Positive smooth measures are local on open submanifolds

Public module ID: M1294.

A Borel measure is smooth positive when its actual subtype comap has this
property near every point. Extend each local density near a singleton and
compare in an arbitrary original chart. The resulting smooth densities agree
on overlaps because they represent the same measure; a countable open cover
then gives the full chart identity. No compact ambient manifold is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Smooth positivity of the actual subtype comaps on an open cover implies global positivity. -/
theorem isSmoothPositiveMeasure_of_locally_comap (μ : Measure M)
    (hμ : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      IsSmoothPositiveMeasure (n := n) (μ.comap (Subtype.val : U → M))) :
    IsSmoothPositiveMeasure (n := n) μ := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  -- Existing relative extension gives global smooth measures equal to μ near each same point.
  have hlocal (x : M) : ∃ (U : Opens M) (ν : Measure M), x ∈ U ∧
      IsSmoothPositiveMeasure (n := n) ν ∧ μ.restrict U = ν.restrict U := by
    obtain ⟨U, hx, hU⟩ := hμ x
    let := hU
    obtain ⟨ν, hν, V, hxV, hVU, heq⟩ := exists_smoothPositiveMeasure_extension (n := n) (M := M) U
      {x} (isCompact_singleton) (Set.singleton_subset_iff.mpr hx)
      (μ.comap (Subtype.val : U → M))
    refine ⟨V, ν, hxV (Set.mem_singleton x), hν, ?_⟩
    have hmap (ρ : Measure M) :
        Measure.map (Subtype.val : U → M) (ρ.comap (Subtype.val : U → M)) =
          ρ.restrict U := map_comap_subtype_coe U.isOpen.measurableSet ρ
    have h := congrArg (Measure.map (Subtype.val : U → M)) heq
    rw [← Measure.restrict_map measurable_subtype_coe V.isOpen.measurableSet,
      ← Measure.restrict_map measurable_subtype_coe V.isOpen.measurableSet,
      hmap ν, hmap μ,
      Measure.restrict_restrict_of_subset hVU,
      Measure.restrict_restrict_of_subset hVU] at h
    exact h.symm
  choose U ν hxU hν hμν using hlocal
  constructor
  intro c hc
  let θ := Measure.map c (μ.restrict c.source)
  let T (x : M) := c.target ∩ c.symm ⁻¹' (U x : Set M)
  have hT (x : M) : IsOpen (T x) := c.isOpen_inter_preimage_symm (U x).isOpen
  choose w hw hp hm using fun x : M ↦ (hν x).exists_smooth_density c hc
  have hmeasure (x : M) : θ.restrict (T x) =
      (volume.restrict (T x)).withDensity (fun y ↦ ENNReal.ofReal (w x y)) := by
    have hsub : c ⁻¹' T x ∩ c.source ⊆ (U x : Set M) := by
      intro z hz
      have h := hz.1.2
      change c.symm (c z) ∈ U x at h
      rwa [c.left_inv hz.2] at h
    have hpush : θ.restrict (T x) =
        (Measure.map c ((ν x).restrict c.source)).restrict (T x) := by
      dsimp only [θ]
      rw [Measure.restrict_map_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) (hT x).measurableSet,
        Measure.restrict_map_of_aemeasurable
          (c.continuousOn.aemeasurable c.open_source.measurableSet) (hT x).measurableSet,
        Measure.restrict_restrict' c.open_source.measurableSet,
        Measure.restrict_restrict' c.open_source.measurableSet]
      exact congrArg (Measure.map c) (Measure.restrict_congr_mono hsub (hμν x))
    rw [hpush, hm x, restrict_withDensity (hT x).measurableSet,
      Measure.restrict_restrict_of_subset (show T x ⊆ c.target from Set.inter_subset_left)]
  have hrestrict (x : M) : θ.restrict (T x) =
      (volume.withDensity (fun y ↦ ENNReal.ofReal (w x y))).restrict (T x) := by
    rw [restrict_withDensity (hT x).measurableSet]
    exact hmeasure x
  -- The actual common measure forces continuous positive coordinate weights to agree.
  have hcompat (x z : M) : Set.EqOn (w x) (w z) (T x ∩ T z) := by
    let V := T x ∩ T z
    have hV : IsOpen V := (hT x).inter (hT z)
    have heqx := Measure.restrict_congr_mono (s := V) Set.inter_subset_left (hrestrict x)
    have heqz := Measure.restrict_congr_mono (s := V) Set.inter_subset_right (hrestrict z)
    have heq : (volume.restrict V).withDensity (fun y ↦ ENNReal.ofReal (w x y)) =
        (volume.restrict V).withDensity (fun y ↦ ENNReal.ofReal (w z y)) := by
      simpa only [restrict_withDensity hV.measurableSet,
        Measure.restrict_restrict_of_subset (show V ⊆ T x from Set.inter_subset_left),
        Measure.restrict_restrict_of_subset (show V ⊆ T z from Set.inter_subset_right)]
          using heqx.symm.trans heqz
    have hxc := (hw x).continuousOn.mono
      (show V ⊆ c.target from fun _ h ↦ h.1.1)
    have hzc := (hw z).continuousOn.mono
      (show V ⊆ c.target from fun _ h ↦ h.2.1)
    have hae := (withDensity_eq_iff_of_sigmaFinite
      (hxc.aemeasurable hV.measurableSet).ennreal_ofReal
      (hzc.aemeasurable hV.measurableSet).ennreal_ofReal).mp heq
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure E)) _ hV hxc hzc
    filter_upwards [hae, ae_restrict_mem hV.measurableSet] with y hy hyV
    have h := congrArg ENNReal.toReal hy
    simpa only [ENNReal.toReal_ofReal (hp x y hyV.1.1).le,
      ENNReal.toReal_ofReal (hp z y hyV.2.1).le] using h
  let a (y : E) : ℝ := w (c.symm y) y
  have hcoverPoint (y : E) (hy : y ∈ c.target) : y ∈ T (c.symm y) :=
    ⟨hy, hxU _⟩
  have halocal (x : M) : Set.EqOn a (w x) (T x) := by
    intro y hy
    exact (hcompat x (c.symm y) ⟨hy, hcoverPoint y hy.1⟩).symm
  have hasmooth : ContDiffOn ℝ ∞ a c.target := by
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    refine ⟨T (c.symm y), hT _, hcoverPoint y hy, ?_⟩
    exact (((hw (c.symm y)).mono Set.inter_subset_left).congr (halocal _)).mono
      Set.inter_subset_right
  refine ⟨a, hasmooth, fun y hy ↦ hp _ y hy, ?_⟩
  -- A countable subcover upgrades these local measure identities to the entire original chart.
  have hcover : ⋃ x : M, T x = c.target := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      exact hx.1
    · intro y hy
      exact Set.mem_iUnion.mpr ⟨c.symm y, hcoverPoint y hy⟩
  obtain ⟨S, hS, hScov⟩ := TopologicalSpace.isOpen_iUnion_countable T hT
  have hcover' : ⋃ x : S, T x.val = c.target := by
    simpa only [Set.iUnion_subtype] using hScov.trans hcover
  let : Countable S := hS.to_subtype
  have hfull : θ.restrict c.target =
      ((volume.restrict c.target).withDensity (fun y ↦ ENNReal.ofReal (a y))).restrict
        c.target := by
    rw [← hcover', Measure.restrict_iUnion_congr]
    intro x
    rw [hcover', hmeasure x.val, restrict_withDensity (hT x.val).measurableSet,
      Measure.restrict_restrict_of_subset
        (show T x.val ⊆ c.target from Set.inter_subset_left)]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (hT x.val).measurableSet] with y hy
    exact congrArg ENNReal.ofReal ((halocal x.val hy).symm)
  have hθ : θ.restrict c.target = θ := by
    dsimp only [θ]
    rw [Measure.restrict_map_of_aemeasurable
      (c.continuousOn.aemeasurable c.open_source.measurableSet) c.open_target.measurableSet,
      Measure.restrict_restrict' c.open_source.measurableSet]
    have hh : c ⁻¹' c.target ∩ c.source = c.source :=
      Set.inter_eq_right.mpr (fun y hy ↦ c.map_source hy)
    rw [hh]
  rw [hθ, restrict_withDensity c.open_target.measurableSet,
    Measure.restrict_restrict c.open_target.measurableSet, Set.inter_self] at hfull
  exact hfull

end AtiyahSinger

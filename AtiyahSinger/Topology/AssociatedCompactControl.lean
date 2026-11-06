/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundle
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Compact control and local topology on the original associated quotient

Public module ID: M1529.

An invariant subset K of the original fiber space defines the subset of classes
[p,y] with y in K. It is the actual image of P times K in the existing quotient,
not a replacement associated carrier. Invariance alone makes membership
independent of the representative. For a compact Hausdorff principal base and
compact K this subset is compact, even when the group and P are noncompact.

The original quotient is Hausdorff when its base and fiber are Hausdorff, and
locally compact when its base and fiber are locally compact. These conclusions
use the specified principal local charts, with their original quotient topology;
no compact-group orbit-space separation theorem is substituted.

Sources: HU IV.5 and IV.7, and SG II.3 and Appendix A, for the associated quotient
and its local products. The finite compact chart-cover argument and the local
separation and compactness certificates are project supplements to those standard
constructions, not claimed numbered theorems in those sections. The compact
control is not asserted to be minimal support. The compactness and separation
certificates are proved below in the existing quotient topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable (G P Y : Type*) [Group G] [MulAction Gᵐᵒᵖ P] [MulAction G Y]

/-- The actual image of the original principal space times the supplied fiber subset. -/
def associatedControl (K : Set Y) : Set (AssociatedBundle G P Y) :=
  (fun q : P × Y ↦ associatedBundleMk G P Y q.1 q.2) '' (Set.univ ×ˢ K)

variable {G P Y}

/-- An invariant fiber subset is detected on each original representative of its quotient class. -/
theorem associatedControl_mk_mem_iff (K : Set Y)
    (hInv : ∀ (g : G) (y : Y), g • y ∈ K ↔ y ∈ K) (p : P) (y : Y) :
    associatedBundleMk G P Y p y ∈ associatedControl G P Y K ↔ y ∈ K := by
  /- A witness (q,v), with v ∈ K, represents the class of (p,y). The quotient
  relation gives y = g⁻¹ • v, and invariance transfers membership to y.
  Conversely, if y ∈ K, the pair (p,y) directly witnesses membership in
  the image. This argument uses neither topology nor principal freeness. -/
  constructor
  · rintro ⟨⟨q, v⟩, hv, hq⟩
    obtain ⟨g, hg⟩ := Quotient.exact hq
    have hy : y = g⁻¹ • v := congrArg Prod.snd hg
    rw [hy]
    exact (hInv g⁻¹ v).mpr hv.2
  · intro hy
    exact ⟨(p, y), ⟨Set.mem_univ p, hy⟩, rfl⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [ContinuousSMul Gᵐᵒᵖ P]
  [TopologicalSpace Y] [ContinuousSMul G Y]
  {B : Type*} [TopologicalSpace B] {projection : P → B}


set_option linter.unusedSectionVars false in
/-- Compact invariant fiber control gives a compact subset over the compact Hausdorff base. -/
theorem isCompact_associatedControl [CompactSpace B] [T2Space B]
    (hP : IsPrincipalBundle G projection) (K : Set Y) (hK : IsCompact K)
    (hInv : ∀ (g : G) (y : Y), g • y ∈ K ↔ y ∈ K) :
    IsCompact (associatedControl G P Y K) := by
  /- Stage 1: the actual principal chart domains cover B. Compact
  Hausdorffness gives finitely many compact closed subsets C_i covering B,
  each contained in one of these domains. The inverse principal chart at
  (b,1) gives a continuous section s_i on that domain, hence on C_i.
  Stage 2: map each C_i times K continuously into the original quotient by
  (b,y) mapped to [s_i(b),y]. Each image is compact because both factors are.
  These maps use the original quotient topology and actual principal sections;
  no compactness of the entire principal space or acting group is inferred.
  Stage 3: their finite union is exactly associatedControl K. Inclusion in
  that control follows from its image definition. Conversely, for [p,y]
  with y in K, choose C_i containing projection(p). The principal chart
  writes p=s_i(projection(p))*g. The original quotient relation replaces
  [p,y] by [s_i(projection(p)),g*y], and invariance keeps g*y in K. Thus the
  finite union covers the exact specified control, proving compactness.
  No closedness or Hausdorffness of K or Y is used in this argument. -/
  classical
  -- Choose compact neighborhoods inside the original principal chart domains.
  choose e he hequiv using hP.exists_trivialization
  choose C hCcompact hCinter hCsub using
    (fun b : B ↦ exists_compact_subset (e b).open_baseSet (he b))
  obtain ⟨t, ht⟩ := finite_cover_nhds (fun b : B ↦
    mem_interior_iff_mem_nhds.mp (hCinter b))
  let localMap (b : B) (z : B × Y) : AssociatedBundle G P Y :=
    associatedBundleMk G P Y ((e b).toOpenPartialHomeomorph.symm (z.1, 1)) z.2
  have hcompact (b : B) : IsCompact (localMap b '' (C b ×ˢ K)) := by
    apply ((hCcompact b).prod hK).image_of_continuousOn
    apply continuous_quot_mk.comp_continuousOn
    exact ((e b).toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_fst.prodMk continuous_const).continuousOn
      (fun z hz ↦ (e b).mem_target.mpr (hCsub b hz.1))).prodMk
      continuous_snd.continuousOn
  -- The finite union of these actual quotient images is exactly the specified control.
  have hcover : associatedControl G P Y K = ⋃ b ∈ t, localMap b '' (C b ×ˢ K) := by
    apply Set.Subset.antisymm
    · rintro q ⟨⟨p, y⟩, hy, rfl⟩
      have hpcover : projection p ∈ ⋃ b ∈ t, C b := by rw [ht]; trivial
      obtain ⟨b, hbt, hpC⟩ := Set.mem_iUnion₂.mp hpcover
      have hpbase : projection p ∈ (e b).baseSet := hCsub b hpC
      let p₀ := (e b).toOpenPartialHomeomorph.symm (projection p, 1)
      obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p₀ p ((e b).proj_symm_apply' hpbase)
      apply Set.mem_iUnion₂.mpr
      refine ⟨b, hbt, (projection p, g • y), ⟨hpC, (hInv g y).mpr hy.2⟩, ?_⟩
      change associatedBundleMk G P Y p₀ (g • y) = associatedBundleMk G P Y p y
      rw [← associatedBundleMk_smul, hg]
    · intro q hq
      obtain ⟨b, _, z, hz, rfl⟩ := Set.mem_iUnion₂.mp hq
      exact ⟨((e b).toOpenPartialHomeomorph.symm (z.1, 1), z.2),
        ⟨Set.mem_univ _, hz.2⟩, rfl⟩
  rw [hcover]
  exact t.isCompact_biUnion (fun b _ ↦ hcompact b)

/-- Hausdorff base and fiber separate points in the original locally trivial associated quotient. -/
theorem associatedBundle_t2Space [T2Space B] [T2Space Y]
    (hP : IsPrincipalBundle G projection) : T2Space (AssociatedBundle G P Y) := by
  /- If the base projections agree, choose one associated chart containing both
  quotient points. Its target lies in B × Y, so Hausdorff separation there
  pulls back to disjoint open neighborhoods in the chart source.
  If the projections differ, pull back their separating neighborhoods under
  the continuous associated projection. Compactness of G is unnecessary. -/
  classical
  constructor
  intro q r hne
  by_cases hbase : associatedBundleProjection (F := Y) hP q =
      associatedBundleProjection (F := Y) hP r
  · -- Equal base points lie in one common original associated chart.
    obtain ⟨e, he, hequiv⟩ := hP.exists_trivialization
      (associatedBundleProjection (F := Y) hP q)
    obtain ⟨eA, hA, _, _⟩ := exists_associatedBundleTrivialization (F := Y) hP e hequiv
    have hq : q ∈ eA.source := eA.mem_source.mpr (hA.symm ▸ he)
    have hr : r ∈ eA.source := eA.mem_source.mpr (hbase ▸ (hA.symm ▸ he))
    have hcoord : eA q ≠ eA r := fun h ↦ hne (eA.injOn hq hr h)
    obtain ⟨u, v, hu, hv, hqu, hrv, huv⟩ := t2_separation hcoord
    refine ⟨eA.source ∩ eA ⁻¹' u, eA.source ∩ eA ⁻¹' v,
      eA.toOpenPartialHomeomorph.isOpen_inter_preimage hu,
      eA.toOpenPartialHomeomorph.isOpen_inter_preimage hv, ⟨hq, hqu⟩, ⟨hr, hrv⟩, ?_⟩
    exact Set.disjoint_left.mpr (fun z hz hw ↦ Set.disjoint_left.mp huv hz.2 hw.2)
  · -- Distinct projections are separated by the original continuous base map.
    exact separated_by_continuous (associatedBundleProjection (F := Y) hP).continuous hbase

/-- Local compactness of the original base and fiber transfers through the associated charts. -/
theorem associatedBundle_locallyCompactSpace [LocallyCompactSpace B] [LocallyCompactSpace Y]
    (hP : IsPrincipalBundle G projection) : LocallyCompactSpace (AssociatedBundle G P Y) := by
  /- At a given quotient point use a principal chart at its projection and
  the corresponding original associated chart. Its target is an open subset
  of the locally compact product B times Y. A neighborhood there contains
  a compact neighborhood inside that chart target. The actual inverse chart
  carries it continuously to a compact neighborhood in the original quotient.
  Applying this construction to every neighborhood establishes local
  compactness. This local argument needs no separation, compactness of G/P,
  global finite chart cover, or continuous global choice of principal points. -/
  constructor
  intro q U hU
  obtain ⟨e, he, hequiv⟩ := hP.exists_trivialization
    (associatedBundleProjection (F := Y) hP q)
  obtain ⟨eA, hA, _, _⟩ := exists_associatedBundleTrivialization (F := Y) hP e hequiv
  have hq : q ∈ eA.source := eA.mem_source.mpr (hA.symm ▸ he)
  let t := eA.toOpenPartialHomeomorph
  have ht : t q ∈ t.target := t.map_source hq
  -- Take a compact neighborhood inside both the chart target and the prescribed neighborhood.
  have hpre : t.symm ⁻¹' U ∈ nhds (t q) := by
    apply t.continuousAt_symm ht
    simpa only [t.left_inv hq] using hU
  obtain ⟨C, hCnhds, hCsub, hCcompact⟩ :=
    local_compact_nhds (Filter.inter_mem hpre (t.open_target.mem_nhds ht))
  refine ⟨t.symm '' C, ?_, ?_, ?_⟩
  · have himage := t.symm.image_mem_nhds ht hCnhds
    simpa only [t.left_inv hq] using himage
  · rintro z ⟨y, hy, rfl⟩
    exact (hCsub hy).1
  · exact hCcompact.image_of_continuousOn (t.continuousOn_symm.mono
      (fun y hy ↦ (hCsub hy).2))

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereStereographic
public import AtiyahSinger.Reuse.Poincare.CompactDisk
public import AtiyahSinger.Topology.CompactificationCohomologyComparison

/-!
# Compact supports and the original fiberwise sphere compactification

Public module ID: M1115.

The original sphere of the real bundle plus a line is compact over a compact
Hausdorff base. Its original stereographic chart embeds the bundle as the complement of
the infinity section. Projection onto this same section is a retraction; hence
relative classes for that section inject into ordinary sphere cohomology.
No such claim is made for a disk bundle after forgetting its boundary.

Sources: SG III.13, fiberwise sphere compactification; Hatcher, Algebraic
Topology, Sections 3.1--3.3, for the relative cohomology splitting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Topology
open scoped Manifold ContDiff

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [hEB : FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [hB : IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [hV : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [hMetric : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere

local notation "Rr" => EuclideanSpace ℝ (Fin r)
local notation "S" => SphereCompactification r V

/-- Projection of the original sphere to the unchanged bundle base. -/
def sphereCompactificationProjection : C(S, B) :=
  ⟨fun z ↦ z.val.1.proj, (FiberBundle.continuous_proj Rr V).comp
    (continuous_fst.comp continuous_subtype_val)⟩

/-- The infinity section consists of the original zero vector and north pole. -/
def sphereCompactificationInfinity : C(B, S) := by
  let north (x : B) : S := ⟨((⟨x, 0⟩ : TotalSpace Rr V), 1), by simp⟩
  refine ⟨north, ?_⟩
  apply Continuous.subtype_mk
  exact (Bundle.Trivialization.continuous_zeroSection ℝ
    (F := Rr) (E := V)).prodMk continuous_const

include hMetric

omit hEB hB hV in
/-- Over a compact Hausdorff base the original fiberwise sphere compactification is compact. -/
theorem compactSpace_sphereCompactification [T2Space B] [CompactSpace B] : CompactSpace S := by
  obtain ⟨g, hg, hmetric⟩ := hMetric.exists_contMDiff
  let : IsContinuousRiemannianBundle Rr V := ⟨⟨g, hg.continuous, hmetric⟩⟩
  let A : Set (TotalSpace Rr V × ℝ) := {z | ‖z.1.snd‖ ^ 2 + z.2 ^ 2 = 1}
  have hnorm : Continuous (fun v : TotalSpace Rr V ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  have hclosed : IsClosed A := isClosed_eq
    (((hnorm.comp continuous_fst).pow 2).add (continuous_snd.pow 2)) continuous_const
  have hdisk : IsCompact {v : TotalSpace Rr V | ‖v.snd‖ ≤ 1} := by
    simpa using Poincare.VectorBundle.isCompact_disk_over
      (F := Rr) (E := V) (K := Set.univ) isCompact_univ 1
  have hcompact : IsCompact A :=
    (hdisk.prod (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))).of_isClosed_subset hclosed (by
    intro z hz
    have heq : ‖z.1.snd‖ ^ 2 + z.2 ^ 2 = 1 := hz
    refine ⟨?_, ?_, ?_⟩
    · change ‖z.1.snd‖ ≤ 1
      nlinarith [sq_nonneg z.2, norm_nonneg z.1.snd]
    · nlinarith [sq_nonneg ‖z.1.snd‖]
    · nlinarith [sq_nonneg ‖z.1.snd‖])
  exact isCompact_iff_compactSpace.mp hcompact

include hEB hB hV hMetric

/-- The existing stereographic chart embeds the original bundle in its original sphere. -/
def sphereCompactificationInclusion : C(TotalSpace Rr V, S) := by
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let A := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace A
  let c := frameSphereHomeomorph (EB := EB) r V
  let e := frameSphereStereographic (EB := EB) r V
  exact ⟨fun v ↦ c (e.symm v), c.continuous.comp
    (e.symm.isOpenEmbedding (frameSphereStereographic_spec (EB := EB) r V).2.1).continuous⟩

/-- The specified inclusion is an open embedding into the original sphere. -/
theorem isOpenEmbedding_sphereCompactificationInclusion :
    IsOpenEmbedding (sphereCompactificationInclusion (EB := EB) r V) := by
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let A := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace A
  let c := frameSphereHomeomorph (EB := EB) r V
  let e := frameSphereStereographic (EB := EB) r V
  exact c.isOpenEmbedding.comp
    (e.symm.isOpenEmbedding (frameSphereStereographic_spec (EB := EB) r V).2.1)

/-- The specified open image omits exactly the original north section. -/
theorem range_sphereCompactificationInclusion :
    Set.range (sphereCompactificationInclusion (EB := EB) r V) = {z : S | z.val.2 ≠ 1} := by
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let A := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace A
  let c := frameSphereHomeomorph (EB := EB) r V
  let e := frameSphereStereographic (EB := EB) r V
  have he := frameSphereStereographic_spec (EB := EB) r V
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    have hv : v ∈ e.target := by rw [he.2.1]; trivial
    have hm := e.map_target hv
    rw [he.1] at hm
    exact hm
  · intro hz
    have hz' : c.symm z ∈ e.source := by
      rw [he.1]
      change (c (c.symm z)).val.2 ≠ 1
      rw [c.apply_symm_apply]
      exact hz
    refine ⟨e (c.symm z), ?_⟩
    change c (e.symm (e (c.symm z))) = z
    rw [e.left_inv hz', c.apply_symm_apply]

/-- Classes relative to the infinity section inject into ordinary cohomology of this sphere. -/
theorem relativeSingularCohomologyToOrdinary_sphere_injective
    (R : Type) [CommRing R] (k : ℕ) :
    Function.Injective (relativeSingularCohomologyToOrdinary R
      ((Set.range (sphereCompactificationInclusion (EB := EB) r V))ᶜ) k) := by
  let j := sphereCompactificationInclusion (EB := EB) r V
  let A : Set S := (Set.range j)ᶜ
  have hA (z : S) : z ∈ A ↔ z.val.2 = 1 := by
    dsimp only [A, j]
    rw [range_sphereCompactificationInclusion (EB := EB) r V]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
  let north := sphereCompactificationInfinity r V
  let πS := sphereCompactificationProjection r V
  let retraction : C(S, A) := ⟨fun z ↦ ⟨north (πS z), (hA _).mpr rfl⟩,
    (north.continuous.comp πS.continuous).subtype_mk _⟩
  have hret : retraction.comp (ContinuousMap.subtypeVal A) = ContinuousMap.id A := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have ht := (hA z.val).mp z.property
      have heq : ‖z.val.val.1.snd‖ ^ 2 + z.val.val.2 ^ 2 = 1 := z.val.property
      rw [ht] at heq
      have hn : z.val.val.1.snd = 0 := by
        apply norm_eq_zero.mp
        nlinarith [norm_nonneg z.val.val.1.snd]
      cases z with
      | mk z hz =>
        cases z with
        | mk w hw =>
          rcases w with ⟨⟨x, v⟩, t⟩
          change (⟨x, 0⟩ : TotalSpace Rr V) = ⟨x, v⟩
          change v = 0 at hn
          rw [hn]
    · exact ((hA z.val).mp z.property).symm
  exact relativeSingularCohomologyToOrdinary_injective_of_retraction R A retraction hret k

end AtiyahSinger

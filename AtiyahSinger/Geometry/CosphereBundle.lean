/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentMetric

import AtiyahSinger.Reuse.Poincare.CompactDisk

/-!
# The cosphere bundle and radial retraction

Public module ID: M1146.

The unit cotangent sphere uses the actual total-space subspace topology.
The normalization formula is defined on all covectors. Its map to unit covectors
is restricted to nonzero covectors, with explicit length and base preservation.
No positivity of the manifold dimension is assumed.
These standard sphere-bundle constructions supply the geometric domain for
SG III.7.10--7.11; their detailed Lean interfaces are project deductions.
Compactness reuses Poincare's PR06 compact-sphere theorem on the same metric fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Nonzero covectors with the subspace topology of the cotangent bundle. -/
abbrev PuncturedCotangentBundle : Type _ :=
  {z : CotangentTotalSpace (n := n) (M := M) // z.snd ≠ 0}

/-- Unit covectors for an explicit smooth cotangent metric. -/
abbrev CosphereBundle (g : SmoothCotangentMetric (n := n) (M := M)) : Type _ :=
  {z : CotangentTotalSpace (n := n) (M := M) // g.length z.proj z.snd = 1}

namespace SmoothCotangentMetric

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- The normalized covector in the same real cotangent fiber. -/
def normalize (x : M) (ξ : CotangentFiber (n := n) x) : CotangentFiber (n := n) x :=
  (g.length x ξ)⁻¹ • ξ

/-- A nonzero covector normalizes to unit length. -/
theorem length_normalize (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
    g.length x (g.normalize x ξ) = 1 := by
  -- Only a nonzero original covector has a cancellable positive metric length.
  rw [normalize, g.length_smul, abs_of_pos (inv_pos.mpr (g.length_pos x ξ hξ))]
  exact inv_mul_cancel₀ (g.length_pos x ξ hξ).ne'

/-- Normalization cannot annihilate a nonzero covector. -/
theorem normalize_ne_zero (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
    g.normalize x ξ ≠ 0 := by
  intro hzero
  have hunit := g.length_normalize x ξ hξ
  rw [hzero, (g.length_eq_zero_iff x 0).mpr rfl] at hunit
  exact zero_ne_one hunit

/-- Length and direction reconstruct a covector, including zero. -/
theorem length_smul_normalize (x : M) (ξ : CotangentFiber (n := n) x) :
    g.length x ξ • g.normalize x ξ = ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ, normalize]
  · rw [normalize, smul_smul, mul_inv_cancel₀ (g.length_pos x ξ hξ).ne', one_smul]

/-- Positive scaling preserves the normalized direction. -/
theorem normalize_pos_smul (x : M) (ξ : CotangentFiber (n := n) x)
    (t : ℝ) (ht : 0 < t) : g.normalize x (t • ξ) = g.normalize x ξ := by
  -- The positive scale cancels before any assumption on the covector is needed.
  simp only [normalize, g.length_smul, abs_of_pos ht, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

/-- Normalizing an already unit covector changes nothing. -/
theorem normalize_of_length_eq_one (x : M) (ξ : CotangentFiber (n := n) x)
    (hξ : g.length x ξ = 1) : g.normalize x ξ = ξ := by
  simp only [normalize, hξ, inv_one, one_smul]

/-- Every point of the cosphere is a nonzero covector. -/
theorem cosphere_ne_zero (z : CosphereBundle g) : z.val.snd ≠ 0 := by
  intro hzero
  have hunit := z.property
  rw [hzero, (g.length_eq_zero_iff z.val.proj 0).mpr rfl] at hunit
  exact zero_ne_one hunit

/-- The actual radial retraction onto the metric cosphere. -/
def radial (z : PuncturedCotangentBundle (n := n) (M := M)) : CosphereBundle g :=
  ⟨⟨z.val.proj, g.normalize z.val.proj z.val.snd⟩,
    g.length_normalize z.val.proj z.val.snd z.property⟩

/-- The inclusion of unit covectors into nonzero covectors. -/
def cosphereInclusion (z : CosphereBundle g) : PuncturedCotangentBundle (n := n) (M := M) :=
  ⟨z.val, g.cosphere_ne_zero z⟩

/-- Radial retraction is continuous in the original bundle topology. -/
theorem continuous_radial : Continuous g.radial := by
  -- In the original bundle coordinates the map is reciprocal length times the same vector.
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let F := CotangentModel n
  let E := CotangentFiber (n := n) (M := M)
  let e := trivializationAt F E z₀.val.proj
  have hz := (FiberBundle.continuousAt_totalSpace F
    (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦ z.val) (x₀ := z₀)).mp
      continuous_subtype_val.continuousAt
  have hlength : Continuous (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦
      g.length z.val.proj z.val.snd) := g.continuous_length.comp continuous_subtype_val
  have hinv := hlength.continuousAt.inv₀ (g.length_pos z₀.val.proj z₀.val.snd z₀.property).ne'
  apply (FiberBundle.continuousAt_totalSpace F _).mpr
  refine ⟨hz.1, ?_⟩
  apply (hinv.smul hz.2).congr_of_eventuallyEq
  filter_upwards [hz.1.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E z₀.val.proj))] with z hz'
  change (e ⟨z.val.proj, g.normalize z.val.proj z.val.snd⟩).2 =
    (g.length z.val.proj z.val.snd)⁻¹ • (e z.val).2
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hz',
    ← e.continuousLinearMapAt_apply_of_mem ℝ hz']
  exact map_smul (e.continuousLinearMapAt ℝ z.val.proj) _ _

/-- The cosphere inclusion is continuous. -/
theorem continuous_cosphereInclusion : Continuous g.cosphereInclusion := by
  exact continuous_subtype_val.subtype_mk _

/-- The radial map is a retraction of the inclusion. -/
theorem radial_cosphereInclusion (z : CosphereBundle g) :
    g.radial (g.cosphereInclusion z) = z := by
  apply Subtype.ext
  change (⟨z.val.proj, g.normalize z.val.proj z.val.snd⟩ : CotangentTotalSpace) = z.val
  rw [g.normalize_of_length_eq_one z.val.proj z.val.snd z.property]

/-- Every unit covector lies in the image of radial normalization. -/
theorem radial_surjective : Function.Surjective g.radial := by
  intro z
  exact ⟨g.cosphereInclusion z, g.radial_cosphereInclusion z⟩

/-- The cosphere is a closed subset of the cotangent total space. -/
theorem isClosed_cosphere :
    IsClosed {z : CotangentTotalSpace (n := n) (M := M) | g.length z.proj z.snd = 1} := by
  exact isClosed_eq g.continuous_length continuous_const

/-- The unit cotangent bundle of a compact Hausdorff base is compact. -/
theorem isCompact_cosphere [T2Space M] [CompactSpace M] :
    IsCompact {z : CotangentTotalSpace (n := n) (M := M) | g.length z.proj z.snd = 1} := by
  -- Reuse PR06 on the same fibers, with the topology-compatible metric supplied by g.
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) :=
    ⟨g.toRiemannianMetric⟩
  let : ∀ x : M, NormedAddCommGroup (CotangentFiber (n := n) x) := fun x ↦ inferInstance
  let : ∀ x : M, InnerProductSpace ℝ (CotangentFiber (n := n) x) := fun x ↦ inferInstance
  let : IsContinuousRiemannianBundle (CotangentModel n)
      (CotangentFiber (n := n) (M := M)) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have hcompact := Poincare.VectorBundle.isCompact_sphere_over
    (F := CotangentModel n) (E := CotangentFiber (n := n) (M := M))
    (K := Set.univ) isCompact_univ 1
  -- The native Riemannian norm is exactly the original explicitly specified length.
  have hnorm (z : CotangentTotalSpace (n := n) (M := M)) :
      ‖z.snd‖ = g.length z.proj z.snd := norm_eq_sqrt_real_inner z.snd
  simpa only [Set.mem_univ, true_and, hnorm] using hcompact

/-- Zero-dimensional manifolds have no unit cotangent covectors. -/
theorem isEmpty_cosphere_of_dim_zero (hn : n = 0) : IsEmpty (CosphereBundle g) := by
  subst n
  refine ⟨fun z ↦ ?_⟩
  let : Subsingleton (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) z.val.proj) := by
    unfold TangentSpace
    infer_instance
  have hzero : z.val.snd = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  exact g.cosphere_ne_zero z hzero

/-- Cosphere compactness packaged for downstream compact-domain arguments. -/
theorem compactSpace_cosphere [T2Space M] [CompactSpace M] : CompactSpace (CosphereBundle g) := by
  exact isCompact_iff_compactSpace.mp g.isCompact_cosphere

end SmoothCotangentMetric

end AtiyahSinger

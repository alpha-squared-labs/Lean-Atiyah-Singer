/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Geometry.SphereTangentCoordinates

/-!
# The actual open manifold in a normalized sphere pole chart

Public module ID: M1422.

The prescribed inverse stereographic chart is a diffeomorphism onto the
complement of the opposite pole. Its actual domain, native sphere atlas and
orthogonal action are retained, including dimension zero. This gives the
geometric input for the common-open excision comparison in ASI I (4.4).

Source: ASI I Proposition (4.4), pp.504--505; the explicit normalized charts
and their metric comparison are project supplements to SG III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator

/-- The actual image of the normalized pole chart, with its inherited smooth atlas. -/
def orthogonalSpherePoleOpen (r : ℕ) (atInfinity : Bool) : Opens (OrthogonalSphere r) :=
  ⟨(orthogonalSphereNormalizedChart r atInfinity).source,
    (orthogonalSphereNormalizedChart r atInfinity).open_source⟩

/-- The specified inverse normalized chart as a diffeomorphism onto its actual image. -/
def orthogonalSpherePoleDiffeomorph (r : ℕ) (atInfinity : Bool) :
    EuclideanSpace ℝ (Fin r) ≃ₘ⟮𝓡 r, 𝓡 r⟯ orthogonalSpherePoleOpen r atInfinity := by
  let e := orthogonalSphereNormalizedChart r atInfinity
  have ht : e.target = Set.univ :=
    (orthogonalSphereNormalizedChart_properties r atInfinity).2.1
  have hm (u : EuclideanSpace ℝ (Fin r)) : u ∈ e.target := ht.symm ▸ Set.mem_univ u
  have hs := orthogonalSphereNormalizedChart_smooth r atInfinity
  exact {
    toFun u := ⟨e.symm u, e.map_target (hm u)⟩
    invFun x := e x
    left_inv u := e.right_inv (hm u)
    right_inv x := Subtype.ext (e.left_inv x.property)
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff (orthogonalSpherePoleOpen r atInfinity) _).mp
      exact hs.2
    contMDiff_invFun := by
      intro x
      exact ((hs.1 x x.property).contMDiffAt (e.open_source.mem_nhds x.property)).comp x
        (contMDiff_subtype_val (n := ∞) x) }

/-- The actual inverse normalized chart is a local diffeomorphism into the native sphere. -/
theorem isLocalDiffeomorph_orthogonalSphereNormalizedChart_symm (r : ℕ) (atInfinity : Bool) :
    IsLocalDiffeomorph (𝓡 r) (𝓡 r) ∞
      (orthogonalSphereNormalizedChart r atInfinity).symm := by
  let e := orthogonalSphereNormalizedChart r atInfinity
  have hs := orthogonalSphereNormalizedChart_smooth r atInfinity
  -- The entire Euclidean source lies in the inverse chart's actual domain.
  let d : PartialDiffeomorph (𝓡 r) (𝓡 r) (EuclideanSpace ℝ (Fin r))
      (OrthogonalSphere r) ∞ := {
    toPartialEquiv := e.symm.toPartialEquiv
    open_source := e.open_target
    open_target := e.open_source
    contMDiffOn_toFun := hs.2.contMDiffOn
    contMDiffOn_invFun := hs.1 }
  intro u
  apply PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 r) (𝓡 r) ∞ d
  change u ∈ e.target
  exact (orthogonalSphereNormalizedChart_properties r atInfinity).2.1.symm ▸ Set.mem_univ u

/-- The same pole diffeomorphism intertwines the original orthogonal transformations. -/
theorem orthogonalSpherePoleDiffeomorph_equivariant (r : ℕ) (atInfinity : Bool)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (u : EuclideanSpace ℝ (Fin r)) :
    (orthogonalSpherePoleDiffeomorph r atInfinity (orthogonalEuclideanIsometry r A u) :
      OrthogonalSphere r) = A • (orthogonalSpherePoleDiffeomorph r atInfinity u :
        OrthogonalSphere r) := by
  -- Project the already established equivariance of the actual tangent chart.
  let z : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 (fun i ↦ (u i : ℂ))
  have hre : (WithLp.toLp 2 (fun i ↦ ((A • z) i).re) : EuclideanSpace ℝ (Fin r)) =
      orthogonalEuclideanIsometry r A u := by
    ext i
    change (∑ j, (A.val i j : ℂ) * (u j : ℂ)).re = ∑ j, A.val i j * u j
    simp
  have h := congrArg TotalSpace.proj (orthogonalSphereTangentChart_equivariant r atInfinity A z)
  change (orthogonalSphereNormalizedChart r atInfinity).symm
      (WithLp.toLp 2 (fun i ↦ ((A • z) i).re)) =
    A • (orthogonalSphereNormalizedChart r atInfinity).symm
      (WithLp.toLp 2 (fun i ↦ (z i).re)) at h
  rw [hre] at h
  change (orthogonalSphereNormalizedChart r atInfinity).symm
      (orthogonalEuclideanIsometry r A u) =
    A • (orthogonalSphereNormalizedChart r atInfinity).symm u
  simpa only [z, Complex.ofReal_re, WithLp.toLp_ofLp] using h

end AtiyahSinger

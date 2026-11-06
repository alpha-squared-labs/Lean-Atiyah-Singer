/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalGroupManifold
public import AtiyahSinger.Geometry.SphereTangentCoordinates
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.EquivariantBottRepresentation
public import AtiyahSinger.Topology.EquivariantOpenExtension
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality

/-!
# The actual two pole maps and tangent-fiber reversal

Public module ID: M2165.

AL02 uses the original native tangent total space with the derivative O(r)
action. The two point pushforwards are the existing equivariant Bott map followed
by actual open extension through the corresponding tangent stereographic chart.
The complex normal coordinate is base plus I times tangent fiber. The normalized
chart has derivative twice the usual pole identification; this positive complex
linear scaling preserves the Bott class. Neither map is defined by the desired
sphere decomposition or an analytical index.

The involution theta fixes the sphere point and negates only the tangent vector.
Its actual proper equivariant pullback is kept separate from the antipodal map
of the sphere. Sources: ASI I, pp.499--500, Lemma (3.2); the point Thom/open
construction is the point case of its section 2 pushforward. Fiber reversal
and the specified chart-conjugation comparison are proved below. The pole
pushforward retains its separate Bott and open-extension dependencies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent tangentBundleFullChartedSpace

set_option maxSynthPendingDepth 25

/-- Negating precisely the native tangent fiber is continuous, proper and equivariant. -/
theorem orthogonalSphereTangentNegation_properties (r : ℕ) :
    let f := fun z : TangentBundle (𝓡 r) (OrthogonalSphere r) ↦
      (⟨z.proj, -z.snd⟩ : TangentBundle (𝓡 r) (OrthogonalSphere r))
    Continuous f ∧ IsProperMap f ∧
      ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
        (z : TangentBundle (𝓡 r) (OrthogonalSphere r)), f (A • z) = A • f z := by
  /- Stage 1: in every native tangent chart the map is (x,v) -> (x,-v),
  so the original vector-bundle topology makes it continuous. Applying it
  twice is the identity on both coordinates; the resulting homeomorphism
  makes this exact map proper, although the tangent space is noncompact.
  Stage 2: each actual derivative action is real linear on the moving
  fiber, hence commutes with negation. Both routes have the same moved
  base point. This is fiber reversal, not the sphere antipodal action. -/
  let V := EuclideanSpace ℝ (Fin r)
  let f : TangentBundle (𝓡 r) (OrthogonalSphere r) →
      TangentBundle (𝓡 r) (OrthogonalSphere r) := fun z ↦ ⟨z.proj, -z.snd⟩
  -- Each original tangent trivialization turns this map into negation of its fiber coordinate.
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro z
    let e := trivializationAt V (TangentSpace (𝓡 r) : OrthogonalSphere r → Type) z.proj
    have hz : z.proj ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hzout : f z ∈ e.source := e.mem_source.mpr hz
    apply (e.tendsto_nhds_iff hzout).mpr
    refine ⟨?_, ?_⟩
    · change Filter.Tendsto (fun w : TangentBundle (𝓡 r) (OrthogonalSphere r) ↦ w.proj)
        (nhds z) (nhds z.proj)
      exact (FiberBundle.continuous_proj V
        (TangentSpace (𝓡 r) : OrthogonalSphere r → Type)).continuousAt
    have hproj : Continuous (fun w : TangentBundle (𝓡 r) (OrthogonalSphere r) ↦
        w.proj) := FiberBundle.continuous_proj V
          (TangentSpace (𝓡 r) : OrthogonalSphere r → Type)
    have hcoords := ((e.continuousAt (e.mem_source.mpr hz)).snd).neg
    apply hcoords.congr_of_eventuallyEq
    filter_upwards [hproj.continuousAt (e.open_baseSet.mem_nhds hz)] with w hw
    exact (e.linear ℝ hw).map_neg w.snd
  -- The inverse is exactly the same fiber map, so the resulting homeomorphism is proper.
  have hinv : Function.Involutive f := by
    intro z
    cases z
    simp only [f, neg_neg]
  let e : TangentBundle (𝓡 r) (OrthogonalSphere r) ≃ₜ
      TangentBundle (𝓡 r) (OrthogonalSphere r) :=
    { toFun := f
      invFun := f
      left_inv := hinv
      right_inv := hinv
      continuous_toFun := hf
      continuous_invFun := hf }
  refine ⟨hf, e.isProperMap, ?_⟩
  -- The actual derivative action is real linear on the same moving tangent fiber.
  intro A z
  change (⟨(orthogonalSphereDiffeomorph r A) z.proj,
      -(mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) z.proj z.snd)⟩ :
      TangentBundle (𝓡 r) (OrthogonalSphere r)) =
    ⟨(orthogonalSphereDiffeomorph r A) z.proj,
      mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) z.proj (-z.snd)⟩
  rw [map_neg]

/-- The original tangent involution fixing the base point. -/
def orthogonalSphereTangentNegation (r : ℕ) :
    C(TangentBundle (𝓡 r) (OrthogonalSphere r),
      TangentBundle (𝓡 r) (OrthogonalSphere r)) where
  toFun z := ⟨z.proj, -z.snd⟩
  continuous_toFun := (orthogonalSphereTangentNegation_properties r).1

/-- Pullback by that same proper fiber reversal on the original equivariant support group. -/
def orthogonalSphereTangentNegationPullback (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) →+
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  equivariantSupportTripleKZeroPullback (orthogonalSphereTangentNegation r)
    (orthogonalSphereTangentNegation_properties r).2.2
    (orthogonalSphereTangentNegation_properties r).2.1

/-- The point Thom map followed by open extension through its specified tangent chart. -/
def orthogonalSpherePolePushforward (r : ℕ) (atInfinity : Bool) :
    RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ) →ₗ[
      RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)]
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) := by
  letI := compactSpace_orthogonalGroup r
  letI := (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
  letI := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r))
    (TangentBundle (𝓡 r) (OrthogonalSphere r))
  exact (equivariantSupportTripleKZeroOpenLinearMap
    (orthogonalSphereTangentChart r atInfinity)
    (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity)
    (orthogonalSphereTangentChart_equivariant r atInfinity)).comp
      (equivariantBottLinearMap (orthogonalComplexification_unitary r))

/-- The actual coordinate conjugation is exactly fiber reversal in either tangent chart. -/
theorem orthogonalSphereTangentChart_conjugation (r : ℕ) (atInfinity : Bool)
    (z : EuclideanSpace ℂ (Fin r)) :
    orthogonalSphereTangentChart r atInfinity (orthogonalComplexificationConjugation r z) =
      orthogonalSphereTangentNegation r (orthogonalSphereTangentChart r atInfinity z) := by
  /- Conjugation keeps the real coordinate u and negates the imaginary
  coordinate v. The base chart therefore returns exactly the same sphere
  point. Its specified real-linear derivative sends -v to the negative
  of its value on v. This proves equality of the two actual total vectors,
  including dimension zero; the base has not been reflected or negated. -/
  -- Conjugation fixes the specified real base coordinate and negates the imaginary part.
  have hre : (WithLp.toLp 2 (fun i : Fin r ↦ (star (z i)).re) :
      EuclideanSpace ℝ (Fin r)) = WithLp.toLp 2 (fun i ↦ (z i).re) := by
    ext i
    simp
  have him : (WithLp.toLp 2 (fun i : Fin r ↦ (star (z i)).im) :
      EuclideanSpace ℝ (Fin r)) = -(WithLp.toLp 2 (fun i ↦ (z i).im)) := by
    ext i
    simp
  -- The same inverse chart and its real-linear derivative determine both tangent vectors.
  change orthogonalSphereTangentChartMap r atInfinity
      (orthogonalComplexificationConjugation r z) =
    (⟨(orthogonalSphereTangentChartMap r atInfinity z).proj,
      -(orthogonalSphereTangentChartMap r atInfinity z).snd⟩ :
      TangentBundle (𝓡 r) (OrthogonalSphere r))
  dsimp only [orthogonalSphereTangentChartMap, orthogonalComplexificationConjugation,
    ContinuousMap.coe_mk, PiLp.toLp_apply]
  rw [hre, him]
  apply TotalSpace.ext
  · rfl
  · apply heq_of_eq
    exact map_neg (mfderiv (𝓡 r) (𝓡 r)
      (orthogonalSphereNormalizedChart r atInfinity).symm
        (WithLp.toLp 2 (fun i ↦ (z i).re))) (WithLp.toLp 2 (fun i ↦ (z i).im))

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereVerticalCotangent
public import AtiyahSinger.Geometry.FrameSphereFiberNegation
public import AtiyahSinger.Geometry.FrameSpherePoleNormalization
public import AtiyahSinger.Geometry.ReflectionHorizontalLift

/-!
# A horizontal lift adapted to the original frame-sphere south section

Public module ID: M1241.

The original fiber-negation involution acts as minus the identity on the
vertical tangent at the south pole. This is checked by the actual sphere
inclusion differential and the original frame fiber derivative equivalence.
Averaging the supplied lift with its reflection therefore gives a smooth
horizontal lift equal to the actual south-section differential.

No compatibility is assumed for the initially supplied lift. The construction
uses the original associated projection, quotient and smooth frame atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxHeartbeats 800000 in
-- The original sphere derivative is detected by its injective ambient inclusion differential.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sphere_neg_one_deriv (r : ℕ)
    (v : TangentSpace (𝓡 r) (orthogonalSpherePole r false)) :
    mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r (-1))
      (orthogonalSpherePole r false) v = -v := by
  let W := OrthogonalSphereAmbient r
  let y := orthogonalSpherePole r false
  let D := orthogonalSphereDiffeomorph r (-1)
  let A := orthogonalSphereBlockIsometry r (-1)
  let inc : OrthogonalSphere r → W := Subtype.val
  let L : EuclideanSpace ℝ (Fin r) →L[ℝ] W := mfderiv (𝓡 r) 𝓘(ℝ, W) inc y
  have hcoord (u : EuclideanSpace ℝ (Fin r)) :
      orthogonalEuclideanIsometry r (-1) u = -u := by
    ext i
    change (∑ k, (-1 : Matrix (Fin r) (Fin r) ℝ) i k * u k) = -u i
    simp [Matrix.one_apply]
  have hfix : D y = y := by
    apply Subtype.ext
    change WithLp.toLp 2 (orthogonalEuclideanIsometry r (-1) y.val.fst, y.val.snd) = y.val
    rw [hcoord]
    apply WithLp.ofLp_injective 2
    simp [y, orthogonalSpherePole, orthogonalSphereNorth]
  have hlast : (L v).snd = 0 := by
    have hmem : L v ∈ (ℝ ∙ y.val)ᗮ := by
      have hrange : L.range = (ℝ ∙ y.val)ᗮ := range_mvfderiv_subtypeVal y
      rw [← hrange]
      exact ⟨v, rfl⟩
    have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
    change inner ℝ (-WithLp.toLp 2 (0, (1 : ℝ)) : W) (L v) = 0 at hi
    rw [inner_neg_left, neg_eq_zero] at hi
    change inner ℝ (0 : EuclideanSpace ℝ (Fin r)) (L v).fst +
      inner ℝ (1 : ℝ) (L v).snd = 0 at hi
    simpa [RCLike.inner_apply] using hi
  have hinc : MDifferentiable (𝓡 r) 𝓘(ℝ, W) inc :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
  have hA : MDifferentiable 𝓘(ℝ, W) 𝓘(ℝ, W) A :=
    (A.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hfun : inc ∘ D = A ∘ inc := rfl
  have hleft := mfderiv_comp y (hinc (D y)) (D.mdifferentiable (by simp) y)
  have hright := mfderiv_comp y (hA (inc y)) (hinc y)
  rw [hfun] at hleft
  have hder := hleft.symm.trans hright
  rw [hfix] at hder
  have hlinear : mfderiv 𝓘(ℝ, W) 𝓘(ℝ, W) A y.val =
      A.toContinuousLinearEquiv.toContinuousLinearMap :=
    A.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hlinear] at hder
  have hi : Function.Injective L := injective_mvfderiv_subtypeVal_sphere y
  apply hi
  calc
    L (mfderiv (𝓡 r) (𝓡 r) D y v) = A (L v) := DFunLike.congr_fun hder v
    _ = -(L v) := by
      apply WithLp.ofLp_injective 2
      change (orthogonalEuclideanIsometry r (-1) (L v).fst, (L v).snd) =
        (-(L v).fst, -(L v).snd)
      rw [hcoord, hlast, neg_zero]
    _ = L (-v) := (map_neg L v).symm

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1800000 in
-- The reflection, actual fiber derivative and pullback lift share the original associated atlas.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A supplied frame-sphere lift admits a smooth replacement agreeing with the
south-section derivative. -/
theorem exists_frameSphere_adaptedHorizontalLift
    (H : letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
      let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let a := frameSphereStereographic (EB := EB) r V
    ∃ K : SmoothHorizontalLift (smoothAssociatedSphereProjection S),
      ∀ y : B, K.lift (a.symm ⟨y, 0⟩) =
        mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB × R) (fun x : B ↦ a.symm ⟨x, 0⟩) y := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let Q := 𝓘(ℝ, EB × R)
  let q := smoothAssociatedSphereProjection S
  let a := frameSphereStereographic (EB := EB) r V
  let c := frameSphereHomeomorph (EB := EB) r V
  have ha := frameSphereStereographic_spec (EB := EB) r V
  have hc := (frameSphereHomeomorph_spec (EB := EB) r V).1
  obtain ⟨d, hdcoords, hd, _, hfixed⟩ := exists_frameSphereFiberNegation (EB := EB) r V
  let j : ContMDiffMap I Q B Z ∞ :=
    ⟨fun y ↦ a.symm ⟨y, 0⟩, ha.2.2.2.2.2.comp (contMDiff_zeroSection ℝ V)⟩
  have hbase (z : Z) : q z = (c z).val.1.proj := by
    induction z using Quotient.inductionOn with
    | h u =>
      change q (associatedBundleMk G P (OrthogonalSphere r) u.1 u.2) =
        (c (associatedBundleMk G P (OrthogonalSphere r) u.1 u.2)).val.1.proj
      rw [hc]
      rfl
  have hqd (z : Z) : q (d z) = q z := by rw [hbase, hbase, hdcoords]
  have hqj (y : B) : q (j y) = y := by
    rw [hbase]
    change (c (a.symm ⟨y, 0⟩)).val.1.proj = y
    rw [ha.2.2.2.1]
  let south := orthogonalSpherePole r false
  let D := orthogonalSphereDiffeomorph r (-1)
  have hcoord (u : R) : orthogonalEuclideanIsometry r (-1) u = -u := by
    ext i
    change (∑ k, (-1 : Matrix (Fin r) (Fin r) ℝ) i k * u k) = -u i
    simp [Matrix.one_apply]
  have hDfix : D south = south := by
    apply Subtype.ext
    change WithLp.toLp 2 (orthogonalEuclideanIsometry r (-1) south.val.fst,
      south.val.snd) = south.val
    rw [hcoord]
    apply WithLp.ofLp_injective 2
    simp [south, orthogonalSpherePole, orthogonalSphereNorth]
  -- On each specified frame the global reflection is the original central orthogonal action.
  have hframe (p : P) (y : OrthogonalSphere r) :
      d (associatedBundleMk G P (OrthogonalSphere r) p y) =
        associatedBundleMk G P (OrthogonalSphere r) p (D y) := by
    apply c.injective
    apply Subtype.ext
    rw [hdcoords, hc, hc]
    change ((⟨p.1, -p.2 y.val.fst⟩ : TotalSpace R V), y.val.snd) =
      ((⟨p.1, p.2 (orthogonalEuclideanIsometry r (-1) y.val.fst)⟩ : TotalSpace R V), y.val.snd)
    rw [hcoord, map_neg]
  have hvert (p : P) (w : TangentSpace Q (associatedBundleMk G P (OrthogonalSphere r) p south))
      (hw : mfderiv Q I q (associatedBundleMk G P (OrthogonalSphere r) p south) w = 0) :
      mfderiv Q Q d (associatedBundleMk G P (OrthogonalSphere r) p south) w = -w := by
    let i : OrthogonalSphere r → Z := associatedBundleMk G P (OrthogonalSphere r) p
    obtain ⟨e, he⟩ := exists_associatedSphereFiberTangentEquiv S p south
    obtain ⟨v, hv⟩ := e.surjective ⟨w, hw⟩
    have hival : mfderiv (𝓡 r) Q i south v = w :=
      (he v).symm.trans (congrArg Subtype.val hv)
    have hi : MDifferentiable (𝓡 r) Q i :=
      (smoothAssociatedSphereFiberInclusion S p).contMDiff.mdifferentiable (by simp)
    have hfun : (d : Z → Z) ∘ i = i ∘ D := funext (hframe p)
    have hleft := mfderiv_comp south (d.mdifferentiable (by simp) _) (hi south)
    have hright := mfderiv_comp south (hi (D south)) (D.mdifferentiable (by simp) south)
    rw [hfun] at hleft
    have hder := hleft.symm.trans hright
    rw [hDfix] at hder
    have hdv := DFunLike.congr_fun hder v
    change mfderiv Q Q d (i south) (mfderiv (𝓡 r) Q i south v) =
      mfderiv (𝓡 r) Q i south (mfderiv (𝓡 r) (𝓡 r) D south v) at hdv
    rw [hival, sphere_neg_one_deriv, map_neg, hival] at hdv
    exact hdv
  -- Every base point has an original orthogonal frame; its pole is the given south section.
  have hvertical (y : B) (w : TangentSpace Q (j y))
      (hw : mfderiv Q I q (j y) w = 0) : mfderiv Q Q d (j y) w = -w := by
    obtain ⟨p, hp⟩ := S.toIsPrincipalBundle.projection_properties.2.2 y
    have hj : j y = associatedBundleMk G P (OrthogonalSphere r) p south := by
      have h := frameSphereStereographic_symm_two_smul (EB := EB) r V p 0
      rw [map_zero, smul_zero, (orthogonalSphereNormalizedChart_properties r false).2.2.1] at h
      change a.symm ⟨p.1, 0⟩ = _ at h
      rw [show p.1 = y from hp] at h
      exact h
    have h := hvert p w
    rw [← hj] at h
    exact h hw
  exact exists_reflection_adaptedHorizontalLift q H d hd hqd j hqj hfixed hvertical

end AtiyahSinger

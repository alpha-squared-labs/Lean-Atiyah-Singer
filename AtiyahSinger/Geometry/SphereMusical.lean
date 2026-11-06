/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereTangentCoordinates
public import AtiyahSinger.Geometry.TangentMusical

/-!
# Equivariant musical transport and vertical reflection on the round sphere

Public module ID: M1435.

AL03 compares the original tangent symbols with the existing cotangent index.
The inverse of the specified round flat homeomorphism is equivariant for the
actual derivative tangent action and inverse-differential cotangent action.
This direction is needed for the contravariant pullback of a tangent K class
to the cotangent group.

The second construction lifts the already defined vertical reflection to
the actual tangent bundle. It exchanges the two normalized pole charts with
the same complex coordinate. It neither negates only the tangent fiber nor
uses the antipodal map. All native tangent and cotangent topologies remain.

Sources: SG II.3 pp.94 and II.5 p.113 for metric duality; ASI I section 8,
pp.523--524, for the two equivariant point inclusions. The concrete round
metric and vertical-reflection comparisons are project expansions of those
standard constructions. The original musical and reflection comparisons are proved here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent

/-- The inverse round musical map intertwines the original cotangent and tangent actions. -/
theorem orthogonalSphereRoundMetric_flat_symm_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ)
    (z : CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :
    (orthogonalSphereRoundMetric r).flatHomeomorph.symm (A • z) =
      A • (orthogonalSphereRoundMetric r).flatHomeomorph.symm z := by
  let g := orthogonalSphereRoundMetric r
  let D := orthogonalSphereDiffeomorph r A
  -- The same sphere diffeomorphism and its inverse have inverse native derivatives.
  have hInverse (x : OrthogonalSphere r) (w : TangentSpace (𝓡 r) (D x)) :
      mfderiv (𝓡 r) (𝓡 r) D x (mfderiv (𝓡 r) (𝓡 r) D.symm (D x) w) = w := by
    have hd := mfderiv_comp (D x) (D.mdifferentiable (by simp) (D.symm (D x)))
      (D.symm.mdifferentiable (by simp) (D x))
    have he : (D : OrthogonalSphere r → OrthogonalSphere r) ∘ D.symm = id :=
      funext D.apply_symm_apply
    rw [he, mfderiv_id] at hd
    -- Expose only the native model fiber before rewriting the inverse base point.
    change ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin r)) =
      (mfderiv (𝓡 r) (𝓡 r) D (D.symm (D x))).comp
        (mfderiv (𝓡 r) (𝓡 r) D.symm (D x)) at hd
    rw [D.symm_apply_apply] at hd
    exact congrArg (fun f : EuclideanSpace ℝ (Fin r) →L[ℝ]
      EuclideanSpace ℝ (Fin r) ↦ f w) hd.symm
  -- Metric invariance identifies the flat covectors against every target tangent vector.
  have hForward (v : TangentBundle (𝓡 r) (OrthogonalSphere r)) :
      g.flatHomeomorph (A • v) = A • g.flatHomeomorph v := by
    change (⟨D v.proj, g.inner (D v.proj) (mfderiv (𝓡 r) (𝓡 r) D v.proj v.snd)⟩ :
      CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) =
      ⟨D v.proj, (g.inner v.proj v.snd).comp (mfderiv (𝓡 r) (𝓡 r) D.symm (D v.proj))⟩
    congr 1
    ext w
    change g.inner (D v.proj) (mfderiv (𝓡 r) (𝓡 r) D v.proj v.snd) w =
      g.inner v.proj v.snd (mfderiv (𝓡 r) (𝓡 r) D.symm (D v.proj) w)
    conv_lhs => rw [← hInverse v.proj w]
    exact orthogonalSphereRoundMetric_invariant r A v.proj v.snd
      (mfderiv (𝓡 r) (𝓡 r) D.symm (D v.proj) w)
  -- Transfer forward equivariance through the exact chosen flat homeomorphism.
  apply g.flatHomeomorph.injective
  rw [g.flatHomeomorph.apply_symm_apply, hForward, g.flatHomeomorph.apply_symm_apply]


/-- The original vertical reflection and its inverse are smooth in the native sphere atlas. -/
theorem orthogonalSphereVerticalReflection_smooth (r : ℕ) :
    ContMDiff (𝓡 r) (𝓡 r) ∞ (orthogonalSphereVerticalReflection r) ∧
      ContMDiff (𝓡 r) (𝓡 r) ∞ (orthogonalSphereVerticalReflection r).symm := by
  -- Restrict the same ambient linear reflection to the native unit sphere.
  have h : ContMDiff (𝓡 r) (𝓡 r) ∞ (orthogonalSphereVerticalReflection r) := by
    apply ContMDiff.codRestrict_sphere
    exact (orthogonalSphereVerticalIsometry r).contDiff.contMDiff.comp contMDiff_coe_sphere
  have hinv : (orthogonalSphereVerticalReflection r).symm =
      orthogonalSphereVerticalReflection r := by
    apply Homeomorph.ext
    intro x
    apply Subtype.ext
    rfl
  exact ⟨h, hinv.symm ▸ h⟩

/-- Vertical reflection packaged as the same original smooth sphere diffeomorphism. -/
def orthogonalSphereVerticalDiffeomorph (r : ℕ) :
    OrthogonalSphere r ≃ₘ⟮𝓡 r, 𝓡 r⟯ OrthogonalSphere r where
  toEquiv := (orthogonalSphereVerticalReflection r).toEquiv
  contMDiff_toFun := (orthogonalSphereVerticalReflection_smooth r).1
  contMDiff_invFun := (orthogonalSphereVerticalReflection_smooth r).2

/-- The genuine derivative lift of vertical reflection is a tangent-bundle homeomorphism. -/
theorem isHomeomorph_orthogonalSphereVerticalTangentMap (r : ℕ) :
    IsHomeomorph (tangentMap (𝓡 r) (𝓡 r) (orthogonalSphereVerticalDiffeomorph r)) := by
  let D := orthogonalSphereVerticalDiffeomorph r
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  -- Differentiate the two genuine inverse identities, including their base points.
  have hleft : Function.LeftInverse (tangentMap (𝓡 r) (𝓡 r) D.symm)
      (tangentMap (𝓡 r) (𝓡 r) D) := by
    intro z
    change (tangentMap (𝓡 r) (𝓡 r) D.symm ∘ tangentMap (𝓡 r) (𝓡 r) D) z = z
    rw [← tangentMap_comp (D.symm.mdifferentiable (by simp))
      (D.mdifferentiable (by simp))]
    have hid : D.symm ∘ D = id := funext D.symm_apply_apply
    rw [hid, tangentMap_id]
    rfl
  have hright : Function.RightInverse (tangentMap (𝓡 r) (𝓡 r) D.symm)
      (tangentMap (𝓡 r) (𝓡 r) D) := by
    intro z
    change (tangentMap (𝓡 r) (𝓡 r) D ∘ tangentMap (𝓡 r) (𝓡 r) D.symm) z = z
    rw [← tangentMap_comp (D.mdifferentiable (by simp))
      (D.symm.mdifferentiable (by simp))]
    have hid : D ∘ D.symm = id := funext D.apply_symm_apply
    rw [hid, tangentMap_id]
    rfl
  -- Both lifts are continuous for the original tangent-bundle topology.
  let h : T ≃ₜ T :=
    { toFun := tangentMap (𝓡 r) (𝓡 r) D
      invFun := tangentMap (𝓡 r) (𝓡 r) D.symm
      left_inv := hleft
      right_inv := hright
      continuous_toFun := D.contMDiff.continuous_tangentMap (by simp)
      continuous_invFun := D.symm.contMDiff.continuous_tangentMap (by simp) }
  exact h.isHomeomorph

/-- The actual derivative-lift homeomorphism, whose base map swaps the two poles. -/
def orthogonalSphereVerticalTangentHomeomorph (r : ℕ) :
    TangentBundle (𝓡 r) (OrthogonalSphere r) ≃ₜ
      TangentBundle (𝓡 r) (OrthogonalSphere r) :=
  (isHomeomorph_orthogonalSphereVerticalTangentMap r).homeomorph
    (tangentMap (𝓡 r) (𝓡 r) (orthogonalSphereVerticalDiffeomorph r))

/-- Vertical reflection's derivative lift commutes with the same original O(r) action. -/
theorem orthogonalSphereVerticalTangentHomeomorph_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ)
    (z : TangentBundle (𝓡 r) (OrthogonalSphere r)) :
    orthogonalSphereVerticalTangentHomeomorph r (A • z) =
      A • orthogonalSphereVerticalTangentHomeomorph r z := by
  let R := orthogonalSphereVerticalDiffeomorph r
  let D := orthogonalSphereDiffeomorph r A
  -- The unchanged horizontal action commutes with reversal of the height coordinate.
  have hcomm : R ∘ D = D ∘ R := by
    funext x
    apply Subtype.ext
    rfl
  -- Lift that exact equality through the chain rule for the native tangent maps.
  change (tangentMap (𝓡 r) (𝓡 r) R ∘ tangentMap (𝓡 r) (𝓡 r) D) z =
    (tangentMap (𝓡 r) (𝓡 r) D ∘ tangentMap (𝓡 r) (𝓡 r) R) z
  rw [← tangentMap_comp (R.mdifferentiable (by simp)) (D.mdifferentiable (by simp)),
    hcomm, tangentMap_comp (D.mdifferentiable (by simp)) (R.mdifferentiable (by simp))]

/-- Vertical reflection exchanges the two actual pole charts without changing complex input. -/
theorem orthogonalSphereVerticalTangentHomeomorph_chart (r : ℕ)
    (atInfinity : Bool) (z : EuclideanSpace ℂ (Fin r)) :
    orthogonalSphereVerticalTangentHomeomorph r
        (orthogonalSphereTangentChart r atInfinity z) =
      orthogonalSphereTangentChart r (!atInfinity) z := by
  let R := orthogonalSphereVerticalDiffeomorph r
  let h := orthogonalSphereVerticalReflection r
  have hinv : h.symm = h := by
    apply Homeomorph.ext
    intro x
    apply Subtype.ext
    rfl
  -- The original opposite inverse charts differ by precisely this reflection.
  have hchart : R ∘ (orthogonalSphereNormalizedChart r atInfinity).symm =
      (orthogonalSphereNormalizedChart r (!atInfinity)).symm := by
    funext u
    cases atInfinity
    · change h _ = h.symm _
      rw [hinv]
      rfl
    · change h (h.symm _) = _
      exact h.apply_symm_apply _
  -- The tangent chart uses the same real coordinate and the same imaginary vector.
  let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).re)
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).im)
  change (tangentMap (𝓡 r) (𝓡 r) R ∘
      tangentMap (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm)
        (⟨u, v⟩ : TangentBundle (𝓡 r) (EuclideanSpace ℝ (Fin r))) =
    tangentMap (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r (!atInfinity)).symm ⟨u, v⟩
  rw [← tangentMap_comp (R.mdifferentiable (by simp))
    ((orthogonalSphereNormalizedChart_smooth r atInfinity).2.mdifferentiable (by simp)),
    hchart]

end AtiyahSinger

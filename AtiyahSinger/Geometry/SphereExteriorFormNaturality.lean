/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexifiedTangentParityForms
public import AtiyahSinger.Geometry.SphereComplexifiedTangent
public import AtiyahSinger.Topology.ExteriorHodgePhaseBundle

/-!
# Orthogonal naturality of the original sphere exterior form coordinates

Public module ID: M1431.

The round metric musical map intertwines the actual complexified derivative
with inverse derivative pullback on differential forms. Its determinant exterior
extension preserves this identity in every degree. Finite parity coordinates and
the original degree phase therefore retain the same orthogonal action.

Source: SG II.5 and III.9, naturality of the metric exterior description of forms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped BigOperators DirectSum Manifold ContDiff TensorProduct

attribute [local instance] continuousSMul_orthogonalSphere sphereComplexifiedTangentTopology
  isFiniteRank_sphereComplexifiedTangent
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity

set_option maxHeartbeats 1200000 in
-- Compare the specified musical covectors, then extend their determinant identity.
set_option backward.isDefEq.respectTransparency false in
/-- The same metric exterior map intertwines the original sphere derivative with form pullback. -/
theorem complexifiedTangentExteriorEquiv_sphere_naturality (r p : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
    (a : ⋀[ℂ]^p (SphereComplexifiedTangent r x)) :
    complexifiedTangentExteriorEquiv (orthogonalSphereRoundMetric r) p (A • x)
        (exteriorPower.map p (sphereComplexifiedTangentAction r A x) a) =
      (complexifiedTangentExteriorEquiv
        (orthogonalSphereRoundMetric r) p x a).compContinuousLinearMap
          (mfderiv (𝓡 r) (𝓡 r) (fun y : OrthogonalSphere r ↦ A⁻¹ • y) (A • x)) := by
  let V := EuclideanSpace ℝ (Fin r)
  let C := ℂ ⊗[ℝ] V
  let g := orthogonalSphereRoundMetric r
  let D := orthogonalSphereDiffeomorph r A
  let B := orthogonalSphereDiffeomorph r A⁻¹
  let L : V →L[ℝ] V := mfderiv (𝓡 r) (𝓡 r) D x
  let K : V →L[ℝ] V := mfderiv (𝓡 r) (𝓡 r) B (A • x)
  let F : C →ₗ[ℂ] C := sphereComplexifiedTangentAction r A x
  have hpoint : B (A • x) = x := inv_smul_smul A x
  have hcomp : D ∘ B = id := funext (fun y ↦ smul_inv_smul A y)
  have hLK (w : V) : L (K w) = w := by
    have h := mfderiv_comp_apply (I := 𝓡 r) (I' := 𝓡 r) (I'' := 𝓡 r) (A • x)
      (D.mdifferentiable (by simp) (B (A • x))) (B.mdifferentiable (by simp) (A • x)) w
    rw [hcomp, mfderiv_id] at h
    let derivative : OrthogonalSphere r → (V →L[ℝ] V) :=
      fun y ↦ mfderiv (𝓡 r) (𝓡 r) D y
    have hD := congrArg derivative hpoint
    have h' : derivative (B (A • x)) (K w) = w := h.symm
    rw [hD] at h'
    exact h'
  have hmetric (v w : V) : g.inner (A • x) (L v) w = g.inner x v (K w) := by
    have h := orthogonalSphereRoundMetric_invariant r A x v (K w)
    change g.inner (A • x) (L v) (L (K w)) = g.inner x v (K w) at h
    rw [hLK] at h
    exact h
  let musical (y : OrthogonalSphere r) : C →ₗ[ℂ] (V →ₗ[ℝ] ℂ) :=
    complexifiedTangentCovectorMap g y
  have hmusical (y : OrthogonalSphere r) (c : ℂ) (v w : V) :
      musical y (c ⊗ₜ[ℝ] v) w = c * (g.inner y v w : ℂ) :=
    complexifiedTangentCovectorMap_tmul g y c v w
  have hF (c : ℂ) (v : V) : F (c ⊗ₜ[ℝ] v) = c ⊗ₜ[ℝ] L v := rfl
  -- Complex linearity extends the actual real metric invariance to every tensor vector.
  have hcov (z : C) (w : V) : musical (A • x) (F z) w = musical x z (K w) := by
    induction z using TensorProduct.inductionOn with
    | tmul c v => rw [hF, hmusical, hmusical, hmetric]
    | add z t hz ht =>
        simp only [map_add, LinearMap.add_apply, hz, ht]
  let T (y : OrthogonalSphere r) : (⋀[ℂ]^p C) ≃ₗ[ℂ] (V [⋀^Fin p]→L[ℝ] ℂ) :=
    complexifiedTangentExteriorEquiv g p y
  have hT (y : OrthogonalSphere r) (z : Fin p → C) (w : Fin p → V) :
      T y (exteriorPower.ιMulti ℂ p z) w =
        Matrix.det (Matrix.of (fun i j ↦ musical y (z i) (w j))) :=
    complexifiedTangentExteriorEquiv_ιMulti g p y z w
  let R : (V [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ] (V [⋀^Fin p]→L[ℝ] ℂ) :=
    { toFun α := α.compContinuousLinearMap K
      map_add' α β := by ext w; rfl
      map_smul' c α := by ext w; rfl }
  have hmaps : (T (A • x)).toLinearMap.comp (exteriorPower.map p F) =
      R.comp (T x).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro z
    change T (A • x) (exteriorPower.map p F (exteriorPower.ιMulti ℂ p z)) =
      R (T x (exteriorPower.ιMulti ℂ p z))
    rw [exteriorPower.map_apply_ιMulti]
    apply ContinuousAlternatingMap.ext
    intro w
    change T (A • x) (exteriorPower.ιMulti ℂ p (F ∘ z)) w =
      T x (exteriorPower.ιMulti ℂ p z) (K ∘ w)
    rw [hT, hT]
    congr 1
    ext i j
    exact hcov (z i) (w j)
  exact LinearMap.congr_fun hmaps a

set_option maxHeartbeats 1200000 in
-- Sum the same degreewise exterior maps through the original finite parity coordinates.
set_option backward.isDefEq.respectTransparency false in
/-- The original even exterior action is inverse derivative pullback on every form degree. -/
theorem complexifiedTangentEvenFormEquiv_sphere_naturality (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
    (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) 0) :
    complexifiedTangentEvenFormEquiv (orthogonalSphereRoundMetric r) (A • x)
        ((sphereExteriorParityEquivariantStructure r 0).linearMap A x a) =
      fun p ↦
        (complexifiedTangentEvenFormEquiv
          (orthogonalSphereRoundMetric r) x a p).compContinuousLinearMap
          (mfderiv (𝓡 r) (𝓡 r) (fun y : OrthogonalSphere r ↦ A⁻¹ • y) (A • x)) := by
  classical
  let g := orthogonalSphereRoundMetric r
  let K := mfderiv (𝓡 r) (𝓡 r) (fun y : OrthogonalSphere r ↦ A⁻¹ • y) (A • x)
  let u := complexifiedTangentEvenFormEquiv g x a
  have ha := complexifiedTangentEvenFormEquiv_symm_coe g x u
  rw [show (complexifiedTangentEvenFormEquiv g x).symm u = a from
    (complexifiedTangentEvenFormEquiv g x).symm_apply_apply a] at ha
  apply (complexifiedTangentEvenFormEquiv g (A • x)).symm.injective
  apply Subtype.ext
  rw [LinearEquiv.symm_apply_apply, sphereExteriorParityEquivariantStructure_apply,
    complexifiedTangentEvenFormEquiv_symm_coe, ha, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← exteriorPower.coe_map]
  apply congrArg Subtype.val
  apply (complexifiedTangentExteriorEquiv g p.val.val (A • x)).injective
  rw [complexifiedTangentExteriorEquiv_sphere_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 1200000 in
-- Sum the same degreewise exterior maps through the original finite parity coordinates.
set_option backward.isDefEq.respectTransparency false in
/-- The original odd exterior action is inverse derivative pullback on every form degree. -/
theorem complexifiedTangentOddFormEquiv_sphere_naturality (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
    (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) 1) :
    complexifiedTangentOddFormEquiv (orthogonalSphereRoundMetric r) (A • x)
        ((sphereExteriorParityEquivariantStructure r 1).linearMap A x a) =
      fun p ↦
        (complexifiedTangentOddFormEquiv
          (orthogonalSphereRoundMetric r) x a p).compContinuousLinearMap
          (mfderiv (𝓡 r) (𝓡 r) (fun y : OrthogonalSphere r ↦ A⁻¹ • y) (A • x)) := by
  classical
  let g := orthogonalSphereRoundMetric r
  let K := mfderiv (𝓡 r) (𝓡 r) (fun y : OrthogonalSphere r ↦ A⁻¹ • y) (A • x)
  let u := complexifiedTangentOddFormEquiv g x a
  have ha := complexifiedTangentOddFormEquiv_symm_coe g x u
  rw [show (complexifiedTangentOddFormEquiv g x).symm u = a from
    (complexifiedTangentOddFormEquiv g x).symm_apply_apply a] at ha
  apply (complexifiedTangentOddFormEquiv g (A • x)).symm.injective
  apply Subtype.ext
  rw [LinearEquiv.symm_apply_apply, sphereExteriorParityEquivariantStructure_apply,
    complexifiedTangentOddFormEquiv_symm_coe, ha, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← exteriorPower.coe_map]
  apply congrArg Subtype.val
  apply (complexifiedTangentExteriorEquiv g p.val.val (A • x)).injective
  rw [complexifiedTangentExteriorEquiv_sphere_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 1200000 in
-- Work directly with the original exterior maps on the two specified sphere fibers.
set_option backward.isDefEq.respectTransparency false in
/-- The original degree phase commutes with the exterior maps of the sphere-action derivative. -/
theorem exteriorHodgePhaseBundleIso_sphere_isEquivariant (r : ℕ) (i : ZMod 2) :
    (exteriorHodgePhaseBundleIso (SphereComplexifiedTangent r)
      (sphereComplexifiedRoundMetric r) i).IsEquivariant
        (sphereExteriorParityEquivariantStructure r i)
        (sphereExteriorParityEquivariantStructure r i) := by
  intro A x a
  apply Subtype.ext
  change ((exteriorHodgePhaseBundleIso (SphereComplexifiedTangent r)
      (sphereComplexifiedRoundMetric r) i).linearEquiv (A • x)
        ((sphereExteriorParityEquivariantStructure r i).linearMap A x a)).val =
    ((sphereExteriorParityEquivariantStructure r i).linearMap A x
      ((exteriorHodgePhaseBundleIso (SphereComplexifiedTangent r)
        (sphereComplexifiedRoundMetric r) i).linearEquiv x a)).val
  rw [exteriorHodgePhaseBundleIso_apply, sphereExteriorParityEquivariantStructure_apply,
    sphereExteriorParityEquivariantStructure_apply, exteriorHodgePhaseBundleIso_apply]
  let F := sphereComplexifiedTangentAction r A x
  -- Scalar multiplication is central for this actual complex-linear derivative map.
  have h : (ExteriorAlgebra.map F).comp
      (ExteriorAlgebra.map
        (Complex.I • (LinearMap.id : SphereComplexifiedTangent r x →ₗ[ℂ] _))) =
      (ExteriorAlgebra.map
        (Complex.I • (LinearMap.id : SphereComplexifiedTangent r (A • x) →ₗ[ℂ] _))).comp
          (ExteriorAlgebra.map F) := by
    rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map]
    congr 1
    apply LinearMap.ext
    intro v
    exact F.map_smul Complex.I v
  exact (AlgHom.congr_fun h a.val).symm

end AtiyahSinger

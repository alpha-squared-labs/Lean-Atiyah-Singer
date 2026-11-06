/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.Complexification
public import AtiyahSinger.Geometry.TangentMusical
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Complexification of the original metric musical map

Public module ID: M1135.

The supplied real tangent metric extends complex linearly from the actual scalar
extension of the tangent fiber to complex-valued real covectors. Positivity and
the two real coordinates prove injectivity; the two matching finite bases prove
surjectivity. No new tangent metric or complexification carrier is chosen.

Source: the metric identification of tangent and cotangent exterior powers in
Lawson--Michelsohn, Spin Geometry, II.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module
open scoped BigOperators Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Complex linear extension of the original real metric musical map. -/
def complexifiedTangentCovectorMap (g : SmoothTangentMetric (n := n) (M := M)) (x : M) :
    (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℂ]
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →ₗ[ℝ] ℂ) :=
  LinearMap.liftBaseChange ℂ
    { toFun v :=
        { toFun w := (g.inner x v w : ℂ)
          map_add' w z := by simp
          map_smul' r w := by simp [Complex.real_smul] }
      map_add' v w := by ext z; simp
      map_smul' r v := by ext z; simp [Complex.real_smul] }

/-- A pure tangent tensor becomes the scalar multiple of its specified metric covector. -/
theorem complexifiedTangentCovectorMap_tmul
    (g : SmoothTangentMetric (n := n) (M := M)) (x : M) (z : ℂ)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    complexifiedTangentCovectorMap g x (z ⊗ₜ[ℝ] v) w = z * (g.inner x v w : ℂ) := rfl

set_option maxHeartbeats 800000 in
-- Keep the metric positivity argument separate from the finite-dimensional rank comparison.
set_option backward.isDefEq.respectTransparency false in
/-- The same complexified musical map is an isomorphism on every original tangent fiber. -/
theorem complexifiedTangentCovectorMap_bijective
    (g : SmoothTangentMetric (n := n) (M := M)) (x : M) :
    Function.Bijective (complexifiedTangentCovectorMap g x) := by
  classical
  let V := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x
  let b : Basis (Fin n) ℝ V := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let c : Basis (Fin n) ℂ (V →ₗ[ℝ] ℂ) := (Pi.basisFun ℂ (Fin n)).map (b.constr ℂ)
  let : FiniteDimensional ℂ (ℂ ⊗[ℝ] V) := Module.Finite.of_basis (b.baseChange ℂ)
  let : FiniteDimensional ℂ (V →ₗ[ℝ] ℂ) := Module.Finite.of_basis c
  let L := complexifiedTangentCovectorMap g x
  have hzero (a : ℂ ⊗[ℝ] V) (ha : L a = 0) : a = 0 := by
    let u := (complexificationReIm V a).1
    let v := (complexificationReIm V a).2
    have hexpand : a = (1 : ℂ) ⊗ₜ[ℝ] u + Complex.I ⊗ₜ[ℝ] v := by
      exact ((complexificationReIm V).symm_apply_apply a).symm.trans
        ((complexificationReIm_properties V).2.1 u v)
    have hvalue (w : V) : (g.inner x u w : ℂ) + Complex.I * (g.inner x v w : ℂ) = 0 := by
      have h := LinearMap.congr_fun ha w
      rw [hexpand, map_add] at h
      change (1 : ℂ) * (g.inner x u w : ℂ) + Complex.I * (g.inner x v w : ℂ) = 0 at h
      simpa only [one_mul] using h
    have hu : u = 0 := by
      have h := congrArg Complex.re (hvalue u)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
        add_zero, Complex.zero_re] at h
      by_contra hu
      exact (ne_of_gt (g.pos x u hu)) h
    have hv : v = 0 := by
      have h := congrArg Complex.im (hvalue v)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
        Complex.zero_im] at h
      by_contra hv
      exact (ne_of_gt (g.pos x v hv)) h
    rw [hexpand, hu, hv, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero]
  have hinj : Function.Injective L := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hab, sub_self]
  have hdim : Module.finrank ℂ (ℂ ⊗[ℝ] V) = Module.finrank ℂ (V →ₗ[ℝ] ℂ) := by
    rw [Module.finrank_eq_card_basis (b.baseChange ℂ), Module.finrank_eq_card_basis c]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- The canonical metric identification from complexified tangent vectors to complex covectors. -/
def complexifiedTangentCovectorEquiv (g : SmoothTangentMetric (n := n) (M := M)) (x : M) :
    (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) ≃ₗ[ℂ]
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →ₗ[ℝ] ℂ) :=
  LinearEquiv.ofBijective (complexifiedTangentCovectorMap g x)
    (complexifiedTangentCovectorMap_bijective g x)

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# The canonical Hermitian metric on a real complexification

Public module ID: M1729.

The original real inner product extends to the native scalar extension.
Its explicit real/imaginary formula fixes the conjugate-linear first slot,
and continuity is tested on the original real bundle total topology.
Neither a new complex bundle topology nor a choice of complex frame is used.

This standard extension supplies the metric for comparing the doubled real
Clifford symbol with the exterior symbol of that very complexified bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct ComplexConjugate

/-- The canonical positive Hermitian form on the actual scalar extension of a real inner space. -/
@[instance_reducible]
def complexificationHermitianCore (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    InnerProductSpace.Core ℂ (ℂ ⊗[ℝ] V) := by
  let r := complexificationReIm V
  have hsmul (c : ℂ) (v : ℂ ⊗[ℝ] V) :
      r (c • v) = (c.re • (r v).1 - c.im • (r v).2,
        c.im • (r v).1 + c.re • (r v).2) := by
    induction v using TensorProduct.inductionOn with
    | tmul z v =>
      rw [TensorProduct.smul_tmul', (complexificationReIm_properties V).1,
        (complexificationReIm_properties V).1]
      simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, sub_smul, add_smul, mul_smul]
      rw [add_comm (c.re • z.im • v)]
    | add u v hu hv =>
      rw [smul_add, map_add, hu, hv, map_add]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, smul_add] <;> abel
  refine
    { inner := fun u v ↦
        ((inner ℝ (r u).1 (r v).1 + inner ℝ (r u).2 (r v).2 : ℝ) : ℂ) +
          ((inner ℝ (r u).1 (r v).2 - inner ℝ (r u).2 (r v).1 : ℝ) : ℂ) * Complex.I
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_
      definite := ?_ }
  · -- Hermitian symmetry retains the original real symmetric pairing in all four slots.
    intro u v
    simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
      real_inner_comm, Complex.ofReal_add, Complex.ofReal_sub]
    ring
  · intro v
    change 0 ≤ (((inner ℝ (r v).1 (r v).1 + inner ℝ (r v).2 (r v).2 : ℝ) : ℂ) +
      ((inner ℝ (r v).1 (r v).2 - inner ℝ (r v).2 (r v).1 : ℝ) : ℂ) * Complex.I).re
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  · intro u v w
    simp only [map_add, Prod.fst_add, Prod.snd_add, inner_add_left,
      Complex.ofReal_add, Complex.ofReal_sub]
    ring
  · -- Multiplication by i rotates the two real coordinates with the specified sign.
    intro u v c
    rw [hsmul]
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
    have hc : conj c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hc]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · -- A zero diagonal forces both original real components to vanish.
    intro v hv
    have h := congrArg Complex.re hv
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.zero_re] at h
    have h₁ : 0 ≤ inner ℝ (r v).1 (r v).1 := real_inner_self_nonneg
    have h₂ : 0 ≤ inner ℝ (r v).2 (r v).2 := real_inner_self_nonneg
    have hr : (r v).1 = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by linarith)
    have hi : (r v).2 = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by linarith)
    apply r.injective
    rw [map_zero]
    exact Prod.ext hr hi

/-- On the original pure tensors, scalar extension has the standard sesquilinear pairing. -/
theorem complexificationHermitianCore_tmul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (z w : ℂ) (u v : V) :
    (complexificationHermitianCore V).inner (z ⊗ₜ[ℝ] u) (w ⊗ₜ[ℝ] v) =
      conj z * w * (inner ℝ u v : ℂ) := by
  change ((inner ℝ (complexificationReIm V (z ⊗ₜ[ℝ] u)).1
          (complexificationReIm V (w ⊗ₜ[ℝ] v)).1 +
        inner ℝ (complexificationReIm V (z ⊗ₜ[ℝ] u)).2
          (complexificationReIm V (w ⊗ₜ[ℝ] v)).2 : ℝ) : ℂ) +
      ((inner ℝ (complexificationReIm V (z ⊗ₜ[ℝ] u)).1
          (complexificationReIm V (w ⊗ₜ[ℝ] v)).2 -
        inner ℝ (complexificationReIm V (z ⊗ₜ[ℝ] u)).2
          (complexificationReIm V (w ⊗ₜ[ℝ] v)).1 : ℝ) : ℂ) * Complex.I = _
  rw [(complexificationReIm_properties V).1, (complexificationReIm_properties V).1]
  simp only [real_inner_smul_left, real_inner_smul_right]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.add_im, Complex.mul_im] <;> ring

/-- Extending a specified real isometry preserves these same canonical Hermitian forms. -/
theorem complexificationHermitianCore_baseChange
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : V ≃ₗᵢ[ℝ] W)
    (u v : ℂ ⊗[ℝ] V) :
    (complexificationHermitianCore W).inner
        ((e.toLinearEquiv.baseChange ℝ ℂ) u) ((e.toLinearEquiv.baseChange ℝ ℂ) v) =
      (complexificationHermitianCore V).inner u v := by
  have hcoords (z : ℂ ⊗[ℝ] V) :
      complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) z) =
        (e (complexificationReIm V z).1, e (complexificationReIm V z).2) := by
    induction z using TensorProduct.inductionOn with
    | tmul z w =>
      rw [LinearEquiv.baseChange_tmul, (complexificationReIm_properties W).1,
        (complexificationReIm_properties V).1, map_smul, map_smul]
      rfl
    | add z w hz hw =>
      simp only [map_add, hz, hw, Prod.fst_add, Prod.snd_add]
      rfl
  change ((inner ℝ (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) u)).1
          (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) v)).1 +
        inner ℝ (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) u)).2
          (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) v)).2 : ℝ) : ℂ) +
      ((inner ℝ (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) u)).1
          (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) v)).2 -
        inner ℝ (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) u)).2
          (complexificationReIm W ((e.toLinearEquiv.baseChange ℝ ℂ) v)).1 : ℝ) : ℂ) * Complex.I = _
  simp only [hcoords, e.inner_map_map]
  rfl

namespace ComplexBundle

attribute [local instance] sumTopology

variable {B R : Type*} {E : B → Type*}
  [TopologicalSpace B] [NormedAddCommGroup R] [NormedSpace ℝ R]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace R E)] [FiberBundle R E] [VectorBundle ℝ R E]
  [IsContinuousRiemannianBundle R E]

/-- Extend the original continuous real metric, keeping the native scalar-extension topology. -/
def complexificationHermitianMetric [FiniteDimensional ℝ R] :
    letI := complexificationTopology R E
    ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x) := by
  let F (x : B) := ℂ ⊗[ℝ] E x
  let := complexificationTopology R E
  refine ⟨fun x ↦ complexificationHermitianCore (E x), ?_,
    isFiniteRank_complexification R E⟩
  let D := TotalSpace Unit (F ×ᵇ F)
  have h₁ : Continuous (fun z : D ↦ (⟨z.proj, z.snd.1⟩ : TotalSpace Unit F)) :=
    continuous_sum_fst
  have h₂ : Continuous (fun z : D ↦ (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F)) :=
    continuous_sum_snd
  have hcoords : Continuous (fun z : TotalSpace (R × R) (E ×ᵇ E) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace R E), (⟨z.proj, z.snd.2⟩ : TotalSpace R E))) :=
    continuous_induced_dom
  have hleft := hcoords.comp ((complexificationDoubleTotalHomeomorph R E).continuous.comp h₁)
  have hright := hcoords.comp ((complexificationDoubleTotalHomeomorph R E).continuous.comp h₂)
  -- All four inner products are evaluated in precisely the same original real fiber.
  change Continuous (fun z : D ↦
    ((inner ℝ (complexificationReIm (E z.proj) z.snd.1).1
          (complexificationReIm (E z.proj) z.snd.2).1 +
        inner ℝ (complexificationReIm (E z.proj) z.snd.1).2
          (complexificationReIm (E z.proj) z.snd.2).2 : ℝ) : ℂ) +
      ((inner ℝ (complexificationReIm (E z.proj) z.snd.1).1
          (complexificationReIm (E z.proj) z.snd.2).2 -
        inner ℝ (complexificationReIm (E z.proj) z.snd.1).2
          (complexificationReIm (E z.proj) z.snd.2).1 : ℝ) : ℂ) * Complex.I)
  exact (Complex.continuous_ofReal.comp
    ((hleft.fst.inner_bundle hright.fst).add (hleft.snd.inner_bundle hright.snd))).add
      ((Complex.continuous_ofReal.comp
        ((hleft.fst.inner_bundle hright.snd).sub (hleft.snd.inner_bundle hright.fst))).mul
          (continuous_const : Continuous (fun _ : D ↦ Complex.I)))

end ComplexBundle

end AtiyahSinger

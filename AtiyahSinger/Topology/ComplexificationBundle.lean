/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.Complexification
public import AtiyahSinger.Topology.SerreSwan
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Complexification of a finite-dimensional real vector bundle

Public module ID: M1724.

K05. The fibers are the genuine scalar extensions `ℂ ⊗[ℝ] E x`. Their total topology
is transported from mathlib's native real double bundle, using the same ordered
real/imaginary equivalence in every fiber. Native real-linear local trivializations
then provide finite-rank complex local trivializations.

Source: Husemoller, *Fibre Bundles*, Chapter 17, §11, printed p. 259. The explicit
total-space transport is a project adapter to the existing `ComplexBundle.IsFiniteRank`
interface. This construction does not identify the normal bundle of a tangent embedding
with a double normal bundle; that geometric identification requires additional data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

variable {X : Type*} (V : Type*)
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]

/-- The fiberwise real/imaginary equivalence preserves the actual base point. -/
def complexificationDoubleTotalEquiv :
    TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] E x) ≃ TotalSpace (V × V) (E ×ᵇ E) where
  toFun := fun z ↦ ⟨z.proj, complexificationReIm (E z.proj) z.snd⟩
  invFun := fun z ↦ ⟨z.proj, (complexificationReIm (E z.proj)).symm z.snd⟩
  left_inv := fun z ↦ by
    cases z
    simp
  right_inv := fun z ↦ by
    cases z
    simp

variable [TopologicalSpace (TotalSpace V E)]

/-- The complexification topology induced from the native real double bundle. -/
@[reducible]
def complexificationTopology :
    TopologicalSpace (TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] E x)) :=
  TopologicalSpace.induced (complexificationDoubleTotalEquiv V E) inferInstance

/-- The explicit real/imaginary map is a homeomorphism for the transported topology. -/
def complexificationDoubleTotalHomeomorph :
    letI := complexificationTopology V E
    TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] E x) ≃ₜ TotalSpace (V × V) (E ×ᵇ E) :=
  letI := complexificationTopology V E
  (complexificationDoubleTotalEquiv V E).toHomeomorphOfIsInducing ⟨rfl⟩

variable [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hD : FiniteDimensional ℝ V] [∀ x, TopologicalSpace (E x)]
  [hB : FiberBundle V E] [hV : VectorBundle ℝ V E]

include hD hB hV

/-- Scalar extension of a finite-dimensional real vector bundle has finite complex rank. -/
theorem isFiniteRank_complexification :
    letI := complexificationTopology V E
    IsFiniteRank (fun x ↦ ℂ ⊗[ℝ] E x) := by
  /- First choose a native real-linear bundle chart near the given base point and a
  real coordinate basis of its fixed finite-dimensional model V. The product of this
  chart with itself gives coordinates (u,v) on the native double bundle.
  Extend the real fiber coordinate equivalences to complex scalars. Their value on
  (u,v) is coord(u) + I * coord(v), componentwise. This gives a complex-linear chart
  with model Fin(finrank ℝ V) → ℂ and its explicit inverse.
  Transport these charts through the real/imaginary total homeomorphism. Continuity
  in both directions follows from the native double charts and finite-dimensional
  real/imaginary coordinates. The original open chart domains cover the base.
  No compactness, Hausdorffness, paracompactness, or choice of bundle metric is needed. -/
  let := complexificationTopology V E
  constructor
  intro x
  -- Use one original real chart and one fixed real coordinate basis of its model.
  let e := trivializationAt V E x
  let n := Module.finrank ℝ V
  let c : V ≃L[ℝ] (Fin n → ℝ) :=
    (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  let q : (V × V) ≃ₜ (Fin n → ℂ) :=
    { toFun := fun uv j ↦ (c uv.1 j : ℂ) + (c uv.2 j : ℂ) * Complex.I
      invFun := fun z ↦ (c.symm (fun j ↦ (z j).re), c.symm (fun j ↦ (z j).im))
      left_inv := by
        intro uv
        simp
      right_inv := by
        intro z
        funext j
        simp [Complex.re_add_im]
      continuous_toFun := by
        apply continuous_pi
        intro j
        exact ((Complex.continuous_ofReal.comp
          ((continuous_apply j).comp (c.continuous.comp continuous_fst))).add
          ((Complex.continuous_ofReal.comp
            ((continuous_apply j).comp (c.continuous.comp continuous_snd))).mul
              continuous_const))
      continuous_invFun := by
        apply Continuous.prodMk
        · exact c.symm.continuous.comp (continuous_pi (fun j ↦
            Complex.continuous_re.comp (continuous_apply j)))
        · exact c.symm.continuous.comp (continuous_pi (fun j ↦
            Complex.continuous_im.comp (continuous_apply j))) }
  let t : Trivialization (Fin n → ℂ) (π Unit (fun y ↦ ℂ ⊗[ℝ] E y)) :=
    ((e.prod e).transFiberHomeomorph q).compHomeomorph
      (complexificationDoubleTotalHomeomorph V E)
  refine ⟨n, t, ?_, ?_⟩
  · exact ⟨FiberBundle.mem_baseSet_trivializationAt V E x,
      FiberBundle.mem_baseSet_trivializationAt V E x⟩
  intro y hy
  have hey : y ∈ e.baseSet := hy.1
  let L : E y →ₗ[ℝ] (Fin n → ℝ) :=
    c.toLinearMap.comp (IsLinearMap.mk' _ (e.linear ℝ hey))
  let f : (ℂ ⊗[ℝ] E y) → (Fin n → ℂ) := fun w j ↦
    (L (complexificationReIm (E y) w).1 j : ℂ) +
      (L (complexificationReIm (E y) w).2 j : ℂ) * Complex.I
  have hvalue (w : ℂ ⊗[ℝ] E y) : (t ⟨y, w⟩).2 = f w := by
    change q ((e.prod e) ⟨y, complexificationReIm (E y) w⟩).2 = _
    rw [Trivialization.prod_apply' ℝ hey hey]
    rfl
  -- The actual coordinates are the scalar extension of the original real linear map.
  have hadd (u v : ℂ ⊗[ℝ] E y) : f (u + v) = f u + f v := by
    funext j
    simp [f, map_add, add_mul]
    ring
  have hpure (z : ℂ) (v : E y) : f (z ⊗ₜ[ℝ] v) = fun j ↦ z * (L v j : ℂ) := by
    funext j
    rw [show f (z ⊗ₜ[ℝ] v) j =
      (L (complexificationReIm (E y) (z ⊗ₜ[ℝ] v)).1 j : ℂ) +
        (L (complexificationReIm (E y) (z ⊗ₜ[ℝ] v)).2 j : ℂ) * Complex.I from rfl]
    rw [(complexificationReIm_properties (E y)).1]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    calc
      _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) * (L v j : ℂ) := by ring
      _ = _ := by rw [Complex.re_add_im]
  constructor
  · intro u v
    rw [hvalue, hvalue, hvalue]
    exact hadd u v
  · intro z w
    rw [hvalue, hvalue]
    induction w using TensorProduct.inductionOn with
    | tmul a v =>
      rw [TensorProduct.smul_tmul', hpure, hpure]
      funext j
      simp [mul_assoc]
    | add u v hu hv =>
      rw [smul_add, hadd, hu, hv, hadd, smul_add]

end AtiyahSinger.ComplexBundle

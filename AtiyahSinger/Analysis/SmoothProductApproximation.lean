/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Uniform approximation by separated smooth functions

Public module ID: M0974.

On a product of compact smooth manifolds, finite sums of products of smooth
factor functions are uniformly dense in the continuous complex functions. Smooth
bumps separate points and the complex Stone--Weierstrass theorem supplies density.
This is the scalar approximation input for the actual exterior-bundle L2 tensor
identification. No assertion about product Sobolev domains is included.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff Topology

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [T2Space N] [CompactSpace M] [CompactSpace N]

/-- Finite sums of products of smooth factor functions are uniformly dense. -/
theorem dense_span_smooth_products :
    Dense (Submodule.span ℂ (Set.range fun p :
      {f : C(M, ℂ) // ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f} ×
      {g : C(N, ℂ) // ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, ℂ) ∞ g} ↦
      (⟨fun z : M × N ↦ p.1.val z.1 * p.2.val z.2,
        (p.1.val.continuous.comp continuous_fst).mul
          (p.2.val.continuous.comp continuous_snd)⟩ : C(M × N, ℂ))) :
        Set C(M × N, ℂ)) := by
  classical
  let SM := {f : C(M, ℂ) // ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f}
  let SN := {g : C(N, ℂ) // ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, ℂ) ∞ g}
  let t (p : SM × SN) : C(M × N, ℂ) :=
    ⟨fun z ↦ p.1.val z.1 * p.2.val z.2,
      (p.1.val.continuous.comp continuous_fst).mul
        (p.2.val.continuous.comp continuous_snd)⟩
  let L := Submodule.span ℂ (Set.range t)
  have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) := contDiff_mul
  have hconst (c : ℂ) : ContinuousMap.const (M × N) c ∈ L := by
    let p : SM × SN := (⟨ContinuousMap.const M c, contMDiff_const⟩,
      ⟨ContinuousMap.const N 1, contMDiff_const⟩)
    have heq : t p = ContinuousMap.const (M × N) c := by
      ext z
      simp [t, p]
    exact heq ▸ Submodule.subset_span ⟨p, rfl⟩
  -- Multiplying separated functions stays separated; bilinearity handles finite sums.
  have hmul {f g : C(M × N, ℂ)} (hf : f ∈ L) (hg : g ∈ L) : f * g ∈ L := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨b, rfl⟩ := hg
        let p : SM × SN :=
          (⟨a.1.val * b.1.val, hm.contMDiff.comp (a.1.property.prodMk_space b.1.property)⟩,
            ⟨a.2.val * b.2.val, hm.contMDiff.comp (a.2.property.prodMk_space b.2.property)⟩)
        have heq : t a * t b = t p := by
          ext z
          simp only [t, ContinuousMap.mul_apply, ContinuousMap.coe_mk, p]
          ring
        rw [heq]
        exact Submodule.subset_span ⟨p, rfl⟩
      | zero => simp
      | add x y hx hy ihx ihy => simpa [mul_add] using L.add_mem ihx ihy
      | smul c x hx ih => simpa [mul_smul_comm] using L.smul_mem c ih
    | zero => simp
    | add x y hx hy ihx ihy => simpa [add_mul] using L.add_mem ihx ihy
    | smul c x hx ih => simpa [smul_mul_assoc] using L.smul_mem c ih
  -- Conjugation preserves smooth separated functions and their complex span.
  have hstar {f : C(M × N, ℂ)} (hf : f ∈ L) : star f ∈ L := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      let p : SM × SN :=
        (⟨star a.1.val, Complex.conjCLE.toContinuousLinearMap.contMDiff.comp a.1.property⟩,
          ⟨star a.2.val, Complex.conjCLE.toContinuousLinearMap.contMDiff.comp a.2.property⟩)
      have heq : star (t a) = t p := by
        ext z
        simp [t, p]
      exact heq ▸ Submodule.subset_span ⟨p, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [star_add] using L.add_mem ihx ihy
    | smul c x hx ih => simpa only [star_smul] using L.smul_mem (star c) ih
  let A : StarSubalgebra ℂ C(M × N, ℂ) :=
    { carrier := L
      zero_mem' := L.zero_mem
      add_mem' := L.add_mem
      one_mem' := hconst 1
      mul_mem' := hmul
      algebraMap_mem' := hconst
      star_mem' := hstar }
  -- A bump in either factor distinguishes points which differ in that factor.
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    by_cases hfst : x.1 = y.1
    · have hsnd : x.2 ≠ y.2 := fun h ↦ hxy (Prod.ext hfst h)
      obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x.2).mem_iff.mp
        (isClosed_singleton.isOpen_compl.mem_nhds hsnd)
      let p : SM × SN := (⟨ContinuousMap.const M 1, contMDiff_const⟩,
        ⟨⟨fun x ↦ (χ x : ℂ), Complex.continuous_ofReal.comp χ.continuous⟩,
          Complex.ofRealCLM.contMDiff.comp χ.contMDiff⟩)
      refine ⟨t p, ⟨t p, Submodule.subset_span ⟨p, rfl⟩, rfl⟩, ?_⟩
      have hz : χ y.2 = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hχ h (Set.mem_singleton y.2))
      simp [t, p, hz]
    · obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x.1).mem_iff.mp
        (isClosed_singleton.isOpen_compl.mem_nhds hfst)
      let p : SM × SN := (⟨⟨fun x ↦ (χ x : ℂ), Complex.continuous_ofReal.comp χ.continuous⟩,
          Complex.ofRealCLM.contMDiff.comp χ.contMDiff⟩,
        ⟨ContinuousMap.const N 1, contMDiff_const⟩)
      refine ⟨t p, ⟨t p, Submodule.subset_span ⟨p, rfl⟩, rfl⟩, ?_⟩
      have hz : χ y.1 = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hχ h (Set.mem_singleton y.1))
      simp [t, p, hz]
  have hA := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  exact congrArg (fun B : StarSubalgebra ℂ C(M × N, ℂ) ↦ B.toSubalgebra.toSubmodule) hA

end AtiyahSinger

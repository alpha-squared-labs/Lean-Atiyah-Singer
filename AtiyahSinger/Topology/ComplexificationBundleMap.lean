/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationBundle

/-!
# Continuity of scalar extension on the original bundle topology

Public module ID: M1725.

Complexification of a continuous real-linear bundle map is continuous in the
original complexification topologies. The actual real/imaginary comparison
identifies it with the original map on each of the two real factors.

This common scalar-extension interface is used by normal-composition and
transverse-normal constructions; it does not replace their specified bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

/-- Scalar extension preserves continuity of the original real bundle map.
This adapter compares the actual real/imaginary induced topologies. -/
theorem continuous_complexification_map
    {X : Type*} {V W : Type*} {E : X → Type*} {F : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    [TopologicalSpace (TotalSpace V E)] [TopologicalSpace (TotalSpace W F)]
    (L : ∀ x, E x →ₗ[ℝ] F x)
    (hL : Continuous (fun z : TotalSpace V E ↦
      (⟨z.proj, L z.proj z.snd⟩ : TotalSpace W F))) :
    letI := complexificationTopology V E
    letI := complexificationTopology W F
    Continuous (fun z : TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] E x) ↦
      (⟨z.proj, (L z.proj).baseChange ℂ z.snd⟩ :
        TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] F x))) := by
  let := complexificationTopology V E
  let := complexificationTopology W F
  have hcoords (x : X) (v : ℂ ⊗[ℝ] E x) :
      complexificationReIm (F x) ((L x).baseChange ℂ v) =
        (L x (complexificationReIm (E x) v).1,
          L x (complexificationReIm (E x) v).2) := by
    induction v using TensorProduct.inductionOn with
    | tmul z v =>
      rw [LinearMap.baseChange_tmul, (complexificationReIm_properties _).1,
        (complexificationReIm_properties _).1, map_smul, map_smul]
    | add u v hu hv =>
      simp only [map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      rfl
  have hpair : Continuous (fun z : TotalSpace (V × V) (E ×ᵇ E) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace V E),
        (⟨z.proj, z.snd.2⟩ : TotalSpace V E))) := continuous_induced_dom
  have hre := hL.comp ((continuous_fst.comp hpair).comp
    (complexificationDoubleTotalHomeomorph V E).continuous)
  have him := hL.comp ((continuous_snd.comp hpair).comp
    (complexificationDoubleTotalHomeomorph V E).continuous)
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply (hre.prodMk him).congr
  intro z
  symm
  change ((⟨z.proj, (complexificationReIm (F z.proj)
      ((L z.proj).baseChange ℂ z.snd)).1⟩ : TotalSpace W F),
    (⟨z.proj, (complexificationReIm (F z.proj)
      ((L z.proj).baseChange ℂ z.snd)).2⟩ : TotalSpace W F)) =
      ((⟨z.proj, L z.proj (complexificationReIm (E z.proj) z.snd).1⟩ : TotalSpace W F),
        (⟨z.proj, L z.proj (complexificationReIm (E z.proj) z.snd).2⟩ : TotalSpace W F))
  rw [hcoords]


end AtiyahSinger.ComplexBundle

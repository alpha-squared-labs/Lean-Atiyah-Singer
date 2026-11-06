/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationBundle
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# The proper real/imaginary product map

Public module ID: M1734.

The native complexification embeds into the product of the original real
total spaces. Its image consists exactly of pairs with a common base point.
For a Hausdorff base this is closed, so the actual map is proper. Neither
individual real projection is asserted proper.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology
open scoped TensorProduct

variable {X : Type*} [TopologicalSpace X] (V : Type*) [TopologicalSpace V]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace V E)]

/-- The actual real and imaginary vectors in their original real total spaces. -/
def complexificationProductMap :
    letI := complexificationTopology V E
    C(TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] E x), TotalSpace V E × TotalSpace V E) :=
  letI := complexificationTopology V E
  { toFun := fun z ↦ (⟨z.proj, (complexificationReIm (E z.proj) z.snd).1⟩,
      ⟨z.proj, (complexificationReIm (E z.proj) z.snd).2⟩)
    continuous_toFun := (FiberBundle.Prod.isInducing_diag V E V E).continuous.comp
      (complexificationDoubleTotalHomeomorph V E).continuous }

variable [T2Space X] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]

/-- The real/imaginary map is a closed embedding onto the pairs over the same base point. -/
theorem isClosedEmbedding_complexificationProductMap :
    letI := complexificationTopology V E
    IsClosedEmbedding (complexificationProductMap V E) := by
  let := complexificationTopology V E
  let d : TotalSpace (V × V) (E ×ᵇ E) → TotalSpace V E × TotalSpace V E :=
    fun z ↦ (⟨z.proj, z.snd.1⟩, ⟨z.proj, z.snd.2⟩)
  have hd : IsClosedEmbedding d := by
    refine ⟨⟨FiberBundle.Prod.isInducing_diag V E V E, ?_⟩, ?_⟩
    · rintro ⟨x, u, v⟩ ⟨y, a, b⟩ h
      have hbase := congrArg (fun z : TotalSpace V E × TotalSpace V E ↦ z.1.proj) h
      change x = y at hbase
      subst y
      have h₁ := TotalSpace.mk_injective x (congrArg Prod.fst h)
      have h₂ := TotalSpace.mk_injective x (congrArg Prod.snd h)
      exact congrArg (TotalSpace.mk x) (Prod.ext h₁ h₂)
    · have hrange : Set.range d = {z : TotalSpace V E × TotalSpace V E | z.1.proj = z.2.proj} := by
        ext z
        constructor
        · rintro ⟨w, rfl⟩
          rfl
        · rcases z with ⟨⟨x, v⟩, ⟨y, w⟩⟩
          intro h
          change x = y at h
          subst y
          exact ⟨⟨x, v, w⟩, rfl⟩
      rw [hrange]
      exact isClosed_eq ((FiberBundle.continuous_proj V E).comp continuous_fst)
        ((FiberBundle.continuous_proj V E).comp continuous_snd)
  exact hd.comp (complexificationDoubleTotalHomeomorph V E).isClosedEmbedding

/-- The combined real/imaginary map preserves compact supports by proper pullback. -/
theorem isProperMap_complexificationProductMap :
    letI := complexificationTopology V E
    IsProperMap (complexificationProductMap V E) :=
  letI := complexificationTopology V E
  (isClosedEmbedding_complexificationProductMap V E).isProperMap

end AtiyahSinger.ComplexBundle

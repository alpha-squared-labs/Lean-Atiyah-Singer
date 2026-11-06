/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.ComplexificationBundle

/-!
# The original complexification topology commutes with pullback

Public module ID: M1735.

The scalar-extension fibers on both sides are literally the same tensor
products. Expanding their existing induced topologies shows that they also
have the same total-space topology: each records the unchanged base point
and the same ordered real and imaginary vectors.

This comparison is used when extending the original complexified normal
pullback to the fiberwise sphere compactification. It supplies no second
complexification or topology convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped TensorProduct

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (V : Type*) (E : Y → Type*) [∀ y, AddCommGroup (E y)] [∀ y, Module ℝ (E y)]
  [TopologicalSpace (TotalSpace V E)] (f : C(X, Y))

/-- Pulling back the original tensor complexification preserves its actual induced topology. -/
theorem complexificationTopology_pullback :
    letI : ∀ x, AddCommGroup (((f : X → Y) *ᵖ E) x) :=
      fun x ↦ inferInstanceAs (AddCommGroup (E (f x)))
    letI := complexificationTopology V E
    complexificationTopology V ((f : X → Y) *ᵖ E) =
      (inferInstance : TopologicalSpace
        (TotalSpace Unit ((f : X → Y) *ᵖ (fun y ↦ ℂ ⊗[ℝ] E y)))) := by
  let : ∀ x, AddCommGroup (((f : X → Y) *ᵖ E) x) :=
    fun x ↦ inferInstanceAs (AddCommGroup (E (f x)))
  let := complexificationTopology V E
  -- Both sides induce the same three coordinates; the source base coordinate occurs twice.
  simp only [complexificationTopology, FiberBundle.Prod.topologicalSpace,
    Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
    instTopologicalSpaceProd, induced_inf, induced_compose]
  let T := TotalSpace Unit (fun x : X ↦ ℂ ⊗[ℝ] E (f x))
  let t₀ : TopologicalSpace T := induced Bundle.TotalSpace.proj inferInstance
  let t₁ : TopologicalSpace T := induced
    (fun z : T ↦ (⟨f z.proj, (complexificationReIm (E (f z.proj)) z.snd).1⟩ :
      TotalSpace V E)) inferInstance
  let t₂ : TopologicalSpace T := induced
    (fun z : T ↦ (⟨f z.proj, (complexificationReIm (E (f z.proj)) z.snd).2⟩ :
      TotalSpace V E)) inferInstance
  change (t₀ ⊓ t₁) ⊓ (t₀ ⊓ t₂) = t₀ ⊓ (t₁ ⊓ t₂)
  calc
    _ = (t₀ ⊓ t₀) ⊓ (t₁ ⊓ t₂) := by ac_rfl
    _ = _ := by rw [inf_idem]

end AtiyahSinger.ComplexBundle

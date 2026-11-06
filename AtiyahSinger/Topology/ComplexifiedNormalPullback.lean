/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalBundle
public import AtiyahSinger.Topology.ComplexificationBundle

/-!
# The fixed complex bundle used by the tangent embedding pushforward

Public module ID: M1742.

The bundle over TM is literally the complexification of the pulled-back real
normal bundle. Its topology is the existing complexification topology of the
native real pullback, and its finite-rank certificate uses the same selected
normal atlas. These are implementation components of SG III.12 (12.7), not a
second definition of the normal bundle of Tf.

The later geometric splitting identifies this fixed complex bundle, as a real
bundle, with that actual normal bundle. Keeping this complex carrier fixed makes
comparison of different splittings possible without changing the Thom domain.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped ContDiff Manifold TensorProduct

attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)

/-- The actual complexification of the normal bundle pulled back to the tangent bundle. -/
abbrev ComplexifiedNormalPullback (z : TangentBundle 𝓘(ℝ, E) M) : Type _ :=
  ℂ ⊗[ℝ] NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj

/-- The original complexification topology on the native real normal pullback. -/
@[reducible]
def complexifiedNormalPullbackTopology :
    TopologicalSpace (TotalSpace Unit (ComplexifiedNormalPullback f)) := by
  letI : ∀ z, AddCommGroup
      (((π E (TangentSpace 𝓘(ℝ, E))) *ᵖ (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) z) :=
    fun z ↦ inferInstanceAs (AddCommGroup (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj))
  exact ComplexBundle.complexificationTopology (NormalModel E F)
    ((π E (TangentSpace 𝓘(ℝ, E))) *ᵖ (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))

attribute [local instance] complexifiedNormalPullbackTopology

set_option linter.defProp false in
/-- Finite complex rank uses the same chosen real normal atlas, pulled back along projection. -/
@[instance_reducible]
def isFiniteRank_complexifiedNormalPullback
    (hf : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ComplexBundle.IsFiniteRank (ComplexifiedNormalPullback f) := by
  let proj : C(TangentBundle 𝓘(ℝ, E) M, M) :=
    ⟨π E (TangentSpace 𝓘(ℝ, E)), FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))⟩
  let : ∀ z, AddCommGroup ((proj *ᵖ (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) z) :=
    fun z ↦ inferInstanceAs (AddCommGroup (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f (proj z)))
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := FiberBundle.pullback (F := NormalModel E F)
    (E := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) proj
  let := VectorBundle.pullback (𝕜 := ℝ) (F := NormalModel E F)
    (E := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) proj
  exact ComplexBundle.isFiniteRank_complexification (NormalModel E F)
    ((proj : TangentBundle 𝓘(ℝ, E) M → M) *ᵖ (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))

end AtiyahSinger

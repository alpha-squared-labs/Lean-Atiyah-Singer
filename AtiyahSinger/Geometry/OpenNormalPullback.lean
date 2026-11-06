/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TransverseNormalPullback
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Normal quotient comparison in a square of local diffeomorphisms

Public module ID: M1321.

The actual differential of the ambient local diffeomorphism identifies the
normal quotients of the two immersions. Invertibility of both horizontal
maps supplies the range-preimage and transversality conditions of the existing
normal pullback theorem. Its quotient representative formula fixes the map,
and both directions are smooth in the original normal atlases.

Source: the standard normal naturality argument underlying SG III.12 and
Karoubi IV.5.21--5.22. No Cartesian or properness assumption is needed here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {M N P Q : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold 𝓘(ℝ, H) ∞ Q]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local diffeomorphisms in a smooth square identify the actual quotient normal bundles. -/
theorem exists_normalPullback_equiv_of_localDiffeomorph
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, H) P Q ∞)
    (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, H) N Q ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsImmersion 𝓘(ℝ, G) 𝓘(ℝ, H) ∞ g)
    (hi : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ i)
    (hj : IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, H) ∞ j)
    (hcomm : ∀ x, j (f x) = g (i x)) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    letI := normalBundleFiberBundle g hg
    letI := normalBundleVectorBundle g hg
    letI := normalBundleContMDiffVectorBundle g hg
    ∃ e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ]
        NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x),
      (∀ (x : M) (v : F),
        e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x)).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f x) v)) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel G H)) ∞
        (fun z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
          (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (NormalModel G H)
            ((i : M → P) *ᵖ (NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g)))) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel G H))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : TotalSpace (NormalModel G H)
            ((i : M → P) *ᵖ (NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g)) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ :
            TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))) := by
  let A (x : M) : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let B (x : M) : G →L[ℝ] H := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x)
  let I (x : M) : E →L[ℝ] G := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) i x
  let J (x : M) : F →L[ℝ] H := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f x)
  have hI (x : M) : Function.Bijective (I x) :=
    (show (I x).IsInvertible from hi.isInvertible_mfderiv (by simp) x).bijective
  have hJ (x : M) : Function.Bijective (J x) :=
    (show (J x).IsInvertible from hj.isInvertible_mfderiv (by simp) (f x)).bijective
  -- The chain rule gives the same commuting linear square at every original base point.
  have hchain (x : M) : (J x).comp (A x) = (B x).comp (I x) := by
    have hl := mfderiv_comp x (j.contMDiff.mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x)
    have hr := mfderiv_comp x (g.contMDiff.mdifferentiable (by simp) (i x))
      (i.contMDiff.mdifferentiable (by simp) x)
    rw [show (j : N → Q) ∘ f = (g : P → Q) ∘ i from funext hcomm] at hl
    exact hl.symm.trans hr
  apply exists_transverse_normalPullback_equiv f g i j hf hg hcomm
  · intro x v
    change J x v ∈ LinearMap.range (B x).toLinearMap ↔
      v ∈ LinearMap.range (A x).toLinearMap
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨a, ha⟩ := (hI x).surjective w
      refine ⟨a, ?_⟩
      apply (hJ x).injective
      have hl := DFunLike.congr_fun (hchain x) a
      change J x (A x a) = B x (I x a) at hl
      rw [ha] at hl
      exact hl.trans hw
    · rintro ⟨w, rfl⟩
      exact ⟨I x w, (DFunLike.congr_fun (hchain x) w).symm⟩
  · intro x
    change ∀ w : H, ∃ (v : F) (u : G), w = J x v + B x u
    intro w
    obtain ⟨v, hv⟩ := (hJ x).surjective w
    refine ⟨v, 0, ?_⟩
    rw [hv, map_zero, add_zero]

end AtiyahSinger

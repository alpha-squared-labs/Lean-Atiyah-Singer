/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNormalBundle

/-!
# Naturality of the canonical vertical tangent lift

Public module ID: M1497.

The differential of the actual tangent map intertwines the two canonical
vertical lifts. Differentiate the same affine fiber curve before and after the
original smooth map, and apply the chain rule. All tangent spaces retain their
native full models and all vertical lifts are the existing ones.

This standard tangent-sequence naturality is used in the normal-composition
and transverse-normal comparisons. Its affine-curve implementation remains
private; no alternative vertical tangent object or connection is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tangent_fiberAffine_derivative
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (z : TangentBundle 𝓘(ℝ, E) M) :
    let a : E → TangentBundle 𝓘(ℝ, E) M := fun v ↦
      ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from v)⟩
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × E) ∞ a ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 = tangentVerticalLift E M z := by
  -- The chosen tangent trivialization at its own base point is the identity.
  let e := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj).continuousLinearEquivAt
    ℝ z.proj (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj)
  have he (v : E) : e v = v := by
    rw [Trivialization.coe_continuousLinearEquivAt_eq]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source E z.proj),
      mfderiv_extChartAt_self]
    rfl
  have hei (v : E) : e.symm v = v := by
    rw [← he (e.symm v), e.apply_symm_apply]
  let a : E → TangentBundle 𝓘(ℝ, E) M := fun v ↦
      ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from v)⟩
  have htriv (v : E) :
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj (a v)).2 = (show E from z.snd) + v :=
    he ((show E from z.snd) + v)
  change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × E) ∞ a ∧
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 = tangentVerticalLift E M z
  refine ⟨?_, ?_⟩
  · intro v
    rw [modelWithCornersSelf_prod, Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_const, ?_⟩
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun b : E ↦ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj (a b)).2) v
    simp_rw [htriv]
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun v : E ↦ (show E from z.snd) + v) v
    exact (contMDiffAt_const.add contMDiffAt_id : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun v : E ↦ (show E from z.snd) + v) v)
  · have hfun : (fun v : E ↦ (⟨z.proj, z.snd + e.symm v⟩ :
          TangentBundle 𝓘(ℝ, E) M)) = a := by
      funext v
      rw [hei]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 =
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E)
        (fun v : E ↦ (⟨z.proj, z.snd + e.symm v⟩ : TangentBundle 𝓘(ℝ, E) M)) 0).comp
        (NormedSpace.fromTangentSpace (0 : E)).symm.toContinuousLinearMap).comp
          e.toContinuousLinearMap
    rw [hfun]
    ext v
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0) v =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0) (e v)
    rw [he]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tangent derivative intertwines the canonical vertical lifts. -/
theorem tangentMap_verticalLift
    {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (z : TangentBundle 𝓘(ℝ, E) M) :
    (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).comp
        (tangentVerticalLift E M z) =
      (tangentVerticalLift F N (smoothTangentMap f z)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) := by
  -- Differentiate the equality between the actual affine fiber curves.
  let a : E → TangentBundle 𝓘(ℝ, E) M := fun v ↦
      ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from v)⟩
  let b : F → TangentBundle 𝓘(ℝ, F) N := fun v ↦
    ⟨f z.proj, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) z.snd +
      (show TangentSpace 𝓘(ℝ, F) (f z.proj) from v)⟩
  let L : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj
  have ha0 : a 0 = z := by simp [a]
  have hb0 : b 0 = smoothTangentMap f z := by simp [b, smoothTangentMap, tangentMap]
  have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × E) ∞ a :=
    (tangent_fiberAffine_derivative z).1
  have hb : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F × F) ∞ b :=
    (tangent_fiberAffine_derivative (smoothTangentMap f z)).1
  have heq : smoothTangentMap f ∘ a = b ∘ L := by
    funext v
    change (⟨f z.proj, L ((show E from z.snd) + v)⟩ : TangentBundle 𝓘(ℝ, F) N) =
      ⟨f z.proj, L z.snd + L v⟩
    exact congrArg (fun w ↦ (⟨f z.proj, w⟩ : TangentBundle 𝓘(ℝ, F) N)) (map_add L _ v)
  have hleft := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E × E))
    (I'' := 𝓘(ℝ, F × F)) 0
    (ha0 ▸ (smoothTangentMap f).contMDiff.mdifferentiable (by simp) z)
    (ha.mdifferentiableAt (by simp))
  have hright := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    (I'' := 𝓘(ℝ, F × F)) 0
    (show MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F × F) b (L 0) from by
      simpa only [map_zero] using hb.mdifferentiableAt (x := 0) (by simp))
    ((L.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp))
  have hLder : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) L 0 = L := by
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  have hDa : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 = tangentVerticalLift E M z :=
    (tangent_fiberAffine_derivative z).2
  have hDb : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) b 0 =
      tangentVerticalLift F N (smoothTangentMap f z) :=
    (tangent_fiberAffine_derivative (smoothTangentMap f z)).2
  rw [heq, hright, hDa, hLder, map_zero, hDb] at hleft
  have hzder : mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) (a 0) =
      mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z := by
    congr 1
  rw [hzder] at hleft
  exact hleft.symm


end AtiyahSinger

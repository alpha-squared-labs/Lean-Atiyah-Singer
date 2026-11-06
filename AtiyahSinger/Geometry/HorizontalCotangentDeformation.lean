/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SubmersionCotangentSplitting

/-!
# The global cotangent deformation fixed by a horizontal lift

Public module ID: M1278.

A specified smooth horizontal lift determines the horizontal part of every
actual covector by pullback along the original submersion differential.
Interpolate from that horizontal part to the original covector on the whole
cotangent bundle. This continuous deformation is defined before choosing any
coordinate chart. It supplies the common global frequency path for the
associated product symbol homotopy; the vertical symbol is evaluated at its
original vertical covector throughout that separate symbol construction.

The deformation at time zero collapses the vertical directions. No properness
or ellipticity is asserted for this cotangent deformation itself.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function
open scoped Manifold ContDiff Topology

attribute [local instance] verticalTangentTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)

namespace SmoothHorizontalLift

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in
-- Keep the original native pullback, vertical, and cotangent bundle topologies together.
/-- The given lift defines one continuous global deformation from horizontal to full covectors. -/
theorem continuous_cotangentDeformation
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (H : SmoothHorizontalLift f) :
    let C := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ
    Continuous (fun p : ℝ × TotalSpace (E →L[ℝ] ℝ) C ↦
      (⟨p.2.proj, (1 - p.1) • ((p.2.snd.comp (H.lift p.2.proj)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f p.2.proj)) + p.1 • p.2.snd⟩ :
          TotalSpace (E →L[ℝ] ℝ) C)) := by
  classical
  let C := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ
  let A := (f : M → N) *ᵖ (fun y : N ↦ TangentSpace 𝓘(ℝ, F) y →L[ℝ] ℝ)
  let V := VerticalTangentModel E F
  let W := VerticalCotangentFiber (E := E) (F := F) (f : M → N)
  let := verticalTangentFiberBundle f hf
  let := verticalTangentVectorBundle f hf
  let := verticalTangentContMDiffVectorBundle f hf
  let X := TotalSpace (E →L[ℝ] ℝ) C
  let Y := TotalSpace ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (A ×ᵇ W)
  let e : X ≃ₜ Y := H.cotangentSplitHomeomorph f hf
  have he (z : X) : e z = H.cotangentSplitMap f z :=
    (exists_cotangentSplitHomeomorph f hf H).choose_spec.1 z
  let collapse : Y → Y := fun z ↦ ⟨z.proj, z.snd.1, 0⟩
  -- The base component and zero vertical section are continuous in the same splitting bundle.
  have hcollapse : Continuous collapse := by
    rw [(FiberBundle.Prod.isInducing_diag (F →L[ℝ] ℝ) A (V →L[ℝ] ℝ) W).continuous_iff]
    apply Continuous.prodMk
    · exact (FiberBundle.Prod.isInducing_diag
        (F →L[ℝ] ℝ) A (V →L[ℝ] ℝ) W).continuous.fst
    · exact (Bundle.Trivialization.continuous_zeroSection ℝ (F := V →L[ℝ] ℝ) (E := W)).comp
        (FiberBundle.continuous_proj ((F →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (A ×ᵇ W))
  let horizontal : X → X := fun z ↦
    ⟨z.proj, (z.snd.comp (H.lift z.proj)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj)⟩
  have hhorizontal (z : X) : e.symm (collapse (e z)) = horizontal z := by
    apply e.injective
    rw [e.apply_symm_apply, he, he]
    change (⟨z.proj, z.snd.comp (H.lift z.proj), 0⟩ : Y) =
      (⟨z.proj,
        (((z.snd.comp (H.lift z.proj)).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj)).comp (H.lift z.proj)),
        verticalCotangentRestriction (E := E) (F := F) f z.proj
          ((z.snd.comp (H.lift z.proj)).comp
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj))⟩ : Y)
    apply congrArg (fun v : A z.proj × W z.proj ↦ (⟨z.proj, v⟩ : Y))
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro v
      change z.snd (H.lift z.proj v) =
        z.snd (H.lift z.proj (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj (H.lift z.proj v)))
      exact (congrArg (fun w ↦ z.snd (H.lift z.proj w)) (H.right_inv z.proj v)).symm
    · apply ContinuousLinearMap.ext
      intro v
      change 0 = z.snd (H.lift z.proj (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj v.val))
      rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj v.val = 0 from v.property,
        map_zero, map_zero]
  have hc : Continuous horizontal :=
    (e.symm.continuous.comp (hcollapse.comp e.continuous)).congr hhorizontal
  -- Interpolate in the actual cotangent fibers, using each original local trivialization.
  have hb : Continuous (fun p : ℝ × X ↦ p.2.proj) :=
    (FiberBundle.continuous_proj (E →L[ℝ] ℝ) C).comp continuous_snd
  change Continuous (fun p : ℝ × X ↦
    (⟨p.2.proj, (1 - p.1) • (horizontal p.2).snd + p.1 • p.2.snd⟩ : X))
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  let a := trivializationAt (E →L[ℝ] ℝ) C p.2.proj
  have hu := ((FiberBundle.continuousAt_totalSpace (E →L[ℝ] ℝ)
    (fun q : ℝ × X ↦ horizontal q.2)
    (x₀ := p)).mp (hc.comp continuous_snd).continuousAt).2
  have hv := ((FiberBundle.continuousAt_totalSpace (E →L[ℝ] ℝ)
    (fun q : ℝ × X ↦ q.2)
    (x₀ := p)).mp (continuous_snd : Continuous (fun q : ℝ × X ↦ q.2)).continuousAt).2
  have hn : ∀ᶠ q in 𝓝 p, q.2.proj ∈ a.baseSet :=
    hb.continuousAt (a.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (E →L[ℝ] ℝ) C p.2.proj))
  have hs : ContinuousAt (fun q : ℝ × X ↦ 1 - q.1) p :=
    continuousAt_const.sub continuousAt_fst
  have ht : ContinuousAt (fun q : ℝ × X ↦ q.1) p := continuousAt_fst
  apply ((hs.smul hu).add (ht.smul hv)).congr_of_eventuallyEq
  filter_upwards [hn] with q hq
  change (a ⟨q.2.proj, (1 - q.1) • (horizontal q.2).snd + q.1 • q.2.snd⟩).2 =
    (1 - q.1) • (a (horizontal q.2)).2 + q.1 • (a q.2).2
  simp only [← a.continuousLinearMapAt_apply_of_mem ℝ hq, map_add, map_smul]
  have h₀ : (a.continuousLinearMapAt ℝ q.2.proj) (horizontal q.2).snd =
      (a (horizontal q.2)).2 := a.continuousLinearMapAt_apply_of_mem ℝ hq _
  have h₁ : (a.continuousLinearMapAt ℝ q.2.proj) q.2.snd = (a q.2).2 :=
    a.continuousLinearMapAt_apply_of_mem ℝ hq _
  rw [h₀, h₁]

end SmoothHorizontalLift

end AtiyahSinger

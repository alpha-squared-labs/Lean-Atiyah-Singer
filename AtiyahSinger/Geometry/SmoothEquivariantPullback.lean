/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import AtiyahSinger.Topology.EquivariantBundlePullback

/-!
# Smooth equivariant pullback with the native bundle model

Public module ID: M1395.

The original equivariant pullback action is transported only across the equality
of its native modeled total topology and the existing Unit pullback topology.
Its moving-fiber maps remain exactly the original pullback maps. Smoothness is
checked in the actual pulled frames, so restriction to an invariant open
submanifold keeps both its original action and its original smooth sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {r : ℕ} {E : X → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- The existing pullback action in the original native modeled total-space topology. -/
def EquivariantStructure.modelPullback
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
    EquivariantStructure G ((f : Y → X) *ᵖ E) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let tP : TopologicalSpace (TotalSpace Unit ((f : Y → X) *ᵖ E)) :=
    @Pullback.TotalSpace.topologicalSpace X Unit E Y (f : Y → X) _
      (modelTopology (EuclideanSpace ℂ (Fin r)) E)
  have htop : modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) = tP := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tP, modelTopology]
    rfl
  let := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
  exact {
    linearMap := σ.pullbackLinearMap f heq
    one_map := (σ.pullback_properties f heq).1
    mul_map := (σ.pullback_properties f heq).2.1
    continuous_action := by
      change @Continuous _ _
        (@instTopologicalSpaceProd G (TotalSpace Unit ((f : Y → X) *ᵖ E)) _
          (modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)))
        (modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)) _
      rw [htop]
      exact (σ.pullback_properties f heq).2.2 }

omit [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E] in
/-- Lifting the native pullback action gives the same original total vector. -/
theorem EquivariantStructure.modelPullback_lift
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (g : G) (y : Y) (v : E (f y)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
    (⟨f (g • y), (σ.modelPullback f heq).linearMap g y v⟩ : TotalSpace Unit E) =
      ⟨g • f y, σ.linearMap g (f y) v⟩ := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
  have hcast (a b : X) (hab : a = b) (L : E (f y) →ₗ[ℂ] E b) :
      (⟨a, (Eq.mpr (congrArg (fun x ↦ E (f y) →ₗ[ℂ] E x) hab) L) v⟩ :
        TotalSpace Unit E) = ⟨b, L v⟩ := by
    subst b
    rfl
  change (⟨f (g • y), σ.pullbackLinearMap f heq g y v⟩ : TotalSpace Unit E) = _
  exact hcast (f (g • y)) (g • f y) (heq g y) (σ.linearMap g (f y))

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG) [ChartedSpace HG G]
  {n m : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) Y]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G X]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G Y]

/-- Equivariant smooth pullback preserves the original joint smooth bundle action. -/
theorem EquivariantStructure.modelPullback_isSmooth
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (hσ : σ.IsSmooth (n := n) (r := r) IG)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f) :
    (σ.modelPullback f heq).IsSmooth (n := m) (r := r) IG := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
  -- Every native pulled frame is an original frame composed with the same base map.
  rintro _ _ ⟨e, he, rfl⟩ ⟨d, hd, rfl⟩ j
  let := he
  let := hd
  have hbase : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : G × Y ↦ (p.1, f p.2)) :=
    contMDiff_fst.prodMk (hf.comp contMDiff_snd)
  apply ((hσ e d j).comp hbase.contMDiffOn (fun p hp ↦
    ⟨hp.1, (heq p.1 p.2) ▸ hp.2⟩)).congr
  intro p hp
  have hframe : (e.pullback f).symmL ℂ p.2 (EuclideanSpace.single j 1) =
      e.symmL ℂ (f p.2) (EuclideanSpace.single j 1) := by
    rw [(e.pullback f).symmL_apply (R := ℂ) hp.1, e.symmL_apply (R := ℂ) hp.1,
      (e.pullback f).symm_apply hp.1]
    rfl
  change (d ⟨f (p.1 • p.2), (σ.modelPullback f heq).linearMap p.1 p.2
    ((e.pullback f).symmL ℂ p.2 (EuclideanSpace.single j 1))⟩).2 = _
  rw [hframe]
  exact congrArg (fun z : TotalSpace Unit E ↦
    (d (⟨z.proj, z.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)).2)
      (σ.modelPullback_lift f heq p.1 p.2 (e.symmL ℂ (f p.2) (EuclideanSpace.single j 1)))

end AtiyahSinger.ComplexBundle

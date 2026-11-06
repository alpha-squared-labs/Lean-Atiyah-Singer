/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNormalPullback
public import AtiyahSinger.Topology.ComplexificationBundleMap
public import AtiyahSinger.Topology.ComplexificationPullbackTopology
public import AtiyahSinger.Topology.ComplexifiedNormalPullback

/-!
# Complexification of a smooth normal pullback comparison

Public module ID: M1965.

The supplied real quotient comparison is pulled back along the actual tangent
projection and extended to complex scalars. Both native pullback layers are
retained. This constructs the complex bundle isomorphism used by the Thom
naturality square, preserving the ordered real and imaginary normal factors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold
open scoped ContDiff TensorProduct

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology complexifiedNormalPullbackTopology

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
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, H) P Q ∞)
  (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsImmersion 𝓘(ℝ, G) 𝓘(ℝ, H) ∞ g)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TP" => TangentBundle 𝓘(ℝ, G) P
local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νg" => NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g
local notation "Vf" => NormalModel E F
local notation "Vg" => NormalModel G H
local notation "Ti" => smoothTangentMap i
local notation "V" => ((fun z : TP ↦ Bundle.TotalSpace.proj z) *ᵖ νg)

set_option maxHeartbeats 600000 in
-- Compare the native iterated pullbacks before introducing their scalar extensions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar extension of a smooth normal comparison respects the actual tangent pullbacks. -/
theorem exists_complexifiedNormalPullback_iso
    (e : ∀ x, νf x ≃L[ℝ] νg (i x))
    (hes :
      letI := normalBundleFiberBundle f hf
      letI := normalBundleVectorBundle f hf
      letI := normalBundleContMDiffVectorBundle f hf
      letI := normalBundleFiberBundle g hg
      letI := normalBundleVectorBundle g hg
      letI := normalBundleContMDiffVectorBundle g hg
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
        (fun z : TotalSpace Vf νf ↦ (⟨z.proj, e z.proj z.snd⟩ :
          TotalSpace Vg ((i : M → P) *ᵖ νg))))
    (heis :
      letI := normalBundleFiberBundle f hf
      letI := normalBundleVectorBundle f hf
      letI := normalBundleContMDiffVectorBundle f hf
      letI := normalBundleFiberBundle g hg
      letI := normalBundleVectorBundle g hg
      letI := normalBundleContMDiffVectorBundle g hg
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
        (fun z : TotalSpace Vg ((i : M → P) *ᵖ νg) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace Vf νf))) :
    letI : ∀ p : TP, AddCommGroup (V p) :=
      fun p ↦ by change AddCommGroup (νg p.proj); infer_instance
    letI : ∀ p : TP, Module ℝ (V p) :=
      fun p ↦ by change Module ℝ (νg p.proj); infer_instance
    letI := ComplexBundle.complexificationTopology Vg V
    let B : TP → Type _ := fun p : TP ↦ ℂ ⊗[ℝ] V p
    let D : TM → Type _ := (Ti : TM → TP) *ᵖ B
    letI gD : ∀ z : TM, AddCommGroup (D z) := fun z ↦ by
      change AddCommGroup (ℂ ⊗[ℝ] V (Ti z)); infer_instance
    letI mD : ∀ z : TM, Module ℂ (D z) := fun z ↦ by
      change Module ℂ (ℂ ⊗[ℝ] V (Ti z)); infer_instance
    letI tD : TopologicalSpace (TotalSpace Unit D) :=
      Pullback.TotalSpace.topologicalSpace Unit B (Ti : TM → TP)
    letI gF : ∀ z : TM, AddCommGroup (ComplexifiedNormalPullback f z) := fun z ↦ by
      change AddCommGroup (ℂ ⊗[ℝ] νf z.proj); infer_instance
    letI mF : ∀ z : TM, Module ℂ (ComplexifiedNormalPullback f z) := fun z ↦ by
      change Module ℂ (ℂ ⊗[ℝ] νf z.proj); infer_instance
    let l (z : TM) : ComplexifiedNormalPullback f z ≃ₗ[ℂ] D z := by
      change (ℂ ⊗[ℝ] νf z.proj) ≃ₗ[ℂ] (ℂ ⊗[ℝ] νg (i z.proj))
      exact (e z.proj).toLinearEquiv.baseChange ℝ ℂ _ _
    ∃ U : @ComplexBundle.Iso TM (ComplexifiedNormalPullback f) D gF mF gD mD
        (complexifiedNormalPullbackTopology f) tD,
      ∀ (z : TM) (v : ComplexifiedNormalPullback f z), U.linearEquiv z v = l z v := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  let (p : TP) : AddCommGroup (V p) := by
    change AddCommGroup (νg p.proj)
    infer_instance
  let (p : TP) : Module ℝ (V p) := by
    change Module ℝ (νg p.proj)
    infer_instance
  let := ComplexBundle.complexificationTopology Vg V
  let p : C(TM, M) := ⟨fun z ↦ z.proj, FiberBundle.continuous_proj _ _⟩
  let s : C(TM, TP) := ⟨Ti, (Ti).contMDiff.continuous⟩
  let ic : C(M, P) := ⟨i, i.contMDiff.continuous⟩
  let ψ : C(TP, P) := ⟨fun z ↦ z.proj, FiberBundle.continuous_proj _ _⟩
  let W := (p : TM → M) *ᵖ νf
  let Z := (s : TM → TP) *ᵖ V
  let (z : TM) : AddCommGroup (W z) := by change AddCommGroup (νf z.proj); infer_instance
  let (z : TM) : Module ℝ (W z) := by change Module ℝ (νf z.proj); infer_instance
  let (z : TM) : AddCommGroup (Z z) := by
    change AddCommGroup (νg (i z.proj)); infer_instance
  let (z : TM) : Module ℝ (Z z) := by change Module ℝ (νg (i z.proj)); infer_instance
  let L (z : TM) : W z ≃ₗ[ℝ] Z z := (e z.proj).toLinearEquiv
  -- Lift to the original normal bundles, then retain each of the two pullback bases.
  have hL : Continuous (fun z : TotalSpace Vf W ↦
      (⟨z.proj, L z.proj z.snd⟩ : TotalSpace Vg Z)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vg V s).continuous_iff]
    refine (Pullback.continuous_proj Vf νf p).prodMk ?_
    rw [(inducing_pullbackTotalSpaceEmbedding Vg νg ψ).continuous_iff]
    refine (s.continuous.comp (Pullback.continuous_proj Vf νf p)).prodMk ?_
    exact (Pullback.continuous_lift Vg νg ic).comp
      (hes.continuous.comp (Pullback.continuous_lift Vf νf p))
  have hLi : Continuous (fun z : TotalSpace Vg Z ↦
      (⟨z.proj, (L z.proj).symm z.snd⟩ : TotalSpace Vf W)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Vf νf p).continuous_iff]
    refine (Pullback.continuous_proj Vg V s).prodMk ?_
    let k : TotalSpace Vg Z → TotalSpace Vg ((ic : M → P) *ᵖ νg) :=
      fun z ↦ ⟨z.proj.proj, z.snd⟩
    have hk : Continuous k := by
      rw [(inducing_pullbackTotalSpaceEmbedding Vg νg ic).continuous_iff]
      exact (p.continuous.comp (Pullback.continuous_proj Vg V s)).prodMk
        ((Pullback.continuous_lift Vg νg ψ).comp (Pullback.continuous_lift Vg V s))
    exact heis.continuous.comp hk
  have htop := ComplexBundle.complexificationTopology_pullback Vg V s
  let B := fun q : TP ↦ ℂ ⊗[ℝ] V q
  let D := (s : TM → TP) *ᵖ B
  let (z : TM) : AddCommGroup (D z) := by
    change AddCommGroup (ℂ ⊗[ℝ] V (Ti z)); infer_instance
  let (z : TM) : Module ℂ (D z) := by
    change Module ℂ (ℂ ⊗[ℝ] V (Ti z)); infer_instance
  let : TopologicalSpace (TotalSpace Unit D) :=
    Pullback.TotalSpace.topologicalSpace Unit B (s : TM → TP)
  let U : ComplexBundle.Iso (X := TM) (ComplexifiedNormalPullback f) D := {
    linearEquiv z := (L z).baseChange ℝ ℂ _ _
    continuous_total := by
      have hc := ComplexBundle.continuous_complexification_map
        (fun z ↦ (L z).toLinearMap) hL
      change @Continuous _ _ (ComplexBundle.complexificationTopology Vf W)
        (ComplexBundle.complexificationTopology Vg Z) _ at hc
      rw [htop] at hc
      exact hc
    continuous_symm := by
      have hc := ComplexBundle.continuous_complexification_map
        (fun z ↦ (L z).symm.toLinearMap) hLi
      change @Continuous _ _ (ComplexBundle.complexificationTopology Vg Z)
        (ComplexBundle.complexificationTopology Vf W) _ at hc
      rw [htop] at hc
      exact hc }
  exact ⟨U, fun _ _ ↦ rfl⟩

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationPullbackTransport
public import AtiyahSinger.Topology.TangentTubularBundleTransport

/-!
# The specified tubular transport in native real normal coordinates

Public module ID: M2244.

Pull the zero-normalized complex transport back by the inverse of the original
complexification/splitting homeomorphism. Its base maps are then exactly the
tangent embedding after projection and the original smooth real tubular map.
The same complex isomorphism gives a real-linear transport of doubled fibers,
continuous in both native directions and equal to the vector identity at zero.

This realizes the continuous coefficient in the actual nested tube construction.
The transport remains continuous; the original tubular base map is smooth.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold Topology
open scoped ContDiff TensorProduct

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [T2Space N] [SecondCountableTopology N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
  (V : Type*) (B : TangentBundle 𝓘(ℝ, F) N → Type*)
  [∀ z, AddCommGroup (B z)] [∀ z, Module ℝ (B z)]
  [TopologicalSpace (TotalSpace V B)]

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "νT" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "VT" => NormalModel (E × E) (F × F)
local notation "X" => TotalSpace VT νT

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in

/-- The actual complex transport and its real double have the original smooth tubular base map. -/
theorem exists_tangentTubular_real_transport (S : TangentNormalSplitting f hf) :
    letI := complexificationTopology V B
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
      (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VT νT)⟩
    let b := T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    IsFiniteRank (fun y ↦ ℂ ⊗[ℝ] B y) →
      ∃ e : Iso ((a : X → TN) *ᵖ (fun y ↦ ℂ ⊗[ℝ] B y))
          ((b : X → TN) *ᵖ (fun y ↦ ℂ ⊗[ℝ] B y)),
        ∃ R : ∀ x : X, (B (a x) × B (a x)) ≃ₗ[ℝ] (B (b x) × B (b x)),
          (∀ x w, R x w = complexificationReIm (B (b x))
            (e.linearEquiv x ((complexificationReIm (B (a x))).symm w))) ∧
          Continuous (fun z : TotalSpace (V × V) ((a : X → TN) *ᵖ (B ×ᵇ B)) ↦
            (⟨z.proj, R z.proj z.snd⟩ : TotalSpace (V × V) ((b : X → TN) *ᵖ (B ×ᵇ B)))) ∧
          Continuous (fun z : TotalSpace (V × V) ((b : X → TN) *ᵖ (B ×ᵇ B)) ↦
            (⟨z.proj, (R z.proj).symm z.snd⟩ :
              TotalSpace (V × V) ((a : X → TN) *ᵖ (B ×ᵇ B)))) ∧
          (∀ (z : TM) (v : ℂ ⊗[ℝ] B (a ⟨z, 0⟩)),
            HEq (e.linearEquiv ⟨z, 0⟩ v) v) ∧
          (∀ (z : TM) (w : B (a ⟨z, 0⟩) × B (a ⟨z, 0⟩)),
            HEq (R ⟨z, 0⟩ w) w) := by
  classical
  let := complexificationTopology V B
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
    (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VT νT)⟩
  let b := T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  dsimp only
  intro hfinite
  let : IsFiniteRank (fun y ↦ ℂ ⊗[ℝ] B y) := hfinite
  let D := fun y ↦ ℂ ⊗[ℝ] B y
  let XC := TotalSpace Unit (ComplexifiedNormalPullback f)
  let : IsFiniteRank (ComplexifiedNormalPullback f) :=
    isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let C := complexifiedNormalTotalHomeomorph f hf S
  let K : C(X, XC) := ⟨C.symm, C.symm.continuous⟩
  let q : C(XC, TM) := ⟨TotalSpace.proj, continuous_proj⟩
  let Tf : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
  let τ := tangentEmbeddingTubularMap f hf S T
  have hKzero (z : TM) : K ⟨z, 0⟩ = (⟨z, 0⟩ : XC) := by
    apply C.injective
    rw [show C (K ⟨z, 0⟩) = (⟨z, 0⟩ : X) from C.apply_symm_apply _]
    apply TotalSpace.ext
    · rfl
    · change HEq (0 : νT z)
        ((S.equiv z).symm (complexificationReIm
          (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) 0))
      simp only [map_zero]
      exact HEq.rfl
  -- Reindex the specified transport, keeping every actual fiber vector in the pullback comparisons.
  obtain ⟨ec, hec⟩ := exists_tangentTubular_pullback_iso f hf S T D
  let c := pullbackCompIso (E := D) Tf q
  let e₀ := c.symm.trans ec
  let ca := pullbackCompIso (E := D) (Tf.comp q) K
  let cb := pullbackCompIso (E := D) τ K
  let en := ca.symm.trans ((Iso.pullback K e₀).trans cb)
  have hc (x : XC) : c.linearEquiv x = LinearEquiv.refl ℂ (D (Tf (q x))) := by
    apply LinearEquiv.ext
    exact pullbackCompIso_apply Tf q x
  have hca (x : X) : ca.linearEquiv x =
      LinearEquiv.refl ℂ (D ((Tf.comp q) (K x))) := by
    apply LinearEquiv.ext
    exact pullbackCompIso_apply (Tf.comp q) K x
  have hcb (x : X) : cb.linearEquiv x = LinearEquiv.refl ℂ (D (τ (K x))) := by
    apply LinearEquiv.ext
    exact pullbackCompIso_apply τ K x
  have henzero (z : TM) (v : D (((Tf.comp q).comp K) ⟨z, 0⟩)) :
      HEq (en.linearEquiv ⟨z, 0⟩ v) v := by
    change HEq ((cb.linearEquiv ⟨z, 0⟩)
      (ec.linearEquiv (K ⟨z, 0⟩)
        ((c.linearEquiv (K ⟨z, 0⟩)).symm ((ca.linearEquiv ⟨z, 0⟩).symm v)))) v
    simp only [hcb, hc, hca]
    change HEq (ec.linearEquiv (K ⟨z, 0⟩) v) v
    revert v
    change ∀ v : D (Tf (q (K ⟨z, 0⟩))), HEq (ec.linearEquiv (K ⟨z, 0⟩) v) v
    rw [hKzero]
    exact hec z
  have ha : (Tf.comp q).comp K = a := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hb : τ.comp K = b := by
    apply ContinuousMap.ext
    intro z
    exact congrArg b (C.apply_symm_apply z)
  let P (a b : C(X, TN)) : Prop :=
    ∃ e : Iso ((a : X → TN) *ᵖ D) ((b : X → TN) *ᵖ D),
      ∀ (z : TM) (v : D (a ⟨z, 0⟩)), HEq (e.linearEquiv ⟨z, 0⟩ v) v
  have hP : P ((Tf.comp q).comp K) (τ.comp K) := ⟨en, henzero⟩
  rw [ha, hb] at hP
  obtain ⟨e, hezero⟩ := hP
  -- The same real/imaginary coordinates give joint continuity in both native real directions.
  obtain ⟨R, hR, hRc, hRic⟩ := exists_realDoublePullback_transport V B a b e
  refine ⟨e, R, hR, hRc, hRic, hezero, ?_⟩
  intro z w
  have hbase : b ⟨z, 0⟩ = a ⟨z, 0⟩ := T.map_zero z
  have hcoords {y y' : TN} (hy : y = y') (u : D y) (v : D y') (hu : HEq u v) :
      HEq (complexificationReIm (B y) u) (complexificationReIm (B y') v) := by
    subst y'
    cases hu
    rfl
  rw [hR]
  have h := hcoords hbase _ _ (hezero z ((complexificationReIm _).symm w))
  simpa only [LinearEquiv.apply_symm_apply] using h

end AtiyahSinger

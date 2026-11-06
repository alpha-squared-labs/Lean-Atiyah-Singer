/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleTransportCoordinates
public import AtiyahSinger.Topology.TangentTubularRealTransport

/-!
# The actual nested tangent tube in one native normal frame

Public module ID: M1487.

In a fixed original frame of the second doubled normal bundle, the nested
tubular map is a smooth geometric map preceded by the actual continuous
coefficient transport. The geometric map uses precisely the two original
tubes and the specified normalized splitting of the second tangent normal.
Both coefficient directions are continuous; identity of the original transport
on the zero section gives exact identity of those coefficients there.

This supplies the local factorization required by continuous-coefficient
rescaling. It does not promote the bundle transport itself to a smooth map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
  (Tf : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
  (Tg : TubularNeighborhood (smoothTangentMap g) (isImmersion_smoothTangentMap g hg))
  (Sg : TangentNormalSplitting g hg)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "TP" => TangentBundle 𝓘(ℝ, G) P
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "νTg" => NormalBundle 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) (smoothTangentMap g)
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTg" => NormalModel (F × F) (G × G)
local notation "Vg" => NormalModel F G
local notation "Bg" => (smoothTangentBundleProjection F N : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg
local notation "X" => TotalSpace VTf νTf

set_option maxSynthPendingDepth 50 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Native pullback and doubled-normal atlases are retained in the geometric factorization.
/-- The actual nested tube factors as smooth geometry after its continuous coefficients. -/
theorem exists_tangentNestedTube_factorization (y₀ : TN) :
    letI := normalBundleFiberBundle g hg.isImmersion
    letI := normalBundleVectorBundle g hg.isImmersion
    letI := normalBundleContMDiffVectorBundle g hg.isImmersion
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle
      (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleFiberBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
    letI := normalBundleVectorBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
    letI := normalBundleContMDiffVectorBundle
      (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
    let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
      (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
    let b := Tf.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    let e := trivializationAt Wg Dg y₀
    let Ψ : X × Wg → TP := fun p ↦
      Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
        ⟨b p.1, (Sg.equiv (b p.1)).symm (e.symm (b p.1) p.2)⟩
    ∀ R : ∀ x : X, Dg (a x) ≃ₗ[ℝ] Dg (b x),
      Continuous (fun z : TotalSpace Wg ((a : X → TN) *ᵖ Dg) ↦
        (⟨z.proj, R z.proj z.snd⟩ : TotalSpace Wg ((b : X → TN) *ᵖ Dg))) →
      Continuous (fun z : TotalSpace Wg ((b : X → TN) *ᵖ Dg) ↦
        (⟨z.proj, (R z.proj).symm z.snd⟩ : TotalSpace Wg ((a : X → TN) *ᵖ Dg))) →
      (∀ (z : TM) (v : Dg (a ⟨z, 0⟩)), HEq (R ⟨z, 0⟩ v) v) →
      ∃ A : X → Wg ≃L[ℝ] Wg,
        ContinuousOn (fun p : X × Wg ↦ A p.1 p.2)
          ((a ⁻¹' e.baseSet ∩ b ⁻¹' e.baseSet) ×ˢ univ) ∧
        ContinuousOn (fun p : X × Wg ↦ (A p.1).symm p.2)
          ((a ⁻¹' e.baseSet ∩ b ⁻¹' e.baseSet) ×ˢ univ) ∧
        ContMDiffOn ((𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)).prod 𝓘(ℝ, Wg))
          𝓘(ℝ, G × G) ∞ Ψ ((b ⁻¹' e.baseSet) ×ˢ univ) ∧
        (∀ (x : X), a x ∈ e.baseSet → b x ∈ e.baseSet → ∀ w : Wg,
          Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
            ⟨b x, (Sg.equiv (b x)).symm (R x (e.symm (a x) w))⟩ = Ψ (x, A x w)) ∧
        (∀ z : TM, a ⟨z, 0⟩ ∈ e.baseSet →
          A ⟨z, 0⟩ = ContinuousLinearEquiv.refl ℝ Wg) := by
  classical
  let := normalBundleFiberBundle g hg.isImmersion
  let := normalBundleVectorBundle g hg.isImmersion
  let := normalBundleContMDiffVectorBundle g hg.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let := normalBundleVectorBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
    (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
  let b := Tf.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let e := trivializationAt Wg Dg y₀
  let Ψ : X × Wg → TP := fun p ↦
    Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
      ⟨b p.1, (Sg.equiv (b p.1)).symm (e.symm (b p.1) p.2)⟩
  dsimp only
  intro R hR hRi hRzero
  have hRn : Continuous (fun z : TotalSpace Wg ((a : X → TN) *ᵖ Dg) ↦
      (⟨b z.proj, R z.proj z.snd⟩ : TotalSpace Wg Dg)) :=
    (Pullback.continuous_lift Wg Dg b).comp hR
  have hRin : Continuous (fun z : TotalSpace Wg ((b : X → TN) *ᵖ Dg) ↦
      (⟨a z.proj, (R z.proj).symm z.snd⟩ : TotalSpace Wg Dg)) :=
    (Pullback.continuous_lift Wg Dg a).comp hRi
  obtain ⟨A, hA, hAi, hformula, hzero⟩ := exists_bundleTransport_coefficients a b R hRn hRin e
  -- The smooth factor uses the same original second frame and the actual two tube maps.
  have hb : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) 𝓘(ℝ, F × F) ∞ b :=
    contMDiff_subtype_val.comp Tf.diffeomorph.contMDiff
  have hTg : ContMDiff (𝓘(ℝ, F × F).prod 𝓘(ℝ, VTg)) 𝓘(ℝ, G × G) ∞
      (Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)) :=
    contMDiff_subtype_val.comp Tg.diffeomorph.contMDiff
  have hframe : ContMDiffOn ((𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)).prod 𝓘(ℝ, Wg))
      (𝓘(ℝ, F × F).prod 𝓘(ℝ, Wg)) ∞
      (fun p : X × Wg ↦ (⟨b p.1, e.symm (b p.1) p.2⟩ : TotalSpace Wg Dg))
      ((b ⁻¹' e.baseSet) ×ˢ univ) := by
    have h : ContMDiffOn ((𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)).prod 𝓘(ℝ, Wg))
        (𝓘(ℝ, F × F).prod 𝓘(ℝ, Wg)) ∞
        (fun p : X × Wg ↦ e.toOpenPartialHomeomorph.symm (b p.1, p.2))
        ((b ⁻¹' e.baseSet) ×ˢ univ) := e.contMDiffOn_symm.comp
      ((hb.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      (fun p hp ↦ e.mem_target.mpr hp.1)
    apply h.congr
    intro p hp
    exact e.mk_symm hp.1 p.2
  have hΨ : ContMDiffOn ((𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)).prod 𝓘(ℝ, Wg))
      𝓘(ℝ, G × G) ∞ Ψ ((b ⁻¹' e.baseSet) ×ˢ univ) :=
    hTg.comp_contMDiffOn (Sg.contMDiff_invFun.comp_contMDiffOn hframe)
  refine ⟨A, hA, hAi, hΨ, ?_, ?_⟩
  · intro x ha hb w
    change Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
      ⟨b x, (Sg.equiv (b x)).symm (R x (e.symm (a x) w))⟩ = _
    rw [hformula x ha hb w]
  · -- Native zero normalization is transported through this same frame, without a new choice.
    intro z hz
    have hbzero : b ⟨z, 0⟩ = a ⟨z, 0⟩ := Tf.map_zero z
    apply hzero ⟨z, 0⟩ hz (hbzero.symm ▸ hz)
    intro v
    exact TotalSpace.ext hbzero (hRzero z v)

end AtiyahSinger

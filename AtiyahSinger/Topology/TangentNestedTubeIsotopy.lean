/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleRescalingCoordinates
public import AtiyahSinger.Geometry.BundleVaryingRadius
public import AtiyahSinger.Geometry.LocalCoefficientInverseRescaling
public import AtiyahSinger.Geometry.LocalCoefficientRescalingContinuity
public import AtiyahSinger.Geometry.NormalizedBundleReferenceDerivative
public import AtiyahSinger.Geometry.SmoothRiemannianMetric
public import AtiyahSinger.Geometry.TangentNestedTubeCoordinates
public import AtiyahSinger.Geometry.TangentNestedTubeReference
public import AtiyahSinger.Topology.BundleRescalingIsotopy
public import AtiyahSinger.Topology.OpenEmbeddingTransition

/-!
# Open isotopy from the reference composite tube to the actual nested tube

Public module ID: M2239.

The reference tube and the actual transported nested tube determine their
precise overlap. In each original normal product chart, the overlap is smooth
normalized geometry after the actual continuous coefficient shear. Both
rescalings are continuous, including the inverse of this same overlap.
Radial compression then extends the comparison to an open isotopy on the
whole original normal sum, fixed on its zero section.

The reference fiber comparison and its quotient-normal derivative are supplied
explicitly, so the same witnesses can be used in the complex-orientation path.
No smoothness is imposed on the actual coefficient transport.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff unitInterval

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
  [T2Space M] [SecondCountableTopology M]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
  (hgf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (g.comp f))
  (Tf : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
  (Tg : TubularNeighborhood (smoothTangentMap g) (isImmersion_smoothTangentMap g hg))
  (Tgf : TubularNeighborhood (smoothTangentMap (g.comp f))
    (isImmersion_smoothTangentMap (g.comp f) hgf))
  (Sg : TangentNormalSplitting g hg)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "TP" => TangentBundle 𝓘(ℝ, G) P
local notation "TfMap" => smoothTangentMap f
local notation "TgMap" => smoothTangentMap g
local notation "TgfMap" => smoothTangentMap (g.comp f)
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) TfMap
local notation "νTgf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TgfMap
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTgf" => NormalModel (E × E) (G × G)
local notation "Vg" => NormalModel F G
local notation "Bg" => (smoothTangentBundleProjection F N : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg
local notation "W" => VTf × Wg
local notation "Tfc" => (TfMap : TM → TN)
local notation "X" => TotalSpace VTf νTf
local notation "Rsum" => νTf ×ᵇ (Tfc *ᵖ Dg)
local notation "NB" => TotalSpace W Rsum
local notation "UC" => (E × E) × W
local notation "IR" => ModelWithCorners.prod 𝓘(ℝ, E × E) 𝓘(ℝ, W)
local notation "IN" => ModelWithCorners.prod 𝓘(ℝ, E × E) 𝓘(ℝ, VTgf)

set_option maxSynthPendingDepth 60 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option maxHeartbeats 6000000 in

/-- The specified normalized reference is openly isotopic to the actual nested tube. -/
theorem exists_tangentNestedTube_openIsotopy :
    letI := normalBundleFiberBundle g hg.isImmersion
    letI := normalBundleVectorBundle g hg.isImmersion
    letI := normalBundleContMDiffVectorBundle g hg.isImmersion
    letI := normalBundleFiberBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleFiberBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleContMDiffVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleFiberBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
    letI := normalBundleVectorBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
    letI := normalBundleContMDiffVectorBundle TgfMap
      (isImmersion_smoothTangentMap (g.comp f) hgf)
    let a : C(X, TN) := ⟨fun z ↦ TfMap z.proj,
      (TfMap).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
    let b := Tf.totalMap TfMap (isImmersion_smoothTangentMap f hf)
    ∀ (L : ∀ z : TM, Rsum z ≃L[ℝ] νTgf z)
      (Q : Diffeomorph IR IN NB (TotalSpace VTgf νTgf) ∞),
      (∀ z : NB, Q z = ⟨z.proj, L z.proj z.snd⟩) →
      (∀ z : TM,
        let ef := (trivializationAt VTf νTf z).continuousLinearEquivAt ℝ z
          (mem_baseSet_trivializationAt VTf νTf z)
        let er := (trivializationAt W Rsum z).continuousLinearEquivAt ℝ z
          (mem_baseSet_trivializationAt W Rsum z)
        let eg := trivializationAt Wg Dg (TfMap z)
        let φ : W → TP := fun p ↦
          Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
            ⟨b ⟨z, ef.symm p.1⟩, (Sg.equiv (b ⟨z, ef.symm p.1⟩)).symm
              (eg.symm (b ⟨z, ef.symm p.1⟩) p.2)⟩
        ∀ w : W,
          (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TgfMap z).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, G × G) φ 0
              ((NormedSpace.fromTangentSpace (0 : W)).symm w)) = L z (er.symm w)) →
      ∀ R : ∀ x : X, Dg (a x) ≃ₗ[ℝ] Dg (b x),
        Continuous (fun z : TotalSpace Wg ((a : X → TN) *ᵖ Dg) ↦
          (⟨z.proj, R z.proj z.snd⟩ : TotalSpace Wg ((b : X → TN) *ᵖ Dg))) →
        Continuous (fun z : TotalSpace Wg ((b : X → TN) *ᵖ Dg) ↦
          (⟨z.proj, (R z.proj).symm z.snd⟩ : TotalSpace Wg ((a : X → TN) *ᵖ Dg))) →
        (∀ (z : TM) (w : Dg (a ⟨z, 0⟩)), HEq (R ⟨z, 0⟩ w) w) →
        ∀ (NR : C(NB, TP)) (_hNR : IsOpenEmbedding NR),
          (∀ z : NB, NR z = Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
            ⟨b ⟨z.proj, z.snd.1⟩, (Sg.equiv (b ⟨z.proj, z.snd.1⟩)).symm
              (R ⟨z.proj, z.snd.1⟩ z.snd.2)⟩) →
          (∀ z : TM, NR ⟨z, 0⟩ = TgMap (TfMap z)) →
          let τ := (Tgf.totalMap TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)).comp
            ⟨Q, Q.contMDiff.continuous⟩
          ∃ H : ContinuousMap.Homotopy τ NR,
            IsOpenEmbedding (fun p : I × NB ↦ (p.1, H p)) ∧
              ∀ (t : I) (z : TM), H (t, ⟨z, 0⟩) = TgfMap z := by
  classical
  let := normalBundleFiberBundle g hg.isImmersion
  let := normalBundleVectorBundle g hg.isImmersion
  let := normalBundleContMDiffVectorBundle g hg.isImmersion
  let := normalBundleFiberBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleContMDiffVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleFiberBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleVectorBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleContMDiffVectorBundle TgfMap
    (isImmersion_smoothTangentMap (g.comp f) hgf)
  let a : C(X, TN) := ⟨fun z ↦ TfMap z.proj,
    (TfMap).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
  let b := Tf.totalMap TfMap (isImmersion_smoothTangentMap f hf)
  dsimp only
  intro L Q hQ hvertical R hR hRi hRzero NR hNR hNRformula hNRzero
  let τ : C(NB, TP) :=
    (Tgf.totalMap TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)).comp
      ⟨Q, Q.contMDiff.continuous⟩
  have hτ : IsOpenEmbedding τ :=
    (Tgf.target.isOpen.isOpenEmbedding_subtypeVal.comp
      Tgf.diffeomorph.toHomeomorph.isOpenEmbedding).comp Q.toHomeomorph.isOpenEmbedding
  have hcomp (z : TM) : TgMap (TfMap z) = TgfMap z :=
    (tangentMap_comp_at z (g.contMDiff.mdifferentiable (by simp) (f z.proj))
      (f.contMDiff.mdifferentiable (by simp) z.proj)).symm
  have hQzero (z : TM) : Q ⟨z, 0⟩ = ⟨z, 0⟩ := by
    rw [hQ, map_zero]
  have hτzero (z : TM) : τ ⟨z, 0⟩ = TgfMap z := by
    change Tgf.totalMap TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf) (Q ⟨z, 0⟩) = _
    rw [hQzero]
    exact Tgf.map_zero z
  -- The overlap is formed from the two actual open maps on the same native source.
  obtain ⟨e, _, _, hezero, hefix, hemap⟩ := exists_openEmbeddingTransition τ NR hτ hNR
    (fun z : TM ↦ (⟨z, 0⟩ : NB))
    (fun z ↦ (hτzero z).trans ((hNRzero z).trans (hcomp z)).symm)
  have hefixi (z : TM) : e.symm ⟨z, 0⟩ = ⟨z, 0⟩ := by
    simpa only [hefix z] using e.left_inv (hezero z)
  have hetarget (z : TM) : (⟨z, 0⟩ : NB) ∈ e.target := by
    simpa only [hefix z] using e.map_source (hezero z)
  have hrescale (x : TM) (v : Rsum x) :
      ContinuousAt (rescaleBundleMap e) (0, (⟨x, v⟩ : NB)) ∧
        ContinuousAt (rescaleBundleMap e.symm) (0, (⟨x, v⟩ : NB)) := by
    let z₀ : NB := ⟨x, 0⟩
    let κ := chartAt (E × E) x
    let x₀ := κ x
    let tr := trivializationAt W Rsum x
    have hxtr : x ∈ tr.baseSet := mem_baseSet_trivializationAt W Rsum x
    let c : OpenPartialHomeomorph NB UC :=
      { toPartialEquiv := extChartAt IR z₀
        open_source := isOpen_extChartAt_source z₀
        open_target := isOpen_extChartAt_target z₀
        continuousOn_toFun := continuousOn_extChartAt z₀
        continuousOn_invFun := continuousOn_extChartAt_symm z₀ }
    have hc₀ : z₀ ∈ c.source := mem_extChartAt_source z₀
    have hcvalue (u : Rsum x) : c ⟨x, u⟩ =
        (x₀, tr.continuousLinearEquivAt ℝ x hxtr u) := by
      change (extChartAt IR z₀) ⟨x, u⟩ = _
      rw [FiberBundle.extChartAt]
      exact congrArg (fun p : TM × W ↦ (κ p.1, p.2))
        (tr.apply_eq_prod_continuousLinearEquivAt ℝ x hxtr u)
    have hcpoint : c z₀ = (x₀, 0) := by simpa only [map_zero] using hcvalue 0
    have hcinv : c.symm (x₀, 0) = z₀ := hcpoint ▸ c.left_inv hc₀
    have hcbase : (x₀, (0 : W)) ∈ c.target := hcpoint ▸ c.map_source hc₀
    let cf := extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨x, 0⟩ : X)
    let eg := trivializationAt Wg Dg (TfMap x)
    let Ψ : UC → TP := fun p ↦
      Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
        ⟨b (cf.symm (p.1, p.2.1)), (Sg.equiv (b (cf.symm (p.1, p.2.1)))).symm
          (eg.symm (b (cf.symm (p.1, p.2.1))) p.2.2)⟩
    have hcoordinates := exists_tangentNestedTube_coordinateFactorization
      f g hf hg Tf Tg Sg x R hR hRi hRzero NR hNRformula
    rcases hcoordinates with ⟨A, S, hS, hA, hAi, hxS, hAzero, hΨ, hΨzero, hslice, hfactor⟩
    let C := continuousCoefficientShear A S hS hA hAi
    let U₀ : Set UC := {p | (p.1, p.2.1) ∈ S}
    have hU₀ : IsOpen U₀ := hS.preimage (continuous_fst.prodMk continuous_snd.fst)
    have hxU₀ : (x₀, (0 : W)) ∈ U₀ := hxS
    have hΨpoint : Ψ (x₀, 0) = TgfMap x := by
      have h := hΨzero x₀ hxS
      change Ψ (x₀, 0) = TgMap (TfMap (κ.symm x₀)) at h
      rw [show κ.symm x₀ = x from κ.left_inv (mem_chart_source (E × E) x)] at h
      exact h.trans (hcomp x)
    have hΨmem : Ψ (x₀, 0) ∈ Tgf.target := by
      rw [hΨpoint, ← Tgf.map_zero x]
      exact (Tgf.diffeomorph ⟨x, 0⟩).property
    -- Invert the actual reference tube only on its original open target.
    let Γ (p : UC) : NB := if hp : Ψ p ∈ Tgf.target then
      Q.symm (Tgf.diffeomorph.symm ⟨Ψ p, hp⟩) else z₀
    have hΓmap (p : UC) (hp : Ψ p ∈ Tgf.target) : τ (Γ p) = Ψ p := by
      dsimp only [Γ]
      rw [dite_eq_left hp]
      change Tgf.totalMap TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
        (Q (Q.symm (Tgf.diffeomorph.symm ⟨Ψ p, hp⟩))) = _
      rw [Q.apply_symm_apply]
      exact congrArg Subtype.val (Tgf.diffeomorph.apply_symm_apply ⟨Ψ p, hp⟩)
    have hΓzero : Γ (x₀, 0) = z₀ :=
      hτ.injective ((hΓmap (x₀, 0) hΨmem).trans (hΨpoint.trans (hτzero x).symm))
    let U₁ : Set UC := U₀ ∩ Ψ ⁻¹' Tgf.target
    have hU₁ : IsOpen U₁ := hΨ.continuousOn.isOpen_inter_preimage hU₀ Tgf.target.isOpen
    have hxU₁ : (x₀, (0 : W)) ∈ U₁ := ⟨hxU₀, hΨmem⟩
    have hΓ : ContMDiffOn 𝓘(ℝ, UC) IR ∞ Γ U₁ := by
      let O : TopologicalSpace.Opens UC := ⟨U₁, hU₁⟩
      let k : O → Tgf.target := fun p ↦ ⟨Ψ p, p.property.2⟩
      have hk : ContMDiff 𝓘(ℝ, UC) 𝓘(ℝ, G × G) ∞ k := by
        apply (ContMDiff.subtypeVal_comp_iff Tgf.target k).mp
        intro p
        exact ((hΨ p p.property.1).contMDiffAt
          (hU₀.mem_nhds p.property.1)).comp p (contMDiff_subtype_val.contMDiffAt)
      have hΓO : ContMDiff 𝓘(ℝ, UC) IR ∞ (fun p : O ↦ Γ p) := by
        have hh := Q.symm.contMDiff.comp (Tgf.diffeomorph.symm.contMDiff.comp hk)
        apply hh.congr
        intro p
        dsimp only [Γ]
        rw [dite_eq_left (show Ψ p ∈ Tgf.target from p.property.2)]
        rfl
      intro p hp
      exact (contMDiffAt_subtype_iff.mp (hΓO ⟨p, hp⟩)).contMDiffWithinAt
    let U : Set UC := (U₁ ∩ Γ ⁻¹' c.source) ∩ c.target
    have hU : IsOpen U :=
      (hΓ.continuousOn.isOpen_inter_preimage hU₁ c.open_source).inter c.open_target
    have hxU : (x₀, (0 : W)) ∈ U :=
      ⟨⟨hxU₁, by
        change Γ (x₀, 0) ∈ c.source
        rw [hΓzero]
        exact hc₀⟩, hcbase⟩
    let γ : UC → UC := c ∘ Γ
    have hcs : ContMDiffOn IR 𝓘(ℝ, UC) ∞ c c.source := by
      change ContMDiffOn IR 𝓘(ℝ, UC) ∞ (extChartAt IR z₀) (extChartAt IR z₀).source
      simpa only [extChartAt_source] using!
        (contMDiffOn_extChartAt («I» := IR) (x := z₀))
    have hγ : ContDiffOn ℝ ∞ γ U :=
      (hcs.comp (hΓ.mono (fun _ hp ↦ hp.1.1)) (fun _ hp ↦ hp.1.2)).contDiffOn
    have hczero (y : E × E) (hy : (y, (0 : W)) ∈ c.target) :
        c.symm (y, 0) = (⟨κ.symm y, 0⟩ : NB) := by
      have hytr : κ.symm y ∈ tr.baseSet := by
        change (y, (0 : W)) ∈ (extChartAt IR z₀).target at hy
        rw [FiberBundle.extChartAt_target] at hy
        exact hy.1.2
      change (extChartAt IR z₀).symm (y, 0) = _
      rw [FiberBundle.extChartAt]
      change tr.toOpenPartialHomeomorph.symm (κ.symm y, 0) = _
      rw [tr.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) _ hytr, map_zero]
    have hγzero (y : E × E) (hy : (y, (0 : W)) ∈ U) : γ (y, 0) = (y, 0) := by
      have hΓy : Γ (y, 0) = c.symm (y, 0) := by
        apply hτ.injective
        rw [hΓmap (y, 0) hy.1.1.2, hczero y hy.2, hτzero]
        exact (hΨzero y hy.1.1.1).trans (hcomp _)
      change c (Γ (y, 0)) = _
      rw [hΓy]
      exact c.right_inv hy.2
    have hΨnormal (w : W) :
        (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TgfMap x).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, G × G) (fun u ↦ Ψ (x₀, u)) 0
            ((NormedSpace.fromTangentSpace (0 : W)).symm w)) =
          L x ((tr.continuousLinearEquivAt ℝ x hxtr).symm w) := by
      have heq : (fun u : W ↦ Ψ (x₀, u)) =
          (fun p : W ↦ Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
            ⟨b ⟨x, ((trivializationAt VTf νTf x).continuousLinearEquivAt ℝ x
              (mem_baseSet_trivializationAt VTf νTf x)).symm p.1⟩,
              (Sg.equiv (b ⟨x, ((trivializationAt VTf νTf x).continuousLinearEquivAt ℝ x
                (mem_baseSet_trivializationAt VTf νTf x)).symm p.1⟩)).symm
                (eg.symm (b ⟨x, ((trivializationAt VTf νTf x).continuousLinearEquivAt ℝ x
                  (mem_baseSet_trivializationAt VTf νTf x)).symm p.1⟩) p.2)⟩) := by
        funext u
        exact hslice u.1 u.2
      rw [heq]
      exact hvertical x w
    have hnormal : (fderiv ℝ (fun p ↦ (γ p).2) (x₀, 0)).comp
        (ContinuousLinearMap.inr ℝ (E × E) W) = ContinuousLinearMap.id ℝ W :=
      fderiv_snd_eq_id_of_normalized_bundleReference TgfMap
        (isImmersion_smoothTangentMap (g.comp f) hgf) Tgf L Q hQ x Ψ Γ
        (hΨ.contMDiffAt (hU₀.mem_nhds hxU₀)) (hΓ.contMDiffAt (hU₁.mem_nhds hxU₁))
        hΓzero (by
          filter_upwards [hU₁.mem_nhds hxU₁] with p hp
          exact hΓmap p hp.2) hΨnormal
    -- Conjugate the actual overlap by this same chart; its local formula uses C.
    let ec := c.symm.trans (e.trans c)
    have hecsource : (x₀, (0 : W)) ∈ ec.source := by
      refine ⟨hcbase, ?_⟩
      change c.symm (x₀, 0) ∈ e.source ∧ e (c.symm (x₀, 0)) ∈ c.source
      rw [hcinv, hefix]
      exact ⟨hezero x, hc₀⟩
    have heczero : ec (x₀, 0) = (x₀, 0) := by
      change c (e (c.symm (x₀, 0))) = _
      rw [hcinv, hefix]
      exact hcpoint
    have hCsource : (x₀, (0 : W)) ∈ C.source := hxS
    have hCzero : C (x₀, 0) = (x₀, 0) := by
      change (x₀, (0 : VTf), A (x₀, 0) (0 : Wg)) = _
      rw [map_zero]
      rfl
    have hlocal : (ec : UC → UC) =ᶠ[𝓝 (x₀, (0 : W))] γ ∘ C := by
      have hnearE := (c.continuousAt_symm hcbase)
        (by
          rw [hcinv]
          exact e.open_source.mem_nhds (hezero x))
      have hnearΓ := (C.continuousAt hCsource)
        (hCzero.symm ▸ hU₁.mem_nhds hxU₁)
      filter_upwards [hU₀.mem_nhds hxU₀, hnearE, hnearΓ] with p hp hpe hpΓ
      have heq : e (c.symm p) = Γ (C p) := by
        apply hτ.injective
        rw [hemap (c.symm p) hpe, hΓmap (C p) hpΓ.2]
        exact hfactor p hp
      exact congrArg c heq
    let w := tr.continuousLinearEquivAt ℝ x hxtr v
    have hforward : ContinuousAt (rescaleAlongFibers ec) (0, x₀, w.1, w.2) := by
      have h := (continuousAt_rescaleAlongFibers_coefficient_comp A S hS hA hAi hAzero
        γ hγ hU hγzero x₀ w.1 w.2 hxS hxU hnormal).1
      exact h.congr_of_eventuallyEq
        (eventuallyEq_rescaleAlongFibers_zero ec (γ ∘ C) x₀ w hlocal)
    have hinverse := continuousAt_rescaleAlongFibers_symm_of_coefficient
      A S hS hA hAi hAzero ec γ hγ hU hγzero x₀ w.1 w.2 hxS hxU
      hecsource heczero hlocal hnormal
    -- Dilation commutes with this actual bundle chart, so both coordinate limits are native.
    have hsrc (t : ℝ) (z : NB) : bundleFiberScale t z ∈ c.source ↔ z ∈ c.source := by
      change _ ∈ (extChartAt IR z₀).source ↔ _ ∈ (extChartAt IR z₀).source
      simp only [extChartAt_source, FiberBundle.chartedSpace_chartAt,
        OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
        OpenPartialHomeomorph.refl_source, mem_inter_iff, mem_preimage, mem_prod,
        mem_univ, and_true, Trivialization.mem_source]
      change ((bundleFiberScale t z).proj ∈ tr.baseSet ∧
        (tr (bundleFiberScale t z)).1 ∈ κ.source) ↔
          (z.proj ∈ tr.baseSet ∧ (tr z).1 ∈ κ.source)
      by_cases hz : z.proj ∈ tr.baseSet
      · rw [tr.coe_fst' (show (bundleFiberScale t z).proj ∈ tr.baseSet from hz), tr.coe_fst' hz]
        rfl
      · simp [bundleFiberScale, hz]
    have hscale (t : ℝ) (z : NB) (hz : z ∈ c.source) :
        c (bundleFiberScale t z) = ((c z).1, t • (c z).2) := by
      have hztr : z.proj ∈ tr.baseSet := by
        change z ∈ (extChartAt IR z₀).source at hz
        rw [extChartAt_source, FiberBundle.chartedSpace_chartAt] at hz
        exact tr.mem_source.mp hz.1
      change extChartAt IR z₀ _ = ((extChartAt IR z₀ z).1, t • (extChartAt IR z₀ z).2)
      simp only [FiberBundle.extChartAt, PartialEquiv.trans_apply, PartialEquiv.prod_coe,
        PartialEquiv.refl_coe, id_eq]
      change ((extChartAt 𝓘(ℝ, E × E) x) (tr (bundleFiberScale t z)).1,
          (tr (bundleFiberScale t z)).2) =
        ((extChartAt 𝓘(ℝ, E × E) x) (tr z).1, t • (tr z).2)
      rw [tr.coe_fst' (show (bundleFiberScale t z).proj ∈ tr.baseSet from hztr), tr.coe_fst' hztr]
      apply Prod.ext
      · rfl
      · change (tr ⟨z.proj, t • z.snd⟩).2 = t • (tr z).2
        simp only [← tr.continuousLinearMapAt_apply_of_mem ℝ hztr, map_smul]
    constructor
    · apply continuousAt_rescaleBundleMap_of_chart e c hsrc hscale x v hc₀
        (e.continuousAt (hezero x)) (hefix x)
      rw [hcvalue v]
      exact hforward
    · apply continuousAt_rescaleBundleMap_of_chart e.symm c hsrc hscale x v hc₀
        (e.continuousAt_symm (hetarget x)) (hefixi x)
      rw [hcvalue v]
      exact hinverse
  have hfull (k : NB → NB) (U : Set NB) (hU : IsOpen U) (hk : ContinuousOn k U)
      (hzero : ∀ x : TM, ∀ v : Rsum x,
        ContinuousAt (rescaleBundleMap k) (0, (⟨x, v⟩ : NB))) :
      ContinuousOn (rescaleBundleMap k) {p | bundleFiberScale p.1 p.2 ∈ U} := by
    intro p hp
    by_cases ht : p.1 = 0
    · rcases p with ⟨t, x, v⟩
      change t = 0 at ht
      subst t
      exact (hzero x v).continuousWithinAt
    · have hvalue : ContinuousAt (fun p : ℝ × NB ↦ k (bundleFiberScale p.1 p.2)) p :=
        (hk.continuousAt (hU.mem_nhds hp)).comp_of_eq
          continuous_bundleFiberScale_of_vectorBundle.continuousAt rfl
      have h := continuous_bundleFiberScale_of_vectorBundle.continuousAt.comp_of_eq
        ((continuous_fst.continuousAt.inv₀ ht).prodMk hvalue) rfl
      apply ContinuousAt.continuousWithinAt
      apply h.congr_of_eventuallyEq
      filter_upwards [continuous_fst.continuousAt (isOpen_ne.mem_nhds ht)] with q hq
      change q.1 ≠ 0 at hq
      simp only [rescaleBundleMap, hq, ↓reduceIte]
      rfl
  -- A positive varying disk in the same overlap supplies whole-total radial compression.
  let : T2Space TM := (tangentBundle_topology E M).1
  let : ParacompactSpace TM := (tangentBundle_topology E M).2.2
  -- Expose the existing quotient-fiber topology through both native pullbacks.
  let (x : TM) : IsTopologicalAddGroup (Rsum x) := by
    change IsTopologicalAddGroup
      (νTf x × (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g (TfMap x).proj ×
        NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g (TfMap x).proj))
    infer_instance
  let (x : TM) : ContinuousConstSMul ℝ (Rsum x) := by
    change ContinuousConstSMul ℝ
      (νTf x × (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g (TfMap x).proj ×
        NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g (TfMap x).proj))
    infer_instance
  let m := smoothRiemannianMetric (EB := E × E) W Rsum
  let : RiemannianBundle Rsum := ⟨m.toRiemannianMetric⟩
  -- Derive both the norm and inner product from this metric on the original topology.
  let (x : TM) : NormedAddCommGroup (Rsum x) :=
    (m.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
      (m.toRiemannianMetric.continuousAt x) (m.toRiemannianMetric.isVonNBounded x)
  let (x : TM) : InnerProductSpace ℝ (Rsum x) :=
    .ofCoreOfTopology (m.toRiemannianMetric.toCore x)
      (m.toRiemannianMetric.continuousAt x) (m.toRiemannianMetric.isVonNBounded x)
  let : IsContinuousRiemannianBundle W Rsum :=
    ⟨⟨m.inner, m.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, E × E) ∞ W Rsum :=
    ⟨m.inner, m.contMDiff, fun _ _ _ ↦ rfl⟩
  obtain ⟨ε, hεpos, hεsub⟩ :=
    exists_contMDiff_radius_subset (EB := E × E) e.open_source hezero
  let q (z : NB) : ℝ := inner ℝ z.snd z.snd / (ε z.proj) ^ 2
  have hq : ContMDiff IR 𝓘(ℝ) ∞ q := by
    have hi : ContMDiff IR 𝓘(ℝ) ∞ (fun z : NB ↦ inner ℝ z.snd z.snd) :=
      contMDiff_id.inner_bundle contMDiff_id
    exact hi.mul (((ε.contMDiff.comp (contMDiff_proj Rsum)).pow 2).inv₀
      (fun z ↦ pow_ne_zero 2 (hεpos z.proj).ne'))
  have hqnonneg (z : NB) : 0 ≤ q z := div_nonneg real_inner_self_nonneg (sq_nonneg _)
  have hquad (t : ℝ) (z : NB) : q ⟨z.proj, t • z.snd⟩ = t ^ 2 * q z := by
    simp only [q, real_inner_smul_left, real_inner_smul_right]
    ring
  have hqsub (z : NB) (hz : q z < 1) : z ∈ e.source := by
    apply hεsub z.proj z.snd
    have h := (div_lt_one (sq_pos_of_pos (hεpos z.proj))).mp hz
    rw [real_inner_self_eq_norm_sq] at h
    exact (sq_lt_sq₀ (norm_nonneg z.snd) (hεpos z.proj).le).mp h
  obtain ⟨H, hH, hzero⟩ := exists_openIsotopy_of_rescaling τ NR hτ hNR e
    hezero hefix hemap (hfull e e.source e.open_source e.continuousOn (fun x v ↦ (hrescale x v).1))
    (hfull e.symm e.target e.open_target e.continuousOn_symm (fun x v ↦ (hrescale x v).2))
    q hq.continuous hqnonneg hquad hqsub
  exact ⟨H, hH, fun t z ↦ (hzero t z).trans (hτzero z)⟩

end AtiyahSinger

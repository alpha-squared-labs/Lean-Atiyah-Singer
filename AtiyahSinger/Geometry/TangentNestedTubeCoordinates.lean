/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ContinuousCoefficientRescaling
public import AtiyahSinger.Geometry.TangentNestedTubeFactorization

/-!
# The actual nested tube in the original product chart

Public module ID: M1485.

The native local factorization of the nested tube becomes a continuous
coefficient shear followed by smooth geometry in the selected original bundle
chart. The chart is the actual product of the first normal frame and the
pulled-back second doubled-normal frame. Both coefficient directions remain
continuous and the coefficients equal identity along the zero section.

The supplied nested map is identified by its actual vector formula. This
connects the supported nested construction to Euclidean rescaling without
assuming that the original transport is smooth.
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
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "Vg" => NormalModel F G
local notation "Bg" => (smoothTangentBundleProjection F N : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg
local notation "Tfc" => (smoothTangentMap f : TM → TN)
local notation "X" => TotalSpace VTf νTf
local notation "Rsum" => νTf ×ᵇ (Tfc *ᵖ Dg)
local notation "UCoord" => (E × E) × (VTf × Wg)

set_option maxSynthPendingDepth 50 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- The selected native sum chart is used on both sides of the exact factorization.
/-- The actual nested tube is smooth geometry after the same continuous coefficient shear. -/
theorem exists_tangentNestedTube_coordinateFactorization (z₀ : TM) :
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
    let c := extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
      (⟨z₀, 0⟩ : TotalSpace (VTf × Wg) Rsum)
    let cf := extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨z₀, 0⟩ : X)
    let eg := trivializationAt Wg Dg (smoothTangentMap f z₀)
    let Ψ : UCoord → TP := fun p ↦
      Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
        ⟨b (cf.symm (p.1, p.2.1)), (Sg.equiv (b (cf.symm (p.1, p.2.1)))).symm
          (eg.symm (b (cf.symm (p.1, p.2.1))) p.2.2)⟩
    ∀ R : ∀ x : X, Dg (a x) ≃ₗ[ℝ] Dg (b x),
      Continuous (fun z : TotalSpace Wg ((a : X → TN) *ᵖ Dg) ↦
        (⟨z.proj, R z.proj z.snd⟩ : TotalSpace Wg ((b : X → TN) *ᵖ Dg))) →
      Continuous (fun z : TotalSpace Wg ((b : X → TN) *ᵖ Dg) ↦
        (⟨z.proj, (R z.proj).symm z.snd⟩ : TotalSpace Wg ((a : X → TN) *ᵖ Dg))) →
      (∀ (z : TM) (w : Dg (a ⟨z, 0⟩)), HEq (R ⟨z, 0⟩ w) w) →
      ∀ N : TotalSpace (VTf × Wg) Rsum → TP,
        (∀ z, N z = Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
          ⟨b ⟨z.proj, z.snd.1⟩, (Sg.equiv (b ⟨z.proj, z.snd.1⟩)).symm
            (R ⟨z.proj, z.snd.1⟩ z.snd.2)⟩) →
        ∃ A : (E × E) × VTf → Wg ≃L[ℝ] Wg,
          ∃ S : Set ((E × E) × VTf), ∃ hS : IsOpen S,
            ∃ hA : ContinuousOn (fun p : ((E × E) × VTf) × Wg ↦ A p.1 p.2) (S ×ˢ univ),
              ∃ hAi : ContinuousOn (fun p : ((E × E) × VTf) × Wg ↦
                  (A p.1).symm p.2) (S ×ˢ univ),
                ((chartAt (E × E) z₀ z₀), 0) ∈ S ∧
                (∀ x : E × E, (x, (0 : VTf)) ∈ S →
                  A (x, 0) = ContinuousLinearEquiv.refl ℝ Wg) ∧
                ContMDiffOn 𝓘(ℝ, UCoord) 𝓘(ℝ, G × G) ∞ Ψ
                  {p | (p.1, p.2.1) ∈ S} ∧
                (∀ x : E × E, (x, (0 : VTf)) ∈ S →
                  Ψ (x, 0) = smoothTangentMap g
                    (smoothTangentMap f ((chartAt (E × E) z₀).symm x))) ∧
                (let ef := (trivializationAt VTf νTf z₀).continuousLinearEquivAt ℝ z₀
                   (mem_baseSet_trivializationAt VTf νTf z₀)
                 ∀ (v : VTf) (w : Wg), Ψ (chartAt (E × E) z₀ z₀, v, w) =
                   Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
                     ⟨b ⟨z₀, ef.symm v⟩, (Sg.equiv (b ⟨z₀, ef.symm v⟩)).symm
                       (eg.symm (b ⟨z₀, ef.symm v⟩) w)⟩) ∧
                (∀ p : UCoord, (p.1, p.2.1) ∈ S →
                  N (c.symm p) = Ψ (continuousCoefficientShear A S hS hA hAi p)) := by
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
  let c := extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf × Wg))
    (⟨z₀, 0⟩ : TotalSpace (VTf × Wg) Rsum)
  let cf : OpenPartialHomeomorph X ((E × E) × VTf) :=
    { toPartialEquiv := extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨z₀, 0⟩ : X)
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _ }
  let eg := trivializationAt Wg Dg (smoothTangentMap f z₀)
  let Ψ₀ : X × Wg → TP := fun p ↦
    Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
      ⟨b p.1, (Sg.equiv (b p.1)).symm (eg.symm (b p.1) p.2)⟩
  let Ψ : UCoord → TP := fun p ↦ Ψ₀ (cf.symm (p.1, p.2.1), p.2.2)
  dsimp only
  intro R hR hRi hRzero N hN
  have hfactor := exists_tangentNestedTube_factorization f g hf hg Tf Tg Sg
    (smoothTangentMap f z₀) R hR hRi hRzero
  rcases hfactor with ⟨An, hAn, hAni, hΨ₀, hformula, hzero⟩
  let O : Set X := a ⁻¹' eg.baseSet ∩ b ⁻¹' eg.baseSet
  have hO : IsOpen O :=
    (eg.open_baseSet.preimage a.continuous).inter (eg.open_baseSet.preimage b.continuous)
  let S : Set ((E × E) × VTf) := cf.target ∩ cf.symm ⁻¹' O
  have hS : IsOpen S := cf.symm.isOpen_inter_preimage hO
  let A : (E × E) × VTf → Wg ≃L[ℝ] Wg := fun p ↦ An (cf.symm p)
  have hA : ContinuousOn (fun p : ((E × E) × VTf) × Wg ↦ A p.1 p.2) (S ×ˢ univ) :=
    hAn.comp ((cf.continuousOn_symm.mono (fun _ hp ↦ hp.1)).prodMap continuousOn_id)
      (fun p hp ↦ ⟨hp.1.2, hp.2⟩)
  have hAi : ContinuousOn (fun p : ((E × E) × VTf) × Wg ↦
      (A p.1).symm p.2) (S ×ˢ univ) :=
    hAni.comp ((cf.continuousOn_symm.mono (fun _ hp ↦ hp.1)).prodMap continuousOn_id)
      (fun p hp ↦ ⟨hp.1.2, hp.2⟩)
  let κ := chartAt (E × E) z₀
  let ef := trivializationAt VTf νTf z₀
  have hcfpoint : cf ⟨z₀, 0⟩ = (κ z₀, 0) := by
    change extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨z₀, 0⟩ : X) ⟨z₀, 0⟩ = _
    rw [FiberBundle.extChartAt]
    change (κ (ef ⟨z₀, 0⟩).1, (ef ⟨z₀, 0⟩).2) = _
    rw [ef.apply_eq_prod_continuousLinearEquivAt ℝ z₀
      (mem_baseSet_trivializationAt VTf νTf z₀), map_zero]
  have hcfzero : cf.symm (κ z₀, 0) = (⟨z₀, 0⟩ : X) := by
    rw [← hcfpoint]
    exact cf.left_inv (mem_extChartAt_source _)
  have hmem : (κ z₀, (0 : VTf)) ∈ S := by
    refine ⟨hcfpoint ▸ cf.map_source (mem_extChartAt_source _), ?_⟩
    change cf.symm (κ z₀, 0) ∈ O
    rw [hcfzero]
    refine ⟨mem_baseSet_trivializationAt Wg Dg (smoothTangentMap f z₀), ?_⟩
    change b ⟨z₀, 0⟩ ∈ eg.baseSet
    rw [show b ⟨z₀, 0⟩ = smoothTangentMap f z₀ from Tf.map_zero z₀]
    exact mem_baseSet_trivializationAt Wg Dg (smoothTangentMap f z₀)
  -- The inverse of the native first chart retains its base and original frame vector.
  have hinverse (p : (E × E) × VTf) (hp : p ∈ cf.target) :
      cf.symm p = (⟨κ.symm p.1, ef.symm (κ.symm p.1) p.2⟩ : X) := by
    have hp' : κ.symm p.1 ∈ ef.baseSet := by
      change p ∈ (extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨z₀, 0⟩ : X)).target at hp
      rw [FiberBundle.extChartAt_target] at hp
      exact hp.1.2
    change (extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨z₀, 0⟩ : X)).symm p = _
    rw [FiberBundle.extChartAt]
    exact (ef.mk_symm hp' p.2).symm
  have hizero (x : E × E) (hx : (x, (0 : VTf)) ∈ cf.target) :
      cf.symm (x, 0) = (⟨κ.symm x, 0⟩ : X) := by
    have hix := hinverse (x, 0) hx
    have hxbase : κ.symm x ∈ ef.baseSet := by
      have hp := hx
      change (x, (0 : VTf)) ∈
        (extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨z₀, 0⟩ : X)).target at hp
      rw [FiberBundle.extChartAt_target] at hp
      exact hp.1.2
    rw [hix, ← ef.symmL_apply (R := ℝ) hxbase, map_zero]
  have hAzero (x : E × E) (hx : (x, (0 : VTf)) ∈ S) :
      A (x, 0) = ContinuousLinearEquiv.refl ℝ Wg := by
    change An (cf.symm (x, 0)) = _
    rw [hizero x hx.1]
    apply hzero
    exact hizero x hx.1 ▸ hx.2.1
  have hci : ContMDiffOn 𝓘(ℝ, (E × E) × VTf)
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) ∞ cf.symm cf.target :=
    contMDiffOn_extChartAt_symm (⟨z₀, 0⟩ : X)
  have hΨ : ContMDiffOn 𝓘(ℝ, UCoord) 𝓘(ℝ, G × G) ∞ Ψ
      {p | (p.1, p.2.1) ∈ S} := by
    have hpair : ContMDiff 𝓘(ℝ, UCoord) 𝓘(ℝ, (E × E) × VTf) ∞
        (fun p : UCoord ↦ (p.1, p.2.1)) :=
      (contDiff_fst.prodMk contDiff_snd.fst).contMDiff
    have hthird : ContMDiff 𝓘(ℝ, UCoord) 𝓘(ℝ, Wg) ∞ (fun p : UCoord ↦ p.2.2) :=
      contDiff_snd.snd.contMDiff
    have hinput := (hci.comp hpair.contMDiffOn
      (fun p (hp : (p.1, p.2.1) ∈ S) ↦ hp.1)).prodMk hthird.contMDiffOn
    exact hΨ₀.comp hinput (fun p hp ↦ ⟨hp.2.2, mem_univ _⟩)
  have hΨzero (x : E × E) (hx : (x, (0 : VTf)) ∈ S) :
      Ψ (x, 0) = smoothTangentMap g (smoothTangentMap f (κ.symm x)) := by
    have hbframe : b (cf.symm (x, 0)) ∈ eg.baseSet := hx.2.2
    change Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
      ⟨b (cf.symm (x, 0)), (Sg.equiv (b (cf.symm (x, 0)))).symm
        (eg.symm (b (cf.symm (x, 0))) 0)⟩ = _
    rw [← eg.symmL_apply (R := ℝ) hbframe, map_zero, map_zero]
    calc
      _ = smoothTangentMap g (b (cf.symm (x, 0))) := Tg.map_zero _
      _ = smoothTangentMap g (b ⟨κ.symm x, 0⟩) :=
        congrArg (fun y : X ↦ smoothTangentMap g (b y)) (hizero x hx.1)
      _ = _ := congrArg (smoothTangentMap g) (Tf.map_zero (κ.symm x))
  have hvertical (v : VTf) : cf.symm (κ z₀, v) =
      (⟨z₀, (ef.continuousLinearEquivAt ℝ z₀
        (mem_baseSet_trivializationAt VTf νTf z₀)).symm v⟩ : X) := by
    change (extChartAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (⟨z₀, 0⟩ : X)).symm (κ z₀, v) = _
    rw [FiberBundle.extChartAt]
    change ef.toOpenPartialHomeomorph.symm (κ.symm (κ z₀), v) = _
    rw [κ.left_inv (mem_chart_source (E × E) z₀)]
    exact ef.symm_apply_eq_mk_continuousLinearEquivAt_symm z₀
      (mem_baseSet_trivializationAt VTf νTf z₀) v
  refine ⟨A, S, hS, hA, hAi, hmem, hAzero, hΨ, hΨzero, ?_, ?_⟩
  · intro v w
    exact congrArg (fun y : X ↦ Ψ₀ (y, w)) (hvertical v)
  intro p hp
  have hin : c.symm p =
      (⟨(cf.symm (p.1, p.2.1)).proj,
        ((cf.symm (p.1, p.2.1)).snd,
          eg.symm (a (cf.symm (p.1, p.2.1))) p.2.2)⟩ :
        TotalSpace (VTf × Wg) Rsum) := by
    rw [hinverse (p.1, p.2.1) hp.1]
    dsimp only [c]
    rw [FiberBundle.extChartAt]
    change (ef.prod (eg.pullback (smoothTangentMap f))).toPartialEquiv.symm
      (κ.symm p.1, p.2.1, p.2.2) = _
    rw [Trivialization.prod_symm_apply]
    have hgbase : smoothTangentMap f (κ.symm p.1) ∈ eg.baseSet := by
      have h := hp.2.1
      rw [hinverse (p.1, p.2.1) hp.1] at h
      exact h
    have hpull : (eg.pullback (smoothTangentMap f)).symm (κ.symm p.1) p.2.2 =
        eg.symm (smoothTangentMap f (κ.symm p.1)) p.2.2 := by
      have h := (eg.pullback (smoothTangentMap f)).mk_symm hgbase p.2.2
      exact eq_of_heq (congr_arg_heq
        (fun y : TotalSpace Wg (Tfc *ᵖ Dg) ↦ y.snd) h)
    rw [hpull]
    rfl
  -- This is the exact supplied nested map, with no differentiability imposed on R.
  rw [hin, hN]
  exact hformula (cf.symm (p.1, p.2.1)) hp.2.1 hp.2.2 p.2.2

end AtiyahSinger

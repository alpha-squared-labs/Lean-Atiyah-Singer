/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalEmbeddingComposition
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Geometry.TubularNormalLift

/-!
# The actual normal derivative of nested tangent tubes

Public module ID: M1486.

The two partial derivatives of the smooth nested geometric map are the first
normal lift followed by the derivative of the second embedding, and the actual
second normal lift. The original quotient therefore identifies their sum with
the inverse of the splitting constructed from that same second tube. This
compares the precise derivative needed by the local rescaling argument; no
smoothness of continuous bundle transport is asserted.

Source: the chain-rule argument in the SG III.12 tubular composition proof,
with the original normal representatives and the same supplied tube witnesses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
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
local notation "TfMap" => smoothTangentMap f
local notation "TgMap" => smoothTangentMap g
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) TfMap
local notation "νTg" => NormalBundle 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) TgMap
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTg" => NormalModel (F × F) (G × G)
local notation "Vg" => NormalModel F G
local notation "Bg" => (smoothTangentBundleProjection F N : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg

set_option maxSynthPendingDepth 50 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option maxHeartbeats 1600000 in
-- The partial derivatives keep the same original quotient and iterated bundle frames.
/-- The actual nested derivative induces the splitting determined by the second tube. -/
theorem exists_tangentNestedTube_normalDerivative
    (hTC : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ ((TgMap).comp TfMap)) :
    letI := normalBundleFiberBundle g hg.isImmersion
    letI := normalBundleVectorBundle g hg.isImmersion
    letI := normalBundleContMDiffVectorBundle g hg.isImmersion
    letI := normalBundleFiberBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
    letI := normalBundleFiberBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    letI := normalBundleContMDiffVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
    ∃ ST : NormalEmbeddingCompositionSplitting TfMap TgMap
        (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg) hTC,
      ∀ z : TM,
        let ef := (trivializationAt VTf νTf z).continuousLinearEquivAt ℝ z
          (mem_baseSet_trivializationAt VTf νTf z)
        let eg := trivializationAt Wg Dg (TfMap z)
        let b : VTf → TN := fun v ↦
          Tf.totalMap TfMap (isImmersion_smoothTangentMap f hf) ⟨z, ef.symm v⟩
        let φ : VTf × Wg → TP := fun p ↦
          Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
            ⟨b p.1, (Sg.equiv (b p.1)).symm (eg.symm (b p.1) p.2)⟩
        ∀ (v : VTf) (w : Wg),
          (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G)
            ((TgMap).comp TfMap) z).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, VTf × Wg) 𝓘(ℝ, G × G) φ 0
              ((NormedSpace.fromTangentSpace (0 : VTf × Wg)).symm (v, w))) =
            (ST.equiv z).symm
              (ef.symm v, (Sg.equiv (TfMap z)).symm (eg.symm (TfMap z) w)) := by
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
  -- Select the right inverse by differentiating the actual second tube itself.
  obtain ⟨Jg, hJgq, hJgs, hJg⟩ := Tg.exists_normalLift TgMap
    (isImmersion_smoothTangentMap g hg)
  obtain ⟨ST, hST⟩ := exists_normalEmbeddingCompositionSplitting_of_rightInverse
    TfMap TgMap (isImmersion_smoothTangentMap f hf)
    (isImmersion_smoothTangentMap g hg) hTC Jg hJgs hJgq
  refine ⟨ST, ?_⟩
  intro z
  let ef := (trivializationAt VTf νTf z).continuousLinearEquivAt ℝ z
    (mem_baseSet_trivializationAt VTf νTf z)
  let eg := trivializationAt Wg Dg (TfMap z)
  let b : VTf → TN := fun v ↦
    Tf.totalMap TfMap (isImmersion_smoothTangentMap f hf) ⟨z, ef.symm v⟩
  let φ : VTf × Wg → TP := fun p ↦
    Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
      ⟨b p.1, (Sg.equiv (b p.1)).symm (eg.symm (b p.1) p.2)⟩
  change ∀ v w, _ = (ST.equiv z).symm
    (ef.symm v, (Sg.equiv (TfMap z)).symm (eg.symm (TfMap z) w))
  have hbzero : b 0 = TfMap z := by
    change Tf.totalMap TfMap (isImmersion_smoothTangentMap f hf) ⟨z, ef.symm 0⟩ = _
    rw [map_zero]
    exact Tf.map_zero z
  have hegz : TfMap z ∈ eg.baseSet := mem_baseSet_trivializationAt Wg Dg (TfMap z)
  have hTg : ContMDiff (𝓘(ℝ, F × F).prod 𝓘(ℝ, VTg)) 𝓘(ℝ, G × G) ∞
      (Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)) :=
    contMDiff_subtype_val.comp Tg.diffeomorph.contMDiff
  have hb : ContMDiff 𝓘(ℝ, VTf) 𝓘(ℝ, F × F) ∞ b := by
    apply (contMDiff_subtype_val.comp Tf.diffeomorph.contMDiff).comp
    intro v
    let e := trivializationAt VTf νTf z
    have hz : z ∈ e.baseSet := mem_baseSet_trivializationAt VTf νTf z
    rw [e.contMDiffAt_iff (e.mem_source.mpr hz)]
    refine ⟨contMDiffAt_const, ?_⟩
    apply contMDiffAt_id.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro w
    change (e ⟨z, ef.symm w⟩).2 = w
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ z hz]
    exact ef.apply_symm_apply w
  -- The fixed second frame is used only on its open domain around the zero point.
  let O : Set (VTf × Wg) := (b ⁻¹' eg.baseSet) ×ˢ univ
  have hO : IsOpen O := (eg.open_baseSet.preimage hb.continuous).prod isOpen_univ
  have hzeroO : (0 : VTf × Wg) ∈ O := by
    refine ⟨?_, Set.mem_univ _⟩
    change b 0 ∈ eg.baseSet
    rw [hbzero]
    exact hegz
  have hframe : ContMDiffOn (𝓘(ℝ, VTf).prod 𝓘(ℝ, Wg))
      (𝓘(ℝ, F × F).prod 𝓘(ℝ, Wg)) ∞
      (fun p : VTf × Wg ↦ (⟨b p.1, eg.symm (b p.1) p.2⟩ : TotalSpace Wg Dg)) O := by
    have h := eg.contMDiffOn_symm.comp
      ((hb.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      (fun p (hp : p ∈ O) ↦ eg.mem_target.mpr hp.1)
    apply h.congr
    intro p hp
    exact eg.mk_symm hp.1 p.2
  have hφ : MDifferentiableAt (𝓘(ℝ, VTf).prod 𝓘(ℝ, Wg)) 𝓘(ℝ, G × G) φ 0 :=
    ((hTg.comp_contMDiffOn (Sg.contMDiff_invFun.comp_contMDiffOn hframe)).contMDiffAt
      (hO.mem_nhds hzeroO)).mdifferentiableAt (by simp)
  -- The first partial is the actual first tube followed by the second tangent map.
  have hfirst : (fun v : VTf ↦ φ (v, 0)) =ᶠ[𝓝 0] (TgMap ∘ b) := by
    filter_upwards [hb.continuous.continuousAt
      (eg.open_baseSet.mem_nhds (hbzero ▸ hegz))] with v hv
    change Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
      ⟨b v, (Sg.equiv (b v)).symm (eg.symm (b v) 0)⟩ = TgMap (b v)
    rw [← eg.symmL_apply (R := ℝ) hv, map_zero, map_zero]
    exact Tg.map_zero (b v)
  have hfirstD : (mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, G × G) (fun v ↦ φ (v, 0)) 0 :
      VTf →L[ℝ] (G × G)) =
      (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) TgMap (TfMap z)).comp
        (mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, F × F) b 0) := by
    have he := hfirst.mfderiv_eq (I := 𝓘(ℝ, VTf)) (I' := 𝓘(ℝ, G × G))
    change (mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, G × G) (fun v ↦ φ (v, 0)) 0 :
      VTf →L[ℝ] (G × G)) = mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, G × G) (TgMap ∘ b) 0 at he
    rw [he, mfderiv_comp 0 ((TgMap).contMDiff.mdifferentiableAt (by simp))
      (hb.mdifferentiableAt (by simp))]
    rw [hbzero]
  -- The second partial is the same second tube in a different fixed linear frame.
  let eg₀ := (trivializationAt VTg νTg (TfMap z)).continuousLinearEquivAt ℝ (TfMap z)
    (mem_baseSet_trivializationAt VTg νTg (TfMap z))
  let Q : Wg →L[ℝ] νTg (TfMap z) :=
    (Sg.equiv (TfMap z)).symm.toContinuousLinearMap.comp (eg.symmL ℝ (TfMap z))
  let C : Wg →L[ℝ] VTg := eg₀.toContinuousLinearMap.comp Q
  let bg : VTg → TP := fun w ↦
    Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg) ⟨TfMap z, eg₀.symm w⟩
  have hbg : ContMDiff 𝓘(ℝ, VTg) 𝓘(ℝ, G × G) ∞ bg := by
    apply hTg.comp
    intro w
    let e := trivializationAt VTg νTg (TfMap z)
    have hz : TfMap z ∈ e.baseSet := mem_baseSet_trivializationAt VTg νTg (TfMap z)
    rw [e.contMDiffAt_iff (e.mem_source.mpr hz)]
    refine ⟨contMDiffAt_const, ?_⟩
    apply contMDiffAt_id.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro v
    change (e ⟨TfMap z, eg₀.symm v⟩).2 = v
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ (TfMap z) hz]
    exact eg₀.apply_symm_apply v
  have hsecond : (fun w : Wg ↦ φ (0, w)) = bg ∘ C := by
    funext w
    change Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
      ⟨b 0, (Sg.equiv (b 0)).symm (eg.symm (b 0) w)⟩ = _
    rw [hbzero]
    change _ = Tg.totalMap TgMap (isImmersion_smoothTangentMap g hg)
      ⟨TfMap z, eg₀.symm (eg₀ (Q w))⟩
    rw [eg₀.symm_apply_apply]
    congr 2
    exact congrArg (Sg.equiv (TfMap z)).symm (eg.symmL_apply hegz w).symm
  have hsecondD (w : Wg) :
      (mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, G × G) (fun w ↦ φ (0, w)) 0
        ((NormedSpace.fromTangentSpace (0 : Wg)).symm w) : G × G) = Jg (TfMap z) (Q w) := by
    have hCzero : C (0 : Wg) = 0 := C.map_zero
    have hc := mfderiv_comp 0
      (show MDifferentiableAt 𝓘(ℝ, VTg) 𝓘(ℝ, G × G) bg (C 0) from by
        rw [hCzero]
        exact hbg.mdifferentiableAt (by simp))
      ((C.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp))
    have hCder : mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, VTg) C 0 =
        ((NormedSpace.fromTangentSpace (C 0)).symm.toContinuousLinearMap.comp C).comp
          (NormedSpace.fromTangentSpace (0 : Wg)).toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv, C.fderiv]
      rfl
    rw [hCder] at hc
    have hp := DFunLike.congr_fun hc ((NormedSpace.fromTangentSpace (0 : Wg)).symm w)
    change mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, G × G) (bg ∘ C) 0
        ((NormedSpace.fromTangentSpace (0 : Wg)).symm w) =
      mfderiv 𝓘(ℝ, VTg) 𝓘(ℝ, G × G) bg (C 0)
        ((NormedSpace.fromTangentSpace (C 0)).symm
          (C ((NormedSpace.fromTangentSpace (0 : Wg))
            ((NormedSpace.fromTangentSpace (0 : Wg)).symm w)))) at hp
    rw [ContinuousLinearEquiv.apply_symm_apply] at hp
    have hj := hJg (TfMap z) (Q w)
    change Jg (TfMap z) (Q w) =
      mfderiv 𝓘(ℝ, VTg) 𝓘(ℝ, G × G) bg 0
        ((NormedSpace.fromTangentSpace (0 : VTg)).symm (C w)) at hj
    calc
      (mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, G × G) (fun w ↦ φ (0, w)) 0
          ((NormedSpace.fromTangentSpace (0 : Wg)).symm w) : G × G) =
        mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, G × G) (bg ∘ C) 0
          ((NormedSpace.fromTangentSpace (0 : Wg)).symm w) :=
        congrArg (fun k : Wg → TP ↦
          (mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, G × G) k 0
            ((NormedSpace.fromTangentSpace (0 : Wg)).symm w) : G × G)) hsecond
      _ = mfderiv 𝓘(ℝ, VTg) 𝓘(ℝ, G × G) bg (C 0)
          ((NormedSpace.fromTangentSpace (C 0)).symm (C w)) := hp
      _ = mfderiv 𝓘(ℝ, VTg) 𝓘(ℝ, G × G) bg 0
          ((NormedSpace.fromTangentSpace (0 : VTg)).symm (C w)) :=
        congrArg (fun x : VTg ↦
          (mfderiv 𝓘(ℝ, VTg) 𝓘(ℝ, G × G) bg x
            ((NormedSpace.fromTangentSpace x).symm (C w)) : G × G)) hCzero
      _ = Jg (TfMap z) (Q w) := hj.symm
  -- Add the partial derivatives in the original quotient, then use its actual inverse formula.
  intro v w
  have hsplit : (mfderiv 𝓘(ℝ, VTf × Wg) 𝓘(ℝ, G × G) φ 0
      ((NormedSpace.fromTangentSpace (0 : VTf × Wg)).symm (v, w)) : G × G) =
      mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, G × G) (fun v ↦ φ (v, 0)) 0
        ((NormedSpace.fromTangentSpace (0 : VTf)).symm v) +
      mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, G × G) (fun w ↦ φ (0, w)) 0
        ((NormedSpace.fromTangentSpace (0 : Wg)).symm w) := by
    rw [modelWithCornersSelf_prod (𝕜 := ℝ) (E := VTf) (F := Wg),
      ← chartedSpaceSelf_prod (H := VTf) (H' := Wg)]
    exact mfderiv_prod_eq_add_apply (p := (0, 0)) (v := (v, w)) hφ
  have hnormal := Tf.normal_deriv z v
  change (LinearMap.range
    (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) TfMap z).toLinearMap).mkQ
      (mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, F × F) b 0
        ((NormedSpace.fromTangentSpace (0 : VTf)).symm v)) = ef.symm v at hnormal
  let q := (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G)
    ((TgMap).comp TfMap) z).toLinearMap).mkQ
  have hqFirst : q (mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, G × G) (fun v ↦ φ (v, 0)) 0
      ((NormedSpace.fromTangentSpace (0 : VTf)).symm v)) = ST.injection z (ef.symm v) :=
    (congrArg q (DFunLike.congr_fun hfirstD
      ((NormedSpace.fromTangentSpace (0 : VTf)).symm v))).trans
        ((ST.injection_apply z
          (mfderiv 𝓘(ℝ, VTf) 𝓘(ℝ, F × F) b 0
            ((NormedSpace.fromTangentSpace (0 : VTf)).symm v))).symm.trans
          (congrArg (ST.injection z) hnormal))
  have hqSecond : q (mfderiv 𝓘(ℝ, Wg) 𝓘(ℝ, G × G) (fun w ↦ φ (0, w)) 0
      ((NormedSpace.fromTangentSpace (0 : Wg)).symm w)) = q (Jg (TfMap z) (Q w)) :=
    congrArg q (hsecondD w)
  have hQ : Q w = (Sg.equiv (TfMap z)).symm (eg.symm (TfMap z) w) :=
    congrArg (Sg.equiv (TfMap z)).symm (eg.symmL_apply hegz w)
  exact ((congrArg q hsplit).trans (q.map_add _ _)).trans
    ((congrArg₂ (· + ·) hqFirst hqSecond).trans
      ((hST z (ef.symm v) (Q w)).symm.trans
        (congrArg (fun u ↦ (ST.equiv z).symm (ef.symm v, u)) hQ)))

end AtiyahSinger

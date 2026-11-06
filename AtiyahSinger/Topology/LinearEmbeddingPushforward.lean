/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.LinearEmbeddingNormalCoordinates
public import AtiyahSinger.Topology.EuclideanTangentKTheory
public import AtiyahSinger.Topology.SupportedTrivialBundleThom
public import AtiyahSinger.Topology.TangentEmbeddingPushforward

import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The actual pushforward of a linear coordinate inclusion

Public module ID: M1933.

The original normal quotient of a complemented linear inclusion has the given
complementary coordinates. Its scalar extension is the native trivial complex
bundle, with the prescribed real part before the imaginary part. The supported
Thom comparison then computes the original pushforward as exterior Bott product
followed by the whole tangent-coordinate homeomorphism.

This supplies the two ordered Euclidean block inclusions used by SG III.13,
pp.243--244, without replacing their actual maps or choosing a Bott generator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold Topology
open scoped ContDiff TensorProduct

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold sumTopology
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Ordered complementary real and imaginary coordinates in the original tangent spaces. -/
def linearEmbeddingTangentProductHomeomorph (k : ℕ)
    (c : F ≃L[ℝ] E × EuclideanSpace ℝ (Fin k)) :
    (TangentBundle 𝓘(ℝ, E) E × EuclideanSpace ℂ (Fin k)) ≃ₜ
      TangentBundle 𝓘(ℝ, F) F :=
  let r := ((PiLp.homeomorph 2 (fun _ : Fin k ↦ ℂ)).trans
    (euclideanTangentComplexHomeomorph k).symm).trans
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin k)))
  (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).prodCongr r).trans
    (LinearEquiv.prodProdProdComm ℝ E E
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))).toContinuousLinearEquiv.toHomeomorph)
      |>.trans ((c.symm.toHomeomorph.prodCongr c.symm.toHomeomorph).trans
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar extension of real coordinates is the ordered real-plus-imaginary complex coordinate.
This private algebra adapter retains the actual tensor product and the given real equivalence. -/
private theorem exists_complexificationEuclidean_equiv
    {W : Type*} [AddCommGroup W] [Module ℝ W] (k : ℕ)
    (e : W ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :
    ∃ d : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k),
      ∀ (w : ℂ ⊗[ℝ] W) (i : Fin k),
        d w i = (e (complexificationReIm W w).1 i : ℂ) +
          (e (complexificationReIm W w).2 i : ℂ) * Complex.I := by
  let a := e.trans (EuclideanSpace.equiv (Fin k) ℝ).toLinearEquiv
  let d : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    ((a.baseChange ℝ ℂ _ _).trans (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin k))).trans
      (EuclideanSpace.equiv (Fin k) ℂ).symm.toLinearEquiv
  refine ⟨d, ?_⟩
  intro w i
  -- Pure tensors fix the sign and order; additivity extends this to the original tensor space.
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    change TensorProduct.piScalarRight ℝ ℂ ℂ (Fin k)
      ((a.baseChange ℝ ℂ _ _) (z ⊗ₜ[ℝ] v)) i = _
    rw [LinearEquiv.baseChange_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, (complexificationReIm_properties W).1]
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    change (e v i : ℂ) * z =
      (z.re : ℂ) * (e v i : ℂ) + ((z.im : ℂ) * (e v i : ℂ)) * Complex.I
    calc
      _ = (e v i : ℂ) * ((z.re : ℂ) + (z.im : ℂ) * Complex.I) :=
        congrArg (fun a : ℂ ↦ (e v i : ℂ) * a) (Complex.re_add_im z).symm
      _ = _ := by ring
  | add u v hu hv =>
    simp only [map_add, PiLp.add_apply, Prod.fst_add, Prod.snd_add, hu, hv,
      Complex.ofReal_add]
    ring

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Keep the original normal, scalar-extension and native trivial-bundle topologies visible.
/-- A complemented linear inclusion pushes forward by the positive exterior Bott product
in its specified ordered whole tangent coordinates. -/
theorem tangentEmbeddingPushforward_linear (k : ℕ)
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (hp : IsProperMap f)
    (c : F ≃L[ℝ] E × EuclideanSpace ℝ (Fin k))
    (hlinear : ∀ x, f x = c.symm (x, 0)) :
    letI : T2Space (TangentBundle 𝓘(ℝ, E) E) := (tangentBundle_topology E E).1
    letI : T2Space (TangentBundle 𝓘(ℝ, F) F) := (tangentBundle_topology F F).1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) E) :=
      ChartedSpace.locallyCompactSpace (E × E) (TangentBundle 𝓘(ℝ, E) E)
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, F) F) :=
      ChartedSpace.locallyCompactSpace (F × F) (TangentBundle 𝓘(ℝ, F) F)
    tangentEmbeddingPushforward f hf hp =
      (compactSupportKZeroHomeomorph (linearEmbeddingTangentProductHomeomorph k c)).comp
        (compactSupportKZeroExternalProduct.flip
          (exteriorBottClass (EuclideanSpace ℂ (Fin k)))) := by
  classical
  let TM := TangentBundle 𝓘(ℝ, E) E
  let TN := TangentBundle 𝓘(ℝ, F) F
  let : T2Space TM := (tangentBundle_topology E E).1
  let : T2Space TN := (tangentBundle_topology F F).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let : ParacompactSpace TM := (tangentBundle_topology E E).2.2
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let ν := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let V := NormalModel E F
  let W := EuclideanSpace ℂ (Fin k)
  let R := (smoothTangentBundleProjection E E : TM → E) *ᵖ ν
  let X := TotalSpace Unit (ComplexifiedNormalPullback f)
  -- Choose the actual normal coordinates, canonical ordered splitting and tube together.
  obtain ⟨e, _, hes, _, S, T, hT⟩ := exists_linearEmbedding_tangentNormal_coordinates f hf c hlinear
  choose d hd using fun x : E ↦
    exists_complexificationEuclidean_equiv k (e x).toLinearEquiv
  let πM := smoothTangentBundleProjection E E
  let C : X ≃ₜ TotalSpace (V × V) (R ×ᵇ R) := complexificationDoubleTotalHomeomorph V R
  have hpair : Continuous (fun z : TotalSpace (V × V) (R ×ᵇ R) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace V R),
        (⟨z.proj, z.snd.2⟩ : TotalSpace V R))) := continuous_induced_dom
  have hreal : Continuous (fun z : TotalSpace V R ↦ e z.proj.proj z.snd) :=
    continuous_snd.comp (hes.continuous.comp (Pullback.continuous_lift V ν πM))
  have hre := hreal.comp ((continuous_fst.comp hpair).comp C.continuous)
  have him := hreal.comp ((continuous_snd.comp hpair).comp C.continuous)
  -- Continuity of scalar extension follows from these same real and imaginary coordinates.
  have hdcont : Continuous (fun z : X ↦ d z.proj.proj z.snd) := by
    have hcoords : Continuous (fun z : X ↦ fun i : Fin k ↦
        (e z.proj.proj (complexificationReIm (ν z.proj.proj) z.snd).1 i : ℂ) +
          (e z.proj.proj (complexificationReIm (ν z.proj.proj) z.snd).2 i : ℂ) * Complex.I) := by
      apply continuous_pi
      intro i
      exact (Complex.continuous_ofReal.comp ((PiLp.proj (𝕜 := ℝ) 2
        (fun _ : Fin k ↦ ℝ) i).continuous.comp
        hre)).add ((Complex.continuous_ofReal.comp
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k ↦ ℝ) i).continuous.comp him)).mul continuous_const)
    apply ((EuclideanSpace.equiv (Fin k) ℂ).symm.continuous.comp hcoords).congr
    intro z
    ext i
    exact (hd z.proj.proj z.snd i).symm
  let TT := Bundle.Trivial TM W
  let := modelTopology W TT
  let := isFiniteRank_model W TT
  let eTT := (unitTotalHomeomorph W TT).trans (Bundle.Trivial.homeomorphProd TM W)
  let a : Hom (ComplexifiedNormalPullback f) TT :=
    { linearMap z := (d z.proj).toLinearMap
      continuous_total := eTT.symm.continuous.comp (continuous_proj.prodMk hdcont) }
  let i := a.toIso (fun z ↦ (d z.proj).bijective)
  let H := linearEmbeddingTangentProductHomeomorph k c
  let τ := tangentEmbeddingTubularMap f hf S T
  have hτ : (τ : X → TN) = H ∘ eTT ∘ i.totalHomeomorph := by
    funext z
    let uv := complexificationReIm (ν z.proj.proj) z.snd
    have hr : (EuclideanSpace.equiv (Fin k) ℝ).symm
        (fun j ↦ (d z.proj.proj z.snd j).re) = e z.proj.proj uv.1 := by
      ext j
      change (d z.proj.proj z.snd j).re = e z.proj.proj uv.1 j
      rw [hd]
      simp [uv, ν]
    have hi : (EuclideanSpace.equiv (Fin k) ℝ).symm
        (fun j ↦ (d z.proj.proj z.snd j).im) = e z.proj.proj uv.2 := by
      ext j
      change (d z.proj.proj z.snd j).im = e z.proj.proj uv.2 j
      rw [hd]
      simp [uv, ν]
    change T.totalMap _ _ ⟨z.proj, (S.equiv z.proj).symm uv⟩ = _
    rw [hT]
    change (⟨c.symm (z.proj.proj, e z.proj.proj uv.1),
      c.symm (z.proj.snd, e z.proj.proj uv.2)⟩ : TN) =
        ⟨c.symm (z.proj.proj, (EuclideanSpace.equiv (Fin k) ℝ).symm
            (fun j ↦ (d z.proj.proj z.snd j).re)),
          c.symm (z.proj.snd, (EuclideanSpace.equiv (Fin k) ℝ).symm
            (fun j ↦ (d z.proj.proj z.snd j).im))⟩
    rw [hr, hi]
  -- The original metric may be chosen arbitrarily; Thom naturality uses this same complex iso.
  let h := (nonempty_continuousHermitianMetric (ComplexifiedNormalPullback f)).some
  have hinner : Continuous (fun z : TotalSpace Unit (TT ×ᵇ TT) ↦
      inner ℂ z.snd.1 z.snd.2) :=
    (eTT.continuous.snd.comp (continuous_sum_fst (E := TT) (F := TT))).inner
      (eTT.continuous.snd.comp (continuous_sum_snd (E := TT) (F := TT)))
  let hTT := ContinuousHermitianMetric.ofInnerProduct TT hinner
  have hchosen : tangentEmbeddingPushforward f hf hp =
      tangentEmbeddingPushforwardWith f hf S T h := by
    unfold tangentEmbeddingPushforward
    exact tangentEmbeddingPushforwardWith_eq f hf _ S _ T _ h
  rw [hchosen]
  apply AddMonoidHom.ext
  intro b
  let hτopen := isOpenEmbedding_tangentEmbeddingTubularMap f hf S T
  have htransport (u : CompactSupportKZero X) :
      compactSupportKZeroOpenPushforward τ hτopen u =
        compactSupportKZeroHomeomorph H
          (compactSupportKZeroHomeomorph eTT
            (compactSupportKZeroHomeomorph i.totalHomeomorph u)) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph H,
      ← compactSupportKZeroOpenPushforward_homeomorph eTT,
      ← compactSupportKZeroOpenPushforward_homeomorph i.totalHomeomorph]
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
    congr 2
  change compactSupportKZeroOpenPushforward τ hτopen (h.supportedThomHom b) =
    compactSupportKZeroHomeomorph H
      (compactSupportKZeroExternalProduct b (exteriorBottClass W))
  rw [htransport]
  have hmetric := DFunLike.congr_fun (h.supportedThomHom_iso hTT i) b
  change compactSupportKZeroHomeomorph i.totalHomeomorph (h.supportedThomHom b) =
    hTT.supportedThomHom b at hmetric
  rw [hmetric]
  exact congrArg (compactSupportKZeroHomeomorph H)
    (ContinuousHermitianMetric.supportedThomHom_trivial_externalProduct TM W hTT b)

end AtiyahSinger

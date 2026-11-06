/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereVerticalDerivative
public import AtiyahSinger.Geometry.HorizontalTangentSplitting

/-!
# Tangent coordinates over the original whole sphere chart

Public module ID: M1250.

A specified horizontal lift and the derivative of the original stereographic
chart identify the pulled tangent bundle with the original base tangent and
vector fibers. The formula retains that same horizontal lift and the exact
affine fiber derivative, including the original stereographic normalization.

This is the smooth tangent parametrization used before reordering its source
as the doubled bundle over the base tangent space. The later normalization
of its tangent normal derivative remains a separate geometric comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology
open scoped ContDiff

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere
  verticalTangentTopology

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 50 in
set_option maxHeartbeats 2200000 in
-- Pull the actual horizontal assembly through the same whole stereographic chart.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tangent coordinates retain the given horizontal lift and actual affine fiber derivative. -/
theorem exists_frameSphere_tangentCoordinateEquiv
    (H : letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
      let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let a := frameSphereStereographic (EB := EB) r V
    let I := 𝓘(ℝ, EB)
    let J := 𝓘(ℝ, EB × R)
    let A := I.prod 𝓘(ℝ, R)
    let H' : SmoothHorizontalLift (smoothAssociatedSphereProjection S) := H
    let pr : ContMDiffMap A I (TotalSpace R V) B ∞ :=
      ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj V⟩
    let aInv : ContMDiffMap A J (TotalSpace R V) Z ∞ :=
      ⟨a.symm, (frameSphereStereographic_spec r V).2.2.2.2.2⟩
    let W := ((pr : TotalSpace R V → B) *ᵖ (TangentSpace I)) ×ᵇ
      ((pr : TotalSpace R V → B) *ᵖ V)
    let T := (aInv : TotalSpace R V → Z) *ᵖ (TangentSpace J)
    ∃ e : ∀ z : TotalSpace R V, (TangentSpace I z.proj × V z.proj) ≃L[ℝ]
        TangentSpace J (a.symm z),
      (∀ (z : TotalSpace R V) (ξ : TangentSpace I z.proj) (v : V z.proj),
        let horizontal : EB × R := H'.lift (a.symm z) ξ
        let vertical : EB × R :=
          mfderiv 𝓘(ℝ, ℝ) J (fun t : ℝ ↦ a.symm ⟨z.proj, z.snd + t • v⟩) 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)
        (e z (ξ, v) : EB × R) = horizontal + vertical) ∧
      ContMDiff (A.prod 𝓘(ℝ, EB × R)) (A.prod 𝓘(ℝ, EB × R)) ∞
        (fun z : TotalSpace (EB × R) W ↦
          (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (EB × R) T)) ∧
      ContMDiff (A.prod 𝓘(ℝ, EB × R)) (A.prod 𝓘(ℝ, EB × R)) ∞
        (fun z : TotalSpace (EB × R) T ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace (EB × R) W)) := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let a := frameSphereStereographic (EB := EB) r V
  have ha := frameSphereStereographic_spec (EB := EB) r V
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let A := I.prod 𝓘(ℝ, R)
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let K := VerticalTangentFiber J I q
  let D := VerticalTangentModel (EB × R) EB
  let pr : ContMDiffMap A I (TotalSpace R V) B ∞ :=
    ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj V⟩
  let aInv : ContMDiffMap A J (TotalSpace R V) Z ∞ := ⟨a.symm, ha.2.2.2.2.2⟩
  let Wb := (pr : TotalSpace R V → B) *ᵖ (TangentSpace I)
  let Wr := (pr : TotalSpace R V → B) *ᵖ V
  let Y := (aInv : TotalSpace R V → Z) *ᵖ K
  let T := (aInv : TotalSpace R V → Z) *ᵖ (TangentSpace J)
  let (z : TotalSpace R V) : AddCommGroup (Wb z) := by
    change AddCommGroup (TangentSpace I z.proj)
    infer_instance
  let (z : TotalSpace R V) : Module ℝ (Wb z) := by
    change Module ℝ (TangentSpace I z.proj)
    infer_instance
  let (z : TotalSpace R V) : IsTopologicalAddGroup (Wb z) := by
    change IsTopologicalAddGroup (TangentSpace I z.proj)
    infer_instance
  let (z : TotalSpace R V) : ContinuousSMul ℝ (Wb z) := by
    change ContinuousSMul ℝ (TangentSpace I z.proj)
    infer_instance
  let (z : TotalSpace R V) : AddCommGroup (Wr z) := by
    change AddCommGroup (V z.proj)
    infer_instance
  let (z : TotalSpace R V) : Module ℝ (Wr z) := by
    change Module ℝ (V z.proj)
    infer_instance
  let (z : TotalSpace R V) : IsTopologicalAddGroup (Wr z) := by
    change IsTopologicalAddGroup (V z.proj)
    infer_instance
  let (z : TotalSpace R V) : ContinuousSMul ℝ (Wr z) := by
    change ContinuousSMul ℝ (V z.proj)
    infer_instance
  let (z : TotalSpace R V) : AddCommGroup (T z) := by
    change AddCommGroup (TangentSpace J (a.symm z))
    infer_instance
  let (z : TotalSpace R V) : Module ℝ (T z) := by
    change Module ℝ (TangentSpace J (a.symm z))
    infer_instance
  let (z : TotalSpace R V) : IsTopologicalAddGroup (T z) := by
    change IsTopologicalAddGroup (TangentSpace J (a.symm z))
    infer_instance
  let (z : TotalSpace R V) : ContinuousSMul ℝ (T z) := by
    change ContinuousSMul ℝ (TangentSpace J (a.symm z))
    infer_instance
  let W := Wb ×ᵇ Wr
  let Bq := (q : Z → B) *ᵖ (TangentSpace I)
  -- The base projection is that of the original bundle, not a new trivialization.
  have hqa (z : TotalSpace R V) : q (a.symm z) = z.proj := by
    let c := frameSphereHomeomorph (EB := EB) r V
    have hc := (frameSphereHomeomorph_spec (EB := EB) r V).1
    have hbase (y : Z) : q y = (c y).val.1.proj := by
      induction y using Quotient.inductionOn with
      | h u =>
        change q (associatedBundleMk G P (OrthogonalSphere r) u.1 u.2) =
          (c (associatedBundleMk G P (OrthogonalSphere r) u.1 u.2)).val.1.proj
        rw [hc]
        rfl
    rw [hbase]
    change (c (a.symm z)).val.1.proj = z.proj
    rw [ha.2.2.2.1]
  obtain ⟨L, hL, hLf, _⟩ := exists_frameSphere_verticalDerivativeEquiv (EB := EB) r V
  obtain ⟨c, hc, hcf, _⟩ := H.exists_tangentAssemblyEquiv q hq
  let e (z : TotalSpace R V) : (TangentSpace I z.proj × V z.proj) ≃L[ℝ]
      TangentSpace J (a.symm z) :=
    ((ContinuousLinearEquiv.refl ℝ EB).prodCongr (L z)).trans (c (a.symm z))
  have he (z : TotalSpace R V) (ξ : TangentSpace I z.proj) (v : V z.proj) :
      e z (ξ, v) = H.lift (a.symm z) ξ + (L z v).val := hc _ _
  -- Lift the two source components into the same horizontal/vertical assembly bundle.
  have hsecond : ContMDiff (A.prod 𝓘(ℝ, EB × R)) (A.prod 𝓘(ℝ, R)) ∞
      (fun z : TotalSpace (EB × R) W ↦ (⟨z.proj, z.snd.2⟩ : TotalSpace R Wr)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj W, ?_⟩
    have ht := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (A.prod 𝓘(ℝ, EB × R))
        (A.prod 𝓘(ℝ, EB × R)) ∞ id z)).2
    exact (ContinuousLinearMap.snd ℝ EB R).contDiff.contMDiff.contMDiffAt.comp z ht
  have hvertical : ContMDiff (A.prod 𝓘(ℝ, EB × R)) (J.prod 𝓘(ℝ, D)) ∞
      (fun z : TotalSpace (EB × R) W ↦
        (⟨a.symm z.proj, L z.proj z.snd.2⟩ : TotalSpace D K)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨ha.2.2.2.2.2.contMDiffAt.comp z (Bundle.contMDiffAt_proj W), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp ((hLf.comp hsecond) z)).2
  have hfirst : ContMDiff (A.prod 𝓘(ℝ, EB × R)) I.tangent ∞
      (fun z : TotalSpace (EB × R) W ↦
        (⟨z.proj.proj, z.snd.1⟩ : TangentBundle I B)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨pr.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj W), ?_⟩
    have ht := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (A.prod 𝓘(ℝ, EB × R))
        (A.prod 𝓘(ℝ, EB × R)) ∞ id z)).2
    exact (ContinuousLinearMap.fst ℝ EB R).contDiff.contMDiff.contMDiffAt.comp z ht
  have hhorizontal : ContMDiff (A.prod 𝓘(ℝ, EB × R)) (J.prod 𝓘(ℝ, EB)) ∞
      (fun z : TotalSpace (EB × R) W ↦
        (⟨a.symm z.proj, z.snd.1⟩ : TotalSpace EB Bq)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨ha.2.2.2.2.2.contMDiffAt.comp z (Bundle.contMDiffAt_proj W), ?_⟩
    have ht := (Bundle.contMDiffAt_totalSpace.mp (hfirst z)).2
    change ContMDiffAt (A.prod 𝓘(ℝ, EB × R)) 𝓘(ℝ, EB) ∞
      (fun w : TotalSpace (EB × R) W ↦
        ((trivializationAt EB (TangentSpace I) (q (a.symm z.proj)))
          ⟨q (a.symm w.proj), w.snd.1⟩).2) z
    rw [hqa z.proj]
    apply ht.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro w
    exact congrArg (fun y : TangentBundle I B ↦
      ((trivializationAt EB (TangentSpace I) z.proj.proj) y).2)
        (Bundle.TotalSpace.ext (hqa w.proj) (by rfl))
  have hcoordinates : ContMDiff (A.prod 𝓘(ℝ, EB × R))
      (J.prod 𝓘(ℝ, EB × D)) ∞
      (fun z : TotalSpace (EB × R) W ↦
        (⟨a.symm z.proj, z.snd.1, L z.proj z.snd.2⟩ :
          TotalSpace (EB × D) (Bq ×ᵇ K))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨ha.2.2.2.2.2.contMDiffAt.comp z (Bundle.contMDiffAt_proj W), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp (hhorizontal z)).2.prodMk_space
      (Bundle.contMDiffAt_totalSpace.mp (hvertical z)).2
  have hforward : ContMDiff (A.prod 𝓘(ℝ, EB × R)) (A.prod 𝓘(ℝ, EB × R)) ∞
      (fun z : TotalSpace (EB × R) W ↦
        (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (EB × R) T)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj W, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp ((hcf.comp hcoordinates) z)).2
  refine ⟨e, ?_, hforward, ?_⟩
  · intro z ξ v
    rw [he, hL]
  -- Smoothness of the inverse is detected by this same original coordinate equivalence.
  · apply contMDiff_bundleMap_of_comp_injective (I := A)
      (W := W) (V₀ := T) («Z» := T) (F := EB × R) («G» := EB × R) (H := EB × R)
      (fun z ↦ (e z).toContinuousLinearMap) (fun z ↦ (e z).symm.toContinuousLinearMap)
      hforward (fun z ↦ (e z).injective)
    apply contMDiff_id.congr
    intro z
    change (⟨z.proj, e z.proj ((e z.proj).symm z.snd)⟩ : TotalSpace (EB × R) T) = z
    rw [(e z.proj).apply_symm_apply]

end AtiyahSinger

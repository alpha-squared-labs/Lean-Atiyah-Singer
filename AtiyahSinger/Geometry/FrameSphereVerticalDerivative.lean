/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereVerticalCotangent
public import AtiyahSinger.Geometry.FrameSpherePoleNormalization
public import AtiyahSinger.Geometry.SmoothBundleQuotientDescent
public import AtiyahSinger.Geometry.SmoothBundleSubbundle

/-!
# The vertical derivative on the whole original sphere chart

Public module ID: M1255.

The original whole-bundle stereographic inverse identifies each original
vector fiber with the actual vertical derivative kernel at every point of its
open image. The formula is the derivative of the same affine fiber curve.
The normalized pole chart and frame verify invertibility pointwise; the
factor one half is retained. Smoothness uses the global affine family,
then the native smooth subbundle criterion for both the map and its inverse.
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
set_option maxHeartbeats 3500000 in
-- Pulled tangent, vertical kernel and original frame atlases share the affine radial family.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual affine fiber derivative is a smooth vertical equivalence throughout the chart. -/
theorem exists_frameSphere_verticalDerivativeEquiv :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let a := frameSphereStereographic (EB := EB) r V
    let q := smoothAssociatedSphereProjection S
    let hq := associatedSphereProjection_isSubmersion S
    letI := verticalTangentFiberBundle q hq
    letI := verticalTangentVectorBundle q hq
    letI := verticalTangentContMDiffVectorBundle q hq
    let K := VerticalTangentFiber 𝓘(ℝ, EB × R) 𝓘(ℝ, EB) q
    let pr : ContMDiffMap (𝓘(ℝ, EB).prod 𝓘(ℝ, R)) 𝓘(ℝ, EB)
        (TotalSpace R V) B ∞ := ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj V⟩
    let aInv : ContMDiffMap (𝓘(ℝ, EB).prod 𝓘(ℝ, R)) 𝓘(ℝ, EB × R)
        (TotalSpace R V) Z ∞ := ⟨a.symm, (frameSphereStereographic_spec r V).2.2.2.2.2⟩
    let W := (pr : TotalSpace R V → B) *ᵖ V
    let Y := (aInv : TotalSpace R V → Z) *ᵖ K
    ∃ e : ∀ z : TotalSpace R V, V z.proj ≃L[ℝ] K (a.symm z),
      (∀ (z : TotalSpace R V) (v : V z.proj), (e z v).val =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EB × R)
          (fun t : ℝ ↦ a.symm ⟨z.proj, z.snd + t • v⟩) 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)) ∧
      ContMDiff ((𝓘(ℝ, EB).prod 𝓘(ℝ, R)).prod 𝓘(ℝ, R))
        ((𝓘(ℝ, EB).prod 𝓘(ℝ, R)).prod 𝓘(ℝ, VerticalTangentModel (EB × R) EB)) ∞
        (fun z : TotalSpace R W ↦
          (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (VerticalTangentModel (EB × R) EB) Y)) ∧
      ContMDiff
        ((𝓘(ℝ, EB).prod 𝓘(ℝ, R)).prod 𝓘(ℝ, VerticalTangentModel (EB × R) EB))
        ((𝓘(ℝ, EB).prod 𝓘(ℝ, R)).prod 𝓘(ℝ, R)) ∞
        (fun z : TotalSpace (VerticalTangentModel (EB × R) EB) Y ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace R W)) := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let A := I.prod 𝓘(ℝ, R)
  let a := frameSphereStereographic (EB := EB) r V
  have ha := frameSphereStereographic_spec (EB := EB) r V
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let K := VerticalTangentFiber J I q
  let pr : ContMDiffMap A I (TotalSpace R V) B ∞ :=
    ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj V⟩
  let aInv : ContMDiffMap A J (TotalSpace R V) Z ∞ := ⟨a.symm, ha.2.2.2.2.2⟩
  let W := (pr : TotalSpace R V → B) *ᵖ V
  let Y := (aInv : TotalSpace R V → Z) *ᵖ K
  let T := (aInv : TotalSpace R V → Z) *ᵖ (TangentSpace J)
  let D := VerticalTangentModel (EB × R) EB
  let : ∀ z, AddCommGroup (W z) := fun z ↦ inferInstanceAs (AddCommGroup (V z.proj))
  let : ∀ z, Module ℝ (W z) := fun z ↦ inferInstanceAs (Module ℝ (V z.proj))
  let : ∀ z, IsTopologicalAddGroup (W z) :=
    fun z ↦ inferInstanceAs (IsTopologicalAddGroup (V z.proj))
  let : ∀ z, ContinuousSMul ℝ (W z) :=
    fun z ↦ inferInstanceAs (ContinuousSMul ℝ (V z.proj))
  let : ∀ z, AddCommGroup (Y z) := fun z ↦ inferInstanceAs (AddCommGroup (K (a.symm z)))
  let : ∀ z, Module ℝ (Y z) := fun z ↦ inferInstanceAs (Module ℝ (K (a.symm z)))
  let : ∀ z, IsTopologicalAddGroup (Y z) :=
    fun z ↦ inferInstanceAs (IsTopologicalAddGroup (K (a.symm z)))
  let : ∀ z, ContinuousSMul ℝ (Y z) :=
    fun z ↦ inferInstanceAs (ContinuousSMul ℝ (K (a.symm z)))
  let : ∀ z, AddCommGroup (T z) :=
    fun z ↦ inferInstanceAs (AddCommGroup (TangentSpace J (a.symm z)))
  let : ∀ z, Module ℝ (T z) :=
    fun z ↦ inferInstanceAs (Module ℝ (TangentSpace J (a.symm z)))
  let : ∀ z, IsTopologicalAddGroup (T z) :=
    fun z ↦ inferInstanceAs (IsTopologicalAddGroup (TangentSpace J (a.symm z)))
  let : ∀ z, ContinuousSMul ℝ (T z) :=
    fun z ↦ inferInstanceAs (ContinuousSMul ℝ (TangentSpace J (a.symm z)))
  -- Frames verify fiberwise bijectivity without asserting a smooth global frame.
  let frame (x : B) : R ≃ₗᵢ[ℝ] V x := by
    apply Classical.choice
    obtain ⟨⟨y, p⟩, hp⟩ := S.toIsPrincipalBundle.projection_properties.2.2 x
    change y = x at hp
    subst y
    exact ⟨p⟩
  let p (x : B) : P := ⟨x, frame x⟩
  let b := orthogonalSphereNormalizedChart r false
  have hb := orthogonalSphereNormalizedChart_smooth r false
  have hbd : b.MDifferentiable (𝓡 r) (𝓡 r) :=
    ⟨hb.1.mdifferentiableOn (by simp), (hb.2.mdifferentiable (by simp)).mdifferentiableOn⟩
  let half : R ≃L[ℝ] R :=
    (LinearEquiv.smulOfNeZero ℝ R (1 / 2 : ℝ) (by norm_num)).toContinuousLinearEquiv
  let u₀ (z : TotalSpace R V) : R := half ((frame z.proj).symm z.snd)
  have hbt (z : TotalSpace R V) : u₀ z ∈ b.target := by
    rw [(orthogonalSphereNormalizedChart_properties r false).2.1]
    trivial
  let db (z : TotalSpace R V) : R ≃L[ℝ] TangentSpace (𝓡 r) (b.symm (u₀ z)) :=
    hbd.symm.mfderiv (hbt z)
  have hpoint (z : TotalSpace R V) :
      associatedBundleMk G P (OrthogonalSphere r) (p z.proj) (b.symm (u₀ z)) = a.symm z := by
    have h := frameSphereStereographic_symm_two_smul (EB := EB) r V (p z.proj) (u₀ z)
    have hvec : (2 : ℝ) • (frame z.proj) (u₀ z) = z.snd := by
      change (2 : ℝ) • (frame z.proj) ((1 / 2 : ℝ) • (frame z.proj).symm z.snd) = _
      rw [map_smul, (frame z.proj).apply_symm_apply, smul_smul]
      norm_num
    rw [hvec] at h
    exact h.symm
  let L₀ (z : TotalSpace R V) : V z.proj ≃L[ℝ]
      K (associatedBundleMk G P (OrthogonalSphere r) (p z.proj) (b.symm (u₀ z))) :=
    ((frame z.proj).symm.toContinuousLinearEquiv.trans half).trans
      ((db z).trans (associatedSphereFiberTangentEquiv S (p z.proj) (b.symm (u₀ z))))
  let L (z : TotalSpace R V) : V z.proj ≃L[ℝ] K (a.symm z) := (hpoint z) ▸ L₀ z
  have hLval (z : TotalSpace R V) (v : V z.proj) : (L z v).val = (L₀ z v).val := by
    -- Transport changes only the kernel index, so it preserves the ambient tangent vector.
    have hcast {y y' : Z} (h : y = y') (e : V z.proj ≃L[ℝ] K y) :
        ((show V z.proj ≃L[ℝ] K y' from h ▸ e) v).val = (e v).val := by
      subst y'
      rfl
    exact hcast (hpoint z) (L₀ z)
  let ρ (z : TotalSpace R W) (t : ℝ) : Z :=
    a.symm ⟨z.proj.proj, z.proj.snd + t • (show V z.proj.proj from z.snd)⟩
  have hρ0 (z : TotalSpace R W) : ρ z 0 = a.symm z.proj := by simp [ρ]
  have hρ : ContMDiff ((A.prod 𝓘(ℝ, R)).prod 𝓘(ℝ, ℝ)) J ∞
      (Function.uncurry ρ) := by
    apply ha.2.2.2.2.2.comp
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    have hsource : ContMDiffAt ((A.prod 𝓘(ℝ, R)).prod 𝓘(ℝ, ℝ)) A ∞
        (fun w : TotalSpace R W × ℝ ↦ w.1.proj) z :=
      (Bundle.contMDiffAt_proj W).comp z contMDiffAt_fst
    have hbase : ContMDiffAt ((A.prod 𝓘(ℝ, R)).prod 𝓘(ℝ, ℝ)) I ∞
        (fun w : TotalSpace R W × ℝ ↦ w.1.proj.proj) z :=
      (Bundle.contMDiffAt_proj V).comp z hsource
    refine ⟨hbase, ?_⟩
    let t := trivializationAt R V z.1.proj.proj
    have hv := (Bundle.contMDiffAt_totalSpace.mp hsource).2
    have hw := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_fst : ContMDiffAt ((A.prod 𝓘(ℝ, R)).prod 𝓘(ℝ, ℝ))
        (A.prod 𝓘(ℝ, R)) ∞ (fun w : TotalSpace R W × ℝ ↦ w.1) z)).2
    apply (hv.add (contMDiffAt_snd.smul hw)).congr_of_eventuallyEq
    filter_upwards [hbase.continuousAt (t.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt R V z.1.proj.proj))] with w hw
    change (t ⟨w.1.proj.proj, w.1.proj.snd + w.2 • (show V w.1.proj.proj from w.1.snd)⟩).2 =
      (t w.1.proj).2 + w.2 • (t ⟨w.1.proj.proj, w.1.snd⟩).2
    simp only [← t.continuousLinearMapAt_apply_of_mem ℝ hw, map_add, map_smul]
  have hradial (z : TotalSpace R W) :
      (mfderiv 𝓘(ℝ, ℝ) J (ρ z) 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R) =
          (L z.proj z.snd).val := by
    let i : OrthogonalSphere r → Z :=
      associatedBundleMk G P (OrthogonalSphere r) (p z.proj.proj)
    let u := half ((frame z.proj.proj).symm z.snd)
    let l (t : ℝ) : R := u₀ z.proj + t • u
    let dl : ℝ →L[ℝ] R := (ContinuousLinearMap.id ℝ ℝ).smulRight u
    have hl₀ : l 0 = u₀ z.proj := by simp [l]
    have hl : HasFDerivAt l dl 0 := dl.hasFDerivAt.const_add (u₀ z.proj)
    have hfun : ρ z = i ∘ b.symm ∘ l := by
      funext t
      have hc := frameSphereStereographic_symm_two_smul (EB := EB) r V
        (p z.proj.proj) (l t)
      have hvec : (2 : ℝ) • (frame z.proj.proj) (l t) =
          z.proj.snd + t • (show V z.proj.proj from z.snd) := by
        change (2 : ℝ) • (frame z.proj.proj)
          ((1 / 2 : ℝ) • (frame z.proj.proj).symm z.proj.snd +
            t • ((1 / 2 : ℝ) • (frame z.proj.proj).symm z.snd)) = _
        rw [map_add, map_smul, map_smul, map_smul,
          (frame z.proj.proj).apply_symm_apply, (frame z.proj.proj).apply_symm_apply,
          smul_add, smul_smul, smul_smul, smul_smul]
        norm_num
        congr 1
        ring
      rw [hvec] at hc
      exact hc
    have hi := (smoothAssociatedSphereFiberInclusion S (p z.proj.proj)).contMDiff
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 r) (I'' := J) 0
      ((hi.comp hb.2).mdifferentiable (by simp) (l 0)) hl.hasMFDerivAt.mdifferentiableAt
    rw [hl₀, hl.hasMFDerivAt.mfderiv] at hchain
    have hchain₂ := mfderiv_comp (I := 𝓡 r) (I' := 𝓡 r) (I'' := J) (u₀ z.proj)
      (hi.mdifferentiable (by simp) _) (hb.2.mdifferentiable (by simp) _)
    rw [hchain₂] at hchain
    have hd := DFunLike.congr_fun hchain
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
    have hfder := congrArg (fun k : ℝ → Z ↦
      (mfderiv 𝓘(ℝ, ℝ) J k 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R))
        hfun
    have hunit : dl ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = u := by
      change (1 : ℝ) • u = u
      exact one_smul ℝ u
    have he := (exists_associatedSphereFiberTangentEquiv S (p z.proj.proj)
      (b.symm (u₀ z.proj))).choose_spec (db z.proj u)
    apply hfder.trans
    calc
      (mfderiv 𝓘(ℝ, ℝ) J ((i ∘ b.symm) ∘ l) 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R) =
        (mfderiv (𝓡 r) J i (b.symm (u₀ z.proj)) : R →L[ℝ] EB × R)
          (db z.proj (dl ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1))) := hd
      _ = (mfderiv (𝓡 r) J i (b.symm (u₀ z.proj)) : R →L[ℝ] EB × R)
          (db z.proj u) := congrArg (fun v : R ↦
            (mfderiv (𝓡 r) J i (b.symm (u₀ z.proj)) : R →L[ℝ] EB × R) (db z.proj v)) hunit
      _ = (L z.proj z.snd).val := he.symm.trans (hLval z.proj z.snd).symm
  -- Differentiating the global affine family supplies ambient smoothness.
  have hLambient : ContMDiff (A.prod 𝓘(ℝ, R)) (A.prod 𝓘(ℝ, EB × R)) ∞
      (fun z : TotalSpace R W ↦ (⟨z.proj, (L z.proj z.snd).val⟩ :
        TotalSpace (EB × R) T)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj W, ?_⟩
    have hd := ContMDiffAt.mfderiv_apply ρ (fun _ : TotalSpace R W ↦ (0 : ℝ)) id
      (fun _ : TotalSpace R W ↦ (1 : ℝ)) (hρ (z, 0)) contMDiffAt_const contMDiffAt_id
      contMDiffAt_const (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
    apply hd.congr_of_eventuallyEq
    let t := trivializationAt (EB × R) (TangentSpace J) (a.symm z.proj)
    have hbase := ha.2.2.2.2.2.contMDiffAt.comp z (Bundle.contMDiffAt_proj W)
    filter_upwards [hbase.continuousAt (t.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (EB × R) (TangentSpace J) (a.symm z.proj)))] with w hw
    dsimp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq,
      ContinuousLinearMap.comp_apply]
    rw [TangentBundle.symmL_model_space]
    change (t ⟨a.symm w.proj, (L w.proj w.snd).val⟩).2 =
      (trivializationAt (EB × R) (TangentSpace J) (ρ z 0)).continuousLinearMapAt ℝ (ρ w 0)
        (mfderiv 𝓘(ℝ, ℝ) J (ρ w) 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))
    rw [hradial, hρ0 z, hρ0 w]
    exact (t.continuousLinearMapAt_apply_of_mem ℝ hw _).symm
  have hinc : ContMDiff (A.prod 𝓘(ℝ, D)) (A.prod 𝓘(ℝ, EB × R)) ∞
      (fun z : TotalSpace D Y ↦ (⟨z.proj, z.snd.val⟩ : TotalSpace (EB × R) T)) := by
    have hlift : ContMDiff (A.prod 𝓘(ℝ, D)) (J.prod 𝓘(ℝ, D)) ∞
        (fun z : TotalSpace D Y ↦ (⟨a.symm z.proj, z.snd⟩ : TotalSpace D K)) := by
      intro z
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨ha.2.2.2.2.2.contMDiffAt.comp z (Bundle.contMDiffAt_proj Y), ?_⟩
      exact (Bundle.contMDiffAt_totalSpace.mp
        (show ContMDiffAt (A.prod 𝓘(ℝ, D)) (A.prod 𝓘(ℝ, D)) ∞ id z
          from contMDiffAt_id)).2
    have h := (smoothVerticalTangentInclusion q hq).contMDiff.comp hlift
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨Bundle.contMDiffAt_proj Y, (Bundle.contMDiffAt_totalSpace.mp (h z)).2⟩
  -- Keep the original product model when detecting smoothness in the native subbundle.
  have hL : ContMDiff (A.prod 𝓘(ℝ, R)) (A.prod 𝓘(ℝ, D)) ∞
      (fun z : TotalSpace R W ↦ (⟨z.proj, L z.proj z.snd⟩ : TotalSpace D Y)) := by
    apply contMDiff_bundleMap_of_comp_injective (I := A)
      (W := Y) (V₀ := T) («Z» := W) (F := D) («G» := EB × R) (H := R)
      (fun z ↦ (LinearMap.ker (mfderiv J I q (a.symm z)).toLinearMap).subtypeL)
      (fun z ↦ (L z).toContinuousLinearMap) hinc (fun _ ↦ Subtype.val_injective)
    exact hLambient
  refine ⟨L, fun z v ↦ (hradial ⟨z, v⟩).symm, hL, ?_⟩
  -- The inverse is detected by the same injection: its forward composite is the identity.
  apply contMDiff_bundleMap_of_comp_injective (I := A)
    (W := W) (V₀ := Y) («Z» := Y) (F := R) («G» := D) (H := D)
    (fun z ↦ (L z).toContinuousLinearMap) (fun z ↦ (L z).symm.toContinuousLinearMap)
    hL (fun z ↦ (L z).injective)
  apply contMDiff_id.congr
  intro z
  change (⟨z.proj, L z.proj ((L z.proj).symm z.snd)⟩ : TotalSpace D Y) = z
  rw [(L z.proj).apply_symm_apply]

end AtiyahSinger

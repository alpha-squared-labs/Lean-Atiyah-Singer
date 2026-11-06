/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedTubularNeighborhood
public import AtiyahSinger.Geometry.TransverseNormalPullback

/-!
# The normal quotient of the zero-time-velocity square

Public module ID: M1520.

The tangent map of a time-preserving embedding preserves time velocity. Its
restriction to zero time velocities therefore has the same normal quotient,
through the actual derivative of the zero-velocity inclusion. The native
product tangent diffeomorphism fixes the coordinate identification explicitly.

This is the transverse normal-bundle comparison needed for the tangent cylinder
in SG III.13. No normal-space identification is inferred merely from its rank.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] productFullChartedSpace product_full_isManifold
  tangentBundleFullChartedSpace tangentBundle_full_isManifold normalBundleTopology

section Coordinates

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Reorder the original product tangent coordinates with time velocity first. -/
def parameterVelocityDiffeomorph :
    (ℝ × (ℝ × TangentBundle 𝓘(ℝ, E) M)) ≃ₘ⟮𝓘(ℝ, ℝ × (ℝ × (E × E))),
      𝓘(ℝ, (ℝ × E) × (ℝ × E))⟯ TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × M) where
  toFun p := ⟨(p.2.1, p.2.2.proj), (p.1, p.2.2.snd)⟩
  invFun z := (z.snd.1, (z.proj.1, ⟨z.proj.2, z.snd.2⟩))
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    have hreal : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)).tangent ∞
        (fun p : ℝ × ℝ ↦ (⟨p.1, p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      rw [chartedSpaceSelf_prod]
      exact contMDiff_tangentBundleModelSpaceHomeomorph_symm
    have hcoord : ContMDiff
        (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E)).tangent))
        ((𝓘(ℝ, ℝ)).tangent.prod (𝓘(ℝ, E)).tangent) ∞
        (fun p : ℝ × (ℝ × TangentBundle 𝓘(ℝ, E) M) ↦
          ((⟨p.2.1, p.1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ), p.2.2)) :=
      (hreal.comp (contMDiff_snd.fst.prodMk contMDiff_fst)).prodMk contMDiff_snd.snd
    have h := (contMDiff_equivTangentBundleProd_symm (n := ∞)
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))).comp hcoord
    simpa only [ModelWithCorners.tangent, modelWithCornersSelf_prod] using! h
  contMDiff_invFun := by
    have hreal : ContMDiff (𝓘(ℝ, ℝ)).tangent (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : TangentBundle 𝓘(ℝ, ℝ) ℝ ↦ (z.proj, z.snd)) := by
      rw [chartedSpaceSelf_prod]
      exact contMDiff_tangentBundleModelSpaceHomeomorph
    have h := hreal.prodMap (contMDiff_id (I := (𝓘(ℝ, E)).tangent)
      (M := TangentBundle 𝓘(ℝ, E) M))
    have k := h.comp (contMDiff_equivTangentBundleProd (n := ∞)
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)))
    have l := k.fst.snd.prodMk (k.fst.fst.prodMk k.snd)
    simpa only [ModelWithCorners.tangent, modelWithCornersSelf_prod] using! l

/-- The actual inclusion of the zero-time-velocity submanifold. -/
def zeroVelocityInclusion :
    ContMDiffMap 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, (ℝ × E) × (ℝ × E))
      (ℝ × TangentBundle 𝓘(ℝ, E) M) (TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × M)) ∞ :=
  ⟨fun p ↦ parameterVelocityDiffeomorph E M (0, p), by
    apply (parameterVelocityDiffeomorph E M).contMDiff.comp
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_const.prodMk contMDiff_id :
        ContMDiff 𝓘(ℝ, ℝ × (E × E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × (E × E))) ∞
          (fun p : ℝ × TangentBundle 𝓘(ℝ, E) M ↦ ((0 : ℝ), p)))⟩

end Coordinates

section NormalComparison

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to zero time velocity preserves the actual normal quotient of a tangent map. -/
theorem exists_zeroVelocity_normalEquiv
    (β : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞)
    (hβ : IsSmoothEmbedding 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ β)
    (H : ContMDiffMap 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F))
      (ℝ × TangentBundle 𝓘(ℝ, E) M) (ℝ × TangentBundle 𝓘(ℝ, F) N) ∞)
    (hH : IsImmersion 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) ∞ H)
    (htime : ∀ p, (β p).1 = p.1)
    (hfactor : ∀ p, zeroVelocityInclusion F N (H p) =
      smoothTangentMap β (zeroVelocityInclusion E M p)) :
    let i := zeroVelocityInclusion E M
    let j := zeroVelocityInclusion F N
    let g := smoothTangentMap β
    letI := normalBundleFiberBundle H hH
    letI := normalBundleVectorBundle H hH
    letI := normalBundleContMDiffVectorBundle H hH
    letI := normalBundleFiberBundle g (isImmersion_smoothTangentMap β hβ)
    letI := normalBundleVectorBundle g (isImmersion_smoothTangentMap β hβ)
    letI := normalBundleContMDiffVectorBundle g (isImmersion_smoothTangentMap β hβ)
    ∃ e : ∀ p, NormalBundle 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) H p ≃L[ℝ]
        NormalBundle 𝓘(ℝ, (ℝ × E) × (ℝ × E)) 𝓘(ℝ, (ℝ × F) × (ℝ × F)) g (i p),
      (∀ p v,
        e p ((LinearMap.range (mfderiv 𝓘(ℝ, ℝ × (E × E))
          𝓘(ℝ, ℝ × (F × F)) H p).toLinearMap).mkQ v) =
            (LinearMap.range (mfderiv 𝓘(ℝ, (ℝ × E) × (ℝ × E))
              𝓘(ℝ, (ℝ × F) × (ℝ × F)) g (i p)).toLinearMap).mkQ
                (mfderiv 𝓘(ℝ, ℝ × (F × F)) 𝓘(ℝ, (ℝ × F) × (ℝ × F)) j (H p) v)) ∧
      ContMDiff (𝓘(ℝ, ℝ × (E × E)).prod
          𝓘(ℝ, NormalModel (ℝ × (E × E)) (ℝ × (F × F))))
        (𝓘(ℝ, ℝ × (E × E)).prod
          𝓘(ℝ, NormalModel ((ℝ × E) × (ℝ × E)) ((ℝ × F) × (ℝ × F)))) ∞
        (fun z : TotalSpace (NormalModel (ℝ × (E × E)) (ℝ × (F × F)))
            (NormalBundle 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) H) ↦
          (⟨z.proj, e z.proj z.snd⟩ :
            TotalSpace (NormalModel ((ℝ × E) × (ℝ × E)) ((ℝ × F) × (ℝ × F)))
              ((i : _ → _) *ᵖ (NormalBundle 𝓘(ℝ, (ℝ × E) × (ℝ × E))
                𝓘(ℝ, (ℝ × F) × (ℝ × F)) g)))) ∧
      ContMDiff (𝓘(ℝ, ℝ × (E × E)).prod
          𝓘(ℝ, NormalModel ((ℝ × E) × (ℝ × E)) ((ℝ × F) × (ℝ × F))))
        (𝓘(ℝ, ℝ × (E × E)).prod
          𝓘(ℝ, NormalModel (ℝ × (E × E)) (ℝ × (F × F)))) ∞
        (fun z : TotalSpace (NormalModel ((ℝ × E) × (ℝ × E)) ((ℝ × F) × (ℝ × F)))
            ((i : _ → _) *ᵖ (NormalBundle 𝓘(ℝ, (ℝ × E) × (ℝ × E))
              𝓘(ℝ, (ℝ × F) × (ℝ × F)) g)) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ :
            TotalSpace (NormalModel (ℝ × (E × E)) (ℝ × (F × F)))
              (NormalBundle 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) H))) := by
  classical
  let A := ℝ × (E × E)
  let B := ℝ × (F × F)
  let G := (ℝ × E) × (ℝ × E)
  let K := (ℝ × F) × (ℝ × F)
  let P := ℝ × TangentBundle 𝓘(ℝ, E) M
  let Q := ℝ × TangentBundle 𝓘(ℝ, F) N
  let CM := parameterVelocityDiffeomorph E M
  let CN := parameterVelocityDiffeomorph F N
  let i := zeroVelocityInclusion E M
  let j := zeroVelocityInclusion F N
  let g := smoothTangentMap β
  let k : ContMDiffMap 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × B) (ℝ × P) (ℝ × Q) ∞ :=
    ⟨fun z ↦ CN.symm (g (CM z)), CN.symm.contMDiff.comp (g.contMDiff.comp CM.contMDiff)⟩
  -- The full tangent map retains the derivative of the original time coordinate.
  have htimeDer (p : ℝ × M) (v : ℝ × E) :
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β p v).1 = v.1 := by
    have hfst : ContMDiff 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) ∞ (@Prod.fst ℝ N) := by
      simpa only [modelWithCornersSelf_prod] using
        (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
          (@Prod.fst ℝ N))
    have h := mfderiv_comp p (hfst.mdifferentiable (by simp) (β p))
      (β.contMDiff.mdifferentiable (by simp) p)
    have heq : (@Prod.fst ℝ N) ∘ β = @Prod.fst ℝ M := funext htime
    rw [heq] at h
    have hdM : mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) (@Prod.fst ℝ M) p =
        ContinuousLinearMap.fst ℝ ℝ E := by
      simpa only [modelWithCornersSelf_prod] using!
        (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (x := p))
    have hdN : mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) (@Prod.fst ℝ N) (β p) =
        ContinuousLinearMap.fst ℝ ℝ F := by
      simpa only [modelWithCornersSelf_prod] using!
        (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F)) (x := β p))
    rw [hdM, hdN] at h
    exact (congrArg (fun L ↦ L v) h).symm
  have hkTime (z : ℝ × P) : (k z).1 = z.1 := htimeDer _ _
  have hkZero (p : P) : k (0, p) = (0, H p) := by
    change CN.symm (g (i p)) = (0, H p)
    rw [← hfactor]
    exact CN.symm_apply_apply _
  let L (p : P) : (ℝ × A) →L[ℝ] (ℝ × B) :=
    mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × B) k (0, p)
  let dH (p : P) : A →L[ℝ] B := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, B) H p
  let dM (p : P) : (ℝ × A) ≃L[ℝ] G := CM.mfderivToContinuousLinearEquiv (by simp) (0, p)
  let dN (p : P) : (ℝ × B) ≃L[ℝ] K :=
    CN.mfderivToContinuousLinearEquiv (by simp) (0, H p)
  let dg (p : P) : G →L[ℝ] K := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, K) g (i p)
  let dj (p : P) : B →L[ℝ] K := mfderiv 𝓘(ℝ, B) 𝓘(ℝ, K) j (H p)
  have hLtime (p : P) (u : ℝ × A) : (L p u).1 = u.1 := by
    have hfst : ContMDiff 𝓘(ℝ, ℝ × B) 𝓘(ℝ, ℝ) ∞ (@Prod.fst ℝ Q) := by
      simpa only [modelWithCornersSelf_prod] using
        (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, B)) 𝓘(ℝ, ℝ) ∞
          (@Prod.fst ℝ Q))
    have h := mfderiv_comp (0, p) (hfst.mdifferentiable (by simp) (k (0, p)))
      (k.contMDiff.mdifferentiable (by simp) (0, p))
    have heq : (@Prod.fst ℝ Q) ∘ k = @Prod.fst ℝ P := funext hkTime
    rw [heq] at h
    have hdP : mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ) (@Prod.fst ℝ P) (0, p) =
        ContinuousLinearMap.fst ℝ ℝ A := by
      simpa only [modelWithCornersSelf_prod] using!
        (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, A)) (x := ((0 : ℝ), p)))
    have hdQ : mfderiv 𝓘(ℝ, ℝ × B) 𝓘(ℝ, ℝ) (@Prod.fst ℝ Q) (k (0, p)) =
        ContinuousLinearMap.fst ℝ ℝ B := by
      simpa only [modelWithCornersSelf_prod] using!
        (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, B)) (x := k (0, p)))
    rw [hdP, hdQ] at h
    exact (congrArg (fun T ↦ T u) h).symm
  -- Differentiate the same zero-velocity slice square, in the explicit native coordinates.
  have hLvertical (p : P) (u : A) : L p (0, u) = (0, dH p u) := by
    let s : ContMDiffMap 𝓘(ℝ, A) 𝓘(ℝ, ℝ × A) P (ℝ × P) ∞ :=
      ⟨fun x ↦ (0, x), by
        simpa only [modelWithCornersSelf_prod] using
          (contMDiff_const.prodMk contMDiff_id : ContMDiff 𝓘(ℝ, A)
            (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A)) ∞ (fun x : P ↦ ((0 : ℝ), x)))⟩
    have hs : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℝ × A) s p = ContinuousLinearMap.inr ℝ ℝ A := by
      have h := mfderiv_prodMk (I := 𝓘(ℝ, A)) (I' := 𝓘(ℝ, ℝ))
        (I'' := 𝓘(ℝ, A)) (f := fun _ : P ↦ (0 : ℝ)) (g := id) (x := p)
        mdifferentiableAt_const mdifferentiableAt_id
      rw [mfderiv_const, mfderiv_id] at h
      simpa only [modelWithCornersSelf_prod] using! h
    have hcomp := mfderiv_comp p (k.contMDiff.mdifferentiable (by simp) (0, p))
      (s.contMDiff.mdifferentiable (by simp) p)
    have heq : (k : _ → _) ∘ s = fun x ↦ ((0 : ℝ), H x) := funext hkZero
    change mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℝ × B) ((k : _ → _) ∘ s) p =
      (L p).comp (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℝ × A) s p) at hcomp
    rw [heq, hs] at hcomp
    have hout := mfderiv_prodMk (I := 𝓘(ℝ, A)) (I' := 𝓘(ℝ, ℝ))
      (I'' := 𝓘(ℝ, B)) (f := fun _ : P ↦ (0 : ℝ)) (g := H) (x := p)
      mdifferentiableAt_const (H.contMDiff.mdifferentiable (by simp) p)
    rw [mfderiv_const] at hout
    have hout' : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℝ × B) (fun x ↦ ((0 : ℝ), H x)) p =
        (0 : A →L[ℝ] ℝ).prod (dH p) := by
      simpa only [modelWithCornersSelf_prod] using! hout
    rw [hout'] at hcomp
    exact (congrArg (fun T ↦ T u) hcomp).symm
  have hchain (p : P) (u : ℝ × A) : dg p (dM p u) = dN p (L p u) := by
    have heq : (g : _ → _) ∘ CM = (CN : _ → _) ∘ k := by
      funext z
      exact (CN.apply_symm_apply (g (CM z))).symm
    have hm := mfderiv_comp (0, p) (g.contMDiff.mdifferentiable (by simp) (CM (0, p)))
      (CM.contMDiff.mdifferentiable (by simp) (0, p))
    have hn := mfderiv_comp (0, p) (CN.contMDiff.mdifferentiable (by simp) (k (0, p)))
      (k.contMDiff.mdifferentiable (by simp) (0, p))
    rw [heq, hn, hkZero] at hm
    have hdM : (dM p).toContinuousLinearMap =
        mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, G) CM (0, p) :=
      CM.mfderivToContinuousLinearEquiv_coe (by simp)
    have hdN : (dN p).toContinuousLinearMap =
        mfderiv 𝓘(ℝ, ℝ × B) 𝓘(ℝ, K) CN (0, H p) :=
      CN.mfderivToContinuousLinearEquiv_coe (by simp)
    rw [← hdM, ← hdN] at hm
    exact (congrArg (fun T ↦ T u) hm).symm
  have hj (p : P) (v : B) : dj p v = dN p (0, v) := by
    have hs : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ × B) ∞ (fun x : Q ↦ ((0 : ℝ), x)) := by
      simpa only [modelWithCornersSelf_prod] using
        (contMDiff_const.prodMk contMDiff_id : ContMDiff 𝓘(ℝ, B)
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, B)) ∞ (fun x : Q ↦ ((0 : ℝ), x)))
    have hd : mfderiv 𝓘(ℝ, B) 𝓘(ℝ, ℝ × B) (fun x : Q ↦ ((0 : ℝ), x)) (H p) =
        ContinuousLinearMap.inr ℝ ℝ B := by
      have h := mfderiv_prodMk (I := 𝓘(ℝ, B)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, B))
        (f := fun _ : Q ↦ (0 : ℝ)) (g := id) (x := H p)
        mdifferentiableAt_const mdifferentiableAt_id
      rw [mfderiv_const, mfderiv_id] at h
      simpa only [modelWithCornersSelf_prod] using! h
    have h := mfderiv_comp (H p) (CN.contMDiff.mdifferentiable (by simp) (0, H p))
      (hs.mdifferentiable (by simp) (H p))
    rw [hd] at h
    have hdN : (dN p).toContinuousLinearMap =
        mfderiv 𝓘(ℝ, ℝ × B) 𝓘(ℝ, K) CN (0, H p) :=
      CN.mfderivToContinuousLinearEquiv_coe (by simp)
    rw [← hdN] at h
    exact congrArg (fun T ↦ T v) h
  -- The velocity coordinate detects the exact tangent range preimage.
  have hpreimage (p : P) (v : B) : dj p v ∈ LinearMap.range (dg p).toLinearMap ↔
      v ∈ LinearMap.range (dH p).toLinearMap := by
    constructor
    · rintro ⟨u, hu⟩
      let w := (dM p).symm u
      have heq : L p w = (0, v) := by
        apply (dN p).injective
        rw [← hj, ← hchain]
        exact ((dM p).apply_symm_apply u ▸ hu)
      have ht : w.1 = 0 := by rw [← hLtime, heq]
      have hw : w = (0, w.2) := Prod.ext ht rfl
      refine ⟨w.2, ?_⟩
      rw [hw, hLvertical] at heq
      exact congrArg Prod.snd heq
    · rintro ⟨u, rfl⟩
      refine ⟨dM p (0, u), ?_⟩
      change dg p (dM p (0, u)) = dj p (dH p u)
      rw [hchain, hLvertical, hj]
  have hspan (p : P) (w : K) : ∃ (v : B) (u : G), w = dj p v + dg p u := by
    let z := (dN p).symm w
    refine ⟨z.2 - (L p (z.1, 0)).2, dM p (z.1, 0), ?_⟩
    rw [hj, hchain, ← map_add]
    have hz : (0, z.2 - (L p (z.1, 0)).2) + L p (z.1, 0) = z := by
      apply Prod.ext
      · change 0 + (L p (z.1, 0)).1 = z.1
        rw [zero_add, hLtime]
      · exact sub_add_cancel _ _
    rw [hz]
    exact ((dN p).apply_symm_apply w).symm
  exact exists_transverse_normalPullback_equiv H g i j hH
    (isImmersion_smoothTangentMap β hβ) hfactor hpreimage hspan

end NormalComparison

end AtiyahSinger

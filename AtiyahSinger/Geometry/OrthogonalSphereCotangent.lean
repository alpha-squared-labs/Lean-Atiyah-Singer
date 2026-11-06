/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import AtiyahSinger.Geometry.OrthogonalSphereParametric
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The actual orthogonal action on the cotangent bundle of the sphere

Public module ID: M1335.

The lifted action sends `(z, ξ)` to `(A • z, ξ ∘ d(A⁻¹)_(A • z))`.
It reuses the existing native `CotangentTotalSpace` and `cotangentDiffeomorphMap`;
the model covector is not left unchanged. The projection is equivariant by the
defining formula. All total spaces retain their original Hom-bundle topologies.

SG III.13, pages 251--252, uses this action on `T*S^r` in the associated
vertical cotangent bundle. The explicit smooth-family assertion is a standard
cotangent-lift supplement. It uses smooth orthogonal matrix entries, without
requiring a smooth atlas on the matrix orthogonal group. Rank zero is retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Topology
open scoped Manifold ContDiff

/-- The original orthogonal sphere transformation and inverse, as a native diffeomorphism. -/
def orthogonalSphereDiffeomorph (r : ℕ) (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    OrthogonalSphere r ≃ₘ⟮𝓡 r, 𝓡 r⟯ OrthogonalSphere r where
  toFun z := A • z
  invFun z := A⁻¹ • z
  left_inv z := inv_smul_smul A z
  right_inv z := smul_inv_smul A z
  contMDiff_toFun := contMDiff_orthogonalSphere_smul r A
  contMDiff_invFun := contMDiff_orthogonalSphere_smul r A⁻¹

/-- The actual inverse-differential cotangent lift of the specified orthogonal action. -/
def orthogonalSphereCotangentMap (r : ℕ) (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    CotangentTotalSpace (n := r) (M := OrthogonalSphere r) →
      CotangentTotalSpace (n := r) (M := OrthogonalSphere r) :=
  cotangentDiffeomorphMap (orthogonalSphereDiffeomorph r A)

/-- The same inverse-differential cotangent transport, registered as the scalar action. -/
instance (priority := 1100) orthogonalSphereCotangentSMul (r : ℕ) :
    SMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) where
  smul := orthogonalSphereCotangentMap r

/-- Cotangent functoriality gives an action using the actual inverse-differential maps. -/
instance orthogonalSphereCotangentMulAction (r : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) where
  smul := orthogonalSphereCotangentMap r
  one_smul z := by
    -- Identify the original sphere identity before differentiating its inverse.
    have h : orthogonalSphereDiffeomorph r 1 =
        Diffeomorph.refl (𝓡 r) (OrthogonalSphere r) ∞ := by
      apply Diffeomorph.ext
      intro x
      exact one_smul (Matrix.orthogonalGroup (Fin r) ℝ) x
    change cotangentDiffeomorphMap (orthogonalSphereDiffeomorph r 1) z = z
    rw [h]
    change (⟨z.proj, z.snd.comp
      (mfderiv (𝓡 r) (𝓡 r) (id : OrthogonalSphere r → OrthogonalSphere r) z.proj)⟩ :
      CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) = z
    rw [mfderiv_id]
    simp
  mul_smul A B z := by
    -- Existing cotangent functoriality already retains the inverse derivative order.
    have h : orthogonalSphereDiffeomorph r (A * B) =
        (orthogonalSphereDiffeomorph r B).trans (orthogonalSphereDiffeomorph r A) := by
      apply Diffeomorph.ext
      intro x
      exact mul_smul A B x
    change cotangentDiffeomorphMap (orthogonalSphereDiffeomorph r (A * B)) z =
      cotangentDiffeomorphMap (orthogonalSphereDiffeomorph r A)
        (cotangentDiffeomorphMap (orthogonalSphereDiffeomorph r B) z)
    rw [h]
    exact congrArg (fun e ↦ e z)
      (cotangentDiffeomorph_trans
        (orthogonalSphereDiffeomorph r B) (orthogonalSphereDiffeomorph r A))

/-- The lifted action is jointly continuous for the native matrix and cotangent topologies. -/
theorem continuousSMul_orthogonalSphereCotangent (r : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) := by
  /- Stage 1: extend the original block action to full matrix parameters
  by radial normalization of its nonzero ambient image. The fallback
  disappears near orthogonal matrices, where the image has unit norm.
  Native target charts make this family smooth as a sphere-valued map.
  It agrees exactly with the specified orthogonal action.
  Stage 2: differentiate this smooth extension only in the sphere
  variable, using the inverse orthogonal matrix as parameter. The
  resulting native derivative coordinates vary continuously with
  that parameter and the transformed point.
  Stage 3: compose the original covector with the same inverse
  differential in the original Hom-bundle charts. Together with
  continuity of the transformed base, this proves joint continuity
  without a Lie-group atlas or a change of cotangent topology. -/
  classical
  -- Extend the same action locally to full matrix parameters before differentiating.
  have hRadial :
      ∃ F : (Fin r → Fin r → ℝ) → OrthogonalSphere r → OrthogonalSphere r,
        (∀ A : Matrix.orthogonalGroup (Fin r) ℝ, F A.val = fun z ↦ A • z) ∧
        ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : OrthogonalSphere r),
          ContMDiffAt ((𝓘(ℝ, Fin r → Fin r → ℝ)).prod (𝓡 r)) (𝓡 r) ∞
            (Function.uncurry F) (A.val, z) := by
    classical
    let Mat := Fin r → Fin r → ℝ
    let V := EuclideanSpace ℝ (Fin r)
    let W := OrthogonalSphereAmbient r
    let I := (𝓘(ℝ, Mat)).prod (𝓡 r)
    -- Native target charts transfer pointwise ambient regularity to sphere regularity.
    have hSphereAt (g : Mat × OrthogonalSphere r → OrthogonalSphere r)
        (p : Mat × OrthogonalSphere r)
        (hg : ContMDiffAt I 𝓘(ℝ, W) ∞ (fun q ↦ (g q).val) p) :
        ContMDiffAt I (𝓡 r) ∞ g p := by
      rw [contMDiffAt_iff_target]
      refine ⟨tendsto_subtype_rng.mpr hg.continuousAt, ?_⟩
      let v : OrthogonalSphere r := g p
      let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
        r (ne_zero_of_mem_unit_sphere (-v))).repr
      have hPole : inner (𝕜 := ℝ) (-(v : W)) (v : W) ≠ 1 := by
        rw [inner_neg_left, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]
        norm_num
      have hStereo : ContDiffAt ℝ ∞ (stereoToFun (-(v : W))) (v : W) :=
        contDiffOn_stereoToFun.contDiffAt
          ((isOpen_ne.preimage (innerSL ℝ (-(v : W))).continuous).mem_nhds hPole)
      change ContMDiffAt I (𝓡 r) ∞
        (fun q ↦ U (stereoToFun (-(v : W)) (g q).val)) p
      have hCoordinate : ContDiffAt ℝ ∞
          (fun w : W ↦ U (stereoToFun (-(v : W)) w)) (v : W) :=
        U.contDiff.contDiffAt.comp (v : W) hStereo
      exact ContMDiffAt.comp (f := fun q ↦ (g q).val)
        (g := fun w : W ↦ U (stereoToFun (-(v : W)) w)) p
        hCoordinate.contMDiffAt hg
    let matrixMap : Mat ≃L[ℝ] (V →L[ℝ] V) :=
      LinearEquiv.toContinuousLinearEquiv
        (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv
    let split := WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ
    let ambient (p : Mat × OrthogonalSphere r) : W :=
      split.symm (matrixMap p.1 p.2.val.fst, p.2.val.snd)
    -- All matrix entries are free parameters in this ambient smooth family.
    have hMatrix : ContMDiff I 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun p : Mat × OrthogonalSphere r ↦ matrixMap p.1) :=
      matrixMap.contDiff.contMDiff.comp contMDiff_fst
    have hSphere : ContMDiff I 𝓘(ℝ, W) ∞
        (fun p : Mat × OrthogonalSphere r ↦ p.2.val) :=
      contMDiff_coe_sphere.comp contMDiff_snd
    have hHorizontal : ContMDiff I 𝓘(ℝ, V) ∞
        (fun p : Mat × OrthogonalSphere r ↦ p.2.val.fst) :=
      (ContinuousLinearMap.fst ℝ V ℝ).contDiff.contMDiff.comp
        (split.contDiff.contMDiff.comp hSphere)
    have hVertical : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun p : Mat × OrthogonalSphere r ↦ p.2.val.snd) :=
      (ContinuousLinearMap.snd ℝ V ℝ).contDiff.contMDiff.comp
        (split.contDiff.contMDiff.comp hSphere)
    have hAmbient : ContMDiff I 𝓘(ℝ, W) ∞ ambient :=
      split.symm.contDiff.contMDiff.comp
        ((hMatrix.clm_apply hHorizontal).prodMk_space hVertical)
    let F (P : Mat) (z : OrthogonalSphere r) : OrthogonalSphere r :=
      if h : ambient (P, z) = 0 then orthogonalSphereNorth r
      else ⟨NormedSpace.normalize (ambient (P, z)), by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize h⟩
    have hOpen : IsOpen {p : Mat × OrthogonalSphere r | ambient p ≠ 0} :=
      isOpen_ne.preimage hAmbient.continuous
    -- On this open locus the fallback disappears and radial normalization is smooth.
    have hSmooth (p : Mat × OrthogonalSphere r) (hp : ambient p ≠ 0) :
        ContMDiffAt I (𝓡 r) ∞ (Function.uncurry F) p := by
      have hNormalize : ContDiffAt ℝ ∞ (NormedSpace.normalize : W → W) (ambient p) :=
        ((contDiffAt_norm ℝ hp).inv (norm_ne_zero_iff.mpr hp)).smul contDiffAt_id
      have hValue : ContMDiffAt I 𝓘(ℝ, W) ∞
          (fun q : Mat × OrthogonalSphere r ↦ (F q.1 q.2).val) p := by
        apply (hNormalize.contMDiffAt.comp p hAmbient.contMDiffAt).congr_of_eventuallyEq
        filter_upwards [hOpen.mem_nhds hp] with q hq
        simp only [F, dite_eq_right hq]
        rfl
      exact hSphereAt (Function.uncurry F) p hValue
    have hOriginal (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : OrthogonalSphere r) :
        ambient (A.val, z) = (A • z).val := rfl
    have hNonzero (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : OrthogonalSphere r) :
        ambient (A.val, z) ≠ 0 := by
      rw [hOriginal]
      exact ne_zero_of_mem_unit_sphere (A • z)
    refine ⟨F, ?_, ?_⟩
    · -- Unit norm makes the extension exactly the already specified orthogonal action.
      intro A
      funext z
      apply Subtype.ext
      simp only [F, dite_eq_right (hNonzero A z)]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one
        (norm_eq_of_mem_sphere (A • z))
    · intro A z
      exact hSmooth (A.val, z) (hNonzero A z)
  obtain ⟨F, hFeq, hFsmooth⟩ := hRadial
  let Mat := Fin r → Fin r → ℝ
  let J := 𝓡 r
  let V := EuclideanSpace ℝ (Fin r)
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let Q := G × CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
  let D (A : G) := orthogonalSphereDiffeomorph r A
  have hD (A : G) (z : OrthogonalSphere r) : D A z = A • z := rfl
  have hInverseSlice (A : G) : F A⁻¹.val = (D A).symm := hFeq A⁻¹
  let := continuousSMul_orthogonalSphere r
  constructor
  change Continuous (fun q : Q ↦ cotangentDiffeomorphMap (D q.1) q.2)
  clear_value D
  apply continuous_iff_continuousAt.mpr
  intro q₀
  -- The original sphere action controls the base point and the native covector frame.
  have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
    (fun q : Q ↦ q.2) (x₀ := q₀)).mp continuousAt_snd
  have hbase : ContinuousAt (fun q : Q ↦ D q.1 q.2.proj) q₀ := by
    have h : ContinuousAt (fun q : Q ↦ q.1 • q.2.proj) q₀ :=
      continuousAt_fst.smul hsource.1
    simpa only [hD] using h
  let a := trivializationAt V (TangentSpace J) q₀.2.proj
  let b := trivializationAt V (TangentSpace J) (D q₀.1 q₀.2.proj)
  have hξ : ContinuousAt (fun q : Q ↦ q.2.snd.comp (a.symmL ℝ q.2.proj)) q₀ := by
    have h := hsource.2
    change ContinuousAt (fun q : Q ↦
      ((Bundle.Trivial.trivialization (OrthogonalSphere r) ℝ).continuousLinearMapAt ℝ
        q.2.proj).comp (q.2.snd.comp (a.symmL ℝ q.2.proj))) q₀ at h
    simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_comp] using h
  let parameter (q : Q) : Mat × OrthogonalSphere r := (q.1⁻¹.val, D q.1 q.2.proj)
  have hparameter : ContinuousAt parameter q₀ :=
    (continuous_subtype_val.continuousAt.comp continuousAt_fst.inv).prodMk hbase
  -- Differentiate the smooth full-matrix extension only in its sphere variable.
  have hfamily : ContMDiffAt (((𝓘(ℝ, Mat)).prod J).prod J) J ∞
      (fun p : (Mat × OrthogonalSphere r) × OrthogonalSphere r ↦ F p.1.1 p.2)
      (parameter q₀, (parameter q₀).2) :=
    ContMDiffAt.comp
      (f := fun p : (Mat × OrthogonalSphere r) × OrthogonalSphere r ↦ (p.1.1, p.2))
      (g := Function.uncurry F) (parameter q₀, (parameter q₀).2)
      (hFsmooth q₀.1⁻¹ (D q₀.1 q₀.2.proj))
      (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
  have hd := ContMDiffAt.mfderiv
    (fun p : Mat × OrthogonalSphere r ↦ fun z : OrthogonalSphere r ↦ F p.1 z)
    (fun p ↦ p.2) hfamily
    (contMDiffAt_snd (I := 𝓘(ℝ, Mat)) (J := J))
    (m := (∞ : WithTop ℕ∞)) (by simp)
  let inverseCoordinates (q : Q) : V →L[ℝ] V :=
    (a.continuousLinearMapAt ℝ q.2.proj).comp
      ((mfderiv J J (D q.1).symm (D q.1 q.2.proj)).comp
        (b.symmL ℝ (D q.1 q.2.proj)))
  have hinverse : ContinuousAt inverseCoordinates q₀ := by
    have h := hd.continuousAt.comp hparameter
    apply h.congr
    filter_upwards [] with q
    dsimp only [Function.comp_apply, parameter, inTangentCoordinates]
    rw [hInverseSlice q₀.1, hInverseSlice q.1]
    simp only [ContinuousLinearMap.inCoordinates, Diffeomorph.symm_apply_apply]
    erw [(D q.1).symm_apply_apply]
    rfl
  -- Compose the same covector with the inverse differential in the original Hom coordinates.
  apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
  refine ⟨hbase, ?_⟩
  apply (hξ.clm_comp hinverse).congr_of_eventuallyEq
  filter_upwards [hsource.1.preimage_mem_nhds
    (a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with q hq
  apply ContinuousLinearMap.ext
  intro v
  have hscalar :
      (trivializationAt ℝ (fun _ : OrthogonalSphere r ↦ ℝ)
        (D q₀.1 q₀.2.proj)).continuousLinearMapAt ℝ (D q.1 q.2.proj) =
      ContinuousLinearMap.id ℝ ℝ := by
    change (Bundle.Trivial.trivialization (OrthogonalSphere r) ℝ).continuousLinearMapAt ℝ _ = _
    exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
  change ContinuousLinearMap.inCoordinates V (TangentSpace J)
      ℝ (Bundle.Trivial (OrthogonalSphere r) ℝ)
      (D q₀.1 q₀.2.proj) (D q.1 q.2.proj) (D q₀.1 q₀.2.proj) (D q.1 q.2.proj)
      (q.2.snd.comp (mfderiv J J (D q.1).symm (D q.1 q.2.proj))) v = _
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    hscalar, ContinuousLinearMap.id_apply]
  change q.2.snd ((mfderiv J J (D q.1).symm (D q.1 q.2.proj))
      (b.symmL ℝ (D q.1 q.2.proj) v)) =
    q.2.snd (a.symmL ℝ q.2.proj (a.continuousLinearMapAt ℝ q.2.proj
      ((mfderiv J J (D q.1).symm (D q.1 q.2.proj))
        (b.symmL ℝ (D q.1 q.2.proj) v))))
  erw [a.symmL_continuousLinearMapAt (R := ℝ) hq]

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  (I : ModelWithCorners ℝ E H) [hB : IsManifold I ∞ B]

include hB in
/-- Matrix families smooth on a parameter set lift smoothly to the sphere cotangent bundle. -/
theorem contMDiffOn_orthogonalSphereCotangent_parametric_smul (r : ℕ)
    (A : B → Matrix (Fin r) (Fin r) ℝ) (s : Set B)
    (hA : ContMDiffOn I 𝓘(ℝ, Fin r → Fin r → ℝ) ∞ (fun b i j ↦ A b i j) s)
    (horth : ∀ b : B, A b ∈ Matrix.orthogonalGroup (Fin r) ℝ) :
    ContMDiffOn (I.prod ((𝓡 r).prod 𝓘(ℝ, CotangentModel r)))
      ((𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
      (fun p : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦
        (⟨A p.1, horth p.1⟩ : Matrix.orthogonalGroup (Fin r) ℝ) • p.2)
      (s ×ˢ Set.univ) := by
  /- Stage 1: the original sphere action is jointly smooth on s times the
  sphere by the preceding theorem. The inverse family has the same regularity: orthogonality
  identifies its entries with the transpose of A(b), a fixed linear operation.
  Stage 2: differentiating that inverse family only in the sphere variable gives
  a family of linear maps smooth on s in the original tangent-bundle coordinates.
  Apply the native smooth parameter-dependent manifold derivative theorem;
  the sphere variable ranges over an open manifold chart, independently of s.
  Differentiating an infinitely smooth map does not exhaust its regularity.
  Stage 3: compose each original covector with that derivative at A(b) • z.
  Smooth Hom-bundle composition and the transformed base map give precisely
  the displayed cotangent lift in the original total-space atlas. No metric
  identifies tangent with cotangent, and no pointwise model vector replaces ξ. -/
  classical
  let J := 𝓡 r
  let K := J.prod 𝓘(ℝ, CotangentModel r)
  let D (b : B) := orthogonalSphereDiffeomorph r ⟨A b, horth b⟩
  let Ainv (b : B) : Matrix (Fin r) (Fin r) ℝ :=
    (⟨A b, horth b⟩ : Matrix.orthogonalGroup (Fin r) ℝ)⁻¹ |>.val
  -- Orthogonal inversion is the transpose of the same original matrix entries.
  have hAinv : ContMDiffOn I 𝓘(ℝ, Fin r → Fin r → ℝ) ∞ (fun b i j ↦ Ainv b i j) s := by
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    change ContMDiffOn I 𝓘(ℝ) ∞ (fun b ↦ A b j i) s
    exact contMDiffOn_pi_space.mp (contMDiffOn_pi_space.mp hA j) i
  have hforward := contMDiffOn_orthogonalSphere_parametric_smul I r A s hA horth
  have hinverse := contMDiffOn_orthogonalSphere_parametric_smul I r Ainv s hAinv
    (fun b ↦ (⟨A b, horth b⟩ : Matrix.orthogonalGroup (Fin r) ℝ)⁻¹ |>.property)
  have hD : ContMDiffOn (I.prod J) J ∞
      (fun p : B × OrthogonalSphere r ↦ D p.1 p.2) (s ×ˢ Set.univ) := hforward
  have hDinv : ContMDiffOn (I.prod J) J ∞
      (fun p : B × OrthogonalSphere r ↦ (D p.1).symm p.2) (s ×ˢ Set.univ) := hinverse
  change ContMDiffOn (I.prod K) K ∞
    (fun q : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦
      cotangentDiffeomorphMap (D q.1) q.2) (s ×ˢ Set.univ)
  -- Retain the same maps while keeping dependent coordinate identities abstract.
  clear_value D
  intro q₀ hq₀
  have hs : ContMDiffWithinAt (I.prod K) K ∞
      (fun q : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦ q.2)
      (s ×ˢ Set.univ) q₀ := contMDiffWithinAt_snd
  have hsource := (contMDiffWithinAt_hom_bundle (IB := J) _).mp hs
  have hbase : ContMDiffWithinAt (I.prod K) J ∞
      (fun q : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦
        D q.1 q.2.proj) (s ×ˢ Set.univ) q₀ :=
    (hD _ ⟨hq₀.1, Set.mem_univ _⟩).comp q₀
      (f := fun q : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦
        (q.1, q.2.proj)) (contMDiffWithinAt_fst.prodMk hsource.1)
      (fun _ hq ↦ ⟨hq.1, Set.mem_univ _⟩)
  let a := trivializationAt (EuclideanSpace ℝ (Fin r)) (TangentSpace J) q₀.2.proj
  have hξ : ContMDiffWithinAt (I.prod K) 𝓘(ℝ, CotangentModel r) ∞
      (fun q : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦
        q.2.snd.comp (a.symmL ℝ q.2.proj)) (s ×ˢ Set.univ) q₀ := by
    have h := hsource.2
    change ContMDiffWithinAt _ _ ∞
      (fun q : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦
        ((Bundle.Trivial.trivialization (OrthogonalSphere r) ℝ).continuousLinearMapAt ℝ
          q.2.proj).comp (q.2.snd.comp (a.symmL ℝ q.2.proj))) (s ×ˢ Set.univ) q₀ at h
    simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_comp] using h
  -- Differentiate only in the unrestricted sphere variable; s remains arbitrary.
  have hf : ContMDiffWithinAt ((I.prod K).prod J) J ∞
      (fun p : (B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) ×
        OrthogonalSphere r ↦ (D p.1.1).symm p.2)
      ((s ×ˢ Set.univ) ×ˢ Set.univ) (q₀, D q₀.1 q₀.2.proj) :=
    (hDinv _ ⟨hq₀.1, Set.mem_univ _⟩).comp _
      (f := fun p : (B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) ×
        OrthogonalSphere r ↦ (p.1.1, p.2))
      (contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd)
      (fun _ hp ↦ ⟨hp.1.1, Set.mem_univ _⟩)
  have hd := ContMDiffWithinAt.mfderivWithin
    (f := fun q : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) ↦
      fun x : OrthogonalSphere r ↦ (D q.1).symm x)
    (I' := J) hf hbase hq₀
    (Set.mapsTo_univ _ _) (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞) uniqueMDiffOn_univ
  simp only [mfderivWithin_univ] at hd
  -- Native Hom coordinates compose the original covector with this same inverse differential.
  apply (contMDiffWithinAt_hom_bundle _).mpr
  refine ⟨hbase, ?_⟩
  apply (hξ.clm_comp hd).congr_of_eventuallyEq_of_mem _ hq₀
  filter_upwards [hsource.1.continuousWithinAt.preimage_mem_nhdsWithin
    (a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with q hq
  apply ContinuousLinearMap.ext
  intro v
  have hscalar :
      (trivializationAt ℝ (fun _ : OrthogonalSphere r ↦ ℝ)
        (D q₀.1 q₀.2.proj)).continuousLinearMapAt ℝ (D q.1 q.2.proj) =
      ContinuousLinearMap.id ℝ ℝ := by
    change (Bundle.Trivial.trivialization (OrthogonalSphere r) ℝ).continuousLinearMapAt
      ℝ _ = _
    exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
  change ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin r)) (TangentSpace J)
      ℝ (Bundle.Trivial (OrthogonalSphere r) ℝ)
      (D q₀.1 q₀.2.proj) (D q.1 q.2.proj) (D q₀.1 q₀.2.proj) (D q.1 q.2.proj)
      (q.2.snd.comp (mfderiv J J (D q.1).symm (D q.1 q.2.proj))) v = _
  simp only [ContinuousLinearMap.inCoordinates, inTangentCoordinates,
    ContinuousLinearMap.comp_apply, hscalar, ContinuousLinearMap.id_apply,
    Diffeomorph.symm_apply_apply]
  erw [(D q.1).symm_apply_apply, ContinuousLinearMap.comp_apply]
  change q.2.snd ((mfderiv J J (D q.1).symm (D q.1 q.2.proj))
      ((trivializationAt (EuclideanSpace ℝ (Fin r)) (TangentSpace J)
        (D q₀.1 q₀.2.proj)).symmL ℝ (D q.1 q.2.proj) v)) =
    q.2.snd (a.symmL ℝ q.2.proj (a.continuousLinearMapAt ℝ q.2.proj
      ((mfderiv J J (D q.1).symm (D q.1 q.2.proj))
        ((trivializationAt (EuclideanSpace ℝ (Fin r)) (TangentSpace J)
          (D q₀.1 q₀.2.proj)).symmL ℝ (D q.1 q.2.proj) v))))
  erw [a.symmL_continuousLinearMapAt (R := ℝ) hq]

end AtiyahSinger

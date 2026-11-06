/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The cotangent lift of the original smooth group action

Public module ID: M1182.

The native action on the original cotangent total space is exactly
cotangentDiffeomorphMap applied to Diffeomorph.smul. In particular its
fiber formula is the inverse differential, not an unchanged model covector.
Joint smoothness uses the native cotangent Hom-bundle atlas. This explicit
action is installed locally, so it does not compete with an already supplied
specialized action such as the orthogonal sphere action.

Sources: SG III.1 (1.6), III.3 coordinate covariance, III.9 equivariance,
and III.13.4 for transport on the cotangent bundle. The joint parameter
statement is the standard differential-geometric cotangent-lift supplement.
In local frames it uses the inverse of the derivative matrix of the given
action. No metric, symplectic form, compact group or base, or new total-space
carrier is selected. The general smooth-symbol transport already uses these
same pointwise lifts; this module makes their total-space action available.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Topology
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- The original inverse-differential lifts form a native action on the same cotangent space. -/
@[reducible]
def smoothCotangentMulAction : MulAction G (CotangentTotalSpace (n := n) (M := M)) where
  smul g := cotangentDiffeomorphMap
    (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
  one_smul z := by
    -- Identify the original base identity before differentiating its inverse.
    have h : Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (1 : G) =
        Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M ∞ := by
      apply Diffeomorph.ext
      intro x
      exact one_smul G x
    change cotangentDiffeomorphMap
      (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (1 : G)) z = z
    rw [h]
    change (⟨z.proj, z.snd.comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (id : M → M) z.proj)⟩ :
      CotangentTotalSpace (n := n) (M := M)) = z
    rw [mfderiv_id]
    simp
  mul_smul g k z := by
    -- The existing functoriality theorem retains the inverse-differential order.
    have h : Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (g * k) =
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ k).trans
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g) := by
      apply Diffeomorph.ext
      intro x
      exact mul_smul g k x
    change cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (g * k)) z =
      cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ k) z)
    rw [h]
    exact congrArg (fun e ↦ e z)
      (cotangentDiffeomorph_trans
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ k)
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g))

variable [hG : IsManifold IG ∞ G]

include hM hG in
/-- The original smooth action lifts jointly smoothly in the native cotangent bundle atlas. -/
theorem contMDiffSMul_smoothCotangent :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    ContMDiffSMul IG
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := M)) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let d (g : G) := Diffeomorph.smul (M := M) IG I ∞ g
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  constructor
  intro q₀
  -- The base action and the original covector coordinates are jointly smooth.
  have hs : ContMDiffAt (IG.prod (I.prod 𝓘(ℝ, CotangentModel n)))
      (I.prod 𝓘(ℝ, CotangentModel n)) ∞
      (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦ q.2) q₀ :=
    contMDiffAt_snd
  have hsource := (contMDiffAt_hom_bundle (IB := I)
    (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦ q.2) (x₀ := q₀)).mp hs
  have hbase : ContMDiffAt (IG.prod (I.prod 𝓘(ℝ, CotangentModel n))) I ∞
      (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦ q.1 • q.2.proj) q₀ :=
    contMDiffAt_fst.smul hsource.1
  -- The given topological action controls the return point of each inverse lift.
  have hreturn : ContinuousAt
      (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦ q.2.proj) q₀ := by
    have h : ContinuousAt
        (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦
          q.1⁻¹ • (q.1 • q.2.proj)) q₀ :=
      continuousAt_fst.inv.smul hbase.continuousAt
    simpa only [inv_smul_smul] using h
  let a := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) q₀.2.proj
  let b := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I)
    (q₀.1 • q₀.2.proj)
  let A (q : G × CotangentTotalSpace (n := n) (M := M)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (b.continuousLinearMapAt ℝ (q.1 • q.2.proj)).comp
      ((mfderiv I I (d q.1) q.2.proj).comp (a.symmL ℝ q.2.proj))
  let B (q : G × CotangentTotalSpace (n := n) (M := M)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (a.continuousLinearMapAt ℝ q.2.proj).comp
      ((mfderiv I I (d q.1).symm (q.1 • q.2.proj)).comp
        (b.symmL ℝ (q.1 • q.2.proj)))
  -- The same forward and inverse differentials cancel, by the manifold chain rule.
  have hAB (q : G × CotangentTotalSpace (n := n) (M := M))
      (ha : q.2.proj ∈ a.baseSet) (hb : q.1 • q.2.proj ∈ b.baseSet) :
      (A q).comp (B q) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) ∧
        (B q).comp (A q) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hleft := mfderiv_comp q.2.proj
      ((d q.1).symm.mdifferentiable (by simp) ((d q.1) q.2.proj))
      ((d q.1).mdifferentiable (by simp) q.2.proj)
    have hl : ((d q.1).symm : M → M) ∘ d q.1 = id :=
      funext (d q.1).symm_apply_apply
    rw [hl, mfderiv_id] at hleft
    have hright := mfderiv_comp ((d q.1) q.2.proj)
      ((d q.1).mdifferentiable (by simp) ((d q.1).symm ((d q.1) q.2.proj)))
      ((d q.1).symm.mdifferentiable (by simp) ((d q.1) q.2.proj))
    have hr : (d q.1 : M → M) ∘ (d q.1).symm = id :=
      funext (d q.1).apply_symm_apply
    rw [hr, mfderiv_id] at hright
    erw [(d q.1).symm_apply_apply] at hright
    constructor
    · apply ContinuousLinearMap.ext
      intro v
      change b.continuousLinearMapAt ℝ (q.1 • q.2.proj)
        ((mfderiv I I (d q.1) q.2.proj) (a.symmL ℝ q.2.proj
          (a.continuousLinearMapAt ℝ q.2.proj
            ((mfderiv I I (d q.1).symm (q.1 • q.2.proj))
              (b.symmL ℝ (q.1 • q.2.proj) v))))) = v
      erw [a.symmL_continuousLinearMapAt (R := ℝ) ha]
      change b.continuousLinearMapAt ℝ (q.1 • q.2.proj)
        (((mfderiv I I (d q.1) q.2.proj).comp
          (mfderiv I I (d q.1).symm (q.1 • q.2.proj)))
          (b.symmL ℝ (q.1 • q.2.proj) v)) = v
      erw [← hright, ContinuousLinearMap.id_apply (R₁ := ℝ),
        b.continuousLinearMapAt_symmL (R := ℝ) hb]
    · apply ContinuousLinearMap.ext
      intro v
      change a.continuousLinearMapAt ℝ q.2.proj
        ((mfderiv I I (d q.1).symm (q.1 • q.2.proj))
          (b.symmL ℝ (q.1 • q.2.proj) (b.continuousLinearMapAt ℝ (q.1 • q.2.proj)
            ((mfderiv I I (d q.1) q.2.proj) (a.symmL ℝ q.2.proj v))))) = v
      erw [b.symmL_continuousLinearMapAt (R := ℝ) hb]
      change a.continuousLinearMapAt ℝ q.2.proj
        (((mfderiv I I (d q.1).symm (q.1 • q.2.proj)).comp
          (mfderiv I I (d q.1) q.2.proj)) (a.symmL ℝ q.2.proj v)) = v
      erw [← hleft, ContinuousLinearMap.id_apply (R₁ := ℝ),
        a.continuousLinearMapAt_symmL (R := ℝ) ha]
  have hA : ContMDiffAt (IG.prod (I.prod 𝓘(ℝ, CotangentModel n)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞ A q₀ := by
    have hf : ContMDiffAt ((IG.prod (I.prod 𝓘(ℝ, CotangentModel n))).prod I) I ∞
        (fun p : (G × CotangentTotalSpace (n := n) (M := M)) × M ↦ p.1.1 • p.2)
        (q₀, q₀.2.proj) := contMDiffAt_fst.fst.smul contMDiffAt_snd
    exact ContMDiffAt.mfderiv
      (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦ fun x : M ↦ q.1 • x)
      (fun q ↦ q.2.proj)
      hf hsource.1 (by simp)
  -- Smooth operator inversion uses only the forward derivative family.
  have ha₀ : q₀.2.proj ∈ a.baseSet := mem_baseSet_trivializationAt _ _ _
  have hb₀ : q₀.1 • q₀.2.proj ∈ b.baseSet := mem_baseSet_trivializationAt _ _ _
  have hinvertible : (A q₀).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (hAB q₀ ha₀ hb₀).1 (hAB q₀ ha₀ hb₀).2
  have hB : ContMDiffAt (IG.prod (I.prod 𝓘(ℝ, CotangentModel n)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞ B q₀ := by
    have hinverse := (hinvertible.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp q₀ hA
    apply hinverse.congr_of_eventuallyEq
    filter_upwards [hreturn.preimage_mem_nhds (a.open_baseSet.mem_nhds ha₀),
      hbase.continuousAt.preimage_mem_nhds (b.open_baseSet.mem_nhds hb₀)] with q ha hb
    exact (ContinuousLinearMap.inverse_eq (hAB q ha hb).1 (hAB q ha hb).2).symm
  have hξ : ContMDiffAt (IG.prod (I.prod 𝓘(ℝ, CotangentModel n)))
      𝓘(ℝ, CotangentModel n) ∞
      (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦
        q.2.snd.comp (a.symmL ℝ q.2.proj)) q₀ := by
    have h := hsource.2
    change ContMDiffAt _ _ ∞ (fun q : G × CotangentTotalSpace (n := n) (M := M) ↦
      ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ q.2.proj).comp
        (q.2.snd.comp (a.symmL ℝ q.2.proj))) q₀ at h
    simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_comp] using h
  -- Precomposition with this exact inverse gives the prescribed cotangent action.
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨hbase, ?_⟩
  apply (hξ.clm_comp hB).congr_of_eventuallyEq
  filter_upwards [hreturn.preimage_mem_nhds
    (a.open_baseSet.mem_nhds ha₀)] with q hq
  apply ContinuousLinearMap.ext
  intro v
  have hscalar :
      (trivializationAt ℝ (fun _ : M ↦ ℝ) (q₀.1 • q₀.2.proj)).continuousLinearMapAt ℝ
        (q.1 • q.2.proj) = ContinuousLinearMap.id ℝ ℝ := by
    change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ _ = _
    exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
  change ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace I)
      ℝ (Bundle.Trivial M ℝ) (q₀.1 • q₀.2.proj) (q.1 • q.2.proj)
      (q₀.1 • q₀.2.proj) (q.1 • q.2.proj)
      (q.2.snd.comp (mfderiv I I (d q.1).symm (q.1 • q.2.proj))) v = _
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    hscalar, ContinuousLinearMap.id_apply]
  change q.2.snd ((mfderiv I I (d q.1).symm (q.1 • q.2.proj))
      (b.symmL ℝ (q.1 • q.2.proj) v)) =
    q.2.snd (a.symmL ℝ q.2.proj (a.continuousLinearMapAt ℝ q.2.proj
      ((mfderiv I I (d q.1).symm (q.1 • q.2.proj))
        (b.symmL ℝ (q.1 • q.2.proj) v))))
  erw [a.symmL_continuousLinearMapAt (R := ℝ) hq]

end AtiyahSinger

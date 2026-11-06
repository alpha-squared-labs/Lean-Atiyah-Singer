/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasComplexConnection
public import AtiyahSinger.Geometry.AtlasHermitianMetric

import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Unitary connections in the original finite-rank atlas

Public module ID: M1105.

A unitary connection preserves the supplied Hermitian form on original
smooth sections and tangent directions. The scalar derivative is the native
manifold derivative of that actual pairing. This does not install another
fiber metric or change any topology. Variable and zero ranks are allowed.

Sources: SG II.4 Proposition 4.4, pp.103--104, gives the metric identity and
local connection law. SG II.5 Proposition 5.10, p.122, uses such connections
in tensor Dirac bundles; it is not an existence theorem for metric connections.
The proof below supplements those sources by the coordinate metric-adjoint
averaging argument. The first Hermitian slot is conjugate-linear, as in mathlib.
Smoothness of the supplied metric is required separately; no operator
formal-adjoint assertion is included.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.AtlasComplexConnection

open Bundle Complex
open scoped Manifold ContDiff ComplexConjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {A : SmoothComplexBundleAtlas (n := n) E}

/-- The original covariant derivative preserves this specified Hermitian form. -/
def IsUnitary (cov : AtlasComplexConnection A)
    (h : ComplexBundle.ContinuousHermitianMetric E) : Prop :=
  ∀ (u v : A.smoothSections) (x : M)
      (X : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ)
        (fun y : M ↦ (h.toCore y).inner (u.val y) (v.val y)) x X =
      (h.toCore x).inner (cov.covariantDerivative u x X) (v.val x) +
        (h.toCore x).inner (u.val x) (cov.covariantDerivative v x X)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

set_option maxHeartbeats 0 in
-- The full Gram-operator and native-chart calculation exceeds the default limit.
include hM hT hSC in
open scoped Matrix.Norms.Elementwise in
/-- Every specified smooth Hermitian metric admits a preserving connection on the same atlas. -/
theorem exists_unitary (h : ComplexBundle.ContinuousHermitianMetric E)
    (hh : A.IsSmoothHermitianMetric h) :
    ∃ cov : AtlasComplexConnection A, cov.IsUnitary h := by
  /- Start with any smooth complex connection on the original atlas. Its
  metric adjoint is characterized by differentiating the actual fiber
  pairing. In original coordinates its form is G⁻¹(dG - Γ†G), where G is
  the positive Gram operator. This identity proves that the adjoint forms
  agree on overlaps. Averaging the two connections then preserves h.
  This avoids requiring a separately formalized smooth Gram square root. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, H)
    let V (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
    let e (i : A.Index) := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
    let C (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) : E x ≃ₗ[ℂ] V i :=
      (A.frameLinearEquiv i x hx).trans (e i).symm.toLinearEquiv
    let G (i : A.Index) (x : M) : Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℂ :=
      fun a b ↦ if hx : x ∈ (A.chart i).baseSet then
        (h.toCore x).inner ((C i x hx).symm (EuclideanSpace.single a 1))
          ((C i x hx).symm (EuclideanSpace.single b 1)) else 0
    let toOp (i : A.Index) :
        Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℂ →L[ℝ] (V i →L[ℂ] V i) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let Q (i : A.Index) (x : M) : V i →L[ℂ] V i := toOp i (G i x)
    have hQapply (i : A.Index) (x : M) (v : V i) (a : Fin (A.rank i)) :
        Q i x v a = ∑ b, G i x a b * v b := by
      rfl
    -- The Gram operator describes the supplied pairing on the original fibers.
    have hpair (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) (u v : E x) :
        (h.toCore x).inner u v = inner ℂ (C i x hx u) (Q i x (C i x hx v)) := by
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      let B : E x →ₗ⋆[ℂ] E x →ₗ[ℂ] ℂ :=
        LinearMap.mk₂'ₛₗ _ _ (h.toCore x).inner
          (fun a b c ↦ (h.toCore x).add_left a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
          (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
      have hexpand (w : E x) :
          ∑ a : Fin (A.rank i), (C i x hx w) a •
            (C i x hx).symm (EuclideanSpace.single a 1) = w := by
        simpa only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
          EuclideanSpace.basisFun_repr, LinearEquiv.symm_apply_apply] using
            congrArg (C i x hx).symm
              ((EuclideanSpace.basisFun (Fin (A.rank i)) ℂ).sum_repr (C i x hx w))
      have hexpansion : (h.toCore x).inner u v =
          ∑ a, ∑ b, conj ((C i x hx u) a) * G i x a b * (C i x hx v) b := by
        change B u v = _
        conv_lhs => rw [← hexpand u, map_sum]
        simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
        apply Finset.sum_congr rfl
        intro a _
        conv_lhs => rw [← hexpand v, map_sum]
        simp only [map_smul, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [G]
        rw [dite_eq_left hx]
        change conj ((C i x hx u) a) * ((C i x hx v) b *
          (h.toCore x).inner ((C i x hx).symm (EuclideanSpace.single a 1))
            ((C i x hx).symm (EuclideanSpace.single b 1))) = _
        ring
      rw [hexpansion, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro a _
      change (∑ b, conj ((C i x hx u) a) * G i x a b * (C i x hx v) b) =
        (Q i x (C i x hx v)) a * conj ((C i x hx u) a)
      rw [hQapply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have hQ (i : A.Index) :
        ContMDiffOn I 𝓘(ℝ, V i →L[ℂ] V i) ∞ (Q i) (A.chart i).baseSet := by
      apply (toOp i).contDiff.contMDiff.comp_contMDiffOn
      apply contMDiffOn_pi_space.mpr
      intro a
      apply contMDiffOn_pi_space.mpr
      intro b
      exact hh i a b
    -- Positivity makes each Gram operator invertible, also in the empty frame.
    have hQequiv (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) :
        ∃ L : V i ≃L[ℂ] V i, L.toContinuousLinearMap = Q i x := by
      have hinj : Function.Injective (Q i x) := by
        intro u v huv
        have hz : Q i x (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hp := hpair i x hx ((C i x hx).symm (u - v))
          ((C i x hx).symm (u - v))
        rw [LinearEquiv.apply_symm_apply, hz, inner_zero_right] at hp
        have hv : (C i x hx).symm (u - v) = 0 := (h.toCore x).definite _ hp
        apply sub_eq_zero.mp
        simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg (C i x hx) hv
      let L := (LinearEquiv.ofBijective (Q i x).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv
      exact ⟨L, rfl⟩
    have hQinverse (i : A.Index) :
        ContMDiffOn I 𝓘(ℝ, V i →L[ℂ] V i) ∞
          (fun x ↦ (Q i x).inverse) (A.chart i).baseSet := by
      intro x hx
      obtain ⟨L, hL⟩ := hQequiv i x hx
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (Q i x) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact hi.contMDiffAt.comp_contMDiffWithinAt x (hQ i x hx)
    have hQinverse_apply (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet)
        (v : V i) : Q i x ((Q i x).inverse v) = v := by
      obtain ⟨L, hL⟩ := hQequiv i x hx
      rw [← hL, ContinuousLinearMap.inverse_equiv]
      exact L.apply_symm_apply v
    obtain ⟨cov⟩ := nonempty_atlasComplexConnection A
    let adjoint (i : A.Index) : (V i →L[ℂ] V i) →L[ℝ] (V i →L[ℂ] V i) := {
      toFun := fun T ↦ T.adjoint
      map_add' := fun _ _ ↦ map_add ContinuousLinearMap.adjoint _ _
      map_smul' := by
        intro a T
        change ((a : ℂ) • T).adjoint = _
        rw [map_smulₛₗ]
        change conj (a : ℂ) • T.adjoint = _
        rw [Complex.conj_ofReal]
        rfl
      cont := ContinuousLinearMap.adjoint.continuous }
    let leftComp (i : A.Index) :
        (V i →L[ℂ] V i) →L[ℝ] ((V i →L[ℂ] V i) →L[ℝ] (V i →L[ℂ] V i)) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (V i →L[ℂ] V i)
        (V i →L[ℂ] V i) ℝ ℝ).comp
          ((ContinuousLinearMap.compL ℂ (V i) (V i) (V i)).restrictScalars ℝ)
    let rightComp (i : A.Index) :
        (V i →L[ℂ] V i) →L[ℝ] ((V i →L[ℂ] V i) →L[ℝ] (V i →L[ℂ] V i)) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (V i →L[ℂ] V i)
        (V i →L[ℂ] V i) ℝ ℝ).comp
          ((ContinuousLinearMap.compL ℂ (V i) (V i) (V i)).flip.restrictScalars ℝ)
    let q (c : OpenPartialHomeomorph M H) (i : A.Index) (z : H) : V i →L[ℂ] V i :=
      Q i (c.symm z)
    let Γ (c : OpenPartialHomeomorph M H) (i : A.Index) (z : H) :
        H →L[ℝ] (V i →L[ℂ] V i) :=
      (leftComp i ((q c i z).inverse)).comp
        (fderiv ℝ (q c i) z -
          (rightComp i (q c i z)).comp ((adjoint i).comp (cov.connectionForm c i z)))
    have hqsmooth (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (z : H)
        (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
        ContDiffAt ℝ ∞ (q c i) z := by
      have hs := (hQ i).contMDiffAt ((A.chart i).open_baseSet.mem_nhds hz.2)
      have hi := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
      exact contMDiffAt_iff_contDiffAt.mp (hs.comp z hi)
    -- Inversion and differentiation are smooth on exactly the valid original region.
    have hΓsmooth (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) :
        ContDiffOn ℝ ∞ (Γ c i) (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) := by
      intro z hz
      have hq := hqsmooth c hc i z hz
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
      have hinv := contMDiffAt_iff_contDiffAt.mp
        (((hQinverse i).contMDiffAt ((A.chart i).open_baseSet.mem_nhds hz.2)).comp z hsymm)
      have hleft₀ := (ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := V i →L[ℂ] V i)
        (F := (V i →L[ℂ] V i) →L[ℂ] (V i →L[ℂ] V i))
        ((ContinuousLinearMap.compL ℂ (V i) (V i) (V i)).restrictScalars ℝ))
        |>.contDiffAt.comp z hinv
      have hrestrict := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
        (E := (V i →L[ℂ] V i) →L[ℂ] (V i →L[ℂ] V i))
        (F := (V i →L[ℂ] V i) →L[ℝ] (V i →L[ℂ] V i))
        (ContinuousLinearMap.restrictScalarsL ℂ (V i →L[ℂ] V i)
          (V i →L[ℂ] V i) ℝ ℝ)
      have hleft := hrestrict.contDiffAt.comp z hleft₀
      have hright₀ := (ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := V i →L[ℂ] V i)
        (F := (V i →L[ℂ] V i) →L[ℂ] (V i →L[ℂ] V i))
        ((ContinuousLinearMap.compL ℂ (V i) (V i) (V i)).flip.restrictScalars ℝ))
        |>.contDiffAt.comp z hq
      have hright := hrestrict.contDiffAt.comp z hright₀
      have hcov := (cov.smooth_connectionForm c hc i).contDiffAt
        ((c.isOpen_inter_preimage_symm (A.chart i).open_baseSet).mem_nhds hz)
      have ha : ContDiffAt ℝ ∞ (fun z ↦ (adjoint i).comp (cov.connectionForm c i z)) z :=
        contDiffAt_const.clm_comp hcov
      exact (hleft.clm_comp
        ((hq.fderiv_right (by simp)).sub (hright.clm_comp ha))).contDiffWithinAt
    let coord (i : A.Index) (u : A.smoothSections) (x : M) : V i :=
      (e i).symm (A.chart i ⟨x, u.val x⟩).2
    have hcoordsmooth (i : A.Index) (u : A.smoothSections) :
        ContMDiffOn I 𝓘(ℝ, V i) ∞ (coord i u) (A.chart i).baseSet :=
      ((e i).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (u.property i)
    have hcoord (i : A.Index) (u : A.smoothSections) (x : M)
        (hx : x ∈ (A.chart i).baseSet) : C i x hx (u.val x) = coord i u x := by
      rfl
    have hchartCoord (c : OpenPartialHomeomorph M H) (i : A.Index)
        (u : A.smoothSections) :
        atlasSectionInChart A c i u.val = fun z ↦ coord i u (c.symm z) := by
      rfl
    have hcoordChartSmooth (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (u : A.smoothSections) (z : H)
        (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
        ContDiffAt ℝ ∞ (atlasSectionInChart A c i u.val) z := by
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
      rw [hchartCoord]
      exact contMDiffAt_iff_contDiffAt.mp
        (((hcoordsmooth i u).contMDiffAt
          ((A.chart i).open_baseSet.mem_nhds hz.2)).comp z hsymm)
    have hexpressionCoord (c : OpenPartialHomeomorph M H) (i : A.Index)
        (Ω : H → H →L[ℝ] (V i →L[ℂ] V i)) (u : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart i).baseSet) (X : TangentSpace I x) :
        C i x hx.2 (atlasConnectionExpression A c i Ω u x hx.2 X) =
          fderiv ℝ (atlasSectionInChart A c i u.val) (c x) (mfderiv I I c x X) +
            Ω (c x) (mfderiv I I c x X) (coord i u x) := by
      change (e i).symm ((A.frameLinearEquiv i x hx.2)
        ((A.frameLinearEquiv i x hx.2).symm (e i _))) = _
      rw [LinearEquiv.apply_symm_apply, (e i).symm_apply_apply, hchartCoord]
      simp only [c.left_inv hx.1]
      rfl
    have hscalarChart (f : M → ℂ) (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f)
        (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (x : M) (hx : x ∈ c.source) (X : TangentSpace I x) :
        fderiv ℝ (fun z ↦ f (c.symm z)) (c x) (mfderiv I I c x X) =
          mfderiv I 𝓘(ℝ, ℂ) f x X := by
      have hchart := mdifferentiable_of_mem_atlas (I := I) hc
      have hsymm := hchart.mdifferentiableAt_symm (c.map_source hx)
      have hchain := mvfderiv_comp (I := I) (I' := I) (c x)
        (by simpa only [c.left_inv hx] using hf.mdifferentiableAt (by simp)) hsymm
      have hlocal : fderiv ℝ (fun z ↦ f (c.symm z)) (c x) =
          (mvfderiv I f x).comp (mfderiv I I c.symm (c x)) := by
        dsimp only [I] at hchain
        rw [mvfderiv_eq_fderiv, c.left_inv hx] at hchain
        exact hchain
      rw [hlocal]
      change (mvfderiv I f x)
        (((mfderiv I I c.symm (c x)).comp (mfderiv I I c x)) X) = _
      rw [hchart.symm_comp_deriv hx]
      rfl
    -- Differentiate the supplied pairing, rather than an unrelated frame metric.
    have hpairDerivative (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (u v : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart i).baseSet) (X : TangentSpace I x) :
        mvfderiv I
            (fun y ↦ (h.toCore y).inner (u.val y) (v.val y)) x X =
          inner ℂ (coord i u x)
              (Q i x (fderiv ℝ (atlasSectionInChart A c i v.val) (c x)
                (mfderiv I I c x X))) +
            inner ℂ (coord i u x)
              (fderiv ℝ (q c i) (c x) (mfderiv I I c x X) (coord i v x)) +
            inner ℂ
              (fderiv ℝ (atlasSectionInChart A c i u.val) (c x)
                (mfderiv I I c x X)) (Q i x (coord i v x)) := by
      let a := atlasSectionInChart A c i u.val
      let b := atlasSectionInChart A c i v.val
      let Y : H := mfderiv I I c x X
      let R := ContinuousLinearMap.restrictScalarsL ℂ (V i) (V i) ℝ ℝ
      have hz : c x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet := by
        refine ⟨c.map_source hx.1, ?_⟩
        change c.symm (c x) ∈ (A.chart i).baseSet
        rw [c.left_inv hx.1]
        exact hx.2
      have ha := (hcoordChartSmooth c hc i u (c x) hz).differentiableAt (by simp)
      have hb := (hcoordChartSmooth c hc i v (c x) hz).differentiableAt (by simp)
      have hq := (hqsmooth c hc i (c x) hz).differentiableAt (by simp)
      have hqr : HasFDerivAt (fun z ↦ (q c i z).restrictScalars ℝ)
          (R.comp (fderiv ℝ (q c i) (c x))) (c x) :=
        R.hasFDerivAt.comp (c x) hq.hasFDerivAt
      have hproduct := hqr.clm_apply hb.hasFDerivAt
      have hinner := ha.hasFDerivAt.inner ℂ hproduct
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) (c.map_source hx.1)
      have hpre : c.symm ⁻¹' (A.chart i).baseSet ∈ nhds (c x) :=
        hsymm.continuousAt.preimage_mem_nhds (by
          simpa only [c.left_inv hx.1] using (A.chart i).open_baseSet.mem_nhds hx.2)
      have hnear : (fun z ↦ (h.toCore (c.symm z)).inner
          (u.val (c.symm z)) (v.val (c.symm z))) =ᶠ[nhds (c x)]
            (fun z ↦ inner ℂ (a z) (q c i z (b z))) := by
        filter_upwards [hpre] with z hz
        exact hpair i (c.symm z) hz (u.val (c.symm z)) (v.val (c.symm z))
      have hd := hinner.fderiv
      change fderiv ℝ (fun z ↦ inner ℂ (a z) (q c i z (b z))) (c x) = _ at hd
      calc
        _ = fderiv ℝ (fun z ↦ (h.toCore (c.symm z)).inner
            (u.val (c.symm z)) (v.val (c.symm z))) (c x) Y :=
          (hscalarChart _ (A.contMDiff_pairing h hh u v) c hc x hx.1 X).symm
        _ = fderiv ℝ (fun z ↦ inner ℂ (a z) (q c i z (b z))) (c x) Y :=
          congrArg (fun L : H →L[ℝ] ℂ ↦ L Y) hnear.fderiv_eq
        _ = _ := by
          rw [hd]
          simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
            fderivInnerCLM_apply, add_apply, inner_add_right]
          change inner ℂ (a (c x)) (q c i (c x) (fderiv ℝ b (c x) Y)) +
            inner ℂ (a (c x)) (fderiv ℝ (q c i) (c x) Y (b (c x))) +
            inner ℂ (fderiv ℝ a (c x) Y) (q c i (c x) (b (c x))) = _
          simp only [a, b, hchartCoord, q, c.left_inv hx.1]
          rfl
    have hΓapply (c : OpenPartialHomeomorph M H) (i : A.Index)
        (z Y : H) (v : V i) :
        Γ c i z Y v = (q c i z).inverse
          (fderiv ℝ (q c i) z Y v -
            (cov.connectionForm c i z Y).adjoint (q c i z v)) := by
      rfl
    have hstarPair (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (i : A.Index) (u v : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart i).baseSet) (X : TangentSpace I x) :
        (h.toCore x).inner (v.val x)
            (atlasConnectionExpression A c i (Γ c i) u x hx.2 X) =
          mvfderiv I
              (fun y ↦ (h.toCore y).inner (v.val y) (u.val y)) x X -
            (h.toCore x).inner (cov.covariantDerivative v x X) (u.val x) := by
      let Y : H := mfderiv I I c x X
      have hqx : q c i (c x) = Q i x := by
        dsimp only [q]
        rw [c.left_inv hx.1]
      rw [hpair i x hx.2, hexpressionCoord c i (Γ c i) u x hx X, hcoord,
        map_add, hΓapply, hqx, hQinverse_apply i x hx.2,
        hpairDerivative c hc i v u x hx X,
        cov.covariantDerivative_eq v c hc i x hx X, hpair i x hx.2,
        hexpressionCoord c i (cov.connectionForm c i) v x hx X, hcoord]
      simp only [inner_add_left, inner_add_right, inner_sub_right]
      let a := coord i u x
      let b := coord i v x
      let du := fderiv ℝ (atlasSectionInChart A c i u.val) (c x) Y
      let dv := fderiv ℝ (atlasSectionInChart A c i v.val) (c x) Y
      let dQ := fderiv ℝ (q c i) (c x) Y
      let L := cov.connectionForm c i (c x) Y
      change inner ℂ b (Q i x du) +
          (inner ℂ b (dQ a) - inner ℂ b (L.adjoint (Q i x a))) =
        (inner ℂ b (Q i x du) + inner ℂ b (dQ a) + inner ℂ dv (Q i x a)) -
          (inner ℂ dv (Q i x a) + inner ℂ (L b) (Q i x a))
      rw [ContinuousLinearMap.adjoint_inner_right]
      ring
    -- A supported original frame section realizes any prescribed fiber vector.
    have hevaluation (x : M) (w : E x) : ∃ u : A.smoothSections, u.val x = w := by
      obtain ⟨i, hi⟩ := A.covers x
      obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        ((A.chart i).open_baseSet.mem_nhds hi)
      let a := C i x hi w
      let s (y : M) : E y := if hy : y ∈ (A.chart i).baseSet then
        (ψ y : ℂ) • (C i y hy).symm a else 0
      have hpoint (y : M) (hy : y ∈ (A.chart i).baseSet) (b : V i) :
          (⟨y, (C i y hy).symm b⟩ : TotalSpace Unit E) =
            (A.chart i).toPartialEquiv.symm (y, e i b) := by
        exact TotalSpace.mk_cast (F := Unit) (E := E) ((A.chart i).proj_symm_apply' hy) _
      let p (j : A.Index) (y : M) : Fin (A.rank j) → ℂ :=
        ∑ b : Fin (A.rank i), a b •
          (A.chart j ((A.chart i).toPartialEquiv.symm (y, Pi.single b 1))).2
      have hp (j : A.Index) (y : M) (hy : y ∈ (A.chart i).baseSet)
          (hyj : y ∈ (A.chart j).baseSet) :
          (A.chart j ⟨y, (C i y hy).symm a⟩).2 = p j y := by
        let L := A.frameLinearEquiv j y hyj
        have hexpand : ∑ b : Fin (A.rank i), a b •
            (C i y hy).symm (EuclideanSpace.single b 1) = (C i y hy).symm a := by
          simpa only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
            EuclideanSpace.basisFun_repr] using congrArg (C i y hy).symm
              ((EuclideanSpace.basisFun (Fin (A.rank i)) ℂ).sum_repr a)
        change L ((C i y hy).symm a) = _
        rw [← hexpand, map_sum]
        simp only [map_smul]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        change (A.chart j ⟨y, (C i y hy).symm (EuclideanSpace.single b 1)⟩).2 = _
        rw [hpoint]
        rfl
      have hpsmooth (j : A.Index) :
          ContMDiffOn I 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞ (p j)
            ((A.chart i).baseSet ∩ (A.chart j).baseSet) := by
        apply contMDiffOn_finsetSum
        intro b _
        have hscale := ((a b • ContinuousLinearMap.id ℂ (Fin (A.rank j) → ℂ))
          |>.restrictScalars ℝ).contMDiff (n := ∞)
        exact hscale.comp_contMDiffOn (A.contMDiffOn_coordChange i j b)
      have hψsmooth : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun y : M ↦ (ψ y : ℂ)) :=
        Complex.ofRealCLM.contMDiff.comp ψ.contMDiff
      have hs : A.IsSmoothSection s := by
        intro j y hyj
        by_cases hy : y ∈ tsupport (ψ : M → ℝ)
        · have hyi := hψ hy
          have hlocal := (hpsmooth j).contMDiffAt
            (((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds ⟨hyi, hyj⟩)
          have hmul : ContDiff ℝ ∞
              (fun z : ℂ × (Fin (A.rank j) → ℂ) ↦ z.1 • z.2) := contDiff_smul
          have hscaled := hmul.contMDiff.contMDiffAt.comp y
            (hψsmooth.contMDiffAt.prodMk_space hlocal)
          apply (hscaled.congr_of_eventuallyEq ?_).contMDiffWithinAt
          filter_upwards [((A.chart i).open_baseSet.inter
            (A.chart j).open_baseSet).mem_nhds ⟨hyi, hyj⟩] with z hz
          dsimp only [s]
          rw [dite_eq_left hz.1]
          change (A.frameLinearEquiv j z hz.2) ((ψ z : ℂ) • (C i z hz.1).symm a) = _
          rw [map_smul]
          exact congrArg (fun b : Fin (A.rank j) → ℂ ↦ (ψ z : ℂ) • b)
            (hp j z hz.1 hz.2)
        · have hzero : (fun z : M ↦ (A.chart j ⟨z, s z⟩).2) =ᶠ[nhds y]
              (fun _ ↦ (0 : Fin (A.rank j) → ℂ)) := by
            filter_upwards [(isClosed_tsupport (ψ : M → ℝ)).isOpen_compl.mem_nhds hy,
              (A.chart j).open_baseSet.mem_nhds hyj] with z hz hzj
            have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
            have hsz : s z = 0 := by
              dsimp only [s]
              split_ifs <;> simp only [hψz, Complex.ofReal_zero, zero_smul]
            rw [hsz]
            exact (A.linear j z hzj).map_zero
          exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
      refine ⟨⟨s, hs⟩, ?_⟩
      change s x = w
      dsimp only [s]
      rw [dite_eq_left hi, ψ.eq_one, Complex.ofReal_one, one_smul]
      exact (C i x hi).symm_apply_apply w
    -- The defining pairing identity determines the same adjoint derivative in every frame.
    let star : AtlasComplexConnection A := {
      connectionForm := Γ
      smooth_connectionForm := hΓsmooth
      compatible := by
        intro c d hc hd i j u x hx hy X
        let a := atlasConnectionExpression A c i (Γ c i) u x hx.2 X
        let b := atlasConnectionExpression A d j (Γ d j) u x hy.2 X
        have htest (w : E x) : (h.toCore x).inner w a = (h.toCore x).inner w b := by
          obtain ⟨v, hv⟩ := hevaluation x w
          have hc' := hstarPair c hc i u v x hx X
          have hd' := hstarPair d hd j u v x hy X
          simpa only [hv] using hc'.trans hd'.symm
        let : InnerProductSpace.Core ℂ (E x) := h.toCore x
        let : Inner ℂ (E x) := (h.toCore x).toInner
        change a = b
        apply sub_eq_zero.mp
        apply (h.toCore x).definite (a - b)
        change inner ℂ (a - b) (a - b) = 0
        rw [InnerProductSpace.Core.inner_sub_right, htest (a - b), sub_self] }
    have hstar (u v : A.smoothSections) (x : M) (X : TangentSpace I x) :
        (h.toCore x).inner (v.val x) (star.covariantDerivative u x X) =
          mvfderiv I (fun y ↦ (h.toCore y).inner (v.val y) (u.val y)) x X -
            (h.toCore x).inner (cov.covariantDerivative v x X) (u.val x) := by
      exact hstarPair (chartAt H x) (chart_mem_atlas H x)
        (Classical.choose (A.covers x)) u v x
        ⟨mem_chart_source H x, Classical.choose_spec (A.covers x)⟩ X
    let Ω (c : OpenPartialHomeomorph M H) (i : A.Index) (z : H) :
        H →L[ℝ] (V i →L[ℂ] V i) :=
      (1 / 2 : ℂ) • (cov.connectionForm c i z + star.connectionForm c i z)
    have hmeanExpression (c : OpenPartialHomeomorph M H) (i : A.Index)
        (u : A.smoothSections) (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
        (X : TangentSpace I x) :
        atlasConnectionExpression A c i (Ω c i) u x hx.2 X =
          (1 / 2 : ℂ) •
            (atlasConnectionExpression A c i (cov.connectionForm c i) u x hx.2 X +
              atlasConnectionExpression A c i (star.connectionForm c i) u x hx.2 X) := by
      apply (C i x hx.2).injective
      rw [map_smul, map_add,
        hexpressionCoord c i (Ω c i) u x hx X,
        hexpressionCoord c i (cov.connectionForm c i) u x hx X,
        hexpressionCoord c i (star.connectionForm c i) u x hx X]
      let Y : H := mfderiv I I c x X
      let du := fderiv ℝ (atlasSectionInChart A c i u.val) (c x) Y
      let a := coord i u x
      let L := cov.connectionForm c i (c x) Y
      let K := star.connectionForm c i (c x) Y
      change du + (1 / 2 : ℂ) • (L a + K a) =
        (1 / 2 : ℂ) • ((du + L a) + (du + K a))
      module
    -- Affine averaging preserves both the connection law and this exact supplied metric.
    let mean : AtlasComplexConnection A := {
      connectionForm := Ω
      smooth_connectionForm := by
        intro c hc i
        exact ((cov.smooth_connectionForm c hc i).add
          (star.smooth_connectionForm c hc i)).const_smul (1 / 2 : ℂ)
      compatible := by
        intro c d hc hd i j u x hx hy X
        rw [hmeanExpression c i u x hx X, hmeanExpression d j u x hy X,
          cov.compatible c d hc hd i j u x hx hy X,
          star.compatible c d hc hd i j u x hx hy X] }
    have hmean (u : A.smoothSections) (x : M) (X : TangentSpace I x) :
        mean.covariantDerivative u x X =
          (1 / 2 : ℂ) • (cov.covariantDerivative u x X + star.covariantDerivative u x X) := by
      exact hmeanExpression (chartAt H x) (Classical.choose (A.covers x)) u x
        ⟨mem_chart_source H x, Classical.choose_spec (A.covers x)⟩ X
    -- Real differentiation commutes with conjugation of the actual Hermitian pairing.
    have hconjugate (u v : A.smoothSections) (x : M) (X : TangentSpace I x) :
        conj (mvfderiv I
          (fun y ↦ (h.toCore y).inner (v.val y) (u.val y)) x X) =
        mvfderiv I (fun y ↦ (h.toCore y).inner (u.val y) (v.val y)) x X := by
      let J : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
      have hchain := mvfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := I) (g := J) x
        (J.contMDiff (n := ∞) |>.mdifferentiableAt (by simp))
        ((A.contMDiff_pairing h hh v u).mdifferentiableAt (by simp))
      rw [mvfderiv_eq_fderiv, J.fderiv] at hchain
      have hd := congrArg (fun L : TangentSpace I x →L[ℝ] ℂ ↦ L X) hchain
      change mvfderiv I
        (fun y ↦ conj ((h.toCore y).inner (v.val y) (u.val y))) x X =
        conj (mvfderiv I
          (fun y ↦ (h.toCore y).inner (v.val y) (u.val y)) x X) at hd
      have hpairConj :
          (fun y : M ↦ conj ((h.toCore y).inner (v.val y) (u.val y))) =
            (fun y : M ↦ (h.toCore y).inner (u.val y) (v.val y)) := by
        funext y
        exact (h.toCore y).conj_inner_symm (u.val y) (v.val y)
      rw [hpairConj] at hd
      exact hd.symm
    refine ⟨mean, ?_⟩
    intro u v x X
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    let : Inner ℂ (E x) := (h.toCore x).toInner
    change mvfderiv I (fun y ↦ (h.toCore y).inner (u.val y) (v.val y)) x X = _
    -- The adjoint identity in the two Hermitian slots cancels the metric defect.
    have hright := hstar v u x X
    have hleft := congrArg (conj : ℂ → ℂ) (hstar u v x X)
    rw [map_sub, (h.toCore x).conj_inner_symm,
      (h.toCore x).conj_inner_symm, hconjugate u v x X] at hleft
    rw [hmean u x X, hmean v x X]
    simp only [InnerProductSpace.Core.inner_smul_left,
      InnerProductSpace.Core.inner_smul_right, InnerProductSpace.Core.inner_add_left,
      InnerProductSpace.Core.inner_add_right, map_div₀, map_one, map_ofNat]
    rw [hleft, hright]
    norm_num
    ring

end AtiyahSinger.AtlasComplexConnection

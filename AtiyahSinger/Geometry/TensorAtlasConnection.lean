/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasUnitaryConnection
public import AtiyahSinger.Geometry.SmoothTensorAtlas

import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The product connection and metric on the original tensor bundle

Public module ID: M1498.

The tensor derivative is specified on original pure smooth sections by
nabla(s tensor t) = nabla(s) tensor t + s tensor nabla(t). Local connection
forms supply an actual AtlasComplexConnection on tensorSmoothAtlas; there is
no choice of an unrelated connection or assumed compatibility equality.
The product metric is determined by its literal pure-tensor pairing.

Sources: the tensor formulas immediately before SG II.5 Proposition 5.10
(printed pp.121--122), the complex unitary twisting discussion in II.8
(printed p.164), and the local connection identities of II.4 Proposition 4.4.
Proposition 5.10 itself is a subsequent Dirac application. All factor atlases,
metrics and derivatives are supplied objects. Local ranks may vary; only
overlapping charts must have matching ranks. Off-domain connection-form
values are not unique, so no uniqueness of the bundled connection is claimed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff TensorProduct ComplexConjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

attribute [local instance] ComplexBundle.tensorTopology

set_option maxHeartbeats 1200000 in
-- The original two-factor tensor coordinates and connection compatibility require this budget.
/-- The two specified connections induce the product connection on the original tensor atlas. -/
theorem exists_atlasTensorConnection (covE : AtlasComplexConnection A)
    (covF : AtlasComplexConnection B) :
    ∃ cov : AtlasComplexConnection (tensorSmoothAtlas A B),
      ∀ (s : A.smoothSections) (t : B.smoothSections) (x : M)
          (X : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
        cov.covariantDerivative (tensorSmoothSection A B s t) x X =
          covE.covariantDerivative s x X ⊗ₜ[ℂ] t.val x +
            s.val x ⊗ₜ[ℂ] covF.covariantDerivative t x X := by
  /- Construct the Kronecker sum in the actual tensor frames. The product
  rule gives its action on pure sections. Differences from one existing
  connection are fiber-linear, so supported factor sections and tensor
  induction prove compatibility for arbitrary tensor sections. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, H)
    let C := tensorSmoothAtlas A B
    let T := fun x : M ↦ E x ⊗[ℂ] F x
    let VE (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
    let VF (j : B.Index) := EuclideanSpace ℂ (Fin (B.rank j))
    let V (p : C.Index) := EuclideanSpace ℂ (Fin (C.rank p))
    let CE (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) : E x ≃ₗ[ℂ] VE i :=
      (A.frameLinearEquiv i x hx).trans (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
    let CF (j : B.Index) (x : M) (hx : x ∈ (B.chart j).baseSet) : F x ≃ₗ[ℂ] VF j :=
      (B.frameLinearEquiv j x hx).trans (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
    let CT (p : C.Index) (x : M)
        (hx : x ∈ (C.chart p).baseSet) : T x ≃ₗ[ℂ] V p :=
      (C.frameLinearEquiv p x hx).trans (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
    have hbase (p : C.Index) :
        (C.chart p).baseSet = (A.chart p.1).baseSet ∩ (B.chart p.2).baseSet :=
      (ComplexBundle.exists_tensor_trivialization (A.chart p.1) (B.chart p.2)
        (A.linear p.1) (B.linear p.2)).choose_spec.1
    -- The finite-dimensional tensor model has exactly the selected coordinate ordering.
    let b (p : C.Index) :=
      ((EuclideanSpace.basisFun (Fin (A.rank p.1)) ℂ).tensorProduct
        (EuclideanSpace.basisFun (Fin (B.rank p.2)) ℂ)).reindex finProdFinEquiv
    let e (p : C.Index) : (VE p.1 ⊗[ℂ] VF p.2) ≃L[ℂ] V p :=
      (b p).repr.toContinuousLinearEquiv
    have he (p : C.Index) (u : VE p.1) (v : VF p.2)
        (a : Fin (A.rank p.1 * B.rank p.2)) :
        e p (u ⊗ₜ[ℂ] v) a = u (finProdFinEquiv.symm a).1 *
          v (finProdFinEquiv.symm a).2 := by
      change (b p).repr (u ⊗ₜ[ℂ] v) a = _
      dsimp only [b]
      rw [OrthonormalBasis.repr_reindex,
        OrthonormalBasis.tensorProduct_repr_tmul_apply']
      simp only [EuclideanSpace.basisFun_repr]
      exact mul_comm _ _
    have hframe (p : C.Index) (x : M) (hx : x ∈ (C.chart p).baseSet)
        (u : E x) (v : F x) :
        CT p x hx (u ⊗ₜ[ℂ] v) = e p
          (CE p.1 x ((hbase p) ▸ hx).1 u ⊗ₜ[ℂ] CF p.2 x ((hbase p) ▸ hx).2 v) := by
      apply (EuclideanSpace.equiv _ ℂ).injective
      funext a
      change (C.chart p ⟨x, u ⊗ₜ[ℂ] v⟩).2 a =
        e p (CE p.1 x ((hbase p) ▸ hx).1 u ⊗ₜ[ℂ]
          CF p.2 x ((hbase p) ▸ hx).2 v) a
      rw [he]
      change (C.chart p ⟨x, u ⊗ₜ[ℂ] v⟩).2 a =
        (A.chart p.1 ⟨x, u⟩).2 (finProdFinEquiv.symm a).1 *
          (B.chart p.2 ⟨x, v⟩).2 (finProdFinEquiv.symm a).2
      have hspec := (ComplexBundle.exists_tensor_trivialization
        (A.chart p.1) (B.chart p.2) (A.linear p.1) (B.linear p.2)).choose_spec
      simpa only [C, tensorSmoothAtlas, tensorBundleChart,
        Prod.mk.eta, Equiv.apply_symm_apply] using
        hspec.2.2 x ((hbase p) ▸ hx) u v
          (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2
    let LE (p : C.Index) :
        (VE p.1 →L[ℂ] VE p.1) →ₗ[ℂ] (V p →L[ℂ] V p) := {
      toFun L := (e p).toContinuousLinearMap.comp
        ((L.rTensor (VF p.2)).comp (e p).symm.toContinuousLinearMap)
      map_add' L K := by
        simp only [ContinuousLinearMap.rTensor_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c L := by
        simp only [ContinuousLinearMap.rTensor_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    let LF (p : C.Index) :
        (VF p.2 →L[ℂ] VF p.2) →ₗ[ℂ] (V p →L[ℂ] V p) := {
      toFun L := (e p).toContinuousLinearMap.comp
        ((L.lTensor (VE p.1)).comp (e p).symm.toContinuousLinearMap)
      map_add' L K := by
        simp only [ContinuousLinearMap.lTensor_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c L := by
        simp only [ContinuousLinearMap.lTensor_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    let PE (p : C.Index) := (LE p).toContinuousLinearMap
    let PF (p : C.Index) := (LF p).toContinuousLinearMap
    have hPE (p : C.Index) (L : VE p.1 →L[ℂ] VE p.1)
        (u : VE p.1) (v : VF p.2) :
        PE p L (e p (u ⊗ₜ[ℂ] v)) = e p (L u ⊗ₜ[ℂ] v) := by
      change e p ((L.rTensor (VF p.2)) ((e p).symm (e p (u ⊗ₜ[ℂ] v)))) = _
      rw [(e p).symm_apply_apply, ContinuousLinearMap.rTensor_tmul]
    have hPF (p : C.Index) (L : VF p.2 →L[ℂ] VF p.2)
        (u : VE p.1) (v : VF p.2) :
        PF p L (e p (u ⊗ₜ[ℂ] v)) = e p (u ⊗ₜ[ℂ] L v) := by
      change e p ((L.lTensor (VE p.1)) ((e p).symm (e p (u ⊗ₜ[ℂ] v)))) = _
      rw [(e p).symm_apply_apply, ContinuousLinearMap.lTensor_tmul]
    let Γ (c : OpenPartialHomeomorph M H) (p : C.Index) (z : H) :=
      ((PE p).restrictScalars ℝ).comp (covE.connectionForm c p.1 z) +
        ((PF p).restrictScalars ℝ).comp (covF.connectionForm c p.2 z)
    have hΓsmooth (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (p : C.Index) :
        ContDiffOn ℝ ∞ (Γ c p) (c.target ∩ c.symm ⁻¹' (C.chart p).baseSet) := by
      have hE := (covE.smooth_connectionForm c hc p.1).mono
        (show c.target ∩ c.symm ⁻¹' (C.chart p).baseSet ⊆
          c.target ∩ c.symm ⁻¹' (A.chart p.1).baseSet from
          fun z hz ↦ ⟨hz.1, ((hbase p) ▸ hz.2).1⟩)
      have hF := (covF.smooth_connectionForm c hc p.2).mono
        (show c.target ∩ c.symm ⁻¹' (C.chart p).baseSet ⊆
          c.target ∩ c.symm ⁻¹' (B.chart p.2).baseSet from
          fun z hz ↦ ⟨hz.1, ((hbase p) ▸ hz.2).2⟩)
      exact (contDiffOn_const.clm_comp hE).add (contDiffOn_const.clm_comp hF)
    -- Work in the same original finite-dimensional frame for each connection expression.
    have hexpressionCoordE (c : OpenPartialHomeomorph M H)
        (i : A.Index) (Ω : H → H →L[ℝ]
          (EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i))))
        (u : A.smoothSections) (x : M) (hx : x ∈ (A.chart i).baseSet)
        (X : TangentSpace I x) :
        CE i x hx
            (atlasConnectionExpression A c i Ω u x hx X) =
          fderiv ℝ (atlasSectionInChart A c i u.val) (c x) (mfderiv I I c x X) +
            Ω (c x) (mfderiv I I c x X) (atlasSectionInChart A c i u.val (c x)) := by
      change (EuclideanSpace.equiv _ ℂ).symm
        ((A.frameLinearEquiv i x hx) ((A.frameLinearEquiv i x hx).symm _)) = _
      rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    have hexpressionCoordF (c : OpenPartialHomeomorph M H)
        (i : B.Index) (Ω : H → H →L[ℝ]
          (EuclideanSpace ℂ (Fin (B.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (B.rank i))))
        (u : B.smoothSections) (x : M) (hx : x ∈ (B.chart i).baseSet)
        (X : TangentSpace I x) :
        CF i x hx
            (atlasConnectionExpression B c i Ω u x hx X) =
          fderiv ℝ (atlasSectionInChart B c i u.val) (c x) (mfderiv I I c x X) +
            Ω (c x) (mfderiv I I c x X) (atlasSectionInChart B c i u.val (c x)) := by
      change (EuclideanSpace.equiv _ ℂ).symm
        ((B.frameLinearEquiv i x hx) ((B.frameLinearEquiv i x hx).symm _)) = _
      rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    have hexpressionCoordT (c : OpenPartialHomeomorph M H)
        (i : C.Index) (Ω : H → H →L[ℝ]
          (V i →L[ℂ] V i))
        (u : C.smoothSections) (x : M) (hx : x ∈ (C.chart i).baseSet)
        (X : TangentSpace I x) :
        CT i x hx
            (atlasConnectionExpression C c i Ω u x hx X) =
          fderiv ℝ (atlasSectionInChart C c i u.val) (c x) (mfderiv I I c x X) +
            Ω (c x) (mfderiv I I c x X) (atlasSectionInChart C c i u.val (c x)) := by
      change (EuclideanSpace.equiv _ ℂ).symm
        ((C.frameLinearEquiv i x hx) ((C.frameLinearEquiv i x hx).symm _)) = _
      rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    have hcoordChartSmoothE (c : OpenPartialHomeomorph M H)
        (hc : c ∈ atlas H M) (i : A.Index) (u : A.smoothSections) (z : H)
        (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
        ContDiffAt ℝ ∞ (atlasSectionInChart A c i u.val) z := by
      have hcoord := ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toContinuousLinearMap
        |>.restrictScalars ℝ).contMDiff.comp_contMDiffOn (u.property i)
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
      exact contMDiffAt_iff_contDiffAt.mp
        ((hcoord.contMDiffAt ((A.chart i).open_baseSet.mem_nhds hz.2)).comp z hsymm)
    have hcoordChartSmoothF (c : OpenPartialHomeomorph M H)
        (hc : c ∈ atlas H M) (i : B.Index) (u : B.smoothSections) (z : H)
        (hz : z ∈ c.target ∩ c.symm ⁻¹' (B.chart i).baseSet) :
        ContDiffAt ℝ ∞ (atlasSectionInChart B c i u.val) z := by
      have hcoord := ((EuclideanSpace.equiv (Fin (B.rank i)) ℂ).symm.toContinuousLinearMap
        |>.restrictScalars ℝ).contMDiff.comp_contMDiffOn (u.property i)
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
      exact contMDiffAt_iff_contDiffAt.mp
        ((hcoord.contMDiffAt ((B.chart i).open_baseSet.mem_nhds hz.2)).comp z hsymm)
    have hpure (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (p : C.Index) (s : A.smoothSections) (t : B.smoothSections)
        (x : M) (hx : x ∈ c.source ∩ (C.chart p).baseSet) (X : TangentSpace I x) :
        atlasConnectionExpression C c p (Γ c p) (tensorSmoothSection A B s t) x hx.2 X =
          covE.covariantDerivative s x X ⊗ₜ[ℂ] t.val x +
            s.val x ⊗ₜ[ℂ] covF.covariantDerivative t x X := by
      let f := atlasSectionInChart A c p.1 s.val
      let g := atlasSectionInChart B c p.2 t.val
      let a := atlasSectionInChart C c p (tensorSmoothSection A B s t).val
      let μ : VE p.1 →L[ℂ] VF p.2 →L[ℂ] V p :=
        (ContinuousLinearMap.compL ℂ (VF p.2) (VE p.1 ⊗[ℂ] VF p.2) (V p)
          (e p).toContinuousLinearMap).comp (TensorProduct.mkL ℂ (VE p.1) (VF p.2))
      let μR := μ.bilinearRestrictScalars ℝ
      let Y := mfderiv I I c x X
      have hxE := ((hbase p) ▸ hx.2).1
      have hxF := ((hbase p) ▸ hx.2).2
      have hs := (hcoordChartSmoothE c hc p.1 s (c x)
        ⟨c.map_source hx.1, by
          change c.symm (c x) ∈ (A.chart p.1).baseSet
          rw [c.left_inv hx.1]
          exact hxE⟩).differentiableAt
          (by simp)
      have ht := (hcoordChartSmoothF c hc p.2 t (c x)
        ⟨c.map_source hx.1, by
          change c.symm (c x) ∈ (B.chart p.2).baseSet
          rw [c.left_inv hx.1]
          exact hxF⟩).differentiableAt
          (by simp)
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) (c.map_source hx.1)
      have hpre : c.symm ⁻¹' (C.chart p).baseSet ∈ nhds (c x) :=
        hsymm.continuousAt.preimage_mem_nhds (by
          simpa only [c.left_inv hx.1] using (C.chart p).open_baseSet.mem_nhds hx.2)
      have hnear : a =ᶠ[nhds (c x)] (fun z ↦ μR (f z) (g z)) := by
        filter_upwards [hpre] with z hz
        exact hframe p (c.symm z) hz (s.val (c.symm z)) (t.val (c.symm z))
      have hd : fderiv ℝ a (c x) Y =
          e p (f (c x) ⊗ₜ[ℂ] fderiv ℝ g (c x) Y) +
            e p (fderiv ℝ f (c x) Y ⊗ₜ[ℂ] g (c x)) := by
        rw [hnear.fderiv_eq, μR.fderiv_of_bilinear hs ht]
        rfl
      have hv : a (c x) = e p (f (c x) ⊗ₜ[ℂ] g (c x)) := hnear.eq_of_nhds
      apply (CT p x hx.2).injective
      rw [hexpressionCoordT c p (Γ c p), map_add, hframe p x hx.2,
        hframe p x hx.2,
        covE.covariantDerivative_eq s c hc p.1 x ⟨hx.1, hxE⟩ X,
        covF.covariantDerivative_eq t c hc p.2 x ⟨hx.1, hxF⟩ X,
        hexpressionCoordE c p.1, hexpressionCoordF c p.2]
      have hf : CE p.1 x hxE (s.val x) = f (c x) := by
        dsimp only [f, atlasSectionInChart]
        rw [c.left_inv hx.1]
        rfl
      have hg : CF p.2 x hxF (t.val x) = g (c x) := by
        dsimp only [g, atlasSectionInChart]
        rw [c.left_inv hx.1]
        rfl
      rw [hf, hg]
      change fderiv ℝ a (c x) Y + Γ c p (c x) Y (a (c x)) = _
      rw [hd, hv]
      change (e p (f (c x) ⊗ₜ[ℂ] fderiv ℝ g (c x) Y) +
        e p (fderiv ℝ f (c x) Y ⊗ₜ[ℂ] g (c x))) +
          (PE p (covE.connectionForm c p.1 (c x) Y) (e p (f (c x) ⊗ₜ[ℂ] g (c x))) +
            PF p (covF.connectionForm c p.2 (c x) Y)
              (e p (f (c x) ⊗ₜ[ℂ] g (c x)))) = _
      rw [hPE, hPF, TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, map_add]
      abel
    -- A bump-supported original factor section realizes any prescribed fiber value.
    have hevaluationE (x : M) (w : E x) :
        ∃ u : A.smoothSections, u.val x = w := by
      let W (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
      let ee (i : A.Index) := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
      let cc (i : A.Index) (y : M) (hy : y ∈ (A.chart i).baseSet) : E y ≃ₗ[ℂ] W i :=
        (A.frameLinearEquiv i y hy).trans (ee i).symm.toLinearEquiv
      obtain ⟨i, hi⟩ := A.covers x
      obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        ((A.chart i).open_baseSet.mem_nhds hi)
      let a := cc i x hi w
      let s (y : M) : E y := if hy : y ∈ (A.chart i).baseSet then
        (ψ y : ℂ) • (cc i y hy).symm a else 0
      have hpoint (y : M) (hy : y ∈ (A.chart i).baseSet) (b : W i) :
          (⟨y, (cc i y hy).symm b⟩ : TotalSpace Unit E) =
            (A.chart i).toPartialEquiv.symm (y, ee i b) := by
        exact TotalSpace.mk_cast (F := Unit) (E := E) ((A.chart i).proj_symm_apply' hy) _
      let p (j : A.Index) (y : M) : Fin (A.rank j) → ℂ :=
        ∑ b : Fin (A.rank i), a b •
          (A.chart j ((A.chart i).toPartialEquiv.symm (y, Pi.single b 1))).2
      have hp (j : A.Index) (y : M) (hy : y ∈ (A.chart i).baseSet)
          (hyj : y ∈ (A.chart j).baseSet) :
          (A.chart j ⟨y, (cc i y hy).symm a⟩).2 = p j y := by
        let L := A.frameLinearEquiv j y hyj
        have hexpand : ∑ b : Fin (A.rank i), a b •
            (cc i y hy).symm (EuclideanSpace.single b 1) = (cc i y hy).symm a := by
          simpa only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
            EuclideanSpace.basisFun_repr] using congrArg (cc i y hy).symm
              ((EuclideanSpace.basisFun (Fin (A.rank i)) ℂ).sum_repr a)
        change L ((cc i y hy).symm a) = _
        rw [← hexpand, map_sum]
        simp only [map_smul]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        change (A.chart j ⟨y, (cc i y hy).symm (EuclideanSpace.single b 1)⟩).2 = _
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
          change (A.frameLinearEquiv j z hz.2) ((ψ z : ℂ) • (cc i z hz.1).symm a) = _
          rw [map_smul]
          exact congrArg (fun b : Fin (A.rank j) → ℂ ↦ (ψ z : ℂ) • b) (hp j z hz.1 hz.2)
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
      exact (cc i x hi).symm_apply_apply w
    have hevaluationF (x : M) (w : F x) :
        ∃ u : B.smoothSections, u.val x = w := by
      let W (i : B.Index) := EuclideanSpace ℂ (Fin (B.rank i))
      let ee (i : B.Index) := EuclideanSpace.equiv (Fin (B.rank i)) ℂ
      let cc (i : B.Index) (y : M) (hy : y ∈ (B.chart i).baseSet) : F y ≃ₗ[ℂ] W i :=
        (B.frameLinearEquiv i y hy).trans (ee i).symm.toLinearEquiv
      obtain ⟨i, hi⟩ := B.covers x
      obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        ((B.chart i).open_baseSet.mem_nhds hi)
      let a := cc i x hi w
      let s (y : M) : F y := if hy : y ∈ (B.chart i).baseSet then
        (ψ y : ℂ) • (cc i y hy).symm a else 0
      have hpoint (y : M) (hy : y ∈ (B.chart i).baseSet) (b : W i) :
          (⟨y, (cc i y hy).symm b⟩ : TotalSpace Unit F) =
            (B.chart i).toPartialEquiv.symm (y, ee i b) := by
        exact TotalSpace.mk_cast (F := Unit) (E := F) ((B.chart i).proj_symm_apply' hy) _
      let p (j : B.Index) (y : M) : Fin (B.rank j) → ℂ :=
        ∑ b : Fin (B.rank i), a b •
          (B.chart j ((B.chart i).toPartialEquiv.symm (y, Pi.single b 1))).2
      have hp (j : B.Index) (y : M) (hy : y ∈ (B.chart i).baseSet)
          (hyj : y ∈ (B.chart j).baseSet) :
          (B.chart j ⟨y, (cc i y hy).symm a⟩).2 = p j y := by
        let L := B.frameLinearEquiv j y hyj
        have hexpand : ∑ b : Fin (B.rank i), a b •
            (cc i y hy).symm (EuclideanSpace.single b 1) = (cc i y hy).symm a := by
          simpa only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
            EuclideanSpace.basisFun_repr] using congrArg (cc i y hy).symm
              ((EuclideanSpace.basisFun (Fin (B.rank i)) ℂ).sum_repr a)
        change L ((cc i y hy).symm a) = _
        rw [← hexpand, map_sum]
        simp only [map_smul]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        change (B.chart j ⟨y, (cc i y hy).symm (EuclideanSpace.single b 1)⟩).2 = _
        rw [hpoint]
        rfl
      have hpsmooth (j : B.Index) :
          ContMDiffOn I 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞ (p j)
            ((B.chart i).baseSet ∩ (B.chart j).baseSet) := by
        apply contMDiffOn_finsetSum
        intro b _
        have hscale := ((a b • ContinuousLinearMap.id ℂ (Fin (B.rank j) → ℂ))
          |>.restrictScalars ℝ).contMDiff (n := ∞)
        exact hscale.comp_contMDiffOn (B.contMDiffOn_coordChange i j b)
      have hψsmooth : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun y : M ↦ (ψ y : ℂ)) :=
        Complex.ofRealCLM.contMDiff.comp ψ.contMDiff
      have hs : B.IsSmoothSection s := by
        intro j y hyj
        by_cases hy : y ∈ tsupport (ψ : M → ℝ)
        · have hyi := hψ hy
          have hlocal := (hpsmooth j).contMDiffAt
            (((B.chart i).open_baseSet.inter (B.chart j).open_baseSet).mem_nhds ⟨hyi, hyj⟩)
          have hmul : ContDiff ℝ ∞
              (fun z : ℂ × (Fin (B.rank j) → ℂ) ↦ z.1 • z.2) := contDiff_smul
          have hscaled := hmul.contMDiff.contMDiffAt.comp y
            (hψsmooth.contMDiffAt.prodMk_space hlocal)
          apply (hscaled.congr_of_eventuallyEq ?_).contMDiffWithinAt
          filter_upwards [((B.chart i).open_baseSet.inter
            (B.chart j).open_baseSet).mem_nhds ⟨hyi, hyj⟩] with z hz
          dsimp only [s]
          rw [dite_eq_left hz.1]
          change (B.frameLinearEquiv j z hz.2) ((ψ z : ℂ) • (cc i z hz.1).symm a) = _
          rw [map_smul]
          exact congrArg (fun b : Fin (B.rank j) → ℂ ↦ (ψ z : ℂ) • b) (hp j z hz.1 hz.2)
        · have hzero : (fun z : M ↦ (B.chart j ⟨z, s z⟩).2) =ᶠ[nhds y]
              (fun _ ↦ (0 : Fin (B.rank j) → ℂ)) := by
            filter_upwards [(isClosed_tsupport (ψ : M → ℝ)).isOpen_compl.mem_nhds hy,
              (B.chart j).open_baseSet.mem_nhds hyj] with z hz hzj
            have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
            have hsz : s z = 0 := by
              dsimp only [s]
              split_ifs <;> simp only [hψz, Complex.ofReal_zero, zero_smul]
            rw [hsz]
            exact (B.linear j z hzj).map_zero
          exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
      refine ⟨⟨s, hs⟩, ?_⟩
      change s x = w
      dsimp only [s]
      rw [dite_eq_left hi, ψ.eq_one, Complex.ofReal_one, one_smul]
      exact (cc i x hi).symm_apply_apply w
    -- Relative to one existing connection, a local difference acts on fiber values only.
    obtain ⟨cov0⟩ := nonempty_atlasComplexConnection C
    let Δ (c : OpenPartialHomeomorph M H) (p : C.Index) (x : M)
        (hx : x ∈ (C.chart p).baseSet) (X : TangentSpace I x) : T x →ₗ[ℂ] T x :=
      let L : V p →L[ℂ] V p := Γ c p (c x) (mfderiv I I c x X) -
        cov0.connectionForm c p (c x) (mfderiv I I c x X)
      (CT p x hx).symm.toLinearMap.comp (L.toLinearMap.comp (CT p x hx).toLinearMap)
    have hdelta (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (p : C.Index) (u : C.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (C.chart p).baseSet) (X : TangentSpace I x) :
        atlasConnectionExpression C c p (Γ c p) u x hx.2 X =
          cov0.covariantDerivative u x X + Δ c p x hx.2 X (u.val x) := by
      apply (CT p x hx.2).injective
      rw [map_add, cov0.covariantDerivative_eq u c hc p x hx X,
        hexpressionCoordT c p, hexpressionCoordT c p]
      have hv : atlasSectionInChart C c p u.val (c x) = CT p x hx.2 (u.val x) := by
        dsimp only [atlasSectionInChart]
        rw [c.left_inv hx.1]
        rfl
      change _ = _ + (CT p x hx.2) ((CT p x hx.2).symm _)
      rw [LinearEquiv.apply_symm_apply]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe]
      rw [← hv, sub_apply]
      abel
    have hdelta_same (c d : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
        (hd : d ∈ atlas H M) (p q : C.Index) (x : M)
        (hx : x ∈ c.source ∩ (C.chart p).baseSet)
        (hy : x ∈ d.source ∩ (C.chart q).baseSet) (X : TangentSpace I x) :
        Δ c p x hx.2 X = Δ d q x hy.2 X := by
      apply LinearMap.ext
      intro v
      induction v using TensorProduct.inductionOn with
      | tmul a b =>
        obtain ⟨s, hs⟩ := hevaluationE x a
        obtain ⟨t, ht⟩ := hevaluationF x b
        have heq := (hdelta c hc p (tensorSmoothSection A B s t) x hx X).symm.trans
          ((hpure c hc p s t x hx X).trans
            ((hpure d hd q s t x hy X).symm.trans
              (hdelta d hd q (tensorSmoothSection A B s t) x hy X)))
        apply add_left_cancel (a := cov0.covariantDerivative (tensorSmoothSection A B s t) x X)
        simpa only [tensorSmoothSection, hs, ht] using heq
      | add u v hu hv => rw [map_add, map_add, hu, hv]
    let cov : AtlasComplexConnection C := {
      connectionForm := Γ
      smooth_connectionForm := hΓsmooth
      compatible := by
        intro c d hc hd p q u x hx hy X
        rw [hdelta c hc p u x hx X, hdelta d hd q u x hy X,
          hdelta_same c d hc hd p q x hx hy X] }
    refine ⟨cov, ?_⟩
    intro s t x X
    obtain ⟨p, hp⟩ := C.covers x
    rw [cov.covariantDerivative_eq (tensorSmoothSection A B s t) (chartAt H x)
      (chart_mem_atlas H x) p x ⟨mem_chart_source H x, hp⟩ X]
    exact hpure (chartAt H x) (chart_mem_atlas H x) p s t x ⟨mem_chart_source H x, hp⟩ X

/-- The product connection selected with its exact pure-section Leibniz formula. -/
def atlasTensorConnection (covE : AtlasComplexConnection A)
    (covF : AtlasComplexConnection B) : AtlasComplexConnection (tensorSmoothAtlas A B) :=
  (exists_atlasTensorConnection covE covF).choose

/-- The selected connection differentiates the original pure tensor by the same two factors. -/
theorem atlasTensorConnection_apply (covE : AtlasComplexConnection A)
    (covF : AtlasComplexConnection B) (s : A.smoothSections) (t : B.smoothSections)
    (x : M) (X : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    (atlasTensorConnection covE covF).covariantDerivative (tensorSmoothSection A B s t) x X =
      covE.covariantDerivative s x X ⊗ₜ[ℂ] t.val x +
        s.val x ⊗ₜ[ℂ] covF.covariantDerivative t x X := by
  /- Use the pure-section specification of the same chosen connection.
  Both its tensor atlas and the section are the selectors fixed above. -/
  exact (exists_atlasTensorConnection covE covF).choose_spec s t x X

set_option linter.unusedSectionVars false in

/-- The product forms determine a unique smooth metric on the same tensor fibers and topology. -/
theorem existsUnique_tensorAtlasMetric
    (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (k : ComplexBundle.ContinuousHermitianMetric F) (hk : B.IsSmoothHermitianMetric k) :
    ∃! l : ComplexBundle.ContinuousHermitianMetric (fun x ↦ E x ⊗[ℂ] F x),
      (tensorSmoothAtlas A B).IsSmoothHermitianMetric l ∧
        ∀ (x : M) (s s' : E x) (t t' : F x),
          (l.toCore x).inner (s ⊗ₜ[ℂ] t) (s' ⊗ₜ[ℂ] t') =
            (h.toCore x).inner s s' * (k.toCore x).inner t t' := by
  /- Stage 1: equip the two fibers temporarily with the norms induced by
  their positive forms and use mathlib's tensor inner-product instance.
  Its core gives a positive definite form with the prescribed pure pairing,
  including zero rank.
  Stage 2: the given tensor charts identify its Gram matrix with the product
  of the two original smooth Gram matrices. Smoothness and joint continuity
  follow locally for the existing tensor total topology, not a new topology.
  Stage 3: pure tensors span every original fiber. Sesquilinearity determines
  the entire form from these pairings; the remaining fields are propositions.
  Thus uniqueness concerns the specified metric, not arbitrary coordinate norms. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let C := tensorSmoothAtlas A B
    let T := fun x : M ↦ E x ⊗[ℂ] F x
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    -- Metric-derived norms are temporary devices for constructing the algebraic positive form.
    let core (x : M) : InnerProductSpace.Core ℂ (T x) := by
      letI : NormedAddCommGroup (E x) := (h.toCore x).toNormedAddCommGroup
      letI : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore (h.toCore x).toCore
      letI : NormedAddCommGroup (F x) := (k.toCore x).toNormedAddCommGroup
      letI : InnerProductSpace ℂ (F x) := InnerProductSpace.ofCore (k.toCore x).toCore
      exact InnerProductSpace.toCore
    have hpure (x : M) (u v : E x) (s t : F x) :
        (core x).inner (u ⊗ₜ[ℂ] s) (v ⊗ₜ[ℂ] t) =
          (h.toCore x).inner u v * (k.toCore x).inner s t := by
      rfl
    have hbase (p : A.Index × B.Index) :
        (C.chart p).baseSet = (A.chart p.1).baseSet ∩ (B.chart p.2).baseSet :=
      (ComplexBundle.exists_tensor_trivialization (A.chart p.1) (B.chart p.2)
        (A.linear p.1) (B.linear p.2)).choose_spec.1
    have hcoord (p : A.Index × B.Index) (x : M) (hx : x ∈ (C.chart p).baseSet)
        (u : E x) (v : F x) (a : Fin (A.rank p.1 * B.rank p.2)) :
        (C.chart p ⟨x, u ⊗ₜ[ℂ] v⟩).2 a =
          (A.chart p.1 ⟨x, u⟩).2 (finProdFinEquiv.symm a).1 *
            (B.chart p.2 ⟨x, v⟩).2 (finProdFinEquiv.symm a).2 := by
      have hspec := (ComplexBundle.exists_tensor_trivialization
        (A.chart p.1) (B.chart p.2) (A.linear p.1) (B.linear p.2)).choose_spec
      simpa only [C, tensorSmoothAtlas, tensorBundleChart, Prod.mk.eta,
        Equiv.apply_symm_apply] using
        hspec.2.2 x (hspec.1 ▸ hx) u v
          (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2
    -- The inverse tensor frame really is the tensor of the two original inverse frames.
    have hframe (p : A.Index × B.Index) (x : M) (hx : x ∈ (C.chart p).baseSet)
        (a : Fin (A.rank p.1 * B.rank p.2)) :
        (C.frameLinearEquiv p x hx).symm (Pi.single a 1) =
          (A.frameLinearEquiv p.1 x ((hbase p) ▸ hx).1).symm
              (Pi.single (finProdFinEquiv.symm a).1 1) ⊗ₜ[ℂ]
            (B.frameLinearEquiv p.2 x ((hbase p) ▸ hx).2).symm
              (Pi.single (finProdFinEquiv.symm a).2 1) := by
      apply (C.frameLinearEquiv p x hx).injective
      rw [LinearEquiv.apply_symm_apply]
      funext b
      symm
      change (C.chart p ⟨x, _⟩).2 b = _
      rw [hcoord p x hx]
      change ((A.frameLinearEquiv p.1 x ((hbase p) ▸ hx).1)
        ((A.frameLinearEquiv p.1 x ((hbase p) ▸ hx).1).symm _)) _ *
        ((B.frameLinearEquiv p.2 x ((hbase p) ▸ hx).2)
        ((B.frameLinearEquiv p.2 x ((hbase p) ▸ hx).2).symm _)) _ = _
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective a
      obtain ⟨⟨b₁, b₂⟩, rfl⟩ := finProdFinEquiv.surjective b
      by_cases h₁ : b₁ = a₁ <;> by_cases h₂ : b₂ = a₂ <;>
        simp only [Equiv.symm_apply_apply, Pi.single_apply,
          finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, (eq_comm : a₁ = b₁ ↔ b₁ = a₁), (eq_comm : a₂ = b₂ ↔ b₂ = a₂), h₁, h₂,
          ite_true, ite_false, true_and, false_and, and_true, and_false,
          one_mul, mul_one, zero_mul, mul_zero]
    let gE (i : A.Index) (a b : Fin (A.rank i)) (x : M) : ℂ :=
      if hx : x ∈ (A.chart i).baseSet then
        (h.toCore x).inner ((A.frameLinearEquiv i x hx).symm (Pi.single a 1))
          ((A.frameLinearEquiv i x hx).symm (Pi.single b 1)) else 0
    let gF (j : B.Index) (a b : Fin (B.rank j)) (x : M) : ℂ :=
      if hx : x ∈ (B.chart j).baseSet then
        (k.toCore x).inner ((B.frameLinearEquiv j x hx).symm (Pi.single a 1))
          ((B.frameLinearEquiv j x hx).symm (Pi.single b 1)) else 0
    let G (p : A.Index × B.Index) (a b : Fin (A.rank p.1 * B.rank p.2)) (x : M) : ℂ :=
      gE p.1 (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1 x *
        gF p.2 (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm b).2 x
    have hG (p : A.Index × B.Index) (a b : Fin (A.rank p.1 * B.rank p.2)) :
        ContMDiffOn I 𝓘(ℝ, ℂ) ∞ (G p a b) (C.chart p).baseSet := by
      have hE : ContMDiffOn I 𝓘(ℝ, ℂ) ∞
          (gE p.1 (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1)
          (A.chart p.1).baseSet := hh p.1 _ _
      have hF : ContMDiffOn I 𝓘(ℝ, ℂ) ∞
          (gF p.2 (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm b).2)
          (B.chart p.2).baseSet := hk p.2 _ _
      exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
        ((hE.mono (fun x hx ↦ ((hbase p) ▸ hx).1)).prodMk_space
          (hF.mono (fun x hx ↦ ((hbase p) ▸ hx).2)))
    have hGram (p : A.Index × B.Index) (x : M) (hx : x ∈ (C.chart p).baseSet)
        (a b : Fin (A.rank p.1 * B.rank p.2)) :
        (core x).inner ((C.frameLinearEquiv p x hx).symm (Pi.single a 1))
          ((C.frameLinearEquiv p x hx).symm (Pi.single b 1)) = G p a b x := by
      rw [hframe p x hx a, hframe p x hx b, hpure]
      simp only [G, gE, gF, dite_eq_left (((hbase p) ▸ hx).1),
        dite_eq_left (((hbase p) ▸ hx).2)]
    -- Sesquilinearity expands the same algebraic form in the actual tensor frame.
    have hformula (p : A.Index × B.Index) (x : M) (hx : x ∈ (C.chart p).baseSet)
        (u v : T x) :
        (core x).inner u v = ∑ a, ∑ b,
          conj ((C.chart p ⟨x, u⟩).2 a) * G p a b x * (C.chart p ⟨x, v⟩).2 b := by
      let : InnerProductSpace.Core ℂ (T x) := core x
      let L : T x →ₗ⋆[ℂ] T x →ₗ[ℂ] ℂ :=
        LinearMap.mk₂'ₛₗ _ _ (core x).inner
          (fun a b c ↦ (core x).add_left a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
          (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
      have hexpand (w : T x) :
          ∑ a, (C.chart p ⟨x, w⟩).2 a •
            (C.frameLinearEquiv p x hx).symm (Pi.single a 1) = w := by
        have heq := congrArg (C.frameLinearEquiv p x hx).symm
          ((Pi.basisFun ℂ (Fin (C.rank p))).sum_repr ((C.frameLinearEquiv p x hx) w))
        simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply,
          LinearEquiv.symm_apply_apply] at heq
        simpa [SmoothComplexBundleAtlas.frameLinearEquiv] using heq
      change L u v = _
      conv_lhs => rw [← hexpand u, map_sum]
      simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro a _
      conv_lhs => rw [← hexpand v, map_sum]
      simp only [map_smul, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      change conj ((C.chart p ⟨x, u⟩).2 a) *
        ((C.chart p ⟨x, v⟩).2 b * (core x).inner
          ((C.frameLinearEquiv p x hx).symm (Pi.single a 1))
          ((C.frameLinearEquiv p x hx).symm (Pi.single b 1))) = _
      rw [hGram]
      ring
    -- Joint continuity is proved for the original double-bundle topology, not the temporary norms.
    let : ComplexBundle.IsFiniteRank T := C.isFiniteRank
    let : TopologicalSpace (TotalSpace Unit (T ×ᵇ T)) := ComplexBundle.sumTopology
    have hfst : Continuous (fun z : TotalSpace Unit (T ×ᵇ T) ↦
        (⟨z.proj, z.snd.1⟩ : TotalSpace Unit T)) := ComplexBundle.continuous_sum_fst
    have hsnd : Continuous (fun z : TotalSpace Unit (T ×ᵇ T) ↦
        (⟨z.proj, z.snd.2⟩ : TotalSpace Unit T)) := ComplexBundle.continuous_sum_snd
    have hprojection : Continuous (π Unit (T ×ᵇ T)) :=
      (ComplexBundle.continuous_proj (E := T)).comp hfst
    have hcontinuous : Continuous (fun z : TotalSpace Unit (T ×ᵇ T) ↦
        (core z.proj).inner z.snd.1 z.snd.2) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      obtain ⟨p, hp⟩ := C.covers z.proj
      let U := π Unit (T ×ᵇ T) ⁻¹' (C.chart p).baseSet
      have hleft : ContinuousOn (fun w : TotalSpace Unit (T ×ᵇ T) ↦
          (C.chart p ⟨w.proj, w.snd.1⟩).2) U :=
        continuous_snd.comp_continuousOn
          ((C.chart p).toOpenPartialHomeomorph.continuousOn.comp hfst.continuousOn
            (fun w hw ↦ (C.chart p).mem_source.mpr hw))
      have hright : ContinuousOn (fun w : TotalSpace Unit (T ×ᵇ T) ↦
          (C.chart p ⟨w.proj, w.snd.2⟩).2) U :=
        continuous_snd.comp_continuousOn
          ((C.chart p).toOpenPartialHomeomorph.continuousOn.comp hsnd.continuousOn
            (fun w hw ↦ (C.chart p).mem_source.mpr hw))
      have hsum : ContinuousOn (fun w : TotalSpace Unit (T ×ᵇ T) ↦ ∑ a, ∑ b,
          conj ((C.chart p ⟨w.proj, w.snd.1⟩).2 a) * G p a b w.proj *
            (C.chart p ⟨w.proj, w.snd.2⟩).2 b) U := by
        apply continuousOn_finsetSum
        intro a _
        apply continuousOn_finsetSum
        intro b _
        exact ((Complex.conjCLE.continuous.comp_continuousOn
          ((continuous_apply a).comp_continuousOn hleft)).mul
          ((hG p a b).continuousOn.comp hprojection.continuousOn (fun w hw ↦ hw))).mul
          ((continuous_apply b).comp_continuousOn hright)
      have hactual : ContinuousOn (fun w : TotalSpace Unit (T ×ᵇ T) ↦
          (core w.proj).inner w.snd.1 w.snd.2) U :=
        hsum.congr (fun w hw ↦ hformula p w.proj hw w.snd.1 w.snd.2)
      exact hactual.continuousAt (((C.chart p).open_baseSet.preimage hprojection).mem_nhds hp)
    let l : ComplexBundle.ContinuousHermitianMetric T := {
      toCore := core
      continuous_pairing := hcontinuous
      isFiniteRank := C.isFiniteRank }
    refine ⟨l, ⟨?_, hpure⟩, ?_⟩
    · intro p a b
      apply (hG p a b).congr
      intro x hx
      change (if hx : x ∈ (C.chart p).baseSet then
        (core x).inner ((C.frameLinearEquiv p x hx).symm (Pi.single a 1))
          ((C.frameLinearEquiv p x hx).symm (Pi.single b 1)) else 0) = _
      rw [dite_eq_left hx]
      exact hGram p x hx a b
    · intro l' hl'
      have hinner (x : M) (u v : T x) :
          (l'.toCore x).inner u v = (core x).inner u v := by
        induction u using TensorProduct.inductionOn with
        | tmul s t =>
          induction v using TensorProduct.inductionOn with
          | tmul s' t' => rw [hl'.2 x s s' t t', hpure]
          | add v w hv hw =>
            rw [InnerProductSpace.Core.inner_add_right (c := (l'.toCore x).toCore),
              InnerProductSpace.Core.inner_add_right (c := (core x).toCore), hv, hw]
        | add u w hu hw => rw [(l'.toCore x).add_left, (core x).add_left, hu, hw]
      have hext (x : M) (a b : InnerProductSpace.Core ℂ (T x))
          (heq : ∀ u v : T x, a.inner u v = b.inner u v) : a = b := by
        cases a with
        | mk a ha =>
          cases b with
          | mk b hb =>
            congr 1
            cases a with
            | mk ia h₁ h₂ h₃ h₄ =>
              cases b with
              | mk ib h₅ h₆ h₇ h₈ =>
                congr 1
                cases ia
                cases ib
                congr 1
                funext u v
                exact heq u v
      have hcores : l'.toCore = core := by
        funext x
        exact hext x (l'.toCore x) (core x) (hinner x)
      cases l' with
      | mk core' continuous' =>
        change core' = core at hcores
        cases hcores
        rfl

/-- The tensor metric with the original factor pairings and no substituted fiber norm. -/
def tensorAtlasMetric
    (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (k : ComplexBundle.ContinuousHermitianMetric F) (hk : B.IsSmoothHermitianMetric k) :
    ComplexBundle.ContinuousHermitianMetric (fun x ↦ E x ⊗[ℂ] F x) :=
  (existsUnique_tensorAtlasMetric h hh k hk).exists.choose

/-- The selected product metric is smooth and retains its exact original pure-vector formula. -/
theorem tensorAtlasMetric_properties
    (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (k : ComplexBundle.ContinuousHermitianMetric F) (hk : B.IsSmoothHermitianMetric k) :
    (tensorSmoothAtlas A B).IsSmoothHermitianMetric (tensorAtlasMetric h hh k hk) ∧
      ∀ (x : M) (s s' : E x) (t t' : F x),
        ((tensorAtlasMetric h hh k hk).toCore x).inner (s ⊗ₜ[ℂ] t) (s' ⊗ₜ[ℂ] t') =
          (h.toCore x).inner s s' * (k.toCore x).inner t t' := by
  /- Read both properties from the single metric existence witness used
  by tensorAtlasMetric. No separate metric is selected for the unitary result. -/
  exact (existsUnique_tensorAtlasMetric h hh k hk).exists.choose_spec

/-- The same product connection preserves the same product metric when its factors do. -/
theorem atlasTensorConnection_isUnitary
    (covE : AtlasComplexConnection A) (covF : AtlasComplexConnection B)
    (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (k : ComplexBundle.ContinuousHermitianMetric F) (hk : B.IsSmoothHermitianMetric k)
    (hE : covE.IsUnitary h) (hF : covF.IsUnitary k) :
    (atlasTensorConnection covE covF).IsUnitary (tensorAtlasMetric h hh k hk) := by
  /- Prove the metric identity on original pure sections first. For the
  passage to arbitrary sections, compare the same selected tensor connection
  with a connection preserving the same selected tensor metric. Their
  difference is fiber-linear, and its metric defect is sesquilinear; supported
  factor sections and double tensor induction make that defect vanish. -/
  set_option backward.isDefEq.respectTransparency false in
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, H)
    let C := tensorSmoothAtlas A B
    let T := fun x : M ↦ E x ⊗[ℂ] F x
    let covT := atlasTensorConnection covE covF
    let l := tensorAtlasMetric h hh k hk
    have hl := tensorAtlasMetric_properties h hh k hk
    have hpure (s s' : A.smoothSections) (t t' : B.smoothSections) (x : M)
        (X : TangentSpace I x) :
        mvfderiv I (fun y ↦ (l.toCore y).inner
            ((tensorSmoothSection A B s t).val y)
            ((tensorSmoothSection A B s' t').val y)) x X =
          (l.toCore x).inner (covT.covariantDerivative (tensorSmoothSection A B s t) x X)
              ((tensorSmoothSection A B s' t').val x) +
            (l.toCore x).inner ((tensorSmoothSection A B s t).val x)
              (covT.covariantDerivative (tensorSmoothSection A B s' t') x X) := by
      let f := fun y : M ↦ (h.toCore y).inner (s.val y) (s'.val y)
      let g := fun y : M ↦ (k.toCore y).inner (t.val y) (t'.val y)
      have hfunction : (fun y ↦ (l.toCore y).inner
          ((tensorSmoothSection A B s t).val y)
          ((tensorSmoothSection A B s' t').val y)) = f * g := by
        funext y
        exact hl.2 y (s.val y) (s'.val y) (t.val y) (t'.val y)
      have hf : MDifferentiableAt I 𝓘(ℝ, ℂ) f x :=
        (A.contMDiff_pairing h hh s s').mdifferentiableAt (by simp)
      have hg : MDifferentiableAt I 𝓘(ℝ, ℂ) g x :=
        (B.contMDiff_pairing k hk t t').mdifferentiableAt (by simp)
      have hdproduct : mvfderiv I (f * g) x =
          f x • mvfderiv I g x + g x • mvfderiv I f x :=
        (hf.hasMFDerivAt.mul hg.hasMFDerivAt).mfderiv
      rw [hfunction, hdproduct]
      dsimp only [covT]
      rw [atlasTensorConnection_apply, atlasTensorConnection_apply]
      simp only [add_apply, smul_apply, smul_eq_mul, tensorSmoothSection]
      rw [(l.toCore x).add_left,
        InnerProductSpace.Core.inner_add_right (c := (l.toCore x).toCore),
        hl.2, hl.2, hl.2, hl.2]
      have hE' : mvfderiv I f x X =
          (h.toCore x).inner (covE.covariantDerivative s x X) (s'.val x) +
            (h.toCore x).inner (s.val x) (covE.covariantDerivative s' x X) := hE s s' x X
      have hF' : mvfderiv I g x X =
          (k.toCore x).inner (covF.covariantDerivative t x X) (t'.val x) +
            (k.toCore x).inner (t.val x) (covF.covariantDerivative t' x X) := hF t t' x X
      rw [hE', hF']
      dsimp only [f, g]
      ring
    -- Keep the auxiliary preserving connection on precisely the same chosen metric.
    obtain ⟨covU, hU⟩ := AtlasComplexConnection.exists_unitary l hl.1
    let V (i : C.Index) := EuclideanSpace ℂ (Fin (C.rank i))
    let CT (i : C.Index) (x : M) (hx : x ∈ (C.chart i).baseSet) : T x ≃ₗ[ℂ] V i :=
      (C.frameLinearEquiv i x hx).trans (EuclideanSpace.equiv _ ℂ).symm.toLinearEquiv
    have hexpressionCoord (c : OpenPartialHomeomorph M H) (i : C.Index)
        (Ω : H → H →L[ℝ] (V i →L[ℂ] V i)) (u : C.smoothSections)
        (x : M) (hx : x ∈ (C.chart i).baseSet) (X : TangentSpace I x) :
        CT i x hx (atlasConnectionExpression C c i Ω u x hx X) =
          fderiv ℝ (atlasSectionInChart C c i u.val) (c x) (mfderiv I I c x X) +
            Ω (c x) (mfderiv I I c x X) (atlasSectionInChart C c i u.val (c x)) := by
      change (EuclideanSpace.equiv _ ℂ).symm
        ((C.frameLinearEquiv i x hx) ((C.frameLinearEquiv i x hx).symm _)) = _
      rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    let Δ (x : M) (X : TangentSpace I x) : T x →ₗ[ℂ] T x :=
      let i := Classical.choose (C.covers x)
      let hx := Classical.choose_spec (C.covers x)
      let c := chartAt H x
      let Y := mfderiv I I c x X
      (CT i x hx).symm.toLinearMap.comp
        ((covT.connectionForm c i (c x) Y - covU.connectionForm c i (c x) Y).toLinearMap.comp
          (CT i x hx).toLinearMap)
    have hdelta (u : C.smoothSections) (x : M) (X : TangentSpace I x) :
        covT.covariantDerivative u x X =
          covU.covariantDerivative u x X + Δ x X (u.val x) := by
      let i := Classical.choose (C.covers x)
      let hx := Classical.choose_spec (C.covers x)
      let c := chartAt H x
      apply (CT i x hx).injective
      rw [map_add,
        covT.covariantDerivative_eq u c (chart_mem_atlas H x) i x
          ⟨mem_chart_source H x, hx⟩ X,
        covU.covariantDerivative_eq u c (chart_mem_atlas H x) i x
          ⟨mem_chart_source H x, hx⟩ X,
        hexpressionCoord, hexpressionCoord]
      have hv : atlasSectionInChart C c i u.val (c x) = CT i x hx (u.val x) := by
        dsimp only [atlasSectionInChart]
        rw [c.left_inv (mem_chart_source H x)]
        rfl
      change _ = _ + (CT i x hx) ((CT i x hx).symm _)
      rw [LinearEquiv.apply_symm_apply]
      let du : V i := fderiv ℝ (atlasSectionInChart C c i u.val) (c x)
        (mfderiv I I c x X)
      let a : V i := atlasSectionInChart C c i u.val (c x)
      let L : V i →L[ℂ] V i := covT.connectionForm c i (c x) (mfderiv I I c x X)
      let K : V i →L[ℂ] V i := covU.connectionForm c i (c x) (mfderiv I I c x X)
      change du + L a = (du + K a) + (L - K) (CT i x hx (u.val x))
      rw [← hv, sub_apply]
      abel
    have hevaluationE (x : M) (w : E x) :
        ∃ u : A.smoothSections, u.val x = w := by
      let W (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
      let ee (i : A.Index) := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
      let cc (i : A.Index) (y : M) (hy : y ∈ (A.chart i).baseSet) : E y ≃ₗ[ℂ] W i :=
        (A.frameLinearEquiv i y hy).trans (ee i).symm.toLinearEquiv
      obtain ⟨i, hi⟩ := A.covers x
      obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        ((A.chart i).open_baseSet.mem_nhds hi)
      let a := cc i x hi w
      let s (y : M) : E y := if hy : y ∈ (A.chart i).baseSet then
        (ψ y : ℂ) • (cc i y hy).symm a else 0
      have hpoint (y : M) (hy : y ∈ (A.chart i).baseSet) (b : W i) :
          (⟨y, (cc i y hy).symm b⟩ : TotalSpace Unit E) =
            (A.chart i).toPartialEquiv.symm (y, ee i b) := by
        exact TotalSpace.mk_cast (F := Unit) (E := E) ((A.chart i).proj_symm_apply' hy) _
      let p (j : A.Index) (y : M) : Fin (A.rank j) → ℂ :=
        ∑ b : Fin (A.rank i), a b •
          (A.chart j ((A.chart i).toPartialEquiv.symm (y, Pi.single b 1))).2
      have hp (j : A.Index) (y : M) (hy : y ∈ (A.chart i).baseSet)
          (hyj : y ∈ (A.chart j).baseSet) :
          (A.chart j ⟨y, (cc i y hy).symm a⟩).2 = p j y := by
        let L := A.frameLinearEquiv j y hyj
        have hexpand : ∑ b : Fin (A.rank i), a b •
            (cc i y hy).symm (EuclideanSpace.single b 1) = (cc i y hy).symm a := by
          simpa only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
            EuclideanSpace.basisFun_repr] using congrArg (cc i y hy).symm
              ((EuclideanSpace.basisFun (Fin (A.rank i)) ℂ).sum_repr a)
        change L ((cc i y hy).symm a) = _
        rw [← hexpand, map_sum]
        simp only [map_smul]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        change (A.chart j ⟨y, (cc i y hy).symm (EuclideanSpace.single b 1)⟩).2 = _
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
          change (A.frameLinearEquiv j z hz.2) ((ψ z : ℂ) • (cc i z hz.1).symm a) = _
          rw [map_smul]
          exact congrArg (fun b : Fin (A.rank j) → ℂ ↦ (ψ z : ℂ) • b) (hp j z hz.1 hz.2)
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
      exact (cc i x hi).symm_apply_apply w
    have hevaluationF (x : M) (w : F x) :
        ∃ u : B.smoothSections, u.val x = w := by
      let W (i : B.Index) := EuclideanSpace ℂ (Fin (B.rank i))
      let ee (i : B.Index) := EuclideanSpace.equiv (Fin (B.rank i)) ℂ
      let cc (i : B.Index) (y : M) (hy : y ∈ (B.chart i).baseSet) : F y ≃ₗ[ℂ] W i :=
        (B.frameLinearEquiv i y hy).trans (ee i).symm.toLinearEquiv
      obtain ⟨i, hi⟩ := B.covers x
      obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        ((B.chart i).open_baseSet.mem_nhds hi)
      let a := cc i x hi w
      let s (y : M) : F y := if hy : y ∈ (B.chart i).baseSet then
        (ψ y : ℂ) • (cc i y hy).symm a else 0
      have hpoint (y : M) (hy : y ∈ (B.chart i).baseSet) (b : W i) :
          (⟨y, (cc i y hy).symm b⟩ : TotalSpace Unit F) =
            (B.chart i).toPartialEquiv.symm (y, ee i b) := by
        exact TotalSpace.mk_cast (F := Unit) (E := F) ((B.chart i).proj_symm_apply' hy) _
      let p (j : B.Index) (y : M) : Fin (B.rank j) → ℂ :=
        ∑ b : Fin (B.rank i), a b •
          (B.chart j ((B.chart i).toPartialEquiv.symm (y, Pi.single b 1))).2
      have hp (j : B.Index) (y : M) (hy : y ∈ (B.chart i).baseSet)
          (hyj : y ∈ (B.chart j).baseSet) :
          (B.chart j ⟨y, (cc i y hy).symm a⟩).2 = p j y := by
        let L := B.frameLinearEquiv j y hyj
        have hexpand : ∑ b : Fin (B.rank i), a b •
            (cc i y hy).symm (EuclideanSpace.single b 1) = (cc i y hy).symm a := by
          simpa only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
            EuclideanSpace.basisFun_repr] using congrArg (cc i y hy).symm
              ((EuclideanSpace.basisFun (Fin (B.rank i)) ℂ).sum_repr a)
        change L ((cc i y hy).symm a) = _
        rw [← hexpand, map_sum]
        simp only [map_smul]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        change (B.chart j ⟨y, (cc i y hy).symm (EuclideanSpace.single b 1)⟩).2 = _
        rw [hpoint]
        rfl
      have hpsmooth (j : B.Index) :
          ContMDiffOn I 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞ (p j)
            ((B.chart i).baseSet ∩ (B.chart j).baseSet) := by
        apply contMDiffOn_finsetSum
        intro b _
        have hscale := ((a b • ContinuousLinearMap.id ℂ (Fin (B.rank j) → ℂ))
          |>.restrictScalars ℝ).contMDiff (n := ∞)
        exact hscale.comp_contMDiffOn (B.contMDiffOn_coordChange i j b)
      have hψsmooth : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun y : M ↦ (ψ y : ℂ)) :=
        Complex.ofRealCLM.contMDiff.comp ψ.contMDiff
      have hs : B.IsSmoothSection s := by
        intro j y hyj
        by_cases hy : y ∈ tsupport (ψ : M → ℝ)
        · have hyi := hψ hy
          have hlocal := (hpsmooth j).contMDiffAt
            (((B.chart i).open_baseSet.inter (B.chart j).open_baseSet).mem_nhds ⟨hyi, hyj⟩)
          have hmul : ContDiff ℝ ∞
              (fun z : ℂ × (Fin (B.rank j) → ℂ) ↦ z.1 • z.2) := contDiff_smul
          have hscaled := hmul.contMDiff.contMDiffAt.comp y
            (hψsmooth.contMDiffAt.prodMk_space hlocal)
          apply (hscaled.congr_of_eventuallyEq ?_).contMDiffWithinAt
          filter_upwards [((B.chart i).open_baseSet.inter
            (B.chart j).open_baseSet).mem_nhds ⟨hyi, hyj⟩] with z hz
          dsimp only [s]
          rw [dite_eq_left hz.1]
          change (B.frameLinearEquiv j z hz.2) ((ψ z : ℂ) • (cc i z hz.1).symm a) = _
          rw [map_smul]
          exact congrArg (fun b : Fin (B.rank j) → ℂ ↦ (ψ z : ℂ) • b) (hp j z hz.1 hz.2)
        · have hzero : (fun z : M ↦ (B.chart j ⟨z, s z⟩).2) =ᶠ[nhds y]
              (fun _ ↦ (0 : Fin (B.rank j) → ℂ)) := by
            filter_upwards [(isClosed_tsupport (ψ : M → ℝ)).isOpen_compl.mem_nhds hy,
              (B.chart j).open_baseSet.mem_nhds hyj] with z hz hzj
            have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
            have hsz : s z = 0 := by
              dsimp only [s]
              split_ifs <;> simp only [hψz, Complex.ofReal_zero, zero_smul]
            rw [hsz]
            exact (B.linear j z hzj).map_zero
          exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
      refine ⟨⟨s, hs⟩, ?_⟩
      change s x = w
      dsimp only [s]
      rw [dite_eq_left hi, ψ.eq_one, Complex.ofReal_one, one_smul]
      exact (cc i x hi).symm_apply_apply w
    -- Pure global sections test every pure pair of actual fiber vectors.
    have hdefectPure (s s' : A.smoothSections) (t t' : B.smoothSections) (x : M)
        (X : TangentSpace I x) :
        (l.toCore x).inner (Δ x X (s.val x ⊗ₜ[ℂ] t.val x))
            (s'.val x ⊗ₜ[ℂ] t'.val x) +
          (l.toCore x).inner (s.val x ⊗ₜ[ℂ] t.val x)
            (Δ x X (s'.val x ⊗ₜ[ℂ] t'.val x)) = 0 := by
      have heq := (hpure s s' t t' x X).symm.trans
        (hU (tensorSmoothSection A B s t) (tensorSmoothSection A B s' t') x X)
      rw [hdelta, hdelta] at heq
      simp only [tensorSmoothSection, (l.toCore x).add_left,
        InnerProductSpace.Core.inner_add_right (c := (l.toCore x).toCore)] at heq
      linear_combination heq
    have hdefect (x : M) (X : TangentSpace I x) (u v : T x) :
        (l.toCore x).inner (Δ x X u) v + (l.toCore x).inner u (Δ x X v) = 0 := by
      induction u using TensorProduct.inductionOn with
      | tmul a b =>
        induction v using TensorProduct.inductionOn with
        | tmul c d =>
          obtain ⟨s, hs⟩ := hevaluationE x a
          obtain ⟨t, ht⟩ := hevaluationF x b
          obtain ⟨s', hs'⟩ := hevaluationE x c
          obtain ⟨t', ht'⟩ := hevaluationF x d
          simpa only [hs, ht, hs', ht'] using hdefectPure s s' t t' x X
        | add v w hv hw =>
          simp only [map_add,
            InnerProductSpace.Core.inner_add_right (c := (l.toCore x).toCore)]
          linear_combination hv + hw
      | add u w hu hw =>
        simp only [map_add, (l.toCore x).add_left]
        linear_combination hu + hw
    -- The auxiliary derivative cancels, leaving compatibility for the selected tensor connection.
    intro u v x X
    change mvfderiv I (fun y ↦ (l.toCore y).inner (u.val y) (v.val y)) x X =
      (l.toCore x).inner (covT.covariantDerivative u x X) (v.val x) +
        (l.toCore x).inner (u.val x) (covT.covariantDerivative v x X)
    have hunitary : mvfderiv I
          (fun y ↦ (l.toCore y).inner (u.val y) (v.val y)) x X =
        (l.toCore x).inner (covU.covariantDerivative u x X) (v.val x) +
          (l.toCore x).inner (u.val x) (covU.covariantDerivative v x X) := hU u v x X
    rw [hunitary, hdelta u x X, hdelta v x X, (l.toCore x).add_left,
      InnerProductSpace.Core.inner_add_right (c := (l.toCore x).toCore)]
    linear_combination -(hdefect x X (u.val x) (v.val x))

end AtiyahSinger

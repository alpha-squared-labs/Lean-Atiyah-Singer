/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.AtlasPrincipalSymbol
public import AtiyahSinger.Geometry.AtlasComplexConnection

/-!
# First-order operators from an actual connection contraction

Public module ID: M1091.

A cotangent-linear smooth bundle map contracts the supplied covariant
derivative, giving an actual operator on original atlas sections. The finite
sum uses the model tangent basis and its genuine dual; basis independence
makes it the intrinsic contraction. The action is specified before its
principal symbol is identified, so quantization of an arbitrary equal symbol
cannot substitute for this operator.

Sources: SG II.5 (5.0) and Lemma 5.1. The atlas formulation includes varying
ranks and distinct source/target bundles. With D_j = -i partial_j, the symbol
is +i times the contraction map. Smoothness off zero together with real
linearity suffices: nonzero local basis covectors determine all coefficients.
No Clifford relation, unitary connection or formal-adjoint claim is needed
for this general construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

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
  (cov : AtlasComplexConnection A)
  (c : AtlasSymbolFunction (n := n) E F)
  (hc : ∀ x : M, IsLinearMap ℝ (c x))
  (hs : IsSmoothOffZeroAtlasSymbol A B c)

include hc hs in

set_option linter.unusedSectionVars false in
/-- The supplied connection and linear contraction determine one actual first-order operator. -/
theorem existsUnique_atlasConnectionContraction :
    ∃! D : AtlasDifferentialOperator A B 1,
      ∀ (u : A.smoothSections) (x : M),
        (D.toLinearMap u).val x =
          ∑ j : Fin n, c x (EuclideanSpace.proj j)
            (cov.covariantDerivative u x (EuclideanSpace.single j 1)) := by
  /- Stage 1: expand the same real-linear contraction and covariant
  derivative in a local tangent basis and its dual. Change-of-basis matrices
  cancel in the sum, so the displayed model-basis expression is intrinsic.
  Stage 2: in every original bundle chart the connection is d+Gamma.
  The contraction coefficients are smooth: evaluate the off-zero smooth
  family on each nonzero local dual basis vector, then use real linearity.
  Thus its contraction has smooth coefficients of order at most one and
  sends the original smooth sections to original smooth sections. At n=0
  both the sum and the cotangent-linear map vanish.
  Stage 3: additivity and complex linearity of the local connection formula
  and each fiber map give a complex-linear section operator. The local
  expressions agree by the connection overlap law and basis independence.
  These supply its AtlasDifferentialOperator certificate. The pointwise
  action determines the linear map uniquely; its remaining field is a proof. -/
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, H)
  let VA (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
  let VB (j : B.Index) := EuclideanSpace ℂ (Fin (B.rank j))
  let ea (i : A.Index) := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let eb (j : B.Index) := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
  let e (a : Fin n) : H := EuclideanSpace.single a 1
  let p (a : Fin n) : H →L[ℝ] ℝ := EuclideanSpace.proj a
  let CA (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) : E x ≃ₗ[ℂ] VA i :=
    (A.frameLinearEquiv i x hx).trans (ea i).symm.toLinearEquiv
  let CB (j : B.Index) (x : M) (hx : x ∈ (B.chart j).baseSet) : F x ≃ₗ[ℂ] VB j :=
    (B.frameLinearEquiv j x hx).trans (eb j).symm.toLinearEquiv
  let D (u : A.smoothSections) (x : M) : F x :=
    ∑ a : Fin n, c x (p a) (cov.covariantDerivative u x (e a))
  let T (d : OpenPartialHomeomorph M H) (i : A.Index) (j : B.Index)
      (a : Fin n) (z : H) : VA i →L[ℂ] VB j :=
    atlasGlobalSymbolInChart A B c d i j z (e a)
  -- A simultaneous tangent/dual expansion preserves the original contraction.
  have htrace {s t : ℕ}
      (C : (H →L[ℝ] ℝ) →ₗ[ℝ]
        (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t)))
      (P : H →ₗ[ℝ] EuclideanSpace ℂ (Fin s)) (L : H →L[ℝ] H) :
      ∑ a : Fin n, C (p a) (P (L (e a))) =
        ∑ a : Fin n, C ((p a).comp L) (P (e a)) := by
    have hsum (v : H) : ∑ a, v a • e a = v := by
      simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, e] using
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v
    have hpull (a : Fin n) : (p a).comp L = ∑ b, (L (e b)) a • p b := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro b
      simp [p, e, EuclideanSpace.basisFun_apply]
      rfl
    calc
      _ = ∑ a, ∑ b, (L (e a)) b • C (p a) (P (e b)) := by
        apply Finset.sum_congr rfl
        intro a _
        conv_lhs => rw [← hsum (L (e a)), map_sum, map_sum]
        simp only [map_smul]
        apply Finset.sum_congr rfl
        intro b _
        exact (C (p a)).toLinearMap.map_smul_of_tower ((L (e a)) b) (P (e b))
      _ = ∑ b, ∑ a, (L (e a)) b • C (p a) (P (e b)) := Finset.sum_comm
      _ = ∑ b, C ((p b).comp L) (P (e b)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hpull, map_sum]
        simp only [map_smul, sum_apply, smul_apply]
  have hlocal (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) (u : A.smoothSections)
      (x : M) (hx : x ∈ d.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet) :
      CB j x hx.2 (D u x) = ∑ a : Fin n, T d i j a (d x)
        (fderiv ℝ (atlasSectionInChart A d i u.val) (d x) (e a) +
          cov.connectionForm d i (d x) (e a) (atlasSectionInChart A d i u.val (d x))) := by
    rcases hx with ⟨⟨hxd, hxi⟩, hxj⟩
    let L : H →L[ℝ] H := mfderiv I I d x
    let f := atlasSectionInChart A d i u.val
    let Γ := cov.connectionForm d i (d x)
    let P : H →ₗ[ℝ] VA i := {
      toFun v := fderiv ℝ f (d x) v + Γ v (f (d x))
      map_add' v w := by
        simp only [map_add, add_apply]
        abel
      map_smul' t v := by
        simp only [map_smul, smul_apply, smul_add, RingHom.id_apply] }
    let C : (H →L[ℝ] ℝ) →ₗ[ℝ] (VA i →L[ℂ] VB j) := {
      toFun ξ := LinearMap.toContinuousLinearMap
        ((CB j x hxj).toLinearMap.comp
          ((c x ξ).comp (CA i x hxi).symm.toLinearMap))
      map_add' ξ η := by
        apply ContinuousLinearMap.ext
        intro v
        change CB j x hxj (c x (ξ + η) ((CA i x hxi).symm v)) = _
        have hh := congrArg
          (fun K : E x →ₗ[ℂ] F x ↦ CB j x hxj (K ((CA i x hxi).symm v)))
          ((hc x).map_add ξ η)
        exact hh.trans (by
          change CB j x hxj (c x ξ ((CA i x hxi).symm v) +
            c x η ((CA i x hxi).symm v)) = _
          rw [map_add]
          rfl)
      map_smul' t ξ := by
        apply ContinuousLinearMap.ext
        intro v
        change CB j x hxj (c x (t • ξ) ((CA i x hxi).symm v)) = _
        have hh := congrArg
          (fun K : E x →ₗ[ℂ] F x ↦ CB j x hxj (K ((CA i x hxi).symm v)))
          ((hc x).map_smul t ξ)
        exact hh.trans (by
          change CB j x hxj ((t : ℂ) • c x ξ ((CA i x hxi).symm v)) = _
          rw [map_smul]
          rfl) }
    have hp (a : Fin n) : covectorFromChart d x (e a) = (p a).comp L := by
      ext v
      change inner ℝ (e a) (L v) = (L v) a
      simpa only [e, map_one, one_mul] using
        EuclideanSpace.inner_single_left a (1 : ℝ) (L v)
    have hT (a : Fin n) (v : VA i) : T d i j a (d x) v = C ((p a).comp L) v := by
      have hraw (z : H) (hi : d.symm z ∈ (A.chart i).baseSet)
          (hj : d.symm z ∈ (B.chart j).baseSet) :
          T d i j a z v = CB j (d.symm z) hj
            (c (d.symm z) (covectorFromChart d (d.symm z) (e a))
              ((CA i (d.symm z) hi).symm v)) := by
        dsimp only [T, atlasGlobalSymbolInChart]
        rw [dite_eq_left ⟨hi, hj⟩]
        rfl
      have hdesc (z : H) (y : M) (hy : d.symm z = y)
          (hi : y ∈ (A.chart i).baseSet) (hj : y ∈ (B.chart j).baseSet) :
          T d i j a z v = CB j y hj
            (c y (covectorFromChart d y (e a)) ((CA i y hi).symm v)) := by
        subst y
        exact hraw z hi hj
      have hh := hdesc (d x) x (d.left_inv hxd) hxi hxj
      rw [hp] at hh
      exact hh
    calc
      _ = ∑ a : Fin n, C (p a) (P (L (e a))) := by
        dsimp only [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        change CB j x hxj (c x (p a) (cov.covariantDerivative u x (e a))) =
          CB j x hxj (c x (p a) ((CA i x hxi).symm (P (L (e a)))))
        rw [cov.covariantDerivative_eq u d hd i x ⟨hxd, hxi⟩ (e a)]
        rfl
      _ = ∑ a : Fin n, C ((p a).comp L) (P (e a)) := htrace C P L
      _ = _ := by simp only [← hT]; rfl
  -- Smoothness is local in the supplied atlases; no global smooth frame is chosen.
  have hcoordSmooth (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (u : A.smoothSections) (z : H)
      (hz : z ∈ d.target ∩ d.symm ⁻¹' (A.chart i).baseSet) :
      ContDiffAt ℝ ∞ (atlasSectionInChart A d i u.val) z := by
    have hcoord := ((ea i).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn (u.property i)
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hd) hz.1
    exact contMDiffAt_iff_contDiffAt.mp
      ((hcoord.contMDiffAt ((A.chart i).open_baseSet.mem_nhds hz.2)).comp z hsymm)
  have hopen (d : OpenPartialHomeomorph M H) (i : A.Index) (j : B.Index) :
      IsOpen (atlasSymbolChartDomain A B d i j) := by
    simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      d.isOpen_inter_preimage_symm ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
  have hTsmooth (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) (a : Fin n) :
      ContDiffOn ℝ ∞ (T d i j a) (atlasSymbolChartDomain A B d i j) := by
    have hne : e a ≠ 0 := by
      intro hh
      have hh' : (1 : ℝ) = 0 := (PiLp.single_eq_zero_iff 2 a).mp hh
      exact one_ne_zero hh'
    exact (hs d hd i j).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz ↦ ⟨hz, hne⟩)
  let J (d : OpenPartialHomeomorph M H) (i : A.Index) (j : B.Index)
      (u : A.smoothSections) (z : H) : VB j :=
    ∑ a : Fin n, T d i j a z
      (fderiv ℝ (atlasSectionInChart A d i u.val) z (e a) +
        cov.connectionForm d i z (e a) (atlasSectionInChart A d i u.val z))
  have hJsmooth (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) (u : A.smoothSections) (z : H)
      (hz : z ∈ atlasSymbolChartDomain A B d i j) : ContDiffAt ℝ ∞ (J d i j u) z := by
    have hf := hcoordSmooth d hd i u z hz.1
    have hdf := hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
    have hΓ := (cov.smooth_connectionForm d hd i).contDiffAt
      ((d.isOpen_inter_preimage_symm (A.chart i).open_baseSet).mem_nhds hz.1)
    apply ContDiffAt.sum
    intro a _
    have hGa : ContDiffAt ℝ ∞ (fun w ↦ cov.connectionForm d i w (e a)) z :=
      hΓ.clm_apply contDiffAt_const
    have hGaf : ContDiffAt ℝ ∞
        (fun w ↦ cov.connectionForm d i w (e a) (atlasSectionInChart A d i u.val w)) z :=
      (((ContinuousLinearMap.restrictScalarsL ℂ (VA i) (VA i) ℝ ℝ).contDiff.contDiffAt).comp z
        hGa).clm_apply hf
    have hT := (hTsmooth d hd i j a).contDiffAt ((hopen d i j).mem_nhds hz)
    have hTR :=
      ((ContinuousLinearMap.restrictScalarsL ℂ (VA i) (VB j) ℝ ℝ).contDiff.contDiffAt).comp z hT
    exact hTR.clm_apply ((hdf.clm_apply contDiffAt_const).add hGaf)
  have hDsmooth (u : A.smoothSections) : B.IsSmoothSection (D u) := by
    intro j x hxj
    obtain ⟨i, hxi⟩ := A.covers x
    let d := chartAt H x
    have hd : d ∈ atlas H M := chart_mem_atlas H x
    have hxd : x ∈ d.source := mem_chart_source H x
    have hx : x ∈ d.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet :=
      ⟨⟨hxd, hxi⟩, hxj⟩
    have hz : d x ∈ atlasSymbolChartDomain A B d i j := by
      simpa only [atlasSymbolChartDomain, Set.mem_inter_iff, Set.mem_preimage,
        d.left_inv hxd] using And.intro (And.intro (d.map_source hxd) hxi) hxj
    have hj := (hJsmooth d hd i j u (d x) hz).contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (I := I) (n := ∞)
        (IsManifold.subset_maximalAtlas hd) hxd)
    have hscalar := ((eb j).toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp x hj
    have hnear : (fun y : M ↦ (B.chart j ⟨y, D u y⟩).2) =ᶠ[nhds x]
        (fun y : M ↦ eb j (J d i j u (d y))) := by
      filter_upwards [((d.open_source.inter (A.chart i).open_baseSet).inter
        (B.chart j).open_baseSet).mem_nhds hx] with y hy
      apply (eb j).symm.injective
      change CB j y hy.2 (D u y) = (eb j).symm (eb j (J d i j u (d y)))
      exact (hlocal d hd i j u y hy).trans ((eb j).symm_apply_apply _).symm
    exact (hscalar.congr_of_eventuallyEq hnear).contMDiffWithinAt
  -- Local first jets preserve addition and complex scalar multiplication.
  have hjetAdd (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (u v : A.smoothSections) (z : H)
      (hz : z ∈ d.target ∩ d.symm ⁻¹' (A.chart i).baseSet) :
      fderiv ℝ (atlasSectionInChart A d i (u + v).val) z =
          fderiv ℝ (atlasSectionInChart A d i u.val) z +
            fderiv ℝ (atlasSectionInChart A d i v.val) z ∧
        atlasSectionInChart A d i (u + v).val z =
          atlasSectionInChart A d i u.val z + atlasSectionInChart A d i v.val z := by
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hd) hz.1
    have hnear : atlasSectionInChart A d i (u + v).val =ᶠ[nhds z]
        (atlasSectionInChart A d i u.val + atlasSectionInChart A d i v.val) := by
      filter_upwards [hsymm.continuousAt.preimage_mem_nhds
        ((A.chart i).open_baseSet.mem_nhds hz.2)] with w hw
      exact ((ea i).symm.congr_arg ((A.linear i (d.symm w) hw).map_add
        (u.val (d.symm w)) (v.val (d.symm w)))).trans
          ((ea i).symm.map_add _ _)
    exact ⟨hnear.fderiv_eq.trans (fderiv_add
      ((hcoordSmooth d hd i u z hz).differentiableAt (by simp))
      ((hcoordSmooth d hd i v z hz).differentiableAt (by simp))), hnear.eq_of_nhds⟩
  have hjetSmul (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (a : ℂ) (u : A.smoothSections) (z : H)
      (hz : z ∈ d.target ∩ d.symm ⁻¹' (A.chart i).baseSet) :
      fderiv ℝ (atlasSectionInChart A d i (a • u).val) z =
          a • fderiv ℝ (atlasSectionInChart A d i u.val) z ∧
        atlasSectionInChart A d i (a • u).val z =
          a • atlasSectionInChart A d i u.val z := by
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hd) hz.1
    have hnear : atlasSectionInChart A d i (a • u).val =ᶠ[nhds z]
        (a • atlasSectionInChart A d i u.val) := by
      filter_upwards [hsymm.continuousAt.preimage_mem_nhds
        ((A.chart i).open_baseSet.mem_nhds hz.2)] with w hw
      exact ((ea i).symm.congr_arg ((A.linear i (d.symm w) hw).map_smul a
        (u.val (d.symm w)))).trans ((ea i).symm.map_smul a _)
    exact ⟨hnear.fderiv_eq.trans (fderiv_const_smul
      ((hcoordSmooth d hd i u z hz).differentiableAt (by simp)) a), hnear.eq_of_nhds⟩
  have hDadd (u v : A.smoothSections) (x : M) : D (u + v) x = D u x + D v x := by
    obtain ⟨i, hxi⟩ := A.covers x
    obtain ⟨j, hxj⟩ := B.covers x
    let d := chartAt H x
    have hd : d ∈ atlas H M := chart_mem_atlas H x
    have hxd : x ∈ d.source := mem_chart_source H x
    have hx : x ∈ d.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet :=
      ⟨⟨hxd, hxi⟩, hxj⟩
    have hz : d x ∈ d.target ∩ d.symm ⁻¹' (A.chart i).baseSet := by
      simpa only [Set.mem_inter_iff, Set.mem_preimage, d.left_inv hxd] using
        And.intro (d.map_source hxd) hxi
    obtain ⟨hderiv, hvalue⟩ := hjetAdd d hd i u v (d x) hz
    apply (CB j x hxj).injective
    rw [map_add, hlocal d hd i j (u + v) x hx, hlocal d hd i j u x hx,
      hlocal d hd i j v x hx, hderiv, hvalue]
    simp only [add_apply, map_add, Finset.sum_add_distrib]
    abel
  have hDsmul (a : ℂ) (u : A.smoothSections) (x : M) : D (a • u) x = a • D u x := by
    obtain ⟨i, hxi⟩ := A.covers x
    obtain ⟨j, hxj⟩ := B.covers x
    let d := chartAt H x
    have hd : d ∈ atlas H M := chart_mem_atlas H x
    have hxd : x ∈ d.source := mem_chart_source H x
    have hx : x ∈ d.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet :=
      ⟨⟨hxd, hxi⟩, hxj⟩
    have hz : d x ∈ d.target ∩ d.symm ⁻¹' (A.chart i).baseSet := by
      simpa only [Set.mem_inter_iff, Set.mem_preimage, d.left_inv hxd] using
        And.intro (d.map_source hxd) hxi
    obtain ⟨hderiv, hvalue⟩ := hjetSmul d hd i a u (d x) hz
    apply (CB j x hxj).injective
    rw [map_smul, hlocal d hd i j (a • u) x hx, hlocal d hd i j u x hx, hderiv, hvalue]
    simp only [smul_apply, map_smul, ← smul_add, ← Finset.smul_sum]
  let P : A.smoothSections →ₗ[ℂ] B.smoothSections := {
    toFun u := ⟨D u, hDsmooth u⟩
    map_add' u v := Subtype.ext (funext (hDadd u v))
    map_smul' a u := Subtype.ext (funext (hDsmul a u)) }
  -- In D_j = -i partial_j coordinates the first coefficients are +i times T.
  let S (d : OpenPartialHomeomorph M H) (i : A.Index) (j : B.Index) (z : H) :
      VA i →L[ℂ] VB j :=
    ∑ a : Fin n, (T d i j a z).comp (cov.connectionForm d i z (e a))
  have hSsmooth (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) :
      ContDiffOn ℝ ∞ (S d i j) (atlasSymbolChartDomain A B d i j) := by
    apply ContDiffOn.sum
    intro a _
    have hΓ : ContDiffOn ℝ ∞ (fun z ↦ cov.connectionForm d i z (e a))
        (atlasSymbolChartDomain A B d i j) :=
      ((cov.smooth_connectionForm d hd i).mono (fun _ hz ↦ hz.1)).clm_apply
        contDiffOn_const
    let μ := (ContinuousLinearMap.compL ℂ (VA i) (VA i) (VB j)).bilinearRestrictScalars ℝ
    exact (μ.contDiff.comp_contDiffOn (hTsmooth d hd i j a)).clm_apply hΓ
  let Q (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) :
      CoordinateDifferentialOperator n (A.rank i) (B.rank j) 1
        (atlasSymbolChartDomain A B d i j) := {
    coefficient := Fin.cases (fun _ ↦ S d i j)
      (fun k α z ↦ Complex.I • T d i j (α ⟨0, Nat.zero_lt_succ k.val⟩) z)
    smooth_coefficient := by
      intro k
      refine Fin.cases (fun _ ↦ hSsmooth d hd i j) (fun k α ↦ ?_) k
      simpa only [Fin.cases_succ] using
        (hTsmooth d hd i j (α ⟨0, Nat.zero_lt_succ k.val⟩)).const_smul Complex.I }
  have hQapply (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) (f : H → VA i) (z : H) :
      (Q d hd i j).apply f z = ∑ a : Fin n, T d i j a z
        (fderiv ℝ f z (e a) + cov.connectionForm d i z (e a) (f z)) := by
    let reindex : (Fin 1 → Fin n) ≃ Fin n := {
      toFun α := α 0
      invFun a := fun _ ↦ a
      left_inv α := by
        funext t
        exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
      right_inv _ := rfl }
    have hsum : (∑ α : Fin 1 → Fin n,
        T d i j (α 0) z (fderiv ℝ f z (e (α 0)))) =
        ∑ a : Fin n, T d i j a z (fderiv ℝ f z (e a)) :=
      reindex.sum_comp (fun a ↦ T d i j a z (fderiv ℝ f z (e a)))
    unfold CoordinateDifferentialOperator.apply
    rw [Fin.sum_univ_two]
    have hone : (1 : Fin 2) = (0 : Fin 1).succ := rfl
    rw [hone]
    simp only [Q, Fin.cases_zero, Fin.cases_succ, Fin.val_succ, Fin.val_zero, zero_add,
      pow_zero, one_smul, iteratedFDeriv_zero_apply, pow_one,
      Fintype.sum_unique, smul_apply, map_smul, smul_smul, neg_mul, Complex.I_mul_I,
      neg_neg]
    change S d i j z (f z) +
      (∑ α : Fin 1 → Fin n,
        T d i j (α 0) z (iteratedFDeriv ℝ 1 f z (fun t ↦ e (α t)))) = _
    simp only [iteratedFDeriv_one_apply]
    rw [hsum]
    simp only [S, sum_apply, ContinuousLinearMap.comp_apply, map_add,
      Finset.sum_add_distrib]
    abel
  have hP : IsAtlasDifferentialOperator A B 1 P := by
    intro d hd i j x hx
    let U := d.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet
    have hmap : d '' U ⊆ atlasSymbolChartDomain A B d i j := by
      rintro _ ⟨y, hy, rfl⟩
      simpa only [atlasSymbolChartDomain, Set.mem_inter_iff, Set.mem_preimage,
        d.left_inv hy.1.1] using And.intro (And.intro (d.map_source hy.1.1) hy.1.2) hy.2
    let R : CoordinateDifferentialOperator n (A.rank i) (B.rank j) 1 (d '' U) := {
      coefficient := (Q d hd i j).coefficient
      smooth_coefficient := fun k α ↦ ((Q d hd i j).smooth_coefficient k α).mono hmap }
    refine ⟨U, (d.open_source.inter (A.chart i).open_baseSet).inter
      (B.chart j).open_baseSet, hx, R, (fun _ hy ↦ hy), ?_⟩
    intro u y hy
    change CB j y hy.2 (D u y) = R.apply (atlasSectionInChart A d i u.val) (d y)
    calc
      _ = _ := hlocal d hd i j u y hy
      _ = (Q d hd i j).apply (atlasSectionInChart A d i u.val) (d y) :=
        (hQapply d hd i j (atlasSectionInChart A d i u.val) (d y)).symm
      _ = R.apply (atlasSectionInChart A d i u.val) (d y) := rfl
  -- The same pointwise action determines the entire bundled operator uniquely.
  let op : AtlasDifferentialOperator A B 1 := ⟨P, hP⟩
  refine ⟨op, (fun _ _ ↦ rfl), ?_⟩
  intro op' hop'
  have heq : op'.toLinearMap = P := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    exact hop' u x
  cases op' with
  | mk L hL =>
    change L = P at heq
    subst L
    rfl

/-- The actual contraction operator selected from its specified covariant-derivative action. -/
def atlasConnectionContraction : AtlasDifferentialOperator A B 1 :=
  (existsUnique_atlasConnectionContraction cov c hc hs).exists.choose

/-- The selected operator is the exact contraction of the supplied connection. -/
theorem atlasConnectionContraction_apply (u : A.smoothSections) (x : M) :
    ((atlasConnectionContraction cov c hc hs).toLinearMap u).val x =
      ∑ j : Fin n, c x (EuclideanSpace.proj j)
        (cov.covariantDerivative u x (EuclideanSpace.single j 1)) := by
  /- Read the action component of the same unique-existence witness.
  This retains the exact connection, cotangent map and original sections. -/
  exact (existsUnique_atlasConnectionContraction cov c hc hs).exists.choose_spec u x

/-- The symbol of the actual contraction is +i times its original cotangent-linear map. -/
theorem atlasConnectionContraction_principalSymbol (x : M)
    (ξ : CotangentFiber (n := n) x) :
    (atlasConnectionContraction cov c hc hs).principalSymbol x ξ = Complex.I • c x ξ := by
  /- Stage 1: in a local tangent frame the derivative part of the exact
  sum is c(e^j) partial_j; the connection matrix terms have order zero.
  Since coordinate differential operators use D_j=-i partial_j, these
  first-order coefficients are +i c(e^j).
  Stage 2: evaluating the leading polynomial at ξ gives +i c(ξ) by the
  real linearity of c and the original dual-basis expansion. The local
  expression uniqueness for this same section operator identifies its
  selected global principal symbol. No independent quantization is used. -/
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, H)
  let VA (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
  let VB (j : B.Index) := EuclideanSpace ℂ (Fin (B.rank j))
  let ea (i : A.Index) := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let eb (j : B.Index) := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
  let e (a : Fin n) : H := EuclideanSpace.single a 1
  let p (a : Fin n) : H →L[ℝ] ℝ := EuclideanSpace.proj a
  let CA (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) : E x ≃ₗ[ℂ] VA i :=
    (A.frameLinearEquiv i x hx).trans (ea i).symm.toLinearEquiv
  let CB (j : B.Index) (x : M) (hx : x ∈ (B.chart j).baseSet) : F x ≃ₗ[ℂ] VB j :=
    (B.frameLinearEquiv j x hx).trans (eb j).symm.toLinearEquiv
  let D (u : A.smoothSections) (x : M) : F x :=
    ∑ a : Fin n, c x (p a) (cov.covariantDerivative u x (e a))
  let T (d : OpenPartialHomeomorph M H) (i : A.Index) (j : B.Index)
      (a : Fin n) (z : H) : VA i →L[ℂ] VB j :=
    atlasGlobalSymbolInChart A B c d i j z (e a)
  -- A simultaneous tangent/dual expansion preserves the original contraction.
  have htrace {s t : ℕ}
      (C : (H →L[ℝ] ℝ) →ₗ[ℝ]
        (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t)))
      (P : H →ₗ[ℝ] EuclideanSpace ℂ (Fin s)) (L : H →L[ℝ] H) :
      ∑ a : Fin n, C (p a) (P (L (e a))) =
        ∑ a : Fin n, C ((p a).comp L) (P (e a)) := by
    have hsum (v : H) : ∑ a, v a • e a = v := by
      simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, e] using
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v
    have hpull (a : Fin n) : (p a).comp L = ∑ b, (L (e b)) a • p b := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro b
      simp [p, e, EuclideanSpace.basisFun_apply]
      rfl
    calc
      _ = ∑ a, ∑ b, (L (e a)) b • C (p a) (P (e b)) := by
        apply Finset.sum_congr rfl
        intro a _
        conv_lhs => rw [← hsum (L (e a)), map_sum, map_sum]
        simp only [map_smul]
        apply Finset.sum_congr rfl
        intro b _
        exact (C (p a)).toLinearMap.map_smul_of_tower ((L (e a)) b) (P (e b))
      _ = ∑ b, ∑ a, (L (e a)) b • C (p a) (P (e b)) := Finset.sum_comm
      _ = ∑ b, C ((p b).comp L) (P (e b)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hpull, map_sum]
        simp only [map_smul, sum_apply, smul_apply]
  have hlocal (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) (u : A.smoothSections)
      (x : M) (hx : x ∈ d.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet) :
      CB j x hx.2 (D u x) = ∑ a : Fin n, T d i j a (d x)
        (fderiv ℝ (atlasSectionInChart A d i u.val) (d x) (e a) +
          cov.connectionForm d i (d x) (e a) (atlasSectionInChart A d i u.val (d x))) := by
    rcases hx with ⟨⟨hxd, hxi⟩, hxj⟩
    let L : H →L[ℝ] H := mfderiv I I d x
    let f := atlasSectionInChart A d i u.val
    let Γ := cov.connectionForm d i (d x)
    let P : H →ₗ[ℝ] VA i := {
      toFun v := fderiv ℝ f (d x) v + Γ v (f (d x))
      map_add' v w := by
        simp only [map_add, add_apply]
        abel
      map_smul' t v := by
        simp only [map_smul, smul_apply, smul_add, RingHom.id_apply] }
    let C : (H →L[ℝ] ℝ) →ₗ[ℝ] (VA i →L[ℂ] VB j) := {
      toFun ξ := LinearMap.toContinuousLinearMap
        ((CB j x hxj).toLinearMap.comp
          ((c x ξ).comp (CA i x hxi).symm.toLinearMap))
      map_add' ξ η := by
        apply ContinuousLinearMap.ext
        intro v
        change CB j x hxj (c x (ξ + η) ((CA i x hxi).symm v)) = _
        have hh := congrArg
          (fun K : E x →ₗ[ℂ] F x ↦ CB j x hxj (K ((CA i x hxi).symm v)))
          ((hc x).map_add ξ η)
        exact hh.trans (by
          change CB j x hxj (c x ξ ((CA i x hxi).symm v) +
            c x η ((CA i x hxi).symm v)) = _
          rw [map_add]
          rfl)
      map_smul' t ξ := by
        apply ContinuousLinearMap.ext
        intro v
        change CB j x hxj (c x (t • ξ) ((CA i x hxi).symm v)) = _
        have hh := congrArg
          (fun K : E x →ₗ[ℂ] F x ↦ CB j x hxj (K ((CA i x hxi).symm v)))
          ((hc x).map_smul t ξ)
        exact hh.trans (by
          change CB j x hxj ((t : ℂ) • c x ξ ((CA i x hxi).symm v)) = _
          rw [map_smul]
          rfl) }
    have hp (a : Fin n) : covectorFromChart d x (e a) = (p a).comp L := by
      ext v
      change inner ℝ (e a) (L v) = (L v) a
      simpa only [e, map_one, one_mul] using
        EuclideanSpace.inner_single_left a (1 : ℝ) (L v)
    have hT (a : Fin n) (v : VA i) : T d i j a (d x) v = C ((p a).comp L) v := by
      have hraw (z : H) (hi : d.symm z ∈ (A.chart i).baseSet)
          (hj : d.symm z ∈ (B.chart j).baseSet) :
          T d i j a z v = CB j (d.symm z) hj
            (c (d.symm z) (covectorFromChart d (d.symm z) (e a))
              ((CA i (d.symm z) hi).symm v)) := by
        dsimp only [T, atlasGlobalSymbolInChart]
        rw [dite_eq_left ⟨hi, hj⟩]
        rfl
      have hdesc (z : H) (y : M) (hy : d.symm z = y)
          (hi : y ∈ (A.chart i).baseSet) (hj : y ∈ (B.chart j).baseSet) :
          T d i j a z v = CB j y hj
            (c y (covectorFromChart d y (e a)) ((CA i y hi).symm v)) := by
        subst y
        exact hraw z hi hj
      have hh := hdesc (d x) x (d.left_inv hxd) hxi hxj
      rw [hp] at hh
      exact hh
    calc
      _ = ∑ a : Fin n, C (p a) (P (L (e a))) := by
        dsimp only [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        change CB j x hxj (c x (p a) (cov.covariantDerivative u x (e a))) =
          CB j x hxj (c x (p a) ((CA i x hxi).symm (P (L (e a)))))
        rw [cov.covariantDerivative_eq u d hd i x ⟨hxd, hxi⟩ (e a)]
        rfl
      _ = ∑ a : Fin n, C ((p a).comp L) (P (e a)) := htrace C P L
      _ = _ := by simp only [← hT]; rfl
  -- Smoothness off zero supplies each first-order coefficient.
  have hTsmooth (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) (a : Fin n) :
      ContDiffOn ℝ ∞ (T d i j a) (atlasSymbolChartDomain A B d i j) := by
    have hne : e a ≠ 0 := by
      intro hh
      have hh' : (1 : ℝ) = 0 := (PiLp.single_eq_zero_iff 2 a).mp hh
      exact one_ne_zero hh'
    exact (hs d hd i j).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz ↦ ⟨hz, hne⟩)
  -- In D_j = -i partial_j coordinates the first coefficients are +i times T.
  let S (d : OpenPartialHomeomorph M H) (i : A.Index) (j : B.Index) (z : H) :
      VA i →L[ℂ] VB j :=
    ∑ a : Fin n, (T d i j a z).comp (cov.connectionForm d i z (e a))
  have hSsmooth (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) :
      ContDiffOn ℝ ∞ (S d i j) (atlasSymbolChartDomain A B d i j) := by
    apply ContDiffOn.sum
    intro a _
    have hΓ : ContDiffOn ℝ ∞ (fun z ↦ cov.connectionForm d i z (e a))
        (atlasSymbolChartDomain A B d i j) :=
      ((cov.smooth_connectionForm d hd i).mono (fun _ hz ↦ hz.1)).clm_apply
        contDiffOn_const
    let μ := (ContinuousLinearMap.compL ℂ (VA i) (VA i) (VB j)).bilinearRestrictScalars ℝ
    exact (μ.contDiff.comp_contDiffOn (hTsmooth d hd i j a)).clm_apply hΓ
  let Q (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) :
      CoordinateDifferentialOperator n (A.rank i) (B.rank j) 1
        (atlasSymbolChartDomain A B d i j) := {
    coefficient := Fin.cases (fun _ ↦ S d i j)
      (fun k α z ↦ Complex.I • T d i j (α ⟨0, Nat.zero_lt_succ k.val⟩) z)
    smooth_coefficient := by
      intro k
      refine Fin.cases (fun _ ↦ hSsmooth d hd i j) (fun k α ↦ ?_) k
      simpa only [Fin.cases_succ] using
        (hTsmooth d hd i j (α ⟨0, Nat.zero_lt_succ k.val⟩)).const_smul Complex.I }
  have hQapply (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M)
      (i : A.Index) (j : B.Index) (f : H → VA i) (z : H) :
      (Q d hd i j).apply f z = ∑ a : Fin n, T d i j a z
        (fderiv ℝ f z (e a) + cov.connectionForm d i z (e a) (f z)) := by
    let reindex : (Fin 1 → Fin n) ≃ Fin n := {
      toFun α := α 0
      invFun a := fun _ ↦ a
      left_inv α := by
        funext t
        exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
      right_inv _ := rfl }
    have hsum : (∑ α : Fin 1 → Fin n,
        T d i j (α 0) z (fderiv ℝ f z (e (α 0)))) =
        ∑ a : Fin n, T d i j a z (fderiv ℝ f z (e a)) :=
      reindex.sum_comp (fun a ↦ T d i j a z (fderiv ℝ f z (e a)))
    unfold CoordinateDifferentialOperator.apply
    rw [Fin.sum_univ_two]
    have hone : (1 : Fin 2) = (0 : Fin 1).succ := rfl
    rw [hone]
    simp only [Q, Fin.cases_zero, Fin.cases_succ, Fin.val_succ, Fin.val_zero, zero_add,
      pow_zero, one_smul, iteratedFDeriv_zero_apply, pow_one,
      Fintype.sum_unique, smul_apply, map_smul, smul_smul, neg_mul, Complex.I_mul_I,
      neg_neg]
    change S d i j z (f z) +
      (∑ α : Fin 1 → Fin n,
        T d i j (α 0) z (iteratedFDeriv ℝ 1 f z (fun t ↦ e (α t)))) = _
    simp only [iteratedFDeriv_one_apply]
    rw [hsum]
    simp only [S, sum_apply, ContinuousLinearMap.comp_apply, map_add,
      Finset.sum_add_distrib]
    abel
  -- Use the exact coordinate action of the selected contraction on the common chart.
  obtain ⟨i, hxi⟩ := A.covers x
  obtain ⟨j, hxj⟩ := B.covers x
  let d := chartAt H x
  have hd : d ∈ atlas H M := chart_mem_atlas H x
  have hxd : x ∈ d.source := mem_chart_source H x
  let U := d.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet
  have hU : IsOpen U :=
    (d.open_source.inter (A.chart i).open_baseSet).inter (B.chart j).open_baseSet
  have hxU : x ∈ U := ⟨⟨hxd, hxi⟩, hxj⟩
  have hmap : d '' U ⊆ atlasSymbolChartDomain A B d i j := by
    rintro _ ⟨y, hy, rfl⟩
    simpa only [atlasSymbolChartDomain, Set.mem_inter_iff, Set.mem_preimage,
      d.left_inv hy.1.1] using And.intro (And.intro (d.map_source hy.1.1) hy.1.2) hy.2
  let R : CoordinateDifferentialOperator n (A.rank i) (B.rank j) 1 (d '' U) := {
    coefficient := (Q d hd i j).coefficient
    smooth_coefficient := fun k α ↦ ((Q d hd i j).smooth_coefficient k α).mono hmap }
  have hR : HasAtlasCoordinateExpression A B 1
      (atlasConnectionContraction cov c hc hs).toLinearMap d i j U R := by
    refine ⟨Set.Subset.rfl, ?_⟩
    intro u y hy
    rw [atlasConnectionContraction_apply]
    change CB j y hy.2 (D u y) = R.apply (atlasSectionInChart A d i u.val) (d y)
    exact (hlocal d hd i j u y hy).trans
      (hQapply d hd i j (atlasSectionInChart A d i u.val) (d y)).symm
  -- Real linearity reconstructs the covector from its chart components.
  let η := covectorInChart d x ξ
  let C : CotangentFiber (n := n) x →ₗ[ℝ] (E x →ₗ[ℂ] F x) := {
    toFun := c x
    map_add' := (hc x).map_add
    map_smul' := (hc x).map_smul }
  have hsum : ∑ a, η a • e a = η := by
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, e] using
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr η
  have hξ : (∑ a, η a • covectorFromChart d x (e a)) = ξ := by
    calc
      _ = covectorFromChart d x η := by
        ext w
        simp only [sum_apply, smul_apply]
        change (∑ a, η a * inner ℝ (e a) (mfderiv I I d x w)) =
          inner ℝ η (mfderiv I I d x w)
        calc
          _ = ∑ a, inner ℝ (η a • e a) (mfderiv I I d x w) := by
            apply Finset.sum_congr rfl
            intro a _
            exact (real_inner_smul_left (e a) (mfderiv I I d x w) (η a)).symm
          _ = inner ℝ (∑ a, η a • e a) (mfderiv I I d x w) :=
            (sum_inner Finset.univ (fun a ↦ η a • e a) (mfderiv I I d x w)).symm
          _ = inner ℝ η (mfderiv I I d x w) :=
            congrArg (fun z : H ↦ inner ℝ z (mfderiv I I d x w)) hsum
      _ = ξ := covectorFromChart_covectorInChart d hd x hxd ξ
  have hC (v : E x) :
      (∑ a, η a • c x (covectorFromChart d x (e a)) v) = c x ξ v := by
    have hh := congrArg (fun K : E x →ₗ[ℂ] F x ↦ K v) (congrArg C hξ)
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at hh
    exact hh
  -- The degree-one polynomial has no contribution from the connection's zero-order term.
  apply LinearMap.ext
  intro v
  have hT (a : Fin n) : T d i j a (d x) (CA i x hxi v) =
      CB j x hxj (c x (covectorFromChart d x (e a)) v) := by
    have hraw (z : H) (y : M) (hy : d.symm z = y)
        (hi : y ∈ (A.chart i).baseSet) (hj : y ∈ (B.chart j).baseSet) (w : E y) :
        T d i j a z (CA i y hi w) =
          CB j y hj (c y (covectorFromChart d y (e a)) w) := by
      subst y
      dsimp only [T, atlasGlobalSymbolInChart]
      rw [dite_eq_left ⟨hi, hj⟩]
      change CB j (d.symm z) hj
        (c (d.symm z) (covectorFromChart d (d.symm z) (e a))
          ((CA i (d.symm z) hi).symm (CA i (d.symm z) hi w))) = _
      rw [LinearEquiv.symm_apply_apply]
    exact hraw (d x) x (d.left_inv hxd) hxi hxj v
  let reindex : (Fin 1 → Fin n) ≃ Fin n := {
    toFun α := α 0
    invFun a := fun _ ↦ a
    left_inv α := by
      funext t
      exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
    right_inv _ := rfl }
  have hpoly : R.principalSymbol (d x) η (CA i x hxi v) =
      Complex.I • CB j x hxj (c x ξ v) := by
    unfold CoordinateDifferentialOperator.principalSymbol
    simp only [R, Q, Fin.val_zero, Fin.prod_univ_one, sum_apply, smul_apply]
    change (∑ α : Fin 1 → Fin n,
      η (α 0) • Complex.I • T d i j (α 0) (d x) (CA i x hxi v)) = _
    have hsum' : (∑ α : Fin 1 → Fin n,
        η (α 0) • Complex.I • T d i j (α 0) (d x) (CA i x hxi v)) =
        ∑ a, η a • Complex.I • T d i j a (d x) (CA i x hxi v) :=
      reindex.sum_comp (fun a ↦ η a • Complex.I • T d i j a (d x) (CA i x hxi v))
    rw [hsum']
    simp only [hT, smul_comm (η _) Complex.I, ← Finset.smul_sum]
    congr 1
    have hmap (a : Fin n) : η a • CB j x hxj
        (c x (covectorFromChart d x (e a)) v) =
        CB j x hxj (η a • c x (covectorFromChart d x (e a)) v) :=
      ((CB j x hxj).toLinearMap.map_smul_of_tower (η a) _).symm
    simpa only [hmap, ← map_sum] using congrArg (CB j x hxj) (hC v)
  apply (CB j x hxj).injective
  have hsymbol := (atlasConnectionContraction cov c hc hs).hasAtlasPrincipalSymbol
    d hd i j U hU R hR x hxU ξ v
  change CB j x hxj ((atlasConnectionContraction cov c hc hs).principalSymbol x ξ v) = _
    at hsymbol
  calc
    _ = R.principalSymbol (d x) η (CA i x hxi v) := hsymbol
    _ = Complex.I • CB j x hxj (c x ξ v) := hpoly
    _ = CB j x hxj ((Complex.I • c x ξ) v) := (map_smul _ _ _).symm

end AtiyahSinger

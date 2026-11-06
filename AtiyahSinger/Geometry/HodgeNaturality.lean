/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HodgeDecomposition
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Naturality of metric Hodge theory under isometric diffeomorphisms

Public module ID: M1277.

P06/E06: a smooth diffeomorphism preserving the supplied tangent metrics
intertwines the actual codifferentials and Hodge Laplacians. The hypothesis
is the original tangent-derivative metric equation, not an assumed operator
intertwining or an unspecified isometry of form spaces. The induced harmonic
map is the restriction of the same smooth pullback already used by de Rham
cohomology. Its canonical Hodge class is the pullback of the original class.

The operator and harmonic-space naturality statements do not require compactness.
Only the canonical Hodge identification with de Rham cohomology uses compactness.
Riemannian densities and Hermitian form metrics are those defined by the same
supplied metrics. Orientation, connectedness and positive dimension are not needed.
Inverse diffeomorphisms therefore supply the natural left actions used on spheres.

Sources: Lawson--Michelsohn, Spin Geometry, II.5, pp.123--126, gives the metric
operators and canonical Hodge identification; III.13.7, p.253, uses their natural
orthogonal-group action. The explicit general isometry naturality argument is
a project supplement. No Hodge star or orientation is added.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Module Set Function
open scoped BigOperators Manifold ContDiff Topology

variable {n m : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  (gM : SmoothTangentMetric (n := n) (M := M))
  (gN : SmoothTangentMetric (n := m) (M := N))
  (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N)
  (he : ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
    gN.inner (e x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) e x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) e x w) =
      gM.inner x v w)

include he in
/-- Pullback by a metric-preserving diffeomorphism commutes with the metric codifferential. -/
theorem smoothFormCodifferential_pullback (p : ℕ) :
    (smoothFormCodifferential gM p).comp (smoothFormPullback e e.contMDiff (p + 1)) =
      (smoothFormPullback e e.contMDiff p).comp (smoothFormCodifferential gN p) := by
  /- Stage 1: the given derivative equation identifies the same induced
  alternating-form metrics under pullback. The coordinate determinant formula
  and change of variables also identify the Riemannian densities of gM and gN.
  Thus metric pullback preserves the integral pairings whenever a test factor
  is compactly supported. A diffeomorphism and its inverse preserve that support.
  Stage 2: conjugate the target codifferential by these actual pullbacks. The
  existing naturality of d and the target formal-adjoint identity show that this
  conjugate satisfies the source formal-adjoint identity for every compactly
  supported test and every unrestricted smooth input. Uniqueness of the original
  source formal adjoint identifies the two linear maps. This argument does not
  infer an adjoint from testing only compactly supported inputs, and it needs
  neither compactness of the manifold nor a chosen orientation. -/
  classical
  -- Inverse manifold derivatives give the actual tangent equivalences.
  let IM := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let IN := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  have hderLeft (x : M) :
      (mfderiv IN IM e.symm (e x)).comp (mfderiv IM IN e x) =
        ContinuousLinearMap.id ℝ (TangentSpace IM x) := by
    rw [← mfderiv_comp x ((e.symm.contMDiff.mdifferentiable (by simp)) (e x))
      ((e.contMDiff.mdifferentiable (by simp)) x)]
    have hcomp : (e.symm : N → M) ∘ (e : M → N) = id := funext e.symm_apply_apply
    rw [hcomp, mfderiv_id]
  have hderRight (x : M) :
      (mfderiv IM IN e x).comp (mfderiv IN IM e.symm (e x)) =
        ContinuousLinearMap.id ℝ (TangentSpace IN (e x)) := by
    have hright' (y : N) :
        (mfderiv IM IN e (e.symm y)).comp (mfderiv IN IM e.symm y) =
          ContinuousLinearMap.id ℝ (TangentSpace IN y) := by
      rw [← mfderiv_comp y ((e.contMDiff.mdifferentiable (by simp)) (e.symm y))
        ((e.symm.contMDiff.mdifferentiable (by simp)) y)]
      have hcomp : (e : M → N) ∘ (e.symm : N → M) = id := funext e.apply_symm_apply
      rw [hcomp, mfderiv_id]
    have hder : mfderiv IM IN e (e.symm (e x)) = mfderiv IM IN e x := by
      congr 1
      exact e.symm_apply_apply x
    exact hder ▸ hright' (e x)
  let F (x : M) : TangentSpace IM x ≃L[ℝ] TangentSpace IN (e x) :=
    { mfderiv IM IN e x with
      invFun := mfderiv IN IM e.symm (e x)
      left_inv := fun v ↦ congrArg (fun f ↦ f v) (hderLeft x)
      right_inv := fun v ↦ congrArg (fun f ↦ f v) (hderRight x)
      continuous_invFun := (mfderiv IN IM e.symm (e x)).continuous }
  -- Empty manifolds are immediate; an actual tangent equivalence fixes the dimension.
  by_cases hM : Nonempty M
  swap
  · let : IsEmpty M := not_nonempty_iff.mp hM
    apply LinearMap.ext
    intro form
    apply Subtype.ext
    funext x
    exact isEmptyElim x
  obtain ⟨x₀⟩ := hM
  have hdim : n = m := by
    have hd := (F x₀).toLinearEquiv.finrank_eq
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) at hd
    simpa only [finrank_euclideanSpace_fin] using hd
  subst m
  -- Compare the original atlas densities before applying the form metric contraction.
  have hvolume : Measure.map e gM.riemannianVolume = gN.riemannianVolume := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, V)
    let GN : N → V →L[ℝ] V →L[ℝ] ℝ := fun z ↦ gN.inner z
    let HM (d : OpenPartialHomeomorph M V) (y : V) : Matrix (Fin n) (Fin n) ℝ :=
      fun i j ↦ gM.inner (d.symm y)
        (mfderiv I I d.symm y (EuclideanSpace.single i 1))
        (mfderiv I I d.symm y (EuclideanSpace.single j 1))
    let HN (c : OpenPartialHomeomorph N V) (y : V) : Matrix (Fin n) (Fin n) ℝ :=
      fun i j ↦ gN.inner (c.symm y)
        (mfderiv I I c.symm y (EuclideanSpace.single i 1))
        (mfderiv I I c.symm y (EuclideanSpace.single j 1))
    let wM (d : OpenPartialHomeomorph M V) (y : V) := Real.sqrt (HM d y).det
    let wN (c : OpenPartialHomeomorph N V) (y : V) := Real.sqrt (HN c y).det
    -- The isometry equation transports the Gram determinant in the original two charts.
    have hchange (d : OpenPartialHomeomorph M V) (c : OpenPartialHomeomorph N V)
        (hd : d ∈ atlas V M) (hc : c ∈ atlas V N)
        (y : V) (hy : y ∈ ((d.symm.trans e.toHomeomorph.toOpenPartialHomeomorph).trans c).source) :
        let t := (d.symm.trans e.toHomeomorph.toOpenPartialHomeomorph).trans c
        wM d y = |(fderiv ℝ t y).det| * wN c (t y) := by
      let t := (d.symm.trans e.toHomeomorph.toOpenPartialHomeomorph).trans c
      have hyd : y ∈ d.target := hy.1.1
      have hyc : e (d.symm y) ∈ c.source := hy.2
      have hds : ContMDiffAt I I ∞ d.symm y :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) hyd
      have hcs : ContMDiffAt I I ∞ c.symm (t y) :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
          (c.map_source hyc)
      have hcsm : ContMDiffAt I I ∞ c (e (d.symm y)) :=
        contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hyc
      have ht : ContMDiffAt I I ∞ t y := by
        change ContMDiffAt I I ∞ (fun z ↦ c (e (d.symm z))) y
        exact hcsm.comp y (e.contMDiff.contMDiffAt.comp y hds)
      have hbase : c.symm (t y) = e (d.symm y) := c.left_inv hyc
      have hevent : c.symm ∘ t =ᶠ[nhds y] e ∘ d.symm := by
        filter_upwards [t.open_source.mem_nhds hy] with z hz
        exact c.left_inv hz.2
      have hder : (mfderiv I I e (d.symm y)).comp (mfderiv I I d.symm y) =
          (mfderiv I I c.symm (t y)).comp (fderiv ℝ t y) := by
        have h := hevent.mfderiv_eq (I := I) (I' := I)
        rw [mfderiv_comp y (hcs.mdifferentiableAt (by simp))
          (ht.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
          mfderiv_comp y (e.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
            (hds.mdifferentiableAt (by simp))] at h
        exact h.symm
      let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      let B : LinearMap.BilinForm ℝ V := (gN.inner (c.symm (t y))).toBilinForm.comp
        (mfderiv I I c.symm (t y)).toLinearMap
        (mfderiv I I c.symm (t y)).toLinearMap
      let L := (fderiv ℝ t y).toLinearMap
      let C := LinearMap.toMatrix b b L
      have hgram : HM d y = C.transpose * HN c (t y) * C := by
        have hb (i : Fin n) : b i = EuclideanSpace.single i 1 :=
          EuclideanSpace.basisFun_apply _ _ _
        have hleft : LinearMap.BilinForm.toMatrix b (B.comp L L) = HM d y := by
          ext i j
          rw [LinearMap.BilinForm.toMatrix_apply]
          change gN.inner (c.symm (t y))
            ((mfderiv I I c.symm (t y)).comp (fderiv ℝ t y) (b i))
            ((mfderiv I I c.symm (t y)).comp (fderiv ℝ t y) (b j)) = _
          have hder' :
              (show V →L[ℝ] V from (mfderiv I I e (d.symm y)).comp
                (mfderiv I I d.symm y)) =
              (show V →L[ℝ] V from (mfderiv I I c.symm (t y)).comp
                (fderiv ℝ t y)) := hder
          change gN.inner (c.symm (t y))
            ((show V →L[ℝ] V from (mfderiv I I c.symm (t y)).comp
              (fderiv ℝ t y)) (b i))
            ((show V →L[ℝ] V from (mfderiv I I c.symm (t y)).comp
              (fderiv ℝ t y)) (b j)) = _
          rw [← hder']
          change gN.inner (c.symm (t y))
            (mfderiv I I e (d.symm y) (mfderiv I I d.symm y (b i)))
            (mfderiv I I e (d.symm y) (mfderiv I I d.symm y (b j))) = _
          let vi : V := mfderiv I I e (d.symm y) (mfderiv I I d.symm y (b i))
          let vj : V := mfderiv I I e (d.symm y) (mfderiv I I d.symm y (b j))
          change GN (c.symm (t y)) vi vj = _
          rw [hbase]
          change gN.inner (e (d.symm y))
            (mfderiv I I e (d.symm y) (mfderiv I I d.symm y (b i)))
            (mfderiv I I e (d.symm y) (mfderiv I I d.symm y (b j))) = _
          rw [he, hb, hb]
        have hright : LinearMap.BilinForm.toMatrix b B = HN c (t y) := by
          ext i j
          rw [LinearMap.BilinForm.toMatrix_apply]
          change gN.inner (c.symm (t y)) (mfderiv I I c.symm (t y) (b i))
            (mfderiv I I c.symm (t y) (b j)) = _
          rw [hb, hb]
        rw [← hleft, ← hright]
        exact LinearMap.BilinForm.toMatrix_comp b b B L L
      have hdet : (HM d y).det = (fderiv ℝ t y).det ^ 2 * (HN c (t y)).det := by
        rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
        have hC : C.det = (fderiv ℝ t y).det := LinearMap.det_toMatrix b L
        rw [hC]
        ring
      dsimp only [wM, wN]
      rw [hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    -- Recover the measure of a measurable subset from its original chart density.
    have hMchart (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
        (S : Set M) (hS : MeasurableSet S) (hSc : S ⊆ c.source) :
        MeasurableSet (c '' S) ∧
        gM.riemannianVolume S = ∫⁻ z in c '' S, ENNReal.ofReal (wM c z) ∂volume := by
      have himage : c '' S = c.symm ⁻¹' S ∩ c.target := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨by simpa only [mem_preimage, c.left_inv (hSc hx)] using hx, c.map_source (hSc hx)⟩
        · rintro ⟨hzS, hzc⟩
          exact ⟨c.symm z, hzS, c.right_inv hzc⟩
      have hcs : MeasurableSet (c '' S) := by
        rw [himage]
        simpa only [Set.domRestrict_eq, Set.preimage_comp,
          Set.image_preimage_eq_inter_range, Subtype.range_coe] using
          c.open_target.measurableSet.subtype_image
            (hS.preimage c.continuousOn_symm.domRestrict.measurable)
      refine ⟨hcs, ?_⟩
      have hset : c ⁻¹' (c '' S) ∩ c.source = S := by
        ext x
        constructor
        · rintro ⟨⟨z, hz, hzx⟩, hx⟩
          exact (c.injOn (hSc hz) hx hzx) ▸ hz
        · intro hx
          exact ⟨⟨x, hx, rfl⟩, hSc hx⟩
      have h := congrArg (fun ν : Measure V ↦ ν (c '' S))
        (gM.isRiemannianVolume_riemannianVolume c hc)
      rw [Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hcs,
        Measure.restrict_apply' c.open_source.measurableSet, hset,
        withDensity_apply _ hcs, Measure.restrict_restrict hcs,
        inter_eq_left.mpr (image_subset_iff.mpr (fun x hx ↦ c.map_source (hSc hx)))] at h
      exact h
    -- Recover the measure of a measurable subset from its original chart density.
    have hNchart (c : OpenPartialHomeomorph N V) (hc : c ∈ atlas V N)
        (S : Set N) (hS : MeasurableSet S) (hSc : S ⊆ c.source) :
        MeasurableSet (c '' S) ∧
        gN.riemannianVolume S = ∫⁻ z in c '' S, ENNReal.ofReal (wN c z) ∂volume := by
      have himage : c '' S = c.symm ⁻¹' S ∩ c.target := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨by simpa only [mem_preimage, c.left_inv (hSc hx)] using hx, c.map_source (hSc hx)⟩
        · rintro ⟨hzS, hzc⟩
          exact ⟨c.symm z, hzS, c.right_inv hzc⟩
      have hcs : MeasurableSet (c '' S) := by
        rw [himage]
        simpa only [Set.domRestrict_eq, Set.preimage_comp,
          Set.image_preimage_eq_inter_range, Subtype.range_coe] using
          c.open_target.measurableSet.subtype_image
            (hS.preimage c.continuousOn_symm.domRestrict.measurable)
      refine ⟨hcs, ?_⟩
      have hset : c ⁻¹' (c '' S) ∩ c.source = S := by
        ext x
        constructor
        · rintro ⟨⟨z, hz, hzx⟩, hx⟩
          exact (c.injOn (hSc hz) hx hzx) ▸ hz
        · intro hx
          exact ⟨⟨x, hx, rfl⟩, hSc hx⟩
      have h := congrArg (fun ν : Measure V ↦ ν (c '' S))
        (gN.isRiemannianVolume_riemannianVolume c hc)
      rw [Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hcs,
        Measure.restrict_apply' c.open_source.measurableSet, hset,
        withDensity_apply _ hcs, Measure.restrict_restrict hcs,
        inter_eq_left.mpr (image_subset_iff.mpr (fun x hx ↦ c.map_source (hSc hx)))] at h
      exact h
    -- On the intersection of two original chart domains, the usual Jacobian theorem applies.
    have hlocal (d : OpenPartialHomeomorph M V) (c : OpenPartialHomeomorph N V)
        (hd : d ∈ atlas V M) (hc : c ∈ atlas V N)
        (S : Set M) (hS : MeasurableSet S)
        (hSd : S ⊆ d.source) (hSc : e '' S ⊆ c.source) :
        gM.riemannianVolume S = gN.riemannianVolume (e '' S) := by
      let t := (d.symm.trans e.toHomeomorph.toOpenPartialHomeomorph).trans c
      have htS : d '' S ⊆ t.source := by
        rintro z ⟨x, hx, rfl⟩
        refine ⟨⟨d.map_source (hSd hx), mem_univ _⟩, ?_⟩
        change e (d.symm (d x)) ∈ c.source
        rw [d.left_inv (hSd hx)]
        exact hSc ⟨x, hx, rfl⟩
      have himage : t '' (d '' S) = c '' (e '' S) := by
        ext z
        constructor
        · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨e x, ⟨x, hx, rfl⟩, by
            change c (e x) = c (e (d.symm (d x)))
            rw [d.left_inv (hSd hx)]⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨d x, ⟨x, hx, rfl⟩, by
            change c (e (d.symm (d x))) = c (e x)
            rw [d.left_inv (hSd hx)]⟩
      have ht (y : V) (hy : y ∈ t.source) : ContDiffAt ℝ ∞ t y := by
        have hds : ContMDiffAt I I ∞ d.symm y :=
          contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) hy.1.1
        have hcs : ContMDiffAt I I ∞ c (e (d.symm y)) :=
          contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy.2
        apply contMDiffAt_iff_contDiffAt.mp
        change ContMDiffAt I I ∞ (fun z ↦ c (e (d.symm z))) y
        exact hcs.comp y (e.contMDiff.contMDiffAt.comp y hds)
      have hder (y : V) (hy : y ∈ d '' S) :
          HasFDerivWithinAt t (fderiv ℝ t y) (d '' S) y :=
        ((ht y (htS hy)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
      have hm := hMchart d hd S hS hSd
      have hn := hNchart c hc (e '' S)
        (e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hS) hSc
      rw [hm.2, hn.2, ← himage,
        lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hm.1 hder
          (t.injOn.mono htS)]
      apply setLIntegral_congr_fun hm.1
      intro y hy
      change ENNReal.ofReal (wM d y) =
        ENNReal.ofReal |(fderiv ℝ t y).det| * ENNReal.ofReal (wN c (t y))
      rw [hchange d c hd hc y (htS hy), ENNReal.ofReal_mul (abs_nonneg _)]
    -- A countable subcover of chart intersections determines both Borel measures.
    let U (x : N) := e.toHomeomorph '' (chartAt V (e.symm x)).source ∩ (chartAt V x).source
    have hU (x : N) : IsOpen (U x) :=
      (e.toHomeomorph.isOpenMap _ (chartAt V (e.symm x)).open_source).inter
        (chartAt V x).open_source
    obtain ⟨S, hS, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
    have hcover' : ⋃ x ∈ S, U x = univ := by
      rw [hcover]
      apply eq_univ_of_forall
      intro x
      refine mem_iUnion.mpr ⟨x, ?_⟩
      exact ⟨⟨e.symm x, mem_chart_source V (e.symm x), e.apply_symm_apply x⟩,
        mem_chart_source V x⟩
    apply Measure.ext_of_biUnion_eq_univ hS hcover'
    intro x _hx
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      Measure.map_apply e.continuous.measurable (hB.inter (hU x).measurableSet)]
    let A := e ⁻¹' (B ∩ U x)
    have hA : MeasurableSet A := (hB.inter (hU x).measurableSet).preimage e.continuous.measurable
    have hAd : A ⊆ (chartAt V (e.symm x)).source := by
      intro z hz
      obtain ⟨w, hw, heq⟩ := hz.2.1
      exact e.injective heq ▸ hw
    have hAc : e '' A ⊆ (chartAt V x).source := by
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2.2
    have hi : e '' A = B ∩ U x := Set.image_preimage_eq _ e.surjective
    exact (hlocal (chartAt V (e.symm x)) (chartAt V x)
      (chart_mem_atlas V (e.symm x)) (chart_mem_atlas V x) A hA hAd hAc).trans
        (congrArg gN.riemannianVolume hi)
  have hinner (p : ℕ) (α β : SmoothDifferentialForm (n := n) N p) (x : M) :
      differentialFormInner gM p x
        ((smoothFormPullback e e.contMDiff p α).val x)
        ((smoothFormPullback e e.contMDiff p β).val x) =
        differentialFormInner gN p (e x) (α.val (e x)) (β.val (e x)) := by
    let a : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    rw [smoothFormPullback_apply, smoothFormPullback_apply,
      differentialFormInner_eq_sum_basis gM p x a,
      differentialFormInner_eq_sum_basis gN p (e x) (a.map (F x).toLinearEquiv)]
    have hb (i : Fin n) : (a.map (F x).toLinearEquiv) i =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x (a i) := rfl
    simp only [hb, he, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rfl
  -- The same measure and fiber metric transport preserve every integral pairing.
  have hpair (q : ℕ) (α β : SmoothDifferentialForm (n := n) N q) :
      smoothFormPairing gM q (smoothFormPullback e e.contMDiff q α)
        (smoothFormPullback e e.contMDiff q β) = smoothFormPairing gN q α β := by
    unfold smoothFormPairing
    simp_rw [hinner]
    rw [← hvolume]
    exact (integral_map_equiv e.toHomeomorph.toMeasurableEquiv
      (fun y ↦ differentialFormInner gN q y (α.val y) (β.val y))).symm
  -- Both original pullbacks are inverse before passing to any operators or kernels.
  have hleft (p : ℕ) (form : SmoothDifferentialForm (n := n) M p) :
      smoothFormPullback e e.contMDiff p
        (smoothFormPullback e.symm e.symm.contMDiff p form) = form := by
    have hcomp : (e.symm : N → M) ∘ (e : M → N) = id := funext e.symm_apply_apply
    have hc : smoothFormPullback (e.symm ∘ e) (e.symm.contMDiff.comp e.contMDiff) p form =
        smoothFormPullback e e.contMDiff p
          (smoothFormPullback e.symm e.symm.contMDiff p form) := by
      apply Subtype.ext
      funext x
      rw [smoothFormPullback_apply, smoothFormPullback_apply, smoothFormPullback_apply,
        mfderiv_comp x ((e.symm.contMDiff.mdifferentiable (by simp)) (e x))
          ((e.contMDiff.mdifferentiable (by simp)) x)]
      rfl
    rw [← hc]
    have hid : smoothFormPullback id contMDiff_id p form = form := by
      apply Subtype.ext
      funext x
      rw [smoothFormPullback_apply, mfderiv_id]
      rfl
    simpa only [hcomp] using hid
  have hright (p : ℕ) (form : SmoothDifferentialForm (n := n) N p) :
      smoothFormPullback e.symm e.symm.contMDiff p
        (smoothFormPullback e e.contMDiff p form) = form := by
    have hcomp : (e : M → N) ∘ (e.symm : N → M) = id := funext e.apply_symm_apply
    have hc : smoothFormPullback (e ∘ e.symm) (e.contMDiff.comp e.symm.contMDiff) p form =
        smoothFormPullback e.symm e.symm.contMDiff p
          (smoothFormPullback e e.contMDiff p form) := by
      apply Subtype.ext
      funext y
      rw [smoothFormPullback_apply, smoothFormPullback_apply, smoothFormPullback_apply,
        mfderiv_comp y ((e.contMDiff.mdifferentiable (by simp)) (e.symm y))
          ((e.symm.contMDiff.mdifferentiable (by simp)) y)]
      rfl
    rw [← hc]
    have hid : smoothFormPullback id contMDiff_id p form = form := by
      apply Subtype.ext
      funext y
      rw [smoothFormPullback_apply, mfderiv_id]
      rfl
    simpa only [hcomp] using hid
  -- Conjugate the target adjoint and test against compact first inputs only.
  let δ : SmoothDifferentialForm (n := n) M (p + 1) →ₗ[ℂ]
      SmoothDifferentialForm (n := n) M p :=
    (smoothFormPullback e e.contMDiff p).comp ((smoothFormCodifferential gN p).comp
      (smoothFormPullback e.symm e.symm.contMDiff (p + 1)))
  have hδadj (u : SmoothDifferentialForm (n := n) M p)
      (v : SmoothDifferentialForm (n := n) M (p + 1))
      (hu : IsCompact (closure {x : M | u.val x ≠ 0})) :
      smoothFormPairing gM (p + 1) (smoothFormExteriorDerivative p u) v =
        smoothFormPairing gM p u (δ v) := by
    let u' := smoothFormPullback e.symm e.symm.contMDiff p u
    let v' := smoothFormPullback e.symm e.symm.contMDiff (p + 1) v
    have hs : {y : N | u'.val y ≠ 0} ⊆
        e.symm ⁻¹' closure {x : M | u.val x ≠ 0} := by
      intro y hy
      apply subset_closure
      intro hz
      apply hy
      change (smoothFormPullback e.symm e.symm.contMDiff p u).val y = 0
      rw [smoothFormPullback_apply, hz]
      rfl
    have hu' : IsCompact (closure {y : N | u'.val y ≠ 0}) :=
      ((e.symm.toHomeomorph.isCompact_preimage).mpr hu).of_isClosed_subset
        isClosed_closure (closure_minimal hs (isClosed_closure.preimage e.symm.continuous))
    have hd : smoothFormExteriorDerivative p u =
        smoothFormPullback e e.contMDiff (p + 1) (smoothFormExteriorDerivative p u') := by
      have h := LinearMap.congr_fun
        (smoothFormExteriorDerivative_pullback e e.contMDiff p) u'
      change smoothFormExteriorDerivative p
          (smoothFormPullback e e.contMDiff p u') = _ at h
      simpa only [u', hleft, LinearMap.comp_apply] using h
    calc
      _ = smoothFormPairing gM (p + 1)
          (smoothFormPullback e e.contMDiff (p + 1) (smoothFormExteriorDerivative p u'))
          (smoothFormPullback e e.contMDiff (p + 1) v') := by
            dsimp only [v']
            rw [hd, hleft]
      _ = smoothFormPairing gN (p + 1) (smoothFormExteriorDerivative p u') v' :=
        hpair (p + 1) _ _
      _ = smoothFormPairing gN p u' (smoothFormCodifferential gN p v') :=
        smoothFormCodifferential_formalAdjoint gN p u' v' hu'
      _ = smoothFormPairing gM p (smoothFormPullback e e.contMDiff p u')
          (smoothFormPullback e e.contMDiff p (smoothFormCodifferential gN p v')) :=
        (hpair p _ _).symm
      _ = smoothFormPairing gM p u (δ v) := by
        dsimp only [u']
        rw [hleft]
        rfl
  -- Uniqueness identifies the original source codifferential with this conjugate.
  have hδ : smoothFormCodifferential gM p = δ :=
    (existsUnique_smoothFormCodifferential gM p).unique
      (smoothFormCodifferential_formalAdjoint gM p) hδadj
  apply LinearMap.ext
  intro v
  rw [hδ]
  change smoothFormPullback e e.contMDiff p (smoothFormCodifferential gN p
      (smoothFormPullback e.symm e.symm.contMDiff (p + 1)
        (smoothFormPullback e e.contMDiff (p + 1) v))) = _
  rw [hright]
  rfl

include he in
/-- The actual metric Hodge Laplacian commutes with pullback by an isometric diffeomorphism. -/
theorem smoothFormHodgeLaplacian_pullback (p : ℕ) :
    (smoothFormHodgeLaplacian gM p).comp (smoothFormPullback e e.contMDiff p) =
      (smoothFormPullback e e.contMDiff p).comp (smoothFormHodgeLaplacian gN p) := by
  /- Stage 1: in positive degree expand the original Laplacian as d delta plus
  delta d. Commute the same pullback through d by smooth-map naturality and
  through delta by the metric-preserving diffeomorphism theorem. Reassociate
  the resulting linear-map compositions without changing any forms or metrics.
  Stage 2: in degree zero the original definition contains only delta d, and
  the same computation applies. All form degrees, including those above either
  manifold dimension, are retained. No analytic completion is introduced. -/
  cases p with
  | zero =>
    change ((smoothFormCodifferential gM 0).comp (smoothFormExteriorDerivative 0)).comp
        (smoothFormPullback e e.contMDiff 0) =
      (smoothFormPullback e e.contMDiff 0).comp
        ((smoothFormCodifferential gN 0).comp (smoothFormExteriorDerivative 0))
    rw [LinearMap.comp_assoc, smoothFormExteriorDerivative_pullback e e.contMDiff 0,
      ← LinearMap.comp_assoc, smoothFormCodifferential_pullback gM gN e he 0,
      LinearMap.comp_assoc]
  | succ p =>
    change (((smoothFormExteriorDerivative p).comp (smoothFormCodifferential gM p)) +
        (smoothFormCodifferential gM (p + 1)).comp (smoothFormExteriorDerivative (p + 1))).comp
        (smoothFormPullback e e.contMDiff (p + 1)) =
      (smoothFormPullback e e.contMDiff (p + 1)).comp
        (((smoothFormExteriorDerivative p).comp (smoothFormCodifferential gN p)) +
          (smoothFormCodifferential gN (p + 1)).comp (smoothFormExteriorDerivative (p + 1)))
    rw [LinearMap.add_comp, LinearMap.comp_add]
    congr 1
    · rw [LinearMap.comp_assoc, smoothFormCodifferential_pullback gM gN e he p,
        ← LinearMap.comp_assoc, smoothFormExteriorDerivative_pullback e e.contMDiff p,
        LinearMap.comp_assoc]
    · rw [LinearMap.comp_assoc,
        smoothFormExteriorDerivative_pullback e e.contMDiff (p + 1),
        ← LinearMap.comp_assoc, smoothFormCodifferential_pullback gM gN e he (p + 1),
        LinearMap.comp_assoc]

/-- Harmonic pullback is the actual smooth pullback restricted to the original Laplacian kernels. -/
def harmonicFormPullback (p : ℕ) : harmonicForms gN p →ₗ[ℂ] harmonicForms gM p :=
  (smoothFormPullback e e.contMDiff p).restrict (by
    intro form hform
    change smoothFormHodgeLaplacian gN p form = 0 at hform
    change smoothFormHodgeLaplacian gM p (smoothFormPullback e e.contMDiff p form) = 0
    have h := LinearMap.congr_fun (smoothFormHodgeLaplacian_pullback gM gN e he p) form
    simpa [hform] using h)

/-- An isometric diffeomorphism gives a bijection between the actual harmonic-form spaces. -/
theorem harmonicFormPullback_bijective (p : ℕ) :
    Function.Bijective (harmonicFormPullback gM gN e he p) := by
  /- Stage 1: the manifold chain rule for e inverse composed with e identifies
  the inverse derivative with the inverse tangent map. The original metric
  equation then proves that e inverse preserves the same metrics in reverse.
  Its pullback consequently preserves the corresponding harmonic kernels.
  Stage 2: the actual tangent formula for form pullback and the chain rule
  make the two restricted pullbacks inverse on every original smooth form.
  Subtype extensionality gives the inverse identities on the harmonic spaces.
  This uses no Hodge cohomology theorem and is valid on noncompact manifolds. -/
  -- Differentiate the inverse identities to recover the same metric in reverse.
  let IM := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let IN := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  have hinverse (y : N) :
      (mfderiv IM IN e (e.symm y)).comp (mfderiv IN IM e.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace IN y) := by
    rw [← mfderiv_comp y ((e.contMDiff.mdifferentiable (by simp)) (e.symm y))
      ((e.symm.contMDiff.mdifferentiable (by simp)) y)]
    have hcomp : (e : M → N) ∘ (e.symm : N → M) = id := funext e.apply_symm_apply
    rw [hcomp, mfderiv_id]
  have heinv (y : N) (v w : TangentSpace IN y) :
      gM.inner (e.symm y) (mfderiv IN IM e.symm y v) (mfderiv IN IM e.symm y w) =
        gN.inner y v w := by
    calc
      _ = gN.inner (e (e.symm y))
          (mfderiv IM IN e (e.symm y) (mfderiv IN IM e.symm y v))
          (mfderiv IM IN e (e.symm y) (mfderiv IN IM e.symm y w)) :=
        (he (e.symm y) _ _).symm
      _ = gN.inner (e (e.symm y)) v w := by
        exact congrArg₂ (fun a b : EuclideanSpace ℝ (Fin m) ↦
          gN.inner (e (e.symm y)) a b)
          (congrArg (fun f ↦ f v) (hinverse y))
          (congrArg (fun f ↦ f w) (hinverse y))
      _ = gN.inner y v w := by
        exact congrArg (fun z : N ↦
          (gN.inner z : EuclideanSpace ℝ (Fin m) →L[ℝ]
            EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) v w) (e.apply_symm_apply y)
  -- The two smooth pullbacks are inverse on their original form spaces.
  have hleft (form : SmoothDifferentialForm (n := n) M p) :
      smoothFormPullback e e.contMDiff p
        (smoothFormPullback e.symm e.symm.contMDiff p form) = form := by
    have hcomp : (e.symm : N → M) ∘ (e : M → N) = id := funext e.symm_apply_apply
    have hc : smoothFormPullback (e.symm ∘ e) (e.symm.contMDiff.comp e.contMDiff) p form =
        smoothFormPullback e e.contMDiff p
          (smoothFormPullback e.symm e.symm.contMDiff p form) := by
      apply Subtype.ext
      funext x
      rw [smoothFormPullback_apply, smoothFormPullback_apply, smoothFormPullback_apply,
        mfderiv_comp x ((e.symm.contMDiff.mdifferentiable (by simp)) (e x))
          ((e.contMDiff.mdifferentiable (by simp)) x)]
      rfl
    rw [← hc]
    have hid : smoothFormPullback id contMDiff_id p form = form := by
      apply Subtype.ext
      funext x
      rw [smoothFormPullback_apply, mfderiv_id]
      rfl
    simpa only [hcomp] using hid
  have hright (form : SmoothDifferentialForm (n := m) N p) :
      smoothFormPullback e.symm e.symm.contMDiff p
        (smoothFormPullback e e.contMDiff p form) = form := by
    have hcomp : (e : M → N) ∘ (e.symm : N → M) = id := funext e.apply_symm_apply
    have hc : smoothFormPullback (e ∘ e.symm) (e.contMDiff.comp e.symm.contMDiff) p form =
        smoothFormPullback e.symm e.symm.contMDiff p
          (smoothFormPullback e e.contMDiff p form) := by
      apply Subtype.ext
      funext y
      rw [smoothFormPullback_apply, smoothFormPullback_apply, smoothFormPullback_apply,
        mfderiv_comp y ((e.contMDiff.mdifferentiable (by simp)) (e.symm y))
          ((e.symm.contMDiff.mdifferentiable (by simp)) y)]
      rfl
    rw [← hc]
    have hid : smoothFormPullback id contMDiff_id p form = form := by
      apply Subtype.ext
      funext y
      rw [smoothFormPullback_apply, mfderiv_id]
      rfl
    simpa only [hcomp] using hid
  -- Restrict those same inverse maps to the Laplacian kernels.
  let inv := harmonicFormPullback gN gM e.symm heinv p
  have hinvl : Function.LeftInverse inv (harmonicFormPullback gM gN e he p) := by
    intro form
    apply Subtype.ext
    exact hright form.val
  have hinvr : Function.RightInverse inv (harmonicFormPullback gM gN e he p) := by
    intro form
    apply Subtype.ext
    exact hleft form.val
  exact ⟨hinvl.injective, hinvr.surjective⟩

/-- The harmonic pullback equivalence has exactly the original restricted pullback as its map. -/
def harmonicFormPullbackEquiv (p : ℕ) : harmonicForms gN p ≃ₗ[ℂ] harmonicForms gM p :=
  LinearEquiv.ofBijective (harmonicFormPullback gM gN e he p)
    (harmonicFormPullback_bijective gM gN e he p)

/-- The canonical Hodge identification intertwines harmonic and de Rham pullbacks. -/
theorem harmonicDeRhamEquiv_naturality [CompactSpace M] [CompactSpace N] (p : ℕ) :
    (deRhamPullback e e.contMDiff p).comp (harmonicDeRhamEquiv gN p).toLinearMap =
      (harmonicDeRhamEquiv gM p).toLinearMap.comp
        (harmonicFormPullback gM gN e he p) := by
  /- Stage 1: the canonical Hodge equivalence sends a harmonic form to that
  same form's closed-form quotient class. The restricted harmonic pullback
  sends it to exactly its original smooth pullback, not merely an isomorphic
  or independently chosen harmonic representative. Stage 2: apply the existing
  de Rham pullback-on-classes theorem to this closed form. Both paths therefore
  give the same original quotient class. Compactness is used only to know that
  harmonic forms are closed and that their canonical class maps are the stated
  Hodge equivalences; all diffeomorphism and metric data remain unchanged. -/
  apply LinearMap.ext
  intro form
  -- Both paths take the class of the same pulled-back smooth form.
  exact deRhamPullback_class e e.contMDiff p
    ⟨form.val, harmonicForms_le_closedForms gN p form.property⟩
    (harmonicForms_le_closedForms gM p
      (harmonicFormPullback gM gN e he p form).property)

end AtiyahSinger

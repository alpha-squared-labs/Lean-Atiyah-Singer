/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DualSobolevBridge
public import AtiyahSinger.Analysis.SobolevAdjoint

/-!
# The differential transpose on the actual dual bundles

Public module ID: M0447.

D02/D03/A02/A07: transport the already specified bilinear formal transpose through
the identity of smooth covector sections, then establish its local differential order
and principal symbol. With D_j = -i∂_j the bilinear transpose has principal symbol
(-1)^m times the fiberwise transpose. The Hermitian adjoint has no such sign.

The common dual-bundle Sobolev extension agrees with the previously constructed
continuous transpose after the canonical isometries of the induced presentations.
Sources: SG III.(3.18), (5.1), pp.194–195; contrast the conjugate transpose in
III.3.11–3.12, pp.183–184. All statements are metric-free; no ellipticity is assumed
except as the predicate compared in the ellipticity equivalence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology

variable {n r q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- The existing transpose acting on the common smooth-section API of the dual bundles. -/
def formalTransposeLinearMap :
    smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E) :=
  (dualSectionsEquiv E).toLinearMap.comp
    ((P.formalTranspose μ).comp (dualSectionsEquiv F).symm.toLinearMap)

set_option maxHeartbeats 1600000 in
-- The proof combines the conjugation bridge, local chart integrals and test separation.
/-- Integration by parts gives the actual bilinear transpose differential order at most m. -/
theorem isDifferentialOperator_formalTranspose :
    IsDifferentialOperator (DualBundle F) (DualBundle E) m
      (P.formalTransposeLinearMap μ) := by
  /- Construct the local bilinear transpose by conjugating the existing scalar-density
  Hermitian adjoint. Its kth coefficient gains (-1)^k. Chart integration and dual-frame
  evaluation compare this expression to the specified global transpose on compact tests.
  An auxiliary metric is used only to separate those tests, without changing the data. -/
  classical
  let TModel := EuclideanSpace ℝ (Fin n)
  let SourceModel := EuclideanSpace ℂ (Fin r)
  let TargetModel := EuclideanSpace ℂ (Fin q)
  -- The coordinate integration formula retains the prescribed measure, not a new density.
  have hchartIntegral (c : OpenPartialHomeomorph M TModel) (μ : Measure M)
      (w : TModel → ℝ) (hw : ContinuousOn w c.target) (hpos : ∀ z ∈ c.target, 0 ≤ w z)
      (hmap : Measure.map c (μ.restrict c.source) =
        (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
      (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
      (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
    classical
    -- Extend the target test by zero outside the prescribed chart target.
    let g : TModel → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
    have hg : Measurable g :=
      (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
        continuousOn_const c.open_target.measurableSet
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
      ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
        |>.aemeasurable c.open_target.measurableSet
    calc
      (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
      _ = ∫ x in c.source, g (c x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
        simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
      _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
          hg.aestronglyMeasurable).symm
      _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
        rw [hmap]
        exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
      _ = ∫ z in c.target, w z • f (c.symm z) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]
  -- Constant conjugations turn the coordinate Hermitian adjoint into a bilinear transpose.
  have hcoordinate {U : Set (EuclideanSpace ℝ (Fin n))}
      (hU : IsOpen U) (w : EuclideanSpace ℝ (Fin n) → ℝ)
      (hw : ContDiffOn ℝ ∞ w U) (hpos : ∀ x ∈ U, 0 < w x)
      (P : CoordinateDifferentialOperator n r q m U) :
      ∃ Q : CoordinateDifferentialOperator n q r m U,
        ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
          (a : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))),
          HasCompactSupport u → tsupport u ⊆ U →
          HasCompactSupport a → tsupport a ⊆ U →
            (∫ x, w x • ∑ i, Q.apply a x i * u x i) =
              ∫ x, w x • ∑ j, a x j * P.apply u x j := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
    let c (s : ℕ) : H s ≃L[ℝ] H s :=
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin s ↦ ℂ)).trans
        (ContinuousLinearEquiv.piCongrRight (fun _ : Fin s ↦ Complex.conjCLE))).trans
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin s ↦ ℂ)).symm
    let C (s : ℕ) : 𝓢(V, H s) →L[ℝ] 𝓢(V, H s) :=
      SchwartzMap.postcompCLM (c s).toContinuousLinearMap
    have hc (s : ℕ) (v : H s) (i : Fin s) : c s v i = (starRingEnd ℂ) (v i) := rfl
    have hsmul (s : ℕ) (z : ℂ) (v : H s) :
        c s (z • v) = (starRingEnd ℂ) z • c s v := by
      ext i
      change (starRingEnd ℂ) (z * v i) = (starRingEnd ℂ) z * (starRingEnd ℂ) (v i)
      exact map_mul _ _ _
    have hcc (s : ℕ) (v : H s) : c s (c s v) = v := by
      ext i
      simp only [hc, starRingEnd_self_apply]
    let : FiniteDimensional ℝ (H q →L[ℂ] H r) := FiniteDimensional.trans ℝ ℂ _
    let J : (H q →L[ℂ] H r) →L[ℝ] (H q →L[ℂ] H r) :=
      LinearMap.toContinuousLinearMap
        { toFun A :=
            { toFun v := c r (A (c q v))
              map_add' := by intro v z; simp only [map_add]
              map_smul' := by
                intro z v
                simp only [hsmul, map_smul, RingHom.id_apply, starRingEnd_self_apply]
              cont := (c r).continuous.comp (A.continuous.comp (c q).continuous) }
          map_add' A B := by
            apply ContinuousLinearMap.ext
            intro v
            change c r ((A + B) (c q v)) = c r (A (c q v)) + c r (B (c q v))
            simp only [add_apply, map_add]
          map_smul' a A := by
            apply ContinuousLinearMap.ext
            intro v
            change c r (a • A (c q v)) = a • c r (A (c q v))
            exact (c r).map_smul a _ }
    -- Differentiating a conjugate input changes each factor -i to +i.
    obtain ⟨R, hR⟩ := exists_formalAdjoint hU w hw hpos P
    let Q : CoordinateDifferentialOperator n q r m U :=
      { coefficient := fun k α x ↦ (-1 : ℂ) ^ k.val • J (R.coefficient k α x)
        smooth_coefficient := fun k α ↦
          (J.contDiff.comp_contDiffOn (R.smooth_coefficient k α)).const_smul _ }
    have hQ (a : 𝓢(V, H q)) (x : V) : Q.apply a x = c r (R.apply (C q a) x) := by
      simp only [CoordinateDifferentialOperator.apply, Q, map_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro α _
      have hjet : iteratedFDeriv ℝ k.val (fun y ↦ C q a y) x =
          (c q).toContinuousLinearMap.compContinuousMultilinearMap
            (iteratedFDeriv ℝ k.val a x) := by
        exact (c q).iteratedFDeriv_comp_left
      rw [hjet]
      change (-1 : ℂ) ^ k.val • c r ((R.coefficient k α x)
        (c q (((-Complex.I) ^ k.val) • _))) =
          c r ((R.coefficient k α x) (((-Complex.I) ^ k.val) • c q _))
      simp only [hsmul, map_smul, map_pow, map_neg, Complex.conj_I, neg_neg,
        smul_smul]
      congr 1
      calc
        (-1 : ℂ) ^ k.val * (-Complex.I) ^ k.val =
            ((-1 : ℂ) * (-Complex.I)) ^ k.val := (mul_pow _ _ _).symm
        _ = Complex.I ^ k.val := by congr 1; ring
    -- Conjugate the weighted integral identity; the prescribed real density is unchanged.
    refine ⟨Q, ?_⟩
    intro u a hu huU ha haU
    have hCa : tsupport (C q a) ⊆ tsupport a :=
      tsupport_comp_subset (c q).map_zero (fun y ↦ a y)
    have h := congrArg (starRingEnd ℂ)
      (hR u (C q a) hu huU (ha.of_isClosed_subset isClosed_closure hCa) (hCa.trans haU))
    rw [← integral_conj, ← integral_conj] at h
    have hleft (x : V) :
        (starRingEnd ℂ) (w x • inner ℂ (P.apply u x) (C q a x)) =
          w x • ∑ j, a x j * P.apply u x j := by
      change Complex.conjCLE (w x • inner ℂ (P.apply u x) (C q a x)) = _
      rw [map_smul]
      congr 1
      change (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (a x j) *
        (starRingEnd ℂ) (P.apply u x j)) = _
      simp only [map_sum, map_mul, starRingEnd_self_apply]
    have hright (x : V) :
        (starRingEnd ℂ) (w x • inner ℂ (u x) (R.apply (C q a) x)) =
          w x • ∑ i, Q.apply a x i * u x i := by
      rw [hQ]
      change Complex.conjCLE (w x • inner ℂ (u x) (R.apply (C q a) x)) = _
      rw [map_smul]
      congr 1
      change (starRingEnd ℂ) (∑ i, R.apply (C q a) x i * (starRingEnd ℂ) (u x i)) =
        ∑ i, c r (R.apply (C q a) x) i * u x i
      simp only [map_sum, map_mul, hc, starRingEnd_self_apply]
    simpa only [hleft, hright] using h.symm
  -- Induced dual coordinates give evaluation by the ordinary bilinear dot pairing.
  have hpairE
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
      (x : M) (hx : x ∈ e.baseSet) (α : DualBundle E x) (w : E x) :
      α w = ∑ i, (dualFrame E e ⟨x, α⟩).2 i * (e ⟨x, w⟩).2 i := by
    have hexpand : ∑ i : Fin r, (e ⟨x, w⟩).2 i •
        e.symmL ℂ x (EuclideanSpace.single i 1) = w := by
      have heq := congrArg (e.symmL ℂ x)
        ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((e ⟨x, w⟩).2))
      calc
        _ = e.symmL ℂ x ((e ⟨x, w⟩).2) := by
          simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
        _ = w := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact e.symmL_continuousLinearMapAt hx w
    have hd := dualFrame_apply_snd E e
      (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
    simp only [dite_true] at hd
    rw [hd]
    conv_lhs => rw [← hexpand, map_sum]
    simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
    exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
  have hpairF
      (e : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas e]
      (x : M) (hx : x ∈ e.baseSet) (α : DualBundle F x) (w : F x) :
      α w = ∑ i, (dualFrame F e ⟨x, α⟩).2 i * (e ⟨x, w⟩).2 i := by
    have hexpand : ∑ i : Fin q, (e ⟨x, w⟩).2 i •
        e.symmL ℂ x (EuclideanSpace.single i 1) = w := by
      have heq := congrArg (e.symmL ℂ x)
        ((EuclideanSpace.basisFun (Fin q) ℂ).sum_repr ((e ⟨x, w⟩).2))
      calc
        _ = e.symmL ℂ x ((e ⟨x, w⟩).2) := by
          simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
        _ = w := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact e.symmL_continuousLinearMapAt hx w
    have hd := dualFrame_apply_snd F e
      (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
    simp only [dite_true] at hd
    rw [hd]
    conv_lhs => rw [← hexpand, map_sum]
    simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
    exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
  -- Localize and extend actual sections; the cutoff is one on the smaller chart domain.
  have hlocalAction
      (c : OpenPartialHomeomorph M TModel)
      (hc : c ∈ atlas TModel M)
      (e : Trivialization SourceModel
        (π SourceModel E)) [MemTrivializationAtlas e]
      (f : Trivialization TargetModel
        (π TargetModel F)) [MemTrivializationAtlas f]
      (U : Set M) (hU : IsOpen U)
      (D : CoordinateDifferentialOperator n r q m (c '' U))
      (hD : HasCoordinateExpression E F m P.toLinearMap c e f U D)
      (x : M) (hx : x ∈ U) :
      ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ R : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
            smoothSections (n := n) (r := r) (DualBundle E),
          (∃ D' : CoordinateDifferentialOperator n q r m (c '' V),
            HasCoordinateExpression (DualBundle F) (DualBundle E) m R c
              (dualFrame F f) (dualFrame E e) V D') ∧
          ∀ (K : Set M), IsCompact K → K ⊆ V →
            ∀ u : supportedSmoothSections (n := n) (r := r) E K,
            ∀ v : smoothSections (n := n) (r := q) (DualBundle F),
              (∫ y, v.val y ((P.toLinearMap u.val).val y) ∂μ) =
                ∫ y, (R v).val y (u.val.val y) ∂μ := by
    classical
    let T := EuclideanSpace ℝ (Fin n)
    let W := EuclideanSpace ℂ (Fin r)
    let Z := EuclideanSpace ℂ (Fin q)
    have hUsource : U ⊆ c.source := fun y hy ↦ (hD.1 hy).1.1
    have hDU : IsOpen (c '' U) := c.isOpen_image_of_subset_source hU hUsource
    have hUc : c '' U ⊆ c.target := fun _ ⟨y, hy, hzy⟩ ↦ hzy ▸ c.map_source (hUsource hy)
    have hUe : c '' U ⊆ c.target ∩ c.symm ⁻¹' e.baseSet := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨c.map_source (hUsource hy), by simpa [c.left_inv (hUsource hy)] using (hD.1 hy).1.2⟩
    have hUf : c '' U ⊆ c.target ∩ c.symm ⁻¹' f.baseSet := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨c.map_source (hUsource hy), by simpa [c.left_inv (hUsource hy)] using (hD.1 hy).2⟩
    obtain ⟨w, hw, hwpos, hwmap⟩ :=
      (inferInstance : IsSmoothPositiveMeasure (n := n) μ).exists_smooth_density c hc
    obtain ⟨Q, hQ⟩ := hcoordinate hDU w (hw.mono hUc)
      (fun z hz ↦ hwpos z (hUc hz)) D
    -- Choose a common cutoff which is one on an open neighborhood of the original point.
    obtain ⟨b, _, hb⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, T)) (c x)).mem_iff.mp
        (hDU.mem_nhds (Set.mem_image_of_mem c hx))
    let A : BundleChartCutoff (r := r) E c :=
      ⟨e, inferInstance, b, b.contMDiff.contDiff, b.hasCompactSupport, hb.trans hUe⟩
    let B : BundleChartCutoff (r := q) (DualBundle F) c :=
      ⟨dualFrame F f, inferInstance, b, b.contMDiff.contDiff, b.hasCompactSupport, by
        simpa only [dualFrame_baseSet] using hb.trans hUf⟩
    let Ad : BundleChartCutoff (r := r) (DualBundle E) c :=
      ⟨dualFrame E e, inferInstance, b, b.contMDiff.contDiff, b.hasCompactSupport, by
        simpa only [dualFrame_baseSet] using hb.trans hUe⟩
    let V := U ∩ c ⁻¹' interior {z : T | b z = 1}
    have hV : IsOpen V := by
      exact (c.continuousOn.mono hUsource).isOpen_inter_preimage hU isOpen_interior
    have hxV : x ∈ V := by
      refine ⟨hx, mem_interior_iff_mem_nhds.mpr ?_⟩
      exact b.eventuallyEq_one
    have hBV (v : smoothSections (n := n) (r := q) (DualBundle F)) :
        ContDiff ℝ ∞ (Q.apply (B.localize hc v)) ∧
          HasCompactSupport (Q.apply (B.localize hc v)) ∧
            tsupport (Q.apply (B.localize hc v)) ⊆ tsupport (B.localize hc v) :=
      Q.apply_testFunction_properties hDU _ ((B.localize hc v).smooth ⊤)
        (B.hasCompactSupport_localizedFunction v)
        ((B.tsupport_localizedFunction_subset v).trans hb)
    let qv (v : smoothSections (n := n) (r := q) (DualBundle F)) : 𝓢(T, W) :=
      (hBV v).2.1.toSchwartzMap (hBV v).1
    have hqadd (u v : smoothSections (n := n) (r := q) (DualBundle F)) :
        qv (u + v) = qv u + qv v := by
      apply DFunLike.ext
      intro z
      change Q.apply (B.localize hc (u + v)) z =
        Q.apply (B.localize hc u) z + Q.apply (B.localize hc v) z
      rw [B.localize_add]
      change Q.apply ((fun z ↦ B.localize hc u z) + (fun z ↦ B.localize hc v z)) z = _
      simp only [CoordinateDifferentialOperator.apply,
        iteratedFDeriv_add_apply ((B.localize hc u).smooth _).contDiffAt
          ((B.localize hc v).smooth _).contDiffAt,
        add_apply, smul_add, map_add, Finset.sum_add_distrib]
    have hqsmul (a : ℂ) (v : smoothSections (n := n) (r := q) (DualBundle F)) :
        qv (a • v) = a • qv v := by
      apply DFunLike.ext
      intro z
      change Q.apply (B.localize hc (a • v)) z = a • Q.apply (B.localize hc v) z
      rw [B.localize_smul]
      change Q.apply (a • (fun z ↦ B.localize hc v z)) z = _
      simp only [CoordinateDifferentialOperator.apply,
        iteratedFDeriv_const_smul_apply ((B.localize hc v).smooth _).contDiffAt,
        smul_apply, smul_comm _ a, map_smul, Finset.smul_sum]
    let qmap : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ] 𝓢(T, W) :=
      { toFun := qv
        map_add' := hqadd
        map_smul' := fun a v ↦ hqsmul a v }
    let R : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
        smoothSections (n := n) (r := r) (DualBundle E) := (Ad.extendLinearMap hc).comp qmap
    refine ⟨V, hV, hxV, Set.inter_subset_left, R, ?_, ?_⟩
    · let Q' : CoordinateDifferentialOperator n q r m (c '' V) :=
        { coefficient := Q.coefficient
          smooth_coefficient := fun j α ↦ (Q.smooth_coefficient j α).mono
            (Set.image_mono Set.inter_subset_left) }
      refine ⟨Q', (fun y hy ↦ ⟨⟨(hD.1 hy.1).1.1,
        by simpa only [dualFrame_baseSet] using (hD.1 hy.1).2⟩,
        by simpa only [dualFrame_baseSet] using (hD.1 hy.1).1.2⟩), ?_⟩
      intro v y hy
      have hyc := hUsource hy.1
      have hye := (hD.1 hy.1).1.2
      have hby : b (c y) = 1 := interior_subset (s := {z : T | b z = 1}) hy.2
      have hgerm : (fun z ↦ B.localize hc v z) =ᶠ[𝓝 (c y)]
          sectionInChart (DualBundle F) c (dualFrame F f) v.val := by
        filter_upwards [isOpen_interior.mem_nhds hy.2,
          c.open_target.mem_nhds (c.map_source hyc)] with z hz hzt
        have hbz : b z = 1 := interior_subset (s := {z : T | b z = 1}) hz
        change (if z ∈ c.target then
          (b z : ℂ) • sectionInChart (DualBundle F) c (dualFrame F f) v.val z else 0) = _
        rw [ite_eq_left hzt, hbz, Complex.ofReal_one, one_smul]
      change ((dualFrame E e) ⟨y, Ad.extendedFunction (qv v) y⟩).2 = Q'.apply _ (c y)
      simp only [BundleChartCutoff.extendedFunction, Ad, ite_eq_left hyc, hby,
        Complex.ofReal_one, one_smul]
      have hyd : y ∈ (dualFrame E e).baseSet := by simpa only [dualFrame_baseSet] using hye
      rw [← (dualFrame E e).continuousLinearMapAt_apply_of_mem ℂ hyd,
        (dualFrame E e).continuousLinearMapAt_symmL hyd]
      change Q.apply (B.localize hc v) (c y) = Q.apply _ (c y)
      simp only [CoordinateDifferentialOperator.apply]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro α _
      rw [(hgerm.iteratedFDeriv ℝ j.val).eq_of_nhds]
    · intro K hK hKV u v
      let a := A.localize hc u.val
      let z := B.localize hc v
      have hKU : K ⊆ U := hKV.trans Set.inter_subset_left
      have hKsource : K ⊆ c.source := hKU.trans hUsource
      have hKc : IsCompact (c '' K) := hK.image_of_continuousOn (c.continuousOn.mono hKsource)
      have hPu (y : M) (hy : y ∉ K) : (P.toLinearMap u.val).val y = 0 := by
        have hgerm : ∀ᶠ t in 𝓝 y, u.val.val t = (0 : E t) := by
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with t ht
          exact u.property t ht
        simpa using P.apply_eq_of_eventually_eq u.val 0 y hgerm
      have hasupp : tsupport a ⊆ c '' K := by
        apply closure_minimal ?_ hKc.isClosed
        intro t ht
        have htb : t ∈ tsupport b := A.tsupport_localizedFunction_subset u.val
          (subset_tsupport _ ht)
        have htt := (hUe (hb htb)).1
        have hte := (hUe (hb htb)).2
        refine ⟨c.symm t, ?_, c.right_inv htt⟩
        by_contra htk
        apply ht
        change (if t ∈ c.target then (b t : ℂ) •
          (e ⟨c.symm t, u.val.val (c.symm t)⟩).2 else 0) = 0
        rw [ite_eq_left htt, u.property _ htk, ← e.continuousLinearMapAt_apply_of_mem ℂ hte,
          map_zero, smul_zero]
      have ha (t : T) (ht : t ∈ c '' U) : a t = sectionInChart E c e u.val.val t := by
        obtain ⟨y, hy, rfl⟩ := ht
        have hyc := hUsource hy
        have hye := (hD.1 hy).1.2
        change (if c y ∈ c.target then (b (c y) : ℂ) •
          sectionInChart E c e u.val.val (c y) else 0) = _
        rw [ite_eq_left (c.map_source hyc)]
        by_cases hyK : y ∈ K
        · have hby : b (c y) = 1 := interior_subset (s := {z : T | b z = 1}) (hKV hyK).2
          rw [hby, Complex.ofReal_one, one_smul]
        · have hzero : sectionInChart E c e u.val.val (c y) = 0 := by
            unfold sectionInChart
            rw [c.left_inv hyc, u.property y hyK,
              ← e.continuousLinearMapAt_apply_of_mem ℂ hye, map_zero]
          rw [hzero, smul_zero]
      have hDP (y : M) (hy : y ∈ U) :
          (f ⟨y, (P.toLinearMap u.val).val y⟩).2 = D.apply a (c y) := by
        rw [hD.2 u.val y hy]
        have hgerm : (fun t ↦ a t) =ᶠ[𝓝 (c y)] sectionInChart E c e u.val.val := by
          filter_upwards [hDU.mem_nhds (Set.mem_image_of_mem c hy)] with t ht
          exact ha t ht
        simp only [CoordinateDifferentialOperator.apply]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro α _
        rw [(hgerm.iteratedFDeriv ℝ j.val).eq_of_nhds]
      have hDa := D.apply_testFunction_properties hDU a (a.smooth ⊤)
        (A.hasCompactSupport_localizedFunction u.val)
        (hasupp.trans (Set.image_mono hKU))
      have hDaK : tsupport (D.apply a) ⊆ c '' K := hDa.2.2.trans hasupp
      have hleft (t : T) (ht : t ∈ c.target) :
          v.val (c.symm t) ((P.toLinearMap u.val).val (c.symm t)) =
            ∑ i, z t i * D.apply a t i := by
        by_cases hyK : c.symm t ∈ K
        · have hyU := hKU hyK
          have htf := (hD.1 hyU).2
          have hbt : b t = 1 := by simpa [c.right_inv ht] using
            (show b (c (c.symm t)) = 1 from
              interior_subset (s := {z : T | b z = 1}) (hKV hyK).2)
          have hz : z t = ((dualFrame F f) ⟨c.symm t, v.val (c.symm t)⟩).2 := by
            change (if t ∈ c.target then (b t : ℂ) •
              ((dualFrame F f) ⟨c.symm t, v.val (c.symm t)⟩).2 else 0) = _
            rw [ite_eq_left ht, hbt, Complex.ofReal_one, one_smul]
          rw [hpairF f _ htf, hz, hDP _ hyU, c.right_inv ht]
        · have hnot : t ∉ c '' K := by
            rintro ⟨y, hy, hyt⟩
            apply hyK
            rw [← hyt, c.left_inv (hKsource hy)]
            exact hy
          have hzero := image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (hDaK h))
          simp [hPu _ hyK, hzero]
      have hright (t : T) (ht : t ∈ c.target) :
          (R v).val (c.symm t) (u.val.val (c.symm t)) =
            ∑ i, Q.apply z t i * a t i := by
        by_cases hyK : c.symm t ∈ K
        · have hyU := hKU hyK
          have hte := (hD.1 hyU).1.2
          have htu : t ∈ c '' U := ⟨c.symm t, hyU, c.right_inv ht⟩
          have hbt : b t = 1 := by simpa [c.right_inv ht] using
            (show b (c (c.symm t)) = 1 from
              interior_subset (s := {z : T | b z = 1}) (hKV hyK).2)
          have hRval : (R v).val (c.symm t) =
              (dualFrame E e).symmL ℂ (c.symm t) (Q.apply z t) := by
            change Ad.extendedFunction (qv v) (c.symm t) = _
            simp only [BundleChartCutoff.extendedFunction, Ad,
              ite_eq_left (c.map_target ht), c.right_inv ht, hbt,
              Complex.ofReal_one, one_smul]
            rfl
          rw [hpairE e _ hte, hRval]
          have htd : c.symm t ∈ (dualFrame E e).baseSet := by
            simpa only [dualFrame_baseSet] using hte
          rw [← (dualFrame E e).continuousLinearMapAt_apply_of_mem ℂ htd,
            (dualFrame E e).continuousLinearMapAt_symmL htd, ha t htu]
          rfl
        · have hnot : t ∉ c '' K := by
            rintro ⟨y, hy, hyt⟩
            apply hyK
            rw [← hyt, c.left_inv (hKsource hy)]
            exact hy
          have hzero := image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (hasupp h))
          simp [u.property _ hyK, hzero]
      have htransportLeft : (∫ y, v.val y ((P.toLinearMap u.val).val y) ∂μ) =
          ∫ t, w t • ∑ i, z t i * D.apply a t i := by
        rw [hchartIntegral c μ w hw.continuousOn (fun t ht ↦ (hwpos t ht).le) hwmap
          _ (contMDiff_dualSection_eval F
            ⟨v.val, (isSmoothSection_dualBundle_iff F _).1 v.property⟩
            (P.toLinearMap u.val)).continuous (by
            intro y hy
            by_contra hyc
            have hyK : y ∉ K := fun h ↦ hyc (hKsource h)
            apply hy
            change v.val y ((P.toLinearMap u.val).val y) = 0
            rw [hPu y hyK, map_zero])]
        calc
          _ = ∫ t in c.target, w t • ∑ i, z t i * D.apply a t i := by
            apply setIntegral_congr_fun c.open_target.measurableSet
            intro t ht
            exact congrArg (fun a : ℂ ↦ w t • a) (hleft t ht)
          _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
            intro t ht
            have hzero := image_eq_zero_of_notMem_tsupport
              (fun h ↦ ht (hUc ((Set.image_mono hKU) (hDaK h))))
            simp [hzero])
      have htransportRight : (∫ y, (R v).val y (u.val.val y) ∂μ) =
          ∫ t, w t • ∑ i, Q.apply z t i * a t i := by
        rw [hchartIntegral c μ w hw.continuousOn (fun t ht ↦ (hwpos t ht).le) hwmap
          _ (contMDiff_dualSection_eval E
            ⟨(R v).val, (isSmoothSection_dualBundle_iff E _).1 (R v).property⟩ u.val).continuous (by
            intro y hy
            by_contra hyc
            have hyK : y ∉ K := fun h ↦ hyc (hKsource h)
            apply hy
            change (R v).val y (u.val.val y) = 0
            rw [u.property y hyK, map_zero])]
        calc
          _ = ∫ t in c.target, w t • ∑ i, Q.apply z t i * a t i := by
            apply setIntegral_congr_fun c.open_target.measurableSet
            intro t ht
            exact congrArg (fun a : ℂ ↦ w t • a) (hright t ht)
          _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
            intro t ht
            have hzero := image_eq_zero_of_notMem_tsupport
              (fun h ↦ ht (hUc ((Set.image_mono hKU) (hasupp h))))
            simp [hzero])
      rw [htransportLeft, htransportRight]
      exact (hQ a z (A.hasCompactSupport_localizedFunction u.val)
        (hasupp.trans (Set.image_mono hKU)) (B.hasCompactSupport_localizedFunction v)
        ((B.tsupport_localizedFunction_subset v).trans hb)).symm
  -- The already specified transpose has exactly the same local test identity.
  let T := P.formalTransposeLinearMap μ
  have hT (v : smoothSections (n := n) (r := q) (DualBundle F))
      (u : smoothSections (n := n) (r := r) E) :
      (∫ y, (T v).val y (u.val y) ∂μ) =
        ∫ y, v.val y ((P.toLinearMap u).val y) ∂μ := by
    exact P.smoothDualSectionPairing_formalTranspose μ ((dualSectionsEquiv F).symm v) u
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) E
  -- Every atlas frame on the dual bundle is induced by an original primal frame.
  rintro c hc _ ⟨f, hf, rfl⟩ _ ⟨e, he, rfl⟩ x hx
  let := hf
  let := he
  simp only [dualFrame_baseSet] at hx
  obtain ⟨U, hU, hxU, D, hD⟩ :=
    P.isDifferentialOperator c hc e f x ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
  obtain ⟨V, hV, hxV, _, R, ⟨Q, hcoord⟩, hpair⟩ :=
    hlocalAction c hc e f U hU D hD x hxU
  refine ⟨V, hV, hxV, Q, hcoord.1, ?_⟩
  intro v y hy
  -- A real bump squared localizes the positive metric test for the covector difference.
  obtain ⟨b, _, hb⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, TModel)) y).mem_iff.mp
      (hV.mem_nhds hy)
  let β := (dualSectionsEquiv E).symm (T v) - (dualSectionsEquiv E).symm (R v)
  let w := h.dualSectionsEquiv.symm β
  have hwβ : h.dualSectionsEquiv w = β := h.dualSectionsEquiv.apply_symm_apply β
  let t := smoothSectionMul E (fun z ↦ (b z : ℂ))
    (Complex.ofRealCLM.contMDiff.comp b.contMDiff) w
  let u : supportedSmoothSections (n := n) (r := r) E (tsupport b) :=
    ⟨smoothSectionMul E (fun z ↦ (b z : ℂ))
      (Complex.ofRealCLM.contMDiff.comp b.contMDiff) t, fun z hz ↦ by
      change (b z : ℂ) • t.val z = 0
      rw [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, zero_smul]⟩
  have hzero : smoothDualSectionPairing E μ β u.val = 0 := by
    change (∫ z, (T v).val z (u.val.val z) - (R v).val z (u.val.val z) ∂μ) = 0
    have hi : Integrable (fun z ↦ (T v).val z (u.val.val z)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T v)) u.val
    have hi' : Integrable (fun z ↦ (R v).val z (u.val.val z)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (R v)) u.val
    rw [integral_sub hi hi', hT, hpair _ b.hasCompactSupport hb u v, sub_self]
  have htzero : h.sectionPairing μ t t = 0 := by
    rw [← hzero, ← hwβ, h.dualSectionPairing_dualSectionsEquiv]
    apply integral_congr_ae
    filter_upwards with z
    change (h.toCore z).inner ((b z : ℂ) • w.val z) ((b z : ℂ) • w.val z) =
      (h.toCore z).inner (w.val z) ((b z : ℂ) • ((b z : ℂ) • w.val z))
    let : InnerProductSpace.Core ℂ (E z) := h.toCore z
    rw [InnerProductSpace.Core.inner_smul_left,
      InnerProductSpace.Core.inner_smul_right, InnerProductSpace.Core.inner_smul_right,
      InnerProductSpace.Core.inner_smul_right, Complex.conj_ofReal]
  have ht : t = 0 := (h.sectionPairing_self_eq_zero_iff μ t).mp htzero
  have hwy := congrArg (fun s : smoothSections (n := n) (r := r) E ↦ s.val y) ht
  change (b y : ℂ) • w.val y = 0 at hwy
  rw [b.eq_one, Complex.ofReal_one, one_smul] at hwy
  have hβy : β.val y = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    have hp := h.dualSectionsEquiv_apply w y a
    rw [hwβ, hwy] at hp
    change β.val y a = 0
    rw [hp]
    let : InnerProductSpace.Core ℂ (E y) := h.toCore y
    exact InnerProductSpace.Core.inner_zero_left _
  have heq : (T v).val y = (R v).val y := sub_eq_zero.mp hβy
  change ((dualFrame E e) ⟨y, (T v).val y⟩).2 = _
  rw [heq]
  exact hcoord.2 v y hy

/-- The bilinear transpose as a differential operator on the actual dual bundles. -/
def formalTransposeOperator :
    DifferentialOperator (n := n) (r := q) (q := r) (DualBundle F) (DualBundle E) m where
  toLinearMap := P.formalTransposeLinearMap μ
  isDifferentialOperator := P.isDifferentialOperator_formalTranspose μ

/-- The packaged operator acts on the original covector sections by their original transpose. -/
theorem formalTransposeOperator_apply
    (α : smoothDualSections (n := n) (r := q) F) :
    (P.formalTransposeOperator μ).toLinearMap (dualSectionsEquiv F α) =
      dualSectionsEquiv E (P.formalTranspose μ α) := by
  /- Expand the transported map and cancel the inverse pair of section equivalences.
  Both equivalences preserve each actual covector value, so no fiber map is changed. -/
  change (dualSectionsEquiv E)
    (P.formalTranspose μ ((dualSectionsEquiv F).symm ((dualSectionsEquiv F) α))) = _
  rw [(dualSectionsEquiv F).symm_apply_apply]

set_option maxHeartbeats 1000000 in
-- Scalar-jet realization and semilinear duality are compared in the same proof.
/-- At a real covector the bilinear transpose symbol includes the differential parity sign. -/
theorem principalSymbol_formalTranspose_apply
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (α : DualBundle F x) (v : E x) :
    ((P.formalTransposeOperator μ).principalSymbol x ξ α) v =
      (-1 : ℂ) ^ m * α (P.principalSymbol x ξ v) := by
  /- Use arbitrary auxiliary metrics to express the already specified transpose through
  the metric adjoint. A real scalar vanishing at x has the same power on both dual sides.
  Its m-jet detects the principal symbols; the conjugate-linear metric identifications
  conjugate (-i)^m m!, producing exactly (-1)^m. The auxiliary metrics then cancel by
  the metric principal-symbol pairing identity. This includes symbols that vanish. -/
  classical
  have exists_scalar_jet (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      ∃ φ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ ∧
        φ x = 0 ∧ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x = ξ := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let b : SmoothBumpFunction I x := Classical.choice inferInstance
    let ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      ξ.comp (mfderiv I I c.symm (c x))
    let φ : M → ℝ := fun y ↦ b y * ℓ (c y - c x)
    have hc := contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (chart_mem_atlas _ x))
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ :=
      b.contMDiff_smul (ℓ.contMDiff.comp_contMDiffOn (hc.sub contMDiffOn_const))
    have heq : φ =ᶠ[𝓝 x] (fun y ↦ ℓ (c y - c x)) := by
      filter_upwards [b.eventuallyEq_one] with y hy
      simp [φ, hy]
    refine ⟨φ, hs, ?_, ?_⟩
    · simp [φ]
    · rw [heq.mfderiv_eq]
      have hchart := mdifferentiable_of_mem_atlas (I := I) (chart_mem_atlas _ x)
      have hcx := hchart.mdifferentiableAt (mem_chart_source _ x)
      change mfderiv I 𝓘(ℝ, ℝ) (ℓ ∘ (fun y ↦ c y - c x)) x = ξ
      erw [mfderiv_comp x (ℓ.contMDiff (n := ∞) |>.contMDiffAt.mdifferentiableAt (by simp))
        (hcx.sub (mdifferentiableAt_const (c := c x))), mfderiv_eq_fderiv, ℓ.fderiv,
        mfderiv_sub hcx (mdifferentiableAt_const (c := c x)), mfderiv_const, sub_zero]
      dsimp only [ℓ]
      change (ξ.comp (mfderiv I I c.symm (c x))).comp (mfderiv I I c x) = ξ
      erw [ContinuousLinearMap.comp_assoc, hchart.symm_comp_deriv (mem_chart_source _ x)]
      exact ContinuousLinearMap.comp_id ξ
  have exists_section_value (x : M) (v : F x) :
      ∃ s : AtiyahSinger.smoothSections (n := n) (r := q) F, s.val x = v := by
    classical
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let e := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds hx)
    let a : EuclideanSpace ℂ (Fin q) := (e.linearEquivAt ℂ x hx) v
    let s : ∀ y, F y := fun y ↦ (b y : ℂ) • e.symmL ℂ y a
    have hs : AtiyahSinger.IsSmoothSection (n := n) (r := q) F s := by
      intro f hf y hy
      let := hf
      by_cases hyb : y ∈ tsupport b
      · have hye : y ∈ e.baseSet := hb hyb
        have htransition :=
          (AtiyahSinger.IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f).contMDiffAt
            ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hye, hy⟩)
        have happly : ContDiff ℝ ∞
            (fun L : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q) ↦ L a) :=
          (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
        have hcoord := happly.comp_contMDiffAt htransition
        have hscalar := Complex.ofRealCLM.contMDiff.comp b.contMDiff
        have hmul : ContDiff ℝ ∞
            (fun p : ℂ × EuclideanSpace ℂ (Fin q) ↦ p.1 • p.2) := contDiff_smul
        have hlocal := hmul.comp_contMDiffAt (hscalar.contMDiffAt.prodMk_space hcoord)
        apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [e.open_baseSet.mem_nhds hye, f.open_baseSet.mem_nhds hy]
          with z hze hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) =
          (b z : ℂ) • e.coordChangeL ℂ f z a
        rw [map_smul, e.coordChangeL_apply f ⟨hze, hzf⟩, e.symmL_apply hze]
        rfl
      · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin q)))
          |>.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [((isClosed_tsupport b).isOpen_compl.mem_nhds hyb),
          f.open_baseSet.mem_nhds hy] with z hzb hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) = 0
        rw [image_eq_zero_of_notMem_tsupport hzb, Complex.ofReal_zero, zero_smul, map_zero]
    refine ⟨⟨s, hs⟩, ?_⟩
    dsimp only [s]
    rw [b.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hx]
    exact e.symm_apply_apply_mk hx v
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) E
  obtain ⟨k⟩ := nonempty_smoothHermitianMetric (n := n) (r := q) F
  let Q := P.metricFormalAdjoint (μ := μ) h k
  -- The chosen bilinear transpose is the metric adjoint transported by the two dualities.
  let S : smoothDualSections (n := n) (r := q) F →ₗ[ℂ]
      smoothDualSections (n := n) (r := r) E :=
    h.dualSectionsEquiv.toLinearMap.comp
      (Q.toLinearMap.comp k.dualSectionsEquiv.symm.toLinearMap)
  have hS : ∀ β u, smoothDualSectionPairing E μ (S β) u =
      smoothDualSectionPairing F μ β (P.toLinearMap u) := by
    intro β u
    change smoothDualSectionPairing E μ
      (h.dualSectionsEquiv (Q.toLinearMap (k.dualSectionsEquiv.symm β))) u = _
    rw [h.dualSectionPairing_dualSectionsEquiv]
    rw [(P.isMetricFormalAdjoint_metricFormalAdjoint h k).symm]
    rw [← k.dualSectionPairing_dualSectionsEquiv, k.dualSectionsEquiv.apply_symm_apply]
  have hST : S = P.formalTranspose μ :=
    (P.existsUnique_formalTranspose μ).unique hS
      (P.smoothDualSectionPairing_formalTranspose μ)
  have htranspose (s : smoothSections (n := n) (r := q) F) :
      (P.formalTransposeOperator μ).toLinearMap
        ((dualSectionsEquiv F) (k.dualSectionsEquiv s)) =
      (dualSectionsEquiv E) (h.dualSectionsEquiv (Q.toLinearMap s)) := by
    rw [P.formalTransposeOperator_apply, ← hST]
    change (dualSectionsEquiv E) (h.dualSectionsEquiv
      (Q.toLinearMap (k.dualSectionsEquiv.symm (k.dualSectionsEquiv s)))) = _
    rw [k.dualSectionsEquiv.symm_apply_apply]
  -- Real scalar powers commute with both conjugate-linear metric identifications.
  obtain ⟨φ, hφ, hφx, hφd⟩ := exists_scalar_jet x ξ
  obtain ⟨s, hs⟩ := exists_section_value x ((k.dualEquiv x).symm α)
  let a : M → ℂ := fun y ↦ ((φ y) ^ m : ℝ)
  have hpow : ContDiff ℝ ∞ (fun z : ℝ ↦ z ^ m) := contDiff_id.pow m
  have ha : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ a :=
    Complex.ofRealCLM.contMDiff.comp (hpow.contMDiff.comp hφ)
  let t := smoothSectionMul F a ha s
  let β := (dualSectionsEquiv F) (k.dualSectionsEquiv s)
  let γ := (dualSectionsEquiv F) (k.dualSectionsEquiv t)
  have hγ (y : M) : γ.val y = ((φ y) ^ m : ℂ) • β.val y := by
    change k.dual y ((a y) • s.val y) = ((φ y) ^ m : ℂ) • k.dual y (s.val y)
    rw [k.dual_smul]
    simp [a]
  have hβ : β.val x = α := by
    change (k.dualEquiv x) (s.val x) = α
    rw [hs, (k.dualEquiv x).apply_symm_apply]
  have hjT := (P.formalTransposeOperator μ).apply_scalar_pow φ hφ x hφx β γ hγ
  have hjQ := Q.apply_scalar_pow φ hφ x hφx s t (fun y ↦ by
    change a y • s.val y = _
    simp only [a, Complex.ofReal_pow])
  rw [hφd, hβ] at hjT
  rw [hφd] at hjQ
  let c : ℂ := (-Complex.I) ^ m * (m.factorial : ℂ)
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
  have hconj : (starRingEnd ℂ) c = (-1 : ℂ) ^ m * c := by
    simp only [c, map_mul, map_pow, map_neg, Complex.conj_I, neg_neg, map_natCast]
    rw [← mul_assoc, ← mul_pow]
    congr 2
    ring
  -- Evaluate the two jets on the original fiber vector and use the metric symbol identity.
  have hjet : c * ((P.formalTransposeOperator μ).principalSymbol x ξ α) v =
      (starRingEnd ℂ) c * α (P.principalSymbol x ξ v) := by
    have he := congrArg (fun δ : DualBundle E x ↦ δ v) hjT
    have htrans := congrArg (fun z : smoothSections (n := n) (r := r) (DualBundle E) ↦
      z.val x v) (htranspose t)
    have hpair : h.pairing x (Q.principalSymbol x ξ (s.val x)) v =
        α (P.principalSymbol x ξ v) := by
      have hp := P.principalSymbol_metricFormalAdjoint_pairing (μ := μ) h k x ξ v (s.val x)
      have hp' := congrArg (starRingEnd ℂ) hp
      change (starRingEnd ℂ) ((k.toCore x).inner (P.principalSymbol x ξ v) (s.val x)) =
        (starRingEnd ℂ) ((h.toCore x).inner v (Q.principalSymbol x ξ (s.val x))) at hp'
      rw [(k.toCore x).conj_inner_symm, (h.toCore x).conj_inner_symm] at hp'
      have hv := k.dualEquiv_apply x (s.val x) (P.principalSymbol x ξ v)
      rw [hs, (k.dualEquiv x).apply_symm_apply] at hv
      rw [hs] at hp'
      simpa only [hs, SmoothHermitianMetric.pairing] using hp'.symm.trans hv.symm
    change ((P.formalTransposeOperator μ).toLinearMap γ).val x v =
      c * ((P.formalTransposeOperator μ).principalSymbol x ξ α) v at he
    rw [← he]
    change ((P.formalTransposeOperator μ).toLinearMap γ).val x v = _
    rw [htrans]
    have hval : ((dualSectionsEquiv E) (h.dualSectionsEquiv (Q.toLinearMap t))).val x v =
        h.pairing x ((Q.toLinearMap t).val x) v :=
      h.dualSectionsEquiv_apply (Q.toLinearMap t) x v
    rw [hval, hjQ]
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    change (h.toCore x).inner (c • Q.principalSymbol x ξ (s.val x)) v = _
    rw [InnerProductSpace.Core.inner_smul_left]
    simpa only [SmoothHermitianMetric.pairing] using
      congrArg (fun z : ℂ ↦ (starRingEnd ℂ) c * z) hpair
  apply (mul_left_cancel₀ hc)
  rw [hjet, hconj]
  ring

/-- Finite-dimensional duality preserves invertibility of the nonzero-covector symbols. -/
theorem isElliptic_formalTranspose_iff :
    (P.formalTransposeOperator μ).IsElliptic ↔ P.IsElliptic := by
  /- At each nonzero real covector the preceding identity describes the symbol as
  (-1)^m times the ordinary dual map. The fibers are finite-dimensional by local
  triviality, so a linear map is bijective exactly when its continuous dual is.
  The nonzero scalar factor does not affect bijectivity. Apply this pointwise;
  neither equal ranks nor ellipticity is assumed separately in either direction. -/
  classical
  -- In finite-dimensional fibers every algebraic covector has its original continuous form.
  have hpoint (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      Function.Bijective ((P.formalTransposeOperator μ).principalSymbol x ξ) ↔
        Function.Bijective (P.principalSymbol x ξ) := by
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let e : Module.Dual ℂ (E x) ≃ₗ[ℂ] DualBundle E x := LinearMap.toContinuousLinearMap
    let f : Module.Dual ℂ (F x) ≃ₗ[ℂ] DualBundle F x := LinearMap.toContinuousLinearMap
    let A := P.principalSymbol x ξ
    let B : DualBundle F x →ₗ[ℂ] DualBundle E x :=
      e.toLinearMap.comp (A.dualMap.comp f.symm.toLinearMap)
    let a : ℂ := (-1 : ℂ) ^ m
    have ha : a ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    let c : DualBundle E x ≃ₗ[ℂ] DualBundle E x :=
      LinearEquiv.smulOfNeZero ℂ _ a ha
    have heq : (P.formalTransposeOperator μ).principalSymbol x ξ =
        c.toLinearMap.comp B := by
      apply LinearMap.ext
      intro α
      apply ContinuousLinearMap.ext
      intro v
      exact P.principalSymbol_formalTranspose_apply μ x ξ α v
    -- Removing the nonzero parity scalar and both dual identifications leaves A.dualMap.
    have hB : Function.Bijective B ↔ Function.Bijective A.dualMap := by
      constructor
      · intro hB
        have h := e.symm.bijective.comp (hB.comp f.bijective)
        have hfun : e.symm ∘ B ∘ f = A.dualMap := by
          funext α
          change e.symm (e (A.dualMap (f.symm (f α)))) = A.dualMap α
          rw [f.symm_apply_apply, e.symm_apply_apply]
        rwa [hfun] at h
      · intro hA
        exact e.bijective.comp (hA.comp f.symm.bijective)
    have hscalar : Function.Bijective (c.toLinearMap.comp B) ↔ Function.Bijective B := by
      constructor
      · intro hC
        have h := c.symm.bijective.comp hC
        have hfun : c.symm ∘ c.toLinearMap.comp B = B := by
          funext α
          exact c.symm_apply_apply (B α)
        rwa [hfun] at h
      · intro hB
        exact c.bijective.comp hB
    rw [heq, hscalar, hB, LinearMap.dualMap_bijective_iff]
  constructor
  · intro hP x ξ hξ
    exact (hpoint x ξ).mp (hP x ξ hξ)
  · intro hP x ξ hξ
    exact (hpoint x ξ).mpr (hP x ξ hξ)

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The common Sobolev extension of the actual transpose, with target order normalized. -/
def formalTransposeSobolevExtension (s : ℝ) :
    B.dualPresentation.SobolevSpace (-(s - m)) →L[ℂ]
      A.dualPresentation.SobolevSpace (-s) := by
  have h : -(s - (m : ℝ)) - (m : ℝ) = -s := by ring
  exact h ▸ (P.formalTransposeOperator μ).sobolevExtension
    B.dualPresentation A.dualPresentation (-(s - m))

/-- On smooth covectors the common Sobolev realization retains the actual transpose action. -/
theorem formalTransposeSobolevExtension_smooth (s : ℝ)
    (α : smoothDualSections (n := n) (r := q) F) :
    P.formalTransposeSobolevExtension μ A B s
        (B.dualPresentation.smoothToSobolev (-(s - m)) (dualSectionsEquiv F α)) =
      A.dualPresentation.smoothToSobolev (-s)
        (dualSectionsEquiv E (P.formalTranspose μ α)) := by
  /- Use the smooth-input specification of the differential operator's Sobolev
  extension and formalTransposeOperator_apply. Normalize the output order by
  -(s-m)-m=-s, exactly as in the definition; the represented smooth section is unchanged. -/
  -- The ordinary extension already acts by the same smooth transpose section.
  have haction := (P.formalTransposeOperator μ).sobolevExtension_smoothToSobolev
    B.dualPresentation A.dualPresentation (-(s - m)) (dualSectionsEquiv F α)
  rw [P.formalTransposeOperator_apply] at haction
  -- Transport only the target order; the input and represented section stay fixed.
  have hcast (t u : ℝ) (htu : t = u)
      (T : B.dualPresentation.SobolevSpace (-(s - m)) →L[ℂ]
        A.dualPresentation.SobolevSpace t)
      (β : B.dualPresentation.SobolevSpace (-(s - m)))
      (v : smoothSections (n := n) (r := r) (DualBundle E))
      (hT : T β = A.dualPresentation.smoothToSobolev t v) :
      (htu ▸ T) β = A.dualPresentation.smoothToSobolev u v := by
    subst u
    exact hT
  exact hcast _ _ (by ring) _ _ _ haction

/-- The independent continuous transpose agrees with the common differential Sobolev extension. -/
theorem dualSobolevEquiv_transpose (s : ℝ) (α : B.DualSobolevSpace (-(s - m))) :
    A.dualSobolevEquiv (-s) (P.sobolevTranspose μ A B s α) =
      P.formalTransposeSobolevExtension μ A B s
        (B.dualSobolevEquiv (-(s - m)) α) := by
  /- Stage 1: on smooth covectors combine both transpose extension specifications
  with dualSobolevEquiv_smooth; both sides are the same smooth output section.
  Stage 2: smooth covectors are dense in the independent dual Sobolev completion.
  Both sides are continuous linear maps, hence equality extends to every input.
  This uses no ellipticity or closed-range hypothesis, and claims no Hilbert-adjoint identity. -/
  have hmap := (B.denseRange_dualSmoothToSobolev (-(s - m))).equalizer
    ((A.dualSobolevEquiv (-s)).continuous.comp
      (P.sobolevTranspose μ A B s).continuous)
    ((P.formalTransposeSobolevExtension μ A B s).continuous.comp
      (B.dualSobolevEquiv (-(s - m))).continuous) (by
      funext β
      simp only [Function.comp_apply]
      rw [P.sobolevTranspose_smooth, A.dualSobolevEquiv_smooth,
        B.dualSobolevEquiv_smooth, P.formalTransposeSobolevExtension_smooth])
  exact congrFun hmap α

end DifferentialOperator

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.ComplexDisk
public import AtiyahSinger.Topology.RelativeKZeroProduct

/-!
# The specified disk boundary class and its plane realization

Public module ID: M1564.

These original constructions and proofs identify multiplication by the positive
boundary coordinate with the complex-line class under the fixed radial map.
Their separation allows the geometric Bott proof to reuse this comparison
without importing the later relative periodicity theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] complexUnitClosedDisc_compactSpace complexUnitClosedDisc_t2Space
  trivialTopology isFiniteRank_trivial

/-- Continuity of the actual multiplication-by-z boundary action and its inverse. -/
theorem bottDisk_boundary_continuity :
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial Complex.UnitClosedDisc (Fin 1 → ℂ)) complexDiskBoundary) ↦
        (⟨z.proj, (z.proj.val : ℂ) • z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial Complex.UnitClosedDisc (Fin 1 → ℂ))
            complexDiskBoundary))) ∧
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial Complex.UnitClosedDisc (Fin 1 → ℂ)) complexDiskBoundary) ↦
        (⟨z.proj, (z.proj.val : ℂ)⁻¹ • z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial Complex.UnitClosedDisc (Fin 1 → ℂ))
            complexDiskBoundary))) := by
  /- In the actual restricted product trivializations, the two maps are
  (z,v) -> (z,zv) and (z,v) -> (z,z⁻¹v). The boundary coordinate has norm
  one, so it is never zero. Joint multiplication and inversion away from
  zero are continuous. Transport these maps through the original trivial
  and restriction topologies, retaining the same boundary points and fibers. -/
  let A := complexDiskBoundary
  let E := Bundle.Trivial Complex.UnitClosedDisc (Fin 1 → ℂ)
  let f : A → Complex.UnitClosedDisc := Subtype.val
  -- Read both coordinates in the actual restricted trivial-bundle topology.
  have hbase : Continuous (fun z : TotalSpace Unit (Restrict E A) ↦ z.proj) :=
    Pullback.continuous_proj Unit E f
  have hpoint : Continuous (fun z : TotalSpace Unit (Restrict E A) ↦ (z.proj.val : ℂ)) :=
    Complex.UnitClosedDisc.continuous_coe.comp (continuous_subtype_val.comp hbase)
  have hvector : Continuous (fun z : TotalSpace Unit (Restrict E A) ↦ z.snd) := by
    have hp : Continuous (fun z : TotalSpace Unit E ↦ (z.proj, z.snd)) :=
      continuous_induced_dom
    exact continuous_snd.comp (hp.comp (Pullback.continuous_lift Unit E f))
  have hne (z : TotalSpace Unit (Restrict E A)) : (z.proj.val : ℂ) ≠ 0 := by
    intro hz
    have hnorm : ‖(z.proj.val : ℂ)‖ = 1 := z.proj.property
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinverse := hpoint.inv₀ hne
  constructor
  · -- The forward boundary action uses the same positive complex coordinate.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    apply hbase.prodMk
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val.comp hbase).prodMk (hpoint.smul hvector)
  · -- Norm one ensures that the jointly continuous inverse never meets zero.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    apply hbase.prodMk
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val.comp hbase).prodMk (hinverse.smul hvector)

/-- The standard disk-boundary Bott triple with its specified positive coordinate action. -/
def bottDiskTriple : BundleTriple complexDiskBoundary where
  source := FiniteBundle.trivial Complex.UnitClosedDisc 1
  target := FiniteBundle.trivial Complex.UnitClosedDisc 1
  boundary :=
    { linearEquiv := fun z ↦
        LinearEquiv.smulOfNeZero ℂ (Fin 1 → ℂ) (z.val : ℂ) (by
          intro hz
          have hnorm : ‖(z.val : ℂ)‖ = 1 := z.property
          rw [hz, norm_zero] at hnorm
          exact zero_ne_one hnorm)
      continuous_total := bottDisk_boundary_continuity.1
      continuous_symm := bottDisk_boundary_continuity.2 }

/-- The relative difference class of the actual disk-boundary triple d(1,1,z). -/
def bottDiskClass : RelativeKZero.{_, 0} complexDiskBoundary isClosed_complexDiskBoundary :=
  bottDiskTriple.relativeClass isClosed_complexDiskBoundary

/-- Positive radial coordinates identify the original open disk with the complex plane. -/
def complexDiskInteriorHomeomorph :
    (complexDiskBoundaryᶜ : Set Complex.UnitClosedDisc) ≃ₜ ℂ :=
  let e : (complexDiskBoundaryᶜ : Set Complex.UnitClosedDisc) ≃ₜ Metric.ball (0 : ℂ) 1 :=
    { toFun := fun z ↦
        ⟨(z.val : ℂ), mem_ball_zero_iff.mpr
          (lt_of_le_of_ne z.val.norm_le_one z.property)⟩
      invFun := fun z ↦
        ⟨Complex.UnitClosedDisc.mk z.val (le_of_lt (mem_ball_zero_iff.mp z.property)),
          (mem_ball_zero_iff.mp z.property).ne⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl
      continuous_toFun :=
        (Complex.UnitClosedDisc.continuous_coe.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  e.trans (Homeomorph.unitBall (E := ℂ)).symm

/-- The specified disk generator becomes the existing positive complex-line class. -/
theorem bottDiskClass_toCompactSupport :
    letI := isClosed_complexDiskBoundary.isOpen_compl.locallyCompactSpace
    compactSupportKZeroHomeomorphEquiv complexDiskInteriorHomeomorph
      (relativeKZeroCompactSupportEquiv complexDiskBoundary isClosed_complexDiskBoundary
        bottDiskClass) = bottLineClass := by
  /- First identify the multiplication-by-z triple on the closed-unit-ball window
  with the pullback of bottDiskTriple by its boundary square. This expresses
  bottLineClass through the window compactification map.
  Next use the saturated radial map R, with positive denominator
  max (sqrt (1 - ‖z‖²)) ‖z‖. The straight-line homotopy from the identity
  to R stays in the disk and fixes its boundary, so R preserves bottDiskClass.
  The two compactification maps satisfy qbar.comp w = Rbar.comp k: inside
  the window the radial coordinates agree, and outside it both maps reach
  the collapsed boundary. Pullback composition gives the desired equality.
  Both boundary triples use multiplication by the positive complex coordinate. -/

  classical
  let := isClosed_complexDiskBoundary.isOpen_compl.locallyCompactSpace
  let D := Complex.UnitClosedDisc
  let S := complexDiskBoundary
  let E := FiniteBundle.trivial ℂ 1
  let a : SupportBundleTriple ℂ := SupportBundleTriple.ofBoundary E E bottLineTriple
  let L : Set ℂ := Metric.closedBall 0 1
  have hL : IsCompact L := isCompact_closedBall 0 1
  let := isCompact_iff_compactSpace.mp hL
  have hInt : interior L = Metric.ball 0 1 := interior_closedBall 0 (by norm_num)
  have haL : a.datum.control ⊆ interior L := by
    intro z hz
    have hz0 : z = 0 := hz
    rw [hz0, hInt]
    exact Metric.mem_ball_self (by norm_num)
  let A := supportWindowBoundary L
  have hA : IsClosed A := isClosed_supportWindowBoundary L
  let := hA.isOpen_compl.locallyCompactSpace
  let := (isOpen_interior (s := L)).locallyCompactSpace
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space S isClosed_complexDiskBoundary
  -- The literal unit-ball window retains the original multiplication-by-z seam.
  let q : C(L, D) :=
    ⟨fun z ↦ Complex.UnitClosedDisc.mk z.val (mem_closedBall_zero_iff.mp z.property),
      continuous_subtype_val.subtype_mk _⟩
  have hpre : A = q ⁻¹' S := by
    ext z
    change (z.val ∉ interior L) ↔ ‖z.val‖ = 1
    rw [hInt, mem_ball_zero_iff]
    exact ⟨fun h ↦ le_antisymm (mem_closedBall_zero_iff.mp z.property)
      (le_of_not_gt h), fun h ↦ by rw [h]; exact lt_irrefl _⟩
  have hpair : Set.MapsTo q A S := fun z hz ↦ by
    change z ∈ q ⁻¹' S
    rw [← hpre]
    exact hz
  let i : C(L, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  let e : Iso (E.restrict L).Fiber ((q : L → D) *ᵖ bottDiskTriple.source.Fiber) :=
    (pullbackTrivialIso i 1).trans (pullbackTrivialIso q 1).symm
  have he (z : L) (v : Fin 1 → ℂ) : e.linearEquiv z v = v := by
    apply ((pullbackTrivialIso q 1).linearEquiv z).injective
    change (pullbackTrivialIso q 1).linearEquiv z
      (((pullbackTrivialIso q 1).linearEquiv z).symm
        ((pullbackTrivialIso i 1).linearEquiv z v)) = _
    rw [LinearEquiv.apply_symm_apply, pullbackTrivialIso_apply, pullbackTrivialIso_apply]
  have classBySquare (C : Set L) (hC : IsClosed C)
      (hmap : Set.MapsTo q C S) (hCeq : C = q ⁻¹' S) (t : BundleTriple C)
      (eS : Iso t.source.Fiber ((q : L → D) *ᵖ bottDiskTriple.source.Fiber))
      (eT : Iso t.target.Fiber ((q : L → D) *ᵖ bottDiskTriple.target.Fiber))
      (hsquare : ∀ (z : C) (v : t.source.Fiber z.val),
        eT.linearEquiv z.val (t.boundary.linearEquiv z v) =
          bottDiskTriple.boundary.linearEquiv ⟨q z.val, hmap z.property⟩
            (eS.linearEquiv z.val v)) :
      t.relativeClass hC = relativeKZeroPullback C hC S
        isClosed_complexDiskBoundary q hmap bottDiskClass := by
    subst C
    have hi : t.IsIsomorphic (bottDiskTriple.pullback q) := by
      refine ⟨eS, eT, ?_⟩
      intro z v
      exact (hsquare z v).trans
        (RelativeTriple.pullback_apply bottDiskTriple.boundary q z
          (eS.linearEquiv z.val v)).symm
    exact (t.relativeClass_eq_of_isIsomorphic hC _ hi).trans
      (bottDiskTriple.relativeClass_pullback isClosed_complexDiskBoundary q)
  have hwindow : (a.windowTriple L haL).relativeClass hA =
      relativeKZeroPullback A hA S isClosed_complexDiskBoundary q hpair bottDiskClass := by
    apply classBySquare A hA hpair hpre (a.windowTriple L haL) e e
    intro z v
    erw [he, he, a.windowBoundary_apply L haL]
    rfl
  let qbar := PointedQuotient.mapContinuous A S q hpair
  let eL := supportWindowInteriorHomeomorph L
  let qL := PointedQuotient.onePointHomeomorph A hA
  let c : C(OnePoint ℂ, OnePoint (interior L)) :=
    ⟨onePointCollapse (interior L), continuous_onePointCollapse (interior L) isOpen_interior⟩
  let p := properOnePointMap ⟨eL.symm, eL.symm.continuous⟩ eL.symm.isProperMap
  let w : C(OnePoint ℂ, PointedQuotient A) :=
    (⟨qL.symm, qL.symm.continuous⟩ : C(_, _)).comp (p.comp c)
  have hwInfty : w OnePoint.infty = PointedQuotient.basepoint A :=
    PointedQuotient.onePointHomeomorph_symm_infty A hA
  have hwMem (z : ℂ) (hz : z ∈ interior L) :
      w (z : OnePoint ℂ) = PointedQuotient.of A ⟨z, interior_subset hz⟩ := by
    change qL.symm (OnePoint.map eL.symm
      (onePointCollapse (interior L) (z : OnePoint ℂ))) = _
    rw [onePointCollapse_coe_of_mem (interior L) z hz]
    exact qL.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of A hA (eL.symm ⟨z, hz⟩)).symm
  have hwNotMem (z : ℂ) (hz : z ∉ interior L) :
      w (z : OnePoint ℂ) = PointedQuotient.basepoint A := by
    change qL.symm (OnePoint.map eL.symm
      (onePointCollapse (interior L) (z : OnePoint ℂ))) = _
    rw [onePointCollapse_coe_of_notMem (interior L) z hz, OnePoint.map_infty]
    exact PointedQuotient.onePointHomeomorph_symm_infty A hA
  have hline : bottLineClass.val = complexKZeroPullback (qbar.comp w) bottDiskClass.val := by
    have hmodel := compactSupportTriple_compactSupportClass_ofBoundary E E bottLineTriple
    change bottLineClass = a.compactSupportClass at hmodel
    rw [hmodel, a.compactSupportClass_eq_windowClass L hL haL]
    change complexKZeroPullback c (complexKZeroPullback p
      (complexKZeroPullback ⟨qL.symm, qL.symm.continuous⟩
        ((a.windowTriple L haL).relativeClass hA).val)) = _
    rw [hwindow]
    change complexKZeroPullback c (complexKZeroPullback p
      (complexKZeroPullback ⟨qL.symm, qL.symm.continuous⟩
        (complexKZeroPullback qbar bottDiskClass.val))) = _
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  -- Saturate the positive radial coordinate at the unit sphere before taking the quotient.
  let r (z : D) : ℝ := max (Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)) ‖(z : ℂ)‖
  have hr (z : D) : 0 < r z := by
    by_cases hz : ‖(z : ℂ)‖ = 0
    · simp [r, hz]
    · exact lt_of_lt_of_le (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)) (le_max_right _ _)
  let R : C(D, D) :=
    ⟨fun z ↦ Complex.UnitClosedDisc.mk ((r z)⁻¹ • (z : ℂ)) (by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hr z).le),
        ← div_eq_inv_mul, div_le_one (hr z)]
      exact le_max_right _ _), by
      apply Continuous.subtype_mk
      have hn : Continuous (fun z : D ↦ ‖(z : ℂ)‖) :=
        Complex.UnitClosedDisc.continuous_coe.norm
      have hd : Continuous r := ((continuous_const.sub (hn.pow 2)).sqrt).max hn
      exact (hd.inv₀ (fun z ↦ (hr z).ne')).smul
        Complex.UnitClosedDisc.continuous_coe⟩
  have hRfixed (z : D) (hz : z ∈ S) : R z = z := by
    apply Complex.UnitClosedDisc.coe_injective
    have hnorm : ‖(z : ℂ)‖ = 1 := hz
    simp [R, r, hnorm]
  have hRpair : Set.MapsTo R S S := by
    intro z hz
    rw [hRfixed z hz]
    exact hz
  let H : ContinuousMap.Homotopy (ContinuousMap.id D) R :=
    { toFun tz := Complex.UnitClosedDisc.mk
        ((1 - (tz.1 : ℝ)) • (tz.2 : ℂ) + (tz.1 : ℝ) • (R tz.2 : ℂ)) (by
          calc
            ‖(1 - (tz.1 : ℝ)) • (tz.2 : ℂ) + (tz.1 : ℝ) • (R tz.2 : ℂ)‖ ≤
                ‖(1 - (tz.1 : ℝ)) • (tz.2 : ℂ)‖ +
                  ‖(tz.1 : ℝ) • (R tz.2 : ℂ)‖ := norm_add_le _ _
            _ = (1 - (tz.1 : ℝ)) * ‖(tz.2 : ℂ)‖ +
                (tz.1 : ℝ) * ‖(R tz.2 : ℂ)‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (sub_nonneg.mpr tz.1.property.2),
                abs_of_nonneg tz.1.property.1]
            _ ≤ (1 - (tz.1 : ℝ)) * 1 + (tz.1 : ℝ) * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left tz.2.norm_le_one
                (sub_nonneg.mpr tz.1.property.2))
                (mul_le_mul_of_nonneg_left (R tz.2).norm_le_one tz.1.property.1)
            _ = 1 := by ring)
      continuous_toFun := by
        apply Continuous.subtype_mk
        have ht : Continuous (fun tz : unitInterval × D ↦ (tz.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        have hz : Continuous (fun tz : unitInterval × D ↦ (tz.2 : ℂ)) :=
          Complex.UnitClosedDisc.continuous_coe.comp continuous_snd
        exact ((continuous_const.sub ht).smul hz).add
          (ht.smul (Complex.UnitClosedDisc.continuous_coe.comp (R.continuous.comp continuous_snd)))
      map_zero_left := fun z ↦ Complex.UnitClosedDisc.coe_injective (by simp)
      map_one_left := fun z ↦ Complex.UnitClosedDisc.coe_injective (by simp) }
  have hHpair (t : unitInterval) (z : D) (hz : z ∈ S) : H (t, z) ∈ S := by
    have heq : H (t, z) = z := by
      apply Complex.UnitClosedDisc.coe_injective
      change (1 - (t : ℝ)) • (z : ℂ) + (t : ℝ) • (R z : ℂ) = (z : ℂ)
      rw [hRfixed z hz, ← add_smul]
      simp
    rw [heq]
    exact hz
  have hRid := relativeKZeroPullback_eq_of_homotopy S isClosed_complexDiskBoundary S
    isClosed_complexDiskBoundary (ContinuousMap.id D) R (fun _ hz ↦ hz) hRpair H hHpair
  have hRclass : relativeKZeroPullback S isClosed_complexDiskBoundary S
      isClosed_complexDiskBoundary R hRpair bottDiskClass = bottDiskClass := by
    rw [← hRid, relativeKZeroPullback_id]
    rfl
  let Rbar := PointedQuotient.mapContinuous S S R hRpair
  let eD := complexDiskInteriorHomeomorph
  let qD := PointedQuotient.onePointHomeomorph S isClosed_complexDiskBoundary
  let k : C(OnePoint ℂ, PointedQuotient S) :=
    (⟨qD.symm, qD.symm.continuous⟩ : C(_, _)).comp
      (properOnePointMap ⟨eD.symm, eD.symm.continuous⟩ eD.symm.isProperMap)
  have hk (z : ℂ) : k (z : OnePoint ℂ) = PointedQuotient.of S (eD.symm z).val := by
    change qD.symm (OnePoint.map eD.symm (z : OnePoint ℂ)) = _
    rw [OnePoint.map_some]
    exact qD.symm_apply_eq.mpr
      (PointedQuotient.onePointHomeomorph_of S isClosed_complexDiskBoundary (eD.symm z)).symm
  have hsqrt (z : (Sᶜ : Set D)) : 0 < Real.sqrt (1 - ‖(z.val : ℂ)‖ ^ 2) := by
    apply Real.sqrt_pos.mpr
    have hz : ‖(z.val : ℂ)‖ < 1 := lt_of_le_of_ne z.val.norm_le_one z.property
    nlinarith [norm_nonneg (z.val : ℂ)]
  have hradial (z : (Sᶜ : Set D)) :
      eD z = (Real.sqrt (1 - ‖(z.val : ℂ)‖ ^ 2))⁻¹ • (z.val : ℂ) := by
    exact Homeomorph.unitBall_symm_apply _
  have hradialNorm (z : (Sᶜ : Set D)) :
      ‖eD z‖ = ‖(z.val : ℂ)‖ / Real.sqrt (1 - ‖(z.val : ℂ)‖ ^ 2) := by
    rw [hradial, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hsqrt z).le),
      div_eq_inv_mul]
  have hRinside (z : (Sᶜ : Set D)) (hz : ‖eD z‖ < 1) : (R z.val : ℂ) = eD z := by
    have hlt : ‖(z.val : ℂ)‖ < Real.sqrt (1 - ‖(z.val : ℂ)‖ ^ 2) := by
      rw [hradialNorm] at hz
      exact (div_lt_one (hsqrt z)).mp hz
    change (max (Real.sqrt (1 - ‖(z.val : ℂ)‖ ^ 2)) ‖(z.val : ℂ)‖)⁻¹ •
      (z.val : ℂ) = _
    rw [max_eq_left hlt.le, hradial]
  have hRoutside (z : (Sᶜ : Set D)) (hz : ¬ ‖eD z‖ < 1) : R z.val ∈ S := by
    have hle : Real.sqrt (1 - ‖(z.val : ℂ)‖ ^ 2) ≤ ‖(z.val : ℂ)‖ := by
      rw [hradialNorm] at hz
      exact le_of_not_gt (fun h ↦ hz ((div_lt_one (hsqrt z)).mpr h))
    have hnorm : 0 < ‖(z.val : ℂ)‖ := lt_of_lt_of_le (hsqrt z) hle
    change ‖(max (Real.sqrt (1 - ‖(z.val : ℂ)‖ ^ 2)) ‖(z.val : ℂ)‖)⁻¹ •
      (z.val : ℂ)‖ = 1
    rw [max_eq_right hle, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le),
      inv_mul_cancel₀ hnorm.ne']
  -- The two compactification maps differ by this boundary-fixing positive radial homotopy.
  have hsquare : qbar.comp w = Rbar.comp k := by
    ext z
    cases z using OnePoint.rec with
    | infty =>
      change qbar (w OnePoint.infty) = Rbar (k OnePoint.infty)
      rw [hwInfty]
      change PointedQuotient.basepoint S =
        Rbar (qD.symm OnePoint.infty)
      rw [PointedQuotient.onePointHomeomorph_symm_infty S isClosed_complexDiskBoundary]
      rfl
    | coe z =>
      change qbar (w (z : OnePoint ℂ)) = Rbar (k (z : OnePoint ℂ))
      rw [hk]
      by_cases hz : z ∈ interior L
      · rw [hwMem z hz]
        change PointedQuotient.of S (q ⟨z, interior_subset hz⟩) =
          PointedQuotient.of S (R (eD.symm z).val)
        apply congrArg (PointedQuotient.of S)
        apply Complex.UnitClosedDisc.coe_injective
        have hz' : ‖eD (eD.symm z)‖ < 1 := by
          rw [eD.apply_symm_apply]
          exact mem_ball_zero_iff.mp (hInt ▸ hz)
        exact ((hRinside (eD.symm z) hz').trans (eD.apply_symm_apply z)).symm
      · rw [hwNotMem z hz]
        change PointedQuotient.basepoint S = PointedQuotient.of S (R (eD.symm z).val)
        apply ((PointedQuotient.of_eq_basepoint_iff S _).mpr ?_).symm
        apply hRoutside
        rw [eD.apply_symm_apply]
        intro hlt
        exact hz (hInt.symm ▸ mem_ball_zero_iff.mpr hlt)
  apply Subtype.ext
  change complexKZeroPullback
    (properOnePointMap ⟨eD.symm, eD.symm.continuous⟩ eD.symm.isProperMap)
    (complexKZeroPullback ⟨qD.symm, qD.symm.continuous⟩ bottDiskClass.val) = bottLineClass.val
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  change complexKZeroPullback k bottDiskClass.val = bottLineClass.val
  calc
    complexKZeroPullback k bottDiskClass.val =
        complexKZeroPullback k (complexKZeroPullback Rbar bottDiskClass.val) :=
      congrArg (complexKZeroPullback k) (congrArg Subtype.val hRclass).symm
    _ = complexKZeroPullback (Rbar.comp k) bottDiskClass.val := by
      rw [complexKZeroPullback_comp k Rbar, AddMonoidHom.comp_apply]
    _ = bottLineClass.val := by rw [← hsquare, ← hline]

end AtiyahSinger

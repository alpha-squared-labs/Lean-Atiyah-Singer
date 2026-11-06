/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolev

import AtiyahSinger.Analysis.SobolevCoordinateChange
import AtiyahSinger.Analysis.SobolevMultiplication
import AtiyahSinger.Geometry.AtlasFrame

/-!
# Presentation independence and Rellich for locally finite-rank Sobolev spaces

Public module ID: M0308.

A01: the identity on the original smooth sections determines the comparison of two
finite presentations and the inclusion between two real Sobolev orders. The actual
continuous linear equivalence expresses two-sided norm equivalence. Every selected
chart retains its own rank, and both completions retain the original bundle atlas.

Sources: Spin Geometry III.2.6 and 2.11–2.14. The finite presentation forces
compactness of the base because its compact cutoff supports cover the base. Negative
orders use the existing Bessel distribution realizations; Rellich requires t < s.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  {A : SmoothComplexBundleAtlas (n := n) E}

include hM hT2 hSC

namespace AtlasBundlePresentation

variable (L K : AtlasBundlePresentation A)

/-- Changing the presentation gives the unique Sobolev equivalence fixing smooth sections. -/
theorem existsUnique_sobolevEquiv (s : ℝ) :
    ∃! T : L.SobolevSpace s ≃L[ℂ] K.SobolevSpace s,
      ∀ u : A.smoothSections,
        T (L.smoothToSobolev s u) = K.smoothToSobolev s u := by
  /- Stage 1: insert the L partition into each K localization. On compact overlap
  supports this is a finite sum of smooth matrix multiplications and coordinate
  changes. Apply SG III.2.11–2.12 at real order s using the actual rectangular
  transition matrices. No global rank or rank equation on disjoint charts is needed.
  Finite summation gives one norm bound, and swapping L and K
  gives the reverse bound.
  Stage 2: extend the actual identity on smooth sections to both completions.
  The two composites are identities on dense smooth images and hence everywhere.
  The same density identifies any competing equivalence with this one. -/
  classical
  have htransfer (L K : AtlasBundlePresentation A) (i : Fin L.size) (j : Fin K.size) :
      ∃ T : 𝓢(EuclideanSpace ℝ (Fin n),
          EuclideanSpace ℂ (Fin (A.rank (L.frameIndex i)))) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (K.frameIndex j)))),
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ v, ‖schwartzSobolevCoordinate s (T v)‖ ≤
            C * ‖schwartzSobolevCoordinate s v‖) ∧
          ∀ (u : A.smoothSections) z,
            T (L.localize i u) z = (L.cutoff i ((K.chart j).symm z) : ℂ) • K.localize j u z := by
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin (A.rank (L.frameIndex i)))
    let W := EuclideanSpace ℂ (Fin (A.rank (K.frameIndex j)))
    let I := 𝓘(ℝ, X)
    let c := L.chart i
    let d := K.chart j
    let e := L.frameIndex i
    let f := K.frameIndex j
    let ev := EuclideanSpace.equiv (Fin (A.rank e)) ℂ
    let ew := EuclideanSpace.equiv (Fin (A.rank f)) ℂ
    let t := d.symm.trans c
    let U := d.target ∩ d.symm ⁻¹' (c.source ∩
      ((A.chart e).baseSet ∩ (A.chart f).baseSet))
    have hU : IsOpen U := d.continuousOn_symm.isOpen_inter_preimage d.open_target
      (c.open_source.inter ((A.chart e).open_baseSet.inter (A.chart f).open_baseSet))
    have hUt : U ⊆ t.source := fun z hz ↦ ⟨hz.1, hz.2.1⟩
    let S := tsupport (L.cutoff i) ∩ tsupport (K.cutoff j)
    have hS : IsCompact S := (L.compact_support i).inter_right (isClosed_tsupport _)
    have hSd : S ⊆ d.source := fun x hx ↦ (K.support_subset j hx.2).1
    have hSimage : IsCompact (d '' S) := hS.image_of_continuousOn (d.continuousOn.mono hSd)
    have hSU : d '' S ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨d.map_source (hSd hx), ?_⟩
      change d.symm (d x) ∈ c.source ∩ ((A.chart e).baseSet ∩ (A.chart f).baseSet)
      rw [d.left_inv (hSd hx)]
      exact ⟨(L.support_subset i hx.1).1, (L.support_subset i hx.1).2,
        (K.support_subset j hx.2).2⟩
    -- One compact plateau stays inside the overlap of the original charts and frames.
    obtain ⟨O, hOo, hSO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure hSimage hU hSU
    obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo hSimage.isClosed hSO
    have hηsupport : tsupport η = closure O := congrArg closure hsη
    have hcη : HasCompactSupport η := by simpa [HasCompactSupport, hηsupport] using hOc
    have hηU : tsupport η ⊆ U := by rwa [hηsupport]
    have hηone (x : M) (hx : x ∈ S) : η (d x) = 1 :=
      (honeη _).mp ⟨x, hx, rfl⟩
    have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) (L.chart_mem_atlas i)
    have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) (K.chart_mem_atlas j)
    have ht : ContDiffOn ℝ ∞ t t.source := by
      intro z hz
      exact (((contMDiffAt_of_mem_maximalAtlas hcM hz.2).comp z
        (contMDiffAt_symm_of_mem_maximalAtlas hdM hz.1)).contDiffAt).contDiffWithinAt
    have hts : ContDiffOn ℝ ∞ t.symm t.target := by
      intro z hz
      exact (((contMDiffAt_of_mem_maximalAtlas hdM hz.2).comp z
        (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1)).contDiffAt).contDiffWithinAt
    have hdU : ContMDiffOn I I ∞ d.symm U := by
      intro z hz
      exact (contMDiffAt_symm_of_mem_maximalAtlas hdM hz.1).contMDiffWithinAt
    -- The rectangular frame matrix is the finite sum of its original transition columns.
    let p (a : Fin (A.rank e)) : V →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj a).comp ev.toContinuousLinearMap
    let H (x : M) : V →L[ℂ] W := ∑ a : Fin (A.rank e),
      ContinuousLinearMap.smulRightL ℂ V W (p a)
        (ew.symm ((A.chart f ((A.chart e).toPartialEquiv.symm (x, Pi.single a 1))).2))
    have hH : ContDiffOn ℝ ∞ (fun z ↦ H (d.symm z)) U := by
      apply ContDiffOn.sum
      intro a _
      have hcol := (A.contMDiffOn_coordChange e f a).comp hdU (fun z hz ↦ hz.2.2)
      have hvec := (ew.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
        hcol.contDiffOn
      exact ((ContinuousLinearMap.smulRightL ℂ V W (p a)).restrictScalars ℝ).contDiff
        |>.comp_contDiffOn hvec
    have hHapply (x : M) (he : x ∈ (A.chart e).baseSet)
        (hf : x ∈ (A.chart f).baseSet) (v : E x) :
        H x (ev.symm ((A.chart e ⟨x, v⟩).2)) = ew.symm ((A.chart f ⟨x, v⟩).2) := by
      let R := (A.frameLinearEquiv f x hf).toLinearMap.comp
        (A.frameLinearEquiv e x he).symm.toLinearMap
      have hexpand := congrArg R ((Pi.basisFun ℂ (Fin (A.rank e))).sum_repr
        ((A.frameLinearEquiv e x he) v))
      simp [R, map_sum, map_smul] at hexpand
      have hcolumn (a : Fin (A.rank e)) :
          (A.frameLinearEquiv f x hf) ((A.frameLinearEquiv e x he).symm (Pi.single a 1)) =
            (A.chart f ((A.chart e).toPartialEquiv.symm (x, Pi.single a 1))).2 := by
        change (A.chart f ⟨x, cast (congrArg E ((A.chart e).proj_symm_apply' he))
          ((A.chart e).toOpenPartialHomeomorph.symm (x, Pi.single a 1)).2⟩).2 = _
        have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
          ((A.chart e).proj_symm_apply' (x := Pi.single a 1) he)
          ((A.chart e).toOpenPartialHomeomorph.symm (x, Pi.single a 1)).2
        exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart f z).2) hpoint
      simp only [hcolumn] at hexpand
      apply ew.injective
      simpa [H, p, map_sum, map_smul, ContinuousLinearMap.smulRightL_apply_apply,
        SmoothComplexBundleAtlas.frameLinearEquiv] using hexpand
    let F : X → V →L[ℂ] W := fun z ↦ (K.cutoff j (d.symm z) : ℂ) • H (d.symm z)
    have hF : ContDiffOn ℝ ∞ F U := by
      have hscalar := (Complex.ofRealCLM.contMDiff.comp (K.smooth_cutoff j))
        |>.comp_contMDiffOn hdU
      exact hscalar.contDiffOn.smul hH
    let G := cutoffMatrix η F
    have hG : ContDiff ℝ ∞ G := contDiff_cutoffMatrix U hU F hF η hη hηU
    have hcG : HasCompactSupport G := hasCompactSupport_cutoffMatrix η F hcη
    let P : 𝓢(X, V) →L[ℂ] 𝓢(X, V) :=
      cutoffPullbackCLM t.source t.open_source t ht η hη hcη (hηU.trans hUt)
    let T := (matrixMultiplierCLM G hG hcG).comp P
    obtain ⟨C₁, hC₁, hb₁⟩ := exists_norm_cutoffPullback_sobolev_le t ht hts
      η hη hcη (hηU.trans hUt) s
    obtain ⟨C₂, hC₂, hb₂⟩ := exists_norm_matrixMultiplier_sobolev_le G hG hcG s
    refine ⟨T, C₂ * C₁, mul_nonneg hC₂ hC₁, ?_, ?_⟩
    · intro v
      apply (hb₂ (P v)).trans
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb₁ v) hC₂
    intro u z
    change matrixMultiplierCLM G hG hcG (P (L.localize i u)) z = _
    rw [matrixMultiplierCLM_apply]
    by_cases hz : z ∈ tsupport η
    · have hzU := hηU hz
      have hctarget : t z ∈ c.target := c.map_source hzU.2.1
      change t z ∈ (L.chart i).target at hctarget
      have hdtarg : z ∈ (K.chart j).target := hzU.1
      have hinv : c.symm (t z) = d.symm z := c.left_inv hzU.2.1
      rw [show P (L.localize i u) z = η z • L.localize i u (t z) from
        cutoffPullbackCLM_apply t.source t.open_source t ht η hη hcη
          (hηU.trans hUt) (L.localize i u) z]
      change G z (η z • L.localizedFunction i u (t z)) =
        (L.cutoff i (d.symm z) : ℂ) • K.localizedFunction j u z
      simp only [localizedFunction, atlasSectionInChart, ite_eq_left hctarget,
        ite_eq_left hdtarg]
      change G z (η z • ((L.cutoff i (c.symm (t z)) : ℂ) •
        ev.symm ((A.chart e ⟨c.symm (t z), u.val (c.symm (t z))⟩).2))) =
          (L.cutoff i (d.symm z) : ℂ) • (K.cutoff j (d.symm z) : ℂ) •
            ew.symm ((A.chart f ⟨d.symm z, u.val (d.symm z)⟩).2)
      rw [hinv]
      by_cases hxχ : L.cutoff i (d.symm z) = 0
      · simp [hxχ]
      by_cases hxψ : K.cutoff j (d.symm z) = 0
      · simp [G, cutoffMatrix, F, hxψ]
      have hxS : d.symm z ∈ S := ⟨subset_tsupport _ hxχ, subset_tsupport _ hxψ⟩
      have hηz : η z = 1 := by simpa only [d.right_inv hzU.1] using hηone _ hxS
      change (η z • ((K.cutoff j (d.symm z) : ℂ) • H (d.symm z)))
        (η z • ((L.cutoff i (d.symm z) : ℂ) •
          ev.symm ((A.chart e ⟨d.symm z, u.val (d.symm z)⟩).2))) = _
      rw [hηz, one_smul, one_smul]
      simp only [smul_apply, map_smul]
      rw [hHapply _ hzU.2.2.1 hzU.2.2.2]
    · have hzero : η z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hleft : G z = 0 := by simp [G, cutoffMatrix, hzero]
      rw [hleft, zero_apply]
      change 0 = (L.cutoff i (d.symm z) : ℂ) • K.localizedFunction j u z
      by_cases hzd : z ∈ d.target
      · change z ∈ (K.chart j).target at hzd
        rw [localizedFunction, ite_eq_left hzd]
        by_cases hxχ : L.cutoff i (d.symm z) = 0
        · simp [hxχ]
        by_cases hxψ : K.cutoff j (d.symm z) = 0
        · change K.cutoff j ((K.chart j).symm z) = 0 at hxψ
          simp [hxψ]
        have hxS : d.symm z ∈ S := ⟨subset_tsupport _ hxχ, subset_tsupport _ hxψ⟩
        have hηz : η z = 1 := by simpa only [d.right_inv hzd] using hηone _ hxS
        exact False.elim (zero_ne_one (hzero.symm.trans hηz))
      · change z ∉ (K.chart j).target at hzd
        simp only [localizedFunction, ite_eq_right hzd, smul_zero]
  have hbound (L K : AtlasBundlePresentation A) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : A.smoothSections, ‖K.smoothToSobolev s u‖ ≤ C * ‖L.smoothToSobolev s u‖ := by
    choose T C hC hb hT using htransfer L K
    have hlocal (j : Fin K.size) (u : A.smoothSections) :
        ‖schwartzSobolevCoordinate s (K.localize j u)‖ ≤
          (∑ i, C i j) * ‖L.smoothToSobolev s u‖ := by
      have hsum : (∑ i, T i j (L.localize i u)) = K.localize j u := by
        apply SchwartzMap.ext
        intro z
        simp only [sum_apply, hT, ← Finset.sum_smul]
        have hcut : ∑ i, (L.cutoff i ((K.chart j).symm z) : ℂ) = 1 := by
          exact_mod_cast L.sum_cutoff ((K.chart j).symm z)
        rw [hcut, one_smul]
      let R := schwartzSobolevCoordinateLinearMap n (A.rank (K.frameIndex j)) s
      change ‖R (K.localize j u)‖ ≤ _
      rw [← hsum, map_sum]
      calc
        ‖∑ i, R (T i j (L.localize i u))‖ ≤ ∑ i, ‖R (T i j (L.localize i u))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i, C i j * ‖L.smoothToSobolev s u‖ := by
          apply Finset.sum_le_sum
          intro i _
          exact (hb i j (L.localize i u)).trans
            (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (L.sobolevCoordinates s u) i)
              (hC i j))
        _ = (∑ i, C i j) * ‖L.smoothToSobolev s u‖ := (Finset.sum_mul _ _ _).symm
    refine ⟨∑ j, ∑ i, C i j,
      Finset.sum_nonneg (fun j _ ↦ Finset.sum_nonneg (fun i _ ↦ hC i j)), ?_⟩
    intro u
    have hnorm : ‖K.smoothToSobolev s u‖ ≤
        ∑ j, ‖schwartzSobolevCoordinate s (K.localize j u)‖ := by
      have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (fun (j : Fin K.size) _ ↦ norm_nonneg (schwartzSobolevCoordinate s (K.localize j u)))
      rw [← K.norm_smoothToSobolev_sq] at hsq
      have hn : 0 ≤ ∑ j, ‖schwartzSobolevCoordinate s (K.localize j u)‖ :=
        Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
      nlinarith [norm_nonneg (K.smoothToSobolev s u)]
    calc
      ‖K.smoothToSobolev s u‖ ≤ ∑ j, ‖schwartzSobolevCoordinate s (K.localize j u)‖ := hnorm
      _ ≤ ∑ j, (∑ i, C i j) * ‖L.smoothToSobolev s u‖ :=
        Finset.sum_le_sum (fun j _ ↦ hlocal j u)
      _ = (∑ j, ∑ i, C i j) * ‖L.smoothToSobolev s u‖ := (Finset.sum_mul _ _ _).symm
  -- Extend the same identity in both directions and identify its dense-image composites.
  obtain ⟨C, _, hC⟩ := hbound L K
  obtain ⟨D, _, hD⟩ := hbound K L
  let T : L.SobolevSpace s →L[ℂ] K.SobolevSpace s :=
    (K.smoothToSobolev s).extendOfNorm (L.smoothToSobolev s)
  let R : K.SobolevSpace s →L[ℂ] L.SobolevSpace s :=
    (L.smoothToSobolev s).extendOfNorm (K.smoothToSobolev s)
  have hT (u : A.smoothSections) : T (L.smoothToSobolev s u) = K.smoothToSobolev s u :=
    LinearMap.extendOfNorm_eq (L.denseRange_smoothToSobolev s) ⟨C, hC⟩ u
  have hR (u : A.smoothSections) : R (K.smoothToSobolev s u) = L.smoothToSobolev s u :=
    LinearMap.extendOfNorm_eq (K.denseRange_smoothToSobolev s) ⟨D, hD⟩ u
  have hRT : Function.LeftInverse R T := by
    intro x
    refine (L.denseRange_smoothToSobolev s).induction_on x
      (isClosed_eq (R.continuous.comp T.continuous) continuous_id) ?_
    intro u
    rw [hT, hR]
  have hTR : Function.RightInverse R T := by
    intro x
    refine (K.denseRange_smoothToSobolev s).induction_on x
      (isClosed_eq (T.continuous.comp R.continuous) continuous_id) ?_
    intro u
    rw [hR, hT]
  let e : L.SobolevSpace s ≃L[ℂ] K.SobolevSpace s :=
    { toFun := T
      invFun := R
      left_inv := hRT
      right_inv := hTR
      map_add' := T.map_add
      map_smul' := T.map_smul
      continuous_toFun := T.continuous
      continuous_invFun := R.continuous }
  refine ⟨e, hT, ?_⟩
  intro e' he'
  apply DFunLike.coe_injective
  apply (L.denseRange_smoothToSobolev s).equalizer e'.continuous e.continuous
  funext u
  exact (he' u).trans (hT u).symm

/-- The presentation equivalence selected by its action on original smooth sections. -/
def sobolevEquiv (s : ℝ) : L.SobolevSpace s ≃L[ℂ] K.SobolevSpace s :=
  Classical.choose (L.existsUnique_sobolevEquiv K s).exists

/-- Presentation comparison keeps the same original smooth section. -/
theorem sobolevEquiv_smoothToSobolev (s : ℝ) (u : A.smoothSections) :
    L.sobolevEquiv K s (L.smoothToSobolev s u) = K.smoothToSobolev s u := by
  /- Apply the dense-subspace specification of the selected equivalence. -/
  exact (Classical.choose_spec (L.existsUnique_sobolevEquiv K s).exists) u

/-- The actual smooth inclusion extends uniquely when the real Sobolev order decreases. -/
theorem existsUnique_sobolevInclusion (s t : ℝ) (hst : t ≤ s) :
    ∃! J : L.SobolevSpace s →L[ℂ] L.SobolevSpace t,
      ∀ u : A.smoothSections,
        J (L.smoothToSobolev s u) = L.smoothToSobolev t u := by
  /- Stage 1: in every selected chart use the Euclidean multiplier
  (1+|xi|²)^((t-s)/2), whose L² operator norm is at most one. These coordinate
  maps preserve the represented localized distributions at the two orders.
  Stage 2: sum the squared local bounds and extend from smooth sections to the
  closed ranges. The image lands in the target closed range by approximation.
  Uniqueness follows from density of the original smooth section image. -/
  classical
  choose J hJnorm hJdist using fun j : Fin L.size ↦
    exists_sobolev_inclusion n (A.rank (L.frameIndex j)) s t hst
  -- Every chart uses its own original rank, including zero-rank charts.
  have hcontract (j : Fin L.size)
      (f : MeasureTheory.Lp (EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
      ‖J j f‖ ≤ ‖f‖ := by
    calc
      ‖J j f‖ ≤ ‖J j‖ * ‖f‖ := (J j).le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (hJnorm j) (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  let T : L.SobolevCoordinates →ₗ[ℂ] L.SobolevCoordinates :=
    { toFun := fun f ↦ WithLp.toLp 2 (fun j ↦ J j (f j))
      map_add' := by
        intro f₁ f₂
        apply (WithLp.ext_iff 2).mpr
        funext j
        exact (J j).map_add (f₁ j) (f₂ j)
      map_smul' := by
        intro c f
        apply (WithLp.ext_iff 2).mpr
        funext j
        exact (J j).map_smul c (f j) }
  have hT (f : L.SobolevCoordinates) : ‖T f‖ ≤ 1 * ‖f‖ := by
    have hsq : ‖T f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (hcontract j (f j)) 2
    nlinarith [norm_nonneg (T f), norm_nonneg f]
  let Tc : L.SobolevCoordinates →L[ℂ] L.SobolevCoordinates := T.mkContinuous 1 hT
  -- All coordinates still represent the same actual localized smooth section.
  have hsmooth (u : A.smoothSections) :
      Tc (L.sobolevCoordinates s u) = L.sobolevCoordinates t u := by
    apply (WithLp.ext_iff 2).mpr
    funext j
    apply besselRealization_injective n (A.rank (L.frameIndex j)) t
    change besselRealization n (A.rank (L.frameIndex j)) t
        (J j (schwartzSobolevCoordinate s (L.localize j u))) =
      besselRealization n (A.rank (L.frameIndex j)) t
        (schwartzSobolevCoordinate t (L.localize j u))
    rw [hJdist, besselRealization_schwartzSobolevCoordinate,
      besselRealization_schwartzSobolevCoordinate]
  -- Pass from smooth coordinate ranges to their original closed Hilbert subspaces.
  have hmaps : ∀ x ∈ (L.sobolevCoordinates s).range.topologicalClosure,
      Tc x ∈ (L.sobolevCoordinates t).range.topologicalClosure := by
    change (L.sobolevCoordinates s).range.topologicalClosure ≤
      ((L.sobolevCoordinates t).range.topologicalClosure).comap Tc.toLinearMap
    apply (L.sobolevCoordinates s).range.topologicalClosure_minimal
    · rintro x ⟨u, rfl⟩
      change Tc (L.sobolevCoordinates s u) ∈
        (L.sobolevCoordinates t).range.topologicalClosure
      rw [hsmooth]
      exact (L.sobolevCoordinates t).range.le_topologicalClosure ⟨u, rfl⟩
    · exact (L.sobolevCoordinates t).range.isClosed_topologicalClosure.preimage Tc.continuous
  let S : L.SobolevSpace s →L[ℂ] L.SobolevSpace t := Tc.restrict hmaps
  have hS (u : A.smoothSections) :
      S (L.smoothToSobolev s u) = L.smoothToSobolev t u := by
    apply Subtype.ext
    exact hsmooth u
  refine ⟨S, hS, ?_⟩
  -- Density fixes this bounded extension without changing the supplied presentation.
  intro R hR
  apply DFunLike.coe_injective
  apply (L.denseRange_smoothToSobolev s).equalizer R.continuous S.continuous
  funext u
  exact (hR u).trans (hS u).symm

/-- The natural order-decreasing map between the specified Sobolev completions. -/
def sobolevInclusion (s t : ℝ) (hst : t ≤ s) :
    L.SobolevSpace s →L[ℂ] L.SobolevSpace t :=
  Classical.choose (L.existsUnique_sobolevInclusion s t hst).exists

/-- The order-decreasing inclusion preserves the represented smooth section. -/
theorem sobolevInclusion_smoothToSobolev (s t : ℝ) (hst : t ≤ s)
    (u : A.smoothSections) :
    L.sobolevInclusion s t hst (L.smoothToSobolev s u) = L.smoothToSobolev t u := by
  /- Use the defining specification of the chosen continuous linear extension. -/
  exact (Classical.choose_spec (L.existsUnique_sobolevInclusion s t hst).exists) u

/-- The natural Sobolev inclusion is injective for all real orders. -/
theorem sobolevInclusion_injective (s t : ℝ) (hst : t ≤ s) :
    Function.Injective (L.sobolevInclusion s t hst) := by
  /- Stage 1: smooth compatibility and continuity show, in each selected chart,
  that the inclusion preserves the actual Bessel distribution realization.
  Stage 2: equal output vectors therefore give equal source distributions.
  Injectivity of the Euclidean Bessel realization in that chart's finite rank
  recovers the source Hilbert coordinates, hence the two original vectors. -/
  -- Continuity extends equality of each actual localized distribution from smooth inputs.
  have hlocal (j : Fin L.size) (w : L.SobolevSpace s) :
      L.localDistribution t j (L.sobolevInclusion s t hst w) =
        L.localDistribution s j w := by
    have hcont (a : ℝ) : Continuous (L.localDistribution a j) :=
      (besselRealization n (A.rank (L.frameIndex j)) a).continuous.comp
        ((PiLp.proj (𝕜 := ℂ) 2 _ j).continuous.comp continuous_subtype_val)
    refine (L.denseRange_smoothToSobolev s).induction_on w
      (isClosed_eq ((hcont t).comp (L.sobolevInclusion s t hst).continuous) (hcont s)) ?_
    intro v
    rw [L.sobolevInclusion_smoothToSobolev, L.localDistribution_smoothToSobolev,
      L.localDistribution_smoothToSobolev]
  intro u v huv
  apply Subtype.ext
  apply (WithLp.ext_iff 2).mpr
  funext j
  -- Bessel injectivity at that chart's rank recovers the original source tuple.
  apply besselRealization_injective n (A.rank (L.frameIndex j)) s
  change L.localDistribution s j u = L.localDistribution s j v
  rw [← hlocal j u, ← hlocal j v, huv]

/-- Rellich: a strict loss of Sobolev order gives a compact inclusion. -/
theorem isCompactOperator_sobolevInclusion (s t : ℝ) (hst : t < s) :
    IsCompactOperator (L.sobolevInclusion s t hst.le) := by
  /- Stage 1: for each chart the unit ball has Bessel coordinates of norm at most
  one, and its localized distributions are supported in the fixed compact image
  of the cutoff support. Apply Euclidean Rellich in that chart's actual rank.
  Stage 2: take the finite product of the resulting compact closures. The actual
  inclusion agrees with these coordinate inclusions because both preserve the
  same distributions. Its range lies in the target closed Sobolev subspace.
  Stage 3: intersect the compact closure in the finite product with that closed
  subspace. Thus the image of the unit ball has compact closure in the target. -/
  classical
  choose J hJnorm hJ using fun j : Fin L.size ↦
    exists_sobolev_inclusion n (A.rank (L.frameIndex j)) s t hst.le
  let K (j : Fin L.size) := (L.chart j) '' tsupport (L.cutoff j)
  have hK (j : Fin L.size) : IsCompact (K j) :=
    (L.compact_support j).image_of_continuousOn
      ((L.chart j).continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  let C (j : Fin L.size) := closure (J j '' {f | ‖f‖ ≤ 1 ∧
    IsSupportedIn (besselRealization n (A.rank (L.frameIndex j)) s f) (K j)})
  have hC (j : Fin L.size) : IsCompact (C j) :=
    rellich_compact_inclusion n (A.rank (L.frameIndex j)) s t hst (K j) (hK j) (J j) (hJ j)
  -- The finite coordinate product is compact in the exact original L2 sum topology.
  let e := PiLp.homeomorph 2 (fun j : Fin L.size ↦ MeasureTheory.Lp
    (EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) 2
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
  have hprod : IsCompact (e ⁻¹' Set.pi Set.univ C) :=
    e.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi hC)
  have htarget : IsClosed ((L.sobolevCoordinates t).range.topologicalClosure :
      Set L.SobolevCoordinates) := (L.sobolevCoordinates t).range.isClosed_topologicalClosure
  have hcompact : IsCompact ((Subtype.val : L.SobolevSpace t → L.SobolevCoordinates) ⁻¹'
      (e ⁻¹' Set.pi Set.univ C)) :=
    htarget.isClosedEmbedding_subtypeVal.isCompact_preimage hprod
  -- Bessel injectivity compares the given global inclusion with these same local maps.
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (L.sobolevInclusion s t hst.le).toLinearMap zero_lt_one).mpr
  refine ⟨_, hcompact, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  change ∀ j ∈ (Set.univ : Set (Fin L.size)),
    ((L.sobolevInclusion s t hst.le u).val j) ∈ C j
  intro j _
  have hcoord : (L.sobolevInclusion s t hst.le u).val j = J j (u.val j) := by
    apply besselRealization_injective n (A.rank (L.frameIndex j)) t
    change L.localDistribution t j (L.sobolevInclusion s t hst.le u) = _
    rw [hJ]
    change L.localDistribution t j (L.sobolevInclusion s t hst.le u) =
      L.localDistribution s j u
    have hcont (a : ℝ) : Continuous (L.localDistribution a j) :=
      (besselRealization n (A.rank (L.frameIndex j)) a).continuous.comp
        ((PiLp.proj (𝕜 := ℂ) 2 _ j).continuous.comp continuous_subtype_val)
    refine (L.denseRange_smoothToSobolev s).induction_on u
      (isClosed_eq ((hcont t).comp (L.sobolevInclusion s t hst.le).continuous) (hcont s)) ?_
    intro v
    rw [L.sobolevInclusion_smoothToSobolev, L.localDistribution_smoothToSobolev,
      L.localDistribution_smoothToSobolev]
  rw [hcoord]
  apply subset_closure
  refine ⟨u.val j, ⟨?_, L.isSupportedIn_localDistribution s j u⟩, rfl⟩
  exact (PiLp.norm_apply_le u.val j).trans (by simpa using hu)

end AtlasBundlePresentation

end AtiyahSinger

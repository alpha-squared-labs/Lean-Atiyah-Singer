/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DualSobolevBridge
public import AtiyahSinger.Analysis.HermitianMetricPseudodifferentialAdjoint

import AtiyahSinger.Analysis.SobolevMultiplication

/-!
# Geometric Sobolev duality for explicit metrics

Public module ID: M0728.

D02/A07: extend actual metric dual sections to the existing Sobolev completions,
then compose with the bilinear continuous-dual equivalence. Sources: SG III.2.15
and III.5 (5.1). These metric-data bridges preserve opposite real orders and do
not identify the geometric formal adjoint with an arbitrary Sobolev Hilbert adjoint.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hM hT2 hSC hE

namespace SmoothHermitianMetric

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The actual conjugate-linear metric map extends uniquely at every real order. -/
theorem existsUnique_sobolevDual (s : ℝ) :
    ∃! T : A.SobolevSpace s ≃L⋆[ℂ] A.DualSobolevSpace s,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) = A.dualSmoothToSobolev s (h.dualSectionsEquiv u) := by
  open Set in
  open scoped SchwartzMap FourierTransform ENNReal Matrix.Norms.Elementwise in
  /- In local coordinates the map conjugates vector coefficients and
  multiplies by the smooth Gram matrix. Conjugation preserves radial Bessel
  norms. Compactly localized Gram and inverse Gram multipliers are bounded
  at every real order. Extend these inverse maps by density to obtain the
  unique continuous semilinear equivalence on the two actual completions. -/
  classical
  -- Conjugation reverses Fourier frequency and preserves the radial Bessel norm.
  have hconjugation :
      ∃ C : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℝ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        (∀ u x i, C u x i = conj (u x i)) ∧
        ∀ t u, ‖schwartzSobolevCoordinate t (C u)‖ =
          ‖schwartzSobolevCoordinate t u‖ := by
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let c : V →L[ℝ] V :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (fun i ↦ Complex.conjCLE.toContinuousLinearMap.comp
          ((EuclideanSpace.proj i).restrictScalars ℝ)))
    have hc (v : V) (i : Fin r) : c v i = conj (v i) := rfl
    have hcc (v : V) : c (c v) = v := by
      ext i
      simp only [hc, starRingEnd_self_apply]
    let e : V ≃L[ℝ] V :=
      { toFun := c
        invFun := c
        left_inv := hcc
        right_inv := hcc
        map_add' := c.map_add
        map_smul' := c.map_smul
        continuous_toFun := c.continuous
        continuous_invFun := c.continuous }
    let C : 𝓢(X, V) →L[ℝ] 𝓢(X, V) := SchwartzMap.postcompCLM c
    have hC (u : 𝓢(X, V)) (x : X) : C u x = c (u x) := rfl
    have hcnorm (v : V) : ‖c v‖ = ‖v‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [hc, Complex.norm_conj]
    have hfourier (u : 𝓢(X, V)) (ξ : X) : 𝓕 (C u) ξ = c (𝓕 u (-ξ)) := by
      change 𝓕 (fun x ↦ c (u x)) ξ = e (𝓕 (u : X → V) (-ξ))
      simp only [Real.fourier_eq, inner_neg_right, neg_neg]
      rw [← e.integral_comp_comm]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply PiLp.ext
      intro i
      change (Real.fourierChar (-inner ℝ x ξ) : ℂ) * conj (u x i) =
        conj ((Real.fourierChar (inner ℝ x ξ) : ℂ) * u x i)
      rw [map_mul, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
    refine ⟨C, fun _ _ _ ↦ rfl, ?_⟩
    intro s u
    let w : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)
    have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
    have hnorm (v : 𝓢(X, V)) : ‖schwartzSobolevCoordinate s v‖ =
        ‖(SchwartzMap.smulLeftCLM V w (𝓕 v)).toLp 2‖ := by
      unfold schwartzSobolevCoordinate
      rw [← SchwartzMap.norm_fourier_toL2_eq, SchwartzMap.fourierMultiplierCLM_apply,
        FourierTransform.fourier_fourierInv_eq]
    rw [hnorm, hnorm]
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num),
      SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    congr 1
    have hpoint (ξ : X) : ‖SchwartzMap.smulLeftCLM V w (𝓕 (C u)) ξ‖ =
        ‖SchwartzMap.smulLeftCLM V w (𝓕 u) (-ξ)‖ := by
      simp only [SchwartzMap.smulLeftCLM_apply_apply hw, hfourier, norm_smul, hcnorm]
      simp [w]
    simp_rw [hpoint]
    exact integral_neg_eq_self
      (fun ξ : X ↦ ‖SchwartzMap.smulLeftCLM V w (𝓕 u) ξ‖ ^ (2 : ℝ≥0∞).toReal)
      (volume : Measure X)
  obtain ⟨C, hC, hCnorm⟩ := hconjugation
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  -- Each fixed chart uses the actual Gram matrix and its smooth inverse.
  have hlocal (j : Fin A.size) : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖schwartzSobolevCoordinate s (A.localizeDual j (h.dualSectionsEquiv u))‖ ≤
            a * ‖schwartzSobolevCoordinate s (A.localize j u)‖ ∧
        ‖schwartzSobolevCoordinate s (A.localize j u)‖ ≤
            b * ‖schwartzSobolevCoordinate s (A.localizeDual j (h.dualSectionsEquiv u))‖ := by
    let c := A.chart j
    let e := A.frame j
    let := A.frame_mem_atlas j
    let U := c.target ∩ c.symm ⁻¹' e.baseSet
    have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target e.open_baseSet
    let K := c '' tsupport (A.cutoff j)
    have hK : IsCompact K := (A.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
    have hKU : K ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      have hs := (A.support_subset j hx).1
      exact ⟨c.map_source hs, by
        change c.symm (c x) ∈ e.baseSet
        rw [c.left_inv hs]
        exact (A.support_subset j hx).2⟩
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo hK.isClosed hKO
    have hηsupport : tsupport η = closure O := congrArg closure hsη
    have hcη : HasCompactSupport η := by simpa [HasCompactSupport, hηsupport] using hOc
    have hηU : tsupport η ⊆ U := by rwa [hηsupport]
    have hηone (z : X) (hz : z ∈ K) : η z = 1 := (honeη z).mp hz
    let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (V →L[ℂ] V) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : X) : V →L[ℂ] V := toOp (h.gramMatrix e (c.symm z))
    have hG (z : X) (hz : z ∈ U) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
          (A.chart_mem_atlas j)) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro k
      exact (((h.contMDiffOn_gram e i k).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hequiv (z : X) (hz : z ∈ U) :
        ∃ L : V ≃L[ℂ] V, L.toContinuousLinearMap = G z := by
      let P := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
      have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
        (h.isUnit_det_gramMatrix e (c.symm z) hz.2)
      let L := (LinearEquiv.ofBijective (h.gramMatrix e (c.symm z)).mulVecLin
        ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
          Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
      refine ⟨P.trans (L.trans P.symm), ?_⟩
      ext v i
      rfl
    have hGi : ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) U := by
      intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    let H := cutoffMatrix η G
    let I := cutoffMatrix η (fun z ↦ (G z).inverse)
    have hH : ContDiff ℝ ∞ H :=
      contDiff_cutoffMatrix U hU G (fun z hz ↦ (hG z hz).contDiffWithinAt) η hη hηU
    have hI : ContDiff ℝ ∞ I :=
      contDiff_cutoffMatrix U hU (fun z ↦ (G z).inverse) hGi η hη hηU
    have hcH : HasCompactSupport H := hasCompactSupport_cutoffMatrix η G hcη
    have hcI : HasCompactSupport I :=
      hasCompactSupport_cutoffMatrix η (fun z ↦ (G z).inverse) hcη
    let T := matrixMultiplierCLM H hH hcH
    let R := matrixMultiplierCLM I hI hcI
    -- Testing against frame basis vectors identifies the precise matrix convention.
    have hcoeff (u : smoothSections (n := n) (r := r) E) (z : X) (hz : z ∈ U)
        (i : Fin r) :
        conj (dualSectionInFrame E e (h.dualSectionsEquiv u).val (c.symm z) i) =
          G z ((e ⟨c.symm z, u.val (c.symm z)⟩).2) i := by
      have htest := congrArg (starRingEnd ℂ)
        (h.dualSectionsEquiv_apply u (c.symm z)
          (e.symmL ℂ (c.symm z) (EuclideanSpace.single i 1)))
      simp only [pairing, (h.toCore (c.symm z)).conj_inner_symm] at htest
      change _ = h.pairing (c.symm z)
        (e.symmL ℂ (c.symm z) (EuclideanSpace.single i 1)) (u.val (c.symm z)) at htest
      rw [h.pairing_eq_gramMatrix e (c.symm z) hz.2] at htest
      have hbase : (e ⟨c.symm z,
          e.symmL ℂ (c.symm z) (EuclideanSpace.single i 1)⟩).2 =
            EuclideanSpace.single i 1 := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 _
      change conj ((h.dualSectionsEquiv u).val (c.symm z)
        (e.symmL ℂ (c.symm z) (EuclideanSpace.single i 1))) =
          ∑ k, h.gramMatrix e (c.symm z) i k * (e ⟨c.symm z, u.val (c.symm z)⟩).2 k
      simpa [hbase] using htest
    have hzero (u : smoothSections (n := n) (r := r) E) (z : X) (hz : z ∉ K) :
        A.localize j u z = 0 ∧ A.localizeDual j (h.dualSectionsEquiv u) z = 0 := by
      change A.localizedFunction j u z = 0 ∧
        A.localizedDualFunction j (h.dualSectionsEquiv u) z = 0
      by_cases hzt : z ∈ c.target
      · have hcut : c.symm z ∉ tsupport (A.cutoff j) := by
          intro hx
          exact hz ⟨c.symm z, hx, c.right_inv hzt⟩
        simp [SmoothBundlePresentation.localizedFunction,
          SmoothBundlePresentation.localizedDualFunction, c,
          image_eq_zero_of_notMem_tsupport hcut]
      · simp [SmoothBundlePresentation.localizedFunction,
          SmoothBundlePresentation.localizedDualFunction, c, hzt]
    have hforward (u : smoothSections (n := n) (r := r) E) :
        C (A.localizeDual j (h.dualSectionsEquiv u)) = T (A.localize j u) := by
      apply SchwartzMap.ext
      intro z
      change _ = matrixMultiplierCLM H hH hcH (A.localize j u) z
      rw [matrixMultiplierCLM_apply]
      by_cases hz : z ∈ K
      · have hzU := hKU hz
        have hHz : H z = G z := by simp [H, cutoffMatrix, hηone z hz]
        rw [hHz]
        change _ = G z (A.localizedFunction j u z)
        rw [SmoothBundlePresentation.localizedFunction, ite_eq_left hzU.1, map_smul]
        apply PiLp.ext
        intro i
        rw [hC]
        change conj ((A.localizedDualFunction j (h.dualSectionsEquiv u) z) i) = _
        have hzt : z ∈ (A.chart j).target := hzU.1
        rw [SmoothBundlePresentation.localizedDualFunction, ite_eq_left hzt]
        change conj ((A.cutoff j (c.symm z) : ℂ) *
          dualSectionInFrame E e (h.dualSectionsEquiv u).val (c.symm z) i) =
            (A.cutoff j (c.symm z) : ℂ) *
              G z ((e ⟨c.symm z, u.val (c.symm z)⟩).2) i
        rw [map_mul, Complex.conj_ofReal, hcoeff u z hzU i]
      · obtain ⟨hv, hα⟩ := hzero u z hz
        rw [hv, map_zero]
        apply PiLp.ext
        intro i
        rw [hC, hα]
        simp
    have hreverse (u : smoothSections (n := n) (r := r) E) :
        R (C (A.localizeDual j (h.dualSectionsEquiv u))) = A.localize j u := by
      rw [hforward]
      apply SchwartzMap.ext
      intro z
      change matrixMultiplierCLM I hI hcI (T (A.localize j u)) z = _
      rw [matrixMultiplierCLM_apply]
      change I z (matrixMultiplierCLM H hH hcH (A.localize j u) z) = _
      rw [matrixMultiplierCLM_apply]
      by_cases hz : z ∈ K
      · obtain ⟨L, hL⟩ := hequiv z (hKU hz)
        have hHz : H z = G z := by simp [H, cutoffMatrix, hηone z hz]
        have hIz : I z = (G z).inverse := by simp [I, cutoffMatrix, hηone z hz]
        rw [hHz, hIz, ← hL, ContinuousLinearMap.inverse_equiv]
        exact L.symm_apply_apply _
      · rw [(hzero u z hz).1, map_zero, map_zero]
    obtain ⟨a, ha, hbound⟩ := exists_norm_matrixMultiplier_sobolev_le H hH hcH s
    obtain ⟨b, hb, hinvbound⟩ := exists_norm_matrixMultiplier_sobolev_le I hI hcI s
    refine ⟨a, b, ha, hb, ?_⟩
    intro u
    constructor
    · rw [← hCnorm s, hforward]
      exact hbound (A.localize j u)
    · rw [← hreverse u]
      exact (hinvbound (C (A.localizeDual j (h.dualSectionsEquiv u)))).trans_eq
        (congrArg (b * ·) (hCnorm s _))
  choose a b ha hb hlocalbound using hlocal
  -- Finite chart sums turn both local estimates into bounds on the original completions.
  have hnormsum (v : A.SobolevCoordinates) : ‖v‖ ≤ ∑ j, ‖v j‖ := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun (j : Fin A.size) _ ↦ norm_nonneg (v j))
    rw [← PiLp.norm_sq_eq_of_L2] at hsq
    have hnonneg : 0 ≤ ∑ j, ‖v j‖ := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
    nlinarith [norm_nonneg v]
  have hforwardBound (u : smoothSections (n := n) (r := r) E) :
      ‖A.dualSmoothToSobolev s (h.dualSectionsEquiv u)‖ ≤
        (∑ j, a j) * ‖A.smoothToSobolev s u‖ := by
    calc
      _ ≤ ∑ j, ‖schwartzSobolevCoordinate s
          (A.localizeDual j (h.dualSectionsEquiv u))‖ :=
        hnormsum (A.dualSobolevCoordinates s (h.dualSectionsEquiv u))
      _ ≤ ∑ j, a j * ‖A.smoothToSobolev s u‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (hlocalbound j u).1.trans
          (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (A.sobolevCoordinates s u) j) (ha j))
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hreverseBound (α : smoothDualSections (n := n) (r := r) E) :
      ‖A.smoothToSobolev s (h.dualSectionsEquiv.symm α)‖ ≤
        (∑ j, b j) * ‖A.dualSmoothToSobolev s α‖ := by
    obtain ⟨u, rfl⟩ := h.dualSectionsEquiv.surjective α
    rw [h.dualSectionsEquiv.symm_apply_apply]
    calc
      _ ≤ ∑ j, ‖schwartzSobolevCoordinate s (A.localize j u)‖ :=
        hnormsum (A.sobolevCoordinates s u)
      _ ≤ ∑ j, b j * ‖A.dualSmoothToSobolev s (h.dualSectionsEquiv u)‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (hlocalbound j u).2.trans (mul_le_mul_of_nonneg_left
          (PiLp.norm_apply_le (A.dualSobolevCoordinates s (h.dualSectionsEquiv u)) j) (hb j))
      _ = _ := (Finset.sum_mul _ _ _).symm
  let T : A.SobolevSpace s →L⋆[ℂ] A.DualSobolevSpace s :=
    ((A.dualSmoothToSobolev s).comp h.dualSectionsEquiv.toLinearMap).extendOfNorm
      (A.smoothToSobolev s)
  let R : A.DualSobolevSpace s →L⋆[ℂ] A.SobolevSpace s :=
    ((A.smoothToSobolev s).comp h.dualSectionsEquiv.symm.toLinearMap).extendOfNorm
      (A.dualSmoothToSobolev s)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s u) = A.dualSmoothToSobolev s (h.dualSectionsEquiv u) :=
    LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s) ⟨_, hforwardBound⟩ u
  have hR (α : smoothDualSections (n := n) (r := r) E) :
      R (A.dualSmoothToSobolev s α) = A.smoothToSobolev s (h.dualSectionsEquiv.symm α) :=
    LinearMap.extendOfNorm_eq (A.denseRange_dualSmoothToSobolev s) ⟨_, hreverseBound⟩ α
  -- The smooth inverse laws persist by density, so these extensions form an equivalence.
  have hRT : Function.LeftInverse R T := by
    intro u
    refine (A.denseRange_smoothToSobolev s).induction_on u
      (isClosed_eq (R.continuous.comp T.continuous) continuous_id) ?_
    intro v
    rw [hT, hR, h.dualSectionsEquiv.symm_apply_apply]
  have hTR : Function.RightInverse R T := by
    intro α
    refine (A.denseRange_dualSmoothToSobolev s).induction_on α
      (isClosed_eq (T.continuous.comp R.continuous) continuous_id) ?_
    intro β
    rw [hR, hT, h.dualSectionsEquiv.apply_symm_apply]
  let e : A.SobolevSpace s ≃L⋆[ℂ] A.DualSobolevSpace s :=
    { toFun := T
      invFun := R
      left_inv := hRT
      right_inv := hTR
      map_add' := T.map_add
      map_smul' := T.map_smulₛₗ
      continuous_toFun := T.continuous
      continuous_invFun := R.continuous }
  refine ⟨e, hT, ?_⟩
  intro f hf
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer f.continuous e.continuous
  funext u
  exact (hf u).trans (hT u).symm

/-- The same-order conjugate-linear metric identification of primal and dual Sobolev spaces. -/
def sobolevDual (s : ℝ) : A.SobolevSpace s ≃L⋆[ℂ] A.DualSobolevSpace s :=
  Classical.choose (h.existsUnique_sobolevDual A s).exists

/-- The Sobolev metric identification keeps the exact smooth dual section. -/
theorem sobolevDual_smooth (s : ℝ) (u : smoothSections (n := n) (r := r) E) :
    h.sobolevDual A s (A.smoothToSobolev s u) =
      A.dualSmoothToSobolev s (h.dualSectionsEquiv u) := by
  /- Read off the chosen equivalence's specifying property. It retains
  the geometric fiberwise metric dual and does not select an unrelated Riesz
  identification for the presentation's auxiliary Hilbert norm. -/
  exact (h.existsUnique_sobolevDual A s).exists.choose_spec u

/-- The metric-change multiplier on a fixed Sobolev model, built from the two dual maps. -/
def sobolevChange (k : SmoothHermitianMetric (n := n) (r := r) E) (s : ℝ) :
    A.SobolevSpace s ≃L[ℂ] A.SobolevSpace s :=
  (k.sobolevDual A s).trans (h.sobolevDual A s).symm

/-- Sobolev metric change extends the actual positive fiber multiplier. -/
theorem sobolevChange_smooth (k : SmoothHermitianMetric (n := n) (r := r) E)
    (s : ℝ) (u : smoothSections (n := n) (r := r) E) :
    h.sobolevChange A k s (A.smoothToSobolev s u) =
      A.smoothToSobolev s (h.changeSections k u) := by
  /- Apply h's Sobolev dual to both sides. The smooth-input formulas
  and dualSectionsEquiv_change identify the images; injectivity cancels that
  map. The two conjugate-linear factors compose to a complex-linear multiplier. -/
  apply (h.sobolevDual A s).injective
  change (h.sobolevDual A s)
    ((h.sobolevDual A s).symm ((k.sobolevDual A s) (A.smoothToSobolev s u))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, k.sobolevDual_smooth,
    h.sobolevDual_smooth, h.dualSectionsEquiv_change k u]

/-- The Sobolev change for identical metrics is the identity. -/
theorem sobolevChange_self (s : ℝ) :
    h.sobolevChange A h s = ContinuousLinearEquiv.refl ℂ (A.SobolevSpace s) := by
  /- The defining composite is a continuous semilinear equivalence
  followed by its inverse. Its underlying function is the identity on every
  completed vector, not only on the dense smooth subspace. -/
  apply DFunLike.ext
  intro u
  exact (h.sobolevDual A s).symm_apply_apply u

/-- Sobolev metric changes retain the noncommutative fiber composition order. -/
theorem sobolevChange_trans (k l : SmoothHermitianMetric (n := n) (r := r) E) (s : ℝ) :
    h.sobolevChange A l s = (k.sobolevChange A l s).trans (h.sobolevChange A k s) := by
  /- Expand both changes as metric dual followed by inverse metric dual.
  The two middle k maps cancel. This yields B_hl=B_hk B_kl without exchanging
  the factors, a property specific to these metric comparison multipliers. -/
  apply DFunLike.ext
  intro u
  change (h.sobolevDual A s).symm ((l.sobolevDual A s) u) =
    (h.sobolevDual A s).symm ((k.sobolevDual A s)
      ((k.sobolevDual A s).symm ((l.sobolevDual A s) u)))
  rw [ContinuousLinearEquiv.apply_symm_apply]

variable [MeasurableSpace M] [hBorel : BorelSpace M] [hC : CompactSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hBorel hC hμ

/-- Opposite-order Hermitian duality formed from actual metric duality and evaluation. -/
def sobolevDuality (s : ℝ) :
    A.SobolevSpace (-s) ≃L⋆[ℂ] StrongDual ℂ (A.SobolevSpace s) :=
  (h.sobolevDual A (-s)).trans (A.sobolevEvaluationDuality μ s)

/-- Evaluate the explicit-metric geometric Sobolev pairing. -/
def sobolevPairing (s : ℝ) (v : A.SobolevSpace (-s)) (u : A.SobolevSpace s) : ℂ :=
  h.sobolevDuality A μ s v u

/-- The completed Hermitian pairing equals the original integral on smooth inputs. -/
theorem sobolevPairing_smooth (s : ℝ) (v u : smoothSections (n := n) (r := r) E) :
    h.sobolevPairing A μ s (A.smoothToSobolev (-s) v) (A.smoothToSobolev s u) =
      h.sectionPairing μ v u := by
  /- First use the Sobolev metric map's smooth-input formula. The
  evaluation pairing becomes the smooth covector integral, which equals
  the h Hermitian integral by the actual metric-dual evaluation identity. -/
  change A.sobolevEvaluationPairing μ s
    (h.sobolevDual A (-s) (A.smoothToSobolev (-s) v)) (A.smoothToSobolev s u) = _
  rw [h.sobolevDual_smooth, A.sobolevEvaluationPairing_smooth]
  exact h.dualSectionPairing_dualSectionsEquiv μ v u

end SmoothHermitianMetric

variable [MeasurableSpace M] [hBorel : BorelSpace M] [hC : CompactSpace M]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hBorel hC hμ

variable {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hF

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The actual adjoint PDO extended from H^{m-s}(F) to H^{-s}(E). -/
def metricSobolevAdjoint (s : ℝ) :
    B.SobolevSpace (-(s - m)) →L[ℂ] A.SobolevSpace (-s) := by
  have hs : -(s - m) - m = -s := by ring
  exact hs ▸ (P.metricFormalAdjoint h k).sobolevExtension B A (-(s - m))

/-- The opposite-order map extends exactly the smooth formal adjoint. -/
theorem metricSobolevAdjoint_smooth (s : ℝ) (v : smoothSections (n := n) (r := q) F) :
    P.metricSobolevAdjoint h k A B s (B.smoothToSobolev (-(s - m)) v) =
      A.smoothToSobolev (-s) ((P.metricFormalAdjoint h k).toLinearMap v) := by
  /- Apply the PDO smooth-extension identity to the actual adjoint and
  transport its target across -(s-m)-m=-s. No new Hilbert adjoint is substituted
  for that geometric smooth-section operator. -/
  have htransport (t : ℝ) (ht : -(s - m) - m = t) :
      (ht ▸ (P.metricFormalAdjoint h k).sobolevExtension B A (-(s - m)))
          (B.smoothToSobolev (-(s - m)) v) =
        A.smoothToSobolev t ((P.metricFormalAdjoint h k).toLinearMap v) := by
    subst t
    exact (P.metricFormalAdjoint h k).sobolevExtension_smoothToSobolev B A (-(s - m)) v
  exact htransport (-s) (by ring)

/-- The bilinear Sobolev transpose is intertwined by explicit metric identifications. -/
theorem sobolevTranspose_metric (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    P.sobolevTranspose A B s (k.sobolevDual B (-(s - m)) v) =
      h.sobolevDual A (-s) (P.metricSobolevAdjoint h k A B s v) := by
  /- On dense smooth inputs use formalTranspose_metric and both
  smooth-extension formulas. Both sides are continuous conjugate-linear maps
  in v, so density extends the exact equality to the Sobolev completion. -/
  refine (B.denseRange_smoothToSobolev (-(s - m))).induction_on v
    (isClosed_eq ((P.sobolevTranspose A B s).continuous.comp
      (k.sobolevDual B (-(s - m))).continuous)
      ((h.sobolevDual A (-s)).continuous.comp
        (P.metricSobolevAdjoint h k A B s).continuous)) ?_
  intro w
  rw [k.sobolevDual_smooth, P.sobolevTranspose_smooth,
    P.metricSobolevAdjoint_smooth, h.sobolevDual_smooth]
  rw [P.formalTranspose_metric, LinearEquiv.symm_apply_apply]

/-- The geometric adjoint represents precomposition on the actual continuous dual. -/
theorem sobolevDuality_metricAdjoint (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    h.sobolevDuality A μ s (P.metricSobolevAdjoint h k A B s v) =
      (k.sobolevDuality B μ (s - m) v).comp (P.sobolevExtension A B s) := by
  /- Insert the metric identifications into the bilinear transpose
  duality diagram. The preceding intertwining equality converts its output
  to the geometric adjoint; the two definitions of metric duality give exactly
  precomposition by P's existing critical-order Sobolev realization. -/
  change A.sobolevEvaluationDuality μ s
    (h.sobolevDual A (-s) (P.metricSobolevAdjoint h k A B s v)) = _
  rw [← P.sobolevTranspose_metric]
  exact P.sobolevEvaluationDuality_transpose A B s (k.sobolevDual B (-(s - m)) v)

/-- Weak adjoint zeros are exactly continuous annihilators of the Sobolev range. -/
theorem metricSobolevAdjoint_eq_zero_iff (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    P.metricSobolevAdjoint h k A B s v = 0 ↔
      ∀ u : A.SobolevSpace s,
        k.sobolevPairing B μ (s - m) v (P.sobolevExtension A B s u) = 0 := by
  /- Injectivity of the source metric duality detects a zero output.
  Substitute the precomposition diagram and test the resulting continuous
  functional on every u. Range closedness and ellipticity are unnecessary. -/
  constructor
  · intro hv u
    change ((k.sobolevDuality B μ (s - m) v).comp (P.sobolevExtension A B s)) u = 0
    rw [← P.sobolevDuality_metricAdjoint h k A B s v, hv, map_zero]
    rfl
  · intro hv
    apply (h.sobolevDuality A μ s).injective
    rw [P.sobolevDuality_metricAdjoint, map_zero]
    apply ContinuousLinearMap.ext
    exact hv

/-- Changing the metrics conjugates the opposite-order Sobolev adjoint. -/
theorem metricSobolevAdjoint_change (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F) (s : ℝ) :
    P.metricSobolevAdjoint h' k' A B s =
      (h'.sobolevChange A h (-s)).toContinuousLinearMap.comp
        ((P.metricSobolevAdjoint h k A B s).comp
          (k.sobolevChange B k' (-(s - m))).toContinuousLinearMap) := by
  /- On smooth inputs use the exact section-map metric-change formula
  and the smooth action of each Sobolev multiplier. The displayed source and
  target orders match the reversed operator. Continuity and density extend
  equality to all vectors without treating the comparison as an isometry. -/
  apply DFunLike.coe_injective
  apply (B.denseRange_smoothToSobolev (-(s - m))).equalizer
    (P.metricSobolevAdjoint h' k' A B s).continuous
    ((h'.sobolevChange A h (-s)).toContinuousLinearMap.comp
      ((P.metricSobolevAdjoint h k A B s).comp
        (k.sobolevChange B k' (-(s - m))).toContinuousLinearMap)).continuous
  funext v
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, metricSobolevAdjoint_smooth,
    SmoothHermitianMetric.sobolevChange_smooth]
  exact congrArg (A.smoothToSobolev (-s))
    (congrArg (fun Q ↦ Q v) (P.metricFormalAdjoint_change h k h' k'))

end PseudodifferentialOperator

end AtiyahSinger

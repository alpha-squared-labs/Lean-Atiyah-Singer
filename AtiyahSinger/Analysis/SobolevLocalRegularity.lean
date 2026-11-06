/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LocalSobolev
public import AtiyahSinger.Analysis.SobolevMaps

import AtiyahSinger.Analysis.CkSections
import AtiyahSinger.Analysis.SobolevLocalization

/-!
# Local regularity of Sobolev sections

Public module ID: M0999.

D04/A01/A06: standard local Sobolev regularity, smoothness and singular support,
expressed through the existing localized distributions of a finite presentation.
The coordinate open set includes the chart source explicitly. Only Sobolev vectors
are inputs; no space of arbitrary distribution sections is postulated.

SG III.2.2, (2.17), and III.5.2(i) use precisely localization in bundle charts.
Local smoothness does not require extension to one global smooth section on a
proper open subset. On the whole base it recovers the actual smooth embedding.
The presentation is finite with compact cutoff supports, so its existence already
forces compactness of the base, even without a separate CompactSpace instance.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- Local H^t regularity of the section represented by a global H^s vector. -/
def MemSobolevOn (s : ℝ) (u : A.SobolevSpace s) (t : ℝ) (U : Set M) : Prop :=
  ∀ j : Fin A.size, AtiyahSinger.MemSobolevOn (A.localDistribution s j u) t
    ((A.chart j) '' (U ∩ (A.chart j).source))

/-- Smoothness on U, tested on the actual cutoff distributions in every presentation chart. -/
def IsSmoothOn (s : ℝ) (u : A.SobolevSpace s) (U : Set M) : Prop :=
  ∀ j : Fin A.size, IsSmoothDistributionOn (A.localDistribution s j u)
    ((A.chart j) '' (U ∩ (A.chart j).source))

/-- Points with no smooth open neighborhood for the represented Sobolev section. -/
def singularSupport (s : ℝ) (u : A.SobolevSpace s) : Set M :=
  {x | ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn s u U}

include hM hT2 hSC hE

/-- A global H^s section is locally H^s on every set. -/
theorem memSobolevOn_self (s : ℝ) (u : A.SobolevSpace s) (U : Set M) :
    A.MemSobolevOn s u s U := by
  /- Each localized distribution is the order-s Bessel realization of the
  corresponding L² coordinate. Its global H^s membership implies the local
  cutoff condition on any set, including the displayed coordinate image. -/
  intro j
  apply AtiyahSinger.memSobolevOn_of_memSobolev
  exact (memSobolev_iff_exists_besselRealization s _).mpr ⟨u.val j, rfl⟩

/-- Local Sobolev regularity restricts to a smaller subset of the base. -/
theorem memSobolevOn_mono (s t : ℝ) (u : A.SobolevSpace s) (U V : Set M)
    (hu : A.MemSobolevOn s u t U) (hVU : V ⊆ U) : A.MemSobolevOn s u t V := by
  /- Intersect hVU with each chart source and take its image. Apply the Euclidean
  restriction theorem to the same localized distribution in that chart. -/
  intro j
  apply (hu j).mono
  rintro z ⟨x, ⟨hxV, hxsource⟩, rfl⟩
  exact ⟨x, ⟨hVU hxV, hxsource⟩, rfl⟩

/-- Decreasing the local target order leaves the global input realization unchanged. -/
theorem memSobolevOn_of_le (s t l : ℝ) (u : A.SobolevSpace s) (U : Set M)
    (hu : A.MemSobolevOn s u t U) (hlt : l ≤ t) : A.MemSobolevOn s u l U := by
  /- Apply the Euclidean local H^t to H^l inclusion in every chart. The index s
  only specifies the given completed section, and is not changed to l or t. -/
  intro j
  exact (hu j).of_le hlt

/-- Subtraction preserves local regularity of sections in the same realization. -/
theorem memSobolevOn_sub (s t : ℝ) (u v : A.SobolevSpace s) (U : Set M)
    (hu : A.MemSobolevOn s u t U) (hv : A.MemSobolevOn s v t U) :
    A.MemSobolevOn s (u - v) t U := by
  /- Coordinate projections and Bessel realizations are linear, so localization
  commutes with subtraction. In each chart add the first locally H^t distribution
  to minus the second using the Euclidean addition and scalar multiplication rules. -/
  intro j
  -- Subtraction takes place in the original Sobolev completion before localization.
  have hlocal : A.localDistribution s j (u - v) =
      A.localDistribution s j u - A.localDistribution s j v := by
    change besselRealization n r s (u.val j - v.val j) = _
    exact map_sub (besselRealization n r s) (u.val j) (v.val j)
  rw [hlocal]
  simpa only [neg_one_smul, sub_eq_add_neg] using (hu j).add ((hv j).smul (-1))

/-- Every actual smooth section has locally smooth Sobolev realizations. -/
theorem isSmoothOn_smoothToSobolev (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) (U : Set M) (hU : IsOpen U) :
    A.IsSmoothOn s (A.smoothToSobolev s u) U := by
  /- The localized distribution identity gives the distribution of A.localize j u,
  an actual Schwartz function. It is smooth on the coordinate image of U intersected
  with the chart source. This image is open by the chart's open partial homeomorphism. -/
  intro j
  rw [A.localDistribution_smoothToSobolev]
  exact AtiyahSinger.isSmoothDistributionOn_schwartz (A.localize j u) _
    ((A.chart j).isOpen_image_of_subset_source
      (hU.inter (A.chart j).open_source) Set.inter_subset_right)

/-- Local smoothness of a Sobolev section is equivalent to membership in every local order. -/
theorem isSmoothOn_iff_forall_memSobolevOn (s : ℝ) (u : A.SobolevSpace s)
    (U : Set M) (hU : IsOpen U) :
    A.IsSmoothOn s u U ↔ ∀ t : ℝ, A.MemSobolevOn s u t U := by
  /- In each chart the coordinate image is open. Apply the Euclidean equivalence
  between local smoothness and all real Sobolev orders, then interchange the two
  universal quantifiers over charts and orders. No global target-order norm is assumed. -/
  have hopen (j : Fin A.size) : IsOpen ((A.chart j) '' (U ∩ (A.chart j).source)) :=
    (A.chart j).isOpen_image_of_subset_source
      (hU.inter (A.chart j).open_source) Set.inter_subset_right
  constructor
  · intro hu t j
    exact (AtiyahSinger.isSmoothDistributionOn_iff_forall_memSobolevOn
      (A.localDistribution s j u) _ (hopen j)).mp (hu j) t
  · intro hu j
    apply (AtiyahSinger.isSmoothDistributionOn_iff_forall_memSobolevOn
      (A.localDistribution s j u) _ (hopen j)).mpr
    intro t
    exact hu t j

set_option maxHeartbeats 800000 in
-- Both real-order reconstruction maps must retain the same finite plateau family.
/-- On the whole base, higher local regularity gives the unique lift to that completion. -/
theorem memSobolevOn_univ_iff_exists_sobolev_lift
    (s t : ℝ) (hst : s ≤ t) (u : A.SobolevSpace s) :
    A.MemSobolevOn s u t Set.univ ↔
      ∃! v : A.SobolevSpace t, A.sobolevInclusion t s hst v = u := by
  /- Each cutoff distribution has fixed compact support in its chart target,
  so local H^t membership yields order-t Bessel coordinates. Extend those coordinates
  through one fixed plateau family, using bounded maps into the actual Sobolev
  completion. The partition reconstructs every completion vector by density.
  Compatibility of the same extension maps with inclusion gives the desired lift;
  injectivity gives uniqueness. No arbitrary ambient coordinate tuple is asserted
  to belong to the defining closure. -/
  classical
  constructor
  · intro hu
    -- Fix a plateau for every original localization, inside its actual chart and frame.
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let H : Type := MeasureTheory.Lp V 2 (MeasureTheory.volume : MeasureTheory.Measure X)
    let K (j : Fin A.size) := (A.chart j) '' tsupport (A.cutoff j)
    let U (j : Fin A.size) :=
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.frame j).baseSet
    have hK (j : Fin A.size) : IsCompact (K j) :=
      (A.compact_support j).image_of_continuousOn
        ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
    have hU (j : Fin A.size) : IsOpen (U j) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage
        (A.chart j).open_target (A.frame j).open_baseSet
    have hKU (j : Fin A.size) : K j ⊆ U j := by
      rintro _ ⟨x, hx, rfl⟩
      have hs := (A.support_subset j hx).1
      refine ⟨(A.chart j).map_source hs, ?_⟩
      change (A.chart j).symm ((A.chart j) x) ∈ (A.frame j).baseSet
      rw [(A.chart j).left_inv hs]
      exact (A.support_subset j hx).2
    have hplateau (j : Fin A.size) : ∃ η : X → ℝ,
        ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U j ∧
          ∀ z ∈ K j, η z = 1 := by
      obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
        exists_open_between_and_isCompact_closure (hK j) (hU j) (hKU j)
      obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
        (n := (⊤ : ℕ∞)) hOo (hK j).isClosed hKO
      have hs : tsupport η = closure O := congrArg closure hsη
      refine ⟨η, hη, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs], ?_⟩
      exact fun z hz ↦ (honeη z).mp hz
    choose η hη hcη hsη honeη using hplateau
    let L (j : Fin A.size) : BundleChartCutoff (r := r) E (A.chart j) :=
      { frame := A.frame j
        frame_mem_atlas := A.frame_mem_atlas j
        cutoff := η j
        smooth_cutoff := hη j
        compact_support := hcη j
        support_subset := hsη j }
    -- The bounded extension is constructed at every order from the same fixed plateau.
    let F (a : ℝ) (j : Fin A.size) : SchwartzMap X V →ₗ[ℂ] A.SobolevSpace a :=
      (A.smoothToSobolev a).comp ((L j).extendLinearMap (A.chart_mem_atlas j))
    have hF (a : ℝ) (j : Fin A.size) : ∃ C : ℝ,
        ∀ v : SchwartzMap X V, ‖F a j v‖ ≤ C * ‖schwartzSobolevCoordinate a v‖ := by
      obtain ⟨C, _, hC⟩ := (L j).exists_norm_extend_sobolev_le
        (A.chart_mem_atlas j) A a
      exact ⟨C, hC⟩
    let S (a : ℝ) (j : Fin A.size) : H →L[ℂ] A.SobolevSpace a :=
      (F a j).extendOfNorm (schwartzSobolevCoordinateLinearMap n r a)
    have hS (a : ℝ) (j : Fin A.size) (v : SchwartzMap X V) :
        S a j (schwartzSobolevCoordinate a v) =
          A.smoothToSobolev a ((L j).extend (A.chart_mem_atlas j) v) :=
      (F a j).extendOfNorm_eq (denseRange_schwartzSobolevCoordinate n r a) (hF a j) v
    have hpartition (v : smoothSections (n := n) (r := r) E) :
        (∑ j, (L j).extend (A.chart_mem_atlas j) (A.localize j v)) = v := by
      apply Subtype.ext
      funext x
      have hterm (j : Fin A.size) :
          ((L j).extend (A.chart_mem_atlas j) (A.localize j v)).val x =
            (A.cutoff j x : ℂ) • v.val x := by
        let := A.frame_mem_atlas j
        by_cases hx : x ∈ (A.chart j).source
        · have hxt := (A.chart j).map_source hx
          change (if x ∈ (A.chart j).source then
            (η j ((A.chart j) x) : ℂ) • (A.frame j).symmL ℂ x
              (A.localizedFunction j v ((A.chart j) x)) else 0) = _
          simp only [hx, ite_true, SmoothBundlePresentation.localizedFunction,
            hxt, sectionInChart, (A.chart j).left_inv hx]
          by_cases hχ : A.cutoff j x = 0
          · simp [hχ]
          · have hxs := subset_tsupport (A.cutoff j) hχ
            have he := (A.support_subset j hxs).2
            rw [honeη j _ ⟨x, hxs, rfl⟩, Complex.ofReal_one, one_smul, map_smul]
            rw [(A.chart j).left_inv hx,
              ← (A.frame j).continuousLinearMapAt_apply_of_mem ℂ he,
              (A.frame j).symmL_continuousLinearMapAt he]
        · have hχ : A.cutoff j x = 0 :=
            image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (A.support_subset j hs).1)
          change (if x ∈ (A.chart j).source then _ else 0) = _
          simp [hx, hχ]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      simp_rw [hterm]
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, A.sum_cutoff, Complex.ofReal_one, one_smul]
    have hreconstruct (a : ℝ) (w : A.SobolevSpace a) :
        (∑ j, S a j (w.val j)) = w := by
      have hcont : Continuous (fun w : A.SobolevSpace a ↦ ∑ j, S a j (w.val j)) :=
        continuous_finsetSum Finset.univ (fun j _ ↦ (S a j).continuous.comp
          ((PiLp.proj (𝕜 := ℂ) 2 _ j).continuous.comp continuous_subtype_val))
      refine (A.denseRange_smoothToSobolev a).induction_on w
        (isClosed_eq hcont continuous_id) ?_
      intro v
      change (∑ j, S a j (schwartzSobolevCoordinate a (A.localize j v))) = _
      simp_rw [hS]
      rw [← map_sum, hpartition]
    -- The local target-order distributions are genuine Bessel realizations.
    have hlocal (j : Fin A.size) :
        (A.localDistribution s j u).MemSobolev t 2 := by
      apply (memSobolev_iff_memSobolevOn_of_isSupportedIn
        (A.localDistribution s j u) t (A.chart j).target (K j)
        (A.chart j).open_target (hK j) (fun z hz ↦ (hKU j hz).1)
        (A.isSupportedIn_localDistribution s j u)).mpr
      have himage : (A.chart j) '' (A.chart j).source = (A.chart j).target := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact (A.chart j).map_source hx
        · intro hz
          exact ⟨(A.chart j).symm z, (A.chart j).map_target hz, (A.chart j).right_inv hz⟩
      simpa only [Set.univ_inter, himage] using hu j
    choose w hw using fun j ↦
      (memSobolev_iff_exists_besselRealization t (A.localDistribution s j u)).mp (hlocal j)
    obtain ⟨J, _, hJ⟩ := exists_sobolev_inclusion n r t s hst
    have hJcoordinate (v : SchwartzMap X V) :
        J (schwartzSobolevCoordinate t v) = schwartzSobolevCoordinate s v := by
      apply besselRealization_injective n r s
      rw [hJ, besselRealization_schwartzSobolevCoordinate,
        besselRealization_schwartzSobolevCoordinate]
    have hcompatible (j : Fin A.size) (z : H) :
        A.sobolevInclusion t s hst (S t j z) = S s j (J z) := by
      refine (denseRange_schwartzSobolevCoordinate n r t).induction_on z
        (isClosed_eq ((A.sobolevInclusion t s hst).continuous.comp (S t j).continuous)
          ((S s j).continuous.comp J.continuous)) ?_
      intro v
      rw [hS, hJcoordinate, hS, A.sobolevInclusion_smoothToSobolev]
    have hcoordinates (j : Fin A.size) : J (w j) = u.val j := by
      apply besselRealization_injective n r s
      exact (hJ (w j)).trans (hw j)
    let v : A.SobolevSpace t := ∑ j, S t j (w j)
    have hv : A.sobolevInclusion t s hst v = u := by
      change A.sobolevInclusion t s hst (∑ j, S t j (w j)) = u
      rw [map_sum]
      simp_rw [hcompatible, hcoordinates]
      exact hreconstruct s u
    exact ⟨v, hv, fun z hz ↦ A.sobolevInclusion_injective t s hst (hz.trans hv.symm)⟩
  · rintro ⟨v, hv, _⟩
    intro j
    rw [← hv, A.localDistribution_sobolevInclusion]
    exact AtiyahSinger.memSobolevOn_of_memSobolev _ t
      ((memSobolev_iff_exists_besselRealization t _).mpr ⟨v.val j, rfl⟩) _

/-- Global local-smoothness recovers one actual smooth section representing the input. -/
theorem isSmoothOn_univ_iff_exists_smooth_lift (s : ℝ) (u : A.SobolevSpace s) :
    A.IsSmoothOn s u Set.univ ↔
      ∃! v : smoothSections (n := n) (r := r) E, A.smoothToSobolev s v = u := by
  /- Recover compatible global lifts in arbitrarily high Sobolev orders. Their
  finite-order differentiable representatives agree as actual C⁰ sections, so one
  section is smooth at every order. The original injective embeddings recover u. -/
  classical
  constructor
  · intro hu
    have hregular := (A.isSmoothOn_iff_forall_memSobolevOn s u Set.univ isOpen_univ).mp hu
    let τ (k : ℕ) : ℝ := max s ((n : ℝ) / 2 + k + 1)
    have hτ (k : ℕ) : (n : ℝ) / 2 + k < τ k := by
      exact (by linarith : (n : ℝ) / 2 + k < (n : ℝ) / 2 + k + 1).trans_le
        (le_max_right _ _)
    have hsτ (k : ℕ) : s ≤ τ k := le_max_left _ _
    have hzero (k : ℕ) : τ 0 ≤ τ k := by
      apply max_le_max le_rfl
      simp only [Nat.cast_zero, add_zero]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    choose w hw using fun k ↦
      ((A.memSobolevOn_univ_iff_exists_sobolev_lift s (τ k) (hsτ k) u).mp
        (hregular (τ k))).exists
    -- All chosen lifts lower to the same C⁰-level Sobolev vector.
    have hcompatible (k : ℕ) : A.sobolevInclusion (τ k) (τ 0) (hzero k) (w k) = w 0 := by
      apply A.sobolevInclusion_injective (τ 0) s (hsτ 0)
      have hcomp : (A.sobolevInclusion (τ 0) s (hsτ 0)).comp
          (A.sobolevInclusion (τ k) (τ 0) (hzero k)) =
            A.sobolevInclusion (τ k) s (hsτ k) := by
        apply DFunLike.coe_injective
        apply (A.denseRange_smoothToSobolev (τ k)).equalizer
          ((A.sobolevInclusion (τ 0) s (hsτ 0)).comp
            (A.sobolevInclusion (τ k) (τ 0) (hzero k))).continuous
          (A.sobolevInclusion (τ k) s (hsτ k)).continuous
        funext v
        simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
          A.sobolevInclusion_smoothToSobolev]
      exact (DFunLike.congr_fun hcomp (w k)).trans ((hw k).trans (hw 0).symm)
    -- Forgetting C^k regularity keeps the underlying section and is bounded.
    let L (k : ℕ) : A.CkSectionSpace k →L[ℂ] A.CkSectionSpace 0 := by
      let l : A.CkSectionSpace k →ₗ[ℂ] A.CkSectionSpace 0 :=
        { toFun := fun v ↦ ⟨v.val, fun e he ↦ (v.property e he).of_le (by simp)⟩
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      apply l.mkContinuous 1
      intro v
      change A.ckNorm 0 (l v) ≤ 1 * A.ckNorm k v
      rw [one_mul]
      by_cases hsize : A.size = 0
      · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
        simp [SmoothBundlePresentation.ckNorm]
      · let i₀ : Fin A.size := ⟨0, Nat.pos_of_ne_zero hsize⟩
        apply csSup_le_csSup (A.bddAbove_ckNorm_values k v)
        · exact ⟨‖iteratedFDeriv ℝ 0 (A.localizedCkFunction 0 i₀ (l v)) 0‖,
            i₀, 0, le_rfl, 0, rfl⟩
        · rintro a ⟨i, j, hj, x, rfl⟩
          exact ⟨i, j, hj.trans (Nat.zero_le k), x, rfl⟩
    let v₀ : A.CkSectionSpace 0 := A.sobolevToCk 0 (τ 0) (hτ 0) (w 0)
    have hsame (k : ℕ) :
        (L k) (A.sobolevToCk k (τ k) (hτ k) (w k)) = v₀ := by
      have hmaps : (L k).comp (A.sobolevToCk k (τ k) (hτ k)) =
          (A.sobolevToCk 0 (τ 0) (hτ 0)).comp
            (A.sobolevInclusion (τ k) (τ 0) (hzero k)) := by
        apply DFunLike.coe_injective
        apply (A.denseRange_smoothToSobolev (τ k)).equalizer
          ((L k).comp (A.sobolevToCk k (τ k) (hτ k))).continuous
          ((A.sobolevToCk 0 (τ 0) (hτ 0)).comp
            (A.sobolevInclusion (τ k) (τ 0) (hzero k))).continuous
        funext v
        simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
          A.sobolevToCk_smoothToSobolev, A.sobolevInclusion_smoothToSobolev]
        rfl
      have heq := DFunLike.congr_fun hmaps (w k)
      simpa only [ContinuousLinearMap.comp_apply, hcompatible] using heq
    -- The C⁰ section has every finite differentiability order, hence is smooth.
    have hsmooth : IsSmoothSection (n := n) (r := r) E v₀.val := by
      intro e he
      apply contMDiffOn_infty.mpr
      intro k
      have hval := congrArg (fun v : A.CkSectionSpace 0 ↦ v.val) (hsame k)
      change (A.sobolevToCk k (τ k) (hτ k) (w k)).val = v₀.val at hval
      rw [← hval]
      exact (A.sobolevToCk k (τ k) (hτ k) (w k)).property e he
    let v : smoothSections (n := n) (r := r) E := ⟨v₀.val, hsmooth⟩
    have hhigh : A.smoothToSobolev (τ 0) v = w 0 := by
      apply A.sobolevToCk_injective 0 (τ 0) (hτ 0)
      rw [A.sobolevToCk_smoothToSobolev]
      rfl
    have hv : A.smoothToSobolev s v = u := by
      rw [← A.sobolevInclusion_smoothToSobolev (τ 0) s (hsτ 0) v, hhigh, hw]
    exact ⟨v, hv, fun z hz ↦ A.smoothToSobolev_injective s (hz.trans hv.symm)⟩
  · rintro ⟨v, hv, _⟩
    rw [← hv]
    exact A.isSmoothOn_smoothToSobolev s v Set.univ isOpen_univ

/-- The singular support of a Sobolev section is closed in the base. -/
theorem isClosed_singularSupport (s : ℝ) (u : A.SobolevSpace s) :
    IsClosed (A.singularSupport s u) := by
  /- Its complement is the union of open sets on which the section is smooth.
  This uses the neighborhood definition, rather than evaluating totalized charts
  outside their source or asserting that each unrestricted chart preimage is closed. -/
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change ¬ ¬ ∃ U, IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn s u U at hx
  obtain ⟨U, hU, hxU, hu⟩ := not_not.mp hx
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  change ¬ ¬ ∃ V, IsOpen V ∧ y ∈ V ∧ A.IsSmoothOn s u V
  exact not_not.mpr ⟨U, hU, hy, hu⟩

/-- On an open set, local smoothness is exactly disjointness from singular support. -/
theorem isSmoothOn_iff_disjoint_singularSupport (s : ℝ) (u : A.SobolevSpace s)
    (U : Set M) (hU : IsOpen U) :
    A.IsSmoothOn s u U ↔ Disjoint U (A.singularSupport s u) := by
  /- One implication uses U as a smooth neighborhood. Conversely, restrict the
  smooth neighborhoods to U. In each chart the corresponding Euclidean smooth
  representatives agree as distributions on overlaps and therefore glue. Apply
  the Euclidean local smoothness criterion to obtain the stated chartwise predicate. -/
  constructor
  · intro hu
    refine Set.disjoint_left.mpr ?_
    intro x hxU hxs
    exact hxs ⟨U, hU, hxU, hu⟩
  · intro hdisjoint j
    -- The Euclidean gluing theorem converts pointwise smooth neighborhoods into one predicate.
    have hopen : IsOpen ((A.chart j) '' (U ∩ (A.chart j).source)) :=
      (A.chart j).isOpen_image_of_subset_source
        (hU.inter (A.chart j).open_source) Set.inter_subset_right
    apply (AtiyahSinger.isSmoothDistributionOn_iff_disjoint_singularSupport
      (A.localDistribution s j u) _ hopen).mpr
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨x, ⟨hxU, hxsource⟩, rfl⟩ hxs
    have hx : x ∉ A.singularSupport s u := fun hs ↦
      Set.disjoint_left.mp hdisjoint hxU hs
    change ¬ ¬ ∃ V, IsOpen V ∧ x ∈ V ∧ A.IsSmoothOn s u V at hx
    obtain ⟨V, hV, hxV, huV⟩ := not_not.mp hx
    -- Use the same chart and the same localized distribution as the global input.
    exact hxs ⟨(A.chart j) '' (V ∩ (A.chart j).source),
      (A.chart j).isOpen_image_of_subset_source
        (hV.inter (A.chart j).open_source) Set.inter_subset_right,
      ⟨x, ⟨hxV, hxsource⟩, rfl⟩, huV j⟩

/-- The singular support is the finite union of the genuine chartwise singular supports. -/
theorem singularSupport_eq_iUnion (s : ℝ) (u : A.SobolevSpace s) :
    A.singularSupport s u = ⋃ j : Fin A.size,
      (A.chart j).source ∩
        (A.chart j) ⁻¹' AtiyahSinger.singularSupport (A.localDistribution s j u) := by
  /- Stage 1: smoothness near a base point makes every localized distribution
  smooth near its coordinate wherever that chart is defined, giving one inclusion.
  Stage 2: outside the displayed union, each relevant chart gives a smooth
  neighborhood. For a chart whose source misses the point, use the fixed compact
  cutoff support to avoid that localization on a neighborhood; its distribution
  vanishes there. Intersect the finitely many neighborhoods. All localized
  distributions are then smooth, giving the reverse inclusion. The source
  intersections exclude arbitrary values of the totalized charts off their domains. -/
  classical
  ext x
  constructor
  · intro hsing
    by_contra hnotUnion
    -- Every chart gives a neighborhood of the same base point on which its localization is smooth.
    have local_neighborhood (j : Fin A.size) :
        ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
          IsSmoothDistributionOn (A.localDistribution s j u)
            ((A.chart j) '' (V ∩ (A.chart j).source)) := by
      by_cases hxsource : x ∈ (A.chart j).source
      · have hx : (A.chart j) x ∉ AtiyahSinger.singularSupport
            (A.localDistribution s j u) := fun hs ↦
          hnotUnion (Set.mem_iUnion.mpr ⟨j, hxsource, hs⟩)
        change ¬ ¬ ∃ W, IsOpen W ∧ (A.chart j) x ∈ W ∧
          IsSmoothDistributionOn (A.localDistribution s j u) W at hx
        obtain ⟨W, hW, hxW, huW⟩ := not_not.mp hx
        let V : Set M := (A.chart j).source ∩ (A.chart j) ⁻¹' W
        have hV : IsOpen V := (A.chart j).isOpen_inter_preimage hW
        refine ⟨V, hV, ⟨hxsource, hxW⟩, ?_⟩
        apply huW.mono
        · exact (A.chart j).isOpen_image_of_subset_source
            (hV.inter (A.chart j).open_source) Set.inter_subset_right
        · rintro z ⟨y, ⟨hyV, _⟩, rfl⟩
          exact hyV.2
      · -- A chart missing x has cutoff support away from x, so its distribution is zero there.
        let V : Set M := (tsupport (A.cutoff j))ᶜ
        have hxV : x ∈ V := fun hcut ↦ hxsource (A.support_subset j hcut).1
        refine ⟨V, (isClosed_tsupport (A.cutoff j)).isOpen_compl, hxV,
          (fun _ ↦ 0), contDiffOn_const, ?_⟩
        intro φ hφ hφV
        have hdisjoint : Disjoint (tsupport φ) ((A.chart j) '' tsupport (A.cutoff j)) := by
          refine Set.disjoint_left.mpr ?_
          rintro z hzφ ⟨y, hy, rfl⟩
          obtain ⟨w, ⟨hwV, hwsource⟩, heq⟩ := hφV hzφ
          have hw : w = y := (A.chart j).injOn hwsource (A.support_subset j hy).1 heq
          exact hwV (hw.symm ▸ hy)
        rw [(A.isSupportedIn_localDistribution s j u).apply_eq_zero φ hφ hdisjoint]
        simp
    choose V hV hxV huV using local_neighborhood
    -- Finiteness permits one common open neighborhood; no uniform coordinate radius is used.
    have hcommon : IsOpen (⋂ j : Fin A.size, V j) := isOpen_iInter_of_finite hV
    apply hsing
    refine ⟨⋂ j : Fin A.size, V j, hcommon, Set.mem_iInter.mpr hxV, ?_⟩
    intro j
    apply (huV j).mono
    · exact (A.chart j).isOpen_image_of_subset_source
        (hcommon.inter (A.chart j).open_source) Set.inter_subset_right
    · rintro z ⟨y, ⟨hyV, hysource⟩, rfl⟩
      exact ⟨y, ⟨Set.mem_iInter.mp hyV j, hysource⟩, rfl⟩
  · intro hxUnion
    obtain ⟨j, hxsource, hxs⟩ := Set.mem_iUnion.mp hxUnion
    rintro ⟨U, hU, hxU, huU⟩
    -- A section-smooth neighborhood gives a coordinate-smooth neighborhood in every valid chart.
    exact hxs ⟨(A.chart j) '' (U ∩ (A.chart j).source),
      (A.chart j).isOpen_image_of_subset_source
        (hU.inter (A.chart j).open_source) Set.inter_subset_right,
      ⟨x, ⟨hxU, hxsource⟩, rfl⟩, huU j⟩

end SmoothBundlePresentation

end AtiyahSinger

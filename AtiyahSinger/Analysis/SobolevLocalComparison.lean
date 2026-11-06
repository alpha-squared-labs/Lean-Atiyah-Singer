/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SobolevLocalRegularity

import AtiyahSinger.Analysis.SobolevLocalization

/-!
# Local regularity under changes of Sobolev realization

Public module ID: M0998.

D04/A01/A06: the usual local regularity and singular support belong to the
represented section. They are invariant under the actual inclusion and the
presentation equivalence, not arbitrary identifications of Hilbert coordinate spaces.
The change-of-presentation proof uses localized coordinate/frame maps and their
real-order bounds from SG III.2.11--2.14. Density alone cannot preserve regularity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology

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

include hM hT2 hSC hE

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- Changing the ambient Sobolev order by its natural inclusion preserves local regularity. -/
theorem memSobolevOn_sobolevInclusion_iff (s l t : ℝ) (hls : l ≤ s)
    (u : A.SobolevSpace s) (U : Set M) :
    A.MemSobolevOn l (A.sobolevInclusion s l hls u) t U ↔ A.MemSobolevOn s u t U := by
  /- The inclusion preserves every localized distribution exactly. Substitute
  localDistribution_sobolevInclusion in the defining cutoff conditions. The local
  target t is independent of both ambient orders, and U need not be open for this identity. -/
  unfold MemSobolevOn
  simp only [A.localDistribution_sobolevInclusion s l hls]

/-- The natural order-decreasing inclusion preserves local smoothness. -/
theorem isSmoothOn_sobolevInclusion_iff (s l : ℝ) (hls : l ≤ s)
    (u : A.SobolevSpace s) (U : Set M) :
    A.IsSmoothOn l (A.sobolevInclusion s l hls u) U ↔ A.IsSmoothOn s u U := by
  /- Substitute the same local distribution identity in each chartwise smoothness
  condition. No elliptic regularity or continuity of smooth representatives is needed. -/
  unfold IsSmoothOn
  simp only [A.localDistribution_sobolevInclusion s l hls]

/-- The actual inclusion does not change the section's singular support. -/
theorem singularSupport_sobolevInclusion (s l : ℝ) (hls : l ≤ s)
    (u : A.SobolevSpace s) :
    A.singularSupport l (A.sobolevInclusion s l hls u) = A.singularSupport s u := by
  /- Local smoothness is equivalent on every open neighborhood by the preceding
  theorem. Their negated neighborhood predicates therefore define the same set. -/
  ext x
  change (¬ ∃ U : Set M,
    IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn l (A.sobolevInclusion s l hls u) U) ↔
    ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn s u U
  simp only [A.isSmoothOn_sobolevInclusion_iff s l hls]

variable (B : SmoothBundlePresentation (n := n) (r := r) E)

set_option maxHeartbeats 800000 in

/-- Local H^t membership is independent of the finite presentation. -/
theorem memSobolevOn_sobolevEquiv_iff (s t : ℝ) (u : A.SobolevSpace s)
    (U : Set M) (hU : IsOpen U) :
    B.MemSobolevOn s (A.sobolevEquiv B s u) t U ↔ A.MemSobolevOn s u t U := by
  /- Stage 1: insert A's partition into each B localization and refine the compact
  overlaps inside U. Each term is multiplication by a smooth matrix and a smooth
  coordinate pullback with compact cutoffs. These maps are bounded at every real
  order. Their distribution identities extend from smooth sections by continuity
  at the ambient order s; coordinate pullback on tests includes the Jacobian.
  Stage 2: apply the order-t bounds to compact cutoffs of the given local H^t
  distributions, then sum the finitely many terms. This transfers membership to B.
  Interchange A and B and use the inverse presentation equivalence. Convergence
  of smooth approximants alone would not show that a limit retains order t. -/
  classical
  have htransfer (C D : SmoothBundlePresentation (n := n) (r := r) E)
      (w : C.SobolevSpace s) (hw : C.MemSobolevOn s w t U) :
      D.MemSobolevOn s (C.sobolevEquiv D s w) t U := by
    by_cases hst : s ≤ t
    · intro k χ hχ hcχ hsχ
      let X := EuclideanSpace ℝ (Fin n)
      let V := EuclideanSpace ℂ (Fin r)
      let H : Type := MeasureTheory.Lp V 2 (MeasureTheory.volume : MeasureTheory.Measure X)
      -- The target cutoff is supported in a compact subset of the same open base set.
      let K := (D.chart k).symm '' tsupport χ
      have hχtarget : tsupport χ ⊆ (D.chart k).target := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := hsχ hz
        exact (D.chart k).map_source hx.2
      have hK : IsCompact K := hcχ.image_of_continuousOn
        ((D.chart k).continuousOn_symm.mono hχtarget)
      have hKU : K ⊆ U := by
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨x, hx, hzx⟩ := hsχ hz
        rw [← hzx, (D.chart k).left_inv hx.2]
        exact hx.1
      let W (j : Fin C.size) := (C.chart j) '' (U ∩ (C.chart j).source)
      let K₁ (j : Fin C.size) := (C.chart j) '' (K ∩ tsupport (C.cutoff j))
      have hW (j : Fin C.size) : IsOpen (W j) :=
        (C.chart j).isOpen_image_of_subset_source (hU.inter (C.chart j).open_source)
          Set.inter_subset_right
      have hK₁ (j : Fin C.size) : IsCompact (K₁ j) :=
        (hK.inter_right (isClosed_tsupport _)).image_of_continuousOn
          ((C.chart j).continuousOn.mono (fun x hx ↦ (C.support_subset j hx.2).1))
      have hK₁W (j : Fin C.size) : K₁ j ⊆ W j := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, ⟨hKU hx.1, (C.support_subset j hx.2).1⟩, rfl⟩
      have hcut (j : Fin C.size) : ∃ η : X → ℝ,
          ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ W j ∧
            ∀ z ∈ K₁ j, η z = 1 := by
        obtain ⟨O, hOo, hKO, hOW, hOc⟩ :=
          exists_open_between_and_isCompact_closure (hK₁ j) (hW j) (hK₁W j)
        obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
          (n := (⊤ : ℕ∞)) hOo (hK₁ j).isClosed hKO
        have hs : tsupport η = closure O := congrArg closure hsη
        exact ⟨η, hη, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs],
          fun z hz ↦ (honeη z).mp hz⟩
      choose η hη hcη hsη honeη using hcut
      -- Fixed chart plateaus give bounded extension into the original completion at both orders.
      let K₀ (j : Fin C.size) := (C.chart j) '' tsupport (C.cutoff j)
      let W₀ (j : Fin C.size) :=
        (C.chart j).target ∩ (C.chart j).symm ⁻¹' (C.frame j).baseSet
      have hK₀ (j : Fin C.size) : IsCompact (K₀ j) :=
        (C.compact_support j).image_of_continuousOn
          ((C.chart j).continuousOn.mono (fun x hx ↦ (C.support_subset j hx).1))
      have hW₀ (j : Fin C.size) : IsOpen (W₀ j) :=
        (C.chart j).continuousOn_symm.isOpen_inter_preimage
          (C.chart j).open_target (C.frame j).open_baseSet
      have hK₀W (j : Fin C.size) : K₀ j ⊆ W₀ j := by
        rintro _ ⟨x, hx, rfl⟩
        have hs := (C.support_subset j hx).1
        refine ⟨(C.chart j).map_source hs, ?_⟩
        change (C.chart j).symm ((C.chart j) x) ∈ (C.frame j).baseSet
        rw [(C.chart j).left_inv hs]
        exact (C.support_subset j hx).2
      have hplateau (j : Fin C.size) : ∃ ζ : X → ℝ,
          ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ W₀ j ∧
            ∀ z ∈ K₀ j, ζ z = 1 := by
        obtain ⟨O, hOo, hKO, hOW, hOc⟩ :=
          exists_open_between_and_isCompact_closure (hK₀ j) (hW₀ j) (hK₀W j)
        obtain ⟨ζ, hζ, _, hsζ, honeζ⟩ := exists_contDiff_support_eq_eq_one_iff
          (n := (⊤ : ℕ∞)) hOo (hK₀ j).isClosed hKO
        have hs : tsupport ζ = closure O := congrArg closure hsζ
        exact ⟨ζ, hζ, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs],
          fun z hz ↦ (honeζ z).mp hz⟩
      choose ζ hζ hcζ hsζ honeζ using hplateau
      let L (j : Fin C.size) : BundleChartCutoff (r := r) E (C.chart j) :=
        { frame := C.frame j
          frame_mem_atlas := C.frame_mem_atlas j
          cutoff := ζ j
          smooth_cutoff := hζ j
          compact_support := hcζ j
          support_subset := hsζ j }
      let F (a : ℝ) (j : Fin C.size) : SchwartzMap X V →ₗ[ℂ] C.SobolevSpace a :=
        (C.smoothToSobolev a).comp ((L j).extendLinearMap (C.chart_mem_atlas j))
      have hF (a : ℝ) (j : Fin C.size) : ∃ c : ℝ,
          ∀ v : SchwartzMap X V, ‖F a j v‖ ≤ c * ‖schwartzSobolevCoordinate a v‖ := by
        obtain ⟨c, _, hc⟩ := (L j).exists_norm_extend_sobolev_le
          (C.chart_mem_atlas j) C a
        exact ⟨c, hc⟩
      let S (a : ℝ) (j : Fin C.size) : H →L[ℂ] C.SobolevSpace a :=
        (F a j).extendOfNorm (schwartzSobolevCoordinateLinearMap n r a)
      have hS (a : ℝ) (j : Fin C.size) (v : SchwartzMap X V) :
          S a j (schwartzSobolevCoordinate a v) =
            C.smoothToSobolev a ((L j).extend (C.chart_mem_atlas j) v) :=
        (F a j).extendOfNorm_eq (denseRange_schwartzSobolevCoordinate n r a) (hF a j) v
      let R (a : ℝ) : C.SobolevSpace a →L[ℂ] H :=
        (sobolevCutoffCLM a χ hχ hcχ).comp
          ((PiLp.proj (𝕜 := ℂ) 2 _ k).comp
            (((D.sobolevCoordinates a).range.topologicalClosure.subtypeL).comp
              (C.sobolevEquiv D a).toContinuousLinearMap))
      have hmult (a : ℝ) (ψ : X → ℝ) (hψ : ContDiff ℝ ∞ ψ)
          (hcψ : HasCompactSupport ψ) (v : SchwartzMap X V) :
          sobolevCutoffCLM a ψ hψ hcψ (schwartzSobolevCoordinate a v) =
            schwartzSobolevCoordinate a
              (SchwartzMap.smulLeftCLM V (fun x ↦ (ψ x : ℂ)) v) := by
        have hgrowth : (fun x ↦ (ψ x : ℂ)).HasTemperateGrowth :=
          (hcψ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
            (Complex.ofRealCLM.contDiff.comp hψ)
        apply besselRealization_injective n r a
        rw [besselRealization_sobolevCutoffCLM,
          besselRealization_schwartzSobolevCoordinate,
          besselRealization_schwartzSobolevCoordinate]
        ext1 φ
        change (∫ x, (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (ψ x : ℂ)) φ) x • v x) =
          ∫ x, φ x • (SchwartzMap.smulLeftCLM V (fun x ↦ (ψ x : ℂ)) v) x
        simp only [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [smul_smul, mul_comm]
        rfl
      have hR (a : ℝ) (v : smoothSections (n := n) (r := r) E) :
          R a (C.smoothToSobolev a v) = schwartzSobolevCoordinate a
            (SchwartzMap.smulLeftCLM V (fun x ↦ (χ x : ℂ)) (D.localize k v)) := by
        change sobolevCutoffCLM a χ hχ hcχ
          ((C.sobolevEquiv D a (C.smoothToSobolev a v)).val k) = _
        rw [C.sobolevEquiv_smoothToSobolev]
        exact hmult a χ hχ hcχ (D.localize k v)
      -- The same source cutoffs are neutral on the support of the requested target cutoff.
      have hsum (v : C.SobolevSpace s) :
          (∑ j, R s (S s j (sobolevCutoffCLM s (η j) (hη j) (hcη j) (v.val j)))) =
            R s v := by
        let vcut (j : Fin C.size) (f : smoothSections (n := n) (r := r) E) :
            smoothSections (n := n) (r := r) E :=
          (L j).extend (C.chart_mem_atlas j)
            (SchwartzMap.smulLeftCLM V (fun x ↦ (η j x : ℂ)) (C.localize j f))
        have hηgrowth (j : Fin C.size) : (fun x ↦ (η j x : ℂ)).HasTemperateGrowth :=
          ((hcη j).comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
            (Complex.ofRealCLM.contDiff.comp (hη j))
        have hsection (j : Fin C.size) (f : smoothSections (n := n) (r := r) E) (x : M) :
            (vcut j f).val x = (η j (C.chart j x) : ℂ) • (C.cutoff j x : ℂ) • f.val x := by
          let := C.frame_mem_atlas j
          by_cases hx : x ∈ (C.chart j).source
          · change (if x ∈ (C.chart j).source then
              (ζ j (C.chart j x) : ℂ) • (C.frame j).symmL ℂ x
                ((SchwartzMap.smulLeftCLM V (fun z ↦ (η j z : ℂ))
                  (C.localize j f)) (C.chart j x)) else 0) = _
            rw [ite_eq_left hx, SchwartzMap.smulLeftCLM_apply_apply (hηgrowth j)]
            change (ζ j (C.chart j x) : ℂ) • (C.frame j).symmL ℂ x
              ((η j (C.chart j x) : ℂ) • C.localizedFunction j f (C.chart j x)) = _
            simp only [SmoothBundlePresentation.localizedFunction,
              ite_eq_left ((C.chart j).map_source hx), sectionInChart, (C.chart j).left_inv hx]
            by_cases hzero : C.cutoff j x = 0
            · simp [hzero]
            · have hxs := subset_tsupport (C.cutoff j) hzero
              have he := (C.support_subset j hxs).2
              rw [honeζ j _ ⟨x, hxs, rfl⟩, Complex.ofReal_one, one_smul, map_smul,
                map_smul]
              rw [(C.chart j).left_inv hx,
                ← (C.frame j).continuousLinearMapAt_apply_of_mem ℂ he,
                (C.frame j).symmL_continuousLinearMapAt he]
          · have hzero : C.cutoff j x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (C.support_subset j hs).1)
            change (if x ∈ (C.chart j).source then _ else 0) = _
            simp [hx, hzero]
        have hreconstruct (f : smoothSections (n := n) (r := r) E) (x : M) (hx : x ∈ K) :
            (∑ j, vcut j f).val x = f.val x := by
          have hterm (j : Fin C.size) :
              (vcut j f).val x = (C.cutoff j x : ℂ) • f.val x := by
            rw [hsection]
            by_cases hzero : C.cutoff j x = 0
            · simp [hzero]
            · rw [honeη j _ ⟨x, ⟨hx, subset_tsupport _ hzero⟩, rfl⟩,
                Complex.ofReal_one, one_smul]
          simp only [Submodule.coe_sum, Finset.sum_apply]
          simp_rw [hterm]
          rw [← Finset.sum_smul, ← Complex.ofReal_sum, C.sum_cutoff,
            Complex.ofReal_one, one_smul]
        have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
          (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
            (Complex.ofRealCLM.contDiff.comp hχ)
        have hlocalized (f : smoothSections (n := n) (r := r) E) :
            SchwartzMap.smulLeftCLM V (fun x ↦ (χ x : ℂ))
              (D.localize k (∑ j, vcut j f)) =
            SchwartzMap.smulLeftCLM V (fun x ↦ (χ x : ℂ)) (D.localize k f) := by
          apply SchwartzMap.ext
          intro z
          simp only [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
          by_cases hzero : χ z = 0
          · simp [hzero]
          · have hz : z ∈ (D.chart k).target := hχtarget (subset_tsupport χ hzero)
            have hx : (D.chart k).symm z ∈ K := ⟨z, subset_tsupport χ hzero, rfl⟩
            change (χ z : ℂ) • D.localizedFunction k (∑ j, vcut j f) z =
              (χ z : ℂ) • D.localizedFunction k f z
            simp only [SmoothBundlePresentation.localizedFunction, ite_eq_left hz,
              sectionInChart, hreconstruct f _ hx]
        have hcont : Continuous (fun v : C.SobolevSpace s ↦
            ∑ j, R s (S s j (sobolevCutoffCLM s (η j) (hη j) (hcη j) (v.val j)))) :=
          continuous_finsetSum Finset.univ (fun j _ ↦ (R s).continuous.comp
            ((S s j).continuous.comp ((sobolevCutoffCLM s (η j) (hη j) (hcη j)).continuous.comp
              ((PiLp.proj (𝕜 := ℂ) 2 _ j).continuous.comp continuous_subtype_val))))
        refine (C.denseRange_smoothToSobolev s).induction_on v
          (isClosed_eq hcont (R s).continuous) ?_
        intro f
        change (∑ j, R s (S s j (sobolevCutoffCLM s (η j) (hη j) (hcη j)
          (schwartzSobolevCoordinate s (C.localize j f))))) = _
        simp_rw [hmult, hS]
        change (∑ j, R s (C.smoothToSobolev s (vcut j f))) = R s (C.smoothToSobolev s f)
        rw [← map_sum, ← map_sum, hR, hR, hlocalized]
      -- Local H^t supplies actual Bessel coordinates for every truncated source distribution.
      have hlocal (j : Fin C.size) :
          (TemperedDistribution.smulLeftCLM V (fun x ↦ (η j x : ℂ))
            (C.localDistribution s j w)).MemSobolev t 2 := hw j (η j) (hη j) (hcη j) (hsη j)
      choose z hz using fun j ↦ (memSobolev_iff_exists_besselRealization t _).mp (hlocal j)
      obtain ⟨J, _, hJ⟩ := exists_sobolev_inclusion n r t s hst
      have hJcoordinate (v : SchwartzMap X V) :
          J (schwartzSobolevCoordinate t v) = schwartzSobolevCoordinate s v := by
        apply besselRealization_injective n r s
        rw [hJ, besselRealization_schwartzSobolevCoordinate,
          besselRealization_schwartzSobolevCoordinate]
      have hcompatible (j : Fin C.size) (v : H) :
          J (R t (S t j v)) = R s (S s j (J v)) := by
        refine (denseRange_schwartzSobolevCoordinate n r t).induction_on v
          (isClosed_eq (J.continuous.comp ((R t).continuous.comp (S t j).continuous))
            ((R s).continuous.comp ((S s j).continuous.comp J.continuous))) ?_
        intro f
        rw [hS, hR, hJcoordinate, hJcoordinate, hS, hR]
      have hzcoordinate (j : Fin C.size) :
          J (z j) = sobolevCutoffCLM s (η j) (hη j) (hcη j) (w.val j) := by
        apply besselRealization_injective n r s
        rw [hJ, hz, besselRealization_sobolevCutoffCLM]
        rfl
      have houtput : J (∑ j, R t (S t j (z j))) = R s w := by
        rw [map_sum]
        simp_rw [hcompatible, hzcoordinate]
        exact hsum w
      apply (memSobolev_iff_exists_besselRealization t _).mpr
      refine ⟨∑ j, R t (S t j (z j)), ?_⟩
      rw [← hJ, houtput]
      exact besselRealization_sobolevCutoffCLM s χ hχ hcχ _
    · exact D.memSobolevOn_of_le s s t (C.sobolevEquiv D s w) U
        (D.memSobolevOn_self s _ U) (le_of_not_ge hst)
  constructor
  · intro hu
    have hinv : B.sobolevEquiv A s (A.sobolevEquiv B s u) = u := by
      refine (A.denseRange_smoothToSobolev s).induction_on u
        (isClosed_eq ((B.sobolevEquiv A s).continuous.comp (A.sobolevEquiv B s).continuous)
          continuous_id) ?_
      intro v
      rw [A.sobolevEquiv_smoothToSobolev, B.sobolevEquiv_smoothToSobolev]
    simpa only [hinv] using htransfer B A (A.sobolevEquiv B s u) hu
  · exact htransfer A B u

/-- Local smoothness is independent of the finite presentation. -/
theorem isSmoothOn_sobolevEquiv_iff (s : ℝ) (u : A.SobolevSpace s)
    (U : Set M) (hU : IsOpen U) :
    B.IsSmoothOn s (A.sobolevEquiv B s u) U ↔ A.IsSmoothOn s u U := by
  /- Characterize smoothness by all local real Sobolev orders in each presentation.
  Transfer each order through memSobolevOn_sobolevEquiv_iff. The smooth representative
  need not extend globally across the boundary of U. -/
  rw [B.isSmoothOn_iff_forall_memSobolevOn s _ U hU,
    A.isSmoothOn_iff_forall_memSobolevOn s u U hU]
  exact forall_congr' (fun t ↦ A.memSobolevOn_sobolevEquiv_iff B s t u U hU)

/-- The canonical change of presentation preserves the actual singular support in M. -/
theorem singularSupport_sobolevEquiv (s : ℝ) (u : A.SobolevSpace s) :
    B.singularSupport s (A.sobolevEquiv B s u) = A.singularSupport s u := by
  /- The previous equivalence applies to every open neighborhood in the common
  base M. Use the neighborhood definitions on both sides and set extensionality.
  No map of base points or arbitrary identification of coordinate tuples is involved. -/
  ext x
  change (¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      B.IsSmoothOn s (A.sobolevEquiv B s u) U) ↔
    ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn s u U
  constructor
  · intro h hx
    obtain ⟨U, hU, hxU, hu⟩ := hx
    exact h ⟨U, hU, hxU, (A.isSmoothOn_sobolevEquiv_iff B s u U hU).mpr hu⟩
  · intro h hx
    obtain ⟨U, hU, hxU, hu⟩ := hx
    exact h ⟨U, hU, hxU, (A.isSmoothOn_sobolevEquiv_iff B s u U hU).mp hu⟩

end SmoothBundlePresentation

end AtiyahSinger

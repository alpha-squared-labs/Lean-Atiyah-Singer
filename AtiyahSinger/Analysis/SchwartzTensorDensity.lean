/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactJetIntegral
public import AtiyahSinger.Analysis.EuclideanSobolev
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Schwartz topology and separated test functions

Public module ID: M0953.

Weighted jets on a common compact support realize the original Schwartz
seminorms in Banach spaces of continuous functions. Finite collections of these
jets allow compact parameter integrals to be approximated in the full Schwartz
topology by finite sums. Fourier reconstruction with separated plateau cutoffs
then supplies the tensor-density input for actual tempered kernels.

The argument retains every spatial weight and derivative order. No density
statement in an Lp or Sobolev space is used as Schwartz density.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option backward.isDefEq.respectTransparency false

attribute [local instance 2000] NormedField.toNormedCommRing Real.normedCommRing

open MeasureTheory FourierTransform Set Topology
open scoped ContDiff SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A weighted Schwartz jet restricted to a specified compact set.
Its supremum norm realizes the corresponding Schwartz seminorm for functions
supported in that set; finite products of these maps provide Banach targets
for integration without imposing a norm on Schwartz space itself. -/
def schwartzWeightedJetOn (K : Set E) [CompactSpace K] (k j : ℕ) :
    𝓢(E, ℂ) →L[ℂ] C(K, E [×j]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun f ↦ ⟨fun x ↦ ‖(x : E)‖ ^ k • iteratedFDeriv ℝ j f x,
      ((continuous_subtype_val.norm.pow k).smul
        (((f.smooth ⊤).continuous_iteratedFDeriv (by simp)).comp
          continuous_subtype_val))⟩)
    (by
      intro f g
      apply ContinuousMap.ext
      intro x
      change ‖(x : E)‖ ^ k • iteratedFDeriv ℝ j ((f : E → ℂ) + (g : E → ℂ)) (x : E) =
        ‖(x : E)‖ ^ k • iteratedFDeriv ℝ j f (x : E) +
          ‖(x : E)‖ ^ k • iteratedFDeriv ℝ j g (x : E)
      rw [iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt,
        smul_add])
    (by
      intro a f
      apply ContinuousMap.ext
      intro x
      change ‖(x : E)‖ ^ k • iteratedFDeriv ℝ j (a • (f : E → ℂ)) x =
        a • (‖(x : E)‖ ^ k • iteratedFDeriv ℝ j f x)
      rw [iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt]
      exact smul_comm _ _ _)
    (by
      refine ⟨{(k, j)}, 1, zero_le_one, ?_⟩
      intro f
      simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply, one_mul]
      apply (ContinuousMap.norm_le _ (apply_nonneg _ _)).mpr
      intro x
      simpa only [ContinuousMap.coe_mk, norm_smul, Real.norm_of_nonneg
        (pow_nonneg (norm_nonneg _) _)] using SchwartzMap.le_seminorm ℂ k j f x)

/-- On a common compact support, a weighted jet has exactly its original Schwartz seminorm. -/
theorem norm_schwartzWeightedJetOn (K : Set E) [CompactSpace K] (k j : ℕ)
    (f : 𝓢(E, ℂ)) (hf : tsupport f ⊆ K) :
    ‖schwartzWeightedJetOn K k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (apply_nonneg _ _)).mpr
    intro x
    change ‖‖(x : E)‖ ^ k • iteratedFDeriv ℝ j f x‖ ≤ _
    simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using
      SchwartzMap.le_seminorm ℂ k j f x
  · apply SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _)
    intro x
    by_cases hx : x ∈ K
    · have h := ContinuousMap.norm_coe_le_norm (schwartzWeightedJetOn K k j f) ⟨x, hx⟩
      change ‖‖x‖ ^ k • iteratedFDeriv ℝ j f x‖ ≤ _ at h
      simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using h
    · have hzero : (f : E → ℂ) =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hf h))
      rw [(hzero.iteratedFDeriv ℝ j).eq_of_nhds]
      simp

/-- A compact-parameter integral with common compact spatial support belongs to the
Schwartz closure of the span of its slices. The continuity assumption concerns
all actual spatial jets and retains the complete Schwartz topology. -/
theorem schwartz_integral_mem_closure_span
    [FiniteDimensional ℝ E]
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (F : Y → 𝓢(E, ℂ))
    (K : Set E) (hK : IsCompact K) (hF : ∀ y, tsupport (F y) ⊆ K)
    (hjets : ∀ j : ℕ,
      Continuous (fun p : Y × E ↦ iteratedFDeriv ℝ j (F p.1) p.2))
    (f : 𝓢(E, ℂ)) (hf : ∀ x, f x = ∫ y, F y x ∂μ) :
    f ∈ (Submodule.span ℂ (Set.range F)).topologicalClosure := by
  classical
  let S := Submodule.span ℂ (Set.range F)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- Every finite linear combination retains the same compact support.
  have hspanSupport (g : 𝓢(E, ℂ)) (hg : g ∈ S) : tsupport g ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hzero : g x = 0 := by
      clear hx
      induction hg using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨y, rfl⟩ := hu
        by_contra h
        exact hxK (hF y (subset_tsupport _ h))
      | zero => rfl
      | add a b ha hb hza hzb => simp only [add_apply, hza, hzb, add_zero]
      | smul a b hb hzb => simp only [smul_apply, hzb, smul_zero]
    exact hx hzero
  have hfSupport : tsupport f ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hzero (y : Y) : F y x = 0 := by
      by_contra h
      exact hxK (hF y (subset_tsupport _ h))
    exact hx (by simp only [hf, hzero, integral_zero])
  have hderiv (j : ℕ) (x : E) :
      iteratedFDeriv ℝ j f x = ∫ y, iteratedFDeriv ℝ j (F y) x ∂μ := by
    have hfun : (f : E → ℂ) = fun z ↦ ∫ y, F y z ∂μ := funext hf
    rw [hfun]
    exact iteratedFDeriv_integral_of_continuous_jets μ isOpen_univ
      (fun y ↦ (F y).smooth ⊤ |>.contDiffOn)
      (fun k ↦ (hjets k).continuousOn) j (mem_univ x)
  -- A neighborhood imposes finitely many weighted-jet conditions.
  change f ∈ closure (S : Set 𝓢(E, ℂ))
  apply (mem_closure_iff_nhds_basis (schwartz_withSeminorms ℂ E ℂ).hasBasis_ball).mpr
  rintro ⟨s, ε⟩ hε
  let B := ∀ i : s, C(K, E [×i.val.2]→L[ℝ] ℂ)
  let J : 𝓢(E, ℂ) →L[ℂ] B :=
    ContinuousLinearMap.pi (fun i ↦ schwartzWeightedJetOn K i.val.1 i.val.2)
  have hJF : Continuous (fun y ↦ J (F y)) := by
    apply continuous_pi
    intro i
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Y × K ↦
      ‖(p.2 : E)‖ ^ i.val.1 • iteratedFDeriv ℝ i.val.2 (F p.1) p.2)
    exact ((continuous_subtype_val.comp continuous_snd).norm.pow _).smul
      ((hjets _).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hJFint : Integrable (fun y ↦ J (F y)) μ := hJF.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hJintegral : (∫ y, J (F y) ∂μ) = J f := by
    funext i
    apply ContinuousMap.ext
    intro x
    let e : B →L[ℂ] E [×i.val.2]→L[ℝ] ℂ :=
      (ContinuousMap.evalCLM ℂ x).comp (ContinuousLinearMap.proj i)
    have he := e.integral_comp_comm hJFint
    change (∫ y, ‖(x : E)‖ ^ i.val.1 •
      iteratedFDeriv ℝ i.val.2 (F y) x ∂μ) = (∫ y, J (F y) ∂μ) i x at he
    rw [← he, integral_smul]
    change ‖(x : E)‖ ^ i.val.1 • (∫ y, iteratedFDeriv ℝ i.val.2 (F y) x ∂μ) =
      ‖(x : E)‖ ^ i.val.1 • iteratedFDeriv ℝ i.val.2 f x
    rw [hderiv]
  -- Integration in a closed Banach subspace produces finite-span approximations.
  let T := S.map J.toLinearMap
  let C := T.topologicalClosure
  let G : Y → C := fun y ↦ ⟨J (F y),
    T.le_topologicalClosure ⟨F y, Submodule.subset_span ⟨y, rfl⟩, rfl⟩⟩
  have hG : Continuous G := hJF.subtype_mk _
  have hGint : Integrable G μ := hG.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hJmem : J f ∈ C := by
    have hval := C.subtypeL.integral_comp_comm hGint
    change (∫ y, J (F y) ∂μ) = ((∫ y, G y ∂μ) : C).val at hval
    rw [hJintegral] at hval
    rw [hval]
    exact (∫ y, G y ∂μ).property
  obtain ⟨z, hzT, hz⟩ := Metric.mem_closure_iff.mp hJmem ε hε
  obtain ⟨g, hg, rfl⟩ := hzT
  refine ⟨g, hg, ?_⟩
  change (s.sup (schwartzSeminormFamily ℂ E ℂ)) (g - f) < ε
  have hz' : ‖J (g - f)‖ < ε := by
    change dist (J f) (J g) < ε at hz
    rw [show dist (J f) (J g) = ‖J f - J g‖ from dist_eq_norm _ _] at hz
    simpa only [map_sub, norm_sub_rev] using hz
  apply lt_of_le_of_lt ?_ hz'
  rw [Seminorm.finset_sup_apply]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  change SchwartzMap.seminorm ℂ i.1 i.2 (g - f) ≤ ‖J (g - f)‖
  have hsupport : tsupport (g - f) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra hxK
    have hgx : g x = 0 := by
      by_contra h
      exact hxK (hspanSupport g hg (subset_tsupport _ h))
    have hfx : f x = 0 := by
      by_contra h
      exact hxK (hfSupport (subset_tsupport _ h))
    exact hx (by simp only [sub_apply, hgx, hfx, sub_self])
  rw [← norm_schwartzWeightedJetOn K i.1 i.2 (g - f) hsupport]
  exact norm_le_pi_norm (J (g - f)) ⟨i, hi⟩

/-- Multiplication by a compactly supported Schwartz function is obtained, in the full
Schwartz topology, from its plane-wave modulations. Compact Fourier amplitudes
are integrated first; Schwartz density then removes the frequency cutoff. -/
theorem schwartz_pairing_mem_closure_span_modulation (n : ℕ)
    (f u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hu : HasCompactSupport u) :
    SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f u ∈
      (Submodule.span ℂ {v : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) |
        ∃ ξ : EuclideanSpace ℝ (Fin n), ∀ x,
          v x = (Real.fourierChar (inner ℝ ξ x) : ℂ) * u x}).topologicalClosure := by
  classical
  have hcast : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  let X := EuclideanSpace ℝ (Fin n)
  let S := Submodule.span ℂ {v : 𝓢(X, ℂ) | ∃ ξ : X, ∀ x,
    v x = (Real.fourierChar (inner ℝ ξ x) : ℂ) * u x}
  let C := S.topologicalClosure
  let w : X → X → ℂ := fun ξ x ↦ (Real.fourierChar (inner ℝ ξ x) : ℂ) * u x
  have hinner (ξ : X) : ContDiff ℝ ∞ (fun x : X ↦ inner ℝ ξ x) :=
    (innerSL ℝ ξ).contDiff
  have hinnerJoint : ContDiff ℝ ∞ (fun p : X × X ↦ inner ℝ p.1 p.2) :=
    ((innerSL ℝ).contDiff.comp contDiff_fst).clm_apply contDiff_snd
  have hw (ξ : X) : ContDiff ℝ ∞ (w ξ) := by
    simp only [w, Real.fourierChar_apply]
    fun_prop
  let M (ξ : X) : 𝓢(X, ℂ) := hu.mul_left.toSchwartzMap (hw ξ)
  have hM (ξ x : X) : M ξ x = w ξ x := rfl
  have hMmem (ξ : X) : M ξ ∈ S := Submodule.subset_span ⟨ξ, hM ξ⟩
  -- The finite frequency integral is controlled simultaneously in every spatial jet.
  have hcompact (a : 𝓢(X, ℂ)) (ha : HasCompactSupport a) :
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ a) u ∈ C := by
    let K := tsupport a
    let : CompactSpace K := isCompact_iff_compactSpace.mp ha
    let μ : Measure K := Measure.comap Subtype.val (volume : Measure X)
    let : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap' volume
      continuous_subtype_val (MeasurableEmbedding.subtype_coe ha.isClosed.measurableSet)
    let F : K → 𝓢(X, ℂ) := fun ξ ↦ a ξ • M ξ
    have hF (ξ : K) : tsupport (F ξ) ⊆ tsupport u := by
      apply closure_minimal ?_ (isClosed_tsupport u)
      intro x hx
      apply subset_tsupport
      intro hux
      exact hx (by simp [F, hM, w, hux])
    let W : X × X → ℂ := fun p ↦ a p.1 * w p.1 p.2
    have hW : ContDiff ℝ ∞ W := by
      simp only [W, w, Real.fourierChar_apply]
      fun_prop
    have hjets (j : ℕ) :
        ContDiff ℝ ∞ (fun p : X × X ↦ iteratedFDeriv ℝ j (fun x ↦ W (p.1, x)) p.2) := by
      induction j with
      | zero =>
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact (continuousMultilinearCurryFin0 ℝ X ℂ).symm.contDiff.comp hW
      | succ j ih =>
        simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
        have hp : ContDiff ℝ ∞ (fun p : (X × X) × X ↦
            iteratedFDeriv ℝ j (fun x ↦ W (p.1.1, x)) p.2) :=
          ih.comp ((contDiff_fst.fst).prodMk contDiff_snd)
        have hd := hp.fderiv
          (f := fun p : X × X ↦ fun x : X ↦
            iteratedFDeriv ℝ j (fun z ↦ W (p.1, z)) x)
          (g := fun p : X × X ↦ p.2) contDiff_snd
          (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
        exact (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (j + 1) ↦ X) ℂ).symm.contDiff.comp hd
    have hFjets (j : ℕ) :
        Continuous (fun p : K × X ↦ iteratedFDeriv ℝ j (F p.1) p.2) := by
      change Continuous (fun p : K × X ↦
        iteratedFDeriv ℝ j (fun x ↦ W ((p.1 : X), x)) p.2)
      exact (hjets j).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hintegral (x : X) :
        SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ a) u x =
          ∫ ξ, F ξ x ∂μ := by
      change (𝓕⁻ a) x * u x = ∫ ξ : K,
        a ξ * ((Real.fourierChar (inner ℝ (ξ : X) x) : ℂ) * u x) ∂μ
      rw [integral_subtype_comap ha.isClosed.measurableSet
        (fun ξ : X ↦ a ξ * ((Real.fourierChar (inner ℝ ξ x) : ℂ) * u x))]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ ?_)]
      · rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
        simp only [Circle.smul_def, smul_eq_mul]
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with ξ
        ring
      · have haξ : a ξ = 0 := by
          by_contra h
          exact hξ (subset_tsupport a h)
        simp [haξ]
    have hclosure := schwartz_integral_mem_closure_span μ F (tsupport u) hu
      hF hFjets (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ a) u) hintegral
    apply (Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)) hclosure
    rintro _ ⟨ξ, rfl⟩
    exact S.smul_mem (a ξ) (hMmem ξ)
  -- Continuity of inverse Fourier transform and Schwartz multiplication removes the cutoff.
  have hall (a : 𝓢(X, ℂ)) :
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ a) u ∈ C := by
    apply (dense_hasCompactSupport_schwartz n).induction
      (P := fun a : 𝓢(X, ℂ) ↦
        SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ a) u ∈ C)
      hcompact ?_ a
    exact S.isClosed_topologicalClosure.preimage
      ((SchwartzMap.pairing_continuous_left (ContinuousLinearMap.mul ℂ ℂ) u).comp
        FourierTransform.continuous_fourierInv)
  simpa only [FourierTransform.fourierInv_fourier_eq] using hall (𝓕 f)

/-- Finite sums of separated coordinate tests are dense in the original Schwartz space.
The proof uses product plateau cutoffs and Fourier reconstruction in every
Schwartz seminorm, including all spatial weights and derivative orders. -/
theorem dense_span_schwartz_products (n m : ℕ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    Dense (Submodule.span ℂ {u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), ℂ) |
      ∃ a : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∃ b : 𝓢(EuclideanSpace ℝ (Fin m), ℂ),
        ∀ z, u z = a (e z).1 * b (e z).2} :
          Set 𝓢(EuclideanSpace ℝ (Fin (n + m)), ℂ)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  have hcast : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let S := Submodule.span ℂ {u : 𝓢(Z, ℂ) | ∃ a : 𝓢(X, ℂ), ∃ b : 𝓢(Y, ℂ),
    ∀ z, u z = a (e z).1 * b (e z).2}
  let C := S.topologicalClosure
  -- Separate plateau functions equal one on both projections of the original support.
  have hcompact (f : 𝓢(Z, ℂ)) (hf : HasCompactSupport f) : f ∈ C := by
    obtain ⟨R, hR, hKR⟩ :=
      ((hf.image e.continuous).image continuous_fst).isBounded.subset_closedBall_lt 0 (0 : X)
    obtain ⟨T, hT, hKT⟩ :=
      ((hf.image e.continuous).image continuous_snd).isBounded.subset_closedBall_lt 0 (0 : Y)
    let a : ContDiffBump (0 : X) :=
      { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
    let b : ContDiffBump (0 : Y) :=
      { rIn := T, rOut := T + 1, rIn_pos := hT, rIn_lt_rOut := by linarith }
    have haSmooth : ContDiff ℝ ∞ a := a.contDiff
    have hbSmooth : ContDiff ℝ ∞ b := b.contDiff
    let c : Z → ℂ := fun z ↦ (a (e z).1 : ℂ) * (b (e z).2 : ℂ)
    have hc : ContDiff ℝ ∞ c := by dsimp [c]; fun_prop
    have hcK : HasCompactSupport c := by
      have hK := (a.hasCompactSupport.prod b.hasCompactSupport).image e.symm.continuous
      apply hK.of_isClosed_subset (isClosed_tsupport c)
      apply closure_minimal ?_ hK.isClosed
      intro z hz
      refine ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩
      · apply subset_tsupport
        intro ha
        exact hz (by simp [c, ha])
      · apply subset_tsupport
        intro hb
        exact hz (by simp [c, hb])
    let u : 𝓢(Z, ℂ) := hcK.toSchwartzMap hc
    have hu (z : Z) : u z = c z := rfl
    have hplateau (z : Z) (hz : z ∈ tsupport f) : c z = 1 := by
      have ha : a (e z).1 = 1 := a.one_of_mem_closedBall (hKR ⟨e z, ⟨z, hz, rfl⟩, rfl⟩)
      have hb : b (e z).2 = 1 := b.one_of_mem_closedBall (hKT ⟨e z, ⟨z, hz, rfl⟩, rfl⟩)
      simp [c, ha, hb]
    have hproduct : SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f u = f := by
      apply SchwartzMap.ext
      intro z
      change f z * c z = f z
      by_cases hz : f z = 0
      · simp [hz]
      · rw [hplateau z (subset_tsupport f hz), mul_one]
    -- Each plane wave on the product splits with the same coordinate equivalence.
    have horbit (v : 𝓢(Z, ℂ))
        (hv : ∃ ξ : Z, ∀ z, v z = (Real.fourierChar (inner ℝ ξ z) : ℂ) * u z) :
        v ∈ S := by
      obtain ⟨ξ, hξ⟩ := hv
      have hinner : ContDiff ℝ ∞ (fun z : Z ↦ inner ℝ ξ z) := (innerSL ℝ ξ).contDiff
      let ax : X → ℂ := fun x ↦
        (Real.fourierChar (inner ℝ ξ (e.symm (x, 0))) : ℂ) * (a x : ℂ)
      let byFun : Y → ℂ := fun y ↦
        (Real.fourierChar (inner ℝ ξ (e.symm (0, y))) : ℂ) * (b y : ℂ)
      have hax : ContDiff ℝ ∞ ax := by
        simp only [ax, Real.fourierChar_apply]
        fun_prop
      have hby : ContDiff ℝ ∞ byFun := by
        simp only [byFun, Real.fourierChar_apply]
        fun_prop
      have hcax : HasCompactSupport ax :=
        (a.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).mul_left
      have hcby : HasCompactSupport byFun :=
        (b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).mul_left
      apply Submodule.subset_span
      refine ⟨hcax.toSchwartzMap hax, hcby.toSchwartzMap hby, ?_⟩
      intro z
      have hsplit : inner ℝ ξ z = inner ℝ ξ (e.symm ((e z).1, 0)) +
          inner ℝ ξ (e.symm (0, (e z).2)) := by
        rw [← inner_add_right, ← map_add]
        simpa only [Prod.mk_add_mk, add_zero, zero_add] using
          congrArg (fun q : Z ↦ inner ℝ ξ q) (e.symm_apply_apply z).symm
      rw [hξ, hu, hsplit, AddChar.map_add_eq_mul]
      change ((Real.fourierChar (inner ℝ ξ (e.symm ((e z).1, 0))) : ℂ) *
        (Real.fourierChar (inner ℝ ξ (e.symm (0, (e z).2))) : ℂ)) * c z =
          ax (e z).1 * byFun (e z).2
      dsimp [ax, byFun, c]
      ring
    have hle : (Submodule.span ℂ {v : 𝓢(Z, ℂ) | ∃ ξ : Z, ∀ z,
        v z = (Real.fourierChar (inner ℝ ξ z) : ℂ) * u z}).topologicalClosure ≤ C :=
      Submodule.topologicalClosure_mono (Submodule.span_le.mpr horbit)
    have hmem := hle (schwartz_pairing_mem_closure_span_modulation (n + m) f u hcK)
    rwa [hproduct] at hmem
  -- The already proved compact-support density is for the same full Schwartz topology.
  have hall (f : 𝓢(Z, ℂ)) : f ∈ C :=
    (dense_hasCompactSupport_schwartz (n + m)).induction hcompact
      S.isClosed_topologicalClosure f
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro f _
  exact hall f

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzKernelConstruction
public import AtiyahSinger.Analysis.SchwartzRealWindow
public import AtiyahSinger.Analysis.SchwartzTensor
public import AtiyahSinger.Analysis.SchwartzTensorDensity
public import Mathlib.Analysis.Distribution.Support

/-!
# Actual tempered Schwartz kernels and conjugate transposition

Public module ID: M0944.

A scalar Schwartz kernel is a continuous complex-linear functional on the
Schwartz space of the product, not merely a bilinear form on separate tests.
The Schwartz kernel theorem extends the latter to that actual distribution.
The external tensor tests below retain their literal function values.
Conjugate transposition swaps the two spatial variables and conjugates both
the test and the resulting scalar, preserving complex linearity.

The Schwartz kernel theorem is a standard additional analysis input for the
Schwartz-kernel formulation of SG III.13.4. The product-test representation
and conjugate-transposition formulas are explicit implementation bridges.
Full Schwartz tensor density gives uniqueness; a continuous windowed Fourier
reconstruction with explicit seminorm-integrability bounds constructs the
kernel itself.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ComplexConjugate ContDiff SchwartzMap

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- Elementary tensor tests determine an actual tempered distribution uniquely. -/
theorem temperedKernel_ext (K L : 𝓢'(V × V, ℂ))
    (h : ∀ φ ψ : 𝓢(V, ℂ), K (schwartzTensor φ ψ) = L (schwartzTensor φ ψ)) :
    K = L := by
  -- Pull the actual product tests back along the fixed Euclidean coordinate equivalence.
  let Z := EuclideanSpace ℝ (Fin (n + n))
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := n)
  let J : 𝓢(Z, ℂ) →L[ℂ] 𝓢(V × V, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  have hgenerators : Set.EqOn (K.comp J).toLinearMap (L.comp J).toLinearMap
      {u : 𝓢(Z, ℂ) | ∃ φ ψ : 𝓢(V, ℂ), ∀ z,
        u z = φ (e z).1 * ψ (e z).2} := by
    rintro u ⟨φ, ψ, hu⟩
    have htensor : J u = schwartzTensor φ ψ := by
      apply SchwartzMap.ext
      intro z
      change u (e.symm z) = schwartzTensor φ ψ z
      rw [hu, schwartzTensor_apply, e.apply_symm_apply]
    change K (J u) = L (J u)
    rw [htensor]
    exact h φ ψ
  -- Linearity gives agreement on the span, and Schwartz density extends it to all tests.
  have hspan := LinearMap.eqOn_span' hgenerators
  have hall (u : 𝓢(Z, ℂ)) : K (J u) = L (J u) :=
    (dense_span_schwartz_products n n).induction
      (fun v hv ↦ hspan hv) (isClosed_eq (K.comp J).continuous (L.comp J).continuous) u
  apply DFunLike.ext
  intro f
  let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hu : J u = f := by
    apply SchwartzMap.ext
    intro z
    change f (e (e.symm z)) = f z
    rw [e.apply_symm_apply]
  simpa only [hu] using hall u

/-- Schwartz kernel theorem: a continuous bilinear test pairing has a unique actual kernel. -/
theorem existsUnique_temperedKernel
    (b : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) →ₗ[ℂ] ℂ)
    (hb : Continuous (fun z : 𝓢(V, ℂ) × 𝓢(V, ℂ) ↦ b z.1 z.2)) :
    ∃! K : 𝓢'(V × V, ℂ),
      ∀ φ ψ : 𝓢(V, ℂ), K (schwartzTensor φ ψ) = b φ ψ := by
  -- A real compact plateau gives a nonzero normalization in every dimension.
  obtain ⟨g, hg, _, hmass⟩ := exists_real_schwartzWindow n
  obtain ⟨K, hK⟩ := exists_temperedKernel_of_schwartzWindow g hg hmass b hb
  refine ⟨K, hK, ?_⟩
  -- The constructed continuous kernel is determined by its original tensor tests.
  intro L hL
  apply temperedKernel_ext
  intro φ ψ
  exact (hL φ ψ).trans (hK φ ψ).symm

/-- Local vanishing on all separated tests detects the actual distributional support.
Product plateau cutoffs reduce the local assertion to global Schwartz tensor
density, so the conclusion concerns all supported tests, not only tensors. -/
theorem notMem_dsupport_of_tensor_tests (K : 𝓢'(V × V, ℂ))
    {s t : Set V} (hs : IsOpen s) (ht : IsOpen t) (z : V × V)
    (hz : z ∈ s ×ˢ t)
    (h : ∀ φ ψ : 𝓢(V, ℂ), tsupport φ ⊆ s → tsupport ψ ⊆ t →
      K (schwartzTensor φ ψ) = 0) : z ∉ Distribution.dsupport K := by
  classical
  -- Choose one plateau bump in each of the specified coordinate neighborhoods.
  obtain ⟨R, hR, hRs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz.1)
  obtain ⟨T, hT, hTt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ht.mem_nhds hz.2)
  let a : ContDiffBump z.1 :=
    { rIn := R / 2, rOut := R, rIn_pos := half_pos hR,
      rIn_lt_rOut := half_lt_self hR }
  let b : ContDiffBump z.2 :=
    { rIn := T / 2, rOut := T, rIn_pos := half_pos hT,
      rIn_lt_rOut := half_lt_self hT }
  let a' : 𝓢(V, ℂ) :=
    (a.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp a.contDiff)
  let b' : 𝓢(V, ℂ) :=
    (b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have has : tsupport a' ⊆ s := by
    apply (tsupport_comp_subset (g := Complex.ofReal) rfl a).trans
    rwa [a.tsupport_eq]
  have hbt : tsupport b' ⊆ t := by
    apply (tsupport_comp_subset (g := Complex.ofReal) rfl b).trans
    rwa [b.tsupport_eq]
  let g := schwartzTensor a' b'
  let J : 𝓢(V × V, ℂ) →L[ℂ] 𝓢(V × V, ℂ) := SchwartzMap.smulLeftCLM ℂ g
  have hzero : K.comp J = 0 := by
    apply temperedKernel_ext
    intro φ ψ
    let φ' := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) a' φ
    let ψ' := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) b' ψ
    have hφ : tsupport φ' ⊆ s := tsupport_mul_subset_left.trans has
    have hψ : tsupport ψ' ⊆ t := tsupport_mul_subset_left.trans hbt
    have hproduct : J (schwartzTensor φ ψ) = schwartzTensor φ' ψ' := by
      apply SchwartzMap.ext
      intro w
      rw [show J (schwartzTensor φ ψ) w = g w * schwartzTensor φ ψ w from
        SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth _ _]
      simp only [g, schwartzTensor_apply]
      change (a' w.1 * b' w.2) * (φ w.1 * ψ w.2) =
        (a' w.1 * φ w.1) * (b' w.2 * ψ w.2)
      ring
    change K (J (schwartzTensor φ ψ)) = 0
    rw [hproduct]
    exact h φ' ψ' hφ hψ
  -- The product multiplier equals one on an open neighborhood of the original point.
  apply (Distribution.notMem_dsupport_iff z).mpr
  refine ⟨Metric.ball z.1 a.rIn ×ˢ Metric.ball z.2 b.rIn, ?_,
    Metric.isOpen_ball.prod Metric.isOpen_ball, ?_⟩
  · intro f hf
    have hJf : J f = f := by
      apply SchwartzMap.ext
      intro w
      rw [show J f w = g w * f w from
        SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth _ _]
      by_cases hw : f w = 0
      · simp [hw]
      · have hw' := hf (subset_tsupport f hw)
        have ha : a w.1 = 1 := a.one_of_mem_closedBall (Metric.ball_subset_closedBall hw'.1)
        have hb : b w.2 = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hw'.2)
        rw [show g w = a' w.1 * b' w.2 from schwartzTensor_apply a' b' w]
        change ((a w.1 : ℂ) * (b w.2 : ℂ)) * f w = f w
        simp [ha, hb]
    have heval := congrArg (fun P : 𝓢'(V × V, ℂ) ↦ P f) hzero
    change K (J f) = 0 at heval
    rwa [hJf] at heval
  · exact ⟨Metric.mem_ball_self a.rIn_pos, Metric.mem_ball_self b.rIn_pos⟩

/-- Pointwise complex conjugation on an actual Schwartz function. -/
def schwartzConj {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : 𝓢(D, ℂ)) : 𝓢(D, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f

/-- Conjugate the test after the actual continuous-linear swap of the two variables. -/
def schwartzConjSwap (f : 𝓢(V × V, ℂ)) : 𝓢(V × V, ℂ) :=
  schwartzConj
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ V V) f)

/-- The double conjugation defining kernel transposition is complex linear and continuous. -/
theorem temperedConjSwap_properties (K : 𝓢'(V × V, ℂ)) :
    IsLinearMap ℂ (fun f : 𝓢(V × V, ℂ) ↦ conj (K (schwartzConjSwap f))) ∧
      Continuous (fun f : 𝓢(V × V, ℂ) ↦ conj (K (schwartzConjSwap f))) := by
  /- The test swap is continuous and complex linear; test conjugation is
  continuous and conjugate-linear. The actual K is continuous and complex
  linear. Conjugating its output a second time restores complex linearity.
  Composition supplies continuity on the existing Schwartz topology. -/
  -- The inner conjugation is conjugate-linear on the original test space.
  have hadd (f g : 𝓢(V × V, ℂ)) :
      schwartzConjSwap (f + g) = schwartzConjSwap f + schwartzConjSwap g := by
    ext z
    change conj (f z.swap + g z.swap) = conj (f z.swap) + conj (g z.swap)
    exact map_add _ _ _
  have hsmul (a : ℂ) (f : 𝓢(V × V, ℂ)) :
      schwartzConjSwap (a • f) = conj a • schwartzConjSwap f := by
    ext z
    change conj (a * f z.swap) = conj a * conj (f z.swap)
    exact map_mul _ _ _
  constructor
  · constructor
    · intro f g
      simp only [hadd, map_add]
    · intro a f
      simp only [hsmul, map_smul, smul_eq_mul, map_mul, starRingEnd_self_apply]
  · -- Each factor is an existing continuous map on the Schwartz topology.
    exact Complex.continuous_conj.comp
      (K.continuous.comp
        ((SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap).continuous.comp
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (ContinuousLinearEquiv.prodComm ℝ V V)).continuous))

/-- The actual conjugate-transposed tempered distribution, retaining its test action. -/
def temperedConjSwap (K : 𝓢'(V × V, ℂ)) : 𝓢'(V × V, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
    { toLinearMap := IsLinearMap.mk'
        (fun f : 𝓢(V × V, ℂ) ↦ conj (K (schwartzConjSwap f)))
        (temperedConjSwap_properties K).1
      cont := (temperedConjSwap_properties K).2 }

/-- Conjugate transposition swaps the actual distributional support. -/
theorem dsupport_temperedConjSwap (K : 𝓢'(V × V, ℂ)) :
    Distribution.dsupport (temperedConjSwap K) = Prod.swap '' Distribution.dsupport K := by
  /- A test and its conjugate have the same support, and precomposition
  by the swap carries support by that homeomorphism. Thus the transposed
  kernel vanishes on an open set precisely when K vanishes on its swapped
  open set. Apply the defining open-vanishing characterization of dsupport
  in both directions; conjugate transposition is its own inverse. -/
  -- Swapping and conjugating a test is involutive and transports its support.
  have hinv (f : 𝓢(V × V, ℂ)) : schwartzConjSwap (schwartzConjSwap f) = f := by
    ext z
    change conj (conj (f z)) = f z
    simp
  have hsupp (f : 𝓢(V × V, ℂ)) :
      tsupport (schwartzConjSwap f) ⊆ Prod.swap ⁻¹' tsupport f := by
    apply closure_minimal ?_ ((isClosed_tsupport f).preimage continuous_swap)
    intro z hz
    apply subset_closure
    intro hf
    apply hz
    change conj (f z.swap) = 0
    simp [hf]
  have hvan (U : Set (V × V)) :
      Distribution.IsVanishingOn (temperedConjSwap K) U ↔
        Distribution.IsVanishingOn K (Prod.swap ⁻¹' U) := by
    constructor
    · intro h f hf
      have hzero := h (schwartzConjSwap f) (by
        intro z hz
        exact hf (hsupp f hz))
      change conj (K (schwartzConjSwap (schwartzConjSwap f))) = 0 at hzero
      simpa only [hinv, map_eq_zero] using hzero
    · intro h f hf
      change conj (K (schwartzConjSwap f)) = 0
      rw [h (schwartzConjSwap f) (fun z hz ↦ hf (hsupp f hz)), map_zero]
  -- The open-neighborhood characterization determines exactly the swapped support.
  have hnot (z : V × V) :
      z ∉ Distribution.dsupport (temperedConjSwap K) ↔
        z.swap ∉ Distribution.dsupport K := by
    rw [Distribution.notMem_dsupport_iff, Distribution.notMem_dsupport_iff]
    constructor
    · rintro ⟨U, hU, hopen, hz⟩
      exact ⟨Prod.swap ⁻¹' U, (hvan U).mp hU, hopen.preimage continuous_swap, hz⟩
    · rintro ⟨U, hU, hopen, hz⟩
      refine ⟨Prod.swap ⁻¹' U, (hvan _).mpr ?_, hopen.preimage continuous_swap, hz⟩
      simpa [Set.preimage_preimage, Function.comp_def] using hU
  ext z
  rw [← not_iff_not, hnot]
  simp only [Set.mem_image]
  constructor
  · intro h hmem
    obtain ⟨w, hw, rfl⟩ := hmem
    exact h hw
  · intro h hz
    exact h ⟨z.swap, hz, Prod.swap_swap z⟩

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexConnection
public import AtiyahSinger.Geometry.SmoothConnectionExistence

/-!
# Smooth complex connections and extension of prescribed local connections

Public module ID: M1141.

E01: existence on the original smooth complex bundle, and extension agreeing
with a specified local connection on a closed region. The base need not be
compact. The relative statement uses a closed/open neighborhood buffer and
fixes the derivative of every differentiable section germ there.

Sources: HU XIX.2.1 for complex covariant derivatives and XIX.4.3 for their
affine structure; SG III.13.3, p.246, for connections preserving prescribed
exterior frames. The locally finite partition-of-unity construction and this
general relative formulation are explicit project supplements. The same
native real covariant derivative is required to be complex linear; neither a
Hermitian compatibility conclusion nor a Dirac construction is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Topology ContinuousLinearMap
open scoped Manifold ContDiff

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hM hT hSC hE

/-- A smooth complex bundle on the given manifold admits a smooth complex connection. -/
theorem exists_smooth_complex_connection :
    ∃ cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℂ (Fin r)) E,
      CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ∧
        IsComplexLinearConnectionOn (n := n) (r := r) E cov := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let F := EuclideanSpace ℂ (Fin r)
  -- Complex scalar multiplication is real-smooth in the original complex frames.
  have hscalarDiff (σ : ∀ x, E x) (x : M)
      (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F))
        (fun y ↦ (⟨y, σ y⟩ : TotalSpace F E)) x) (c : ℂ) :
      MDifferentiableAt I (I.prod 𝓘(ℝ, F))
        (fun y ↦ (⟨y, c • σ y⟩ : TotalSpace F E)) x := by
    let e := trivializationAt F E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
    rw [e.mdifferentiableAt_section_iff I _ hx] at hσ ⊢
    have hscale := ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ).contMDiff
      (n := (1 : WithTop ℕ∞)) |>.mdifferentiable (by simp)
    apply (hscale.mdifferentiableAt.comp x hσ).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact (e.linearEquivAt ℂ y hy).map_smul c (σ y)
  have hscalarSmooth (σ : ∀ x, E x)
      (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (fun y ↦ (⟨y, σ y⟩ : TotalSpace F E))) (c : ℂ) :
      ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (fun y ↦ (⟨y, c • σ y⟩ : TotalSpace F E)) := by
    intro x
    let e := trivializationAt F E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
    apply (e.contMDiffAt_section_iff hx).mpr
    have hσc := (e.contMDiffAt_section_iff hx).mp (hσ x)
    have hscale := ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ).contMDiff
      (n := (∞ : WithTop ℕ∞))
    apply (hscale.contMDiffAt.comp x hσc).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact (e.linearEquivAt ℂ y hy).map_smul c (σ y)
  -- The same frame calculation controls complex scaling in the native real Hom bundle.
  have hhomScalar (A : ∀ x : M, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] E x)
      (s : Set M)
      (hA : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin r))) ∞
        (fun x ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℂ (Fin r)) x (A x)) s)
      (c : ℂ) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin r))) ∞
        (fun x ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℂ (Fin r)) x (c • A x)) s := by
    intro x hx
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoords (y : M) (hy : y ∈ e.baseSet) :
        inCoordinates (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (EuclideanSpace ℂ (Fin r)) E x y x y (c • A y) =
        c • inCoordinates (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (EuclideanSpace ℂ (Fin r)) E x y x y (A y) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [inCoordinates, comp_apply, smul_apply]
      rw [e.continuousLinearMapAt_apply_of_mem ℝ hy,
        e.continuousLinearMapAt_apply_of_mem ℝ hy]
      exact (e.linear ℂ hy).map_smul c _
    apply (contMDiffWithinAt_hom_bundle _).mpr
    refine ⟨contMDiffWithinAt_id, ?_⟩
    let C : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin r)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin r)) :=
      c • ContinuousLinearMap.id ℝ _
    have h := C.contMDiff.contMDiffAt.comp_contMDiffWithinAt x
      ((contMDiffWithinAt_hom_bundle _).mp (hA x hx)).2
    apply h.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds he)] with y _ hy
      exact hcoords y hy
    · exact hcoords x he
  -- Project a real connection onto its complex-linear part. Both the input and output
  -- actions below are the given complex scalar action on the original fibers.
  obtain ⟨realCov, hreal⟩ := exists_smooth_covariantDerivative (n := n) F E
  let complexCov (σ : ∀ x, E x) (x : M) : TangentSpace I x →L[ℝ] E x :=
    (1 / 2 : ℂ) • (realCov σ x - Complex.I • realCov (Complex.I • σ) x)
  -- Averaging preserves additivity and the real Leibniz term because I squared is -1.
  have hcov : IsCovariantDerivativeOn F complexCov Set.univ := by
    constructor
    · intro σ τ x hσ hτ _
      have hIσ := hscalarDiff σ x hσ Complex.I
      have hIτ := hscalarDiff τ x hτ Complex.I
      dsimp only [complexCov]
      rw [realCov.isCovariantDerivativeOnUniv.add hσ hτ, smul_add,
        realCov.isCovariantDerivativeOnUniv.add (σ := Complex.I • σ)
          (σ' := Complex.I • τ) hIσ hIτ]
      module
    · intro σ g x hσ hg _
      have hIσ := hscalarDiff σ x hσ Complex.I
      have hcomm : Complex.I • (g • σ) = g • (Complex.I • σ) := by
        ext y
        exact smul_comm Complex.I (g y) (σ y)
      dsimp only [complexCov]
      rw [realCov.isCovariantDerivativeOnUniv.leibniz hσ hg, hcomm,
        realCov.isCovariantDerivativeOnUniv.leibniz (σ := Complex.I • σ) hIσ hg]
      ext v
      simp only [smul_apply, sub_apply, add_apply, ContinuousLinearMap.smulRight_apply,
        Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      match_scalars <;> apply Complex.ext <;> simp <;> ring
  refine ⟨⟨complexCov, hcov⟩, ?_, ?_⟩
  · -- Smooth input sections remain smooth under I and under the averaged connection.
    refine ⟨⟨?_⟩⟩
    intro σ hσ
    simp only [show (∞ : WithTop ℕ∞) + 1 = ∞ by simp] at hσ
    have hIσ := hscalarSmooth σ (contMDiffOn_univ.mp hσ) Complex.I
    have hrealσ := hreal.contMDiff.contMDiff (by simpa using hσ)
    have hrealIσ := hreal.contMDiff.contMDiff (σ := Complex.I • σ)
      (by simpa using hIσ.contMDiffOn (s := Set.univ))
    have hIout := hhomScalar (realCov (Complex.I • σ)) Set.univ hrealIσ Complex.I
    exact hhomScalar (fun x ↦ realCov σ x - Complex.I • realCov (Complex.I • σ) x)
      Set.univ (hrealσ.sub_section hIout) (1 / 2)
  · -- Split the complex scalar into real and imaginary parts before using real linearity.
    intro σ x hσ _ c v
    have hIσ := hscalarDiff σ x hσ Complex.I
    have hdecomp (z : ℂ) : z • σ = z.re • σ + z.im • (Complex.I • σ) := by
      ext y
      simp only [Pi.smul_apply, Pi.add_apply,
        RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, ← add_smul]
      exact congrArg (fun z : ℂ ↦ z • σ y) (Complex.re_add_im z).symm
    have hrealScalar (z : ℂ) : realCov (z • σ) x =
        z.re • realCov σ x + z.im • realCov (Complex.I • σ) x := by
      rw [hdecomp, realCov.isCovariantDerivativeOnUniv.add
        (σ := z.re • σ) (σ' := z.im • (Complex.I • σ))
        (hσ.smul_const_section) (hIσ.smul_const_section),
        realCov.isCovariantDerivativeOnUniv.smul_const z.re hσ,
        realCov.isCovariantDerivativeOnUniv.smul_const (σ := Complex.I • σ) z.im hIσ]
    change complexCov (c • σ) x v = c • complexCov σ x v
    dsimp only [complexCov]
    have hinside : Complex.I • (c • σ) = (Complex.I * c) • σ := smul_smul _ _ _
    rw [hinside, hrealScalar c, hrealScalar (Complex.I * c)]
    simp only [smul_apply, sub_apply, add_apply, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    match_scalars <;> apply Complex.ext <;> simp <;> ring

/-- Extend a prescribed smooth local complex connection while fixing a closed region. -/
theorem exists_smooth_complex_connection_relative
    (A U : Set M) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (localCov : (∀ x : M, E x) → ∀ x : M,
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] E x)
    (hlocal : IsCovariantDerivativeOn (EuclideanSpace ℂ (Fin r)) localCov U)
    (hsmooth : ContMDiffCovariantDerivativeOn (EuclideanSpace ℂ (Fin r)) ∞ localCov U)
    (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E localCov U) :
    ∃ cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℂ (Fin r)) E,
      CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ∧
        IsComplexLinearConnectionOn (n := n) (r := r) E cov ∧
          ∀ (s : ∀ x : M, E x) (x : M), x ∈ A →
            MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r)))
              (fun y ↦ (⟨y, s y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x →
            cov s x = localCov s x := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let F := EuclideanSpace ℂ (Fin r)
  -- Smooth Urysohn separation provides a closed-support cutoff inside U, even when
  -- A is noncompact. Its value is one on a neighborhood of A.
  obtain ⟨globalCov, hglobalSmooth, hglobalComplex⟩ :=
    exists_smooth_complex_connection (n := n) (r := r) E
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    I hU.isClosed_compl hA
    (Set.disjoint_left.mpr fun _ hxU hxA ↦ hxU (hAU hxA)) (n := (⊤ : ℕ∞))
  have hsupport : tsupport χ ⊆ U := by
    intro x hx
    by_contra hxU
    have hz : (χ : M → ℝ) =ᶠ[nhds x] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hxU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  have honeA (x : M) (hx : x ∈ A) : χ x = 1 := hone.self_of_nhdsSet x hx
  have houtside (x : M) (hx : x ∉ U) : χ x = 0 := by
    exact image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hsupport ht))
  -- Use an affine combination on U; where the cutoff vanishes it is the global connection.
  let splice (σ : ∀ x, E x) (x : M) : TangentSpace I x →L[ℝ] E x :=
    χ x • localCov σ x + (1 - χ x) • globalCov σ x
  have hon : IsCovariantDerivativeOn F splice U :=
    hlocal.affine_combination globalCov.isCovariantDerivativeOn (χ : M → ℝ)
  have hsplice : IsCovariantDerivativeOn F splice Set.univ := by
    constructor
    · intro σ τ x hσ hτ _
      by_cases hx : x ∈ U
      · exact hon.add hσ hτ hx
      · simp only [splice, houtside x hx, zero_smul, sub_zero, one_smul, zero_add]
        exact globalCov.isCovariantDerivativeOnUniv.add hσ hτ
    · intro σ g x hσ hg _
      by_cases hx : x ∈ U
      · exact hon.leibniz hσ hg hx
      · simp only [splice, houtside x hx, zero_smul, sub_zero, one_smul, zero_add]
        exact globalCov.isCovariantDerivativeOnUniv.leibniz hσ hg
  refine ⟨⟨splice, hsplice⟩, ?_, ?_, ?_⟩
  · -- The local weighted term extends smoothly by zero before adding the global term.
    refine ⟨⟨?_⟩⟩
    intro σ hσ
    have hlocalWeighted := ContMDiffOn.smul_section_of_tsupport
      χ.contMDiff.contMDiffOn hU hsupport (hsmooth.contMDiff (hσ.mono (Set.subset_univ U)))
    have hglobal := contMDiffOn_univ.mp (hglobalSmooth.contMDiff.contMDiff hσ)
    have hglobalWeighted := ((contMDiff_const (c := (1 : ℝ))).sub χ.contMDiff).smul_section hglobal
    exact (hlocalWeighted.add_section hglobalWeighted).contMDiffOn
  · intro σ x hσ _ c v
    change splice (fun y ↦ c • σ y) x v = c • splice σ x v
    by_cases hx : x ∈ U
    · simp only [splice, add_apply, smul_apply]
      rw [hcomplex σ x hσ hx c v, hglobalComplex σ x hσ (Set.mem_univ x) c v]
      module
    · simp only [splice, houtside x hx, zero_smul, sub_zero, one_smul, zero_add]
      exact hglobalComplex σ x hσ (Set.mem_univ x) c v
  · -- The same specified local derivative is recovered wherever the cutoff is one.
    intro σ x hx _
    change splice σ x = localCov σ x
    simp [splice, honeA x hx]

end AtiyahSinger

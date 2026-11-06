/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FormalTransposeCalculus
public import AtiyahSinger.Analysis.PseudodifferentialKernel

/-!
# Smooth representatives of the weak PDO transpose kernel

Public module ID: M0902.

A06/A07: extend SG III.5.2(ii), diagram (5.1), to the existing real-order PDO
parametrix interface. Only the original right smoothing error is needed for
smoothness of the weak transpose kernel. Finiteness and Fredholmness below use
both errors. All comparisons preserve the actual dual-section embeddings;
no Hermitian identification or abstract dimension-selected isomorphism is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The original smooth dual embedding carries the formal-transpose kernel into the weak kernel. -/
theorem dualSmoothToSobolev_mem_ker_sobolevTranspose (s : ℝ)
    (β : P.formalTranspose.toLinearMap.ker) :
    B.dualSmoothToSobolev (-(s - m)) ((dualSectionsEquiv F).symm β.val) ∈
      (P.sobolevTranspose A B s).ker := by
  /- Use the smooth-input transpose identity, after writing the common dual
  section through dualSectionsEquiv. Its image under the smooth transpose is
  zero, so its embedded image under the weak transpose is also zero. -/
  change P.sobolevTranspose A B s _ = 0
  rw [P.sobolevTranspose_smooth, LinearEquiv.apply_symm_apply, β.property,
    map_zero, map_zero]

/-- Restrict the actual smooth dual embedding to the two transpose kernels. -/
def sobolevTransposeKerMap (s : ℝ) :
    P.formalTranspose.toLinearMap.ker →ₗ[ℂ] (P.sobolevTranspose A B s).ker :=
  (((B.dualSmoothToSobolev (-(s - m))).comp (dualSectionsEquiv F).symm.toLinearMap).comp
    P.formalTranspose.toLinearMap.ker.subtype).codRestrict
      (P.sobolevTranspose A B s).ker (P.dualSmoothToSobolev_mem_ker_sobolevTranspose A B s)

/-- The restricted map retains the original smooth covector, in the independent dual completion. -/
theorem sobolevTransposeKerMap_apply (s : ℝ) (β : P.formalTranspose.toLinearMap.ker) :
    (P.sobolevTransposeKerMap A B s β).val =
      B.dualSmoothToSobolev (-(s - m)) ((dualSectionsEquiv F).symm β.val) := by
  /- Project the codomain restriction. Its forward formula is precisely the
  inverse smooth-section identification followed by the given dual embedding. -/
  rfl

/-- Injectivity of the dual embedding gives injectivity on the smooth transpose kernel. -/
theorem sobolevTransposeKerMap_injective (s : ℝ) :
    Function.Injective (P.sobolevTransposeKerMap A B s) := by
  /- Project an equality of kernel vectors to the ambient dual completion.
  Injectivity of dualSmoothToSobolev and of dualSectionsEquiv.symm identifies
  the original smooth sections; subtype extensionality finishes the argument. -/
  intro β γ h
  apply Subtype.ext
  apply (dualSectionsEquiv F).symm.injective
  apply B.dualSmoothToSobolev_injective (-(s - m))
  exact congrArg Subtype.val h

variable (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))

/-- A right smoothing inverse gives one smooth representative of each weak transpose zero. -/
theorem existsUnique_smooth_of_sobolevTranspose_eq_zero_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) (α : B.DualSobolevSpace (-(s - m)))
    (hα : P.sobolevTranspose A B s α = 0) :
    ∃! β : smoothSections (n := n) (r := q) (DualBundle F),
      B.dualSmoothToSobolev (-(s - m)) ((dualSectionsEquiv F).symm β) = α ∧
        P.formalTranspose.toLinearMap β = 0 := by
  /- Stage 1: transpose the right error P Q-I. The resulting Q^t P^t-I is
  a left smooth-kernel error for P^t, and Q^t has order -m.
  Stage 2: dualSobolevEquiv_transpose transports α to the common dual-bundle
  Sobolev model. Normalize -(s-m)-m=-s. The equal-order inclusion is injective,
  so hα gives zero under the actual common realization of P^t.
  Stage 3: apply its left-parametrix smooth lifting with right-hand side zero.
  Compatibility of the two dual embeddings gives the displayed representative.
  Injectivity gives uniqueness for this fixed α, not uniqueness of solutions of P. -/
  -- Transfer the right error to a left smoothing error on the same dual bundle.
  have hQt := P.isSmoothingOperator_formalTranspose_comp_sub_id Q hQ
  have hzero : P.formalTranspose.sobolevExtension B.dualPresentation
      A.dualPresentation (-(s - m)) (B.dualSobolevEquiv (-(s - m)) α) = 0 := by
    apply A.dualPresentation.sobolevInclusion_injective (-(s - m) - m) (-s)
      (by linarith)
    have h := P.dualSobolevEquiv_transpose A B s α
    rw [hα, map_zero] at h
    simpa only [map_zero] using h.symm
  -- The original smooth lifting theorem applies to this fixed weak kernel vector.
  obtain ⟨β, ⟨hβ, hPβ⟩, _⟩ :=
    P.formalTranspose.existsUnique_smooth_lift_of_isSmoothingOperator Q.formalTranspose
      B.dualPresentation A.dualPresentation hQt (-(s - m))
        (B.dualSobolevEquiv (-(s - m)) α) 0 (by simpa only [map_zero] using hzero)
  have hrep : B.dualSmoothToSobolev (-(s - m)) ((dualSectionsEquiv F).symm β) = α := by
    apply (B.dualSobolevEquiv (-(s - m))).injective
    rw [B.dualSobolevEquiv_smooth, LinearEquiv.apply_symm_apply]
    exact hβ
  refine ⟨β, ⟨hrep, hPβ⟩, ?_⟩
  -- Uniqueness concerns the representative of α, using the specified injective embedding.
  intro γ hγ
  apply (dualSectionsEquiv F).symm.injective
  exact B.dualSmoothToSobolev_injective (-(s - m)) (hγ.1.trans hrep.symm)

/-- The original right smoothing error makes the transpose-kernel embedding surjective. -/
theorem sobolevTransposeKerMap_surjective_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) : Function.Surjective (P.sobolevTransposeKerMap A B s) := by
  /- Apply the preceding smooth lifting to the ambient value of each weak
  kernel vector. Its smooth representative lies in the formal-transpose kernel,
  and the forward formula identifies its image with the specified weak vector. -/
  intro α
  obtain ⟨β, ⟨hβ, hPβ⟩, _⟩ :=
    P.existsUnique_smooth_of_sobolevTranspose_eq_zero_of_isSmoothingOperator
      A B Q hQ s α.val α.property
  refine ⟨⟨β, hPβ⟩, ?_⟩
  apply Subtype.ext
  exact hβ

/-- A right smoothing inverse identifies the two kernels by their natural embedding. -/
def sobolevTransposeKerEquiv
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) : P.formalTranspose.toLinearMap.ker ≃ₗ[ℂ] (P.sobolevTranspose A B s).ker :=
  LinearEquiv.ofBijective (P.sobolevTransposeKerMap A B s)
    ⟨P.sobolevTransposeKerMap_injective A B s,
      P.sobolevTransposeKerMap_surjective_of_isSmoothingOperator A B Q hQ s⟩

/-- The weak transpose kernel and the smooth formal-transpose kernel have the same dimension. -/
theorem finrank_ker_sobolevTranspose_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) : Module.finrank ℂ (P.sobolevTranspose A B s).ker =
      Module.finrank ℂ P.formalTranspose.toLinearMap.ker := by
  /- Apply dimension invariance to the natural transpose-kernel equivalence.
  This step does not use cokernel duality or assume two-sided Fredholmness. -/
  exact (P.sobolevTransposeKerEquiv A B Q hQ s).finrank_eq.symm

include A B in
/-- A two-sided parametrix makes the original smooth formal-transpose kernel finite-dimensional. -/
theorem finiteDimensional_ker_formalTranspose_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    FiniteDimensional ℂ P.formalTranspose.toLinearMap.ker := by
  /- Transfer hQ to the two transposed PDOs. Apply the previously stated smooth
  kernel finiteness theorem to P^t with presentations B.dualPresentation and
  A.dualPresentation and parametrix Q^t. No cokernel dimension formula is used. -/
  exact P.formalTranspose.finiteDimensional_ker_of_isParametrix
    B.dualPresentation A.dualPresentation Q.formalTranspose
      (P.isParametrix_formalTranspose Q hQ)

/-- The weak transpose is Fredholm on its specified opposite-order completions. -/
theorem isFredholm_sobolevTranspose_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    (P.sobolevTranspose A B s).IsFredholm := by
  /- Stage 1: the transposed parametrix gives Fredholmness for the common
  dual-bundle realization of P^t at order -(s-m).
  Stage 2: the transpose comparison diagram transports it through the two
  dualSobolevEquiv isometries and the equal-order target isomorphism. These
  preserve closed range and finite kernel/cokernel, giving exactly the weak map. -/
  -- First obtain Fredholmness of the actual common dual-bundle realization.
  have hFred := P.formalTranspose.isFredholm_sobolevExtension_of_isParametrix
    Q.formalTranspose B.dualPresentation A.dualPresentation
      (P.isParametrix_formalTranspose Q hQ) (-(s - m))
  -- An inclusion between equal orders is precisely the identity after that equality.
  have hinclusion (t u : ℝ) (htu : t = u) :
      Function.Bijective (A.dualPresentation.sobolevInclusion t u (by linarith)) := by
    subst u
    have hid : A.dualPresentation.sobolevInclusion t t (by rfl) =
        ContinuousLinearMap.id ℂ (A.dualPresentation.SobolevSpace t) := by
      apply DFunLike.coe_injective
      apply (A.dualPresentation.denseRange_smoothToSobolev t).equalizer
        (A.dualPresentation.sobolevInclusion t t (by rfl)).continuous continuous_id
      funext v
      exact A.dualPresentation.sobolevInclusion_smoothToSobolev t t (by rfl) v
    rw [hid]
    exact Function.bijective_id
  let e := ContinuousLinearEquiv.ofBijective
    (A.dualPresentation.sobolevInclusion (-(s - m) - m) (-s) (by linarith))
      (LinearMap.ker_eq_bot.mpr (hinclusion (-(s - m) - m) (-s) (by ring)).1)
      (LinearMap.range_eq_top.mpr (hinclusion (-(s - m) - m) (-s) (by ring)).2)
  let a := (A.dualSobolevEquiv (-s)).toContinuousLinearEquiv
  let b := (B.dualSobolevEquiv (-(s - m))).toContinuousLinearEquiv
  have hdiagram : a.toContinuousLinearMap.comp (P.sobolevTranspose A B s) =
      e.toContinuousLinearMap.comp
        ((P.formalTranspose.sobolevExtension B.dualPresentation
          A.dualPresentation (-(s - m))).comp b.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro α
    exact P.dualSobolevEquiv_transpose A B s α
  -- These specified isomorphisms preserve closed range, finite kernel and finite cokernel.
  have htransport : (a.toContinuousLinearMap.comp (P.sobolevTranspose A B s)).IsFredholm := by
    rw [hdiagram]
    simpa only [ContinuousLinearMap.isFredholm_equiv_comp,
      ContinuousLinearMap.isFredholm_comp_equiv] using hFred
  exact ContinuousLinearMap.isFredholm_equiv_comp.mp htransport

end PseudodifferentialOperator

end AtiyahSinger

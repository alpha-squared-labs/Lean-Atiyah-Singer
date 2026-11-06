/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SobolevParametrix

/-!
# Smooth and Sobolev kernels for real-order PDOs

Public module ID: M0895.

A06/A07: the kernel part of SG III.5.2, using the existing actual PDO parametrix
and regularity interfaces. Kernel bijectivity only uses the left smoothing error;
finite-dimensionality below uses the two-sided parametrix Fredholm theorem.
All maps are restrictions of the original smooth embedding. The proofs preserve
that embedding and use only the stated smoothing inverse assumptions.
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

/-- The original smooth embedding takes smooth kernel vectors to Sobolev kernel vectors. -/
theorem smoothToSobolev_mem_ker (s : ℝ) (u : P.toLinearMap.ker) :
    A.smoothToSobolev s u.val ∈ (P.sobolevExtension A B s).ker := by
  /- Use the smooth-input extension formula and the equation P u=0. The image
  is the embedding of zero in the target completion. No parametrix is needed. -/
  change P.sobolevExtension A B s (A.smoothToSobolev s u.val) = 0
  rw [P.sobolevExtension_smoothToSobolev, show P.toLinearMap u.val = 0 from u.property,
    map_zero]

/-- Restrict the actual smooth embedding to the two kernels. -/
def sobolevKerMap (s : ℝ) :
    P.toLinearMap.ker →ₗ[ℂ] (P.sobolevExtension A B s).ker :=
  ((A.smoothToSobolev s).comp P.toLinearMap.ker.subtype).codRestrict
    (P.sobolevExtension A B s).ker (P.smoothToSobolev_mem_ker A B s)

/-- The restricted kernel map still embeds the original section. -/
theorem sobolevKerMap_apply (s : ℝ) (u : P.toLinearMap.ker) :
    (P.sobolevKerMap A B s u).val = A.smoothToSobolev s u.val := by
  /- Unfold the codomain restriction and project to the ambient completion.
  The membership proof contributes no change to the section or its embedding. -/
  rfl

/-- The smooth embedding is injective on kernels without ellipticity. -/
theorem sobolevKerMap_injective (s : ℝ) :
    Function.Injective (P.sobolevKerMap A B s) := by
  /- Project an equality to the ambient Sobolev space. Injectivity of
  smoothToSobolev gives equality of the smooth sections; use subtype extensionality. -/
  intro u v huv
  apply Subtype.ext
  apply A.smoothToSobolev_injective s
  exact congrArg Subtype.val huv

variable (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))

/-- A left smoothing inverse gives a smooth representative of every Sobolev kernel vector. -/
theorem sobolevKerMap_surjective_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s : ℝ) : Function.Surjective (P.sobolevKerMap A B s) := by
  /- Apply existsUnique_smooth_lift_of_isSmoothingOperator to the given kernel
  vector and smooth right-hand side zero. The resulting section is in the smooth
  kernel and embeds to the original vector. No right inverse is used here. -/
  intro u
  -- Lift the same Sobolev vector with zero smooth right-hand side.
  obtain ⟨w, ⟨hw, hPw⟩, _⟩ :=
    P.existsUnique_smooth_lift_of_isSmoothingOperator Q A B hQ s u.val 0 (by
      rw [map_zero]
      exact u.property)
  refine ⟨⟨w, hPw⟩, ?_⟩
  apply Subtype.ext
  exact hw

/-- The natural kernel equivalence furnished by a left smoothing inverse. -/
def sobolevKerEquiv
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s : ℝ) : P.toLinearMap.ker ≃ₗ[ℂ] (P.sobolevExtension A B s).ker :=
  LinearEquiv.ofBijective (P.sobolevKerMap A B s)
    ⟨P.sobolevKerMap_injective A B s,
      P.sobolevKerMap_surjective_of_isSmoothingOperator A B Q hQ s⟩

/-- The actual kernel equivalence identifies the two dimensions. -/
theorem finrank_ker_sobolevExtension_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s : ℝ) :
    Module.finrank ℂ (P.sobolevExtension A B s).ker = Module.finrank ℂ P.toLinearMap.ker := by
  /- Apply dimension invariance to sobolevKerEquiv. The assertion records the
  actual embedding, and does not assume a smooth-kernel finiteness theorem. -/
  exact (P.sobolevKerEquiv A B Q hQ s).finrank_eq.symm

include A B in
/-- A two-sided smooth parametrix makes the original smooth kernel finite-dimensional. -/
theorem finiteDimensional_ker_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    FiniteDimensional ℂ P.toLinearMap.ker := by
  /- Sobolev Fredholmness at order zero gives a finite-dimensional kernel.
  Restrict the injective original smooth embedding to the smooth kernel and
  transfer finiteness through this natural kernel map. -/
  -- Fredholmness supplies finiteness only in the already complete Sobolev carrier.
  have hFred := P.isFredholm_sobolevExtension_of_isParametrix Q A B hQ 0
  let : FiniteDimensional ℂ (P.sobolevExtension A B 0).ker := hFred.finite_ker
  -- The original embedding then transfers it to the actual smooth kernel.
  exact FiniteDimensional.of_injective (P.sobolevKerMap A B 0)
    (P.sobolevKerMap_injective A B 0)

end PseudodifferentialOperator

end AtiyahSinger

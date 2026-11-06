/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticKernel

/-!
# Smooth and Sobolev cokernels, and the opposite-order transpose kernel

Public module ID: M0448.

A07: SG III.5.2, diagram (5.1), and Corollary 5.3. Descend the actual smooth
embedding to the algebraic quotients by the respective ranges. Smooth regularity
gives injectivity; density in the finite-dimensional Hausdorff Sobolev cokernel
gives surjectivity. Separately expose the book's transpose-kernel dimension
comparison through continuous duality. A cokernel is not canonically its complex
linear dual, so that step asserts a dimension identity, not a false identity of maps.
The natural quotient map, its bijectivity, and its dimension formulas are proved
for the original differential realization and the specified weak transpose.
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
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The target smooth embedding carries the smooth image into the Sobolev image. -/
theorem range_le_comap_smoothToSobolev (s : ℝ) :
    P.toLinearMap.range ≤
      (P.sobolevExtension A B s).range.comap (B.smoothToSobolev (s - m)) := by
  /- A vector in the smooth range is P u for a smooth u. Its target embedding
  equals P_s applied to the source embedding of u, by the extension formula.
  Thus it lies in the actual range, without closing the range or assuming ellipticity. -/
  rintro v ⟨u, rfl⟩
  refine ⟨A.smoothToSobolev s u, ?_⟩
  rw [← P.sobolevExtension_toPseudodifferentialOperator μ A B s]
  exact (P.toPseudodifferentialOperator μ).sobolevExtension_smoothToSobolev A B s u

/-- The natural map of algebraic cokernels induced by the original smooth embedding. -/
def sobolevCokerMap (s : ℝ) :
    (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) →ₗ[ℂ]
      (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) :=
  P.toLinearMap.range.mapQ (P.sobolevExtension A B s).range
    (B.smoothToSobolev (s - m)) (P.range_le_comap_smoothToSobolev μ A B s)

/-- A smooth cokernel class is sent to the class of the same section in the completion. -/
theorem sobolevCokerMap_mkQ (s : ℝ) (v : smoothSections (n := n) (r := q) F) :
    P.sobolevCokerMap μ A B s (P.toLinearMap.range.mkQ v) =
      (P.sobolevExtension A B s).range.mkQ (B.smoothToSobolev (s - m) v) := by
  /- Apply Submodule.mapQ to the class represented by v. Its defining quotient
  lift applies the smooth embedding and then the target quotient projection;
  no representative is selected and no quotient by closure is substituted. -/
  rfl

/-- A smooth right-hand side with a Sobolev preimage has a smooth preimage. -/
theorem sobolevCokerMap_injective (hP : P.IsElliptic) (s : ℝ) :
    Function.Injective (P.sobolevCokerMap μ A B s) := by
  /- It suffices to show that a class mapping to zero is zero. Represent it by
  a smooth v. Its embedded image lies in the Sobolev range, so choose u with
  P_s u equal to that embedding. Global smooth lifting supplies w with P w=v.
  Thus v is in the smooth range. This is the missing reverse implication in
  the range comparison; density of smooth sections alone would not give it. -/
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
  rw [P.sobolevCokerMap_mkQ μ A B s] at hz
  have hv : B.smoothToSobolev (s - m) v ∈ (P.sobolevExtension A B s).range :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨u, hu⟩ := hv
  -- Regularity supplies a smooth preimage of this same original section.
  obtain ⟨w, ⟨_, hPw⟩, _⟩ :=
    P.existsUnique_smooth_lift μ A B hP s u v hu
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hPw⟩

/-- Smooth cokernel classes cover the entire finite-dimensional Sobolev cokernel. -/
theorem sobolevCokerMap_surjective (hP : P.IsElliptic) (s : ℝ) :
    Function.Surjective (P.sobolevCokerMap μ A B s) := by
  /- Stage 1: Fredholmness of P_s gives closed range and a finite-dimensional
  algebraic cokernel. The closed range makes its quotient topology Hausdorff.
  Stage 2: the image of the dense smooth subspace under the continuous surjective
  quotient map is dense. It is the range of sobolevCokerMap by its class formula.
  Stage 3: every linear subspace of this finite-dimensional Hausdorff quotient
  is closed. The image is therefore the whole quotient. No smooth-cokernel
  finiteness theorem is used here; that finiteness follows from the comparison. -/
  classical
  let H := B.SobolevSpace (s - m)
  let R : Submodule ℂ H := (P.sobolevExtension A B s).range
  let C := H ⧸ R
  have hFred := P.isFredholm_sobolevExtension μ A B hP s
  let : IsClosed (R : Set H) := hFred.isClosed_range
  let : FiniteDimensional ℂ C := hFred.finite_coker
  let proj : H →L[ℂ] C := ⟨R.mkQ, R.continuous_mkQ⟩
  -- The same smooth embedding followed by the quotient has dense range.
  have hdense : DenseRange (fun v ↦ proj (B.smoothToSobolev (s - m) v)) :=
    R.mkQ_surjective.denseRange.comp (B.denseRange_smoothToSobolev (s - m)) proj.continuous
  have hclosed : IsClosed (Set.range (P.sobolevCokerMap μ A B s)) :=
    (P.sobolevCokerMap μ A B s).range.closed_of_finiteDimensional
  have hsubset : Set.range (fun v ↦ proj (B.smoothToSobolev (s - m) v)) ⊆
      Set.range (P.sobolevCokerMap μ A B s) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨P.toLinearMap.range.mkQ v, rfl⟩
  -- A closed linear subspace containing this dense image is the whole quotient.
  intro z
  exact hclosed.closure_subset_iff.mpr hsubset (hdense z)

/-- The canonical cokernel comparison induced by the actual smooth-section embedding. -/
def sobolevCokerEquiv (hP : P.IsElliptic) (s : ℝ) :
    (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) ≃ₗ[ℂ]
      (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) :=
  LinearEquiv.ofBijective (P.sobolevCokerMap μ A B s)
    ⟨P.sobolevCokerMap_injective μ A B hP s, P.sobolevCokerMap_surjective μ A B hP s⟩

/-- The cokernel dimension agrees with the algebraic quotient on smooth sections. -/
theorem finrank_coker_sobolevExtension (hP : P.IsElliptic) (s : ℝ) :
    Module.finrank ℂ (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) =
      Module.finrank ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  /- The natural cokernel equivalence preserves dimension. Sobolev Fredholmness
  makes these dimensions finite, and transfers finiteness to the smooth quotient.
  This does not assume the earlier smooth finiteDimensional_coker declaration. -/
  exact (P.sobolevCokerEquiv μ A B hP s).finrank_eq.symm

set_option maxHeartbeats 800000 in
-- The quotient-dual equivalence unfolds several nested differential Sobolev realizations.
/-- SG (5.1): the Sobolev cokernel has the dimension of the opposite-order weak transpose kernel. -/
theorem finrank_coker_eq_finrank_ker_sobolevTranspose (hP : P.IsElliptic) (s : ℝ) :
    Module.finrank ℂ (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) =
      Module.finrank ℂ (P.sobolevTranspose μ A B s).ker := by
  /- Stage 1: P_s is Fredholm, hence its range is closed and its quotient is
  finite-dimensional. The continuous dual of this quotient is the annihilator
  of the range in the continuous dual of H^(s-m)(F).
  Stage 2: sobolevEvaluationDuality_transpose identifies this annihilator with
  the kernel of the specified weak transpose on H^(-(s-m))(F*).
  Stage 3: a finite-dimensional complex space and its continuous complex dual
  have the same dimension. This last step is a dimension statement; the canonical
  object paired with the cokernel is its dual, not the cokernel itself. -/
  classical
  let H := B.SobolevSpace (s - m)
  let R : Submodule ℂ H := (P.sobolevExtension A B s).range
  let C := H ⧸ R
  let e := B.sobolevEvaluationDuality μ (s - m)
  have hFred := P.isFredholm_sobolevExtension μ A B hP s
  let : IsClosed (R : Set H) := hFred.isClosed_range
  let : FiniteDimensional ℂ C := hFred.finite_coker
  -- Closed range makes the actual quotient Hausdorff, so all its linear functionals are continuous.
  let q : H →L[ℂ] C := ⟨R.mkQ, R.continuous_mkQ⟩
  let g : Module.Dual ℂ C →ₗ[ℂ] B.DualSobolevSpace (-(s - m)) :=
    e.symm.toLinearMap.comp
      (((ContinuousLinearMap.compL ℂ H C ℂ).flip q).toLinearMap.comp
        LinearMap.toContinuousLinearMap.toLinearMap)
  have hg (ℓ : Module.Dual ℂ C) (v : H) : e (g ℓ) v = ℓ (R.mkQ v) := by
    exact congrArg (fun f : H →L[ℂ] ℂ ↦ f v) (e.apply_symm_apply _)
  have hgker (ℓ : Module.Dual ℂ C) : g ℓ ∈ (P.sobolevTranspose μ A B s).ker := by
    change P.sobolevTranspose μ A B s (g ℓ) = 0
    apply (A.sobolevEvaluationDuality μ s).injective
    rw [P.sobolevEvaluationDuality_transpose μ A B s, map_zero]
    apply ContinuousLinearMap.ext
    intro u
    change e (g ℓ) (P.sobolevExtension A B s u) = 0
    rw [hg]
    have hzero : R.mkQ (P.sobolevExtension A B s u) = 0 :=
      (Submodule.Quotient.mk_eq_zero R).mpr ⟨u, rfl⟩
    rw [hzero, map_zero]
  let G : Module.Dual ℂ C →ₗ[ℂ] (P.sobolevTranspose μ A B s).ker :=
    g.codRestrict _ hgker
  have hGinj : Function.Injective G := by
    intro ℓ κ heq
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := R.mkQ_surjective z
    have hval := congrArg (fun α : (P.sobolevTranspose μ A B s).ker ↦ e α.val v) heq
    exact (hg ℓ v).symm.trans (hval.trans (hg κ v))
  -- Conversely, a weak transpose zero annihilates the original range and descends to the quotient.
  have hGsurj : Function.Surjective G := by
    intro α
    have hann : R ≤ (e α.val).toLinearMap.ker := by
      rintro v ⟨u, rfl⟩
      have heq := congrArg (fun f : A.SobolevSpace s →L[ℂ] ℂ ↦ f u)
        (P.sobolevEvaluationDuality_transpose μ A B s α.val)
      rw [show P.sobolevTranspose μ A B s α.val = 0 from α.property, map_zero] at heq
      exact heq.symm
    let ℓ : Module.Dual ℂ C := R.liftQ (e α.val).toLinearMap hann
    refine ⟨ℓ, ?_⟩
    apply Subtype.ext
    apply e.injective
    apply ContinuousLinearMap.ext
    intro v
    exact hg ℓ v
  let equiv := LinearEquiv.ofBijective G ⟨hGinj, hGsurj⟩
  -- This identifies the dual of the quotient with the weak kernel; only dimensions are equated.
  exact (Subspace.dual_finrank_eq (K := ℂ) (V := C)).symm.trans equiv.finrank_eq

/-- The Sobolev cokernel dimension is the smooth formal-transpose kernel dimension. -/
theorem finrank_coker_eq_finrank_ker_formalTranspose (hP : P.IsElliptic) (s : ℝ) :
    Module.finrank ℂ (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) =
      Module.finrank ℂ (P.formalTranspose μ).ker := by
  /- First identify the cokernel dimension with the opposite-order weak transpose
  kernel. Then apply finrank_ker_sobolevTranspose, whose regularity step uses the
  ellipticity of the differential transpose. This follows the two steps in SG's
  proof of 5.2(ii) and does not replace the transpose by a Sobolev Hilbert adjoint. -/
  rw [P.finrank_coker_eq_finrank_ker_sobolevTranspose μ A B hP s,
    P.finrank_ker_sobolevTranspose μ A B hP s]

end DifferentialOperator

end AtiyahSinger

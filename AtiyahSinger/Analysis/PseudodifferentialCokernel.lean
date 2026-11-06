/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialIndex
public import AtiyahSinger.Analysis.PseudodifferentialTransposeRegularity

/-!
# PDO cokernels, the smooth transpose index formula, and range tests

Public module ID: M0887.

A07: SG III.5.2(ii), (5.1)--(5.2), and Corollary 5.3 for actual real-order PDOs
with a two-sided smoothing parametrix. Continuous duality concerns the dual of
the cokernel; only the resulting dimensions are identified with its transpose
kernel. Closed-range separation also supplies explicit solvability criteria.
These last criteria are project consequences, not extra numbered book lemmas.
All quotients use actual ranges; the annihilator and dimension arguments retain
the original geometric transpose and Sobolev realizations.
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

variable (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))

/-- SG (5.1): the actual Sobolev cokernel has the dimension of the weak transpose kernel. -/
theorem finrank_coker_eq_finrank_ker_sobolevTranspose_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    Module.finrank ℂ (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) =
      Module.finrank ℂ (P.sobolevTranspose A B s).ker := by
  /- Stage 1: the original parametrix makes P_s Fredholm, hence its actual
  range is closed and its quotient is finite-dimensional and Hausdorff.
  Stage 2: the continuous dual of this quotient is the range annihilator.
  Geometric evaluation duality and the precomposition identity identify this
  annihilator with the kernel of the specified opposite-order weak transpose.
  Stage 3: a finite-dimensional complex space and its continuous dual have
  equal dimensions. The canonical identification pairs the transpose kernel with
  the dual of the cokernel; a complex-linear isomorphism to the cokernel itself
  would require additional choices. -/
  classical
  let H := B.SobolevSpace (s - m)
  let R : Submodule ℂ H := (P.sobolevExtension A B s).range
  let C := H ⧸ R
  let e := B.sobolevEvaluationDuality μ (s - m)
  have hFred := P.isFredholm_sobolevExtension_of_isParametrix Q A B hQ s
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
  have hgker (ℓ : Module.Dual ℂ C) : g ℓ ∈ (P.sobolevTranspose A B s).ker := by
    change P.sobolevTranspose A B s (g ℓ) = 0
    apply (A.sobolevEvaluationDuality μ s).injective
    rw [P.sobolevEvaluationDuality_transpose, map_zero]
    apply ContinuousLinearMap.ext
    intro u
    change e (g ℓ) (P.sobolevExtension A B s u) = 0
    rw [hg]
    have hzero : R.mkQ (P.sobolevExtension A B s u) = 0 :=
      (Submodule.Quotient.mk_eq_zero R).mpr ⟨u, rfl⟩
    rw [hzero, map_zero]
  let G : Module.Dual ℂ C →ₗ[ℂ] (P.sobolevTranspose A B s).ker :=
    g.codRestrict _ hgker
  have hGinj : Function.Injective G := by
    intro ℓ κ heq
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := R.mkQ_surjective z
    have hval := congrArg (fun α : (P.sobolevTranspose A B s).ker ↦ e α.val v) heq
    exact (hg ℓ v).symm.trans (hval.trans (hg κ v))
  -- Conversely, a weak transpose zero annihilates the original range and descends to the quotient.
  have hGsurj : Function.Surjective G := by
    intro α
    have hann : R ≤ (e α.val).toLinearMap.ker := by
      rintro v ⟨u, rfl⟩
      have heq := congrArg (fun f : A.SobolevSpace s →L[ℂ] ℂ ↦ f u)
        (P.sobolevEvaluationDuality_transpose A B s α.val)
      rw [show P.sobolevTranspose A B s α.val = 0 from α.property, map_zero] at heq
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

/-- The actual Sobolev cokernel has the dimension of the smooth formal-transpose kernel. -/
theorem finrank_coker_eq_finrank_ker_formalTranspose_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    Module.finrank ℂ (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) =
      Module.finrank ℂ P.formalTranspose.toLinearMap.ker := by
  /- First use continuous cokernel duality to compare with the weak kernel.
  Then use its natural smooth-kernel equivalence, supplied by the right error
  hQ.2. This follows the two distinct steps in SG's proof of index independence. -/
  rw [P.finrank_coker_eq_finrank_ker_sobolevTranspose_of_isParametrix A B Q hQ s,
    P.finrank_ker_sobolevTranspose_of_isSmoothingOperator A B Q hQ.2 s]

include A B in
/-- The original smooth algebraic cokernel has the dimension of the smooth transpose kernel. -/
theorem finrank_smoothCoker_eq_finrank_ker_formalTranspose_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    Module.finrank ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) =
      Module.finrank ℂ P.formalTranspose.toLinearMap.ker := by
  /- At any one real Sobolev order, use the existing natural cokernel comparison
  and then the preceding transpose-kernel comparison. Both dimensions are finite
  by the parametrix results. No topology on the algebraic smooth quotient is needed. -/
  calc
    Module.finrank ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) =
        Module.finrank ℂ (B.SobolevSpace (0 - m) ⧸
          (P.sobolevExtension A B 0).range) :=
      (P.finrank_coker_sobolevExtension_of_isParametrix A B Q hQ 0).symm
    _ = Module.finrank ℂ P.formalTranspose.toLinearMap.ker :=
      P.finrank_coker_eq_finrank_ker_formalTranspose_of_isParametrix A B Q hQ 0

include A B in
/-- SG (5.2): the original smooth-map index is the difference of two smooth kernel dimensions. -/
theorem index_eq_finrank_ker_sub_finrank_ker_formalTranspose_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    P.toLinearMap.index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ P.formalTranspose.toLinearMap.ker := by
  /- Smooth kernel and cokernel finiteness justify LinearMap.index's usual
  integer dimension formula. Substitute the smooth cokernel dimension identity.
  The right side uses the metric-free bilinear transpose for the same density. -/
  rw [LinearMap.index_eq_finrank_sub,
    P.finrank_smoothCoker_eq_finrank_ker_formalTranspose_of_isParametrix A B Q hQ]

/-- Every critical Sobolev index has the same two smooth-kernel expression. -/
theorem index_sobolevExtension_eq_finrank_ker_sub_finrank_ker_formalTranspose_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    (P.sobolevExtension A B s).index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ P.formalTranspose.toLinearMap.ker := by
  /- Identify the Sobolev index with the original smooth-map index using the
  natural kernel/cokernel comparisons, then apply the preceding two-kernel formula.
  This is SG 5.3 with its two-kernel expression now justified for real-order PDOs. -/
  rw [P.index_sobolevExtension_eq_of_isParametrix A B Q hQ s]
  exact P.index_eq_finrank_ker_sub_finrank_ker_formalTranspose_of_isParametrix A B Q hQ

set_option maxHeartbeats 600000 in
-- The extended limit accommodates the smooth transpose, dual pairing and closed critical-range
-- comparison.
/-- Smooth transpose zeros detect membership in the closed range of every critical realization. -/
theorem mem_range_sobolevExtension_iff_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ)
    (v : B.SobolevSpace (s - m)) :
    v ∈ (P.sobolevExtension A B s).range ↔
      ∀ α : P.formalTranspose.toLinearMap.ker,
        B.sobolevEvaluationDuality μ (s - m)
          (B.dualSmoothToSobolev (-(s - m)) ((dualSectionsEquiv F).symm α.val)) v = 0 := by
  /- Stage 1: Fredholmness makes the actual quotient finite-dimensional and
  Hausdorff. Its linear functionals are continuous and separate its points, so
  their pullbacks detect the original range. Without closedness, continuous
  annihilators would detect only the range closure in general.
  Stage 2: geometric duality identifies these functionals with weak transpose
  zeros. The natural smooth-kernel equivalence supplies exactly the smooth tests
  in the displayed formula. This is a project consequence of SG's (5.1) argument. -/
  classical
  let H := B.SobolevSpace (s - m)
  let R : Submodule ℂ H := (P.sobolevExtension A B s).range
  let C := H ⧸ R
  let e := B.sobolevEvaluationDuality μ (s - m)
  have hFred := P.isFredholm_sobolevExtension_of_isParametrix Q A B hQ s
  let : IsClosed (R : Set H) := hFred.isClosed_range
  let : FiniteDimensional ℂ C := hFred.finite_coker
  let quotientMap : H →L[ℂ] C := ⟨R.mkQ, R.continuous_mkQ⟩
  have hann (β : (P.sobolevTranspose A B s).ker) (u : A.SobolevSpace s) :
      e β.val (P.sobolevExtension A B s u) = 0 := by
    have heq := congrArg (fun f : A.SobolevSpace s →L[ℂ] ℂ ↦ f u)
      (P.sobolevEvaluationDuality_transpose A B s β.val)
    rw [show P.sobolevTranspose A B s β.val = 0 from β.property, map_zero] at heq
    exact heq.symm
  constructor
  · rintro ⟨u, rfl⟩ α
    exact hann (P.sobolevTransposeKerMap A B s α) u
  · intro hv
    -- Test the actual finite-dimensional Hausdorff quotient, not merely its separated completion.
    apply (Submodule.Quotient.mk_eq_zero R).mp
    apply (Module.forall_dual_apply_eq_zero_iff ℂ (R.mkQ v)).mp
    intro ℓ
    let f : H →L[ℂ] ℂ := (LinearMap.toContinuousLinearMap ℓ).comp quotientMap
    let β : B.DualSobolevSpace (-(s - m)) := e.symm f
    have hβ : P.sobolevTranspose A B s β = 0 := by
      apply (A.sobolevEvaluationDuality μ s).injective
      rw [P.sobolevEvaluationDuality_transpose, map_zero]
      change (e (e.symm f)).comp (P.sobolevExtension A B s) = 0
      rw [e.apply_symm_apply]
      apply ContinuousLinearMap.ext
      intro u
      change ℓ (R.mkQ (P.sobolevExtension A B s u)) = 0
      have hzero : R.mkQ (P.sobolevExtension A B s u) = 0 :=
        (Submodule.Quotient.mk_eq_zero R).mpr ⟨u, rfl⟩
      rw [hzero, map_zero]
    -- The right residual supplies the same smooth covector representing this annihilator.
    obtain ⟨α, hα⟩ := P.sobolevTransposeKerMap_surjective_of_isSmoothingOperator
      A B Q hQ.2 s ⟨β, hβ⟩
    have hval := congrArg Subtype.val hα
    have htest := hv α
    change e (P.sobolevTransposeKerMap A B s α).val v = 0 at htest
    rw [hval] at htest
    have heval : e β v = ℓ (R.mkQ v) := by
      exact congrArg (fun g : H →L[ℂ] ℂ ↦ g v) (e.apply_symm_apply f)
    exact heval.symm.trans htest

include A B in
/-- A smooth section has a smooth preimage exactly when all transpose zeros annihilate it. -/
theorem mem_range_iff_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (v : smoothSections (n := n) (r := q) F) :
    v ∈ P.toLinearMap.range ↔
      ∀ α : P.formalTranspose.toLinearMap.ker, (∫ x, α.val.val x (v.val x) ∂μ) = 0 := by
  /- Forward: write v=P u and use the formal transpose pairing with P^t α=0.
  Reverse, stage 1: embed v at any critical target Sobolev order. The smooth
  evaluation formula turns the integral conditions into the preceding range
  criterion, yielding a Sobolev preimage u.
  Stage 2: the original left error hQ.1 upgrades this preimage of the smooth v
  to a smooth section w with P w=v. No uniqueness of w or self-adjointness is asserted. -/
  have htests (α : P.formalTranspose.toLinearMap.ker) :
      B.sobolevEvaluationDuality μ (0 - m)
        (B.dualSmoothToSobolev (-(0 - m)) ((dualSectionsEquiv F).symm α.val))
        (B.smoothToSobolev (0 - m) v) = ∫ x, α.val.val x (v.val x) ∂μ := by
    exact B.sobolevEvaluationPairing_smooth μ (0 - m)
      ((dualSectionsEquiv F).symm α.val) v
  constructor
  · rintro ⟨u, rfl⟩ α
    have hv : B.smoothToSobolev (0 - m) (P.toLinearMap u) ∈
        (P.sobolevExtension A B 0).range :=
      ⟨A.smoothToSobolev 0 u, P.sobolevExtension_smoothToSobolev A B 0 u⟩
    exact (htests α).symm.trans
      ((P.mem_range_sobolevExtension_iff_of_isParametrix A B Q hQ 0 _).mp hv α)
  · intro hv
    have hsob : B.smoothToSobolev (0 - m) v ∈ (P.sobolevExtension A B 0).range := by
      apply (P.mem_range_sobolevExtension_iff_of_isParametrix A B Q hQ 0 _).mpr
      intro α
      exact (htests α).trans (hv α)
    obtain ⟨u, hu⟩ := hsob
    -- The original left residual upgrades this preimage of the specified smooth section.
    obtain ⟨w, ⟨_, hPw⟩, _⟩ :=
      P.existsUnique_smooth_lift_of_isSmoothingOperator Q A B hQ.1 0 u v hu
    exact ⟨w, hPw⟩

end PseudodifferentialOperator

end AtiyahSinger

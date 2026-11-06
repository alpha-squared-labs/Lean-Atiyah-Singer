/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialKernel

/-!
# Cokernel comparison and the smooth index of a real-order PDO

Public module ID: M0892.

A07: SG III.5.2--5.3. Natural quotient maps and regularity compare the original
smooth-section map with each critical Sobolev realization of a supplied two-sided
smoothing parametrix pair. The index is mathlib's `LinearMap.index`; the natural
comparisons accompany its algebraic dimension formula with finite-dimensional
kernel and cokernel results for that same pair. Arbitrary full-symbol ellipticity
and parametrix existence are separate construction issues.
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

/-- The target embedding carries the original smooth range into the Sobolev range. -/
theorem range_le_comap_smoothToSobolev (s : ℝ) :
    P.toLinearMap.range ≤
      (P.sobolevExtension A B s).range.comap (B.smoothToSobolev (s - m)) := by
  /- Represent a smooth range vector as P u. The extension formula sends its
  target embedding to P_s applied to the source embedding of u. This is actual
  range membership, with no closure and no parametrix assumption. -/
  rintro v ⟨u, rfl⟩
  exact ⟨A.smoothToSobolev s u, P.sobolevExtension_smoothToSobolev A B s u⟩

/-- The original target embedding descends to the algebraic cokernels. -/
def sobolevCokerMap (s : ℝ) :
    (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) →ₗ[ℂ]
      (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) :=
  P.toLinearMap.range.mapQ (P.sobolevExtension A B s).range
    (B.smoothToSobolev (s - m)) (P.range_le_comap_smoothToSobolev A B s)

/-- The induced map sends the class of a section to the class of its actual embedding. -/
theorem sobolevCokerMap_mkQ (s : ℝ) (v : smoothSections (n := n) (r := q) F) :
    P.sobolevCokerMap A B s (P.toLinearMap.range.mkQ v) =
      (P.sobolevExtension A B s).range.mkQ (B.smoothToSobolev (s - m) v) := by
  /- Evaluate Submodule.mapQ on a quotient representative. Its defining lift
  applies exactly the target smooth embedding followed by the quotient map. -/
  rfl

variable (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))

/-- A left smoothing inverse suffices for injectivity of the cokernel comparison. -/
theorem sobolevCokerMap_injective_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s : ℝ) : Function.Injective (P.sobolevCokerMap A B s) := by
  /- If the class of a smooth v maps to zero, choose a Sobolev preimage u of
  its embedding. Smooth lifting using the left residual gives a smooth w with
  P w=v. Thus the original class was zero. Apply the kernel criterion for injectivity. -/
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
  rw [P.sobolevCokerMap_mkQ] at hz
  have hv : B.smoothToSobolev (s - m) v ∈ (P.sobolevExtension A B s).range :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨u, hu⟩ := hv
  -- Regularity supplies a smooth preimage of this same original section.
  obtain ⟨w, ⟨_, hPw⟩, _⟩ :=
    P.existsUnique_smooth_lift_of_isSmoothingOperator Q A B hQ s u v hu
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hPw⟩

/-- A two-sided parametrix makes smooth classes cover the Sobolev cokernel. -/
theorem sobolevCokerMap_surjective_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    Function.Surjective (P.sobolevCokerMap A B s) := by
  /- The right identity writes each target vector as P(Q(u))-K(u). The kernel
  output is represented by one actual smooth section, so its negative has the
  original quotient class of u. This direct representative argument does not
  require smooth-cokernel finiteness; that follows separately from Fredholmness
  and the resulting natural comparison. -/
  intro z
  obtain ⟨u, rfl⟩ := (P.sobolevExtension A B s).range.mkQ_surjective z
  obtain ⟨K, hK⟩ := hQ.2
  let T := P.sobolevExtension A B s
  let R := Q.sobolevRealization B A (s - m) s (by linarith)
  let S := K.sobolevExtension μ B B (s - m) (s - m)
  let proj := T.range.mkQ
  -- The right error represents every quotient class by the same smooth output -K(u).
  refine ⟨P.toLinearMap.range.mkQ (-K.sobolevToSmooth μ B B (s - m) u), ?_⟩
  have hres : T (R u) - u = S u :=
    DFunLike.congr_fun (P.comp_sobolevRealization_sub_id_eq Q A B K hK s) u
  have hzero : proj (T (R u)) = 0 :=
    (Submodule.Quotient.mk_eq_zero T.range).mpr ⟨R u, rfl⟩
  have hclass : proj (S u) = -proj u := by
    calc
      proj (S u) = proj (T (R u) - u) := congrArg proj hres.symm
      _ = proj (T (R u)) - proj u := map_sub proj _ _
      _ = -proj u :=
        (congrArg (fun v ↦ v - proj u) hzero).trans (zero_sub _)
  have hsmooth : B.smoothToSobolev (s - m)
      (-K.sobolevToSmooth μ B B (s - m) u) = -S u := by
    rw [map_neg, K.smoothToSobolev_sobolevToSmooth]
  calc
    _ = proj (B.smoothToSobolev (s - m)
        (-K.sobolevToSmooth μ B B (s - m) u)) := P.sobolevCokerMap_mkQ A B s _
    _ = proj (-S u) := congrArg proj hsmooth
    _ = -proj (S u) := map_neg proj _
    _ = proj u := (congrArg Neg.neg hclass).trans (neg_neg _)

/-- The canonical cokernel equivalence induced by the original smooth embedding. -/
def sobolevCokerEquiv (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) ≃ₗ[ℂ]
      (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) :=
  LinearEquiv.ofBijective (P.sobolevCokerMap A B s)
    ⟨P.sobolevCokerMap_injective_of_isSmoothingOperator A B Q hQ.1 s,
      P.sobolevCokerMap_surjective_of_isParametrix A B Q hQ s⟩

/-- The smooth and Sobolev cokernels have the same dimension. -/
theorem finrank_coker_sobolevExtension_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    Module.finrank ℂ (B.SobolevSpace (s - m) ⧸ (P.sobolevExtension A B s).range) =
      Module.finrank ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  /- Apply dimension invariance to sobolevCokerEquiv. Its forward map is the
  natural quotient comparison. The equivalence follows from smoothing regularity
  and the right residual identity, independently of cokernel finiteness. -/
  exact (P.sobolevCokerEquiv A B Q hQ s).finrank_eq.symm

include A B in
/-- The actual quotient of smooth sections by the smooth range is finite-dimensional. -/
theorem finiteDimensional_coker_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    FiniteDimensional ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  /- Sobolev Fredholmness at order zero gives a finite-dimensional cokernel.
  Transfer finiteness to the smooth quotient through the injective natural
  cokernel map, whose injectivity uses regularity for the left residual. -/
  -- Finiteness is established in the Sobolev quotient before transferring it to smooth classes.
  have hFred := P.isFredholm_sobolevExtension_of_isParametrix Q A B hQ 0
  let : FiniteDimensional ℂ
      (B.SobolevSpace (0 - m) ⧸ (P.sobolevExtension A B 0).range) := hFred.finite_coker
  exact FiniteDimensional.of_injective (P.sobolevCokerMap A B 0)
    (P.sobolevCokerMap_injective_of_isSmoothingOperator A B Q hQ.1 0)

/-- Every critical Sobolev realization has the index of the original smooth section map. -/
theorem index_sobolevExtension_eq_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    (P.sobolevExtension A B s).index = P.toLinearMap.index := by
  /- Stage 1: the two-sided parametrix gives a Fredholm Sobolev realization;
  the natural comparisons transfer finite kernel and cokernel to smooth sections.
  Stage 2: apply the integer kernel-minus-cokernel formula to both actual maps
  and substitute the dimension comparisons. The right side uses mathlib's
  existing algebraic index, now certified to have finite kernel and cokernel. -/
  -- The comparisons are induced by the actual embeddings, and finiteness is already proved.
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    P.finrank_ker_sobolevExtension_of_isSmoothingOperator A B Q hQ.1 s,
    P.finrank_coker_sobolevExtension_of_isParametrix A B Q hQ s]

include A B in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- The algebraic index formula for the original smooth map and parametrix parameters. -/
theorem index_eq_finrank_sub_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    P.toLinearMap.index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  /- This equality is the defining algebraic index formula in mathlib.
  Finite-dimensionality is a separate assertion: the formula and its totalized
  finite dimensions do not by themselves certify a Fredholm operator. -/
  exact LinearMap.index_eq_finrank_sub

/-- Real Sobolev order and finite presentations do not change this index. -/
theorem index_sobolevExtension_eq_of_isParametrix_of_presentations
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (A' : SmoothBundlePresentation (n := n) (r := r) E)
    (B' : SmoothBundlePresentation (n := n) (r := q) F) (s t : ℝ) :
    (P.sobolevExtension A B s).index = (P.sobolevExtension A' B' t).index := by
  /- Compare each bounded index with the same original smooth-map index.
  The completions on the two sides may differ both in norms and in regularity;
  no identification of their carriers or common norm-continuous path is assumed. -/
  rw [P.index_sobolevExtension_eq_of_isParametrix A B Q hQ s,
    P.index_sobolevExtension_eq_of_isParametrix A' B' Q hQ t]

end PseudodifferentialOperator

end AtiyahSinger

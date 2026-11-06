/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialSupport
public import AtiyahSinger.Analysis.ExcisionLocalization
public import AtiyahSinger.Geometry.OpenSections

/-!
# Kernel comparison by restriction and zero extension

Public module ID: M0826.

UL03/P02: the maps used in SG III.13.4's kernel argument, pp.248--249.
The local operator here has domain Γ_K(U;E): its input is zero-extended, the
original ambient operator is applied, and its output is restricted to U.
The comparison specifies both directions of the resulting kernel equivalence.

This proves neither equivalence with a PDO on all smooth sections of a noncompact
U nor compatibility between two different ambient extensions. Those require separate
relative bundle and operator comparisons. In particular, the second
localized map below comes from the ambient metric adjoint; it is not declared to
be an adjoint on a new noncompact Hilbert or section-space carrier.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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

include hM

/-- Supported kernels are identified by actual restriction, with zero extension as inverse. -/
theorem exists_ker_restriction_equiv (U : Opens M) (K : Set M)
    (hK : IsClosed K) (hKU : K ⊆ (U : Set M))
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hker : ∀ u : P.ker, ∀ x, x ∉ K → u.val.val x = 0)
    (himage : ∀ u : supportedSmoothSections (n := n) (r := r) E K,
      ∀ x, x ∉ K → (P u.val).val x = 0) :
    let R := (smoothSectionRestriction F U).comp
      (P.comp (smoothSectionZeroExtension E U K hK hKU))
    ∃ e : P.ker ≃ₗ[ℂ] R.ker,
      (∀ u, (e u).val.val = smoothSectionRestriction E U u.val) ∧
      (∀ v, (e.symm v).val = smoothSectionZeroExtension E U K hK hKU v.val) := by
  /- Stage 1: hker makes restriction of each P-zero a section supported in the
  inverse image of K. Its zero extension is the original section, so it lies
  in the displayed R-kernel. Pointwise restriction is complex-linear.
  Stage 2: zero-extend an R-zero. It is smooth and supported in K. Its P-image
  restricts to zero on U by the kernel equation, and himage makes that image
  zero off K, hence also off U. It is therefore a P-zero.
  Stage 3: restriction followed by zero extension, and conversely, retain the
  original fiber values. They are inverse linear maps, giving the specified
  equivalence. Ambient closedness handles boundary smoothness; no Fredholm,
  finite-dimensionality, compactness or adjoint assumption enters this result. -/
  classical
  let Z := smoothSectionZeroExtension (n := n) (r := r) E U K hK hKU
  let R := (smoothSectionRestriction (n := n) (r := q) F U).comp (P.comp Z)
  -- Restrict the original kernel section, retaining its support in the pulled-back K.
  let restrictKernel (u : P.ker) :
      supportedSmoothSections (n := n) (r := r) (M := U)
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
        ((Subtype.val : U → M) ⁻¹' K) :=
    ⟨smoothSectionRestriction (n := n) (r := r) E U u.val, by
      intro x hx
      exact hker u x.val hx⟩
  have hzeroRestrict (u : P.ker) : Z (restrictKernel u) = u.val := by
    apply Subtype.ext
    funext x
    change (if hx : x ∈ U then u.val.val x else 0) = u.val.val x
    by_cases hx : x ∈ U
    · rw [dite_eq_left hx]
    · rw [dite_eq_right hx]
      exact (hker u x (fun hxK ↦ hx (hKU hxK))).symm
  have hrestrictMem (u : P.ker) : R (restrictKernel u) = 0 := by
    change (smoothSectionRestriction (n := n) (r := q) F U)
      (P (Z (restrictKernel u))) = 0
    rw [hzeroRestrict u, show P u.val = 0 from u.property, map_zero]
  -- Zero extension has the same ambient support, so its P-image vanishes off K.
  have hzeroSupport (v : R.ker) : ∀ x, x ∉ K → (Z v.val).val x = 0 := by
    intro x hxK
    change (if hx : x ∈ U then v.val.val.val ⟨x, hx⟩ else (0 : E x)) = 0
    by_cases hx : x ∈ U
    · erw [dite_eq_left hx]
      exact v.val.property ⟨x, hx⟩ hxK
    · erw [dite_eq_right hx]
  have hextMem (v : R.ker) : P (Z v.val) = 0 := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ U
    · -- The local kernel equation supplies the value at this same point of U.
      have hv : (smoothSectionRestriction (n := n) (r := q) F U)
          (P (Z v.val)) = 0 := v.property
      exact congrArg (fun w ↦ w.val ⟨x, hx⟩) hv
    · -- Outside U the point lies outside K, where the supported image is zero.
      exact himage ⟨Z v.val, hzeroSupport v⟩ x (fun hxK ↦ hx (hKU hxK))
  -- Both inverse relations are identities of the actual original fiber values.
  let e : P.ker ≃ₗ[ℂ] R.ker :=
    { toFun := fun u ↦ ⟨restrictKernel u, hrestrictMem u⟩
      invFun := fun v ↦ ⟨Z v.val, hextMem v⟩
      left_inv := by
        intro u
        apply Subtype.ext
        exact hzeroRestrict u
      right_inv := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change (if hx : x.val ∈ U then v.val.val.val ⟨x.val, hx⟩ else (0 : E x.val)) =
          v.val.val.val x
        erw [dite_eq_left x.property]
      map_add' := by
        intro u v
        apply Subtype.ext
        apply Subtype.ext
        exact (smoothSectionRestriction (n := n) (r := r) E U).map_add u.val v.val
      map_smul' := by
        intro c u
        apply Subtype.ext
        apply Subtype.ext
        exact (smoothSectionRestriction (n := n) (r := r) E U).map_smul c u.val }
  exact ⟨e, fun _ ↦ rfl, fun _ ↦ rfl⟩

variable [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hT hSC hC hBorel hE hF hμ

set_option maxHeartbeats 1200000 in
-- Normalize both localized kernels with the same restriction and zero extension maps.
/-- The localized operator and its metric adjoint both have the specified kernel identifications. -/
theorem PseudodifferentialOperator.exists_localized_ker_restriction_equivs
    (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (B : DifferentialOperator (n := n) (r := r) (q := q) E F 0)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ)
    (hQ : Q.toLinearMap = B.toLinearMap +
      twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap) χ hχ)
    (hBext : ∀ x, x ∉ tsupport χ → Function.Bijective (B.principalSymbol x 0))
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (U : Opens M) (hχU : tsupport χ ⊆ (U : Set M)) :
    let zE := smoothSectionZeroExtension E U (tsupport χ) (isClosed_tsupport χ) hχU
    let zF := smoothSectionZeroExtension F U (tsupport χ) (isClosed_tsupport χ) hχU
    let R := (smoothSectionRestriction F U).comp (Q.toLinearMap.comp zE)
    let S := (smoothSectionRestriction E U).comp ((Q.metricFormalAdjoint h k).toLinearMap.comp zF)
    ∃ e : Q.toLinearMap.ker ≃ₗ[ℂ] R.ker,
      (∀ u, (e u).val.val = smoothSectionRestriction E U u.val) ∧
      (∀ v, (e.symm v).val = zE v.val) ∧
      ∃ f : (Q.metricFormalAdjoint h k).toLinearMap.ker ≃ₗ[ℂ] S.ker,
        (∀ u, (f u).val.val = smoothSectionRestriction F U u.val) ∧
        (∀ v, (f.symm v).val = zF v.val) := by
  /- Stage 1: ker_support_of_localization puts both ambient kernels in the
  closed cutoff support. On sections supported there, B acts pointwise and
  preserves that support; the correction does too by its outer cutoff.
  Stage 2: the exact adjoint formula is B†+χ(P†-B†)χ. Its zero-order part is
  again pointwise, so it also preserves the same supported section space.
  Exterior invertibility of B, not unitarity, was enough to localize its kernel.
  Stage 3: apply exists_ker_restriction_equiv to Q and to its specified metric
  adjoint separately. Both inverse maps are the actual zero extensions to the
  same ambient bundles. This includes n=0 and the empty open set. It makes no
  assertion about an unrestricted noncompact adjoint or a second ambient manifold. -/
  classical
  -- The full kernels lie in the same closed cutoff support.
  have hker := PseudodifferentialOperator.ker_support_of_localization
    P Q B χ hχ hQ hBext h k
  have hkerQ (u : Q.toLinearMap.ker) (x : M) (hx : x ∉ tsupport χ) :
      u.val.val x = 0 := by
    by_contra hne
    exact hx (hker.1 u (subset_closure hne))
  have hkerAdj (u : (Q.metricFormalAdjoint h k).toLinearMap.ker)
      (x : M) (hx : x ∉ tsupport χ) : u.val.val x = 0 := by
    by_contra hne
    exact hx (hker.2 u (subset_closure hne))
  -- Differential locality and the outer cutoff preserve every supported input.
  have hmapQ (u : supportedSmoothSections (n := n) (r := r) E (tsupport χ)) :
      ∀ x, x ∉ tsupport χ → (Q.toLinearMap u.val).val x = 0 := by
    intro x hx
    have hb := B.map_mem_supportedSmoothSections (tsupport χ) (isClosed_tsupport χ) u
    have hc : (twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap) χ hχ u.val).val x =
        0 := by
      by_contra hne
      exact hx ((twoSidedSectionCutoff_support
        (P.toLinearMap - B.toLinearMap) χ hχ).1 u.val (subset_closure hne))
    rw [hQ]
    change (B.toLinearMap u.val).val x +
      (twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap) χ hχ u.val).val x = 0
    rw [hb x hx, hc, add_zero]
  -- Identify the actual same-density adjoint, without choosing a new local adjoint.
  let B₀ : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨B.toLinearMap, by simpa only [Nat.cast_zero] using
      B.isPseudodifferentialOperator (μ := μ)⟩
  let R := P.add (B₀.smul (-1))
  have hR : R.toLinearMap = P.toLinearMap - B.toLinearMap := by
    change P.toLinearMap + (-1 : ℂ) • B.toLinearMap = _
    simp only [neg_one_smul, sub_eq_add_neg]
  let C : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨twoSidedSectionCutoff R.toLinearMap χ hχ,
      isPseudodifferentialOperator_twoSidedSectionCutoff R χ hχ⟩
  let Bdagger := B.metricFormalAdjoint (μ := μ) h k
  have hCadj := R.metricFormalAdjoint_twoSidedSectionCutoff C χ hχ rfl h k
  have hrel := C.isMetricFormalAdjoint_metricFormalAdjoint h k
  rw [hCadj] at hrel
  have hsum := (B.isMetricFormalAdjoint_metricFormalAdjoint h k).add hrel
  have hsumQ : IsMetricFormalAdjoint h k μ Q.toLinearMap
      (Bdagger.toLinearMap +
        twoSidedSectionCutoff (R.metricFormalAdjoint h k).toLinearMap χ hχ) := by
    rw [hQ, ← hR]
    exact hsum
  have hQadj := (Q.isMetricFormalAdjoint_metricFormalAdjoint h k).unique hsumQ
  have hmapAdj (v : supportedSmoothSections (n := n) (r := q) F (tsupport χ)) :
      ∀ x, x ∉ tsupport χ → ((Q.metricFormalAdjoint h k).toLinearMap v.val).val x = 0 := by
    intro x hx
    have hb := Bdagger.map_mem_supportedSmoothSections
      (tsupport χ) (isClosed_tsupport χ) v
    have hc :
        (twoSidedSectionCutoff (R.metricFormalAdjoint h k).toLinearMap χ hχ v.val).val x =
          0 := by
      by_contra hne
      exact hx ((twoSidedSectionCutoff_support
        (R.metricFormalAdjoint h k).toLinearMap χ hχ).1 v.val (subset_closure hne))
    rw [hQadj]
    change (Bdagger.toLinearMap v.val).val x +
      (twoSidedSectionCutoff (R.metricFormalAdjoint h k).toLinearMap χ hχ v.val).val x = 0
    rw [hb x hx, hc, add_zero]
  -- Restriction and zero extension give both equivalences with their original value formulas.
  obtain ⟨e, he, he'⟩ := exists_ker_restriction_equiv U (tsupport χ)
    (isClosed_tsupport χ) hχU Q.toLinearMap hkerQ hmapQ
  obtain ⟨f, hf, hf'⟩ := exists_ker_restriction_equiv U (tsupport χ)
    (isClosed_tsupport χ) hχU (Q.metricFormalAdjoint h k).toLinearMap hkerAdj hmapAdj
  exact ⟨e, he, he', f, hf, hf'⟩

end AtiyahSinger

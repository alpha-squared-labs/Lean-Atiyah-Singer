/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialCokernel
public import AtiyahSinger.Analysis.PseudodifferentialSobolevAdjoint

import AtiyahSinger.Analysis.HermitianMetricCompatibility

/-!
# Geometric PDO adjoint kernels and actual cokernels

Public module ID: M0885.

A06/A07: transport the weak transpose regularity of SG III.5.2(ii) through
conjugate-linear metric duality, retaining the original right smoothing error.
Two-sided parametrices then give finite-dimensional kernels, the actual smooth
quotient-map equivalence, the Hermitian index formula, and solvability tests.
These natural-map refinements are project bridges to (5.1)--(5.2) and pp.194-195;
they are not additional numbered book lemmas. The stated parametrix hypotheses
are retained throughout the proofs below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

include hM hT2 hSC hC hBorel hE hF hHE hHF hμ

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The actual smooth embedding maps the geometric adjoint kernel into its weak kernel. -/
theorem smoothToSobolev_mem_ker_sobolevFormalAdjoint (s : ℝ)
    (v : P.formalAdjoint.toLinearMap.ker) :
    B.smoothToSobolev (-(s - m)) v.val ∈ (P.sobolevFormalAdjoint A B s).ker := by
  /- Apply the smooth-input formula to v.val. Its adjoint image is zero by
  kernel membership, hence so is the embedded image in the opposite-order space. -/
  change P.sobolevFormalAdjoint A B s (B.smoothToSobolev (-(s - m)) v.val) = 0
  rw [P.sobolevFormalAdjoint_smooth, v.property, map_zero]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Restriction of the original smooth embedding to the two geometric adjoint kernels. -/
def sobolevFormalAdjointKerMap (s : ℝ) :
    P.formalAdjoint.toLinearMap.ker →ₗ[ℂ] (P.sobolevFormalAdjoint A B s).ker :=
  ((B.smoothToSobolev (-(s - m))).comp P.formalAdjoint.toLinearMap.ker.subtype).codRestrict
    (P.sobolevFormalAdjoint A B s).ker (P.smoothToSobolev_mem_ker_sobolevFormalAdjoint A B s)

variable (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Only the original right smoothing error is needed to make a weak adjoint zero smooth. -/
theorem existsUnique_smooth_of_sobolevFormalAdjoint_eq_zero_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) (v : B.SobolevSpace (-(s - m)))
    (hv : P.sobolevFormalAdjoint A B s v = 0) :
    ∃! w : smoothSections (n := n) (r := q) F,
      B.smoothToSobolev (-(s - m)) w = v ∧ P.formalAdjoint.toLinearMap w = 0 := by
  /- Stage 1: metric duality carries v to a weak transpose zero. Apply the
  transpose regularity theorem, using only the original right error P Q-I.
  Stage 2: its smooth dual representative has a unique smooth primal inverse
  under smoothHermitianDualEquiv and dualSectionsEquiv. The compatibility of
  these maps with the Sobolev metric identification gives the displayed lift.
  Stage 3: the original smooth-extension identity and faithful embedding
  give P†w=0. The same embedding gives uniqueness for this specified v. -/
  -- Recover the smooth covector corresponding to the same weak adjoint zero.
  have htrans : P.sobolevTranspose A B s (B.sobolevHermitianDual (-(s - m)) v) = 0 := by
    rw [P.sobolevTranspose_hermitian, hv, map_zero]
  obtain ⟨β, hβ, _⟩ :=
    P.existsUnique_smooth_of_sobolevTranspose_eq_zero_of_isSmoothingOperator
      A B Q hQ s (B.sobolevHermitianDual (-(s - m)) v) htrans
  let w := (smoothHermitianDualEquiv F).symm ((dualSectionsEquiv F).symm β)
  have hw : B.smoothToSobolev (-(s - m)) w = v := by
    apply (B.sobolevHermitianDual (-(s - m))).injective
    rw [B.sobolevHermitianDual_smooth]
    simpa only [w, LinearEquiv.apply_symm_apply] using hβ.1
  -- Its original smooth adjoint image vanishes because the embedding is faithful.
  have hPw : P.formalAdjoint.toLinearMap w = 0 := by
    apply A.smoothToSobolev_injective (-s)
    rw [map_zero, ← P.sobolevFormalAdjoint_smooth, hw]
    exact hv
  refine ⟨w, ⟨hw, hPw⟩, ?_⟩
  intro z hz
  exact B.smoothToSobolev_injective (-(s - m)) (hz.1.trans hw.symm)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The right smoothing error makes the natural adjoint-kernel embedding bijective. -/
theorem bijective_sobolevFormalAdjointKerMap_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) : Function.Bijective (P.sobolevFormalAdjointKerMap A B s) := by
  /- Injectivity is inherited from the smooth embedding. For surjectivity,
  lift the ambient value of a weak kernel vector by the preceding theorem.
  Its smooth representative belongs to ker P† and maps to that same vector. -/
  constructor
  · intro u v huv
    apply Subtype.ext
    exact B.smoothToSobolev_injective (-(s - m)) (congrArg Subtype.val huv)
  · intro v
    obtain ⟨w, ⟨hw, hPw⟩, _⟩ :=
      P.existsUnique_smooth_of_sobolevFormalAdjoint_eq_zero_of_isSmoothingOperator
        A B Q hQ s v.val v.property
    exact ⟨⟨w, hPw⟩, Subtype.ext hw⟩

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The kernel equivalence retains the given smooth embedding as its forward map. -/
def sobolevFormalAdjointKerEquiv
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) : P.formalAdjoint.toLinearMap.ker ≃ₗ[ℂ]
      (P.sobolevFormalAdjoint A B s).ker :=
  LinearEquiv.ofBijective (P.sobolevFormalAdjointKerMap A B s)
    (P.bijective_sobolevFormalAdjointKerMap_of_isSmoothingOperator A B Q hQ s)

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this included context.
include A B in
/-- A two-sided parametrix makes the smooth geometric adjoint kernel finite-dimensional. -/
theorem finiteDimensional_ker_formalAdjoint_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    FiniteDimensional ℂ P.formalAdjoint.toLinearMap.ker := by
  /- The metric map identifies this kernel conjugate-linearly with the smooth
  transpose kernel. That kernel is finite-dimensional by the transposed
  parametrix. Restrict the bijective semilinear metric identification to the
  kernels and transport finite-dimensionality; no complex-linear Riesz map
  or arbitrary isomorphism to an algebraic dual is assumed. -/
  let e := (smoothHermitianDualEquiv (n := n) (r := q) F).trans (dualSectionsEquiv F)
  let : FiniteDimensional ℂ P.formalTranspose.toLinearMap.ker :=
    P.finiteDimensional_ker_formalTranspose_of_isParametrix A B Q hQ
  -- Restrict the actual inverse metric identification to transpose zeros.
  have hzero (β : P.formalTranspose.toLinearMap.ker) :
      P.formalAdjoint.toLinearMap (e.symm β.val) = 0 := by
    apply (smoothHermitianDualEquiv E).injective
    apply (dualSectionsEquiv E).injective
    rw [← P.formalTranspose_hermitian,
      show dualSectionsEquiv F (smoothHermitianDualEquiv F (e.symm β.val)) = β.val from
        e.apply_symm_apply β.val, β.property, map_zero, map_zero]
  let T : P.formalTranspose.toLinearMap.ker →ₗ⋆[ℂ] P.formalAdjoint.toLinearMap.ker :=
    (e.symm.toLinearMap.comp P.formalTranspose.toLinearMap.ker.subtype).codRestrict
      P.formalAdjoint.toLinearMap.ker hzero
  have hT : Function.Surjective T := by
    intro w
    have hw : P.formalTranspose.toLinearMap (e w.val) = 0 := by
      change P.formalTranspose.toLinearMap
        (dualSectionsEquiv F (smoothHermitianDualEquiv F w.val)) = 0
      rw [P.formalTranspose_hermitian, w.property, map_zero, map_zero]
    refine ⟨⟨e w.val, hw⟩, Subtype.ext ?_⟩
    exact e.symm_apply_apply w.val
  exact Module.Finite.of_surjective T hT

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this included context.
include A B in
/-- The actual quotient projection identifies the adjoint kernel with the smooth cokernel. -/
theorem bijective_ker_formalAdjoint_to_coker_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    Function.Bijective
      (P.toLinearMap.range.mkQ.comp P.formalAdjoint.toLinearMap.ker.subtype) := by
  /- Stage 1: the transpose-kernel criterion becomes orthogonality to ker P†
  under metric identification. Both the smooth cokernel and ker P† are finite;
  their dimensions agree by the transpose comparison and semilinear duality.
  Stage 2: if a smooth adjoint zero w also lies in range P, write w=Pu.
  The adjoint identity gives <w,w>=<u,P†w>=0, hence w=0. Thus the displayed
  quotient map is injective. Equal finite dimensions make this SAME map
  surjective. This avoids treating an arbitrary Sobolev norm as the L² metric. -/
  -- Specialize the proved explicit-metric statement to the same installed inner products.
  have hbij := P.bijective_ker_metricFormalAdjoint_to_coker
    (SmoothHermitianMetric.ofInnerProduct E) (SmoothHermitianMetric.ofInnerProduct F) A B Q hQ
  rw [P.metricFormalAdjoint_ofInnerProduct μ] at hbij
  exact hbij

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Canonical for the specified density and metrics: include an adjoint zero and take its class. -/
def kerFormalAdjointEquivCoker
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    P.formalAdjoint.toLinearMap.ker ≃ₗ[ℂ]
      (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) :=
  LinearEquiv.ofBijective
    (P.toLinearMap.range.mkQ.comp P.formalAdjoint.toLinearMap.ker.subtype)
    (P.bijective_ker_formalAdjoint_to_coker_of_isParametrix A B Q hQ)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The cokernel equivalence sends a smooth adjoint zero to its original quotient class. -/
theorem kerFormalAdjointEquivCoker_apply
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (w : P.formalAdjoint.toLinearMap.ker) :
    P.kerFormalAdjointEquivCoker A B Q hQ w = P.toLinearMap.range.mkQ w.val := by
  /- LinearEquiv.ofBijective retains the original forward map. Projecting
  through the kernel inclusion and then mkQ is exactly the displayed class. -/
  rfl

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this included context.
include A B in
/-- The Hermitian version of SG (5.2) computes the index of the original smooth section map. -/
theorem index_eq_finrank_ker_sub_finrank_ker_formalAdjoint_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    P.toLinearMap.index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ P.formalAdjoint.toLinearMap.ker := by
  /- The parametrix gives finite kernel and cokernel, so use the dimension
  formula for LinearMap.index. Replace the cokernel finrank using the actual
  quotient-map equivalence above. The index on the left is the original smooth
  algebraic index; the density and Hermitian choices enter only its expression. -/
  rw [LinearMap.index_eq_finrank_sub,
    ← (P.kerFormalAdjointEquivCoker A B Q hQ).finrank_eq]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Every critical Sobolev realization has the same two smooth Hermitian-kernel formula. -/
theorem index_sobolevExtension_eq_finrank_ker_sub_finrank_ker_formalAdjoint_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    (P.sobolevExtension A B s).index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ P.formalAdjoint.toLinearMap.ker := by
  /- Identify the Sobolev index with the smooth section-map index using the
  natural kernel and cokernel comparisons. Then substitute the preceding
  Hermitian formula. The opposite-order adjoint is not assumed to be the
  Hilbert adjoint for the selected Sobolev norms. -/
  rw [P.index_sobolevExtension_eq_of_isParametrix A B Q hQ s]
  exact P.index_eq_finrank_ker_sub_finrank_ker_formalAdjoint_of_isParametrix A B Q hQ

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this included context.
include A B in
/-- A smooth right hand side is solvable exactly when it is orthogonal to every adjoint zero. -/
theorem mem_range_iff_pairing_formalAdjoint_eq_zero_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (v : smoothSections (n := n) (r := q) F) :
    v ∈ P.toLinearMap.range ↔
      ∀ w : P.formalAdjoint.toLinearMap.ker, smoothSectionPairing μ F w.val v = 0 := by
  /- Convert the existing smooth range criterion through formalTranspose_hermitian
  and the bijective smooth metric identification. Every transpose zero is the
  metric dual of an adjoint zero. Its evaluation on v is exactly <w,v>.
  Closed range and smooth solvability come from the two-sided parametrix;
  no uniqueness of a solution and no self-adjointness of P is asserted. -/
  -- The specialized explicit metrics retain both the native adjoint and the original integral.
  have hrange := P.mem_range_iff_pairing_metricFormalAdjoint_eq_zero
    (SmoothHermitianMetric.ofInnerProduct E) (SmoothHermitianMetric.ofInnerProduct F) A B Q hQ v
  rw [P.metricFormalAdjoint_ofInnerProduct μ] at hrange
  simpa only [sectionPairing_ofInnerProduct] using hrange

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Smooth geometric adjoint zeros test the actual closed range at every critical Sobolev order. -/
theorem mem_range_sobolevExtension_iff_pairing_formalAdjoint_eq_zero_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ)
    (v : B.SobolevSpace (s - m)) :
    v ∈ (P.sobolevExtension A B s).range ↔
      ∀ w : P.formalAdjoint.toLinearMap.ker,
        B.sobolevPairing μ (s - m) (B.smoothToSobolev (-(s - m)) w.val) v = 0 := by
  /- Stage 1: the Fredholm range is closed, so continuous annihilators detect
  range membership. Geometric Sobolev duality and the weak adjoint identity
  identify these annihilators with the weak geometric adjoint kernel.
  Stage 2: its natural smooth-kernel equivalence supplies precisely the
  displayed smooth tests, with order -(s-m). Without closedness, the same
  separation argument would detect only the closure of the range. -/
  -- Identify the completed pairings via their specified native metric maps.
  have hpair (t : ℝ) (w : B.SobolevSpace (-t)) (z : B.SobolevSpace t) :
      (SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F).sobolevPairing B μ t w z =
        B.sobolevPairing μ t w z := by
    change B.sobolevEvaluationPairing μ t
      ((SmoothHermitianMetric.ofInnerProduct F).sobolevDual B (-t) w) z = _
    rw [sobolevDual_ofInnerProduct, B.sobolevEvaluationPairing_hermitian]
  have hrange := P.mem_range_sobolevExtension_iff_pairing_metricFormalAdjoint_eq_zero
    (SmoothHermitianMetric.ofInnerProduct E) (SmoothHermitianMetric.ofInnerProduct F)
    A B Q hQ s v
  rw [P.metricFormalAdjoint_ofInnerProduct μ] at hrange
  simpa only [hpair] using hrange

end PseudodifferentialOperator

end AtiyahSinger

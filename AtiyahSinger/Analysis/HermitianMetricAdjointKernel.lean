/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricSobolev
public import AtiyahSinger.Analysis.PseudodifferentialCokernel

/-!
# Explicit-metric adjoint kernels and the smooth cokernel

Public module ID: M0719.

A06/A07: the natural weak-kernel embedding and quotient projection are kept as
actual maps. The original right smoothing error suffices for adjoint regularity;
a two-sided parametrix supplies finiteness and closed range. Sources: SG III.5.2–5.3,
(5.1)–(5.2), pp.194–195; these natural-map comparisons are project refinements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The smooth embedding carries an adjoint zero into its specified weak kernel. -/
theorem smoothToSobolev_mem_ker_metricSobolevAdjoint (s : ℝ)
    (v : (P.metricFormalAdjoint h k).toLinearMap.ker) :
    B.smoothToSobolev (-(s - m)) v.val ∈ (P.metricSobolevAdjoint h k A B s).ker := by
  /- Apply metricSobolevAdjoint_smooth to the kernel vector. Its smooth
  adjoint image is zero by membership, so its embedded output in order -s is
  zero. This checks exactly the codomain of the restricted smooth embedding. -/
  change P.metricSobolevAdjoint h k A B s (B.smoothToSobolev (-(s - m)) v.val) = 0
  rw [P.metricSobolevAdjoint_smooth, v.property, map_zero]

/-- Restrict the original smooth embedding to the actual two adjoint kernels. -/
def metricSobolevAdjointKerMap (s : ℝ) :
    (P.metricFormalAdjoint h k).toLinearMap.ker →ₗ[ℂ]
      (P.metricSobolevAdjoint h k A B s).ker :=
  ((B.smoothToSobolev (-(s - m))).comp
    (P.metricFormalAdjoint h k).toLinearMap.ker.subtype).codRestrict
      (P.metricSobolevAdjoint h k A B s).ker
      (P.smoothToSobolev_mem_ker_metricSobolevAdjoint h k A B s)

variable (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))

/-- The original right smoothing error gives a unique smooth lift of any weak adjoint zero. -/
theorem existsUnique_smooth_of_metricSobolevAdjoint_eq_zero
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) (v : B.SobolevSpace (-(s - m)))
    (hv : P.metricSobolevAdjoint h k A B s v = 0) :
    ∃! w : smoothSections (n := n) (r := q) F,
      B.smoothToSobolev (-(s - m)) w = v ∧ (P.metricFormalAdjoint h k).toLinearMap w = 0 := by
  /- Metric Sobolev duality carries v to a weak bilinear transpose zero.
  The original right error P Q-I becomes a left error for that transpose, so
  transpose regularity supplies a smooth dual representative. Invert the
  smooth metric identification and use its Sobolev compatibility to lift the
  same v. Injectivity of the smooth embedding gives uniqueness for that input. -/
  have htrans : P.sobolevTranspose A B s (k.sobolevDual B (-(s - m)) v) = 0 := by
    rw [P.sobolevTranspose_metric, hv, map_zero]
  obtain ⟨β, hβ, _⟩ :=
    P.existsUnique_smooth_of_sobolevTranspose_eq_zero_of_isSmoothingOperator
      A B Q hQ s (k.sobolevDual B (-(s - m)) v) htrans
  let w := k.dualSectionsEquiv.symm ((dualSectionsEquiv F).symm β)
  have hw : B.smoothToSobolev (-(s - m)) w = v := by
    apply (k.sobolevDual B (-(s - m))).injective
    rw [k.sobolevDual_smooth]
    simpa only [w, LinearEquiv.apply_symm_apply] using hβ.1
  -- Faithfulness of the original embedding verifies the actual smooth adjoint equation.
  have hPw : (P.metricFormalAdjoint h k).toLinearMap w = 0 := by
    apply A.smoothToSobolev_injective (-s)
    rw [map_zero, ← P.metricSobolevAdjoint_smooth, hw]
    exact hv
  refine ⟨w, ⟨hw, hPw⟩, ?_⟩
  intro z hz
  exact B.smoothToSobolev_injective (-(s - m)) (hz.1.trans hw.symm)

/-- The right smoothing error makes the natural smooth-kernel map bijective. -/
theorem bijective_metricSobolevAdjointKerMap
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id))
    (s : ℝ) : Function.Bijective (P.metricSobolevAdjointKerMap h k A B s) := by
  /- Injectivity follows from the original smooth-to-Sobolev injection.
  For a weak kernel vector apply the unique smooth lifting theorem to its
  ambient value. The lift is a smooth adjoint zero and maps to that vector. -/
  constructor
  · intro u v huv
    apply Subtype.ext
    exact B.smoothToSobolev_injective (-(s - m)) (congrArg Subtype.val huv)
  · intro v
    obtain ⟨w, ⟨hw, hPw⟩, _⟩ :=
      P.existsUnique_smooth_of_metricSobolevAdjoint_eq_zero
        h k A B Q hQ s v.val v.property
    exact ⟨⟨w, hPw⟩, Subtype.ext hw⟩

/-- The adjoint-kernel equivalence retains the actual smooth embedding. -/
def metricSobolevAdjointKerEquiv
    (hQ : IsSmoothingOperator μ (P.toLinearMap.comp Q.toLinearMap - LinearMap.id)) (s : ℝ) :
    (P.metricFormalAdjoint h k).toLinearMap.ker ≃ₗ[ℂ]
      (P.metricSobolevAdjoint h k A B s).ker :=
  LinearEquiv.ofBijective (P.metricSobolevAdjointKerMap h k A B s)
    (P.bijective_metricSobolevAdjointKerMap h k A B Q hQ s)

include A B in
/-- A two-sided parametrix makes the smooth explicit-metric adjoint kernel finite-dimensional. -/
theorem finiteDimensional_ker_metricFormalAdjoint_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    FiniteDimensional ℂ (P.metricFormalAdjoint h k).toLinearMap.ker := by
  /- The smooth metric identification gives a conjugate-linear
  equivalence with the bilinear transpose kernel. Its two-sided transposed
  parametrix gives finite dimension; transport that property across this
  semilinear equivalence, without calling the metric identification linear. -/
  let e := k.dualSectionsEquiv.trans (dualSectionsEquiv F)
  let : FiniteDimensional ℂ P.formalTranspose.toLinearMap.ker :=
    P.finiteDimensional_ker_formalTranspose_of_isParametrix A B Q hQ
  -- Inverse metric duality is a surjective semilinear map between the specified kernels.
  have hzero (β : P.formalTranspose.toLinearMap.ker) :
      (P.metricFormalAdjoint h k).toLinearMap (e.symm β.val) = 0 := by
    apply h.dualSectionsEquiv.injective
    apply (dualSectionsEquiv E).injective
    rw [← P.formalTranspose_metric,
      show dualSectionsEquiv F (k.dualSectionsEquiv (e.symm β.val)) = β.val from
        e.apply_symm_apply β.val, β.property, map_zero, map_zero]
  let T : P.formalTranspose.toLinearMap.ker →ₗ⋆[ℂ]
      (P.metricFormalAdjoint h k).toLinearMap.ker :=
    (e.symm.toLinearMap.comp P.formalTranspose.toLinearMap.ker.subtype).codRestrict
      (P.metricFormalAdjoint h k).toLinearMap.ker hzero
  have hT : Function.Surjective T := by
    intro w
    have hw : P.formalTranspose.toLinearMap (e w.val) = 0 := by
      change P.formalTranspose.toLinearMap (dualSectionsEquiv F (k.dualSectionsEquiv w.val)) = 0
      rw [P.formalTranspose_metric, w.property, map_zero, map_zero]
    refine ⟨⟨e w.val, hw⟩, Subtype.ext ?_⟩
    exact e.symm_apply_apply w.val
  exact Module.Finite.of_surjective T hT

include A B in
/-- The original smooth quotient projection restricts to a bijection on the adjoint kernel. -/
theorem bijective_ker_metricFormalAdjoint_to_coker
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    Function.Bijective
      (P.toLinearMap.range.mkQ.comp (P.metricFormalAdjoint h k).toLinearMap.ker.subtype) := by
  /- The transpose cokernel theorem and metric duality give equal finite
  dimensions for this kernel and the smooth cokernel. If w=Pu also lies in
  ker P†, the adjoint identity gives k(w,w)=h(u,P†w)=0, so w=0. Thus the
  displayed quotient map is injective and equal finite dimensions make it
  surjective. The particular projection is retained, not an arbitrary isomorphism. -/
  classical
  let K := (P.metricFormalAdjoint h k).toLinearMap.ker
  let C := smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range
  let : FiniteDimensional ℂ K :=
    P.finiteDimensional_ker_metricFormalAdjoint_of_isParametrix h k A B Q hQ
  let : FiniteDimensional ℂ C := P.finiteDimensional_coker_of_isParametrix A B Q hQ
  -- Restrict the specified metric map; this comparison remains conjugate-linear.
  let e := k.dualSectionsEquiv.trans (dualSectionsEquiv F)
  have hmap : K.map e.toLinearMap = P.formalTranspose.toLinearMap.ker := by
    ext β
    constructor
    · rintro ⟨w, hw, rfl⟩
      change P.formalTranspose.toLinearMap (dualSectionsEquiv F (k.dualSectionsEquiv w)) = 0
      rw [P.formalTranspose_metric, show (P.metricFormalAdjoint h k).toLinearMap w = 0 from
        hw, map_zero, map_zero]
    · intro hβ
      refine ⟨e.symm β, ?_, e.apply_symm_apply β⟩
      change (P.metricFormalAdjoint h k).toLinearMap (e.symm β) = 0
      apply h.dualSectionsEquiv.injective
      apply (dualSectionsEquiv E).injective
      rw [← P.formalTranspose_metric,
        show dualSectionsEquiv F (k.dualSectionsEquiv (e.symm β)) = β from
          e.apply_symm_apply β, show P.formalTranspose.toLinearMap β = 0 from hβ,
        map_zero, map_zero]
  let c := e.ofSubmodules K P.formalTranspose.toLinearMap.ker hmap
  have hdim : Module.finrank ℂ K = Module.finrank ℂ C := by
    have hrank := lift_rank_eq_of_equiv_equiv (starRingEnd ℂ) c.toAddEquiv
      (star_involutive.bijective : Function.Bijective (starRingEnd ℂ))
      (fun a v ↦ c.map_smulₛₗ a v)
    have hfin : Module.finrank ℂ K = Module.finrank ℂ P.formalTranspose.toLinearMap.ker := by
      simpa only [Module.finrank, Cardinal.toNat_lift] using congrArg Cardinal.toNat hrank
    exact hfin.trans
      (P.finrank_smoothCoker_eq_finrank_ker_formalTranspose_of_isParametrix A B Q hQ).symm
  -- Positivity makes the actual kernel inclusion followed by the quotient injective.
  let f : K →ₗ[ℂ] C := P.toLinearMap.range.mkQ.comp K.subtype
  have hfzero (w : K) (hw : f w = 0) : w = 0 := by
    have hwRange : w.val ∈ P.toLinearMap.range :=
      (Submodule.Quotient.mk_eq_zero P.toLinearMap.range).mp hw
    obtain ⟨u, hu⟩ := hwRange
    have horth := (P.metricFormalAdjoint_apply_eq_zero_iff h k w.val).mp w.property u
    rw [hu] at horth
    exact Subtype.ext ((k.sectionPairing_self_eq_zero_iff μ w.val).mp horth)
  have hfinj : Function.Injective f := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hfzero
    rw [map_sub, huv, sub_self]
  exact ⟨hfinj, (LinearEquiv.ofInjectiveOfFinrankEq f hfinj hdim).surjective⟩

/-- Include the smooth adjoint zero and take its class in the original smooth cokernel. -/
def kerMetricFormalAdjointEquivCoker
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    (P.metricFormalAdjoint h k).toLinearMap.ker ≃ₗ[ℂ]
      (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) :=
  LinearEquiv.ofBijective
    (P.toLinearMap.range.mkQ.comp (P.metricFormalAdjoint h k).toLinearMap.ker.subtype)
    (P.bijective_ker_metricFormalAdjoint_to_coker h k A B Q hQ)

/-- The natural cokernel equivalence retains the input section quotient class. -/
theorem kerMetricFormalAdjointEquivCoker_apply
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (v : (P.metricFormalAdjoint h k).toLinearMap.ker) :
    P.kerMetricFormalAdjointEquivCoker h k A B Q hQ v = P.toLinearMap.range.mkQ v.val := by
  /- The forward map in LinearEquiv.ofBijective is exactly kernel
  inclusion followed by mkQ. Evaluating it at v gives the displayed class
  in the quotient by the actual smooth range, with no closure inserted. -/
  rfl

include A B in
/-- The smooth index is the difference of the two actual smooth kernel dimensions. -/
theorem index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    P.toLinearMap.index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (P.metricFormalAdjoint h k).toLinearMap.ker := by
  /- The two-sided parametrix makes the original kernel and cokernel
  finite-dimensional. Replace the cokernel finrank by the adjoint-kernel
  finrank through the actual quotient equivalence, then use the index formula. -/
  rw [LinearMap.index_eq_finrank_sub,
    ← (P.kerMetricFormalAdjointEquivCoker h k A B Q hQ).finrank_eq]

/-- Every critical Sobolev realization has the same formula in terms of two smooth kernels. -/
theorem index_sobolevExtension_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    (P.sobolevExtension A B s).index = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (P.metricFormalAdjoint h k).toLinearMap.ker := by
  /- Use the existing natural smooth/Sobolev kernel and cokernel
  comparisons for this two-sided parametrix. They identify the bounded index
  with P's smooth index, to which the preceding explicit-metric formula applies. -/
  rw [P.index_sobolevExtension_eq_of_isParametrix A B Q hQ s]
  exact P.index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint h k A B Q hQ

include A B in
/-- Smooth solvability is equivalent to orthogonality to the explicit-metric adjoint kernel. -/
theorem mem_range_iff_pairing_metricFormalAdjoint_eq_zero
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (v : smoothSections (n := n) (r := q) F) :
    v ∈ P.toLinearMap.range ↔
      ∀ w : (P.metricFormalAdjoint h k).toLinearMap.ker, k.sectionPairing μ w.val v = 0 := by
  /- Transform the bilinear transpose range criterion by the smooth
  metric identification. Its evaluation becomes k(w,v), and every transpose
  zero arises uniquely this way. Closed range and smooth solvability are
  supplied by the two-sided parametrix, without uniqueness of solutions. -/
  let e := k.dualSectionsEquiv.trans (dualSectionsEquiv F)
  have hker (w : smoothSections (n := n) (r := q) F) :
      e w ∈ P.formalTranspose.toLinearMap.ker ↔
        w ∈ (P.metricFormalAdjoint h k).toLinearMap.ker := by
    change P.formalTranspose.toLinearMap (dualSectionsEquiv F (k.dualSectionsEquiv w)) = 0 ↔ _
    rw [P.formalTranspose_metric]
    constructor
    · intro hw
      apply h.dualSectionsEquiv.injective
      apply (dualSectionsEquiv E).injective
      simpa only [map_zero] using hw
    · intro hw
      rw [show (P.metricFormalAdjoint h k).toLinearMap w = 0 from hw, map_zero, map_zero]
  rw [P.mem_range_iff_of_isParametrix A B Q hQ]
  constructor
  · intro hv w
    let β : P.formalTranspose.toLinearMap.ker := ⟨e w.val, (hker w.val).mpr w.property⟩
    have hz := hv β
    change smoothDualSectionPairing F μ (k.dualSectionsEquiv w.val) v = 0 at hz
    rwa [k.dualSectionPairing_dualSectionsEquiv] at hz
  · intro hv β
    obtain ⟨w, hw⟩ := e.surjective β.val
    have hPw : w ∈ (P.metricFormalAdjoint h k).toLinearMap.ker := by
      apply (hker w).mp
      rw [hw]
      exact β.property
    have hz := hv ⟨w, hPw⟩
    rw [← k.dualSectionPairing_dualSectionsEquiv] at hz
    rw [← hw]
    exact hz

/-- Smooth adjoint zeros test the closed range at every critical Sobolev order. -/
theorem mem_range_sobolevExtension_iff_pairing_metricFormalAdjoint_eq_zero
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ)
    (v : B.SobolevSpace (s - m)) :
    v ∈ (P.sobolevExtension A B s).range ↔
      ∀ w : (P.metricFormalAdjoint h k).toLinearMap.ker,
        k.sobolevPairing B μ (s - m) (B.smoothToSobolev (-(s - m)) w.val) v = 0 := by
  /- Fredholmness makes the actual Sobolev range closed. Continuous
  annihilators therefore detect range membership. Explicit-metric duality
  identifies these with weak adjoint zeros, and right-error regularity lifts
  each to the displayed smooth test at order -(s-m). -/
  let e := k.dualSectionsEquiv.trans (dualSectionsEquiv F)
  have hker (w : smoothSections (n := n) (r := q) F) :
      e w ∈ P.formalTranspose.toLinearMap.ker ↔
        w ∈ (P.metricFormalAdjoint h k).toLinearMap.ker := by
    change P.formalTranspose.toLinearMap (dualSectionsEquiv F (k.dualSectionsEquiv w)) = 0 ↔ _
    rw [P.formalTranspose_metric]
    constructor
    · intro hw
      apply h.dualSectionsEquiv.injective
      apply (dualSectionsEquiv E).injective
      simpa only [map_zero] using hw
    · intro hw
      rw [show (P.metricFormalAdjoint h k).toLinearMap w = 0 from hw, map_zero, map_zero]
  rw [P.mem_range_sobolevExtension_iff_of_isParametrix A B Q hQ s]
  constructor
  · intro hv w
    let β : P.formalTranspose.toLinearMap.ker := ⟨e w.val, (hker w.val).mpr w.property⟩
    change B.sobolevEvaluationDuality μ (s - m)
      (k.sobolevDual B (-(s - m)) (B.smoothToSobolev (-(s - m)) w.val)) v = 0
    rw [k.sobolevDual_smooth]
    simpa only [β, e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hv β
  · intro hv β
    obtain ⟨w, hw⟩ := e.surjective β.val
    have hPw : w ∈ (P.metricFormalAdjoint h k).toLinearMap.ker := by
      apply (hker w).mp
      rw [hw]
      exact β.property
    have hz := hv ⟨w, hPw⟩
    change B.sobolevEvaluationDuality μ (s - m)
      (k.sobolevDual B (-(s - m)) (B.smoothToSobolev (-(s - m)) w)) v = 0 at hz
    rw [k.sobolevDual_smooth] at hz
    rw [← hw]
    simpa only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hz

variable (h' : SmoothHermitianMetric (n := n) (r := r) E)
  (k' : SmoothHermitianMetric (n := n) (r := q) F)

/-- Inverse output-metric change carries an old adjoint zero to a new one. -/
theorem changeSections_mem_ker_metricFormalAdjoint
    (v : (P.metricFormalAdjoint h k).toLinearMap.ker) :
    k'.changeSections k v.val ∈ (P.metricFormalAdjoint h' k').toLinearMap.ker := by
  /- Substitute the exact adjoint conjugation formula. The new output
  multiplier B_F cancels the inverse multiplier applied to v, and the old
  adjoint then gives zero. The invertible input-metric factor sends zero to zero. -/
  change (P.metricFormalAdjoint h' k').toLinearMap (k'.changeSections k v.val) = 0
  rw [P.metricFormalAdjoint_change h k h' k']
  change h'.changeSections h
    ((P.metricFormalAdjoint h k).toLinearMap (k.changeSections k' (k'.changeSections k v.val))) = 0
  rw [← k.changeSections_symm k', LinearEquiv.apply_symm_apply, v.property, map_zero]

/-- The explicit inverse output-metric multiplier restricted to adjoint kernels. -/
def metricAdjointKerChange : (P.metricFormalAdjoint h k).toLinearMap.ker →ₗ[ℂ]
    (P.metricFormalAdjoint h' k').toLinearMap.ker :=
  ((k'.changeSections k).toLinearMap.comp
    (P.metricFormalAdjoint h k).toLinearMap.ker.subtype).codRestrict
      (P.metricFormalAdjoint h' k').toLinearMap.ker
      (P.changeSections_mem_ker_metricFormalAdjoint h k h' k')

/-- The specified kernel multiplier is bijective without an ellipticity assumption. -/
theorem bijective_metricAdjointKerChange :
    Function.Bijective (P.metricAdjointKerChange h k h' k') := by
  /- Use the reverse metric-change map as inverse. The two output
  multipliers are inverse on all smooth sections; the membership theorem in
  both directions restricts these identities to the exact adjoint kernels. -/
  have hforward (v : (P.metricFormalAdjoint h k).toLinearMap.ker) :
      (P.metricAdjointKerChange h k h' k' v).val = k'.changeSections k v.val := rfl
  have hbackward (v : (P.metricFormalAdjoint h' k').toLinearMap.ker) :
      (P.metricAdjointKerChange h' k' h k v).val = k.changeSections k' v.val := rfl
  have hleft : Function.LeftInverse (P.metricAdjointKerChange h' k' h k)
      (P.metricAdjointKerChange h k h' k') := by
    intro v
    apply Subtype.ext
    rw [hbackward, hforward, ← k.changeSections_symm k', LinearEquiv.apply_symm_apply]
  have hright : Function.RightInverse (P.metricAdjointKerChange h' k' h k)
      (P.metricAdjointKerChange h k h' k') := by
    intro v
    apply Subtype.ext
    rw [hforward, hbackward, ← k.changeSections_symm k', LinearEquiv.symm_apply_apply]
  exact ⟨hleft.injective, hright.surjective⟩

/-- The natural metric-multiplier equivalence between smooth adjoint kernels. -/
def metricAdjointKerEquiv : (P.metricFormalAdjoint h k).toLinearMap.ker ≃ₗ[ℂ]
    (P.metricFormalAdjoint h' k').toLinearMap.ker :=
  LinearEquiv.ofBijective (P.metricAdjointKerChange h k h' k')
    (P.bijective_metricAdjointKerChange h k h' k')

end PseudodifferentialOperator

end AtiyahSinger

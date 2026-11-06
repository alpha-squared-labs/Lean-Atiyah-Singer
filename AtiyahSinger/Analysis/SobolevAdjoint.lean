/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DualSobolev
public import AtiyahSinger.Analysis.GlobalFormalAdjoint
public import AtiyahSinger.Analysis.HermitianMetricDifferentialAdjoint

/-!
# Formal transposes and opposite-order Sobolev adjoints

Public module ID: M0987.

D02/A07, SG III.(3.18), (5.1), and pp.194-195. First construct the metric-free
transpose on actual smooth dual sections from its integral identity. Its bounded
extension is the continuous transpose H^(m-s)(F*) -> H^(-s)(E*).

The Hermitian version is the Sobolev extension of the already constructed formal
adjoint. It has the same opposite orders. None of these results assumes ellipticity
or closed range. They are not identifications with the Hilbert adjoint for arbitrary
localized Sobolev inner products. Elliptic regularity and Fredholmness remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- SG (3.18): a differential operator has a unique transpose on smooth dual sections. -/
theorem existsUnique_formalTranspose :
    ∃! T : smoothDualSections (n := n) (r := q) F →ₗ[ℂ]
        smoothDualSections (n := n) (r := r) E,
      ∀ (α : smoothDualSections (n := n) (r := q) F)
        (u : smoothSections (n := n) (r := r) E),
        smoothDualSectionPairing E μ (T α) u =
          smoothDualSectionPairing F μ α (P.toLinearMap u) := by
  classical
  -- Auxiliary metrics construct the transpose; its bilinear identity fixes it uniquely.
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) (E := E)
  obtain ⟨k⟩ := nonempty_smoothHermitianMetric (n := n) (r := q) (E := F)
  let Q := P.metricFormalAdjoint (μ := μ) h k
  have hQ : IsMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap :=
    P.isMetricFormalAdjoint_metricFormalAdjoint h k
  let T : smoothDualSections (n := n) (r := q) F →ₗ[ℂ]
      smoothDualSections (n := n) (r := r) E :=
    h.dualSectionsEquiv.toLinearMap.comp
      (Q.toLinearMap.comp k.dualSectionsEquiv.symm.toLinearMap)
  have hT : ∀ α u, smoothDualSectionPairing E μ (T α) u =
      smoothDualSectionPairing F μ α (P.toLinearMap u) := by
    intro α u
    change smoothDualSectionPairing E μ
      (h.dualSectionsEquiv (Q.toLinearMap (k.dualSectionsEquiv.symm α))) u = _
    rw [h.dualSectionPairing_dualSectionsEquiv]
    rw [hQ.symm]
    rw [← k.dualSectionPairing_dualSectionsEquiv, k.dualSectionsEquiv.apply_symm_apply]
  refine ⟨T, hT, ?_⟩
  -- Transport an arbitrary transpose back to the primal bundles and use adjoint uniqueness.
  intro R hR
  let S : smoothSections (n := n) (r := q) F →ₗ[ℂ]
      smoothSections (n := n) (r := r) E :=
    h.dualSectionsEquiv.symm.toLinearMap.comp
      (R.comp k.dualSectionsEquiv.toLinearMap)
  have hSP : IsMetricFormalAdjoint k h μ S P.toLinearMap := by
    intro v u
    rw [← h.dualSectionPairing_dualSectionsEquiv]
    change smoothDualSectionPairing E μ
      (h.dualSectionsEquiv (h.dualSectionsEquiv.symm (R (k.dualSectionsEquiv v)))) u = _
    rw [h.dualSectionsEquiv.apply_symm_apply, hR,
      k.dualSectionPairing_dualSectionsEquiv]
  have hQS : Q.toLinearMap = S := hQ.unique hSP.symm
  apply LinearMap.ext
  intro α
  have hv := congrArg (fun A ↦ h.dualSectionsEquiv (A (k.dualSectionsEquiv.symm α))) hQS
  simpa [S, T] using hv.symm

/-- The geometric transpose, uniquely determined by the bilinear integral identity. -/
def formalTranspose :
    smoothDualSections (n := n) (r := q) F →ₗ[ℂ]
      smoothDualSections (n := n) (r := r) E :=
  Classical.choose (P.existsUnique_formalTranspose μ).exists

/-- The constructed transpose satisfies its integral identity on actual smooth sections. -/
theorem smoothDualSectionPairing_formalTranspose
    (α : smoothDualSections (n := n) (r := q) F)
    (u : smoothSections (n := n) (r := r) E) :
    smoothDualSectionPairing E μ (P.formalTranspose μ α) u =
      smoothDualSectionPairing F μ α (P.toLinearMap u) := by
  -- Read the identity for the chosen map, using the original density and dual sections.
  exact (P.existsUnique_formalTranspose μ).exists.choose_spec α u

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The smooth transpose has a unique bounded extension at the opposite Sobolev orders. -/
theorem existsUnique_sobolevTranspose (s : ℝ) :
    ∃! T : B.DualSobolevSpace (-(s - m)) →L[ℂ] A.DualSobolevSpace (-s),
      ∀ α : smoothDualSections (n := n) (r := q) F,
        T (B.dualSmoothToSobolev (-(s - m)) α) =
          A.dualSmoothToSobolev (-s) (P.formalTranspose μ α) := by
  /- Stage 1: precompose a continuous functional on H^(s-m)(F) with the bounded
  realization P:H^s(E)->H^(s-m)(F). This is a bounded map on continuous dual spaces.
  Stage 2: conjugate that map by the two bilinear Sobolev duality equivalences. Its
  domain is H^(-(s-m))(F*) and its codomain is H^(-s)(E*).
  Stage 3: the smooth transpose integral identity and separation by smooth tests
  show that this map extends the actual formalTranspose. Smooth dual density gives uniqueness. -/
  -- Transport actual precomposition through the two perfect bilinear duality maps.
  let T : B.DualSobolevSpace (-(s - m)) →L[ℂ] A.DualSobolevSpace (-s) :=
    (A.sobolevEvaluationDuality μ s).symm.toContinuousLinearMap.comp
      (((ContinuousLinearMap.compL ℂ (A.SobolevSpace s) (B.SobolevSpace (s - m)) ℂ).flip
        (P.sobolevExtension A B s)).comp
          (B.sobolevEvaluationDuality μ (s - m)).toContinuousLinearMap)
  have hT (α : smoothDualSections (n := n) (r := q) F) :
      T (B.dualSmoothToSobolev (-(s - m)) α) =
        A.dualSmoothToSobolev (-s) (P.formalTranspose μ α) := by
    apply (A.sobolevEvaluationDuality μ s).injective
    change (A.sobolevEvaluationDuality μ s)
      ((A.sobolevEvaluationDuality μ s).symm _) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer
      (((B.sobolevEvaluationDuality μ (s - m))
        (B.dualSmoothToSobolev (-(s - m)) α)).comp
          (P.sobolevExtension A B s)).continuous
      ((A.sobolevEvaluationDuality μ s) _).continuous
    funext u
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [P.sobolevExtension_smoothToSobolev]
    change B.sobolevEvaluationPairing μ (s - m) _ _ =
      A.sobolevEvaluationPairing μ s _ _
    rw [B.sobolevEvaluationPairing_smooth, A.sobolevEvaluationPairing_smooth]
    exact (P.smoothDualSectionPairing_formalTranspose μ α u).symm
  refine ⟨T, hT, ?_⟩
  -- Agreement on the same dense smooth dual image determines the bounded extension.
  intro S hS
  apply DFunLike.coe_injective
  apply (B.denseRange_dualSmoothToSobolev (-(s - m))).equalizer S.continuous T.continuous
  funext α
  exact (hS α).trans (hT α).symm

/-- The continuous transpose expressed in the concrete opposite-order dual-bundle completions. -/
def sobolevTranspose (s : ℝ) :
    B.DualSobolevSpace (-(s - m)) →L[ℂ] A.DualSobolevSpace (-s) :=
  Classical.choose (P.existsUnique_sobolevTranspose μ A B s).exists

/-- The Sobolev transpose extends the actual smooth transpose. -/
theorem sobolevTranspose_smooth (s : ℝ)
    (α : smoothDualSections (n := n) (r := q) F) :
    P.sobolevTranspose μ A B s (B.dualSmoothToSobolev (-(s - m)) α) =
      A.dualSmoothToSobolev (-s) (P.formalTranspose μ α) := by
  /- Unpack the specifying property of the chosen extension. This records the link
  to the original section operator rather than only to an abstract dual-space map. -/
  exact (P.existsUnique_sobolevTranspose μ A B s).exists.choose_spec α

set_option maxHeartbeats 800000 in
-- Normalize the dependent dual-space maps while extending the same smooth transpose identity.
/-- SG (5.1): the transpose is precomposition on the continuous duals under geometric duality. -/
theorem sobolevEvaluationDuality_transpose (s : ℝ)
    (α : B.DualSobolevSpace (-(s - m))) :
    A.sobolevEvaluationDuality μ s (P.sobolevTranspose μ A B s α) =
      (B.sobolevEvaluationDuality μ (s - m) α).comp (P.sobolevExtension A B s) := by
  /- On smooth covectors and primal sections this is exactly the formal transpose
  integral identity. Extend first in the primal input and then in the dual input by
  continuity and density. Equality on every primal input gives equality of the functionals. -/
  -- Equality of the two continuous maps follows from their common dense smooth inputs.
  have hmap := (B.denseRange_dualSmoothToSobolev (-(s - m))).equalizer
    ((A.sobolevEvaluationDuality μ s).continuous.comp
      (P.sobolevTranspose μ A B s).continuous)
    ((((ContinuousLinearMap.compL ℂ (A.SobolevSpace s) (B.SobolevSpace (s - m)) ℂ).flip
      (P.sobolevExtension A B s)).continuous).comp
        (B.sobolevEvaluationDuality μ (s - m)).continuous) (by
      funext β
      simp only [Function.comp_apply]
      rw [P.sobolevTranspose_smooth]
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev s).equalizer
        ((A.sobolevEvaluationDuality μ s) _).continuous
        (((B.sobolevEvaluationDuality μ (s - m))
          (B.dualSmoothToSobolev (-(s - m)) β)).comp
            (P.sobolevExtension A B s)).continuous
      funext u
      change A.sobolevEvaluationPairing μ s _ (A.smoothToSobolev s u) =
        B.sobolevEvaluationPairing μ (s - m) _
          (P.sobolevExtension A B s (A.smoothToSobolev s u))
      rw [P.sobolevExtension_smoothToSobolev,
        A.sobolevEvaluationPairing_smooth, B.sobolevEvaluationPairing_smooth]
      exact P.smoothDualSectionPairing_formalTranspose μ β u)
  exact congrFun hmap α

/-- The transpose kernel is the annihilator of the range, without a closed-range assumption. -/
theorem sobolevTranspose_eq_zero_iff (s : ℝ)
    (α : B.DualSobolevSpace (-(s - m))) :
    P.sobolevTranspose μ A B s α = 0 ↔
      ∀ u : A.SobolevSpace s,
        B.sobolevEvaluationPairing μ (s - m) α (P.sobolevExtension A B s u) = 0 := by
  /- Apply the injective duality equivalence to the transpose output. The preceding
  identity identifies its functional with evaluation on P's range. A functional is
  zero exactly when its value on every input is zero. Closed range is not needed. -/
  constructor
  · intro h u
    change ((B.sobolevEvaluationDuality μ (s - m) α).comp
      (P.sobolevExtension A B s)) u = 0
    rw [← P.sobolevEvaluationDuality_transpose μ A B s α, h, map_zero]
    rfl
  · intro h
    apply (A.sobolevEvaluationDuality μ s).injective
    rw [P.sobolevEvaluationDuality_transpose, map_zero]
    apply ContinuousLinearMap.ext
    exact h

end DifferentialOperator

end AtiyahSinger

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothHermitianBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothHermitianBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Hermitian identification converts the bilinear transpose into the geometric formal adjoint. -/
theorem formalTranspose_hermitian (v : smoothSections (n := n) (r := q) F) :
    P.formalTranspose μ (smoothHermitianDualEquiv F v) =
      smoothHermitianDualEquiv E ((P.formalAdjoint μ).toLinearMap v) := by
  /- Evaluate both sides against an arbitrary smooth primal section and integrate.
  Convert covector evaluation to the Hermitian pairing. Conjugate the defining
  formal-adjoint identity because mathlib makes its first inner-product variable
  conjugate-linear. The resulting integrals agree; smooth tests separate covectors. -/
  -- Transport the actual adjoint through the two specified Hermitian identifications.
  let e := smoothHermitianDualEquiv (n := n) (r := r) E
  let f := smoothHermitianDualEquiv (n := n) (r := q) F
  let T : smoothDualSections (n := n) (r := q) F →ₗ[ℂ]
      smoothDualSections (n := n) (r := r) E :=
    e.toLinearMap.comp ((P.formalAdjoint μ).toLinearMap.comp f.symm.toLinearMap)
  have hT : ∀ α u, smoothDualSectionPairing E μ (T α) u =
      smoothDualSectionPairing F μ α (P.toLinearMap u) := by
    intro α u
    obtain ⟨w, rfl⟩ := f.surjective α
    have hTw : T (f w) = e ((P.formalAdjoint μ).toLinearMap w) := by simp [T]
    rw [hTw]
    change smoothDualSectionPairing E μ (smoothHermitianDualEquiv E
      ((P.formalAdjoint μ).toLinearMap w)) u =
        smoothDualSectionPairing F μ (smoothHermitianDualEquiv F w) (P.toLinearMap u)
    rw [smoothDualSectionPairing_hermitian, smoothDualSectionPairing_hermitian]
    have hpair := congrArg (starRingEnd ℂ) (P.isFormalAdjoint_formalAdjoint μ u w)
    simpa only [smoothSectionPairing, ← integral_conj, inner_conj_symm] using hpair.symm
  -- The original uniqueness theorem identifies maps on all smooth dual sections.
  have hmaps : T = P.formalTranspose μ :=
    (P.existsUnique_formalTranspose μ).unique hT (P.smoothDualSectionPairing_formalTranspose μ)
  change P.formalTranspose μ (f v) = e ((P.formalAdjoint μ).toLinearMap v)
  rw [← hmaps]
  simp [T]

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The actual Sobolev extension of the formal adjoint, with its target order normalized. -/
def sobolevFormalAdjoint (s : ℝ) :
    B.SobolevSpace (-(s - m)) →L[ℂ] A.SobolevSpace (-s) := by
  have h : -(s - (m : ℝ)) - (m : ℝ) = -s := by ring
  exact h ▸ (P.formalAdjoint μ).sobolevExtension B A (-(s - m))

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The opposite-order realization acts on smooth sections by the original formal adjoint. -/
theorem sobolevFormalAdjoint_smooth (s : ℝ)
    (v : smoothSections (n := n) (r := q) F) :
    P.sobolevFormalAdjoint μ A B s (B.smoothToSobolev (-(s - m)) v) =
      A.smoothToSobolev (-s) ((P.formalAdjoint μ).toLinearMap v) := by
  /- Use the smooth-input formula for the formal adjoint's Sobolev extension.
  The only additional step is the real-order identity -(s-m)-m=-s used in the definition. -/
  have htransport (t : ℝ) (ht : -(s - (m : ℝ)) - (m : ℝ) = t) :
      (ht ▸ (P.formalAdjoint μ).sobolevExtension B A (-(s - m)))
          (B.smoothToSobolev (-(s - m)) v) =
        A.smoothToSobolev t ((P.formalAdjoint μ).toLinearMap v) := by
    subst t
    exact (P.formalAdjoint μ).sobolevExtension_smoothToSobolev B A (-(s - m)) v
  exact htransport (-s) (by ring)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The Hermitian realization and bilinear transpose agree after the metric identifications. -/
theorem sobolevTranspose_hermitian (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    P.sobolevTranspose μ A B s (B.sobolevHermitianDual (-(s - m)) v) =
      A.sobolevHermitianDual (-s) (P.sobolevFormalAdjoint μ A B s v) := by
  /- All maps preserve the original dense smooth inputs. Their continuity extends
  the native metric intertwining identity to the two specified completions. -/
  refine (B.denseRange_smoothToSobolev (-(s - m))).induction_on v
    (isClosed_eq ((P.sobolevTranspose μ A B s).continuous.comp
      (B.sobolevHermitianDual (-(s - m))).continuous)
      ((A.sobolevHermitianDual (-s)).continuous.comp
        (P.sobolevFormalAdjoint μ A B s).continuous)) ?_
  intro w
  rw [B.sobolevHermitianDual_smooth, P.sobolevTranspose_smooth,
    P.sobolevFormalAdjoint_smooth, A.sobolevHermitianDual_smooth]
  exact congrArg (A.dualSmoothToSobolev (-s)) (P.formalTranspose_hermitian μ w)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The Hermitian form of SG (5.1), with all source and target orders explicit. -/
theorem sobolevDuality_formalAdjoint (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    A.sobolevDuality μ s (P.sobolevFormalAdjoint μ A B s v) =
      (B.sobolevDuality μ (s - m) v).comp (P.sobolevExtension A B s) := by
  /- Insert the same native metric maps into the proven evaluation diagram.
  Its output is the original geometric adjoint, with the displayed opposite orders. -/
  apply ContinuousLinearMap.ext
  intro u
  change A.sobolevPairing μ s (P.sobolevFormalAdjoint μ A B s v) u =
    B.sobolevPairing μ (s - m) v (P.sobolevExtension A B s u)
  rw [← A.sobolevEvaluationPairing_hermitian μ s,
    ← B.sobolevEvaluationPairing_hermitian μ (s - m)]
  change A.sobolevEvaluationDuality μ s
    (A.sobolevHermitianDual (-s) (P.sobolevFormalAdjoint μ A B s v)) u = _
  rw [← P.sobolevTranspose_hermitian]
  exact congrArg (fun f : StrongDual ℂ (A.SobolevSpace s) ↦ f u)
    (P.sobolevEvaluationDuality_transpose μ A B s
      (B.sobolevHermitianDual (-(s - m)) v))

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The weak formal-adjoint kernel is exactly the geometric annihilator of the range. -/
theorem sobolevFormalAdjoint_eq_zero_iff (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    P.sobolevFormalAdjoint μ A B s v = 0 ↔
      ∀ u : A.SobolevSpace s,
        B.sobolevPairing μ (s - m) v (P.sobolevExtension A B s u) = 0 := by
  /- The native perfect pairing is injective. The precomposition diagram turns
  zero adjoint output into vanishing on the actual Sobolev range, and conversely. -/
  constructor
  · intro h u
    change ((B.sobolevDuality μ (s - m) v).comp (P.sobolevExtension A B s)) u = 0
    rw [← P.sobolevDuality_formalAdjoint μ A B s v, h, map_zero]
    rfl
  · intro h
    apply (A.sobolevDuality μ s).injective
    rw [P.sobolevDuality_formalAdjoint, map_zero]
    apply ContinuousLinearMap.ext
    exact h

end DifferentialOperator

end AtiyahSinger

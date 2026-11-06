/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionTopology
public import AtiyahSinger.Analysis.GeometricEquivariantIndex

import AtiyahSinger.Algebra.FiniteRepresentationCoefficients
import AtiyahSinger.Analysis.FullSymbolParametrix
import AtiyahSinger.Analysis.SmoothSectionCoefficients

/-!
# The equivariant index on the original smooth kernel and cokernel

Public module ID: M0967.

SG III.9.3 defines the index of an equivariant elliptic operator as the
difference of its actual finite-dimensional kernel and cokernel representations.
This construction applies to every real order of the existing PDO calculus.
The finite presentations below are tied to the original smooth kernel and the
quotient by the original smooth range by specified linear isomorphisms and
the actual geometric action formulas. They are not arbitrary representations
having the same dimensions. Joint continuity is part of each finite presentation.

The order-zero comparison retains the same PDO, actions, metrics and measure
as the existing L² index. Its conclusion is equality in the full representation
ring, rather than equality after the dimension homomorphism. Positive-order
operators are not treated as bounded operators on L².

Sources: SG III.5.2--5.3 and III.9.3--9.4, printed pp.193--195 and 211--213.
The source uses compact Lie groups. Compactness is unnecessary for this
construction and comparison after the original smooth actions, and for the
comparison the invariant metrics and measure, have been supplied. No invariant
Sobolev norm, irreducible decomposition or equivariant order reduction is assumed.
Finite representation coordinates use integral coefficients; the index
comparisons use the specified smooth-to-L² comparison maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : LieGroup IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction

section RealOrder

variable {m : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)

include hPg hP

/-- The original smooth kernel and quotient-cokernel are finite continuous representations. -/
theorem exists_smoothKernelCokernelRepresentations :
    ∃ ρ τ : FiniteContinuousRepresentation G,
      ∃ e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] P.toLinearMap.ker,
        ∃ f : (Fin τ.dimension → ℂ) ≃ₗ[ℂ]
            (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range),
          (∀ (g : G) (v : Fin ρ.dimension → ℂ),
            (e (ρ.representation g v)).val =
              σE.smoothSectionRepresentation IG hσE g (e v).val) ∧
          (∀ (g : G) (v : smoothSections (n := n) (r := q) F),
            f (τ.representation g (f.symm (P.toLinearMap.range.mkQ v))) =
              P.toLinearMap.range.mkQ (σF.smoothSectionRepresentation IG hσF g v)) := by
  /- Ellipticity gives finite dimension of the same smooth kernel and range
  quotient. Restrict and descend the original algebraic actions. Their matrix
  coefficients are continuous integral pairings: the metric separates the
  kernel, and the actual adjoint kernel separates the original quotient.
  Finite-dimensional coefficient reconstruction then gives joint continuity
  in the fixed Fin models. Auxiliary metrics need not be invariant, and the
  cokernel remains the quotient by the original smooth range. -/
  classical
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) (E := E)
  obtain ⟨k⟩ := nonempty_smoothHermitianMetric (n := n) (r := q) (E := F)
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  let K := P.toLinearMap.ker
  let C := smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range
  let D := (P.metricFormalAdjoint h k).toLinearMap.ker
  let : FiniteDimensional ℂ K := P.finiteDimensional_ker_of_isParametrix A B Q hQ
  let : FiniteDimensional ℂ C := P.finiteDimensional_coker_of_isParametrix A B Q hQ
  let RE := σE.smoothSectionRepresentation IG hσE
  let RF := σF.smoothSectionRepresentation IG hσF
  -- Equivariance preserves the actual kernel and actual smooth range.
  have hker (g : G) : K ≤ K.comap (RE g) := by
    intro u hu
    change P.toLinearMap (RE g u) = 0
    have heq := congrArg (fun T ↦ T u) (hPg g)
    change P.toLinearMap (RE g u) = RF g (P.toLinearMap u) at heq
    rw [heq, show P.toLinearMap u = 0 from hu, map_zero]
  have hrange (g : G) : P.toLinearMap.range ≤ P.toLinearMap.range.comap (RF g) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨RE g u, congrArg (fun T ↦ T u) (hPg g)⟩
  let RK := RE.subrepresentation K hker
  let RC := RF.quotient P.toLinearMap.range hrange
  -- Positivity separates kernel vectors; every coefficient uses the original integral.
  let JK : K →ₗ[ℂ] (smoothSections (n := n) (r := r) E → ℂ) :=
    LinearMap.pi fun v ↦ ((innerSL ℂ (h.smoothToL2 μ v)).toLinearMap.comp
      (h.smoothToL2 μ)).comp K.subtype
  have hJK : Function.Injective JK := by
    intro u v huv
    have hz : JK (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hzero : h.sectionPairing μ (u - v).val (u - v).val = 0 := by
      rw [← h.inner_smoothToL2]
      exact congrFun hz (u - v).val
    apply sub_eq_zero.mp
    exact Subtype.ext ((h.sectionPairing_self_eq_zero_iff μ _).mp hzero)
  have hKcoeff (v : smoothSections (n := n) (r := r) E) (u : K) :
      Continuous (fun g : G ↦ JK (RK g u) v) := by
    have hc := h.continuous_sectionPairing_smoothSectionRepresentation μ IG σE hσE u.val v
    apply hc.congr
    intro g
    exact (h.inner_smoothToL2 μ v (RE g u.val)).symm
  obtain ⟨ρ, e, he⟩ := exists_finiteContinuousRepresentation_of_coefficients RK JK hJK hKcoeff
  -- Adjoint zeros annihilate the original range, so their pairings descend to its quotient.
  let J₀ (v : D) : smoothSections (n := n) (r := q) F →ₗ[ℂ] ℂ :=
    (innerSL ℂ (k.smoothToL2 μ v.val)).toLinearMap.comp (k.smoothToL2 μ)
  have hvanish (v : D) : P.toLinearMap.range ≤ (J₀ v).ker := by
    rintro _ ⟨u, rfl⟩
    change inner ℂ (k.smoothToL2 μ v.val) (k.smoothToL2 μ (P.toLinearMap u)) = 0
    rw [k.inner_smoothToL2, ← k.sectionPairing_conj_symm]
    rw [(P.metricFormalAdjoint_apply_eq_zero_iff h k v.val).mp v.property u]
    simp
  let JC : C →ₗ[ℂ] (D → ℂ) :=
    LinearMap.pi fun v ↦ P.toLinearMap.range.liftQ (J₀ v) (hvanish v)
  let fD := P.kerMetricFormalAdjointEquivCoker h k A B Q hQ
  have hJC : Function.Injective JC := by
    intro u v huv
    let w := fD.symm (u - v)
    have hw : fD w = u - v := fD.apply_symm_apply (u - v)
    have hz : JC (fD w) = 0 := by rw [hw, map_sub, huv, sub_self]
    have hzero : k.sectionPairing μ w.val w.val = 0 := by
      rw [← k.inner_smoothToL2]
      exact congrFun hz w
    have hwzero : w = 0 := Subtype.ext ((k.sectionPairing_self_eq_zero_iff μ _).mp hzero)
    apply sub_eq_zero.mp
    rw [← hw, hwzero, map_zero]
  have hCcoeff (v : D) (u : C) : Continuous (fun g : G ↦ JC (RC g u) v) := by
    obtain ⟨w, rfl⟩ := P.toLinearMap.range.mkQ_surjective u
    have hc := k.continuous_sectionPairing_smoothSectionRepresentation μ IG σF hσF w v.val
    apply hc.congr
    intro g
    exact (k.inner_smoothToL2 μ v.val (RF g w)).symm
  obtain ⟨τ, f, hf⟩ := exists_finiteContinuousRepresentation_of_coefficients RC JC hJC hCcoeff
  refine ⟨ρ, τ, e, f, ?_, ?_⟩
  · intro g v
    exact congrArg Subtype.val (he g v)
  · intro g v
    rw [hf, f.apply_symm_apply]
    rfl

/-- SG Definition 9.3 at any real PDO order, using the actual smooth finite representations. -/
def smoothEquivariantAnalyticIndex : RepresentationGrothendieckGroup G :=
  let h := P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  finiteRepresentationClass h.choose - finiteRepresentationClass h.choose_spec.choose

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the full kernel and quotient representations in the same finite
-- coordinates.
/-- Any actual equivariant finite coordinates give the same smooth representation-valued index. -/
theorem smoothEquivariantAnalyticIndex_eq
    (ρ τ : FiniteContinuousRepresentation G)
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] P.toLinearMap.ker)
    (f : (Fin τ.dimension → ℂ) ≃ₗ[ℂ]
      (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range))
    (he : ∀ (g : G) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation g v)).val =
        σE.smoothSectionRepresentation IG hσE g (e v).val)
    (hf : ∀ (g : G) (v : smoothSections (n := n) (r := q) F),
      f (τ.representation g (f.symm (P.toLinearMap.range.mkQ v))) =
        P.toLinearMap.range.mkQ (σF.smoothSectionRepresentation IG hσF g v)) :
    P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP =
      finiteRepresentationClass ρ - finiteRepresentationClass τ := by
  /- Stage 1: compare the chosen kernel coordinates in the definition with e.
  Their composite is a complex-linear equivalence between finite standard
  models, hence a continuous linear equivalence. Both action equations use
  the same original smooth section, so the composite intertwines the actions.
  Stage 2: compare the chosen cokernel coordinates with f. Surjectivity of
  the original quotient map extends the two displayed representative formulas
  to all cokernel elements. Their composite is therefore also an actual
  continuous intertwiner, not just an equality of dimensions.
  Stage 3: finiteRepresentationClass_eq_of_isEquivalent identifies the two
  kernel classes and the two cokernel classes separately. Subtract the
  equalities. This proves independence of finite coordinates without changing
  P, the original geometric actions or the quotient by its actual range. -/
  classical
  let hex := P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  let ρ₀ := hex.choose
  let τ₀ := hex.choose_spec.choose
  obtain ⟨e₀, f₀, he₀, hf₀⟩ := hex.choose_spec.choose_spec
  -- Compare the same smooth kernel vectors in the two finite coordinate systems.
  have hρ : ρ₀.IsEquivalent ρ := by
    refine ⟨ContRepresentation.Equiv.mk (e₀.trans e.symm).toContinuousLinearEquiv ?_⟩
    intro g
    apply ContinuousLinearMap.ext
    intro v
    apply e.injective
    apply Subtype.val_injective
    change (e (e.symm (e₀ (ρ₀.representation g v)))).val =
      (e (ρ.representation g (e.symm (e₀ v)))).val
    rw [e.apply_symm_apply, he₀, he, e.apply_symm_apply]
  -- Surjectivity of the original quotient map supplies a common section representative.
  have quotientCompare (τ₀ : FiniteContinuousRepresentation G)
      (f₀ : (Fin τ₀.dimension → ℂ) ≃ₗ[ℂ]
        (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range))
      (hf₀ : ∀ (g : G) (v : smoothSections (n := n) (r := q) F),
        f₀ (τ₀.representation g (f₀.symm (P.toLinearMap.range.mkQ v))) =
          P.toLinearMap.range.mkQ (σF.smoothSectionRepresentation IG hσF g v)) :
      τ₀.IsEquivalent τ := by
    refine ⟨ContRepresentation.Equiv.mk (f₀.trans f.symm).toContinuousLinearEquiv ?_⟩
    intro g
    apply ContinuousLinearMap.ext
    intro v
    apply f.injective
    change f (f.symm (f₀ (τ₀.representation g v))) =
      f (τ.representation g (f.symm (f₀ v)))
    refine (f.apply_symm_apply _).trans ?_
    obtain ⟨w, hw⟩ := P.toLinearMap.range.mkQ_surjective (f₀ v)
    have h₀ := hf₀ g w
    have h₁ := hf g w
    rw [hw, f₀.symm_apply_apply] at h₀
    rw [hw] at h₁
    exact h₀.trans h₁.symm
  have hτ := quotientCompare τ₀ f₀ hf₀
  change finiteRepresentationClass ρ₀ - finiteRepresentationClass τ₀ = _
  rw [finiteRepresentationClass_eq_of_isEquivalent ρ₀ ρ hρ,
    finiteRepresentationClass_eq_of_isEquivalent τ₀ τ hτ]


end RealOrder

variable (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
  (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the full kernel and quotient representations in the same finite
-- coordinates.
/-- The original order-zero L² and smooth indices agree as full virtual representations. -/
theorem equivariantAnalyticIndex_eq_smoothEquivariantAnalyticIndex :
    P.equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hPg hP =
      P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP := by
  /- Stage 1: use the original metricL2KerMap and metricL2CokerMap. Their
  bijectivity follows from ellipticity and regularity for this same order-zero
  P. On the kernel the map is exactly the original smoothToL2 inclusion; on
  the cokernel it sends the class of v to the class of that same inclusion.
  The given geometric action formulas for the L² representations show that
  both maps intertwine the original actions. Their finite-dimensional
  Hausdorff carriers make these linear bijections continuous equivalences.
  Stage 2: compose the chosen smooth finite coordinates with these exact
  comparison maps. The resulting coordinates present the actual bounded
  kernel and quotient-cokernel representations used by equivariantFredholmIndex.
  Representation-class invariance identifies each class individually.
  Stage 3: subtract in the original representation ring and unfold the
  geometric index definition. The same P, h, k, mu and group actions occur on
  both sides. No passage through the dimension homomorphism, equivariant
  order reduction or assertion of positive-order boundedness on L² is used. -/
  classical
  obtain ⟨ρ, τ, e, f, he, hf⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP ρ τ e f he hf]
  let ρL := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τL := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let hρL := h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let hτL := k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let T := P.metricL2Extension h k
  let hTg := (P.isEquivariant_iff_metricL2Extension_intertwines IG σE σF hσE hσF
    h k hInvariant kInvariant hμInvariant).mp hPg
  let hT := P.isFredholm_metricL2Extension h k hP
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ (k.L2SectionSpace μ ⧸ T.range) := hT.finite_coker
  let : IsClosed (T.range : Set (k.L2SectionSpace μ)) := hT.isClosed_range
  let RK := equivariantKernelRepresentation ρL τL T hTg
  let RC := equivariantCokernelRepresentation ρL τL T hTg
  let hRK := continuous_equivariantKernelRepresentation ρL τL T hTg hρL
  let hRC := continuous_equivariantCokernelRepresentation ρL τL T hTg hτL
  -- The kernel comparison sends each original section to that same L² vector.
  let eK : (Fin ρ.dimension → ℂ) ≃L[ℂ] T.ker :=
    (e.trans (P.metricL2KerEquiv h k hP)).toContinuousLinearEquiv
  have heK (g : G) (v : Fin ρ.dimension → ℂ) :
      eK (ρ.representation g v) = RK g (eK v) := by
    apply Subtype.ext
    change h.smoothToL2 μ (e (ρ.representation g v)).val =
      ρL g (h.smoothToL2 μ (e v).val)
    rw [he]
    exact (h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE
      hInvariant hμInvariant g (e v).val).symm
  -- On the cokernel the specified comparison sends the class of v to the class of its inclusion.
  let f₀ := LinearEquiv.ofBijective (P.metricL2CokerMap h k)
    (P.bijective_metricL2CokerMap h k hP)
  let eC : (Fin τ.dimension → ℂ) ≃L[ℂ] (k.L2SectionSpace μ ⧸ T.range) :=
    (f.trans f₀).toContinuousLinearEquiv
  have heC (g : G) (v : Fin τ.dimension → ℂ) :
      eC (τ.representation g v) = RC g (eC v) := by
    obtain ⟨w, hw⟩ := P.toLinearMap.range.mkQ_surjective (f v)
    have hfw := hf g w
    rw [hw, f.symm_apply_apply] at hfw
    change f₀ (f (τ.representation g v)) = RC g (f₀ (f v))
    rw [hfw, ← hw]
    change T.range.mkQ (k.smoothToL2 μ (σF.smoothSectionRepresentation IG hσF g w)) =
      T.range.mkQ (τL g (k.smoothToL2 μ w))
    congr 1
    exact (k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF
      kInvariant hμInvariant g w).symm
  -- Actual equivariant coordinates preserve each representation class separately.
  change representationClass RK hRK - representationClass RC hRC = _
  exact congrArg₂ (· - ·)
    (representationClass_eq_finiteRepresentationClass_of_equiv RK hRK ρ eK heK)
    (representationClass_eq_finiteRepresentationClass_of_equiv RC hRC τ eC heC)


end AtiyahSinger.PseudodifferentialOperator

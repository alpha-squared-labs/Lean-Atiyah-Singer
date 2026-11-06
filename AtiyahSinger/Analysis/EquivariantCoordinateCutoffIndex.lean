/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantIndexOperations
public import AtiyahSinger.Analysis.EquivariantSobolevCutoffIndex

/-!
# Full averaged index in fixed geometric coordinates

Public module ID: M0493.

A fixed Hilbert graph may be compared with native Sobolev and integral L²
spaces through continuous equivalences that are not isometries. The same
coordinate maps transport the actual cutoff error and the whole Fredholm
index. The source action is recovered from its injective original L²
embedding, so no atlas Sobolev norm is assumed invariant.
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
  [hG : LieGroup IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

include hInvariant

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1800000 in
-- Fix all geometric coordinates before choosing the norm radius or the native cutoff.
/-- Fixed geometric coordinates preserve the full index of close elliptic averaged cutoffs. -/
theorem exists_radius_smoothEquivariantAnalyticIndex_average_eq_of_coordinates
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    {X Y Z W : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (γ : ContRepresentation ℂ G X)
    (hγ : Continuous (fun p : G × X ↦ γ p.1 p.2))
    (R : G →* (X ≃ₗᵢ[ℂ] X)) (hR : ∀ g x, R g x = γ g x)
    (τ : ContRepresentation ℂ G W)
    (hτ : Continuous (fun p : G × W ↦ τ p.1 p.2))
    (I : A.SobolevSpace 1 ≃L[ℂ] Y) (Φ : Y ≃L[ℂ] X)
    (U : h.L2SectionSpace μ ≃L[ℂ] Z) (O : k.L2SectionSpace μ ≃L[ℂ] W)
    (J : X →L[ℂ] Z) (hJ : Function.Injective J)
    (hJg : ∀ g x, J (γ g x) = U
      (h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g (U.symm (J x))))
    (hJsmooth : ∀ u, J (Φ (I (A.smoothToSobolev 1 u))) = U (h.smoothToL2 μ u))
    (hOg : ∀ g y, O (k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant g y) =
      τ g (O y))
    (T₀ : X →L[ℂ] W)
    (hT₀g : ∀ g, T₀.comp (γ g) = (τ g).comp T₀) (hT₀ : T₀.IsFredholm) :
    let T (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1) :=
      (O.toContinuousLinearMap.comp
        ((k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp
          (P.sobolevRealization A B 1 0 (by norm_num)))).comp I.symm.toContinuousLinearMap
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
        (hP : (P.average IG σE σF hσE hσF).IsElliptic),
        ‖T P - T₀.comp Φ.toContinuousLinearMap‖ < ε →
          (P.average IG σE σF hσE hσF).smoothEquivariantAnalyticIndex
            IG σE σF hσE hσF (P.isEquivariant_average IG σE σF hσE hσF) hP =
              equivariantFredholmIndex γ τ hγ hτ T₀ hT₀g hT₀ := by
  classical
  let Ψ := Φ.symm.trans I.symm
  let J₀ := U.symm.toContinuousLinearMap.comp J
  let S₀ := O.symm.toContinuousLinearMap.comp T₀
  let τ₀ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let hτ₀ := k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  -- Injectivity of the original source embedding determines the smooth action on the graph.
  have hjg (g : G) (u : smoothSections (n := n) (r := r) E) :
      γ g (Ψ.symm (A.smoothToSobolev 1 u)) =
        Ψ.symm (A.smoothToSobolev 1 (σE.smoothSectionRepresentation IG hσE g u)) := by
    apply hJ
    change J (γ g (Φ (I (A.smoothToSobolev 1 u)))) =
      J (Φ (I (A.smoothToSobolev 1 (σE.smoothSectionRepresentation IG hσE g u))))
    rw [hJg, hJsmooth, U.symm_apply_apply, hJsmooth]
    exact congrArg U (h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE
      hInvariant hμInvariant g u)
  have hJ₀ : Function.Injective J₀ := U.symm.injective.comp hJ
  have hJ₀smooth (u : smoothSections (n := n) (r := r) E) :
      J₀ (Ψ.symm (A.smoothToSobolev 1 u)) = h.smoothToL2 μ u := by
    change U.symm (J (Φ (I (A.smoothToSobolev 1 u)))) = _
    rw [hJsmooth, U.symm_apply_apply]
  have hS₀g (g : G) : S₀.comp (γ g) = (τ₀ g).comp S₀ := by
    apply ContinuousLinearMap.ext
    intro x
    apply O.injective
    change O (O.symm (T₀ (γ g x))) = O (τ₀ g (O.symm (T₀ x)))
    rw [O.apply_symm_apply, hOg, O.apply_symm_apply]
    exact congrArg (fun T : X →L[ℂ] W ↦ T x) (hT₀g g)
  have hS₀ : S₀.IsFredholm := O.symm.isFredholm.comp hT₀
  -- The same target equivalence identifies both actual finite representation terms.
  let u : ContRepresentation.Equiv γ γ :=
    ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ X) (fun _ ↦ rfl)
  let v : ContRepresentation.Equiv τ₀ τ := ContRepresentation.Equiv.mk O (by
    intro g
    apply ContinuousLinearMap.ext
    intro y
    exact hOg g y)
  have hindex : equivariantFredholmIndex γ τ₀ hγ hτ₀ S₀ hS₀g hS₀ =
      equivariantFredholmIndex γ τ hγ hτ T₀ hT₀g hT₀ := by
    apply equivariantFredholmIndex_eq_of_equiv γ τ₀ γ τ hγ hτ₀ hγ hτ u v
      S₀ T₀ hS₀g hT₀g _ hS₀ hT₀
    apply ContinuousLinearMap.ext
    intro x
    exact (O.apply_symm_apply (T₀ x)).symm
  obtain ⟨η, hη, hstable⟩ := exists_radius_smoothEquivariantAnalyticIndex_average_eq
    IG σE σF hσE hσF h k hInvariant kInvariant hμInvariant A B
    γ hγ R hR Ψ hjg J₀ hJ₀ hJ₀smooth S₀ hS₀g hS₀
  -- Adding one to each fixed norm handles zero-dimensional or empty spaces uniformly.
  let c := (‖O.symm.toContinuousLinearMap‖ + 1) * (‖Φ.symm.toContinuousLinearMap‖ + 1)
  have hc : 0 < c := mul_pos (by positivity) (by positivity)
  have hnorm : ‖O.symm.toContinuousLinearMap‖ * ‖Φ.symm.toContinuousLinearMap‖ ≤ c :=
    mul_le_mul (le_add_of_nonneg_right (by norm_num))
      (le_add_of_nonneg_right (by norm_num)) (norm_nonneg _) (by positivity)
  dsimp only
  refine ⟨η / c, div_pos hη hc, ?_⟩
  intro P hP hclose
  let N := (k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp
    (P.sobolevRealization A B 1 0 (by norm_num))
  let D := (O.toContinuousLinearMap.comp N).comp I.symm.toContinuousLinearMap -
    T₀.comp Φ.toContinuousLinearMap
  have herror : N.comp Ψ.toContinuousLinearMap - S₀ =
      O.symm.toContinuousLinearMap.comp (D.comp Φ.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro x
    change N (I.symm (Φ.symm x)) - O.symm (T₀ x) =
      O.symm (O (N (I.symm (Φ.symm x))) - T₀ (Φ (Φ.symm x)))
    rw [map_sub, O.symm_apply_apply, Φ.apply_symm_apply]
  have hbound : ‖N.comp Ψ.toContinuousLinearMap - S₀‖ ≤ c * ‖D‖ := by
    rw [herror]
    calc
      _ ≤ ‖O.symm.toContinuousLinearMap‖ * ‖D.comp Φ.symm.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖O.symm.toContinuousLinearMap‖ * (‖D‖ * ‖Φ.symm.toContinuousLinearMap‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = (‖O.symm.toContinuousLinearMap‖ * ‖Φ.symm.toContinuousLinearMap‖) * ‖D‖ := by ring
      _ ≤ c * ‖D‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  have hDc : ‖D‖ * c < η := (lt_div_iff₀ hc).mp hclose
  have hcD : c * ‖D‖ < η := by simpa only [mul_comm] using hDc
  have hclose' : ‖N.comp Ψ.toContinuousLinearMap - S₀‖ < η := hbound.trans_lt hcD
  exact (hstable P hP hclose').trans hindex

end AtiyahSinger.PseudodifferentialOperator

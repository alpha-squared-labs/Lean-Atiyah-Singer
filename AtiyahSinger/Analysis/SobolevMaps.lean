/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev

import AtiyahSinger.Analysis.CompactQuantization
import AtiyahSinger.Analysis.DifferentialSymbol
import AtiyahSinger.Analysis.SobolevLocalization

/-!
# Maps between global Sobolev completions

Public module ID: M1001.

D04/A01/SR02. Every map is specified on
the dense image of actual smooth sections in the concrete completion. Existence and
uniqueness are specified separately; the selected maps are not arbitrary operators.

Sources: Spin Geometry III.2.6, 2.11–2.14 and 2.15(4). Real orders, including negative
orders, use distribution realizations. Rellich requires a strict drop in order and the
fixed compact supports of the finite presentation. Such a presentation itself forces
the base to be compact: its finitely many compact cutoff supports cover the base.
No ellipticity, orientation, spin structure or Hermitian bundle metric is required here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (A B : SmoothBundlePresentation (n := n) (r := r) E)

/-- SG III.2.14: changing the finite presentation gives an equivalent Sobolev norm.
Interchanging A and B gives the reverse estimate. -/
theorem exists_norm_smoothToSobolev_le (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      ‖B.smoothToSobolev s u‖ ≤ C * ‖A.smoothToSobolev s u‖ := by
  /- The same chart/frame overlap maps preserve each real Sobolev order. Apply their
  finite-partition estimate to every B-localization, then compare its Hilbert norm
  with the sum of coordinate norms. No metric or stronger fiber hypothesis is added. -/
  classical
  have hlocal (i : Fin B.size) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖schwartzSobolevCoordinate s (B.localize i u)‖ ≤
          C * ‖A.smoothToSobolev s u‖ := by
    let := B.frame_mem_atlas i
    obtain ⟨C, hC, hbound⟩ := A.exists_norm_chartLocalization_sobolev_le
      (B.chart i) (B.chart_mem_atlas i) (B.frame i) (B.cutoff i)
      (B.smooth_cutoff i) (B.support_subset i) s
    exact ⟨C, hC, fun u ↦ hbound u (B.localize i u) (fun _ ↦ rfl)⟩
  choose C hC hb using hlocal
  let D : ℝ := ∑ i, C i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ ↦ hC i)
  refine ⟨D + 1, by positivity, ?_⟩
  intro u
  -- The original squared-sum norm is controlled by the finite sum of local norms.
  have hnorm : ‖B.smoothToSobolev s u‖ ≤
      ∑ i, ‖schwartzSobolevCoordinate s (B.localize i u)‖ := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun (i : Fin B.size) _ ↦ norm_nonneg (schwartzSobolevCoordinate s (B.localize i u)))
    rw [← B.norm_smoothToSobolev_sq] at hsq
    have hnonneg : 0 ≤ ∑ i, ‖schwartzSobolevCoordinate s (B.localize i u)‖ :=
      Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
    nlinarith [norm_nonneg (B.smoothToSobolev s u)]
  calc
    ‖B.smoothToSobolev s u‖ ≤ ∑ i, ‖schwartzSobolevCoordinate s (B.localize i u)‖ := hnorm
    _ ≤ ∑ i, C i * ‖A.smoothToSobolev s u‖ := Finset.sum_le_sum (fun i _ ↦ hb i u)
    _ = D * ‖A.smoothToSobolev s u‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (D + 1) * ‖A.smoothToSobolev s u‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

/-- The identity on smooth sections extends to a unique change-of-presentation equivalence. -/
theorem existsUnique_sobolevEquiv (s : ℝ) :
    ∃! T : A.SobolevSpace s ≃L[ℂ] B.SobolevSpace s,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) = B.smoothToSobolev s u := by
  /- Extend the actual identity in both directions using the two norm estimates.
  Their compositions are identity on the dense smooth images and therefore everywhere. -/
  obtain ⟨C, _, hC⟩ := A.exists_norm_smoothToSobolev_le B s
  obtain ⟨D, _, hD⟩ := B.exists_norm_smoothToSobolev_le A s
  let T : A.SobolevSpace s →L[ℂ] B.SobolevSpace s :=
    (B.smoothToSobolev s).extendOfNorm (A.smoothToSobolev s)
  let R : B.SobolevSpace s →L[ℂ] A.SobolevSpace s :=
    (A.smoothToSobolev s).extendOfNorm (B.smoothToSobolev s)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s u) = B.smoothToSobolev s u :=
    LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s) ⟨C, hC⟩ u
  have hR (u : smoothSections (n := n) (r := r) E) :
      R (B.smoothToSobolev s u) = A.smoothToSobolev s u :=
    LinearMap.extendOfNorm_eq (B.denseRange_smoothToSobolev s) ⟨D, hD⟩ u
  have hRT : Function.LeftInverse R T := by
    intro x
    refine (A.denseRange_smoothToSobolev s).induction_on x
      (isClosed_eq (R.continuous.comp T.continuous) continuous_id) ?_
    intro u
    rw [hT, hR]
  have hTR : Function.RightInverse R T := by
    intro x
    refine (B.denseRange_smoothToSobolev s).induction_on x
      (isClosed_eq (T.continuous.comp R.continuous) continuous_id) ?_
    intro u
    rw [hR, hT]
  let e : A.SobolevSpace s ≃L[ℂ] B.SobolevSpace s :=
    { toFun := T
      invFun := R
      left_inv := hRT
      right_inv := hTR
      map_add' := T.map_add
      map_smul' := T.map_smul
      continuous_toFun := T.continuous
      continuous_invFun := R.continuous }
  refine ⟨e, hT, ?_⟩
  -- Density fixes the equivalence on exactly the original smooth sections.
  intro e' he'
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer e'.continuous e.continuous
  funext u
  exact (he' u).trans (hT u).symm

/-- The canonical equivalence extending the identity on smooth sections. -/
def sobolevEquiv (s : ℝ) : A.SobolevSpace s ≃L[ℂ] B.SobolevSpace s :=
  Classical.choose (A.existsUnique_sobolevEquiv B s).exists

/-- The presentation equivalence preserves the represented smooth section. -/
theorem sobolevEquiv_smoothToSobolev (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    A.sobolevEquiv B s (A.smoothToSobolev s u) = B.smoothToSobolev s u := by
  /- Apply the witness specification to the actual identity on the dense smooth image. -/
  exact (Classical.choose_spec (A.existsUnique_sobolevEquiv B s).exists) u

/-- The identity on smooth sections has a unique bounded extension when the order decreases. -/
theorem existsUnique_sobolevInclusion (s t : ℝ) (hst : t ≤ s) :
    ∃! J : A.SobolevSpace s →L[ℂ] A.SobolevSpace t,
      ∀ u : smoothSections (n := n) (r := r) E,
        J (A.smoothToSobolev s u) = A.smoothToSobolev t u := by
  /- In each chart apply the actual Euclidean inclusion in Bessel coordinates, whose
  multiplier is (1+|ξ|²)^((t-s)/2). Its norm is at most one by Plancherel. The finite
  square sum gives the same estimate on smooth sections. Extend to the closures;
  continuity carries their ranges into the target closure. Density gives uniqueness. -/
  classical
  obtain ⟨J, hJnorm, hJdist⟩ := exists_sobolev_inclusion n r s t hst
  -- Use the same Euclidean contraction in every coordinate of the fixed presentation.
  have hcontract (f : MeasureTheory.Lp (EuclideanSpace ℂ (Fin r)) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
      ‖J f‖ ≤ ‖f‖ := by
    calc
      ‖J f‖ ≤ ‖J‖ * ‖f‖ := J.le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hJnorm (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  let T : A.SobolevCoordinates →ₗ[ℂ] A.SobolevCoordinates :=
    { toFun := fun f ↦ WithLp.toLp 2 (fun j ↦ J (f j))
      map_add' := by
        intro f₁ f₂
        apply (WithLp.ext_iff 2).mpr
        funext j
        exact J.map_add (f₁ j) (f₂ j)
      map_smul' := by
        intro c f
        apply (WithLp.ext_iff 2).mpr
        funext j
        exact J.map_smul c (f j) }
  have hT (f : A.SobolevCoordinates) : ‖T f‖ ≤ 1 * ‖f‖ := by
    have hsq : ‖T f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (hcontract (f j)) 2
    nlinarith [norm_nonneg (T f), norm_nonneg f]
  let Tc : A.SobolevCoordinates →L[ℂ] A.SobolevCoordinates := T.mkContinuous 1 hT
  -- Bessel injectivity identifies its action on each actual localized smooth function.
  have hsmooth (u : smoothSections (n := n) (r := r) E) :
      Tc (A.sobolevCoordinates s u) = A.sobolevCoordinates t u := by
    apply (WithLp.ext_iff 2).mpr
    funext j
    apply besselRealization_injective n r t
    change besselRealization n r t (J (schwartzSobolevCoordinate s (A.localize j u))) =
      besselRealization n r t (schwartzSobolevCoordinate t (A.localize j u))
    rw [hJdist, besselRealization_schwartzSobolevCoordinate,
      besselRealization_schwartzSobolevCoordinate]
  -- Continuity carries the smooth range closure into the target smooth range closure.
  have hmaps : ∀ x ∈ (A.sobolevCoordinates s).range.topologicalClosure,
      Tc x ∈ (A.sobolevCoordinates t).range.topologicalClosure := by
    change (A.sobolevCoordinates s).range.topologicalClosure ≤
      ((A.sobolevCoordinates t).range.topologicalClosure).comap Tc.toLinearMap
    apply (A.sobolevCoordinates s).range.topologicalClosure_minimal
    · rintro x ⟨u, rfl⟩
      change Tc (A.sobolevCoordinates s u) ∈
        (A.sobolevCoordinates t).range.topologicalClosure
      rw [hsmooth]
      exact (A.sobolevCoordinates t).range.le_topologicalClosure ⟨u, rfl⟩
    · exact (A.sobolevCoordinates t).range.isClosed_topologicalClosure.preimage Tc.continuous
  let S : A.SobolevSpace s →L[ℂ] A.SobolevSpace t := Tc.restrict hmaps
  have hS (u : smoothSections (n := n) (r := r) E) :
      S (A.smoothToSobolev s u) = A.smoothToSobolev t u := by
    apply Subtype.ext
    exact hsmooth u
  refine ⟨S, hS, ?_⟩
  -- The original smooth image is dense, so the extension is unique.
  intro R hR
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer R.continuous S.continuous
  funext u
  exact (hR u).trans (hS u).symm

/-- The natural inclusion, not the identity on the weighted L² coordinate tuples. -/
def sobolevInclusion (s t : ℝ) (hst : t ≤ s) :
    A.SobolevSpace s →L[ℂ] A.SobolevSpace t :=
  Classical.choose (A.existsUnique_sobolevInclusion s t hst).exists

/-- The inclusion at two orders represents the same smooth section. -/
theorem sobolevInclusion_smoothToSobolev (s t : ℝ) (hst : t ≤ s)
    (u : smoothSections (n := n) (r := r) E) :
    A.sobolevInclusion s t hst (A.smoothToSobolev s u) = A.smoothToSobolev t u := by
  /- This is the specification of the chosen bounded extension. The equality is in
  the concrete target completion and does not identify the two Bessel coordinate tuples. -/
  exact (Classical.choose_spec (A.existsUnique_sobolevInclusion s t hst).exists) u

/-- For one fixed presentation the natural inclusion has operator norm at most one. -/
theorem norm_sobolevInclusion_le (s t : ℝ) (hst : t ≤ s) :
    ‖A.sobolevInclusion s t hst‖ ≤ 1 := by
  /- The pointwise frequency multiplier has absolute value at most one. Apply the
  local L² contraction to each coordinate and sum their squared norms. Pass this
  estimate from the dense smooth image to the closure, then use the operator norm bound. -/
  obtain ⟨J, hJnorm, hJdist⟩ := exists_sobolev_inclusion n r s t hst
  -- Verify the contraction on the same dense smooth image as the selected map.
  have hsmooth (u : smoothSections (n := n) (r := r) E) :
      ‖A.smoothToSobolev t u‖ ≤ ‖A.smoothToSobolev s u‖ := by
    have hcoord (j : Fin A.size) :
        J (schwartzSobolevCoordinate s (A.localize j u)) =
          schwartzSobolevCoordinate t (A.localize j u) := by
      apply besselRealization_injective n r t
      rw [hJdist, besselRealization_schwartzSobolevCoordinate,
        besselRealization_schwartzSobolevCoordinate]
    have hsq : ‖A.smoothToSobolev t u‖ ^ 2 ≤ ‖A.smoothToSobolev s u‖ ^ 2 := by
      rw [A.norm_smoothToSobolev_sq, A.norm_smoothToSobolev_sq]
      apply Finset.sum_le_sum
      intro j _
      rw [← hcoord]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖J (schwartzSobolevCoordinate s (A.localize j u))‖ ≤
            ‖J‖ * ‖schwartzSobolevCoordinate s (A.localize j u)‖ := J.le_opNorm _
        _ ≤ 1 * ‖schwartzSobolevCoordinate s (A.localize j u)‖ :=
          mul_le_mul_of_nonneg_right hJnorm (norm_nonneg _)
        _ = ‖schwartzSobolevCoordinate s (A.localize j u)‖ := one_mul _
    nlinarith [norm_nonneg (A.smoothToSobolev t u), norm_nonneg (A.smoothToSobolev s u)]
  -- A closed inequality extends that contraction to the entire concrete completion.
  apply (A.sobolevInclusion s t hst).opNorm_le_bound (by norm_num)
  intro u
  refine (A.denseRange_smoothToSobolev s).induction_on u
    (isClosed_le (A.sobolevInclusion s t hst).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro v
  rw [A.sobolevInclusion_smoothToSobolev, one_mul]
  exact hsmooth v

/-- The inclusion preserves the actual localized distributions. -/
theorem localDistribution_sobolevInclusion (s t : ℝ) (hst : t ≤ s)
    (j : Fin A.size) (u : A.SobolevSpace s) :
    A.localDistribution t j (A.sobolevInclusion s t hst u) = A.localDistribution s j u := by
  /- For smooth inputs both sides are the distribution of the same localized function.
  Coordinate projection and Bessel realization are continuous. Approximate an arbitrary
  vector by smooth inputs and pass their equality to the limit in tempered distributions. -/
  -- Projection and inverse Bessel realization remain continuous at both real orders.
  have hcont (a : ℝ) : Continuous (A.localDistribution a j) :=
    (besselRealization n r a).continuous.comp
      ((PiLp.proj (𝕜 := ℂ) 2 _ j).continuous.comp continuous_subtype_val)
  refine (A.denseRange_smoothToSobolev s).induction_on u
    (isClosed_eq ((hcont t).comp (A.sobolevInclusion s t hst).continuous) (hcont s)) ?_
  intro v
  rw [A.sobolevInclusion_smoothToSobolev, A.localDistribution_smoothToSobolev,
    A.localDistribution_smoothToSobolev]

/-- The bounded order-decreasing map is injective, including at negative orders. -/
theorem sobolevInclusion_injective (s t : ℝ) (hst : t ≤ s) :
    Function.Injective (A.sobolevInclusion s t hst) := by
  /- Equality of the images implies equality of their localized distributions. The
  preceding compatibility transfers this equality to order s. Injectivity of every
  Bessel realization gives equality of each Hilbert coordinate and hence of the vectors. -/
  intro u v huv
  apply Subtype.ext
  apply (WithLp.ext_iff 2).mpr
  funext j
  -- Recover each source coordinate from the same distribution represented in the target.
  apply besselRealization_injective n r s
  change A.localDistribution s j u = A.localDistribution s j v
  rw [← A.localDistribution_sobolevInclusion s t hst j u,
    ← A.localDistribution_sobolevInclusion s t hst j v, huv]

/-- Global Rellich theorem: a strict drop in Sobolev order gives a compact inclusion. -/
theorem isCompactOperator_sobolevInclusion (s t : ℝ) (hst : t < s) :
    IsCompactOperator (A.sobolevInclusion s t hst.le) := by
  /- Stage 1: every j-localized distribution in the unit ball is supported in the
  fixed compact image of tsupport χ_j, including after completion. Its local norm
  is at most one. Apply the real-order Euclidean Rellich theorem at that compact set.
  Stage 2: the finite product of the resulting compact closures is compact. The actual
  inclusion agrees coordinatewise with those local inclusions, by its distribution
  identity and injectivity of the target Bessel realizations.
  Stage 3: the target Sobolev space is a closed subspace of that finite Hilbert sum.
  Thus the image of the unit ball has compact closure also in the target space. -/
  classical
  obtain ⟨J, _, hJ⟩ := exists_sobolev_inclusion n r s t hst.le
  let K (j : Fin A.size) := (A.chart j) '' tsupport (A.cutoff j)
  have hK (j : Fin A.size) : IsCompact (K j) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  let C (j : Fin A.size) := closure (J '' {f | ‖f‖ ≤ 1 ∧
    IsSupportedIn (besselRealization n r s f) (K j)})
  have hC (j : Fin A.size) : IsCompact (C j) :=
    rellich_compact_inclusion n r s t hst (K j) (hK j) J hJ
  -- The finite coordinate product is compact in the exact original L2 sum topology.
  let e := PiLp.homeomorph 2 (fun _ : Fin A.size ↦ MeasureTheory.Lp
    (EuclideanSpace ℂ (Fin r)) 2
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
  have hprod : IsCompact (e ⁻¹' Set.pi Set.univ C) :=
    e.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi hC)
  have htarget : IsClosed ((A.sobolevCoordinates t).range.topologicalClosure :
      Set A.SobolevCoordinates) := (A.sobolevCoordinates t).range.isClosed_topologicalClosure
  have hcompact : IsCompact ((Subtype.val : A.SobolevSpace t → A.SobolevCoordinates) ⁻¹'
      (e ⁻¹' Set.pi Set.univ C)) :=
    htarget.isClosedEmbedding_subtypeVal.isCompact_preimage hprod
  -- Bessel injectivity compares the given global inclusion with these same local maps.
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (A.sobolevInclusion s t hst.le).toLinearMap zero_lt_one).mpr
  refine ⟨_, hcompact, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  change ∀ j ∈ (Set.univ : Set (Fin A.size)),
    ((A.sobolevInclusion s t hst.le u).val j) ∈ C j
  intro j _
  have hcoord : (A.sobolevInclusion s t hst.le u).val j = J (u.val j) := by
    apply besselRealization_injective n r t
    change A.localDistribution t j (A.sobolevInclusion s t hst.le u) = _
    rw [A.localDistribution_sobolevInclusion, hJ]
    rfl
  rw [hcoord]
  apply subset_closure
  refine ⟨u.val j, ⟨?_, A.isSupportedIn_localDistribution s j u⟩, rfl⟩
  exact (PiLp.norm_apply_le u.val j).trans (by simpa using hu)

end SmoothBundlePresentation

variable {F : M → Type*}
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- SG III.2.13/2.15(4): an order-at-most-m differential operator loses at most m derivatives. -/
theorem exists_sobolev_bound (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      ‖B.smoothToSobolev (s - m) (P.toLinearMap u)‖ ≤ C * ‖A.smoothToSobolev s u‖ := by
  /- Refine the output partition to P's actual finite differential expressions.
  Adjoin an input partition weight equal to one near each output support; this retains
  the complete coordinate germ. Quantization of the compactly localized polynomial
  symbol is exactly the output localization. Its real-order Sobolev bound, the finite
  square-sum norm, and the presentation comparisons give the required estimate.
  All added presentations use the original fibers and topology, without a fiber norm,
  ellipticity assumption, or equality of the input and output ranks. -/
  classical
  -- The finite compact partition already forces compactness of the original base.
  have hcompact : IsCompact (Set.univ : Set M) := by
    have hcover : (Set.univ : Set M) = ⋃ j, tsupport (A.cutoff j) := by
      apply Set.Subset.antisymm
      · intro x _
        by_contra hx
        have hzero (j : Fin A.size) : A.cutoff j x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hj ↦ hx (Set.mem_iUnion.mpr ⟨j, hj⟩))
        have hsum := A.sum_cutoff x
        simp only [hzero, Finset.sum_const_zero] at hsum
        exact zero_ne_one hsum
      · exact Set.subset_univ _
    rw [hcover]
    exact isCompact_iUnion A.compact_support
  let : CompactSpace M := ⟨hcompact⟩
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have hexpr (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ Q : CoordinateDifferentialOperator n r q m (c x '' U),
        HasCoordinateExpression E F m P.toLinearMap (c x) (e x) (f x) U Q :=
    P.isDifferentialOperator (c x) (chart_mem_atlas _ x) (e x) (f x) x
      ⟨⟨mem_chart_source _ x, mem_baseSet_trivializationAt _ _ x⟩,
        mem_baseSet_trivializationAt _ _ x⟩
  choose U hU hxU Q hQ using hexpr
  have hcover : Set.univ ⊆ ⋃ x, U x := fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let index : Fin σ.card ≃ σ := σ.equivFin.symm
  let V (j : Fin σ.card) := U (index j)
  have hfinitecover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hσ hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V
    (fun j ↦ hU (index j)) hfinitecover
  let L : SmoothBundlePresentation (n := n) (r := q) F :=
    { size := σ.card
      chart := fun j ↦ c (index j)
      chart_mem_atlas := fun j ↦ chart_mem_atlas _ (index j : M)
      frame := fun j ↦ f (index j)
      frame_mem_atlas := fun _ ↦ inferInstance
      cutoff := fun j ↦ ρ j
      smooth_cutoff := fun j ↦ (ρ j).contMDiff
      cutoff_nonneg := ρ.nonneg
      compact_support := fun _ ↦ HasCompactSupport.of_compactSpace _
      support_subset := fun j x hx ↦
        ⟨((hQ (index j)).1 (hρ j hx)).1.1, ((hQ (index j)).1 (hρ j hx)).2⟩
      sum_cutoff := fun x ↦ by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x) }
  -- In each input presentation adjoin a weight equal to one near the output support.
  have hplateau (j : Fin σ.card) :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed
      (n := (⊤ : ℕ∞)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (hU (index j)).isClosed_compl
      (isClosed_tsupport (ρ j)) (Set.disjoint_compl_left_iff_subset.mpr (hρ j))
  choose β hβzero hβone hβrange using hplateau
  have hβsupport (j : Fin σ.card) : tsupport (β j : M → ℝ) ⊆ U (index j) := by
    intro x hx
    by_contra hout
    have hzero : (β j : M → ℝ) =ᶠ[nhds x] 0 :=
      Filter.Eventually.filter_mono (nhds_le_nhdsSet hout) (hβzero j)
    have hnot : x ∉ closure (Function.support (β j : M → ℝ)) := by
      rw [mem_closure_iff_frequently]
      exact fun hfreq ↦ (hfreq.and_eventually hzero).exists.elim
        (fun y hy ↦ hy.1 hy.2)
    exact hnot hx
  let C (j : Fin σ.card) : SmoothBundlePresentation (n := n) (r := r) E :=
    { size := A.size + 1
      chart := Fin.cases (c (index j)) A.chart
      chart_mem_atlas := Fin.cases (chart_mem_atlas _ (index j : M)) A.chart_mem_atlas
      frame := Fin.cases (e (index j)) A.frame
      frame_mem_atlas := Fin.cases
        (show MemTrivializationAtlas (e (index j)) from inferInstance) A.frame_mem_atlas
      cutoff := Fin.cases (fun x ↦ β j x) (fun i x ↦ (1 - β j x) * A.cutoff i x)
      smooth_cutoff := Fin.cases (β j).contMDiff
        (fun i ↦ (show ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (1 - p.1) * p.2) from
          (contDiff_const.sub contDiff_fst).mul contDiff_snd).comp_contMDiff
            ((β j).contMDiff.prodMk_space (A.smooth_cutoff i)))
      cutoff_nonneg := Fin.cases (fun x ↦ (hβrange j x).1)
        (fun i x ↦ mul_nonneg (sub_nonneg.mpr (hβrange j x).2) (A.cutoff_nonneg i x))
      compact_support := fun _ ↦ HasCompactSupport.of_compactSpace _
      support_subset := Fin.cases
        (fun x hx ↦ ((hQ (index j)).1 (hβsupport j hx)).1)
        (fun i ↦ tsupport_mul_subset_right.trans (A.support_subset i))
      sum_cutoff := by
        intro x
        simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
        rw [← Finset.mul_sum, A.sum_cutoff]
        ring }
  let χ (j : Fin σ.card) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if z ∈ (c (index j)).target then ρ j ((c (index j)).symm z) else 0
  let K (j : Fin σ.card) := (c (index j)) '' tsupport (ρ j)
  have hK (j : Fin σ.card) : IsCompact (K j) :=
    (HasCompactSupport.of_compactSpace (ρ j)).image_of_continuousOn
      ((c (index j)).continuousOn.mono (fun x hx ↦ ((hQ (index j)).1 (hρ j hx)).1.1))
  have hχ (j : Fin σ.card) : tsupport (χ j) ⊆ K j := by
    apply closure_minimal ?_ (hK j).isClosed
    intro z hz
    have ht : z ∈ (c (index j)).target := by
      by_contra ht
      exact hz (by simp [χ, ht])
    have hr : (c (index j)).symm z ∈ tsupport (ρ j) := by
      by_contra hr
      exact hz (by simp [χ, ht, image_eq_zero_of_notMem_tsupport hr])
    exact ⟨(c (index j)).symm z, hr, (c (index j)).right_inv ht⟩
  have hχcompact (j : Fin σ.card) : HasCompactSupport (χ j) :=
    (hK j).of_isClosed_subset (isClosed_tsupport _) (hχ j)
  have hχsmooth (j : Fin σ.card) : ContDiff ℝ ∞ (χ j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ K j
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := ((hQ (index j)).1 (hρ j hx)).1.1
      have ht := (c (index j)).map_source hxsource
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (chart_mem_atlas _ (index j : M))) ht
      have hlocal := ((ρ j).contMDiff.contMDiffAt.comp _ hchart).contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(c (index j)).open_target.mem_nhds ht] with y hy
      simp only [χ, ite_eq_left hy]
      rfl
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hK j).isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχ j h))
  let D (j : Fin σ.card) := c (index j) '' U (index j)
  have hD (j : Fin σ.card) : IsOpen (D j) :=
    (c (index j)).isOpen_image_of_subset_source (hU (index j))
      (fun x hx ↦ ((hQ (index j)).1 hx).1.1)
  have hχD (j : Fin σ.card) : tsupport (χ j) ⊆ D j :=
    (hχ j).trans (Set.image_mono (hρ j))
  let a (j : Fin σ.card) := zeroExtendedSymbol (D j) (χ j) (Q (index j)).totalSymbol
  have ha (j : Fin σ.card) : IsSymbol Set.univ (m : ℝ) (a j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) m (χ j) (hχsmooth j)
      (hχcompact j) (hχD j) _ ((Q (index j)).isSymbol_totalSymbol (hD j))
  have hac (j : Fin σ.card) : HasCompactSupport (a j) :=
    hasCompactSupport_zeroExtendedSymbol (D j) (χ j) _ (hχcompact j)
  -- Polynomial quantization differentiates only where the input weight is identically one.
  have hquant (j : Fin σ.card) (u : smoothSections (n := n) (r := r) E)
      (z : EuclideanSpace ℝ (Fin n)) :
      quantize (a j) ((C j).localize 0 u) z = L.localize j (P.toLinearMap u) z := by
    by_cases hz : z ∈ tsupport (χ j)
    · obtain ⟨x, hx, rfl⟩ := hχD j hz
      have hu := (hQ (index j)).1 hx
      have ht := (c (index j)).map_source hu.1.1
      have hρx : x ∈ tsupport (ρ j) := by
        obtain ⟨y, hy, hyx⟩ := hχ j hz
        have hyc := ((hQ (index j)).1 (hρ j hy)).1.1
        have hxy := (c (index j)).injOn hyc hu.1.1 hyx
        exact hxy ▸ hy
      have hβnear : ∀ᶠ y in nhds x, β j y = 1 :=
        Filter.Eventually.filter_mono (nhds_le_nhdsSet hρx) (hβone j)
      have hnear : ((C j).localize 0 u :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)) =ᶠ[nhds (c (index j) x)]
            sectionInChart E (c (index j)) (e (index j)) u.val := by
        filter_upwards [(c (index j)).tendsto_symm hu.1.1 |>.eventually hβnear,
          (c (index j)).open_target.mem_nhds ht] with y hy hyt
        change (C j).localizedFunction 0 u y = _
        simp only [SmoothBundlePresentation.localizedFunction, C, Fin.cases_zero,
          ite_eq_left hyt, hy, Complex.ofReal_one, one_smul]
      have hpoly : (Q (index j)).apply ((C j).localize 0 u) (c (index j) x) =
          (Q (index j)).apply
            (sectionInChart E (c (index j)) (e (index j)) u.val) (c (index j) x) := by
        simp only [CoordinateDifferentialOperator.apply]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro α _
        rw [(hnear.iteratedFDeriv ℝ k.val).eq_of_nhds]
      have haeq (ξ : EuclideanSpace ℝ (Fin n)) :
          a j (c (index j) x) ξ =
            (χ j (c (index j) x) : ℂ) • (Q (index j)).totalSymbol (c (index j) x) ξ := by
        simp only [a, zeroExtendedSymbol, ite_eq_left (show c (index j) x ∈ D j from
          ⟨x, hx, rfl⟩)]
      calc
        quantize (a j) ((C j).localize 0 u) (c (index j) x) =
            (χ j (c (index j) x) : ℂ) •
              quantize (Q (index j)).totalSymbol ((C j).localize 0 u) (c (index j) x) := by
          simp only [quantize, haeq, smul_apply]
          simp_rw [smul_comm _ (χ j (c (index j) x) : ℂ)]
          rw [MeasureTheory.integral_smul]
          exact smul_comm _ _ _
        _ = (ρ j x : ℂ) • (f (index j) ⟨x, (P.toLinearMap u).val x⟩).2 := by
          rw [(Q (index j)).quantize_totalSymbol, hpoly, ← (hQ (index j)).2 u x hx]
          simp only [χ, ite_eq_left ht, (c (index j)).left_inv hu.1.1]
        _ = L.localize j (P.toLinearMap u) (c (index j) x) := by
          change _ = L.localizedFunction j (P.toLinearMap u) (c (index j) x)
          simp only [SmoothBundlePresentation.localizedFunction, L, ite_eq_left ht,
            sectionInChart, (c (index j)).left_inv hu.1.1]
          rw [(c (index j)).left_inv hu.1.1]
    · have hzero := image_eq_zero_of_notMem_tsupport hz
      have ha0 : ∀ ξ, a j z ξ = 0 := by
        intro ξ
        simp [a, zeroExtendedSymbol, hzero]
      have hleft : quantize (a j) ((C j).localize 0 u) z = 0 := by
        simp [quantize, ha0]
      rw [hleft]
      change 0 = L.localizedFunction j (P.toLinearMap u) z
      by_cases ht : z ∈ (c (index j)).target
      · have hρ0 : ρ j ((c (index j)).symm z) = 0 := by
          simpa only [χ, ite_eq_left ht] using hzero
        simp only [SmoothBundlePresentation.localizedFunction, L, ite_eq_left ht,
          hρ0, Complex.ofReal_zero, zero_smul]
      · simp only [SmoothBundlePresentation.localizedFunction, L, ite_eq_right ht]
  -- The same local quantizations give uniform bounds for the finite output coordinates.
  have hlocal (j : Fin L.size) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖schwartzSobolevCoordinate (s - m) (L.localize j (P.toLinearMap u))‖ ≤
          D * ‖A.smoothToSobolev s u‖ := by
    let T := quantizeSobolev m s (a j) (ha j) (hac j)
    obtain ⟨D, hD, hb⟩ := A.exists_norm_smoothToSobolev_le (C j) s
    refine ⟨‖T‖ * D, mul_nonneg (norm_nonneg _) hD.le, ?_⟩
    intro u
    have hT : T (schwartzSobolevCoordinate s ((C j).localize 0 u)) =
        schwartzSobolevCoordinate (s - m) (L.localize j (P.toLinearMap u)) := by
      apply besselRealization_injective n q (s - m)
      ext1 φ
      rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
        SchwartzMap.coe_apply]
      simp only [hquant]
    rw [← hT]
    calc
      ‖T (schwartzSobolevCoordinate s ((C j).localize 0 u))‖ ≤
          ‖T‖ * ‖schwartzSobolevCoordinate s ((C j).localize 0 u)‖ := T.le_opNorm _
      _ ≤ ‖T‖ * ‖(C j).smoothToSobolev s u‖ :=
        mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ((C j).sobolevCoordinates s u) 0)
          (norm_nonneg _)
      _ ≤ ‖T‖ * (D * ‖A.smoothToSobolev s u‖) :=
        mul_le_mul_of_nonneg_left (hb u) (norm_nonneg _)
      _ = (‖T‖ * D) * ‖A.smoothToSobolev s u‖ := (mul_assoc _ _ _).symm
  choose D hD hb using hlocal
  obtain ⟨H, hH, hB⟩ := L.exists_norm_smoothToSobolev_le B (s - m)
  refine ⟨H * ∑ j, D j, mul_nonneg hH.le (Finset.sum_nonneg (fun j _ ↦ hD j)), ?_⟩
  intro u
  have hsum : ‖L.smoothToSobolev (s - m) (P.toLinearMap u)‖ ≤
      ∑ j, ‖schwartzSobolevCoordinate (s - m) (L.localize j (P.toLinearMap u))‖ := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun (j : Fin L.size) _ ↦ norm_nonneg
        (schwartzSobolevCoordinate (s - m) (L.localize j (P.toLinearMap u))))
    rw [← L.norm_smoothToSobolev_sq] at hsq
    have hnonneg : 0 ≤ ∑ j, ‖schwartzSobolevCoordinate (s - m)
        (L.localize j (P.toLinearMap u))‖ := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
    nlinarith [norm_nonneg (L.smoothToSobolev (s - m) (P.toLinearMap u))]
  calc
    ‖B.smoothToSobolev (s - m) (P.toLinearMap u)‖ ≤
        H * ‖L.smoothToSobolev (s - m) (P.toLinearMap u)‖ := hB _
    _ ≤ H * (∑ j, ‖schwartzSobolevCoordinate (s - m)
        (L.localize j (P.toLinearMap u))‖) := mul_le_mul_of_nonneg_left hsum hH.le
    _ ≤ H * (∑ j, D j * ‖A.smoothToSobolev s u‖) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hb j u)) hH.le
    _ = (H * ∑ j, D j) * ‖A.smoothToSobolev s u‖ := by rw [← Finset.sum_mul, mul_assoc]

/-- The actual smooth-section operator has a unique bounded Sobolev extension. -/
theorem existsUnique_sobolevExtension (s : ℝ) :
    ∃! T : A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m),
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) = B.smoothToSobolev (s - m) (P.toLinearMap u) := by
  /- The Sobolev estimate makes the displayed map on the smooth image bounded, and
  injectivity of the source embedding makes it well-defined. The target is complete,
  so it extends continuously and linearly to the closure. The smooth image is dense;
  hence any two bounded extensions satisfying this formula are equal. -/
  obtain ⟨C, _, hC⟩ := P.exists_sobolev_bound A B s
  let L := (B.smoothToSobolev (s - m)).comp P.toLinearMap
  let T : A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m) :=
    L.extendOfNorm (A.smoothToSobolev s)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s u) = B.smoothToSobolev (s - m) (P.toLinearMap u) :=
    LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s) ⟨C, hC⟩ u
  refine ⟨T, hT, ?_⟩
  intro R hR
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer R.continuous T.continuous
  funext u
  exact (hR u).trans (hT u).symm

/-- The Sobolev realization of P selected by its unique dense-subspace specification. -/
def sobolevExtension (s : ℝ) : A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m) :=
  Classical.choose (P.existsUnique_sobolevExtension A B s).exists

/-- The bounded realization agrees with the original global differential operator. -/
theorem sobolevExtension_smoothToSobolev (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    P.sobolevExtension A B s (A.smoothToSobolev s u) =
      B.smoothToSobolev (s - m) (P.toLinearMap u) := by
  /- Unpack the chosen witness in existsUnique_sobolevExtension. Its defining equality
  specifies the action on each actual smooth section, so this realization is tied to P. -/
  exact (Classical.choose_spec (P.existsUnique_sobolevExtension A B s).exists) u

end DifferentialOperator

end AtiyahSinger

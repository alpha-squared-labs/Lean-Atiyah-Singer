/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.RepresentationTheory.Continuous.Basic

import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Finite-dimensional approximation of compact unitary representations

Public module ID: M0008.

For a continuous unitary representation of a compact Hausdorff group on a
complex Hilbert space, finite-dimensional invariant subspaces have dense span.
The proof averages the rank-one operators associated to a single orbit and
uses the spectral theorem for compact self-adjoint operators. Positivity of
Haar measure on nonempty open sets detects a nonzero vector at the identity.

This is the Hilbert-space finite-vector input needed for an equivariant
finite-representation embedding. Continuity in the group variable is an
explicit assumption, since `ContRepresentation` only bundles continuous
linear maps on the representation space. No Lie or countability assumption
on the compact group is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory InnerProductSpace

open scoped ComplexConjugate

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The finite-dimensional invariant subspaces of a continuous compact-group
unitary representation have dense linear span. -/
theorem topologicalClosure_sSup_finiteDimensional_invariant_eq_top
    (ρ : ContRepresentation ℂ G H)
    (hρ : Continuous (fun p : G × H ↦ ρ p.1 p.2))
    (hunitary : ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    (sSup {W : Submodule ℂ H | FiniteDimensional ℂ W ∧
      ∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W}).topologicalClosure = ⊤ := by
  classical
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := Measure.haar
  let μ : Measure G := (ν Set.univ)⁻¹ • ν
  let K : Submodule ℂ H := sSup {W : Submodule ℂ H | FiniteDimensional ℂ W ∧
    ∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W}
  -- It suffices to show that a vector perpendicular to all finite invariant
  -- subspaces is zero. The averaged orbit operator will detect any exception.
  suffices hK : Kᗮ = ⊥ by
    rw [← K.orthogonal_orthogonal_eq_closure, hK, Submodule.bot_orthogonal_eq_top]
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  by_contra hv0
  have hcont : Continuous (fun g : G ↦ ρ g v) :=
    hρ.comp (continuous_id.prodMk continuous_const)
  let R : G → H →L[ℂ] H := fun g ↦ rankOne ℂ (ρ g v) (ρ g v)
  have hR : Continuous R := by
    change Continuous (fun g : G ↦ rankOne ℂ (ρ g v) (ρ g v))
    simpa only [rankOne_def, Function.comp_apply,
      ContinuousLinearMap.smulRightL_apply_apply] using
      ((ContinuousLinearMap.smulRightL ℂ H H).continuous.comp
        ((innerSL ℂ).continuous.comp hcont)).clm_apply hcont
  have hRI : Integrable R μ :=
    hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint (x : H) : Integrable (fun g : G ↦ R g x) μ :=
    (hR.clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let T : H →L[ℂ] H := ∫ g, R g ∂μ
  have happly (x : H) : T x = ∫ g, R g x ∂μ :=
    ContinuousLinearMap.integral_apply hRI x
  -- The integral stays in the closed submodule of compact operators. Each
  -- integrand factors through the one-dimensional scalar space.
  have hcompact : IsCompactOperator T := by
    let C := compactOperator (RingHom.id ℂ) H H
    have hconvex : Convex ℝ (C : Set (H →L[ℂ] H)) :=
      (C.restrictScalars ℝ).convex
    apply hconvex.integral_mem isClosed_setOfPred_isCompactOperator _ hRI
    filter_upwards [] with g
    change IsCompactOperator (rankOne ℂ (ρ g v) (ρ g v))
    rw [rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ (ρ g v))).comp_clm (innerSL ℂ (ρ g v))
  have hsymm : T.IsSymmetric := by
    intro x y
    change inner ℂ (T x) y = inner ℂ x (T y)
    rw [happly, happly]
    calc
      _ = ∫ g, inner ℂ (R g x) y ∂μ :=
        ((innerSLFlip ℂ y).integral_comp_commSL (by simp) (hint x)).symm
      _ = ∫ g, inner ℂ x (R g y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        exact isSymmetric_rankOne_self (ρ g v) x y
      _ = _ := (innerSL ℂ x).integral_comp_comm (hint y)
  -- Left translation of Haar measure and unitarity give equivariance of the
  -- same operator. Thus each of its eigenspaces is an invariant subspace.
  have hcomm (g : G) (x : H) : T (ρ g x) = ρ g (T x) := by
    rw [happly, happly, ← (ρ g).integral_comp_comm (hint x)]
    calc
      _ = ∫ h, R (g * h) (ρ g x) ∂μ :=
        (integral_mul_left_eq_self (μ := μ) (fun h ↦ R h (ρ g x)) g).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with h
        simp only [R, rankOne_apply, map_mul, mul_apply_eq_comp]
        rw [hunitary, map_smul]
  have horth (W : Submodule ℂ H) (hW : FiniteDimensional ℂ W)
      (hinv : ∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W)
      (x : H) (hx : x ∈ W) (g : G) : inner ℂ (ρ g v) x = 0 := by
    have hmem : W ∈ {W : Submodule ℂ H | FiniteDimensional ℂ W ∧
        ∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W} := ⟨hW, hinv⟩
    have hx' : ρ g⁻¹ x ∈ K := (le_sSup hmem) (hinv g⁻¹ x hx)
    have hi : inner ℂ v (ρ g⁻¹ x) = 0 := K.inner_left_of_mem_orthogonal hx' hv
    have hi' := hunitary g v (ρ g⁻¹ x)
    simpa only [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self] using hi'.trans hi
  -- A nonzero eigenspace would be finite-dimensional by compactness. Its
  -- vectors are killed by every orbit rank-one operator by orthogonality,
  -- contradicting their nonzero eigenvalue. The spectral theorem gives T=0.
  have hzero : T = 0 := by
    apply (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hcompact hsymm).mp
    intro z hz
    by_contra hz0
    let W : Submodule ℂ H := Module.End.eigenspace T.toLinearMap z
    have hW : FiniteDimensional ℂ W :=
      ContinuousLinearMap.finite_dimensional_eigenspace hcompact z hz0
    have hinv (g : G) (x : H) (hx : x ∈ W) : ρ g x ∈ W := by
      change x ∈ Module.End.eigenspace T.toLinearMap z at hx
      change ρ g x ∈ Module.End.eigenspace T.toLinearMap z
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change T x = z • x at hx
      change T (ρ g x) = z • ρ g x
      rw [hcomm, hx, map_smul]
    obtain ⟨x, hx, hx0⟩ := hz.exists_hasEigenvector
    have hTx : T x = 0 := by
      rw [happly]
      have hpoint (g : G) : R g x = 0 := by
        simp only [R, rankOne_apply, horth W hW hinv x hx g, zero_smul]
      simp only [hpoint, integral_zero]
    have heigen : T x = z • x := Module.End.mem_eigenspace_iff.mp hx
    exact hx0 ((smul_eq_zero.mp (heigen.symm.trans hTx)).resolve_left hz0)
  -- The quadratic form at v is the integral of a continuous nonnegative
  -- squared matrix coefficient, strictly positive at the identity. Haar
  -- measure has full support on G, so this contradicts T=0 for nonzero v.
  let f : G → ℝ := fun g ↦ Complex.normSq (inner ℂ (ρ g v) v)
  have hf : Continuous f := Complex.continuous_normSq.comp (hcont.inner continuous_const)
  have hfI : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfpos : 0 < ∫ g, f g ∂μ := by
    apply integral_pos_of_integrable_nonneg_nonzero hf hfI
      (fun g ↦ Complex.normSq_nonneg _) (x := (1 : G))
    simpa [f, Complex.normSq_eq_zero, inner_self_eq_zero] using hv0
  have hq : (∫ g, f g ∂μ) = (inner ℂ v (T v)).re := by
    rw [happly]
    change (∫ g, f g ∂μ) = RCLike.re ((innerSL ℂ v) (∫ g, R g v ∂μ))
    rw [← (innerSL ℂ v).integral_comp_comm (hint v),
      ← integral_re ((innerSL ℂ v).integrable_comp (hint v))]
    apply integral_congr_ae
    filter_upwards [] with g
    simp only [f, R, rankOne_apply, innerSL_apply_apply, inner_smul_right]
    rw [← inner_conj_symm v (ρ g v), Complex.mul_conj]
    rfl
  rw [hq, hzero] at hfpos
  simp at hfpos

/-- A compact set in a continuous unitary representation can be approximated
uniformly by one finite-dimensional invariant subspace. -/
theorem exists_finiteDimensional_invariant_approximation
    (ρ : ContRepresentation ℂ G H)
    (hρ : Continuous (fun p : G × H ↦ ρ p.1 p.2))
    (hunitary : ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (C : Set H) (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧
      (∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W) ∧
      ∀ x ∈ C, ∃ y ∈ W, dist x y < ε := by
  classical
  let S : Set (Submodule ℂ H) := {W | FiniteDimensional ℂ W ∧
    ∀ (g : G) (x : H), x ∈ W → ρ g x ∈ W}
  have hSne : S.Nonempty := ⟨⊥, inferInstance, by simp⟩
  have hdir : DirectedOn (· ≤ ·) S := by
    intro U hU V hV
    let : FiniteDimensional ℂ U := hU.1
    let : FiniteDimensional ℂ V := hV.1
    refine ⟨U ⊔ V, ⟨inferInstance, ?_⟩, le_sup_left, le_sup_right⟩
    intro g x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact (U ⊔ V).add_mem ((show U ≤ U ⊔ V from le_sup_left) (hU.2 g u hu))
      ((show V ≤ U ⊔ V from le_sup_right) (hV.2 g v hv))
  -- Density supplies a finite invariant approximant to every net point. A
  -- vector in the algebraic supremum already lies in one such subspace,
  -- since finite-dimensional invariant subspaces are directed under sums.
  have hpoint (x : H) : ∃ W ∈ S, ∃ y ∈ W, dist x y < ε / 2 := by
    have hx : x ∈ closure ((sSup S : Submodule ℂ H) : Set H) := by
      rw [← Submodule.topologicalClosure_coe,
        topologicalClosure_sSup_finiteDimensional_invariant_eq_top ρ hρ hunitary]
      trivial
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
    obtain ⟨W, hW, hyW⟩ := (Submodule.mem_sSup_of_directed hSne hdir).mp hy
    exact ⟨W, hW, y, hyW, hxy⟩
  choose V hV y hy hxy using hpoint
  let : ∀ x : H, FiniteDimensional ℂ (V x) := fun x ↦ (hV x).1
  obtain ⟨t, _, ht, hcover⟩ := hC.finite_cover_balls (half_pos hε)
  let W : Submodule ℂ H := ht.toFinset.sup V
  have hVW (x : H) (hx : x ∈ t) : V x ≤ W :=
    Finset.le_sup (ht.mem_toFinset.mpr hx)
  refine ⟨W, inferInstance, ?_, ?_⟩
  · -- The same finite sum remains invariant under every group element.
    intro g
    change W ≤ W.comap (ρ g).toLinearMap
    apply Finset.sup_le
    intro x hx u hu
    exact hVW x (ht.mem_toFinset.mp hx) ((hV x).2 g u hu)
  · -- The compact finite net makes the approximation uniform on all of C.
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hcover hx)
    refine ⟨y z, hVW z hz (hy z), ?_⟩
    calc
      dist x (y z) ≤ dist x z + dist z (y z) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hxz (hxy z)
      _ = ε := add_halves ε

end AtiyahSinger

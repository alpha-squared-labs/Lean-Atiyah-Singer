/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Fredholm.Open
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Path

/-!
# Fredholm statements for the analytic index

Public module ID: M0643.

The definition and algebraic index are mathlib's. The Hilbert characterization
identifies the quotient cokernel with the adjoint kernel and yields the usual
index formula. Atkinson's criterion gives compact-perturbation invariance,
and the index is constant along operator-norm-continuous Fredholm paths.
The fixed-complement theorem retains the prescribed subspaces throughout a
norm neighborhood. Finite-dimensional normalization gives the rank difference.
Every use of the index has a Fredholm or finite-dimensional hypothesis.
The adjoint here is the bounded Hilbert adjoint; geometric formal adjoints
are treated separately.

References: Spin Geometry III.5 and III.7; Fredholm operator and Atkinson's
theorem in Wikipedia.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ContinuousLinearMap Topology Filter

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [InnerProductSpace ℂ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- the Hilbert-space definition agrees with mathlib's topological definition. -/
theorem isFredholm_iff_closed_range_finite (T : E →L[ℂ] F) :
    T.IsFredholm ↔ IsClosed (T.range : Set F) ∧
      FiniteDimensional ℂ T.ker ∧ FiniteDimensional ℂ (F ⧸ T.range) := by
  -- Use the defining conditions forwards and open mapping for the closed-range quotient backwards.
  constructor
  · intro hT
    exact ⟨hT.isClosed_range, hT.finite_ker, hT.finite_coker⟩
  · rintro ⟨hclosed, hker, hcoker⟩
    have : CompleteSpace T.range := hclosed.completeSpace_coe
    exact {
      isStrictMap := by
        rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
        apply T.rangeRestrict.isQuotientMap
        rintro ⟨_, x, rfl⟩
        exact ⟨x, rfl⟩
      isClosed_range := hclosed
      finite_ker := hker
      finite_coker := hcoker
      closedComplemented_ker := .of_finiteDimensional T.ker }

/-- for closed range, the cokernel is the kernel of the Hilbert adjoint. -/
theorem nonempty_coker_equiv_ker_adjoint (T : E →L[ℂ] F)
    (hT : IsClosed (T.range : Set F)) :
    Nonempty ((F ⧸ T.range) ≃ₗ[ℂ] T.adjoint.ker) := by
  -- Identify the closed-range quotient with its orthogonal complement and the adjoint kernel.
  have : CompleteSpace T.range := hT.completeSpace_coe
  exact ⟨T.range.quotientEquivOrthogonal.toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ T.orthogonal_range)⟩

/-- the usual kernel-minus-adjoint-kernel formula, with finiteness certified. -/
theorem index_eq_finrank_ker_sub_finrank_ker_adjoint (T : E →L[ℂ] F)
    (hT : T.IsFredholm) :
    T.index = (Module.finrank ℂ T.ker : ℤ) - Module.finrank ℂ T.adjoint.ker := by
  -- Use dimension invariance under the cokernel equivalence in the original integer index formula.
  obtain ⟨e⟩ := nonempty_coker_equiv_ker_adjoint T hT.isClosed_range
  rw [LinearMap.index_eq_finrank_sub, e.finrank_eq]

/-- taking the Hilbert adjoint preserves Fredholmness. -/
theorem isFredholm_adjoint (T : E →L[ℂ] F) (hT : T.IsFredholm) :
    T.adjoint.IsFredholm := by
  -- Take a quasi-inverse with finite-rank errors; adjoints reverse composition.
  obtain ⟨Q, hQ⟩ := hT.exists_isQuasiInverse
  have hE : FiniteDimensional ℂ (Q.comp T - ContinuousLinearMap.id ℂ E).range := by
    have h := (LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hQ.1).isNoetherian_range
    rw [toLinearMap_sub, toLinearMap_comp, coe_id]
    infer_instance
  have hF : FiniteDimensional ℂ (T.comp Q - ContinuousLinearMap.id ℂ F).range := by
    have h := (LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hQ.2).isNoetherian_range
    rw [toLinearMap_sub, toLinearMap_comp, coe_id]
    infer_instance
  -- Factor each error through its finite-dimensional range to control the adjoint range.
  have hEadj : FiniteDimensional ℂ
      (Q.comp T - ContinuousLinearMap.id ℂ E).adjoint.range := by
    let A : E →L[ℂ] E := Q.comp T - ContinuousLinearMap.id ℂ E
    let B : E →L[ℂ] A.range := A.rangeRestrict
    have hA : A = A.range.subtypeL.comp B := rfl
    change FiniteDimensional ℂ A.adjoint.range
    rw [hA, adjoint_comp]
    exact FiniteDimensional.of_injective
      (Submodule.inclusion (LinearMap.range_comp_le_range _ _))
      (Submodule.inclusion_injective _)
  have hFadj : FiniteDimensional ℂ
      (T.comp Q - ContinuousLinearMap.id ℂ F).adjoint.range := by
    let A : F →L[ℂ] F := T.comp Q - ContinuousLinearMap.id ℂ F
    let B : F →L[ℂ] A.range := A.rangeRestrict
    have hA : A = A.range.subtypeL.comp B := rfl
    change FiniteDimensional ℂ A.adjoint.range
    rw [hA, adjoint_comp]
    exact FiniteDimensional.of_injective
      (Submodule.inclusion (LinearMap.range_comp_le_range _ _))
      (Submodule.inclusion_injective _)
  -- Interchange the errors to obtain the two-sided quasi-inverse Q* for T*.
  rw [map_sub, adjoint_comp, adjoint_id] at hEadj hFadj
  apply IsFredholm.of_isQuasiInverse (v := Q.adjoint)
  constructor
  · apply LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mpr
    have h : FiniteDimensional ℂ
        (Q.adjoint.comp T.adjoint - ContinuousLinearMap.id ℂ F).range := hFadj
    change IsNoetherian ℂ _
    rw [← toLinearMap_comp, ← coe_id, ← toLinearMap_sub]
    infer_instance
  · apply LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mpr
    have h : FiniteDimensional ℂ
        (T.adjoint.comp Q.adjoint - ContinuousLinearMap.id ℂ E).range := hEadj
    change IsNoetherian ℂ _
    rw [← toLinearMap_comp, ← coe_id, ← toLinearMap_sub]
    infer_instance

/-- the adjoint reverses the index. -/
theorem index_adjoint (T : E →L[ℂ] F) (hT : T.IsFredholm) :
    T.adjoint.index = -T.index := by
  -- Apply the kernel-minus-adjoint-kernel formula twice and identify the double adjoint.
  rw [index_eq_finrank_ker_sub_finrank_ker_adjoint T.adjoint (isFredholm_adjoint T hT),
    adjoint_adjoint, index_eq_finrank_ker_sub_finrank_ker_adjoint T hT]
  ring

/-- Atkinson's criterion: Fredholmness is equivalent to a two-sided inverse modulo compacts.
The two Hilbert spaces need not be equal or separable. -/
theorem atkinson (T : E →L[ℂ] F) :
    T.IsFredholm ↔ ∃ Q : F →L[ℂ] E,
      IsCompactOperator (Q.comp T - ContinuousLinearMap.id ℂ E) ∧
      IsCompactOperator (T.comp Q - ContinuousLinearMap.id ℂ F) := by
  constructor
  · intro hT
    -- A Fredholm quasi-inverse has finite-rank errors.
    -- Factoring through their finite-dimensional ranges proves compactness.
    obtain ⟨Q, hQ⟩ := hT.exists_isQuasiInverse
    have hEfin : FiniteDimensional ℂ (Q.comp T - ContinuousLinearMap.id ℂ E).range := by
      have h :=
        (LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hQ.1).isNoetherian_range
      rw [toLinearMap_sub, toLinearMap_comp, coe_id]
      infer_instance
    have hFfin : FiniteDimensional ℂ (T.comp Q - ContinuousLinearMap.id ℂ F).range := by
      have h :=
        (LinearMap.FiniteRangeSetoid.equiv_iff_hasNoetherianRange.mp hQ.2).isNoetherian_range
      rw [toLinearMap_sub, toLinearMap_comp, coe_id]
      infer_instance
    refine ⟨Q, ?_, ?_⟩
    · exact (isCompactOperator_of_locallyCompactSpace_dom
        (Q.comp T - ContinuousLinearMap.id ℂ E).rangeRestrict).clm_comp
        (Q.comp T - ContinuousLinearMap.id ℂ E).range.subtypeL
    · exact (isCompactOperator_of_locallyCompactSpace_dom
        (T.comp Q - ContinuousLinearMap.id ℂ F).rangeRestrict).clm_comp
        (T.comp Q - ContinuousLinearMap.id ℂ F).range.subtypeL
  · rintro ⟨Q, hE, hF⟩
    -- On the kernel, the left compact error is minus the identity.
    have hker : FiniteDimensional ℂ T.ker := by
      apply FiniteDimensional.of_isCompactOperator_id
      have hcompact := (hE.comp_clm T.ker.subtypeL).clm_comp
        (-T.ker.orthogonalProjectionOnto)
      convert hcompact using 1
      ext x
      simp [ContinuousLinearMap.comp_apply]
    -- A failed lower bound on the kernel complement produces unit vectors with T xₙ → 0.
    let V : Submodule ℂ E := T.kerᗮ
    let A : V →L[ℂ] F := T.comp V.subtypeL
    have hA : ∃ C, AntilipschitzWith C A := by
      rw [antilipschitzWith_iff_exists_mul_le_norm]
      by_contra! hbound
      have hunits : ∀ ε > 0, ∃ x : V, ‖x‖ = 1 ∧ ‖A x‖ < ε := by
        intro ε hε
        obtain ⟨x, hx⟩ := hbound ε hε
        have hxne : x ≠ 0 := by
          intro hxzero
          simp [hxzero] at hx
        refine ⟨(‖x‖⁻¹ : ℂ) • x, norm_smul_inv_norm hxne, ?_⟩
        have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
        have hnorm : ‖(‖x‖⁻¹ : ℂ)‖ = ‖x‖⁻¹ := by simp
        rw [map_smul, norm_smul, hnorm]
        calc
          _ < ‖x‖⁻¹ * (ε * ‖x‖) := mul_lt_mul_of_pos_left hx (inv_pos.mpr hxpos)
          _ = ε := by rw [mul_left_comm, inv_mul_cancel₀ hxpos.ne', mul_one]
      obtain ⟨φ, _, hφpos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
      choose x hxnorm hxbound using fun n ↦ hunits (φ n) (hφpos n)
      have hAx : Tendsto (fun n ↦ A (x n)) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n ↦ (hxbound n).le) hφ
      -- Compactness makes their error images converge; the parametrix then forces xₙ to converge.
      obtain ⟨K, hK, hKE⟩ := hE.image_closedBall_subset_compact 1
      obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
        (fun n ↦ hKE ⟨(x n : E), by simpa using (hxnorm n).le, rfl⟩)
      have hxlim : Tendsto (fun n ↦ (x (ψ n) : E)) atTop (𝓝 (-y)) := by
        have hQT := Q.continuous.continuousAt.tendsto.comp (hAx.comp hψ.tendsto_atTop)
        have hsub := hQT.sub hψy
        simpa [A, ContinuousLinearMap.comp_apply] using hsub
      -- The limit lies in both the kernel and its orthogonal complement, but has unit norm.
      have hymem : -y ∈ V := T.ker.isClosed_orthogonal.mem_of_tendsto hxlim
        (Eventually.of_forall fun n ↦ (x (ψ n)).property)
      have hyker : -y ∈ T.ker := by
        apply LinearMap.mem_ker.mpr
        have hTy := T.continuous.continuousAt.tendsto.comp hxlim
        exact tendsto_nhds_unique hTy (hAx.comp hψ.tendsto_atTop)
      have hyzero : -y = 0 := Submodule.disjoint_def.mp T.ker.orthogonal_disjoint (-y) hyker hymem
      have hynorm : ‖-y‖ = 1 := by
        apply tendsto_nhds_unique (continuous_norm.continuousAt.tendsto.comp hxlim)
        change Tendsto (fun n ↦ ‖x (ψ n)‖) atTop (𝓝 1)
        simpa only [hxnorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          atTop (𝓝 1))
      simp [hyzero] at hynorm
    -- The bounded-below restriction has closed range, equal to the range of T.
    obtain ⟨C, hC⟩ := hA
    have hrange : T.range = A.range := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        obtain ⟨y, hy, z, hz, hsum⟩ := T.ker.exists_add_mem_mem_orthogonal x
        refine ⟨⟨z, hz⟩, ?_⟩
        change T z = T x
        rw [hsum, map_add, show T y = 0 from hy, zero_add]
      · rintro _ ⟨x, rfl⟩
        exact ⟨x, rfl⟩
    have hclosed : IsClosed (T.range : Set F) := by
      rw [hrange]
      exact (hC.isClosedEmbedding A.uniformContinuous).isClosed_range
    have : CompleteSpace T.range := hclosed.completeSpace_coe
    -- Projecting the right compact error to the cokernel complement gives minus the identity.
    have horth : FiniteDimensional ℂ T.rangeᗮ := by
      apply FiniteDimensional.of_isCompactOperator_id
      have hcompact := (hF.comp_clm T.rangeᗮ.subtypeL).clm_comp
        (-T.rangeᗮ.orthogonalProjectionOnto)
      convert hcompact using 1
      ext x
      simp only [Function.comp_apply, neg_apply,
        sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, Submodule.subtypeL_apply, map_sub,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
      rw [Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero
        (show T (Q (x : F)) ∈ T.range from ⟨Q x, rfl⟩)]
      simp
    have hcoker : FiniteDimensional ℂ (F ⧸ T.range) :=
      FiniteDimensional.of_injective T.range.quotientEquivOrthogonal.toLinearMap
        T.range.quotientEquivOrthogonal.injective
    exact (isFredholm_iff_closed_range_finite T).mpr ⟨hclosed, hker, hcoker⟩

/-- The opposite member of a two-sided parametrix pair is Fredholm. -/
theorem isFredholm_parametrix (T : E →L[ℂ] F) (Q : F →L[ℂ] E)
    (hE : IsCompactOperator (Q.comp T - ContinuousLinearMap.id ℂ E))
    (hF : IsCompactOperator (T.comp Q - ContinuousLinearMap.id ℂ F)) :
    Q.IsFredholm := by
  -- Exchange the two spaces and the two compact errors in Atkinson's criterion.
  exact (atkinson Q).mpr ⟨T, hF, hE⟩

/-- index is constant on operator-norm-continuous Fredholm paths. -/
theorem index_eq_of_fredholm_path {T₀ T₁ : E →L[ℂ] F} (γ : Path T₀ T₁)
    (hγ : ∀ t, (γ t).IsFredholm) : T₀.index = T₁.index := by
  -- The operator-norm continuity of the path transports local constancy of the index.
  have hcontinuous : Continuous (fun t ↦ (γ t).index) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hγ t).index_continuousAt.comp γ.continuous.continuousAt
  -- A continuous integer-valued function on the connected interval is constant.
  have hconstant := TotallyDisconnectedSpace.eq_of_continuous
    (fun t ↦ (γ t).index) hcontinuous 0 1
  simpa only [γ.source, γ.target] using hconstant

/-- compact perturbations preserve Fredholmness. -/
theorem isFredholm_add_compact (T K : E →L[ℂ] F) (hT : T.IsFredholm)
    (hK : IsCompactOperator K) : (T + K).IsFredholm := by
  -- The old parametrix still works, because each new error adds a compact composition.
  obtain ⟨Q, hE, hF⟩ := (atkinson T).mp hT
  apply (atkinson (T + K)).mpr
  refine ⟨Q, ?_, ?_⟩
  · convert hE.add (hK.clm_comp Q) using 1
    ext x
    simp only [comp_apply, add_apply, map_add, sub_apply, id_apply,
      Pi.add_apply, Function.comp_apply]
    abel
  · convert hF.add (hK.comp_clm Q) using 1
    ext x
    simp only [comp_apply, add_apply, sub_apply, id_apply,
      Pi.add_apply, Function.comp_apply]
    abel

/-- compact perturbations preserve the integer index. -/
theorem index_add_compact (T K : E →L[ℂ] F) (hT : T.IsFredholm)
    (hK : IsCompactOperator K) : (T + K).index = T.index := by
  -- Interpolate in the operator norm; every scalar multiple of K remains compact.
  let γ : Path T (T + K) := {
    toFun := fun t ↦ T + (t : ℝ) • K
    continuous_toFun := by fun_prop
    source' := by simp
    target' := by simp }
  have hγ : ∀ t, (γ t).IsFredholm := by
    intro t
    exact isFredholm_add_compact T ((t : ℝ) • K) hT (hK.smul (t : ℝ))
  -- The same path connects the original operator to the specified perturbation.
  exact (index_eq_of_fredholm_path γ hγ).symm

/-- a fixed finite-codimension domain complement works for all small perturbations.
The quotient is identified by the natural inclusion of the *fixed* orthogonal complement. -/
theorem exists_radius_fixed_complement (T₀ : E →L[ℂ] F) (hT₀ : T₀.IsFredholm)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hVfin : FiniteDimensional ℂ (E ⧸ V)) (hdisj : Disjoint V T₀.ker) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : E →L[ℂ] F, ‖T - T₀‖ < ε →
      Function.Injective (T.comp V.subtypeL) ∧
      IsClosed (V.map T.toLinearMap : Set F) ∧
      Function.Bijective (fun w : (V.map T₀.toLinearMap)ᗮ ↦
        (V.map T.toLinearMap).mkQ (w : F)) := by
  -- Restricting a Fredholm operator to the closed finite-codimension V preserves Fredholmness.
  let : CompleteSpace V := hV.completeSpace_coe
  let : FiniteDimensional ℂ (E ⧸ V) := hVfin
  let A₀ : V →L[ℂ] F := T₀.comp V.subtypeL
  have hA₀ : A₀.IsFredholm := hT₀.comp (V.isFredholm_subtypeL hV)
  have hA₀range : A₀.range = V.map T₀.toLinearMap := by
    simp [A₀, LinearMap.range_comp]
  have hA₀inj : Function.Injective A₀ := by
    apply (injective_iff_map_eq_zero A₀).mpr
    intro v hv
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hdisj v v.property hv
  -- The closed base image has its specified orthogonal complement, giving an invertible block.
  let W : Submodule ℂ F := (V.map T₀.toLinearMap)ᗮ
  have hclosed₀ : IsClosed (V.map T₀.toLinearMap : Set F) := by
    rw [← hA₀range]
    exact hA₀.isClosed_range
  let : CompleteSpace (V.map T₀.toLinearMap) := hclosed₀.completeSpace_coe
  have hcompl : IsCompl A₀.range W := by
    rw [hA₀range]
    exact (V.map T₀.toLinearMap).isCompl_orthogonal
  let B (T : E →L[ℂ] F) : V × W →L[ℂ] F :=
    (T.comp V.subtypeL).coprod W.subtypeL
  have hB₀ : (B T₀).IsInvertible := by
    refine ⟨A₀.coprodSubtypeLEquivOfIsCompl hcompl
      (LinearMap.ker_eq_bot.mpr hA₀inj), ?_⟩
    simp only [coprodSubtypeLEquivOfIsCompl, ContinuousLinearEquiv.coe_ofBijective]
    rfl
  -- Openness of invertibility supplies one positive operator-norm radius for this fixed block.
  have hBcontinuous : Continuous B := by
    exact (coprodEquivL ℂ).continuous.comp
      ((continuous_id.clm_comp continuous_const).prodMk continuous_const)
  have hopen : IsOpen {T : E →L[ℂ] F | (B T).IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hBcontinuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen T₀ hB₀
  refine ⟨ε, hε, ?_⟩
  intro T hT
  have hBT : (B T).IsInvertible := hball
    (by simpa [Metric.mem_ball, dist_eq_norm] using hT)
  -- Inside that radius, the inverse block supplies the complement and solution coordinates.
  let P : F →L[ℂ] W := (ContinuousLinearMap.snd ℂ V W).comp (B T).inverse
  let S : F →L[ℂ] V := (ContinuousLinearMap.fst ℂ V W).comp (B T).inverse
  have hPsub (w : W) : P w = w := by
    have h := congrArg Prod.snd (hBT.inverse_apply_self (0, w))
    simpa [P, B] using h
  have hPimage (v : V) : P (T v) = 0 := by
    have h := congrArg Prod.snd (hBT.inverse_apply_self (v, 0))
    simpa [P, B] using h
  have hdecomp (y : F) : T (S y) + (P y : F) = y := by
    simpa [P, S, B] using hBT.self_apply_inverse y
  -- The varying image is exactly the kernel of the continuous complement coordinate.
  have hker : P.ker = V.map T.toLinearMap := by
    ext y
    constructor
    · intro hy
      have hzero : P y = 0 := hy
      refine ⟨S y, (S y).property, ?_⟩
      simpa [hzero] using hdecomp y
    · rintro ⟨v, hv, rfl⟩
      exact hPimage ⟨v, hv⟩
  -- Recover injectivity, closedness, and the quotient map induced by the original inclusion W → F.
  refine ⟨?_, ?_, ?_⟩
  · intro v₁ v₂ hsame
    have hsameBlock : B T (v₁, 0) = B T (v₂, 0) := by
      simpa [B] using hsame
    exact congrArg Prod.fst (hBT.bijective.injective hsameBlock)
  · rw [← hker]
    exact P.isClosed_ker
  · have hsplit : IsCompl W P.ker := LinearMap.isCompl_of_proj hPsub
    rw [hker] at hsplit
    exact ((V.map T.toLinearMap).quotientEquivOfIsCompl W hsplit.symm).symm.bijective

/-- on a point every linear map has index equal to the rank difference. -/
theorem index_on_point (r s : ℕ)
    (T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)) :
    T.index = (r : ℤ) - s := by
  -- Rank-nullity cancels the range dimension in the kernel-minus-cokernel index.
  rw [LinearMap.index_eq_of_finiteDimensional]
  -- The standard complex coordinate spaces have the stated ranks, including zero.
  simp only [finrank_euclideanSpace_fin]

end AtiyahSinger

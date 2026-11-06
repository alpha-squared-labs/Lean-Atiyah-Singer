/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Fredholm
public import Mathlib

/-!
# Norm paths of invertible and Fredholm operators

Public module ID: M0648.

Path connectedness of the complex invertible group is weaker than Kuiper's
contractibility theorem and also holds in finite-dimensional complex Hilbert
spaces. Equal-index Fredholm operators lie in the same norm path component.

The unitary path uses reflection in the kernel of the negative real part and
continuous functional calculus. Polar deformation handles arbitrary invertibles;
a fixed parametrix reduces equal-index Fredholm endpoints to an invertible compact
perturbation. No measurable functional calculus or separability hypothesis is required.

Source: Spin Geometry III.7.6–7.7.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Complex Ring
open scoped CStarAlgebra ComplexOrder ComplexStarModule unitInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

/-- A kernel invariant under an operator and its adjoint has a commuting projection. -/
private theorem commute_starProjection_ker {B T : E →L[ℂ] E}
    (hBT : Commute B T) (hBTstar : Commute B (star T)) :
    Commute B.ker.starProjection T := by
  -- Both the kernel and its orthogonal complement are invariant under T.
  have hker (x : E) (hx : x ∈ B.ker) : T x ∈ B.ker := by
    change B x = 0 at hx
    change B (T x) = 0
    have h := congrArg (fun A : E →L[ℂ] E ↦ A x) hBT.eq
    simpa [mul_apply_eq_comp, hx] using h
  have hkerstar (x : E) (hx : x ∈ B.ker) : (star T) x ∈ B.ker := by
    change B x = 0 at hx
    change B ((star T) x) = 0
    have h := congrArg (fun A : E →L[ℂ] E ↦ A x) hBTstar.eq
    simpa [mul_apply_eq_comp, hx] using h
  apply ContinuousLinearMap.ext
  intro x
  change B.ker.starProjection (T x) = T (B.ker.starProjection x)
  apply B.ker.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hker _ (B.ker.starProjection_apply_mem x)
  · intro y hy
    rw [← map_sub, ← T.adjoint_inner_right]
    exact B.ker.starProjection_inner_eq_zero x _ (hkerstar y hy)

/-- A unitary with nonnegative real part lies in the path component of the identity. -/
private theorem unitary_joined_one_of_nonneg_realPart
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (u : unitary A) (hu : 0 ≤ (ℜ (u : A) : A)) :
    Joined (1 : unitary A) u := by
  -- Positivity of the real part excludes the branch cut at -1.
  have hgap : -(1 : ℂ) ∉ spectrum ℂ (u : A) := by
    intro h
    have hmem : (-1 : ℝ) ∈ spectrum ℝ (ℜ (u : A) : A) := by
      rw [spectrum_realPart' (u : A) (by infer_instance)]
      exact ⟨-1, h, by simp⟩
    have hnonneg := spectrum_nonneg_of_nonneg hu hmem
    norm_num at hnonneg
  exact Unitary.joined 1 u ((Unitary.norm_sub_one_lt_two_iff u.property).mpr hgap)

/-- A self-adjoint unitary lies in the path component of the identity over the complex field. -/
private theorem unitary_joined_one_of_isSelfAdjoint
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) : Joined (1 : unitary A) u := by
  -- Multiplication by i moves the spectrum {1,-1} away from the logarithm's cut.
  let w : unitary A := ⟨Complex.I • (1 : A), by
    constructor <;> simp [star_smul, smul_smul]⟩
  have hw : Joined (1 : unitary A) w := by
    apply unitary_joined_one_of_nonneg_realPart
    change 0 ≤ (ℜ (Complex.I • (1 : A)) : A)
    rw [realPart_apply_coe]
    simp [star_smul]
  have hwu : Joined (1 : unitary A) (w * u) := by
    apply unitary_joined_one_of_nonneg_realPart
    change 0 ≤ (ℜ ((Complex.I • (1 : A)) * u) : A)
    rw [realPart_apply_coe]
    simp [star_smul, hu.star_eq]
  have hstar : Continuous (star : unitary A → unitary A) :=
    continuous_subtype_val.star.subtype_mk _
  simpa [← mul_assoc] using (hw.map hstar).mul hwu

/-- The unitary group of a complete complex Hilbert space is path connected. -/
private theorem unitary_joined_one (u : unitary (E →L[ℂ] E)) :
    Joined (1 : unitary (E →L[ℂ] E)) u := by
  let : PartialOrder (E →L[ℂ] E) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (E →L[ℂ] E) := CStarAlgebra.spectralOrderedRing _
  -- The kernel of the negative part provides the required spectral cut using only
  -- continuous functional calculus and Hilbert-space orthogonal projection.
  let A : E →L[ℂ] E := ℜ (u : E →L[ℂ] E)
  let N : E →L[ℂ] E := A⁻
  let P : E →L[ℂ] E := N.ker.starProjection
  have hA : IsSelfAdjoint A := (realPart (u : E →L[ℂ] E)).property
  have hN : IsSelfAdjoint N := (CFC.negPart_nonneg A).isSelfAdjoint
  have hP : IsSelfAdjoint P := isSelfAdjoint_starProjection N.ker
  have hPproj : IsStarProjection P :=
    ⟨N.ker.isIdempotentElem_starProjection, hP⟩
  have hAU : Commute A (u : E →L[ℂ] E) := by
    dsimp [A]
    rw [realPart_apply_coe]
    exact ((Commute.refl _).add_left (commute_unitary_star_self u.property)).smul_left _
  have hNU : Commute N (u : E →L[ℂ] E) := hAU.cfcₙ_real (·⁻)
  have hNUstar : Commute N (star (u : E →L[ℂ] E)) := by
    simpa only [hN.star_eq] using hNU.star_star
  have hPU : Commute P (u : E →L[ℂ] E) := commute_starProjection_ker hNU hNUstar
  -- The projection kills the negative part and fixes the positive part.
  have hNP : N * P = 0 := by
    ext x
    exact N.ker.starProjection_apply_mem x
  have hPN : P * N = 0 := by
    simpa only [star_mul, hN.star_eq, hP.star_eq, star_zero] using congrArg star hNP
  have hPpos : P * A⁺ = A⁺ := by
    ext x
    apply N.ker.starProjection_eq_self_iff.mpr
    have hzero : N * A⁺ = 0 := CFC.negPart_mul_posPart A
    exact congrArg (fun T : E →L[ℂ] E ↦ T x) hzero
  -- Reflection in ker(A⁻) turns the real part into the positive operator A⁺ + A⁻.
  let s : unitary (E →L[ℂ] E) := ⟨2 * P - 1, hPproj.two_mul_sub_one_mem_unitary⟩
  have hs : IsSelfAdjoint (s : E →L[ℂ] E) := by
    change star (2 * P - 1) = 2 * P - 1
    simp only [star_sub, star_mul, star_ofNat, hP.star_eq, star_one]
    noncomm_ring
  have hsU : Commute (s : E →L[ℂ] E) (u : E →L[ℂ] E) :=
    ((Commute.ofNat_left 2 _).mul_left hPU).sub_left (Commute.one_left _)
  have hsA : (s : E →L[ℂ] E) * A = A⁺ + N := by
    nth_rw 1 [← CFC.posPart_sub_negPart A hA]
    change (2 * P - 1) * (A⁺ - N) = A⁺ + N
    noncomm_ring [hPpos, hPN]
  have hreal : (ℜ ((s * u : unitary (E →L[ℂ] E)) : E →L[ℂ] E) : E →L[ℂ] E) =
      A⁺ + N := by
    rw [← hsA]
    change (ℜ ((s : E →L[ℂ] E) * u) : E →L[ℂ] E) = (s : E →L[ℂ] E) * A
    dsimp only [A]
    rw [realPart_apply_coe, realPart_apply_coe, star_mul, hs.star_eq,
      mul_smul_comm, mul_add]
    congr 1
    have hsUstar : Commute (s : E →L[ℂ] E) (star (u : E →L[ℂ] E)) := by
      simpa only [hs.star_eq] using hsU.star_star
    rw [hsUstar.eq]
  have hsu : Joined (1 : unitary (E →L[ℂ] E)) (s * u) := by
    apply unitary_joined_one_of_nonneg_realPart
    rw [hreal]
    exact add_nonneg (CFC.posPart_nonneg A) (CFC.negPart_nonneg A)
  have hsjoined : Joined (1 : unitary (E →L[ℂ] E)) s :=
    unitary_joined_one_of_isSelfAdjoint s hs
  have hstar : Continuous
      (star : unitary (E →L[ℂ] E) → unitary (E →L[ℂ] E)) :=
    continuous_subtype_val.star.subtype_mk _
  simpa [← mul_assoc] using (hsjoined.map hstar).mul hsu

/-- An invertible complex Hilbert-space operator admits an invertible path to a unitary. -/
private theorem exists_unitary_path (T : E →L[ℂ] E) (hT : T.IsInvertible) :
    ∃ u : unitary (E →L[ℂ] E), ∃ γ : Path T (u : E →L[ℂ] E),
      ∀ t, (γ t).IsInvertible := by
  -- First identify invertibility with units, so the positive square-root calculus applies.
  have hTu : IsUnit T := by
    obtain ⟨e, he⟩ := hT
    exact ⟨(ContinuousLinearEquiv.unitsEquiv ℂ E).symm e, he⟩
  have invertible_of_isUnit (f : E →L[ℂ] E) (hf : IsUnit f) : f.IsInvertible := by
    obtain ⟨v, rfl⟩ := hf
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℂ E v, rfl⟩
  -- The positive square root P satisfies P² = T* T and remains invertible.
  let P : E →L[ℂ] E := CFC.sqrt (star T * T)
  have hPnonneg : 0 ≤ P := CFC.sqrt_nonneg _
  have hPunit : IsUnit P := (CFC.isUnit_sqrt_iff _).mpr (hTu.star.mul hTu)
  have hPpos : IsStrictlyPositive P := hPunit.isStrictlyPositive hPnonneg
  have hPself : IsSelfAdjoint P := hPnonneg.isSelfAdjoint
  have hPsq : P * P = star T * T := CFC.sqrt_mul_sqrt_self _
  -- Removing P produces an invertible isometry, hence a unitary operator.
  let U : E →L[ℂ] E := T * P⁻¹ʳ
  have hUunit : IsUnit U := hTu.mul hPunit.ringInverse
  have hUstar : star U * U = 1 := by
    dsimp [U]
    rw [star_mul, ← Ring.inverse_star, hPself.star_eq]
    calc
      P⁻¹ʳ * star T * (T * P⁻¹ʳ) = P⁻¹ʳ * (star T * T) * P⁻¹ʳ := by
        simp only [mul_assoc]
      _ = P⁻¹ʳ * (P * P) * P⁻¹ʳ := by rw [hPsq]
      _ = 1 := by
        rw [Ring.inverse_mul_cancel_left P P hPunit, Ring.mul_inverse_cancel P hPunit]
  let u : unitary (E →L[ℂ] E) := ⟨U, hUunit.mem_unitary_of_star_mul_self hUstar⟩
  -- Interpolate the inverse positive factor with the identity; positivity keeps it invertible.
  let γ : Path T (u : E →L[ℂ] E) :=
    { toFun := fun t ↦ T * ((1 - (t : ℝ)) • 1 + (t : ℝ) • P⁻¹ʳ)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp [u, U] }
  refine ⟨u, γ, ?_⟩
  intro t
  apply invertible_of_isUnit
  apply hTu.mul
  have hinv : IsStrictlyPositive P⁻¹ʳ := hPpos.ringInverse
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hleft : 0 ≤ (1 - (t : ℝ)) • (1 : E →L[ℂ] E) :=
      smul_nonneg (sub_nonneg.mpr t.property.2) zero_le_one
    exact (IsStrictlyPositive.nonneg_add hleft (hinv.smul htpos)).isUnit

/-- the invertible group of a complex Hilbert space is path connected in norm. -/
theorem exists_invertible_path_to_id (T : E →L[ℂ] E) (hT : T.IsInvertible) :
    ∃ γ : Path T (ContinuousLinearMap.id ℂ E), ∀ t, (γ t).IsInvertible := by
  -- First remove the positive factor, then reverse the unitary path to the identity.
  obtain ⟨u, γ, hγ⟩ := exists_unitary_path T hT
  have h₁ : JoinedIn {S : E →L[ℂ] E | S.IsInvertible} T (u : E →L[ℂ] E) := ⟨γ, hγ⟩
  obtain ⟨δ⟩ := (unitary_joined_one u).symm
  have h₂ : JoinedIn {S : E →L[ℂ] E | S.IsInvertible} (u : E →L[ℂ] E)
      (ContinuousLinearMap.id ℂ E) := by
    refine ⟨δ.map continuous_subtype_val, ?_⟩
    intro t
    obtain ⟨v, hv⟩ := Unitary.isUnit_coe (U := δ t)
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℂ E v, hv⟩
  exact h₁.trans h₂

/-- A compact difference gives an explicit Fredholm path with the original endpoints. -/
private theorem exists_fredholm_path_of_isCompactOperator_sub (T₀ T₁ : E →L[ℂ] F)
    (hT₀ : T₀.IsFredholm) (hK : IsCompactOperator (T₁ - T₀)) :
    ∃ γ : Path T₀ T₁, ∀ t, (γ t).IsFredholm := by
  -- The affine path retains the fixed compact difference at every time.
  let γ : Path T₀ T₁ :=
    { toContinuousMap :=
        { toFun := fun t : unitInterval ↦ T₀ + (t : ℝ) • (T₁ - T₀)
          continuous_toFun := continuous_const.add
            (continuous_subtype_val.smul continuous_const) }
      source' := by simp
      target' := by simp }
  -- Apply compact-perturbation invariance to the same affine path.
  refine ⟨γ, fun t ↦ ?_⟩
  exact AtiyahSinger.isFredholm_add_compact T₀ ((t : ℝ) • (T₁ - T₀))
    hT₀ (hK.smul _)

omit [CompleteSpace E] [CompleteSpace F] in
/-- An index-zero Fredholm operator can be made invertible by a compact perturbation. -/
private theorem exists_isInvertible_sub_isCompactOperator_of_index_eq_zero (T : E →L[ℂ] F)
    (hT : T.IsFredholm) (hind : T.index = 0) :
    ∃ C : E →L[ℂ] F, C.IsInvertible ∧ IsCompactOperator (C - T) := by
  -- The Fredholm package isolates the only missing block: kernel to cokernel.
  obtain ⟨pkg⟩ := hT.nonempty_fredholmPackage
  let := pkg.decDom.finite_X₀
  let := pkg.decCodom.finite_X₀
  have hcoker : Module.finrank ℂ (F ⧸ pkg.decCodom.X₁) =
      Module.finrank ℂ pkg.decCodom.X₀ :=
    (pkg.decCodom.X₁.quotientEquivOfIsTopCompl pkg.decCodom.X₀
      pkg.decCodom.isTopCompl).toLinearEquiv.finrank_eq
  have hdim : Module.finrank ℂ pkg.decDom.X₀ = Module.finrank ℂ pkg.decCodom.X₀ := by
    rw [LinearMap.index_eq_finrank_sub, pkg.ker_eq, pkg.range_eq, hcoker] at hind
    omega
  let e₀ : pkg.decDom.X₀ ≃L[ℂ] pkg.decCodom.X₀ :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  -- Complete the diagonal operator with an isomorphism of the finite missing blocks.
  let dE : (pkg.decDom.X₁ × pkg.decDom.X₀) ≃L[ℂ] E :=
    pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl
  let dF : (pkg.decCodom.X₁ × pkg.decCodom.X₀) ≃L[ℂ] F :=
    pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl
  let C : E ≃L[ℂ] F := dE.symm.trans ((pkg.equiv.prodCongr e₀).trans dF)
  let P₀ : E →L[ℂ] pkg.decDom.X₀ :=
    pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm
  let K : E →L[ℂ] F := pkg.decCodom.X₀.subtypeL.comp (e₀.toContinuousLinearMap.comp P₀)
  have hK : IsCompactOperator K := by
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (pkg.decCodom.X₀.subtypeL.comp e₀.toContinuousLinearMap)).comp_clm P₀
  have hCT : (C : E →L[ℂ] F) - T = K := by
    ext x
    have hTx : T x = (pkg.equiv (pkg.decDom.proj x) : F) :=
      DFunLike.congr_fun pkg.eq_equiv x
    simp only [sub_apply, hTx, C, dE, dF,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      Submodule.prodEquivOfIsTopCompl_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
      Submodule.prodEquivOfIsTopCompl_apply]
    simp [K, P₀, FredholmDecomposition.proj]
  refine ⟨C, ⟨C, rfl⟩, ?_⟩
  rwa [hCT]

/-- equal-index Fredholm operators lie in the same norm path component. -/
theorem exists_fredholm_path_of_index_eq (T₀ T₁ : E →L[ℂ] F)
    (hT₀ : T₀.IsFredholm) (hT₁ : T₁.IsFredholm) (hind : T₀.index = T₁.index) :
    ∃ γ : Path T₀ T₁, ∀ t, (γ t).IsFredholm := by
  -- A parametrix for T₁ turns equality of indices into a single index-zero operator.
  obtain ⟨Q, hQT, hTQ⟩ := (AtiyahSinger.atkinson T₁).mp hT₁
  have hQ : Q.IsFredholm :=
    AtiyahSinger.isFredholm_parametrix T₁ Q hQT hTQ
  have hQTindex : (Q.comp T₁).index = 0 := by
    have h := AtiyahSinger.index_add_compact
      (ContinuousLinearMap.id ℂ E) (Q.comp T₁ - ContinuousLinearMap.id ℂ E)
      ContinuousLinearMap.IsFredholm.id hQT
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hindex : (Q.comp T₀).index = 0 := by
    rw [hQ.index_comp hT₀, hind, ← hQ.index_comp hT₁]
    exact hQTindex
  obtain ⟨C, hC, hK⟩ := exists_isInvertible_sub_isCompactOperator_of_index_eq_zero
    (Q.comp T₀) (hQ.comp hT₀) hindex
  -- The same Q and C give a compact difference at the original target endpoints.
  have hdiff : IsCompactOperator (T₁.comp C - T₀) := by
    have hleft := hK.clm_comp T₁
    have hright := hTQ.comp_clm T₀
    convert hleft.add hright using 1
    ext x
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  obtain ⟨γ₀, hγ₀⟩ := exists_fredholm_path_of_isCompactOperator_sub
    T₀ (T₁.comp C) hT₀ hdiff
  -- Transport the invertible path by left composition with the fixed Fredholm T₁.
  obtain ⟨γC, hγC⟩ := exists_invertible_path_to_id C hC
  let γ₁ : Path (T₁.comp C) T₁ :=
    { toContinuousMap :=
        { toFun := fun t : unitInterval ↦ T₁.comp (γC t)
          continuous_toFun := continuous_const.clm_comp γC.continuous }
      source' := by simp
      target' := by simp }
  have hγ₁ : ∀ t, (γ₁ t).IsFredholm := by
    intro t
    exact hT₁.comp (hγC t).isFredholm
  -- Concatenation keeps the compact deformation and coordinate deformation witnesses.
  refine ⟨γ₀.trans γ₁, fun t ↦ ?_⟩
  have ht : (γ₀.trans γ₁) t ∈ Set.range γ₀ ∪ Set.range γ₁ := by
    rw [← Path.trans_range]
    exact Set.mem_range_self t
  rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]
    exact hγ₀ s
  · rw [← hs]
    exact hγ₁ s

end AtiyahSinger

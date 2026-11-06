/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolParametrix
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev

import AtiyahSinger.Analysis.AtlasSobolevEmbedding
import AtiyahSinger.Analysis.Fredholm

/-!
# Sobolev and Fredholm realizations on the original finite-rank atlases

Public module ID: M0285.

A10: every actual atlas PDO has its unique bounded extension between the
original real-order atlas Sobolev completions. If its principal class has a
specified elliptic homogeneous representative, it has a two-sided parametrix,
Fredholm realizations and the original smooth kernel/cokernel index.

The smooth maps and completions retain independent locally varying fiber
ranks. No new norm or globally constant rank is imposed on the original fibers.
The smoothing remainder may couple different components. Ellipticity of the
given homogeneous data is a hypothesis; Fredholmness, a parametrix and finite
kernel/cokernel are conclusions. This is not a new definition of ellipticity
for the larger class of arbitrary nonhomogeneous full symbols.

Sources: SG III.3.17, III.4.7 and III.5.2--5.3. The finite atlas adaptation
is a project supplement of the local estimates and regularity argument.
The bounded Sobolev realizations retain the original section actions. The elliptic
parametrix, Fredholm property, and natural kernel/cokernel comparisons are proved
using that same action and its all-order smoothing residuals.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

namespace AtlasPseudodifferentialOperator

variable {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
  (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)

/-- An all-order atlas smoothing map has one actual smooth output on every Sobolev input. -/
private theorem exists_smooth_lift_of_isAtlasSmoothingOperator
    (R : A.smoothSections →ₗ[ℂ] B.smoothSections) (hR : IsAtlasSmoothingOperator A B R)
    (s t : ℝ) (T : L.SobolevSpace s →L[ℂ] K.SobolevSpace t)
    (hT : ∀ v : A.smoothSections,
      T (L.smoothToSobolev s v) = K.smoothToSobolev t (R v)) (u : L.SobolevSpace s) :
    ∃ w : B.smoothSections, K.smoothToSobolev t w = T u := by
  classical
  -- Forgetting higher derivatives is bounded for the same finite localization norm.
  let forget (k : ℕ) : K.CkSectionSpace k →ₗ[ℂ] K.CkSectionSpace 0 := {
    toFun := fun v ↦ ⟨v.val, fun i ↦ (v.property i).of_le (by simp)⟩
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hforget (k : ℕ) (v : K.CkSectionSpace k) : ‖forget k v‖ ≤ ‖v‖ := by
    change ‖K.ckDerivativeCoordinates 0 (forget k v)‖ ≤ ‖K.ckDerivativeCoordinates k v‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ := by ext; omega
    subst i
    exact (norm_le_pi_norm (K.ckDerivativeCoordinates k v j) ⟨0, Nat.zero_lt_succ k⟩).trans
      (norm_le_pi_norm (K.ckDerivativeCoordinates k v) j)
  let F (k : ℕ) : K.CkSectionSpace k →L[ℂ] K.CkSectionSpace 0 :=
    (forget k).mkContinuous 1 (by simpa using hforget k)
  -- All finite-order extensions agree as actual C0 sections by the dense smooth formula.
  let order (k : ℕ) : ℝ := (n : ℝ) / 2 + k + 1
  have horder (k : ℕ) : (n : ℝ) / 2 + k < order k := by dsimp [order]; linarith
  choose T' hT' using fun k : ℕ ↦ hR L K s (order k)
  let V (k : ℕ) : L.SobolevSpace s →L[ℂ] K.CkSectionSpace k :=
    (K.sobolevToCk k (order k) (horder k)).comp (T' k)
  have hV (k : ℕ) (v : A.smoothSections) :
      V k (L.smoothToSobolev s v) = K.smoothToCk k (R v) := by
    simp only [V, ContinuousLinearMap.comp_apply, hT', K.sobolevToCk_smoothToSobolev]
  have hsame (k : ℕ) : (F k).comp (V k) = V 0 := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      ((F k).comp (V k)).continuous (V 0).continuous
    funext v
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, hV]
    rfl
  let w₀ := V 0 u
  have hvalues (k : ℕ) : (V k u).val = w₀.val := by
    have h := congrArg (fun S : L.SobolevSpace s →L[ℂ] K.CkSectionSpace 0 ↦ S u) (hsame k)
    exact congrArg Subtype.val h
  have hw : B.IsSmoothSection w₀.val := by
    intro i
    apply contMDiffOn_infty.mpr
    intro k
    rw [← hvalues k]
    exact (V k u).property i
  let w : B.smoothSections := ⟨w₀.val, hw⟩
  -- Compare at one target order high enough both for C0 embedding and for the specified t.
  let a : ℝ := max t (order 0)
  have ha0 : (n : ℝ) / 2 + (0 : ℕ) < a := (horder 0).trans_le (le_max_right _ _)
  obtain ⟨S, hS⟩ := hR L K s a
  let W := (K.sobolevToCk 0 a ha0).comp S
  have hW : W = V 0 := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer W.continuous (V 0).continuous
    funext v
    simp only [Function.comp_apply, W, ContinuousLinearMap.comp_apply, hS,
      K.sobolevToCk_smoothToSobolev, hV]
  have hwS : K.smoothToSobolev a w = S u := by
    apply K.sobolevToCk_injective 0 a ha0
    rw [K.sobolevToCk_smoothToSobolev]
    change K.smoothToCk 0 w = W u
    rw [hW]
    rfl
  have hST : (K.sobolevInclusion a t (le_max_left _ _)).comp S = T := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      ((K.sobolevInclusion a t (le_max_left _ _)).comp S).continuous T.continuous
    funext v
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, hS, hT,
      K.sobolevInclusion_smoothToSobolev]
  refine ⟨w, ?_⟩
  have h := congrArg (fun S : L.SobolevSpace s →L[ℂ] K.SobolevSpace t ↦ S u) hST
  simpa only [ContinuousLinearMap.comp_apply, ← hwS, K.sobolevInclusion_smoothToSobolev] using h

variable (g : SmoothCotangentMetric (n := n) (M := M))
  (a : AtlasSymbolFunction (n := n) E F)
  (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
  (hP : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
    (atlasRegularizedSymbol A B g m a hs hh))
  (hi : IsEllipticAtlasSymbol a)

include g a hs hh hP hi

/-- SG III.4.7: the specified elliptic principal data give an actual two-sided parametrix. -/
theorem exists_parametrix_of_homogeneous :
    ∃ Q : AtlasPseudodifferentialOperator B A (-m),
      IsAtlasSmoothingOperator A A (Q.toLinearMap.comp P.toLinearMap - LinearMap.id) ∧
      IsAtlasSmoothingOperator B B (P.toLinearMap.comp Q.toLinearMap - LinearMap.id) := by
  -- The prescribed homogeneous representative satisfies exactly the full-symbol inverse bounds.
  apply P.exists_parametrix_of_isElliptic
  refine ⟨atlasRegularizedSymbol A B g m a hs hh, hP, ?_⟩
  exact (isEllipticFullAtlasSymbol_atlasRegularizedSymbol_iff A B g m a hs hh).mpr hi

/-- Every real critical Sobolev realization of the given homogeneous elliptic PDO is Fredholm. -/
theorem isFredholm_sobolevExtension_of_homogeneous (s : ℝ) :
    (P.sobolevExtension L K s).IsFredholm := by
  -- The one return map below realizes the same parametrix at the original critical orders.
  obtain ⟨Q, hleft, hright⟩ := P.exists_parametrix_of_homogeneous g a hs hh hP hi
  have hreturn : ∃ S : K.SobolevSpace (s - m) →L[ℂ] L.SobolevSpace s,
      ∀ v : B.smoothSections,
        S (K.smoothToSobolev (s - m) v) = L.smoothToSobolev s (Q.toLinearMap v) := by
    have h := (Q.existsUnique_sobolevExtension K L (s - m)).exists
    rw [show (s - m) - (-m) = s by ring] at h
    exact h
  obtain ⟨S, hS⟩ := hreturn
  let T := P.sobolevExtension L K s
  -- Each actual residual factors through one higher order and the compact Sobolev inclusion.
  obtain ⟨R, hR⟩ := hleft L L s (s + 1)
  let J := L.sobolevInclusion (s + 1) s (by linarith)
  have hleft_eq : S.comp T - ContinuousLinearMap.id ℂ _ = J.comp R := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      (S.comp T - ContinuousLinearMap.id ℂ _).continuous (J.comp R).continuous
    funext u
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      P.sobolevExtension_smoothToSobolev, hS, hR, J,
      L.sobolevInclusion_smoothToSobolev, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  obtain ⟨R', hR'⟩ := hright K K (s - m) (s - m + 1)
  let J' := K.sobolevInclusion (s - m + 1) (s - m) (by linarith)
  have hright_eq : T.comp S - ContinuousLinearMap.id ℂ _ = J'.comp R' := by
    apply DFunLike.coe_injective
    apply (K.denseRange_smoothToSobolev (s - m)).equalizer
      (T.comp S - ContinuousLinearMap.id ℂ _).continuous (J'.comp R').continuous
    funext v
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      hS, P.sobolevExtension_smoothToSobolev, hR', J',
      K.sobolevInclusion_smoothToSobolev, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  apply (atkinson T).mpr
  refine ⟨S, ?_, ?_⟩
  · rw [hleft_eq]
    exact (L.isCompactOperator_sobolevInclusion (s + 1) s (by linarith)).comp_clm R
  · rw [hright_eq]
    exact (K.isCompactOperator_sobolevInclusion (s - m + 1) (s - m)
      (by linarith)).comp_clm R'

set_option maxHeartbeats 4000000 in
-- The extended limit accommodates the actual smooth-to-Sobolev kernel and cokernel comparisons.
set_option synthInstance.maxHeartbeats 100000 in
-- The extended limit accommodates the actual smooth-to-Sobolev kernel and cokernel comparisons.
/-- Elliptic regularity identifies the actual smooth and Sobolev kernels and cokernels. -/
theorem exists_kernel_cokernel_sobolevEquiv_of_homogeneous (s : ℝ) :
    ∃ e : P.toLinearMap.ker ≃ₗ[ℂ] (P.sobolevExtension L K s).ker,
      ∃ c : (B.smoothSections ⧸ P.toLinearMap.range) ≃ₗ[ℂ]
          (K.SobolevSpace (s - m) ⧸ (P.sobolevExtension L K s).range),
        (∀ u : P.toLinearMap.ker,
          (e u).val = L.smoothToSobolev s u.val) ∧
        ∀ v : B.smoothSections,
          c (P.toLinearMap.range.mkQ v) =
            (P.sobolevExtension L K s).range.mkQ (K.smoothToSobolev (s - m) v) := by
  classical
  obtain ⟨Q, hleft, hright⟩ := P.exists_parametrix_of_homogeneous g a hs hh hP hi
  let T := P.sobolevExtension L K s
  have hreturn : ∃ S : K.SobolevSpace (s - m) →L[ℂ] L.SobolevSpace s,
      ∀ v : B.smoothSections,
        S (K.smoothToSobolev (s - m) v) = L.smoothToSobolev s (Q.toLinearMap v) := by
    have h := (Q.existsUnique_sobolevExtension K L (s - m)).exists
    rw [show (s - m) - (-m) = s by ring] at h
    exact h
  obtain ⟨S, hS⟩ := hreturn
  obtain ⟨R, hR⟩ := hleft L L s s
  obtain ⟨R', hR'⟩ := hright K K (s - m) (s - m)
  -- Extend the two identities for these exact maps from the dense smooth sections.
  have hleft_eq : S.comp T - ContinuousLinearMap.id ℂ _ = R := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      (S.comp T - ContinuousLinearMap.id ℂ _).continuous R.continuous
    funext u
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      P.sobolevExtension_smoothToSobolev, hS, hR, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  have hright_eq : T.comp S - ContinuousLinearMap.id ℂ _ = R' := by
    apply DFunLike.coe_injective
    apply (K.denseRange_smoothToSobolev (s - m)).equalizer
      (T.comp S - ContinuousLinearMap.id ℂ _).continuous R'.continuous
    funext v
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      hS, P.sobolevExtension_smoothToSobolev, hR', LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  -- The left residual gives a smooth preimage whenever the image is already smooth.
  have hlift (u : L.SobolevSpace s) (v : B.smoothSections)
      (hu : T u = K.smoothToSobolev (s - m) v) :
      ∃ w : A.smoothSections, L.smoothToSobolev s w = u ∧ P.toLinearMap w = v := by
    obtain ⟨z, hz⟩ := exists_smooth_lift_of_isAtlasSmoothingOperator L L
      (Q.toLinearMap.comp P.toLinearMap - LinearMap.id) hleft s s R hR u
    let w := Q.toLinearMap v - z
    have hres : S (T u) - u = R u := DFunLike.congr_fun hleft_eq u
    rw [hu, hS] at hres
    have hw : L.smoothToSobolev s w = u := by
      change L.smoothToSobolev s (Q.toLinearMap v - z) = u
      rw [map_sub, hz]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hres).trans (add_comm _ _))
    refine ⟨w, hw, ?_⟩
    apply K.smoothToSobolev_injective (s - m)
    rw [← P.sobolevExtension_smoothToSobolev, hw]
    exact hu
  -- The forward kernel map is precisely the original smooth embedding.
  let e₀ : P.toLinearMap.ker →ₗ[ℂ] T.ker :=
    ((L.smoothToSobolev s).comp P.toLinearMap.ker.subtype).codRestrict _ (by
      intro u
      change T (L.smoothToSobolev s u.val) = 0
      rw [P.sobolevExtension_smoothToSobolev,
        show P.toLinearMap u.val = 0 from u.property, map_zero])
  have heinj : Function.Injective e₀ := by
    intro u v huv
    apply Subtype.ext
    apply L.smoothToSobolev_injective s
    exact congrArg Subtype.val huv
  have hesurj : Function.Surjective e₀ := by
    intro u
    obtain ⟨w, hw, hPw⟩ := hlift u.val 0 (by rw [map_zero]; exact u.property)
    exact ⟨⟨w, hPw⟩, Subtype.ext hw⟩
  -- Descend the specified target embedding to the actual algebraic ranges.
  have hrange : P.toLinearMap.range ≤ T.range.comap (K.smoothToSobolev (s - m)) := by
    rintro v ⟨u, rfl⟩
    exact ⟨L.smoothToSobolev s u, P.sobolevExtension_smoothToSobolev L K s u⟩
  let c₀ : (B.smoothSections ⧸ P.toLinearMap.range) →ₗ[ℂ]
      (K.SobolevSpace (s - m) ⧸ T.range) :=
    P.toLinearMap.range.mapQ T.range (K.smoothToSobolev (s - m)) hrange
  have hcinj : Function.Injective c₀ := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
    change T.range.mkQ (K.smoothToSobolev (s - m) v) = 0 at hz
    obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero T.range).mp hz
    obtain ⟨w, _, hPw⟩ := hlift u v hu
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hPw⟩
  have hcsurj : Function.Surjective c₀ := by
    intro z
    obtain ⟨u, rfl⟩ := T.range.mkQ_surjective z
    -- The right residual represents each completed cokernel class by an actual smooth section.
    obtain ⟨w, hw⟩ := exists_smooth_lift_of_isAtlasSmoothingOperator K K
      (P.toLinearMap.comp Q.toLinearMap - LinearMap.id) hright
      (s - m) (s - m) R' hR' u
    refine ⟨P.toLinearMap.range.mkQ (-w), ?_⟩
    have hres : T (S u) - u = R' u := DFunLike.congr_fun hright_eq u
    have hzero : T.range.mkQ (T (S u)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨S u, rfl⟩
    change T.range.mkQ (K.smoothToSobolev (s - m) (-w)) = T.range.mkQ u
    rw [map_neg, hw, ← hres, map_neg, map_sub, hzero, zero_sub, neg_neg]
  refine ⟨LinearEquiv.ofBijective e₀ ⟨heinj, hesurj⟩,
    LinearEquiv.ofBijective c₀ ⟨hcinj, hcsurj⟩, ?_, ?_⟩
  · intro u
    rfl
  · intro v
    rfl

/-- The Fredholm index is the original finite smooth-kernel minus smooth-cokernel index. -/
theorem index_sobolevExtension_of_homogeneous (s : ℝ) :
    FiniteDimensional ℂ P.toLinearMap.ker ∧
      FiniteDimensional ℂ (B.smoothSections ⧸ P.toLinearMap.range) ∧
      (P.sobolevExtension L K s).index = P.toLinearMap.index := by
  -- Finiteness is established in the completed spaces and transported by the natural maps.
  have hFred := P.isFredholm_sobolevExtension_of_homogeneous L K g a hs hh hP hi s
  obtain ⟨e, c, _, _⟩ :=
    P.exists_kernel_cokernel_sobolevEquiv_of_homogeneous L K g a hs hh hP hi s
  let : FiniteDimensional ℂ (P.sobolevExtension L K s).ker := hFred.finite_ker
  let : FiniteDimensional ℂ
      (K.SobolevSpace (s - m) ⧸ (P.sobolevExtension L K s).range) := hFred.finite_coker
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
    FiniteDimensional.of_injective c.toLinearMap c.injective, ?_⟩
  -- Both dimensions refer to the same smooth and Sobolev actions fixed above.
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    ← e.finrank_eq, ← c.finrank_eq]

end AtlasPseudodifferentialOperator

end AtiyahSinger

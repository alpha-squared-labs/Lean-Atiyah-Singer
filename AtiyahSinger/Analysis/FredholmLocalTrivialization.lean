/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComplementQuotient

/-!
# Fredholm charts and finite-dimensional reduction

Public module ID: M0644.

The quotient-family homeomorphism in ComplementQuotient implements the
fixed-complement construction of SG III.7 Lemma 7.2. Here the hypotheses at a
Fredholm base operator produce
the required chart. Its finite-dimensional reduction computes kernels, cokernels,
and indices without treating those possibly jumping kernels as vector bundles.
The reduction is induced by x ↦ projection(T)(Tx) on E/V; no arbitrary finite
matrix or index formula is placed inside a carrier.
Sources: SG III.7 (7.1)--(7.4), pp.202--203. The explicit reduction maps are
project deductions from the same fixed-complement argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (V : Submodule ℂ E) (W : Submodule ℂ F)

variable {V W} (T : E →L[ℂ] F) (hT : T ∈ complementChartDomain V W)

include hT in
/-- The composite projection of Tx vanishes on the fixed domain subspace. -/
theorem le_ker_complementReduction : V ≤ ((complementProjection V W T).comp T).ker := by
  /- A vector v in V is sent by T to T(V), which the first block
  coordinate annihilates. This is the condition for descending to E/V. -/
  intro v hv
  exact complementProjection_apply_image hT ⟨v, hv⟩

/-- The standard finite-dimensional reduction, before imposing dimension hypotheses. -/
def complementReduction : (E ⧸ V) →L[ℂ] W :=
  V.liftQL ((complementProjection V W T).comp T) (le_ker_complementReduction T hT)

/-- Reduction applies the original T followed by its complement coordinate. -/
theorem complementReduction_mkQ (x : E) :
    complementReduction T hT (V.mkQ x) = complementProjection V W T (T x) := by
  /- Evaluate the continuous quotient lift on the representative x.
  The displayed order of composition is essential to the kernel comparison. -/
  rfl

/-- The original kernel maps isomorphically to the kernel of the reduction. -/
theorem existsUnique_complementKernelEquiv :
    ∃! e : T.ker ≃ₗ[ℂ] (complementReduction T hT).ker,
      ∀ u, (e u).val = V.mkQ (u.val) := by
  /- Send u in ker T to its class modulo V. This is injective because
  T is injective on V. For a class represented by x in the reduced kernel,
  subtract the solution coordinate of Tx from x. The result lies in ker T
  and represents the same class. The prescribed values determine the map uniquely. -/
  -- Restrict the actual quotient map to the original kernel.
  let q : T.ker →ₗ[ℂ] (complementReduction T hT).ker :=
    (V.mkQ.comp T.ker.subtype).codRestrict _ (by
      intro u
      change complementReduction T hT (V.mkQ u.val) = 0
      rw [complementReduction_mkQ, show T u.val = 0 from u.property, map_zero])
  have hqinj : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hclass : V.mkQ u.val = 0 := congrArg Subtype.val hu
    have huV : u.val ∈ V := (Submodule.Quotient.mk_eq_zero V).mp hclass
    have hinj := injective_restrict_of_mem_complementChartDomain hT
    have heq : (⟨u.val, huV⟩ : V) = 0 := hinj (by
      change T u.val = T 0
      rw [map_zero]
      exact u.property)
    apply Subtype.ext
    exact congrArg (fun v : V ↦ (v : E)) heq
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨x, hx⟩ := V.mkQ_surjective z.val
    have hzero : complementProjection V W T (T x) = 0 := by
      rw [← complementReduction_mkQ T hT x, hx]
      exact z.property
    -- Subtracting the solution component puts the representative in ker T.
    let u : T.ker := ⟨x - (complementSolution V W T (T x) : E), by
      change T (x - (complementSolution V W T (T x) : E)) = 0
      rw [map_sub, sub_eq_zero]
      symm
      simpa only [hzero, Submodule.coe_zero, zero_add] using
        complementProjection_add_image_solution hT (T x)⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    change V.mkQ (x - (complementSolution V W T (T x) : E)) = z.val
    rw [map_sub]
    have hsolution : V.mkQ (complementSolution V W T (T x) : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero V).mpr (complementSolution V W T (T x)).property
    rw [hsolution, sub_zero, hx]
  refine ⟨LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩, ?_, ?_⟩
  · intro u
    rfl
  · intro e he
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    exact he u

/-- The kernel comparison induced by the actual quotient map E → E/V. -/
def complementKernelEquiv : T.ker ≃ₗ[ℂ] (complementReduction T hT).ker :=
  Classical.choose (existsUnique_complementKernelEquiv T hT).exists

/-- The selected kernel comparison retains the original quotient class. -/
theorem complementKernelEquiv_apply (u : T.ker) :
    (complementKernelEquiv T hT u).val = V.mkQ (u.val) := by
  /- Extract the uniquely specified quotient formula from the chosen
  kernel equivalence. No identification by dimensions alone is used. -/
  exact Classical.choose_spec (existsUnique_complementKernelEquiv T hT).exists u

/-- Inclusion of W induces the natural cokernel comparison. -/
theorem existsUnique_complementCokernelEquiv :
    ∃! e : (W ⧸ (complementReduction T hT).range) ≃ₗ[ℂ] (F ⧸ T.range),
      ∀ w : W, e ((complementReduction T hT).range.mkQ w) = T.range.mkQ (w : F) := by
  /- The image of a reduced vector equals Tx modulo T(V), hence is zero
  modulo range T. Inclusion of W therefore descends. Every y differs from
  its W coordinate by a vector in range T, proving surjectivity. If w=Tx,
  projection recovers w as a reduced image, proving injectivity and uniqueness. -/
  let P : Submodule ℂ W := (complementReduction T hT).range
  let q : W →ₗ[ℂ] (F ⧸ T.range) := T.range.mkQ.comp W.subtype
  -- Inclusion kills precisely the reduced image, so it descends to its quotient.
  have hkill : P ≤ q.ker := by
    rintro w ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := V.mkQ_surjective z
    change T.range.mkQ (complementReduction T hT (V.mkQ x) : F) = 0
    rw [complementReduction_mkQ]
    apply (Submodule.Quotient.mk_eq_zero T.range).mpr
    refine ⟨x - (complementSolution V W T (T x) : E), ?_⟩
    have hdecomp := complementProjection_add_image_solution hT (T x)
    rw [map_sub]
    exact (eq_sub_iff_add_eq.mpr hdecomp).symm
  let qbar : (W ⧸ P) →ₗ[ℂ] (F ⧸ T.range) := P.liftQ q hkill
  have hqinj : Function.Injective qbar := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨w, rfl⟩ := P.mkQ_surjective z
    have hw : (w : F) ∈ T.range := (Submodule.Quotient.mk_eq_zero T.range).mp hz
    obtain ⟨x, hx⟩ := hw
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    refine ⟨V.mkQ x, ?_⟩
    change complementReduction T hT (V.mkQ x) = w
    rw [complementReduction_mkQ]
    change T x = (w : F) at hx
    rw [hx]
    exact complementProjection_subtype hT w
  have hqsurj : Function.Surjective qbar := by
    intro z
    obtain ⟨y, rfl⟩ := T.range.mkQ_surjective z
    refine ⟨P.mkQ (complementProjection V W T y), ?_⟩
    change T.range.mkQ (complementProjection V W T y : F) = T.range.mkQ y
    -- The discarded solution term is an actual image of the same operator T.
    have hsolution : T.range.mkQ (T (complementSolution V W T y)) = 0 :=
      (Submodule.Quotient.mk_eq_zero T.range).mpr ⟨_, rfl⟩
    have hdecomp := congrArg T.range.mkQ (complementProjection_add_image_solution hT y)
    simpa only [map_add, hsolution, add_zero] using hdecomp
  refine ⟨LinearEquiv.ofBijective qbar ⟨hqinj, hqsurj⟩, ?_, ?_⟩
  · intro w
    rfl
  · intro e he
    apply LinearEquiv.ext
    intro z
    obtain ⟨w, rfl⟩ := P.mkQ_surjective z
    exact he w

/-- The natural cokernel equivalence induced by inclusion of the fixed complement. -/
def complementCokernelEquiv :
    (W ⧸ (complementReduction T hT).range) ≃ₗ[ℂ] (F ⧸ T.range) :=
  Classical.choose (existsUnique_complementCokernelEquiv T hT).exists

/-- The selected cokernel comparison has the natural inclusion formula. -/
theorem complementCokernelEquiv_mkQ (w : W) :
    complementCokernelEquiv T hT ((complementReduction T hT).range.mkQ w) =
      T.range.mkQ (w : F) := by
  /- Apply the selected equivalence specification to w. Both sides are
  actual module quotient classes with their original range submodules. -/
  exact Classical.choose_spec (existsUnique_complementCokernelEquiv T hT).exists w

/-- Reduction preserves the original algebraic index. -/
theorem index_eq_complementReduction :
    T.toLinearMap.index = (complementReduction T hT).toLinearMap.index := by
  /- The specified kernel and cokernel equivalences identify both dimension
  terms in the algebraic index. This identity does not assert closed range
  or finiteness; those properties require the separate hypotheses below. -/
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    (complementKernelEquiv T hT).finrank_eq, ← (complementCokernelEquiv T hT).finrank_eq]

include hT in
/-- A finite-dimensional complement forces the full image of T to be closed. -/
theorem isClosed_range_of_mem_complementChartDomain [FiniteDimensional ℂ W] :
    IsClosed (T.range : Set F) := by
  /- The full range is the inverse image, under the continuous complement
  projection, of the reduction range. That range is a subspace of finite-
  dimensional W and is closed. The block decomposition proves the inverse-image equality. -/
  have hrange : (T.range : Set F) =
      (complementProjection V W T) ⁻¹' ((complementReduction T hT).range : Set W) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨V.mkQ x, complementReduction_mkQ T hT x⟩
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := V.mkQ_surjective z
      change complementReduction T hT (V.mkQ x) = complementProjection V W T y at hz
      rw [complementReduction_mkQ] at hz
      -- Matching complement coordinates leave only a difference in T(V).
      refine ⟨x - (complementSolution V W T (T x) : E) +
        (complementSolution V W T y : E), ?_⟩
      rw [map_add, map_sub]
      have hx := complementProjection_add_image_solution hT (T x)
      have hy := complementProjection_add_image_solution hT y
      have hsubtract : T x - T (complementSolution V W T (T x)) =
          (complementProjection V W T (T x) : F) := (eq_sub_iff_add_eq.mpr hx).symm
      change T x - T (complementSolution V W T (T x)) +
        T (complementSolution V W T y) = y
      rw [hsubtract, hz]
      exact hy
  rw [hrange]
  exact (complementReduction T hT).range.closed_of_finiteDimensional.preimage
    (complementProjection V W T).continuous

include hT in
/-- With two finite-dimensional ends, the chart index is their dimension difference. -/
theorem index_eq_finrank_quotient_sub_finrank_complement
    [FiniteDimensional ℂ (E ⧸ V)] [FiniteDimensional ℂ W] :
    T.toLinearMap.index = (Module.finrank ℂ (E ⧸ V) : ℤ) - Module.finrank ℂ W := by
  /- The reduction is a map between the fixed finite-dimensional spaces
  E/V and W. Rank-nullity cancels its rank from its kernel-minus-cokernel
  dimension. Transfer the resulting index through the natural equivalences. -/
  rw [index_eq_complementReduction T hT]
  exact (complementReduction T hT).toLinearMap.index_eq_of_finiteDimensional

end AtiyahSinger

namespace AtiyahSinger

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [hE : CompleteSpace E] [hF : CompleteSpace F]

include hE hF

/-- The image of a closed finite-codimension subspace has finite orthogonal complement. -/
theorem finiteDimensional_orthogonal_image_of_isFredholm (T₀ : E →L[ℂ] F) (hT₀ : T₀.IsFredholm)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hVfin : FiniteDimensional ℂ (E ⧸ V)) :
    FiniteDimensional ℂ (V.map T₀.toLinearMap)ᗮ := by
  /- Modulo ker T₀ the Fredholm map is a Banach isomorphism onto its closed
  range. The image of V has finite codimension there; adding the finite
  original cokernel gives finite codimension in F. Its orthogonal complement is finite. -/
  have : FiniteDimensional ℂ (E ⧸ V) := hVfin
  have : FiniteDimensional ℂ (F ⧸ T₀.range) := hT₀.finite_coker
  have : FiniteDimensional ℂ (F ⧸ V.map T₀.toLinearMap) := inferInstance
  -- Restriction along a closed finite-codimensional inclusion is still Fredholm.
  have : CompleteSpace V := hV.completeSpace_coe
  have hrestriction := hT₀.comp (Submodule.isFredholm_subtypeL hV)
  have hclosed : IsClosed (V.map T₀.toLinearMap : Set F) := by
    have h := ((isFredholm_iff_closed_range_finite (T₀.comp V.subtypeL)).mp hrestriction).1
    simpa only [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using h
  -- The actual quotient identifies with the orthogonal complement of this closed image.
  have : CompleteSpace (V.map T₀.toLinearMap) := hclosed.completeSpace_coe
  exact (V.map T₀.toLinearMap).quotientEquivOrthogonal.toLinearEquiv.finiteDimensional

/-- The SG hypotheses put the base operator in its actual block chart. -/
theorem mem_complementChartDomain_orthogonal_of_isFredholm (T₀ : E →L[ℂ] F) (hT₀ : T₀.IsFredholm)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hVfin : FiniteDimensional ℂ (E ⧸ V)) (hdisj : Disjoint V T₀.ker) :
    T₀ ∈ complementChartDomain V (V.map T₀.toLinearMap)ᗮ := by
  /- The restriction T₀|V is injective. Since V is closed and finite-
  codimensional, its image under a Fredholm map is closed. Orthogonal
  decomposition of F gives a bijective block operator W × V → F.
  Both factors are complete; the bounded inverse theorem gives a continuous inverse. -/
  have : FiniteDimensional ℂ (E ⧸ V) := hVfin
  have : CompleteSpace V := hV.completeSpace_coe
  let P := V.map T₀.toLinearMap
  have hrestriction := hT₀.comp (Submodule.isFredholm_subtypeL hV)
  have hclosed : IsClosed (P : Set F) := by
    simpa only [P, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using hrestriction.isClosed_range
  have : CompleteSpace P := hclosed.completeSpace_coe
  have : CompleteSpace Pᗮ := P.isClosed_orthogonal.completeSpace_coe
  let b := complementBlock V Pᗮ T₀
  -- Disjointness with ker T₀ and the orthogonal direct sum give block injectivity.
  have hinj : b.toLinearMap.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨w, v⟩ hv
    change (w : F) + T₀ v = 0 at hv
    have hwP : (w : F) ∈ P := by
      have heq : (w : F) = -T₀ v := eq_neg_of_add_eq_zero_left hv
      rw [heq]
      exact P.neg_mem ⟨v, v.property, rfl⟩
    have hw : (w : F) = 0 :=
      Submodule.disjoint_def.mp P.orthogonal_disjoint _ hwP w.property
    have hvker : (v : E) ∈ T₀.ker := by
      change T₀ v = 0
      simpa only [hw, zero_add] using hv
    have hvzero : (v : E) = 0 := Submodule.disjoint_def.mp hdisj _ v.property hvker
    apply Prod.ext
    · exact Subtype.ext hw
    · exact Subtype.ext hvzero
  -- Every target vector decomposes into the same image P and its orthogonal complement.
  have hsurj : b.toLinearMap.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    have hy : y ∈ P ⊔ Pᗮ := by rw [P.isCompl_orthogonal.sup_eq_top]; trivial
    obtain ⟨p, hp, w, hw, hy⟩ := Submodule.mem_sup.mp hy
    obtain ⟨v, hv, rfl⟩ := hp
    refine ⟨(⟨w, hw⟩, ⟨v, hv⟩), ?_⟩
    change w + T₀ v = y
    rw [add_comm]
    exact hy
  -- The fixed block domain and target are Banach, so its inverse is continuous.
  exact ⟨ContinuousLinearEquiv.ofBijective b hinj hsurj, rfl⟩

/-- Every operator in a finite-complement chart is Fredholm. -/
theorem isFredholm_of_mem_complementChartDomain (V : Submodule ℂ E) (W : Submodule ℂ F)
    [FiniteDimensional ℂ (E ⧸ V)] [FiniteDimensional ℂ W]
    (T : E →L[ℂ] F) (hT : T ∈ complementChartDomain V W) : T.IsFredholm := by
  /- The reduction kernel and cokernel are finite-dimensional. Transfer
  them by the natural equivalences, and use closedness of the full range
  from the projection argument. Apply the Hilbert Fredholm characterization. -/
  apply (isFredholm_iff_closed_range_finite T).mpr
  refine ⟨isClosed_range_of_mem_complementChartDomain T hT, ?_, ?_⟩
  · exact (complementKernelEquiv T hT).symm.finiteDimensional
  · exact (complementCokernelEquiv T hT).finiteDimensional

-- Keep the original Hilbert-space signature; the algebraic index calculation is stronger.
set_option linter.unusedSectionVars false in
/-- The index is constant on an entire fixed finite-complement chart. -/
theorem index_eq_of_mem_complementChartDomain (V : Submodule ℂ E) (W : Submodule ℂ F)
    [FiniteDimensional ℂ (E ⧸ V)] [FiniteDimensional ℂ W]
    (T S : E →L[ℂ] F) (hT : T ∈ complementChartDomain V W)
    (hS : S ∈ complementChartDomain V W) : T.index = S.index := by
  /- Both maps are Fredholm by the preceding theorem. Their indices equal
  the same fixed integer dim(E/V)-dim(W), even if their kernel dimensions
  differ. No connectedness assumption on the whole block chart is required. -/
  rw [show T.index = T.toLinearMap.index from rfl,
    show S.index = S.toLinearMap.index from rfl,
    index_eq_finrank_quotient_sub_finrank_complement T hT,
    index_eq_finrank_quotient_sub_finrank_complement S hS]

end Hilbert

end AtiyahSinger

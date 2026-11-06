/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix

/-!
# Ellipticity from an actual symbolic parametrix

Public module ID: M0850.

A symbol with a two-sided inverse modulo symbols of negative order satisfies
its original quantitative high-frequency inverse bound. This is the converse
parametrix criterion in SG III.4, used to transport ellipticity through smooth
bundle isomorphisms. The estimates concern the specified symbols and norms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff Topology

/-- A symbolic inverse with lower-order errors gives the original inverse bound. -/
theorem isEllipticFullSymbol_of_symbolic_inverse {n r q : ℕ} {m : ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (a : SymbolFunction n r q) (b : SymbolFunction n q r)
    (hb : IsSymbol U (-m) b)
    (hl : IsSymbol U (-1) (fun x ξ ↦
      (b x ξ).comp (a x ξ) - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))))
    (hr : IsSymbol U (-1) (fun x ξ ↦
      (a x ξ).comp (b x ξ) - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q)))) :
    IsEllipticFullSymbol U m a := by
  intro K hKU hK
  obtain ⟨B, hB, hbnd⟩ := hb.2 K hKU hK 0 0
  obtain ⟨L, hL, hlbnd⟩ := hl.2 K hKU hK 0 0
  obtain ⟨R, hR, hrbnd⟩ := hr.2 K hKU hK 0 0
  refine ⟨1 + 2 * (L + R), 2 * B, by positivity, by positivity, ?_⟩
  intro x hx ξ hξ
  have hweight : 0 < 1 + ‖ξ‖ := by positivity
  have hbound : ‖b x ξ‖ ≤ B * (1 + ‖ξ‖) ^ (-m) := by
    simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
      using hbnd x hx ξ
  have hleft :
      ‖(b x ξ).comp (a x ξ) - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))‖ ≤
        1 / 2 := by
    have h := hlbnd x hx ξ
    simp only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at h
    rw [Real.rpow_neg_one, ← div_eq_mul_inv] at h
    exact h.trans ((div_le_iff₀ hweight).mpr (by linarith))
  have hright :
      ‖(a x ξ).comp (b x ξ) - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q))‖ ≤
        1 / 2 := by
    have h := hrbnd x hx ξ
    simp only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at h
    rw [Real.rpow_neg_one, ← div_eq_mul_inv] at h
    exact h.trans ((div_le_iff₀ hweight).mpr (by linarith))
  -- The left error controls every input vector in terms of its actual image.
  have hlower (v : EuclideanSpace ℂ (Fin r)) :
      ‖v‖ ≤ 2 * ‖b x ξ‖ * ‖a x ξ v‖ := by
    have hdecomp : v = b x ξ (a x ξ v) -
        ((b x ξ).comp (a x ξ) - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))) v := by simp
    have hnorm := norm_sub_le (b x ξ (a x ξ v))
      (((b x ξ).comp (a x ξ) -
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))) v)
    have herr := ((b x ξ).comp (a x ξ) -
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))).le_opNorm v
    have hmain := (b x ξ).le_opNorm (a x ξ v)
    rw [← hdecomp] at hnorm
    have hsmall := mul_le_mul_of_nonneg_right hleft (norm_nonneg v)
    nlinarith
  have hinj : Function.Injective (a x ξ) := by
    apply (a x ξ).ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hz : a x ξ v = 0 := hv
    have h := hlower v
    rw [hz, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg v))
  -- The right error makes the output endomorphism injective, hence surjective.
  let T := (a x ξ).comp (b x ξ)
  have hTinj : Function.Injective T := by
    apply T.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hz : T v = 0 := hv
    have h := (T - ContinuousLinearMap.id ℂ _).le_opNorm v
    have hs := mul_le_mul_of_nonneg_right hright (norm_nonneg v)
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      hz, zero_sub, norm_neg] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  have hTsurj := (LinearMap.injective_iff_surjective (f := T.toLinearMap)).mp hTinj
  have hsurj : Function.Surjective (a x ξ) := by
    intro v
    obtain ⟨w, hw⟩ := hTsurj v
    exact ⟨b x ξ w, hw⟩
  have hi : (a x ξ).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (a x ξ).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      rfl⟩
  refine ⟨hi, ?_⟩
  -- Apply the same lower estimate to the inverse, retaining the order weight.
  have hn : ‖(a x ξ).inverse‖ ≤ 2 * ‖b x ξ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simpa only [hi.self_apply_inverse] using hlower ((a x ξ).inverse v)
  exact hn.trans (by nlinarith [hbound])

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- An original global symbolic parametrix gives quantitative ellipticity in every frame. -/
theorem isEllipticFullGlobalSymbol_of_symbolic_inverse {m : ℝ}
    (a : GlobalSymbolFunction (n := n) E F) (b : GlobalSymbolFunction (n := n) F E)
    (hb : IsGlobalSymbol (r := q) (q := r) F E (-m) b)
    (hl : IsGlobalSymbol (r := r) (q := r) E E (-1)
      (globalSymbolComp b a - globalSymbolId E))
    (hr : IsGlobalSymbol (r := q) (q := q) F F (-1)
      (globalSymbolComp a b - globalSymbolId F)) :
    IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a := by
  intro c hc e f he hf
  let U := symbolChartDomain E F c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have hUE : U ⊆ symbolChartDomain E E c e e := fun x hx ↦ ⟨hx.1, hx.1.2⟩
  have hUF : U ⊆ symbolChartDomain F F c f f := fun x hx ↦ ⟨⟨hx.1.1, hx.2⟩, hx.2⟩
  have hUFE : U ⊆ symbolChartDomain F E c f e :=
    fun x hx ↦ ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
  -- Restrict to the same frame overlap and transport its full derivative estimates.
  have hrestrict {r' q' : ℕ} {W : Set (EuclideanSpace ℝ (Fin n))}
      (d d' : SymbolFunction n r' q') (hd : IsSymbol W (-1) d)
      (hUW : U ⊆ W) (heq : ∀ x ∈ U, ∀ ξ, d x ξ = d' x ξ) :
      IsSymbol U (-1) d' := by
    refine ⟨(hd.1.mono (Set.prod_mono hUW Set.Subset.rfl)).congr
      (fun z hz ↦ (heq z.1 hz.1 z.2).symm), ?_⟩
    intro K hKU hK i j
    obtain ⟨C, hC, hbound⟩ := hd.2 K (hKU.trans hUW) hK i j
    refine ⟨C, hC, fun x hx ξ ↦ ?_⟩
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (d y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (d' y) ξ) := by
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      rw [funext (heq y hy)]
    have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← hder]
    exact hbound x hx ξ
  apply isEllipticFullSymbol_of_symbolic_inverse
    (globalSymbolInChart E F a c e f) (globalSymbolInChart F E b c f e)
  · refine ⟨(hb c hc f e).1.mono (Set.prod_mono hUFE Set.Subset.rfl), ?_⟩
    intro K hKU hK i j
    exact (hb c hc f e).2 K (hKU.trans hUFE) hK i j
  · apply hrestrict _ _ (hl c hc e e) hUE
    intro x hx ξ
    have hcomp := globalSymbolInChart_globalSymbolComp b a c e f e x ξ hx.2
    have hid : globalSymbolInChart E E (globalSymbolId E) c e e x ξ =
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r)) := by
      apply ContinuousLinearMap.ext
      intro v
      exact e.continuousLinearMapAt_symmL (R := ℂ) hx.1.2 v
    have hsub : globalSymbolInChart E E (globalSymbolComp b a - globalSymbolId E)
        c e e x ξ = globalSymbolInChart E E (globalSymbolComp b a) c e e x ξ -
          globalSymbolInChart E E (globalSymbolId E) c e e x ξ := by
      ext v
      simp [globalSymbolInChart]
    rw [hsub, hcomp, hid]
    rfl
  · apply hrestrict _ _ (hr c hc f f) hUF
    intro x hx ξ
    have hcomp := globalSymbolInChart_globalSymbolComp a b c f e f x ξ hx.1.2
    have hid : globalSymbolInChart F F (globalSymbolId F) c f f x ξ =
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q)) := by
      apply ContinuousLinearMap.ext
      intro v
      exact f.continuousLinearMapAt_symmL (R := ℂ) hx.2 v
    have hsub : globalSymbolInChart F F (globalSymbolComp a b - globalSymbolId F)
        c f f x ξ = globalSymbolInChart F F (globalSymbolComp a b) c f f x ξ -
          globalSymbolInChart F F (globalSymbolId F) c f f x ξ := by
      ext v
      simp [globalSymbolInChart]
    rw [hsub, hcomp, hid]
    rfl

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

/- Isolate the order equality before specializing the same principal representatives. -/
private theorem principal_remainder_of_smoothing {l : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l)
    (hl : l = 0) (a : globalSymbolSpace (n := n) (r := r) (q := r) E E l)
    (ha : P.principalSymbol = globalPrincipalSymbolClass E E l a)
    (hP : IsSmoothingOperator μ (P.toLinearMap - LinearMap.id)) :
    IsGlobalSymbol (r := r) (q := r) E E (-1) (a.val - globalSymbolId E) := by
  subst l
  have hσ : P.principalSymbol = (PseudodifferentialOperator.id
      (n := n) (r := r) (E := E) μ).principalSymbol := by
    apply (P.principalSymbol_eq_iff _).mpr
    simpa only [zero_sub, PseudodifferentialOperator.id] using
      hP.isPseudodifferentialOperator (-1) _
  rw [ha, PseudodifferentialOperator.principalSymbol_id] at hσ
  simpa only [zero_sub, globalIdentitySymbol] using (globalPrincipalSymbolClass_eq_iff E E 0 a
    (globalIdentitySymbol (n := n) (r := r) (E := E))).mp hσ

include hM hT2 hSC hC hE hF hμ

/-- A two-sided order-zero parametrix forces full-symbol ellipticity. -/
theorem PseudodifferentialOperator.isElliptic_of_isParametrix
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ 0)
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) : P.IsElliptic := by
  -- Choose representatives of the actual two principal classes.
  obtain ⟨a, ha⟩ := globalPrincipalSymbolClass_surjective E F 0 P.principalSymbol
  obtain ⟨b, hb⟩ := globalPrincipalSymbolClass_surjective F E 0 Q.principalSymbol
  -- Keep the composition order and both original representative values during transport.
  have hlower := principal_remainder_of_smoothing (Q.comp P) (zero_add (0 : ℝ))
    (globalSymbolSpaceComp b a) (by
      rw [PseudodifferentialOperator.principalSymbol_comp, ← ha, ← hb,
        globalPrincipalSymbolComp_class]) hQ.1
  have hrlower := principal_remainder_of_smoothing (P.comp Q) (zero_add (0 : ℝ))
    (globalSymbolSpaceComp a b) (by
      rw [PseudodifferentialOperator.principalSymbol_comp, ← ha, ← hb,
        globalPrincipalSymbolComp_class]) hQ.2
  refine ⟨a, ha.symm, ?_⟩
  exact isEllipticFullGlobalSymbol_of_symbolic_inverse a.val b.val
    (by rw [neg_zero]; exact b.property) hlower hrlower

end AtiyahSinger

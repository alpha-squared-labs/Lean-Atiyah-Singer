/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedHodgePrincipalAssembly
public import AtiyahSinger.Geometry.DifferentialFormExteriorAdjoint

/-!
# A native first-order realization of the original positive Hodge operator

Public module ID: M0858.

The finite even and odd form bundles retain the original total-form grading,
pointwise coordinates and normalized metrics. Their adjacent-degree blocks are
the actual exterior derivatives and their actual metric formal adjoints. Finite
matrix assembly realizes precisely the already defined positive Hodge operator
as an order-one PDO, with its actual homogeneous symbol on those same witnesses.
The independently proved normalized wedge/contraction adjunction fixes the
lowering term, and no additional symbol or adjunction hypothesis is assumed.

Source: Lawson--Michelsohn, Spin Geometry, II.5 and III.5, with the native finite
bundle and operator transport spelled out as an implementation supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators DirectSum Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] (g : SmoothTangentMetric (n := n) (M := M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise principal map of d plus its metric adjoint, at the specified metric covector. -/
def differentialFormHodgeSymbolComponent (p q : ℕ) (x : M)
    (v : EuclideanSpace ℝ (Fin n))
    (α : DifferentialFormFiber (n := n) p x) : DifferentialFormFiber (n := n) q x :=
  if hraise : q = p + 1 then by
    subst q
    exact Complex.I • ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n)) (F := ℂ) (n := p) ((g.inner x v).smulRight α)
  else if hlower : p = q + 1 then by
    subst p
    exact -Complex.I • α.curryLeft v
  else 0

set_option maxHeartbeats 1800000 in
-- Retain dependent degree coordinates, the two native sums and the original total operator.
set_option maxRecDepth 6000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original positive Hodge operator is an actual first-order PDO on its finite form bundles. -/
theorem exists_positiveHodgeDirac_nativeRealization :
    letI : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
      g.isSmoothPositiveMeasure_riemannianVolume
    ∃ E F : SmoothFiniteComplexBundle (n := n) M,
    ∃ e : ∀ x, ((p : {p : Fin (n + 1) // Even p.val}) →
        DifferentialFormFiber (n := n) p.val.val x) ≃ₗ[ℂ] E.Fiber x,
    ∃ f : ∀ x, ((p : {p : Fin (n + 1) // Odd p.val}) →
        DifferentialFormFiber (n := n) p.val.val x) ≃ₗ[ℂ] F.Fiber x,
    ∃ Φ : evenSmoothDifferentialForms (n := n) (M := M) ≃ₗ[ℂ]
        smoothSections (n := n) (r := E.rank) E.Fiber,
      (∀ u x, (Φ u).val x = e x (fun p ↦ (u.val p.val.val).val x)) ∧
    ∃ Ψ : oddSmoothDifferentialForms (n := n) (M := M) ≃ₗ[ℂ]
        smoothSections (n := n) (r := F.rank) F.Fiber,
      (∀ u x, (Ψ u).val x = f x (fun p ↦ (u.val p.val.val).val x)) ∧
    ∃ h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber,
    ∃ k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber,
      (∀ x a b, h.pairing x (e x a) (e x b) =
        ∑ p, differentialFormInner g p.val.val x (a p) (b p)) ∧
      (∀ x a b, k.pairing x (f x a) (f x b) =
        ∑ p, differentialFormInner g p.val.val x (a p) (b p)) ∧
    ∃ P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber g.riemannianVolume 1,
      (∀ u, P.toLinearMap (Φ u) = Ψ (positiveHodgeDirac g u)) ∧
    ∃ b : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber 1,
      (∀ (x : M) (v : EuclideanSpace ℝ (Fin n)) u,
        b.val x (g.inner x v) (e x u) = f x (fun q ↦ ∑ p,
          differentialFormHodgeSymbolComponent g p.val.val q.val.val x v (u p))) ∧
      ∀ R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber,
        P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 1
          (R.regularizedSymbol 1 b.val b.property.1 b.property.2) := by
  classical
  have hcontraction := differentialFormInner_alternatizeUncurryFin g
  let : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
    g.isSmoothPositiveMeasure_riemannianVolume
  let EvenDegree := {p : Fin (n + 1) // Even p.val}
  let OddDegree := {p : Fin (n + 1) // Odd p.val}
  -- Choose one actual degreewise family containing both d and its selected adjoint.
  obtain ⟨rank, core, coordinates, hdata⟩ := exists_smoothFormDifferential_bundleRealization g
  let normedGroup (p : ℕ) : ∀ x, NormedAddCommGroup ((core p).Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin (rank p))))
  let normedSpace (p : ℕ) : ∀ x, NormedSpace ℂ ((core p).Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin (rank p))))
  obtain ⟨hSmooth, _, _, sectionEquiv, hsection, metric, hmetric, D, hD, hDsymbol, hAdj⟩ := hdata
  let smoothBundle (p : ℕ) : IsSmoothComplexBundle (n := n) (r := rank p) (core p).Fiber :=
    hSmooth p
  let A (p : ℕ) : SmoothFiniteComplexBundle (n := n) M :=
    { rank := rank p
      Fiber := (core p).Fiber }
  have hsectionInv (p : ℕ) (u : smoothSections (n := n) (r := rank p) (core p).Fiber)
      (x : M) : ((sectionEquiv p).symm u).val x = (coordinates p).symm (u.val x) := by
    have h := hsection p ((sectionEquiv p).symm u) x
    rw [(sectionEquiv p).apply_symm_apply] at h
    exact ((coordinates p).symm_apply_apply _).symm.trans (congrArg (coordinates p).symm h.symm)
  -- Both finite native bundles keep all original homogeneous coordinates and pairings.
  obtain ⟨r, Z, c, hZ⟩ :=
    exists_finiteDifferentialForm_bundleModel g (fun p : EvenDegree ↦ p.val.val)
  let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin r)))
  let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin r)))
  obtain ⟨hZS, _, _, Φ₀, hΦ₀, h, hh⟩ := hZ
  let : IsSmoothComplexBundle (n := n) (r := r) Z.Fiber := hZS
  obtain ⟨q, Y, d, hY⟩ :=
    exists_finiteDifferentialForm_bundleModel g (fun p : OddDegree ↦ p.val.val)
  let : ∀ x, NormedAddCommGroup (Y.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin q)))
  let : ∀ x, NormedSpace ℂ (Y.Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin q)))
  obtain ⟨hYS, _, _, Ψ₀, hΨ₀, k, hk⟩ := hY
  let : IsSmoothComplexBundle (n := n) (r := q) Y.Fiber := hYS
  let E : SmoothFiniteComplexBundle (n := n) M := { rank := r, Fiber := Z.Fiber }
  let F : SmoothFiniteComplexBundle (n := n) M := { rank := q, Fiber := Y.Fiber }
  obtain ⟨⟨evenEquiv, hEvenEquiv⟩, ⟨oddEquiv, hOddEquiv⟩⟩ :=
    exists_finiteParityDifferentialForm_equiv (n := n) (M := M)
  let Φ := evenEquiv.trans Φ₀
  let Ψ := oddEquiv.trans Ψ₀
  let e (x : M) : ((p : EvenDegree) → DifferentialFormFiber (n := n) p.val.val x) ≃ₗ[ℂ] E.Fiber x :=
    c.toLinearEquiv
  let f (x : M) : ((p : OddDegree) → DifferentialFormFiber (n := n) p.val.val x) ≃ₗ[ℂ] F.Fiber x :=
    d.toLinearEquiv
  let Φsum := (LinearEquiv.piCongrRight (fun p : EvenDegree ↦
    (sectionEquiv p.val.val).symm)).trans Φ₀
  let Ψsum := (LinearEquiv.piCongrRight (fun p : OddDegree ↦
    (sectionEquiv p.val.val).symm)).trans Ψ₀
  let esum (x : M) : ((p : EvenDegree) → (A p.val.val).Fiber x) ≃ₗ[ℂ] E.Fiber x :=
    (LinearEquiv.piCongrRight (fun p : EvenDegree ↦
      (coordinates p.val.val).symm.toLinearEquiv)).trans (e x)
  let fsum (x : M) : ((p : OddDegree) → (A p.val.val).Fiber x) ≃ₗ[ℂ] F.Fiber x :=
    (LinearEquiv.piCongrRight (fun p : OddDegree ↦
      (coordinates p.val.val).symm.toLinearEquiv)).trans (f x)
  have hΦsum : ∀ u x, (Φsum u).val x = esum x (fun p ↦ (u p).val x) := by
    intro u x
    change (Φ₀ (fun p ↦ (sectionEquiv p.val.val).symm (u p))).val x = _
    rw [hΦ₀]
    apply congrArg c
    funext p
    exact hsectionInv p.val.val (u p) x
  have hΨsum : ∀ u x, (Ψsum u).val x = fsum x (fun p ↦ (u p).val x) := by
    intro u x
    change (Ψ₀ (fun p ↦ (sectionEquiv p.val.val).symm (u p))).val x = _
    rw [hΨ₀]
    apply congrArg d
    funext p
    exact hsectionInv p.val.val (u p) x
  have hΦactual (u : evenSmoothDifferentialForms (n := n) (M := M)) :
      Φ u = Φsum (fun p ↦ sectionEquiv p.val.val (u.val p.val.val)) := by
    apply congrArg Φ₀
    funext p
    exact (hEvenEquiv u p).trans ((sectionEquiv p.val.val).symm_apply_apply _).symm
  have hΨactual (u : oddSmoothDifferentialForms (n := n) (M := M)) :
      Ψ u = Ψsum (fun p ↦ sectionEquiv p.val.val (u.val p.val.val)) := by
    apply congrArg Ψ₀
    funext p
    exact (hOddEquiv u p).trans ((sectionEquiv p.val.val).symm_apply_apply _).symm
  -- Each matrix entry is an original adjacent derivative, its original adjoint, or zero.
  let Dpdo (p : ℕ) : PseudodifferentialOperator (n := n) (r := rank p)
      (q := rank (p + 1)) (core p).Fiber (core (p + 1)).Fiber g.riemannianVolume 1 :=
    ⟨(D p).toLinearMap, by
      simpa only [Nat.cast_one] using
        (D p).isPseudodifferentialOperator (μ := g.riemannianVolume)⟩
  let Qpdo (p : ℕ) : PseudodifferentialOperator (n := n) (r := rank (p + 1))
      (q := rank p) (core (p + 1)).Fiber (core p).Fiber g.riemannianVolume 1 :=
    ⟨((D p).metricFormalAdjoint (μ := g.riemannianVolume)
        (metric p) (metric (p + 1))).toLinearMap, by
      simpa only [Nat.cast_one] using ((D p).metricFormalAdjoint (μ := g.riemannianVolume)
        (metric p) (metric (p + 1))).isPseudodifferentialOperator
          (μ := g.riemannianVolume)⟩
  let edge (p q : ℕ) : PseudodifferentialOperator (n := n) (r := rank p)
      (q := rank q) (core p).Fiber (core q).Fiber g.riemannianVolume 1 :=
    if hraise : q = p + 1 then by
      subst q
      exact Dpdo p
    else if hlower : p = q + 1 then by
      subst p
      exact Qpdo q
    else ⟨0, isPseudodifferentialOperator_zero _ _ _ 1⟩
  -- Identify the adjoint symbol by the same normalized metric, fixing the lowering sign.
  have hQsymbol (p : ℕ) (x : M)
      (v : EuclideanSpace ℝ (Fin n))
      (β : DifferentialFormFiber (n := n) (p + 1) x) :
      ((D p).metricFormalAdjoint (μ := g.riemannianVolume)
        (metric p) (metric (p + 1))).principalSymbol x (g.inner x v) (coordinates (p + 1) β) =
          coordinates p (-Complex.I • β.curryLeft v) := by
    let adj := ((D p).metricFormalAdjoint (μ := g.riemannianVolume)
      (metric p) (metric (p + 1))).principalSymbol x (g.inner x v) (coordinates (p + 1) β)
    let target : (core p).Fiber x := coordinates p (-Complex.I • β.curryLeft v)
    have hpair (w : (core p).Fiber x) :
        (metric p).pairing x w adj = (metric p).pairing x w target := by
      obtain ⟨α, rfl⟩ := (coordinates p).surjective w
      rw [show (metric p).pairing x (coordinates p α) adj =
        (metric (p + 1)).pairing x
          ((D p).principalSymbol x (g.inner x v) (coordinates p α))
          (coordinates (p + 1) β) from
            ((D p).principalSymbol_metricFormalAdjoint_pairing
              (μ := g.riemannianVolume) (metric p) (metric (p + 1))
              x (g.inner x v) (coordinates p α) (coordinates (p + 1) β)).symm]
      rw [hDsymbol]
      have hleft (a b : (core (p + 1)).Fiber x) :
          (metric (p + 1)).pairing x (Complex.I • a) b =
            -Complex.I * (metric (p + 1)).pairing x a b := by
        let : InnerProductSpace.Core ℂ ((core (p + 1)).Fiber x) := (metric (p + 1)).toCore x
        change ((metric (p + 1)).toCore x).inner (Complex.I • a) b = _
        rw [((metric (p + 1)).toCore x).smul_left]
        rw [Complex.conj_I]
        rfl
      have hright (a b : (core p).Fiber x) :
          (metric p).pairing x a (-Complex.I • b) =
            -Complex.I * (metric p).pairing x a b := by
        let : InnerProductSpace.Core ℂ ((core p).Fiber x) := (metric p).toCore x
        exact InnerProductSpace.Core.inner_smul_right a b
      change _ = (metric p).pairing x (coordinates p α)
        (coordinates p (-Complex.I • β.curryLeft v))
      rw [map_smul, hleft, hright, hmetric, hmetric]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      rw [hcontraction]
    apply sub_eq_zero.mp
    apply ((metric p).toCore x).definite
    let : InnerProductSpace.Core ℂ ((core p).Fiber x) := (metric p).toCore x
    change (metric p).pairing x (adj - target) (adj - target) = 0
    rw [show (metric p).pairing x (adj - target) (adj - target) =
      (metric p).pairing x (adj - target) adj -
        (metric p).pairing x (adj - target) target from
          InnerProductSpace.Core.inner_sub_right _ _ _, hpair, sub_self]
  let dsymbol (p : ℕ) : homogeneousGlobalSymbolSpace (n := n) (r := rank p)
      (q := rank (p + 1)) (core p).Fiber (core (p + 1)).Fiber 1 :=
    ⟨(D p).principalSymbolFunction, (D p).isSmoothOffZeroGlobalSymbol_principalSymbolFunction,
      by simpa only [Nat.cast_one] using (D p).isHomogeneousGlobalSymbol_principalSymbolFunction⟩
  let qsymbol (p : ℕ) : homogeneousGlobalSymbolSpace (n := n) (r := rank (p + 1))
      (q := rank p) (core (p + 1)).Fiber (core p).Fiber 1 :=
    ⟨((D p).metricFormalAdjoint (μ := g.riemannianVolume)
        (metric p) (metric (p + 1))).principalSymbolFunction,
      ((D p).metricFormalAdjoint (μ := g.riemannianVolume)
        (metric p) (metric (p + 1))).isSmoothOffZeroGlobalSymbol_principalSymbolFunction,
      by simpa only [Nat.cast_one] using ((D p).metricFormalAdjoint (μ := g.riemannianVolume)
        (metric p) (metric (p + 1))).isHomogeneousGlobalSymbol_principalSymbolFunction⟩
  let asymbol (p q : ℕ) : homogeneousGlobalSymbolSpace (n := n) (r := rank p)
      (q := rank q) (core p).Fiber (core q).Fiber 1 :=
    if hraise : q = p + 1 then by
      subst q
      exact dsymbol p
    else if hlower : p = q + 1 then by
      subst p
      exact qsymbol q
    else 0
  -- Transport the exact real order before comparing dependent principal quotients.
  have principalTransfer (p q : ℕ) (t : ℝ) (ht : t = 1)
      (P₀ : PseudodifferentialOperator (n := n) (r := rank p) (q := rank q)
        (core p).Fiber (core q).Fiber g.riemannianVolume t)
      (a₀ : homogeneousGlobalSymbolSpace (n := n) (r := rank p) (q := rank q)
        (core p).Fiber (core q).Fiber t)
      (P₁ : PseudodifferentialOperator (n := n) (r := rank p) (q := rank q)
        (core p).Fiber (core q).Fiber g.riemannianVolume 1)
      (a₁ : homogeneousGlobalSymbolSpace (n := n) (r := rank p) (q := rank q)
        (core p).Fiber (core q).Fiber 1)
      (hP : P₀.toLinearMap = P₁.toLinearMap) (ha : a₀.val = a₁.val)
      (R : QuantizationPresentation (n := n) (r := rank p) (q := rank q)
        (core p).Fiber (core q).Fiber)
      (hprincipal : P₀.principalSymbol =
        globalPrincipalSymbolClass (core p).Fiber (core q).Fiber t
          (R.regularizedSymbol t a₀.val a₀.property.1 a₀.property.2)) :
      P₁.principalSymbol = globalPrincipalSymbolClass (core p).Fiber (core q).Fiber 1
        (R.regularizedSymbol 1 a₁.val a₁.property.1 a₁.property.2) := by
    subst t
    have haa : a₀ = a₁ := Subtype.ext ha
    subst a₀
    exact (P₁.principalSymbol_eq_of_toLinearMap_eq g.riemannianVolume P₀ hP.symm).trans hprincipal
  have hasymbol (p q : ℕ) (R : QuantizationPresentation (n := n)
      (r := rank p) (q := rank q) (core p).Fiber (core q).Fiber) :
      (edge p q).principalSymbol = globalPrincipalSymbolClass (core p).Fiber (core q).Fiber 1
        (R.regularizedSymbol 1 (asymbol p q).val
          (asymbol p q).property.1 (asymbol p q).property.2) := by
    by_cases hraise : q = p + 1
    · subst q
      simp only [edge, asymbol, dite_eq_left rfl]
      exact principalTransfer p (p + 1) ((1 : ℕ) : ℝ) (Nat.cast_one)
        ((D p).toPseudodifferentialOperator g.riemannianVolume)
        ⟨(D p).principalSymbolFunction, (D p).isSmoothOffZeroGlobalSymbol_principalSymbolFunction,
          (D p).isHomogeneousGlobalSymbol_principalSymbolFunction⟩
        (Dpdo p) (dsymbol p) rfl rfl R
        ((D p).principalSymbol_eq_regularizedSymbol g.riemannianVolume R)
    · by_cases hlower : p = q + 1
      · subst p
        simp only [edge, asymbol, dite_eq_right hraise, dite_true]
        let Q := (D q).metricFormalAdjoint (μ := g.riemannianVolume)
          (metric q) (metric (q + 1))
        exact principalTransfer (q + 1) q ((1 : ℕ) : ℝ) (Nat.cast_one)
          (Q.toPseudodifferentialOperator g.riemannianVolume)
          ⟨Q.principalSymbolFunction, Q.isSmoothOffZeroGlobalSymbol_principalSymbolFunction,
            Q.isHomogeneousGlobalSymbol_principalSymbolFunction⟩
          (Qpdo q) (qsymbol q) rfl rfl R
          (Q.principalSymbol_eq_regularizedSymbol g.riemannianVolume R)
      · simp only [edge, asymbol, dite_eq_right hraise, dite_eq_right hlower]
        change (principalSymbolLinearMap (core p).Fiber (core q).Fiber g.riemannianVolume 1) 0 = _
        rw [map_zero]
        change 0 = globalPrincipalSymbolClass (core p).Fiber (core q).Fiber 1
          (R.regularizedSymbol 1 0 _ _)
        have hz : R.regularizedSymbol 1 0
            (isSmoothOffZeroGlobalSymbol_zero (core p).Fiber (core q).Fiber)
            (isHomogeneousGlobalSymbol_zero (core p).Fiber (core q).Fiber 1) = 0 := by
          let reg : homogeneousGlobalSymbolSpace (n := n) (r := rank p) (q := rank q)
              (core p).Fiber (core q).Fiber 1 →ₗ[ℂ]
              globalSymbolSpace (n := n) (r := rank p) (q := rank q)
                (core p).Fiber (core q).Fiber 1 := {
            toFun a := R.regularizedSymbol 1 a.val a.property.1 a.property.2
            map_add' a b := Subtype.ext (R.regularizedSymbolFunction_add a.val b.val)
            map_smul' z a := Subtype.ext (R.regularizedSymbolFunction_smul z a.val) }
          exact reg.map_zero
        rw [hz, map_zero]
  have hasymbolValue (p q : ℕ) (x : M)
      (v : EuclideanSpace ℝ (Fin n))
      (α : DifferentialFormFiber (n := n) p x) :
      (asymbol p q).val x (g.inner x v) (coordinates p α) =
        coordinates q (differentialFormHodgeSymbolComponent g p q x v α) := by
    by_cases hraise : q = p + 1
    · subst q
      simp only [asymbol, differentialFormHodgeSymbolComponent, dite_eq_left rfl, dite_true]
      change (D p).principalSymbol x (g.inner x v) (coordinates p α) = _
      rw [map_smul]
      exact hDsymbol p x (g.inner x v) α
    · by_cases hlower : p = q + 1
      · subst p
        simp only [asymbol, differentialFormHodgeSymbolComponent,
          dite_eq_right hraise, dite_true]
        exact hQsymbol q x v α
      · simp [asymbol, differentialFormHodgeSymbolComponent, hraise, hlower]
  let lof (p : ℕ) := DirectSum.lof ℂ ℕ (SmoothDifferentialForm (n := n) M) p
  have hedge (p q : ℕ) (u : SmoothDifferentialForm (n := n) M p) :
      (edge p q).toLinearMap (sectionEquiv p u) =
        sectionEquiv q ((totalFormHodgeDirac g (lof p u)) q) := by
    have hsectionZero (j : ℕ) : sectionEquiv j 0 = 0 :=
      (sectionEquiv j).toLinearMap.map_zero
    simp only [lof, totalFormHodgeDirac, LinearMap.add_apply, totalFormExteriorDerivative,
      totalFormCodifferential, DirectSum.toModule_lof, LinearMap.comp_apply]
    cases p with
    | zero =>
        by_cases hq : q = 1
        · subst q
          simpa [edge, Dpdo, DirectSum.lof_eq_of] using hD 0 u
        · simp [edge, hq, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hsectionZero]
    | succ p =>
        by_cases hq : q = (p + 1) + 1
        · subst q
          have hne : p ≠ (p + 1) + 1 := by omega
          simpa [edge, Dpdo, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne,
            Ne.symm hne] using hD (p + 1) u
        · by_cases hqp : q = p
          · subst q
            have hn : ¬p = p + 1 + 1 := by omega
            simpa [edge, hn, Qpdo, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne] using hAdj p u
          · simp [edge, hq, Ne.symm hqp,
              DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hqp, hsectionZero]
  let P := finiteMatrixPseudodifferentialOperator E F
    (fun p : EvenDegree ↦ A p.val.val) (fun q : OddDegree ↦ A q.val.val)
    esum fsum Φsum Ψsum hΦsum hΨsum (fun q p ↦ edge p.val.val q.val.val)
  obtain ⟨b, hb, hPprincipal⟩ := exists_finiteMatrixPseudodifferentialOperator_homogeneous
    E F (fun p : EvenDegree ↦ A p.val.val) (fun q : OddDegree ↦ A q.val.val)
    esum fsum Φsum Ψsum hΦsum hΨsum (fun q p ↦ edge p.val.val q.val.val)
    (fun q p ↦ asymbol p.val.val q.val.val) (fun q p ↦ hasymbol p.val.val q.val.val)
  -- Every original even form is exactly its finite even homogeneous sum.
  have hhigh (p : ℕ) (hp : n < p) (u : SmoothDifferentialForm (n := n) M p) : u = 0 := by
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext_alternating
    intro v hv
    have hcard := Fintype.card_le_of_injective v hv
    simp only [Fintype.card_fin] at hcard
    omega
  have hsum (u : evenSmoothDifferentialForms (n := n) (M := M)) :
      u.val = ∑ p : EvenDegree, lof p.val.val (u.val p.val.val) := by
    apply DFinsupp.ext
    intro q
    change (DirectSum.component ℂ ℕ (SmoothDifferentialForm (n := n) M) q) u.val =
      (DirectSum.component ℂ ℕ (SmoothDifferentialForm (n := n) M) q)
        (∑ p : EvenDegree, lof p.val.val (u.val p.val.val))
    rw [map_sum]
    change u.val q = ∑ p : EvenDegree, (lof p.val.val (u.val p.val.val)) q
    by_cases hq : q < n + 1
    · by_cases he : Even q
      · let p₀ : EvenDegree := ⟨⟨q, hq⟩, he⟩
        rw [Finset.sum_eq_single p₀]
        · simp [lof, p₀]
        · intro p _ hp
          change (DirectSum.of (SmoothDifferentialForm (n := n) M) p.val.val
            (u.val p.val.val)) q = 0
          apply DirectSum.of_eq_of_ne
          intro heq
          apply hp
          apply Subtype.ext
          exact Fin.ext heq.symm
        · simp
      · rw [u.property q (Nat.not_even_iff_odd.mp he)]
        symm
        apply Finset.sum_eq_zero
        intro p _
        change (DirectSum.of (SmoothDifferentialForm (n := n) M) p.val.val
          (u.val p.val.val)) q = 0
        apply DirectSum.of_eq_of_ne
        intro hp
        exact he (hp ▸ p.property)
    · rw [hhigh q (by omega) (u.val q)]
      symm
      apply Finset.sum_eq_zero
      intro p _
      change (DirectSum.of (SmoothDifferentialForm (n := n) M) p.val.val
        (u.val p.val.val)) q = 0
      apply DirectSum.of_eq_of_ne
      have hp := p.val.isLt
      omega
  refine ⟨E, F, e, f, Φ, ?_, Ψ, ?_, h, k, ?_, ?_, P, ?_, b, ?_, hPprincipal⟩
  · intro u x
    change (Φ₀ (evenEquiv u)).val x = _
    rw [hΦ₀]
    apply congrArg c
    funext p
    rw [hEvenEquiv]
  · intro u x
    change (Ψ₀ (oddEquiv u)).val x = _
    rw [hΨ₀]
    apply congrArg d
    funext p
    rw [hOddEquiv]
  · intro x a b
    change h.pairing x (c a) (c b) = _
    rw [hh, c.symm_apply_apply, c.symm_apply_apply]
  · intro x a b
    change k.pairing x (d a) (d b) = _
    rw [hk, d.symm_apply_apply, d.symm_apply_apply]
  · intro u
    rw [hΦactual, finiteMatrixPseudodifferentialOperator_apply, hΨactual]
    apply congrArg Ψsum
    funext q
    change (∑ p : EvenDegree, (edge p.val.val q.val.val).toLinearMap
      (sectionEquiv p.val.val (u.val p.val.val))) =
      sectionEquiv q.val.val ((positiveHodgeDirac g u).val q.val.val)
    simp_rw [hedge]
    change (∑ p : EvenDegree, (sectionEquiv q.val.val).toLinearMap
      ((totalFormHodgeDirac g (lof p.val.val (u.val p.val.val))) q.val.val)) =
      (sectionEquiv q.val.val).toLinearMap ((positiveHodgeDirac g u).val q.val.val)
    rw [← map_sum (sectionEquiv q.val.val).toLinearMap]
    apply congrArg (sectionEquiv q.val.val)
    have hu := congrArg ((DirectSum.component ℂ ℕ (SmoothDifferentialForm (n := n) M)
      q.val.val).comp (totalFormHodgeDirac g)) (hsum u)
    rw [map_sum] at hu
    exact hu.symm
  · intro x v u
    have he : e x u = esum x (fun p ↦ coordinates p.val.val (u p)) := by
      apply congrArg (e x)
      funext p
      exact ((coordinates p.val.val).symm_apply_apply (u p)).symm
    rw [he, hb]
    change f x (fun q : OddDegree ↦ (coordinates q.val.val).symm
      (∑ p : EvenDegree, (asymbol p.val.val q.val.val).val x (g.inner x v)
        (coordinates p.val.val (u p)))) = _
    apply congrArg (f x)
    funext q
    simp_rw [hasymbolValue, ← map_sum]
    exact (coordinates q.val.val).symm_apply_apply _

end AtiyahSinger

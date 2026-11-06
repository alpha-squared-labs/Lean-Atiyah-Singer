/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.SmoothEquivariantIndex
public import AtiyahSinger.Analysis.SphereHodgeIndex
public import AtiyahSinger.Geometry.FiniteSphereFormAction
public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import AtiyahSinger.Geometry.SmoothBundleIsoFromSections
public import AtiyahSinger.Geometry.SmoothEquivariantBundleIso
public import AtiyahSinger.Topology.EquivariantBundleTransport

/-!
# The original sphere Hodge action in native section coordinates

Public module ID: M1009.

Specified native section equivalences retain the original inverse pullback on
even and odd smooth forms. The same operator square identifies the actual
smooth kernels and quotients by the actual smooth ranges. Their finite
continuous representations therefore compute the original sphere Hodge index.

Source: SG III.9, the analytic index of the de Rham operator. The explicit
section-coordinate comparison supplements the original bundle realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  SmoothTangentMetric.isSmoothPositiveMeasure_riemannianVolume

set_option maxSynthPendingDepth 30

set_option maxHeartbeats 1200000 in
-- The two indices retain the same nested smooth kernel and quotient carriers.
set_option synthInstance.maxHeartbeats 100000 in
-- The extended limit accommodates instance synthesis in the full native sphere Hodge action.
set_option backward.isDefEq.respectTransparency false in
/-- Native coordinates of the same equivariant Hodge operator preserve its full smooth index. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_orthogonalSphereDeRhamIndex
    (r : ℕ) (E F : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E.Fiber)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
    (hσE : σE.IsSmooth (n := r) (r := E.rank) 𝓘(ℝ, OrthogonalGroupModel r))
    (hσF : σF.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
    (Φ : evenSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ≃ₗ[ℂ]
      smoothSections (n := r) (r := E.rank) E.Fiber)
    (Ψ : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ≃ₗ[ℂ]
      smoothSections (n := r) (r := F.rank) F.Fiber)
    (hΦ : ∀ A u, Φ (orthogonalSphereEvenFormRepresentation r A u) =
      σE.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσE A (Φ u))
    (hΨ : ∀ A u, Ψ (orthogonalSphereOddFormRepresentation r A u) =
      σF.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσF A (Ψ u))
    (P : PseudodifferentialOperator (n := r) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber (orthogonalSphereRoundMetric r).riemannianVolume 1)
    (hPg : P.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σE σF hσE hσF)
    (hP : P.IsElliptic)
    (hinter : ∀ u, P.toLinearMap (Φ u) = Ψ (positiveHodgeDirac
      (orthogonalSphereRoundMetric r) u)) :
    P.smoothEquivariantAnalyticIndex 𝓘(ℝ, OrthogonalGroupModel r)
      σE σF hσE hσF hPg hP = orthogonalSphereDeRhamIndex r := by
  classical
  let D := positiveHodgeDirac (orthogonalSphereRoundMetric r)
  -- Restrict exactly the supplied source coordinate map to the two original kernels.
  let K : D.ker ≃ₗ[ℂ] P.toLinearMap.ker := {
    toFun u := ⟨Φ u.val, by rw [LinearMap.mem_ker, hinter, u.property, map_zero]⟩
    invFun u := ⟨Φ.symm u.val, by
      apply Ψ.injective
      rw [map_zero, ← hinter, Φ.apply_symm_apply]
      exact u.property⟩
    left_inv u := Subtype.ext (Φ.symm_apply_apply u.val)
    right_inv u := Subtype.ext (Φ.apply_symm_apply u.val)
    map_add' u v := Subtype.ext (Φ.map_add u.val v.val)
    map_smul' c u := Subtype.ext (Φ.map_smul c u.val) }
  have hrange : D.range.map Ψ.toLinearMap = P.toLinearMap.range := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨Φ u, hinter u⟩
    · rintro ⟨u, rfl⟩
      exact ⟨D (Φ.symm u), ⟨Φ.symm u, rfl⟩,
        (hinter (Φ.symm u)).symm.trans (congrArg P.toLinearMap (Φ.apply_symm_apply u))⟩
  -- Descend the specified target coordinate map through these actual smooth ranges.
  let C := Submodule.Quotient.equiv D.range P.toLinearMap.range Ψ hrange
  have hC (v : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)) :
      C (D.range.mkQ v) = P.toLinearMap.range.mkQ (Ψ v) := rfl
  obtain ⟨ρ, τ, a, b, ha, hb⟩ := exists_orthogonalSphereHodgeRepresentations r
  have hkernel (A : Matrix.orthogonalGroup (Fin r) ℝ) (v : Fin ρ.dimension → ℂ) :
      ((a.trans K) (ρ.representation A v)).val =
        σE.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσE A
          ((a.trans K) v).val := by
    change Φ (a (ρ.representation A v)).val =
      σE.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσE A (Φ (a v).val)
    rw [ha, hΦ]
  have hcoker (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (v : smoothSections (n := r) (r := F.rank) F.Fiber) :
      (b.trans C) (τ.representation A ((b.trans C).symm (P.toLinearMap.range.mkQ v))) =
        P.toLinearMap.range.mkQ
          (σF.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσF A v) := by
    have hpre : C (D.range.mkQ (Ψ.symm v)) = P.toLinearMap.range.mkQ v := by
      rw [hC, Ψ.apply_symm_apply]
    change C (b (τ.representation A (b.symm (C.symm (P.toLinearMap.range.mkQ v))))) = _
    rw [← hpre, C.symm_apply_apply, hb, hC, hΨ, Ψ.apply_symm_apply]
  -- Both definitions now use the same full continuous representations, including their actions.
  rw [P.smoothEquivariantAnalyticIndex_eq 𝓘(ℝ, OrthogonalGroupModel r)
    σE σF hσE hσF hPg hP ρ τ (a.trans K) (b.trans C) hkernel hcoker]
  exact (orthogonalSphereDeRhamIndex_eq r ρ τ a b ha hb).symm


set_option maxHeartbeats 2500000 in
-- Keep the two original native fiber and section coordinates through the same actions.
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 100000 in
-- The extended limit accommodates instance synthesis in the full native sphere Hodge action.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same native even and odd form coordinates carry the original smooth sphere Hodge action. -/
theorem exists_sphereHodgeNativeAction (r : ℕ)
    (E F : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
    (e : ∀ x, ((p : {p : Fin (r + 1) // Even p.val}) →
      DifferentialFormFiber (n := r) p.val.val x) ≃ₗ[ℂ] E.Fiber x)
    (f : ∀ x, ((p : {p : Fin (r + 1) // Odd p.val}) →
      DifferentialFormFiber (n := r) p.val.val x) ≃ₗ[ℂ] F.Fiber x)
    (Φ : evenSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ≃ₗ[ℂ]
      smoothSections (n := r) (r := E.rank) E.Fiber)
    (hΦ : ∀ u x, (Φ u).val x = e x (fun p ↦ (u.val p.val.val).val x))
    (Ψ : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ≃ₗ[ℂ]
      smoothSections (n := r) (r := F.rank) F.Fiber)
    (hΨ : ∀ u x, (Ψ u).val x = f x (fun p ↦ (u.val p.val.val).val x)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∃ σE : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E.Fiber,
    ∃ hσE : σE.IsSmooth (n := r) (r := E.rank) 𝓘(ℝ, OrthogonalGroupModel r),
    ∃ σF : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber,
    ∃ hσF : σF.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r),
      (∀ A x a, σE.linearMap A x (e x a) = e (A • x)
        (fun p ↦ (a p).compContinuousLinearMap
          (mfderiv (𝓡 r) (𝓡 r) (fun z : OrthogonalSphere r ↦ A⁻¹ • z) (A • x)))) ∧
      (∀ A x a, σF.linearMap A x (f x a) = f (A • x)
        (fun p ↦ (a p).compContinuousLinearMap
          (mfderiv (𝓡 r) (𝓡 r) (fun z : OrthogonalSphere r ↦ A⁻¹ • z) (A • x)))) ∧
      (∀ A u, Φ (orthogonalSphereEvenFormRepresentation r A u) =
        σE.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσE A (Φ u)) ∧
      (∀ A u, Ψ (orthogonalSphereOddFormRepresentation r A u) =
        σF.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσF A (Ψ u)) ∧
      ∀ P : PseudodifferentialOperator (n := r) (r := E.rank) (q := F.rank)
          E.Fiber F.Fiber (orthogonalSphereRoundMetric r).riemannianVolume 1,
        (∀ u, P.toLinearMap (Φ u) = Ψ (positiveHodgeDirac (orthogonalSphereRoundMetric r) u)) →
          P.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σE σF hσE hσF := by
  classical
  let S := OrthogonalSphere r
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let IG := 𝓘(ℝ, OrthogonalGroupModel r)
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  -- One finite-family transport argument applies to both original parity bundles.
  have htransport {ι : Type} [Fintype ι] (degree : ι → ℕ)
      (A : SmoothFiniteComplexBundle (n := r) S)
      (a : ∀ x, ((i : ι) → DifferentialFormFiber (n := r) (degree i) x) ≃ₗ[ℂ] A.Fiber x)
      (ΦA : ((i : ι) → SmoothDifferentialForm (n := r) S (degree i)) ≃ₗ[ℂ]
        smoothSections (n := r) (r := A.rank) A.Fiber)
      (hΦA : ∀ u x, (ΦA u).val x = a x (fun i ↦ (u i).val x)) :
      letI := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
      ∃ σ : EquivariantStructure G A.Fiber,
      ∃ hσ : σ.IsSmooth (n := r) (r := A.rank) IG,
        (∀ γ x v, σ.linearMap γ x (a x v) = a (γ • x)
          (fun i ↦ (v i).compContinuousLinearMap
            (mfderiv (𝓡 r) (𝓡 r) (fun z : S ↦ γ⁻¹ • z) (γ • x)))) ∧
        ∀ γ u, ΦA (fun i ↦ smoothFormPullback (fun z : S ↦ γ⁻¹ • z)
          (contMDiff_orthogonalSphere_smul r γ⁻¹) (degree i) (u i)) =
            σ.smoothSectionRepresentation IG hσ γ (ΦA u) := by
    let := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
    -- Choose actual finite tensor charts, then retain their original section comparison.
    obtain ⟨R, Z, c, hZ⟩ :=
      exists_finiteDifferentialForm_bundleModel (orthogonalSphereRoundMetric r) degree
    let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
    let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
    obtain ⟨hSmooth, hbase, hchart, Φ₀, hΦ₀, _, _⟩ := hZ
    let : IsSmoothComplexBundle (n := r) (r := R) Z.Fiber := hSmooth
    let := modelTopology (EuclideanSpace ℂ (Fin R)) Z.Fiber
    obtain ⟨σ₀, hσ₀, hσ₀formula⟩ :=
      exists_finiteSphereFormEquivariantStructure r R degree Z c hbase hchart
    let b (x : S) : Z.Fiber x ≃ₗ[ℂ] A.Fiber x := c.symm.toLinearEquiv.trans (a x)
    let Γ := Φ₀.symm.trans ΦA
    have hΓ (u : smoothSections (n := r) (r := R) Z.Fiber) (x : S) :
        (Γ u).val x = b x (u.val x) := by
      change (ΦA (Φ₀.symm u)).val x = a x (c.symm (u.val x))
      rw [hΦA]
      have h := hΦ₀ (Φ₀.symm u) x
      rw [Φ₀.apply_symm_apply] at h
      rw [h, c.symm_apply_apply]
    obtain ⟨hb, b₀, hb₀⟩ := exists_smoothBundleIso_of_sectionEquiv b Γ hΓ
    obtain ⟨σ, hbσ⟩ := σ₀.exists_conjugate b₀
    have hbaction : ∀ γ x v, b (γ • x) (σ₀.linearMap γ x v) =
        σ.linearMap γ x (b x v) := by
      intro γ x v
      simpa only [Iso.toHom, LinearEquiv.coe_coe, hb₀] using hbσ γ x v
    have hσ : σ.IsSmooth (n := r) (r := A.rank) IG :=
      EquivariantStructure.IsSmooth.of_iso IG σ₀ σ hσ₀ b hb hbaction
    have hformula : ∀ γ x v, σ.linearMap γ x (a x v) = a (γ • x)
        (fun i ↦ (v i).compContinuousLinearMap
          (mfderiv (𝓡 r) (𝓡 r) (fun z : S ↦ γ⁻¹ • z) (γ • x))) := by
      intro γ x v
      have h := hbaction γ x (c v)
      rw [hσ₀formula] at h
      change a (γ • x) (c.symm (c (fun i ↦ (v i).compContinuousLinearMap
        (mfderiv (𝓡 r) (𝓡 r) (fun z : S ↦ γ⁻¹ • z) (γ • x))))) =
          σ.linearMap γ x (a x (c.symm (c v))) at h
      rw [c.symm_apply_apply, c.symm_apply_apply] at h
      exact h.symm
    refine ⟨σ, hσ, hformula, ?_⟩
    intro γ u
    apply Subtype.ext
    funext y
    obtain ⟨x, rfl⟩ := (MulAction.surjective γ) y
    change (ΦA (fun i ↦ smoothFormPullback _ _ (degree i) (u i))).val (γ • x) =
      σ.sectionLinearMap γ (ΦA u).val (γ • x)
    rw [hΦA, σ.sectionLinearMap_smul, hΦA, hformula]
    apply congrArg (a (γ • x))
    funext i
    rw [smoothFormPullback_apply]
    erw [inv_smul_smul]
  -- The original total parity spaces use exactly the same finite homogeneous components.
  obtain ⟨⟨e₀, he₀⟩, ⟨f₀, hf₀⟩⟩ :=
    exists_finiteParityDifferentialForm_equiv (n := r) (M := S)
  let Φfin := e₀.symm.trans Φ
  let Ψfin := f₀.symm.trans Ψ
  have hΦfin u x : (Φfin u).val x = e x (fun p ↦ (u p).val x) := by
    change (Φ (e₀.symm u)).val x = _
    rw [hΦ]
    apply congrArg (e x)
    funext p
    have h := he₀ (e₀.symm u) p
    rw [e₀.apply_symm_apply] at h
    exact congrFun (congrArg Subtype.val h.symm) x
  have hΨfin u x : (Ψfin u).val x = f x (fun p ↦ (u p).val x) := by
    change (Ψ (f₀.symm u)).val x = _
    rw [hΨ]
    apply congrArg (f x)
    funext p
    have h := hf₀ (f₀.symm u) p
    rw [f₀.apply_symm_apply] at h
    exact congrFun (congrArg Subtype.val h.symm) x
  obtain ⟨σE, hσE, hEformula, hEsections⟩ :=
    htransport (fun p : {p : Fin (r + 1) // Even p.val} ↦ p.val.val) E e Φfin hΦfin
  obtain ⟨σF, hσF, hFformula, hFsections⟩ :=
    htransport (fun p : {p : Fin (r + 1) // Odd p.val} ↦ p.val.val) F f Ψfin hΨfin
  have hEven (A : G) u : Φ (orthogonalSphereEvenFormRepresentation r A u) =
      σE.smoothSectionRepresentation IG hσE A (Φ u) := by
    have hdegrees : e₀ (orthogonalSphereEvenFormRepresentation r A u) =
        (fun p ↦ smoothFormPullback (fun z : S ↦ A⁻¹ • z)
          (contMDiff_orthogonalSphere_smul r A⁻¹) p.val.val (e₀ u p)) := by
      funext p
      rw [he₀, he₀]
      rfl
    have h := hEsections A (e₀ u)
    rw [← hdegrees] at h
    change Φ (e₀.symm (e₀ (orthogonalSphereEvenFormRepresentation r A u))) =
      σE.smoothSectionRepresentation IG hσE A (Φ (e₀.symm (e₀ u))) at h
    rw [e₀.symm_apply_apply, e₀.symm_apply_apply] at h
    exact h
  have hOdd (A : G) u : Ψ (orthogonalSphereOddFormRepresentation r A u) =
      σF.smoothSectionRepresentation IG hσF A (Ψ u) := by
    have hdegrees : f₀ (orthogonalSphereOddFormRepresentation r A u) =
        (fun p ↦ smoothFormPullback (fun z : S ↦ A⁻¹ • z)
          (contMDiff_orthogonalSphere_smul r A⁻¹) p.val.val (f₀ u p)) := by
      funext p
      rw [hf₀, hf₀]
      rfl
    have h := hFsections A (f₀ u)
    rw [← hdegrees] at h
    change Ψ (f₀.symm (f₀ (orthogonalSphereOddFormRepresentation r A u))) =
      σF.smoothSectionRepresentation IG hσF A (Ψ (f₀.symm (f₀ u))) at h
    rw [f₀.symm_apply_apply, f₀.symm_apply_apply] at h
    exact h
  refine ⟨σE, hσE, σF, hσF, hEformula, hFformula, hEven, hOdd, ?_⟩
  -- Transport equivariance of the original round positive Hodge operator through these same maps.
  intro P hinter A
  apply LinearMap.ext
  intro u
  obtain ⟨v, rfl⟩ := Φ.surjective u
  change P.toLinearMap (σE.smoothSectionRepresentation IG hσE A (Φ v)) =
    σF.smoothSectionRepresentation IG hσF A (P.toLinearMap (Φ v))
  rw [← hEven, hinter, hinter, ← hOdd]
  exact congrArg Ψ (LinearMap.congr_fun (positiveHodgeDirac_orthogonalSphere_equivariant r A) v)

end AtiyahSinger

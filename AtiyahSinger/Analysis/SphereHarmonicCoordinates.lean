/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereHodge

/-!
# The actual graded harmonic representation of a sphere

Public module ID: M1007.

For a positive-dimensional sphere, the Hodge class equivalence identifies
the degree-zero and top-degree harmonic spaces with their de Rham quotients. All other harmonic
components vanish. This gives coordinates on the actual total harmonic kernel,
retaining its even and odd subspaces and its original inverse-pullback action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped DirectSum Manifold ContDiff

set_option maxHeartbeats 1800000 in
-- Retain the original total Laplacian kernel, degree projections and actual Hodge class maps.
set_option synthInstance.maxHeartbeats 100000 in
-- The extended limit accommodates instance synthesis for the full sphere harmonic representation.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original total sphere harmonic space is the trivial line plus the determinant line,
with their actual degrees determining membership in the even and odd subspaces. -/
theorem exists_sphereTotalHarmonicCoordinates (r : ℕ) (hr : 0 < r) :
    ∃ e : LinearMap.ker (totalFormHodgeLaplacian (orthogonalSphereRoundMetric r)) ≃ₗ[ℂ]
        (ℂ × ℂ),
      (∀ u, u.val ∈ evenSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ↔
        (Odd r → (e u).2 = 0)) ∧
      (∀ u, u.val ∈ oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ↔
        (e u).1 = 0 ∧ (Even r → (e u).2 = 0)) ∧
      (∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) u, ∃ v,
        v.val = orthogonalSphereTotalFormAction r A u.val ∧
        e v = ((e u).1, (A.val.det : ℂ) * (e u).2)) := by
  classical
  let S := OrthogonalSphere r
  let g := orthogonalSphereRoundMetric r
  let F := SmoothDifferentialForm (n := r) S
  let K := LinearMap.ker (totalFormHodgeLaplacian g)
  let L (p : ℕ) := DirectSum.lof ℂ ℕ F p
  have hr0 : r ≠ 0 := Nat.ne_zero_of_lt hr
  have h0r : 0 ≠ r := Ne.symm hr0
  have hcomponentLaw (a : TotalSmoothDifferentialForm (n := r) S) (p : ℕ) :
      (totalFormHodgeLaplacian g a) p = smoothFormHodgeLaplacian g p (a p) := by
    let proj := DirectSum.component ℂ ℕ F p
    have hmap : proj.comp (totalFormHodgeLaplacian g) =
        (smoothFormHodgeLaplacian g p).comp proj := by
      apply DirectSum.linearMap_ext
      intro q
      apply LinearMap.ext
      intro v
      by_cases hq : q = p
      · subst q
        simp [proj, F, S, totalFormHodgeLaplacian, LinearMap.comp_apply]
      · simp [proj, F, S, totalFormHodgeLaplacian, DirectSum.component.of, hq,
          LinearMap.comp_apply]
    exact LinearMap.congr_fun hmap a
  have hcomponent (u : K) (p : ℕ) : smoothFormHodgeLaplacian g p (u.val p) = 0 := by
    rw [← hcomponentLaw]
    exact congrArg (fun a : TotalSmoothDifferentialForm (n := r) S ↦ a p) u.property
  have hvanish (u : K) (p : ℕ) (hp0 : p ≠ 0) (hpr : p ≠ r) : u.val p = 0 := by
    let : Subsingleton (DeRhamCohomology (n := r) S p) :=
      subsingleton_deRhamCohomology_sphere r p hr hp0 hpr
    have h : (⟨u.val p, hcomponent u p⟩ : harmonicForms g p) = 0 :=
      (harmonicDeRhamEquiv g p).injective (Subsingleton.elim _ _)
    exact congrArg Subtype.val h
  -- The inverse inserts precisely the two surviving homogeneous harmonic forms.
  let T : K →ₗ[ℂ] harmonicForms g 0 × harmonicForms g r := {
    toFun u := (⟨u.val 0, hcomponent u 0⟩, ⟨u.val r, hcomponent u r⟩)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hT : Function.Bijective T := by
    constructor
    · intro u v h
      apply Subtype.ext
      apply DFinsupp.ext
      intro p
      by_cases hp0 : p = 0
      · subst p
        exact congrArg (fun w : harmonicForms g 0 × harmonicForms g r ↦ w.1.val) h
      by_cases hpr : p = r
      · subst p
        exact congrArg (fun w : harmonicForms g 0 × harmonicForms g r ↦ w.2.val) h
      rw [hvanish u p hp0 hpr, hvanish v p hp0 hpr]
    · rintro ⟨u, v⟩
      have hh : totalFormHodgeLaplacian g (L 0 u.val + L r v.val) = 0 := by
        simp [L, F, S, totalFormHodgeLaplacian,
          show smoothFormHodgeLaplacian g 0 u.val = 0 from u.property,
          show smoothFormHodgeLaplacian g r v.val = 0 from v.property]
      refine ⟨⟨L 0 u.val + L r v.val, hh⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change (L 0 u.val + L r v.val) 0 = u.val
        simp [L, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, h0r]
      · apply Subtype.ext
        change (L 0 u.val + L r v.val) r = v.val
        simp [L, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hr0]
  obtain ⟨d₀⟩ := nonempty_deRhamCohomology_sphere_zero_equiv r hr
  obtain ⟨dᵣ⟩ := nonempty_deRhamCohomology_sphere_top_equiv r hr
  let e₀ := (harmonicDeRhamEquiv g 0).trans d₀
  let eᵣ := (harmonicDeRhamEquiv g r).trans dᵣ
  let e := (LinearEquiv.ofBijective T hT).trans (e₀.prodCongr eᵣ)
  have he0 (u : K) : (e u).1 = 0 ↔ u.val 0 = 0 := by
    change e₀ ⟨u.val 0, hcomponent u 0⟩ = 0 ↔ u.val 0 = 0
    constructor
    · intro h
      exact congrArg Subtype.val (e₀.injective (h.trans e₀.map_zero.symm))
    · intro h
      exact (congrArg e₀ (Subtype.ext h)).trans e₀.map_zero
  have her (u : K) : (e u).2 = 0 ↔ u.val r = 0 := by
    change eᵣ ⟨u.val r, hcomponent u r⟩ = 0 ↔ u.val r = 0
    constructor
    · intro h
      exact congrArg Subtype.val (eᵣ.injective (h.trans eᵣ.map_zero.symm))
    · intro h
      exact (congrArg eᵣ (Subtype.ext h)).trans eᵣ.map_zero
  refine ⟨e, ?_, ?_, ?_⟩
  · intro u
    constructor
    · intro h hr
      exact (her u).mpr (h r hr)
    · intro h p hp
      by_cases hpr : p = r
      · subst p
        exact (her u).mp (h hp)
      have hp0 : p ≠ 0 := by intro hp0; subst p; simp at hp
      exact hvanish u p hp0 hpr
  · intro u
    constructor
    · intro h
      exact ⟨(he0 u).mpr (h 0 (by decide)), fun hr ↦ (her u).mpr (h r hr)⟩
    · rintro ⟨hzero, htop⟩ p hp
      by_cases hp0 : p = 0
      · subst p
        exact (he0 u).mp hzero
      by_cases hpr : p = r
      · subst p
        exact (her u).mp (htop hp)
      exact hvanish u p hp0 hpr
  · intro A u
    have hh : totalFormHodgeLaplacian g (orthogonalSphereTotalFormAction r A u.val) = 0 := by
      apply DFinsupp.ext
      intro p
      rw [hcomponentLaw]
      change smoothFormHodgeLaplacian g p
        (smoothFormPullback (fun x : S ↦ A⁻¹ • x)
          (contMDiff_orthogonalSphere_smul r A⁻¹) p (u.val p)) = 0
      have h := LinearMap.congr_fun (smoothFormHodgeLaplacian_pullback g g
        (orthogonalSphereDiffeomorph r A⁻¹)
        (orthogonalSphereRoundMetric_invariant r A⁻¹) p) (u.val p)
      change smoothFormHodgeLaplacian g p
        (smoothFormPullback (fun x : S ↦ A⁻¹ • x)
          (contMDiff_orthogonalSphere_smul r A⁻¹) p (u.val p)) =
        smoothFormPullback (fun x : S ↦ A⁻¹ • x)
          (contMDiff_orthogonalSphere_smul r A⁻¹) p
            (smoothFormHodgeLaplacian g p (u.val p)) at h
      rw [hcomponent, map_zero] at h
      exact h
    let v : K := ⟨orthogonalSphereTotalFormAction r A u.val, hh⟩
    refine ⟨v, rfl, ?_⟩
    -- The canonical harmonic class map sends the same pulled-back form to its original class.
    have hdegree (p : ℕ) :
        v.val p = smoothFormPullback (fun x : S ↦ A⁻¹ • x)
          (contMDiff_orthogonalSphere_smul r A⁻¹) p (u.val p) := by
      rfl
    have hclass (p : ℕ) :
        harmonicDeRhamEquiv g p ⟨v.val p, hcomponent v p⟩ =
          orthogonalSphereDeRhamRepresentation r p A
            (harmonicDeRhamEquiv g p ⟨u.val p, hcomponent u p⟩) := by
      let hu : harmonicForms g p := ⟨u.val p, hcomponent u p⟩
      let hv : harmonicForms g p := ⟨v.val p, hcomponent v p⟩
      have h := LinearMap.congr_fun (harmonicDeRhamEquiv_naturality g g
        (orthogonalSphereDiffeomorph r A⁻¹)
        (orthogonalSphereRoundMetric_invariant r A⁻¹) p) hu
      have heq : harmonicFormPullback g g (orthogonalSphereDiffeomorph r A⁻¹)
          (orthogonalSphereRoundMetric_invariant r A⁻¹) p hu = hv := by
        apply Subtype.ext
        exact (hdegree p).symm
      change orthogonalSphereDeRhamRepresentation r p A (harmonicDeRhamEquiv g p hu) =
        harmonicDeRhamEquiv g p _ at h
      rw [heq] at h
      exact h.symm
    apply Prod.ext
    · change d₀ (harmonicDeRhamEquiv g 0 ⟨v.val 0, hcomponent v 0⟩) =
        d₀ (harmonicDeRhamEquiv g 0 ⟨u.val 0, hcomponent u 0⟩)
      rw [hclass, orthogonalSphereDeRhamRepresentation_zero]
      rfl
    · change dᵣ (harmonicDeRhamEquiv g r ⟨v.val r, hcomponent v r⟩) =
        (A.val.det : ℂ) * dᵣ (harmonicDeRhamEquiv g r ⟨u.val r, hcomponent u r⟩)
      rw [hclass, orthogonalSphereDeRhamRepresentation_top r hr]
      change dᵣ ((A.val.det : ℂ) • _) = _
      rw [dᵣ.map_smul]
      rfl

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CircleCotangent
public import AtiyahSinger.Geometry.FiniteDimensionalLocalDiffeomorph
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The normalized angular chart and its actual derivative

Public module ID: M1120.

The standard angular tangent field is smooth and has ambient derivative x*i.
The normalized angular chart has positive derivative everywhere. These facts
fix the sign when the actual derivative tube is transported to cotangent space
through an arbitrary positive tangent metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

local notation "IC" => 𝓡 1
local notation "ER" => EuclideanSpace ℝ (Fin 1)

/-- The invariant positive angular vector field is smooth in the original tangent bundle. -/
theorem contMDiff_circleAngularTangent :
    ContMDiff IC (IC).tangent ∞
      (fun x : Circle ↦ (⟨x, circleAngularTangent x⟩ : TangentBundle IC Circle)) := by
  let f (p : Circle × ℝ) := p.1 * Circle.exp p.2
  have hf : ContMDiff ((IC).prod 𝓘(ℝ, ℝ)) IC ∞ f :=
    contMDiff_fst.mul (contMDiff_circleExp.comp contMDiff_snd)
  have hv : ContMDiff IC ((IC).prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x : Circle ↦ (⟨(x, 0), (0, 1)⟩ : TangentBundle ((IC).prod 𝓘(ℝ, ℝ)) (Circle × ℝ))) := by
    exact contMDiff_equivTangentBundleProd_symm.comp
      ((contMDiff_zeroSection (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin 1))
        (E := TangentSpace IC) (IB := IC)).prodMk
        (contMDiff_const (c := (⟨0, (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1⟩ :
          TangentBundle 𝓘(ℝ, ℝ) ℝ))))
  have hsm := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hv
  apply hsm.congr
  intro x
  apply Bundle.TotalSpace.ext (by simp [f])
  apply heq_of_eq
  change circleAngularTangent x = mfderiv ((IC).prod 𝓘(ℝ, ℝ)) IC f (x, 0) (0, 1)
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) ((IC).prod 𝓘(ℝ, ℝ))
      (fun t : ℝ ↦ (x, t)) 0 := mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hder := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := (IC).prod 𝓘(ℝ, ℝ)) (I'' := IC)
    0 (hf.mdifferentiableAt (by simp)) hcurve
  have hderv := congrArg (fun L ↦ L (1 : ℝ)) hder
  have hp := mfderiv_prodMk (I := 𝓘(ℝ, ℝ)) (I' := IC) (I'' := 𝓘(ℝ, ℝ))
    (f := fun _ : ℝ ↦ x) (g := fun t : ℝ ↦ t) (x := 0)
    mdifferentiableAt_const mdifferentiableAt_id
  rw [hp] at hderv
  change mfderiv 𝓘(ℝ, ℝ) IC (fun t : ℝ ↦ x * Circle.exp t) 0 (1 : ℝ) =
    mfderiv ((IC).prod 𝓘(ℝ, ℝ)) IC f (x, 0)
      ((mfderiv 𝓘(ℝ, ℝ) IC (fun _ : ℝ ↦ x) 0 (1 : ℝ),
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ t) 0 (1 : ℝ))) at hderv
  have hid : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ t) 0 (1 : ℝ) = (1 : ℝ) := by
    erw [mfderiv_id]
    rfl
  have hc : mfderiv 𝓘(ℝ, ℝ) IC (fun _ : ℝ ↦ x) 0 (1 : ℝ) = 0 := by
    rw [mfderiv_const]
    rfl
  rw [hc, hid] at hderv
  have hcast : circleAngularTangent x =
      mfderiv 𝓘(ℝ, ℝ) IC (fun t : ℝ ↦ x * Circle.exp t) 0 (1 : ℝ) := by
    simp only [circleAngularTangent]
    rfl
  exact hcast.trans hderv

/-- The actual circle inclusion sends the positive angular vector to x times i. -/
theorem mfderiv_coe_circleAngularTangent (x : Circle) :
    mfderiv IC 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) x (circleAngularTangent x) =
      (x : ℂ) * Complex.I := by
  let f (t : ℝ) := x * Circle.exp t
  have hfs : ContMDiff 𝓘(ℝ, ℝ) IC ∞ f := contMDiff_const.mul contMDiff_circleExp
  have hf := hfs.mdifferentiableAt (x := 0) (by simp)
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hcs : ContMDiff IC 𝓘(ℝ, ℂ) ∞ (fun z : Circle ↦ (z : ℂ)) :=
    contMDiff_coe_sphere
  have hc := hcs.mdifferentiableAt (x := x) (by simp)
  have hzero : f 0 = x := by simp [f]
  have hcomp := mfderiv_comp_of_eq (I := 𝓘(ℝ, ℝ)) (I' := IC) (I'' := 𝓘(ℝ, ℂ))
    (x := 0) hc hf hzero
  have hreal : HasDerivAt (fun t : ℝ ↦ (f t : ℂ)) ((x : ℂ) * Complex.I) 0 := by
    simpa [f, Circle.coe_exp] using
      (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const Complex.I).cexp.const_mul (x : ℂ))
  have hamb : mfderiv IC 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) x
      (circleAngularTangent x) = (x : ℂ) * Complex.I := by
    have hv := congrArg (fun L ↦ L (1 : ℝ)) hcomp
    have hv' := hreal.hasFDerivAt.fderiv
    have hcast : circleAngularTangent x = mfderiv 𝓘(ℝ, ℝ) IC f 0 (1 : ℝ) := by
      simp only [circleAngularTangent]
      rfl
    rw [hcast]
    have hvleft : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ((fun z : Circle ↦ (z : ℂ)) ∘ f) 0 (1 : ℝ) =
        (x : ℂ) * Complex.I := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun t : ℝ ↦ (f t : ℂ)) 0 (1 : ℝ) = _
      rw [hv']
      simp
    rw [hvleft] at hv
    change (x : ℂ) * Complex.I =
      mfderiv IC 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (f 0)
        (mfderiv 𝓘(ℝ, ℝ) IC f 0 (1 : ℝ)) at hv
    rw [hzero] at hv
    exact hv.symm
  exact hamb

set_option maxHeartbeats 1000000 in
-- Compare the same one-dimensional angular vectors through the original sphere inclusion.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized angular chart has its prescribed positive derivative on every original fiber. -/
theorem exists_circlePointAngularChart (a : Circle) :
    ∃ c : ContMDiffMap IC IC ER Circle ∞,
      (∀ u : ER, c u = a * Circle.exp (2 * Real.arctan (u 0 / 2))) ∧
      IsLocalDiffeomorph IC IC ∞ c ∧ Function.Injective c ∧
      ∀ (u v : ER), mfderiv IC IC c u v =
        (((1 + (u 0 / 2) ^ 2)⁻¹ * v 0) : ℝ) • circleAngularTangent (c u) := by
  classical
  let eR : ER ≃L[ℝ] ℝ := (EuclideanSpace.equiv (Fin 1) ℝ).toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
  let θ (t : ℝ) : ℝ := 2 * Real.arctan (t / 2)
  let k (t : ℝ) : Circle := a * Circle.exp (θ t)
  have hθ : ContDiff ℝ ∞ θ := contDiff_const.mul
    (Real.contDiff_arctan.comp (contDiff_id.div_const 2))
  let c : ContMDiffMap IC IC ER Circle ∞ :=
    ⟨fun u ↦ k (eR u), contMDiff_const.mul
      (contMDiff_circleExp.comp (hθ.comp eR.contDiff).contMDiff)⟩
  have hcvalue (u : ER) : c u = a * Circle.exp (2 * Real.arctan (u 0 / 2)) := rfl
  have hθd (t : ℝ) : HasDerivAt θ (1 + (t / 2) ^ 2)⁻¹ t := by
    convert ((Real.hasDerivAt_arctan (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)).const_mul 2 using 1
    · funext y
      dsimp [θ]
    · simp only [one_div]
      ring
  have hk (t : ℝ) : HasDerivAt (fun s ↦ (k s : ℂ))
      ((((1 + (t / 2) ^ 2)⁻¹ : ℝ) : ℂ) * ((k t : ℂ) * Complex.I)) t := by
    have h := ((hθd t).ofReal_comp.mul_const Complex.I).cexp.const_mul (a : ℂ)
    convert h using 1
    · funext s
      simp [k, Circle.coe_exp]
    · simp only [k, Circle.coe_mul, Circle.coe_exp]
      ring
  have hangular (x : Circle) : circleAngularTangent x ≠ 0 := by
    intro hz
    have h := mfderiv_coe_circleAngularTangent x
    rw [hz, map_zero] at h
    exact mul_ne_zero x.coe_ne_zero Complex.I_ne_zero h.symm
  have hambinj (x : Circle) : Function.Injective
      (mfderiv IC 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) x) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hdim : Module.finrank ℝ (TangentSpace IC x) = 1 := by
      change Module.finrank ℝ ER = 1
      simp
    obtain ⟨t, rfl⟩ :=
      (finrank_eq_one_iff_of_nonzero' (circleAngularTangent x) (hangular x)).mp hdim v
    rw [map_smul, mfderiv_coe_circleAngularTangent] at hv
    change t • ((x : ℂ) * Complex.I) = (0 : ℂ) at hv
    have ht : t = 0 := (smul_eq_zero.mp hv).resolve_right
      (mul_ne_zero x.coe_ne_zero Complex.I_ne_zero)
    rw [ht, zero_smul]
  have hder (u v : ER) : mfderiv IC IC c u v =
      (((1 + (u 0 / 2) ^ 2)⁻¹ * v 0) : ℝ) • circleAngularTangent (c u) := by
    let α : ℝ := (1 + (eR u / 2) ^ 2)⁻¹
    have hcomplex : HasFDerivAt (fun w : ER ↦ (c w : ℂ))
        (eR.toContinuousLinearMap.smulRight ((α : ℂ) * ((c u : ℂ) * Complex.I))) u := by
      convert (hk (eR u)).hasFDerivAt.comp u eR.hasFDerivAt using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro v
        simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearEquiv.coe_coe]
        rfl
    let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
    have hcoe : ContMDiff IC 𝓘(ℝ, ℂ) ∞ (fun z : Circle ↦ (z : ℂ)) := contMDiff_coe_sphere
    have hchain := mfderiv_comp u (hcoe.mdifferentiable (by simp) (c u))
      (c.contMDiff.mdifferentiable (by simp) u)
    have hd : mfderiv IC 𝓘(ℝ, ℂ) ((fun z : Circle ↦ (z : ℂ)) ∘ c) u =
        eR.toContinuousLinearMap.smulRight ((α : ℂ) * ((c u : ℂ) * Complex.I)) := by
      rw [mfderiv_eq_fderiv]
      exact hcomplex.fderiv
    rw [hd] at hchain
    apply hambinj (c u)
    rw [map_smul, mfderiv_coe_circleAngularTangent]
    have h := congrArg (fun L : ER →L[ℝ] ℂ ↦ L v) hchain
    change eR v • ((α : ℂ) * ((c u : ℂ) * Complex.I)) =
      mfderiv IC 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (c u) (mfderiv IC IC c u v) at h
    rw [← h]
    change (v 0 : ℂ) * ((α : ℂ) * ((c u : ℂ) * Complex.I)) =
      ((α * v 0 : ℝ) : ℂ) * ((c u : ℂ) * Complex.I)
    rw [Complex.ofReal_mul]
    ring
  have hc : IsLocalDiffeomorph IC IC ∞ c := by
    apply isLocalDiffeomorph_of_isInvertible_mfderiv c
    intro u
    let L : ER →L[ℝ] ER := mfderiv IC IC c u
    have hinj : Function.Injective L := by
      apply (injective_iff_map_eq_zero L).mpr
      intro v hv
      have h := hder u v
      change L v = _ at h
      rw [hv] at h
      have heq : ((1 + (u 0 / 2) ^ 2)⁻¹ * v 0) = 0 :=
        (smul_eq_zero.mp h.symm).resolve_right (hangular (c u))
      have hα : (1 + (u 0 / 2) ^ 2)⁻¹ ≠ 0 :=
        inv_ne_zero (by positivity)
      have hv0 : v 0 = 0 := (mul_eq_zero.mp heq).resolve_left hα
      apply eR.injective
      exact hv0.trans (map_zero eR).symm
    have hbij : Function.Bijective L := ⟨hinj, LinearMap.surjective_of_injective hinj⟩
    let d : ER ≃L[ℝ] ER := (LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv
    change L.IsInvertible
    exact ⟨d, rfl⟩
  have hinj : Function.Injective c := by
    have hθinj : Function.Injective θ := by
      intro u v h
      apply (fun h : u / 2 = v / 2 ↦ (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp h)
      apply Real.arctan_injective
      dsimp [θ] at h
      linarith
    have hrange (t : ℝ) : θ t ∈ Set.Ico (-Real.pi) Real.pi := by
      obtain ⟨hl, hu⟩ := Real.arctan_mem_Ioo (t / 2)
      constructor <;> dsimp [θ] <;> linarith
    intro u v huv
    apply eR.injective
    apply hθinj
    apply Circle.exp_injOn_Ico (by linarith) (hrange _) (hrange _)
    exact mul_left_cancel huv
  exact ⟨c, hcvalue, hc, hinj, hder⟩

end AtiyahSinger

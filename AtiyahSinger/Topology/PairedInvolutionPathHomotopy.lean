/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopy
public import AtiyahSinger.Topology.BundleTrivial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Contraction of a path paired with its reversed involution conjugate

Public module ID: M1984.

A path between two finite complex fibers with involutive sewing has a
paired doubled path which contracts through the same sewing relation to a constant
intertwiner. The proof first replaces the paired reversal by an exchange path,
using a square of block rotations, and then contracts the exchange angle.

All maps and inverse maps are jointly continuous. The original finite fibers and
their direct-sum topologies are retained, including zero-dimensional fibers. This
is an elementary supplement for the reflection formula of Atiyah--Singer I,
Lemma 2.8; no Bott generation, index theorem, or homotopy-group classification is
used. Every interpolation and rotation remains local to the one theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped unitInterval

attribute [local instance] trivialTopology sumTopology

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 3200000 in
-- Check the three explicit deformation stages and both inverse-continuity directions together.
/-- A path paired with its reversed involution conjugate contracts, with its exact
endpoint sewing, to a constant intertwiner on the same doubled fibers. -/
theorem exists_paired_involution_path_homotopy {r q : ℕ}
    (A : (Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))
    (B : (Fin q → ℂ) ≃ₗ[ℂ] (Fin q → ℂ))
    (hA : Function.Involutive A) (hB : Function.Involutive B)
    (p : Iso (Bundle.Trivial I (Fin r → ℂ)) (Bundle.Trivial I (Fin q → ℂ)))
    (hp : ∀ v, p.linearEquiv 1 v = B (p.linearEquiv 0 (A v))) :
    ∃ H : Iso
        (Bundle.Trivial (I × I) (Fin r → ℂ) ×ᵇ Bundle.Trivial (I × I) (Fin r → ℂ))
        (Bundle.Trivial (I × I) (Fin q → ℂ) ×ᵇ Bundle.Trivial (I × I) (Fin q → ℂ)),
      ∃ e : ((Fin r → ℂ) × (Fin r → ℂ)) ≃ₗ[ℂ] ((Fin q → ℂ) × (Fin q → ℂ)),
        (∀ t v, H.linearEquiv (0, t) v =
          (B (p.linearEquiv (unitInterval.symm t) (A v.1)), p.linearEquiv t v.2)) ∧
        (∀ t v, H.linearEquiv (1, t) v = e v) ∧
        (∀ s v, H.linearEquiv (s, 1) (A v.1, -A v.2) =
          (B (H.linearEquiv (s, 0) v).1, -B (H.linearEquiv (s, 0) v).2)) ∧
        (∀ v, e (A v.1, -A v.2) = (B (e v).1, -B (e v).2)) := by
  classical
  let U := Fin r → ℂ
  let W := Fin q → ℂ
  have hAA (x : U) : A (A x) = x := hA x
  have hBB (x : W) : B (B x) = x := hB x
  let L := (U × U) ≃ₗ[ℂ] (W × W)
  let good (f : I × I → L) : Prop :=
    Continuous (fun z : (I × I) × (U × U) ↦ f z.1 z.2) ∧
      Continuous (fun z : (I × I) × (W × W) ↦ (f z.1).symm z.2)
  let ku (v : U × U) : U × U := (A v.1, -A v.2)
  let kw (v : W × W) : W × W := (B v.1, -B v.2)
  let sewing (f : I × I → L) : Prop := ∀ s v, f (s, 1) (ku v) = kw (f (s, 0) v)
  -- Read the original path and its inverse in the original product topology.
  have hpc : Continuous (fun z : I × U ↦ p.linearEquiv z.1 z.2) := by
    have hin : Continuous (fun z : I × U ↦
        (⟨z.1, z.2⟩ : TotalSpace Unit (Bundle.Trivial I U))) :=
      continuous_induced_rng.mpr continuous_id
    exact (continuous_induced_dom.comp (p.continuous_total.comp hin)).snd
  have hpi : Continuous (fun z : I × W ↦ (p.linearEquiv z.1).symm z.2) := by
    have hin : Continuous (fun z : I × W ↦
        (⟨z.1, z.2⟩ : TotalSpace Unit (Bundle.Trivial I W))) :=
      continuous_induced_rng.mpr continuous_id
    exact (continuous_induced_dom.comp (p.continuous_symm.comp hin)).snd
  let dA : (U × U) ≃ₗ[ℂ] (U × U) := A.prodCongr (LinearEquiv.refl ℂ U)
  let dB : (W × W) ≃ₗ[ℂ] (W × W) := B.prodCongr (LinearEquiv.refl ℂ W)
  let twist (e : L) : L := dA.trans (e.trans dB)
  have htwist (f : I × I → L) (hf : good f) : good (fun x ↦ twist (f x)) := by
    constructor
    · exact dB.toLinearMap.continuous_of_finiteDimensional.comp
        (hf.1.comp (continuous_fst.prodMk
          (dA.toLinearMap.continuous_of_finiteDimensional.comp continuous_snd)))
    · exact dA.symm.toLinearMap.continuous_of_finiteDimensional.comp
        (hf.2.comp (continuous_fst.prodMk
          (dB.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_snd)))
  have hdiag (a b : C(I × I, I)) :
      good (fun x ↦ (p.linearEquiv (a x)).prodCongr (p.linearEquiv (b x))) := by
    constructor
    · exact (hpc.comp ((a.continuous.comp continuous_fst).prodMk continuous_snd.fst)).prodMk
        (hpc.comp ((b.continuous.comp continuous_fst).prodMk continuous_snd.snd))
    · exact (hpi.comp ((a.continuous.comp continuous_fst).prodMk continuous_snd.fst)).prodMk
        (hpi.comp ((b.continuous.comp continuous_fst).prodMk continuous_snd.snd))
  have hpre (f : I × I → L) (hf : good f) (c : C(I × I, I × I)) :
      good (fun x ↦ f (c x)) := by
    exact ⟨hf.1.comp ((c.continuous.comp continuous_fst).prodMk continuous_snd),
      hf.2.comp ((c.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  -- Ordinary block rotations are invertible at every angle, on each actual finite fiber.
  let rot (m : ℕ) (a : ℝ) :
      ((Fin m → ℂ) × (Fin m → ℂ)) ≃ₗ[ℂ] ((Fin m → ℂ) × (Fin m → ℂ)) :=
    { toFun := fun v ↦ ((Real.cos a : ℂ) • v.1 - (Real.sin a : ℂ) • v.2,
        (Real.sin a : ℂ) • v.1 + (Real.cos a : ℂ) • v.2)
      invFun := fun v ↦ ((Real.cos a : ℂ) • v.1 + (Real.sin a : ℂ) • v.2,
        -(Real.sin a : ℂ) • v.1 + (Real.cos a : ℂ) • v.2)
      map_add' := by intros; ext i <;> simp <;> ring
      map_smul' := by intros; ext i <;> simp <;> ring
      left_inv := by
        intro v
        have htrig : (Real.sin a : ℂ) ^ 2 + (Real.cos a : ℂ) ^ 2 = 1 := by
          exact_mod_cast Real.sin_sq_add_cos_sq a
        apply Prod.ext
        · ext i
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination v.1 i * htrig
        · ext i
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination v.2 i * htrig
      right_inv := by
        intro v
        have htrig : (Real.sin a : ℂ) ^ 2 + (Real.cos a : ℂ) ^ 2 = 1 := by
          exact_mod_cast Real.sin_sq_add_cos_sq a
        apply Prod.ext
        · ext i
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination v.1 i * htrig
        · ext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination v.2 i * htrig }
  have hrotapply (m : ℕ) (a : ℝ) (x : (Fin m → ℂ) × (Fin m → ℂ)) :
      rot m a x = ((Real.cos a : ℂ) • x.1 - (Real.sin a : ℂ) • x.2,
        (Real.sin a : ℂ) • x.1 + (Real.cos a : ℂ) • x.2) := rfl
  have hrotsymmapply (m : ℕ) (a : ℝ) (x : (Fin m → ℂ) × (Fin m → ℂ)) :
      (rot m a).symm x = ((Real.cos a : ℂ) • x.1 + (Real.sin a : ℂ) • x.2,
        -(Real.sin a : ℂ) • x.1 + (Real.cos a : ℂ) • x.2) := rfl
  clear_value rot
  have hrotinv (m : ℕ) (a : ℝ) : rot m (-a) = (rot m a).symm := by
    ext v i <;> simp [hrotapply, hrotsymmapply]
  have hrotc (m : ℕ) : Continuous (fun z : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) ↦
      rot m z.1 z.2) := by
    simp_rw [hrotapply]
    fun_prop
  have hrotated (f : I × I → L) (hf : good f) (c : C(I × I, ℝ)) :
      good (fun x ↦ (rot r (-c x)).trans ((f x).trans (rot q (c x)))) := by
    constructor
    · exact (hrotc q).comp ((c.continuous.comp continuous_fst).prodMk
        (hf.1.comp (continuous_fst.prodMk ((hrotc r).comp
          ((c.continuous.neg.comp continuous_fst).prodMk continuous_snd)))))
    · change Continuous (fun z : (I × I) × (W × W) ↦
        (rot r (-c z.1)).symm ((f z.1).symm ((rot q (c z.1)).symm z.2)))
      simp_rw [← hrotinv, neg_neg]
      exact (hrotc r).comp ((c.continuous.comp continuous_fst).prodMk
        (hf.2.comp (continuous_fst.prodMk ((hrotc q).comp
          ((c.continuous.neg.comp continuous_fst).prodMk continuous_snd)))))
  -- This square interpolates between a diagonal path and its block interchange.
  let F (x : I × I) : L := (rot r (-(Real.pi * (x.1 : ℝ) / 2))).trans
    (((p.linearEquiv x.2).prodCongr (p.linearEquiv 0)).trans
      (rot q (Real.pi * (x.1 : ℝ) / 2)))
  have hFc : good F := hrotated
    (fun x : I × I ↦ (p.linearEquiv x.2).prodCongr (p.linearEquiv 0))
    (hdiag ⟨Prod.snd, continuous_snd⟩ ⟨fun _ ↦ 0, continuous_const⟩)
    ⟨fun x ↦ Real.pi * (x.1 : ℝ) / 2, by fun_prop⟩
  have hFleft (v : I) : F (0, v) =
      (p.linearEquiv v).prodCongr (p.linearEquiv 0) := by
    apply LinearEquiv.ext
    intro x
    change rot q (Real.pi * (0 : ℝ) / 2)
      ((p.linearEquiv v).prodCongr (p.linearEquiv 0)
        (rot r (-(Real.pi * (0 : ℝ) / 2)) x)) = _
    simp only [LinearEquiv.prodCongr_apply]
    simp_rw [hrotapply]
    simp
    rfl
  have hFright (v : I) : F (1, v) =
      (p.linearEquiv 0).prodCongr (p.linearEquiv v) := by
    apply LinearEquiv.ext
    intro x
    change rot q (Real.pi * (1 : ℝ) / 2)
      ((p.linearEquiv v).prodCongr (p.linearEquiv 0)
        (rot r (-(Real.pi * (1 : ℝ) / 2)) x)) = _
    simp only [LinearEquiv.prodCongr_apply]
    simp_rw [hrotapply]
    simp
    rfl
  have hFbottom (u : I) : F (u, 0) =
      (p.linearEquiv 0).prodCongr (p.linearEquiv 0) := by
    have hnat (a : ℝ) (x : U × U) :
        rot q a ((p.linearEquiv 0).prodCongr (p.linearEquiv 0) x) =
          (p.linearEquiv 0).prodCongr (p.linearEquiv 0) (rot r a x) := by
      ext i <;> simp [hrotapply, map_sub, map_add, map_smul]
    apply LinearEquiv.ext
    intro x
    change rot q (Real.pi * (u : ℝ) / 2)
      ((p.linearEquiv 0).prodCongr (p.linearEquiv 0)
        (rot r (-(Real.pi * (u : ℝ) / 2)) x)) = _
    rw [hnat, hrotinv, LinearEquiv.apply_symm_apply]
  -- Affine interpolation and the three-edge path stay inside the same parameter square.
  let mix (s x y : I) : I := ⟨(1 - (s : ℝ)) * x + (s : ℝ) * y, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.2.2) x.2.1)
        (mul_nonneg s.2.1 y.2.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr x.2.2),
        mul_nonneg s.2.1 (sub_nonneg.mpr y.2.2)]⟩
  have hmixc : Continuous (fun z : I × I × I ↦ mix z.1 z.2.1 z.2.2) := by
    apply Continuous.subtype_mk
    fun_prop
  have hmix0 (x y : I) : mix 0 x y = x := by ext; simp [mix]
  have hmix1 (x y : I) : mix 1 x y = y := by ext; simp [mix]
  have hmixsame (s x : I) : mix s x x = x := by
    apply Subtype.ext
    change (1 - (s : ℝ)) * x + (s : ℝ) * x = (x : ℝ)
    ring
  clear_value mix
  let clip : C(ℝ, I) := ⟨Set.projIcc 0 1 zero_le_one, by fun_prop⟩
  let a : C(I, I) := ⟨fun t ↦ clip (1 - 3 * (t : ℝ)), by fun_prop⟩
  let b : C(I, I) := ⟨fun t ↦ clip (3 * (t : ℝ) - 2), by fun_prop⟩
  let u : C(I, I) := ⟨fun t ↦ clip (3 * (t : ℝ) - 1), by fun_prop⟩
  let v : C(I, I) := ⟨fun t ↦ clip ((a t : ℝ) + (b t : ℝ)), by fun_prop⟩
  have hclip0 {x : ℝ} (hx : x ≤ 0) : clip x = 0 :=
    _root_.projIcc_eq_zero.mpr hx
  have hclip1 {x : ℝ} (hx : 1 ≤ x) : clip x = 1 :=
    _root_.projIcc_eq_one.mpr hx
  have hclipval (x : I) : clip (x : ℝ) = x := by
    exact Set.projIcc_val (zero_le_one : (0 : ℝ) ≤ 1) x
  have ha0 : a 0 = 1 := hclip1 (by norm_num)
  have ha1 : a 1 = 0 := hclip0 (by norm_num)
  have hb0 : b 0 = 0 := hclip0 (by norm_num)
  have hb1 : b 1 = 1 := hclip1 (by norm_num)
  have hu0 : u 0 = 0 := hclip0 (by norm_num)
  have hu1 : u 1 = 1 := hclip1 (by norm_num)
  have hv0 : v 0 = 1 := by change clip _ = 1; rw [ha0, hb0]; exact hclip1 (by norm_num)
  have hv1 : v 1 = 1 := by change clip _ = 1; rw [ha1, hb1]; exact hclip1 (by norm_num)
  have hedge (t : I) : F (u t, v t) =
      (p.linearEquiv (a t)).prodCongr (p.linearEquiv (b t)) := by
    by_cases ht : (t : ℝ) ≤ 1 / 3
    · have hb : b t = 0 := hclip0 (by linarith)
      have hu : u t = 0 := hclip0 (by linarith)
      have hv : v t = a t := by
        change clip ((a t : ℝ) + (b t : ℝ)) = a t
        rw [hb]; simpa using hclipval (a t)
      rw [hu, hv, hFleft, hb]
    · by_cases ht' : (t : ℝ) ≤ 2 / 3
      · have ha : a t = 0 := hclip0 (by linarith)
        have hb : b t = 0 := hclip0 (by linarith)
        have hv : v t = 0 := by
          change clip ((a t : ℝ) + (b t : ℝ)) = 0
          rw [ha, hb]; exact hclip0 (by norm_num)
        rw [hv, hFbottom, ha, hb]
      · have ha : a t = 0 := hclip0 (by linarith)
        have hu : u t = 1 := hclip1 (by linarith)
        have hv : v t = b t := by
          change clip ((a t : ℝ) + (b t : ℝ)) = b t
          rw [ha]; simpa using hclipval (b t)
        rw [hu, hv, hFright, ha]
  -- The first two deformations fix the endpoints, hence retain the given sewing.
  let J (x : I × I) : L := twist
    ((p.linearEquiv (mix x.1 (unitInterval.symm x.2) (a x.2))).prodCongr
      (p.linearEquiv (mix x.1 x.2 (b x.2))))
  have hJc : good J := by
    exact htwist
      (fun x : I × I ↦
        (p.linearEquiv (mix x.1 (unitInterval.symm x.2) (a x.2))).prodCongr
          (p.linearEquiv (mix x.1 x.2 (b x.2))))
      (hdiag
      ⟨fun x ↦ mix x.1 (unitInterval.symm x.2) (a x.2),
        hmixc.comp (continuous_fst.prodMk
          ((unitInterval.continuous_symm.comp continuous_snd).prodMk
            (a.continuous.comp continuous_snd)))⟩
      ⟨fun x ↦ mix x.1 x.2 (b x.2),
        hmixc.comp (continuous_fst.prodMk
          (continuous_snd.prodMk (b.continuous.comp continuous_snd)))⟩)
  let K (x : I × I) : L := twist (F (mix x.1 (u x.2) x.2, mix x.1 (v x.2) 1))
  have hKc : good K := by
    exact htwist
      (fun x : I × I ↦ F (mix x.1 (u x.2) x.2, mix x.1 (v x.2) 1))
      (hpre F hFc
      ⟨fun x ↦ (mix x.1 (u x.2) x.2, mix x.1 (v x.2) 1),
        (hmixc.comp (continuous_fst.prodMk
          ((u.continuous.comp continuous_snd).prodMk continuous_snd))).prodMk
          (hmixc.comp (continuous_fst.prodMk
            ((v.continuous.comp continuous_snd).prodMk continuous_const)))⟩)
  have hJK (t : I) : J (1, t) = K (0, t) := by
    dsimp [J, K]
    rw [hmix1, hmix1, hmix0, hmix0, hedge]
  have hJ0 (s : I) : J (s, 0) = twist
      ((p.linearEquiv 1).prodCongr (p.linearEquiv 0)) := by
    dsimp [J]
    rw [unitInterval.symm_zero, ha0, hb0, hmixsame, hmixsame]
  have hJ1 (s : I) : J (s, 1) = twist
      ((p.linearEquiv 0).prodCongr (p.linearEquiv 1)) := by
    dsimp [J]
    rw [unitInterval.symm_one, ha1, hb1, hmixsame, hmixsame]
  have hK0 (s : I) : K (s, 0) = twist
      ((p.linearEquiv 1).prodCongr (p.linearEquiv 0)) := by
    dsimp [K]
    rw [hu0, hv0, hmixsame, hmixsame, hFleft]
  have hK1 (s : I) : K (s, 1) = twist
      ((p.linearEquiv 0).prodCongr (p.linearEquiv 1)) := by
    dsimp [K]
    rw [hu1, hv1, hmixsame, hFright]
  have hendsew (x : U × U) :
      twist ((p.linearEquiv 0).prodCongr (p.linearEquiv 1)) (ku x) =
        kw (twist ((p.linearEquiv 1).prodCongr (p.linearEquiv 0)) x) := by
    change (B (p.linearEquiv 0 (A (A x.1))), p.linearEquiv 1 (-A x.2)) =
      (B (B (p.linearEquiv 1 (A x.1))), -B (p.linearEquiv 0 x.2))
    simp [hp, hAA, hBB]
  have hJs : sewing J := by intro s x; rw [hJ1, hJ0]; exact hendsew x
  have hKs : sewing K := by intro s x; rw [hK1, hK0]; exact hendsew x
  -- The exchange path has an angular reflection identity, so its contraction keeps sewing.
  let S (a : ℝ) : L := twist ((rot r (-a)).trans
    (((p.linearEquiv 1).prodCongr (p.linearEquiv 0)).trans (rot q a)))
  have hSapply (a : ℝ) (x : U × U) : S a x =
      let y := rot r (-a) (A x.1, x.2)
      let z := rot q a (p.linearEquiv 1 y.1, p.linearEquiv 0 y.2)
      (B z.1, z.2) := rfl
  have hSsym (a : ℝ) (x : U × U) : S (Real.pi / 2 - a) (ku x) = kw (S a x) := by
    rw [hSapply, hSapply]
    dsimp only [ku, kw]
    simp_rw [hrotapply]
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub, Complex.ofReal_neg]
    apply Prod.ext <;> simp [hp, hAA, hBB, map_add, map_sub, map_smul] <;> module
  let angle (x : I × I) : ℝ :=
    Real.pi / 2 * ((1 - (x.1 : ℝ)) * x.2 + (x.1 : ℝ) / 2)
  let N (x : I × I) : L := S (angle x)
  have hNc : good N := by
    exact htwist
      (fun x : I × I ↦ (rot r (-angle x)).trans
        (((p.linearEquiv 1).prodCongr (p.linearEquiv 0)).trans (rot q (angle x))))
      (hrotated (fun _ : I × I ↦ (p.linearEquiv 1).prodCongr (p.linearEquiv 0))
        (hdiag ⟨fun _ ↦ 1, continuous_const⟩ ⟨fun _ ↦ 0, continuous_const⟩)
        ⟨angle, by dsimp [angle]; fun_prop⟩)
  have hNs : sewing N := by
    intro s x
    change S (angle (s, 1)) (ku x) = kw (S (angle (s, 0)) x)
    have hangle : angle (s, 1) = Real.pi / 2 - angle (s, 0) := by
      dsimp [angle]
      ring
    rw [hangle]
    exact hSsym _ _
  have hKN (t : I) : K (1, t) = N (0, t) := by
    dsimp [K, N]
    rw [hmix1, hmix1]
    have heq : angle (0, t) = Real.pi * (t : ℝ) / 2 := by dsimp [angle]; ring
    rw [heq]
  let e : L := S (Real.pi / 4)
  have hNend (t : I) : N (1, t) = e := by
    have heq : angle (1, t) = Real.pi / 4 := by dsimp [angle]; ring
    change S (angle (1, t)) = e
    rw [heq]
  have hequiv (x : U × U) : e (ku x) = kw (e x) := by
    have heq : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    simpa only [heq] using hSsym (Real.pi / 4) x
  -- Closed-half pasting preserves both inverse continuity and the same sewing equation.
  have hjoin (f g : I × I → L) (hf : good f) (hg : good g)
      (hfg : ∀ t, f (1, t) = g (0, t)) (hfs : sewing f) (hgs : sewing g) :
      ∃ h : I × I → L, good h ∧ sewing h ∧
        (∀ t, h (0, t) = f (0, t)) ∧ (∀ t, h (1, t) = g (1, t)) := by
    let left : C(I, I) := ⟨fun s ↦ clip (2 * (s : ℝ)), by fun_prop⟩
    let right : C(I, I) := ⟨fun s ↦ clip (2 * (s : ℝ) - 1), by fun_prop⟩
    let f' (x : I × I) : L := f (left x.1, x.2)
    let g' (x : I × I) : L := g (right x.1, x.2)
    have hfc : good f' := hpre f hf
      ⟨fun x ↦ (left x.1, x.2), (left.continuous.comp continuous_fst).prodMk continuous_snd⟩
    have hgc : good g' := hpre g hg
      ⟨fun x ↦ (right x.1, x.2), (right.continuous.comp continuous_fst).prodMk continuous_snd⟩
    have hseam (s t : I) (hs : (s : ℝ) = 1 / 2) : f' (s, t) = g' (s, t) := by
      have hl : left s = 1 := hclip1 (by linarith)
      have hr : right s = 0 := hclip0 (by linarith)
      dsimp [f', g']
      rw [hl, hr, hfg]
    let h (x : I × I) : L := if (x.1 : ℝ) ≤ 1 / 2 then f' x else g' x
    have hhc : good h := by
      constructor
      · have hc := continuous_if_le
          (continuous_subtype_val.comp continuous_fst.fst) continuous_const
          hfc.1.continuousOn hgc.1.continuousOn
          (fun z hz ↦ congrArg (fun j : L ↦ j z.2) (hseam z.1.1 z.1.2 hz))
        exact hc.congr (fun z ↦ by dsimp [h]; split_ifs <;> rfl)
      · have hc := continuous_if_le
          (continuous_subtype_val.comp continuous_fst.fst) continuous_const
          hfc.2.continuousOn hgc.2.continuousOn
          (fun z hz ↦ congrArg (fun j : L ↦ j.symm z.2) (hseam z.1.1 z.1.2 hz))
        exact hc.congr (fun z ↦ by dsimp [h]; split_ifs <;> rfl)
    refine ⟨h, hhc, ?_, ?_, ?_⟩
    · intro s x
      change (if (s : ℝ) ≤ 1 / 2 then f' (s, 1) else g' (s, 1)) (ku x) =
        kw ((if (s : ℝ) ≤ 1 / 2 then f' (s, 0) else g' (s, 0)) x)
      split_ifs with hs
      · exact hfs (left s) x
      · exact hgs (right s) x
    · intro t
      have hl : left 0 = 0 := hclip0 (by norm_num)
      simp only [h, Set.Icc.coe_zero, show (0 : ℝ) ≤ 1 / 2 by norm_num, ↓reduceIte]
      change f (left 0, t) = f (0, t)
      rw [hl]
    · intro t
      have hr : right 1 = 1 := hclip1 (by norm_num)
      simp only [h, Set.Icc.coe_one, show ¬(1 : ℝ) ≤ 1 / 2 by norm_num, ↓reduceIte]
      change g (right 1, t) = g (1, t)
      rw [hr]
  obtain ⟨M, hMc, hMs, hM0, hM1⟩ := hjoin J K hJc hKc hJK hJs hKs
  obtain ⟨f, hfc, hfs, hf0, hf1⟩ := hjoin M N hMc hNc
    (fun t ↦ (hM1 t).trans (hKN t)) hMs hNs
  -- Package the same family with the existing doubled trivial-bundle topology.
  have hcoords (m : ℕ) : Continuous (fun z : TotalSpace Unit
      (Bundle.Trivial (I × I) (Fin m → ℂ) ×ᵇ Bundle.Trivial (I × I) (Fin m → ℂ)) ↦
        ((z.proj, z.snd) : (I × I) × ((Fin m → ℂ) × (Fin m → ℂ)))) := by
    have hd : Continuous (fun z : TotalSpace Unit
        (Bundle.Trivial (I × I) (Fin m → ℂ) ×ᵇ Bundle.Trivial (I × I) (Fin m → ℂ)) ↦
          ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit (Bundle.Trivial (I × I) (Fin m → ℂ))),
            (⟨z.proj, z.snd.2⟩ : TotalSpace Unit (Bundle.Trivial (I × I) (Fin m → ℂ))))) :=
      continuous_induced_dom
    have hleft := (continuous_induced_dom.comp hd.fst)
    have hright := (continuous_induced_dom.comp hd.snd)
    exact hleft.fst.prodMk (hleft.snd.prodMk hright.snd)
  have hin (m : ℕ) : Continuous (fun z : (I × I) × ((Fin m → ℂ) × (Fin m → ℂ)) ↦
      (⟨z.1, z.2⟩ : TotalSpace Unit
        (Bundle.Trivial (I × I) (Fin m → ℂ) ×ᵇ Bundle.Trivial (I × I) (Fin m → ℂ)))) := by
    apply continuous_induced_rng.mpr
    exact (continuous_induced_rng.mpr (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (continuous_induced_rng.mpr (continuous_fst.prodMk continuous_snd.snd))
  let H : Iso (Bundle.Trivial (I × I) U ×ᵇ Bundle.Trivial (I × I) U)
      (Bundle.Trivial (I × I) W ×ᵇ Bundle.Trivial (I × I) W) :=
    { linearEquiv := f
      continuous_total := (hin q).comp ((continuous_fst.prodMk hfc.1).comp (hcoords r))
      continuous_symm := (hin r).comp ((continuous_fst.prodMk hfc.2).comp (hcoords q)) }
  refine ⟨H, e, ?_, ?_, hfs, hequiv⟩
  · intro t x
    change f (0, t) x = _
    rw [hf0, hM0]
    change twist ((p.linearEquiv (mix 0 (unitInterval.symm t) (a t))).prodCongr
      (p.linearEquiv (mix 0 t (b t)))) x = _
    rw [hmix0, hmix0]
    rfl
  · intro t x
    change f (1, t) x = e x
    rw [hf1, hNend]

end AtiyahSinger

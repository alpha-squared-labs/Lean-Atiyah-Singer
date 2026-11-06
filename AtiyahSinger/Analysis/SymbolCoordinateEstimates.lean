/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Symbol
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Derivative estimates for smooth linear changes of symbol frequency

Public module ID: M1019.

The mixed derivatives in the original symbol definition are compared with derivatives on
product spaces before rescaling frequency. This supplies the quantitative chain rule used
both for cotangent coordinate changes and for the corresponding spatial-pair amplitudes.
No additional symbol class or replacement frequency object is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff Manifold

set_option maxSynthPendingDepth 20

/-- Quantitative comparison between full derivatives and mixed partial derivatives.
The bound permits the higher chain rule after frequency rescaling. -/
theorem norm_iteratedFDeriv_uncurry_le_of_mixed
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (k : ℕ) (x y : P) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ i ≤ k, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (Function.uncurry f) (x, y)‖ ≤ 2 ^ k * A := by
  have mixed_fderiv_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v := by
    let F := Function.uncurry f
    let L : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
    let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
    have hF : Differentiable ℝ F := hf.differentiable (by simp)
    have hDF : Differentiable ℝ (fderiv ℝ F) :=
      (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiable (by simp)
    -- Each partial first derivative is the full derivative restricted to one factor.
    have hleft (a : X) (b : Y) :
        fderiv ℝ (fun t ↦ f t b) a = (fderiv ℝ F (a, b)).comp L := by
      exact ((hF (a, b)).hasFDerivAt.comp a
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) a b)).fderiv
    have hright (a : X) (b : Y) :
        fderiv ℝ (f a) b = (fderiv ℝ F (a, b)).comp R :=
      ((hF (a, b)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right (𝕜 := ℝ) a b)).fderiv
    -- Differentiate those restrictions through fixed continuous linear composition maps.
    have hxy : fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) y v u =
        fderiv ℝ (fderiv ℝ F) (x, y) (0, v) (u, 0) := by
      simp_rw [hleft]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] X →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ X (X × Y) V).flip L
      have hd := (hDF (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp y hd
      exact congrArg (fun K : Y →L[ℝ] X →L[ℝ] V ↦ K v u) hc.fderiv
    have hyx : fderiv ℝ (fun t ↦ fderiv ℝ (f t) y) x u v =
        fderiv ℝ (fderiv ℝ F) (x, y) (u, 0) (0, v) := by
      simp_rw [hright]
      let C : ((X × Y) →L[ℝ] V) →L[ℝ] Y →L[ℝ] V :=
        (ContinuousLinearMap.compL ℝ Y (X × Y) V).flip R
      have hd := (hDF (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
      have hc := C.hasFDerivAt.comp x hd
      exact congrArg (fun K : X →L[ℝ] Y →L[ℝ] V ↦ K u v) hc.fderiv
    -- Symmetry applies on the full product, with the original two factor directions.
    rw [hxy, hyx]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (0, v) (u, 0)
  have mixed_fderiv_apply_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
        fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u := by
    have hl : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x) := by
      have hh : ContDiff ℝ ∞ (Function.uncurry (fun z t ↦ f t z)) :=
        hf.comp (contDiff_snd.prodMk contDiff_fst)
      exact hh.fderiv contDiff_const (by simp)
    have hr : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (f t) y) :=
      hf.fderiv contDiff_const (by simp)
    rw [fderiv_clm_apply (hl.differentiable (by simp) y) (differentiableAt_const u),
      fderiv_clm_apply (hr.differentiable (by simp) x) (differentiableAt_const v)]
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using mixed_fderiv_comm f hf x y u v
  have parametric {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Y V).symm : _ →L[ℝ] Y [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) V).symm :
          _ →L[ℝ] Y [×(k + 1)]→L[ℝ] V)
  have iterated_comm {X Y V : Type}
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (comm : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (f : X → Y → W) (_hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : X) (y : Y) (u : X) (v : Y),
        fderiv ℝ (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y v =
          fderiv ℝ (fun t ↦ fderiv ℝ (f t) y v) x u)
      (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : X) (y : Y)
      (u : X) :
      iteratedFDeriv ℝ k (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) y =
        fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) y) x u := by
    induction k generalizing y with
    | zero =>
      let J := (continuousMultilinearCurryFin0 ℝ Y V).symm.toContinuousLinearEquiv
      exact (congrArg (fun T : X →L[ℝ] Y [×0]→L[ℝ] V ↦ T u)
        (J.comp_fderiv (f := fun t ↦ f t y) (x := x))).symm
    | succ k ih =>
      ext v
      have hs : ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (f z.1) z.2) :=
        parametric f hf k
      rw [iteratedFDeriv_succ_apply_left]
      have hi : (fun z ↦ iteratedFDeriv ℝ k
          (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) =
          (fun z ↦ fderiv ℝ (fun t ↦ iteratedFDeriv ℝ k (f t) z) x u) := by
        funext z
        exact ih z
      change ((fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k
        (fun z ↦ fderiv ℝ (fun t ↦ f t z) x u) z) y) (v 0)) (Fin.tail v) = _
      rw [hi]
      have hc := comm (fun t z ↦ iteratedFDeriv ℝ k (f t) z) hs x y u (v 0)
      rw [hc]
      have hd : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun t : X ↦ fun z : Y ↦ iteratedFDeriv ℝ k (f t) z)) := hs
        exact h.fderiv contDiff_const (by simp)
      have heq : (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y v) =
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0) (Fin.tail v)) := by
        funext t
        exact iteratedFDeriv_succ_apply_left v
      have hx : ContDiff ℝ ∞ (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y) :=
        (parametric f hf (k + 1)).comp (contDiff_id.prodMk contDiff_const)
      have ha : ContDiff ℝ ∞
          (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ k (f t)) y (v 0)) :=
        hd.clm_apply contDiff_const
      rw [← fderiv_continuousMultilinear_apply_const_apply
        (hx.contDiffAt.differentiableAt (by simp)), heq,
        fderiv_continuousMultilinear_apply_const_apply (ha.contDiffAt.differentiableAt (by simp))]
  let mixed {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      P [×i]→L[ℝ] P [×j]→L[ℝ] V :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  have mixed_map_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (L : V →L[ℝ] W) (f : P → P → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f)) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ L (f y η)) i j x ξ‖ ≤ ‖L‖ * ‖mixed f i j x ξ‖ := by
    let T := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ P) V W L
    have hT : ‖T‖ ≤ ‖L‖ := by
      apply T.opNorm_le_bound (norm_nonneg _)
      intro v
      exact L.norm_compContinuousMultilinearMap_le v
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ L (f y η)) ξ) =
        T ∘ (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) := by
      funext y
      exact L.iteratedFDeriv_comp_left
        ((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt) (by simp)
    unfold mixed
    rw [heq]
    exact (T.norm_iteratedFDeriv_comp_left
      (((parametric f hf j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt)
        (by simp)).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have mixed_shift {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  -- Separated spatial derivatives control restriction to the same spatial diagonal.
  have mixed_left_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y u : P) :
      ‖mixed (fun a b ↦ fderiv ℝ (fun z ↦ f z b) a u) i j x y‖ ≤
        ‖u‖ * ‖mixed f (i + 1) j x y‖ := by
    have heq : (fun a ↦ iteratedFDeriv ℝ j
        (fun b ↦ fderiv ℝ (fun z ↦ f z b) a u) y) =
        (fun a ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ j (f z) y) a u) := by
      funext a
      exact iterated_comm mixed_fderiv_apply_comm f hf j a y u
    unfold mixed
    rw [heq]
    have hs : ContDiff ℝ ∞ (fun a ↦ iteratedFDeriv ℝ j (f a) y) :=
      (parametric f hf j).comp (contDiff_id.prodMk contDiff_const)
    have hds : ContDiff ℝ ∞ (fderiv ℝ (fun a ↦ iteratedFDeriv ℝ j (f a) y)) :=
      hs.fderiv_right (by simp)
    have h := norm_iteratedFDeriv_clm_apply_const hds.contDiffAt (x := x) (n := i)
      (c := u) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at h
    exact h
  have mixed_right_bound {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (i j : ℕ) (x y u : P) :
      ‖mixed (fun a b ↦ fderiv ℝ (f a) b u) i j x y‖ ≤
        ‖u‖ * ‖mixed f i (j + 1) x y‖ := by
    have hd : ContDiff ℝ ∞ (fun z : P × P ↦ fderiv ℝ (f z.1) z.2) := by
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : P × P ↦ fun b : P ↦ f z.1 b)) :=
        hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact h.fderiv contDiff_snd (by simp)
    let L : (P →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V u
    have hL : ‖L‖ ≤ ‖u‖ := by
      apply L.opNorm_le_bound (norm_nonneg _)
      intro T
      exact (T.le_opNorm u).trans_eq (mul_comm _ _)
    have h := mixed_map_bound L (fun a b ↦ fderiv ℝ (f a) b) hd i j x y
    rw [mixed_shift] at h
    exact h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have joint_bound {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      (i : ℕ) : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V), ContDiff ℝ ∞ (Function.uncurry f) →
      ∀ (x y : P) (A : ℝ), 0 ≤ A →
      (∀ a ≤ i, ∀ b ≤ i, ‖mixed f a b x y‖ ≤ A) →
      ‖iteratedFDeriv ℝ i (Function.uncurry f) (x, y)‖ ≤ 2 ^ i * A := by
    induction i with
    | zero =>
      intro V _ _ f hf x y A hA hbound
      simpa only [mixed, norm_iteratedFDeriv_zero, pow_zero, one_mul,
        Function.uncurry_apply_pair] using hbound 0 le_rfl 0 le_rfl
    | succ i ih =>
      intro V _ _ f hf x y A hA hbound
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro v
      let u := v (Fin.last i)
      let fl (a b : P) : V := fderiv ℝ (fun z ↦ f z b) a u.1
      let fr (a b : P) : V := fderiv ℝ (f a) b u.2
      have hfl : ContDiff ℝ ∞ (Function.uncurry fl) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun a : P ↦ f a z.2)) :=
          hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
        exact (h.fderiv contDiff_fst (by simp)).clm_apply contDiff_const
      have hfr : ContDiff ℝ ∞ (Function.uncurry fr) := by
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : P × P ↦ fun b : P ↦ f z.1 b)) :=
          hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
        exact (h.fderiv contDiff_snd (by simp)).clm_apply contDiff_const
      have hleft : ‖iteratedFDeriv ℝ i (Function.uncurry fl) (x, y)‖ ≤
          2 ^ i * (‖u‖ * A) := by
        apply ih fl hfl x y (‖u‖ * A) (mul_nonneg (norm_nonneg _) hA)
        intro a ha b hb
        calc
          _ ≤ ‖u.1‖ * ‖mixed f (a + 1) b x y‖ := mixed_left_bound f hf a b x y u.1
          _ ≤ ‖u‖ * A := mul_le_mul (norm_fst_le u)
            (hbound (a + 1) (Nat.add_le_add_right ha 1) b (Nat.le.step hb))
            (norm_nonneg _) (norm_nonneg _)
      have hright : ‖iteratedFDeriv ℝ i (Function.uncurry fr) (x, y)‖ ≤
          2 ^ i * (‖u‖ * A) := by
        apply ih fr hfr x y (‖u‖ * A) (mul_nonneg (norm_nonneg _) hA)
        intro a ha b hb
        calc
          _ ≤ ‖u.2‖ * ‖mixed f a (b + 1) x y‖ := mixed_right_bound f hf a b x y u.2
          _ ≤ ‖u‖ * A := mul_le_mul (norm_snd_le u)
            (hbound a (Nat.le.step ha) (b + 1) (Nat.add_le_add_right hb 1))
            (norm_nonneg _) (norm_nonneg _)
      -- Split each full derivative into its two product directions.
      have hsplit : (fun z ↦ fderiv ℝ (Function.uncurry f) z u) =
          Function.uncurry fl + Function.uncurry fr := by
        funext z
        have hF := (hf.differentiable (by simp) z).hasFDerivAt
        have hl := hF.comp (f := fun t : P ↦ (t, z.2)) z.1
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
        have hr := hF.comp (f := fun t : P ↦ (z.1, t)) z.2
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
        change fderiv ℝ (Function.uncurry f) z u =
          fderiv ℝ (fun t ↦ f t z.2) z.1 u.1 + fderiv ℝ (f z.1) z.2 u.2
        simp only [Function.comp_def, Function.uncurry_def] at hl hr
        rw [hl.fderiv, hr.fderiv]
        change fderiv ℝ (Function.uncurry f) z u =
          fderiv ℝ (Function.uncurry f) z (u.1, 0) +
            fderiv ℝ (Function.uncurry f) z (0, u.2)
        rw [← map_add]
        simp
      have hd : ContDiff ℝ ∞ (fderiv ℝ (Function.uncurry f)) := hf.fderiv_right (by simp)
      rw [iteratedFDeriv_succ_apply_right,
        ← iteratedFDeriv_clm_apply_const_apply hd (by simp), hsplit,
        iteratedFDeriv_add_apply (f := Function.uncurry fl) (g := Function.uncurry fr)
          (hfl.contDiffAt.of_le (by simp)) (hfr.contDiffAt.of_le (by simp))]
      apply (norm_add_le _ _).trans
      have hl := (iteratedFDeriv ℝ i (Function.uncurry fl) (x, y)).le_opNorm (Fin.init v)
      have hr := (iteratedFDeriv ℝ i (Function.uncurry fr) (x, y)).le_opNorm (Fin.init v)
      apply (add_le_add (hl.trans (mul_le_mul_of_nonneg_right hleft (by positivity)))
        (hr.trans (mul_le_mul_of_nonneg_right hright (by positivity)))).trans_eq
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.init, u, pow_succ]
      ring
  exact joint_bound k f hf x y A hA hbound

/-- Repeated differentiation has the same norm as the corresponding total derivative. -/
private theorem norm_iteratedFDeriv_twice
    {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X → V) (i j : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ i (iteratedFDeriv ℝ j f) x‖ =
      ‖iteratedFDeriv ℝ (i + j) f x‖ := by
  induction j generalizing i with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    simp only [Nat.add_zero]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_fderiv, ih]
    exact congrArg (fun k : ℕ ↦ ‖iteratedFDeriv ℝ k f x‖) (by omega)

/-- Derivatives along either factor are bounded by the corresponding full derivative. -/
private theorem norm_iteratedFDeriv_affine_restrict_le
    {X Y V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X → V) (hf : ContDiff ℝ ∞ f) (L : Y →L[ℝ] X)
    (hL : ‖L‖ ≤ 1) (a : X) (i : ℕ) (y : Y) :
    ‖iteratedFDeriv ℝ i (fun z ↦ f (a + L z)) y‖ ≤
      ‖iteratedFDeriv ℝ i f (a + L y)‖ := by
  let g := fun z ↦ f (a + z)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have heq : (fun z ↦ f (a + L z)) = g ∘ L := rfl
  rw [heq, L.iteratedFDeriv_comp_right hg y (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hprod : (∏ _ : Fin i, ‖L‖) ≤ 1 := by
    exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL)
  have hn := mul_le_mul_of_nonneg_left hprod
    (norm_nonneg (iteratedFDeriv ℝ i g (L y)))
  simpa only [mul_one, g, iteratedFDeriv_comp_add_left] using hn

/-- Mixed derivatives are restrictions of a full derivative on the product space. -/
theorem norm_mixed_iteratedFDeriv_le
    {X Y V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X → Y → V) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (i j : ℕ) (x : X) (y : Y) :
    ‖iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) y) x‖ ≤
      ‖iteratedFDeriv ℝ (i + j) (Function.uncurry f) (x, y)‖ := by
  let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
  let L : X →L[ℝ] X × Y := ContinuousLinearMap.inl ℝ X Y
  let T : ((X × Y) [×j]→L[ℝ] V) →L[ℝ] (Y [×j]→L[ℝ] V) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j ↦ R)
  have hR : ‖R‖ ≤ 1 := by
    apply R.opNorm_le_bound zero_le_one
    intro v
    simp [R]
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro v
    simp [L]
  have hT : ‖T‖ ≤ 1 := by
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le V _).trans
      (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hR))
  have heq (z : X) : iteratedFDeriv ℝ j (f z) y =
      T (iteratedFDeriv ℝ j (Function.uncurry f) (z, y)) := by
    let g := fun w : X × Y ↦ f (z + w.1) w.2
    have hg : ContDiff ℝ ∞ g := hf.comp
      ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
    have hg' : g = fun w : X × Y ↦ Function.uncurry f ((z, 0) + w) := by
      ext w
      simp [g, Function.uncurry]
    have hcomp : f z = g ∘ R := by
      ext w
      simp [g, R]
    rw [hcomp, R.iteratedFDeriv_comp_right hg y (by simp)]
    change _ = (iteratedFDeriv ℝ j (Function.uncurry f) (z, y)).compContinuousLinearMap _
    congr 1
    rw [hg', iteratedFDeriv_comp_add_left]
    simp [R]
  have hG : ContDiff ℝ ∞ (iteratedFDeriv ℝ j (Function.uncurry f)) :=
    hf.iteratedFDeriv_right (by simp)
  have hslice : ContDiff ℝ ∞
      (fun z : X ↦ iteratedFDeriv ℝ j (Function.uncurry f) (z, y)) :=
    hG.comp (contDiff_id.prodMk contDiff_const)
  simp_rw [heq]
  have hfirst := T.norm_iteratedFDeriv_comp_left hslice.contDiffAt (n := i) (x := x)
    (by simp)
  have hsecond := norm_iteratedFDeriv_affine_restrict_le
    (iteratedFDeriv ℝ j (Function.uncurry f)) hG L hL (0, y) i x
  simp only [L, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero] at hsecond
  apply hfirst.trans
  apply (mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans
  simpa only [one_mul, norm_iteratedFDeriv_twice] using hsecond

/-- Exact rescaling of mixed derivatives, including the original totalized derivatives. -/
private theorem mixed_iteratedFDeriv_frequency_smul
    {X Y V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : X → Y → V) (R : ℝ) (hR : R ≠ 0) (i j : ℕ) (x : X) (y : Y) :
    iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ f z (R • η)) y) x =
      R ^ j • iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (f z) (R • y)) x := by
  let e : Y ≃L[ℝ] Y := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR)
  have hfreq (z : X) : iteratedFDeriv ℝ j (fun η ↦ f z (R • η)) y =
      R ^ j • iteratedFDeriv ℝ j (f z) (R • y) := by
    have h := e.iteratedFDerivWithin_comp_right (f z) uniqueDiffOn_univ
      (x := y) (Set.mem_univ _) j
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
    change iteratedFDeriv ℝ j (f z ∘ e) y = _
    rw [h]
    ext v
    change (iteratedFDeriv ℝ j (f z) (R • y)) (fun a ↦ R • v a) = _
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp
  simp_rw [hfreq]
  let J : (Y [×j]→L[ℝ] V) ≃L[ℝ] (Y [×j]→L[ℝ] V) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (R ^ j) (pow_ne_zero _ hR))
  exact J.iteratedFDeriv_comp_left

/-- A two-sided comparison of positive bases controls every real power. -/
private theorem rpow_le_mul_rpow_of_comparable
    (a b B s : ℝ) (ha : 0 < a) (hb : 0 < b) (hB : 0 < B)
    (hab : a ≤ B * b) (hba : b ≤ B * a) :
    a ^ s ≤ B ^ |s| * b ^ s := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs, ← Real.mul_rpow hB.le hb.le]
    exact Real.rpow_le_rpow ha.le hab hs
  · have hs' : s ≤ 0 := (lt_of_not_ge hs).le
    have hcomp : (B * a) ^ s ≤ b ^ s :=
      Real.rpow_le_rpow_of_nonpos hb hba hs'
    calc
      a ^ s = B ^ |s| * (B * a) ^ s := by
        rw [Real.mul_rpow hB.le ha.le, abs_of_nonpos hs', ← mul_assoc,
          ← Real.rpow_add hB, neg_add_cancel, Real.rpow_zero, one_mul]
      _ ≤ B ^ |s| * b ^ s := mul_le_mul_of_nonneg_left hcomp (by positivity)

/-- Quantitative symbol substitution for globally smooth data on a fixed compact set.
The sole growth assumption on the linear frequency map is its two-sided norm comparison there. -/
private theorem exists_bound_symbol_comp_linear_frequency_global
    {Z X V : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : X → X → V) (hp : ContDiff ℝ ∞ (Function.uncurry p))
    (φ : Z → X) (hφ : ContDiff ℝ ∞ φ)
    (Θ : Z → X →L[ℝ] X) (hΘ : ContDiff ℝ ∞ Θ)
    (m : ℝ) (K : Set Z) (hK : IsCompact K)
    (hpbound : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j (p x) ξ) (φ z)‖ ≤
        C * (1 + ‖ξ‖) ^ (m - (j : ℝ)))
    (B : ℝ) (hB : 1 ≤ B)
    (hupper : ∀ z ∈ K, ∀ ξ, ‖Θ z ξ‖ ≤ B * ‖ξ‖)
    (hlower : ∀ z ∈ K, ∀ ξ, ‖ξ‖ ≤ B * ‖Θ z ξ‖) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i
        (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ p (φ w) (Θ w η)) ξ) z‖ ≤
          C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  classical
  let k := i + j
  let g : Z × X → X × X := fun z ↦ (φ z.1, Θ z.1 z.2)
  have hg : ContDiff ℝ ∞ g :=
    (hφ.comp contDiff_fst).prodMk ((hΘ.comp contDiff_fst).clm_apply contDiff_snd)
  have hcompact : IsCompact (K ×ˢ Metric.closedBall (0 : X) 1) :=
    hK.prod (isCompact_closedBall _ _)
  -- The normalized inner map is evaluated only at frequencies of norm at most one.
  have hgbound (a : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ w ∈ K ×ˢ Metric.closedBall (0 : X) 1, ‖iteratedFDeriv ℝ a g w‖ ≤ D := by
    obtain ⟨D, hD⟩ := hcompact.exists_bound_of_continuousOn
      (hg.continuous_iteratedFDeriv (by simp)).continuousOn
    exact ⟨max D 0, le_max_right _ _, fun w hw ↦ (hD w hw).trans (le_max_left _ _)⟩
  choose D hD hgD using hgbound
  choose C hC hpC using hpbound
  let D' := 1 + ∑ a ∈ Finset.range (k + 1), D a
  have hD' : 1 ≤ D' :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun a _ ↦ hD a))
  have hDD' (a : ℕ) (ha : a ≤ k) : D a ≤ D' := by
    apply le_trans (Finset.single_le_sum (fun b _ ↦ hD b)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le ha)))
    exact le_add_of_nonneg_left zero_le_one
  let A := ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
    C a b * B ^ |m - (b : ℝ)|
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg
      (fun b _ ↦ mul_nonneg (hC a b) (Real.rpow_nonneg (zero_le_one.trans hB) _)))
  have hCA (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
      C a b * B ^ |m - (b : ℝ)| ≤ A := by
    have hn (a b : ℕ) : 0 ≤ C a b * B ^ |m - (b : ℝ)| :=
      mul_nonneg (hC a b) (Real.rpow_nonneg (zero_le_one.trans hB) _)
    exact (Finset.single_le_sum (fun b _ ↦ hn a b)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))).trans
      (Finset.single_le_sum (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ hn a b))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ha)))
  let C' : ℝ := k.factorial * (2 ^ k * A) * D' ^ k
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨C', hC', ?_⟩
  intro z hz ξ
  let R : ℝ := 1 + ‖ξ‖
  have hR : 0 < R := by dsimp [R]; positivity
  let η : X := R⁻¹ • ξ
  have hη : ‖η‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    apply (inv_mul_le_iff₀ hR).mpr
    dsimp [R]
    linarith
  have hRη : R • η = ξ := smul_inv_smul₀ hR.ne' ξ
  let pR : X → X → V := fun x y ↦ p x (R • y)
  have hpR : ContDiff ℝ ∞ (Function.uncurry pR) :=
    hp.comp (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd))
  have hscaled (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
      ‖iteratedFDeriv ℝ a
        (fun x ↦ iteratedFDeriv ℝ b (pR x) (Θ z η)) (φ z)‖ ≤ A * R ^ m := by
    -- Each frequency derivative contributes R, while the symbol order loses the same power.
    rw [mixed_iteratedFDeriv_frequency_smul p R hR.ne' a b,
      norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR b)]
    have hfreq : R • Θ z η = Θ z ξ := by rw [← map_smul, hRη]
    rw [hfreq]
    have hweight : (1 + ‖Θ z ξ‖) ^ (m - (b : ℝ)) ≤
        B ^ |m - (b : ℝ)| * R ^ (m - (b : ℝ)) := by
      apply rpow_le_mul_rpow_of_comparable _ _ _ _ (by positivity) hR
        (zero_lt_one.trans_le hB)
      · dsimp [R]
        nlinarith [hupper z hz ξ]
      · dsimp [R]
        nlinarith [hlower z hz ξ]
    calc
      _ ≤ R ^ b * (C a b * (B ^ |m - (b : ℝ)| * R ^ (m - (b : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left ((hpC a b z hz (Θ z ξ)).trans
          (mul_le_mul_of_nonneg_left hweight (hC a b))) (pow_nonneg hR.le _)
      _ = (C a b * B ^ |m - (b : ℝ)|) * R ^ m := by
        have hpow : R ^ b * R ^ (m - (b : ℝ)) = R ^ m := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (C a b * B ^ |m - (b : ℝ)|) *
              (R ^ b * R ^ (m - (b : ℝ))) := by ring
          _ = _ := by rw [hpow]
      _ ≤ A * R ^ m := mul_le_mul_of_nonneg_right (hCA a b ha hb) (by positivity)
  have houter (a : ℕ) (ha : a ≤ k) :
      ‖iteratedFDeriv ℝ a (Function.uncurry pR) (g (z, η))‖ ≤
        (2 ^ k * A) * R ^ m := by
    have h := norm_iteratedFDeriv_uncurry_le_of_mixed pR hpR a (φ z) (Θ z η)
      (A * R ^ m) (mul_nonneg hA (by positivity))
      (fun b hb c hc ↦ hscaled b c (hb.trans ha) (hc.trans ha))
    apply h.trans
    calc
      2 ^ a * (A * R ^ m) ≤ 2 ^ k * (A * R ^ m) := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ha)
          (mul_nonneg hA (by positivity))
      _ = _ := by ring
  have hinner (a : ℕ) (ha : 1 ≤ a) (hak : a ≤ k) :
      ‖iteratedFDeriv ℝ a g (z, η)‖ ≤ D' ^ a := by
    exact (hgD a (z, η) ⟨hz, by simpa using hη⟩).trans
      ((hDD' a hak).trans (le_self_pow₀ hD' (by omega)))
  have hchain := norm_iteratedFDeriv_comp_le hpR hg (n := k) (by simp) (z, η)
    houter hinner
  let q : Z → X → V := fun w ζ ↦ p (φ w) (Θ w ζ)
  have hq : ContDiff ℝ ∞ (Function.uncurry q) := hp.comp hg
  have heq : Function.uncurry (fun w ζ ↦ q w (R • ζ)) = Function.uncurry pR ∘ g := by
    ext w
    simp [q, pR, g, Function.uncurry, map_smul]
  have hfull : ‖iteratedFDeriv ℝ k
      (Function.uncurry (fun w ζ ↦ q w (R • ζ))) (z, η)‖ ≤ C' * R ^ m := by
    rw [heq]
    convert hchain using 1
    dsimp [C']
    ring
  have hmixed := norm_mixed_iteratedFDeriv_le (fun w ζ ↦ q w (R • ζ))
    (hq.comp (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd))) i j z η
  have hfinal := hmixed.trans hfull
  rw [mixed_iteratedFDeriv_frequency_smul q R hR.ne' i j,
    norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hR j), hRη] at hfinal
  have hdivide : ‖iteratedFDeriv ℝ i
      (fun w ↦ iteratedFDeriv ℝ j (q w) ξ) z‖ ≤ (C' * R ^ m) / R ^ j :=
    (le_div_iff₀ (pow_pos hR j)).mpr (by simpa only [mul_comm] using hfinal)
  have hpower : (C' * R ^ m) / R ^ j = C' * R ^ (m - (j : ℝ)) := by
    rw [Real.rpow_sub hR, Real.rpow_natCast, mul_div_assoc]
  exact hdivide.trans_eq hpower

/-- Smooth cutoffs preserve a neighborhood of a compact set inside an open domain. -/
private theorem exists_symbol_cutoff
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (U K : Set Z) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : Z → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ z ∈ K, χ =ᶠ[nhds z] (fun _ ↦ 1)) ∧
      (∀ z ∉ U, χ =ᶠ[nhds z] (fun _ ↦ 0)) := by
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, Z) hU.isClosed_compl hK.isClosed
      (Set.disjoint_compl_left_iff_subset.mpr hKU)
  exact ⟨χ, contMDiff_iff_contDiff.mp χ.contMDiff,
    fun z hz ↦ hone.filter_mono (nhds_le_nhdsSet hz),
    fun z hz ↦ hzero.filter_mono (nhds_le_nhdsSet hz)⟩

/-- A smooth parameter-dependent invertible linear frequency substitution preserves symbol order.
This is the common estimate for cotangent coordinate changes and spatial-pair amplitudes. -/
theorem exists_bound_symbol_comp_linear_frequency
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {n r s : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)))
    (hp : IsSymbol U m p) (V : Set Z) (hV : IsOpen V)
    (φ : Z → EuclideanSpace ℝ (Fin n)) (hφ : ContDiffOn ℝ ∞ φ V)
    (hφU : Set.MapsTo φ V U)
    (Θ : Z → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hΘ : ContDiffOn ℝ ∞ Θ V) (hinv : ∀ z ∈ V, (Θ z).IsInvertible)
    (K : Set Z) (hK : IsCompact K) (hKV : K ⊆ V) (i j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ i
        (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ p (φ w) (Θ w η)) ξ) z‖ ≤
          C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)
  -- Cutoffs change none of the germs used by the desired mixed derivatives.
  obtain ⟨χ, hχ, hχone, hχzero⟩ := exists_symbol_cutoff V K hV hK hKV
  have smooth_extend {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (f : Z → Y) (hf : ContDiffOn ℝ ∞ f V) : ContDiff ℝ ∞ (fun z ↦ χ z • f z) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ V
    · exact hχ.contDiffAt.smul (hf.contDiffAt (hV.mem_nhds hz))
    · apply (contDiffAt_const (c := (0 : Y))).congr_of_eventuallyEq
      filter_upwards [hχzero z hz] with w hw
      simp only [hw, zero_smul]
  let φ' : Z → X := fun z ↦ χ z • φ z
  let Θ' : Z → X →L[ℝ] X := fun z ↦ χ z • Θ z
  have hφ' : ContDiff ℝ ∞ φ' := smooth_extend φ hφ
  have hΘ' : ContDiff ℝ ∞ Θ' := smooth_extend Θ hΘ
  have hφeq (z : Z) (hz : z ∈ K) : φ' =ᶠ[nhds z] φ := by
    filter_upwards [hχone z hz] with w hw
    simp only [φ', hw, one_smul]
  have hΘeq (z : Z) (hz : z ∈ K) : Θ' =ᶠ[nhds z] Θ := by
    filter_upwards [hχone z hz] with w hw
    simp only [Θ', hw, one_smul]
  have himage : IsCompact (φ '' K) := hK.image_of_continuousOn (hφ.continuousOn.mono hKV)
  obtain ⟨β, hβ, hβone, hβzero⟩ := exists_symbol_cutoff U (φ '' K) hU himage
    (by rintro _ ⟨z, hz, rfl⟩; exact hφU (hKV hz))
  let p' : X → X → H := fun x ξ ↦ β x • p x ξ
  have hp' : ContDiff ℝ ∞ (Function.uncurry p') := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z.1 ∈ U
    · exact (hβ.comp contDiff_fst).contDiffAt.smul
        (hp.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩))
    · apply (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq
      have heq := (hβzero z.1 hz).comp_tendsto continuous_fst.continuousAt
      filter_upwards [heq] with w hw
      change β w.1 = 0 at hw
      simp only [p', Function.uncurry, hw, zero_smul]
  have hpeq (z : Z) (hz : z ∈ K) :
      p' =ᶠ[nhds (φ z)] p := by
    filter_upwards [hβone (φ z) ⟨z, hz, rfl⟩] with x hx
    funext ξ
    simp only [p', hx, one_smul]
  have hpbound (a b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ a (fun x ↦ iteratedFDeriv ℝ b (p' x) ξ) (φ' z)‖ ≤
        C * (1 + ‖ξ‖) ^ (m - (b : ℝ)) := by
    obtain ⟨C, hC, hpC⟩ := hp.2 (φ '' K)
      (by rintro _ ⟨z, hz, rfl⟩; exact hφU (hKV hz)) himage a b
    refine ⟨C, hC, fun z hz ξ ↦ ?_⟩
    rw [(hφeq z hz).eq_of_nhds]
    have heq : (fun x ↦ iteratedFDeriv ℝ b (p' x) ξ) =ᶠ[nhds (φ z)]
        (fun x ↦ iteratedFDeriv ℝ b (p x) ξ) := by
      filter_upwards [hpeq z hz] with x hx
      rw [hx]
    rw [(heq.iteratedFDeriv ℝ a).eq_of_nhds]
    exact hpC (φ z) ⟨z, hz, rfl⟩ ξ
  -- Compactness bounds the original linear maps and their inverses on the same K.
  have hΘcont : ContinuousOn Θ K := hΘ.continuousOn.mono hKV
  have hΘinv : ContinuousOn (fun z ↦ (Θ z).inverse) K := by
    intro z hz
    exact (((hinv z (hKV hz)).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
      (hΘcont z hz))
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn hΘcont
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn hΘinv
  let B : ℝ := max 1 (max B₁ B₂)
  have hB : 1 ≤ B := le_max_left _ _
  have hupper (z : Z) (hz : z ∈ K) (ξ : X) : ‖Θ' z ξ‖ ≤ B * ‖ξ‖ := by
    rw [(hΘeq z hz).eq_of_nhds]
    exact (Θ z).le_opNorm ξ |>.trans (mul_le_mul_of_nonneg_right
      ((hB₁ z hz).trans ((le_max_left _ _).trans (le_max_right _ _))) (norm_nonneg _))
  have hlower (z : Z) (hz : z ∈ K) (ξ : X) : ‖ξ‖ ≤ B * ‖Θ' z ξ‖ := by
    rw [(hΘeq z hz).eq_of_nhds]
    calc
      ‖ξ‖ = ‖(Θ z).inverse (Θ z ξ)‖ := by rw [(hinv z (hKV hz)).inverse_apply_self]
      _ ≤ ‖(Θ z).inverse‖ * ‖Θ z ξ‖ := (Θ z).inverse.le_opNorm _
      _ ≤ B * ‖Θ z ξ‖ := mul_le_mul_of_nonneg_right
        ((hB₂ z hz).trans ((le_max_right _ _).trans (le_max_right _ _))) (norm_nonneg _)
  obtain ⟨C, hC, hbound⟩ := exists_bound_symbol_comp_linear_frequency_global
    p' hp' φ' hφ' Θ' hΘ' m K hK hpbound B hB hupper hlower i j
  refine ⟨C, hC, fun z hz ξ ↦ ?_⟩
  have hlocal : (fun w η ↦ p' (φ' w) (Θ' w η)) =ᶠ[nhds z]
      (fun w η ↦ p (φ w) (Θ w η)) := by
    have hφat : ContinuousAt φ z := (hφ.contDiffAt (hV.mem_nhds (hKV hz))).continuousAt
    have hpφ := (hpeq z hz).comp_tendsto hφat
    filter_upwards [hφeq z hz, hΘeq z hz, hpφ] with w hw₁ hw₂ hw₃
    change p' (φ w) = p (φ w) at hw₃
    simp only [hw₁, hw₂, hw₃]
  have hder : (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ p' (φ' w) (Θ' w η)) ξ) =ᶠ[nhds z]
      (fun w ↦ iteratedFDeriv ℝ j (fun η ↦ p (φ w) (Θ w η)) ξ) := by
    filter_upwards [hlocal] with w hw
    rw [hw]
  rw [← (hder.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hbound z hz ξ

end AtiyahSinger

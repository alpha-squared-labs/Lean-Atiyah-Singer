/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanDeRhamSuspension
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compactly supported primitives below the top Euclidean degree

Public module ID: M1212.

Induction on the actual Euclidean dimension removes the lower-dimensional
tail of directional integration. A scalar cutoff extends a compactly
supported primitive of that tail; subtracting its exterior derivative keeps
the original differential unchanged and leaves support in a compact slab.
The degree-one case uses that a compactly supported closed zero-form on a
positive-dimensional Euclidean space is zero.

Source: the usual compact-support Poincaré lemma below top degree,
Bott--Tu, Chapter I. No ordinary Poincaré primitive is assumed to preserve
compact support, and no de Rham comparison theorem is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

set_option maxHeartbeats 2500000 in
-- The dimension induction retains the actual tail primitive and both compact support sets.
set_option maxRecDepth 5000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every closed compactly supported Euclidean form of positive degree below the dimension
has a smooth compactly supported primitive for the original exterior derivative. -/
theorem exists_smooth_compactlySupported_euclideanFormPrimitive (n p : ℕ)
    (hp : p + 1 < n)
    (α : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ)
    (hα : ContDiff ℝ ∞ α) (hcompact : HasCompactSupport α)
    (hclosed : ∀ x, extDeriv α x = 0) :
    ∃ η : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ ∀ x, extDeriv η x = α x := by
  classical
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    let V := EuclideanSpace ℝ (Fin (n + 1))
    let U := EuclideanSpace ℝ (Fin n)
    -- Use the actual first coordinate and the remaining original Euclidean coordinates.
    let e : V := EuclideanSpace.single 0 1
    let l : V →L[ℝ] ℝ := EuclideanSpace.proj 0
    let j : U →L[ℝ] V := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun k : Fin (n + 1) ↦
        Fin.cases (0 : U →L[ℝ] ℝ) (fun a ↦ EuclideanSpace.proj a) k))
    let q : V →L[ℝ] U := (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun k : Fin n ↦ EuclideanSpace.proj k.succ))
    have hle : l e = 1 := by
      change (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0 = 1
      simp
    have hlj (y : U) : l (j y) = 0 := rfl
    have hqe : q e = 0 := by
      ext k
      change (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) k.succ = 0
      simp
    have hqj (y : U) : q (j y) = y := by ext k; rfl
    have hsplit (x : V) : j (q x) = x - l x • e := by
      ext k
      refine Fin.cases ?_ (fun a ↦ ?_) k
      · change 0 = x 0 - x 0 * (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0
        simp
      · change x a.succ = x a.succ -
          x 0 * (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) a.succ
        simp
    obtain ⟨R, hR, hbound, η, hη, hdη, hbelow, hoff, θ, hθ, hθcompact, hdθ,
        hθslice, _, hupper⟩ :=
      exists_smooth_euclideanForm_tail p e l j q hle hlj hqe hqj hsplit α hα hcompact hclosed
    let S : ℝ := R + 2
    -- Construct a closed correction equal to the tail above the support and zero below it.
    have hcorrection :
        ∃ c : V → V [⋀^Fin p]→L[ℝ] ℂ, ContDiff ℝ ∞ c ∧
          (∀ x, extDeriv c x = 0) ∧
          (∀ x, l x < -S → c x = 0) ∧
          (∀ x, S < l x → c x = η x) ∧
          ∃ K : Set U, IsCompact K ∧ ∀ x, q x ∉ K → c x = 0 := by
      cases p with
      | zero =>
        -- A closed zero-form is constant; positive-dimensional Euclidean space is noncompact.
        have hn : 0 < n := by omega
        let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
        have hfd (y : U) : fderiv ℝ θ y = 0 := by
          apply ContinuousLinearMap.ext
          intro v
          apply ContinuousAlternatingMap.ext
          intro w
          have h := congrArg (fun a : U [⋀^Fin 1]→L[ℝ] ℂ ↦ a (fun _ ↦ v)) (hdθ y)
          change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ θ y)
            (fun _ ↦ v) = 0 at h
          rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply] at h
          change (∑ i : Fin 1, (-1 : ℤ) ^ i.val •
            (fderiv ℝ θ y v) (i.removeNth (fun _ : Fin 1 ↦ v))) = 0 at h
          rw [Fin.sum_univ_one] at h
          simp only [Fin.val_zero, pow_zero, one_smul] at h
          have hw : (0 : Fin 1).removeNth (fun _ : Fin 1 ↦ v) = w := by
            funext k
            exact Fin.elim0 k
          rw [hw] at h
          exact h
        obtain ⟨y₀, hy₀⟩ := (Set.ne_univ_iff_exists_notMem _).mp hθcompact.ne_univ
        have hθzero (y : U) : θ y = 0 :=
          (is_const_of_fderiv_eq_zero (hθ.differentiable (by simp)) hfd y y₀).trans
            (image_eq_zero_of_notMem_tsupport hy₀)
        refine ⟨0, contDiff_const, ?_, ?_, ?_, ∅, isCompact_empty, ?_⟩
        · intro x
          change ContinuousAlternatingMap.alternatizeUncurryFin
            (fderiv ℝ (fun _ : V ↦ (0 : V [⋀^Fin 0]→L[ℝ] ℂ)) x) = 0
          rw [fderiv_const_apply]
          exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ (n := 0)).map_zero
        · intro x _
          rfl
        · intro x hx
          rw [hupper x (by dsimp [S] at hx; linarith), hθzero]
          ext v
          rfl
        · intro x _
          rfl
      | succ p =>
        -- The tail lies below top degree in the lower-dimensional space, so induction applies.
        obtain ⟨ζ, hζ, hζcompact, hdζ⟩ := ih p (by omega) θ hθ hθcompact hdθ
        obtain ⟨χ, hχ, _, hχzero, hχone⟩ :=
          exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞))
            (isClosed_Iic : IsClosed (Iic (-R - 1)))
            (isClosed_Ici : IsClosed (Ici (R + 1)))
            (Set.disjoint_left.mpr (fun y hy₁ hy₂ ↦ by
              change y ≤ -R - 1 at hy₁
              change R + 1 ≤ y at hy₂
              linarith))
        let Q : (U [⋀^Fin p]→L[ℝ] ℂ) →L[ℝ] V [⋀^Fin p]→L[ℝ] ℂ :=
          ContinuousAlternatingMap.compContinuousLinearMapCLM q
        let ψ (x : V) : V [⋀^Fin p]→L[ℝ] ℂ := Q (ζ (q x))
        have hψ : ContDiff ℝ ∞ ψ := Q.contDiff.comp (hζ.comp q.contDiff)
        let f (x : V) : V [⋀^Fin p]→L[ℝ] ℂ := χ (l x) • ψ x
        have hf : ContDiff ℝ ∞ f := (hχ.comp l.contDiff).smul hψ
        let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ (n := p)
        let c (x : V) : V [⋀^Fin (p + 1)]→L[ℝ] ℂ := extDeriv f x
        have hc : ContDiff ℝ ∞ c := A.contDiff.comp (hf.fderiv_right (by simp))
        have hdc (x : V) : extDeriv c x = 0 := by
          have h := extDeriv_extDeriv hf (by simp : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω))
          exact congrFun h x
        have hdψ (x : V) : extDeriv ψ x = (θ (q x)).compContinuousLinearMap q := by
          have h := extDeriv_pullback (hζ.differentiable (by simp) (q x)) q.contDiff.contDiffAt
            (by simp : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω))
          have hq (y : V) : fderiv ℝ q y = q := q.hasFDerivAt.fderiv
          simp_rw [hq] at h
          exact h.trans (congrArg (fun a : U [⋀^Fin (p + 1)]→L[ℝ] ℂ ↦
            a.compContinuousLinearMap q) (hdζ (q x)))
        have hlocalZero (x : V) (h : f =ᶠ[𝓝 x] (fun _ ↦ 0)) : c x = 0 := by
          change extDeriv f x = 0
          rw [h.extDeriv_eq]
          change ContinuousAlternatingMap.alternatizeUncurryFin
            (fderiv ℝ (fun _ : V ↦ (0 : V [⋀^Fin p]→L[ℝ] ℂ)) x) = 0
          rw [fderiv_const_apply]
          exact A.map_zero
        refine ⟨c, hc, hdc, ?_, ?_, tsupport ζ, hζcompact, ?_⟩
        · intro x hx
          apply hlocalZero
          have hlx : l x < -R - 1 := by
            dsimp [S] at hx
            linarith
          have hnear : ∀ᶠ y in 𝓝 x, l y < -R - 1 :=
            (isOpen_lt l.continuous continuous_const).mem_nhds hlx
          filter_upwards [hnear] with y hy
          change χ (l y) • ψ y = 0
          rw [(hχzero (l y)).mp hy.le, zero_smul]
        · intro x hx
          have hlx : R + 1 < l x := by
            dsimp [S] at hx
            linarith
          have hnear : ∀ᶠ y in 𝓝 x, R + 1 < l y :=
            (isOpen_lt continuous_const l.continuous).mem_nhds hlx
          have heq : f =ᶠ[𝓝 x] ψ := by
            filter_upwards [hnear] with y hy
            change χ (l y) • ψ y = ψ y
            rw [(hχone (l y)).mp hy.le, one_smul]
          change extDeriv f x = η x
          rw [heq.extDeriv_eq, hdψ]
          exact (hupper x (by dsimp [S] at hx; linarith)).symm
        · intro x hx
          apply hlocalZero
          have hnear : ∀ᶠ y in 𝓝 x, q y ∉ tsupport ζ :=
            q.continuous.continuousAt.preimage_mem_nhds
              ((isClosed_tsupport ζ).isOpen_compl.mem_nhds hx)
          filter_upwards [hnear] with y hy
          have hψzero : ψ y = 0 := by
            change Q (ζ (q y)) = 0
            rw [image_eq_zero_of_notMem_tsupport hy, map_zero]
          change χ (l y) • ψ y = 0
          rw [hψzero, smul_zero]
    obtain ⟨c, hc, hdc, hcbelow, hcabove, K, hK, hcoff⟩ := hcorrection
    let μ : V → V [⋀^Fin p]→L[ℝ] ℂ := η - c
    have hμ : ContDiff ℝ ∞ μ := hη.sub hc
    have hdμ (x : V) : extDeriv μ x = α x := by
      let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ (n := p)
      change A (fderiv ℝ (η - c) x) = α x
      rw [fderiv_sub (hη.differentiable (by simp) x) (hc.differentiable (by simp) x), map_sub]
      exact (congrArg₂ (· - ·) (hdη x) (hdc x)).trans (sub_zero _)
    -- The corrected form is supported in one compact slab over two specified compact supports.
    let L : Set U := q '' tsupport α ∪ K
    have hL : IsCompact L := (hcompact.image q.continuous).union hK
    let slab : Set V := (fun z : ℝ × U ↦ z.1 • e + j z.2) '' (Icc (-S) S ×ˢ L)
    have hslab : IsCompact slab :=
      (isCompact_Icc.prod hL).image
        ((continuous_fst.smul continuous_const).add (j.continuous.comp continuous_snd))
    have hsupp : Function.support μ ⊆ slab := by
      intro x hx
      have hlow : -S ≤ l x := by
        by_contra h
        have hlx : l x < -S := lt_of_not_ge h
        have hηzero := hbelow x (by dsimp [S] at hlx; linarith)
        have hczero := hcbelow x hlx
        apply hx
        change η x - c x = 0
        rw [hηzero, hczero, sub_self]
      have hhigh : l x ≤ S := by
        by_contra h
        have hcx := hcabove x (lt_of_not_ge h)
        apply hx
        change η x - c x = 0
        rw [hcx, sub_self]
      have hproj : q x ∈ L := by
        by_contra h
        have hαoff : q x ∉ q '' tsupport α := fun hx ↦ h (Or.inl hx)
        have hKoff : q x ∉ K := fun hx ↦ h (Or.inr hx)
        apply hx
        change η x - c x = 0
        rw [hoff x hαoff, hcoff x hKoff, sub_self]
      refine ⟨(l x, q x), ⟨⟨hlow, hhigh⟩, hproj⟩, ?_⟩
      change l x • e + j (q x) = x
      rw [hsplit]
      module
    have hμcompact : HasCompactSupport μ :=
      hslab.of_isClosed_subset (isClosed_tsupport μ) (closure_minimal hsupp hslab.isClosed)
    exact ⟨μ, hμ, hμcompact, hdμ⟩

end AtiyahSinger

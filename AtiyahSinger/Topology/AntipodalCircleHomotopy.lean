/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CircleMatrixLoop
public import AtiyahSinger.Topology.PairedInvolutionPathHomotopy

/-!
# Antipodal extension of paths and bundle homotopies

Public module ID: M1526.

A path from x to its image under a continuous involution extends over the circle
by the same involution on the second half. The interval quotient retains the
positive parametrization exp(i*pi*t), including both sewing points. This is the
topological gluing needed for the paired-involution contraction on a punctured
complex line. The final theorem contracts the conjugated and original boundary
maps with the same doubled actions and constant intertwiner. Both forward
and inverse continuity are retained in the original bundle-sum topology.

Sources: the interval quotient of the circle, the existing paired-involution
path theorem, and radial normalization. No Bott or index theorem is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

/-- A path with involutive endpoint sewing extends to an antipodally equivariant circle map. -/
theorem exists_antipodal_circleMap_of_path {X : Type*} [TopologicalSpace X]
    (J : X → X) (hJ : Continuous J) (hJJ : Function.Involutive J)
    (x : X) (p : Path x (J x)) :
    ∃ f : C(Circle, X),
      (∀ t : I, f (Circle.exp (Real.pi * (t : ℝ))) = p t) ∧
      ∀ z : Circle, f (-z) = J (f z) := by
  -- Traverse the given half and its involutive image before descending the endpoint quotient.
  let q : Path (J x) x := {
    toFun := fun t ↦ J (p t)
    continuous_toFun := hJ.comp p.continuous
    source' := by rw [p.source]
    target' := by rw [p.target, hJJ] }
  obtain ⟨f, hf, hpath⟩ := exists_circleMap_of_path x (p.trans q)
  have hfull (t : I) : f (Circle.exp (2 * Real.pi * (t : ℝ))) = (p.trans q) t :=
    congrArg (fun γ : Path x x ↦ γ t) hpath
  have hpi : Circle.exp Real.pi = -1 := by
    apply Circle.ext
    simp [Circle.coe_exp, Complex.exp_pi_mul_I]
  have hshift (a : ℝ) : Circle.exp (a + Real.pi) = -Circle.exp a := by
    rw [Circle.exp_add, hpi, mul_neg_one]
  have hupper (t : I) : f (Circle.exp (Real.pi * (t : ℝ))) = p t := by
    let u : I := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
    have hu : (u : ℝ) ≤ 1 / 2 := by dsimp [u]; linarith [t.property.2]
    have hangle : Real.pi * (t : ℝ) = 2 * Real.pi * (u : ℝ) := by dsimp [u]; ring
    rw [hangle, hfull]
    calc
      (p.trans q) u = (p.trans q).extend (u : ℝ) := (Path.extend_apply _ u.property).symm
      _ = p.extend (2 * (u : ℝ)) := Path.extend_trans_of_le_half p q hu
      _ = p t := by
        have hu' : 2 * (u : ℝ) = (t : ℝ) := by dsimp [u]; ring
        rw [hu', Path.extend_apply]
  have hlower (t : I) : f (-Circle.exp (Real.pi * (t : ℝ))) = J (p t) := by
    let u : I := ⟨((t : ℝ) + 1) / 2,
      by constructor <;> linarith [t.property.1, t.property.2]⟩
    have hu : 1 / 2 ≤ (u : ℝ) := by dsimp [u]; linarith [t.property.1]
    have hangle : Real.pi * (t : ℝ) + Real.pi = 2 * Real.pi * (u : ℝ) := by
      dsimp [u]
      ring
    rw [← hshift, hangle, hfull]
    calc
      (p.trans q) u = (p.trans q).extend (u : ℝ) := (Path.extend_apply _ u.property).symm
      _ = q.extend (2 * (u : ℝ) - 1) := Path.extend_trans_of_half_le p q hu
      _ = J (p t) := by
        have hu' : 2 * (u : ℝ) - 1 = (t : ℝ) := by dsimp [u]; ring
        rw [hu', Path.extend_apply]
        rfl
  -- Every circle point lies in one of the same two closed parametrized semicircles.
  have hcover (z : Circle) : ∃ t : I,
      z = Circle.exp (Real.pi * (t : ℝ)) ∨ z = -Circle.exp (Real.pi * (t : ℝ)) := by
    by_cases hz : 0 ≤ Complex.arg (z : ℂ)
    · let t : I := ⟨Complex.arg (z : ℂ) / Real.pi,
        div_nonneg hz Real.pi_pos.le, (div_le_one Real.pi_pos).mpr (Complex.arg_le_pi _)⟩
      refine ⟨t, Or.inl ?_⟩
      have ht : Real.pi * (t : ℝ) = Complex.arg (z : ℂ) := by
        dsimp [t]
        field_simp
      rw [ht, Circle.exp_arg]
    · let t : I := ⟨(Complex.arg (z : ℂ) + Real.pi) / Real.pi,
        div_nonneg (by linarith [Complex.neg_pi_lt_arg (z : ℂ)]) Real.pi_pos.le,
        (div_le_one Real.pi_pos).mpr (by linarith)⟩
      refine ⟨t, Or.inr ?_⟩
      have ht : Real.pi * (t : ℝ) = Complex.arg (z : ℂ) + Real.pi := by
        dsimp [t]
        field_simp
      rw [ht, hshift, Circle.exp_arg, neg_neg]
  refine ⟨f, hupper, ?_⟩
  intro z
  obtain ⟨t, hz | hz⟩ := hcover z
  · rw [hz, hlower, hupper]
  · rw [hz, neg_neg, hupper, hlower, hJJ]

open Bundle ComplexBundle Metric

attribute [local instance] trivialTopology sumTopology

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000 in
-- Descend both continuous inverse maps, then verify the original radial boundary at all points.
/-- The paired boundary of a radial antipodal isomorphism contracts equivariantly. -/
theorem exists_antipodal_paired_homotopy_of_radial_iso {r q : ℕ}
    (A : (Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ))
    (B : (Fin q → ℂ) ≃ₗ[ℂ] (Fin q → ℂ))
    (hA : Function.Involutive A) (hB : Function.Involutive B)
    (a : Iso (Trivial {z : ℂ // z ≠ 0} (Fin r → ℂ))
      (Trivial {z : ℂ // z ≠ 0} (Fin q → ℂ)))
    (hradial : ∀ (c : ℝ) (hc : 0 < c) (z : {z : ℂ // z ≠ 0}) (u : Fin r → ℂ),
      a.linearEquiv ⟨c • z.val, smul_ne_zero hc.ne' z.property⟩ u = a.linearEquiv z u)
    (hanti : ∀ (z : {z : ℂ // z ≠ 0}) (u : Fin r → ℂ),
      a.linearEquiv ⟨-z.val, neg_ne_zero.mpr z.property⟩ (A u) = B (a.linearEquiv z u)) :
    ∃ H : Iso
        (Trivial (I × {z : ℂ // z ≠ 0}) (Fin r → ℂ) ×ᵇ
          Trivial (I × {z : ℂ // z ≠ 0}) (Fin r → ℂ))
        (Trivial (I × {z : ℂ // z ≠ 0}) (Fin q → ℂ) ×ᵇ
          Trivial (I × {z : ℂ // z ≠ 0}) (Fin q → ℂ)),
      ∃ e : ((Fin r → ℂ) × (Fin r → ℂ)) ≃ₗ[ℂ] ((Fin q → ℂ) × (Fin q → ℂ)),
        (∀ (z : {z : ℂ // z ≠ 0}) v,
          H.linearEquiv (0, z) v =
            (a.linearEquiv ⟨star z.val, star_ne_zero.mpr z.property⟩ v.1,
              a.linearEquiv z v.2)) ∧
        (∀ (z : {z : ℂ // z ≠ 0}) v, H.linearEquiv (1, z) v = e v) ∧
        (∀ (t : I) (z : {z : ℂ // z ≠ 0}) v,
          H.linearEquiv (t, ⟨-z.val, neg_ne_zero.mpr z.property⟩) (A v.1, -A v.2) =
            (B (H.linearEquiv (t, z) v).1, -B (H.linearEquiv (t, z) v).2)) ∧
        ∀ v, e (A v.1, -A v.2) = (B (e v).1, -B (e v).2) := by
  classical
  let Z := {z : ℂ // z ≠ 0}
  let U := Fin r → ℂ
  let W := Fin q → ℂ
  let UU := U × U
  let WW := W × W
  let LE := UU ≃ₗ[ℂ] WW
  let negZ (z : Z) : Z := ⟨-z.val, neg_ne_zero.mpr z.property⟩
  let starZ (z : Z) : Z := ⟨star z.val, star_ne_zero.mpr z.property⟩
  let circleZ (z : Circle) : Z := ⟨z, z.coe_ne_zero⟩
  let upper : C(I, Z) := ⟨fun t ↦ circleZ (Circle.exp (Real.pi * (t : ℝ))), by
    exact (continuous_subtype_val.comp
      (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))).subtype_mk _⟩
  have hpi : Circle.exp Real.pi = -1 := by
    apply Circle.ext
    simp [Circle.coe_exp, Complex.exp_pi_mul_I]
  have hshift (s : ℝ) : Circle.exp (s + Real.pi) = -Circle.exp s := by
    rw [Circle.exp_add, hpi, mul_neg_one]
  -- Read the same bundle map and its inverse in their original product topologies.
  have hac : Continuous (fun z : Z × U ↦ a.linearEquiv z.1 z.2) := by
    have hin : Continuous (fun z : Z × U ↦
        (⟨z.1, z.2⟩ : TotalSpace Unit (Trivial Z U))) :=
      continuous_induced_rng.mpr continuous_id
    exact (continuous_induced_dom.comp (a.continuous_total.comp hin)).snd
  have hai : Continuous (fun z : Z × W ↦ (a.linearEquiv z.1).symm z.2) := by
    have hin : Continuous (fun z : Z × W ↦
        (⟨z.1, z.2⟩ : TotalSpace Unit (Trivial Z W))) :=
      continuous_induced_rng.mpr continuous_id
    exact (continuous_induced_dom.comp (a.continuous_symm.comp hin)).snd
  have hpc : Continuous (fun z : I × U ↦ a.linearEquiv (upper z.1) z.2) :=
    hac.comp (upper.continuous.prodMap continuous_id)
  have hpic : Continuous (fun z : I × W ↦ (a.linearEquiv (upper z.1)).symm z.2) :=
    hai.comp (upper.continuous.prodMap continuous_id)
  have hpcoords : Continuous (fun z : TotalSpace Unit (Trivial I U) ↦
      ((z.proj, z.snd) : I × U)) := continuous_induced_dom
  have hpicoords : Continuous (fun z : TotalSpace Unit (Trivial I W) ↦
      ((z.proj, z.snd) : I × W)) := continuous_induced_dom
  let p : Iso (Trivial I U) (Trivial I W) := {
    linearEquiv t := a.linearEquiv (upper t)
    continuous_total := continuous_induced_rng.mpr
      (hpcoords.fst.prodMk (hpc.comp hpcoords))
    continuous_symm := continuous_induced_rng.mpr
      (hpicoords.fst.prodMk (hpic.comp hpicoords)) }
  have hu : upper 1 = negZ (upper 0) := by
    apply Subtype.ext
    simp [upper, circleZ, negZ]
  have hp (v : U) : p.linearEquiv 1 v = B (p.linearEquiv 0 (A v)) := by
    have hv := hanti (upper 0) (A v)
    rw [hA] at hv
    change a.linearEquiv (upper 1) v = _
    rw [hu]
    exact hv
  obtain ⟨K, e, hK0, hK1, hKsew, he⟩ :=
    exists_paired_involution_path_homotopy A B hA hB p hp
  -- These coordinate maps retain the existing doubled trivial-bundle topology.
  have hcoords (Y : Type) [TopologicalSpace Y] (m : ℕ) : Continuous
      (fun z : TotalSpace Unit (Trivial Y (Fin m → ℂ) ×ᵇ Trivial Y (Fin m → ℂ)) ↦
        ((z.proj, z.snd) : Y × ((Fin m → ℂ) × (Fin m → ℂ)))) := by
    have hd : Continuous (fun z : TotalSpace Unit
        (Trivial Y (Fin m → ℂ) ×ᵇ Trivial Y (Fin m → ℂ)) ↦
          ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit (Trivial Y (Fin m → ℂ))),
            (⟨z.proj, z.snd.2⟩ : TotalSpace Unit (Trivial Y (Fin m → ℂ))))) :=
      continuous_induced_dom
    have hl := continuous_induced_dom.comp hd.fst
    have hr := continuous_induced_dom.comp hd.snd
    exact hl.fst.prodMk (hl.snd.prodMk hr.snd)
  have hin (Y : Type) [TopologicalSpace Y] (m : ℕ) : Continuous
      (fun z : Y × ((Fin m → ℂ) × (Fin m → ℂ)) ↦
        (⟨z.1, z.2⟩ : TotalSpace Unit
          (Trivial Y (Fin m → ℂ) ×ᵇ Trivial Y (Fin m → ℂ)))) := by
    apply continuous_induced_rng.mpr
    exact (continuous_induced_rng.mpr (continuous_fst.prodMk continuous_snd.fst)).prodMk
      (continuous_induced_rng.mpr (continuous_fst.prodMk continuous_snd.snd))
  let kmap (st : I × I) : LE := K.linearEquiv st
  let kval : (I × I) × UU → WW := fun z ↦ kmap z.1 z.2
  let kinv : (I × I) × WW → UU := fun z ↦ (kmap z.1).symm z.2
  have hKc : Continuous kval := by
    simpa only [kval, kmap, Function.comp_apply] using
      ((hcoords (I × I) q).comp (K.continuous_total.comp (hin (I × I) r))).snd
  have hKi : Continuous kinv := by
    simpa only [kinv, kmap, Function.comp_apply] using
      ((hcoords (I × I) r).comp (K.continuous_symm.comp (hin (I × I) q))).snd
  let KA : UU ≃ₗ[ℂ] UU := A.prodCongr (A.trans (LinearEquiv.neg ℂ))
  let KB : WW ≃ₗ[ℂ] WW := B.prodCongr (B.trans (LinearEquiv.neg ℂ))
  have hka : Function.Involutive KA := by
    intro v
    apply Prod.ext
    · exact hA v.1
    · change -A (-A v.2) = v.2
      rw [map_neg, neg_neg, hA]
  have hkb : Function.Involutive KB := by
    intro v
    apply Prod.ext
    · exact hB v.1
    · change -B (-B v.2) = v.2
      rw [map_neg, neg_neg, hB]
  have hkas : KA.symm = KA := by
    apply LinearEquiv.ext
    intro v
    apply KA.injective
    rw [KA.apply_symm_apply, hka]
  have hkbs : KB.symm = KB := by
    apply LinearEquiv.ext
    intro v
    apply KB.injective
    rw [KB.apply_symm_apply, hkb]
  -- Descend forward and inverse maps together in standard compact-open function spaces.
  let Maps := C(UU, WW) × C(WW, UU)
  let ofLE (d : LE) : Maps :=
    (⟨d, d.toLinearMap.continuous_of_finiteDimensional⟩,
      ⟨d.symm, d.symm.toLinearMap.continuous_of_finiteDimensional⟩)
  let ca : C(UU, UU) := ⟨KA, KA.toLinearMap.continuous_of_finiteDimensional⟩
  let cb : C(WW, WW) := ⟨KB, KB.toLinearMap.continuous_of_finiteDimensional⟩
  let j : C(Maps, Maps) := {
    toFun d := ((cb.comp d.1).comp ca, (ca.comp d.2).comp cb)
    continuous_toFun :=
      ((ContinuousMap.continuous_precomp ca).comp
        ((ContinuousMap.continuous_postcomp cb).comp continuous_fst)).prodMk
      ((ContinuousMap.continuous_precomp cb).comp
        ((ContinuousMap.continuous_postcomp ca).comp continuous_snd)) }
  have hjj : Function.Involutive j := by
    intro d
    apply Prod.ext
    · apply ContinuousMap.ext
      intro v
      change KB (KB (d.1 (KA (KA v)))) = d.1 v
      rw [hka, hkb]
    · apply ContinuousMap.ext
      intro v
      change KA (KA (d.2 (KB (KB v)))) = d.2 v
      rw [hkb, hka]
  have hjLE (d : LE) : j (ofLE d) = ofLE (KA.trans (d.trans KB)) := by
    apply Prod.ext
    · apply ContinuousMap.ext
      intro v
      rfl
    · apply ContinuousMap.ext
      intro v
      change KA (d.symm (KB v)) = KA.symm (d.symm (KB.symm v))
      rw [hkas, hkbs]
  let m : C(I × I, Maps) := {
    toFun st := ofLE (K.linearEquiv st)
    continuous_toFun :=
      (ContinuousMap.curry ⟨_, hKc⟩).continuous.prodMk
        (ContinuousMap.curry ⟨_, hKi⟩).continuous }
  have hsew (s : I) : m (s, 1) = j (m (s, 0)) := by
    have hd : K.linearEquiv (s, 1) = KA.trans ((K.linearEquiv (s, 0)).trans KB) := by
      apply LinearEquiv.ext
      intro v
      have hv := hKsew s (KA v)
      change K.linearEquiv (s, 1) (KA (KA v)) = KB (K.linearEquiv (s, 0) (KA v)) at hv
      rw [hka] at hv
      exact hv
    change ofLE (K.linearEquiv (s, 1)) = j (ofLE (K.linearEquiv (s, 0)))
    rw [hd, hjLE]
  let cur : C(I, C(I, Maps)) :=
    (⟨fun ts : I × I ↦ m (ts.2, ts.1), m.continuous.comp continuous_swap⟩ :
      C(I × I, Maps)).curry
  let J : C(I, Maps) → C(I, Maps) := fun f ↦ j.comp f
  have hJ : Continuous J := ContinuousMap.continuous_postcomp j
  have hJJ : Function.Involutive J := by
    intro f
    apply ContinuousMap.ext
    intro s
    exact hjj (f s)
  let P : Path (cur 0) (J (cur 0)) := {
    toContinuousMap := cur
    source' := rfl
    target' := by
      apply ContinuousMap.ext
      intro s
      exact hsew s }
  obtain ⟨F, hFup, hFant⟩ := exists_antipodal_circleMap_of_path J hJ hJJ (cur 0) P
  let f : C(I × Circle, Maps) :=
    ⟨fun sz ↦ F sz.2 sz.1, F.uncurry.continuous.comp continuous_swap⟩
  have hfup (s t : I) : f (s, Circle.exp (Real.pi * (t : ℝ))) =
      ofLE (K.linearEquiv (s, t)) :=
    congrArg (fun d : C(I, Maps) ↦ d s) (hFup t)
  have hfant (s : I) (z : Circle) : f (s, -z) = j (f (s, z)) :=
    congrArg (fun d : C(I, Maps) ↦ d s) (hFant z)
  have hcover (z : Circle) : ∃ t : I,
      z = Circle.exp (Real.pi * (t : ℝ)) ∨ z = -Circle.exp (Real.pi * (t : ℝ)) := by
    by_cases hz : 0 ≤ Complex.arg (z : ℂ)
    · let t : I := ⟨Complex.arg (z : ℂ) / Real.pi,
        div_nonneg hz Real.pi_pos.le, (div_le_one Real.pi_pos).mpr (Complex.arg_le_pi _)⟩
      refine ⟨t, Or.inl ?_⟩
      have ht : Real.pi * (t : ℝ) = Complex.arg (z : ℂ) := by dsimp [t]; field_simp
      rw [ht, Circle.exp_arg]
    · let t : I := ⟨(Complex.arg (z : ℂ) + Real.pi) / Real.pi,
        div_nonneg (by linarith [Complex.neg_pi_lt_arg (z : ℂ)]) Real.pi_pos.le,
        (div_le_one Real.pi_pos).mpr (by linarith)⟩
      refine ⟨t, Or.inr ?_⟩
      have ht : Real.pi * (t : ℝ) = Complex.arg (z : ℂ) + Real.pi := by
        dsimp [t]
        field_simp
      rw [ht, hshift, Circle.exp_arg, neg_neg]
  have hfLE (s : I) (z : Circle) : ∃ d : LE, f (s, z) = ofLE d := by
    obtain ⟨t, hz | hz⟩ := hcover z
    · refine ⟨K.linearEquiv (s, t), ?_⟩
      rw [hz, hfup]
    · refine ⟨KA.trans ((K.linearEquiv (s, t)).trans KB), ?_⟩
      rw [hz, hfant, hfup, hjLE]
  let E (s : I) (z : Circle) : LE := Classical.choose (hfLE s z)
  have hE (s : I) (z : Circle) : f (s, z) = ofLE (E s z) :=
    Classical.choose_spec (hfLE s z)
  have hEup (s t : I) : E s (Circle.exp (Real.pi * (t : ℝ))) =
      K.linearEquiv (s, t) := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun d : Maps ↦ d.1 v) ((hE _ _).symm.trans (hfup s t))
  have hEant (s : I) (z : Circle) : E s (-z) = KA.trans ((E s z).trans KB) := by
    apply LinearEquiv.ext
    intro v
    have hd := (hE s (-z)).symm.trans ((hfant s z).trans
      ((congrArg j (hE s z)).trans (hjLE (E s z))))
    exact congrArg (fun d : Maps ↦ d.1 v) hd
  have hEc : Continuous (fun z : (I × Circle) × UU ↦ E z.1.1 z.1.2 z.2) := by
    have hc : Continuous (fun z : (I × Circle) × UU ↦ (f z.1).1 z.2) :=
      (f.continuous.comp continuous_fst).fst.eval continuous_snd
    exact hc.congr (fun z ↦ congrArg (fun d : Maps ↦ d.1 z.2) (hE z.1.1 z.1.2))
  have hEi : Continuous (fun z : (I × Circle) × WW ↦ (E z.1.1 z.1.2).symm z.2) := by
    have hc : Continuous (fun z : (I × Circle) × WW ↦ (f z.1).2 z.2) :=
      (f.continuous.comp continuous_fst).snd.eval continuous_snd
    exact hc.congr (fun z ↦ congrArg (fun d : Maps ↦ d.2 z.2) (hE z.1.1 z.1.2))
  -- Identify the entire initial and final circles using the original antipodal boundary.
  have hanti' (z : Z) (u : U) : a.linearEquiv (negZ z) u = B (a.linearEquiv z (A u)) := by
    simpa only [hA u] using hanti z (A u)
  have hstarup (t : I) : starZ (upper t) = negZ (upper (unitInterval.symm t)) := by
    apply Subtype.ext
    have hc : (Circle.exp (Real.pi * (t : ℝ)))⁻¹ =
        -Circle.exp (Real.pi * (unitInterval.symm t : ℝ)) := by
      rw [← Circle.exp_neg]
      have ht : -(Real.pi * (t : ℝ)) =
          Real.pi * (unitInterval.symm t : ℝ) - Real.pi := by
        rw [unitInterval.coe_symm_eq]
        ring
      rw [ht, Circle.exp_sub, hpi]
      apply Circle.ext
      simp [div_neg_eq_neg_div]
    exact (Circle.coe_inv_eq_conj _).symm.trans
      ((congrArg (fun z : Circle ↦ (z : ℂ)) hc).trans (Circle.coe_neg _))
  have hE0up (t : I) (v : UU) : E 0 (Circle.exp (Real.pi * (t : ℝ))) v =
      (a.linearEquiv (starZ (upper t)) v.1, a.linearEquiv (upper t) v.2) := by
    rw [hEup, hK0, hstarup, hanti']
  have hE0 (z : Circle) (v : UU) : E 0 z v =
      (a.linearEquiv (starZ (circleZ z)) v.1, a.linearEquiv (circleZ z) v.2) := by
    obtain ⟨t, hz | hz⟩ := hcover z
    · rw [hz]
      exact hE0up t v
    · rw [hz, hEant]
      change KB (E 0 (Circle.exp (Real.pi * (t : ℝ))) (KA v)) = _
      rw [hE0up]
      have hs : starZ (circleZ (-Circle.exp (Real.pi * (t : ℝ)))) =
          negZ (starZ (upper t)) := by apply Subtype.ext; simp [starZ, negZ, circleZ, upper]
      change (B (a.linearEquiv (starZ (upper t)) (A v.1)),
        -B (a.linearEquiv (upper t) (-A v.2))) = _
      rw [hs]
      change _ = (a.linearEquiv (negZ (starZ (upper t))) v.1,
        a.linearEquiv (negZ (upper t)) v.2)
      rw [hanti', hanti', map_neg, map_neg, neg_neg]
  have hE1 (z : Circle) (v : UU) : E 1 z v = e v := by
    obtain ⟨t, hz | hz⟩ := hcover z
    · rw [hz, hEup, hK1]
    · rw [hz, hEant]
      change KB (E 1 (Circle.exp (Real.pi * (t : ℝ))) (KA v)) = e v
      rw [hEup, hK1]
      have hev : e (KA v) = KB (e v) := he v
      rw [hev, hkb]
  -- Radial normalization is continuous off zero and commutes with the same antipodal action.
  have hNmem (z : Z) : ‖z.val‖⁻¹ • z.val ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    simp [norm_ne_zero_iff.mpr z.property]
  let N : C(Z, Circle) := {
    toFun z := ⟨‖z.val‖⁻¹ • z.val, hNmem z⟩
    continuous_toFun := ((continuous_subtype_val.norm.inv₀
      (fun z : Z ↦ norm_ne_zero_iff.mpr z.property)).smul continuous_subtype_val).subtype_mk
        hNmem }
  have hNneg (z : Z) : N (negZ z) = -(N z) := by
    apply Circle.ext
    simp [N, negZ]
  have hradN (z : Z) (u : U) : a.linearEquiv (circleZ (N z)) u = a.linearEquiv z u :=
    hradial ‖z.val‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr z.property)) z u
  have hradStar (z : Z) (u : U) :
      a.linearEquiv (starZ (circleZ (N z))) u = a.linearEquiv (starZ z) u := by
    have hs : starZ (circleZ (N z)) =
        (⟨‖z.val‖⁻¹ • (starZ z).val,
          smul_ne_zero (inv_pos.mpr (norm_pos_iff.mpr z.property)).ne'
            (starZ z).property⟩ : Z) := by
      apply Subtype.ext
      simp [starZ, circleZ, N]
    rw [hs]
    exact hradial ‖z.val‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr z.property)) (starZ z) u
  have hLc : Continuous (fun z : (I × Z) × UU ↦ E z.1.1 (N z.1.2) z.2) :=
    hEc.comp ((continuous_fst.fst.prodMk
      (N.continuous.comp continuous_fst.snd)).prodMk continuous_snd)
  have hLi : Continuous (fun z : (I × Z) × WW ↦ (E z.1.1 (N z.1.2)).symm z.2) :=
    hEi.comp ((continuous_fst.fst.prodMk
      (N.continuous.comp continuous_fst.snd)).prodMk continuous_snd)
  let H : Iso (Trivial (I × Z) U ×ᵇ Trivial (I × Z) U)
      (Trivial (I × Z) W ×ᵇ Trivial (I × Z) W) := {
    linearEquiv tz := E tz.1 (N tz.2)
    continuous_total := (hin (I × Z) q).comp
      ((continuous_fst.prodMk hLc).comp (hcoords (I × Z) r))
    continuous_symm := (hin (I × Z) r).comp
      ((continuous_fst.prodMk hLi).comp (hcoords (I × Z) q)) }
  refine ⟨H, e, ?_, ?_, ?_, he⟩
  · intro z v
    change E 0 (N z) v = _
    rw [hE0, hradStar, hradN]
  · intro z v
    exact hE1 (N z) v
  · intro t z v
    change E t (N (negZ z)) (KA v) = KB (E t (N z) v)
    rw [hNneg, hEant]
    change KB (E t (N z) (KA (KA v))) = _
    rw [hka]

end AtiyahSinger

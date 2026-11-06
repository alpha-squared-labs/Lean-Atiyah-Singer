/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularOpenExcision
public import AtiyahSinger.Topology.RelativeSingularTriple
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Homotopies of local pairs and differentiable linearization

Public module ID: M1940.

Homotopies preserving the specified subspaces induce equal maps on the original
relative singular homology. The cylinder projection is compared through the
absolute homology of both spaces and subspaces, so the result retains the actual
chain quotient maps. This is the relative homotopy invariance argument used for
local degree and orientation, as in Hatcher, sections 2.1 and 3.3.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A homotopy preserving the given subspaces preserves their original relative homology maps. -/
theorem relativeSingularHomologyMap_eq_of_homotopy
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : f.Homotopy g) (hH : ∀ t : unitInterval, ∀ x ∈ A, H (t, x) ∈ B) (k : ℕ) :
    relativeSingularHomologyMap R f hf k = relativeSingularHomologyMap R g hg k := by
  let D : Set (unitInterval × X) := Prod.snd ⁻¹' A
  let p : C(unitInterval × X, X) := ⟨Prod.snd, continuous_snd⟩
  let s (t : unitInterval) : C(X, unitInterval × X) :=
    ⟨fun x ↦ (t, x), by fun_prop⟩
  have hp : Set.MapsTo p D A := fun _ hx ↦ hx
  have hs (t : unitInterval) : Set.MapsTo (s t) A D := fun _ hx ↦ hx
  have hsp : ((s 0).comp p).Homotopic (ContinuousMap.id (unitInterval × X)) := by
    refine ⟨{ toFun z := (z.1 * z.2.1, z.2.2)
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      simp [s, p]
    · intro z
      simp
  have hps : (p.comp (s 0)).Homotopic (ContinuousMap.id X) := by
    have h : p.comp (s 0) = ContinuousMap.id X := rfl
    rw [h]
  let pA : C(D, A) := ⟨fun z ↦ ⟨z.val.2, z.property⟩, by fun_prop⟩
  let sA : C(A, D) := ⟨fun x ↦ ⟨(0, x.val), x.property⟩, by fun_prop⟩
  have hspA : (sA.comp pA).Homotopic (ContinuousMap.id D) := by
    refine ⟨{ toFun z := ⟨(z.1 * z.2.val.1, z.2.val.2), z.2.property⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      simp [sA, pA]
    · intro z
      apply Subtype.ext
      simp
  have hpsA : (pA.comp sA).Homotopic (ContinuousMap.id A) := by
    have h : pA.comp sA = ContinuousMap.id A := rfl
    rw [h]
  let P := relativeSingularHomologyMap R p hp k
  let : IsIso P := isIso_relativeSingularHomologyMap_of_absolute R p hp
    (fun j ↦ isIso_singularHomologyMap_of_homotopyInverse R p (s 0) hsp hps j)
    (fun j ↦ isIso_singularHomologyMap_of_homotopyInverse R pA sA hspA hpsA j) k
  -- Both ends of the same cylinder are inverse to its projection on relative homology.
  have hright (t : unitInterval) : relativeSingularHomologyMap R (s t) (hs t) k ≫ P = 𝟙 _ := by
    change HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k = _
    rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
    have heq : p.comp (s t) = ContinuousMap.id X := rfl
    generalize_proofs at *
    generalize hfun : p.comp (s t) = q at *
    clear hfun
    subst q
    simp [relativeSingularChainsMap, cokernel.map]
  have hends : relativeSingularHomologyMap R (s 0) (hs 0) k =
      relativeSingularHomologyMap R (s 1) (hs 1) k := by
    apply (cancel_mono P).mp
    rw [hright, hright]
  let h : C(unitInterval × X, Y) := H.toContinuousMap
  have hh : Set.MapsTo h D B := fun z hz ↦ hH z.1 z.2 hz
  have hcomp (t : unitInterval) :
      relativeSingularHomologyMap R (h.comp (s t)) (hh.comp (hs t)) k =
        relativeSingularHomologyMap R (s t) (hs t) k ≫
          relativeSingularHomologyMap R h hh k := by
    exact congrArg (fun F ↦ HomologicalComplex.homologyMap F k)
      (relativeSingularChainsMap_comp R (s t) h (hs t) hh) |>.trans
        (HomologicalComplex.homologyMap_comp _ _ _)
  have hzero : h.comp (s 0) = f := by ext x; exact H.map_zero_left x
  have hone : h.comp (s 1) = g := by ext x; exact H.map_one_left x
  have heq := (hcomp 0).trans ((congrArg (fun F ↦ F ≫
    relativeSingularHomologyMap R h hh k) hends).trans (hcomp 1).symm)
  generalize_proofs at *
  generalize hfun₀ : h.comp (s 0) = f₀ at *
  generalize hfun₁ : h.comp (s 1) = f₁ at *
  clear hfun₀ hfun₁
  subst f₀ f₁
  exact heq

/-- Near a point with invertible derivative, the straight homotopy to that derivative
preserves the puncture. Continuity is required only on the specified neighborhood. -/
theorem exists_localPairHomotopy_of_hasFDerivAt
    {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (U : Set V) (hU : U ∈ nhds (0 : V)) (hf : ContinuousOn f U)
    (e : V ≃L[ℝ] W) (he : HasFDerivAt f e.toContinuousLinearMap 0) :
    ∃ (δ : ℝ) (_ : 0 < δ) (hδ : Metric.ball (0 : V) δ ⊆ U),
      let D := Metric.ball (0 : V) δ
      let F : C(D, W) := ⟨fun v ↦ f v.val - f 0,
        (hf.mono hδ).domRestrict.sub continuous_const⟩
      let G : C(D, W) := ⟨fun v ↦ e v.val, by fun_prop⟩
      ∃ H : F.Homotopy G, ∀ t : unitInterval, ∀ v : D, v.val ≠ 0 → H (t, v) ≠ 0 := by
  let K : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := 1 / (2 * K)
  have hc : 0 < c := by dsimp [c]; positivity
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp he).bound hc
  have hnear : {v : V | ‖f v - f 0 - e v‖ ≤ c * ‖v‖} ∈ nhds 0 := by
    filter_upwards [hrem] with v hv
    simpa only [zero_add, ContinuousLinearEquiv.coe_coe] using hv
  obtain ⟨δ, hδpos, hδsmall⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU hnear)
  have hδU : Metric.ball (0 : V) δ ⊆ U := fun v hv ↦ (hδsmall hv).1
  refine ⟨δ, hδpos, hδU, ?_⟩
  let D := Metric.ball (0 : V) δ
  let F : C(D, W) := ⟨fun v ↦ f v.val - f 0,
    (hf.mono hδU).domRestrict.sub continuous_const⟩
  let G : C(D, W) := ⟨fun v ↦ e v.val, by fun_prop⟩
  let H : F.Homotopy G :=
    { toFun z := (1 - (z.1 : ℝ)) • F z.2 + (z.1 : ℝ) • G z.2
      continuous_toFun := by fun_prop
      map_zero_left := by intro v; simp
      map_one_left := by intro v; simp }
  refine ⟨H, ?_⟩
  intro t v hv hzero
  let d := f v.val - f 0 - e v.val
  have hd : ‖d‖ ≤ c * ‖v.val‖ := (hδsmall v.property).2
  -- The derivative has a uniform lower bound, whereas its remainder is at most half of it.
  have hlower : ‖v.val‖ ≤ K * ‖e v.val‖ := by
    calc
      ‖v.val‖ = ‖e.symm (e v.val)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e v.val‖ :=
        e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ K * ‖e v.val‖ := by dsimp [K]; nlinarith [norm_nonneg (e v.val)]
  have hrewrite : e v.val + (1 - (t : ℝ)) • d = 0 := by
    change (1 - (t : ℝ)) • (f v.val - f 0) + (t : ℝ) • e v.val = 0 at hzero
    calc
      e v.val + (1 - (t : ℝ)) • d =
          (1 - (t : ℝ)) • (f v.val - f 0) + (t : ℝ) • e v.val := by
        dsimp [d]
        module
      _ = 0 := hzero
  have heq : e v.val = -((1 - (t : ℝ)) • d) := eq_neg_of_add_eq_zero_left hrewrite
  have hupper : ‖e v.val‖ ≤ ‖d‖ := by
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    nlinarith [t.property.1, norm_nonneg d]
  have hhalf : K * c = 1 / 2 := by
    dsimp [c]
    field_simp
  have hvpos : 0 < ‖v.val‖ := norm_pos_iff.mpr hv
  have hbound : ‖v.val‖ ≤ (1 / 2 : ℝ) * ‖v.val‖ := by
    calc
      ‖v.val‖ ≤ K * ‖e v.val‖ := hlower
      _ ≤ K * ‖d‖ := mul_le_mul_of_nonneg_left hupper hK.le
      _ ≤ K * (c * ‖v.val‖) := mul_le_mul_of_nonneg_left hd hK.le
      _ = (1 / 2 : ℝ) * ‖v.val‖ := by rw [← mul_assoc, hhalf]
  linarith

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual local pair map agrees with its invertible derivative after the actual
source inclusion. The map need only be continuous on that source neighborhood. -/
theorem relativeSingularHomologyMap_eq_derivative
    (R : Type) [CommRing R] {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (U : Set V) (hU : IsOpen U) (h0 : (0 : V) ∈ U)
    (hf : ContinuousOn f U) (hinj : ∀ v ∈ U, v ≠ 0 → f v ≠ f 0)
    (e : V ≃L[ℝ] W) (he : HasFDerivAt f e.toContinuousLinearMap 0) (k : ℕ) :
    relativeSingularHomologyMap R
      (⟨fun v : U ↦ f v.val - f 0, hf.domRestrict.sub continuous_const⟩ : C(U, W))
      (A := Set.ofPred (fun v : U ↦ v.val ≠ 0)) (B := Set.ofPred (fun w : W ↦ w ≠ 0))
      (fun v hv ↦ sub_ne_zero.mpr (hinj v.val v.property hv)) k =
        relativeSingularHomologyMap R (⟨Subtype.val, continuous_subtype_val⟩ : C(U, V))
          (A := Set.ofPred (fun v : U ↦ v.val ≠ 0)) (B := Set.ofPred (fun v : V ↦ v ≠ 0))
          (fun _ hv ↦ hv) k ≫
            relativeSingularHomologyMap R (⟨e, e.continuous⟩ : C(V, W))
              (A := Set.ofPred (fun v : V ↦ v ≠ 0)) (B := Set.ofPred (fun w : W ↦ w ≠ 0))
              (fun _ hv hz ↦ hv (e.injective (hz.trans (map_zero e).symm))) k := by
  obtain ⟨δ, hδpos, hδU, H, hH⟩ :=
    exists_localPairHomotopy_of_hasFDerivAt f U (hU.mem_nhds h0) hf e he
  let D := Metric.ball (0 : V) δ
  let A : Set U := {v | v.val ≠ 0}
  let B : Set D := {v | v.val ≠ 0}
  let j : C(D, U) := ⟨Set.inclusion hδU, by fun_prop⟩
  have hj : Set.MapsTo j B A := fun _ hv ↦ hv
  let F : C(U, W) := ⟨fun v ↦ f v.val - f 0, hf.domRestrict.sub continuous_const⟩
  have hF : Set.MapsTo F A {w | w ≠ 0} :=
    fun v hv ↦ sub_ne_zero.mpr (hinj v.val v.property hv)
  let i : C(U, V) := ⟨Subtype.val, continuous_subtype_val⟩
  have hi : Set.MapsTo i A {v | v ≠ 0} := fun _ hv ↦ hv
  let g : C(V, W) := ⟨e, e.continuous⟩
  have hg : Set.MapsTo g {v | v ≠ 0} {w | w ≠ 0} :=
    fun _ hv hz ↦ hv (e.injective (hz.trans (map_zero e).symm))
  let J := relativeSingularHomologyMap R j hj k
  -- Excision makes the smaller ball inclusion cancellable on the same local pair.
  have hjopen : Topology.IsOpenEmbedding j :=
    Topology.IsOpenEmbedding.inclusion hδU
      (Metric.isOpen_ball.preimage continuous_subtype_val)
  have hjrange : Aᶜ ⊆ Set.range j := by
    intro v hv
    have hvzero : v.val = 0 := by simpa [A] using hv
    refine ⟨⟨0, Metric.mem_ball_self hδpos⟩, ?_⟩
    exact Subtype.ext hvzero.symm
  have hAclosed : IsClosed Aᶜ := by
    have heq : Aᶜ = ({⟨0, h0⟩} : Set U) := by
      ext v
      change (¬ v.val ≠ 0) ↔ v = ⟨0, h0⟩
      rw [not_not]
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    rw [heq]
    exact isClosed_singleton
  have hB : (j ⁻¹' Aᶜ)ᶜ = B := by ext v; simp [A, B, j]
  have hexc {B' : Set D} {A' : Set U}
      (hB' : B' = (j ⁻¹' Aᶜ)ᶜ) (hA' : A' = Aᶜᶜ)
      (h' : Set.MapsTo j B' A') :
      HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R)
        (ComplexShape.down ℕ) (relativeSingularChainsMap R j h') := by
    subst B' A'
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding
      R j hjopen Aᶜ hAclosed hjrange
  obtain ⟨q, hq⟩ := hexc hB.symm (compl_compl A).symm hj
  let : IsIso J := by
    change IsIso (HomologicalComplex.homologyMap (relativeSingularChainsMap R j hj) k)
    erw [← hq]
    exact inferInstanceAs (IsIso (q.toHomologyIso k).hom)
  apply (cancel_epi J).mp
  change HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k =
    HomologicalComplex.homologyMap _ k ≫
      (HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k)
  rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp,
    ← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp,
    ← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
  -- The small-ball homotopy compares these exact restrictions, with every puncture preserved.
  have hloc := relativeSingularHomologyMap_eq_of_homotopy R
    (f := F.comp j) (g := (g.comp i).comp j) (A := B) (B := {w : W | w ≠ 0})
    (hF.comp hj) ((hg.comp hi).comp hj) H hH k
  exact hloc

end AtiyahSinger

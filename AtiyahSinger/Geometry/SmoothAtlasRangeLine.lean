/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The smooth range line of an original smooth bundle endomorphism

Public module ID: M1365.

A constant rank-one smooth endomorphism defines a smooth line subbundle in
the original induced total-space topology. Local charts use a nonzero column
of its actual matrix and one nonzero coordinate of that column. Division by
that coordinate gives the line coordinate, so no auxiliary metric is needed.
The inclusion and the original map corestricted to its range are smooth.

This is the standard constant-rank subbundle construction (SG III.1), here
specialized to the rank-one ranges used by the flag splitting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped Manifold ContDiff

universe u v w

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type v} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas.{w} (n := n) E)

set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth rank-one range has its original subbundle topology and smooth structural maps. -/
theorem exists_rangeLine_smoothAtlas (p : ∀ x, E x →ₗ[ℂ] E x)
    (hp : IsSmoothAtlasBundleMap A A p)
    (hr : ∀ x, Module.finrank ℂ (LinearMap.range (p x)) = 1) :
    let : TopologicalSpace (TotalSpace Unit (fun x ↦ LinearMap.range (p x))) :=
      TopologicalSpace.induced
        (fun z : TotalSpace Unit (fun x ↦ LinearMap.range (p x)) ↦
          (⟨z.proj, z.snd.val⟩ : TotalSpace Unit E)) inferInstance
    ∃ L : SmoothComplexBundleAtlas.{w} (n := n) (fun x ↦ LinearMap.range (p x)),
      IsSmoothAtlasBundleMap L A (fun x ↦ (LinearMap.range (p x)).subtype) ∧
        IsSmoothAtlasBundleMap A L (fun x ↦ (p x).rangeRestrict) := by
  classical
  let R (x : M) : Type v := LinearMap.range (p x)
  let : TopologicalSpace (TotalSpace Unit R) := TopologicalSpace.induced
    (fun z : TotalSpace Unit R ↦ (⟨z.proj, z.snd.val⟩ : TotalSpace Unit E)) inferInstance
  let := A.isFiniteRank
  let col (i j : A.Index) (a : Fin (A.rank i)) (x : M) : Fin (A.rank j) → ℂ :=
    if hx : x ∈ (A.chart i).baseSet then
      (A.chart j ⟨x, p x ((A.frameLinearEquiv i x hx).symm (Pi.single a 1))⟩).2
    else 0
  have hcol (i j : A.Index) (a : Fin (A.rank i)) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (col i j a) ((A.chart i).baseSet ∩ (A.chart j).baseSet) := hp.2 i j a
  let J := Σ i : A.Index, Fin (A.rank i) × Fin (A.rank i)
  let sec (t : J) (x : M) : R x :=
    if hx : x ∈ (A.chart t.1).baseSet then
      ⟨p x ((A.frameLinearEquiv t.1 x hx).symm (Pi.single t.2.1 1)), ⟨_, rfl⟩⟩
    else 0
  let den (t : J) (x : M) : ℂ := col t.1 t.1 t.2.1 x t.2.2
  let U (t : J) : Set M := (A.chart t.1).baseSet ∩ den t ⁻¹' ({0}ᶜ : Set ℂ)
  have hden (t : J) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (den t) (A.chart t.1).baseSet := by
    simpa only [Set.inter_self] using
      (contMDiffOn_pi_space.mp (hcol t.1 t.1 t.2.1)) t.2.2
  have hopen (t : J) : IsOpen (U t) :=
    (hden t).continuousOn.isOpen_inter_preimage (A.chart t.1).open_baseSet
      isClosed_singleton.isOpen_compl
  have hsec (t : J) (x : M) (hx : x ∈ (A.chart t.1).baseSet) (j : A.Index) :
      (A.chart j ⟨x, (sec t x).val⟩).2 = col t.1 j t.2.1 x := by
    simp only [sec, col, dite_eq_left hx]
  have hnonzero (t : J) (x : M) (hx : x ∈ U t) : sec t x ≠ 0 := by
    intro hz
    apply hx.2
    change col t.1 t.1 t.2.1 x t.2.2 = 0
    rw [← hsec t x hx.1 t.1]
    have hv : (sec t x).val = 0 := congrArg Subtype.val hz
    rw [hv]
    exact congrFun (A.linear t.1 x hx.1).map_zero t.2.2
  let coeff (t : J) (x : M) (v : R x) : ℂ :=
    (A.chart t.1 ⟨x, v.val⟩).2 t.2.2 / den t x
  have hcoeff_smul (t : J) (x : M) (hx : x ∈ U t) (c : ℂ) (v : R x) :
      coeff t x (c • v) = c * coeff t x v := by
    change (A.frameLinearEquiv t.1 x hx.1 (c • v.val)) t.2.2 / den t x = _
    rw [map_smul]
    change (c * (A.chart t.1 ⟨x, v.val⟩).2 t.2.2) / den t x = _
    exact mul_div_assoc _ _ _
  have hcoeff_self (t : J) (x : M) (hx : x ∈ U t) : coeff t x (sec t x) = 1 := by
    dsimp only [coeff]
    rw [hsec t x hx.1 t.1]
    exact div_self hx.2
  have hleft (t : J) (x : M) (hx : x ∈ U t) (v : R x) :
      coeff t x v • sec t x = v := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (hr x) (hnonzero t x hx) v
    rw [← hc, hcoeff_smul t x hx, hcoeff_self t x hx, mul_one]
  have hright (t : J) (x : M) (hx : x ∈ U t) (c : ℂ) :
      coeff t x (c • sec t x) = c := by
    rw [hcoeff_smul t x hx, hcoeff_self t x hx, mul_one]
  -- All continuity certificates refer to the original induced range topology.
  have hinc : Continuous (fun z : TotalSpace Unit R ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit E)) := continuous_induced_dom
  have hbase : Continuous (π Unit R) := (continuous_proj (E := E)).comp hinc
  have hcoeff (t : J) : ContinuousOn (fun z : TotalSpace Unit R ↦ coeff t z.proj z.snd)
      (π Unit R ⁻¹' U t) := by
    have hc : ContinuousOn
        (fun z : TotalSpace Unit R ↦ (A.chart t.1 ⟨z.proj, z.snd.val⟩).2 t.2.2)
        (π Unit R ⁻¹' U t) := (continuous_apply t.2.2).comp_continuousOn
      (continuous_snd.comp_continuousOn
        ((A.chart t.1).toOpenPartialHomeomorph.continuousOn.comp hinc.continuousOn
          (fun z hz ↦ (A.chart t.1).mem_source.mpr hz.1)))
    exact hc.div ((hden t).continuousOn.comp hbase.continuousOn (fun z hz ↦ hz.1))
      (fun z hz ↦ hz.2)
  have hfront (t : J) : ContinuousOn
      (fun z : M × (Fin 1 → ℂ) ↦ (⟨z.1, z.2 0 • sec t z.1⟩ : TotalSpace Unit R))
      (U t ×ˢ Set.univ) := by
    have hind : Topology.IsInducing (fun z : TotalSpace Unit R ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace Unit E)) := ⟨rfl⟩
    rw [hind.continuousOn_iff]
    have hc : ContinuousOn (fun z : M × (Fin 1 → ℂ) ↦
        z.2 0 • col t.1 t.1 t.2.1 z.1) (U t ×ˢ Set.univ) :=
      ((continuous_apply 0).comp continuous_snd).continuousOn.smul
        ((hcol t.1 t.1 t.2.1).continuousOn.comp continuous_fst.continuousOn
          (fun z hz ↦ ⟨hz.1.1, hz.1.1⟩))
    have hinv := (A.chart t.1).toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuousOn_fst.prodMk hc) (fun z hz ↦ (A.chart t.1).mem_target.mpr hz.1.1)
    apply hinv.congr
    intro z hz
    let v := z.2 0 • (sec t z.1).val
    have hcoord : (A.chart t.1 ⟨z.1, v⟩).2 = z.2 0 • col t.1 t.1 t.2.1 z.1 := by
      change A.frameLinearEquiv t.1 z.1 hz.1.1 (z.2 0 • (sec t z.1).val) = _
      rw [map_smul]
      exact congrArg (z.2 0 • ·) (hsec t z.1 hz.1.1 t.1)
    exact ((A.chart t.1).symm_apply_mk_proj
      (x := (⟨z.1, v⟩ : TotalSpace Unit E)) ((A.chart t.1).mem_source.mpr hz.1.1)).symm.trans
      (congrArg (A.chart t.1).toPartialEquiv.symm (congrArg (z.1, ·) hcoord))
  let chart (t : J) : Trivialization (Fin 1 → ℂ) (π Unit R) :=
    { toFun := fun z ↦ (z.proj, fun _ ↦ coeff t z.proj z.snd)
      invFun := fun z ↦ ⟨z.1, z.2 0 • sec t z.1⟩
      source := π Unit R ⁻¹' U t
      target := U t ×ˢ Set.univ
      baseSet := U t
      open_source := (hopen t).preimage hbase
      open_target := (hopen t).prod isOpen_univ
      open_baseSet := hopen t
      map_source' := fun z hz ↦ ⟨hz, Set.mem_univ _⟩
      map_target' := fun z hz ↦ hz.1
      left_inv' := by
        intro z hz
        exact congrArg (fun v : R z.proj ↦ (⟨z.proj, v⟩ : TotalSpace Unit R))
          (hleft t z.proj hz z.snd)
      right_inv' := by
        intro z hz
        apply Prod.ext
        · rfl
        · funext a
          have ha : a = 0 := Subsingleton.elim _ _
          subst a
          exact hright t z.1 hz.1 (z.2 0)
      continuousOn_toFun := hbase.continuousOn.prodMk (continuousOn_pi.mpr fun _ ↦ hcoeff t)
      continuousOn_invFun := hfront t
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  -- Rank one guarantees a nonzero matrix column and a nonzero entry in that column.
  have hcover (x : M) : ∃ t : J, x ∈ U t := by
    obtain ⟨i, hi⟩ := A.covers x
    let : Nontrivial (R x) := Module.nontrivial_of_finrank_pos (by rw [hr x]; omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : R x)
    obtain ⟨w, hw⟩ := v.property
    have hpw : p x w ≠ 0 := by
      intro hz
      exact hv (Subtype.ext (hw.symm.trans hz))
    have hexpand : ∑ a : Fin (A.rank i), (A.frameLinearEquiv i x hi w) a •
        p x ((A.frameLinearEquiv i x hi).symm (Pi.single a 1)) = p x w := by
      simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply,
        LinearEquiv.symm_apply_apply] using
          congrArg (fun z ↦ p x ((A.frameLinearEquiv i x hi).symm z))
            ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr (A.frameLinearEquiv i x hi w))
    have hcolne : ∃ a : Fin (A.rank i), col i i a x ≠ 0 := by
      by_contra! hn
      apply hpw
      rw [← hexpand]
      apply Finset.sum_eq_zero
      intro a _
      have ha : p x ((A.frameLinearEquiv i x hi).symm (Pi.single a 1)) = 0 := by
        apply (A.frameLinearEquiv i x hi).injective
        rw [map_zero]
        change (A.chart i ⟨x, p x ((A.frameLinearEquiv i x hi).symm
          (Pi.single a 1))⟩).2 = 0
        simpa only [col, dite_eq_left hi] using hn a
      rw [ha, smul_zero]
    obtain ⟨a, ha⟩ := hcolne
    obtain ⟨b, hb⟩ : ∃ b : Fin (A.rank i), col i i a x b ≠ 0 := by
      by_contra! hn
      exact ha (funext hn)
    exact ⟨⟨i, a, b⟩, hi, hb⟩
  have hdiv {f g : M → ℂ} {s : Set M}
      (hf : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f s)
      (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ g s)
      (hzero : ∀ x ∈ s, g x ≠ 0) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ (f / g) s := by
    have hinv : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun x ↦ (g x)⁻¹) s := by
      intro x hx
      have hi := (contDiffAt_inv ℝ (hzero x hx) (n := ∞)).contMDiffAt
      exact hi.comp_contMDiffWithinAt x (hg x hx)
    have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) := contDiff_mul
    apply (hmul.contMDiff.comp_contMDiffOn (hf.prodMk_space hinv)).congr
    intro x _
    simp only [Pi.div_apply, Function.comp_apply, div_eq_mul_inv]
  let L : SmoothComplexBundleAtlas.{w} (n := n) R :=
    { Index := J
      rank := fun _ ↦ 1
      chart := chart
      covers := hcover
      linear := by
        intro t x hx
        constructor
        · intro v w
          funext a
          change (A.frameLinearEquiv t.1 x hx.1 (v.val + w.val)) t.2.2 / den t x = _
          rw [map_add]
          exact add_div _ _ _
        · intro c v
          funext a
          exact hcoeff_smul t x hx c v
      contMDiffOn_coordChange := by
        intro t s a
        have ha : a = 0 := Subsingleton.elim _ _
        subst a
        have hn := ((contMDiffOn_pi_space.mp (hcol t.1 s.1 t.2.1)) s.2.2).mono
          (fun x (hx : x ∈ U t ∩ U s) ↦ ⟨hx.1.1, hx.2.1⟩)
        have hd := (hden s).mono (fun x (hx : x ∈ U t ∩ U s) ↦ hx.2.1)
        apply contMDiffOn_pi_space.mpr
        intro b
        apply (hdiv hn hd (fun x hx ↦ hx.2.2)).congr
        intro x hx
        simp only [Pi.div_apply]
        simp only [chart, Trivialization.coe_mk, OpenPartialHomeomorph.coe_mk,
          PartialEquiv.coe_symm_mk]
        change coeff s x ((Pi.single (M := fun _ : Fin 1 ↦ ℂ) 0 1) 0 • sec t x) =
          col t.1 s.1 t.2.1 x s.2.2 / den s x
        simp only [Pi.single_eq_same, one_smul, coeff]
        rw [hsec t x hx.1.1 s.1] }
  refine ⟨L, ?_, ?_⟩
  · refine ⟨contMDiff_id, ?_⟩
    intro t j a
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    have hs := (hcol t.1 j t.2.1).mono
      (fun x (hx : x ∈ U t ∩ (A.chart j).baseSet) ↦ ⟨hx.1.1, hx.2⟩)
    apply hs.congr
    intro x hx
    rw [dite_eq_left hx.1]
    have hf : (L.frameLinearEquiv t x hx.1).symm (Pi.single 0 1) = sec t x := by
      apply (L.frameLinearEquiv t x hx.1).injective
      rw [LinearEquiv.apply_symm_apply]
      funext b
      have hb : b = 0 := Subsingleton.elim _ _
      subst b
      exact (hcoeff_self t x hx.1).symm
    change (A.chart j ⟨x, ((L.frameLinearEquiv t x hx.1).symm (Pi.single 0 1)).val⟩).2 = _
    rw [hf, hsec t x hx.1.1 j]
  · refine ⟨contMDiff_id, ?_⟩
    intro i t a
    have hn := ((contMDiffOn_pi_space.mp (hcol i t.1 a)) t.2.2).mono
      (fun x (hx : x ∈ (A.chart i).baseSet ∩ U t) ↦ ⟨hx.1, hx.2.1⟩)
    have hd := (hden t).mono (fun x (hx : x ∈ (A.chart i).baseSet ∩ U t) ↦ hx.2.1)
    apply contMDiffOn_pi_space.mpr
    intro b
    apply (hdiv hn hd (fun x hx ↦ hx.2.2)).congr
    intro x hx
    simp only [Pi.div_apply, col, dite_eq_left hx.1]
    rfl

end AtiyahSinger.SmoothComplexBundleAtlas

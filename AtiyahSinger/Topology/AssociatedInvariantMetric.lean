/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantBundle
public import AtiyahSinger.Topology.ContinuousHermitianMetric

/-!
# The invariant metric on the original associated bundle

Public module ID: M1540.

The specified invariant Hermitian form descends to the actual associated
quotient fibers. Every principal representative gives the same original
pairing. Continuity is checked in the existing quotient total topology using
one original principal chart for both vectors. No new topology or invariant
metric is selected in this construction.

This is the standard metric descent for associated bundles, used for the
fiberwise formal adjunction in SG III.13.6. The construction preserves the
given moving-fiber action, including its dependent base transport.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology sumTopology

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (hP : IsPrincipalBundle G projection) (σ : EquivariantStructure G E)
  (h : ContinuousHermitianMetric E)

local notation "Z" => AssociatedBundle G P Y
local notation "D" => AssociatedEquivariantFiber hP σ

/-- The given form in the original representative coordinates of the associated fiber. -/
@[instance_reducible]
def associatedEquivariantMetricCore (z : Z) : InnerProductSpace.Core ℂ (D z) :=
  let e := associatedEquivariantFiberLinearEquiv hP σ z
  { inner := fun u v ↦ (h.toCore (Quotient.out z).2).inner (e u) (e v)
    conj_inner_symm u v := (h.toCore _).conj_inner_symm _ _
    re_inner_nonneg u := (h.toCore _).re_inner_nonneg _
    add_left u v w := by rw [map_add, (h.toCore _).add_left]
    smul_left u v c := by rw [map_smul, (h.toCore _).smul_left]
    definite u hu := e.injective ((h.toCore _).definite _ hu |>.trans (map_zero e).symm) }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invariance makes every actual principal representative an isometry for the descended form. -/
theorem associatedEquivariantMetricCore_inner
    (hInvariant : ∀ (g : G) (y : Y) (u v : E y),
      (h.toCore (g • y)).inner (σ.linearMap g y u) (σ.linearMap g y v) =
        (h.toCore y).inner u v)
    (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z)
    (u v : E y) :
    (associatedEquivariantMetricCore hP σ h z).inner
        (associatedEquivariantFiberMk hP σ p y hz u)
        (associatedEquivariantFiberMk hP σ p y hz v) = (h.toCore y).inner u v := by
  let := σ.toMulAction
  let e := associatedEquivariantFiberLinearEquiv hP σ z
  have hbase : associatedBundleMk G P Y p y =
      associatedBundleMk G P Y (Quotient.out z).1 (Quotient.out z).2 :=
    hz.trans (Quotient.out_eq z).symm
  obtain ⟨g, hg⟩ := Quotient.exact hbase
  have hy : g⁻¹ • y = (Quotient.out z).2 := (congrArg Prod.snd hg).symm
  let L : E y →ₗ[ℂ] E (Quotient.out z).2 :=
    (LinearEquiv.cast (R := ℂ) (M := E) hy).toLinearMap.comp (σ.linearMap g⁻¹ y)
  -- The same orbit element transports both original vectors into the chosen coordinates.
  have hcoord (w : E y) :
      associatedEquivariantFiberMk hP σ p y hz w = e.symm (L w) := by
    apply Subtype.ext
    change associatedBundleMk G P (TotalSpace Unit E) p ⟨y, w⟩ =
      associatedBundleMk G P (TotalSpace Unit E) (Quotient.out z).1
        ⟨(Quotient.out z).2, L w⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Prod.ext
    · exact congrArg (fun t : P × Y ↦ t.1) hg
    · exact TotalSpace.mk_cast (F := Unit) (E := E) hy (σ.linearMap g⁻¹ y w)
  change (h.toCore _).inner (e _) (e _) = _
  rw [hcoord, hcoord, e.apply_symm_apply, e.apply_symm_apply]
  have hcast {y y' : Y} (hy : y = y') (u v : E y) :
      (h.toCore y').inner ((LinearEquiv.cast (R := ℂ) (M := E) hy) u)
        ((LinearEquiv.cast (R := ℂ) (M := E) hy) v) = (h.toCore y).inner u v := by
    subst y'
    rfl
  exact (hcast hy _ _).trans (hInvariant g⁻¹ y u v)

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The invariant form descends continuously in the original double-quotient topology. -/
theorem continuous_associatedEquivariantMetricCore
    (hInvariant : ∀ (g : G) (y : Y) (u v : E y),
      (h.toCore (g • y)).inner (σ.linearMap g y u) (σ.linearMap g y v) =
        (h.toCore y).inner u v) :
    Continuous (fun w : TotalSpace Unit (D ×ᵇ D) ↦
      (associatedEquivariantMetricCore hP σ h w.proj).inner w.snd.1 w.snd.2) := by
  classical
  let := σ.toMulAction
  let : ContinuousSMul G (TotalSpace Unit E) := ⟨σ.continuous_action⟩
  let := isFiniteRank_associatedEquivariant hP σ
  let H := associatedEquivariantTotalHomeomorph hP σ
  let q := associatedBundleProjection (F := Y) hP
  let pA := associatedEquivariantProjection (P := P) σ
  have hproj (w : TotalSpace Unit D) : pA (H w) = w.proj := w.snd.property
  have hprojB (w : AssociatedBundle G P (TotalSpace Unit E)) :
      associatedBundleProjection (F := TotalSpace Unit E) hP w = q (pA w) := by
    induction w using Quotient.inductionOn with
    | h t => rfl
  have hbase : Continuous (fun w : TotalSpace Unit (D ×ᵇ D) ↦ q w.proj) :=
    q.continuous.comp ((continuous_proj (E := D)).comp continuous_sum_fst)
  apply continuous_iff_continuousAt.mpr
  intro w₀
  obtain ⟨e, he₀, he⟩ := hP.exists_trivialization (q w₀.proj)
  obtain ⟨eB, hBb, hBf, _⟩ := exists_associatedBundleTrivialization (F := Y) hP e he
  obtain ⟨eT, hTb, hTf, _⟩ :=
    exists_associatedBundleTrivialization (F := TotalSpace Unit E) hP e he
  let U : Set (TotalSpace Unit (D ×ᵇ D)) := {w | q w.proj ∈ e.baseSet}
  have hU : IsOpen U := e.open_baseSet.preimage hbase
  have hcomm (w : AssociatedBundle G P (TotalSpace Unit E))
      (hw : q (pA w) ∈ e.baseSet) :
      eB (pA w) = ((eT w).1, (eT w).2.proj) := by
    induction w using Quotient.inductionOn with
    | h t =>
      rcases t with ⟨p, v⟩
      exact (hBf p v.proj hw).trans
        (congrArg (fun t : B × TotalSpace Unit E ↦ (t.1, t.2.proj)) (hTf p v hw)).symm
  -- Both original vectors use the same principal chart, so their normalized bases coincide.
  let u (w : U) : TotalSpace Unit E := (eT (H ⟨w.val.proj, w.val.snd.1⟩)).2
  let v (w : U) : TotalSpace Unit E := (eT (H ⟨w.val.proj, w.val.snd.2⟩)).2
  have hu : Continuous u := by
    apply continuous_snd.comp
    apply eT.toOpenPartialHomeomorph.continuousOn.comp_continuous
      (H.continuous_toFun.comp (continuous_sum_fst.comp continuous_subtype_val))
    intro w
    apply eT.mem_source.mpr
    simp only [hTb, hprojB, Function.comp_apply]
    change q (pA (H ⟨w.val.proj, w.val.snd.1⟩)) ∈ e.baseSet
    rw [hproj]
    exact w.property
  have hv : Continuous v := by
    apply continuous_snd.comp
    apply eT.toOpenPartialHomeomorph.continuousOn.comp_continuous
      (H.continuous_toFun.comp (continuous_sum_snd.comp continuous_subtype_val))
    intro w
    apply eT.mem_source.mpr
    simp only [hTb, hprojB, Function.comp_apply]
    change q (pA (H ⟨w.val.proj, w.val.snd.2⟩)) ∈ e.baseSet
    rw [hproj]
    exact w.property
  have huv (w : U) : (v w).proj = (u w).proj := by
    have h₁ := hcomm (H ⟨w.val.proj, w.val.snd.1⟩) (by rw [hproj]; exact w.property)
    have h₂ := hcomm (H ⟨w.val.proj, w.val.snd.2⟩) (by rw [hproj]; exact w.property)
    rw [hproj] at h₁ h₂
    exact (congrArg Prod.snd h₂).symm.trans (congrArg Prod.snd h₁)
  let pair (w : U) : TotalSpace Unit (E ×ᵇ E) :=
    ⟨(u w).proj, (u w).snd, cast (congrArg E (huv w)) (v w).snd⟩
  have hpair : Continuous pair := by
    apply continuous_induced_rng.mpr
    apply (hu.prodMk hv).congr
    intro w
    apply Prod.ext
    · rfl
    · exact (TotalSpace.mk_cast (F := Unit) (E := E) (huv w) (v w).snd).symm
  have hvalue (w : U) :
      (h.toCore (pair w).proj).inner (pair w).snd.1 (pair w).snd.2 =
        (associatedEquivariantMetricCore hP σ h w.val.proj).inner
          w.val.snd.1 w.val.snd.2 := by
    let p := (Quotient.out w.val.proj).1
    let y := (Quotient.out w.val.proj).2
    have hz : associatedBundleMk G P Y p y = w.val.proj := Quotient.out_eq _
    obtain ⟨u₀, hu₀⟩ := (associatedEquivariantFiberMk_bijective hP σ p y hz).surjective
      w.val.snd.1
    obtain ⟨v₀, hv₀⟩ := (associatedEquivariantFiberMk_bijective hP σ p y hz).surjective
      w.val.snd.2
    have hp : projection p ∈ e.baseSet := by
      have hq : projection p = q w.val.proj := congrArg q hz
      exact hq.symm ▸ w.property
    have huvalue : u w = ⟨(e p).2 • y, σ.linearMap (e p).2 y u₀⟩ := by
      have ht := congrArg Prod.snd (hTf p (⟨y, u₀⟩ : TotalSpace Unit E) hp)
      change (eT (H ⟨w.val.proj, associatedEquivariantFiberMk hP σ p y hz u₀⟩)).2 = _
        at ht
      rw [hu₀] at ht
      exact ht
    have hvvalue : v w = ⟨(e p).2 • y, σ.linearMap (e p).2 y v₀⟩ := by
      have ht := congrArg Prod.snd (hTf p (⟨y, v₀⟩ : TotalSpace Unit E) hp)
      change (eT (H ⟨w.val.proj, associatedEquivariantFiberMk hP σ p y hz v₀⟩)).2 = _
        at ht
      rw [hv₀] at ht
      exact ht
    have hlocal : (h.toCore (pair w).proj).inner (pair w).snd.1 (pair w).snd.2 =
        (h.toCore ((e p).2 • y)).inner (σ.linearMap (e p).2 y u₀)
          (σ.linearMap (e p).2 y v₀) := by
      have htransport (t s : TotalSpace Unit E) (hts : s.proj = t.proj)
          (z : Y) (a b : E z) (ht : t = ⟨z, a⟩) (hs : s = ⟨z, b⟩) :
          (h.toCore t.proj).inner t.snd (cast (congrArg E hts) s.snd) =
            (h.toCore z).inner a b := by
        cases ht
        cases hs
        rfl
      exact htransport (u w) (v w) (huv w) _ _ _ huvalue hvvalue
    rw [hlocal, hInvariant]
    have hform := associatedEquivariantMetricCore_inner hP σ h hInvariant p y hz u₀ v₀
    rw [hu₀, hv₀] at hform
    exact hform.symm
  -- The original double-bundle topology tests exactly the two continuous normalized vectors.
  have hcontinuous := (h.continuous_pairing.comp hpair).congr hvalue
  have hon : ContinuousOn (fun w : TotalSpace Unit (D ×ᵇ D) ↦
      (associatedEquivariantMetricCore hP σ h w.proj).inner w.snd.1 w.snd.2) U :=
    continuousOn_iff_continuous_domRestrict.mpr hcontinuous
  exact hon.continuousAt (hU.mem_nhds he₀)

/-- The specified invariant metric on the original associated fibers and quotient topology. -/
def associatedEquivariantMetric
    (hInvariant : ∀ (g : G) (y : Y) (u v : E y),
      (h.toCore (g • y)).inner (σ.linearMap g y u) (σ.linearMap g y v) =
        (h.toCore y).inner u v) : ContinuousHermitianMetric D where
  toCore := associatedEquivariantMetricCore hP σ h
  continuous_pairing := continuous_associatedEquivariantMetricCore hP σ h hInvariant
  isFiniteRank := isFiniteRank_associatedEquivariant hP σ

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ProjectiveCoordinateSection

/-!
# Localized coordinate sections in the projective affine chart

Public module ID: M2021.

The projected coordinate section is a nonzero scalar multiple of its conjugate
linear coordinate in the fixed affine frame. The scalar is obtained from the
same orthogonal projector and never vanishes on the chart. This identifies the
localized first Chern class with the pullback of the original complex orientation
class on the coordinate plane.

Source: the coordinate-section proof for projective Chern powers in
Milnor--Stasheff, Characteristic Classes, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open Bundle CategoryTheory

universe u

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

attribute [local instance] tautologicalLineTopology isFiniteRank_tautologicalLine

/-- The original projected coordinate is its conjugate affine coordinate times a nonzero frame. -/
theorem projectedSection_chart_formula (e : V) (he : ‖e‖ = 1)
    (v w : (innerSL ℂ e).ker) :
    (chartEmbedding e he v).val w.val =
      (inner ℂ e ((chartEmbedding e he v).val e) * inner ℂ v.val w.val) • (e + v.val) := by
  let P := chartEmbedding e he v
  let x := e + v.val
  have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
  have hex : inner ℂ e x = 1 := by
    rw [inner_add_right, hee, show inner ℂ e v.val = 0 from v.property, add_zero]
  have hx : x ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hex
    exact zero_ne_one hex
  have hPx : P.val x = x := by
    change (ofVector x hx).val x = x
    exact ofVector_apply_self x hx
  let x' : LinearMap.range P.val.toLinearMap := ⟨x, ⟨x, hPx⟩⟩
  have hx' : x' ≠ 0 := fun h ↦ hx (congrArg Subtype.val h)
  -- Rank one and the normalization against e give the scalar of every projected vector.
  have hspan (y : V) : P.val y = inner ℂ e (P.val y) • x := by
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one P.property.2.1 hx'
      (⟨P.val y, LinearMap.mem_range_self _ y⟩ : LinearMap.range P.val.toLinearMap)
    have hav : a • x = P.val y := congrArg Subtype.val ha
    rw [← hav, inner_smul_right, hex, mul_one]
  have hd : inner ℂ e (P.val e) = inner ℂ (P.val e) (P.val e) := by
    have hid : P.val (P.val e) = P.val e :=
      congrArg (fun f : V →L[ℂ] V ↦ f e) P.property.1
    rw [P.property.2.2, hid]
  have hstar : (starRingEnd ℂ) (inner ℂ e (P.val e)) = inner ℂ e (P.val e) := by
    rw [hd, inner_self_eq_norm_sq_to_K]
    simp
  -- Self-adjointness moves P onto e; the scalar is real and the e-coordinate of w is zero.
  have hc : inner ℂ e (P.val w.val) = inner ℂ e (P.val e) * inner ℂ v.val w.val := by
    calc
      inner ℂ e (P.val w.val) = inner ℂ (P.val e) w.val := (P.property.2.2 e w.val).symm
      _ = (starRingEnd ℂ) (inner ℂ e (P.val e)) * inner ℂ x w.val := by
        conv_lhs => rw [hspan e, inner_smul_left]
      _ = inner ℂ e (P.val e) * inner ℂ v.val w.val := by
        rw [hstar]
        change _ * inner ℂ (e + v.val) w.val = _
        rw [inner_add_left, show inner ℂ e w.val = 0 from w.property, zero_add]
  exact (hspan w.val).trans (congrArg (fun a ↦ a • x) hc)

set_option maxHeartbeats 600000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The localized projected section has the original complex Thom class of its affine coordinate. -/
theorem complexLineSectionClass_projectedSection_pullback [FiniteDimensional ℂ V]
    (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0) (w : (innerSL ℂ e).ker)
    (hf : Set.MapsTo (chartEmbedding e he)
      {v : (innerSL ℂ e).ker | inner ℂ v.val w.val ≠ 0}
      {P | projectedSection V w.val P ≠ 0}) :
    relativeSingularCohomologyPullback ℤ (chartEmbedding e he) hf 2
        (complexLineSectionClass (TautologicalLine V) (fun P ↦ P.property.2.1)
          (projectedSection V w.val) (continuous_projectedSection V w.val)) =
      relativeSingularCohomologyPullback ℤ
        (⟨fun v : (innerSL ℂ e).ker ↦ ULift.up (inner ℂ v.val w.val),
          continuous_uliftUp.comp (continuous_subtype_val.inner continuous_const)⟩ :
          C((innerSL ℂ e).ker, ULift.{u} ℂ))
        (A := {v | inner ℂ v.val w.val ≠ 0}) (B := {z | z ≠ 0})
        (fun _ hv hz ↦ hv (congrArg ULift.down hz)) 2 complexOrientationClass.{u} := by
  let W := (innerSL ℂ e).ker
  let L := TautologicalLine V
  let S : Set W := {v | inner ℂ v.val w.val ≠ 0}
  let Z : Set (ULift.{u} ℂ) := {z | z ≠ 0}
  let B : Set (W × ULift.{u} ℂ) := {z | z.2 ≠ 0}
  let T : Set (TotalSpace Unit L) := {z | z.snd ≠ 0}
  let U := {P | projectedSection V w.val P ≠ 0}
  let p := chartEmbedding e he
  let σ : C(HermitianProjectiveSpace V InnerProductSpace.toCore, TotalSpace Unit L) :=
    ⟨fun P ↦ ⟨P, projectedSection V w.val P⟩, continuous_projectedSection V w.val⟩
  let F := tautologicalChartTotalMap V e he
  let g : C(W, ULift.{u} ℂ) :=
    ⟨fun v ↦ ULift.up (inner ℂ v.val w.val),
      continuous_uliftUp.comp (continuous_subtype_val.inner continuous_const)⟩
  let d : C(W, ℂ) :=
    ⟨fun v ↦ inner ℂ e ((p v).val e),
      continuous_const.inner ((continuous_subtype_val.comp p.continuous).clm_apply
        continuous_const)⟩
  -- The scalar is the squared norm of P(e), which is nonzero throughout this affine chart.
  have hd (v : W) : d v ≠ 0 := by
    have hPe : (p v).val e ≠ 0 := ((chart e he).symm v).property
    have hid : (p v).val ((p v).val e) = (p v).val e :=
      congrArg (fun f : V →L[ℂ] V ↦ f e) (p v).property.1
    have heq : d v = inner ℂ ((p v).val e) ((p v).val e) := by
      change inner ℂ e ((p v).val e) = _
      rw [(p v).property.2.2, hid]
    rw [heq]
    exact fun hz ↦ hPe (inner_self_eq_zero.mp hz)
  have hd0 : d 0 = 1 := by
    change inner ℂ e ((chartEmbedding e he 0).val e) = 1
    rw [(chartEmbedding_eq_ofVector_iff e he hne 0).mpr rfl, ofVector_apply_self,
      inner_self_eq_norm_sq_to_K, he]
    simp
  let m : C(W × ULift.{u} ℂ, ULift.{u} ℂ) :=
    ⟨fun z ↦ ULift.up (d z.1 * z.2.down),
      continuous_uliftUp.comp ((d.continuous.comp continuous_fst).mul
        (continuous_uliftDown.comp continuous_snd))⟩
  have hm : Set.MapsTo m B Z := by
    intro z hz hzero
    apply hz
    apply ULift.ext
    exact (mul_eq_zero.mp (congrArg ULift.down hzero)).resolve_left (hd z.1)
  let graph : C(W, W × ULift.{u} ℂ) := (ContinuousMap.id W).prodMk g
  have hg : Set.MapsTo g S Z := fun _ hv hz ↦ hv (congrArg ULift.down hz)
  have hgraph : Set.MapsTo graph S B := hg
  let q := m.comp graph
  have hq : Set.MapsTo q S Z := hm.comp hgraph
  let ψ : C(W, W × ULift.{u} ℂ) := (ContinuousMap.id W).prodMk q
  have hψ : Set.MapsTo ψ S B := hq
  have hF : Set.MapsTo F B T :=
    fun z hz ↦ (tautologicalChartTotalMap_nonzero_iff V e he z).mpr hz
  have hσ : Set.MapsTo σ U T := fun _ hz ↦ hz
  have hcomp {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
      (f : C(X, Y)) (g : C(Y, Z)) {A : Set X} {B : Set Y} {C : Set Z}
      (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ)
      (a : relativeSingularCohomology ℤ C n) :
      relativeSingularCohomologyPullback ℤ f hf n
          (relativeSingularCohomologyPullback ℤ g hg n a) =
        relativeSingularCohomologyPullback ℤ (g.comp f) (hg.comp hf) n a :=
    (congrArg (fun h ↦ h a) (relativeSingularCohomologyPullback_comp ℤ f g hf hg n)).symm
  have hcongr {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (f g : C(X, Y)) (h : f = g) {A : Set X} {B : Set Y}
      (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (n : ℕ) :
      relativeSingularCohomologyPullback ℤ f hf n =
        relativeSingularCohomologyPullback ℤ g hg n := by
    subst g
    rfl
  -- The actual projected section has this same scaled scalar in the same affine frame.
  have hsquare : σ.comp p = F.comp ψ := by
    apply ContinuousMap.ext
    intro v
    have hp : ((σ.comp p) v).proj = ((F.comp ψ) v).proj := rfl
    apply TotalSpace.ext hp
    apply heq_of_eq
    apply Subtype.ext
    exact projectedSection_chart_formula V e he v w
  have hlocal : relativeSingularCohomologyPullback ℤ p hf 2
      (complexLineSectionClass L (fun P ↦ P.property.2.1)
        (projectedSection V w.val) (continuous_projectedSection V w.val)) =
      relativeSingularCohomologyPullback ℤ q hq 2 complexOrientationClass.{u} := by
    change relativeSingularCohomologyPullback ℤ p hf 2
      (relativeSingularCohomologyPullback ℤ σ hσ 2
        (complexLineThomClass L (fun P ↦ P.property.2.1))) = _
    rw [hcomp p σ hf hσ,
      hcongr _ _ hsquare _ (hF.comp hψ), ← hcomp ψ F hψ hF,
      complexLineThomClass_pullback_tautologicalChart V e he hne hF,
      hcomp ψ ContinuousMap.snd hψ (fun _ hz ↦ hz)]
    rfl
  -- On the contractible affine base, this scalar family has the identity map at the center.
  let s : C(ULift.{u} ℂ, W × ULift.{u} ℂ) :=
    ⟨fun z ↦ (0, z), continuous_const.prodMk continuous_id⟩
  have hs : Set.MapsTo s Z B := fun _ hz ↦ hz
  have hms : m.comp s = ContinuousMap.id (ULift.{u} ℂ) := by
    apply ContinuousMap.ext
    intro z
    apply ULift.ext
    change d 0 * z.down = z.down
    rw [hd0, one_mul]
  let a := relativeSingularCohomologyPullback ℤ m hm 2 complexOrientationClass.{u}
  have ha : relativeSingularCohomologyPullback ℤ s hs 2 a = complexOrientationClass.{u} := by
    dsimp only [a]
    rw [hcomp s m hs hm, hcongr _ _ hms _ (Set.mapsTo_id Z)]
    have hid : relativeSingularCohomologyPullback ℤ (ContinuousMap.id (ULift.{u} ℂ))
        (Set.mapsTo_id Z) 2 = 𝟙 _ := by
      change (relativeSingularCohomologyFunctor ℤ (ULift.{u} ℂ) 2).map
        (𝟙 (Opposite.op Z)) = 𝟙 (relativeSingularCohomology ℤ Z 2)
      exact (relativeSingularCohomologyFunctor ℤ (ULift.{u} ℂ) 2).map_id (Opposite.op Z)
    exact congrArg (fun f ↦ f complexOrientationClass.{u}) hid
  have hprod := relativeSingularCohomology_prod_eq_pullback_fiber ℤ (0 : W) Z 2 a
  change relativeSingularCohomologyPullback ℤ ContinuousMap.snd
      (A := B) (B := Z) (fun _ hz ↦ hz) 2
      (relativeSingularCohomologyPullback ℤ s hs 2 a) = a at hprod
  rw [ha] at hprod
  have hscaled := congrArg (relativeSingularCohomologyPullback ℤ graph hgraph 2) hprod
  dsimp only [a] at hscaled
  rw [hcomp graph ContinuousMap.snd hgraph (fun _ hz ↦ hz), hcomp graph m hgraph hm] at hscaled
  exact hlocal.trans hscaled.symm

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

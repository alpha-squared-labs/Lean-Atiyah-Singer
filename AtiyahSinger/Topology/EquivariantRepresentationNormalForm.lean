/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundleHomotopy
public import AtiyahSinger.Topology.EquivariantSupportPoint
public import AtiyahSinger.Topology.EquivariantSupportTransport
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Radial representatives on a unitary representation

Public module ID: M1807.

Every class in the original equivariant support-triple group of a finite-dimensional
unitary representation has fixed representation bundles, singleton-zero control,
and a boundary constant on positive rays. The original bundle actions are transported
from their zero fibers. A single invariant closed ball controls the boundary homotopy.

The contraction of the base is used only for bundle isomorphisms, never as a proper
compact-support pullback. Zero-dimensional representations are included: their
punctured space is empty, and no positive-dimensional choice is made.

This is a project supplement to the equivariant bundle homotopy theorem of Karoubi
I.9.31 and the supported-triple model. It supplies normal forms for independent Bott
and reflection arguments; it does not assert Bott generation or a Bott inverse.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped unitInterval

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]

attribute [local instance] trivialTopology isFiniteRank_trivial isFiniteRank_pullback

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000 in
-- Transport the original equivariant support class to its two finite zero-fiber representations.
/-- Every original equivariant class has a zero-controlled radial boundary on two
fixed finite representation bundles. -/
theorem exists_equivariant_representation_radial_representative
    (hunitary : ∀ (g : G) (x y : V), inner ℂ (g • x) (g • y) = inner ℂ x y)
    (z : EquivariantSupportTripleKZero G V) :
    ∃ ρ τ : FiniteContinuousRepresentation G,
      ∃ a : CompactSupportTriple (FiniteBundle.trivial V ρ.dimension).Fiber
          (FiniteBundle.trivial V τ.dimension).Fiber,
        ∃ ha : a.IsEquivariant (EquivariantStructure.ofFiniteRepresentation ρ)
            (EquivariantStructure.ofFiniteRepresentation τ),
          a.control = {0} ∧
          (∀ (x : V) (t : ℝ), 0 < t →
            ∀ (hx : x ∈ a.controlᶜ) (htx : (t : ℂ) • x ∈ a.controlᶜ),
              a.boundary.linearEquiv ⟨(t : ℂ) • x, htx⟩ =
                a.boundary.linearEquiv ⟨x, hx⟩) ∧
          (EquivariantSupportBundleTriple.ofBoundary
            (FiniteBundle.trivial V ρ.dimension) (FiniteBundle.trivial V τ.dimension) a
            (EquivariantStructure.ofFiniteRepresentation ρ)
            (EquivariantStructure.ofFiniteRepresentation τ) ha).kZeroClass = z := by
  classical
  let := FiniteDimensional.proper ℂ V
  let : ContinuousSMul G PUnit.{1} := ⟨continuous_const⟩
  -- Contract each original bundle to its own zero fiber, then use the point representation.
  let zeroMap : C(PUnit.{1}, V) := ⟨fun _ ↦ 0, continuous_const⟩
  let pointMap : C(V, PUnit.{1}) := ⟨fun _ ↦ PUnit.unit, continuous_const⟩
  have hzero (g : G) (x : PUnit.{1}) : zeroMap (g • x) = g • zeroMap x := by
    exact (smul_zero g).symm
  have hpoint (g : G) (x : V) : pointMap (g • x) = g • pointMap x := rfl
  have hcomp (g : G) (x : V) :
      (zeroMap.comp pointMap) (g • x) = g • (zeroMap.comp pointMap) x := by
    exact (smul_zero g).symm
  let H : ContinuousMap.Homotopy (zeroMap.comp pointMap) (ContinuousMap.id V) := {
    toFun p := ((p.1 : ℝ) : ℂ) • p.2
    continuous_toFun :=
      (Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp continuous_fst)).smul continuous_snd
    map_zero_left x := by simp [zeroMap, pointMap]
    map_one_left x := by simp }
  have hH (t : unitInterval) (g : G) (x : V) : H (t, g • x) = g • H (t, x) :=
    (smul_comm g ((t : ℝ) : ℂ) x).symm
  have hcompare : ∀ (J : FiniteBundle V) (bundleAction : EquivariantStructure G J.Fiber),
      ∃ ρ : FiniteContinuousRepresentation G,
        ∃ e : Iso J.Fiber (FiniteBundle.trivial V ρ.dimension).Fiber,
          e.IsEquivariant bundleAction (EquivariantStructure.ofFiniteRepresentation ρ) := by
    intro J bundleAction
    let P := J.pullback zeroMap
    let pointAction := bundleAction.pullback zeroMap hzero
    obtain ⟨ρ, j, hj⟩ := EquivariantStructure.exists_pointRepresentation P pointAction
    obtain ⟨i, hi⟩ := bundleAction.exists_pullback_iso_of_homotopy (zeroMap.comp pointMap)
      (ContinuousMap.id V) hcomp (fun _ _ ↦ rfl) H hH
    let c := pullbackCompIso (E := J.Fiber) zeroMap pointMap
    let u := c.trans (i.trans (pullbackIdIso (E := J.Fiber)))
    have hu : u.IsEquivariant (pointAction.pullback pointMap hpoint) bundleAction := by
      intro g x v
      have hc := bundleAction.pullbackCompIso_isEquivariant zeroMap hzero pointMap hpoint g x v
      change c.linearEquiv (g • x) _ =
        (bundleAction.pullback (zeroMap.comp pointMap) hcomp).linearMap g x
          (c.linearEquiv x v) at hc
      change (pullbackIdIso (E := J.Fiber)).linearEquiv (g • x)
        (i.linearEquiv (g • x) (c.linearEquiv (g • x) _)) =
        bundleAction.linearMap g x ((pullbackIdIso (E := J.Fiber)).linearEquiv x
          (i.linearEquiv x (c.linearEquiv x v)))
      rw [pullbackIdIso_apply, pullbackIdIso_apply, hc]
      exact hi g x (c.linearEquiv x v)
    let k := (j.pullback pointMap).trans (pullbackTrivialIso pointMap ρ.dimension)
    have hk : k.IsEquivariant (pointAction.pullback pointMap hpoint)
        (EquivariantStructure.ofFiniteRepresentation ρ) := by
      intro g x v
      change (pullbackTrivialIso pointMap ρ.dimension).linearEquiv (g • x)
        (j.linearEquiv PUnit.unit _) =
        ρ.representation g ((pullbackTrivialIso pointMap ρ.dimension).linearEquiv x
          (j.linearEquiv PUnit.unit v))
      rw [pullbackTrivialIso_apply, pullbackTrivialIso_apply]
      exact hj g PUnit.unit v
    refine ⟨ρ, u.symm.trans k, ?_⟩
    intro g x v
    have hinv : (u.linearEquiv (g • x)).symm (bundleAction.linearMap g x v) =
        (pointAction.pullback pointMap hpoint).linearMap g x ((u.linearEquiv x).symm v) := by
      apply (u.linearEquiv (g • x)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact ((hu g x ((u.linearEquiv x).symm v)).trans
        (congrArg (bundleAction.linearMap g x) ((u.linearEquiv x).apply_symm_apply v))).symm
    change k.linearEquiv (g • x) ((u.linearEquiv (g • x)).symm _) = _
    rw [hinv]
    exact hk g x ((u.linearEquiv x).symm v)
  obtain ⟨a₀, ha₀⟩ := equivariantSupportBundleTriple_kZeroClass_surjective z
  obtain ⟨ρ, e, he⟩ := hcompare a₀.1.source a₀.2.sourceAction
  obtain ⟨τ, f, hf⟩ := hcompare a₀.1.target a₀.2.targetAction
  let E := FiniteBundle.trivial V ρ.dimension
  let F := FiniteBundle.trivial V τ.dimension
  let ρE : EquivariantStructure G E.Fiber := .ofFiniteRepresentation ρ
  let ρF : EquivariantStructure G F.Fiber := .ofFiniteRepresentation τ
  let a : CompactSupportTriple E.Fiber F.Fiber := a₀.1.datum.congr e f
  obtain ⟨ha, haclass⟩ := exists_equivariantSupportTransport a₀ E F ρE ρF e f he hf
  -- Evaluation of this fixed representation boundary is jointly continuous in both directions.
  have heval {X : Type} [TopologicalSpace X] (q : C(X, (a.controlᶜ : Set V))) :
      ∃ j : Iso (Bundle.Trivial X (Fin ρ.dimension → ℂ))
          (Bundle.Trivial X (Fin τ.dimension → ℂ)),
        ∀ x v, j.linearEquiv x v = a.boundary.linearEquiv (q x) v := by
    let inc : C((a.controlᶜ : Set V), V) := ⟨Subtype.val, continuous_subtype_val⟩
    let flatten (n : ℕ) :=
      (pullbackCompIso (E := Bundle.Trivial V (Fin n → ℂ)) inc q).trans
        (pullbackTrivialIso (inc.comp q) n)
    have hflat (n : ℕ) (x : X) (v : Fin n → ℂ) :
        (flatten n).linearEquiv x v = v := by
      change (pullbackTrivialIso (inc.comp q) n).linearEquiv x
        ((pullbackCompIso (E := Bundle.Trivial V (Fin n → ℂ)) inc q).linearEquiv x v) = v
      rw [pullbackCompIso_apply, pullbackTrivialIso_apply]
    let j := (flatten ρ.dimension).symm.trans
      ((Iso.pullback q a.boundary).trans (flatten τ.dimension))
    refine ⟨j, ?_⟩
    intro x v
    have hinv : ((flatten ρ.dimension).linearEquiv x).symm v = v := by
      apply ((flatten ρ.dimension).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, hflat]
    change (flatten τ.dimension).linearEquiv x
      (a.boundary.linearEquiv (q x) (((flatten ρ.dimension).linearEquiv x).symm v)) = _
    rw [hflat, hinv]
  -- Choose one invariant radius outside the original compact control.
  have hnorm (g : G) (x : V) : ‖g • x‖ = ‖x‖ := by
    have h := congrArg Complex.re (hunitary g x x)
    have h₁ : (inner ℂ (g • x) (g • x)).re = ‖g • x‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    have h₂ : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [h₁, h₂] at h
    nlinarith [norm_nonneg (g • x), norm_nonneg x]
  obtain ⟨B, hB⟩ := a.isCompact_control.bddAbove_image continuous_norm.continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hbound (x : V) (hx : x ∈ a.control) : ‖x‖ < R := by
    have h := hB (Set.mem_image_of_mem (fun v : V ↦ ‖v‖) hx)
    dsimp only [R]
    linarith [le_max_left B 0]
  let K₀ : Set V := {0}
  have hK₀ : IsCompact K₀ := isCompact_singleton
  have hpos (x : (K₀ᶜ : Set V)) : 0 < ‖x.val‖ := by
    apply norm_pos_iff.mpr
    simpa only [K₀, Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
  have hKInv (g : G) (x : V) : g • x ∈ K₀ ↔ x ∈ K₀ := by
    change g • x = 0 ↔ x = 0
    exact (DistribMulAction.toLinearEquiv ℂ V g).map_eq_zero_iff
  let r (x : (K₀ᶜ : Set V)) : V := ((R / ‖x.val‖ : ℝ) : ℂ) • x.val
  have hr (x : (K₀ᶜ : Set V)) : ‖r x‖ = R := by
    change ‖((R / ‖x.val‖ : ℝ) : ℂ) • x.val‖ = R
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hR (hpos x))]
    exact div_mul_cancel₀ R (ne_of_gt (hpos x))
  have hrout (x : (K₀ᶜ : Set V)) : r x ∈ a.controlᶜ := by
    intro hx
    exact (lt_irrefl R) (hr x ▸ hbound _ hx)
  let q : C((K₀ᶜ : Set V), (a.controlᶜ : Set V)) :=
    ⟨fun x ↦ ⟨r x, hrout x⟩,
      ((Complex.continuous_ofReal.comp
        (continuous_const.div (continuous_norm.comp continuous_subtype_val)
          (fun x ↦ ne_of_gt (hpos x)))).smul continuous_subtype_val).subtype_mk _⟩
  obtain ⟨d₀, hd₀⟩ := heval q
  let inc₀ : C((K₀ᶜ : Set V), V) := ⟨Subtype.val, continuous_subtype_val⟩
  let d : RelativeTriple E.Fiber F.Fiber K₀ᶜ :=
    (pullbackTrivialIso inc₀ ρ.dimension).trans
      (d₀.trans (pullbackTrivialIso inc₀ τ.dimension).symm)
  have hd (x : (K₀ᶜ : Set V)) (v : Fin ρ.dimension → ℂ) :
      d.linearEquiv x v = a.boundary.linearEquiv (q x) v := by
    apply ((pullbackTrivialIso inc₀ τ.dimension).linearEquiv x).injective
    change (pullbackTrivialIso inc₀ τ.dimension).linearEquiv x
      (((pullbackTrivialIso inc₀ τ.dimension).linearEquiv x).symm
        (d₀.linearEquiv x ((pullbackTrivialIso inc₀ ρ.dimension).linearEquiv x v))) = _
    rw [LinearEquiv.apply_symm_apply, pullbackTrivialIso_apply, hd₀,
      pullbackTrivialIso_apply]
  let b : CompactSupportTriple E.Fiber F.Fiber := ⟨K₀, hK₀, d⟩
  have hb : b.IsEquivariant ρE ρF := by
    refine ⟨hKInv, ?_⟩
    intro g x v
    let gx : (K₀ᶜ : Set V) := ⟨g • x.val, fun h ↦ x.property ((hKInv g x.val).mp h)⟩
    have hq : q gx = ⟨g • (q x).val,
        fun h ↦ (q x).property ((ha.invariant_control g (q x).val).mp h)⟩ := by
      apply Subtype.ext
      change ((R / ‖g • x.val‖ : ℝ) : ℂ) • (g • x.val) =
        g • (((R / ‖x.val‖ : ℝ) : ℂ) • x.val)
      rw [hnorm]
      exact (smul_comm g ((R / ‖x.val‖ : ℝ) : ℂ) x.val).symm
    change d.linearEquiv gx (ρ.representation g v) =
      τ.representation g (d.linearEquiv x v)
    rw [hd, hd, hq]
    exact ha.boundary_intertwines g (q x) v
  have hradial (x : V) (t : ℝ) (ht : 0 < t)
      (hx : x ∈ b.controlᶜ) (htx : (t : ℂ) • x ∈ b.controlᶜ) :
      b.boundary.linearEquiv ⟨(t : ℂ) • x, htx⟩ =
        b.boundary.linearEquiv ⟨x, hx⟩ := by
    have hnt : ‖(t : ℂ) • x‖ = t * ‖x‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hq : q ⟨(t : ℂ) • x, htx⟩ = q ⟨x, hx⟩ := by
      apply Subtype.ext
      change ((R / ‖(t : ℂ) • x‖ : ℝ) : ℂ) • ((t : ℂ) • x) =
        ((R / ‖x‖ : ℝ) : ℂ) • x
      rw [hnt, smul_smul, ← Complex.ofReal_mul]
      have hc : R / (t * ‖x‖) * t = R / ‖x‖ := by
        have hxpos := hpos ⟨x, hx⟩
        field_simp [ne_of_gt ht, ne_of_gt hxpos]
      rw [hc]
    apply LinearEquiv.ext
    intro v
    change d.linearEquiv ⟨(t : ℂ) • x, htx⟩ v = d.linearEquiv ⟨x, hx⟩ v
    rw [hd, hd, hq]
  -- Interpolate only outside one invariant ball, keeping these same two actions fixed.
  let D : Set V := Metric.closedBall 0 R
  have hD : IsCompact D := isCompact_closedBall 0 R
  have hDInv (g : G) (x : V) : g • x ∈ D ↔ x ∈ D := by
    simp only [D, Metric.mem_closedBall, dist_zero_right, hnorm]
  have haD : a.control ⊆ D := by
    intro x hx
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (hbound x hx).le)
  have hbD : b.control ⊆ D := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Metric.mem_closedBall_self hR.le
  have hlarge (x : (Dᶜ : Set V)) : R < ‖x.val‖ := by
    simpa only [D, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
      using x.property
  let c (p : unitInterval × (Dᶜ : Set V)) : ℝ :=
    (1 - (p.1 : ℝ)) + (p.1 : ℝ) * R / ‖p.2.val‖
  have hc : Continuous c :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).div
        ((continuous_norm.comp continuous_subtype_val).comp continuous_snd)
        (fun p ↦ ne_of_gt (hR.trans (hlarge p.2))))
  have hcpos (p : unitInterval × (Dᶜ : Set V)) : 0 < c p := by
    dsimp only [c]
    have hp := hR.trans (hlarge p.2)
    by_cases ht : (p.1 : ℝ) = 1
    · simp only [ht, sub_self, one_mul, zero_add]
      exact div_pos hR hp
    · have hlt : (p.1 : ℝ) < 1 := lt_of_le_of_ne p.1.property.2 ht
      exact add_pos_of_pos_of_nonneg (sub_pos.mpr hlt)
        (div_nonneg (mul_nonneg p.1.property.1 hR.le) hp.le)
  have hcout (p : unitInterval × (Dᶜ : Set V)) : (c p : ℂ) • p.2.val ∈ a.controlᶜ := by
    intro hp
    have hn : R ≤ ‖(c p : ℂ) • p.2.val‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hcpos p)]
      dsimp only [c]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (hR.trans (hlarge p.2)))]
      nlinarith [p.1.property.1, p.1.property.2, hlarge p.2]
    exact (not_lt_of_ge hn) (hbound _ hp)
  let Q : C(unitInterval × (Dᶜ : Set V), (a.controlᶜ : Set V)) :=
    ⟨fun p ↦ ⟨(c p : ℂ) • p.2.val, hcout p⟩,
      ((Complex.continuous_ofReal.comp hc).smul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  obtain ⟨j₀, hj₀⟩ := heval Q
  let incD : C((Dᶜ : Set V), V) := ⟨Subtype.val, continuous_subtype_val⟩
  let pr : C(unitInterval × (Dᶜ : Set V), (Dᶜ : Set V)) := ⟨Prod.snd, continuous_snd⟩
  let flatten (n : ℕ) :=
    (pullbackCompIso (E := Bundle.Trivial V (Fin n → ℂ)) incD pr).trans
      (pullbackTrivialIso (incD.comp pr) n)
  have hflat (n : ℕ) (p : unitInterval × (Dᶜ : Set V)) (v : Fin n → ℂ) :
      (flatten n).linearEquiv p v = v := by
    change (pullbackTrivialIso (incD.comp pr) n).linearEquiv p
      ((pullbackCompIso (E := Bundle.Trivial V (Fin n → ℂ)) incD pr).linearEquiv p v) = v
    rw [pullbackCompIso_apply, pullbackTrivialIso_apply]
  let j := (flatten ρ.dimension).trans (j₀.trans (flatten τ.dimension).symm)
  have hj (p : unitInterval × (Dᶜ : Set V)) (v : Fin ρ.dimension → ℂ) :
      j.linearEquiv p v = a.boundary.linearEquiv (Q p) v := by
    apply ((flatten τ.dimension).linearEquiv p).injective
    change (flatten τ.dimension).linearEquiv p
      (((flatten τ.dimension).linearEquiv p).symm
        (j₀.linearEquiv p ((flatten ρ.dimension).linearEquiv p v))) = _
    rw [LinearEquiv.apply_symm_apply, hflat, hj₀, hflat]
  have hab : a.EquivariantlyHomotopic b ρE ρF := by
    refine ⟨{ control := D
              isCompact_control := hD
              invariant_control := hDInv
              left_control := haD
              right_control := hbD
              homotopy := { iso := j, map_zero := ?_, map_one := ?_ }
              intertwines := ?_ }⟩
    · intro x v
      refine (hj (0, x) v).trans ?_
      refine Eq.trans ?_ (a.enlarge_apply D hD haD x v).symm
      apply congrArg (fun y : (a.controlᶜ : Set V) ↦ a.boundary.linearEquiv y v)
      apply Subtype.ext
      simp [Q, c]
    · intro x v
      refine (hj (1, x) v).trans ?_
      refine Eq.trans ?_ (b.enlarge_apply D hD hbD x v).symm
      change _ = d.linearEquiv ⟨x.val, fun h ↦ x.property (hbD h)⟩ v
      rw [hd]
      apply congrArg (fun y : (a.controlᶜ : Set V) ↦ a.boundary.linearEquiv y v)
      apply Subtype.ext
      simp [Q, q, r, c]
    · intro t g x v
      let gx : (Dᶜ : Set V) := ⟨g • x.val, fun h ↦ x.property ((hDInv g x.val).mp h)⟩
      have hcEq : c (t, gx) = c (t, x) := by
        dsimp only [c, gx]
        rw [hnorm]
      have hQ : Q (t, gx) = ⟨g • (Q (t, x)).val,
          fun h ↦ (Q (t, x)).property ((ha.invariant_control g (Q (t, x)).val).mp h)⟩ := by
        apply Subtype.ext
        change (c (t, gx) : ℂ) • (g • x.val) = g • ((c (t, x) : ℂ) • x.val)
        rw [hcEq]
        exact (smul_comm g (c (t, x) : ℂ) x.val).symm
      change j.linearEquiv (t, gx) (ρ.representation g v) =
        τ.representation g (j.linearEquiv (t, x) v)
      rw [hj, hj, hQ]
      exact ha.boundary_intertwines g (Q (t, x)) v
  -- Pass the exact fixed-action homotopy through the original quotient and the original transport.
  refine ⟨ρ, τ, b, hb, rfl, hradial, ?_⟩
  have heq := equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic E F ρE ρF a b ha hb hab
  exact heq.symm.trans (haclass.trans ha₀)

end AtiyahSinger

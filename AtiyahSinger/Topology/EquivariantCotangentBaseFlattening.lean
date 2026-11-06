/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantCotangentRadial

import all AtiyahSinger.Topology.RealBundleRadial

/-!
# Equivariant cotangent boundaries constant outside a base window

Public module ID: M1773.

A continuous invariant base cutoff changes only fibers whose projection misses
the projected original control. The resulting fixed-action homotopy therefore keeps that
entire compact control unchanged. Outside the prescribed base window the new
boundary is exactly the original boundary at the zero vector. This is the
relative step needed before radial normalization in analytic excision.

No compact-support pullback along fiber contraction is used: the construction
is an actual boundary homotopy on the same projection-pullback bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [hG : IsManifold IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

include hG hM hT hC hAction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Compare the original pulled fibers throughout one fixed-control boundary homotopy.
/-- A base cutoff deforms an equivariant boundary to its zero-fiber value at base infinity. -/
theorem exists_equivariant_cotangent_base_flattening
    (E F : FiniteBundle M)
    (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ a : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
      a.IsEquivariant (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
        (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) →
      ∀ (K : Set M) (hcontrol : ∀ z ∈ a.control, z.proj ∈ K)
        (ψ : C(M, ℝ)) (_hψzero : ∀ z ∈ a.control, ψ z.proj = 0)
        (_hψone : ∀ x ∉ K, ψ x = 1)
        (_hψinv : ∀ (g : G) (x : M), ψ (g • x) = ψ x),
      ∃ b : CompactSupportTriple
          ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
          ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
        b.IsEquivariant (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
          (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ∧
        b.control = a.control ∧
        (∀ (x : M) (hx : x ∉ K) (ξ : CotangentFiber (n := n) x)
          (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ b.controlᶜ),
          b.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ =
            a.boundary.linearEquiv ⟨⟨x, 0⟩, fun hz ↦ hx (hcontrol _ hz)⟩) ∧
        (∃ H : CompactSupportTriple.EquivariantHomotopy
          (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
          (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) a b,
          H.control = a.control) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro a ha K hcontrol ψ hψzero hψone hψinv
  let Z := CotangentTotalSpace (n := n) (M := M)
  let C := CotangentModel n
  let W := CotangentFiber (n := n) (M := M)
  let πV := cotangentProjection (n := n) (M := M)
  let PE := (πV : Z → M) *ᵖ E.Fiber
  let PF := (πV : Z → M) *ᵖ F.Fiber
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : RealBundle.IsFiniteRank C W := RealBundle.isFiniteRank_of_vectorBundle C W
  -- The cutoff is zero over the entire projected control, so scalar multiplication in any
  -- other fiber cannot enter that control. The original compact set is unchanged.
  have hsafe (z : Z) (hz : z ∈ a.controlᶜ) (t : ℝ) :
      (⟨z.proj, (1 - t * ψ z.proj) • z.snd⟩ : Z) ∈ a.controlᶜ := by
    intro h
    have hp := hψzero _ h
    change ψ z.proj = 0 at hp
    have heq : (⟨z.proj, (1 - t * ψ z.proj) • z.snd⟩ : Z) = z := by
      simp only [hp, mul_zero, sub_zero, one_smul]
      rfl
    exact hz (heq ▸ h)
  have hsame (x : M) (v w : W x)
      (hv : (⟨x, v⟩ : Z) ∈ a.controlᶜ) (hw : (⟨x, w⟩ : Z) ∈ a.controlᶜ)
      (h : v = w) (u : E.Fiber x) :
      a.boundary.linearEquiv ⟨⟨x, v⟩, hv⟩ u =
        a.boundary.linearEquiv ⟨⟨x, w⟩, hw⟩ u := by
    subst w
    rfl
  let τ : RelativeTriple E.Fiber F.Fiber (Set.univ : Set M)ᶜ := {
    linearEquiv x := (x.property (Set.mem_univ _)).elim
    continuous_total := continuous_iff_continuousAt.mpr fun z ↦
      (z.proj.property (Set.mem_univ _)).elim
    continuous_symm := continuous_iff_continuousAt.mpr fun z ↦
      (z.proj.property (Set.mem_univ _)).elim }
  let p₀ : C((a.controlᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let s (z : (a.controlᶜ : Set Z)) : ℝ := 1 - ψ z.val.proj
  have hs : Continuous s := continuous_const.sub
    (ψ.continuous.comp (πV.continuous.comp continuous_subtype_val))
  have hsafety (z : (a.controlᶜ : Set Z)) :
      (⟨z.val.proj, s z • z.val.snd⟩ : Z) ∈ a.controlᶜ := by
    simpa only [one_mul] using hsafe z.val z.property 1
  obtain ⟨d, hd⟩ := RealBundle.exists_boundary_reparametrization C W E F a
    Set.univ isCompact_univ (fun _ _ ↦ Set.mem_univ _) τ
    (fun _ hz _ ↦ (hz (Set.mem_univ _)).elim) p₀ s (fun z _ ↦ hs.continuousAt) hsafety
  let b : CompactSupportTriple PE PF := ⟨a.control, a.isCompact_control, d⟩
  have hb : b.IsEquivariant (ρE.pullback πV (fun _ _ ↦ rfl))
      (ρF.pullback πV (fun _ _ ↦ rfl)) := by
    refine ⟨ha.invariant_control, ?_⟩
    intro g z v
    let zg : (a.controlᶜ : Set Z) :=
      ⟨g • z.val, fun h ↦ z.property ((ha.invariant_control g z.val).mp h)⟩
    have heq : s zg = s z := by
      dsimp only [s, zg]
      rw [show (g • z.val).proj = g • z.val.proj from rfl, hψinv]
    change d.linearEquiv zg (ρE.linearMap g z.val.proj v) =
      ρF.linearMap g z.val.proj (d.linearEquiv z v)
    refine (hd zg (ρE.linearMap g z.val.proj v)).trans ?_
    have hz : (⟨(g • z.val).proj, s z • (g • z.val).snd⟩ : Z) ∈ a.controlᶜ := by
      rw [← heq]
      exact hsafety zg
    refine (hsame (g • z.val).proj _ _ (hsafety zg) hz
      (congrArg (fun t : ℝ ↦ t • (g • z.val).snd) heq) _).trans ?_
    exact (ha.boundary_intertwines g ⟨⟨z.val.proj, s z • z.val.snd⟩, hsafety z⟩ v).trans
      (congrArg (ρF.linearMap g z.val.proj) (hd z v).symm)
  refine ⟨b, hb, rfl, ?_, ?_⟩
  · intro x hx ξ hξ
    apply LinearEquiv.ext
    intro v
    refine (hd ⟨⟨x, ξ⟩, hξ⟩ v).trans ?_
    apply hsame x _ 0 _ (fun hz ↦ hx (hcontrol _ hz)) _ v
    simp only [s, hψone x hx, sub_self, zero_smul]
  · -- The same scalar family supplies a fixed-action homotopy on the original exterior.
    let sndD : C(unitInterval × (a.controlᶜ : Set Z), (a.controlᶜ : Set Z)) :=
      ⟨Prod.snd, continuous_snd⟩
    let p := p₀.comp sndD
    let c (z : unitInterval × (a.controlᶜ : Set Z)) : ℝ :=
      1 - (z.1 : ℝ) * ψ z.2.val.proj
    have hc : Continuous c := continuous_const.sub
      ((continuous_subtype_val.comp continuous_fst).mul
        (ψ.continuous.comp (πV.continuous.comp
          (continuous_subtype_val.comp continuous_snd))))
    have hcSafety (z : unitInterval × (a.controlᶜ : Set Z)) :
        (⟨(p z).proj, c z • (p z).snd⟩ : Z) ∈ a.controlᶜ :=
      hsafe z.2.val z.2.property z.1
    obtain ⟨j, hj⟩ := RealBundle.exists_boundary_reparametrization C W E F a
      Set.univ isCompact_univ (fun _ _ ↦ Set.mem_univ _) τ
      (fun _ hz _ ↦ (hz (Set.mem_univ _)).elim) p c (fun z _ ↦ hc.continuousAt) hcSafety
    let ce := pullbackCompIso (E := PE) p₀ sndD
    let cf := pullbackCompIso (E := PF) p₀ sndD
    let j' := ce.trans (j.trans cf.symm)
    have hj' (z : unitInterval × (a.controlᶜ : Set Z)) (v : E.Fiber z.2.val.proj) :
        j'.linearEquiv z v =
          a.boundary.linearEquiv ⟨⟨(p z).proj, c z • (p z).snd⟩, hcSafety z⟩ v := by
      change (cf.linearEquiv z).symm (j.linearEquiv z (ce.linearEquiv z v)) = _
      apply (cf.linearEquiv z).injective
      have hce : ce.linearEquiv z v = v := pullbackCompIso_apply (E := PE) p₀ sndD z v
      exact ((cf.linearEquiv z).apply_symm_apply _).trans
        ((congrArg (j.linearEquiv z) hce).trans
          ((hj z v).trans (pullbackCompIso_apply (E := PF) p₀ sndD z _).symm))
    refine ⟨{ control := a.control
              isCompact_control := a.isCompact_control
              invariant_control := ha.invariant_control
              left_control := Set.Subset.rfl
              right_control := Set.Subset.rfl
              homotopy := { iso := j', map_zero := ?_, map_one := ?_ }
              intertwines := ?_ }, rfl⟩
    · intro z v
      refine (hj' (0, z) v).trans ?_
      refine Eq.trans ?_ (a.enlarge_apply _ _ Set.Subset.rfl z v).symm
      have hc₀ : c (0, z) = 1 := by simp [c]
      exact hsame z.val.proj (c (0, z) • z.val.snd) z.val.snd
        (hcSafety (0, z)) z.property (by rw [hc₀, one_smul]) v
    · intro z v
      refine (hj' (1, z) v).trans ?_
      refine Eq.trans ?_ (b.enlarge_apply _ _ Set.Subset.rfl z v).symm
      change _ = d.linearEquiv z v
      have hc₁ : c (1, z) = s z := by simp [c, s]
      exact (hsame z.val.proj (c (1, z) • z.val.snd) (s z • z.val.snd)
        (hcSafety (1, z)) (hsafety z) (by rw [hc₁]) v).trans (hd z v).symm
    · intro t g z v
      let zg : (a.controlᶜ : Set Z) :=
        ⟨g • z.val, fun h ↦ z.property ((ha.invariant_control g z.val).mp h)⟩
      have heq : c (t, zg) = c (t, z) := by
        dsimp only [c, zg]
        rw [show (g • z.val).proj = g • z.val.proj from rfl, hψinv]
      change j'.linearEquiv (t, zg) (ρE.linearMap g z.val.proj v) =
        ρF.linearMap g z.val.proj (j'.linearEquiv (t, z) v)
      refine (hj' (t, zg) (ρE.linearMap g z.val.proj v)).trans ?_
      have hz : (⟨(g • z.val).proj, c (t, z) • (g • z.val).snd⟩ : Z) ∈ a.controlᶜ := by
        rw [← heq]
        exact hcSafety (t, zg)
      refine (hsame (g • z.val).proj _ _ (hcSafety (t, zg)) hz
        (congrArg (fun r : ℝ ↦ r • (g • z.val).snd) heq) _).trans ?_
      exact (ha.boundary_intertwines g
        ⟨⟨z.val.proj, c (t, z) • z.val.snd⟩, hcSafety (t, z)⟩ v).trans
        (congrArg (ρF.linearMap g z.val.proj) (hj' (t, z) v).symm)

end AtiyahSinger

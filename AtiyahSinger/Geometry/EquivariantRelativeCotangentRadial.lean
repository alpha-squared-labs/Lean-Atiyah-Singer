/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.InvariantCotangentMetric
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportTriple

import all AtiyahSinger.Topology.RealBundleRadial
import AtiyahSinger.Reuse.Poincare.CompactDisk

/-!
# Relative equivariant radial normalization inside a compact base window

Public module ID: M1201.

A specified equivariant boundary that is already a base bundle isomorphism
outside a compact window is normalized along positive real rays. Its control is
only the zero section over that same window, and its exterior base isomorphism
is preserved exactly. One invariant disk over the window controls the full
homotopy. This is the relative equivariant form of SG III.13, Lemma 13.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hDim : FiniteDimensional ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

include hDim hG hGC hGT hM hT hSC hAction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Allow native pullback comparisons in the complete radial homotopy certificate.

/-- Relative radial normalization preserves the base window and its exterior boundary. -/
theorem exists_equivariant_relative_radial_cotangent_representative
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
      ∀ (K : Set M) (_hK : IsCompact K)
        (_hKi : ∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K)
        (_hcontrol : ∀ z ∈ a.control, z.proj ∈ K)
        (τ : RelativeTriple E.Fiber F.Fiber Kᶜ)
        (_hτ : ∀ (z : CotangentTotalSpace (n := n) (M := M)) (hz : z.proj ∉ K)
          (ha : z ∈ a.controlᶜ),
          a.boundary.linearEquiv ⟨z, ha⟩ = τ.linearEquiv ⟨z.proj, hz⟩),
      ∃ b : CompactSupportTriple
          ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
          ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
        b.IsEquivariant (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
          (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ∧
        b.control = cotangentZeroSection '' K ∧
        (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
          ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ b.controlᶜ)
            (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ b.controlᶜ),
            b.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
              b.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) ∧
        (∀ (z : CotangentTotalSpace (n := n) (M := M)) (hz : z.proj ∉ K)
          (hb : z ∈ b.controlᶜ),
          b.boundary.linearEquiv ⟨z, hb⟩ = τ.linearEquiv ⟨z.proj, hz⟩) ∧
        (∃ H : CompactSupportTriple.EquivariantHomotopy
          (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
          (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) a b,
          ∀ z ∈ H.control, z.proj ∈ K) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro a ha K hK hKi hcontrol τ hτ
  let Z := CotangentTotalSpace (n := n) (M := M)
  let C := CotangentModel n
  let W := CotangentFiber (n := n) (M := M)
  let πV := cotangentProjection (n := n) (M := M)
  let PE := (πV : Z → M) *ᵖ E.Fiber
  let PF := (πV : Z → M) *ᵖ F.Fiber
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : RealBundle.IsFiniteRank C W := RealBundle.isFiniteRank_of_vectorBundle C W
  -- The averaged original metric gives an invariant radial coordinate and compact disks.
  obtain ⟨m, hm⟩ := exists_invariant_smoothCotangentMetric (n := n) (M := M) (G := G) IG
  let ν : C(Z, ℝ) := ⟨fun z ↦ m.length z.proj z.snd, m.continuous_length⟩
  have hν (z : Z) : 0 ≤ ν z := m.length_nonneg z.proj z.snd
  have hzero (x : M) (v : W x) : ν ⟨x, v⟩ = 0 ↔ v = 0 := m.length_eq_zero_iff x v
  have hsmul (x : M) (v : W x) (t : ℝ) :
      ν ⟨x, t • v⟩ = |t| * ν ⟨x, v⟩ := m.length_smul x t v
  have hinv (g : G) (z : Z) : ν (g • z) = ν z := by
    change Real.sqrt (m.inner (g • z.proj) (g • z).snd (g • z).snd) =
      Real.sqrt (m.inner z.proj z.snd z.snd)
    exact congrArg Real.sqrt (hm g z.proj z.snd z.snd)
  have hdisk (R : ℝ) : IsCompact {z : Z | z.proj ∈ K ∧ ν z ≤ R} := by
    let : RiemannianBundle W := ⟨m.toRiemannianMetric⟩
    let : ∀ x : M, NormedAddCommGroup (W x) := fun x ↦ inferInstance
    let : ∀ x : M, InnerProductSpace ℝ (W x) := fun x ↦ inferInstance
    let : IsContinuousRiemannianBundle C W :=
      ⟨m.inner, m.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    have hcompact := Poincare.VectorBundle.isCompact_disk_over
      (F := C) (E := W) (K := K) hK R
    have hnorm (z : Z) : ‖z.snd‖ = ν z := norm_eq_sqrt_real_inner z.snd
    simpa only [hnorm] using hcompact
  have hscale (g : G) (z : Z) (t : ℝ) :
      (⟨(g • z).proj, t • (g • z).snd⟩ : Z) = g • (⟨z.proj, t • z.snd⟩ : Z) := by
    rfl
  have hsame (x : M) (v w : W x)
      (hv : (⟨x, v⟩ : Z) ∈ a.controlᶜ) (hw : (⟨x, w⟩ : Z) ∈ a.controlᶜ)
      (h : v = w) (u : E.Fiber x) :
      a.boundary.linearEquiv ⟨⟨x, v⟩, hv⟩ u =
        a.boundary.linearEquiv ⟨⟨x, w⟩, hw⟩ u := by
    subst w
    rfl
  have hinter (g : G) (z : Z) (t : ℝ)
      (hz : (⟨z.proj, t • z.snd⟩ : Z) ∈ a.controlᶜ)
      (hgz : (⟨(g • z).proj, t • (g • z).snd⟩ : Z) ∈ a.controlᶜ)
      (v : E.Fiber z.proj) :
      a.boundary.linearEquiv ⟨⟨(g • z).proj, t • (g • z).snd⟩, hgz⟩
          (ρE.linearMap g z.proj v) =
        ρF.linearMap g z.proj (a.boundary.linearEquiv ⟨⟨z.proj, t • z.snd⟩, hz⟩ v) := by
    have h := ha.boundary_intertwines g ⟨⟨z.proj, t • z.snd⟩, hz⟩ v
    exact h
  obtain ⟨B, hB⟩ := a.isCompact_control.bddAbove_image ν.continuous.continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hbound (z : Z) (hz : z ∈ a.control) : ν z < R := by
    have h := hB (Set.mem_image_of_mem ν hz)
    dsimp only [R]
    linarith [le_max_left B 0]
  let K₀ : Set Z := cotangentZeroSection '' K
  have hK₀ : IsCompact K₀ := hK.image continuous_cotangentZeroSection
  have hmem₀ (z : Z) : z ∈ K₀ ↔ z.proj ∈ K ∧ z.snd = 0 := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, hz⟩
      exact ⟨z.proj, hx, TotalSpace.ext rfl (heq_of_eq hz.symm)⟩
  have hpos (z : Z) (hz : z ∈ K₀ᶜ) (hx : z.proj ∈ K) : 0 < ν z := by
    apply m.length_pos z.proj z.snd
    intro hzero
    exact hz ((hmem₀ z).mpr ⟨hx, hzero⟩)
  have hKInv (g : G) (z : Z) : g • z ∈ K₀ ↔ z ∈ K₀ := by
    rw [hmem₀, hmem₀]
    constructor
    · rintro ⟨hx, hz⟩
      have hn := (hzero (g • z).proj (g • z).snd).mpr hz
      rw [hinv] at hn
      exact ⟨(hKi g z.proj).mp hx, (hzero z.proj z.snd).mp hn⟩
    · rintro ⟨hx, hz⟩
      refine ⟨(hKi g z.proj).mpr hx, ?_⟩
      apply (hzero (g • z).proj (g • z).snd).mp
      rw [hinv]
      exact (hzero z.proj z.snd).mpr hz
  let p₀ : C((K₀ᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let s (z : (K₀ᶜ : Set Z)) : ℝ := R / ν z.val
  have hs (z : (K₀ᶜ : Set Z)) (hx : z.val.proj ∈ K) : ContinuousAt s z :=
    continuousAt_const.div (ν.continuous.comp continuous_subtype_val).continuousAt
      (ne_of_gt (hpos z.val z.property hx))
  have hsupport (z : (K₀ᶜ : Set Z)) :
      (⟨z.val.proj, s z • z.val.snd⟩ : Z) ∈ a.controlᶜ := by
    intro ha
    have hx : z.val.proj ∈ K :=
      hcontrol (⟨z.val.proj, s z • z.val.snd⟩ : Z) ha
    have hp := hpos z.val z.property hx
    have hn : ν ⟨z.val.proj, s z • z.val.snd⟩ = R := by
      rw [hsmul, abs_of_pos (div_pos hR hp)]
      exact div_mul_cancel₀ R (ne_of_gt hp)
    exact (lt_irrefl R) (hn ▸ hbound _ ha)
  -- Reuse the actual radial evaluation map, with the specified invariant length.
  obtain ⟨d, hd⟩ := RealBundle.exists_boundary_reparametrization C W E F a
    K hK hcontrol τ hτ p₀ s hs hsupport
  let b : CompactSupportTriple PE PF := ⟨K₀, hK₀, d⟩
  have hb : b.IsEquivariant (ρE.pullback πV (fun _ _ ↦ rfl))
      (ρF.pullback πV (fun _ _ ↦ rfl)) := by
    refine ⟨hKInv, ?_⟩
    intro g z v
    let zg : (K₀ᶜ : Set Z) :=
      ⟨g • z.val, fun h ↦ z.property ((hKInv g z.val).mp h)⟩
    have heq : s zg = s z := by
      dsimp only [s, zg]
      rw [hinv]
    have hgz : (⟨(g • z.val).proj, s z • (g • z.val).snd⟩ : Z) ∈ a.controlᶜ := by
      rw [← heq]
      exact hsupport zg
    change d.linearEquiv zg (ρE.linearMap g z.val.proj v) =
      (ρF.linearMap g z.val.proj) (d.linearEquiv z v)
    refine (hd zg (ρE.linearMap g z.val.proj v)).trans ?_
    refine (hsame (g • z.val).proj _ _ (hsupport zg) hgz
      (congrArg (fun r : ℝ ↦ r • (g • z.val).snd) heq) _).trans ?_
    exact (hinter g z.val (s z) (hsupport z) hgz v).trans
      (congrArg (ρF.linearMap g z.val.proj) (hd z v).symm)
  have hbτ (z : Z) (hz : z.proj ∉ K) (hbz : z ∈ b.controlᶜ) :
      b.boundary.linearEquiv ⟨z, hbz⟩ = τ.linearEquiv ⟨z.proj, hz⟩ := by
    apply LinearEquiv.ext
    intro u
    refine (hd ⟨z, hbz⟩ u).trans ?_
    exact congrArg (fun e ↦ e u)
      (hτ (⟨z.proj, s ⟨z, hbz⟩ • z.snd⟩ : Z) hz (hsupport ⟨z, hbz⟩))
  refine ⟨b, hb, rfl, ?_, hbτ, ?_⟩
  · -- Positive scaling has exactly the same normalized vector, hence the same boundary map.
    intro x v t ht hv htv
    by_cases hx : x ∈ K
    case neg => exact (hbτ ⟨x, t • v⟩ hx htv).trans (hbτ ⟨x, v⟩ hx hv).symm
    have hp := hpos ⟨x, v⟩ hv hx
    have hnt : ν ⟨x, t • v⟩ = t * ν ⟨x, v⟩ := by
      rw [hsmul, abs_of_pos ht]
    have hfiber : s ⟨⟨x, t • v⟩, htv⟩ • (t • v) = s ⟨⟨x, v⟩, hv⟩ • v := by
      dsimp only [s]
      rw [hnt, smul_smul]
      have hc : R / (t * ν ⟨x, v⟩) * t = R / ν ⟨x, v⟩ := by field_simp
      rw [hc]
    apply LinearEquiv.ext
    intro w
    change d.linearEquiv ⟨⟨x, t • v⟩, htv⟩ w = d.linearEquiv ⟨⟨x, v⟩, hv⟩ w
    rw [hd, hd]
    exact hsame x _ _ _ _ hfiber w
  · -- Outside the chosen invariant disk over K, radial interpolation avoids the original control.
    let D : Set Z := {z | z.proj ∈ K ∧ ν z ≤ R}
    have hD : IsCompact D := hdisk R
    have hDInv (g : G) (z : Z) : g • z ∈ D ↔ z ∈ D := by
      change (g • z).proj ∈ K ∧ ν (g • z) ≤ R ↔ z.proj ∈ K ∧ ν z ≤ R
      rw [show (g • z).proj = g • z.proj from rfl, hKi, hinv]
    have haD : a.control ⊆ D := fun z hz ↦ ⟨hcontrol z hz, (hbound z hz).le⟩
    have hbD : b.control ⊆ D := by
      intro z hz
      obtain ⟨hx, hv⟩ := (hmem₀ z).mp hz
      refine ⟨hx, ?_⟩
      rw [(hzero z.proj z.snd).mpr hv]
      exact hR.le
    let pD : C((Dᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
    let sndD : C(unitInterval × (Dᶜ : Set Z), (Dᶜ : Set Z)) := ⟨Prod.snd, continuous_snd⟩
    let p := pD.comp sndD
    let c (z : unitInterval × (Dᶜ : Set Z)) : ℝ :=
      (1 - (z.1 : ℝ)) + (z.1 : ℝ) * R / ν z.2.val
    have hlarge (z : (Dᶜ : Set Z)) (hx : z.val.proj ∈ K) : R < ν z.val :=
      lt_of_not_ge (fun hn ↦ z.property ⟨hx, hn⟩)
    have hc (z : unitInterval × (Dᶜ : Set Z)) (hx : (p z).proj ∈ K) :
        ContinuousAt c z :=
      ((continuousAt_const.sub
        (continuous_subtype_val.comp continuous_fst).continuousAt).add
        (((continuous_subtype_val.comp continuous_fst).continuousAt.mul continuousAt_const).div
          ((ν.continuous.comp continuous_subtype_val).comp continuous_snd).continuousAt
          (ne_of_gt (hR.trans (hlarge z.2 hx)))))
    have hcSupport (z : unitInterval × (Dᶜ : Set Z)) :
        (⟨(p z).proj, c z • (p z).snd⟩ : Z) ∈ a.controlᶜ := by
      intro ha
      have hn := hlarge z.2 (hcontrol (⟨(p z).proj, c z • (p z).snd⟩ : Z) ha)
      have hνpos := hR.trans hn
      have hcpos : 0 < c z := by
        dsimp only [c]
        have ht := z.1.property
        have hratio := div_pos hR hνpos
        by_cases ht₁ : (z.1 : ℝ) = 1
        · simp only [ht₁, sub_self, one_mul, zero_add]
          exact hratio
        · have htlt : (z.1 : ℝ) < 1 := lt_of_le_of_ne ht.2 ht₁
          exact add_pos_of_pos_of_nonneg (sub_pos.mpr htlt)
            (div_nonneg (mul_nonneg ht.1 hR.le) hνpos.le)
      have hnorm : R ≤ ν ⟨(p z).proj, c z • (p z).snd⟩ := by
        rw [hsmul, abs_of_pos hcpos]
        change R ≤ c z * ν z.2.val
        dsimp only [c]
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hνpos)]
        nlinarith [z.1.property.1, z.1.property.2]
      exact (not_lt_of_ge hnorm) (hbound _ ha)
    obtain ⟨j, hj⟩ := RealBundle.exists_boundary_reparametrization C W E F a
      K hK hcontrol τ hτ p c hc hcSupport
    let ce := pullbackCompIso (E := PE) pD sndD
    let cf := pullbackCompIso (E := PF) pD sndD
    let j' := ce.trans (j.trans cf.symm)
    have hj' (z : unitInterval × (Dᶜ : Set Z)) (v : E.Fiber z.2.val.proj) :
        j'.linearEquiv z v =
          a.boundary.linearEquiv ⟨⟨(p z).proj, c z • (p z).snd⟩, hcSupport z⟩ v := by
      change (cf.linearEquiv z).symm (j.linearEquiv z (ce.linearEquiv z v)) = _
      rw [pullbackCompIso_apply, hj]
      apply (cf.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
      rfl
    refine ⟨{ control := D
              isCompact_control := hD
              invariant_control := hDInv
              left_control := haD
              right_control := hbD
              homotopy := { iso := j', map_zero := ?_, map_one := ?_ }
              intertwines := ?_ }, fun _ hz ↦ hz.1⟩
    · intro z v
      refine (hj' (0, z) v).trans ?_
      refine Eq.trans ?_ (a.enlarge_apply D hD haD z v).symm
      have hc₀ : c (0, z) = 1 := by simp [c]
      apply hsame z.val.proj _ z.val.snd _ _ _ v
      change c (0, z) • z.val.snd = z.val.snd
      rw [hc₀, one_smul]
    · intro z v
      refine (hj' (1, z) v).trans ?_
      refine Eq.trans ?_ (b.enlarge_apply D hD hbD z v).symm
      change _ = d.linearEquiv ⟨z.val, fun hz ↦ z.property (hbD hz)⟩ v
      rw [hd]
      have hc₁ : c (1, z) = R / ν z.val := by simp [c]
      apply hsame z.val.proj _ _ _ _ _ v
      change c (1, z) • z.val.snd = (R / ν z.val) • z.val.snd
      rw [hc₁]
    · intro t g z v
      let zg : (Dᶜ : Set Z) :=
        ⟨g • z.val, fun h ↦ z.property ((hDInv g z.val).mp h)⟩
      have heq : c (t, zg) = c (t, z) := by
        dsimp only [c, zg]
        rw [hinv]
      have hgz : (⟨(g • z.val).proj, c (t, z) • (g • z.val).snd⟩ : Z) ∈
          a.controlᶜ := by
        rw [← heq]
        exact hcSupport (t, zg)
      change j'.linearEquiv (t, zg) (ρE.linearMap g z.val.proj v) =
        (ρF.linearMap g z.val.proj) (j'.linearEquiv (t, z) v)
      refine (hj' (t, zg) (ρE.linearMap g z.val.proj v)).trans ?_
      refine (hsame (g • z.val).proj _ _ (hcSupport (t, zg)) hgz
        (congrArg (fun r : ℝ ↦ r • (g • z.val).snd) heq) _).trans ?_
      exact (hinter g z.val (c (t, z)) (hcSupport (t, z)) hgz v).trans
        (congrArg (ρF.linearMap g z.val.proj) (hj' (t, z) v).symm)

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.InvariantPositiveFunction
public import AtiyahSinger.Topology.VariableRankEquivariantAverage

import all AtiyahSinger.Topology.BundleHomotopyType
import AtiyahSinger.Topology.HermitianMetricPullback

/-!
# Equivariant transport along a paracompact cylinder

Public module ID: M1778.

Average an identity-normalized continuous near-diagonal transport. A positive
invariant time step gives a locally finite composition of actual invertible
transports. Their eventual endpoint is continuous and equivariant. The base
may be noncompact and its locally finite fiber ranks may be unbounded.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Topology unitInterval

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [MulAction G X] [ContinuousSMul G X]
  [MulAction G (X × unitInterval)] [ContinuousSMul G (X × unitInterval)]
  (E : X × unitInterval → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

attribute [local instance] isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Local stabilization uses the same original pullback topologies and moving-fiber maps.
/-- An equivariant bundle on a paracompact cylinder has equivariantly isomorphic endpoints. -/
theorem EquivariantStructure.exists_equivariant_endpoint_iso
    (ρ : EquivariantStructure G E)
    (hcyl : ∀ (g : G) (x : X) (t : unitInterval), (g • x, t) = g • (x, t)) :
    let p₀ : C(X, X × unitInterval) := ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩
    let p₁ : C(X, X × unitInterval) := ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩
    ∃ e : Iso ((p₀ : X → X × unitInterval) *ᵖ E) ((p₁ : X → X × unitInterval) *ᵖ E),
      e.IsEquivariant (ρ.pullback p₀ (fun g x ↦ hcyl g x 0))
        (ρ.pullback p₁ (fun g x ↦ hcyl g x 1)) := by
  classical
  let B := X × unitInterval
  let pr₁ : C(B × B, B) := ContinuousMap.fst
  let pr₂ : C(B × B, B) := ContinuousMap.snd
  obtain ⟨T₀, hT₀⟩ := exists_diagonal_transport E
  obtain ⟨h⟩ := nonempty_continuousHermitianMetric (E := E)
  let ρ₁ := ρ.pullback pr₁ (fun _ _ ↦ rfl)
  let ρ₂ := ρ.pullback pr₂ (fun _ _ ↦ rfl)
  obtain ⟨T, hTeq, hretain⟩ :=
    T₀.exists_equivariant_average_of_hermitian ρ₁ ρ₂ (h.pullback pr₂)
  have hT (b : B) : T.linearMap (b, b) = LinearMap.id := by
    rw [hretain (b, b) (by
      intro g v
      change T₀.linearMap (g • b, g • b) (ρ.linearMap g b v) =
        ρ.linearMap g b (T₀.linearMap (b, b) v)
      rw [hT₀, hT₀]
      rfl), hT₀]
  let U : Set (X × (unitInterval × unitInterval)) :=
    {z | Function.Bijective (T.linearMap ((z.1, z.2.1), (z.1, z.2.2)))}
  have hU : IsOpen U := (Hom.isOpen_setOf_bijective ((pr₁ : B × B → B) *ᵖ E) T).preimage
    ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hdiag : ∀ x t, (x, t, t) ∈ U := by
    intro x t
    change Function.Bijective (T.linearMap ((x, t), (x, t)))
    rw [hT]
    exact Function.bijective_id
  obtain ⟨δ, hδ, hnearδ⟩ := exists_continuous_time_step U hU hdiag
  obtain ⟨ε, hε, hεδ, hinvε⟩ := exists_positive_invariant_le (G := G) δ hδ
  have hnear (x : X) (s t : unitInterval) (hst : dist s t ≤ ε x) : (x, s, t) ∈ U :=
    hnearδ x s t (hst.trans (hεδ x))
  -- The clipped uniform grid is continuous and reaches the endpoint locally in finitely many steps.
  let time (n : ℕ) (x : X) : unitInterval :=
    ⟨min 1 ((n : ℝ) * ε x), le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) (hε x).le),
      min_le_left _ _⟩
  have htime (n : ℕ) : Continuous (time n) :=
    (continuous_const.min (continuous_const.mul ε.continuous)).subtype_mk _
  have hmono (x : X) : Monotone (fun n ↦ time n x) := by
    intro n m hnm
    exact min_le_min_left 1 (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) (hε x).le)
  have hstep (n : ℕ) (x : X) : dist (time n x) (time (n + 1) x) ≤ ε x := by
    change |min 1 ((n : ℝ) * ε x) - min 1 (((n + 1 : ℕ) : ℝ) * ε x)| ≤ ε x
    have hreal : (time n x : ℝ) ≤ (time (n + 1) x : ℝ) := hmono x (Nat.le_succ n)
    rw [abs_of_nonpos (sub_nonpos.mpr hreal)]
    have hn : (n : ℝ) * ε x ≤ ((n + 1 : ℕ) : ℝ) * ε x :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (hε x).le
    dsimp only [time]
    rw [Nat.cast_add, Nat.cast_one]
    by_cases hsmall : (n : ℝ) * ε x ≤ 1
    · rw [min_eq_right hsmall]
      have hle := min_le_right (1 : ℝ) (((n : ℝ) + 1) * ε x)
      nlinarith
    · rw [min_eq_left (le_of_not_ge hsmall), min_eq_left (by
        push_cast at hn
        linarith)]
      linarith [hε x]
  let f (n : ℕ) : C(X, B) := ⟨fun x ↦ (x, time n x), continuous_id.prodMk (htime n)⟩
  let p₀ : C(X, B) := ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩
  let p₁ : C(X, B) := ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩
  let pair (n : ℕ) : C(X, B × B) := (f n).prodMk (f (n + 1))
  let step (n : ℕ) : Hom ((f n : X → B) *ᵖ E)
      ((f (n + 1) : X → B) *ᵖ E) :=
    { linearMap x := T.linearMap (pair n x)
      continuous_total := by
        have hin : Continuous (fun z : TotalSpace Unit ((f n : X → B) *ᵖ E) ↦
            (⟨pair n z.proj, z.snd⟩ : TotalSpace Unit (pr₁ *ᵖ E))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit E pr₁).continuous_iff]
          exact ((pair n).continuous.comp continuous_proj).prodMk
            (Pullback.continuous_lift Unit E (f n))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E (f (n + 1))).continuous_iff]
        exact continuous_proj.prodMk
          ((Pullback.continuous_lift Unit E pr₂).comp (T.continuous_total.comp hin)) }
  have hbij (n : ℕ) (x : X) : Function.Bijective ((step n).linearMap x) :=
    hnear x (time n x) (time (n + 1) x) (hstep n x)
  let S (n : ℕ) := (step n).toIso (hbij n)
  have hf : f 0 = p₀ := by
    apply ContinuousMap.ext
    intro x
    change (x, time 0 x) = (x, (0 : unitInterval))
    congr 1
    apply Subtype.ext
    simp only [time, Nat.cast_zero, zero_mul, min_eq_right zero_le_one, Set.Icc.coe_zero]
  let castFiber (a b : B) (hab : a = b) : E a ≃ₗ[ℂ] E b := by
    subst b
    exact LinearEquiv.refl _ _
  have hcast (a b : B) (hab : a = b) (v : E a) :
      (⟨b, castFiber a b hab v⟩ : TotalSpace Unit E) = ⟨a, v⟩ := by
    subst b
    rfl
  let M₀ : Iso ((p₀ : X → B) *ᵖ E) ((f 0 : X → B) *ᵖ E) := {
    linearEquiv x := castFiber (p₀ x) (f 0 x) (congrArg (fun q : C(X, B) ↦ q x) hf.symm)
    continuous_total := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E (f 0)).continuous_iff]
      apply continuous_proj.prodMk
      apply (Pullback.continuous_lift Unit E p₀).congr
      intro z
      exact (hcast _ _ _ z.snd).symm
    continuous_symm := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E p₀).continuous_iff]
      apply continuous_proj.prodMk
      apply (Pullback.continuous_lift Unit E (f 0)).congr
      intro z
      have h := hcast (p₀ z.proj) (f 0 z.proj)
        (congrArg (fun q : C(X, B) ↦ q z.proj) hf.symm)
        ((castFiber (p₀ z.proj) (f 0 z.proj)
          (congrArg (fun q : C(X, B) ↦ q z.proj) hf.symm)).symm z.snd)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h }
  let M : (n : ℕ) → Iso ((p₀ : X → B) *ᵖ E) ((f n : X → B) *ᵖ E) :=
    Nat.rec M₀ (fun n a ↦ a.trans (S n))
  let D := TotalSpace Unit ((p₀ : X → B) *ᵖ E)
  let A (n : ℕ) (z : D) : TotalSpace Unit E :=
    ⟨f n z.proj, (M n).linearEquiv z.proj z.snd⟩
  have hA (n : ℕ) : Continuous (A n) :=
    (Pullback.continuous_lift Unit E (f n)).comp (M n).continuous_total
  have hstationary {a b : B} (hab : a = b) (v : E a) :
      (⟨b, T.linearMap (a, b) v⟩ : TotalSpace Unit E) = ⟨a, v⟩ := by
    subst b
    rw [hT]
    rfl
  have hdone (n : ℕ) (x : X) (hn : time n x = 1) (m : ℕ) (hnm : n ≤ m) :
      time m x = 1 := le_antisymm (time m x).property.2 (by
        rw [← hn]
        exact hmono x hnm)
  have hsucc (n : ℕ) (z : D) (hn : time n z.proj = 1) : A (n + 1) z = A n z := by
    change (⟨f (n + 1) z.proj, T.linearMap (f n z.proj, f (n + 1) z.proj)
      ((M n).linearEquiv z.proj z.snd)⟩ : TotalSpace Unit E) = _
    exact hstationary (congrArg (fun t ↦ (z.proj, t))
      (hn.trans (hdone n z.proj hn (n + 1) (Nat.le_succ n)).symm)) _
  have hstable (n m : ℕ) (hnm : n ≤ m) (z : D) (hn : time n z.proj = 1) :
      A m z = A n z := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact (hsucc m z (hdone n z.proj hn m hnm)).trans ih
  have hreach (x : X) : ∃ n : ℕ, 1 < (n : ℝ) * ε x := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε x)
    exact ⟨n, (div_lt_iff₀ (hε x)).mp hn⟩
  choose N hN using hreach
  have hNtime (x : X) : time (N x) x = 1 :=
    Subtype.ext (min_eq_left (hN x).le)
  let L (x : X) : E (x, 0) ≃ₗ[ℂ] E (x, 1) :=
    ((M (N x)).linearEquiv x).trans (castFiber (x, time (N x) x) (x, 1)
      (congrArg (fun t ↦ (x, t)) (hNtime x)))
  have hL (z : D) : (⟨p₁ z.proj, L z.proj z.snd⟩ : TotalSpace Unit E) =
      A (N z.proj) z := hcast _ _ (congrArg (fun t ↦ (z.proj, t)) (hNtime z.proj)) _
  -- Local finite stabilization proves continuity even when the chosen stopping index jumps.
  have hcont : Continuous (fun z : D ↦
      (⟨p₁ z.proj, L z.proj z.snd⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let n := N z₀.proj
    have hnbhd : ∀ᶠ x in 𝓝 z₀.proj, 1 < (n : ℝ) * ε x :=
      (continuous_const.mul ε.continuous).continuousAt.eventually
        (Ioi_mem_nhds (hN z₀.proj))
    apply (hA n).continuousAt.congr_of_eventuallyEq
    filter_upwards [(continuous_proj (E := (p₀ : X → B) *ᵖ E)).continuousAt.eventually
      hnbhd] with z hz
    rw [hL]
    have hn : time n z.proj = 1 := Subtype.ext (min_eq_left hz.le)
    calc
      A (N z.proj) z = A (max n (N z.proj)) z :=
        (hstable (N z.proj) (max n (N z.proj)) (le_max_right _ _) z (hNtime z.proj)).symm
      _ = A n z := hstable n (max n (N z.proj)) (le_max_left _ _) z hn
  let result : Hom ((p₀ : X → B) *ᵖ E) ((p₁ : X → B) *ᵖ E) :=
    { linearMap x := (L x).toLinearMap
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E p₁).continuous_iff]
        exact continuous_proj.prodMk hcont }
  let : MulAction G (TotalSpace Unit E) := ρ.toMulAction
  have hf₀ (g : G) (x : X) : p₀ (g • x) = g • p₀ x := hcyl g x 0
  have hf₁ (g : G) (x : X) : p₁ (g • x) = g • p₁ x := hcyl g x 1
  let ρD := ρ.pullback p₀ hf₀
  let : MulAction G D := ρD.toMulAction
  have hfn (n : ℕ) (g : G) (x : X) : f n (g • x) = g • f n x := by
    change (g • x, time n (g • x)) = g • (x, time n x)
    have ht : time n (g • x) = time n x := by
      apply Subtype.ext
      change min 1 ((n : ℝ) * ε (g • x)) = min 1 ((n : ℝ) * ε x)
      rw [hinvε]
    rw [ht]
    exact hcyl g x (time n x)
  have hlift (p : C(X, B)) (heq : ∀ (g : G) (x : X), p (g • x) = g • p x)
      (g : G) (x : X) (v : E (p x)) :
      (⟨p (g • x), (ρ.pullback p heq).linearMap g x v⟩ : TotalSpace Unit E) =
        g • (⟨p x, v⟩ : TotalSpace Unit E) := by
    have hcast' (a b : B) (hab : a = b) (L : E (p x) →ₗ[ℂ] E b) :
        (⟨a, (Eq.mpr (congrArg (fun y ↦ E (p x) →ₗ[ℂ] E y) hab) L) v⟩ :
          TotalSpace Unit E) = ⟨b, L v⟩ := by
      subst b
      rfl
    exact hcast' (p (g • x)) (g • p x) (heq g x) (ρ.linearMap g (p x))
  let Θ (b : B) (z : TotalSpace Unit E) : TotalSpace Unit E :=
    ⟨b, T.linearMap (z.proj, b) z.snd⟩
  have hΘ (g : G) (b : B) (z : TotalSpace Unit E) :
      Θ (g • b) (g • z) = g • Θ b z := by
    change (⟨g • b, T.linearMap (g • z.proj, g • b)
      (ρ.linearMap g z.proj z.snd)⟩ : TotalSpace Unit E) =
      ⟨g • b, ρ.linearMap g b (T.linearMap (z.proj, b) z.snd)⟩
    exact congrArg (TotalSpace.mk (g • b)) (hTeq g (z.proj, b) z.snd)
  have hA₀ (z : D) : A 0 z = (⟨p₀ z.proj, z.snd⟩ : TotalSpace Unit E) :=
    hcast _ _ _ _
  have hAeq (n : ℕ) (g : G) (z : D) : A n (g • z) = g • A n z := by
    induction n with
    | zero => rw [hA₀, hA₀]; exact hlift p₀ hf₀ g z.proj z.snd
    | succ n ih =>
      change Θ (f (n + 1) (g • z.proj)) (A n (g • z)) =
        g • Θ (f (n + 1) z.proj) (A n z)
      rw [hfn, ih, hΘ]
  have hLeq (g : G) (z : D) :
      (⟨p₁ (g • z.proj), L (g • z.proj) (ρD.linearMap g z.proj z.snd)⟩ :
        TotalSpace Unit E) = g • (⟨p₁ z.proj, L z.proj z.snd⟩ : TotalSpace Unit E) := by
    let k := max (N (g • z.proj)) (N z.proj)
    have hc : A (N (g • z.proj)) (g • z) = g • A (N z.proj) z := calc
      A (N (g • z.proj)) (g • z) = A k (g • z) :=
        (hstable _ _ (le_max_left _ _) (g • z) (hNtime _)).symm
      _ = g • A k z := hAeq k g z
      _ = g • A (N z.proj) z :=
        congrArg (g • ·) (hstable _ _ (le_max_right _ _) z (hNtime _))
    exact (hL (g • z)).trans (hc.trans (congrArg (g • ·) (hL z).symm))
  refine ⟨result.toIso (fun x ↦ (L x).bijective), ?_⟩
  intro g x v
  apply TotalSpace.mk_injective (F := Unit) (p₁ (g • x))
  change (⟨p₁ (g • x), L (g • x) (ρD.linearMap g x v)⟩ : TotalSpace Unit E) =
    ⟨p₁ (g • x), (ρ.pullback p₁ hf₁).linearMap g x (L x v)⟩
  rw [hlift]
  exact hLeq g ⟨x, v⟩

end AtiyahSinger.ComplexBundle

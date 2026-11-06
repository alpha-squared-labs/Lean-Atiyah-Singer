/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalHomologyChart
public import AtiyahSinger.Topology.LocalRelativeCupNormalization
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup
public import AtiyahSinger.Topology.SimplexLocalHomology
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality

/-!
# Local cup evaluation in the native Euclidean coordinates

Public module ID: M1944.

The finite-coordinate identification preserves the original positive simplex
cycle. The grouped Euclidean splitting uses the same base-first coordinate
order as the lifted function-space calculation. Translation then gives the
same formula at any base point, with the original local orientation cycles.

Source: naturality of the original relative Kronecker pairing and the actual
basis simplex, Hatcher, Algebraic Topology, Sections 3.1 and 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

-- These private adapters preserve the order and value of every finite coordinate.
private def liftedPiNativeEquiv (n : ℕ) :
    ULift.{0} (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((ULift.moduleEquiv : ULift.{0} (Fin n → ℝ) ≃ₗ[ℝ] _).trans
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm).toContinuousLinearEquiv

private theorem liftedPiNativeEquiv_basis (n : ℕ) :
    ((Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : ULift.{0} (Fin n → ℝ) ≃ₗ[ℝ] _).symm).map
        (liftedPiNativeEquiv n).toLinearEquiv =
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis := by
  apply Module.Basis.eq_of_apply_eq
  intro i
  ext j
  simp [liftedPiNativeEquiv, EuclideanSpace.basisFun_apply, Pi.basisFun_apply]

private theorem liftedPiNativeEquiv_evaluation (n : ℕ)
    (a : relativeSingularCohomology ℚ {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} n) :
    let e := liftedPiNativeEquiv n
    let b := (Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : ULift.{0} (Fin n → ℝ) ≃ₗ[ℝ] _).symm
    let c := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (singularCochainHomologyEvaluation ℚ
      (relativeSingularChains ℚ {v : ULift.{0} (Fin n → ℝ) | v ≠ 0}) n
      (relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(_, _))
        (A := {v | v ≠ 0}) (B := {v | v ≠ 0})
        (fun _ hv ↦ e.map_ne_zero_iff.mpr hv) n a)
      (relativeSingularHomologyRationalization {v : ULift.{0} (Fin n → ℝ) | v ≠ 0} n
        (realOrientationCycle b b.orientation))).down =
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) n a
        (relativeSingularHomologyRationalization
          {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} n
          (realOrientationCycle c c.orientation))).down := by
  let e := liftedPiNativeEquiv n
  let f : C(ULift.{0} (Fin n → ℝ), EuclideanSpace ℝ (Fin n)) := ⟨e, e.continuous⟩
  let hf : Set.MapsTo f {v | v ≠ 0} {v | v ≠ 0} :=
    fun _ hv ↦ e.map_ne_zero_iff.mpr hv
  let b := (Pi.basisFun ℝ (Fin n)).map
    (ULift.moduleEquiv : ULift.{0} (Fin n → ℝ) ≃ₗ[ℝ] _).symm
  have hcycle := realOrientationCycle_map_basis b e
  rw [liftedPiNativeEquiv_basis] at hcycle
  have hρ := relativeSingularHomologyRationalization_naturality f hf n
    (realOrientationCycle b b.orientation)
  rw [hcycle] at hρ
  change _ = HomologicalComplex.homologyMap (relativeSingularChainsMap ℚ f hf) n
    (relativeSingularHomologyRationalization {v : ULift.{0} (Fin n → ℝ) | v ≠ 0} n
      (realOrientationCycle b b.orientation)) at hρ
  have heval := singularCochainHomologyEvaluation_naturality ℚ
    (relativeSingularChains ℚ {v : ULift.{0} (Fin n → ℝ) | v ≠ 0})
    (relativeSingularChains ℚ {v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
    (relativeSingularChainsMap ℚ f hf) n a
    (relativeSingularHomologyRationalization {v : ULift.{0} (Fin n → ℝ) | v ≠ 0} n
      (realOrientationCycle b b.orientation))
  rw [← hρ] at heval
  exact congrArg ULift.down heval.symm

private def liftedPiNativeEquivOfEq (m n : ℕ) (h : m = n) :
    ULift.{0} (Fin m → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  h ▸ liftedPiNativeEquiv m

private theorem liftedPiNativeEquivOfEq_apply (m n : ℕ) (h : m = n)
    (x : ULift.{0} (Fin m → ℝ)) (i : Fin n) :
    liftedPiNativeEquivOfEq m n h x i = x.down (Fin.cast h.symm i) := by
  subst n
  rfl

private theorem liftedPiNativeEquivOfEq_evaluation (m n : ℕ) (h : m = n)
    (a : relativeSingularCohomology ℚ {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} n) :
    let e := liftedPiNativeEquivOfEq m n h
    let b := (Pi.basisFun ℝ (Fin m)).map
      (ULift.moduleEquiv : ULift.{0} (Fin m → ℝ) ≃ₗ[ℝ] _).symm
    let c := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (singularCochainHomologyEvaluation ℚ
      (relativeSingularChains ℚ {v : ULift.{0} (Fin m → ℝ) | v ≠ 0}) m
      (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ
        {v : ULift.{0} (Fin m → ℝ) | v ≠ 0} k)) h.symm)
        (relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(_, _))
          (A := {v | v ≠ 0}) (B := {v | v ≠ 0})
          (fun _ hv ↦ e.map_ne_zero_iff.mpr hv) n a))
      (relativeSingularHomologyRationalization {v : ULift.{0} (Fin m → ℝ) | v ≠ 0} m
        (realOrientationCycle b b.orientation))).down =
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) n a
        (relativeSingularHomologyRationalization
          {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} n
          (realOrientationCycle c c.orientation))).down := by
  subst n
  exact liftedPiNativeEquiv_evaluation m a

private theorem nativeTranslation_evaluation (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (a : relativeSingularCohomology ℚ ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) n) :
    let V := EuclideanSpace ℝ (Fin n)
    let t : C(V, V) := ⟨fun z ↦ x + z, continuous_const.add continuous_id⟩
    let ht : Set.MapsTo t {z | z ≠ 0} ({x}ᶜ : Set V) :=
      fun _ hz h ↦ hz (add_left_cancel (h.trans (add_zero x).symm))
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({x}ᶜ : Set V)) n a
      (relativeSingularHomologyRationalization ({x}ᶜ : Set V) n
        (euclideanLocalOrientationCycle n x))).down =
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {z : V | z ≠ 0}) n
        (relativeSingularCohomologyPullback ℚ t ht n a)
        (relativeSingularHomologyRationalization {z : V | z ≠ 0} n
          (realOrientationCycle b b.orientation))).down := by
  let V := EuclideanSpace ℝ (Fin n)
  let t : C(V, V) := ⟨fun z ↦ x + z, continuous_const.add continuous_id⟩
  let ht : Set.MapsTo t {z | z ≠ 0} ({x}ᶜ : Set V) :=
    fun _ hz h ↦ hz (add_left_cancel (h.trans (add_zero x).symm))
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hρ := relativeSingularHomologyRationalization_naturality t ht n
    (realOrientationCycle b b.orientation)
  change _ = HomologicalComplex.homologyMap (relativeSingularChainsMap ℚ t ht) n
    (relativeSingularHomologyRationalization {z : V | z ≠ 0} n
      (realOrientationCycle b b.orientation)) at hρ
  have h := singularCochainHomologyEvaluation_naturality ℚ
    (relativeSingularChains ℚ {z : V | z ≠ 0})
    (relativeSingularChains ℚ ({x}ᶜ : Set V)) (relativeSingularChainsMap ℚ t ht) n a
    (relativeSingularHomologyRationalization {z : V | z ≠ 0} n
      (realOrientationCycle b b.orientation))
  rw [← hρ] at h
  exact congrArg ULift.down h

/-- The genuine local cup pairs multiplicatively in native base-first Euclidean coordinates. -/
theorem relativeSingularCohomologyUnionCup_local_evaluation (n r : ℕ)
    (a : relativeSingularCohomology ℚ {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} n)
    (b : relativeSingularCohomology ℚ {v : EuclideanSpace ℝ (Fin r) | v ≠ 0} r) :
    let V := EuclideanSpace ℝ (Fin n)
    let W := EuclideanSpace ℝ (Fin r)
    let T := EuclideanSpace ℝ (Fin (n + r))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let f : C(T, V) := ⟨fun z ↦ (e z).1, continuous_fst.comp e.continuous⟩
    let g : C(T, W) := ⟨fun z ↦ (e z).2, continuous_snd.comp e.continuous⟩
    let A : Set T := f ⁻¹' {v : V | v ≠ 0}
    let B : Set T := g ⁻¹' {w : W | w ≠ 0}
    let P : Set T := {z | z ≠ 0}
    ∀ hP : Set.MapsTo (ContinuousMap.id T) P (A ∪ B),
    let c := relativeSingularCohomologyUnionCup ℚ A B
      ((isOpen_ne_fun continuous_id continuous_const).preimage f.continuous)
      ((isOpen_ne_fun continuous_id continuous_const).preimage g.continuous) n r
      (relativeSingularCohomologyPullback ℚ f (A := A) (B := {v : V | v ≠ 0})
        (fun _ h ↦ h) n a)
      (relativeSingularCohomologyPullback ℚ g (A := B) (B := {w : W | w ≠ 0})
        (fun _ h ↦ h) r b)
    let d := relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r) c
    let bV := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let bW := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
    let bT := (EuclideanSpace.basisFun (Fin (n + r)) ℝ).toBasis
    (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ P) (n + r) d
      (relativeSingularHomologyRationalization P (n + r)
        (realOrientationCycle bT bT.orientation))).down =
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {v : V | v ≠ 0}) n a
        (relativeSingularHomologyRationalization {v : V | v ≠ 0} n
          (realOrientationCycle bV bV.orientation))).down *
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {w : W | w ≠ 0}) r b
        (relativeSingularHomologyRationalization {w : W | w ≠ 0} r
          (realOrientationCycle bW bW.orientation))).down := by
  let V := EuclideanSpace ℝ (Fin n)
  let W := EuclideanSpace ℝ (Fin r)
  let T := EuclideanSpace ℝ (Fin (n + r))
  let V₀ := ULift.{0} (Fin n → ℝ)
  let W₀ := ULift.{0} (Fin r → ℝ)
  let T₀ := ULift.{0} (Fin (r + n) → ℝ)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let f : C(T, V) := ⟨fun z ↦ (e z).1, continuous_fst.comp e.continuous⟩
  let g : C(T, W) := ⟨fun z ↦ (e z).2, continuous_snd.comp e.continuous⟩
  let A : Set T := f ⁻¹' {v : V | v ≠ 0}
  let B : Set T := g ⁻¹' {w : W | w ≠ 0}
  let P : Set T := {z | z ≠ 0}
  change ∀ hP : Set.MapsTo (ContinuousMap.id T) P (A ∪ B), _
  intro hP
  let f₀ : C(T₀, V₀) :=
    ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨i.val, by omega⟩), by dsimp only [T₀, V₀]; fun_prop⟩
  let g₀ : C(T₀, W₀) :=
    ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨n + i.val, by omega⟩), by dsimp only [T₀, W₀]; fun_prop⟩
  let A₀ : Set T₀ := f₀ ⁻¹' {v : V₀ | v ≠ 0}
  let B₀ : Set T₀ := g₀ ⁻¹' {w : W₀ | w ≠ 0}
  let P₀ : Set T₀ := {z | z ≠ 0}
  let ev := liftedPiNativeEquiv n
  let ew := liftedPiNativeEquiv r
  let et := liftedPiNativeEquivOfEq (r + n) (n + r) (Nat.add_comm r n)
  let v : C(V₀, V) := ⟨ev, ev.continuous⟩
  let w : C(W₀, W) := ⟨ew, ew.continuous⟩
  let t : C(T₀, T) := ⟨et, et.continuous⟩
  have hv : Set.MapsTo v {z | z ≠ 0} {z | z ≠ 0} :=
    fun _ hz ↦ ev.map_ne_zero_iff.mpr hz
  have hw : Set.MapsTo w {z | z ≠ 0} {z | z ≠ 0} :=
    fun _ hz ↦ ew.map_ne_zero_iff.mpr hz
  have ht : Set.MapsTo t P₀ P := fun _ hz ↦ et.map_ne_zero_iff.mpr hz
  -- The same coordinate values commute with both base-first projections.
  have hf : f.comp t = v.comp f₀ := by
    apply ContinuousMap.ext
    intro x
    ext i
    change et x (Fin.castAdd r i) = x.down ⟨i.val, by omega⟩
    rw [liftedPiNativeEquivOfEq_apply]
    rfl
  have hg : g.comp t = w.comp g₀ := by
    apply ContinuousMap.ext
    intro x
    ext i
    change et x (Fin.natAdd n i) = x.down ⟨n + i.val, by omega⟩
    rw [liftedPiNativeEquivOfEq_apply]
    rfl
  have hta : Set.MapsTo t A₀ A := by
    intro x hx
    change f (t x) ≠ 0
    change f₀ x ≠ 0 at hx
    have h := congrArg (fun F : C(T₀, V) ↦ F x) hf
    change f (t x) = ev (f₀ x) at h
    rw [h]
    exact ev.map_ne_zero_iff.mpr hx
  have htb : Set.MapsTo t B₀ B := by
    intro x hx
    change g (t x) ≠ 0
    change g₀ x ≠ 0 at hx
    have h := congrArg (fun F : C(T₀, W) ↦ F x) hg
    change g (t x) = ew (g₀ x) at h
    rw [h]
    exact ew.map_ne_zero_iff.mpr hx
  have hP₀ : Set.MapsTo (ContinuousMap.id T₀) P₀ (A₀ ∪ B₀) := by
    intro x hx
    rcases hP (ht hx) with h | h
    · left
      change f₀ x ≠ 0
      change f (t x) ≠ 0 at h
      have hh := congrArg (fun F : C(T₀, V) ↦ F x) hf
      change f (t x) = ev (f₀ x) at hh
      rw [hh] at h
      exact ev.map_ne_zero_iff.mp h
    · right
      change g₀ x ≠ 0
      change g (t x) ≠ 0 at h
      have hh := congrArg (fun F : C(T₀, W) ↦ F x) hg
      change g (t x) = ew (g₀ x) at hh
      rw [hh] at h
      exact ew.map_ne_zero_iff.mp h
  have hA : IsOpen A := (isOpen_ne_fun continuous_id continuous_const).preimage f.continuous
  have hB : IsOpen B := (isOpen_ne_fun continuous_id continuous_const).preimage g.continuous
  have hA₀ : IsOpen A₀ := (isOpen_ne_fun continuous_id continuous_const).preimage f₀.continuous
  have hB₀ : IsOpen B₀ := (isOpen_ne_fun continuous_id continuous_const).preimage g₀.continuous
  have hfA : Set.MapsTo f A {z | z ≠ 0} := fun _ hz ↦ hz
  have hgB : Set.MapsTo g B {z | z ≠ 0} := fun _ hz ↦ hz
  have hfA₀ : Set.MapsTo f₀ A₀ {z | z ≠ 0} := fun _ hz ↦ hz
  have hgB₀ : Set.MapsTo g₀ B₀ {z | z ≠ 0} := fun _ hz ↦ hz
  let a₀ := relativeSingularCohomologyPullback ℚ v hv n a
  let b₀ := relativeSingularCohomologyPullback ℚ w hw r b
  let c := relativeSingularCohomologyUnionCup ℚ A B hA hB n r
    (relativeSingularCohomologyPullback ℚ f hfA n a)
    (relativeSingularCohomologyPullback ℚ g hgB r b)
  let c₀ := relativeSingularCohomologyUnionCup ℚ A₀ B₀ hA₀ hB₀ n r
    (relativeSingularCohomologyPullback ℚ f₀ hfA₀ n a₀)
    (relativeSingularCohomologyPullback ℚ g₀ hgB₀ r b₀)
  let d := relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r) c
  let d₀ := relativeSingularCohomologyPullback ℚ (ContinuousMap.id T₀) hP₀ (n + r) c₀
  have mapCongr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      {S : Set X} {D : Set Y} (f g : C(X, Y)) (h : f = g)
      (hf : Set.MapsTo f S D) (hg : Set.MapsTo g S D) (k : ℕ) :
      relativeSingularCohomologyPullback ℚ f hf k =
        relativeSingularCohomologyPullback ℚ g hg k := by
    subst g
    rfl
  have htaB : Set.MapsTo t (A₀ ∪ B₀) (A ∪ B) :=
    fun _ h ↦ h.elim (fun h ↦ Or.inl (hta h)) (fun h ↦ Or.inr (htb h))
  -- The two genuine relative factors commute with this same coordinate map.
  have hc : relativeSingularCohomologyPullback ℚ t htaB (n + r) c = c₀ := by
    have hnat := relativeSingularCohomologyPullback_unionCup ℚ t
      hA₀ hB₀ hA hB hta htb n r
      (relativeSingularCohomologyPullback ℚ f hfA n a)
      (relativeSingularCohomologyPullback ℚ g hgB r b)
    refine hnat.trans ?_
    have hleft : relativeSingularCohomologyPullback ℚ t hta n
        (relativeSingularCohomologyPullback ℚ f hfA n a) =
          relativeSingularCohomologyPullback ℚ f₀ hfA₀ n a₀ := by
      change _ = relativeSingularCohomologyPullback ℚ f₀ hfA₀ n
        (relativeSingularCohomologyPullback ℚ v hv n a)
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp ℚ t f hta hfA n,
        mapCongr _ _ hf _ (hv.comp hfA₀) n,
        relativeSingularCohomologyPullback_comp ℚ f₀ v hfA₀ hv n, ModuleCat.comp_apply]
    have hright : relativeSingularCohomologyPullback ℚ t htb r
        (relativeSingularCohomologyPullback ℚ g hgB r b) =
          relativeSingularCohomologyPullback ℚ g₀ hgB₀ r b₀ := by
      change _ = relativeSingularCohomologyPullback ℚ g₀ hgB₀ r
        (relativeSingularCohomologyPullback ℚ w hw r b)
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp ℚ t g htb hgB r,
        mapCongr _ _ hg _ (hw.comp hgB₀) r,
        relativeSingularCohomologyPullback_comp ℚ g₀ w hgB₀ hw r, ModuleCat.comp_apply]
    exact congrArg₂ (fun x y ↦ relativeSingularCohomologyUnionCup ℚ A₀ B₀ hA₀ hB₀ n r x y)
      hleft hright
  have hd : relativeSingularCohomologyPullback ℚ t ht (n + r) d = d₀ := by
    change relativeSingularCohomologyPullback ℚ t ht (n + r)
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r) c) = _
    have hsquare : relativeSingularCohomologyPullback ℚ t ht (n + r)
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r) c) =
          relativeSingularCohomologyPullback ℚ (ContinuousMap.id T₀) hP₀ (n + r)
            (relativeSingularCohomologyPullback ℚ t htaB (n + r) c) := by
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp ℚ t (ContinuousMap.id T) ht hP (n + r),
        ← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp ℚ (ContinuousMap.id T₀) t hP₀ htaB (n + r)]
      rfl
    exact hsquare.trans (congrArg
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T₀) hP₀ (n + r)) hc)
  -- Positive cycles and evaluations are transported by this coordinate equivalence.
  have htEval := liftedPiNativeEquivOfEq_evaluation (r + n) (n + r) (Nat.add_comm r n) d
  change _ = _ at htEval
  rw [hd] at htEval
  have hstandard := relativeSingularCohomologyUnionCup_liftedPi_evaluation n r a₀ b₀ hP₀
  have hvEval := liftedPiNativeEquiv_evaluation n a
  have hwEval := liftedPiNativeEquiv_evaluation r b
  exact htEval.symm.trans (hstandard.trans (congrArg₂ (· * ·) hvEval hwEval))


/-- The local product formula at a translated base point uses the same native local cycles. -/
theorem relativeSingularCohomologyUnionCup_local_evaluation_at (n r : ℕ)
    (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin (n + r)))
    (a : relativeSingularCohomology ℚ ({x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) n)
    (b : relativeSingularCohomology ℚ {w : EuclideanSpace ℝ (Fin r) | w ≠ 0} r) :
    let V := EuclideanSpace ℝ (Fin n)
    let W := EuclideanSpace ℝ (Fin r)
    let T := EuclideanSpace ℝ (Fin (n + r))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let f : C(T, V) := ⟨fun z ↦ (e z).1, continuous_fst.comp e.continuous⟩
    let g : C(T, W) := ⟨fun z ↦ (e z).2, continuous_snd.comp e.continuous⟩
    let A : Set T := {z | f z ≠ x}
    let B : Set T := {z | g z ≠ 0}
    ∀ hS : A ∪ B = ({y}ᶜ : Set T),
    let c := relativeSingularCohomologyUnionCup ℚ A B
      (isOpen_ne_fun f.continuous continuous_const)
      (isOpen_ne_fun g.continuous continuous_const) n r
      (relativeSingularCohomologyPullback ℚ f (A := A) (B := ({x}ᶜ : Set V))
        (fun _ h ↦ h) n a)
      (relativeSingularCohomologyPullback ℚ g (A := B) (B := {w : W | w ≠ 0})
        (fun _ h ↦ h) r b)
    let d := (eqToIso (congrArg (fun S ↦ relativeSingularCohomology ℚ S (n + r)) hS)).hom c
    let bW := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
    (singularCochainHomologyEvaluation ℚ
      (relativeSingularChains ℚ ({y}ᶜ : Set T)) (n + r) d
      (relativeSingularHomologyRationalization ({y}ᶜ : Set T) (n + r)
        (euclideanLocalOrientationCycle (n + r) y))).down =
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ ({x}ᶜ : Set V)) n a
        (relativeSingularHomologyRationalization ({x}ᶜ : Set V) n
          (euclideanLocalOrientationCycle n x))).down *
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {w : W | w ≠ 0}) r b
        (relativeSingularHomologyRationalization {w : W | w ≠ 0} r
          (realOrientationCycle bW bW.orientation))).down := by
  let V := EuclideanSpace ℝ (Fin n)
  let W := EuclideanSpace ℝ (Fin r)
  let T := EuclideanSpace ℝ (Fin (n + r))
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let f : C(T, V) := ⟨fun z ↦ (e z).1, continuous_fst.comp e.continuous⟩
  let g : C(T, W) := ⟨fun z ↦ (e z).2, continuous_snd.comp e.continuous⟩
  let A : Set T := {z | f z ≠ x}
  let B : Set T := {z | g z ≠ 0}
  let A₀ : Set T := {z | f z ≠ 0}
  let B₀ : Set T := {z | g z ≠ 0}
  let P : Set T := {z | z ≠ 0}
  change ∀ hS : A ∪ B = ({y}ᶜ : Set T), _
  intro hS
  -- The support equality fixes both coordinates of the same translated point.
  have hy : y ∉ A ∪ B := by
    rw [hS]
    exact fun h ↦ h rfl
  have hfy : f y = x := by
    by_contra h
    exact hy (Or.inl h)
  have hgy : g y = 0 := by
    by_contra h
    exact hy (Or.inr h)
  let t : C(T, T) := ⟨fun z ↦ y + z, continuous_const.add continuous_id⟩
  let v : C(V, V) := ⟨fun z ↦ x + z, continuous_const.add continuous_id⟩
  have ht : Set.MapsTo t P ({y}ᶜ : Set T) :=
    fun _ hz h ↦ hz (add_left_cancel (h.trans (add_zero y).symm))
  have hv : Set.MapsTo v {z | z ≠ 0} ({x}ᶜ : Set V) :=
    fun _ hz h ↦ hz (add_left_cancel (h.trans (add_zero x).symm))
  have hf : f.comp t = v.comp f := by
    apply ContinuousMap.ext
    intro z
    change (e (y + z)).1 = x + (e z).1
    rw [map_add]
    exact congrArg (· + (e z).1) hfy
  have hg : g.comp t = g := by
    apply ContinuousMap.ext
    intro z
    change (e (y + z)).2 = (e z).2
    rw [map_add]
    change g y + (e z).2 = (e z).2
    rw [hgy, zero_add]
  have hta : Set.MapsTo t A₀ A := by
    intro z hz h
    have heq := congrArg (fun F : C(T, V) ↦ F z) hf
    change f (t z) = x + f z at heq
    exact hz (add_left_cancel ((heq.symm.trans h).trans (add_zero x).symm))
  have htb : Set.MapsTo t B₀ B := by
    intro z hz
    have heq := congrArg (fun F : C(T, W) ↦ F z) hg
    change g (t z) = g z at heq
    change g (t z) ≠ 0
    rw [heq]
    exact hz
  have hP : Set.MapsTo (ContinuousMap.id T) P (A₀ ∪ B₀) := by
    intro z hz
    by_cases hfz : f z ≠ 0
    · exact Or.inl hfz
    · by_cases hgz : g z ≠ 0
      · exact Or.inr hgz
      · exfalso
        apply hz
        apply e.injective
        rw [map_zero]
        exact Prod.ext (not_ne_iff.mp hfz) (not_ne_iff.mp hgz)
  have htaB : Set.MapsTo t (A₀ ∪ B₀) (A ∪ B) :=
    fun _ h ↦ h.elim (fun h ↦ Or.inl (hta h)) (fun h ↦ Or.inr (htb h))
  have htS : Set.MapsTo t P (A ∪ B) := fun _ h ↦ htaB (hP h)
  have hA : IsOpen A := isOpen_ne_fun f.continuous continuous_const
  have hB : IsOpen B := isOpen_ne_fun g.continuous continuous_const
  have hA₀ : IsOpen A₀ := isOpen_ne_fun f.continuous continuous_const
  have hB₀ : IsOpen B₀ := isOpen_ne_fun g.continuous continuous_const
  have hfA : Set.MapsTo f A ({x}ᶜ : Set V) := fun _ h ↦ h
  have hgB : Set.MapsTo g B {z | z ≠ 0} := fun _ h ↦ h
  have hfA₀ : Set.MapsTo f A₀ {z | z ≠ 0} := fun _ h ↦ h
  have hgB₀ : Set.MapsTo g B₀ {z | z ≠ 0} := fun _ h ↦ h
  let a₀ := relativeSingularCohomologyPullback ℚ v hv n a
  let c := relativeSingularCohomologyUnionCup ℚ A B hA hB n r
    (relativeSingularCohomologyPullback ℚ f hfA n a)
    (relativeSingularCohomologyPullback ℚ g hgB r b)
  let c₀ := relativeSingularCohomologyUnionCup ℚ A₀ B₀ hA₀ hB₀ n r
    (relativeSingularCohomologyPullback ℚ f hfA₀ n a₀)
    (relativeSingularCohomologyPullback ℚ g hgB₀ r b)
  let d := (eqToIso (congrArg (fun S ↦ relativeSingularCohomology ℚ S (n + r)) hS)).hom c
  let d₀ := relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r) c₀
  have mapCongr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      {S : Set X} {D : Set Y} (f g : C(X, Y)) (h : f = g)
      (hf : Set.MapsTo f S D) (hg : Set.MapsTo g S D) (k : ℕ) :
      relativeSingularCohomologyPullback ℚ f hf k =
        relativeSingularCohomologyPullback ℚ g hg k := by
    subst g
    rfl
  -- Naturality retains both relative factors before the final support transport.
  have hc : relativeSingularCohomologyPullback ℚ t htaB (n + r) c = c₀ := by
    have hnat := relativeSingularCohomologyPullback_unionCup ℚ t
      hA₀ hB₀ hA hB hta htb n r
      (relativeSingularCohomologyPullback ℚ f hfA n a)
      (relativeSingularCohomologyPullback ℚ g hgB r b)
    refine hnat.trans ?_
    have hleft : relativeSingularCohomologyPullback ℚ t hta n
        (relativeSingularCohomologyPullback ℚ f hfA n a) =
          relativeSingularCohomologyPullback ℚ f hfA₀ n a₀ := by
      change _ = relativeSingularCohomologyPullback ℚ f hfA₀ n
        (relativeSingularCohomologyPullback ℚ v hv n a)
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp ℚ t f hta hfA n,
        mapCongr _ _ hf _ (hv.comp hfA₀) n,
        relativeSingularCohomologyPullback_comp ℚ f v hfA₀ hv n, ModuleCat.comp_apply]
    have hright : relativeSingularCohomologyPullback ℚ t htb r
        (relativeSingularCohomologyPullback ℚ g hgB r b) =
          relativeSingularCohomologyPullback ℚ g hgB₀ r b := by
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp ℚ t g htb hgB r,
        mapCongr _ _ hg _ hgB₀ r]
    exact congrArg₂ (fun u v ↦ relativeSingularCohomologyUnionCup ℚ A₀ B₀ hA₀ hB₀ n r u v)
      hleft hright
  have castPullback {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) (D : Set X) (S T : Set Y) (hST : S = T)
      (hfS : Set.MapsTo f D S) (hfT : Set.MapsTo f D T) (k : ℕ)
      (u : relativeSingularCohomology ℚ S k) :
      relativeSingularCohomologyPullback ℚ f hfT k
          ((eqToIso (congrArg (fun A ↦ relativeSingularCohomology ℚ A k) hST)).hom u) =
        relativeSingularCohomologyPullback ℚ f hfS k u := by
    subst T
    rfl
  have hd : relativeSingularCohomologyPullback ℚ t ht (n + r) d = d₀ := by
    change relativeSingularCohomologyPullback ℚ t ht (n + r)
      ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology ℚ S (n + r)) hS)).hom c) = _
    rw [castPullback t P (A ∪ B) ({y}ᶜ : Set T) hS htS ht]
    have hsquare : relativeSingularCohomologyPullback ℚ t htS (n + r) c =
        relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r)
          (relativeSingularCohomologyPullback ℚ t htaB (n + r) c) := by
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp ℚ (ContinuousMap.id T) t hP htaB (n + r)]
      rfl
    exact hsquare.trans (congrArg
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r)) hc)
  -- Translate the same original local cycles, apply the zero-point formula, then translate back.
  have htEval := nativeTranslation_evaluation (n + r) y d
  change _ = _ at htEval
  rw [hd] at htEval
  have hzero := relativeSingularCohomologyUnionCup_local_evaluation n r a₀ b hP
  have hvEval := nativeTranslation_evaluation n x a
  exact htEval.trans (hzero.trans (congrArg (· *
    (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ {w : W | w ≠ 0}) r b
      (relativeSingularHomologyRationalization {w : W | w ≠ 0} r
        (realOrientationCycle (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.orientation))).down) hvEval.symm))


end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalOrientationTransport

/-!
# The integral sign of a specified homological orientation in a fixed chart

Public module ID: M1908.

The chart sign compares the actual positive Euclidean local cycle with the
given integral local generator. It is an integral unit and is locally constant
in one fixed chart. The comparison retains signed zero-dimensional points.

Source: Hatcher, Algebraic Topology, section 3.3. All transport uses the original
open-excision chart equivalence and translations of the specified simplex.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The translated positive Euclidean local cycle remains a primitive integral generator. -/
theorem euclideanLocalOrientationCycle_is_generator
    (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    Function.Bijective (fun m : ℤ ↦ m • euclideanLocalOrientationCycle n a) := by
  let V := EuclideanSpace ℝ (Fin n)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let t : C(V, V) := ⟨fun v ↦ a + v, continuous_const.add continuous_id⟩
  let s : C(V, V) := ⟨fun v ↦ v - a, continuous_id.sub continuous_const⟩
  have ht : Set.MapsTo t {v : V | v ≠ 0} ({a}ᶜ : Set V) :=
    fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero a).symm))
  have hs : Set.MapsTo s ({a}ᶜ : Set V) {v : V | v ≠ 0} :=
    fun _ hv h ↦ hv (sub_eq_zero.mp h)
  let T := relativeSingularHomologyMap ℤ t ht n
  let : IsIso T := isIso_relativeSingularHomologyMap_of_inverse ℤ t s ht hs
    (by apply ContinuousMap.ext; intro v; dsimp [t, s]; abel)
    (by apply ContinuousMap.ext; intro v; dsimp [t, s]; abel) n
  have h := ((ConcreteCategory.isIso_iff_bijective T).mp inferInstance).comp
    (realOrientationCycle_is_generator b b.orientation)
  convert h using 1
  funext m
  exact (map_zsmul T.hom m (realOrientationCycle b b.orientation)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Translation between two points carries the actual positive Euclidean local cycle. -/
theorem euclideanLocalOrientationCycle_translate
    (n : ℕ) (a b : EuclideanSpace ℝ (Fin n)) :
    relativeSingularHomologyMap ℤ
        (⟨fun v : EuclideanSpace ℝ (Fin n) ↦ b + (v - a),
          continuous_const.add (continuous_id.sub continuous_const)⟩ : C(_, _))
        (A := ({a}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
        (B := ({b}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
        (fun _ hv heq ↦ hv (sub_eq_zero.mp
          (add_left_cancel (heq.trans (add_zero _).symm)))) n
        (euclideanLocalOrientationCycle n a) = euclideanLocalOrientationCycle n b := by
  let V := EuclideanSpace ℝ (Fin n)
  let t : C(V, V) := ⟨fun v ↦ b + (v - a),
    continuous_const.add (continuous_id.sub continuous_const)⟩
  let p : C(V, V) := ⟨fun v ↦ a + v, continuous_const.add continuous_id⟩
  let q : C(V, V) := ⟨fun v ↦ b + v, continuous_const.add continuous_id⟩
  have ht : Set.MapsTo t ({a}ᶜ : Set V) ({b}ᶜ : Set V) :=
    fun _ hv heq ↦ hv (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))
  have hp : Set.MapsTo p {v : V | v ≠ 0} ({a}ᶜ : Set V) :=
    fun _ hv heq ↦ hv (add_left_cancel (heq.trans (add_zero _).symm))
  have hq : Set.MapsTo q {v : V | v ≠ 0} ({b}ᶜ : Set V) :=
    fun _ hv heq ↦ hv (add_left_cancel (heq.trans (add_zero _).symm))
  have hmaps : relativeSingularHomologyMap ℤ p hp n ≫
      relativeSingularHomologyMap ℤ t ht n = relativeSingularHomologyMap ℤ q hq n := by
    change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n
    rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
    have heq : t.comp p = q := by
      apply ContinuousMap.ext
      intro v
      change b + (a + v - a) = b + v
      abel
    generalize_proofs at *
    generalize hfun : t.comp p = f at *
    clear hfun
    subst f
    rfl
  exact congrArg (fun H ↦ H (realOrientationCycle
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation)) hmaps

variable {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  (O : HomologicalOrientation n M)
  (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

/-- The integral comparison of this chart-positive cycle with the specified local generator. -/
def homologicalOrientationChartSign (x : M) (hx : x ∈ e.source) : ℤ :=
  (O.localGenerator x).symm
    ((localHomologyChartEquiv e x hx n).symm (euclideanLocalOrientationCycle n (e x)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison of the two primitive integral local generators is a unit. -/
theorem isUnit_homologicalOrientationChartSign (x : M) (hx : x ∈ e.source) :
    IsUnit (homologicalOrientationChartSign O e x hx) := by
  let C := localHomologyChartEquiv e x hx n
  let G := O.localGenerator x
  have hbij := G.symm.bijective.comp
    (C.symm.bijective.comp (euclideanLocalOrientationCycle_is_generator n (e x)))
  apply IsUnit.isUnit_iff_mulRight_bijective.mpr
  convert hbij using 1
  funext m
  change m * homologicalOrientationChartSign O e x hx =
    G.symm (C.symm (m • euclideanLocalOrientationCycle n (e x)))
  rw [map_zsmul, map_zsmul, smul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same sign gives the chart image of the specified local generator at one. -/
theorem localHomologyChartEquiv_localGenerator
    (x : M) (hx : x ∈ e.source) :
    localHomologyChartEquiv e x hx n (O.localGenerator x 1) =
      homologicalOrientationChartSign O e x hx • euclideanLocalOrientationCycle n (e x) := by
  let s := homologicalOrientationChartSign O e x hx
  have hs : s * s = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_homologicalOrientationChartSign O e x hx) with h | h
    · change s = 1 at h
      rw [h]
      norm_num
    · change s = -1 at h
      rw [h]
      norm_num
  apply (localHomologyChartEquiv e x hx n).symm.injective
  apply (O.localGenerator x).symm.injective
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, map_zsmul, map_zsmul]
  change 1 = s * s
  exact hs.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In one fixed chart the sign of a given homological orientation is locally constant. -/
theorem exists_locally_constant_homologicalOrientationChartSign
    (x : M) (hx : x ∈ e.source) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ hUe : U ⊆ e.source,
      ∀ y (hy : y ∈ U), homologicalOrientationChartSign O e y (hUe hy) =
        homologicalOrientationChartSign O e x hx := by
  obtain ⟨U, hU, hxU, hUe, c, hc⟩ := exists_chart_localOrientation_transport O e x hx
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨m, hm⟩ := (realOrientationCycle_is_generator b b.orientation).surjective c
  have hsign (y : M) (hy : y ∈ U) :
      homologicalOrientationChartSign O e y (hUe hy) = m := by
    have h := (hc y hy).trans (localHomologyChartEquiv_localGenerator O e y (hUe hy))
    rw [← hm, map_zsmul] at h
    exact ((euclideanLocalOrientationCycle_is_generator n (e y)).injective h).symm
  exact ⟨U, hU, hxU, hUe, fun y hy ↦ (hsign y hy).trans (hsign x hxU).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On a common open source, two actual base charts differ by the product of their
integral signs after translating their distinguished coordinate points to agree. -/
theorem relativeSingularHomologyMap_chart_eq_sign_smul
    (f : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (U : Set M) (hU : IsOpen U) (hUe : U ⊆ e.source) (hUf : U ⊆ f.source) (x : U) :
    relativeSingularHomologyMap ℤ
        (⟨fun y : U ↦ f y.val, f.continuousOn.comp_continuous continuous_subtype_val
          (fun y ↦ hUf y.property)⟩ : C(U, EuclideanSpace ℝ (Fin n)))
        (A := ({x}ᶜ : Set U)) (B := ({f x.val}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
        (fun y hy heq ↦ hy (Subtype.ext (f.injOn (hUf y.property) (hUf x.property) heq))) n =
      (homologicalOrientationChartSign O f x.val (hUf x.property) *
        homologicalOrientationChartSign O e x.val (hUe x.property)) •
        relativeSingularHomologyMap ℤ
          (⟨fun y : U ↦ f x.val + (e y.val - e x.val),
            continuous_const.add
              ((e.continuousOn.comp_continuous continuous_subtype_val
                (fun y ↦ hUe y.property)).sub continuous_const)⟩ :
            C(U, EuclideanSpace ℝ (Fin n)))
          (A := ({x}ᶜ : Set U)) (B := ({f x.val}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
          (fun y hy heq ↦ hy (Subtype.ext (e.injOn (hUe y.property) (hUe x.property)
            (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))))) n := by
  let V := EuclideanSpace ℝ (Fin n)
  let j : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Set.MapsTo j ({x}ᶜ : Set U) ({x.val}ᶜ : Set M) :=
    fun y hy heq ↦ hy (Subtype.ext heq)
  let P : C(U, V) := ⟨fun y ↦ f y.val, f.continuousOn.comp_continuous
    continuous_subtype_val (fun y ↦ hUf y.property)⟩
  let Q : C(U, V) := ⟨fun y ↦ e y.val, e.continuousOn.comp_continuous
    continuous_subtype_val (fun y ↦ hUe y.property)⟩
  have hP : Set.MapsTo P ({x}ᶜ : Set U) ({f x.val}ᶜ : Set V) :=
    fun y hy heq ↦ hy (Subtype.ext (f.injOn (hUf y.property) (hUf x.property) heq))
  have hQ : Set.MapsTo Q ({x}ᶜ : Set U) ({e x.val}ᶜ : Set V) :=
    fun y hy heq ↦ hy (Subtype.ext (e.injOn (hUe y.property) (hUe x.property) heq))
  let t : C(V, V) := ⟨fun v ↦ f x.val + (v - e x.val),
    continuous_const.add (continuous_id.sub continuous_const)⟩
  have ht : Set.MapsTo t ({e x.val}ᶜ : Set V) ({f x.val}ᶜ : Set V) :=
    fun _ hv heq ↦ hv (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))
  let J := (localHomologyOpenInclusionEquiv U hU x n).toModuleIso
  let Ce := (localHomologyChartEquiv e x.val (hUe x.property) n).toModuleIso
  let Cf := (localHomologyChartEquiv f x.val (hUf x.property) n).toModuleIso
  let PH := relativeSingularHomologyMap ℤ P hP n
  let QH := relativeSingularHomologyMap ℤ Q hQ n
  let T := relativeSingularHomologyMap ℤ t ht n
  let se := homologicalOrientationChartSign O e x.val (hUe x.property)
  let sf := homologicalOrientationChartSign O f x.val (hUf x.property)
  have hPe : J.hom ≫ Ce.hom = QH := localHomologyChartEquiv_naturality
    e x.val (hUe x.property) j (fun y ↦ hUe y.property) hj n
  have hPf : J.hom ≫ Cf.hom = PH := localHomologyChartEquiv_naturality
    f x.val (hUf x.property) j (fun y ↦ hUf y.property) hj n
  -- The translation between the two coordinate points carries the actual positive simplex.
  have hpositive : T (euclideanLocalOrientationCycle n (e x.val)) =
      euclideanLocalOrientationCycle n (f x.val) :=
    euclideanLocalOrientationCycle_translate n (e x.val) (f x.val)
  let G := (O.localGenerator x.val).trans J.symm.toLinearEquiv
  have hJG : J.hom (G 1) = O.localGenerator x.val 1 := J.inv_hom_id_apply _
  have hPgen : PH (G 1) = sf • euclideanLocalOrientationCycle n (f x.val) := by
    have h := congrArg (fun H ↦ H (G 1)) hPf
    change Cf.hom (J.hom (G 1)) = PH (G 1) at h
    rw [hJG] at h
    exact h.symm.trans (localHomologyChartEquiv_localGenerator O f x.val (hUf x.property))
  have hQgen : (QH ≫ T) (G 1) = se • euclideanLocalOrientationCycle n (f x.val) := by
    have h := congrArg (fun H ↦ H (G 1)) hPe
    change Ce.hom (J.hom (G 1)) = QH (G 1) at h
    rw [hJG] at h
    change T (QH (G 1)) = _
    rw [← h]
    change T (localHomologyChartEquiv e x.val (hUe x.property) n
      (O.localGenerator x.val 1)) = _
    rw [localHomologyChartEquiv_localGenerator, map_zsmul, hpositive]
  have hse : se * se = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_homologicalOrientationChartSign O e x.val
      (hUe x.property)) with h | h
    · change se = 1 at h
      rw [h]
      norm_num
    · change se = -1 at h
      rw [h]
      norm_num
  have hscalar : PH = (sf * se) • (QH ≫ T) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨m, rfl⟩ := G.surjective z
    have hm : G m = m • G 1 := by
      simpa using (map_zsmul G m (1 : ℤ))
    rw [hm]
    change PH (m • G 1) = (sf * se) • (QH ≫ T) (m • G 1)
    rw [map_zsmul, map_zsmul, hPgen, hQgen, smul_smul, smul_smul, smul_smul]
    congr 1
    calc
      m * sf = m * sf * (se * se) := by rw [hse, mul_one]
      _ = sf * se * m * se := by ring
  change PH = (sf * se) • relativeSingularHomologyMap ℤ (t.comp Q) (ht.comp hQ) n
  rw [hscalar]
  congr 1
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]

end AtiyahSinger

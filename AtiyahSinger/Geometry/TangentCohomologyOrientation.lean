/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentMusical
public import AtiyahSinger.Topology.CohomologyOrientation
public import AtiyahSinger.Topology.EuclideanLocalHomology
public import AtiyahSinger.Topology.HomologicalOrientation
public import AtiyahSinger.Topology.LocalHomologyChart
public import AtiyahSinger.Topology.LocalHomologyChartDifferentiation
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality
public import AtiyahSinger.Topology.SingularIntegralEvaluation
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# The tangent Thom orientation induced by the original manifold orientation

Public module ID: M1471.

A homological orientation O is the original integral orientation of M. The
native tangent chart at x identifies T_x M with the Euclidean chart model.
Translate its linear coordinates to chartAt x x, then invert the existing
local-homology chart comparison. This gives an actual equivalence from the
punctured tangent fiber's homology to the original local homology of M at x.

The tangent fiber cohomology generator is uniquely normalized by evaluating
to one on the inverse image of O.localGenerator x 1 under that equivalence.
Evaluation is the original relative cap followed by the original degree-zero
augmentation. The locally compatible family of these exact generators is the
integral tangent CohomologyOrientation. Its existing rationalization therefore
uses the same manifold orientation; no independent fiber orientation enters.

This includes signed zero-dimensional points. The negative point orientation
induces the negative degree-zero fiber generator, not a negative empty basis.
The local homology equivalence and normalized fiber classes need no metric.
The existing CohomologyOrientation API requires normed fibers, whereas native
TangentSpace supplies only a topological module. Its final packaging uses the
supplied smooth metric's native RiemannianBundle instances, which retain the
original fiber topology, operations and total topology. The same metric is
later used by the tangent symbol and supported Chern character. No independent
orientation, compactness, connectedness or positive dimension is assumed.
The common universe is Type, as in the existing local chart comparison API.

Sources: Hatcher, Algebraic Topology, section 3.3, for local orientations;
Milnor--Stasheff, Characteristic Classes, section 9, for normalized tangent
Thom orientations; Lawson--Michelsohn, Spin Geometry, III.13, (13.24), p.255.
The explicit native-chart/cap implementation and signed rank-zero treatment
are project supplements. The proofs compare actual chart transitions with
their derivatives, transport the original compatible local generators, and
use integral Kronecker duality to construct their common local fiber class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory
open scoped Bundle Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "T" => (TangentSpace 𝓘(ℝ, E) : M → Type)

/-- The native tangent linear chart, translated and followed by actual local chart excision. -/
def tangentLocalHomologyEquiv (x : M) :
    relativeSingularHomology ℤ (Set.ofPred (fun v : T x ↦ v ≠ 0)) n ≃ₗ[ℤ]
      relativeSingularHomology ℤ ({x}ᶜ : Set M) n := by
  -- The preferred tangent trivialization is the derivative coordinate map of this base chart.
  let e : T x ≃L[ℝ] E := VectorBundle.continuousLinearEquivAt ℝ E T x
  let a : E := chartAt E x x
  -- Translate that actual linear coordinate map so that the zero tangent vector maps to a.
  let h : T x ≃ₜ E :=
    { toFun := fun v ↦ a + e v
      invFun := fun w ↦ e.symm (w - a)
      left_inv := by
        intro v
        simp
      right_inv := by
        intro w
        simp
      continuous_toFun := continuous_const.add e.continuous
      continuous_invFun := e.symm.continuous.comp (continuous_id.sub continuous_const) }
  have h0 : h (0 : T x) = a := by
    change a + e 0 = a
    simp
  let hLocal : relativeSingularHomology ℤ ({0}ᶜ : Set (T x)) n ≃ₗ[ℤ]
      relativeSingularHomology ℤ ({a}ᶜ : Set E) n := by
    exact Eq.ndrec (motive := fun z : E ↦
      relativeSingularHomology ℤ ({0}ᶜ : Set (T x)) n ≃ₗ[ℤ]
        relativeSingularHomology ℤ ({z}ᶜ : Set E) n)
      (localHomologyHomeomorphEquiv h (0 : T x) n) h0
  -- Return to the original manifold point through exactly the chart's excision equivalence.
  exact hLocal.trans
    (localHomologyChartEquiv (chartAt E x) x (mem_chart_source E x) n).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Any fixed native tangent chart gives the same base-induced local homology map. -/
theorem tangentLocalHomologyEquiv_chartAt
    (x y : M) (hy : y ∈ (chartAt E x).source)
    (z : relativeSingularHomology ℤ {v : T y | v ≠ 0} n) :
    (localHomologyChartEquiv (chartAt E x) y hy n) (tangentLocalHomologyEquiv y z) =
      relativeSingularHomologyMap ℤ
        (⟨fun v : T y ↦ chartAt E x y +
          (trivializationAt E T x).continuousLinearEquivAt ℝ y hy v,
          continuous_const.add
            ((trivializationAt E T x).continuousLinearEquivAt ℝ y hy).continuous⟩ : C(T y, E))
        (A := Set.ofPred (fun v : T y ↦ v ≠ 0))
        (B := ({chartAt E x y}ᶜ : Set E))
        (fun _ hv h ↦ hv
          (((trivializationAt E T x).continuousLinearEquivAt ℝ y hy).injective
            ((add_left_cancel (h.trans (add_zero _).symm)).trans (map_zero _).symm))) n z := by
  let ep : T y ≃L[ℝ] E := VectorBundle.continuousLinearEquivAt ℝ E T y
  let ef : T y ≃L[ℝ] E := (trivializationAt E T x).continuousLinearEquivAt ℝ y hy
  let L : E ≃L[ℝ] E := ep.symm.trans ef
  -- Native preferred tangent coordinates are the derivative of the identical chart transition.
  have hep (v : T y) : ep v = v := by
    change tangentCoordChange 𝓘(ℝ, E) y y y v = v
    exact tangentCoordChange_self (by simp only [mfld_simps])
  have hL : L.toContinuousLinearMap = tangentCoordChange 𝓘(ℝ, E) y x y := by
    apply ContinuousLinearMap.ext
    intro v
    have hinv : ep.symm v = v := (hep (ep.symm v)).symm.trans (ep.apply_symm_apply v)
    change ef (ep.symm v) = _
    rw [hinv]
    rfl
  have hd : HasFDerivAt (fun v : E ↦ chartAt E x ((chartAt E y).symm v))
      L.toContinuousLinearMap (chartAt E y y) := by
    rw [hL]
    have h := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, E))
      (x := y) (y := x) (z := y)
      (by simpa only [mfld_simps] using And.intro (mem_chart_source E y) hy)
    simp only [mfld_simps, hasFDerivWithinAt_univ] at h
    exact h
  let cp := (localHomologyChartEquiv (chartAt E y) y (mem_chart_source E y) n).toModuleIso
  let cf := (localHomologyChartEquiv (chartAt E x) y hy n).toModuleIso
  let a := chartAt E y y
  let b := chartAt E x y
  let p : C(T y, E) := ⟨ep, ep.continuous⟩
  have hp : Set.MapsTo p {v | v ≠ 0} {w | w ≠ 0} :=
    fun _ hv h ↦ hv (ep.injective (h.trans (map_zero ep).symm))
  let ta : C(E, E) := ⟨fun v ↦ a + v, continuous_const.add continuous_id⟩
  let tb : C(E, E) := ⟨fun v ↦ b + v, continuous_const.add continuous_id⟩
  have hta : Set.MapsTo ta {v | v ≠ 0} ({a}ᶜ : Set E) :=
    fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero _).symm))
  have htb : Set.MapsTo tb {v | v ≠ 0} ({b}ᶜ : Set E) :=
    fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero _).symm))
  let l : C(E, E) := ⟨L, L.continuous⟩
  have hl : Set.MapsTo l {v | v ≠ 0} {w | w ≠ 0} :=
    fun _ hv h ↦ hv (L.injective (h.trans (map_zero L).symm))
  let P := relativeSingularHomologyMap ℤ p hp n
  let Ta := relativeSingularHomologyMap ℤ ta hta n
  let Tb := relativeSingularHomologyMap ℤ tb htb n
  let Lh := relativeSingularHomologyMap ℤ l hl n
  let tIso := (tangentLocalHomologyEquiv (n := n) y).toModuleIso
  have htransition : Ta ≫ cp.inv ≫ cf.hom = Lh ≫ Tb :=
    localHomologyChartEquiv_transition_derivative (chartAt E y) (chartAt E x) y
      (mem_chart_source E y) hy L hd n
  -- Retain the original zero-point transport in the translated preferred chart definition.
  have hpreferred : tIso.hom ≫ cp.hom = P ≫ Ta := by
    let h : T y ≃ₜ E :=
      { toFun := fun v ↦ a + ep v
        invFun := fun w ↦ ep.symm (w - a)
        left_inv := by intro v; simp
        right_inv := by intro w; simp
        continuous_toFun := continuous_const.add ep.continuous
        continuous_invFun := ep.symm.continuous.comp (continuous_id.sub continuous_const) }
    have hzero : h 0 = a := by change a + ep 0 = a; simp
    have hvalue {c : E} (hc : h 0 = c) (w : relativeSingularHomology ℤ {v : T y | v ≠ 0} n) :
        (Eq.ndrec (motive := fun c : E ↦
          relativeSingularHomology ℤ ({0}ᶜ : Set (T y)) n ≃ₗ[ℤ]
            relativeSingularHomology ℤ ({c}ᶜ : Set E) n)
          (localHomologyHomeomorphEquiv h 0 n) hc) w =
          relativeSingularHomologyMap ℤ (⟨h, h.continuous⟩ : C(T y, E))
            (A := Set.ofPred (fun v : T y ↦ v ≠ 0)) (B := ({c}ᶜ : Set E))
            (fun _ hv heq ↦ hv (h.injective (heq.trans hc.symm))) n w := by
      subst c
      rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    change (localHomologyChartEquiv (chartAt E y) y (mem_chart_source E y) n)
      ((localHomologyChartEquiv (chartAt E y) y (mem_chart_source E y) n).symm
        ((Eq.ndrec (motive := fun c : E ↦
          relativeSingularHomology ℤ ({0}ᶜ : Set (T y)) n ≃ₗ[ℤ]
            relativeSingularHomology ℤ ({c}ᶜ : Set E) n)
          (localHomologyHomeomorphEquiv h 0 n) hzero) w)) = _
    rw [LinearEquiv.apply_symm_apply, hvalue hzero]
    have hcomp := congrArg (fun F ↦ HomologicalComplex.homologyMap F n)
      (relativeSingularChainsMap_comp ℤ p ta hp hta)
    rw [HomologicalComplex.homologyMap_comp] at hcomp
    exact congrArg (fun F ↦ F w) hcomp
  -- The derivative comparison cancels the preferred chart and leaves this same fixed chart.
  have hmain : tIso.hom ≫ cf.hom = P ≫ Lh ≫ Tb := by
    calc
      tIso.hom ≫ cf.hom = tIso.hom ≫ cp.hom ≫ cp.inv ≫ cf.hom := by
        simp only [cp.hom_inv_id_assoc]
      _ = (P ≫ Ta) ≫ cp.inv ≫ cf.hom := by rw [← Category.assoc tIso.hom, hpreferred]
      _ = P ≫ (Ta ≫ cp.inv ≫ cf.hom) := by simp only [Category.assoc]
      _ = P ≫ Lh ≫ Tb := by rw [htransition]
  have hcomp : P ≫ Lh ≫ Tb =
      relativeSingularHomologyMap ℤ (tb.comp (l.comp p)) (htb.comp (hl.comp hp)) n := by
    dsimp only [P, Lh, Tb, relativeSingularHomologyMap]
    rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hfunction : tb.comp (l.comp p) =
      (⟨fun v : T y ↦ b + ef v, continuous_const.add ef.continuous⟩ : C(T y, E)) := by
    apply ContinuousMap.ext
    intro v
    change b + ef (ep.symm (ep v)) = b + ef v
    rw [ep.symm_apply_apply]
  have hmap {q : C(T y, E)} (hq : Set.MapsTo q {v | v ≠ 0} ({b}ᶜ : Set E))
      (heq : tb.comp (l.comp p) = q) :
      relativeSingularHomologyMap ℤ (tb.comp (l.comp p)) (htb.comp (hl.comp hp)) n =
        relativeSingularHomologyMap ℤ q hq n := by
    subst q
    rfl
  have hfinal := hmap (fun _ hv h ↦ hv
    (ef.injective ((add_left_cancel (h.trans (add_zero _).symm)).trans (map_zero _).symm)))
    hfunction
  exact congrArg (fun F ↦ F z) (hmain.trans (hcomp.trans hfinal))


/-- Original cap evaluation on the tangent local generator induced by the given base orientation. -/
def tangentCohomologyFiberEvaluation (O : HomologicalOrientation n M) (x : M)
    (a : relativeSingularCohomology ℤ (Set.ofPred (fun v : T x ↦ v ≠ 0)) n) : ℤ :=
  (((TopCat.of (T x)).singularHomology₀ε (singularCoefficient ℤ))
    (relativeSingularCapProduct ℤ (Set.ofPred (fun v : T x ↦ v ≠ 0)) n 0 a
      ((tangentLocalHomologyEquiv x).symm (O.localGenerator x 1)))).down

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same oriented tangent local generator has one integral dual cohomology generator. -/
theorem existsUnique_tangentCohomologyFiberClass (O : HomologicalOrientation n M) (x : M) :
    ∃! a : relativeSingularCohomology ℤ (Set.ofPred (fun v : T x ↦ v ≠ 0)) n,
      tangentCohomologyFiberEvaluation O x a = 1 := by
  -- Transport the given base generator through precisely the original tangent comparison.
  let e := (O.localGenerator x).trans (tangentLocalHomologyEquiv x).symm
  have hgen : Function.Bijective (fun a : ℤ ↦
      (relativeSingularHomology ℤ {v : T x | v ≠ 0} n).isModule.smul a (e 1)) := by
    have he (a : ℤ) :
        (relativeSingularHomology ℤ {v : T x | v ≠ 0} n).isModule.smul a (e 1) = e a := by
      simp_rw [int_smul_eq_zsmul]
      have he := (e.toAddMonoidHom.map_zsmul a (1 : ℤ)).symm
      simp only [zsmul_eq_mul, mul_one, Int.cast_id] at he
      change a • e 1 = e a at he
      exact he
    simpa only [he] using e.bijective
  -- Native tangent coordinates suffice for the preceding-degree vanishing; no metric enters.
  have hprev : n = 0 ∨ Subsingleton
      (relativeSingularHomology ℤ {v : T x | v ≠ 0} (n - 1)) := by
    by_cases hn : n = 0
    · exact Or.inl hn
    · refine Or.inr ?_
      exact subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv ℤ
        ((VectorBundle.continuousLinearEquivAt ℝ E T x).trans
          (EuclideanSpace.equiv (Fin n) ℝ)) (n - 1) (by omega)
  -- Integral Kronecker evaluation is the same cap followed by augmentation, including n=0.
  have hbij := relativeSingularCapProduct_augmentation_bijective_of_generator ℤ
    {v : T x | v ≠ 0} n (e 1) hgen hprev
  obtain ⟨a, ha⟩ := hbij.surjective 1
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact hbij.injective (hb.trans ha.symm)

/-- The actual fiber class selected by evaluation one on the original oriented local generator. -/
def tangentCohomologyFiberClass (O : HomologicalOrientation n M) (x : M) :
    relativeSingularCohomology ℤ (Set.ofPred (fun v : T x ↦ v ≠ 0)) n :=
  (existsUnique_tangentCohomologyFiberClass O x).exists.choose

/-- Each selected integral dual class freely generates the original fiber cohomology. -/
theorem tangentCohomologyFiberClass_is_generator (O : HomologicalOrientation n M) (x : M) :
    Function.Bijective (fun a : ℤ ↦ a • tangentCohomologyFiberClass O x) := by
  let F : relativeSingularCohomology ℤ {v : T x | v ≠ 0} n →+ ℤ :=
    { toFun := tangentCohomologyFiberEvaluation O x
      map_zero' := by
        unfold tangentCohomologyFiberEvaluation
        erw [map_zero, LinearMap.zero_apply, map_zero]
        rfl
      map_add' := by
        intro a b
        unfold tangentCohomologyFiberEvaluation
        erw [map_add, LinearMap.add_apply, map_add]
        rfl }
  have hnorm : F (tangentCohomologyFiberClass O x) = 1 :=
    (existsUnique_tangentCohomologyFiberClass O x).exists.choose_spec
  -- Translating a kernel element by the chosen class reduces injectivity to uniqueness at one.
  have hinj : Function.Injective F := by
    intro a b hab
    have hvalue : F (a - b + tangentCohomologyFiberClass O x) = 1 := by
      rw [map_add, map_sub, hab, sub_self, zero_add, hnorm]
    have heq := (existsUnique_tangentCohomologyFiberClass O x).unique hvalue hnorm
    exact sub_eq_zero.mp (add_right_cancel (heq.trans (zero_add _).symm))
  constructor
  · intro a b hab
    have h := congrArg F hab
    simpa only [map_zsmul, hnorm, smul_eq_mul, mul_one] using h
  · intro a
    refine ⟨F a, hinj ?_⟩
    rw [map_zsmul, hnorm, smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Local compatibility of the base orientation induces that of the same tangent fiber classes. -/
theorem tangentCohomologyFiberClass_locally_compatible
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M) :
    letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
    ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ c : relativeSingularCohomology ℤ (bundleNonzeroOver n T U) n,
        ∀ (y : M) (hy : y ∈ U),
          relativeSingularCohomologyPullback ℤ (bundleFiberInclusionOver n T U y hy)
            (A := Set.ofPred (fun v : T y ↦ v ≠ 0)) (B := bundleNonzeroOver n T U)
            (fun _ hv ↦ hv) n c = tangentCohomologyFiberClass O y := by
  /- One fixed chart turns the original compatible local generators into one
  translated Euclidean class. The native tangent transition is the derivative
  of the corresponding chart transition, so the actual local linearization
  theorem identifies each base-induced tangent generator with this same class.
  Integral Kronecker duality gives a model cohomology class evaluating to one.
  Pull it back through the fixed bundle trivialization; pairing naturality and
  the original uniqueness theorem identify all of its fiber restrictions.
  This argument includes signed zero-dimensional points. The supplied metric
  only satisfies the normed-bundle API and introduces no orientation choice. -/
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  intro x
  obtain ⟨U, hU, hx, hUe, z, hz⟩ :=
    exists_chart_localOrientation_transport O (chartAt E x) x (mem_chart_source E x)
  let t := trivializationAt E T x
  let e (y : U) : T y.val ≃L[ℝ] E := t.continuousLinearEquivAt ℝ y.val (hUe y.property)
  let f (y : U) : C(T y.val, E) := ⟨e y, (e y).continuous⟩
  have hf (y : U) : Set.MapsTo (f y) {v | v ≠ 0} {w | w ≠ 0} :=
    fun _ hv h ↦ hv ((e y).injective (h.trans (map_zero (e y)).symm))
  let γ (y : U) := (tangentLocalHomologyEquiv y.val).symm (O.localGenerator y.val 1)
  -- In this one fixed tangent trivialization the original base-induced generators are constant.
  have hcoord (y : U) : relativeSingularHomologyMap ℤ (f y) (hf y) n (γ y) = z := by
    let a := chartAt E x y.val
    let ta : C(E, E) := ⟨fun v ↦ a + v, continuous_const.add continuous_id⟩
    let sa : C(E, E) := ⟨fun v ↦ v - a, continuous_id.sub continuous_const⟩
    have hta : Set.MapsTo ta {v | v ≠ 0} ({a}ᶜ : Set E) :=
      fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero _).symm))
    have hsa : Set.MapsTo sa ({a}ᶜ : Set E) {v | v ≠ 0} :=
      fun _ hv h ↦ hv (sub_eq_zero.mp h)
    let : IsIso (relativeSingularHomologyMap ℤ ta hta n) :=
      isIso_relativeSingularHomologyMap_of_inverse ℤ ta sa hta hsa
        (by apply ContinuousMap.ext; intro v; dsimp [ta, sa]; abel)
        (by apply ContinuousMap.ext; intro v; dsimp [ta, sa]; abel) n
    apply (ConcreteCategory.isIso_iff_bijective
      (relativeSingularHomologyMap ℤ ta hta n)).mp inferInstance |>.injective
    have hnative := tangentLocalHomologyEquiv_chartAt x y.val (hUe y.property) (γ y)
    have hcomp := congrArg (fun F ↦ HomologicalComplex.homologyMap F n)
      (relativeSingularChainsMap_comp ℤ (f y) ta (hf y) hta)
    rw [HomologicalComplex.homologyMap_comp] at hcomp
    have hvalue := congrArg (fun F ↦ F (γ y)) hcomp
    change relativeSingularHomologyMap ℤ ta hta n
      (relativeSingularHomologyMap ℤ (f y) (hf y) n (γ y)) = _
    refine hvalue.symm.trans (hnative.symm.trans ?_)
    change (localHomologyChartEquiv (chartAt E x) y.val (hUe y.property) n)
      ((tangentLocalHomologyEquiv y.val)
        ((tangentLocalHomologyEquiv y.val).symm (O.localGenerator y.val 1))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (hz y.val y.property).symm
  -- The constant model generator has an integral dual under the original cap augmentation.
  let xU : U := ⟨x, hx⟩
  let fx := f xU
  let gx : C(E, T x) := ⟨(e xU).symm, (e xU).symm.continuous⟩
  have hgx : Set.MapsTo gx {w | w ≠ 0} {v | v ≠ 0} :=
    fun _ hw h ↦ hw ((e xU).symm.injective (h.trans (map_zero _).symm))
  let Hx := relativeSingularHomologyMap ℤ fx (hf xU) n
  let : IsIso Hx := isIso_relativeSingularHomologyMap_of_inverse ℤ fx gx (hf xU) hgx
    (by apply ContinuousMap.ext; intro v; exact (e xU).symm_apply_apply v)
    (by apply ContinuousMap.ext; intro v; exact (e xU).apply_symm_apply v) n
  let q := ((O.localGenerator x).trans (tangentLocalHomologyEquiv x).symm).trans
    (asIso Hx).toLinearEquiv
  have hq : q 1 = z := hcoord xU
  have hgen : Function.Bijective (fun a : ℤ ↦
      (relativeSingularHomology ℤ {v : E | v ≠ 0} n).isModule.smul a z) := by
    have hvalue (a : ℤ) :
        (relativeSingularHomology ℤ {v : E | v ≠ 0} n).isModule.smul a z = q a := by
      rw [← hq]
      simp_rw [int_smul_eq_zsmul]
      have h := (q.toAddMonoidHom.map_zsmul a (1 : ℤ)).symm
      simp only [zsmul_eq_mul, mul_one, Int.cast_id] at h
      exact h
    simpa only [hvalue] using q.bijective
  have hprev : n = 0 ∨ Subsingleton
      (relativeSingularHomology ℤ {v : E | v ≠ 0} (n - 1)) := by
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr (subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv
        ℤ (EuclideanSpace.equiv (Fin n) ℝ) (n - 1) (by omega))
  obtain ⟨a, ha⟩ :=
    (relativeSingularCapProduct_augmentation_bijective_of_generator ℤ {v : E | v ≠ 0}
      n z hgen hprev).surjective 1
  let p : C(BundleTotalOver n T U, E) :=
    ⟨fun w ↦ (t w.val).2,
      (t.continuousOn.comp_continuous continuous_subtype_val
        (fun w ↦ t.mem_source.mpr (hUe w.property))).snd⟩
  have hp : Set.MapsTo p (bundleNonzeroOver n T U) {v : E | v ≠ 0} := by
    intro w hw heq
    let y : U := ⟨w.val.proj, w.property⟩
    exact hw ((e y).injective (heq.trans (map_zero _).symm))
  refine ⟨U, hU, hx, relativeSingularCohomologyPullback ℤ p hp n a, ?_⟩
  intro y hy
  let yU : U := ⟨y, hy⟩
  let i := bundleFiberInclusionOver n T U y hy
  have hi : Set.MapsTo i {v | v ≠ 0} (bundleNonzeroOver n T U) := fun _ hv ↦ hv
  have hcomp := congrArg (fun F ↦ F a)
    (relativeSingularCohomologyPullback_comp ℤ i p hi hp n)
  change relativeSingularCohomologyPullback ℤ (p.comp i) (hp.comp hi) n a =
    relativeSingularCohomologyPullback ℤ i hi n
      (relativeSingularCohomologyPullback ℤ p hp n a) at hcomp
  apply (existsUnique_tangentCohomologyFiberClass O y).unique
  · change tangentCohomologyFiberEvaluation O y
      (relativeSingularCohomologyPullback ℤ i hi n
        (relativeSingularCohomologyPullback ℤ p hp n a)) = 1
    rw [← hcomp]
    change tangentCohomologyFiberEvaluation O y
      (relativeSingularCohomologyPullback ℤ (f yU) (hf yU) n a) = 1
    -- Pairing naturality and the same constant generator give precisely the required value one.
    unfold tangentCohomologyFiberEvaluation
    rw [relativeSingularCapProduct_augmentation]
    have hnat := singularCochainHomologyEvaluation_naturality ℤ
      (relativeSingularChains ℤ {v : T y | v ≠ 0})
      (relativeSingularChains ℤ {v : E | v ≠ 0})
      (relativeSingularChainsMap ℤ (f yU) (hf yU)) n a (γ yU)
    change singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ {v : E | v ≠ 0})
      n a (relativeSingularHomologyMap ℤ (f yU) (hf yU) n (γ yU)) =
      singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ {v : T y | v ≠ 0})
        n (relativeSingularCohomologyPullback ℤ (f yU) (hf yU) n a) (γ yU) at hnat
    rw [← hnat, hcoord]
    exact (congrArg ULift.down (relativeSingularCapProduct_augmentation ℤ
      {v : E | v ≠ 0} n a z)).symm.trans ha
  · exact (existsUnique_tangentCohomologyFiberClass O y).exists.choose_spec

/-- The manifold orientation induces the integral Thom orientation of its same tangent bundle. -/
def tangentCohomologyOrientation
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M) :
    letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
    CohomologyOrientation ℤ n T := by
  -- The native metric API supplies only norms, preserving the original topological module.
  letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  exact {
    fiberClass := tangentCohomologyFiberClass O
    is_generator := by
      -- Convert only the integer module action to its underlying additive scalar action.
      intro x
      change Function.Bijective (fun a : ℤ ↦
        (relativeSingularCohomology ℤ (Set.ofPred (fun v : T x ↦ v ≠ 0)) n).isModule.smul a
          (tangentCohomologyFiberClass O x))
      simp_rw [int_smul_eq_zsmul]
      exact tangentCohomologyFiberClass_is_generator O x
    locally_compatible := tangentCohomologyFiberClass_locally_compatible g O }

/-- The tangent Thom fiber class evaluates to one on precisely the base-induced generator. -/
theorem tangentCohomologyOrientation_evaluation
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M) (x : M) :
    letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
    tangentCohomologyFiberEvaluation O x ((tangentCohomologyOrientation g O).fiberClass x) = 1 := by
  /- Unfold the structure's fiberClass, which is exactly the class selected
  from existsUnique_tangentCohomologyFiberClass O x. Its defining evaluation
  is one on the inverse image of this same O.localGenerator x 1. This keeps
  both orientation signs linked and includes signed zero-dimensional points. -/
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  exact (existsUnique_tangentCohomologyFiberClass O x).exists.choose_spec

end AtiyahSinger

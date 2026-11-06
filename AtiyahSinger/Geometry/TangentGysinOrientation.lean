/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleHomologicalOrientation
public import AtiyahSinger.Geometry.TangentCoordinatePermutation
public import AtiyahSinger.Geometry.TangentCohomologyOrientation
public import AtiyahSinger.Geometry.TangentHomologicalOrientation
public import AtiyahSinger.Topology.EuclideanOrientationPermutation

/-!
# The grouped tangent orientation and the canonical interleaved orientation

Public module ID: M1481.

The total orientation induced by the base orientation and its own tangent
fiber cohomology orientation uses base-first coordinates. The existing
canonical tangent orientation uses (x1,v1,...,xn,vn). Their local generators
differ by the sign of the permutation moving the fiber coordinates into
these interleaved positions. The integral degree transport n+n=2*n is explicit.

The fiber orientation is constructed from exactly the same base O. Reversing
O on a component reverses both the base and fiber factors, so their product
remains canonical. Signed zero-dimensional points are included. The supplied
metric g supplies only the existing native normed-bundle instances with
unchanged tangent topology and operations. Compactness is not assumed.

Sources: Lawson--Michelsohn, Spin Geometry, III.13, (13.18) and (13.24),
pp.254--255; Atiyah--Singer III, (2.12)--(2.13), pp.556--557. The explicit
comparison of these actual integral local generators is a project supplement.
It is independent of cohomological degree and of any target index formula.
The proof compares the original chart maps and geometric local cycles, including
the explicit degree transport and the empty coordinate permutation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Topology
open scoped Bundle Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original tangent local generators differ by exactly the grouped/interleaved permutation. -/
theorem bundleHomologicalOrientation_tangent_localGenerator
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M) (z : TM) :
    letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
    (eqToIso (congrArg (relativeSingularHomology ℤ ({z}ᶜ : Set TM))
        (by omega : n + n = 2 * n))).hom
      ((bundleHomologicalOrientation n T O (tangentCohomologyOrientation g O)).localGenerator z 1) =
        (-1 : ℤ) ^ (n * (n - 1) / 2) •
          (tangentHomologicalOrientation (n := n) (M := M)).localGenerator z 1 := by
  /- Stage 1: the tangent fiber class is normalized by evaluation one on
  the inverse image of O.localGenerator x 1 under the actual native linear
  coordinates, translation and local base-chart excision. Thus, in any one
  base chart, its fiber-cap sign equals the base local-generator sign.
  Both signs are integral units, so their product in the grouped total
  normalization is +1. This includes a negative zero-dimensional O.
  Stage 2: use the original native tangent chart at z for both total
  orientations. The grouped construction follows finAddEquivProd.symm;
  the canonical construction follows tangentModelCoordinateEquiv. Moving
  each fiber coordinate past the remaining base coordinates requires
  n*(n-1)/2 transpositions. The local-homology map of this actual linear
  coordinate permutation multiplies the Euclidean generator by that sign.
  Stage 3: transport this equality back through the same chart excision
  maps and the explicit degree equality n+n=2*n. Translation from fiber
  zero to z.snd preserves both local orientations. The same metric's
  native instances preserve the underlying topologies; no total-space
  orientation, compatibility condition or target Gysin equality is supplied
  independently. All arguments are local, so noncompact bases are included. -/
  classical
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  -- The base-induced fiber class makes the two signs in the original grouped chart cancel.
  have hcoeff : bundleTotalLocalOrientationCoefficient n T O
      (tangentCohomologyOrientation g O) z = 1 := by
    let x := z.proj
    let e : T x ≃L[ℝ] V := VectorBundle.continuousLinearEquivAt ℝ V T x
    let b₀ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let b := b₀.map e.symm.toLinearEquiv
    let C := localHomologyChartEquiv (chartAt V x) x (mem_chart_source V x) n
    let s := homologicalOrientationChartSign O (chartAt V x) x (mem_chart_source V x)
    let a := (tangentCohomologyOrientation g O).fiberClass x
    let L := tangentLocalHomologyEquiv (n := n) x
    -- The same native fiber simplex maps to the positive base chart simplex.
    have hcycle : C (L (realOrientationCycle b b.orientation)) =
        euclideanLocalOrientationCycle n (chartAt V x x) := by
      rw [tangentLocalHomologyEquiv_chartAt x x (mem_chart_source V x)]
      let f : C(T x, V) := ⟨e, e.continuous⟩
      let t : C(V, V) := ⟨fun v ↦ chartAt V x x + v, continuous_const.add continuous_id⟩
      have hf : Set.MapsTo f {v : T x | v ≠ 0} {v : V | v ≠ 0} :=
        fun _ hv heq ↦ hv (e.injective (heq.trans e.map_zero.symm))
      have ht : Set.MapsTo t {v : V | v ≠ 0} ({chartAt V x x}ᶜ : Set V) :=
        fun _ hv heq ↦ hv (add_left_cancel (heq.trans (add_zero _).symm))
      have hm : relativeSingularHomologyMap ℤ (t.comp f) (ht.comp hf) n =
          relativeSingularHomologyMap ℤ f hf n ≫ relativeSingularHomologyMap ℤ t ht n := by
        dsimp only [relativeSingularHomologyMap]
        rw [← HomologicalComplex.homologyMap_comp, relativeSingularChainsMap_comp]
      change relativeSingularHomologyMap ℤ (t.comp f) (ht.comp hf) n
        (realOrientationCycle b b.orientation) = _
      rw [hm, ModuleCat.comp_apply, realOrientationCycle_map_basis]
      have hb : b.map e.toLinearEquiv = b₀ := by
        apply Module.Basis.eq_of_apply_eq
        intro i
        exact e.apply_symm_apply (b₀ i)
      rw [hb]
      rfl
    -- The normalization of the fiber class therefore makes the product of signs one.
    have hgen : L.symm (O.localGenerator x 1) = s • realOrientationCycle b b.orientation := by
      apply L.injective
      apply C.injective
      rw [L.apply_symm_apply, map_zsmul, map_zsmul, hcycle]
      exact localHomologyChartEquiv_localGenerator O (chartAt V x) x (mem_chart_source V x)
    have heval := tangentCohomologyOrientation_evaluation g O x
    change (((TopCat.of (T x)).singularHomology₀ε (singularCoefficient ℤ))
      (relativeSingularCapProduct ℤ {v : T x | v ≠ 0} n 0 a
        (L.symm (O.localGenerator x 1)))).down = 1 at heval
    rw [hgen, map_zsmul, map_zsmul] at heval
    change s * realOrientationEvaluation b b.orientation a = 1 at heval
    exact heval
  -- Identify the actual native grouped-to-interleaved coordinate map and its permutation.
  have hcoord : ∃ σ : Equiv.Perm (Fin (n + n)),
      (σ.sign : ℤ) = (-1 : ℤ) ^ (n * (n - 1) / 2) ∧
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := n)).trans
        (tangentModelCoordinateEquiv n) =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (σ.trans (finCongr (by omega : n + n = 2 * n)))).toContinuousLinearEquiv := by
    let p : (Fin n ⊕ Fin n) ≃ (Fin n × Fin 2) :=
      { toFun := Sum.elim (fun i ↦ (i, 0)) (fun i ↦ (i, 1))
        invFun := fun p ↦ if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
        left_inv := by
          intro i
          cases i <;> simp
        right_inv := by
          rintro ⟨i, j⟩
          fin_cases j <;> simp }
    let σ : Equiv.Perm (Fin (n + n)) := finSumFinEquiv.symm.trans
      (p.trans (finProdFinEquiv.trans (finCongr (by omega : n * 2 = n + n))))
    have hleft (i : Fin n) : (σ (i.castAdd n)).val = 2 * i.val := by
      simp only [σ, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
      change 0 + 2 * i.val = 2 * i.val
      omega
    have hright (i : Fin n) : (σ (i.natAdd n)).val = 2 * i.val + 1 := by
      simp only [σ, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
      change 1 + 2 * i.val = 2 * i.val + 1
      omega
    refine ⟨σ, sign_of_interleaved_coordinates n σ hleft hright, ?_⟩
    apply ContinuousLinearEquiv.ext
    funext v
    change (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (p.trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))))
      ((EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin n) (κ := Fin n)).symm
        ((EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin n) (κ := Fin n))
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm v))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨σ, hsign, hcoord⟩ := hcoord
  let W := EuclideanSpace ℝ (Fin (n + n))
  let W' := EuclideanSpace ℝ (Fin (2 * n))
  let G := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := n)).symm
  let I := tangentModelCoordinateEquiv n
  let L : W ≃L[ℝ] W' := G.symm.trans I
  let cg := @chartAt W _ TM _ (bundleTotalEuclideanChartedSpace n n T) z
  let ci := @chartAt W' _ TM _ (tangentBundleEuclideanChartedSpace (n := n) (M := M)) z
  let cp := @chartAt (V × V) _ TM _ (tangentBundleFullChartedSpace V M) z
  let : T2Space TM := (tangentBundle_topology V M).1
  have hcg : z ∈ cg.source := @mem_chart_source W TM _ _
    (bundleTotalEuclideanChartedSpace n n T) z
  have hci : z ∈ ci.source := @mem_chart_source W' TM _ _
    (tangentBundleEuclideanChartedSpace (n := n) (M := M)) z
  have hfun (u : TM) : ci u = L (cg u) := by
    change I (cp u) = I (G.symm (G (cp u)))
    rw [G.symm_apply_apply]
  have hder : HasFDerivAt (fun w : W ↦ ci (cg.symm w))
      L.toContinuousLinearMap (cg z) := by
    have heq : (fun w : W ↦ ci (cg.symm w)) =ᶠ[𝓝 (cg z)] L := by
      filter_upwards [cg.open_target.mem_nhds (cg.map_source hcg)] with w hw
      rw [hfun, cg.right_inv hw]
    exact L.toContinuousLinearMap.hasFDerivAt.congr_of_eventuallyEq heq
  let Cg := localHomologyChartEquiv cg z hcg (n + n)
  let Ci (k : ℕ) := localHomologyChartEquiv ci z hci k
  let Z := (bundleHomologicalOrientation n T O
    (tangentCohomologyOrientation g O)).localGenerator z 1
  have hgrouped : Z = Cg.symm (euclideanLocalOrientationCycle (n + n) (cg z)) := by
    apply Cg.injective
    rw [Cg.apply_symm_apply]
    have h := bundleHomologicalOrientation_chart n T O (tangentCohomologyOrientation g O) z
    rw [hcoeff, one_smul] at h
    exact h
  let b := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  let l : C(W, W') := ⟨L, L.continuous⟩
  have hl : Set.MapsTo l {v : W | v ≠ 0} {v : W' | v ≠ 0} :=
    fun _ hv heq ↦ hv (L.injective (heq.trans L.map_zero.symm))
  let t : C(W', W') := ⟨fun w ↦ ci z + w, continuous_const.add continuous_id⟩
  have ht : Set.MapsTo t {v : W' | v ≠ 0} ({ci z}ᶜ : Set W') :=
    fun _ hv heq ↦ hv (add_left_cancel (heq.trans (add_zero _).symm))
  have htrans : Ci (n + n) Z = relativeSingularHomologyMap ℤ t ht (n + n)
      (relativeSingularHomologyMap ℤ l hl (n + n) (realOrientationCycle b b.orientation)) := by
    rw [hgrouped]
    have h := localHomologyChartEquiv_transition_derivative cg ci z hcg hci L hder (n + n)
    exact congrArg (fun f ↦ f (realOrientationCycle b b.orientation)) h
  -- Homology degree transport is explicit and commutes with these same chart and pair maps.
  have hdegreeMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
      (i j : ℕ) (h : i = j) (v : relativeSingularHomology ℤ A i) :
      (eqToIso (congrArg (relativeSingularHomology ℤ B) h)).hom
        (relativeSingularHomologyMap ℤ f hf i v) =
      relativeSingularHomologyMap ℤ f hf j
        ((eqToIso (congrArg (relativeSingularHomology ℤ A) h)).hom v) := by
    subst j
    rfl
  have hdegreeChart (i j : ℕ) (h : i = j)
      (v : relativeSingularHomology ℤ ({z}ᶜ : Set TM) i) :
      (eqToIso (congrArg (relativeSingularHomology ℤ ({ci z}ᶜ : Set W')) h)).hom (Ci i v) =
        Ci j ((eqToIso (congrArg (relativeSingularHomology ℤ ({z}ᶜ : Set TM)) h)).hom v) := by
    subst j
    rfl
  have hcycleCast (k m : ℕ) (h : k = m) (τ : Equiv.Perm (Fin k)) :
      let e := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (τ.trans (finCongr h))).toContinuousLinearEquiv
      let bk := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      let bm := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (eqToIso (congrArg (relativeSingularHomology ℤ
        {v : EuclideanSpace ℝ (Fin m) | v ≠ 0}) h)).hom
        (relativeSingularHomologyMap ℤ
          (⟨e, e.continuous⟩ : C(EuclideanSpace ℝ (Fin k), EuclideanSpace ℝ (Fin m)))
          (A := {v : EuclideanSpace ℝ (Fin k) | v ≠ 0})
          (B := {v : EuclideanSpace ℝ (Fin m) | v ≠ 0})
          (fun _ hv heq ↦ hv (e.injective (heq.trans e.map_zero.symm))) k
          (realOrientationCycle bk bk.orientation)) =
        (τ.sign : ℤ) • realOrientationCycle bm bm.orientation := by
    subst m
    simpa only [finCongr_refl, Equiv.trans_refl, eqToIso_refl, Iso.refl_hom,
      ModuleCat.id_apply] using
      realOrientationCycle_piLpCongrLeft k τ
  have hdim : n + n = 2 * n := by omega
  have hcycle : (eqToIso (congrArg (relativeSingularHomology ℤ
      {v : W' | v ≠ 0}) hdim)).hom
      (relativeSingularHomologyMap ℤ l hl (n + n) (realOrientationCycle b b.orientation)) =
      (σ.sign : ℤ) • realOrientationCycle
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.orientation := by
    have h := hcycleCast (n + n) (2 * n) hdim σ
    dsimp only at h
    have hL : L = (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (σ.trans (finCongr hdim))).toContinuousLinearEquiv := hcoord
    simpa only [← hL] using h
  have hfinal := congrArg (fun v ↦
    (eqToIso (congrArg (relativeSingularHomology ℤ ({ci z}ᶜ : Set W')) hdim)).hom v) htrans
  rw [hdegreeChart (n + n) (2 * n) hdim Z,
    hdegreeMap t ht (n + n) (2 * n) hdim _, hcycle, map_zsmul, hsign] at hfinal
  apply (Ci (2 * n)).injective
  rw [map_zsmul]
  have hcanonical : Ci (2 * n)
      ((tangentHomologicalOrientation (n := n) (M := M)).localGenerator z 1) =
        euclideanLocalOrientationCycle (2 * n) (ci z) :=
    tangentHomologicalOrientation_chart z z hci
  rw [hcanonical]
  exact hfinal

end AtiyahSinger

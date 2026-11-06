/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanLocalHomology
public import AtiyahSinger.Topology.RealOrientationCycle
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The actual affine simplex and local homology suspension

Public module ID: M2118.

The sum coordinate and differences from the first coordinate place the original
simplex between opposite half axes. Its zeroth face is the section at height one
of the lower-dimensional original simplex; every remaining face is killed in the
lower-half-axis relative quotient. The connecting map is evaluated on these same
chains, using the original categorical homology comparison.

This implements the simplex normalization in Milnor--Stasheff, section 9, and the
relative suspension calculation of Hatcher, sections 2.1 and 3.3.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open CategoryTheory Convexity Limits Opposite
open scoped Simplicial
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The connecting morphism sends a represented cycle to the represented lifted boundary. -/
theorem homologyConnecting_cycleClass (R : Type) [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
    (n : ℕ) (c₃ : (S.X₃.sc (n + 1)).moduleCatLeftHomologyData.K)
    (c₂ : S.X₂.X (n + 1)) (hc₂ : S.g.f (n + 1) c₂ = c₃.val)
    (c₁ : (S.X₁.sc n).moduleCatLeftHomologyData.K)
    (hc₁ : S.f.f n c₁.val = S.X₂.d (n + 1) n c₂) :
    hS.δ (n + 1) n rfl
      ((S.X₃.sc (n + 1)).moduleCatHomologyIso.inv
        ((S.X₃.sc (n + 1)).moduleCatToCycles.range.mkQ c₃)) =
      (S.X₁.sc n).moduleCatHomologyIso.inv ((S.X₁.sc n).moduleCatToCycles.range.mkQ c₁) := by
  -- Identify the original module quotient class with the same native cycles representative.
  have hclass (C : ChainComplex (ModuleCat.{u} R) ℕ) (i j : ℕ)
      (hj : (ComplexShape.down ℕ).next i = j)
      (c : (C.sc i).moduleCatLeftHomologyData.K)
      (hc : (forget₂ (ModuleCat.{u} R) Ab).map (C.d i j) c.val = 0) :
      C.homologyπ i (C.cyclesMk c.val j hj hc) =
        (C.sc i).moduleCatHomologyIso.inv ((C.sc i).moduleCatToCycles.range.mkQ c) := by
    have heq : C.cyclesMk c.val j hj hc = (C.sc i).moduleCatCyclesIso.inv c := by
      apply (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
      have hleft := HomologicalComplex.i_cyclesMk C c.val j hj hc
      have hright := congrArg (fun f ↦ f c) (C.sc i).moduleCatCyclesIso_inv_iCycles
      exact hleft.trans hright.symm
    rw [heq]
    exact congrArg (fun f ↦ f c) (C.sc i).moduleCatCyclesIso_inv_π
  have hz : (forget₂ (ModuleCat.{u} R) Ab).map (S.X₃.d (n + 1) n) c₃.val = 0 := by
    have h : S.X₃.dFrom (n + 1) c₃.val = 0 := c₃.property
    rw [HomologicalComplex.dFrom_eq (r := rfl), ModuleCat.comp_apply] at h
    apply (ModuleCat.mono_iff_injective (S.X₃.xNextIso rfl).inv).mp inferInstance
    exact h.trans (map_zero _).symm
  have h := hS.δ_apply (n + 1) n rfl c₃.val hz c₂ hc₂ c₁.val hc₁
    ((ComplexShape.down ℕ).next n) rfl
  change hS.δ (n + 1) n rfl (S.X₃.homologyπ (n + 1) _) = S.X₁.homologyπ n _ at h
  rw [hclass S.X₃ (n + 1) n _ c₃, hclass S.X₁ n _ _ c₁] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Chain maps preserve the actual homology class of each specified cycle. -/
theorem homologyMap_cycleClass (R : Type) [CommRing R] {shape : ComplexShape ℕ}
    (C D : HomologicalComplex (ModuleCat.{u} R) shape) (F : C ⟶ D) (n : ℕ)
    (a : (C.sc n).moduleCatLeftHomologyData.K)
    (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
    HomologicalComplex.homologyMap F n
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
      (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
  let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) shape n).map F
  let G := ShortComplex.leftHomologyMapData S
    (C.sc n).moduleCatLeftHomologyData (D.sc n).moduleCatLeftHomologyData
  have hcycles : G.φK a = b := by
    apply Subtype.ext
    exact (congrArg (fun f ↦ f a) G.commi).trans h
  have hquot := congrArg (fun f ↦ f a) G.commπ
  change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
    (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
  rw [hcycles] at hquot
  have hmap := G.homologyMap_eq
  change HomologicalComplex.homologyMap F n = _ at hmap
  rw [hmap]
  change (D.sc n).moduleCatHomologyIso.inv
    (G.φH ((C.sc n).moduleCatHomologyIso.hom
      ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))) = _
  have hcancel : (C.sc n).moduleCatHomologyIso.hom
      ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
        (C.sc n).moduleCatToCycles.range.mkQ a :=
    congrArg (fun f ↦ f ((C.sc n).moduleCatToCycles.range.mkQ a))
      (C.sc n).moduleCatHomologyIso.inv_hom_id
  rw [hcancel, hquot]


/-- The unlifted sum-and-difference coordinate equivalence used in arbitrary universes. -/
def simplexCoordinateSplittingBase (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin n → ℝ) where
  toFun x := (∑ i, x i, fun i ↦ x i.succ - x 0)
  invFun z := Fin.cases ((z.1 - ∑ i, z.2 i) / (n + 1))
    (fun i ↦ z.2 i + (z.1 - ∑ i, z.2 i) / (n + 1))
  left_inv x := by
    have hsum : (∑ i : Fin (n + 1), x i) -
        ∑ i : Fin n, (x i.succ - x 0) = (n + 1 : ℝ) * x 0 := by
      rw [Fin.sum_univ_succ, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.cases_zero, hsum] using mul_div_cancel_left₀ (x 0) hn
    · simp only [Fin.cases_succ, hsum, mul_div_cancel_left₀ _ hn]
      ring
  right_inv z := by
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    apply Prod.ext
    · simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    · funext i
      simp
  map_add' x y := by
    apply Prod.ext
    · simp [Finset.sum_add_distrib]
    · funext i
      simp
      ring
  map_smul' a x := by
    apply Prod.ext
    · simp [Finset.mul_sum]
    · funext i
      simp [mul_sub]

/-- The sum coordinate and differences from the first coordinate split the original simplex. -/
def simplexCoordinateSplitting (n : ℕ) :
    ULift.{u} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] ℝ × ULift.{u} (Fin n → ℝ) :=
  ULift.moduleEquiv.trans ((simplexCoordinateSplittingBase n).trans
    ((LinearEquiv.refl ℝ ℝ).prodCongr ULift.moduleEquiv.symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual local suspension sends the original positive simplex to the smaller simplex. -/
theorem realOrientationCycle_suspension (n : ℕ) :
    let b := (Pi.basisFun ℝ (Fin (n + 1))).map
      (ULift.moduleEquiv : ULift.{u} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] _).symm
    let c := (Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).symm
    let e := (simplexCoordinateSplitting.{u} n).toContinuousLinearEquiv
    (euclideanLocalSuspensionIso ℤ (ULift.{u} (Fin n → ℝ)) n).hom
      (relativeSingularHomologyMap ℤ (⟨e, e.continuous⟩ : C(_, _))
        (A := {x | x ≠ 0}) (B := {y | y ≠ 0})
        (fun _ hx h ↦ hx (e.injective (h.trans e.map_zero.symm))) (n + 1)
        (realOrientationCycle b b.orientation)) = realOrientationCycle c c.orientation := by
  classical
  -- Compute the same simplex coordinates once, then use its distinguished and omitted faces.
  have hcoordinates (n : ℕ)
      (t : StdSimplex ℝ (Fin (n + 1))) (i : Fin n) :
      (((TopCat.of (ULift.{u} (Fin n → ℝ))).toSSetObjEquiv (op ⦋n⦌)
        (realOrientationSimplex ((Pi.basisFun ℝ (Fin n)).map ULift.moduleEquiv.symm))) t).down i =
        t.weights i.succ - t.weights 0 := by
    simp [realOrientationSimplex, Module.Basis.map_apply, Pi.basisFun_apply, Pi.single_apply,
      ← ULift.moduleEquiv_apply (R := ℝ), map_sum]
  have hsplitSimplex (n : ℕ)
      (t : StdSimplex ℝ (Fin (n + 2))) :
      simplexCoordinateSplitting n
        (((TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))).toSSetObjEquiv (op ⦋n + 1⦌)
          (realOrientationSimplex ((Pi.basisFun ℝ (Fin (n + 1))).map
          ULift.moduleEquiv.symm))) t) =
        (∑ i : Fin (n + 1), (t.weights i.succ - t.weights 0),
          ULift.up (fun i : Fin n ↦ t.weights i.succ.succ - t.weights 1)) := by
    apply Prod.ext
    · change (∑ i : Fin (n + 1), _ : ℝ) = _
      apply Finset.sum_congr rfl
      intro i _
      exact hcoordinates (n + 1) t i
    · apply ULift.ext
      funext i
      change _ - _ = _
      simp only [LinearEquiv.coe_coe, ULift.moduleEquiv_apply]
      rw [hcoordinates (n + 1) t i.succ,
        hcoordinates (n + 1) t 0]
      simp only [Fin.succ_zero_eq_one]
      ring
  have hsplitFaceZero (n : ℕ)
      (t : StdSimplex ℝ (Fin (n + 1))) :
      simplexCoordinateSplitting n
        (((TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))).toSSetObjEquiv (op ⦋n + 1⦌)
          (realOrientationSimplex ((Pi.basisFun ℝ (Fin (n + 1))).map
            ULift.moduleEquiv.symm))) (t.map Fin.succ)) =
        (1, ((TopCat.of (ULift.{u} (Fin n → ℝ))).toSSetObjEquiv (op ⦋n⦌)
          (realOrientationSimplex ((Pi.basisFun ℝ (Fin n)).map ULift.moduleEquiv.symm))) t) := by
    have hw (i : Fin (n + 1)) : (t.map Fin.succ).weights i.succ = t.weights i :=
      Finsupp.mapDomain_apply_of_injective (Fin.succ_injective _) t.weights i
    have hzero : (t.map Fin.succ).weights 0 = 0 :=
      Finsupp.mapDomain_of_notMem_range t.weights 0
        (by rintro ⟨i, hi⟩; exact Fin.succ_ne_zero i hi)
    have hw0 : (t.map Fin.succ).weights 1 = t.weights 0 := by
      simpa only [Fin.succ_zero_eq_one] using hw 0
    rw [hsplitSimplex]
    apply Prod.ext
    · simp only [hzero, hw, sub_zero]
      exact t.total_of_fintype
    · apply ULift.ext
      funext i
      change (t.map Fin.succ).weights i.succ.succ - (t.map Fin.succ).weights 1 = _
      rw [hw, hw0]
      exact (hcoordinates n t i).symm
  have hsplitOtherFaces (n : ℕ)
      (t : StdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 1)) (hi : t.weights i.succ = 0) :
      (simplexCoordinateSplitting n
        (((TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))).toSSetObjEquiv (op ⦋n + 1⦌)
          (realOrientationSimplex ((Pi.basisFun ℝ (Fin (n + 1))).map
            ULift.moduleEquiv.symm))) t)).1 < 0 ∨
      (simplexCoordinateSplitting n
        (((TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))).toSSetObjEquiv (op ⦋n + 1⦌)
          (realOrientationSimplex ((Pi.basisFun ℝ (Fin (n + 1))).map
            ULift.moduleEquiv.symm))) t)).2 ≠ 0 := by
    rw [hsplitSimplex]
    by_cases hz : (fun j : Fin n ↦ t.weights j.succ.succ - t.weights 1) = 0
    · left
      have hsame (j : Fin (n + 1)) : t.weights j.succ = t.weights 1 := by
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · simp only [Fin.succ_zero_eq_one]
        · exact sub_eq_zero.mp (congrFun hz k)
      have hzero : t.weights 1 = 0 := (hsame i).symm.trans hi
      have hweights (j : Fin (n + 1)) : t.weights j.succ = 0 := (hsame j).trans hzero
      have hone : t.weights 0 = 1 := by
        have h := t.total_of_fintype
        rw [Fin.sum_univ_succ] at h
        simpa only [hweights, Finset.sum_const_zero, add_zero] using h
      change (∑ j : Fin (n + 1), (t.weights j.succ - t.weights 0)) < 0
      simp only [hweights, hone, zero_sub, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · exact Or.inr (fun h ↦ hz (congrArg ULift.down h))
  let E := ULift.{u} (Fin n → ℝ)
  let V := ULift.{u} (Fin (n + 1) → ℝ)
  let W := ℝ × E
  let b := (Pi.basisFun ℝ (Fin (n + 1))).map (ULift.moduleEquiv : V ≃ₗ[ℝ] _).symm
  let c := (Pi.basisFun ℝ (Fin n)).map (ULift.moduleEquiv : E ≃ₗ[ℝ] _).symm
  let e := (simplexCoordinateSplitting.{u} n).toContinuousLinearEquiv
  let f : C(V, W) := ⟨e, e.continuous⟩
  have hf : Set.MapsTo f (Set.ofPred (fun x : V ↦ x ≠ 0))
      (Set.ofPred (fun y : W ↦ y ≠ 0)) :=
    fun x hx h ↦ hx (e.injective (h.trans e.map_zero.symm))
  change (euclideanLocalSuspensionIso ℤ E n).hom
    (relativeSingularHomologyMap ℤ f hf (n + 1) (realOrientationCycle b b.orientation)) =
      realOrientationCycle c c.orientation
  let U := euclideanPuncturedHalfSpace E 1
  let A := euclideanPuncturedHalfSpace E (-1)
  let P := {z : W // z ≠ 0}
  let AU : Set U := (Subtype.val : U → W) ⁻¹' A
  let AP : Set P := (Subtype.val : P → W) ⁻¹' A
  let j := euclideanLocalSuspensionInclusion E
  let g : C(E, U) := ⟨fun y ↦ ⟨(1, y), Or.inl (by norm_num)⟩, by fun_prop⟩
  have hg : Set.MapsTo g (Set.ofPred (fun y : E ↦ y ≠ 0)) AU := fun _ hy ↦ Or.inr hy
  let T := euclideanLocalSuspensionTriple ℤ E
  let J := relativeSingularChainsMap ℤ j (A := AU) (B := AP) (fun _ hx ↦ hx)
  let G := relativeSingularChainsMap ℤ g hg
  let F := relativeSingularChainsMap ℤ f hf
  -- All representatives are obtained by the actual maps on the original cycle kernels.
  let mapCycle {C D : ChainComplex (ModuleCat.{u} ℤ) ℕ} (L : C ⟶ D) (k : ℕ)
      (z : (C.sc k).moduleCatLeftHomologyData.K) :
      (D.sc k).moduleCatLeftHomologyData.K :=
    ⟨L.f k z.val, by
      change D.dFrom k (L.f k z.val) = 0
      have h := congrArg (fun a ↦ a z.val) (L.comm_from k)
      change D.dFrom k (L.f k z.val) = L.next k (C.dFrom k z.val) at h
      rw [h, show C.dFrom k z.val = 0 from z.property, map_zero]⟩
  let z₃₀ : (relativeSingularChains ℤ (Set.ofPred (fun x : V ↦ x ≠ 0))).sc (n + 1)
      |>.moduleCatLeftHomologyData.K :=
    ⟨realOrientationRelativeChain b b.orientation,
      realOrientationRelativeChain_mem_cycles b b.orientation⟩
  let z₀ : (relativeSingularChains ℤ (Set.ofPred (fun x : E ↦ x ≠ 0))).sc n
      |>.moduleCatLeftHomologyData.K :=
    ⟨realOrientationRelativeChain c c.orientation,
      realOrientationRelativeChain_mem_cycles c c.orientation⟩
  let z₃ := mapCycle F (n + 1) z₃₀
  let zU := mapCycle G n z₀
  let z₁ := mapCycle J n zU
  let S := TopCat.toSSet.obj (TopCat.of W)
  let σ := (TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋n + 1⦌)
    (realOrientationSimplex b)
  let πA := relativeSingularChainsProjection ℤ A
  let z₂ := πA.f (n + 1) (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1))
  have hprojection {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (a : C(X, Y)) {B : Set X} {D : Set Y} (ha : Set.MapsTo a B D) :
      relativeSingularChainsProjection ℤ B ≫ relativeSingularChainsMap ℤ a ha =
        (singularChainsFunctor ℤ).map (TopCat.ofHom a) ≫
          relativeSingularChainsProjection ℤ D := by
    simp [relativeSingularChainsProjection, relativeSingularChainsMap, cokernel.map]
  have hgen {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (a : C(X, Y)) (k : ℕ)
      (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋k⦌)) :
      ((singularChainsFunctor ℤ).map (TopCat.ofHom a)).f k
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient ℤ) τ (ULift.up 1)) =
        (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex (R := singularCoefficient ℤ)
          ((TopCat.toSSet.map (TopCat.ofHom a)).app (op ⦋k⦌) τ) (ULift.up 1) := by
    exact congrArg (fun h ↦ h (ULift.up 1))
      (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (TopCat.ofHom a))
        (singularCoefficient ℤ) τ)
  have hz₃ : T.g.f (n + 1) z₂ = z₃.val := by
    let πP := relativeSingularChainsProjection ℤ (Set.ofPred (fun z : W ↦ z ≠ 0))
    have hT : πA ≫ T.g = πP := by
      simp [πA, πP, T, euclideanLocalSuspensionTriple, relativeSingularTripleSequence,
        relativeSingularChainsMap, A, cokernel.map]
      rfl
    have hmap := congrArg (fun a ↦ a.f (n + 1)
      ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
        (R := singularCoefficient ℤ) (realOrientationSimplex b) (ULift.up 1)))
      (hprojection f hf)
    change F.f (n + 1) ((relativeSingularChainsProjection ℤ _).f (n + 1) _) =
      πP.f (n + 1) (((singularChainsFunctor ℤ).map (TopCat.ofHom f)).f (n + 1) _) at hmap
    rw [hgen] at hmap
    have hraw : z₃.val = πP.f (n + 1)
        (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1)) := by
      simpa only [z₃, mapCycle, z₃₀, realOrientationRelativeChain, ite_true] using hmap
    rw [hraw]
    exact congrArg (fun a ↦ a.f (n + 1)
      (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1))) hT
  -- The zeroth face is the same smaller simplex at height one.
  have hface₀ : S.δ 0 σ =
      (TopCat.toSSet.map (TopCat.ofHom
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, W)).comp g))).app (op ⦋n⦌)
          (realOrientationSimplex c) := by
    apply ((TopCat.of W).toSSetObjEquiv (op ⦋n⦌)).injective
    apply ContinuousMap.ext
    intro t
    change simplexCoordinateSplitting n
      (((TopCat.of V).toSSetObjEquiv (op ⦋n + 1⦌)
        (realOrientationSimplex b)) (t.map (0 : Fin (n + 2)).succAbove)) =
        (1, ((TopCat.of E).toSSetObjEquiv (op ⦋n⦌) (realOrientationSimplex c)) t)
    simpa only [Fin.succAbove_zero] using hsplitFaceZero n t
  -- Every other face lies in the lower half-axis complement and is killed there.
  have hface (i : Fin (n + 1)) :
      S.ιChainComplex (R := singularCoefficient ℤ) (S.δ i.succ σ) ≫ πA.f n = 0 := by
    let face := (TopCat.of W).toSSetObjEquiv (op ⦋n⦌) (S.δ i.succ σ)
    have hmem (t : StdSimplex ℝ (Fin (n + 1))) : face t ∈ A := by
      have hzero : (t.map i.succ.succAbove).weights i.succ = 0 :=
        Finsupp.mapDomain_of_notMem_range t.weights i.succ
          (by rintro ⟨j, hj⟩; exact i.succ.succAbove_ne j hj)
      rcases hsplitOtherFaces n
          (t.map i.succ.succAbove) i hzero with h | h
      · have hnegative : (face t).1 < 0 := h
        exact Or.inl (by linarith)
      · exact Or.inr h
    let τ := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm
      (⟨fun t ↦ ⟨face t, hmem t⟩, face.continuous.subtype_mk _⟩ :
        C(StdSimplex ℝ (Fin (n + 1)), A))
    let a : C(A, W) := ⟨Subtype.val, continuous_subtype_val⟩
    have hτ : (TopCat.toSSet.map (TopCat.ofHom a)).app (op ⦋n⦌) τ = S.δ i.succ σ := rfl
    rw [← hτ, ← SSet.ι_chainComplexMap_f]
    erw [Category.assoc]
    have hz := congrArg (fun h ↦ h.f n) (cokernel.condition (singularSubspaceChains ℤ A))
    change (singularSubspaceChains ℤ A).f n ≫ πA.f n = 0 at hz
    change _ ≫ ((singularSubspaceChains ℤ A).f n ≫ πA.f n) = 0
    erw [hz, comp_zero]
  have hd : T.f.f n z₁.val = T.X₂.d (n + 1) n z₂ := by
    let a : C(E, W) := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, W)).comp g
    have ha : Set.MapsTo a (Set.ofPred (fun y : E ↦ y ≠ 0)) A := fun _ hy ↦ Or.inr hy
    have hcomp : G ≫ J ≫ T.f = relativeSingularChainsMap ℤ a ha := by
      dsimp only [G, J, T, euclideanLocalSuspensionTriple, relativeSingularTripleSequence]
      rw [← relativeSingularChainsMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    have hmap := congrArg (fun l ↦ l.f n
      ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (R := singularCoefficient ℤ) (realOrientationSimplex c) (ULift.up 1)))
      (hprojection a ha)
    change (relativeSingularChainsMap ℤ a ha).f n
      ((relativeSingularChainsProjection ℤ _).f n _) =
        πA.f n (((singularChainsFunctor ℤ).map (TopCat.ofHom a)).f n _) at hmap
    rw [hgen, ← hface₀] at hmap
    have hleft : T.f.f n z₁.val =
        πA.f n (S.ιChainComplex (R := singularCoefficient ℤ) (S.δ 0 σ) (ULift.up 1)) := by
      change (G ≫ J ≫ T.f).f n (realOrientationRelativeChain c c.orientation) = _
      rw [hcomp]
      dsimp only [realOrientationRelativeChain]
      simp only [ite_true]
      exact hmap
    have hboundary : S.ιChainComplex (R := singularCoefficient ℤ) σ ≫
        πA.f (n + 1) ≫ T.X₂.d (n + 1) n =
        S.ιChainComplex (R := singularCoefficient ℤ) (S.δ 0 σ) ≫ πA.f n := by
      change S.ιChainComplex (R := singularCoefficient ℤ) σ ≫
        πA.f (n + 1) ≫ (relativeSingularChains ℤ A).d (n + 1) n = _
      erw [πA.comm, ← Category.assoc, SSet.ιChainComplex_d,
        Preadditive.sum_comp]
      simp only [Fin.sum_univ_succ, Preadditive.zsmul_comp, Fin.val_zero,
        pow_zero, one_smul, hface, smul_zero, Finset.sum_const_zero, add_zero]
    exact hleft.trans (congrArg (fun a ↦ a (ULift.up 1)) hboundary).symm
  have hδ := homologyConnecting_cycleClass ℤ T
    (shortExact_euclideanLocalSuspensionTriple ℤ E) n z₃ z₂ hz₃ z₁ hd
  let HJ := relativeSingularHomologyMap ℤ j (A := AU) (B := AP) (fun _ hx ↦ hx) n
  let p := euclideanLocalSuspensionProjection E
  let hp := euclideanLocalSuspensionProjection_mapsTo E
  let HP := relativeSingularHomologyMap ℤ p hp n
  let : IsIso HJ := isIso_euclideanLocalSuspensionExcision ℤ E n
  have hF := homologyMap_cycleClass ℤ _ _ F (n + 1) z₃₀ z₃ rfl
  have hJ := homologyMap_cycleClass ℤ _ _ J n zU z₁ rfl
  have hG := homologyMap_cycleClass ℤ _ _ G n z₀ zU rfl
  change HP (inv HJ
    ((shortExact_euclideanLocalSuspensionTriple ℤ E).δ (n + 1) n rfl
      (relativeSingularHomologyMap ℤ f hf (n + 1) (realOrientationCycle b b.orientation)))) = _
  change relativeSingularHomologyMap ℤ f hf (n + 1) (realOrientationCycle b b.orientation) = _ at hF
  rw [hF]
  erw [hδ, ← hJ]
  have hcancel : inv HJ (HJ (relativeSingularCycleClass ℤ AU n zU)) =
      relativeSingularCycleClass ℤ AU n zU :=
    congrArg (fun l ↦ l (relativeSingularCycleClass ℤ AU n zU)) (IsIso.hom_inv_id HJ)
  change HP (inv HJ (HJ (relativeSingularCycleClass ℤ AU n zU))) = _
  rw [hcancel]
  erw [← hG]
  change (HomologicalComplex.homologyMap G n ≫
    HomologicalComplex.homologyMap (relativeSingularChainsMap ℤ p hp) n)
      (realOrientationCycle c c.orientation) = _
  rw [← HomologicalComplex.homologyMap_comp]
  have hidentity : G ≫ relativeSingularChainsMap ℤ p hp =
      𝟙 (relativeSingularChains ℤ (Set.ofPred (fun y : E ↦ y ≠ 0))) := by
    rw [← relativeSingularChainsMap_comp]
    have heq : p.comp g = ContinuousMap.id E := rfl
    simp [heq, relativeSingularChainsMap]
  rw [hidentity, HomologicalComplex.homologyMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Transporting the basis transports the same positive relative simplex class. -/
theorem realOrientationCycle_map_basis {r : ℕ} {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : Module.Basis (Fin r) ℝ V) (e : V ≃L[ℝ] W) :
    relativeSingularHomologyMap ℤ (⟨e, e.continuous⟩ : C(V, W))
      (A := (Set.ofPred (fun v : V ↦ v ≠ 0))) (B := (Set.ofPred (fun w : W ↦ w ≠ 0)))
      (fun _ hv h ↦ hv (e.injective (h.trans (map_zero e).symm))) r
      (realOrientationCycle b b.orientation) =
        realOrientationCycle (b.map e.toLinearEquiv) (b.map e.toLinearEquiv).orientation := by
  let f : C(V, W) := ⟨e, e.continuous⟩
  let A : Set V := {v | v ≠ 0}
  let B : Set W := {w | w ≠ 0}
  let hf : Set.MapsTo f A B := fun _ hv h ↦ hv (e.injective (h.trans (map_zero e).symm))
  let F := relativeSingularChainsMap ℤ f hf
  let b' := b.map e.toLinearEquiv
  change HomologicalComplex.homologyMap F r _ = _
  apply homologyMap_cycleClass ℤ (relativeSingularChains ℤ A)
    (relativeSingularChains ℤ B) F r
    ⟨realOrientationRelativeChain b b.orientation,
      realOrientationRelativeChain_mem_cycles b b.orientation⟩
    ⟨realOrientationRelativeChain b' b'.orientation,
      realOrientationRelativeChain_mem_cycles b' b'.orientation⟩
  have hsimplex : (TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋r⦌)
      (realOrientationSimplex b) = realOrientationSimplex b' := by
    apply ((TopCat.of W).toSSetObjEquiv (op ⦋r⦌)).injective
    apply ContinuousMap.ext
    intro t
    change e (∑ i : Fin r, (t.weights i.succ - t.weights 0) • b i) =
      ∑ i : Fin r, (t.weights i.succ - t.weights 0) • b' i
    simp [b', map_sum, map_smul]
  have hpair : relativeSingularChainsProjection ℤ A ≫ F =
      (singularChainsFunctor ℤ).map (TopCat.ofHom f) ≫
        relativeSingularChainsProjection ℤ B := by
    simp [F, relativeSingularChainsMap, relativeSingularChainsProjection]
  have hformula : (TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
      (R := singularCoefficient ℤ) (realOrientationSimplex b) ≫
      (relativeSingularChainsProjection ℤ A).f r ≫ F.f r =
      (TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
        (R := singularCoefficient ℤ) (realOrientationSimplex b') ≫
          (relativeSingularChainsProjection ℤ B).f r := by
    rw [show (relativeSingularChainsProjection ℤ A).f r ≫ F.f r =
      ((singularChainsFunctor ℤ).map (TopCat.ofHom f)).f r ≫
        (relativeSingularChainsProjection ℤ B).f r from congrArg (fun k ↦ k.f r) hpair]
    change _ ≫ (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
      (singularCoefficient ℤ)).f r ≫ _ = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f, hsimplex]
  have hvalue := congrArg (fun h ↦ h (ULift.up 1)) hformula
  change F.f r ((relativeSingularChainsProjection ℤ A).f r
    ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
      (R := singularCoefficient ℤ) (realOrientationSimplex b) (ULift.up 1))) =
      (relativeSingularChainsProjection ℤ B).f r
        ((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
          (R := singularCoefficient ℤ) (realOrientationSimplex b') (ULift.up 1)) at hvalue
  simpa only [realOrientationRelativeChain, ite_true] using hvalue


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same positive zero-dimensional simplex has augmentation one. -/
theorem realOrientationCycle_zero_augmentation
    (b : Module.Basis (Fin 0) ℝ (ULift.{u} (Fin 0 → ℝ))) :
    (euclideanLocalZeroIso.{u} ℤ).hom (realOrientationCycle b b.orientation) = ULift.up 1 := by
  let V := ULift.{u} (Fin 0 → ℝ)
  let A : Set V := {x | x ≠ 0}
  let S := TopCat.toSSet.obj (TopCat.of V)
  let C := (singularChainsFunctor ℤ).obj (TopCat.of V)
  let Q := relativeSingularChains ℤ A
  let π := relativeSingularChainsProjection ℤ A
  let σ := realOrientationSimplex b
  let c : (C.sc 0).moduleCatLeftHomologyData.K :=
    ⟨S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1), by
      change C.dFrom 0 _ = 0
      simp⟩
  let z : C.homology 0 :=
    (C.sc 0).moduleCatHomologyIso.inv ((C.sc 0).moduleCatLeftHomologyData.π c)
  have hmap : HomologicalComplex.homologyMap π 0 z = realOrientationCycle b b.orientation := by
    apply homologyMap_cycleClass ℤ C Q π 0 c
      ⟨realOrientationRelativeChain b b.orientation,
        realOrientationRelativeChain_mem_cycles b b.orientation⟩
    simp only [realOrientationRelativeChain, ite_true]
    rfl
  have hcancel : (euclideanLocalZeroIso.{u} ℤ).hom
      (HomologicalComplex.homologyMap π 0 z) =
      (TopCat.of V).singularHomology₀ε (singularCoefficient ℤ) z := by
    let : IsEmpty A := ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    let : IsIso π := isIso_relativeSingularChainsProjection_of_isEmpty ℤ A
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 0
    let e := H.mapIso (asIso π)
    change (TopCat.of V).singularHomology₀ε (singularCoefficient ℤ) (e.inv (e.hom z)) = _
    have hz : e.inv (e.hom z) = z := congrArg (fun f ↦ f z) e.hom_inv_id
    rw [hz]
  rw [← hmap, hcancel]
  let l := C.liftCycles (S.ιChainComplex (R := singularCoefficient ℤ) σ) 0
    (by simp) (by simp)
  have hcycles : l (ULift.up 1) = (C.sc 0).moduleCatCyclesIso.inv c := by
    apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
    have hleft := congrArg (fun f ↦ f (ULift.up 1))
      (C.liftCycles_i (S.ιChainComplex (R := singularCoefficient ℤ) σ) 0
        (by simp) (by simp))
    have hright := congrArg (fun f ↦ f c) (C.sc 0).moduleCatCyclesIso_inv_iCycles
    exact hleft.trans hright.symm
  have hclass : C.homologyπ 0 (l (ULift.up 1)) = z := by
    rw [hcycles]
    exact congrArg (fun f ↦ f c) (C.sc 0).moduleCatCyclesIso_inv_π
  have hε := congrArg (fun f ↦ f (ULift.up 1))
    (S.liftCycles_ιChainComplex_homologyπ_homology₀ε (singularCoefficient ℤ) σ)
  change (TopCat.of V).singularHomology₀ε (singularCoefficient ℤ)
    (C.homologyπ 0 (l (ULift.up 1))) = ULift.up 1 at hε
  rw [hclass] at hε
  exact hε


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original positive simplex is a primitive integral local homology generator. -/
theorem realOrientationCycle_ulift_pi_is_generator (n : ℕ) :
    let b := (Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).symm
    Function.Bijective (fun a : ℤ ↦ a • realOrientationCycle b b.orientation) := by
  have htransfer {M N : Type u} [AddCommGroup M] [AddCommGroup N]
      (f : M →+ N) (hf : Function.Injective f) (x : M)
      (hx : Function.Bijective (fun a : ℤ ↦ a • f x)) :
      Function.Bijective (fun a : ℤ ↦ a • x) := by
    constructor
    · intro a b h
      apply hx.injective
      simpa only [map_zsmul] using congrArg f h
    · intro y
      obtain ⟨a, ha⟩ := hx.surjective (f y)
      exact ⟨a, hf ((map_zsmul f a x).trans ha)⟩
  induction n with
  | zero =>
    let b := (Pi.basisFun ℝ (Fin 0)).map
      (ULift.moduleEquiv : ULift.{u} (Fin 0 → ℝ) ≃ₗ[ℝ] _).symm
    let e := euclideanLocalZeroIso.{u} ℤ
    have he : e.hom (realOrientationCycle b b.orientation) = ULift.up 1 :=
      realOrientationCycle_zero_augmentation b
    apply htransfer e.hom.hom.toAddMonoidHom
      ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance).injective
    change Function.Bijective (fun a : ℤ ↦ a • e.hom (realOrientationCycle b b.orientation))
    rw [he]
    constructor
    · intro a b h
      have h' := congrArg ULift.down h
      simpa using h'
    · intro y
      refine ⟨y.down, ?_⟩
      apply ULift.ext
      simp
  | succ n ih =>
    let E := ULift.{u} (Fin n → ℝ)
    let V := ULift.{u} (Fin (n + 1) → ℝ)
    let W := ℝ × E
    let b := (Pi.basisFun ℝ (Fin (n + 1))).map (ULift.moduleEquiv : V ≃ₗ[ℝ] _).symm
    let c := (Pi.basisFun ℝ (Fin n)).map (ULift.moduleEquiv : E ≃ₗ[ℝ] _).symm
    let e := (simplexCoordinateSplitting.{u} n).toContinuousLinearEquiv
    let f : C(V, W) := ⟨e, e.continuous⟩
    let g : C(W, V) := ⟨e.symm, e.symm.continuous⟩
    have hf : Set.MapsTo f (Set.ofPred (fun x : V ↦ x ≠ 0))
        (Set.ofPred (fun y : W ↦ y ≠ 0)) :=
      fun _ hx h ↦ hx (e.injective (h.trans e.map_zero.symm))
    have hg : Set.MapsTo g (Set.ofPred (fun y : W ↦ y ≠ 0))
        (Set.ofPred (fun x : V ↦ x ≠ 0)) :=
      fun _ hy h ↦ hy (e.symm.injective (h.trans e.symm.map_zero.symm))
    let F := relativeSingularHomologyMap ℤ f hf (n + 1)
    let : IsIso F := isIso_relativeSingularHomologyMap_of_inverse ℤ f g hf hg
      (by apply ContinuousMap.ext; intro x; exact e.symm_apply_apply x)
      (by apply ContinuousMap.ext; intro y; exact e.apply_symm_apply y) (n + 1)
    let Ψ := F ≫ (euclideanLocalSuspensionIso ℤ E n).hom
    have hΨ : Function.Injective Ψ :=
      ((ConcreteCategory.isIso_iff_bijective Ψ).mp inferInstance).injective
    have hrec : Ψ (realOrientationCycle b b.orientation) =
        realOrientationCycle c c.orientation := realOrientationCycle_suspension n
    apply htransfer Ψ.hom.toAddMonoidHom hΨ
    change Function.Bijective (fun a : ℤ ↦ a • Ψ (realOrientationCycle b b.orientation))
    rw [hrec]
    exact ih

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The signed actual simplex is a primitive local integral homology generator for every basis. -/
theorem realOrientationCycle_is_generator {r : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r)) :
    Function.Bijective (fun a : ℤ ↦ a • realOrientationCycle b o) := by
  classical
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  let W := ULift.{u} (Fin r → ℝ)
  let c := (Pi.basisFun ℝ (Fin r)).map (ULift.moduleEquiv : W ≃ₗ[ℝ] _).symm
  let e : V ≃L[ℝ] W := (b.equivFun.trans ULift.moduleEquiv.symm).toContinuousLinearEquiv
  let f : C(V, W) := ⟨e, e.continuous⟩
  let g : C(W, V) := ⟨e.symm, e.symm.continuous⟩
  have hf : Set.MapsTo f (Set.ofPred (fun v : V ↦ v ≠ 0))
      (Set.ofPred (fun w : W ↦ w ≠ 0)) :=
    fun _ hv h ↦ hv (e.injective (h.trans e.map_zero.symm))
  have hg : Set.MapsTo g (Set.ofPred (fun w : W ↦ w ≠ 0))
      (Set.ofPred (fun v : V ↦ v ≠ 0)) :=
    fun _ hw h ↦ hw (e.symm.injective (h.trans e.symm.map_zero.symm))
  let F := relativeSingularHomologyMap ℤ f hf r
  let : IsIso F := isIso_relativeSingularHomologyMap_of_inverse ℤ f g hf hg
    (by apply ContinuousMap.ext; intro v; exact e.symm_apply_apply v)
    (by apply ContinuousMap.ext; intro w; exact e.apply_symm_apply w) r
  have hinj : Function.Injective F :=
    ((ConcreteCategory.isIso_iff_bijective F).mp inferInstance).injective
  have hb : b.map e.toLinearEquiv = c := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    apply ULift.ext
    funext j
    change b.equivFun (b i) j = (Pi.basisFun ℝ (Fin r)) i j
    simp [Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have hmap : F (realOrientationCycle b b.orientation) =
      realOrientationCycle c c.orientation := by
    have h := realOrientationCycle_map_basis b e
    rw [hb] at h
    exact h
  -- Transport the geometrically computed coordinate generator through this actual basis chart.
  have hcoordinate := realOrientationCycle_ulift_pi_is_generator.{u} r
  have hpositive : Function.Bijective (fun a : ℤ ↦ a • realOrientationCycle b b.orientation) := by
    constructor
    · intro a a' h
      apply hcoordinate.injective
      have h' := congrArg F h
      simpa only [map_zsmul, hmap] using h'
    · intro z
      obtain ⟨a, ha⟩ := hcoordinate.surjective (F z)
      refine ⟨a, hinj ?_⟩
      simpa only [map_zsmul, hmap] using ha
  -- The original native-orientation sign is a unit, including in dimension zero.
  by_cases h : b.orientation = o
  · subst o
    exact hpositive
  · have hneg : realOrientationCycle b o = -realOrientationCycle b b.orientation := by
      unfold realOrientationCycle
      rw [← map_neg]
      congr 1
      apply Subtype.ext
      change realOrientationRelativeChain b o = -realOrientationRelativeChain b b.orientation
      simp only [realOrientationRelativeChain, h, ite_false, ite_true]
      erw [← map_neg, ← map_neg]
      rfl
    rw [hneg]
    constructor
    · intro a a' h'
      apply hpositive.injective
      simpa only [zsmul_neg, neg_inj] using h'
    · intro z
      obtain ⟨a, ha⟩ := hpositive.surjective (-z)
      refine ⟨a, ?_⟩
      simpa only [zsmul_neg, neg_neg] using congrArg Neg.neg ha


end AtiyahSinger

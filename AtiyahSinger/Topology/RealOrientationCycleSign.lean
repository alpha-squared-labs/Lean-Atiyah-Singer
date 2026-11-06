/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SimplexLocalHomology
public import Mathlib.LinearAlgebra.Reflection

/-!
# The sign of the actual local simplex under reflection

Public module ID: M2047.

A repeated-vertex simplex has relative boundary equal to the original centered
simplex plus its first-vertex swap. Every other face omits an original vertex
and therefore avoids zero. Thus the specified reflection reverses the class
with the native alternating boundary sign, without assuming an orientation
comparison. This is the standard simplex orientation argument used in the
local orientation construction of Milnor--Stasheff, section 9.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open CategoryTheory Convexity Limits Opposite
open scoped Simplicial
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Swapping the first two vertices of the actual centered simplex reverses its local class. -/
theorem realOrientationCycle_reflection {n : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin (n + 1)) ℝ V) (e : V ≃L[ℝ] V)
    (hzero : e (b 0) = -∑ i, b i)
    (hsucc : ∀ i : Fin n, e (b i.succ) = b i.succ) :
    realOrientationCycle (b.map e.toLinearEquiv) (b.map e.toLinearEquiv).orientation =
      -realOrientationCycle b b.orientation := by
  classical
  -- In basis coordinates the reflection is exactly the swap of the first two vertices.
  have hsimplex (t : StdSimplex ℝ (Fin (n + 2))) :
    ((TopCat.of V).toSSetObjEquiv (op ⦋n + 1⦌)
      (realOrientationSimplex (b.map e.toLinearEquiv))) t =
    ((TopCat.of V).toSSetObjEquiv (op ⦋n + 1⦌)
      (realOrientationSimplex b)) (t.map (Equiv.swap 0 1)) := by
    change (∑ i : Fin (n + 1), (t.weights i.succ - t.weights 0) • e (b i)) =
      ∑ i : Fin (n + 1), ((t.map (Equiv.swap 0 1)).weights i.succ -
        (t.map (Equiv.swap 0 1)).weights 0) • b i
    apply b.repr.injective
    ext j
    rw [Module.Basis.repr_sum_self, Fin.sum_univ_succ, hzero]
    simp only [map_add, map_smul, map_neg, map_sum]
    cases j using Fin.cases with
    | zero =>
      simp [hsucc, Module.Basis.repr_self, Finsupp.single_apply, Fin.succ_zero_eq_one]
    | succ j =>
      have hfix : Equiv.swap (0 : Fin (n + 2)) 1 j.succ.succ = j.succ.succ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · exact Fin.succ_ne_zero _
        · intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_one] at hv
          omega
      simp [hsucc, Module.Basis.repr_self, Finsupp.single_apply, hfix]
  let S := TopCat.toSSet.obj (TopCat.of V)
  let A := Set.ofPred (fun v : V ↦ v ≠ 0)
  let Q := relativeSingularChains ℤ A
  let π := relativeSingularChainsProjection ℤ A
  let c := b.map e.toLinearEquiv
  let p : Fin (n + 3) → Fin (n + 2) := Fin.cases 1 id
  let j₂ : Fin (n + 3) := (0 : Fin (n + 1)).succ.succ
  let σ₀ := (TopCat.of V).toSSetObjEquiv (op ⦋n + 1⦌) (realOrientationSimplex b)
  let σ := ((TopCat.of V).toSSetObjEquiv (op ⦋n + 2⦌)).symm
    (⟨fun t ↦ σ₀ (t.map p), σ₀.continuous.comp (StdSimplex.continuous_map ℝ p)⟩ :
      C(StdSimplex ℝ (Fin (n + 3)), V))
  -- The extra vertex creates two surviving faces, both with positive boundary sign.
  have hp₀ : p ∘ (0 : Fin (n + 3)).succAbove = id := by
    funext i
    simp [p]
  have hp₂ : p ∘ j₂.succAbove = Equiv.swap 0 1 := by
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
    · rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [j₂, Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
        omega)]
      simp [p]
    · rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [j₂, Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
        omega)]
      change (0 : Fin (n + 2)) = Equiv.swap 0 1 ((0 : Fin (n + 1)).succ)
      simp [Fin.succ_zero_eq_one]
    · rw [Function.comp_apply, Fin.succAbove_of_le_castSucc _ _ (by
        simp only [j₂, Fin.le_def, Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
        omega)]
      simp only [p, Fin.cases_succ, id_eq]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · exact Fin.succ_ne_zero _
      · intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at hv
        omega
  have hface₀ : S.δ 0 σ = realOrientationSimplex b := by
    apply ((TopCat.of V).toSSetObjEquiv (op ⦋n + 1⦌)).injective
    apply ContinuousMap.ext
    intro t
    change σ₀ ((t.map (0 : Fin (n + 3)).succAbove).map p) = σ₀ t
    rw [← StdSimplex.map_comp, hp₀, StdSimplex.map_id]
  have hface₂ : S.δ j₂ σ = realOrientationSimplex c := by
    apply ((TopCat.of V).toSSetObjEquiv (op ⦋n + 1⦌)).injective
    apply ContinuousMap.ext
    intro t
    change σ₀ ((t.map j₂.succAbove).map p) = _
    rw [← StdSimplex.map_comp, hp₂]
    exact (hsimplex t).symm
  have hinjective (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hi₂ : i ≠ j₂)
      (j : Fin (n + 3)) (h : p j = p i) : j = i := by
    cases i using Fin.cases with
    | zero => exact (hi₀ rfl).elim
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hi : i = 1 := h.symm
        subst i
        exact (hi₂ (by rfl)).elim
      | succ j => exact congrArg Fin.succ h
  -- Any other face misses one original vertex. Its zero barycentric coordinate
  -- is incompatible with the equal positive coordinates forced by a zero image.
  have hface (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hi₂ : i ≠ j₂) :
      S.ιChainComplex (R := singularCoefficient ℤ) (S.δ i σ) ≫ π.f (n + 1) = 0 := by
    let face := (TopCat.of V).toSSetObjEquiv (op ⦋n + 1⦌) (S.δ i σ)
    have hmem (t : StdSimplex ℝ (Fin (n + 2))) : face t ∈ A := by
      let t' := t.map (p ∘ i.succAbove)
      have hmissing : t'.weights (p i) = 0 :=
        Finsupp.mapDomain_of_notMem_range t.weights (p i) (by
          rintro ⟨j, hj⟩
          exact i.succAbove_ne j (hinjective i hi₀ hi₂ _ hj))
      intro hz
      have heq (j : Fin (n + 1)) : t'.weights j.succ = t'.weights 0 := by
        have h := congrArg (fun v ↦ b.repr v j) hz
        change b.repr (∑ k : Fin (n + 1),
          (((t.map i.succAbove).map p).weights k.succ -
            ((t.map i.succAbove).map p).weights 0) • b k) j = _ at h
        rw [← StdSimplex.map_comp] at h
        simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h
        exact sub_eq_zero.mp h
      have hall (j : Fin (n + 2)) : t'.weights j = t'.weights 0 := Fin.cases rfl heq j
      have hzero' : t'.weights 0 = 0 := (hall (p i)).symm.trans hmissing
      have hone := t'.total_of_fintype
      simp only [hall, hzero', Finset.sum_const_zero] at hone
      exact zero_ne_one hone
    let τ := ((TopCat.of A).toSSetObjEquiv (op ⦋n + 1⦌)).symm
      (⟨fun t ↦ ⟨face t, hmem t⟩, face.continuous.subtype_mk _⟩ :
        C(StdSimplex ℝ (Fin (n + 2)), A))
    let a : C(A, V) := ⟨Subtype.val, continuous_subtype_val⟩
    have hτ : (TopCat.toSSet.map (TopCat.ofHom a)).app (op ⦋n + 1⦌) τ = S.δ i σ := rfl
    rw [← hτ, ← SSet.ι_chainComplexMap_f]
    erw [Category.assoc]
    have hz := congrArg (fun h ↦ h.f (n + 1))
      (cokernel.condition (singularSubspaceChains ℤ A))
    change (singularSubspaceChains ℤ A).f (n + 1) ≫ π.f (n + 1) = 0 at hz
    change _ ≫ ((singularSubspaceChains ℤ A).f (n + 1) ≫ π.f (n + 1)) = 0
    erw [hz, comp_zero]
  have hboundary : S.ιChainComplex (R := singularCoefficient ℤ) σ ≫
      π.f (n + 2) ≫ Q.d (n + 2) (n + 1) =
      (S.ιChainComplex (R := singularCoefficient ℤ) (realOrientationSimplex b) ≫
        π.f (n + 1)) +
      (S.ιChainComplex (R := singularCoefficient ℤ) (realOrientationSimplex c) ≫
        π.f (n + 1)) := by
    erw [π.comm, ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    have hface₁ : S.ιChainComplex (R := singularCoefficient ℤ)
        (S.δ (0 : Fin (n + 2)).succ σ) ≫ π.f (n + 1) = 0 := by
      apply hface
      · exact Fin.succ_ne_zero _
      · intro h
        have hv := congrArg Fin.val h
        simp only [j₂, Fin.val_succ, Fin.val_zero] at hv
        omega
    have htail (i : Fin n) : S.ιChainComplex (R := singularCoefficient ℤ)
        (S.δ i.succ.succ.succ σ) ≫ π.f (n + 1) = 0 := by
      apply hface
      · exact Fin.succ_ne_zero _
      · intro h
        have hv := congrArg Fin.val h
        simp only [j₂, Fin.val_succ, Fin.val_zero] at hv
        omega
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Preadditive.zsmul_comp, hface₀, hface₁, htail, Fin.val_zero,
      Fin.val_succ, pow_zero, one_smul, smul_zero, Finset.sum_const_zero, add_zero,
      zero_add]
    change _ + (-1 : ℤ) ^ 2 • (S.ιChainComplex (S.δ j₂ σ) ≫ π.f (n + 1)) = _
    norm_num [hface₂]
  let z₀ : (Q.sc (n + 1)).moduleCatLeftHomologyData.K :=
    ⟨realOrientationRelativeChain b b.orientation,
      realOrientationRelativeChain_mem_cycles b b.orientation⟩
  let z₁ : (Q.sc (n + 1)).moduleCatLeftHomologyData.K :=
    ⟨realOrientationRelativeChain c c.orientation,
      realOrientationRelativeChain_mem_cycles c c.orientation⟩
  let v := π.f (n + 2) (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1))
  have hd : Q.d (n + 2) (n + 1) v = (z₀ + z₁).val := by
    have h := congrArg (fun f ↦ f (ULift.up 1)) hboundary
    change Q.d (n + 2) (n + 1) v =
      π.f (n + 1) (S.ιChainComplex (R := singularCoefficient ℤ)
        (realOrientationSimplex b) (ULift.up 1)) +
        π.f (n + 1) (S.ιChainComplex (R := singularCoefficient ℤ)
          (realOrientationSimplex c) (ULift.up 1)) at h
    change Q.d (n + 2) (n + 1) v = z₀.val + z₁.val
    dsimp only [z₀, z₁, realOrientationRelativeChain]
    simp only [ite_true]
    exact h
  have hmem : z₀ + z₁ ∈ relativeSingularBoundaries ℤ A (n + 1) := by
    refine ⟨(Q.xPrevIso (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)).inv v, ?_⟩
    apply Subtype.ext
    change Q.dTo (n + 1) _ = (z₀ + z₁).val
    rw [← ModuleCat.comp_apply, HomologicalComplex.xPrevIso_comp_dTo]
    exact hd
  have hzero' : relativeSingularCycleClass ℤ A (n + 1) (z₀ + z₁) = 0 := by
    change (Q.sc (n + 1)).moduleCatHomologyIso.inv
      ((relativeSingularBoundaries ℤ A (n + 1)).mkQ (z₀ + z₁)) = 0
    rw [show (relativeSingularBoundaries ℤ A (n + 1)).mkQ (z₀ + z₁) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr hmem, map_zero]
  rw [map_add] at hzero'
  exact eq_neg_of_add_eq_zero_right hzero'

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual linear pair map transports the simplex with its native orientation sign. -/
theorem realOrientationCycle_map {r : ℕ} {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r)) (e : V ≃L[ℝ] W) :
    relativeSingularHomologyMap ℤ (⟨e, e.continuous⟩ : C(V, W))
      (A := (Set.ofPred (fun v : V ↦ v ≠ 0))) (B := (Set.ofPred (fun w : W ↦ w ≠ 0)))
      (fun _ hv h ↦ hv (e.injective (h.trans e.map_zero.symm))) r
      (realOrientationCycle b o) =
        realOrientationCycle (b.map e.toLinearEquiv)
          (Orientation.map (Fin r) e.toLinearEquiv o) := by
  classical
  have hsign {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (b : Module.Basis (Fin r) ℝ E) (o : Orientation ℝ E (Fin r))
      (h : b.orientation ≠ o) :
      realOrientationCycle b o = -realOrientationCycle b b.orientation := by
    unfold realOrientationCycle
    rw [← map_neg]
    congr 1
    apply Subtype.ext
    change realOrientationRelativeChain b o = -realOrientationRelativeChain b b.orientation
    simp only [realOrientationRelativeChain, h, ite_false, ite_true]
    erw [← map_neg, ← map_neg]
    rfl
  -- A linear equivalence carries both the basis orientation and its comparison sign.
  by_cases h : b.orientation = o
  · subst o
    rw [← Module.Basis.orientation_map]
    exact realOrientationCycle_map_basis b e
  · have he : (b.map e.toLinearEquiv).orientation ≠
        Orientation.map (Fin r) e.toLinearEquiv o := by
      rw [Module.Basis.orientation_map]
      exact fun h' ↦ h ((Orientation.map (Fin r) e.toLinearEquiv).injective h')
    rw [hsign b o h, map_neg, hsign _ _ he, realOrientationCycle_map_basis]

end AtiyahSinger

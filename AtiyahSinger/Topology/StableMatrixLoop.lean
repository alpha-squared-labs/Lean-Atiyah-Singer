/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Instances.Matrix

/-!
# Stable based loops in finite general linear groups

Public module ID: M2183.

The group underlying Karoubi III.1.7–1.10 is the direct limit of the based fundamental
groups of GLₙ(A). Here it is constructed as the quotient of actual finite matrix loops
by based homotopy after adjoining identity blocks. Addition is block sum and the inverse
is path reversal. The topology on units records both a matrix and its inverse.

Only a unital complex normed algebra is needed for these constructions; completeness is
not required until the analytic Bott argument. This file does not assert Bott periodicity
or the relative K-group comparison of Karoubi III.1.8. The stable relation, quotient,
block-sum compatibility and abelian group structure are proved for the original finite
matrix representatives. Constant conjugation is removed by a further stabilization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

open scoped unitInterval

variable {A : Type u} [NormedRing A] [hA : NormedAlgebra ℂ A]

/-- Block sum of invertible matrices, in the standard finite-index ordering. -/
def matrixUnitBlockSum {n m : ℕ} (a : (Matrix (Fin n) (Fin n) A)ˣ)
    (b : (Matrix (Fin m) (Fin m) A)ˣ) :
    (Matrix (Fin (n + m)) (Fin (n + m)) A)ˣ :=
  Units.map (Matrix.reindexRingEquiv A finSumFinEquiv).toMonoidHom
    { val := Matrix.fromBlocks (a : _) 0 0 (b : _)
      inv := Matrix.fromBlocks (↑(a⁻¹) : _) 0 0 (↑(b⁻¹) : _)
      val_inv := by simp [Matrix.fromBlocks_multiply]
      inv_val := by simp [Matrix.fromBlocks_multiply] }

/-- Continuity of block sum, including the inverse matrices in the units topology. -/
theorem continuous_matrixUnitBlockSum (n m : ℕ) :
    Continuous (fun ab : (Matrix (Fin n) (Fin n) A)ˣ ×
      (Matrix (Fin m) (Fin m) A)ˣ ↦ matrixUnitBlockSum ab.1 ab.2) := by
  -- Check the matrix and its displayed inverse in the original units topology.
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun ab : (Matrix (Fin n) (Fin n) A)ˣ ×
      (Matrix (Fin m) (Fin m) A)ˣ ↦ Matrix.fromBlocks (ab.1 : Matrix (Fin n) (Fin n) A) 0 0
        (ab.2 : Matrix (Fin m) (Fin m) A)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_val (M := Matrix (Fin n) (Fin n) A)).comp continuous_fst))
    · exact continuous_const
    · exact continuous_const
    · exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_val (M := Matrix (Fin m) (Fin m) A)).comp continuous_snd))
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun ab : (Matrix (Fin n) (Fin n) A)ˣ ×
      (Matrix (Fin m) (Fin m) A)ˣ ↦ Matrix.fromBlocks (↑(ab.1⁻¹) : Matrix (Fin n) (Fin n) A)
        0 0 (↑(ab.2⁻¹) : Matrix (Fin m) (Fin m) A)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · fun_prop
    · exact continuous_const
    · exact continuous_const
    · fun_prop

/-- A based loop in a specified finite general linear group. -/
structure FiniteMatrixLoop (A : Type u) [NormedRing A] where
  /-- The matrix size; size zero is allowed and represents the identity loop. -/
  size : ℕ
  /-- A continuous loop of units with both endpoints equal to the identity. -/
  loop : Path (1 : (Matrix (Fin size) (Fin size) A)ˣ) 1

namespace FiniteMatrixLoop

/-- The constant identity loop of a specified size. -/
def constant (n : ℕ) : FiniteMatrixLoop A where
  size := n
  loop := Path.refl 1

/-- The direct sum of two based matrix loops. -/
def blockSum (p q : FiniteMatrixLoop A) : FiniteMatrixLoop A where
  size := p.size + q.size
  loop :=
    { toFun := fun t ↦ matrixUnitBlockSum (p.loop t) (q.loop t)
      continuous_toFun := (continuous_matrixUnitBlockSum p.size q.size).comp
        (p.loop.continuous.prodMk q.loop.continuous)
      source' := by
        apply Units.ext
        simp [matrixUnitBlockSum, p.loop.source, q.loop.source]
      target' := by
        apply Units.ext
        simp [matrixUnitBlockSum, p.loop.target, q.loop.target] }

/-- Stabilization by an identity block. -/
def stabilize (p : FiniteMatrixLoop A) (k : ℕ) : FiniteMatrixLoop A :=
  p.blockSum (constant k)

/-- Reversing the parameter of a based loop represents its additive inverse. -/
def reverse (p : FiniteMatrixLoop A) : FiniteMatrixLoop A where
  size := p.size
  loop := p.loop.symm

/-- Based homotopy after adding sufficiently many identity coordinates on both sides.
The equality transports the first path into exactly the same finite matrix group. -/
def StablyHomotopic (p q : FiniteMatrixLoop A) : Prop :=
  ∃ k l : ℕ, ∃ h : p.size + k = q.size + l,
    Path.Homotopic
      (cast (congrArg (fun n : ℕ ↦ Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1) h)
        (p.stabilize k).loop) (q.stabilize l).loop

/-- Stable based homotopy is an equivalence relation. -/
theorem stablyHomotopic_equivalence :
    Equivalence (StablyHomotopic (A := A)) := by
  classical
  -- Read the original ordered identity extension directly on its finite coordinates.
  have block_value {n k : ℕ} (u : (Matrix (Fin n) (Fin n) A)ˣ)
      (i j : Fin (n+k)) :
      (matrixUnitBlockSum u (1 : (Matrix (Fin k) (Fin k) A)ˣ) :
        Matrix (Fin (n+k)) (Fin (n+k)) A) i j =
        if hi : i.val < n then if hj : j.val < n then
          (u : Matrix (Fin n) (Fin n) A) ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
        else if i = j then 1 else 0 := by
    classical
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
    · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
      · simp [matrixUnitBlockSum, Matrix.reindex_apply, Matrix.submatrix_apply]
      · simp [matrixUnitBlockSum, Matrix.reindex_apply, Matrix.submatrix_apply]
    · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
      · have hne : Fin.natAdd n i ≠ Fin.castAdd k j := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at this
          omega
        simp [matrixUnitBlockSum, Matrix.reindex_apply, Matrix.submatrix_apply, hne]
      · simp [matrixUnitBlockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  -- Repeated stabilization is exactly the same path after the displayed size transport.
  have stable_assoc (p : FiniteMatrixLoop A) (k l : ℕ) :
      cast (congrArg (fun n : ℕ ↦ Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1)
        (Nat.add_assoc p.size k l)) ((p.stabilize k).stabilize l).loop =
        (p.stabilize (k+l)).loop := by
    classical
    have hcast {n m : ℕ} (h : n = m)
        (q : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1)
        (t : unitInterval) (i j : Fin m) :
        ((cast (congrArg (fun d : ℕ ↦ Path (1 : (Matrix (Fin d) (Fin d) A)ˣ) 1) h) q) t :
          Matrix (Fin m) (Fin m) A) i j =
          (q t : Matrix (Fin n) (Fin n) A) (Fin.cast h.symm i) (Fin.cast h.symm j) := by
      subst m
      rfl
    apply Path.ext
    funext t
    apply Units.ext
    ext i j
    erw [hcast (Nat.add_assoc p.size k l) ((p.stabilize k).stabilize l).loop t i j]
    change (matrixUnitBlockSum
      (matrixUnitBlockSum (p.loop t) (1 : (Matrix (Fin k) (Fin k) A)ˣ))
      (1 : (Matrix (Fin l) (Fin l) A)ˣ) :
      Matrix (Fin (p.size+k+l)) (Fin (p.size+k+l)) A)
        (Fin.cast (Nat.add_assoc p.size k l).symm i)
        (Fin.cast (Nat.add_assoc p.size k l).symm j) =
      (matrixUnitBlockSum (p.loop t) (1 : (Matrix (Fin (k+l)) (Fin (k+l)) A)ˣ) :
        Matrix (Fin (p.size+(k+l))) (Fin (p.size+(k+l))) A) i j
    rw [block_value, block_value]
    by_cases hi : i.val < p.size
    · have hik : i.val < p.size+k := by omega
      simp only [Fin.val_cast, hik, ↓reduceDIte, hi]
      by_cases hjk : j.val < p.size+k
      · simp only [hjk, ↓reduceDIte]
        rw [block_value]
        simp [hi]
      · have hj : ¬ j.val < p.size := by omega
        simp [hjk, hj]
    · by_cases hik : i.val < p.size+k
      · simp only [Fin.val_cast, hik, ↓reduceDIte, hi]
        by_cases hjk : j.val < p.size+k
        · simp only [hjk, ↓reduceDIte]
          rw [block_value]
          simp only [hi, ↓reduceDIte]
          simp only [Fin.ext_iff]
        · have hij : i ≠ j := by intro h; subst j; exact hjk hik
          simp [hjk, hij]
      · simp only [Fin.val_cast, hik, ↓reduceDIte, hi]
        simp only [Fin.ext_iff, Fin.val_cast]
  let P (n : ℕ) := Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1
  let S {n : ℕ} (p : P n) (k : ℕ) : P (n + k) :=
    ((⟨n, p⟩ : FiniteMatrixLoop A).stabilize k).loop
  -- Extend a based homotopy through the same continuous identity-block operation.
  have hLift {n m : ℕ} (h : n = m) (p : P n) (q : P m)
      (H : Path.Homotopic (cast (congrArg P h) p) q) (k : ℕ) :
      Path.Homotopic (cast (congrArg P (congrArg (· + k) h)) (S p k)) (S q k) := by
    subst m
    change Path.Homotopic (S p k) (S q k)
    obtain ⟨H⟩ := H
    refine ⟨{ toFun := fun st ↦ matrixUnitBlockSum (H st) (1 :
        (Matrix (Fin k) (Fin k) A)ˣ)
              continuous_toFun := (continuous_matrixUnitBlockSum n k).comp
                (H.continuous.prodMk continuous_const)
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      change matrixUnitBlockSum (H (0, t)) 1 = matrixUnitBlockSum (p t) 1
      exact congrArg (fun a : (Matrix (Fin n) (Fin n) A)ˣ ↦
        matrixUnitBlockSum a (1 : (Matrix (Fin k) (Fin k) A)ˣ)) (H.map_zero_left t)
    · intro t
      change matrixUnitBlockSum (H (1, t)) 1 = matrixUnitBlockSum (q t) 1
      exact congrArg (fun a : (Matrix (Fin n) (Fin n) A)ˣ ↦
        matrixUnitBlockSum a (1 : (Matrix (Fin k) (Fin k) A)ˣ)) (H.map_one_left t)
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        change matrixUnitBlockSum (H (s, 0)) 1 = matrixUnitBlockSum (p 0) 1
        rw [H.source, p.source]
      · have ht' : t = 1 := ht
        subst t
        change matrixUnitBlockSum (H (s, 1)) 1 = matrixUnitBlockSum (p 1) 1
        rw [H.target, p.target]
  -- Transporting the ambient finite size also transports a based homotopy.
  have hCast {n m : ℕ} (e : n = m) (p q : P n) (H : Path.Homotopic p q) :
      Path.Homotopic (cast (congrArg P e) p) (cast (congrArg P e) q) := by
    subst m
    exact H
  have hSize {n d k l : ℕ} (p : P n) (h : k = l) (e : n + k = d) (e' : n + l = d) :
      cast (congrArg P e) (S p k) = cast (congrArg P e') (S p l) := by
    subst l
    rfl
  have hAssoc {n : ℕ} (p : P n) (k l : ℕ) :
      S (S p k) l = cast (congrArg P (Nat.add_assoc n k l).symm) (S p (k + l)) := by
    have h := stable_assoc (⟨n, p⟩ : FiniteMatrixLoop A) k l
    change cast (congrArg P (Nat.add_assoc n k l)) (S (S p k) l) = S p (k + l) at h
    rw [← h]
    simp only [cast_cast, cast_eq]
  -- Reflexivity and symmetry are direct; transitivity uses one common finite size.
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨0, 0, rfl, Path.Homotopic.refl _⟩
  · intro p q h
    obtain ⟨k, l, e, H⟩ := h
    refine ⟨l, k, e.symm, ?_⟩
    change Path.Homotopic (cast (congrArg P e) (S p.loop k)) (S q.loop l) at H
    change Path.Homotopic (cast (congrArg P e.symm) (S q.loop l)) (S p.loop k)
    have h := hCast e.symm _ _ H.symm
    simpa only [cast_cast, cast_eq] using h
  · intro p q r hpq hqr
    obtain ⟨k₁, l₁, e₁, H₁⟩ := hpq
    obtain ⟨k₂, l₂, e₂, H₂⟩ := hqr
    -- Append the other identity block to each homotopy, then use their common size.
    have H₁' := hLift e₁ (S p.loop k₁) (S q.loop l₁) H₁ k₂
    have H₂' := hLift e₂ (S q.loop k₂) (S r.loop l₂) H₂ l₁
    have d₁ : (q.size + l₁) + k₂ = r.size + (l₂ + l₁) := by omega
    have d₂ : (r.size + l₂) + l₁ = r.size + (l₂ + l₁) := Nat.add_assoc _ _ _
    have K₁ := hCast d₁ _ _ H₁'
    have K₂ := hCast d₂ _ _ H₂'
    rw [hAssoc, hAssoc] at K₁ K₂
    simp only [cast_cast] at K₁ K₂
    have e : p.size + (k₁ + k₂) = r.size + (l₂ + l₁) := by omega
    have d : q.size + (k₂ + l₁) = r.size + (l₂ + l₁) := by omega
    have first : Path.Homotopic
        (cast (congrArg P e) (S p.loop (k₁ + k₂)))
        (cast (congrArg P d) (S q.loop (k₂ + l₁))) := by
      have d' : q.size + (l₁ + k₂) = r.size + (l₂ + l₁) := by omega
      change Path.Homotopic (cast (congrArg P e) (S p.loop (k₁ + k₂)))
        (cast (congrArg P d') (S q.loop (l₁ + k₂))) at K₁
      rw [hSize q.loop (Nat.add_comm l₁ k₂) d' d] at K₁
      exact K₁
    have second : Path.Homotopic
        (cast (congrArg P d) (S q.loop (k₂ + l₁))) (S r.loop (l₂ + l₁)) := by
      simpa only [cast_eq] using K₂
    exact ⟨k₁ + k₂, l₂ + l₁, e, first.trans second⟩

/-- A constant conjugation preserves stable based homotopy.
The doubled conjugator diag(u,u⁻¹) is joined to the identity by elementary shears;
no path from u itself to the identity is assumed. -/
theorem stablyHomotopic_of_conjugate {n : ℕ}
    (p q : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1)
    (u : (Matrix (Fin n) (Fin n) A)ˣ) (h : ∀ t, q t = u * p t * u⁻¹) :
    (⟨n, p⟩ : FiniteMatrixLoop A).StablyHomotopic ⟨n, q⟩ := by
  classical
  let B := Matrix (Fin n) (Fin n) A
  let M := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A
  -- Each elementary shear has the opposite shear as its actual inverse.
  let upper (b : B) : Mˣ :=
    { val := Matrix.fromBlocks 1 b 0 1
      inv := Matrix.fromBlocks 1 (-b) 0 1
      val_inv := by simp [B, M, Matrix.fromBlocks_multiply]
      inv_val := by simp [B, M, Matrix.fromBlocks_multiply] }
  let lower (b : B) : Mˣ :=
    { val := Matrix.fromBlocks 1 0 b 1
      inv := Matrix.fromBlocks 1 0 (-b) 1
      val_inv := by simp [B, M, Matrix.fromBlocks_multiply]
      inv_val := by simp [B, M, Matrix.fromBlocks_multiply] }
  have hup : Continuous upper := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) b 0 1)
      fun_prop
    · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) (-b) 0 1)
      fun_prop
  have hlo : Continuous lower := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) 0 b 1)
      fun_prop
    · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) 0 (-b) 1)
      fun_prop
  let T (t : unitInterval) : ℂ := ((t : ℝ) : ℂ)
  let W (v : Bˣ) (t : unitInterval) : Mˣ :=
    upper (T t • (v : B)) * lower (-T t • (↑(v⁻¹) : B)) * upper (T t • (v : B))
  have hW (v : Bˣ) : Continuous (W v) := by
    exact ((hup.comp (by fun_prop)).mul (hlo.comp (by fun_prop))).mul
      (hup.comp (by fun_prop))
  have hWzero (v : Bˣ) : W v 0 = 1 := by
    apply Units.ext
    simp [W, T, upper, lower, B, M]
  have hWone (v : Bˣ) : (W v 1 : M) =
      Matrix.fromBlocks 0 (v : B) (-(↑(v⁻¹) : B)) 0 := by
    simp [W, T, upper, lower, B, M, Matrix.fromBlocks_multiply]
  let R (t : unitInterval) : Mˣ := W u t * W (-1) t
  have hR : Continuous R := (hW u).mul (hW (-1))
  have hRzero : R 0 = 1 := by simp only [R, hWzero, mul_one]
  have hRone : (R 1 : M) = Matrix.fromBlocks (u : B) 0 0 (↑(u⁻¹) : B) := by
    change (W u 1 : M) * (W (-1) 1 : M) = _
    rw [hWone, hWone]
    simp [B, M, Matrix.fromBlocks_multiply]
  -- Reindex the same path by the production block ordering, keeping both unit components.
  let e := (Matrix.reindexRingEquiv A (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n+n)))
  let U (t : unitInterval) := Units.map e.toMonoidHom (R t)
  have hU : Continuous U := by
    apply Units.continuous_iff.mpr
    constructor
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (continuous_apply (finSumFinEquiv.symm j)).comp
        ((continuous_apply (finSumFinEquiv.symm i)).comp
          ((Units.continuous_val (M := M)).comp hR))
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (continuous_apply (finSumFinEquiv.symm j)).comp
        ((continuous_apply (finSumFinEquiv.symm i)).comp
          ((Units.continuous_coe_inv (M := M)).comp hR))
  have hUzero : U 0 = 1 := by simp only [U, hRzero, map_one]
  have hUone : U 1 = matrixUnitBlockSum u u⁻¹ := by
    apply Units.ext
    exact congrArg e hRone
  have hblock {a b : ℕ} (x x' : (Matrix (Fin a) (Fin a) A)ˣ)
      (y y' : (Matrix (Fin b) (Fin b) A)ˣ) :
      matrixUnitBlockSum x y * matrixUnitBlockSum x' y' =
        matrixUnitBlockSum (x*x') (y*y') := by
    apply Units.ext
    simp [matrixUnitBlockSum, Matrix.fromBlocks_multiply]
  have hbinv {a b : ℕ} (x : (Matrix (Fin a) (Fin a) A)ˣ)
      (y : (Matrix (Fin b) (Fin b) A)ˣ) :
      (matrixUnitBlockSum x y)⁻¹ = matrixUnitBlockSum x⁻¹ y⁻¹ := by
    apply Units.ext
    rfl
  -- Conjugation fixes the based endpoints throughout and realizes the requested conjugate.
  refine ⟨n, n, rfl, ⟨{
    toFun := fun st ↦ U st.1 * matrixUnitBlockSum (p st.2) 1 * (U st.1)⁻¹
    continuous_toFun := ((hU.comp continuous_fst).mul
      ((continuous_matrixUnitBlockSum n n).comp
        ((p.continuous.comp continuous_snd).prodMk continuous_const))).mul
      (hU.comp continuous_fst).inv
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro t
    change U 0 * matrixUnitBlockSum (p t) 1 * (U 0)⁻¹ = matrixUnitBlockSum (p t) 1
    rw [hUzero, inv_one, one_mul, mul_one]
  · intro t
    change U 1 * matrixUnitBlockSum (p t) 1 * (U 1)⁻¹ = matrixUnitBlockSum (q t) 1
    rw [hUone, hbinv, hblock, hblock, mul_one, inv_inv, inv_mul_cancel, h]
  · intro s t ht
    rcases ht with ht | ht
    · subst t
      change U s * matrixUnitBlockSum (p 0) 1 * (U s)⁻¹ = matrixUnitBlockSum (p 0) 1
      rw [p.source]
      have hb : matrixUnitBlockSum (1 : (Matrix (Fin n) (Fin n) A)ˣ)
          (1 : (Matrix (Fin n) (Fin n) A)ˣ) = 1 := by
        apply Units.ext
        simp [matrixUnitBlockSum]
      rw [hb, mul_one, mul_inv_cancel]
    · have ht' : t = 1 := ht
      subst t
      change U s * matrixUnitBlockSum (p 1) 1 * (U s)⁻¹ = matrixUnitBlockSum (p 1) 1
      rw [p.target]
      have hb : matrixUnitBlockSum (1 : (Matrix (Fin n) (Fin n) A)ˣ)
          (1 : (Matrix (Fin n) (Fin n) A)ˣ) = 1 := by
        apply Units.ext
        simp [matrixUnitBlockSum]
      rw [hb, mul_one, mul_inv_cancel]

include hA in
/-- Block sum respects stable based homotopy in both variables. -/
theorem StablyHomotopic.blockSum {p p' q q' : FiniteMatrixLoop A}
    (hp : p.StablyHomotopic p') (hq : q.StablyHomotopic q') :
    (p.blockSum q).StablyHomotopic (p'.blockSum q') := by
  /- Stabilize each homotopy to a common size and take their pointwise block sum.
  Move the inserted identity blocks to the last coordinates using permutation
  conjugation. Stabilizing each conjugator together with its inverse gives a path
  of elementary shears, so the reordering preserves the stable class. -/
  classical
  -- Finite-coordinate changes are constant conjugations, after one further stabilization.
  have hblock_apply {n m : ℕ} (a : (Matrix (Fin n) (Fin n) A)ˣ)
      (b : (Matrix (Fin m) (Fin m) A)ˣ) (i j : Fin (n + m)) :
      (matrixUnitBlockSum a b : Matrix (Fin (n + m)) (Fin (n + m)) A) i j =
        Matrix.fromBlocks (a : Matrix (Fin n) (Fin n) A) 0 0
          (b : Matrix (Fin m) (Fin m) A) (finSumFinEquiv.symm i)
          (finSumFinEquiv.symm j) := by
    rfl
  -- Finite-coordinate changes are constant conjugations, after one further stabilization.
  have rel_reindex (p q : FiniteMatrixLoop A)
      (e : Fin p.size ≃ Fin q.size)
      (he : ∀ t i j, (q.loop t : Matrix (Fin q.size) (Fin q.size) A) (e i) (e j) =
        (p.loop t : Matrix (Fin p.size) (Fin p.size) A) i j) : p.StablyHomotopic q := by
    classical
    rcases p with ⟨n, p⟩
    rcases q with ⟨m, q⟩
    have hsize : n = m := by simpa using Fintype.card_congr e
    subst m
    let u : (Matrix (Fin n) (Fin n) A)ˣ :=
      { val := e.symm.toPEquiv.toMatrix
        inv := e.toPEquiv.toMatrix
        val_inv := by
          rw [PEquiv.toMatrix_toPEquiv_mul]
          ext i j
          simp [Matrix.submatrix_apply, PEquiv.toMatrix_apply, Matrix.one_apply]
        inv_val := by
          rw [PEquiv.toMatrix_toPEquiv_mul]
          ext i j
          simp [Matrix.submatrix_apply, PEquiv.toMatrix_apply, Matrix.one_apply] }
    apply stablyHomotopic_of_conjugate p q u
    intro t
    apply Units.ext
    change (q t : Matrix (Fin n) (Fin n) A) =
      e.symm.toPEquiv.toMatrix * (p t : Matrix (Fin n) (Fin n) A) * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simpa using he t (e.symm i) (e.symm j)
  have rel_swap (p q : FiniteMatrixLoop A) :
      (p.blockSum q).StablyHomotopic (q.blockSum p) := by
    classical
    let e : Fin (p.size+q.size) ≃ Fin (q.size+p.size) :=
      finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)
    apply rel_reindex (p.blockSum q) (q.blockSum p) e
    intro t i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    change (matrixUnitBlockSum (q.loop t) (p.loop t) :
      Matrix (Fin (q.size+p.size)) (Fin (q.size+p.size)) A) (e _) (e _) =
        (matrixUnitBlockSum (p.loop t) (q.loop t) :
          Matrix (Fin (p.size+q.size)) (Fin (p.size+q.size)) A) _ _
    cases i <;> cases j <;>
      simp [e, hblock_apply]
  have rel_middle_swap (p q r : FiniteMatrixLoop A) :
      ((p.blockSum q).blockSum r).StablyHomotopic ((p.blockSum r).blockSum q) := by
    classical
    let e : Fin ((p.size+q.size)+r.size) ≃ Fin ((p.size+r.size)+q.size) :=
      finSumFinEquiv.symm.trans ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
        ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
          ((Equiv.sumAssoc _ _ _).symm.trans
            ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)))))
    apply rel_reindex ((p.blockSum q).blockSum r) ((p.blockSum r).blockSum q) e
    intro t i j
    change Fin ((p.size+q.size)+r.size) at i j
    change (matrixUnitBlockSum (matrixUnitBlockSum (p.loop t) (r.loop t)) (q.loop t) :
      Matrix (Fin ((p.size+r.size)+q.size)) (Fin ((p.size+r.size)+q.size)) A) (e i) (e j) =
        (matrixUnitBlockSum (matrixUnitBlockSum (p.loop t) (q.loop t)) (r.loop t) :
          Matrix (Fin ((p.size+q.size)+r.size)) (Fin ((p.size+q.size)+r.size)) A) i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i
    · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      rcases j with j | j
      · obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        cases i <;> cases j <;>
          simp [e, hblock_apply]
      · cases i <;>
          simp [e, hblock_apply]
    · rcases j with j | j
      · obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        cases j <;>
          simp [e, hblock_apply]
      · simp [e, hblock_apply]
  have stable_zero (p : FiniteMatrixLoop A) : (p.stabilize 0).loop = p.loop := by
    apply Path.ext
    funext t
    apply Units.ext
    ext i j
    change (matrixUnitBlockSum (p.loop t) (1 : (Matrix (Fin 0) (Fin 0) A)ˣ) :
      Matrix (Fin (p.size+0)) (Fin (p.size+0)) A) i j =
        (p.loop t : Matrix (Fin p.size) (Fin p.size) A) i j
    refine Fin.addCases (fun i ↦ ?_) (fun i : Fin 0 ↦ Fin.elim0 i) i
    refine Fin.addCases (fun j ↦ ?_) (fun j : Fin 0 ↦ Fin.elim0 j) j
    change Matrix.fromBlocks (p.loop t : Matrix (Fin p.size) (Fin p.size) A)
      (0 : Matrix (Fin p.size) (Fin 0) A) 0 1
        (finSumFinEquiv.symm (Fin.castAdd 0 i))
        (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have rel_stabilize (p : FiniteMatrixLoop A) (k : ℕ) :
      p.StablyHomotopic (p.stabilize k) := by
    refine ⟨k, 0, rfl, ?_⟩
    change Path.Homotopic (p.stabilize k).loop ((p.stabilize k).stabilize 0).loop
    rw [stable_zero]
  have rel_of_homotopy {n : ℕ}
      (p q : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1) (H : p.Homotopic q) :
      (⟨n,p⟩ : FiniteMatrixLoop A).StablyHomotopic ⟨n,q⟩ := by
    refine ⟨0, 0, rfl, ?_⟩
    change Path.Homotopic ((⟨n,p⟩ : FiniteMatrixLoop A).stabilize 0).loop
      ((⟨n,q⟩ : FiniteMatrixLoop A).stabilize 0).loop
    rw [stable_zero, stable_zero]
    exact H
  have rel_block_lift {n m : ℕ} (e : n = m)
      (p : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1)
      (q : Path (1 : (Matrix (Fin m) (Fin m) A)ˣ) 1)
      (H : Path.Homotopic
        (cast (congrArg (fun d : ℕ ↦ Path (1 : (Matrix (Fin d) (Fin d) A)ˣ) 1) e) p) q)
      (r : FiniteMatrixLoop A) :
      ((⟨n,p⟩ : FiniteMatrixLoop A).blockSum r).StablyHomotopic
        ((⟨m,q⟩ : FiniteMatrixLoop A).blockSum r) := by
    subst m
    obtain ⟨H⟩ := H
    apply rel_of_homotopy
    refine ⟨{ toFun := fun st ↦ matrixUnitBlockSum (H st) (r.loop st.2)
              continuous_toFun := (continuous_matrixUnitBlockSum n r.size).comp
                (H.continuous.prodMk (r.loop.continuous.comp continuous_snd))
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      change matrixUnitBlockSum (H (0,t)) (r.loop t) = matrixUnitBlockSum (p t) (r.loop t)
      exact congrArg (fun v ↦ matrixUnitBlockSum v (r.loop t)) (H.map_zero_left t)
    · intro t
      change matrixUnitBlockSum (H (1,t)) (r.loop t) = matrixUnitBlockSum (q t) (r.loop t)
      exact congrArg (fun v ↦ matrixUnitBlockSum v (r.loop t)) (H.map_one_left t)
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        change matrixUnitBlockSum (H (s,0)) (r.loop 0) = matrixUnitBlockSum (p 0) (r.loop 0)
        rw [H.source, p.source]
      · have ht' : t = 1 := ht
        subst t
        change matrixUnitBlockSum (H (s,1)) (r.loop 1) = matrixUnitBlockSum (p 1) (r.loop 1)
        rw [H.target, p.target]
  -- Extend each supplied homotopy, moving its actual identity blocks past the fixed loop.
  have right {a b : FiniteMatrixLoop A} (hab : a.StablyHomotopic b)
      (c : FiniteMatrixLoop A) : (a.blockSum c).StablyHomotopic (b.blockSum c) := by
    obtain ⟨k,l,e,H⟩ := hab
    have step₁ := rel_stabilize (a.blockSum c) k
    have step₂ := rel_middle_swap a c (constant k)
    have step₃ := rel_block_lift e (a.stabilize k).loop (b.stabilize l).loop H c
    have step₄ := rel_middle_swap b (constant l) c
    have step₅ := (stablyHomotopic_equivalence (A := A)).symm
      (rel_stabilize (b.blockSum c) l)
    exact stablyHomotopic_equivalence.trans step₁
      (stablyHomotopic_equivalence.trans step₂
        (stablyHomotopic_equivalence.trans step₃
          (stablyHomotopic_equivalence.trans step₄ step₅)))
  exact stablyHomotopic_equivalence.trans (right hp q)
    (stablyHomotopic_equivalence.trans (rel_swap p' q)
      (stablyHomotopic_equivalence.trans (right hq p') (rel_swap q' p')))

/-- Reversal respects stable based homotopy. -/
theorem StablyHomotopic.reverse {p q : FiniteMatrixLoop A}
    (h : p.StablyHomotopic q) : p.reverse.StablyHomotopic q.reverse := by
  -- Reversal commutes exactly with adjoining the same constant identity block.
  have hrev (p : FiniteMatrixLoop A) (k : ℕ) :
      (p.reverse.stabilize k).loop = (p.stabilize k).loop.symm := by
    apply Path.ext
    rfl
  have hcast {n m : ℕ} (e : n = m)
      (p : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1) :
      cast (congrArg (fun d ↦ Path (1 : (Matrix (Fin d) (Fin d) A)ˣ) 1) e) p.symm =
        (cast (congrArg (fun d ↦ Path (1 : (Matrix (Fin d) (Fin d) A)ˣ) 1) e) p).symm := by
    subst m
    rfl
  obtain ⟨k, l, e, H⟩ := h
  refine ⟨k, l, e, ?_⟩
  rw [hrev, hrev]
  change Path.Homotopic
    (cast (congrArg (fun n ↦ Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1) e)
      (p.stabilize k).loop.symm) (q.stabilize l).loop.symm
  erw [hcast e]
  exact H.symm₂

/-- The setoid used in the actual stable homotopy quotient. -/
def stableSetoid : Setoid (FiniteMatrixLoop A) where
  r := StablyHomotopic
  iseqv := stablyHomotopic_equivalence

end FiniteMatrixLoop

/-- Stable based loop classes, the usual direct-limit model of π₁(GL(A)). -/
def StableMatrixLoopClass (A : Type u) [NormedRing A] [NormedAlgebra ℂ A] : Type u :=
  Quotient (FiniteMatrixLoop.stableSetoid (A := A))

/-- The stable homotopy class of a finite based matrix loop. -/
def stableMatrixLoopClass (p : FiniteMatrixLoop A) : StableMatrixLoopClass A :=
  Quotient.mk (FiniteMatrixLoop.stableSetoid (A := A)) p

/-- Equality of classes is precisely based homotopy after finite stabilization. -/
theorem stableMatrixLoopClass_eq_iff (p q : FiniteMatrixLoop A) :
    stableMatrixLoopClass p = stableMatrixLoopClass q ↔ p.StablyHomotopic q := by

  exact Quotient.eq

/-- Addition is induced by the concrete block sum of representatives. -/
instance stableMatrixLoopClassAdd : Add (StableMatrixLoopClass A) where
  add := Quotient.map₂ FiniteMatrixLoop.blockSum
    (fun _ _ hp _ _ hq ↦ hp.blockSum hq)

/-- The neutral element is the class of the zero-size identity loop. -/
instance stableMatrixLoopClassZero : Zero (StableMatrixLoopClass A) where
  zero := stableMatrixLoopClass (FiniteMatrixLoop.constant 0)

/-- Negation is induced by path reversal. -/
instance stableMatrixLoopClassNeg : Neg (StableMatrixLoopClass A) where
  neg := Quotient.map FiniteMatrixLoop.reverse (fun _ _ h ↦ h.reverse)

/-- Associativity, identity, inverse and commutativity for the specified quotient operations. -/
theorem stableMatrixLoopClass_group_laws :
    (∀ a b c : StableMatrixLoopClass A, a + b + c = a + (b + c)) ∧
      (∀ a : StableMatrixLoopClass A, 0 + a = a) ∧
      (∀ a : StableMatrixLoopClass A, a + 0 = a) ∧
      (∀ a : StableMatrixLoopClass A, -a + a = 0) ∧
      (∀ a b : StableMatrixLoopClass A, a + b = b + a) := by
  /- First compare block sum with pointwise multiplication after stabilizing both
  loops to the same matrix group. The second block can be moved to the first block
  by a signed rotation, preserving the identity basepoint throughout.
  Pointwise multiplication of based loops represents the same fundamental-group
  operation as concatenation. Path reversal is therefore the inverse operation.
  Associativity and the identity law follow from finite block arithmetic, while
  commutativity follows by conjugating with the actual block permutation after
  stabilizing the conjugator with its inverse. Descend these homotopies to
  the quotient; no Bott-periodicity result is used. -/
  classical
  -- Finite reindexings, associativity, and stabilization preserve the original stable relation.
  have hblock_apply {n m : ℕ} (a : (Matrix (Fin n) (Fin n) A)ˣ)
      (b : (Matrix (Fin m) (Fin m) A)ˣ) (i j : Fin (n + m)) :
      (matrixUnitBlockSum a b : Matrix (Fin (n + m)) (Fin (n + m)) A) i j =
        Matrix.fromBlocks (a : Matrix (Fin n) (Fin n) A) 0 0
          (b : Matrix (Fin m) (Fin m) A) (finSumFinEquiv.symm i)
          (finSumFinEquiv.symm j) := by
    rfl
  -- Finite-coordinate changes are constant conjugations, after one further stabilization.
  have rel_reindex (p q : FiniteMatrixLoop A)
      (e : Fin p.size ≃ Fin q.size)
      (he : ∀ t i j, (q.loop t : Matrix (Fin q.size) (Fin q.size) A) (e i) (e j) =
        (p.loop t : Matrix (Fin p.size) (Fin p.size) A) i j) : p.StablyHomotopic q := by
    classical
    rcases p with ⟨n, p⟩
    rcases q with ⟨m, q⟩
    have hsize : n = m := by simpa using Fintype.card_congr e
    subst m
    let u : (Matrix (Fin n) (Fin n) A)ˣ :=
      { val := e.symm.toPEquiv.toMatrix
        inv := e.toPEquiv.toMatrix
        val_inv := by
          rw [PEquiv.toMatrix_toPEquiv_mul]
          ext i j
          simp [Matrix.submatrix_apply, PEquiv.toMatrix_apply, Matrix.one_apply]
        inv_val := by
          rw [PEquiv.toMatrix_toPEquiv_mul]
          ext i j
          simp [Matrix.submatrix_apply, PEquiv.toMatrix_apply, Matrix.one_apply] }
    apply FiniteMatrixLoop.stablyHomotopic_of_conjugate p q u
    intro t
    apply Units.ext
    change (q t : Matrix (Fin n) (Fin n) A) =
      e.symm.toPEquiv.toMatrix * (p t : Matrix (Fin n) (Fin n) A) * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simpa using he t (e.symm i) (e.symm j)
  have rel_swap (p q : FiniteMatrixLoop A) :
      (p.blockSum q).StablyHomotopic (q.blockSum p) := by
    classical
    let e : Fin (p.size+q.size) ≃ Fin (q.size+p.size) :=
      finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)
    apply rel_reindex (p.blockSum q) (q.blockSum p) e
    intro t i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    change (matrixUnitBlockSum (q.loop t) (p.loop t) :
      Matrix (Fin (q.size+p.size)) (Fin (q.size+p.size)) A) (e _) (e _) =
        (matrixUnitBlockSum (p.loop t) (q.loop t) :
          Matrix (Fin (p.size+q.size)) (Fin (p.size+q.size)) A) _ _
    cases i <;> cases j <;>
      simp [e, hblock_apply]
  have rel_assoc (p q r : FiniteMatrixLoop A) :
      ((p.blockSum q).blockSum r).StablyHomotopic (p.blockSum (q.blockSum r)) := by
    classical
    let e : Fin ((p.size+q.size)+r.size) ≃ Fin (p.size+(q.size+r.size)) :=
      finSumFinEquiv.symm.trans ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
        ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
          finSumFinEquiv)))
    apply rel_reindex ((p.blockSum q).blockSum r) (p.blockSum (q.blockSum r)) e
    intro t i j
    change Fin ((p.size+q.size)+r.size) at i j
    change (matrixUnitBlockSum (p.loop t) (matrixUnitBlockSum (q.loop t) (r.loop t)) :
      Matrix (Fin (p.size+(q.size+r.size))) (Fin (p.size+(q.size+r.size))) A) (e i) (e j) =
        (matrixUnitBlockSum (matrixUnitBlockSum (p.loop t) (q.loop t)) (r.loop t) :
          Matrix (Fin ((p.size+q.size)+r.size)) (Fin ((p.size+q.size)+r.size)) A) i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i
    · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      rcases j with j | j
      · obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        cases i <;> cases j <;>
          simp [e, hblock_apply]
      · cases i <;>
          simp [e, hblock_apply]
    · rcases j with j | j
      · obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        cases j <;>
          simp [e, hblock_apply]
      · simp [e, hblock_apply]
  have stable_zero (p : FiniteMatrixLoop A) : (p.stabilize 0).loop = p.loop := by
    apply Path.ext
    funext t
    apply Units.ext
    ext i j
    change (matrixUnitBlockSum (p.loop t) (1 : (Matrix (Fin 0) (Fin 0) A)ˣ) :
      Matrix (Fin (p.size+0)) (Fin (p.size+0)) A) i j =
        (p.loop t : Matrix (Fin p.size) (Fin p.size) A) i j
    refine Fin.addCases (fun i ↦ ?_) (fun i : Fin 0 ↦ Fin.elim0 i) i
    refine Fin.addCases (fun j ↦ ?_) (fun j : Fin 0 ↦ Fin.elim0 j) j
    change Matrix.fromBlocks (p.loop t : Matrix (Fin p.size) (Fin p.size) A)
      (0 : Matrix (Fin p.size) (Fin 0) A) 0 1
        (finSumFinEquiv.symm (Fin.castAdd 0 i))
        (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have rel_stabilize (p : FiniteMatrixLoop A) (k : ℕ) :
      p.StablyHomotopic (p.stabilize k) := by
    refine ⟨k, 0, rfl, ?_⟩
    change Path.Homotopic (p.stabilize k).loop ((p.stabilize k).stabilize 0).loop
    rw [stable_zero]
  have rel_of_homotopy {n : ℕ}
      (p q : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1) (H : p.Homotopic q) :
      (⟨n,p⟩ : FiniteMatrixLoop A).StablyHomotopic ⟨n,q⟩ := by
    refine ⟨0, 0, rfl, ?_⟩
    change Path.Homotopic ((⟨n,p⟩ : FiniteMatrixLoop A).stabilize 0).loop
      ((⟨n,q⟩ : FiniteMatrixLoop A).stabilize 0).loop
    rw [stable_zero, stable_zero]
    exact H
  have concat_homotopic_pointwise {G : Type u} [TopologicalSpace G] [Group G]
      [IsTopologicalGroup G] (p q r : Path (1 : G) 1)
      (hr : ∀ t, r t = p t * q t) : (p.trans q).Homotopic r := by
    refine ⟨{ toFun := fun st ↦
        Path.delayReflRight st.1 p st.2 * Path.delayReflLeft st.1 q st.2
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · have h₁ : Continuous (fun st : unitInterval × unitInterval ↦
          Path.delayReflRight st.1 p st.2) :=
        (Path.continuous_delayReflRight.comp
          (continuous_fst.prodMk continuous_const)).eval continuous_snd
      have h₂ : Continuous (fun st : unitInterval × unitInterval ↦
          Path.delayReflLeft st.1 q st.2) :=
        (Path.continuous_delayReflLeft.comp
          (continuous_fst.prodMk continuous_const)).eval continuous_snd
      exact h₁.mul h₂
    · intro t
      change Path.delayReflRight 0 p t * Path.delayReflLeft 0 q t = (p.trans q) t
      rw [Path.delayReflRight_zero, Path.delayReflLeft_zero]
      simp only [Path.trans_apply, Path.refl_apply]
      split_ifs <;> simp
    · intro t
      rw [Path.delayReflRight_one, Path.delayReflLeft_one]
      exact (hr t).symm
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        simp
      · have ht' : t = 1 := ht
        subst t
        simp
  have reverse_pointwise_nullhomotopic {G : Type u} [TopologicalSpace G] [Group G]
      [IsTopologicalGroup G] (p r : Path (1 : G) 1)
      (hr : ∀ t, r t = p.symm t * p t) : r.Homotopic (Path.refl 1) := by
    exact (concat_homotopic_pointwise p.symm p r hr).symm.trans
      (Path.Homotopic.symm_trans p)
  have block_sum_homotopic_pointwise {n : ℕ}
      (p q r : Path (1 : (Matrix (Fin n) (Fin n) A)ˣ) 1)
      (hr : ∀ t, r t = p t * q t) :
      (((⟨n, p⟩ : FiniteMatrixLoop A).blockSum ⟨n, q⟩).loop).Homotopic
        (((⟨n, r⟩ : FiniteMatrixLoop A).stabilize n).loop) := by
    classical
    let B := Matrix (Fin n) (Fin n) A
    let M := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A
    -- Each elementary shear has the opposite shear as its actual inverse.
    let upper (b : B) : Mˣ :=
      { val := Matrix.fromBlocks 1 b 0 1
        inv := Matrix.fromBlocks 1 (-b) 0 1
        val_inv := by simp [B, M, Matrix.fromBlocks_multiply]
        inv_val := by simp [B, M, Matrix.fromBlocks_multiply] }
    let lower (b : B) : Mˣ :=
      { val := Matrix.fromBlocks 1 0 b 1
        inv := Matrix.fromBlocks 1 0 (-b) 1
        val_inv := by simp [B, M, Matrix.fromBlocks_multiply]
        inv_val := by simp [B, M, Matrix.fromBlocks_multiply] }
    have hup : Continuous upper := by
      apply Units.continuous_iff.mpr
      constructor
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) b 0 1)
        fun_prop
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) (-b) 0 1)
        fun_prop
    have hlo : Continuous lower := by
      apply Units.continuous_iff.mpr
      constructor
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) 0 b 1)
        fun_prop
      · change Continuous (fun b : B ↦ Matrix.fromBlocks (1 : B) 0 (-b) 1)
        fun_prop
    let T (t : unitInterval) : ℂ := ((t : ℝ) : ℂ)
    let W (v : Bˣ) (t : unitInterval) : Mˣ :=
      upper (T t • (v : B)) * lower (-T t • (↑(v⁻¹) : B)) * upper (T t • (v : B))
    have hW (v : Bˣ) : Continuous (W v) := by
      exact ((hup.comp (by fun_prop)).mul (hlo.comp (by fun_prop))).mul
        (hup.comp (by fun_prop))
    have hWzero (v : Bˣ) : W v 0 = 1 := by
      apply Units.ext
      simp [W, T, upper, lower, B, M]
    have hWone (v : Bˣ) : (W v 1 : M) =
        Matrix.fromBlocks 0 (v : B) (-(↑(v⁻¹) : B)) 0 := by
      simp [W, T, upper, lower, B, M, Matrix.fromBlocks_multiply]
    let e := (Matrix.reindexRingEquiv A (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n+n)))
    let U (t : unitInterval) := Units.map e.toMonoidHom (W (-1) t)
    have hU : Continuous U := by
      apply Units.continuous_iff.mpr
      constructor
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_val (M := M)).comp (hW (-1))))
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact (continuous_apply (finSumFinEquiv.symm j)).comp
          ((continuous_apply (finSumFinEquiv.symm i)).comp
            ((Units.continuous_coe_inv (M := M)).comp (hW (-1))))
    have hUzero : U 0 = 1 := by simp only [U, hWzero, map_one]
    have hswap (b : Bˣ) :
        U 1 * matrixUnitBlockSum (1 : Bˣ) b * (U 1)⁻¹ = matrixUnitBlockSum b (1 : Bˣ) := by
      apply (mul_inv_eq_iff_eq_mul).mpr
      apply Units.ext
      change e (W (-1) 1 : M) * e (Matrix.fromBlocks (1 : B) 0 0 (b : B)) =
        e (Matrix.fromBlocks (b : B) 0 0 (1 : B)) * e (W (-1) 1 : M)
      rw [← map_mul, ← map_mul, hWone]
      simp [B, Matrix.fromBlocks_multiply]
    have hblock (a b c d : Bˣ) :
        matrixUnitBlockSum a b * matrixUnitBlockSum c d =
          matrixUnitBlockSum (a*c) (b*d) := by
      apply Units.ext
      simp [matrixUnitBlockSum, Matrix.fromBlocks_multiply]
    have hb : matrixUnitBlockSum (1 : Bˣ) (1 : Bˣ) = 1 := by
      apply Units.ext
      simp [matrixUnitBlockSum]
    refine ⟨{ toFun := fun st ↦ matrixUnitBlockSum (p st.2) (1 : Bˣ) *
        (U st.1 * matrixUnitBlockSum (1 : Bˣ) (q st.2) * (U st.1)⁻¹)
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · have hp : Continuous (fun st : unitInterval × unitInterval ↦
          matrixUnitBlockSum (p st.2) (1 : Bˣ)) := (continuous_matrixUnitBlockSum n n).comp
        ((p.continuous.comp continuous_snd).prodMk continuous_const)
      have hq : Continuous (fun st : unitInterval × unitInterval ↦
          matrixUnitBlockSum (1 : Bˣ) (q st.2)) := (continuous_matrixUnitBlockSum n n).comp
        (continuous_const.prodMk (q.continuous.comp continuous_snd))
      exact hp.mul (((hU.comp continuous_fst).mul hq).mul (hU.comp continuous_fst).inv)
    · intro t
      change matrixUnitBlockSum (p t) (1 : Bˣ) *
        (U 0 * matrixUnitBlockSum (1 : Bˣ) (q t) * (U 0)⁻¹) =
          matrixUnitBlockSum (p t) (q t)
      rw [hUzero, inv_one, one_mul, mul_one, hblock, mul_one, one_mul]
    · intro t
      change matrixUnitBlockSum (p t) (1 : Bˣ) *
        (U 1 * matrixUnitBlockSum (1 : Bˣ) (q t) * (U 1)⁻¹) =
          matrixUnitBlockSum (r t) (1 : Bˣ)
      rw [hswap, hblock, mul_one, hr]
    · intro s t ht
      rcases ht with ht | ht
      · subst t
        change matrixUnitBlockSum (p 0) (1 : Bˣ) *
          (U s * matrixUnitBlockSum (1 : Bˣ) (q 0) * (U s)⁻¹) =
            matrixUnitBlockSum (p 0) (q 0)
        rw [p.source, q.source, hb, mul_one, mul_inv_cancel, one_mul]
      · have ht' : t = 1 := ht
        subst t
        change matrixUnitBlockSum (p 1) (1 : Bˣ) *
          (U s * matrixUnitBlockSum (1 : Bˣ) (q 1) * (U s)⁻¹) =
            matrixUnitBlockSum (p 1) (q 1)
        rw [p.target, q.target, hb, mul_one, mul_inv_cancel, one_mul]
  -- A constant loop of any size represents the same zero-size class.
  have rel_constant (n : ℕ) : (FiniteMatrixLoop.constant (A := A) n).StablyHomotopic
      (FiniteMatrixLoop.constant 0) := by
    have hc (n k : ℕ) : ((FiniteMatrixLoop.constant (A := A) n).stabilize k).loop =
        Path.refl 1 := by
      apply Path.ext
      funext t
      apply Units.ext
      change (matrixUnitBlockSum (1 : (Matrix (Fin n) (Fin n) A)ˣ)
        (1 : (Matrix (Fin k) (Fin k) A)ˣ) : Matrix (Fin (n+k)) (Fin (n+k)) A) = 1
      simp [matrixUnitBlockSum]
    refine ⟨0, n, show n + 0 = 0 + n by omega, ?_⟩
    rw [hc, hc]
    have hcast {n m : ℕ} (e : n = m) :
        cast (congrArg (fun d : ℕ ↦ Path (1 : (Matrix (Fin d) (Fin d) A)ˣ) 1) e)
          (Path.refl 1) = Path.refl 1 := by subst m; rfl
    erw [hcast (show n + 0 = 0 + n by omega)]
    exact Path.Homotopic.refl _
  -- Descend the actual finite homotopies to the original quotient operations.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro p q r
    change stableMatrixLoopClass ((p.blockSum q).blockSum r) =
      stableMatrixLoopClass (p.blockSum (q.blockSum r))
    exact (stableMatrixLoopClass_eq_iff _ _).mpr (rel_assoc p q r)
  · intro a
    refine Quotient.inductionOn a ?_
    intro p
    change stableMatrixLoopClass ((FiniteMatrixLoop.constant 0).blockSum p) =
      stableMatrixLoopClass p
    apply (stableMatrixLoopClass_eq_iff _ _).mpr
    exact FiniteMatrixLoop.stablyHomotopic_equivalence.trans
      (rel_swap (FiniteMatrixLoop.constant 0) p)
      (FiniteMatrixLoop.stablyHomotopic_equivalence.symm (rel_stabilize p 0))
  · intro a
    refine Quotient.inductionOn a ?_
    intro p
    change stableMatrixLoopClass (p.stabilize 0) = stableMatrixLoopClass p
    exact (stableMatrixLoopClass_eq_iff _ _).mpr
      (FiniteMatrixLoop.stablyHomotopic_equivalence.symm (rel_stabilize p 0))
  · intro a
    refine Quotient.inductionOn a ?_
    intro p
    change stableMatrixLoopClass (p.reverse.blockSum p) =
      stableMatrixLoopClass (FiniteMatrixLoop.constant 0)
    let r : Path (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ) 1 :=
      { toFun := fun t ↦ p.loop.symm t * p.loop t
        continuous_toFun := p.loop.symm.continuous.mul p.loop.continuous
        source' := by simp
        target' := by simp }
    have first := block_sum_homotopic_pointwise p.loop.symm p.loop r (fun _ ↦ rfl)
    have h₁ : (p.reverse.blockSum p).StablyHomotopic
        ((⟨p.size,r⟩ : FiniteMatrixLoop A).stabilize p.size) :=
      rel_of_homotopy _ _ first
    have h₂ := FiniteMatrixLoop.stablyHomotopic_equivalence.symm
      (rel_stabilize (⟨p.size,r⟩ : FiniteMatrixLoop A) p.size)
    have h₃ := rel_of_homotopy r (Path.refl 1)
      (reverse_pointwise_nullhomotopic p.loop r (fun _ ↦ rfl))
    apply (stableMatrixLoopClass_eq_iff _ _).mpr
    exact FiniteMatrixLoop.stablyHomotopic_equivalence.trans h₁
      (FiniteMatrixLoop.stablyHomotopic_equivalence.trans h₂
        (FiniteMatrixLoop.stablyHomotopic_equivalence.trans h₃ (rel_constant p.size)))
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    change stableMatrixLoopClass (p.blockSum q) = stableMatrixLoopClass (q.blockSum p)
    exact (stableMatrixLoopClass_eq_iff _ _).mpr (rel_swap p q)


/-- The usual abelian group structure on stable based loop classes. -/
instance stableMatrixLoopClassAddCommGroup : AddCommGroup (StableMatrixLoopClass A) where
  add_assoc := stableMatrixLoopClass_group_laws.1
  zero_add := stableMatrixLoopClass_group_laws.2.1
  add_zero := stableMatrixLoopClass_group_laws.2.2.1
  neg_add_cancel := stableMatrixLoopClass_group_laws.2.2.2.1
  add_comm := stableMatrixLoopClass_group_laws.2.2.2.2
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Block sum of finite representatives induces addition of stable loop classes. -/
theorem stableMatrixLoopClass_blockSum (p q : FiniteMatrixLoop A) :
    stableMatrixLoopClass (p.blockSum q) = stableMatrixLoopClass p + stableMatrixLoopClass q := by
  /- Addition was defined by descending the very same block-sum operation. -/
  rfl

/-- Adding an identity block does not change a stable based loop class. -/
theorem stableMatrixLoopClass_stabilize (p : FiniteMatrixLoop A) (k : ℕ) :
    stableMatrixLoopClass (p.stabilize k) = stableMatrixLoopClass p := by
  -- A zero-size identity block changes neither the original matrix nor its path.
  have hzero (q : FiniteMatrixLoop A) : (q.stabilize 0).loop = q.loop := by
    apply Path.ext
    funext t
    apply Units.ext
    ext i j
    change (matrixUnitBlockSum (q.loop t) (1 : (Matrix (Fin 0) (Fin 0) A)ˣ) :
      Matrix (Fin (q.size + 0)) (Fin (q.size + 0)) A) i j =
      (q.loop t : Matrix (Fin q.size) (Fin q.size) A) i j
    refine Fin.addCases (fun i ↦ ?_) (fun i : Fin 0 ↦ Fin.elim0 i) i
    refine Fin.addCases (fun j ↦ ?_) (fun j : Fin 0 ↦ Fin.elim0 j) j
    change Matrix.fromBlocks (q.loop t : Matrix (Fin q.size) (Fin q.size) A)
      (0 : Matrix (Fin q.size) (Fin 0) A) 0 1
        (finSumFinEquiv.symm (Fin.castAdd 0 i))
        (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  apply (stableMatrixLoopClass_eq_iff _ _).mpr
  -- Both representatives become the same path in size p.size + k.
  refine ⟨0, k, rfl, ?_⟩
  change Path.Homotopic ((p.stabilize k).stabilize 0).loop (p.stabilize k).loop
  rw [hzero]
  exact Path.Homotopic.refl _

/-- Path reversal realizes the inverse stable loop class. -/
theorem stableMatrixLoopClass_reverse (p : FiniteMatrixLoop A) :
    stableMatrixLoopClass p.reverse = -stableMatrixLoopClass p := by
  -- The existing quotient negation uses this very same reversal of representatives.
  rfl

end AtiyahSinger

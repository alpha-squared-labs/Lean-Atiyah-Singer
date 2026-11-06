/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AffineSimplexSubdivision
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# Mesh estimates for the original affine barycentric subdivision

Public module ID: M1525.

The centroid of a simplex lies within n/(n+1) times its diameter of every
point in its convex hull. Recursing over the original finite cone subdivision
gives the same contraction for each simplex in its support. Affine coordinate
maps allow this estimate to be applied to the native standard simplex without
changing its topology or its singular realization.

Source: the mesh argument in Hatcher, Algebraic Topology, section 2.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Convexity
open scoped BigOperators

universe u v w

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [ConvexSpace ℝ V] [IsModuleConvexSpace ℝ V]

/-- The centroid belongs to the original convex hull and is uniformly close to every point of it. -/
theorem barycenter_convexHull_bound (k : ℕ) (v : Fin (k + 1) → V)
    (D : ℝ) (_hD : 0 ≤ D) (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    (StdSimplex.barycenter (K := ℝ)).iConvexComb v ∈ convexHull ℝ (Set.range v) ∧
      ∀ x ∈ convexHull ℝ (Set.range v),
        dist ((StdSimplex.barycenter (K := ℝ)).iConvexComb v) x ≤
          (k : ℝ) / (k + 1) * D := by
  classical
  let a : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : ∑ _ : Fin (k + 1), a = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, a]
    exact mul_inv_cancel₀ (by positivity)
  have hc : (StdSimplex.barycenter (K := ℝ)).iConvexComb v = ∑ i, a • v i := by
    rw [iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
    simp only [StdSimplex.weights_barycenter_apply, Fintype.card_fin, a]
  constructor
  · rw [hc]
    exact (convex_convexHull ℝ (Set.range v)).sum_mem (fun _ _ ↦ ha) hs
      (fun i _ ↦ subset_convexHull ℝ (Set.range v) ⟨i, rfl⟩)
  · -- One summand vanishes at each vertex; the remaining k summands are bounded by D.
    have hvertex (i : Fin (k + 1)) :
        dist ((StdSimplex.barycenter (K := ℝ)).iConvexComb v) (v i) ≤
          (k : ℝ) / (k + 1) * D := by
      have hd : (∑ j, a • v j) - v i = ∑ j, a • (v j - v i) := by
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]
      have hsum : (∑ j : Fin (k + 1), ‖v j - v i‖) ≤ (k : ℝ) * D := by
        calc
          _ = ∑ j ∈ Finset.univ.erase i, ‖v j - v i‖ := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
            simp
          _ ≤ ∑ _j ∈ Finset.univ.erase i, D := by
            apply Finset.sum_le_sum
            intro j _
            simpa only [dist_eq_norm] using hv j i
          _ = (k : ℝ) * D := by simp
      rw [hc, dist_eq_norm, hd]
      calc
        _ ≤ ∑ j : Fin (k + 1), ‖a • (v j - v i)‖ := norm_sum_le _ _
        _ = a * ∑ j : Fin (k + 1), ‖v j - v i‖ := by
          simp only [norm_smul, Real.norm_of_nonneg ha, Finset.mul_sum]
        _ ≤ a * ((k : ℝ) * D) := mul_le_mul_of_nonneg_left hsum ha
        _ = (k : ℝ) / (k + 1) * D := by simp only [a, Nat.cast_add, Nat.cast_one]; ring
    -- A closed ball is convex, so the same estimate extends from the vertices to their hull.
    have hball : convexHull ℝ (Set.range v) ⊆ Metric.closedBall
        ((StdSimplex.barycenter (K := ℝ)).iConvexComb v) ((k : ℝ) / (k + 1) * D) := by
      apply convexHull_min _ (convex_closedBall _ _)
      rintro _ ⟨i, rfl⟩
      rw [Metric.mem_closedBall, dist_comm]
      exact hvertex i
    intro x hx
    simpa only [Metric.mem_closedBall, dist_comm] using hball hx

variable (R : Type u) [CommRing R] {E : Type v} [ConvexSpace ℝ E]

/-- Every simplex in the original subdivision remains in the vertex hull and contracts its mesh. -/
theorem vertexChainSubdivision_support_mesh (f : ConvexSpace.AffineMap ℝ E V)
    (k : ℕ) (v : Fin (k + 1) → E) (a : R) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (f (v i)) (f (v j)) ≤ D)
    (w : Fin (k + 1) → E)
    (hw : w ∈ (vertexChainSubdivision R E (k + 1) (Finsupp.single v a)).support) :
    (∀ j, f (w j) ∈ convexHull ℝ (Set.range (f ∘ v))) ∧
      ∀ i j, dist (f (w i)) (f (w j)) ≤ (k : ℝ) / (k + 1) * D := by
  classical
  induction k generalizing a D with
  | zero =>
    have hvcons : Fin.cons (v 0) (v ∘ Fin.succ) = v := by
      funext j
      fin_cases j
      rfl
    have hsd : vertexChainSubdivision R E 1 (Finsupp.single v a) = Finsupp.single v a := by
      simp [vertexChainBoundary_single, vertexChainSubdivision,
        StdSimplex.barycenter_fin_one, hvcons]
    rw [hsd] at hw
    have hwv : w = v := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hw) (Finsupp.single_eq_of_ne h)
    subst w
    constructor
    · intro j
      exact subset_convexHull ℝ (Set.range (f ∘ v)) ⟨j, rfl⟩
    · intro i j
      have hij : i = j := Fin.ext (by omega)
      simp [hij]
  | succ k ih =>
    let c := (StdSimplex.barycenter (K := ℝ)).iConvexComb v
    let b := vertexChainSubdivision R E (k + 1)
      (vertexChainBoundary R E (k + 1) (Finsupp.single v 1))
    rw [vertexChainSubdivision_single] at hw
    have hwcone : w ∈ (vertexChainCone R E c (k + 1) b).support :=
      Finsupp.support_smul hw
    -- A supported cone term comes from a supported subdivided boundary face.
    have himage : w ∈ (fun t : Fin (k + 1) → E ↦ Fin.cons c t) '' (b.support : Set _) := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hwcone)
        (Finsupp.mapDomain_of_notMem_image_support h)
    obtain ⟨t, ht, rfl⟩ := himage
    change t ∈ (vertexChainSubdivision R E (k + 1)
      (vertexChainBoundary R E (k + 1) (Finsupp.single v 1))).support at ht
    rw [vertexChainBoundary_single] at ht
    simp only [one_smul, map_sum, map_smul] at ht
    obtain ⟨i, _, hti⟩ := Finsupp.mem_support_finsetSum t ht
    have htface := Finsupp.support_smul hti
    obtain ⟨hthull, htmesh⟩ := ih (v ∘ i.succAbove) 1 D hD
      (fun a b ↦ hv (i.succAbove a) (i.succAbove b)) t htface
    have hface : convexHull ℝ (Set.range (f ∘ (v ∘ i.succAbove))) ⊆
        convexHull ℝ (Set.range (f ∘ v)) := by
      apply convexHull_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨i.succAbove j, rfl⟩
    have hcent : f c = (StdSimplex.barycenter (K := ℝ)).iConvexComb (f ∘ v) :=
      f.isAffineMap.map_iConvexComb _ v
    obtain ⟨hchull, hcdist⟩ := barycenter_convexHull_bound (k + 1) (f ∘ v) D hD hv
    have hratio : (k : ℝ) / (k + 1) ≤ ((k + 1 : ℕ) : ℝ) / (k + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith
    constructor
    · intro j
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simpa only [Fin.cons_zero, hcent] using hchull
      · simpa only [Fin.cons_succ] using hface (hthull j)
    · intro j l
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · refine Fin.cases ?_ (fun l ↦ ?_) l
        · simp only [Fin.cons_zero, dist_self]
          positivity
        · simpa only [Fin.cons_zero, Fin.cons_succ, hcent, Nat.cast_add, Nat.cast_one] using
            hcdist (f (t l)) (hface (hthull l))
      · refine Fin.cases ?_ (fun l ↦ ?_) l
        · simpa only [Fin.cons_zero, Fin.cons_succ, hcent, dist_comm,
            Nat.cast_add, Nat.cast_one] using hcdist (f (t j)) (hface (hthull j))
        · apply (htmesh j l).trans
          simpa only [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_right hratio hD

/-- Repeated original subdivision keeps the same hull and contracts mesh by a geometric power. -/
theorem vertexChainSubdivision_iterate_support_mesh (f : ConvexSpace.AffineMap ℝ E V)
    (k m : ℕ) (v : Fin (k + 1) → E) (a : R) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (f (v i)) (f (v j)) ≤ D)
    (w : Fin (k + 1) → E)
    (hw : w ∈ ((vertexChainSubdivision R E (k + 1))^[m] (Finsupp.single v a)).support) :
    (∀ j, f (w j) ∈ convexHull ℝ (Set.range (f ∘ v))) ∧
      ∀ i j, dist (f (w i)) (f (w j)) ≤ ((k : ℝ) / (k + 1)) ^ m * D := by
  classical
  induction m generalizing w with
  | zero =>
    change w ∈ (Finsupp.single v a).support at hw
    have hwv : w = v := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hw) (Finsupp.single_eq_of_ne h)
    subst w
    exact ⟨fun j ↦ subset_convexHull ℝ (Set.range (f ∘ v)) ⟨j, rfl⟩,
      fun i j ↦ by simpa using hv i j⟩
  | succ m ih =>
    let T := vertexChainSubdivision R E (k + 1)
    let c := T^[m] (Finsupp.single v a)
    have hexp : T c = ∑ t ∈ c.support, T (Finsupp.single t (c t)) := by
      calc
        T c = T (c.sum (fun t b ↦ Finsupp.single t b)) :=
          congrArg T (Finsupp.sum_single c).symm
        _ = _ := map_sum T _ _
    rw [Function.iterate_succ_apply'] at hw
    change w ∈ (T c).support at hw
    rw [hexp] at hw
    obtain ⟨t, ht, hwt⟩ := Finsupp.mem_support_finsetSum w hw
    obtain ⟨hthull, htmesh⟩ := ih t ht
    have hnonneg : 0 ≤ ((k : ℝ) / (k + 1)) ^ m * D := by positivity
    obtain ⟨hwhull, hwmesh⟩ := vertexChainSubdivision_support_mesh R f k t (c t)
      (((k : ℝ) / (k + 1)) ^ m * D) hnonneg htmesh w hwt
    constructor
    · intro j
      apply convexHull_min _ (convex_convexHull ℝ (Set.range (f ∘ v))) (hwhull j)
      rintro _ ⟨l, rfl⟩
      exact hthull l
    · intro i j
      calc
        _ ≤ (k : ℝ) / (k + 1) * (((k : ℝ) / (k + 1)) ^ m * D) := hwmesh i j
        _ = ((k : ℝ) / (k + 1)) ^ (m + 1) * D := by rw [pow_succ]; ring

/-- In every fixed dimension, all sufficiently iterated subdivision simplices have small mesh. -/
theorem vertexChainSubdivision_eventually_mesh_lt (f : ConvexSpace.AffineMap ℝ E V)
    (k : ℕ) (v : Fin (k + 1) → E) (a : R) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ w : Fin (k + 1) → E,
      w ∈ ((vertexChainSubdivision R E (k + 1))^[m] (Finsupp.single v a)).support →
        ∀ i j, dist (f (w i)) (f (w j)) < ε := by
  classical
  let D : ℝ := ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), dist (f (v i)) (f (v j))
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))
  have hv (i j : Fin (k + 1)) : dist (f (v i)) (f (v j)) ≤ D := by
    calc
      _ ≤ ∑ l : Fin (k + 1), dist (f (v i)) (f (v l)) :=
        Finset.single_le_sum (fun _ _ ↦ dist_nonneg) (Finset.mem_univ j)
      _ ≤ D :=
        Finset.single_le_sum
          (f := fun i : Fin (k + 1) ↦ ∑ j : Fin (k + 1), dist (f (v i)) (f (v j)))
          (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))
          (Finset.mem_univ i)
  let q : ℝ := (k : ℝ) / (k + 1)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have ht : Filter.Tendsto (fun m : ℕ ↦ q ^ m * D) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const D
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨N, ?_⟩
  intro m hm w hw i j
  have hle := (vertexChainSubdivision_iterate_support_mesh R f k m v a D hD hv w hw).2 i j
  exact hle.trans_lt (hN m hm)

/-- Eventually the whole affine image of each subdivision simplex lies in a small vertex ball. -/
theorem vertexChainSubdivision_eventually_affine_ball (f : ConvexSpace.AffineMap ℝ E V)
    (k : ℕ) (v : Fin (k + 1) → E) (a : R) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ w : Fin (k + 1) → E,
      w ∈ ((vertexChainSubdivision R E (k + 1))^[m] (Finsupp.single v a)).support →
        ∀ t : StdSimplex ℝ (Fin (k + 1)),
          dist (f (StdSimplex.affineMapMk (R := ℝ) w t)) (f (w 0)) < ε := by
  classical
  obtain ⟨N, hN⟩ := vertexChainSubdivision_eventually_mesh_lt R f k v a ε hε
  refine ⟨N, ?_⟩
  intro m hm w hw t
  -- Every vertex lies in the same open ball, which contains all their convex combinations.
  have hvertex (i : Fin (k + 1)) : f (w i) ∈ Metric.ball (f (w 0)) ε :=
    hN m hm w hw i 0
  rw [StdSimplex.affineMapMk_apply, f.isAffineMap.map_iConvexComb, iConvexComb_eq_sum,
    Finsupp.sum_fintype _ _ (by simp)]
  exact (convex_ball (f (w 0)) ε).sum_mem (fun i _ ↦ t.weights_nonneg i)
    t.total_of_fintype (fun i _ ↦ hvertex i)

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev

/-!
# The order filtration of atlas pseudodifferential operators

Public module ID: M0284.

A02: the original locally finite-rank section operators form a complex vector
space in each real order, with increasing order filtration. Its intersection
over all real orders is exactly the existing all-order Sobolev smoothing class.
Both sides concern one fixed map on the original smooth sections. No common
global rank, density, homogeneous principal representative or ellipticity is
assumed. The smoothing class can couple distinct connected components.

Sources: Spin Geometry III.3.15--3.17, pp.186--187. The filtration and
intersection statements follow from the finite local representation and
Sobolev estimate. Closure supplies the order submodule; the intersection
uses the actual critical Sobolev extension between the given presentations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- The actual order class is closed under zero, addition and complex scalar multiplication. -/
theorem isAtlasPseudodifferentialOperator_closure (m : ℝ) :
    IsAtlasPseudodifferentialOperator A B m 0 ∧
      (∀ P Q : A.smoothSections →ₗ[ℂ] B.smoothSections,
        IsAtlasPseudodifferentialOperator A B m P →
        IsAtlasPseudodifferentialOperator A B m Q →
        IsAtlasPseudodifferentialOperator A B m (P + Q)) ∧
      ∀ (z : ℂ) (P : A.smoothSections →ₗ[ℂ] B.smoothSections),
        IsAtlasPseudodifferentialOperator A B m P →
        IsAtlasPseudodifferentialOperator A B m (z • P) := by
  /- Stage 1: the zero operator has the empty local representation and
  the zero bounded extension at every pair of Sobolev orders.
  Stage 2: concatenate the two finite families of actual local pieces.
  Their sum is exactly the sum of the two section maps after subtraction
  of the sum of their smoothing remainders. Add the bounded extensions
  of those remainders at the same two presentations and the same orders.
  Stage 3: multiply each actual coordinate operator and its full symbol
  by z, retaining its original chart, frames and cutoffs. Fourier
  quantization is complex-linear, so its section action is z times the
  original action. Scale each bounded remainder extension by the same z.
  These operations require neither equal ranks nor connectedness. -/
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- The empty family leaves zero, with a zero extension at every pair of orders.
    refine ⟨0, Fin.elim0, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    intro L K s t
    exact ⟨0, fun u ↦ by simp⟩
  · intro P Q hP hQ
    obtain ⟨N, L, hL⟩ := hP
    obtain ⟨N', L', hL'⟩ := hQ
    -- Concatenate the actual local pieces; add the two remainder extensions.
    refine ⟨N + N', Fin.append L L', ?_⟩
    intro C D s t
    obtain ⟨T, hT⟩ := hL C D s t
    obtain ⟨T', hT'⟩ := hL' C D s t
    refine ⟨T + T', ?_⟩
    intro u
    rw [add_apply, hT, hT', ← map_add]
    congr 1
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.sum_apply]
    abel
  · intro z P hP
    obtain ⟨N, L, hL⟩ := hP
    -- Scale the coordinate maps and symbols together, keeping each original cutoff and frame.
    let L' (j : Fin N) : AtlasPseudodifferentialPiece A B m :=
      { L j with
        operator := z • (L j).operator
        symbol := z • (L j).symbol
        isSymbol := (L j).isSymbol.smul isOpen_univ z
        operator_apply := by
          intro u x
          change z • (L j).operator u x = quantize (z • (L j).symbol) u x
          rw [(L j).operator_apply]
          simp only [quantize, Pi.smul_apply, smul_apply]
          simp_rw [smul_comm (Complex.exp _) z]
          rw [MeasureTheory.integral_smul, smul_comm] }
    have hlocal (j : Fin N) : (L' j).toLinearMap = z • (L j).toLinearMap := by
      apply LinearMap.ext
      intro u
      change (L j).output.extendLinearMap (L j).chart_mem_atlas
        (z • (L j).operator ((L j).input.localize (L j).chart_mem_atlas u)) =
          z • (L j).output.extendLinearMap (L j).chart_mem_atlas
            ((L j).operator ((L j).input.localize (L j).chart_mem_atlas u))
      exact map_smul _ z _
    refine ⟨N, L', ?_⟩
    intro C D s t
    obtain ⟨T, hT⟩ := hL C D s t
    -- The same scalar scales the bounded remainder between the same two completions.
    refine ⟨z • T, ?_⟩
    intro u
    rw [smul_apply, hT, ← map_smul]
    congr 1
    simp only [hlocal, ← Finset.smul_sum, ← smul_sub, LinearMap.smul_apply]

/-- The standard order submodule of actual operators on the original smooth sections. -/
def atlasPseudodifferentialSpace (m : ℝ) :
    Submodule ℂ (A.smoothSections →ₗ[ℂ] B.smoothSections) where
  carrier := {P | IsAtlasPseudodifferentialOperator A B m P}
  zero_mem' := (isAtlasPseudodifferentialOperator_closure A B m).1
  add_mem' := fun hP hQ ↦
    (isAtlasPseudodifferentialOperator_closure A B m).2.1 _ _ hP hQ
  smul_mem' := fun z P hP ↦
    (isAtlasPseudodifferentialOperator_closure A B m).2.2 z P hP

/-- Increasing the allowed order preserves the same actual atlas operator. -/
theorem IsAtlasPseudodifferentialOperator.mono {m l : ℝ} (hml : m ≤ l)
    {P : A.smoothSections →ₗ[ℂ] B.smoothSections}
    (hP : IsAtlasPseudodifferentialOperator A B m P) :
    IsAtlasPseudodifferentialOperator A B l P := by
  /- Retain the finite local representation of hP, including all its
  charts, original frames, cutoffs, coordinate operators and full symbols.
  Symbol order monotonicity changes only each isSymbol field from order m
  to order l. Every transported section map is unchanged, so the same
  all-order smoothing remainder represents the original P at order l. -/
  obtain ⟨N, L, hL⟩ := hP
  -- Only the order certificate changes; all original section maps stay identical.
  let L' (j : Fin N) : AtlasPseudodifferentialPiece A B l :=
    { L j with isSymbol := (L j).isSymbol.mono hml }
  exact ⟨N, L', hL⟩

/-- The intersection of all real atlas PDO orders is precisely all-order Sobolev smoothing. -/
theorem isAtlasSmoothingOperator_iff_forall_isAtlasPseudodifferentialOperator
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) :
    IsAtlasSmoothingOperator A B P ↔
      ∀ m : ℝ, IsAtlasPseudodifferentialOperator A B m P := by
  /- Stage 1: a smoothing operator belongs to every order by the empty
  local representation. Its remainder is exactly P, not a new map.
  Stage 2: conversely fix any two original finite Sobolev presentations
  and any source and target orders s and t. Regard the same P as an atlas
  PDO of order s-t. Its established Sobolev extension maps order s to
  order s-(s-t)=t and agrees with P on every original smooth section.
  Stage 3: varying the two presentations and the two orders gives the
  existing IsAtlasSmoothingOperator predicate. There is no assertion that
  a fixed finite order suffices, and no smooth kernel or density is chosen. -/
  classical
  constructor
  · intro h m
    -- The empty local sum leaves this same all-order remainder.
    refine ⟨0, Fin.elim0, ?_⟩
    simpa using h
  · intro h L K s t
    -- Choose precisely the order that realizes this specified source and target pair.
    let Q : AtlasPseudodifferentialOperator A B (s - t) := ⟨P, h (s - t)⟩
    have hord : s - (s - t) = t := by ring
    have hQ : ∃ T : L.SobolevSpace s →L[ℂ] K.SobolevSpace (s - (s - t)),
        ∀ u : A.smoothSections,
          T (L.smoothToSobolev s u) = K.smoothToSobolev (s - (s - t)) (P u) :=
      (Q.existsUnique_sobolevExtension L K s).exists
    rwa [hord] at hQ

end AtiyahSinger

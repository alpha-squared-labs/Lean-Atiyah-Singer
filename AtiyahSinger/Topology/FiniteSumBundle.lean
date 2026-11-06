/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.BundleTrivial
public import AtiyahSinger.Topology.HermitianMetricComap
public import AtiyahSinger.Topology.HermitianMetricSum

/-!
# Finite sums of the specified complex bundles

Public module ID: M1858.

The fibers are the actual finite dependent products, with the topology induced
by their common base and original total-space coordinates. This is exactly the
topology used by the original Hermitian flag sum, including the empty sum.
Head--tail splitting, coordinatewise isomorphisms and pullback comparisons keep
these vectors, rather than introducing a recursively chosen replacement bundle.
The orthogonal metric uses the supplied forms on those same coordinates.

Source: finite direct sums and pullback of vector bundles, Husemoller,
Fibre Bundles, Chapter III. These are implementation interfaces for the original
flag splitting and its projective enlargement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped ComplexConjugate

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- The finite sum retains precisely the specified coordinate fibers. -/
abbrev FiniteSum (n : ℕ) (L : Fin n → X → Type v) (x : X) : Type v := ∀ i, L i x

/-- The same-base product topology, retaining the base for the empty family. -/
@[reducible]
def finiteSumTopology (n : ℕ) (L : Fin n → X → Type v)
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] :
    TopologicalSpace (TotalSpace Unit (FiniteSum n L)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (FiniteSum n L) ↦
      (z.proj, fun i ↦ (⟨z.proj, z.snd i⟩ : TotalSpace Unit (L i)))) inferInstance

attribute [local instance] finiteSumTopology sumTopology trivialTopology

private theorem continuous_finiteSum_coordinates (n : ℕ) (L : Fin n → X → Type v)
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] :
    Continuous (fun z : TotalSpace Unit (FiniteSum n L) ↦
      (z.proj, fun i ↦ (⟨z.proj, z.snd i⟩ : TotalSpace Unit (L i)))) :=
  continuous_induced_dom

/-- The actual first coordinate and tail identify the finite sum with a binary sum. -/
def finiteSumSuccIso (n : ℕ) (L : Fin (n + 1) → X → Type v)
    [∀ i x, AddCommGroup (L i x)] [∀ i x, Module ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] :
    Iso (FiniteSum (n + 1) L) (L 0 ×ᵇ FiniteSum n (fun i ↦ L i.succ)) where
  linearEquiv x :=
    { toFun := fun v ↦ (v 0, fun i ↦ v i.succ)
      invFun := fun v ↦ Fin.cons v.1 v.2
      left_inv := fun v ↦ by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  continuous_total := by
    have hc := continuous_finiteSum_coordinates (n + 1) L
    apply continuous_induced_rng.mpr
    refine ((continuous_apply 0).comp hc.snd).prodMk ?_
    apply continuous_induced_rng.mpr
    exact hc.fst.prodMk (continuous_pi (fun i ↦ (continuous_apply i.succ).comp hc.snd))
  continuous_symm := by
    have ht := (continuous_finiteSum_coordinates n (fun i ↦ L i.succ)).comp
      (continuous_sum_snd (E := L 0) (F := FiniteSum n (fun i ↦ L i.succ)))
    apply continuous_induced_rng.mpr
    refine ht.fst.prodMk (continuous_pi (fun i ↦ ?_))
    exact Fin.cases (continuous_sum_fst (E := L 0))
      (fun j ↦ (continuous_apply j).comp ht.snd) i

/-- The empty actual sum is the original zero-dimensional trivial bundle. -/
def finiteSumZeroIso (L : Fin 0 → X → Type v)
    [∀ i x, AddCommGroup (L i x)] [∀ i x, Module ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] :
    Iso (FiniteSum 0 L) (Bundle.Trivial X (Fin 0 → ℂ)) where
  linearEquiv x := LinearEquiv.ofSubsingleton (R := ℂ) (FiniteSum 0 L x) (Fin 0 → ℂ)
  continuous_total := by
    apply continuous_induced_rng.mpr
    exact (continuous_finiteSum_coordinates 0 L).fst.prodMk
      (continuous_pi (fun i ↦ Fin.elim0 i))
  continuous_symm := by
    have hc : Continuous (fun z : TotalSpace Unit (Bundle.Trivial X (Fin 0 → ℂ)) ↦
        (z.proj, z.snd)) := continuous_induced_dom
    apply continuous_induced_rng.mpr
    exact hc.fst.prodMk (continuous_pi (fun i ↦ Fin.elim0 i))

/-- A finite sum of locally finite-rank bundles has locally finite rank. -/
theorem isFiniteRank_finiteSum (n : ℕ) (L : Fin n → X → Type v)
    [∀ i x, AddCommGroup (L i x)] [∀ i x, Module ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] [∀ i, IsFiniteRank (L i)] :
    IsFiniteRank (FiniteSum n L) := by
  induction n with
  | zero =>
      let := isFiniteRank_trivial (X := X) 0
      exact (finiteSumZeroIso L).symm.isFiniteRank
  | succ n ih =>
      let := ih (fun i ↦ L i.succ)
      let := isFiniteRank_sum (E := L 0) (F := FiniteSum n (fun i ↦ L i.succ))
      exact (finiteSumSuccIso n L).symm.isFiniteRank

/-- The rank of this actual finite sum is the sum of the original fiber ranks. -/
theorem finrank_finiteSum (n : ℕ) (L : Fin n → X → Type v)
    [∀ i x, AddCommGroup (L i x)] [∀ i x, Module ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] [∀ i, IsFiniteRank (L i)] (x : X) :
    Module.finrank ℂ (FiniteSum n L x) = ∑ i, Module.finrank ℂ (L i x) := by
  let : ∀ i, FiniteDimensional ℂ (L i x) := fun i ↦ finite_fiber (E := L i) x
  exact Module.finrank_pi_fintype ℂ

/-- Isomorphisms of the specified coordinates give an isomorphism of the actual finite sums. -/
def Iso.finiteSum {n : ℕ} {L M : Fin n → X → Type v}
    [∀ i x, AddCommGroup (L i x)] [∀ i x, Module ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))]
    [∀ i x, AddCommGroup (M i x)] [∀ i x, Module ℂ (M i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (M i))]
    (e : ∀ i, Iso (L i) (M i)) : Iso (FiniteSum n L) (FiniteSum n M) where
  linearEquiv x := LinearEquiv.piCongrRight (fun i ↦ (e i).linearEquiv x)
  continuous_total := by
    have hc := continuous_finiteSum_coordinates n L
    apply continuous_induced_rng.mpr
    exact hc.fst.prodMk (continuous_pi (fun i ↦
      (e i).continuous_total.comp ((continuous_apply i).comp hc.snd)))
  continuous_symm := by
    have hc := continuous_finiteSum_coordinates n M
    apply continuous_induced_rng.mpr
    exact hc.fst.prodMk (continuous_pi (fun i ↦
      (e i).continuous_symm.comp ((continuous_apply i).comp hc.snd)))

/-- Pullback commutes with this actual finite sum by the identity on every vector. -/
def finiteSumPullbackIso {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
    (n : ℕ) (L : Fin n → X → Type v)
    [∀ i x, AddCommGroup (L i x)] [∀ i x, Module ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] :
    Iso ((f : Y → X) *ᵖ (FiniteSum n L))
      (FiniteSum n (fun i ↦ (f : Y → X) *ᵖ (L i))) where
  linearEquiv _ := LinearEquiv.refl ℂ _
  continuous_total := by
    have hc := (continuous_finiteSum_coordinates n L).comp
      (Pullback.continuous_lift Unit (FiniteSum n L) f)
    apply continuous_induced_rng.mpr
    refine (Pullback.continuous_proj Unit (FiniteSum n L) f).prodMk
      (continuous_pi (fun i ↦ ?_))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (L i) f).continuous_iff]
    exact (Pullback.continuous_proj Unit (FiniteSum n L) f).prodMk
      ((continuous_apply i).comp hc.snd)
  continuous_symm := by
    have hc := continuous_finiteSum_coordinates n (fun i ↦ (f : Y → X) *ᵖ (L i))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (FiniteSum n L) f).continuous_iff]
    refine hc.fst.prodMk ?_
    apply continuous_induced_rng.mpr
    exact (f.continuous.comp hc.fst).prodMk (continuous_pi (fun i ↦
      (Pullback.continuous_lift Unit (L i) f).comp ((continuous_apply i).comp hc.snd)))

/-- The sum metric is the orthogonal sum of precisely the supplied coordinate forms. -/
def ContinuousHermitianMetric.finiteSum {n : ℕ} {L : Fin n → X → Type v}
    [∀ i x, AddCommGroup (L i x)] [∀ i x, Module ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))]
    (h : ∀ i, ContinuousHermitianMetric (L i)) :
    ContinuousHermitianMetric (FiniteSum n L) where
  toCore x :=
    { inner := fun v w ↦ ∑ i, ((h i).toCore x).inner (v i) (w i)
      conj_inner_symm v w := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ ↦ ((h i).toCore x).conj_inner_symm _ _)
      re_inner_nonneg v := by
        rw [map_sum]
        exact Finset.sum_nonneg (fun i _ ↦ ((h i).toCore x).re_inner_nonneg _)
      add_left v w z := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ ↦ ((h i).toCore x).add_left _ _ _)
      smul_left v w c := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ ↦ ((h i).toCore x).smul_left _ _ _)
      definite v hv := by
        -- Nonnegative summands force every coordinate norm to vanish.
        have hs := congrArg Complex.re hv
        simp only [Complex.re_sum, Complex.zero_re] at hs
        have hz := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i (_ : i ∈ Finset.univ) ↦ ((h i).toCore x).re_inner_nonneg (v i))).mp hs
        funext i
        apply ((h i).toCore x).definite
        apply Complex.ext
        · exact hz i (Finset.mem_univ i)
        · have hi := congrArg Complex.im (((h i).toCore x).conj_inner_symm (v i) (v i))
          change -_ = _ at hi
          change _ = 0
          linarith }
  continuous_pairing := by
    -- Each original pairing is continuous after taking its two actual coordinates.
    have hleft := (continuous_finiteSum_coordinates n L).comp
      (continuous_sum_fst (E := FiniteSum n L) (F := FiniteSum n L))
    have hright := (continuous_finiteSum_coordinates n L).comp
      (continuous_sum_snd (E := FiniteSum n L) (F := FiniteSum n L))
    change Continuous (fun z : TotalSpace Unit (FiniteSum n L ×ᵇ FiniteSum n L) ↦
      ∑ i, ((h i).toCore z.proj).inner (z.snd.1 i) (z.snd.2 i))
    apply continuous_finsetSum
    intro i _
    have hi : Continuous (fun z : TotalSpace Unit (FiniteSum n L ×ᵇ FiniteSum n L) ↦
        (⟨z.proj, z.snd.1 i, z.snd.2 i⟩ : TotalSpace Unit (L i ×ᵇ L i))) := by
      apply continuous_induced_rng.mpr
      exact ((continuous_apply i).comp hleft.snd).prodMk
        ((continuous_apply i).comp hright.snd)
    exact (h i).continuous_pairing.comp hi
  isFiniteRank := by
    let : ∀ i, IsFiniteRank (L i) := fun i ↦ (h i).isFiniteRank
    exact isFiniteRank_finiteSum n L

end AtiyahSinger.ComplexBundle

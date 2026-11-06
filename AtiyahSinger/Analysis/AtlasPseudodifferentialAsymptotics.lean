/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialFiltration
public import AtiyahSinger.Analysis.AtlasQuantizationAsymptotics

/-!
# Asymptotic sums on the original locally finite-rank bundles

Public module ID: M0280.

A02: a sequence of actual atlas pseudodifferential operators with orders
strictly decreasing to minus infinity has one actual asymptotic sum. All
finite-order remainders retain the same sum and the same original sequence
of section maps. Two such sums differ by the existing all-order Sobolev
smoothing predicate. No operator-norm convergence of the sequence is claimed.

Sources: Spin Geometry III.3.4, p.179, with the finite coordinate assembly
of III.3.15--3.19, pp.186--188. These are the standard global consequences
of local symbol asymptotic summation, stated for the project's original
locally finite-rank bundle atlases. They do not require a homogeneous
principal representative, a global common rank or a chosen density.
A fixed atlas quantization presentation gives asymptotic summation by principal-class
recursion. Uniqueness follows from the established all-order intersection.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 30

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

/-- Decreasing-order actual atlas operators have one asymptotic sum with every remainder. -/
theorem exists_atlasPseudodifferential_expansion (m : ℕ → ℝ) (hm : StrictAnti m)
    (hlim : Tendsto m atTop atBot)
    (terms : ℕ → (A.smoothSections →ₗ[ℂ] B.smoothSections))
    (hterms : ∀ j : ℕ, IsAtlasPseudodifferentialOperator A B (m j) (terms j)) :
    ∃ Q : AtlasPseudodifferentialOperator A B (m 0),
      ∀ N : ℕ, IsAtlasPseudodifferentialOperator A B (m N)
        (Q.toLinearMap - ∑ j ∈ Finset.range N, terms j) := by
  /- Use the principal-symbol exact sequence in one fixed quantization presentation.
  Integer order levels group all original terms already above that level. At each
  stage quantize the principal class of the remaining discrepancy; exactness lowers
  it by one order. Borel summation in the fixed finite presentation then sums these
  corrections. Comparing at a sufficiently low integer level recovers every original
  partial sum, including nonintegral and arbitrarily close prescribed orders. -/
  classical
  obtain ⟨C⟩ := nonempty_atlasQuantizationPresentation A B
  let orders : ℕ → ℝ := fun k ↦ m 0 - k
  have horders : StrictAnti orders := by
    intro i j hij
    exact sub_lt_sub_left (Nat.cast_lt.mpr hij) _
  have hordersLim : Tendsto orders atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    obtain ⟨K, hK⟩ := exists_nat_ge (m 0 - b)
    filter_upwards [eventually_ge_atTop K] with k hk
    have hKk : (K : ℝ) ≤ k := Nat.cast_le.mpr hk
    dsimp [orders]
    linarith
  -- Group the original sequence by integer order, without discarding any of its terms.
  have hex (k : ℕ) : ∃ j : ℕ, m j ≤ orders k :=
    (hlim.eventually (eventually_le_atBot (orders k))).exists
  let cutoff (k : ℕ) : ℕ := Nat.find (hex k)
  have hcutoff (k : ℕ) : m (cutoff k) ≤ orders k := Nat.find_spec (hex k)
  have hcutoffMono : Monotone cutoff := by
    intro i j hij
    exact Nat.find_min' (hex i) ((hcutoff j).trans (horders.antitone hij))
  have hcutoffZero : cutoff 0 = 0 :=
    Nat.eq_zero_of_le_zero (Nat.find_min' (hex 0) (by simp [orders]))
  let sectionMap := A.smoothSections →ₗ[ℂ] B.smoothSections
  let targets (k : ℕ) : sectionMap := ∑ j ∈ Finset.range (cutoff k), terms j
  have hinterval (i j : ℕ) (hij : i ≤ j) (l : ℝ) (hl : m i ≤ l) :
      IsAtlasPseudodifferentialOperator A B l
        ((∑ k ∈ Finset.range j, terms k) - ∑ k ∈ Finset.range i, terms k) := by
    rw [← Finset.sum_Ico_eq_sub terms hij]
    apply (atlasPseudodifferentialSpace A B l).sum_mem
    intro k hk
    exact IsAtlasPseudodifferentialOperator.mono A B
      ((hm.antitone (Finset.mem_Ico.mp hk).1).trans hl) (hterms k)
  have hincrement (k : ℕ) : IsAtlasPseudodifferentialOperator A B (orders k)
      (targets (k + 1) - targets k) :=
    hinterval (cutoff k) (cutoff (k + 1)) (hcutoffMono (Nat.le_succ k))
      (orders k) (hcutoff k)
  -- Each recursive state retains the exact accumulated section map and its discrepancy.
  let State (k : ℕ) := {R : sectionMap //
    IsAtlasPseudodifferentialOperator A B (orders k) (targets k - R)}
  have hstep (k : ℕ) (R : State k) :
      ∃ a : atlasGlobalSymbolSpace A B (orders k),
        IsAtlasPseudodifferentialOperator A B (orders (k + 1))
          (targets (k + 1) - (R.val + C.toLinearMap a)) := by
    have hresidual : IsAtlasPseudodifferentialOperator A B (orders k)
        (targets (k + 1) - R.val) := by
      have h := (atlasPseudodifferentialSpace A B (orders k)).add_mem
        (hincrement k) R.property
      change IsAtlasPseudodifferentialOperator A B (orders k) _ at h
      simpa only [sub_add_sub_cancel] using h
    let P : AtlasPseudodifferentialOperator A B (orders k) :=
      ⟨targets (k + 1) - R.val, hresidual⟩
    obtain ⟨a, ha⟩ := Quotient.exists_rep P.principalSymbol
    change atlasGlobalPrincipalSymbolClass A B (orders k) a = P.principalSymbol at ha
    have hclass : P.principalSymbol = (C.quantize a).principalSymbol := by
      rw [C.principalSymbol_quantize a, ha]
    have hlow :=
      (AtlasPseudodifferentialOperator.principalSymbol_eq_iff A B P (C.quantize a)).mp hclass
    refine ⟨a, ?_⟩
    have horder : orders (k + 1) = orders k - 1 := by
      simp only [orders, Nat.cast_add, Nat.cast_one]
      ring
    rw [horder]
    simpa only [P, AtlasQuantizationPresentation.quantize, sub_add_eq_sub_sub] using hlow
  choose correction hcorrection using hstep
  let initial : State 0 := ⟨0, by
    change IsAtlasPseudodifferentialOperator A B (orders 0) (targets 0 - 0)
    simp only [targets, hcutoffZero, Finset.range_zero, Finset.sum_empty, sub_self]
    exact (atlasPseudodifferentialSpace A B (orders 0)).zero_mem⟩
  let states : (k : ℕ) → State k := fun k ↦ Nat.rec initial
    (fun j R ↦ ⟨R.val + C.toLinearMap (correction j R), hcorrection j R⟩) k
  let symbols (k : ℕ) : atlasGlobalSymbolSpace A B (orders k) :=
    correction k (states k)
  have hsum (k : ℕ) : (states k).val =
      ∑ j ∈ Finset.range k, C.toLinearMap (symbols j) := by
    induction k with
    | zero => rfl
    | succ k hk =>
      change (states k).val + C.toLinearMap (symbols k) = _
      rw [hk, Finset.sum_range_succ]
  -- Sum only symbols in the same fixed finite presentation; no operator norm series is used.
  obtain ⟨Q, hQ⟩ := AtlasQuantizationPresentation.exists_pseudodifferential_expansion
    A B C orders horders hordersLim symbols
  let Q' : AtlasPseudodifferentialOperator A B (m 0) :=
    ⟨Q.toLinearMap, by simpa only [orders, Nat.cast_zero, sub_zero] using
      Q.isPseudodifferentialOperator⟩
  refine ⟨Q', ?_⟩
  intro N
  obtain ⟨k, hk⟩ := (hordersLim.eventually (eventually_lt_atBot (m N))).exists
  have hNk : N ≤ cutoff k := by
    by_contra h
    have hless : cutoff k < N := Nat.lt_of_not_ge h
    have hmN := hm hless
    linarith [hcutoff k]
  have happrox : IsAtlasPseudodifferentialOperator A B (orders k)
      (Q.toLinearMap - targets k) := by
    have hs := (states k).property
    rw [hsum] at hs
    have hneg := (atlasPseudodifferentialSpace A B (orders k)).neg_mem hs
    have h := (atlasPseudodifferentialSpace A B (orders k)).add_mem (hQ k) hneg
    change IsAtlasPseudodifferentialOperator A B (orders k) _ at h
    simpa only [neg_sub, sub_add_sub_cancel] using h
  have htail := hinterval N (cutoff k) hNk (m N) le_rfl
  have h := (atlasPseudodifferentialSpace A B (m N)).add_mem
    (IsAtlasPseudodifferentialOperator.mono A B hk.le happrox) htail
  change IsAtlasPseudodifferentialOperator A B (m N) _ at h
  simpa only [targets, sub_add_sub_cancel, Q'] using h

/-- Two asymptotic sums of the same actual sequence differ by an all-order smoothing map. -/
theorem isAtlasSmoothingOperator_sub_of_atlasPseudodifferential_expansion
    (m : ℕ → ℝ) (hlim : Tendsto m atTop atBot)
    (terms : ℕ → (A.smoothSections →ₗ[ℂ] B.smoothSections))
    (Q Q' : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (hQ : ∀ N : ℕ, IsAtlasPseudodifferentialOperator A B (m N)
      (Q - ∑ j ∈ Finset.range N, terms j))
    (hQ' : ∀ N : ℕ, IsAtlasPseudodifferentialOperator A B (m N)
      (Q' - ∑ j ∈ Finset.range N, terms j)) :
    IsAtlasSmoothingOperator A B (Q - Q') := by
  /- Stage 1: subtract the two actual order-m(N) remainder maps at the
  same N. Closure of the order submodule and exact cancellation of their
  identical finite partial sums put Q-Q' in order m(N).
  Stage 2: because m tends to minus infinity, for each real order l some
  m(N) is at most l. Order monotonicity puts that same difference Q-Q'
  in every real order. The intersection characterization then supplies
  its bounded extension between every pair of original Sobolev spaces.
  Neither monotonicity of m nor membership of the individual terms is
  required for uniqueness once these exact remainder hypotheses hold. -/
  classical
  apply (isAtlasSmoothingOperator_iff_forall_isAtlasPseudodifferentialOperator A B _).2
  intro l
  -- Both remainders use this same cofinal index and hence the same finite partial sum.
  obtain ⟨N, hN⟩ := (hlim.eventually (Filter.eventually_le_atBot l)).exists
  have h₁ := IsAtlasPseudodifferentialOperator.mono A B hN (hQ N)
  have h₂ := IsAtlasPseudodifferentialOperator.mono A B hN (hQ' N)
  have hd := (atlasPseudodifferentialSpace A B l).sub_mem h₁ h₂
  have hcancel : (Q - ∑ j ∈ Finset.range N, terms j) -
      (Q' - ∑ j ∈ Finset.range N, terms j) = Q - Q' := by abel
  -- Exact cancellation preserves the original difference at every real order.
  change IsAtlasPseudodifferentialOperator A B l _ at hd
  rwa [hcancel] at hd

end AtiyahSinger

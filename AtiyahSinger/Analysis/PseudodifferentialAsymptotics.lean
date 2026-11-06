/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialRegularity
public import AtiyahSinger.Analysis.QuantizationAsymptotics
public import AtiyahSinger.Analysis.SymbolExistence

/-!
# Asymptotic summation of actual global pseudodifferential operators

Public module ID: M0886.

SR01/A04: globalize SG III.3.4 through the finite chart calculus of III.3.15--3.19.
The sequence consists of actual section maps, and the remainders keep those same
maps. An asymptotic sum is not asserted to converge in an operator norm.
This is the summation step used in the parametrix recursion of III.4.3--4.7.
Theorems below are project-derived global interfaces, not additional numbered lemmas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

/-- A sequence of decreasing-order global PDOs has one asymptotic sum with all remainders. -/
theorem exists_pseudodifferential_expansion (m : ℕ → ℝ) (hm : StrictAnti m)
    (hlim : Tendsto m atTop atBot)
    (terms : ℕ → (smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F))
    (hterms : ∀ j : ℕ, IsPseudodifferentialOperator E F μ (m j) (terms j)) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (m 0),
      ∀ N : ℕ, IsPseudodifferentialOperator E F μ (m N)
        (Q.toLinearMap - ∑ j ∈ Finset.range N, terms j) := by
  /- Use the principal-symbol exact sequence in one fixed quantization presentation.
  Integer order levels group all original terms already above that level. At each
  stage quantize the principal class of the remaining discrepancy; exactness lowers
  it by one order. Borel summation in the fixed finite presentation then sums these
  corrections. Comparing at a sufficiently low integer level recovers every original
  partial sum, including nonintegral and arbitrarily close prescribed orders. -/
  classical
  obtain ⟨A⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q)
    (E := E) (F := F)
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
  let sectionMap := smoothSections (n := n) (r := r) E →ₗ[ℂ]
    smoothSections (n := n) (r := q) F
  let targets (k : ℕ) : sectionMap := ∑ j ∈ Finset.range (cutoff k), terms j
  have hinterval (i j : ℕ) (hij : i ≤ j) (l : ℝ) (hl : m i ≤ l) :
      IsPseudodifferentialOperator E F μ l
        ((∑ k ∈ Finset.range j, terms k) - ∑ k ∈ Finset.range i, terms k) := by
    rw [← Finset.sum_Ico_eq_sub terms hij]
    apply (pseudodifferentialSpace E F μ l).sum_mem
    intro k hk
    exact (hterms k).mono ((hm.antitone (Finset.mem_Ico.mp hk).1).trans hl) _
  have hincrement (k : ℕ) : IsPseudodifferentialOperator E F μ (orders k)
      (targets (k + 1) - targets k) :=
    hinterval (cutoff k) (cutoff (k + 1)) (hcutoffMono (Nat.le_succ k))
      (orders k) (hcutoff k)
  -- Each recursive state retains the exact accumulated section map and its discrepancy.
  let State (k : ℕ) := {R : sectionMap //
    IsPseudodifferentialOperator E F μ (orders k) (targets k - R)}
  have hstep (k : ℕ) (R : State k) :
      ∃ a : globalSymbolSpace (n := n) (r := r) (q := q) E F (orders k),
        IsPseudodifferentialOperator E F μ (orders (k + 1))
          (targets (k + 1) - (R.val + A.toLinearMap a)) := by
    have hresidual : IsPseudodifferentialOperator E F μ (orders k)
        (targets (k + 1) - R.val) := by
      have h := IsPseudodifferentialOperator.add (orders k) _ _ (hincrement k) R.property
      simpa only [sub_add_sub_cancel] using h
    let P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (orders k) :=
      ⟨targets (k + 1) - R.val, hresidual⟩
    obtain ⟨a, ha⟩ := globalPrincipalSymbolClass_surjective E F (orders k) P.principalSymbol
    have hclass : P.principalSymbol = (A.quantize μ a).principalSymbol := by
      rw [A.principalSymbol_quantize μ a, ha]
    have hlow := (P.principalSymbol_eq_iff (A.quantize μ a)).mp hclass
    refine ⟨a, ?_⟩
    have horder : orders (k + 1) = orders k - 1 := by
      simp only [orders, Nat.cast_add, Nat.cast_one]
      ring
    rw [horder]
    simpa only [P, QuantizationPresentation.quantize, sub_add_eq_sub_sub] using hlow
  choose correction hcorrection using hstep
  let initial : State 0 := ⟨0, by
    change IsPseudodifferentialOperator E F μ (orders 0) (targets 0 - 0)
    simp only [targets, hcutoffZero, Finset.range_zero, Finset.sum_empty, sub_self]
    exact isPseudodifferentialOperator_zero E F μ (orders 0)⟩
  let states : (k : ℕ) → State k := fun k ↦ Nat.rec initial
    (fun j R ↦ ⟨R.val + A.toLinearMap (correction j R), hcorrection j R⟩) k
  let symbols (k : ℕ) : globalSymbolSpace (n := n) (r := r) (q := q) E F (orders k) :=
    correction k (states k)
  have hsum (k : ℕ) : (states k).val =
      ∑ j ∈ Finset.range k, A.toLinearMap (symbols j) := by
    induction k with
    | zero => rfl
    | succ k hk =>
      change (states k).val + A.toLinearMap (symbols k) = _
      rw [hk, Finset.sum_range_succ]
  -- Sum only symbols in the same fixed finite presentation; no operator norm series is used.
  obtain ⟨Q, hQ⟩ := A.exists_pseudodifferential_expansion μ orders horders hordersLim symbols
  let Q' : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (m 0) :=
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
  have happrox : IsPseudodifferentialOperator E F μ (orders k)
      (Q.toLinearMap - targets k) := by
    have hs := (states k).property
    rw [hsum] at hs
    have hneg := IsPseudodifferentialOperator.smul (orders k) (-1) _ hs
    have h := IsPseudodifferentialOperator.add (orders k) _ _ (hQ k) hneg
    simpa only [neg_one_smul, neg_sub, sub_add_sub_cancel] using h
  have htail := hinterval N (cutoff k) hNk (m N) le_rfl
  have h := IsPseudodifferentialOperator.add (m N) _ _ (happrox.mono hk.le _) htail
  simpa only [targets, sub_add_sub_cancel, Q'] using h

/-- Any two asymptotic sums of the same actual operator sequence differ by a smooth kernel. -/
theorem isSmoothingOperator_sub_of_pseudodifferential_expansion (m : ℕ → ℝ)
    (hlim : Tendsto m atTop atBot)
    (terms : ℕ → (smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F))
    (Q Q' : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (hQ : ∀ N : ℕ, IsPseudodifferentialOperator E F μ (m N)
      (Q - ∑ j ∈ Finset.range N, terms j))
    (hQ' : ∀ N : ℕ, IsPseudodifferentialOperator E F μ (m N)
      (Q' - ∑ j ∈ Finset.range N, terms j)) : IsSmoothingOperator μ (Q - Q') := by
  /- Subtract the two remainders at the same N; the finite partial sums cancel
  exactly as section maps. The difference has order m(N) for every N. Cofinality
  at minus infinity and order monotonicity give every real order. Choose smooth
  bundle presentations and apply the established all-order/smooth-kernel criterion.
  The smooth kernel represents this fixed difference, not a sequence of different maps. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ (Q - Q') A B).mpr
  intro l
  -- Cofinality chooses one common truncation for both original remainders.
  obtain ⟨N, hN⟩ := (hlim.eventually (Filter.eventually_le_atBot l)).exists
  have hleft := (hQ N).mono hN _
  have hright := (hQ' N).mono hN _
  have hsub := IsPseudodifferentialOperator.add l _ _ hleft
    (IsPseudodifferentialOperator.smul l (-1) _ hright)
  -- Only the same finite sum cancels; the resulting operator is the specified difference.
  have heq : (Q - ∑ j ∈ Finset.range N, terms j) +
      (-1 : ℂ) • (Q' - ∑ j ∈ Finset.range N, terms j) = Q - Q' := by
    rw [neg_one_smul]
    abel
  rwa [heq] at hsub

end AtiyahSinger

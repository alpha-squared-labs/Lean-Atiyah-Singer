/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.FullSymbolEllipticity
public import AtiyahSinger.Analysis.LocalComposition

/-!
# One local two-sided parametrix on each compact coordinate window

Public module ID: M0791.

SG III.4.3--4.5, with the compact-local full-symbol inverse condition
of Taylor III.1.1--1.5. The original symbol is defined on an arbitrary
open coordinate domain U. It need not extend smoothly across its boundary
or satisfy any uniform spatial estimate over U. A compact K inside U
admits an outer cutoff rho equal to one near K. Its zero-extended symbol
has the existing continuous Schwartz realization P.

One actual Schwartz operator Q of order -m then inverts P locally on
the plateau of rho. Every inner cutoff chi supported in that plateau
gives two exact operator identities: chi(QP-I) and chi(PQ-I) are the
quantizations of compactly supported smoothing symbols. The same Q
works for every chi; the smoothing remainders may depend on chi.
Q itself has both operator-support conditions in one compact subset
of U. Output-symbol compactness alone is not used as operator support.

The inner cutoff multiplies each whole residual. In particular this
does not claim the generally false simultaneous identities QP=chi I+R
and PQ=chi I+S for a nonconstant chi. No global parametrix on a noncompact
manifold, uniform estimates at infinity, or global Fredholm property is
asserted. This is the local version in coordinate charts and bundle
frames, with independent local source and target ranks. The proof uses full-symbol
inversion,
fixed-support asymptotic correction and the exact local smoothing ideal.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap

variable {n r q : ℕ}

/-- Proper localization preserves the same leading left and right inverse on the window. -/
private theorem exists_proper_first_inverse_symbols {n r q : ℕ}
    (m : ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (p : SymbolFunction n r q) (hp : IsSymbol U m p) (he : IsEllipticFullSymbol U m p)
    (θ ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ) (hθU : tsupport θ ⊆ U)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hone : ∀ x ∈ tsupport θ, ψ x = 1) :
    ∃ (a : SymbolFunction n r q) (b : SymbolFunction n q r),
      ∃ (ha : IsSymbol Set.univ m a) (hb : IsSymbol Set.univ (-m) b)
        (hca : HasCompactSupport a) (hcb : HasCompactSupport b),
        tsupport a ⊆ U ∧ tsupport b ⊆ U ∧
          ∃ L : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact L ∧ L ⊆ U ∧ tsupport θ ⊆ L ∧
              HasOperatorSupport L (quantizeSchwartz m a ha hca) ∧
              HasOperatorSupport L (quantizeSchwartz (-m) b hb hcb) ∧
              HasCompactSmoothingSchwartzSymbol
                (quantizeSchwartz m (zeroExtendedSymbol U ψ p)
                    (isSymbol_zeroExtendedSymbol U hU m ψ hψ hcψ hψU p hp)
                    (hasCompactSupport_zeroExtendedSymbol U ψ p hcψ) -
                  quantizeSchwartz m a ha hca) ∧
              IsSymbol Set.univ (-1)
                (symbolComp b a - zeroExtendedSymbol Set.univ θ (besselSymbol n r 0)) ∧
              IsSymbol Set.univ (-1)
                (symbolComp a b - zeroExtendedSymbol Set.univ θ (besselSymbol n q 0)) := by
  /- One fixed compact window admits left and right full-symbol inverses modulo smoothing. -/
  have exists_compact_inverse_symbols {n r q : ℕ}
      (m : ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
      (p : SymbolFunction n r q) (hp : IsSymbol U m p) (he : IsEllipticFullSymbol U m p)
      (θ ψ : EuclideanSpace ℝ (Fin n) → ℝ)
      (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ) (hθU : tsupport θ ⊆ U)
      (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
      (hone : ∀ x ∈ tsupport θ, ψ x = 1) :
      ∃ b : SymbolFunction n q r,
        IsSymbol Set.univ (-m) b ∧ HasCompactSupport b ∧ tsupport b ⊆ U ∧
          IsSmoothingSymbol Set.univ
            (symbolComp b (zeroExtendedSymbol U ψ p) -
              zeroExtendedSymbol Set.univ θ (besselSymbol n r 0)) ∧
          IsSmoothingSymbol Set.univ
            (symbolComp (zeroExtendedSymbol U ψ p) b -
              zeroExtendedSymbol Set.univ θ (besselSymbol n q 0)) := by
    -- The compact window supplies one radius for the actual inverse and ellipticity.
    obtain ⟨b₀, hb₀, hinv⟩ := exists_inverse_symbol_of_isEllipticFullSymbol hU p hp he
    obtain ⟨R, hR, hactual⟩ := hinv (tsupport θ) hθU hcθ
    obtain ⟨S, C, hS, hC, hbound⟩ := he (tsupport θ) hθU hcθ
    let b := zeroExtendedSymbol U θ b₀
    let a := zeroExtendedSymbol U ψ p
    let i (s : ℕ) := zeroExtendedSymbol Set.univ θ (besselSymbol n s 0)
    have hb := isSymbol_zeroExtendedSymbol U hU (-m) θ hθ hcθ hθU b₀ hb₀
    have hcb := hasCompactSupport_zeroExtendedSymbol U θ b₀ hcθ
    have ha := isSymbol_zeroExtendedSymbol U hU m ψ hψ hcψ hψU p hp
    have hi (s : ℕ) : IsSymbol Set.univ 0 (i s) :=
      isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 0 θ hθ hcθ (Set.subset_univ _)
        (besselSymbol n s 0) (isSymbol_besselSymbol n s 0)
    have hleft : IsSymbol Set.univ 0 (symbolComp b a) := by
      simpa only [neg_add_cancel] using hb.symbolComp isOpen_univ ha
    have hright : IsSymbol Set.univ 0 (symbolComp a b) := by
      simpa only [add_neg_cancel] using ha.symbolComp isOpen_univ hb
    have hsmoothL : ContDiffOn ℝ ∞
        (Function.uncurry (symbolComp b a - i r)) (Set.univ ×ˢ Set.univ) :=
      hleft.1.sub (hi r).1
    have hsmoothR : ContDiffOn ℝ ∞
        (Function.uncurry (symbolComp a b - i q)) (Set.univ ×ˢ Set.univ) :=
      hright.1.sub (hi q).1
    -- Both remainders vanish at high frequency; no global inverse radius on U is needed.
    have hvanish (x ξ : EuclideanSpace ℝ (Fin n)) (hξ : max R S ≤ ‖ξ‖) :
        (symbolComp b a - i r) x ξ = 0 ∧ (symbolComp a b - i q) x ξ = 0 := by
      by_cases hx : x ∈ tsupport θ
      · have hxU := hθU hx
        have hinv' := hactual x hx ξ ((le_max_left _ _).trans hξ)
        have he' := (hbound x hx ξ ((le_max_right _ _).trans hξ)).1
        have hbval : b x ξ = (θ x : ℂ) • (p x ξ).inverse := by
          rw [show b = zeroExtendedSymbol U θ b₀ from rfl,
            zeroExtendedSymbol_apply_of_mem U θ b₀ x ξ hxU, hinv']
        have haval : a x ξ = p x ξ := by
          rw [show a = zeroExtendedSymbol U ψ p from rfl,
            zeroExtendedSymbol_apply_of_mem U ψ p x ξ hxU, hone x hx,
            Complex.ofReal_one, one_smul]
        have hival (s : ℕ) : i s x ξ = (θ x : ℂ) • ContinuousLinearMap.id ℂ _ := by
          simp only [i, zeroExtendedSymbol_apply_of_mem Set.univ θ _ x ξ (Set.mem_univ x),
            besselSymbol, zero_div, Real.rpow_zero, one_smul]
        constructor
        · simp only [Pi.sub_apply, symbolComp, hbval, haval, hival,
            ContinuousLinearMap.smul_comp, he'.inverse_comp_self, sub_self]
        · simp only [Pi.sub_apply, symbolComp, hbval, haval, hival,
            ContinuousLinearMap.comp_smul, he'.self_comp_inverse, sub_self]
      · have hz : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
        have hbzero : b x ξ = 0 := by
          by_cases hxU : x ∈ U
          · simp only [b, zeroExtendedSymbol_apply_of_mem U θ b₀ x ξ hxU, hz,
              Complex.ofReal_zero, zero_smul]
          · simp [b, zeroExtendedSymbol, hxU]
        have hizero (s : ℕ) : i s x ξ = 0 := by
          simp only [i, zeroExtendedSymbol_apply_of_mem Set.univ θ _ x ξ (Set.mem_univ x),
            hz, Complex.ofReal_zero, zero_smul]
        simp only [Pi.sub_apply, symbolComp, hbzero, hizero,
          ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, sub_self, and_self]
    refine ⟨b, hb, hcb, (tsupport_zeroExtendedSymbol_subset U θ b₀).trans hθU, ?_, ?_⟩
    · exact isSmoothingSymbol_of_frequency_support isOpen_univ _ (max R S) hsmoothL
        (fun x _ ξ hξ ↦ (hvanish x ξ hξ).1)
    · exact isSmoothingSymbol_of_frequency_support isOpen_univ _ (max R S) hsmoothR
        (fun x _ ξ hξ ↦ (hvanish x ξ hξ).2)
  obtain ⟨b₀, hb₀, hcb₀, hb₀U, hleft, hright⟩ :=
    exists_compact_inverse_symbols m U hU p hp he θ ψ hθ hcθ hθU hψ hcψ hψU hone
  let a₀ := zeroExtendedSymbol U ψ p
  have ha₀ := isSymbol_zeroExtendedSymbol U hU m ψ hψ hcψ hψU p hp
  have hca₀ := hasCompactSupport_zeroExtendedSymbol U ψ p hcψ
  obtain ⟨a, ha, hca, haU, K, hK, hKU, hKa, hda, hdas⟩ :=
    exists_proper_quantization_mod_smoothing m a₀ ha₀ hca₀ U hU
      ((tsupport_zeroExtendedSymbol_subset U ψ p).trans hψU)
  obtain ⟨b, hb, hcb, KbU, J, hJ, hJU, hJb, _, hdbs⟩ :=
    exists_proper_quantization_mod_smoothing (-m) b₀ hb₀ hcb₀ U hU hb₀U
  let L := (K ∪ J) ∪ tsupport θ
  have hL : IsCompact L := (hK.union hJ).union hcθ
  have hKL : K ⊆ L := (Set.subset_union_left).trans Set.subset_union_left
  have hJL : J ⊆ L := (Set.subset_union_right).trans Set.subset_union_left
  refine ⟨a, b, ha, hb, hca, hcb, haU, KbU, L, hL,
    Set.union_subset (Set.union_subset hKU hJU) hθU, Set.subset_union_right,
    hKa.mono hKL, hJb.mono hJL, hda, ?_, ?_⟩
  · -- The changed first-inverse symbol and the changed original symbol each cost one order.
    have h₁ : IsSymbol Set.univ (-1) (symbolComp ((-1 : ℂ) • (b₀ - b)) a) := by
      convert ((hdbs (-m - 1)).smul isOpen_univ (-1)).symbolComp isOpen_univ ha using 1
      ring
    have h₂ : IsSymbol Set.univ (-1) (symbolComp b₀ ((-1 : ℂ) • (a₀ - a))) := by
      convert hb₀.symbolComp isOpen_univ ((hdas (m - 1)).smul isOpen_univ (-1)) using 1
      ring
    have h := (h₁.add isOpen_univ h₂).add isOpen_univ (hleft (-1))
    convert h using 1
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    simp [symbolComp, a₀]
  · have h₁ : IsSymbol Set.univ (-1) (symbolComp ((-1 : ℂ) • (a₀ - a)) b) := by
      convert ((hdas (m - 1)).smul isOpen_univ (-1)).symbolComp isOpen_univ hb using 1
      ring
    have h₂ : IsSymbol Set.univ (-1) (symbolComp a₀ ((-1 : ℂ) • (b₀ - b))) := by
      convert ha₀.symbolComp isOpen_univ ((hdbs (-m - 1)).smul isOpen_univ (-1)) using 1
      ring
    have h := (h₁.add isOpen_univ h₂).add isOpen_univ (hright (-1))
    convert h using 1
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    simp [symbolComp, a₀]

/-- The local smoothing ideal identifies the two sums and retains one proper two-sided inverse. -/
private theorem exists_proper_local_inverse_of_first_inverse {n r q : ℕ}
    (m : ℝ) (P : LocalSchwartzOperator n r q) (B : LocalSchwartzOperator n q r)
    (hP : HasCompactSchwartzSymbol m P) (hB : HasCompactSchwartzSymbol (-m) B)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hPK : HasOperatorSupport K P) (hBK : HasOperatorSupport K B)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcθ : HasCompactSupport θ) (hθK : tsupport θ ⊆ K)
    (hR : HasCompactSchwartzSymbol (-1)
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ)) - B.comp P))
    (hS : HasCompactSchwartzSymbol (-1)
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (θ x : ℂ)) - P.comp B)) :
    ∃ c : SymbolFunction n q r,
      ∃ (hc : IsSymbol Set.univ (-m) c) (hcc : HasCompactSupport c),
        tsupport c ⊆ U ∧ ∃ L : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact L ∧ K ⊆ L ∧ L ⊆ U ∧
            HasOperatorSupport L (quantizeSchwartz (-m) c hc hcc) ∧
            IsLocallySmoothingSchwartz (interior {x | θ x = 1})
              ((quantizeSchwartz (-m) c hc hcc).comp P -
                SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ))) ∧
            IsLocallySmoothingSchwartz (interior {x | θ x = 1})
              (P.comp (quantizeSchwartz (-m) c hc hcc) -
                SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (θ x : ℂ))) := by
  /- Asymptotic geometric sums improve the first inverses on the fixed local window. -/
  have exists_local_left_right_inverse {n r q : ℕ}
      (m : ℝ) (P : LocalSchwartzOperator n r q) (B : LocalSchwartzOperator n q r)
      (hP : HasCompactSchwartzSymbol m P) (hB : HasCompactSchwartzSymbol (-m) B)
      (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hK : IsCompact K)
      (hKU : K ⊆ U) (hPK : HasOperatorSupport K P) (hBK : HasOperatorSupport K B)
      (θ : EuclideanSpace ℝ (Fin n) → ℝ) (hθ : ContDiff ℝ ∞ θ)
      (hcθ : HasCompactSupport θ) (hθK : tsupport θ ⊆ K)
      (hR : HasCompactSchwartzSymbol (-1)
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ)) - B.comp P))
      (hS : HasCompactSchwartzSymbol (-1)
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (θ x : ℂ)) - P.comp B)) :
      ∃ (a b : SymbolFunction n q r),
        ∃ (ha : IsSymbol Set.univ (-m) a) (hb : IsSymbol Set.univ (-m) b)
          (hca : HasCompactSupport a) (hcb : HasCompactSupport b),
          tsupport a ⊆ U ∧ tsupport b ⊆ U ∧
            IsLocallySmoothingSchwartz (interior {x | θ x = 1})
              ((quantizeSchwartz (-m) a ha hca).comp P -
                SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ))) ∧
            IsLocallySmoothingSchwartz (interior {x | θ x = 1})
              (P.comp (quantizeSchwartz (-m) b hb hcb) -
                SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (θ x : ℂ))) := by
    /- Positive powers of a compact, supported order-minus-one operator have the expected order. -/
    have compact_symbol_pow_succ {n r : ℕ} (R : LocalSchwartzOperator n r r)
        (hR : HasCompactSchwartzSymbol (-1) R)
        (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
        (hRK : HasOperatorSupport K R) (j : ℕ) :
        HasCompactSchwartzSymbol (-((j + 1 : ℕ) : ℝ)) (R ^ (j + 1)) ∧
          HasOperatorSupport K (R ^ (j + 1)) := by
      induction j with
      | zero => simpa only [zero_add, pow_one, Nat.cast_one] using And.intro hR hRK
      | succ j ih =>
        rw [pow_succ, ContinuousLinearMap.mul_def]
        constructor
        · convert ih.1.comp hR K hK hRK using 1
          push_cast
          ring
        · exact ih.2.comp K _ _ hRK
    classical
    let Mr := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ))
    let Mq := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (θ x : ℂ))
    let R := Mr - B.comp P
    let S := Mq - P.comp B
    have hRK : HasOperatorSupport K R :=
      ((compact_symbol_cutoff θ hθ hcθ).2.mono hθK).sub (hBK.comp K B P hPK) hK.isClosed
    have hSK : HasOperatorSupport K S :=
      ((compact_symbol_cutoff θ hθ hcθ).2.mono hθK).sub (hPK.comp K P B hBK) hK.isClosed
    have hpR := compact_symbol_pow_succ R hR K hK hRK
    have hpS := compact_symbol_pow_succ S hS K hK hSK
    let left (j : ℕ) := (R ^ j).comp B
    let right (j : ℕ) := B.comp (S ^ j)
    have hleft (j : ℕ) : HasCompactSchwartzSymbol (-m - j) (left j) ∧
        HasOperatorSupport K (left j) := by
      cases j with
      | zero => simpa [left, ContinuousLinearMap.one_def] using And.intro hB hBK
      | succ j =>
        constructor
        · convert (hpR j).1.comp hB K hK hBK using 1
          push_cast
          ring
        · exact (hpR j).2.comp K _ B hBK
    have hright (j : ℕ) : HasCompactSchwartzSymbol (-m - j) (right j) ∧
        HasOperatorSupport K (right j) := by
      cases j with
      | zero => simpa [right, ContinuousLinearMap.one_def] using And.intro hB hBK
      | succ j =>
        constructor
        · convert hB.comp (hpS j).1 K hK (hpS j).2 using 1
        · exact hBK.comp K B _ (hpS j).2
    let leftSum (N : ℕ) := ∑ j ∈ Finset.range N, left j
    let rightSum (N : ℕ) := ∑ j ∈ Finset.range N, right j
    -- A cutoff need not be idempotent. Keep the finite tails supported away from its plateau.
    have hfiniteL (k : ℕ) : IsLocallySmoothingSchwartz (interior {x | θ x = 1})
        ((leftSum (k + 1)).comp P - Mr + R ^ (k + 1)) := by
      induction k with
      | zero =>
        have heq : (leftSum 1).comp P - Mr + R = 0 := by
          simp [leftSum, left, R, ContinuousLinearMap.one_def]
        simpa only [zero_add, pow_one, heq] using
          (IsLocallySmoothingSchwartz.zero (n := n) (r := r) (s := r)
            (U := interior {x | θ x = 1}))
      | succ k ih =>
        have htail := isLocallySmoothingSchwartz_comp_cutoff_sub (hpR k).1 θ hθ hcθ
        convert ih.add htail using 1
        apply ContinuousLinearMap.ext
        intro u
        simp only [leftSum, Finset.sum_range_succ, left, pow_succ,
          ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, add_apply, sub_apply,
          map_sub, R]
        abel
    have hfiniteR (k : ℕ) : IsLocallySmoothingSchwartz (interior {x | θ x = 1})
        (P.comp (rightSum (k + 1)) - Mq + S ^ (k + 1)) := by
      induction k with
      | zero =>
        have heq : P.comp (rightSum 1) - Mq + S = 0 := by
          simp [rightSum, right, S, ContinuousLinearMap.one_def]
        simpa only [zero_add, pow_one, heq] using
          (IsLocallySmoothingSchwartz.zero (n := n) (r := q) (s := q)
            (U := interior {x | θ x = 1}))
      | succ k ih =>
        have htail := isLocallySmoothingSchwartz_cutoff_comp_sub (S ^ (k + 1)) θ hθ hcθ
        convert ih.add htail using 1
        apply ContinuousLinearMap.ext
        intro u
        simp only [rightSum, Finset.sum_range_succ, right, pow_succ',
          ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, add_apply, sub_apply,
          map_add, map_sub, S]
        abel
    -- Borel summation uses one compact support for every geometric correction.
    obtain ⟨a, ha, hca, haU, harem⟩ := exists_compact_schwartzOperator_expansion
      U K hU hK hKU (-m) left (fun j ↦ (hleft j).1) (fun j ↦ (hleft j).2)
    obtain ⟨b, hb, hcb, hbU, hbrem⟩ := exists_compact_schwartzOperator_expansion
      U K hU hK hKU (-m) right (fun j ↦ (hright j).1) (fun j ↦ (hright j).2)
    refine ⟨a, b, ha, hb, hca, hcb, haU, hbU, ?_, ?_⟩
    · intro χ hχ hcχ hχone
      apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
      intro l
      obtain ⟨k, hk⟩ := exists_nat_ge (-l)
      have hkl : -((k + 1 : ℕ) : ℝ) ≤ l := by
        push_cast
        linarith
      have hcomp : HasCompactSchwartzSymbol (-((k + 1 : ℕ) : ℝ))
          ((quantizeSchwartz (-m) a ha hca - leftSum (k + 1)).comp P) := by
        convert (harem (k + 1)).comp hP K hK hPK using 1
        ring
      have h := (((hcomp.cutoff χ hχ hcχ).add
        ((hfiniteL k χ hχ hcχ hχone).order (-((k + 1 : ℕ) : ℝ)))).sub
          ((hpR k).1.cutoff χ hχ hcχ)).mono hkl
      convert h using 1
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_sub, map_add]
      abel
    · intro χ hχ hcχ hχone
      apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
      intro l
      obtain ⟨k, hk⟩ := exists_nat_ge (-l)
      have hkl : -((k + 1 : ℕ) : ℝ) ≤ l := by
        push_cast
        linarith
      have hcomp : HasCompactSchwartzSymbol (-((k + 1 : ℕ) : ℝ))
          (P.comp (quantizeSchwartz (-m) b hb hcb - rightSum (k + 1))) := by
        convert hP.comp_any (hbrem (k + 1)) using 1
        ring
      have h := (((hcomp.cutoff χ hχ hcχ).add
        ((hfiniteR k χ hχ hcχ hχone).order (-((k + 1 : ℕ) : ℝ)))).sub
          ((hpS k).1.cutoff χ hχ hcχ)).mono hkl
      convert h using 1
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_sub, map_add]
      abel
  obtain ⟨a, b, ha, hb, hca, hcb, haU, _, hleft, hright⟩ :=
    exists_local_left_right_inverse m P B hP hB U K hU hK hKU hPK hBK θ hθ hcθ hθK hR hS
  let QL := quantizeSchwartz (-m) a ha hca
  let QR := quantizeSchwartz (-m) b hb hcb
  let Mr := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ))
  let Mq := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (θ x : ℂ))
  have hQL : HasCompactSchwartzSymbol (-m) QL := ⟨a, ha, hca, rfl⟩
  have hQR : HasCompactSchwartzSymbol (-m) QR := ⟨b, hb, hcb, rfl⟩
  have hER : HasCompactSchwartzSymbol 0 (P.comp QR - Mq) := by
    have hcomp : HasCompactSchwartzSymbol 0 (P.comp QR) := by
      simpa only [add_neg_cancel] using hP.comp_any hQR
    exact hcomp.sub (compact_symbol_cutoff θ hθ hcθ).1
  -- The same plateau acts as the identity modulo local smoothing on both sides.
  have hdiff : IsLocallySmoothingSchwartz (interior {x | θ x = 1}) (QL - QR) := by
    have h₁ := hright.comp_left hQL hER isOpen_interior
    have h₂ := hleft.comp hQR
    have h₃ := isLocallySmoothingSchwartz_comp_cutoff_sub hQL θ hθ hcθ
    have h₄ := isLocallySmoothingSchwartz_cutoff_comp_sub QR θ hθ hcθ
    have h := (((h₁.sub h₂).add h₃).sub h₄).neg
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, neg_apply, map_sub]
    abel
  have hrightL : IsLocallySmoothingSchwartz (interior {x | θ x = 1}) (P.comp QL - Mq) := by
    have h := (hdiff.comp_left hP (hQL.sub hQR) isOpen_interior).add hright
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub]
    abel
  -- Properization changes that one common inverse only by a globally smoothing operator.
  obtain ⟨c, hc, hcc, hcU, J, hJ, hJU, hQcJ, htail, _⟩ :=
    exists_proper_quantization_mod_smoothing (-m) a ha hca U hU haU
  let L := K ∪ J
  refine ⟨c, hc, hcc, hcU, L, hK.union hJ, Set.subset_union_left,
    Set.union_subset hKU hJU, hQcJ.mono Set.subset_union_right, ?_, ?_⟩
  · have hs : IsLocallySmoothingSchwartz (interior {x | θ x = 1})
        ((QL - quantizeSchwartz (-m) c hc hcc).comp P) :=
      IsLocallySmoothingSchwartz.of_smoothing (htail.comp_any hP)
    have h := hleft.sub hs
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply]
    abel
  · have hs : IsLocallySmoothingSchwartz (interior {x | θ x = 1})
        (P.comp (QL - quantizeSchwartz (-m) c hc hcc)) :=
      IsLocallySmoothingSchwartz.of_smoothing (htail.comp_left hP)
    have h := hrightL.sub hs
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    abel

/-- One proper local inverse works on both sides for every inner cutoff. -/
theorem exists_local_two_sided_parametrix
    (m : ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (p : SymbolFunction n r q) (hp : IsSymbol U m p)
    (he : IsEllipticFullSymbol U m p)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
      ∃ (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U),
        K ⊆ interior {x | ρ x = 1} ∧
          ∃ b : SymbolFunction n q r,
            ∃ (hb : IsSymbol Set.univ (-m) b) (hcb : HasCompactSupport b),
              tsupport b ⊆ U ∧
                ∃ L : Set (EuclideanSpace ℝ (Fin n)),
                  IsCompact L ∧ tsupport ρ ⊆ L ∧ L ⊆ U ∧
                    HasOperatorSupport L (quantizeSchwartz (-m) b hb hcb) ∧
                      let P := quantizeSchwartz m (zeroExtendedSymbol U ρ p)
                        (isSymbol_zeroExtendedSymbol U hU m ρ hρ hcρ hρU p hp)
                        (hasCompactSupport_zeroExtendedSymbol U ρ p hcρ)
                      let Q := quantizeSchwartz (-m) b hb hcb
                      ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ,
                        ContDiff ℝ ∞ χ → HasCompactSupport χ →
                          tsupport χ ⊆ interior {x | ρ x = 1} →
                            ∃ (c : SymbolFunction n r r) (d : SymbolFunction n q q),
                              ∃ (hc : IsSmoothingSymbol Set.univ c)
                                (hd : IsSmoothingSymbol Set.univ d)
                                (hcc : HasCompactSupport c) (hcd : HasCompactSupport d),
                                tsupport c ⊆ tsupport χ ∧ tsupport d ⊆ tsupport χ ∧
                                  (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
                                      (fun x ↦ (χ x : ℂ))).comp
                                      (Q.comp P - ContinuousLinearMap.id ℂ _) =
                                    quantizeSchwartz 0 c (hc 0) hcc ∧
                                  (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q))
                                      (fun x ↦ (χ x : ℂ))).comp
                                      (P.comp Q - ContinuousLinearMap.id ℂ _) =
                                    quantizeSchwartz 0 d (hd 0) hcd := by
  /- The leading inverse identity improves the actual operator residual by one order. -/
  have compact_first_inverse_residual {n r q : ℕ}
      (l m : ℝ) (hlm : l + m = 0)
      (p : SymbolFunction n q r) (a : SymbolFunction n r q)
      (hp : IsSymbol Set.univ l p) (ha : IsSymbol Set.univ m a)
      (hcp : HasCompactSupport p) (hca : HasCompactSupport a)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hPK : HasOperatorSupport K (quantizeSchwartz l p hp hcp))
      (hAK : HasOperatorSupport K (quantizeSchwartz m a ha hca))
      (θ : EuclideanSpace ℝ (Fin n) → ℝ) (hθ : ContDiff ℝ ∞ θ)
      (hcθ : HasCompactSupport θ)
      (hfirst : IsSymbol Set.univ (-1)
        (symbolComp p a - zeroExtendedSymbol Set.univ θ (besselSymbol n r 0))) :
      HasCompactSchwartzSymbol (-1)
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ)) -
          (quantizeSchwartz l p hp hcp).comp (quantizeSchwartz m a ha hca)) := by
    obtain ⟨hcprod, hprod⟩ :=
      compact_schwartzOperator_comp_sub_symbolComp l m p a hp ha hcp hca K hK hPK hAK
    have horder : IsSymbol Set.univ 0 (symbolComp p a) := by
      simpa only [hlm] using hp.symbolComp isOpen_univ ha
    have hprod' : HasCompactSchwartzSymbol (-1)
        ((quantizeSchwartz l p hp hcp).comp (quantizeSchwartz m a ha hca) -
          quantizeSchwartz 0 (symbolComp p a) horder hcprod) := by
      simpa only [hlm, zero_sub] using hprod
    let i := zeroExtendedSymbol Set.univ θ (besselSymbol n r 0)
    have hi := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 0 θ hθ hcθ
      (Set.subset_univ _) (besselSymbol n r 0) (isSymbol_besselSymbol n r 0)
    have hci := hasCompactSupport_zeroExtendedSymbol Set.univ θ (besselSymbol n r 0) hcθ
    have hrem := HasCompactSchwartzSymbol.sub_quantize 0 (-1)
      (symbolComp p a) i horder hi hcprod hci hfirst
    have h := (hprod'.add hrem).smul (-1)
    rw [quantizeSchwartz_cutoffIdentity θ hθ hcθ] at h
    convert h using 1
    simp only [neg_one_smul]
    abel
  -- Choose the eventual original localization first, inside two larger plateau windows.
  obtain ⟨ρ, hρ, hcρ, hρU, hρone⟩ := exists_compact_cutoff_one_near K U hK hU hKU
  obtain ⟨θ, hθ, hcθ, hθU, hθone⟩ :=
    exists_compact_cutoff_one_near (tsupport ρ) U hcρ hU hρU
  obtain ⟨ψ, hψ, hcψ, hψU, hψone⟩ :=
    exists_compact_cutoff_one_near (tsupport θ) U hcθ hU hθU
  have hψeq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport θ) : ψ x = 1 :=
    show x ∈ {x | ψ x = 1} from interior_subset (hψone hx)
  obtain ⟨a, b, ha, hb, hca, hcb, _, _, J, hJ, hJU, hθJ, hAJ, hBJ, hdiff, hfirstL,
    hfirstR⟩ := exists_proper_first_inverse_symbols m U hU p hp he θ ψ
      hθ hcθ hθU hψ hcψ hψU hψeq
  let A := quantizeSchwartz m a ha hca
  let B := quantizeSchwartz (-m) b hb hcb
  have hA : HasCompactSchwartzSymbol m A := ⟨a, ha, hca, rfl⟩
  have hB : HasCompactSchwartzSymbol (-m) B := ⟨b, hb, hcb, rfl⟩
  have hR := compact_first_inverse_residual (-m) m (neg_add_cancel m)
    b a hb ha hcb hca J hJ hBJ hAJ θ hθ hcθ hfirstL
  have hS := compact_first_inverse_residual m (-m) (add_neg_cancel m)
    a b ha hb hca hcb J hJ hAJ hBJ θ hθ hcθ hfirstR
  -- One common proper inverse is fixed before any inner cutoff is supplied.
  obtain ⟨qSym, hq, hcq, hqU, L₀, hL₀, _, hL₀U, hQL₀, hleft, hright⟩ :=
    exists_proper_local_inverse_of_first_inverse m A B hA hB U J hU hJ hJU hAJ hBJ
      θ hθ hcθ hθJ hR hS
  let Q := quantizeSchwartz (-m) qSym hq hcq
  have hQ : HasCompactSchwartzSymbol (-m) Q := ⟨qSym, hq, hcq, rfl⟩
  let pψ := zeroExtendedSymbol U ψ p
  have hpψ := isSymbol_zeroExtendedSymbol U hU m ψ hψ hcψ hψU p hp
  have hcpψ := hasCompactSupport_zeroExtendedSymbol U ψ p hcψ
  let Pψ := quantizeSchwartz m pψ hpψ hcpψ
  let pρ := zeroExtendedSymbol U ρ p
  have hpρ := isSymbol_zeroExtendedSymbol U hU m ρ hρ hcρ hρU p hp
  have hcpρ := hasCompactSupport_zeroExtendedSymbol U ρ p hcρ
  let P := quantizeSchwartz m pρ hpρ hcpρ
  let Mρ := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (ρ x : ℂ))
  have hP : HasCompactSchwartzSymbol m P := ⟨pρ, hpρ, hcpρ, rfl⟩
  have hmem (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
      (hx : f x = 1) : x ∈ tsupport f := by
    apply subset_closure
    change f x ≠ 0
    rw [hx]
    exact one_ne_zero
  have hρθ : interior {x | ρ x = 1} ⊆ interior {x | θ x = 1} := by
    intro x hx
    exact hθone (hmem ρ x (show x ∈ {x | ρ x = 1} from interior_subset hx))
  have hψρ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ρ) : ψ x = 1 :=
    hψeq x (hmem θ x (show x ∈ {x | θ x = 1} from interior_subset (hθone hx)))
  -- The original rho-localization differs from the larger proper operator only locally smoothly.
  have hsymbol : pρ = zeroExtendedSymbol Set.univ ρ pψ := by
    funext x ξ
    rw [zeroExtendedSymbol_apply_of_mem Set.univ ρ pψ x ξ (Set.mem_univ x)]
    by_cases hx : x ∈ tsupport ρ
    · rw [show pρ = zeroExtendedSymbol U ρ p from rfl,
        zeroExtendedSymbol_apply_of_mem U ρ p x ξ (hρU hx)]
      simp only [pψ, zeroExtendedSymbol_apply_of_mem U ψ p x ξ (hρU hx),
        hψρ x hx, Complex.ofReal_one, one_smul]
    · have hz : ρ x = 0 := image_eq_zero_of_notMem_tsupport hx
      by_cases hxU : x ∈ U
      · simp only [pρ, zeroExtendedSymbol_apply_of_mem U ρ p x ξ hxU, hz,
          Complex.ofReal_zero, zero_smul]
      · simp [pρ, zeroExtendedSymbol, hxU, hz]
  have hPact : P = Mρ.comp Pψ := by
    rw [show Mρ = SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q))
      (fun x ↦ (ρ x : ℂ)) from rfl,
      ← quantizeSchwartz_zeroExtendedSymbol_univ m pψ hpψ hcpψ ρ hρ hcρ]
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    rw [quantizeSchwartz_apply, quantizeSchwartz_apply, hsymbol]
  have htail : HasCompactSmoothingSchwartzSymbol (P - Mρ.comp A) := by
    have h := hdiff.cutoff ρ hρ hcρ
    rw [hPact]
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rfl
  have hPA : IsLocallySmoothingSchwartz (interior {x | ρ x = 1}) (P - A) := by
    have hs : IsLocallySmoothingSchwartz (interior {x | ρ x = 1}) (P - Mρ.comp A) :=
      IsLocallySmoothingSchwartz.of_smoothing htail
    have h := hs.add (isLocallySmoothingSchwartz_cutoff_comp_sub A ρ hρ hcρ)
    convert h using 1
    abel
  have hunit (s : ℕ) : IsLocallySmoothingSchwartz (interior {x | ρ x = 1})
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (θ x : ℂ)) -
        ContinuousLinearMap.id ℂ _) := by
    have h := (isLocallySmoothingSchwartz_cutoff_comp_sub
      (ContinuousLinearMap.id ℂ (𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s))))
      θ hθ hcθ).mono hρθ
    simpa only [ContinuousLinearMap.comp_id] using h
  have hleftP : IsLocallySmoothingSchwartz (interior {x | ρ x = 1})
      (Q.comp P - ContinuousLinearMap.id ℂ _) := by
    have h := (hPA.comp_left hQ (hP.sub hA) isOpen_interior).add
      ((hleft.mono hρθ).add (hunit r))
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub]
    abel
  have hrightP : IsLocallySmoothingSchwartz (interior {x | ρ x = 1})
      (P.comp Q - ContinuousLinearMap.id ℂ _) := by
    have h := (hPA.comp hQ).add ((hright.mono hρθ).add (hunit q))
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply]
    abel
  refine ⟨ρ, hρ, hcρ, hρU, hρone, qSym, hq, hcq, hqU, L₀ ∪ tsupport ρ,
    hL₀.union hcρ, Set.subset_union_right, Set.union_subset hL₀U hρU,
    hQL₀.mono Set.subset_union_left, ?_⟩
  dsimp only
  intro χ hχ hcχ hχone
  obtain ⟨c, hc, hcc, hcSupp, hcact⟩ :=
    hleftP.exists_supported_symbol isOpen_interior χ hχ hcχ hχone
  obtain ⟨d, hd, hcd, hdSupp, hdact⟩ :=
    hrightP.exists_supported_symbol isOpen_interior χ hχ hcχ hχone
  exact ⟨c, d, hc, hd, hcc, hcd, hcSupp, hdSupp, hcact, hdact⟩

end AtiyahSinger

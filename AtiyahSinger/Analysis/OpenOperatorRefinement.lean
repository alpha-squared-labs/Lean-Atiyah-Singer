/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.FrameChange

import all AtiyahSinger.Analysis.SmoothingKernelSymbol
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compact coordinate refinement for open operator transport

Public module ID: M0830.

A finite refinement of a compact coordinate operator retains its actual action
modulo a genuine compact smoothing symbol. The argument takes place entirely in
the original Euclidean coordinates and imposes no compactness on the source
manifold. Nested input plateaus separate every discarded input from its output
cutoff. This is the local partition argument underlying SG III.3 and III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap Topology

/-- A compact coordinate operator refines into any open cover with a true smoothing remainder. -/
theorem HasCompactSchwartzSymbol.exists_refinement {n r s : ℕ} {m : ℝ}
    {P : LocalSchwartzOperator n r s} (hP : HasCompactSchwartzSymbol m P)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K P)
    {ι : Type*} (U : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ (d : ℕ) (a : Fin d → ι) (χ ρ : Fin d → EuclideanSpace ℝ (Fin n) → ℝ)
        (Q : Fin d → LocalSchwartzOperator n r s),
      (∀ j, ContDiff ℝ ∞ (χ j) ∧ HasCompactSupport (χ j) ∧
        ContDiff ℝ ∞ (ρ j) ∧ HasCompactSupport (ρ j) ∧
        tsupport (χ j) ∪ tsupport (ρ j) ⊆ U (a j) ∧
        tsupport (χ j) ⊆ interior {x | ρ j x = 1} ∧
        Q j = ((SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s))
          (fun x ↦ (χ j x : ℂ))).comp P).comp
            (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
              (fun x ↦ (ρ j x : ℂ))) ∧
        HasCompactSchwartzSymbol m (Q j) ∧
        HasOperatorSupport (tsupport (χ j) ∪ tsupport (ρ j)) (Q j)) ∧
      HasCompactSmoothingSchwartzSymbol (P - ∑ j, Q j) ∧
      HasOperatorSupport K (P - ∑ j, Q j) ∧
      (∀ x ∈ K, ∑ j, χ j x = 1) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  -- Shrink a finite subcover before taking the partition, so every weight is compact.
  choose a ha using fun x : K ↦ Set.mem_iUnion.mp (hcover x.property)
  have hshrink (x : K) : ∃ V : Set X, IsOpen V ∧ x.val ∈ V ∧
      closure V ⊆ U (a x) ∧ IsCompact (closure V) := by
    obtain ⟨V, hV, hxV, hVU, hVc⟩ :=
      exists_open_between_and_isCompact_closure (isCompact_singleton (x := x.val))
      (hU (a x)) (Set.singleton_subset_iff.mpr (ha x))
    exact ⟨V, hV, hxV (Set.mem_singleton _), hVU, hVc⟩
  choose V hV hxV hVU hVc using hshrink
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV
    (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let index : Fin t.card ≃ t := t.equivFin.symm
  let W (j : Fin t.card) := V (index j)
  have hWcover : K ⊆ ⋃ j, W j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [W] using hxy⟩
  obtain ⟨χ, hχsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hK.isClosed W
    (fun j ↦ hV (index j)) hWcover
  have hχ (j : Fin t.card) : ContDiff ℝ ∞ (χ j) := (χ j).contMDiff.contDiff
  have hcχ (j : Fin t.card) : HasCompactSupport (χ j) :=
    (hVc (index j)).of_isClosed_subset (isClosed_tsupport _)
      (fun x hx ↦ subset_closure (hχsub j hx))
  have hsχ (j : Fin t.card) : tsupport (χ j) ⊆ U (a (index j)) :=
    fun x hx ↦ hVU (index j) (subset_closure (hχsub j hx))
  choose ρ hρ hcρ hsρ hρone using fun j : Fin t.card ↦
    exists_compact_cutoff_one_near (tsupport (χ j)) (U (a (index j)))
      (hcχ j) (hU (a (index j))) (hsχ j)
  let A (j : Fin t.card) :=
    SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ j x : ℂ))
  let B (j : Fin t.card) :=
    SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (ρ j x : ℂ))
  let Q (j : Fin t.card) := ((A j).comp P).comp (B j)
  let R (j : Fin t.card) := ((A j).comp P).comp (ContinuousLinearMap.id ℂ _ - B j)
  have hχT (j : Fin t.card) : (fun x ↦ (χ j x : ℂ)).HasTemperateGrowth :=
    ((hcχ j).comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp (hχ j))
  have hρT (j : Fin t.card) : (fun x ↦ (ρ j x : ℂ)).HasTemperateGrowth :=
    ((hcρ j).comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp (hρ j))
  have hA (j : Fin t.card) (u : 𝓢(X, EuclideanSpace ℂ (Fin s))) (x : X) :
      A j u x = (χ j x : ℂ) • u x :=
    SchwartzMap.smulLeftCLM_apply_apply (hχT j) u x
  have hB (j : Fin t.card) (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      B j u x = (ρ j x : ℂ) • u x :=
    SchwartzMap.smulLeftCLM_apply_apply (hρT j) u x
  -- Each omitted input is separated from its output; keep its exact full smoothing symbol.
  have hR (j : Fin t.card) : HasCompactSmoothingSchwartzSymbol (R j) :=
    hasCompactSmoothingSchwartzSymbol_offDiagonal hP (χ j) (ρ j)
      (hχ j) (hcχ j) (hρ j) (hcρ j) (hρone j)
  have hQ (j : Fin t.card) : HasCompactSchwartzSymbol m (Q j) := by
    have h := (hP.cutoff (χ j) (hχ j) (hcχ j)).sub ((hR j).order m)
    convert h using 1
    simp only [R, Q, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    abel
  have hQsupport (j : Fin t.card) :
      HasOperatorSupport (tsupport (χ j) ∪ tsupport (ρ j)) (Q j) := by
    constructor
    · intro u
      apply closure_minimal _ ((isClosed_tsupport _).union (isClosed_tsupport _))
      intro x hx
      apply Or.inl
      by_contra hout
      exact hx (by
        change A j (P (B j u)) x = 0
        rw [hA, image_eq_zero_of_notMem_tsupport hout, Complex.ofReal_zero, zero_smul])
    · intro u hu
      have hzero : B j u = 0 := by
        apply SchwartzMap.ext
        intro x
        rw [hB]
        by_cases hx : x ∈ tsupport (ρ j)
        · rw [image_eq_zero_of_notMem_tsupport
            (fun h ↦ Set.disjoint_left.mp hu h (Or.inr hx)), smul_zero]
          rfl
        · rw [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_smul]
          rfl
      simp only [Q, ContinuousLinearMap.comp_apply, hzero, map_zero]
  -- The original input/output support K is retained as well, even when cutoffs are larger.
  have hQK (j : Fin t.card) : HasOperatorSupport K (Q j) := by
    constructor
    · intro u
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hout
      exact hx (by
        change A j (P (B j u)) x = 0
        rw [hA, image_eq_zero_of_notMem_tsupport
          (fun h ↦ hout (hPK.1 (B j u) h)), smul_zero])
    · intro u hu
      have hb : tsupport (B j u) ⊆ tsupport u := by
        apply closure_minimal _ (isClosed_tsupport _)
        intro x hx
        by_contra hout
        exact hx (by rw [hB, image_eq_zero_of_notMem_tsupport hout, smul_zero])
      simp only [Q, ContinuousLinearMap.comp_apply, hPK.2 _ (hu.mono_left hb), map_zero]
  have hsum : (∑ j, (A j).comp P) = P := by
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    simp only [sum_apply,
      ContinuousLinearMap.comp_apply, hA, ← Finset.sum_smul, ← Complex.ofReal_sum]
    by_cases hx : x ∈ K
    · have hone : ∑ j, χ j x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using χ.sum_eq_one hx
      rw [hone, Complex.ofReal_one, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hPK.1 u h)), smul_zero]
  have herror : (∑ j, R j) = P - ∑ j, Q j := by
    simp only [R, Q, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      Finset.sum_sub_distrib, hsum]
  refine ⟨t.card, fun j ↦ a (index j), fun j ↦ χ j, ρ, Q, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨hχ j, hcχ j, hρ j, hcρ j, Set.union_subset (hsχ j) (hsρ j),
      hρone j, rfl, hQ j, hQsupport j⟩
  · rw [← herror]
    have hfin (t : Finset (Fin t.card)) :
        HasCompactSmoothingSchwartzSymbol (∑ j ∈ t, R j) := by
      induction t using Finset.induction_on with
      | empty => simpa using HasCompactSmoothingSchwartzSymbol.zero (n := n) (r := r) (s := s)
      | @insert j t hj ih =>
        simpa only [Finset.sum_insert hj] using (hR j).add ih
    exact hfin Finset.univ
  · apply hPK.sub _ hK.isClosed
    constructor
    · intro u
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hout
      apply hx
      simp only [sum_apply]
      apply Finset.sum_eq_zero
      intro j _
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hout ((hQK j).1 u h))
    · intro u hu
      simp only [sum_apply, fun j ↦ (hQK j).2 u hu, Finset.sum_const_zero]
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using χ.sum_eq_one hx

/-- A supported smoothing operator has an actual kernel inside any prescribed open neighborhood. -/
theorem HasCompactSmoothingSchwartzSymbol.exists_kernel_supported {n r s : ℕ}
    {P : LocalSchwartzOperator n r s} (hP : HasCompactSmoothingSchwartzSymbol P)
    (K U : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hPK : HasOperatorSupport K P) :
    ∃ k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)),
      ContDiff ℝ ∞ (Function.uncurry k) ∧ HasCompactSupport (Function.uncurry k) ∧
      tsupport (Function.uncurry k) ⊆ U ×ˢ U ∧
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) x,
        P u x = ∫ y, k x y (u y) := by
  classical
  obtain ⟨p, hp, hcp, hPp⟩ := hP
  obtain ⟨χ, hχ, hcχ, hχU, hχone⟩ := exists_compact_cutoff_one_near K U hK hU hKU
  let X := EuclideanSpace ℝ (Fin n)
  let k (x y : X) := χ x • (χ y • smoothingSymbolKernel p x y)
  have hk : ContDiff ℝ ∞ (Function.uncurry k) :=
    (hχ.comp contDiff_fst).smul
      ((hχ.comp contDiff_snd).smul (contDiff_smoothingSymbolKernel p hp))
  have hs : tsupport (Function.uncurry k) ⊆ tsupport χ ×ˢ tsupport χ := by
    apply closure_minimal _ ((isClosed_tsupport χ).prod (isClosed_tsupport χ))
    intro z hz
    constructor
    · by_contra hx
      exact hz (by simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport hx])
    · by_contra hy
      exact hz (by simp [Function.uncurry, k, image_eq_zero_of_notMem_tsupport hy])
  refine ⟨k, hk, (hcχ.prod hcχ).of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (Set.prod_mono hχU hχU), ?_⟩
  intro u x
  let v := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
    (fun y ↦ (χ y : ℂ)) u
  have hχT : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hv (y : X) : v y = χ y • u y := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hχT]
    exact algebraMap_smul ℂ (χ y) (u y)
  -- A plateau preserves the actual input germ, so the original support law removes it.
  have hinput : P v = P u := by
    have hd : Disjoint (tsupport (v - u)) K := by
      apply Set.disjoint_left.mpr
      intro y hy hyK
      have hnear : (fun z ↦ (v - u) z) =ᶠ[nhds y] 0 := by
        filter_upwards [isOpen_interior.mem_nhds (hχone hyK)] with z hz
        have hχz : χ z = 1 := show z ∈ {y | χ y = 1} from interior_subset hz
        simp only [sub_apply, hv, hχz, one_smul, sub_self, Pi.zero_apply]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hnear) hy
    exact sub_eq_zero.mp (by simpa only [map_sub] using hPK.2 (v - u) hd)
  have houtput : χ x • P u x = P u x := by
    by_cases hx : x ∈ K
    · have hχx : χ x = 1 := show x ∈ {y | χ y = 1} from interior_subset (hχone hx)
      rw [hχx, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hPK.1 u h)), smul_zero]
  -- Fourier inversion supplies the genuine smooth kernel; both cutoffs now lie inside U.
  calc
    P u x = χ x • P v x := by rw [hinput, houtput]
    _ = χ x • quantize p v x := by rw [hPp, quantizeSchwartz_apply]
    _ = χ x • ∫ y, smoothingSymbolKernel p x y (v y) := by
      rw [quantize_eq_integral_smoothingSymbolKernel p hp]
    _ = ∫ y, k x y (u y) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [hv, ContinuousLinearMap.map_smul_of_tower, k, smul_apply]

/-- The actual coordinate and rectangular frame transport has one compact full symbol and class. -/
theorem exists_compactSymbol_matrixCoordinatePushforward {n r s k l : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hρV : tsupport ρ ⊆ e.target)
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol Set.univ m p)
    (P : LocalSchwartzOperator n r s) (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ e.source)
    (hPK : HasOperatorSupport K P) (hχone : K ⊆ interior {x | χ x = 1})
    (hρone : e '' K ⊆ interior {x | ρ x = 1})
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B) :
    let Q := (matrixMultiplierCLM A hA hcA).comp
      ((coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P).comp
        (matrixMultiplierCLM B hB hcB))
    ∃ q : SymbolFunction n k l,
      IsSymbol Set.univ m q ∧ HasCompactSupport q ∧
      (∀ u x, Q u x = quantize q u x) ∧ HasOperatorSupport (e '' K) Q ∧
      IsSymbol e.target (m - 1) (q - matrixSymbol A B (cotangentSymbol e p)) := by
  classical
  let T := coordinatePushforward e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P
  let Q := (matrixMultiplierCLM A hA hcA).comp (T.comp (matrixMultiplierCLM B hB hcB))
  -- Retain the exact coordinate symbol with all of its lower-order contributions.
  obtain ⟨p₁, hp₁, hTp₁, hrem₁⟩ := exists_symbol_coordinatePushforward
    e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV m p hp P hP K hK hKU hPK hχone hρone
  have hTK : HasOperatorSupport (e '' K) T := hasOperatorSupport_coordinatePushforward
    e he hψ χ ρ hχ hcχ hχU hρ hcρ hρV P K hK hKU hPK
  let a := matrixAmplitude A B p₁
  have ha : IsAmplitude m a := isAmplitude_matrixAmplitude m p₁ hp₁ A B hA hB
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_matrixAmplitude A B p₁ hcA hcB
  let q := amplitudeSymbol a
  have hq : IsSymbol Set.univ m q := isSymbol_amplitudeSymbol m a ha hca
  have hcq : HasCompactSupport q := hasCompactSupport_amplitudeSymbol a hca
  have hact (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin k))) x :
      Q u x = quantize q u x := by
    change matrixMultiplierCLM A hA hcA (T (matrixMultiplierCLM B hB hcB u)) x = _
    rw [matrixMultiplierCLM_apply, hTp₁]
    exact (quantize_matrixAmplitude m p₁ hp₁ A B hA hcA hB hcB u x).symm
  refine ⟨q, hq, hcq, hact, ?_, ?_⟩
  · constructor
    · intro u
      exact (tsupport_matrixMultiplierCLM_subset A hA hcA _).trans
        (hTK.1 (matrixMultiplierCLM B hB hcB u))
    · intro u hu
      have hzero : T (matrixMultiplierCLM B hB hcB u) = 0 :=
        hTK.2 _ (hu.mono_left (tsupport_matrixMultiplierCLM_subset B hB hcB u))
      change matrixMultiplierCLM A hA hcA (T (matrixMultiplierCLM B hB hcB u)) = 0
      rw [hzero, map_zero]
  · -- Both principal comparisons refer to this same exact operator and the same matrices.
    have hrem₂ := (isSymbol_amplitudeSymbol_matrixAmplitude_sub m p₁ hp₁
      A B hA hcA hB hcB).restrict (Set.subset_univ e.target)
    have hrem₃ := isSymbol_matrixSymbol e.target e.open_target (m - 1)
      (p₁ - cotangentSymbol e p) hrem₁ A B hA.contDiffOn hB.contDiffOn
    convert hrem₂.add e.open_target hrem₃ using 1
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    simp only [Pi.add_apply, Pi.sub_apply, matrixSymbol, ContinuousLinearMap.comp_apply,
      add_apply, sub_apply, map_sub]
    abel

end AtiyahSinger

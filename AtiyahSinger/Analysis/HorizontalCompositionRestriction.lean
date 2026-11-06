/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateDifferentialProductLift
public import AtiyahSinger.Analysis.JointFrequencySymbolRestriction
public import AtiyahSinger.Analysis.LocalComposition

/-!
# Exact restriction of the horizontal symbol composition terms

Public module ID: M0751.

The symbol of the horizontal differential lift depends only on horizontal frequency.
Its differentiated composition terms therefore vanish whenever a contraction uses
the extra direction. The remaining contractions are exactly the original-dimensional
composition terms of the actual restricted symbol, even when the ambient symbol
depends on the extra base coordinate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.CoordinateDifferentialOperator

open scoped ContDiff

set_option maxSynthPendingDepth 25

/-- Every composition term of the horizontal lift restricts to the same term of the
original differential symbol and the actual frequency slice. -/
theorem compositionExpansionTerm_firstFactorLift_jointFrequencySymbolSlice
    {n r s q d : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (P : CoordinateDifferentialOperator n s q d U)
    (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hW : IsOpen W)
    (a : SymbolFunction (n + 1) r s)
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (W ×ˢ Set.univ))
    (τ : ℝ) (x ξ : EuclideanSpace ℝ (Fin n))
    (hx : EuclideanSpace.finAddEquivProd.symm
      (x, (0 : EuclideanSpace ℝ (Fin 1))) ∈ W) (j : ℕ) :
    compositionExpansionTerm P.firstFactorLift.totalSymbol a j
        (EuclideanSpace.finAddEquivProd.symm (x, (0 : EuclideanSpace ℝ (Fin 1))))
        (EuclideanSpace.finAddEquivProd.symm
          (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ))) =
      compositionExpansionTerm P.totalSymbol (jointFrequencySymbolSlice a τ) j x ξ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)
  let R := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let split : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let π : Y →L[ℝ] X := (ContinuousLinearMap.fst ℝ X _).comp split.toContinuousLinearMap
  let ι : X →L[ℝ] Y :=
    split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ X _)
  let ζ : Y := split.symm (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ))
  have hπι (y : X) : π (ι y) = y := by
    change (split (split.symm (y, 0))).1 = y
    rw [split.apply_symm_apply]
  have hπζ : π ζ = ξ := by
    change (split (split.symm (ξ, _))).1 = ξ
    rw [split.apply_symm_apply]
  have hπcoord (η : Y) (i : Fin n) : π η i = η i.castSucc := rfl
  have hιcoord (y : X) (i : Fin n) : ι y i.castSucc = y i := by
    exact (hπcoord (ι y) i).symm.trans (congrArg (fun z : X ↦ z i) (hπι y))
  have hιlast (y : X) : ι y (Fin.last n) = 0 := by
    change (split (split.symm (y, 0))).2 0 = 0
    rw [split.apply_symm_apply]
    simp only [PiLp.zero_apply]
  have hπsingle (i : Fin n) :
      π (EuclideanSpace.single i.castSucc 1) = EuclideanSpace.single i 1 := by
    ext k
    simp only [hπcoord, PiLp.single_apply, Fin.castSucc_inj]
  have hπlast : π (EuclideanSpace.single (Fin.last n) 1) = 0 := by
    ext i
    simp only [hπcoord, PiLp.single_apply, ite_eq_right (Fin.castSucc_ne_last i), PiLp.zero_apply]
  have hιsingle (i : Fin n) :
      ι (EuclideanSpace.single i 1) = EuclideanSpace.single i.castSucc 1 := by
    ext k
    refine Fin.lastCases ?_ (fun b ↦ ?_) k
    · simp only [hιlast, PiLp.single_apply, ite_eq_right (Fin.castSucc_ne_last i).symm]
    · simp only [hιcoord, PiLp.single_apply, Fin.castSucc_inj]
  -- At a fixed base point, the total symbol is a frequency polynomial, including outside U.
  have hp : ContDiff ℝ ∞ (P.totalSymbol x) := by
    unfold totalSymbol
    apply ContDiff.sum
    intro k _
    apply ContDiff.sum
    intro α _
    exact (contDiff_prod fun b _ ↦
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) (α b)).contDiff).smul contDiff_const
  have hpoly : P.firstFactorLift.totalSymbol (ι x) = P.totalSymbol x ∘ π := by
    funext η
    rw [firstFactorLift_totalSymbol]
    change P.totalSymbol (π (ι x)) (π η) = _
    rw [hπι]
    rfl
  have hfrequency (β : Fin j → Fin (n + 1)) :
      iteratedFDeriv ℝ j (P.firstFactorLift.totalSymbol (ι x)) ζ
          (fun b ↦ EuclideanSpace.single (β b) 1) =
        iteratedFDeriv ℝ j (P.totalSymbol x) ξ
          (fun b ↦ π (EuclideanSpace.single (β b) 1)) := by
    rw [hpoly, π.iteratedFDeriv_comp_right hp ζ (by simp)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hπζ]
  -- Restrict the actual base jet on an open neighborhood; no dummy-coordinate invariance.
  have hix : ι x ∈ W := hx
  have haslice : ContDiffOn ℝ ∞ (fun z : Y ↦ a z ζ) W :=
    ha.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz ↦ ⟨hz, Set.mem_univ _⟩)
  have hpre : IsOpen (ι ⁻¹' W) := hW.preimage ι.continuous
  have hbase (α : Fin j → Fin n) :
      iteratedFDeriv ℝ j (fun y ↦ jointFrequencySymbolSlice a τ y ξ) x
          (fun b ↦ EuclideanSpace.single (α b) 1) =
        iteratedFDeriv ℝ j (fun z : Y ↦ a z ζ) (ι x)
          (fun b ↦ EuclideanSpace.single (α b).castSucc 1) := by
    change iteratedFDeriv ℝ j ((fun z : Y ↦ a z ζ) ∘ ι) x
      (fun b ↦ EuclideanSpace.single (α b) 1) = _
    have h := ι.iteratedFDerivWithin_comp_right haslice hW.uniqueDiffOn
      hpre.uniqueDiffOn hix (i := j) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hpre hix,
      iteratedFDerivWithin_of_isOpen _ hW hix] at h
    have heval := congrArg
      (fun A : X [×j]→L[ℝ] H ↦ A (fun b ↦ EuclideanSpace.single (α b) 1)) h
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hιsingle] using heval
  -- Reindex exactly the horizontal coordinate tuples; all other summands vanish.
  let lift : (Fin j → Fin n) → (Fin j → Fin (n + 1)) :=
    fun α b ↦ (α b).castSucc
  have hlift : Function.Injective lift := by
    intro α β h
    funext b
    simpa only [lift, Fin.castSucc_inj] using congrFun h b
  let F (β : Fin j → Fin (n + 1)) : R :=
    (iteratedFDeriv ℝ j (P.firstFactorLift.totalSymbol (ι x)) ζ
      (fun b ↦ EuclideanSpace.single (β b) 1)).comp
        (iteratedFDeriv ℝ j (fun z : Y ↦ a z ζ) (ι x)
          (fun b ↦ EuclideanSpace.single (β b) 1))
  let G (α : Fin j → Fin n) : R :=
    (iteratedFDeriv ℝ j (P.totalSymbol x) ξ
      (fun b ↦ EuclideanSpace.single (α b) 1)).comp
        (iteratedFDeriv ℝ j (fun y ↦ jointFrequencySymbolSlice a τ y ξ) x
          (fun b ↦ EuclideanSpace.single (α b) 1))
  have hzero (β : Fin j → Fin (n + 1)) (hβ : β ∉ Set.range lift) : F β = 0 := by
    have hlast : ∃ b : Fin j, β b = Fin.last n := by
      by_contra! h
      choose α hα using fun b : Fin j ↦ Fin.exists_castSucc_eq.mpr (h b)
      exact hβ ⟨α, funext hα⟩
    obtain ⟨b, hb⟩ := hlast
    have hvanish : iteratedFDeriv ℝ j (P.totalSymbol x) ξ
        (fun c ↦ π (EuclideanSpace.single (β c) 1)) = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ b (by rw [hb, hπlast])
    dsimp only [F]
    rw [hfrequency, hvanish, ContinuousLinearMap.zero_comp]
  have hsame (α : Fin j → Fin n) : G α = F (lift α) := by
    dsimp only [F, G]
    rw [hfrequency, hbase]
    simp only [lift, hπsingle]
  have hsum : (∑ α, G α) = ∑ β, F β :=
    Fintype.sum_of_injective lift hlift G F hzero hsame
  change ((-Complex.I) ^ j / (j.factorial : ℂ)) • (∑ β, F β) =
    ((-Complex.I) ^ j / (j.factorial : ℂ)) • (∑ α, G α)
  rw [hsum]

end AtiyahSinger.CoordinateDifferentialOperator

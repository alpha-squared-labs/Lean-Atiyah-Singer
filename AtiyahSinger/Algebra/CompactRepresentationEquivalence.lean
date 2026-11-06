/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CompactRepresentationAveraging

/-!
# Characters determine finite continuous compact-group representations

Public module ID: M0007.

Equal characters give a nonzero intertwiner by Haar averaging on Hom. Split
its kernel and range equivariantly, cancel the common image, and induct on
dimension. This proves actual equivalence without choosing an irreducible
classification. The original jointly continuous actions are retained.
-/

@[expose] public noncomputable section

universe u

namespace AtiyahSinger

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

include μ
set_option maxHeartbeats 800000 in
-- The induction retains four restricted actions and the actual kernel/image equivalences.
/-- Finite jointly continuous compact-group representations with equal characters are equivalent. -/
theorem nonempty_equiv_of_character_eq (ρ : ContRepresentation ℂ G E)
    (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hchar : ρ.toRepresentation.character = σ.toRepresentation.character) :
    Nonempty (ContRepresentation.Equiv ρ σ) := by
  classical
  generalize hd : Module.finrank ℂ E = d
  induction d using Nat.strong_induction_on generalizing E F with
  | h d ih =>
    have hdim : Module.finrank ℂ E = Module.finrank ℂ F := by
      apply Nat.cast_injective (R := ℂ)
      simpa only [Representation.char_one] using congrFun hchar 1
    by_cases hzero : d = 0
    · -- Zero-dimensional representations have the unique equivariant linear equivalence.
      let : Subsingleton E := Module.finrank_zero_iff.mp (hd.trans hzero)
      let : Subsingleton F := Module.finrank_zero_iff.mp (hdim.symm.trans (hd.trans hzero))
      exact ⟨ContRepresentation.Equiv.mk
        (ContinuousLinearEquiv.ofFinrankEq hdim) (fun _ ↦ Subsingleton.elim _ _)⟩
    · let : Nontrivial E := Module.finrank_pos_iff.mp (hd ▸ Nat.pos_of_ne_zero hzero)
      obtain ⟨T, hT, hTint⟩ := exists_ne_zero_intertwining_of_character_eq μ ρ σ hρ hσ hchar
      let K := T.ker
      let R := T.range
      have hK (g : G) (v : E) (hv : v ∈ K) : ρ g v ∈ K := by
        change T (ρ g v) = 0
        rw [hTint, show T v = 0 from hv, map_zero]
      have hR (g : G) (v : F) (hv : v ∈ R) : σ g v ∈ R := by
        obtain ⟨w, rfl⟩ := hv
        exact ⟨ρ g w, hTint g w⟩
      -- Split the source kernel and target image using the original actions and one Haar measure.
      obtain ⟨C, hKC, hC⟩ := exists_invariant_complement μ ρ hρ K hK
      obtain ⟨D, hRD, hD⟩ := exists_invariant_complement μ σ hσ R hR
      let ρK := continuousSubmoduleRepresentation ρ K hK
      let ρC := continuousSubmoduleRepresentation ρ C hC
      let σR := continuousSubmoduleRepresentation σ R hR
      let σD := continuousSubmoduleRepresentation σ D hD
      let eS : (K × C) ≃L[ℂ] E := (K.prodEquivOfIsCompl C hKC).toContinuousLinearEquiv
      let eF : (R × D) ≃L[ℂ] F := (R.prodEquivOfIsCompl D hRD).toContinuousLinearEquiv
      let eT₀ : C ≃ₗ[ℂ] R :=
        (K.quotientEquivOfIsCompl C hKC).symm.trans T.toLinearMap.quotKerEquivRange
      let eT : C ≃L[ℂ] R := eT₀.toContinuousLinearEquiv
      have heT (v : C) : (eT v).val = T v.val := by
        exact T.toLinearMap.quotKerEquivRange_apply_mk v.val
      have hTequiv (g : G) (v : C) : eT (ρC g v) = σR g (eT v) := by
        apply Subtype.ext
        rw [heT]
        change T (ρ g v.val) = σ g (eT v).val
        rw [heT, hTint]
      -- Trace is additive for the same two direct-sum decompositions.
      have hsplit {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W]
          [FiniteDimensional ℂ W] (κ : ContRepresentation ℂ G W)
          (N C' : Submodule ℂ W) (hc : IsCompl N C')
          (hN : ∀ (g : G) (v : W), v ∈ N → κ g v ∈ N)
          (hC' : ∀ (g : G) (v : W), v ∈ C' → κ g v ∈ C') (g : G) :
          κ.toRepresentation.character g =
            (continuousSubmoduleRepresentation κ N hN).toRepresentation.character g +
            (continuousSubmoduleRepresentation κ C' hC').toRepresentation.character g := by
        let κN := continuousSubmoduleRepresentation κ N hN
        let κC := continuousSubmoduleRepresentation κ C' hC'
        let e := N.prodEquivOfIsCompl C' hc
        let φ : Representation.Equiv (Representation.prod κN.toRepresentation κC.toRepresentation)
            κ.toRepresentation := Representation.Equiv.mk e (by
          intro h
          apply LinearMap.ext
          intro v
          exact (κ h).map_add v.1.val v.2.val |>.symm)
        rw [← congrFun (Representation.char_iso φ) g]
        exact LinearMap.trace_prodMap' _ _
      have hcancel : ρK.toRepresentation.character = σD.toRepresentation.character := by
        let φ : Representation.Equiv ρC.toRepresentation σR.toRepresentation :=
          Representation.Equiv.mk eT.toLinearEquiv (by
            intro g
            apply LinearMap.ext
            intro v
            exact hTequiv g v)
        funext g
        have h₁ := hsplit ρ K C hKC hK hC g
        have h₂ := hsplit σ R D hRD hR hD g
        have h₃ := congrFun (Representation.char_iso φ) g
        have h₄ := congrFun hchar g
        change ρ.toRepresentation.character g =
          ρK.toRepresentation.character g + ρC.toRepresentation.character g at h₁
        change σ.toRepresentation.character g =
          σR.toRepresentation.character g + σD.toRepresentation.character g at h₂
        rw [h₁, h₂, h₃, add_comm] at h₄
        exact add_left_cancel h₄
      have hρK : Continuous (fun p : G × K ↦ ρK p.1 p.2) :=
        (hρ.comp (continuous_fst.prodMk
          (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      have hσD : Continuous (fun p : G × D ↦ σD p.1 p.2) :=
        (hσ.comp (continuous_fst.prodMk
          (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      have hless : Module.finrank ℂ K < d := by
        rw [← hd]
        apply Submodule.finrank_lt
        intro hk
        apply hT
        apply ContinuousLinearMap.ext
        intro v
        exact (show v ∈ K from hk ▸ Submodule.mem_top)
      obtain ⟨eK⟩ := ih (Module.finrank ℂ K) hless ρK σD hρK hσD hcancel rfl
      -- Reassemble the unchanged common image and the equivalence obtained by induction.
      let eprod₀ : (C × K) ≃ₗ[ℂ] (R × D) :=
        eT.toLinearEquiv.prodCongr eK.toContinuousLinearEquiv.toLinearEquiv
      let eprod : (C × K) ≃L[ℂ] (R × D) := eprod₀.toContinuousLinearEquiv
      let e : E ≃L[ℂ] F := eS.symm.trans
        (((LinearEquiv.prodComm ℂ K C).toContinuousLinearEquiv).trans
          (eprod.trans eF))
      have he (k : K) (c : C) : e (eS (k, c)) = eF (eT c, eK k) := by
        simp [e]
        rfl
      have hS (g : G) (k : K) (c : C) :
          ρ g (eS (k, c)) = eS (ρK g k, ρC g c) := (ρ g).map_add k.val c.val
      have hF (g : G) (r : R) (s : D) :
          σ g (eF (r, s)) = eF (σR g r, σD g s) := (σ g).map_add r.val s.val
      refine ⟨ContRepresentation.Equiv.mk e ?_⟩
      intro g
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨⟨k, c⟩, rfl⟩ := eS.surjective v
      change e (ρ g (eS (k, c))) = σ g (e (eS (k, c)))
      rw [hS, he, he, hF, hTequiv]
      exact congrArg (fun z ↦ eF (σR g (eT c), z))
        (DFunLike.congr_fun (eK.isIntertwining g) k)

end AtiyahSinger

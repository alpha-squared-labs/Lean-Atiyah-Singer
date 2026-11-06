/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologySequenceCup
public import AtiyahSinger.Topology.SimplexLocalHomology
public import AtiyahSinger.Topology.SingularHomologyEvaluation

/-!
# Connecting homomorphisms and the original Kronecker pairing

Public module ID: M2140.

The connecting map of an actual algebraic dual sequence is adjoint to the
connecting map of the original chain sequence. Both maps are computed with
the same lifted cochain and chain, retaining the native differential convention.
This comparison applies to the degreewise split relative singular triple used
by local homology and cohomology suspension.

Source: Hatcher, Algebraic Topology, Sections 2.1 and 3.1, the relative exact
sequences and the Kronecker pairing. The displayed compatibility is the direct
chain-level identity evaluating a coboundary on a lifted cycle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original dual connecting map is adjoint to the original chain connecting map. -/
theorem singularCochainHomologyEvaluation_boundary (R : Type) [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
    (hD : (S.op.map (singularCochainDualFunctor R)).ShortExact) (n : ℕ)
    (a : ((singularCochainDualFunctor R).obj (op S.X₁)).homology n)
    (c : S.X₃.homology (n + 1)) :
    singularCochainHomologyEvaluation R S.X₃ (n + 1)
        (hD.δ n (n + 1) rfl a) c =
      singularCochainHomologyEvaluation R S.X₁ n a (hS.δ (n + 1) n rfl c) := by
  /- Choose representatives and lift them through the two actual short exact
  sequences. Each connecting class is the corresponding lifted differential.
  The last calculation moves that differential across the same evaluation. -/
  let D := S.op.map (singularCochainDualFunctor R)
  have hrep {shape : ComplexShape ℕ} (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (k : ℕ) (z : C.homology k) :
      ∃ b : (C.sc k).moduleCatLeftHomologyData.K,
        (C.sc k).moduleCatHomologyIso.inv ((C.sc k).moduleCatToCycles.range.mkQ b) = z := by
    obtain ⟨b, hb⟩ := (C.sc k).moduleCatToCycles.range.mkQ_surjective
      ((C.sc k).moduleCatHomologyIso.hom z)
    refine ⟨b, ?_⟩
    rw [hb]
    exact congrArg (fun f ↦ f z) (C.sc k).moduleCatHomologyIso.hom_inv_id
  have hSn (k : ℕ) :
      (S.map (eval (ModuleCat.{u} R) (ComplexShape.down ℕ) k)).ShortExact :=
    hS.map_of_exact _
  have hDn (k : ℕ) :
      (D.map (eval (ModuleCat.{u} R) (ComplexShape.up ℕ) k)).ShortExact :=
    hD.map_of_exact _
  -- Lift the original cycle; its boundary is the first term's connecting representative.
  obtain ⟨c₃, rfl⟩ := hrep S.X₃ (n + 1) c
  obtain ⟨c₂, hc₂⟩ := (hSn (n + 1)).moduleCat_surjective_g c₃.val
  change S.g.f (n + 1) c₂ = c₃.val at hc₂
  have hdc : S.g.f n (S.X₂.d (n + 1) n c₂) = 0 := by
    have h := congrArg (fun f ↦ f c₂) (S.g.comm (n + 1) n)
    change S.X₃.d (n + 1) n (S.g.f (n + 1) c₂) =
      S.g.f n (S.X₂.d (n + 1) n c₂) at h
    rw [← h, hc₂]
    have hc : S.X₃.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c₃.val = 0 :=
      c₃.property
    exact (congrArg (fun j ↦ S.X₃.d (n + 1) j c₃.val = 0)
      (ChainComplex.next_nat_succ n)).mp hc
  obtain ⟨b₁, hb₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hSn n).exact (S.X₂.d (n + 1) n c₂) hdc
  change S.f.f n b₁ = S.X₂.d (n + 1) n c₂ at hb₁
  have hbclosed : S.X₁.d n ((ComplexShape.down ℕ).next n) b₁ = 0 := by
    apply (hSn ((ComplexShape.down ℕ).next n)).moduleCat_injective_f
    rw [map_zero]
    change S.f.f ((ComplexShape.down ℕ).next n)
      (S.X₁.d n ((ComplexShape.down ℕ).next n) b₁) = 0
    have h := congrArg (fun f ↦ f b₁) (S.f.comm n ((ComplexShape.down ℕ).next n))
    change S.X₂.d n ((ComplexShape.down ℕ).next n) (S.f.f n b₁) =
      S.f.f ((ComplexShape.down ℕ).next n) (S.X₁.d n ((ComplexShape.down ℕ).next n) b₁)
      at h
    rw [← h, hb₁]
    exact congrArg (fun f : S.X₂.X (n + 1) ⟶ S.X₂.X ((ComplexShape.down ℕ).next n) ↦
      f c₂) (S.X₂.d_comp_d (n + 1) n ((ComplexShape.down ℕ).next n))
  let c₁ : (S.X₁.sc n).moduleCatLeftHomologyData.K := ⟨b₁, hbclosed⟩
  have hδc := homologyConnecting_cycleClass R S hS n c₃ c₂ hc₂ c₁ hb₁
  -- Lift the original cocycle in the dual sequence, using its actual opposite order.
  obtain ⟨φ₁, rfl⟩ := hrep D.X₃ n a
  obtain ⟨φ₂, hφ₂⟩ := (hDn n).moduleCat_surjective_g φ₁.val
  change D.g.f n φ₂ = φ₁.val at hφ₂
  have hdφ : D.g.f (n + 1) (D.X₂.d n (n + 1) φ₂) = 0 := by
    have h := congrArg (fun f ↦ f φ₂) (D.g.comm n (n + 1))
    change D.X₃.d n (n + 1) (D.g.f n φ₂) =
      D.g.f (n + 1) (D.X₂.d n (n + 1) φ₂) at h
    rw [← h, hφ₂]
    have hφ : D.X₃.d n ((ComplexShape.up ℕ).next n) φ₁.val = 0 := φ₁.property
    exact (congrArg (fun j ↦ D.X₃.d n j φ₁.val = 0) (CochainComplex.next ℕ n)).mp hφ
  obtain ⟨ψ₃, hψ₃⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hDn (n + 1)).exact (D.X₂.d n (n + 1) φ₂) hdφ
  change D.f.f (n + 1) ψ₃ = D.X₂.d n (n + 1) φ₂ at hψ₃
  have hψclosed : D.X₁.d (n + 1) (n + 1 + 1) ψ₃ = 0 := by
    apply (hDn (n + 1 + 1)).moduleCat_injective_f
    rw [map_zero]
    change D.f.f (n + 1 + 1) (D.X₁.d (n + 1) (n + 1 + 1) ψ₃) = 0
    have h := congrArg (fun f ↦ f ψ₃) (D.f.comm (n + 1) (n + 1 + 1))
    change D.X₂.d (n + 1) (n + 1 + 1) (D.f.f (n + 1) ψ₃) =
      D.f.f (n + 1 + 1) (D.X₁.d (n + 1) (n + 1 + 1) ψ₃) at h
    rw [← h, hψ₃]
    exact congrArg (fun f ↦ f φ₂) (D.X₂.d_comp_d n (n + 1) (n + 1 + 1))
  let φ₃ : (D.X₁.sc (n + 1)).moduleCatLeftHomologyData.K := ⟨ψ₃, by
    change D.X₁.d (n + 1) ((ComplexShape.up ℕ).next (n + 1)) ψ₃ = 0
    exact (congrArg (fun j ↦ D.X₁.d (n + 1) j ψ₃ = 0)
      (CochainComplex.next ℕ (n + 1))).mpr hψclosed⟩
  have hδφ := cohomologyBoundary_cocycleClass R D hD n φ₁ φ₂ hφ₂ φ₃ hψ₃
  rw [hδφ, hδc]
  refine (singularCochainHomologyEvaluation_cycleClass R S.X₃ (n + 1) φ₃ c₃).trans ?_
  refine Eq.trans ?_ (singularCochainHomologyEvaluation_cycleClass R S.X₁ n φ₁ c₁).symm
  -- Evaluation of the lifted coboundary equals evaluation on the lifted boundary.
  change (show S.X₃.X (n + 1) ⟶ singularCoefficient R from φ₃.val) c₃.val =
    (show S.X₁.X n ⟶ singularCoefficient R from φ₁.val) c₁.val
  calc
    (show S.X₃.X (n + 1) ⟶ singularCoefficient R from φ₃.val) c₃.val =
        (show S.X₂.X (n + 1) ⟶ singularCoefficient R from D.f.f (n + 1) φ₃.val) c₂ := by
          change _ = (show S.X₃.X (n + 1) ⟶ singularCoefficient R from φ₃.val)
            (S.g.f (n + 1) c₂)
          rw [hc₂]
    _ = (show S.X₂.X (n + 1) ⟶ singularCoefficient R from D.X₂.d n (n + 1) φ₂) c₂ :=
      congrArg (fun f : D.X₂.X (n + 1) ↦
        (show S.X₂.X (n + 1) ⟶ singularCoefficient R from f) c₂) hψ₃
    _ = (show S.X₂.X n ⟶ singularCoefficient R from φ₂) (S.X₂.d (n + 1) n c₂) := rfl
    _ = (show S.X₁.X n ⟶ singularCoefficient R from D.g.f n φ₂) c₁.val := by
      change _ = (show S.X₂.X n ⟶ singularCoefficient R from φ₂) (S.f.f n c₁.val)
      rw [hb₁]
    _ = (show S.X₁.X n ⟶ singularCoefficient R from φ₁.val) c₁.val :=
      congrArg (fun f : D.X₃.X n ↦ (show S.X₁.X n ⟶ singularCoefficient R from f) c₁.val) hφ₂

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The two original relative triple boundaries are adjoint under Kronecker evaluation. -/
theorem relativeSingularCohomologyTripleBoundary_evaluation (R : Type) [CommRing R]
    {X : Type u} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B) (n : ℕ)
    (a : relativeSingularCohomology R ((Subtype.val : B → X) ⁻¹' A) n)
    (c : relativeSingularHomology R B (n + 1)) :
    singularCochainHomologyEvaluation R (relativeSingularChains R B) (n + 1)
        ((shortExact_relativeSingularCochainTripleSequence R A B hAB).δ n (n + 1) rfl a)
        c =
      singularCochainHomologyEvaluation R
        (relativeSingularChains R ((Subtype.val : B → X) ⁻¹' A)) n a
        ((shortExact_relativeSingularTripleSequence R A B hAB).δ (n + 1) n rfl c) := by
  -- These are the actual quotient-chain sequence and its degreewise exact algebraic dual.
  exact singularCochainHomologyEvaluation_boundary R (relativeSingularTripleSequence R A B hAB)
    (shortExact_relativeSingularTripleSequence R A B hAB)
    (shortExact_relativeSingularCochainTripleSequence R A B hAB) n a c

end AtiyahSinger

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSupportedCohomologyThom

/-!
# The relative boundary and the actual two-support cup product

Public module ID: M2100.

Right cup with a fixed relative class intertwines the ordinary pair boundary
and the boundary of the original joint relative quotient sequence. The target
is the specified joint Alexander--Whitney product, identified with the open
union relative cohomology by its actual small-chain comparison.

Source: Hatcher, Algebraic Topology, Section 3.2, compatibility of cup products
with the relative exact sequence. The factor order is retained throughout;
the right factor is closed, so this boundary formula has no extra sign.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The pair boundary in the left factor agrees with the original joint-support boundary. -/
theorem relativeUnionSingularCohomologyBoundary_cup (R : Type) [CommRing R]
    {X : Type u} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (p r : ℕ) (a : singularCohomology R B p) (b : relativeSingularCohomology R A r) :
    (shortExact_relativeUnionSingularCochainSequence R A B).δ
        (p + r) (p + r + 1) rfl
        (relativeSingularCohomologyAction R ((Subtype.val : B → X) ⁻¹' A) p r a
          (relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
            (fun _ hx ↦ hx) r b)) =
      (eqToIso (congrArg (fun k ↦ relativeUnionSingularCohomology R B A k)
        (Nat.add_right_comm p 1 r))).hom
        (relativeUnionCohomologyComparison R B A ((p + 1) + r)
          (relativeSingularCohomologyUnionCup R B A hB hA (p + 1) r
            ((shortExact_singularSubspaceCochains R B).δ p (p + 1) rfl a) b)) := by
  /- Lift the ordinary cocycle on B. Its coboundary is relative to B.
  Multiplication by the same closed A-relative cocycle gives a lift in the
  joint sequence, whose coboundary is precisely the two-relative cup. -/
  let S := singularSubspaceCochainsSequence R B
  let T := relativeUnionSingularCochainSequence R A B
  let C := relativeUnionSingularCochains R B A
  have hS := shortExact_singularSubspaceCochains R B
  have hT := shortExact_relativeUnionSingularCochainSequence R A B
  let A' : Set B := (Subtype.val : B → X) ⁻¹' A
  let I := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let J := (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R B A).op
  have hrep (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (z : D.homology k) :
      ∃ c : (D.sc k).moduleCatLeftHomologyData.K,
        (D.sc k).moduleCatHomologyIso.inv ((D.sc k).moduleCatToCycles.range.mkQ c) = z := by
    obtain ⟨c, hc⟩ := (D.sc k).moduleCatToCycles.range.mkQ_surjective
      ((D.sc k).moduleCatHomologyIso.hom z)
    refine ⟨c, ?_⟩
    rw [hc]
    exact congrArg (fun f ↦ f z) (D.sc k).moduleCatHomologyIso.hom_inv_id
  have hclosed (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (c : (D.sc k).moduleCatLeftHomologyData.K) : D.d k (k + 1) c.val = 0 := by
    have hc : D.d k ((ComplexShape.up ℕ).next k) c.val = 0 := c.property
    exact (congrArg (fun j ↦ D.d k j c.val = 0) (CochainComplex.next ℕ k)).mp hc
  have hcycle (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (z : D.X k)
      (hz : D.d k (k + 1) z = 0) : z ∈ (D.sc k).g.hom.ker := by
    change D.d k ((ComplexShape.up ℕ).next k) z = 0
    exact (congrArg (fun j ↦ D.d k j z = 0) (CochainComplex.next ℕ k)).mpr hz
  have hSn (k : ℕ) :
      (S.map (eval (ModuleCat.{u} R) (ComplexShape.up ℕ) k)).ShortExact := hS.map_of_exact _
  -- Keep actual representatives for both prescribed cohomology classes.
  obtain ⟨α, hα⟩ := hrep S.X₃ p a
  obtain ⟨β, hβ⟩ := hrep (relativeSingularCochains R A) r b
  obtain ⟨α₂, hα₂⟩ := (hSn p).moduleCat_surjective_g α.val
  change S.g.f p α₂ = α.val at hα₂
  have hdα : S.g.f (p + 1) (S.X₂.d p (p + 1) α₂) = 0 := by
    have h := congrArg (fun f ↦ f α₂) (S.g.comm p (p + 1))
    change S.X₃.d p (p + 1) (S.g.f p α₂) =
      S.g.f (p + 1) (S.X₂.d p (p + 1) α₂) at h
    rw [← h, hα₂, hclosed]
  obtain ⟨γ₁, hγ₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hSn (p + 1)).exact (S.X₂.d p (p + 1) α₂) hdα
  change S.f.f (p + 1) γ₁ = S.X₂.d p (p + 1) α₂ at hγ₁
  have hγclosed : S.X₁.d (p + 1) (p + 1 + 1) γ₁ = 0 := by
    apply (hSn (p + 1 + 1)).moduleCat_injective_f
    rw [map_zero]
    change S.f.f (p + 1 + 1) (S.X₁.d (p + 1) (p + 1 + 1) γ₁) = 0
    have h := congrArg (fun f ↦ f γ₁) (S.f.comm (p + 1) (p + 1 + 1))
    change S.X₂.d (p + 1) (p + 1 + 1) (S.f.f (p + 1) γ₁) =
      S.f.f (p + 1 + 1) (S.X₁.d (p + 1) (p + 1 + 1) γ₁) at h
    rw [← h, hγ₁]
    exact congrArg (fun f ↦ f α₂) (S.X₂.d_comp_d p (p + 1) (p + 1 + 1))
  let γ : relativeSingularCocycles R B (p + 1) :=
    ⟨γ₁, hcycle S.X₁ (p + 1) γ₁ hγclosed⟩
  have hδα := cohomologyBoundary_cocycleClass R S hS p α α₂ hα₂ γ hγ₁
  -- Restrict the same right cocycle and use the original right-cup lift on X.
  let βB : relativeSingularCocycles R A' r := ⟨T.g.f r β.val, by
    apply hcycle
    change T.X₃.d r (r + 1) (T.g.f r β.val) = 0
    have h := congrArg (fun f ↦ f β.val) (T.g.comm r (r + 1))
    change T.X₃.d r (r + 1) (T.g.f r β.val) =
      T.g.f (r + 1) (T.X₂.d r (r + 1) β.val) at h
    rw [h, hclosed, map_zero]⟩
  have hβB : relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
      (fun _ hx ↦ hx) r (relativeSingularCocycleClass R A r β) =
        relativeSingularCocycleClass R A' r βB :=
    homologyMap_cycleClass R T.X₂ T.X₃ T.g r β βB rfl
  let ξB := relativeSingularCocycleAction R A' p r α βB
  let ξ₂ := relativeSingularCochainAction R A p r α₂ β.val
  have hξ₂ : T.g.f (p + r) ξ₂ = ξB.val := by
    have h := relativeSingularCochainAction_natural R (ContinuousMap.subtypeVal B)
      A' A (fun _ hx ↦ hx) p r α₂ β.val
    change T.g.f (p + r) ξ₂ =
      relativeSingularCochainAction R A' p r (S.g.f p α₂) (T.g.f r β.val) at h
    rw [hα₂] at h
    exact h
  -- The inclusion of the joint kernel preserves the actual two-relative AW formula.
  have hproj : T.f ≫ I = J := by
    change (singularCochainDualFunctor R).map (relativeUnionSingularChainSequence R A B).g.op ≫
      (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op = _
    rw [← Functor.map_comp, ← op_comp]
    congr 1
    apply congrArg Quiver.Hom.op
    dsimp [relativeUnionSingularChainSequence, relativeSingularChainsProjection]
    exact cokernel.π_desc _ _ _
  have hcup (i j : ℕ) (x : (relativeSingularCochains R B).X i)
      (y : (relativeSingularCochains R A).X j) :
      T.f.f (i + j) (relativeUnionSingularCochainCup R B A i j x y) =
        relativeSingularCochainAction R A i j (S.f.f i x) y := by
    apply (relativeSingularCochainEquiv R A (i + j)).injective
    apply Subtype.ext
    change I.f (i + j) (T.f.f (i + j) _) = I.f (i + j) _
    have hmap := congrArg (fun f ↦ f.f (i + j)
      (relativeUnionSingularCochainCup R B A i j x y)) hproj
    change I.f (i + j) (T.f.f (i + j) _) = J.f (i + j) _ at hmap
    rw [hmap]
    have hjoint : J.f (i + j) (relativeUnionSingularCochainCup R B A i j x y) =
        singularCochainCup R X i j (S.f.f i x) (I.f j y) :=
      congrArg Subtype.val
        ((relativeUnionSingularCochainEquiv R B A (i + j)).apply_symm_apply _)
    have haction : I.f (i + j) (relativeSingularCochainAction R A i j (S.f.f i x) y) =
        singularCochainCup R X i j (S.f.f i x) (I.f j y) :=
      congrArg Subtype.val ((relativeSingularCochainEquiv R A (i + j)).apply_symm_apply _)
    exact hjoint.trans haction.symm
  let ξ₁ := relativeUnionSingularCocycleCup R B A (p + 1) r γ β
  let e : (p + 1) + r = p + r + 1 := Nat.add_right_comm p 1 r
  have hcast {i j : ℕ} (h : i = j) (z : (C.sc i).moduleCatLeftHomologyData.K) :
      ∃ w : (C.sc j).moduleCatLeftHomologyData.K,
        w.val = (C.XIsoOfEq h).hom z.val ∧
          (C.sc j).moduleCatHomologyIso.inv ((C.sc j).moduleCatToCycles.range.mkQ w) =
            (eqToIso (congrArg (fun k ↦ C.homology k) h)).hom
              ((C.sc i).moduleCatHomologyIso.inv ((C.sc i).moduleCatToCycles.range.mkQ z)) := by
    subst j
    exact ⟨z, rfl, rfl⟩
  obtain ⟨ξ₁', hξ₁'val, hξ₁'class⟩ := hcast e ξ₁
  have hξ₁ : T.f.f (p + r + 1) ξ₁'.val = T.X₂.d (p + r) (p + r + 1) ξ₂ := by
    have htransport {i j : ℕ} (h : i = j) (z : C.X i) :
        T.f.f j ((C.XIsoOfEq h).hom z) = (T.X₂.XIsoOfEq h).hom (T.f.f i z) := by
      subst j
      rfl
    rw [hξ₁'val, htransport]
    change (T.X₂.XIsoOfEq e).hom
      (T.f.f ((p + 1) + r) (relativeUnionSingularCochainCup R B A (p + 1) r γ.val β.val)) = _
    rw [hcup]
    change (T.X₂.XIsoOfEq e).hom
      (relativeSingularCochainAction R A (p + 1) r (S.f.f (p + 1) γ₁) β.val) = _
    rw [hγ₁]
    have hleib := relativeSingularCochainAction_leibniz R A p r α₂ β.val
    rw [hclosed] at hleib
    change ((relativeSingularCochains R A).XIsoOfEq (Nat.add_right_comm p 1 r)).hom
      (relativeSingularCochainAction R A (p + 1) r
        ((singularCochains R X).d p (p + 1) α₂) β.val) =
      (relativeSingularCochains R A).d (p + r) (p + r + 1)
        (relativeSingularCochainAction R A p r α₂ β.val)
    simpa only [map_zero, smul_zero, add_zero] using hleib.symm
  have hδξ := cohomologyBoundary_cocycleClass R T hT (p + r) ξB ξ₂ hξ₂ ξ₁' hξ₁
  -- Pass through the same cocycle quotients and the specified open-union comparison.
  change singularCocycleClass R B p α = a at hα
  change relativeSingularCocycleClass R A r β = b at hβ
  have hinput : relativeSingularCohomologyAction R A' p r a
      (relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
        (A := A') (B := A) (fun _ hx ↦ hx) r b) =
        relativeSingularCocycleClass R A' (p + r) ξB := by
    have hb' := (congrArg (relativeSingularCohomologyPullback R
      (ContinuousMap.subtypeVal B) (A := A') (B := A) (fun _ hx ↦ hx) r) hβ.symm).trans hβB
    exact (congrArg₂ (fun x y ↦ relativeSingularCohomologyAction R A' p r x y)
      hα.symm hb').trans
      (relativeSingularCohomologyAction_cocycleClass R A' p r α βB)
  have hsource : hS.δ p (p + 1) rfl a = relativeSingularCocycleClass R B (p + 1) γ :=
    (congrArg (hS.δ p (p + 1) rfl) hα.symm).trans hδα
  have hproduct : relativeUnionCohomologyComparison R B A ((p + 1) + r)
      (relativeSingularCohomologyUnionCup R B A hB hA (p + 1) r
        (hS.δ p (p + 1) rfl a) b) =
      (C.sc ((p + 1) + r)).moduleCatHomologyIso.inv
        ((C.sc ((p + 1) + r)).moduleCatToCycles.range.mkQ ξ₁) :=
    (congrArg₂ (fun x y ↦ relativeUnionCohomologyComparison R B A ((p + 1) + r)
      (relativeSingularCohomologyUnionCup R B A hB hA (p + 1) r x y))
      hsource hβ.symm).trans
        (relativeSingularCohomologyUnionCup_cocycleClass R B A hB hA (p + 1) r γ β)
  exact ((congrArg (hT.δ (p + r) (p + r + 1) rfl) hinput).trans hδξ).trans
    (hξ₁'class.trans (congrArg
      (eqToIso (congrArg (fun k ↦ C.homology k) e)).hom hproduct).symm)

end AtiyahSinger

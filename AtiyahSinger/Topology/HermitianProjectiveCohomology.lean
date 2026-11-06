/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyPowerNaturality
public import AtiyahSinger.Topology.FiniteCupVanishing
public import AtiyahSinger.Topology.HermitianProjectiveTopSummand
public import AtiyahSinger.Topology.ProjectivePuncturedProduct
public import AtiyahSinger.Topology.SingularCohomologyChangeCoefficients
public import AtiyahSinger.Topology.SingularCohomologyLerayHirschStep
public import AtiyahSinger.Topology.SingularCohomologyLerayHirschTransport

/-!
# The projective cohomology basis over an arbitrary parameter space

Public module ID: M1892.

The powers of the original tautological Chern root give the actual finite
Leray--Hirsch comparison on X times the orthogonal-projector projective space.
Induction removes one projective point. Its complement retracts onto the
orthogonal projective hyperplane, while the point-supported coordinate top
class supplies the last summand through the original relative exact sequence.

The parameter space and commutative coefficient ring are arbitrary. No
Kunneth isomorphism is assumed. The zero-dimensional vector space has empty
projective space and the empty basis, so this initial case is included.

Source: the cellular projective-space calculation and relative Leray--Hirsch
argument, Hatcher, Algebraic Topology, Sections 3.2 and 4.D; the specified
tautological normalization is from Milnor--Stasheff, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open CategoryTheory HomologicalComplex Opposite

universe u

set_option maxHeartbeats 600000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual tautological powers form a cohomology basis after any product parameter. -/
theorem homologyMap_hermitianProjectiveProdLerayHirsch_bijective
    (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]
    (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (r : ℕ) (hr : Module.finrank ℂ V = r)
    (c : ∀ i : ULift.{u} (Fin r),
      singularCocycles R (X × HermitianProjectiveSpace V InnerProductSpace.toCore)
        (2 * i.down.val))
    (hc : ∀ i : ULift.{u} (Fin r), singularCocycleClass R
      (X × HermitianProjectiveSpace V InnerProductSpace.toCore) (2 * i.down.val) (c i) =
        singularCohomologyPullback R (ContinuousMap.snd :
          C(X × HermitianProjectiveSpace V InnerProductSpace.toCore,
            HermitianProjectiveSpace V InnerProductSpace.toCore)) (2 * i.down.val)
          (singularCohomologyDegreeTwoPow R
            (HermitianProjectiveSpace V InnerProductSpace.toCore)
            (singularCohomologyChangeCoefficients R
              (HermitianProjectiveSpace V InnerProductSpace.toCore) 2
              (tautologicalChernRoot V)) i.down.val)) (n : ℕ) :
    Function.Bijective (homologyMap (singularCohomologyLerayHirschMap R
      (ContinuousMap.fst : C(X × HermitianProjectiveSpace V InnerProductSpace.toCore, X))
      (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val) c) n) := by
  classical
  have hpull {Y Z T : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
      [TopologicalSpace T] (f : C(Y, Z)) (g : C(Z, T)) (k : ℕ)
      (a : singularCohomology R T k) :
      singularCohomologyPullback R f k (singularCohomologyPullback R g k a) =
        singularCohomologyPullback R (g.comp f) k a :=
    congrArg (fun F ↦ F a)
      ((singularCohomologyFunctor R k).map_comp (TopCat.ofHom g).op (TopCat.ofHom f).op).symm
  induction r generalizing V n with
  | zero =>
    -- Rank zero gives an empty projective space and an empty source family.
    let Q := HermitianProjectiveSpace V InnerProductSpace.toCore
    have : IsEmpty Q := ⟨fun P ↦ by
      have hdim := Submodule.finrank_le (LinearMap.range P.val.toLinearMap)
      rw [P.property.2.1, hr] at hdim
      omega⟩
    let C (i : ULift.{u} (Fin 0)) : CochainComplex (ModuleCat.{u} R) ℕ :=
      (singularCochains R X).extend
        (ComplexShape.embeddingUp'Add (1 : ℕ) (2 * i.down.val))
    have hsource : Subsingleton ((cochainFamilyProduct R C).homology n) :=
      (bijective_homologyMap_cochainFamilyProductProjection R C n).injective.subsingleton
    have htarget := subsingleton_singularCohomology_of_isEmpty R (X × Q) n
    exact ⟨fun _ _ _ ↦ hsource.elim _ _, fun a ↦ ⟨0, htarget.elim _ a⟩⟩
  | succ r ih =>
    -- Fix a unit vector and its actual orthogonal hyperplane for the induction.
    let basis := (stdOrthonormalBasis ℂ V).reindex (finCongr hr)
    let e : V := basis 0
    have he : ‖e‖ = 1 := basis.norm_eq_one 0
    have hne : e ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at he
      exact zero_ne_one he
    let K := (Submodule.span ℂ {e})ᗮ
    let : Fact (Module.finrank ℂ V = r + 1) := ⟨hr⟩
    have hK : Module.finrank ℂ K = r := Submodule.finrank_orthogonal_span_singleton hne
    have hker : (innerSL ℂ e).ker = K := by
      ext v
      change inner ℂ e v = 0 ↔ v ∈ (Submodule.span ℂ {e})ᗮ
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm
    have hkerDim : Module.finrank ℂ (innerSL ℂ e).ker = r := by rw [hker]; exact hK
    let b := (stdOrthonormalBasis ℂ (innerSL ℂ e).ker).reindex (finCongr hkerDim)
    let Q := HermitianProjectiveSpace V InnerProductSpace.toCore
    let QK := HermitianProjectiveSpace K InnerProductSpace.toCore
    let A : Set (X × Q) := {z | z.2 ≠ ofVector e hne}
    let π : C(X × Q, X) := ContinuousMap.fst
    let πK : C(X × QK, X) := ContinuousMap.fst
    let inc : C(A, X × Q) := ContinuousMap.subtypeVal A
    let H := puncturedProdHomotopyEquiv X e hne
    let s : C(X × QK, A) := H.invFun
    let f : C(X × QK, X × Q) := inc.comp s
    have hπ : π.comp f = πK :=
      (puncturedProdHomotopyEquiv_symm_properties X e hne).2
    let top : ULift.{u} (Fin (r + 1)) := ULift.up (Fin.last r)
    let I₀ := {i : ULift.{u} (Fin (r + 1)) // i ≠ top}
    have hlt (i : I₀) : i.val.down.val < r := by
      by_contra h
      have heq : i.val.down.val = r := by have := i.val.down.isLt; omega
      apply i.property
      apply ULift.ext
      exact Fin.ext heq
    let index : I₀ ≃ ULift.{u} (Fin r) :=
      { toFun := fun i ↦ ULift.up ⟨i.val.down.val, hlt i⟩
        invFun := fun j ↦ ⟨ULift.up j.down.castSucc, by
          intro h
          have hv := congrArg (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down.val) h
          change j.down.val = r at hv
          have := j.down.isLt
          omega⟩
        left_inv := fun _ ↦ Subtype.ext (ULift.ext (Fin.ext rfl))
        right_inv := fun _ ↦ ULift.ext (Fin.ext rfl) }
    let cK (i : ULift.{u} (Fin r)) : singularCocycles R (X × QK) (2 * i.down.val) :=
      singularCocyclePullback R f (2 * i.down.val) (c (ULift.up i.down.castSucc))
    let tV : singularCohomology R Q 2 :=
      singularCohomologyChangeCoefficients R Q 2 (tautologicalChernRoot V)
    let tK : singularCohomology R QK 2 :=
      singularCohomologyChangeCoefficients R QK 2 (tautologicalChernRoot K)
    let q : C(X × QK, Q) := (ContinuousMap.snd : C(X × Q, Q)).comp f
    have hrootInt : singularCohomologyPullback ℤ q 2 (tautologicalChernRoot V) =
        singularCohomologyPullback ℤ (ContinuousMap.snd : C(X × QK, QK)) 2
          (tautologicalChernRoot K) := by
      have h := tautologicalChernRoot_pullback_puncturedProdHomotopyEquiv_symm X e hne
      have hcomp : singularCohomologyPullback ℤ s 2
          (singularCohomologyPullback ℤ ((ContinuousMap.snd : C(X × Q, Q)).comp inc) 2
            (tautologicalChernRoot V)) =
          singularCohomologyPullback ℤ q 2 (tautologicalChernRoot V) :=
        congrArg (fun F ↦ F (tautologicalChernRoot V))
          ((singularCohomologyFunctor ℤ 2).map_comp
            (TopCat.ofHom ((ContinuousMap.snd : C(X × Q, Q)).comp inc)).op
            (TopCat.ofHom s).op).symm
      exact hcomp.symm.trans h
    have hroot : singularCohomologyPullback R q 2 tV =
        singularCohomologyPullback R (ContinuousMap.snd : C(X × QK, QK)) 2 tK := by
      dsimp only [tV, tK]
      rw [← singularCohomologyChangeCoefficients_naturality, hrootInt,
        singularCohomologyChangeCoefficients_naturality]
    have hcK (i : ULift.{u} (Fin r)) : singularCocycleClass R (X × QK)
        (2 * i.down.val) (cK i) =
        singularCohomologyPullback R (ContinuousMap.snd : C(X × QK, QK)) (2 * i.down.val)
          (singularCohomologyDegreeTwoPow R QK tK i.down.val) := by
      have hci : singularCocycleClass R (X × Q) (2 * i.down.val)
          (c (ULift.up i.down.castSucc)) =
          singularCohomologyPullback R (ContinuousMap.snd : C(X × Q, Q)) (2 * i.down.val)
            (singularCohomologyDegreeTwoPow R Q tV i.down.val) := hc (ULift.up i.down.castSucc)
      calc
        _ = singularCohomologyPullback R f (2 * i.down.val)
            (singularCohomologyPullback R (ContinuousMap.snd : C(X × Q, Q))
              (2 * i.down.val) (singularCohomologyDegreeTwoPow R Q tV i.down.val)) :=
          (singularCocycleClass_pullback R f (2 * i.down.val)
            (c (ULift.up i.down.castSucc))).trans
              (congrArg (singularCohomologyPullback R f (2 * i.down.val)) hci)
        _ = singularCohomologyPullback R q (2 * i.down.val)
            (singularCohomologyDegreeTwoPow R Q tV i.down.val) :=
          hpull f (ContinuousMap.snd : C(X × Q, Q)) (2 * i.down.val) _
        _ = singularCohomologyDegreeTwoPow R (X × QK)
            (singularCohomologyPullback R q 2 tV) i.down.val :=
          singularCohomologyPullback_degreeTwoPow R q tV i.down.val
        _ = singularCohomologyDegreeTwoPow R (X × QK)
            (singularCohomologyPullback R (ContinuousMap.snd : C(X × QK, QK)) 2 tK)
            i.down.val := congrArg (fun t ↦ singularCohomologyDegreeTwoPow R (X × QK)
              t i.down.val) hroot
        _ = _ := (singularCohomologyPullback_degreeTwoPow R
          (ContinuousMap.snd : C(X × QK, QK)) tK i.down.val).symm
    -- The lower comparison uses exactly the original family with its highest power omitted.
    let d (i : ULift.{u} (Fin (r + 1))) := 2 * i.down.val
    let cLower (i : I₀) : singularCocycles R (X × QK) (d i.val) := cK (index i)
    let old := singularCohomologyLerayHirschMap R π
      (fun i : I₀ ↦ d i.val) (fun i ↦ c i.val)
    have hOld (k : ℕ) : Function.Bijective (fun a : (cochainFamilyProduct R
        (fun i : I₀ ↦ (singularCochains R X).extend
          (ComplexShape.embeddingUp'Add (1 : ℕ) (d i.val)))).homology k ↦
        singularCohomologyPullback R inc k (homologyMap old k a)) := by
      have hsmall := ih K hK cK hcK k
      have hlower : Function.Bijective (homologyMap
          (singularCohomologyLerayHirschMap R πK (fun i : I₀ ↦ d i.val) cLower) k) :=
        homologyMap_singularCohomologyLerayHirschMap_bijective_reindex R πK
          (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val) cK index k hsmall
      have hclasses (i : I₀) : singularCohomologyPullback R f (d i.val)
          (singularCocycleClass R (X × Q) (d i.val) (c i.val)) =
          singularCocycleClass R (X × QK) (d i.val) (cLower i) := by
        exact (singularCocycleClass_pullback R f (d i.val) (c i.val)).symm
      have hmap := homologyMap_singularCohomologyLerayHirschMap_comp_pullback
        R π πK f hπ (fun i : I₀ ↦ d i.val) (fun i ↦ c i.val) cLower hclasses k
      have hcompose : singularCohomologyPullback R inc k ≫
          singularCohomologyPullback R s k = singularCohomologyPullback R f k := by
        simp only [singularCohomologyPullback, ← Functor.map_comp, ← op_comp]
        rfl
      have hmap' : homologyMap old k ≫ singularCohomologyPullback R inc k ≫
          singularCohomologyPullback R s k = homologyMap
            (singularCohomologyLerayHirschMap R πK (fun i : I₀ ↦ d i.val) cLower) k := by
        rw [hcompose]
        exact hmap
      have hcomp : Function.Bijective (singularCohomologyPullback R s k ∘
          fun a ↦ singularCohomologyPullback R inc k (homologyMap old k a)) := by
        change Function.Bijective (homologyMap old k ≫
          singularCohomologyPullback R inc k ≫ singularCohomologyPullback R s k)
        rw [hmap']
        exact hlower
      have : IsIso (singularCohomologyPullback R s k) :=
        isIso_singularCohomologyPullback_of_homotopyInverse R s H.toFun
          H.right_inv H.left_inv k
      exact hcomp.of_comp_left
        (ConcreteCategory.bijective_of_isIso (singularCohomologyPullback R s k)).injective
    -- The original localized top class gives the missing summand of the exact sequence.
    obtain ⟨g, hg, hformula⟩ := exists_hermitianProjectiveProdTopSummand
      R X V r e he hne b (c top) (hc top) n
    refine homologyMap_singularCohomologyLerayHirschMap_bijective_of_relative
      (X := X) (Y := X × Q) (ι := ULift.{u} (Fin (r + 1)))
      R π d c A top n ?_ g hg hformula
    intro k
    -- The two subtype sums differ only in the chosen finite enumeration.
    convert hOld k using 1
    funext a
    congr 4
    dsimp only [old]
    congr 1
    exact Subsingleton.elim _ _

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

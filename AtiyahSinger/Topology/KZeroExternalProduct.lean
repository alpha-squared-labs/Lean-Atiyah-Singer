/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KZeroProduct

/-!
# The external product on absolute complex K⁰

Public module ID: M1921.

Pull back along the two actual projections and multiply by the
idempotent tensor product. Hatcher, Vector Bundles and K-Theory, §2.1, pp.40–41,
gives this construction. Both bases here are compact Hausdorff. Compact supports
on noncompact bases require a separate smash-product construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TopologicalSpace X'] [CompactSpace X'] [T2Space X']
  [TopologicalSpace Y'] [CompactSpace Y'] [T2Space Y']

/-- The external product of absolute classes is the tensor product of their pullbacks. -/
def complexKZeroExternalProduct : ComplexKZero X →+ ComplexKZero Y →+ ComplexKZero (X × Y) :=
  (AddMonoidHom.compHom' (complexKZeroPullback (ContinuousMap.snd : C(X × Y, Y)))).comp
      ((kZeroMul C(X × Y, ℂ)).comp
        (complexKZeroPullback (ContinuousMap.fst : C(X × Y, X))))

/-- External product is natural for the specified product of continuous maps. -/
theorem complexKZeroExternalProduct_natural (f : C(X', X)) (g : C(Y', Y))
    (a : ComplexKZero X) (b : ComplexKZero Y) :
    complexKZeroPullback (f.prodMap g) (complexKZeroExternalProduct a b) =
      complexKZeroExternalProduct (complexKZeroPullback f a) (complexKZeroPullback g b) := by
  /- Stage 1: compose each projection with f × g; these composites are f after
  the first projection and g after the second projection.
  Stage 2: apply the multiplicativity of the actual ring-induced K₀ map and
  pullback composition. This preserves the chosen tensor product on both sides. -/
  -- Pullback preserves the product of the two projected classes.
  change kZeroMap _ (kZeroMul _ _ _) = _
  rw [kZeroMap_mul]
  -- Both projection squares commute as actual continuous maps.
  have hfst : (ContinuousMap.fst : C(X × Y, X)).comp (f.prodMap g) =
      f.comp (ContinuousMap.fst : C(X' × Y', X')) := rfl
  have hsnd : (ContinuousMap.snd : C(X × Y, Y)).comp (f.prodMap g) =
      g.comp (ContinuousMap.snd : C(X' × Y', Y')) := rfl
  change kZeroMul _
    (complexKZeroPullback (f.prodMap g) (complexKZeroPullback ContinuousMap.fst a))
    (complexKZeroPullback (f.prodMap g) (complexKZeroPullback ContinuousMap.snd b)) = _
  have hpull_fst : complexKZeroPullback (f.prodMap g)
      (complexKZeroPullback ContinuousMap.fst a) =
      complexKZeroPullback ContinuousMap.fst (complexKZeroPullback f a) := by
    change ((complexKZeroPullback (f.prodMap g)).comp
      (complexKZeroPullback ContinuousMap.fst)) a = _
    rw [← complexKZeroPullback_comp, hfst, complexKZeroPullback_comp]
    rfl
  have hpull_snd : complexKZeroPullback (f.prodMap g)
      (complexKZeroPullback ContinuousMap.snd b) =
      complexKZeroPullback ContinuousMap.snd (complexKZeroPullback g b) := by
    change ((complexKZeroPullback (f.prodMap g)).comp
      (complexKZeroPullback ContinuousMap.snd)) b = _
    rw [← complexKZeroPullback_comp, hsnd, complexKZeroPullback_comp]
    rfl
  rw [hpull_fst, hpull_snd]
  rfl

/-- Interchanging the two factors interchanges the even external product. -/
theorem complexKZeroExternalProduct_swap (a : ComplexKZero X) (b : ComplexKZero Y) :
    complexKZeroPullback (ContinuousMap.prodSwap : C(X × Y, Y × X))
      (complexKZeroExternalProduct b a) = complexKZeroExternalProduct a b := by
  /- The swap interchanges the two actual projections. Pullback preserves
  multiplication, and tensor symmetry makes the two resulting factors commute.
  These are degree-zero groups; there is no odd-degree sign in this statement. -/
  -- Multiplicativity transports the two factors through the same swap map.
  change kZeroMap _ (kZeroMul _ _ _) = _
  rw [kZeroMap_mul]
  change kZeroMul _
    (complexKZeroPullback ContinuousMap.prodSwap (complexKZeroPullback ContinuousMap.fst b))
    (complexKZeroPullback ContinuousMap.prodSwap (complexKZeroPullback ContinuousMap.snd a)) = _
  have hfst := DFunLike.congr_fun
    (complexKZeroPullback_comp (ContinuousMap.prodSwap : C(X × Y, Y × X))
      (ContinuousMap.fst : C(Y × X, Y))) b
  have hsnd := DFunLike.congr_fun
    (complexKZeroPullback_comp (ContinuousMap.prodSwap : C(X × Y, Y × X))
      (ContinuousMap.snd : C(Y × X, X))) a
  simp only [AddMonoidHom.comp_apply] at hfst hsnd
  rw [← hfst, ← hsnd]
  -- The resulting degree-zero factors commute, without a grading sign.
  exact kZeroMul_comm _ _

end AtiyahSinger

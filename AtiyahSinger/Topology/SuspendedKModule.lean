/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportModule
public import AtiyahSinger.Topology.SuspendedKTheory

/-!
# Multiplication by a degree-zero class in every suspended degree

Public module ID: M2221.

SG Appendix C.1 constructs the graded module multiplication by an external
product and a proper graph pullback. For the existing negative-degree model
`CompactSupportK n X = CompactSupportKZero (X × (Fin n → ℝ))`, this file fixes
the actual map on the suspension coordinate: `(y,t) ↦ ((f(y),t),y)`.
The suspension coordinate remains attached to the first factor throughout.

The graph is proper because the continuous map `((x,t),y) ↦ (y,t)` is its
retraction and the target is Hausdorff. The map f itself need not be proper.
The second K-class has degree zero; no interchange of two suspended factors,
Koszul sign, or arbitrary choice of a suspension isomorphism is involved.

Associativity, proper-pullback naturality and degree-zero comparison retain
these exact maps. They supply the standard operation used to state that one
degree-zero orientation class induces isomorphisms in all nonpositive degrees.
They do not assert a general fully graded product or a Mayer--Vietoris sequence.
Sources: Spin Geometry, Appendix C.1--C.2; Karoubi, K-Theory, IV.1.2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y Z : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]

/-- SG C.1: the suspended class acts on a degree-zero class through the proper graph. -/
def compactSupportKAction (n : ℕ) (f : C(Y, X)) :
    CompactSupportK n X →+ CompactSupportKZero Y →+ CompactSupportK n Y :=
  let graph : C(Y × (Fin n → ℝ), (X × (Fin n → ℝ)) × Y) :=
    (f.prodMap (ContinuousMap.id (Fin n → ℝ))).prodMk ContinuousMap.fst
  let retract : C((X × (Fin n → ℝ)) × Y, Y × (Fin n → ℝ)) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  compactSupportKZeroExternalProduct.compr₂
    (compactSupportKZeroPullback graph
      (isProperMap_of_comp_of_t2 graph.continuous retract.continuous isProperMap_id))

/-- Successive graph actions associate without changing the suspended coordinate. -/
theorem compactSupportKAction_assoc (n : ℕ) (f : C(Y, X)) (g : C(Z, Y))
    (a : CompactSupportK n X) (b : CompactSupportKZero Y) (c : CompactSupportKZero Z) :
    compactSupportKAction n g (compactSupportKAction n f a b) c =
      compactSupportKAction n (f.comp g) a (compactSupportKZeroAction g b c) := by
  /- Stage 1: expand both actions into the specified external products and graph
  pullbacks. Proper pullback commutes with the external product by comparing the
  same one-point extensions and the defining reduced smash-lift identities.
  Stage 2: the external-product associator only changes parentheses in the three
  factors X×R^n, Y and Z. Both resulting pullbacks evaluate the same class along
  (z,t) ↦ ((f(g(z)),t),g(z),z), with the indicated parentheses on each side.
  Stage 3: this graph is proper because projecting back to (z,t) retracts it.
  Proper-pullback composition and external-product associativity therefore give
  equality for the specified actions. The coordinate t never moves past another
  suspended factor: b and c have degree zero, so no graded sign is introduced. -/
  let T := Fin n → ℝ
  let F : C(Y × T, (X × T) × Y) :=
    (f.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let G : C(Z × T, (Y × T) × Z) :=
    (g.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let H : C(Z × T, (X × T) × Z) :=
    ((f.comp g).prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let Q : C(Z, Y × Z) := g.prodMk (ContinuousMap.id Z)
  let rY : C((X × T) × Y, Y × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  let rZ : C((Y × T) × Z, Z × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  let rH : C((X × T) × Z, Z × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous rY.continuous isProperMap_id
  have hG : IsProperMap G :=
    isProperMap_of_comp_of_t2 G.continuous rZ.continuous isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous rH.continuous isProperMap_id
  have hQ : IsProperMap Q :=
    isProperMap_of_comp_of_t2 Q.continuous continuous_snd isProperMap_id
  have hIX : IsProperMap (ContinuousMap.id (X × T)) := isProperMap_id
  have hIZ : IsProperMap (ContinuousMap.id Z) := isProperMap_id
  -- Move the two proper graphs through the original external products.
  have hleft := compactSupportKZeroExternalProduct_properPullback F hF
    (ContinuousMap.id Z) hIZ (compactSupportKZeroExternalProduct a b) c
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hleft
  have hright := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id (X × T)) hIX Q hQ a (compactSupportKZeroExternalProduct b c)
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hright
  change compactSupportKZeroPullback G hG
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroPullback F hF (compactSupportKZeroExternalProduct a b)) c) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroExternalProduct a
        (compactSupportKZeroPullback Q hQ (compactSupportKZeroExternalProduct b c)))
  rw [← hleft, ← hright, ← compactSupportKZeroExternalProduct_assoc a b c]
  -- Reassociation changes parentheses only; the same real vector stays with X.
  let L : C((Y × T) × Z, ((X × T) × Y) × Z) := F.prodMap (ContinuousMap.id Z)
  let R : C((X × T) × Z, (X × T) × (Y × Z)) :=
    (ContinuousMap.id (X × T)).prodMap Q
  let r : C((X × T) × (Y × Z), ((X × T) × Y) × Z) :=
    ⟨(Homeomorph.prodAssoc (X × T) Y Z).symm,
      (Homeomorph.prodAssoc (X × T) Y Z).symm.continuous⟩
  have hL : IsProperMap L := hF.prodMap hIZ
  have hR : IsProperMap R := hIX.prodMap hQ
  have hr : IsProperMap r := (Homeomorph.prodAssoc (X × T) Y Z).symm.isProperMap
  let t := compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) c
  change compactSupportKZeroPullback G hG (compactSupportKZeroPullback L hL t) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroPullback R hR (compactSupportKZeroPullback r hr t))
  calc
    _ = compactSupportKZeroPullback (L.comp G) (hL.comp hG) t :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp G L hG hL) t).symm
    _ = compactSupportKZeroPullback (r.comp (R.comp H)) (hr.comp (hR.comp hH)) t := by
      -- Both maps send (z,t) to (((f(g(z)),t),g(z)),z).
      rfl
    _ = _ := by
      rw [compactSupportKZeroPullback_comp (R.comp H) r (hR.comp hH) hr,
        AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp H R hH hR,
        AddMonoidHom.comp_apply]

/-- Proper pullback preserves the suspended action of the same original base class. -/
theorem compactSupportKPullback_action (n : ℕ) (f : C(Y, X)) (g : C(Z, Y))
    (hg : IsProperMap g) (a : CompactSupportK n X) (b : CompactSupportKZero Y) :
    compactSupportKPullback n g hg (compactSupportKAction n f a b) =
      compactSupportKAction n (f.comp g) a (compactSupportKZeroPullback g hg b) := by
  /- Stage 1: suspended pullback is the original compact-support pullback along
  g×id_R^n. The two graph maps and id_(X×R^n)×g form a commuting square: both
  composites send (z,t) to ((f(g(z)),t),g(z)). The latter product map is proper
  because g is proper; no properness hypothesis is imposed on f.
  Stage 2: external-product naturality for these proper maps follows from their
  actual one-point extensions and the same reduced smash-lift characterization.
  Apply proper-pullback composition to the commuting square. Its two sides are
  exactly the displayed operations, retaining both the suspension coordinate and
  the original unsuspended pullback of b. -/
  let T := Fin n → ℝ
  let F : C(Y × T, (X × T) × Y) :=
    (f.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let H : C(Z × T, (X × T) × Z) :=
    ((f.comp g).prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let rY : C((X × T) × Y, Y × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  let rZ : C((X × T) × Z, Z × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous rY.continuous isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous rZ.continuous isProperMap_id
  let G := g.prodMap (ContinuousMap.id T)
  have hG : IsProperMap G := hg.prodMap isProperMap_id
  have hI : IsProperMap (ContinuousMap.id (X × T)) := isProperMap_id
  -- The product map is proper because g is; f itself remains arbitrary continuous.
  have hproduct := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id (X × T)) hI g hg a b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKZeroPullback G hG
      (compactSupportKZeroPullback F hF (compactSupportKZeroExternalProduct a b)) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroExternalProduct a (compactSupportKZeroPullback g hg b))
  rw [← hproduct]
  let L : C((X × T) × Z, (X × T) × Y) := (ContinuousMap.id (X × T)).prodMap g
  have hL : IsProperMap L := hI.prodMap hg
  let t := compactSupportKZeroExternalProduct a b
  -- The graph square retains the original g(z) and the same real coordinate.
  calc
    _ = compactSupportKZeroPullback (F.comp G) (hF.comp hG) t :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp G F hG hF) t).symm
    _ = compactSupportKZeroPullback (L.comp H) (hL.comp hH) t := by rfl
    _ = _ := DFunLike.congr_fun (compactSupportKZeroPullback_comp H L hH hL) t

/-- The fixed zero-dimensional suspension comparison recovers the original graph action. -/
theorem compactSupportKAction_zero (f : C(Y, X))
    (a : CompactSupportK 0 X) (b : CompactSupportKZero Y) :
    compactSupportKZeroDegreeEquiv Y (compactSupportKAction 0 f a b) =
      compactSupportKZeroAction f (compactSupportKZeroDegreeEquiv X a) b := by
  /- Stage 1: Fin 0 → ℝ has one point. The fixed zero-degree equivalence is
  covariant transport along the actual projection X×(Fin 0→ℝ) ≃ X, and similarly
  for Y. These homeomorphisms take the suspended graph to y ↦ (f(y),y) while
  retaining its unsuspended second factor.
  Stage 2: apply external-product homeomorphism naturality and proper-pullback
  composition to this commuting square. The definition of compactSupportKAction
  then becomes the already specified compactSupportKZeroAction. This comparison
  concerns the original operations, not merely the existence of isomorphic groups. -/
  let T := Fin 0 → ℝ
  let eX := Homeomorph.prodUnique X T
  let eY := Homeomorph.prodUnique Y T
  let jX : C(X, X × T) := ⟨eX.symm, eX.symm.continuous⟩
  let jY : C(Y, Y × T) := ⟨eY.symm, eY.symm.continuous⟩
  let F : C(Y × T, (X × T) × Y) :=
    (f.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let H : C(Y, X × Y) := f.prodMk (ContinuousMap.id Y)
  let r : C((X × T) × Y, Y × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous r.continuous isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous continuous_snd isProperMap_id
  have hI : IsProperMap (ContinuousMap.id Y) := isProperMap_id
  -- Insert the unique empty tuple in the first factor of the same external product.
  have hproduct := compactSupportKZeroExternalProduct_properPullback
    jX eX.symm.isProperMap (ContinuousMap.id Y) hI a b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKZeroPullback jY eY.symm.isProperMap
      (compactSupportKZeroPullback F hF (compactSupportKZeroExternalProduct a b)) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroPullback jX eX.symm.isProperMap a) b)
  rw [← hproduct]
  let L := jX.prodMap (ContinuousMap.id Y)
  have hL : IsProperMap L := eX.symm.isProperMap.prodMap hI
  let t := compactSupportKZeroExternalProduct a b
  -- Both composites send y to ((f(y),the empty tuple),y).
  calc
    _ = compactSupportKZeroPullback (F.comp jY) (hF.comp eY.symm.isProperMap) t :=
      (DFunLike.congr_fun
        (compactSupportKZeroPullback_comp jY F eY.symm.isProperMap hF) t).symm
    _ = compactSupportKZeroPullback (L.comp H) (hL.comp hH) t := by rfl
    _ = _ := DFunLike.congr_fun (compactSupportKZeroPullback_comp H L hH hL) t

end AtiyahSinger

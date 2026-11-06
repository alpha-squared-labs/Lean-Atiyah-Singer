/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GradedKProduct
public import AtiyahSinger.Topology.GradedKProductNaturality
public import AtiyahSinger.Topology.SuspendedKModule

/-!
# The fully graded compact-support action along a continuous map

Public module ID: M1869.

SG Appendix C.1 constructs the graded multiplication along a continuous
map f : Y -> X by taking an external product and pulling back along its graph.
Here the two classes have degrees -m and -n. Their actual external product uses
the fixed ordered suspension blocks, and its pullback uses the proper graph
y -> (f(y), y), together with the identity on those same m+n real coordinates.
The map f itself need not be proper: projection to Y retracts its graph.

Associativity retains the order of all three suspension blocks; the displayed
degree transport only changes the parentheses in their lengths. No interchange
of suspension blocks or graded sign occurs in that law. Proper-pullback
naturality uses the original map on the second base and its actual suspension.
The n=0 comparison removes the unique empty block and recovers the already
defined action on an unsuspended compact-support class.

Sources: Lawson--Michelsohn, Spin Geometry, Appendix C.1; Karoubi, K-Theory,
IV.1.2, together with the degree-zero graph action. The
parameters count suspensions and represent nonpositive cohomological degrees.
The construction introduces no Bott-periodicity choice or artificial unit on a
noncompact base. The three original laws are proved below for these same maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y Z : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]

/-- SG C.1: the fully graded action is the original external product pulled back by the graph. -/
def compactSupportKGradedAction (m n : ℕ) (f : C(Y, X)) :
    CompactSupportK m X →+ CompactSupportK n Y →+ CompactSupportK (m + n) Y :=
  (compactSupportKExternalProduct m n).compr₂
    (compactSupportKPullback (m + n) (f.prodMk (ContinuousMap.id Y))
      (isProperMap_of_comp_of_t2 (f.continuous.prodMk continuous_id)
        continuous_snd isProperMap_id))

/-- Graded graph actions associate with the specified transport of the total degree. -/
theorem compactSupportKGradedAction_assoc (m n p : ℕ) (f : C(Y, X)) (g : C(Z, Y))
    (a : CompactSupportK m X) (b : CompactSupportK n Y) (c : CompactSupportK p Z) :
    compactSupportKDegreeCongr Z (Nat.add_assoc m n p)
        (compactSupportKGradedAction (m + n) p g
          (compactSupportKGradedAction m n f a b) c) =
      compactSupportKGradedAction m (n + p) (f.comp g) a
        (compactSupportKGradedAction n p g b c) := by
  /- Stage 1: expand both actions into the original graded external product
  and suspended proper-graph pullback. External-product naturality moves the
  two graph pullbacks to the common threefold product. All maps used for these
  pullbacks are proper graphs or products of proper graphs with identities;
  properness of f or g is not required.
  Stage 2: the underlying threefold graph is z -> (f(g(z)),g(z),z).
  Both coordinate constructions append the m-block, the n-block and the p-block
  in this order. Their change of parentheses is exactly the product associator
  together with the reindexing given by Nat.add_assoc. Thus no suspended block
  crosses another block, and no graded commutativity sign enters the formula.
  Stage 3: apply external-product associativity and proper-pullback composition
  to these same maps. The degree equality transports the left result to the
  right result's actual group, giving the stated identity. This also covers
  empty bases and zero-length blocks, without invoking periodicity. -/
  let S := Fin m → ℝ
  let T := Fin n → ℝ
  let U := Fin p → ℝ
  let F := f.prodMk (ContinuousMap.id Y)
  let G := g.prodMk (ContinuousMap.id Z)
  let Q := (f.comp g).prodMk (ContinuousMap.id Z)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous continuous_snd isProperMap_id
  have hG : IsProperMap G :=
    isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
  have hQ : IsProperMap Q :=
    isProperMap_of_comp_of_t2 Q.continuous continuous_snd isProperMap_id
  let eF := suspendedProductHomeomorph m n X Y
  let eL := suspendedProductHomeomorph (m + n) p Y Z
  let eG := suspendedProductHomeomorph n p Y Z
  let eR := suspendedProductHomeomorph m (n + p) X Z
  let jF : C((X × Y) × (Fin (m + n) → ℝ), (X × S) × (Y × T)) :=
    ⟨eF.symm, eF.symm.continuous⟩
  let jL : C((Y × Z) × (Fin ((m + n) + p) → ℝ),
      (Y × (Fin (m + n) → ℝ)) × (Z × U)) := ⟨eL.symm, eL.symm.continuous⟩
  let jG : C((Y × Z) × (Fin (n + p) → ℝ), (Y × T) × (Z × U)) :=
    ⟨eG.symm, eG.symm.continuous⟩
  let jR : C((X × Z) × (Fin (m + (n + p)) → ℝ),
      (X × S) × (Z × (Fin (n + p) → ℝ))) := ⟨eR.symm, eR.symm.continuous⟩
  let u := jF.comp (F.prodMap (ContinuousMap.id (Fin (m + n) → ℝ)))
  let v := jL.comp (G.prodMap (ContinuousMap.id (Fin ((m + n) + p) → ℝ)))
  let w := jG.comp (G.prodMap (ContinuousMap.id (Fin (n + p) → ℝ)))
  let r := jR.comp (Q.prodMap (ContinuousMap.id (Fin (m + (n + p)) → ℝ)))
  have hu : IsProperMap u := eF.symm.isProperMap.comp (hF.prodMap isProperMap_id)
  have hv : IsProperMap v := eL.symm.isProperMap.comp (hG.prodMap isProperMap_id)
  have hw : IsProperMap w := eG.symm.isProperMap.comp (hG.prodMap isProperMap_id)
  have hr : IsProperMap r := eR.symm.isProperMap.comp (hQ.prodMap isProperMap_id)
  -- Combine each prescribed graph with its own ordered-coordinate comparison.
  have hfa : compactSupportKGradedAction m n f a b =
      compactSupportKZeroPullback u hu (compactSupportKZeroExternalProduct a b) :=
    (DFunLike.congr_fun (compactSupportKZeroPullback_comp
      (F.prodMap (ContinuousMap.id (Fin (m + n) → ℝ))) jF
      (hF.prodMap isProperMap_id) eF.symm.isProperMap)
      (compactSupportKZeroExternalProduct a b)).symm
  have hleft (d : CompactSupportK (m + n) Y) :
      compactSupportKGradedAction (m + n) p g d c =
        compactSupportKZeroPullback v hv (compactSupportKZeroExternalProduct d c) :=
    (DFunLike.congr_fun (compactSupportKZeroPullback_comp
      (G.prodMap (ContinuousMap.id (Fin ((m + n) + p) → ℝ))) jL
      (hG.prodMap isProperMap_id) eL.symm.isProperMap)
      (compactSupportKZeroExternalProduct d c)).symm
  have hgc : compactSupportKGradedAction n p g b c =
      compactSupportKZeroPullback w hw (compactSupportKZeroExternalProduct b c) :=
    (DFunLike.congr_fun (compactSupportKZeroPullback_comp
      (G.prodMap (ContinuousMap.id (Fin (n + p) → ℝ))) jG
      (hG.prodMap isProperMap_id) eG.symm.isProperMap)
      (compactSupportKZeroExternalProduct b c)).symm
  have hright (d : CompactSupportK (n + p) Z) :
      compactSupportKGradedAction m (n + p) (f.comp g) a d =
        compactSupportKZeroPullback r hr (compactSupportKZeroExternalProduct a d) :=
    (DFunLike.congr_fun (compactSupportKZeroPullback_comp
      (Q.prodMap (ContinuousMap.id (Fin (m + (n + p)) → ℝ))) jR
      (hQ.prodMap isProperMap_id) eR.symm.isProperMap)
      (compactSupportKZeroExternalProduct a d)).symm
  -- An equality of degrees is just reindexing the same tuple, with no permutation.
  have hdegree (i j : ℕ) (h : i = j) (d : CompactSupportK i Z) :
      compactSupportKDegreeCongr Z h d = compactSupportKZeroHomeomorph
        ((Homeomorph.refl Z).prodCongr
          (Homeomorph.piCongrLeft (Y := fun _ : Fin j ↦ ℝ) (finCongr h))) d := by
    subst j
    simp only [finCongr_refl, Homeomorph.piCongrLeft_refl]
    change d = compactSupportKZeroPullback (ContinuousMap.id _) isProperMap_id d
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  let e := (Homeomorph.refl Z).prodCongr
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (m + (n + p)) ↦ ℝ)
      (finCongr (Nat.add_assoc m n p)))
  let J : C(Z × (Fin (m + (n + p)) → ℝ), Z × (Fin ((m + n) + p) → ℝ)) :=
    ⟨e.symm, e.symm.continuous⟩
  let L := u.prodMap (ContinuousMap.id (Z × U))
  let R := (ContinuousMap.id (X × S)).prodMap w
  let A : C((X × S) × ((Y × T) × (Z × U)), ((X × S) × (Y × T)) × (Z × U)) :=
    ⟨(Homeomorph.prodAssoc (X × S) (Y × T) (Z × U)).symm,
      (Homeomorph.prodAssoc (X × S) (Y × T) (Z × U)).symm.continuous⟩
  have hL : IsProperMap L := hu.prodMap isProperMap_id
  have hR : IsProperMap R := isProperMap_id.prodMap hw
  have hA : IsProperMap A :=
    (Homeomorph.prodAssoc (X × S) (Y × T) (Z × U)).symm.isProperMap
  have hLP := compactSupportKZeroExternalProduct_properPullback
    u hu (ContinuousMap.id (Z × U)) isProperMap_id
    (compactSupportKZeroExternalProduct a b) c
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hLP
  have hRP := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id (X × S)) isProperMap_id w hw a
    (compactSupportKZeroExternalProduct b c)
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hRP
  rw [hdegree, hleft, hfa, hright, hgc, ← hLP, ← hRP,
    ← compactSupportKZeroExternalProduct_assoc a b c]
  let t := compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) c
  change compactSupportKZeroPullback J e.symm.isProperMap
      (compactSupportKZeroPullback v hv (compactSupportKZeroPullback L hL t)) =
    compactSupportKZeroPullback r hr
      (compactSupportKZeroPullback R hR (compactSupportKZeroPullback A hA t))
  have hsquare : L.comp (v.comp J) = A.comp (R.comp r) := by
    apply ContinuousMap.ext
    rintro ⟨z, s⟩
    refine Prod.ext (Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)) (Prod.ext rfl ?_)
    · funext i
      change s (Fin.cast (Nat.add_assoc m n p) (Fin.castAdd p (Fin.castAdd n i))) =
        s (Fin.castAdd (n + p) i)
      rfl
    · funext i
      change s (Fin.cast (Nat.add_assoc m n p) (Fin.castAdd p (Fin.natAdd m i))) =
        s (Fin.natAdd m (Fin.castAdd p i))
      rfl
    · funext i
      change s (Fin.cast (Nat.add_assoc m n p) (Fin.natAdd (m + n) i)) =
        s (Fin.natAdd m (Fin.natAdd n i))
      congr 1
      exact Fin.ext (Nat.add_assoc m n i.val)
  -- These composites retain (f(g(z)),g(z),z) and each of the three original blocks.
  calc
    _ = compactSupportKZeroPullback (L.comp (v.comp J))
        (hL.comp (hv.comp e.symm.isProperMap)) t := by
      rw [compactSupportKZeroPullback_comp (v.comp J) L
          (hv.comp e.symm.isProperMap) hL,
        AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp J v e.symm.isProperMap hv,
        AddMonoidHom.comp_apply]
    _ = compactSupportKZeroPullback (A.comp (R.comp r)) (hA.comp (hR.comp hr)) t := by
      simp only [hsquare]
    _ = _ := by
      rw [compactSupportKZeroPullback_comp (R.comp r) A (hR.comp hr) hA,
        AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp r R hr hR,
        AddMonoidHom.comp_apply]

/-- Proper pullback in the second base preserves the fully graded graph action. -/
theorem compactSupportKPullback_gradedAction (m n : ℕ) (f : C(Y, X)) (g : C(Z, Y))
    (hg : IsProperMap g) (a : CompactSupportK m X) (b : CompactSupportK n Y) :
    compactSupportKPullback (m + n) g hg (compactSupportKGradedAction m n f a b) =
      compactSupportKGradedAction m n (f.comp g) a (compactSupportKPullback n g hg b) := by
  /- Stage 1: the square formed by the graphs of f and f composed with g,
  the map g and the product id_X times g commutes on the original bases.
  The product map is proper because g is proper. Suspending the square by
  the identity on the same m+n coordinates preserves both commutativity
  and properness.
  Stage 2: the external product is natural for these proper maps. Its
  specified coordinate homeomorphism leaves the m-block fixed and carries
  the pullback of b along g with its original n-block. Apply proper-pullback
  composition to the commuting square. The resulting maps are precisely
  the two sides displayed above, with no pullback of a along f alone. -/
  let F := f.prodMk (ContinuousMap.id Y)
  let H := (f.comp g).prodMk (ContinuousMap.id Z)
  let L := (ContinuousMap.id X).prodMap g
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous continuous_snd isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous continuous_snd isProperMap_id
  have hI : IsProperMap (ContinuousMap.id X) := isProperMap_id
  have hL : IsProperMap L := hI.prodMap hg
  -- Move the original pullback of b through the actual graded external product.
  have hproduct := compactSupportKExternalProduct_properPullback m n
    (ContinuousMap.id X) hI g hg a b
  rw [compactSupportKPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKPullback (m + n) g hg
      (compactSupportKPullback (m + n) F hF
        (compactSupportKExternalProduct m n a b)) =
    compactSupportKPullback (m + n) H hH
      (compactSupportKExternalProduct m n a (compactSupportKPullback n g hg b))
  rw [← hproduct]
  let t := compactSupportKExternalProduct m n a b
  -- The two composites both send z to (f(g(z)),g(z)), keeping every real coordinate.
  calc
    _ = compactSupportKPullback (m + n) (F.comp g) (hF.comp hg) t :=
      (DFunLike.congr_fun (compactSupportKPullback_comp (m + n) g F hg hF) t).symm
    _ = compactSupportKPullback (m + n) (L.comp H) (hL.comp hH) t := by rfl
    _ = _ := DFunLike.congr_fun
      (compactSupportKPullback_comp (m + n) H L hH hL) t

/-- Removing the empty second suspension block recovers the existing suspended action. -/
theorem compactSupportKGradedAction_zero_right (m : ℕ) (f : C(Y, X))
    (a : CompactSupportK m X) (b : CompactSupportK 0 Y) :
    compactSupportKDegreeCongr Y (Nat.add_zero m)
        (compactSupportKGradedAction m 0 f a b) =
      compactSupportKAction m f a (compactSupportKZeroDegreeEquiv Y b) := by
  /- Stage 1: the specified zero-degree comparison removes the unique
  empty tuple in Y times R^0. The ordered-coordinate homeomorphism for
  the (m,0) external product therefore retains exactly the m coordinates
  of a; Nat.add_zero transports their index set to the original Fin m.
  Stage 2: after these coordinate identifications, the suspended graph
  y,t -> ((f(y),y),t) becomes (y,t) -> ((f(y),t),y). This is the actual
  proper graph used in compactSupportKAction, not an arbitrarily chosen
  isomorphism of the resulting groups.
  Stage 3: external-product homeomorphism naturality and proper-pullback
  composition identify the two constructions. The same specified
  compactSupportKZeroDegreeEquiv is applied only to the second class,
  so the conclusion also retains the original suspended first class. -/
  let S := Fin m → ℝ
  let T := Fin 0 → ℝ
  let j : C(Y, Y × T) :=
    ⟨(Homeomorph.prodUnique Y T).symm, (Homeomorph.prodUnique Y T).symm.continuous⟩
  let e := suspendedProductHomeomorph m 0 X Y
  let q : C((X × Y) × S, (X × S) × (Y × T)) := ⟨e.symm, e.symm.continuous⟩
  let G : C(Y × S, (X × Y) × S) :=
    (f.prodMk (ContinuousMap.id Y)).prodMap (ContinuousMap.id S)
  let H : C(Y × S, (X × S) × Y) :=
    (f.prodMap (ContinuousMap.id S)).prodMk ContinuousMap.fst
  let L := (ContinuousMap.id (X × S)).prodMap j
  let retract : C((X × S) × Y, Y × S) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  have hF : IsProperMap (f.prodMk (ContinuousMap.id Y)) :=
    isProperMap_of_comp_of_t2 (f.continuous.prodMk continuous_id)
      continuous_snd isProperMap_id
  have hG : IsProperMap G := hF.prodMap isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous retract.continuous isProperMap_id
  have hI : IsProperMap (ContinuousMap.id (X × S)) := isProperMap_id
  have hL : IsProperMap L := hI.prodMap (Homeomorph.prodUnique Y T).symm.isProperMap
  -- Insert the unique empty tuple only in the coefficient class, as prescribed.
  have hproduct := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id (X × S)) hI j (Homeomorph.prodUnique Y T).symm.isProperMap a b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKZeroPullback G hG
      (compactSupportKZeroPullback q e.symm.isProperMap
        (compactSupportKZeroExternalProduct a b)) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroExternalProduct a
        (compactSupportKZeroPullback j (Homeomorph.prodUnique Y T).symm.isProperMap b))
  rw [← hproduct]
  let t := compactSupportKZeroExternalProduct a b
  have hsquare : q.comp G = L.comp H := by
    -- Fin.castAdd 0 retains every original coordinate; the other block is empty.
    apply ContinuousMap.ext
    intro z
    refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
    · rfl
    · exact Subsingleton.elim _ _
  calc
    _ = compactSupportKZeroPullback (q.comp G) (e.symm.isProperMap.comp hG) t :=
      (DFunLike.congr_fun
        (compactSupportKZeroPullback_comp G q hG e.symm.isProperMap) t).symm
    _ = compactSupportKZeroPullback (L.comp H) (hL.comp hH) t := by simp only [hsquare]
    _ = _ := DFunLike.congr_fun (compactSupportKZeroPullback_comp H L hH hL) t

end AtiyahSinger

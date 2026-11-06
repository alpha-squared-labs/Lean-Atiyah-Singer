/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportProductNaturality
public import AtiyahSinger.Topology.GradedKProduct

/-!
# Proper pullback and open extension of the full graded K-product

Public module ID: M1872.

The product in degrees -m and -n is the specified degree-zero product on the
two suspended spaces, with its real blocks concatenated in their original order.
Proper pullback and open pushforward retain those same coordinates. The latter
is the original degree-zero open pushforward along f times identity, and agrees
with the already defined open extension for an actual open subset inclusion.

Sources: Spin Geometry, Appendix C.1 and I.9.26; Karoubi, K-Theory, II.5.21--5.22,
for products, proper maps and open extension, applied to the standard suspended
groups. Open embeddings need not be proper. Conversely, a general continuous
map does not give compact-support pullback without the properness hypothesis.
No compactness, connectedness, nonemptiness or CW hypothesis is added.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

variable {X X' Y Y' : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace X'] [LocallyCompactSpace X'] [T2Space X']
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Y'] [LocallyCompactSpace Y'] [T2Space Y']

/-- Open pushforward in degree -n retains the original embedding and all real coordinates. -/
def compactSupportKOpenPushforward (n : ℕ) (f : X → Y) (hf : IsOpenEmbedding f) :
    CompactSupportK n X →+ CompactSupportK n Y :=
  compactSupportKZeroOpenPushforward (Prod.map f (id : (Fin n → ℝ) → (Fin n → ℝ)))
    (hf.prodMap IsOpenEmbedding.id)

/-- For an actual open subset, suspended pushforward is the original suspended open extension. -/
theorem compactSupportKOpenPushforward_subtype_val (n : ℕ) (U : Set X) (hU : IsOpen U) :
    letI := hU.locallyCompactSpace
    compactSupportKOpenPushforward n (Subtype.val : U → X) hU.isOpenEmbedding_subtypeVal =
      compactSupportKOpenExtension n U hU := by
  /- Stage 1: the image of the suspended inclusion is exactly the inverse image
  of U under the first projection. Its homeomorphism onto that image retains
  the point of U and all n real coordinates, as does subspaceProdHomeomorph.
  Stage 2: the two actual one-point collapse maps therefore agree at finite
  points and infinity. Apply degree-zero open-pushforward composition and
  its homeomorphism formula to obtain the existing suspended extension. -/
  let := hU.locallyCompactSpace
  let T := Fin n → ℝ
  let U' : Set (X × T) := Prod.fst ⁻¹' U
  let hU' : IsOpen U' := hU.preimage continuous_fst
  let := hU'.locallyCompactSpace
  let e := subspaceProdHomeomorph U T
  let j : U' → X × T := Subtype.val
  have hj : IsOpenEmbedding j := hU'.isOpenEmbedding_subtypeVal
  -- The suspended inclusion factors through the exact product-subspace homeomorphism.
  have hcomp := compactSupportKZeroOpenPushforward_comp e e.isOpenEmbedding j hj
  have hinclusion : compactSupportKZeroOpenPushforward j hj =
      compactSupportKZeroOpenExtension U' hU' := by
    -- On the actual subspace the range collapse returns exactly the same original point.
    let := hj.isOpen_range.locallyCompactSpace
    let er := hj.isEmbedding.toHomeomorph
    let i : C(Set.range j, U') := ⟨er.symm, er.symm.continuous⟩
    let c : C(OnePoint (X × T), OnePoint (Set.range j)) :=
      ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
    let d : C(OnePoint (X × T), OnePoint U') :=
      ⟨onePointCollapse U', continuous_onePointCollapse _ hU'⟩
    have hmap : (properOnePointMap i er.symm.isProperMap).comp c = d := by
      ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe x =>
        by_cases hx : x ∈ U'
        · have hrange : x ∈ Set.range j := ⟨⟨x, hx⟩, rfl⟩
          change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U' x
          rw [onePointCollapse_coe_of_mem _ _ hrange,
            onePointCollapse_coe_of_mem _ _ hx, OnePoint.map_some]
          apply congrArg OnePoint.some
          apply Subtype.ext
          exact congrArg (fun z : Set.range j ↦ z.val) (er.apply_symm_apply ⟨x, hrange⟩)
        · have hrange : x ∉ Set.range j := by
            rintro ⟨x', rfl⟩
            exact hx x'.property
          change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U' x
          rw [onePointCollapse_coe_of_notMem _ _ hrange,
            onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
    apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    change complexKZeroPullback c
      (complexKZeroPullback (properOnePointMap i er.symm.isProperMap) a.val) =
      complexKZeroPullback d a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  rw [hinclusion, compactSupportKZeroOpenPushforward_homeomorph] at hcomp
  exact hcomp

/-- Proper pullback preserves the full external product in both suspended degrees. -/
theorem compactSupportKExternalProduct_properPullback (m n : ℕ)
    (f : C(X, X')) (hf : IsProperMap f) (g : C(Y, Y')) (hg : IsProperMap g)
    (a : CompactSupportK m X') (b : CompactSupportK n Y') :
    compactSupportKPullback (m + n) (f.prodMap g) (hf.prodMap hg)
        (compactSupportKExternalProduct m n a b) =
      compactSupportKExternalProduct m n
        (compactSupportKPullback m f hf a) (compactSupportKPullback n g hg b) := by
  /- Stage 1: f times the identity on real m-space and g times the identity
  on real n-space are proper. Apply the existing degree-zero product
  naturality theorem to those original suspended maps.
  Stage 2: the suspended product homeomorphisms commute with these maps:
  both routes send ((x,s),(y,t)) to ((f(x),g(y)), Fin.append s t).
  Proper-pullback composition through this square identifies the two
  displayed products, retaining the order and dimensions of both blocks. -/
  let S := Fin m → ℝ
  let T := Fin n → ℝ
  let R := Fin (m + n) → ℝ
  let F := f.prodMap (ContinuousMap.id S)
  let G := g.prodMap (ContinuousMap.id T)
  let H := (f.prodMap g).prodMap (ContinuousMap.id R)
  let e := suspendedProductHomeomorph m n X Y
  let e' := suspendedProductHomeomorph m n X' Y'
  let j : C((X × Y) × R, (X × S) × (Y × T)) := ⟨e.symm, e.symm.continuous⟩
  let j' : C((X' × Y') × R, (X' × S) × (Y' × T)) := ⟨e'.symm, e'.symm.continuous⟩
  have hF : IsProperMap F := hf.prodMap isProperMap_id
  have hG : IsProperMap G := hg.prodMap isProperMap_id
  have hH : IsProperMap H := (hf.prodMap hg).prodMap isProperMap_id
  -- Apply the actual degree-zero product law before changing coordinates.
  have hproduct := compactSupportKZeroExternalProduct_properPullback F hF G hG a b
  change compactSupportKZeroPullback H hH
      (compactSupportKZeroPullback j' e'.symm.isProperMap
        (compactSupportKZeroExternalProduct a b)) =
    compactSupportKZeroPullback j e.symm.isProperMap
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroPullback F hF a) (compactSupportKZeroPullback G hG b))
  rw [← hproduct]
  let t := compactSupportKZeroExternalProduct a b
  -- Splitting the same concatenated vector commutes with changing only the base points.
  calc
    _ = compactSupportKZeroPullback (j'.comp H) (e'.symm.isProperMap.comp hH) t :=
      (DFunLike.congr_fun
        (compactSupportKZeroPullback_comp H j' hH e'.symm.isProperMap) t).symm
    _ = compactSupportKZeroPullback ((F.prodMap G).comp j)
        ((hF.prodMap hG).comp e.symm.isProperMap) t := by rfl
    _ = _ := DFunLike.congr_fun
      (compactSupportKZeroPullback_comp j (F.prodMap G) e.symm.isProperMap
        (hF.prodMap hG)) t

/-- Arbitrary open embeddings preserve the same full graded external product. -/
theorem compactSupportKExternalProduct_openPushforward (m n : ℕ)
    (f : X → X') (hf : IsOpenEmbedding f) (g : Y → Y') (hg : IsOpenEmbedding g)
    (a : CompactSupportK m X) (b : CompactSupportK n Y) :
    compactSupportKOpenPushforward (m + n) (Prod.map f g) (hf.prodMap hg)
        (compactSupportKExternalProduct m n a b) =
      compactSupportKExternalProduct m n
        (compactSupportKOpenPushforward m f hf a)
        (compactSupportKOpenPushforward n g hg b) := by
  /- Stage 1: take the actual open embeddings f times identity and g times
  identity on their respective real coordinate spaces. The original
  degree-zero open-pushforward product theorem applies without properness.
  Stage 2: concatenate the same real blocks on source and target. The
  coordinate square commutes on each original finite point; its open-image
  identifications and collapse maps commute as well, with every point
  outside the original product image sent to infinity. Functoriality of
  open pushforward and its homeomorphism compatibility give the equality. -/
  let S := Fin m → ℝ
  let T := Fin n → ℝ
  let R := Fin (m + n) → ℝ
  let F : (X × S) → (X' × S) := Prod.map f id
  let G : (Y × T) → (Y' × T) := Prod.map g id
  let H : ((X × Y) × R) → ((X' × Y') × R) := Prod.map (Prod.map f g) id
  have hF : IsOpenEmbedding F := hf.prodMap IsOpenEmbedding.id
  have hG : IsOpenEmbedding G := hg.prodMap IsOpenEmbedding.id
  have hH : IsOpenEmbedding H := (hf.prodMap hg).prodMap IsOpenEmbedding.id
  let e := suspendedProductHomeomorph m n X Y
  let e' := suspendedProductHomeomorph m n X' Y'
  -- The two factorwise open collapses preserve the original degree-zero product.
  have hproduct := compactSupportKZeroExternalProduct_openPushforward F hF G hG a b
  change compactSupportKZeroOpenPushforward H hH
      (compactSupportKZeroHomeomorph e (compactSupportKZeroExternalProduct a b)) =
    compactSupportKZeroHomeomorph e'
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroOpenPushforward F hF a)
        (compactSupportKZeroOpenPushforward G hG b))
  rw [← hproduct, ← compactSupportKZeroOpenPushforward_homeomorph e,
    ← compactSupportKZeroOpenPushforward_homeomorph e']
  let t := compactSupportKZeroExternalProduct a b
  -- Both composites retain f(x), g(y), and the same first-then-second vector blocks.
  calc
    _ = compactSupportKZeroOpenPushforward (H ∘ e) (hH.comp e.isOpenEmbedding) t :=
      (DFunLike.congr_fun
        (compactSupportKZeroOpenPushforward_comp e e.isOpenEmbedding H hH) t).symm
    _ = compactSupportKZeroOpenPushforward (e' ∘ Prod.map F G)
        (e'.isOpenEmbedding.comp (hF.prodMap hG)) t := by rfl
    _ = _ := DFunLike.congr_fun
      (compactSupportKZeroOpenPushforward_comp (Prod.map F G) (hF.prodMap hG)
        e' e'.isOpenEmbedding) t

end AtiyahSinger

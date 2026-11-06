/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedSupportCoefficients
public import AtiyahSinger.Topology.PrincipalBundlePullback

/-!
# The topological twisted compact-support product

Public module ID: M1557.

For f : X to B, pair a point of the original associated principal pullback
with its X coordinate and its original associated Y class. This map embeds
the actual quotient as the closed fiber product in X times (P associated Y).
It is proper when B is Hausdorff, even if f is not proper and X is noncompact.

Take the ordinary compact-support external product of a class on X with the
specified associated descent of an equivariant class on Y, then pull it back
along that paired map. The resulting biadditive operation is balanced over the
full representation ring through the original associated coefficient bundle.

Sources: SG III.13 (13.16), pp.251--252, and Appendix C.1, together with HU
IV.6 Proposition 6.3. This constructs the topological multiplication before
the geometric identification with a split cotangent bundle. It does not assert
that geometric splitting, a sphere-bundle index formula, or associated support
descent over a noncompact principal base. The original principal base B is
compact Hausdorff, but X and Y may be noncompact LCH spaces and G may be
noncompact. The paired closed embedding and the full virtual coefficient
balance are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle

variable {G P B X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [hP : IsPrincipalBundle G projection]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- Pair the original pullback base point with its original associated class. -/
def associatedBundlePullbackProdMap (f : C(X, B)) :
    C(AssociatedBundle G (PrincipalBundlePullback f projection) Y,
      X × AssociatedBundle G P Y) where
  toFun z :=
    (associatedBundlePullbackMap (G := G) (F := Y) (projection := projection) f z).val
  continuous_toFun :=
    (associatedBundlePullbackMap (G := G) (F := Y) (projection := projection) f).continuous
      |>.subtype_val

/-- The exact paired quotient map is a closed embedding without requiring a proper base map. -/
theorem associatedBundlePullbackProdMap_isClosedEmbedding [T2Space B] (f : C(X, B)) :
    Topology.IsClosedEmbedding
      (associatedBundlePullbackProdMap (G := G) (Y := Y) (projection := projection) f) := by
  /- Stage 1: the existing associatedBundlePullbackHomeomorph identifies the
  source with exactly {(x,z) | f(x)=q(z)}, with its native subtype topology.
  The stated paired map is this homeomorphism followed by subtype inclusion.
  Stage 2: f after the first projection and the original associated projection
  q after the second are continuous into Hausdorff B. Their equality locus
  is closed. Its inclusion is a closed embedding, and composing with the
  specified homeomorphism gives the assertion for the actual quotient map.
  In particular this paired map is proper. Neither f nor either product
  projection is claimed proper; no compactness or local compactness is used. -/
  -- Hausdorffness is needed only for the equality locus in the original product.
  have hclosed : IsClosed
      {w : X × AssociatedBundle G P Y |
        f w.1 = associatedBundleProjection (F := Y) hP w.2} :=
    isClosed_eq (f.continuous.comp continuous_fst)
      ((associatedBundleProjection (F := Y) hP).continuous.comp continuous_snd)
  -- The fixed quotient comparison has exactly this subtype inclusion as its paired map.
  let e := associatedBundlePullbackHomeomorph (G := G) (F := Y)
    (projection := projection) f
  exact hclosed.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding

variable [CompactSpace B] [T2Space B]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- The twisted product takes an ordinary class and an equivariant class to the actual pullback. -/
def associatedSupportTwistedProduct (f : C(X, B)) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    CompactSupportKZero X →+ EquivariantSupportTripleKZero G Y →+
      CompactSupportKZero (AssociatedBundle G (PrincipalBundlePullback f projection) Y) :=
  letI := associatedBundle_t2Space (Y := Y) hP
  letI := associatedBundle_locallyCompactSpace (Y := Y) hP
  letI := associatedBundle_t2Space (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  letI := associatedBundle_locallyCompactSpace (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  ((compactSupportKZeroExternalProduct (X := X) (Y := AssociatedBundle G P Y)).flip.comp
    (associatedSupportKZero hP)).flip.compr₂
      (compactSupportKZeroPullback
        (associatedBundlePullbackProdMap (G := G) (Y := Y) (projection := projection) f)
        (associatedBundlePullbackProdMap_isClosedEmbedding f).isProperMap)

/-- The full representation coefficient can move between the two inputs of the twisted product. -/
theorem associatedSupportTwistedProduct_balanced (f : C(X, B))
    (r : RepresentationGrothendieckGroup G) (u : CompactSupportKZero X)
    (v : EquivariantSupportTripleKZero G Y) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    associatedSupportTwistedProduct (G := G) (projection := projection) f
        (complexKZeroCompactSupportAction f (associatedRepresentationKZero hP r) u) v =
      associatedSupportTwistedProduct (G := G) (projection := projection) f u (r • v) := by
  /- Let k be the compact-support image of associatedRepresentationKZero hP r,
  and let a be associatedSupportKZero hP v. Both coefficient actions use
  the proper graphs F=(f,id) and Q=(q,id); their second projections are
  identities, so no properness of f or q is required.
  External-product proper-pullback naturality moves those graph restrictions
  outside the same three-factor product. The inverse swap and associator
  move the degree-zero coefficient k past u without a grading sign.
  The existing associatedSupportKZero_smul theorem identifies the virtual
  coefficient action on v directly, without choosing support representatives.
  On the original fiber product W, f(x)=q(z) gives the exact map identity
  L.comp p = C.comp (A.comp (D.comp p)). Proper-pullback composition then
  identifies the two class expressions. All compact-support pullbacks use
  the proper paired map or these graphs; none is taken along f alone. -/
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let := associatedBundle_t2Space (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  let := associatedBundle_locallyCompactSpace (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  let Z := AssociatedBundle G P Y
  let W := AssociatedBundle G (PrincipalBundlePullback f projection) Y
  let p : C(W, X × Z) :=
    associatedBundlePullbackProdMap (G := G) (Y := Y) (projection := projection) f
  have hp : IsProperMap p := (associatedBundlePullbackProdMap_isClosedEmbedding f).isProperMap
  let q : C(Z, B) := associatedBundleProjection (F := Y) hP
  let k : CompactSupportKZero B :=
    (compactSupportKZeroCompactEquiv B).symm (associatedRepresentationKZero hP r)
  let a : CompactSupportKZero Z := associatedSupportKZero hP v
  -- Both actions use proper graphs; no properness of f or q is required.
  let F : C(X, B × X) := f.prodMk (ContinuousMap.id X)
  let Q : C(Z, B × Z) := q.prodMk (ContinuousMap.id Z)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous continuous_snd isProperMap_id
  have hQ : IsProperMap Q :=
    isProperMap_of_comp_of_t2 Q.continuous continuous_snd isProperMap_id
  have hIX : IsProperMap (ContinuousMap.id X) := isProperMap_id
  have hIZ : IsProperMap (ContinuousMap.id Z) := isProperMap_id
  let L : C(X × Z, (B × X) × Z) := F.prodMap (ContinuousMap.id Z)
  let D : C(X × Z, X × (B × Z)) := (ContinuousMap.id X).prodMap Q
  let A : C(X × (B × Z), (X × B) × Z) :=
    ⟨(Homeomorph.prodAssoc X B Z).symm, (Homeomorph.prodAssoc X B Z).symm.continuous⟩
  let flip : C(X × B, B × X) :=
    ⟨(Homeomorph.prodComm B X).symm, (Homeomorph.prodComm B X).symm.continuous⟩
  let C : C((X × B) × Z, (B × X) × Z) := flip.prodMap (ContinuousMap.id Z)
  have hL : IsProperMap L := hF.prodMap hIZ
  have hD : IsProperMap D := hIX.prodMap hQ
  have hA : IsProperMap A := (Homeomorph.prodAssoc X B Z).symm.isProperMap
  have hflip : IsProperMap flip := (Homeomorph.prodComm B X).symm.isProperMap
  have hC : IsProperMap C := hflip.prodMap hIZ
  let t : CompactSupportKZero ((B × X) × Z) :=
    compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct k u) a
  -- Naturality moves the graph restrictions outside the same three-factor product.
  have hleft := compactSupportKZeroExternalProduct_properPullback F hF
    (ContinuousMap.id Z) hIZ (compactSupportKZeroExternalProduct k u) a
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hleft
  have hright := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) hIX Q hQ u (compactSupportKZeroExternalProduct k a)
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hright
  -- The even coefficient passes the X factor using the actual inverse swap and associator.
  have hswap := compactSupportKZeroExternalProduct_swap k u
  change compactSupportKZeroPullback flip hflip
    (compactSupportKZeroExternalProduct k u) = compactSupportKZeroExternalProduct u k at hswap
  have hpermute := compactSupportKZeroExternalProduct_properPullback flip hflip
    (ContinuousMap.id Z) hIZ (compactSupportKZeroExternalProduct k u) a
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply, hswap] at hpermute
  have hassoc := compactSupportKZeroExternalProduct_assoc u k a
  change compactSupportKZeroPullback A hA
      (compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct u k) a) =
    compactSupportKZeroExternalProduct u (compactSupportKZeroExternalProduct k a) at hassoc
  rw [← hpermute] at hassoc
  -- The virtual coefficient theorem reduces the original descent to this graph action.
  change compactSupportKZeroPullback p hp
      (compactSupportKZeroExternalProduct
        (complexKZeroCompactSupportAction f (associatedRepresentationKZero hP r) u) a) =
    compactSupportKZeroPullback p hp
      (compactSupportKZeroExternalProduct u (associatedSupportKZero hP (r • v)))
  rw [associatedSupportKZero_smul hP r v]
  change compactSupportKZeroPullback p hp
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroPullback F hF (compactSupportKZeroExternalProduct k u)) a) =
    compactSupportKZeroPullback p hp
      (compactSupportKZeroExternalProduct u
        (compactSupportKZeroPullback Q hQ (compactSupportKZeroExternalProduct k a)))
  rw [← hleft, ← hright, ← hassoc]
  change compactSupportKZeroPullback p hp (compactSupportKZeroPullback L hL t) =
    compactSupportKZeroPullback p hp
      (compactSupportKZeroPullback D hD
        (compactSupportKZeroPullback A hA (compactSupportKZeroPullback C hC t)))
  -- On this precise fiber product, the two coefficient coordinates coincide by definition.
  have hmaps : L.comp p = C.comp (A.comp (D.comp p)) := by
    ext w
    · exact (associatedBundlePullbackMap (G := G) (F := Y) (projection := projection) f w).property
    · rfl
    · rfl
  calc
    compactSupportKZeroPullback p hp (compactSupportKZeroPullback L hL t) =
        compactSupportKZeroPullback (L.comp p) (hL.comp hp) t :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp p L hp hL) t).symm
    _ = compactSupportKZeroPullback (C.comp (A.comp (D.comp p)))
        (hC.comp (hA.comp (hD.comp hp))) t := by simp only [hmaps]
    _ = compactSupportKZeroPullback p hp
        (compactSupportKZeroPullback D hD
          (compactSupportKZeroPullback A hA (compactSupportKZeroPullback C hC t))) := by
      rw [compactSupportKZeroPullback_comp (A.comp (D.comp p)) C (hA.comp (hD.comp hp)) hC,
        AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp (D.comp p) A (hD.comp hp) hA,
        AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp p D hp hD,
        AddMonoidHom.comp_apply]

end AtiyahSinger

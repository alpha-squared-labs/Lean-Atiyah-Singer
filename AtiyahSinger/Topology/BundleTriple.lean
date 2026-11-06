/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteBundle

/-!
# A carrier for geometric triples and their stable equivalence

Public module ID: M1601.

D07/K02. Bundle objects have arbitrary locally finite rank with small fibers.
A triple records its two bundles and the original boundary isomorphism. Stable
equivalence adds identity triples with independently chosen bundles on each side,
as in SG I.9.23–9.25 and Karoubi II.2.26–2.29. It is not equality of absolute classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

attribute [local instance] sumTopology trivialTopology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A geometric relative triple, including both finite-rank bundle objects. -/
structure BundleTriple (A : Set X) where
  /-- The source bundle on the whole base. -/
  source : FiniteBundle X
  /-- The target bundle on the whole base. -/
  target : FiniteBundle X
  /-- Its actual boundary isomorphism on the relative subspace. -/
  boundary : RelativeTriple source.Fiber target.Fiber A

variable {A : Set X}

/-- Package the existing boundary data into a geometric triple. -/
@[reducible]
def BundleTriple.ofBoundary (E F : FiniteBundle X) (a : RelativeTriple E.Fiber F.Fiber A) :
    BundleTriple A where
  source := E
  target := F
  boundary := a

/-- The identity triple of a bundle. -/
@[reducible]
def BundleTriple.identity (A : Set X) (E : FiniteBundle X) : BundleTriple A where
  source := E
  target := E
  boundary := RelativeTriple.identity E.Fiber A

/-- Direct sum of triples with the specified boundary direct sum. -/
@[reducible]
def BundleTriple.sum (a b : BundleTriple A) : BundleTriple A where
  source := a.source.sum b.source
  target := a.target.sum b.target
  boundary := RelativeTriple.sum a.boundary b.boundary

/-- Reverse the bundles and the boundary isomorphism. -/
@[reducible]
def BundleTriple.inverse (a : BundleTriple A) : BundleTriple A where
  source := a.target
  target := a.source
  boundary := a.boundary.symm

/-- Pullback over the exact inverse-image pair, retaining the boundary action. -/
@[reducible]
def BundleTriple.pullback (a : BundleTriple A) (f : C(Y, X)) : BundleTriple (f ⁻¹' A) where
  source := a.source.pullback f
  target := a.target.pullback f
  boundary := a.boundary.pullback f


/-- Global isomorphisms must commute with the original boundary maps. -/
def BundleTriple.IsIsomorphic (a b : BundleTriple A) : Prop :=
  RelativeTriple.IsIsomorphic a.boundary b.boundary

/-- Stable equivalence adds identity triples, with no homotopy hidden in the definition. -/
def BundleTriple.IsStablyIsomorphic (a b : BundleTriple A) : Prop :=
  ∃ E F : FiniteBundle X,
    (a.sum (BundleTriple.identity A E)).IsIsomorphic (b.sum (BundleTriple.identity A F))

/-- Adding the zero bundle shows that isomorphism implies stable equivalence. -/
theorem BundleTriple.isStablyIsomorphic_of_isIsomorphic (a b : BundleTriple A)
    (h : a.IsIsomorphic b) : a.IsStablyIsomorphic b := by
  /- Use the zero-rank trivial bundle for both stabilizing objects. Take the
  direct sum of each given global isomorphism with its identity. The resulting
  boundary square is the original square on the first coordinate and identity
  on the stabilizing coordinate. -/
  obtain ⟨u, v, huv⟩ := h
  let Z := FiniteBundle.trivial X 0
  refine ⟨Z, Z, u.sum (Iso.refl Z.Fiber), v.sum (Iso.refl Z.Fiber), ?_⟩
  intro x w
  change ((v.sum (Iso.refl Z.Fiber)).linearEquiv x)
    ((RelativeTriple.sum a.boundary (RelativeTriple.identity Z.Fiber A)).linearEquiv x w) =
    (RelativeTriple.sum b.boundary (RelativeTriple.identity Z.Fiber A)).linearEquiv x
      ((u.sum (Iso.refl Z.Fiber)).linearEquiv x w)
  rw [RelativeTriple.sum_apply, RelativeTriple.sum_apply]
  exact Prod.ext (huv x w.1) rfl

/-- Stable equivalence is reflexive. -/
theorem BundleTriple.isStablyIsomorphic_refl (a : BundleTriple A) : a.IsStablyIsomorphic a := by
  /- Use the same zero-rank stabilizing bundle on each side and identity maps
  on the two resulting bundles. Their restrictions commute with the same boundary map. -/
  exact ⟨FiniteBundle.trivial X 0, FiniteBundle.trivial X 0,
    RelativeTriple.isIsomorphic_refl _⟩

/-- Stable equivalence is symmetric. -/
theorem BundleTriple.IsStablyIsomorphic.symm {a b : BundleTriple A}
    (h : a.IsStablyIsomorphic b) : b.IsStablyIsomorphic a := by
  /- Exchange the two stabilizing bundles and invert the global isomorphisms
  of the stabilized triples. The inverted boundary square still commutes. -/
  obtain ⟨E, F, hEF⟩ := h
  exact ⟨F, E, RelativeTriple.IsIsomorphic.symm hEF⟩

/-- Stable equivalence is transitive. -/
theorem BundleTriple.IsStablyIsomorphic.trans {a b c : BundleTriple A}
    (h : a.IsStablyIsomorphic b) (k : b.IsStablyIsomorphic c) : a.IsStablyIsomorphic c := by
  /- Add the other pair of stabilizing bundles to each commuting square.
  Reassociate and permute summands until the middle stabilized triples agree,
  then compose the global isomorphisms. All permutations act on boundary maps too. -/
  obtain ⟨E, F, u, v, huv⟩ := h
  obtain ⟨G, H, w, z, hwz⟩ := k
  -- Combine the two actual maps after interchanging only the stabilizing coordinates.
  have combine (A B C E F G H : FiniteBundle X)
      (u : Iso (A.sum E).Fiber (B.sum F).Fiber)
      (w : Iso (B.sum G).Fiber (C.sum H).Fiber) :
      ∃ U : Iso (A.sum (E.sum G)).Fiber (C.sum (H.sum F)).Fiber,
        ∀ x q, U.linearEquiv x q =
          let r := u.linearEquiv x (q.1, q.2.1)
          let s := w.linearEquiv x (r.1, q.2.2)
          (s.1, s.2, r.2) := by
    have hassoc (J K L : FiniteBundle X) (x : X)
        (q : (J.sum (K.sum L)).Fiber x) :
        ((J.sumAssocIso K L).linearEquiv x).symm q = ((q.1, q.2.1), q.2.2) := by
      apply ((J.sumAssocIso K L).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, FiniteBundle.sumAssocIso_apply]
    let swap : Iso ((B.sum F).sum G).Fiber ((B.sum G).sum F).Fiber :=
      (B.sumAssocIso F G).trans
        (((Iso.refl B.Fiber).sum (sumCommIso (E := F.Fiber) (F := G.Fiber))).trans
          (B.sumAssocIso G F).symm)
    have hswap (x : X) (q : ((B.sum F).sum G).Fiber x) :
        swap.linearEquiv x q = ((q.1.1, q.2), q.1.2) := by
      change ((B.sumAssocIso G F).linearEquiv x).symm
        (((Iso.refl B.Fiber).sum (sumCommIso (E := F.Fiber) (F := G.Fiber))).linearEquiv x
          ((B.sumAssocIso F G).linearEquiv x q)) = _
      rw [hassoc, FiniteBundle.sumAssocIso_apply]
      rfl
    let U := (A.sumAssocIso E G).symm.trans
      ((u.sum (Iso.refl G.Fiber)).trans
        (swap.trans ((w.sum (Iso.refl F.Fiber)).trans (C.sumAssocIso H F))))
    refine ⟨U, ?_⟩
    intro x q
    change (C.sumAssocIso H F).linearEquiv x
      ((w.sum (Iso.refl F.Fiber)).linearEquiv x
        (swap.linearEquiv x ((u.sum (Iso.refl G.Fiber)).linearEquiv x
          (((A.sumAssocIso E G).linearEquiv x).symm q)))) = _
    rw [hassoc, hswap, FiniteBundle.sumAssocIso_apply]
    rfl
  obtain ⟨U, hU⟩ := combine a.source b.source c.source E F G H u w
  obtain ⟨V, hV⟩ := combine a.target b.target c.target E F G H v z
  refine ⟨E.sum G, H.sum F, U, V, ?_⟩
  intro x q
  change V.linearEquiv x ((RelativeTriple.sum a.boundary
    (RelativeTriple.identity (E.sum G).Fiber A)).linearEquiv x q) =
    (RelativeTriple.sum c.boundary (RelativeTriple.identity (H.sum F).Fiber A)).linearEquiv x
      (U.linearEquiv x q)
  erw [RelativeTriple.sum_apply, RelativeTriple.sum_apply, hU, hV]
  have hfirst := huv x (q.1, q.2.1)
  have hsecond := hwz x ((u.linearEquiv x (q.1, q.2.1)).1, q.2.2)
  simp only [RelativeTriple.sum_apply] at hfirst hsecond
  change v.linearEquiv x (a.boundary.linearEquiv x q.1, q.2.1) =
    (b.boundary.linearEquiv x (u.linearEquiv x (q.1, q.2.1)).1,
      (u.linearEquiv x (q.1, q.2.1)).2) at hfirst
  change z.linearEquiv x
      (b.boundary.linearEquiv x (u.linearEquiv x (q.1, q.2.1)).1, q.2.2) =
    (c.boundary.linearEquiv x
      (w.linearEquiv x ((u.linearEquiv x (q.1, q.2.1)).1, q.2.2)).1,
        (w.linearEquiv x ((u.linearEquiv x (q.1, q.2.1)).1, q.2.2)).2) at hsecond
  dsimp only [RelativeTriple.identity, Iso.refl, LinearEquiv.refl_apply]
  erw [hfirst, hsecond]
  rfl

/-- Direct sums respect stable equivalence in both arguments. -/
theorem BundleTriple.IsStablyIsomorphic.sum {a b c d : BundleTriple A}
    (h : a.IsStablyIsomorphic b) (k : c.IsStablyIsomorphic d) :
    (a.sum c).IsStablyIsomorphic (b.sum d) := by
  /- Take the direct sum of the two stabilized commuting squares. Move their
  identity summands to the right using associativity and commutativity.
  This gives the required witnesses. -/
  obtain ⟨E, F, u, v, huv⟩ := h
  obtain ⟨G, H, w, z, hwz⟩ := k
  -- This standard four-factor permutation keeps each original fiber vector.
  let shuffle (J K L M : FiniteBundle X) :
      Iso ((J.sum K).sum (L.sum M)).Fiber ((J.sum L).sum (K.sum M)).Fiber :=
    { linearEquiv x := LinearEquiv.prodProdProdComm ℂ
        (J.Fiber x) (K.Fiber x) (L.Fiber x) (M.Fiber x)
      continuous_total := by
        have hJK := continuous_sum_fst (E := (J.sum K).Fiber) (F := (L.sum M).Fiber)
        have hLM := continuous_sum_snd (E := (J.sum K).Fiber) (F := (L.sum M).Fiber)
        have hJ := (continuous_sum_fst (E := J.Fiber) (F := K.Fiber)).comp hJK
        have hK := (continuous_sum_snd (E := J.Fiber) (F := K.Fiber)).comp hJK
        have hL := (continuous_sum_fst (E := L.Fiber) (F := M.Fiber)).comp hLM
        have hM := (continuous_sum_snd (E := L.Fiber) (F := M.Fiber)).comp hLM
        exact continuous_induced_rng.mpr ((continuous_induced_rng.mpr (hJ.prodMk hL)).prodMk
          (continuous_induced_rng.mpr (hK.prodMk hM)))
      continuous_symm := by
        have hJL := continuous_sum_fst (E := (J.sum L).Fiber) (F := (K.sum M).Fiber)
        have hKM := continuous_sum_snd (E := (J.sum L).Fiber) (F := (K.sum M).Fiber)
        have hJ := (continuous_sum_fst (E := J.Fiber) (F := L.Fiber)).comp hJL
        have hL := (continuous_sum_snd (E := J.Fiber) (F := L.Fiber)).comp hJL
        have hK := (continuous_sum_fst (E := K.Fiber) (F := M.Fiber)).comp hKM
        have hM := (continuous_sum_snd (E := K.Fiber) (F := M.Fiber)).comp hKM
        exact continuous_induced_rng.mpr ((continuous_induced_rng.mpr (hJ.prodMk hK)).prodMk
          (continuous_induced_rng.mpr (hL.prodMk hM))) }
  let U := (shuffle a.source c.source E G).trans
    ((u.sum w).trans (shuffle b.source F d.source H))
  let V := (shuffle a.target c.target E G).trans
    ((v.sum z).trans (shuffle b.target F d.target H))
  refine ⟨E.sum G, F.sum H, U, V, ?_⟩
  intro x q
  have hfirst := huv x (q.1.1, q.2.1)
  have hsecond := hwz x (q.1.2, q.2.2)
  simp only [RelativeTriple.sum_apply] at hfirst hsecond
  change v.linearEquiv x (a.boundary.linearEquiv x q.1.1, q.2.1) =
    (b.boundary.linearEquiv x (u.linearEquiv x (q.1.1, q.2.1)).1,
      (u.linearEquiv x (q.1.1, q.2.1)).2) at hfirst
  change z.linearEquiv x (c.boundary.linearEquiv x q.1.2, q.2.2) =
    (d.boundary.linearEquiv x (w.linearEquiv x (q.1.2, q.2.2)).1,
      (w.linearEquiv x (q.1.2, q.2.2)).2) at hsecond
  change V.linearEquiv x ((RelativeTriple.sum
    (RelativeTriple.sum a.boundary c.boundary)
    (RelativeTriple.identity (E.sum G).Fiber A)).linearEquiv x q) =
    (RelativeTriple.sum (RelativeTriple.sum b.boundary d.boundary)
      (RelativeTriple.identity (F.sum H).Fiber A)).linearEquiv x (U.linearEquiv x q)
  rw [RelativeTriple.sum_apply, RelativeTriple.sum_apply,
    RelativeTriple.sum_apply, RelativeTriple.sum_apply]
  change (((v.linearEquiv x (a.boundary.linearEquiv x q.1.1, q.2.1)).1,
      (z.linearEquiv x (c.boundary.linearEquiv x q.1.2, q.2.2)).1),
      (v.linearEquiv x (a.boundary.linearEquiv x q.1.1, q.2.1)).2,
      (z.linearEquiv x (c.boundary.linearEquiv x q.1.2, q.2.2)).2) = _
  erw [hfirst, hsecond]
  rfl

/-- Pullback preserves stable equivalence over inverse-image pairs. -/
theorem BundleTriple.IsStablyIsomorphic.pullback {a b : BundleTriple A}
    (h : a.IsStablyIsomorphic b) (f : C(Y, X)) :
    (a.pullback f).IsStablyIsomorphic (b.pullback f) := by
  /- Pull back the stabilizing bundles and both maps in the commuting square.
  The canonical comparisons for pullback and sum preserve each vector, so the
  resulting square is the stabilization of the pulled-back triples. -/
  obtain ⟨E, F, u, v, huv⟩ := h
  -- Compare the two original induced topologies by the identity on fiber pairs.
  have compare (J K : FiniteBundle X) :
      ∃ e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber,
        ∀ y w, e.linearEquiv y w = w := by
    let e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber :=
      { linearEquiv y := LinearEquiv.refl ℂ (J.Fiber (f y) × K.Fiber (f y))
        continuous_total := by
          apply continuous_induced_rng.mpr
          apply Continuous.prodMk
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit J.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
              (continuous_sum_fst.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit K.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
              (continuous_sum_snd.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.sum K).Fiber f).continuous_iff]
          apply ((Pullback.continuous_proj Unit J.Fiber f).comp continuous_sum_fst).prodMk
          apply continuous_induced_rng.mpr
          exact ((Pullback.continuous_lift Unit J.Fiber f).comp continuous_sum_fst).prodMk
            ((Pullback.continuous_lift Unit K.Fiber f).comp continuous_sum_snd) }
    exact ⟨e, fun _ _ ↦ rfl⟩
  obtain ⟨aE, haE⟩ := compare a.source E
  obtain ⟨aE', haE'⟩ := compare a.target E
  obtain ⟨bF, hbF⟩ := compare b.source F
  obtain ⟨bF', hbF'⟩ := compare b.target F
  let U := aE.symm.trans ((u.pullback f).trans bF)
  let V := aE'.symm.trans ((v.pullback f).trans bF')
  have hU (y : Y) (w : ((a.source.pullback f).sum (E.pullback f)).Fiber y) :
      U.linearEquiv y w = u.linearEquiv (f y) w := by
    have ha : aE.linearEquiv y = LinearEquiv.refl ℂ _ := LinearEquiv.ext (haE y)
    change bF.linearEquiv y (u.linearEquiv (f y) ((aE.linearEquiv y).symm w)) = _
    erw [hbF, ha]
    rfl
  have hV (y : Y) (w : ((a.target.pullback f).sum (E.pullback f)).Fiber y) :
      V.linearEquiv y w = v.linearEquiv (f y) w := by
    have ha : aE'.linearEquiv y = LinearEquiv.refl ℂ _ := LinearEquiv.ext (haE' y)
    change bF'.linearEquiv y (v.linearEquiv (f y) ((aE'.linearEquiv y).symm w)) = _
    erw [hbF', ha]
    rfl
  refine ⟨E.pullback f, F.pullback f, U, V, ?_⟩
  intro y w
  change V.linearEquiv y ((RelativeTriple.sum (a.boundary.pullback f)
    (RelativeTriple.identity (E.pullback f).Fiber (f ⁻¹' A))).linearEquiv y w) =
    (RelativeTriple.sum (b.boundary.pullback f)
      (RelativeTriple.identity (F.pullback f).Fiber (f ⁻¹' A))).linearEquiv y
        (U.linearEquiv y w)
  erw [RelativeTriple.sum_apply, RelativeTriple.sum_apply, hU, hV,
    RelativeTriple.pullback_apply, RelativeTriple.pullback_apply]
  have hsquare := huv ⟨f y, y.property⟩ w
  erw [RelativeTriple.sum_apply, RelativeTriple.sum_apply] at hsquare
  exact hsquare

/-- The setoid of the stated stable-isomorphism relation. -/
def BundleTriple.stableSetoid (A : Set X) : Setoid (BundleTriple A) :=
  { r := BundleTriple.IsStablyIsomorphic
    iseqv := ⟨BundleTriple.isStablyIsomorphic_refl,
      fun h ↦ h.symm, fun h k ↦ h.trans k⟩ }

/-- Actual stable-isomorphism classes of geometric triples. -/
abbrev StableTripleClass (A : Set X) : Type _ := Quotient (BundleTriple.stableSetoid A)

/-- The stable class represented by a geometric triple. -/
def BundleTriple.stableClass (a : BundleTriple A) : StableTripleClass A :=
  Quotient.mk _ a

/-- The stable quotient identifies exactly the specified stabilizations. -/
theorem BundleTriple.stableClass_eq_iff (a b : BundleTriple A) :
    a.stableClass = b.stableClass ↔ a.IsStablyIsomorphic b := by
  /- Apply effectiveness of the setoid quotient. Its relation is exactly the
  existential stabilization relation. No further group-completion or homotopy
  relation is added. -/
  constructor
  · exact Quotient.exact
  · intro h
    exact @Quotient.sound _ (BundleTriple.stableSetoid A) a b h

/-- The underlying absolute difference still remembers only the two bundle classes. -/
def BundleTriple.absoluteClass [CompactSpace X] [T2Space X] (a : BundleTriple A) :
    ComplexKZero X :=
  a.source.kZeroClass - a.target.kZeroClass

end AtiyahSinger.ComplexBundle

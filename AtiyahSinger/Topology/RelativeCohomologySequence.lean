/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyExactness
public import AtiyahSinger.Topology.RelativeSingularTriple

/-!
# Exact sequences for the original relative singular cochains

Public module ID: M2069.

The singular-chain sequence of a triple is split in each degree. Its actual
algebraic dual is therefore short exact over any commutative coefficient ring.
This supplies cohomological connecting maps without assuming that dualization
preserves an arbitrary exact sequence or replacing the original relative pairs.

Source: Hatcher, Algebraic Topology, Sections 2.1 and 3.1, the relative sequence
and the degreewise split singular-cochain construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R]

/-- The specified algebraic dual preserves addition of chain maps. -/
instance instAdditiveSingularCochainDualFunctor :
    (singularCochainDualFunctor.{u} R).Additive where
  map_add := by
    intro C D f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (f.unop.f n + g.unop.f n) ≫ φ = _
    exact Preadditive.add_comp _ _ _ (f.unop.f n) (g.unop.f n) φ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Dualizing a degreewise split chain sequence gives an exact sequence of the actual cochains. -/
theorem shortExact_singularCochainDual_of_degreewiseSplit
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ))
    (hS : ∀ n : ℕ,
      (S.map (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)).Splitting) :
    (S.op.map (singularCochainDualFunctor R)).ShortExact := by
  -- The given sections and retractions dualize in the opposite order, degree by degree.
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let D := (linearYoneda R (ModuleCat.{u} R)).obj (singularCoefficient R)
  exact ((hS n).op.map D).shortExact

variable {X : Type u} [TopologicalSpace X]

/-- An explicit homotopy inverse makes the original cohomology pullback invertible. -/
theorem isIso_singularCohomologyPullback_of_homotopyInverse
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (hX : (g.comp f).Homotopic (ContinuousMap.id X))
    (hY : (f.comp g).Homotopic (ContinuousMap.id Y)) (k : ℕ) :
    IsIso (singularCohomologyPullback R f k) := by
  have hcomp {Z W : Type u} [TopologicalSpace Z] [TopologicalSpace W]
      (a : C(Z, W)) (b : C(W, Z))
      (h : (b.comp a).Homotopic (ContinuousMap.id Z)) :
      singularCohomologyPullback R b k ≫ singularCohomologyPullback R a k = 𝟙 _ := by
    let F := singularCohomologyFunctor R k
    change F.map (TopCat.ofHom b).op ≫ F.map (TopCat.ofHom a).op = _
    rw [← F.map_comp, ← op_comp]
    change singularCohomologyPullback R (b.comp a) k = _
    obtain ⟨H⟩ := h
    rw [singularCohomologyPullback_homotopic R H]
    exact F.map_id _
  exact ⟨singularCohomologyPullback R g k, hcomp g f hY, hcomp f g hX⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Inverse maps of pairs induce inverse pullbacks on the original relative cohomology. -/
theorem isIso_relativeSingularCohomologyPullback_of_inverse
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B A)
    (hX : g.comp f = ContinuousMap.id X) (hY : f.comp g = ContinuousMap.id Y)
    (k : ℕ) : IsIso (relativeSingularCohomologyPullback R f hf k) := by
  have hcomp {Z W : Type u} [TopologicalSpace Z] [TopologicalSpace W]
      (a : C(Z, W)) (b : C(W, Z)) {S : Set Z} {T : Set W}
      (ha : Set.MapsTo a S T) (hb : Set.MapsTo b T S)
      (h : b.comp a = ContinuousMap.id Z) :
      relativeSingularCohomologyPullback R b hb k ≫
        relativeSingularCohomologyPullback R a ha k = 𝟙 _ := by
    rw [← relativeSingularCohomologyPullback_comp]
    generalize_proofs at *
    generalize hfun : b.comp a = c at *
    clear hfun
    subst c
    simp [relativeSingularCohomologyPullback, relativeSingularChainsMap, cokernel.map]
  exact ⟨relativeSingularCohomologyPullback R g hg k,
    hcomp g f hg hf hY, hcomp f g hf hg hX⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A map inducing cohomology isomorphisms on spaces and subspaces does so on their pairs. -/
theorem isIso_relativeSingularCohomologyPullback_of_absolute
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B)
    (hX : ∀ k : ℕ, IsIso (singularCohomologyPullback R f k))
    (hA : ∀ k : ℕ, IsIso (singularCohomologyPullback R
      (⟨fun x ↦ ⟨f x, hf x.property⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩ : C(A, B)) k))
    (k : ℕ) : IsIso (relativeSingularCohomologyPullback R f hf k) := by
  let D := singularCochainDualFunctor R
  let F := (singularChainsFunctor R).map (TopCat.ofHom f)
  let fA : C(A, B) := ⟨fun x ↦ ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let G := (singularChainsFunctor R).map (TopCat.ofHom fA)
  let P := relativeSingularChainsMap R f hf
  let φ : singularSubspaceCochainsSequence R B ⟶ singularSubspaceCochainsSequence R A :=
    { τ₁ := D.map P.op
      τ₂ := D.map F.op
      τ₃ := D.map G.op
      comm₁₂ := by
        change D.map P.op ≫ D.map (relativeSingularChainsProjection R A).op =
          D.map (relativeSingularChainsProjection R B).op ≫ D.map F.op
        rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp]
        congr 1
        apply congrArg Quiver.Hom.op
        simp [P, F, relativeSingularChainsMap, relativeSingularChainsProjection]
      comm₂₃ := by
        change D.map F.op ≫ D.map (singularSubspaceChains R A).op =
          D.map (singularSubspaceChains R B).op ≫ D.map G.op
        rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp]
        congr 1
        apply congrArg Quiver.Hom.op
        simp only [F, G, singularSubspaceChains, ← Functor.map_comp]
        rfl }
  have hSB := shortExact_singularSubspaceCochains R B
  have hSA := shortExact_singularSubspaceCochains R A
  have h₂ (j : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₂ j) := hX j
  have h₃ (j : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₃ j) := hA j
  change IsIso (HomologicalComplex.homologyMap φ.τ₁ k)
  -- The first degree has a genuine zero endpoint; later degrees use the same pair LES.
  open HomologySequence ComposableArrows CategoryTheory.Abelian in
  cases k with
  | zero =>
    apply isIso_of_isIso_of_mono (mapComposableArrows₂ φ 0)
      (composableArrows₂_exact hSB 0) (composableArrows₂_exact hSA 0)
    · have := hSB.mono_f
      apply mono_homologyMap_of_mono_of_not_rel
      simp
    · have := hSA.mono_f
      apply mono_homologyMap_of_mono_of_not_rel
      simp
    · exact h₂ 0
    · change Mono (HomologicalComplex.homologyMap φ.τ₃ 0)
      have := h₃ 0
      infer_instance
  | succ j =>
    apply isIso_of_epi_of_isIso_of_isIso_of_mono
      (composableArrows₅_exact hSB j (j + 1) rfl).δ₀
      (composableArrows₅_exact hSA j (j + 1) rfl).δ₀
      (δ₀Functor.map (mapComposableArrows₅ φ hSB hSA j (j + 1) rfl))
    · exact (h₂ j).epi_of_iso
    · exact h₃ j
    · exact h₂ (j + 1)
    · exact (h₃ (j + 1)).mono_of_iso

/-- A cohomological equivalence of the subspace inclusion makes the original pair acyclic. -/
theorem subsingleton_relativeSingularCohomology_of_isIso_inclusion (A : Set X)
    (hA : ∀ n : ℕ, IsIso (singularCohomologyPullback R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) n)) (k : ℕ) :
    Subsingleton (relativeSingularCohomology R A k) := by
  let S := singularSubspaceCochainsSequence R A
  have hq : QuasiIso S.g := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hA n
  -- The pair is the kernel term of the same short exact cochain sequence.
  have hexact := (shortExact_singularSubspaceCochains R A).acyclic_X₁ hq k
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((exactAt_iff_isZero_homology _ k).mp hexact)

/-- The original cochain sequence of the triple `A ⊆ B ⊆ X`, with pullbacks as its arrows. -/
def relativeSingularCochainTripleSequence (A B : Set X) (hAB : A ⊆ B) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  (relativeSingularTripleSequence R A B hAB).op.map (singularCochainDualFunctor R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The relative cochain sequence of a triple is short exact
over every commutative coefficient ring. -/
theorem shortExact_relativeSingularCochainTripleSequence (A B : Set X) (hAB : A ⊆ B) :
    (relativeSingularCochainTripleSequence R A B hAB).ShortExact := by
  let S := relativeSingularTripleSequence R A B hAB
  apply shortExact_singularCochainDual_of_degreewiseSplit R S
  intro n
  let ev := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let T := S.map ev
  have hT : T.ShortExact :=
    (shortExact_relativeSingularTripleSequence R A B hAB).map_of_exact ev
  -- Keep precisely the original B-simplices in the relative quotient to split its inclusion.
  let split : SplitMono (S.f.f n) :=
    (isSplitMono_relativeSingularChainsMap_preimage R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
      Subtype.val_injective A n).exists_splitMono.some
  exact ShortComplex.Splitting.ofExactOfRetraction T hT.exact
    split.retraction split.id hT.epi_g

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The connecting homomorphism of the original cochain triple is natural for maps of triples. -/
theorem relativeSingularCohomologyTripleBoundary_natural
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    {A B : Set X} {A' B' : Set Y} (hAB : A ⊆ B) (hAB' : A' ⊆ B')
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (k : ℕ) :
    (shortExact_relativeSingularCochainTripleSequence R A' B' hAB').δ k (k + 1) rfl ≫
        relativeSingularCohomologyPullback R f hfB (k + 1) =
      relativeSingularCohomologyPullback R
        (⟨fun z ↦ ⟨f z.val, hfB z.property⟩,
          (f.continuous.comp continuous_subtype_val).subtype_mk _⟩ : C(B, B'))
        (A := (Subtype.val : B → X) ⁻¹' A)
        (B := (Subtype.val : B' → Y) ⁻¹' A')
        (fun _ hz ↦ hfA hz) k ≫
          (shortExact_relativeSingularCochainTripleSequence R A B hAB).δ k (k + 1) rfl := by
  let fB : C(B, B') := ⟨fun z ↦ ⟨f z.val, hfB z.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let S := relativeSingularTripleSequence R A B hAB
  let T := relativeSingularTripleSequence R A' B' hAB'
  -- The square commutes before taking quotients, duals, or cohomology.
  let φ : S ⟶ T :=
    { τ₁ := relativeSingularChainsMap R fB
        (A := (Subtype.val : B → X) ⁻¹' A)
        (B := (Subtype.val : B' → Y) ⁻¹' A') (fun _ hz ↦ hfA hz)
      τ₂ := relativeSingularChainsMap R f hfA
      τ₃ := relativeSingularChainsMap R f hfB
      comm₁₂ := by
        dsimp [S, T, relativeSingularTripleSequence]
        rw [← relativeSingularChainsMap_comp, ← relativeSingularChainsMap_comp]
        rfl
      comm₂₃ := by
        dsimp [S, T, relativeSingularTripleSequence]
        rw [← relativeSingularChainsMap_comp, ← relativeSingularChainsMap_comp]
        rfl }
  exact HomologySequence.δ_naturality
    ((singularCochainDualFunctor R).mapShortComplex.map (ShortComplex.opMap φ))
    (shortExact_relativeSingularCochainTripleSequence R A' B' hAB')
    (shortExact_relativeSingularCochainTripleSequence R A B hAB) k (k + 1) rfl

end AtiyahSinger

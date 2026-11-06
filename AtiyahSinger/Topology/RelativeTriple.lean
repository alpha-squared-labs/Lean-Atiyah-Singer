/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopy
public import AtiyahSinger.Topology.BundleKZero
public import AtiyahSinger.Topology.MatrixRestrictionLifting

/-!
# Geometric relative bundle triples with explicit boundary data

Public module ID: M2098.

The families E and F are explicit, and a triple (E,F,α) specifies their isomorphism
over A. The operations below act on the actual boundary maps. Local finite rank is
required where K classes and extension theorems use vector-bundle properties.
Sources: SG I.9.23–9.25; Karoubi II.2.13–2.16 and II.2.24–2.29.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- Boundary data of the triple (E,F,α), with its two bundles explicit in the type. -/
abbrev RelativeTriple (E F : X → Type*) [∀ x, AddCommGroup (E x)]
    [∀ x, Module ℂ (E x)] [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
    (A : Set X) : Type _ := Iso (Restrict E A) (Restrict F A)

variable {A B : Set X}

/-- The identity boundary triple on a given bundle. -/
def RelativeTriple.identity (E : X → Type*) [∀ x, AddCommGroup (E x)]
    [∀ x, Module ℂ (E x)] [TopologicalSpace (TotalSpace Unit E)] (A : Set X) :
    RelativeTriple E E A :=
  Iso.refl (Restrict E A)

/-- Reverse the two bundles and invert the boundary map. -/
def RelativeTriple.inverse (a : RelativeTriple E F A) : RelativeTriple F E A :=
  a.symm

/-- Compose compatible boundary triples. -/
def RelativeTriple.compose (a : RelativeTriple E F A) (b : RelativeTriple F G A) :
    RelativeTriple E G A :=
  a.trans b

/-- Pass to a smaller relative subspace. -/
def RelativeTriple.restrict (a : RelativeTriple E F A) (h : B ⊆ A) :
    RelativeTriple E F B :=
  a.restrictTo h

variable {H : X → Type*} [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)]

attribute [local instance] sumTopology isFiniteRank_sum

/-- The direct sum of triples uses the original two boundary maps. -/
def RelativeTriple.sum (a : RelativeTriple E F A) (b : RelativeTriple G H A) :
    RelativeTriple (E ×ᵇ G) (F ×ᵇ H) A :=
  (restrictSumIso A).trans ((Iso.sum a b).trans (restrictSumIso A).symm)

/-- The boundary direct sum acts separately on its two vectors. -/
theorem RelativeTriple.sum_apply (a : RelativeTriple E F A) (b : RelativeTriple G H A)
    (x : A) (v : E x × G x) :
    (RelativeTriple.sum a b).linearEquiv x v = (a.linearEquiv x v.1, b.linearEquiv x v.2) := by
  /- Expand the vector-preserving restriction/sum comparisons on both sides of
  the sum isomorphism. The intermediate fiber equivalence acts componentwise. -/
  -- Both restriction comparisons preserve the actual fiber pair.
  change ((restrictSumIso (E := F) (F := H) A).linearEquiv x).symm
    ((a.linearEquiv x).prodCongr (b.linearEquiv x)
      ((restrictSumIso (E := E) (F := G) A).linearEquiv x v)) = _
  apply ((restrictSumIso (E := F) (F := H) A).linearEquiv x).injective
  simp only [LinearEquiv.apply_symm_apply, restrictSumIso_apply]
  exact (restrictSumIso_apply (E := F) (F := H) A x
    (a.linearEquiv x v.1, b.linearEquiv x v.2)).symm

/-- Stabilize a triple by the identity triple of a specified bundle. -/
def RelativeTriple.stabilize (a : RelativeTriple E F A) (G : X → Type*)
    [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
    [TopologicalSpace (TotalSpace Unit G)] : RelativeTriple (E ×ᵇ G) (F ×ᵇ G) A :=
  RelativeTriple.sum a (RelativeTriple.identity G A)

/-- Isomorphism of triples means an actual commuting boundary square. -/
def RelativeTriple.IsIsomorphic (a : RelativeTriple E F A) (b : RelativeTriple G H A) :
    Prop :=
  ∃ u : Iso E G, ∃ v : Iso F H,
    ∀ x : A, ∀ w : E x, v.linearEquiv x (a.linearEquiv x w) =
      b.linearEquiv x (u.linearEquiv x w)

/-- Identity global isomorphisms identify each triple with itself. -/
theorem RelativeTriple.isIsomorphic_refl (a : RelativeTriple E F A) : a.IsIsomorphic a := by
  /- Use identity isomorphisms on the two global bundles. Their restrictions
  give a commuting square because both routes are the original boundary isomorphism. -/
  exact ⟨Iso.refl E, Iso.refl F, fun _ _ ↦ rfl⟩

/-- Triple isomorphism can be reversed. -/
theorem RelativeTriple.IsIsomorphic.symm {a : RelativeTriple E F A}
    {b : RelativeTriple G H A} (h : a.IsIsomorphic b) : b.IsIsomorphic a := by
  /- Invert the two global isomorphisms witnessing the square. Solve the original
  commuting equality for the reverse routes using their fiberwise inverse laws. -/
  obtain ⟨u, v, huv⟩ := h
  refine ⟨u.symm, v.symm, ?_⟩
  intro x w
  -- Solve the original commuting square using these same two inverse maps.
  apply (v.linearEquiv x).injective
  change (v.linearEquiv x) ((v.linearEquiv x).symm (b.linearEquiv x w)) =
    (v.linearEquiv x) (a.linearEquiv x ((u.linearEquiv x).symm w))
  exact ((v.linearEquiv x).apply_symm_apply (b.linearEquiv x w)).trans
    ((huv x ((u.linearEquiv x).symm w)).trans
      (congrArg (b.linearEquiv x) ((u.linearEquiv x).apply_symm_apply w))).symm

/-- Homotopy of boundary data is through invertible maps at every time. -/
def RelativeTriple.Homotopic (a b : RelativeTriple E F A) : Prop :=
  Nonempty (IsoHomotopy a b)

/-- An elementary triple has boundary automorphism homotopic to identity. -/
def RelativeTriple.IsElementary (a : RelativeTriple E E A) : Prop :=
  RelativeTriple.Homotopic (RelativeTriple.identity E A) a

/-- Identity boundary triples are elementary. -/
theorem RelativeTriple.isElementary_identity :
    (RelativeTriple.identity E A).IsElementary := by
  /- The cylinder pullback of the identity gives the constant homotopy. Its
  endpoint equations show that the identity automorphism is homotopic to itself. -/
  exact IsoHomotopy.nonempty_refl (RelativeTriple.identity E A)

/-- Boundary homotopy is invariant under reversal. -/
theorem RelativeTriple.Homotopic.symm {a b : RelativeTriple E F A}
    (h : a.Homotopic b) : b.Homotopic a := by
  /- Choose the witnessing cylinder isomorphism and reverse its time parameter.
  The resulting path exchanges the endpoint boundary maps and stays invertible. -/
  obtain ⟨H⟩ := h
  exact H.nonempty_symm

/-- Boundary homotopies compose in time. -/
theorem RelativeTriple.Homotopic.trans {a b c : RelativeTriple E F A}
    (h : a.Homotopic b) (k : b.Homotopic c) : a.Homotopic c := by
  /- Concatenate the two chosen isomorphism homotopies along their common
  endpoint. The closed pasting construction preserves both forward and inverse continuity. -/
  obtain ⟨H⟩ := h
  obtain ⟨K⟩ := k
  exact H.nonempty_trans K

variable {Y : Type*} [TopologicalSpace Y]

/-- Pull a triple back to the inverse image of its relative subspace. -/
theorem RelativeTriple.exists_pullback (a : RelativeTriple E F A) (f : C(Y, X)) :
    ∃ b : RelativeTriple ((f : Y → X) *ᵖ E) ((f : Y → X) *ᵖ F) (f ⁻¹' A),
      ∀ y v, b.linearEquiv y v = a.linearEquiv ⟨f y, y.property⟩ v := by
  /- Pull the boundary isomorphism back along the induced map from the inverse
  image of A into A. Identify the iterated pullbacks by their vector-preserving
  comparisons. Their induced topologies give continuity in both directions. -/
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let j : C(f ⁻¹' A, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(f ⁻¹' A, A) :=
    ⟨fun y ↦ ⟨f y, y.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  -- Both routes to X have the same original fiber; compare their iterated pullbacks.
  let u : Iso (Restrict ((f : Y → X) *ᵖ E) (f ⁻¹' A))
      ((q : f ⁻¹' A → A) *ᵖ (Restrict E A)) :=
    (pullbackCompIso (E := E) f j).trans (pullbackCompIso (E := E) i q).symm
  let v : Iso (Restrict ((f : Y → X) *ᵖ F) (f ⁻¹' A))
      ((q : f ⁻¹' A → A) *ᵖ (Restrict F A)) :=
    (pullbackCompIso (E := F) f j).trans (pullbackCompIso (E := F) i q).symm
  have hu (y : f ⁻¹' A) (w : E (f y)) : u.linearEquiv y w = w := by
    change ((pullbackCompIso (E := E) i q).linearEquiv y).symm
      ((pullbackCompIso (E := E) f j).linearEquiv y w) = w
    apply ((pullbackCompIso (E := E) i q).linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hv (y : f ⁻¹' A) (w : F (f y)) : v.linearEquiv y w = w := by
    change ((pullbackCompIso (E := F) i q).linearEquiv y).symm
      ((pullbackCompIso (E := F) f j).linearEquiv y w) = w
    apply ((pullbackCompIso (E := F) i q).linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  refine ⟨u.trans ((a.pullback q).trans v.symm), ?_⟩
  intro y w
  -- The resulting boundary map retains the prescribed value at f(y).
  change (v.linearEquiv y).symm (a.linearEquiv (q y) (u.linearEquiv y w)) = _
  apply (v.linearEquiv y).injective
  exact ((v.linearEquiv y).apply_symm_apply _).trans
    ((congrArg (a.linearEquiv (q y)) (hu y w)).trans
      (hv y (a.linearEquiv (q y) w)).symm)

/-- The actual boundary triple over an inverse-image pair. -/
def RelativeTriple.pullback (a : RelativeTriple E F A) (f : C(Y, X)) :
    RelativeTriple ((f : Y → X) *ᵖ E) ((f : Y → X) *ᵖ F) (f ⁻¹' A) :=
  (a.exists_pullback f).choose

/-- Triple pullback retains the original boundary fiber map. -/
theorem RelativeTriple.pullback_apply (a : RelativeTriple E F A) (f : C(Y, X))
    (y : (f ⁻¹' A)) (v : E (f y)) :
    (a.pullback f).linearEquiv y v = a.linearEquiv ⟨f y, y.property⟩ v := by
  /- Apply the fiber identity in the theorem used to choose the pulled-back
  triple. In particular, no arbitrary isomorphism of the restricted bundles is chosen. -/
  exact (a.exists_pullback f).choose_spec y v

variable [hX : CompactSpace X] [hT : T2Space X] [hE : IsFiniteRank E]

include hX hT hE

open scoped Matrix Matrix.Norms.Operator

attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
attribute [local instance] IdempotentMatrix.isFiniteRank_fiber
attribute [local instance] trivialTopology isFiniteRank_trivial

/-- Karoubi II.2.24: a boundary automorphism homotopy lifts with fixed start. -/
theorem exists_lift_restriction_homotopy (A : Set X) (hA : IsClosed A)
    (e : Iso E E) (a : RelativeTriple E E A) (H : IsoHomotopy (e.restrict A) a) :
    ∃ f : Iso E E, ∃ K : IsoHomotopy e f,
      ∀ t : I, ∀ x : A, ∀ v : E x,
        K.iso.linearEquiv (t, x.val) v = H.iso.linearEquiv (t, x) v := by
  /- Present E as the image of one continuous idempotent. Extend the given
  automorphisms by identity on its complementary image, and lift their matrix
  path inside the centralizer of that same idempotent. Restrict the lifted
  matrices back to the image and transport through the original presentation.
  Every conversion retains the given homotopy at all times, not only endpoints. -/
  classical
  let : CompactSpace A := hA.isClosedEmbedding_subtypeVal.compactSpace
  let p := idempotentPresentation (E := E)
  let θ : Iso E (fun x ↦ p.fiber x) := presentationIso
  let C : X → Type _ := fun x ↦ p.complement.fiber x
  let S : Iso (E ×ᵇ C) (Bundle.Trivial X (Fin p.size → ℂ)) :=
    (θ.sum (Iso.refl C)).trans p.complementIso
  let P (x : X) : Matrix (Fin p.size) (Fin p.size) ℂ :=
    (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix p.matrix
  have hPP (x : X) : P x * P x = P x :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  -- The one fixed splitting identifies p with the first summand projection.
  have hS (x : X) (v : E x) (w : C x) :
      S.linearEquiv x (v, w) = (θ.linearEquiv x v).val + w.val := rfl
  have hprojection (x : X) (v : E x) (w : C x) :
      P x *ᵥ S.linearEquiv x (v, w) = S.linearEquiv x (v, 0) := by
    have hfix : P x *ᵥ (θ.linearEquiv x v).val = (θ.linearEquiv x v).val := by
      obtain ⟨u, hu⟩ : ∃ u : Fin p.size → ℂ, P x *ᵥ u =
          (θ.linearEquiv x v).val := (θ.linearEquiv x v).property
      rw [← hu, Matrix.mulVec_mulVec, hPP]
    have hzero : P x *ᵥ w.val = 0 := by
      let Q := (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix p.complement.matrix
      have hQ : Q = 1 - P x := by
        change (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (1 - p.matrix) = _
        rw [map_sub, map_one]
      obtain ⟨u, hu⟩ : ∃ u : Fin p.size → ℂ, Q *ᵥ u = w.val := w.property
      rw [hQ] at hu
      rw [← hu, Matrix.mulVec_mulVec]
      have hz : P x * (1 - P x) = 0 := by
        rw [mul_sub, mul_one, hPP, sub_self]
      rw [hz, Matrix.zero_mulVec]
    rw [hS, Matrix.mulVec_add, hfix, hzero, hS]
    rfl
  let extendFiber (x : X) (g : E x ≃ₗ[ℂ] E x) :
      (Fin p.size → ℂ) ≃ₗ[ℂ] (Fin p.size → ℂ) :=
    (S.linearEquiv x).symm.trans
      ((g.prodCongr (LinearEquiv.refl ℂ (C x))).trans (S.linearEquiv x))
  have hextend (x : X) (g : E x ≃ₗ[ℂ] E x) (v : E x) (w : C x) :
      extendFiber x g (S.linearEquiv x (v, w)) = S.linearEquiv x (g v, w) := by
    exact congrArg (fun z : E x × C x ↦ S.linearEquiv x (g z.1, z.2))
      ((S.linearEquiv x).symm_apply_apply (v, w))
  have hcomm (x : X) (g : E x ≃ₗ[ℂ] E x) (v : Fin p.size → ℂ) :
      extendFiber x g (P x *ᵥ v) = P x *ᵥ extendFiber x g v := by
    obtain ⟨⟨w, z⟩, rfl⟩ := (S.linearEquiv x).surjective v
    rw [hprojection, hextend, hextend, hprojection]
  -- Extend any prescribed pullback automorphism by identity on the same complement.
  have extend : ∀ {Y : Type _} [TopologicalSpace Y] (f : C(Y, X))
      (D : Iso ((f : Y → X) *ᵖ E) ((f : Y → X) *ᵖ E)),
      ∃ U : Iso (Bundle.Trivial Y (Fin p.size → ℂ))
          (Bundle.Trivial Y (Fin p.size → ℂ)),
        ∀ y v, U.linearEquiv y v = extendFiber (f y) (D.linearEquiv y) v := by
    intro Y inst f D
    let f' : Y → X := f
    have hin : Continuous (fun z : TotalSpace Unit (f' *ᵖ (E ×ᵇ C)) ↦
        (⟨z.proj, z.snd.1⟩ : TotalSpace Unit (f' *ᵖ E))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E f').continuous_iff]
      exact (Pullback.continuous_proj Unit (E ×ᵇ C) f').prodMk
        (continuous_sum_fst.comp (Pullback.continuous_lift Unit (E ×ᵇ C) f'))
    have hsecond : Continuous (fun z : TotalSpace Unit (f' *ᵖ (E ×ᵇ C)) ↦
        (⟨f' z.proj, z.snd.2⟩ : TotalSpace Unit C)) :=
      continuous_sum_snd.comp (Pullback.continuous_lift Unit (E ×ᵇ C) f')
    let B : Iso (f' *ᵖ (E ×ᵇ C)) (f' *ᵖ (E ×ᵇ C)) :=
      { linearEquiv := fun y ↦ (D.linearEquiv y).prodCongr (LinearEquiv.refl ℂ (C (f y)))
        continuous_total := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (E ×ᵇ C) f').continuous_iff]
          apply (Pullback.continuous_proj Unit (E ×ᵇ C) f').prodMk
          apply continuous_induced_rng.mpr
          exact ((Pullback.continuous_lift Unit E f').comp
            (D.continuous_total.comp hin)).prodMk
            hsecond
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (E ×ᵇ C) f').continuous_iff]
          apply (Pullback.continuous_proj Unit (E ×ᵇ C) f').prodMk
          apply continuous_induced_rng.mpr
          exact ((Pullback.continuous_lift Unit E f').comp
            (D.continuous_symm.comp hin)).prodMk
            hsecond }
    let T := (S.pullback f).trans (pullbackTrivialIso f p.size)
    have hT (y : Y) : T.linearEquiv y = S.linearEquiv (f y) := by
      apply LinearEquiv.ext
      intro v
      exact pullbackTrivialIso_apply f p.size y (S.linearEquiv (f y) v)
    refine ⟨T.symm.trans (B.trans T), ?_⟩
    intro y v
    change T.linearEquiv y ((D.linearEquiv y).prodCongr
      (LinearEquiv.refl ℂ (C (f y))) ((T.linearEquiv y).symm v)) = _
    rw [hT]
    rfl
  -- Record matrix entries as actual continuous coordinate sections, in both directions.
  have encode : ∀ {Y : Type _} [TopologicalSpace Y]
      (U : Iso (Bundle.Trivial Y (Fin p.size → ℂ))
        (Bundle.Trivial Y (Fin p.size → ℂ))),
      ∃ u : (Matrix (Fin p.size) (Fin p.size) C(Y, ℂ))ˣ,
        ∀ y v,
          ((ContinuousMap.evalAlgHom ℂ ℂ y).toRingHom.mapMatrix u.val) *ᵥ v =
            U.linearEquiv y v := by
    intro Y inst U
    let coeff (D : Iso (Bundle.Trivial Y (Fin p.size → ℂ))
        (Bundle.Trivial Y (Fin p.size → ℂ))) :
        Matrix (Fin p.size) (Fin p.size) C(Y, ℂ) := fun i j ↦
      ⟨fun y ↦ D.linearEquiv y (Pi.single j 1) i, by
        have hs : Continuous (fun y : Y ↦
            (⟨y, Pi.single j 1⟩ : TotalSpace Unit (Bundle.Trivial Y (Fin p.size → ℂ)))) := by
          apply continuous_induced_rng.mpr
          exact continuous_id.prodMk continuous_const
        have hc : Continuous (fun z : TotalSpace Unit
            (Bundle.Trivial Y (Fin p.size → ℂ)) ↦ (z.proj, z.snd)) := continuous_induced_dom
        exact (continuous_apply i).comp (hc.snd.comp (D.continuous_total.comp hs))⟩
    have heval (D : Iso (Bundle.Trivial Y (Fin p.size → ℂ))
        (Bundle.Trivial Y (Fin p.size → ℂ))) (y : Y) :
        (ContinuousMap.evalAlgHom ℂ ℂ y).toRingHom.mapMatrix (coeff D) =
          LinearMap.toMatrix' (D.linearEquiv y).toLinearMap := rfl
    have hinverse (D : Iso (Bundle.Trivial Y (Fin p.size → ℂ))
        (Bundle.Trivial Y (Fin p.size → ℂ))) : coeff D * coeff D.symm = 1 := by
      ext i j y
      have hm := congrArg (fun M : Matrix (Fin p.size) (Fin p.size) ℂ ↦ M i j)
        (show (ContinuousMap.evalAlgHom ℂ ℂ y).toRingHom.mapMatrix
            (coeff D * coeff D.symm) =
            (ContinuousMap.evalAlgHom ℂ ℂ y).toRingHom.mapMatrix 1 from by
          rw [map_mul, map_one, heval, heval, ← LinearMap.toMatrix'_comp]
          change LinearMap.toMatrix' ((D.linearEquiv y).toLinearMap.comp
            ((D.linearEquiv y).symm.toLinearMap)) = 1
          have hid : (D.linearEquiv y).toLinearMap.comp
              ((D.linearEquiv y).symm.toLinearMap) = LinearMap.id := by
            apply LinearMap.ext
            intro v
            exact (D.linearEquiv y).apply_symm_apply v
          rw [hid, LinearMap.toMatrix'_id])
      exact hm
    refine ⟨{ val := coeff U
              inv := coeff U.symm
              val_inv := hinverse U
              inv_val := hinverse U.symm }, ?_⟩
    intro y v
    rw [heval, LinearMap.toMatrix'_mulVec]
    rfl
  obtain ⟨U₀, hU₀⟩ := extend (ContinuousMap.id X) (e.pullback (ContinuousMap.id X))
  obtain ⟨u₀, hu₀⟩ := encode U₀
  have h₀ (x : X) (v : Fin p.size → ℂ) :
      (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix u₀.val *ᵥ v =
        extendFiber x (e.linearEquiv x) v := (hu₀ x v).trans (hU₀ x v)
  let j : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(I × A, A) := ⟨Prod.snd, continuous_snd⟩
  let J := pullbackCompIso (E := E) j q
  let D : Iso (((j.comp q : C(I × A, X)) : I × A → X) *ᵖ E)
      (((j.comp q : C(I × A, X)) : I × A → X) *ᵖ E) :=
    J.symm.trans (H.iso.trans J)
  have hD (z : I × A) : D.linearEquiv z = H.iso.linearEquiv z := by
    have hJ : J.linearEquiv z = LinearEquiv.refl ℂ (E z.2) := by
      apply LinearEquiv.ext
      exact pullbackCompIso_apply j q z
    change (J.linearEquiv z).symm.trans ((H.iso.linearEquiv z).trans
      (J.linearEquiv z)) = _
    rw [hJ]
    rfl
  obtain ⟨UH, hUH⟩ := extend (j.comp q) D
  obtain ⟨uH, huH⟩ := encode UH
  have hH (z : I × A) (v : Fin p.size → ℂ) :
      (ContinuousMap.evalAlgHom ℂ ℂ z).toRingHom.mapMatrix uH.val *ᵥ v =
        extendFiber z.2 (H.iso.linearEquiv z) v := by
    rw [huH, hUH, hD]
    rfl
  let slice (t : I) : C(I × A, ℂ) →+* C(A, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ
      ⟨fun x ↦ (t, x), continuous_const.prodMk continuous_id⟩).toRingHom
  let b : C(I, (Matrix (Fin p.size) (Fin p.size) C(A, ℂ))ˣ) :=
    ⟨fun t ↦ Units.map (slice t).mapMatrix.toMonoidHom uH, by
      apply Units.continuous_iff.mpr
      constructor
      · exact continuous_pi fun i ↦ continuous_pi fun k ↦ (uH.val i k).curry.continuous
      · exact continuous_pi fun i ↦ continuous_pi fun k ↦ (uH.inv i k).curry.continuous⟩
  have hb (t : I) (x : A) (v : Fin p.size → ℂ) :
      (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (b t).val *ᵥ v =
        extendFiber x (H.iso.linearEquiv (t, x)) v := hH (t, x) v
  have hmatrix (x : X) (g : E x ≃ₗ[ℂ] E x)
      (N : Matrix (Fin p.size) (Fin p.size) ℂ)
      (hN : ∀ v, N *ᵥ v = extendFiber x g v) : Commute N (P x) := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    change (N * P x) *ᵥ v = (P x * N) *ᵥ v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hN, hN]
    exact hcomm x g v
  let r : Matrix (Fin p.size) (Fin p.size) C(X, ℂ) →+*
      Matrix (Fin p.size) (Fin p.size) C(A, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ j).toRingHom.mapMatrix
  have hcomm₀ : Commute u₀.val p.matrix := by
    ext i k x
    have hc := (hmatrix x (e.linearEquiv x)
      ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix u₀.val) (h₀ x)).eq
    have hmul := congrArg (fun M : Matrix (Fin p.size) (Fin p.size) ℂ ↦ M i k) hc
    change ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix
      (u₀.val * p.matrix)) i k =
      ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (p.matrix * u₀.val)) i k
    rw [map_mul, map_mul]
    exact hmul
  have hcommB (t : I) : Commute (b t).val (r p.matrix) := by
    ext i k x
    have hc := (hmatrix x (H.iso.linearEquiv (t, x))
      ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (b t).val) (hb t x)).eq
    change ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix
      ((b t).val * r p.matrix)) i k =
      ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix
        (r p.matrix * (b t).val)) i k
    rw [map_mul, map_mul]
    exact congrArg (fun M : Matrix (Fin p.size) (Fin p.size) ℂ ↦ M i k) hc
  have hstart : b 0 = Units.map r.toMonoidHom u₀ := by
    apply Units.ext
    ext i k x
    have hm : (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (b 0).val =
        (ContinuousMap.evalAlgHom ℂ ℂ (x : X)).toRingHom.mapMatrix u₀.val := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      change _ *ᵥ v = _ *ᵥ v
      rw [hb, h₀]
      have heq : H.iso.linearEquiv (0, x) = e.linearEquiv x := by
        apply LinearEquiv.ext
        exact H.map_zero x
      rw [heq]
    exact congrArg (fun M : Matrix (Fin p.size) (Fin p.size) ℂ ↦ M i k) hm
  -- Lift in the centralizer of this same p, preserving the complete boundary path.
  obtain ⟨c, hc₀, hcA, hcP⟩ := exists_unit_path_lift_restrict_commuting
    p.size p.matrix p.mul_self A hA u₀ hcomm₀ b hcommB hstart
  let V : X → Type := fun x ↦ p.fiber x
  let ev (x : X) : Matrix (Fin p.size) (Fin p.size) C(X, ℂ) →+*
      Matrix (Fin p.size) (Fin p.size) ℂ :=
    (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix
  let u (t : I) (x : X) : (Matrix (Fin p.size) (Fin p.size) ℂ)ˣ :=
    Units.map (ev x).toMonoidHom (c t)
  have huc (t : I) (x : X) : Commute (u t x).val (P x) := by
    change ev x (c t).val * ev x p.matrix = ev x p.matrix * ev x (c t).val
    rw [← map_mul, ← map_mul]
    exact congrArg (ev x) (hcP t).eq
  have hpreserves (x : X) (v : (Matrix (Fin p.size) (Fin p.size) ℂ)ˣ)
      (hv : Commute v.val (P x)) (w : V x) : v.val *ᵥ w.val ∈ p.fiber x := by
    obtain ⟨z, hz⟩ : ∃ z : Fin p.size → ℂ, P x *ᵥ z = w.val := w.property
    refine ⟨v.val *ᵥ z, ?_⟩
    change P x *ᵥ (v.val *ᵥ z) = v.val *ᵥ w.val
    rw [← hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hv.eq]
  let L (t : I) (x : X) : V x ≃ₗ[ℂ] V x :=
    { toFun := fun w ↦ ⟨(u t x).val *ᵥ w.val, hpreserves x (u t x) (huc t x) w⟩
      invFun := fun w ↦ ⟨(u t x).inv *ᵥ w.val,
        hpreserves x (u t x)⁻¹ (huc t x).units_inv_left w⟩
      left_inv := by
        intro w
        apply Subtype.ext
        change (u t x).inv *ᵥ ((u t x).val *ᵥ w.val) = w.val
        rw [Matrix.mulVec_mulVec, (u t x).inv_val, Matrix.one_mulVec]
      right_inv := by
        intro w
        apply Subtype.ext
        change (u t x).val *ᵥ ((u t x).inv *ᵥ w.val) = w.val
        rw [Matrix.mulVec_mulVec, (u t x).val_inv, Matrix.one_mulVec]
      map_add' := by
        intro v w
        apply Subtype.ext
        change (u t x).val *ᵥ (v.val + w.val) =
          (u t x).val *ᵥ v.val + (u t x).val *ᵥ w.val
        exact Matrix.mulVec_add _ _ _
      map_smul' := by
        intro z w
        apply Subtype.ext
        change (u t x).val *ᵥ (z • w.val) = z • ((u t x).val *ᵥ w.val)
        exact Matrix.mulVec_smul _ _ _ }
  -- Matrix evaluation is jointly continuous, including the actual inverse units.
  have hcontinuous (d : C(I, (Matrix (Fin p.size) (Fin p.size) C(X, ℂ))ˣ)) :
      Continuous (fun z : I × X ↦ ev z.2 (d z.1).val) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    have hvalue : Continuous (fun z : I × X ↦ (d z.1).val) :=
      Units.continuous_val.comp (d.continuous.comp continuous_fst)
    have hentry : Continuous (fun z : I × X ↦ (d z.1).val i k) :=
      (continuous_apply k).comp ((continuous_apply i).comp hvalue)
    exact hentry.eval continuous_snd
  let cInv : C(I, (Matrix (Fin p.size) (Fin p.size) C(X, ℂ))ˣ) :=
    ⟨fun t ↦ (c t)⁻¹, continuous_inv.comp c.continuous⟩
  let πX : C(I × X, X) := ⟨Prod.snd, continuous_snd⟩
  have hcoords : Continuous (fun z : TotalSpace Unit ((πX : I × X → X) *ᵖ V) ↦
      z.snd.val) := by
    have hV : Continuous (fun z : TotalSpace Unit V ↦ (z.proj, z.snd.val)) :=
      continuous_induced_dom
    exact hV.snd.comp (Pullback.continuous_lift Unit V πX)
  let B : Iso ((πX : I × X → X) *ᵖ V) ((πX : I × X → X) *ᵖ V) :=
    { linearEquiv := fun z ↦ L z.1 z.2
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit V πX).continuous_iff]
        apply (Pullback.continuous_proj Unit V πX).prodMk
        apply continuous_induced_rng.mpr
        apply (Pullback.continuous_proj Unit V πX).snd.prodMk
        exact ((hcontinuous c).comp (Pullback.continuous_proj Unit V πX)).matrix_mulVec
          hcoords
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit V πX).continuous_iff]
        apply (Pullback.continuous_proj Unit V πX).prodMk
        apply continuous_induced_rng.mpr
        apply (Pullback.continuous_proj Unit V πX).snd.prodMk
        exact ((hcontinuous cInv).comp (Pullback.continuous_proj Unit V πX)).matrix_mulVec
          hcoords }
  let T := θ.pullback πX
  let Kiso : Iso ((πX : I × X → X) *ᵖ E) ((πX : I × X → X) *ᵖ E) :=
    T.trans (B.trans T.symm)
  have hK (t : I) (x : X) (v : E x) :
      (θ.linearEquiv x (Kiso.linearEquiv (t, x) v)).val =
        ev x (c t).val *ᵥ (θ.linearEquiv x v).val := by
    change (θ.linearEquiv x ((θ.linearEquiv x).symm
      (L t x (θ.linearEquiv x v)))).val = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hstartK (x : X) (v : E x) : Kiso.linearEquiv (0, x) v = e.linearEquiv x v := by
    apply (θ.linearEquiv x).injective
    apply Subtype.ext
    rw [hK, hc₀]
    change _ = (θ.linearEquiv x (e.linearEquiv x v)).val
    rw [h₀]
    have hs₀ : S.linearEquiv x (v, 0) = (θ.linearEquiv x v).val := by
      rw [hS]
      exact add_zero _
    rw [← hs₀, hextend, hS]
    exact add_zero _
  have hboundary (t : I) (x : A) (v : E x) :
      Kiso.linearEquiv (t, x.val) v = H.iso.linearEquiv (t, x) v := by
    apply (θ.linearEquiv x).injective
    apply Subtype.ext
    rw [hK]
    have hval : ev x (c t).val =
        (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (b t).val := by
      exact congrArg (fun w : (Matrix (Fin p.size) (Fin p.size) C(A, ℂ))ˣ ↦
        (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix w.val) (hcA t)
    rw [hval, hb]
    have hs₀ : S.linearEquiv x (v, 0) = (θ.linearEquiv x v).val := by
      rw [hS]
      exact add_zero _
    rw [← hs₀]
    exact (hextend x (H.iso.linearEquiv (t, x)) v 0).trans
      ((hS x (H.iso.linearEquiv (t, x) v) 0).trans (add_zero _))
  -- The endpoint is the actual time-one slice of the constructed cylinder isomorphism.
  have hin (t : I) : Continuous (fun z : TotalSpace Unit E ↦
      (⟨(t, z.proj), z.snd⟩ : TotalSpace Unit ((πX : I × X → X) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E πX).continuous_iff]
    exact (continuous_const.prodMk (continuous_proj (E := E))).prodMk continuous_id
  let f : Iso E E :=
    { linearEquiv := fun x ↦ Kiso.linearEquiv (1, x)
      continuous_total := (Pullback.continuous_lift Unit E πX).comp
        (Kiso.continuous_total.comp (hin 1))
      continuous_symm := (Pullback.continuous_lift Unit E πX).comp
        (Kiso.continuous_symm.comp (hin 1)) }
  exact ⟨f, { iso := Kiso, map_zero := hstartK, map_one := fun _ _ ↦ rfl }, hboundary⟩

/-- An elementary boundary automorphism extends to a global automorphism. -/
theorem RelativeTriple.exists_extension_of_isElementary (A : Set X) (hA : IsClosed A)
    (a : RelativeTriple E E A) (ha : a.IsElementary) :
    ∃ e : Iso E E, e.restrict A = a := by
  /- Lift the elementary homotopy starting from the global identity using the
  preceding lifting theorem. At time one its global endpoint restricts to a;
  fiberwise extensionality turns the endpoint equation into equality of isomorphisms. -/
  obtain ⟨H⟩ := ha
  have hid : (Iso.refl E).restrict A = RelativeTriple.identity E A := by
    apply Iso.ext
    intro x
    rfl
  have H' : IsoHomotopy ((Iso.refl E).restrict A) a := by
    rw [hid]
    exact H
  -- Keep the prescribed elementary homotopy while lifting from the global identity.
  obtain ⟨f, K, hK⟩ := exists_lift_restriction_homotopy A hA (Iso.refl E) a H'
  refine ⟨f, ?_⟩
  apply Iso.ext
  intro x
  apply LinearEquiv.ext
  intro v
  exact (K.map_one x v).symm.trans ((hK 1 x v).trans (H'.map_one x v))

/-- An elementary triple is isomorphic to the identity triple on a closed compact pair. -/
theorem RelativeTriple.isIsomorphic_identity_of_isElementary (A : Set X) (hA : IsClosed A)
    (a : RelativeTriple E E A) (ha : a.IsElementary) :
    a.IsIsomorphic (RelativeTriple.identity E A) := by
  /- Extend the boundary automorphism globally. Use that extension as the source
  isomorphism and the identity as the target isomorphism; their boundary square
  commutes. This is the hypothesis-sensitive bridge from Karoubi to SG elementary triples. -/
  obtain ⟨e, he⟩ := a.exists_extension_of_isElementary A hA ha
  refine ⟨e, Iso.refl E, ?_⟩
  intro x w
  -- The extension is the source map of the original commuting boundary square.
  exact (congrArg (fun b : RelativeTriple E E A ↦ b.linearEquiv x w) he).symm

/-- The absolute difference underlying a finite-rank geometric triple. -/
def RelativeTriple.absoluteClass [IsFiniteRank F]
    (_a : RelativeTriple E F A) : ComplexKZero X :=
  ComplexBundle.kZeroClass E - ComplexBundle.kZeroClass F

/-- Triple isomorphism preserves the underlying absolute difference. -/
theorem RelativeTriple.absoluteClass_eq_of_isIsomorphic
    [IsFiniteRank F] [IsFiniteRank G] [IsFiniteRank H]
    (a : RelativeTriple E F A) (b : RelativeTriple G H A) (h : a.IsIsomorphic b) :
    a.absoluteClass = b.absoluteClass := by
  /- Use the two global isomorphisms in the commuting square. Isomorphism
  invariance of the two bundle K classes identifies the corresponding terms of the
  difference; no boundary homotopy or triple-quotient comparison is needed here. -/
  obtain ⟨u, v, _⟩ := h
  exact congrArg₂ (· - ·) (kZeroClass_eq_of_iso u) (kZeroClass_eq_of_iso v)

/-- A triple has zero absolute restriction on its relative subspace. -/
theorem RelativeTriple.absoluteClass_restrict [IsFiniteRank F]
    (A : Set X) (hA : IsClosed A) (a : RelativeTriple E F A) :
    letI := hA.isClosedEmbedding_subtypeVal.compactSpace
    complexKZeroPullback ⟨(Subtype.val : A → X), continuous_subtype_val⟩ a.absoluteClass = 0 := by
  /- Naturality of bundle K classes identifies the restricted difference with
  the difference of the two restricted bundles. The boundary isomorphism makes
  these classes equal, so their difference is zero. This supplies a necessary
  condition only, not a definition of the relative triple class. -/
  let : CompactSpace A := hA.isClosedEmbedding_subtypeVal.compactSpace
  let : IsFiniteRank (Restrict E A) := isFiniteRank_restrict A
  let : IsFiniteRank (Restrict F A) := isFiniteRank_restrict A
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  -- Naturality identifies the restriction with the actual two boundary bundles.
  change complexKZeroPullback i (kZeroClass E - kZeroClass F) = 0
  rw [map_sub, ← kZeroClass_pullback i, ← kZeroClass_pullback i]
  change kZeroClass (Restrict E A) - kZeroClass (Restrict F A) = 0
  exact sub_eq_zero.mpr (kZeroClass_eq_of_iso a)

end AtiyahSinger.ComplexBundle

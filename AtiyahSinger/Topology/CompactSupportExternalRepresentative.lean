/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyOrdinary
public import AtiyahSinger.Topology.CompactSupportProduct
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup

/-!
# External cup products on specified compact representatives

Public module ID: M1673.

The product uses the actual product compact set and the ordinary projections
as maps of relative pairs. Neither projection is required to be proper.
Excision extends that same product across a product of open embeddings; its
ordinary image is the cup product of the two extended original classes.
This representative interface is used for the supported Chern convolution.

Source: the relative Alexander--Whitney product and singular excision,
Hatcher, Algebraic Topology, Sections 3.2 and 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The external cup of two given relative representatives has their actual product support. -/
def compactSupportCohomologyExternalRepresentative
    (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : relativeSingularCohomology R (K : Set X)ᶜ p)
    (b : relativeSingularCohomology R (L : Set Y)ᶜ q) :
    compactSupportCohomology R (X × Y) (p + q) :=
  let A : Set (X × Y) := Prod.fst ⁻¹' (K : Set X)ᶜ
  let B : Set (X × Y) := Prod.snd ⁻¹' (L : Set Y)ᶜ
  compactSupportCohomologyClass R (X × Y) (K ×ˢ L) (p + q)
    (relativeSingularCohomologyPullback R (ContinuousMap.id (X × Y))
      (A := (K ×ˢ L : Set (X × Y))ᶜ) (B := A ∪ B)
      (fun z hz ↦ by
        change ¬(z.1 ∈ K ∧ z.2 ∈ L) at hz
        exact not_and_or.mp hz) (p + q)
      (relativeSingularCohomologyUnionCup R A B
        (K.isCompact.isClosed.isOpen_compl.preimage continuous_fst)
        (L.isCompact.isClosed.isOpen_compl.preimage continuous_snd) p q
        (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(X × Y, X))
          (A := A) (B := (K : Set X)ᶜ) (fun _ hz ↦ hz) p a)
        (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Y, Y))
          (A := B) (B := (L : Set Y)ᶜ) (fun _ hz ↦ hz) q b)))

set_option maxHeartbeats 800000 in
-- Use the same compact-image excision maps on all three actual total spaces.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Product open extension carries the specified external cup to the ordinary external cup. -/
theorem compactSupportCohomologyExternalRepresentative_openExtension_toOrdinary
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] [T2Space S] [T2Space T]
    (f : C(X, S)) (hf : IsOpenEmbedding f) (g : C(Y, T)) (hg : IsOpenEmbedding g)
    (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : relativeSingularCohomology R (K : Set X)ᶜ p)
    (b : relativeSingularCohomology R (L : Set Y)ᶜ q) :
    compactSupportCohomologyToOrdinary R (S × T) (p + q)
      (compactSupportCohomologyOpenExtension R (f.prodMap g) (hf.prodMap hg) (p + q)
        (compactSupportCohomologyExternalRepresentative R K L p q a b)) =
    singularCohomologyCup R (S × T) p q
      (singularCohomologyPullback R ContinuousMap.fst p
        (compactSupportCohomologyToOrdinary R S p
          (compactSupportCohomologyOpenExtension R f hf p
            (compactSupportCohomologyClass R X K p a))))
      (singularCohomologyPullback R ContinuousMap.snd q
        (compactSupportCohomologyToOrdinary R T q
          (compactSupportCohomologyOpenExtension R g hg q
            (compactSupportCohomologyClass R Y L q b)))) := by
  let A : Set (X × Y) := Prod.fst ⁻¹' (K : Set X)ᶜ
  let B : Set (X × Y) := Prod.snd ⁻¹' (L : Set Y)ᶜ
  let K' := openEmbeddingCompactImage f K
  let L' := openEmbeddingCompactImage g L
  let C : Set (S × T) := Prod.fst ⁻¹' (K' : Set S)ᶜ
  let D : Set (S × T) := Prod.snd ⁻¹' (L' : Set T)ᶜ
  let hA : IsOpen A := K.isCompact.isClosed.isOpen_compl.preimage continuous_fst
  let hB : IsOpen B := L.isCompact.isClosed.isOpen_compl.preimage continuous_snd
  let hC : IsOpen C := K'.isCompact.isClosed.isOpen_compl.preimage continuous_fst
  let hD : IsOpen D := L'.isCompact.isClosed.isOpen_compl.preimage continuous_snd
  let j := f.prodMap g
  let hj : IsOpenEmbedding j := hf.prodMap hg
  let W := (K ×ˢ L)
  let W' := openEmbeddingCompactImage j W
  let PX := openEmbeddingCohomologySupportPullback R f hf K p
  let PY := openEmbeddingCohomologySupportPullback R g hg L q
  let PZ := openEmbeddingCohomologySupportPullback R j hj W (p + q)
  let := isIso_openEmbeddingCohomologySupportPullback R f hf K p
  let := isIso_openEmbeddingCohomologySupportPullback R g hg L q
  let := isIso_openEmbeddingCohomologySupportPullback R j hj W (p + q)
  let a' := (asIso PX).inv a
  let b' := (asIso PY).inv b
  have ha : PX a' = a := (asIso PX).inv_hom_id_apply a
  have hb : PY b' = b := (asIso PY).inv_hom_id_apply b
  let α := relativeSingularCohomologyPullback R (ContinuousMap.fst : C(S × T, S))
    (A := C) (B := (K' : Set S)ᶜ) (fun _ hz ↦ hz) p a'
  let β := relativeSingularCohomologyPullback R (ContinuousMap.snd : C(S × T, T))
    (A := D) (B := (L' : Set T)ᶜ) (fun _ hz ↦ hz) q b'
  have hAC : Set.MapsTo j A C := by
    rintro z hz ⟨x, hx, heq⟩
    exact hz ((hf.injective heq) ▸ hx)
  have hBD : Set.MapsTo j B D := by
    rintro z hz ⟨y, hy, heq⟩
    exact hz ((hg.injective heq) ▸ hy)
  have hW : Set.MapsTo (ContinuousMap.id (X × Y)) (W : Set (X × Y))ᶜ (A ∪ B) := by
    intro z hz
    exact not_and_or.mp hz
  have hW' : Set.MapsTo (ContinuousMap.id (S × T)) (W' : Set (S × T))ᶜ (C ∪ D) := by
    intro z hz
    change z.1 ∉ K' ∨ z.2 ∉ L'
    by_contra h
    obtain ⟨⟨x, hx, hfx⟩, ⟨y, hy, hgy⟩⟩ := not_or.mp h |>.imp not_not.mp not_not.mp
    exact hz ⟨(x, y), ⟨hx, hy⟩, Prod.ext hfx hgy⟩
  let c := relativeSingularCohomologyPullback R (ContinuousMap.id (X × Y)) hW (p + q)
    (relativeSingularCohomologyUnionCup R A B hA hB p q
      (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(X × Y, X))
          (A := A) (B := (K : Set X)ᶜ) (fun _ hz ↦ hz) p a)
      (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Y, Y))
          (A := B) (B := (L : Set Y)ᶜ) (fun _ hz ↦ hz) q b))
  let c' := relativeSingularCohomologyPullback R (ContinuousMap.id (S × T)) hW' (p + q)
    (relativeSingularCohomologyUnionCup R C D hC hD p q α β)
  -- Naturality of the same two-relative product identifies the actual excision inverse.
  have hcomp {Z₁ Z₂ Z₃ : Type u} [TopologicalSpace Z₁] [TopologicalSpace Z₂]
      [TopologicalSpace Z₃] (f₀ : C(Z₁, Z₂)) (g₀ : C(Z₂, Z₃))
      {U₁ : Set Z₁} {U₂ : Set Z₂} {U₃ : Set Z₃}
      (hf₀ : Set.MapsTo f₀ U₁ U₂) (hg₀ : Set.MapsTo g₀ U₂ U₃) (k : ℕ)
      (z : relativeSingularCohomology R U₃ k) :
      relativeSingularCohomologyPullback R f₀ hf₀ k
        (relativeSingularCohomologyPullback R g₀ hg₀ k z) =
      relativeSingularCohomologyPullback R (g₀.comp f₀) (hg₀.comp hf₀) k z :=
    (congrArg (fun t ↦ t z) (relativeSingularCohomologyPullback_comp R f₀ g₀ hf₀ hg₀ k)).symm
  have hα : relativeSingularCohomologyPullback R j hAC p α =
      relativeSingularCohomologyPullback R (ContinuousMap.fst : C(X × Y, X))
        (A := A) (B := (K : Set X)ᶜ) (fun _ hz ↦ hz) p a := by
    have h₁ := hcomp j (ContinuousMap.fst : C(S × T, S)) hAC
      (show Set.MapsTo ContinuousMap.fst C (K' : Set S)ᶜ from fun _ hz ↦ hz) p a'
    have h₂ := hcomp (ContinuousMap.fst : C(X × Y, X)) f
      (show Set.MapsTo ContinuousMap.fst A (K : Set X)ᶜ from fun _ hz ↦ hz)
      (show Set.MapsTo f (K : Set X)ᶜ (K' : Set S)ᶜ from fun x hx h ↦
        hx (by obtain ⟨y, hy, hyx⟩ := h; exact hf.injective hyx ▸ hy)) p a'
    exact h₁.trans (h₂.symm.trans (congrArg
      (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(X × Y, X))
        (A := A) (B := (K : Set X)ᶜ) (fun _ hz ↦ hz) p) ha))
  have hβ : relativeSingularCohomologyPullback R j hBD q β =
      relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Y, Y))
        (A := B) (B := (L : Set Y)ᶜ) (fun _ hz ↦ hz) q b := by
    have h₁ := hcomp j (ContinuousMap.snd : C(S × T, T)) hBD
      (show Set.MapsTo ContinuousMap.snd D (L' : Set T)ᶜ from fun _ hz ↦ hz) q b'
    have h₂ := hcomp (ContinuousMap.snd : C(X × Y, Y)) g
      (show Set.MapsTo ContinuousMap.snd B (L : Set Y)ᶜ from fun _ hz ↦ hz)
      (show Set.MapsTo g (L : Set Y)ᶜ (L' : Set T)ᶜ from fun y hy h ↦
        hy (by obtain ⟨x, hx, hxy⟩ := h; exact hg.injective hxy ▸ hx)) q b'
    exact h₁.trans (h₂.symm.trans (congrArg
      (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Y, Y))
        (A := B) (B := (L : Set Y)ᶜ) (fun _ hz ↦ hz) q) hb))
  have hc : PZ c' = c := by
    have hnat := relativeSingularCohomologyPullback_unionCup R j hA hB hC hD hAC hBD p q α β
    rw [hα, hβ] at hnat
    have h₁ := hcomp j (ContinuousMap.id (S × T))
      (show Set.MapsTo j (W : Set (X × Y))ᶜ (W' : Set (S × T))ᶜ from
        fun x hx h ↦ hx (by obtain ⟨y, hy, hyx⟩ := h; exact hj.injective hyx ▸ hy))
      hW' (p + q) (relativeSingularCohomologyUnionCup R C D hC hD p q α β)
    have h₂ := hcomp (ContinuousMap.id (X × Y)) j hW
      (show Set.MapsTo j (A ∪ B) (C ∪ D) from
        fun _ hz ↦ hz.elim (fun h ↦ Or.inl (hAC h)) (fun h ↦ Or.inr (hBD h)))
      (p + q) (relativeSingularCohomologyUnionCup R C D hC hD p q α β)
    exact h₁.trans (h₂.symm.trans (congrArg
      (relativeSingularCohomologyPullback R (ContinuousMap.id (X × Y)) hW (p + q)) hnat))
  have hc' : (asIso PZ).inv c = c' := by
    rw [← hc]
    exact (asIso PZ).hom_inv_id_apply c'
  -- Forgetting support commutes with the specified relative pair maps.
  have hforget {Z Z' : Type u} [TopologicalSpace Z] [TopologicalSpace Z']
      (l : C(Z, Z')) {U : Set Z} {V : Set Z'} (hl : Set.MapsTo l U V)
      (k : ℕ) (z : relativeSingularCohomology R V k) :
      relativeSingularCohomologyToOrdinary R U k
        (relativeSingularCohomologyPullback R l hl k z) =
      singularCohomologyPullback R l k (relativeSingularCohomologyToOrdinary R V k z) :=
    congrArg (fun t ↦ t z) (relativeSingularCohomologyPullback_toOrdinary R l hl k)
  have hid {Z : Type u} [TopologicalSpace Z] (k : ℕ) (z : singularCohomology R Z k) :
      singularCohomologyPullback R (ContinuousMap.id Z) k z = z := by
    change (singularCohomologyFunctor R k).map (𝟙 _) z = z
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hcup : relativeSingularCohomologyToOrdinary R (C ∪ D) (p + q)
      (relativeSingularCohomologyUnionCup R C D hC hD p q α β) =
      singularCohomologyCup R (S × T) p q
        (relativeSingularCohomologyToOrdinary R C p α)
        (relativeSingularCohomologyToOrdinary R D q β) := by
    have h := congrArg (relativeSingularCohomologyToOrdinary R D (p + q))
      (relativeSingularCohomologyUnionCup_restrict_right R C D hC hD p q α β)
    rw [relativeSingularCohomologyToOrdinary_action] at h
    change relativeSingularCohomologyToOrdinary R D (p + q)
      (relativeSingularCohomologyPullback R (ContinuousMap.id (S × T))
        (A := D) (B := C ∪ D) (fun _ hz ↦ Or.inr hz) (p + q) _) = _ at h
    rw [hforget, hid] at h
    exact h
  have hleg {Z : Type u} [TopologicalSpace Z] (K₀ : Compacts Z) (k : ℕ)
      (z : relativeSingularCohomology R (K₀ : Set Z)ᶜ k) :
      compactSupportCohomologyToOrdinary R Z k (compactSupportCohomologyClass R Z K₀ k z) =
      relativeSingularCohomologyToOrdinary R (K₀ : Set Z)ᶜ k z := by
    have h : compactSupportCohomologyClass R Z K₀ k ≫
        compactSupportCohomologyToOrdinary R Z k =
      relativeSingularCohomologyToOrdinary R (K₀ : Set Z)ᶜ k := colimit.ι_desc _ K₀
    exact congrArg (fun t ↦ t z) h
  change compactSupportCohomologyToOrdinary R (S × T) (p + q)
    (compactSupportCohomologyOpenExtension R j hj (p + q)
      (compactSupportCohomologyClass R (X × Y) W (p + q) c)) = _
  rw [compactSupportCohomologyOpenExtension_representative,
    compactSupportCohomologyOpenExtension_representative,
    compactSupportCohomologyOpenExtension_representative]
  change compactSupportCohomologyToOrdinary R (S × T) (p + q)
    (compactSupportCohomologyClass R (S × T) W' (p + q) ((asIso PZ).inv c)) =
    singularCohomologyCup R (S × T) p q
      (singularCohomologyPullback R ContinuousMap.fst p
        (compactSupportCohomologyToOrdinary R S p (compactSupportCohomologyClass R S K' p a')))
      (singularCohomologyPullback R ContinuousMap.snd q
        (compactSupportCohomologyToOrdinary R T q (compactSupportCohomologyClass R T L' q b')))
  rw [hc', hleg, hleg, hleg]
  change relativeSingularCohomologyToOrdinary R (W' : Set (S × T))ᶜ (p + q)
    (relativeSingularCohomologyPullback R (ContinuousMap.id (S × T)) hW' (p + q) _) = _
  rw [hforget, hid, hcup]
  exact congrArg₂ (fun a b ↦ singularCohomologyCup R (S × T) p q a b)
    (hforget (ContinuousMap.fst : C(S × T, S))
      (show Set.MapsTo ContinuousMap.fst C (K' : Set S)ᶜ from fun _ hz ↦ hz) p a')
    (hforget (ContinuousMap.snd : C(S × T, T))
      (show Set.MapsTo ContinuousMap.snd D (L' : Set T)ᶜ from fun _ hz ↦ hz) q b')

end AtiyahSinger

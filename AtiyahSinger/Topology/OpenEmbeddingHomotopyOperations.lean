/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Parameter changes and concatenation of open embedding homotopies

Public module ID: M1968.

The relevant openness condition concerns the entire parameter-preserving cylinder map.
A continuous change of parameter preserves this condition, including when the original
cylinder is only an open partial homeomorphism and the new parameters stay in its source.
We pull back both open domains and the actual inverse, so no inverse to the parameter map
or separate assumption about individual slices is needed.

The standard `ContinuousMap.Homotopy.trans` also preserves the open-cylinder condition.
The two clamped affine time changes separately give open cylinders on the whole interval.
On either side of the joining time the image uses the corresponding open image. At the
joining time both maps have the same endpoint, and the intersection of their open images
supplies an open neighborhood. This proves openness of the full concatenated map.

The construction uses mathlib's unchanged homotopy concatenation. Any fixed-subset or
pointwise property preserved by its two branches can therefore be checked directly from
that existing definition. No separation, compactness, or local compactness is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set Topology
open scoped unitInterval

variable {A C X Y : Type*} [TopologicalSpace A] [TopologicalSpace C]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back a parameter-preserving partial cylinder gives an open embedding when the
new parameterized source is contained in the original open source. -/
theorem isOpenEmbedding_parameter_comp
    (e : OpenPartialHomeomorph (A × X) (A × Y))
    (he : ∀ p ∈ e.source, (e p).1 = p.1)
    (hei : ∀ p ∈ e.target, (e.symm p).1 = p.1)
    (a : C → A) (ha : Continuous a)
    (hs : ∀ p : C × X, (a p.1, p.2) ∈ e.source) :
    IsOpenEmbedding (fun p : C × X ↦ (p.1, (e (a p.1, p.2)).2)) := by
  let jX : C × X → A × X := fun p ↦ (a p.1, p.2)
  let jY : C × Y → A × Y := fun p ↦ (a p.1, p.2)
  have hjX : Continuous jX := (ha.comp continuous_fst).prodMk continuous_snd
  have hjY : Continuous jY := (ha.comp continuous_fst).prodMk continuous_snd
  have hforward (p : C × X) (hp : jX p ∈ e.source) :
      (a p.1, (e (jX p)).2) = e (jX p) := Prod.ext (he _ hp).symm rfl
  have hinverse (p : C × Y) (hp : jY p ∈ e.target) :
      (a p.1, (e.symm (jY p)).2) = e.symm (jY p) := Prod.ext (hei _ hp).symm rfl
  -- Pull back both open domains and the same inverse along the continuous parameter map.
  let K : OpenPartialHomeomorph (C × X) (C × Y) :=
    { toFun := fun p ↦ (p.1, (e (jX p)).2)
      invFun := fun p ↦ (p.1, (e.symm (jY p)).2)
      source := jX ⁻¹' e.source
      target := jY ⁻¹' e.target
      map_source' := fun p hp ↦ by
        change (a p.1, (e (jX p)).2) ∈ e.target
        rw [hforward p hp]
        exact e.map_source hp
      map_target' := fun p hp ↦ by
        change (a p.1, (e.symm (jY p)).2) ∈ e.source
        rw [hinverse p hp]
        exact e.map_target hp
      left_inv' := fun p hp ↦ by
        apply Prod.ext
        · rfl
        · change (e.symm (a p.1, (e (jX p)).2)).2 = p.2
          rw [hforward p hp]
          exact congrArg Prod.snd (e.left_inv hp)
      right_inv' := fun p hp ↦ by
        apply Prod.ext
        · rfl
        · change (e (a p.1, (e.symm (jY p)).2)).2 = p.2
          rw [hinverse p hp]
          exact congrArg Prod.snd (e.right_inv hp)
      open_source := e.open_source.preimage hjX
      open_target := e.open_target.preimage hjY
      continuousOn_toFun := continuous_fst.continuousOn.prodMk
        ((e.continuousOn.comp hjX.continuousOn (fun _ hp ↦ hp)).snd)
      continuousOn_invFun := continuous_fst.continuousOn.prodMk
        ((e.continuousOn_symm.comp hjY.continuousOn (fun _ hp ↦ hp)).snd) }
  exact K.isOpenEmbedding (Set.eq_univ_of_forall hs)

/-- An open embedding cylinder remains an open embedding after any continuous parameter change. -/
theorem isOpenEmbedding_parameter_comp_of_isOpenEmbedding
    (F : A × X → Y) (hF : IsOpenEmbedding (fun p : A × X ↦ (p.1, F p)))
    (a : C → A) (ha : Continuous a) :
    IsOpenEmbedding (fun p : C × X ↦ (p.1, F (a p.1, p.2))) := by
  classical
  cases isEmpty_or_nonempty (C × X) with
  | inl hEmpty =>
    let := hEmpty
    exact IsOpenEmbedding.of_isEmpty _
  | inr hNonempty =>
    let : Nonempty (A × X) := hNonempty.map (fun p ↦ (a p.1, p.2))
    let e := hF.toOpenPartialHomeomorph (fun p : A × X ↦ (p.1, F p))
    have he (p : A × X) (hp : p ∈ e.source) : (e p).1 = p.1 := by
      simp only [e, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    have hei (p : A × Y) (hp : p ∈ e.target) : (e.symm p).1 = p.1 := by
      have h := congrArg Prod.fst (e.right_inv hp)
      rw [he _ (e.map_target hp)] at h
      exact h
    have hs (p : C × X) : (a p.1, p.2) ∈ e.source := by
      simp only [e, IsOpenEmbedding.toOpenPartialHomeomorph_source, mem_univ]
    simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_apply] using
      isOpenEmbedding_parameter_comp e he hei a ha hs

/-- Standard homotopy concatenation preserves openness and embedding of the entire cylinder. -/
theorem isOpenEmbedding_homotopy_trans {f g h : C(X, Y)}
    (F : ContinuousMap.Homotopy f g) (G : ContinuousMap.Homotopy g h)
    (hF : IsOpenEmbedding (fun p : I × X ↦ (p.1, F p)))
    (hG : IsOpenEmbedding (fun p : I × X ↦ (p.1, G p))) :
    IsOpenEmbedding (fun p : I × X ↦ (p.1, (F.trans G) p)) := by
  let L : I × X → I × Y := fun p ↦ (p.1, F.extend (2 * p.1) p.2)
  let R : I × X → I × Y := fun p ↦ (p.1, G.extend (2 * p.1 - 1) p.2)
  let K : I × X → I × Y := fun p ↦ (p.1, (F.trans G) p)
  -- Clamping each affine time coordinate extends its open cylinder across the joining time.
  have hL : IsOpenEmbedding L := by
    exact isOpenEmbedding_parameter_comp_of_isOpenEmbedding F hF
      (fun t : I ↦ Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)))
      (continuous_projIcc.comp (continuous_const.mul continuous_subtype_val))
  have hR : IsOpenEmbedding R := by
    exact isOpenEmbedding_parameter_comp_of_isOpenEmbedding G hG
      (fun t : I ↦ Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))
      (continuous_projIcc.comp
        ((continuous_const.mul continuous_subtype_val).sub continuous_const))
  have hleft (p : I × X) (hp : (p.1 : ℝ) ≤ 1 / 2) : K p = L p := by
    change (p.1, if (p.1 : ℝ) ≤ 1 / 2 then
      F.extend (2 * p.1) p.2 else G.extend (2 * p.1 - 1) p.2) = _
    rw [ite_eq_left hp]
  have hright (p : I × X) (hp : ¬ (p.1 : ℝ) ≤ 1 / 2) : K p = R p := by
    change (p.1, if (p.1 : ℝ) ≤ 1 / 2 then
      F.extend (2 * p.1) p.2 else G.extend (2 * p.1 - 1) p.2) = _
    rw [ite_eq_right hp]
  have hseam (p : I × X) (hp : (p.1 : ℝ) = 1 / 2) : L p = R p := by
    apply Prod.ext
    · rfl
    · change F.extend (2 * p.1) p.2 = G.extend (2 * p.1 - 1) p.2
      norm_num [hp]
  have hKinj : Function.Injective K := by
    intro p q hpq
    have ht := congrArg (fun r : I × Y ↦ r.1) hpq
    change p.1 = q.1 at ht
    by_cases hp : (p.1 : ℝ) ≤ 1 / 2
    · apply hL.injective
      rw [← hleft p hp, ← hleft q (by simpa only [← ht] using hp)]
      exact hpq
    · apply hR.injective
      rw [← hright p hp, ← hright q (by simpa only [← ht] using hp)]
      exact hpq
  have hKopen : IsOpenMap K := by
    intro W hW
    have htime : Continuous (fun p : I × Y ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    -- At the seam both open images contain the same point; their intersection is a neighborhood.
    have himage : K '' W =
        ((L '' W) ∩ {p : I × Y | (p.1 : ℝ) < 1 / 2}) ∪
        ((R '' W) ∩ {p : I × Y | 1 / 2 < (p.1 : ℝ)}) ∪ ((L '' W) ∩ (R '' W)) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        by_cases hlt : (p.1 : ℝ) < 1 / 2
        · apply Or.inl
          apply Or.inl
          rw [hleft p hlt.le]
          exact ⟨⟨p, hp, rfl⟩, hlt⟩
        · by_cases hgt : 1 / 2 < (p.1 : ℝ)
          · apply Or.inl
            apply Or.inr
            rw [hright p (not_le.mpr hgt)]
            exact ⟨⟨p, hp, rfl⟩, hgt⟩
          · have heq : (p.1 : ℝ) = 1 / 2 := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
            apply Or.inr
            rw [hleft p heq.le]
            exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, (hseam p heq).symm⟩⟩
      · rintro ((hz | hz) | hz)
        · rcases hz with ⟨⟨p, hp, rfl⟩, hlt⟩
          exact ⟨p, hp, hleft p hlt.le⟩
        · rcases hz with ⟨⟨p, hp, rfl⟩, hgt⟩
          exact ⟨p, hp, hright p (not_le.mpr hgt)⟩
        · rcases hz with ⟨⟨p, hp, hpz⟩, ⟨q, hq, hqz⟩⟩
          by_cases ht : (z.1 : ℝ) ≤ 1 / 2
          · have hpt : (p.1 : ℝ) = (z.1 : ℝ) := congrArg (fun r : I × Y ↦ (r.1 : ℝ)) hpz
            exact ⟨p, hp, (hleft p (hpt ▸ ht)).trans hpz⟩
          · have hqt : (q.1 : ℝ) = (z.1 : ℝ) := congrArg (fun r : I × Y ↦ (r.1 : ℝ)) hqz
            exact ⟨q, hq, (hright q (hqt ▸ ht)).trans hqz⟩
    rw [himage]
    exact (((hL.isOpenMap W hW).inter (isOpen_lt htime continuous_const)).union
      ((hR.isOpenMap W hW).inter (isOpen_lt continuous_const htime))).union
        ((hL.isOpenMap W hW).inter (hR.isOpenMap W hW))
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_fst.prodMk (F.trans G).continuous) hKinj hKopen

end AtiyahSinger

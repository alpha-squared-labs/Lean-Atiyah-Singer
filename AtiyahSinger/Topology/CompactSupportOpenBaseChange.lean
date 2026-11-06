/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportFunctoriality
public import AtiyahSinger.Topology.OpenEmbeddingKZero

/-!
# Proper pullback across an actual open square

Public module ID: M1680.

The original reverse one-point collapse maps commute for a cartesian open
square. The induced equality compares exactly the specified proper pullback
and open extension maps, including points outside the common open image.
This makes the existing local square argument from KTheoryMayerVietoris
available for the associated twisted product without importing its later
K-theory boundary theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

/-- Proper pullback commutes with open extension through the specified cartesian square. -/
theorem compactSupportKZeroPullback_openPushforward_square
    {P : Type _} {Q : Type _} {P' : Type _} {Q' : Type _}
    [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
    [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
    [TopologicalSpace P'] [LocallyCompactSpace P'] [T2Space P']
    [TopologicalSpace Q'] [LocallyCompactSpace Q'] [T2Space Q']
    (j : Q' → Q) (hj : IsOpenEmbedding j) (k : P' → P) (hk : IsOpenEmbedding k)
    (g : C(P, Q)) (hg : IsProperMap g) (h : C(P', Q')) (hh : IsProperMap h)
    (hsquare : ∀ x : P', g (k x) = j (h x))
    (himage : ∀ x : P, g x ∈ Set.range j ↔ x ∈ Set.range k) :
    (compactSupportKZeroPullback g hg).comp (compactSupportKZeroOpenPushforward j hj) =
      (compactSupportKZeroOpenPushforward k hk).comp (compactSupportKZeroPullback h hh) := by
  let := hj.isOpen_range.locallyCompactSpace
  let := hk.isOpen_range.locallyCompactSpace
  let ej := hj.isEmbedding.toHomeomorph
  let ek := hk.isEmbedding.toHomeomorph
  let ij : C(Set.range j, Q') := ⟨ej.symm, ej.symm.continuous⟩
  let ik : C(Set.range k, P') := ⟨ek.symm, ek.symm.continuous⟩
  let cj : C(OnePoint Q, OnePoint Q') :=
    (properOnePointMap ij ej.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
  let ck : C(OnePoint P, OnePoint P') :=
    (properOnePointMap ik ek.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range k), continuous_onePointCollapse _ hk.isOpen_range⟩
  have hcj (x : Q') : cj (j x) = (x : OnePoint Q') := by
    change OnePoint.map ij (onePointCollapse (Set.range j) (j x)) = (x : OnePoint Q')
    rw [onePointCollapse_coe_of_mem (Set.range j) (j x) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hj.isEmbedding.toHomeomorph_symm_apply x)
  have hck (x : P') : ck (k x) = (x : OnePoint P') := by
    change OnePoint.map ik (onePointCollapse (Set.range k) (k x)) = (x : OnePoint P')
    rw [onePointCollapse_coe_of_mem (Set.range k) (k x) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hk.isEmbedding.toHomeomorph_symm_apply x)
  have hpointed : cj.comp (properOnePointMap g hg) =
      (properOnePointMap h hh).comp ck := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      by_cases hx : x ∈ Set.range k
      · obtain ⟨x, rfl⟩ := hx
        change cj (g (k x)) = (properOnePointMap h hh) (ck (k x))
        rw [hsquare, hcj, hck]
        rfl
      · have hgx : g x ∉ Set.range j := fun hxj ↦ hx ((himage x).mp hxj)
        change OnePoint.map ij (onePointCollapse (Set.range j) (g x)) =
          (properOnePointMap h hh)
            (OnePoint.map ik (onePointCollapse (Set.range k) x))
        rw [onePointCollapse_coe_of_notMem _ _ hgx,
          onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty, OnePoint.map_infty]
        rfl
  have heq := congrArg complexKZeroPullback hpointed
  simp only [cj, ck, complexKZeroPullback_comp] at heq
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun heq a.val

end AtiyahSinger

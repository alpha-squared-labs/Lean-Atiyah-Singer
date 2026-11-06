/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteSimplicialRealization
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# The realized boundary of a standard simplex

Public module ID: M2119.

The original geometric realization sends the original simplicial boundary
inclusion to a closed embedding. Every realized boundary point is represented
on a codimension-one face. Equal barycentric coordinates on distinct faces
lie on their common face, where the original simplicial maps already agree.
Compactness of the finite boundary then upgrades injectivity to a closed
embedding into the Hausdorff standard simplex.

The zero-dimensional empty boundary and the two vertices of the one-dimensional
simplex are included. This is the boundary attachment input for the finite
skeleton realization argument; no different realization model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Convexity Set Topology

open scoped Simplicial

universe u

namespace SSet

/-- The original realized boundary inclusion is a closed embedding in every dimension. -/
theorem isClosedEmbedding_toTop_boundary (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (SSet.boundary.{u} n).ι) := by
  classical
  let : CompactSpace |(boundary.{u} n : SSet)| := compactSpace_toTop_of_finite _
  let : T2Space (StdSimplex ℝ (Fin (n + 1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  apply (SSet.toTop.map (boundary.{u} n).ι).hom.continuous.isClosedEmbedding
  -- Affine cofaces are injective because extending barycentric weights along
  -- an injective vertex map is injective. Transport through the original simplex homeomorphism.
  have hmap_injective (d : ℕ) (i : Fin (d + 2)) :
      Function.Injective (StdSimplex.map (R := ℝ) i.succAbove) := by
    intro a b hab
    apply StdSimplex.ext
    exact Finsupp.mapDomain_injective Fin.succAbove_right_injective
      (congrArg StdSimplex.weights hab)
  have hface_injective (d : ℕ) (i : Fin (d + 2)) :
      Function.Injective (SSet.toTop.map (stdSimplex.{u}.δ i)) := by
    intro a b hab
    apply (SimplexCategory.toTopHomeo ⦋d⦌).injective
    apply hmap_injective d i
    simpa only [CosimplicialObject.δ, SimplexCategory.toTopHomeo_naturality_apply,
      SimplexCategory.coe_δ] using
      congrArg (SimplexCategory.toTopHomeo ⦋d + 1⦌) hab
  cases n with
  | zero =>
    -- The empty boundary maps by adjunction to an empty topological space.
    let Z := TopCat.of (ULift.{u} Empty)
    have h : (boundary.{u} 0 : SSet) ⟶ TopCat.toSSet.obj Z := by
      rw [boundary_zero]
      exact Subcomplex.isInitialBot.to _
    let q := (sSetTopAdj.homEquiv (boundary.{u} 0) Z).symm h
    intro x y _
    exact (q x).down.elim
  | succ n =>
    let F (i : Fin (n + 2)) : |(Δ[n] : SSet.{u})| → |(boundary.{u} (n + 1) : SSet)| :=
      SSet.toTop.map (boundary.ι i)
    let D (i : Fin (n + 2)) : |(Δ[n] : SSet.{u})| → |(Δ[n + 1] : SSet.{u})| :=
      SSet.toTop.map (stdSimplex.δ i)
    let inclusion := SSet.toTop.map (boundary.{u} (n + 1)).ι
    have hinc (i : Fin (n + 2)) (a : |(Δ[n] : SSet.{u})|) :
        inclusion (F i a) = D i a := by
      have h := congrArg (fun g ↦ SSet.toTop.map g) (boundary.ι_ι.{u} i)
      rw [Functor.map_comp] at h
      exact congrArg (fun g ↦ g a) h
    -- The coproduct of the original cofaces is epi by the boundary universal
    -- property. Realization preserves that epi and its coproduct, giving this actual face cover.
    have hcover (x : |(boundary.{u} (n + 1) : SSet)|) :
        ∃ (i : Fin (n + 2)) (a : |(Δ[n] : SSet.{u})|), F i a = x := by
      let V : Fin (n + 2) → SSet.{u} := fun _ ↦ Δ[n]
      let p : ∐ V ⟶ (boundary.{u} (n + 1) : SSet) := Sigma.desc (fun i ↦ boundary.ι i)
      let : Epi p := ⟨by
        intro Z f g hfg
        apply boundary.hom_ext
        intro i
        have h := congrArg (fun q ↦ Sigma.ι V i ≫ q) hfg
        simpa only [p, Category.assoc, Sigma.ι_comp_desc_assoc] using h⟩
      have hsurj : Function.Surjective (SSet.toTop.map p) :=
        (TopCat.epi_iff_surjective _).mp inferInstance
      obtain ⟨z, hz⟩ := hsurj x
      obtain ⟨⟨i⟩, a, ha⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (SSet.toTop ⋙ forget TopCat)
          (colimit.isColimit (Discrete.functor V))) z
      refine ⟨i, a, ?_⟩
      have h : SSet.toTop.map (Sigma.ι V i) ≫ SSet.toTop.map p =
          SSet.toTop.map (boundary.ι i) := by
        rw [← Functor.map_comp]
        simp only [p, Sigma.ι_comp_desc]
      exact (congrArg (fun q ↦ q a) h).symm.trans
        ((congrArg (SSet.toTop.map p) ha).trans hz)
    -- Representatives from distinct faces have zero weight at both omitted
    -- vertices. Their common-face representative supplies equality already in the boundary.
    have hpair (i j : Fin (n + 2)) (a b : |(Δ[n] : SSet.{u})|)
        (hij : i < j) (hab : D i a = D j b) : F i a = F j b := by
      have hcoordinates :
          StdSimplex.map i.succAbove (SimplexCategory.toTopHomeo ⦋n⦌ a) =
            StdSimplex.map j.succAbove (SimplexCategory.toTopHomeo ⦋n⦌ b) := by
        simpa only [D, CosimplicialObject.δ, SimplexCategory.toTopHomeo_naturality_apply,
          SimplexCategory.coe_δ] using
          congrArg (SimplexCategory.toTopHomeo ⦋n + 1⦌) hab
      let w : StdSimplex ℝ (Fin (n + 2)) :=
        StdSimplex.map i.succAbove (SimplexCategory.toTopHomeo ⦋n⦌ a)
      have hwi : w.weights i = 0 :=
        (StdSimplex.mem_range_map_iff i.succAbove w).mp
          ⟨_, rfl⟩ i (by simp [Fin.range_succAbove])
      have hwj : w.weights j = 0 :=
        (StdSimplex.mem_range_map_iff j.succAbove w).mp
          ⟨_, hcoordinates.symm⟩ j (by simp [Fin.range_succAbove])
      cases n with
      | zero =>
        -- Distinct endpoint vertices cannot represent the same probability weights.
        exfalso
        have hw := w.total_fin_two
        fin_cases i <;> fin_cases j <;> norm_num at hij
        change w.weights 0 = 0 at hwi
        change w.weights 1 = 0 at hwj
        rw [hwi, hwj, add_zero] at hw
        exact zero_ne_one hw
      | succ n =>
        let i' : Fin (n + 2) := i.castPred (Fin.ne_last_of_lt hij)
        let j' : Fin (n + 2) := j.pred (Fin.ne_zero_of_lt hij)
        let d : Fin (n + 1) → Fin (n + 3) := fun k ↦ j.succAbove (i'.succAbove k)
        let e := stdSimplex.finOrderIsoPairCompl i j hij
        have hrange (k : Fin (n + 3)) (hki : k ≠ i) (hkj : k ≠ j) : k ∈ range d := by
          let t : ({i, j}ᶜ : Finset (Fin (n + 3))) := ⟨k, by simp [hki, hkj]⟩
          exact ⟨e.symm t, congrArg Subtype.val (e.apply_symm_apply t)⟩
        obtain ⟨v, hv⟩ := (StdSimplex.mem_range_map_iff d w).mpr (by
          intro k hk
          by_cases hki : k = i
          · simpa only [hki] using hwi
          by_cases hkj : k = j
          · simpa only [hkj] using hwj
          exact (hk (hrange k hki hkj)).elim)
        let z : |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm v
        let t : |(Δ[n + 1] : SSet.{u})| := SSet.toTop.map (stdSimplex.δ i') z
        let t' : |(Δ[n + 1] : SSet.{u})| := SSet.toTop.map (stdSimplex.δ j') z
        have ht : SimplexCategory.toTopHomeo ⦋n + 1⦌ t = StdSimplex.map i'.succAbove v := by
          change SimplexCategory.toTopHomeo ⦋n + 1⦌
            (SSet.toTop.map (stdSimplex.δ i') ((SimplexCategory.toTopHomeo ⦋n⦌).symm v)) = _
          simp only [CosimplicialObject.δ, SimplexCategory.toTopHomeo_naturality_apply,
            SimplexCategory.coe_δ, Homeomorph.apply_symm_apply]
        have hbt : b = t := by
          apply (SimplexCategory.toTopHomeo ⦋n + 1⦌).injective
          apply hmap_injective (n + 1) j
          calc
            StdSimplex.map j.succAbove (SimplexCategory.toTopHomeo ⦋n + 1⦌ b) = w :=
              hcoordinates.symm
            _ = StdSimplex.map j.succAbove (SimplexCategory.toTopHomeo ⦋n + 1⦌ t) := by
              rw [ht, ← hv]
              exact StdSimplex.map_comp v i'.succAbove j.succAbove
        -- Both routes are the original double-face inclusion, with equality
        -- proved before realization and with the very same point z in its domain.
        have hcom : stdSimplex.δ i' ≫ boundary.ι j = stdSimplex.δ j' ≫ boundary.ι i := by
          apply (cancel_mono (boundary.{u} (n + 2)).ι).mp
          simp only [Category.assoc, boundary.ι_ι]
          exact (stdSimplex.facePairComplIso_hom_ι i j hij).symm.trans
            (stdSimplex.facePairComplIso_hom_ι' i j hij)
        have hF : F j t = F i t' := by
          have h := congrArg (fun q ↦ SSet.toTop.map q) hcom
          simp only [Functor.map_comp] at h
          exact congrArg (fun q ↦ q z) h
        have hat : a = t' := by
          apply hface_injective (n + 1) i
          exact hab.trans ((hinc j b).symm.trans
            ((congrArg inclusion ((congrArg (F j) hbt).trans hF)).trans (hinc i t')))
        exact (congrArg (F i) hat).trans (hF.symm.trans (congrArg (F j) hbt.symm))
    intro x y hxy
    obtain ⟨i, a, rfl⟩ := hcover x
    obtain ⟨j, b, rfl⟩ := hcover y
    have hab : D i a = D j b := (hinc i a).symm.trans (hxy.trans (hinc j b))
    obtain hij | rfl | hji := lt_trichotomy i j
    · exact hpair i j a b hij hab
    · exact congrArg (F i) (hface_injective n i hab)
    · exact (hpair j i b a hji hab.symm).symm

end SSet

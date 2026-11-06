/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CompactUnitaryApproximation
public import AtiyahSinger.Algebra.CompactRepresentationAveraging
public import AtiyahSinger.Topology.BundleComplement
public import AtiyahSinger.Topology.EquivariantVectorBundle
public import AtiyahSinger.Topology.EquivariantTrivialBundle
public import Mathlib.MeasureTheory.Function.L2Space

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Group.Measure

/-!
# Orbit embeddings into the regular Hilbert representation

Public module ID: M1789.

An ordinary fiberwise injection into a finite trivial bundle gives an
equivariant injection into its Haar L² orbit space. This uses full support of
Haar measure on the group and requires no measure on the base. The original
fiber maps, moving-base action and total-space topology are retained.

The Hilbert-space finite-vector theorem then supplies finite invariant
approximations of compact sets. Compactness of the normalized finite
presentation controls injectivity uniformly over the original base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Bundle

open scoped Matrix

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (μ : Measure G) [μ.IsMulLeftInvariant]

/-- The left regular unitary representation on the actual Haar L² space. -/
def leftRegularL2Representation : ContRepresentation ℂ G (Lp V 2 μ) :=
  .ofMonoidHom {
    toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (fun h : G ↦ g⁻¹ * h)
      (measurePreserving_mul_left μ g⁻¹)).toContinuousLinearMap
    map_one' := by
      apply ContinuousLinearMap.ext
      intro f
      change Lp.compMeasurePreserving (fun h : G ↦ (1 : G)⁻¹ * h) _ f = f
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving f
        (measurePreserving_mul_left μ (1 : G)⁻¹)] with h hh
      simpa only [Function.comp_apply, inv_one, one_mul] using hh
    map_mul' g h := by
      apply ContinuousLinearMap.ext
      intro f
      change Lp.compMeasurePreserving (fun k : G ↦ (g * h)⁻¹ * k) _ f =
        Lp.compMeasurePreserving (fun k : G ↦ g⁻¹ * k) _
          (Lp.compMeasurePreserving (fun k : G ↦ h⁻¹ * k) _ f)
      simpa only [Function.comp_def, mul_inv_rev, mul_assoc] using
        Lp.compMeasurePreserving_comp_apply f (measurePreserving_mul_left μ h⁻¹)
          (measurePreserving_mul_left μ g⁻¹) }

/-- The actual left regular action preserves the Hilbert inner product. -/
theorem leftRegularL2Representation_inner (g : G) (x y : Lp V 2 μ) :
    inner ℂ (leftRegularL2Representation μ g x) (leftRegularL2Representation μ g y) =
      inner ℂ x y :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun h : G ↦ g⁻¹ * h)
    (measurePreserving_mul_left μ g⁻¹)).inner_map_map x y

/-- Haar regularity gives joint continuity of the actual L² regular action. -/
theorem continuous_leftRegularL2Representation [T2Space G] [LocallyCompactSpace G]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] :
    Continuous (fun p : G × Lp V 2 μ ↦ leftRegularL2Representation μ p.1 p.2) := by
  let shift : C(G, C(G, G)) :=
    (⟨fun p : G × G ↦ p.1⁻¹ * p.2, continuous_fst.inv.mul continuous_snd⟩ :
      C(G × G, G)).curry
  change Continuous (fun p : G × Lp V 2 μ ↦
    Lp.compMeasurePreserving (shift p.1) (measurePreserving_mul_left μ p.1⁻¹) p.2)
  exact continuous_snd.compMeasurePreservingLp (shift.continuous.comp continuous_fst)
    (fun p ↦ measurePreserving_mul_left μ p.1⁻¹) (by simp)

namespace ComplexBundle

variable {X : Type*} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [CompactSpace G] [T2Space G]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

attribute [local instance] trivialTopology IdempotentMatrix.fiberTotalSpaceTopology
  IdempotentMatrix.isFiniteRank_fiber

omit [T2Space G] in
/-- Orbitizing an ordinary finite bundle injection gives a continuous
equivariant fiberwise injection into the same regular L² representation. -/
theorem EquivariantStructure.exists_hilbert_embedding (σ : EquivariantStructure G E)
    (n : ℕ) (f : Hom E (Bundle.Trivial X (Fin n → ℂ)))
    (hf : ∀ x, Function.Injective (f.linearMap x)) :
    ∃ J : ∀ x, E x →ₗ[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 μ,
      Continuous (fun z : TotalSpace Unit E ↦ J z.proj z.snd) ∧
      (∀ x, Function.Injective (J x)) ∧
      ∀ (g : G) (x : X) (v : E x),
        J (g • x) (σ.linearMap g x v) = leftRegularL2Representation μ g (J x v) := by
  classical
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let e : (Fin n → ℂ) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℂ).symm
  let F : TotalSpace Unit E → EuclideanSpace ℂ (Fin n) :=
    fun z ↦ e (f.linearMap z.proj z.snd)
  have hF : Continuous F :=
    e.continuous.comp (continuous_induced_rng.mp f.continuous_total).snd
  let Φ : C(TotalSpace Unit E × G, EuclideanSpace ℂ (Fin n)) :=
    ⟨fun p ↦ F (p.2⁻¹ • p.1),
      hF.comp (σ.continuous_action.comp (continuous_snd.inv.prodMk continuous_fst))⟩
  let A (x : X) : E x →ₗ[ℂ] C(G, EuclideanSpace ℂ (Fin n)) := {
    toFun v := Φ.curry ⟨x, v⟩
    map_add' u v := by
      apply ContinuousMap.ext
      intro g
      exact (e.toLinearMap.comp
        ((f.linearMap (g⁻¹ • x)).comp (σ.linearMap g⁻¹ x))).map_add u v
    map_smul' c v := by
      apply ContinuousMap.ext
      intro g
      exact (e.toLinearMap.comp
        ((f.linearMap (g⁻¹ • x)).comp (σ.linearMap g⁻¹ x))).map_smul c v }
  let J (x : X) : E x →ₗ[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 μ :=
    (ContinuousMap.toLp 2 μ ℂ).toLinearMap.comp (A x)
  refine ⟨J, ?_, ?_, ?_⟩
  · -- Joint continuity comes from currying on the compact group parameter,
    -- followed by the bounded inclusion of continuous functions into L².
    exact (ContinuousMap.toLp 2 μ ℂ).continuous.comp Φ.curry.continuous
  · -- Haar full support upgrades equality in L² to equality everywhere for
    -- these continuous orbit functions. Evaluation at 1 recovers f itself.
    intro x u v huv
    have hA : A x u = A x v := (ContinuousMap.toLp_injective μ) huv
    have h1 := congrArg (fun k : C(G, EuclideanSpace ℂ (Fin n)) ↦ k 1) hA
    change F ((1 : G)⁻¹ • (⟨x, u⟩ : TotalSpace Unit E)) =
      F ((1 : G)⁻¹ • (⟨x, v⟩ : TotalSpace Unit E)) at h1
    simp only [inv_one, one_smul] at h1
    exact hf x (e.injective h1)
  · -- Translation of the orbit function matches the original total-space
    -- multiplication law, including its moving base point.
    intro g x v
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp μ (𝕜 := ℂ) (p := 2)
        (A (g • x) (σ.linearMap g x v)),
      Lp.coeFn_compMeasurePreserving (J x v) (measurePreserving_mul_left μ g⁻¹),
      (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae
        (ContinuousMap.coeFn_toLp μ (𝕜 := ℂ) (p := 2) (A x v))] with h hleft hright hcomp
    change ((J (g • x) (σ.linearMap g x v)) : G → EuclideanSpace ℂ (Fin n)) h = _
      at hleft
    change ((leftRegularL2Representation μ g (J x v)) :
      G → EuclideanSpace ℂ (Fin n)) h = _ at hright
    change ((J x v) : G → EuclideanSpace ℂ (Fin n)) (g⁻¹ * h) = _ at hcomp
    rw [hleft, hright, Function.comp_apply, hcomp]
    change F (h⁻¹ • (g • (⟨x, v⟩ : TotalSpace Unit E))) =
      F ((g⁻¹ * h)⁻¹ • (⟨x, v⟩ : TotalSpace Unit E))
    rw [mul_inv_rev, inv_inv, mul_smul]

variable [CompactSpace X] [T2Space X] [IsFiniteRank E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [MeasurableSpace G] [BorelSpace G] in
/-- A continuous equivariant Hilbert embedding over a compact base admits
an injective finite-dimensional invariant projection, in actual finite coordinates. -/
theorem EquivariantStructure.exists_finiteRepresentation_embedding_of_hilbert
    (σ : EquivariantStructure G E) (ρ : ContRepresentation ℂ G H)
    (hρ : Continuous (fun p : G × H ↦ ρ p.1 p.2))
    (hunitary : ∀ (g : G) (u v : H), inner ℂ (ρ g u) (ρ g v) = inner ℂ u v)
    (J : ∀ x, E x →ₗ[ℂ] H)
    (hJ : Continuous (fun z : TotalSpace Unit E ↦ J z.proj z.snd))
    (hJinj : ∀ x, Function.Injective (J x))
    (hJeq : ∀ (g : G) (x : X) (v : E x), J (g • x) (σ.linearMap g x v) = ρ g (J x v)) :
    ∃ κ : FiniteContinuousRepresentation G,
      ∃ q : Hom E (Bundle.Trivial X (Fin κ.dimension → ℂ)),
        (∀ x, Function.Injective (q.linearMap x)) ∧
        q.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation κ) := by
  classical
  -- Use the same finite presentation throughout. Its unit vectors form a
  -- closed subset of the compact product of X and one finite unit sphere.
  let p := idempotentPresentation (E := E)
  let e : Iso E (fun x ↦ p.fiber x) := presentationIso
  let B (x : X) : Matrix (Fin p.size) (Fin p.size) ℂ :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
  have hB : Continuous B :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ (p.matrix i j).continuous
  have hfix (x : X) (w : p.fiber x) : B x *ᵥ w.val = w.val := by
    obtain ⟨v, hv⟩ : ∃ v, B x *ᵥ v = w.val := w.property
    rw [← hv, Matrix.mulVec_mulVec]
    exact congrArg (fun A ↦ A *ᵥ v)
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  let S : Set (X × (Fin p.size → ℂ)) :=
    {a | B a.1 *ᵥ a.2 = a.2 ∧ ‖a.2‖ = 1}
  have hS : IsCompact S := by
    apply (isCompact_univ.prod (isCompact_sphere (0 : Fin p.size → ℂ) 1)).of_isClosed_subset
    · exact (isClosed_eq ((hB.comp continuous_fst).matrix_mulVec continuous_snd)
        continuous_snd).inter (isClosed_eq continuous_snd.norm continuous_const)
    · intro a ha
      exact ⟨Set.mem_univ _, by simpa [Metric.mem_sphere, dist_zero_right] using ha.2⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let D : S → TotalSpace Unit (fun x ↦ p.fiber x) := fun a ↦
    ⟨a.val.1, ⟨a.val.2, ⟨a.val.2, a.property.1⟩⟩⟩
  have hD : Continuous D := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val
  let Φ : S → H := fun a ↦ J a.val.1 ((e.linearEquiv a.val.1).symm (D a).snd)
  have hΦ : Continuous Φ := hJ.comp (e.continuous_symm.comp hD)
  have hcompact : IsCompact (Set.range Φ) := isCompact_range hΦ
  have hzero : (0 : H) ∉ Set.range Φ := by
    rintro ⟨a, ha⟩
    have hv : (e.linearEquiv a.val.1).symm (D a).snd = 0 :=
      hJinj a.val.1 (ha.trans (map_zero (J a.val.1)).symm)
    have hcoord : a.val.2 = 0 := by
      have := congrArg (fun v ↦ (e.linearEquiv a.val.1 v).val) hv
      simpa [D] using this
    have := a.property.2
    simp [hcoord] at this
  -- Compactness separates the entire normalized image from zero, giving a
  -- single positive margin over all fibers, including locally varying ranks.
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hcompact.isClosed.isOpen_compl.mem_nhds hzero)
  have hbound (a : S) : ε ≤ ‖Φ a‖ := by
    by_contra h
    have hmem : Φ a ∈ Metric.ball (0 : H) ε := by
      simpa [Metric.mem_ball, dist_zero_right] using lt_of_not_ge h
    exact hball hmem (Set.mem_range_self a)
  obtain ⟨W, hW, hinv, happ⟩ :=
    exists_finiteDimensional_invariant_approximation ρ hρ hunitary
      (Set.range Φ) hcompact hε
  let : FiniteDimensional ℂ W := hW
  let P : H →L[ℂ] W := W.orthogonalProjectionOnto
  have hPcomm (g : G) (v : H) :
      (P (ρ g v) : H) = ρ g (P v) := by
    have heq : W.map (ρ g).toLinearMap = W := by
      apply le_antisymm
      · rintro _ ⟨u, hu, rfl⟩
        exact hinv g u hu
      · intro u hu
        refine ⟨ρ g⁻¹ u, hinv g⁻¹ u hu, ?_⟩
        simp only [ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp,
          ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
    let L : H →ₗᵢ[ℂ] H := (ρ g).toLinearMap.isometryOfInner (hunitary g)
    have hmap := L.map_starProjection W v
    change W.starProjection (L v) = L (W.starProjection v)
    simpa only [show W.map L.toLinearMap = W from heq] using hmap.symm
  let τ : ContRepresentation ℂ G W := continuousSubmoduleRepresentation ρ W hinv
  have hτ : Continuous (fun a : G × W ↦ τ a.1 a.2) :=
    (hρ.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  let c : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  let κ := FiniteContinuousRepresentation.ofEquiv τ hτ c
  let q : Hom E (Bundle.Trivial X (Fin κ.dimension → ℂ)) := {
    linearMap x := c.toLinearMap.comp (P.toLinearMap.comp (J x))
    continuous_total := continuous_induced_rng.mpr
      ((continuous_proj (E := E)).prodMk (c.continuous.comp (P.continuous.comp hJ))) }
  refine ⟨κ, q, ?_, ?_⟩
  · -- If the projected map killed a vector, normalize its original finite
    -- coordinates. The projection error would then be at least the uniform margin.
    intro x
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    by_contra hv0
    let z := (e.linearEquiv x v).val
    have hz : z ≠ 0 := by
      intro hz
      apply hv0
      apply (e.linearEquiv x).injective
      exact Subtype.ext (hz.trans (by simp))
    let a : ℂ := (‖z‖ : ℂ)⁻¹
    let w := a • v
    have hn : ‖(e.linearEquiv x w).val‖ = 1 := by
      change ‖(e.linearEquiv x (a • v)).val‖ = 1
      rw [map_smul, Submodule.coe_smul]
      change ‖a • z‖ = 1
      simp [a, norm_smul, Complex.norm_real, norm_ne_zero_iff.mpr hz]
    let s : S := ⟨(x, (e.linearEquiv x w).val), hfix x (e.linearEquiv x w), hn⟩
    have hΦs : Φ s = J x w := by
      change J x ((e.linearEquiv x).symm _) = J x w
      exact congrArg (J x) ((e.linearEquiv x).symm_apply_apply w)
    have hPv : P (J x v) = 0 := by
      apply c.injective
      exact (show q.linearMap x v = 0 from hv).trans c.map_zero.symm
    have hPw : P (J x w) = 0 := by
      change P (J x (a • v)) = 0
      rw [map_smul, map_smul, hPv, smul_zero]
    obtain ⟨y, hy, hxy⟩ := happ (Φ s) (Set.mem_range_self s)
    have hsmall : dist (Φ s) (W.starProjection (Φ s)) < ε := by
      rw [W.dist_starProjection_eq_infDist]
      exact (Metric.infDist_le_dist_of_mem hy).trans_lt hxy
    have hPs : W.starProjection (Φ s) = 0 := by
      rw [hΦs]
      exact congrArg Subtype.val hPw
    rw [hPs, dist_zero_right] at hsmall
    exact (not_lt_of_ge (hbound s)) hsmall
  · -- Coordinates retain the restricted original representation, and the
    -- orthogonal projection intertwines that same unitary action.
    intro g x v
    change c (P (J (g • x) (σ.linearMap g x v))) =
      c (τ g (c.symm (c (P (J x v)))))
    rw [c.symm_apply_apply, hJeq]
    congr 1
    apply Subtype.ext
    exact hPcomm g (J x v)

omit [MeasurableSpace G] [BorelSpace G] in
/-- An original compact equivariant bundle embeds in a finite representation bundle. -/
theorem EquivariantStructure.exists_finiteRepresentation_embedding
    (σ : EquivariantStructure G E) :
    ∃ κ : FiniteContinuousRepresentation G,
      ∃ q : Hom E (Bundle.Trivial X (Fin κ.dimension → ℂ)),
        (∀ x, Function.Injective (q.linearMap x)) ∧
        q.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation κ) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := Measure.haar
  -- The orbitized ordinary injection lands in the genuine regular Hilbert
  -- representation. Finite invariant approximation preserves it uniformly.
  obtain ⟨n, f, hf⟩ := exists_fiberwise_injective_trivial_map (E := E)
  obtain ⟨J, hJ, hJinj, hJeq⟩ := σ.exists_hilbert_embedding ν n f hf
  exact σ.exists_finiteRepresentation_embedding_of_hilbert (leftRegularL2Representation ν)
    (continuous_leftRegularL2Representation ν) (leftRegularL2Representation_inner ν)
    J hJ hJinj hJeq

end ComplexBundle

end AtiyahSinger

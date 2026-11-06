/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.HermitianFlagBundle

/-!
# Tautological lines and the actual full-flag splitting

Public module ID: M1884.

The i-th tautological line is the range of the i-th projection in the
original fiber. Its topology is induced from the original pulled-back bundle.
Their finite sum carries the same-base product topology, including the base
coordinate when the index set is empty. The displayed splitting adds the
original fiber vectors; its inverse applies the specified projections.

Source: Hatcher, Vector Bundles and K-Theory, Section 1.2, p.20 (5), and
Section 3.1, Proposition 3.3, pp.80--81. This is the continuous bundle part of
SG III.11.1, with a given positive Hermitian metric. Neither cohomological
injectivity nor existence of a splitting is assumed as an input.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable (r : ℕ) {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

/-- The i-th tautological line, literally a subspace of the original fiber. -/
abbrev HermitianFlagLine (i : Fin r) (p : HermitianFlagBundle r E h) : Type _ :=
  LinearMap.range (p.2.val i).toLinearMap

/-- The finite sum of the actual tautological lines on the same flag base. -/
abbrev HermitianFlagSum (p : HermitianFlagBundle r E h) : Type _ :=
  ∀ i : Fin r, HermitianFlagLine r E h i p

variable [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

attribute [local instance] hermitianFlagTopology isFiniteRank_pullback sectionModule sumTopology
  InnerProductSpace.Core.toPreInner'

/-- Each tautological line has the subbundle topology of the original pullback. -/
@[reducible]
def hermitianFlagLineTopology (i : Fin r) :
    TopologicalSpace (TotalSpace Unit (HermitianFlagLine r E h i)) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (HermitianFlagLine r E h i) ↦
      (⟨z.proj, z.snd.val⟩ :
        TotalSpace Unit ((hermitianFlagProjection r E h : HermitianFlagBundle r E h → X) *ᵖ E)))
    inferInstance

attribute [local instance] hermitianFlagLineTopology

/-- The finite same-base product topology, retaining the base also for an empty sum. -/
@[reducible]
def hermitianFlagSumTopology :
    TopologicalSpace (TotalSpace Unit (HermitianFlagSum r E h)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (HermitianFlagSum r E h) ↦
      (z.proj, fun i : Fin r ↦
        (⟨z.proj, z.snd i⟩ : TotalSpace Unit (HermitianFlagLine r E h i))))
    inferInstance

attribute [local instance] hermitianFlagSumTopology

/-- The actual tautological ranges form continuous finite-rank line bundles. -/
theorem isFiniteRank_hermitianFlagLine (i : Fin r) :
    IsFiniteRank (HermitianFlagLine r E h i) := by
  set_option backward.isDefEq.respectTransparency.types false in
    /- Stage 1: near a flag p, choose a nonzero vector in its i-th projection range.
    Extend it using an original bundle chart to a local section near its base.
    Apply the varying i-th projection. Native Hom-bundle evaluation is continuous,
    and the resulting section has its original nonzero value at p. Shrink to the
    open set where it is nonzero. Rank one makes it a basis of each nearby range.
    Stage 2: scalar multiplication by this section gives the linear chart inverse.
    The forward coefficient is h(section,vector)/h(section,section), with the
    first slot conjugate-linear and the second slot linear. The denominator is
    positive on this neighborhood. Joint metric continuity proves continuity of
    this inverse coefficient for the original induced line topology. These
    rank-one linear charts cover the flag base and establish IsFiniteRank.
    This construction is local on the original flag bundle; no replacement
    line carrier, chosen global section or topology is introduced. -/
    classical
    let V := EuclideanSpace ℂ (Fin r)
    let := modelTopology V E
    let := isFiniteRank_model V E
    let Q := HermitianFlagBundle r E h
    let p : C(Q, X) := hermitianFlagProjection r E h
    let L := HermitianFlagLine r E h i
    let F := (p : Q → X) *ᵖ E
    have hbase : Continuous (fun q : Q ↦ q.1) := p.continuous
    have hc : Continuous (fun q : Q ↦
        (q.1, fun j : Fin r ↦
          (⟨q.1, q.2.val j⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)))) :=
      continuous_induced_dom
    have hP : Continuous (fun q : Q ↦
        (⟨q.1, q.2.val i⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x))) :=
      (continuous_apply i).comp hc.snd
    have hdouble : Topology.IsInducing (fun z : TotalSpace Unit (E ×ᵇ E) ↦
        ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
          (⟨z.proj, z.snd.2⟩ : TotalSpace Unit E))) := ⟨rfl⟩
    -- Project an original local frame vector to obtain a nonzero local range section.
    constructor
    intro q₀
    let : Nontrivial (L q₀) := Module.nontrivial_of_finrank_pos (by
      rw [q₀.2.property.2.1 i]
      exact zero_lt_one)
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : L q₀)
    let e := trivializationAt V E q₀.1
    have he : q₀.1 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt V E q₀.1
    let w := (e ⟨q₀.1, v₀.val⟩).2
    let s (q : Q) : L q := ⟨q.2.val i (e.symm q.1 w), ⟨e.symm q.1 w, rfl⟩⟩
    let U₀ : Set Q := p ⁻¹' e.baseSet
    have hU₀ : IsOpen U₀ := e.open_baseSet.preimage hbase
    have hs₀ : (s q₀).val = v₀.val := by
      change q₀.2.val i (e.symm q₀.1 (e ⟨q₀.1, v₀.val⟩).2) = v₀.val
      rw [e.symm_apply_apply_mk he]
      obtain ⟨v, hv⟩ := v₀.property
      rw [← hv]
      exact DFunLike.congr_fun (q₀.2.property.1 i) v
    have hs : ContinuousOn (fun q : Q ↦ (⟨q.1, (s q).val⟩ : TotalSpace Unit E)) U₀ := by
      have hframe : ContinuousOn (fun q : Q ↦ (⟨q.1, e.symm q.1 w⟩ : TotalSpace V E)) U₀ :=
        e.continuousOn_symm.comp (hbase.prodMk continuous_const).continuousOn
          (fun q hq ↦ ⟨hq, Set.mem_univ _⟩)
      exact (continuous_unitTotalEquiv_symm V E).comp_continuousOn
        (hP.continuousOn.clm_bundle_apply hframe)
    -- Shrink only where this same section has nonvanishing Hermitian length.
    let a (q : Q) : ℂ := (h.toCore q.1).inner (s q).val (s q).val
    have ha : ContinuousOn a U₀ := by
      have hpair : ContinuousOn (fun q : Q ↦
          (⟨q.1, (s q).val, (s q).val⟩ : TotalSpace Unit (E ×ᵇ E))) U₀ :=
        hdouble.continuousOn_iff.mpr (hs.prodMk hs)
      exact h.continuous_pairing.comp_continuousOn hpair
    let U : Set Q := U₀ ∩ a ⁻¹' ({0}ᶜ : Set ℂ)
    have hU : IsOpen U := ha.isOpen_inter_preimage hU₀ isClosed_singleton.isOpen_compl
    have hq₀ : q₀ ∈ U := by
      refine ⟨he, ?_⟩
      change a q₀ ≠ 0
      intro hz
      apply hv₀
      apply Subtype.ext
      exact hs₀.symm.trans ((h.toCore q₀.1).definite _ hz)
    have hnonzero (q : Q) (hq : q ∈ U) : s q ≠ 0 := by
      intro hz
      apply hq.2
      change a q = 0
      have hval : (s q).val = 0 := congrArg Subtype.val hz
      let := h.toCore q.1
      change inner ℂ (s q).val (s q).val = 0
      rw [hval]
      exact InnerProductSpace.Core.inner_zero_right _
    -- The metric coefficient is linear in the original vector and inverts scalar multiplication.
    let coeff (q : Q) (v : L q) : ℂ := (h.toCore q.1).inner (s q).val v.val / a q
    have hcoeff_smul (q : Q) (c : ℂ) (v : L q) :
        coeff q (c • v) = c * coeff q v := by
      let := h.toCore q.1
      change inner ℂ (s q).val (c • v.val) / a q = c * (inner ℂ (s q).val v.val / a q)
      rw [InnerProductSpace.Core.inner_smul_right, mul_div_assoc]
    have hcoeff_self (q : Q) (hq : q ∈ U) : coeff q (s q) = 1 := div_self hq.2
    have hleft (q : Q) (hq : q ∈ U) (v : L q) : coeff q v • s q = v := by
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (q.2.property.2.1 i) (hnonzero q hq) v
      rw [← hc, hcoeff_smul, hcoeff_self q hq, mul_one]
    have hright (q : Q) (hq : q ∈ U) (c : ℂ) : coeff q (c • s q) = c := by
      rw [hcoeff_smul, hcoeff_self q hq, mul_one]
    -- The line topology is the original pulled-back subspace topology.
    have hinc : Continuous (fun z : TotalSpace Unit L ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace Unit F)) := continuous_induced_dom
    have hb : Continuous (fun z : TotalSpace Unit L ↦ z.proj) :=
      (continuous_proj (E := F)).comp hinc
    have hvec : Continuous (fun z : TotalSpace Unit L ↦
        (⟨z.proj.1, z.snd.val⟩ : TotalSpace Unit E)) :=
      (Pullback.continuous_lift Unit E p).comp hinc
    have hcoeff : ContinuousOn (fun z : TotalSpace Unit L ↦ coeff z.proj z.snd)
        ((fun z : TotalSpace Unit L ↦ z.proj) ⁻¹' U) := by
      have hsection : ContinuousOn (fun z : TotalSpace Unit L ↦
          (⟨z.proj.1, (s z.proj).val⟩ : TotalSpace Unit E))
          ((fun z : TotalSpace Unit L ↦ z.proj) ⁻¹' U) :=
        hs.comp hb.continuousOn (fun z hz ↦ hz.1)
      have hpair : ContinuousOn (fun z : TotalSpace Unit L ↦
          (⟨z.proj.1, (s z.proj).val, z.snd.val⟩ : TotalSpace Unit (E ×ᵇ E)))
          ((fun z : TotalSpace Unit L ↦ z.proj) ⁻¹' U) :=
        hdouble.continuousOn_iff.mpr (hsection.prodMk hvec.continuousOn)
      exact (h.continuous_pairing.comp_continuousOn hpair).div
        (ha.comp hb.continuousOn (fun z hz ↦ hz.1)) (fun z hz ↦ hz.2)
    -- Check the inverse in the induced topology, using sections on the actual chart domain.
    have hfront : ContinuousOn (fun z : Q × (Fin 1 → ℂ) ↦
        (⟨z.1, z.2 0 • s z.1⟩ : TotalSpace Unit L)) (U ×ˢ Set.univ) := by
      rw [continuousOn_iff_continuous_domRestrict]
      let D := ↥(U ×ˢ (Set.univ : Set (Fin 1 → ℂ)))
      let b : C(D, X) := ⟨fun z ↦ z.val.1.1,
        hbase.comp (continuous_fst.comp continuous_subtype_val)⟩
      have hsec : Continuous (fun z : D ↦
          (⟨z, (s z.val.1).val⟩ : TotalSpace Unit ((b : D → X) *ᵖ E))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E b).continuous_iff]
        exact continuous_id.prodMk (hs.comp_continuous
          (continuous_fst.comp continuous_subtype_val) (fun z ↦ z.property.1.1))
      let c : C(D, ℂ) := ⟨fun z ↦ z.val.2 0,
        (continuous_apply 0).comp (continuous_snd.comp continuous_subtype_val)⟩
      have hsmul := continuous_smul_section ((b : D → X) *ᵖ E) c
        (fun z ↦ (s z.val.1).val) hsec
      apply continuous_induced_rng.mpr
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
      exact (continuous_fst.comp continuous_subtype_val).prodMk
        ((Pullback.continuous_lift Unit E b).comp hsmul)
    -- Assemble the original range-line chart with one standard complex coordinate.
    let t : Trivialization (Fin 1 → ℂ) (π Unit L) :=
      { toFun := fun z ↦ (z.proj, fun _ ↦ coeff z.proj z.snd)
        invFun := fun z ↦ ⟨z.1, z.2 0 • s z.1⟩
        source := (π Unit L) ⁻¹' U
        target := U ×ˢ Set.univ
        baseSet := U
        open_source := hU.preimage hb
        open_target := hU.prod isOpen_univ
        open_baseSet := hU
        map_source' := fun z hz ↦ ⟨hz, Set.mem_univ _⟩
        map_target' := fun z hz ↦ hz.1
        left_inv' := by
          intro z hz
          exact congrArg (fun v : L z.proj ↦ (⟨z.proj, v⟩ : TotalSpace Unit L))
            (hleft z.proj hz z.snd)
        right_inv' := by
          intro z hz
          apply Prod.ext
          · rfl
          · funext j
            have hj : j = 0 := Subsingleton.elim _ _
            subst j
            exact hright z.1 hz.1 (z.2 0)
        continuousOn_toFun := hb.continuousOn.prodMk (continuousOn_pi.mpr fun _ ↦ hcoeff)
        continuousOn_invFun := hfront
        source_eq := rfl
        target_eq := rfl
        proj_toFun := fun _ _ ↦ rfl }
    refine ⟨1, t, hq₀, ?_⟩
    intro q hq
    constructor
    · intro v w
      funext j
      let := h.toCore q.1
      change inner ℂ (s q).val (v.val + w.val) / a q =
        inner ℂ (s q).val v.val / a q + inner ℂ (s q).val w.val / a q
      rw [InnerProductSpace.Core.inner_add_right, add_div]
    · intro c v
      funext j
      exact hcoeff_smul q c v

set_option backward.isDefEq.respectTransparency.types false in
/-- The sum and component formulas are inverse and continuous on the original total spaces. -/
theorem hermitianFlagSplitting_properties :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    (∀ (p : HermitianFlagBundle r E h) (s : HermitianFlagSum r E h p) (i : Fin r),
      p.2.val i (∑ j, (s j).val) = (s i).val) ∧
    (∀ (p : HermitianFlagBundle r E h) (v : E p.1), (∑ i, p.2.val i v) = v) ∧
    Continuous (fun z : TotalSpace Unit (HermitianFlagSum r E h) ↦
      (⟨z.proj, ∑ i, (z.snd i).val⟩ :
        TotalSpace Unit ((hermitianFlagProjection r E h : HermitianFlagBundle r E h → X) *ᵖ E))) ∧
    Continuous
      (fun z : TotalSpace Unit
          ((hermitianFlagProjection r E h : HermitianFlagBundle r E h → X) *ᵖ E) ↦
        (⟨z.proj, fun i ↦ ⟨z.proj.2.val i z.snd, ⟨z.snd, rfl⟩⟩⟩ :
          TotalSpace Unit (HermitianFlagSum r E h))) := by
  /- Stage 1: apply the i-th projection to the finite sum of line vectors.
  Idempotence makes it identity on its own range. Pairwise annihilation kills
  every other range. This recovers exactly the original i-th component.
  Conversely, evaluation of the sum-of-projections identity at v gives v.
  Stage 2: addition of original fiber vectors is jointly continuous in native
  bundle charts and hence in the retyped original pullback. The line topology
  makes each inclusion into that pullback continuous. The same-base sum
  topology therefore makes the actual finite sum map continuous.
  Stage 3: projection evaluation is continuous in the original Hom bundle.
  Its image lies in the corresponding range by construction, so the induced
  line topology gives continuity of every inverse component. The base
  coordinate is unchanged, giving continuity into the finite same-base sum.
  Stage 4: the argument also treats r=0. The original fiber is zero-dimensional,
  and both maps are the unique fiber maps; the retained base coordinates keep
  the total topologies correct. No separate trivialization, splitting witness,
  positive-rank assumption or equality of merely isomorphic bundles is used. -/
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let := modelTopology V E
  let := isFiniteRank_model V E
  let p : C(HermitianFlagBundle r E h, X) := hermitianFlagProjection r E h
  let F := (p : HermitianFlagBundle r E h → X) *ᵖ E
  -- Idempotence and pairwise annihilation recover precisely the original component vectors.
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q s i
    rw [map_sum, Finset.sum_eq_single i]
    · obtain ⟨v, hv⟩ := (s i).property
      rw [← hv]
      exact DFunLike.congr_fun (q.2.property.1 i) v
    · intro j _ hji
      obtain ⟨v, hv⟩ := (s j).property
      rw [← hv]
      exact DFunLike.congr_fun (q.2.property.2.2.1 i j hji.symm) v
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · intro q v
    have heq := DFunLike.congr_fun q.2.property.2.2.2.1 v
    simpa only [sum_apply, ContinuousLinearMap.id_apply] using heq
  · -- Regard the component inclusions as continuous sections over the sum's total space.
    let D := TotalSpace Unit (HermitianFlagSum r E h)
    have hc : Continuous (fun z : D ↦
        (z.proj, fun i : Fin r ↦
          (⟨z.proj, z.snd i⟩ : TotalSpace Unit (HermitianFlagLine r E h i)))) :=
      continuous_induced_dom
    let b : C(D, HermitianFlagBundle r E h) := ⟨fun z ↦ z.proj, hc.fst⟩
    have hi (i : Fin r) : Continuous (fun z : D ↦
        (⟨z.proj, (z.snd i).val⟩ : TotalSpace Unit F)) :=
      continuous_induced_dom.comp ((continuous_apply i).comp hc.snd)
    let s (i : Fin r) : continuousSections ((b : D → HermitianFlagBundle r E h) *ᵖ F) :=
      ⟨fun z ↦ (z.snd i).val, by
        change Continuous (fun z : D ↦
          (⟨z, (z.snd i).val⟩ : TotalSpace Unit ((b : D → HermitianFlagBundle r E h) *ᵖ F)))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F b).continuous_iff]
        exact continuous_id.prodMk (hi i)⟩
    have hs := (Pullback.continuous_lift Unit F b).comp (∑ i : Fin r, s i).property
    apply hs.congr
    intro z
    apply congrArg (fun v : F z.proj ↦ (⟨z.proj, v⟩ : TotalSpace Unit F))
    change (∑ i : Fin r, s i).val z = ∑ i, (z.snd i).val
    simp only [Submodule.coe_sum, Finset.sum_apply]
    rfl
  · -- Apply the actual native Hom-bundle projections to the unchanged original vector.
    let D := TotalSpace Unit F
    have hb : Continuous (fun z : D ↦ z.proj) := continuous_proj
    have hc : Continuous (fun q : HermitianFlagBundle r E h ↦
        (q.1, fun i : Fin r ↦
          (⟨q.1, q.2.val i⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)))) :=
      continuous_induced_dom
    have hv : Continuous (fun z : D ↦ (⟨z.proj.1, z.snd⟩ : TotalSpace V E)) :=
      (continuous_unitTotalEquiv V E).comp (Pullback.continuous_lift Unit E p)
    apply continuous_induced_rng.mpr
    refine hb.prodMk (continuous_pi fun i ↦ ?_)
    apply continuous_induced_rng.mpr
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    refine hb.prodMk ?_
    have hP : Continuous (fun z : D ↦
        (⟨z.proj.1, z.proj.2.val i⟩ :
          TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x))) :=
      ((continuous_apply i).comp hc.snd).comp hb
    exact (continuous_unitTotalEquiv_symm V E).comp (hP.clm_bundle_apply hv)

/-- The actual tautological splitting of the original pullback, by summing its line vectors. -/
def hermitianFlagSplitting :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    Iso (HermitianFlagSum r E h)
      ((hermitianFlagProjection r E h : HermitianFlagBundle r E h → X) *ᵖ E) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  { linearEquiv := fun p ↦
      { toFun := fun s ↦ ∑ i, (s i).val
        invFun := fun v i ↦ ⟨p.2.val i v, ⟨v, rfl⟩⟩
        left_inv := by
          -- Recover every original line component using its specified projection.
          intro s
          funext i
          apply Subtype.ext
          exact (hermitianFlagSplitting_properties r E h).1 p s i
        right_inv := (hermitianFlagSplitting_properties r E h).2.1 p
        map_add' := by
          intro s t
          change (∑ i, ((s i).val + (t i).val)) =
            (∑ i, (s i).val) + (∑ i, (t i).val)
          exact Finset.sum_add_distrib
        map_smul' := by
          intro c s
          change (∑ i, c • (s i).val) = c • (∑ i, (s i).val)
          exact Finset.smul_sum.symm }
    continuous_total := (hermitianFlagSplitting_properties r E h).2.2.1
    continuous_symm := (hermitianFlagSplitting_properties r E h).2.2.2 }

/-- The displayed finite sum is a continuous finite-rank bundle over the same flag space. -/
theorem isFiniteRank_hermitianFlagSum : IsFiniteRank (HermitianFlagSum r E h) := by
  /- The original modeled bundle has local rank r. Pull those local linear
  charts back along the original continuous flag projection. Transport them
  through the explicit inverse of hermitianFlagSplitting, which preserves all
  original vectors and uses precisely the induced topologies above. Thus the
  finite sum has local finite rank without choosing a different splitting. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_pullback (E := E) (hermitianFlagProjection r E h)
  exact (hermitianFlagSplitting r E h).symm.isFiniteRank

end AtiyahSinger.ComplexBundle

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexLineChern
public import AtiyahSinger.Topology.HermitianFlagSplitting

/-!
# The Hermitian projective bundle and its tautological line

Public module ID: M1890.

The projective fiber consists of actual rank-one orthogonal projections in the
original vector space. Its total topology is induced by the original native
endomorphism bundle. The tautological line is the actual range, with the subbundle
topology induced from the original pullback. Every flag line therefore determines
an actual map to this projective bundle over the original base.

The local range-line argument extends the construction in `HermitianFlagSplitting`.
It uses an original local frame and the specified continuous Hermitian metric;
no global line section or separation condition on the base is needed.

Source: Hatcher, Vector Bundles and K-Theory, Sections 1.1 and 3.1, for the
projective bundle and tautological line. Cohomological Leray--Hirsch and its
normalization are separate mathematical obligations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

/-- The projective space of actual rank-one orthogonal projections for the given form. -/
abbrev HermitianProjectiveSpace (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] (h : InnerProductSpace.Core ℂ V) : Type _ :=
  {P : V →L[ℂ] V // P.comp P = P ∧
    Module.finrank ℂ (LinearMap.range P.toLinearMap) = 1 ∧
    ∀ u v, h.inner (P u) v = h.inner u (P v)}

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

/-- Projective lines in the original fibers, represented by their orthogonal projections. -/
def HermitianProjectiveBundle : Type _ :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  (x : X) × HermitianProjectiveSpace (E x) (h.toCore x)

/-- The tautological line is literally the range of the specified original projection. -/
abbrev HermitianProjectiveLine (p : HermitianProjectiveBundle r E h) : Type _ :=
  LinearMap.range p.2.val.toLinearMap

variable [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- The projective topology induced by the original native endomorphism bundle. -/
@[reducible]
def hermitianProjectiveTopology : TopologicalSpace (HermitianProjectiveBundle r E h) :=
  TopologicalSpace.induced
    (fun p : HermitianProjectiveBundle r E h ↦
      (p.1, (⟨p.1, p.2.val⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
          (fun x ↦ E x →L[ℂ] E x)))) inferInstance

attribute [local instance] hermitianProjectiveTopology

/-- The actual projection of the projective bundle to the original base. -/
def hermitianProjectiveProjection : C(HermitianProjectiveBundle r E h, X) where
  toFun p := p.1
  continuous_toFun := by
    have hc : Continuous (fun p : HermitianProjectiveBundle r E h ↦
        (p.1, (⟨p.1, p.2.val⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
            (fun x ↦ E x →L[ℂ] E x)))) := continuous_induced_dom
    exact hc.fst

/-- The tautological line carries the induced topology of the original pullback bundle. -/
@[reducible]
def hermitianProjectiveLineTopology :
    TopologicalSpace (TotalSpace Unit (HermitianProjectiveLine r E h)) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (HermitianProjectiveLine r E h) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit
        ((hermitianProjectiveProjection r E h : HermitianProjectiveBundle r E h → X) *ᵖ E)))
    inferInstance

attribute [local instance] hermitianProjectiveLineTopology isFiniteRank_pullback
  sectionModule sumTopology InnerProductSpace.Core.toPreInner'

/-- The actual tautological ranges form a continuous complex line bundle. -/
theorem isFiniteRank_hermitianProjectiveLine :
    IsFiniteRank (HermitianProjectiveLine r E h) := by
  set_option backward.isDefEq.respectTransparency.types false in
    /- Stage 1: near p, choose a nonzero vector in its projection range.
    Extend it using an original bundle chart to a local section near its base.
    Apply the varying projection. Native Hom-bundle evaluation is continuous,
    and the resulting section has its original nonzero value at p. Shrink to the
    open set where it is nonzero. Rank one makes it a basis of each nearby range.
    Stage 2: scalar multiplication by this section gives the linear chart inverse.
    The forward coefficient is h(section,vector)/h(section,section), with the
    first slot conjugate-linear and the second slot linear. The denominator is
    positive on this neighborhood. Joint metric continuity proves continuity of
    this inverse coefficient for the original induced line topology. These
    rank-one linear charts cover the projective base and establish IsFiniteRank.
    This construction is local on the original projective bundle; no replacement
    line carrier, chosen global section or topology is introduced. -/
    classical
    let V := EuclideanSpace ℂ (Fin r)
    let := modelTopology V E
    let := isFiniteRank_model V E
    let Q := HermitianProjectiveBundle r E h
    let p : C(Q, X) := hermitianProjectiveProjection r E h
    let L := HermitianProjectiveLine r E h
    let F := (p : Q → X) *ᵖ E
    have hbase : Continuous (fun q : Q ↦ q.1) := p.continuous
    have hc : Continuous (fun q : Q ↦
        (q.1, (⟨q.1, q.2.val⟩ :
          TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)))) :=
      continuous_induced_dom
    have hP : Continuous (fun q : Q ↦
        (⟨q.1, q.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x))) :=
      hc.snd
    have hdouble : Topology.IsInducing (fun z : TotalSpace Unit (E ×ᵇ E) ↦
        ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
          (⟨z.proj, z.snd.2⟩ : TotalSpace Unit E))) := ⟨rfl⟩
    -- Project an original local frame vector to obtain a nonzero local range section.
    constructor
    intro q₀
    let : Nontrivial (L q₀) := Module.nontrivial_of_finrank_pos (by
      rw [q₀.2.property.2.1]
      exact zero_lt_one)
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : L q₀)
    let e := trivializationAt V E q₀.1
    have he : q₀.1 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt V E q₀.1
    let w := (e ⟨q₀.1, v₀.val⟩).2
    let s (q : Q) : L q := ⟨q.2.val (e.symm q.1 w), ⟨e.symm q.1 w, rfl⟩⟩
    let U₀ : Set Q := p ⁻¹' e.baseSet
    have hU₀ : IsOpen U₀ := e.open_baseSet.preimage hbase
    have hs₀ : (s q₀).val = v₀.val := by
      change q₀.2.val (e.symm q₀.1 (e ⟨q₀.1, v₀.val⟩).2) = v₀.val
      rw [e.symm_apply_apply_mk he]
      obtain ⟨v, hv⟩ := v₀.property
      rw [← hv]
      exact DFunLike.congr_fun (q₀.2.property.1) v
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
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (q.2.property.2.1) (hnonzero q hq) v
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


/-- The normalized integral first Chern class of the actual projective tautological line. -/
def hermitianProjectiveChernRoot :
    singularCohomology ℤ (HermitianProjectiveBundle r E h) 2 :=
  letI := isFiniteRank_hermitianProjectiveLine r E h
  firstChernClass (HermitianProjectiveLine r E h) (fun p ↦ p.2.property.2.1)

attribute [local instance] hermitianFlagTopology

/-- Each original flag line determines its actual point in the original projective bundle. -/
def hermitianFlagLineProjection (i : Fin r) :
    C(HermitianFlagBundle r E h, HermitianProjectiveBundle r E h) where
  toFun p := ⟨p.1, p.2.val i, p.2.property.1 i,
    p.2.property.2.1 i, p.2.property.2.2.2.2 i⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    have hc : Continuous (fun p : HermitianFlagBundle r E h ↦
        (p.1, fun j : Fin r ↦
          (⟨p.1, p.2.val j⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
              (fun x ↦ E x →L[ℂ] E x)))) := continuous_induced_dom
    exact hc.fst.prodMk ((continuous_apply i).comp hc.snd)

/-- The projective image of an original flag retains exactly its original base projection. -/
theorem hermitianProjectiveProjection_comp_flagLineProjection (i : Fin r) :
    (hermitianProjectiveProjection r E h).comp (hermitianFlagLineProjection r E h i) =
      hermitianFlagProjection r E h := rfl

end AtiyahSinger.ComplexBundle

/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundle
public import AtiyahSinger.Topology.EquivariantVectorBundle
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Associated bundles from original equivariant vector families

Public module ID: M1531.

For an equivariant vector family E over Y, the total carrier is the original
associated quotient of P times TotalSpace E. Its projection sends [p,(y,v)]
to the original class [p,y]. The fiber over z is the actual subtype of that
total quotient, not a replacement coordinate space.

Choose one representative (p,y) of z only to transport the algebra from E(y).
Every representative map v -> [p,(y,v)] is linear for those same operations.
The total topology is induced from the original quotient by forgetting the
fiber certificate. Principal charts and the original local finite charts of E
give finite linear local triviality on P associated Y, with locally varying rank.
The chosen representatives are never asserted to vary continuously.

Sources: SG II.3 and Appendix A, HU IV.5--6, and ASI I Section 2 provide the
associated and equivariant bundle constructions. Passing from a fixed vector
representation to a varying equivariant vector family is the standard associated
family supplement. The earlier AssociatedVectorBundle for a fixed representation
is retained unchanged. No compactness, separation, paracompactness, norm, metric,
or global rank bound is required. The construction certificates below retain
these original quotient fibers, transported operations and total topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- The actual quotient projection sends [p,(y,v)] to [p,y]. -/
def associatedEquivariantProjection (σ : EquivariantStructure G E) :
    letI := σ.toMulAction
    C(AssociatedBundle G P (TotalSpace Unit E), AssociatedBundle G P Y) :=
  letI := σ.toMulAction
  letI : ContinuousSMul G (TotalSpace Unit E) := ⟨σ.continuous_action⟩
  associatedBundleMap ⟨π Unit E, continuous_proj (E := E)⟩ (fun _ _ ↦ rfl)

/-- The original associated total-quotient fiber over an original associated base point. -/
abbrev AssociatedEquivariantFiber (_hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E)
    (z : AssociatedBundle G P Y) : Type _ :=
  letI := σ.toMulAction
  {w : AssociatedBundle G P (TotalSpace Unit E) // associatedEquivariantProjection σ w = z}

/-- An original vector determines its actual quotient class in the specified associated fiber. -/
def associatedEquivariantFiberMk (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (p : P) (y : Y)
    {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z)
    (v : E y) : AssociatedEquivariantFiber hP σ z :=
  letI := σ.toMulAction
  ⟨associatedBundleMk G P (TotalSpace Unit E) p ⟨y, v⟩, hz⟩

/-- Every original representative gives bijective vector coordinates on its actual fiber. -/
theorem associatedEquivariantFiberMk_bijective (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (p : P) (y : Y)
    {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z) :
    Function.Bijective (associatedEquivariantFiberMk hP σ p y hz) := by
  /- First prove injectivity. An orbit element relating [p,(y,u)] and [p,(y,v)]
  fixes p; principal freeness makes it one, and the total-space identity
  then gives u = v in E y.
  For surjectivity, represent the target vector by [q,t]. Its base equation
  yields g with p = q*g and y = (g⁻¹ • t).proj. Transport the vector
  g⁻¹ • t along this base equality to E y. The same diagonal relation
  identifies its class at p with the original target vector. -/
  classical
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  constructor
  · -- A group element relating two vectors with the same principal point must be the identity.
    intro u v huv
    have hq := congrArg Subtype.val huv
    obtain ⟨g, hg⟩ := Quotient.exact hq
    have hfix : MulOpposite.op g • p = p := (congrArg Prod.fst hg).symm
    obtain ⟨k, _, huniq⟩ := hP.existsUnique_smul p p rfl
    have hg1 : g = 1 := (huniq g hfix).trans (huniq 1 (one_smul Gᵐᵒᵖ p)).symm
    have hvu := congrArg (fun t : P × TotalSpace Unit E ↦ t.2) hg
    rw [hg1] at hvu
    simp only [inv_one, one_smul] at hvu
    exact (TotalSpace.mk_injective y hvu).symm
  · -- The quotient equality on bases moves the original total vector into this exact fiber.
    intro w
    obtain ⟨⟨q, t⟩, hw⟩ := Quotient.exists_rep w.val
    have hbase : associatedBundleMk G P Y q t.proj = associatedBundleMk G P Y p y :=
      ((congrArg (associatedEquivariantProjection σ) hw).trans w.property).trans hz.symm
    obtain ⟨g, hg⟩ := Quotient.exact hbase
    have hp : p = MulOpposite.op g • q := congrArg Prod.fst hg
    have hy : (g⁻¹ • t).proj = y := (congrArg Prod.snd hg).symm
    let v : E y := cast (congrArg E hy) (g⁻¹ • t).snd
    refine ⟨v, ?_⟩
    apply Subtype.ext
    have hrel : associatedBundleMk G P (TotalSpace Unit E) q t =
        associatedBundleMk G P (TotalSpace Unit E) p ⟨y, v⟩ := by
      apply Quotient.sound
      refine ⟨g, ?_⟩
      apply Prod.ext
      · exact hp
      · exact TotalSpace.mk_cast (F := Unit) (E := E) hy (g⁻¹ • t).snd
    exact hrel.symm.trans hw

/-- Algebraic coordinates use one actual representative of z and its original vector fiber. -/
def associatedEquivariantFiberEquiv (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (z : AssociatedBundle G P Y) :
    AssociatedEquivariantFiber hP σ z ≃ E (Quotient.out z).2 :=
  (Equiv.ofBijective
    (associatedEquivariantFiberMk hP σ (Quotient.out z).1 (Quotient.out z).2
      (Quotient.out_eq z))
    (associatedEquivariantFiberMk_bijective hP σ (Quotient.out z).1
      (Quotient.out z).2 (Quotient.out_eq z))).symm

/-- Addition on the actual quotient fiber is transported from its specified original coordinates. -/
@[reducible]
def associatedEquivariantFiberAddCommGroup (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (z : AssociatedBundle G P Y) :
    AddCommGroup (AssociatedEquivariantFiber hP σ z) :=
  (associatedEquivariantFiberEquiv hP σ z).addCommGroup

attribute [local instance] associatedEquivariantFiberAddCommGroup

/-- Complex scalar multiplication uses the same coordinates and the same transported addition. -/
@[reducible]
def associatedEquivariantFiberModule (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (z : AssociatedBundle G P Y) :
    Module ℂ (AssociatedEquivariantFiber hP σ z) :=
  (associatedEquivariantFiberEquiv hP σ z).addEquiv.module ℂ

attribute [local instance] associatedEquivariantFiberModule

/-- The chosen coordinates are a complex-linear equivalence for these original fiber operations. -/
def associatedEquivariantFiberLinearEquiv (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (z : AssociatedBundle G P Y) :
    AssociatedEquivariantFiber hP σ z ≃ₗ[ℂ] E (Quotient.out z).2 :=
  (associatedEquivariantFiberEquiv hP σ z).addEquiv.linearEquiv ℂ

/-- Every representative map is linear for the same transported algebra on the actual fiber. -/
theorem associatedEquivariantFiberMk_isLinear (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (p : P) (y : Y)
    {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z) :
    IsLinearMap ℂ (associatedEquivariantFiberMk hP σ p y hz) := by
  /- Let (p₀,y₀) be the representative selected by Quotient.out. The equality
  of base classes gives g carrying (p,y) to (p₀,y₀), so y₀ = g⁻¹ • y.
  In these selected coordinates the representative map is σ.linearMap g⁻¹ y
  followed by the cast along that base equality. The quotient relation proves
  this coordinate formula, and linearity transfers through e₀.symm.
  The same transported addition and scalar multiplication therefore work
  for every principal representative; no continuous selection is used. -/
  classical
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let e₀ := associatedEquivariantFiberLinearEquiv hP σ z
  have hbase : associatedBundleMk G P Y p y =
      associatedBundleMk G P Y (Quotient.out z).1 (Quotient.out z).2 :=
    hz.trans (Quotient.out_eq z).symm
  obtain ⟨g, hg⟩ := Quotient.exact hbase
  have hy : g⁻¹ • y = (Quotient.out z).2 := (congrArg Prod.snd hg).symm
  let L : E y →ₗ[ℂ] E (Quotient.out z).2 :=
    (LinearEquiv.cast hy).toLinearMap.comp (σ.linearMap g⁻¹ y)
  -- The arbitrary representative differs from the chosen one by this actual linear action.
  have hcoord (v : E y) : associatedEquivariantFiberMk hP σ p y hz v = e₀.symm (L v) := by
    apply Subtype.ext
    change associatedBundleMk G P (TotalSpace Unit E) p ⟨y, v⟩ =
      associatedBundleMk G P (TotalSpace Unit E) (Quotient.out z).1
        ⟨(Quotient.out z).2, L v⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Prod.ext
    · exact congrArg (fun t : P × Y ↦ t.1) hg
    · exact TotalSpace.mk_cast (F := Unit) (E := E) hy (σ.linearMap g⁻¹ y v)
  constructor
  · intro u v
    simp only [hcoord, map_add]
  · intro c v
    simp only [hcoord, map_smul]

/-- Forgetting only fiber membership identifies the total family with the original quotient. -/
def associatedEquivariantTotalEquiv (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) :
    letI := σ.toMulAction
    TotalSpace Unit (AssociatedEquivariantFiber hP σ) ≃
      AssociatedBundle G P (TotalSpace Unit E) :=
  letI := σ.toMulAction
  { toFun := fun z ↦ z.snd.val
    invFun := fun w ↦ ⟨associatedEquivariantProjection σ w, ⟨w, rfl⟩⟩
    left_inv := by
      intro z
      rcases z with ⟨z, w, hw⟩
      cases hw
      rfl
    right_inv := fun _ ↦ rfl }

/-- The total topology comes from the same original quotient, independently of algebraic choices. -/
@[reducible]
def associatedEquivariantTotalTopology (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) :
    TopologicalSpace (TotalSpace Unit (AssociatedEquivariantFiber hP σ)) :=
  letI := σ.toMulAction
  TopologicalSpace.induced (associatedEquivariantTotalEquiv hP σ) inferInstance

attribute [local instance] associatedEquivariantTotalTopology

/-- The total equivalence is a homeomorphism for the original associated quotient topology. -/
def associatedEquivariantTotalHomeomorph (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) :
    letI := σ.toMulAction
    TotalSpace Unit (AssociatedEquivariantFiber hP σ) ≃ₜ
      AssociatedBundle G P (TotalSpace Unit E) :=
  letI := σ.toMulAction
  (associatedEquivariantTotalEquiv hP σ).toHomeomorphOfIsInducing ⟨rfl⟩

/-- Principal charts and original finite vector charts give the associated finite-rank family. -/
theorem isFiniteRank_associatedEquivariant (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) :
    IsFiniteRank (AssociatedEquivariantFiber hP σ) := by
  /- Stage 1: use the exact continuous total action sigma.toMulAction.
  A principal chart over U identifies the two associated quotients locally
  with U times Y and U times TotalSpace E. Their projections commute with
  identity on U times the original E projection: the total formula is
  [p,(y,v)] mapped to (projection(p),sigma(gamma(p))(y,v)), and the base
  formula is [p,y] mapped to (projection(p),gamma(p)*y).
  Stage 2: choose an original finite linear chart of E around that moved
  point of Y. Its product with U is a finite linear chart over the open
  subset of the original associated base. Every representative map is linear
  for the actual transported operations, so these coordinates are linear on
  each associated fiber. The rank is only the local rank of this E chart.
  Stage 3: the original open quotient charts and associatedEquivariantTotalHomeomorph
  prove continuity in both directions, preserving the original quotient topology
  and the actual projection. The chart domains cover the associated base.
  No globally constant rank, choice of continuous representatives, compactness,
  separation property, metric, or replacement total space is required. -/
  classical
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let : ContinuousSMul G (TotalSpace Unit E) := ⟨σ.continuous_action⟩
  let H := associatedEquivariantTotalHomeomorph hP σ
  let pA := associatedEquivariantProjection (P := P) σ
  let pB := associatedBundleProjection (F := Y) hP
  have hproj (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ)) :
      pA (H w) = w.proj := w.snd.property
  have hprojB (q : AssociatedBundle G P (TotalSpace Unit E)) :
      associatedBundleProjection (F := TotalSpace Unit E) hP q = pB (pA q) := by
    induction q using Quotient.inductionOn with
    | h t => rfl
  have hcontinuousProj : Continuous (π Unit (AssociatedEquivariantFiber hP σ)) :=
    (pA.continuous.comp H.continuous_toFun).congr hproj
  constructor
  intro z₀
  obtain ⟨e, he₀, he⟩ := hP.exists_trivialization (pB z₀)
  obtain ⟨eB, hBb, hBf, hBi⟩ := exists_associatedBundleTrivialization (F := Y) hP e he
  obtain ⟨eT, hTb, hTf, hTi⟩ :=
    exists_associatedBundleTrivialization (F := TotalSpace Unit E) hP e he
  -- The two quotient charts use the same principal chart and commute with the original projection.
  have hcomm (q : AssociatedBundle G P (TotalSpace Unit E))
      (hq : associatedBundleProjection (F := TotalSpace Unit E) hP q ∈ e.baseSet) :
      eB (pA q) = ((eT q).1, (eT q).2.proj) := by
    induction q using Quotient.inductionOn with
    | h t =>
      rcases t with ⟨p, v⟩
      change eB (associatedBundleMk G P Y p v.proj) = _
      exact (hBf p v.proj hq).trans
        (congrArg (fun t : B × TotalSpace Unit E ↦ (t.1, t.2.proj)) (hTf p v hq)).symm
  have hinverseProj (b : B) (v : TotalSpace Unit E) (hb : b ∈ e.baseSet) :
      pA (eT.toOpenPartialHomeomorph.symm (b, v)) =
        eB.toOpenPartialHomeomorph.symm (b, v.proj) := by
    rw [hTi b v hb, hBi b v.proj hb]
    rfl
  have hz₀ : z₀ ∈ eB.source := eB.mem_source.mpr (hBb.symm ▸ he₀)
  obtain ⟨r, d, hd₀, hdlin⟩ := IsFiniteRank.exists_linear_trivialization (E := E) (eB z₀).2
  let V : Set (AssociatedBundle G P Y) := eB.source ∩ eB ⁻¹' (Set.univ ×ˢ d.baseSet)
  have hV : IsOpen V := eB.toOpenPartialHomeomorph.isOpen_inter_preimage
    (isOpen_univ.prod d.open_baseSet)
  have hb (z : AssociatedBundle G P Y) (hz : z ∈ V) : (eB z).1 ∈ e.baseSet :=
    hBb ▸ eB.mem_target.mp (eB.map_source hz.1)
  have hsource (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ))
      (hw : w.proj ∈ eB.source) : H w ∈ eT.source := by
    apply eT.mem_source.mpr
    rw [hTb, hprojB, hproj]
    exact hBb ▸ eB.mem_source.mp hw
  have hcommTotal (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ))
      (hw : w.proj ∈ eB.source) :
      eB w.proj = ((eT (H w)).1, (eT (H w)).2.proj) := by
    rw [← hproj w]
    exact hcomm (H w) (hTb ▸ eT.mem_source.mp (hsource w hw))
  have hdsource (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ))
      (hw : w.proj ∈ V) : (eT (H w)).2 ∈ d.source := by
    apply d.mem_source.mpr
    have hc : (eB w.proj).2 = (eT (H w)).2.proj :=
      congrArg Prod.snd (hcommTotal w hw.1)
    exact hc ▸ hw.2.2
  let inverse (y : AssociatedBundle G P Y × (Fin r → ℂ)) :
      TotalSpace Unit (AssociatedEquivariantFiber hP σ) :=
    H.symm (eT.toOpenPartialHomeomorph.symm
      ((eB y.1).1, d.toOpenPartialHomeomorph.symm ((eB y.1).2, y.2)))
  have hinverseBase (y : AssociatedBundle G P Y × (Fin r → ℂ)) (hy : y.1 ∈ V) :
      (inverse y).proj = y.1 := by
    change pA (eT.toOpenPartialHomeomorph.symm
      ((eB y.1).1, d.toOpenPartialHomeomorph.symm ((eB y.1).2, y.2))) = y.1
    rw [hinverseProj _ _ (hb y.1 hy), d.proj_symm_apply' hy.2.2]
    exact eB.left_inv hy.1
  -- Compose these charts on their actual open domains in the unchanged total topology.
  let t : Trivialization (Fin r → ℂ) (π Unit (AssociatedEquivariantFiber hP σ)) :=
    { toFun := fun w ↦ (w.proj, (d (eT (H w)).2).2)
      invFun := inverse
      source := π Unit (AssociatedEquivariantFiber hP σ) ⁻¹' V
      target := V ×ˢ Set.univ
      baseSet := V
      map_source' := fun _ hw ↦ ⟨hw, Set.mem_univ _⟩
      map_target' := by
        intro y hy
        change (inverse y).proj ∈ V
        rw [hinverseBase y hy.1]
        exact hy.1
      left_inv' := by
        intro w hw
        change H.symm (eT.toOpenPartialHomeomorph.symm
          ((eB w.proj).1,
            d.toOpenPartialHomeomorph.symm ((eB w.proj).2, (d (eT (H w)).2).2))) = w
        rw [hcommTotal w hw.1, d.symm_apply_mk_proj (hdsource w hw)]
        change H.symm (eT.toOpenPartialHomeomorph.symm (eT (H w))) = w
        exact (congrArg H.symm (eT.left_inv (hsource w hw.1))).trans
          (H.symm_apply_apply w)
      right_inv' := by
        intro y hy
        apply Prod.ext
        · exact hinverseBase y hy.1
        · change (d (eT (H (inverse y))).2).2 = y.2
          dsimp only [inverse]
          rw [H.apply_symm_apply, eT.apply_symm_apply' (hTb.symm ▸ hb y.1 hy.1)]
          rw [d.apply_symm_apply' hy.1.2.2]
      open_source := hV.preimage hcontinuousProj
      open_target := hV.prod isOpen_univ
      open_baseSet := hV
      continuousOn_toFun := by
        apply hcontinuousProj.continuousOn.prodMk
        apply continuous_snd.comp_continuousOn
        apply d.toOpenPartialHomeomorph.continuousOn.comp
        · exact continuous_snd.comp_continuousOn
            (eT.toOpenPartialHomeomorph.continuousOn.comp H.continuous_toFun.continuousOn
              (fun w hw ↦ hsource w hw.1))
        · exact fun w hw ↦ hdsource w hw
      continuousOn_invFun := by
        have hcB : ContinuousOn (fun y : AssociatedBundle G P Y × (Fin r → ℂ) ↦ eB y.1)
            (V ×ˢ Set.univ) :=
          eB.toOpenPartialHomeomorph.continuousOn.comp continuous_fst.continuousOn
            (fun y hy ↦ hy.1.1)
        apply H.symm.continuous_toFun.comp_continuousOn
        apply eT.toOpenPartialHomeomorph.continuousOn_symm.comp
        · exact (continuous_fst.comp_continuousOn hcB).prodMk
            (d.toOpenPartialHomeomorph.continuousOn_symm.comp
              ((continuous_snd.comp_continuousOn hcB).prodMk continuous_snd.continuousOn)
              (fun y hy ↦ d.mem_target.mpr hy.1.2.2))
        · exact fun y hy ↦ eT.mem_target.mpr (hTb.symm ▸ hb y.1 hy.1)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  refine ⟨r, t, ⟨hz₀, Set.mem_univ _, hd₀⟩, ?_⟩
  intro z hz
  -- Representative linearity uses the same algebra; the inverse section gives linear charts.
  let b := (eB z).1
  let y := (eB z).2
  let p₀ := e.toOpenPartialHomeomorph.symm (b, 1)
  have hzrep : associatedBundleMk G P Y p₀ y = z :=
    (hBi b y (hb z hz)).symm.trans (eB.left_inv hz.1)
  let mk := associatedEquivariantFiberMk hP σ p₀ y hzrep
  have hmk := associatedEquivariantFiberMk_isLinear hP σ p₀ y hzrep
  have hsurj := (associatedEquivariantFiberMk_bijective hP σ p₀ y hzrep).2
  have hformula (v : E y) : (t ⟨z, mk v⟩).2 = (d ⟨y, v⟩).2 := by
    change (d (eT (associatedBundleMk G P (TotalSpace Unit E) p₀ ⟨y, v⟩)).2).2 = _
    rw [← hTi b ⟨y, v⟩ (hb z hz), eT.apply_symm_apply' (hTb.symm ▸ hb z hz)]
  constructor
  · intro u v
    obtain ⟨u₀, rfl⟩ := hsurj u
    obtain ⟨v₀, rfl⟩ := hsurj v
    rw [← hmk.map_add, hformula, hformula, hformula]
    exact (hdlin y hz.2.2).map_add u₀ v₀
  · intro c v
    obtain ⟨v₀, rfl⟩ := hsurj v
    rw [← hmk.map_smul, hformula, hformula]
    exact (hdlin y hz.2.2).map_smul c v₀

end AtiyahSinger

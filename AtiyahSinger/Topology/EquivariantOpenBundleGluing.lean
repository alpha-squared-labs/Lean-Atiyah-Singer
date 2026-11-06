/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundleEmbedding
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportCutoff

/-!
# Equivariant gluing on compact control windows

Public module ID: M1793.

Isomorphisms between the original bundles glue on two invariant open sets when
both local values agree on their intersection. The resulting global map retains
the specified actions and the actual local fiber maps. This supplies the local
square extension in equivariant compact-support excision; no arbitrary bundle
extension across an open-image boundary or global rank bound is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- Compatible equivariant local isomorphisms glue to one specified global square. -/
theorem Iso.exists_equivariant_gluing (σ : EquivariantStructure G E)
    (τ : EquivariantStructure G F) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (hUinv : ∀ (g : G) (x : X), g • x ∈ U ↔ x ∈ U)
    (hVinv : ∀ (g : G) (x : X), g • x ∈ V ↔ x ∈ V)
    (u : RelativeTriple E F U) (v : RelativeTriple E F V)
    (hagree : ∀ (x : X) (hxU : x ∈ U) (hxV : x ∈ V),
      u.linearEquiv ⟨x, hxU⟩ = v.linearEquiv ⟨x, hxV⟩)
    (hu : ∀ (g : G) (x : U) (w : E x),
      u.linearEquiv ⟨g • x.val, (hUinv g x.val).mpr x.property⟩
          (σ.linearMap g x.val w) = τ.linearMap g x.val (u.linearEquiv x w))
    (hv : ∀ (g : G) (x : V) (w : E x),
      v.linearEquiv ⟨g • x.val, (hVinv g x.val).mpr x.property⟩
          (σ.linearMap g x.val w) = τ.linearMap g x.val (v.linearEquiv x w)) :
    ∃ e : Iso E F, e.IsEquivariant σ τ ∧
      (∀ (x : X) (hx : x ∈ U), e.linearEquiv x = u.linearEquiv ⟨x, hx⟩) ∧
      ∀ (x : X) (hx : x ∈ V), e.linearEquiv x = v.linearEquiv ⟨x, hx⟩ :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  have hother (x : X) (hx : x ∉ U) : x ∈ V := by
    have h : x ∈ U ∪ V := by rw [hcover]; trivial
    exact h.resolve_left hx
  let eFiber (x : X) : E x ≃ₗ[ℂ] F x :=
    if hx : x ∈ U then u.linearEquiv ⟨x, hx⟩ else v.linearEquiv ⟨x, hother x hx⟩
  have heU (x : X) (hx : x ∈ U) : eFiber x = u.linearEquiv ⟨x, hx⟩ := by
    dsimp only [eFiber]
    rw [dite_eq_left hx]
  have heV (x : X) (hx : x ∈ V) : eFiber x = v.linearEquiv ⟨x, hx⟩ := by
    by_cases hxU : x ∈ U
    · exact (heU x hxU).trans (hagree x hxU hx)
    · dsimp only [eFiber]
      rw [dite_eq_right hxU]
  -- Each local map is read in the original bundle through its actual pullback lift.
  have hlocal (S : Set X) (j : RelativeTriple E F S)
      (hj : ∀ (x : X) (hx : x ∈ S), eFiber x = j.linearEquiv ⟨x, hx⟩) :
      ContinuousOn (fun z : TotalSpace Unit E ↦
        (⟨z.proj, eFiber z.proj z.snd⟩ : TotalSpace Unit F))
        {z : TotalSpace Unit E | z.proj ∈ S} := by
    let A := {z : TotalSpace Unit E | z.proj ∈ S}
    let base : A → S := fun z ↦ ⟨z.val.proj, z.property⟩
    have hbase : Continuous base :=
      ((continuous_proj (E := E)).comp continuous_subtype_val).subtype_mk _
    let lift (z : A) : TotalSpace Unit (Restrict E S) := ⟨base z, z.val.snd⟩
    have hlift : Continuous lift := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E (Subtype.val : S → X)).continuous_iff]
      exact hbase.prodMk continuous_subtype_val
    have hout := (Pullback.continuous_lift Unit F (Subtype.val : S → X)).comp
      (j.continuous_total.comp hlift)
    rw [continuousOn_iff_continuous_domRestrict]
    apply hout.congr
    intro z
    change (⟨z.val.proj, j.linearEquiv (base z) z.val.snd⟩ : TotalSpace Unit F) =
      ⟨z.val.proj, eFiber z.val.proj z.val.snd⟩
    rw [hj z.val.proj z.property]
    rfl
  have hcontinuous : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, eFiber z.proj z.snd⟩ : TotalSpace Unit F)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.proj ∈ U
    · exact (hlocal U u heU).continuousAt ((hU.preimage continuous_proj).mem_nhds hz)
    · exact (hlocal V v heV).continuousAt
        ((hV.preimage continuous_proj).mem_nhds (hother z.proj hz))
  let a : Hom E F := {
    linearMap x := (eFiber x).toLinearMap
    continuous_total := hcontinuous }
  let e := a.toIso (fun x ↦ (eFiber x).bijective)
  have he (x : X) : e.linearEquiv x = eFiber x := by
    apply LinearEquiv.ext
    intro w
    rfl
  refine ⟨e, ?_, (fun x hx ↦ (he x).trans (heU x hx)),
    fun x hx ↦ (he x).trans (heV x hx)⟩
  -- Both local pieces intertwine the same original actions, and their domains are invariant.
  intro g x w
  change e.linearEquiv (g • x) (σ.linearMap g x w) = τ.linearMap g x (e.linearEquiv x w)
  by_cases hx : x ∈ U
  · rw [he, he, heU x hx, heU (g • x) ((hUinv g x).mpr hx)]
    exact hu g ⟨x, hx⟩ w
  · have hxV := hother x hx
    rw [he, he, heV x hxV, heV (g • x) ((hVinv g x).mpr hxV)]
    exact hv g ⟨x, hxV⟩ w

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- A square-zero equivariant bundle map gives the elementary shear with its specified inverse.
The compact-window projection and the comparison square use these same elementary shears. -/
theorem Hom.exists_equivariant_shear (σ : EquivariantStructure G E) (N : Hom E E)
    (hN : ∀ x v, N.linearMap x (N.linearMap x v) = 0) (heq : N.IsEquivariant σ σ)
    (c : ℂ) :
    ∃ e : Iso E E, e.IsEquivariant σ σ ∧
      (∀ x v, e.linearEquiv x v = v + c • N.linearMap x v) ∧
      ∀ x v, (e.linearEquiv x).symm v = v + (-c) • N.linearMap x v := by
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit E → X) *ᵖ E) := isFiniteRank_pullback p
  have hcontinuous (a : ℂ) : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, z.snd + a • N.linearMap z.proj z.snd⟩ : TotalSpace Unit E)) := by
    -- Addition takes place in the same pulled fiber over the entire original total space.
    have hi : Continuous (fun z : TotalSpace Unit E ↦
        (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit E → X) *ᵖ E))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
      exact continuous_id.prodMk continuous_id
    have hmap : Continuous (fun z : TotalSpace Unit E ↦
        (⟨z, N.linearMap z.proj z.snd⟩ :
          TotalSpace Unit ((p : TotalSpace Unit E → X) *ᵖ E))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
      exact continuous_id.prodMk N.continuous_total
    exact (Pullback.continuous_lift Unit E p).comp
      (continuous_add_section ((p : TotalSpace Unit E → X) *ᵖ E) _ _ hi
        (continuous_smul_section ((p : TotalSpace Unit E → X) *ᵖ E)
          (ContinuousMap.const _ a) _ hmap))
  let e : Iso E E := {
    linearEquiv x := {
      toLinearMap := LinearMap.id + c • N.linearMap x
      invFun v := v + (-c) • N.linearMap x v
      left_inv v := by
        change v + c • N.linearMap x v +
          (-c) • N.linearMap x (v + c • N.linearMap x v) = v
        simp [map_add, hN]
      right_inv v := by
        change v + (-c) • N.linearMap x v +
          c • N.linearMap x (v + (-c) • N.linearMap x v) = v
        simp [map_add, hN] }
    continuous_total := hcontinuous c
    continuous_symm := hcontinuous (-c) }
  refine ⟨e, ?_, (fun _ _ ↦ rfl), (fun _ _ ↦ rfl)⟩
  -- The two terms separately intertwine the specified action on the original bundle.
  intro g x v
  change σ.linearMap g x v + c • N.linearMap (g • x) (σ.linearMap g x v) =
    σ.linearMap g x (v + c • N.linearMap x v)
  rw [heq g x v, map_add, map_smul]

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger

open Topology

/-- A map constant outside an inner open window extends along an open embedding by that constant.
The compact window is retained exactly; the target need not be a vector space. -/
theorem exists_open_extension_eq_const
    {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    [T2Space Y] (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (L U : Set X) (hL : IsCompact L) (hU : IsOpen U) (hUL : U ⊆ L)
    (p : C(L, T)) (c : T) (hp : ∀ x : L, x.val ∉ U → p x = c) :
    ∃ q : C(Y, T), (∀ x : L, q (f x) = p x) ∧ ∀ y ∉ f '' U, q y = c := by
  classical
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let g : C(L, Y) := ⟨fun x ↦ f x.val, f.continuous.comp continuous_subtype_val⟩
  have hge : IsEmbedding g := hf.isEmbedding.comp IsEmbedding.subtypeVal
  let e := hge.toHomeomorph
  let q (y : Y) : T := if hy : y ∈ Set.range g then p (e.symm ⟨y, hy⟩) else c
  have hqg (x : L) : q (g x) = p x := by
    dsimp only [q]
    rw [dite_eq_left ⟨x, rfl⟩]
    exact congrArg p (hge.toHomeomorph_symm_apply x)
  have hqout (y : Y) (hy : y ∉ f '' U) : q y = c := by
    by_cases hyg : y ∈ Set.range g
    · obtain ⟨x, rfl⟩ := hyg
      rw [hqg]
      apply hp x
      intro hx
      exact hy ⟨x.val, hx, rfl⟩
    · exact dite_eq_right hyg
  -- The two closed domains overlap only where the prescribed map is already constant.
  have hcompact : IsCompact (Set.range g) := isCompact_range g.continuous
  have hfirst : ContinuousOn q (Set.range g) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply (p.continuous.comp e.symm.continuous).congr
    intro y
    change p (e.symm y) = q y.val
    dsimp only [q]
    rw [dite_eq_left y.property]
  have hsecond : ContinuousOn q (f '' U)ᶜ :=
    continuousOn_const.congr (fun y hy ↦ hqout y hy)
  have hcover : Set.range g ∪ (f '' U)ᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ f '' U
    · obtain ⟨x, hx, rfl⟩ := hy
      exact Or.inl ⟨⟨x, hUL hx⟩, rfl⟩
    · exact Or.inr hy
  have hcont : Continuous q := by
    rw [← continuousOn_univ, ← hcover]
    exact hfirst.union_of_isClosed hsecond hcompact.isClosed
      (hf.isOpenMap U hU).isClosed_compl
  exact ⟨⟨q, hcont⟩, hqg, hqout⟩

end AtiyahSinger

namespace AtiyahSinger.ComplexBundle

open Bundle

open scoped Matrix

attribute [local instance] trivialTopology IdempotentMatrix.fiberTotalSpaceTopology
  IdempotentMatrix.isFiniteRank_fiber

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- A specified continuous equivariant idempotent splits onto its actual finite image bundle. -/
theorem Hom.exists_equivariant_image_of_idempotent (κ : FiniteContinuousRepresentation G)
    (p : Hom (Bundle.Trivial X (Fin κ.dimension → ℂ))
      (Bundle.Trivial X (Fin κ.dimension → ℂ)))
    (hp : ∀ x v, p.linearMap x (p.linearMap x v) = p.linearMap x v)
    (heq : p.IsEquivariant (EquivariantStructure.ofFiniteRepresentation κ)
      (EquivariantStructure.ofFiniteRepresentation κ)) :
    ∃ B : FiniteBundle X, ∃ σ : EquivariantStructure G B.Fiber,
      ∃ i : Hom B.Fiber (Bundle.Trivial X (Fin κ.dimension → ℂ)),
        ∃ r : Hom (Bundle.Trivial X (Fin κ.dimension → ℂ)) B.Fiber,
          i.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation κ) ∧
          r.IsEquivariant (EquivariantStructure.ofFiniteRepresentation κ) σ ∧
          (∀ x v, i.linearMap x (r.linearMap x v) = p.linearMap x v) ∧
          ∀ x w, r.linearMap x (i.linearMap x w) = w := by
  classical
  let T := Bundle.Trivial X (Fin κ.dimension → ℂ)
  let A (x : X) : Matrix (Fin κ.dimension) (Fin κ.dimension) ℂ :=
    LinearMap.toMatrix' (p.linearMap x)
  have hA (i j : Fin κ.dimension) : Continuous (fun x ↦ A x i j) := by
    have hsection : Continuous (fun x : X ↦
        (⟨x, Pi.single j (1 : ℂ)⟩ : TotalSpace Unit T)) :=
      continuous_induced_rng.mpr (continuous_id.prodMk continuous_const)
    exact (continuous_apply i).comp
      ((continuous_induced_rng.mp (p.continuous_total.comp hsection)).snd)
  have hAA (x : X) : A x * A x = A x := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact LinearMap.ext (hp x)
  let P : IdempotentMatrix C(X, ℂ) := {
    size := κ.dimension
    matrix i j := ⟨fun x ↦ A x i j, hA i j⟩
    mul_self := by
      ext i j x
      change (∑ k : Fin κ.dimension,
        (⟨fun y ↦ A y i k, hA i k⟩ : C(X, ℂ)) *
          (⟨fun y ↦ A y k j, hA k j⟩ : C(X, ℂ))) x = A x i j
      simpa [Matrix.mul_apply] using congrFun (congrFun (hAA x) i) j }
  have hmat (x : X) (v : Fin κ.dimension → ℂ) :
      (P.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix *ᵥ v = p.linearMap x v :=
    LinearMap.toMatrix'_mulVec (p.linearMap x) v
  have hmem (x : X) (v : Fin κ.dimension → ℂ) :
      v ∈ P.fiber x ↔ p.linearMap x v = v := by
    constructor
    · rintro ⟨w, hw⟩
      change Fin κ.dimension → ℂ at w
      have hv : p.linearMap x w = v := (hmat x w).symm.trans hw
      rw [← hv]
      exact hp x w
    · intro hv
      exact ⟨v, (hmat x v).trans hv⟩
  let B := FiniteBundle.ofFamily (fun x ↦ P.fiber x)
  have hcoords : Continuous (fun z : TotalSpace Unit B.Fiber ↦ (z.proj, z.snd.val)) :=
    continuous_induced_dom
  have hcoords_inj : Function.Injective
      (fun z : TotalSpace Unit B.Fiber ↦ (z.proj, z.snd.val)) := by
    rintro ⟨x, u⟩ ⟨y, v⟩ h
    obtain ⟨rfl, huv⟩ := Prod.mk.inj h
    exact congrArg (TotalSpace.mk x) (Subtype.ext huv)
  have hc (g : G) (x : X) (v : Fin κ.dimension → ℂ) :
      p.linearMap (g • x) (κ.representation g v) = κ.representation g (p.linearMap x v) :=
    heq g x v
  -- The original ambient representation preserves this exact image, with its induced topology.
  let σ : EquivariantStructure G B.Fiber := {
    linearMap g x := {
      toFun v := ⟨κ.representation g v.val, (hmem (g • x) _).mpr (by
        rw [hc, (hmem x v.val).mp v.property])⟩
      map_add' u v := by apply Subtype.ext; exact map_add (κ.representation g) u.val v.val
      map_smul' c v := by apply Subtype.ext; exact map_smul (κ.representation g) c v.val }
    one_map x v := by
      apply hcoords_inj
      change ((1 : G) • x, κ.representation 1 v.val) = (x, v.val)
      simp
    mul_map g h x v := by
      apply hcoords_inj
      change ((g * h) • x, κ.representation (g * h) v.val) =
        (g • (h • x), κ.representation g (κ.representation h v.val))
      simp [map_mul, mul_smul, mul_apply_eq_comp]
    continuous_action := continuous_induced_rng.mpr
      ((continuous_fst.smul (hcoords.fst.comp continuous_snd)).prodMk
        (κ.continuous_action.comp
          (continuous_fst.prodMk (hcoords.snd.comp continuous_snd)))) }
  let i : Hom B.Fiber T := {
    linearMap x := (P.fiber x).subtype
    continuous_total := continuous_induced_rng.mpr hcoords }
  let r : Hom T B.Fiber := {
    linearMap x := (p.linearMap x).codRestrict (P.fiber x)
      (fun v ↦ (hmem x _).mpr (hp x v))
    continuous_total := by
      apply continuous_induced_rng.mpr
      change Continuous (fun z : TotalSpace Unit T ↦ (z.proj, p.linearMap z.proj z.snd))
      exact continuous_induced_rng.mp p.continuous_total }
  refine ⟨B, σ, i, r, (fun _ _ _ ↦ rfl), ?_, (fun _ _ ↦ rfl), ?_⟩
  · intro g x v
    apply Subtype.ext
    exact hc g x v
  · intro x w
    apply Subtype.ext
    exact (hmem x w.val).mp w.property

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

attribute [local instance] trivialTopology

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X]
  [TopologicalSpace Y] [T2Space Y] [MulAction G Y] [ContinuousSMul G Y]

/-- An equivariant projection constant off an inner window extends with its actual split image.
Both image maps are retained, so a later stable square can use the same projection witnesses. -/
theorem Hom.exists_equivariant_image_extension (κ : FiniteContinuousRepresentation G)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (hfEq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (L U : Set X) (hL : IsCompact L) (hU : IsOpen U) (hUL : U ⊆ L)
    (hLinv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L)
    (p : C(L, (Fin κ.dimension → ℂ) →L[ℂ] (Fin κ.dimension → ℂ)))
    (q : (Fin κ.dimension → ℂ) →L[ℂ] (Fin κ.dimension → ℂ))
    (hp : ∀ x v, p x (p x v) = p x v) (hq : ∀ v, q (q v) = q v)
    (hpout : ∀ x : L, x.val ∉ U → p x = q)
    (hpeq : ∀ (g : G) (x : L) (v : Fin κ.dimension → ℂ),
      p ⟨g • x.val, (hLinv g x.val).mpr x.property⟩ (κ.representation g v) =
        κ.representation g (p x v))
    (hqeq : ∀ (g : G) (v : Fin κ.dimension → ℂ),
      q (κ.representation g v) = κ.representation g (q v)) :
    ∃ B : FiniteBundle Y, ∃ σ : EquivariantStructure G B.Fiber,
      ∃ i : Hom B.Fiber (Bundle.Trivial Y (Fin κ.dimension → ℂ)),
        ∃ r : Hom (Bundle.Trivial Y (Fin κ.dimension → ℂ)) B.Fiber,
          i.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation κ) ∧
          r.IsEquivariant (EquivariantStructure.ofFiniteRepresentation κ) σ ∧
          (∀ x w, r.linearMap x (i.linearMap x w) = w) ∧
          (∀ (x : L) v, i.linearMap (f x) (r.linearMap (f x) v) = p x v) ∧
          ∀ (y : Y), y ∉ f '' U → ∀ v, i.linearMap y (r.linearMap y v) = q v := by
  classical
  obtain ⟨P, hPin, hPout⟩ := exists_open_extension_eq_const f hf L U hL hU hUL p q hpout
  have houtside (y : Y) (hy : y ∉ f '' L) : y ∉ f '' U :=
    fun h ↦ hy (Set.image_mono hUL h)
  have hinv (g : G) (y : Y) : g • y ∈ f '' L ↔ y ∈ f '' L := by
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨g⁻¹ • x, (hLinv g⁻¹ x).mpr hx, ?_⟩
      rw [hfEq, hxy, inv_smul_smul]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g • x, (hLinv g x).mpr hx, hfEq g x⟩
  -- The extension has exactly the original projection on the compact window,
  -- and exactly the supplied constant projection everywhere else.
  have hidem (y : Y) (v : Fin κ.dimension → ℂ) : P y (P y v) = P y v := by
    by_cases hy : y ∈ f '' L
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [hPin ⟨x, hx⟩]
      exact hp ⟨x, hx⟩ v
    · rw [hPout y (houtside y hy)]
      exact hq v
  have hequiv (g : G) (y : Y) (v : Fin κ.dimension → ℂ) :
      P (g • y) (κ.representation g v) = κ.representation g (P y v) := by
    by_cases hy : y ∈ f '' L
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [← hfEq, hPin ⟨g • x, (hLinv g x).mpr hx⟩, hPin ⟨x, hx⟩]
      exact hpeq g ⟨x, hx⟩ v
    · rw [hPout y (houtside y hy),
        hPout (g • y) (houtside (g • y) (fun h ↦ hy ((hinv g y).mp h)))]
      exact hqeq g v
  let T := Bundle.Trivial Y (Fin κ.dimension → ℂ)
  let a : Hom T T := {
    linearMap y := (P y).toLinearMap
    continuous_total := by
      have hc : Continuous (fun z : TotalSpace Unit T ↦ (z.proj, z.snd)) :=
        continuous_induced_dom
      exact continuous_induced_rng.mpr
        (hc.fst.prodMk ((P.continuous.comp hc.fst).clm_apply hc.snd)) }
  obtain ⟨B, σ, i, r, hi, hr, hir, hri⟩ :=
    a.exists_equivariant_image_of_idempotent κ hidem hequiv
  refine ⟨B, σ, i, r, hi, hr, hri, ?_, ?_⟩
  · intro x v
    exact (hir (f x) v).trans (congrArg (fun A ↦ A v) (hPin x))
  · intro y hy v
    exact (hir y v).trans (congrArg (fun A ↦ A v) (hPout y hy))

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [T2Space X] [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- Zero extension by an invariant cutoff retains the specified moving-fiber action. -/
theorem CompactSupportTriple.IsEquivariant.cutoffHom
    {a : CompactSupportTriple E F} {σ : EquivariantStructure G E}
    {τ : EquivariantStructure G F} (ha : a.IsEquivariant σ τ)
    (ρ : C(X, unitInterval)) (U : Set X) (hU : IsOpen U) (haU : a.control ⊆ U)
    (hρzero : ∀ x ∈ U, ρ x = 0) (hρinv : ∀ (g : G) (x : X), ρ (g • x) = ρ x) :
    (a.cutoffHom ρ U hU haU hρzero).IsEquivariant σ τ :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro g x v
  change a.cutoffLinearMap ρ (g • x) (σ.linearMap g x v) =
    τ.linearMap g x (a.cutoffLinearMap ρ x v)
  by_cases hx : x ∈ a.control
  · have hgx : g • x ∈ a.control := (ha.invariant_control g x).mpr hx
    dsimp only [CompactSupportTriple.cutoffLinearMap]
    rw [dite_eq_left hx, dite_eq_left hgx]
    exact (map_zero (τ.linearMap g x)).symm
  · have hgx : g • x ∉ a.control := fun h ↦ hx ((ha.invariant_control g x).mp h)
    dsimp only [CompactSupportTriple.cutoffLinearMap]
    rw [dite_eq_right hx, dite_eq_right hgx]
    change ((ρ (g • x) : ℝ) : ℂ) • a.boundary.linearEquiv
      ⟨g • x, hgx⟩ (σ.linearMap g x v) =
        τ.linearMap g x (((ρ x : ℝ) : ℂ) • a.boundary.linearEquiv ⟨x, hx⟩ v)
    rw [hρinv]
    exact (congrArg (fun w : F (g • x) ↦ ((ρ x : ℝ) : ℂ) • w)
      (ha.boundary_intertwines g ⟨x, hx⟩ v)).trans ((τ.linearMap g x).map_smul _ _).symm

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The vector-preserving adapter between the native pullback and sum topologies.
This implementation map is used repeatedly when gluing the original stabilized bundle square. -/
def sumPullbackIso (f : C(X, Y)) (E F : FiniteBundle Y) :
    Iso ((E.sum F).pullback f).Fiber ((E.pullback f).sum (F.pullback f)).Fiber :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  {
  linearEquiv _ := LinearEquiv.refl ℂ _
  continuous_total := by
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber f).continuous_iff]
      exact (Pullback.continuous_proj Unit (E.sum F).Fiber f).prodMk
        (continuous_sum_fst.comp (Pullback.continuous_lift Unit (E.sum F).Fiber f))
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber f).continuous_iff]
      exact (Pullback.continuous_proj Unit (E.sum F).Fiber f).prodMk
        (continuous_sum_snd.comp (Pullback.continuous_lift Unit (E.sum F).Fiber f))
  continuous_symm := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (E.sum F).Fiber f).continuous_iff]
    apply ((Pullback.continuous_proj Unit E.Fiber f).comp continuous_sum_fst).prodMk
    apply continuous_induced_rng.mpr
    exact ((Pullback.continuous_lift Unit E.Fiber f).comp continuous_sum_fst).prodMk
      ((Pullback.continuous_lift Unit F.Fiber f).comp continuous_sum_snd)
 }

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {E F : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- A bundle isomorphism over an embedded base descends to its actual image,
retaining the same map on every original fiber. -/
theorem Iso.exists_descend_embedding (f : C(X, Y)) (hf : IsEmbedding f)
    (a : Iso ((f : X → Y) *ᵖ E) ((f : X → Y) *ᵖ F)) :
    ∃ b : RelativeTriple E F (Set.range f),
      ∀ (x : X) (v : E (f x)),
        b.linearEquiv ⟨f x, ⟨x, rfl⟩⟩ v = a.linearEquiv x v :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let R := Set.range f
  let p : C(R, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(R, X) := ⟨hf.toHomeomorph.symm, hf.toHomeomorph.symm.continuous⟩
  have hq (x : X) : q ⟨f x, ⟨x, rfl⟩⟩ = x := hf.toHomeomorph_symm_apply x
  have hcomp : f.comp q = p := by
    ext y
    exact congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply y)
  let cE := pullbackCompIso (E := E) f q
  let cF := pullbackCompIso (E := F) f q
  let J : Iso (((f.comp q : C(R, Y)) : R → Y) *ᵖ E)
      (((f.comp q : C(R, Y)) : R → Y) *ᵖ F) :=
    cE.symm.trans ((a.pullback q).trans cF)
  have hJ (y : R) (v : E (f (q y))) : J.linearEquiv y v = a.linearEquiv (q y) v := by
    have hi : (cE.linearEquiv y).symm v = v := by
      apply (cE.linearEquiv y).injective
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    change cF.linearEquiv y (a.linearEquiv (q y) ((cE.linearEquiv y).symm v)) = _
    rw [pullbackCompIso_apply, hi]
  -- The composite base map is literally the subtype inclusion. Transport both
  -- original bundles and their native pullback topologies along that equality.
  let family (s : C(R, Y)) := Iso ((s : R → Y) *ᵖ E) ((s : R → Y) *ᵖ F)
  let b : RelativeTriple E F R := cast (congrArg family hcomp) J
  have htransport (s t : C(R, Y)) (h : s = t) (u : family s)
      (y : R) (v : E (t y)) :
      (cast (congrArg family h) u).linearEquiv y v =
        cast (congrArg F (congrArg (fun k : C(R, Y) ↦ k y) h))
          (u.linearEquiv y
            (cast (congrArg E (congrArg (fun k : C(R, Y) ↦ k y) h).symm) v)) := by
    subst t
    rfl
  have hpoint (x₁ x₂ : X) (h : x₁ = x₂) (v : E (f x₂)) :
      cast (congrArg F (congrArg f h))
        (a.linearEquiv x₁ (cast (congrArg E (congrArg f h).symm) v)) =
          a.linearEquiv x₂ v := by
    subst x₂
    rfl
  refine ⟨b, ?_⟩
  intro x v
  let y : R := ⟨f x, ⟨x, rfl⟩⟩
  have hy : f (q y) = f x := congrArg (fun k : C(R, Y) ↦ k y) hcomp
  calc
    b.linearEquiv y v = cast (congrArg F hy)
        (J.linearEquiv y (cast (congrArg E hy.symm) v)) :=
      htransport (f.comp q) p hcomp J y v
    _ = cast (congrArg F hy)
        (a.linearEquiv (q y) (cast (congrArg E hy.symm) v)) :=
      congrArg (cast (congrArg F hy)) (hJ y (cast (congrArg E hy.symm) v))
    _ = a.linearEquiv x v := hpoint (q y) x (hq x) v

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback

/-- The native sum/pullback comparison intertwines the same two pulled bundle actions. -/
theorem EquivariantStructure.sumPullbackIso_isEquivariant (E F : FiniteBundle Y)
    (σ : EquivariantStructure G E.Fiber) (τ : EquivariantStructure G F.Fiber)
    (f : C(X, Y)) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    (sumPullbackIso f E F).IsEquivariant ((σ.sum τ).pullback f heq)
      ((σ.pullback f heq).sum (τ.pullback f heq)) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  intro g x w
  -- Both components use exactly the same target-base transport.
  have htransport (y z : Y) (h : y = z)
      (LE : E.Fiber (f x) →ₗ[ℂ] E.Fiber z) (LF : F.Fiber (f x) →ₗ[ℂ] F.Fiber z) :
      (Eq.mpr (congrArg (fun b ↦ (E.Fiber (f x) × F.Fiber (f x)) →ₗ[ℂ]
        (E.Fiber b × F.Fiber b)) h) (LE.prodMap LF)) w =
      ((Eq.mpr (congrArg (fun b ↦ E.Fiber (f x) →ₗ[ℂ] E.Fiber b) h) LE) w.1,
        (Eq.mpr (congrArg (fun b ↦ F.Fiber (f x) →ₗ[ℂ] F.Fiber b) h) LF) w.2) := by
    subst z
    rfl
  exact htransport (f (g • x)) (g • f x) (heq g x)
    (σ.linearMap g (f x)) (τ.linearMap g (f x))

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger

open Topology
open scoped unitInterval

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [LocallyCompactSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] [MulAction G Y]

/-- Compact control inside an equivariant open image admits invariant cutoff data
whose entire compact window remains inside that same image. -/
theorem exists_invariant_time_cutoff_in_openImage
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (K : Set Y) (hK : IsCompact K) (hKrange : K ⊆ Set.range f) :
    ∃ U : Set Y, IsOpen U ∧ K ⊆ U ∧
      (∀ (g : G) (y : Y), g • y ∈ U ↔ y ∈ U) ∧
      ∃ L : Set Y, IsCompact L ∧ U ⊆ L ∧ L ⊆ Set.range f ∧
        (∀ (g : G) (y : Y), g • y ∈ L ↔ y ∈ L) ∧
        ∃ ρ : C(Y, I), (∀ (g : G) (y : Y), ρ (g • y) = ρ y) ∧
          (∀ y ∈ U, ρ y = 0) ∧ ∀ y ∉ L, ρ y = 1 := by
  classical
  have hpK : IsCompact (f ⁻¹' K) := hf.isEmbedding.isInducing.isCompact_preimage' hK hKrange
  obtain ⟨U, hU, hKU, hUinv, L, hL, hUL, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
    ComplexBundle.exists_invariant_time_cutoff (G := G) (f ⁻¹' K) hpK
  obtain ⟨V, hV, hLV, _, M, hM, hVM, _, _, _, _, _⟩ :=
    ComplexBundle.exists_invariant_time_cutoff (G := G) L hL
  let j : C(M, X) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨q, hqin, hqout⟩ := exists_open_extension_eq_const f hf M V hM hV hVM
    (ρ.comp j) (1 : I) (fun x hx ↦ hρone x (fun h ↦ hx (hLV h)))
  -- Extending by one retains every source value, including points outside the compact window.
  have hqf (x : X) : q (f x) = ρ x := by
    by_cases hx : x ∈ M
    · exact hqin ⟨x, hx⟩
    · have hxV : f x ∉ f '' V := by
        rintro ⟨z, hz, hzx⟩
        exact hx ((hf.injective hzx) ▸ hVM hz)
      exact (hqout (f x) hxV).trans (hρone x (fun h ↦ hx (hVM (hLV h)))).symm
  have hqone (y : Y) (hy : y ∉ f '' L) : q y = 1 := by
    by_cases hym : y ∈ f '' V
    · obtain ⟨x, hx, rfl⟩ := hym
      exact (hqf x).trans (hρone x (fun h ↦ hy ⟨x, h, rfl⟩))
    · exact hqout y hym
  have hinv (S : Set X) (hS : ∀ (g : G) (x : X), g • x ∈ S ↔ x ∈ S)
      (g : G) (y : Y) : g • y ∈ f '' S ↔ y ∈ f '' S := by
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨g⁻¹ • x, (hS g⁻¹ x).mpr hx, ?_⟩
      rw [heq, hxy, inv_smul_smul]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g • x, (hS g x).mpr hx, heq g x⟩
  refine ⟨f '' U, hf.isOpenMap U hU, ?_, hinv U hUinv, f '' L,
    hL.image f.continuous, Set.image_mono hUL, Set.image_subset_range _ _,
    hinv L hLinv, q, ?_, ?_, hqone⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := hKrange hy
    exact ⟨x, hKU hy, rfl⟩
  · -- The same compact image is invariant, so the outside value stays one on every orbit.
    intro g y
    by_cases hy : y ∈ f '' L
    · obtain ⟨x, _, rfl⟩ := hy
      rw [← heq, hqf, hqf, hρinv]
    · exact (hqone (g • y) (fun h ↦ hy ((hinv L hLinv g y).mp h))).trans (hqone y hy).symm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hqf x).trans (hρzero x hx)

end AtiyahSinger

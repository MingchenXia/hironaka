/-
Adapted from Hironaka/Scheme/BlowUp/GlueIdealSheaf.lean in
EnvelopeProperty/deps/hironaka-ep33, original SHA256
d595329279b1042b853e0f78f61f42991704360da160bba599cbe29d2abbd10e.
Copyright (c) 2026 Resolution; author Chris Elliott (Resolution).
Original Lean formalization by Claude Fable 5.1; Apache License 2.0.
Modified: Mathlib-only imports and the proved whole-ideal stalk/pullback
adapters, a disjoint namespace, native actual-open point producer.
License reproduced in Algebra/AdicCompletionTransport.lean.
-/
import DeJongAlterations.Algebra.NodeFittingIdealSheafStalks
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Actual entire ideal-sheaf gluing on arbitrary original open covers

The cover, native ideal-sheaf data, full overlap equality, actual closed
subschemes, and native relative gluing are retained. No finiteness,
Noetherian or separation hypothesis is used.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingIdealSheaf

open AlgebraicGeometry Scheme.IdealSheafData CategoryTheory Limits TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- Actual membership in an original open gives a point of that very open subscheme. -/
theorem exists_ι_eq_of_mem {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ y : U.toScheme, U.ι y = x := by
  apply Scheme.Hom.mem_opensRange.mp
  rwa [Scheme.Opens.opensRange_ι]


section ExtOfCover

/-- Along an open immersion the stalk maps are isomorphisms, so equal inverse images give equal
stalk ideals at the points of the image. -/
theorem stalkIdeal_eq_of_comap_eq (f : Y ⟶ X) [IsOpenImmersion f] {J K : X.IdealSheafData}
    (h : J.comap f = K.comap f) (y : Y) : stalkIdeal J (f y) = stalkIdeal K (f y) := by
  have h1 := stalkIdeal_comap J f y
  have h2 := stalkIdeal_comap K f y
  rw [h] at h1
  have hbij : Function.Bijective (f.stalkMap y).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  rw [← Ideal.comap_map_of_bijective _ hbij (I := stalkIdeal J (f y)), ← h1, h2,
    Ideal.comap_map_of_bijective _ hbij]

/-- An ideal sheaf is determined by its inverse images along the members of an open cover
(a consequence of extensionality by stalks, `ext_stalkIdeal`). -/
theorem ext_of_openCover {J K : X.IdealSheafData} (𝒱 : X.OpenCover.{u})
    (h : ∀ i, J.comap (𝒱.f i) = K.comap (𝒱.f i)) : J = K := by
  refine ext_stalkIdeal fun x => ?_
  obtain ⟨i, y, rfl⟩ := 𝒱.exists_eq x
  exact stalkIdeal_eq_of_comap_eq (𝒱.f i) (h i) y

/-- A point of an open subscheme, viewed in the ambient scheme, lies in the open. -/
theorem opens_ι_mem {Z : Scheme.{u}} {U : Z.Opens}
    (x : U.toScheme) : U.ι x ∈ U := by
  have : U.ι x ∈ U.ι.opensRange := Scheme.Hom.mem_opensRange.mpr ⟨x, rfl⟩
  rwa [Scheme.Opens.opensRange_ι] at this

end ExtOfCover

variable (𝒰 : X.OpenCover.{u})

/-- The compatibility of the local closed subschemes on the pairwise overlaps
`𝒰.X i ×_X 𝒰.X j` (the condition (37.2) in the proof of [Kol07, Proposition 37]). -/
def GlueCompat (I : ∀ i, (𝒰.X i).IdealSheafData) : Prop :=
  ∀ i j, (I i).comap (Limits.pullback.fst (𝒰.f i) (𝒰.f j)) = (I j).comap (Limits.pullback.snd
      (𝒰.f i) (𝒰.f j))

section Index

/-- The index type of the locally directed refinement: pairs `(i, V)` of a member of the cover
and an affine open of it. -/
structure GlueIdx : Type u where
  /-- The member of the cover. -/
  i : 𝒰.I₀
  /-- An affine open of the member. -/
  V : (𝒰.X i).affineOpens

variable {𝒰}

/-- The open subset of `X` covered by the index `p = (i, V)`: the image of `V` under `𝒰.f i`. -/
abbrev GlueIdx.opens (p : GlueIdx 𝒰) : X.Opens := (𝒰.f p.i) ''ᵁ p.V.1

/-- The member scheme of the index `p`: the affine open `V` itself. -/
abbrev GlueIdx.scheme (p : GlueIdx 𝒰) : Scheme.{u} := p.V.1.toScheme

/-- The map of the member to `X`: `V ⟶ 𝒰.X i ⟶ X`. -/
noncomputable abbrev GlueIdx.toX (p : GlueIdx 𝒰) : p.scheme ⟶ X := p.V.1.ι ≫ 𝒰.f p.i

/-- The affine open of the index, as an `IsAffineOpen` fact. -/
theorem GlueIdx.isAffineOpen (p : GlueIdx 𝒰) : IsAffineOpen p.V.1 := p.V.2

theorem GlueIdx.opensRange_toX (p : GlueIdx 𝒰) : p.toX.opensRange = p.opens := by
  change (p.V.1.ι ≫ 𝒰.f p.i).opensRange = _
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]

theorem GlueIdx.range_toX (p : GlueIdx 𝒰) : Set.range p.toX = (p.opens : Set X) := by
  rw [← Scheme.Hom.coe_opensRange, GlueIdx.opensRange_toX]

theorem GlueIdx.toX_apply (p : GlueIdx 𝒰) (y : p.scheme) : p.toX y = 𝒰.f p.i (p.V.1.ι y) :=
  Scheme.Hom.comp_apply _ _ y

/-- The preorder by inclusion of the covered opens. -/
instance : Preorder (GlueIdx 𝒰) := Preorder.lift GlueIdx.opens

theorem GlueIdx.le_def {p q : GlueIdx 𝒰} : p ≤ q ↔ p.opens ≤ q.opens := Iff.rfl

theorem GlueIdx.range_toX_subset {p q : GlueIdx 𝒰} (h : p ≤ q) :
    Set.range p.toX ⊆ Set.range q.toX := by
  rw [GlueIdx.range_toX, GlueIdx.range_toX]
  exact h

/-- The transition map `V_p ⟶ V_q` over `X` for `p ≤ q`. -/
noncomputable def GlueIdx.trans {p q : GlueIdx 𝒰} (h : p ≤ q) : p.scheme ⟶ q.scheme :=
  IsOpenImmersion.lift q.toX p.toX (GlueIdx.range_toX_subset h)

@[reassoc (attr := simp)]
theorem GlueIdx.trans_toX {p q : GlueIdx 𝒰} (h : p ≤ q) : GlueIdx.trans h ≫ q.toX = p.toX :=
  IsOpenImmersion.lift_fac _ _ _

theorem GlueIdx.isOpenImmersion_trans {p q : GlueIdx 𝒰} (h : p ≤ q) :
    IsOpenImmersion (GlueIdx.trans h) := by
  have : IsOpenImmersion (GlueIdx.trans h ≫ q.toX) := by
    rw [GlueIdx.trans_toX]
    infer_instance
  exact IsOpenImmersion.of_comp (GlueIdx.trans h) q.toX

instance {p q : GlueIdx 𝒰} (h : p ≤ q) : IsOpenImmersion (GlueIdx.trans h) :=
  GlueIdx.isOpenImmersion_trans h

theorem GlueIdx.trans_eq_of_comp_eq {p q : GlueIdx 𝒰} (h : p ≤ q) (g : p.scheme ⟶ q.scheme)
    (hg : g ≫ q.toX = p.toX) : g = GlueIdx.trans h :=
  (cancel_mono q.toX).mp (by rw [hg, GlueIdx.trans_toX])

theorem GlueIdx.trans_comp_trans {p q r : GlueIdx 𝒰} (hpq : p ≤ q) (hqr : q ≤ r) :
    GlueIdx.trans hpq ≫ GlueIdx.trans hqr = GlueIdx.trans (hpq.trans hqr) :=
  GlueIdx.trans_eq_of_comp_eq _ _ (by rw [Category.assoc, GlueIdx.trans_toX, GlueIdx.trans_toX])

theorem GlueIdx.trans_self (p : GlueIdx 𝒰) : GlueIdx.trans (le_refl p) = 𝟙 p.scheme :=
  (GlueIdx.trans_eq_of_comp_eq le_rfl (𝟙 _) (Category.id_comp _)).symm

end Index

section Cover

variable {𝒰}

/-- The members of the refinement cover `X`: every point lies in some `𝒰.X i`, and every point
of `𝒰.X i` lies in some affine open of it. -/
theorem GlueIdx.exists_toX_eq (x : X) : ∃ (p : GlueIdx 𝒰) (y : p.scheme), p.toX y = x := by
  obtain ⟨i, u, rfl⟩ := 𝒰.exists_eq x
  obtain ⟨V, huV⟩ := exists_affineOpens_mem u
  obtain ⟨y, hy⟩ := exists_ι_eq_of_mem huV
  exact ⟨⟨i, V⟩, y, by rw [GlueIdx.toX_apply, hy]⟩

variable (𝒰) in
/-- The locally directed refinement of `𝒰`: the affine opens of the members, mapping to `X`.
An `abbrev`, so that its index type is `GlueIdx 𝒰` on the nose. -/
noncomputable abbrev glueCover : X.OpenCover.{u} where
  I₀ := GlueIdx 𝒰
  X := GlueIdx.scheme
  f := GlueIdx.toX
  mem₀ := (Scheme.Cover.mkOfCovers (GlueIdx 𝒰) GlueIdx.scheme GlueIdx.toX GlueIdx.exists_toX_eq).mem₀

/-- Two points of members with the same image in `X` lie in a common smaller member: an affine
basic open of `V_p` inside `V_p ∩ (𝒰.f p.i)⁻¹(𝒰.f q.i ''ᵁ V_q)` around the point. -/
theorem GlueIdx.exists_common {p q : GlueIdx 𝒰} (xp : p.scheme) (xq : q.scheme)
    (hx : p.toX xp = q.toX xq) :
    ∃ (k : GlueIdx 𝒰) (hkp : k ≤ p) (hkq : k ≤ q) (y : k.scheme),
      GlueIdx.trans hkp y = xp ∧ GlueIdx.trans hkq y = xq := by
  have huV : p.V.1.ι xp ∈ p.V.1 := opens_ι_mem xp
  have hx' : 𝒰.f p.i (p.V.1.ι xp) = 𝒰.f q.i (q.V.1.ι xq) := by
    rw [GlueIdx.toX_apply, GlueIdx.toX_apply] at hx
    exact hx
  have huW : p.V.1.ι xp ∈ (𝒰.f p.i) ⁻¹ᵁ ((𝒰.f q.i) ''ᵁ q.V.1) := by
    change 𝒰.f p.i (p.V.1.ι xp) ∈ ((𝒰.f q.i) ''ᵁ q.V.1 : Set X)
    rw [hx', Scheme.Hom.coe_image]
    exact ⟨_, opens_ι_mem xq, rfl⟩
  obtain ⟨s, hs_le, hus⟩ := p.isAffineOpen.exists_basicOpen_le
    (V := p.V.1 ⊓ (𝒰.f p.i) ⁻¹ᵁ ((𝒰.f q.i) ''ᵁ q.V.1)) ⟨p.V.1.ι xp, ⟨huV, huW⟩⟩ huV
  have hkp : (⟨p.i, (𝒰.X p.i).affineBasicOpen s⟩ : GlueIdx 𝒰) ≤ p :=
    (Scheme.Hom.image_le_image_iff _ _ _).mpr (hs_le.trans inf_le_left)
  have hkq : (⟨p.i, (𝒰.X p.i).affineBasicOpen s⟩ : GlueIdx 𝒰) ≤ q :=
    ((Scheme.Hom.image_le_image_iff _ _ _).mpr (hs_le.trans inf_le_right)).trans
      ((𝒰.f p.i).image_preimage_le _)
  obtain ⟨y, hy⟩ :=
    exists_ι_eq_of_mem (U := ((𝒰.X p.i).affineBasicOpen s).1) hus
  refine ⟨⟨p.i, (𝒰.X p.i).affineBasicOpen s⟩, hkp, hkq, y, ?_, ?_⟩
  · apply p.toX.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, GlueIdx.trans_toX, GlueIdx.toX_apply, GlueIdx.toX_apply]
    exact congrArg (𝒰.f p.i) hy
  · apply q.toX.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, GlueIdx.trans_toX, GlueIdx.toX_apply, GlueIdx.toX_apply, ← hx']
    exact congrArg (𝒰.f p.i) hy

noncomputable instance glueCover_locallyDirected : (glueCover 𝒰).LocallyDirected where
  trans h := GlueIdx.trans h.le
  trans_id p := GlueIdx.trans_self p
  trans_comp hpq hqr := (GlueIdx.trans_comp_trans hpq.le hqr.le).symm
  w h := GlueIdx.trans_toX h.le
  directed {p q} x := by
    obtain ⟨k, hkp, hkq, y, hy₁, -⟩ := GlueIdx.exists_common
      ((Limits.pullback.fst p.toX q.toX) x) ((Limits.pullback.snd p.toX q.toX) x)
      (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.pullback.condition])
    refine ⟨k, hkp.hom, hkq.hom, y, ?_⟩
    apply (Limits.pullback.fst p.toX q.toX).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst]
    exact hy₁
  property_trans h := GlueIdx.isOpenImmersion_trans h.le

end Cover

section Data

variable {𝒰} (I : ∀ i, (𝒰.X i).IdealSheafData)

/-- The local closed subscheme over the index `p = (i, V)`: `V(I i) ∩ V`. -/
noncomputable abbrev GlueIdx.ideal (p : GlueIdx 𝒰) : p.scheme.IdealSheafData :=
  (I p.i).comap p.V.1.ι

/-- The compatibility hypothesis transported to a transition map: for `p ≤ q` the ideal of `q`
pulls back to the ideal of `p`, through `V_p ⟶ 𝒰.X i ×_X 𝒰.X j`. -/
theorem GlueIdx.comap_trans (compat : GlueCompat 𝒰 I) {p q : GlueIdx 𝒰} (h : p ≤ q) :
    (GlueIdx.ideal I q).comap (GlueIdx.trans h) = GlueIdx.ideal I p := by
  have hw : p.V.1.ι ≫ 𝒰.f p.i = (GlueIdx.trans h ≫ q.V.1.ι) ≫ 𝒰.f q.i := by
    rw [Category.assoc]
    exact (GlueIdx.trans_toX h).symm
  set φ : p.scheme ⟶ Limits.pullback (𝒰.f p.i) (𝒰.f q.i) :=
    Limits.pullback.lift p.V.1.ι (GlueIdx.trans h ≫ q.V.1.ι) hw
  have h1 : GlueIdx.ideal I p = ((I p.i).comap (Limits.pullback.fst _ _)).comap φ := by
    rw [← comap_comp, Limits.pullback.lift_fst]
  have h2 : (GlueIdx.ideal I q).comap (GlueIdx.trans h) =
      ((I q.i).comap (Limits.pullback.snd _ _)).comap φ := by
    rw [GlueIdx.ideal, ← comap_comp, ← comap_comp, Limits.pullback.lift_snd]
  rw [h1, h2, compat p.i q.i]

variable (compat : GlueCompat 𝒰 I)

/-- The transition map of the closed subschemes over `p ≤ q`. -/
noncomputable def GlueIdx.subschemeTrans {p q : GlueIdx 𝒰} (h : p ≤ q) :
    (GlueIdx.ideal I p).subscheme ⟶ (GlueIdx.ideal I q).subscheme :=
  subschemeMap _ _ (GlueIdx.trans h)
    (le_map_iff_comap_le.mpr (GlueIdx.comap_trans I compat h).le)

@[reassoc (attr := simp)]
theorem GlueIdx.subschemeTrans_subschemeι {p q : GlueIdx 𝒰} (h : p ≤ q) :
    GlueIdx.subschemeTrans I compat h ≫ (GlueIdx.ideal I q).subschemeι =
      (GlueIdx.ideal I p).subschemeι ≫ GlueIdx.trans h :=
  subschemeMap_subschemeι _ _ _ _

/-- The closed subschemes `Z_p` as a functor on the index preorder. -/
noncomputable def glueFunctor : GlueIdx 𝒰 ⥤ Scheme.{u} where
  obj p := (GlueIdx.ideal I p).subscheme
  map {p q} h := GlueIdx.subschemeTrans I compat h.le
  map_id p := by
    rw [← cancel_mono (GlueIdx.ideal I p).subschemeι, GlueIdx.subschemeTrans_subschemeι,
      Category.id_comp, GlueIdx.trans_self, Category.comp_id]
  map_comp {p q r} hpq hqr := by
    rw [← cancel_mono (GlueIdx.ideal I r).subschemeι, GlueIdx.subschemeTrans_subschemeι,
      Category.assoc, GlueIdx.subschemeTrans_subschemeι, GlueIdx.subschemeTrans_subschemeι_assoc,
      GlueIdx.trans_comp_trans]

/-- The closed immersions `Z_p ⟶ V_p` as a natural transformation to the cover's diagram. -/
noncomputable def glueNatTrans :
    glueFunctor I compat ⟶ (glueCover 𝒰).functorOfLocallyDirected where
  app p := (GlueIdx.ideal I p).subschemeι
  naturality _ _ h := GlueIdx.subschemeTrans_subschemeι I compat h.le

/-- The squares `Z_p → Z_q` over `V_p → V_q` are cartesian: a closed subscheme is its ideal sheaf
(Mathlib's `isPullback_of_isClosedImmersion`), and the ideals match by `comap_trans`. -/
theorem glueNatTrans_equifibered : (glueNatTrans I compat).Equifibered := by
  intro p q h
  refine (isPullback_of_isClosedImmersion (GlueIdx.ideal I p).subschemeι
    (GlueIdx.ideal I q).subschemeι (GlueIdx.subschemeTrans I compat h.le) (GlueIdx.trans h.le)
    (GlueIdx.subschemeTrans_subschemeι I compat h.le).symm ?_).flip
  rw [ker_subschemeι, ker_subschemeι]
  exact GlueIdx.comap_trans I compat h.le

/-- The relative gluing datum of the local closed subschemes [Sta, Tag 01LH]. -/
noncomputable def glueRelData : (glueCover 𝒰).RelativeGluingData where
  functor := glueFunctor I compat
  natTrans := glueNatTrans I compat
  equifibered := glueNatTrans_equifibered I compat

/-- The glued closed subscheme `Z ⊆ X` as a scheme. -/
noncomputable abbrev glueScheme : Scheme.{u} := (glueRelData I compat).glued

/-- The structure map `Z ⟶ X`. -/
noncomputable def glueι : glueScheme I compat ⟶ X := (glueRelData I compat).toBase

/-- The base change of `Z ⟶ X` to a member `V_p` is the closed immersion `Z_p ⟶ V_p`. -/
theorem isClosedImmersion_pullbackSnd (p : GlueIdx 𝒰) :
    IsClosedImmersion (Limits.pullback.snd (glueι I compat) p.toX) := by
  have H := ((glueRelData I compat).isPullback_natTrans_ι_toBase p).flip
  have e : Arrow.mk ((glueRelData I compat).natTrans.app p) ≅
      Arrow.mk (Limits.pullback.snd (glueRelData I compat).toBase ((glueCover 𝒰).f p)) :=
    Arrow.isoMk H.isoPullback (Iso.refl _)
      (H.isoPullback_hom_snd.trans (Category.comp_id _).symm)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).mp
    (inferInstanceAs (IsClosedImmersion (GlueIdx.ideal I p).subschemeι))

/-- `Z ⟶ X` is a closed immersion: it is one over every member of the refinement cover. -/
instance isClosedImmersion_glueι : IsClosedImmersion (glueι I compat) :=
  IsZariskiLocalAtTarget.of_openCover (glueCover 𝒰) fun p =>
    isClosedImmersion_pullbackSnd I compat p

/-- **The glued ideal sheaf**, the kernel of the closed immersion of the glued subscheme
[Kol07, Proposition 37, proof]. -/
noncomputable def glue : X.IdealSheafData := (glueι I compat).ker

/-- On a member `V_p` the glued ideal sheaf restricts to `Z_p`'s ideal. -/
theorem glue_comap_toX (p : GlueIdx 𝒰) : (glue I compat).comap p.toX = GlueIdx.ideal I p := by
  have H := (glueRelData I compat).isPullback_natTrans_ι_toBase p
  have : IsClosedImmersion (glueRelData I compat).toBase := isClosedImmersion_glueι I compat
  have h1 := (ker_fst_of_isClosedImmersion (glueRelData I compat).toBase ((glueCover 𝒰).f p)).symm
  have h2 := (Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom (Limits.pullback.fst _ _)).symm
  have h3 := congrArg Scheme.Hom.ker H.isoPullback_hom_fst
  have h4 := ker_subschemeι (GlueIdx.ideal I p)
  exact h1.trans (h2.trans (h3.trans h4))

/-- **`Z ∩ 𝒰.X i = V(I i)`** — the glued ideal sheaf restricts to `I i` on each member of the
cover. -/
theorem glue_comap (i : 𝒰.I₀) : (glue I compat).comap (𝒰.f i) = I i := by
  refine ext_stalkIdeal fun u => ?_
  obtain ⟨V, huV⟩ := exists_affineOpens_mem u
  have h := glue_comap_toX I compat ⟨i, V⟩
  change (glue I compat).comap (V.1.ι ≫ 𝒰.f i) = (I i).comap V.1.ι at h
  rw [comap_comp] at h
  have := stalkIdeal_eq_of_comap_eq V.1.ι (J := (glue I compat).comap (𝒰.f i)) (K := I i) h
    ⟨u, huV⟩
  rwa [Scheme.Opens.ι_apply] at this

/-- **Uniqueness** — an ideal sheaf restricting to `I i` on every member is the glued one. -/
theorem glue_unique (J : X.IdealSheafData) (hJ : ∀ i, J.comap (𝒰.f i) = I i) :
    J = glue I compat :=
  ext_of_openCover 𝒰 fun i => by rw [hJ, glue_comap]

end Data

end DeJongAlterations.Algebra.NodeFittingIdealSheaf

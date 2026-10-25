/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.CohomologyTwoCover
import DeJongAlterations.StableModification.CurvesField.RiemannRochAlgebra

/-!
# Twisting a module along a cover by two opens

Let `Y` be a scheme covered by two opens `U`, `V`, and let `u ∈ Γ(U ∩ V, 𝒪_Y)ˣ`. For a module `F`
on `Y`, the *twist* `F_u = twist F U V u` is the module obtained by gluing `F|_U` and `F|_V` along
`U ∩ V` through multiplication by `u`: its sections over `W` are the pairs
`(a, b) ∈ Γ(W ∩ U, F) × Γ(W ∩ V, F)` with `b = u · a` on `W ∩ U ∩ V`. It is a sheaf
(`twistPresheaf_isSheaf`), and `F_u|_U ≅ F|_U`, `F_u|_V ≅ F|_V` on sections
(`twistSectionsUEquiv`, `twistSectionsVEquiv`, `twistSectionsUVEquiv`).

If `D ⊆ V` is the zero locus of `f ∈ Γ(V, 𝒪_Y)` with `f` a unit on `U ∩ V`, the twist by `u = fᵐ`
(`m ∈ ℤ`) is `F(mD) = F ⊗ 𝒪(mD)`: sections of `𝒪(mD)` over `V` are `f⁻ᵐ` times regular functions
(the `V`-component is `fᵐ` times the function). For `D` an effective Cartier divisor on a curve
this is the sheaf of Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Prop. 4.4.6 (`𝒪(m Σ pᵢ)`, `references/temkin10-stable-modification/source/semi-stable.tex`,
lines 3204–3225); blueprint `sm-curves-fields-cohomology.tex`, `def:sm-twist`.

The Čech complex of `F_u` for the cover `(U, V)` is identified with the twisted two-term complex
`Γ(U, F) × Γ(V, F) → Γ(U ∩ V, F)`, `(a, b) ↦ b| - u · a|` of `RiemannRochAlgebra`
(`cechTwistOneEquiv`, `cechTwistZeroEquiv`).

## Main definitions

* `twistSubmodule F U V u W`, `twistPresheaf F U V u`, `twist F U V u`.
* `twistSectionsUEquiv`, `twistSectionsVEquiv`, `twistSectionsUVEquiv`: sections over `U`, `V`,
  `U ∩ V` (as `R`-modules through `c : R →+* Γ(Y, ⊤)`).

## Main results

* `twistPresheaf_isSheaf`: the twist is a sheaf.
* `cechTwistOneEquiv`, `cechTwistZeroEquiv`: `Ȟ¹((U, V), F_u) ≃ H1 ρU ρV (u ·)` and
  `Ȟ⁰((U, V), F_u) ≃ H0 ρU ρV (u ·)` in the notation of `RiemannRochAlgebra`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModification.CurvesField

noncomputable section

variable {Y : Scheme.{u}} (F : Y.Modules) (U V : Y.Opens) (u : Γ(Y, U ⊓ V)ˣ)

section Construction

lemma twist_le₁ (W : Y.Opens) : W ⊓ (U ⊓ V) ≤ W ⊓ U := inf_le_inf_left _ inf_le_left
lemma twist_le₂ (W : Y.Opens) : W ⊓ (U ⊓ V) ≤ W ⊓ V := inf_le_inf_left _ inf_le_right
lemma twist_le₃ (W : Y.Opens) : W ⊓ (U ⊓ V) ≤ U ⊓ V := inf_le_right

/-- The gluing condition `b = u · a` on `W ∩ U ∩ V`. -/
def TwistCond (W : Y.Opens) (a : Γ(F, W ⊓ U)) (b : Γ(F, W ⊓ V)) : Prop :=
  F.presheaf.map (homOfLE (twist_le₂ U V W)).op b =
    Y.presheaf.map (homOfLE (twist_le₃ U V W)).op (u : Γ(Y, U ⊓ V)) •
      F.presheaf.map (homOfLE (twist_le₁ U V W)).op a

lemma ringMap_ringMap {W₁ W₂ W₃ : Y.Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) (h₃ : W₃ ≤ W₁)
    (r : Γ(Y, W₁)) :
    Y.presheaf.map (homOfLE h₂).op (Y.presheaf.map (homOfLE h₁).op r) =
      Y.presheaf.map (homOfLE h₃).op r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The sections of the twist over `W`: pairs `(a, b)` with `b = u · a` on `W ∩ U ∩ V`. -/
def twistSubgroup (W : Y.Opens) : AddSubgroup (Γ(F, W ⊓ U) × Γ(F, W ⊓ V)) where
  carrier := {p | TwistCond F U V u W p.1 p.2}
  zero_mem' := by
    change F.presheaf.map _ (0 : Γ(F, W ⊓ V)) = _ • F.presheaf.map _ (0 : Γ(F, W ⊓ U))
    rw [map_zero, map_zero, smul_zero]
  add_mem' := by
    intro p q hp hq
    change F.presheaf.map _ (p.2 + q.2) = _ • F.presheaf.map _ (p.1 + q.1)
    rw [map_add, map_add, smul_add, hp, hq]
  neg_mem' := by
    intro p hp
    change F.presheaf.map _ (-p.2) = _ • F.presheaf.map _ (-p.1)
    rw [map_neg, map_neg, smul_neg, hp]

variable {F U V u} in
lemma mem_twistSubgroup {W : Y.Opens} (p : Γ(F, W ⊓ U) × Γ(F, W ⊓ V)) :
    p ∈ twistSubgroup F U V u W ↔ TwistCond F U V u W p.1 p.2 :=
  Iff.rfl

/-- Restriction `Γ(Y, W) → Γ(Y, W ∩ U)`. -/
abbrev resU (W : Y.Opens) : Γ(Y, W) →+* Γ(Y, W ⊓ U) :=
  (Y.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op).hom

/-- Restriction `Γ(Y, W) → Γ(Y, W ∩ V)`. -/
abbrev resV (W : Y.Opens) : Γ(Y, W) →+* Γ(Y, W ⊓ V) :=
  (Y.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom

lemma presheaf_map_self {W : Y.Opens} (h : W ≤ W) (x : Γ(F, W)) :
    F.presheaf.map (homOfLE h).op x = x := by
  rw [show homOfLE h = 𝟙 W from rfl, op_id, F.presheaf.map_id]
  rfl

lemma twistCond_smul {W : Y.Opens} (r : Γ(Y, W)) {a : Γ(F, W ⊓ U)} {b : Γ(F, W ⊓ V)}
    (h : TwistCond F U V u W a b) :
    TwistCond F U V u W (resU U W r • a) (resV V W r • b) := by
  unfold TwistCond at h ⊢
  rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, h, smul_comm, ringMap_ringMap,
    ringMap_ringMap]
  all_goals exact inf_le_left

instance (W : Y.Opens) : SMul Γ(Y, W) (twistSubgroup F U V u W) where
  smul r p := ⟨(resU U W r • p.1.1, resV V W r • p.1.2), twistCond_smul F U V u r p.2⟩

lemma twist_smul_val {W : Y.Opens} (r : Γ(Y, W)) (p : twistSubgroup F U V u W) :
    ((r • p : twistSubgroup F U V u W) : Γ(F, W ⊓ U) × Γ(F, W ⊓ V)) =
      (resU U W r • p.1.1, resV V W r • p.1.2) :=
  rfl

/-- The inclusion of the sections of the twist into the product of the `Γ(Y, W)`-modules
`Γ(W ∩ U, F) × Γ(W ∩ V, F)`. -/
def twistIncl (W : Y.Opens) : twistSubgroup F U V u W →+
    (sectionsModuleCat F (RingHom.id Γ(Y, W)) (W ⊓ U) inf_le_left ×
      sectionsModuleCat F (RingHom.id Γ(Y, W)) (W ⊓ V) inf_le_left) where
  toFun p := (p.1.1, p.1.2)
  map_zero' := rfl
  map_add' _ _ := rfl

instance (W : Y.Opens) : Module Γ(Y, W) (twistSubgroup F U V u W) :=
  Function.Injective.module Γ(Y, W) (twistIncl F U V u W)
    (fun _ _ h => Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)))
    (fun _ _ => rfl)

/-- Restriction of sections of the twist along `W' ≤ W`. -/
def twistRestrict {W W' : Y.Opens} (h : W' ≤ W) :
    twistSubgroup F U V u W →+ twistSubgroup F U V u W' where
  toFun p := ⟨(F.presheaf.map (homOfLE (inf_le_inf_right U h)).op p.1.1,
      F.presheaf.map (homOfLE (inf_le_inf_right V h)).op p.1.2), by
    have hp : TwistCond F U V u W p.1.1 p.1.2 := p.2
    change TwistCond F U V u W' _ _
    unfold TwistCond at hp ⊢
    rw [presheaf_map_map F _ _ ((twist_le₂ U V W').trans (inf_le_inf_right V h)),
      presheaf_map_map F _ _ ((twist_le₁ U V W').trans (inf_le_inf_right U h))]
    have hle : W' ⊓ (U ⊓ V) ≤ W ⊓ (U ⊓ V) := inf_le_inf_right _ h
    have e := congrArg (F.presheaf.map (homOfLE hle).op) hp
    rw [presheaf_map_map F _ _ ((twist_le₂ U V W').trans (inf_le_inf_right V h)),
      Scheme.Modules.map_smul, presheaf_map_map F _ _
        ((twist_le₁ U V W').trans (inf_le_inf_right U h)), ringMap_ringMap] at e
    exact e⟩
  map_zero' := by
    apply Subtype.ext
    exact Prod.ext (map_zero _) (map_zero _)
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext (map_add _ _ _) (map_add _ _ _)

@[simp]
lemma twistRestrict_apply_fst {W W' : Y.Opens} (h : W' ≤ W) (p : twistSubgroup F U V u W) :
    (twistRestrict F U V u h p).1.1 = F.presheaf.map (homOfLE (inf_le_inf_right U h)).op p.1.1 :=
  rfl

@[simp]
lemma twistRestrict_apply_snd {W W' : Y.Opens} (h : W' ≤ W) (p : twistSubgroup F U V u W) :
    (twistRestrict F U V u h p).1.2 = F.presheaf.map (homOfLE (inf_le_inf_right V h)).op p.1.2 :=
  rfl

lemma twistRestrict_smul {W W' : Y.Opens} (h : W' ≤ W) (r : Γ(Y, W))
    (p : twistSubgroup F U V u W) :
    twistRestrict F U V u h (r • p) =
      Y.presheaf.map (homOfLE h).op r • twistRestrict F U V u h p := by
  apply Subtype.ext
  apply Prod.ext
  · change F.presheaf.map _ (resU U W r • p.1.1) =
      resU U W' (Y.presheaf.map (homOfLE h).op r) • F.presheaf.map _ p.1.1
    rw [Scheme.Modules.map_smul, ringMap_ringMap, ringMap_ringMap]
    exact inf_le_left.trans h
  · change F.presheaf.map _ (resV V W r • p.1.2) =
      resV V W' (Y.presheaf.map (homOfLE h).op r) • F.presheaf.map _ p.1.2
    rw [Scheme.Modules.map_smul, ringMap_ringMap, ringMap_ringMap]
    exact inf_le_left.trans h

/-- The twist as a presheaf of abelian groups. -/
def twistPresheafAb : (Y.Opens)ᵒᵖ ⥤ Ab where
  obj W := AddCommGrpCat.of (twistSubgroup F U V u W.unop)
  map {W W'} i := AddCommGrpCat.ofHom (twistRestrict F U V u (leOfHom i.unop))
  map_id W := by
    ext p
    · exact presheaf_map_self F _ p.1.1
    · exact presheaf_map_self F _ p.1.2
  map_comp {W W' W''} i j := by
    ext p
    · exact (presheaf_map_map F _ _ _ p.1.1).symm
    · exact (presheaf_map_map F _ _ _ p.1.2).symm

instance (W : (Y.Opens)ᵒᵖ) :
    Module (Y.ringCatSheaf.obj.obj W) ((twistPresheafAb F U V u).obj W) :=
  inferInstanceAs (Module Γ(Y, W.unop) (twistSubgroup F U V u W.unop))

/-- The twist as a presheaf of modules. -/
def twistPresheaf : Y.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (twistPresheafAb F U V u) (fun {_ _} i r p =>
    twistRestrict_smul F U V u (leOfHom i.unop) r p)

lemma inf_iSup_le {ι : Type*} (W : ι → Y.Opens) (U : Y.Opens) :
    (⨆ i, W i) ⊓ U ≤ ⨆ i, (W i ⊓ U) := by
  rw [iSup_inf_eq]

/-- Gluing of sections of `F` over the opens `W i ⊓ U` (an auxiliary statement). -/
lemma exists_glue {ι : Type u} (W : ι → Y.Opens) (U : Y.Opens) (A : ∀ i, Γ(F, W i ⊓ U))
    (hA : ∀ i j, F.presheaf.map (homOfLE (inf_le_inf_right U
        (inf_le_left : W i ⊓ W j ≤ W i))).op (A i) =
      F.presheaf.map (homOfLE (inf_le_inf_right U (inf_le_right : W i ⊓ W j ≤ W j))).op (A j)) :
    ∃! a : Γ(F, (⨆ i, W i) ⊓ U), ∀ i,
      F.presheaf.map (homOfLE (inf_le_inf_right U (le_iSup W i))).op a = A i := by
  let G : TopCat.Sheaf Ab Y := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible G.1 (fun i => W i ⊓ U) A := by
    intro i j
    have hle : (W i ⊓ U) ⊓ (W j ⊓ U) ≤ (W i ⊓ W j) ⊓ U := by
      intro x hx
      exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
    have e := congrArg (F.presheaf.map (homOfLE hle).op) (hA i j)
    rw [presheaf_map_map F _ _ inf_le_left, presheaf_map_map F _ _ inf_le_right] at e
    exact e
  exact G.existsUnique_gluing' (fun i => W i ⊓ U) ((⨆ i, W i) ⊓ U)
    (fun i => homOfLE (inf_le_inf_right U (le_iSup W i))) (inf_iSup_le W U) A hcompat

/-- **The twist is a sheaf.** -/
theorem twistPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) (twistPresheaf F U V u).presheaf := by
  change TopCat.Presheaf.IsSheaf (twistPresheafAb F U V u)
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro ι W sf hsf
  have hsf₁ : ∀ i j, F.presheaf.map (homOfLE (inf_le_inf_right U
        (inf_le_left : W i ⊓ W j ≤ W i))).op (sf i).1.1 =
      F.presheaf.map (homOfLE (inf_le_inf_right U (inf_le_right : W i ⊓ W j ≤ W j))).op
        (sf j).1.1 := fun i j => congrArg (fun p => p.1.1) (hsf i j)
  have hsf₂ : ∀ i j, F.presheaf.map (homOfLE (inf_le_inf_right V
        (inf_le_left : W i ⊓ W j ≤ W i))).op (sf i).1.2 =
      F.presheaf.map (homOfLE (inf_le_inf_right V (inf_le_right : W i ⊓ W j ≤ W j))).op
        (sf j).1.2 := fun i j => congrArg (fun p => p.1.2) (hsf i j)
  obtain ⟨a, ha, ha'⟩ := exists_glue F W U (fun i => (sf i).1.1) hsf₁
  obtain ⟨b, hb, hb'⟩ := exists_glue F W V (fun i => (sf i).1.2) hsf₂
  let G : TopCat.Sheaf Ab Y := ⟨F.presheaf, F.isSheaf⟩
  have hcond : TwistCond F U V u (⨆ i, W i) a b := by
    unfold TwistCond
    refine G.eq_of_locally_eq' (fun i => W i ⊓ (U ⊓ V)) _
      (fun i => homOfLE (inf_le_inf_right _ (le_iSup W i))) (inf_iSup_le W (U ⊓ V)) _ _
      (fun i => ?_)
    change F.presheaf.map _ (F.presheaf.map _ b) =
      F.presheaf.map _ (Y.presheaf.map _ (u : Γ(Y, U ⊓ V)) • F.presheaf.map _ a)
    rw [Scheme.Modules.map_smul, ringMap_ringMap _ _ (twist_le₃ U V (W i)),
      presheaf_map_map F _ _ ((twist_le₂ U V (W i)).trans (inf_le_inf_right V (le_iSup W i))),
      presheaf_map_map F _ _ ((twist_le₁ U V (W i)).trans (inf_le_inf_right U (le_iSup W i))),
      ← presheaf_map_map F (inf_le_inf_right V (le_iSup W i)) (twist_le₂ U V (W i)),
      ← presheaf_map_map F (inf_le_inf_right U (le_iSup W i)) (twist_le₁ U V (W i)), ha i, hb i]
    exact (sf i).2
  refine ⟨⟨(a, b), hcond⟩, fun i => ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    exact Prod.ext (ha i) (hb i)
  · apply Subtype.ext
    apply Prod.ext
    · exact ha' s.1.1 (fun i => congrArg (fun p => p.1.1) (hs i))
    · exact hb' s.1.2 (fun i => congrArg (fun p => p.1.2) (hs i))

/-- **The twist** `F_u` of `F` along `(U, V)` by the unit `u` on `U ∩ V` (blueprint
`def:sm-twist`). -/
def twist : Y.Modules where
  val := twistPresheaf F U V u
  isSheaf := twistPresheaf_isSheaf F U V u

lemma twist_presheaf_obj (W : Y.Opens) :
    Γ(twist F U V u, W) = AddCommGrpCat.of (twistSubgroup F U V u W) :=
  rfl

end Construction

section Sections

variable {R : Type u} [CommRing R] (c : R →+* Γ(Y, ⊤))

lemma ringMap_self {W : Y.Opens} (h : W ≤ W) (r : Γ(Y, W)) :
    Y.presheaf.map (homOfLE h).op r = r := by
  rw [show homOfLE h = 𝟙 W from rfl, op_id, Y.presheaf.map_id]
  rfl

/-- Multiplication by a function `g ∈ Γ(W, 𝒪_Y)` on `Γ(W, F)`, as an `R`-linear map. -/
def smulLin {W : Y.Opens} (g : Γ(Y, W)) :
    sectionsModuleCat F c W le_top →ₗ[R] sectionsModuleCat F c W le_top where
  toFun s := (g • (show Γ(F, W) from s) : Γ(F, W))
  map_add' s t := smul_add g (show Γ(F, W) from s) t
  map_smul' r s := smul_comm g (sectionsRingHom c le_top r) (show Γ(F, W) from s)

lemma smulLin_apply {W : Y.Opens} (g : Γ(Y, W)) (s : sectionsModuleCat F c W le_top) :
    smulLin F c g s = (g • (show Γ(F, W) from s) : Γ(F, W)) :=
  rfl

/-! ### Sections over `U`, `V` and `U ∩ V` on raw section groups -/

/-- The `U`-component of a section of the twist over `U`. -/
def twistToU (p : twistSubgroup F U V u U) : Γ(F, U) :=
  F.presheaf.map (homOfLE (le_inf le_rfl le_rfl : U ≤ U ⊓ U)).op p.1.1

/-- The section of the twist over `U` with `U`-component `s`. -/
def twistOfU (s : Γ(F, U)) : twistSubgroup F U V u U :=
  ⟨(F.presheaf.map (homOfLE inf_le_left : U ⊓ U ⟶ U).op s,
    (u : Γ(Y, U ⊓ V)) • F.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op s), by
    change TwistCond F U V u U _ _
    unfold TwistCond
    rw [Scheme.Modules.map_smul, presheaf_map_map F _ _ (twist_le₁ U V U |>.trans inf_le_left),
      presheaf_map_map F _ _ (twist_le₁ U V U |>.trans inf_le_left)]⟩

lemma twistToU_ofU (s : Γ(F, U)) : twistToU F U V u (twistOfU F U V u s) = s :=
  presheaf_map_map_self F _ _ s

lemma twistOfU_toU (p : twistSubgroup F U V u U) : twistOfU F U V u (twistToU F U V u p) = p := by
  have hp : TwistCond F U V u U p.1.1 p.1.2 := p.2
  apply Subtype.ext
  apply Prod.ext
  · exact presheaf_map_map_self F _ _ _
  · change (u : Γ(Y, U ⊓ V)) • F.presheaf.map _ (F.presheaf.map _ p.1.1) = p.1.2
    unfold TwistCond at hp
    have e := congrArg (F.presheaf.map (homOfLE (le_inf inf_le_left le_rfl :
      U ⊓ V ≤ U ⊓ (U ⊓ V))).op) hp
    have h₃ : U ⊓ V ≤ U ⊓ U := le_inf inf_le_left inf_le_left
    rw [presheaf_map_map_self, Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl,
      ringMap_self, presheaf_map_map F _ _ h₃] at e
    rw [presheaf_map_map F _ _ h₃, e]

lemma twistToU_add (p q : twistSubgroup F U V u U) :
    twistToU F U V u (p + q) = twistToU F U V u p + twistToU F U V u q :=
  map_add _ _ _

lemma twistToU_smul (r : Γ(Y, U)) (p : twistSubgroup F U V u U) :
    twistToU F U V u (r • p) = r • twistToU F U V u p := by
  change F.presheaf.map _ (resU U U r • p.1.1) = r • F.presheaf.map _ p.1.1
  rw [Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl, ringMap_self]

/-- The `V`-component of a section of the twist over `V`. -/
def twistToV (p : twistSubgroup F U V u V) : Γ(F, V) :=
  F.presheaf.map (homOfLE (le_inf le_rfl le_rfl : V ≤ V ⊓ V)).op p.1.2

lemma twist_le_VU : V ⊓ U ≤ U ⊓ V := fun _ h => ⟨h.2, h.1⟩

/-- The section of the twist over `V` with `V`-component `s`. -/
def twistOfV (s : Γ(F, V)) : twistSubgroup F U V u V :=
  ⟨(Y.presheaf.map (homOfLE (twist_le_VU U V)).op ((u⁻¹ : Γ(Y, U ⊓ V)ˣ) : Γ(Y, U ⊓ V)) •
      F.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op s,
    F.presheaf.map (homOfLE inf_le_left : V ⊓ V ⟶ V).op s), by
    change TwistCond F U V u V _ _
    unfold TwistCond
    rw [Scheme.Modules.map_smul, ringMap_ringMap, smul_smul, ← map_mul, Units.mul_inv, map_one,
      one_smul, presheaf_map_map F _ _ (twist_le₁ U V V |>.trans inf_le_left),
      presheaf_map_map F _ _ (twist_le₁ U V V |>.trans inf_le_left)]
    exact twist_le₃ U V V⟩

lemma twistToV_ofV (s : Γ(F, V)) : twistToV F U V u (twistOfV F U V u s) = s :=
  presheaf_map_map_self F _ _ s

lemma twistOfV_toV (p : twistSubgroup F U V u V) : twistOfV F U V u (twistToV F U V u p) = p := by
  have hp : TwistCond F U V u V p.1.1 p.1.2 := p.2
  apply Subtype.ext
  apply Prod.ext
  · change Y.presheaf.map _ _ • F.presheaf.map _ (F.presheaf.map _ p.1.2) = p.1.1
    unfold TwistCond at hp
    have e := congrArg (F.presheaf.map (homOfLE (le_inf inf_le_left (twist_le_VU U V) :
      V ⊓ U ≤ V ⊓ (U ⊓ V))).op) hp
    have h₃ : V ⊓ U ≤ V ⊓ V := le_inf inf_le_left inf_le_left
    rw [presheaf_map_map F _ _ h₃, Scheme.Modules.map_smul,
      ringMap_ringMap _ _ (twist_le_VU U V), presheaf_map_map_self] at e
    rw [presheaf_map_map F _ _ h₃, e, smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul]
  · exact presheaf_map_map_self F _ _ _

lemma twistToV_add (p q : twistSubgroup F U V u V) :
    twistToV F U V u (p + q) = twistToV F U V u p + twistToV F U V u q :=
  map_add _ _ _

lemma twistToV_smul (r : Γ(Y, V)) (p : twistSubgroup F U V u V) :
    twistToV F U V u (r • p) = r • twistToV F U V u p := by
  change F.presheaf.map _ (resV V V r • p.1.2) = r • F.presheaf.map _ p.1.2
  rw [Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl, ringMap_self]

/-- The `V`-component of a section of the twist over `U ∩ V`. -/
def twistToUV (p : twistSubgroup F U V u (U ⊓ V)) : Γ(F, U ⊓ V) :=
  F.presheaf.map (homOfLE (le_inf le_rfl inf_le_right : U ⊓ V ≤ U ⊓ V ⊓ V)).op p.1.2

/-- The section of the twist over `U ∩ V` with `V`-component `s`. -/
def twistOfUV (s : Γ(F, U ⊓ V)) : twistSubgroup F U V u (U ⊓ V) :=
  ⟨(Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ⊓ U ≤ U ⊓ V)).op
        ((u⁻¹ : Γ(Y, U ⊓ V)ˣ) : Γ(Y, U ⊓ V)) •
      F.presheaf.map (homOfLE inf_le_left : U ⊓ V ⊓ U ⟶ U ⊓ V).op s,
    F.presheaf.map (homOfLE inf_le_left : U ⊓ V ⊓ V ⟶ U ⊓ V).op s), by
    change TwistCond F U V u (U ⊓ V) _ _
    unfold TwistCond
    rw [Scheme.Modules.map_smul, ringMap_ringMap, smul_smul, ← map_mul, Units.mul_inv, map_one,
      one_smul, presheaf_map_map F _ _ (twist_le₁ U V (U ⊓ V) |>.trans inf_le_left),
      presheaf_map_map F _ _ (twist_le₁ U V (U ⊓ V) |>.trans inf_le_left)]
    exact twist_le₃ U V (U ⊓ V)⟩

lemma twistToUV_ofUV (s : Γ(F, U ⊓ V)) : twistToUV F U V u (twistOfUV F U V u s) = s :=
  presheaf_map_map_self F _ _ s

lemma twistOfUV_toUV (p : twistSubgroup F U V u (U ⊓ V)) :
    twistOfUV F U V u (twistToUV F U V u p) = p := by
  have hp : TwistCond F U V u (U ⊓ V) p.1.1 p.1.2 := p.2
  apply Subtype.ext
  apply Prod.ext
  · change Y.presheaf.map _ _ • F.presheaf.map _ (F.presheaf.map _ p.1.2) = p.1.1
    unfold TwistCond at hp
    have hle : U ⊓ V ⊓ U ≤ U ⊓ V ⊓ (U ⊓ V) := le_inf inf_le_left inf_le_left
    have e := congrArg (F.presheaf.map (homOfLE hle).op) hp
    have h₃ : U ⊓ V ⊓ U ≤ U ⊓ V ⊓ V := le_inf inf_le_left (inf_le_left.trans inf_le_right)
    rw [presheaf_map_map F _ _ h₃, Scheme.Modules.map_smul, ringMap_ringMap _ _ inf_le_left,
      presheaf_map_map_self] at e
    rw [presheaf_map_map F _ _ h₃, e, smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul]
  · exact presheaf_map_map_self F _ _ _

lemma twistToUV_add (p q : twistSubgroup F U V u (U ⊓ V)) :
    twistToUV F U V u (p + q) = twistToUV F U V u p + twistToUV F U V u q :=
  map_add _ _ _

lemma twistToUV_sub (p q : twistSubgroup F U V u (U ⊓ V)) :
    twistToUV F U V u (p - q) = twistToUV F U V u p - twistToUV F U V u q :=
  map_sub _ _ _

lemma twistToUV_smul (r : Γ(Y, U ⊓ V)) (p : twistSubgroup F U V u (U ⊓ V)) :
    twistToUV F U V u (r • p) = r • twistToUV F U V u p := by
  change F.presheaf.map _ (resV V (U ⊓ V) r • p.1.2) = r • F.presheaf.map _ p.1.2
  rw [Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl, ringMap_self]

/-- Restriction of a section of the twist from `V` to `U ∩ V`, in components. -/
lemma twistToUV_restrict_V (p : twistSubgroup F U V u V) :
    twistToUV F U V u (twistRestrict F U V u (inf_le_right : U ⊓ V ≤ V) p) =
      F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (twistToV F U V u p) := by
  change F.presheaf.map _ (F.presheaf.map _ p.1.2) = F.presheaf.map _ (F.presheaf.map _ p.1.2)
  rw [presheaf_map_map F _ _ (le_inf inf_le_right inf_le_right : U ⊓ V ≤ V ⊓ V),
    presheaf_map_map F _ _ (le_inf inf_le_right inf_le_right : U ⊓ V ≤ V ⊓ V)]

/-- Restriction of a section of the twist from `U` to `U ∩ V`, in components: the `V`-component is
`u` times the `U`-component. -/
lemma twistToUV_restrict_U (p : twistSubgroup F U V u U) :
    twistToUV F U V u (twistRestrict F U V u (inf_le_left : U ⊓ V ≤ U) p) =
      (u : Γ(Y, U ⊓ V)) •
        F.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (twistToU F U V u p) := by
  have hp : TwistCond F U V u U p.1.1 p.1.2 := p.2
  change F.presheaf.map _ (F.presheaf.map _ p.1.2) = _ • F.presheaf.map _ (F.presheaf.map _ p.1.1)
  unfold TwistCond at hp
  have e := congrArg (F.presheaf.map (homOfLE (le_inf inf_le_left le_rfl :
    U ⊓ V ≤ U ⊓ (U ⊓ V))).op) hp
  have h₃ : U ⊓ V ≤ U ⊓ U := le_inf inf_le_left inf_le_left
  rw [presheaf_map_map_self, Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl,
    ringMap_self, presheaf_map_map F _ _ h₃] at e
  rw [presheaf_map_map F _ _ le_rfl, presheaf_map_self, presheaf_map_map F _ _ h₃, e]

/-- Sections of the twist over `U` are sections of `F` over `U` (the `U`-component). -/
def twistSecUEquiv :
    sectionsModuleCat (twist F U V u) c U le_top ≃ₗ[R] sectionsModuleCat F c U le_top where
  toFun p := twistToU F U V u p
  invFun s := twistOfU F U V u s
  left_inv := twistOfU_toU F U V u
  right_inv := twistToU_ofU F U V u
  map_add' := twistToU_add F U V u
  map_smul' r p := twistToU_smul F U V u (sectionsRingHom c le_top r) p

/-- Sections of the twist over `V` are sections of `F` over `V` (the `V`-component). -/
def twistSecVEquiv :
    sectionsModuleCat (twist F U V u) c V le_top ≃ₗ[R] sectionsModuleCat F c V le_top where
  toFun p := twistToV F U V u p
  invFun s := twistOfV F U V u s
  left_inv := twistOfV_toV F U V u
  right_inv := twistToV_ofV F U V u
  map_add' := twistToV_add F U V u
  map_smul' r p := twistToV_smul F U V u (sectionsRingHom c le_top r) p

/-- Sections of the twist over `U ∩ V` are sections of `F` over `U ∩ V` (the `V`-component). -/
def twistSecUVEquiv :
    sectionsModuleCat (twist F U V u) c (U ⊓ V) le_top ≃ₗ[R]
      sectionsModuleCat F c (U ⊓ V) le_top where
  toFun p := twistToUV F U V u p
  invFun s := twistOfUV F U V u s
  left_inv := twistOfUV_toUV F U V u
  right_inv := twistToUV_ofUV F U V u
  map_add' := twistToUV_add F U V u
  map_smul' r p := twistToUV_smul F U V u (sectionsRingHom c le_top r) p

/-- The restriction `Γ(U, F) → Γ(U ∩ V, F)` as an `R`-linear map. -/
abbrev resUV : sectionsModuleCat F c U le_top →ₗ[R] sectionsModuleCat F c (U ⊓ V) le_top :=
  (sectionsRestrict F c le_top le_top inf_le_left).hom

/-- The restriction `Γ(V, F) → Γ(U ∩ V, F)` as an `R`-linear map. -/
abbrev resVU : sectionsModuleCat F c V le_top →ₗ[R] sectionsModuleCat F c (U ⊓ V) le_top :=
  (sectionsRestrict F c le_top le_top inf_le_right).hom

/-- Under the identifications of sections, the Čech differential of the twist is the twisted
differential `(a, b) ↦ b| - u · a|`. -/
lemma twistSecUVEquiv_pairDiff (p : sectionsModuleCat (twist F U V u) c U le_top ×
    sectionsModuleCat (twist F U V u) c V le_top) :
    twistSecUVEquiv F U V u c (pairDiff U V (twist F U V u) c p) =
      twistDiff (resUV F U V c) (resVU F U V c) (smulLin F c (u : Γ(Y, U ⊓ V)))
        ((twistSecUEquiv F U V u c).prodCongr (twistSecVEquiv F U V u c) p) := by
  obtain ⟨pU, pV⟩ := p
  have h1 := twistToUV_restrict_V F U V u pV
  have h2 := twistToUV_restrict_U F U V u pU
  change twistToUV F U V u (twistRestrict F U V u (inf_le_right : U ⊓ V ≤ V) pV -
      twistRestrict F U V u (inf_le_left : U ⊓ V ≤ U) pU) = _
  refine (twistToUV_sub F U V u _ _).trans ?_
  rw [h1, h2]
  rfl

/-- **`Ȟ¹` of the twist**: `Ȟ¹((U, V), F_u) ≃ Γ(U ∩ V, F) ⧸ {b| - u · a|}`. -/
def cechTwistOneEquiv :
    cechCohomology (twist F U V u) (pairCover U V) c 1 ≃ₗ[R]
      H1 (resUV F U V c) (resVU F U V c) (smulLin F c (u : Γ(Y, U ⊓ V))) :=
  (cechPairOneEquiv U V (twist F U V u) c).trans
    (Submodule.Quotient.equiv _ _ (twistSecUVEquiv F U V u c) (by
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_range]
      constructor
      · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
        exact ⟨_, (twistSecUVEquiv_pairDiff F U V u c p).symm⟩
      · rintro ⟨q, rfl⟩
        refine ⟨_, ⟨((twistSecUEquiv F U V u c).prodCongr (twistSecVEquiv F U V u c)).symm q,
          rfl⟩, ?_⟩
        change twistSecUVEquiv F U V u c (pairDiff U V (twist F U V u) c _) = _
        rw [twistSecUVEquiv_pairDiff, LinearEquiv.apply_symm_apply]))

/-- **`Ȟ⁰` of the twist**: `Ȟ⁰((U, V), F_u) ≃ {(a, b) | b| = u · a|}`. -/
def cechTwistZeroEquiv :
    cechCohomology (twist F U V u) (pairCover U V) c 0 ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (smulLin F c (u : Γ(Y, U ⊓ V))) :=
  (cechPairZeroEquiv U V (twist F U V u) c).trans
    (((twistSecUEquiv F U V u c).prodCongr (twistSecVEquiv F U V u c)).ofSubmodules _ _ (by
      ext q
      simp only [Submodule.mem_map, LinearMap.mem_ker]
      constructor
      · rintro ⟨p, hp, rfl⟩
        change twistDiff _ _ _ (((twistSecUEquiv F U V u c).prodCongr
          (twistSecVEquiv F U V u c)) p) = 0
        rw [← twistSecUVEquiv_pairDiff, hp, map_zero]
      · intro hq
        refine ⟨((twistSecUEquiv F U V u c).prodCongr (twistSecVEquiv F U V u c)).symm q, ?_,
          by simp⟩
        apply (twistSecUVEquiv F U V u c).injective
        rw [twistSecUVEquiv_pairDiff, LinearEquiv.apply_symm_apply, hq, map_zero]))

lemma smulLin_one {W : Y.Opens} : smulLin F c (1 : Γ(Y, W)) = LinearMap.id :=
  LinearMap.ext fun s => (fun x : Γ(F, W) => one_smul Γ(Y, W) x) s

/-- The Čech differential of `F` itself is the untwisted differential. -/
lemma pairDiff_eq_twistDiff :
    pairDiff U V F c = twistDiff (resUV F U V c) (resVU F U V c) (smulLin F c 1) := by
  rw [smulLin_one]
  rfl

/-- `Ȟ¹((U, V), F) ≃ H1 ρU ρV id`. -/
def cechOneEquivH1 :
    cechCohomology F (pairCover U V) c 1 ≃ₗ[R]
      H1 (resUV F U V c) (resVU F U V c) (smulLin F c 1) :=
  (cechPairOneEquiv U V F c).trans
    (Submodule.quotEquivOfEq _ _ (by rw [pairDiff_eq_twistDiff]))

/-- `Ȟ⁰((U, V), F) ≃ H0 ρU ρV id`. -/
def cechZeroEquivH0 :
    cechCohomology F (pairCover U V) c 0 ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (smulLin F c 1) :=
  (cechPairZeroEquiv U V F c).trans (LinearEquiv.ofEq _ _ (by rw [pairDiff_eq_twistDiff]))

/-! ### Global sections of the twist -/

lemma top_inf_le (W : Y.Opens) : W ≤ ⊤ ⊓ W := le_inf le_top le_rfl

/-- A global section of the twist gives a compatible pair of sections over `U` and `V`. -/
lemma twistGlobal_cond (p : twistSubgroup F U V u ⊤) :
    F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
        (F.presheaf.map (homOfLE (top_inf_le V)).op p.1.2) =
      (u : Γ(Y, U ⊓ V)) • F.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
        (F.presheaf.map (homOfLE (top_inf_le U)).op p.1.1) := by
  have hp : TwistCond F U V u ⊤ p.1.1 p.1.2 := p.2
  unfold TwistCond at hp
  have e := congrArg (F.presheaf.map (homOfLE (top_inf_le (U ⊓ V))).op) hp
  rw [presheaf_map_map F _ _ ((inf_le_right : U ⊓ V ≤ V).trans (top_inf_le V)),
    Scheme.Modules.map_smul, ringMap_ringMap _ _ le_rfl, ringMap_self,
    presheaf_map_map F _ _ ((inf_le_left : U ⊓ V ≤ U).trans (top_inf_le U))] at e
  rw [presheaf_map_map F _ _ ((inf_le_right : U ⊓ V ≤ V).trans (top_inf_le V)),
    presheaf_map_map F _ _ ((inf_le_left : U ⊓ V ≤ U).trans (top_inf_le U)), e]

lemma twistGlobal_smul_fst (r : Γ(Y, ⊤)) (p : twistSubgroup F U V u ⊤) :
    F.presheaf.map (homOfLE (top_inf_le U)).op (r • p).1.1 =
      Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r •
        F.presheaf.map (homOfLE (top_inf_le U)).op p.1.1 := by
  change F.presheaf.map _ (resU U ⊤ r • p.1.1) = _
  rw [Scheme.Modules.map_smul, ringMap_ringMap]

lemma twistGlobal_smul_snd (r : Γ(Y, ⊤)) (p : twistSubgroup F U V u ⊤) :
    F.presheaf.map (homOfLE (top_inf_le V)).op (r • p).1.2 =
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r •
        F.presheaf.map (homOfLE (top_inf_le V)).op p.1.2 := by
  change F.presheaf.map _ (resV V ⊤ r • p.1.2) = _
  rw [Scheme.Modules.map_smul, ringMap_ringMap]

lemma twistGlobal_smul_fst' (x : Γ(Y, ⊤)) (p : twistSubgroup F U V u ⊤) :
    F.presheaf.map (homOfLE (top_inf_le U)).op
        ((Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op x) • p).1.1 =
      Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x •
        F.presheaf.map (homOfLE (top_inf_le U)).op p.1.1 := by
  rw [twistGlobal_smul_fst, ringMap_ringMap]

lemma twistGlobal_smul_snd' (x : Γ(Y, ⊤)) (p : twistSubgroup F U V u ⊤) :
    F.presheaf.map (homOfLE (top_inf_le V)).op
        ((Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op x) • p).1.2 =
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op x •
        F.presheaf.map (homOfLE (top_inf_le V)).op p.1.2 := by
  rw [twistGlobal_smul_snd, ringMap_ringMap]

/-- A compatible pair gives a global section of the twist. -/
def twistGlobalOfPair (a : Γ(F, U)) (b : Γ(F, V))
    (h : F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b =
      (u : Γ(Y, U ⊓ V)) • F.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) :
    twistSubgroup F U V u ⊤ :=
  ⟨(F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ U ≤ U)).op a,
    F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op b), by
    change TwistCond F U V u ⊤ _ _
    unfold TwistCond
    have e := congrArg (F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ (U ⊓ V) ≤ U ⊓ V)).op) h
    rw [presheaf_map_map F _ _ ((twist_le₂ U V ⊤).trans inf_le_right), Scheme.Modules.map_smul,
      presheaf_map_map F _ _ ((twist_le₁ U V ⊤).trans inf_le_right)] at e
    rw [presheaf_map_map F _ _ ((twist_le₂ U V ⊤).trans inf_le_right),
      presheaf_map_map F _ _ ((twist_le₁ U V ⊤).trans inf_le_right), e]⟩

/-- **Global sections of the twist** are the pairs `(a, b) ∈ Γ(U, F) × Γ(V, F)` with
`b| = u · a|`, i.e. `H⁰` of the twisted two-term complex. -/
def twistGlobalEquiv :
    sectionsModuleCat (twist F U V u) c ⊤ le_top ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (smulLin F c (u : Γ(Y, U ⊓ V))) where
  toFun p := ⟨(F.presheaf.map (homOfLE (top_inf_le U)).op (p : twistSubgroup F U V u ⊤).1.1,
      F.presheaf.map (homOfLE (top_inf_le V)).op (p : twistSubgroup F U V u ⊤).1.2), by
    rw [LinearMap.mem_ker, twistDiff_apply, sub_eq_zero]
    exact twistGlobal_cond F U V u p⟩
  invFun q := twistGlobalOfPair F U V u q.1.1 q.1.2 (by
    have hq := q.2
    rw [LinearMap.mem_ker, twistDiff_apply, sub_eq_zero] at hq
    exact hq)
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact presheaf_map_map_self F _ _ _
    · exact presheaf_map_map_self F _ _ _
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact presheaf_map_map_self F _ _ _
    · exact presheaf_map_map_self F _ _ _
  map_add' p q := by
    apply Subtype.ext
    exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' r p := by
    apply Subtype.ext
    apply Prod.ext
    · exact twistGlobal_smul_fst' F U V u (c r) p
    · exact twistGlobal_smul_snd' F U V u (c r) p

end Sections

end

end DeJongAlterations.StableModification.CurvesField

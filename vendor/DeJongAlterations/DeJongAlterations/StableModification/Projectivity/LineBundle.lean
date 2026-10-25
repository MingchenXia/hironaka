/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.StableModification.Cohomology.CechCover
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Line-bundle data, twists, fibre-ampleness and local projectivity

This file publishes the three interface definitions of the projectivity route (PLAN-OM3 §4,
blueprint `sm-projectivity-core.tex`) for Temkin's Theorem 1.1 (M. Temkin, *Stable modification
of relative curves*, J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification/
source/semi-stable.tex`, T:1713–1749): projectivity of the stable modification, proved by a
finite map to `ℙᴺ` and a local-to-global theorem.

Mathlib has no line bundles and no tensor products of `𝒪_X`-modules, so a line bundle is given
by a *cocycle*:

* `LineBundleData X` (blueprint `def:sm-lbd`): opens `U i` covering `X` and units
  `u i j ∈ Γ(U i ∩ U j, 𝒪_X)ˣ` with `u i j · u j k = u i k` on `U i ∩ U j ∩ U k`. The intended
  line bundle `𝓛` has a generator `e i` on `U i` with `e j = u i j · e i` on `U i ∩ U j`.
* `LineBundleData.twist L F m` (blueprint `def:sm-lbd-twist`): the module `F ⊗ 𝓛^{⊗ m}`
  (`m ∈ ℤ`) for an arbitrary `𝒪_X`-module `F`. Its sections over `W` are the families
  `t i ∈ Γ(W ∩ U i, F)` with `t i = (u i j)^m · t j` on `W ∩ U i ∩ U j` (the coefficients of a
  section `s = t i · e i^m`). It is a sheaf (`twistPresheaf_isSheaf`).
* `LineBundleData.pullback L f`: the pulled-back cocycle on `f⁻¹ U i`.
* `IsGloballyGenerated M`: the germs of global sections generate every stalk of `M`.
* `FiberAmple L β y` (Serre's cohomological ampleness on the scheme-theoretic fibre
  `X_y = β⁻¹(y)`; EGA III 2.2.1, Hartshorne III.5.3): for every quasi-coherent `F` of finite
  type on `X_y` and all `m ≫ 0`, `Ȟ¹(𝒰, F ⊗ 𝓛^m|_{X_y}) = 0` for every finite affine cover `𝒰`
  of `X_y`, and `F ⊗ 𝓛^m|_{X_y}` is globally generated.
* `LocallyRelativelyProjective pY β`: `β : X ⟶ Y` is relatively projective over the members of a
  finite open cover of `Y`.

## Design notes

* The cover is arbitrary (no affineness, no finiteness): this makes `pullback` (along any
  morphism), products and powers immediate, and quasi-coherence of the twist is local
  (`F ⊗ 𝓛^m|_{U i} ≅ F|_{U i}`).
* `FiberAmple` asks for vanishing *and* generation for *all* coherent `F`, not only for `F = 𝒪`:
  the weaker form ("`H¹(X_y, 𝓛^m) = 0` and `𝓛^m|_{X_y}` generated for `m ≫ 0`", PLAN-OM3 §4 draft)
  holds for `𝓛 = 𝒪` on any tree of rational curves, so it cannot detect positivity on contracted
  curves, and the local-to-global theorem fails with it (Hironaka's non-projective modification
  of `ℙ³`, which is projective over the two members of an open cover, with `𝓛 = 𝒪`).
* For a proper `β` the fibre `X_y` is proper over `κ(y)`, so finite affine covers exist
  (`Cohomology.FiniteAffineCover.nonempty`) and for quasi-coherent modules the condition does not
  depend on the cover (`Cohomology.cohomologyIsoCech`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {X Y : Scheme.{u}}

/-- Restriction of functions `Γ(X, W) → Γ(X, V)` along `V ≤ W`, as a ring homomorphism. -/
abbrev res {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma res_res {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (h₃ : V₃ ≤ V₁)
    (r : Γ(X, V₁)) : res h₂ (res h₁ r) = res h₃ r := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op) r = _
  rw [← Functor.map_comp]
  rfl

lemma res_self {V : X.Opens} (h : V ≤ V) (r : Γ(X, V)) : res h r = r := by
  change X.presheaf.map (𝟙 _) r = r
  rw [X.presheaf.map_id]
  rfl

/-- **Line-bundle data** (blueprint `def:sm-lbd`): a cover of `X` by opens `U i` with transition
units `u i j ∈ Γ(U i ∩ U j, 𝒪_X)ˣ` satisfying the cocycle condition `u i j · u j k = u i k` on
`U i ∩ U j ∩ U k`. The associated line bundle has generators `e i` on `U i` with
`e j = u i j · e i` on overlaps. -/
structure LineBundleData (X : Scheme.{u}) where
  /-- The index type of the trivializing cover. -/
  ι : Type u
  /-- The trivializing opens. -/
  U : ι → X.Opens
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The transition units: `e j = u i j · e i` on `U i ∩ U j`. -/
  u : ∀ i j, Γ(X, U i ⊓ U j)ˣ
  cocycle : ∀ i j k,
    res (inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j) (u i j : Γ(X, U i ⊓ U j)) *
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k)
          (u j k : Γ(X, U j ⊓ U k)) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k)
        (u i k : Γ(X, U i ⊓ U k))

namespace LineBundleData

variable (L : LineBundleData X)

/-- The transition unit `u i j` restricted to an open `V ⊆ U i ∩ U j`. -/
def trans {i j : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U j) : Γ(X, V)ˣ :=
  Units.map (res h).toMonoidHom (L.u i j)

lemma coe_trans {i j : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U j) :
    (L.trans h : Γ(X, V)) = res h (L.u i j : Γ(X, L.U i ⊓ L.U j)) :=
  rfl

lemma res_trans {i j : L.ι} {V V' : X.Opens} (h : V ≤ L.U i ⊓ L.U j) (h' : V' ≤ V) :
    res h' (L.trans h : Γ(X, V)) = (L.trans (h'.trans h) : Γ(X, V')) :=
  res_res _ _ _ _

lemma res_trans_zpow {i j : L.ι} {V V' : X.Opens} (h : V ≤ L.U i ⊓ L.U j) (h' : V' ≤ V)
    (m : ℤ) :
    res h' ((L.trans h ^ m : Γ(X, V)ˣ) : Γ(X, V)) = ((L.trans (h'.trans h) ^ m : Γ(X, V')ˣ) :
      Γ(X, V')) := by
  have : Units.map (res h').toMonoidHom (L.trans h) = L.trans (h'.trans h) :=
    Units.ext (L.res_trans h h')
  rw [← this, ← map_zpow]
  rfl

/-- The cocycle condition on any open `V ⊆ U i ∩ U j ∩ U k`. -/
lemma trans_mul_trans {i j k : L.ι} {V : X.Opens} (h₁ : V ≤ L.U i ⊓ L.U j)
    (h₂ : V ≤ L.U j ⊓ L.U k) (h₃ : V ≤ L.U i ⊓ L.U k) :
    L.trans h₁ * L.trans h₂ = L.trans h₃ := by
  have hV : V ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  apply Units.ext
  have e := congrArg (res hV) (L.cocycle i j k)
  rw [map_mul, res_res, res_res, res_res] at e
  exact e

lemma trans_self {i : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U i) : L.trans h = 1 := by
  have e := L.trans_mul_trans h h h
  exact mul_eq_left.mp e

lemma trans_symm {i j : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U j) (h' : V ≤ L.U j ⊓ L.U i) :
    L.trans h' = (L.trans h)⁻¹ := by
  have e := L.trans_mul_trans h h' (le_inf (h.trans inf_le_left) (h.trans inf_le_left))
  rw [L.trans_self] at e
  exact eq_inv_of_mul_eq_one_right e

lemma trans_congr {i j : L.ι} {V : X.Opens} (h h' : V ≤ L.U i ⊓ L.U j) :
    L.trans h = L.trans h' :=
  rfl

/-! ### The twist `F ⊗ 𝓛^m` -/

section Twist

variable (F : X.Modules) (m : ℤ)

lemma le_left (W : X.Opens) (i j : L.ι) : W ⊓ (L.U i ⊓ L.U j) ≤ W ⊓ L.U i :=
  inf_le_inf_left _ inf_le_left

lemma le_right (W : X.Opens) (i j : L.ι) : W ⊓ (L.U i ⊓ L.U j) ≤ W ⊓ L.U j :=
  inf_le_inf_left _ inf_le_right

/-- The transition unit `(u i j)^m` on `W ∩ U i ∩ U j`, as a function. -/
abbrev transPow (W : X.Opens) (i j : L.ι) : Γ(X, W ⊓ (L.U i ⊓ L.U j)) :=
  ((L.trans (inf_le_right : W ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j) ^ m :
    Γ(X, W ⊓ (L.U i ⊓ L.U j))ˣ) : Γ(X, W ⊓ (L.U i ⊓ L.U j)))

/-- The compatibility condition `t i = (u i j)^m · t j` on `W ∩ U i ∩ U j` for the local
coefficients of a section of `F ⊗ 𝓛^m` over `W`. -/
def IsCompatible (W : X.Opens) (t : ∀ i, Γ(F, W ⊓ L.U i)) : Prop :=
  ∀ i j, F.presheaf.map (homOfLE (L.le_left W i j)).op (t i) =
    L.transPow m W i j • F.presheaf.map (homOfLE (L.le_right W i j)).op (t j)

/-- The sections of `F ⊗ 𝓛^m` over `W`: compatible families of local coefficients. -/
def twistSubgroup (W : X.Opens) : AddSubgroup (∀ i, Γ(F, W ⊓ L.U i)) where
  carrier := {t | L.IsCompatible F m W t}
  zero_mem' := by
    intro i j
    change F.presheaf.map _ (0 : Γ(F, W ⊓ L.U i)) = _ • F.presheaf.map _ (0 : Γ(F, W ⊓ L.U j))
    rw [map_zero, map_zero, smul_zero]
  add_mem' := by
    intro s t hs ht i j
    change F.presheaf.map _ (s i + t i) = _ • F.presheaf.map _ (s j + t j)
    rw [map_add, map_add, smul_add, hs i j, ht i j]
  neg_mem' := by
    intro s hs i j
    change F.presheaf.map _ (-s i) = _ • F.presheaf.map _ (-s j)
    rw [map_neg, map_neg, smul_neg, hs i j]

variable {L F m} in
lemma mem_twistSubgroup {W : X.Opens} (t : ∀ i, Γ(F, W ⊓ L.U i)) :
    t ∈ L.twistSubgroup F m W ↔ L.IsCompatible F m W t :=
  Iff.rfl

lemma isCompatible_smul {W : X.Opens} (r : Γ(X, W)) {t : ∀ i, Γ(F, W ⊓ L.U i)}
    (ht : L.IsCompatible F m W t) :
    L.IsCompatible F m W (fun i => res (inf_le_left : W ⊓ L.U i ≤ W) r • t i) := by
  intro i j
  simp only
  rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, ht i j, smul_comm]
  have e : (X.presheaf.map (homOfLE (L.le_left W i j)).op) (res (inf_le_left : W ⊓ L.U i ≤ W) r) =
      (X.presheaf.map (homOfLE (L.le_right W i j)).op) (res (inf_le_left : W ⊓ L.U j ≤ W) r) :=
    (res_res _ _ inf_le_left r).trans (res_res _ _ inf_le_left r).symm
  rw [e]

instance (W : X.Opens) : SMul Γ(X, W) (L.twistSubgroup F m W) where
  smul r t := ⟨fun i => res (inf_le_left : W ⊓ L.U i ≤ W) r • t.1 i,
    L.isCompatible_smul F m r t.2⟩

lemma twist_smul_val {W : X.Opens} (r : Γ(X, W)) (t : L.twistSubgroup F m W) (i : L.ι) :
    (r • t).1 i = res (inf_le_left : W ⊓ L.U i ≤ W) r • t.1 i :=
  rfl

/-- The inclusion of the sections of the twist into the product of the `Γ(X, W)`-modules
`Γ(W ∩ U i, F)`. -/
def twistIncl (W : X.Opens) : L.twistSubgroup F m W →+
    (∀ i, Cohomology.sectionsModuleCat F (RingHom.id Γ(X, W)) (W ⊓ L.U i) inf_le_left) where
  toFun t := fun i => t.1 i
  map_zero' := rfl
  map_add' _ _ := rfl

instance (W : X.Opens) : Module Γ(X, W) (L.twistSubgroup F m W) :=
  Function.Injective.module Γ(X, W) (L.twistIncl F m W)
    (fun _ _ h => Subtype.ext (funext fun i => congrFun h i)) (fun _ _ => rfl)

/-- Restriction of sections of the twist along `W' ≤ W`. -/
def twistRestrict {W W' : X.Opens} (h : W' ≤ W) :
    L.twistSubgroup F m W →+ L.twistSubgroup F m W' where
  toFun t := ⟨fun i => F.presheaf.map (homOfLE (inf_le_inf_right (L.U i) h)).op (t.1 i), by
    intro i j
    have ht := t.2 i j
    have hle : W' ⊓ (L.U i ⊓ L.U j) ≤ W ⊓ (L.U i ⊓ L.U j) := inf_le_inf_right _ h
    have e := congrArg (F.presheaf.map (homOfLE hle).op) ht
    rw [Cohomology.presheaf_map_map F _ _ ((L.le_left W' i j).trans
        (inf_le_inf_right (L.U i) h)), Scheme.Modules.map_smul,
      Cohomology.presheaf_map_map F _ _ ((L.le_right W' i j).trans
        (inf_le_inf_right (L.U j) h))] at e
    rw [Cohomology.presheaf_map_map F _ _ ((L.le_left W' i j).trans
        (inf_le_inf_right (L.U i) h)),
      Cohomology.presheaf_map_map F _ _ ((L.le_right W' i j).trans
        (inf_le_inf_right (L.U j) h)), e]
    congr 1
    exact L.res_trans_zpow _ hle m⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    exact map_zero _
  map_add' _ _ := by
    apply Subtype.ext
    funext i
    exact map_add _ _ _

@[simp]
lemma twistRestrict_apply {W W' : X.Opens} (h : W' ≤ W) (t : L.twistSubgroup F m W) (i : L.ι) :
    (L.twistRestrict F m h t).1 i =
      F.presheaf.map (homOfLE (inf_le_inf_right (L.U i) h)).op (t.1 i) :=
  rfl

lemma twistRestrict_smul {W W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W))
    (t : L.twistSubgroup F m W) :
    L.twistRestrict F m h (r • t) = res h r • L.twistRestrict F m h t := by
  apply Subtype.ext
  funext i
  change F.presheaf.map _ (res _ r • t.1 i) = res _ (res h r) • F.presheaf.map _ (t.1 i)
  rw [Scheme.Modules.map_smul]
  congr 1
  change res _ (res _ r) = _
  rw [res_res _ _ (inf_le_left.trans h), res_res]

/-- The twist as a presheaf of abelian groups. -/
def twistPresheafAb : (X.Opens)ᵒᵖ ⥤ Ab where
  obj W := AddCommGrpCat.of (L.twistSubgroup F m W.unop)
  map {W W'} i := AddCommGrpCat.ofHom (L.twistRestrict F m (leOfHom i.unop))
  map_id W := by
    ext t i
    change F.presheaf.map (homOfLE _).op (t.1 i) = t.1 i
    rw [show (homOfLE _ : W.unop ⊓ L.U i ⟶ W.unop ⊓ L.U i) = 𝟙 _ from rfl, op_id,
      F.presheaf.map_id]
    rfl
  map_comp {W W' W''} i j := by
    ext t k
    change F.presheaf.map _ (t.1 k) = F.presheaf.map _ (F.presheaf.map _ (t.1 k))
    exact (Cohomology.presheaf_map_map F _ _ _ _).symm

instance (W : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj W) ((L.twistPresheafAb F m).obj W) :=
  inferInstanceAs (Module Γ(X, W.unop) (L.twistSubgroup F m W.unop))

/-- The twist as a presheaf of modules. -/
def twistPresheaf : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (L.twistPresheafAb F m) (fun {_ _} i r t =>
    L.twistRestrict_smul F m (leOfHom i.unop) r t)

lemma iSup_inf_le {κ : Type*} (W : κ → X.Opens) (V : X.Opens) :
    (⨆ k, W k) ⊓ V ≤ ⨆ k, (W k ⊓ V) := by
  rw [iSup_inf_eq]

/-- Gluing of sections of `F` over the opens `W k ⊓ V`. -/
lemma exists_glue {κ : Type u} (W : κ → X.Opens) (V : X.Opens) (A : ∀ k, Γ(F, W k ⊓ V))
    (hA : ∀ k l, F.presheaf.map (homOfLE (inf_le_inf_right V
        (inf_le_left : W k ⊓ W l ≤ W k))).op (A k) =
      F.presheaf.map (homOfLE (inf_le_inf_right V (inf_le_right : W k ⊓ W l ≤ W l))).op (A l)) :
    ∃! a : Γ(F, (⨆ k, W k) ⊓ V), ∀ k,
      F.presheaf.map (homOfLE (inf_le_inf_right V (le_iSup W k))).op a = A k := by
  let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible G.1 (fun k => W k ⊓ V) A := by
    intro k l
    have hle : (W k ⊓ V) ⊓ (W l ⊓ V) ≤ (W k ⊓ W l) ⊓ V := by
      intro x hx
      exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
    have e := congrArg (F.presheaf.map (homOfLE hle).op) (hA k l)
    rw [Cohomology.presheaf_map_map F _ _ inf_le_left,
      Cohomology.presheaf_map_map F _ _ inf_le_right] at e
    exact e
  exact G.existsUnique_gluing' (fun k => W k ⊓ V) ((⨆ k, W k) ⊓ V)
    (fun k => homOfLE (inf_le_inf_right V (le_iSup W k))) (iSup_inf_le W V) A hcompat

/-- **The twist is a sheaf.** -/
theorem twistPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (L.twistPresheaf F m).presheaf := by
  change TopCat.Presheaf.IsSheaf (L.twistPresheafAb F m)
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro κ W sf hsf
  have hsf' : ∀ i k l, F.presheaf.map (homOfLE (inf_le_inf_right (L.U i)
        (inf_le_left : W k ⊓ W l ≤ W k))).op ((sf k).1 i) =
      F.presheaf.map (homOfLE (inf_le_inf_right (L.U i) (inf_le_right : W k ⊓ W l ≤ W l))).op
        ((sf l).1 i) := fun i k l => congrFun (congrArg Subtype.val (hsf k l)) i
  choose a ha ha' using fun i => exists_glue F W (L.U i) (fun k => (sf k).1 i) (hsf' i)
  let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hcond : L.IsCompatible F m (⨆ k, W k) a := by
    intro i j
    refine G.eq_of_locally_eq' (fun k => W k ⊓ (L.U i ⊓ L.U j)) _
      (fun k => homOfLE (inf_le_inf_right _ (le_iSup W k))) (iSup_inf_le W _) _ _
      (fun k => ?_)
    have hk := (sf k).2 i j
    change F.presheaf.map _ (F.presheaf.map _ (a i)) =
      F.presheaf.map _ (L.transPow m (⨆ k, W k) i j • F.presheaf.map _ (a j))
    rw [Scheme.Modules.map_smul,
      Cohomology.presheaf_map_map F _ _ ((L.le_left (W k) i j).trans
        (inf_le_inf_right (L.U i) (le_iSup W k))),
      Cohomology.presheaf_map_map F _ _ ((L.le_right (W k) i j).trans
        (inf_le_inf_right (L.U j) (le_iSup W k))),
      ← Cohomology.presheaf_map_map F (inf_le_inf_right (L.U i) (le_iSup W k)) (L.le_left (W k) i j),
      ← Cohomology.presheaf_map_map F (inf_le_inf_right (L.U j) (le_iSup W k))
        (L.le_right (W k) i j), ha i k, ha j k]
    rw [hk]
    congr 1
    exact (L.res_trans_zpow _ _ m).symm
  refine ⟨⟨a, hcond⟩, fun k => ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    funext i
    exact ha i k
  · apply Subtype.ext
    funext i
    exact ha' i (s.1 i) (fun k => congrFun (congrArg Subtype.val (hs k)) i)

/-- **The twist** `F ⊗ 𝓛^{⊗ m}` of a module `F` by the `m`-th power of the line bundle of `L`
(blueprint `def:sm-lbd-twist`). Its sections over `W` are the families `t i ∈ Γ(W ∩ U i, F)`
with `t i = (u i j)^m · t j` on `W ∩ U i ∩ U j`. -/
def twist : X.Modules where
  val := L.twistPresheaf F m
  isSheaf := L.twistPresheaf_isSheaf F m

lemma twist_presheaf_obj (W : X.Opens) :
    Γ(L.twist F m, W) = AddCommGrpCat.of (L.twistSubgroup F m W) :=
  rfl

end Twist

/-! ### Pullback -/

section Pullback

variable {X' : Scheme.{u}} (f : X' ⟶ X)

lemma app_res {V W : X.Opens} (h : V ≤ W) (r : Γ(X, W)) :
    f.app V (res h r) = res (f.preimage_mono h) (f.app W r) := by
  change (X.presheaf.map (homOfLE h).op ≫ f.app V) r =
    (f.app W ≫ X'.presheaf.map (homOfLE (f.preimage_mono h)).op) r
  rw [f.naturality]
  rfl

/-- The pullback `f^* 𝓛` of line-bundle data along a morphism `f : X' ⟶ X`: the cover
`f⁻¹ U i` with the transition units `f^♯ (u i j)`. -/
def pullback : LineBundleData X' where
  ι := L.ι
  U i := f ⁻¹ᵁ L.U i
  iSup_eq_top := f.iSup_preimage_eq_top L.iSup_eq_top
  u i j := Units.map ((f.app (L.U i ⊓ L.U j)).hom.toMonoidHom :
    Γ(X, L.U i ⊓ L.U j) →* Γ(X', f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)) (L.u i j)
  cocycle i j k := by
    have h := congrArg (f.app (L.U i ⊓ L.U j ⊓ L.U k)) (L.cocycle i j k)
    rw [map_mul, app_res, app_res, app_res] at h
    exact h

@[simp]
lemma pullback_U (i : L.ι) : (L.pullback f).U i = f ⁻¹ᵁ L.U i :=
  rfl

lemma coe_pullback_u (i j : L.ι) :
    ((L.pullback f).u i j : Γ(X', (L.pullback f).U i ⊓ (L.pullback f).U j)) =
      f.app (L.U i ⊓ L.U j) (L.u i j : Γ(X, L.U i ⊓ L.U j)) :=
  rfl

end Pullback

end LineBundleData

/-! ### Global generation -/

/-- A module `M` is *generated by its global sections*: every local section is, near each point
of its domain, a `𝒪`-linear combination of restrictions of global sections (equivalently, the
germs of global sections generate every stalk `M_x` over `𝒪_{X,x}`). -/
def IsGloballyGenerated (M : X.Modules) : Prop :=
  ∀ (W : X.Opens) (s : Γ(M, W)) (x : X), x ∈ W → ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧
    M.presheaf.map (homOfLE hVW).op s ∈
      Submodule.span Γ(X, V) (Set.range fun t : Γ(M, ⊤) => M.presheaf.map (homOfLE le_top).op t)

/-! ### Fibre-ampleness -/

/-- **Fibre-ampleness** of the line bundle `𝓛` of `L` along `β : X ⟶ Y` at `y ∈ Y` (Serre's
cohomological criterion on the scheme-theoretic fibre `X_y = β⁻¹(y)`, EGA III 2.2.1, Hartshorne
III.5.3): for every quasi-coherent `𝒪_{X_y}`-module `F` of finite type there is `m₀` such that for
all `m ≥ m₀` the module `F ⊗ 𝓛^m|_{X_y}` has vanishing first Čech cohomology for every finite
affine cover of `X_y` and is generated by its global sections.

For a proper `β` the fibre is proper over `κ(y)`, so finite affine covers exist and, for
quasi-coherent modules, the vanishing does not depend on the cover. -/
def FiberAmple (L : LineBundleData X) (β : X ⟶ Y) (y : Y) : Prop :=
  ∀ (F : (β.fiber y).Modules) [F.IsQuasicoherent] [F.IsFiniteType], ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    (∀ 𝒰 : Cohomology.FiniteAffineCover (β.fiber y),
      IsZero (Cohomology.cechCohomology ((L.pullback (β.fiberι y)).twist F m) 𝒰.U
        (RingHom.id Γ(β.fiber y, ⊤)) 1)) ∧
    IsGloballyGenerated ((L.pullback (β.fiberι y)).twist F m)

/-! ### Local projectivity -/

/-- `β : X ⟶ Y` is *locally relatively projective* over `pY : Y ⟶ Spec k`: there is a finite open
cover `Y = ⋃ W j` such that each restriction `β⁻¹(W j) ⟶ W j` is projective relative to
`W j ⟶ Y ⟶ Spec k` (PLAN-OM3 §3, input of the local-to-global theorem). -/
def LocallyRelativelyProjective {k : Type u} [CommRing k] (pY : Y ⟶ Spec (.of k))
    (β : X ⟶ Y) : Prop :=
  ∃ (J : Type u) (_ : Finite J) (W : J → Y.Opens), ⨆ j, W j = ⊤ ∧
    ∀ j, DeJong.IsRelativelyProjective ((W j).ι ≫ pY) (β ∣_ W j)

end

end DeJongAlterations.StableModification.Projectivity

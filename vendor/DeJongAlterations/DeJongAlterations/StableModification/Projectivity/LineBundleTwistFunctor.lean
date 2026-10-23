/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleOps

/-!
# Twisting is an exact auto-equivalence of the category of modules

Blueprint `sm-projectivity-core.tex`, `lem:sm-lbd-twist-functor` (PLAN-OM3 M1). For line-bundle
data `L` on `X` and `m ∈ ℤ`:

* `LineBundleData.twistMap φ : F ⊗ 𝓛^m ⟶ G ⊗ 𝓛^m` for `φ : F ⟶ G` (coefficientwise), and the
  functor `LineBundleData.twistFunctor L m`;
* `LineBundleData.twistTwistIso : (F ⊗ 𝓛^m) ⊗ 𝓛^n ≅ F ⊗ 𝓛^{m+n}` (on `W ⊆ U i` the `i`-th
  coefficient of the `i`-th coefficient), natural in `F`;
* `LineBundleData.twistEquivalence L m : X.Modules ≌ X.Modules` with inverse the twist by `-m`;
* `LineBundleData.shortExact_twist`: twisting preserves short exact sequences, so the long exact
  cohomology sequences of COH1 (`Cohomology.cohomologyδ`) apply to twisted sequences
  `0 → F' ⊗ 𝓛^m → F ⊗ 𝓛^m → F'' ⊗ 𝓛^m → 0` (used for the dévissage of fibre-ampleness on
  curves, lane OM3B).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {X : Scheme.{u}}

namespace LineBundleData

variable (L : LineBundleData X) {F G H : X.Modules} (m n : ℤ)

/-! ### Functoriality -/

lemma app_res_apply (φ : F ⟶ G) {V W : X.Opens} (h : V ≤ W) (t : Γ(F, W)) :
    φ.app V (F.presheaf.map (homOfLE h).op t) = G.presheaf.map (homOfLE h).op (φ.app W t) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) t

/-- A morphism of modules acts on compatible families coefficientwise. -/
def twistMapApp (φ : F ⟶ G) (W : X.Opens) : L.twistSubgroup F m W →+ L.twistSubgroup G m W where
  toFun t := ⟨fun i => φ.app (W ⊓ L.U i) (t.1 i), by
    intro i j
    simp only
    rw [← app_res_apply, ← app_res_apply, t.2 i j, Scheme.Modules.Hom.app_smul]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

@[simp]
lemma twistMapApp_apply (φ : F ⟶ G) (W : X.Opens) (t : L.twistSubgroup F m W) (i : L.ι) :
    (L.twistMapApp m φ W t).1 i = φ.app (W ⊓ L.U i) (t.1 i) :=
  rfl

/-- **Twisting a morphism**: `φ ⊗ 𝓛^m : F ⊗ 𝓛^m ⟶ G ⊗ 𝓛^m`. -/
def twistMap (φ : F ⟶ G) : L.twist F m ⟶ L.twist G m where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (L.twistMapApp m φ W.unop)
      naturality := fun {W W'} k => by
        ext t
        apply Subtype.ext
        funext i
        exact app_res_apply φ _ _ }
    (fun W r t => by
      apply Subtype.ext
      funext i
      exact Scheme.Modules.Hom.app_smul φ _ _)

@[simp]
lemma twistMap_app_apply (φ : F ⟶ G) (W : X.Opens) (t : L.twistSubgroup F m W) (i : L.ι) :
    ((L.twistMap m φ).app W t : L.twistSubgroup G m W).1 i = φ.app (W ⊓ L.U i) (t.1 i) :=
  rfl

lemma twistMap_id (F : X.Modules) : L.twistMap m (𝟙 F) = 𝟙 _ := by
  ext W t
  apply Subtype.ext
  funext i
  rfl

lemma twistMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    L.twistMap m (φ ≫ ψ) = L.twistMap m φ ≫ L.twistMap m ψ := by
  ext W t
  apply Subtype.ext
  funext i
  rfl

/-- **The twist functor** `F ↦ F ⊗ 𝓛^m`. -/
@[simps]
def twistFunctor : X.Modules ⥤ X.Modules where
  obj F := L.twist F m
  map φ := L.twistMap m φ
  map_id F := L.twistMap_id m F
  map_comp φ ψ := L.twistMap_comp m φ ψ

/-! ### Twisting twice -/

section TwistTwist

variable (F) {m}

/-- Change of chart for the local coefficient: `t_i = (u i j)^m · t_j` on `V ⊆ U i ∩ U j`. -/
lemma toLocal_change {V : X.Opens} {i j : L.ι} (hi : V ≤ L.U i) (hj : V ≤ L.U j)
    (t : L.twistSubgroup F m V) :
    toLocal F m hi t =
      ((L.trans (le_inf hi hj : V ≤ L.U i ⊓ L.U j) ^ m : Γ(X, V)ˣ) : Γ(X, V)) •
        toLocal F m hj t := by
  have hle : V ≤ V ⊓ (L.U i ⊓ L.U j) := le_inf le_rfl (le_inf hi hj)
  have e := congrArg (F.presheaf.map (homOfLE hle).op) (t.2 i j)
  rw [Scheme.Modules.map_smul, Cohomology.presheaf_map_map F _ _ (le_inf le_rfl hi),
    Cohomology.presheaf_map_map F _ _ (le_inf le_rfl hj), L.map_res_trans_zpow] at e
  exact e

variable (m)

/-- The coefficient map `(F ⊗ 𝓛^m) ⊗ 𝓛^n ⟶ F ⊗ 𝓛^{m+n}` on sections over `W`: the `i`-th
coefficient of the `i`-th coefficient. -/
def twistTwistApp (W : X.Opens) :
    L.twistSubgroup (L.twist F m) n W →+ L.twistSubgroup F (m + n) W where
  toFun a := ⟨fun i => toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i)
      (a.1 i : L.twistSubgroup F m (W ⊓ L.U i)), by
    intro i j
    have hV : W ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_right
    let a' : ∀ k, L.twistSubgroup F m (W ⊓ L.U k) := fun k => a.1 k
    have ha' : L.twistRestrict F m (L.le_left W i j) (a' i) =
        L.transPow n W i j • L.twistRestrict F m (L.le_right W i j) (a' j) := a.2 i j
    have h1 : toLocal F m (hV.trans inf_le_left) (L.twistRestrict F m (L.le_left W i j) (a' i)) =
        F.presheaf.map (homOfLE (L.le_left W i j)).op
          (toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) (a' i)) :=
      toLocal_restrict F m inf_le_right (L.le_left W i j) (a' i)
    have h2 : toLocal F m (hV.trans inf_le_right)
        (L.twistRestrict F m (L.le_right W i j) (a' j)) =
        F.presheaf.map (homOfLE (L.le_right W i j)).op
          (toLocal F m (inf_le_right : W ⊓ L.U j ≤ L.U j) (a' j)) :=
      toLocal_restrict F m inf_le_right (L.le_right W i j) (a' j)
    have h3 := L.toLocal_change F (hV.trans inf_le_left) (hV.trans inf_le_right)
      (L.twistRestrict F m (L.le_right W i j) (a' j))
    have e₁ := congrArg (toLocal F m (hV.trans inf_le_left)) ha'
    rw [toLocal_smul, h3, h2, h1] at e₁
    show F.presheaf.map (homOfLE (L.le_left W i j)).op
        (toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) (a' i)) =
      L.transPow (m + n) W i j • F.presheaf.map (homOfLE (L.le_right W i j)).op
        (toLocal F m (inf_le_right : W ⊓ L.U j ≤ L.U j) (a' j))
    rw [e₁, smul_smul]
    congr 1
    simp only [transPow]
    rw [← Units.val_mul, ← zpow_add, add_comm]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

lemma twistTwistApp_apply (W : X.Opens) (a : L.twistSubgroup (L.twist F m) n W) (i : L.ι) :
    (L.twistTwistApp F m n W a).1 i =
      toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) (a.1 i : L.twistSubgroup F m (W ⊓ L.U i)) :=
  rfl

lemma twistTwistApp_bijective (W : X.Opens) : Function.Bijective (L.twistTwistApp F m n W) := by
  constructor
  · intro a a' h
    apply Subtype.ext
    funext i
    let b : L.twistSubgroup F m (W ⊓ L.U i) := a.1 i
    let b' : L.twistSubgroup F m (W ⊓ L.U i) := a'.1 i
    have hi : toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) b =
        toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) b' :=
      congrFun (congrArg Subtype.val h) i
    have := congrArg (ofLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i)) hi
    rwa [ofLocal_toLocal, ofLocal_toLocal] at this
  · intro b
    refine ⟨⟨fun i => (ofLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) (b.1 i) :
        L.twistSubgroup F m (W ⊓ L.U i)), ?_⟩, ?_⟩
    · intro i j
      have hV : W ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_right
      let c : ∀ k, L.twistSubgroup F m (W ⊓ L.U k) := fun k =>
        ofLocal F m (inf_le_right : W ⊓ L.U k ≤ L.U k) (b.1 k)
      show L.twistRestrict F m (L.le_left W i j) (c i) =
        L.transPow n W i j • L.twistRestrict F m (L.le_right W i j) (c j)
      apply (localEquiv F m (hV.trans inf_le_left)).injective
      simp only [localEquiv_apply]
      have h1 : toLocal F m (hV.trans inf_le_left) (L.twistRestrict F m (L.le_left W i j) (c i)) =
          F.presheaf.map (homOfLE (L.le_left W i j)).op (b.1 i) := by
        rw [show toLocal F m (hV.trans inf_le_left) (L.twistRestrict F m (L.le_left W i j) (c i)) =
          F.presheaf.map (homOfLE (L.le_left W i j)).op
            (toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) (c i)) from
          toLocal_restrict F m inf_le_right (L.le_left W i j) (c i)]
        rw [toLocal_ofLocal]
      have h2 : toLocal F m (hV.trans inf_le_right)
          (L.twistRestrict F m (L.le_right W i j) (c j)) =
          F.presheaf.map (homOfLE (L.le_right W i j)).op (b.1 j) := by
        rw [show toLocal F m (hV.trans inf_le_right)
          (L.twistRestrict F m (L.le_right W i j) (c j)) =
          F.presheaf.map (homOfLE (L.le_right W i j)).op
            (toLocal F m (inf_le_right : W ⊓ L.U j ≤ L.U j) (c j)) from
          toLocal_restrict F m inf_le_right (L.le_right W i j) (c j)]
        rw [toLocal_ofLocal]
      have h3 := L.toLocal_change F (hV.trans inf_le_left) (hV.trans inf_le_right)
        (L.twistRestrict F m (L.le_right W i j) (c j))
      rw [toLocal_smul, h3, h1, h2, smul_smul, b.2 i j]
      congr 1
      simp only [transPow]
      rw [← Units.val_mul, ← zpow_add, add_comm]
    · apply Subtype.ext
      funext i
      exact toLocal_ofLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) (b.1 i)

/-- The morphism `(F ⊗ 𝓛^m) ⊗ 𝓛^n ⟶ F ⊗ 𝓛^{m+n}`. -/
def twistTwistHom : L.twist (L.twist F m) n ⟶ L.twist F (m + n) where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (L.twistTwistApp F m n W.unop)
      naturality := fun {W W'} k => by
        ext a
        apply Subtype.ext
        funext i
        exact toLocal_restrict F m (inf_le_right : W.unop ⊓ L.U i ≤ L.U i)
          (inf_le_inf_right (L.U i) (leOfHom k.unop)) (a.1 i) }
    (fun W r a => by
      apply Subtype.ext
      funext i
      exact toLocal_smul F m (inf_le_right : W.unop ⊓ L.U i ≤ L.U i)
        (res (inf_le_left : W.unop ⊓ L.U i ≤ W.unop) r) (a.1 i))

instance : IsIso (L.twistTwistHom F m n) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact L.twistTwistApp_bijective F m n W

/-- **Twisting twice**: `(F ⊗ 𝓛^m) ⊗ 𝓛^n ≅ F ⊗ 𝓛^{m+n}`. -/
def twistTwistIso : L.twist (L.twist F m) n ≅ L.twist F (m + n) :=
  asIso (L.twistTwistHom F m n)

variable {F}

lemma twistTwistHom_naturality (φ : F ⟶ G) :
    L.twistMap n (L.twistMap m φ) ≫ L.twistTwistHom G m n =
      L.twistTwistHom F m n ≫ L.twistMap (m + n) φ := by
  ext W a
  apply Subtype.ext
  funext i
  change toLocal G m (inf_le_right : W ⊓ L.U i ≤ L.U i) (L.twistMapApp m φ (W ⊓ L.U i) (a.1 i)) =
    φ.app (W ⊓ L.U i) (toLocal F m (inf_le_right : W ⊓ L.U i ≤ L.U i) (a.1 i))
  exact (app_res_apply φ _ _).symm

end TwistTwist

/-! ### Naturality of `F ≅ F ⊗ 𝓛^0` -/

lemma toTwistZeroHom_naturality (φ : F ⟶ G) :
    φ ≫ L.toTwistZeroHom G = L.toTwistZeroHom F ≫ L.twistMap 0 φ := by
  ext W s
  apply Subtype.ext
  funext i
  change G.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op (φ.app W s) =
    φ.app (W ⊓ L.U i) (F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op s)
  exact (app_res_apply φ _ _).symm

/-- `F ≅ F ⊗ 𝓛^0`, naturally in `F`. -/
def twistZeroNatIso : 𝟭 X.Modules ≅ L.twistFunctor 0 :=
  NatIso.ofComponents (fun F => (L.twistZeroIso F).symm) (fun φ => by
    change φ ≫ (asIso (L.toTwistZeroHom _)).hom = (asIso (L.toTwistZeroHom _)).hom ≫ _
    exact L.toTwistZeroHom_naturality φ)

/-- `F ⊗ 𝓛^{a} ≅ F ⊗ 𝓛^{b}` for `a = b`, naturally in `F`. -/
def twistFunctorCongr {a b : ℤ} (h : a = b) : L.twistFunctor a ≅ L.twistFunctor b :=
  eqToIso (by rw [h])

/-- `(F ⊗ 𝓛^m) ⊗ 𝓛^n ≅ F ⊗ 𝓛^{m+n}`, naturally in `F`. -/
def twistTwistNatIso : L.twistFunctor m ⋙ L.twistFunctor n ≅ L.twistFunctor (m + n) :=
  NatIso.ofComponents (fun F => L.twistTwistIso F m n)
    (fun φ => L.twistTwistHom_naturality m n φ)

/-! ### The equivalence and exactness -/

/-- **Twisting by `𝓛^m` is an auto-equivalence** of `X.Modules`, with inverse the twist by
`𝓛^{-m}`. -/
def twistEquivalence : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (L.twistFunctor m) (L.twistFunctor (-m))
    (L.twistZeroNatIso ≪≫ L.twistFunctorCongr (by ring) ≪≫ (L.twistTwistNatIso m (-m)).symm)
    (L.twistTwistNatIso (-m) m ≪≫ L.twistFunctorCongr (by ring) ≪≫ L.twistZeroNatIso.symm)

lemma twistEquivalence_functor : (L.twistEquivalence m).functor = L.twistFunctor m :=
  rfl

instance : (L.twistFunctor m).Additive where
  map_add {F G} {φ ψ} := by
    ext W t
    apply Subtype.ext
    funext i
    rfl

instance : (L.twistFunctor m).IsEquivalence :=
  (L.twistEquivalence m).isEquivalence_functor

/-- **Twisting preserves short exact sequences.** -/
theorem shortExact_twist {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (L.twistFunctor m)).ShortExact :=
  hS.map_of_exact _

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity

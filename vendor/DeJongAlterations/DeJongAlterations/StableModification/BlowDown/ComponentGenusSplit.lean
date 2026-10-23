/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ComponentGenusAlgebra

/-!
# The δ-invariant of a normalization in a disjoint union

Let `f : X → Y` be quasi-compact and quasi-separated and `X = U ⊔ V`. The relative normalization
`Ỹ_f` of `f` is the disjoint union of those of `f|_U` and `f|_V` (Mathlib's
`Scheme.Hom.normalizationCoprodIso`), so on every open the sections of `𝒪_{Ỹ_f}` are the product of
the sections of the two pieces (`normalizationSectionsIso`). Consequently the δ-invariant
`dim_k (π_*𝒪_{Ỹ}/𝒪_Y)_y` of `CurvesField.Genus.deltaInvariant` drops when `Ỹ_f` is replaced by
`Ỹ_{f|_U}` (`deltaInvariant_le_of_coprod`), and drops by at least one if both pieces have a point
over `y` and `𝒪_Y → π_*𝒪_{Ỹ_f}` is injective (`deltaInvariant_add_one_le_of_coprod`). For the
normalization of a reduced curve `C` in its generic points (`CurvesField.Genus.normalizationPoints`),
split as one component `{v}` and the others, this says
`δ_{C̃_v}(y) + 1 ≤ δ_C(y)` at a point `y` of `closure {v}` lying on another component
(`deltaInvariant_normalizationPoints_add_one_le`): Temkin's count `g(x) ≥ |x̃| - 1` (M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, App. B, l. 4388–4391) in the
relative form needed to compare a component with the whole curve.

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-delta-split`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.BlowDown.ComponentGenus

universe u

open Cohomology CurvesField CurvesField.Genus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Prod

/-- The binary product of commutative rings in `CommRingCat` is the cartesian product. -/
def prodIso (A B : CommRingCat.{u}) : A ⨯ B ≅ CommRingCat.of (A × B) :=
  (limit.isLimit _).conePointUniqueUpToIso (CommRingCat.prodFanIsLimit A B)

theorem prodIso_hom_fst (A B : CommRingCat.{u}) (x : ↑(A ⨯ B)) :
    ((prodIso A B).hom.hom x).1 = (prod.fst : A ⨯ B ⟶ A).hom x := by
  have h : (prodIso A B).hom ≫ (CommRingCat.prodFan A B).fst = prod.fst :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨.left⟩ : Discrete WalkingPair)
  rw [← h]
  rfl

theorem prodIso_hom_snd (A B : CommRingCat.{u}) (x : ↑(A ⨯ B)) :
    ((prodIso A B).hom.hom x).2 = (prod.snd : A ⨯ B ⟶ B).hom x := by
  have h : (prodIso A B).hom ≫ (CommRingCat.prodFan A B).snd = prod.snd :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨.right⟩ : Discrete WalkingPair)
  rw [← h]
  rfl

end Prod

section Nonvanishing

/-- **A function not vanishing at `y` pulls back to a nonzero function** on any scheme with a
point over `y`: for `g : X' → Y`, an affine open `W ∋ y` and `s ∈ Γ(Y, W)` outside the prime of `y`,
`g^♯ s ≠ 0` as soon as some point of `X'` maps to `y`. -/
theorem app_ne_zero_of_not_mem {X' Y : Scheme.{u}} (g : X' ⟶ Y) {W : Y.Opens} (hW : IsAffineOpen W)
    {y : Y} (hy : y ∈ W) {s : Γ(Y, W)} (hs : s ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal)
    {x' : X'} (hx' : g x' = y) : (g.app W).hom s ≠ 0 := by
  intro h0
  have hyb : y ∈ Y.basicOpen s := by
    rw [Scheme.mem_basicOpen _ _ y hy]
    let _ : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
    have := hW.isLocalization_stalk ⟨y, hy⟩
    have hm : ¬ (Y.presheaf.germ W y hy).hom s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
      fun hm => hs ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y)
        (hW.primeIdealOf ⟨y, hy⟩).asIdeal s).1 hm)
    exact not_not.1 fun hu => hm ((IsLocalRing.mem_maximalIdeal _).2 hu)
  have hx : x' ∈ g ⁻¹ᵁ Y.basicOpen s := by
    change g x' ∈ Y.basicOpen s
    rw [hx']
    exact hyb
  rw [Scheme.preimage_basicOpen, h0, Scheme.basicOpen_zero] at hx
  exact hx

end Nonvanishing

section Split

variable {X Y U V : Scheme.{u}} (f : X ⟶ Y) {iU : U ⟶ X} {iV : V ⟶ X}
  (e : IsColimit (BinaryCofan.mk iU iV)) [QuasiCompact f] [QuasiSeparated f]
  [QuasiCompact iU] [QuasiSeparated iU] [QuasiCompact iV] [QuasiSeparated iV]

/-- **The sections of a normalization in a disjoint union split**: for an open `T` of `Ỹ_f`,
`Γ(Ỹ_f, T) ≅ Γ(Ỹ_{f|U}, T) × Γ(Ỹ_{f|V}, T)` through the two open immersions
`Ỹ_{f|U}, Ỹ_{f|V} → Ỹ_f` of Mathlib's `Scheme.Hom.normalizationCoprodIso`. -/
def normalizationSectionsIso (T : f.normalization.Opens) :
    Γ(f.normalization, T) ≅ CommRingCat.of
      (Γ((iU ≫ f).normalization,
          coprod.inl (C := Scheme) ⁻¹ᵁ ((f.normalizationCoprodIso e).hom ⁻¹ᵁ T)) ×
        Γ((iV ≫ f).normalization,
          coprod.inr (C := Scheme) ⁻¹ᵁ ((f.normalizationCoprodIso e).hom ⁻¹ᵁ T))) :=
  asIso ((f.normalizationCoprodIso e).hom.app T) ≪≫ Scheme.coprodPresheafObjIso _ ≪≫
    prodIso _ _

theorem normalizationSectionsIso_fst (T : f.normalization.Opens) (x : Γ(f.normalization, T)) :
    ((normalizationSectionsIso f e T).hom.hom x).1 =
      ((coprod.inl ≫ (f.normalizationCoprodIso e).hom).app T).hom x := by
  change ((prodIso _ _).hom.hom ((Scheme.coprodPresheafObjIso _).hom.hom
    (((f.normalizationCoprodIso e).hom.app T).hom x))).1 =
      ((coprod.inl (C := Scheme)).app _).hom
        (((f.normalizationCoprodIso e).hom.app T).hom x)
  rw [prodIso_hom_fst, ← CommRingCat.comp_apply, Scheme.coprodPresheafObjIso_hom_fst]

theorem normalizationSectionsIso_snd (T : f.normalization.Opens) (x : Γ(f.normalization, T)) :
    ((normalizationSectionsIso f e T).hom.hom x).2 =
      ((coprod.inr ≫ (f.normalizationCoprodIso e).hom).app T).hom x := by
  change ((prodIso _ _).hom.hom ((Scheme.coprodPresheafObjIso _).hom.hom
    (((f.normalizationCoprodIso e).hom.app T).hom x))).2 =
      ((coprod.inr (C := Scheme)).app _).hom
        (((f.normalizationCoprodIso e).hom.app T).hom x)
  rw [prodIso_hom_snd, ← CommRingCat.comp_apply, Scheme.coprodPresheafObjIso_hom_snd]

/-- Restricting sections of `Ỹ_f` to `Ỹ_{f|U}` is surjective. -/
theorem app_inl_surjective (T : f.normalization.Opens) :
    Function.Surjective ((coprod.inl ≫ (f.normalizationCoprodIso e).hom).app T).hom := by
  intro b
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
    (normalizationSectionsIso f e T).hom).2 (b, 0)
  refine ⟨x, ?_⟩
  rw [← normalizationSectionsIso_fst, hx]

variable {k : Type u} [Field k] (c : k →+* Γ(Y, ⊤))

include e in
/-- **The δ-invariant of a piece of the normalization is at most that of the whole**:
`δ_{Ỹ_{f|U}}(y) ≤ δ_{Ỹ_f}(y)` when `π_*𝒪_{Ỹ_f}/𝒪_Y` is finite-dimensional on affine opens. -/
theorem deltaInvariant_le_of_coprod {gU : U ⟶ Y} (hU : iU ≫ f = gU) [QuasiCompact gU]
    [QuasiSeparated gU] [IsAffineHom f.fromNormalization] [IsAffineHom gU.fromNormalization]
    (hfin : ∀ (W : Y.Opens) (hW : IsAffineOpen W),
      IsFiniteCoker (sectionsRingHom c (le_top : W ≤ ⊤)) (f.fromNormalization.app W).hom)
    (y : Y) :
    deltaInvariant gU.fromNormalization c y ≤ deltaInvariant f.fromNormalization c y := by
  subst hU
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have h₁ := Scheme.Hom.inl_normalizationCoprodIso_hom_fromNormalization f e
  rw [← chartDelta_eq_deltaInvariant (π := (iU ≫ f).fromNormalization) W hW y hyW,
    ← chartDelta_eq_deltaInvariant (π := f.fromNormalization) W hW y hyW]
  unfold chartDelta
  rw [← h₁]
  exact deltaAt_comp_le _ _ ((coprod.inl ≫ (f.normalizationCoprodIso e).hom).app
    (f.fromNormalization ⁻¹ᵁ W)).hom (app_inl_surjective f e _) (hfin W hW) _

include e in
/-- **Splitting off a second piece lowers the δ-invariant** (blueprint
`lem:sm-bdu-delta-split`): if `𝒪_Y → π_*𝒪_{Ỹ_f}` is injective with finite-dimensional cokernel
on affine opens and both `Ỹ_{f|U}` and `Ỹ_{f|V}` have a point over `y`, then
`δ_{Ỹ_{f|U}}(y) + 1 ≤ δ_{Ỹ_f}(y)` (`deltaAt_comp_add_one_le` with the idempotent `(0, 1)`). -/
theorem deltaInvariant_add_one_le_of_coprod {gU : U ⟶ Y} {gV : V ⟶ Y} (hU : iU ≫ f = gU)
    (hV : iV ≫ f = gV) [QuasiCompact gU] [QuasiSeparated gU] [QuasiCompact gV]
    [QuasiSeparated gV] [IsAffineHom f.fromNormalization] [IsAffineHom gU.fromNormalization]
    (hinj : ∀ (W : Y.Opens), IsAffineOpen W → Function.Injective (f.fromNormalization.app W).hom)
    (hfin : ∀ (W : Y.Opens) (hW : IsAffineOpen W),
      IsFiniteCoker (sectionsRingHom c (le_top : W ≤ ⊤)) (f.fromNormalization.app W).hom)
    (y : Y) (hyU : ∃ a, gU.fromNormalization a = y) (hyV : ∃ b, gV.fromNormalization b = y) :
    deltaInvariant gU.fromNormalization c y + 1 ≤ deltaInvariant f.fromNormalization c y := by
  subst hU hV
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have h₁ := Scheme.Hom.inl_normalizationCoprodIso_hom_fromNormalization f e
  have h₂ := Scheme.Hom.inr_normalizationCoprodIso_hom_fromNormalization f e
  rw [← chartDelta_eq_deltaInvariant (π := (iU ≫ f).fromNormalization) W hW y hyW,
    ← chartDelta_eq_deltaInvariant (π := f.fromNormalization) W hW y hyW]
  unfold chartDelta
  set T := f.fromNormalization ⁻¹ᵁ W
  set Φ := normalizationSectionsIso f e T
  set ε : Γ(f.normalization, T) := Φ.inv.hom (0, 1) with hε
  have hΦε : Φ.hom.hom ε = (0, 1) := by
    rw [hε, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  have hε₁ : ((coprod.inl ≫ (f.normalizationCoprodIso e).hom).app T).hom ε = 0 := by
    rw [← normalizationSectionsIso_fst, hΦε]
  have hε₂ : ((coprod.inr ≫ (f.normalizationCoprodIso e).hom).app T).hom ε = 1 := by
    rw [← normalizationSectionsIso_snd, hΦε]
  have hidem : IsIdempotentElem ε := by
    apply (ConcreteCategory.bijective_of_isIso Φ.hom).1
    rw [map_mul, hΦε, Prod.mk_mul_mk, zero_mul, one_mul]
  obtain ⟨a, ha⟩ := hyU
  obtain ⟨b, hb⟩ := hyV
  have ha' : ((coprod.inl ≫ (f.normalizationCoprodIso e).hom) ≫ f.fromNormalization) a = y := by
    rw [Category.assoc, h₁]
    exact ha
  have hb' : ((coprod.inr ≫ (f.normalizationCoprodIso e).hom) ≫ f.fromNormalization) b = y := by
    rw [Category.assoc, h₂]
    exact hb
  rw [← h₁]
  refine deltaAt_comp_add_one_le _ _ (hinj W hW) _ (app_inl_surjective f e T) (hfin W hW) _ ε hidem
    hε₁ (fun s hs h0 => ?_) (fun s hs h0 => ?_)
  · have := congrArg ((coprod.inr ≫ (f.normalizationCoprodIso e).hom).app T).hom h0
    rw [map_mul, hε₂, mul_one, map_zero] at this
    exact app_ne_zero_of_not_mem _ hW hyW hs hb' this
  · have := congrArg ((coprod.inl ≫ (f.normalizationCoprodIso e).hom).app T).hom h0
    rw [map_mul, map_sub, map_one, hε₁, sub_zero, mul_one, map_zero] at this
    exact app_ne_zero_of_not_mem _ hW hyW hs ha' this

end Split

end DeJongAlterations.StableModification.BlowDown.ComponentGenus

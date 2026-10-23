/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.RelativeAlgebra
import DeJongAlterations.StableModification.Projectivity.RelativeFinite
import DeJongAlterations.StableModification.Projectivity.RelativeCech

/-!
# Lifting sections of `𝓛^m` from a fibre (`lem:sm-ltg-onto`)

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-onto` (PLAN-OM3 §3 step 1, pointwise form
requested by PLAN-T5 §7 for T5G's Lemma 5.1(ii)). Let `β : X ⟶ Y`, `y ∈ Y` a closed point, `W ∋ y`
an affine open, and `U₀, U₁` affine opens of `X` with affine intersection and
`U₀ ∪ U₁ = β⁻¹ W`. Let `A = Γ(Y, W)` and `d : Γ(U₀, 𝓛^m) × Γ(U₁, 𝓛^m) → Γ(U₀ ∩ U₁, 𝓛^m)` the
difference of the restrictions (`pairDiffOn`, an `A`-linear map). If `Ȟ¹` of `(ι^* 𝓛)^m` on the
fibre `X_y` vanishes for the cover `{ι⁻¹ U₀, ι⁻¹ U₁}` and `coker d` is a finite `A`-module, then every
global section of `(ι^* 𝓛)^m` on `X_y` is the pullback of a section of `𝓛^m` over `β⁻¹ W`
(`exists_lift_of_twoAffines`).

The proof is Nakayama's lemma for the two-term complex (`exists_smul_lift_of_twoTerm`), with the
base-change inputs of `RelativeFibre.lean` and the identification of `Ȟ¹` of two opens of
`RelativeCech.lean`; no flatness is used.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Cohomology

/-! ### Two-term complexes over an open -/

section PairDiffOn

variable {Z : Scheme.{u}} {R : Type u} [CommRing R] (F : Z.Modules) {V₀ : Z.Opens}
  (c : R →+* Γ(Z, V₀)) {U₀ U₁ : Z.Opens} (h₀ : U₀ ≤ V₀) (h₁ : U₁ ≤ V₀)

/-- The difference of the restrictions `(a, b) ↦ b|_{U₀ ∩ U₁} - a|_{U₀ ∩ U₁}` for opens below
`V₀`, as an `R`-linear map. -/
def pairDiffOn : (sectionsModuleCat F c U₀ h₀ × sectionsModuleCat F c U₁ h₁) →ₗ[R]
    sectionsModuleCat F c (U₀ ⊓ U₁) (inf_le_left.trans h₀) :=
  (sectionsRestrict F c h₁ (inf_le_left.trans h₀) inf_le_right).hom ∘ₗ LinearMap.snd _ _ _ -
    (sectionsRestrict F c h₀ (inf_le_left.trans h₀) inf_le_left).hom ∘ₗ LinearMap.fst _ _ _

lemma pairDiffOn_apply (a : sectionsModuleCat F c U₀ h₀) (b : sectionsModuleCat F c U₁ h₁) :
    pairDiffOn F c h₀ h₁ (a, b) =
      F.presheaf.map (homOfLE inf_le_right).op b - F.presheaf.map (homOfLE inf_le_left).op a :=
  rfl

end PairDiffOn

/-- **Gluing two sections** of a sheaf of modules which agree on the intersection. -/
theorem exists_glue_two {X : Scheme.{u}} (F : X.Modules) {U₀ U₁ : X.Opens} (s₀ : Γ(F, U₀))
    (s₁ : Γ(F, U₁))
    (h : F.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op s₀ =
      F.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op s₁) :
    ∃ s : Γ(F, U₀ ⊔ U₁), F.presheaf.map (homOfLE le_sup_left).op s = s₀ ∧
      F.presheaf.map (homOfLE le_sup_right).op s = s₁ := by
  let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  let U : Bool → X.Opens := fun b => if b then U₀ else U₁
  let sf : ∀ b : Bool, ToType (G.1.obj (op (U b)))
    | true => s₀
    | false => s₁
  have hcompat : TopCat.Presheaf.IsCompatible G.1 U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · have e := congrArg (F.presheaf.map (homOfLE (le_of_eq (inf_comm U₁ U₀))).op) h
      rw [presheaf_map_map F _ _ inf_le_right, presheaf_map_map F _ _ inf_le_left] at e
      exact e.symm
    · exact h
    · rfl
  obtain ⟨s, hs, -⟩ := G.existsUnique_gluing' U (U₀ ⊔ U₁)
    (fun b => match b with | true => homOfLE le_sup_left | false => homOfLE le_sup_right)
    (by
      intro x hx
      rcases hx with hx | hx
      · exact Opens.mem_iSup.mpr ⟨true, hx⟩
      · exact Opens.mem_iSup.mpr ⟨false, hx⟩) sf hcompat
  exact ⟨s, hs true, hs false⟩

namespace LineBundleData

variable {X Y : Scheme.{u}} (β : X ⟶ Y) (y : Y) (L : LineBundleData X) (m : ℤ)

/-! ### Coefficients -/

section Coefficients

variable {W : Y.Opens} (hy : y ∈ W)

include hy in
lemma top_le_fiber_preimage : (⊤ : (β.fiber y).Opens) ≤ (β.fiberι y ≫ β) ⁻¹ᵁ W := by
  intro z _
  change β (β.fiberι y z) ∈ W
  have hz : β.fiberι y z ∈ β ⁻¹' {y} := by
    rw [← Scheme.Hom.range_fiberι]
    exact ⟨z, rfl⟩
  rw [hz]
  exact hy

/-- The coefficient map `Γ(Y, W) → Γ(X_y, ⊤)` of the fibre. -/
def fibreCoeff : Γ(Y, W) →+* Γ(β.fiber y, ⊤) :=
  ((β.fiberι y ≫ β).appLE W ⊤ (top_le_fiber_preimage β y hy)).hom

lemma fibreCoeff_eq (a : Γ(Y, W)) :
    fibreCoeff β y hy a = (β.fiberToSpecResidueField y).appLE ⊤ ⊤ le_top (fibreResidue y hy a) := by
  have hw : β.fiberι y ≫ β = β.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
    (IsPullback.of_hasPullback β (Y.fromSpecResidueField y)).w
  have e2 : (fibreResidue y hy ≫ (β.fiberToSpecResidueField y).appLE ⊤ ⊤ le_top) =
      (β.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y).appLE W ⊤
        (fun x hx => top_le_fromSpecResidueField_preimage y hy trivial) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have := congrArg (fun q => q.hom a) e2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this]
  have key2 : ∀ (f g : (β.fiber y) ⟶ Y) (_ : f = g) (e : (⊤ : (β.fiber y).Opens) ≤ f ⁻¹ᵁ W)
      (e' : (⊤ : (β.fiber y).Opens) ≤ g ⁻¹ᵁ W),
      (f.appLE W ⊤ e).hom a = (g.appLE W ⊤ e').hom a := by
    rintro f g rfl e e'
    rfl
  exact key2 _ _ hw _ _

lemma fibreCoeff_eq_zero {a : Γ(Y, W)} (ha : a ∈ RingHom.ker (fibreResidue y hy).hom) :
    fibreCoeff β y hy a = 0 := by
  rw [fibreCoeff_eq, RingHom.mem_ker.mp ha, map_zero]

/-- On the fibre, `Γ(Y, W)` acts through its residue map: a restricted coefficient is the
pullback of the restricted function. -/
lemma fiberι_app_res (a : Γ(Y, W)) {V : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) :
    (β.fiberι y).app V (res hV (β.app W a)) =
      res (le_top : β.fiberι y ⁻¹ᵁ V ≤ ⊤) (fibreCoeff β y hy a) := by
  rw [LineBundleData.app_res]
  simp only [fibreCoeff, Scheme.Hom.appLE]
  change _ = ((β.fiberι y ≫ β).app W ≫ _ ≫ _) a
  rw [Scheme.Hom.comp_app]
  change res _ ((β.fiberι y).app (β ⁻¹ᵁ W) (β.app W a)) =
    (β.fiber y).presheaf.map _ ((β.fiber y).presheaf.map _ ((β.fiberι y).app (β ⁻¹ᵁ W)
      (β.app W a)))
  exact (res_res _ _ _ _).symm

end Coefficients

/-! ### The pullback maps -/

section Maps

variable {W : Y.Opens} (hy : y ∈ W)

/-- Pullback of sections of `𝓛^m` over `V ⊆ β⁻¹ W` to the fibre, as a `Γ(Y, W)`-linear map. -/
def fibrePullbackLin {V : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) :
    sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom V hV →ₗ[Γ(Y, W)]
      sectionsModuleCat ((L.pullback (β.fiberι y)).twist (unitModule (β.fiber y)) m)
        (fibreCoeff β y hy) (β.fiberι y ⁻¹ᵁ V) le_top where
  toFun s := Sections.pullback (β.fiberι y) (L := L) (m := m) s
  map_add' s t := Sections.pullback_add L m _ s t
  map_smul' a s := by
    change Sections.pullback (β.fiberι y) ((res hV (β.app W a)) • (show L.Sections m V from s)) =
      (res (le_top : β.fiberι y ⁻¹ᵁ V ≤ ⊤) (fibreCoeff β y hy a)) • Sections.pullback (β.fiberι y)
        (show L.Sections m V from s)
    rw [Sections.pullback_smul, fiberι_app_res β y hy a hV]

lemma fibrePullbackLin_apply {V : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) (s : L.Sections m V) :
    L.fibrePullbackLin β y m hy hV s = s.pullback (β.fiberι y) :=
  rfl

lemma fibrePullbackLin_map {V V' : X.Opens} (hV : V ≤ β ⁻¹ᵁ W) (hV' : V' ≤ β ⁻¹ᵁ W) (h : V' ≤ V)
    (s : sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom V hV) :
    L.fibrePullbackLin β y m hy hV' ((L.twist (unitModule X) m).presheaf.map (homOfLE h).op s) =
      ((L.pullback (β.fiberι y)).twist (unitModule (β.fiber y)) m).presheaf.map
        (homOfLE ((β.fiberι y).preimage_mono h)).op (L.fibrePullbackLin β y m hy hV s) :=
  Sections.pullback_restrict L m _ h s

end Maps

/-! ### The lifting lemma -/

section Lift

variable {W : Y.Opens} (hW : IsAffineOpen W) (hy : y ∈ W) (hcl : IsClosed ({y} : Set Y))
  {U₀ U₁ : X.Opens} (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
  (h₀₁ : IsAffineOpen (U₀ ⊓ U₁)) (hcov : U₀ ⊔ U₁ = β ⁻¹ᵁ W)

include hcov in
lemma le_of_sup_eq₀ : U₀ ≤ β ⁻¹ᵁ W := hcov ▸ le_sup_left

include hcov in
lemma le_of_sup_eq₁ : U₁ ≤ β ⁻¹ᵁ W := hcov ▸ le_sup_right

/-- The fibre opens `ι⁻¹ U₀`, `ι⁻¹ U₁` form a finite affine cover of the fibre. -/
def fibrePairCover : Cohomology.FiniteAffineCover (β.fiber y) :=
  pairCover (β.fiberι y ⁻¹ᵁ U₀) (β.fiberι y ⁻¹ᵁ U₁)
    (isAffineOpen_fiberι_preimage β y hW hy h₀ (le_of_sup_eq₀ β hcov))
    (isAffineOpen_fiberι_preimage β y hW hy h₁ (le_of_sup_eq₁ β hcov))
    (isAffineOpen_fiberι_preimage β y hW hy h₀₁ (inf_le_left.trans (le_of_sup_eq₀ β hcov)))
    (by
      rw [← Scheme.Hom.preimage_sup, hcov]
      exact top_unique (top_le_fiber_preimage β y hy))

include hW hy hcl h₀ h₁ h₀₁ in
/-- **Lifting sections from the fibre** (blueprint `lem:sm-ltg-onto`). If `Ȟ¹` of `(ι^* 𝓛)^m` on
the fibre vanishes for the cover by `ι⁻¹ U₀`, `ι⁻¹ U₁` and the cokernel of the difference map on
`X` is a finite `Γ(Y, W)`-module, every global section of `(ι^* 𝓛)^m` on the fibre over the closed
point `y` is the pullback of a section of `𝓛^m` over `β⁻¹ W`. -/
theorem exists_lift_of_twoAffines
    (hH1 : IsZero (cechCohomology ((L.pullback (β.fiberι y)).twist (unitModule (β.fiber y)) m)
      (pairOpens (β.fiberι y ⁻¹ᵁ U₀) (β.fiberι y ⁻¹ᵁ U₁)) (RingHom.id Γ(β.fiber y, ⊤)) 1))
    (hfin : Module.Finite Γ(Y, W)
      (sectionsModuleCat (L.twist (unitModule X) m) (β.app W).hom (U₀ ⊓ U₁)
          (inf_le_left.trans (le_of_sup_eq₀ β hcov)) ⧸
        LinearMap.range (pairDiffOn (L.twist (unitModule X) m) (β.app W).hom
          (le_of_sup_eq₀ β hcov) (le_of_sup_eq₁ β hcov))))
    (z : (L.pullback (β.fiberι y)).Sections m ⊤) :
    ∃ τ : L.Sections m (β ⁻¹ᵁ W), τ.pullback (β.fiberι y) = z.restrict le_top := by
  let ι := β.fiberι y
  have hU₀ := le_of_sup_eq₀ β hcov
  have hU₁ := le_of_sup_eq₁ β hcov
  have hU₀₁ : U₀ ⊓ U₁ ≤ β ⁻¹ᵁ W := inf_le_left.trans hU₀
  set FX := L.twist (unitModule X) m
  set Fy := (L.pullback ι).twist (unitModule (β.fiber y)) m
  set c := fibreCoeff β y hy
  let d := pairDiffOn FX (β.app W).hom hU₀ hU₁
  let e := pairDiffOn Fy c (le_top : ι ⁻¹ᵁ U₀ ≤ ⊤) (le_top : ι ⁻¹ᵁ U₁ ≤ ⊤)
  let φ₀ := (L.fibrePullbackLin β y m hy hU₀).prodMap (L.fibrePullbackLin β y m hy hU₁)
  let φ₁ := L.fibrePullbackLin β y m hy hU₀₁
  have hcomm : ∀ x, φ₁ (d x) = e (φ₀ x) := by
    rintro ⟨a, b⟩
    simp only [d, e, φ₀, φ₁, LinearMap.prodMap_apply, pairDiffOn_apply, map_sub]
    rw [L.fibrePullbackLin_map β y m hy hU₁ hU₀₁ inf_le_right,
      L.fibrePullbackLin_map β y m hy hU₀ hU₀₁ inf_le_left]
    rfl
  have hN : ∀ a ∈ RingHom.ker (fibreResidue y hy).hom, ∀ n : (sectionsModuleCat Fy c
      (ι ⁻¹ᵁ U₀) le_top × sectionsModuleCat Fy c (ι ⁻¹ᵁ U₁) le_top), a • n = 0 := by
    rintro a ha ⟨n₀, n₁⟩
    have h0 : c a = 0 := fibreCoeff_eq_zero β y hy ha
    refine Prod.ext ?_ ?_
    · change res (le_top : ι ⁻¹ᵁ U₀ ≤ ⊤) (c a) •
        (show (L.pullback ι).Sections m (ι ⁻¹ᵁ U₀) from n₀) = 0
      rw [h0, map_zero, zero_smul]
    · change res (le_top : ι ⁻¹ᵁ U₁ ≤ ⊤) (c a) •
        (show (L.pullback ι).Sections m (ι ⁻¹ᵁ U₁) from n₁) = 0
      rw [h0, map_zero, zero_smul]
  have hφ₀ : Function.Surjective φ₀ := by
    rintro ⟨n₀, n₁⟩
    obtain ⟨s₀, hs₀⟩ := L.surjective_pullback_fiberι β y m hW hy hcl h₀ hU₀ n₀
    obtain ⟨s₁, hs₁⟩ := L.surjective_pullback_fiberι β y m hW hy hcl h₁ hU₁ n₁
    exact ⟨(s₀, s₁), Prod.ext hs₀ hs₁⟩
  have hφ₁ : LinearMap.ker φ₁ ≤ (RingHom.ker (fibreResidue y hy).hom) • ⊤ := by
    intro s hs
    obtain ⟨n, a, z, ha, hsum⟩ := L.exists_sum_of_pullback_fiberι_eq_zero β y m hW hy hcl h₀₁ hU₀₁
      s hs
    have hsum' : s = ∑ i, a i • (show sectionsModuleCat FX (β.app W).hom (U₀ ⊓ U₁) hU₀₁ from
        z i) := by
      refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
      change _ = res hU₀₁ (β.app W (a i)) • (show L.Sections m (U₀ ⊓ U₁) from z i)
      rfl
    rw [hsum']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (ha i) Submodule.mem_top
  have he : Function.Surjective e :=
    surjective_pairDiff_of_isZero (ι ⁻¹ᵁ U₀) (ι ⁻¹ᵁ U₁) Fy (RingHom.id _) hH1
  have hfg : (⊤ : Submodule Γ(Y, W) (sectionsModuleCat FX (β.app W).hom (U₀ ⊓ U₁) hU₀₁ ⧸
      LinearMap.range d)).FG := hfin.fg_top
  obtain ⟨a, ha, -, hlift⟩ := exists_smul_lift_of_twoTerm (RingHom.ker (fibreResidue y hy).hom)
    d e φ₀ φ₁ hcomm hN hφ₀ hφ₁ he hfg
  -- the restrictions of `z` form a cocycle of the fibre complex
  let zz : sectionsModuleCat Fy c (ι ⁻¹ᵁ U₀) le_top × sectionsModuleCat Fy c (ι ⁻¹ᵁ U₁) le_top :=
    (z.restrict le_top, z.restrict le_top)
  have hzz : e zz = 0 := by
    change (z.restrict (le_top : ι ⁻¹ᵁ U₁ ≤ ⊤)).restrict
        (inf_le_right : ι ⁻¹ᵁ U₀ ⊓ ι ⁻¹ᵁ U₁ ≤ ι ⁻¹ᵁ U₁) -
      (z.restrict (le_top : ι ⁻¹ᵁ U₀ ≤ ⊤)).restrict
        (inf_le_left : ι ⁻¹ᵁ U₀ ⊓ ι ⁻¹ᵁ U₁ ≤ ι ⁻¹ᵁ U₀) = 0
    rw [sub_eq_zero]
    ext i
    simp only [Sections.coeff_restrict]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  obtain ⟨⟨x₀, x₁⟩, hx, hxz⟩ := hlift zz hzz
  -- `a` acts as `1` on the fibre
  have hca : c a = 1 := by
    have : c (a - 1) = 0 := fibreCoeff_eq_zero β y hy ha
    rwa [map_sub, map_one, sub_eq_zero] at this
  have haz : a • zz = zz := by
    refine Prod.ext ?_ ?_
    · change res (le_top : ι ⁻¹ᵁ U₀ ≤ ⊤) (c a) • (show (L.pullback ι).Sections m (ι ⁻¹ᵁ U₀) from
        z.restrict le_top) = _
      rw [hca, map_one, one_smul]
    · change res (le_top : ι ⁻¹ᵁ U₁ ≤ ⊤) (c a) • (show (L.pullback ι).Sections m (ι ⁻¹ᵁ U₁) from
        z.restrict le_top) = _
      rw [hca, map_one, one_smul]
  rw [haz] at hxz
  have hx₀ : Sections.pullback ι (show L.Sections m U₀ from x₀) = z.restrict le_top :=
    congrArg Prod.fst hxz
  have hx₁ : Sections.pullback ι (show L.Sections m U₁ from x₁) = z.restrict le_top :=
    congrArg Prod.snd hxz
  -- glue `x₀` and `x₁`
  have hagree : FX.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op x₀ =
      FX.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op x₁ := by
    have := hx
    change (show L.Sections m U₁ from x₁).restrict inf_le_right -
      (show L.Sections m U₀ from x₀).restrict inf_le_left = 0 at this
    exact (sub_eq_zero.mp this).symm
  obtain ⟨τ₀, hτ₀, hτ₁⟩ := exists_glue_two FX x₀ x₁ hagree
  let τ : L.Sections m (β ⁻¹ᵁ W) := (show L.Sections m (U₀ ⊔ U₁) from τ₀).restrict hcov.ge
  refine ⟨τ, ?_⟩
  -- compare on the cover `ι⁻¹ U₀ ∪ ι⁻¹ U₁`
  let G : TopCat.Sheaf Ab (β.fiber y) := ⟨Fy.presheaf, Fy.isSheaf⟩
  refine G.eq_of_locally_eq₂ (homOfLE ((ι).preimage_mono (le_of_sup_eq₀ β hcov)))
    (homOfLE ((ι).preimage_mono (le_of_sup_eq₁ β hcov))) (by
      rw [← Scheme.Hom.preimage_sup, hcov]) _ _ ?_ ?_
  · change (Sections.pullback ι τ).restrict (ι.preimage_mono (le_of_sup_eq₀ β hcov)) =
      (z.restrict le_top).restrict (ι.preimage_mono (le_of_sup_eq₀ β hcov))
    rw [← Sections.pullback_restrict L m ι (le_of_sup_eq₀ β hcov)]
    have : (τ.restrict (le_of_sup_eq₀ β hcov)) = (show L.Sections m U₀ from x₀) := by
      rw [← hτ₀]
      ext i
      simp only [Sections.coeff_restrict, τ]
      exact Cohomology.presheaf_map_map (unitModule X) _ _ _ _
    rw [this, hx₀]
    ext i
    simp only [Sections.coeff_restrict]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · change (Sections.pullback ι τ).restrict (ι.preimage_mono (le_of_sup_eq₁ β hcov)) =
      (z.restrict le_top).restrict (ι.preimage_mono (le_of_sup_eq₁ β hcov))
    rw [← Sections.pullback_restrict L m ι (le_of_sup_eq₁ β hcov)]
    have : (τ.restrict (le_of_sup_eq₁ β hcov)) = (show L.Sections m U₁ from x₁) := by
      rw [← hτ₁]
      ext i
      simp only [Sections.coeff_restrict, τ]
      exact Cohomology.presheaf_map_map (unitModule X) _ _ _ _
    rw [this, hx₁]
    ext i
    simp only [Sections.coeff_restrict]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

end Lift

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity

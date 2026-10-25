/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleOps
import DeJongAlterations.StableModification.Omega.Dualizing

/-!
# Line-bundle data of an invertible module

Blueprint `sm-projectivity-core.tex`, `lem:sm-lbd-of-invertible` (PLAN-OM3 M1). An `𝒪_X`-module
`M` which is invertible in the sense of `Omega.IsInvertibleModule` (locally on affine charts
`Spec Γ(X, W) ⟶ X` isomorphic to `𝒪`) has local free generators: for every point there is an
open `W ∋ x` and `σ ∈ Γ(W, M)` such that `r ↦ r · σ|_V` is bijective `Γ(V, 𝒪_X) → Γ(V, M)` for
every open `V ⊆ W` (`exists_isFreeGenerator`). The ratios of the generators on overlaps are units
forming a cocycle (`LocalGenerators.toLineBundleData`), and the line bundle of this cocycle is
`M` again: `LocalGenerators.twistIso : 𝒪_X ⊗ 𝓛 ≅ M` (coefficients with respect to the local
generators).

* `IsFreeGenerator M σ`, `IsFreeGenerator.coord` (the coefficient of a section);
* `exists_isFreeGenerator`, `LocalGenerators.ofIsInvertibleModule`;
* `LocalGenerators.toLineBundleData`, `LocalGenerators.twistIso`;
* `ofInvertible M hM`, `ofInvertible_twistIso : (ofInvertible M hM).twist 𝒪 1 ≅ M`.

This is how the relative dualizing sheaf `ω_{C'/S'}` (invertible by
`Omega.isInvertibleModule_dualizingSheaf_of_isNodalCurve`, Temkin §1.2, T:1691–1712) becomes
line-bundle data in the projectivity route (lane OM3D).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {X : Scheme.{u}} (M : X.Modules)

/-! ### Free generators -/

/-- `σ ∈ Γ(W, M)` **freely generates** `M` over every open `V ⊆ W`: `r ↦ r · σ|_V` is a
bijection `Γ(V, 𝒪_X) → Γ(V, M)`. -/
def IsFreeGenerator {W : X.Opens} (σ : Γ(M, W)) : Prop :=
  ∀ (V : X.Opens) (hV : V ≤ W),
    Function.Bijective (fun r : Γ(X, V) => r • M.presheaf.map (homOfLE hV).op σ)

namespace IsFreeGenerator

variable {M} {W : X.Opens} {σ : Γ(M, W)} (h : IsFreeGenerator M σ)

/-- The coefficient of a section `m ∈ Γ(V, M)` with respect to the free generator `σ|_V`. -/
def coord {V : X.Opens} (hV : V ≤ W) (m : Γ(M, V)) : Γ(X, V) :=
  (Equiv.ofBijective _ (h V hV)).symm m

include h in
lemma coord_smul {V : X.Opens} (hV : V ≤ W) (m : Γ(M, V)) :
    h.coord hV m • M.presheaf.map (homOfLE hV).op σ = m :=
  (Equiv.ofBijective _ (h V hV)).apply_symm_apply m

include h in
lemma coord_eq_iff {V : X.Opens} (hV : V ≤ W) (m : Γ(M, V)) (r : Γ(X, V)) :
    h.coord hV m = r ↔ r • M.presheaf.map (homOfLE hV).op σ = m := by
  constructor
  · rintro rfl
    exact h.coord_smul hV m
  · intro hr
    exact (h V hV).1 ((h.coord_smul hV m).trans hr.symm)

include h in
lemma eq_of_smul_eq {V : X.Opens} (hV : V ≤ W) {r r' : Γ(X, V)}
    (e : r • M.presheaf.map (homOfLE hV).op σ = r' • M.presheaf.map (homOfLE hV).op σ) :
    r = r' :=
  (h V hV).1 e

include h in
/-- Coefficients commute with restriction. -/
lemma coord_restrict {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ V) (m : Γ(M, V)) :
    h.coord (hV'.trans hV) (M.presheaf.map (homOfLE hV').op m) =
      X.presheaf.map (homOfLE hV').op (h.coord hV m) := by
  rw [h.coord_eq_iff]
  conv_rhs => rw [← h.coord_smul hV m]
  rw [Scheme.Modules.map_smul, Cohomology.presheaf_map_map M _ _ (hV'.trans hV)]

include h in
/-- The restricted coefficient times the restricted generator is the restricted section. -/
lemma res_coord_smul {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ V) (m : Γ(M, V)) :
    X.presheaf.map (homOfLE hV').op (h.coord hV m) •
        M.presheaf.map (homOfLE (hV'.trans hV)).op σ =
      M.presheaf.map (homOfLE hV').op m := by
  rw [← h.coord_restrict hV hV' m, h.coord_smul]

include h in
lemma coord_add {V : X.Opens} (hV : V ≤ W) (m m' : Γ(M, V)) :
    h.coord hV (m + m') = h.coord hV m + h.coord hV m' := by
  rw [h.coord_eq_iff, add_smul, h.coord_smul, h.coord_smul]

include h in
lemma coord_smul_left {V : X.Opens} (hV : V ≤ W) (r : Γ(X, V)) (m : Γ(M, V)) :
    h.coord hV (r • m) = r * h.coord hV m := by
  rw [h.coord_eq_iff, mul_smul, h.coord_smul]

include h in
/-- A free generator restricts to a free generator. -/
lemma restrict {W' : X.Opens} (hW' : W' ≤ W) :
    IsFreeGenerator M (M.presheaf.map (homOfLE hW').op σ) := by
  intro V hV
  have e : M.presheaf.map (homOfLE hV).op (M.presheaf.map (homOfLE hW').op σ) =
      M.presheaf.map (homOfLE (hV.trans hW')).op σ :=
    Cohomology.presheaf_map_map M _ _ _ σ
  simp only [e]
  exact h V (hV.trans hW')

end IsFreeGenerator

/-! ### Invertible modules have local free generators -/

section Generators

variable {M}

set_option backward.isDefEq.respectTransparency false in
/-- On the image of an affine chart `j = fromSpec : Spec Γ(X, W) ⟶ X` along which `M ≅ 𝒪`, the
section corresponding to `1` freely generates `M` over every open of the form `j(V')`. -/
lemma isFreeGenerator_image {W : X.Opens} (hW : IsAffineOpen W)
    (e : M.restrict hW.fromSpec ≅ SheafOfModules.unit _) (V' : (Spec Γ(X, W)).Opens) :
    Function.Bijective (fun r : Γ(X, hW.fromSpec ''ᵁ V') => r •
      M.presheaf.map (homOfLE (hW.fromSpec.image_mono (le_top : V' ≤ ⊤))).op
        (e.inv.app ⊤ (1 : Γ(Spec Γ(X, W), ⊤)) : Γ(M, hW.fromSpec ''ᵁ ⊤))) := by
  have key : (fun r : Γ(X, hW.fromSpec ''ᵁ V') => r •
      M.presheaf.map (homOfLE (hW.fromSpec.image_mono (le_top : V' ≤ ⊤))).op
        (e.inv.app ⊤ (1 : Γ(Spec Γ(X, W), ⊤)) : Γ(M, hW.fromSpec ''ᵁ ⊤))) =
      (fun r => (e.inv.app V' ((hW.fromSpec.appIso V').hom r : Γ(Spec Γ(X, W), V')) :
        Γ(M, hW.fromSpec ''ᵁ V'))) := by
    funext r
    have h1 : e.inv.app V' ((hW.fromSpec.appIso V').hom r : Γ(Spec Γ(X, W), V')) =
        ((hW.fromSpec.appIso V').hom r : Γ(Spec Γ(X, W), V')) •
          e.inv.app V' (1 : Γ(Spec Γ(X, W), V')) := by
      rw [← Scheme.Modules.Hom.app_smul]
      congr 1
      exact (mul_one ((hW.fromSpec.appIso V').hom r : Γ(Spec Γ(X, W), V'))).symm
    have h1' : (Scheme.Modules.presheaf (X := Spec Γ(X, W))
        (SheafOfModules.unit (Spec Γ(X, W)).ringCatSheaf)).map (homOfLE (le_top : V' ≤ ⊤)).op
          (1 : Γ(Spec Γ(X, W), ⊤)) = (1 : Γ(Spec Γ(X, W), V')) :=
      map_one ((Spec Γ(X, W)).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op).hom
    have h2 : e.inv.app V' (1 : Γ(Spec Γ(X, W), V')) =
        (M.restrict hW.fromSpec).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
          (e.inv.app ⊤ (1 : Γ(Spec Γ(X, W), ⊤))) := by
      have := ConcreteCategory.congr_hom (e.inv.mapPresheaf.naturality (homOfLE (le_top :
        V' ≤ ⊤)).op) (1 : Γ(Spec Γ(X, W), ⊤))
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h1'] at this
      exact this
    have hr : (hW.fromSpec.appIso V').inv ((hW.fromSpec.appIso V').hom r) = r := by
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
    simp only
    rw [h1, h2]
    nth_rewrite 1 [← hr]
    rfl
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso (e.inv.app V')).comp
    (ConcreteCategory.bijective_of_isIso (hW.fromSpec.appIso V').hom)

/-- **Invertible modules have local free generators.** -/
theorem exists_isFreeGenerator (hM : Omega.IsInvertibleModule M) (x : X) :
    ∃ (W : X.Opens) (σ : Γ(M, W)), x ∈ W ∧ IsFreeGenerator M σ := by
  obtain ⟨W, hW, hxW, ⟨e⟩⟩ := hM x
  let j := hW.fromSpec
  refine ⟨j ''ᵁ ⊤, (e.inv.app ⊤ (1 : Γ(Spec Γ(X, W), ⊤)) : Γ(M, j ''ᵁ ⊤)), ?_, ?_⟩
  · rw [Scheme.Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
    exact hxW
  · intro V hV
    have hVeq : j ''ᵁ (j ⁻¹ᵁ V) = V := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_top_eq_opensRange]
      exact inf_eq_right.mpr hV
    have H : ∀ (V₀ : X.Opens) (_ : V₀ = j ''ᵁ (j ⁻¹ᵁ V)) (hV₀ : V₀ ≤ j ''ᵁ ⊤),
        Function.Bijective (fun r : Γ(X, V₀) => r •
          M.presheaf.map (homOfLE hV₀).op
            (e.inv.app ⊤ (1 : Γ(Spec Γ(X, W), ⊤)) : Γ(M, j ''ᵁ ⊤))) := by
      rintro V₀ rfl hV₀
      exact isFreeGenerator_image hW e (j ⁻¹ᵁ V)
    exact H V hVeq.symm hV

end Generators

/-! ### The cocycle of local generators -/

/-- A family of **local free generators** of a module `M` on an open cover. -/
structure LocalGenerators (M : X.Modules) where
  /-- The index type. -/
  ι : Type u
  /-- The opens. -/
  U : ι → X.Opens
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The generators. -/
  σ : ∀ i, Γ(M, U i)
  free : ∀ i, IsFreeGenerator M (σ i)

namespace LocalGenerators

variable {M}

/-- The local free generators of an invertible module, indexed by the points. -/
def ofIsInvertibleModule (hM : Omega.IsInvertibleModule M) : LocalGenerators M where
  ι := X
  U x := (exists_isFreeGenerator hM x).choose
  iSup_eq_top := by
    refine eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, ?_⟩
    exact (exists_isFreeGenerator hM x).choose_spec.choose_spec.1
  σ x := (exists_isFreeGenerator hM x).choose_spec.choose
  free x := (exists_isFreeGenerator hM x).choose_spec.choose_spec.2

variable (G : LocalGenerators M)

/-- The transition function: `σ j = t i j · σ i` on `U i ∩ U j`. -/
def transFun (i j : G.ι) : Γ(X, G.U i ⊓ G.U j) :=
  (G.free i).coord inf_le_left (M.presheaf.map (homOfLE inf_le_right).op (G.σ j))

lemma transFun_spec (i j : G.ι) :
    G.transFun i j • M.presheaf.map (homOfLE (inf_le_left : G.U i ⊓ G.U j ≤ G.U i)).op (G.σ i) =
      M.presheaf.map (homOfLE (inf_le_right : G.U i ⊓ G.U j ≤ G.U j)).op (G.σ j) :=
  (G.free i).coord_smul _ _

/-- Restricted form of `transFun_spec`. -/
lemma transFun_spec' (i j : G.ι) {V : X.Opens} (hV : V ≤ G.U i ⊓ G.U j) :
    X.presheaf.map (homOfLE hV).op (G.transFun i j) •
        M.presheaf.map (homOfLE (hV.trans inf_le_left)).op (G.σ i) =
      M.presheaf.map (homOfLE (hV.trans inf_le_right)).op (G.σ j) := by
  have e := congrArg (M.presheaf.map (homOfLE hV).op) (G.transFun_spec i j)
  rwa [Scheme.Modules.map_smul, Cohomology.presheaf_map_map M _ _ (hV.trans inf_le_left),
    Cohomology.presheaf_map_map M _ _ (hV.trans inf_le_right)] at e

lemma transFun_mul_transFun (i j k : G.ι) {V : X.Opens} (h₁ : V ≤ G.U i ⊓ G.U j)
    (h₂ : V ≤ G.U j ⊓ G.U k) (h₃ : V ≤ G.U i ⊓ G.U k) :
    X.presheaf.map (homOfLE h₁).op (G.transFun i j) *
      X.presheaf.map (homOfLE h₂).op (G.transFun j k) =
        X.presheaf.map (homOfLE h₃).op (G.transFun i k) := by
  have hVi : V ≤ G.U i := h₁.trans inf_le_left
  apply (G.free i).eq_of_smul_eq hVi
  rw [mul_comm, mul_smul, G.transFun_spec' i j h₁, G.transFun_spec' j k h₂,
    G.transFun_spec' i k h₃]

lemma transFun_self (i : G.ι) {V : X.Opens} (h : V ≤ G.U i ⊓ G.U i) :
    X.presheaf.map (homOfLE h).op (G.transFun i i) = 1 := by
  apply (G.free i).eq_of_smul_eq (h.trans inf_le_left)
  rw [G.transFun_spec' i i h, one_smul]

/-- The transition units. -/
def transUnit (i j : G.ι) : Γ(X, G.U i ⊓ G.U j)ˣ :=
  Units.mkOfMulEqOne (G.transFun i j)
    (X.presheaf.map (homOfLE (le_inf inf_le_right inf_le_left : G.U i ⊓ G.U j ≤ G.U j ⊓ G.U i)).op
      (G.transFun j i)) (by
    have e := G.transFun_mul_transFun i j i (V := G.U i ⊓ G.U j) le_rfl
      (le_inf inf_le_right inf_le_left) (le_inf inf_le_left inf_le_left)
    rw [ringMap_self', G.transFun_self] at e
    exact e)

/-- **The line-bundle data of local free generators**: transition units `σ j = u i j · σ i`. -/
abbrev toLineBundleData : LineBundleData X where
  ι := G.ι
  U := G.U
  iSup_eq_top := G.iSup_eq_top
  u := G.transUnit
  cocycle i j k := by
    change X.presheaf.map _ (G.transFun i j) * X.presheaf.map _ (G.transFun j k) =
      X.presheaf.map _ (G.transFun i k)
    exact G.transFun_mul_transFun i j k _ _ _

lemma toLineBundleData_trans {i j : G.ι} {V : X.Opens} (h : V ≤ G.U i ⊓ G.U j) :
    (G.toLineBundleData.trans (i := i) (j := j) h : Γ(X, V)) =
      X.presheaf.map (homOfLE h).op (G.transFun i j) :=
  rfl

/-! ### The twist of the structure sheaf is `M` -/

/-- The `i`-th coefficient of a section of `M` over `W`. -/
abbrev coeffAt (W : X.Opens) (m : Γ(M, W)) (i : G.ι) : Γ(X, W ⊓ G.U i) :=
  (G.free i).coord (inf_le_right : W ⊓ G.U i ≤ G.U i)
    (M.presheaf.map (homOfLE (inf_le_left : W ⊓ G.U i ≤ W)).op m)

lemma coeffAt_smul (W : X.Opens) (m : Γ(M, W)) (i : G.ι) {V : X.Opens} (hV : V ≤ W ⊓ G.U i) :
    X.presheaf.map (homOfLE hV).op (G.coeffAt W m i) •
        M.presheaf.map (homOfLE (hV.trans inf_le_right)).op (G.σ i) =
      M.presheaf.map (homOfLE (hV.trans inf_le_left)).op m := by
  rw [(G.free i).res_coord_smul, Cohomology.presheaf_map_map M _ _ (hV.trans inf_le_left)]

/-- The coefficients of a section of `M` over `W` with respect to the local generators, a section
of `𝒪_X ⊗ 𝓛`. -/
def coeffs (W : X.Opens) (m : Γ(M, W)) :
    G.toLineBundleData.twistSubgroup (unitModule X) 1 W :=
  ⟨fun i => G.coeffAt W m i, by
    intro i j
    change X.presheaf.map (homOfLE (G.toLineBundleData.le_left W i j)).op (G.coeffAt W m i) =
      G.toLineBundleData.transPow 1 W i j *
        X.presheaf.map (homOfLE (G.toLineBundleData.le_right W i j)).op (G.coeffAt W m j)
    have hT : G.toLineBundleData.transPow 1 W i j =
        X.presheaf.map (homOfLE (inf_le_right : W ⊓ (G.U i ⊓ G.U j) ≤ G.U i ⊓ G.U j)).op
          (G.transFun i j) := by
      simp only [LineBundleData.transPow, zpow_one]
      rfl
    rw [hT]
    have hVi : W ⊓ (G.U i ⊓ G.U j) ≤ G.U i := inf_le_right.trans inf_le_left
    apply (G.free i).eq_of_smul_eq hVi
    rw [G.coeffAt_smul W m i (G.toLineBundleData.le_left W i j), mul_comm, mul_smul,
      G.transFun_spec' i j inf_le_right,
      G.coeffAt_smul W m j (G.toLineBundleData.le_right W i j)]⟩

lemma coeffs_apply (W : X.Opens) (m : Γ(M, W)) (i : G.ι) :
    (G.coeffs W m).1 i = G.coeffAt W m i :=
  rfl

lemma coeffs_injective (W : X.Opens) : Function.Injective (G.coeffs W) := by
  intro m m' h
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine F.eq_of_locally_eq' (fun i => W ⊓ G.U i) W (fun i => homOfLE inf_le_left) ?_ m m'
    (fun i => ?_)
  · intro x hx
    have hx' : x ∈ (⊤ : X.Opens) := trivial
    rw [← G.iSup_eq_top] at hx'
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · have hi := congrFun (congrArg Subtype.val h) i
    change G.coeffAt W m i = G.coeffAt W m' i at hi
    rw [← (G.free i).coord_smul (inf_le_right : W ⊓ G.U i ≤ G.U i)
        (M.presheaf.map (homOfLE (inf_le_left : W ⊓ G.U i ≤ W)).op m),
      ← (G.free i).coord_smul (inf_le_right : W ⊓ G.U i ≤ G.U i)
        (M.presheaf.map (homOfLE (inf_le_left : W ⊓ G.U i ≤ W)).op m')]
    exact congrArg (· • _) hi

lemma coeffs_surjective (W : X.Opens) : Function.Surjective (G.coeffs W) := by
  intro t
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let s : G.toLineBundleData.Sections 1 W := LineBundleData.Sections.ofTwist t
  let A : ∀ i, Γ(M, W ⊓ G.U i) := fun i =>
    s.coeff i • M.presheaf.map (homOfLE (inf_le_right : W ⊓ G.U i ≤ G.U i)).op (G.σ i)
  have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun i => W ⊓ G.U i) A := by
    intro i j
    have hle : (W ⊓ G.U i) ⊓ (W ⊓ G.U j) ≤ W ⊓ (G.U i ⊓ G.U j) :=
      fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
    have hV : (W ⊓ G.U i) ⊓ (W ⊓ G.U j) ≤ G.U i ⊓ G.U j := hle.trans inf_le_right
    have ht : X.presheaf.map (homOfLE (inf_le_left : (W ⊓ G.U i) ⊓ (W ⊓ G.U j) ≤ W ⊓ G.U i)).op
        (s.coeff i) = X.presheaf.map (homOfLE hV).op (G.transFun i j) *
          X.presheaf.map (homOfLE (inf_le_right : (W ⊓ G.U i) ⊓ (W ⊓ G.U j) ≤ W ⊓ G.U j)).op
            (s.coeff j) := by
      have := congrArg (X.presheaf.map (homOfLE hle).op) (s.coeff_compat i j)
      simp only [LineBundleData.transPow, zpow_one] at this
      rw [ringMap_map_trans, map_mul, ringMap_map_trans, toLineBundleData_trans,
        ringMap_map_trans] at this
      exact this
    change M.presheaf.map (homOfLE (inf_le_left : (W ⊓ G.U i) ⊓ (W ⊓ G.U j) ≤ W ⊓ G.U i)).op
        (s.coeff i • _) =
      M.presheaf.map (homOfLE (inf_le_right : (W ⊓ G.U i) ⊓ (W ⊓ G.U j) ≤ W ⊓ G.U j)).op
        (s.coeff j • _)
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul,
      Cohomology.presheaf_map_map M _ _ (inf_le_left.trans inf_le_right),
      Cohomology.presheaf_map_map M _ _ (inf_le_right.trans inf_le_right), ht, mul_comm,
      mul_smul, G.transFun_spec' i j hV]
  have hcov : W ≤ ⨆ i, W ⊓ G.U i := by
    intro x hx
    have hx' : x ∈ (⊤ : X.Opens) := trivial
    rw [← G.iSup_eq_top] at hx'
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  obtain ⟨m, hm, -⟩ := F.existsUnique_gluing' (fun i => W ⊓ G.U i) W
    (fun i => homOfLE inf_le_left) hcov A hcompat
  refine ⟨m, Subtype.ext (funext fun i => ?_)⟩
  exact ((G.free i).coord_eq_iff _ _ _).mpr (hm i).symm

lemma coeffAt_add (W : X.Opens) (m m' : Γ(M, W)) (i : G.ι) :
    G.coeffAt W (m + m') i = G.coeffAt W m i + G.coeffAt W m' i := by
  show (G.free i).coord _ (M.presheaf.map _ (m + m')) =
    (G.free i).coord _ (M.presheaf.map _ m) + (G.free i).coord _ (M.presheaf.map _ m')
  rw [map_add, (G.free i).coord_add]

lemma coeffAt_zero (W : X.Opens) (i : G.ι) : G.coeffAt W 0 i = 0 := by
  show (G.free i).coord _ (M.presheaf.map _ 0) = 0
  rw [map_zero, (G.free i).coord_eq_iff, zero_smul]

lemma coeffAt_smul_left (W : X.Opens) (r : Γ(X, W)) (m : Γ(M, W)) (i : G.ι) :
    G.coeffAt W (r • m) i =
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ G.U i ≤ W)).op r * G.coeffAt W m i := by
  show (G.free i).coord _ (M.presheaf.map _ (r • m)) = _ * (G.free i).coord _ (M.presheaf.map _ m)
  rw [Scheme.Modules.map_smul, (G.free i).coord_smul_left]

lemma coeffAt_restrict {W W' : X.Opens} (h : W' ≤ W) (m : Γ(M, W)) (i : G.ι) :
    G.coeffAt W' (M.presheaf.map (homOfLE h).op m) i =
      X.presheaf.map (homOfLE (inf_le_inf_right (G.U i) h)).op (G.coeffAt W m i) := by
  show (G.free i).coord _ (M.presheaf.map _ (M.presheaf.map _ m)) =
    X.presheaf.map _ ((G.free i).coord _ (M.presheaf.map _ m))
  rw [← (G.free i).coord_restrict]
  congr 1
  exact (Cohomology.presheaf_map_map M _ _ (inf_le_left.trans h : W' ⊓ G.U i ≤ W) m).trans
    (Cohomology.presheaf_map_map M _ _ (inf_le_left.trans h : W' ⊓ G.U i ≤ W) m).symm

/-- `coeffs` as an additive map. -/
def coeffsHom (W : X.Opens) :
    Γ(M, W) →+ G.toLineBundleData.twistSubgroup (unitModule X) 1 W where
  toFun := G.coeffs W
  map_zero' := Subtype.ext (funext fun i => G.coeffAt_zero W i)
  map_add' m m' := Subtype.ext (funext fun i => G.coeffAt_add W m m' i)

/-- The morphism `M ⟶ 𝒪_X ⊗ 𝓛` taking coefficients with respect to the local generators. -/
def toTwist : M ⟶ G.toLineBundleData.twist (unitModule X) 1 where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (G.coeffsHom W.unop)
      naturality := fun {W W'} k => by
        ext m
        apply Subtype.ext
        funext i
        exact G.coeffAt_restrict (leOfHom k.unop) m i }
    (fun W r m => by
      apply Subtype.ext
      funext i
      exact G.coeffAt_smul_left W.unop r m i)

instance : IsIso G.toTwist := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨G.coeffs_injective W, G.coeffs_surjective W⟩

/-- **The line bundle of local free generators is the module**: `𝒪_X ⊗ 𝓛 ≅ M`. -/
def twistIso : G.toLineBundleData.twist (unitModule X) 1 ≅ M :=
  (asIso G.toTwist).symm

end LocalGenerators

namespace LineBundleData

variable {M}

/-- **Line-bundle data of an invertible module** (blueprint `lem:sm-lbd-of-invertible`). -/
def ofInvertible (hM : Omega.IsInvertibleModule M) : LineBundleData X :=
  (LocalGenerators.ofIsInvertibleModule hM).toLineBundleData

/-- The line bundle of `ofInvertible M hM` is `M`: `𝒪_X ⊗ 𝓛 ≅ M`. -/
def ofInvertibleTwistIso (hM : Omega.IsInvertibleModule M) :
    (ofInvertible hM).twist (unitModule X) 1 ≅ M :=
  (LocalGenerators.ofIsInvertibleModule hM).twistIso

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity

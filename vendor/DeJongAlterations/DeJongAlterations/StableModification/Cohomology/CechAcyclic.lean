/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechComplex
import DeJongAlterations.Geometry.ProperSteinProjectiveCechAffineDenominators
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Acyclicity of Čech complexes of quasi-coherent modules on affine schemes

Let `F` be a quasi-coherent module on a scheme `X`, `V` an affine open and `U : ι → X.Opens` a
finite family with `V ⊆ ⋃ U_i` such that every `V ∩ U_T` is affine. Then the augmented Čech
complex of the diagram `T ↦ Γ(F, V ∩ U_T)` (including the term `Γ(F, V)` for `T = ∅`) is exact
(`linkDiagram_exact`). In particular the Čech cohomology of a finite affine cover of an affine
scheme vanishes in positive degrees (`isZero_cechCohomology_of_isAffine`). Blueprint:
`sm-cohomology-cech.tex`, `lem:sm-cech-cone`, `lem:sm-cech-local`, `lem:sm-qcoh-localization`,
`prop:sm-cech-affine`. This is the standard input of Čech theory (Hartshorne III.4.2-4.3 in the
Noetherian case, Stacks 01X9 in general); the proof here is by localization:

* `subsetCech_exact_of_cone`: if one index `i₀` is a *cone vertex* of a diagram `D`, i.e.
  `D(T) → D(T ∪ {i₀})` is bijective for all `T ∌ i₀`, the total Čech cube of `D` is exact
  (explicit contracting homotopy).
* `subsetCech_exact_of_isLocalized_span`: exactness of the total cube is local on the ring
  (Mathlib's `exact_of_isLocalized_span` together with `IsLocalizedModule.pi`).
* `isLocalizedModule_restrict_basicOpen`: for `F` quasi-coherent, `W` affine and `f ∈ Γ(X, W)`,
  the restriction `Γ(F, W) → Γ(F, D(f))` is a localization at `f` (Mathlib's `tilde` theory,
  transported along `IsAffineOpen.fromSpec`).
* `linkDiagram_exact`: localize at the `f ∈ Γ(X, V)` with `D(f)` inside some `U_i`; there `i` is a
  cone vertex.

The exactness statement is about the underlying additive maps; it is formulated for the total
cube of the diagram (all finite subsets at once), which by `CechComplex` gives the vanishing of
Čech cohomology in positive degrees.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section Cone

variable {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι]
  (D : Finset ι ⥤ ModuleCat.{u} R) (i₀ : ι)

/-- The sign `(-1)^{#{j ∈ T | j < i₀}}` of the position of `i₀` in `T ∪ {i₀}`. -/
def coneSign (T : Finset ι) : ℤ := (-1) ^ (T.filter (fun j => j < i₀)).card

lemma coneSign_mul_self (T : Finset ι) : coneSign i₀ T * coneSign i₀ T = 1 := by
  unfold coneSign
  rw [← mul_pow]
  norm_num

lemma subsetCechSign_insert_self (T : Finset ι) :
    subsetCechSign (insert i₀ T) i₀ = coneSign i₀ T := by
  unfold subsetCechSign coneSign
  rw [Finset.filter_insert, if_neg (lt_irrefl i₀)]

lemma subsetCechSign_insert_of_notMem {T : Finset ι} (hT : i₀ ∉ T) (i : ι) :
    subsetCechSign (insert i₀ T) i = (if i₀ < i then -1 else 1) * subsetCechSign T i := by
  unfold subsetCechSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hT]), pow_succ]
    ring
  · ring

lemma coneSign_erase {T : Finset ι} {i : ι} (hi : i ∈ T) :
    coneSign i₀ (T.erase i) = (if i < i₀ then -1 else 1) * coneSign i₀ T := by
  unfold coneSign
  rw [Finset.filter_erase]
  split_ifs with h
  · have hmem : i ∈ T.filter (fun j => j < i₀) := Finset.mem_filter.mpr ⟨hi, h⟩
    have hcard := Finset.card_erase_add_one hmem
    rw [← hcard, pow_succ]
    ring
  · rw [Finset.erase_eq_of_notMem (by simp [h])]
    ring

variable {D i₀}

variable (hcone : ∀ T, i₀ ∉ T →
  Function.Bijective (subsetCechRestriction D (Finset.subset_insert i₀ T)))

include hcone

/-- The bijection `D(T) ≃ D(T ∪ {i₀})` at a cone vertex. -/
def coneEquiv (T : Finset ι) (hT : i₀ ∉ T) : D.obj T ≃ₗ[R] D.obj (insert i₀ T) :=
  LinearEquiv.ofBijective _ (hcone T hT)

lemma coneEquiv_apply (T : Finset ι) (hT : i₀ ∉ T) (x : D.obj T) :
    coneEquiv hcone T hT x = subsetCechRestriction D (Finset.subset_insert i₀ T) x :=
  rfl

/-- Restricting the inverse of the cone bijection is restricting from `T ∪ {i₀}`. -/
lemma subsetCechRestriction_coneEquiv_symm {T S : Finset ι} (hT : i₀ ∉ T) (hTS : T ⊆ S)
    (hiS : insert i₀ T ⊆ S) (y : D.obj (insert i₀ T)) :
    subsetCechRestriction D hTS ((coneEquiv hcone T hT).symm y) =
      subsetCechRestriction D hiS y := by
  conv_rhs => rw [← (coneEquiv hcone T hT).apply_symm_apply y]
  rw [coneEquiv_apply, subsetCechRestriction_comp]

/-- The contracting homotopy at a cone vertex:
`(h x)_T = ε(T) · (x_{T ∪ i₀})|_T` for `i₀ ∉ T`, and `0` for `i₀ ∈ T`. -/
def coneHomotopy (x : subsetCechCube D) : subsetCechCube D := fun T =>
  if h : i₀ ∈ T then 0 else coneSign i₀ T • (coneEquiv hcone T h).symm (x (insert i₀ T))

lemma coneHomotopy_zero : coneHomotopy hcone (0 : subsetCechCube D) = 0 := by
  funext T
  simp only [coneHomotopy]
  split_ifs
  · rfl
  · change coneSign i₀ T • (coneEquiv hcone T _).symm 0 = 0
    rw [map_zero, smul_zero]

lemma coneHomotopy_of_mem (x : subsetCechCube D) {T : Finset ι} (h : i₀ ∈ T) :
    coneHomotopy hcone x T = 0 := by
  simp only [coneHomotopy, dif_pos h]

lemma coneHomotopy_of_notMem (x : subsetCechCube D) {T : Finset ι} (h : i₀ ∉ T) :
    coneHomotopy hcone x T = coneSign i₀ T • (coneEquiv hcone T h).symm (x (insert i₀ T)) := by
  simp only [coneHomotopy, dif_neg h]

/-- `d h + h d = id` on the total cube. -/
theorem coneHomotopy_spec (x : subsetCechCube D) :
    subsetCechDifferential D (coneHomotopy hcone x) +
      coneHomotopy hcone (subsetCechDifferential D x) = x := by
  classical
  funext T
  by_cases hT : i₀ ∈ T
  · -- `T = S ∪ {i₀}`; only the deletion of `i₀` survives
    rw [Pi.add_apply, coneHomotopy_of_mem hcone _ hT, add_zero, subsetCechDifferential_apply]
    rw [← Finset.add_sum_erase T _ hT]
    have hrest : ∑ i ∈ T.erase i₀, subsetCechSign T i •
        subsetCechRestriction D (Finset.erase_subset i T) (coneHomotopy hcone x (T.erase i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hmem : i₀ ∈ T.erase i := Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hi).symm, hT⟩
      rw [coneHomotopy_of_mem hcone _ hmem, map_zero, smul_zero]
    rw [hrest, add_zero]
    have hS : i₀ ∉ T.erase i₀ := Finset.notMem_erase i₀ T
    rw [coneHomotopy_of_notMem hcone _ hS, map_zsmul, smul_smul]
    have hins : insert i₀ (T.erase i₀) = T := Finset.insert_erase hT
    rw [subsetCechRestriction_coneEquiv_symm hcone hS (Finset.erase_subset i₀ T) hins.le]
    have hsign : subsetCechSign T i₀ * coneSign i₀ (T.erase i₀) = 1 := by
      have := subsetCechSign_insert_self i₀ (T.erase i₀)
      rw [hins] at this
      rw [this, coneSign_mul_self]
    rw [hsign, one_smul]
    exact (subsetCechRestriction_value_congr D x hins.le (Finset.Subset.refl T) hins).trans
      (by simp [subsetCechRestriction])
  · -- `i₀ ∉ T`: compare after applying the cone bijection
    apply (hcone T hT).1
    rw [Pi.add_apply, map_add, coneHomotopy_of_notMem hcone _ hT, map_zsmul]
    change _ + coneSign i₀ T • (coneEquiv hcone T hT) ((coneEquiv hcone T hT).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    -- expand the differential at `T ∪ {i₀}`
    rw [subsetCechDifferential_apply (c := x) (S := insert i₀ T), Finset.sum_insert hT,
      subsetCechSign_insert_self i₀ T, smul_add, smul_smul, coneSign_mul_self, one_smul]
    have hfirst : subsetCechRestriction D (Finset.erase_subset i₀ (insert i₀ T))
        (x ((insert i₀ T).erase i₀)) =
        subsetCechRestriction D (Finset.subset_insert i₀ T) (x T) :=
      subsetCechRestriction_value_congr D x _ _ (Finset.erase_insert hT)
    rw [hfirst]
    -- the remaining sums cancel
    rw [subsetCechDifferential_apply, map_sum, Finset.smul_sum, add_comm, add_assoc,
      ← Finset.sum_add_distrib]
    conv_rhs => rw [← add_zero (subsetCechRestriction D (Finset.subset_insert i₀ T) (x T))]
    congr 1
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ i₀ := fun h => hT (h ▸ hi)
    have hiS : i₀ ∉ T.erase i := fun h => hT (Finset.mem_of_mem_erase h)
    rw [coneHomotopy_of_notMem hcone _ hiS, map_zsmul, map_zsmul, map_zsmul,
      subsetCechRestriction_comp]
    have hins : insert i₀ (T.erase i) = (insert i₀ T).erase i :=
      (Finset.erase_insert_of_ne hne.symm).symm
    rw [subsetCechRestriction_coneEquiv_symm hcone hiS
      ((Finset.erase_subset i T).trans (Finset.subset_insert i₀ T))
      (Finset.insert_subset_insert i₀ (Finset.erase_subset i T))]
    rw [subsetCechRestriction_value_congr D x
      (Finset.insert_subset_insert i₀ (Finset.erase_subset i T))
      (Finset.erase_subset i (insert i₀ T)) hins]
    rw [smul_smul, smul_smul, ← add_smul]
    convert zero_smul ℤ _
    rw [subsetCechSign_insert_of_notMem i₀ hT i, coneSign_erase i₀ hi]
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h, if_neg (not_lt_of_gt h)]
      ring
    · rw [if_neg (not_lt_of_gt h), if_pos h]
      ring

/-- **Cone lemma** (blueprint `lem:sm-cech-cone`): at a cone vertex the total Čech cube is
exact. -/
theorem subsetCech_exact_of_cone :
    Function.Exact (subsetCechDifferential D) (subsetCechDifferential D) := by
  intro y
  constructor
  · intro hy
    refine ⟨coneHomotopy hcone y, ?_⟩
    have := coneHomotopy_spec hcone y
    rw [hy, coneHomotopy_zero hcone, add_zero] at this
    exact this
  · rintro ⟨z, rfl⟩
    exact subsetCechDifferential_squared D z

end Cone

section Local

variable {A : Type u} [CommRing A] {ι : Type u} [LinearOrder ι] [Finite ι]

/-- **Exactness is local** (blueprint `lem:sm-cech-local`): if `s` spans the unit ideal and for
each `r ∈ s` the diagram `D` maps componentwise by localizations at `r` to a diagram with exact
total cube, then the total cube of `D` is exact. -/
theorem subsetCech_exact_of_isLocalized_span (D : Finset ι ⥤ ModuleCat.{u} A) (s : Set A)
    (hs : Ideal.span s = ⊤) (Dr : s → Finset ι ⥤ ModuleCat.{u} A) (lr : ∀ r, D ⟶ Dr r)
    (hloc : ∀ r T, IsLocalizedModule (Submonoid.powers r.1) ((lr r).app T).hom)
    (hex : ∀ r, Function.Exact (subsetCechDifferential (Dr r)) (subsetCechDifferential (Dr r))) :
    Function.Exact (subsetCechDifferential D) (subsetCechDifferential D) := by
  have : ∀ r : s, IsLocalizedModule.Away r.1 (subsetCechCubeMap (lr r)) := by
    intro r
    have := hloc r
    have h := IsLocalizedModule.pi (Submonoid.powers r.1) (fun T => ((lr r).app T).hom)
    exact h
  have hmap : ∀ r : s, IsLocalizedModule.map (Submonoid.powers r.1) (subsetCechCubeMap (lr r))
      (subsetCechCubeMap (lr r)) (subsetCechDifferential D) = subsetCechDifferential (Dr r) := by
    intro r
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.1) (subsetCechCubeMap (lr r))
      (subsetCechCubeMap (lr r))
    rw [IsLocalizedModule.map_comp]
    apply LinearMap.ext
    intro x
    exact subsetCechCubeMap_comm (lr r) x
  apply exact_of_isLocalized_span s hs (fun r => subsetCechCube (Dr r))
    (fun r => subsetCechCubeMap (lr r)) (fun r => subsetCechCube (Dr r))
    (fun r => subsetCechCubeMap (lr r)) (fun r => subsetCechCube (Dr r))
    (fun r => subsetCechCubeMap (lr r))
  intro r
  rw [hmap r]
  exact hex r

end Local

section QuasiCoherent

variable {X : Scheme.{u}}

lemma fromSpec_image_le {W : X.Opens} (hW : IsAffineOpen W) (U : (Spec Γ(X, W)).Opens) :
    hW.fromSpec ''ᵁ U ≤ W := by
  have := hW.fromSpec.image_le_opensRange U
  rwa [hW.opensRange_fromSpec] at this

/-- On `Spec Γ(X, W) → X`, the scalar `b ∈ Γ(X, W)` acts on the image of an open `U` as its
restriction. -/
lemma fromSpec_appIso_inv_algebraMap {W : X.Opens} (hW : IsAffineOpen W)
    (U : (Spec Γ(X, W)).Opens) (b : Γ(X, W)) :
    (hW.fromSpec.appIso U).inv (algebraMap Γ(X, W) Γ(Spec Γ(X, W), U) b) =
      X.presheaf.map (homOfLE (fromSpec_image_le hW U)).op b := by
  apply (ConcreteCategory.bijective_of_isIso (hW.fromSpec.appIso U).hom).1
  rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom', ← ConcreteCategory.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE, ConcreteCategory.comp_apply,
    IsAffineOpen.fromSpec_app_self, IsAffineOpen.algebraMap_Spec_obj]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply ((Spec Γ(X, W)).presheaf.map _),
    ← Functor.map_comp]
  rfl

variable (F : X.Modules)

/-- Restriction `Γ(F, W) → Γ(F, V)`, `V ≤ W`, as a `Γ(X, W)`-linear map, for the natural
structure on the source and restriction of scalars on the target. -/
def restrictLinearNative {V W : X.Opens} (h : V ≤ W) :
    letI := Module.compHom Γ(F, V) (X.presheaf.map (homOfLE h).op).hom
    Γ(F, W) →ₗ[Γ(X, W)] Γ(F, V) :=
  letI := Module.compHom Γ(F, V) (X.presheaf.map (homOfLE h).op).hom
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s => Scheme.Modules.map_smul F (homOfLE h) r s }

variable [F.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency.types false in
/-- Sections of a quasi-coherent module over a basic open of an affine open are the localization
(Mathlib's `tilde` theory, transported along `IsAffineOpen.fromSpec`). -/
theorem isLocalizedModule_restrictLinearNative {W : X.Opens} (hW : IsAffineOpen W)
    (g : Γ(X, W)) :
    letI := Module.compHom Γ(F, X.basicOpen g) (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
    IsLocalizedModule (Submonoid.powers g) (restrictLinearNative F (X.basicOpen_le g)) := by
  let := Module.compHom Γ(F, X.basicOpen g) (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  let j := hW.fromSpec
  let G : (Spec Γ(X, W)).Modules := F.restrict j
  have hloc := affineSectionRestriction_isLocalized G g
  have heq₀ : j ''ᵁ ⊤ = W := by
    rw [Scheme.Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have heq₁ : j ''ᵁ PrimeSpectrum.basicOpen g = X.basicOpen g := hW.fromSpec_image_basicOpen g
  let e₀ : Γ(F, W) →ₗ[Γ(X, W)] Γ(G, ⊤) :=
    { toFun := fun s => (F.presheaf.map (homOfLE heq₀.le).op s : Γ(F, j ''ᵁ ⊤))
      map_add' := map_add _
      map_smul' := by
        intro b s
        change F.presheaf.map (homOfLE heq₀.le).op (b • s) =
          (j.appIso ⊤).inv (algebraMap Γ(X, W) Γ(Spec Γ(X, W), ⊤) b) •
            (F.presheaf.map (homOfLE heq₀.le).op s : Γ(F, j ''ᵁ ⊤))
        rw [Scheme.Modules.map_smul, fromSpec_appIso_inv_algebraMap] }
  let D₀ : (Spec Γ(X, W)).Opens := PrimeSpectrum.basicOpen g
  let e₁ : Γ(G, D₀) →ₗ[Γ(X, W)] Γ(F, X.basicOpen g) :=
    { toFun := fun t => F.presheaf.map (homOfLE heq₁.ge).op (show Γ(F, j ''ᵁ D₀) from t)
      map_add' := map_add _
      map_smul' := by
        intro b t
        change F.presheaf.map (homOfLE heq₁.ge).op
            ((j.appIso D₀).inv (algebraMap Γ(X, W) Γ(Spec Γ(X, W), D₀) b) •
              (show Γ(F, j ''ᵁ D₀) from t)) =
          X.presheaf.map (homOfLE (X.basicOpen_le g)).op b •
            F.presheaf.map (homOfLE heq₁.ge).op (show Γ(F, j ''ᵁ D₀) from t)
        rw [Scheme.Modules.map_smul, fromSpec_appIso_inv_algebraMap,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }
  have he₀ : Function.Bijective e₀ :=
    Function.bijective_iff_has_inverse.mpr
      ⟨fun t => F.presheaf.map (homOfLE heq₀.ge).op (t : Γ(F, j ''ᵁ ⊤)),
        fun s => presheaf_map_map_self F _ _ s, fun t => presheaf_map_map_self F _ _ t⟩
  have he₁ : Function.Bijective e₁ :=
    Function.bijective_iff_has_inverse.mpr
      ⟨fun t => (F.presheaf.map (homOfLE heq₁.le).op t : Γ(F, j ''ᵁ D₀)),
        fun s => presheaf_map_map_self F _ _ s, fun t => presheaf_map_map_self F _ _ t⟩
  have hcomp : restrictLinearNative F (X.basicOpen_le g) =
      e₁ ∘ₗ affineSectionRestriction G g ∘ₗ e₀ := by
    apply LinearMap.ext
    intro s
    have h : j ''ᵁ D₀ ≤ W := (j.image_mono (le_top : D₀ ≤ ⊤)).trans heq₀.le
    exact ((congrArg (F.presheaf.map (homOfLE heq₁.ge).op)
      (presheaf_map_map F heq₀.le (j.image_mono (le_top : D₀ ≤ ⊤)) h s)).trans
      (presheaf_map_map F h heq₁.ge (X.basicOpen_le g) s)).symm
  rw [hcomp]
  exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers g) e₁ he₁).mpr
    ((IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers g) e₀ he₀).mpr hloc)

omit [F.IsQuasicoherent] in
/-- Two restrictions of a regular function compose to one. -/
lemma ring_presheaf_map_map {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (h₃ : V₃ ≤ V₁)
    (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE h₃).op r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Localization of sections** (blueprint `lem:sm-qcoh-localization`): for `F` quasi-coherent,
`W ≤ V₀` affine, `c : A →+* Γ(X, V₀)` and `f ∈ A`, the restriction
`Γ(F, W) → Γ(F, D(c f) ∩ W)` is a localization at `f`, as `A`-modules through `c`. -/
theorem isLocalizedModule_sectionsRestrict {V₀ W W' : X.Opens} {A : Type u} [CommRing A]
    (c : A →+* Γ(X, V₀)) (hW : IsAffineOpen W) (hWV : W ≤ V₀) (f : A)
    (hW' : W' = X.basicOpen (c f) ⊓ W) :
    IsLocalizedModule (Submonoid.powers f)
      (sectionsRestrict F c hWV ((hW'.le.trans inf_le_right).trans hWV)
        (hW'.le.trans inf_le_right)).hom := by
  have hW'W : W' ≤ W := hW'.le.trans inf_le_right
  have hW'V : W' ≤ V₀ := hW'W.trans hWV
  let g : Γ(X, W) := sectionsRingHom c hWV f
  have hbg : X.basicOpen g = W' := by
    rw [hW']
    change X.basicOpen (X.presheaf.map (homOfLE hWV).op (c f)) = _
    rw [Scheme.basicOpen_res, inf_comm]
  let : Module Γ(X, W) Γ(F, X.basicOpen g) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  have hN := isLocalizedModule_restrictLinearNative F hW g
  -- the action of `f ^ n` on the target is that of a unit
  have hgres : ∀ n : ℕ, sectionsRingHom c hW'V (f ^ n) =
      X.presheaf.map (homOfLE hW'W).op (g ^ n) := by
    intro n
    rw [map_pow, map_pow]
    congr 1
    exact (ring_presheaf_map_map hWV hW'W hW'V (c f)).symm
  have hunit : IsUnit (sectionsRingHom c hW'V f) := by
    have h0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (c f))).op (c f)) :=
      X.toRingedSpace.isUnit_res_basicOpen (c f)
    have hle : W' ≤ X.basicOpen (c f) := hW'.le.trans inf_le_left
    have := h0.map (X.presheaf.map (homOfLE hle).op).hom
    have e := ring_presheaf_map_map (X.basicOpen_le (c f)) hle hW'V (c f)
    show IsUnit (X.presheaf.map (homOfLE hW'V).op (c f))
    rw [← e]
    exact this
  constructor
  · rintro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hunit' : IsUnit (sectionsRingHom c hW'V (f ^ n)) := by
      rw [map_pow]
      exact hunit.pow n
    have hb := (Module.End.isUnit_iff _).mp
      (hunit'.map (algebraMap Γ(X, W') (Module.End Γ(X, W') Γ(F, W'))))
    exact hb
  · intro y
    obtain ⟨y', rfl⟩ : ∃ y' : Γ(F, W'), y' = y := ⟨y, rfl⟩
    obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, hm⟩ := hN.surj (F.presheaf.map (homOfLE hbg.le).op y')
    refine ⟨⟨m, ⟨f ^ n, n, rfl⟩⟩, ?_⟩
    change X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) •
        F.presheaf.map (homOfLE hbg.le).op y' =
      F.presheaf.map (homOfLE (X.basicOpen_le g)).op m at hm
    have h2 := congrArg (fun z => F.presheaf.map (homOfLE hbg.ge).op z) hm
    simp only at h2
    rw [Scheme.Modules.map_smul, presheaf_map_map_self, ring_presheaf_map_map,
      presheaf_map_map] at h2
    change sectionsRingHom c hW'V (f ^ n) • y' = F.presheaf.map (homOfLE hW'W).op m
    rw [hgres]
    exact h2
  · intro m₁ m₂ h
    have h' : restrictLinearNative F (X.basicOpen_le g) m₁ =
        restrictLinearNative F (X.basicOpen_le g) m₂ := by
      have h2 := congrArg (fun z : Γ(F, W') => F.presheaf.map (homOfLE hbg.le).op z) h
      exact (presheaf_map_map F hW'W hbg.le (X.basicOpen_le g) m₁).symm.trans
        (h2.trans (presheaf_map_map F hW'W hbg.le (X.basicOpen_le g) m₂))
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hN.exists_of_eq h'
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    change sectionsRingHom c hWV (f ^ n) • (show Γ(F, W) from m₁) =
      sectionsRingHom c hWV (f ^ n) • (show Γ(F, W) from m₂)
    rw [map_pow]
    exact hn

end QuasiCoherent

section Affine

variable {X : Scheme.{u}} (F : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (V : X.Opens)

/-- The link diagram `T ↦ Γ(F, V ∩ U_T)` (with `Γ(F, V)` at `T = ∅`), as `Γ(X, V)`-modules. -/
abbrev linkDiagram : Finset ι ⥤ ModuleCat.{u} Γ(X, V) :=
  sectionsDiagram F (RingHom.id Γ(X, V)) (fun T => V ⊓ T.inf U)
    (fun _ _ h => inf_le_inf_left V (Finset.inf_mono h)) (fun _ => inf_le_left)

/-- The link diagram localized at `r ∈ Γ(X, V)`: `T ↦ Γ(F, D(r) ∩ V ∩ U_T)`. -/
abbrev linkDiagramLoc (r : Γ(X, V)) : Finset ι ⥤ ModuleCat.{u} Γ(X, V) :=
  sectionsDiagram F (RingHom.id Γ(X, V)) (fun T => X.basicOpen r ⊓ (V ⊓ T.inf U))
    (fun _ _ h => inf_le_inf_left _ (inf_le_inf_left V (Finset.inf_mono h)))
    (fun _ => inf_le_right.trans inf_le_left)

/-- The localization map from the link diagram to its localization at `r`. -/
def linkDiagramToLoc (r : Γ(X, V)) : linkDiagram F U V ⟶ linkDiagramLoc F U V r where
  app T := sectionsRestrict F (RingHom.id Γ(X, V)) inf_le_left
    (inf_le_right.trans inf_le_left) inf_le_right
  naturality {S T} h := by
    simp only [sectionsRestrict_comp]

/-- **Acyclicity on an affine** (blueprint `prop:sm-cech-affine`): for `F` quasi-coherent, `V`
affine, `V ⊆ ⋃ U_i` and all `V ∩ U_T` affine, the total cube of the link diagram is exact. -/
theorem linkDiagram_exact [Finite ι] [F.IsQuasicoherent] (hV : IsAffineOpen V)
    (hcov : V ≤ ⨆ i, U i) (haff : ∀ T : Finset ι, IsAffineOpen (V ⊓ T.inf U)) :
    Function.Exact (subsetCechDifferential (linkDiagram F U V))
      (subsetCechDifferential (linkDiagram F U V)) := by
  classical
  let s : Set Γ(X, V) := {r | ∃ i, X.basicOpen r ≤ U i}
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hx)
    obtain ⟨r, hr, hxr⟩ := hV.exists_basicOpen_le (V := U i) ⟨x, hi⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨r, i, hr⟩, hxr⟩
  apply subsetCech_exact_of_isLocalized_span (linkDiagram F U V) s hs
    (fun r => linkDiagramLoc F U V r.1) (fun r => linkDiagramToLoc F U V r.1)
  · intro r T
    exact isLocalizedModule_sectionsRestrict F (RingHom.id Γ(X, V)) (haff T) inf_le_left r.1 rfl
  · rintro ⟨r, i, hri⟩
    apply subsetCech_exact_of_cone (i₀ := i)
    intro T _
    apply sectionsRestrict_bijective_of_eq
    show X.basicOpen r ⊓ (V ⊓ (insert i T).inf U) = X.basicOpen r ⊓ (V ⊓ T.inf U)
    rw [Finset.inf_insert]
    apply le_antisymm
    · exact inf_le_inf_left _ (inf_le_inf_left _ inf_le_right)
    · exact le_inf inf_le_left (le_inf (inf_le_right.trans inf_le_left)
        (le_inf (inf_le_left.trans hri) (inf_le_right.trans inf_le_right)))

variable {F} in
/-- Componentwise restriction between section diagrams with `W₁ T ≤ W₀ T` commutes with the
alternating differentials. -/
lemma sectionsCube_restrict_differential {A B : Type u} [CommRing A] [CommRing B]
    {V₀ V₁ : X.Opens} (c₀ : A →+* Γ(X, V₀)) (c₁ : B →+* Γ(X, V₁))
    (W₀ W₁ : Finset ι → X.Opens) (hW₀ : Antitone W₀) (hW₁ : Antitone W₁) (h₀ : ∀ T, W₀ T ≤ V₀)
    (h₁ : ∀ T, W₁ T ≤ V₁) (hle : ∀ T, W₁ T ≤ W₀ T)
    (x : subsetCechCube (sectionsDiagram F c₀ W₀ hW₀ h₀)) (T : Finset ι) :
    sectionsRestrictAdd F c₀ c₁ (h₀ T) (h₁ T) (hle T) (subsetCechDifferential _ x T) =
      subsetCechDifferential (sectionsDiagram F c₁ W₁ hW₁ h₁)
        (fun S => sectionsRestrictAdd F c₀ c₁ (h₀ S) (h₁ S) (hle S) (x S)) T := by
  rw [subsetCechDifferential_apply, subsetCechDifferential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  simp only [subsetCechRestriction]
  rw [sectionsRestrictAdd_sectionsRestrict, sectionsRestrict_sectionsRestrictAdd]

variable {F} in
/-- Exactness of the total cube is insensitive to the coefficient ring and to replacing the
opens by equal ones. -/
theorem sectionsDiagram_exact_congr {A B : Type u} [CommRing A] [CommRing B] {V₀ V₁ : X.Opens}
    (c₀ : A →+* Γ(X, V₀)) (c₁ : B →+* Γ(X, V₁)) (W₀ W₁ : Finset ι → X.Opens) (hW₀ : Antitone W₀)
    (hW₁ : Antitone W₁) (h₀ : ∀ T, W₀ T ≤ V₀) (h₁ : ∀ T, W₁ T ≤ V₁) (heq : ∀ T, W₁ T = W₀ T)
    (hex : Function.Exact (subsetCechDifferential (sectionsDiagram F c₀ W₀ hW₀ h₀))
      (subsetCechDifferential (sectionsDiagram F c₀ W₀ hW₀ h₀))) :
    Function.Exact (subsetCechDifferential (sectionsDiagram F c₁ W₁ hW₁ h₁))
      (subsetCechDifferential (sectionsDiagram F c₁ W₁ hW₁ h₁)) := by
  let e : subsetCechCube (sectionsDiagram F c₀ W₀ hW₀ h₀) →
      subsetCechCube (sectionsDiagram F c₁ W₁ hW₁ h₁) := fun x S =>
    sectionsRestrictAdd F c₀ c₁ (h₀ S) (h₁ S) (heq S).le (x S)
  let e' : subsetCechCube (sectionsDiagram F c₁ W₁ hW₁ h₁) →
      subsetCechCube (sectionsDiagram F c₀ W₀ hW₀ h₀) := fun x S =>
    sectionsRestrictAdd F c₁ c₀ (h₁ S) (h₀ S) (heq S).ge (x S)
  have hee' : ∀ y, e (e' y) = y := fun y => funext fun S =>
    sectionsRestrictAdd_sectionsRestrictAdd F c₁ c₀ (h₁ S) (h₀ S) (heq S).symm (y S)
  have he : ∀ x, e (subsetCechDifferential _ x) = subsetCechDifferential _ (e x) :=
    fun x => funext fun T => sectionsCube_restrict_differential c₀ c₁ W₀ W₁ hW₀ hW₁ h₀ h₁
      (fun S => (heq S).le) x T
  have he' : ∀ y, e' (subsetCechDifferential _ y) = subsetCechDifferential _ (e' y) :=
    fun y => funext fun T => sectionsCube_restrict_differential c₁ c₀ W₁ W₀ hW₁ hW₀ h₁ h₀
      (fun S => (heq S).ge) y T
  have he'0 : e' 0 = 0 := funext fun S => map_zero _
  intro y
  constructor
  · intro hy
    have h0 : subsetCechDifferential _ (e' y) = 0 := by rw [← he', hy, he'0]
    obtain ⟨z, hz⟩ := (hex (e' y)).mp h0
    refine ⟨e z, ?_⟩
    rw [← he, hz, hee']
  · rintro ⟨z, rfl⟩
    exact subsetCechDifferential_squared _ z

/-- **Vanishing on affine schemes**: for a finite family covering an affine scheme with affine
intersections and `F` quasi-coherent, `Ȟ^p(U, F) = 0` for `p > 0`. -/
theorem isZero_cechCohomology_of_isAffine [Finite ι] [IsAffine X] [F.IsQuasicoherent]
    (hU : ⨆ i, U i = ⊤) (haff : ∀ T : Finset ι, T.Nonempty → IsAffineOpen (T.inf U))
    {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (p : ℕ) :
    Limits.IsZero (cechCohomology F U c (p + 1)) := by
  apply isZero_subsetCechComplex_homology_succ_of_exact
  apply sectionsDiagram_exact_congr (RingHom.id Γ(X, ⊤)) c (fun T => ⊤ ⊓ T.inf U)
    (fun T => T.inf U) _ _ _ _ (fun T => (top_inf_eq _).symm)
  apply linkDiagram_exact F U ⊤ (isAffineOpen_top X) (by rw [hU])
  intro T
  rw [top_inf_eq]
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h, Finset.inf_empty]
    exact isAffineOpen_top X
  · exact haff T h

end Affine

end

end DeJongAlterations.StableModification.Cohomology

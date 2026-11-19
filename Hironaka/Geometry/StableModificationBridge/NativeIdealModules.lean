/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1

Native small cone ported from EnvelopeProperty/deps/hironaka-ep33/Hironaka/Scheme/Modules.
Only imports and collision-free declaration names are adapted; every original scheme and coefficient map is retained.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Module.FinitePresentation

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The ring identity behind the restriction to an affine open: the `Γ(X, V)`-action on the
sections of `F.restrict hV.fromSpec` over `W` is the restriction. -/
theorem dja_fromSpec_appIso_inv {V : X.Opens} (hV : IsAffineOpen V) (W : (Spec Γ(X, V)).Opens)
    (h : hV.fromSpec ''ᵁ W ≤ V) (r : Γ(X, V)) :
    (hV.fromSpec.appIso W).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso Γ(X, V)).inv r)) = X.presheaf.map (homOfLE h).op r := by
  apply (ConcreteCategory.bijective_of_isIso (hV.fromSpec.appIso W).hom).1
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    Scheme.Hom.appIso_hom, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.naturality_assoc, hV.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 3


/-- The restriction `Γ(F, V) → Γ(F, U)` as a `Γ(X, V)`-linear map, `Γ(F, U)` a `Γ(X, V)`-module
through the restriction of functions. -/
noncomputable def dja_resₗ {U V : X.Opens} (h : U ≤ V) :
    letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
    Γ(F, V) →ₗ[Γ(X, V)] Γ(F, U) :=
  letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r x => F.val.map_smul (homOfLE h).op r x }

theorem dja_resₗ_apply {U V : X.Opens} (h : U ≤ V) (x : Γ(F, V)) :
    F.dja_resₗ h x = F.presheaf.map (homOfLE h).op x := rfl

omit F in
theorem dja_fromSpec_image_top {V : X.Opens} (hV : IsAffineOpen V) : hV.fromSpec ''ᵁ ⊤ = V :=
  (Scheme.Hom.image_top_eq_opensRange _).trans hV.opensRange_fromSpec

/-- The sections of `F` over an affine open `V` are the global sections of the restriction of `F`
to `Spec Γ(X, V) ≅ V`, as `Γ(X, V)`-modules. -/
noncomputable def dja_topSectionsEquiv {V : X.Opens} (hV : IsAffineOpen V) :
    Γ(F, V) ≃ₗ[Γ(X, V)] Γ(F.restrict hV.fromSpec, ⊤) :=
  LinearEquiv.ofBijective (M₂ := Γ(F.restrict hV.fromSpec, ⊤))
    { toFun := F.presheaf.map (homOfLE (dja_fromSpec_image_top hV).le).op
      map_add' := map_add _
      map_smul' := fun c x => by
        change F.presheaf.map (homOfLE (dja_fromSpec_image_top hV).le).op (c • x) =
          (hV.fromSpec.appIso ⊤).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, V)).inv c)) •
              F.presheaf.map (homOfLE (dja_fromSpec_image_top hV).le).op x
        rw [dja_fromSpec_appIso_inv hV ⊤ (dja_fromSpec_image_top hV).le]
        exact F.val.map_smul (homOfLE (dja_fromSpec_image_top hV).le).op c x }
    (by
      have : IsIso (homOfLE (dja_fromSpec_image_top hV).le).op := by
        rw [show (homOfLE (dja_fromSpec_image_top hV).le).op = (eqToHom (dja_fromSpec_image_top hV)).op
          from rfl]
        infer_instance
      exact ConcreteCategory.bijective_of_isIso
        (F.presheaf.map (homOfLE (dja_fromSpec_image_top hV).le).op))

theorem dja_topSectionsEquiv_apply {V : X.Opens} (hV : IsAffineOpen V) (x : Γ(F, V)) :
    F.dja_topSectionsEquiv hV x = F.presheaf.map (homOfLE (dja_fromSpec_image_top hV).le).op x :=
  rfl

/-- The restriction to a basic open `D(r)` of an affine open `V` is a localization on `X` if and
only if it is one for the restriction of `F` to `Spec Γ(X, V) ≅ V`, the condition of Mathlib's
`isIso_fromTildeΓ_iff_isLocalizing`: the two restriction maps are identified by the restrictions
of `F` along `Spec Γ(X, V) ≅ V`, and the actions of `Γ(X, V)` by `dja_fromSpec_appIso_inv`. -/
theorem dja_isLocalizedModule_restrict_fromSpec_iff {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, V)) :
    letI := Module.compHom Γ(F, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    IsLocalizedModule (Submonoid.powers r)
      ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map
        (PrimeSpectrum.basicOpen r : (Spec Γ(X, V)).Opens).leTop.op).hom ↔
      IsLocalizedModule (Submonoid.powers r) (F.dja_resₗ (X.basicOpen_le r)) := by
  let := Module.compHom Γ(F, X.basicOpen r)
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  set W : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen r with hW
  have h2 : hV.fromSpec ''ᵁ W = X.basicOpen r := hV.fromSpec_image_basicOpen r
  let e1 := (F.dja_topSectionsEquiv hV).toLinearMap
  let e2 : Γ(F, X.basicOpen r) →ₗ[Γ(X, V)] Γ(F.restrict hV.fromSpec, W) :=
    { toFun := F.presheaf.map (homOfLE h2.le).op
      map_add' := map_add _
      map_smul' := fun c x => by
        change F.presheaf.map (homOfLE h2.le).op
            (X.presheaf.map (homOfLE (X.basicOpen_le r)).op c • x) =
          (hV.fromSpec.appIso W).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, V)).inv c)) • F.presheaf.map (homOfLE h2.le).op x
        rw [dja_fromSpec_appIso_inv hV _ (h2.le.trans (X.basicOpen_le r)),
          show X.presheaf.map (homOfLE (h2.le.trans (X.basicOpen_le r))).op c =
            X.presheaf.map (homOfLE h2.le).op
              (X.presheaf.map (homOfLE (X.basicOpen_le r)).op c) by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl]
        exact F.val.map_smul (homOfLE h2.le).op _ x }
  have he1 : Function.Bijective e1 := (F.dja_topSectionsEquiv hV).bijective
  have he2 : Function.Bijective e2 := by
    have : IsIso (homOfLE h2.le).op := by
      rw [show (homOfLE h2.le).op = (eqToHom h2).op from rfl]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (F.presheaf.map (homOfLE h2.le).op)
  have hcomm : e2 ∘ₗ F.dja_resₗ (X.basicOpen_le r) =
      ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map W.leTop.op).hom ∘ₗ e1 := by
    ext x
    change F.presheaf.map (homOfLE h2.le).op (F.presheaf.map (homOfLE (X.basicOpen_le r)).op x) =
      F.presheaf.map _ (F.presheaf.map (homOfLE (dja_fromSpec_image_top hV).le).op x)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : IsLocalizedModule (Submonoid.powers r) (e2 ∘ₗ F.dja_resₗ (X.basicOpen_le r)) := by
      rw [hcomm]
      exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r) e1 he1).mpr h
    exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r) e2 he2).mp h'
  · have h' : IsLocalizedModule (Submonoid.powers r)
        (((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map W.leTop.op).hom ∘ₗ e1) := by
      rw [← hcomm]
      exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r) e2 he2).mpr h
    exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r) e1 he1).mp h'

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The restriction of `F` to an open `U` along `U.ι` is the restriction to `Spec Γ(X, U)` pushed
along `U ≅ Spec Γ(X, U)`. -/
noncomputable def dja_restrictιIso {U : X.Opens} (hU : IsAffineOpen U) :
    (F.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ F.restrict U.ι :=
  ((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app F).symm ≪≫
    (restrictFunctorCongr (by rw [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc])).app F

/-- `F.over U` is the restriction of `F` along `U.ι`, through `overEquiv U`. -/
noncomputable def dja_overIso (U : X.Opens) :
    (overEquiv U).inverse.obj (F.restrict U.ι) ≅ F.over U :=
  (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app F).symm ≪≫
    ((overEquiv U).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency false in
/-- **A presentation of `F.over U` from one of the restriction of `F` to `Spec Γ(X, U)`**, for an
affine open `U`: transported along the restriction to `U ≅ Spec Γ(X, U)` and the equivalence
`overEquiv U`, which preserve colimits and the unit. -/
noncomputable def dja_presentationOverOfRestrict {U : X.Opens} (hU : IsAffineOpen U)
    (P : (F.restrict hU.fromSpec).Presentation) : (F.over U).Presentation :=
  have : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse :=
    (overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits
  (((presentationRestrict hU.isoSpec.hom P).ofIsIso (F.dja_restrictιIso hU).hom).map
    (overEquiv U).inverse (Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf).symm).ofIsIso
      (F.dja_overIso U).hom

set_option backward.isDefEq.respectTransparency false in
theorem dja_isFinite_presentationOverOfRestrict {U : X.Opens} (hU : IsAffineOpen U)
    (P : (F.restrict hU.fromSpec).Presentation) [P.IsFinite] :
    (F.dja_presentationOverOfRestrict hU P).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

/-- **Finite presentation from the affine opens**: if over every affine open `U` the restriction of
`F` to `Spec Γ(X, U)` has a finite presentation, then `F` is of finite presentation (hence
quasi-coherent and of finite type). -/
theorem dja_isFinitePresentation_of_forall_affine
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      ∃ P : (F.restrict hU.fromSpec).Presentation, P.IsFinite) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F := by
  choose P hP using h
  let σ : SheafOfModules.QuasicoherentData.{u} (R := X.ringCatSheaf) F :=
    { I := X.affineOpens
      X := fun U => (U : X.Opens)
      coversTop := (Opens.coversTop_iff (U := fun U : X.affineOpens => (U : X.Opens))).mpr
        (iSup_affineOpens_eq_top X)
      presentation := fun (U : X.affineOpens) => F.dja_presentationOverOfRestrict U.2 (P U U.2) }
  have hσ : σ.IsFinitePresentation := by
    constructor
    intro U
    have := hP U U.2
    exact F.dja_isFinite_presentationOverOfRestrict U.2 (P U U.2)
  constructor
  exact ⟨σ, hσ⟩

set_option backward.isDefEq.respectTransparency false in
/-- Over an affine open `V`, if the restriction of `F` to `Spec Γ(X, V)` is the sheaf associated to
its global sections and `Γ(F, V)` is a finitely presented `Γ(X, V)`-module, the restriction has a
finite presentation (Mathlib's `presentationTilde`). -/
theorem dja_exists_isFinite_presentation_restrict {V : X.Opens} (hV : IsAffineOpen V)
    [IsIso (F.restrict hV.fromSpec).fromTildeΓ] [Module.FinitePresentation Γ(X, V) Γ(F, V)] :
    ∃ P : (F.restrict hV.fromSpec).Presentation, P.IsFinite := by
  let M := (modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).presheaf.obj (op ⊤)
  have : Module.FinitePresentation Γ(X, V) M :=
    Module.FinitePresentation.of_equiv (F.dja_topSectionsEquiv hV)
  obtain ⟨s, hs, t, ht⟩ : ∃ (s : Finset M), Submodule.span Γ(X, V) (s : Set M) = ⊤ ∧
      ∃ t : Finset (s →₀ Γ(X, V)), Submodule.span Γ(X, V) (t : Set (s →₀ Γ(X, V))) =
        LinearMap.ker (Finsupp.linearCombination Γ(X, V) ((↑) : s → M)) := by
    obtain ⟨s, hs, t, ht⟩ := this.out
    exact ⟨s, hs, t, ht⟩
  let P₀ := presentationTilde (M := M) (s : Set M) hs (t : Set (s →₀ Γ(X, V))) ht
  have : P₀.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set M))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ Γ(X, V))))⟩ }
  exact ⟨P₀.ofIsIso (F.restrict hV.fromSpec).fromTildeΓ, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Membership in `I(U)` is local**: a function on an affine open `U` lies in `I(U)` if every
point of `U` has an open neighbourhood `V` such that the restriction of the function to every affine
open inside `V ∩ U` lies in the ideal of that open. -/
theorem dja_mem_ideal_of_locally_mem (U : X.affineOpens) (s : Γ(X, U))
    (h : ∀ x ∈ (U : X.Opens), ∃ V : X.Opens, x ∈ V ∧ ∀ (U' : X.affineOpens)
      (hU' : (U' : X.Opens) ≤ U), (U' : X.Opens) ≤ V →
        X.presheaf.map (homOfLE hU').op s ∈ I.ideal U') :
    s ∈ I.ideal U := by
  let S : Set Γ(X, U) := {g | X.presheaf.map (homOfLE (X.basicOpen_le g)).op s ∈
    I.ideal (X.affineBasicOpen g)}
  have hspan : Ideal.span S = ⊤ := by
    refine (U.2.iSup_basicOpen_eq_self_iff).mp (le_antisymm (iSup_le fun g => X.basicOpen_le _)
      fun x hxU => ?_)
    obtain ⟨V, hxV, hV⟩ := h x hxU
    obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hxU
    exact Opens.mem_iSup.mpr ⟨⟨g, hV (X.affineBasicOpen g) (X.basicOpen_le g) hgV⟩, hxg⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S hspan s fun g => ?_
  have := U.2.isLocalization_basicOpen (g : Γ(X, U))
  have hg := g.2
  change X.presheaf.map (homOfLE (X.basicOpen_le _)).op s ∈ I.ideal (X.affineBasicOpen _) at hg
  rw [← I.map_ideal_basicOpen] at hg
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ham⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Submonoid.powers (g : Γ(X, U))) Γ(X, X.basicOpen (g : Γ(X, U)))).mp hg
  have ham' : algebraMap Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U))) (s * (g : Γ(X, U)) ^ n) =
      algebraMap Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U))) a := by
    rw [map_mul]
    exact ham
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (g : Γ(X, U)))
    Γ(X, X.basicOpen (g : Γ(X, U)))).mp ham'
  refine ⟨n + k, ?_⟩
  change (g : Γ(X, U)) ^ (n + k) * s ∈ I.ideal U
  rw [pow_add, mul_comm ((g : Γ(X, U)) ^ n), mul_assoc, mul_comm _ s, hc]
  exact Ideal.mul_mem_left _ _ a.2

/-- The condition defining the sections of the ideal sheaf `I` over an open `W`: the restriction to
every affine open `U ⊆ W` lies in `I(U)`. -/
def dja_IsLocallyMem (W : X.Opens) (s : Γ(X, W)) : Prop :=
  ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W), X.presheaf.map (homOfLE hU).op s ∈ I.ideal U

theorem dja_isLocallyMem_map {W W' : X.Opens} (h : W' ≤ W) {s : Γ(X, W)} (hs : I.dja_IsLocallyMem W s) :
    I.dja_IsLocallyMem W' (X.presheaf.map (homOfLE h).op s) := fun U hU => by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact hs U (hU.trans h)

/-- The submodules of sections of the ideal sheaf `I` inside `𝒪_X`: over an open `W`, the
functions whose restriction to every affine open `U ⊆ W` lies in `I(U)`. -/
noncomputable def dja_toSubmodule : (SheafOfModules.unit X.ringCatSheaf).val.Submodule where
  obj W :=
    { carrier := {s | I.dja_IsLocallyMem W.unop (s : Γ(X, W.unop))}
      add_mem' := fun {a b} ha hb U hU =>
        (congrArg (· ∈ I.ideal U) (map_add (X.presheaf.map (homOfLE hU).op).hom
          (a : Γ(X, W.unop)) (b : Γ(X, W.unop)))).mpr (add_mem (ha U hU) (hb U hU))
      zero_mem' := fun U hU =>
        (congrArg (· ∈ I.ideal U) (map_zero (X.presheaf.map (homOfLE hU).op).hom)).mpr
          (zero_mem _)
      smul_mem' := fun c s hs U hU =>
        (congrArg (· ∈ I.ideal U) (map_mul (X.presheaf.map (homOfLE hU).op).hom
          (c : Γ(X, W.unop)) (s : Γ(X, W.unop)))).mpr (Ideal.mul_mem_left _ _ (hs U hU)) }
  map f _ hs := I.dja_isLocallyMem_map f.unop.le hs

/-- The sheaf condition of `dja_toSubmodule`, from the locality of membership in `I(U)`
(`dja_mem_ideal_of_locally_mem`). -/
theorem dja_isSheaf_toSubmodule :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) I.dja_toSubmodule.toPresheafOfModules.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type]
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.presheaf ⋙ CategoryTheory.forget CommRingCat) := by
    rw [← isSheaf_iff_isSheaf_of_type, ← Presheaf.isSheaf_iff_isSheaf_forget]
    exact X.IsSheaf
  let G : Subfunctor (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    { obj W := {s | I.dja_IsLocallyMem W.unop s}
      map {W W'} f s hs := I.dja_isLocallyMem_map f.unop.le hs }
  have hG : Presieve.IsSheaf (Opens.grothendieckTopology X) G.toFunctor := by
    refine (G.isSheaf_iff hF).mpr fun W s hs U hU => ?_
    refine I.dja_mem_ideal_of_locally_mem U _ fun x hxU => ?_
    obtain ⟨V, f, hf, hxV⟩ := hs x (hU hxU)
    refine ⟨V, hxV, fun U' hU' hU'V => ?_⟩
    have := hf U' hU'V
    change X.presheaf.map (homOfLE hU'V).op (X.presheaf.map (homOfLE f.le).op s) ∈ I.ideal U'
      at this
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact this
  refine Presieve.isSheaf_iso (Opens.grothendieckTopology X) ?_ hG
  exact NatIso.ofComponents (fun W =>
    { hom := TypeCat.ofHom fun x => ⟨x.1, x.2⟩
      inv := TypeCat.ofHom fun x => ⟨x.1, x.2⟩ }) (fun _ => rfl)

/-- **The ideal sheaf `I` as a sheaf of `𝒪_X`-modules**: the subsheaf of `𝒪_X` of the functions
whose restriction to every affine open `U` lies in `I(U)`. -/
noncomputable def dja_toModules : X.Modules where
  val := I.dja_toSubmodule.toPresheafOfModules
  isSheaf := I.dja_isSheaf_toSubmodule

/-- Over an affine open `U`, the sections of `I.dja_toModules` are the elements of `I(U)`. -/
theorem dja_isLocallyMem_iff (U : X.affineOpens) (s : Γ(X, U)) :
    I.dja_IsLocallyMem U s ↔ s ∈ I.ideal U := by
  refine ⟨fun hs => ?_, fun hs U' hU' => ?_⟩
  · have := hs U le_rfl
    rwa [show homOfLE (le_refl (U : X.Opens)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id] at this
  · exact I.ideal_le_comap_ideal hU' hs

/-- Over an affine open `U`, the sections of `I.dja_toModules` are the elements of `I(U)`, as modules
over `Γ(X, U)`. -/
noncomputable def dja_toModulesSectionsEquiv (U : X.affineOpens) :
    Γ(I.dja_toModules, U) ≃ₗ[Γ(X, U)] I.ideal U where
  toFun s := ⟨(s : I.dja_toSubmodule.obj (op (U : X.Opens))).1,
    (I.dja_isLocallyMem_iff U _).mp (s : I.dja_toSubmodule.obj (op (U : X.Opens))).2⟩
  invFun a := (⟨a.1, (I.dja_isLocallyMem_iff U a.1).mpr a.2⟩ : I.dja_toSubmodule.obj (op (U : X.Opens)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dja_coe_toModulesSectionsEquiv (U : X.affineOpens) (s : Γ(I.dja_toModules, U)) :
    ((I.dja_toModulesSectionsEquiv U s : I.ideal U) : Γ(X, U)) =
      (s : I.dja_toSubmodule.obj (op (U : X.Opens))).1 :=
  rfl

/-- The restriction maps of `I.dja_toModules` are the restrictions of functions. -/
theorem dja_coe_toModulesSectionsEquiv_restrictionMap {U V : X.affineOpens} (h : U ≤ V)
    (s : Γ(I.dja_toModules, V)) :
    ((I.dja_toModulesSectionsEquiv U (I.dja_toModules.presheaf.map (homOfLE h).op s) : I.ideal U) :
        Γ(X, U)) =
      X.presheaf.map (homOfLE h).op (I.dja_toModulesSectionsEquiv V s : Γ(X, V)) :=
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (I : X.IdealSheafData)

theorem dja_coe_toModulesSectionsEquiv_smul (U : X.affineOpens) (c : Γ(X, U))
    (s : Γ(I.dja_toModules, U)) :
    ((I.dja_toModulesSectionsEquiv U (c • s) : I.ideal U) : Γ(X, U)) =
      c * (I.dja_toModulesSectionsEquiv U s : Γ(X, U)) := by
  rw [LinearEquiv.map_smul]
  rfl

/-- Over a basic open `D(r)` of an affine open `U`, the sections of `I.dja_toModules` are the
localization of those over `U`: `I(D(r)) = I(U)_r`. -/
theorem dja_isLocalizedModule_toModules_resₗ (U : X.affineOpens) (r : Γ(X, U)) :
    letI := Module.compHom Γ(I.dja_toModules, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    IsLocalizedModule (Submonoid.powers r) (I.dja_toModules.dja_resₗ (X.basicOpen_le r)) := by
  let := Module.compHom Γ(I.dja_toModules, X.basicOpen r)
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have := U.2.isLocalization_basicOpen r
  set ρ := X.presheaf.map (homOfLE (X.basicOpen_le r)).op
  set eU := I.dja_toModulesSectionsEquiv U
  set eD := I.dja_toModulesSectionsEquiv (X.affineBasicOpen r)
  -- The values in `Γ(X, D(r))` of the sections over `D(r)`.
  let v : Γ(I.dja_toModules, X.basicOpen r) → Γ(X, X.basicOpen r) := fun w => (eD w).1
  have hv : Function.Injective v := fun w w' h => eD.injective (Subtype.ext h)
  have hres (s : Γ(I.dja_toModules, U)) :
      v (I.dja_toModules.dja_resₗ (X.basicOpen_le r) s) = ρ (eU s : Γ(X, U)) :=
    I.dja_coe_toModulesSectionsEquiv_restrictionMap (U := X.affineBasicOpen r) (V := U)
      (X.basicOpen_le r) s
  have hsmul' (c : Γ(X, X.basicOpen r)) (y : Γ(I.dja_toModules, X.basicOpen r)) :
      v (c • y) = c * v y :=
    I.dja_coe_toModulesSectionsEquiv_smul (X.affineBasicOpen r) c y
  have hsmul (c : Γ(X, U)) (y : Γ(I.dja_toModules, X.basicOpen r)) : v (c • y) = ρ c * v y :=
    hsmul' (ρ c) y
  have hunit (n : ℕ) : IsUnit (ρ (r ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen r)) r).pow n
  refine ⟨fun x => ?_, fun y => ?_, fun {a b} h => ?_⟩
  · obtain ⟨_, n, rfl⟩ := x
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hunit n
    refine ⟨fun y z hyz => hv ?_, fun y => ⟨(u⁻¹ : (Γ(X, X.basicOpen r))ˣ) • y, hv ?_⟩⟩
    · have := congrArg v hyz
      simp only [Module.algebraMap_end_apply] at this
      rw [hsmul, hsmul, ← hu] at this
      exact u.isUnit.mul_left_cancel this
    · change v ((r ^ n) • ((u⁻¹ : (Γ(X, X.basicOpen r))ˣ) • y)) = v y
      rw [hsmul, ← hu, Units.smul_def, hsmul', ← mul_assoc, Units.mul_inv, one_mul]
  · have hmap : ∀ w : Γ(X, X.basicOpen r), w ∈ I.ideal (X.affineBasicOpen r) →
        w ∈ (I.ideal U).map ρ.hom := fun w hw => by rwa [← I.map_ideal_basicOpen] at hw
    have hy := hmap (v y) (eD y).2
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers r) Γ(X, X.basicOpen r)).mp hy
    refine ⟨(eU.symm a, ⟨r ^ n, n, rfl⟩), hv ?_⟩
    change v ((r ^ n) • y) = _
    rw [hsmul, hres, LinearEquiv.apply_symm_apply, mul_comm]
    exact ha
  · have h' := congrArg v h
    simp only [hres] at h'
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r)
      Γ(X, X.basicOpen r)).mp h'
    refine ⟨c, eU.injective (Subtype.ext ?_)⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, LinearEquiv.map_smul, LinearEquiv.map_smul]
    exact hc

/-- Over an affine open `U`, the restriction of `I.dja_toModules` to `Spec Γ(X, U)` is the sheaf
associated to its global sections: the restrictions to the basic opens are localizations
(`dja_isLocalizedModule_toModules_resₗ`). -/
theorem dja_isIso_fromTildeΓ_toModules {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (I.dja_toModules.restrict hU.fromSpec).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mpr fun r =>
    (I.dja_toModules.dja_isLocalizedModule_restrict_fromSpec_iff hU r).mpr
      (I.dja_isLocalizedModule_toModules_resₗ ⟨U, hU⟩ r)

/-- **An ideal sheaf on a locally Noetherian scheme is of finite presentation** as a sheaf of
modules: over each affine open `U` its restriction to `Spec Γ(X, U)` is the sheaf associated to
`I(U)`, a finitely presented module over the Noetherian ring `Γ(X, U)`. -/
theorem dja_isFinitePresentation_toModules [IsLocallyNoetherian X] :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) I.dja_toModules := by
  refine I.dja_toModules.dja_isFinitePresentation_of_forall_affine fun U hU => ?_
  let U' : X.affineOpens := ⟨U, hU⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
  have : Module.FinitePresentation Γ(X, U) (I.ideal U') :=
    Module.finitePresentation_of_finite _ _
  have : Module.FinitePresentation Γ(X, U) Γ(I.dja_toModules, U) :=
    Module.FinitePresentation.of_equiv (I.dja_toModulesSectionsEquiv U').symm
  have := I.dja_isIso_fromTildeΓ_toModules hU
  exact I.dja_toModules.dja_exists_isFinite_presentation_restrict hU

end AlgebraicGeometry.Scheme.IdealSheafData

import DeJongAlterations.StableModification.LocalUniformization.Cofinal
import DeJongAlterations.StableModification.LocalUniformization.CurveAlgebra
import DeJongAlterations.StableModification.LocalUniformization.CurveFinite
import DeJongAlterations.Geometry.NormalCurveModificationFunctionField

/-!
# Local rings of a curve inside its function field

Let `X` be an integral scheme and `L` a field with an algebra structure `K(X) → L`, so that the
generic point of `X` gives `η = RiemannZariskiSpace.functionFieldPoint X L : Spec L → X` (RZ1).
For a point `x` of `X` the local ring `𝒪_{X,x}` maps to `L` through the function field
(`localRingMap`); its image is a local subring `𝒪_x ⊆ L` (`localSubring`). This file proves the
dictionary between centres and domination used in our proof of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), Proposition 4.3.3 (`locunifprop`,
`semi-stable.tex` lines 3048–3081):

* `localRingMap_germ`: on an affine open `U ∋ x`, the section map `Γ(X,U) → L` of `η` is the germ
  at `x` followed by `localRingMap` (`sectionsToField_eq_localRingMap_germ`);
* `isCentre_iff_localSubring_le`: for `X` separated, a valuation ring `V` of `L` is centred at
  `x` iff it dominates `𝒪_x`;
* `isIntegrallyClosedIn_localSubring`: if `X` is normal and `K(X) → L` is surjective, `𝒪_x` is
  integrally closed in `L`;
* `genericLiftAlgebra`, `functionFieldPoint_genericLiftAlgebra`: for a modification
  `f : X → Y`, the lift `ValCurves.genericLift f : Spec K(Y) → X` of the generic point of `Y` is
  `functionFieldPoint X K(Y)` for the inverse of the function field isomorphism of `f`.

Blueprint `lem:sm-lu-curve-local-ring` (`sm-local-uniformization-curve.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace DeJongAlterations.StableModification.LocalUniformization.Curve

open ValCurves RiemannZariskiSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section LocalRing

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

/-- The map `𝒪_{X,x} → K(X) → L`. -/
def localRingMap (x : X) : X.presheaf.stalk x →+* L :=
  (algebraMap X.functionField L).comp (algebraMap (X.presheaf.stalk x) X.functionField)

/-- The local ring `𝒪_{X,x}` as a local subring of `L`. -/
def localSubring (x : X) : LocalSubring L :=
  LocalSubring.range (localRingMap X L x)

variable {X L}

/-- The generic point lies in every open containing a point. -/
theorem genericPoint_mem_of_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

theorem localRingMap_injective (x : X) : Function.Injective (localRingMap X L x) :=
  (algebraMap X.functionField L).injective.comp
    (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)

theorem mem_localSubring_iff {x : X} {b : L} :
    b ∈ (localSubring X L x).toSubring ↔ ∃ y, localRingMap X L x y = b :=
  Iff.rfl

/-- The germ of a section, followed by `localRingMap`, is its image in the function field. -/
theorem localRingMap_germ {U : X.Opens} {x : X} (hx : x ∈ U) (s : Γ(X, U)) :
    localRingMap X L x (X.presheaf.germ U x hx s) =
      algebraMap X.functionField L
        (X.presheaf.germ U (genericPoint X) (genericPoint_mem_of_mem hx) s) := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [localRingMap, RingHom.comp_apply, Scheme.algebraMap_germ_eq_germToFunctionField]

/-- On an affine open `U ∋ x`, the section map of the generic point is the germ at `x` followed by
`localRingMap`. -/
theorem sectionsToField_eq_localRingMap_germ {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (s : Γ(X, U)) :
    sectionsToField (functionFieldPoint X L) U
      (functionFieldPoint_preimage hU (genericPoint_mem_of_mem hx)) s =
      localRingMap X L x (X.presheaf.germ U x hx s) := by
  rw [sectionsToField_functionFieldPoint hU, localRingMap_germ hx]
  rfl

end LocalRing

section Affine

variable {X : Scheme.{u}} [IsIntegral X] {L : Type u} [Field L] [Algebra X.functionField L]

/-- The sections over an affine open `U ∋ x` lie in `𝒪_x`. -/
theorem range_sectionsToField_le_localSubring {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (h : functionFieldPoint X L ⁻¹ᵁ U = ⊤) :
    (sectionsToField (functionFieldPoint X L) U h).range ≤ (localSubring X L x).toSubring := by
  rintro _ ⟨s, rfl⟩
  rw [sectionsToField_congr rfl h (functionFieldPoint_preimage hU (genericPoint_mem_of_mem hx)),
    sectionsToField_eq_localRingMap_germ hU hx s]
  exact ⟨_, rfl⟩

/-- **Finitely many elements of `𝒪_x` are sections over one affine open neighbourhood of `x`.** -/
theorem exists_affineOpen_of_mem_localSubring {x : X} (F : Finset L)
    (hF : ∀ b ∈ F, b ∈ (localSubring X L x).toSubring) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U), ∀ b ∈ F,
      b ∈ (sectionsToField (functionFieldPoint X L) U
        (functionFieldPoint_preimage hU (genericPoint_mem_of_mem hxU))).range := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU, fun b hb ↦ absurd hb (Finset.notMem_empty b)⟩
  | @insert b F _ ih =>
    obtain ⟨U, hU, hxU, hFU⟩ := ih fun c hc ↦ hF c (Finset.mem_insert_of_mem hc)
    obtain ⟨y, hy⟩ := hF b (Finset.mem_insert_self b F)
    obtain ⟨Ub, hxUb, s, rfl⟩ := X.presheaf.exists_germ_eq y
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'le⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ U ⊓ Ub from ⟨hxU, hxUb⟩) (U ⊓ Ub).isOpen
    have hle : U' ≤ U := fun z hz ↦ (hU'le hz).1
    have hleb : U' ≤ Ub := fun z hz ↦ (hU'le hz).2
    refine ⟨U', hU', hxU', fun c hc ↦ ?_⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [← hy, ← X.presheaf.germ_res_apply (homOfLE hleb) x hxU' s,
        ← sectionsToField_eq_localRingMap_germ hU' hxU']
      exact ⟨_, rfl⟩
    · exact range_sectionsToField_le_of_comp (𝟙 X) (Category.comp_id _) hle _ _ (hFU c hc)

end Affine

/-! ### Centres and domination -/

section Centre

variable {X : Scheme.{u}} [IsIntegral X] {L : Type u} [Field L] [Algebra X.functionField L]

/-- The ring map `𝒪_{X,x} → L` composed with the generic point is `K(X) → L`. -/
theorem ofHom_localRingMap (x : X) :
    CommRingCat.ofHom (localRingMap X L x) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) ≫
        CommRingCat.ofHom (algebraMap X.functionField L) :=
  rfl

/-- **Domination gives a centre**: a valuation ring of `L` dominating `𝒪_x` is centred at `x`
(with respect to the generic point `functionFieldPoint X L`). -/
theorem isCentre_of_localSubring_le {x : X} {V : RiemannZariskiSpace L}
    (h : localSubring X L x ≤ V.valuationSubring.toLocalSubring) :
    IsCentre (functionFieldPoint X L) V x := by
  obtain ⟨hle, hloc⟩ := h
  have hmem : ∀ y, localRingMap X L x y ∈ V.valuationSubring.toSubring :=
    fun y ↦ hle ⟨y, rfl⟩
  let φ : X.presheaf.stalk x →+* V.valuationSubring :=
    (localRingMap X L x).codRestrict V.valuationSubring.toSubring hmem
  have hφ : IsLocalHom φ := by
    refine ⟨fun a ha ↦ ?_⟩
    have h1 : IsUnit (Subring.inclusion hle ((localRingMap X L x).rangeRestrict a)) := ha
    obtain ⟨⟨c, hc⟩, hcinv⟩ := isUnit_iff_exists_inv.mp (hloc.map_nonunit _ h1)
    obtain ⟨y, rfl⟩ := hc
    refine isUnit_iff_exists_inv.mpr ⟨y, localRingMap_injective (L := L) x ?_⟩
    have := congrArg Subtype.val hcinv
    simpa using this
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x, ?_, ?_⟩
  · rw [toSpecValuationSubring, ← Spec.map_comp_assoc]
    have e : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap V.valuationSubring L) =
        CommRingCat.ofHom (localRingMap X L x) := rfl
    rw [e, ofHom_localRingMap, Spec.map_comp_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  · rw [Scheme.Hom.comp_apply, specClosedPoint, Spec_closedPoint]
    exact Scheme.fromSpecStalk_closedPoint

/-- **A centre gives domination**: on a separated integral scheme, a valuation ring centred at
`x` dominates `𝒪_x`. -/
theorem le_localSubring_of_isCentre [X.IsSeparated] {x : X} {V : RiemannZariskiSpace L}
    (h : IsCentre (functionFieldPoint X L) V x) :
    localSubring X L x ≤ V.valuationSubring.toLocalSubring := by
  obtain ⟨ψ, hψ, hψx⟩ := h
  have key : ∀ y : X.presheaf.stalk x, localRingMap X L x y ∈ V.valuationSubring ∧
      (localRingMap X L x y ∉ V.valuationSubring.nonunits → IsUnit y) := by
    intro y
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq y
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    obtain ⟨s', hs'⟩ : ∃ s', X.presheaf.germ U x hxU s = X.presheaf.germ U' x hxU' s' :=
      ⟨_, (X.presheaf.germ_res_apply (homOfLE hU'U) x hxU' s).symm⟩
    rw [hs', ← sectionsToField_eq_localRingMap_germ hU' hxU' s']
    obtain ⟨hηU, hVr⟩ := mem_ofOpen_of_extension ψ hψ (hψx ▸ hxU' : ψ (specClosedPoint V) ∈ U')
    refine ⟨mem_ofRingHom.1 hVr s', fun hnu ↦ ?_⟩
    have heq := extension_unique hψ (toSpecValuationSubring_comp_extensionOfMem hU' hηU V hVr)
    have hc := (extensionOfMem_closedPoint_mem_basicOpen_iff hU' hηU V hVr s').mpr hnu
    rw [← heq, hψx] at hc
    exact (X.mem_basicOpen s' x hxU').mp hc
  refine ⟨fun b ⟨y, hy⟩ ↦ hy ▸ (key y).1, ⟨fun a ha ↦ ?_⟩⟩
  obtain ⟨_, y, rfl⟩ := a
  have hv : localRingMap X L x y ∉ V.valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff, not_lt]
    exact ((V.valuationSubring.valuation_eq_one_iff ⟨_, (key y).1⟩).mp ha).ge
  have hy := (key y).2 hv
  exact hy.map (localRingMap X L x).rangeRestrict

/-- **Centres are the dominating valuation rings.** -/
theorem isCentre_iff_localSubring_le [X.IsSeparated] {x : X} {V : RiemannZariskiSpace L} :
    IsCentre (functionFieldPoint X L) V x ↔
      localSubring X L x ≤ V.valuationSubring.toLocalSubring :=
  ⟨le_localSubring_of_isCentre, isCentre_of_localSubring_le⟩

/-- **The local ring is integrally closed in `L`** when `𝒪_{X,x}` is integrally closed and
`K(X) → L` is surjective. -/
theorem isIntegrallyClosedIn_localSubring {x : X} [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hsurj : Function.Surjective (algebraMap X.functionField L)) :
    IsIntegrallyClosedIn (localSubring X L x).toSubring L := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro z hz
  obtain ⟨w, rfl⟩ := hsurj z
  obtain ⟨P, hPm, hP⟩ := hz
  obtain ⟨P', hP', -, hP'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (localRingMap X L x).rangeRestrict
      (localRingMap X L x).rangeRestrict_surjective P) hPm
  have hw : IsIntegral (X.presheaf.stalk x) w := by
    refine ⟨P', hP'm, (algebraMap X.functionField L).injective ?_⟩
    rw [map_zero, ← hP, Polynomial.hom_eval₂, ← hP', Polynomial.eval₂_map]
    rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hw
  exact ⟨y, by rw [localRingMap, RingHom.comp_apply, hy]⟩

end Centre

/-! ### The lift of the generic point to a modification -/

section GenericLift

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [hf : IsModification f]

/-- The algebra `K(X) → K(Y)` inverse to the function field isomorphism of a modification
`f : X → Y` (Codex's `Geometry.NormalCurveModification.functionFieldMap`). -/
abbrev genericLiftAlgebra : Algebra X.functionField Y.functionField :=
  have := Geometry.NormalCurveModification.functionFieldMap_isIso f hf.birational
  (inv (Geometry.NormalCurveModification.functionFieldMap f hf.birational)).hom.toAlgebra

/-- The function field map of `genericLiftAlgebra` is bijective. -/
theorem genericLiftAlgebra_bijective :
    letI := genericLiftAlgebra f
    Function.Bijective (algebraMap X.functionField Y.functionField) := by
  have := Geometry.NormalCurveModification.functionFieldMap_isIso f hf.birational
  exact ConcreteCategory.bijective_of_isIso
    (inv (Geometry.NormalCurveModification.functionFieldMap f hf.birational))

/-- **The lift of the generic point** of `Y` to a modification `f : X → Y` is the generic point
of `X` with respect to `genericLiftAlgebra f`. -/
theorem functionFieldPoint_genericLiftAlgebra :
    letI := genericLiftAlgebra f
    functionFieldPoint X Y.functionField = genericLift f := by
  let := genericLiftAlgebra f
  have := Geometry.NormalCurveModification.functionFieldMap_isIso f hf.birational
  set M := Geometry.NormalCurveModification.functionFieldMap f hf.birational
  have hgen := Geometry.NormalCurveModification.genericPoint_map f hf.birational
  apply genericLift_unique
  have hM : f.stalkMap (genericPoint X) ≫ inv M =
      (Y.presheaf.stalkCongr (.of_eq hgen.symm)).inv := by
    rw [← cancel_epi (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom, Iso.hom_inv_id,
      ← Category.assoc]
    exact IsIso.hom_inv_id M
  have halg : CommRingCat.ofHom (algebraMap X.functionField Y.functionField) = inv M := rfl
  rw [functionFieldPoint, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
    ← Spec.map_comp, halg, hM, genericPt]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq hgen.symm).le

end GenericLift

end DeJongAlterations.StableModification.LocalUniformization.Curve

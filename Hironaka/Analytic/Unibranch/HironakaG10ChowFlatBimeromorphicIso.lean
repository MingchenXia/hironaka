import Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion
import Hironaka.Resolution.HironakaG10ChowDirectImage
import Hironaka.Resolution.HironakaG10ChowFiniteFlatRankOne
import Hironaka.Resolution.HironakaChowNativeFlatNeighborhood

/-!
# A flat proper bimeromorphic morphism is an isomorphism

Blueprint `chow:flat-bimeromorphic-iso` (file `hironaka-g10-chowside-flat-iso.tex`), in the
original category `SourceReducedComplexSpace` of reduced complex spaces, proved from two
classical theorems of local analytic geometry, each stated as a named proposition (not an
axiom, not proved here):

* `FlatMorphismsAreOpen` — a flat morphism of complex spaces is open.  Source checked
  (`references/douady66-modules`): Douady, *Le problème des modules pour les sous-espaces
  analytiques compacts d'un espace analytique donné*, Ann. Inst. Fourier 16 (1966), §8.3
  Prop. 1 (p. 66: over a finite-dimensional base `S`, `S`-anaplat = coherent and `S`-flat) and
  footnote (13) to §8.3 Prop. 2 (p. 68: the projection to `S` of the support of an `S`-anaplat
  sheaf on `S × U` is an open map); apply it to `𝒪_Y` on a local graph embedding
  `Y ⊆ X × U`.  Also Fischer, *Complex Analytic Geometry*, LNM 538, Prop. 3.19 (not in
  `references/`, not re-checked);
* `FiniteMappingTheorem` — for a proper morphism with finite fibres the direct image
  `p_* 𝒪_Y` is a finitely presented `𝒪_X`-module.  Sources checked: Douady, loc. cit., §10.1,
  p. 85–86 ("soit `f : X → Y` un morphisme fini et propre; pour tout faisceau cohérent `F`
  sur `X`, le faisceau image directe `f_* F` est cohérent"), and the case `q = 0`, `S = 𝒪_Y` of
  Grauert's direct image theorem (Demailly, *Complex analytic and differential geometry*,
  Ch. IX (5.1), in `references/demailly-cadg`); a coherent sheaf is locally finitely presented.

Both inputs are stated for the native category (reduced, Hausdorff, paracompact complex
spaces) and are true there, including the degenerate cases (empty source or target: the zero
module is finitely presented; a point as target: every map to a point is open, and a proper
map with finite fibres to a point has a finite reduced source, whose ring of functions is a
finite-dimensional algebra).

Everything else is proved: an open proper bimeromorphic morphism is a homeomorphism
(`HironakaG10ChowNativeIsoCriterion`, no dimension theory); the stalk of `p_* 𝒪_Y` at `p y` is
`𝒪_{Y,y}` (`HironakaG10ChowDirectImage`); a flat stalk of a finitely presented module is free
on a neighbourhood (`HironakaChowNativeFlatNeighborhood`); the rank is `1` at the nearby points
of the dense good locus, hence `1` at `p y`; a free algebra of rank one has bijective structure
map (`HironakaG10ChowFiniteFlatRankOne`); and the native isomorphism criterion concludes.

Main declarations:

* `IsFlatMorphism`, `FlatMorphismsAreOpen`, `FiniteMappingTheorem`.
* `isIso_stalkMap_of_flat_of_isHomeomorph` — a flat morphism with homeomorphic point map
  whose stalk maps are isomorphisms over a dense set has all stalk maps isomorphisms, given
  the finite mapping theorem.
* `isIso_of_flat_of_dense_stalk_iso` — **the lemma, general form**: a flat proper morphism
  which is bijective with isomorphic stalk maps over a dense subset of the target is an
  isomorphism.
* `isIso_of_isProperBimeromorphic_of_flat` — the lemma for proper bimeromorphic morphisms.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowFlatBimeromorphicIso

open SourceReducedComplexSpace HironakaG10ChowNativeIsoCriterion
  Hironaka.HironakaG10ChowOpenHomeomorph
  Hironaka.HironakaG10ChowDirectImage
  Hironaka.HironakaG10ChowFiniteFlatRankOne
  Hironaka.HironakaChowNativeFlatNeighborhood
  Hironaka.HironakaChowNativeFiniteFreeStalk
  Hironaka.HironakaSingularLocallyFreeStalk
  Hironaka.HironakaSingularModuleSheafStalk

noncomputable section

/-- A morphism of reduced complex spaces is *flat* if every stalk map
`𝒪_{X,p y} → 𝒪_{Y,y}` is flat. -/
def IsFlatMorphism {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) : Prop :=
  ∀ y : Y.obj.left, (p.hom.left.stalkMap y).hom.Flat

/-- **Named classical input: flat morphisms are open** (Douady 1966, Ann. Inst. Fourier 16,
§8.3 Prop. 1 and footnote (13), p. 66–68; Fischer, *Complex Analytic Geometry*, Prop. 3.19).
Not an axiom; not proved here. -/
def FlatMorphismsAreOpen : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (p : Y ⟶ X), IsFlatMorphism p →
    IsOpenMap p.hom.left.base

/-- **Named classical input: the finite mapping theorem** (Grauert; Douady 1966, §10.1, p. 85;
Demailly, *Complex analytic and differential geometry*, IX (5.1) with `q = 0`): the direct image of the
structure sheaf under a proper morphism of reduced complex spaces with finite fibres is a
finitely presented `𝒪_X`-module.  Not an axiom; not proved here. -/
def FiniteMappingTheorem : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (p : Y ⟶ X), IsProperMap p.hom.left.base →
    (∀ x : X.obj.left, (p.hom.left.base ⁻¹' {x}).Finite) →
    (directImage p.hom.left).IsFinitePresentation

variable {X Y : SourceReducedComplexSpace}

/-- The finrank of a stalk of `p_* 𝒪_Y` at a point where the stalk map is an isomorphism is one. -/
private theorem finrank_stalk_eq_one_of_isIso {p : Y ⟶ X} (hhom : IsHomeomorph p.hom.left.base)
    (y : Y.obj.left) (hs : IsIso (p.hom.left.stalkMap y)) :
    Module.finrank ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))
      ↑(TopCat.Presheaf.stalk (directImage p.hom.left).val.presheaf (p.hom.left.base y)) = 1 := by
  let := stalkAlgebra p.hom.left y
  have hbij : Function.Bijective (p.hom.left.stalkMap y).hom :=
    (ConcreteCategory.isIso_iff_bijective (p.hom.left.stalkMap y)).mp hs
  let e₁ := stalkLinearEquiv p.hom.left y hhom.isInducing
  let e₂ : ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y)) ≃ₗ[↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj
      (p.hom.left.base y))] (Y.obj.left.presheaf.stalk y) :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij
  have : IsLocalRing ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y)) :=
    X.obj.left.isLocalRing (p.hom.left.base y)
  rw [e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_self]

/-- **Stalks of a flat morphism with homeomorphic point map**, given the finite mapping
theorem: if the stalk maps are isomorphisms at the points over a dense subset `V` of the
target, every stalk map is an isomorphism. -/
theorem isIso_stalkMap_of_flat_of_isHomeomorph (H₂ : FiniteMappingTheorem) {p : Y ⟶ X}
    (hhom : IsHomeomorph p.hom.left.base) {V : Set X.obj.left} (hV : Dense V)
    (hgen : ∀ y : Y.obj.left, p.hom.left.base y ∈ V → IsIso (p.hom.left.stalkMap y))
    (hflat : IsFlatMorphism p) (y : Y.obj.left) : IsIso (p.hom.left.stalkMap y) := by
  let M := directImage p.hom.left
  have hfin : ∀ x : X.obj.left, (p.hom.left.base ⁻¹' {x}).Finite := fun x =>
    Set.Subsingleton.finite fun a ha b hb => hhom.injective (ha.trans hb.symm)
  have : M.IsFinitePresentation := H₂ X Y p hhom.isProperMap hfin
  -- flatness of the stalk of `p_* 𝒪_Y` at `p y`
  let := stalkAlgebra p.hom.left y
  have hflatM : Module.Flat ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))
      ↑(TopCat.Presheaf.stalk M.val.presheaf (p.hom.left.base y)) := by
    have : Module.Flat ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))
        (Y.obj.left.presheaf.stalk y) := hflat y
    exact Module.Flat.of_linearEquiv (stalkLinearEquiv p.hom.left y hhom.isInducing)
  have : IsLocalRing ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y)) :=
    X.obj.left.isLocalRing (p.hom.left.base y)
  obtain ⟨r, U, hxU, ⟨e⟩⟩ :=
    exists_free_neighborhood_of_flat_stalk X.obj.left.toSheafedSpace.sheaf
      (p.hom.left.base y) hflatM
  -- the rank is one at a nearby point of the dense set
  obtain ⟨x', hx'U, hx'V⟩ := hV.inter_open_nonempty U.1 U.2 ⟨_, hxU⟩
  obtain ⟨y', rfl⟩ := hhom.surjective x'
  have hr : r = 1 := by
    have h₁ := finrank_stalk_eq_one_of_isIso hhom y' (hgen y' hx'V)
    have : IsLocalRing ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y')) :=
      X.obj.left.isLocalRing (p.hom.left.base y')
    rw [((stalkLinearEquivOfOverIso X.obj.left.toSheafedSpace.sheaf U e _ hx'U).trans
      (finiteFreeStalkLinearEquiv X.obj.left.toSheafedSpace.sheaf (ULift.{0} (Fin r)) _)).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_ulift, Fintype.card_fin] at h₁
    exact h₁
  subst hr
  -- at `p y` the stalk `𝒪_{Y,y}` is free of rank one
  let E : Y.obj.left.presheaf.stalk y ≃ₗ[↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))]
      (ULift.{0} (Fin 1) → ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))) :=
    (stalkLinearEquiv p.hom.left y hhom.isInducing).symm.trans
      ((stalkLinearEquivOfOverIso X.obj.left.toSheafedSpace.sheaf U e _ hxU).trans
        (finiteFreeStalkLinearEquiv X.obj.left.toSheafedSpace.sheaf (ULift.{0} (Fin 1)) _))
  have : Module.Free ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))
      (Y.obj.left.presheaf.stalk y) := Module.Free.of_equiv E.symm
  have : Module.Finite ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))
      (Y.obj.left.presheaf.stalk y) := Module.Finite.equiv E.symm
  have hrank : Module.finrank ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj (p.hom.left.base y))
      (Y.obj.left.presheaf.stalk y) = 1 := by
    rw [E.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_ulift, Fintype.card_fin]
  have hbij : Function.Bijective (p.hom.left.stalkMap y).hom :=
    algebraMap_bijective_of_free_of_finrank_eq_one hrank
  exact (ConcreteCategory.isIso_iff_bijective (p.hom.left.stalkMap y)).mpr hbij

/-- **A flat proper morphism which is generically an isomorphism is an isomorphism**
(general form of `chow:flat-bimeromorphic-iso`), from the two named classical inputs.
`V` is any dense subset of the target over which the point map is bijective and at whose
points the stalk maps are isomorphisms; no analyticity of the complement is used. -/
theorem isIso_of_flat_of_dense_stalk_iso (H₁ : FlatMorphismsAreOpen)
    (H₂ : FiniteMappingTheorem) {p : Y ⟶ X} (hproper : IsProperMap p.hom.left.base)
    (hflat : IsFlatMorphism p) {V : Set X.obj.left} (hV : Dense V)
    (hinj : InjOn p.hom.left.base (p.hom.left.base ⁻¹' V)) (hrange : V ⊆ range p.hom.left.base)
    (hgen : ∀ y : Y.obj.left, p.hom.left.base y ∈ V → IsIso (p.hom.left.stalkMap y)) :
    IsIso p := by
  have : T2Space Y.obj.left.toPresheafedSpace := Y.property.1
  have hhom : IsHomeomorph p.hom.left.base :=
    isHomeomorph_of_isOpenMap_of_isProperMap (H₁ X Y p hflat) hproper hV hinj hrange
  exact isIso_of_isHomeomorph_of_isIso_stalkMap p hhom
    (isIso_stalkMap_of_flat_of_isHomeomorph H₂ hhom hV hgen hflat)

/-- **Stalks of a flat open proper bimeromorphic morphism**, given the finite mapping
theorem: every stalk map is an isomorphism. -/
theorem isIso_stalkMap_of_flat (H₂ : FiniteMappingTheorem) {p : Y ⟶ X}
    (hp : IsProperBimeromorphic p) (ho : IsOpenMap p.hom.left.base)
    (hflat : IsFlatMorphism p) (y : Y.obj.left) : IsIso (p.hom.left.stalkMap y) := by
  have hhom : IsHomeomorph p.hom.left.base :=
    isHomeomorph_of_isProperBimeromorphic_of_isOpenMap hp ho
  obtain ⟨_hproper, Z, _hZa, hZt, _hpre, hiso⟩ := hp
  exact isIso_stalkMap_of_flat_of_isHomeomorph H₂ hhom
    (interior_eq_empty_iff_dense_compl.mp hZt)
    (fun y' hy' => isIso_stalkMap_of_isIsoOver hiso y' hy') hflat y

/-- **A flat proper bimeromorphic morphism of reduced complex spaces is an isomorphism**
(`chow:flat-bimeromorphic-iso`), from the two named classical inputs. -/
theorem isIso_of_isProperBimeromorphic_of_flat (H₁ : FlatMorphismsAreOpen)
    (H₂ : FiniteMappingTheorem) {p : Y ⟶ X} (hp : IsProperBimeromorphic p)
    (hflat : IsFlatMorphism p) : IsIso p := by
  have ho : IsOpenMap p.hom.left.base := H₁ X Y p hflat
  exact isIso_of_isProperBimeromorphic_of_isOpenMap hp ho
    (isIso_stalkMap_of_flat H₂ hp ho hflat)

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowFlatBimeromorphicIso

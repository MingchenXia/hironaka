import Hironaka.Analytic.Unibranch.HironakaG10GlStepSquare

/-!
# Pulled torsion presentations over an arbitrary square, and their transport to one flattening step

Lane G10HP, run 0081 (continuing lane G10GL, item GL-3b, `hpres` assembly).  The consumer
`HironakaG10GlStrictFlatAssembly.PulledPresentation s c y''` is stated for the native blowup `X' = Bl_B X` of one
flattening step, while the canonical-chart machinery reads the strict transform through the geometric blowup
`Bl_B X` and the induced map `inducedMorphism`.  Here:

* `GenPresentation σ p q f D y'' z hz` — the fields of `PulledPresentation` over an ARBITRARY square
  `p ≫ σ = q ≫ f` of reduced complex spaces (`D` the centre ideals of the base), at a point `y''` and a base point
  `z = p y''` (Hironaka 1975, Lemma 4.4.5, printed pp. 537–538: the strict transform is the fibre product modulo its
  exceptional torsion, and the flattener commutes with base change); the closed-fibre field is stated intrinsically
  (`nonunit`: nonunits of the presentation ring lie in its Jacobson radical);
* `GenPresentation.transport` / `nonempty_transport` — transport along an isomorphism `ι : X₁ ≅ X₂` of new bases
  over the old base (BC3, `HironakaG10SbBlowupComparison.blowupIso`): stalk isomorphism of `ι`, `stalkMap_comp`;
* `GenPresentation.toPulled` — at one flattening step, a generic presentation for `stepσ`, `f'`, `stepQ` IS a
  `PulledPresentation` (the closed-fibre field `local_` from `nonunit`, `comm` and locality of `f'^♯`);
* `quotient_nonunit_mem_jacobson` — the `nonunit` field for a quotient of a local ring.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10GlPresentationTransport

open Hironaka HironakaG10HirFlatQuotient
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform

noncomputable section

/-! ### Algebra -/

/-- In a quotient of a local ring, every nonunit lies in the Jacobson radical. -/
theorem quotient_nonunit_mem_jacobson {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) (b : R ⧸ I)
    (hb : ¬ IsUnit b) : b ∈ (⊥ : Ideal (R ⧸ I)).jacobson := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hr : r ∈ IsLocalRing.maximalIdeal R := fun hu => hb (hu.map (Ideal.Quotient.mk I))
  have hj := IsLocalRing.maximalIdeal_le_jacobson ⊥ hr
  rw [Ideal.mem_jacobson_bot] at hj ⊢
  intro y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h := (hj s).map (Ideal.Quotient.mk I)
  rwa [map_add, map_mul, map_one] at h

/-- Flattener ideals transported along a ring isomorphism of the base, in `map` form. -/
theorem isFlattenerIdeal_comp_symm {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B] {φ : A →+* B}
    {I : Ideal A} (h : IsFlattenerIdeal φ I) (e : A ≃+* A') :
    IsFlattenerIdeal (φ.comp e.symm.toRingHom) (Ideal.map e.toRingHom I) := by
  have H := h.comp_ringEquiv e.symm
  have hI : Ideal.comap e.symm.toRingHom I = Ideal.map e.toRingHom I := Ideal.comap_symm (I := I) e
  rw [hI] at H
  exact H

/-! ### Generic presentations -/

/-- A **pulled torsion presentation over an arbitrary square** `p ≫ σ = q ≫ f` (the fields of
`HironakaG10GlStrictFlatAssembly.PulledPresentation`, with the new base read at a point `z = p y''`):
a noetherian ring `B` over the stalk at `z` whose quotient by its `ψ g`-power torsion is the stalk at `y''` (over the
stalk at `z`), with `g` a generator of the pulled centre, the flattener of `ψ` the pull-back of the pointed flattener
of `f`, and every nonunit of `B` in its Jacobson radical. -/
structure GenPresentation {X X₁ Y Y₁ : SourceReducedComplexSpace} (σ : X₁ ⟶ X) (p : Y₁ ⟶ X₁) (q : Y₁ ⟶ Y)
    (f : Y ⟶ X) (D : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)) (y'' : Y₁.obj.left)
    (z : X₁.obj.left) (hz : p.hom.left.base y'' = z) where
  /-- the presentation ring (the local ring of the fibre product) -/
  B : Type
  [ring : CommRing B]
  [noetherian : IsNoetherianRing B]
  /-- its structure map over the new base -/
  ψ : X₁.obj.left.presheaf.stalk z →+* B
  /-- a generator of the pulled centre -/
  g : X₁.obj.left.presheaf.stalk z
  span_g : Ideal.map (σ.hom.left.stalkMap z).hom (D (σ.hom.left.base z)) = Ideal.span {g}
  /-- the source stalk is the presentation ring modulo its exceptional torsion -/
  β : B ⧸ powerSat (⊥ : Ideal B) (ψ g) ≃+* Y₁.obj.left.presheaf.stalk y''
  comm : ∀ a, β (Ideal.Quotient.mk _ (ψ a)) = fibreStalkMap p z y'' hz a
  /-- base change of the pointed flattener -/
  flattener : ∀ (h : f.hom.left.base (q.hom.left.base y'') = σ.hom.left.base z)
    (P : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base z))),
    IsPointFlattenerAt f _ (q.hom.left.base y'') h P →
      IsFlattenerIdeal ψ (Ideal.map (σ.hom.left.stalkMap z).hom P)
  /-- the closed fibre: nonunits lie in the Jacobson radical -/
  nonunit : ∀ b : B, ¬ IsUnit b → b ∈ (⊥ : Ideal B).jacobson

attribute [instance] GenPresentation.ring GenPresentation.noetherian

/-- The ring isomorphism of stalks of an isomorphism of reduced complex spaces. -/
def isoStalkEquiv {S T : SourceReducedComplexSpace} (ι : S ≅ T) (s : S.obj.left) :
    T.obj.left.presheaf.stalk (ι.hom.hom.left.base s) ≃+* S.obj.left.presheaf.stalk s :=
  haveI : IsIso ι.hom.hom.left :=
    ⟨⟨ι.inv.hom.left, congrArg (fun f => f.hom.left) ι.hom_inv_id,
      congrArg (fun f => f.hom.left) ι.inv_hom_id⟩⟩
  haveI : IsIso (ι.hom.hom.left.stalkMap s) := LocallyRingedSpace.IsOpenImmersion.stalk_iso _ s
  (asIso (ι.hom.hom.left.stalkMap s)).commRingCatIsoToRingEquiv

theorem isoStalkEquiv_apply {S T : SourceReducedComplexSpace} (ι : S ≅ T) (s : S.obj.left)
    (r : T.obj.left.presheaf.stalk (ι.hom.hom.left.base s)) :
    isoStalkEquiv ι s r = (ι.hom.hom.left.stalkMap s).hom r :=
  rfl

section Transport

variable {X X₁ X₂ Y Y₁ : SourceReducedComplexSpace} (ι : X₁ ≅ X₂) (σ₂ : X₂ ⟶ X) (q : Y₁ ⟶ Y) (f : Y ⟶ X)
  (D : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)) (p₁ : Y₁ ⟶ X₁) (y'' : Y₁.obj.left)

/-- The stalk map of `ι ≫ σ₂` is the stalk map of `σ₂` followed by the stalk isomorphism of `ι`. -/
theorem stalkMap_comp_iso (x₁ : X₁.obj.left) :
    ((ι.hom ≫ σ₂).hom.left.stalkMap x₁).hom =
      (isoStalkEquiv ι x₁).toRingHom.comp (σ₂.hom.left.stalkMap (ι.hom.hom.left.base x₁)).hom :=
  congrArg CommRingCat.Hom.hom (LocallyRingedSpace.stalkMap_comp ι.hom.hom.left σ₂.hom.left x₁)

theorem map_stalkMap_comp_iso (x₁ : X₁.obj.left) (I : Ideal (X.obj.left.presheaf.stalk
      (σ₂.hom.left.base (ι.hom.hom.left.base x₁)))) :
    Ideal.map ((ι.hom ≫ σ₂).hom.left.stalkMap x₁).hom I =
      Ideal.map (isoStalkEquiv ι x₁).toRingHom (Ideal.map (σ₂.hom.left.stalkMap (ι.hom.hom.left.base x₁)).hom I) := by
  rw [Ideal.map_map, stalkMap_comp_iso]

/-- **Transport along an isomorphism of new bases over the old base.** -/
def GenPresentation.transport
    (P : GenPresentation σ₂ (p₁ ≫ ι.hom) q f D y'' (ι.hom.hom.left.base (p₁.hom.left.base y'')) rfl) :
    GenPresentation (ι.hom ≫ σ₂) p₁ q f D y'' (p₁.hom.left.base y'') rfl where
  B := P.B
  ψ := P.ψ.comp (isoStalkEquiv ι (p₁.hom.left.base y'')).symm.toRingHom
  g := isoStalkEquiv ι (p₁.hom.left.base y'') P.g
  span_g := (map_stalkMap_comp_iso ι σ₂ (p₁.hom.left.base y'') _).trans
    ((congrArg (Ideal.map (isoStalkEquiv ι (p₁.hom.left.base y'')).toRingHom) P.span_g).trans
      (by rw [Ideal.map_span, Set.image_singleton]; rfl))
  β := (Ideal.quotEquivOfEq (congrArg (powerSat (⊥ : Ideal P.B))
      (congrArg P.ψ ((isoStalkEquiv ι (p₁.hom.left.base y'')).symm_apply_apply P.g)))).trans P.β
  comm a := by
    have hc := ConcreteCategory.congr_hom
      (LocallyRingedSpace.stalkMap_comp p₁.hom.left ι.hom.hom.left y'')
      ((isoStalkEquiv ι (p₁.hom.left.base y'')).symm a)
    exact (congrArg P.β (Ideal.quotEquivOfEq_mk _ _)).trans
      ((P.comm ((isoStalkEquiv ι (p₁.hom.left.base y'')).symm a)).trans
        (hc.trans (congrArg (p₁.hom.left.stalkMap y'').hom
          ((isoStalkEquiv ι (p₁.hom.left.base y'')).apply_symm_apply a))))
  flattener h P' hP := by
    have H := isFlattenerIdeal_comp_symm (P.flattener h P' hP) (isoStalkEquiv ι (p₁.hom.left.base y''))
    rw [← map_stalkMap_comp_iso ι σ₂ (p₁.hom.left.base y'') P'] at H
    exact H
  nonunit := P.nonunit

/-- **Transport along an isomorphism of new bases**, with the square and the base point as equations. -/
theorem nonempty_transport (σ₁ : X₁ ⟶ X) (hσ : ι.hom ≫ σ₂ = σ₁) (p₂ : Y₁ ⟶ X₂) (hp : p₁ ≫ ι.hom = p₂)
    (z : X₂.obj.left) (hz : p₂.hom.left.base y'' = z) (P : GenPresentation σ₂ p₂ q f D y'' z hz) :
    Nonempty (GenPresentation σ₁ p₁ q f D y'' (p₁.hom.left.base y'') rfl) := by
  subst hσ hp hz
  exact ⟨P.transport ι σ₂ q f D p₁ y''⟩

end Transport

/-! ### One flattening step -/

/-- **A generic presentation for one flattening step is a pulled torsion presentation.** -/
def GenPresentation.toPulled (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left)
    (P : GenPresentation (stepσ s c) (nextWith s c).f (stepQ s c) s.f (centreIdeal c) y''
      ((nextWith s c).f.hom.left.base y'') rfl) :
    PulledPresentation s c y'' where
  B := P.B
  ψ := P.ψ
  g := P.g
  span_g := P.span_g
  β := P.β
  comm := P.comm
  flattener := P.flattener
  local_ := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => P.nonunit _ fun hu => ?_
    have h1 : IsUnit (P.β (Ideal.Quotient.mk _ (P.ψ a))) := (hu.map (Ideal.Quotient.mk _)).map P.β
    rw [P.comm a] at h1
    exact (IsLocalRing.mem_maximalIdeal _).mp
      (map_nonunit ((nextWith s c).f.hom.left.stalkMap y'').hom a ha) h1

end

end Hironaka.Analytic.Unibranch.HironakaG10GlPresentationTransport

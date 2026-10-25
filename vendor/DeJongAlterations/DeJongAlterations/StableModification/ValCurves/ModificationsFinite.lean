import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.AlgebraicClosure
import DeJongAlterations.StableModification.ValuationRing.FibreDimension
import DeJongAlterations.Geometry.NormalCurveModification

/-!
# Proper morphisms with algebraic fibres are finite

This file collects the scheme-theoretic tools behind Temkin's §4.2 (M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), `semi-stable.tex`
lines 2857–2946): for a morphism `g : X → Y` and `x ∈ X`, write `IsAlgebraicAt g x` if the
residue field extension `κ(x)/κ(g x)` is algebraic (equivalently `fiberTrdeg g x = 0`).

* `isAlgebraicAt_of_quasiFiniteAt`: at a quasi-finite point the residue field extension is
  finite, hence algebraic.
* `isClosed_singleton_asFiber_of_isAlgebraicAt`: for `g` separated, a point with algebraic
  residue field extension is closed in its fibre (`Spec κ(x) → Spec κ(g x)` is integral, hence
  universally closed, so `Spec κ(x) → X_{g x}` is universally closed).
* `finite_inter_preimage_of_isAlgebraicAt`: for `g` quasi-compact, separated and locally of
  finite type and a closed `T ⊆ X`, if every point of `T` over `y` is algebraic over `κ(y)`, then
  `T ∩ g⁻¹(y)` is finite (a closed subset of the Noetherian sober fibre consisting of closed
  points).
* `exists_isFinite_morphismRestrict_of_isAlgebraicAt`: **a proper morphism whose fibre over `y`
  consists of points algebraic over `κ(y)` is finite over a neighbourhood `V` of `y`**, and every
  point over `V` is algebraic over its image. This replaces the reference to EGA IV 8.11.1 in
  Temkin's proof of Lemma 4.2.1 (lines 2899–2900) by Zariski's Main Theorem in Mathlib
  (`exists_isFinite_morphismRestrict_of_finite_preimage_singleton`).
* `isAlgebraicAt_pullback_fst`: in a fibre product `X ×_S Y`, if `κ(y)/κ(s)` is algebraic then
  so is `κ(t)/κ(x)` (the residue field of `t` is algebraic over the relative algebraic closure of
  `κ(x)` in it, by the universal property of the fibre product). This is the step "therefore `x`
  has to be a closed point of `C̄_s`" of Temkin's proof of Proposition 4.2.3 (line 2945).
* `fiberTrdeg_comp`: transcendence degrees of residue fields add in a composite.

Blueprint chapter `sm-val-modifications.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace DeJongAlterations.StableModification.ValCurves

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

/-- In a Noetherian quasi-sober space, a closed set all of whose points are closed is finite. -/
theorem finite_of_isClosed_of_forall_isClosed {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] [QuasiSober α] {T : Set α} (hT : IsClosed T)
    (h : ∀ x ∈ T, IsClosed ({x} : Set α)) : T.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  refine Set.Finite.sUnion hSf fun t ht ↦ ?_
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  have hζt : ζ ∈ t := hζ.mem
  rw [← hζ.def, (h ζ (Set.mem_sUnion_of_mem hζt ht)).closure_eq]
  exact Set.finite_singleton ζ

variable {X Y Z : Scheme.{u}}

/-- The residue field extension `κ(x)/κ(g x)` of `g : X → Y` at `x` is algebraic (integral). -/
def IsAlgebraicAt (g : X ⟶ Y) (x : X) : Prop :=
  (g.residueFieldMap x).hom.IsIntegral

/-- Algebraicity of the residue field extension is the vanishing of its transcendence
degree. -/
theorem isAlgebraicAt_iff_fiberTrdeg_eq_zero (g : X ⟶ Y) (x : X) :
    IsAlgebraicAt g x ↔ fiberTrdeg g x = 0 := by
  let := (g.residueFieldMap x).hom.toAlgebra
  rw [fiberTrdeg, trdeg_eq_zero_iff, Algebra.isAlgebraic_iff_isIntegral]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.1⟩

/-- Transcendence degrees of residue field extensions add in a composite. -/
theorem fiberTrdeg_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    fiberTrdeg (f ≫ g) x = fiberTrdeg g (f x) + fiberTrdeg f x := by
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let := (g.residueFieldMap (f x) ≫ f.residueFieldMap x).hom.toAlgebra
  have e : fiberTrdeg (f ≫ g) x = Algebra.trdeg (Z.residueField (g (f x))) (X.residueField x) := by
    change @Algebra.trdeg (Z.residueField (g (f x))) (X.residueField x) _ _
      ((f ≫ g).residueFieldMap x).hom.toAlgebra = _
    rw [Scheme.residueFieldMap_comp]
    rfl
  have : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FaithfulSMul (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have : FaithfulSMul (Y.residueField (f x)) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  rw [e]
  exact (trdeg_add_eq (Z.residueField (g (f x))) (Y.residueField (f x))
    (A := X.residueField x)).symm

/-- Algebraic residue field extensions compose. -/
theorem IsAlgebraicAt.comp {f : X ⟶ Y} {g : Y ⟶ Z} {x : X} (hf : IsAlgebraicAt f x)
    (hg : IsAlgebraicAt g (f x)) : IsAlgebraicAt (f ≫ g) x := by
  change ((f ≫ g).residueFieldMap x).hom.IsIntegral
  have e : ((f ≫ g).residueFieldMap x).hom =
      (f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom := by
    change ((f ≫ g).residueFieldMap x).hom = (g.residueFieldMap (f x) ≫ f.residueFieldMap x).hom
    rw [Scheme.residueFieldMap_comp]
    rfl
  rw [e]
  exact RingHom.IsIntegral.trans _ _ hg hf

/-- A surjective residue field map is algebraic. -/
theorem isAlgebraicAt_of_surjective {g : X ⟶ Y} {x : X}
    (h : Function.Surjective (g.residueFieldMap x)) : IsAlgebraicAt g x :=
  RingHom.isIntegral_of_surjective _ h

/-- A morphism whose stalk map at `x` is surjective (e.g. an isomorphism of local rings) has
trivial, hence algebraic, residue field extension at `x`. -/
theorem isAlgebraicAt_of_stalkMap_surjective {g : X ⟶ Y} {x : X}
    (h : Function.Surjective (g.stalkMap x)) : IsAlgebraicAt g x := by
  refine isAlgebraicAt_of_surjective fun z ↦ ?_
  obtain ⟨b, rfl⟩ := X.residue_surjective x z
  obtain ⟨a, rfl⟩ := h b
  refine ⟨Y.residue (g x) a, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-- A morphism which is surjective on stalks (e.g. a closed immersion) has trivial residue field
extensions. -/
theorem isAlgebraicAt_of_surjectiveOnStalks (g : X ⟶ Y) [SurjectiveOnStalks g] (x : X) :
    IsAlgebraicAt g x :=
  isAlgebraicAt_of_stalkMap_surjective (g.stalkMap_surjective x)

/-- An isomorphism of local rings gives an algebraic residue field extension. -/
theorem isAlgebraicAt_of_isIso_stalkMap {g : X ⟶ Y} {x : X} [IsIso (g.stalkMap x)] :
    IsAlgebraicAt g x :=
  isAlgebraicAt_of_stalkMap_surjective (ConcreteCategory.bijective_of_isIso (g.stalkMap x)).2

/-- **Quasi-finite points are algebraic**: if `g` is quasi-finite at `x`, the residue field
extension `κ(x)/κ(g x)` is finite. -/
theorem isAlgebraicAt_of_quasiFiniteAt {g : X ⟶ Y} {x : X} (h : g.QuasiFiniteAt x) :
    IsAlgebraicAt g x := by
  let R := Y.presheaf.stalk (g x)
  let B := X.presheaf.stalk x
  let : Algebra R B := (g.stalkMap x).hom.toAlgebra
  let : Algebra R (X.residueField x) := (g.stalkMap x ≫ X.residue x).hom.toAlgebra
  have hQF : Algebra.QuasiFinite R B := h
  let e : B →ₐ[R] X.residueField x := { (X.residue x).hom with commutes' := fun _ ↦ rfl }
  have : Algebra.QuasiFinite R (X.residueField x) :=
    Algebra.QuasiFinite.of_surjective_algHom e (X.residue_surjective x)
  let : Algebra R (Y.residueField (g x)) := (Y.residue (g x)).hom.toAlgebra
  let := (g.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower R (Y.residueField (g x)) (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (g.stalkMap x ≫ X.residue x).hom r = (Y.residue (g x) ≫ g.residueFieldMap x).hom r
    rw [Scheme.residue_residueFieldMap]
  have : Algebra.QuasiFinite (Y.residueField (g x)) (X.residueField x) :=
    Algebra.QuasiFinite.of_restrictScalars R _ _
  have : Module.Finite (Y.residueField (g x)) (X.residueField x) := Module.Finite.of_quasiFinite
  exact (Algebra.IsIntegral.of_finite (Y.residueField (g x)) (X.residueField x)).isIntegral

/-- **A point with algebraic residue field extension is closed in its fibre** (for `g`
separated): `Spec κ(x) → Spec κ(g x)` is integral, so `Spec κ(x) → X_{g x}` is universally
closed. -/
theorem isClosed_singleton_asFiber_of_isAlgebraicAt (g : X ⟶ Y) [IsSeparated g] {x : X}
    (hx : IsAlgebraicAt g x) : IsClosed {g.asFiber x} := by
  have : IsIntegralHom (Spec.map (g.residueFieldMap x)) := IsIntegralHom.SpecMap_iff.mpr hx
  have : IsIntegralHom (g.asFiberHom x ≫ g.fiberToSpecResidueField (g x)) := by
    rw [g.asFiberHom_fiberToSpecResidueField]
    infer_instance
  have : IsSeparated (g.fiberToSpecResidueField (g x)) :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have := IsIntegralHom.of_comp (g.asFiberHom x) (g.fiberToSpecResidueField (g x))
  have : UniversallyClosed (g.asFiberHom x) :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp this).1
  rw [← g.range_asFiberHom x]
  exact (g.asFiberHom x).isClosedMap.isClosed_range

/-- A point with algebraic residue field extension is closed in the set-theoretic fibre. -/
theorem isClosed_singleton_preimage_of_isAlgebraicAt (g : X ⟶ Y) [IsSeparated g] {x : X}
    {y : Y} (h : g x = y) (hx : IsAlgebraicAt g x) :
    IsClosed ({⟨x, h⟩} : Set (g ⁻¹' {y})) := by
  subst h
  have h1 := isClosed_singleton_asFiber_of_isAlgebraicAt g hx
  rw [← (g.fiberHomeo (g x)).isClosed_image, Set.image_singleton] at h1
  convert h1
  simp [Scheme.Hom.asFiber]

/-- **Finiteness of algebraic fibres.** Let `g` be quasi-compact, separated and locally of
finite type, `T ⊆ X` closed and `y ∈ Y`. If every point of `T` over `y` has residue field
algebraic over `κ(y)`, then `T ∩ g⁻¹(y)` is finite. -/
theorem finite_inter_preimage_of_isAlgebraicAt (g : X ⟶ Y) [QuasiCompact g] [IsSeparated g]
    [LocallyOfFiniteType g] {T : Set X} (hT : IsClosed T) (y : Y)
    (h : ∀ x ∈ T, g x = y → IsAlgebraicAt g x) : (T ∩ g ⁻¹' {y}).Finite := by
  have : IsLocallyNoetherian (g.fiber y) := inferInstanceAs (IsLocallyNoetherian (pullback _ _))
  have : IsNoetherian (g.fiber y) := {}
  let e := g.fiberHomeo y
  have : TopologicalSpace.NoetherianSpace (g ⁻¹' {y}) :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph e).mp inferInstance
  have : QuasiSober (g ⁻¹' {y}) := e.symm.isClosedEmbedding.quasiSober
  let T₀ : Set (g ⁻¹' {y}) := Subtype.val ⁻¹' T
  have hfin : T₀.Finite := finite_of_isClosed_of_forall_isClosed
    (hT.preimage continuous_subtype_val)
    fun p hp ↦ isClosed_singleton_preimage_of_isAlgebraicAt g p.2 (h p.1 hp p.2)
  have heq : T ∩ g ⁻¹' {y} = Subtype.val '' T₀ := by
    ext x
    constructor
    · rintro ⟨hxT, hxy⟩
      exact ⟨⟨x, hxy⟩, hxT, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, p.2⟩
  rw [heq]
  exact hfin.image _

/-- Quasi-finiteness at a point transfers from the restriction to an open of the source. -/
theorem quasiFiniteAt_of_comp_ι (g : X ⟶ Y) (V : Y.Opens) {x : X} (hx : g x ∈ V)
    (h : ((g ⁻¹ᵁ V).ι ≫ g).QuasiFiniteAt ⟨x, hx⟩) : g.QuasiFiniteAt x := by
  have h' := Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mp h
  have e : (g ⁻¹ᵁ V).ι ⟨x, hx⟩ = x := Scheme.Opens.ι_apply _ _
  rwa [e] at h'

/-- A point over an open `V` over which `g` is finite is a quasi-finite point of `g`. -/
theorem quasiFiniteAt_of_isFinite_morphismRestrict (g : X ⟶ Y) (V : Y.Opens) [IsFinite (g ∣_ V)]
    {x : X} (hx : g x ∈ V) : g.QuasiFiniteAt x := by
  have h1 : (g ∣_ V).QuasiFiniteAt ⟨x, hx⟩ := (g ∣_ V).quasiFiniteAt _
  have h2 : (g ∣_ V ≫ V.ι).QuasiFiniteAt ⟨x, hx⟩ := Scheme.Hom.quasiFiniteAt_comp_iff.mpr h1
  rw [morphismRestrict_ι] at h2
  exact quasiFiniteAt_of_comp_ι g V hx h2

/-- **Proper morphisms with algebraic fibres are finite nearby.** Let `g` be proper and `y ∈ Y`
such that every point over `y` has residue field algebraic over `κ(y)`. Then there is an open
`V ∋ y` over which `g` is finite, and every point over `V` has algebraic residue field
extension. -/
theorem exists_isFinite_morphismRestrict_of_isAlgebraicAt (g : X ⟶ Y) [IsProper g] (y : Y)
    (h : ∀ x, g x = y → IsAlgebraicAt g x) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (g ∣_ V) ∧ ∀ x, g x ∈ V → IsAlgebraicAt g x := by
  have hfin : (g ⁻¹' {y}).Finite := by
    have := finite_inter_preimage_of_isAlgebraicAt g isClosed_univ y fun x _ hx ↦ h x hx
    rwa [Set.univ_inter] at this
  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton g y hfin
  refine ⟨V, hyV, hV, fun x hx ↦ isAlgebraicAt_of_quasiFiniteAt ?_⟩
  exact quasiFiniteAt_of_isFinite_morphismRestrict g V hx

/-- Morphisms out of `Spec K₁` are determined by their composites with `Spec K → Spec K₁` for a
field extension `K₁ → K`. -/
theorem eq_of_SpecMap_comp_eq {K₁ K : Type u} [Field K₁] [Field K]
    (ι : CommRingCat.of K₁ ⟶ CommRingCat.of K) {T : Scheme.{u}} {h₁ h₂ : Spec (.of K₁) ⟶ T}
    (h : Spec.map ι ≫ h₁ = Spec.map ι ≫ h₂) : h₁ = h₂ := by
  obtain ⟨⟨p₁, d₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ T).symm.surjective h₁
  obtain ⟨⟨p₂, d₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ T).symm.surjective h₂
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc] at h
  have h' : (Scheme.SpecToEquivOfField K T).symm ⟨p₁, d₁ ≫ ι⟩ =
      (Scheme.SpecToEquivOfField K T).symm ⟨p₂, d₂ ≫ ι⟩ := h
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    ((Scheme.SpecToEquivOfField K T).symm.injective h')
  dsimp only at e he
  subst e
  have : Mono ι := ConcreteCategory.mono_of_injective _ ι.hom.injective
  have hd : d₁ = d₂ := by
    rw [← cancel_mono ι]
    simpa using he
  rw [hd]

/-- **Residue fields of a fibre product.** For `t ∈ X ×_S Y` with images `x ∈ X` and `y ∈ Y`, if
`κ(y)` is algebraic over `κ(g y)` then `κ(t)` is algebraic over `κ(x)`. The relative algebraic
closure `K₁` of `κ(x)` in `κ(t)` contains the image of `κ(y)`, so the canonical point
`Spec κ(t) → X ×_S Y` factors through `Spec K₁`; hence `K₁ = κ(t)`. -/
theorem isAlgebraicAt_pullback_fst {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) (h : IsAlgebraicAt g (pullback.snd f g t)) :
    IsAlgebraicAt (pullback.fst f g) t := by
  let x := pullback.fst f g t
  let y := pullback.snd f g t
  let K := (pullback f g).residueField t
  let a : X.residueField x ⟶ K := (pullback.fst f g).residueFieldMap t
  let b : Y.residueField y ⟶ K := (pullback.snd f g).residueFieldMap t
  let := a.hom.toAlgebra
  let K₁ := algebraicClosure (X.residueField x) K
  -- compatibility over the base
  let T := Scheme.Pullback.Triplet.ofPoint t
  have hy : g y = f x := T.hy
  let A : S.residueField (f x) ⟶ X.residueField x :=
    (S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x
  let B : S.residueField (f x) ⟶ Y.residueField y :=
    (S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y
  have hc : a.hom.comp A.hom = b.hom.comp B.hom := by
    have := congrArg CommRingCat.Hom.hom
      (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint (f := f) (g := g) t)
    exact this
  have hB : B.hom.comp (S.residueFieldCongr hy).hom.hom = (g.residueFieldMap y).hom := by
    change ((S.residueFieldCongr hy).hom ≫ (S.residueFieldCongr hy).inv ≫
      g.residueFieldMap y).hom = _
    rw [Iso.hom_inv_id_assoc]
  have hb : ∀ w : Y.residueField y, b.hom w ∈ K₁ := by
    intro w
    rw [mem_algebraicClosure_iff']
    obtain ⟨p, hpm, hpw⟩ := h w
    refine ⟨(p.map (S.residueFieldCongr hy).hom.hom).map A.hom, (hpm.map _).map _, ?_⟩
    change Polynomial.eval₂ a.hom (b.hom w) _ = 0
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, Polynomial.eval₂_map, hB, hpw, map_zero]
  -- the morphisms from `Spec K₁`
  let a₁ : X.residueField x ⟶ CommRingCat.of K₁ :=
    CommRingCat.ofHom (algebraMap (X.residueField x) K₁)
  let b₁ : Y.residueField y ⟶ CommRingCat.of K₁ := CommRingCat.ofHom (b.hom.codRestrict K₁ hb)
  let ι : CommRingCat.of K₁ ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap K₁ K)
  have ha₁ : a₁ ≫ ι = a := rfl
  have hb₁ : b₁ ≫ ι = b := rfl
  let ψ₁ : Spec (.of K₁) ⟶ X := Spec.map a₁ ≫ X.fromSpecResidueField x
  let ψ₂ : Spec (.of K₁) ⟶ Y := Spec.map b₁ ≫ Y.fromSpecResidueField y
  have h₁ : Spec.map ι ≫ ψ₁ = (pullback f g).fromSpecResidueField t ≫ pullback.fst f g := by
    rw [← Spec.map_comp_assoc, ha₁]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (pullback.fst f g) t
  have h₂ : Spec.map ι ≫ ψ₂ = (pullback f g).fromSpecResidueField t ≫ pullback.snd f g := by
    rw [← Spec.map_comp_assoc, hb₁]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (pullback.snd f g) t
  have hcond : ψ₁ ≫ f = ψ₂ ≫ g := by
    refine eq_of_SpecMap_comp_eq ι ?_
    rw [← Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, Category.assoc,
      pullback.condition]
  let L' := pullback.lift ψ₁ ψ₂ hcond
  have hL : Spec.map ι ≫ L' = (pullback f g).fromSpecResidueField t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, h₁]
    · rw [Category.assoc, pullback.lift_snd, h₂]
  obtain ⟨⟨p, d⟩, hpd⟩ := (Scheme.SpecToEquivOfField K₁ (pullback f g)).symm.surjective L'
  have key : (Scheme.SpecToEquivOfField K (pullback f g)).symm ⟨p, d ≫ ι⟩ =
      (Scheme.SpecToEquivOfField K (pullback f g)).symm ⟨t, 𝟙 _⟩ := by
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hpd ⊢
    rw [Spec.map_comp, Category.assoc, hpd, hL, Spec.map_id]
    exact (Category.id_comp _).symm
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    ((Scheme.SpecToEquivOfField K (pullback f g)).symm.injective key)
  dsimp only at e he
  intro z
  have hz : (d ≫ ι).hom (((pullback f g).residueFieldCongr e).inv.hom z) = z := by
    rw [he, Category.comp_id, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  rw [← hz]
  exact mem_algebraicClosure_iff'.mp (d.hom (((pullback f g).residueFieldCongr e).inv.hom z)).2
section Normal

open Geometry.NormalCurveModification (affineSections_isIntegrallyClosed)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [IsIntegral X] [IsIntegral Y]

/-- The function field map `K(Y) → K(X)` of a morphism `f` of integral schemes sending the generic
point to the generic point. -/
def genericFieldMap (f : X ⟶ Y) (hgen : f (genericPoint X) = genericPoint Y) :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫ f.stalkMap (genericPoint X)

/-- Naturality of the function field map with respect to local rings. -/
theorem genericFieldMap_stalk (f : X ⟶ Y) (hgen : f (genericPoint X) = genericPoint Y) (x : X) :
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) ≫
      genericFieldMap f hgen =
    f.stalkMap x ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
  change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ (f x))) ≫
      ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫ f.stalkMap (genericPoint X)) =
    f.stalkMap x ≫ X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x))
  simpa only [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp] using
    f.stalkSpecializes_stalkMap (genericPoint X) x
      ((genericPoint_spec X).specializes (Set.mem_univ x))

/-- Naturality of the function field map with respect to sections. -/
theorem genericFieldMap_sections (f : X ⟶ Y) (hgen : f (genericPoint X) = genericPoint Y)
    (U : Y.Opens) [Nonempty U] [hpre : Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ genericFieldMap f hgen =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  let x : f ⁻¹ᵁ U := Classical.choice hpre
  have hY : Y.presheaf.germ U (f x) x.2 ≫
      CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) =
      Y.germToFunctionField U := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a ↦ Y.algebraMap_germ_eq_germToFunctionField x.2 a
  have hX : X.presheaf.germ (f ⁻¹ᵁ U) x x.2 ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.germToFunctionField (f ⁻¹ᵁ U) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a ↦ X.algebraMap_germ_eq_germToFunctionField x.2 a
  rw [← hY, Category.assoc, genericFieldMap_stalk, ← Category.assoc, f.germ_stalkMap,
    Category.assoc, hX]

/-- **Finite birational morphisms onto normal schemes are isomorphisms**, with birationality
expressed by the generic stalk map: a finite morphism `f : X → Y` of integral schemes sending the
generic point to the generic point, with `K(Y) → K(X)` an isomorphism and `Y` normal, is an
isomorphism (on affine opens, `Γ(X, f⁻¹U)` is integral over the integrally closed `Γ(Y, U)` inside
`K(Y)`). This is the form of `Geometry.NormalCurveModification.isIso_of_finite_birational` used
for the graph closure in Temkin's Proposition 4.2.3. -/
theorem isIso_of_isFinite_of_isIso_stalkMap (f : X ⟶ Y) [IsFinite f]
    (hgen : f (genericPoint X) = genericPoint Y) [hiso : IsIso (f.stalkMap (genericPoint X))]
    (hnormal : IsNormalScheme Y) : IsIso f := by
  have hdom : IsDominant f := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq]
    refine Set.eq_univ_of_forall fun y ↦ ?_
    have hsub : ({genericPoint Y} : Set Y) ⊆ Set.range f :=
      Set.singleton_subset_iff.mpr ⟨genericPoint X, hgen⟩
    refine closure_mono hsub ?_
    rw [(genericPoint_spec Y).def]
    trivial
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms _)
    (fun U : Y.affineOpens ↦ U.1) (iSup_affineOpens_eq_top Y)).mpr
  intro a
  let U := a.1
  have hU : IsAffineOpen U := a.2
  by_cases hne : Nonempty U
  · have hpre : Nonempty (f ⁻¹ᵁ U) := by
      obtain ⟨x, hx⟩ := f.denseRange.exists_mem_open U.isOpen (Set.nonempty_coe_sort.mp hne)
      exact ⟨⟨x, hx⟩⟩
    let := hne
    let : IsDomain Γ(Y, U) := IsIntegral.component_integral U
    let : IsIntegrallyClosed Γ(Y, U) := affineSections_isIntegrallyClosed hnormal U hU
    let : IsFractionRing Γ(Y, U) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y U hU
    let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    let : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
    let φ := genericFieldMap f hgen
    have : IsIso φ := by
      dsimp only [φ, genericFieldMap]
      infer_instance
    let g : Γ(X, f ⁻¹ᵁ U) →+* Y.functionField :=
      (inv φ).hom.comp (X.germToFunctionField (f ⁻¹ᵁ U)).hom
    have hg : Function.Injective g :=
      (ConcreteCategory.bijective_of_isIso (inv φ)).1.comp
        (X.germToFunctionField_injective (f ⁻¹ᵁ U))
    have h : g.comp (f.app U).hom = algebraMap Γ(Y, U) Y.functionField := by
      apply CommRingCat.hom_ext_iff.mp
      change (f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U)) ≫ inv φ = _
      rw [← genericFieldMap_sections f hgen, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    let gA : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.functionField :=
      { g with commutes' := fun r ↦ DFunLike.congr_fun h r }
    have hbij : Function.Bijective (f.app U).hom := by
      refine ⟨Function.Injective.of_comp (f := g) ?_, ?_⟩
      · rw [← RingHom.coe_comp, h]
        exact IsFractionRing.injective Γ(Y, U) Y.functionField
      · intro b
        obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff Y.functionField).mp
          (inferInstance : IsIntegrallyClosed Γ(Y, U))
          ((Algebra.IsIntegral.isIntegral b).map gA)
        refine ⟨a, hg ?_⟩
        change (g.comp (f.app U).hom) a = g b
        rwa [h]
    have : IsIso (f.app U) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have : IsIso (f ∣_ U) := (isIso_morphismRestrict_iff_isIso_app f hU).mpr this
    exact this
  · let : IsEmpty U.toScheme := not_nonempty_iff.mp hne
    exact isIso_of_isEmpty (f ∣_ U)

end Normal

end DeJongAlterations.StableModification.ValCurves

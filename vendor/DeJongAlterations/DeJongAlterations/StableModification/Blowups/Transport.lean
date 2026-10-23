import DeJongAlterations.StableModification.Blowups.TransportSection
import DeJongAlterations.StableModification.Blowups.BaseChange
import DeJongAlterations.StableModification.Blowups.SmoothChart
import DeJongAlterations.Geometry.AffineBlowupModification
import DeJongAlterations.StableModification.Valuation.SepClosed

/-!
# Transport of chart blow-ups along étale neighbourhoods

M. Temkin, *Stable modification of relative curves*, proof of Prop 4.3.1 (T:2970–2983) and of
Lemma 4.3.2 (T:3031–3046): locally at a point `x` of the closed fibre of a strictly semi-stable
curve `C` over a valuation ring `R` with separably closed fraction field, there is an étale map
`φ : U ⟶ M` from an open neighbourhood `U ∋ x` to a standard model `M` (`Curves.smoothModel` or
`Curves.nodeModel`), and a chart blow-up `β₀ : M' ⟶ M` (`Blowups.nodeBlowupMorphism`,
`Blowups.smoothBlowupMorphism`) whose centre lies over a closed subscheme `Spec R/J ⊆ Spec R`.
Temkin spreads `β₀` to `C` by base change along `φ` and extends the result "trivially" by the
identity. The extension needs the modification locus to be closed in `C` (`ERRATA.md` DJA-T33);
this file carries out the fix: shrink `U` with `exists_open_isClosed_locus` (strict
henselianity), then glue (`Blowups.extension`).

Blueprint: `sm-boundary-separation.tex`, `lem:sm-transport-glue` and `thm:sm-transport`.

## Main results

* `isIso_morphismRestrict_of_le`, `isIso_pullback_snd_restrict_of_le`: isomorphism loci shrink.
* `IsStrictlySemistable.of_isOpenImmersion_cover`, `IsStrictlySemistable.of_isOpenImmersion_pair`,
  `IsStrictlySemistable.comp_isOpenImmersion`:
  strict semi-stability is checked on a cover by open immersions, and is stable under open
  immersions of the base.
* `isReduced_of_etale_of_cover`: an étale scheme over a scheme covered by spectra of integrally
  closed domains is reduced (it is normal, by `Curves.isNormalScheme_of_etale`); the chart
  blow-ups are so covered (`nodeBlowup_cover`, `smoothBlowup_cover`).
* For the extension `extension W (pullback.snd β₀ φ)` of the pulled-back blow-up:
  `isProper_transport`, `isModification_transport`, `isStrictlySemistable_transport` (with
  marks) and `isStrictlySemistable_transport_top` (without marks).
* `exists_transport_opens`: the shrunk neighbourhood `U₀` and the open `W` over which the
  extension is the identity.
* **`exists_transport`** (`thm:sm-transport`), and its instances `exists_nodeBlowup_transport`,
  `exists_smoothBlowup_transport` for the two chart blow-ups of BL1: a strictly semi-stable
  modification `β : C' ⟶ C`, an isomorphism over an open `W ∌ x` whose complement lies in the
  image of the étale preimage of the centre, which over a neighbourhood `U₀ ∋ x` is the base
  change of the chart blow-up.

## Hypotheses

The base `A` is a henselian local domain, integrally closed, with separably closed residue field
(a valuation ring with separably closed fraction field, `Valuation.henselianLocalRing_of_isSepClosed`,
`Valuation.isSepClosed_residueField`). The curve `C` is assumed **separated** over `A`: closedness
of the modification locus in `C` uses it (see the blueprint remark `rem:sm-transport-separated`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Generalities

/-- If `f` is an isomorphism over `V`, it is an isomorphism over every smaller open `V'`. -/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : Y.Opens}
    (h : V' ≤ V) [IsIso (f ∣_ V)] : IsIso (f ∣_ V') := by
  have h1 : IsIso (f ∣_ V ∣_ (V.ι ⁻¹ᵁ V')) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (inferInstanceAs (IsIso (f ∣_ V))) _
  have himage : V.ι ''ᵁ (V.ι ⁻¹ᵁ V') = V' := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr h]
  have e := morphismRestrictRestrict f V (V.ι ⁻¹ᵁ V') ≪≫ morphismRestrictEq f himage
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mp h1

/-- The base change of a morphism which is an isomorphism over `O` is an isomorphism over every
open contained in the preimage of `O`. -/
theorem isIso_pullback_snd_restrict_of_le {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (O : Y.Opens) [IsIso (f ∣_ O)] {V : Y'.Opens} (hV : V ≤ g ⁻¹ᵁ O) :
    IsIso (pullback.snd f g ∣_ V) := by
  have := isIso_pullback_snd_restrict f g O
  exact isIso_morphismRestrict_of_le _ hV

/-- **Strict semi-stability is checked on a cover by open immersions.** -/
theorem IsStrictlySemistable.of_isOpenImmersion_cover {X S : Scheme.{u}} {g : X ⟶ S}
    {D : X.IdealSheafData} {ι : Type*} {Y : ι → Scheme.{u}} (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (h : ∀ i, IsStrictlySemistable (j i ≫ g) (D.comap (j i))) : IsStrictlySemistable g D := by
  refine IsStrictlySemistable.of_openCover fun x ↦ ?_
  obtain ⟨i, hi⟩ := hcov x
  refine ⟨(j i).opensRange, hi, ?_⟩
  have heq : (j i).opensRange.ι ≫ g = (j i).isoOpensRange.inv ≫ j i ≫ g := by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hD : D.comap (j i).opensRange.ι = (D.comap (j i)).comap (j i).isoOpensRange.inv := by
    rw [← Scheme.IdealSheafData.comap_comp, Scheme.Hom.isoOpensRange_inv_comp]
  rw [heq, hD]
  exact (h i).etale_comp _

/-- Strict semi-stability is checked on two open immersions covering the source. -/
theorem IsStrictlySemistable.of_isOpenImmersion_pair {X Y₁ Y₂ S : Scheme.{u}} {g : X ⟶ S}
    {D : X.IdealSheafData} (j₁ : Y₁ ⟶ X) (j₂ : Y₂ ⟶ X) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hcov : ∀ x : X, x ∈ Set.range j₁ ∨ x ∈ Set.range j₂)
    (h₁ : IsStrictlySemistable (j₁ ≫ g) (D.comap j₁))
    (h₂ : IsStrictlySemistable (j₂ ≫ g) (D.comap j₂)) : IsStrictlySemistable g D := by
  let Y : Bool → Scheme.{u} := fun b ↦ if b then Y₁ else Y₂
  let j : ∀ b, Y b ⟶ X := fun b ↦ match b with
    | true => j₁
    | false => j₂
  have : ∀ b, IsOpenImmersion (j b) := fun b ↦ match b with
    | true => inferInstanceAs (IsOpenImmersion j₁)
    | false => inferInstanceAs (IsOpenImmersion j₂)
  refine IsStrictlySemistable.of_isOpenImmersion_cover j (fun x ↦ ?_) fun b ↦ ?_
  · rcases hcov x with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · cases b
    · exact h₂
    · exact h₁

/-- **Strict semi-stability is stable under open immersions of the base.** -/
theorem IsStrictlySemistable.comp_isOpenImmersion {X S T : Scheme.{u}} {g : X ⟶ S}
    {D : X.IdealSheafData} (hs : IsStrictlySemistable g D) (ι : S ⟶ T) [IsOpenImmersion ι] :
    IsStrictlySemistable (g ≫ ι) D := by
  intro x
  obtain ⟨U, hxU, A, _, ι', _, h, hh, hcase⟩ := hs x
  exact ⟨U, hxU, A, inferInstance, ι' ≫ ι, inferInstance, h, by
    rw [← Category.assoc, hh, Category.assoc], hcase⟩

/-- **Étale over normal is reduced.** If `Y` is covered by open immersions of spectra of
integrally closed domains and `p : X ⟶ Y` is étale, then `X` is reduced: the pieces
`X ×_Y Spec B` are étale over `Spec B`, hence normal (`Curves.isNormalScheme_of_etale`). -/
theorem isReduced_of_etale_of_cover {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p]
    (hY : ∀ y : Y, ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B)
      (j : Spec (.of B) ⟶ Y) (_ : IsOpenImmersion j), y ∈ Set.range j) : IsReduced X := by
  choose B _ _ _ j _ hj using hY
  let 𝒰 : X.OpenCover :=
    Scheme.Cover.mkOfCovers X (fun x ↦ pullback p (j (p x))) (fun x ↦ pullback.fst p (j (p x)))
      (fun x ↦ by
        obtain ⟨b, hb⟩ := hj (p x)
        obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x b hb.symm
        exact ⟨x, z, hz⟩)
      (fun x ↦ inferInstanceAs (IsOpenImmersion (pullback.fst p (j (p x)))))
  have : ∀ x, IsReduced (𝒰.X x) := by
    intro x
    have hn : IsNormalScheme (pullback p (j (p x))) :=
      isNormalScheme_of_etale (B (p x)) (pullback.snd p (j (p x)))
    have : ∀ z, _root_.IsReduced ((𝒰.X x).presheaf.stalk z) := fun z ↦ by
      have : IsDomain ((𝒰.X x).presheaf.stalk z) := (hn z).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  exact IsReduced.of_openCover X 𝒰

end Generalities

section Extension

variable {C M M' : Scheme.{u}} {U : C.Opens} (φ : U.toScheme ⟶ M) (β₀ : M' ⟶ M) (W : C.Opens)
  [IsIso (pullback.snd β₀ φ ∣_ (U.ι ⁻¹ᵁ W))]

/-- The extension of the pulled-back blow-up is proper. -/
theorem isProper_transport [IsProper β₀] (hUW : U ⊔ W = ⊤) :
    IsProper (extensionHom W (pullback.snd β₀ φ)) :=
  isProper_extensionHom W _ hUW

/-- **The extension of the pulled-back blow-up is a modification**, for integral `C`, a
modification `β₀`, a flat `φ` and a reduced fibre product (`isReduced_of_etale_of_cover`). -/
theorem isModification_transport [IsIntegral C] [IsModification β₀] [Flat φ]
    [IsReduced (pullback β₀ φ)] (hUW : U ⊔ W = ⊤) (hU : (U : Set C).Nonempty)
    (hW : (W : Set C).Nonempty) : IsModification (extensionHom W (pullback.snd β₀ φ)) := by
  have : Nonempty U.toScheme := hU.to_subtype
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hβ := isModification_pullback_snd β₀ φ
  have : IsIntegral (pullback β₀ φ) := hβ.sourceIntegral
  exact isModification_extensionHom W _ hUW hW

/-- The extension of the pulled-back blow-up is covered by the two charts. -/
theorem transport_cover (y : extension W (pullback.snd β₀ φ)) :
    y ∈ Set.range (extensionι₁ W (pullback.snd β₀ φ)) ∨
      y ∈ Set.range (extensionι₂ W (pullback.snd β₀ φ)) := by
  rcases extension_jointly_surjective W _ y with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

/-- **Strict semi-stability of the transported blow-up, with marks.** Let `g : C ⟶ S` and
`q : M ⟶ S` with `φ` étale over `S`. If `(M', D₀)` and `(C, D)` are strictly semi-stable over
`S` and the marks `D'` of the extension restrict to `D₀` on the first chart (pulled back along the
étale projection to `M'`) and to `D` on `W`, then `(extension, D')` is strictly semi-stable. -/
theorem isStrictlySemistable_transport {S : Scheme.{u}} (g : C ⟶ S) (q : M ⟶ S) [Etale φ]
    (hφ : φ ≫ q = U.ι ≫ g) {D : C.IdealSheafData} {D₀ : M'.IdealSheafData}
    (D' : (extension W (pullback.snd β₀ φ)).IdealSheafData)
    (hD₁ : D'.comap (extensionι₁ W (pullback.snd β₀ φ)) = D₀.comap (pullback.fst β₀ φ))
    (hD₂ : D'.comap (extensionι₂ W (pullback.snd β₀ φ)) = D.comap W.ι)
    (hM' : IsStrictlySemistable (β₀ ≫ q) D₀) (hC : IsStrictlySemistable g D) :
    IsStrictlySemistable (extensionHom W (pullback.snd β₀ φ) ≫ g) D' := by
  refine IsStrictlySemistable.of_isOpenImmersion_pair (extensionι₁ W (pullback.snd β₀ φ))
    (extensionι₂ W (pullback.snd β₀ φ)) (transport_cover φ β₀ W) ?_ ?_
  · rw [← Category.assoc, extensionι₁_extensionHom, Category.assoc, ← hφ,
      ← Category.assoc, ← pullback.condition, Category.assoc, hD₁]
    exact hM'.etale_comp (pullback.fst β₀ φ)
  · rw [← Category.assoc, extensionι₂_extensionHom, hD₂]
    exact hC.etale_comp W.ι

/-- **Strict semi-stability of the transported blow-up, without marks.** -/
theorem isStrictlySemistable_transport_top {S : Scheme.{u}} (g : C ⟶ S) (q : M ⟶ S) [Etale φ]
    (hφ : φ ≫ q = U.ι ≫ g) (hM' : IsStrictlySemistable (β₀ ≫ q) ⊤)
    (hC : IsStrictlySemistable g ⊤) :
    IsStrictlySemistable (extensionHom W (pullback.snd β₀ φ) ≫ g) ⊤ :=
  isStrictlySemistable_transport φ β₀ W g q hφ ⊤ (by rw [Scheme.IdealSheafData.comap_top,
    Scheme.IdealSheafData.comap_top]) (by rw [Scheme.IdealSheafData.comap_top,
    Scheme.IdealSheafData.comap_top]) hM' hC

end Extension

section Existence

variable {A : Type u} [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
  {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g] (U : C.Opens) {M : Scheme.{u}}
  (q : M ⟶ Spec (.of A)) (φ : U.toScheme ⟶ M) [Etale φ] (hφ : φ ≫ q = U.ι ≫ g)
  {Ā : Type u} [CommRing Ā] [Algebra A Ā] (hĀ : Function.Surjective (algebraMap A Ā))
  (i : Spec (.of Ā) ⟶ M) [IsClosedImmersion i]
  (hi : i ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A Ā)))

include hφ hĀ hi in
/-- **The opens of the transport step.** In the situation of `exists_open_isClosed_locus`, let
`O ⊆ M` be the complement of the centre `i(Spec Ā)`. There are an open `x ∈ U₀ ⊆ U` and an open
`W ∌ x` of `C` with `U₀ ∪ W = C`, such that `U₀ ∩ W` maps into `O` (so a blow-up of `M` which is
an isomorphism over `O` pulls back to an isomorphism over `U₀ ∩ W`), the complement of `W`
lies in the image of `φ⁻¹(i(Spec Ā))`, and `x` is its only point on the closed fibre. -/
theorem exists_transport_opens (O : M.Opens) (hO : (O : Set M) = (Set.range i)ᶜ)
    (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A) (hxi : φ ⟨x, hxU⟩ ∈ Set.range i) :
    ∃ (U₀ : C.Opens) (hU₀ : U₀ ≤ U) (W : C.Opens), x ∈ U₀ ∧ x ∉ W ∧ U₀ ⊔ W = ⊤ ∧
      U₀.ι ⁻¹ᵁ W ≤ (C.homOfLE hU₀ ≫ φ) ⁻¹ᵁ O ∧ (W : Set C)ᶜ ⊆ U.ι '' (φ ⁻¹' Set.range i) ∧
      ∀ y ∉ W, g y = closedPoint A → y = x := by
  obtain ⟨U₀, hU₀, hxU₀, hcl, huniq⟩ :=
    exists_open_isClosed_locus g U q φ hφ hĀ i hi x hxU hx hxi
  let W : C.Opens := ⟨_, hcl.isOpen_compl⟩
  have hxZ : x ∈ (U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i) := ⟨hxU₀, ⟨x, hxU⟩, hxi, rfl⟩
  have hhom : ∀ y : U₀.toScheme, U.ι (C.homOfLE hU₀ y) = U₀.ι y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  refine ⟨U₀, hU₀, W, hxU₀, fun h ↦ h hxZ, ?_, ?_, ?_, fun y hy ↦ huniq y (by
    by_contra h
    exact hy h)⟩
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    by_cases hy : y ∈ (U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i)
    · exact Or.inl hy.1
    · exact Or.inr hy
  · intro y hy
    change φ (C.homOfLE hU₀ y) ∈ (O : Set M)
    rw [hO]
    intro hφy
    apply hy
    refine ⟨y.2, C.homOfLE hU₀ y, hφy, hhom y⟩
  · intro y hy
    have hy' : y ∈ (U₀ : Set C) ∩ U.ι '' (φ ⁻¹' Set.range i) := by
      by_contra h
      exact hy h
    exact hy'.2

include hφ hĀ hi in
/-- **Transport of a chart blow-up** (`thm:sm-transport`; Temkin, proof of Prop 4.3.1,
T:2970–2983, with the fix of `ERRATA.md` DJA-T33). Let `A` be a henselian local ring with
separably closed residue field, `g : C ⟶ Spec A` separated, `φ : U ⟶ M` an étale `A`-morphism
from an open of `C`, `i : Spec Ā ⟶ M` a closed immersion over the closed subscheme
`Spec Ā ⊆ Spec A`, and `β₀ : M' ⟶ M` proper with `(M', ∅)` strictly semi-stable over `A` and
`β₀` an isomorphism off `i(Spec Ā)`. For every point `x ∈ U` of the closed fibre with
`φ x ∈ i(Spec Ā)` there are an open `x ∈ U₀ ⊆ U`, an open `W ∌ x` of `C` whose complement lies in
the image of `φ⁻¹(i(Spec Ā))`, and a proper `β : C' ⟶ C` such that

* `β` is an isomorphism over `W`, via an open immersion `k : W ⟶ C'`, and `x` is the only
  point of the closed fibre outside `W`;
* over `U₀`, `β` is the base change of `β₀` along `φ|_{U₀}`, via an open immersion `j`;
* `C'` is covered by the images of `j` and `k`;
* if `(C, ∅)` is strictly semi-stable, so is `(C', ∅)`;
* if `C` is integral, `β₀` is a modification, `M'` is covered by spectra of integrally closed
  domains and some point of `C` lies off the preimage of `Spec Ā`, then `β` is a modification. -/
theorem exists_transport {M' : Scheme.{u}} (β₀ : M' ⟶ M) [IsProper β₀] (O : M.Opens)
    (hO : (O : Set M) = (Set.range i)ᶜ) [IsIso (β₀ ∣_ O)]
    (hM' : IsStrictlySemistable (β₀ ≫ q) ⊤)
    (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A) (hxi : φ ⟨x, hxU⟩ ∈ Set.range i) :
    ∃ (U₀ : C.Opens) (hU₀ : U₀ ≤ U) (W : C.Opens) (C' : Scheme.{u}) (β : C' ⟶ C)
      (j : pullback β₀ (C.homOfLE hU₀ ≫ φ) ⟶ C') (k : W.toScheme ⟶ C'),
      x ∈ U₀ ∧ x ∉ W ∧ (W : Set C)ᶜ ⊆ U.ι '' (φ ⁻¹' Set.range i) ∧
      (∀ y ∉ W, g y = closedPoint A → y = x) ∧ IsOpenImmersion j ∧ IsOpenImmersion k ∧
      j ≫ β = pullback.snd β₀ (C.homOfLE hU₀ ≫ φ) ≫ U₀.ι ∧ k ≫ β = W.ι ∧
      (∀ y : C', y ∈ Set.range j ∨ y ∈ Set.range k) ∧ IsProper β ∧ IsIso (β ∣_ W) ∧
      (IsStrictlySemistable g ⊤ → IsStrictlySemistable (β ≫ g) ⊤) ∧
      (IsIntegral C → IsModification β₀ →
        (∀ m : M', ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B)
          (j : Spec (.of B) ⟶ M') (_ : IsOpenImmersion j), m ∈ Set.range j) →
        (∃ y : C, g y ∉ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A Ā)))) →
        IsModification β) := by
  obtain ⟨U₀, hU₀, W, hxU₀, hxW, hUW, hWO, hWc, huniq⟩ :=
    exists_transport_opens g U q φ hφ hĀ i hi O hO x hxU hx hxi
  let φ₀ : U₀.toScheme ⟶ M := C.homOfLE hU₀ ≫ φ
  have hφ₀ : φ₀ ≫ q = U₀.ι ≫ g := by
    rw [Category.assoc, hφ, ← Category.assoc, Scheme.homOfLE_ι]
  have : IsIso (pullback.snd β₀ φ₀ ∣_ (U₀.ι ⁻¹ᵁ W)) :=
    isIso_pullback_snd_restrict_of_le β₀ φ₀ O hWO
  refine ⟨U₀, hU₀, W, extension W (pullback.snd β₀ φ₀), extensionHom W (pullback.snd β₀ φ₀),
    extensionι₁ W _, extensionι₂ W _, hxU₀, hxW, hWc, huniq, inferInstance, inferInstance,
    extensionι₁_extensionHom W _, extensionι₂_extensionHom W _, transport_cover φ₀ β₀ W,
    isProper_transport φ₀ β₀ W hUW, inferInstance,
    fun hC ↦ isStrictlySemistable_transport_top φ₀ β₀ W g q hφ₀ hM' hC, ?_⟩
  intro hCint hβ₀ hcov hy
  have : IsReduced (pullback β₀ φ₀) := isReduced_of_etale_of_cover (pullback.fst β₀ φ₀) hcov
  obtain ⟨y, hy⟩ := hy
  have hyW : y ∈ W := by
    by_contra hyW
    obtain ⟨y', ⟨a, ha⟩, rfl⟩ := hWc hyW
    apply hy
    refine ⟨a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hi, Scheme.Hom.comp_apply, ha, ← Scheme.Hom.comp_apply, hφ,
      Scheme.Hom.comp_apply]
  exact isModification_transport φ₀ β₀ W hUW ⟨x, hxU₀⟩ ⟨y, hyW⟩

end Existence

section Charts

variable {A : Type u} [CommRing A] [IsDomain A]

open Algebra.NodeBlowupChart NodeBlowupCover

/-- The node chart blow-up is covered by spectra of integrally closed domains (its two charts are
node models with nonzero parameters). -/
theorem nodeBlowup_cover [IsIntegrallyClosed A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]
    (m : affineBlowup (centerIdeal π b)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B)
      (j : Spec (.of B) ⟶ affineBlowup (centerIdeal π b)) (_ : IsOpenImmersion j),
      m ∈ Set.range j := by
  have hm : m ∈ (uChartInclusion π b).opensRange ⊔ (tChartInclusion π b).opensRange := by
    rw [chartInclusions_sup_opensRange]
    trivial
  rcases hm with hm | hm
  · exact ⟨Node A π, inferInstance, Algebra.NodeDomain.nodeQuotient_isDomain π Fact.out,
      Algebra.NodeNormal.node_isIntegrallyClosed π Fact.out, _, inferInstance, hm⟩
  · exact ⟨Node A b, inferInstance, Algebra.NodeDomain.nodeQuotient_isDomain b Fact.out,
      Algebra.NodeNormal.node_isIntegrallyClosed b Fact.out, _, inferInstance, hm⟩

/-- The smooth chart blow-up is covered by spectra of integrally closed domains (`A[S]` and a node
model with nonzero parameter). -/
theorem smoothBlowup_cover [IsIntegrallyClosed A] (π a : A) [Fact (π ≠ 0)]
    (m : affineBlowup (smoothCenter π a)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B)
      (j : Spec (.of B) ⟶ affineBlowup (smoothCenter π a)) (_ : IsOpenImmersion j),
      m ∈ Set.range j := by
  have hm : m ∈ (smoothParamChartInclusion π a).opensRange ⊔
      (smoothCoordChartInclusion π a).opensRange := by
    rw [smoothChartInclusions_sup_opensRange]
    trivial
  rcases hm with hm | hm
  · exact ⟨A[X], inferInstance, inferInstance, inferInstance, _, inferInstance, hm⟩
  · exact ⟨Node A π, inferInstance, Algebra.NodeDomain.nodeQuotient_isDomain π Fact.out,
      Algebra.NodeNormal.node_isIntegrallyClosed π Fact.out, _, inferInstance, hm⟩

omit [IsDomain A] in
/-- The node locus `V(u, v, π)` lies over `Spec A/(π)`. -/
theorem nodeLocus_comp_nodeModel (π b : A) :
    nodeLocus π b ≫ nodeModel (π * b) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Node A (π * b) ⧸ nodeLocusIdeal π b))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

omit [IsDomain A] in
/-- The smooth locus `V(π, T - a)` lies over `Spec A/(π)`. -/
theorem smoothLocus_comp_smoothModel (π a : A) :
    smoothLocus π a ≫ smoothModel A =
      Spec.map (CommRingCat.ofHom (algebraMap A (A[X] ⧸ smoothCenter π a))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- If `π ≠ 0` vanishes on `Ā` and `C` is flat over the domain `A`, some point of `C` lies off the
preimage of `Spec Ā`: generize any point to the generic fibre. -/
theorem exists_not_mem_range_of_flat {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [Flat g]
    [Nonempty C] {Ā : Type u} [CommRing Ā] [Algebra A Ā] {π : A} (hπ : π ≠ 0)
    (hπĀ : algebraMap A Ā π = 0) :
    ∃ y : C, g y ∉ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A Ā))) := by
  obtain ⟨y₀⟩ := ‹Nonempty C›
  have hgen : (⊥ : PrimeSpectrum A) ⤳ g y₀ := by
    rw [← PrimeSpectrum.le_iff_specializes]
    exact bot_le
  obtain ⟨y, -, hy⟩ := Flat.generalizingMap g hgen
  refine ⟨y, ?_⟩
  rintro ⟨a, ha⟩
  have hmem : π ∈ (g y).asIdeal := by
    rw [← ha]
    change π ∈ Ideal.comap (algebraMap A Ā) a.asIdeal
    rw [Ideal.mem_comap, hπĀ]
    exact a.asIdeal.zero_mem
  rw [hy] at hmem
  exact hπ hmem

end Charts

section ChartTransport

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [HenselianLocalRing A]
  [IsSepClosed (ResidueField A)]

open Algebra.NodeBlowupChart

/-- **Transport of the node chart blow-up** (`thm:sm-transport`, node case; Temkin, proof of
Prop 4.3.1, stage 1, T:2976–2990, and of Lemma 4.3.2, T:3036–3046). Let `A` be a henselian,
integrally closed local domain with separably closed residue field (e.g. a valuation ring with
separably closed fraction field), `(C, ∅)` strictly semi-stable and separated over `A`, and
`φ : U ⟶ Spec A[u,v]/(uv - πb)` étale over `A` from an open of `C`, with `π, b ≠ 0`. For every
point `x ∈ U` of the closed fibre with `φ x ∈ V(u, v, π)` there is a strictly semi-stable
modification `β : C' ⟶ C` (if `C` is integral) which is an isomorphism over an open `W ∌ x`
whose complement lies in the image of `φ⁻¹V(u, v, π)`, and which over a neighbourhood
`x ∈ U₀ ⊆ U` is the base change of `Bl_{(u,π)}` along `φ`. -/
theorem exists_nodeBlowup_transport (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g] (hC : IsStrictlySemistable g ⊤)
    (U : C.Opens) (φ : U.toScheme ⟶ Spec (.of (Node A (π * b)))) [Etale φ]
    (hφ : φ ≫ nodeModel (π * b) = U.ι ≫ g) (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A)
    (hxi : φ ⟨x, hxU⟩ ∈ Set.range (nodeLocus π b)) :
    ∃ (U₀ : C.Opens) (hU₀ : U₀ ≤ U) (W : C.Opens) (C' : Scheme.{u}) (β : C' ⟶ C)
      (j : pullback (affineBlowupStructure (centerIdeal π b)) (C.homOfLE hU₀ ≫ φ) ⟶ C')
      (k : W.toScheme ⟶ C'),
      x ∈ U₀ ∧ x ∉ W ∧ (W : Set C)ᶜ ⊆ U.ι '' (φ ⁻¹' Set.range (nodeLocus π b)) ∧
      (∀ y ∉ W, g y = closedPoint A → y = x) ∧ IsOpenImmersion j ∧ IsOpenImmersion k ∧
      j ≫ β = pullback.snd (affineBlowupStructure (centerIdeal π b)) (C.homOfLE hU₀ ≫ φ) ≫
        U₀.ι ∧ k ≫ β = W.ι ∧
      (∀ y : C', y ∈ Set.range j ∨ y ∈ Set.range k) ∧ IsProper β ∧ IsIso (β ∣_ W) ∧
      IsStrictlySemistable (β ≫ g) ⊤ ∧ (IsIntegral C → IsModification β) := by
  have : IsProper (affineBlowupStructure (centerIdeal π b)) :=
    affineBlowupStructure_isProper _ (centerIdeal_fg π b)
  have : IsIso (affineBlowupStructure (centerIdeal π b) ∣_ nodeLocusComplement π b) :=
    nodeBlowup_isIso π b
  have hO : ((nodeLocusComplement π b : (Spec (.of (Node A (π * b)))).Opens) :
      Set (Spec (.of (Node A (π * b))))) = (Set.range (nodeLocus π b))ᶜ := by
    rw [range_nodeLocus, compl_compl]
  obtain ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
      hss, hmod⟩ :=
    exists_transport g U (nodeModel (π * b)) φ hφ (algebraMap_nodeLocus_surjective π b)
      (nodeLocus π b) (nodeLocus_comp_nodeModel π b) (affineBlowupStructure (centerIdeal π b))
      (nodeLocusComplement π b) hO (nodeBlowup_isStrictlySemistable π b) x hxU hx hxi
  refine ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
    hss hC,
    fun hCint ↦ hmod hCint (nodeBlowup_isModification π b) (nodeBlowup_cover π b) ?_⟩
  have : DeJong.IsNodalCurve g := hC.isNodalCurve
  have : Nonempty C := ⟨x⟩
  refine exists_not_mem_range_of_flat g (Fact.out : π ≠ 0) ?_
  rw [IsScalarTower.algebraMap_apply A (Node A (π * b)), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

/-- **Transport of the smooth chart blow-up** (`thm:sm-transport`, smooth case; Temkin, proof
of Prop 4.3.1, stage 2, T:2992–3016, and the separation step of Lemma 4.3.2, T:3027–3030).
Same as `exists_nodeBlowup_transport` for an étale `φ : U ⟶ Spec A[T]` and the blow-up of
`(π, T - a)`, `π ≠ 0`, at a point `x` of the closed fibre with `φ x ∈ V(π, T - a)`. -/
theorem exists_smoothBlowup_transport (π a : A) [Fact (π ≠ 0)]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of A)) [IsSeparated g] (hC : IsStrictlySemistable g ⊤)
    (U : C.Opens) (φ : U.toScheme ⟶ Spec (.of A[X])) [Etale φ]
    (hφ : φ ≫ smoothModel A = U.ι ≫ g) (x : C) (hxU : x ∈ U) (hx : g x = closedPoint A)
    (hxi : φ ⟨x, hxU⟩ ∈ Set.range (smoothLocus π a)) :
    ∃ (U₀ : C.Opens) (hU₀ : U₀ ≤ U) (W : C.Opens) (C' : Scheme.{u}) (β : C' ⟶ C)
      (j : pullback (affineBlowupStructure (smoothCenter π a)) (C.homOfLE hU₀ ≫ φ) ⟶ C')
      (k : W.toScheme ⟶ C'),
      x ∈ U₀ ∧ x ∉ W ∧ (W : Set C)ᶜ ⊆ U.ι '' (φ ⁻¹' Set.range (smoothLocus π a)) ∧
      (∀ y ∉ W, g y = closedPoint A → y = x) ∧ IsOpenImmersion j ∧ IsOpenImmersion k ∧
      j ≫ β = pullback.snd (affineBlowupStructure (smoothCenter π a)) (C.homOfLE hU₀ ≫ φ) ≫
        U₀.ι ∧ k ≫ β = W.ι ∧
      (∀ y : C', y ∈ Set.range j ∨ y ∈ Set.range k) ∧ IsProper β ∧ IsIso (β ∣_ W) ∧
      IsStrictlySemistable (β ≫ g) ⊤ ∧ (IsIntegral C → IsModification β) := by
  have : IsProper (affineBlowupStructure (smoothCenter π a)) :=
    affineBlowupStructure_isProper _ (smoothCenter_fg π a)
  have : IsIso (affineBlowupStructure (smoothCenter π a) ∣_
      affineBlowupCenterComplement (smoothCenter π a)) := smoothBlowup_isIso π a
  have hO : ((affineBlowupCenterComplement (smoothCenter π a) : (Spec (.of A[X])).Opens) :
      Set (Spec (.of A[X]))) = (Set.range (smoothLocus π a))ᶜ := by
    rw [range_smoothLocus, compl_compl]
  obtain ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
      hss, hmod⟩ :=
    exists_transport g U (smoothModel A) φ hφ (algebraMap_smoothLocus_surjective π a)
      (smoothLocus π a) (smoothLocus_comp_smoothModel π a)
      (affineBlowupStructure (smoothCenter π a)) (affineBlowupCenterComplement (smoothCenter π a))
      hO (smoothBlowup_isStrictlySemistable π a) x hxU hx hxi
  refine ⟨U₀, hU₀, W, C', β, j, k, hxU₀, hxW, hWc, huniq, hj, hk, hjβ, hkβ, hcov, hprop, hiso,
    hss hC,
    fun hCint ↦ hmod hCint (smoothBlowup_isModification π a) (smoothBlowup_cover π a) ?_⟩
  have : DeJong.IsNodalCurve g := hC.isNodalCurve
  have : Nonempty C := ⟨x⟩
  refine exists_not_mem_range_of_flat g (Fact.out : π ≠ 0) ?_
  rw [IsScalarTower.algebraMap_apply A A[X], Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact C_mem_smoothCenter π a

end ChartTransport

end DeJongAlterations.StableModification.Blowups

/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.Valuation
import DeJongAlterations.StableModification.Cohomology.PullbackQcoh
import DeJongAlterations.StableModification.CurvesField.GenusNormalization
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.StableModification.Cohomology.SteinFinite

/-!
# Constancy of the arithmetic genus of the fibres (Temkin, proof of Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (`stabcritlem`, T:3125–3131): "the Euler–Poincaré characteristic of the fibers is
constant on `S` … Hence `h¹(C′_s) = h¹(C_η) = h¹(C_s)`". This file proves this step in the form
used by Corollary B.2 (`CurvesField.Genus.stabdown_*`), with the arithmetic genus
`p_a = 1 − χ(𝒪)` of `CurvesField.Genus.arithmeticGenus` (so that, unlike Temkin's `h¹`, no
connectedness of the fibres is needed; ERRATA T50).

## Main results

* `eulerChar_baseChange_eq_sum`: for a finite affine open cover `U` of `X → Spec A` and a field
  point `φ : A → κ`, the Euler characteristic of the fibre `X_κ = X ×_A κ`
  (`CurvesField.Genus.eulerChar`, computed with a chosen cover) is the alternating sum of the
  dimensions of the Čech cohomology of `q^* 𝒪_X` for the preimage cover (lane COH3A's form).
* `eulerChar_fibre_eq` (blueprint `lem:sm-bd-euler-fibres`): **if `X` is projective over a
  valuation ring `V` (projective coordinates with coefficients the structure map) and flat on the
  charts, then `χ(X_κ, 𝒪)` does not depend on the field point `V → κ`** (lane COH3A's
  `exists_eulerChar_fibre_valuation` for `F = 𝒪_X`).
* `eulerChar_eq_of_iso`: `χ` is invariant under isomorphisms of schemes over a field.
* `eulerChar_fibre_eq_of_isIso` and `arithmeticGenus_fibre_eq_of_isEtaModification`
  (blueprint `lem:sm-bd-genus-modification`): **for a morphism `f : X′ → X` of projective flat
  `V`-schemes which is an isomorphism on the generic fibres, `p_a(X′_κ) = p_a(X_κ)` for every
  field point**; in particular `p_a(C′_s) = p_a(C_s)` at the closed point, the genus hypothesis of
  Temkin's Corollary B.2 in the proof of Lemma 4.4.2.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.BlowDown

open Cohomology CurvesField.Genus

universe u

section Instances

variable {X : Scheme.{u}} {A : Type u} [CommRing A] (p : X ⟶ Spec (CommRingCat.of A))
  {B : Type u} [CommRing B] (φ : A →+* B)

/-- The base change of a quasi-compact scheme to an affine scheme is quasi-compact. -/
instance compactSpace_baseChange [CompactSpace X] :
    CompactSpace (pullback (C := Scheme.{u}) p (Spec.map (CommRingCat.ofHom φ))) :=
  CurvesField.Genus.compactSpace_of_isAffineHom (bcFst φ p)

/-- The base change of a scheme with affine diagonal to an affine scheme has affine diagonal. -/
instance isAffineHom_diagonal_baseChange
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    IsAffineHom (pullback.diagonal
      (terminal.from (pullback (C := Scheme.{u}) p (Spec.map (CommRingCat.ofHom φ))))) :=
  CurvesField.Genus.isAffineHom_diagonal_of_isAffineHom (bcFst φ p)

omit p in
/-- A scheme quasi-compact over an affine scheme is quasi-compact. -/
theorem compactSpace_of_quasiCompact (q : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact q] :
    CompactSpace X :=
  ⟨by simpa using QuasiCompact.isCompact_preimage (f := q) Set.univ isOpen_univ isCompact_univ⟩

omit p in
/-- A scheme separated over an affine scheme has affine diagonal (over `Spec ℤ`). -/
theorem isAffineHom_diagonal_of_isSeparated (q : X ⟶ Spec (CommRingCat.of A)) [IsSeparated q] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  have e : q ≫ terminal.from _ = terminal.from X := terminal.hom_ext _ _
  have : IsSeparated (terminal.from X) := by rw [← e]; infer_instance
  infer_instance

end Instances

section EulerChar

variable {X : Scheme.{u}} [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
  {κ : Type u} [Field κ] (c : κ →+* Γ(X, ⊤))

/-- `χ(X, 𝒪_X)` is the alternating sum of the dimensions of the cohomology of any complex of
`κ`-modules whose cohomology is that of `𝒪_X`, in degrees `< N` beyond which it vanishes. -/
theorem eulerChar_eq_sum_of_iso (N : ℕ)
    (M : ℕ → ModuleCat.{u} κ) (e : ∀ i, cohomology (SheafOfModules.unit X.ringCatSheaf) c i ≅ M i)
    (hN : ∀ i, N ≤ i → Subsingleton (M i)) :
    eulerChar X c = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (Module.finrank κ (M i) : ℤ) := by
  unfold eulerChar
  rw [homologyEulerChar_eq_sum _ N fun i hi => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    exact (e i).toLinearEquiv.finrank_eq
  · have := hN i hi
    exact (e i).toLinearEquiv.toEquiv.subsingleton

end EulerChar

section BaseChange

variable {X : Scheme.{u}} {A : Type u} [CommRing A] (p : X ⟶ Spec (CommRingCat.of A))
  [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
  {κ : Type u} [Field κ] (φ : A →+* κ)

/-- **`χ` of a fibre through the preimage of an affine cover** (bridge to lane COH3A): for a
finite family `U` of affine opens covering `X` and a field point `φ : A → κ`, the Euler
characteristic of `X_κ = X ×_A κ` is `∑_{i < N} (-1)^i dim Ȟⁱ(q⁻¹U, q^* 𝒪_X)` for every
`N ≥ #U`. -/
theorem eulerChar_baseChange_eq_sum {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i)) (N : ℕ) (hN : Fintype.card ι ≤ N) :
    eulerChar (pullback p (Spec.map (CommRingCat.ofHom φ))) (structureCoeff (bcSnd φ p)) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (Module.finrank κ
        (cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj
          (SheafOfModules.unit X.ringCatSheaf)) (fun j => bcFst φ p ⁻¹ᵁ U j)
          (structureCoeff (bcSnd φ p)) i) : ℤ) := by
  set Xκ := pullback p (Spec.map (CommRingCat.ofHom φ))
  let U' : ι → Xκ.Opens := fun j => bcFst φ p ⁻¹ᵁ U j
  have hU' : ⨆ j, U' j = ⊤ := by
    simp only [U']
    rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  have hU'a : ∀ j, IsAffineOpen (U' j) := fun j => (hUa j).preimage _
  -- `q^* 𝒪_X ≅ 𝒪_{X_κ}` on Čech cohomology
  let f : ∀ i, cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj
      (SheafOfModules.unit X.ringCatSheaf)) U' (structureCoeff (bcSnd φ p)) i ≅
      cechCohomology (SheafOfModules.unit Xκ.ringCatSheaf) U' (structureCoeff (bcSnd φ p)) i :=
    fun i => (HomologicalComplex.homologyFunctor _ _ i).mapIso
      ((cechComplexFunctor U' (structureCoeff (bcSnd φ p))).mapIso (pullbackUnitIso (bcFst φ p)))
  let e : ∀ i, cohomology (SheafOfModules.unit Xκ.ringCatSheaf) (structureCoeff (bcSnd φ p)) i ≅
      cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj
        (SheafOfModules.unit X.ringCatSheaf)) U' (structureCoeff (bcSnd φ p)) i :=
    fun i => cechCohomologyIsoOfAffineCovers (SheafOfModules.unit Xκ.ringCatSheaf)
      (structureCoeff (bcSnd φ p)) (FiniteAffineCover.choose Xκ).iSup_eq_top hU'
      (FiniteAffineCover.choose Xκ).isAffineOpen hU'a i ≪≫ (f i).symm
  refine eulerChar_eq_sum_of_iso _ N _ e fun i hi => ?_
  have hz := isZero_cechCohomology_of_card_le (SheafOfModules.unit Xκ.ringCatSheaf) U'
    (structureCoeff (bcSnd φ p)) i (hN.trans hi)
  exact (ModuleCat.subsingleton_of_isZero (hz.of_iso (f i)))

end BaseChange

section Valuation

variable {X : Scheme.{u}} {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {p : X ⟶ Spec (CommRingCat.of V)}
  [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **Constancy of `χ(𝒪)` on the fibres of a projective flat scheme over a valuation ring**
(blueprint `lem:sm-bd-euler-fibres`; Temkin T:3125–3129, EGA III 7.9.4 without Noetherian
approximation): if `X → Spec V` has projective coordinates with coefficients the structure map
and `𝒪_X` is `V`-flat on the charts (e.g. `X` flat over `V`), then `χ(X_κ, 𝒪)` is the same for
all field points `V → κ`. -/
theorem eulerChar_fibre_eq (D : ProjectiveCoordinates X V (structureCoeff p))
    (hflat : ∀ i, Module.Flat V (sectionsModuleCat (SheafOfModules.unit X.ringCatSheaf)
      (structureCoeff p) (D.U i) le_top))
    {κ κ' : Type u} [Field κ] [Field κ'] (φ : V →+* κ) (φ' : V →+* κ') :
    eulerChar (pullback p (Spec.map (CommRingCat.ofHom φ))) (structureCoeff (bcSnd φ p)) =
      eulerChar (pullback p (Spec.map (CommRingCat.ofHom φ'))) (structureCoeff (bcSnd φ' p)) := by
  set q := Fintype.card D.ι
  have hvan : ∀ k, q < k → Limits.IsZero (cechCohomology
      (SheafOfModules.unit X.ringCatSheaf) D.U (structureCoeff p) k) :=
    fun k hk => isZero_cechCohomology_of_card_le _ _ _ k hk.le
  obtain ⟨χ, hχ⟩ := D.exists_eulerChar_fibre_valuation (SheafOfModules.unit X.ringCatSheaf)
    (fun _ => Module.Finite.self _) hflat q hvan
  rw [eulerChar_baseChange_eq_sum p φ D.U D.iSup_eq_top D.isAffineOpen (q + 1) (by omega),
    eulerChar_baseChange_eq_sum p φ' D.U D.iSup_eq_top D.isAffineOpen (q + 1) (by omega),
    hχ κ φ, hχ κ' φ']

end Valuation

section Iso

variable {X Y : Scheme.{u}} [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
  [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
  {κ : Type u} [Field κ]

omit [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))] [CompactSpace Y]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] in
/-- On Čech complexes, `𝒪_Y → e_* 𝒪_X` is an isomorphism for an isomorphism `e : X ≅ Y`. -/
theorem isIso_cechComplexMap_structureMap (e : X ≅ Y) (c : κ →+* Γ(Y, ⊤)) {ι : Type u}
    [LinearOrder ι] (U : ι → Y.Opens) :
    IsIso (cechComplexMap U c (CurvesField.Genus.structureMap e.hom)) := by
  have hbij : ∀ W : Y.Opens, Function.Bijective (e.hom.app W).hom := fun W =>
    ConcreteCategory.bijective_of_isIso (e.hom.app W)
  suffices h : ∀ n, IsIso ((cechComplexMap U c (CurvesField.Genus.structureMap e.hom)).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext T
    have h := congrArg (fun z => z.val T) hxy
    exact (hbij (T.inf U)).1 h
  · intro y
    classical
    let x : (T : Finset ι) → _ := fun T => (hbij (T.inf U)).2 (y.val T) |>.choose
    have hx : ∀ T, (e.hom.app (T.inf U)).hom (x T) = y.val T := fun T =>
      ((hbij (T.inf U)).2 (y.val T)).choose_spec
    refine ⟨⟨x, fun T hT => ?_⟩, ?_⟩
    · apply (hbij (T.inf U)).1
      rw [hx]
      refine (y.2 T hT).trans ?_
      exact (map_zero (e.hom.app (T.inf U)).hom).symm
    · apply Subtype.ext
      funext T
      exact hx T

/-- **The Euler characteristic is invariant under isomorphisms over a field.** -/
theorem eulerChar_eq_of_iso (qX : X ⟶ Spec (CommRingCat.of κ)) (qY : Y ⟶ Spec (CommRingCat.of κ))
    (e : X ≅ Y) (he : e.hom ≫ qY = qX) :
    eulerChar X (structureCoeff qX) = eulerChar Y (structureCoeff qY) := by
  set 𝒱 := FiniteAffineCover.choose Y
  have : Fintype 𝒱.ι := Fintype.ofFinite _
  have hc : e.hom.appTop.hom.comp (structureCoeff qY) = structureCoeff qX := by
    rw [← he]
    ext a
    simp only [structureCoeff, Scheme.Hom.comp_appTop, RingHom.comp_apply]
    rfl
  -- the Čech complex of `𝒪_X` for `e⁻¹ 𝒱` is that of `𝒪_Y` for `𝒱`
  have := isIso_cechComplexMap_structureMap e (structureCoeff qY) 𝒱.U
  let E : cechComplex (SheafOfModules.unit Y.ringCatSheaf) 𝒱.U (structureCoeff qY) ≅
      cechComplex (SheafOfModules.unit X.ringCatSheaf) (fun i => e.hom ⁻¹ᵁ 𝒱.U i)
        (e.hom.appTop.hom.comp (structureCoeff qY)) :=
    asIso (cechComplexMap 𝒱.U (structureCoeff qY) (CurvesField.Genus.structureMap e.hom)) ≪≫
      cechComplexPushforwardIso e.hom (SheafOfModules.unit X.ringCatSheaf) (structureCoeff qY) 𝒱.U
  let N := Fintype.card 𝒱.ι
  have hX : eulerChar X (structureCoeff qX) = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
      (Module.finrank κ ((cechComplex (SheafOfModules.unit Y.ringCatSheaf) 𝒱.U
        (structureCoeff qY)).homology i) : ℤ) := by
    rw [← hc]
    refine eulerChar_eq_sum_of_iso _ N _ (fun i => cohomologyIsoCech
      (SheafOfModules.unit X.ringCatSheaf) _ (𝒱.comap (π := e.hom)) i ≪≫
        ((HomologicalComplex.homologyFunctor _ _ i).mapIso E).symm) fun i hi => ?_
    exact ModuleCat.subsingleton_of_isZero
      (isZero_cechCohomology_of_card_le _ _ _ i hi)
  have hY : eulerChar Y (structureCoeff qY) = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
      (Module.finrank κ ((cechComplex (SheafOfModules.unit Y.ringCatSheaf) 𝒱.U
        (structureCoeff qY)).homology i) : ℤ) := by
    refine eulerChar_eq_sum_of_iso _ N _ (fun i => cohomologyIsoCech
      (SheafOfModules.unit Y.ringCatSheaf) _ 𝒱 i) fun i hi => ?_
    exact ModuleCat.subsingleton_of_isZero
      (isZero_cechCohomology_of_card_le _ _ _ i hi)
  rw [hX, hY]

end Iso

section Modification

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (f : X' ⟶ X)

section Fibres

variable [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
  [CompactSpace X'] [IsAffineHom (pullback.diagonal (terminal.from X'))]

/-- **Equal Euler characteristics of the fibres of a generic isomorphism** (blueprint
`lem:sm-bd-genus-modification`; Temkin T:3129–3131 "`h¹(C′_s) = h¹(C_η) = h¹(C_s)`"): let
`f : X′ → X` be a morphism of `V`-schemes, both projective and flat on the charts, which is an
isomorphism on the fibres over some field point `ψ : V → L` (e.g. the generic point). Then
`χ(X′_κ, 𝒪) = χ(X_κ, 𝒪)` for every field point `φ : V → κ`. -/
theorem eulerChar_fibre_eq_of_isIso (D : ProjectiveCoordinates X V (structureCoeff p))
    (hflat : ∀ i, Module.Flat V (sectionsModuleCat (SheafOfModules.unit X.ringCatSheaf)
      (structureCoeff p) (D.U i) le_top))
    (D' : ProjectiveCoordinates X' V (structureCoeff (f ≫ p)))
    (hflat' : ∀ i, Module.Flat V (sectionsModuleCat (SheafOfModules.unit X'.ringCatSheaf)
      (structureCoeff (f ≫ p)) (D'.U i) le_top))
    {L : Type u} [Field L] (ψ : V →+* L)
    (hiso : IsIso (Curves.pullbackCompMap f p (Spec.map (CommRingCat.ofHom ψ))))
    {κ : Type u} [Field κ] (φ : V →+* κ) :
    eulerChar (pullback (f ≫ p) (Spec.map (CommRingCat.ofHom φ)))
        (structureCoeff (bcSnd φ (f ≫ p))) =
      eulerChar (pullback p (Spec.map (CommRingCat.ofHom φ))) (structureCoeff (bcSnd φ p)) := by
  rw [eulerChar_fibre_eq D' hflat' φ ψ, eulerChar_fibre_eq D hflat φ ψ]
  exact eulerChar_eq_of_iso _ _ (asIso (Curves.pullbackCompMap f p _))
    (Curves.pullbackCompMap_snd f p _)

end Fibres

omit [IsDomain V] [ValuationRing V] in
/-- The ring map `V → 𝒪_{Spec V, x} → κ(x)` of a point of `Spec V`. -/
abbrev residueFieldPoint (x : Spec (CommRingCat.of V)) :
    V →+* (Spec (CommRingCat.of V)).residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (Spec (CommRingCat.of V)).presheaf.germ ⊤ x trivial ≫
    (Spec (CommRingCat.of V)).residue x).hom

omit [IsDomain V] [ValuationRing V] in
/-- The residue field morphism of `Spec V` at `x` is `Spec` of `residueFieldPoint x`. -/
theorem fromSpecResidueField_eq_specMap (x : Spec (CommRingCat.of V)) :
    (Spec (CommRingCat.of V)).fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom (residueFieldPoint x)) := by
  rw [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp, CommRingCat.ofHom_hom,
    Category.assoc]

variable [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
  [CompactSpace X'] [IsAffineHom (pullback.diagonal (terminal.from X'))]

/-- **Equal arithmetic genera of the fibres of an η-modification** (blueprint
`lem:sm-bd-genus-modification`; the genus count of Temkin's Lemma 4.4.2, T:3125–3131): for an
η-modification `f : X′ → X` (`Curves.IsEtaModification`) of `V`-schemes which are projective and
flat on the charts, `p_a(X′_κ) = p_a(X_κ)` for every field point `φ : V → κ`; at the residue
field of the closed point this is the hypothesis `p_a(C′_s) = p_a(C_s)` of Corollary B.2. -/
theorem arithmeticGenus_fibre_eq_of_isEtaModification (hf : Curves.IsEtaModification f p)
    (D : ProjectiveCoordinates X V (structureCoeff p))
    (hflat : ∀ i, Module.Flat V (sectionsModuleCat (SheafOfModules.unit X.ringCatSheaf)
      (structureCoeff p) (D.U i) le_top))
    (D' : ProjectiveCoordinates X' V (structureCoeff (f ≫ p)))
    (hflat' : ∀ i, Module.Flat V (sectionsModuleCat (SheafOfModules.unit X'.ringCatSheaf)
      (structureCoeff (f ≫ p)) (D'.U i) le_top))
    {κ : Type u} [Field κ] (φ : V →+* κ) :
    arithmeticGenus (pullback (f ≫ p) (Spec.map (CommRingCat.ofHom φ)))
        (structureCoeff (bcSnd φ (f ≫ p))) =
      arithmeticGenus (pullback p (Spec.map (CommRingCat.ofHom φ)))
        (structureCoeff (bcSnd φ p)) := by
  have hiso : IsIso (Curves.pullbackCompMap f p
      ((Spec (CommRingCat.of V)).fromSpecResidueField (genericPoint _))) := hf.isIso_fiberMap
  rw [fromSpecResidueField_eq_specMap] at hiso
  unfold arithmeticGenus
  rw [eulerChar_fibre_eq_of_isIso p f D hflat D' hflat' _ hiso φ]

omit [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))] [CompactSpace X']
  [IsAffineHom (pullback.diagonal (terminal.from X'))] in
/-- The sections of `𝒪_X` of a flat `V`-scheme form a flat `V`-module (they have no `V`-torsion,
`Cohomology.eq_zero_of_mul_eq_zero_of_flat`). -/
theorem flat_sectionsModuleCat_unit (q : X ⟶ Spec (CommRingCat.of V)) [Flat q] (W : X.Opens) :
    Module.Flat V (sectionsModuleCat (SheafOfModules.unit X.ringCatSheaf) (structureCoeff q) W
      le_top) := by
  rw [ValuationRing.flat_iff_forall_smul_eq_zero]
  intro c hc s hs
  refine Cohomology.eq_zero_of_mul_eq_zero_of_flat q
    (a := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) ?_ (W := W) s hs
  intro h0
  apply hc
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom h0
  rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this

/-- **Equal arithmetic genera of the fibres of an η-modification of projective flat `V`-curves**
(blueprint `lem:sm-bd-genus-modification`, the form used in `lem:sm-stability-criterion`): if
`p : X → Spec V` and `f ≫ p : X′ → Spec V` are projective (`IsProjectiveOver`) and flat, and
`f : X′ → X` is an η-modification, then `p_a(X′_κ) = p_a(X_κ)` for every field point
`φ : V → κ`. -/
theorem arithmeticGenus_fibre_eq_of_isProjectiveOver [Flat p] [Flat (f ≫ p)]
    (hp : IsProjectiveOver p) (hp' : IsProjectiveOver (f ≫ p))
    (hf : Curves.IsEtaModification f p) {κ : Type u} [Field κ] (φ : V →+* κ) :
    arithmeticGenus (pullback (f ≫ p) (Spec.map (CommRingCat.ofHom φ)))
        (structureCoeff (bcSnd φ (f ≫ p))) =
      arithmeticGenus (pullback p (Spec.map (CommRingCat.ofHom φ)))
        (structureCoeff (bcSnd φ p)) := by
  obtain ⟨D⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hp
  obtain ⟨D'⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hp'
  exact arithmeticGenus_fibre_eq_of_isEtaModification p f hf D
    (fun i => flat_sectionsModuleCat_unit p (D.U i)) D'
    (fun i => flat_sectionsModuleCat_unit (f ≫ p) (D'.U i)) φ

end Modification

end DeJongAlterations.StableModification.BlowDown

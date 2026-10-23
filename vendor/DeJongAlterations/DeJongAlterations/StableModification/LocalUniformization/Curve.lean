import DeJongAlterations.StableModification.LocalUniformization.CurveLine
import DeJongAlterations.StableModification.LocalUniformization.CurveEtale
import DeJongAlterations.StableModification.LocalUniformization.CurveUniformization

/-!
# Local uniformization of a curve over a valuation ring (Temkin, Proposition 4.3.3)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
Proposition 4.3.3 (`locunifprop`, `semi-stable.tex` lines 3048–3081): for a curve `C → S` with
smooth generic fibre over `S = Spec R`, `R` a valuation ring of finite height with separably
closed fraction field `K`, there are finitely many strictly semi-stable quasi-modifications
`Cᵢ → C` such that every point of `𝔊 = RZ_L(C)` (`L = K(C)`) is centred on some `Cᵢ`.
Blueprint chapter `sm-local-uniformization-curve.tex` (`prop:sm-local-uniformization`).

## Main results

* `exists_isStrictlySemistable_of_mem_rzSpace` (**the pointwise statement**): every
  `V ∈ RZ_L(C)` is centred on `Spec E` for a subring `E ⊆ L` with a separated morphism of finite
  type `Spec E → C` compatible with the generic points (an affine `L`-quasi-modification of `C`
  in the sense of Temkin §3.2, T:2300–2306) such that `Spec E` is strictly semi-stable over `R`.
* `exists_finite_isStrictlySemistable_cover` (**Proposition 4.3.3**): for `C` quasi-compact,
  finitely many such `Spec Eᵢ` have Riemann–Zariski spaces with union `RZ_L(C)`.
* `exists_finite_isStrictlySemistable_cover_of_isAlgClosed`: the same for `K` algebraically
  closed, without the hypothesis on places.

## The route (plan `PLAN-SM-GEOM.md`, S7)

For `V ∈ RZ_L(C)` with valuation ring `O`, the uniformization property (Temkin's Theorem 2.1.8
with Lemma 2.1.1, `Valuation.uniformizationEtaleStatement`) gives `T ∈ L` with `O` standard
étale over `Ō = O ∩ K(T)` (`exists_isStandardEtale_of_le`); replacing `T` by `T⁻¹` we may assume
`T ∈ O`. With `R' = O ∩ K`, `K(T)` is the function field of `𝔸¹_{R'}` (`lineEmbedding`) and `Ō`
is centred on `𝔸¹_{R'}` with `Ō ∩ K = R'`. The coefficients of a standard étale presentation of
`O` over `Ō` and of expressions of finitely many generators of the coordinate ring of an affine
neighbourhood of the centre of `V` on `C` are finitely many elements of `Ō`; by
`exists_affine_mem_range` they are sections of an affine open `U` of a strictly semi-stable
modification `C₁ → 𝔸¹_{R'}` with `Γ(C₁, U) ⊆ Ō`. The presentation descends to a standard étale
`Γ(C₁, U)`-algebra `E ⊆ O` (`exists_finset_standardEtale_descent`) containing the generators;
`Spec E` is étale over `C₁`, hence strictly semi-stable over `R'` and over `R`, and maps to `C`.
Finally `RZ_L(C)` is quasi-compact and the `RZ_L(Spec E)` are open in it.

This avoids the flattening theorem used by Temkin at line 3065 (`ERRATA.md` T12).

## Hypotheses

* `hsep`: `L/K` has a separating transcendence element (the smoothness of the generic fibre is
  used only through this).
* `hrat : AllPlacesRational K L` (every place of `L/K` has residue field `K`): needed by the
  integrated uniformization property (see `CurveUniformization`); automatic for `K`
  algebraically closed.
* `R` has finite height and equal characteristic; `C` is integral, separated, flat and locally of
  finite type over `R` (quasi-compact for the covering statement).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open scoped IntermediateField

universe u

namespace DeJongAlterations.StableModification.LocalUniformization.Curve

open ValCurves RiemannZariskiSpace Curves
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ### Auxiliary facts on spectra -/

/-- Morphisms out of `Spec E` agree if they agree after an injective map `E → L` to a field. -/
theorem eq_of_specMap_ofHom_comp_eq {E A : CommRingCat.{u}} {L : Type u} [Field L]
    (ι : E →+* L) (hι : Function.Injective ι) {a b : Spec E ⟶ Spec A}
    (h : Spec.map (CommRingCat.ofHom ι) ≫ a = Spec.map (CommRingCat.ofHom ι) ≫ b) : a = b := by
  obtain ⟨α, rfl⟩ := Spec.map_surjective a
  obtain ⟨β, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext y
  exact hι (congrArg (fun f ↦ f.hom y) h')

/-- The section map of a point `Spec γ` of `Spec R` over `Spec R` is `γ`. -/
theorem sectionsToField_SpecMap_top {L : Type u} [Field L] {R : CommRingCat.{u}}
    (γ : R ⟶ CommRingCat.of L) (h : (Spec.map γ) ⁻¹ᵁ ⊤ = ⊤) :
    sectionsToField (Spec.map γ) ⊤ h = ((Scheme.ΓSpecIso R).hom ≫ γ).hom := by
  have key : Spec.map γ = Spec.map ((Scheme.ΓSpecIso R).hom ≫ γ) ≫
      (isAffineOpen_top (Spec R)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp,
      Iso.inv_hom_id_assoc]
  rw [sectionsToField_congr key h (preimage_SpecMap_fromSpec (isAffineOpen_top (Spec R)) _),
    sectionsToField_SpecMap_fromSpec]


/-- If `A → B` is of finite type with generators `s`, every ring map `θ : B → M` sends `B` into
any subring containing the images of `A` and of `s`. -/
theorem map_mem_of_adjoin_eq_top {A B M : Type*} [CommRing A] [CommRing B] [CommRing M]
    (ρ : A →+* B) (θ : B →+* M) (Sb : Subring M) {s : Set B}
    (hs : letI := ρ.toAlgebra; Algebra.adjoin A s = ⊤) (hA : ∀ a, θ (ρ a) ∈ Sb)
    (hsS : ∀ b ∈ s, θ b ∈ Sb) (b : B) : θ b ∈ Sb := by
  let := ρ.toAlgebra
  have hb : b ∈ Algebra.adjoin A s := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hsS x hx
  | algebraMap a => exact hA a
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-! ### Sections of a curve of finite type -/

section FiniteType

variable {K : Type u} [Field K] {R : ValuationSubring K}

/-- **Sections over an affine open of a scheme of finite type over `R`.** The section map
`θ : Γ(C, U) → K(C)` of the generic point contains the image of `R` (through `K → K(C)`), and
there is a finite set `s ⊆ Γ(C, U)` such that `θ` maps `Γ(C, U)` into every subring of `K(C)`
containing the images of `R` and of `s`. -/
theorem exists_finset_sections_mem {C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of R))
    [Flat φ] [LocallyOfFiniteType φ] {UC : C.Opens} (hUC : IsAffineOpen UC)
    (hηUC : genericPt C ⁻¹ᵁ UC = ⊤) :
    letI := functionFieldAlgebra φ
    (∀ r : R, ∃ a, sectionsToField (genericPt C) UC hηUC a = algebraMap K C.functionField r) ∧
    ∃ s : Finset Γ(C, UC), ∀ Sb : Subring C.functionField,
      (∀ r : R, algebraMap K C.functionField r ∈ Sb) →
      (∀ b ∈ s, sectionsToField (genericPt C) UC hηUC b ∈ Sb) →
      ∀ a, sectionsToField (genericPt C) UC hηUC a ∈ Sb := by
  let := functionFieldAlgebra φ
  have e : UC ≤ φ ⁻¹ᵁ ⊤ := le_top
  let ρ : R →+* Γ(C, UC) := ((Scheme.ΓSpecIso (.of R)).inv ≫ φ.appLE ⊤ UC e).hom
  have hθρ : (sectionsToField (genericPt C) UC hηUC).comp ρ =
      (algebraMap K C.functionField).comp R.subtype := by
    have h1 := sectionsToField_comp_appLE φ (genericPt_comp φ) e hηUC rfl
    rw [sectionsToField_SpecMap_top] at h1
    calc (sectionsToField (genericPt C) UC hηUC).comp ρ
        = ((sectionsToField (genericPt C) UC hηUC).comp (φ.appLE ⊤ UC e).hom).comp
            (Scheme.ΓSpecIso (.of R)).inv.hom := rfl
      _ = ((Scheme.ΓSpecIso (.of R)).inv ≫ (Scheme.ΓSpecIso (.of R)).hom ≫
            CommRingCat.ofHom ((algebraMap K C.functionField).comp R.subtype)).hom := by
          rw [h1]; rfl
      _ = _ := by rw [Iso.inv_hom_id_assoc]; rfl
  have hft : ρ.FiniteType := RingHom.FiniteType.comp
    (HasRingHomProperty.appLE @LocallyOfFiniteType φ inferInstance ⟨⊤, isAffineOpen_top _⟩
      ⟨UC, hUC⟩ e)
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2)
  refine ⟨fun r ↦ ⟨ρ r, by rw [← RingHom.comp_apply, hθρ]; rfl⟩, ?_⟩
  let := ρ.toAlgebra
  obtain ⟨s, hs⟩ := (hft : Algebra.FiniteType R Γ(C, UC)).out
  exact ⟨s, fun Sb hR hsS ↦ map_mem_of_adjoin_eq_top ρ _ Sb hs
    (fun r ↦ by rw [← RingHom.comp_apply, hθρ]; exact hR r) hsS⟩

/-- The function field of an integral scheme locally of finite type and flat over `R` is a
finitely generated field extension of `K`. -/
theorem fg_functionField {C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of R)) [Flat φ]
    [LocallyOfFiniteType φ] :
    letI := functionFieldAlgebra φ
    (⊤ : IntermediateField K C.functionField).FG := by
  classical
  let := functionFieldAlgebra φ
  obtain ⟨_, ⟨UC, hUC, rfl⟩, hgUC, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint C)) isOpen_univ
  have hηUC : genericPt C ⁻¹ᵁ UC = ⊤ := by
    rw [← functionFieldPoint_eq_genericPt]
    exact functionFieldPoint_preimage hUC hgUC
  obtain ⟨-, s, hs⟩ := exists_finset_sections_mem φ hUC hηUC
  refine ⟨s.image (sectionsToField (genericPt C) UC hηUC), eq_top_iff.mpr fun z _ ↦ ?_⟩
  have : Nonempty UC := ⟨⟨_, hgUC⟩⟩
  have : IsFractionRing Γ(C, UC) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C UC hUC
  have hθ : sectionsToField (genericPt C) UC hηUC = algebraMap Γ(C, UC) C.functionField := by
    rw [sectionsToField_congr functionFieldPoint_eq_genericPt.symm hηUC
      (functionFieldPoint_preimage hUC hgUC), sectionsToField_functionFieldPoint hUC hgUC]
    rfl
  have hmem : ∀ a, sectionsToField (genericPt C) UC hηUC a ∈
      IntermediateField.adjoin K
        (↑(s.image (sectionsToField (genericPt C) UC hηUC)) : Set C.functionField) :=
    hs (IntermediateField.adjoin K _).toSubalgebra.toSubring
      (fun r ↦ IntermediateField.algebraMap_mem _ _)
      (fun b hb ↦ IntermediateField.subset_adjoin _ _ (Finset.mem_image_of_mem _ hb))
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(C, UC)) z
  rw [← hθ]
  exact div_mem (hmem a) (hmem b)

end FiniteType

/-! ### A strictly semi-stable étale neighbourhood over the line -/

section Line

variable {K : Type u} [Field K] [IsSepClosed K] {L : Type u} [Field L] [Algebra K L]

/-- **Descent of the uniformization to a strictly semi-stable curve** (Temkin, proof of
Proposition 4.3.3, T:3062–3079, route S7). Let `O` be a valuation ring of `L` with
`O ∩ K = R'` of finite height, `S ∈ O` transcendental over `K`, and `O` standard étale over
`O ∩ K(S)`. For every finite set `A ⊆ O` there are a ring `E` with an injective map `E → L` into
`O` whose image contains `A`, and a strictly semi-stable morphism `Spec E → Spec R'` compatible
with `Spec L → Spec R'`. -/
theorem exists_etale_of_isStandardEtale (R' : ValuationSubring K) [Finite (PrimeSpectrum R')]
    (O : ValuationSubring L) (hO : O.comap (algebraMap K L) = R') {S : L}
    (hS : Transcendental K S) (hSO : S ∈ O) (M : IntermediateField K L) (hM : K⟮S⟯ = M)
    [Algebra.IsStandardEtale (O.comap (algebraMap M L)) O] (A : Finset O) :
    ∃ (E : Type u) (_ : CommRing E) (ιE : E →+* L), Function.Injective ιE ∧
      (∀ e, ιE e ∈ O) ∧ (∀ a ∈ A, (a : L) ∈ ιE.range) ∧
      ∃ q : Spec (.of E) ⟶ Spec (.of R'), IsStrictlySemistable q ⊤ ∧
        Spec.map (CommRingCat.ofHom ιE) ≫ q =
          Spec.map (CommRingCat.ofHom ((algebraMap K L).comp R'.subtype)) := by
  classical
  let := functionFieldAlgebra (lineModel R')
  let j := lineEmbedding R' hS
  have hjK : j.comp (algebraMap K (Spec (lineRing R')).functionField) = algebraMap K L :=
    lineEmbedding_comp_algebraMap R' hS
  have hcoef : ∀ r : R', algebraMap K L r ∈ O := fun r ↦ by
    have : (r : K) ∈ O.comap (algebraMap K L) := hO ▸ r.2
    exact this
  have hjP : ∀ P : R'[X], j (lineAlgebraMap R' P) ∈ O := fun P ↦ by
    rw [lineEmbedding_lineAlgebraMap, aeval_def, eval₂_map, eval₂_eq_sum_range]
    exact sum_mem fun i _ ↦ mul_mem (hcoef _) (pow_mem hSO _)
  -- the valuation ring `O ∩ K(S)` of the function field of the line
  let W : RiemannZariskiSpace (Spec (lineRing R')).functionField := ⟨O.comap j⟩
  have hgen : genericPt (Spec (lineRing R')) =
      Spec.map (CommRingCat.ofHom (lineAlgebraMap R')) := by
    rw [genericPt, Spec.fromSpecStalk_eq']
    rfl
  have hW : W ∈ rzSpace (Spec (lineRing R')) := by
    rw [rzSpace, ofScheme_eq_ofOpen_top]
    refine ⟨rfl, mem_ofRingHom.mpr fun a ↦ ?_⟩
    rw [sectionsToField_congr hgen rfl rfl, sectionsToField_SpecMap_top]
    exact hjP _
  have hWK : W.valuationSubring.comap (algebraMap K (Spec (lineRing R')).functionField) = R' := by
    change (O.comap j).comap (algebraMap K _) = R'
    rw [ValuationSubring.comap_comap, hjK, hO]
  -- the coefficients of the descended presentation
  obtain ⟨G, hG⟩ := exists_finset_standardEtale_descent (Ob := O.comap (algebraMap M L)) (O := O) A
  have hz : ∀ c : O.comap (algebraMap M L), ∃ z, j z = ((c : M) : L) := fun c ↦
    exists_lineEmbedding_eq R' hS (by rw [hM]; exact (c : M).2)
  choose zc hzc using hz
  have hF₀ : ∀ b ∈ G.image zc, b ∈ W.valuationSubring := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hb
    show j (zc c) ∈ O
    rw [hzc]
    exact c.2
  -- an affine open of a strictly semi-stable modification of the line with sections in `O`
  have : CompactSpace (Spec (lineRing R')) := inferInstanceAs (CompactSpace (PrimeSpectrum R'[X]))
  obtain ⟨C₁, _, f₁, _, hss₁, U, hU, hηU, hWU, hF₁⟩ :=
    exists_affine_mem_range (lineModel R') (isStrictlySemistable_lineModel R')
      (fiberTrdeg_line_le R') (finiteDimensional_line R') W hW hWK _ hF₀
  let sU := sectionsToField (genericLift f₁) U hηU
  have hsU : Function.Injective sU := by
    let := genericLiftAlgebra f₁
    have hη := functionFieldPoint_genericLiftAlgebra f₁
    have hgU : genericPoint C₁ ∈ U := by
      obtain ⟨z⟩ : Nonempty (Spec (.of (Spec (lineRing R')).functionField)) :=
        inferInstanceAs (Nonempty (PrimeSpectrum _))
      have hz : z ∈ genericLift f₁ ⁻¹ᵁ U := by rw [hηU]; trivial
      have hz' : genericLift f₁ z ∈ U := hz
      rwa [← hη, functionFieldPoint_apply] at hz'
    have := injective_sectionsToField_functionFieldPoint
      (L := (Spec (lineRing R')).functionField) hU hgU
    rwa [sectionsToField_congr hη (functionFieldPoint_preimage hU hgU) hηU] at this
  have hsUW : ∀ y, j (sU y) ∈ O := fun y ↦ mem_ofRingHom.mp hWU y
  let jM : (Spec (lineRing R')).functionField →+* M :=
    j.codRestrict M fun z ↦ by rw [← hM]; exact lineEmbedding_mem_adjoin R' hS z
  let ι : Γ(C₁, U) →+* O.comap (algebraMap M L) :=
    (jM.comp sU).codRestrict (O.comap (algebraMap M L)) hsUW
  have hι : Function.Injective ι := fun y₁ y₂ h ↦
    hsU (j.injective (congrArg (fun c : O.comap (algebraMap M L) ↦ ((c : M) : L)) h))
  have hGι : ∀ c ∈ G, c ∈ ι.range := by
    intro c hc
    obtain ⟨y, hy⟩ := hF₁ (zc c) (Finset.mem_image_of_mem _ hc)
    refine ⟨y, Subtype.ext (Subtype.ext ?_)⟩
    change j (sU y) = ((c : M) : L)
    rw [hy, hzc]
  -- the descended standard étale algebra
  obtain ⟨E, _, _, φE, hstd, hφE, hcomm, hA⟩ := hG Γ(C₁, U) ι hι hGι
  let ιE : E →+* L := O.subtype.comp φE
  have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(C₁, U) E)) ≫ hU.fromSpec) := by
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(C₁, U) E))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact RingHom.etale_algebraMap.mpr inferInstance
    infer_instance
  have hq := hss₁.etale_comp (Spec.map (CommRingCat.ofHom (algebraMap Γ(C₁, U) E)) ≫ hU.fromSpec)
  rw [Scheme.IdealSheafData.comap_top] at hq
  have hcompat : Spec.map (CommRingCat.ofHom ιE) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(C₁, U) E)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom sU) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext y
    change (φE (algebraMap Γ(C₁, U) E y) : L) = j (sU y)
    rw [← RingHom.comp_apply, hcomm]
    rfl
  refine ⟨E, inferInstance, ιE, Subtype.val_injective.comp hφE, fun e ↦ (φE e).2,
    fun a ha ↦ ?_, _, hq, ?_⟩
  · obtain ⟨e, he⟩ := hA a ha
    exact ⟨e, congrArg Subtype.val he⟩
  · calc Spec.map (CommRingCat.ofHom ιE) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(C₁, U) E)) ≫ hU.fromSpec) ≫ f₁ ≫
            lineModel R'
        = Spec.map (CommRingCat.ofHom j) ≫ (Spec.map (CommRingCat.ofHom sU) ≫ hU.fromSpec) ≫
            f₁ ≫ lineModel R' := by
          rw [Category.assoc, reassoc_of% hcompat]
          simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom j) ≫ (genericLift f₁ ≫ f₁) ≫ lineModel R' := by
          rw [SpecMap_sectionsToField_fromSpec, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
            ((algebraMap K (Spec (lineRing R')).functionField).comp R'.subtype)) := by
          rw [genericLift_comp, genericPt_comp]
      _ = _ := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hjK]

end Line

/-! ### Proposition 4.3.3 -/

section Main

variable {K : Type u} [Field K] [IsSepClosed K] {R : ValuationSubring K} [Finite (PrimeSpectrum R)]

/-- **Local uniformization at one valuation** (the pointwise form of Temkin, Proposition 4.3.3;
blueprint `prop:sm-local-uniformization`). Let `R` be a valuation ring of finite height of the
separably closed field `K`, of equal characteristic, and `C` an integral separated scheme, flat
and locally of finite type over `R`, whose function field `L` has a separating transcendence
element over `K` and only places with residue field `K`. Then every `V ∈ RZ_L(C)` is centred on
`Spec E` for a ring `E` embedded in `L` (so `Spec L → Spec E` is schematically dominant) with a
separated morphism of finite type `g : Spec E → C` compatible with the generic points, such that
`Spec E` is strictly semi-stable over `R`. -/
theorem exists_isStrictlySemistable_of_mem_rzSpace
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p)
    {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated] (φ : C ⟶ Spec (.of R)) [Flat φ]
    [LocallyOfFiniteType φ]
    (hsep : letI := functionFieldAlgebra φ
      ∃ x : C.functionField, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ C.functionField)
    (hrat : letI := functionFieldAlgebra φ; AllPlacesRational K C.functionField)
    (V : RiemannZariskiSpace C.functionField) (hV : V ∈ rzSpace C) :
    ∃ (E : Type u) (_ : CommRing E) (ιE : E →+* C.functionField) (g : Spec (.of E) ⟶ C),
      Function.Injective ιE ∧ Spec.map (CommRingCat.ofHom ιE) ≫ g = genericPt C ∧
      LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsSeparated g ∧
      IsStrictlySemistable (g ≫ φ) ⊤ ∧ V ∈ ofScheme (Spec.map (CommRingCat.ofHom ιE)) := by
  classical
  let := functionFieldAlgebra φ
  -- an affine neighbourhood `UC` of the centre of `V` and its section map `θC`
  obtain ⟨x, hVx⟩ := exists_isCentre_of_mem_ofScheme hV
  obtain ⟨_, ⟨UC, hUC, rfl⟩, hxUC, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨hηUC, hVUC⟩ := mem_ofOpen_of_extension' hVx hxUC
  have hθO : ∀ a, sectionsToField (genericPt C) UC hηUC a ∈ V.valuationSubring :=
    mem_ofRingHom.mp hVUC
  obtain ⟨hRθ, s, hs⟩ := exists_finset_sections_mem φ hUC hηUC
  have hRO : R ≤ V.valuationSubring.comap (algebraMap K C.functionField) := fun r hr ↦ by
    obtain ⟨a, ha⟩ := hRθ ⟨r, hr⟩
    have := hθO a
    rw [ha] at this
    exact this
  -- the uniformization property: `O` is standard étale over `O ∩ K(T₀)`
  obtain ⟨T₀, hT₀, hstd⟩ := exists_isStandardEtale_of_le hchar (fg_functionField φ) hsep hrat
    V.valuationSubring hRO
  obtain ⟨S, hS, hSO, hM⟩ : ∃ S : C.functionField, Transcendental K S ∧
      S ∈ V.valuationSubring ∧ K⟮S⟯ = K⟮T₀⟯ := by
    rcases V.valuationSubring.mem_or_inv_mem T₀ with h | h
    · exact ⟨T₀, hT₀, h, rfl⟩
    · refine ⟨T₀⁻¹, fun h' ↦ hT₀ (IsAlgebraic.inv_iff.mp h'), h, le_antisymm ?_ ?_⟩
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self K T₀)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have := inv_mem (IntermediateField.mem_adjoin_simple_self K T₀⁻¹)
        rwa [inv_inv] at this
  have := finite_primeSpectrum R _ hRO
  obtain ⟨E, _, ιE, hιE, hιEO, hAE, q, hq, hqc⟩ :=
    exists_etale_of_isStandardEtale (V.valuationSubring.comap (algebraMap K C.functionField))
      V.valuationSubring rfl hS hSO K⟮T₀⟯ hM
      (s.image fun a ↦ ⟨sectionsToField (genericPt C) UC hηUC a, hθO a⟩)
  -- the ring map `R' → E`
  obtain ⟨ρq, rfl⟩ := Spec.map_surjective q
  have hρq : ιE.comp ρq.hom = (algebraMap K C.functionField).comp
      (V.valuationSubring.comap (algebraMap K C.functionField)).subtype := by
    rw [← Spec.map_comp] at hqc
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hqc)
  -- `Γ(C, UC)` maps into `E`
  have hθE : ∀ a, sectionsToField (genericPt C) UC hηUC a ∈ ιE.range :=
    hs ιE.range (fun r ↦ ⟨ρq.hom ⟨r, hRO r.2⟩, by rw [← RingHom.comp_apply, hρq]; rfl⟩)
      (fun b hb ↦ hAE _ (Finset.mem_image_of_mem _ hb))
  let eE : E ≃+* ιE.range := RingEquiv.ofBijective ιE.rangeRestrict
    ⟨fun a b h ↦ hιE (congrArg Subtype.val h), ιE.rangeRestrict_surjective⟩
  let γ : Γ(C, UC) →+* E :=
    eE.symm.toRingHom.comp ((sectionsToField (genericPt C) UC hηUC).codRestrict ιE.range hθE)
  have hγ : ιE.comp γ = sectionsToField (genericPt C) UC hηUC := by
    ext a
    change ((eE (eE.symm _) : ιE.range) : C.functionField) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  have hcomp : Spec.map (CommRingCat.ofHom ιE) ≫ Spec.map (CommRingCat.ofHom γ) ≫
      hUC.fromSpec = genericPt C := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hγ]
    exact SpecMap_sectionsToField_fromSpec (genericPt C) hUC hηUC
  have hgφ : (Spec.map (CommRingCat.ofHom γ) ≫ hUC.fromSpec) ≫ φ =
      Spec.map ρq ≫ specInclusion R _ hRO := by
    apply eq_of_specMap_ofHom_comp_eq ιE hιE
    have h1 : Spec.map (CommRingCat.ofHom ιE) ≫ (Spec.map (CommRingCat.ofHom γ) ≫
        hUC.fromSpec) ≫ φ =
        Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp R.subtype)) := by
      rw [← Category.assoc, hcomp, genericPt_comp]
    have h2 : Spec.map (CommRingCat.ofHom ιE) ≫ Spec.map ρq ≫ specInclusion R _ hRO =
        Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp R.subtype)) := by
      change Spec.map (CommRingCat.ofHom ιE) ≫ Spec.map ρq ≫
        Spec.map (CommRingCat.ofHom (ValuationSubring.inclusion R _ hRO)) = _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      change ιE (ρq.hom (ValuationSubring.inclusion R _ hRO r)) = _
      rw [← RingHom.comp_apply, hρq]
      rfl
    rw [h1, h2]
  have hss : IsStrictlySemistable ((Spec.map (CommRingCat.ofHom γ) ≫ hUC.fromSpec) ≫ φ) ⊤ := by
    rw [hgφ]
    exact Blowups.IsStrictlySemistable.comp_isOpenImmersion hq _
  refine ⟨E, inferInstance, ιE, Spec.map (CommRingCat.ofHom γ) ≫ hUC.fromSpec, hιE, hcomp, ?_,
    inferInstance, inferInstance, hss, ?_⟩
  · have : DeJong.IsNodalCurve ((Spec.map (CommRingCat.ofHom γ) ≫ hUC.fromSpec) ≫ φ) :=
      hss.isNodalCurve
    exact locallyOfFiniteType_of_comp _ φ
  · rw [ofScheme_eq_ofOpen_top]
    refine ⟨rfl, mem_ofRingHom.mpr fun a ↦ ?_⟩
    rw [sectionsToField_SpecMap_top]
    exact hιEO _

/-- **Temkin, Proposition 4.3.3** (`locunifprop`; blueprint `prop:sm-local-uniformization`).
Under the hypotheses of `exists_isStrictlySemistable_of_mem_rzSpace`, with `C` moreover
quasi-compact, there are finitely many subrings `Eᵢ ⊆ L` and separated morphisms of finite type
`gᵢ : Spec Eᵢ → C` compatible with the generic points (`L`-quasi-modifications of `C`), each
`Spec Eᵢ` strictly semi-stable over `R`, such that `RZ_L(C)` is the union of the
`RZ_L(Spec Eᵢ)`: every point of `RZ_L(C)` is centred on some `Spec Eᵢ`. -/
theorem exists_finite_isStrictlySemistable_cover
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p)
    {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated] [CompactSpace C] (φ : C ⟶ Spec (.of R))
    [Flat φ] [LocallyOfFiniteType φ]
    (hsep : letI := functionFieldAlgebra φ
      ∃ x : C.functionField, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ C.functionField)
    (hrat : letI := functionFieldAlgebra φ; AllPlacesRational K C.functionField) :
    ∃ (ι : Type u) (_ : Finite ι) (E : ι → Type u) (_ : ∀ i, CommRing (E i))
      (ιE : ∀ i, E i →+* C.functionField) (g : ∀ i, Spec (.of (E i)) ⟶ C),
      (∀ i, Function.Injective (ιE i) ∧ Spec.map (CommRingCat.ofHom (ιE i)) ≫ g i = genericPt C ∧
        LocallyOfFiniteType (g i) ∧ QuasiCompact (g i) ∧ IsSeparated (g i) ∧
        IsStrictlySemistable (g i ≫ φ) ⊤) ∧
      rzSpace C = ⋃ i, ofScheme (Spec.map (CommRingCat.ofHom (ιE i))) := by
  choose E _ ιE g hg using fun V : rzSpace C ↦
    exists_isStrictlySemistable_of_mem_rzSpace hchar φ hsep hrat V.1 V.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : rzSpace C ↦
      (Subtype.val : rzSpace C → _) ⁻¹' ofScheme (Spec.map (CommRingCat.ofHom (ιE V))))
    (fun V ↦ by
      have := (hg V).2.2.1
      exact isOpen_ofScheme_of_locallyOfFiniteType (g V) (hg V).2.1)
    (fun V _ ↦ Set.mem_iUnion.mpr ⟨V, (hg V).2.2.2.2.2.2⟩)
  refine ⟨t, inferInstance, fun i ↦ E i.1, fun i ↦ inferInstance, fun i ↦ ιE i.1,
    fun i ↦ g i.1, fun i ↦ ⟨(hg i.1).1, (hg i.1).2.1, (hg i.1).2.2.1, (hg i.1).2.2.2.1,
      (hg i.1).2.2.2.2.1, (hg i.1).2.2.2.2.2.1⟩,
    Set.Subset.antisymm (fun V hV ↦ ?_)
      (Set.iUnion_subset fun i ↦ ofScheme_subset_of_comp (g i.1) (hg i.1).2.1)⟩
  obtain ⟨i, hi, hVi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ⟨V, hV⟩))
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hVi⟩

/-- **Temkin, Proposition 4.3.3 for `K` algebraically closed**: the hypothesis on places in
`exists_finite_isStrictlySemistable_cover` is automatic. -/
theorem exists_finite_isStrictlySemistable_cover_of_isAlgClosed [IsAlgClosed K]
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p)
    {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated] [CompactSpace C] (φ : C ⟶ Spec (.of R))
    [Flat φ] [LocallyOfFiniteType φ]
    (hsep : letI := functionFieldAlgebra φ
      ∃ x : C.functionField, Transcendental K x ∧ Algebra.IsSeparable K⟮x⟯ C.functionField) :
    ∃ (ι : Type u) (_ : Finite ι) (E : ι → Type u) (_ : ∀ i, CommRing (E i))
      (ιE : ∀ i, E i →+* C.functionField) (g : ∀ i, Spec (.of (E i)) ⟶ C),
      (∀ i, Function.Injective (ιE i) ∧ Spec.map (CommRingCat.ofHom (ιE i)) ≫ g i = genericPt C ∧
        LocallyOfFiniteType (g i) ∧ QuasiCompact (g i) ∧ IsSeparated (g i) ∧
        IsStrictlySemistable (g i ≫ φ) ⊤) ∧
      rzSpace C = ⋃ i, ofScheme (Spec.map (CommRingCat.ofHom (ιE i))) :=
  let := functionFieldAlgebra φ
  exists_finite_isStrictlySemistable_cover hchar φ hsep
    (allPlacesRational_of_isAlgClosed (fg_functionField φ) hsep)

end Main

end DeJongAlterations.StableModification.LocalUniformization.Curve

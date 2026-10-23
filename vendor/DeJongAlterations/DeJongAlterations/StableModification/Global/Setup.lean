import DeJongAlterations.StableModification.Global.Pairwise
import DeJongAlterations.StableModification.DeJong.BaseStepFibers
import DeJongAlterations.StableModification.Valuation.FiniteHeight
import DeJongAlterations.Algebra.FunctionFieldDimension
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension

/-!
# The curve over a valuation ring of `RZ_{K(S)ᵃ}(S)`

Node G1 of `PLAN-T5.md` (§2.1 step 1; Temkin, *Stable modification of relative curves*,
`semi-stable.tex`, proof of Theorem 1.5, T:3384–3388). Let `(C, D)` be a multipointed `S`-curve
over an integral base whose generic fibre is smooth, geometrically integral (decision D-DJ6) and,
with the marks, semi-stable. For a morphism `ψ : T ⟶ S` from an integral scheme mapping the
generic point to the generic point (e.g. the extension `Spec W ⟶ S` of the `K(S)ᵃ`-point to a
valuation ring `W` of `RZ_{K(S)ᵃ}(S)`):

* the generic fibre of `C ×_S T ⟶ T` is the base change of the generic fibre of `C ⟶ S`
  along the residue field extension (`isPullback_fiber_pullback_snd`), hence integral;
* `C ×_S T` is integral (`isIntegral_pullback_of_generic`): flat over `T`, so its generic fibre
  is schematically dense (`isIntegral_of_isSchemeTheoreticallyDominant`);
* the generic pair of `(C, D) ×_S T` is semi-stable (`isSemistablePair_generic_pullback`).

Blueprint: `sm-global.tex`, `lem:sm-global-setup`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective IsMultipointedCurve IsSmoothAt)
open Curves (pullbackCompMap IsStableModification)

section Fibre

variable {C S T : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **The fibre of a base change is the base change of the fibre**: `(C ×_S T)_t` is the base
change of `C_{ψ(t)} ⟶ Spec κ(ψ(t))` along `Spec κ(t) ⟶ Spec κ(ψ(t))` (Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback`). -/
theorem isPullback_fiber_pullback_snd (g : C ⟶ S) (ψ : T ⟶ S) (t : T) :
    IsPullback (pullback.map _ _ _ _ (pullback.fst g ψ) (Spec.map (ψ.residueFieldMap t)) ψ
        (IsPullback.of_hasPullback g ψ).w.symm (by simp))
      ((pullback.snd g ψ).fiberToSpecResidueField t) (g.fiberToSpecResidueField (ψ t))
      (Spec.map (ψ.residueFieldMap t)) :=
  isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback g ψ) t

variable [IsIntegral S]

/-- **Integrality of the base change** (`PLAN-T5.md` §2.1 step 1, G1; D-DJ6). For `g : C ⟶ S`
flat with geometrically integral generic fibre and `ψ : T ⟶ S` from an integral scheme mapping
the generic point to the generic point, `C ×_S T` is integral: its generic fibre over `T` is a
base change of the generic fibre of `g` along a field extension, hence integral, and it is
schematically dense because `C ×_S T` is flat over `T`. -/
theorem isIntegral_pullback_of_generic (g : C ⟶ S) [Flat g]
    (hgi : GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S))) [IsIntegral T]
    (ψ : T ⟶ S) (hη : ψ (genericPoint T) = genericPoint S) :
    IsIntegral (pullback (C := Scheme.{u}) g ψ) := by
  have hfib : IsIntegral ((pullback.snd g ψ).fiber (genericPoint T)) := by
    rw [← hη] at hgi
    exact hgi.geometrically_isIntegral _ _ _ (isPullback_fiber_pullback_snd g ψ _)
  have : QuasiCompact ((pullback.snd g ψ).fiberι (genericPoint T)) :=
    inferInstanceAs (QuasiCompact (pullback.fst (pullback.snd g ψ)
      (T.fromSpecResidueField (genericPoint T))))
  have : IsSchemeTheoreticallyDominant ((pullback.snd g ψ).fiberι (genericPoint T)) :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  exact DeJong.isIntegral_of_isSchemeTheoreticallyDominant
    ((pullback.snd g ψ).fiberι (genericPoint T))

omit [IsIntegral S] in
/-- **Smoothness over a point of the base is inherited from the fibre when the point is open**
(e.g. the generic point of the spectrum of a valuation ring of finite height). -/
theorem isSmoothAt_of_smooth_fiber {X : Scheme.{u}} (f : X ⟶ T) (t : T)
    (ht : IsOpen ({t} : Set T)) (hfield : IsField (T.presheaf.stalk t))
    (hsm : Smooth (f.fiberToSpecResidueField t)) (x : X) (hx : f x = t) : IsSmoothAt f x := by
  have : IsOpenImmersion (T.fromSpecResidueField t) :=
    Limits.SpreadModification.isOpenImmersion_fromSpecResidueField t ht hfield
  have : IsOpenImmersion (f.fiberι t) :=
    inferInstanceAs (IsOpenImmersion (pullback.fst f (T.fromSpecResidueField t)))
  have hx' : x ∈ Set.range (f.fiberι t) := by
    rw [Scheme.Hom.range_fiberι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  refine Curves.isSmoothAt_of_isOpenImmersion_comp (f.fiberι t) ?_
  rw [Scheme.Hom.fiber_fac]
  exact Curves.isSmoothAt_of_smooth _ y

/-- **The generic fibre of a base change is smooth** when the generic fibre of `g` is, for
`ψ : T ⟶ S` mapping the generic point to the generic point. -/
theorem smooth_fiber_pullback_snd (g : C ⟶ S)
    (hsm : Smooth (g.fiberToSpecResidueField (genericPoint S))) [IsIntegral T] (ψ : T ⟶ S)
    (hη : ψ (genericPoint T) = genericPoint S) :
    Smooth ((pullback.snd g ψ).fiberToSpecResidueField (genericPoint T)) := by
  rw [← hη] at hsm
  exact MorphismProperty.of_isPullback (P := @Smooth)
    (isPullback_fiber_pullback_snd g ψ (genericPoint T)) hsm

set_option backward.isDefEq.respectTransparency false in
/-- **The generic pair of a base change is semi-stable** when the generic pair of `(C, D)` is,
for `ψ : T ⟶ S` mapping the generic point to the generic point. -/
theorem isSemistablePair_generic_pullback (g : C ⟶ S) (D : C.IdealSheafData)
    (hss : IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
      (DeJong.fiberMarks g D (genericPoint S))) [IsIntegral T] (ψ : T ⟶ S)
    (hη : ψ (genericPoint T) = genericPoint S) :
    IsSemistablePair ((pullback.snd g ψ).fiberToSpecResidueField (genericPoint T))
      (DeJong.fiberMarks (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) (genericPoint T)) := by
  rw [← hη] at hss
  set H := isPullback_fiber_pullback_snd g ψ (genericPoint T)
  have h1 := Curves.IsSemistablePair.pullback hss (Spec.map (ψ.residueFieldMap (genericPoint T)))
  have h2 := Curves.IsSemistablePair.etale_comp h1 H.isoPullback.hom
  rw [H.isoPullback_hom_snd] at h2
  have hm : ((DeJong.fiberMarks g D (ψ (genericPoint T))).comap
      (pullback.fst (g.fiberToSpecResidueField (ψ (genericPoint T)))
        (Spec.map (ψ.residueFieldMap (genericPoint T))))).comap H.isoPullback.hom =
      DeJong.fiberMarks (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) (genericPoint T) := by
    simp only [DeJong.fiberMarks, ← Scheme.IdealSheafData.comap_comp]
    congr 1
    rw [H.isoPullback_hom_fst_assoc]
    exact pullback.lift_fst _ _ _
  rw [hm] at h2
  exact h2

end Fibre

section Valuation

open RiemannZariskiSpace

variable {k : Type u} [Field k] {S C : Scheme.{u}} [IsIntegral S] {pS : S ⟶ Spec (.of k)}
  {g : C ⟶ S} {D : C.IdealSheafData} {L : Type u} [Field L] [Algebra S.functionField L]

/-- The generic point of `Spec W` maps to the generic point of `S`, for `W ∈ RZ_L(S)`. -/
theorem apply_genericPoint_of_extension (W : RiemannZariskiSpace L)
    (ψ : Spec (.of W.valuationSubring) ⟶ S)
    (hψ : toSpecValuationSubring W ≫ ψ = functionFieldPoint S L) :
    ψ (genericPoint (Spec (.of W.valuationSubring))) = genericPoint S := by
  have : IsDominant (toSpecValuationSubring W) :=
    isDominant_SpecMap_of_injective _ Subtype.val_injective
  rw [← genericPoint_map_of_isDominant (toSpecValuationSubring W), ← Scheme.Hom.comp_apply, hψ,
    functionFieldPoint_apply]

/-- **The curve over a valuation ring of `RZ_L(S)`** (`PLAN-T5.md` §2.1 step 1, node G1). For
`S` integral over `k` with `C` projective over `k`, `(C, D)` a multipointed `S`-curve whose
generic fibre is smooth, geometrically integral and, with the marks, semi-stable, and `W` a
valuation ring of `L` of finite height in `RZ_L(S)` with extension `ψ : Spec W ⟶ S`, the
base change `(C, D) ×_S Spec W` is a curve over `W` in the situation of Temkin's §4.5
(`IsValuationCurve`). -/
theorem isValuationCurve_pullback [IsSeparated pS] (hC : IsProjectiveOver (g ≫ pS))
    (hD : IsMultipointedCurve g D) (hsm : Smooth (g.fiberToSpecResidueField (genericPoint S)))
    (hss : IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
      (DeJong.fiberMarks g D (genericPoint S)))
    (hgi : GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)))
    (W : RiemannZariskiSpace L) [Finite (PrimeSpectrum W.valuationSubring)]
    (ψ : Spec (.of W.valuationSubring) ⟶ S)
    (hψ : toSpecValuationSubring W ≫ ψ = functionFieldPoint S L) :
    IsValuationCurve (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) := by
  have hη := apply_genericPoint_of_extension W ψ hψ
  have := hD.flat
  have := hD.locallyOfFinitePresentation
  refine
    { isIntegral := isIntegral_pullback_of_generic g hgi ψ hη
      flat := inferInstance
      locallyOfFinitePresentation := inferInstance
      isProjectiveOver := ?_
      isSmoothAt_generic := fun x hx ↦ isSmoothAt_of_smooth_fiber _ _
        (Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite _)
        (Field.toIsField (Spec (.of W.valuationSubring)).functionField)
        (smooth_fiber_pullback_snd g hsm ψ hη) x hx
      marksFlat := by
        have := hD.marksFlat
        exact Curves.flat_comap_fst_subschemeι_snd g ψ D
      genericPair := isSemistablePair_generic_pullback g D hss ψ hη }
  have h1 := Projectivity.isRelativelyProjective_of_isProjectiveOver pS g hC
  have h2 := h1.pullback_snd ψ
  have e : ψ ≫ pS = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Spec.preimage (ψ ≫ pS)).hom) := by
    simp
  rw [e, Projectivity.isRelativelyProjective_comp_specMap_iff] at h2
  exact (DeJong.isRelativelyProjective_id_iff _).mp h2

variable (pS L) in
/-- The map `k → K(S) → L` of the constants. -/
def constMap : k →+* L :=
  (algebraMap S.functionField L).comp
    (letI := Geometry.SeparableGenericSmoothness.functionFieldAlgebra pS
    algebraMap k S.functionField)

/-- **The constants lie in every valuation ring of `RZ_L(S)`**: they come from the sections over
an affine open containing the centre. -/
theorem constMap_mem (W : RiemannZariskiSpace L) (hW : W ∈ ofScheme (functionFieldPoint S L))
    (x : k) : constMap pS L x ∈ W.valuationSubring := by
  obtain ⟨ψ, hψ⟩ := hW
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ψ (specClosedPoint W))) isOpen_univ
  have hgU : genericPoint S ∈ U :=
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr ⟨_, trivial, hcU⟩
  obtain ⟨hηU, hWU⟩ := mem_ofOpen_of_extension ψ hψ hcU
  rw [mem_ofRingHom] at hWU
  have : Nonempty (⟨U, hU⟩ : S.affineOpens).1 := ⟨⟨_, hgU⟩⟩
  let := Geometry.SeparableGenericSmoothness.functionFieldAlgebra pS
  let := Geometry.RationalCoordinateMap.sectionAlgebra pS ⟨U, hU⟩
  have := Geometry.RationalCoordinateMap.functionFieldScalarTower pS ⟨U, hU⟩
  have key := hWU (Geometry.RationalCoordinateMap.coefficientMap pS ⟨U, hU⟩ x)
  rw [sectionsToField_functionFieldPoint hU hgU] at key
  convert key using 1
  simp only [constMap, RingHom.comp_apply]
  congr 1
  exact IsScalarTower.algebraMap_apply k Γ(S, U) S.functionField x

/-- **Valuation rings of `RZ_L(S)` have finite height** for `S` a variety over `k` and `L`
algebraic over `K(S)` (Temkin, Corollary 2.1.3 (i); `Valuation.finite_primeSpectrum_of_trdeg_eq`
of lane VAL0): the height is at most `trdeg_k L = trdeg_k K(S) = dim S`. -/
theorem finite_primeSpectrum_of_mem [LocallyOfFiniteType pS]
    [Algebra.IsAlgebraic S.functionField L] (W : RiemannZariskiSpace L)
    (hW : W ∈ ofScheme (functionFieldPoint S L)) : Finite (PrimeSpectrum W.valuationSubring) := by
  let : Algebra k S.functionField := Geometry.SeparableGenericSmoothness.functionFieldAlgebra pS
  let : Algebra k L := (constMap pS L).toAlgebra
  have : IsScalarTower k S.functionField L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨d, -, hd⟩ := Geometry.FunctionFieldDimension.exists_dimension_and_trdeg pS
  have htr : Algebra.trdeg k L = d := by
    rw [← hd]
    exact (Algebra.FunctionFieldDimension.trdeg_eq_of_isAlgebraic k S.functionField L).symm
  exact Valuation.finite_primeSpectrum_of_trdeg_eq W.valuationSubring
    (fun x ↦ constMap_mem W hW x) htr

include pS in
/-- **Equal characteristic**: `L` and the residue field of a valuation ring of `RZ_L(S)` have the
exponential characteristic of `k`. -/
theorem exists_expChar_of_mem (W : RiemannZariskiSpace L)
    (hW : W ∈ ofScheme (functionFieldPoint S L)) :
    ∃ p : ℕ, ExpChar L p ∧ ExpChar (IsLocalRing.ResidueField W.valuationSubring) p := by
  refine ⟨ringExpChar k, expChar_of_injective_ringHom (constMap pS L).injective _, ?_⟩
  let f : k →+* W.valuationSubring :=
    (constMap pS L).codRestrict W.valuationSubring (constMap_mem W hW)
  exact expChar_of_injective_ringHom ((IsLocalRing.residue _).comp f).injective _

/-- Relative projectivity over `Spec W ⟶ Spec k` of a morphism to a curve projective over `W`
gives projectivity over `W`. -/
theorem isProjectiveOver_of_isRelativelyProjective {V : Type u} [CommRing V] {X Y : Scheme.{u}}
    (φ : Y ⟶ Spec (.of V)) (hφ : IsProjectiveOver φ) (ψ : Spec (.of V) ⟶ Spec (.of k))
    (β : X ⟶ Y) (h : IsRelativelyProjective (φ ≫ ψ) β) : IsProjectiveOver (β ≫ φ) := by
  have e : φ ≫ ψ = φ ≫ Spec.map (CommRingCat.ofHom (Spec.preimage ψ).hom) := by simp
  rw [e, Projectivity.isRelativelyProjective_comp_specMap_iff] at h
  exact h.isProjectiveOver hφ

/-- **Uniqueness of stable models over the valuation rings of `RZ_L(S)`** from lane T45B's
`ValuationStableUniqueness` (node G1): the base changes are curves over the valuation ring in the
situation of Temkin's §4.5 (`isValuationCurve_pullback`), and stable models are stable,
numerically stable and projective over the valuation ring. -/
theorem stableModelUniqueOver_of [IsAlgClosed L] (hU : ValuationStableUniqueness.{u})
    [IsSeparated pS] (hC : IsProjectiveOver (g ≫ pS)) (hD : IsMultipointedCurve g D)
    (hsm : Smooth (g.fiberToSpecResidueField (genericPoint S)))
    (hss : IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
      (DeJong.fiberMarks g D (genericPoint S)))
    (hgi : GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)))
    (hfin : ∀ W ∈ ofScheme (functionFieldPoint S L), Finite (PrimeSpectrum W.valuationSubring))
    (hchar : ∀ W ∈ ofScheme (functionFieldPoint S L),
      ∃ p : ℕ, ExpChar L p ∧ ExpChar (IsLocalRing.ResidueField W.valuationSubring) p) :
    StableModelUniqueOver pS g D L := by
  intro W ψ hψ X₁ X₂ β₁ β₂ D₁ D₂ hm₁ hm₂
  have hW : W ∈ ofScheme (functionFieldPoint S L) := ⟨ψ, hψ⟩
  have := hfin W hW
  have hV := isValuationCurve_pullback hC hD hsm hss hgi W ψ hψ
  exact hU L W.valuationSubring (hchar W hW) _ (pullback.snd g ψ) (D.comap (pullback.fst g ψ))
    hV X₁ X₂ β₁ β₂ D₁ D₂ hm₁.isStableModification hm₁.isNumericallyStable
    (isProjectiveOver_of_isRelativelyProjective _ hV.isProjectiveOver _ β₁
      hm₁.isRelativelyProjective)
    hm₂.isStableModification hm₂.isNumericallyStable
    (isProjectiveOver_of_isRelativelyProjective _ hV.isProjectiveOver _ β₂
      hm₂.isRelativelyProjective)

end Valuation

end DeJongAlterations.StableModification.Global

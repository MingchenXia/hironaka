import Hironaka.Geometry.QuotGrassmannPivotOverPivotMaps

/-!
# The SAME actual original global contraction has its internally produced local split factorization

The original maps q=C r, s from original pivot columns, and J=s C satisfy the
actual split identities and whole native factorization, by the actual original
scalar coefficient identities. No local factorization data is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

private theorem originalFiniteFree_expand
    {C : Type*} [Category C] [Preadditive C] {I : Type u} [Fintype I]
    {L P A B K Z : C} (l : L ⟶ A) (q : A ⟶ B) (J : B ⟶ K) (d : K ⟶ Z)
    (π : I → (B ⟶ P)) (ι : I → (P ⟶ B))
    (h : ∑ i : I, π i ≫ ι i = 𝟙 B) :
    l ≫ q ≫ J ≫ d = ∑ i : I, (l ≫ q ≫ π i) ≫ (ι i ≫ J ≫ d) := by
  calc
    _ = (l ≫ q) ≫ (∑ i : I, π i ≫ ι i) ≫ (J ≫ d) := by
      rw [h]
      simp only [Category.id_comp, Category.assoc]
    _ = _ := by simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]

private theorem originalActualOverUnitEnd_commute (X : Scheme.{u}) (U : X.Opens)
    (b c : End (SheafOfModules.unit (X.ringCatSheaf.over U))) : b ≫ c = c ≫ b := by
  apply originalOverUnitEnd_ext_one_top
  change originalOverUnitCoefficient X U (b ≫ c) = originalOverUnitCoefficient X U (c ≫ b)
  rw [originalOverUnitEnd_comp_one_top, originalOverUnitEnd_comp_one_top, mul_comm]

private theorem originalOverFramedCoproductProduct_hom_ext
    (X : Scheme.{u}) (U : X.Opens) {E S : Type u} (T : X.Modules)
    (frame : T.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {f g : (SheafOfModules.free (R := X.ringCatSheaf) E).over U ⟶
      (∏ᶜ fun (_ : S) => T).over U}
    (h : ∀ a row,
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map (SheafOfModules.ιFree a) ≫
        f ≫ (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map
          (Pi.π (fun (_ : S) => T) row) ≫ frame.hom :
            End (SheafOfModules.unit (X.ringCatSheaf.over U))) =
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map (SheafOfModules.ιFree a) ≫
        g ≫ (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map
          (Pi.π (fun (_ : S) => T) row) ≫ frame.hom :
            End (SheafOfModules.unit (X.ringCatSheaf.over U)))) : f = g := by
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  let := originalOverFunctor_preservesColimits X U
  let := originalOverFunctor_preservesLimits X U
  apply (isColimitOfPreserves F
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) E)).hom_ext
  intro a
  apply (isLimitOfPreserves F (productIsProduct (fun (_ : S) => T))).hom_ext
  intro row
  apply (cancel_mono frame.hom).mp
  simp only [Category.assoc]
  exact h a.as row.as

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The SAME actual original pivot columns split the SAME actual native local quotient. -/
theorem originalOverPivotSection_quotient :
    originalOverPivotSection R ι ν (pivotIndex (coordinateSelector ι ν) e) ≫
      originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e) = 𝟙 _ := by
  let j := pivotIndex (coordinateSelector ι ν) e
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν j
  have hp : coordinateSelector ι ν j = e ∘ Sum.inl :=
    (coordinateSelector ι ν).apply_symm_apply (e ∘ Sum.inl)
  apply (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf.over U) ι).hom_ext
  intro i
  apply originalOverFreeProjection_hom_ext X U (I := ι)
  intro h
  change SheafOfModules.ιFree i.as ≫
      (originalOverPivotSection R ι ν j ≫ originalOverPivotQuotient R ι ν j) ≫
        originalOverFreeProjection X U h =
    SheafOfModules.ιFree i.as ≫ 𝟙 _ ≫ originalOverFreeProjection X U h
  have hi := congrArg (fun l => l ≫ originalOverPivotQuotient R ι ν j ≫
    originalOverFreeProjection X U h) (originalOverPivotSection_inclusion R ι ν j i.as)
  have hc := originalOverPivotQuotient_coefficient R ι ν j (coordinateSelector ι ν j i.as) h
  have hb : originalOverContractionEntry R ι ν j
      (coordinateSelector ι ν j i.as) (coordinateSelector ι ν j, h) =
        if h = i.as then 𝟙 _ else 0 := by
    simpa only [hp, Function.comp_apply] using originalOverContractionEntry_pivot_block R e h i.as
  calc
    _ = originalOverContractionEntry R ι ν j
        (coordinateSelector ι ν j i.as) (coordinateSelector ι ν j, h) := by
      simpa only [Category.assoc] using hi.trans hc
    _ = if h = i.as then 𝟙 _ else 0 := hb
    _ = _ := by
      have hid : SheafOfModules.ιFree i.as ≫ 𝟙 (OriginalOverFree R ι ν j) ≫
          originalOverFreeProjection X U h = if i.as = h then 𝟙 _ else 0 :=
        (congrArg (fun t => SheafOfModules.ιFree i.as ≫ t)
          (Category.id_comp (originalOverFreeProjection X U h))).trans
            (originalOverFreeProjection_inclusion X U h i.as)
      apply Eq.trans _ hid.symm
      by_cases hih : h = i.as
      · simp [hih]
      · simp [hih, Ne.symm hih]

/-- The SAME actual original local factor has its actual native left inverse. -/
theorem originalOverPivotFactor_retraction :
    originalOverPivotFactor R ι ν (pivotIndex (coordinateSelector ι ν) e) ≫
      originalOverPivotRetraction R ι ν (pivotIndex (coordinateSelector ι ν) e) = 𝟙 _ := by
  change (originalOverPivotSection R ι ν _ ≫ originalOverContraction R ι ν _) ≫
    originalOverPivotRetraction R ι ν _ = _
  rw [Category.assoc]
  exact originalOverPivotSection_quotient R e

/-- The SAME actual native original global contraction has its whole original local factorization. -/
theorem originalOverPivotQuotient_factor :
    originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e) ≫
      originalOverPivotFactor R ι ν (pivotIndex (coordinateSelector ι ν) e) =
        originalOverContraction R ι ν (pivotIndex (coordinateSelector ι ν) e) := by
  let j := pivotIndex (coordinateSelector ι ν) e
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν j
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  let := originalOverFunctor_preservesColimits X U
  let := originalOverFunctor_preservesLimits X U
  have hp : coordinateSelector ι ν j = e ∘ Sum.inl :=
    (coordinateSelector ι ν).apply_symm_apply (e ∘ Sum.inl)
  apply originalOverFramedCoproductProduct_hom_ext X U (E := ι ⊕ ν)
    (S := (ι → ι ⊕ ν) × ι) (originalPositiveTwisting R ι ν) (originalGlobalCoordinateFrame R ι ν j)
  intro a row
  let l : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ OriginalOverSource R ι ν j :=
    F.map (SheafOfModules.ιFree a)
  let d := F.map (Pi.π (fun (_ : (ι → ι ⊕ ν) × ι) => originalPositiveTwisting R ι ν) row) ≫
    (originalGlobalCoordinateFrame R ι ν j).hom
  have hex := originalFiniteFree_expand (I := ι)
    l (originalOverPivotQuotient R ι ν j)
    (originalOverPivotFactor R ι ν j) d
    (originalOverFreeProjection X U) (fun i => SheafOfModules.ιFree i)
    (originalOverFreeProjection_sum X U ι)
  have hsum : (∑ i : ι,
      (l ≫ originalOverPivotQuotient R ι ν j ≫
        originalOverFreeProjection X U i) ≫
      (SheafOfModules.ιFree i ≫ originalOverPivotFactor R ι ν j ≫ d)) =
      ∑ i : ι, originalOverContractionEntry R ι ν j a (coordinateSelector ι ν j, i) ≫
        originalOverContractionEntry R ι ν j (coordinateSelector ι ν j i) row := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg₂ (fun b c : End (SheafOfModules.unit (X.ringCatSheaf.over U)) => b ≫ c)
      (originalOverPivotQuotient_coefficient R ι ν j a i)
      (originalOverPivotFactor_coefficient R ι ν j i row)
  have hf : originalOverContractionEntry R ι ν j a row =
      ∑ i : ι, originalOverContractionEntry R ι ν j a (coordinateSelector ι ν j, i) ≫
        originalOverContractionEntry R ι ν j (coordinateSelector ι ν j i) row := by
    have hscalar := originalOverContractionEntry_pivot_factor R e a row
    apply hscalar.trans
    apply Finset.sum_congr rfl
    intro i _
    simpa only [hp, Function.comp_apply] using originalActualOverUnitEnd_commute X U
      (originalOverContractionEntry R ι ν j (e (Sum.inl i)) row)
      (originalOverContractionEntry R ι ν j a (e ∘ Sum.inl, i))
  have hc : l ≫ originalOverContraction R ι ν j ≫ d =
      originalOverContractionEntry R ι ν j a row := by
    simp only [l, d, originalOverContraction, originalOverContractionEntry, Functor.map_comp,
      Category.assoc]
    rfl
  simp only [Category.assoc]
  exact (hex.trans (hsum.trans hf.symm)).trans hc.symm

instance originalOverPivotQuotient_isSplitEpi :
    IsSplitEpi (originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e)) :=
  ⟨⟨originalOverPivotSection R ι ν _, originalOverPivotSection_quotient R e⟩⟩

instance originalOverPivotFactor_isSplitMono :
    IsSplitMono (originalOverPivotFactor R ι ν (pivotIndex (coordinateSelector ι ν) e)) :=
  ⟨⟨originalOverPivotRetraction R ι ν _, originalOverPivotFactor_retraction R e⟩⟩

end Hironaka.Geometry.QuotGrassmann

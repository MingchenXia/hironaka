import DeJongAlterations.StableModification.LocalUniformization.GlobalNodeStage
import DeJongAlterations.StableModification.LocalUniformization.GlobalNormal

/-!
# Cofinality of strictly semi-stable modifications (Temkin, Proposition 4.3.1)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition
4.3.1 (`cofinprop`, `semi-stable.tex` lines 2956–3017): for a strictly semi-stable curve `C`
over a valuation ring `R` with separably closed fraction field, strictly semi-stable
modifications are cofinal among modifications. Blueprint chapter `sm-local-uniformization.tex`
(`prop:sm-cofinal`).

## Main results

* `centreClaim` (`lem:sm-cofinal-claim`, T:2967–3016): **Temkin's claim**
  `LocalUniformization.CentreClaim φ` (T43M's formulation), for `R = O` a valuation ring of a
  separably closed field `K` with `Spec O` finite and `C` integral, separated and strictly
  semi-stable of relative dimension one. Given a strictly semi-stable modification `C₁` and
  `𝔵 ∈ ⋃ Γ(C')` centred at a closed point `x₁` of `C₁`: either `x₁` is already generic in its
  fibre, or `C₁` has a chart at `x₁` over `B = 𝒪_𝔵 ∩ K` (`Blowups.exists_chart` for
  `X_B`, `isStrictlySemistable_baseRestrict`); a smooth chart, or a node chart off its origin, is
  handled by the smooth stage (`exists_smoothStep`), the origin of a node chart by the node stage
  (`exists_nodeStep`) followed by the smooth stage.
* `exists_dominates_isStrictlySemistable` (**`prop:sm-cofinal`**): every normal modification of
  `C` is dominated by a strictly semi-stable modification
  (`exists_dominates_isStrictlySemistable_of_finite` for modifications with finite `Γ₀`), with
  the normality of strictly semi-stable modifications supplied by
  `isNormalScheme_of_isStrictlySemistable_spec` (no hypothesis left).

## Hypotheses

The smoothness of the generic fibre in Temkin's statement is not used. The relative dimension
is the hypothesis `fiberTrdeg φ (genericPoint C) ≤ 1` (as in `ValCurves`), `C` is separated
(`ERRATA.md` DJA-T44), and `Spec O` is finite (`O` of finite height, the case of the de Jong
route; it makes `Spec (𝒪_𝔵 ∩ K) ⊆ Spec O` open, `GlobalBase`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open ValCurves RiemannZariskiSpace Curves Blowups Algebra.NodeBlowupChart
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]

/-- **Temkin's claim in the proof of Proposition 4.3.1** (`lem:sm-cofinal-claim`, T:2967–3016).
For an integral separated strictly semi-stable relative curve `C` over a valuation ring `O` of
finite height with separably closed fraction field, every point of `⋃ Γ(C')` centred at a closed
point of a strictly semi-stable modification `C₁` lies in `Γ(C₂)` for a strictly semi-stable
modification `C₂` dominating `C₁`. -/
theorem centreClaim {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated] (φ : C ⟶ Spec (.of O))
    (hC : IsStrictlySemistable φ ⊤) (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) :
    CentreClaim φ := by
  intro C₁ _ f₁ _ hss₁ V x₁ hVG hcl hVx
  have : DeJong.IsNodalCurve φ := hC.isNodalCurve
  let := functionFieldAlgebra φ
  have hK := genericPt_comp φ
  have htr : Algebra.trdeg K C.functionField ≤ 1 := (trdeg_functionField_eq φ).le.trans hdim
  -- the valuation and the base `B = 𝒪_𝔵 ∩ K`
  set vL := V.valuationSubring.valuation
  have hVeq : rzOf vL = V := rzOf_eq V
  rw [← hVeq] at hVx hVG ⊢
  have hq₁ : genericLift f₁ ≫ f₁ ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  have hOB := le_of_isCentre vL (f₁ ≫ φ) hq₁ hVx
  have hidx := asIdeal_eq_idealOfLE vL (f₁ ≫ φ) hq₁ hVx
  have hx' : x₁ ∈ baseOpen O _ hOB (f₁ ≫ φ) := (mem_baseOpen_iff O _ hOB (f₁ ≫ φ)).mpr hidx.le
  have hxc : baseRestrict O _ hOB (f₁ ≫ φ) ⟨x₁, hx'⟩ = closedPoint _ :=
    (baseRestrict_apply_eq_closedPoint_iff O _ hOB (f₁ ≫ φ) _).mpr (PrimeSpectrum.ext hidx)
  -- a transcendental residue, from `𝔵 ∈ Γ(C')`
  obtain ⟨C', _, f', _, y', hy'fib, hVy'⟩ := hVG
  have hq' : genericLift f' ≫ f' ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, hK]
  obtain ⟨t, ht⟩ := exists_transcendental_residue vL (le_of_isCentre vL (f' ≫ φ) hq' hVy')
    (f' ≫ φ) hq' hVy' (asIdeal_eq_idealOfLE vL (f' ≫ φ) hq' hVy')
    (by rw [hy'fib]; exact one_ne_zero)
  -- if the centre is generic in its fibre there is nothing to do
  have hdone : ∀ {C₂ : Scheme.{u}} [IsIntegral C₂] (f₂ : C₂ ⟶ C) [IsModification f₂]
      (g : C₂ ⟶ C₁), g ≫ f₁ = f₂ → IsStrictlySemistable (f₂ ≫ φ) ⊤ → ∀ y₂,
      IsCentre (genericLift f₂) (rzOf vL) y₂ → fiberTrdeg (f₂ ≫ φ) y₂ = 1 →
      ∃ (C₃ : Scheme.{u}) (_ : IsIntegral C₃) (f₃ : C₃ ⟶ C) (_ : IsModification f₃),
        (∃ g : C₃ ⟶ C₁, g ≫ f₁ = f₃) ∧ IsStrictlySemistable (f₃ ≫ φ) ⊤ ∧
          rzOf vL ∈ gammaSet (f₃ ≫ φ) (genericLift f₃) :=
    fun f₂ _ g hg hss₂ y₂ hV₂ hy₂ ↦
      ⟨_, inferInstance, f₂, inferInstance, ⟨g, hg⟩, hss₂, y₂, hy₂, hV₂⟩
  by_cases hgen : fiberTrdeg (f₁ ≫ φ) x₁ = 1
  · exact hdone f₁ (𝟙 _) (Category.id_comp _) hss₁ x₁ hVx hgen
  have h0 : fiberTrdeg (f₁ ≫ φ) x₁ = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f₁ x₁) hgen
  -- the smooth stage, for a smooth chart at a closed point of a strictly semi-stable modification
  have hsmooth : ∀ {C₂ : Scheme.{u}} [IsIntegral C₂] (f₂ : C₂ ⟶ C) [IsModification f₂]
      (g : C₂ ⟶ C₁), g ≫ f₁ = f₂ → IsStrictlySemistable (f₂ ≫ φ) ⊤ → ∀ {y₂ : C₂},
      IsClosed ({y₂} : Set C₂) → IsCentre (genericLift f₂) (rzOf vL) y₂ →
      fiberTrdeg (f₂ ≫ φ) y₂ = 0 → ∀ (hy : y₂ ∈ baseOpen O _ hOB (f₂ ≫ φ)),
      baseRestrict O _ hOB (f₂ ≫ φ) ⟨y₂, hy⟩ = closedPoint _ →
      HasSmoothChart (baseRestrict O _ hOB (f₂ ≫ φ)) ⟨y₂, hy⟩ →
      ∃ (C₃ : Scheme.{u}) (_ : IsIntegral C₃) (f₃ : C₃ ⟶ C) (_ : IsModification f₃),
        (∃ g : C₃ ⟶ C₁, g ≫ f₁ = f₃) ∧ IsStrictlySemistable (f₃ ≫ φ) ⊤ ∧
          rzOf vL ∈ gammaSet (f₃ ≫ φ) (genericLift f₃) := by
    intro C₂ _ f₂ _ g hg hss₂ y₂ hcl₂ hV₂ h0₂ hy hyc hch
    obtain ⟨C₃, _, f₃, _, ⟨g', hg'⟩, hss₃, hV₃⟩ :=
      exists_smoothStep φ hK hdim vL htr ht hOB f₂ hss₂ hcl₂ hV₂ h0₂ hy hyc hch
    exact ⟨C₃, inferInstance, f₃, inferInstance, ⟨g' ≫ g, by rw [Category.assoc, hg, hg']⟩,
      hss₃, hV₃⟩
  -- a chart at `x₁` over `B`
  have hss₁' := isStrictlySemistable_baseRestrict O _ hOB (f₁ ≫ φ) hss₁
  obtain ⟨U, hxU, hcase⟩ := exists_chart hss₁' ⟨x₁, hx'⟩ hxc
  rcases hcase with ⟨e, he, hecomp⟩ | ⟨c, e, he, hecomp⟩
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hcl hVx h0 hx' hxc
      (hasSmoothChart_of_etale _ U e hecomp _ hxU)
  have hcoord : ∀ i : Fin 2, coordinate c i ∉ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal →
      HasSmoothChart (baseRestrict O _ hOB (f₁ ≫ φ)) ⟨x₁, hx'⟩ := fun i hi ↦
    hasSmoothChart_of_node (baseRestrict O _ hOB (f₁ ≫ φ)) U.ι c e hecomp ⟨⟨x₁, hx'⟩, hxU⟩ i hi
  by_cases hu : coordinate c 0 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal
  swap
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hcl hVx h0 hx' hxc (hcoord 0 hu)
  by_cases hv : coordinate c 1 ∈ (e ⟨⟨x₁, hx'⟩, hxU⟩).asIdeal
  swap
  · exact hsmooth f₁ (𝟙 _) (Category.id_comp _) hss₁ hcl hVx h0 hx' hxc (hcoord 1 hv)
  -- the origin of a node chart: the node stage, then the smooth stage
  have : Nonempty (baseOpen O _ hOB (f₁ ≫ φ)).toScheme := ⟨⟨x₁, hx'⟩⟩
  have : IsIntegral (baseOpen O _ hOB (f₁ ≫ φ)).toScheme :=
    isIntegral_of_isOpenImmersion (baseOpen O _ hOB (f₁ ≫ φ)).ι
  have : Nonempty U.toScheme := ⟨⟨⟨x₁, hx'⟩, hxU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsDomain (U.toScheme.presheaf.stalk ⟨⟨x₁, hx'⟩, hxU⟩) :=
    AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral (X := U.toScheme)
  have hc : c ≠ 0 := node_param_ne_zero c e ⟨⟨x₁, hx'⟩, hxU⟩ hu hv
  obtain ⟨C₂, _, f₂, _, g, _, hg, hss₂, y₂, hV₂, hgy₂, hy₂, hch⟩ :=
    exists_nodeStep φ hK vL htr ht hOB f₁ hss₁ hcl hVx hx' hxc U hxU hc e hecomp hu hv
  have : IsSeparated (f₂ ≫ φ) := inferInstance
  by_cases hgen₂ : fiberTrdeg (f₂ ≫ φ) y₂ = 1
  · exact hdone f₂ g hg hss₂ y₂ hV₂ hgen₂
  have hdim₁ : fiberTrdeg (f₁ ≫ φ) (genericPoint C₁) ≤ 1 := fiberTrdeg_le_one φ hdim f₁ _
  have hcl₂ : IsClosed ({y₂} : Set C₂) := by
    rcases mem_fibreGenericSet_or_isClosed (φ := f₁ ≫ φ) hdim₁ g (x₁ := y₂)
        (by rw [hgy₂]; exact hcl) with h | h
    · exfalso
      apply hgen₂
      have h' : fiberTrdeg (g ≫ f₁ ≫ φ) y₂ = 1 := h
      rwa [← Category.assoc, hg] at h'
    · exact h
  have h0₂ : fiberTrdeg (f₂ ≫ φ) y₂ = 0 :=
    Cardinal.eq_zero_of_le_one_of_ne_one (fiberTrdeg_le_one φ hdim f₂ y₂) hgen₂
  have hyc : baseRestrict O _ hOB (f₂ ≫ φ) ⟨y₂, hy₂⟩ = closedPoint _ := by
    rw [baseRestrict_apply_eq_closedPoint_iff]
    change (f₂ ≫ φ) y₂ = _
    rw [← hg, Category.assoc, Scheme.Hom.comp_apply, hgy₂]
    exact (baseRestrict_apply_eq_closedPoint_iff O _ hOB (f₁ ≫ φ) _).mp hxc
  exact hsmooth f₂ g hg hss₂ hcl₂ hV₂ h0₂ hy₂ hyc hch

/-- **Proposition 4.3.1 for modifications with finite `Γ₀`** (`prop:sm-cofinal`, general form):
every modification `C' → C` with `Γ₀(C')` finite is dominated by a strictly semi-stable
modification. -/
theorem exists_dominates_isStrictlySemistable_of_finite {C : Scheme.{u}} [IsIntegral C]
    [CompactSpace C] [C.IsSeparated] (φ : C ⟶ Spec (.of O)) (hC : IsStrictlySemistable φ ⊤)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {C' : Scheme.{u}} [IsIntegral C'] (f' : C' ⟶ C)
    [IsModification f'] (hfin : (gammaZeroSet (f' ≫ φ) (genericLift f') (genericPt C)).Finite) :
    ∃ (C'' : Scheme.{u}) (_ : IsIntegral C'') (f'' : C'' ⟶ C) (_ : IsModification f''),
      IsStrictlySemistable (f'' ≫ φ) ⊤ ∧ ∃ g : C'' ⟶ C', g ≫ f' = f'' :=
  exists_dominates_of_finite_gammaZeroSet hdim hC
    (fun _ _ _ _ hss ↦ isNormalScheme_of_isStrictlySemistable_spec hss) (centreClaim φ hC hdim) f'
    hfin

/-- **Temkin, Proposition 4.3.1** (`prop:sm-cofinal`; `cofinprop`, T:2956–3017, in the form of
`ERRATA.md` T41 and DJA-O3): let `O` be a valuation ring of finite height with separably closed
fraction field and `C → Spec O` an integral, quasi-compact, separated, strictly semi-stable
relative curve. Then every normal modification `C' → C` is dominated by a strictly semi-stable
modification of `C`. -/
theorem exists_dominates_isStrictlySemistable {C : Scheme.{u}} [IsIntegral C] [CompactSpace C]
    [C.IsSeparated] (φ : C ⟶ Spec (.of O)) (hC : IsStrictlySemistable φ ⊤)
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) {C' : Scheme.{u}} [IsIntegral C'] (f' : C' ⟶ C)
    [IsModification f'] (hC' : IsNormalScheme C') :
    ∃ (C'' : Scheme.{u}) (_ : IsIntegral C'') (f'' : C'' ⟶ C) (_ : IsModification f''),
      IsStrictlySemistable (f'' ≫ φ) ⊤ ∧ ∃ g : C'' ⟶ C', g ≫ f' = f'' := by
  have : DeJong.IsNodalCurve φ := hC.isNodalCurve
  have : Finite (Spec (.of O)) := inferInstanceAs (Finite (PrimeSpectrum O))
  have : QuasiCompact φ := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹_›
  exact exists_dominates_of_isNormalScheme hdim hC
    (fun _ _ _ _ hss ↦ isNormalScheme_of_isStrictlySemistable_spec hss) (centreClaim φ hC hdim) f'
    hC'

end DeJongAlterations.StableModification.LocalUniformization

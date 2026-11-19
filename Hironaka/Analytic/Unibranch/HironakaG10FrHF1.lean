import Hironaka.Analytic.Unibranch.HironakaG10FrNativeIV9
import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertTheorem
import Hironaka.Analytic.Unibranch.HironakaG10RdFinal
import Hironaka.Analytic.Unibranch.HironakaG10GfFinal

/-!
# hF1: the relative non-flat set is analytic (ASM step 4, the hF1 splice)

Frisch's Th. (IV,9) for reduced complex spaces (`HironakaG10FrNativeIV9.isAnalyticSubset_relNonflatSource`: the
source non-flat locus `N_A` of the fibre-product family over the reduced structure of `A` is analytic in `Y`) and
Remmert's proper mapping theorem for reduced complex spaces
(`HironakaG10MwRemmertTheorem.isAnalyticSubset_image_of_isProperMap`) give, for a proper `f : Y ⟶ X` and analytic
`A ⊆ X`, that `relNonflat f A = f (N_A)` is analytic (**`isAnalyticSubset_relNonflat`**), i.e. lane G10RD's input
`hF1` of `HironakaG10RdFinal.hironakaFlattening_of_frisch` (**`hF1_of_hGF`**), and
**`hironakaFlattening_of_hGF`**: Hironaka's flattening theorem from `hT` and generic flatness at a fixed fibre
point `hGF` (Frisch Th. (II,1) (i)+(ii); lane G10GN) — the only remaining input of the Frisch route:

* the chart local criterion of flatness (item 1) is discharged by lane G10GF's
  `HironakaG10GfFinal.chartFlat_baseIdeal_iff_fibreExactAt` (lane G10LF's `chartFlat_iff_fibreExactAt`);
* `hF2` (Frisch Prop. (IV,14)) is lane G10GF's `HironakaG10GfFinal.hF2_stage`.

No named `Prop`.  Lane G10R3 (continuing lane G10FR), run 0081.  Blueprint: `hironaka-g10fr-hf1.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10FrHF1

open Hironaka Hironaka OkaRelationSheaf
  HironakaG10LocFibreOpen HironakaG10LocRelative HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10RdLemma455
  Hironaka.Analytic.Unibranch.HironakaG10RdTheoremI
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdEndToEnd
  Hironaka.Analytic.Unibranch.HironakaG10EpS3
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover
  Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily Hironaka.Analytic.Unibranch.HironakaG10FrRouteG
  Hironaka.Analytic.Unibranch.HironakaG10GfModStart Hironaka.Analytic.Unibranch.HironakaG10FrNativeIV9

noncomputable section

/-- **Frisch's Theorem (IV,9) for reduced complex spaces, item 1 discharged**: the source non-flat locus of the
fibre-product family over an analytic `A` is analytic, from generic flatness `hGF` alone. -/
theorem isAnalyticSubset_relNonflatSource_of_hGF
    (hGF : ∀ (m t : ℕ) (p₀ : ComplexModel m) (P : Set (ComplexModel m)), IsAnalyticNear P p₀ → p₀ ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, (0 : ComplexModel t)) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p 0)
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) {A : Set X.obj.left} (hA : X.IsAnalyticSubset A) :
    Y.IsAnalyticSubset (relNonflatSource f A) :=
  isAnalyticSubset_relNonflatSource HironakaG10GfFinal.chartFlat_baseIdeal_iff_fibreExactAt hGF f hA

/-- **The relative non-flat set of an analytic set under a proper morphism is analytic** (Frisch Th. (IV,9) +
Remmert), from generic flatness `hGF` alone. -/
theorem isAnalyticSubset_relNonflat
    (hGF : ∀ (m t : ℕ) (p₀ : ComplexModel m) (P : Set (ComplexModel m)), IsAnalyticNear P p₀ → p₀ ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, (0 : ComplexModel t)) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p 0)
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    {A : Set X.obj.left} (hA : X.IsAnalyticSubset A) :
    X.IsAnalyticSubset (relNonflat f A) := by
  rw [relNonflat_eq_image]
  exact HironakaG10MwRemmertTheorem.isAnalyticSubset_image_of_isProperMap f hf
    (isAnalyticSubset_relNonflatSource_of_hGF hGF f hA)

/-- **`hF1`** in exactly the shape consumed by `HironakaG10RdFinal.hironakaFlattening_of_frisch`. -/
theorem hF1_of_hGF
    (hGF : ∀ (m t : ℕ) (p₀ : ComplexModel m) (P : Set (ComplexModel m)), IsAnalyticNear P p₀ → p₀ ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, (0 : ComplexModel t)) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p 0) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A) :=
  fun s _ hp _ hA => isAnalyticSubset_relNonflat hGF s.f hp hA

/-- **Hironaka's flattening theorem from `hT` and generic flatness `hGF`** (`hF1` by the Frisch route above, `hF2`
by lane G10GF's `HironakaG10GfFinal.hF2_stage`). -/
theorem hironakaFlattening_of_hGF
    (hGF : ∀ (m t : ℕ) (p₀ : ComplexModel m) (P : Set (ComplexModel m)), IsAnalyticNear P p₀ → p₀ ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, (0 : ComplexModel t)) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p 0)
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z) :
    HironakaFlattening :=
  HironakaG10RdFinal.hironakaFlattening_of_frisch (hF1_of_hGF hGF) HironakaG10GfFinal.hF2_stage hT

end

end Hironaka.Analytic.Unibranch.HironakaG10FrHF1

import Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
import Hironaka.Resolution.HironakaG10PNKernelSquare
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-!
# Restricting a chart square and translating the parameter family (G10-01-10/11 support)

Lane G10MW, run 0081.

* `exists_restricted_square`: from an actual chart square `(eX, e, φ)` of an ordinary morphism and an
  open `O` of the base ambient, the square of the RESTRICTED charts `eX.restrict O` and
  `e.restrict T`, `T = φ⁻¹(O)`, with the restricted lift.  Uses only uniqueness of reduced-subspace maps
  over the complex point with the same base map.
* `translate`, `actualStalkChartEquiv_translate`: the translation `u ↦ u − c` between open subsets of
  `ℂ^d` acts as the identity on translated chart germs.
* `ambientFamily`, `map_ambientFamily`, `isLocallyFinitelyGeneratedAt_ambientFamily`: the parameter
  family of chart window criteria (centred at `0`), pulled to the open `O ⊆ c + U` of the base
  ambient by the translation: at `u` its chart image is the criterion ideal at `u − c`, and it is
  locally finitely generated.

No named input.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10MwChartRestriction

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaHolomorphicJetRankLoci
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceLocalFunctions HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaG10LocSectionNoether
  HironakaG10PNIdealFamily HironakaG10PNKernelSquare
  Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily

/-! ### Restricting both charts of a chart square -/

/-- **The restricted chart square.** -/
theorem exists_restricted_square {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (eX : LocalEmbedding X) (e : LocalEmbedding Y) (φ : e.ambient → eX.ambient)
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ φ)
    (hCD : ∀ z ∈ e.carrier, φ z ∈ eX.carrier)
    (hsq : actualSubspaceMap hφ hCD ≫ eX.map = e.map ≫ f.hom.left)
    (O : Opens (ComplexModel eX.dim)) (hO : O ≤ eX.ambient) :
    ∃ (T : Opens (ComplexModel e.dim)) (hT : T ≤ e.ambient) (φ' : T → O)
      (hφ' : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ φ')
      (hCD' : ∀ z ∈ (e.restrict T hT).carrier, φ' z ∈ (eX.restrict O hO).carrier),
      (∀ z : T, (φ' z).val = (φ (Opens.inclusion hT z)).val) ∧
      (∀ z (hz : z ∈ e.ambient), (φ ⟨z, hz⟩).val ∈ O → z ∈ T) ∧
      actualSubspaceMap hφ' hCD' ≫ (eX.restrict O hO).map = (e.restrict T hT).map ≫ f.hom.left := by
  let P : Set e.ambient := φ ⁻¹' {v | v.val ∈ O}
  have hP : IsOpen P := (O.isOpen.preimage continuous_subtype_val).preimage hφ.continuous
  let T : Opens (ComplexModel e.dim) := ⟨Subtype.val '' P, e.ambient.isOpen.isOpenMap_subtype_val P hP⟩
  have hT : T ≤ e.ambient := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hφT : ∀ z : T, (φ (Opens.inclusion hT z)).val ∈ O := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    exact hw
  let φ' : T → O := fun z => ⟨(φ (Opens.inclusion hT z)).val, hφT z⟩
  have hφ' : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ φ' := by
    apply (ContMDiff.subtypeVal_comp_iff O φ').mp
    have h : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞
        (Subtype.val ∘ (φ ∘ Opens.inclusion hT)) :=
      contMDiff_subtype_val.comp (hφ.comp (contMDiff_inclusion hT))
    exact h
  have hCD' : ∀ z ∈ (e.restrict T hT).carrier, φ' z ∈ (eX.restrict O hO).carrier := by
    intro z hz
    change Opens.inclusion hO (φ' z) ∈ eX.carrier
    have h := hCD (Opens.inclusion hT z) hz
    have heq : Opens.inclusion hO (φ' z) = φ (Opens.inclusion hT z) := Subtype.ext rfl
    rw [heq]
    exact h
  refine ⟨T, hT, φ', hφ', hCD', fun z => rfl, fun z hz hzO => ⟨⟨z, hz⟩, hzO, rfl⟩, ?_⟩
  -- the square of models, by uniqueness over the complex point
  have hmodel : actualSubspaceMap hφ' hCD' ≫
        eX.restrictModelMapWith O hO (eX.restrictCarrier O hO) (fun _ => Iff.rfl) =
      e.restrictModelMapWith T hT (e.restrictCarrier T hT) (fun _ => Iff.rfl) ≫
        actualSubspaceMap hφ hCD := by
    apply actualSubspaceMap_eq_of_base_eq
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (actualSubspaceMap hφ' hCD' ≫ ·)
        (eX.restrictModelMapWith_over O hO (eX.restrictCarrier O hO) (fun _ => Iff.rfl))).trans ?_
      exact actualSubspaceMap_point hφ' hCD'
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (e.restrictModelMapWith T hT (e.restrictCarrier T hT) (fun _ => Iff.rfl) ≫ ·)
        (actualSubspaceMap_point hφ hCD)).trans ?_
      exact e.restrictModelMapWith_over T hT _ _
    · ext z
      rfl
  have h1 : actualSubspaceMap hφ' hCD' ≫ (eX.restrict O hO).map =
      (actualSubspaceMap hφ' hCD' ≫
        eX.restrictModelMapWith O hO (eX.restrictCarrier O hO) (fun _ => Iff.rfl)) ≫ eX.map :=
    (Category.assoc _ _ _).symm
  have h2 : (e.restrict T hT).map ≫ f.hom.left =
      e.restrictModelMapWith T hT (e.restrictCarrier T hT) (fun _ => Iff.rfl) ≫
        (e.map ≫ f.hom.left) :=
    Category.assoc _ _ _
  exact h1.trans ((congrArg (· ≫ eX.map) hmodel).trans ((Category.assoc _ _ _).trans
    ((congrArg (e.restrictModelMapWith T hT (e.restrictCarrier T hT) (fun _ => Iff.rfl) ≫ ·)
      hsq).trans h2.symm)))

/-! ### Whole vanishing stalk ideals under restriction of the source ambient -/

/-- The whole vanishing stalk ideal of a carrier is unchanged by restricting the ambient open: both are
the vanishing stalk ideal of its image in `ℂ^m` at the same point. -/
theorem wholeChartStalkIdeal_vanishing_restrict {m : ℕ} {U T : Opens (ComplexModel m)} (hT : T ≤ U)
    (C : Set U) (z : T) :
    wholeChartStalkIdeal (vanishingIdeal (n := m) (Opens.inclusion hT ⁻¹' C)) z z (mem_chart_source _ z) =
      wholeChartStalkIdeal (vanishingIdeal (n := m) C) (Opens.inclusion hT z) (Opens.inclusion hT z)
        (mem_chart_source _ (Opens.inclusion hT z)) := by
  let Ĉ : Set (ComplexModel m) := Subtype.val '' C
  have hU : C = (Subtype.val : U → ComplexModel m) ⁻¹' Ĉ :=
    (Set.preimage_image_eq C Subtype.val_injective).symm
  have hT' : Opens.inclusion hT ⁻¹' C = (Subtype.val : T → ComplexModel m) ⁻¹' Ĉ := by
    ext w
    constructor
    · intro hw
      exact ⟨Opens.inclusion hT w, hw, rfl⟩
    · rintro ⟨v, hv, hvw⟩
      have : v = Opens.inclusion hT w := Subtype.ext hvw
      show Opens.inclusion hT w ∈ C
      rw [← this]
      exact hv
  rw [hT', hU, HironakaActualVanishingIntrinsicHSTransport.wholeChartStalkIdeal_vanishing_actual_open
      (n := m) T Ĉ z,
    HironakaActualVanishingIntrinsicHSTransport.wholeChartStalkIdeal_vanishing_actual_open
      (n := m) U Ĉ (Opens.inclusion hT z)]

/-! ### Translating the parameter family -/

variable {d : ℕ}

/-- The translation `u ↦ u − c` from an open set `O ⊆ c + U` to `U`. -/
def translate (O U : Opens (ComplexModel d)) (c : ComplexModel d) (h : ∀ u ∈ O, u - c ∈ U) : O → U :=
  fun u => ⟨u.val - c, h u.val u.property⟩

theorem translate_contMDiff (O U : Opens (ComplexModel d)) (c : ComplexModel d)
    (h : ∀ u ∈ O, u - c ∈ U) :
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ (translate O U c h) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  have h1 : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (fun v : ComplexModel d => v - c) :=
    (contDiff_id.sub contDiff_const).contMDiff
  exact h1.comp contMDiff_subtype_val

/-- The translation acts as the identity on translated chart germs. -/
theorem actualTranslatedMap_translate_eventually (O U : Opens (ComplexModel d)) (c : ComplexModel d)
    (h : ∀ u ∈ O, u - c ∈ U) (u : O) :
    actualTranslatedMap (n := d) (m := d) (translate O U c h) u =ᶠ[𝓝 (0 : ComplexModel d)] id := by
  have hO : ∀ᶠ w in 𝓝 (0 : ComplexModel d), u.val + w ∈ O :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa only [Pi.add_apply, Function.id_def, add_zero] using O.isOpen.mem_nhds u.property)
  filter_upwards [hO] with w hw
  have hap := HironakaG10FlatOrdinaryPointFlattener.actualTranslatedMap_open_apply
    (M := ComplexModel d) (O := O) (translate O U c h) u.val (u.val + w) u.property hw
    (by rw [chartAt_self_eq]; trivial)
  have hl : (chartAt (ComplexModel d) u.val) (u.val + w) - (chartAt (ComplexModel d) u.val) u.val = w := by
    change (u.val + w) - u.val = w
    abel
  rw [hl] at hap
  refine hap.trans ?_
  change ((u.val + w) - c) - (u.val - c) = w
  abel

theorem actualHolomorphicGermPullback_translate (O U : Opens (ComplexModel d)) (c : ComplexModel d)
    (h : ∀ u ∈ O, u - c ∈ U) (u : O) :
    actualHolomorphicGermPullback (translate_contMDiff O U c h) u = AlgHom.id ℂ _ := by
  apply AlgHom.ext
  intro a
  induction a using HolGerm.induction_on with
  | h F hF =>
    change actualHolomorphicGermPullback (translate_contMDiff O U c h) u (HolGerm.mk F hF) =
      HolGerm.mk F hF
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (actualTranslatedMap_translate_eventually O U c h u).mono (fun z hz => congrArg F hz)

/-- **Translation and chart germs.** -/
theorem actualStalkChartEquiv_translate (O U : Opens (ComplexModel d)) (c : ComplexModel d)
    (h : ∀ u ∈ O, u - c ∈ U) (u : O)
    (r : actualComplexStructureStalk (n := d) (translate O U c h u)) :
    actualStalkChartEquiv (n := d) u
        ((ChartedSpace.locallyRingedSpaceMap (translate O U c h) (translate_contMDiff O U c h)).stalkMap
          u r) =
      actualStalkChartEquiv (n := d) (translate O U c h u) r := by
  rw [actualNativeStalk_chart_pullback, actualHolomorphicGermPullback_translate]
  rfl

/-! ### The parameter family on the base ambient -/

variable {t a b : ℕ} {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
  {K : Set (ComplexModel t)}

/-- The parameter family of chart criteria, pulled to `O ⊆ c + U` by the translation. -/
def ambientFamily (crit : ChartWindowCriteria d t F K) (O : Opens (ComplexModel d)) (c : ComplexModel d)
    (h : ∀ u ∈ O, u - c ∈ crit.U) :
    ∀ u : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) O,
      Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) O).presheaf.stalk u) :=
  pullFamily (ChartedSpace.locallyRingedSpaceMap (translate O crit.U c h) (translate_contMDiff O crit.U c h))
    (spanFamily crit.s univ)

/-- At every point, the chart image of the pulled family is the criterion ideal at `u − c`. -/
theorem map_ambientFamily (crit : ChartWindowCriteria d t F K) (O : Opens (ComplexModel d))
    (c : ComplexModel d) (h : ∀ u ∈ O, u - c ∈ crit.U) (u : O) :
    Ideal.map (actualStalkChartEquiv (n := d) u).toRingHom (ambientFamily crit O c h u) =
      Ideal.map (actualStalkChartEquiv (n := d) (translate O crit.U c h u)).toRingHom
        (spanFamily crit.s univ (translate O crit.U c h u)) := by
  unfold ambientFamily pullFamily
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun r => actualStalkChartEquiv_translate O crit.U c h u r

/-- The pulled family is locally finitely generated at every point. -/
theorem isLocallyFinitelyGeneratedAt_ambientFamily (crit : ChartWindowCriteria d t F K)
    (O : Opens (ComplexModel d)) (c : ComplexModel d) (h : ∀ u ∈ O, u - c ∈ crit.U) (u : O) :
    IsLocallyFinitelyGeneratedAt (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) O)
      (ambientFamily crit O c h) u := by
  apply IsLocallyFinitelyGeneratedAt.pull
  obtain ⟨T, hT⟩ := crit.finite_near (translate O crit.U c h u)
  obtain ⟨tt, htt, hto, hpt⟩ := eventually_nhds_iff.1 hT
  have hfin := isLocallyFinitelyGenerated_spanFamily crit.s T (translate O crit.U c h u)
  exact IsLocallyFinitelyGeneratedAt.congr hfin ⟨tt, hto⟩ hpt fun y hy => (htt y hy).symm

end

end Hironaka.Analytic.Unibranch.HironakaG10MwChartRestriction

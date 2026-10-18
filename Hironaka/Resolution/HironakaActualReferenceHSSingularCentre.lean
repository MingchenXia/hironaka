/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel
import Hironaka.Resolution.HironakaRelativeNormalActualBaseJetDimension
import Hironaka.Resolution.HironakaHilbertSamuelTangentValue
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaSharpOriginalDeepProductBlowup

/-! Actual whole original HS reference loci give a first singular centre with the whole original boundary. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualReferenceHSSingularCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaHolomorphicPointJets
  HironakaRelativeNormalActualBaseJetDimension HironakaActualWholeAmbientHSSuperlevel
  AnalyticDimensionBasics Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  BlowupTowers BlowupTowerTransforms ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The genuine order-zero quotient has dimension one exactly for a proper original local ideal. -/
theorem actualLocalHilbertSamuel_zero (I : Ideal (HolGerm (ComplexModel n))) :
    hilbertSamuelValue I 0 = if I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) then 1 else 0 := by
  classical
  by_cases hI : I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))
  · rw [if_pos hI]
    change Module.finrank ℂ (HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (1 : ℕ))) = 1
    rw [pow_one,sup_eq_right.mpr hI]
    have hb := actualBaseJetDimension n 0
    change Module.finrank ℂ (HolGerm (ComplexModel n) ⧸
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (1 : ℕ)) = n.choose n at hb
    rw [pow_one,Nat.choose_self] at hb
    exact hb
  · rw [if_neg hI]
    have htop : I = ⊤ := by
      by_contra hne
      exact hI (IsLocalRing.le_maximalIdeal hne)
    unfold hilbertSamuelValue
    rw [htop,top_sup_eq]
    exact Module.finrank_zero_of_subsingleton

/-- BOTH original whole-stalk maximal-ideal directions use every actual original membership germ. -/
theorem wholeChartStalk_le_maximal_iff_support (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    wholeChartStalkIdeal A y y (mem_chart_source _ y) ≤
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ↔ y ∈ A.zeroLocus := by
  constructor
  · intro hle f hf
    have hh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA hf
    have hg := hle (Ideal.subset_span ⟨f,hh,hf,rfl⟩)
    have he := (HolGerm.mem_maximalIdeal_iff _).mp hg
    simpa [chartTranslatedGerm,HironakaHolomorphicJetRankLoci.translatedGerm,HolGerm.eval_mk,
      (chartAt (ComplexModel n) y).left_inv (mem_chart_source _ y)] using he
  · intro hy
    apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hmem,rfl⟩
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    simpa [chartTranslatedGerm,HironakaHolomorphicJetRankLoci.translatedGerm,HolGerm.eval_mk,
      (chartAt (ComplexModel n) y).left_inv (mem_chart_source _ y)] using hy f hmem

/-- The SAME existing intrinsic original order-zero HS value detects the ENTIRE original support. -/
theorem hilbertSamuelAt_zero_eq_support (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    hilbertSamuelAt A y 0 = if y ∈ A.zeroLocus then 1 else 0 := by
  rw [hilbertSamuelAt,actualLocalHilbertSamuel_zero,
    wholeChartStalk_le_maximal_iff_support A hA y]

/-- The true original order-zero support dictionary is an equivalence, without a caller certificate. -/
theorem one_le_hilbertSamuelAt_zero_iff (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    1 ≤ hilbertSamuelAt A y 0 ↔ y ∈ A.zeroLocus := by
  rw [hilbertSamuelAt_zero_eq_support A hA y]
  split_ifs <;> simp_all

/-- The literal whole original reference HS locus uses the EXISTING intrinsic function at every order. -/
def actualReferenceHSLocus (A : GermIdeal n M) (a : M) : Set M :=
  actualWholeAmbientHSSuperlevel A (hilbertSamuelAt A a)

/-- ONLY original current geometry puts the SAME true reference locus inside the CURRENT singular set. -/
theorem actualReferenceHSLocus_subset_current_singular {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) {a : M} (ha : a ∈ W \ regularLocus (n := n) W d) :
    actualReferenceHSLocus (vanishingIdeal (n := n) W) a ⊆ W \ regularLocus (n := n) W d := by
  let A := vanishingIdeal (n := n) W
  have hA : A.IsCoherent := CartanIrreducible.cartanCoherence W hW
  have hz : A.zeroLocus = W := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW.isClosed
  have hsing := HironakaHilbertSamuelTangentValue.singularLocus_eq_first_hilbertSamuel_superlevel hW hd hpure
  have ha1 : d+2 ≤ hilbertSamuelAt A a 1 := ((Set.ext_iff.mp hsing a).mp ha).2
  have ha0 : 1 ≤ hilbertSamuelAt A a 0 := (one_le_hilbertSamuelAt_zero_iff A hA a).mpr (hz.symm ▸ ha.1)
  intro y hy
  have hyW : y ∈ W := hz ▸ (one_le_hilbertSamuelAt_zero_iff A hA y).mp (ha0.trans (hy 0))
  exact (Set.ext_iff.mp hsing y).mpr ⟨hyW,ha1.trans (hy 1)⟩

/-- The SAME singular reference INTERNALLY produces a genuine nonempty analytic compact whole HS locus. -/
theorem actualReferenceHSLocus_current_geometry {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) {a : M} (ha : a ∈ W \ regularLocus (n := n) W d) :
    (actualReferenceHSLocus (vanishingIdeal (n := n) W) a).Nonempty ∧
    IsComplexAnalyticSubset (n := n) (actualReferenceHSLocus (vanishingIdeal (n := n) W) a) ∧
    IsCompact (actualReferenceHSLocus (vanishingIdeal (n := n) W) a) ∧
    actualReferenceHSLocus (vanishingIdeal (n := n) W) a ⊆ W \ regularLocus (n := n) W d := by
  have hSa := isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel
    (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW)
    (hilbertSamuelAt (vanishingIdeal (n := n) W) a)
  have hsub := actualReferenceHSLocus_subset_current_singular hW hd hpure ha
  exact ⟨⟨a,fun _ => le_rfl⟩,hSa,hK.of_isClosed_subset hSa.isClosed
    (fun _ hy => (hsub hy).1),hsub⟩

/-- The SAME actual whole reference locus and the ENTIRE original ordered boundary form a literal marked input. -/
def actualReferenceHSMarked (W : Set M) (E : List (Set M)) (a : M) : MarkedIdeal n M :=
  ⟨univ,E,vanishingIdeal (n := n) (actualReferenceHSLocus (vanishingIdeal (n := n) W) a),1⟩

/-- Original purity of smaller dimension INTERNALLY gives actual ambient thinness. -/
theorem currentPure_interior_empty {W : Set M} {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) : interior W = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hr : RegularAtDim (n := n) W x n := EmbeddedFromResolution.regularAtDim_of_mem_nhds
    (mem_interior_iff_mem_nhds.mp hx)
  have he := hpure x n hr
  omega

/-- ONLY original geometry constructs ALL domain fields for the same whole HS ideal and unchanged boundary. -/
theorem actualReferenceHSMarked_isInvDomain {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) {E : List (Set M)} (hE : IsSNCDivisor n E)
    {a : M} (ha : a ∈ W \ regularLocus (n := n) W d) :
    IsInvDomain n (actualReferenceHSMarked (n := n) W E a) := by
  have hSa := isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel
    (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW)
    (hilbertSamuelAt (vanishingIdeal (n := n) W) a)
  have hsub := actualReferenceHSLocus_subset_current_singular hW hd.le hpure ha
  have hint : interior (actualReferenceHSLocus (vanishingIdeal (n := n) W) a) = ∅ :=
    eq_empty_of_subset_empty ((interior_mono (fun _ hy => (hsub hy).1)).trans
      (currentPure_interior_empty hd hpure).subset)
  exact HironakaEmbeddedBoundary.isInvDomain_boundary hSa hint hE

/-- The literal auxiliary cosupport is the ENTIRE genuine original all-order reference locus. -/
theorem actualReferenceHSMarked_cosupp {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (E : List (Set M)) (a : M) :
    (actualReferenceHSMarked (n := n) W E a).cosupp = actualReferenceHSLocus (vanishingIdeal (n := n) W) a := by
  have hSa := isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel
    (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW)
    (hilbertSamuelAt (vanishingIdeal (n := n) W) a)
  exact HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hSa.isClosed E

/-- Original nonsmooth current geometry INTERNALLY chooses a singular reference and a true SAME-boundary centre. -/
theorem exists_actual_current_full_hs_singular_first_centre {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∃ (a : X) (C : Set X), a ∈ W \ regularLocus (n := n) W d ∧ C.Nonempty ∧
      C ⊆ actualReferenceHSLocus (vanishingIdeal (n := n) W) a ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C = maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) W E a) (.refl : BlowupTower X X))
        (actualReferenceHSMarked (n := n) W E a).cosupp := by
  have hne : (W \ regularLocus (n := n) W d).Nonempty := by
    by_contra hempty
    apply hns
    refine ⟨hW.isClosed,fun x hx => ⟨d,?_⟩⟩
    by_contra hr
    exact hempty ⟨x,hx,hr⟩
  obtain ⟨a,ha⟩ := hne
  let M := actualReferenceHSMarked (n := n) W E a
  let R := CanonicalCentres.canonicalInvariant.{u} n
  have hdom : IsInvDomain n M := actualReferenceHSMarked_isInvDomain hW hd hpure hE ha
  have hcos : M.cosupp = actualReferenceHSLocus (vanishingIdeal (n := n) W) a :=
    actualReferenceHSMarked_cosupp hW E a
  obtain ⟨hSane,_hSa,hSak,hSasub⟩ := actualReferenceHSLocus_current_geometry hW hK hd.le hpure ha
  have hcompact : IsCompact M.cosupp := hcos.symm ▸ hSak
  have hnonempty : M.cosupp.Nonempty := hcos.symm ▸ hSane
  have husc := R.isInvValue.usc M hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at husc
  obtain ⟨c,hc,hmax⟩ := husc.exists_isMaxOn hcompact hnonempty
  let C := maxLocus (R.inv M (.refl : BlowupTower X X)) M.cosupp
  have hadm := R.isInvValue.isAdmissibleCentre_maxLocus hdom (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl] at hadm
  have hCSa : C ⊆ actualReferenceHSLocus (vanishingIdeal (n := n) W) a := hcos ▸ hadm.2.1
  have hCsing := hCSa.trans hSasub
  have hemb : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
    refine ⟨hadm.1,?_,hadm.2.2⟩
    rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.isClosed E]
    exact fun _ hy => (hCsing hy).1
  exact ⟨a,C,ha,⟨c,hc,hmax⟩,hCSa,hCsing,hemb,rfl⟩

/-- The SAME internally produced singular centre gives a true proper first blowup preserving EVERY regular-open point. -/
theorem exists_actual_current_full_hs_singular_first_blowup {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∃ (a : X) (C : Set X) (Y : CMfd.{u} n) (π : Y → X),
      a ∈ W \ regularLocus (n := n) W d ∧ C.Nonempty ∧
      C ⊆ actualReferenceHSLocus (vanishingIdeal (n := n) W) a ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (W \ regularLocus (n := n) W d)ᶜ ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      C = maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) W E a) (.refl : BlowupTower X X))
        (actualReferenceHSMarked (n := n) W E a).cosupp := by
  obtain ⟨a,C,ha,hCne,hCSa,hCsing,hCadm,hCeq⟩ :=
    exists_actual_current_full_hs_singular_first_centre hW hK hd hpure hns hE
  have hint : interior C = ∅ := eq_empty_of_subset_empty
    ((interior_mono (fun _ hy => (hCsing hy).1)).trans (currentPure_interior_empty hd hpure).subset)
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hint
  have hGsub : (W \ regularLocus (n := n) W d)ᶜ ⊆ Cᶜ :=
    fun _ hy hC => hy (hCsing hC)
  have hisoC := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (W \ regularLocus (n := n) W d)ᶜ := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hisoC.2.mono_left (preimage_mono hGsub)⟩
    · exact hisoC.1.2.1.mono (preimage_mono hGsub)
    · intro x hx
      obtain ⟨y,_hy,hπy⟩ := hisoC.1.2.2 (hGsub hx)
      exact ⟨y,by change π y ∈ (W \ regularLocus (n := n) W d)ᶜ; rwa [hπy],hπy⟩
  have hMwell : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hW,
      hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hE' := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hMwell hCadm hπ).isSNCDivisor
  exact ⟨a,C,Y,π,ha,hCne,hCSa,hCsing,hCadm,hπ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hiso,hE',hCeq⟩

end
end Hironaka.HironakaActualReferenceHSSingularCentre

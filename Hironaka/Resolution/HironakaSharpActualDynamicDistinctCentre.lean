/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFiniteProductResidual

/-! True current DISTINCT maxima construct actual next geometric blowups.
Full accumulated exceptional geometry retained; original modified-history
comparison/decrease, composite raw-TOTAL and sharp termination remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualDynamicDistinctCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFiniteProductResidual HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalDistinctTraceUSC HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalAllBoundaryCentre HironakaSharpActualChronologicalResidualDictionary
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder DivisorExponentAlong
  MonomialPartAlong NormalCrossings NormalCrossingsInvariance MarkedIdeals MarkedIdeals.MarkedIdeal
  CanonicalCentres ResolutionDriver ResolutionInvariantDriver MarkedIdealRestrictOpen
  AnalyticDimensionBasics BlowupTowerTransforms
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X : CMfd.{u} n}

/-- Genuine old-to-nearby quotient images bound ACTUAL distinct proper classes. -/
theorem eventually_actualDistinctProperCount_le {F : Fin m → GermIdeal n X}
    (hc : ∀ i,(F i).IsCoherent) (x : X) :
    ∀ᶠ y in 𝓝 x,actualDistinctProperCount F y ≤ actualDistinctProperCount F x := by
  have hrels : ∀ᶠ y in 𝓝 x,∀ i j,(actualIdealGermSetoid F x).r i j → (actualIdealGermSetoid F y).r i j := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : (actualIdealGermSetoid F x).r i j
    · exact (eventually_coherent_germ_eq (hc i) (hc j) hij).mono fun _ hy _ => hy
    · exact Eventually.of_forall fun _ h => False.elim (hij h)
  have hproper : ∀ᶠ y in 𝓝 x,actualProperPositions F y ⊆ actualProperPositions F x := by
    have hinc : ∀ᶠ y in 𝓝 x,∀ i,y ∈ (F i).zeroLocus → x ∈ (F i).zeroLocus := by
      apply eventually_all.mpr
      intro i
      by_cases hi : x ∈ (F i).zeroLocus
      · exact Eventually.of_forall fun _ _ => hi
      · filter_upwards [(CodimOneSupport.isComplexAnalyticSubset_zeroLocus (hc i)).isClosed.isOpen_compl.mem_nhds hi]
          with y hy hiy
        exact False.elim (hy hiy)
    filter_upwards [hinc] with y hy i hi
    exact (actual_proper_iff_zeroLocus hc i x).mpr (hy i ((actual_proper_iff_zeroLocus hc i y).mp hi))
  filter_upwards [hrels,hproper] with y hrel hsub
  let f : Quotient (actualIdealGermSetoid F x) → Quotient (actualIdealGermSetoid F y) := Quotient.map id hrel
  let Q := (actualProperPositions F x).image (Quotient.mk (actualIdealGermSetoid F x))
  have himg : (actualProperPositions F y).image (Quotient.mk (actualIdealGermSetoid F y)) ⊆ Q.image f := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨Quotient.mk (actualIdealGermSetoid F x) i,
      Finset.mem_image.mpr ⟨i,hsub hi,rfl⟩,rfl⟩
  exact (Finset.card_le_card himg).trans Finset.card_image_le

/-- Actual current marked product, with the ENTIRE genuine exceptional list. -/
def currentProductMarked (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : MarkedIdeal n Y :=
  ⟨(geoTransformAlong (geometricTemplate W []) T).N,(geoTransformAlong (geometricTemplate W []) T).E,
    chronologicalMemberProduct W E T,1⟩

private theorem template_compact_pure {W : Set X} (hW : IsClosedSubmanifold n W) (hK : IsCompact W)
    (d : ℕ) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T →
      IsCompact (geoTransformAlong (geometricTemplate W []) T).N ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N y d
  | _, .refl, _ => ⟨hK,hr⟩
  | _, .step T C π hπ, ht => by
    obtain ⟨hkT,hrT⟩ := template_compact_pure hW hK d hr T ht.1
    have hw : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht.1
    have hwNew := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw (.step T C π hπ) ht
    have hsub := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage (C := C)
      hπ.contMDiff.continuous hwT.isClosedSubmanifold_N.1
    refine ⟨((HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ).isCompact_preimage hkT).of_isClosed_subset
      hwNew.isClosedSubmanifold_N.1 hsub,?_⟩
    intro y hy
    exact BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hwT.isClosedSubmanifold_N.1 hrT ht.2.subset_N hy

/-- Genuine original input geometry supplies the actual SAME-list product domain. -/
theorem currentProductMarked_isInvDomain (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1 ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (ht : IsGeoTestTower (geometricTemplate W []) T) :
    IsInvDomain (n+1) (currentProductMarked W E T) := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht
  obtain ⟨hcP,hnzP,_hprP,_hord⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T ht
  have hgeom := template_compact_pure hW hK (d+1) hr T ht
  exact ⟨⟨hwT.isClosedSubmanifold_N,hcP,hwT.isSNCDivisor,hwT.isTransverse⟩,
    fun y hy => ⟨d+1,hd.trans (Nat.le_succ n),hgeom.2 y hy⟩,le_rfl,hnzP⟩

/-- True intrinsic nonmonomial normalization identifies the actual first order. -/
theorem currentProductMarked_nmOrd_eq_ordinaryTraceOrder (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (ht : IsGeoTestTower (geometricTemplate W []) T) (y : Y) :
    NonmonomialOrderLocal.nmOrd (currentProductMarked W E T) y=
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) y := by
  have hNm := (original_chronological_full_product_residual_dictionary hn hW hE hdense T ht).2.2.1
  apply NonmonomialOrderLocal.nmOrd_congr
  intro q
  change y ∈ cosupport n _ (nonmonomialPartAlong n _ _ _) q ↔ y ∈ cosupport n _ (nonmonomialPartAlong n _ _ []) q
  simp only [currentProductMarked,ordinaryTraceMarked]
  rw [hNm,nonmonomialPartAlong_nil_eq_restrictOn]

/-- True actual count USC and REAL first-coordinate equality give literal Z saturation. -/
theorem eventually_chronologicalDistinctDefect_of_same_value (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (ht : IsGeoTestTower (geometricTemplate W []) T)
    {x : Y} (hx : x ∈ chronologicalDistinctDefect W E T) :
    ∀ᶠ y in 𝓝 x,y ∈ (currentProductMarked W E T).N →
      (invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y) y=
        (invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y) x →
      y ∈ chronologicalDistinctDefect W E T := by
  have hc (i : Fin E.length) := (original_members_actual_finite_chronological_geometry hn hW hE hdense i T ht).2.2.2.1.isCoherent
  filter_upwards [eventually_actualDistinctProperCount_le hc x] with y hcount hyN hval
  have hfirst := congrArg (fun v : ValTy (n+1) => (ofLex v).1) hval
  change NonmonomialOrderLocal.nmOrd (geoTransformAlong (currentProductMarked W E T) (.refl : BlowupTower Y Y)) y=
    NonmonomialOrderLocal.nmOrd (geoTransformAlong (currentProductMarked W E T) (.refl : BlowupTower Y Y)) x at hfirst
  rw [geoTransformAlong_refl,currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T ht,
    currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T ht] at hfirst
  refine ⟨hyN,?_⟩
  rw [← chronological_product_eq_actual_family_product W E T]
  rw [hfirst]
  have hxnu := hx.2
  rw [← chronological_product_eq_actual_family_product W E T] at hxnu
  exact hcount.trans_lt hxnu

/-- ONLY original compact pure geometry and ACTUAL current history construct the
real restricted dynamic-Z maximum, with ENTIRE actual exceptional NC. -/
theorem exists_actual_dynamic_distinct_max_centre (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1 ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (ht : IsGeoTestTower (geometricTemplate W []) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ C : Set Y,C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (currentProductMarked W E T).IsAdmissibleCentre C ∧
      (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C ∧
      C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y))
        (chronologicalDistinctDefect W E T) := by
  let M := currentProductMarked W E T
  let R := invFamily.{u} hn (n+1)
  let f := R.inv M (.refl : BlowupTower Y Y)
  let Z := chronologicalDistinctDefect W E T
  have hdom := currentProductMarked_isInvDomain hn hW hE hdense hK hd hr T ht
  have hPcoh := hdom.isWellFormed.isCoherent
  have hZcos : Z ⊆ M.cosupp := by
    intro x hx
    apply (ordinaryTraceOrder_cosupport_iff hdom.isWellFormed.isClosedSubmanifold_N hPcoh hdom.isNonzeroAlongAt hx.1 1).mpr
    have hh := hx.2
    rw [← chronological_product_eq_actual_family_product W E T] at hh
    change 1 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x
    omega
  have husc := R.isInvValue.usc M hdom (.refl : BlowupTower Y Y) trivial
  rw [geoTransformAlong_refl] at husc
  have hZusc := husc.mono hZcos
  have haZ := original_chronological_distinct_defect_analytic hn hW hE hdense d hr T ht
  have hkN := (template_compact_pure hW hK (d+1) hr T ht).1
  have hkZ := hkN.of_isClosed_subset haZ.isClosed (fun _ hx => hx.1)
  obtain ⟨a,ha,hmax⟩ := hZusc.exists_isMaxOn hkZ hne
  let C := maxLocus f Z
  have hCeq : C={x | x ∈ Z ∧ f x=f a} := maxLocus_eq_level ⟨ha,hmax⟩
  have hCne : C.Nonempty := ⟨a,ha,hmax⟩
  have hCZ : C ⊆ Z := fun _ hx => hx.1
  have hCclosed : IsClosed C := hCeq ▸ hZusc.isClosed_maxLocus haZ.isClosed hmax
  have hClocal : ∀ x ∈ C,(∃ j,RegularAtDim (n := n) C x j) ∧
      HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) C M.E x := by
    intro x hx
    have hxeq : f x=f a := (hCeq ▸ hx).2
    have hnb : ∀ᶠ y in 𝓝 x,(y ∈ M.cosupp → f y ≤ f x) ∧
        (y ∈ M.N → f y=f x → y ∈ Z) :=
      (husc x (hZcos hx.1)).and (eventually_chronologicalDistinctDefect_of_same_value hn hW hE hdense T ht hx.1)
    obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hnb
    let U : Opens Y := ⟨V,hVo⟩
    let z : U := ⟨x,hxV⟩
    have hAdm := R.isInvValue.admissible M hdom (.refl : BlowupTower Y Y) trivial U (f x)
      (fun y hy hyU => by simpa only [geoTransformAlong_refl] using (hV hyU).1 (by simpa only [geoTransformAlong_refl] using hy))
    rw [geoTransformAlong_refl] at hAdm
    have hlocal : (Subtype.val : U → Y) ⁻¹' {y | y ∈ M.cosupp ∧ f y=f x}=(Subtype.val : U → Y) ⁻¹' C := by
      ext y
      constructor
      · intro hy
        have hyZ : (y : Y) ∈ Z := (hV y.property).2 (M.cosupp_subset_N hy.1) hy.2
        apply (show (y : Y) ∈ C ↔ (y : Y) ∈ Z ∧ f y=f a from by rw [hCeq];rfl).mpr
        exact ⟨hyZ,hy.2.trans hxeq⟩
      · intro hy
        exact ⟨hZcos hy.1,((hCeq ▸ hy).2).trans hxeq.symm⟩
    rw [hlocal] at hAdm
    obtain ⟨j,hj⟩ := hAdm.1.2 z hx
    refine ⟨⟨j,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hj⟩,?_⟩
    exact normalCrossingsAt_preimage_val_iff.mp (hAdm.2.2 z hx)
  have hCsm : IsClosedSubmanifold n C := ⟨hCclosed,fun x hx => (hClocal x hx).1⟩
  have hNC : HasNormalCrossings n C M.E := fun x hx => (hClocal x hx).2
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht
  have htemp : (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C := by
    refine ⟨hCsm,?_,hNC⟩
    change C ⊆ cosupport n _ _ (geoTransformAlong (geometricTemplate W []) T).d
    rw [d_geoTransformAlong]
    change C ⊆ cosupport n _ _ 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwT.isCoherent hg)]
    exact fun _ hx => hx.1.1
  exact ⟨C,hCne,hCZ,⟨hCsm,hCZ.trans hZcos,hNC⟩,htemp,rfl⟩

/-- The SAME independently selected centre really appends an actual geometric
step, with the whole dynamic-Z complement isomorphism and ordered SNC. -/
theorem exists_actual_dynamic_distinct_next_blowup (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1 ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (ht : IsGeoTestTower (geometricTemplate W []) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (currentProductMarked W E T).IsAdmissibleCentre C ∧
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ ∧
      IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) ∧
      IsSNCDivisor n ((geoTransformAlong (geometricTemplate W []) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y))
        (chronologicalDistinctDefect W E T) := by
  obtain ⟨C,hneC,hCZ,hadm,htemp,hCeq⟩ := exists_actual_dynamic_distinct_max_centre hn hW hE hdense hK hd hr T ht hne
  have hdom := currentProductMarked_isInvDomain hn hW hE hdense hK hd hr T ht
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hadm.2.1).trans (interior_cosupp_eq_empty hdom).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup C hadm.1 hint
  have hsub : (chronologicalDistinctDefect W E T)ᶜ ⊆ Cᶜ := fun _ hx hC => hx (hCZ hC)
  have hi := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hi.2.mono_left (preimage_mono hsub)⟩
    · exact hi.1.2.1.mono (preimage_mono hsub)
    · intro y hy
      obtain ⟨z,_hz,hz⟩ := hi.1.2.2 (hsub hy)
      exact ⟨z,by change π z ∈ (chronologicalDistinctDefect W E T)ᶜ;rwa [hz],hz⟩
  have htNew : IsGeoTestTower (geometricTemplate W []) (.step T C π hπ) := ⟨ht,htemp⟩
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hEnew := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw (.step T C π hπ) htNew).isSNCDivisor
  exact ⟨C,Z,π,hπ,hneC,hCZ,hadm,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,
    hπ.contMDiff,hiso,htNew,hEnew,hCeq⟩

end
end Hironaka.HironakaSharpActualDynamicDistinctCentre

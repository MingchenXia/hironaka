/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualOriginalControlledHistory

/-! Genuine SAME ORIGINAL dynamic FIRST-Z step and original FIRST-coordinate
nonincrease. Higher full-invariant histories/decrease and termination stay OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualOriginalDynamicStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFiniteMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalProductTraceOrder HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers MarkedIdealOperationsAlong GermIdealOrder InvertibleIdealQuotient
  NonmonomialOrderLocal NonmonomialOrderCanonical CanonicalCentres ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Real WHOLE original residual equality supplies BOTH true order-threshold
directions before comparing the SAME original and actual current product orders. -/
theorem original_product_nmOrd_eq_current (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (q : ℕ)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E q) T) (y : Y) :
    nmOrd (geoTransformAlong (originalMemberProductMarked W E q) T) y=nmOrd (currentProductMarked W E T) y := by
  let M := originalMemberProductMarked W E q
  have hcI := isCoherent_originalMemberProduct hn hE
  have hwM : M.IsWellFormed := ⟨hW,hcI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template M hwM T hT
  have hResidual := (original_product_controlled_history_residual_dictionary hn hW hE hdense q T hT).1
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  obtain ⟨hcP,_hnzP,_hprP,_hordP⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hGeom
  refine Eq.trans ?_ (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hGeom y).symm
  apply nmOrd_congr
  intro r
  change y ∈ cosupport n (geoTransformAlong M T).N (nonmonomialPartAlong n (geoTransformAlong M T).N
    (geoTransformAlong M T).ideal (geoTransformAlong M T).E) r ↔
    y ∈ cosupport n (geoTransformAlong (geometricTemplate W []) T).N
      (nonmonomialPartAlong n (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) []) r
  rw [hResidual,hQN,nonmonomialPartAlong_nil_eq_restrictOn]
  constructor
  · intro hy
    exact cosupport_subset_of_restrictLe (N := (geoTransformAlong (geometricTemplate W []) T).N)
      (𝔞 := restrictOn n (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T))
      (𝔟 := chronologicalMemberProduct W E T) restrictLe_restrictOn r hy
  · intro hy
    exact cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hcP) r hy

private theorem actual_dynamic_max_original_admissible_constant (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {C : Set Y} (hneC : C.Nonempty) (hCur : (currentProductMarked W E T).IsAdmissibleCentre C)
    (hCeq : C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y))
      (chronologicalDistinctDefect W E T)) :
    (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C ∧
      ∃ r : ℕ,∀ c ∈ C,nmOrd (geoTransformAlong (originalMemberProductMarked W E 1) T) c=r := by
  let M := originalMemberProductMarked W E 1
  let Q := geoTransformAlong M T
  have hcI := isCoherent_originalMemberProduct hn hE
  have hwM : M.IsWellFormed := ⟨hW,hcI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwM T hT
  have hGeom := actual_original_test_history_template M hwM T hT
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hQE := geoTransformAlong_E_eq_of_E_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hResidual := (original_product_controlled_history_residual_dictionary hn hW hE hdense 1 T hT).1
  obtain ⟨hcP,_hnzP,_hprP,_hordP⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hGeom
  have hLe : Q.ideal.Le (chronologicalMemberProduct W E T) := by
    rw [←hResidual]
    exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hwQ.isCoherent
  have hRestrict := RestrictLeCalculus.restrictLe_of_le (W := Q.N) hcP hLe
  have hCos : C ⊆ Q.cosupp := by
    intro x hx
    have hxP := hCur.2.1 hx
    change x ∈ cosupport n (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) 1 at hxP
    have hxQ : x ∈ cosupport n Q.N (chronologicalMemberProduct W E T) 1 := by rw [hQN]; exact hxP
    change x ∈ cosupport n Q.N Q.ideal (geoTransformAlong M T).d
    rw [d_geoTransformAlong]
    exact cosupport_subset_of_restrictLe hRestrict 1 hxQ
  have hAdm : Q.IsAdmissibleCentre C := by
    refine ⟨hCur.1,hCos,?_⟩
    rw [hQE]
    exact hCur.2.2
  obtain ⟨a,ha⟩ := hneC
  refine ⟨hAdm,nmOrd Q a,?_⟩
  intro c hc
  have hca := (hCeq ▸ hc).2 a (hCeq ▸ ha).1
  have hac := (hCeq ▸ ha).2 c (hCeq ▸ hc).1
  have hval := le_antisymm hac hca
  have hfirst := congrArg (fun v : ValTy (n+1) => (ofLex v).1) hval
  change nmOrd (geoTransformAlong (currentProductMarked W E T) (.refl : BlowupTower Y Y)) c=
    nmOrd (geoTransformAlong (currentProductMarked W E T) (.refl : BlowupTower Y Y)) a at hfirst
  rw [geoTransformAlong_refl] at hfirst
  rw [original_product_nmOrd_eq_current hn hW hE hdense 1 T hT c,
    original_product_nmOrd_eq_current hn hW hE hdense 1 T hT a]
  exact hfirst

/-- The independently selected true dynamic maximum is ORIGINAL-admissible,
and ORIGINAL first order is internally proved constant on that SAME centre. -/
theorem exists_original_dynamic_distinct_centre (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1 ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ C : Set Y,C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (geoTransformAlong (originalMemberProductMarked W E 1) T).IsAdmissibleCentre C ∧
      (∃ r : ℕ,∀ c ∈ C,nmOrd (geoTransformAlong (originalMemberProductMarked W E 1) T) c=r) ∧
      C=maxLocus ((invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y))
        (chronologicalDistinctDefect W E T) := by
  have hwM : (originalMemberProductMarked W E 1).IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template _ hwM T hT
  obtain ⟨C,hneC,hCZ,hCur,_htemp,hCeq⟩ := exists_actual_dynamic_distinct_max_centre hn hW hE hdense hK hd hr T hGeom hne
  obtain ⟨hAdm,hLevel⟩ := actual_dynamic_max_original_admissible_constant hn hW hE hdense T hT hneC hCur hCeq
  exact ⟨C,hneC,hCZ,hAdm,hLevel,hCeq⟩

/-- SAME independently selected dynamic blowup appends the ORIGINAL history
and compares its EXISTING original first coordinate at EVERY new cosupport point. -/
theorem exists_original_dynamic_distinct_step_comparison (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W) {d : ℕ} (hd : d+1 ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    let M := originalMemberProductMarked W E 1
    ∃ (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (geoTransformAlong M T).IsAdmissibleCentre C ∧ IsGeoTestTower M (.step T C π hπ) ∧
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ ∧
      IsSNCDivisor n (geoTransformAlong M (.step T C π hπ)).E ∧
      ∀ z ∈ (geoTransformAlong M (.step T C π hπ)).cosupp,
        π z ∈ (geoTransformAlong M T).cosupp ∧
        (ofLex ((invFamily hn (n+1)).inv M (.step T C π hπ) z)).1≤
          (ofLex ((invFamily hn (n+1)).inv M T (π z))).1 ∧
        (π z ∉ C → (ofLex ((invFamily hn (n+1)).inv M (.step T C π hπ) z)).1=
          (ofLex ((invFamily hn (n+1)).inv M T (π z))).1) := by
  let M := originalMemberProductMarked W E 1
  let Q := geoTransformAlong M T
  have hDom : IsInvDomain (n+1) M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨d+1,hd.trans (Nat.le_succ n),hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hGeom := actual_original_test_history_template M hDom.isWellFormed T hT
  obtain ⟨C,Z,π,hπ,hneC,hCZ,hCur,hproper,hholo,hiso,_hGeomNew,_hSNC,hCeq⟩ :=
    exists_actual_dynamic_distinct_next_blowup hn hW hE hdense hK hd hr T hGeom hne
  obtain ⟨hAdm,r,hLevel⟩ := actual_dynamic_max_original_admissible_constant hn hW hE hdense T hT hneC hCur hCeq
  have hStep : IsGeoTestTower M (.step T C π hπ) := ⟨hT,hAdm⟩
  have hDomQ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom T hT
  have hPost := InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom (.step T C π hπ) hStep
  refine ⟨C,Z,π,hπ,hneC,hCZ,hAdm,hStep,hproper,hholo,hiso,hPost.isWellFormed.isSNCDivisor,?_⟩
  intro z hz
  change π z ∈ Q.cosupp ∧ nmOrd (Q.geoTransform C π) z≤nmOrd Q (π z) ∧
    (π z ∉ C → nmOrd (Q.geoTransform C π) z=nmOrd Q (π z))
  have hOff : π z ∉ C → nmOrd (Q.geoTransform C π) z=nmOrd Q (π z) :=
    fun hzC => nmOrd_geoTransform_of_notMem hn hDomQ hAdm hπ hzC
  by_cases hzC : π z ∈ C
  · refine ⟨hAdm.2.1 hzC,?_,hOff⟩
    rw [hLevel (π z) hzC]
    exact nmOrd_geoTransform_le_of_level hn hDomQ hAdm hπ hLevel hz hzC
  · have hCos := (TransformOffCentre.mem_cosupp_geoTransform_iff Q hDomQ.isWellFormed.isClosedSubmanifold_N.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDomQ.isWellFormed.isCoherent hg)
        hπ hzC).mp hz
    exact ⟨hCos,(hOff hzC).le,hOff⟩

end
end Hironaka.HironakaSharpActualOriginalDynamicStep

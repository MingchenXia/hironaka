/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.MarkedIdeal.GeoStrictEmptyExact
import Hironaka.MarkedIdeal.GeoResolutionAppendExact
import Hironaka.Invariant.UnitCosupportExact
import Hironaka.Invariant.NonzeroAlongUnivExact
import Hironaka.Resolution.HironakaNormalCrossingsOriginalExponents
import Hironaka.Blowup.BlowupExistenceCodimOne

/-!
# Genuine finite marked completion for the original NC ideal

The sole original input is an actual closed NC carrier. Its SAME original
whole vanishing ideal, actual separating tower and recorded historical r-1
weights internally produce a genuine finite mark-one test resolution.
Every remaining Cartier identity projection is a real universal-property
blowup with internally proved admissibility and whole controlled division.
The tail length is exactly one plus the actual coefficient sum; its bound is
1+(n-1)^2 and the complete tower bound is 1+n*(n-1), without compactness.
All literal empty/repeated historical entries are retained. Dimension zero
has exactly one genuine empty Cartier step and literal final boundary [∅].

Blueprint: hironaka-normal-crossings-finite-marked-completion-extension.tex.
No caller tower, termination, order, coefficient or naturality certificate.
Old ordered/colex driver identification and unrelated marked ideals remain
OPEN; this elementary SAME-original producer does not close G9.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsFiniteMarkedCompletion
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaNormalCrossingsOriginalExponents HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsBoundaryTransform
  BlowupTowers BlowupFlatCoordinates BlowupStrictSubmanifold NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
  DivisorExponent HironakaDivisorResidual IdealOrderArithmetic HironakaNormalCrossingsLocalBranches
open Hironaka
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- True actual SNC coordinates exclude the interior of EVERY literal member, including dimension zero. -/
theorem interior_snc_member_eq_empty {E : List (Set M)} (hE : IsSNCDivisor n E)
    (i : Fin E.length) : interior (E.get i) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxi : x ∈ E.get i := interior_subset hx
  obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard,hinj⟩ := hE.2 x
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (hcard i hxi)
  have hfreq := MonomialPart.frequently_flatMap_ne_zero hsrc (mem_flatDomain_self Φ) {j}
  obtain ⟨y,⟨hyD,hyne,_⟩,hyE⟩ := (hfreq.and_eventually (mem_interior_iff_mem_nhds.mp hx)).exists
  have hy0 := (hflat i hxi hyD.1 hyD.2).mp hyE
  exact hyne j (Finset.mem_singleton_self j) (hy0 j (by rw [hj]; simp))

/-- Genuine actual SNC member geometry, with no smoothness or codimension certificate. -/
theorem snc_member_codimOne_geometry {E : List (Set M)} (hE : IsSNCDivisor n E)
    (i : Fin E.length) :
    IsClosedSubmanifold n (E.get i) ∧ interior (E.get i) = ∅ ∧
      ∀ x ∈ E.get i, ∃ k, RegularAtDim (n := n) (E.get i) x k ∧ k+1=n := by
  refine ⟨?_,interior_snc_member_eq_empty hE i,?_⟩
  · refine ⟨hE.1 _ (List.get_mem _ _),?_⟩
    intro x hx
    cases n with
    | zero =>
      obtain ⟨S,_,hcard,_⟩ := hE.2 x
      have hb := Finset.card_le_univ (S i)
      have hc := hcard i hx
      simp only [Fintype.card_fin] at hb
      omega
    | succ m => exact ⟨m,SNCGlobalPrimeComponents.regularAtDim_member hE i hx⟩
  · intro x hx
    cases n with
    | zero =>
      obtain ⟨S,_,hcard,_⟩ := hE.2 x
      have hb := Finset.card_le_univ (S i)
      have hc := hcard i hx
      simp only [Fintype.card_fin] at hb
      omega
    | succ m => exact ⟨m,SNCGlobalPrimeComponents.regularAtDim_member hE i hx,rfl⟩

/-- The internally produced genuine Cartier centre ideal is COMPLETE and invertible. -/
theorem isInvertible_vanishingIdeal_snc_member {E : List (Set M)}
    (hE : IsSNCDivisor n E) (i : Fin E.length) :
    (vanishingIdeal (n := n) (E.get i)).IsInvertible := by
  obtain ⟨hc,hi,hr⟩ := snc_member_codimOne_geometry hE i
  exact BlowupExistenceCodimOne.isInvertible_vanishingIdeal_of_codimOne hc.1 hi hr

/-- Actual identity projection is a TRUE universal-property blowup along the actual SNC member. -/
theorem isBlowupAlong_id_snc_member {E : List (Set M)}
    (hE : IsSNCDivisor n E) (i : Fin E.length) :
    IsBlowupAlong n (E.get i) (id : M → M) := by
  obtain ⟨hc,hi,hr⟩ := snc_member_codimOne_geometry hE i
  exact BlowupExistenceCodimOne.isBlowupAlong_id_of_codimOne hc hi hr

omit [IsComplexManifold n M] in
/-- A real present SNC member has genuine centre coordinates with the ENTIRE actual boundary. -/
theorem hasNormalCrossings_snc_member {E : List (Set M)}
    (hE : IsSNCDivisor n E) (i : Fin E.length) : HasNormalCrossings n (E.get i) E := by
  intro x hx
  obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard,_⟩ := hE.2 x
  refine ⟨S i,S,⟨Φ,hsrc,h0,?_⟩,hcard⟩
  rintro (_|j) hy z hz hzΦ
  · exact hflat i hy hz hzΦ
  · exact hflat j hy hz hzΦ

/-- The selected actual Cartier member has literal geometric strict transform EMPTY. -/
theorem geoStrictTransform_id_selected {C : Set M} : geoStrictTransform (id : M → M) C C = ∅ :=
  geoStrictTransform_eq_empty_of_subset (Subset.refl C)

/-- Different LITERAL true SNC indices retain the whole actual carrier under a genuine identity Cartier blowup. -/
theorem geoStrictTransform_id_snc_other {E : List (Set M)}
    (hE : IsSNCDivisor n E) (i j : Fin E.length) (hij : i ≠ j) :
    geoStrictTransform (id : M → M) (E.get j) (E.get i) = E.get i := by
  change closure ((id : M → M) ⁻¹' (E.get i \ E.get j)) = E.get i
  rw [preimage_id]
  apply Subset.antisymm
  · exact closure_minimal sdiff_subset (hE.1 _ (List.get_mem _ _))
  · intro x hx
    by_cases hxj : x ∈ E.get j
    · obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard,hinj⟩ := hE.2 x
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard i hx)
      obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (hcard j hxj)
      have hab : a ≠ b := by
        intro heq
        apply hij
        exact hinj hx hxj (by rw [ha,hb,heq])
      apply mem_closure_iff_frequently.mpr
      apply (MonomialPart.frequently_flatMap_ne_zero hsrc (mem_flatDomain_self Φ) {b}).mono
      rintro y ⟨hyD,hyne,hyeq⟩
      refine ⟨(hflat i hx hyD.1 hyD.2).mpr ?_,?_⟩
      · intro l hl
        have hl' : l = a := by simpa only [ha,Finset.mem_singleton] using hl
        subst l
        change GiraudAlong.flatMap Φ y a = 0
        rw [hyeq a (by simpa only [Finset.mem_singleton] using hab)]
        change Φ.toFun (chartAt (ComplexModel n) x x) a = 0
        exact ((hflat i hx (mem_flatDomain_self Φ).1 (mem_flatDomain_self Φ).2).mp hx) a hl
      · intro hyj
        have hy0 := (hflat j hxj hyD.1 hyD.2).mp hyj
        exact hyne b (Finset.mem_singleton_self b) (hy0 b (by rw [hb]; simp))
    · exact subset_closure ⟨hx,hxj⟩


private theorem invertible_componentPowerProduct_of_present {E : List (Set M)}
    (hE : IsSNCDivisor n E) (F : List (Set M × ℕ)) (hF : ∀ p ∈ F, p.1 ∈ E) :
    (componentPowerProduct (n := n) F).IsInvertible := by
  induction F with
  | nil => exact BlowupExceptionalDivisor.isInvertible_unitIdeal
  | cons p F ih =>
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hF p (by simp))
    have hI : (vanishingIdeal (n := n) p.1).IsInvertible := by
      rw [← hi]
      exact isInvertible_vanishingIdeal_snc_member hE i
    exact GermIdealTotalTransform.isInvertible_mul
      (BlowupExceptionalDivisor.isInvertible_idealPow hI p.2)
      (ih fun q hq => hF q (List.mem_cons_of_mem p hq))

/-- The COMPLETE actual component-power ideal defines its true whole-ambient mark-one datum. -/
def monomialMarkedIdeal (E : List (Set M)) (F : List (Set M × ℕ)) : MarkedIdeal n M :=
  ⟨univ,E,componentPowerProduct (n := n) F,1⟩

/-- Ordinary actual SNC input internally supplies complete-product marked well-formedness. -/
theorem isWellFormed_monomialMarkedIdeal {E : List (Set M)} (hE : IsSNCDivisor n E)
    (F : List (Set M × ℕ)) (hF : ∀ p ∈ F, p.1 ∈ E) :
    (monomialMarkedIdeal (n := n) E F).IsWellFormed :=
  ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    DivisorMetric.isCoherent_of_isInvertible (invertible_componentPowerProduct_of_present hE F hF),
    hE,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩

/-- Actual whole product invertibility supplies every genuine marking-one domain field internally. -/
theorem isInvDomain_monomialMarkedIdeal {E : List (Set M)} (hE : IsSNCDivisor n E)
    (F : List (Set M × ℕ)) (hF : ∀ p ∈ F, p.1 ∈ E) :
    Hironaka.ResolutionInvariantSpec.IsInvDomain n (monomialMarkedIdeal (n := n) E F) := by
  refine ⟨isWellFormed_monomialMarkedIdeal hE F hF,?_,le_rfl,?_⟩
  · intro x _
    exact ⟨n,le_rfl,AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  · intro x _
    exact DivisorExponentAlong.isNonzeroAlongAt_univ_iff.mpr
      (HironakaDivisorPowers.isNonzeroAt_of_isInvertible
        (invertible_componentPowerProduct_of_present hE F hF) x)

/-- Whole carrier availability is preserved in the LITERAL actual Cartier boundary, including empty/repeated history. -/
theorem mem_cartier_boundary_of_mem {E : List (Set M)} (hE : IsSNCDivisor n E)
    {C W : Set M} (hC : C ∈ E) (hW : W ∈ E) :
    W ∈ E.map (geoStrictTransform (id : M → M) C) ++ [C] := by
  by_cases heq : W = C
  · exact List.mem_append_right _ (heq ▸ List.mem_singleton_self C)
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hW
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hC
    have hij : i ≠ j := by intro hij; apply heq; rw [← hi,← hj,hij]
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨W,hW,?_⟩
    rw [← hi,← hj]
    exact geoStrictTransform_id_snc_other hE i j hij

variable {A : CMfd.{u} n}

private theorem cartier_factor_admissible (M : MarkedIdeal n A)
    (hN : M.N = univ) (hd : M.d = 1)
    {C : Set A} (hC : IsClosedSubmanifold n C) (hNC : HasNormalCrossings n C M.E)
    (J : GermIdeal n A) (hJ : J.IsInvertible)
    (hf : M.ideal = (vanishingIdeal (n := n) C).mul J) : M.IsAdmissibleCentre C := by
  refine ⟨hC,?_,hNC⟩
  intro x hx
  change x ∈ GermIdealOrder.cosupport n M.N M.ideal M.d
  rw [hN,hd]
  refine ⟨mem_univ x,?_⟩
  intro g hg
  rw [hf] at hg
  apply IsInSpanAt.vanishesToOrderOn (InvertibleIdealQuotient.mem_mul_iff.mp hg)
  rintro _ ⟨a,b,ha,hb,rfl⟩
  have hbh := RelativePrincipalizationSpan.GermIdeal.IsInvertible.holomorphicAt_mem hJ hb
  apply (GermIdealOrder.vanishesToOrderOn_one_iff (mem_univ x) (ha.1.mul hbh)).mpr
  rw [ha.2.self_of_nhds hx,zero_mul]

private theorem cartier_factor_control (M : MarkedIdeal n A)
    (hw : M.IsWellFormed) (hN : M.N = univ) (hd : M.d = 1) (hI : M.ideal.IsInvertible)
    {C : Set A} (hπ : IsBlowupAlong n C (id : A → A))
    (hCadm : M.IsAdmissibleCentre C) (J : GermIdeal n A) (hJ : J.IsInvertible)
    (hf : M.ideal = (vanishingIdeal (n := n) C).mul J) :
    (M.geoTransform C (id : A → A)).ideal = J := by
  let L := vanishingIdeal (n := n) C
  have hL : L.IsInvertible := by
    have hh := hπ.2.2.2.1
    rw [BlowupControlledTransform.pullback_id (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)] at hh
    exact hh
  have hLc := DivisorMetric.isCoherent_of_isInvertible hL
  have hsub : C ⊆ GermIdealOrder.cosupport n univ M.ideal 1 := by
    simpa only [MarkedIdeal.cosupp,hN,hd] using hCadm.2.1
  have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hw.isCoherent hCadm.1 hsub
  have hp := BlowupControlledTransform.pullback_eq_mul_controlledTransform hπ hw.isCoherent hle
  rw [BlowupControlledTransform.pullback_id hw.isCoherent,exceptionalIdeal_eq_vanishingIdeal hπ,
    preimage_id,FactorizationFromResolution.idealPow_one_of_isCoherent hLc] at hp
  have hc : BlowupControlledTransform.controlledTransform hπ M.ideal 1 = J :=
    eq_of_invertible_mul_left_eq (HironakaHypersurfaceStrictIdeal.isInvertible_controlledTransform hπ hI 1 hle)
      hJ hL (hp.symm.trans hf)
  rw [geoTransform_ideal_eq_controlledTransform hN hw.isCoherent hπ,hd,hc]

/-- An actual PRESENT component of positive power is a true SAME-ideal marking-one admissible centre. -/
theorem isAdmissibleCentre_monomial_succ {E : List (Set A)} (hE : IsSNCDivisor n E)
    (C : Set A) (hC : C ∈ E) (F : List (Set A × ℕ)) (hF : ∀ p ∈ F, p.1 ∈ E) (k : ℕ) :
    (monomialMarkedIdeal (n := n) E ((C,k+1)::F)).IsAdmissibleCentre C := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hC
  have hL : (vanishingIdeal (n := n) C).IsInvertible := by
    rw [← hi]
    exact isInvertible_vanishingIdeal_snc_member hE i
  have hLc := DivisorMetric.isCoherent_of_isInvertible hL
  have hJ := invertible_componentPowerProduct_of_present hE F hF
  have hJc := DivisorMetric.isCoherent_of_isInvertible hJ
  have hp := GermIdealPullbackCalculus.isCoherent_idealPow hLc k
  have hf : (monomialMarkedIdeal (n := n) E ((C,k+1)::F)).ideal =
      (vanishingIdeal (n := n) C).mul (componentPowerProduct (n := n) ((C,k)::F)) := by
    change (idealPow (vanishingIdeal (n := n) C) (k+1)).mul (componentPowerProduct (n := n) F) = _
    rw [idealPow_succ,RestrictLeCalculus.mul_comm' (idealPow (vanishingIdeal (n := n) C) k) (vanishingIdeal (n := n) C),
      GermIdealTotalTransform.mul_assoc hLc hp hJc]
    rfl
  apply cartier_factor_admissible _ rfl rfl
    (hi ▸ (snc_member_codimOne_geometry hE i).1) (hi ▸ hasNormalCrossings_snc_member hE i)
    _ (invertible_componentPowerProduct_of_present hE _ (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl|hp
      · exact hC
      · exact hF p hp)) hf


/-- The TRUE whole positive-power marking-one Cartier transform divides exactly one actual factor and keeps its literal boundary. -/
theorem geoTransform_monomial_succ {E : List (Set A)} (hE : IsSNCDivisor n E)
    (C : Set A) (hC : C ∈ E) (F : List (Set A × ℕ)) (hF : ∀ p ∈ F, p.1 ∈ E) (k : ℕ) :
    (monomialMarkedIdeal (n := n) E ((C,k+1)::F)).geoTransform C (id : A → A) =
      monomialMarkedIdeal (n := n) (E.map (geoStrictTransform (id : A → A) C) ++ [C]) ((C,k)::F) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hC
  have hπ : IsBlowupAlong n C (id : A → A) := hi ▸ isBlowupAlong_id_snc_member hE i
  have hL : (vanishingIdeal (n := n) C).IsInvertible := hi ▸ isInvertible_vanishingIdeal_snc_member hE i
  have hLc := DivisorMetric.isCoherent_of_isInvertible hL
  have hJ := invertible_componentPowerProduct_of_present hE F hF
  have hJc := DivisorMetric.isCoherent_of_isInvertible hJ
  have hp := GermIdealPullbackCalculus.isCoherent_idealPow hLc k
  have hfull : ∀ p ∈ (C,k+1)::F, p.1 ∈ E := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact hC
    · exact hF p hp
  have hremain : ∀ p ∈ (C,k)::F, p.1 ∈ E := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact hC
    · exact hF p hp
  have hf : (monomialMarkedIdeal (n := n) E ((C,k+1)::F)).ideal =
      (vanishingIdeal (n := n) C).mul (componentPowerProduct (n := n) ((C,k)::F)) := by
    change (idealPow (vanishingIdeal (n := n) C) (k+1)).mul (componentPowerProduct (n := n) F) = _
    rw [idealPow_succ,RestrictLeCalculus.mul_comm' (idealPow (vanishingIdeal (n := n) C) k) (vanishingIdeal (n := n) C),
      GermIdealTotalTransform.mul_assoc hLc hp hJc]
    rfl
  have hcontrol := cartier_factor_control (monomialMarkedIdeal (n := n) E ((C,k+1)::F))
    (isWellFormed_monomialMarkedIdeal hE _ hfull) rfl rfl
    (invertible_componentPowerProduct_of_present hE _ hfull) hπ
    (isAdmissibleCentre_monomial_succ hE C hC F hF k)
    _ (invertible_componentPowerProduct_of_present hE _ hremain) hf
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ hcontrol rfl
  · exact geoTransform_N_eq_univ rfl hπ
  · rfl

/-- Literal zero powers produce the exact SAME marked datum as the genuine whole tail product. -/
theorem monomialMarkedIdeal_zero_head {E : List (Set A)} (hE : IsSNCDivisor n E)
    (C : Set A) (F : List (Set A × ℕ)) (hF : ∀ p ∈ F, p.1 ∈ E) :
    monomialMarkedIdeal (n := n) E ((C,0)::F) = monomialMarkedIdeal (n := n) E F := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change (idealPow (vanishingIdeal (n := n) C) 0).mul (componentPowerProduct (n := n) F) = _
  rw [idealPow_zero,BlowupControlledTransform.unitIdeal_mul
    (DivisorMetric.isCoherent_of_isInvertible (invertible_componentPowerProduct_of_present hE F hF))]
  rfl

/-- Actual complete unit ideal is a resolved SAME whole-ambient marking-one datum. -/
theorem monomialMarkedIdeal_nil_resolution (E : List (Set A)) :
    IsGeoResolution (monomialMarkedIdeal (n := n) E []) (BlowupTower.refl : BlowupTower A A) := by
  refine ⟨trivial,?_⟩
  change GermIdealOrder.cosupport n univ (unitIdeal n A) 1 = ∅
  exact GermIdealOrder.cosupport_unitIdeal le_rfl


/-- A genuine finite SAME-ideal Cartier resolution is internally produced by the literal coefficient sum. -/
theorem exists_monomial_cartier_resolution (F : List (Set A × ℕ)) :
    ∀ (E : List (Set A)), IsSNCDivisor n E → (∀ p ∈ F, p.1 ∈ E) →
      ∃ S : BlowupTower A A, S.proj = id ∧ S.length = (F.map Prod.snd).sum ∧
        IsGeoResolution (monomialMarkedIdeal (n := n) E F) S ∧
        (geoTransformAlong (monomialMarkedIdeal (n := n) E F) S).ideal = unitIdeal n A := by
  induction F with
  | nil =>
    intro E _ _
    exact ⟨.refl,rfl,rfl,monomialMarkedIdeal_nil_resolution E,rfl⟩
  | cons p F ih =>
    rcases p with ⟨C,k⟩
    have hloop : ∀ k (E : List (Set A)), IsSNCDivisor n E → C ∈ E →
        (∀ p ∈ F, p.1 ∈ E) →
        ∃ S : BlowupTower A A, S.proj = id ∧ S.length = k+(F.map Prod.snd).sum ∧
          IsGeoResolution (monomialMarkedIdeal (n := n) E ((C,k)::F)) S ∧
          (geoTransformAlong (monomialMarkedIdeal (n := n) E ((C,k)::F)) S).ideal = unitIdeal n A := by
      intro k
      induction k with
      | zero =>
        intro E hE _ hf
        obtain ⟨S,hp,hl,hr,hu⟩ := ih E hE hf
        rw [monomialMarkedIdeal_zero_head hE C F hf]
        exact ⟨S,hp,by simpa using hl,hr,hu⟩
      | succ k ihk =>
        intro E hE hc hf
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
        have hπ : IsBlowupAlong n C (id : A → A) := hi ▸ isBlowupAlong_id_snc_member hE i
        let T : BlowupTower A A := .step .refl C id hπ
        let E' := E.map (geoStrictTransform (id : A → A) C) ++ [C]
        have ht : IsGeoTestTower (monomialMarkedIdeal (n := n) E ((C,k+1)::F)) T :=
          ⟨trivial,isAdmissibleCentre_monomial_succ hE C hc F hf k⟩
        have heq : geoTransformAlong (monomialMarkedIdeal (n := n) E ((C,k+1)::F)) T =
            monomialMarkedIdeal (n := n) E' ((C,k)::F) :=
          geoTransform_monomial_succ hE C hc F hf k
        have hw : (monomialMarkedIdeal (n := n) E ((C,k+1)::F)).IsWellFormed :=
          isWellFormed_monomialMarkedIdeal hE _ (by
            intro p hp
            rcases List.mem_cons.mp hp with rfl|hp
            · exact hc
            · exact hf p hp)
        have he : IsSNCDivisor n E' := by
          have h := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht).isSNCDivisor
          rw [heq] at h
          exact h
        have hc' : C ∈ E' := List.mem_append_right _ (List.mem_singleton_self C)
        have hf' : ∀ p ∈ F, p.1 ∈ E' := fun p hp => mem_cartier_boundary_of_mem hE hc (hf p hp)
        obtain ⟨S,hp,hl,hr,hu⟩ := ihk E' he hc' hf'
        refine ⟨T.append S,?_,?_,?_,?_⟩
        · rw [BlowupTower.proj_append,hp]
          rfl
        · rw [BlowupTower.length_append,hl]
          change 1+(k+(F.map Prod.snd).sum) = k+1+(F.map Prod.snd).sum
          omega
        · apply IsGeoResolution.append _ ht
          rw [heq]
          exact hr
        · rw [geoTransformAlong_append,heq]
          exact hu
    intro E hE hf
    have hc : C ∈ E := hf (C,k) (by simp)
    have htail : ∀ p ∈ F, p.1 ∈ E := fun p hp => hf p (List.mem_cons_of_mem (C,k) hp)
    simpa only [List.map_cons,List.sum_cons] using hloop k E hE hc htail


/-- The genuine terminal-original Cartier step keeps EVERY old literal SNC member whole. -/
theorem map_geoStrictTransform_id_snc_append_left {E : List (Set A)} {C : Set A}
    (h : IsSNCDivisor n (E++[C])) : E.map (geoStrictTransform (id : A → A) C) = E := by
  conv_rhs => rw [← List.map_id E]
  apply List.map_congr_left
  intro W hw
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hw
  let i' : Fin (E++[C]).length := ⟨i.val,by simp only [List.length_append,List.length_singleton]; omega⟩
  let j : Fin (E++[C]).length := ⟨E.length,by simp⟩
  have hgi : (E++[C]).get i' = E.get i := by
    simp only [List.get_eq_getElem]
    exact List.getElem_append_left i.isLt
  have hgj : (E++[C]).get j = C := by
    simp only [List.get_eq_getElem]
    simp [j]
  have hij : i' ≠ j := by
    intro heq
    have hv := congrArg Fin.val heq
    change i.val = E.length at hv
    omega
  have heq := geoStrictTransform_id_snc_other h i' j hij
  rw [hgi,hgj,hi] at heq
  exact heq

/-- The actual ENTIRE terminal differential original internally yields the true Cartier blowup. -/
theorem originalTerminal_isBlowupAlong_id {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsBlowupAlong n (strictTransform n (originalSeparation hH).T.proj H)
      (id : (originalSeparation hH).D → (originalSeparation hH).D) := by
  let E := (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).E
  let C := strictTransform n (originalSeparation hH).T.proj H
  let j : Fin (E++[C]).length := ⟨E.length,by simp⟩
  have hj : (E++[C]).get j = C := by simp [List.get_eq_getElem,j]
  have h := isBlowupAlong_id_snc_member (originalSeparation_geometry hH).2.2.2.1 j
  change IsBlowupAlong n ((E++[C]).get j) id at h
  rw [hj] at h
  exact h

/-- The ENTIRE actual terminal original is admissible for the SAME actual original controlled ideal. -/
theorem originalTerminal_isAdmissibleCentre {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).IsAdmissibleCentre
      (strictTransform n (originalSeparation hH).T.proj H) :=
  ⟨(originalSeparation_geometry hH).2.1,originalSeparation_strict_subset_cosupp hH,
    (originalSeparation_geometry hH).2.2.1.hasNormalCrossings⟩

/-- The SAME actual history weights on the real terminal space, without a transported split type. -/
def originalTerminalWeights {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    List (Set (originalSeparation hH).D × ℕ) :=
  recordedOriginalWeights H 1 (originalSeparation hH).T (originalSeparation hH).centres

/-- One genuine terminal-original Cartier division leaves EXACTLY the SAME whole recorded r-1 product. -/
theorem originalTerminal_geoTransform_dictionary {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).geoTransform
      (strictTransform n (originalSeparation hH).T.proj H) id =
    monomialMarkedIdeal (n := n) (terminalBoundary hH) (originalTerminalWeights hH) := by
  let M := geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T
  let C := strictTransform n (originalSeparation hH).T.proj H
  let F := originalTerminalWeights hH
  have htest := originalSeparation_isGeoTestTower hH
  have hw : M.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isInvDomain_originalMarkedIdeal hH).isWellFormed _ htest
  have hN : M.N = univ := (pullback_eq_mul_geoTransformAlong (originalMarkedIdeal H) rfl
    (isInvDomain_originalMarkedIdeal hH).isWellFormed.isCoherent _ htest).1
  have hd : M.d = 1 := d_geoTransformAlong _ _
  have hF : ∀ p ∈ F, p.1 ∈ M.E := by
    intro p hp
    have he := recordedOriginalWeights_carriers H 1 (originalSeparation hH).T (originalSeparation hH).centres
    change F.map Prod.fst = M.E at he
    rw [← he]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hJ := invertible_componentPowerProduct_of_present hw.isSNCDivisor F hF
  have hI : M.ideal.IsInvertible := isInvertible_originalControlledIdeal hH
  have hf : M.ideal = (vanishingIdeal (n := n) C).mul (componentPowerProduct (n := n) F) := by
    have hh := higherSeparationCentres_controlled_dictionary hH (originalSeparation hH).T (originalSeparation hH).centres
    change M.ideal = (componentPowerProduct (n := n) F).mul (vanishingIdeal (n := n) C) at hh
    exact hh.trans (RestrictLeCalculus.mul_comm' _ _)
  have hp := originalTerminal_isBlowupAlong_id hH
  have hi := cartier_factor_control M hw hN hd hI hp
    (originalTerminal_isAdmissibleCentre hH) _ hJ hf
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of (geoTransform_N_eq_univ hN hp) ?_ hi hd
  change M.E.map (geoStrictTransform (id : (originalSeparation hH).D → _) C) ++ [C] = M.E++[C]
  rw [map_geoStrictTransform_id_snc_append_left (originalSeparation_geometry hH).2.2.2.1]


/-- The SAME genuine recorded history has exact carrier list and actual coefficient bounds. -/
theorem originalTerminalWeights_geometry {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalTerminalWeights hH).map Prod.fst =
      (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).E ∧
    (originalTerminalWeights hH).length = (originalSeparation hH).T.length ∧
    (∀ p ∈ originalTerminalWeights hH, 1 ≤ p.2 ∧ p.2 ≤ n-1) := by
  have hc := recordedOriginalWeights_carriers H 1 (originalSeparation hH).T (originalSeparation hH).centres
  refine ⟨hc,?_,?_⟩
  · have hh := congrArg List.length hc
    rw [List.length_map,length_E_geoTransformAlong] at hh
    simpa only [originalTerminalWeights,originalMarkedIdeal,List.length_nil,zero_add] using hh
  · exact recordedOriginalWeights_bounds H 1 (originalSeparation hH).T (originalSeparation hH).centres

private theorem sum_weights_le_mul_length {B : Type u} (F : List (B × ℕ)) (b : ℕ)
    (hb : ∀ p ∈ F, p.2 ≤ b) : (F.map Prod.snd).sum ≤ F.length*b := by
  induction F with
  | nil => simp
  | cons p F ih =>
    have hp := hb p (by simp)
    have hh := ih fun q hq => hb q (List.mem_cons_of_mem p hq)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      p.2 + (F.map Prod.snd).sum ≤ b + F.length*b := Nat.add_le_add hp hh
      _ = (F.length+1)*b := by rw [Nat.add_mul,Nat.one_mul]; omega

/-- The noncompact original inputs internally bound the sum of the ACTUAL recorded r-1 coefficients. -/
theorem originalTerminalWeights_sum_le {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ((originalTerminalWeights hH).map Prod.snd).sum ≤ (n-1)*(n-1) := by
  have hg := originalTerminalWeights_geometry hH
  exact (sum_weights_le_mul_length _ (n-1) (fun p hp => (hg.2.2 p hp).2)).trans
    (Nat.mul_le_mul_right (n-1) (hg.2.1.le.trans (originalSeparation_geometry hH).1))

/-- One true terminal-original step followed by actual internal component division gives the real same-ideal tail. -/
theorem exists_original_marked_cartier_tail {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∃ S : BlowupTower (originalSeparation hH).D (originalSeparation hH).D,
      S.proj = id ∧ S.length = 1+((originalTerminalWeights hH).map Prod.snd).sum ∧
      IsGeoResolution (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T) S ∧
      (geoTransformAlong (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T) S).ideal =
        unitIdeal n (originalSeparation hH).D := by
  let M := geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T
  let C := strictTransform n (originalSeparation hH).T.proj H
  let F := originalTerminalWeights hH
  let T : BlowupTower (originalSeparation hH).D (originalSeparation hH).D :=
    .step .refl C id (originalTerminal_isBlowupAlong_id hH)
  have ht : IsGeoTestTower M T := ⟨trivial,originalTerminal_isAdmissibleCentre hH⟩
  have heq : geoTransformAlong M T = monomialMarkedIdeal (n := n) (terminalBoundary hH) F :=
    originalTerminal_geoTransform_dictionary hH
  have hf : ∀ p ∈ F, p.1 ∈ terminalBoundary hH := by
    intro p hp
    apply List.mem_append_left
    rw [← (originalTerminalWeights_geometry hH).1]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  obtain ⟨S,hp,hl,hr,hu⟩ := exists_monomial_cartier_resolution F (terminalBoundary hH)
    (originalSeparation_geometry hH).2.2.2.1 hf
  refine ⟨T.append S,?_,?_,?_,?_⟩
  · rw [BlowupTower.proj_append,hp]
    rfl
  · rw [BlowupTower.length_append,hl]
    rfl
  · apply IsGeoResolution.append _ ht
    rw [heq]
    exact hr
  · rw [geoTransformAlong_append,heq]
    exact hu

/-- The real SAME-ideal Cartier tail is CHOSEN ONLY from its internally proved actual recursion. -/
def originalMarkedCartierTail {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    BlowupTower (originalSeparation hH).D (originalSeparation hH).D :=
  Classical.choose (exists_original_marked_cartier_tail hH)

/-- Exact true projection, length, test-resolution and COMPLETE endpoint of the internally generated tail. -/
theorem originalMarkedCartierTail_spec {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalMarkedCartierTail hH).proj = id ∧
    (originalMarkedCartierTail hH).length = 1+((originalTerminalWeights hH).map Prod.snd).sum ∧
    IsGeoResolution (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T)
      (originalMarkedCartierTail hH) ∧
    (geoTransformAlong (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T)
      (originalMarkedCartierTail hH)).ideal = unitIdeal n (originalSeparation hH).D :=
  Classical.choose_spec (exists_original_marked_cartier_tail hH)

/-- The genuine original tower followed by its actual SAME-ideal internally finite Cartier completion. -/
def originalMarkedCompletion {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    BlowupTower A (originalSeparation hH).D :=
  (originalSeparation hH).T.append (originalMarkedCartierTail hH)

/-- The actual complete finite tower resolves the SAME original marked datum. -/
theorem originalMarkedCompletion_isGeoResolution {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsGeoResolution (originalMarkedIdeal H) (originalMarkedCompletion hH) :=
  IsGeoResolution.append _ (originalSeparation_isGeoTestTower hH) (originalMarkedCartierTail_spec hH).2.2.1

/-- The COMPLETE actual same-original controlled ideal at the real endpoint is unit. -/
theorem originalMarkedCompletion_ideal_eq_unit {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (geoTransformAlong (originalMarkedIdeal H) (originalMarkedCompletion hH)).ideal =
      unitIdeal n (originalSeparation hH).D := by
  rw [originalMarkedCompletion,geoTransformAlong_append]
  exact (originalMarkedCartierTail_spec hH).2.2.2

/-- The real Cartier completion projection is EXACTLY the actual prior separation projection. -/
theorem originalMarkedCompletion_proj {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalMarkedCompletion hH).proj = (originalSeparation hH).T.proj := by
  rw [originalMarkedCompletion,BlowupTower.proj_append,(originalMarkedCartierTail_spec hH).1]
  rfl

/-- Exact tail length is distinct from the complete original tower length. -/
theorem originalMarkedCompletion_length {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalMarkedCompletion hH).length = (originalSeparation hH).T.length +
      1+((originalTerminalWeights hH).map Prod.snd).sum := by
  rw [originalMarkedCompletion,BlowupTower.length_append,(originalMarkedCartierTail_spec hH).2.1]
  omega

/-- True noncompact Cartier tail length bound comes ONLY from actual NC multiplicities and actual generated length. -/
theorem originalMarkedCartierTail_length_le {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalMarkedCartierTail hH).length ≤ 1+(n-1)*(n-1) := by
  rw [(originalMarkedCartierTail_spec hH).2.1]
  exact Nat.add_le_add_left (originalTerminalWeights_sum_le hH) 1

/-- The entire genuine original tower has its internally finite length bound, with n=0 and literal empty steps retained. -/
theorem originalMarkedCompletion_length_le {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalMarkedCompletion hH).length ≤ 1+n*(n-1) := by
  rw [originalMarkedCompletion_length]
  have hsum := originalTerminalWeights_sum_le hH
  have hlen := (originalSeparation_geometry hH).1
  cases n with
  | zero => simp only [Nat.zero_sub,Nat.mul_zero] at *; omega
  | succ k =>
    simp only [Nat.add_sub_cancel] at hsum hlen ⊢
    have heq : 1+(k+1)*k = k+1+k*k := by rw [Nat.add_mul,Nat.one_mul]; omega
    rw [heq]
    omega

/-- EVERY literal prefix of the generated complete tower internally has the actual original marked domain. -/
theorem originalMarkedCompletion_prefix_domain {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    Hironaka.ResolutionInvariantSpec.IsInvDomain n
      (geoTransformAlong (originalMarkedIdeal H) (BlowupTowerSplit.head (originalMarkedCompletion hH) i)) := by
  have hh := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail (originalMarkedIdeal H)
    (originalMarkedCompletion hH) i).mp (originalMarkedCompletion_isGeoResolution hH).1).1
  exact InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_originalMarkedIdeal hH) _ hh

/-- The true SNC boundary holds at EVERY literal actual prefix, including every retained empty/repeated historical entry. -/
theorem originalMarkedCompletion_prefix_snc {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    IsSNCDivisor n
      (geoTransformAlong (originalMarkedIdeal H) (BlowupTowerSplit.head (originalMarkedCompletion hH) i)).E :=
  (originalMarkedCompletion_prefix_domain hH i).isWellFormed.isSNCDivisor

/-- COMPLETE actual boundary length retains ALL actual steps, even empty centres or repeated carrier history. -/
theorem originalMarkedCompletion_boundary_length {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (geoTransformAlong (originalMarkedIdeal H) (originalMarkedCompletion hH)).E.length =
      (originalMarkedCompletion hH).length := by
  simpa only [originalMarkedIdeal,List.length_nil,zero_add] using
    length_E_geoTransformAlong (originalMarkedIdeal H) (originalMarkedCompletion hH)


/-- The full original complement isomorphism is preserved by the actual identity Cartier completion. -/
theorem originalMarkedCompletion_isIsomorphismOver {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsIsomorphismOver n (originalMarkedCompletion hH).proj Hᶜ := by
  rw [originalMarkedCompletion_proj]
  exact (originalSeparation_geometry hH).2.2.2.2.2

/-- The SAME original marked cosupport is genuinely empty at the real complete endpoint. -/
theorem originalMarkedCompletion_cosupp_eq_empty {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (geoTransformAlong (originalMarkedIdeal H) (originalMarkedCompletion hH)).cosupp = ∅ :=
  (originalMarkedCompletion_isGeoResolution hH).2

/-- In dimension zero the ACTUAL generated whole tower has exactly one genuine retained empty Cartier step. -/
theorem originalMarkedCompletion_dimension_zero {A₀ : CMfd.{u} 0} {H₀ : Set A₀}
    (hH : IsNormalCrossingsCarrier (n := 0) H₀) :
    (originalMarkedCartierTail hH).length = 1 ∧ (originalMarkedCompletion hH).length = 1 ∧
    (geoTransformAlong (originalMarkedIdeal H₀) (originalMarkedCompletion hH)).E = [∅] := by
  have hs : (originalSeparation hH).T.length = 0 := Nat.eq_zero_of_le_zero (originalSeparation_geometry hH).1
  have hf : originalTerminalWeights hH = [] := List.length_eq_zero_iff.mp
    ((originalTerminalWeights_geometry hH).2.1.trans hs)
  have ht : (originalMarkedCartierTail hH).length = 1 := by
    rw [(originalMarkedCartierTail_spec hH).2.1,hf]
    rfl
  have hl : (originalMarkedCompletion hH).length = 1 := by
    rw [originalMarkedCompletion_length,hs,hf]
    rfl
  refine ⟨ht,hl,?_⟩
  have hlen : (geoTransformAlong (originalMarkedIdeal H₀) (originalMarkedCompletion hH)).E.length = 1 :=
    (originalMarkedCompletion_boundary_length hH).trans hl
  obtain ⟨C,hC⟩ := List.length_eq_one_iff.mp hlen
  have he : IsSNCDivisor 0 [C] := by
    have hh := (InvDomainTowerAlong.isInvDomain_geoTransformAlong
      (isInvDomain_originalMarkedIdeal hH) _ (originalMarkedCompletion_isGeoResolution hH).1).isWellFormed.isSNCDivisor
    rw [hC] at hh
    exact hh
  have hc : C = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨S,_,hcard,_⟩ := he.2 x
    let i : Fin [C].length := ⟨0,by simp⟩
    have hci : x ∈ [C].get i := hx
    have hb := Finset.card_le_univ (S i)
    have h1 := hcard i hci
    simp only [Fintype.card_fin] at hb
    omega
  rw [hC,hc]

end
end Hironaka.HironakaNormalCrossingsFiniteMarkedCompletion

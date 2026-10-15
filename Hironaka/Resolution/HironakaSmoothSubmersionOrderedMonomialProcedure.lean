/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionNormalCrossings

/-! # Actual independent finite ordered monomial procedures under smooth submersions

The unchanged old-gamma singleton key internally selects each actual nonempty
maximum Cartier member. Genuine identity blowups and whole controlled products
produce an actual bounded tower from original SNC alone. Its OWN coefficient
sum internally supplies termination, canonical segment, true test resolution
and whole unit endpoint, in every dimension without compactness. Actual append
factorization identifies bounded runs as genuine geometric prefixes.
Independent procedures under genuine surjective submersions have the SAME
literal index word, entire preimage state and centre histories, genuine whole
controlled marked prefix dictionaries, lengths, projections and unit endpoints.
Whole finite-list identities supply actual identity and composition coherence.
All empty or repeated historical entries remain literal. General higher
invariant functoriality, identifying prior separation with the old general
driver, arbitrary blowup choices and nonsurjective compression remain OPEN.
Blueprint: `hironaka-smooth-submersion-ordered-monomial-procedure-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOrderedMonomialProcedure
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothSubmersionNormalCrossings HironakaNormalCrossingsOrderedMonomialTail
  HironakaNormalCrossingsFiniteMarkedCompletion NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  MonomialCase MonomialInvariant IdealWeightPowers DivisorExponent
  HironakaDivisorResidual BlowupTowerTransforms HironakaSmoothSubmersionCoefficientIdeals
noncomputable section

variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

omit [TopologicalSpace X] in
/-- Only the actual finite positive nonempty family supplies its unique literal old-key index. -/
def selectedIndex (n : ℕ) (F : List (Set X × ℕ)) : Option (Fin F.length) :=
  if h : activeIndices F = ∅ then none else
    some (Classical.choose ((exists_actual_maximum_index (n := n) F).resolve_left h))

omit [TopologicalSpace X] in
/-- The actual procedure stops exactly at its genuine inactive family. -/
theorem selectedIndex_eq_none_iff (F : List (Set X × ℕ)) :
    selectedIndex n F = none ↔ activeIndices F = ∅ := by
  classical
  unfold selectedIndex
  split_ifs <;> simp_all

omit [TopologicalSpace X] in
/-- Every real selection is active and is its complete unique old singleton maximum. -/
theorem selectedIndex_some_spec (F : List (Set X × ℕ)) {j : Fin F.length}
    (hj : selectedIndex n F = some j) :
    j ∈ activeIndices F ∧
      (∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j) ∧
      ∀ k ∈ activeIndices F, (∀ i ∈ activeIndices F,
        singletonKey (n := n) F i ≤ singletonKey (n := n) F k) → k = j := by
  classical
  by_cases he : activeIndices F = ∅
  · simp [selectedIndex,he] at hj
  · have hj' : Classical.choose ((exists_actual_maximum_index (n := n) F).resolve_left he) = j := by
      simpa only [selectedIndex,dif_neg he,Option.some.injEq] using hj
    rw [← hj']
    exact Classical.choose_spec ((exists_actual_maximum_index (n := n) F).resolve_left he)

omit [TopologicalSpace X] in
/-- Actual singleton uniqueness identifies independent selections without a caller choice certificate. -/
theorem selectedIndex_eq_some_of_maximum (F : List (Set X × ℕ)) (j : Fin F.length)
    (hj : j ∈ activeIndices F)
    (hm : ∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j) :
    selectedIndex n F = some j := by
  classical
  have he : activeIndices F ≠ ∅ := Finset.ne_empty_of_mem hj
  unfold selectedIndex
  rw [dif_neg he]
  apply congrArg some
  exact (Classical.choose_spec ((exists_actual_maximum_index (n := n) F).resolve_left he)).2.2 j hj hm |>.symm

/-- Two independent actual singleton selections transport by genuine surjective geometry. -/
theorem selectedIndex_pullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    selectedIndex m (pulledWeights f F) = (selectedIndex n F).map (pulledIndex f F) := by
  classical
  rcases exists_common_actual_gamma_maximum_centre hf hsurj F hF with ⟨he,he'⟩|⟨j,hj,hj',_,_,hm,hm',_,_⟩
  · rw [(selectedIndex_eq_none_iff F).mpr he,
      (selectedIndex_eq_none_iff (pulledWeights f F)).mpr he']
    rfl
  · rw [selectedIndex_eq_some_of_maximum F j hj hm,
      selectedIndex_eq_some_of_maximum (pulledWeights f F) (pulledIndex f F j) hj' hm']
    rfl

omit [TopologicalSpace X] in
/-- Literal original coefficient sum is internally available as finite fuel. -/
def coefficientSum (F : List (Set X × ℕ)) : ℕ := (F.map Prod.snd).sum

omit [TopologicalSpace X] in
/-- Actual bounded recursion records every complete state, without deleting historical entries. -/
def stateTrace (n : ℕ) : ℕ → List (Set X × ℕ) → List (List (Set X × ℕ))
  | 0,F => [F]
  | q+1,F => match selectedIndex n F with
    | none => [F]
    | some j => F :: stateTrace n q (dividedWeights F j)

omit [TopologicalSpace X] in
/-- The genuine selected whole Cartier carriers of the same actual recursion. -/
def centreTrace (n : ℕ) : ℕ → List (Set X × ℕ) → List (Set X)
  | 0,_ => []
  | q+1,F => match selectedIndex n F with
    | none => []
    | some j => (F.get j).1 :: centreTrace n q (dividedWeights F j)

omit [TopologicalSpace X] in
/-- The entire literal natural index word, including all growing old colex indices. -/
def indexTrace (n : ℕ) : ℕ → List (Set X × ℕ) → List ℕ
  | 0,_ => []
  | q+1,F => match selectedIndex n F with
    | none => []
    | some j => j.val :: indexTrace n q (dividedWeights F j)

omit [TopologicalSpace X] in
/-- The actual terminal WHOLE coefficient/carrier state of that same finite recursion. -/
def terminalState (n : ℕ) : ℕ → List (Set X × ℕ) → List (Set X × ℕ)
  | 0,F => F
  | q+1,F => match selectedIndex n F with
    | none => F
    | some j => terminalState n q (dividedWeights F j)

omit [TopologicalSpace X] in
/-- The actual recorded terminal state has its precise inactive-branch equation. -/
theorem terminalState_succ_none (q : ℕ) (F : List (Set X × ℕ)) (hs : selectedIndex n F = none) :
    terminalState n (q+1) F = F := by
  conv_lhs => unfold terminalState
  rw [hs]

omit [TopologicalSpace X] in
/-- The actual recorded terminal state has its precise selected-successor equation. -/
theorem terminalState_succ_some (q : ℕ) (F : List (Set X × ℕ)) (j : Fin F.length)
    (hs : selectedIndex n F = some j) :
    terminalState n (q+1) F = terminalState n q (dividedWeights F j) := by
  conv_lhs => unfold terminalState
  rw [hs]

/-- A real selected index internally produces the whole actual old-gamma centre, with no dimension certificate. -/
theorem selectedIndex_actual_centre (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : selectedIndex n F = some j) :
    (F.get j).1.Nonempty ∧
      (F.get j).1 = ResolutionDriver.maxLocus
        (gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1)
        (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp := by
  classical
  obtain ⟨hja,hm,_⟩ := selectedIndex_some_spec F hj
  obtain ⟨_,hp,hne⟩ := Finset.mem_filter.mp hja
  obtain ⟨x,hx⟩ := hne
  obtain ⟨S,_,hc,_⟩ := hF.2 x
  let j' : Fin (F.map Prod.fst).length := ⟨j.val,by simp only [List.length_map]; exact j.isLt⟩
  have hx' : x ∈ (F.map Prod.fst).get j' := by simpa [List.get_eq_getElem,j'] using hx
  have hcard := hc j' hx'
  have hle := Finset.card_le_univ (S j')
  simp only [Fintype.card_fin] at hle
  have hn : 0 < n := by omega
  have he : activeIndices F ≠ ∅ := Finset.ne_empty_of_mem hja
  obtain ⟨k,hk,hcentre,_,hu⟩ := (exists_actual_gamma_maximum_centre hn F hF).resolve_left he
  have heq := hu j hja hm
  rw [← heq] at hcentre
  exact ⟨⟨x,hx⟩,hcentre.symm⟩

section Towers
variable {A : CMfd.{u} n}

open Classical in
/-- Genuine finite recursion produces actual universal-property Cartier blowups from the original SNC input alone. -/
def procedureTower : ∀ (_q : ℕ) (F : List (Set A × ℕ)),
    IsSNCDivisor n (F.map Prod.fst) → BlowupTower A A
  | 0,_,_ => .refl
  | q+1,F,hF =>
    match hs : selectedIndex n F with
    | none => .refl
    | some j =>
      let hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      let hD := dividedWeights_isSNCDivisor F hF j hj
      (BlowupTower.step BlowupTower.refl (F.get j).1 id
        (isBlowupAlong_id_indexed_member F hF j)).append
          (procedureTower q (dividedWeights F j) hD)

/-- The true projection of every actually generated finite prefix is the identity. -/
theorem procedureTower_proj (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (procedureTower q F hF).proj = id := by
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    unfold procedureTower
    split
    · rfl
    · rw [BlowupTower.proj_append,ih]
      rfl

/-- Every actual generated tower has exactly its real recorded finite centre-history length. -/
theorem procedureTower_length (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (procedureTower q F hF).length = (centreTrace n q F).length := by
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    unfold procedureTower centreTrace
    split
    · rename_i hs
      rw [hs]
      rfl
    · rename_i j hs
      conv_rhs => rw [hs]
      rw [BlowupTower.length_append,ih]
      simp only [BlowupTower.length,List.length_cons]
      omega

/-- The entire actual terminal marked datum is its genuine controlled transform along the SAME produced tower. -/
theorem procedureTower_marked_dictionary (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF) =
      monomialMarkedIdeal (n := n) ((terminalState n q F).map Prod.fst) (terminalState n q F) := by
  classical
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    unfold procedureTower terminalState
    split
    · rename_i hs
      rw [hs]
      rfl
    · rename_i j hs
      conv_rhs => rw [hs]
      rw [geoTransformAlong_append]
      change geoTransformAlong
        ((monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 id) _ = _
      rw [geoTransform_indexed_positive F hF j
        (((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1),ih]

private theorem canonical_append {D B : CMfd.{u} n} (I : MarkedIdeal n A)
    (T : BlowupTower A D) (S : BlowupTower D B)
    (hT : ResolutionDriver.IsCanonicalSegment I (fun {V} R => MonomialStepAlong.towerInvAlong I (Y := V) R) T)
    (hS : ResolutionDriver.IsCanonicalSegment (geoTransformAlong I T)
      (fun {V} R => MonomialStepAlong.towerInvAlong (geoTransformAlong I T) (Y := V) R) S) :
    ResolutionDriver.IsCanonicalSegment I (fun {V} R => MonomialStepAlong.towerInvAlong I (Y := V) R) (T.append S) := by
  induction S with
  | refl => exact hT
  | step S C π hπ ih =>
    obtain ⟨hs,hne,hc⟩ := hS
    refine ⟨ih hs,hne,?_⟩
    change C = ResolutionDriver.maxLocus (MonomialStepAlong.towerInvAlong I (T.append S))
      (geoTransformAlong I (T.append S)).cosupp
    unfold MonomialStepAlong.towerInvAlong
    rw [geoTransformAlong_append]
    exact hc

/-- EVERY actually generated bounded tower is the unchanged old-gamma canonical segment. -/
theorem procedureTower_isCanonicalSegment (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ResolutionDriver.IsCanonicalSegment (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (fun {V} R => MonomialStepAlong.towerInvAlong
        (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (Y := V) R) (procedureTower q F hF) := by
  classical
  induction q generalizing F with
  | zero => trivial
  | succ q ih =>
    unfold procedureTower
    split
    · trivial
    · rename_i j hs
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hc := selectedIndex_actual_centre F hF j hs
      have hstep : ResolutionDriver.IsCanonicalSegment
          (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (fun {V} R => MonomialStepAlong.towerInvAlong
            (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (Y := V) R)
          (BlowupTower.step BlowupTower.refl (F.get j).1 id (isBlowupAlong_id_indexed_member F hF j)) := by
        refine ⟨trivial,hc.1,?_⟩
        change (F.get j).1 = ResolutionDriver.maxLocus
          (MonomialCaseAlong.gammaAlong n univ (componentPowerProduct (n := n) F) (F.map Prod.fst) 1)
          (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp
        have hγ : (MonomialCaseAlong.gammaAlong n univ (componentPowerProduct (n := n) F)
            (F.map Prod.fst) 1 : A → WithBot Val) =
              gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1 :=
          funext fun z => MonomialCaseAlong.gammaAlong_univ 1 z
        rw [hγ]
        exact hc.2
      apply canonical_append _ _ _ hstep
      have he : geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (BlowupTower.step BlowupTower.refl (F.get j).1 id (isBlowupAlong_id_indexed_member F hF j)) =
          monomialMarkedIdeal (n := n) ((dividedWeights F j).map Prod.fst) (dividedWeights F j) :=
        geoTransform_indexed_positive F hF j hj
      rw [he]
      exact ih _ _

/-- Genuine selected-factor admissibility internally makes EVERY bounded procedure a real marked test tower. -/
theorem procedureTower_isGeoTestTower (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoTestTower (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF) := by
  classical
  induction q generalizing F with
  | zero => trivial
  | succ q ih =>
    unfold procedureTower
    split
    · trivial
    · rename_i j hs
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      apply (isGeoTestTower_append_iff _ _ _).mpr
      refine ⟨⟨trivial,isAdmissibleCentre_indexed_positive F hF j hj⟩,?_⟩
      change IsGeoTestTower ((monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 id) _
      rw [geoTransform_indexed_positive F hF j hj]
      exact ih _ _

/-- Every bounded generated tower has its genuine internally computed global coefficient length bound. -/
theorem procedureTower_length_le_sum (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (procedureTower q F hF).length ≤ coefficientSum F := by
  classical
  induction q generalizing F with
  | zero => exact Nat.zero_le _
  | succ q ih =>
    unfold procedureTower
    split
    · exact Nat.zero_le _
    · rename_i j hs
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      rw [BlowupTower.length_append]
      have hl := ih (dividedWeights F j) (dividedWeights_isSNCDivisor F hF j hj)
      have hd := dividedWeights_sum_add_one F j hj
      change 1+(procedureTower q (dividedWeights F j) _).length ≤ (F.map Prod.snd).sum
      unfold coefficientSum at hl
      omega

private theorem terminalState_inactive_of_sum_le (q : ℕ) (F : List (Set A × ℕ))
    (hq : coefficientSum F ≤ q) : activeIndices (terminalState n q F) = ∅ := by
  classical
  induction q generalizing F with
  | zero =>
    change activeIndices F = ∅
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hp := ((Finset.mem_filter.mp hj).2).1
    have hs := ((List.getElem_cons_eraseIdx_perm (l := F) j.isLt).map Prod.snd).sum_eq
    simp only [List.map_cons,List.sum_cons] at hs
    change (F.get j).2+(F.eraseIdx j.val |>.map Prod.snd).sum = (F.map Prod.snd).sum at hs
    unfold coefficientSum at hq
    omega
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none =>
      rw [terminalState_succ_none q F hs]
      exact (selectedIndex_eq_none_iff F).mp hs
    | some j =>
      rw [terminalState_succ_some q F j hs]
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      apply ih
      have hd := dividedWeights_sum_add_one F j hj
      unfold coefficientSum at hq ⊢
      omega

/-- The procedure using its OWN actual coefficient sum has a complete whole unit endpoint. -/
theorem procedureTower_ideal_eq_unit (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (procedureTower (coefficientSum F) F hF)).ideal = unitIdeal n A := by
  rw [procedureTower_marked_dictionary]
  have hsnc := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)) _
    (procedureTower_isGeoTestTower (coefficientSum F) F hF)).isSNCDivisor
  rw [procedureTower_marked_dictionary] at hsnc
  exact indexed_product_eq_unit_of_no_active _ hsnc (terminalState_inactive_of_sum_le _ F le_rfl)

/-- SAME internally bounded finite recursion gives an actual original resolution, with no compactness or termination input. -/
theorem procedureTower_isGeoResolution (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoResolution (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (procedureTower (coefficientSum F) F hF) := by
  refine ⟨procedureTower_isGeoTestTower _ F hF,?_⟩
  change GermIdealOrder.cosupport n _ _ _ = ∅
  have hd : (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (procedureTower (coefficientSum F) F hF)).d = 1 := by rw [procedureTower_marked_dictionary]; rfl
  have hN : (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (procedureTower (coefficientSum F) F hF)).N = univ := by rw [procedureTower_marked_dictionary]; rfl
  rw [procedureTower_ideal_eq_unit F hF,hd,hN]
  exact GermIdealOrder.cosupport_unitIdeal le_rfl

/-- Original SNC internally supplies the ENTIRE actual terminal boundary for every bounded run. -/
theorem terminalState_isSNCDivisor (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSNCDivisor n ((terminalState n q F).map Prod.fst) := by
  have h := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)) _
    (procedureTower_isGeoTestTower q F hF)).isSNCDivisor
  rw [procedureTower_marked_dictionary] at h
  exact h

/-- EVERY literal head of the genuinely generated tower has the complete actual original marked domain. -/
theorem procedureTower_prefix_domain (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (i : ℕ) :
    ResolutionInvariantSpec.IsInvDomain n (geoTransformAlong
      (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (BlowupTowerSplit.head (procedureTower q F hF) i)) :=
  InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (isInvDomain_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)) _
    (((BlowupTowerSplit.isGeoTestTower_iff_head_tail
      (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF) i).mp
      (procedureTower_isGeoTestTower q F hF)).1)

/-- EVERY real literal head retains its genuine entire SNC boundary history. -/
theorem procedureTower_prefix_snc (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (i : ℕ) :
    IsSNCDivisor n (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (BlowupTowerSplit.head (procedureTower q F hF) i)).E :=
  (procedureTower_prefix_domain q F hF i).isWellFormed.isSNCDivisor

/-- True inactive states produce the actual reflexive tower for EVERY finite fuel. -/
theorem procedureTower_eq_refl_of_none (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (he : selectedIndex n F = none) :
    procedureTower q F hF = BlowupTower.refl := by
  cases q with
  | zero => rfl
  | succ q =>
    unfold procedureTower
    split
    · rfl
    · rename_i j hs
      have h := he.symm.trans hs
      contradiction


open Classical in
/-- The true procedure's actually selected successor records its SAME genuine first Cartier step and smaller tail. -/
theorem procedureTower_succ_some (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hs : selectedIndex n F = some j) :
    procedureTower (q+1) F hF =
      (BlowupTower.step BlowupTower.refl (F.get j).1 id (isBlowupAlong_id_indexed_member F hF j)).append
        (procedureTower q (dividedWeights F j) (dividedWeights_isSNCDivisor F hF j
          (((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1))) := by
  conv_lhs => unfold procedureTower
  split
  · rename_i he
    have h := he.symm.trans hs
    contradiction
  · rename_i k hk
    have heq : k = j := Option.some.inj (hk.symm.trans hs)
    subst k
    rfl

private theorem procedureTower_congr_state (q : ℕ) (F G : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (hG : IsSNCDivisor n (G.map Prod.fst)) (he : F = G) :
    procedureTower q F hF = procedureTower q G hG := by
  subst G
  rfl

/-- Actual sequential recursion factorizes after every internally generated bounded prefix. -/
theorem procedureTower_add (p q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    procedureTower (p+q) F hF = (procedureTower p F hF).append
      (procedureTower q (terminalState n p F) (terminalState_isSNCDivisor p F hF)) := by
  classical
  induction p generalizing F with
  | zero => simp only [Nat.zero_add,procedureTower,terminalState,BlowupTower.refl_append]
  | succ p ih =>
    cases hs : selectedIndex n F with
    | none =>
      have ht := procedureTower_congr_state q (terminalState n (p+1) F) F
        (terminalState_isSNCDivisor (p+1) F hF) hF (terminalState_succ_none p F hs)
      rw [procedureTower_eq_refl_of_none _ F hF hs,procedureTower_eq_refl_of_none _ F hF hs,ht,
        procedureTower_eq_refl_of_none q F hF hs]
      rfl
    | some j =>
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hD := dividedWeights_isSNCDivisor F hF j hj
      have ht := procedureTower_congr_state q (terminalState n (p+1) F)
        (terminalState n p (dividedWeights F j)) (terminalState_isSNCDivisor (p+1) F hF)
        (terminalState_isSNCDivisor p (dividedWeights F j) hD) (terminalState_succ_some p F j hs)
      rw [Nat.succ_add,procedureTower_succ_some (p+q) F hF j hs,
        procedureTower_succ_some p F hF j hs,ht,ih,BlowupTower.append_assoc]

/-- EVERY real bounded initial run is an actual prefix of the internally completed tower. -/
theorem procedureTower_isPrefix_of_completion (p : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (hp : p ≤ coefficientSum F) :
    ∃ S : BlowupTower A A, (procedureTower p F hF).append S = procedureTower (coefficientSum F) F hF := by
  refine ⟨procedureTower (coefficientSum F-p) (terminalState n p F) (terminalState_isSNCDivisor p F hF),?_⟩
  rw [← procedureTower_add,Nat.add_sub_of_le hp]

end Towers

/-- Actual independent bounded runs have the complete literal state, centre, index and terminal preimage dictionary. -/
theorem bounded_history_pullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (q : ℕ) (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    stateTrace m q (pulledWeights f F) = (stateTrace n q F).map (pulledWeights f) ∧
    centreTrace m q (pulledWeights f F) = (centreTrace n q F).map (f ⁻¹' ·) ∧
    indexTrace m q (pulledWeights f F) = indexTrace n q F ∧
    terminalState m q (pulledWeights f F) = pulledWeights f (terminalState n q F) := by
  classical
  induction q generalizing F with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ q ih =>
    have hsel := selectedIndex_pullback hf hsurj F hF
    simp only [stateTrace,centreTrace,indexTrace,terminalState,hsel]
    cases hs : selectedIndex n F with
    | none => exact ⟨rfl,rfl,rfl,rfl⟩
    | some j =>
      simp only [Option.map_some]
      rw [← pulledWeights_dividedWeights]
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hD := dividedWeights_isSNCDivisor (A := CMfd.of (n := n) X) F hF j hj
      obtain ⟨hstate,hcentre,hindex,hterminal⟩ := ih (dividedWeights F j) hD
      refine ⟨?_,?_,?_,hterminal⟩
      · rw [hstate,List.map_cons]
      · rw [hcentre,List.map_cons,pulledWeights_get]
      · rw [hindex]
        rfl

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- The two procedures internally compute exactly the SAME true finite fuel. -/
theorem coefficientSum_pulled (f : Y → X) (F : List (Set X × ℕ)) :
    coefficientSum (pulledWeights f F) = coefficientSum F := by
  unfold coefficientSum
  rw [pulledWeights_powers]

/-- Entire actual completed state histories transport without any caller run or termination input. -/
theorem completed_history_pullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    stateTrace m (coefficientSum (pulledWeights f F)) (pulledWeights f F) =
      (stateTrace n (coefficientSum F) F).map (pulledWeights f) ∧
    centreTrace m (coefficientSum (pulledWeights f F)) (pulledWeights f F) =
      (centreTrace n (coefficientSum F) F).map (f ⁻¹' ·) ∧
    indexTrace m (coefficientSum (pulledWeights f F)) (pulledWeights f F) =
      indexTrace n (coefficientSum F) F ∧
    terminalState m (coefficientSum (pulledWeights f F)) (pulledWeights f F) =
      pulledWeights f (terminalState n (coefficientSum F) F) := by
  rw [coefficientSum_pulled]
  exact bounded_history_pullback hf hsurj _ F hF

section GeometricNaturality
variable {A : CMfd.{u} n} {B : CMfd.{u} m}

/-- Every corresponding independently generated geometric prefix has its ENTIRE actual controlled marked pullback dictionary. -/
theorem bounded_controlled_marked_pullback {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    markedPullback (m := m) f
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)) =
      geoTransformAlong (markedPullback (m := m) f
        (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
        (procedureTower q (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)) := by
  rw [markedPullback_indexed_dictionary hf F hF]
  simp only [procedureTower_marked_dictionary]
  rw [markedPullback_indexed_dictionary hf (terminalState n q F) (terminalState_isSNCDivisor q F hF)]
  rw [(bounded_history_pullback hf hsurj q F hF).2.2.2]

/-- The two internally completed actual geometric towers have exactly equal lengths. -/
theorem completed_procedure_length_pullback {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (procedureTower (coefficientSum (pulledWeights f F)) (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).length =
      (procedureTower (coefficientSum F) F hF).length := by
  simp only [procedureTower_length]
  rw [(completed_history_pullback hf hsurj F hF).2.1,List.length_map]

/-- Genuine projections of the two independently built actual complete towers commute with the original smooth map. -/
theorem completed_procedure_projections_commute {f : B → A}
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    f ∘ (procedureTower (coefficientSum (pulledWeights f F)) (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).proj =
      (procedureTower (coefficientSum F) F hF).proj ∘ f := by
  rw [procedureTower_proj,procedureTower_proj]
  rfl

/-- The genuine unit endpoints of the two internally terminated runs have the complete marked pullback identity. -/
theorem completed_controlled_marked_pullback {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    markedPullback (m := m) f
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
        (procedureTower (coefficientSum F) F hF)) =
      geoTransformAlong (markedPullback (m := m) f
        (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
        (procedureTower (coefficientSum (pulledWeights f F)) (pulledWeights f F)
          (pulledWeights_isSNCDivisor hf F hF)) := by
  rw [coefficientSum_pulled]
  exact bounded_controlled_marked_pullback hf hsurj _ F hF

end GeometricNaturality

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Exact literal coefficient histories obey actual composition, with every empty and repeated entry retained. -/
theorem pulledWeights_comp {Z : Type u} (f : Y → X) (g : Z → Y) (F : List (Set X × ℕ)) :
    pulledWeights (f ∘ g) F = pulledWeights g (pulledWeights f F) := by
  simp only [pulledWeights,List.map_map,Function.comp_def]
  rfl

omit [TopologicalSpace X] in
/-- Exact literal identity keeps the complete original indexed coefficient state. -/
theorem pulledWeights_id (F : List (Set X × ℕ)) : pulledWeights id F = F := by
  simp only [pulledWeights,Set.preimage_id_eq]
  induction F with
  | nil => rfl
  | cons p F ih =>
    rcases p with ⟨C,a⟩
    simp only [List.map_cons] at ih ⊢
    rw [ih]
    rfl

/-- Independent actual histories satisfy the whole literal cocycle for two genuine surjective smooth maps. -/
theorem completed_history_composition {k : ℕ} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] {f : Y → X} {g : Z → Y}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) ∞ g)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g) (F : List (Set X × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    stateTrace k (coefficientSum (pulledWeights (f ∘ g) F)) (pulledWeights (f ∘ g) F) =
      (stateTrace n (coefficientSum F) F).map (pulledWeights (f ∘ g)) ∧
    centreTrace k (coefficientSum (pulledWeights (f ∘ g) F)) (pulledWeights (f ∘ g) F) =
      (centreTrace n (coefficientSum F) F).map ((f ∘ g) ⁻¹' ·) ∧
    indexTrace k (coefficientSum (pulledWeights (f ∘ g) F)) (pulledWeights (f ∘ g) F) =
      indexTrace n (coefficientSum F) F ∧
    terminalState k (coefficientSum (pulledWeights (f ∘ g) F)) (pulledWeights (f ∘ g) F) =
      pulledWeights (f ∘ g) (terminalState n (coefficientSum F) F) := by
  have hpF := pulledWeights_isSNCDivisor hf F hF
  obtain ⟨hfstate,hfcentre,hfindex,hfterm⟩ := completed_history_pullback hf hsf F hF
  obtain ⟨hgstate,hgcentre,hgindex,hgterm⟩ := completed_history_pullback hg hsg (pulledWeights f F) hpF
  rw [pulledWeights_comp]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hgstate,hfstate,List.map_map]
    apply List.map_congr_left
    intro G hG
    exact (pulledWeights_comp f g G).symm
  · rw [hgcentre,hfcentre,List.map_map]
    rfl
  · rw [hgindex,hfindex]
  · rw [hgterm,hfterm,← pulledWeights_comp]

omit [TopologicalSpace X] in
/-- The independently defined procedure has literal identity histories and exact original terminal state. -/
theorem completed_history_identity (F : List (Set X × ℕ)) :
    stateTrace n (coefficientSum (pulledWeights id F)) (pulledWeights id F) = stateTrace n (coefficientSum F) F ∧
    centreTrace n (coefficientSum (pulledWeights id F)) (pulledWeights id F) = centreTrace n (coefficientSum F) F ∧
    indexTrace n (coefficientSum (pulledWeights id F)) (pulledWeights id F) = indexTrace n (coefficientSum F) F ∧
    terminalState n (coefficientSum (pulledWeights id F)) (pulledWeights id F) = terminalState n (coefficientSum F) F := by
  rw [pulledWeights_id]
  exact ⟨rfl,rfl,rfl,rfl⟩

end
end Hironaka.HironakaSmoothSubmersionOrderedMonomialProcedure

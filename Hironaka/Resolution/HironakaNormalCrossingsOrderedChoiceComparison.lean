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
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedMonomialProcedure
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison

/-! # Actual finite ordered monomial procedures with arbitrary genuine Cartier choices

Only original entire indexed SNC data and genuine primitive Cartier blowup
choices are inputs. Actual unique global Cartier inverses, whole marked
successors and every selected old-key maximum are internally produced.
The independent chosen bounded procedure constructs all actual manifolds,
blowups, whole literal weights and true projection inverses. Its OWN original
coefficient sum internally gives old-gamma canonicality, test resolution,
whole unit endpoint, exact coefficient accounting and genuine finite length.
Actual simultaneous tower comparison to the independent identity procedure
produces UNIQUE real two-choice comparisons with whole marked dictionaries,
full literal index words and actual identity/inverse/composition cocycles.
All empty/repeated historical entries remain literal. Higher invariant and
prior general-separation identification with the old general driver remain
OPEN; unrelated arbitrary ideal admissibility is not inferred.
Blueprint: `hironaka-normal-crossings-ordered-choice-comparison-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsOrderedChoiceComparison
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  NormalCrossings BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaNormalCrossingsFiniteMarkedCompletion HironakaNormalCrossingsOrderedMonomialTail
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionOrderedMonomialProcedure
  HironakaNormalCrossingsSeparationChoiceComparison HironakaDivisorResidual IdealWeightPowers
  MarkedIdealBiholomorphism MarkedIdealTowerTransport BlowupTowerIsomorphism
noncomputable section
variable {n : ℕ} {A B : CMfd.{u} n}

/-- Genuine biholomorphic geometry internally supplies the entire literal pulled SNC family. -/
theorem pulledWeights_isSNCDivisor_biholomorphism
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSNCDivisor n ((pulledWeights Φ F).map Prod.fst) := by
  rw [pulledWeights_carriers]
  exact (isSNCDivisor_map_preimage_iff Φ).mpr hF

private theorem pullback_vanishing_biholomorphism
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (C : Set A) (hC : IsClosedSubmanifold n C) :
    GermIdeal.pullback (m := n) Φ (vanishingIdeal (n := n) C) = vanishingIdeal (n := n) (Φ ⁻¹' C) := by
  have hc := (isClosedSubmanifold_preimage_iff Φ).mpr hC
  have he := pullback_vanishingIdeal_preimage Φ.contMDiff Φ.symm.contMDiff
    Φ.apply_symm_apply Φ.symm_apply_apply (g := id) contMDiff_id C
  rw [Function.comp_id,BlowupControlledTransform.pullback_id
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hc)] at he
  exact he.symm

private theorem pullback_product_biholomorphism_of_present
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    {E : List (Set A)} (hE : IsSNCDivisor n E) (F : List (Set A × ℕ))
    (hF : ∀ p ∈ F, p.1 ∈ E) :
    GermIdeal.pullback (m := n) Φ (componentPowerProduct (n := n) F) =
      componentPowerProduct (n := n) (pulledWeights Φ F) := by
  induction F with
  | nil => exact HironakaSmoothSubmersionCoefficientIdeals.pullback_unitIdeal
  | cons p F ih =>
    have htail : ∀ q ∈ F, q.1 ∈ E := fun q hq => hF q (List.mem_cons_of_mem p hq)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hF p (by simp))
    have hc : IsClosedSubmanifold n p.1 := hi ▸ (snc_member_codimOne_geometry hE i).1
    have hcoh := VanishingIdealCoherent.isCoherent_vanishingIdeal hc
    have htc : (componentPowerProduct (n := n) F).IsCoherent :=
      (isWellFormed_monomialMarkedIdeal hE F htail).isCoherent
    change GermIdeal.pullback (m := n) Φ ((idealPow (vanishingIdeal (n := n) p.1) p.2).mul
      (componentPowerProduct (n := n) F)) =
      (idealPow (vanishingIdeal (n := n) (Φ ⁻¹' p.1)) p.2).mul
        (componentPowerProduct (n := n) (pulledWeights Φ F))
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul Φ.contMDiff
      (GermIdealPullbackCalculus.isCoherent_idealPow hcoh p.2) htc,
      HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow Φ.contMDiff hcoh,
      pullback_vanishing_biholomorphism Φ p.1 hc,ih htail]

/-- True biholomorphic geometry internally identifies the COMPLETE original indexed marked product. -/
theorem markedPullback_indexed_biholomorphism
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal.pullback Φ (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) =
      monomialMarkedIdeal (n := n) ((pulledWeights Φ F).map Prod.fst) (pulledWeights Φ F) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ (pulledWeights_carriers Φ F).symm
    (pullback_product_biholomorphism_of_present Φ hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)) rfl

/-- The independently defined old-key selector is actually invariant under every genuine biholomorphism. -/
theorem selectedIndex_biholomorphism
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) :
    selectedIndex n (pulledWeights Φ F) = (selectedIndex n F).map (pulledIndex Φ F) := by
  classical
  cases hs : selectedIndex n F with
  | none =>
    have he := (selectedIndex_eq_none_iff F).mp hs
    apply (selectedIndex_eq_none_iff (pulledWeights Φ F)).mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have := (activeIndices_pulled_iff Φ Φ.toEquiv.surjective F ((pulledIndex Φ F).symm i)).mp hi
    rw [he] at this
    exact Finset.notMem_empty _ this
  | some j =>
    rw [Option.map_some]
    obtain ⟨hj,hm,_⟩ := selectedIndex_some_spec F hs
    apply selectedIndex_eq_some_of_maximum
    · exact (activeIndices_pulled_iff Φ Φ.toEquiv.surjective F j).mpr hj
    · intro i hi
      let k := (pulledIndex Φ F).symm i
      have hk := (activeIndices_pulled_iff Φ Φ.toEquiv.surjective F k).mp hi
      have hh := hm k hk
      have hiEq : pulledIndex Φ F k = i := (pulledIndex Φ F).apply_symm_apply i
      rw [← hiEq,singletonKey_pulled,singletonKey_pulled]
      exact hh

/-- Only genuine primitive Cartier blowup choices are supplied; every maximum and successor is internally generated. -/
structure CartierBlowupChoices (n : ℕ) where
  choose : (A : CMfd.{u} n) → (F : List (Set A × ℕ)) → IsSNCDivisor n (F.map Prod.fst) →
    (j : Fin F.length) → Σ D : CMfd.{u} n, {π : D → A // IsBlowupAlong n (F.get j).1 π}

/-- Original SNC internally supplies a genuine default primitive choice family. -/
def identityCartierChoices : CartierBlowupChoices.{u} n where
  choose A F hF j := ⟨A,id,isBlowupAlong_id_indexed_member F hF j⟩

/-- A real chosen blowup of an original actual SNC member internally has its UNIQUE actual global inverse. -/
theorem exists_unique_Cartier_biholomorphism (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) {π : B → A}
    (hπ : IsBlowupAlong n (F.get j).1 π) :
    ∃! χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A, (χ : B → A) = π := by
  obtain ⟨χ,hχ,hu⟩ := exists_unique_lift (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞)
    hπ (isBlowupAlong_id_indexed_member F hF j) (by rfl)
  refine ⟨χ,funext hχ,?_⟩
  intro χ' hχ'
  apply hu
  intro z
  exact congrFun hχ' z

/-- The actual comparison is chosen only from its true universal-property primitive producer. -/
def CartierBiholomorphism (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (j : Fin F.length) {π : B → A} (hπ : IsBlowupAlong n (F.get j).1 π) :
    B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A :=
  Classical.choose (exists_unique_Cartier_biholomorphism F hF j hπ)

/-- Its entire actual projection, rather than only a support or point correspondence, equals the genuine blowup map. -/
theorem CartierBiholomorphism_coe (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (j : Fin F.length) {π : B → A} (hπ : IsBlowupAlong n (F.get j).1 π) :
    (CartierBiholomorphism F hF j hπ : B → A) = π :=
  (Classical.choose_spec (exists_unique_Cartier_biholomorphism F hF j hπ)).1

/-- The REAL entire controlled successor of every positive actually chosen Cartier step is internally produced. -/
theorem chosen_Cartier_controlled_dictionary (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : 0 < (F.get j).2)
    {π : B → A} (hπ : IsBlowupAlong n (F.get j).1 π) :
    (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 π =
      monomialMarkedIdeal (n := n)
        ((pulledWeights (CartierBiholomorphism F hF j hπ) (dividedWeights F j)).map Prod.fst)
        (pulledWeights (CartierBiholomorphism F hF j hπ) (dividedWeights F j)) := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hi := isBlowupAlong_id_indexed_member F hF j
  have ha := isAdmissibleCentre_indexed_positive F hF j hj
  have hc := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw ha hi).isCoherent
  have he := BlowupBiholomorphismLift.geoTransform_comp_diffeo
    (CartierBiholomorphism F hF j hπ) _ hw.isCoherent (F.get j).1
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hi.1) contMDiff_id hc
  have hmap : (id : A → A) ∘ (CartierBiholomorphism F hF j hπ) = π := by
    simpa only [Function.id_comp] using CartierBiholomorphism_coe F hF j hπ
  rw [hmap,geoTransform_indexed_positive F hF j hj,
    markedPullback_indexed_biholomorphism _ _ (dividedWeights_isSNCDivisor F hF j hj)] at he
  exact he

/-- Complete actual terminal geometry and literal state produced by the real bounded procedure. -/
structure ChosenOutput (A : CMfd.{u} n) where
  D : CMfd.{u} n
  T : BlowupTower A D
  back : D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A
  proj_eq : (back : D → A) = T.proj
  weights : List (Set D × ℕ)
  snc : IsSNCDivisor n (weights.map Prod.fst)
  indices : List ℕ

private def prependCartier (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (j : Fin F.length) {π : B → A} (hπ : IsBlowupAlong n (F.get j).1 π) (o : ChosenOutput B) : ChosenOutput A where
  D := o.D
  T := (BlowupTower.step BlowupTower.refl (F.get j).1 π hπ).append o.T
  back := o.back.trans (CartierBiholomorphism F hF j hπ)
  proj_eq := by
    rw [Diffeomorph.coe_trans,BlowupTower.proj_append,← o.proj_eq,CartierBiholomorphism_coe]
    rfl
  weights := o.weights
  snc := o.snc
  indices := j.val :: o.indices

open Classical in
/-- The chosen real bounded procedure recursively constructs every actual manifold, blowup, whole state and inverse projection. -/
def chosenProcedure (β : CartierBlowupChoices.{u} n) : (q : ℕ) → (A : CMfd.{u} n) →
    (F : List (Set A × ℕ)) → IsSNCDivisor n (F.map Prod.fst) → ChosenOutput A
  | 0,A,F,hF => ⟨A,.refl,Diffeomorph.refl _ A ∞,rfl,F,hF,[]⟩
  | q+1,A,F,hF =>
    match hs : selectedIndex n F with
    | none => ⟨A,.refl,Diffeomorph.refl _ A ∞,rfl,F,hF,[]⟩
    | some j =>
      let hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      let c := β.choose A F hF j
      let χ := CartierBiholomorphism F hF j c.2.property
      let G := pulledWeights χ (dividedWeights F j)
      let hG := pulledWeights_isSNCDivisor_biholomorphism χ _ (dividedWeights_isSNCDivisor F hF j hj)
      prependCartier F hF j c.2.property (chosenProcedure β q c.1 G hG)

private theorem chosenProcedure_succ_none (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (hs : selectedIndex n F = none) :
    chosenProcedure β (q+1) A F hF = ⟨A,.refl,Diffeomorph.refl _ A ∞,rfl,F,hF,[]⟩ := by
  conv_lhs => unfold chosenProcedure
  split
  · rfl
  · rename_i j hj
    have he := hs.symm.trans hj
    contradiction

open Classical in
private theorem chosenProcedure_succ_some (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length)
    (hs : selectedIndex n F = some j) :
    chosenProcedure β (q+1) A F hF =
      let hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      let c := β.choose A F hF j
      let χ := CartierBiholomorphism F hF j c.2.property
      let G := pulledWeights χ (dividedWeights F j)
      let hG := pulledWeights_isSNCDivisor_biholomorphism χ _ (dividedWeights_isSNCDivisor F hF j hj)
      prependCartier F hF j c.2.property (chosenProcedure β q c.1 G hG) := by
  conv_lhs => unfold chosenProcedure
  split
  · rename_i he
    have h := he.symm.trans hs
    contradiction
  · rename_i k hk
    have heq : k = j := Option.some.inj (hk.symm.trans hs)
    subst k
    rfl

private theorem chosenProcedure_congr_state (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F G : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (hG : IsSNCDivisor n (G.map Prod.fst)) (he : F = G) :
    chosenProcedure β q A F hF = chosenProcedure β q A G hG := by
  subst G
  rfl

/-- Actual literal state pullback through real composed biholomorphisms. -/
theorem pulledWeights_trans {C : CMfd.{u} n}
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (χ : C ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B)
    (F : List (Set A × ℕ)) :
    pulledWeights (χ.trans Φ) F = pulledWeights χ (pulledWeights Φ F) := by
  rw [Diffeomorph.coe_trans,pulledWeights_comp]

/-- The actual independently selected successor and whole stage map align with the original reference input. -/
theorem pulled_divided_biholomorphism {C : CMfd.{u} n}
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (χ : C ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B)
    (F : List (Set A × ℕ)) (j : Fin F.length) :
    pulledWeights (χ.trans Φ) (dividedWeights F j) =
      pulledWeights χ (dividedWeights (pulledWeights Φ F) (pulledIndex Φ F j)) := by
  rw [pulledWeights_trans,pulledWeights_dividedWeights]

/-- A real bounded chosen run has an internally produced ACTUAL tower isomorphism to the independent identity run. -/
theorem chosenProcedure_reference (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsTowerIso Φ (chosenProcedure β q B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).T
      (procedureTower q F hF)
      ((chosenProcedure β q B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).back.trans Φ) := by
  classical
  induction q generalizing A B with
  | zero => exact IsTowerIso.refl
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none =>
      have hp : selectedIndex n (pulledWeights Φ F) = none := by
        rw [selectedIndex_biholomorphism,hs]; rfl
      rw [chosenProcedure_succ_none β q _ _ hp,procedureTower_eq_refl_of_none _ F hF hs]
      exact IsTowerIso.refl
    | some j =>
      have hp : selectedIndex n (pulledWeights Φ F) = some (pulledIndex Φ F j) := by
        rw [selectedIndex_biholomorphism,hs]; rfl
      rw [chosenProcedure_succ_some β q _ _ _ hp,procedureTower_succ_some q F hF j hs]
      dsimp only
      let hP := pulledWeights_isSNCDivisor_biholomorphism Φ F hF
      let jP := pulledIndex Φ F j
      let c := β.choose B (pulledWeights Φ F) hP jP
      let χ := CartierBiholomorphism (pulledWeights Φ F) hP jP c.2.property
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hD := dividedWeights_isSNCDivisor F hF j hj
      have hrec := ih (χ.trans Φ) (dividedWeights F j) hD
      have hjP := ((Finset.mem_filter.mp (selectedIndex_some_spec (pulledWeights Φ F) hp).1).2).1
      have hG := pulledWeights_isSNCDivisor_biholomorphism χ _
        (dividedWeights_isSNCDivisor (pulledWeights Φ F) hP jP hjP)
      have hOut := chosenProcedure_congr_state β q _ _
        (pulledWeights_isSNCDivisor_biholomorphism (χ.trans Φ) _ hD) hG
        (pulled_divided_biholomorphism Φ χ F j)
      rw [hOut] at hrec
      have hfirst : IsTowerIso Φ
          (BlowupTower.step BlowupTower.refl ((pulledWeights Φ F).get jP).1 c.2.val c.2.property)
          (BlowupTower.step BlowupTower.refl (F.get j).1 id (isBlowupAlong_id_indexed_member F hF j))
          (χ.trans Φ) := by
        apply IsTowerIso.step IsTowerIso.refl
        · intro z
          change Φ (χ z) = Φ (c.2.val z)
          rw [show (χ : c.1 → B) = c.2.val from CartierBiholomorphism_coe _ _ _ _]
        · rw [pulledWeights_get]
      have hc := hfirst.append hrec
      exact hc

/-- The real procedure on its own original state has its actual total projection as the reference tower isomorphism. -/
theorem chosenProcedure_self_reference (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) (chosenProcedure β q A F hF).T
      (procedureTower q F hF) (chosenProcedure β q A F hF).back := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞
  have he := chosenProcedure_reference β q Φ F hF
  have hweights : pulledWeights Φ F = F := pulledWeights_id F
  have hO := chosenProcedure_congr_state β q _ _
    (pulledWeights_isSNCDivisor_biholomorphism Φ F hF) hF hweights
  rw [hO] at he
  exact he

private theorem pullback_refl_marked (M : MarkedIdeal n A) (hI : M.ideal.IsCoherent) :
    MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) M = M := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change M.E.map (id ⁻¹' ·) = M.E
    simp only [preimage_id_eq,List.map_id]
  · exact BlowupControlledTransform.pullback_id hI
  · rfl

private theorem actual_gamma_towerIso {A' D' D : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (M : MarkedIdeal n A) (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hi : IsTowerIso Φ T' T χ) (ht : IsGeoTestTower M T) (p : D') :
    MonomialStepAlong.towerInvAlong (MarkedIdeal.pullback Φ M) T' p =
      MonomialStepAlong.towerInvAlong M T (χ p) := by
  have hc := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T ht).2
  unfold MonomialStepAlong.towerInvAlong
  rw [hi.geoTransformAlong_eq Φ hN hI ht]
  exact MonomialInvariantFunctorialAlong.gammaAlong_pullback_diffeomorph χ _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg) p _

private theorem actual_canonical_towerIso {A' D' D : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (M : MarkedIdeal n A) (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hi : IsTowerIso Φ T' T χ) (ht : IsGeoTestTower M T)
    (hcan : ResolutionDriver.IsCanonicalSegment M
      (fun {V} R => MonomialStepAlong.towerInvAlong M (Y := V) R) T) :
    ResolutionDriver.IsCanonicalSegment (MarkedIdeal.pullback Φ M)
      (fun {V} R => MonomialStepAlong.towerInvAlong (MarkedIdeal.pullback Φ M) (Y := V) R) T' := by
  revert ht hcan
  induction hi with
  | refl => exact fun _ _ => trivial
  | @step D' D Z' Z T' T χ hi C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro ht hcan
    obtain ⟨hcan0,hne,he⟩ := hcan
    refine ⟨ih ht.1 hcan0,?_,?_⟩
    · obtain ⟨p,hp⟩ := hne
      refine ⟨χ.symm p,?_⟩
      rw [← hC]
      change χ (χ.symm p) ∈ C
      rwa [χ.apply_symm_apply]
    · have hmax : ResolutionDriver.maxLocus
          (MonomialStepAlong.towerInvAlong (MarkedIdeal.pullback Φ M) T')
          (geoTransformAlong (MarkedIdeal.pullback Φ M) T').cosupp =
          χ ⁻¹' ResolutionDriver.maxLocus (MonomialStepAlong.towerInvAlong M T)
            (geoTransformAlong M T).cosupp := by
        rw [hi.cosupp_geoTransformAlong Φ hN hI ht.1]
        exact ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.toEquiv.surjective
          (fun p _ => actual_gamma_towerIso Φ M hN hI hi ht.1 p)
      rw [hmax,← he,hC]

/-- Every real chosen bounded procedure is a genuine marked test tower, internally supplied from original SNC. -/
theorem chosenProcedure_isGeoTestTower (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoTestTower (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β q A F hF).T := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := ((chosenProcedure_self_reference β q F hF).isGeoTestTower_iff
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) hw.isClosedSubmanifold_N hw.isCoherent).mpr
      (procedureTower_isGeoTestTower q F hF)
  rwa [pullback_refl_marked _ hw.isCoherent] at he

/-- The old-gamma canonical segment of the independently chosen real tower is internally proved, never assumed. -/
theorem chosenProcedure_isCanonicalSegment (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ResolutionDriver.IsCanonicalSegment (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (fun {V} R => MonomialStepAlong.towerInvAlong
        (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (Y := V) R) (chosenProcedure β q A F hF).T := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := actual_canonical_towerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞)
    _ hw.isClosedSubmanifold_N hw.isCoherent (chosenProcedure_self_reference β q F hF)
    (procedureTower_isGeoTestTower q F hF) (procedureTower_isCanonicalSegment q F hF)
  rwa [pullback_refl_marked _ hw.isCoherent] at he

/-- True chosen bounded lengths equal those of the independent actual reference procedure. -/
theorem chosenProcedure_length_eq (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β q A F hF).T.length = (procedureTower q F hF).length :=
  (chosenProcedure_self_reference β q F hF).length_eq

/-- Actual full coefficient sum internally bounds every genuine chosen bounded procedure. -/
theorem chosenProcedure_length_le_sum (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β q A F hF).T.length ≤ coefficientSum F := by
  rw [chosenProcedure_length_eq]
  exact procedureTower_length_le_sum q F hF

/-- OWN original coefficient sum supplies the whole true chosen unit endpoint without any termination certificate. -/
theorem chosenProcedure_ideal_eq_unit (β : CartierBlowupChoices.{u} n)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β (coefficientSum F) A F hF).T).ideal =
        unitIdeal n (chosenProcedure β (coefficientSum F) A F hF).D := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := (chosenProcedure_self_reference β (coefficientSum F) F hF).geoTransformAlong_eq
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) hw.isClosedSubmanifold_N hw.isCoherent
    (procedureTower_isGeoTestTower _ F hF)
  rw [pullback_refl_marked _ hw.isCoherent] at he
  have hi := congrArg (fun M => M.ideal) he
  change _ = GermIdeal.pullback (m := n) _ _ at hi
  rw [procedureTower_ideal_eq_unit,HironakaSmoothSubmersionCoefficientIdeals.pullback_unitIdeal] at hi
  exact hi

/-- SAME actual original full product is genuinely resolved by the independently chosen internally finite tower. -/
theorem chosenProcedure_isGeoResolution (β : CartierBlowupChoices.{u} n)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoResolution (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β (coefficientSum F) A F hF).T := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := ((chosenProcedure_self_reference β (coefficientSum F) F hF).isGeoResolution_iff
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) hw.isClosedSubmanifold_N hw.isCoherent).mpr
      (procedureTower_isGeoResolution F hF)
  rwa [pullback_refl_marked _ hw.isCoherent] at he

/-- Every literal chosen-tower prefix internally retains the complete actual invariant domain. -/
theorem chosenProcedure_prefix_domain (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    ResolutionInvariantSpec.IsInvDomain n (geoTransformAlong
      (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j)) :=
  InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (isInvDomain_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)) _
    (((BlowupTowerSplit.isGeoTestTower_iff_head_tail
      (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β q A F hF).T j).mp
      (chosenProcedure_isGeoTestTower β q F hF)).1)

/-- Every real literal chosen prefix retains the ENTIRE true SNC boundary history. -/
theorem chosenProcedure_prefix_snc (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    IsSNCDivisor n (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j)).E :=
  (chosenProcedure_prefix_domain β q F hF j).isWellFormed.isSNCDivisor

/-- Actual recorded whole terminal weights and all selected natural labels agree with the true independent reference run. -/
theorem chosenProcedure_record_dictionary (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β q B (pulledWeights Φ F) (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).weights =
      pulledWeights ((chosenProcedure β q B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).back.trans Φ) (terminalState n q F) ∧
    (chosenProcedure β q B (pulledWeights Φ F)
      (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).indices = indexTrace n q F := by
  classical
  induction q generalizing A B with
  | zero => exact ⟨rfl,rfl⟩
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none =>
      have hp : selectedIndex n (pulledWeights Φ F) = none := by
        rw [selectedIndex_biholomorphism,hs]; rfl
      rw [chosenProcedure_succ_none β q _ _ hp,terminalState_succ_none q F hs]
      simp only [indexTrace,hs]
      exact ⟨rfl,trivial⟩
    | some j =>
      have hp : selectedIndex n (pulledWeights Φ F) = some (pulledIndex Φ F j) := by
        rw [selectedIndex_biholomorphism,hs]; rfl
      rw [chosenProcedure_succ_some β q _ _ _ hp,terminalState_succ_some q F j hs]
      let hP := pulledWeights_isSNCDivisor_biholomorphism Φ F hF
      let jP := pulledIndex Φ F j
      let c := β.choose B (pulledWeights Φ F) hP jP
      let χ := CartierBiholomorphism (pulledWeights Φ F) hP jP c.2.property
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hD := dividedWeights_isSNCDivisor F hF j hj
      have hrec := ih (χ.trans Φ) (dividedWeights F j) hD
      have hjP := ((Finset.mem_filter.mp (selectedIndex_some_spec (pulledWeights Φ F) hp).1).2).1
      have hG := pulledWeights_isSNCDivisor_biholomorphism χ _
        (dividedWeights_isSNCDivisor (pulledWeights Φ F) hP jP hjP)
      have hOut := chosenProcedure_congr_state β q _ _
        (pulledWeights_isSNCDivisor_biholomorphism (χ.trans Φ) _ hD) hG
        (pulled_divided_biholomorphism Φ χ F j)
      rw [hOut] at hrec
      refine ⟨hrec.1,?_⟩
      change j.val :: _ = indexTrace n (q+1) F
      rw [indexTrace,hs,hrec.2]

/-- Own actual recorded whole state is the COMPLETE genuine controlled terminal marked datum. -/
theorem chosenProcedure_marked_dictionary (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β q A F hF).T =
      monomialMarkedIdeal (n := n) ((chosenProcedure β q A F hF).weights.map Prod.fst)
        (chosenProcedure β q A F hF).weights := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := (chosenProcedure_self_reference β q F hF).geoTransformAlong_eq
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) hw.isClosedSubmanifold_N hw.isCoherent
    (procedureTower_isGeoTestTower q F hF)
  rw [pullback_refl_marked _ hw.isCoherent,procedureTower_marked_dictionary,
    markedPullback_indexed_biholomorphism _ _ (terminalState_isSNCDivisor q F hF)] at he
  have hr := chosenProcedure_record_dictionary β q (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) F hF
  have hOut := chosenProcedure_congr_state β q _ _
    (pulledWeights_isSNCDivisor_biholomorphism (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) F hF)
    hF (pulledWeights_id F)
  rw [hOut] at hr
  have hrW : (chosenProcedure β q A F hF).weights =
      pulledWeights (chosenProcedure β q A F hF).back (terminalState n q F) := hr.1
  rw [← hrW] at he
  exact he

/-- Actual two-choice stage comparisons are constructed from the two real independent reference comparisons. -/
theorem chosenProcedures_comparison (β' β : CartierBlowupChoices.{u} n) (q : ℕ)
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsTowerIso Φ (chosenProcedure β' q B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).T
      (chosenProcedure β q A F hF).T
      (((chosenProcedure β' q B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).back.trans Φ).trans
        (chosenProcedure β q A F hF).back.symm) :=
  (chosenProcedure_reference β' q Φ F hF).trans (chosenProcedure_self_reference β q F hF).symm

/-- Primitive original geometry internally gives a UNIQUE actual whole tower comparison for two independent choices. -/
theorem exists_unique_chosenProcedures_comparison (β' β : CartierBlowupChoices.{u} n) (q : ℕ)
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃! χ : (chosenProcedure β' q B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).D
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (chosenProcedure β q A F hF).D,
      IsTowerIso Φ (chosenProcedure β' q B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).T (chosenProcedure β q A F hF).T χ := by
  refine ⟨_,chosenProcedures_comparison β' β q Φ F hF,?_⟩
  intro χ hχ
  apply Diffeomorph.ext
  intro z
  apply (chosenProcedure β q A F hF).back.injective
  change (chosenProcedure β q A F hF).back (χ z) =
    (chosenProcedure β q A F hF).back ((((chosenProcedure β' q B (pulledWeights Φ F)
      (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).back.trans Φ).trans
      (chosenProcedure β q A F hF).back.symm) z)
  rw [(chosenProcedure β q A F hF).proj_eq,← hχ.proj_comm z,
    ← (chosenProcedures_comparison β' β q Φ F hF).proj_comm z]

/-- Actual canonical comparison of two genuine independently generated runs on the same original input. -/
def choiceComparison (β' β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' q A F hF).D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (chosenProcedure β q A F hF).D :=
  (chosenProcedure β' q A F hF).back.trans (chosenProcedure β q A F hF).back.symm

/-- The actual comparison is a genuine tower isomorphism, not a supplied comparison certificate. -/
theorem choiceComparison_isTowerIso (β' β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞)
      (chosenProcedure β' q A F hF).T (chosenProcedure β q A F hF).T (choiceComparison β' β q F hF) :=
  (chosenProcedure_self_reference β' q F hF).trans (chosenProcedure_self_reference β q F hF).symm

/-- Real unique comparison transports the ENTIRE actual controlled marked record of the original input. -/
theorem choiceComparison_marked_dictionary (β' β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β' q A F hF).T =
      MarkedIdeal.pullback (choiceComparison β' β q F hF)
        (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β q A F hF).T) := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := (choiceComparison_isTowerIso β' β q F hF).geoTransformAlong_eq
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) hw.isClosedSubmanifold_N hw.isCoherent
    (chosenProcedure_isGeoTestTower β q F hF)
  rwa [pullback_refl_marked _ hw.isCoherent] at he

/-- Exact actual identity of the internally generated real comparison. -/
theorem choiceComparison_identity (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    choiceComparison β β q F hF = Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (chosenProcedure β q A F hF).D ∞ := by
  apply Diffeomorph.ext
  intro z
  simp only [choiceComparison,Diffeomorph.coe_trans,Function.comp_apply,Diffeomorph.symm_apply_apply]
  rfl

/-- Exact actual inverse of the true independent-procedure comparison. -/
theorem choiceComparison_inverse (β' β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (choiceComparison β' β q F hF).symm = choiceComparison β β' q F hF := by
  apply Diffeomorph.ext
  intro z
  rfl

/-- Actual three-choice comparison cocycle follows from the REAL generated projection inverses. -/
theorem choiceComparison_cocycle (β'' β' β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (choiceComparison β'' β' q F hF).trans (choiceComparison β' β q F hF) =
      choiceComparison β'' β q F hF := by
  apply Diffeomorph.ext
  intro z
  simp only [choiceComparison,Diffeomorph.coe_trans,Function.comp_apply,Diffeomorph.apply_symm_apply]

/-- Every independent genuine chosen index word is EXACTLY the original actual old-colex reference word. -/
theorem chosenProcedure_indices_dictionary (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β q A F hF).indices = indexTrace n q F := by
  have hr := chosenProcedure_record_dictionary β q (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) F hF
  have hOut := chosenProcedure_congr_state β q _ _
    (pulledWeights_isSNCDivisor_biholomorphism (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) F hF)
    hF (pulledWeights_id F)
  rw [hOut] at hr
  exact hr.2

/-- Both OWN internally computed fuels give the UNIQUE actual comparison of their completed independently chosen procedures. -/
theorem exists_unique_completed_choice_comparison (β' β : CartierBlowupChoices.{u} n)
    (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃! χ : (chosenProcedure β' (coefficientSum (pulledWeights Φ F)) B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).D
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (chosenProcedure β (coefficientSum F) A F hF).D,
      IsTowerIso Φ (chosenProcedure β' (coefficientSum (pulledWeights Φ F)) B (pulledWeights Φ F)
        (pulledWeights_isSNCDivisor_biholomorphism Φ F hF)).T
        (chosenProcedure β (coefficientSum F) A F hF).T χ := by
  rw [coefficientSum_pulled]
  exact exists_unique_chosenProcedures_comparison β' β _ Φ F hF

/-- Actual recorded coefficients account for EVERY genuine performed step, including complete literal inactive histories. -/
theorem chosenProcedure_coefficient_accounting (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    coefficientSum (chosenProcedure β q A F hF).weights + (chosenProcedure β q A F hF).T.length =
      coefficientSum F := by
  classical
  induction q generalizing A with
  | zero => exact Nat.add_zero _
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none =>
      rw [chosenProcedure_succ_none β q F hF hs]
      exact Nat.add_zero _
    | some j =>
      rw [chosenProcedure_succ_some β q F hF j hs]
      let c := β.choose A F hF j
      let χ := CartierBiholomorphism F hF j c.2.property
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hD := dividedWeights_isSNCDivisor F hF j hj
      have hG := pulledWeights_isSNCDivisor_biholomorphism χ _ hD
      have hrec := ih (pulledWeights χ (dividedWeights F j)) hG
      rw [coefficientSum_pulled] at hrec
      have hd := dividedWeights_sum_add_one F j hj
      change coefficientSum (chosenProcedure β q c.1 (pulledWeights χ (dividedWeights F j)) hG).weights +
        ((BlowupTower.step BlowupTower.refl (F.get j).1 c.2.val c.2.property).append
          (chosenProcedure β q c.1 (pulledWeights χ (dividedWeights F j)) hG).T).length = coefficientSum F
      rw [BlowupTower.length_append]
      change coefficientSum (chosenProcedure β q c.1 (pulledWeights χ (dividedWeights F j)) hG).weights +
        (1+(chosenProcedure β q c.1 (pulledWeights χ (dividedWeights F j)) hG).T.length) = coefficientSum F
      change coefficientSum (dividedWeights F j)+1=coefficientSum F at hd
      omega

end
end Hironaka.HironakaNormalCrossingsOrderedChoiceComparison

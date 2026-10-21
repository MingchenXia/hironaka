/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaComponentwiseCanonicalHistory
import Hironaka.Invariant.StepOneTangentChange

/-!
# Genuine prefix isomorphisms of internally chosen parallel histories

Whole parallel centres transport under actual prefix isomorphisms.
Induction and the blowup universal property then construct genuine
isomorphisms of every absolute recorded prefix, retaining empty stages.
An original-only endpoint constructs both histories before their comparison.
Only ambient biholomorphisms, not arbitrary smooth submersions, are asserted.
Blueprint: `hironaka-componentwise-history-naturality-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaComponentwiseHistoryNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantDriver CanonicalCentres
  HironakaComponentwiseCanonicalCentre HironakaComponentwiseCanonicalHistory
  HironakaLocallyFiniteResolutionSequence BlowupTowerIsomorphism StepOneTangentChange
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n k : ℕ} {X X' : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- The literal preimage open under the supplied actual ambient biholomorphism. -/
def pullbackOpen
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (U : Opens X) : Opens X' :=
  ⟨Φ ⁻¹' (U : Set X),U.isOpen.preimage Φ.continuous⟩

/-- The whole local maximum transports under an actual restricted prefix isomorphism. -/
theorem localMaximum_transport
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {Y Y' : CMfd.{u} n} (T : BlowupTower X Y) (T' : BlowupTower X' Y')
    (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (hiso : IsTowerIso Φ T' T χ) (U : Opens X) (U' : Opens X')
    (hU : ∀ x, x ∈ U' ↔ Φ x ∈ U)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U → X) M)) (restrict U T)) :
    localMaximum R (MarkedIdeal.pullback Φ M) T' U'=
      (diffeoOpens χ (openPreimage T' U') (openPreimage T U)
        (isTowerIso_mem_openPreimage_iff hiso hU)) ⁻¹' localMaximum R M T U := by
  let φ := diffeoOpens Φ U' U hU
  let ξ := diffeoOpens χ (openPreimage T' U') (openPreimage T U)
    (isTowerIso_mem_openPreimage_iff hiso hU)
  let Mi := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hd : IsInvDomain k Mi := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hMi : MarkedIdeal.pullback (Subtype.val : U' → X') (MarkedIdeal.pullback Φ M)=
      MarkedIdeal.pullback φ Mi :=
    ContactMarkedCanonical.pullback_pullback_of_comp_eq hM.isWellFormed.isCoherent
      Φ.contMDiff contMDiff_subtype_val φ.contMDiff contMDiff_subtype_val (fun _ => rfl)
  have hξ : IsTowerIso φ (restrict U' T') (restrict U T) ξ :=
    isTowerIso_restrictOpens hU hiso (isTowerIso_mem_openPreimage_iff hiso hU)
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hd (restrict U T) hcan
  change maxLocus
    (R.inv (MarkedIdeal.pullback (Subtype.val : U' → X') (MarkedIdeal.pullback Φ M)) (restrict U' T'))
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U' → X') (MarkedIdeal.pullback Φ M))
      (restrict U' T')).cosupp=ξ ⁻¹'
    maxLocus (R.inv Mi (restrict U T)) (geoTransformAlong Mi (restrict U T)).cosupp
  rw [hMi,IsTowerIso.cosupp_geoTransformAlong φ hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isCoherent hξ ht]
  exact ResolutionInvariantSegments.maxLocus_preimage_of_surjective ξ.toEquiv.surjective
    (fun p hp => R.isInvValue.towerIso φ Mi hd (restrict U' T') (restrict U T) ξ hξ hcan p hp)

/-- Whole parallel centres correspond; no centre correspondence is a premise. -/
theorem parallelCentre_transport
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {Y Y' : CMfd.{u} n} (T : BlowupTower X Y) (T' : BlowupTower X' Y')
    (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (hiso : IsTowerIso Φ T' T χ)
    {J : Type w} (U : J → Opens X) (U' : J → Opens X')
    (hU : ∀ i x, x ∈ U' i ↔ Φ x ∈ U i)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (hcan : ∀ i, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) T)) :
    χ ⁻¹' parallelCentre R M T U=parallelCentre R (MarkedIdeal.pullback Φ M) T' U' := by
  have hdisj' : Pairwise (fun i j => Disjoint (U' i : Set X') (U' j : Set X')) := by
    intro i j hij
    exact disjoint_left.mpr (fun x hxi hxj =>
      disjoint_left.mp (hdisj hij) ((hU i x).mp hxi) ((hU j x).mp hxj))
  ext y'
  obtain ⟨i,hi⟩ := hcover (T.proj (χ y'))
  have hi' : T'.proj y' ∈ U' i := (hU i _).mpr (hiso.proj_comm y' ▸ hi)
  let p : openPreimage T' (U' i) := ⟨y',hi'⟩
  let q : openPreimage T (U i) := ⟨χ y',hi⟩
  change q ∈ (Subtype.val : openPreimage T (U i) → Y) ⁻¹' parallelCentre R M T U ↔
    p ∈ (Subtype.val : openPreimage T' (U' i) → Y') ⁻¹'
      parallelCentre R (MarkedIdeal.pullback Φ M) T' U'
  rw [preimage_parallelCentre R M T U hdisj i,
    preimage_parallelCentre R (MarkedIdeal.pullback Φ M) T' U' hdisj' i,
    localMaximum_transport R M hM Φ T T' χ hiso (U i) (U' i) (hU i) (hcan i)]
  rfl

/-- Universal-property lifts compare every actual absolute prefix, independently of blowup choices. -/
theorem parallel_sequences_isTowerIso
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {J : Type w} (U : J → Opens X) (U' : J → Opens X')
    (hU : ∀ i x, x ∈ U' i ↔ Φ x ∈ U i)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (s : GrowingSeq X) (s' : GrowingSeq X')
    (hcan : ∀ i j, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) (s.stage j).2))
    (hsteps : ParallelSteps R M U s)
    (hsteps' : ParallelSteps R (MarkedIdeal.pullback Φ M) U' s') :
    ∀ j, ∃ χ : (s'.stage j).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (s.stage j).1,
      IsTowerIso Φ (s'.stage j).2 (s.stage j).2 χ := by
  intro j
  induction j with
  | zero => rw [s.zero,s'.zero]; exact ⟨Φ,IsTowerIso.refl⟩
  | succ j ih =>
    obtain ⟨χ,hiso⟩ := ih
    obtain ⟨C,π,hπ,he,hC⟩ := hsteps j
    obtain ⟨C',π',hπ',he',hC'⟩ := hsteps' j
    have hCC : χ ⁻¹' C=C' := by
      rw [hC,hC']
      exact parallelCentre_transport R M hM Φ (s.stage j).2 (s'.stage j).2 χ hiso U U'
        hU hcover hdisj (fun i => hcan i j)
    have hB := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
      χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply hπ
    rw [hCC] at hB
    obtain ⟨e,f,hehol,hfhol,hπe,_hπf,hfe,hef⟩ := BlowupUniqueness.exists_biholomorphism_over hπ' hB
    rw [he,he']
    refine ⟨⟨⟨e,f,congrFun hfe,congrFun hef⟩,hehol,hfhol⟩,
      IsTowerIso.step hiso hπ' hπ _ (fun p => ?_) hCC⟩
    have hh : χ.symm (π (e p))=π' p := congrFun hπe p
    show π (e p)=χ (π' p)
    rw [← hh,χ.apply_symm_apply]

section Original
variable {n : ℕ} {X X' : CMfd.{u} n}

/-- Both actual histories and all prefix comparisons are internally produced from ORIGINAL input. -/
theorem exists_original_componentwise_histories_biholomorphic
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hK : ∀ i : ConnectedComponents X,
      IsCompact ((Subtype.val : componentOpen i → X) ⁻¹' M.cosupp))
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    ∃ (s : GrowingSeq X) (s' : GrowingSeq X'),
      (∀ j, IsGeoTestTower M (s.stage j).2 ∧
        IsGeoTestTower (MarkedIdeal.pullback Φ M) (s'.stage j).2) ∧
      (∀ (i : ConnectedComponents X) j,
        IsCanonical (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M)
          ((canonicalInvariant n).inv (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M))
          (restrict (componentOpen i) (s.stage j).2) ∧
        IsCanonical (MarkedIdeal.pullback (Subtype.val : pullbackOpen Φ (componentOpen i) → X')
          (MarkedIdeal.pullback Φ M))
          ((canonicalInvariant n).inv (MarkedIdeal.pullback
            (Subtype.val : pullbackOpen Φ (componentOpen i) → X') (MarkedIdeal.pullback Φ M)))
          (restrict (pullbackOpen Φ (componentOpen i)) (s'.stage j).2)) ∧
      ParallelSteps (canonicalInvariant n) M componentOpen s ∧
      ParallelSteps (canonicalInvariant n) (MarkedIdeal.pullback Φ M)
        (fun i => pullbackOpen Φ (componentOpen i)) s' ∧
      (∀ i : ConnectedComponents X, ∃ N, ∀ j, N ≤ j →
        IsGeoResolution (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M)
          (restrict (componentOpen i) (s.stage j).2) ∧
        IsGeoResolution (MarkedIdeal.pullback (Subtype.val : pullbackOpen Φ (componentOpen i) → X')
          (MarkedIdeal.pullback Φ M))
          (restrict (pullbackOpen Φ (componentOpen i)) (s'.stage j).2)) ∧
      LocallyFinite (centreImage s) ∧ LocallyFinite (centreImage s') ∧
      ∀ j, ∃ χ : (s'.stage j).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (s.stage j).1,
        IsTowerIso Φ (s'.stage j).2 (s.stage j).2 χ := by
  let U : ConnectedComponents X → Opens X := componentOpen
  let U' : ConnectedComponents X → Opens X' := fun i => pullbackOpen Φ (U i)
  have hU : ∀ i x, x ∈ U' i ↔ Φ x ∈ U i := fun _ _ => Iff.rfl
  have hcover' : ∀ x : X', ∃ i, x ∈ U' i := by
    intro x
    obtain ⟨i,hi⟩ := componentOpen_cover (Φ x)
    exact ⟨i,hi⟩
  have hdisj' : Pairwise (fun i j => Disjoint (U' i : Set X') (U' j : Set X')) := by
    intro i j hij
    exact disjoint_left.mpr (fun x hxi hxj =>
      disjoint_left.mp (componentOpen_pairwise hij) hxi hxj)
  obtain ⟨s,hTest,hCan,hSteps,hTerminal,hLF,_hclosed,_htails⟩ :=
    exists_original_componentwise_locally_terminal_history M hM hK
  have hd' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  obtain ⟨s',hTest',hCan',hSteps'⟩ := exists_parallel_canonical_sequence
    (canonicalInvariant n) (MarkedIdeal.pullback Φ M) hd' U' hcover' hdisj'
  have hIso := parallel_sequences_isTowerIso (canonicalInvariant n) M hM Φ U U' hU
    componentOpen_cover componentOpen_pairwise s s' hCan hSteps hSteps'
  have hBoth : ∀ i, ∃ N, ∀ j, N ≤ j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (restrict (U i) (s.stage j).2) ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U' i → X') (MarkedIdeal.pullback Φ M))
        (restrict (U' i) (s'.stage j).2) := by
    intro i
    obtain ⟨N,hN⟩ := hTerminal i
    refine ⟨N,fun j hj => ⟨hN j hj,?_⟩⟩
    obtain ⟨χ,hχ⟩ := hIso j
    let φ := diffeoOpens Φ (U' i) (U i) (hU i)
    have hMi : MarkedIdeal.pullback (Subtype.val : U' i → X') (MarkedIdeal.pullback Φ M)=
        MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : U i → X) M) :=
      ContactMarkedCanonical.pullback_pullback_of_comp_eq hM.isWellFormed.isCoherent
        Φ.contMDiff contMDiff_subtype_val φ.contMDiff contMDiff_subtype_val (fun _ => rfl)
    have hξ := isTowerIso_restrictOpens (hU i) hχ (isTowerIso_mem_openPreimage_iff hχ (hU i))
    have hd := InvDomainTowerAlong.isInvDomain_pullback_val (U i) hM
    rw [hMi]
    exact (IsTowerIso.isGeoResolution_iff φ hd.isWellFormed.isClosedSubmanifold_N
      hd.isWellFormed.isCoherent hξ).mpr (hN j hj)
  have hTerminal' : ∀ i, ∃ N, ∀ j, N ≤ j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U' i → X') (MarkedIdeal.pullback Φ M))
        (restrict (U' i) (s'.stage j).2) := by
    intro i
    obtain ⟨N,hN⟩ := hBoth i
    exact ⟨N,fun j hj => (hN j hj).2⟩
  have hLF' := (locally_finite_empty_tails_of_component_terminal (canonicalInvariant n)
    (MarkedIdeal.pullback Φ M) U' hcover' hdisj' s' hSteps' hTerminal').1
  exact ⟨s,s',fun j => ⟨hTest j,hTest' j⟩,fun i j => ⟨hCan i j,hCan' i j⟩,
    hSteps,hSteps',hBoth,hLF,hLF',hIso⟩

end Original
end
end Hironaka.HironakaComponentwiseHistoryNaturality

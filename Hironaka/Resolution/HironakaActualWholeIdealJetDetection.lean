/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHolomorphicJetMonomialSpan
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual original ideal separation, before standard-basis reconstruction. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWholeIdealJetDetection
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
variable {n : ℕ}

/-- Module Krull intersection detects membership in the ENTIRE original ideal, including the unit ideal. -/
theorem mem_original_ideal_iff_all_maximal_thickenings
    (I : Ideal (HolGerm (ComplexModel n))) (g : HolGerm (ComplexModel n)) :
    g ∈ I ↔ ∀ q : ℕ, g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  constructor
  · intro hg q
    exact Ideal.mem_sup_left hg
  · intro hg
    let := isNoetherianRing_holGerm_euclidean n
    let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))
    let M := HolGerm (ComplexModel n) ⧸ I
    have hsep : (⨅ q : ℕ, m^q • (⊤ : Submodule (HolGerm (ComplexModel n)) M))=⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_isLocalRing m
        (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have hx : Ideal.Quotient.mk I g ∈
        (⨅ q : ℕ, m^q • (⊤ : Submodule (HolGerm (ComplexModel n)) M)) := by
      simp only [Submodule.mem_iInf]
      intro q
      obtain ⟨a,ha,z,hz,haz⟩ := Submodule.mem_sup.mp (hg q)
      have he : Ideal.Quotient.mk I g=Ideal.Quotient.mk I z := by
        apply Ideal.Quotient.eq.mpr
        have : g-z=a := by rw [← haz]; ring
        rwa [this]
      rw [he]
      have hm := Submodule.smul_mem_smul hz (show (1 : M) ∈ (⊤ : Submodule _ M) from trivial)
      change Ideal.Quotient.mk I (z*1) ∈ m^q • (⊤ : Submodule (HolGerm (ComplexModel n)) M) at hm
      simpa only [mul_one] using hm
    rw [hsep] at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Submodule.mem_bot] using hx

/-- No original whole ideal is lost by passing to ALL actual maximal thickenings. -/
theorem iInf_original_maximal_thickenings (I : Ideal (HolGerm (ComplexModel n))) :
    (⨅ q : ℕ, I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)=I := by
  ext g
  simp only [Ideal.mem_iInf]
  exact (show (∀ q : ℕ, g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) ↔ g ∈ I
    from (mem_original_ideal_iff_all_maximal_thickenings I g).symm)

/-- The order-zero tautology can be removed without losing any whole original numerator. -/
theorem mem_original_ideal_iff_all_positive_thickenings
    (I : Ideal (HolGerm (ComplexModel n))) (g : HolGerm (ComplexModel n)) :
    g ∈ I ↔ ∀ ℓ : ℕ, g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1) := by
  rw [mem_original_ideal_iff_all_maximal_thickenings]
  constructor
  · intro h ℓ
    exact h (ℓ+1)
  · intro h q
    cases q with
    | zero => simp
    | succ ℓ => exact h ℓ

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- BOTH actual whole finite-jet image directions precede the all-order reconstruction. -/
theorem finiteJet_mem_original_image_iff (I : Ideal (HolGerm (ComplexModel n)))
    (q : ℕ) (g : HolGerm (ComplexModel n)) :
    finiteJet q g ∈ (I.restrictScalars ℂ).map (finiteJet q) ↔
      g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  constructor
  · rintro ⟨a,ha,he⟩
    have hrem : g-a ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
      change g-a ∈ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q).restrictScalars ℂ
      rw [← ker_finiteJet]
      apply LinearMap.mem_ker.mpr
      rw [map_sub,he,sub_self]
    exact Submodule.mem_sup.mpr ⟨a,ha,g-a,hrem,by abel⟩
  · intro hg
    obtain ⟨a,ha,z,hz,haz⟩ := Submodule.mem_sup.mp hg
    have he : finiteJet q z=0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_finiteJet]
      exact hz
    apply Submodule.mem_map.mpr
    refine ⟨a,ha,?_⟩
    rw [← haz,map_add,he,add_zero]

/-- ALL true derivative jets detect membership in the ENTIRE original ideal. -/
theorem mem_original_ideal_iff_all_finiteJet_images
    (I : Ideal (HolGerm (ComplexModel n))) (g : HolGerm (ComplexModel n)) :
    g ∈ I ↔ ∀ q : ℕ, finiteJet q g ∈ (I.restrictScalars ℂ).map (finiteJet q) := by
  simp only [finiteJet_mem_original_image_iff]
  exact mem_original_ideal_iff_all_maximal_thickenings I g

/-- EVERY positive true jet is enough; no finite cut-off is presumed. -/
theorem mem_original_ideal_iff_all_positive_finiteJet_images
    (I : Ideal (HolGerm (ComplexModel n))) (g : HolGerm (ComplexModel n)) :
    g ∈ I ↔ ∀ ℓ : ℕ, finiteJet (ℓ+1) g ∈ (I.restrictScalars ℂ).map (finiteJet (ℓ+1)) := by
  simp only [finiteJet_mem_original_image_iff]
  exact mem_original_ideal_iff_all_positive_thickenings I g

/-- Actual inclusion of ALL original derivative images reconstructs whole ideal inclusion. -/
theorem original_ideal_le_iff_all_finiteJet_images
    (I J : Ideal (HolGerm (ComplexModel n))) : I ≤ J ↔
    ∀ q : ℕ, (I.restrictScalars ℂ).map (finiteJet q) ≤ (J.restrictScalars ℂ).map (finiteJet q) := by
  constructor
  · intro h q
    exact Submodule.map_mono h
  · intro h g hg
    apply (mem_original_ideal_iff_all_finiteJet_images J g).mpr
    intro q
    exact h q (Submodule.mem_map.mpr ⟨g,hg,rfl⟩)

/-- BOTH whole original ideal directions follow from equality of ALL genuine jet images. -/
theorem original_ideal_eq_iff_all_finiteJet_images
    (I J : Ideal (HolGerm (ComplexModel n))) : I=J ↔
    ∀ q : ℕ, (I.restrictScalars ℂ).map (finiteJet q)=(J.restrictScalars ℂ).map (finiteJet q) := by
  constructor
  · rintro rfl q
    rfl
  · intro h
    apply le_antisymm
    · exact (original_ideal_le_iff_all_finiteJet_images I J).mpr fun q => (h q).le
    · exact (original_ideal_le_iff_all_finiteJet_images J I).mpr fun q => (h q).ge

/-- A genuine strict original inclusion forces a strict inequality at some EXISTING original HS order. -/
theorem exists_hilbertSamuelValue_lt_of_original_ideal_lt
    (I J : Ideal (HolGerm (ComplexModel n))) (hIJ : I < J) :
    ∃ ℓ : ℕ, hilbertSamuelValue J ℓ < hilbertSamuelValue I ℓ := by
  obtain ⟨g,hgJ,hgI⟩ := SetLike.exists_of_lt hIJ
  obtain ⟨ℓ,hjet⟩ := not_forall.mp
    (mt (mem_original_ideal_iff_all_positive_finiteJet_images I g).mpr hgI)
  let A := (I.restrictScalars ℂ).map (finiteJet (ℓ+1))
  let B := (J.restrictScalars ℂ).map (finiteJet (ℓ+1))
  have hab : A ≤ B := Submodule.map_mono hIJ.le
  have hgb : finiteJet (ℓ+1) g ∈ B := Submodule.mem_map.mpr ⟨g,hgJ,rfl⟩
  have hlt : A < B := lt_of_le_of_ne hab (by
    intro he
    apply hjet
    change finiteJet (ℓ+1) g ∈ A
    rw [he]
    exact hgb)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have hrange : B ≤ LinearMap.range (finiteJet (n := n) (ℓ+1)) := by
    rintro v ⟨a,ha,rfl⟩
    exact LinearMap.mem_range_self _ _
  have hbound := Submodule.finrank_mono hrange
  refine ⟨ℓ,?_⟩
  change Module.finrank ℂ (HolGerm (ComplexModel n) ⧸
      (J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1))) <
    Module.finrank ℂ (HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1)))
  rw [finrank_quotient_eq_jet_rank_sub_ideal_image_rank,
    finrank_quotient_eq_jet_rank_sub_ideal_image_rank]
  change Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ+1)))-Module.finrank ℂ B <
    Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ+1)))-Module.finrank ℂ A
  omega

/-- Under ACTUAL inclusion, the ENTIRE existing HS profile detects equality of the original whole ideals. -/
theorem original_ideal_eq_iff_entire_hs_eq_of_le
    (I J : Ideal (HolGerm (ComplexModel n))) (hIJ : I ≤ J) :
    I=J ↔ ∀ ℓ : ℕ, hilbertSamuelValue I ℓ=hilbertSamuelValue J ℓ := by
  constructor
  · rintro rfl ℓ
    rfl
  · intro h
    by_contra hn
    obtain ⟨ℓ,hlt⟩ := exists_hilbertSamuelValue_lt_of_original_ideal_lt I J (lt_of_le_of_ne hIJ hn)
    rw [h ℓ] at hlt
    exact (lt_irrefl _ hlt)

end
end Hironaka.HironakaActualWholeIdealJetDetection

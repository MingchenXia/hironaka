import Hironaka.Resolution.HironakaG1InitialCompanionSectionPairOrder
import Hironaka.Resolution.HironakaG1InitialCompanionSpecial

/-! Maxima on an initial same-level positive stratum across both section branches. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialPositiveAllStratumCentres
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  CanonicalCentres ResolutionDriver StepOneValue StepOneValueMasked StepOneRegime
  HironakaG1InitialPositiveFiniteCentres HironakaG1InitialCompanionSpecial
  HironakaG1InitialCompanionSectionPairOrder HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualOpenZeroSectionDifferentials
  HironakaActualRelativeNormalGeometry HironakaG8MemberLoci

private theorem special_read_of_level {m k s : ℕ} {X : CMfd.{0} m} (hm : 0 < m)
    (A : MarkedIdeal m X) (x : X) (hs : IsSpecial A (.refl (X := X)) x)
    (hLevel : level A (.refl (X := X)) x = s) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm k) A (.refl (X := X)) x =
      toLex (s, (⊤ : WithTop (ValTy k))) := by
  have hRead := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hm k) A
    (lowerMarkedM A) (.refl (X := X)) hs
  exact hRead.trans (congrArg (fun t => toLex (t, (⊤ : WithTop (ValTy k)))) hLevel)

set_option maxHeartbeats 1400000 in
/-- Every original padded-nonspecial anchor at one initial positive level
has the same pairwise order as a section read. Special sections use the
literal upper top value. Finite sections use the actual supported lower
record on the prescribed companion zero mask. -/
theorem initial_positive_all_stratum_max_loci {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q) {A : Type*} (i : A → productOpen U) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let T := BlowupTower.refl (X := X)
    let P := properNormalMarked Q
    let M := sectionMarked Q
    let V := invFamily (Nat.succ_pos n) k
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1)) P T
    let fM := Seq.StepOneValueMasked.stepOneInvM V M T
    (∀ a : A, i a ∈ P.cosupp ∧ level P T (i a) = s+1 ∧ ¬ IsSpecial P T (i a)) →
    ∃ g : A → WithTop (ValTy k),
      (∀ a : A, IsSpecial M T (i a) →
        fM (i a) = toLex (s+1, g a) ∧ g a = ⊤) ∧
      (∀ a : A, ¬ IsSpecial M T (i a) →
        ∃ (Z : CMfd.{0} (n+1)) (K R : MarkedIdeal (n+1) Z) (r : Z),
          FiniteSectionPair (X := Z) Q k K R r ∧
            g a = (V.inv R (.refl (X := Z)) r : WithTop (ValTy k))) ∧
      (∀ a b : A, f (i a) < f (i b) ↔ g a < g b) ∧
      i '' maxLocus g univ = maxLocus f (range i) ∧
      i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
  classical
  intro X T P M V f fM hAnchor
  let F (a : A) : InitialFiniteRead Q T (i a) k s :=
    Classical.choice (exists_initialFiniteRead Q T (i a) hQ trivial
      (hAnchor a).1 (hAnchor a).2.1 (hAnchor a).2.2 rfl)
  let B := {a : A // ¬ IsSpecial M T (i a)}
  have hSpecial (a : A) : IsSpecial (initialCompanion Q T (i a) s)
      (initialCompanionTower Q T (i a) s) (F a).point ↔ IsSpecial M T (i a) := by
    exact (initial_positive_companion_special_iff Q hQ (i a) (hAnchor a).1
      (hAnchor a).2.1 (F a).point rfl).2
  obtain ⟨gFin, hFin, _, _⟩ := initial_finite_section_stratum_max_loci Q hQ
    (fun a : B => i a.val) (fun a => F a.val)
    (fun a h => a.property ((hSpecial a.val).mp h))
  let g (a : A) : WithTop (ValTy k) :=
    if h : IsSpecial M T (i a) then ⊤ else (gFin ⟨a, h⟩ : WithTop (ValTy k))
  let e (v : WithTop (ValTy k)) : ℕ ×ₗ WithTop (ValTy k) := toLex (0, v)
  have he : StrictMono e := by
    intro u v h
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)
  have hFtop (a : A) (ha : IsSpecial M T (i a)) : (F a).value = e ⊤ :=
    initial_positive_companion_special_value Q hQ (i a) (hAnchor a).1
      (hAnchor a).2.1 ha (F a).point rfl
  have hCut (a b : A) : (F a).value < (F b).value ↔ g a < g b := by
    by_cases ha : IsSpecial M T (i a) <;> by_cases hb : IsSpecial M T (i b)
    · rw [hFtop a ha, hFtop b hb]
      simp [g, ha, hb]
    · obtain ⟨Z, K, R, r, hp, hG, hv⟩ := hFin ⟨b, hb⟩
      rw [hFtop a ha, hv, he.lt_iff_lt]
      simp [g, ha, hb]
    · obtain ⟨Z, K, R, r, hp, hG, hv⟩ := hFin ⟨a, ha⟩
      rw [hFtop b hb, hv, he.lt_iff_lt]
      simp [g, ha, hb]
    · obtain ⟨Z₁, K₁, R₁, r₁, hp₁, hG₁, hv₁⟩ := hFin ⟨a, ha⟩
      obtain ⟨Z₂, K₂, R₂, r₂, hp₂, hG₂, hv₂⟩ := hFin ⟨b, hb⟩
      rw [hv₁, hv₂, he.lt_iff_lt]
      simp only [g, dif_neg ha, dif_neg hb, hG₁, hG₂, WithTop.coe_lt_coe]
      exact hp₁.lt_iff hp₂
  have hLt (a b : A) : f (i a) < f (i b) ↔ g a < g b :=
    (InitialFiniteRead.upper_lt_iff (F a) (F b)).trans (hCut a b)
  have hLe (a b : A) : f (i a) ≤ f (i b) ↔ g a ≤ g b := by
    simpa only [not_lt] using not_congr (hLt b a)
  have hPre : i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
    ext a
    constructor
    · intro ha
      have hm : i a ∈ maxLocus f (range i) := ha
      exact ⟨mem_univ a, fun b _ => (hLe b a).mp (hm.2 (i b) (mem_range_self b))⟩
    · intro ha
      refine ⟨mem_range_self a, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact (hLe b a).mpr (ha.2 b (mem_univ b))
  refine ⟨g, ?_, ?_, hLt, ?_, hPre⟩
  · intro a ha
    have hg : g a = ⊤ := dif_pos ha
    have hLev : level M T (i a) = s+1 :=
      (level_eq_of_E_eq (A := P) (B := M) rfl T (i a)).symm.trans (hAnchor a).2.1
    have hRead : fM (i a) = toLex (s+1, (⊤ : WithTop (ValTy k))) :=
      special_read_of_level (X := X) (k := k) (Nat.succ_pos n) M (i a) ha hLev
    refine ⟨hRead.trans ?_, hg⟩
    exact congrArg (fun t : WithTop (ValTy k) => toLex (s+1, t)) hg.symm
  · intro a ha
    obtain ⟨Z, K, R, r, hp, hG, _⟩ := hFin ⟨a, ha⟩
    exact ⟨Z, K, R, r, hp, (dif_neg ha).trans (congrArg (fun v : ValTy k => (v : WithTop (ValTy k))) hG)⟩
  · rw [← hPre, image_preimage_eq_inter_range]
    exact inter_eq_left.mpr (fun _ h => h.1)

end
end Hironaka.HironakaG1InitialPositiveAllStratumCentres

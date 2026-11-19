import Hironaka.Resolution.HironakaG1LaterLiteralSectionCanonicalTail

/-! The special and finite reads on a common later positive section stratum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterLiteralSectionMixedStratum
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres ResolutionDriver
  StepOneValue StepOneValueMasked StepOneRegime
  HomogenizedIdealAlong CoefficientIdealRestriction
  HironakaG1LaterSectionPairOrder HironakaG1LaterLiteralSectionCanonicalTail
  HironakaG1RecursiveMemberValueTransport HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaActualOpenZeroSectionDifferentials

private theorem special_read_of_level {m k l : ℕ} {X Y : CMfd.{0} m} (hm : 0 < m)
    (A : MarkedIdeal m X) (T : BlowupTower X Y) (y : Y)
    (hs : IsSpecial A T y) (hl : level A T y = l) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hm k) A T y =
      toLex (l, (⊤ : WithTop (ValTy k))) := by
  have h := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (X := X) (invFamily hm k) A
    (lowerMarkedM A) T (y := y) hs
  exact h.trans (congrArg (fun j => toLex (j, (⊤ : WithTop (ValTy k)))) hl)

/-- A special point has the original top read at its actual level along
the literal section history. -/
theorem later_literal_section_special_read {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y) (y : Y)
    (hl : level (sectionMarked Q) T y = s+1) (hsp : IsSpecial (sectionMarked Q) T y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q) T y =
      toLex (s+1, (⊤ : WithTop (ValTy k))) :=
  special_read_of_level (X := CMfd.of (n := n+1) (productOpen U)) (k := k)
    (Nat.succ_pos n) (sectionMarked Q) T y hsp hl

set_option maxHeartbeats 1300000 in
/-- The maximum locus at one positive level is read by the actual
canonical contact suffix at finite anchors and by the literal top at
special anchors. If any special anchor occurs, exactly those anchors
form the common highest stratum. -/
theorem later_literal_section_mixed_stratum {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q) {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q)) T)
    {A : Type*} (i : A → Y)
    (hAnchor : ∀ a : A, i a ∈ (geoTransformAlong (sectionMarked Q) T).cosupp ∧
      level (sectionMarked Q) T (i a) = s+1) :
    let I := invFamily (Nat.succ_pos n) k
    let Sec := sectionMarked Q
    let f := Seq.StepOneValueMasked.stepOneInvM I Sec T
    ∃ g : A → WithTop (ValTy k),
      (∀ a : A, g a = ⊤ ↔ IsSpecial Sec T (i a)) ∧
      (∀ a : A, ¬ IsSpecial Sec T (i a) →
        let y := i a
        let j := regimeRun (stepRegime Sec (s+1)) T y
        let H := head T j
        let F := tail T j
        let p := F.proj y
        ∃ (W : Opens (split T j).1) (u : (split T j).1 → ℂ) (hpW : p ∈ W),
          let L := positiveMemberOn (properNormalMarked Q) H p W
          let S := positiveMemberOn Sec H p W
          let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
          let z : openPreimage F W := ⟨y, hpW⟩
          LaterSectionComparison (X := CMfd.of (n := n+1) W) Q.d k C S ∧
          IsCanonical C (I.inv C) (restrict W F) ∧
          z ∈ (geoTransformAlong C (restrict W F)).cosupp ∧
          g a = (I.inv C (restrict W F) z : WithTop (ValTy k))) ∧
      (∀ a b : A, g a < g b ↔ f (i a) < f (i b)) ∧
      i '' maxLocus g univ = maxLocus f (range i) ∧
      i ⁻¹' maxLocus f (range i) = maxLocus g univ ∧
      ((∃ a : A, IsSpecial Sec T (i a)) →
        maxLocus f (range i) = range i ∩ {y | IsSpecial Sec T y}) := by
  classical
  intro I Sec f
  let B := {a : A // ¬ IsSpecial Sec T (i a)}
  obtain ⟨gFin, hFin, hFinLt, _⟩ := later_literal_section_finite_stratum Q hQ T hMax hCan
    (fun a : B => i a.val)
    (fun a => ⟨(hAnchor a.val).1, (hAnchor a.val).2, a.property⟩)
  let g (a : A) : WithTop (ValTy k) :=
    if h : IsSpecial Sec T (i a) then ⊤ else (gFin ⟨a, h⟩ : WithTop (ValTy k))
  have hgTop (a : A) : g a = ⊤ ↔ IsSpecial Sec T (i a) := by
    by_cases ha : IsSpecial Sec T (i a) <;> simp [g, ha]
  let e (v : WithTop (ValTy k)) : ℕ ×ₗ WithTop (ValTy k) := toLex (s+1, v)
  have he : StrictMono e := by
    intro a b hab
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hab⟩)
  have hTop (a : A) (ha : IsSpecial Sec T (i a)) : f (i a) = e ⊤ :=
    later_literal_section_special_read (k := k) Q T (i a) (hAnchor a).2 ha
  have hBelow (a : A) (ha : ¬ IsSpecial Sec T (i a)) : f (i a) < e ⊤ := by
    obtain ⟨W, u, hpW, hW, hPair, hC, hS, hx, hRead⟩ :=
      later_literal_section_finite_read Q hQ T (i a)
        (hAnchor a).1 (hAnchor a).2 ha hMax hCan
    have hv : f (i a) = e _ := hRead
    rw [hv, he.lt_iff_lt]
    exact WithTop.coe_lt_top _
  have hLt (a b : A) : g a < g b ↔ f (i a) < f (i b) := by
    by_cases ha : IsSpecial Sec T (i a) <;> by_cases hb : IsSpecial Sec T (i b)
    · rw [hTop a ha, hTop b hb]
      simp [g, ha, hb]
    · rw [hTop a ha]
      exact iff_of_false (by simp [g, ha]) (not_lt_of_ge (hBelow b hb).le)
    · rw [hTop b hb]
      exact iff_of_true (by simp [g, ha, hb]) (hBelow a ha)
    · simpa only [g, dif_neg ha, dif_neg hb, WithTop.coe_lt_coe] using hFinLt ⟨a, ha⟩ ⟨b, hb⟩
  have hLe (a b : A) : g a ≤ g b ↔ f (i a) ≤ f (i b) := by
    simpa only [not_lt] using not_congr (hLt b a)
  have hPre : i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
    ext a
    constructor
    · intro ha
      have hm : i a ∈ maxLocus f (range i) := ha
      exact ⟨mem_univ a, fun b _ => (hLe b a).mpr (hm.2 (i b) (mem_range_self b))⟩
    · intro ha
      refine ⟨mem_range_self a, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact (hLe b a).mp (ha.2 b (mem_univ b))
  have hImg : i '' maxLocus g univ = maxLocus f (range i) := by
    rw [← hPre, image_preimage_eq_inter_range]
    exact inter_eq_left.mpr (fun _ h => h.1)
  refine ⟨g, hgTop, ?_, hLt, hImg, hPre, ?_⟩
  · intro a ha
    obtain ⟨W, u, hpW, hPair, hC, hCos, hg⟩ := hFin ⟨a, ha⟩
    refine ⟨W, u, hpW, hPair, hC, hCos, (dif_neg ha).trans ?_⟩
    exact congrArg (fun v : ValTy k => (v : WithTop (ValTy k))) hg
  · rintro ⟨b, hb⟩
    have hgb : g b = ⊤ := (hgTop b).mpr hb
    ext y
    constructor
    · rintro ⟨⟨a, rfl⟩, hMaxa⟩
      have hba := (hLe b a).mpr (hMaxa _ (mem_range_self b))
      rw [hgb] at hba
      exact ⟨mem_range_self a, (hgTop a).mp (top_le_iff.mp hba)⟩
    · rintro ⟨⟨a, rfl⟩, hSa⟩
      refine ⟨mem_range_self a, ?_⟩
      rintro _ ⟨c, rfl⟩
      exact (hLe c a).mp ((hgTop a).mpr hSa ▸ le_top)

/-- If the highest level is attained, the original section maximum
locus may be computed just on that level, before comparing the finite
and special values there. -/
theorem later_literal_section_max_locus_highest_level {n k l : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (S : Set Y) (hBound : ∀ y ∈ S, level (sectionMarked Q) T y ≤ l)
    (hAttained : ∃ y ∈ S, level (sectionMarked Q) T y = l) :
    let Sec := sectionMarked Q
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) Sec T
    maxLocus f S = maxLocus f (S ∩ {y | level Sec T y = l}) := by
  intro Sec f
  let X₀ := CMfd.of (n := n+1) (productOpen U)
  let I := invFamily (Nat.succ_pos n) k
  have hFirst (y : Y) : (ofLex (f y)).1 = level Sec T y :=
    Seq.StepOneValueMasked.stepOneInvL_fst (X := X₀) I Sec (lowerMarkedM (X := X₀) Sec) T y
  have hLt (x y : Y) (h : level Sec T x < level Sec T y) : f x < f y := by
    apply Prod.Lex.lt_iff.mpr
    exact Or.inl (by rwa [hFirst, hFirst])
  obtain ⟨p, hp, hpL⟩ := hAttained
  ext y
  constructor
  · rintro ⟨hy, hyMax⟩
    have hLy : level Sec T y = l := by
      apply le_antisymm (hBound y hy)
      by_contra! hLt'
      exact (not_lt_of_ge (hyMax p hp)) (hLt y p (hpL.symm ▸ hLt'))
    exact ⟨⟨hy, hLy⟩, fun p hp => hyMax p hp.1⟩
  · rintro ⟨⟨hy, hyL⟩, hyMax⟩
    refine ⟨hy, fun p hp => ?_⟩
    rcases lt_or_eq_of_le (hBound p hp) with hLt' | hEq
    · exact (hLt p y (hyL.symm ▸ hLt')).le
    · exact hyMax p ⟨hp, hEq⟩

end
end Hironaka.HironakaG1LaterLiteralSectionMixedStratum

import Hironaka.Resolution.HironakaG8P1ForeignCount
import Hironaka.Resolution.HironakaOriginalSmoothIntrinsicRegularLoci

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# BM08 Theorem 6.1 for different carriers, from one common arc tower (G8B lane, run 0080; port P1, step (iv))

Blueprint: `hironaka-g8-p1-assembly.tex`.  Plan: `work/hironaka-resume-20261111/G8B/REPORT-r1.md` §2 (iv).

Source: Bierstone–Milman 2008, §6, Theorem 6.1 and its proof (the set `S ⊆ ℕ × ℕ` "depends only on `dim N` and the
weak-equivalence class").  Here the two records `A` (carrier `N`) and `B` (carrier `P`) are compared through ONE arc
tower `T_q` over the product with a line and TWO Cartier families `G_A`, `G_B` on its last stage (centres `N_s ∩ D_s`,
resp. `P_s ∩ D_s`), each with its own exact counts (`CartierQueryCountOutput`), sharing the arc point `z`:

* `sameCarrierDim_projectionTest`: equal carrier dimensions on the cosupport pass to the products with a line;
* `count_zero_exponent`, `foreignInv_zero`: the stage-`0` data of a Cartier family, read on the record itself;
* `le_of_cross`: if the family of the first record counts `s·d₁ ≤ β₁` and every test of the first projected record is one
  of the second, then `s·d₂ ≤ β₂` (via `HironakaG8P1ForeignCount.foreign_count`, the second record along the FIRST
  record's family);
* `eq_of_bounds`: the arithmetic — with `β_A = q(ρ_A − d_A)`, `β_B = q(ρ_B − d_B)`, `q = d_A d_B`, the two implications
  force `d_B ρ_A = d_A ρ_B`;
* **`normalized_order_eq_of_common_tower`**: Theorem 6.1 (`B.d · ord_x A = A.d · ord_x B`) for `WEquiv` projection tests,
  `SameCarrierDim`, and a common arc tower carrying both families.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1Assembly

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec NormalCrossings DivisorExponentAlong GermIdealOrder
  HironakaActualSharedCartierTraceTests HironakaActualProjectionTestRecord HironakaG8P1ForeignCount
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open scoped Hironaka.ProductComplexManifold

noncomputable section

/-! ### Products with a line keep equal carrier dimensions -/

/-- **Equal carrier dimensions on the cosupport pass to the products with a line.** -/
theorem sameCarrierDim_projectionTest {n kA kB : ℕ} {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hA : IsInvDomain kA A) (_hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) :
    SameCarrierDim (projectionTest A) (projectionTest B) := by
  intro p hp j
  have hp' : p.1 ∈ A.cosupp := by
    have h := (projection_test_dictionary A hA).2.2.2.2.2.2.2
    rw [h] at hp
    exact hp
  obtain ⟨d, hd⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 p.1 (A.cosupp_subset_N hp')
  have hdB : RegularAtDim (n := n) B.N p.1 d := (hdim p.1 hp' d).mp hd
  have hsub := (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X)
    (Y := ComplexModel 1)).isSubmersionAt p
  have h1 := (HironakaOriginalSmoothIntrinsicRegularLoci.regularAtDim_preimage_iff
    (X := X) (Y := projectionAmbient X) hsub A.N d).mpr hd
  have h2 := (HironakaOriginalSmoothIntrinsicRegularLoci.regularAtDim_preimage_iff
    (X := X) (Y := projectionAmbient X) hsub B.N d).mpr hdB
  exact HironakaG8SpecialLoci.regularAtDim_iff_of_regularAtDim h1 h2 j

/-! ### Stage `0` of a Cartier family -/

section StageZero

variable {m : ℕ} {Y : CMfd.{u} m}

/-- **The stage-`0` exponent of a counted record**: if the family's stage `0` is the geometry of `Q` (carrier, boundary,
last member, arc point `z`), the count output says that `z` lies on the carrier and on the last member and that the
exponent of `Q` along the last member at `z` is exactly `β`. -/
theorem count_zero_exponent {k : ℕ} (G : CartierGeometryFamily Y) (Q : MarkedIdeal m Y) (β : ℕ) (z : Y)
    (hC : CartierQueryCountOutput (k := k) Q β G) (hN : HEq (G.state 0).N Q.N) (hE : HEq (G.state 0).E Q.E)
    (hi : ((G.state 0).i).val + 1 = (G.state 0).E.length) (hz : HEq (G.state 0).z z) :
    ∃ hne : Q.E ≠ [], z ∈ Q.N ∧ z ∈ Q.E.getLast hne ∧
      ∀ e, IsDivNearAlong m Q.N Q.ideal (Q.E.getLast hne) e z ↔ e ≤ β := by
  obtain ⟨-, -, -, htest, hrest⟩ := hC.1 0
  have ht0 : IsGeoTestTower Q (G.state 0).R := htest.mpr (by simp)
  obtain ⟨-, -, hw⟩ := hrest ht0
  obtain ⟨-, hcuts, -⟩ := hw (G.state 0).z (G.state 0).hz
  have hzmem := (G.state 0).hz
  have hY := G.zeroAmbient
  have hR := G.zeroTower
  revert hcuts hzmem hN hE hi hz hY hR
  generalize G.state 0 = s
  obtain ⟨Y', R, N, E, i, z', hN', hE', hT', hz'⟩ := s
  intro hN hE hi hz hcuts hzmem hY hR
  dsimp only at hY hR hN hE hi hz hzmem hcuts
  subst hY
  obtain rfl := eq_of_heq hR
  obtain rfl := eq_of_heq hN
  obtain rfl := eq_of_heq hE
  obtain rfl := eq_of_heq hz
  have hne : Q.E ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have hlast : Q.E.get i = Q.E.getLast hne := by
    rw [List.getLast_eq_getElem]
    simp only [List.get_eq_getElem]
    congr 1
    omega
  refine ⟨hne, hzmem.1, hlast ▸ hzmem.2, fun e => ?_⟩
  have h := hcuts e
  rw [geoTransformAlong_refl, hlast, Nat.zero_mul, Nat.sub_zero] at h
  exact h

/-- **The foreign invariant at stage `0`**, read on the record: the family's stage `0` has the geometry of a record `Q'`
(carrier `N`, boundary `E = Q.E`, last member, arc point `z`), and `Q` (carrier `P`, possibly different) has exponent `β`
along the last member at `z` and the same carrier dimension at `z` as `Q'`. -/
theorem foreignInv_zero (G : CartierGeometryFamily Y) (Q Q' : MarkedIdeal m Y) (β : ℕ) (z : Y)
    (hN : HEq (G.state 0).N Q'.N) (hE : HEq (G.state 0).E Q'.E) (hi : ((G.state 0).i).val + 1 = (G.state 0).E.length)
    (hz : HEq (G.state 0).z z) (hQE : Q.E = Q'.E) (D : Set Y) (hne : Q'.E ≠ []) (hD : Q'.E.getLast hne = D)
    (hExp : z ∈ Q.N → ∀ e, IsDivNearAlong m Q.N Q.ideal D e z ↔ e ≤ β)
    (hDim : z ∈ Q.N → ∃ k, RegularAtDim (n := m) Q'.N z k ∧ RegularAtDim (n := m) Q.N z k) :
    (Q.geoTransformAlong (G.state 0).R).E = (G.state 0).E ∧ ForeignInv G Q β 0 := by
  unfold ForeignInv
  have hY := G.zeroAmbient
  have hR := G.zeroTower
  revert hN hE hi hz hY hR
  generalize G.state 0 = s
  obtain ⟨Y', R, N, E, i, z', hN', hE', hT', hz'⟩ := s
  intro hN hE hi hz hY hR
  dsimp only at hY hR hN hE hi hz ⊢
  subst hY
  obtain rfl := eq_of_heq hR
  obtain rfl := eq_of_heq hN
  obtain rfl := eq_of_heq hE
  obtain rfl := eq_of_heq hz
  rw [geoTransformAlong_refl]
  refine ⟨hQE, fun hzQ => ⟨fun e => ?_, hDim hzQ⟩⟩
  have hlast : Q'.E.get i = D := by
    rw [← hD, List.getLast_eq_getElem]
    simp only [List.get_eq_getElem]
    congr 1
    omega
  rw [hlast, Nat.zero_mul, Nat.sub_zero]
  exact hExp hzQ e

end StageZero

/-! ### The cross comparison and the arithmetic -/

/-- **One direction of the comparison**: if the family of the first projected record counts `s·d₁ ≤ β₁`, and every test
of the first record is one of the second, then the second record's count along the FIRST family gives `s·d₂ ≤ β₂`. -/
theorem le_of_cross {m : ℕ} {W : CMfd.{u} m} (P₁ P₂ : MarkedIdeal m W)
    (hEq : ∀ {Z : CMfd.{u} m} (T : BlowupTower W Z), IsGeoTestTower P₁ T → IsGeoTestTower P₂ T)
    {Yq : CMfd.{u} m} (Tq : BlowupTower W Yq) (G : CartierGeometryFamily Yq) {k₁ k₂ : ℕ} (β₁ β₂ : ℕ)
    (hT : IsGeoTestTower P₁ Tq) (hD₂ : IsInvDomain k₂ (P₂.geoTransformAlong Tq))
    (hC : CartierQueryCountOutput (k := k₁) (P₁.geoTransformAlong Tq) β₁ G)
    (hE0 : ((P₂.geoTransformAlong Tq).geoTransformAlong (G.state 0).R).E = (G.state 0).E)
    (h0 : ForeignInv G (P₂.geoTransformAlong Tq) β₂ 0) (s : ℕ) (hs : s * P₁.d ≤ β₁) : s * P₂.d ≤ β₂ := by
  have hd₁ : (P₁.geoTransformAlong Tq).d = P₁.d := d_geoTransformAlong P₁ Tq
  have hd₂ : (P₂.geoTransformAlong Tq).d = P₂.d := d_geoTransformAlong P₂ Tq
  have htest : IsGeoTestTower (P₁.geoTransformAlong Tq) (G.state s).R :=
    ((hC.1 s).2.2.2.1).mpr (by rw [hd₁]; exact hs)
  have h1 : IsGeoTestTower P₁ (Tq.append (G.state s).R) := (isGeoTestTower_append_iff P₁ Tq _).mpr ⟨hT, htest⟩
  have h3 := ((isGeoTestTower_append_iff P₂ Tq _).mp (hEq _ h1)).2
  have h4 := (foreign_count G _ hD₂ β₂ hE0 h0 s h3).1
  rw [hd₂] at h4
  exact h4

/-- **The arithmetic of the two counts** (`q = d_A d_B`). -/
theorem eq_of_bounds (dA dB ρA ρB : ℕ) (hdA : 0 < dA) (hdB : 0 < dB) (hA : dA ≤ ρA) (hB : dB ≤ ρB)
    (h₁ : ∀ s, s * dA ≤ dA * dB * (ρA - dA) → s * dB ≤ dA * dB * (ρB - dB))
    (h₂ : ∀ s, s * dB ≤ dA * dB * (ρB - dB) → s * dA ≤ dA * dB * (ρA - dA)) :
    dB * ρA = dA * ρB := by
  obtain ⟨a, rfl⟩ : ∃ a, ρA = dA + a := ⟨ρA - dA, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, ρB = dB + b := ⟨ρB - dB, by omega⟩
  simp only [Nat.add_sub_cancel_left] at h₁ h₂
  have e1 := h₁ (dB * a) (le_of_eq (by ring))
  have e2 := h₂ (dA * b) (le_of_eq (by ring))
  have f1 : dB * a ≤ dA * b := by
    have h : dB * a * dB ≤ dA * b * dB := by
      calc dB * a * dB ≤ dA * dB * b := e1
        _ = dA * b * dB := by ring
    exact Nat.le_of_mul_le_mul_right h hdB
  have f2 : dA * b ≤ dB * a := by
    have h : dA * b * dA ≤ dB * a * dA := by
      calc dA * b * dA ≤ dA * dB * a := e2
        _ = dB * a * dA := by ring
    exact Nat.le_of_mul_le_mul_right h hdA
  have hab : dB * a = dA * b := le_antisymm f1 f2
  calc dB * (dA + a) = dA * dB + dB * a := by ring
    _ = dA * dB + dA * b := by rw [hab]
    _ = dA * (dB + b) := by ring

/-! ### The theorem from a common arc tower -/

/-- **Bierstone–Milman 2008, Theorem 6.1, for different carriers, from one common arc tower.**  `A` (carrier `N`) and `B`
(carrier `P`) in the native domain, with Włodarczyk-equivalent products with a line and the same carrier dimensions on
the cosupport; `T_q` a multiple test blowup of the product of `A` (`q = A.d·B.d`), and two Cartier families `G_A`, `G_B`
on its last stage, with the geometry of `A_q`, resp. `B_q`, at the same arc point `z` of the cosupport, and with the exact
counts `β_A = q(ρ_A − A.d)`, `β_B = q(ρ_B − B.d)`.  Then `B.d · ρ_A = A.d · ρ_B`. -/
theorem normalized_order_eq_of_common_tower {n kA kB : ℕ} {X : CMfd.{u} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (ρA ρB : ℕ) (hρA : A.d ≤ ρA) (hρB : B.d ≤ ρB)
    (hW : WEquiv (projectionTest A) (projectionTest B)) (hdim : SameCarrierDim A B)
    {Yq : CMfd.{u} (n+1)} (Tq : BlowupTower (projectionAmbient X) Yq) (hTA : IsGeoTestTower (projectionTest A) Tq)
    (GA GB : CartierGeometryFamily Yq) (z : Yq) (hzA : z ∈ ((projectionTest A).geoTransformAlong Tq).cosupp)
    (hCA : CartierQueryCountOutput (k := kA + 1) ((projectionTest A).geoTransformAlong Tq)
      (A.d * B.d * (ρA - A.d)) GA)
    (hNA : HEq (GA.state 0).N ((projectionTest A).geoTransformAlong Tq).N)
    (hEA : HEq (GA.state 0).E ((projectionTest A).geoTransformAlong Tq).E)
    (hiA : ((GA.state 0).i).val + 1 = (GA.state 0).E.length) (hzGA : HEq (GA.state 0).z z)
    (hCB : CartierQueryCountOutput (k := kB + 1) ((projectionTest B).geoTransformAlong Tq)
      (A.d * B.d * (ρB - B.d)) GB)
    (hNB : HEq (GB.state 0).N ((projectionTest B).geoTransformAlong Tq).N)
    (hEB : HEq (GB.state 0).E ((projectionTest B).geoTransformAlong Tq).E)
    (hiB : ((GB.state 0).i).val + 1 = (GB.state 0).E.length) (hzGB : HEq (GB.state 0).z z) :
    B.d * ρA = A.d * ρB := by
  set QA := (projectionTest A).geoTransformAlong Tq with hQA
  set QB := (projectionTest B).geoTransformAlong Tq with hQB
  have hTB : IsGeoTestTower (projectionTest B) Tq := (hW.2 Tq).1.mp hTA
  have hDA : IsInvDomain (kA + 1) QA :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong (projection_test_isInvDomain A hA) Tq hTA
  have hDB : IsInvDomain (kB + 1) QB :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong (projection_test_isInvDomain B hB) Tq hTB
  have hEAB : QA.E = QB.E := MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1 Tq
  have hdimQ : SameCarrierDim QA QB :=
    HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong (projection_test_isInvDomain A hA).isWellFormed
      (projection_test_isInvDomain B hB).isWellFormed hW (sameCarrierDim_projectionTest hA hB hdim) Tq hTA
  obtain ⟨kz, hkz⟩ := hDA.isWellFormed.isClosedSubmanifold_N.2 z (QA.cosupp_subset_N hzA)
  have hkzB : RegularAtDim (n := n + 1) QB.N z kz := (hdimQ z hzA kz).mp hkz
  obtain ⟨hneA, -, -, hExpA⟩ := count_zero_exponent GA QA _ z hCA hNA hEA hiA hzGA
  obtain ⟨hneB, -, -, hExpB⟩ := count_zero_exponent GB QB _ z hCB hNB hEB hiB hzGB
  -- `B` along `A`'s family
  have hlastEq : ∀ (l₁ l₂ : List (Set Yq)) (h : l₁ = l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
      l₁.getLast h₁ = l₂.getLast h₂ := by
    rintro _ _ rfl _ _
    rfl
  obtain ⟨hE0B, h0B⟩ := foreignInv_zero GA QB QA (A.d * B.d * (ρB - B.d)) z hNA hEA hiA hzGA hEAB.symm
    (QB.E.getLast hneB) hneA (hlastEq _ _ hEAB _ _) (fun _ e => hExpB e) (fun _ => ⟨kz, hkz, hkzB⟩)
  -- `A` along `B`'s family
  obtain ⟨hE0A, h0A⟩ := foreignInv_zero GB QA QB (A.d * B.d * (ρA - A.d)) z hNB hEB hiB hzGB hEAB
    (QA.E.getLast hneA) hneB (hlastEq _ _ hEAB.symm _ _) (fun _ e => hExpA e) (fun _ => ⟨kz, hkzB, hkz⟩)
  have hdA : 0 < A.d := by have := hA.one_le_d; omega
  have hdB : 0 < B.d := by have := hB.one_le_d; omega
  have h₁ : ∀ s, s * A.d ≤ A.d * B.d * (ρA - A.d) → s * B.d ≤ A.d * B.d * (ρB - B.d) :=
    fun s hs => le_of_cross (projectionTest A) (projectionTest B) (fun T hT => (hW.2 T).1.mp hT) Tq GA _ _ hTA hDB
      hCA hE0B h0B s hs
  have h₂ : ∀ s, s * B.d ≤ A.d * B.d * (ρB - B.d) → s * A.d ≤ A.d * B.d * (ρA - A.d) :=
    fun s hs => le_of_cross (projectionTest B) (projectionTest A) (fun T hT => (hW.2 T).1.mpr hT) Tq GB _ _ hTB hDA
      hCB hE0A h0A s hs
  exact eq_of_bounds A.d B.d ρA ρB hdA hdB hρA hρB h₁ h₂

end

end Hironaka.HironakaG8P1Assembly

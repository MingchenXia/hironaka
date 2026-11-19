import Hironaka.Resolution.HironakaG8FreshNativeFirstCentreOverlap
import Hironaka.Resolution.HironakaG8NativeCompactShrink

open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8FreshNativeCompactFirstCut
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver HironakaG11PresLineState
  HironakaG8FreshNativeFirstCentreOverlap HironakaActualPowerBoundaryExponents
  HironakaActualVanishingIntrinsicHSTransport HironakaEmbeddedAnalytic
  HironakaHolomorphicJetChartInvariance CanonicalCentres
  HironakaG8NativeGlobalSuccessor HironakaG8NativeCompactShrink
  HironakaG1OriginalUnequalMarkCanonical

/-- A finite atlas of positive marks has a literal common whole-power mark. -/
theorem exists_common_positive_whole_power_mark {I : Type*} [Fintype I]
    (mark : I → ℕ) (hMark : ∀ i, 0 < mark i) :
    ∃ (e : I → ℕ) (d : ℕ), 0 < d ∧ (∀ i, 1 ≤ e i) ∧ ∀ i, mark i * e i = d := by
  classical
  let d := ∏ i, mark i
  have hd : 0 < d := Finset.prod_pos fun i _ => hMark i
  have hDiv (i : I) : mark i ∣ d := Finset.dvd_prod_of_mem mark (Finset.mem_univ i)
  choose e he using hDiv
  exact ⟨e,d,hd,fun i => Nat.one_le_iff_ne_zero.mpr fun hz =>
    (Nat.ne_of_gt hd) (by rw [he i,hz,Nat.mul_zero]),fun i => (he i).symm⟩

/-- On a compact covered profile fibre the original window invariants give
an attained common numerical key. Its cut is one genuine ambient blowup and
every chart trace, including an empty trace, yields a canonical first step. -/
theorem exists_fresh_native_compact_first_cut
    {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n} {I : Type}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : ℕ → ℕ) (E : List (Set X)) (U : I → Opens X)
    (F : Set X) (hFibre : F = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ})
    (hF : IsCompact F) (hNe : F.Nonempty) (hSing : F ⊆ singularSet (n := n) W)
    (hCover : ∀ x ∈ F, ∃ i, x ∈ U i)
    (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain k (P i))
    (hState : ∀ i, NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H)
    (hE : ∀ i, (P i).E = E.map ((Subtype.val : U i → X) ⁻¹' ·))
    (e : I → ℕ) (he : ∀ i, 1 ≤ e i) (d : ℕ)
    (hd : ∀ i, (powerMarked (P i) (e i)).d = d)
    (hNot : ∀ D ∈ E, ∀ x ∈ F, x ∈ D → ¬ ∀ᶠ y in 𝓝 x, y ∈ D → y ∈ W) :
    let Q := fun i => powerMarked (P i) (e i)
    let R := invFamily hn k
    ∃ (m : ValTy k) (C : Set X) (Y : CMfd.{0} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ F ∧ IsProperMap π ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
        (.step .refl C π hπ) ∧
      (∀ i (x : U i), x ∈ (Q i).cosupp → R.inv (Q i) .refl x ≤ m) ∧
      (∀ i, (Subtype.val : U i → X) ⁻¹' C =
        {x | x ∈ (Q i).cosupp ∧ R.inv (Q i) .refl x = m}) ∧
      (∀ i {Z : CMfd.{0} n} (ρ : Z → U i)
        (hρ : IsBlowupAlong n ((Subtype.val : U i → X) ⁻¹' C) ρ),
        IsCanonical (P i) (R.inv (P i))
          (.step .refl ((Subtype.val : U i → X) ⁻¹' C) ρ hρ) ∧
        ∀ z ∈ (geoTransformAlong (Q i) (.step .refl ((Subtype.val : U i → X) ⁻¹' C) ρ hρ)).cosupp,
          R.inv (Q i) (.step .refl ((Subtype.val : U i → X) ⁻¹' C) ρ hρ) z < m) ∧
      (∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) (.step .refl C π hπ))) := by
  intro Q R
  have hQ (i : I) : IsInvDomain k (Q i) := powerMarked_isInvDomain (P i) (hP i) (he i)
  have hRaw (i : I) (x : U i) : x ∈ (P i).cosupp ↔ x.val ∈ F := by
    rw [(hState i).cosupp_eq,hFibre]
    simp only [Set.mem_ofPred_eq,hilbertSamuelAt_vanishing_actual_open_any]
  have hCos (i : I) (x : U i) : x ∈ (Q i).cosupp ↔ x.val ∈ F := by
    rw [show (Q i).cosupp = (P i).cosupp from powerMarked_cosupp (P i) (hP i) (he i)]
    exact hRaw i x
  have hOverlap (i j : I) (x : X) (hi : x ∈ U i) (hj : x ∈ U j)
      (hx : (⟨x,hi⟩ : U i) ∈ (Q i).cosupp) :
      (⟨x,hj⟩ : U j) ∈ (Q j).cosupp ∧ R.inv (Q i) .refl ⟨x,hi⟩ = R.inv (Q j) .refl ⟨x,hj⟩ := by
    obtain ⟨hc,hv⟩ := fresh_native_first_values_agree hn (U i) (U j) (P i) (P j) (hP i) (hP j)
      W H (hState i) (hState j) E (hE i) (hE j) (e i) (e j) (he i) (he j)
      ((hd i).trans (hd j).symm) (fun D hD y hy hyD => hNot D hD y.val ((hRaw i y).mp hy) hyD) hi hj
    exact ⟨hc.mp hx,hv hx⟩
  have hCover' (x : X) (hx : x ∈ F) :
      ∃ (i : I) (hi : x ∈ U i), (⟨x,hi⟩ : U i) ∈ (Q i).cosupp := by
    obtain ⟨i,hi⟩ := hCover x hx
    exact ⟨i,hi,(hCos i _).mpr hx⟩
  have hFoot (i : I) (x : U i) (hx : x ∈ (Q i).cosupp) : x.val ∈ F := (hCos i x).mp hx
  obtain ⟨m,hUpper,hAttain⟩ := exists_actual_native_compact_maximum R U F hF hNe Q hQ hCover' hFoot hOverlap
  have hCut (i : I) (x : U i) (hx : x ∈ (Q i).cosupp) :
      x.val ∈ singularSet (n := n) W ∧ ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x.val ℓ = H ℓ := by
    have hxF := hFoot i x hx
    refine ⟨hSing hxF,?_⟩
    rwa [hFibre] at hxF
  obtain ⟨C,Y,π,hπ,hC,hCF,_,hProper,hTest,hTrace,_,_⟩ :=
    exists_actual_native_global_maximum_blowup R hW E U F hF.isClosed hCover Q hQ hE
      H hCut hFoot hOverlap m hUpper hAttain
  have hLocal (i : I) {Z : CMfd.{0} n} (ρ : Z → U i)
      (hρ : IsBlowupAlong n ((Subtype.val : U i → X) ⁻¹' C) ρ) :
      IsCanonical (P i) (R.inv (P i))
        (.step .refl ((Subtype.val : U i → X) ⁻¹' C) ρ hρ) ∧
      ∀ z ∈ (geoTransformAlong (Q i) (.step .refl ((Subtype.val : U i → X) ⁻¹' C) ρ hρ)).cosupp,
        R.inv (Q i) (.step .refl ((Subtype.val : U i → X) ⁻¹' C) ρ hρ) z < m := by
    obtain ⟨hCan,hBelow⟩ := canonical_step_and_values_lt_of_value_cut R (Q i) (hQ i) .refl trivial
      m (hUpper i) _ ρ hρ (hTrace i)
    exact ⟨(invFamily_isCanonical_power_iff hn (P i) (hP i) (e i) (he i) _).mpr hCan,hBelow⟩
  refine ⟨m,C,Y,π,hπ,hC,hCF,hProper,hTest,hUpper,hTrace,hLocal,?_⟩
  intro i
  exact (hLocal i _ (isBlowupAlong_restrict hπ (U i)
    ((U i).isOpen.preimage hπ.contMDiff.continuous))).1

end
end Hironaka.HironakaG8FreshNativeCompactFirstCut

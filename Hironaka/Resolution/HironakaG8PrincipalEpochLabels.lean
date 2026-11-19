import Hironaka.Resolution.HironakaG8PrincipalEpochSuccession
import Hironaka.Resolution.HironakaG1RHypersurfaceRecord

/-! Hilbert--Samuel profile reads along exact finite principal atlas histories. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalEpochLabels
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaEmbeddedAnalytic HironakaG8NativePhaseCertificate
  HironakaG8PrincipalEpochSuccession HironakaHolomorphicJetChartInvariance

variable {n : ℕ} {X A Z : CMfd.{0} (n+1)}
  {M : MarkedIdeal (n+1) X} {W : Set X} {P : BlowupTower X A}
  {cap last : ℕ} {T : BlowupTower A Z} {labels : List ((ℕ → ℕ) × ℕ)}

local notation "HS[" U "]" => hilbertSamuelAt (vanishingIdeal (n := n+1) U)

/-- The physical projection relates every final profile to the profile at
the start of the supplied finite succession. -/
theorem profile_nonincrease
    (h : PrincipalAtlasEpochs M W P cap T labels last) :
    ∀ z ℓ, HS[strictTransform (n+1) (P.append T).proj W] z ℓ ≤
      HS[strictTransform (n+1) P.proj W] (T.proj z) ℓ := by
  induction h with
  | done _ _ => intro z ℓ; exact le_rfl
  | next _ _ phase _ _ _ ih =>
    intro z ℓ
    rw [← BlowupTower.append_assoc]
    apply (ih z ℓ).trans
    rw [BlowupTower.proj_append, StrictTransformComposition.strictTransform_comp
      (by apply BlowupTower.contMDiff_proj) (by apply BlowupTower.contMDiff_proj)]
    simpa only [BlowupTower.proj_append, Function.comp_apply] using phase.nonincrease _ ℓ

/-- A label on an actual first phase remains strictly cleared over the
initial label locus after any further principal atlas phases. -/
theorem first_label_stays_cleared {H : ℕ → ℕ} {q : ℕ}
    (h : PrincipalAtlasEpochs M W P cap T ((H,q) :: labels) last) :
    ∀ z ∈ T.proj ⁻¹' phaseLevel (strictTransform (n+1) P.proj W) H,
      toLex (HS[strictTransform (n+1) (P.append T).proj W] z) < toLex H := by
  cases h with
  | next _ _ phase _ _ rest =>
    intro z hz
    rw [← BlowupTower.append_assoc]
    have hLe := Pi.toLex_monotone (profile_nonincrease rest z)
    apply hLe.trans_lt
    rw [BlowupTower.proj_append, StrictTransformComposition.strictTransform_comp
      (by apply BlowupTower.contMDiff_proj) (by apply BlowupTower.contMDiff_proj)]
    exact phase.strictDrop _ (by rwa [mem_preimage, BlowupTower.proj_append, Function.comp_apply] at hz)


open GermIdealOrder HironakaG1RHypersurfaceRecord HomogenizedIdealAlong

/-- For nonzero principal hypersurface germs the strict order of actual
Hilbert--Samuel profiles is exactly the strict order of multiplicities. -/
theorem principal_profile_lt_iff_order_lt {B : CMfd.{0} (n+1)}
    (I : GermIdeal (n+1) A) (J : GermIdeal (n+1) B)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (x : A) (y : B) :
    toLex (hilbertSamuelAt I x) < toLex (hilbertSamuelAt J y) ↔
      order (n+1) univ I x < order (n+1) univ J y := by
  obtain ⟨a,ha,hHa⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS I hI x
  obtain ⟨b,hb,hHb⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS J hJ y
  rw [ha,hb,funext hHa,funext hHb]
  constructor
  · intro h
    by_contra hn
    have hab : b ≤ a := by exact_mod_cast (le_of_not_gt hn)
    exact (not_le_of_gt h) (Pi.toLex_monotone (hypersurfaceHS_mono (n+1) hab))
  · intro h
    have hab : a < b := by exact_mod_cast h
    apply lt_of_le_of_ne (Pi.toLex_monotone (hypersurfaceHS_mono (n+1) hab.le))
    intro he
    have hEq := eq_of_hypersurfaceHS_eq (n+1)
      (congrFun (congrArg (ofLex : Lex (ℕ → ℕ) → ℕ → ℕ) he))
    exact (ne_of_lt hab) hEq

/-- A genuine global maximal principal profile gives the required order
cap once its order is read at a point attaining that profile. -/
theorem principal_order_cap_of_maximal_profile
    (I : GermIdeal (n+1) A) (hI : I.IsInvertible) (hC : I.IsCoherent) (a : A) (q : ℕ)
    (ha : order (n+1) univ I a = q)
    (hMax : ∀ x, toLex (hilbertSamuelAt I x) ≤ toLex (hilbertSamuelAt I a)) :
    IsMaximalOrderAlong univ I q := by
  intro x hx
  have hOrder : (↑(q+1) : ℕ∞) ≤ order (n+1) univ I x :=
    (le_order_iff (𝔞 := I) (fun g hg => by
      obtain ⟨U,_,hxU,N,f,_,hf⟩ := hC x
      exact ((hf x hxU g).mp hg).1)).2 hx.2
  have hLt : order (n+1) univ I a < order (n+1) univ I x := by
    rw [ha]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self q) hOrder
  exact (not_lt_of_ge (hMax x)) ((principal_profile_lt_iff_order_lt I I hI hI a x).2 hLt)


open HironakaG8NativeRelativeClearing HironakaG8OccupiedAtlasRestart
  HironakaG11PresLineState HironakaActualVanishingIntrinsicHSTransport

/-- Literal native charts already imply the needed whole order cap as
soon as one point identifies the native label with the proposed mark. -/
theorem principal_order_cap_of_exact_covered_native_atlas
    (U : Set A) (E : List (Set A)) (H : ℕ → ℕ) (S : BlowupTower A Z)
    (q : ℕ) (a : A)
    (hI : (vanishingIdeal (n := n+1) U).IsInvertible)
    (ha : order (n+1) univ (vanishingIdeal (n := n+1) U) a = q)
    (hH : hilbertSamuelAt (vanishingIdeal (n := n+1) U) a = H)
    (hAtlas : HasExactCoveredNativeAtlas U E H S
      (⟨univ,E,vanishingIdeal (n := n+1) U,q⟩ : MarkedIdeal (n+1) A)) :
    IsMaximalOrderAlong univ (vanishingIdeal (n := n+1) U) q := by
  obtain ⟨ι,K,_,_,hCover⟩ := hAtlas
  intro x hx
  have hxCos : x ∈ (⟨univ,E,vanishingIdeal (n := n+1) U,q⟩ : MarkedIdeal (n+1) A).cosupp :=
    cosupport_anti (Nat.le_succ q) hx
  obtain ⟨i,hi⟩ := hCover x hxCos
  let y : K.openSet i := ⟨x,hi⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hUpper,_⟩ := K.native i
  have hBound : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) U) x ℓ ≤ H ℓ := by
    rw [← funext (hilbertSamuelAt_vanishing_actual_open_any (K.openSet i) U y)]
    exact hUpper y
  have hOrder : (↑(q+1) : ℕ∞) ≤ order (n+1) univ (vanishingIdeal (n := n+1) U) x :=
    (le_order_iff (𝔞 := vanishingIdeal (n := n+1) U) (fun _ hg => hg.1)).2 hx.2
  have hLt : order (n+1) univ (vanishingIdeal (n := n+1) U) a <
      order (n+1) univ (vanishingIdeal (n := n+1) U) x := by
    rw [ha]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self q) hOrder
  have hHS := (principal_profile_lt_iff_order_lt _ _ hI hI a x).2 hLt
  rw [hH] at hHS
  exact (not_le_of_gt hHS) (Pi.toLex_monotone hBound)

/-- Strictly descending actual principal labels force strictly descending
marks whenever the marks have been identified at the two label anchors. -/
theorem marks_lt_of_principal_labels_lt
    (U : Set A) (V : Set Z) (a : A) (b : Z) {q r : ℕ} {H K : ℕ → ℕ}
    (hU : (vanishingIdeal (n := n+1) U).IsInvertible)
    (hV : (vanishingIdeal (n := n+1) V).IsInvertible)
    (ha : order (n+1) univ (vanishingIdeal (n := n+1) U) a = q)
    (hb : order (n+1) univ (vanishingIdeal (n := n+1) V) b = r)
    (hH : hilbertSamuelAt (vanishingIdeal (n := n+1) U) a = H)
    (hK : hilbertSamuelAt (vanishingIdeal (n := n+1) V) b = K)
    (hDrop : toLex K < toLex H) :
    r < q := by
  have h := (principal_profile_lt_iff_order_lt _ _ hV hU b a).1
    (by rwa [hK,hH])
  rw [hb,ha] at h
  exact_mod_cast h


/-- An actual smaller principal label supplies both numerical guards for
continuing on the literal physical prefix. The new mark is identified at
its anchor, and the next cap follows from the intervening atlas. -/
theorem advance_of_smaller_principal_label
    (hM : IsInvDomain (n+1) M) (hMN : M.N = univ) (hMd : M.d = 1)
    (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hP : PrincipalPrefixState M W P cap)
    {B : CMfd.{0} (n+1)} (V : Set B) (b : B)
    (hV : (vanishingIdeal (n := n+1) V).IsInvertible)
    (hb : order (n+1) univ (vanishingIdeal (n := n+1) V) b = cap)
    {H : ℕ → ℕ} {q : ℕ} (hq : 2 ≤ q) (a : A) (S : BlowupTower A Z) :
    let U := strictTransform (n+1) P.proj W
    let E := (geoTransformAlong M P).E
    let F : MarkedIdeal (n+1) A := ⟨univ,E,vanishingIdeal (n := n+1) U,q⟩
    order (n+1) univ F.ideal a = q →
    hilbertSamuelAt F.ideal a = H →
    toLex H < toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) V) b) →
    ActualNativePhase U E H S →
    HasExactCoveredNativeAtlas U E H S F →
    PrincipalPrefixState M W (P.append S) q := by
  dsimp only
  intro ha hH hDrop hPhase hAtlas
  let U := strictTransform (n+1) P.proj W
  have hqcap := marks_lt_of_principal_labels_lt V U b a hV hP.invertible hb ha rfl hH hDrop
  have hCap := principal_order_cap_of_exact_covered_native_atlas
    U (geoTransformAlong M P).E H S q a hP.invertible ha hH hAtlas
  exact hP.advance hM hMN hMd hW hq hqcap H S hPhase hCap hAtlas

end
end Hironaka.HironakaG8PrincipalEpochLabels

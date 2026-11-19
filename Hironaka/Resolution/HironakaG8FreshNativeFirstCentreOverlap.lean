import Hironaka.Resolution.HironakaG8FreshPostCutNativeFamily
import Hironaka.Resolution.HironakaG8NativeNumericalOverlap
import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8FreshNativeFirstCentreOverlap
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG8NativeNumericalOverlap
  HironakaActualPowerBoundaryExponents CanonicalCentres HironakaG1OriginalInvariantClassFunctorial
  HironakaActualVanishingIntrinsicHSTransport

/-- At a point with the same active value, centre membership differs exactly
when the other chart contains an active point of strictly higher value. -/
theorem mem_maxLocus_iff_no_higher {A B Λ : Type*} [LinearOrder Λ]
    {t : Set B} {f : A → Λ} {g : B → Λ} {x : A} {y : B}
    (hy : y ∈ t) (hVal : f x = g y) :
    y ∈ maxLocus g t ↔ ¬ ∃ z ∈ t, f x < g z := by
  constructor
  · intro hm ⟨z,hz,hlt⟩
    exact (not_lt_of_ge (hm.2 z hz)) (hVal ▸ hlt)
  · intro hnone
    exact ⟨hy, fun z hz => le_of_not_gt (fun hlt => hnone ⟨z,hz,hVal.symm ▸ hlt⟩)⟩

private theorem mem_maxLocus_iff_key {D Λ : Type*} [LinearOrder Λ]
    (v : D → Λ) (a : Set D) (z : D) {m : Λ} (h : IsGreatest (v '' a) m) :
    z ∈ maxLocus v a ↔ z ∈ a ∧ v z = m := by
  constructor
  · intro hz
    obtain ⟨u,hu,rfl⟩ := h.1
    exact ⟨hz.1,le_antisymm (h.2 (mem_image_of_mem v hz.1)) (hz.2 u hu)⟩
  · rintro ⟨hz,hzv⟩
    exact ⟨hz,fun u hu => hzv ▸ h.2 (mem_image_of_mem v hu)⟩

/-- Equality of the attained maximum key identifies both maxima on any point
where active membership and the active value agree. -/
theorem mem_maxLocus_iff_of_common_key {A B Λ : Type*} [LinearOrder Λ]
    {s : Set A} {t : Set B} {f : A → Λ} {g : B → Λ} {x : A} {y : B} {m : Λ}
    (hCos : x ∈ s ↔ y ∈ t) (hVal : x ∈ s → f x = g y)
    (hf : IsGreatest (f '' s) m) (hg : IsGreatest (g '' t) m) :
    x ∈ maxLocus f s ↔ y ∈ maxLocus g t := by
  rw [mem_maxLocus_iff_key f s x hf,mem_maxLocus_iff_key g t y hg]
  exact ⟨fun ⟨hx,hm⟩ => ⟨hCos.mp hx,(hVal hx).symm.trans hm⟩,
    fun ⟨hy,hm⟩ => ⟨hCos.mpr hy,(hVal (hCos.mpr hy)).trans hm⟩⟩

/-- First original invariant values of powered fresh native windows agree on
the actual overlap whenever their marks are synchronized and the touching
boundary germs are noncontaining. -/
theorem fresh_native_first_values_agree
    {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (U V : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U))
    (Q : MarkedIdeal n (CMfd.of (n := n) V)) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (W : Set X) (H : ℕ → ℕ)
    (hSP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hSQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (E : List (Set X)) (hEP : P.E = E.map ((Subtype.val : U → X) ⁻¹' ·))
    (hEQ : Q.E = E.map ((Subtype.val : V → X) ⁻¹' ·))
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) (hd : (powerMarked P e).d = (powerMarked Q f).d)
    (hNot : ∀ D ∈ E, ∀ y : U, y ∈ P.cosupp → y.val ∈ D →
      ¬ ∀ᶠ z in 𝓝 y.val, z ∈ D → z ∈ W)
    {z : X} (hzU : z ∈ U) (hzV : z ∈ V) :
    let Pe := powerMarked P e
    let Qf := powerMarked Q f
    ((⟨z,hzU⟩ : U) ∈ Pe.cosupp ↔ (⟨z,hzV⟩ : V) ∈ Qf.cosupp) ∧
    ((⟨z,hzU⟩ : U) ∈ Pe.cosupp →
      (invFamily hn k).inv Pe .refl ⟨z,hzU⟩ = (invFamily hn k).inv Qf .refl ⟨z,hzV⟩) := by
  intro Pe Qf
  let B : BMInvariant n (fun {Y} A A' => LocWPEquiv (X := Y) A A') k _ :=
    ⟨invFamily hn k,classFunctorialFor_invFamily hn k⟩
  have hzUR : z ∈ openPreimage (.refl : BlowupTower X X) U := hzU
  have hzVR : z ∈ openPreimage (.refl : BlowupTower X X) V := hzV
  have hVals := native_window_values_agree_along hn B U V P Q hP hQ W H hSP hSQ E hEP hEQ
    e f he hf hd hNot (.refl : BlowupTower X X) (by trivial) (by trivial) hzUR hzVR
  have hCos : (⟨z,hzU⟩ : U) ∈ Pe.cosupp ↔ (⟨z,hzV⟩ : V) ∈ Qf.cosupp := by
    rw [powerMarked_cosupp P hP he,
      powerMarked_cosupp Q hQ hf,hSP.cosupp_eq,hSQ.cosupp_eq]
    simp only [Set.mem_ofPred_eq,hilbertSamuelAt_vanishing_actual_open_any]
  exact ⟨hCos,fun hz => (hVals hz).2⟩

/-- Actual nonempty first centres of synchronized native windows agree on
their overlap once their respective full cosupports attain one common key. -/
theorem fresh_native_first_centres_agree_of_common_key
    {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (U V : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U))
    (Q : MarkedIdeal n (CMfd.of (n := n) V)) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (W : Set X) (H : ℕ → ℕ)
    (hSP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hSQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (E : List (Set X)) (hEP : P.E = E.map ((Subtype.val : U → X) ⁻¹' ·))
    (hEQ : Q.E = E.map ((Subtype.val : V → X) ⁻¹' ·))
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) (hd : (powerMarked P e).d = (powerMarked Q f).d)
    (hNot : ∀ D ∈ E, ∀ y : U, y ∈ P.cosupp → y.val ∈ D →
      ¬ ∀ᶠ z in 𝓝 y.val, z ∈ D → z ∈ W)
    {YU YV : CMfd.{0} n} (CU : Set U) (CV : Set V)
    (πU : YU → U) (πV : YV → V)
    (hπU : IsBlowupAlong n CU πU) (hπV : IsBlowupAlong n CV πV)
    (hCU : CU.Nonempty) (hCV : CV.Nonempty)
    (hCanU : IsCanonical (powerMarked P e) ((invFamily hn k).inv (powerMarked P e))
      (.step .refl CU πU hπU))
    (hCanV : IsCanonical (powerMarked Q f) ((invFamily hn k).inv (powerMarked Q f))
      (.step .refl CV πV hπV))
    (m : ValTy k)
    (hKeyU : IsGreatest (((invFamily hn k).inv (powerMarked P e) .refl) '' (powerMarked P e).cosupp) m)
    (hKeyV : IsGreatest (((invFamily hn k).inv (powerMarked Q f) .refl) '' (powerMarked Q f).cosupp) m)
    {z : X} (hzU : z ∈ U) (hzV : z ∈ V) :
    (⟨z,hzU⟩ : U) ∈ CU ↔ (⟨z,hzV⟩ : V) ∈ CV := by
  obtain ⟨hCos,hVal⟩ := fresh_native_first_values_agree hn U V P Q hP hQ W H hSP hSQ
    E hEP hEQ e f he hf hd hNot hzU hzV
  rcases hCanU.2 with h0 | hMaxU
  · exact False.elim (hCU.ne_empty h0)
  rcases hCanV.2 with h0 | hMaxV
  · exact False.elim (hCV.ne_empty h0)
  rw [hMaxU,hMaxV]
  exact mem_maxLocus_iff_of_common_key hCos hVal hKeyU hKeyV

/-- Starting at a first maximizer in one window, failure of synchronization
is equivalent to a strictly greater active value outside that window. -/
theorem fresh_native_first_maximum_iff_no_higher_off_overlap
    {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (U V : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U))
    (Q : MarkedIdeal n (CMfd.of (n := n) V)) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (W : Set X) (H : ℕ → ℕ)
    (hSP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hSQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (E : List (Set X)) (hEP : P.E = E.map ((Subtype.val : U → X) ⁻¹' ·))
    (hEQ : Q.E = E.map ((Subtype.val : V → X) ⁻¹' ·))
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) (hd : (powerMarked P e).d = (powerMarked Q f).d)
    (hNot : ∀ D ∈ E, ∀ y : U, y ∈ P.cosupp → y.val ∈ D →
      ¬ ∀ᶠ z in 𝓝 y.val, z ∈ D → z ∈ W)
    {z : X} (hzU : z ∈ U) (hzV : z ∈ V)
    (hMax : (⟨z,hzU⟩ : U) ∈
      maxLocus ((invFamily hn k).inv (powerMarked P e) .refl) (powerMarked P e).cosupp) :
    (⟨z,hzV⟩ : V) ∈ maxLocus ((invFamily hn k).inv (powerMarked Q f) .refl)
      (powerMarked Q f).cosupp ↔
    ¬ ∃ y : V, y ∈ (powerMarked Q f).cosupp ∧ y.val ∉ U ∧
      (invFamily hn k).inv (powerMarked P e) .refl ⟨z,hzU⟩ <
        (invFamily hn k).inv (powerMarked Q f) .refl y := by
  obtain ⟨hCos,hVal⟩ := fresh_native_first_values_agree hn U V P Q hP hQ W H hSP hSQ
    E hEP hEQ e f he hf hd hNot hzU hzV
  rw [mem_maxLocus_iff_no_higher (hCos.mp hMax.1) (hVal hMax.1)]
  constructor
  · intro h ⟨y,hy,_,hlt⟩
    exact h ⟨y,hy,hlt⟩
  · intro h ⟨y,hy,hlt⟩
    by_cases hyU : y.val ∈ U
    · obtain ⟨hc,hv⟩ := fresh_native_first_values_agree hn U V P Q hP hQ W H hSP hSQ
        E hEP hEQ e f he hf hd hNot hyU y.property
      exact (not_lt_of_ge ((hv (hc.mpr hy)) ▸ hMax.2 ⟨y.val,hyU⟩ (hc.mpr hy))) hlt
    · exact h ⟨y,hy,hyU,hlt⟩

/-- Compare the actual raw first centres of two fresh windows. The common
numerical key is measured in their synchronized whole-power records. -/
theorem fresh_native_raw_first_centres_agree_of_common_key
    {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (U V : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U))
    (Q : MarkedIdeal n (CMfd.of (n := n) V)) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (W : Set X) (H : ℕ → ℕ)
    (hSP : NativeHSState P ((Subtype.val : U → X) ⁻¹' W) H)
    (hSQ : NativeHSState Q ((Subtype.val : V → X) ⁻¹' W) H)
    (E : List (Set X)) (hEP : P.E = E.map ((Subtype.val : U → X) ⁻¹' ·))
    (hEQ : Q.E = E.map ((Subtype.val : V → X) ⁻¹' ·))
    (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) (hd : (powerMarked P e).d = (powerMarked Q f).d)
    (hNot : ∀ D ∈ E, ∀ y : U, y ∈ P.cosupp → y.val ∈ D →
      ¬ ∀ᶠ z in 𝓝 y.val, z ∈ D → z ∈ W)
    {YU YV : CMfd.{0} n} (CU : Set U) (CV : Set V)
    (πU : YU → U) (πV : YV → V)
    (hπU : IsBlowupAlong n CU πU) (hπV : IsBlowupAlong n CV πV)
    (hCU : CU.Nonempty) (hCV : CV.Nonempty)
    (hCanU : IsCanonical P ((invFamily hn k).inv P)
      (.step .refl CU πU hπU))
    (hCanV : IsCanonical Q ((invFamily hn k).inv Q)
      (.step .refl CV πV hπV))
    (m : ValTy k)
    (hKeyU : IsGreatest (((invFamily hn k).inv (powerMarked P e) .refl) '' (powerMarked P e).cosupp) m)
    (hKeyV : IsGreatest (((invFamily hn k).inv (powerMarked Q f) .refl) '' (powerMarked Q f).cosupp) m)
    {z : X} (hzU : z ∈ U) (hzV : z ∈ V) :
    (⟨z,hzU⟩ : U) ∈ CU ↔ (⟨z,hzV⟩ : V) ∈ CV := by
  have hp := (HironakaG1OriginalUnequalMarkCanonical.invFamily_isCanonical_power_iff
    hn P hP e he (.step .refl CU πU hπU)).mp hCanU
  have hq := (HironakaG1OriginalUnequalMarkCanonical.invFamily_isCanonical_power_iff
    hn Q hQ f hf (.step .refl CV πV hπV)).mp hCanV
  exact fresh_native_first_centres_agree_of_common_key hn U V P Q hP hQ W H hSP hSQ
    E hEP hEQ e f he hf hd hNot CU CV πU πV hπU hπV hCU hCV hp hq m hKeyU hKeyV hzU hzV

end
end Hironaka.HironakaG8FreshNativeFirstCentreOverlap

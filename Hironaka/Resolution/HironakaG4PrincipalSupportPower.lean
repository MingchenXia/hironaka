import Hironaka.Analytic.HolomorphicCoordinateFactorization
import Hironaka.Resolution.HironakaG4MonomialChartCosupport
import Hironaka.Resolution.HironakaG4OneBornCartierCleanup

set_option autoImplicit false

/-! The whole actual principal old trace supported in one transverse born
member is a genuine local unit times its power on the actual carrier.
Blueprint: `hironaka-g4-principal-support-power.tex`. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4PrincipalSupportPower

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings SimultaneousNormalCrossings BlowupSNCTransform
  BlowupFlatCoordinates GiraudAlong MonomialPartAlong MemberPullback
  HolomorphicGermReducednessBridge HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProduct HironakaG4MonomialChartCosupport
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  GermIdealOrder IdealWeightPowers DivisorExponentAlong OrderTaylor MonomialCase

variable {n d : ℕ} {X : CMfd.{u} n}

private theorem coordinate_power_of_zero_support {m : ℕ} (j : Fin m)
    {G : ComplexModel m → ℂ}
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z)
    (hzero : ∀ᶠ z in 𝓝 0, G z = 0 → z j = 0) :
    ∃ (a : ℕ) (U : ComplexModel m → ℂ),
      (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ U z) ∧ U 0 ≠ 0 ∧
        G =ᶠ[𝓝 0] fun z => U z * (z j) ^ a := by
  let p := HolGerm.mk (fun z : ComplexModel m => z j) (eventually_differentiableAt_coordinate j)
  let I : Ideal (HolGerm (ComplexModel m)) := Ideal.span {HolGerm.mk G hG}
  have hvan : p ∈ AnalyticGermDecomposition.vanishingIdeal {z | ∀ _ : Fin 1, G z = 0} := by
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    filter_upwards [hzero] with z hz hzg
    exact hz (hzg 0)
  have hrad : p ∈ I.radical :=
    RueckertNullstellensatz.vanishingIdeal_le_radical I (fun _ : Fin 1 => G)
      (fun _ => ⟨hG, Ideal.subset_span (Set.mem_singleton _)⟩) hvan
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hrad
  have hdiv : HolGerm.mk G hG ∣ p ^ N := Ideal.mem_span_singleton.mp hN
  obtain ⟨a, _ha, hassoc⟩ :=
    (dvd_prime_pow (HolomorphicCoordinatePrime.prime_coordinate_germ j) N).mp hdiv
  obtain ⟨v, hv⟩ := hassoc.symm
  obtain ⟨U, hU, hrep⟩ := HolGerm.exists_eq_mk (v : HolGerm (ComplexModel m))
  have hU0 : U 0 ≠ 0 := by
    have hval := (HolGerm.isUnit_iff_eval_ne_zero _).mp v.isUnit
    rw [hrep, HolGerm.eval_mk] at hval
    exact hval
  let M : ComplexModel m → ℂ := fun z => (z j) ^ a
  have hM : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ M z :=
    eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) a
  have hmon : HolGerm.mk M hM = p ^ a :=
    HolGerm.mk_pow (fun z : ComplexModel m => z j) (eventually_differentiableAt_coordinate j) a
  refine ⟨a, U, hU, hU0, ?_⟩
  apply (HolGerm.mk_eq_mk_iff (hf := hG)
    (hg := eventually_differentiableAt_mul hU hM)).mp
  calc
    HolGerm.mk G hG = p ^ a * (v : HolGerm (ComplexModel m)) := hv.symm
    _ = HolGerm.mk U hU * HolGerm.mk M hM := by rw [hrep, ← hmon, mul_comm]
    _ = HolGerm.mk (fun z => U z * M z) (eventually_differentiableAt_mul hU hM) :=
      (HolGerm.mk_mul U M hU hM).symm

private theorem relative_power_in_coordinates (hn : 0 < n) {N F : Set X}
    (hF : IsSNCDivisor n [F]) (hT : IsTransverse n N [F])
    {x : X} (hx : x ∈ N ∩ F) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ N → f y = 0 → y ∈ F) :
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (j : Fin n) (a : ℕ) (u : X → ℂ),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧ j.val < k ∧
      (∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)) ∧
      (∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ F ↔ flatCoord Φ j y = 0)) ∧
      HolomorphicAt n u x ∧ u x ≠ 0 ∧
      ∀ᶠ y in 𝓝 x, y ∈ N → f y = u y * flatCoord Φ j y ^ a := by
  obtain ⟨_kC, k, Φ, s, hsrc, hsk, _hinj, hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn subset_rfl hF hT hT.hasNormalCrossings hx.1
  let j := s (0 : Fin [F].length)
  have hj : j.val < k := hsk (0 : Fin [F].length) hx.2
  have hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k) :=
    fun hy hyΦ => (hflat hy hyΦ).2.1
  have hFflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source → (y ∈ F ↔ flatCoord Φ j y = 0) :=
    fun hy hyΦ => (hflat hy hyΦ).2.2 (0 : Fin [F].length) hx.2
  have hxD := mem_flatDomain_self Φ
  let r := flatRetract Φ k
  have hr : IsLocalRetraction n N r x := isLocalRetraction_flatRetract hsrc hNflat hxD hx.1
  let q := flatMap Φ x
  have hqj : q j = 0 := (hFflat hxD.1 hxD.2).mp hx.2
  have hqT : q ∈ Φ.target := Φ.mapsTo_toFun hxD.2
  let T : ComplexModel n → X := fun z => flatInv Φ (z + q)
  have hshift : Tendsto (fun z : ComplexModel n => z + q) (𝓝 0) (𝓝 q) := by
    simpa using ((continuousAt_id : ContinuousAt (fun z : ComplexModel n => z) 0).add_const q).tendsto
  have hTend : Tendsto T (𝓝 0) (𝓝 x) := (tendsto_flatInverse Φ hxD).comp hshift
  let G : ComplexModel n → ℂ := fun z => f (r (T z))
  have hfr : HolomorphicAt n (f ∘ r) x := hr.holomorphicAt_comp hf
  have hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z := by
    filter_upwards [hshift.eventually (Φ.isOpen_target.mem_nhds hqT),
      hTend.eventually hfr.eventually] with z hz hgf
    have hinv : Φ.invFun (z+q) ∈ (chartAt (ComplexModel n) x).target := hsrc (Φ.mapsTo_invFun hz)
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
        (fun w => (f ∘ r) ((chartAt (ComplexModel n) x).symm w)) (Φ.invFun (z+q)) :=
      hgf.mdifferentiableAt.comp (Φ.invFun (z+q)) (mdifferentiableAt_chart_symm hinv)
    have h2 : DifferentiableAt ℂ (fun w => (f ∘ r) (flatInv Φ w)) (z+q) :=
      (mdifferentiableAt_iff_differentiableAt.mp h1).comp (z+q)
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))
    have hadd : DifferentiableAt ℂ (fun w : ComplexModel n => w+q) z :=
      differentiableAt_id.add_const q
    have h3 := h2.comp z hadd
    exact h3
  have hpres := eventually_flatMap_flatRetract hsrc hNflat hxD hx.1 hj
  have hGzero : ∀ᶠ z in 𝓝 0, G z = 0 → z j = 0 := by
    filter_upwards [hshift.eventually (Φ.isOpen_target.mem_nhds hqT),
      hTend.eventually hr.mem, hTend.eventually (hr.tendsto.eventually hzero),
      hTend.eventually hpres] with z hz hzN hzZero hzPres hGz
    have hrF : r (T z) ∈ F := hzZero hzN hGz
    have hc : flatMap Φ (r (T z)) j = 0 := (hFflat hzPres.1.1 hzPres.1.2).mp hrF
    have hTc : flatMap Φ (T z) = z+q := flatMap_flatInv hz hsrc
    rw [hzPres.2, hTc] at hc
    change z j + q j = 0 at hc
    simpa only [hqj, add_zero] using hc
  obtain ⟨a, U, hU, hU0, hEq⟩ := coordinate_power_of_zero_support j hG hGzero
  let u : X → ℂ := fun y => U (flatMap Φ y - q)
  have hminus : Tendsto (fun w : ComplexModel n => w-q) (𝓝 q) (𝓝 0) := by
    have hc : ContinuousAt (fun w : ComplexModel n => w-q) q :=
      continuousAt_id.sub continuousAt_const
    simpa using hc.tendsto
  have hUshift : ∀ᶠ w in 𝓝 q, DifferentiableAt ℂ (fun v => U (v-q)) w := by
    filter_upwards [hminus.eventually hU] with w hw
    exact hw.comp w (differentiableAt_id.sub_const q)
  have hu : HolomorphicAt n u x := holomorphicAt_comp_flat Φ hxD hUshift
  have hu0 : u x ≠ 0 := by simpa only [u, q, sub_self] using hU0
  have hMap : Tendsto (fun y => flatMap Φ y-q) (𝓝 x) (𝓝 0) := by
    have hc : ContinuousAt (fun y => flatMap Φ y-q) x :=
      (MonomialPartAlong.mdifferentiableAt_flatMap hxD).continuousAt.sub continuousAt_const
    simpa only [q, sub_self] using hc.tendsto
  refine ⟨k, Φ, j, a, u, hsrc, hj, hNflat, hFflat, hu, hu0, ?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD, hMap.eventually hEq,
    hr.eventually_eq_comp f] with y hyD heq hry hyN
  have hGy : G (flatMap Φ y-q) = f (r y) := by
    dsimp only [G, T]
    rw [sub_add_cancel, flatInv_flatMap hyD]
  have hjy : (flatMap Φ y-q) j = flatCoord Φ j y := by
    change flatMap Φ y j - q j = flatCoord Φ j y
    rw [hqj, sub_zero]
    rfl
  rw [hGy, hjy] at heq
  exact (hry hyN).trans heq

/-- The actual whole F ideal supplies its true equation, and genuine support
containment on the actual N supplies the unit and power internally. -/
theorem exists_actual_relative_born_power (hn : 0 < n) {N F : Set X}
    (hF : IsSNCDivisor n [F]) (hT : IsTransverse n N [F])
    {x : X} (hx : x ∈ N ∩ F) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ N → f y = 0 → y ∈ F) :
    ∃ (a : ℕ) (g u : X → ℂ), HolomorphicAt n g x ∧ HolomorphicAt n u x ∧ u x ≠ 0 ∧
      (∀ v, (vanishingIdeal (n := n) F).mem x v ↔ IsInSpanAt (n := n) (· = g) x v) ∧
      ∀ᶠ y in 𝓝 x, y ∈ N → f y = u y * g y ^ a := by
  obtain ⟨_k, Φ, j, a, u, _hsrc, _hj, _hNflat, hFflat, hu, hu0, heq⟩ :=
    relative_power_in_coordinates hn hF hT hx f hf hzero
  exact ⟨a, flatCoord Φ j, u, holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ), hu, hu0,
    vanishingIdeal_mem_iff_flatCoord Φ hFflat (mem_flatDomain_self Φ), heq⟩

private theorem relative_span_of_unit {N : Set X} {x : X} {f p u v : X → ℂ}
    (hu : HolomorphicAt n u x) (hu0 : u x ≠ 0)
    (heq : ∀ᶠ y in 𝓝 x, y ∈ N → f y = u y * p y) :
    IsInSpanOnAt (n := n) N (· = f) x v ↔ IsInSpanOnAt (n := n) N (· = p) x v := by
  constructor
  · intro hv
    obtain ⟨c, hc, hcv⟩ := isInSpanOnAt_eq_iff.mp hv
    refine isInSpanOnAt_eq_iff.mpr ⟨c*u, hc.mul hu, ?_⟩
    filter_upwards [heq, hcv] with y hy he hyN
    change v y = (c y*u y)*p y
    rw [he hyN, hy hyN]
    ring
  · intro hv
    obtain ⟨c, hc, hcv⟩ := isInSpanOnAt_eq_iff.mp hv
    refine isInSpanOnAt_eq_iff.mpr ⟨c*(fun y => (u y)⁻¹),
      hc.mul (BlowupFlatCoordinates.HolomorphicAt.inv hu hu0), ?_⟩
    filter_upwards [heq, hcv, hu.continuousAt.eventually (isOpen_ne.mem_nhds hu0)] with y hy he hy0 hyN
    change v y = (c y*(u y)⁻¹)*f y
    rw [he hyN, hy hyN]
    field_simp

private theorem vanishes_coordinate_power_iff {N : Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (k : ℕ)
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hNflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
      (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n k))
    {y : X} (hyD : y ∈ flatDomain Φ) (hyN : y ∈ N) (j : Fin n) (hj : j.val < k)
    (hy0 : flatCoord Φ j y = 0) (a q : ℕ) :
    VanishesToOrderOn n N y q (fun z => flatCoord Φ j z ^ a) ↔ q ≤ a := by
  let p : X → ℂ := fun z => flatCoord Φ j z ^ a
  have hpow : (idealPow (pointIdeal n y) a).mem y p ∧
      ¬ (idealPow (pointIdeal n y) (a+1)).mem y p := by
    simpa using MonomialCase.prod_flatCoord_pow_order Φ (fun _ : Unit => j)
      (fun _ => a) hyD {()} (fun _ _ => hy0)
  have hr : IsLocalRetraction n N (flatRetract Φ k) y :=
    isLocalRetraction_flatRetract hsrc hNflat hyD hyN
  have hpr : p ∘ flatRetract Φ k =ᶠ[𝓝 y] p := by
    filter_upwards [eventually_flatMap_flatRetract hsrc hNflat hyD hyN hj] with z hz
    exact congrArg (· ^ a) hz.2
  constructor
  · intro hq
    by_contra hlt
    have hpq := mem_idealPow_congr (hr.vanishesToOrderOn_iff.mp hq) hpr
    exact hpow.2 (idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg)
      (by omega : a+1 ≤ q) y p hpq)
  · intro hq
    exact ⟨p, idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) hq y p hpow.1,
      Eventually.of_forall fun _ _ => rfl⟩

private theorem ordinaryTraceOrder_eq_of_cosupport {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) (y : X) (a : ℕ)
    (hcos : ∀ q, y ∈ cosupport n N I q ↔ q ≤ a) : ordinaryTraceOrder N I y = a := by
  have hlow := (hcos a).mpr le_rfl
  have hhigh : y ∉ cosupport n N I (a+1) := fun h => Nat.not_succ_le_self a ((hcos _).mp h)
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport N I hI] at hlow hhigh
  have hu := NonmonomialOrderLocal.nmOrd_le_of_notMem hhigh
  have hl : a ≤ NonmonomialOrderLocal.nmOrd (ordinaryTraceMarked N I) y := by
    cases a with
    | zero => exact Nat.zero_le _
    | succ b => exact NonmonomialOrderLocal.succ_le_nmOrd_of_mem ⟨b+1, hhigh⟩ hlow
  exact hu.antisymm hl

/-- Support in one actual transverse member forces the ENTIRE normalized old
ideal to be its positive coordinate power, with every nearby whole order computed. -/
theorem actual_supported_old_trace_local_model (hn : 0 < n) {N H F : Set X}
    (_hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hF : IsSNCDivisor n [F]) (hT : IsTransverse n N [F]) (hsub : N ∩ H ⊆ F)
    {x : X} (hx : x ∈ N ∩ H) :
    ∃ (a : ℕ) (g : X → ℂ), 0 < a ∧ HolomorphicAt n g x ∧
      (∀ v, (vanishingIdeal (n := n) F).mem x v ↔ IsInSpanAt (n := n) (· = g) x v) ∧
      ∀ᶠ y in 𝓝 x,
        (∀ v, (restrictOn n N (vanishingIdeal (n := n) H)).mem y v ↔
          HolomorphicAt n v y ∧ IsInSpanOnAt (n := n) N (· = fun z => g z ^ a) y v) ∧
        (y ∈ N ∩ F → ordinaryTraceOrder N (vanishingIdeal (n := n) H) y = a) ∧
        (y ∈ N ∩ H ↔ y ∈ N ∩ F) := by
  obtain ⟨Ψ, σ, _hsrcH, _h0H, _hinjH, hA⟩ := exists_snc_chart hn hH x
  let f : X → ℂ := flatCoord Ψ (σ (0 : Fin [H].length))
  have hHflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ψ.source → (y ∈ H ↔ f y = 0) :=
    fun hy hyΨ => hA (0 : Fin [H].length) hx.2 hy hyΨ
  have hxDH := mem_flatDomain_self Ψ
  have hf : HolomorphicAt n f x := holomorphicAt_flatCoord Ψ _ hxDH
  have hzero : ∀ᶠ y in 𝓝 x, y ∈ N → f y = 0 → y ∈ F := by
    filter_upwards [(isOpen_flatDomain Ψ).mem_nhds hxDH] with y hy hyN hyf
    exact hsub ⟨hyN, (hHflat hy.1 hy.2).mpr hyf⟩
  obtain ⟨k, Φ, j, a, u, hsrc, hj, hNflat, hFflat, hu, hu0, heq⟩ :=
    relative_power_in_coordinates hn hF hT ⟨hx.1, hsub hx⟩ f hf hzero
  have hxD := mem_flatDomain_self Φ
  have ha : 0 < a := by
    by_contra hna
    have haz : a = 0 := by omega
    have he := heq.self_of_nhds hx.1
    rw [haz, pow_zero, mul_one] at he
    exact hu0 (he.symm.trans ((hHflat hxDH.1 hxDH.2).mp hx.2))
  have hcH : (vanishingIdeal (n := n) H).IsCoherent := by
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length))
  refine ⟨a, flatCoord Φ j, ha, holomorphicAt_flatCoord Φ j hxD,
    vanishingIdeal_mem_iff_flatCoord Φ hFflat hxD, ?_⟩
  filter_upwards [(isOpen_flatDomain Ψ).mem_nhds hxDH, (isOpen_flatDomain Φ).mem_nhds hxD,
    hu.eventually, hu.continuousAt.eventually (isOpen_ne.mem_nhds hu0), heq.eventually_nhds, heq]
    with y hyH hyF huy huy0 heqG heqY
  have hfy : HolomorphicAt n f y := holomorphicAt_flatCoord Ψ _ hyH
  have hgenH := vanishingIdeal_mem_iff_flatCoord Ψ hHflat hyH
  have hdict (v : X → ℂ) : (restrictOn n N (vanishingIdeal (n := n) H)).mem y v ↔
      HolomorphicAt n v y ∧ IsInSpanOnAt (n := n) N (· = fun z => flatCoord Φ j z ^ a) y v := by
    change (HolomorphicAt n v y ∧ IsInSpanOnAt (n := n) N
      ((vanishingIdeal (n := n) H).mem y) y v) ↔ _
    exact and_congr_right fun _ => (restricted_span_iff_principal hfy hgenH v).trans
      (relative_span_of_unit huy huy0 heqG)
  refine ⟨hdict, ?_, ?_⟩
  · intro hyNF
    apply ordinaryTraceOrder_eq_of_cosupport hcH y a
    intro q
    have hnorm : y ∈ cosupport n N (restrictOn n N (vanishingIdeal (n := n) H)) q ↔
        y ∈ cosupport n N (vanishingIdeal (n := n) H) q :=
      ⟨fun h => MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe
          (restrictLe_self_restrictOn hcH) q h,
        fun h => MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe restrictLe_restrictOn q h⟩
    exact hnorm.symm.trans ((HironakaSharpActualRelativeProductOrder.cosupport_relative_principal_iff_vanishes
      hyNF.1 (CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ j hyF) a) hdict q).trans
        (vanishes_coordinate_power_iff Φ k hsrc hNflat hyF hyNF.1 j hj
          ((hFflat hyF.1 hyF.2).mp hyNF.2) a q))
  · constructor
    · intro hyNH
      exact ⟨hyNH.1, hsub hyNH⟩
    · rintro ⟨hyN, hyInF⟩
      have hgy : flatCoord Φ j y = 0 := (hFflat hyF.1 hyF.2).mp hyInF
      refine ⟨hyN, (hHflat hyH.1 hyH.2).mpr ?_⟩
      rw [heqY hyN, hgy, zero_pow (Nat.ne_of_gt ha), mul_zero]

/-- The whole supported old trace itself is a genuine closed smooth Cartier
centre. It can occupy a proper clopen part of the selected born trace. -/
theorem actual_supported_old_trace_regular (hn : 0 < n) {N H F : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hF : IsSNCDivisor n [F]) (hT : IsTransverse n N [F]) (hsub : N ∩ H ⊆ F)
    (hrN : ∀ x ∈ N, RegularAtDim (n := n) N x (d+1)) :
    IsClosedSubmanifold n (N ∩ H) ∧
      (∀ x ∈ N ∩ H, RegularAtDim (n := n) (N ∩ H) x d) ∧
      ∀ x ∈ N ∩ H, ∀ᶠ y in 𝓝 x, y ∈ N ∩ H ↔ y ∈ N ∩ F := by
  have hgerm : ∀ x ∈ N ∩ H, ∀ᶠ y in 𝓝 x, y ∈ N ∩ H ↔ y ∈ N ∩ F := by
    intro x hx
    obtain ⟨_a, _g, _ha, _hg, _hgen, hm⟩ :=
      actual_supported_old_trace_local_model hn hN hH hF hT hsub hx
    exact hm.mono fun _ h => h.2.2
  let A := restrictOn n N (vanishingIdeal (n := n) F)
  obtain ⟨hcA, hnzA, hprA, horder⟩ :=
    HironakaSharpActualFirstAmbientStrictExponent.actual_normalized_transverse_member_geometry hn hN hF hT
  have hcF : (vanishingIdeal (n := n) F).IsCoherent :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hF (0 : Fin [F].length))
  have hzero : N ∩ A.zeroLocus = N ∩ F := by
    ext y
    apply and_congr_right
    intro hyN
    exact (HironakaSharpActualTraceIncidence.zeroLocus_restrictOn_iff hcF hyN).trans (by
      rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hF.1 F (by simp))])
  have hrC : ∀ x ∈ N ∩ H, RegularAtDim (n := n) (N ∩ H) x d := by
    intro x hx
    obtain ⟨f, hf, hgen⟩ := hprA x hx.1
    obtain ⟨_U, _u, _hxU, _hu, _hux, _hg, _hi, k, hNk, hCk⟩ :=
      HironakaSharpActualPrincipalOrderOneTrace.actual_orderOne_relative_reduced_trace
        hN hcA hnzA hx.1 f hf hgen (horder x ⟨hx.1, hsub hx⟩)
    have hk : k = d+1 := RegularPointDimension.eq_of_regularAtDim hNk (hrN x hx.1)
    rw [hzero, hk] at hCk
    have hrNF : RegularAtDim (n := n) (N ∩ F) x d := by
      simpa only [Nat.add_sub_cancel] using hCk
    exact CodimOneSupport.regularAtDim_of_eventually_mem_iff
      ((hgerm x hx).mono fun _ h => h.symm) hrNF
  exact ⟨⟨hN.1.inter (hH.1 H (by simp)), fun x hx => ⟨d, hrC x hx⟩⟩, hrC, hgerm⟩

/-- Compactness makes actual finite upper semicontinuity a finite natural bound
for the entire ordinary trace ideal, without a constancy inference. -/
theorem exists_bounded_ordinaryTraceOrder_on_isCompact (hn : 0 < n) {N K : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N, IsNonzeroAlongAt N I x) (hK : IsCompact K) (hKN : K ⊆ N) :
    ∃ A : ℕ, ∀ x ∈ K, ordinaryTraceOrder N I x ≤ A := by
  obtain ⟨t, _ht, hcover⟩ := hK.elim_nhds_subcover
    (fun x => {y | ordinaryTraceOrder N I y ≤ ordinaryTraceOrder N I x})
    (fun x hx => eventually_ordinaryTraceOrder_le hn hN hI hnz (hKN hx))
  refine ⟨t.sup (fun x => ordinaryTraceOrder N I x), ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (hcover hy)
  exact hyx.trans (Finset.le_sup hxt)

end

end Hironaka.HironakaG4PrincipalSupportPower

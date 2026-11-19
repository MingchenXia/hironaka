import Hironaka.Resolution.HironakaG8ExceptionalLogCentre

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Lifting logarithmic vector fields through a monomial blowup chart (G8 lane, run 0079, round 2; leaf G8-3H-C06)

Blueprint: `hironaka-g8-resume-log-lift-chart.tex`.

A `LogLiftChart` at `y` records the coordinate shape of a blowup `π` along a centre `C` at a point `y` of the strict
transform `N'` of a carrier `N`: flat coordinates `ψ` at `x = π y` and `ζ` at `y` with

* `N = {ψ_b = 0, b ∈ B}` and `N' = {ζ_b = 0, b ∈ B}`;
* a pivot `p ∉ B`, a set `Q ∌ p` of the other centre indices and constants `v` (`v_b = 0` for `b ∈ B`) with
  `ψ_l ∘ π = ζ_p (ζ_l + v_l)` for `l ∈ Q` and `ψ_l ∘ π = ζ_l + v_l` otherwise (the monomial chart, recentred at `y`);
* `π⁻¹ C = {ζ_p = 0}`;
* every member of the target boundary list `E'` either misses a neighbourhood of `y` or is `{ζ_m = 0}` with `v_m = 0`,
  where `m = p` or `{ψ_m = 0}` is a member of the source boundary list `E`.

No relation between `B` and `Q` is assumed, so the structure covers admissible centres (`C ⊆ N`, `B ⊆ Q`) and centres
transverse to `N` alike.

For EVERY holomorphic field `ξ` at `x` (chart `e`), `liftField e ξ` is the explicit field at `y` with

  `liftField(f ∘ π) = ζ_p · (ξ f) ∘ π` for every holomorphic `f` (`eventually_fieldDeriv_liftField_comp`),
  `liftField(ζ_p) = (ξ ψ_p) ∘ π · ζ_p` (`eventually_fieldDeriv_liftField_t`),

and if `ξ` is logarithmic for `(N, E)` then `liftField e ξ` is logarithmic for `(N', E')`
(`isLogTangentField_liftField`).  This is the transformation law of logarithmic derivations under an admissible
blowup (Bierstone--Milman 2008, Lemma 3.1): the lift of `ξ` has a simple pole along the exceptional divisor, and
`ζ_p ξ` lifts to a logarithmic field.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogLiftChart

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
open Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong
  Hironaka.DerivativeIdealAlongCoherent Hironaka.DerivativeIdealAlongEtale
  Hironaka.HadamardBridge
  Hironaka.GiraudAlong Hironaka.BlowupFlatCoordinates
  Hironaka.NormalCrossings Hironaka.RelativePrincipalizationSpan
  Hironaka.BlowupStrictIdeal
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaG8TransverseCarrierIdeal
  Hironaka.HironakaG8FlatFieldCalculus
  Hironaka.HironakaG8LogDerivEtale
  Hironaka.HironakaG8ExceptionalLogCentre
  Hironaka.BlowupMonomialCharts Hironaka.BlowupLocalSurjectivity
  Hironaka.BlowupSNCTransform Hironaka.BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- **Coordinate data of a blowup along `C` at a point `y` of the strict transform** (see the module docstring). -/
structure LogLiftChart (C N : Set X) (E : List (Set X)) (N' : Set Y) (E' : List (Set Y)) (π : Y → X) (y : Y) where
  Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π y) (π y))
  hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π y)).target
  Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y)
  hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) y).target
  B : Finset (Fin n)
  p : Fin n
  Q : Finset (Fin n)
  v : Fin n → ℂ
  p_B : p ∉ B
  p_Q : p ∉ Q
  v_B : ∀ b ∈ B, v b = 0
  kC : ℕ
  C_flat : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source →
    chartAt (ComplexModel n) (π y) u ∈ Φ.source →
    (u ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π y) u) ∈ complexCoordinatePlane n kC)
  centre_idx : ∀ l : Fin n, kC ≤ l.val → l = p ∨ l ∈ Q
  v_p : v p = 0
  N_flat : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source →
    chartAt (ComplexModel n) (π y) u ∈ Φ.source →
    (u ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace B)
  mdiff : ∀ᶠ u in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π u
  coord_eq : ∀ l : Fin n, flatCoord Φ l ∘ π =ᶠ[𝓝 y] fun u =>
    if l ∈ Q then flatCoord Θ p u * (flatCoord Θ l u + v l) else flatCoord Θ l u + v l
  N'_flat : ∀ {u : Y}, u ∈ (chartAt (ComplexModel n) y).source →
    chartAt (ComplexModel n) y u ∈ Θ.source →
    (u ∈ N' ↔ Θ.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace B)
  Exc_flat : ∀ {u : Y}, u ∈ (chartAt (ComplexModel n) y).source →
    chartAt (ComplexModel n) y u ∈ Θ.source →
    (u ∈ π ⁻¹' C ↔ Θ.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {p})
  E'_flat : ∀ H' ∈ E', (∀ᶠ u in 𝓝 y, u ∉ H') ∨ ∃ m, v m = 0 ∧
    (∀ {u : Y}, u ∈ (chartAt (ComplexModel n) y).source → chartAt (ComplexModel n) y u ∈ Θ.source →
      (u ∈ H' ↔ Θ.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {m})) ∧
    (m = p ∨ ∃ H ∈ E, ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) u ∈ Φ.source →
      (u ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace {m}))

namespace LogLiftChart

variable {C N : Set X} {E : List (Set X)} {N' : Set Y} {E' : List (Set Y)} {π : Y → X} {y : Y}
  (K : LogLiftChart C N E N' E' π y)
include K

theorem mem_flatDomain_Φ : π y ∈ flatDomain K.Φ := mem_flatDomain_self K.Φ
theorem mem_flatDomain_Θ : y ∈ flatDomain K.Θ := mem_flatDomain_self K.Θ

theorem tendsto_π : Tendsto π (𝓝 y) (𝓝 (π y)) := K.mdiff.self_of_nhds.continuousAt.tendsto

theorem eventually_flatDomain_Φ : ∀ᶠ u in 𝓝 y, π u ∈ flatDomain K.Φ :=
  K.tendsto_π.eventually ((isOpen_flatDomain K.Φ).mem_nhds K.mem_flatDomain_Φ)

theorem eventually_flatDomain_Θ : ∀ᶠ u in 𝓝 y, u ∈ flatDomain K.Θ :=
  (isOpen_flatDomain K.Θ).mem_nhds K.mem_flatDomain_Θ

/-- Near `y`: if `v_m = 0` and `ζ_m` vanishes at `u`, then `ψ_m` vanishes at `π u`. -/
theorem eventually_coord_eq_zero (m : Fin n) (hv : K.v m = 0) :
    ∀ᶠ u in 𝓝 y, flatCoord K.Θ m u = 0 → flatCoord K.Φ m (π u) = 0 := by
  filter_upwards [K.coord_eq m] with u hu hz
  have hu' : flatCoord K.Φ m (π u) =
      if m ∈ K.Q then flatCoord K.Θ K.p u * (flatCoord K.Θ m u + K.v m) else flatCoord K.Θ m u + K.v m := hu
  rw [hu', hz, hv]
  split_ifs <;> simp

/-- Near `y`, the strict carrier lies over the carrier. -/
theorem eventually_mem_N : ∀ᶠ u in 𝓝 y, u ∈ N' → π u ∈ N := by
  have hB' : ∀ᶠ u in 𝓝 y, ∀ b ∈ K.B, flatCoord K.Θ b u = 0 → flatCoord K.Φ b (π u) = 0 := by
    rw [Finset.eventually_all]
    intro b hb
    exact K.eventually_coord_eq_zero b (K.v_B b hb)
  filter_upwards [hB', K.eventually_flatDomain_Φ, K.eventually_flatDomain_Θ] with u hu hπu hΘu huN
  refine (K.N_flat hπu.1 hπu.2).mpr fun b hb => ?_
  exact hu b hb ((K.N'_flat hΘu.1 hΘu.2).mp huN b hb)

theorem flatCoord_mem_N {m : Fin n} (hm : m ∈ K.B) :
    (vanishingIdeal (n := n) N).mem (π y) (flatCoord K.Φ m) :=
  ⟨holomorphicAt_flatCoord K.Φ m K.mem_flatDomain_Φ, by
    filter_upwards [(isOpen_flatDomain K.Φ).mem_nhds K.mem_flatDomain_Φ] with q hq hqN
    exact (K.N_flat hq.1 hq.2).mp hqN m hm⟩

/-- The exceptional coordinate does not vanish off the preimage of the centre. -/
theorem flatCoord_p_ne_zero {u : Y} (hu : u ∈ flatDomain K.Θ) (huC : π u ∉ C) : flatCoord K.Θ K.p u ≠ 0 := by
  intro h0
  refine huC ((K.Exc_flat hu.1 hu.2).mpr fun j hj => ?_)
  rw [Finset.mem_singleton] at hj
  subst hj
  exact h0

/-- **Germs vanishing on the centre pull back to multiples of the exceptional coordinate**: for `a ∈ 𝓘_C` at `π y`,
`a ∘ π = ζ_p · h` near `y` with `h` holomorphic (Hadamard in the flat coordinates at `π y`, then
`ψ_l ∘ π = ζ_p (ζ_l + v_l)` for `l ∈ Q` and `ψ_p ∘ π = ζ_p`). -/
theorem exists_comp_eq_mul_t {a : X → ℂ} (ha : (vanishingIdeal (n := n) C).mem (π y) a) :
    ∃ h : Y → ℂ, HolomorphicAt n h y ∧
      (fun u => a (π u)) =ᶠ[𝓝 y] fun u => flatCoord K.Θ K.p u * h u := by
  classical
  obtain ⟨b, hb0, hbh, hab⟩ := exists_eq_sum_flatCoord K.Φ K.hΦsrc K.C_flat K.mem_flatDomain_Φ ha
  refine ⟨fun u => ∑ i, b i (π u) * (if i ∈ K.Q then flatCoord K.Θ i u + K.v i else 1), ?_, ?_⟩
  · refine HolomorphicAt.sum _ fun i _ => (holomorphicAt_comp_map K.mdiff (hbh i)).mul ?_
    split_ifs
    · exact (holomorphicAt_flatCoord K.Θ i K.mem_flatDomain_Θ).add (holomorphicAt_const _)
    · exact holomorphicAt_const 1
  · filter_upwards [K.tendsto_π.eventually hab, eventually_all.2 K.coord_eq] with u h1 h2
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2i : flatCoord K.Φ i (π u) =
        if i ∈ K.Q then flatCoord K.Θ K.p u * (flatCoord K.Θ i u + K.v i) else flatCoord K.Θ i u + K.v i :=
      h2 i
    by_cases hi : K.kC ≤ i.val
    · rcases K.centre_idx i hi with hip | hiQ
      · have hiQ : i ∉ K.Q := fun h => K.p_Q (hip ▸ h)
        rw [h2i, if_neg hiQ, if_neg hiQ, hip, K.v_p]
        ring
      · rw [h2i, if_pos hiQ, if_pos hiQ]
        ring
    · rw [hb0 i (Nat.lt_of_not_le hi)]
      simp

/-! ### The lifted field -/

/-- The coefficient `ξ(ψ_l)` of a source field in the flat coordinates at `π y`. -/
def srcCoeff (e : ComplexChart n X) (ξ : Fin n → X → ℂ) (l : Fin n) : X → ℂ :=
  fieldDeriv e ξ (flatCoord K.Φ l)

theorem holomorphicAt_srcCoeff {e : ComplexChart n X} {ξ : Fin n → X → ℂ} (hx : π y ∈ e.val.source)
    (hξ : ∀ m, HolomorphicAt n (ξ m) (π y)) (l : Fin n) : HolomorphicAt n (K.srcCoeff e ξ l) (π y) :=
  holomorphicAt_fieldDeriv hx hξ (holomorphicAt_flatCoord K.Φ l K.mem_flatDomain_Φ)

theorem holomorphicAt_srcCoeff_comp {e : ComplexChart n X} {ξ : Fin n → X → ℂ} (hx : π y ∈ e.val.source)
    (hξ : ∀ m, HolomorphicAt n (ξ m) (π y)) (l : Fin n) :
    HolomorphicAt n (fun u => K.srcCoeff e ξ l (π u)) y :=
  holomorphicAt_comp_map K.mdiff (K.holomorphicAt_srcCoeff hx hξ l)

/-- The coefficients, in the target flat coordinates, of the lift of `ζ_p ξ`:
`ζ_p a_p ∂_p + ∑_{l ∈ Q} (a_l - a_p (ζ_l + v_l)) ∂_l + ∑_{l ∉ Q ∪ {p}} ζ_p a_l ∂_l`, with `a_l = ξ(ψ_l) ∘ π`. -/
def liftCoeff (e : ComplexChart n X) (ξ : Fin n → X → ℂ) (r : Fin n) : Y → ℂ :=
  if r = K.p then fun u => flatCoord K.Θ K.p u * K.srcCoeff e ξ K.p (π u)
  else if r ∈ K.Q then
    fun u => K.srcCoeff e ξ r (π u) - K.srcCoeff e ξ K.p (π u) * (flatCoord K.Θ r u + K.v r)
  else fun u => flatCoord K.Θ K.p u * K.srcCoeff e ξ r (π u)

theorem liftCoeff_p (e : ComplexChart n X) (ξ : Fin n → X → ℂ) :
    K.liftCoeff e ξ K.p = fun u => flatCoord K.Θ K.p u * K.srcCoeff e ξ K.p (π u) := by
  rw [liftCoeff, if_pos rfl]

theorem liftCoeff_Q (e : ComplexChart n X) (ξ : Fin n → X → ℂ) {r : Fin n} (hr : r ∈ K.Q) :
    K.liftCoeff e ξ r =
      fun u => K.srcCoeff e ξ r (π u) - K.srcCoeff e ξ K.p (π u) * (flatCoord K.Θ r u + K.v r) := by
  have hrp : r ≠ K.p := fun h => K.p_Q (h ▸ hr)
  rw [liftCoeff, if_neg hrp, if_pos hr]

theorem liftCoeff_other (e : ComplexChart n X) (ξ : Fin n → X → ℂ) {r : Fin n} (hrp : r ≠ K.p)
    (hr : r ∉ K.Q) : K.liftCoeff e ξ r = fun u => flatCoord K.Θ K.p u * K.srcCoeff e ξ r (π u) := by
  rw [liftCoeff, if_neg hrp, if_neg hr]

theorem holomorphicAt_liftCoeff {e : ComplexChart n X} {ξ : Fin n → X → ℂ} (hx : π y ∈ e.val.source)
    (hξ : ∀ m, HolomorphicAt n (ξ m) (π y)) (r : Fin n) : HolomorphicAt n (K.liftCoeff e ξ r) y := by
  have hz : ∀ l, HolomorphicAt n (flatCoord K.Θ l) y := fun l =>
    holomorphicAt_flatCoord K.Θ l K.mem_flatDomain_Θ
  have ha : ∀ l, HolomorphicAt n (fun u => K.srcCoeff e ξ l (π u)) y := fun l =>
    K.holomorphicAt_srcCoeff_comp hx hξ l
  by_cases hrp : r = K.p
  · rw [hrp, K.liftCoeff_p]
    exact (hz K.p).mul (ha K.p)
  · by_cases hrQ : r ∈ K.Q
    · rw [K.liftCoeff_Q e ξ hrQ]
      exact holomorphicAt_sub (ha r) ((ha K.p).mul ((hz r).add (holomorphicAt_const (K.v r))))
    · rw [K.liftCoeff_other e ξ hrp hrQ]
      exact (hz K.p).mul (ha r)

/-- **The lift of `ζ_p ξ`**, a field at `y` written in the preferred chart at `y`. -/
def liftField (e : ComplexChart n X) (ξ : Fin n → X → ℂ) : Fin n → Y → ℂ :=
  combField K.Θ (K.liftCoeff e ξ)

theorem holomorphicAt_liftField {e : ComplexChart n X} {ξ : Fin n → X → ℂ} (hx : π y ∈ e.val.source)
    (hξ : ∀ m, HolomorphicAt n (ξ m) (π y)) (m : Fin n) : HolomorphicAt n (K.liftField e ξ m) y :=
  holomorphicAt_combField K.mem_flatDomain_Θ (K.holomorphicAt_liftCoeff hx hξ) m

theorem fieldDeriv_liftField_flatCoord (e : ComplexChart n X) (ξ : Fin n → X → ℂ) (r : Fin n) {u : Y}
    (hu : u ∈ flatDomain K.Θ) :
    fieldDeriv (complexChartAt (n := n) y) (K.liftField e ξ) (flatCoord K.Θ r) u = K.liftCoeff e ξ r u :=
  fieldDeriv_combField_flatCoord K.hΘsrc _ r hu

theorem eventually_fieldDeriv_liftField_flatCoord (e : ComplexChart n X) (ξ : Fin n → X → ℂ) (r : Fin n) :
    fieldDeriv (complexChartAt (n := n) y) (K.liftField e ξ) (flatCoord K.Θ r) =ᶠ[𝓝 y] K.liftCoeff e ξ r := by
  filter_upwards [K.eventually_flatDomain_Θ] with u hu
  exact K.fieldDeriv_liftField_flatCoord e ξ r hu

/-- **The lifted field on the pulled-back source coordinates**: `liftField(ψ_l ∘ π) = ζ_p · ξ(ψ_l) ∘ π`. -/
theorem eventually_fieldDeriv_liftField_coord (e : ComplexChart n X) (ξ : Fin n → X → ℂ) (l : Fin n) :
    fieldDeriv (complexChartAt (n := n) y) (K.liftField e ξ) (flatCoord K.Φ l ∘ π) =ᶠ[𝓝 y]
      fun u => flatCoord K.Θ K.p u * K.srcCoeff e ξ l (π u) := by
  have hy : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
  have hcongr := DerivativeIdealAlongEtale.fieldDeriv_congr (ξ := K.liftField e ξ) hy (K.coord_eq l)
  have hz : ∀ l, HolomorphicAt n (flatCoord K.Θ l) y := fun l =>
    holomorphicAt_flatCoord K.Θ l K.mem_flatDomain_Θ
  by_cases hlQ : l ∈ K.Q
  · simp only [hlQ, if_true] at hcongr
    have hprod := fieldDeriv_mul_eventuallyEq (ξ := K.liftField e ξ) hy (hz K.p)
      ((hz l).add (holomorphicAt_const (K.v l)))
    filter_upwards [hcongr, hprod, K.eventually_flatDomain_Θ] with u h1 h2 hu
    rw [h1, h2, fieldDeriv_add_const, K.fieldDeriv_liftField_flatCoord e ξ K.p hu,
      K.fieldDeriv_liftField_flatCoord e ξ l hu, K.liftCoeff_p, K.liftCoeff_Q e ξ hlQ]
    ring
  · simp only [hlQ, if_false] at hcongr
    filter_upwards [hcongr, K.eventually_flatDomain_Θ] with u h1 hu
    rw [h1, fieldDeriv_add_const, K.fieldDeriv_liftField_flatCoord e ξ l hu]
    by_cases hlp : l = K.p
    · rw [hlp, K.liftCoeff_p]
    · rw [K.liftCoeff_other e ξ hlp hlQ]

/-- **The lift identity**: `liftField(f ∘ π) = ζ_p · (ξ f) ∘ π` near `y`, for every `f` holomorphic at `π y`. -/
theorem eventually_fieldDeriv_liftField_comp {e : ComplexChart n X} (ξ : Fin n → X → ℂ)
    (hx : π y ∈ e.val.source) {f : X → ℂ} (hf : HolomorphicAt n f (π y)) :
    fieldDeriv (complexChartAt (n := n) y) (K.liftField e ξ) (f ∘ π) =ᶠ[𝓝 y]
      fun u => flatCoord K.Θ K.p u * fieldDeriv e ξ f (π u) := by
  have hy : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
  have hCR := fieldDeriv_comp_eventuallyEq_sum_flatPartial K.hΦsrc K.mdiff K.mem_flatDomain_Φ
    (complexChartAt (n := n) y) hy (K.liftField e ξ) hf
  have hsrc := K.tendsto_π.eventually
    (fieldDeriv_eventuallyEq_sum_flatPartial K.hΦsrc e ξ hx K.mem_flatDomain_Φ hf)
  filter_upwards [hCR, eventually_all.2 (K.eventually_fieldDeriv_liftField_coord e ξ), hsrc] with u h1 h2 h3
  rw [h1, h3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h2 m]
  simp only [srcCoeff]
  ring

/-- **The lifted field is logarithmic along the exceptional coordinate**: `liftField(ζ_p) = ξ(ψ_p) ∘ π · ζ_p`. -/
theorem eventually_fieldDeriv_liftField_t (e : ComplexChart n X) (ξ : Fin n → X → ℂ) :
    fieldDeriv (complexChartAt (n := n) y) (K.liftField e ξ) (flatCoord K.Θ K.p) =ᶠ[𝓝 y]
      fun u => K.srcCoeff e ξ K.p (π u) * flatCoord K.Θ K.p u := by
  filter_upwards [K.eventually_flatDomain_Θ] with u hu
  rw [K.fieldDeriv_liftField_flatCoord e ξ K.p hu, K.liftCoeff_p]
  ring

/-- **The lift of a logarithmic field is logarithmic** for the strict carrier and the target boundary list. -/
theorem isLogTangentField_liftField {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsLogTangentField N E e ξ (π y)) :
    IsLogTangentField N' E' (complexChartAt (n := n) y) (K.liftField e ξ) y := by
  have hy : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
  have hx := hξ.1.mem_source
  have hξh := hξ.1.holomorphicAt
  have hhol := K.holomorphicAt_liftField hx hξh
  have hψ : ∀ l, HolomorphicAt n (flatCoord K.Φ l) (π y) := fun l =>
    holomorphicAt_flatCoord K.Φ l K.mem_flatDomain_Φ
  refine ⟨isTangentField_of_coordinate K.hΘsrc K.B K.N'_flat K.mem_flatDomain_Θ hy hhol fun b hb => ?_,
    fun H' hH' => ?_⟩
  · -- the carrier
    refine mem_vanishing_of_eventuallyEq (K.eventually_fieldDeriv_liftField_flatCoord e ξ b)
      ⟨K.holomorphicAt_liftCoeff hx hξh b, ?_⟩
    have hbp : b ≠ K.p := fun h => K.p_B (h ▸ hb)
    have hab : ∀ᶠ u in 𝓝 y, u ∈ N' → K.srcCoeff e ξ b (π u) = 0 := by
      have h1 := (hξ.1.preserves _ (K.flatCoord_mem_N hb)).2
      filter_upwards [K.tendsto_π.eventually h1, K.eventually_mem_N] with u hu hN huN
      exact hu (hN huN)
    filter_upwards [hab, K.eventually_flatDomain_Θ] with u hu hΘu huN
    have hζ : flatCoord K.Θ b u = 0 := (K.N'_flat hΘu.1 hΘu.2).mp huN b hb
    by_cases hbQ : b ∈ K.Q
    · rw [K.liftCoeff_Q e ξ hbQ]
      beta_reduce
      rw [hu huN, hζ, K.v_B b hb]
      ring
    · rw [K.liftCoeff_other e ξ hbp hbQ]
      beta_reduce
      rw [hu huN, mul_zero]
  · -- the boundary members
    rcases K.E'_flat H' hH' with hout | ⟨m, hvm, hflat', hsrc⟩
    · exact isTangentField_of_eventually_notMem hy hhol hout
    · refine isTangentField_of_coordinate K.hΘsrc {m} hflat' K.mem_flatDomain_Θ hy hhol fun t ht => ?_
      rw [Finset.mem_singleton] at ht
      subst ht
      refine mem_vanishing_of_eventuallyEq (K.eventually_fieldDeriv_liftField_flatCoord e ξ t)
        ⟨K.holomorphicAt_liftCoeff hx hξh t, ?_⟩
      by_cases htp : t = K.p
      · filter_upwards [K.eventually_flatDomain_Θ] with u hΘu huH
        have hζ : flatCoord K.Θ t u = 0 :=
          (hflat' hΘu.1 hΘu.2).mp huH t (Finset.mem_singleton_self t)
        rw [htp] at hζ ⊢
        rw [K.liftCoeff_p]
        beta_reduce
        rw [hζ, zero_mul]
      · obtain ⟨H, hH, hflat⟩ := hsrc.resolve_left htp
        have hmemH : (vanishingIdeal (n := n) H).mem (π y) (flatCoord K.Φ t) :=
          mem_vanishing_of_coord t hflat K.mem_flatDomain_Φ (hψ t) fun _ _ h => h
        have h1 := ((hξ.2 H hH).preserves _ hmemH).2
        have hat : ∀ᶠ u in 𝓝 y, flatCoord K.Θ t u = 0 → K.srcCoeff e ξ t (π u) = 0 := by
          filter_upwards [K.tendsto_π.eventually h1, K.eventually_coord_eq_zero t hvm,
            K.eventually_flatDomain_Φ] with u hu h0 hπu hζ
          refine hu ((hflat hπu.1 hπu.2).mpr fun j hj => ?_)
          rw [Finset.mem_singleton] at hj
          subst hj
          exact h0 hζ
        filter_upwards [hat, K.eventually_flatDomain_Θ] with u hu hΘu huH
        have hζ : flatCoord K.Θ t u = 0 :=
          (hflat' hΘu.1 hΘu.2).mp huH t (Finset.mem_singleton_self t)
        by_cases htQ : t ∈ K.Q
        · rw [K.liftCoeff_Q e ξ htQ]
          beta_reduce
          rw [hu hζ, hζ, hvm]
          ring
        · rw [K.liftCoeff_other e ξ htp htQ]
          beta_reduce
          rw [hu hζ, mul_zero]

end LogLiftChart

/-! ### Existence over an admissible centre -/

/-- **Every point of the strict carrier over an adapted centre carries a log-lift chart** for
`(C, N, E)` and `(strict N, strict E ++ [π⁻¹C])`.  The hypothesis `IsAdaptedAt n C N E (π y)` is the simultaneous
normal crossings of `C`, `N` and `E` at `π y` (coordinates in which `C ⊆ N` are nested coordinate planes and every
member of `E` through `π y` is a coordinate hyperplane transverse to `N`).  The chart is built from the actual
monomial local inverse of the blowup and its recentring. -/
theorem exists_logLiftChart {C N : Set X} {E : List (Set X)} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hEc : ∀ H ∈ E, IsClosed H) {y : Y} (hyC : π y ∈ C) (hyN : y ∈ geoStrictTransform π C N)
    (had : IsAdaptedAt n C N E (π y)) :
    Nonempty (LogLiftChart C N E (geoStrictTransform π C N)
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) π y) := by
  classical
  obtain ⟨kC, kN, Phi, s, hsrc, -, -, hflat⟩ := had
  have hz' : π y ∈ flatDomain Phi := mem_flatDomain_self Phi
  have hflatC : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) u ∈ Phi.source →
      (u ∈ C ↔ Phi.toFun (chartAt (ComplexModel n) (π y) u) ∈ complexCoordinatePlane n kC) :=
    fun hu huP => (hflat hu huP).1
  set B : Finset (Fin n) := Finset.univ.filter fun t : Fin n => kN ≤ t.1 with hB
  have hflatN : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) u ∈ Phi.source →
      (u ∈ N ↔ Phi.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace B) := by
    intro u hu huP
    rw [hB, coordSubspace_eq_complexCoordinatePlane]
    exact (hflat hu huP).2.1
  have hflatH : ∀ i : Fin E.length, π y ∈ E.get i → ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) u ∈ Phi.source →
      (u ∈ E.get i ↔ Phi.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace {s i}) := by
    intro i hi u hu huP
    rw [mem_coordSubspace_singleton]
    exact (hflat hu huP).2.2 i hi
  obtain ⟨p, hp, O, hO, hyO, W, hWs, hWeq, hleft, -⟩ := exists_monomialLocalInverse hπ hsrc hflatC hz'
  have hWmem : ∀ u ∈ O, W u ∈ monomialDomain Phi kC p := by
    intro u hu
    show monomial kC p (W u) ∈ Phi.target
    rw [(hWeq u hu).2]
    exact Phi.mapsTo_toFun (hWeq u hu).1.2
  obtain ⟨ell, ⟨hells, hellpi⟩, -⟩ := existsUnique_monomialLift hπ hsrc hflatC hp
  have hinj := injective_fderiv_of_monomialInverse hO hWs hWmem hells (hleft ell hells hellpi) hyO
  obtain ⟨Theta, htgt, -, hTheta⟩ := exists_recentred_coords hO hWs hyO hinj
  set v : ComplexModel n := W y with hv
  set Q : Finset (Fin n) := Finset.univ.filter fun l : Fin n => kC ≤ l.val ∧ l ≠ p with hQ
  have hThetaW : ∀ {u : Y}, u ∈ flatDomain Theta → u ∈ O ∧ ∀ l, flatCoord Theta l u = W u l - v l := by
    intro u hu
    obtain ⟨huO, heq⟩ := hTheta hu.1 hu.2
    refine ⟨huO, fun l => ?_⟩
    have heq' : Theta.toFun (chartAt (ComplexModel n) y u) = W u - v := heq
    change Theta.toFun (chartAt (ComplexModel n) y u) l = W u l - v l
    rw [heq']
    rfl
  have hstrict : ∀ {H : Set X} {T : Finset (Fin n)},
      (∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source → chartAt (ComplexModel n) (π y) u ∈ Phi.source →
        (u ∈ H ↔ Phi.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace T)) →
      ∀ u ∈ O, (u ∈ geoStrictTransform π C H ↔ p ∉ T ∧ W u ∈ coordSubspace T) :=
    fun hflatA u hu => mem_geoStrictTransform_iff_of_chart hπ hsrc hflatC hflatA hp hO hWs hWeq hleft hu
  have hExc : ∀ u ∈ O, (π u ∈ C ↔ W u p = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hp]
  have hvp : v p = 0 := (hExc y hyO).mp hyC
  have hNy := (hstrict hflatN y hyO).mp hyN
  have hOnhds : ∀ᶠ u in 𝓝 y, u ∈ O := hO.mem_nhds hyO
  have hWcont : ContinuousAt W y := (hWs y hyO).continuousAt
  have hcoordW : ∀ {H' : Set Y} {m : Fin n}, v m = 0 → (∀ u ∈ O, (u ∈ H' ↔ W u m = 0)) →
      ∀ {u : Y}, u ∈ (chartAt (ComplexModel n) y).source → chartAt (ComplexModel n) y u ∈ Theta.source →
        (u ∈ H' ↔ Theta.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {m}) := by
    intro H' m hvm hH' u hu huT
    obtain ⟨huO, hz⟩ := hThetaW (u := u) ⟨hu, huT⟩
    rw [hH' u huO]
    have hz' := hz m
    change Theta.toFun (chartAt (ComplexModel n) y u) m = W u m - v m at hz'
    rw [show Theta.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {m} ↔
      Theta.toFun (chartAt (ComplexModel n) y u) m = 0 by simp [coordSubspace], hz', hvm, sub_zero]
  refine ⟨{
    Φ := Phi
    hΦsrc := hsrc
    Θ := Theta
    hΘsrc := htgt
    B := B
    p := p
    Q := Q
    v := fun l => v l
    p_B := hNy.1
    p_Q := by simp [hQ]
    v_B := fun b hb => hNy.2 b hb
    kC := kC
    C_flat := hflatC
    centre_idx := fun l hl => by
      by_cases hlp : l = p
      · exact Or.inl hlp
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hlp⟩)
    v_p := hvp
    N_flat := hflatN
    mdiff := Eventually.of_forall fun u => (hπ.contMDiff u).mdifferentiableAt (by simp)
    coord_eq := ?_
    N'_flat := ?_
    Exc_flat := ?_
    E'_flat := ?_ }⟩
  · -- `coord_eq`
    intro l
    filter_upwards [(isOpen_flatDomain Theta).mem_nhds (mem_flatDomain_self Theta)] with u hu
    obtain ⟨huO, hz⟩ := hThetaW hu
    have hmono : flatCoord Phi l (π u) = monomial kC p (W u) l := by
      change Phi.toFun (chartAt (ComplexModel n) (π y) (π u)) l = _
      rw [← (hWeq u huO).2]
    simp only [Function.comp_apply, hmono, monomial_apply, hz]
    by_cases hlQ : l ∈ Q
    · have hl : kC ≤ l.val ∧ l ≠ p := (Finset.mem_filter.mp hlQ).2
      rw [if_pos hl, if_pos hlQ, hvp]
      ring
    · have hl : ¬(kC ≤ l.val ∧ l ≠ p) := fun h' => hlQ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
      rw [if_neg hl, if_neg hlQ]
      ring
  · -- `N'_flat`
    intro u hu huT
    obtain ⟨huO, -⟩ := hThetaW (u := u) ⟨hu, huT⟩
    obtain ⟨-, heq⟩ := hTheta hu huT
    have heq' : Theta.toFun (chartAt (ComplexModel n) y u) = W u - v := heq
    rw [(hstrict hflatN u huO).trans (and_iff_right hNy.1), heq']
    exact (sub_mem_coordSubspace_iff hNy.2).symm
  · -- `Exc_flat`
    intro u hu huT
    exact hcoordW (H' := π ⁻¹' C) hvp (fun u' hu' => hExc u' hu') hu huT
  · -- `E'_flat`
    intro H' hH'
    rcases List.mem_append.mp hH' with hH' | hH'
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      obtain ⟨h, rfl⟩ := List.mem_iff_get.mp hH
      by_cases hxh : π y ∈ E.get h
      · by_cases hsp : s h = p
        · left
          filter_upwards [hOnhds] with u hu hmem
          exact ((hstrict (hflatH h hxh) u hu).mp hmem).1 (by rw [hsp]; exact Finset.mem_singleton_self p)
        · by_cases hvs : v (s h) = 0
          · right
            refine ⟨s h, hvs, hcoordW hvs fun u hu => ?_, Or.inr ⟨E.get h, List.get_mem E h, hflatH h hxh⟩⟩
            rw [hstrict (hflatH h hxh) u hu, and_iff_right (by simpa [eq_comm] using hsp)]
            simp [coordSubspace]
          · left
            have hne : ∀ᶠ u in 𝓝 y, W u (s h) ≠ 0 :=
              ((EuclideanSpace.proj (𝕜 := ℂ) (s h)).continuous.continuousAt.comp hWcont).eventually_ne hvs
            filter_upwards [hOnhds, hne] with u hu hne' hmem
            exact hne' (((hstrict (hflatH h hxh) u hu).mp hmem).2 (s h) (Finset.mem_singleton_self _))
      · left
        have hcl : IsClosed (E.get h) := hEc _ (List.get_mem E h)
        filter_upwards [(hcl.preimage hπ.contMDiff.continuous).isOpen_compl.mem_nhds hxh] with u hu hmem
        exact hu (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hcl hmem)
    · rw [List.mem_singleton] at hH'
      subst hH'
      exact Or.inr ⟨p, hvp, hcoordW hvp fun u hu => hExc u hu, Or.inl rfl⟩

end

end Hironaka.HironakaG8LogLiftChart

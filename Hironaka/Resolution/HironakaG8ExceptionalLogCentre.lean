import Hironaka.Resolution.HironakaG8FlatFieldCalculus
import Hironaka.Resolution.HironakaG8LogDerivEtale

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ordinary exceptional log equality at a centre point, from a centre chart (G8 lane, run 0079)

Blueprint: `hironaka-g8-resume-exceptional-log-centre.tex`.

A `CentreChart` at `y` records the coordinate shape of an ordinary blowup of two transverse boundary members at
a point `y` over the centre: flat coordinates `ψ` at `x = π y` and `ζ` at `y` with

* `N = {ψ_b = 0, b ∈ B}`, every member of `E` through `x` is `{ψ_m = 0}` for a boundary index `m ∈ bd`
  (`bd ∩ B = ∅`), the others miss a neighbourhood of `x`;
* `ψ_l ∘ π = ζ_l` for `l ∉ Q` and `ψ_l ∘ π = ζ_p · (ζ_l + v_l)` for `l ∈ Q` (the monomial chart with pivot
  `p ∈ bd`, `Q ⊆ bd`, recentred at `y`);
* `N' = {ζ_b = 0, b ∈ B}`, every member of `E'` is `{ζ_m = 0}` for some `m ∈ bd` with `v_m = 0` or misses a
  neighbourhood of `y`, and every such `ζ_m` cuts out a member of `E'`.

`log_mem_iff_of_centreChart` proves from these data alone that the ordinary pullback of the log operator of
`(N, E, A)` and the log operator of `(N', E', π^*A)` have the same germs at `y`.  The proof lifts the weighted
coordinate fields `ψ_m ∂/∂ψ_m` (boundary `m`) and `∂/∂ψ_m` (other tangential `m`) to explicit log fields of the
target (`ζ_p ∂_p - ∑_{q∈Q} (ζ_q + v_q) ∂_q` for the pivot, `(ζ_q + v_q) ∂_q` for `q ∈ Q`), and conversely
expands every target log field through the chain rule.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ExceptionalLogCentre

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

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n}

/-! ### Single-coordinate division -/

section Division

variable {y₀ : X} {Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}

/-- **Division by one flat coordinate.**  If `H = {ψ_m = 0}` on the flat domain, every germ of `𝓘_H` at a point
of the flat domain is a holomorphic multiple of `ψ_m`. -/
theorem exists_eq_mul_flatCoord (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) y₀).target) (m : Fin n)
    {H : Set X}
    (hH : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ u ∈ Θ.source →
      (u ∈ H ↔ Θ.toFun (chartAt (ComplexModel n) y₀ u) ∈ coordSubspace {m}))
    {u : X} (hu : u ∈ flatDomain Θ) {g : X → ℂ} (hg : (vanishingIdeal (n := n) H).mem u g) :
    ∃ d : X → ℂ, HolomorphicAt n d u ∧ g =ᶠ[𝓝 u] fun q => d q * flatCoord Θ m q := by
  classical
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ :=
    (mem_vanishingIdeal_iff_coordinate_span Θ hΘsrc {m} H hH hu g).mp hg
  choose a ha using hs
  refine ⟨fun q => ∑ k, if a k = m then c k q else 0,
    HolomorphicAt.sum _ fun k _ => ?_, ?_⟩
  · by_cases hk : a k = m
    · simpa only [hk, if_true] using hc k
    · simpa only [hk, if_false] using holomorphicAt_const (n := n) (x := u) (0 : ℂ)
  · filter_upwards [hsum] with q hq
    rw [hq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ha k]
    by_cases hk : a k = m
    · simp [hk]
    · simp [hk]

end Division

/-! ### The centre chart -/

/-- **Coordinate data at a point `y` over the centre** (see the module docstring). -/
structure CentreChart (N : Set X) (E : List (Set X)) (N' : Set Y) (E' : List (Set Y)) (π : Y → X) (y : Y) where
  Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π y) (π y))
  hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π y)).target
  Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y)
  hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) y).target
  Θ_zero : Θ.toFun (chartAt (ComplexModel n) y y) = 0
  B : Finset (Fin n)
  bd : Finset (Fin n)
  p : Fin n
  Q : Finset (Fin n)
  v : Fin n → ℂ
  disj : Disjoint bd B
  p_bd : p ∈ bd
  Q_bd : Q ⊆ bd
  p_Q : p ∉ Q
  v_zero : ∀ l, l ∉ Q → v l = 0
  N_flat : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π y)).source →
    chartAt (ComplexModel n) (π y) u ∈ Φ.source →
    (u ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace B)
  E_flat : ∀ H ∈ E, (∀ᶠ u in 𝓝 (π y), u ∉ H) ∨ ∃ m ∈ bd, ∀ {u : X},
    u ∈ (chartAt (ComplexModel n) (π y)).source → chartAt (ComplexModel n) (π y) u ∈ Φ.source →
    (u ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace {m})
  bd_flat : ∀ m ∈ bd, ∃ H ∈ E, ∀ {u : X},
    u ∈ (chartAt (ComplexModel n) (π y)).source → chartAt (ComplexModel n) (π y) u ∈ Φ.source →
    (u ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) (π y) u) ∈ coordSubspace {m})
  mdiff : ∀ᶠ u in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π u
  coord_eq : ∀ l : Fin n, flatCoord Φ l ∘ π =ᶠ[𝓝 y] fun u =>
    if l ∈ Q then flatCoord Θ p u * (flatCoord Θ l u + v l) else flatCoord Θ l u
  N'_flat : ∀ {u : Y}, u ∈ (chartAt (ComplexModel n) y).source →
    chartAt (ComplexModel n) y u ∈ Θ.source →
    (u ∈ N' ↔ Θ.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace B)
  E'_flat : ∀ H' ∈ E', (∀ᶠ u in 𝓝 y, u ∉ H') ∨ ∃ m ∈ bd, v m = 0 ∧ ∀ {u : Y},
    u ∈ (chartAt (ComplexModel n) y).source → chartAt (ComplexModel n) y u ∈ Θ.source →
    (u ∈ H' ↔ Θ.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {m})
  bd'_flat : ∀ m ∈ bd, v m = 0 → ∃ H' ∈ E', ∀ {u : Y},
    u ∈ (chartAt (ComplexModel n) y).source → chartAt (ComplexModel n) y u ∈ Θ.source →
    (u ∈ H' ↔ Θ.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {m})

namespace CentreChart

variable {N : Set X} {E : List (Set X)} {N' : Set Y} {E' : List (Set Y)} {π : Y → X} {y : Y}
  (K : CentreChart N E N' E' π y)
include K

theorem mem_flatDomain_Φ : π y ∈ flatDomain K.Φ := mem_flatDomain_self K.Φ
theorem mem_flatDomain_Θ : y ∈ flatDomain K.Θ := mem_flatDomain_self K.Θ

theorem flatCoord_Θ_self (l : Fin n) : flatCoord K.Θ l y = 0 := by
  show K.Θ.toFun (chartAt (ComplexModel n) y y) l = 0
  rw [K.Θ_zero]
  rfl

theorem tendsto_π : Tendsto π (𝓝 y) (𝓝 (π y)) := K.mdiff.self_of_nhds.continuousAt.tendsto

/-- `π` is eventually in the flat domain of `Φ`. -/
theorem eventually_flatDomain_Φ : ∀ᶠ u in 𝓝 y, π u ∈ flatDomain K.Φ :=
  K.tendsto_π.eventually ((isOpen_flatDomain K.Φ).mem_nhds K.mem_flatDomain_Φ)

theorem eventually_flatDomain_Θ : ∀ᶠ u in 𝓝 y, u ∈ flatDomain K.Θ :=
  (isOpen_flatDomain K.Θ).mem_nhds K.mem_flatDomain_Θ

theorem coord_eq_of_notMem {l : Fin n} (hl : l ∉ K.Q) : flatCoord K.Φ l ∘ π =ᶠ[𝓝 y] flatCoord K.Θ l := by
  filter_upwards [K.coord_eq l] with u hu
  rw [hu, if_neg hl]

/-- Near `y`, the strict carrier lies over the carrier. -/
theorem eventually_mem_N : ∀ᶠ u in 𝓝 y, u ∈ N' → π u ∈ N := by
  have hB : ∀ b ∈ K.B, flatCoord K.Φ b ∘ π =ᶠ[𝓝 y] flatCoord K.Θ b := fun b hb =>
    K.coord_eq_of_notMem fun hbQ => Finset.disjoint_left.mp K.disj (K.Q_bd hbQ) hb
  have hB' : ∀ᶠ u in 𝓝 y, ∀ b ∈ K.B, flatCoord K.Φ b (π u) = flatCoord K.Θ b u := by
    rw [Finset.eventually_all]
    intro b hb
    exact hB b hb
  filter_upwards [hB', K.eventually_flatDomain_Φ, K.eventually_flatDomain_Θ] with u hu hπu hΘu huN
  refine (K.N_flat hπu.1 hπu.2).mpr fun b hb => ?_
  have h1 := (K.N'_flat hΘu.1 hΘu.2).mp huN b hb
  have h2 := hu b hb
  change flatCoord K.Φ b (π u) = 0
  rw [h2]
  exact h1

/-- Germs vanishing on `N` pull back to germs vanishing on `N'`. -/
theorem comp_mem_vanishing {s : X → ℂ} (hs : (vanishingIdeal (n := n) N).mem (π y) s) :
    (vanishingIdeal (n := n) N').mem y (s ∘ π) := by
  refine ⟨holomorphicAt_comp_map K.mdiff hs.1, ?_⟩
  filter_upwards [K.tendsto_π.eventually hs.2, K.eventually_mem_N] with u hu hN huN
  exact hu (hN huN)

end CentreChart

/-! ### Elementary vanishing-ideal facts -/

section Vanishing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem mem_vanishing_of_eventuallyEq {H : Set M} {u : M} {g h : M → ℂ} (hgh : g =ᶠ[𝓝 u] h)
    (hh : (vanishingIdeal (n := n) H).mem u h) : (vanishingIdeal (n := n) H).mem u g :=
  ⟨hh.1.congr hgh.symm, by
    filter_upwards [hgh, hh.2] with q h1 h2 hq
    rw [h1]
    exact h2 hq⟩

theorem zero_mem_vanishing {H : Set M} {u : M} : (vanishingIdeal (n := n) H).mem u (fun _ => 0) :=
  ⟨holomorphicAt_const 0, Eventually.of_forall fun _ _ => rfl⟩

end Vanishing

section Coord

variable {y₀ : X} {Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}

/-- A holomorphic germ vanishing wherever a flat coordinate does lies in the vanishing ideal of the coordinate
hyperplane. -/
theorem mem_vanishing_of_coord (m : Fin n) {H : Set X}
    (hH : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ u ∈ Θ.source →
      (u ∈ H ↔ Θ.toFun (chartAt (ComplexModel n) y₀ u) ∈ coordSubspace {m}))
    {u : X} (hu : u ∈ flatDomain Θ) {F : X → ℂ} (hF : HolomorphicAt n F u)
    (hFz : ∀ q ∈ flatDomain Θ, flatCoord Θ m q = 0 → F q = 0) :
    (vanishingIdeal (n := n) H).mem u F :=
  ⟨hF, by
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds hu] with q hq hqH
    exact hFz q hq ((hH hq.1 hq.2).mp hqH m (Finset.mem_singleton_self m))⟩

end Coord

namespace CentreChart

variable {N : Set X} {E : List (Set X)} {N' : Set Y} {E' : List (Set Y)} {π : Y → X} {y : Y}
  (K : CentreChart N E N' E' π y)
include K

/-! ### Source fields -/

open Classical in
/-- The weight of a direction at `x = π y`: `ψ_m` for a boundary index, `1` otherwise. -/
def wX (m : Fin n) : X → ℂ := if m ∈ K.bd then flatCoord K.Φ m else fun _ => 1

/-- The source field `w_m ∂/∂ψ_m`. -/
def ξX (m : Fin n) : Fin n → X → ℂ :=
  combField K.Φ (fun r => if r = m then K.wX m else fun _ => 0)

theorem holomorphicAt_wX (m : Fin n) {q : X} (hq : q ∈ flatDomain K.Φ) : HolomorphicAt n (K.wX m) q := by
  unfold wX
  split_ifs
  · exact holomorphicAt_flatCoord K.Φ m hq
  · exact holomorphicAt_const 1

theorem holomorphicAt_ξX (m j : Fin n) : HolomorphicAt n (K.ξX m j) (π y) := by
  refine holomorphicAt_combField K.mem_flatDomain_Φ (fun r => ?_) j
  split_ifs
  · exact K.holomorphicAt_wX m K.mem_flatDomain_Φ
  · exact holomorphicAt_const 0

theorem fieldDeriv_ξX (m : Fin n) (f : X → ℂ) (q : X) :
    fieldDeriv (complexChartAt (n := n) (π y)) (K.ξX m) f q = K.wX m q * flatPartial K.Φ m f q := by
  rw [ξX, fieldDeriv_combField, Finset.sum_eq_single m]
  · simp
  · intro r _ hr
    simp [hr]
  · intro h
    exact absurd (Finset.mem_univ m) h

theorem fieldDeriv_ξX_flatCoord (m t : Fin n) {q : X} (hq : q ∈ flatDomain K.Φ) :
    fieldDeriv (complexChartAt (n := n) (π y)) (K.ξX m) (flatCoord K.Φ t) q =
      if t = m then K.wX m q else 0 := by
  rw [ξX, fieldDeriv_combField_flatCoord K.hΦsrc _ t hq]
  split_ifs <;> rfl

/-- **The source weighted coordinate fields are log tangent at `x`.** -/
theorem isLogTangentField_ξX {m : Fin n} (hm : m ∉ K.B) :
    IsLogTangentField N E (complexChartAt (n := n) (π y)) (K.ξX m) (π y) := by
  have hx : π y ∈ (complexChartAt (n := n) (π y)).val.source := mem_complexChartAt_source (π y)
  have hev : ∀ t, fieldDeriv (complexChartAt (n := n) (π y)) (K.ξX m) (flatCoord K.Φ t) =ᶠ[𝓝 (π y)]
      fun q => if t = m then K.wX m q else 0 := fun t => by
    filter_upwards [(isOpen_flatDomain K.Φ).mem_nhds K.mem_flatDomain_Φ] with q hq
    exact K.fieldDeriv_ξX_flatCoord m t hq
  refine ⟨isTangentField_of_coordinate K.hΦsrc K.B K.N_flat K.mem_flatDomain_Φ hx (K.holomorphicAt_ξX m)
    fun t ht => ?_, fun H hH => ?_⟩
  · have htm : t ≠ m := fun h => hm (h ▸ ht)
    refine mem_vanishing_of_eventuallyEq (hev t) ?_
    simp only [htm, if_false]
    exact zero_mem_vanishing
  · rcases K.E_flat H hH with hout | ⟨m', hm', hflat⟩
    · exact isTangentField_of_eventually_notMem hx (K.holomorphicAt_ξX m) hout
    · refine isTangentField_of_coordinate K.hΦsrc {m'} hflat K.mem_flatDomain_Φ hx (K.holomorphicAt_ξX m)
        fun t ht => ?_
      rw [Finset.mem_singleton] at ht
      subst ht
      refine mem_vanishing_of_eventuallyEq (hev t) ?_
      by_cases htm : t = m
      · subst htm
        simp only [if_true, wX, hm', if_true]
        exact mem_vanishing_of_coord t hflat K.mem_flatDomain_Φ (holomorphicAt_flatCoord K.Φ t K.mem_flatDomain_Φ)
          fun _ _ h => h
      · simp only [htm, if_false]
        exact zero_mem_vanishing

/-- `w_m ∂f/∂ψ_m` lies in the source log operator for `f ∈ A`. -/
theorem weighted_mem {A : GermIdeal n X} {m : Fin n} (hm : m ∉ K.B) {f : X → ℂ} (hf : A.mem (π y) f)
    (hfh : HolomorphicAt n f (π y)) :
    (logDerivIdealAlong N E A).mem (π y) (fun q => K.wX m q * flatPartial K.Φ m f q) := by
  have hx : π y ∈ (complexChartAt (n := n) (π y)).val.source := mem_complexChartAt_source (π y)
  have hgen : LogGen N E A (π y) (fieldDeriv (complexChartAt (n := n) (π y)) (K.ξX m) f) :=
    Or.inr (Or.inr ⟨_, _, f, K.isLogTangentField_ξX hm, hf, rfl⟩)
  have h := InvertibleIdealQuotient.isInSpanAt_self hgen
    (holomorphicAt_fieldDeriv hx (K.holomorphicAt_ξX m) hfh)
  have heq : fieldDeriv (complexChartAt (n := n) (π y)) (K.ξX m) f =
      fun q => K.wX m q * flatPartial K.Φ m f q := funext fun q => K.fieldDeriv_ξX m f q
  rw [heq] at h
  exact mem_logDerivIdealAlong_iff.mpr h

end CentreChart

namespace CentreChart

variable {N : Set X} {E : List (Set X)} {N' : Set Y} {E' : List (Set Y)} {π : Y → X} {y : Y}
  (K : CentreChart N E N' E' π y)
include K

/-! ### Target fields -/

open Classical in
/-- The coefficients of the lifted target fields: `ζ_p ∂_p - ∑_{q∈Q} (ζ_q + v_q) ∂_q` for the pivot,
`(ζ_q + v_q) ∂_q` for `q ∈ Q`, `ζ_m ∂_m` for another boundary index and `∂_m` otherwise. -/
def aY (m r : Fin n) : Y → ℂ :=
  if m = K.p then
    (if r = K.p then flatCoord K.Θ K.p else if r ∈ K.Q then fun u => -(flatCoord K.Θ r u + K.v r)
      else fun _ => 0)
  else if r = m then
    (if m ∈ K.Q then fun u => flatCoord K.Θ m u + K.v m else if m ∈ K.bd then flatCoord K.Θ m
      else fun _ => 1)
  else fun _ => 0

/-- The lifted target field. -/
def ξY (m : Fin n) : Fin n → Y → ℂ := combField K.Θ (K.aY m)

theorem holomorphicAt_aY (m r : Fin n) : HolomorphicAt n (K.aY m r) y := by
  have hz : ∀ l, HolomorphicAt n (flatCoord K.Θ l) y := fun l =>
    holomorphicAt_flatCoord K.Θ l K.mem_flatDomain_Θ
  unfold aY
  split_ifs
  · exact hz _
  · exact ((holomorphicAt_const (-1 : ℂ)).mul ((hz r).add (holomorphicAt_const (K.v r)))).congr
      (Eventually.of_forall fun u => by ring)
  · exact holomorphicAt_const 0
  · exact (hz m).add (holomorphicAt_const _)
  · exact hz m
  · exact holomorphicAt_const 1
  · exact holomorphicAt_const 0

theorem holomorphicAt_ξY (m j : Fin n) : HolomorphicAt n (K.ξY m j) y :=
  holomorphicAt_combField K.mem_flatDomain_Θ (K.holomorphicAt_aY m) j

theorem fieldDeriv_ξY_flatCoord (m r : Fin n) {u : Y} (hu : u ∈ flatDomain K.Θ) :
    fieldDeriv (complexChartAt (n := n) y) (K.ξY m) (flatCoord K.Θ r) u = K.aY m r u :=
  fieldDeriv_combField_flatCoord K.hΘsrc _ r hu

theorem eventually_fieldDeriv_ξY_flatCoord (m r : Fin n) :
    fieldDeriv (complexChartAt (n := n) y) (K.ξY m) (flatCoord K.Θ r) =ᶠ[𝓝 y] K.aY m r := by
  filter_upwards [K.eventually_flatDomain_Θ] with u hu
  exact K.fieldDeriv_ξY_flatCoord m r hu

theorem aY_p_p : K.aY K.p K.p = flatCoord K.Θ K.p := by simp [aY]

theorem aY_p_Q {r : Fin n} (hr : r ∈ K.Q) :
    K.aY K.p r = fun u => -(flatCoord K.Θ r u + K.v r) := by
  have hrp : r ≠ K.p := fun h => K.p_Q (h ▸ hr)
  simp [aY, hrp, hr]

theorem aY_p_other {r : Fin n} (hrp : r ≠ K.p) (hr : r ∉ K.Q) : K.aY K.p r = fun _ => 0 := by
  simp [aY, hrp, hr]

theorem aY_m_m {m : Fin n} (hmp : m ≠ K.p) :
    K.aY m m = if m ∈ K.Q then fun u => flatCoord K.Θ m u + K.v m else
      if m ∈ K.bd then flatCoord K.Θ m else fun _ => 1 := by
  simp [aY, hmp]

theorem aY_m_other {m r : Fin n} (hmp : m ≠ K.p) (hrm : r ≠ m) : K.aY m r = fun _ => 0 := by
  simp [aY, hmp, hrm]

/-- The value of `w_m` along `π`, in target coordinates. -/
theorem eventually_wX_comp (m : Fin n) : ∀ᶠ u in 𝓝 y, m ∈ K.bd →
    K.wX m (π u) = if m ∈ K.Q then flatCoord K.Θ K.p u * (flatCoord K.Θ m u + K.v m)
      else flatCoord K.Θ m u := by
  filter_upwards [K.coord_eq m] with u hu hm
  simp only [wX, hm, if_true]
  exact hu

/-- **The lifted field computes the weighted source derivative on every source coordinate.** -/
theorem eventually_fieldDeriv_ξY_coord (m l : Fin n) :
    fieldDeriv (complexChartAt (n := n) y) (K.ξY m) (flatCoord K.Φ l ∘ π) =ᶠ[𝓝 y]
      fun u => if l = m then K.wX m (π u) else 0 := by
  classical
  have hy : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
  have hcongr := DerivativeIdealAlongEtale.fieldDeriv_congr (ξ := K.ξY m) hy (K.coord_eq l)
  have hz : ∀ l, HolomorphicAt n (flatCoord K.Θ l) y := fun l =>
    holomorphicAt_flatCoord K.Θ l K.mem_flatDomain_Θ
  have hpQ := K.p_Q
  by_cases hlQ : l ∈ K.Q
  · simp only [hlQ, if_true] at hcongr
    have hprod := fieldDeriv_mul_eventuallyEq (ξ := K.ξY m) hy (hz K.p)
      ((hz l).add (holomorphicAt_const (K.v l)))
    filter_upwards [hcongr, hprod, K.eventually_flatDomain_Θ, K.eventually_wX_comp m] with u h1 h2 hu hw
    rw [h1, h2, fieldDeriv_add_const, K.fieldDeriv_ξY_flatCoord m K.p hu,
      K.fieldDeriv_ξY_flatCoord m l hu]
    have hlp : l ≠ K.p := fun h => hpQ (h ▸ hlQ)
    by_cases hmp : m = K.p
    · have hlm : l ≠ m := fun h => hlp (h.trans hmp)
      rw [if_neg hlm, hmp, K.aY_p_p, K.aY_p_Q hlQ]
      ring
    · have hpm : K.p ≠ m := fun h => hmp h.symm
      rw [K.aY_m_other hmp hpm]
      by_cases hlm : l = m
      · have hmQ : m ∈ K.Q := hlm ▸ hlQ
        rw [if_pos hlm, hlm, K.aY_m_m hmp, if_pos hmQ, hw (K.Q_bd hmQ), if_pos hmQ]
        ring
      · rw [if_neg hlm, K.aY_m_other hmp hlm]
        ring
  · simp only [hlQ, if_false] at hcongr
    filter_upwards [hcongr, K.eventually_flatDomain_Θ, K.eventually_wX_comp m] with u h1 hu hw
    rw [h1, K.fieldDeriv_ξY_flatCoord m l hu]
    by_cases hmp : m = K.p
    · by_cases hlm : l = m
      · have hlp : l = K.p := hlm.trans hmp
        have hw' := hw (hmp ▸ K.p_bd)
        rw [hmp] at hw'
        rw [if_pos hlm, hlp, hmp, K.aY_p_p, hw', if_neg K.p_Q]
      · have hlp : l ≠ K.p := fun h => hlm (h.trans hmp.symm)
        rw [if_neg hlm, hmp, K.aY_p_other hlp hlQ]
    · by_cases hlm : l = m
      · have hmQ : m ∉ K.Q := hlm ▸ hlQ
        rw [if_pos hlm, hlm, K.aY_m_m hmp, if_neg hmQ]
        by_cases hmbd : m ∈ K.bd
        · rw [if_pos hmbd, hw hmbd, if_neg hmQ]
        · rw [if_neg hmbd]
          simp [wX, hmbd]
      · rw [if_neg hlm, K.aY_m_other hmp hlm]

/-- **The lifted target fields are log tangent at `y`.** -/
theorem isLogTangentField_ξY {m : Fin n} (hm : m ∉ K.B) :
    IsLogTangentField N' E' (complexChartAt (n := n) y) (K.ξY m) y := by
  classical
  have hy : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
  have hpB : K.p ∉ K.B := fun h => Finset.disjoint_left.mp K.disj K.p_bd h
  refine ⟨isTangentField_of_coordinate K.hΘsrc K.B K.N'_flat K.mem_flatDomain_Θ hy (K.holomorphicAt_ξY m)
    fun t ht => ?_, fun H' hH' => ?_⟩
  · refine mem_vanishing_of_eventuallyEq (K.eventually_fieldDeriv_ξY_flatCoord m t) ?_
    have htp : t ≠ K.p := fun h => hpB (h ▸ ht)
    have htQ : t ∉ K.Q := fun h => Finset.disjoint_left.mp K.disj (K.Q_bd h) ht
    have htm : t ≠ m := fun h => hm (h ▸ ht)
    by_cases hmp : m = K.p
    · rw [hmp, K.aY_p_other htp htQ]
      exact zero_mem_vanishing
    · rw [K.aY_m_other hmp htm]
      exact zero_mem_vanishing
  · rcases K.E'_flat H' hH' with hout | ⟨m', hm', hv, hflat⟩
    · exact isTangentField_of_eventually_notMem hy (K.holomorphicAt_ξY m) hout
    · refine isTangentField_of_coordinate K.hΘsrc {m'} hflat K.mem_flatDomain_Θ hy (K.holomorphicAt_ξY m)
        fun t ht => ?_
      rw [Finset.mem_singleton] at ht
      subst ht
      refine mem_vanishing_of_eventuallyEq (K.eventually_fieldDeriv_ξY_flatCoord m t) ?_
      refine mem_vanishing_of_coord t hflat K.mem_flatDomain_Θ (K.holomorphicAt_aY m t) fun q _ hq => ?_
      by_cases hmp : m = K.p
      · rw [hmp]
        by_cases htp : t = K.p
        · rw [htp, K.aY_p_p]
          rw [htp] at hq
          exact hq
        · by_cases htQ : t ∈ K.Q
          · rw [K.aY_p_Q htQ]
            simp [hq, hv]
          · rw [K.aY_p_other htp htQ]
      · by_cases htm : t = m
        · rw [htm, K.aY_m_m hmp]
          rw [htm] at hq hv hm'
          by_cases hmQ : m ∈ K.Q
          · rw [if_pos hmQ]
            simp [hq, hv]
          · rw [if_neg hmQ, if_pos hm']
            exact hq
        · rw [K.aY_m_other hmp htm]

/-- **Lemma T**: `(w_m ∂f/∂ψ_m) ∘ π` lies in the target log operator. -/
theorem weighted_comp_mem {A : GermIdeal n X} {m : Fin n} (hm : m ∉ K.B) {f : X → ℂ}
    (hf : A.mem (π y) f) (hfh : HolomorphicAt n f (π y)) :
    (logDerivIdealAlong N' E' (GermIdeal.pullback (m := n) π A)).mem y
      ((fun q => K.wX m q * flatPartial K.Φ m f q) ∘ π) := by
  classical
  have hy : y ∈ (complexChartAt (n := n) y).val.source := mem_complexChartAt_source y
  have hgen : LogGen N' E' (GermIdeal.pullback (m := n) π A) y
      (fieldDeriv (complexChartAt (n := n) y) (K.ξY m) (f ∘ π)) :=
    Or.inr (Or.inr ⟨_, _, f ∘ π, K.isLogTangentField_ξY hm, comp_mem_pullback K.mdiff hf hfh, rfl⟩)
  have hhol := holomorphicAt_fieldDeriv hy (K.holomorphicAt_ξY m) (holomorphicAt_comp_map K.mdiff hfh)
  have hCR := fieldDeriv_comp_eventuallyEq_sum_flatPartial K.hΦsrc K.mdiff K.mem_flatDomain_Φ
    (complexChartAt (n := n) y) hy (K.ξY m) hfh
  have heq : fieldDeriv (complexChartAt (n := n) y) (K.ξY m) (f ∘ π) =ᶠ[𝓝 y]
      (fun q => K.wX m q * flatPartial K.Φ m f q) ∘ π := by
    filter_upwards [hCR, eventually_all.2 (K.eventually_fieldDeriv_ξY_coord m)] with u h1 h2
    rw [h1]
    simp only [h2, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply]
  exact mem_logDerivIdealAlong_iff.mpr
    (DerivativeIdeal.isInSpanAt_congr (InvertibleIdealQuotient.isInSpanAt_self hgen hhol) heq)

end CentreChart

namespace CentreChart

variable {N : Set X} {E : List (Set X)} {N' : Set Y} {E' : List (Set Y)} {π : Y → X} {y : Y}
  (K : CentreChart N E N' E' π y)
include K

/-! ### The two inclusions -/

theorem flatCoord_mem_N {m : Fin n} (hm : m ∈ K.B) :
    (vanishingIdeal (n := n) N).mem (π y) (flatCoord K.Φ m) :=
  ⟨holomorphicAt_flatCoord K.Φ m K.mem_flatDomain_Φ, by
    filter_upwards [(isOpen_flatDomain K.Φ).mem_nhds K.mem_flatDomain_Φ] with q hq hqN
    exact (K.N_flat hq.1 hq.2).mp hqN m hm⟩

theorem flatCoord_mem_N' {m : Fin n} (hm : m ∈ K.B) :
    (vanishingIdeal (n := n) N').mem y (flatCoord K.Θ m) :=
  ⟨holomorphicAt_flatCoord K.Θ m K.mem_flatDomain_Θ, by
    filter_upwards [K.eventually_flatDomain_Θ] with q hq hqN
    exact (K.N'_flat hq.1 hq.2).mp hqN m hm⟩

theorem notMem_Q_of_mem_B {m : Fin n} (hm : m ∈ K.B) : m ∉ K.Q := fun h =>
  Finset.disjoint_left.mp K.disj (K.Q_bd h) hm

/-- Every source log field maps `ψ_m` to a multiple of the weight `w_m`. -/
theorem exists_source_factor {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsLogTangentField N E e ξ (π y)) (m : Fin n) :
    ∃ d : X → ℂ, HolomorphicAt n d (π y) ∧
      fieldDeriv e ξ (flatCoord K.Φ m) =ᶠ[𝓝 (π y)] fun q => d q * K.wX m q := by
  by_cases hm : m ∈ K.bd
  · obtain ⟨H, hH, hflat⟩ := K.bd_flat m hm
    have hmem : (vanishingIdeal (n := n) H).mem (π y) (flatCoord K.Φ m) :=
      mem_vanishing_of_coord m hflat K.mem_flatDomain_Φ (holomorphicAt_flatCoord K.Φ m K.mem_flatDomain_Φ)
        fun _ _ h => h
    obtain ⟨d, hd, hdeq⟩ := exists_eq_mul_flatCoord K.hΦsrc m hflat K.mem_flatDomain_Φ
      ((hξ.2 H hH).preserves _ hmem)
    refine ⟨d, hd, ?_⟩
    simpa only [wX, hm, if_true] using hdeq
  · refine ⟨fieldDeriv e ξ (flatCoord K.Φ m),
      holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt
        (holomorphicAt_flatCoord K.Φ m K.mem_flatDomain_Φ), Eventually.of_forall fun q => ?_⟩
    simp [wX, hm]

/-- **`π^* 𝓓_{N,E}(A) ⊆ 𝓓_{N',E'}(π^*A)` at `y`.** -/
theorem comp_mem {A : GermIdeal n X} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) {a : X → ℂ}
    (ha : (logDerivIdealAlong N E A).mem (π y) a) :
    (logDerivIdealAlong N' E' (GermIdeal.pullback (m := n) π A)).mem y (a ∘ π) := by
  obtain ⟨-, K', t, c, ht, hc, hsum⟩ := mem_logDerivIdealAlong_iff.mp ha
  have hcomp : (a ∘ π) =ᶠ[𝓝 y] fun u => ∑ k, (c k ∘ π) u * (t k ∘ π) u :=
    K.tendsto_π.eventually hsum
  refine mem_logDerivIdealAlong_iff.mpr (DerivativeIdeal.isInSpanAt_congr ?_ hcomp.symm)
  refine IsInSpanAt.sum Finset.univ fun k _ =>
    IsInSpanAt.mul_left (holomorphicAt_comp_map K.mdiff (hc k)) ?_
  refine mem_logDerivIdealAlong_iff.mp ?_
  rcases ht k with htk | htk | ⟨e, ξ, f, hξ, hf, htk⟩
  · exact mem_logDerivIdealAlong_of_mem (comp_mem_pullback K.mdiff htk (hA _ _ htk))
      (holomorphicAt_comp_map K.mdiff (hA _ _ htk))
  · exact mem_logDerivIdealAlong_of_vanishing (K.comp_mem_vanishing htk)
  · have hfh := hA _ _ hf
    have hexp := fieldDeriv_eventuallyEq_sum_flatPartial K.hΦsrc e ξ hξ.1.mem_source K.mem_flatDomain_Φ hfh
    have hexp' : t k ∘ π =ᶠ[𝓝 y] fun u =>
        ∑ m, flatPartial K.Φ m f (π u) * fieldDeriv e ξ (flatCoord K.Φ m) (π u) := by
      filter_upwards [K.tendsto_π.eventually hexp] with u hu
      rw [Function.comp_apply, htk, hu]
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    refine mem_logDerivIdealAlong_iff.mpr (DerivativeIdeal.isInSpanAt_congr ?_ hexp'.symm)
    refine IsInSpanAt.sum Finset.univ fun m _ => ?_
    by_cases hmB : m ∈ K.B
    · refine IsInSpanAt.mul_left
        (holomorphicAt_comp_map (f := flatPartial K.Φ m f) K.mdiff
          (holomorphicAt_flatPartial m K.mem_flatDomain_Φ hfh)) ?_
      have hv := K.comp_mem_vanishing (hξ.1.preserves _ (K.flatCoord_mem_N hmB))
      exact mem_logDerivIdealAlong_iff.mp (mem_logDerivIdealAlong_of_vanishing hv)
    · obtain ⟨d, hd, hdeq⟩ := K.exists_source_factor hξ m
      have hT := mem_logDerivIdealAlong_iff.mp (K.weighted_comp_mem hmB hf hfh)
      have h2 := IsInSpanAt.mul_left (holomorphicAt_comp_map K.mdiff hd) hT
      refine DerivativeIdeal.isInSpanAt_congr h2 ?_
      filter_upwards [K.tendsto_π.eventually hdeq] with u hu
      simp only [Function.comp_apply]
      rw [hu]
      ring

/-- Germs vanishing on `N'` lie in the pullback of the source log operator. -/
theorem vanishing_mem_pullback {A : GermIdeal n X} {s : Y → ℂ} (hs : (vanishingIdeal (n := n) N').mem y s) :
    IsInSpanAt (n := n) (fun t => ∃ a, (logDerivIdealAlong N E A).mem (π y) a ∧ t = a ∘ π) y s := by
  classical
  refine IsInSpanAt.trans ?_
    ((mem_vanishingIdeal_iff_coordinate_span K.Θ K.hΘsrc K.B N' K.N'_flat K.mem_flatDomain_Θ s).mp hs)
  rintro t ⟨a, rfl⟩
  by_cases ha : a ∈ K.B
  · simp only [ha, if_true]
    have hD : (logDerivIdealAlong N E A).mem (π y) (flatCoord K.Φ a) :=
      mem_logDerivIdealAlong_of_vanishing (K.flatCoord_mem_N ha)
    exact DerivativeIdeal.isInSpanAt_congr (comp_mem_pullback K.mdiff hD hD.1)
      (K.coord_eq_of_notMem (K.notMem_Q_of_mem_B ha))
  · simp only [ha, if_false]
    exact isInSpanAt_zero

/-- Every target log field maps `ψ_m ∘ π` (`m ∉ B`) to a multiple of `w_m ∘ π`. -/
theorem exists_target_factor {e' : ComplexChart n Y} {ξ' : Fin n → Y → ℂ}
    (hξ' : IsLogTangentField N' E' e' ξ' y) (m : Fin n) :
    ∃ d : Y → ℂ, HolomorphicAt n d y ∧
      fieldDeriv e' ξ' (flatCoord K.Φ m ∘ π) =ᶠ[𝓝 y] fun u => d u * K.wX m (π u) := by
  classical
  have hy := hξ'.1.mem_source
  have hz : ∀ l, HolomorphicAt n (flatCoord K.Θ l) y := fun l =>
    holomorphicAt_flatCoord K.Θ l K.mem_flatDomain_Θ
  -- division in a target coordinate hyperplane of `E'`
  have hdiv : ∀ l ∈ K.bd, K.v l = 0 → ∃ d : Y → ℂ, HolomorphicAt n d y ∧
      fieldDeriv e' ξ' (flatCoord K.Θ l) =ᶠ[𝓝 y] fun u => d u * flatCoord K.Θ l u := by
    intro l hl hv
    obtain ⟨H', hH', hflat⟩ := K.bd'_flat l hl hv
    have hmem : (vanishingIdeal (n := n) H').mem y (flatCoord K.Θ l) :=
      mem_vanishing_of_coord l hflat K.mem_flatDomain_Θ (hz l) fun _ _ h => h
    exact exists_eq_mul_flatCoord K.hΘsrc l hflat K.mem_flatDomain_Θ ((hξ'.2 H' hH').preserves _ hmem)
  by_cases hm : m ∈ K.bd
  · by_cases hmQ : m ∈ K.Q
    · -- `ψ_m ∘ π = ζ_p (ζ_m + v_m)`
      obtain ⟨dp, hdp, hdpeq⟩ := hdiv K.p K.p_bd (K.v_zero _ K.p_Q)
      have hcongr := DerivativeIdealAlongEtale.fieldDeriv_congr (ξ := ξ') hy (K.coord_eq m)
      simp only [hmQ, if_true] at hcongr
      have hprod := fieldDeriv_mul_eventuallyEq (ξ := ξ') hy (hz K.p) ((hz m).add (holomorphicAt_const (K.v m)))
      by_cases hv : K.v m = 0
      · obtain ⟨dm, hdm, hdmeq⟩ := hdiv m hm hv
        refine ⟨fun u => dp u + dm u, hdp.add hdm, ?_⟩
        filter_upwards [hcongr, hprod, hdpeq, hdmeq, K.eventually_wX_comp m] with u h1 h2 h3 h4 hw
        rw [h1, h2, fieldDeriv_add_const, h3, h4, hw hm]
        simp only [hmQ, if_true, hv, add_zero]
        ring
      · have hne : flatCoord K.Θ m y + K.v m ≠ 0 := by rw [K.flatCoord_Θ_self, zero_add]; exact hv
        have hinv := BlowupFlatCoordinates.HolomorphicAt.inv ((hz m).add (holomorphicAt_const (K.v m))) hne
        have hd' : HolomorphicAt n (fieldDeriv e' ξ' (flatCoord K.Θ m)) y :=
          holomorphicAt_fieldDeriv hy hξ'.1.holomorphicAt (hz m)
        refine ⟨fun u => dp u + fieldDeriv e' ξ' (flatCoord K.Θ m) u * (flatCoord K.Θ m u + K.v m)⁻¹,
          hdp.add (hd'.mul hinv), ?_⟩
        have hnear : ∀ᶠ u in 𝓝 y, flatCoord K.Θ m u + K.v m ≠ 0 :=
          ((hz m).add (holomorphicAt_const (K.v m))).continuousAt.eventually_ne hne
        filter_upwards [hcongr, hprod, hdpeq, K.eventually_wX_comp m, hnear] with u h1 h2 h3 hw hu0
        rw [h1, h2, fieldDeriv_add_const, h3, hw hm]
        simp only [hmQ, if_true]
        field_simp
    · obtain ⟨d, hd, hdeq⟩ := hdiv m hm (K.v_zero m hmQ)
      refine ⟨d, hd, ?_⟩
      have hcongr := DerivativeIdealAlongEtale.fieldDeriv_congr (ξ := ξ') hy (K.coord_eq_of_notMem hmQ)
      filter_upwards [hcongr, hdeq, K.eventually_wX_comp m] with u h1 h2 hw
      rw [h1, h2, hw hm]
      simp only [hmQ, if_false]
  · refine ⟨fieldDeriv e' ξ' (flatCoord K.Φ m ∘ π),
      holomorphicAt_fieldDeriv hy hξ'.1.holomorphicAt
        (holomorphicAt_comp_map K.mdiff (holomorphicAt_flatCoord K.Φ m K.mem_flatDomain_Φ)),
      Eventually.of_forall fun u => ?_⟩
    simp [wX, hm]

/-- A target log field applied to a pulled-back germ of `A` lies in the pullback of the source log operator. -/
theorem fieldDeriv_comp_mem {A : GermIdeal n X} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x)
    {e' : ComplexChart n Y} {ξ' : Fin n → Y → ℂ} (hξ' : IsLogTangentField N' E' e' ξ' y) {b : X → ℂ}
    (hb : A.mem (π y) b) :
    IsInSpanAt (n := n) (fun t => ∃ a, (logDerivIdealAlong N E A).mem (π y) a ∧ t = a ∘ π) y
      (fieldDeriv e' ξ' (b ∘ π)) := by
  have hbh := hA _ _ hb
  have hy := hξ'.1.mem_source
  have hCR := fieldDeriv_comp_eventuallyEq_sum_flatPartial K.hΦsrc K.mdiff K.mem_flatDomain_Φ e' hy ξ' hbh
  refine DerivativeIdeal.isInSpanAt_congr ?_ hCR.symm
  refine IsInSpanAt.sum Finset.univ fun m _ => ?_
  have hpartial : HolomorphicAt n (flatPartial K.Φ m b ∘ π) y :=
    holomorphicAt_comp_map K.mdiff (holomorphicAt_flatPartial m K.mem_flatDomain_Φ hbh)
  by_cases hmB : m ∈ K.B
  · have hv : (vanishingIdeal (n := n) N').mem y (flatCoord K.Φ m ∘ π) :=
      mem_vanishing_of_eventuallyEq (K.coord_eq_of_notMem (K.notMem_Q_of_mem_B hmB)) (K.flatCoord_mem_N' hmB)
    have h1 := IsInSpanAt.mul_left hpartial (K.vanishing_mem_pullback (A := A) (hξ'.1.preserves _ hv))
    refine DerivativeIdeal.isInSpanAt_congr h1 (Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply]
    ring
  · obtain ⟨d, hd, hdeq⟩ := K.exists_target_factor hξ' m
    have hW := K.weighted_mem hmB hb hbh
    have h1 := IsInSpanAt.mul_left hd (GermIdeal.mem_pullback_iff.mp (comp_mem_pullback K.mdiff hW hW.1))
    refine DerivativeIdeal.isInSpanAt_congr h1 ?_
    filter_upwards [hdeq] with u hu
    simp only [Function.comp_apply]
    rw [hu]
    ring

/-- **`𝓓_{N',E'}(π^*A) ⊆ π^* 𝓓_{N,E}(A)` at `y`.** -/
theorem mem_pullback {A : GermIdeal n X} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) {g : Y → ℂ}
    (hg : (logDerivIdealAlong N' E' (GermIdeal.pullback (m := n) π A)).mem y g) :
    (GermIdeal.pullback (m := n) π (logDerivIdealAlong N E A)).mem y g := by
  have hpb : ∀ {b : X → ℂ}, (logDerivIdealAlong N E A).mem (π y) b →
      IsInSpanAt (n := n) (fun t => ∃ a, (logDerivIdealAlong N E A).mem (π y) a ∧ t = a ∘ π) y (b ∘ π) :=
    fun {b} hb => comp_mem_pullback K.mdiff hb hb.1
  refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (mem_logDerivIdealAlong_iff.mp hg))
  rintro t (ht | ht | ⟨e', ξ', f', hξ', hf', rfl⟩)
  · exact (GermIdeal.mem_pullback_iff.mp ht).mono fun s ⟨a, ha, hs⟩ =>
      ⟨a, mem_logDerivIdealAlong_of_mem ha (hA _ _ ha), hs⟩
  · exact K.vanishing_mem_pullback ht
  · obtain ⟨-, K', s, c, hs, hc, hsum⟩ := GermIdeal.mem_pullback_iff.mp hf'
    choose b hb hsb using hs
    have hbhol : ∀ k, HolomorphicAt n (b k) (π y) := fun k => hA _ _ (hb k)
    have hsφ : ∀ k, HolomorphicAt n (s k) y := fun k =>
      hsb k ▸ holomorphicAt_comp_map K.mdiff (hbhol k)
    have hprod := fieldDeriv_eventuallyEq_sum_mul (ξ := ξ') hξ'.1.mem_source hc hsφ hsum
    refine DerivativeIdeal.isInSpanAt_congr ?_ hprod.symm
    refine IsInSpanAt.sum Finset.univ fun k _ => IsInSpanAt.add ?_ ?_
    · refine IsInSpanAt.mul_left
        (holomorphicAt_fieldDeriv hξ'.1.mem_source hξ'.1.holomorphicAt (hc k)) ?_
      rw [hsb k]
      exact hpb (mem_logDerivIdealAlong_of_mem (hb k) (hbhol k))
    · refine IsInSpanAt.mul_left (hc k) ?_
      rw [hsb k]
      exact K.fieldDeriv_comp_mem hA hξ' (hb k)

/-- **The ordinary exceptional log equality at a centre point**, from a centre chart. -/
theorem log_mem_iff {A : GermIdeal n X} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (logDerivIdealAlong N E A)).mem y g ↔
      (logDerivIdealAlong N' E' (GermIdeal.pullback (m := n) π A)).mem y g := by
  constructor
  · intro hg
    refine mem_logDerivIdealAlong_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro t ⟨a, ha, rfl⟩
    exact mem_logDerivIdealAlong_iff.mp (K.comp_mem hA ha)
  · exact K.mem_pullback hA

end CentreChart

end

end Hironaka.HironakaG8ExceptionalLogCentre

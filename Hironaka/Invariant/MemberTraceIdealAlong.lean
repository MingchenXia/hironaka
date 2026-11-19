import Hironaka.Blowup.ExceptionalPushforwardAlong
import Hironaka.Invariant.NonmonomialTransformTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ideal of the trace of a member on a submanifold, and `𝓘_{D ∩ N'} ⊆ 𝒪(-D) + 𝓘_{N'}`

Hironaka phase H2 (TN3), for TN-CLASSICAL's monomial / nonmonomial cases along a submanifold
`N ≠ M` (claim I-0977 C-0090).  Blueprint `bcalc:member-retraction`,
`bcalc:member-trace-ideal`, `bcalc:exceptional-trace-ideal` (chapter `blowup-calculus.tex`).
Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`) §2.1 (marked ideals `(M, N, E, 𝓘, μ)`, `E`
transverse to `N`); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`) §2 (the ideals of
`E|_N`).

Let `E` be a simple normal crossings divisor transverse to `N` (`IsTransverse`), `x ∈ N`, and
`H = E_i` a member.

* `exists_memberRetraction`: a holomorphic retraction `ρ` of a neighbourhood of `x` onto `N`
  (`ρ x = x`, values in `N`, `ρ = id` on `N`) mapping every member of `E` into itself near `x`.  In
  simultaneous coordinates (`SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings` with
  `C = N`: `N = ℂ^k × 0`, the members through `x` the hyperplanes `{w_{s i} = 0}` with `s i < k`)
  it is the flat retraction `φ ∘ P ∘ ψ` (`P` = `planeRetract k`), which keeps the coordinates
  `w_{s i}`; in dimension `0`, `N` is a neighbourhood of `x` and `ρ = id`.
* `isInSpanOnAt_idealPow_vanishingIdeal_iff`: `(𝓘_H^K)|_N = (𝓘_{N ∩ H}^K)|_N` at `x`, i.e. a
  function agrees on `N` near `x` with a combination of germs of `𝓘_H^K` iff it does with germs of
  `𝓘_{N ∩ H}^K` (one direction since `𝓘_H ⊆ 𝓘_{N ∩ H}`, the other through `s ↦ s ∘ ρ`, which maps
  `𝓘_{N ∩ H}` into `𝓘_H` and does not change `s` on `N`); `isInSpanOnAt_vanishingIdeal_iff` the
  same for `K = 1`; `isInSpanOnAt_vanishingIdeal_iff_mem` for a holomorphic germ: it lies in
  `𝓘_H + 𝓘_N` iff it vanishes on `N ∩ H` near `x`.  The forms `_of_isWellFormed` read them for a
  well-formed marked ideal `(M, N, E, 𝔞, d)` (every stage of a multiple test blow-up).
* The restricted helper (I-0977 C-0082, the along-`N'` form of TN-CLASSICAL's
  `NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem`): for the blowup `π`
  along `C ⊆ N`, `N` a closed submanifold, `N' = geoStrictTransform π C N` and `z ∈ N'` over `C`,
  `isInSpanOnAt_exceptionalDivisor_of_mem_vanishingIdeal`: a germ vanishing on `N' ∩ D`,
  `D = π⁻¹ C`, agrees on `N'` near `z` with a germ of `𝒪(-D)` (`𝓘_{D ∩ N'} ⊆ 𝒪(-D) + 𝓘_{N'}`);
  `isInSpanOnAt_exceptionalDivisor_iff_mem` the converse for a holomorphic germ; and
  `isInSpanOnAt_idealPow_exceptionalDivisor_iff`: `𝒪(-KD)|_{N'} = (𝓘_{N' ∩ D}^K)|_{N'}` at `z`.
  Route: `[π⁻¹ C]` is simple normal crossings and transverse to `N'`
  (`BlowupSNCTransform.isSNCDivisor_preimage_centre`, `isTransverse_preimage_centre`), and
  `𝒪(-D) = 𝓘_{π⁻¹ C}` at `z` (`BlowupStrictIdeal.pullback_vanishingIdeal_le` and TN-CLASSICAL's
  helper with `E = []`, imported, nothing edited).
* tools: `comp_mem_idealPow_of_comp_mem` (powers pass under a holomorphic map fixing the point that
  maps one ideal into another), `mem_idealPow_of_forall_mem` (powers are monotone in the stalk),
  `comp_mem_vanishingIdeal`, `isInSpanOnAt_of_retraction`, `mem_vanishingIdeal_of_isInSpanOnAt`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberTraceIdealAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
open Hironaka.BlowupFlatCoordinates
open Hironaka.BlowupExceptionalDivisor
open Hironaka.BlowupStrictSubmanifold
open Hironaka.BlowupSNCTransform
open Hironaka.NormalCrossings
open Hironaka.HadamardBridgeAlong
open Hironaka.GiraudAlong
open Hironaka.RelativePrincipalizationSpan
open Hironaka.MarkedIdeals

noncomputable section

variable {n : ℕ}

/-! ### Tools: powers, vanishing ideals and restricted spans under a map -/

section Tools

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Powers pass under a holomorphic map fixing the point** that maps one ideal into another: if
`ρ z = z`, `ρ` is holomorphic near `z` and `q ∘ ρ ∈ 𝔩'` at `z` for every `q ∈ 𝔩` at `z`, then
`g ∘ ρ ∈ 𝔩'^K` at `z` for every `g ∈ 𝔩^K` at `z`. -/
theorem comp_mem_idealPow_of_comp_mem {𝔩 𝔩' : GermIdeal n M} {ρ : M → M} {z : M} (hρz : ρ z = z)
    (hρ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ρ w)
    (h𝔩 : ∀ q, 𝔩.mem z q → 𝔩'.mem z (q ∘ ρ)) :
    ∀ (K : ℕ) {g : M → ℂ}, (idealPow 𝔩 K).mem z g → (idealPow 𝔩' K).mem z (g ∘ ρ)
  | 0, g, hg => HadamardBridge.holomorphicAt_comp_map hρ (by rw [hρz]; exact hg)
  | K + 1, g, hg => by
    obtain ⟨hghol, N, s, a, hs, ha, hsum⟩ := mem_idealPow_succ_iff.mp hg
    have hρt : Tendsto ρ (𝓝 z) (𝓝 z) := by
      have h := hρ.self_of_nhds.continuousAt
      rwa [ContinuousAt, hρz] at h
    refine mem_idealPow_succ_iff.mpr
      ⟨HadamardBridge.holomorphicAt_comp_map hρ (by rw [hρz]; exact hghol), N,
        fun i => s i ∘ ρ, fun i => a i ∘ ρ, fun i => ?_,
        fun i => HadamardBridge.holomorphicAt_comp_map hρ (by rw [hρz]; exact ha i), ?_⟩
    · obtain ⟨p, q, hp, hq, hpq⟩ := hs i
      exact ⟨p ∘ ρ, q ∘ ρ, comp_mem_idealPow_of_comp_mem hρz hρ h𝔩 K hp, h𝔩 q hq, by
        show s i ∘ ρ = _
        rw [hpq]; rfl⟩
    · filter_upwards [hρt.eventually hsum] with w hw
      simpa using hw

/-- **Powers are monotone in the stalk**: if `𝔩 ⊆ 𝔩'` at `z`, then `𝔩^K ⊆ 𝔩'^K` at `z`. Duplicate of
`ExceptionalIdealPushforward.mem_idealPow_of_mem_at` (the same statement, proved earlier), kept per the no-delete rule. -/
theorem mem_idealPow_of_forall_mem {𝔩 𝔩' : GermIdeal n M} {z : M}
    (h : ∀ q, 𝔩.mem z q → 𝔩'.mem z q) (K : ℕ) {g : M → ℂ} (hg : (idealPow 𝔩 K).mem z g) :
    (idealPow 𝔩' K).mem z g :=
  comp_mem_idealPow_of_comp_mem (ρ := id) rfl (Eventually.of_forall fun _ => mdifferentiableAt_id)
    h K hg

/-- **Vanishing ideals pull back under a map sending `A` into `B` near a fixed point**: if
`ρ z = z`, `ρ` is holomorphic near `z` and maps the points of `A` near `z` into `B`, then
`q ∘ ρ ∈ 𝓘_A` at `z` for every `q ∈ 𝓘_B` at `z`. -/
theorem comp_mem_vanishingIdeal {A B : Set M} {ρ : M → M} {z : M} (hρz : ρ z = z)
    (hρ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ρ w)
    (hAB : ∀ᶠ y in 𝓝 z, y ∈ A → ρ y ∈ B) {q : M → ℂ}
    (hq : (vanishingIdeal (n := n) B).mem z q) : (vanishingIdeal (n := n) A).mem z (q ∘ ρ) := by
  have hρt : Tendsto ρ (𝓝 z) (𝓝 z) := by
    have h := hρ.self_of_nhds.continuousAt
    rwa [ContinuousAt, hρz] at h
  refine ⟨HadamardBridge.holomorphicAt_comp_map hρ (by rw [hρz]; exact hq.1), ?_⟩
  filter_upwards [hAB, hρt.eventually hq.2] with y hy1 hy2 hyA
  exact hy2 (hy1 hyA)

/-- **Restricted spans through a retraction**: if `ρ = id` on `N` near `x` and `s ∘ ρ ∈ S'` for
every `s ∈ S`, then a function agreeing on `N` near `x` with a combination of germs of `S` agrees
there with a combination of germs of `S'`. -/
theorem isInSpanOnAt_of_retraction {N : Set M} {S S' : (M → ℂ) → Prop} {ρ : M → M} {x : M}
    (hfix : ∀ᶠ y in 𝓝 x, y ∈ N → ρ y = y) (hSS' : ∀ s, S s → S' (s ∘ ρ)) {g : M → ℂ}
    (hg : IsInSpanOnAt (n := n) N S x g) : IsInSpanOnAt (n := n) N S' x g := by
  obtain ⟨K, s, a, hs, ha, hsum⟩ := hg
  refine ⟨K, fun i => s i ∘ ρ, a, fun i => hSS' _ (hs i), ha, ?_⟩
  filter_upwards [hsum, hfix] with y h1 h2 hyN
  rw [h1 hyN]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, h2 hyN]

/-- **A restricted span of a vanishing ideal vanishes**: if `A ⊆ N` and the holomorphic `g` agrees
on `N` near `x` with a combination of germs of `𝓘_A`, then `g ∈ 𝓘_A` at `x`. -/
theorem mem_vanishingIdeal_of_isInSpanOnAt {N A : Set M} (hAN : A ⊆ N) {x : M} {g : M → ℂ}
    (hg : HolomorphicAt n g x)
    (h : IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) A).mem x) x g) :
    (vanishingIdeal (n := n) A).mem x g := by
  obtain ⟨K, s, a, hs, -, hsum⟩ := h
  refine ⟨hg, ?_⟩
  have hs0 : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ A → s i y = 0 := eventually_all.mpr fun i => (hs i).2
  filter_upwards [hsum, hs0] with y h1 h2 hyA
  rw [h1 (hAN hyA)]
  exact Finset.sum_eq_zero fun i _ => by rw [h2 i hyA, mul_zero]

/-- `𝓘_H ⊆ 𝓘_{N ∩ H}`. -/
theorem vanishingIdeal_mem_inter {N H : Set M} {x : M} {q : M → ℂ}
    (hq : (vanishingIdeal (n := n) H).mem x q) : (vanishingIdeal (n := n) (N ∩ H)).mem x q :=
  ⟨hq.1, hq.2.mono fun _ hy hyA => hy hyA.2⟩

end Tools

/-! ### The member retraction -/

section Retraction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A holomorphic retraction onto `N` preserving the members of `E`.**  Let `E` be a simple
normal crossings divisor transverse to `N` and `x ∈ N`.  There is `ρ : M → M`, holomorphic near
`x`, with `ρ x = x`, `ρ y ∈ N` and `ρ y = y` for `y ∈ N` near `x`, and mapping the points of every
member `E_i` near `x` into `E_i`.  (In simultaneous coordinates `N = ℂ^k × 0` and the members
through `x` are hyperplanes `{w_{s i} = 0}`, `s i < k`; `ρ` is the flat retraction.) -/
theorem exists_memberRetraction {N : Set M} {E : List (Set M)} (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) {x : M} (hxN : x ∈ N) :
    ∃ ρ : M → M, ρ x = x ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ρ y) ∧
      (∀ᶠ y in 𝓝 x, ρ y ∈ N) ∧ (∀ᶠ y in 𝓝 x, y ∈ N → ρ y = y) ∧
      ∀ i, ∀ᶠ y in 𝓝 x, y ∈ E.get i → ρ y ∈ E.get i := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- dimension zero: `N` is a neighbourhood of `x`, and `ρ = id`
    subst hn
    obtain ⟨S₀, S, ⟨Φ, -, -, hA⟩, -⟩ := hT x hxN
    have hNx : ∀ᶠ y in 𝓝 x, y ∈ N := by
      filter_upwards [(isOpen_flatDomain (y₀ := x) Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
      exact (hA none hxN hy.1 hy.2).mpr fun j => j.elim0
    exact ⟨id, rfl, Eventually.of_forall fun _ => mdifferentiableAt_id, hNx,
      Eventually.of_forall fun _ _ => rfl, fun _ => Eventually.of_forall fun _ hy => hy⟩
  · obtain ⟨kC, kN, Φ, s, hΦsrc, hslt, -, hflat⟩ :=
      SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hT
        hT.hasNormalCrossings hxN
    have hflatN : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
          (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kN) :=
      fun hy hyΦ => (hflat hy hyΦ).2.1
    set P := planeRetract (n := n) kN with hP
    have hx' : x ∈ flatDomain Φ := mem_flatDomain_self Φ
    have hxk : flatMap Φ x ∈ complexCoordinatePlane n kN := (mem_iff_flatMap_mem hflatN hx').mp hxN
    have hPx : P (flatMap Φ x) = flatMap Φ x := planeRetract_of_mem hxk
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ flatDomain Φ ∧ P (flatMap Φ y) ∈ Φ.target := by
      refine ((isOpen_flatDomain Φ).eventually_mem hx').and ?_
      have hc : ContinuousAt (fun y => P (flatMap Φ y)) x :=
        P.continuous.continuousAt.comp
          (ExceptionalPushforwardAlong.mdifferentiableAt_flatMap hx').continuousAt
      exact hc.preimage_mem_nhds (Φ.isOpen_target.mem_nhds (by
        show P (flatMap Φ x) ∈ Φ.target
        rw [hPx]; exact flatMap_mem_target hx'))
    refine ⟨fun y => flatInv Φ (P (flatMap Φ y)), ?_, ?_, ?_, ?_, ?_⟩
    · show flatInv Φ (P (flatMap Φ x)) = x
      rw [hPx, flatInv_flatMap hx']
    · filter_upwards [hnear] with y hy
      have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
          (fun y => P (flatMap Φ y)) y :=
        P.differentiableAt.mdifferentiableAt.comp y
          (ExceptionalPushforwardAlong.mdifferentiableAt_flatMap hy.1)
      exact MDifferentiableAt.comp (g := flatInv Φ) y
        (ExceptionalPushforwardAlong.mdifferentiableAt_flatInv hΦsrc hy.2) h2
    · filter_upwards [hnear] with y hy
      exact flatInv_mem hΦsrc hflatN hy.2 (planeRetract_mem kN _)
    · filter_upwards [hnear] with y hy hyN
      show flatInv Φ (P (flatMap Φ y)) = y
      rw [planeRetract_of_mem ((mem_iff_flatMap_mem hflatN hy.1).mp hyN), flatInv_flatMap hy.1]
    · intro i
      by_cases hxi : x ∈ E.get i
      · filter_upwards [hnear] with y hy hyi
        have hD : flatInv Φ (P (flatMap Φ y)) ∈ flatDomain Φ := flatInv_mem_flatDomain hy.2 hΦsrc
        rw [(hflat hD.1 hD.2).2.2 i hxi]
        have hmap : flatMap Φ (flatInv Φ (P (flatMap Φ y))) = P (flatMap Φ y) :=
          flatMap_flatInv hy.2 hΦsrc
        show flatMap Φ (flatInv Φ (P (flatMap Φ y))) (s i) = 0
        rw [hmap, planeRetract_apply, if_pos (hslt i hxi)]
        exact ((hflat hy.1.1 hy.1.2).2.2 i hxi).mp hyi
      · have hc : IsClosed (E.get i) := hE.1 _ (List.get_mem _ _)
        filter_upwards [hc.isOpen_compl.mem_nhds hxi] with y hy hyi
        exact absurd hyi hy

end Retraction

/-! ### The ideal of the trace of a member on `N` -/

section Trace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`(𝓘_H^K)|_N = (𝓘_{N ∩ H}^K)|_N`** for a member `H = E_i` of a simple normal crossings divisor
transverse to `N`, at every `x ∈ N`: a function agrees on `N` near `x` with a combination of germs
of `𝓘_H^K` at `x` iff it agrees there with a combination of germs of `𝓘_{N ∩ H}^K` at `x`. -/
theorem isInSpanOnAt_idealPow_vanishingIdeal_iff {N : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {x : M} (hxN : x ∈ N) (i : Fin E.length)
    (K : ℕ) (g : M → ℂ) :
    IsInSpanOnAt (n := n) N ((idealPow (vanishingIdeal (n := n) (E.get i)) K).mem x) x g ↔
      IsInSpanOnAt (n := n) N ((idealPow (vanishingIdeal (n := n) (N ∩ E.get i)) K).mem x) x g := by
  obtain ⟨ρ, hρx, hρ, hρN, hρfix, hρE⟩ := exists_memberRetraction hE hT hxN
  have hmaps : ∀ᶠ y in 𝓝 x, y ∈ E.get i → ρ y ∈ N ∩ E.get i := by
    filter_upwards [hρN, hρE i] with y h1 h2 hy using ⟨h1, h2 hy⟩
  constructor
  · exact IsInSpanOnAt.mono fun s hs =>
      mem_idealPow_of_forall_mem (fun q hq => vanishingIdeal_mem_inter hq) K hs
  · exact isInSpanOnAt_of_retraction hρfix fun s hs =>
      comp_mem_idealPow_of_comp_mem hρx hρ (fun q hq => comp_mem_vanishingIdeal hρx hρ hmaps hq) K hs

/-- **`(𝓘_H)|_N = (𝓘_{N ∩ H})|_N`** (the case `K = 1`, without powers). -/
theorem isInSpanOnAt_vanishingIdeal_iff {N : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {x : M} (hxN : x ∈ N) (i : Fin E.length)
    (g : M → ℂ) :
    IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x g ↔
      IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (N ∩ E.get i)).mem x) x g := by
  obtain ⟨ρ, hρx, hρ, hρN, hρfix, hρE⟩ := exists_memberRetraction hE hT hxN
  have hmaps : ∀ᶠ y in 𝓝 x, y ∈ E.get i → ρ y ∈ N ∩ E.get i := by
    filter_upwards [hρN, hρE i] with y h1 h2 hy using ⟨h1, h2 hy⟩
  exact ⟨IsInSpanOnAt.mono fun _ hq => vanishingIdeal_mem_inter hq,
    isInSpanOnAt_of_retraction hρfix fun _ hq => comp_mem_vanishingIdeal hρx hρ hmaps hq⟩

/-- **`𝓘_{N ∩ H} = 𝓘_H + 𝓘_N` at the points of `N`**: a holomorphic germ at `x ∈ N` agrees on `N`
near `x` with a combination of germs of `𝓘_H` (`H = E_i`, `E` simple normal crossings and transverse
to `N`) iff it vanishes on `N ∩ H` near `x`. -/
theorem isInSpanOnAt_vanishingIdeal_iff_mem {N : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {x : M} (hxN : x ∈ N) (i : Fin E.length)
    {g : M → ℂ} (hg : HolomorphicAt n g x) :
    IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x g ↔
      (vanishingIdeal (n := n) (N ∩ E.get i)).mem x g := by
  rw [isInSpanOnAt_vanishingIdeal_iff hE hT hxN i g]
  refine ⟨mem_vanishingIdeal_of_isInSpanOnAt inter_subset_left hg, fun h => ?_⟩
  exact ⟨1, fun _ => g, fun _ => 1, fun _ => h, fun _ => holomorphicAt_const 1,
    Eventually.of_forall fun y _ => by simp⟩

/-- `isInSpanOnAt_idealPow_vanishingIdeal_iff` for a well-formed marked ideal `(M, N, E, 𝔞, d)`. -/
theorem isInSpanOnAt_idealPow_vanishingIdeal_iff_of_isWellFormed {𝔪 : MarkedIdeal n M}
    (h𝔪 : 𝔪.IsWellFormed) {x : M} (hx : x ∈ 𝔪.N) (i : Fin 𝔪.E.length) (K : ℕ) (g : M → ℂ) :
    IsInSpanOnAt (n := n) 𝔪.N ((idealPow (vanishingIdeal (n := n) (𝔪.E.get i)) K).mem x) x g ↔
      IsInSpanOnAt (n := n) 𝔪.N
        ((idealPow (vanishingIdeal (n := n) (𝔪.N ∩ 𝔪.E.get i)) K).mem x) x g :=
  isInSpanOnAt_idealPow_vanishingIdeal_iff h𝔪.isSNCDivisor h𝔪.isTransverse hx i K g

/-- `isInSpanOnAt_vanishingIdeal_iff_mem` for a well-formed marked ideal `(M, N, E, 𝔞, d)`. -/
theorem isInSpanOnAt_vanishingIdeal_iff_mem_of_isWellFormed {𝔪 : MarkedIdeal n M}
    (h𝔪 : 𝔪.IsWellFormed) {x : M} (hx : x ∈ 𝔪.N) (i : Fin 𝔪.E.length) {g : M → ℂ}
    (hg : HolomorphicAt n g x) :
    IsInSpanOnAt (n := n) 𝔪.N ((vanishingIdeal (n := n) (𝔪.E.get i)).mem x) x g ↔
      (vanishingIdeal (n := n) (𝔪.N ∩ 𝔪.E.get i)).mem x g :=
  isInSpanOnAt_vanishingIdeal_iff_mem h𝔪.isSNCDivisor h𝔪.isTransverse hx i hg

end Trace

/-! ### The exceptional divisor on the strict transform: `𝓘_{D ∩ N'} ⊆ 𝒪(-D) + 𝓘_{N'}` -/

section Exceptional

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **`𝒪(-D) = 𝓘_{π⁻¹ C}` at the points of `D = π⁻¹ C`.** -/
theorem exceptionalDivisor_mem_iff_vanishingIdeal (hπ : IsBlowupAlong n C π) {z : Y}
    (hzC : π z ∈ C) (g : Y → ℂ) :
    (exceptionalDivisor hπ).ideal.mem z g ↔ (vanishingIdeal (n := n) (π ⁻¹' C)).mem z g :=
  ⟨fun hg => BlowupStrictIdeal.pullback_vanishingIdeal_le hπ.contMDiff.continuous C z g hg,
    fun hg => NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem hπ
      (isSNCDivisor_nil (M := X)) (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1) hzC hg⟩

/-- **`𝒪(-KD)|_{N'} = (𝓘_{N' ∩ D}^K)|_{N'}`**: let `π` be the blowup along `C ⊆ N`, `N` a closed
submanifold, `N'` its strict transform and `z ∈ N'` over `C`.  A function agrees on `N'` near `z`
with a combination of germs of `𝒪(-D)^K` at `z` iff it agrees there with a combination of germs of
`𝓘_{N' ∩ D}^K` at `z` (`D = π⁻¹ C`). -/
theorem isInSpanOnAt_idealPow_exceptionalDivisor_iff (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {z : Y} (hzC : π z ∈ C)
    (hzN : z ∈ geoStrictTransform π C N) (K : ℕ) (g : Y → ℂ) :
    IsInSpanOnAt (n := n) (geoStrictTransform π C N)
        ((idealPow (exceptionalDivisor hπ).ideal K).mem z) z g ↔
      IsInSpanOnAt (n := n) (geoStrictTransform π C N)
        ((idealPow (vanishingIdeal (n := n) (geoStrictTransform π C N ∩ π ⁻¹' C)) K).mem z) z g := by
  have h := isInSpanOnAt_idealPow_vanishingIdeal_iff (isSNCDivisor_preimage_centre hπ)
    (isTransverse_preimage_centre hπ hN hCN) hzN ⟨0, by simp⟩ K g
  have hpow : ∀ s, (idealPow (exceptionalDivisor hπ).ideal K).mem z s ↔
      (idealPow (vanishingIdeal (n := n) (π ⁻¹' C)) K).mem z s := fun s =>
    ⟨mem_idealPow_of_forall_mem (fun q hq => (exceptionalDivisor_mem_iff_vanishingIdeal hπ hzC q).mp hq)
        K,
      mem_idealPow_of_forall_mem
        (fun q hq => (exceptionalDivisor_mem_iff_vanishingIdeal hπ hzC q).mpr hq) K⟩
  exact ⟨fun h1 => h.mp (IsInSpanOnAt.mono (fun s hs => (hpow s).mp hs) h1),
    fun h1 => IsInSpanOnAt.mono (fun s hs => (hpow s).mpr hs) (h.mpr h1)⟩

/-- **`𝓘_{D ∩ N'} = 𝒪(-D) + 𝓘_{N'}` at the points of `D ∩ N'`**: a holomorphic germ at `z ∈ N'`
over `C` agrees on `N'` near `z` with a combination of germs of `𝒪(-D)` iff it vanishes on
`N' ∩ π⁻¹ C` near `z`. -/
theorem isInSpanOnAt_exceptionalDivisor_iff_mem (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {z : Y} (hzC : π z ∈ C)
    (hzN : z ∈ geoStrictTransform π C N) {g : Y → ℂ} (hg : HolomorphicAt n g z) :
    IsInSpanOnAt (n := n) (geoStrictTransform π C N) ((exceptionalDivisor hπ).ideal.mem z) z g ↔
      (vanishingIdeal (n := n) (geoStrictTransform π C N ∩ π ⁻¹' C)).mem z g := by
  have h := isInSpanOnAt_vanishingIdeal_iff_mem (isSNCDivisor_preimage_centre hπ)
    (isTransverse_preimage_centre hπ hN hCN) hzN ⟨0, by simp⟩ hg
  exact ⟨fun h1 => h.mp (IsInSpanOnAt.mono
      (fun s hs => (exceptionalDivisor_mem_iff_vanishingIdeal hπ hzC s).mp hs) h1),
    fun h1 => IsInSpanOnAt.mono (fun s hs => (exceptionalDivisor_mem_iff_vanishingIdeal hπ hzC s).mpr hs)
      (h.mpr h1)⟩

/-- **The restricted helper `𝓘_{D ∩ N'} ⊆ 𝒪(-D) + 𝓘_{N'}`** (the along-`N'` form of
`NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem`): a germ at `z ∈ N'` over
`C` vanishing on `N' ∩ π⁻¹ C` near `z` agrees on `N'` near `z` with a combination of germs of
`𝒪(-D)` at `z`. -/
theorem isInSpanOnAt_exceptionalDivisor_of_mem_vanishingIdeal (hπ : IsBlowupAlong n C π)
    {N : Set X} (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {z : Y} (hzC : π z ∈ C)
    (hzN : z ∈ geoStrictTransform π C N) {g : Y → ℂ}
    (hg : (vanishingIdeal (n := n) (geoStrictTransform π C N ∩ π ⁻¹' C)).mem z g) :
    IsInSpanOnAt (n := n) (geoStrictTransform π C N) ((exceptionalDivisor hπ).ideal.mem z) z g :=
  (isInSpanOnAt_exceptionalDivisor_iff_mem hπ hN hCN hzC hzN hg.1).mpr hg

end Exceptional

end

end Hironaka.MemberTraceIdealAlong

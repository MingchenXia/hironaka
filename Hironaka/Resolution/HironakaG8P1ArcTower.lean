import Hironaka.Resolution.HironakaG8P1Assembly
import Hironaka.Blowup.BlowupIsomorphismOff

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Arc towers are determined by the arc (G8B lane, run 0080; port P1, step (ii))

Blueprint: `hironaka-g8-p1-arc-tower.tex`.  Plan: `work/hironaka-resume-20261111/G8B/REPORT-r1.md` §2 (ii).

Source: Bierstone–Milman 2008, §6, proof of Theorem 6.1: after the product with a line, the centres are the points
`a_{j+1} = Γ_{j+1} ∩ D_{j+1}` of the strict transforms of the arc `Γ₁ = {a} × 𝔸¹` — they depend only on the point `a`,
not on the marked ideal.  The library's arc towers (`HironakaActualSharedRecursivePointTests`, run for one record) are
built with charts adapted to that record's carrier; this module shows that the CENTRES are intrinsic: a point `z` of a
stage carrying an `ArcChart` (a chart `e` centred at `z` whose last coordinate axis lifts the arc `t ↦ (x, t)`) is the
limit `t → 0` of the unique lifts of `(x, t)`.  Hence two such towers built from the same first blowup, each step the
canonical point blowup `blowupProj` at the previous arc point, coincide.

* `lastVec`, `lineVec`: the vectors `t·e_last` of `ℂⁿ⁺¹` and `t` of `ℂ¹`; `monomial_lastVec`;
* `ArcChart x T e z`, `InjOff T` (the tower's projection is injective over `t ≠ 0`);
* `ArcChart.proj_eq` (`T.proj z = (x, 0)`), `injOff_refl`, `injOff_step` (point blowups at points over `t = 0`),
  **`arc_unique`** (two arc charts of one tower have the same centre), `arcChart_step` (an arc chart passes to the next
  canonical point blowup through a monomial chart with pivot the last coordinate), `arcChart_base` (the first blowup, in
  the flat chart of the product), **`arc_step_identify`** (two arc towers agreeing up to stage `r` agree at `r + 1`);
* `ArcStage`, `IsArcFamily`, **`arcFamily_identify`** (two arc families at the same point are the same tower, stage by
  stage); `TailState`, `NextGeom` (public copies of the library's arc-test state and successor geometry),
  `arc_of_tail`, `succ_of_next`, `isArcFamily_of_tail`, `ArcCountsRaw`, `ArcCounts`, `arcCounts_of_raw`,
  **`exists_arcFamily`** (the library's arc test `exists_two_record_shared_cartier_trace_test_counts`, run for ONE
  record, is an arc family with exact Cartier counts at every stage);
* **`normalized_order_eq_of_projected_wEquiv`** — BM08 Theorem 6.1 for different carriers of equal dimension: run the
  library's arc test once for `A` and once for `B`; by `arcFamily_identify` both runs build the same tower; conclude with
  `HironakaG8P1Assembly.normalized_order_eq_of_common_tower`.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal BlowupConstruction BlowupMonomialCharts BlowupFlatCoordinates
  HironakaActualProjectionTestRecord
open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ}

/-! ### The arc vectors -/

/-- `t · e_last` in `ℂⁿ⁺¹`. -/
def lastVec (n : ℕ) (t : ℂ) : ComplexModel (n+1) := t • EuclideanSpace.single (Fin.last n) (1 : ℂ)

/-- `t` in `ℂ¹`. -/
def lineVec (t : ℂ) : ComplexModel 1 := t • EuclideanSpace.single 0 (1 : ℂ)

theorem continuous_lastVec : Continuous (lastVec n) := continuous_id.smul continuous_const

theorem continuous_lineVec : Continuous lineVec := continuous_id.smul continuous_const

theorem lastVec_zero : lastVec n 0 = 0 := zero_smul _ _

theorem lineVec_zero : lineVec 0 = 0 := zero_smul _ _

theorem lastVec_apply (t : ℂ) (i : Fin (n+1)) : lastVec n t i = if i = Fin.last n then t else 0 := by
  by_cases h : i = Fin.last n
  · subst h
    simp [lastVec]
  · simp [lastVec, h]

theorem lineVec_apply_zero (t : ℂ) : lineVec t 0 = t := by
  simp [lineVec]

/-- The monomial chart map with pivot the last coordinate fixes the last axis. -/
theorem monomial_lastVec (t : ℂ) : monomial 0 (Fin.last n) (lastVec n t) = lastVec n t := by
  ext i
  rw [monomial_apply]
  split_ifs with h
  · rw [lastVec_apply, if_neg h.2, zero_mul]
  · rfl

/-! ### Arc charts -/

variable {X : CMfd.{u} n}

/-- **An arc chart** at `z`: a chart centred at `z` whose last coordinate axis `t ↦ e⁻¹(t e_last)` lies over the arc
`t ↦ (x, t)` of the product with a line. -/
structure ArcChart (x : X) {Z : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1))) (z : Z) : Prop where
  mem_source : z ∈ e.source
  eq_zero : e z = 0
  arc : ∀ᶠ t in 𝓝 (0 : ℂ), lastVec n t ∈ e.target ∧ (T.proj (e.symm (lastVec n t))).1 = x ∧
    (T.proj (e.symm (lastVec n t))).2 0 = t

/-- The tower's projection is injective over the points off the horizontal hyperplane `t = 0`. -/
def InjOff {Z : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Z) : Prop :=
  ∀ v w : Z, T.proj v = T.proj w → (T.proj v).2 0 ≠ 0 → v = w

theorem ArcChart.symm_zero {x : X} {Z : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z}
    {e : OpenPartialHomeomorph Z (ComplexModel (n+1))} {z : Z} (h : ArcChart x T e z) : e.symm 0 = z := by
  rw [← h.eq_zero]
  exact e.left_inv h.mem_source

/-- An arc point lies over `(x, 0)`. -/
theorem ArcChart.proj_eq {x : X} {Z : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z}
    {e : OpenPartialHomeomorph Z (ComplexModel (n+1))} {z : Z} (h : ArcChart x T e z) :
    (T.proj z).1 = x ∧ (T.proj z).2 0 = 0 := by
  obtain ⟨-, h1, h2⟩ := h.arc.self_of_nhds
  rw [lastVec_zero, h.symm_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem injOff_refl : InjOff (BlowupTower.refl : BlowupTower (projectionAmbient X) (projectionAmbient X)) :=
  fun _ _ h _ => h

/-- **Point blowups at points over `t = 0` keep the injectivity off `t = 0`.** -/
theorem injOff_step {Z Z' : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z} (hT : InjOff T) {z : Z}
    (hz : (T.proj z).2 0 = 0) {π : Z' → Z} (hπ : IsBlowupAlong (n+1) ({z} : Set Z) π) :
    InjOff (T.step ({z} : Set Z) π hπ) := by
  intro v w hvw hne
  change T.proj (π v) = T.proj (π w) at hvw
  change (T.proj (π v)).2 0 ≠ 0 at hne
  have h1 : π v = π w := hT _ _ hvw hne
  have hv : π v ∈ ({z} : Set Z)ᶜ := by
    intro h
    rw [mem_singleton_iff] at h
    rw [h] at hne
    exact hne hz
  have hw : π w ∈ ({z} : Set Z)ᶜ := h1 ▸ hv
  exact (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.injOn hv hw h1

/-- **The arc point is unique**: two arc charts of the same tower (injective off `t = 0`) have the same centre — both
centres are the limit of the unique lifts of `(x, t)`, `t → 0`. -/
theorem arc_unique {x : X} {Z : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z} (hT : InjOff T)
    {e e' : OpenPartialHomeomorph Z (ComplexModel (n+1))} {z z' : Z} (h : ArcChart x T e z)
    (h' : ArcChart x T e' z') : z = z' := by
  have h0 : (0 : ComplexModel (n+1)) ∈ e.target := by
    rw [← h.eq_zero]
    exact e.map_source h.mem_source
  have h0' : (0 : ComplexModel (n+1)) ∈ e'.target := by
    rw [← h'.eq_zero]
    exact e'.map_source h'.mem_source
  have hl : Tendsto (lastVec n) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have := continuous_lastVec (n := n).tendsto 0
    rwa [lastVec_zero] at this
  have hf : Tendsto (fun t => e.symm (lastVec n t)) (𝓝 (0 : ℂ)) (𝓝 z) := by
    have := (e.continuousAt_symm h0).tendsto.comp hl
    rwa [h.symm_zero] at this
  have hg : Tendsto (fun t => e'.symm (lastVec n t)) (𝓝 (0 : ℂ)) (𝓝 z') := by
    have := (e'.continuousAt_symm h0').tendsto.comp hl
    rwa [h'.symm_zero] at this
  have heq : (fun t => e.symm (lastVec n t)) =ᶠ[𝓝[≠] (0 : ℂ)] (fun t => e'.symm (lastVec n t)) := by
    filter_upwards [nhdsWithin_le_nhds h.arc, nhdsWithin_le_nhds h'.arc, self_mem_nhdsWithin]
      with t ha ha' ht
    obtain ⟨-, h1, h2⟩ := ha
    obtain ⟨-, h1', h2'⟩ := ha'
    have hproj : T.proj (e.symm (lastVec n t)) = T.proj (e'.symm (lastVec n t)) := by
      refine Prod.ext (h1.trans h1'.symm) ?_
      ext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact h2.trans h2'.symm
    exact hT _ _ hproj (by rw [h2]; exact ht)
  exact tendsto_nhds_unique ((tendsto_nhdsWithin_of_tendsto_nhds hf).congr' heq)
    (tendsto_nhdsWithin_of_tendsto_nhds hg)

/-- **An arc chart passes to the next canonical point blowup** through a monomial chart with pivot the last coordinate. -/
theorem arcChart_step {x : X} {Z : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z}
    {e : OpenPartialHomeomorph Z (ComplexModel (n+1))} {z : Z} (h : ArcChart x T e z)
    (c2 : FlatChart (n+1) ({z} : Set Z)) (hsrc : c2.invFun 0 ∈ c2.source) (hz0 : c2.toFun (c2.invFun 0) = 0)
    (hchart : ∀ v ∈ c2.source, blowupProj (n+1) ({z} : Set Z) v ∈ e.source ∧
      e (blowupProj (n+1) ({z} : Set Z) v) = monomial 0 (Fin.last n) (c2.toFun v))
    (hπ : IsBlowupAlong (n+1) ({z} : Set Z) (blowupProj (n+1) ({z} : Set Z))) :
    ArcChart x (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({z} : Set Z))) T ({z} : Set Z)
      (blowupProj (n+1) ({z} : Set Z)) hπ) c2.homeo (c2.invFun 0) := by
  have h0t : (0 : ComplexModel (n+1)) ∈ c2.homeo.target := by
    rw [← hz0]
    exact c2.homeo.map_source hsrc
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), lastVec n t ∈ c2.homeo.target := by
    have hc := continuous_lastVec (n := n).continuousAt (x := (0 : ℂ))
    rw [ContinuousAt, lastVec_zero] at hc
    exact hc (c2.homeo.open_target.mem_nhds h0t)
  refine ⟨hsrc, hz0, ?_⟩
  filter_upwards [hev, h.arc] with t ht ha
  obtain ⟨-, h1, h2⟩ := ha
  refine ⟨ht, ?_⟩
  have hv : c2.homeo.symm (lastVec n t) ∈ c2.source := c2.homeo.map_target ht
  have hcv : c2.toFun (c2.homeo.symm (lastVec n t)) = lastVec n t := c2.homeo.right_inv ht
  obtain ⟨hbs, hbe⟩ := hchart _ hv
  have hb : blowupProj (n+1) ({z} : Set Z) (c2.homeo.symm (lastVec n t)) = e.symm (lastVec n t) := by
    rw [← e.left_inv hbs, hbe, hcv, monomial_lastVec]
  change (T.proj (blowupProj (n+1) ({z} : Set Z) (c2.homeo.symm (lastVec n t)))).1 = x ∧
    (T.proj (blowupProj (n+1) ({z} : Set Z) (c2.homeo.symm (lastVec n t)))).2 0 = t
  rw [hb]
  exact ⟨h1, h2⟩

/-- **The first arc chart**: the flat chart of the point blowup of the product at `(x, 0)`, whose flat coordinates are
the coordinates of a chart of `X` centred at `x` followed by the line coordinate, is an arc chart at its centre. -/
theorem arcChart_base (x : X) (c : FlatChart (n+1) ({(x, 0)} : Set (projectionAmbient X)))
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (hcy : c.y₀ = (x, 0)) (hck : c.k = 0)
    (hcj : c.j = Fin.last n)
    (hOld : ∀ (y : projectionAmbient X) (i : Fin n), flatCoord c.Φ (i.castAdd 1) y = flatCoord Φ i y.1)
    (hLast : ∀ y : projectionAmbient X, flatCoord c.Φ (Fin.last n) y = y.2 0)
    (h0c : (0 : ComplexModel (n+1)) ∈ c.target) (hzsrc : c.invFun 0 ∈ c.source) (hz0 : c.toFun (c.invFun 0) = 0)
    (hπ : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) :
    ArcChart x (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({(x, 0)} : Set (projectionAmbient X))))
      BlowupTower.refl ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))) hπ) c.homeo (c.invFun 0) := by
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), lastVec n t ∈ c.target := by
    have hc := continuous_lastVec (n := n).continuousAt (x := (0 : ℂ))
    rw [ContinuousAt, lastVec_zero] at hc
    exact hc (c.isOpen_target.mem_nhds h0c)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), ((x, lineVec t) : projectionAmbient X) ∈ flatDomain c.Φ := by
    have hcont : Continuous (fun t : ℂ => ((x, lineVec t) : X × ComplexModel 1)) :=
      continuous_const.prodMk continuous_lineVec
    have hc := hcont.continuousAt (x := (0 : ℂ))
    rw [ContinuousAt, lineVec_zero] at hc
    have hmem : ((x, 0) : projectionAmbient X) ∈ flatDomain c.Φ :=
      Eq.mp (congrArg (fun a => a ∈ flatDomain c.Φ) hcy) (mem_flatDomain_self c.Φ)
    exact hc ((isOpen_flatDomain c.Φ).mem_nhds hmem)
  refine ⟨hzsrc, hz0, ?_⟩
  filter_upwards [hev1, hev2] with t ht ht2
  refine ⟨ht, ?_⟩
  change (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (c.invFun (lastVec n t))).1 = x ∧
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)) (c.invFun (lastVec n t))).2 0 = t
  rw [c.blowupProj_invFun ht]
  have hy : c.pt (lastVec n t) ∈ flatDomain c.Φ := c.pt_mem_dom ht
  have hfy : c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ (c.pt (lastVec n t))) = lastVec n t := by
    rw [c.flat_pt ht, hck, hcj, monomial_lastVec]
  have hfy'' : c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ ((x, lineVec t) : projectionAmbient X)) =
      lastVec n t := by
    ext i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · have h := hLast ((x, lineVec t) : projectionAmbient X)
      unfold flatCoord at h
      rw [h, lastVec_apply, if_pos rfl]
      exact lineVec_apply_zero t
    · have h := hOld ((x, lineVec t) : projectionAmbient X) i'
      unfold flatCoord at h
      have hcs : (Fin.castAdd 1 i' : Fin (n+1)) = Fin.castSucc i' := rfl
      rw [← hcs, h, lastVec_apply, if_neg (by rw [hcs]; exact Fin.castSucc_ne_last i')]
      change Φ.toFun (chartAt (ComplexModel n) x x) i' = 0
      rw [hΦ0]
      rfl
  have hc1 : chartAt (ComplexModel (n+1)) c.y₀ (c.pt (lastVec n t)) =
      chartAt (ComplexModel (n+1)) c.y₀ ((x, lineVec t) : projectionAmbient X) := by
    rw [← c.Φ.left_inv _ hy.2, hfy, ← hfy'', c.Φ.left_inv _ ht2.2]
  have hyy : c.pt (lastVec n t) = ((x, lineVec t) : projectionAmbient X) := by
    rw [← (chartAt (ComplexModel (n+1)) c.y₀).left_inv hy.1, hc1,
      (chartAt (ComplexModel (n+1)) c.y₀).left_inv ht2.1]
  rw [hyy]
  exact ⟨rfl, lineVec_apply_zero t⟩

/-- **Two arc towers agreeing at stage `r` agree at stage `r + 1`**: if both next stages are the canonical point blowup
`blowupProj` at the (common) previous arc point and both carry arc charts, their towers and arc points coincide, and the
injectivity off `t = 0` passes on. -/
theorem arc_step_identify {x : X} {Y1 : CMfd.{u} (n+1)} (A₁ : BlowupTower (projectionAmbient X) Y1)
    {Zs : CMfd.{u} (n+1)} (Rs : BlowupTower Y1 Zs) (zs : Zs) (hInj : InjOff (A₁.append Rs))
    (hzs : ((A₁.append Rs).proj zs).2 0 = 0)
    (hπ hπ' : IsBlowupAlong (n+1) ({zs} : Set Zs) (blowupProj (n+1) ({zs} : Set Zs)))
    {Zt Zt' : CMfd.{u} (n+1)} (Rt : BlowupTower Y1 Zt) (Rt' : BlowupTower Y1 Zt')
    (et : OpenPartialHomeomorph Zt (ComplexModel (n+1))) (et' : OpenPartialHomeomorph Zt' (ComplexModel (n+1)))
    (zt : Zt) (zt' : Zt')
    (hZt : Zt = CMfd.of (n := n+1) (BlowupSpace (n+1) ({zs} : Set Zs)))
    (hZt' : Zt' = CMfd.of (n := n+1) (BlowupSpace (n+1) ({zs} : Set Zs)))
    (hRt : HEq Rt (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({zs} : Set Zs))) Rs ({zs} : Set Zs)
      (blowupProj (n+1) ({zs} : Set Zs)) hπ))
    (hRt' : HEq Rt' (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({zs} : Set Zs))) Rs ({zs} : Set Zs)
      (blowupProj (n+1) ({zs} : Set Zs)) hπ'))
    (hA : ArcChart x (A₁.append Rt) et zt) (hA' : ArcChart x (A₁.append Rt') et' zt') :
    Zt = Zt' ∧ HEq Rt Rt' ∧ HEq zt zt' ∧ InjOff (A₁.append Rt) := by
  subst hZt hZt'
  obtain rfl := eq_of_heq hRt
  obtain rfl := eq_of_heq hRt'
  have hInj' : InjOff (A₁.append (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({zs} : Set Zs)))
      Rs ({zs} : Set Zs) (blowupProj (n+1) ({zs} : Set Zs)) hπ)) :=
    injOff_step hInj hzs hπ
  exact ⟨rfl, HEq.rfl, heq_of_eq (arc_unique hInj' hA hA'), hInj'⟩


/-! ### Arc families -/

open HironakaActualSharedCartierTraceTests HironakaG8P1Assembly ResolutionInvariantSpec
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)

/-- The first blowup space of the arc test at `x`: the point blowup of the product at `(x, 0)`. -/
abbrev arcY1 (x : X) : CMfd.{u} (n+1) :=
  CMfd.of (n := n+1) (BlowupSpace (n+1) ({(x, 0)} : Set (projectionAmbient X)))

/-- The first blowup of the arc test at `x`. -/
abbrev arcA1 (x : X) (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) :
    BlowupTower (projectionAmbient X) (arcY1 x) :=
  BlowupTower.step BlowupTower.refl ({(x, 0)} : Set (projectionAmbient X))
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))) hπ1

/-- A stage of an arc tower after the first blowup: the stage, its tower, a chart and the arc point. -/
structure ArcStage (n : ℕ) (Y1 : CMfd.{u} (n+1)) : Type (u+1) where
  Z : CMfd.{u} (n+1)
  R : BlowupTower Y1 Z
  e : OpenPartialHomeomorph Z (ComplexModel (n+1))
  z : Z

/-- **An arc family**: stage `0` is the first blowup itself, every stage carries an arc chart, and each next stage is the
canonical point blowup at the previous arc point. -/
structure IsArcFamily (x : X) (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) (S : ℕ → ArcStage n (arcY1 x)) : Prop where
  zero_Z : (S 0).Z = arcY1 x
  zero_R : HEq (S 0).R (BlowupTower.refl : BlowupTower (arcY1 x) (arcY1 x))
  arc : ∀ r, ArcChart x ((arcA1 x hπ1).append (S r).R) (S r).e (S r).z
  succ : ∀ r, ∃ hπ : IsBlowupAlong (n+1) ({(S r).z} : Set (S r).Z) (blowupProj (n+1) ({(S r).z} : Set (S r).Z)),
    (S (r+1)).Z = CMfd.of (n := n+1) (BlowupSpace (n+1) ({(S r).z} : Set (S r).Z)) ∧
    HEq (S (r+1)).R (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({(S r).z} : Set (S r).Z)))
      (S r).R ({(S r).z} : Set (S r).Z) (blowupProj (n+1) ({(S r).z} : Set (S r).Z)) hπ)

/-- **Two arc families at the same point are the same tower**, stage by stage. -/
theorem arcFamily_identify {x : X} {hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))} {S S' : ℕ → ArcStage n (arcY1 x)}
    (hS : IsArcFamily x hπ1 S) (hS' : IsArcFamily x hπ1 S') :
    ∀ r, (S r).Z = (S' r).Z ∧ HEq (S r).R (S' r).R ∧ HEq (S r).z (S' r).z ∧
      InjOff ((arcA1 x hπ1).append (S r).R) := by
  intro r
  induction r with
  | zero =>
    have h1 := hS.arc 0
    have h2 := hS'.arc 0
    have hZ := hS.zero_Z
    have hZ' := hS'.zero_Z
    have hR := hS.zero_R
    have hR' := hS'.zero_R
    generalize S 0 = s at h1 hZ hR ⊢
    generalize S' 0 = s' at h2 hZ' hR' ⊢
    obtain ⟨Zs, Rs, es, zs⟩ := s
    obtain ⟨Zs', Rs', es', zs'⟩ := s'
    dsimp only at h1 h2 hZ hZ' hR hR' ⊢
    subst hZ hZ'
    obtain rfl := eq_of_heq hR
    obtain rfl := eq_of_heq hR'
    have hInj : InjOff (arcA1 x hπ1) := injOff_step injOff_refl (by rfl) hπ1
    exact ⟨rfl, HEq.rfl, heq_of_eq (arc_unique hInj h1 h2), hInj⟩
  | succ r ih =>
    obtain ⟨hZ, hR, hz, hinj⟩ := ih
    have hzs := (hS.arc r).proj_eq.2
    obtain ⟨hπ, hZt, hRt⟩ := hS.succ r
    obtain ⟨hπ', hZt', hRt'⟩ := hS'.succ r
    have hAt := hS.arc (r + 1)
    have hAt' := hS'.arc (r + 1)
    generalize S (r + 1) = t at hZt hRt hAt ⊢
    generalize S' (r + 1) = t' at hZt' hRt' hAt' ⊢
    generalize S r = s at hZ hR hz hinj hzs hπ hZt hRt
    generalize S' r = s' at hZ hR hz hπ' hZt' hRt'
    obtain ⟨Zs, Rs, es, zs⟩ := s
    obtain ⟨Zs', Rs', es', zs'⟩ := s'
    obtain ⟨Zt, Rt, et, zt⟩ := t
    obtain ⟨Zt', Rt', et', zt'⟩ := t'
    dsimp only at hZ hR hz hinj hzs hπ hπ' hZt hRt hZt' hRt' hAt hAt' ⊢
    subst hZ
    obtain rfl := eq_of_heq hR
    obtain rfl := eq_of_heq hz
    exact arc_step_identify (arcA1 x hπ1) Rs zs hinj hzs hπ hπ' Rt Rt' et et' zt zt' hZt hZt' hRt hRt' hAt hAt'

/-- **The counts of the arc test at a stage `r`** for a record `M` (exact Cartier counts on the last stage, with
`β = (r + 1)(ρ - d)`, the stage being a test tower whose arc point is a cosupport point). -/
def ArcCounts {k : ℕ} (M : MarkedIdeal n X) (x : X) (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) (s : ArcStage n (arcY1 x)) (r : ℕ) : Prop :=
  s.R.length = r ∧ IsGeoTestTower (projectionTest M) ((arcA1 x hπ1).append s.R) ∧
    s.z ∈ ((projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R)).cosupp ∧
    ∃ G : CartierGeometryFamily s.Z,
      HEq (G.state 0).N ((projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R)).N ∧
      HEq (G.state 0).E ((projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R)).E ∧
      ((G.state 0).i).val + 1 = (G.state 0).E.length ∧ HEq (G.state 0).z s.z ∧
      CartierQueryCountOutput (k := k + 1) ((projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R))
        ((r + 1) * (HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder M.N M.ideal x - M.d)) G

/-- The counts of the arc test as the library states them (before rewriting): the stage, its test property, the
record identity of the transform, the arc point in the cosupport, and the Cartier counts with `β = (|R| + 1)(ρ - d)`. -/
def ArcCountsRaw {k : ℕ} (M : MarkedIdeal n X) (x : X) (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) (s : ArcStage n (arcY1 x)) (r : ℕ) : Prop :=
  s.R.length = r ∧ IsGeoTestTower (projectionTest M) ((arcA1 x hπ1).append s.R) ∧
    ((projectionTest M).geoTransform ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))).geoTransformAlong s.R =
      (projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R) ∧
    s.z ∈ (((projectionTest M).geoTransform ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))).geoTransformAlong s.R).cosupp ∧
    ∃ G : CartierGeometryFamily s.Z,
      HEq (G.state 0).N ((projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R)).N ∧
      HEq (G.state 0).E ((projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R)).E ∧
      ((G.state 0).i).val + 1 = (G.state 0).E.length ∧ HEq (G.state 0).z s.z ∧
      CartierQueryCountOutput (k := k + 1) ((projectionTest M).geoTransformAlong ((arcA1 x hπ1).append s.R))
        ((s.R.length + 1) * (HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder M.N M.ideal x - M.d)) G

theorem arcCounts_of_raw {k : ℕ} {M : MarkedIdeal n X} {x : X} {hπ1 : IsBlowupAlong (n+1)
    ({(x, 0)} : Set (projectionAmbient X)) (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))}
    {s : ArcStage n (arcY1 x)} {r : ℕ} (h : ArcCountsRaw (k := k) M x hπ1 s r) : ArcCounts (k := k) M x hπ1 s r := by
  obtain ⟨hL, hT, hRec, hCos, G, hN, hE, hi, hz, hC⟩ := h
  refine ⟨hL, hT, ?_, G, hN, hE, hi, hz, ?_⟩
  · rw [← hRec]
    exact hCos
  · rw [hL] at hC
    exact hC

/-- The tail states of the library's arc test (a public copy of its state type: stage, tower after the first blowup,
anchored chart chain, arc point). -/
abbrev TailState {Y1 : CMfd.{u} (n+1)} (Q1 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))) : Type (u+1) :=
  Σ Z : CMfd.{u} (n+1), Σ R : BlowupTower Y1 Z, Σ e : OpenPartialHomeomorph Z (ComplexModel (n+1)),
    {z : Z // HironakaActualAnchoredVerticalChart.AnchoredInheritedLastChartChain a R e ∧ IsGeoTestTower Q1 R ∧
      z ∈ e.source ∧ e z = 0}

/-- The successor geometry of the library's arc test (a public copy): the canonical point blowup at the arc point, read
in a monomial chart with pivot the last coordinate. -/
abbrev NextGeom {Y1 : CMfd.{u} (n+1)} (Q1 : MarkedIdeal (n+1) Y1)
    (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1))) (s t : TailState Q1 a) : Prop :=
  ∃ (c2 : FlatChart (n+1) ({s.2.2.2.1} : Set s.1))
    (hπ2 : IsBlowupAlong (n+1) ({s.2.2.2.1} : Set s.1) (blowupProj (n+1) ({s.2.2.2.1} : Set s.1))),
    c2.y₀ = s.2.2.2.1 ∧ c2.k = 0 ∧ c2.j = Fin.last n ∧
    c2.invFun 0 ∈ c2.source ∧ c2.toFun (c2.invFun 0) = 0 ∧
    blowupProj (n+1) ({s.2.2.2.1} : Set s.1) (c2.invFun 0) = s.2.2.2.1 ∧
    (∀ v ∈ c2.source,
      blowupProj (n+1) ({s.2.2.2.1} : Set s.1) v ∈ s.2.2.1.source ∧
      s.2.2.1 (blowupProj (n+1) ({s.2.2.2.1} : Set s.1) v) = monomial 0 (Fin.last n) (c2.toFun v)) ∧
    HEq t.1 (CMfd.of (n := n+1) (BlowupSpace (n+1) ({s.2.2.2.1} : Set s.1))) ∧
    HEq t.2.1 (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({s.2.2.2.1} : Set s.1)))
      s.2.1 ({s.2.2.2.1} : Set s.1) (blowupProj (n+1) ({s.2.2.2.1} : Set s.1)) hπ2) ∧
    HEq t.2.2.1 c2.homeo ∧ HEq t.2.2.2.1 (c2.invFun 0)

/-- The arc charts of the library's arc test (stage `0`: the flat chart of the first blowup; successors through the monomial charts). -/
theorem arc_of_tail (x : X) (c : FlatChart (n+1) ({(x, 0)} : Set (projectionAmbient X)))
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (hcy : c.y₀ = (x, 0)) (hck : c.k = 0)
    (hcj : c.j = Fin.last n)
    (hOld : ∀ (y : projectionAmbient X) (i : Fin n), flatCoord c.Φ (i.castAdd 1) y = flatCoord Φ i y.1)
    (hLast : ∀ y : projectionAmbient X, flatCoord c.Φ (Fin.last n) y = y.2 0)
    (h0c : (0 : ComplexModel (n+1)) ∈ c.target) (hzsrc : c.invFun 0 ∈ c.source) (hz0 : c.toFun (c.invFun 0) = 0)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
    (Q1 : MarkedIdeal (n+1) (arcY1 x))
    (h0 : HironakaActualAnchoredVerticalChart.AnchoredInheritedLastChartChain c.homeo
      (BlowupTower.refl : BlowupTower (arcY1 x) (arcY1 x)) c.homeo ∧
      IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower (arcY1 x) (arcY1 x)) ∧
      c.invFun 0 ∈ c.homeo.source ∧ c.homeo (c.invFun 0) = 0)
    (Next : TailState Q1 c.homeo → TailState Q1 c.homeo) (hNext : ∀ s, NextGeom Q1 c.homeo s (Next s))
    (F : ℕ → TailState Q1 c.homeo) (hZero : F 0 = ⟨arcY1 x, BlowupTower.refl, c.homeo, ⟨c.invFun 0, h0⟩⟩)
    (hSucc : ∀ r, F (r + 1) = Next (F r)) :
    ∀ r, ArcChart x ((arcA1 x hπ1).append (F r).2.1) (F r).2.2.1 (F r).2.2.2.1 := by
  intro r
  induction r with
  | zero =>
    rw [hZero]
    exact arcChart_base x c Φ hΦ0 hcy hck hcj hOld hLast h0c hzsrc hz0 hπ1
  | succ r ih =>
    have H := hNext (F r)
    rw [hSucc r]
    generalize Next (F r) = t at H ⊢
    obtain ⟨c2, hπ2, _u20, _u23, _u21, hsrc2, hz02, _u22, hchart2, hHY, hHT, hHe, hHz⟩ := H
    obtain ⟨Zt, Rt, et, zt, _u24⟩ := t
    change HEq Zt _ at hHY
    change HEq Rt _ at hHT
    change HEq et _ at hHe
    change HEq zt _ at hHz
    change ArcChart x ((arcA1 x hπ1).append Rt) et zt
    clear _u24
    obtain rfl := eq_of_heq hHY
    obtain rfl := eq_of_heq hHT
    obtain rfl := eq_of_heq hHe
    have hz' : zt = c2.invFun 0 := eq_of_heq hHz
    rw [hz']
    exact arcChart_step ih c2 hsrc2 hz02 hchart2 hπ2

/-- The successors of the library's arc test are the canonical point blowups at the arc points. -/
theorem succ_of_next {Y1 : CMfd.{u} (n+1)} (Q1 : MarkedIdeal (n+1) Y1) (a : OpenPartialHomeomorph Y1 (ComplexModel (n+1)))
    (s t : TailState Q1 a) (H : NextGeom Q1 a s t) :
    ∃ hπ : IsBlowupAlong (n+1) ({s.2.2.2.1} : Set s.1) (blowupProj (n+1) ({s.2.2.2.1} : Set s.1)),
      t.1 = CMfd.of (n := n+1) (BlowupSpace (n+1) ({s.2.2.2.1} : Set s.1)) ∧
      HEq t.2.1 (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({s.2.2.2.1} : Set s.1))) s.2.1
        ({s.2.2.2.1} : Set s.1) (blowupProj (n+1) ({s.2.2.2.1} : Set s.1)) hπ) := by
  obtain ⟨c2, hπ2, _u20, _u23, _u21, _u25, _u26, _u22, _u27, hHY, hHT, _u28, _u29⟩ := H
  exact ⟨hπ2, eq_of_heq hHY, hHT⟩

/-- **The library's arc test is an arc family** (stage `0`: the flat chart of the first blowup; successors: canonical
point blowups at the arc points). -/
theorem isArcFamily_of_tail (x : X) (c : FlatChart (n+1) ({(x, 0)} : Set (projectionAmbient X)))
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (hcy : c.y₀ = (x, 0)) (hck : c.k = 0)
    (hcj : c.j = Fin.last n)
    (hOld : ∀ (y : projectionAmbient X) (i : Fin n), flatCoord c.Φ (i.castAdd 1) y = flatCoord Φ i y.1)
    (hLast : ∀ y : projectionAmbient X, flatCoord c.Φ (Fin.last n) y = y.2 0)
    (h0c : (0 : ComplexModel (n+1)) ∈ c.target) (hzsrc : c.invFun 0 ∈ c.source) (hz0 : c.toFun (c.invFun 0) = 0)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
    (Q1 : MarkedIdeal (n+1) (arcY1 x))
    (h0 : HironakaActualAnchoredVerticalChart.AnchoredInheritedLastChartChain c.homeo
      (BlowupTower.refl : BlowupTower (arcY1 x) (arcY1 x)) c.homeo ∧
      IsGeoTestTower Q1 (BlowupTower.refl : BlowupTower (arcY1 x) (arcY1 x)) ∧
      c.invFun 0 ∈ c.homeo.source ∧ c.homeo (c.invFun 0) = 0)
    (Next : TailState Q1 c.homeo → TailState Q1 c.homeo) (hNext : ∀ s, NextGeom Q1 c.homeo s (Next s))
    (F : ℕ → TailState Q1 c.homeo) (hZero : F 0 = ⟨arcY1 x, BlowupTower.refl, c.homeo, ⟨c.invFun 0, h0⟩⟩)
    (hSucc : ∀ r, F (r + 1) = Next (F r)) :
    IsArcFamily x hπ1 (fun r => ⟨(F r).1, (F r).2.1, (F r).2.2.1, (F r).2.2.2.1⟩) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (F 0).1 = arcY1 x
    rw [hZero]
  · show HEq (F 0).2.1 (BlowupTower.refl : BlowupTower (arcY1 x) (arcY1 x))
    rw [hZero]
  · exact arc_of_tail x c Φ hΦ0 hcy hck hcj hOld hLast h0c hzsrc hz0 hπ1 Q1 h0 Next hNext F hZero hSucc
  · intro r
    have h := succ_of_next Q1 c.homeo (F r) (Next (F r)) (hNext (F r))
    exact (congrArg (fun t : TailState Q1 c.homeo => ∃ hπ : IsBlowupAlong (n+1) ({(F r).2.2.2.1} : Set (F r).1)
        (blowupProj (n+1) ({(F r).2.2.2.1} : Set (F r).1)),
      t.1 = CMfd.of (n := n+1) (BlowupSpace (n+1) ({(F r).2.2.2.1} : Set (F r).1)) ∧
      HEq t.2.1 (BlowupTower.step (Z := CMfd.of (n := n+1) (BlowupSpace (n+1) ({(F r).2.2.2.1} : Set (F r).1)))
        (F r).2.1 ({(F r).2.2.2.1} : Set (F r).1) (blowupProj (n+1) ({(F r).2.2.2.1} : Set (F r).1)) hπ))
      (hSucc r)).mpr h

/-- **The library's arc test, read as an arc family with its counts** (`HironakaActualSharedCartierTraceTests`, run for
one record). -/
theorem exists_arcFamily {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x ∈ M.cosupp)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) :
    ∃ S : ℕ → ArcStage n (arcY1 x), IsArcFamily x hπ1 S ∧ ∀ r, ArcCountsRaw (k := k) M x hπ1 (S r) r := by
  obtain ⟨_h2, Φ, _Φs, c, _SN, _SE, _U, hOut⟩ :=
    exists_two_record_shared_cartier_trace_test_counts M M hM hM x hx hx rfl rfl
  obtain ⟨hWhole, h0, Next, hNext, hData⟩ := hOut
  extract_lets s0 F at hData
  clear_value F
  obtain ⟨hZero, hLen, hSucc, _u1, _u2, hAll⟩ := hData
  obtain ⟨_u5, hΦ0, hcy, hck, hcj, hOld, hLast, _u6, _u7, _u8, _u9, h0c, hzsrc, _u10, hz0, _u11, _u12⟩ := hWhole
  refine ⟨fun r => ⟨(F r).1, (F r).2.1, (F r).2.2.1, (F r).2.2.2.1⟩,
    isArcFamily_of_tail x c Φ hΦ0 hcy hck hcj hOld hLast h0c hzsrc hz0 hπ1 _ h0 Next hNext F hZero hSucc, ?_⟩
  intro r
  obtain ⟨hq, _u30, hcart⟩ := hAll r
  obtain ⟨hT, hRec, _u31, _u32, _u33, _u34, _u35, _u36, _u37, _u38, _u39, _u40, _u41, _u42, _u43, _u44, _u45,
    _u46, hCos, _u47⟩ := hq.1.2.2.2.2.1
  obtain ⟨G, hN, hE, hi, hz, hC, _u48, _u49, _u50⟩ := hcart
  exact ⟨hLen r, hT, hRec, hCos, G, hN, hE, hi, hz, hC⟩

/-! ### The final theorem -/

/-- **Bierstone–Milman 2008, Theorem 6.1, for different carriers of equal dimension** (port P1): marked ideals `A`
(carrier `N`) and `B` (carrier `P`) of the native domain whose products with a line are Włodarczyk-equivalent and whose
carriers have the same dimension at the points of the cosupport have the same normalized order at every cosupport point:
`B.d · ord_x(A) = A.d · ord_x(B)`.  (The library's `normalized_ordinary_order_of_projected_wEquiv` is the case
`B.N = A.N`.) -/
theorem normalized_order_eq_of_projected_wEquiv {kA kB : ℕ} {X : CMfd.{u} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (x : X) (hxA : x ∈ A.cosupp) (hxB : x ∈ B.cosupp)
    (hW : WEquiv (projectionTest A) (projectionTest B)) (hdim : SameCarrierDim A B) :
    B.d * HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder A.N A.ideal x =
      A.d * HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder B.N B.ideal x := by
  have hρA' : A.d ≤ HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder A.N A.ideal x :=
    (HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff hA.isWellFormed.isClosedSubmanifold_N
      hA.isWellFormed.isCoherent hA.isNonzeroAlongAt (A.cosupp_subset_N hxA) A.d).mp hxA
  have hρB' : B.d ≤ HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder B.N B.ideal x :=
    (HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff hB.isWellFormed.isClosedSubmanifold_N
      hB.isWellFormed.isCoherent hB.isNonzeroAlongAt (B.cosupp_subset_N hxB) B.d).mp hxB
  have hdA : 0 < A.d := by have := hA.one_le_d; omega
  have hdB : 0 < B.d := by have := hB.one_le_d; omega
  have hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))) :=
    isBlowupAlong_blowupProj (n := n+1) (C := ({(x, 0)} : Set (projectionAmbient X)))
      (HironakaActualProjectionVerticalBlowupChart.projection_point_centre A hA x hxA).2
  obtain ⟨S, hS, hcA⟩ := exists_arcFamily (k := kA) A hA x hxA hπ1
  obtain ⟨S', hS', hcB⟩ := exists_arcFamily (k := kB) B hB x hxB hπ1
  set r := A.d * B.d - 1 with hr
  have hrq : r + 1 = A.d * B.d := by have := Nat.mul_pos hdA hdB; omega
  obtain ⟨hZ, hR, hz, -⟩ := arcFamily_identify hS hS' r
  have hca := arcCounts_of_raw (hcA r)
  have hcb := arcCounts_of_raw (hcB r)
  generalize S r = s at hZ hR hz hca
  generalize S' r = s' at hZ hR hz hcb
  obtain ⟨Zs, Rs, es, zs⟩ := s
  obtain ⟨Zs', Rs', es', zs'⟩ := s'
  dsimp only at hZ hR hz
  subst hZ
  obtain rfl := eq_of_heq hR
  obtain rfl := eq_of_heq hz
  obtain ⟨-, hTA, hCosA, GA, hNA, hEA, hiA, hzGA, hCA⟩ := hca
  obtain ⟨-, -, -, GB, hNB, hEB, hiB, hzGB, hCB⟩ := hcb
  rw [hrq] at hCA hCB
  exact normalized_order_eq_of_common_tower A B hA hB _ _ hρA' hρB' hW hdim ((arcA1 x hπ1).append Rs) hTA GA GB zs
    hCosA hCA hNA hEA hiA hzGA hCB hNB hEB hiB hzGB

end

end Hironaka.HironakaG8P1ArcTower

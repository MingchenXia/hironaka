import Hironaka.Analytic.QuasiPshSingularities
import Hironaka.Analytic.ERealChordUSC
import Hironaka.Analytic.ThetaPshCompactBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The coefficient calculus behind the collar estimate

Source: Copy-4, Step 5 of `prop:principalization`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1908-1962`),
whose central sentence is

> Since all the functions `ψ_𝔧∘π`, `ψ_{G̃_M}`, `ψ_{H^fix_m}`, `ψ_{P^mov}`,
> `ψ_{P^F}` are bounded above, we conclude from `eq:def-DLY` that
> `ψ_{D-τE_rel} + χ ≤ ((1-L/M)/M) ψ_{G̃_M} + (LA_R/M)(ψ_H + ψ_𝔧∘π) + O(1)` on `Y`.

Two ingredients are hidden in that sentence, and both are supplied here.

**The comparison itself.**  For a weight `u` bounded above by a real `K` and
real coefficients `0 ≤ b ≤ a`, one has `a u ≤ b u + (a-b) K`: a *larger*
coefficient makes a weight *more* singular.  This is `moreSingularOn_const_mul`
below, and it is the only reason the displayed inequality holds — the manuscript's
`C - 1 ≥ L A_R` and `1 ≥ 1 - L/M` are exactly the five coefficient comparisons it
is applied to.  Note that it is genuinely one-sided: nothing like it holds for
`a ≤ b`, since `a u - b u = (a-b) u` is `+∞` at a pole.

**Boundedness above.**  `exists_forall_le_coe` records that an upper
semicontinuous `EReal` function which never takes the value `⊤` is bounded above
on a compact space, and
`ManifoldQuasiPlurisubharmonic.exists_forall_le_coe` specialises this to a
quasi-psh function on a compact complex manifold — which is what each of the five
weights above is.  The proof is the countable exhaustion `{u < k}`, `k : ℕ`.

The `O(1)` calculus itself (`MoreSingularOn`) is
`FirstPass/QuasiPshSingularities`; this module adds the two combinators it was
missing, additivity and nonnegative scaling.

Everything here is sorry-free.
-/

open Set

namespace Hironaka.CollarWeightComparison



noncomputable section

/-! ### Combinators for the `O(1)` order -/

variable {X : Type*}

/-- **Additivity of the singularity order.**  Two comparisons add, with the sum
of the two constants. -/
theorem moreSingularOn_add {u₁ v₁ u₂ v₂ : X → EReal} {U : Set X}
    (h₁ : MoreSingularOn u₁ v₁ U) (h₂ : MoreSingularOn u₂ v₂ U) :
    MoreSingularOn (fun x => u₁ x + u₂ x) (fun x => v₁ x + v₂ x) U := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun x hx => ?_⟩
  calc u₁ x + u₂ x ≤ (v₁ x + (C₁ : EReal)) + (v₂ x + (C₂ : EReal)) :=
        add_le_add (hC₁ x hx) (hC₂ x hx)
    _ = (v₁ x + v₂ x) + ((C₁ + C₂ : ℝ) : EReal) := by
        rw [EReal.coe_add]; exact add_add_add_comm _ _ _ _

/-- **A nonnegative real multiple preserves the singularity order**, scaling the
constant. -/
theorem moreSingularOn_smul {u v : X → EReal} {U : Set X} {c : ℝ} (hc : 0 ≤ c)
    (h : MoreSingularOn u v U) :
    MoreSingularOn (fun x => (c : EReal) * u x) (fun x => (c : EReal) * v x) U := by
  obtain ⟨C, hC⟩ := h
  refine ⟨c * C, fun x hx => ?_⟩
  calc (c : EReal) * u x ≤ (c : EReal) * (v x + (C : EReal)) :=
        mul_le_mul_of_nonneg_left (hC x hx) (EReal.coe_nonneg.mpr hc)
    _ = (c : EReal) * v x + ((c * C : ℝ) : EReal) := by
        rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc)
          (EReal.coe_ne_top c), EReal.coe_mul]

/-- **A larger coefficient on a weight bounded above is more singular.**  If
`u ≤ K` on `U` and `0 ≤ b ≤ a`, then `a u ≤ b u + (a-b) K` on `U`.

This is the one-sided comparison that Copy-4 Step 5 applies five times, and the
hypothesis `u ≤ K` cannot be dropped: at a pole of `u` the difference
`(a-b) u` is `-∞`, which is harmless, but on an unbounded-above `u` the same
difference is unbounded above. -/
theorem moreSingularOn_const_mul {u : X → EReal} {U : Set X} {a b K : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (hK : ∀ x ∈ U, u x ≤ (K : EReal)) :
    MoreSingularOn (fun x => (a : EReal) * u x) (fun x => (b : EReal) * u x) U := by
  have hab : (0 : ℝ) ≤ a - b := sub_nonneg.mpr hba
  refine ⟨(a - b) * K, fun x hx => ?_⟩
  have hsplit : (a : EReal) * u x = (b : EReal) * u x + ((a - b : ℝ) : EReal) * u x := by
    rw [← EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr hb)
      (EReal.coe_nonneg.mpr hab), ← EReal.coe_add]
    norm_num
  simp only
  rw [hsplit]
  refine add_le_add le_rfl ?_
  calc ((a - b : ℝ) : EReal) * u x ≤ ((a - b : ℝ) : EReal) * (K : EReal) :=
        mul_le_mul_of_nonneg_left (hK x hx) (EReal.coe_nonneg.mpr hab)
    _ = (((a - b) * K : ℝ) : EReal) := by rw [EReal.coe_mul]

/-! ### Weights are bounded above on a compact space -/

variable {Y : Type*} [TopologicalSpace Y]

/-- **An upper semicontinuous `EReal` function avoiding `⊤` is bounded above on a
compact space**, with no nonemptiness hypothesis.

This is `Hironaka.exists_real_upper_bound_of_upperSemicontinuous` with its
`[Nonempty X]` removed: an empty space is bounded above by `0` vacuously, and
everything else is that lemma.  The hypothesis matters here because Step 5 is
applied on a blown-up `Y` whose nonemptiness is not among the data. -/
theorem exists_forall_le_coe [CompactSpace Y] {u : Y → EReal}
    (husc : UpperSemicontinuous u) (htop : ∀ x, u x ≠ ⊤) :
    ∃ K : ℝ, ∀ x, u x ≤ (K : EReal) := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨0, fun x => isEmptyElim x⟩
  · exact Hironaka.exists_real_upper_bound_of_upperSemicontinuous husc htop

variable {n : ℕ} [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **A quasi-psh function on a compact complex manifold is bounded above.**
This is the hypothesis "`ψ` is bounded above" of Copy-4 Step 5, for each of the
five weights it is applied to.  It is the `Nonempty`-free form of
`Hironaka.ThetaPlurisubharmonic.exists_global_upper_bound`; for a function
presenting an *ideal* rather than a divisor, use
`IdealWeightComparison.exists_le_of_hasAnalyticSingularitiesOfType` instead, which
needs no topology on the value. -/
theorem ManifoldQuasiPlurisubharmonic.exists_forall_le_coe [CompactSpace Y]
    {u : Y → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u) :
    ∃ K : ℝ, ∀ x, u x ≤ (K : EReal) :=
  _root_.Hironaka.CollarWeightComparison.exists_forall_le_coe
    hu.upperSemicontinuous hu.ne_top

/-! ### Copy-4 Step 5: the weighted comparison on `Y` -/

section Step5

variable {Z : Type*}

/-- Distribution of a finite nonnegative real coefficient over an `EReal` sum. -/
theorem coe_mul_add {c : ℝ} (hc : 0 ≤ c) (x y : EReal) :
    (c : EReal) * (x + y) = (c : EReal) * x + (c : EReal) * y :=
  EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c) x y

/-- **Copy-4 Step 5, the inequality on all of `Y` preceding `eq:collar`.**

With `ψ_D - τψ_{E_rel}`, `χ` and the five exceptional weights in the roles they
have in the manuscript — `ψGM = ψ_{G̃_M}`, `ψHfix = ψ_{H^fix_m}`,
`ψPmov = ψ_{P^mov}`, `ψPF = ψ_{P^F}`, `ψj = ψ_𝔧∘π`, `ψH = ψ_H` — the three
hypotheses are `eq:def-DLY` (the shape of `ψ_{D-τE_rel}`), the bound on `χ`
obtained in the manuscript from `eq:def-Psi` and `G̃_m ≥ H^fix_m`, and the
additivity `ψ_H = ψ_{H^fix_m} + ψ_{P^mov} + ψ_{P^F} + O(1)` of `H = H^fix_m +
P^mov + P^F`.  The conclusion is the display that Step 5 then feeds to
`eq:QM-lower`.

Everything rests on five coefficient comparisons, all of which are `eq:constants`:
`1 ≥ 1 - L/M` for `ψ_{G̃_M}`, and `C - 1 ≥ L A_R` (hence also `C ≥ L A_R`) for the
other four.  Note that `C ≥ 1` is forced by `hCA` together with `L, A ≥ 0`, so it
is not a separate hypothesis. -/
theorem moreSingularOn_exceptionalWeightSum
    {ψGM ψHfix ψPmov ψPF ψj ψH ψD χ : Z → EReal}
    {lev L C A KGM KHfix KPmov KPF Kj : ℝ}
    (hL : 0 < L) (hLlev : L < lev) (hA : 0 ≤ A) (hCA : L * A ≤ C - 1)
    (hbGM : ∀ y, ψGM y ≤ (KGM : EReal))
    (hbHfix : ∀ y, ψHfix y ≤ (KHfix : EReal))
    (hbPmov : ∀ y, ψPmov y ≤ (KPmov : EReal))
    (hbPF : ∀ y, ψPF y ≤ (KPF : EReal))
    (hbj : ∀ y, ψj y ≤ (Kj : EReal))
    (hD : MoreSingularOn ψD
      (fun y => ((1 / lev : ℝ) : EReal) * ψGM y
        + (((C - 1) / lev : ℝ) : EReal) * ψPmov y
        + ((C / lev : ℝ) : EReal) * ψPF y) univ)
    (hχ : MoreSingularOn χ
      (fun y => (((C - 1) / lev : ℝ) : EReal) * (ψj y + ψHfix y)) univ)
    (hH : MoreSingularOn (fun y => ψHfix y + ψPmov y + ψPF y) ψH univ) :
    MoreSingularOn (fun y => ψD y + χ y)
      (fun y => (((1 - L / lev) / lev : ℝ) : EReal) * ψGM y
        + ((L * A / lev : ℝ) : EReal) * (ψH y + ψj y)) univ := by
  have hlev : 0 < lev := lt_trans hL hLlev
  have hLA : 0 ≤ L * A := mul_nonneg hL.le hA
  have hC1 : 0 ≤ C - 1 := le_trans hLA hCA
  -- the six coefficients
  set A1 : ℝ := 1 / lev with hA1
  set A2 : ℝ := (C - 1) / lev with hA2
  set A3 : ℝ := C / lev with hA3
  set B1 : ℝ := (1 - L / lev) / lev with hB1
  set B2 : ℝ := L * A / lev with hB2
  have hA2nn : 0 ≤ A2 := div_nonneg hC1 hlev.le
  have hB1nn : 0 ≤ B1 := by
    have : L / lev ≤ 1 := (div_le_one hlev).mpr hLlev.le
    exact div_nonneg (by linarith) hlev.le
  have hB2nn : 0 ≤ B2 := div_nonneg hLA hlev.le
  have hB1A1 : B1 ≤ A1 := by
    rw [hB1, hA1]
    have hLl : 0 ≤ L / lev := div_nonneg hL.le hlev.le
    gcongr
    linarith
  have hB2A2 : B2 ≤ A2 := by
    rw [hB2, hA2]; gcongr
  have hB2A3 : B2 ≤ A3 := le_trans hB2A2 (by
    rw [hA2, hA3]; gcongr; linarith)
  -- step (a): the sum, in canonical left-associated form
  have hχ' : MoreSingularOn χ
      (fun y => (A2 : EReal) * ψj y + (A2 : EReal) * ψHfix y) univ :=
    hχ.trans (MoreSingularOn.of_le fun y _ => le_of_eq (coe_mul_add hA2nn _ _))
  have ha := moreSingularOn_add hD hχ'
  have hcanon : ∀ y : Z,
      ((A1 : EReal) * ψGM y + (A2 : EReal) * ψPmov y + (A3 : EReal) * ψPF y)
        + ((A2 : EReal) * ψj y + (A2 : EReal) * ψHfix y)
      = (A1 : EReal) * ψGM y + (A2 : EReal) * ψPmov y + (A3 : EReal) * ψPF y
        + (A2 : EReal) * ψj y + (A2 : EReal) * ψHfix y := fun y => by
    abel
  have ha' : MoreSingularOn (fun y => ψD y + χ y)
      (fun y => (A1 : EReal) * ψGM y + (A2 : EReal) * ψPmov y + (A3 : EReal) * ψPF y
        + (A2 : EReal) * ψj y + (A2 : EReal) * ψHfix y) univ :=
    ha.trans (MoreSingularOn.of_le fun y _ => le_of_eq (hcanon y))
  -- step (b): drop each coefficient
  have hb : MoreSingularOn
      (fun y => (A1 : EReal) * ψGM y + (A2 : EReal) * ψPmov y + (A3 : EReal) * ψPF y
        + (A2 : EReal) * ψj y + (A2 : EReal) * ψHfix y)
      (fun y => (B1 : EReal) * ψGM y + (B2 : EReal) * ψPmov y + (B2 : EReal) * ψPF y
        + (B2 : EReal) * ψj y + (B2 : EReal) * ψHfix y) univ :=
    moreSingularOn_add (moreSingularOn_add (moreSingularOn_add (moreSingularOn_add
      (moreSingularOn_const_mul hB1nn hB1A1 fun y _ => hbGM y)
      (moreSingularOn_const_mul hB2nn hB2A2 fun y _ => hbPmov y))
      (moreSingularOn_const_mul hB2nn hB2A3 fun y _ => hbPF y))
      (moreSingularOn_const_mul hB2nn hB2A2 fun y _ => hbj y))
      (moreSingularOn_const_mul hB2nn hB2A2 fun y _ => hbHfix y)
  -- step (c): reassemble `ψ_H`
  have hHs : MoreSingularOn
      (fun y => (B2 : EReal) * (ψHfix y + ψPmov y + ψPF y))
      (fun y => (B2 : EReal) * ψH y) univ :=
    moreSingularOn_smul hB2nn hH
  have hc1 : ∀ y : Z,
      (B1 : EReal) * ψGM y + (B2 : EReal) * ψPmov y + (B2 : EReal) * ψPF y
        + (B2 : EReal) * ψj y + (B2 : EReal) * ψHfix y
      = ((B1 : EReal) * ψGM y + (B2 : EReal) * (ψHfix y + ψPmov y + ψPF y))
        + (B2 : EReal) * ψj y := fun y => by
    rw [coe_mul_add hB2nn, coe_mul_add hB2nn]
    abel
  have hc2 : ∀ y : Z,
      ((B1 : EReal) * ψGM y + (B2 : EReal) * ψH y) + (B2 : EReal) * ψj y
      = (B1 : EReal) * ψGM y + (B2 : EReal) * (ψH y + ψj y) := fun y => by
    rw [coe_mul_add hB2nn, add_assoc]
  have hc : MoreSingularOn
      (fun y => (B1 : EReal) * ψGM y + (B2 : EReal) * ψPmov y + (B2 : EReal) * ψPF y
        + (B2 : EReal) * ψj y + (B2 : EReal) * ψHfix y)
      (fun y => (B1 : EReal) * ψGM y + (B2 : EReal) * (ψH y + ψj y)) univ := by
    refine (MoreSingularOn.of_le fun y _ => le_of_eq (hc1 y)).trans ?_
    refine (moreSingularOn_add (moreSingularOn_add
      (MoreSingularOn.refl _ _) hHs) (MoreSingularOn.refl _ _)).trans ?_
    exact MoreSingularOn.of_le fun y _ => le_of_eq (hc2 y)
  exact (ha'.trans hb).trans hc

end Step5

/-! ### Copy-4 Step 5: `eq:QM-lower` and `eq:collar` -/

section Collar

variable {Z W : Type*}

/-- Composition with any map preserves the singularity order, on the preimage. -/
theorem moreSingularOn_comp (f : W → Z) {u v : Z → EReal} {U : Set Z}
    (h : MoreSingularOn u v U) :
    MoreSingularOn (fun w => u (f w)) (fun w => v (f w)) (f ⁻¹' U) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun w hw => hC (f w) hw⟩

/-- **A summand bounded below may be dropped from the more singular side.**  If
`u + w ≤ v + O(1)` on `U` and `w ≥ K` there, then `u ≤ v + O(1)` on `U`.  This is
how Copy-4 removes `ψ_{𝓘_W}` from `eq:IV-H` on a compact `Λ ⊆ U \ W`. -/
theorem moreSingularOn_of_add_le {u v w : Z → EReal} {U : Set Z} {K : ℝ}
    (hw : ∀ x ∈ U, (K : EReal) ≤ w x)
    (h : MoreSingularOn (fun x => u x + w x) v U) :
    MoreSingularOn u v U := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C + -K, fun x hx => ?_⟩
  have hstep : u x + (K : EReal) ≤ v x + (C : EReal) :=
    le_trans (add_le_add le_rfl (hw x hx)) (hC x hx)
  calc u x = u x + (K : EReal) + ((-K : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
    _ ≤ v x + (C : EReal) + ((-K : ℝ) : EReal) := add_le_add hstep le_rfl
    _ = v x + ((C + -K : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]

/-- **`eq:QM-lower`.**  Copy-4 pushes `eq:phiQ-lower` down to `Y` along `π`:
`ψ_{𝔅_M}∘π = ψ_{G̃_M} + O(1)`, `ψ_{𝓘_V}∘π = ψ_H + ψ_{𝓘_W} + O(1)` by `eq:IV-H`,
and `ψ_{𝓘_W}` is bounded below on a compact `Λ ⊆ U \ W`, so it drops out.

Only the halves of the two `O(1)` identities that are actually used are assumed:
`ψ_{G̃_M} ≤ ψ_{𝔅_M}∘π + O(1)` and `ψ_H + ψ_{𝓘_W} ≤ ψ_{𝓘_V}∘π + O(1)`. -/
theorem moreSingularOn_ambientLowerBound
    {π : W → Z} {ψBM ψIV ψj φQ : Z → EReal} {ψGM ψH ψIW : W → EReal}
    {B1 B2 KW : ℝ} {Λ : Set W} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hphiQ : MoreSingularOn
      (fun x => (B1 : EReal) * ψBM x + (B2 : EReal) * (ψIV x + ψj x)) φQ univ)
    (hGM : MoreSingularOn ψGM (fun w => ψBM (π w)) univ)
    (hIV : MoreSingularOn (fun w => ψH w + ψIW w) (fun w => ψIV (π w)) univ)
    (hIWb : ∀ w ∈ Λ, (KW : EReal) ≤ ψIW w) :
    MoreSingularOn
      (fun w => (B1 : EReal) * ψGM w + (B2 : EReal) * (ψH w + ψj (π w)))
      (fun w => φQ (π w)) Λ := by
  have h1 : MoreSingularOn ψH (fun w => ψIV (π w)) Λ :=
    moreSingularOn_of_add_le hIWb (hIV.mono (subset_univ Λ))
  have h2 : MoreSingularOn (fun w => ψH w + ψj (π w))
      (fun w => ψIV (π w) + ψj (π w)) Λ :=
    moreSingularOn_add h1 (MoreSingularOn.refl _ _)
  have h3 := moreSingularOn_smul hB2 h2
  have h4 := moreSingularOn_smul hB1 (hGM.mono (subset_univ Λ))
  have h5 := moreSingularOn_add h4 h3
  have h6 : MoreSingularOn
      (fun w => (B1 : EReal) * ψBM (π w) + (B2 : EReal) * (ψIV (π w) + ψj (π w)))
      (fun w => φQ (π w)) Λ :=
    (moreSingularOn_comp π hphiQ).mono (by simp)
  exact h5.trans h6

/-- **`eq:collar`** (Copy-4, Step 5).  On a compact `Λ ⊆ U \ W`,
`ψ_D + χ ≤ φ_G + C_Λ`, where `ψ_D = ψ_{D-τE_rel} + τψ_{E_rel}` by `eq:def-DLY`
and `φ_G = φ_{Q_M}∘π + τψ_{E_rel}` by Step 3.  The common `τψ_{E_rel}` cancels,
and what is left is the display of `moreSingularOn_exceptionalWeightSum`
compared with `eq:QM-lower` through `moreSingularOn_ambientLowerBound`. -/
theorem moreSingularOn_collar {ψDres ψE χ φQπ φG ψD : Z → EReal} {Λ : Set Z}
    {rhs : Z → EReal} {τ : ℝ}
    (hψD : ∀ y, ψD y = ψDres y + (τ : EReal) * ψE y)
    (hφG : ∀ y, φG y = φQπ y + (τ : EReal) * ψE y)
    (hstep5 : MoreSingularOn (fun y => ψDres y + χ y) rhs univ)
    (hQM : MoreSingularOn rhs φQπ Λ) :
    MoreSingularOn (fun y => ψD y + χ y) φG Λ := by
  have hrearrange : ∀ y : Z, ψD y + χ y
      = (ψDres y + χ y) + (τ : EReal) * ψE y := fun y => by
    rw [hψD y]; abel
  refine (MoreSingularOn.of_le fun y _ => le_of_eq (hrearrange y)).trans ?_
  refine (moreSingularOn_add (hstep5.mono (subset_univ Λ))
    (MoreSingularOn.refl _ _)).trans ?_
  refine (moreSingularOn_add hQM (MoreSingularOn.refl _ _)).trans ?_
  exact MoreSingularOn.of_le fun y _ => le_of_eq (hφG y).symm

end Collar

end

end Hironaka.CollarWeightComparison

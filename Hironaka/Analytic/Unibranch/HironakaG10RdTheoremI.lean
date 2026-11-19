import Hironaka.Analytic.Unibranch.HironakaG10RdInnerSplice
import Hironaka.Analytic.Unibranch.HironakaG10RdRelativeRounds
import Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow

/-!
# Hironaka's double induction `II_{n-1} ⇒ I_n ⇒ II_n` and `HironakaFlattening` from the macro-step (lane G10RD)

Plan items G10-03-13 (base case), G10-03-15 (the well-founded mutual induction, IH eliminated here) and the hand-off
to G10-04-06 (contract `work/hironaka-run0081-20261117/G10RD/G10-03-01-double-induction-contract.md` §3.2).
Source: H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), printed p. 540:
"If n = 0, then Theorems I_n and II_n are obviously true. The inductive proof … will be carried out in the order
II_{n-1} ⇒ I_n and I_n ⇒ II_n"; pp. 541–546.

The dimension bound is an abstract predicate `dim n s B` ("`dim B ≤ n`") with exactly the four properties Hironaka
uses (G10-03-01 §2.1, lane G10EP's D1–D4): `hD2` (dimension `0` ⇒ flat over `B`), `hD3` (stable under strict
transforms), `hD4` (a compact base has finite dimension), `hmono`. Hironaka's index `i` is an abstract measure `μ`.

* `theoremII_zero` — the base case (G10-03-13);
* `theoremII_of_theoremI` — `I_n ⇒ II_n` (`HironakaG10RdRelativeRounds.exists_flatOverB_of_theoremI`);
* `theoremI_succ_of_macroStep` — `II_n ⇒ I_{n+1}` from the macro-step (Hironaka pp. 541–544, by induction on `μ`,
  `HironakaG10RdInnerSplice.exists_openTracked_of_macroStep`); runs keep compactness, properness and `dim`;
* `theoremI_all` — **the double induction**: every `I_{n+1}` from the base case and the macro-steps; the
  lower-dimensional hypothesis is eliminated;
* `hI_of_macroStep`, **`nonempty_roundData_of_macroStep`**, **`hironakaFlattening_of_macroStep`** — `hI` of
  `HironakaG10RdRoundMachine.nonempty_roundData_of_theoremI`, round data, and `HironakaFlattening`, from: the
  macro-step, relative round covers, and the dimension properties (the local input is lane G10MW's PROVED
  `HironakaG10MwNativeWindow.persistentLocalFlattener`).

No named input is introduced; the remaining hypotheses are the macro-step (G10-03-07 … 11), relative round covers
(G10-03-04.a, lane G10TM) and D2–D4 (G10-03-14, lane G10EP).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdTheoremI

open Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdFinish
  Hironaka.Analytic.Unibranch.HironakaG10RdInnerSplice
  Hironaka.Analytic.Unibranch.HironakaG10RdRoundMachine
  Hironaka.Analytic.Unibranch.HironakaG10RdRelativeRounds
  Hironaka.Analytic.Unibranch.HironakaG10TmTermination

noncomputable section

variable (dim : ℕ → ∀ s : Stage, Set s.X.obj.left → Prop)

/-- Hironaka's Theorem `I_n` for data with `dim B ≤ n` (the statement, p. 540). -/
abbrev TheoremI (n : ℕ) : Prop :=
  ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
    IsProperMap s.f.hom.left.base → dim n s R.B → ∃ l : PermRun s R, OpenTracked l.final.2

/-- Hironaka's Theorem `II_n` for data with `dim B ≤ n` (the statement, p. 540). -/
abbrev TheoremII (n : ℕ) : Prop :=
  ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
    IsProperMap s.f.hom.left.base → dim n s R.B → ∃ l : PermRun s R, FlatOverB l.final.2

/-- **The base case** (p. 540, "obviously true"): over a set of dimension `0` the family is flat. -/
theorem theoremII_zero (hD2 : ∀ (s : Stage) (B : Set s.X.obj.left), dim 0 s B → relNonflat s.f B = ∅) :
    TheoremII dim 0 :=
  fun s _ R _ _ h => ⟨.nil s R, hD2 s R.B h⟩

/-- **`I_n ⇒ II_n`** (pp. 544–546). -/
theorem theoremII_of_theoremI
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (n : ℕ) (hI : TheoremI dim n) : TheoremII dim n :=
  fun s _ R hc hp h => exists_flatOverB_of_theoremI HironakaG10MwNativeWindow.persistentLocalFlattener
    (dim n) (hD3 n) hcover hI s hc hp R h

/-- Runs keep compactness, properness and the dimension bound. -/
theorem permRun_final_props
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B)) (n : ℕ) {q : ℕ} :
    {s : Stage} → {R : FDatum s q} → (l : PermRun s R) →
      (CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ dim n s R.B) →
        (CompactSpace l.final.1.X.obj.left ∧ IsProperMap l.final.1.f.hom.left.base ∧
          dim n l.final.1 l.final.2.B)
  | _, _, .nil _ _, h => h
  | s, _, .cons _ _ st rest, ⟨hc, hp, hd⟩ => by
      have : CompactSpace s.X.obj.left := hc
      refine permRun_final_props hD3 n rest ⟨compactSpace_nextWith s st.c, ?_, ?_⟩
      · let _ := st.c.finiteType
        exact strictP_isProperMap _ _ _ _ hp
      · rw [st.next_B]
        exact hD3 n s st.c _ hd

/-- **`II_n ⇒ I_{n+1}`** (pp. 541–544) from the macro-step at `dim ≤ n + 1`: a permissible run lowering Hironaka's
index `μ`, or ending with open tracked supports when `μ = 0`. -/
theorem theoremI_succ_of_macroStep
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (μ : ∀ (s : Stage) (q : ℕ), FDatum s q → ℕ) (n : ℕ)
    (hmacro : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B →
        ∃ l : PermRun s R, (μ s q R = 0 → OpenTracked l.final.2) ∧
          (0 < μ s q R → μ l.final.1 q l.final.2 < μ s q R)) :
    TheoremI dim (n + 1) := by
  intro s q R hc hp h
  refine exists_openTracked_of_macroStep
    (fun s _ R => CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ dim (n + 1) s R.B) μ
    (fun s q R hP => ?_) s q R ⟨hc, hp, h⟩
  obtain ⟨l, h0, hlt⟩ := hmacro s q R hP.1 hP.2.1 hP.2.2
  exact ⟨l, permRun_final_props dim hD3 (n + 1) l hP, h0, hlt⟩

/-- **The double induction** (p. 540): from the base case and the macro-steps (each using the lower-dimensional
Theorem `II_n` as its hypothesis), Theorem `I_{n+1}` holds for every `n`. -/
theorem theoremI_all
    (hD2 : ∀ (s : Stage) (B : Set s.X.obj.left), dim 0 s B → relNonflat s.f B = ∅)
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (μ : ∀ (s : Stage) (q : ℕ), FDatum s q → ℕ)
    (hmacro : ∀ n : ℕ, TheoremII dim n →
      ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
        IsProperMap s.f.hom.left.base → dim (n + 1) s R.B →
          ∃ l : PermRun s R, (μ s q R = 0 → OpenTracked l.final.2) ∧
            (0 < μ s q R → μ l.final.1 q l.final.2 < μ s q R)) :
    ∀ n, TheoremI dim (n + 1) := by
  intro n
  induction n with
  | zero => exact theoremI_succ_of_macroStep dim hD3 μ 0 (hmacro 0 (theoremII_zero dim hD2))
  | succ n ih =>
    exact theoremI_succ_of_macroStep dim hD3 μ (n + 1)
      (hmacro (n + 1) (theoremII_of_theoremI dim hD3 hcover (n + 1) ih))

/-- **`hI` of `nonempty_roundData_of_theoremI`** (Theorem `I_n` with `B = X`). -/
theorem hI_of_macroStep
    (hD2 : ∀ (s : Stage) (B : Set s.X.obj.left), dim 0 s B → relNonflat s.f B = ∅)
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (hD4 : ∀ s : Stage, CompactSpace s.X.obj.left → ∃ n, dim n s univ)
    (hmono : ∀ (n : ℕ) (s : Stage) (B : Set s.X.obj.left), dim n s B → dim (n + 1) s B)
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (μ : ∀ (s : Stage) (q : ℕ), FDatum s q → ℕ)
    (hmacro : ∀ n : ℕ, TheoremII dim n →
      ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
        IsProperMap s.f.hom.left.base → dim (n + 1) s R.B →
          ∃ l : PermRun s R, (μ s q R = 0 → OpenTracked l.final.2) ∧
            (0 < μ s q R → μ l.final.1 q l.final.2 < μ s q R)) :
    ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∃ l : PermRun s R, ∀ p, IsRelOpen l.final.2.B (l.final.2.Z p).support := by
  intro s q R hc hp hB
  obtain ⟨n, hn⟩ := hD4 s hc
  exact theoremI_all dim hD2 hD3 hcover μ hmacro n s q R hc hp (hB ▸ hmono n s univ hn)

/-- **Round data from the macro-step** (with relative round covers and the dimension properties). -/
theorem nonempty_roundData_of_macroStep
    (hD2 : ∀ (s : Stage) (B : Set s.X.obj.left), dim 0 s B → relNonflat s.f B = ∅)
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (hD4 : ∀ s : Stage, CompactSpace s.X.obj.left → ∃ n, dim n s univ)
    (hmono : ∀ (n : ℕ) (s : Stage) (B : Set s.X.obj.left), dim n s B → dim (n + 1) s B)
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (μ : ∀ (s : Stage) (q : ℕ), FDatum s q → ℕ)
    (hmacro : ∀ n : ℕ, TheoremII dim n →
      ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
        IsProperMap s.f.hom.left.base → dim (n + 1) s R.B →
          ∃ l : PermRun s R, (μ s q R = 0 → OpenTracked l.final.2) ∧
            (0 < μ s q R → μ l.final.1 q l.final.2 < μ s q R))
    (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left) (hf : IsProperMap s₀.f.hom.left.base) :
    Nonempty (RoundData s₀ hf) :=
  nonempty_roundData_of_theoremI s₀ hX hf
    (fun s hc hp => by
      obtain ⟨m, Z, hZ⟩ := hcover s hc hp univ isClosed_univ
      exact ⟨m, Z, (relNonflat_univ_eq_nonflatImage s.f).symm ▸ hZ⟩)
    (hI_of_macroStep dim hD2 hD3 hD4 hmono hcover μ hmacro)

/-- **`HironakaFlattening` from the macro-step** (with relative round covers and the dimension properties; the
local input is lane G10MW's proved `persistentLocalFlattener`). -/
theorem hironakaFlattening_of_macroStep
    (hD2 : ∀ (s : Stage) (B : Set s.X.obj.left), dim 0 s B → relNonflat s.f B = ∅)
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (hD4 : ∀ s : Stage, CompactSpace s.X.obj.left → ∃ n, dim n s univ)
    (hmono : ∀ (n : ℕ) (s : Stage) (B : Set s.X.obj.left), dim n s B → dim (n + 1) s B)
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (μ : ∀ (s : Stage) (q : ℕ), FDatum s q → ℕ)
    (hmacro : ∀ n : ℕ, TheoremII dim n →
      ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
        IsProperMap s.f.hom.left.base → dim (n + 1) s R.B →
          ∃ l : PermRun s R, (μ s q R = 0 → OpenTracked l.final.2) ∧
            (0 < μ s q R → μ l.final.1 q l.final.2 < μ s q R)) :
    HironakaFlattening :=
  hironakaFlattening_of_roundData HironakaG10MwNativeWindow.persistentLocalFlattener
    fun s₀ hX hf => nonempty_roundData_of_macroStep dim hD2 hD3 hD4 hmono hcover μ hmacro s₀ hX hf

end

end Hironaka.Analytic.Unibranch.HironakaG10RdTheoremI

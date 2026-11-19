import Hironaka.Analytic.Unibranch.HironakaG10RdEndToEnd
import Hironaka.Analytic.Unibranch.HironakaG10EpS3

/-!
# The flattening theorem from Frisch's theorems and Lemma 4.4.5 (lane G10RD)

Final splice of the G10-03 chain (Hironaka 1975, Theorems `I_n`/`II_n`, printed pp. 540–547).  The remaining inputs
are exactly:

* `hF1` — Frisch's Th. (IV,9) with Remmert's proper mapping theorem: on every compact stage with a proper family the
  relative non-flat set of an analytic set is analytic (J. Frisch, Invent. Math. 4 (1967), printed p. 133);
* `hF2` — Frisch's Prop. (IV,14): it is nowhere dense in it (printed p. 135);
* `hT` — Hironaka's Lemma 4.4.5 (printed pp. 537–538) for one sum-centre step, for every local flattener (lane G10SB).

`C_i` analytic and closed (Lemma 4.5.1), D1–D4, the relative round covers, S3 (lane G10EP,
`HironakaG10EpS3.hS3_of_stratification`) and the `D_β` step (Lemmas 4.5.2–4.5.5) are all derived from `hF1`, `hF2`.

* **`hironakaFlattening_of_frisch`** — `HironakaFlattening` from `hF1`, `hF2`, `hT`;
* **`macroStep_of_frisch`**, **`theoremI_of_frisch`** — the macro-step and Theorem `I_n` (with `B = X`, the `hI` of
  `HironakaG10RdRoundMachine.nonempty_roundData_of_theoremI`) from the same inputs;
* **`nonempty_roundData_of_frisch`** — complete `RoundData` (the G10-03 deliverable: compatible global centres and
  tracked sets for `HironakaG10ChowLeavingRounds.exists_flattening_of_roundData`) from the same inputs.

No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdFinal

open Hironaka HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover
  Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep
  Hironaka.Analytic.Unibranch.HironakaG10RdLemma455
  Hironaka.Analytic.Unibranch.HironakaG10RdTheoremI
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdEndToEnd
  Hironaka.Analytic.Unibranch.HironakaG10EpS3
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- **Hironaka's flattening theorem from Frisch's two theorems and Lemma 4.4.5 for sum centres.** -/
theorem hironakaFlattening_of_frisch
    (hF1 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z) :
    HironakaFlattening :=
  hironakaFlattening_of_inputs (fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩) hT
    fun n s q R hc hp hd _ l hl =>
      hS3_of_stratification dimA hF1 hF2 (fun _ _ _ h => h.1)
        (hC_dimA fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩) n s q R hc hp hd l hl

/-- **The macro-step of Theorem `I_{n+1}`** (Hironaka pp. 543–544) from Frisch's theorems and Lemma 4.4.5. -/
theorem macroStep_of_frisch
    (hF1 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z) :
    ∀ n : ℕ, TheoremII dimA n →
      ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
        IsProperMap s.f.hom.left.base → dimA (n + 1) s R.B →
          ∃ l : PermRun s R, (topIndexOf R = 0 → OpenTracked l.final.2) ∧
            (0 < topIndexOf R → topIndexOf l.final.2 < topIndexOf R) :=
  fun n hII => macroStep_of_S3_Dβ dimA (hD1_dimA fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩)
    (hC_dimA fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩)
    (hS3_of_stratification dimA hF1 hF2 (fun _ _ _ h => h.1)
      (hC_dimA fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩))
    (hDβ_of_frisch dimA (fun _ _ _ h => h.1) (fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩) hT)
    hD3_dimA n hII

/-- **Theorem `I_n` with `B = X`** (the `hI` of `HironakaG10RdRoundMachine.nonempty_roundData_of_theoremI`) from
Frisch's theorems and Lemma 4.4.5. -/
theorem theoremI_of_frisch
    (hF1 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z) :
    ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∃ l : PermRun s R, ∀ p, IsRelOpen l.final.2.B (l.final.2.Z p).support :=
  hI_of_macroStep dimA hD2_dimA hD3_dimA hD4_dimA hmono_dimA
    (relHcover_of_frisch fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩) (fun _ _ R => topIndexOf R)
    (macroStep_of_frisch hF1 hF2 hT)

/-- **Complete round data** (the deliverable of G10-03: compatible global centres, tracked sets and `RoundData` for
`HironakaG10ChowLeavingRounds.exists_flattening_of_roundData`) from Frisch's theorems and Lemma 4.4.5. -/
theorem nonempty_roundData_of_frisch
    (hF1 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z)
    (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left) (hf : IsProperMap s₀.f.hom.left.base) :
    Nonempty (RoundData s₀ hf) :=
  nonempty_roundData_of_macroStep dimA hD2_dimA hD3_dimA hD4_dimA hmono_dimA
    (relHcover_of_frisch fun s hc hp => ⟨hF1 s hc hp, hF2 s hc hp⟩) (fun _ _ R => topIndexOf R)
    (macroStep_of_frisch hF1 hF2 hT) s₀ hX hf

end

end Hironaka.Analytic.Unibranch.HironakaG10RdFinal

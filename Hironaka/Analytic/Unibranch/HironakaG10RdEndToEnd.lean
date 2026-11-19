import Hironaka.Analytic.Unibranch.HironakaG10RdLemma455
import Hironaka.Analytic.Unibranch.HironakaG10EpNativeDim
import Hironaka.Analytic.Unibranch.HironakaG10EpStrictAnalytic

/-!
# The end-to-end flattening theorem from the remaining inputs (lane G10RD)

Final assembly of the G10-03 chain (Hironaka 1975, Theorems `I_n`/`II_n`, printed pp. 540–547) with every remaining
input as an explicit hypothesis, one per input, so that the final splice is mechanical:

* `hFrisch` — Frisch's two theorems on every compact stage with a proper family (J. Frisch, Invent. Math. 4 (1967),
  Th. (IV,9) with Remmert's proper mapping theorem, and Prop. (IV,14)), in exactly the form of lane G10TM's
  `HironakaG10TmFlattenerCover.hcover_of_frisch`;
* `hT` — Hironaka's Lemma 4.4.5 (printed pp. 537–538) for one sum-centre step, for every local flattener (lane G10SB,
  `HironakaG10SbTransportClosed.exists_localFlattener_transport_of_germs` once its support-germ hypothesis is proved);
* `hS3` — S3 (plan item L2, lane G10EP): after the lower-dimensional run on `C_i` the index is unchanged and the family
  is flat over the new `C_i` (Hironaka p. 544, "the integer i is not affected by Π_1 applied to R").

Everything else is proved: the dimension predicate `dimA` (analytic of native dimension `≤ n`) with D1–D4 (lane G10EP),
the relative round covers (lane G10TM), `C_i` analytic and closed (Lemma 4.5.1), the `D_β` step with Lemmas
4.5.2–4.5.5 (`HironakaG10RdLemma455.hDβ_of_frisch`), the double induction (`HironakaG10RdTheoremI`) and the local
input (`HironakaG10MwNativeWindow.persistentLocalFlattener`).

* `dimA` (a predicate, not an input) and **`hD1_dimA`**, `hD2_dimA`, `hD3_dimA`, `hD4_dimA`, `hmono_dimA` — the dimension properties;
* **`hironakaFlattening_of_inputs`** — `HironakaFlattening` from `hFrisch`, `hT`, `hS3`.

No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdEndToEnd

open Hironaka HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover
  Hironaka.Analytic.Unibranch.HironakaG10EpNativeDim
  Hironaka.Analytic.Unibranch.HironakaG10EpStrictAnalytic
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdStratification
  Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep
  Hironaka.Analytic.Unibranch.HironakaG10RdLemma455
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- Hironaka's dimension predicate for the double induction: `B` is analytic of native dimension `≤ n`. -/
abbrev dimA (n : ℕ) (s : Stage) (B : Set s.X.obj.left) : Prop :=
  s.X.IsAnalyticSubset B ∧ NativeDimLE s.X B n

/-- **D1 for `C_i`** (Hironaka p. 544, "dim C_i < n"): `C_i` is analytic (Lemma 4.5.1) and nowhere dense in `B`
(Frisch (IV,14)). -/
theorem hD1_dimA (hFrisch : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A)) ∧
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))) :
    ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dimA (n + 1) s R.B → dimA n s (csetOf R) :=
  fun _ s _ R hc hp hd =>
    ⟨(csetOf_analytic_closed R (hFrisch s hc hp).1 (hFrisch s hc hp).2 hd.1).1,
      nativeDimLE_of_analytic_subset_of_dense hd.1
        (csetOf_analytic_closed R (hFrisch s hc hp).1 (hFrisch s hc hp).2 hd.1).1
        (cset_subset_B R _)
        (subset_closure_diff_cset s.f (hFrisch s hc hp).2 hd.1 (fun p => (R.Z p).support) _) hd.2⟩

/-- **`C_i` is closed** (Lemma 4.5.1). -/
theorem hC_dimA (hFrisch : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A)) ∧
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))) :
    ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dimA (n + 1) s R.B → IsClosed (csetOf R) :=
  fun _ s _ R hc hp hd => (csetOf_analytic_closed R (hFrisch s hc hp).1 (hFrisch s hc hp).2 hd.1).2

/-- **D2.** -/
theorem hD2_dimA : ∀ (s : Stage) (B : Set s.X.obj.left), dimA 0 s B → relNonflat s.f B = ∅ :=
  fun s _ h => relNonflat_eq_empty_of_nativeDimLE_zero s.f h.1 h.2

/-- **D3.** -/
theorem hD3_dimA : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dimA n s B →
    dimA n (nextWith s c) (strictSet s c B) :=
  fun _ s c _ h => analytic_nativeDimLE_strictSet s c h

/-- **D4.** -/
theorem hD4_dimA : ∀ s : Stage, CompactSpace s.X.obj.left → ∃ n, dimA n s univ := fun s _ => by
  obtain ⟨n, hn⟩ := exists_nativeDimLE_univ s.X
  exact ⟨n, s.X.isAnalyticSubset_univ, hn⟩

/-- Monotonicity of the dimension predicate. -/
theorem hmono_dimA : ∀ (n : ℕ) (s : Stage) (B : Set s.X.obj.left), dimA n s B → dimA (n + 1) s B :=
  fun n _ _ h => ⟨h.1, h.2.mono (Nat.le_succ n)⟩

/-- **The flattening theorem from the remaining inputs** (Hironaka 1975, Theorems `I_n`/`II_n`): Frisch's theorems
(`hFrisch`), Lemma 4.4.5 for sum centres (`hT`) and S3 (`hS3`). -/
theorem hironakaFlattening_of_inputs (hFrisch : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A)) ∧
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A)))
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z)
    (hS3 : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dimA (n + 1) s R.B → ∀ (hC : IsClosed (csetOf R))
      (l : PermRun s (R.withB (csetOf R) hC)), FlatOverB l.final.2 →
        topIndexOf (liftRun R hC l).final.2 = topIndexOf R ∧
          relNonflat (liftRun R hC l).final.1.f (csetOf (liftRun R hC l).final.2) = ∅) :
    HironakaFlattening :=
  hironakaFlattening_of_S3_Dβ dimA (hD1_dimA hFrisch) hD2_dimA hD3_dimA hD4_dimA hmono_dimA
    (relHcover_of_frisch hFrisch) (hC_dimA hFrisch)
    (fun n s q R hc hp hd l hl => hS3 n s q R hc hp hd _ l hl)
    (hDβ_of_frisch dimA (fun _ _ _ h => h.1) hFrisch hT)

end

end Hironaka.Analytic.Unibranch.HironakaG10RdEndToEnd

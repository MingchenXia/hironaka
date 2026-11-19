import Hironaka.Analytic.Unibranch.HironakaG10RdTheoremI
import Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex

/-!
# The macro-step of Theorem `I_n` from S3 and one `D_β` step (lane G10RD)

Plan items G10-03-10/11/12 (composition; contract `G10-03-01-double-induction-contract.md` §3.2 (a)–(c)). Source:
H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), end of the proof of
`II_{n-1} ⇒ I_n`, printed pp. 543–544: apply `II_{n-1}` to `R̄ = (F, f; C_i; V_p, Z_p)` ("dim C_i < n"); "the integer
i is not affected by Π_1 applied to R"; then the `D_β` step (Lemmas 4.5.2–4.5.5).

* `topIndexOf` — Hironaka's index `i` of an (F)-datum (`HironakaG10RdTopIndex.topIndex` of its tracked supports,
  `0` if no bound exists);
* `cset_subset_B` — `C_i ⊆ B`;
* **`macroStep_of_S3_Dβ`** — the macro-step in the form consumed by `HironakaG10RdTheoremI.theoremI_succ_of_macroStep`
  (measure `topIndexOf`), from: Theorem `II_n` (the lower-dimensional hypothesis), the dimension drop for `C_i`
  (`hD1`, lane G10EP + Frisch), closedness of `C_i` (`hC`, Lemma 4.5.1 under the stratification contract), **S3**
  (`hS3`: after the lower-dimensional run the index is unchanged and the family is flat over the new `C_i`;
  plan item L2), and **one `D_β` step** (`hDβ`: Lemmas 4.5.2–4.5.5; plan item L4);
* **`hironakaFlattening_of_S3_Dβ`** — `HironakaFlattening` from the same inputs plus the dimension properties and
  relative round covers.

No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
  Hironaka.Analytic.Unibranch.HironakaG10RdTheoremI

noncomputable section

/-- **Hironaka's index `i` of an (F)-datum** (p. 543), `0` when no bound of the bad component indices exists. -/
def topIndexOf {s : Stage} {q : ℕ} (R : FDatum s q) : ℕ := by
  classical
  exact if h : ∃ i, ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ i then
    topIndex s.f R.B (fun p => (R.Z p).support) h else 0

/-- The selected set `C_i` of a datum at its index. -/
abbrev csetOf {s : Stage} {q : ℕ} (R : FDatum s q) : Set s.X.obj.left :=
  Cset s.f R.B (fun p => (R.Z p).support) (topIndexOf R)

theorem cset_subset_B {s : Stage} {q : ℕ} (R : FDatum s q) (i : ℕ) :
    Cset s.f R.B (fun p => (R.Z p).support) i ⊆ R.B :=
  fun _ hx => (cset_subset_relNonflat (f := s.f) (B := R.B) (Z := fun p => (R.Z p).support) i hx).1

/-- A run permissible for `R̄ = R.withB C_i`, read as a run of `R` (same centres; Hironaka p. 544). -/
def liftRun {s : Stage} {q : ℕ} (R : FDatum s q) (hC : IsClosed (csetOf R))
    (l : PermRun s (R.withB (csetOf R) hC)) : PermRun s R :=
  PermRun.liftB (R' := R.withB (csetOf R) hC) R rfl (cset_subset_B R _) l

variable (dim : ℕ → ∀ s : Stage, Set s.X.obj.left → Prop)

/-- **The macro-step of Theorem `I_{n+1}`** (pp. 543–544): the lower-dimensional run of `II_n` on `C_i`, read as a
run of `R`, followed by one `D_β` step. -/
theorem macroStep_of_S3_Dβ
    (hD1 : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → dim n s (csetOf R))
    (hC : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → IsClosed (csetOf R))
    (hS3 : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q) (hc : CompactSpace s.X.obj.left)
      (hp : IsProperMap s.f.hom.left.base) (hd : dim (n + 1) s R.B)
      (l : PermRun s (R.withB (csetOf R) (hC n s q R hc hp hd))), FlatOverB l.final.2 →
        topIndexOf (liftRun R _ l).final.2 = topIndexOf R ∧
          relNonflat (liftRun R _ l).final.1.f
            (csetOf (liftRun R _ l).final.2) = ∅)
    (hDβ : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → relNonflat s.f (csetOf R) = ∅ →
        ∃ st : PermStep R, (topIndexOf R = 0 → OpenTracked st.next) ∧
          (0 < topIndexOf R → topIndexOf st.next < topIndexOf R))
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (n : ℕ) (hII : TheoremII dim n) :
    ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B →
        ∃ l : PermRun s R, (topIndexOf R = 0 → OpenTracked l.final.2) ∧
          (0 < topIndexOf R → topIndexOf l.final.2 < topIndexOf R) := by
  intro s q R hc hp hd
  obtain ⟨l₁, hl₁⟩ := hII s q (R.withB (csetOf R) (hC n s q R hc hp hd)) hc hp (hD1 n s q R hc hp hd)
  obtain ⟨hidx, hflat⟩ := hS3 n s q R hc hp hd l₁ hl₁
  obtain ⟨hc₁, hp₁, hd₁⟩ := permRun_final_props dim hD3 (n + 1)
    (liftRun R _ l₁) ⟨hc, hp, hd⟩
  obtain ⟨st, h0, hlt⟩ := hDβ n _ q _ hc₁ hp₁ hd₁ hflat
  refine ⟨(liftRun R _ l₁).append (.cons _ _ st (.nil _ _)), ?_, ?_⟩
  · intro hz
    rw [PermRun.final_append]
    exact h0 (hidx.trans hz)
  · intro hpos
    rw [PermRun.final_append]
    exact (hlt (by rw [hidx]; exact hpos)).trans_eq hidx

/-- **`HironakaFlattening` from S3 and the `D_β` step** (with the dimension properties, closedness of `C_i`, and
relative round covers; the local input is lane G10MW's proved `persistentLocalFlattener`). -/
theorem hironakaFlattening_of_S3_Dβ
    (hD1 : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → dim n s (csetOf R))
    (hD2 : ∀ (s : Stage) (B : Set s.X.obj.left), dim 0 s B → relNonflat s.f B = ∅)
    (hD3 : ∀ (n : ℕ) (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), dim n s B →
      dim n (nextWith s c) (strictSet s c B))
    (hD4 : ∀ s : Stage, CompactSpace s.X.obj.left → ∃ n, dim n s univ)
    (hmono : ∀ (n : ℕ) (s : Stage) (B : Set s.X.obj.left), dim n s B → dim (n + 1) s B)
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (hC : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → IsClosed (csetOf R))
    (hS3 : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q) (hc : CompactSpace s.X.obj.left)
      (hp : IsProperMap s.f.hom.left.base) (hd : dim (n + 1) s R.B)
      (l : PermRun s (R.withB (csetOf R) (hC n s q R hc hp hd))), FlatOverB l.final.2 →
        topIndexOf (liftRun R _ l).final.2 = topIndexOf R ∧
          relNonflat (liftRun R _ l).final.1.f
            (csetOf (liftRun R _ l).final.2) = ∅)
    (hDβ : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → relNonflat s.f (csetOf R) = ∅ →
        ∃ st : PermStep R, (topIndexOf R = 0 → OpenTracked st.next) ∧
          (0 < topIndexOf R → topIndexOf st.next < topIndexOf R)) :
    HironakaFlattening :=
  hironakaFlattening_of_macroStep dim hD2 hD3 hD4 hmono hcover (fun _ _ R => topIndexOf R)
    fun n hII => macroStep_of_S3_Dβ dim hD1 hC hS3 hDβ hD3 n hII

end

end Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep

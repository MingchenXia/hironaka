import Hironaka.Resolution.HironakaSmoothSubmersionRelativePartsCompanion
import Hironaka.Resolution.HironakaActualProjectionTestRecord
import Hironaka.Resolution.HironakaG8LogMixedHistory
import Hironaka.Resolution.HironakaG8MixedBoundaryExponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion ideal under a product with a line (G8C lane, run 0080; (B') P5, E4c)

Blueprint: `hironaka-g8-e4c-product.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P5, E4c); lane G8
`REPORT-r4.md` ("P5 E4c": products via `markedPullback_companionOf` plus the remark that the new horizontal member has
exponent `0` along the carrier).  Source: Bierstone--Milman 2008, Definition 2.4 (the test transformation (ii), product
with a line, with the new boundary member `X × {0}`) and §5 (monomial and nonmonomial parts, the companion ideal).

The product test `projectionTest A = (N × ℂ, (E_i × ℂ)_i ++ [X × 0], pr^*𝔞, d)` adds the horizontal member `X × {0}`
(`HironakaActualProjectionTestRecord`).  The pullback of a coherent ideal nonzero along `N` is divisible by no power of the
coordinate `t` along `N × ℂ`, so this member has exponent `0` and changes neither part:

* `divExpAlong_congr_of_iff` (exponents from divisibility predicates, across spaces), `isDivNearAlong_fst_iff`,
  `divExpAlong_fst`: exponents along `N × ℂ` of the members `H × ℂ` are those along `N` of `H`;
* `divExpAlong_horizontal_eq_zero`: the horizontal member has exponent `0` (nonzero along `N`);
* `monomialPartAlong_append_of_eq_zero`, `nonmonomialPartAlong_append_of_eq_zero`: a member of exponent `0` changes
  neither part;
* `monomialPartAlong_projectionTest`, `nonmonomialPartAlong_projectionTest`: the parts of the product are the pullbacks;
* **`companionOf_projectionTest`**: `𝓞(projectionTest A, o) = projectionTest 𝓞(A, o)`;
* `ordGe_projectionTest`, `cosupp_projectionTest`, `bound_projectionTest`: orders, cosupports and the bound
  `ord(𝓝|_N) ≤ o` pull back;
* `RestrictEquiv.projectionTest`: restricted equivalence passes to products;
* **`expAgree_projectionTest`** (universe `0`): agreement of boundary exponents passes to products.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8E4cProduct

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.GermIdealOrder
  Hironaka.IdealWeightPowers Hironaka.DivisorExponentAlong
  Hironaka.MonomialPartAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.RelativePrincipalizationSpan Hironaka.RestrictedIdealWeight
  Hironaka.RestrictedIdealQuotient
open Hironaka.CompanionRebase (companionOf)
open Hironaka.CompanionReductionAlong (companionAlong companionAlong_N companionAlong_E)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal)
open Hironaka.HironakaSmoothSubmersionCoefficientIdeals (markedPullback)
open Hironaka.NonmonomialOrderLocal (ordGe)
open Hironaka.HironakaG8LogMixedHistory (restrictLe_pullback_of_restrictLe)
open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ}

/-! ### Exponents from divisibility predicates -/

section Exponent

variable {m m' : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel m') M']

/-- **The exponent along `H` is determined by the divisibility predicates** (possibly on different manifolds). -/
theorem divExpAlong_congr_of_iff {N H : Set M} {I : GermIdeal m M} {x : M} {N' H' : Set M'}
    {J : GermIdeal m' M'} {x' : M'} (h : ∀ e, IsDivNearAlong m N I H e x ↔ IsDivNearAlong m' N' J H' e x') :
    divExpAlong m N I H x = divExpAlong m' N' J H' x' := by
  classical
  have hex : (∃ e, ¬ IsDivNearAlong m N I H (e + 1) x) ↔ ∃ e, ¬ IsDivNearAlong m' N' J H' (e + 1) x' :=
    exists_congr fun e => not_congr (h (e + 1))
  by_cases hE : ∃ e, ¬ IsDivNearAlong m N I H (e + 1) x
  · have hE' := hex.mp hE
    simp only [divExpAlong, dif_pos hE, dif_pos hE']
    exact Nat.find_congr' fun {e} => not_congr (h (e + 1))
  · have hE' : ¬ ∃ e, ¬ IsDivNearAlong m' N' J H' (e + 1) x' := fun h' => hE (hex.mpr h')
    simp only [divExpAlong, dif_neg hE, dif_neg hE']

/-- The exponent is `0` as soon as divisibility by the first power fails. -/
theorem divExpAlong_eq_zero_of_not {N H : Set M} {I : GermIdeal m M} {x : M}
    (h : ¬ IsDivNearAlong m N I H 1 x) : divExpAlong m N I H x = 0 := by
  classical
  have hE : ∃ e, ¬ IsDivNearAlong m N I H (e + 1) x := ⟨0, h⟩
  simp only [divExpAlong, dif_pos hE]
  exact (Nat.find_eq_zero hE).mpr h

end Exponent

/-! ### A member of exponent `0` changes neither part -/

section Append

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {I : GermIdeal n M} {E : List (Set M)} {H : Set M}

/-- **Appending a member of exponent `0` does not change the monomial part.** -/
theorem monomialPartAlong_append_of_eq_zero (h : ∀ y ∈ N, y ∈ H → divExpAlong n N I H y = 0) :
    monomialPartAlong n N I (E ++ [H]) = monomialPartAlong n N I E := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ?_)
  rw [MonomialPartEtale.monomialPartAlong_mem_iff', MonomialPartEtale.monomialPartAlong_mem_iff']
  refine ⟨fun hg => ⟨hg.1, fun H' hH' => hg.2 H' (List.mem_append_left _ hH')⟩, fun hg => ⟨hg.1, ?_⟩⟩
  intro H' hH' hyN hyH
  rcases List.mem_append.mp hH' with hH' | hH'
  · exact hg.2 H' hH' hyN hyH
  · rw [List.mem_singleton.mp hH'] at hyH ⊢
    rw [h y hyN hyH, idealPow_zero]
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self (S := (unitIdeal n M).mem _) hg.1 hg.1)

/-- **Appending a member of exponent `0` does not change the nonmonomial part.** -/
theorem nonmonomialPartAlong_append_of_eq_zero (h : ∀ y ∈ N, y ∈ H → divExpAlong n N I H y = 0) :
    nonmonomialPartAlong n N I (E ++ [H]) = nonmonomialPartAlong n N I E := by
  unfold nonmonomialPartAlong
  rw [monomialPartAlong_append_of_eq_zero h]

end Append

/-! ### The product with a line -/

section Product

variable {X : CMfd.{u} n}

/-- **Divisibility along `H × ℂ` inside `N × ℂ` is divisibility along `H` inside `N`** (coherent ideal). -/
theorem isDivNearAlong_fst_iff {N H : Set X} {I : GermIdeal n X} (hI : I.IsCoherent) (e : ℕ)
    (p : projectionAmbient X) :
    IsDivNearAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' N)
        (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) I)
        ((Prod.fst : projectionAmbient X → X) ⁻¹' H) e p ↔ IsDivNearAlong n N I H e p.1 := by
  have hsub := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  unfold IsDivNearAlong
  rw [HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq (Y := projectionAmbient X) hsub hI N e]
  have hmap : Filter.map (Prod.fst : projectionAmbient X → X) (𝓝 p) = 𝓝 p.1 := map_fst_nhds p
  rw [← hmap, Filter.eventually_map]
  rfl

/-- **The exponents along `N × ℂ` of the members `H × ℂ`** are those along `N` of `H`. -/
theorem divExpAlong_fst {N H : Set X} {I : GermIdeal n X} (hI : I.IsCoherent) (p : projectionAmbient X) :
    divExpAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' N)
        (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) I)
        ((Prod.fst : projectionAmbient X → X) ⁻¹' H) p = divExpAlong n N I H p.1 :=
  divExpAlong_congr_of_iff fun e => isDivNearAlong_fst_iff hI e p

/-- **The horizontal member has exponent `0`** along `N × ℂ` (the ideal coherent and nonzero along `N`). -/
theorem divExpAlong_horizontal_eq_zero {N : Set X} {I : GermIdeal n X} (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) {p : projectionAmbient X} (hpN : p.1 ∈ N) (hp : p ∈ horizontal X) :
    divExpAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' N)
      (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) I) (horizontal X) p = 0 := by
  have hsub := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  refine divExpAlong_eq_zero_of_not fun hdiv => ?_
  have hp0 : p.2 = 0 := hp
  unfold IsDivNearAlong at hdiv
  rw [HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq (Y := projectionAmbient X) hsub hI N 1] at hdiv
  -- the zero section through `p`
  set s : X → projectionAmbient X := fun x => (x, (0 : ComplexModel 1)) with hs
  have hscont : Continuous s := continuous_id.prodMk continuous_const
  have hsp : s p.1 = p := by
    show (p.1, (0 : ComplexModel 1)) = p
    rw [← hp0]
  have hev : ∀ᶠ x in 𝓝 p.1, x ∈ N → x ∈ cosupport n N I 1 := by
    have h1 : ∀ᶠ x in 𝓝 p.1, s x ∈ (Prod.fst : projectionAmbient X → X) ⁻¹' N → s x ∈ horizontal X →
        s x ∈ (Prod.fst : projectionAmbient X → X) ⁻¹' cosupport n N I 1 :=
      hscont.continuousAt.eventually (by rw [hsp]; exact hdiv)
    filter_upwards [h1] with x hx hxN
    exact hx hxN rfl
  obtain ⟨g, hg, hfreq⟩ := hne p.1 hpN
  have hgev := HadamardBridge.eventually_mem_of_isCoherent hI hg
  obtain ⟨x, ⟨hxN, hgx⟩, hx1, hx2⟩ := (hfreq.and_eventually (hev.and hgev)).exists
  have hxc := hx1 hxN
  exact hgx ((vanishesToOrderOn_one_iff hxN (GermIdeal.IsCoherent.holomorphicAt_mem hI hx2)).mp (hxc.2 g hx2))

variable {A : MarkedIdeal n X}

/-- The horizontal member has exponent `0` at every point of the carrier of the product test. -/
theorem horizontal_exp_zero (hA : A.ideal.IsCoherent) (hne : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y) :
    ∀ y ∈ (Prod.fst : projectionAmbient X → X) ⁻¹' A.N, y ∈ horizontal X →
      divExpAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' A.N)
        (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A.ideal) (horizontal X) y = 0 :=
  fun _ hyN hy => divExpAlong_horizontal_eq_zero hA hne hyN hy

/-- **The monomial part of the product test is the pullback of the monomial part.** -/
theorem monomialPartAlong_projectionTest (hn : 0 < n) (hA : A.IsWellFormed)
    (hne : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y) :
    monomialPartAlong (n + 1) (projectionTest A).N (projectionTest A).ideal (projectionTest A).E =
      GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) (monomialPartAlong n A.N A.ideal A.E) := by
  have hsub := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  show monomialPartAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' A.N)
      (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A.ideal)
      (A.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]) = _
  rw [monomialPartAlong_append_of_eq_zero (horizontal_exp_zero hA.isCoherent hne),
    HironakaSmoothSubmersionRelativePartsCompanion.pullback_monomialPartAlong (Y := projectionAmbient X) hsub hn hA.isClosedSubmanifold_N
      hA.isSNCDivisor hA.isTransverse hA.isCoherent hne]

/-- **The nonmonomial part of the product test is the pullback of the nonmonomial part.** -/
theorem nonmonomialPartAlong_projectionTest (hn : 0 < n) (hA : A.IsWellFormed)
    (hne : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y) :
    nonmonomialPartAlong (n + 1) (projectionTest A).N (projectionTest A).ideal (projectionTest A).E =
      GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X)
        (nonmonomialPartAlong n A.N A.ideal A.E) := by
  have hsub := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  show nonmonomialPartAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' A.N)
      (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A.ideal)
      (A.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]) = _
  rw [nonmonomialPartAlong_append_of_eq_zero (horizontal_exp_zero hA.isCoherent hne),
    HironakaSmoothSubmersionRelativePartsCompanion.pullback_nonmonomialPartAlong (Y := projectionAmbient X) hsub hn hA.isClosedSubmanifold_N
      hA.isSNCDivisor hA.isTransverse hA.isCoherent hne]

/-- **The companion ideal commutes with the product with a line**: `𝓞(projectionTest A, o) = projectionTest 𝓞(A, o)`. -/
theorem companionOf_projectionTest (hn : 0 < n) (hA : A.IsWellFormed)
    (hne : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y) (o : ℕ) :
    companionOf (n + 1) (projectionTest A) o = projectionTest (companionOf n A o) := by
  have hsub := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  have hmp := HironakaSmoothSubmersionRelativePartsCompanion.markedPullback_companionOf (m := n + 1)
    (Y := projectionAmbient X) hsub hn A hA hne o
  have hI : (projectionTest (companionOf n A o)).ideal =
      (companionOf (n + 1) (markedPullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A) o).ideal := by
    rw [← hmp]
    rfl
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_
  · show (companionOf (n + 1) (projectionTest A) o).N = (Prod.fst : projectionAmbient X → X) ⁻¹' (companionOf n A o).N
    simp only [companionOf, companionAlong_N]
    rfl
  · show (companionOf (n + 1) (projectionTest A) o).E =
      (companionOf n A o).E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
    simp only [companionOf, companionAlong_E]
    rfl
  · rw [hI]
    have e1 : nonmonomialPartAlong (n + 1) (markedPullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A).N
        (markedPullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A).ideal
        (markedPullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A).E =
        GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) (nonmonomialPartAlong n A.N A.ideal A.E) :=
      (HironakaSmoothSubmersionRelativePartsCompanion.pullback_nonmonomialPartAlong (Y := projectionAmbient X) hsub hn
        hA.isClosedSubmanifold_N hA.isSNCDivisor hA.isTransverse hA.isCoherent hne).symm
    have e2 : monomialPartAlong (n + 1) (markedPullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A).N
        (markedPullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A).ideal
        (markedPullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A).E =
        GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) (monomialPartAlong n A.N A.ideal A.E) :=
      (HironakaSmoothSubmersionRelativePartsCompanion.pullback_monomialPartAlong (Y := projectionAmbient X) hsub hn
        hA.isClosedSubmanifold_N hA.isSNCDivisor hA.isTransverse hA.isCoherent hne).symm
    simp only [companionOf, CompanionRebase.companionAlong_ideal]
    rw [monomialPartAlong_projectionTest hn hA hne, nonmonomialPartAlong_projectionTest hn hA hne, e1, e2]
    rfl
  · show (companionOf (n + 1) (projectionTest A) o).d = (companionOf n A o).d
    simp only [companionOf, CompanionRebase.companionAlong_d]
    rfl

/-- **Orders of the nonmonomial part pull back to the product.** -/
theorem ordGe_projectionTest (hn : 0 < n) (hA : A.IsWellFormed) (hne : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y)
    (q : ℕ) : ordGe (projectionTest A) q = (Prod.fst : projectionAmbient X → X) ⁻¹' ordGe A q := by
  have hsub := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  show cosupport (n + 1) (projectionTest A).N
    (nonmonomialPartAlong (n + 1) (projectionTest A).N (projectionTest A).ideal (projectionTest A).E) q = _
  rw [nonmonomialPartAlong_projectionTest hn hA hne]
  exact HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq (Y := projectionAmbient X) hsub
    (isCoherent_nonmonomialPartAlong hn hA.isClosedSubmanifold_N hA.isSNCDivisor hA.isTransverse hA.isCoherent hne)
    A.N q

/-- **Cosupports pull back to the product.** -/
theorem cosupp_projectionTest (hA : A.ideal.IsCoherent) :
    (projectionTest A).cosupp = (Prod.fst : projectionAmbient X → X) ⁻¹' A.cosupp :=
  HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq (Y := projectionAmbient X)
    (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hA A.N A.d

/-- **The bound `ord(𝓝|_N) ≤ o` on the cosupport passes to the product.** -/
theorem bound_projectionTest (hn : 0 < n) (hA : A.IsWellFormed) (hne : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y)
    {o : ℕ} (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) :
    ∀ z ∈ (projectionTest A).cosupp, z ∉ ordGe (projectionTest A) (o + 1) := by
  intro z hz hzo
  rw [cosupp_projectionTest hA.isCoherent] at hz
  rw [ordGe_projectionTest hn hA hne] at hzo
  exact hbound z.1 hz hzo

/-- **Restricted equivalence passes to products with a line** (the targets coherent). -/
theorem RestrictEquiv.projectionTest {P Q : MarkedIdeal n X} (h : RestrictEquiv P Q) (hP : P.ideal.IsCoherent)
    (hQ : Q.ideal.IsCoherent) : RestrictEquiv (projectionTest P) (projectionTest Q) := by
  have hφ := Hironaka.ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := X)
    (Y := ComplexModel 1)
  refine ⟨?_, ?_, h.d_eq, ?_, ?_⟩
  · show (Prod.fst : projectionAmbient X → X) ⁻¹' P.N = (Prod.fst : projectionAmbient X → X) ⁻¹' Q.N
    rw [h.N_eq]
  · show P.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] =
      Q.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
    rw [h.E_eq]
  · exact restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQ hg) h.le
  · exact restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP hg) h.ge

end Product

/-! ### Exponent agreement passes to products (universe `0`) -/

section Agree

open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree)

variable {X : CMfd.{0} n}

/-- **Agreement of boundary exponents passes to the product with a line** (same carrier and boundary; both ideals
coherent and nonzero along the carrier): along `H × ℂ` the exponents are those along `H`, along `X × {0}` both are `0`. -/
theorem expAgree_projectionTest {A B : MarkedIdeal n X} (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
    (hneA : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y) (hneB : ∀ y ∈ B.N, IsNonzeroAlongAt B.N B.ideal y)
    (hN : B.N = A.N) (h : ExpAgree A B) : ExpAgree (projectionTest A) (projectionTest B) := by
  intro H hH y hy hyH
  have hy' : y.1 ∈ A.cosupp := by
    have := hy
    rw [cosupp_projectionTest hA] at this
    exact this
  rcases List.mem_append.mp hH with hH | hH
  · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    show divExpAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' A.N)
        (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A.ideal)
        ((Prod.fst : projectionAmbient X → X) ⁻¹' H₀) y =
      divExpAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' B.N)
        (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) B.ideal)
        ((Prod.fst : projectionAmbient X → X) ⁻¹' H₀) y
    rw [divExpAlong_fst hA, divExpAlong_fst hB]
    exact h H₀ hH₀ y.1 hy' hyH
  · rw [List.mem_singleton.mp hH] at hyH ⊢
    show divExpAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' A.N)
        (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) A.ideal) (horizontal X) y =
      divExpAlong (n + 1) ((Prod.fst : projectionAmbient X → X) ⁻¹' B.N)
        (GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient X → X) B.ideal) (horizontal X) y
    have hyN : y.1 ∈ A.N := A.cosupp_subset_N hy'
    have hyNB : y.1 ∈ B.N := by rw [hN]; exact hyN
    rw [horizontal_exp_zero hA hneA y hyN hyH, horizontal_exp_zero hB hneB y hyNB hyH]

end Agree

end

end Hironaka.HironakaG8E4cProduct

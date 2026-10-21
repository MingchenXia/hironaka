import TranscendentalNakamaye.Pending.SimultaneousNormalCrossings
import TranscendentalNakamaye.Pending.MarkedIdealGeoTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Normal crossings with a divisor and with the divisor minus members containing the centre

Hironaka phase H2 (TN3), item 6 of the H2 list for H4 (I-0977 C-0048 / C-0054), consumed by the
design node `hir:drop-containing-members` (`blueprint/src/hironaka.tex`).  Blueprint
`bcalc:nc-comparison`, `bcalc:sub-divisor` (chapter `blowup-calculus.tex`).  Sources:
Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Definitions 2.1--2.2; Włodarczyk 2005
(`wlodarczyk05-hironaka`), Step 1a of the proof of `pr:resol` (`E_S`: the divisor without the
members containing `S`).

Let `E` be a simple normal crossings divisor and `C` a set.  If every member of `E` that is not a
member of the list `E'` contains `C`, and every member of `E'` is a member of `E`, then

  `HasNormalCrossings n C E' ↔ HasNormalCrossings n C E`

(`hasNormalCrossings_iff_of_forall_mem`).  The direction `⇐` is restriction to fewer members
(`hasNormalCrossings_of_forall_mem`, no hypothesis on `E`).  For `⇒`, at a point `x ∈ C` take
coordinates in which `C` and the members of `E'` through `x` are coordinate subspaces, and turn the
remaining members (they contain `C`) into coordinate hyperplanes one at a time
(`IsPartialNCAt.insert`): for one such member `H₀`, the simple normal crossings coordinates `Ψ` of
`E` make `H₀ = {v_{t₀} = 0}` and the members already treated hyperplanes `{v_{t_i} = 0}` with
`t_i ≠ t₀`; `SimultaneousNormalCrossings.exists_model_coords` with `S₀ = {t₀}` replaces one
coordinate of `C` by `v_{t₀}` and keeps the coordinates of the members already treated.

Corollaries: the filter form `hasNormalCrossings_filter_iff` (`E' = E.filter p`, the dropped members
contain `C`), the index form `hasNormalCrossings_drop_iff` (drop the members with indices in `A`),
sub-divisors of simple normal crossings divisors (`isSNCDivisor_of_sublist`,
`isTransverse_of_forall_mem`),
and for marked ideals: admissibility of a centre for `(M, N, E, 𝓘, d)` and `(M, N, E', 𝓘, d)` agree
(`isAdmissibleCentre_withE_iff`), and well-formedness passes to a sublist (`isWellFormed_withE`).
Along one blowup the hypotheses pass to the transformed divisors (`forall_mem_transformE`,
`sublist_transformE`, `forall_notMem_transformE`: the dropped members keep containing the strict
transform of `S`), and the transform of `(M, N, E', 𝓘, d)` is the transform of `𝔪` with the
transformed `E'` (`geoTransform_withE`) -- the induction step for towers in
`hir:drop-containing-members`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace TranscendentalNakamaye.Pending.NormalCrossingsComparison

open FirstPass FirstPass.BlowupSequences NormalCrossings BlowupSNCTransform
  SimultaneousNormalCrossings RegularAtDimTransport RegularPatchPushforward MarkedIdeals
  BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-! ### Restriction to fewer members -/

/-- **Normal crossings with fewer members**: if `C` has only normal crossings with `E`, it has only
normal crossings with every list `E'` of members of `E`. -/
theorem hasNormalCrossings_of_forall_mem {C : Set X} {E E' : List (Set X)}
    (h : HasNormalCrossings n C E) (hsub : ∀ H ∈ E', H ∈ E) : HasNormalCrossings n C E' := by
  intro x hx
  obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hS⟩ := h x hx
  have hidx : ∀ j : Fin E'.length, ∃ i : Fin E.length, E.get i = E'.get j :=
    fun j => List.mem_iff_get.mp (hsub _ (List.get_mem _ _))
  choose idx hidx using hidx
  refine ⟨S₀, fun j => S (idx j), ⟨Φ, hΦt, hΦ0, ?_⟩,
    fun j hj => hS (idx j) (by rw [hidx]; exact hj)⟩
  rintro (_ | j) hj y hy hyΦ
  · exact hΦA none hj hy hyΦ
  · have h1 := hΦA (some (idx j)) (by simp only [Option.elim]; rw [hidx]; exact hj) hy hyΦ
    simp only [Option.elim] at h1 ⊢
    rw [hidx] at h1
    exact h1

/-- **Transversality to fewer members.** -/
theorem isTransverse_of_forall_mem {N : Set X} {E E' : List (Set X)}
    (h : IsTransverse n N E) (hsub : ∀ H ∈ E', H ∈ E) : IsTransverse n N E' := by
  intro x hx
  obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hS⟩ := h x hx
  have hidx : ∀ j : Fin E'.length, ∃ i : Fin E.length, E.get i = E'.get j :=
    fun j => List.mem_iff_get.mp (hsub _ (List.get_mem _ _))
  choose idx hidx using hidx
  refine ⟨S₀, fun j => S (idx j), ⟨Φ, hΦt, hΦ0, ?_⟩,
    fun j hj => hS (idx j) (by rw [hidx]; exact hj)⟩
  rintro (_ | j) hj y hy hyΦ
  · exact hΦA none hj hy hyΦ
  · have h1 := hΦA (some (idx j)) (by simp only [Option.elim]; rw [hidx]; exact hj) hy hyΦ
    simp only [Option.elim] at h1 ⊢
    rw [hidx] at h1
    exact h1

/-- **A sublist of a simple normal crossings divisor is a simple normal crossings divisor.**
(Duplicated members would break the injectivity of the hyperplane indices, so a sublist, not an
arbitrary list of members, is needed.) -/
theorem isSNCDivisor_of_sublist {E E' : List (Set X)} (hE : IsSNCDivisor n E) (h : E'.Sublist E) :
    IsSNCDivisor n E' := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp h
  refine ⟨fun H hH => hE.1 H (h.subset hH), fun x => ?_⟩
  obtain ⟨S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hcard, hinj⟩ := hE.2 x
  refine ⟨fun j => S (f j), ⟨Φ, hΦt, hΦ0, fun j hj y hy hyΦ => ?_⟩, fun j hj => ?_,
    fun j₁ hj₁ j₂ hj₂ h12 => ?_⟩
  · have hj' : x ∈ E.get (f j) := by rw [← hf]; exact hj
    have h1 := hΦA (f j) hj' hy hyΦ
    show y ∈ E'.get j ↔ _
    rw [hf]
    exact h1
  · exact hcard (f j) (by rw [← hf]; exact hj)
  · have hj₁' : x ∈ E.get (f j₁) := by rw [← hf]; exact hj₁
    have hj₂' : x ∈ E.get (f j₂) := by rw [← hf]; exact hj₂
    exact f.injective (hinj hj₁' hj₂' h12)

/-! ### Adding members that contain the centre -/

/-- `z ∈ ℂ^{n-1} × 0` iff the last coordinate vanishes. -/
theorem mem_complexCoordinatePlane_pred_iff {z : ComplexModel n} (hn : 0 < n) :
    z ∈ complexCoordinatePlane n (n - 1) ↔ z ⟨n - 1, by omega⟩ = 0 := by
  constructor
  · intro h
    exact h _ le_rfl
  · intro h i hi
    have : i = ⟨n - 1, by omega⟩ := Fin.ext (show i.1 = n - 1 by have := i.2; omega)
    rw [this]
    exact h

variable [IsComplexManifold n X]

variable (n) in
/-- **Partially adapted coordinates**: holomorphic coordinates `Θ` at `x` (after the preferred
chart, centred at `0`) in which `C` is the coordinate subspace cut out by `Y` and every member
`E.get i` with `i ∈ I` through `x` is the coordinate hyperplane cut out by the one-element set
`s i`. -/
def IsPartialNCAt (C : Set X) (E : List (Set X)) (I : Finset (Fin E.length)) (x : X) : Prop :=
  ∃ (Y : Finset (Fin n)) (s : Fin E.length → Finset (Fin n))
    (Θ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
    Θ.source ⊆ (complexChartAt (n := n) x).val.target ∧
    Θ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
    (∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Θ.source →
        (y ∈ C ↔ Θ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Y)) ∧
    ∀ i ∈ I, x ∈ E.get i → (s i).card = 1 ∧
      ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Θ.source →
          (y ∈ E.get i ↔ Θ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (s i))

/-- **The start**: normal crossings of `C` with `E'` give partially adapted coordinates for the
members of `E` that are members of `E'`. -/
theorem isPartialNCAt_of_hasNormalCrossings {C : Set X} {E E' : List (Set X)}
    (hE' : HasNormalCrossings n C E') {x : X} (hx : x ∈ C) :
    IsPartialNCAt n C E (Finset.univ.filter fun i => E.get i ∈ E') x := by
  classical
  obtain ⟨Y, S', ⟨Θ, hΘt, hΘ0, hΘA⟩, hS'⟩ := hE' x hx
  have hidx : ∀ i : Fin E.length, E.get i ∈ E' → ∃ j : Fin E'.length, E'.get j = E.get i :=
    fun i hi => List.mem_iff_get.mp hi
  choose idx hidx using hidx
  refine ⟨Y, fun i => if h : E.get i ∈ E' then S' (idx i h) else ∅, Θ, hΘt, hΘ0,
    fun hy hyΘ => hΘA none hx hy hyΘ, fun i hi hxi => ?_⟩
  have hiE : E.get i ∈ E' := (Finset.mem_filter.mp hi).2
  have hxj : x ∈ E'.get (idx i hiE) := by rw [hidx]; exact hxi
  simp only [hiE, dite_true]
  refine ⟨hS' _ hxj, fun hy hyΘ => ?_⟩
  have h1 := hΘA (some (idx i hiE)) hxj hy hyΘ
  simp only [Option.elim] at h1
  rw [hidx] at h1
  exact h1

/-- **One more member containing `C` becomes a coordinate hyperplane.**  If `E` is a simple normal
crossings divisor, `x ∈ C`, the member `E.get i₀` contains `C`, and there are partially adapted
coordinates for the members indexed by `I`, then there are partially adapted coordinates for the
members indexed by `insert i₀ I`. -/
theorem IsPartialNCAt.insert {C : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) {x : X}
    (hx : x ∈ C) {I : Finset (Fin E.length)} {i₀ : Fin E.length} (hi₀ : C ⊆ E.get i₀)
    (h : IsPartialNCAt n C E I x) : IsPartialNCAt n C E (insert i₀ I) x := by
  classical
  by_cases hI : i₀ ∈ I
  · rwa [Finset.insert_eq_of_mem hI]
  obtain ⟨Y, s, Θ, hΘt, hΘ0, hCΘ, hHΘ⟩ := h
  obtain ⟨S, ⟨Ψ, hΨt, hΨ0, hΨA⟩, hcard, hinj⟩ := hE.2 x
  let e := (complexChartAt (n := n) x).val
  have hx₀ : x ∈ E.get i₀ := hi₀ hx
  obtain ⟨a₀, -⟩ := Finset.card_eq_one.mp (hcard i₀ hx₀)
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a₀.2
  -- the index of a one-element set
  set pick : Finset (Fin n) → Fin n := fun s => if h : s.Nonempty then s.min' h else a₀
    with hpick
  have hpick1 : ∀ s : Finset (Fin n), s.card = 1 → s = {pick s} := by
    intro s hs
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    simp [hpick]
  set t : Fin E.length → Fin n := fun i => pick (S i) with ht
  set p : Fin E.length → Fin n := fun i => pick (s i) with hp
  -- the members through `x` in the simple normal crossings coordinates `Ψ`
  have hHΨ : ∀ i, x ∈ E.get i → ∀ {y : X}, y ∈ e.source → e y ∈ Ψ.source →
      (y ∈ E.get i ↔ Ψ.toFun (e y) (t i) = 0) := by
    intro i hi y hy hyΨ
    have h := hΨA i hi hy hyΨ
    rw [hpick1 _ (hcard i hi), mem_coordSubspace_singleton] at h
    exact h
  have htinj : ∀ i, x ∈ E.get i → i ≠ i₀ → t i ≠ t i₀ := by
    intro i hi hne heq
    apply hne
    apply hinj hi hx₀
    rw [hpick1 _ (hcard i hi), hpick1 _ (hcard i₀ hx₀)]
    exact congrArg (fun a : Fin n => ({a} : Finset (Fin n))) heq
  -- the members already treated, in the coordinates `Θ`
  have hHΘ' : ∀ i ∈ I, x ∈ E.get i → ∀ {y : X}, y ∈ e.source → e y ∈ Θ.source →
      (y ∈ E.get i ↔ Θ.toFun (e y) (p i) = 0) := by
    intro i hi hxi y hy hyΘ
    obtain ⟨hc, hm⟩ := hHΘ i hi hxi
    have h := hm hy hyΘ
    rw [hpick1 _ hc, mem_coordSubspace_singleton] at h
    exact h
  -- `Ξ = Ψ ∘ Θ⁻¹` in the `Θ`-coordinates
  have h0Θ : (0 : ComplexModel n) ∈ Θ.target := hΘ0 ▸ Θ.mapsTo_toFun Θ.center_mem_source
  have hΘinv0 : Θ.invFun 0 = e x := by
    rw [← hΘ0]
    exact Θ.left_inv _ Θ.center_mem_source
  set Ξ := LocalHolomorphicEquivAt.comp (symmAt Θ h0Θ) Ψ hΘinv0 with hΞ
  have hpt : ∀ u ∈ Ξ.source, e.symm (Θ.invFun u) ∈ e.source ∧
      e (e.symm (Θ.invFun u)) ∈ Θ.source ∧ e (e.symm (Θ.invFun u)) ∈ Ψ.source ∧
      Θ.toFun (e (e.symm (Θ.invFun u))) = u ∧
      Ψ.toFun (e (e.symm (Θ.invFun u))) = Ξ.toFun u := by
    intro u hu
    have hwΘ : Θ.invFun u ∈ Θ.source := Θ.mapsTo_invFun hu.1
    have hwe : Θ.invFun u ∈ e.target := hΘt hwΘ
    rw [e.right_inv hwe]
    exact ⟨e.map_target hwe, hwΘ, hu.2, Θ.right_inv u hu.1, rfl⟩
  have hΞ0 : Ξ.toFun 0 = 0 := by
    show Ψ.toFun (Θ.invFun 0) = 0
    rw [hΘinv0]
    exact hΨ0
  -- the model: replace one coordinate of `C` by `Ψ_{t i₀}`
  obtain ⟨Xs, σ, Φ', hXY, hXp, hΦ's, hσ, hΦ'⟩ := exists_model_coords Ξ Y {t i₀}
    {i | i ∈ I ∧ x ∈ E.get i} p t
    (fun i hi => by
      rw [Finset.mem_singleton]
      exact htinj i hi.2 (fun h => hI (h ▸ hi.1)))
    (fun i hi u hu hu0 => by
      obtain ⟨hy, hyΘ, hyΨ, hΘu, hΨu⟩ := hpt u hu
      have hmem : e.symm (Θ.invFun u) ∈ E.get i :=
        (hHΘ' i hi.1 hi.2 hy hyΘ).mpr (by rw [hΘu]; exact hu0)
      rw [← hΨu]
      exact (hHΨ i hi.2 hy hyΨ).mp hmem)
    (fun u hu huY => by
      obtain ⟨hy, hyΘ, hyΨ, hΘu, hΨu⟩ := hpt u hu
      have hmem : e.symm (Θ.invFun u) ∈ C := (hCΘ hy hyΘ).mpr (by rw [hΘu]; exact huY)
      rw [← hΨu, mem_coordSubspace_singleton]
      exact (hHΨ i₀ hx₀ hy hyΨ).mp (hi₀ hmem))
  have hcard1 : ({t i₀} : Finset (Fin n)).card = 1 := Finset.card_singleton _
  -- `Φ'` is centred
  have hΦ'0 : Φ'.toFun 0 = 0 := by
    obtain ⟨-, hN0, hH0⟩ := hΦ' 0 Φ'.center_mem_source
    have h1 : Φ'.toFun 0 ∈ complexCoordinatePlane n (n - ({t i₀} : Finset (Fin n)).card) :=
      hN0.mp (by rw [hΞ0]; intro j _; rfl)
    ext r
    obtain ⟨τ, rfl⟩ := σ.surjective r
    by_cases hτ : τ ∈ Xs
    · exact h1 _ ((hσ τ).mpr hτ)
    · rw [hH0 τ hτ]
      rfl
  have hΘΦ : Θ.toFun (e x) = 0 := hΘ0
  set r₀ : Fin n := ⟨n - 1, by omega⟩ with hr₀
  refine ⟨Finset.univ.filter (fun j : Fin n => n - Y.card ≤ j.1),
    fun i => if i = i₀ then {r₀} else {σ (p i)}, LocalHolomorphicEquivAt.comp Θ Φ' hΘΦ,
    fun w hw => hΘt hw.1, ?_, ?_, ?_⟩
  · show Φ'.toFun (Θ.toFun (e x)) = 0
    rw [hΘΦ, hΦ'0]
  · intro y hy hyΘ'
    obtain ⟨hyΘ, huΦ'⟩ := hyΘ'
    rw [coordSubspace_eq_complexCoordinatePlane]
    exact (hCΘ hy hyΘ).trans (hΦ' _ huΦ').1
  · intro i hi hxi
    rcases Finset.mem_insert.mp hi with rfl | hiI
    · refine ⟨by simp, fun {y} hy hyΘ' => ?_⟩
      obtain ⟨hyΘ, huΦ'⟩ := hyΘ'
      have huΞ : Θ.toFun (e y) ∈ Ξ.source := hΦ's huΦ'
      have hinv : Θ.invFun (Θ.toFun (e y)) = e y := Θ.left_inv _ hyΘ
      have hyΨ : e y ∈ Ψ.source := by rw [← hinv]; exact huΞ.2
      have hΞu : Ξ.toFun (Θ.toFun (e y)) = Ψ.toFun (e y) := by
        show Ψ.toFun (Θ.invFun (Θ.toFun (e y))) = _
        rw [hinv]
      have h2 := (hΦ' _ huΦ').2.1
      rw [hcard1] at h2
      have hif : (if i = i then ({r₀} : Finset (Fin n)) else {σ (p i)}) = {r₀} := if_pos rfl
      show y ∈ E.get i ↔ Φ'.toFun (Θ.toFun (e y)) ∈
        coordSubspace (if i = i then ({r₀} : Finset (Fin n)) else {σ (p i)})
      rw [hif, mem_coordSubspace_singleton, hHΨ _ hxi hy hyΨ, ← hΞu, ← mem_coordSubspace_singleton,
        h2, mem_complexCoordinatePlane_pred_iff hn]
    · have hne : i ≠ i₀ := fun h => hI (h ▸ hiI)
      refine ⟨by simp [hne], fun {y} hy hyΘ' => ?_⟩
      obtain ⟨hyΘ, huΦ'⟩ := hyΘ'
      simp only [if_neg hne, mem_coordSubspace_singleton]
      have hX : p i ∉ Xs := hXp i ⟨hiI, hxi⟩
      show y ∈ E.get i ↔ Φ'.toFun (Θ.toFun (e y)) (σ (p i)) = 0
      rw [(hΦ' _ huΦ').2.2 _ hX]
      exact hHΘ' i hiI hxi hy hyΘ

/-- **Adding members that contain the centre** (`⇒` of the comparison).  If `E` is a simple normal
crossings divisor, `C` has only normal crossings with `E'`, and every member of `E` that is not a
member of `E'` contains `C`, then `C` has only normal crossings with `E`. -/
theorem hasNormalCrossings_of_forall_notMem {C : Set X} {E E' : List (Set X)}
    (hE : IsSNCDivisor n E) (hE' : HasNormalCrossings n C E')
    (hA : ∀ H ∈ E, H ∉ E' → C ⊆ H) : HasNormalCrossings n C E := by
  classical
  intro x hx
  have hbase := isPartialNCAt_of_hasNormalCrossings (E := E) hE' hx
  have key : ∀ J : Finset (Fin E.length), (∀ i ∈ J, C ⊆ E.get i) →
      IsPartialNCAt n C E ((Finset.univ.filter fun i => E.get i ∈ E') ∪ J) x := by
    intro J
    refine Finset.induction_on J ?_ ?_
    · intro _
      simpa using hbase
    · intro a J _ ih hJ
      rw [Finset.union_insert]
      exact (ih fun i hi => hJ i (Finset.mem_insert_of_mem hi)).insert hE hx
        (hJ a (Finset.mem_insert_self a J))
  have hall := key (Finset.univ.filter fun i => E.get i ∉ E')
    (fun i hi => hA _ (List.get_mem _ _) (Finset.mem_filter.mp hi).2)
  have huniv : ((Finset.univ.filter fun i => E.get i ∈ E') ∪
      Finset.univ.filter fun i => E.get i ∉ E') = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (em _) trivial
  rw [huniv] at hall
  obtain ⟨Y, s, Θ, hΘt, hΘ0, hCΘ, hHΘ⟩ := hall
  refine ⟨Y, s, ⟨Θ, hΘt, hΘ0, ?_⟩, fun i hi => (hHΘ i (Finset.mem_univ i) hi).1⟩
  rintro (_ | i) hi y hy hyΘ
  · exact hCΘ hy hyΘ
  · exact (hHΘ i (Finset.mem_univ i) hi).2 hy hyΘ

/-! ### The comparison -/

/-- **The normal-crossings comparison** (H2 list item 6).  Let `E` be a simple normal crossings
divisor and `E'` a list of members of `E` such that every member of `E` not in `E'` contains `C`.
Then `C` has only normal crossings with `E'` iff it has only normal crossings with `E`. -/
theorem hasNormalCrossings_iff_of_forall_mem {C : Set X} {E E' : List (Set X)}
    (hE : IsSNCDivisor n E) (hsub : ∀ H ∈ E', H ∈ E) (hA : ∀ H ∈ E, H ∉ E' → C ⊆ H) :
    HasNormalCrossings n C E' ↔ HasNormalCrossings n C E :=
  ⟨fun h => hasNormalCrossings_of_forall_notMem hE h hA,
    fun h => hasNormalCrossings_of_forall_mem h hsub⟩

/-- **The comparison, filter form**: dropping members that contain `C` does not change normal
crossings with `C`. -/
theorem hasNormalCrossings_filter_iff {C : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E)
    (q : Set X → Bool) (hq : ∀ H ∈ E, q H = false → C ⊆ H) :
    HasNormalCrossings n C (E.filter q) ↔ HasNormalCrossings n C E :=
  hasNormalCrossings_iff_of_forall_mem hE (fun _ hH => (List.mem_filter.mp hH).1)
    (fun H hH hH' => hq H hH (by
      by_contra hne
      exact hH' (List.mem_filter.mpr ⟨hH, by simpa using hne⟩)))

/-- **The comparison, index form**: drop the members `E.get i`, `i ∈ A`, all containing `C`. -/
theorem hasNormalCrossings_drop_iff {C : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E)
    (A : Finset (Fin E.length)) (hA : ∀ i ∈ A, C ⊆ E.get i) :
    HasNormalCrossings n C (((List.finRange E.length).filter fun i => i ∉ A).map E.get) ↔
      HasNormalCrossings n C E := by
  classical
  refine hasNormalCrossings_iff_of_forall_mem hE (fun H hH => ?_) (fun H hH hH' => ?_)
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hH
    exact List.get_mem _ _
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    by_cases hi : i ∈ A
    · exact hA i hi
    · exact absurd (List.mem_map.mpr
        ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i, by simpa using hi⟩, rfl⟩) hH'

/-! ### Marked ideals with fewer members -/

/-- **Admissibility does not see the members containing the centre**: for a marked ideal `𝔪` with a
simple normal crossings divisor and a list `E'` of members of `𝔪.E` such that every member of `𝔪.E`
not in `E'` contains `C`, `C` is admissible for `(M, N, E', 𝓘, d)` iff it is for `𝔪`. -/
theorem isAdmissibleCentre_withE_iff (𝔪 : MarkedIdeal n X) {E' : List (Set X)} {C : Set X}
    (hE : IsSNCDivisor n 𝔪.E) (hsub : ∀ H ∈ E', H ∈ 𝔪.E) (hA : ∀ H ∈ 𝔪.E, H ∉ E' → C ⊆ H) :
    ({ 𝔪 with E := E' } : MarkedIdeal n X).IsAdmissibleCentre C ↔ 𝔪.IsAdmissibleCentre C :=
  Iff.and Iff.rfl (Iff.and Iff.rfl (hasNormalCrossings_iff_of_forall_mem hE hsub hA))

/-- **Well-formedness passes to a sublist of the divisor.** -/
theorem isWellFormed_withE {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed) {E' : List (Set X)}
    (hE' : E'.Sublist 𝔪.E) : ({ 𝔪 with E := E' } : MarkedIdeal n X).IsWellFormed :=
  ⟨h𝔪.isClosedSubmanifold_N, h𝔪.isCoherent, isSNCDivisor_of_sublist h𝔪.isSNCDivisor hE',
    isTransverse_of_forall_mem h𝔪.isTransverse fun _ hH => hE'.subset hH⟩

/-! ### One blowup: the hypotheses pass to the transformed divisor -/

section Transform

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Strict transforms are monotone.** -/
theorem geoStrictTransform_mono (π : Y → X) (C : Set X) {A B : Set X} (h : A ⊆ B) :
    geoStrictTransform π C A ⊆ geoStrictTransform π C B :=
  closure_mono (preimage_mono (sdiff_subset_sdiff_left h))

/-- **Members pass to the transformed divisor**: if every member of `E'` is a member of `E`, the
same holds for the transformed divisors `[H'₁, …, π⁻¹ C]`. -/
theorem forall_mem_transformE (π : Y → X) (C : Set X) {E E' : List (Set X)}
    (hsub : ∀ H ∈ E', H ∈ E) :
    ∀ H ∈ E'.map (geoStrictTransform π C) ++ [π ⁻¹' C],
      H ∈ E.map (geoStrictTransform π C) ++ [π ⁻¹' C] := by
  intro H hH
  rcases List.mem_append.mp hH with hH | hH
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hH
    exact List.mem_append_left _ (List.mem_map_of_mem (hsub K hK))
  · exact List.mem_append_right _ hH

/-- **Sublists pass to the transformed divisor.** -/
theorem sublist_transformE (π : Y → X) (C : Set X) {E E' : List (Set X)} (h : E'.Sublist E) :
    (E'.map (geoStrictTransform π C) ++ [π ⁻¹' C]).Sublist
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) :=
  (h.map _).append (List.Sublist.refl _)

/-- **The dropped members keep containing the strict transform**: if every member of `E` that is not
a member of `E'` contains `S`, then every member of the transformed divisor of `E` that is not a
member of the transformed divisor of `E'` contains the strict transform of `S` (it is the strict
transform of a dropped member; the exceptional divisor is in both). -/
theorem forall_notMem_transformE (π : Y → X) (C : Set X) {E E' : List (Set X)} {S : Set X}
    (hA : ∀ H ∈ E, H ∉ E' → S ⊆ H) :
    ∀ H ∈ E.map (geoStrictTransform π C) ++ [π ⁻¹' C],
      H ∉ E'.map (geoStrictTransform π C) ++ [π ⁻¹' C] → geoStrictTransform π C S ⊆ H := by
  intro H hH hH'
  rcases List.mem_append.mp hH with hH | hH
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hH
    have hK' : K ∉ E' := fun h => hH' (List.mem_append_left _ (List.mem_map_of_mem h))
    exact geoStrictTransform_mono π C (hA K hK hK')
  · exact absurd (List.mem_append_right _ hH) hH'

/-- **The transform of `(M, N, E', 𝓘, d)`** is the transform of `𝔪` with the transformed `E'`: only
the divisor differs. -/
theorem geoTransform_withE (𝔪 : MarkedIdeal n X) (E' : List (Set X)) (C : Set X) (π : Y → X) :
    ({ 𝔪 with E := E' } : MarkedIdeal n X).geoTransform C π =
      { 𝔪.geoTransform C π with
        E := E'.map (geoStrictTransform π C) ++ [π ⁻¹' C] } :=
  rfl

end Transform

end

end TranscendentalNakamaye.Pending.NormalCrossingsComparison

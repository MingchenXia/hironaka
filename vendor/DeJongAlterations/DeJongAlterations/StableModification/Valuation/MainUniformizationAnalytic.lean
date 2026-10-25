import DeJongAlterations.StableModification.Valuation.Analytic.Uniformization
import DeJongAlterations.StableModification.Valuation.Analytic.SepClosedCompletion
import DeJongAlterations.StableModification.Valuation.MainUniformizationBasic

/-!
# The height-one step of Theorem 2.1.8: completion, Theorem 2.1.10 and decompletion

This file carries out the analytic part of the proof of Theorem 2.1.8 (`valunif`) of M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §2.2 (`semi-stable.tex`,
lines 2205–2232). Let `K` be a separably closed field, `L/K` a finitely generated extension with
a separating transcendental element `x₀` (so `L/K(x₀)` is finite separable) and `O₁` a valuation
ring of `L` of height one whose trace `A₁ = O₁ ∩ K` is not `K`. One passes to the completion
`L̂₁` of `L` and to the closure `k̂₁` of `K` in it, which is algebraically closed (Temkin,
l. 2208–2209), applies the uniformization of one-dimensional analytic fields (Theorem 2.1.10,
`uniformization_analytic` and `IsGaussGenerator.isUnramified`) and comes back with the
decompletion criterion (Proposition 2.2.1,
`Decompletion.exists_isStdUnramifiedGenerator_of_finrank_le`).
Blueprint chapter `sm-val-main.tex`.

The analytic statements are proved for an abstract complete non-archimedean field `M` with a
dense embedding `ι : L → M` such that `O₁ = {y | ‖ι y‖ ≤ 1}` and some `c ∈ K` has
`‖ι c‖ > 1`; the last section specializes to `M = O₁.valuation.Completion`.

## Main definitions

* `badField K L p`: `K Lᵖ` in characteristic `p > 1` and the algebraic closure of `K` in `L`
  otherwise; elements outside it are separating (`finiteDimensional_isSeparable_of_notMem`).
* `baseClosure K ι`: the closure `k̂₁` of `ι(K)` in `M`; under
  `Fact (∃ c : K, 1 < ‖ι c‖)` it is a complete nontrivially normed field, algebraically closed
  when `K` is separably closed. `residueBaseEquiv` and `residueComplEquiv` identify its residue
  field with `κ(A₁)` and the residue field of `M` with `κ(O₁)`.

## Main results

* `finiteDimensional_closureAdjoin_of_denseRange`: if `L/K(x)` is finite then `M` is finite
  over `\overline{k̂₁(ι x)}`.
* `isSeparable_residueField_of_denseRange`: residue separability passes to completions.
* `exists_adapted_of_isUnramified` (**decompletion at the height-one valuation**): if `M` is
  unramified over `\overline{k̂₁(ι T)}`, then `L/K(T)` has a standard-unramified generator at
  `O₁` with any prescribed separable generating residue, in the adapted form.
* `isUnramified_of_transcendental` (Temkin, l. 2227–2231, via Theorem 2.1.10(iii)): if the
  residue of `T ∈ O₁` is transcendental over `κ(A₁)` and `κ(O₁)/κ(O₁ ∩ K(T))` is separable, then
  `M` is unramified over `\overline{k̂₁(ι T)}`.
* `exists_lift` (Temkin, l. 2227–2228): a residue transcendental over `κ(A₁)` lifts to `T ∈ O₁`
  with `L/K(T)` finite and separable.
* `exists_isUnramified_transcendental` (Temkin, l. 2214–2220, via Theorem 2.1.10(ii)): some
  `x ∈ L` transcendental over `K`, with `L/K(x)` finite separable, has `M` unramified over
  `\overline{k̂₁(ι x)}`.
* `exists_adapted_of_transcendental`, `exists_lift_of_rankOne`, `exists_adapted_of_surjective`:
  the same statements for the completion `M = L̂₁`, in terms of `L` only.
-/
noncomputable section

open IsLocalRing Polynomial Topology
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.MainUniformization

open Analytic Decompletion

/-! ### Avoiding subspaces -/

section Avoid

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A line `x₁ + K w` with `w ∉ W` meets an intermediate field `W` at most once. -/
theorem eq_of_add_smul_mem (W : IntermediateField K L) {w : L} (hw : w ∉ W) (x₁ : L) {c c' : K}
    (hc : x₁ + c • w ∈ W) (hc' : x₁ + c' • w ∈ W) : c = c' := by
  by_contra hne
  have hsub : (c - c') • w ∈ W := by
    have := sub_mem hc hc'
    rwa [add_sub_add_left_eq_sub, ← sub_smul] at this
  have : w = (c - c')⁻¹ • ((c - c') • w) := by
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
  exact hw (this ▸ W.smul_mem hsub)

/-- Among three points `x₁ + cᵢ w` with distinct `cᵢ`, one avoids two intermediate fields not
containing `w`. -/
theorem exists_add_smul_notMem (W₁ W₂ : IntermediateField K L) {w : L} (hw₁ : w ∉ W₁)
    (hw₂ : w ∉ W₂) (x₁ : L) {c₀ c₁ c₂ : K} (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) :
    ∃ c ∈ ({c₀, c₁, c₂} : Set K), x₁ + c • w ∉ W₁ ∧ x₁ + c • w ∉ W₂ := by
  by_contra h
  push Not at h
  have h0 := h c₀ (by simp)
  have h1 := h c₁ (by simp)
  have h2 := h c₂ (by simp)
  by_cases a0 : x₁ + c₀ • w ∈ W₁ <;> by_cases a1 : x₁ + c₁ • w ∈ W₁ <;>
    by_cases a2 : x₁ + c₂ • w ∈ W₁
  · exact h01 (eq_of_add_smul_mem W₁ hw₁ x₁ a0 a1)
  · exact h01 (eq_of_add_smul_mem W₁ hw₁ x₁ a0 a1)
  · exact h02 (eq_of_add_smul_mem W₁ hw₁ x₁ a0 a2)
  · exact h12 (eq_of_add_smul_mem W₂ hw₂ x₁ (h1 a1) (h2 a2))
  · exact h12 (eq_of_add_smul_mem W₁ hw₁ x₁ a1 a2)
  · exact h02 (eq_of_add_smul_mem W₂ hw₂ x₁ (h0 a0) (h2 a2))
  · exact h01 (eq_of_add_smul_mem W₂ hw₂ x₁ (h0 a0) (h1 a1))
  · exact h01 (eq_of_add_smul_mem W₂ hw₂ x₁ (h0 a0) (h1 a1))

end Avoid

/-! ### Separability of `L/K(x)` -/

section Separating

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The "bad" intermediate field for the choice of a separating element: `K Lᵖ` in
characteristic `p > 1`, the algebraic closure of `K` in `L` in characteristic zero. -/
def badField (K L : Type*) [Field K] [Field L] [Algebra K L] (p : ℕ) : IntermediateField K L :=
  if 1 < p then IntermediateField.adjoin K (Set.range fun a : L ↦ a ^ p) else algebraicClosure K L

/-- A separating transcendental element `x₀` is not in the bad field. -/
theorem notMem_badField (p : ℕ) [ExpChar K p] (hfg : (⊤ : IntermediateField K L).FG) {x₀ : L}
    (hx₀ : Transcendental K x₀) [FiniteDimensional K⟮x₀⟯ L] [Algebra.IsSeparable K⟮x₀⟯ L] :
    x₀ ∉ badField K L p := by
  unfold badField
  split_ifs with hp
  · have hprime : p.Prime := by
      rcases ‹ExpChar K p› with _ | hp'
      · exact absurd hp (lt_irrefl 1)
      · exact hp'
    have : Fact p.Prime := ⟨hprime⟩
    have : CharP K p := by
      rcases ‹ExpChar K p› with _ | hp'
      · exact absurd hp (lt_irrefl 1)
      · assumption
    exact DVRCoordinate.notMem_of_isSeparable_adjoin p hfg hx₀
  · rw [mem_algebraicClosure_iff]
    exact hx₀

/-- **Separating elements** (Temkin, l. 2204–2206): if `x` is transcendental over `K` and not in
the bad field (that is, `x ∉ K Lᵖ` in characteristic `p > 1`), then `L/K(x)` is finite and
separable. -/
theorem finiteDimensional_isSeparable_of_notMem (p : ℕ) [ExpChar K p]
    (hfg : (⊤ : IntermediateField K L).FG) {x₀ : L} (hx₀ : Transcendental K x₀)
    [FiniteDimensional K⟮x₀⟯ L] [Algebra.IsSeparable K⟮x₀⟯ L] {x : L} (hx : Transcendental K x)
    (hxp : 1 < p → x ∉ badField K L p) :
    FiniteDimensional K⟮x⟯ L ∧ Algebra.IsSeparable K⟮x⟯ L := by
  rcases ‹ExpChar K p› with _ | hprime
  · have halg : Algebra.IsAlgebraic K⟮x₀⟯ L := Algebra.IsSeparable.isAlgebraic _ _
    have : Algebra.IsAlgebraic K⟮x⟯ L :=
      DVRCoordinate.isAlgebraic_adjoin_of_transcendental hx₀ halg hx
    have := DVRCoordinate.finiteDimensional_adjoin_of_transcendental hfg (y := x)
    exact ⟨this, Algebra.IsAlgebraic.isSeparable_of_perfectField⟩
  · have : Fact p.Prime := ⟨hprime⟩
    have hbad := hxp hprime.one_lt
    unfold badField at hbad
    rw [if_pos hprime.one_lt] at hbad
    exact DVRCoordinate.isSeparable_adjoin_of_notMem p hfg hx₀ hx hbad

end Separating


/-! ### Separability of residue fields under completion -/

section SeparableTransport

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {E M : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] [NormedField M]
  [IsUltrametricDist M] [NormedAlgebra E M] [Algebra K E] [Algebra L M] [Algebra K M]
  [IsScalarTower K E M]
  [IsScalarTower K L M]

/-- **Residue separability under completion** (the converse of the separability part of
`Decompletion.finrank_residueField_eq_of_denseRange`): if `K` is dense in `E`, `L` is dense in
`M` and `κ(B)/κ(B ∩ K)` is separable, then so is the residue extension of `M°` over
`M° ∩ E`. -/
theorem isSeparable_residueField_of_denseRange (B : ValuationSubring L)
    (hB : ∀ y, y ∈ B ↔ ‖algebraMap L M y‖ ≤ 1) (hdK : DenseRange (algebraMap K E))
    (hdL : DenseRange (algebraMap L M))
    [hsep : Algebra.IsSeparable (ResidueField (B.comap (algebraMap K L))) (ResidueField B)] :
    Algebra.IsSeparable (ResidueField (unitBall E)) (ResidueField (unitBall M)) := by
  set A := B.comap (algebraMap K L)
  have hι₁ : ∀ c : K, algebraMap E M (algebraMap K E c) = algebraMap L M (algebraMap K L c) :=
    fun c ↦ by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hA : ∀ c : K, c ∈ A ↔ ‖algebraMap L M (algebraMap K L c)‖ ≤ 1 := fun c ↦ by
    rw [ValuationSubring.mem_comap, hB]
  have hE : ∀ z : E, z ∈ unitBall E ↔ ‖algebraMap E M z‖ ≤ 1 := fun z ↦ by
    rw [mem_unitBall, norm_algebraMap']
  have hdA : ∀ z : E, ∃ c : K, ‖algebraMap E M (z - algebraMap K E c)‖ < 1 := by
    intro z
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp hdK z 1 one_pos
    exact ⟨c, by rw [norm_algebraMap', ← dist_eq_norm]; exact hc⟩
  have hdB : ∀ z : M, ∃ y : L, ‖RingHom.id M (z - algebraMap L M y)‖ < 1 := by
    intro z
    obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hdL z 1 one_pos
    exact ⟨y, by rw [RingHom.id_apply, ← dist_eq_norm]; exact hy⟩
  set φA := normRestrict (algebraMap K E) ((algebraMap L M).comp (algebraMap K L))
    (algebraMap E M) hι₁ (V := A) (W := unitBall E) hA hE
  set φB := normRestrict (algebraMap L M) (algebraMap L M) (RingHom.id M) (fun _ ↦ rfl)
    (V := B) (W := unitBall M) hB (fun z ↦ mem_unitBall)
  set i := RingEquiv.ofBijective _ (bijective_residueField_map_normRestrict (algebraMap K E)
    ((algebraMap L M).comp (algebraMap K L)) (algebraMap E M) hι₁ (V := A) (W := unitBall E) hA
    hE hdA)
  set j := RingEquiv.ofBijective _ (bijective_residueField_map_normRestrict (algebraMap L M)
    (algebraMap L M) (RingHom.id M) (fun _ ↦ rfl) (V := B) (W := unitBall M) hB
    (fun z ↦ mem_unitBall) hdB)
  have hcomm : (algebraMap (ResidueField (unitBall E)) (ResidueField (unitBall M))).comp
      i.toRingHom = j.toRingHom.comp (algebraMap (ResidueField A) (ResidueField B)) := by
    ext a
    obtain ⟨a, rfl⟩ := residue_surjective a
    change algebraMap (ResidueField (unitBall E)) (ResidueField (unitBall M))
        (ResidueField.map φA (residue A a)) =
      ResidueField.map φB (algebraMap (ResidueField A) (ResidueField B) (residue A a))
    rw [ResidueField.map_residue, ResidueField.algebraMap_residue]
    change _ = ResidueField.map φB (residue B (algebraMap A B a))
    rw [ResidueField.map_residue]
    congr 1
    exact Subtype.ext (hι₁ a)
  exact Algebra.IsSeparable.of_equiv_equiv i j hcomm

end SeparableTransport

/-! ### The closure of the base field in a completion -/

section Closure

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {M : Type*} [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M]
  (ι : L →+* M)

variable (K) in
/-- The closure `k̂₁` of the image of `K` in `M` (Temkin, l. 2208–2209: for `M = L̂₁` this is the
completion of `K` at the height-one valuation `k₁`). -/
def baseClosure : Subfield M :=
  (ι.comp (algebraMap K L)).fieldRange.topologicalClosure

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- `ι(K) ⊆ k̂₁`. -/
theorem algebraMap_mem_baseClosure (c : K) : ι (algebraMap K L c) ∈ baseClosure K ι :=
  Subfield.le_topologicalClosure _ ⟨c, rfl⟩

/-- `k̂₁` is a `K`-algebra through `ι`. -/
instance : Algebra K (baseClosure K ι) :=
  ((ι.comp (algebraMap K L)).codRestrict _ (algebraMap_mem_baseClosure ι)).toAlgebra

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- The structure map `K → k̂₁` is `ι` on `K`. -/
theorem coe_algebraMap_baseClosure (c : K) :
    ((algebraMap K (baseClosure K ι) c : baseClosure K ι) : M) = ι (algebraMap K L c) := rfl

/-- `k̂₁` is complete, being closed in the complete field `M`. -/
instance : CompleteSpace (baseClosure K ι) :=
  (Subfield.isClosed_topologicalClosure _).completeSpace_coe

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- `K` is dense in `k̂₁`. -/
theorem denseRange_algebraMap_baseClosure : DenseRange (algebraMap K (baseClosure K ι)) := by
  rw [Metric.denseRange_iff]
  intro z r hr
  have hz : (z : M) ∈ closure ((ι.comp (algebraMap K L)).fieldRange : Set M) := z.2
  obtain ⟨_, ⟨c, rfl⟩, hc⟩ := Metric.mem_closure_iff.mp hz r hr
  exact ⟨c, hc⟩

/-- `k̂₁` is nontrivially normed when `K` has an element of norm `> 1`. -/
instance [hK : Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] :
    NontriviallyNormedField (baseClosure K ι) where
  __ := SubfieldClass.toNormedField (baseClosure K ι)
  non_trivial := by
    obtain ⟨c, hc⟩ := hK.out
    exact ⟨algebraMap K _ c, hc⟩

/-- **The completion of a separably closed field is algebraically closed** (Temkin,
l. 2208–2209). -/
instance [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] [IsSepClosed K] :
    IsAlgClosed (baseClosure K ι) :=
  isAlgClosed_of_denseRange_of_isSepClosed (denseRange_algebraMap_baseClosure ι)

/-- `k̂₁` has the exponential characteristic of `K`. -/
instance (p : ℕ) [ExpChar K p] : ExpChar (baseClosure K ι) p :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- Elements of `K(x)` are mapped into `k̂₁(ι x)`. -/
theorem map_mem_adjoin {x c : L} (hc : c ∈ K⟮x⟯) :
    ι c ∈ IntermediateField.adjoin (baseClosure K ι) {ι x} := by
  induction hc using IntermediateField.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact IntermediateField.mem_adjoin_simple_self _ _
  | algebraMap a =>
    rw [← coe_algebraMap_baseClosure ι a]
    exact IntermediateField.algebraMap_mem _ (algebraMap K (baseClosure K ι) a)
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- Elements of `K(x)` are mapped into `\overline{k̂₁(ι x)}`. -/
theorem map_mem_closureAdjoin {x c : L} (hc : c ∈ K⟮x⟯) :
    ι c ∈ closureAdjoin (baseClosure K ι) (ι x) :=
  adjoin_le_closureAdjoin _ (map_mem_adjoin ι hc)

omit [IsUltrametricDist M] [CompleteSpace M] in
/-- `\overline{k̂₁(ι T)}` is contained in the closure of `ι(K(T))`. -/
theorem closureAdjoin_subset_closure (T : L) :
    (closureAdjoin (baseClosure K ι) (ι T) : Set M) ⊆ closure (ι '' (K⟮T⟯ : Set L)) := by
  set S : Subfield M := ((K⟮T⟯).toSubfield.map ι).topologicalClosure
  have hS : (S : Set M) = closure (ι '' (K⟮T⟯ : Set L)) := rfl
  have hk : ∀ c : baseClosure K ι, algebraMap (baseClosure K ι) M c ∈ S := by
    intro c
    have hc : (c : M) ∈ closure ((ι.comp (algebraMap K L)).fieldRange : Set M) := c.2
    change (c : M) ∈ (S : Set M)
    rw [hS]
    refine closure_mono ?_ hc
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap K L a, IntermediateField.algebraMap_mem _ a, rfl⟩
  let S' : IntermediateField (baseClosure K ι) M := S.toIntermediateField hk
  have hT : ι T ∈ S' :=
    Subfield.le_topologicalClosure _ ⟨T, IntermediateField.mem_adjoin_simple_self K T, rfl⟩
  have hle := closureAdjoin_le (E := S') (Subfield.isClosed_topologicalClosure _) hT
  intro z hz
  have := hle hz
  change z ∈ (S : Set M) at this
  rwa [hS] at this

variable [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)]

/-- **Finiteness of the completion** (used for Theorem 2.1.10): if `L/K(x)` is finite and `L` is
dense in `M`, then `M` is finite over `\overline{k̂₁(ι x)}`. -/
theorem finiteDimensional_closureAdjoin_of_denseRange (hd : DenseRange ι) {x : L}
    [FiniteDimensional K⟮x⟯ L] :
    FiniteDimensional (closureAdjoin (baseClosure K ι) (ι x)) M := by
  set E₀ := closureAdjoin (baseClosure K ι) (ι x)
  let b := Module.finBasis K⟮x⟯ L
  let V : Submodule E₀ M := Submodule.span E₀ (Set.range (ι ∘ b))
  have hVfg : V.FG := Submodule.fg_span (Set.finite_range _)
  have : FiniteDimensional E₀ V := FiniteDimensional.span_of_finite E₀ (Set.finite_range _)
  have hVclosed : IsClosed (V : Set M) := V.closed_of_finiteDimensional
  have hsub : ∀ y : L, ι y ∈ V := by
    intro y
    rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hmem : ι ((b.repr y i : K⟮x⟯) : L) ∈ E₀ := map_mem_closureAdjoin ι (b.repr y i).2
    have : ι (b.repr y i • b i) = (⟨_, hmem⟩ : E₀) • ι (b i) := by
      rw [IntermediateField.smul_def, smul_eq_mul, map_mul, IntermediateField.smul_def,
        smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : V = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ closure (Set.range ι) := by rw [hd.closure_range]; trivial
    exact (hVclosed.closure_subset_iff.mpr (by rintro _ ⟨y, rfl⟩; exact hsub y)) hz
  exact Module.finite_def.mpr (htop ▸ hVfg)

variable {O₁ : ValuationSubring L} {ι}

omit [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] [IsUltrametricDist M] [CompleteSpace M] in
/-- `O₁ ∩ K` is the unit ball of `K` for the norm induced by `ι`. -/
theorem mem_comap_iff_norm (hι : ∀ y, y ∈ O₁ ↔ ‖ι y‖ ≤ 1) (c : K) :
    c ∈ O₁.comap (algebraMap K L) ↔ ‖(ι.comp (algebraMap K L)) c‖ ≤ 1 := hι _

omit [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] in
variable (K) in
/-- `κ(O₁ ∩ K) ≅ κ(k̂₁)`. -/
def residueBaseEquiv (hι : ∀ y, y ∈ O₁ ↔ ‖ι y‖ ≤ 1) :
    ResidueField (O₁.comap (algebraMap K L)) ≃+* ResidueField (unitBall (baseClosure K ι)) :=
  letI f := normRestrict (algebraMap K (baseClosure K ι))
    (ι.comp (algebraMap K L)) (baseClosure K ι).subtype (fun _ ↦ rfl)
    (mem_comap_iff_norm hι) (fun _ ↦ mem_unitBall)
  haveI : IsLocalHom f := isLocalHom_normRestrict _ _ _ _ _ _
  RingEquiv.ofBijective (ResidueField.map f) <|
    bijective_residueField_map_normRestrict _ _ _ _ _ _ fun z ↦ by
      obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp (denseRange_algebraMap_baseClosure ι) z 1
        one_pos
      rw [dist_eq_norm] at hc
      exact ⟨c, hc⟩

omit [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] in
/-- `κ(O₁) ≅ κ(M)`. -/
def residueComplEquiv (hι : ∀ y, y ∈ O₁ ↔ ‖ι y‖ ≤ 1) (hd : DenseRange ι) :
    ResidueField O₁ ≃+* ResidueField (unitBall M) :=
  letI f := normRestrict ι ι (RingHom.id M) (fun _ ↦ rfl) hι (fun _ ↦ mem_unitBall)
  haveI : IsLocalHom f := isLocalHom_normRestrict _ _ _ _ _ _
  RingEquiv.ofBijective (ResidueField.map f) <|
    bijective_residueField_map_normRestrict _ _ _ _ _ _ fun z ↦ by
      obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hd z 1 one_pos
      rw [dist_eq_norm] at hy
      exact ⟨y, hy⟩

omit [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] [CompleteSpace M] in
/-- `κ(O₁) ≅ κ(M)` on residues. -/
theorem residueComplEquiv_residue (hι : ∀ y, y ∈ O₁ ↔ ‖ι y‖ ≤ 1) (hd : DenseRange ι) {y : L}
    (hy : y ∈ O₁) :
    residueComplEquiv hι hd (residue O₁ ⟨y, hy⟩) =
      residue (unitBall M) ⟨ι y, mem_unitBall.mpr ((hι y).mp hy)⟩ := by
  simp only [residueComplEquiv, RingEquiv.ofBijective_apply, ResidueField.map_residue]
  rfl

omit [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] [CompleteSpace M] in
variable (K) in
/-- The residue isomorphisms are compatible with the residue field extensions. -/
theorem comp_residueBaseEquiv (hι : ∀ y, y ∈ O₁ ↔ ‖ι y‖ ≤ 1) (hd : DenseRange ι) :
    (algebraMap (ResidueField (unitBall (baseClosure K ι))) (ResidueField (unitBall M))).comp
        (residueBaseEquiv K hι : ResidueField (O₁.comap (algebraMap K L)) →+* _) =
      (residueComplEquiv hι hd : ResidueField O₁ →+* _).comp
        (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁)) := by
  ext a
  obtain ⟨a, rfl⟩ := residue_surjective a
  simp only [RingHom.comp_apply, RingHom.coe_coe, residueBaseEquiv, residueComplEquiv,
    RingEquiv.ofBijective_apply, ResidueField.map_residue, ResidueField.algebraMap_residue]
  rfl

omit [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)] [CompleteSpace M] in
variable (K) in
/-- The residue field of `k̂₁` has the exponential characteristic of `κ(O₁ ∩ K)`. -/
theorem expChar_residueField_baseClosure (hι : ∀ y, y ∈ O₁ ↔ ‖ι y‖ ≤ 1) (p : ℕ)
    [ExpChar (ResidueField (O₁.comap (algebraMap K L))) p] :
    ExpChar (ResidueField (unitBall (baseClosure K ι))) p :=
  expChar_of_injective_ringHom (residueBaseEquiv K hι).injective p

end Closure

/-! ### Decompletion and Theorem 2.1.10 at the height-one valuation -/

section HeightOne

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O₁ : ValuationSubring L}
  {M : Type*} [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M]
  {ι : L →+* M} (hι : ∀ y, y ∈ O₁ ↔ ‖ι y‖ ≤ 1) (hd : DenseRange ι)
  [Fact (∃ c : K, 1 < ‖ι (algebraMap K L c)‖)]

include hι hd

set_option linter.style.haveILetI false in
/-- **Decompletion at the height-one valuation** (Temkin, Proposition 2.2.1 applied to
`L/K(T)` at `O₁`, l. 2218–2220 and 2230–2231): if `M = L̂₁` is unramified over
`\overline{k̂₁(ι T)}`, then `L/K(T)` has a standard-unramified generator at `O₁` with any
prescribed nonzero residue `η` that is a separable generator of `κ(O₁)/κ(O₁ ∩ K(T))`, and its
minimal polynomial reduces to `minpoly η · X^m` (the adapted form). -/
theorem exists_adapted_of_isUnramified {T : L} [FiniteDimensional K⟮T⟯ L]
    [Algebra.IsSeparable K⟮T⟯ L]
    (hU : IsUnramified (closureAdjoin (baseClosure K ι) (ι T)) M)
    {η : ResidueField O₁} (hη0 : η ≠ 0)
    (hgen : IntermediateField.adjoin (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) {η} = ⊤)
    (hsep : IsSeparable (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) η) :
    ∃ y : L, ∃ hy : IsStdUnramifiedGenerator K⟮T⟯ O₁ y, residue O₁ ⟨y, hy.mem⟩ = η ∧
      ∃ m : ℕ, (minpoly (O₁.comap (algebraMap K⟮T⟯ L)) y).map
          (residue (O₁.comap (algebraMap K⟮T⟯ L))) =
        minpoly (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) η * X ^ m := by
  set E := closureAdjoin (baseClosure K ι) (ι T)
  letI : Algebra L M := ι.toAlgebra
  letI : Algebra K⟮T⟯ M := (ι.comp (algebraMap K⟮T⟯ L)).toAlgebra
  have hmemE : ∀ c : K⟮T⟯, (ι.comp (algebraMap K⟮T⟯ L)) c ∈ E := fun c ↦
    map_mem_closureAdjoin ι c.2
  letI : Algebra K⟮T⟯ E := ((ι.comp (algebraMap K⟮T⟯ L)).codRestrict E hmemE).toAlgebra
  haveI : @IsScalarTower K⟮T⟯ E M Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : @IsScalarTower K⟮T⟯ L M Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hB : ∀ y, y ∈ O₁ ↔ ‖algebraMap L M y‖ ≤ 1 := hι
  have hdK : DenseRange (algebraMap K⟮T⟯ E) := by
    rw [Metric.denseRange_iff]
    intro z r hr
    obtain ⟨_, ⟨c, hc, rfl⟩, hcz⟩ := Metric.mem_closure_iff.mp
      (closureAdjoin_subset_closure ι T z.2) r hr
    exact ⟨⟨c, hc⟩, hcz⟩
  have hdL : DenseRange (algebraMap L M) := hd
  haveI := hU.finiteDimensional
  have hdeg : Module.finrank E M ≤
      Module.finrank (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) (ResidueField O₁) := by
    rw [(finrank_residueField_eq_of_denseRange O₁ hB hdK hdL).1, ← hU.inertiaDegree_eq]
    rfl
  exact exists_isStdUnramifiedGenerator_of_finrank_le O₁ hB hdK hdeg hη0 hgen hsep

set_option linter.style.haveILetI false in
/-- **Theorem 2.1.10(iii) at the height-one valuation** (Temkin, l. 2227–2231): let `T ∈ O₁`
have residue transcendental over `κ(O₁ ∩ K)`, with `L/K(T)` finite and `κ(O₁)/κ(O₁ ∩ K(T))`
separable. Then `M = L̂₁` is finite and unramified over `\overline{k̂₁(ι T)}`. -/
theorem isUnramified_of_transcendental [IsSepClosed K] (p : ℕ) [ExpChar K p]
    [ExpChar (ResidueField (O₁.comap (algebraMap K L))) p] {T : L} (hT : T ∈ O₁)
    (htr : Transcendental (ResidueField (O₁.comap (algebraMap K L))) (residue O₁ ⟨T, hT⟩))
    [FiniteDimensional K⟮T⟯ L]
    [hsep : Algebra.IsSeparable (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) (ResidueField O₁)] :
    IsUnramified (closureAdjoin (baseClosure K ι) (ι T)) M := by
  haveI := expChar_residueField_baseClosure K hι p
  set E := closureAdjoin (baseClosure K ι) (ι T)
  have hx : ‖ι T‖ ≤ 1 := (hι T).mp hT
  -- the residue of `ι T` is transcendental over the residue field of `k̂₁`
  have htr' : Transcendental (ResidueField (unitBall (baseClosure K ι)))
      (residue (unitBall M) ⟨ι T, mem_unitBall.mpr hx⟩) := by
    have := htr.ringHom_of_comp_eq (residueBaseEquiv K hι) (residueComplEquiv hι hd)
      (residueBaseEquiv K hι).surjective (residueComplEquiv hι hd).injective
      (comp_residueBaseEquiv K hι hd)
    rwa [residueComplEquiv_residue] at this
  have hGK := isGaussGenerator_closureAdjoin (isGaussElement_of_transcendental_residue hx htr')
  haveI : FiniteDimensional E M := finiteDimensional_closureAdjoin_of_denseRange ι hd
  -- separability of the residue extension of `M/E`
  letI : Algebra L M := ι.toAlgebra
  letI : Algebra K⟮T⟯ M := (ι.comp (algebraMap K⟮T⟯ L)).toAlgebra
  have hmemE : ∀ c : K⟮T⟯, (ι.comp (algebraMap K⟮T⟯ L)) c ∈ E := fun c ↦
    map_mem_closureAdjoin ι c.2
  letI : Algebra K⟮T⟯ E := ((ι.comp (algebraMap K⟮T⟯ L)).codRestrict E hmemE).toAlgebra
  haveI : @IsScalarTower K⟮T⟯ E M Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : @IsScalarTower K⟮T⟯ L M Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hdK : DenseRange (algebraMap K⟮T⟯ E) := by
    rw [Metric.denseRange_iff]
    intro z r hr
    obtain ⟨_, ⟨c, hc, rfl⟩, hcz⟩ := Metric.mem_closure_iff.mp
      (closureAdjoin_subset_closure ι T z.2) r hr
    exact ⟨⟨c, hc⟩, hcz⟩
  haveI : Algebra.IsSeparable (ResidueField (unitBall E)) (ResidueField (unitBall M)) :=
    isSeparable_residueField_of_denseRange O₁ hι hdK hd
  exact IsGaussGenerator.isUnramified (k := baseClosure K ι) (K := E) (L := M) p hGK

omit hι hd [IsUltrametricDist M] [CompleteSpace M] in
/-- An element `π ∈ K` with `0 < ‖ι π‖ < 1`. -/
theorem exists_norm_pos_lt_one : ∃ π : K, 0 < ‖ι (algebraMap K L π)‖ ∧
    ‖ι (algebraMap K L π)‖ < 1 := by
  obtain ⟨c, hc⟩ := (Fact.out : ∃ c : K, 1 < ‖ι (algebraMap K L c)‖)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    linarith
  refine ⟨c⁻¹, ?_, ?_⟩
  · rw [map_inv₀, map_inv₀, norm_inv]
    exact inv_pos.mpr (one_pos.trans hc)
  · rw [map_inv₀, map_inv₀, norm_inv]
    exact inv_lt_one_of_one_lt₀ hc

omit hι hd [IsUltrametricDist M] [CompleteSpace M] in
/-- Three distinct elements `c ∈ K` with `‖ι (c w)‖ < δ`. -/
theorem exists_three_small (w : L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c₀ c₁ c₂ : K, c₀ ≠ c₁ ∧ c₀ ≠ c₂ ∧ c₁ ≠ c₂ ∧
      ∀ c ∈ ({c₀, c₁, c₂} : Set K), ‖ι (c • w)‖ < δ := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_pos_lt_one (K := K) (ι := ι)
  set r := ‖ι (algebraMap K L π)‖
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hδ (by positivity :
    (0 : ℝ) < ‖ι w‖ + 1)) hπ1
  have hnorm : ∀ k : ℕ, ‖ι ((π ^ (N + k)) • w)‖ = r ^ (N + k) * ‖ι w‖ := fun k ↦ by
    rw [Algebra.smul_def, map_mul, map_pow, map_pow, norm_mul, norm_pow]
  have hsmall : ∀ k : ℕ, ‖ι ((π ^ (N + k)) • w)‖ < δ := fun k ↦ by
    rw [hnorm]
    have h1 : r ^ (N + k) ≤ r ^ N := pow_le_pow_of_le_one hπ0.le hπ1.le (Nat.le_add_right _ _)
    calc r ^ (N + k) * ‖ι w‖ ≤ r ^ N * ‖ι w‖ := by gcongr
      _ ≤ r ^ N * (‖ι w‖ + 1) := by gcongr; linarith
      _ < δ / (‖ι w‖ + 1) * (‖ι w‖ + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ (by positivity)
  have hne : ∀ a b : ℕ, a < b → π ^ (N + a) ≠ π ^ (N + b) := by
    intro a b hab h
    have := congrArg (fun c : K ↦ ‖ι (algebraMap K L c)‖) h
    simp only [map_pow, norm_pow] at this
    exact (pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 (by omega : N + a < N + b)).ne' this
  refine ⟨π ^ (N + 0), π ^ (N + 1), π ^ (N + 2), hne 0 1 (by omega), hne 0 2 (by omega),
    hne 1 2 (by omega), ?_⟩
  rintro c (rfl | rfl | rfl) <;> exact hsmall _

omit hd [IsUltrametricDist M] [CompleteSpace M] in
/-- **Lifting a residue** (Temkin, l. 2227–2228): a residue `T̃` transcendental over `κ(O₁ ∩ K)`
lifts to some `T ∈ O₁`, transcendental over `K`, with `L/K(T)` finite and separable (that is,
`T ∉ K Lᵖ`). -/
theorem exists_lift (p : ℕ) [ExpChar K p] (hfg : (⊤ : IntermediateField K L).FG) {x₀ : L}
    (hx₀ : Transcendental K x₀) [FiniteDimensional K⟮x₀⟯ L] [Algebra.IsSeparable K⟮x₀⟯ L]
    {T₀ : L} (hT₀ : T₀ ∈ O₁)
    (htr : Transcendental (ResidueField (O₁.comap (algebraMap K L))) (residue O₁ ⟨T₀, hT₀⟩)) :
    ∃ T : L, ∃ hT : T ∈ O₁, residue O₁ ⟨T, hT⟩ = residue O₁ ⟨T₀, hT₀⟩ ∧ Transcendental K T ∧
      FiniteDimensional K⟮T⟯ L ∧ Algebra.IsSeparable K⟮T⟯ L := by
  have hw := notMem_badField p hfg hx₀
  obtain ⟨c₀, c₁, c₂, h01, h02, h12, hsmall⟩ := exists_three_small (K := K) (ι := ι) x₀ one_pos
  obtain ⟨c, hc, hcbad, -⟩ := exists_add_smul_notMem _ _ hw hw T₀ h01 h02 h12
  have hcw : O₁.valuation (c • x₀) < 1 :=
    (valuation_lt_one_iff_of_forall_mem_iff hι _).mpr (hsmall c hc)
  have hcwO : c • x₀ ∈ O₁ := (O₁.valuation_le_one_iff _).mp hcw.le
  have hT : T₀ + c • x₀ ∈ O₁ := add_mem hT₀ hcwO
  have hres : residue O₁ ⟨T₀ + c • x₀, hT⟩ = residue O₁ ⟨T₀, hT₀⟩ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    have : (⟨T₀ + c • x₀, hT⟩ - ⟨T₀, hT₀⟩ : O₁) = ⟨c • x₀, hcwO⟩ :=
      Subtype.ext (add_sub_cancel_left _ _)
    rw [this]
    exact hcw
  have htrT : Transcendental (ResidueField (O₁.comap (algebraMap K L)))
      (residue O₁ ⟨T₀ + c • x₀, hT⟩) := by rwa [hres]
  have hTK := transcendental_of_transcendental_residue hT htrT
  obtain ⟨hfin, hsep⟩ := finiteDimensional_isSeparable_of_notMem p hfg hx₀ hTK fun _ ↦ hcbad
  exact ⟨_, hT, hres, hTK, hfin, hsep⟩

/-- **Theorem 2.1.10(i)(ii) at the height-one valuation, with density** (Temkin,
l. 2214–2220): some `x ∈ L`, transcendental over `K` and not in `K Lᵖ`, has `M = L̂₁` finite
and unramified over `\overline{k̂₁(ι x)}`; `L/K(x)` is finite and separable. -/
theorem exists_isUnramified_transcendental [IsSepClosed K] (p : ℕ) [ExpChar K p]
    [ExpChar (ResidueField (O₁.comap (algebraMap K L))) p] (hfg : (⊤ : IntermediateField K L).FG)
    {x₀ : L} (hx₀ : Transcendental K x₀) [FiniteDimensional K⟮x₀⟯ L]
    [Algebra.IsSeparable K⟮x₀⟯ L] :
    ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L ∧ Algebra.IsSeparable K⟮x⟯ L ∧
      IsUnramified (closureAdjoin (baseClosure K ι) (ι x)) M := by
  have := expChar_residueField_baseClosure K hι p
  have : FiniteDimensional (closureAdjoin (baseClosure K ι) (ι x₀)) M :=
    finiteDimensional_closureAdjoin_of_denseRange ι hd
  obtain ⟨-, ⟨z, ε, hε, hU⟩, -⟩ := uniformization_analytic (k := baseClosure K ι) (L := M) p
    (ι x₀)
  obtain ⟨x₁, hx₁⟩ := Metric.denseRange_iff.mp hd z ε hε
  rw [dist_eq_norm] at hx₁
  have hw₁ := notMem_badField p hfg hx₀
  have hw₂ : x₀ ∉ algebraicClosure K L := by
    rw [mem_algebraicClosure_iff]
    exact hx₀
  obtain ⟨c₀, c₁, c₂, h01, h02, h12, hsmall⟩ := exists_three_small (K := K) (ι := ι) x₀
    (sub_pos.mpr hx₁)
  obtain ⟨c, hc, hcbad, hcalg⟩ := exists_add_smul_notMem _ _ hw₁ hw₂ x₁ h01 h02 h12
  have hxK : Transcendental K (x₁ + c • x₀) := by
    rwa [mem_algebraicClosure_iff] at hcalg
  obtain ⟨hfin, hsep⟩ := finiteDimensional_isSeparable_of_notMem p hfg hx₀ hxK fun _ ↦ hcbad
  refine ⟨_, hxK, hfin, hsep, hU _ ?_⟩
  have h1 := hsmall c hc
  calc ‖z - ι (x₁ + c • x₀)‖ = ‖(z - ι x₁) - ι (c • x₀)‖ := by rw [map_add, sub_add_eq_sub_sub]
    _ ≤ max ‖z - ι x₁‖ ‖ι (c • x₀)‖ := norm_sub_le_max _ _
    _ < ε := max_lt hx₁ (by linarith [norm_nonneg (z - ι x₁)])

end HeightOne

/-! ### The height-one step for the completion `L̂₁` -/

section Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O₁ : ValuationSubring L}
  [O₁.valuation.RankOne]

/-- `O₁` is the trace of the unit ball of its completion. -/
theorem mem_iff_norm_toCompletion_le_one (y : L) :
    y ∈ O₁ ↔ ‖toCompletion O₁.valuation y‖ ≤ 1 := by
  rw [norm_toCompletion_le_one_iff, ValuationSubring.valuation_le_one_iff]

/-- If `O₁ ∩ K ≠ K`, some element of `K` has norm `> 1` in `L̂₁`. -/
theorem fact_exists_one_lt_norm (hA : O₁.comap (algebraMap K L) ≠ ⊤) :
    Fact (∃ c : K, 1 < ‖toCompletion O₁.valuation (algebraMap K L c)‖) := by
  obtain ⟨a, ha⟩ : ∃ a : K, a ∉ O₁.comap (algebraMap K L) := by
    by_contra h
    push Not at h
    exact hA (eq_top_iff.mpr fun a _ ↦ h a)
  exact ⟨⟨a, not_le.mp fun h ↦
    ha ((mem_iff_norm_toCompletion_le_one (O₁ := O₁) (algebraMap K L a)).mpr h)⟩⟩

/-- **The height-one step, transcendental residue case** (Temkin, proof of Theorem 2.1.8,
l. 2224–2231): let `O₁` be a rank-one valuation ring of `L` with `O₁ ∩ K ≠ K`, and let `T ∈ O₁`
have residue transcendental over `κ(O₁ ∩ K)`, with `L/K(T)` finite separable and
`κ(O₁)/κ(O₁ ∩ K(T))` separable. Then for every nonzero separable generator `η` of
`κ(O₁)/κ(O₁ ∩ K(T))` there is a standard-unramified generator of `L/K(T)` at `O₁` with residue
`η`, in the adapted form. -/
theorem exists_adapted_of_transcendental [IsSepClosed K]
    (hA : O₁.comap (algebraMap K L) ≠ ⊤) (p : ℕ) [ExpChar K p]
    [ExpChar (ResidueField (O₁.comap (algebraMap K L))) p] {T : L} (hT : T ∈ O₁)
    (htr : Transcendental (ResidueField (O₁.comap (algebraMap K L))) (residue O₁ ⟨T, hT⟩))
    [FiniteDimensional K⟮T⟯ L] [Algebra.IsSeparable K⟮T⟯ L]
    [Algebra.IsSeparable (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) (ResidueField O₁)]
    {η : ResidueField O₁} (hη0 : η ≠ 0)
    (hgen : IntermediateField.adjoin (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) {η} = ⊤)
    (hsep : IsSeparable (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) η) :
    ∃ y : L, ∃ hy : IsStdUnramifiedGenerator K⟮T⟯ O₁ y, residue O₁ ⟨y, hy.mem⟩ = η ∧
      ∃ m : ℕ, (minpoly (O₁.comap (algebraMap K⟮T⟯ L)) y).map
          (residue (O₁.comap (algebraMap K⟮T⟯ L))) =
        minpoly (ResidueField (O₁.comap (algebraMap K⟮T⟯ L))) η * X ^ m := by
  have := fact_exists_one_lt_norm hA
  have hι := mem_iff_norm_toCompletion_le_one (O₁ := O₁)
  have hd := denseRange_toCompletion O₁.valuation
  exact exists_adapted_of_isUnramified hι hd
    (isUnramified_of_transcendental hι hd p hT htr) hη0 hgen hsep

/-- **Lifting a residue** (Temkin, l. 2227–2228) for the rank-one valuation ring `O₁`. -/
theorem exists_lift_of_rankOne (hA : O₁.comap (algebraMap K L) ≠ ⊤) (p : ℕ) [ExpChar K p]
    (hfg : (⊤ : IntermediateField K L).FG) {x₀ : L} (hx₀ : Transcendental K x₀)
    [FiniteDimensional K⟮x₀⟯ L] [Algebra.IsSeparable K⟮x₀⟯ L] {T₀ : L} (hT₀ : T₀ ∈ O₁)
    (htr : Transcendental (ResidueField (O₁.comap (algebraMap K L))) (residue O₁ ⟨T₀, hT₀⟩)) :
    ∃ T : L, ∃ hT : T ∈ O₁, residue O₁ ⟨T, hT⟩ = residue O₁ ⟨T₀, hT₀⟩ ∧ Transcendental K T ∧
      FiniteDimensional K⟮T⟯ L ∧ Algebra.IsSeparable K⟮T⟯ L := by
  have := fact_exists_one_lt_norm hA
  exact exists_lift (mem_iff_norm_toCompletion_le_one (O₁ := O₁)) p hfg hx₀ hT₀ htr

/-- **The height-one step, trivial residue extension case** (Temkin, proof of Theorem 2.1.8,
l. 2213–2223): if `κ(O₁) = κ(O₁ ∩ K)`, there is `x ∈ L`, transcendental over `K` with `L/K(x)`
finite separable, such that `L/K(x)` has a standard-unramified generator at `O₁` with residue `1`
whose minimal polynomial reduces to `(X - 1) X^m`. -/
theorem exists_adapted_of_surjective [IsSepClosed K] (hA : O₁.comap (algebraMap K L) ≠ ⊤)
    (p : ℕ) [ExpChar K p] [ExpChar (ResidueField (O₁.comap (algebraMap K L))) p]
    (hfg : (⊤ : IntermediateField K L).FG) {x₀ : L} (hx₀ : Transcendental K x₀)
    [FiniteDimensional K⟮x₀⟯ L] [Algebra.IsSeparable K⟮x₀⟯ L]
    (hsurj : Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K L))) (ResidueField O₁))) :
    ∃ x : L, Transcendental K x ∧ FiniteDimensional K⟮x⟯ L ∧ Algebra.IsSeparable K⟮x⟯ L ∧
      ∃ y : L, ∃ hy : IsStdUnramifiedGenerator K⟮x⟯ O₁ y, residue O₁ ⟨y, hy.mem⟩ = 1 ∧
        ∃ m : ℕ, (minpoly (O₁.comap (algebraMap K⟮x⟯ L)) y).map
            (residue (O₁.comap (algebraMap K⟮x⟯ L))) =
          minpoly (ResidueField (O₁.comap (algebraMap K⟮x⟯ L))) (1 : ResidueField O₁) *
            X ^ m := by
  have := fact_exists_one_lt_norm hA
  have hι := mem_iff_norm_toCompletion_le_one (O₁ := O₁)
  have hd := denseRange_toCompletion O₁.valuation
  obtain ⟨x, hxK, hfin, hsep, hU⟩ := exists_isUnramified_transcendental hι hd p hfg hx₀
  refine ⟨x, hxK, hfin, hsep, ?_⟩
  have hsurj' : Function.Surjective
      (algebraMap (ResidueField (O₁.comap (algebraMap K⟮x⟯ L))) (ResidueField O₁)) := by
    intro z
    obtain ⟨a, rfl⟩ := hsurj z
    obtain ⟨a, rfl⟩ := residue_surjective a
    exact ⟨_, algebraMap_residue_comap (T := x) a⟩
  have hgen := DVRCoordinate.adjoin_one_eq_top_of_surjective hsurj'
  have hsep1 : IsSeparable (ResidueField (O₁.comap (algebraMap K⟮x⟯ L))) (1 : ResidueField O₁) := by
    rw [← map_one (algebraMap (ResidueField (O₁.comap (algebraMap K⟮x⟯ L))) (ResidueField O₁))]
    exact isSeparable_algebraMap 1
  exact exists_adapted_of_isUnramified hι hd hU one_ne_zero hgen hsep1

end Completion

end DeJongAlterations.StableModification.Valuation.MainUniformization

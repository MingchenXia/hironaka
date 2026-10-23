import DeJongAlterations.StableModification.Valuation.FunctionField.PoleNorm

/-!
# Frobenius-graded bases of function fields (Temkin, Lemma 6.2.6)

Let `E` be a perfect field of characteristic `p > 0` and `F/E` a function field of one variable in
which `E` is algebraically closed. Then there is `U ⊆ F ∖ F ^ p` such that
`{1} ⊔ U ⊔ U ^ p ⊔ U ^ (p ^ 2) ⊔ ⋯` is a basis of `F` over `E` and `span_E U ∩ F ^ p = 0`
(`exists_frobeniusBasis`). This is Lemma 6.2.6 (`basislem`) of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010) (`semi-stable.tex`, lines 3758–3784), for
function fields of one variable, the case used in the proof of Proposition 6.2.5 (type-2 fields,
with `F` the residue field `L̃` over `E = k̃`).

The proof follows Temkin's and is split in two parts.

* **Abstract part** (`IsFrobeniusNorm.exists_frobeniusBasis`): for any `ν : F → ℕ` which is
  ultrametric, `E`-invariant, satisfies `ν (f ^ p) = p * ν f` and vanishes exactly on `E`
  (`IsFrobeniusNorm`), one chooses `U = ⋃ₙ Tₙ₊₁`, where `Tₙ₊₁ ⊆ {ν ≤ n + 1}` lifts a basis of the
  image of `{ν ≤ n + 1}` in `F / ({ν ≤ n} + F ^ p)`. Then `U` is independent modulo `F ^ p`
  (`linearIndepOn_mkQ`), every `f` is congruent modulo `F ^ p` to some `f₀ ∈ span U` with
  `ν f₀ ≤ ν f` (`exists_reduction`), and iterating the Frobenius shows that the family spans
  (`span_frobeniusFamily`); independence follows by Frobenius descent
  (`linearIndependent_frobeniusFamily`).
* **Concrete part** (`exists_frobeniusBasis`): the pole-order norm `poleNorm E` is such a function
  (`isFrobeniusNorm_poleNorm`).

Temkin's filtration of `V = F / F ^ p` by "balls of radii less than `n`" has to be read as balls of
radius at most `n` (his `Uₙ` consists of elements of norm `n` whose images span `Vₙ`); here the
filtration is `{ν ≤ n}`. The blueprint chapter is `blueprint/src/sm-val-funfield.tex` (plan node
F3 of `PLAN-SM-VAL`).
-/

open scoped IntermediateField

noncomputable section

namespace DeJongAlterations.StableModification.Valuation.FunctionField

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

section Abstract

variable (E) (p : ℕ)

/-- An `ℕ`-valued function `ν` on `F` adapted to the Frobenius: it is ultrametric, does not increase
under multiplication by constants, satisfies `ν (f ^ p) = p * ν f`, and vanishes exactly on the
constants. The pole-order norm of a function field of one variable is the example
(`isFrobeniusNorm_poleNorm`). -/
structure IsFrobeniusNorm (ν : F → ℕ) : Prop where
  add_le : ∀ f g : F, ν (f + g) ≤ max (ν f) (ν g)
  smul_le : ∀ (c : E) (f : F), ν (c • f) ≤ ν f
  pow_char : ∀ f : F, ν (f ^ p) = p * ν f
  eq_zero_iff : ∀ f : F, ν f = 0 ↔ f ∈ (algebraMap E F).range

variable {E}

/-- The family `{1} ⊔ U ⊔ U ^ p ⊔ U ^ (p ^ 2) ⊔ ⋯`, indexed by `Option (ℕ × U)`: `none ↦ 1` and
`(j, u) ↦ u ^ p ^ j`. -/
def frobeniusFamily (U : Set F) : Option (ℕ × U) → F
  | none => 1
  | some x => (x.2 : F) ^ p ^ x.1

namespace IsFrobeniusNorm

variable {p} {ν : F → ℕ} (hν : IsFrobeniusNorm E p ν)
include hν

/-- `ν 0 = 0`. -/
theorem apply_zero : ν 0 = 0 := (hν.eq_zero_iff 0).mpr ⟨0, map_zero _⟩

/-- `ν (-f) = ν f`. -/
theorem apply_neg (f : F) : ν (-f) = ν f := by
  refine le_antisymm ?_ ?_
  · simpa using hν.smul_le (-1) f
  · simpa using hν.smul_le (-1) (-f)

/-- `ν (f - g) ≤ max (ν f) (ν g)`. -/
theorem sub_le (f g : F) : ν (f - g) ≤ max (ν f) (ν g) := by
  rw [sub_eq_add_neg, ← hν.apply_neg g]; exact hν.add_le f (-g)

/-- `ν (f ^ p ^ i) = p ^ i * ν f`. -/
theorem pow_char_pow (f : F) (i : ℕ) : ν (f ^ p ^ i) = p ^ i * ν f := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, hν.pow_char, ih, ← mul_assoc, mul_comm p]

/-- The subspace `{f | ν f ≤ n}`. -/
def ball (n : ℕ) : Submodule E F where
  carrier := {f | ν f ≤ n}
  add_mem' ha hb := (hν.add_le _ _).trans (max_le ha hb)
  zero_mem' := by simp [Set.mem_ofPred_eq, hν.apply_zero]
  smul_mem' c _ hf := (hν.smul_le c _).trans hf

/-- Membership in `ball`. -/
theorem mem_ball {n : ℕ} {f : F} : f ∈ hν.ball n ↔ ν f ≤ n := Iff.rfl

/-- The balls increase with the radius. -/
theorem ball_mono {m n : ℕ} (h : m ≤ n) : hν.ball m ≤ hν.ball n := fun _ hf => le_trans hf h

end IsFrobeniusNorm

variable [Fact p.Prime] [CharP F p] [PerfectField E]

variable (E) in
/-- `F ^ p` as an `E`-subspace of `F`. -/
def frobeniusSubmodule : Submodule E F where
  carrier := {x | ∃ g : F, g ^ p = x}
  add_mem' := by
    rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g + h, add_pow_char g h p⟩
  zero_mem' := ⟨0, zero_pow (Fact.out : p.Prime).ne_zero⟩
  smul_mem' := by
    rintro c _ ⟨g, rfl⟩
    have : CharP E p := (algebraMap E F).charP (algebraMap E F).injective p
    have : ExpChar E p := ExpChar.prime Fact.out
    have : PerfectRing E p := PerfectField.toPerfectRing p
    exact ⟨(frobeniusEquiv E p).symm c • g, by rw [smul_pow, frobeniusEquiv_symm_pow_p]⟩

/-- Membership in `frobeniusSubmodule`. -/
theorem mem_frobeniusSubmodule {x : F} : x ∈ frobeniusSubmodule E p ↔ ∃ g : F, g ^ p = x :=
  Iff.rfl

/-- `p`-th powers lie in `F ^ p`. -/
theorem pow_mem_frobeniusSubmodule (g : F) : g ^ p ∈ frobeniusSubmodule E p := ⟨g, rfl⟩

/-- Constants lie in `F ^ p`, as `E` is perfect. -/
theorem algebraMap_mem_frobeniusSubmodule (c : E) : algebraMap E F c ∈ frobeniusSubmodule E p := by
  have : CharP E p := (algebraMap E F).charP (algebraMap E F).injective p
  have : ExpChar E p := ExpChar.prime Fact.out
  have : PerfectRing E p := PerfectField.toPerfectRing p
  exact ⟨algebraMap E F ((frobeniusEquiv E p).symm c), by
    rw [← map_pow, frobeniusEquiv_symm_pow_p]⟩

namespace IsFrobeniusNorm

variable {p} {ν : F → ℕ} (hν : IsFrobeniusNorm E p ν)
include hν

/-- The level `n + 1` of the construction: a subset of `{ν ≤ n + 1}` lifting a basis of the image
of `{ν ≤ n + 1}` in `F / ({ν ≤ n} + F ^ p)`. -/
theorem exists_level (n : ℕ) : ∃ T : Set F, T ⊆ hν.ball (n + 1) ∧
    LinearIndepOn E (hν.ball n ⊔ frobeniusSubmodule E p).mkQ T ∧
    ∀ f ∈ hν.ball (n + 1), ∃ g ∈ Submodule.span E T,
      f - g ∈ hν.ball n ⊔ frobeniusSubmodule E p := by
  set G := hν.ball n ⊔ frobeniusSubmodule E p
  set S : Set (F ⧸ G) := G.mkQ '' (hν.ball (n + 1) : Set F)
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent E S
  have hlift : ∀ y : b, ∃ f : F, f ∈ hν.ball (n + 1) ∧ G.mkQ f = y := fun y => by
    obtain ⟨f, hf, hfy⟩ := hbS y.2; exact ⟨f, hf, hfy⟩
  choose ℓ hℓ hℓy using hlift
  have hinj : Function.Injective ℓ := fun y z h => Subtype.ext (by rw [← hℓy y, ← hℓy z, h])
  refine ⟨Set.range ℓ, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩; exact hℓ y
  · rw [linearIndepOn_range_iff hinj]
    have : (G.mkQ ∘ ℓ) = Subtype.val := funext hℓy
    rw [this]; exact hli
  · intro f hf
    have hmem : G.mkQ f ∈ Submodule.span E b := hspan ▸ Submodule.subset_span ⟨f, hf, rfl⟩
    have hb : b = G.mkQ '' Set.range ℓ := by
      ext y
      constructor
      · intro hy; exact ⟨ℓ ⟨y, hy⟩, ⟨_, rfl⟩, hℓy _⟩
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩; rw [hℓy]; exact z.2
    rw [hb, Submodule.span_image] at hmem
    obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp hmem
    exact ⟨g, hg, (Submodule.Quotient.eq G).mp (by simpa using hgf.symm)⟩

/-- The chosen set of level `n + 1`. -/
def level (n : ℕ) : Set F := Classical.choose (hν.exists_level n)

/-- The set of level `n + 1` lies in `{ν ≤ n + 1}`. -/
theorem level_subset (n : ℕ) : hν.level n ⊆ hν.ball (n + 1) :=
  (Classical.choose_spec (hν.exists_level n)).1

/-- The set of level `n + 1` is linearly independent modulo `{ν ≤ n} + F ^ p`. -/
theorem level_linearIndepOn (n : ℕ) :
    LinearIndepOn E (hν.ball n ⊔ frobeniusSubmodule E p).mkQ (hν.level n) :=
  (Classical.choose_spec (hν.exists_level n)).2.1

/-- The set of level `n + 1` spans `{ν ≤ n + 1}` modulo `{ν ≤ n} + F ^ p`. -/
theorem level_spec (n : ℕ) : ∀ f ∈ hν.ball (n + 1), ∃ g ∈ Submodule.span E (hν.level n),
    f - g ∈ hν.ball n ⊔ frobeniusSubmodule E p :=
  (Classical.choose_spec (hν.exists_level n)).2.2

/-- The set `U = ⋃ₙ T_{n+1}` of Temkin's construction. -/
def basisSet : Set F := ⋃ n, hν.level n

/-- **(a)** The image of `U` in `F / F ^ p` is linearly independent. -/
theorem linearIndepOn_mkQ : LinearIndepOn E (frobeniusSubmodule E p).mkQ hν.basisSet := by
  classical
  set W : Submodule E F := frobeniusSubmodule E p
  have claim : ∀ N : ℕ, ∀ (t : Finset F) (g : F → E),
      (↑t ⊆ ⋃ n ∈ Finset.range N, hν.level n) → ∑ i ∈ t, g i • i ∈ W → ∀ i ∈ t, g i = 0 := by
    intro N
    induction N with
    | zero =>
      intro t g ht _ i hi
      have := ht hi
      simp at this
    | succ N ih =>
      intro t g ht hW
      set t1 := t.filter (· ∈ hν.level N)
      set t2 := t.filter (· ∉ hν.level N)
      have hsplit : ∑ i ∈ t, g i • i = ∑ i ∈ t1, g i • i + ∑ i ∈ t2, g i • i :=
        (Finset.sum_filter_add_sum_filter_not t _ _).symm
      have ht2 : ↑t2 ⊆ ⋃ n ∈ Finset.range N, hν.level n := by
        intro i hi
        obtain ⟨hit, hiN⟩ := Finset.mem_filter.mp hi
        obtain ⟨n, hn, hin⟩ := Set.mem_iUnion₂.mp (ht hit)
        have hnN : n ≠ N := fun h => hiN (h ▸ hin)
        exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hn; omega), hin⟩
      have h2ball : ∑ i ∈ t2, g i • i ∈ hν.ball N := by
        refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
        obtain ⟨n, hn, hin⟩ := Set.mem_iUnion₂.mp (ht2 hi)
        exact hν.ball_mono (Finset.mem_range.mp hn) (hν.level_subset n hin)
      have h1G : ∑ i ∈ t1, g i • i ∈ hν.ball N ⊔ W := by
        have : ∑ i ∈ t1, g i • i = ∑ i ∈ t, g i • i - ∑ i ∈ t2, g i • i := by
          rw [hsplit]; abel
        rw [this]
        exact sub_mem (Submodule.mem_sup_right hW) (Submodule.mem_sup_left h2ball)
      have h1zero : ∀ i ∈ t1, g i = 0 := by
        have hli := hν.level_linearIndepOn N
        rw [linearIndepOn_iff'] at hli
        refine hli t1 g (fun i hi => (Finset.mem_filter.mp hi).2) ?_
        have : ∑ i ∈ t1, g i • (hν.ball N ⊔ W).mkQ i = (hν.ball N ⊔ W).mkQ (∑ i ∈ t1, g i • i) := by
          simp [map_sum]
        rw [this]
        exact (Submodule.Quotient.mk_eq_zero _).mpr h1G
      have h2W : ∑ i ∈ t2, g i • i ∈ W := by
        have : ∑ i ∈ t1, g i • i = 0 :=
          Finset.sum_eq_zero fun i hi => by rw [h1zero i hi, zero_smul]
        rw [hsplit, this, zero_add] at hW
        exact hW
      intro i hi
      by_cases hiN : i ∈ hν.level N
      · exact h1zero i (Finset.mem_filter.mpr ⟨hi, hiN⟩)
      · exact ih t2 g ht2 h2W i (Finset.mem_filter.mpr ⟨hi, hiN⟩)
  rw [linearIndepOn_iff']
  intro t g ht hsum
  have hx : ∀ x ∈ t, ∃ n, x ∈ hν.level n := fun x hx => Set.mem_iUnion.mp (ht hx)
  choose! nx hnx using hx
  refine claim (t.sup nx + 1) t g (fun x hx => Set.mem_iUnion₂.mpr
    ⟨nx x, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hx)), hnx x hx⟩) ?_
  have : W.mkQ (∑ i ∈ t, g i • i) = 0 := by rw [map_sum]; simpa using hsum
  exact (Submodule.Quotient.mk_eq_zero _).mp this

/-- **(b)** Every `f` is congruent modulo `F ^ p` to some `f₀ ∈ span U` with `ν f₀ ≤ ν f`. -/
theorem exists_reduction (n : ℕ) : ∀ f : F, ν f ≤ n →
    ∃ f₀ ∈ Submodule.span E hν.basisSet, f - f₀ ∈ frobeniusSubmodule E p ∧ ν f₀ ≤ n := by
  induction n with
  | zero =>
    intro f hf
    obtain ⟨c, rfl⟩ := (hν.eq_zero_iff f).mp (Nat.le_zero.mp hf)
    exact ⟨0, Submodule.zero_mem _, by rw [sub_zero]; exact algebraMap_mem_frobeniusSubmodule p c,
      by rw [hν.apply_zero]⟩
  | succ n ih =>
    intro f hf
    obtain ⟨g, hg, hfg⟩ := hν.level_spec n f hf
    obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp hfg
    obtain ⟨y₀, hy₀, hyy₀, hy₀n⟩ := ih y hy
    refine ⟨g + y₀, Submodule.add_mem _ (Submodule.span_mono (Set.subset_iUnion _ n) hg) hy₀,
      ?_, ?_⟩
    · have : f - (g + y₀) = (y - y₀) + w := by rw [← sub_sub, ← hyw]; abel
      rw [this]; exact Submodule.add_mem _ hyy₀ hw
    · have hgb : g ∈ hν.ball (n + 1) :=
        (Submodule.span_le.mpr (hν.level_subset n)) hg
      exact (hν.add_le _ _).trans (max_le hgb (hy₀n.trans (Nat.le_succ n)))

/-- **(c)** `span U ∩ F ^ p = 0`. -/
theorem eq_zero_of_mem_span_of_mem {f : F} (hf : f ∈ Submodule.span E hν.basisSet)
    (hW : f ∈ frobeniusSubmodule E p) : f = 0 := by
  obtain ⟨c, t, ht, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  have hli := hν.linearIndepOn_mkQ
  rw [linearIndepOn_iff'] at hli
  have h0 := hli t c ht (by
    have : ∑ i ∈ t, c i • (frobeniusSubmodule E p).mkQ i =
        (frobeniusSubmodule E p).mkQ (∑ i ∈ t, c i • i) := by simp [map_sum]
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hW)
  exact Finset.sum_eq_zero fun i hi => by rw [h0 i hi, zero_smul]

/-- No element of `U` is a `p`-th power. -/
theorem notMem_frobeniusSubmodule {u : F} (hu : u ∈ hν.basisSet) :
    u ∉ frobeniusSubmodule E p := fun h =>
  hν.linearIndepOn_mkQ.ne_zero hu ((Submodule.Quotient.mk_eq_zero _).mpr h)

end IsFrobeniusNorm


/-- Over a perfect field, the Frobenius preserves linear independence. -/
theorem linearIndependent_pow {ι : Type*} {v : ι → F} (hv : LinearIndependent E v) :
    LinearIndependent E (fun i => v i ^ p) := by
  have : CharP E p := (algebraMap E F).charP (algebraMap E F).injective p
  have : ExpChar E p := ExpChar.prime Fact.out
  have : PerfectRing E p := PerfectField.toPerfectRing p
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hsum i hi
  have h1 : (∑ j ∈ s, (frobeniusEquiv E p).symm (g j) • v j) ^ p = ∑ j ∈ s, g j • v j ^ p := by
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_pow, frobeniusEquiv_symm_pow_p]
  have h2 : ∑ j ∈ s, (frobeniusEquiv E p).symm (g j) • v j = 0 :=
    (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp (h1.trans hsum)
  have := hv s (fun j => (frobeniusEquiv E p).symm (g j)) h2 i hi
  simpa using this

section Family

omit [Fact p.Prime] [CharP F p] [PerfectField E]

/-- The truncation of `frobeniusFamily` to the exponents `p ^ j` with `j < N`. -/
def frobeniusFamilyFin (U : Set F) (N : ℕ) : Option (Fin N × U) → F
  | none => 1
  | some x => (x.2 : F) ^ p ^ (x.1 : ℕ)

/-- Splitting off the exponent `p ^ 0`. -/
def finSuccSplit (U : Set F) (N : ℕ) : Option (Fin (N + 1) × U) → U ⊕ Option (Fin N × U)
  | none => Sum.inr none
  | some (k, u) => Fin.cases (Sum.inl u) (fun j => Sum.inr (some (j, u))) k

/-- Inverse of `finSuccSplit`. -/
def finSuccJoin (U : Set F) (N : ℕ) : U ⊕ Option (Fin N × U) → Option (Fin (N + 1) × U)
  | Sum.inl u => some (0, u)
  | Sum.inr none => none
  | Sum.inr (some (j, u)) => some (j.succ, u)

/-- `Option (Fin (N + 1) × U) ≃ U ⊕ Option (Fin N × U)`. -/
def finSuccSplitEquiv (U : Set F) (N : ℕ) : Option (Fin (N + 1) × U) ≃ U ⊕ Option (Fin N × U) where
  toFun := finSuccSplit U N
  invFun := finSuccJoin U N
  left_inv := by
    rintro (_ | ⟨k, u⟩)
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) k <;> simp [finSuccSplit, finSuccJoin]
  right_inv := by
    rintro (u | _ | ⟨j, u⟩) <;> simp [finSuccSplit, finSuccJoin]

/-- The truncated family of length `N + 1` is `U` together with the Frobenius of the truncated
family of length `N`. -/
theorem frobeniusFamilyFin_succ (U : Set F) (N : ℕ) :
    frobeniusFamilyFin p U (N + 1) =
      Sum.elim (fun u : U => (u : F)) (fun i => frobeniusFamilyFin p U N i ^ p) ∘
        finSuccSplitEquiv U N := by
  funext x
  rcases x with _ | ⟨k, u⟩
  · simp [frobeniusFamilyFin, finSuccSplitEquiv, finSuccSplit]
  · refine Fin.cases ?_ (fun j => ?_) k
    · simp [frobeniusFamilyFin, finSuccSplitEquiv, finSuccSplit]
    · simp only [frobeniusFamilyFin, finSuccSplitEquiv, finSuccSplit, Equiv.coe_fn_mk,
        Function.comp_apply, Fin.cases_succ, Sum.elim_inr, Fin.val_succ]
      rw [pow_succ, pow_mul]

end Family

namespace IsFrobeniusNorm

variable {p} {ν : F → ℕ} (hν : IsFrobeniusNorm E p ν)
include hν

/-- `U` itself is linearly independent. -/
theorem linearIndependent_basisSet : LinearIndependent E (fun u : hν.basisSet => (u : F)) := by
  classical
  have hli := hν.linearIndepOn_mkQ
  rw [linearIndepOn_iff'] at hli
  rw [linearIndependent_iff']
  intro s g hsum i hi
  set G : F → E := fun x => if h : x ∈ hν.basisSet then g ⟨x, h⟩ else 0
  have hsub : ↑(s.map (Function.Embedding.subtype _)) ⊆ hν.basisSet := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hx
    exact u.2
  have hsum' : ∑ x ∈ s.map (Function.Embedding.subtype _), G x • (frobeniusSubmodule E p).mkQ x
      = 0 := by
    rw [Finset.sum_map]
    have : ∀ u ∈ s, G ((Function.Embedding.subtype _) u) • (frobeniusSubmodule E p).mkQ
        ((Function.Embedding.subtype _) u) = (frobeniusSubmodule E p).mkQ (g u • (u : F)) := by
      intro u _
      simp [G, u.2]
    rw [Finset.sum_congr rfl this, ← map_sum, hsum, map_zero]
  have := hli _ G hsub hsum' i (Finset.mem_map_of_mem _ hi)
  simpa [G, i.2] using this

/-- The truncated families are linearly independent. -/
theorem linearIndependent_frobeniusFamilyFin (N : ℕ) :
    LinearIndependent E (frobeniusFamilyFin p hν.basisSet N) := by
  induction N with
  | zero =>
    let hU : Unique (Option (Fin 0 × hν.basisSet)) :=
      { default := none
        uniq := fun i => by
          rcases i with _ | ⟨k, _⟩
          · rfl
          · exact k.elim0 }
    refine linearIndependent_unique_iff.mpr ?_
    show frobeniusFamilyFin p hν.basisSet 0 none ≠ 0
    simp [frobeniusFamilyFin]
  | succ N ih =>
    rw [frobeniusFamilyFin_succ, linearIndependent_equiv]
    refine LinearIndependent.sum_type ?_ (linearIndependent_pow p ih) ?_
    · exact hν.linearIndependent_basisSet
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      rw [Subtype.range_coe] at hx
      refine hν.eq_zero_of_mem_span_of_mem hx ?_
      refine (Submodule.span_le.mpr ?_) hx'
      rintro _ ⟨i, rfl⟩
      exact pow_mem_frobeniusSubmodule p _

/-- **(e)** The family `{1} ⊔ U ⊔ U ^ p ⊔ ⋯` is linearly independent. -/
theorem linearIndependent_frobeniusFamily :
    LinearIndependent E (frobeniusFamily p hν.basisSet) := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum i hi
  set lvl : Option (ℕ × hν.basisSet) → ℕ := fun i => i.elim 0 (fun x => x.1)
  set N := t.sup lvl + 1
  set incl : Option (Fin N × hν.basisSet) → Option (ℕ × hν.basisSet) :=
    Option.map (fun x => ((x.1 : ℕ), x.2))
  have hinj : Function.Injective incl := Option.map_injective (fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) h.2)
  have hcomp : frobeniusFamily p hν.basisSet ∘ incl = frobeniusFamilyFin p hν.basisSet N := by
    funext x; rcases x with _ | ⟨k, u⟩ <;> rfl
  have hli : LinearIndepOn E (frobeniusFamily p hν.basisSet) (Set.range incl) := by
    rw [linearIndepOn_range_iff hinj, hcomp]; exact hν.linearIndependent_frobeniusFamilyFin N
  rw [linearIndepOn_iff'] at hli
  refine hli t g (fun x hx => ?_) hsum i hi
  rcases x with _ | ⟨j, u⟩
  · exact ⟨none, rfl⟩
  · have : j < N := Nat.lt_succ_of_le (Finset.le_sup (f := lvl) hx)
    exact ⟨some (⟨j, this⟩, u), rfl⟩

/-- Frobenius powers map `span U` into the span of the family. -/
theorem pow_mem_span (i : ℕ) {x : F} (hx : x ∈ Submodule.span E hν.basisSet) :
    x ^ p ^ i ∈ Submodule.span E (Set.range (frobeniusFamily p hν.basisSet)) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨some (i, ⟨x, hx⟩), rfl⟩
  | zero =>
    rw [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_pow_char_pow]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_pow]; exact Submodule.smul_mem _ _ hx

/-- **(d)** The family `{1} ⊔ U ⊔ U ^ p ⊔ ⋯` spans `F`. -/
theorem span_frobeniusFamily :
    Submodule.span E (Set.range (frobeniusFamily p hν.basisSet)) = ⊤ := by
  set S := Submodule.span E (Set.range (frobeniusFamily p hν.basisSet))
  have step : ∀ i : ℕ, ∀ f : F, ∃ g ∈ S, ∃ h : F, f = g + h ^ p ^ i ∧ p ^ i * ν h ≤ ν f := by
    intro i
    induction i with
    | zero => intro f; exact ⟨0, S.zero_mem, f, by simp, by simp⟩
    | succ i ih =>
      intro f
      obtain ⟨g, hg, h, hf, hbound⟩ := ih f
      obtain ⟨h₀, hh₀, hW, hν₀⟩ := hν.exists_reduction (ν h) h le_rfl
      obtain ⟨k, hk⟩ := (mem_frobeniusSubmodule p).mp hW
      refine ⟨g + h₀ ^ p ^ i, S.add_mem hg (hν.pow_mem_span i hh₀), k, ?_, ?_⟩
      · have hh : h = h₀ + k ^ p := by rw [hk]; abel
        rw [hf, hh, add_pow_char_pow, ← pow_mul, ← pow_succ', add_assoc]
      · calc p ^ (i + 1) * ν k = p ^ i * ν (k ^ p) := by rw [hν.pow_char, pow_succ, mul_assoc]
          _ = p ^ i * ν (h - h₀) := by rw [hk]
          _ ≤ p ^ i * ν h := Nat.mul_le_mul_left _ ((hν.sub_le _ _).trans (max_le le_rfl hν₀))
          _ ≤ ν f := hbound
  refine eq_top_iff.mpr fun f _ => ?_
  obtain ⟨g, hg, h, hf, hbound⟩ := step (ν f) f
  have hlt : ν f < p ^ ν f := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  have hh : ν h = 0 := by
    by_contra hne
    have : p ^ ν f ≤ p ^ ν f * ν h := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    omega
  obtain ⟨c, rfl⟩ := (hν.eq_zero_iff h).mp hh
  rw [hf, ← map_pow, Algebra.algebraMap_eq_smul_one]
  exact S.add_mem hg (S.smul_mem _ (Submodule.subset_span ⟨none, rfl⟩))

/-- **Frobenius-graded bases from an integer-valued norm** (abstract form of Temkin's proof of
Lemma 6.2.6): there is `U ⊆ F ∖ F ^ p` such that `{1} ⊔ U ⊔ U ^ p ⊔ U ^ (p ^ 2) ⊔ ⋯` is an
`E`-basis of `F` and `span_E U ∩ F ^ p = 0`. -/
theorem exists_frobeniusBasis :
    ∃ U : Set F, (∀ u ∈ U, ∀ g : F, g ^ p ≠ u) ∧
      LinearIndependent E (frobeniusFamily p U) ∧
      Submodule.span E (Set.range (frobeniusFamily p U)) = ⊤ ∧
      ∀ f ∈ Submodule.span E U, ∀ g : F, g ^ p = f → f = 0 :=
  ⟨hν.basisSet, fun _ hu g hg => hν.notMem_frobeniusSubmodule hu ⟨g, hg⟩,
    hν.linearIndependent_frobeniusFamily, hν.span_frobeniusFamily,
    fun _ hf g hg => hν.eq_zero_of_mem_span_of_mem hf ⟨g, hg⟩⟩

end IsFrobeniusNorm

end Abstract

section FunctionField

variable (p : ℕ)

/-- The pole-order norm of a function field of one variable in which `E` is algebraically closed
satisfies the hypotheses of the abstract Frobenius-basis lemma. -/
theorem isFrobeniusNorm_poleNorm (hF : IsFunctionFieldOneVar E F)
    (halg : ∀ x : F, IsAlgebraic E x → x ∈ (algebraMap E F).range) :
    IsFrobeniusNorm E p (poleNorm E (F := F)) where
  add_le := poleNorm_add_le hF
  smul_le := poleNorm_smul_le hF
  pow_char f := poleNorm_pow hF f p
  eq_zero_iff _ := poleNorm_eq_zero_iff_mem_range hF halg

variable [Fact p.Prime] [CharP F p] [PerfectField E]

/-- **Temkin, Lemma 6.2.6** (for function fields of one variable). Let `E` be a perfect field of
characteristic `p` and `F/E` a function field of one variable in which `E` is algebraically
closed. Then there is `U ⊆ F ∖ F ^ p` such that `{1} ⊔ U ⊔ U ^ p ⊔ U ^ (p ^ 2) ⊔ ⋯` is a basis of
`F` over `E` and `span_E U ∩ F ^ p = 0`. -/
theorem exists_frobeniusBasis (hF : IsFunctionFieldOneVar E F)
    (halg : ∀ x : F, IsAlgebraic E x → x ∈ (algebraMap E F).range) :
    ∃ U : Set F, (∀ u ∈ U, ∀ g : F, g ^ p ≠ u) ∧
      LinearIndependent E (frobeniusFamily p U) ∧
      Submodule.span E (Set.range (frobeniusFamily p U)) = ⊤ ∧
      ∀ f ∈ Submodule.span E U, ∀ g : F, g ^ p = f → f = 0 :=
  (isFrobeniusNorm_poleNorm p hF halg).exists_frobeniusBasis

/-- `exists_frobeniusBasis` packaged as a `Module.Basis` indexed by `Option (ℕ × U)`. -/
theorem exists_basis_frobeniusFamily (hF : IsFunctionFieldOneVar E F)
    (halg : ∀ x : F, IsAlgebraic E x → x ∈ (algebraMap E F).range) :
    ∃ (U : Set F) (b : Module.Basis (Option (ℕ × U)) E F), ⇑b = frobeniusFamily p U ∧
      (∀ u ∈ U, ∀ g : F, g ^ p ≠ u) ∧ ∀ f ∈ Submodule.span E U, ∀ g : F, g ^ p = f → f = 0 := by
  obtain ⟨U, hU, hli, hspan, hdisj⟩ := exists_frobeniusBasis p hF halg
  exact ⟨U, Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk _ _, hU, hdisj⟩

/-- `exists_frobeniusBasis` over an algebraically closed field (the case used in Temkin's
Proposition 6.2.5, where `E = k̃`). -/
theorem exists_frobeniusBasis_of_isAlgClosed [IsAlgClosed E] (hF : IsFunctionFieldOneVar E F) :
    ∃ U : Set F, (∀ u ∈ U, ∀ g : F, g ^ p ≠ u) ∧
      LinearIndependent E (frobeniusFamily p U) ∧
      Submodule.span E (Set.range (frobeniusFamily p U)) = ⊤ ∧
      ∀ f ∈ Submodule.span E U, ∀ g : F, g ^ p = f → f = 0 :=
  exists_frobeniusBasis p hF fun _ hx => mem_range_of_isAlgebraic hx

end FunctionField

end DeJongAlterations.StableModification.Valuation.FunctionField

end

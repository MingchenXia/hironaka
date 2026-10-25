import DeJongAlterations.StableModification.Resolution.GlobalNodeModel

/-!
# Ideals of the formal models

Computations with the coordinate ideals of the formal node model
`NodeModel k n = k[[U, V, Z_1, …, Z_m]] / (U V - ∏ Z_i ^ n_i)` (blueprint
`lem:sm-dj-centre-traces`; de Jong 1996, 3.4 and 4.27):

* `truncate S`: the ring endomorphism of `k[[X]]` setting the variables of `S` to zero; its
  kernel is `(X_i : i ∈ S)` (`ker_truncate`), so `(X_i : i ∈ S)` is prime over a domain
  (`isPrime_span_X`), and `f ∈ (X_S, X^a)` iff `X^a ∣ T_S f` (`mem_span_insert_monomial_iff`);
* `monomial_one_dvd_iff`: divisibility by a monomial is a condition on the support;
* the ideals `nIdeal a = (U, V, Z^a)` (`a ≤ n`) of the node model: membership
  (`mk_mem_nIdeal_iff`), colon by monomials (`nIdeal_colon_nodeZMon`, `nIdeal_iterate_colon`) and
  by each other (`nIdeal_colon_nIdeal`), `nIdeal n = (U, V)` (`nIdeal_self`), primality of
  `(U, V, Z_α)` for `n_α ≥ 1` (`isPrime_nIdeal_single`) and of the crossing ideal
  `(U, V, Z_a, Z_b)` (`isPrime_crossIdeal`), and the maximal ideal (`maximalIdeal_nodeModel`).

In a node chart the singular-locus ideal has trace `(U, V) = nIdeal n` and a boundary ideal has
trace `(Z^E)`; the centres `(𝒩 : ℰ^{N-1}) : (𝒩 : ℰ^N)` then have trace
`nIdeal ((n - (N - 1) E) - (n - N E))`, which is `(U, V, Z_α)` exactly where `n_α ≥ N` for
`E = e_α`.
-/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.StableModification.Resolution.Global

set_option backward.isDefEq.respectTransparency false

section Monomial

variable {σ R : Type*} [CommRing R]

/-- Divisibility by a monomial: `X^a ∣ f` iff `f` has no monomial outside `a + ℕ^σ`. -/
theorem monomial_one_dvd_iff (a : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    monomial a (1 : R) ∣ f ↔ ∀ d, ¬ a ≤ d → coeff d f = 0 := by
  classical
  constructor
  · rintro ⟨g, rfl⟩ d hd
    rw [coeff_monomial_mul, if_neg hd]
  · intro h
    refine ⟨fun d ↦ coeff (d + a) f, ?_⟩
    ext d
    rw [coeff_monomial_mul]
    split_ifs with had
    · rw [one_mul]
      change coeff d f = coeff (d - a + a) f
      rw [tsub_add_cancel_of_le had]
    · exact h d had

/-- `X^a ∣ X^b g` iff `X^{a - b} ∣ g`. -/
theorem monomial_one_dvd_monomial_mul_iff (a b : σ →₀ ℕ) (g : MvPowerSeries σ R) :
    monomial a (1 : R) ∣ monomial b 1 * g ↔ monomial (a - b) (1 : R) ∣ g := by
  classical
  rw [monomial_one_dvd_iff, monomial_one_dvd_iff]
  constructor
  · intro h d hd
    have h1 := h (d + b) (fun hle ↦ hd (tsub_le_iff_right.mpr hle))
    rwa [coeff_monomial_mul, if_pos le_add_self, one_mul, add_tsub_cancel_right] at h1
  · intro h d hd
    rw [coeff_monomial_mul]
    split_ifs with hbd
    · rw [one_mul]
      refine h _ fun hle ↦ hd ?_
      have := tsub_le_iff_right.mp hle
      rwa [tsub_add_cancel_of_le hbd] at this
    · rfl

/-- A finite product of powers of variables is a monomial. -/
theorem prod_X_pow_eq_monomial {ι : Type*} (s : Finset ι) (v : ι → σ) (a : ι → ℕ) :
    ∏ i ∈ s, (X (v i) : MvPowerSeries σ R) ^ a i =
      monomial (∑ i ∈ s, Finsupp.single (v i) (a i)) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero_eq_C_apply]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, X_pow_eq, monomial_mul_monomial,
      one_mul]

end Monomial

section Truncation

variable {σ R : Type*} [CommRing R]

/-- The underlying function of the truncation `T_S`. -/
def truncateFun (S : Finset σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ if ∀ i ∈ S, d i = 0 then coeff d f else 0

theorem coeff_truncateFun (S : Finset σ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (truncateFun S f) = if ∀ i ∈ S, d i = 0 then coeff d f else 0 := rfl

/-- The **truncation** `T_S` of a power series: the monomials involving a variable of `S` are
removed, i.e. the variables of `S` are set to zero. It is a ring endomorphism. -/
def truncate (S : Finset σ) : MvPowerSeries σ R →+* MvPowerSeries σ R where
  toFun := truncateFun S
  map_one' := by
    classical
    ext d
    rw [coeff_truncateFun, coeff_one]
    by_cases hd : d = 0
    · subst hd
      simp
    · simp [hd]
  map_mul' f g := by
    classical
    ext d
    rw [coeff_truncateFun, coeff_mul, coeff_mul]
    split_ifs with hd
    · refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      have hpi : ∀ i ∈ S, p.1 i = 0 ∧ p.2 i = 0 := fun i hi ↦ by
        have := congrArg (· i) hp
        simp only [Finsupp.add_apply] at this
        have := hd i hi
        omega
      rw [coeff_truncateFun, coeff_truncateFun, if_pos fun i hi ↦ (hpi i hi).1,
        if_pos fun i hi ↦ (hpi i hi).2]
    · push Not at hd
      obtain ⟨i, hi, hdi⟩ := hd
      symm
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      have := congrArg (· i) hp
      simp only [Finsupp.add_apply] at this
      rw [coeff_truncateFun, coeff_truncateFun]
      by_cases h1 : p.1 i = 0
      · have h2 : p.2 i ≠ 0 := by omega
        simp only [show ¬ (∀ j ∈ S, p.2 j = 0) from fun h ↦ h2 (h i hi), if_false, mul_zero]
      · simp only [show ¬ (∀ j ∈ S, p.1 j = 0) from fun h ↦ h1 (h i hi), if_false, zero_mul]
  map_zero' := by
    ext d
    rw [coeff_truncateFun]
    simp
  map_add' f g := by
    ext d
    rw [map_add, coeff_truncateFun, coeff_truncateFun, coeff_truncateFun]
    split_ifs <;> simp

theorem coeff_truncate (S : Finset σ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (truncate S f) = if ∀ i ∈ S, d i = 0 then coeff d f else 0 := rfl

theorem truncate_monomial (S : Finset σ) (a : σ →₀ ℕ) (c : R) (ha : ∀ i ∈ S, a i = 0) :
    truncate S (monomial a c) = monomial a c := by
  classical
  ext d
  rw [coeff_truncate, coeff_monomial]
  by_cases h : d = a
  · subst h
    rw [if_pos ha]
  · simp [h]

theorem truncate_X_of_mem (S : Finset σ) {i : σ} (hi : i ∈ S) :
    truncate S (X i : MvPowerSeries σ R) = 0 := by
  classical
  ext d
  rw [coeff_truncate, coeff_X, map_zero]
  split_ifs with h1 h2 <;> try rfl
  have := h1 i hi
  rw [h2, Finsupp.single_eq_same] at this
  exact absurd this one_ne_zero

theorem truncate_truncate (S : Finset σ) (f : MvPowerSeries σ R) :
    truncate S (truncate S f) = truncate S f := by
  ext d
  rw [coeff_truncate, coeff_truncate]
  split_ifs <;> rfl

/-- Truncating by `insert i S` is truncating by `S` and then by `{i}`. -/
theorem truncate_insert [DecidableEq σ] (i : σ) (S : Finset σ) (f : MvPowerSeries σ R) :
    truncate (insert i S) f = truncate {i} (truncate S f) := by
  ext d
  rw [coeff_truncate, coeff_truncate, coeff_truncate]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  split_ifs <;> tauto

theorem truncate_empty (f : MvPowerSeries σ R) : truncate ∅ f = f := by
  ext d
  rw [coeff_truncate]
  simp

/-- `f - T_S f` lies in the ideal generated by the variables of `S`. -/
theorem sub_truncate_mem (S : Finset σ) (f : MvPowerSeries σ R) :
    f - truncate S f ∈ Ideal.span ((X : σ → MvPowerSeries σ R) '' (S : Set σ)) := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => rw [truncate_empty, sub_self]; exact Ideal.zero_mem _
  | insert i S hi ih =>
    rw [truncate_insert]
    have h1 : f - truncate S f ∈
        Ideal.span ((X : σ → MvPowerSeries σ R) '' ((insert i S : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp)) (ih f)
    have h2 : truncate S f - truncate {i} (truncate S f) ∈
        Ideal.span ((X : σ → MvPowerSeries σ R) '' ((insert i S : Finset σ) : Set σ)) := by
      have hdvd : (X i : MvPowerSeries σ R) ∣ truncate S f - truncate {i} (truncate S f) := by
        rw [X_dvd_iff]
        intro m hm
        rw [map_sub, coeff_truncate {i} (truncate S f)]
        simp [hm]
      obtain ⟨g, hg⟩ := hdvd
      rw [hg]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, by simp, rfl⟩)
    have := Ideal.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at this

/-- The kernel of the truncation `T_S` is the ideal generated by the variables of `S`. -/
theorem truncate_eq_zero_iff (S : Finset σ) (f : MvPowerSeries σ R) :
    truncate S f = 0 ↔ f ∈ Ideal.span ((X : σ → MvPowerSeries σ R) '' (S : Set σ)) := by
  constructor
  · intro h
    have := sub_truncate_mem S f
    rwa [h, sub_zero] at this
  · intro h
    have : Ideal.span ((X : σ → MvPowerSeries σ R) '' (S : Set σ)) ≤ RingHom.ker (truncate S) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact truncate_X_of_mem S hi
    exact this h

theorem ker_truncate (S : Finset σ) :
    RingHom.ker (truncate (R := R) S) =
      Ideal.span ((X : σ → MvPowerSeries σ R) '' (S : Set σ)) := by
  ext f
  exact truncate_eq_zero_iff S f

/-- Over a domain, the ideal generated by a finite set of variables is prime. -/
theorem isPrime_span_X [IsDomain R] (S : Finset σ) :
    (Ideal.span ((X : σ → MvPowerSeries σ R) '' (S : Set σ))).IsPrime := by
  have : IsDomain (MvPowerSeries σ R) := NoZeroDivisors.to_isDomain _
  rw [← ker_truncate]
  exact RingHom.ker_isPrime _

/-- **Membership in `(X_i : i ∈ S) + (X^a)`** for a monomial `X^a` not involving `S`:
`f ∈ (X_S, X^a)` iff `X^a ∣ T_S f`. -/
theorem mem_span_insert_monomial_iff (S : Finset σ) (a : σ →₀ ℕ) (ha : ∀ i ∈ S, a i = 0)
    (f : MvPowerSeries σ R) :
    f ∈ Ideal.span (insert (monomial a 1) ((X : σ → MvPowerSeries σ R) '' (S : Set σ))) ↔
      monomial a (1 : R) ∣ truncate S f := by
  constructor
  · intro hf
    have hle : (Ideal.span (insert (monomial a 1)
        ((X : σ → MvPowerSeries σ R) '' (S : Set σ)))).map (truncate S) ≤
        Ideal.span {monomial a (1 : R)} := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨q, hq, rfl⟩
      rcases hq with rfl | ⟨i, hi, rfl⟩
      · rw [truncate_monomial S a 1 ha]
        exact Ideal.mem_span_singleton_self _
      · rw [truncate_X_of_mem S hi]
        exact Ideal.zero_mem _
    exact Ideal.mem_span_singleton.mp (hle (Ideal.mem_map_of_mem _ hf))
  · rintro ⟨g, hg⟩
    have h1 := sub_truncate_mem S f
    have : f = (f - truncate S f) + monomial a 1 * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.span_mono (Set.subset_insert _ _) h1) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

end Truncation

section NodeIdeals

variable (k : Type*) [Field k] {m : ℕ}

/-- The exponent vector of `∏ Z_i ^ a_i` in the variables `Fin (m + 2)` (`Z_i = X (i + 2)`). -/
def zExp (a : Fin m → ℕ) : Fin (m + 2) →₀ ℕ := ∑ i, Finsupp.single i.succ.succ (a i)

omit k in
theorem zExp_apply (a : Fin m → ℕ) (j : Fin (m + 2)) :
    zExp a j = Fin.cases 0 (Fin.cases 0 a) j := by
  classical
  rw [zExp, Finsupp.finsetSum_apply]
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun l ↦ ?_) j) j
  · simp [Fin.succ_ne_zero]
  · simp only [Finsupp.single_apply, Fin.cases_succ, Fin.cases_zero]
    refine Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ Fin.succ_ne_zero i (Fin.succ_injective _ h)
  · simp only [Finsupp.single_apply, Fin.cases_succ, Fin.succ_inj, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]

omit k in
theorem zExp_apply_zero (a : Fin m → ℕ) : zExp a 0 = 0 := by rw [zExp_apply]; rfl

omit k in
theorem zExp_apply_one (a : Fin m → ℕ) : zExp a 1 = 0 := by
  rw [zExp_apply]; rfl

omit k in
theorem zExp_apply_succ_succ (a : Fin m → ℕ) (i : Fin m) : zExp a i.succ.succ = a i := by
  rw [zExp_apply]; rfl

omit k in
theorem zExp_sub (a b : Fin m → ℕ) : zExp (a - b) = zExp a - zExp b := by
  ext j
  rw [Finsupp.tsub_apply, zExp_apply, zExp_apply, zExp_apply]
  refine Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ ?_) j) j
  simp

omit k in
theorem zExp_le_zExp {a b : Fin m → ℕ} (h : a ≤ b) : zExp a ≤ zExp b := by
  intro j
  rw [zExp_apply, zExp_apply]
  refine Fin.cases le_rfl (fun j ↦ Fin.cases le_rfl (fun l ↦ ?_) j) j
  simpa using h l

/-- The monomial `∏ Z_i ^ a_i` in `k[[U, V, Z]]`. -/
abbrev zMon (a : Fin m → ℕ) : MvPowerSeries (Fin (m + 2)) k := ∏ i, X i.succ.succ ^ a i

theorem zMon_eq_monomial (a : Fin m → ℕ) : zMon k a = monomial (zExp a) 1 :=
  prod_X_pow_eq_monomial _ _ _

/-- The variables `U = X 0`, `V = X 1`. -/
abbrev uvSet : Finset (Fin (m + 2)) := {0, 1}

omit k in
theorem zExp_uv (a : Fin m → ℕ) : ∀ i ∈ (uvSet : Finset (Fin (m + 2))), zExp a i = 0 := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact zExp_apply_zero a
  · exact zExp_apply_one a

variable (n : Fin m → ℕ)

/-- The node coordinate `U` of the node model. -/
abbrev nodeU : NodeModel k n := Ideal.Quotient.mk _ (X 0)
/-- The node coordinate `V` of the node model. -/
abbrev nodeV : NodeModel k n := Ideal.Quotient.mk _ (X 1)
/-- The coordinates `Z_i` of the node model. -/
abbrev nodeZ (i : Fin m) : NodeModel k n := Ideal.Quotient.mk _ (X i.succ.succ)
/-- The monomial `∏ Z_i ^ a_i` of the node model. -/
abbrev nodeZMon (a : Fin m → ℕ) : NodeModel k n := Ideal.Quotient.mk _ (zMon k a)

theorem nodeZMon_eq_prod (a : Fin m → ℕ) : nodeZMon k n a = ∏ i, nodeZ k n i ^ a i := by
  simp only [nodeZMon, zMon, map_prod, map_pow]

/-- The node relation `U V = ∏ Z_i ^ n_i`. -/
theorem nodeU_mul_nodeV : nodeU k n * nodeV k n = nodeZMon k n n := by
  rw [← map_mul, Ideal.Quotient.eq, ← nodeSeries_eq]
  exact Ideal.mem_span_singleton_self _

/-- The ideals `(U, V, ∏ Z_i ^ a_i)` of the node model. -/
def nIdeal (a : Fin m → ℕ) : Ideal (NodeModel k n) :=
  Ideal.span {nodeU k n, nodeV k n, nodeZMon k n a}

theorem nodeSeries_mem_span (a : Fin m → ℕ) (ha : a ≤ n) :
    nodeSeries k n ∈ Ideal.span (insert (monomial (zExp a) (1 : k))
      ((X : Fin (m + 2) → MvPowerSeries (Fin (m + 2)) k) '' (uvSet : Finset (Fin (m + 2))))) := by
  rw [nodeSeries_eq]
  refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)) ?_
  · exact Set.mem_insert_of_mem _ ⟨0, by simp, rfl⟩
  · have hexp : zExp n = zExp a + zExp (n - a) := by
      ext j
      rw [Finsupp.add_apply, zExp_apply, zExp_apply, zExp_apply]
      refine Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ ?_) j) j
      simp only [Fin.cases_succ, Pi.sub_apply]
      have : a l ≤ n l := ha l
      omega
    have : (∏ i, (X i.succ.succ : MvPowerSeries (Fin (m + 2)) k) ^ n i) =
        monomial (zExp a) 1 * zMon k (n - a) := by
      rw [zMon_eq_monomial, monomial_mul_monomial, one_mul, ← hexp]
      exact zMon_eq_monomial k n
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

theorem comap_nIdeal (a : Fin m → ℕ) (ha : a ≤ n) :
    (nIdeal k n a).comap (Ideal.Quotient.mk _) = Ideal.span (insert (monomial (zExp a) (1 : k))
      ((X : Fin (m + 2) → MvPowerSeries (Fin (m + 2)) k) '' (uvSet : Finset (Fin (m + 2))))) := by
  have hmap : nIdeal k n a = (Ideal.span (insert (monomial (zExp a) (1 : k))
      ((X : Fin (m + 2) → MvPowerSeries (Fin (m + 2)) k) '' (uvSet : Finset (Fin (m + 2)))))).map
      (Ideal.Quotient.mk (Ideal.span {nodeSeries k n})) := by
    rw [Ideal.map_span, nIdeal, Set.image_insert_eq, Finset.coe_insert, Finset.coe_singleton,
      Set.image_insert_eq, Set.image_singleton, Set.image_insert_eq, Set.image_singleton,
      ← zMon_eq_monomial]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hmap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
  exact nodeSeries_mem_span k n a ha

/-- **Membership in `(U, V, Z^a)`** (`a ≤ n`): `[f] ∈ (U, V, Z^a)` iff `Z^a` divides the
truncation of `f` at `U = V = 0`. -/
theorem mk_mem_nIdeal_iff (a : Fin m → ℕ) (ha : a ≤ n) (f : MvPowerSeries (Fin (m + 2)) k) :
    Ideal.Quotient.mk _ f ∈ nIdeal k n a ↔ monomial (zExp a) (1 : k) ∣ truncate uvSet f := by
  rw [← Ideal.mem_comap, comap_nIdeal k n a ha]
  exact mem_span_insert_monomial_iff _ _ (zExp_uv a) f

/-- **Colon by a monomial**: `(U, V, Z^a) : Z^b = (U, V, Z^{a - b})` for `a ≤ n`. -/
theorem nIdeal_colon_nodeZMon (a b : Fin m → ℕ) (ha : a ≤ n) :
    (nIdeal k n a).colon {nodeZMon k n b} = nIdeal k n (a - b) := by
  ext x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Submodule.mem_colon_singleton, smul_eq_mul, nodeZMon, ← map_mul,
    mk_mem_nIdeal_iff k n a ha, mk_mem_nIdeal_iff k n (a - b)
      (fun i ↦ (Nat.sub_le _ _).trans (ha i)), map_mul, zMon_eq_monomial,
    truncate_monomial _ _ _ (zExp_uv b), mul_comm, monomial_one_dvd_monomial_mul_iff,
    zExp_sub]

/-- Iterated colon by a monomial. -/
theorem nIdeal_iterate_colon (a b : Fin m → ℕ) (ha : a ≤ n) (j : ℕ) :
    (fun I : Ideal (NodeModel k n) ↦ I.colon {nodeZMon k n b})^[j] (nIdeal k n a) =
      nIdeal k n (a - j • b) := by
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply, show a - 0 • b = a from funext fun i ↦ by simp]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, nIdeal_colon_nodeZMon k n (a - j • b) b
      (fun i ↦ (Nat.sub_le _ _).trans (ha i))]
    congr 1
    funext i
    simp only [Pi.sub_apply, succ_nsmul, Pi.add_apply]
    omega

/-- `(U, V, Z^n) = (U, V)`. -/
theorem nIdeal_self : nIdeal k n n = Ideal.span {nodeU k n, nodeV k n} := by
  apply le_antisymm
  · rw [nIdeal, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · rw [← nodeU_mul_nodeV]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.span_mono (by intro x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)

/-- `(U, V, Z^0)` is the unit ideal. -/
theorem nIdeal_zero : nIdeal k n 0 = ⊤ := by
  rw [eq_top_iff, ← Ideal.span_singleton_one]
  refine Ideal.span_mono ?_
  simp [nodeZMon, zMon]

/-- **Colon of two coordinate ideals**: `(U, V, Z^a) : (U, V, Z^b) = (U, V, Z^{a - b})` for
`a ≤ n`. -/
theorem nIdeal_colon_nIdeal (a b : Fin m → ℕ) (ha : a ≤ n) :
    (nIdeal k n a).colon (nIdeal k n b : Set (NodeModel k n)) = nIdeal k n (a - b) := by
  rw [show (nIdeal k n b : Set (NodeModel k n)) =
      ((Ideal.span {nodeU k n, nodeV k n, nodeZMon k n b} : Ideal (NodeModel k n)) :
        Set (NodeModel k n)) from rfl, Ideal.colon_span, ← nIdeal_colon_nodeZMon k n a b ha]
  have hU : nodeU k n ∈ nIdeal k n a := Ideal.subset_span (by simp)
  have hV : nodeV k n ∈ nIdeal k n a := Ideal.subset_span (by simp)
  ext x
  simp only [Submodule.mem_colon, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, smul_eq_mul]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨Ideal.mul_mem_left _ _ hU, Ideal.mul_mem_left _ _ hV, h⟩⟩

/-- An ideal of the node model whose preimage in `k[[U, V, Z]]` is prime is prime. -/
theorem isPrime_of_comap (I : Ideal (NodeModel k n))
    (hI : (I.comap (Ideal.Quotient.mk (Ideal.span {nodeSeries k n}))).IsPrime) : I.IsPrime := by
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I]
  refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
  rw [Ideal.mk_ker]
  intro f hf
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
  exact Ideal.zero_mem _

/-- **The coordinate ideal `(U, V, Z_α)` is prime** when `n_α ≥ 1`. -/
theorem isPrime_nIdeal_single [DecidableEq (Fin m)] (α : Fin m) (hα : 1 ≤ n α) :
    (nIdeal k n (Pi.single α 1)).IsPrime := by
  have hle : (Pi.single α 1 : Fin m → ℕ) ≤ n := by
    intro i
    by_cases h : i = α
    · subst h; simpa using hα
    · simp [h]
  apply isPrime_of_comap
  rw [comap_nIdeal k n _ hle]
  have : (monomial (zExp (Pi.single α 1)) (1 : k)) = X α.succ.succ := by
    rw [← zMon_eq_monomial]
    change ∏ i, (X i.succ.succ : MvPowerSeries (Fin (m + 2)) k) ^ (Pi.single α 1 : Fin m → ℕ) i = _
    rw [Finset.prod_eq_single α (fun i _ hi ↦ by simp [hi])
      (fun h ↦ absurd (Finset.mem_univ α) h)]
    simp
  rw [this, ← Set.image_insert_eq, ← Finset.coe_insert]
  exact isPrime_span_X _

/-- The crossing ideal `(U, V, Z_a, Z_b)` of the node model. -/
def crossIdeal (a b : Fin m) : Ideal (NodeModel k n) :=
  Ideal.span {nodeU k n, nodeV k n, nodeZ k n a, nodeZ k n b}

/-- **The crossing ideal `(U, V, Z_a, Z_b)` is prime** when `n_a ≥ 1`. -/
theorem isPrime_crossIdeal (a b : Fin m) (ha : 1 ≤ n a) : (crossIdeal k n a b).IsPrime := by
  classical
  let S : Finset (Fin (m + 2)) := {0, 1, a.succ.succ, b.succ.succ}
  have hmap : crossIdeal k n a b = (Ideal.span ((X : Fin (m + 2) → MvPowerSeries (Fin (m + 2)) k) ''
      (S : Set (Fin (m + 2))))).map (Ideal.Quotient.mk (Ideal.span {nodeSeries k n})) := by
    rw [Ideal.map_span, crossIdeal]
    congr 1
    ext x
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  apply isPrime_of_comap
  rw [hmap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr]
  · exact isPrime_span_X S
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, nodeSeries_eq]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, by simp [S], rfl⟩)) ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨e, he⟩ : ∃ e, n a = e + 1 := ⟨n a - 1, by omega⟩
    rw [he, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a.succ.succ, by simp [S], rfl⟩)

/-- The maximal ideal of the node model is generated by `U`, `V` and the `Z_i`. -/
theorem maximalIdeal_nodeModel [IsLocalRing (NodeModel k n)] :
    maximalIdeal (NodeModel k n) =
      Ideal.span (insert (nodeU k n) (insert (nodeV k n) (Set.range (nodeZ k n)))) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
    maximalIdeal_mvPowerSeries_eq, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Function.comp_apply]
  constructor
  · rintro ⟨j, rfl⟩
    cases j using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => exact Or.inr (Or.inl rfl)
      | succ l => exact Or.inr (Or.inr ⟨l, rfl⟩)
  · rintro (rfl | rfl | ⟨l, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨l.succ.succ, rfl⟩

end NodeIdeals

end DeJongAlterations.StableModification.Resolution.Global

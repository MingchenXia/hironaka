import DeJongAlterations.StableModification.Resolution.GlobalNodeChart
import DeJongAlterations.StableModification.Resolution.GlobalModelIdeals
import DeJongAlterations.StableModification.Resolution.GlobalFlat
import DeJongAlterations.Algebra.CompletionRegularityAscent

/-!
# Formal charts and the blowup steps of the resolution of a nodal curve

The local algebra of one blowup step of the resolution of a nodal curve over a regular base with
strict normal crossings boundary (de Jong 1996, 3.4 and 4.27,
`references/dejong96-alterations/tex/page-0014.tex`, `page-0015.tex`, `page-0027.tex`;
blueprint `def:sm-dj-formal-charts`, `lem:sm-dj-node-chart-branch`,
`lem:sm-dj-node-chart-crossing`, `lem:sm-dj-centre-traces`).

For a Noetherian local ring `O` with completion `Ô`, a singular-locus ideal `N` and boundary
ideals `E β`:

* `NodeChart k O m N E`: `Ô ≅ k[[U, V, Z_1, …, Z_m]]/(UV - ∏ Z_i^{n_i})` with `N Ô = (U, V)`,
  `E β Ô = (Z^{exp β})`, and the boundary coordinates coming from `O` up to units;
* `RegChart O m E`: generators `T_0, …, T_m` of `𝔪_Ô` with `E β Ô = (T^{exp β})`, and the product
  of the boundary coordinates coming from `O` up to a unit.

For a local homomorphism `φ : O → P` which is a localization of a blowup chart for an ideal `I`
(`IsChartLocalization`, `I P = (φ g)`), with `P` a domain of dimension `≥ m + 1` and residue
field `k`, the transformed ideals are `N' = (N P : I P)` (the singular-locus ideal of the blowup)
and `E' = E P`:

* `branch_step`: if `I Ô = (U, V, Z_a)` with `n_a ≥ 2`, then `P` has a node chart of type
  `n - 2 e_a` with the same boundary exponents (the `Z_a`-chart through the strict transform of the
  node), or a regular chart with `N' P̂ = P̂`;
* `crossing_step`: if `I Ô = (U, V, Z_a, Z_b)` with `n_a = n_b = 1`, then `P` has a regular chart
  with `N' P̂ = P̂`, or a node chart from the `Z_{a'}`-chart (`{a', b'} = {a, b}`) with
  `n_{a'} = 0`, `n_{b'} ≤ 1` and boundary exponents transformed by `Z_{b'} = Z_{a'} Z'_{b'}`;
* `NodeChart.transport`, `RegChart.transport`: charts transport along isomorphisms (away from the
  centre);
* `NodeChart.regChart_of_single`: a node chart with `n = e_i` is regular (`UV = Z_i`);
* `NodeChart.trace_iterColon`, `NodeChart.trace_centre`: the centres
  `(N : E_α^{N₀ - 1}) : (N : E_α^{N₀})` have trace `(U, V, Z^{(n - (N₀ - 1) e) - (n - N₀ e)})`,
  `e = exp α` (via the flat base change of colon ideals, `map_colon_of_flat`).

The chart computations are those of `GlobalNodeChart`; the charts are recognized with
`exists_nodeModel_algEquiv` (`GlobalNodeModel`).
-/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.StableModification.Resolution.Global

open Algebra.CompletionLocalMap Algebra.CompletionRegularityBasics Strictify

set_option backward.isDefEq.respectTransparency false

section Helpers

variable {R : Type*} [CommRing R]

/-- Principal ideals of products of powers transform by an exponent matrix: if
`(x_i) = (∏_j T_j ^ M_{j i})` for all `i`, then `(∏_i x_i ^ w_i) = (∏_j T_j ^ (M w)_j)`. -/
theorem span_prod_pow_eq {κ ι' : Type*} [Fintype κ] [Fintype ι'] (x : ι' → R) (T : κ → R)
    (M : κ → ι' → ℕ) (hx : ∀ i, Ideal.span {x i} = Ideal.span {∏ j, T j ^ M j i})
    (w : ι' → ℕ) :
    Ideal.span {∏ i, x i ^ w i} = Ideal.span {∏ j, T j ^ ∑ i, M j i * w i} := by
  have h1 : Ideal.span {∏ i, x i ^ w i} = ∏ i, Ideal.span {x i} ^ w i := by
    rw [← Ideal.prod_span_singleton]
    exact Finset.prod_congr rfl fun i _ ↦ (Ideal.span_singleton_pow _ _).symm
  rw [h1]
  simp_rw [hx]
  have h2 : ∏ i, Ideal.span {∏ j, T j ^ M j i} ^ w i =
      Ideal.span {∏ i, (∏ j, T j ^ M j i) ^ w i} := by
    rw [← Ideal.prod_span_singleton]
    exact Finset.prod_congr rfl fun i _ ↦ Ideal.span_singleton_pow _ _
  rw [h2]
  congr 2
  simp_rw [← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun j _ ↦ (Finset.prod_pow_eq_pow_sum _ _ _)

/-- Cancelling a non-zero-divisor in principal ideals. -/
theorem span_singleton_eq_of_mul {a x y : R} (ha : IsSMulRegular R a)
    (h : Ideal.span {a * x} = Ideal.span {a * y}) : Ideal.span {x} = Ideal.span {y} := by
  have hxy : ∀ x y : R, Ideal.span {a * x} = Ideal.span {a * y} → x ∈ Ideal.span {y} := by
    intro x y h
    have : a * x ∈ Ideal.span {a * y} := h ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    rw [Ideal.mem_span_singleton']
    refine ⟨c, ha ?_⟩
    simp only [smul_eq_mul]
    linear_combination hc
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem]; exact hxy x y h
  · rw [Ideal.span_singleton_le_iff_mem]; exact hxy y x h.symm

/-- Colon of a pair of multiples of a non-zero-divisor: `(g a, g b) : (g) = (a, b)`. -/
theorem span_pair_mul_colon {g a b : R} (hg : IsSMulRegular R g) :
    (Ideal.span {g * a, g * b}).colon ((Ideal.span {g} : Ideal R) : Set R) =
      Ideal.span {a, b} := by
  rw [Ideal.colon_span]
  ext x
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  constructor
  · intro hx
    rw [Ideal.mem_span_pair] at hx ⊢
    obtain ⟨c, d, hcd⟩ := hx
    refine ⟨c, d, hg ?_⟩
    simp only [smul_eq_mul]
    linear_combination hcd
  · intro hx
    rw [Ideal.mem_span_pair] at hx ⊢
    obtain ⟨c, d, hcd⟩ := hx
    exact ⟨c, d, by rw [← hcd]; ring⟩

open Classical in
/-- The squarefree exponent vector of the coordinates occurring in some boundary monomial. -/
noncomputable def boundaryExp {ι κ : Type*} (exp : ι → κ → ℕ) (j : κ) : ℕ :=
  if ∃ β, exp β j ≠ 0 then 1 else 0

/-- Coordinates that come one by one from a subring give a squarefree product coming from it. -/
theorem rad_of_coord {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {ι κ : Type*}
    [Fintype κ] {T : κ → B} (exp : ι → κ → ℕ)
    (h : ∀ j, (∃ β, exp β j ≠ 0) → ∃ a : A, Ideal.span {f a} = Ideal.span {T j}) :
    ∃ a : A, Ideal.span {f a} = Ideal.span {∏ j, T j ^ boundaryExp exp j} := by
  classical
  choose! a ha using h
  refine ⟨∏ j, (if ∃ β, exp β j ≠ 0 then a j else 1), ?_⟩
  rw [map_prod, ← Ideal.prod_span_singleton, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  unfold boundaryExp
  split_ifs with hj
  · rw [ha j hj, pow_one]
  · rw [map_one, pow_zero]

end Helpers

section Charts

variable (k : Type*) [Field k] (O : Type*) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  {ι : Type*}

/-- A **formal node chart** of the Noetherian local ring `O` with respect to the singular-locus
ideal `N` and the boundary ideals `E β` (blueprint `def:sm-dj-formal-charts`): an isomorphism
`e : NodeModel k n ≃+* Ô` (`∑ n_i ≥ 1`) carrying `(U, V)` to the trace of `N` and monomials
`Z^{exp β}` to generators of the traces of the `E β`, such that every coordinate `Z_i` occurring in
a boundary monomial is, up to a unit, the image of an element of `O`. -/
structure NodeChart (m : ℕ) (N : Ideal O) (E : ι → Ideal O) where
  /-- The exponents of the node equation `U V = ∏ Z_i ^ n_i`. -/
  n : Fin m → ℕ
  pos : ∑ i, n i ≠ 0
  /-- The chart. -/
  e : NodeModel k n ≃+* AdicCompletion (maximalIdeal O) O
  trace_N : N.map (algebraMap O (AdicCompletion (maximalIdeal O) O)) =
    Ideal.span {e (nodeU k n), e (nodeV k n)}
  /-- The exponents of the boundary monomials. -/
  exp : ι → Fin m → ℕ
  trace_E : ∀ β, (E β).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) =
    Ideal.span {e (nodeZMon k n (exp β))}
  coord : ∀ i, (∃ β, exp β i ≠ 0) → ∃ f : O,
    Ideal.span {algebraMap O (AdicCompletion (maximalIdeal O) O) f} =
      Ideal.span {e (nodeZ k n i)}

/-- A **formal regular chart** of `O` with respect to the boundary ideals `E β`: `m + 1`
generators `T` of the maximal ideal of `Ô` such that the traces of the `E β` are generated by
monomials in `T`, and the product of the coordinates occurring in some boundary monomial is, up
to a unit, the image of an element of `O`. -/
structure RegChart (m : ℕ) (E : ι → Ideal O) where
  /-- The coordinates. -/
  T : Fin (m + 1) → AdicCompletion (maximalIdeal O) O
  span_eq : Ideal.span (Set.range T) = maximalIdeal (AdicCompletion (maximalIdeal O) O)
  /-- The exponents of the boundary monomials. -/
  exp : ι → Fin (m + 1) → ℕ
  trace_E : ∀ β, (E β).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) =
    Ideal.span {∏ j, T j ^ exp β j}
  rad : ∃ f : O, Ideal.span {algebraMap O (AdicCompletion (maximalIdeal O) O) f} =
    Ideal.span {∏ j, T j ^ boundaryExp exp j}

end Charts

namespace NodeChart

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  {ι : Type*} {m : ℕ} {N : Ideal O} {E : ι → Ideal O} (c : NodeChart k O m N E)

/-- The node model of a node chart is local. -/
theorem isLocalRing : IsLocalRing (NodeModel k c.n) := c.e.symm.isLocalRing

/-- The node coordinates generate the maximal ideal of `Ô`. -/
theorem span_eq : Ideal.span (insert (c.e (nodeU k c.n)) (insert (c.e (nodeV k c.n))
    (Set.range fun i ↦ c.e (nodeZ k c.n i)))) =
      maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
  have := c.isLocalRing
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal c.e, maximalIdeal_nodeModel, Ideal.map_span,
    Set.image_insert_eq, Set.image_insert_eq, ← Set.range_comp]
  rfl

omit [IsNoetherianRing O] in
/-- The node relation in `Ô`. -/
theorem rel : c.e (nodeU k c.n) * c.e (nodeV k c.n) = ∏ i, c.e (nodeZ k c.n i) ^ c.n i := by
  rw [← map_mul, nodeU_mul_nodeV, nodeZMon_eq_prod, map_prod]
  simp_rw [map_pow]

omit [IsNoetherianRing O] in
/-- The boundary traces as products of coordinates. -/
theorem trace_E' (β : ι) : (E β).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) =
    Ideal.span {∏ i, c.e (nodeZ k c.n i) ^ c.exp β i} := by
  rw [c.trace_E β, nodeZMon_eq_prod, map_prod]
  simp_rw [map_pow]

end NodeChart

section Step

variable {k O P : Type*} [Field k] [CommRing O] [IsLocalRing O]
  [Algebra k O] [CommRing P] [IsLocalRing P] [Algebra k P]
  (φ : O →+* P) [IsNoetherianRing O] [IsNoetherianRing P] [IsLocalHom φ]

local notation "Rh" => AdicCompletion (maximalIdeal O) O
local notation "Qh" => AdicCompletion (maximalIdeal P) P

omit [IsNoetherianRing O] [IsNoetherianRing P] in
/-- Extension to `P̂` of an extension to `P` is extension to `Ô` followed by the completion map. -/
theorem map_map_completion (J : Ideal O) :
    (J.map φ).map (algebraMap P Qh) = (J.map (algebraMap O Rh)).map (completionMap φ) := by
  rw [Ideal.map_map, Ideal.map_map, show (algebraMap P Qh).comp φ =
    (completionMap φ).comp (algebraMap O Rh) from
      RingHom.ext fun o ↦ (completionMap_algebraMap φ o).symm]

omit [IsNoetherianRing O] [IsLocalRing O] [IsLocalHom φ] in
/-- The trace on `P̂` of a colon ideal `(N P : I P)`. -/
theorem trace_colon (N I : Ideal O) :
    ((N.map φ).colon ((I.map φ : Ideal P) : Set P)).map (algebraMap P Qh) =
      ((N.map φ).map (algebraMap P Qh)).colon
        (((I.map φ).map (algebraMap P Qh) : Ideal Qh) : Set Qh) := by
  have : Module.FaithfullyFlat P Qh := faithfullyFlat P
  exact map_colon_of_flat _ _ (Ideal.fg_of_isNoetherianRing _)

omit [IsNoetherianRing O] in
/-- The image in `P̂` of a non-zero element of the domain `P` is a non-zero-divisor. -/
theorem isSMulRegular_algebraMap [IsDomain P] {x : P} (hx : x ≠ 0) :
    IsSMulRegular Qh (algebraMap P Qh x) := by
  have : Module.FaithfullyFlat P Qh := faithfullyFlat P
  apply IsSMulRegular.of_flat
  intro a b hab
  exact mul_left_cancel₀ hx hab

omit [IsNoetherianRing O] [IsNoetherianRing P] in
/-- Coordinates coming from `O` stay coordinates coming from `P`. -/
theorem coord_map {f : O} {z : Rh}
    (hf : Ideal.span {algebraMap O Rh f} = Ideal.span {z}) :
    Ideal.span {algebraMap P Qh (φ f)} = Ideal.span {completionMap φ z} := by
  have := congrArg (Ideal.map (completionMap φ)) hf
  rwa [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    completionMap_algebraMap] at this

/-- **Strict transforms of coordinates.** If `f ∈ O` gives the coordinate `z ∈ I Ô`, and
`Φ(z) = G w` where `G` generates `I P̂ = (φ g)`, then `w` is, up to a unit, the image of an element
of `P`. -/
theorem coord_div [IsDomain P] (I : Ideal O) (g : O) (hIg : I.map φ = Ideal.span {φ g})
    (hg0 : φ g ≠ 0) {f : O} {z : Rh} (hf : Ideal.span {algebraMap O Rh f} = Ideal.span {z})
    (hzI : z ∈ I.map (algebraMap O Rh)) {G w : Qh}
    (hG : Ideal.span {G} = Ideal.span {algebraMap P Qh (φ g)})
    (hzw : completionMap φ z = G * w) :
    ∃ q : P, Ideal.span {algebraMap P Qh q} = Ideal.span {w} := by
  have hfI : f ∈ I := by
    rw [← comap_map O I, Ideal.mem_comap]
    have : algebraMap O Rh f ∈ Ideal.span {z} := hf ▸ Ideal.mem_span_singleton_self _
    exact (Ideal.span_singleton_le_iff_mem _).mpr hzI this
  have : φ f ∈ Ideal.span {φ g} := hIg ▸ Ideal.mem_map_of_mem φ hfI
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp this
  refine ⟨q, ?_⟩
  have h1 := coord_map φ hf
  rw [← hq, map_mul, hzw] at h1
  -- `(q̂ ĝ) = (G w)` and `(G) = (ĝ)`
  have h2 : Ideal.span {algebraMap P Qh (φ g) * algebraMap P Qh q} =
      Ideal.span {algebraMap P Qh (φ g) * w} := by
    rw [mul_comm, h1, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_mul_span_singleton, hG]
  exact span_singleton_eq_of_mul (isSMulRegular_algebraMap hg0) h2

omit [IsNoetherianRing O] in
/-- In a local ring, `x` with `x - c ∈ 𝔪` for a non-zero constant `c` is a unit. -/
theorem isUnit_of_sub_constQ_mem {x : Qh} {c : k} (hc : c ≠ 0)
    (hx : x - constQ (P := P) c ∈ maximalIdeal Qh) : IsUnit x := by
  by_contra hnu
  have hxm : x ∈ maximalIdeal Qh := (mem_maximalIdeal x).mpr hnu
  have : constQ (P := P) c ∈ maximalIdeal Qh := by
    have := Ideal.sub_mem _ hxm hx
    rwa [sub_sub_cancel] at this
  apply (mem_maximalIdeal _).mp this
  have hu : IsUnit (algebraMap k P c) := (isUnit_iff_ne_zero.mpr hc).map (algebraMap k P)
  exact hu.map (algebraMap P Qh)

omit [Algebra k O] in
/-- **The regular `U`-chart of a branch blowup** (de Jong 3.4). In the chart where `Φ(u)`
generates the exceptional ideal, `Φ(z_a) = Φ(u) z'` and `z' ≡ c`, the coordinates
`Φ(u), Φ(z_i) (i ≠ a), z' - c` form a regular chart for the transformed boundary ideals. -/
theorem regChart_of_uChart [IsDomain P] {ι : Type*} {m : ℕ} (u : Rh) (z : Fin m → Rh)
    (a : Fin m) (E : ι → Ideal O) (exp : ι → Fin m → ℕ)
    (hE : ∀ β, (E β).map (algebraMap O Rh) = Ideal.span {∏ i, z i ^ exp β i})
    (hcoord : ∀ i, (∃ β, exp β i ≠ 0) → ∃ f : O,
      Ideal.span {algebraMap O Rh f} = Ideal.span {z i})
    (I : Ideal O) (hzaI : z a ∈ I.map (algebraMap O Rh)) (g : O)
    (hIg : I.map φ = Ideal.span {φ g}) (hg0 : φ g ≠ 0) (z' : Qh) (c : k)
    (hza : completionMap φ (z a) = completionMap φ u * z')
    (hexc : Ideal.span {completionMap φ u} = Ideal.span {algebraMap P Qh (φ g)})
    (hc : z' - constQ (P := P) c ∈ maximalIdeal Qh)
    (hmax : Ideal.span (Set.range (Fin.cons (completionMap φ u) (Function.update
      (fun i ↦ completionMap φ (z i)) a (z' - constQ (P := P) c)) : Fin (m + 1) → Qh)) =
      maximalIdeal Qh) :
    Nonempty (RegChart P m fun β ↦ (E β).map φ) := by
  classical
  set Φ := completionMap φ
  let T : Fin (m + 1) → Qh :=
    Fin.cons (Φ u) (Function.update (fun i ↦ Φ (z i)) a (z' - constQ (P := P) c))
  let M : Fin (m + 1) → Fin m → ℕ := fun j i ↦
    if i = a then (if j = 0 then 1 else if j = a.succ ∧ c = 0 then 1 else 0)
    else (if j = i.succ then 1 else 0)
  have hT0 : T 0 = Φ u := rfl
  have hTs : ∀ l, T l.succ = Function.update (fun i ↦ Φ (z i)) a (z' - constQ (P := P) c) l :=
    fun l ↦ rfl
  have hx : ∀ i, Ideal.span {Φ (z i)} = Ideal.span {∏ j, T j ^ M j i} := by
    intro i
    rw [Fin.prod_univ_succ]
    by_cases hia : i = a
    · subst hia
      have hM0 : M 0 i = 1 := by simp [M]
      have hMs : ∀ l, M l.succ i = if l = i ∧ c = 0 then 1 else 0 := by
        intro l
        simp only [M, if_true, Fin.succ_ne_zero, if_false, Fin.succ_inj]
      simp_rw [hM0, hMs, pow_one]
      by_cases hc0 : c = 0
      · subst hc0
        rw [Finset.prod_eq_single i (fun l _ hl ↦ by simp [hl]) (by simp)]
        simp only [and_true, if_true, pow_one, hTs, Function.update_self, hT0]
        rw [hza]
        congr 2
        simp [constQ]
      · rw [Finset.prod_eq_one (fun l _ ↦ by simp [hc0]), mul_one, hT0, hza]
        exact Ideal.span_singleton_mul_right_unit (isUnit_of_sub_constQ_mem hc0 hc) _
    · have hM0 : M 0 i = 0 := by simp [M, hia, (Fin.succ_ne_zero i).symm]
      have hMs : ∀ l, M l.succ i = if l = i then 1 else 0 := by
        intro l
        simp only [M, hia, if_false, Fin.succ_inj]
      simp_rw [hM0, hMs, pow_zero, one_mul]
      rw [Finset.prod_eq_single i (fun l _ hl ↦ by simp [hl]) (by simp)]
      simp only [if_true, pow_one, hTs, Function.update_of_ne hia]
  have hcoordT : ∀ j, (∃ β, ∑ i, M j i * exp β i ≠ 0) → ∃ f : P,
      Ideal.span {algebraMap P Qh f} = Ideal.span {T j} := by
    rintro j ⟨β, hβ⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
    have hMi : M j i ≠ 0 := left_ne_zero_of_mul hi
    have hei : exp β i ≠ 0 := right_ne_zero_of_mul hi
    cases j using Fin.cases with
    | zero => exact ⟨φ g, hexc.symm⟩
    | succ l =>
      by_cases hia : i = a
      · subst hia
        have hl : l = i ∧ c = 0 := by
          by_contra h
          apply hMi
          simp only [M, if_true, Fin.succ_ne_zero, if_false, Fin.succ_inj]
          rw [if_neg h]
        obtain ⟨rfl, rfl⟩ := hl
        obtain ⟨f, hf⟩ := hcoord l ⟨β, hei⟩
        have hT : T l.succ = z' := by
          rw [hTs, Function.update_self]
          simp [constQ]
        rw [hT]
        exact coord_div φ I g hIg hg0 hf hzaI hexc hza
      · have hli : l = i := by
          by_contra h
          apply hMi
          simp only [M, hia, if_false, Fin.succ_inj, h]
        subst hli
        obtain ⟨f, hf⟩ := hcoord l ⟨β, hei⟩
        refine ⟨φ f, ?_⟩
        rw [hTs, Function.update_of_ne hia]
        exact coord_map φ hf
  refine ⟨RegChart.mk T hmax (fun β j ↦ ∑ i, M j i * exp β i) ?_ (rad_of_coord _ _ hcoordT)⟩
  intro β
  rw [map_map_completion, hE β, Ideal.map_span, Set.image_singleton, map_prod]
  simp_rw [map_pow]
  exact span_prod_pow_eq _ T M hx (exp β)

omit [IsNoetherianRing O] [Algebra k O] [Algebra k P] in
/-- A **regular chart with shifted coordinates**: if `t, Φ(z_1), …, Φ(z_m)` generate `𝔪_{P̂}`,
they form a regular chart for the transformed boundary ideals. -/
theorem regChart_of_cons {ι : Type*} {m : ℕ} (z : Fin m → Rh) (E : ι → Ideal O)
    (exp : ι → Fin m → ℕ)
    (hE : ∀ β, (E β).map (algebraMap O Rh) = Ideal.span {∏ i, z i ^ exp β i})
    (hcoord : ∀ i, (∃ β, exp β i ≠ 0) → ∃ f : O,
      Ideal.span {algebraMap O Rh f} = Ideal.span {z i}) (t : Qh)
    (hmax : Ideal.span (Set.range (Fin.cons t (fun i ↦ completionMap φ (z i)) :
      Fin (m + 1) → Qh)) = maximalIdeal Qh) :
    Nonempty (RegChart P m fun β ↦ (E β).map φ) := by
  classical
  let T : Fin (m + 1) → Qh := Fin.cons t (fun i ↦ completionMap φ (z i))
  let M : Fin (m + 1) → Fin m → ℕ := fun j i ↦ if j = i.succ then 1 else 0
  have hx : ∀ i, Ideal.span {completionMap φ (z i)} = Ideal.span {∏ j, T j ^ M j i} := by
    intro i
    rw [Finset.prod_eq_single i.succ (fun j _ hj ↦ by simp [M, hj]) (by simp)]
    simp [M, T]
  have hcoordT : ∀ j, (∃ β, ∑ i, M j i * exp β i ≠ 0) → ∃ f : P,
      Ideal.span {algebraMap P Qh f} = Ideal.span {T j} := by
    rintro j ⟨β, hβ⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
    have hMi : M j i ≠ 0 := left_ne_zero_of_mul hi
    have hji : j = i.succ := by
      by_contra h
      exact hMi (by simp [M, h])
    subst hji
    obtain ⟨f, hf⟩ := hcoord i ⟨β, right_ne_zero_of_mul hi⟩
    exact ⟨φ f, coord_map φ hf⟩
  refine ⟨RegChart.mk T hmax (fun β j ↦ ∑ i, M j i * exp β i) ?_ (rad_of_coord _ _ hcoordT)⟩
  intro β
  rw [map_map_completion, hE β, Ideal.map_span, Set.image_singleton, map_prod]
  simp_rw [map_pow]
  exact span_prod_pow_eq _ T M hx (exp β)

/-- A generator of the same principal ideal as a non-zero-divisor is a non-zero-divisor. -/
theorem isSMulRegular_of_span_eq {R : Type*} [CommRing R] {x y : R}
    (h : Ideal.span {x} = Ideal.span {y}) (hy : IsSMulRegular R y) : IsSMulRegular R x := by
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self y)
  intro a b hab
  apply hy
  simp only [smul_eq_mul] at hab ⊢
  rw [← hs, mul_assoc, mul_assoc, hab]

omit [IsNoetherianRing O] in
/-- **The singular-locus ideal over a regular chart**: if the exceptional generator lies in
`(Φ u, Φ v)` (the image of the trace of `N`), the transformed ideal `(N P : I P)` has trivial
trace. -/
theorem trace_colon_eq_top (N I : Ideal O) (u v : Rh)
    (hN : N.map (algebraMap O Rh) = Ideal.span {u, v}) (g : O)
    (hIg : I.map φ = Ideal.span {φ g})
    (hle : algebraMap P Qh (φ g) ∈ Ideal.span {completionMap φ u, completionMap φ v}) :
    ((N.map φ).colon ((I.map φ : Ideal P) : Set P)).map (algebraMap P Qh) = ⊤ := by
  rw [trace_colon, map_map_completion, hN, hIg, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_pair, Ideal.colon_span, Submodule.colon_eq_top_iff_subset,
    Set.singleton_subset_iff]
  exact hle

omit [IsNoetherianRing O] in
/-- **The singular-locus ideal over a node chart**: if `Φ u = G u'`, `Φ v = G v'` for a
generator `G` of the exceptional ideal, the transformed ideal `(N P : I P)` has trace `(u', v')`. -/
theorem trace_colon_eq_span [IsDomain P] (N I : Ideal O) (u v : Rh)
    (hN : N.map (algebraMap O Rh) = Ideal.span {u, v}) (g : O)
    (hIg : I.map φ = Ideal.span {φ g}) (hg0 : φ g ≠ 0) (G u' v' : Qh)
    (hG : Ideal.span {G} = Ideal.span {algebraMap P Qh (φ g)})
    (hu : completionMap φ u = G * u') (hv : completionMap φ v = G * v') :
    ((N.map φ).colon ((I.map φ : Ideal P) : Set P)).map (algebraMap P Qh) =
      Ideal.span {u', v'} := by
  rw [trace_colon, map_map_completion, hN, hIg, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_pair, hu, hv, ← hG]
  exact span_pair_mul_colon (isSMulRegular_of_span_eq hG (isSMulRegular_algebraMap hg0))

omit [IsNoetherianRing O] [Algebra k O] in
/-- **The node chart of a blowup chart.** If `P̂` has generators `u', v', Φ(z)` with
`u' v' = ∏ Φ(z_i) ^ {n'_i}` (some `n'_i > 0`), `Φ u = Φ(z_a) u'`, `Φ v = Φ(z_a) v'` and `Φ(z_a)`
generates the exceptional ideal, then `P̂` has a node chart of type `n'` for the transformed
singular-locus and boundary ideals, with the same boundary exponents. -/
theorem nodeChart_of_zChart [IsDomain P]
    (hresP : Function.Bijective (algebraMap k (ResidueField P)))
    {ι : Type*} {m : ℕ} (u v : Rh) (z : Fin m → Rh) (N : Ideal O) (E : ι → Ideal O)
    (exp : ι → Fin m → ℕ) (hN : N.map (algebraMap O Rh) = Ideal.span {u, v})
    (hE : ∀ β, (E β).map (algebraMap O Rh) = Ideal.span {∏ i, z i ^ exp β i})
    (hcoord : ∀ i, (∃ β, exp β i ≠ 0) → ∃ f : O,
      Ideal.span {algebraMap O Rh f} = Ideal.span {z i})
    (I : Ideal O) (g : O) (hIg : I.map φ = Ideal.span {φ g}) (hg0 : φ g ≠ 0) (a : Fin m)
    (u' v' : Qh) (hu : completionMap φ u = completionMap φ (z a) * u')
    (hv : completionMap φ v = completionMap φ (z a) * v')
    (hexc : Ideal.span {completionMap φ (z a)} = Ideal.span {algebraMap P Qh (φ g)})
    (n' : Fin m → ℕ) (hn' : ∑ i, n' i ≠ 0)
    (hrel : u' * v' = ∏ i, completionMap φ (z i) ^ n' i)
    (hspan : Ideal.span (insert u' (insert v' (Set.range fun i ↦ completionMap φ (z i)))) =
      maximalIdeal Qh)
    (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim P) :
    ∃ c' : NodeChart k P m ((N.map φ).colon ((I.map φ : Ideal P) : Set P))
      (fun β ↦ (E β).map φ), c'.n = n' ∧ c'.exp = exp := by
  classical
  let : Algebra k Qh := ((algebraMap P Qh).comp (algebraMap k P)).toAlgebra
  have hres : Function.Surjective (algebraMap k (ResidueField Qh)) :=
    (bijective_constQ_residue (k := k) hresP).2
  have hdimQ : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim Qh :=
    hdim.trans (Algebra.CompletionRegularityAscent.ringKrullDim_le_completion P)
  obtain ⟨e', he'U, he'V, he'Z⟩ := exists_nodeModel_algEquiv (k := k) n' hn' hres u' v'
    (fun i ↦ completionMap φ (z i)) hspan hrel hdimQ
  refine ⟨⟨n', hn', e'.toRingEquiv, ?_, exp, ?_, ?_⟩, rfl, rfl⟩
  · change _ = Ideal.span {e' (nodeU k n'), e' (nodeV k n')}
    rw [he'U, he'V]
    exact trace_colon_eq_span φ N I u v hN g hIg hg0 _ u' v' hexc hu hv
  · intro β
    change _ = Ideal.span {e' (nodeZMon k n' (exp β))}
    rw [map_map_completion, hE β, Ideal.map_span, Set.image_singleton, map_prod,
      nodeZMon_eq_prod, map_prod]
    simp_rw [map_pow, he'Z]
  · intro i hi
    obtain ⟨f, hf⟩ := hcoord i hi
    refine ⟨φ f, ?_⟩
    change _ = Ideal.span {e' (nodeZ k n' i)}
    rw [he'Z]
    exact coord_map φ hf

/-- **The blowup step at a branch** (de Jong 3.4). Let `O` have a node chart `c` with
`n_a ≥ 2`, and let `φ : O → P` be a chart localization for an ideal `I` with
`I Ô = (U, V, Z_a)`, `P` a domain of dimension at least `m + 1` with residue field `k`. Then `P` has
a node chart of type `n - 2 e_a` with the same boundary exponents for the transformed ideals
`N' = (N P : I P)`, `E' = E P`, or a regular chart with `N'` of trivial trace. -/
theorem branch_step [IsDomain P]
    (hφk : ∀ c : k, φ (algebraMap k O c) = algebraMap k P c)
    (hresO : Function.Surjective (algebraMap k (ResidueField O)))
    (hresP : Function.Bijective (algebraMap k (ResidueField P)))
    {ι : Type*} {m : ℕ} {N : Ideal O} {E : ι → Ideal O} (c : NodeChart k O m N E)
    (a : Fin m) (hna : 2 ≤ c.n a) (I : Ideal O)
    (hI : I.map (algebraMap O Rh) =
      Ideal.span {c.e (nodeU k c.n), c.e (nodeV k c.n), c.e (nodeZ k c.n a)})
    (g : O) (hg : g ∈ I) (hIg : I.map φ = Ideal.span {φ g}) (hg0 : φ g ≠ 0)
    (hgen : IsChartLocalization φ I g) (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim P) :
    (∃ c' : NodeChart k P m ((N.map φ).colon ((I.map φ : Ideal P) : Set P))
        (fun β ↦ (E β).map φ), c'.n = Function.update c.n a (c.n a - 2) ∧ c'.exp = c.exp) ∨
      (Nonempty (RegChart P m fun β ↦ (E β).map φ) ∧
        ((N.map φ).colon ((I.map φ : Ideal P) : Set P)).map (algebraMap P Qh) = ⊤) := by
  classical
  set u := c.e (nodeU k c.n)
  set v := c.e (nodeV k c.n)
  set z : Fin m → Rh := fun i ↦ c.e (nodeZ k c.n i)
  have hzaI : z a ∈ I.map (algebraMap O Rh) := hI ▸ Ideal.subset_span (by simp [z])
  have hE := c.trace_E'
  have hN := c.trace_N
  set G := algebraMap P Qh (φ g)
  rcases branch_blowup_chart φ hφk hresO hresP u v z c.n a hna c.span_eq c.rel I hI g hg hIg
    hg0 hgen with ⟨z', cc, hza, hvU, hexc, hcc, hmax⟩ | ⟨z', cc, hza, huV, hexc, hcc, hmax⟩ |
    ⟨u', v', bu, bv, hu, hv, hexc, hrel', hcases⟩
  · refine Or.inr ⟨regChart_of_uChart φ u z a E c.exp hE c.coord I hzaI g hIg hg0 z' cc hza hexc
      hcc hmax, trace_colon_eq_top φ N I u v hN g hIg ?_⟩
    have hG : G ∈ Ideal.span {completionMap φ u} := by
      rw [hexc]; exact Ideal.mem_span_singleton_self _
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hG
  · refine Or.inr ⟨regChart_of_uChart φ v z a E c.exp hE c.coord I hzaI g hIg hg0 z' cc hza hexc
      hcc hmax, trace_colon_eq_top φ N I u v hN g hIg ?_⟩
    have hG : G ∈ Ideal.span {completionMap φ v} := by
      rw [hexc]; exact Ideal.mem_span_singleton_self _
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hG
  · rcases hcases with ⟨rfl, rfl, hspan'⟩ | ⟨hbu, hbu', hmax⟩ | ⟨hbv, hbv', hmax⟩
    · refine Or.inl (nodeChart_of_zChart φ hresP u v z N E c.exp hN hE c.coord I g hIg hg0 a u' v'
        hu hv hexc _ ?_ hrel' hspan' hdim)
      intro h0
      have hall : ∀ i, Function.update c.n a (c.n a - 2) i = 0 := fun i ↦
        Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ i)
      have hone : u' * v' = 1 := by
        rw [hrel']
        exact Finset.prod_eq_one fun i _ ↦ by rw [hall i, pow_zero]
      have hu'm : u' ∈ maximalIdeal Qh := hspan' ▸ Ideal.subset_span (Set.mem_insert _ _)
      exact (mem_maximalIdeal _).mp hu'm (IsUnit.of_mul_eq_one _ hone)
    · refine Or.inr ⟨regChart_of_cons φ z E c.exp hE c.coord _ hmax,
        trace_colon_eq_top φ N I u v hN g hIg ?_⟩
      have hunit := isUnit_of_sub_constQ_mem hbu hbu'
      have : Ideal.span {completionMap φ u} = Ideal.span {G} := by
        rw [hu, Ideal.span_singleton_mul_right_unit hunit, hexc]
      have hG : G ∈ Ideal.span {completionMap φ u} := by
        rw [this]; exact Ideal.mem_span_singleton_self _
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hG
    · refine Or.inr ⟨regChart_of_cons φ z E c.exp hE c.coord _ hmax,
        trace_colon_eq_top φ N I u v hN g hIg ?_⟩
      have hunit := isUnit_of_sub_constQ_mem hbv hbv'
      have : Ideal.span {completionMap φ v} = Ideal.span {G} := by
        rw [hv, Ideal.span_singleton_mul_right_unit hunit, hexc]
      have hG : G ∈ Ideal.span {completionMap φ v} := by
        rw [this]; exact Ideal.mem_span_singleton_self _
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hG

omit [IsNoetherianRing O] [Algebra k O] in
/-- **Packaging a node chart from generators.** If `P̂` has generators `u', v', Z'` of its maximal
ideal with `u' v' = ∏ Z'_i ^ {n'_i}` (some `n'_i > 0`), `P` has dimension at least `m + 1` and
residue field `k`, and the transformed ideals have the traces of a node chart, then `P` has a node
chart of type `n'`. -/
theorem nodeChart_of_generators (hresP : Function.Bijective (algebraMap k (ResidueField P)))
    {ι : Type*} {m : ℕ} (N' : Ideal P) (E' : ι → Ideal P) (u' v' : Qh) (Z' : Fin m → Qh)
    (n' : Fin m → ℕ) (hn' : ∑ i, n' i ≠ 0) (hrel : u' * v' = ∏ i, Z' i ^ n' i)
    (hspan : Ideal.span (insert u' (insert v' (Set.range Z'))) = maximalIdeal Qh)
    (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim P)
    (hN : N'.map (algebraMap P Qh) = Ideal.span {u', v'}) (exp' : ι → Fin m → ℕ)
    (hE : ∀ β, (E' β).map (algebraMap P Qh) = Ideal.span {∏ i, Z' i ^ exp' β i})
    (hcoord : ∀ i, (∃ β, exp' β i ≠ 0) → ∃ f : P,
      Ideal.span {algebraMap P Qh f} = Ideal.span {Z' i}) :
    ∃ c' : NodeChart k P m N' E', c'.n = n' ∧ c'.exp = exp' := by
  classical
  let : Algebra k Qh := ((algebraMap P Qh).comp (algebraMap k P)).toAlgebra
  have hres : Function.Surjective (algebraMap k (ResidueField Qh)) :=
    (bijective_constQ_residue (k := k) hresP).2
  have hdimQ : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim Qh :=
    hdim.trans (Algebra.CompletionRegularityAscent.ringKrullDim_le_completion P)
  obtain ⟨e', he'U, he'V, he'Z⟩ := exists_nodeModel_algEquiv (k := k) n' hn' hres u' v' Z'
    hspan hrel hdimQ
  refine ⟨⟨n', hn', e'.toRingEquiv, ?_, exp', ?_, ?_⟩, rfl, rfl⟩
  · change _ = Ideal.span {e' (nodeU k n'), e' (nodeV k n')}
    rw [he'U, he'V, hN]
  · intro β
    change _ = Ideal.span {e' (nodeZMon k n' (exp' β))}
    rw [hE β, nodeZMon_eq_prod, map_prod]
    simp_rw [map_pow, he'Z]
  · intro i hi
    change ∃ f : P, _ = Ideal.span {e' (nodeZ k n' i)}
    rw [he'Z]
    exact hcoord i hi

omit [Algebra k O] in
/-- **The regular `U`-chart of a blowup along `(u, v, z_S)`.** In the chart where `Φ(u)`
generates the exceptional ideal and `Φ(z_i) = Φ(u) w_i`, `w_i ≡ c_i` (`i ∈ S`), the coordinates
`Φ(u)`, `Φ(z_i)` (`i ∉ S`), `w_i - c_i` (`i ∈ S`) form a regular chart. -/
theorem regChart_of_uChart_finset [IsDomain P] {ι : Type*} {m : ℕ} (u : Rh) (z : Fin m → Rh)
    (S : Finset (Fin m)) (E : ι → Ideal O) (exp : ι → Fin m → ℕ)
    (hE : ∀ β, (E β).map (algebraMap O Rh) = Ideal.span {∏ i, z i ^ exp β i})
    (hcoord : ∀ i, (∃ β, exp β i ≠ 0) → ∃ f : O,
      Ideal.span {algebraMap O Rh f} = Ideal.span {z i})
    (I : Ideal O) (hzI : ∀ i ∈ S, z i ∈ I.map (algebraMap O Rh)) (g : O)
    (hIg : I.map φ = Ideal.span {φ g}) (hg0 : φ g ≠ 0) (w : Fin m → Qh) (c : Fin m → k)
    (hzw : ∀ i ∈ S, completionMap φ (z i) = completionMap φ u * w i)
    (hexc : Ideal.span {completionMap φ u} = Ideal.span {algebraMap P Qh (φ g)})
    (hc : ∀ i ∈ S, w i - constQ (P := P) (c i) ∈ maximalIdeal Qh)
    (hmax : Ideal.span (Set.range (Fin.cons (completionMap φ u) (fun i ↦ if i ∈ S then
      w i - constQ (P := P) (c i) else completionMap φ (z i)) : Fin (m + 1) → Qh)) =
      maximalIdeal Qh) :
    Nonempty (RegChart P m fun β ↦ (E β).map φ) := by
  classical
  set Φ := completionMap φ
  let T : Fin (m + 1) → Qh :=
    Fin.cons (Φ u) (fun i ↦ if i ∈ S then w i - constQ (P := P) (c i) else Φ (z i))
  let M : Fin (m + 1) → Fin m → ℕ := fun j i ↦
    if i ∈ S then (if j = 0 then 1 else if j = i.succ ∧ c i = 0 then 1 else 0)
    else (if j = i.succ then 1 else 0)
  have hT0 : T 0 = Φ u := rfl
  have hTs : ∀ l, T l.succ = if l ∈ S then w l - constQ (P := P) (c l) else Φ (z l) :=
    fun l ↦ rfl
  have hx : ∀ i, Ideal.span {Φ (z i)} = Ideal.span {∏ j, T j ^ M j i} := by
    intro i
    rw [Fin.prod_univ_succ]
    by_cases hiS : i ∈ S
    · have hM0 : M 0 i = 1 := by simp [M, hiS]
      have hMs : ∀ l, M l.succ i = if l = i ∧ c i = 0 then 1 else 0 := by
        intro l
        simp only [M, hiS, if_true, Fin.succ_ne_zero, if_false, Fin.succ_inj]
      simp_rw [hM0, hMs, pow_one]
      by_cases hc0 : c i = 0
      · rw [Finset.prod_eq_single i (fun l _ hl ↦ by simp [hl]) (by simp)]
        simp only [hc0, and_true, if_true, pow_one, hTs, hiS, hT0]
        rw [hzw i hiS]
        congr 2
        simp [constQ]
      · rw [Finset.prod_eq_one (fun l _ ↦ by simp [hc0]), mul_one, hT0, hzw i hiS]
        exact Ideal.span_singleton_mul_right_unit (isUnit_of_sub_constQ_mem hc0 (hc i hiS)) _
    · have hM0 : M 0 i = 0 := by simp [M, hiS, (Fin.succ_ne_zero i).symm]
      have hMs : ∀ l, M l.succ i = if l = i then 1 else 0 := by
        intro l
        simp only [M, hiS, if_false, Fin.succ_inj]
      simp_rw [hM0, hMs, pow_zero, one_mul]
      rw [Finset.prod_eq_single i (fun l _ hl ↦ by simp [hl]) (by simp)]
      simp only [if_true, pow_one, hTs, hiS, if_false]
  have hcoordT : ∀ j, (∃ β, ∑ i, M j i * exp β i ≠ 0) → ∃ f : P,
      Ideal.span {algebraMap P Qh f} = Ideal.span {T j} := by
    rintro j ⟨β, hβ⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
    have hMi : M j i ≠ 0 := left_ne_zero_of_mul hi
    have hei : exp β i ≠ 0 := right_ne_zero_of_mul hi
    cases j using Fin.cases with
    | zero => exact ⟨φ g, hexc.symm⟩
    | succ l =>
      by_cases hiS : i ∈ S
      · have hl : l = i ∧ c i = 0 := by
          by_contra h
          apply hMi
          simp only [M, hiS, if_true, Fin.succ_ne_zero, if_false, Fin.succ_inj]
          rw [if_neg h]
        obtain ⟨rfl, hc0⟩ := hl
        obtain ⟨f, hf⟩ := hcoord l ⟨β, hei⟩
        have hT : T l.succ = w l := by
          rw [hTs, if_pos hiS, hc0]
          simp [constQ]
        rw [hT]
        exact coord_div φ I g hIg hg0 hf (hzI l hiS) hexc (hzw l hiS)
      · have hli : l = i := by
          by_contra h
          apply hMi
          simp only [M, hiS, if_false, Fin.succ_inj, h]
        subst hli
        obtain ⟨f, hf⟩ := hcoord l ⟨β, hei⟩
        refine ⟨φ f, ?_⟩
        rw [hTs, if_neg hiS]
        exact coord_map φ hf
  refine ⟨RegChart.mk T hmax (fun β j ↦ ∑ i, M j i * exp β i) ?_ (rad_of_coord _ _ hcoordT)⟩
  intro β
  rw [map_map_completion, hE β, Ideal.map_span, Set.image_singleton, map_prod]
  simp_rw [map_pow]
  exact span_prod_pow_eq _ T M hx (exp β)

omit [IsNoetherianRing O] [Algebra k O] [Algebra k P] in
/-- Packaging a regular chart from generators and an exponent matrix. -/
theorem regChart_of_matrix {ι : Type*} {m : ℕ} (z : Fin m → Rh) (E : ι → Ideal O)
    (exp : ι → Fin m → ℕ)
    (hE : ∀ β, (E β).map (algebraMap O Rh) = Ideal.span {∏ i, z i ^ exp β i})
    (T : Fin (m + 1) → Qh) (hmax : Ideal.span (Set.range T) = maximalIdeal Qh)
    (M : Fin (m + 1) → Fin m → ℕ)
    (hx : ∀ i, Ideal.span {completionMap φ (z i)} = Ideal.span {∏ j, T j ^ M j i})
    (hcoordT : ∀ j, (∃ β, ∑ i, M j i * exp β i ≠ 0) → ∃ f : P,
      Ideal.span {algebraMap P Qh f} = Ideal.span {T j}) :
    Nonempty (RegChart P m fun β ↦ (E β).map φ) := by
  refine ⟨RegChart.mk T hmax (fun β j ↦ ∑ i, M j i * exp β i) ?_ (rad_of_coord _ _ hcoordT)⟩
  intro β
  rw [map_map_completion, hE β, Ideal.map_span, Set.image_singleton, map_prod]
  simp_rw [map_pow]
  exact span_prod_pow_eq _ T M hx (exp β)

/-- `∏_i f_i = f_a f_b ∏_{i ≠ a, b} f_i`. -/
theorem prod_eq_mul_mul_prod_erase {M : Type*} [CommMonoid M] {m : ℕ} (f : Fin m → M)
    {a b : Fin m} (hab : a ≠ b) :
    ∏ i, f i = f a * f b * ∏ i ∈ (Finset.univ.erase a).erase b, f i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩), mul_assoc]

omit [Algebra k O] in
open Classical in
/-- **The coordinates of the `Z_{a'}`-chart of a crossing blowup.** With
`Z' = Φ(z)` with `Φ(z_{b'})` replaced by `w - c` (where `Φ(z_{b'}) = Φ(z_{a'}) w`, `w ≡ c`), every
`Φ(z_i)` is, up to a unit, a monomial in `Z'`, and the coordinates of `Z'` occurring in the
transformed boundary monomials come from `P`. -/
theorem crossing_coords [IsDomain P] {ι : Type*} {m : ℕ} (z : Fin m → Rh) (exp : ι → Fin m → ℕ)
    (hcoord : ∀ i, (∃ β, exp β i ≠ 0) → ∃ f : O,
      Ideal.span {algebraMap O Rh f} = Ideal.span {z i})
    (I : Ideal O) {a' b' : Fin m} (hab : a' ≠ b') (hzbI : z b' ∈ I.map (algebraMap O Rh))
    (g : O) (hIg : I.map φ = Ideal.span {φ g}) (hg0 : φ g ≠ 0) (w : Qh) (c : k)
    (hzb : completionMap φ (z b') = completionMap φ (z a') * w)
    (hexc : Ideal.span {completionMap φ (z a')} = Ideal.span {algebraMap P Qh (φ g)})
    (hc : w - constQ (P := P) c ∈ maximalIdeal Qh) :
    let Z' := Function.update (fun i ↦ completionMap φ (z i)) b' (w - constQ (P := P) c)
    let M : Fin m → Fin m → ℕ := fun l i ↦
      if i = b' then ((if l = a' then 1 else 0) + (if l = b' ∧ c = 0 then 1 else 0))
      else (if l = i then 1 else 0)
    (∀ i, Ideal.span {completionMap φ (z i)} = Ideal.span {∏ l, Z' l ^ M l i}) ∧
    (∀ l, (∃ β, ∑ i, M l i * exp β i ≠ 0) → ∃ f : P,
      Ideal.span {algebraMap P Qh f} = Ideal.span {Z' l}) := by
  classical
  intro Z' M
  have hZa : Z' a' = completionMap φ (z a') := Function.update_of_ne hab _ _
  have hZb : Z' b' = w - constQ (P := P) c := Function.update_self _ _ _
  have hZo : ∀ i, i ≠ b' → Z' i = completionMap φ (z i) := fun i hi ↦ Function.update_of_ne hi _ _
  refine ⟨fun i ↦ ?_, fun l ⟨β, hβ⟩ ↦ ?_⟩
  · by_cases hib : i = b'
    · subst hib
      have hMa : M a' i = 1 := by simp [M, hab]
      by_cases hc0 : c = 0
      · have hprod : ∏ l, Z' l ^ M l i = Z' a' * Z' i := by
          rw [prod_eq_mul_mul_prod_erase _ hab, Finset.prod_eq_one, mul_one, hMa, pow_one]
          · have : M i i = 1 := by simp [M, hab.symm, hc0]
            rw [this, pow_one]
          · intro l hl
            have hl1 : l ≠ i := (Finset.mem_erase.mp hl).1
            have hl2 : l ≠ a' := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
            simp [M, hl1, hl2]
        rw [hprod, hZa, hZb, hzb, hc0]
        simp [constQ]
      · have hprod : ∏ l, Z' l ^ M l i = Z' a' := by
          rw [prod_eq_mul_mul_prod_erase _ hab, Finset.prod_eq_one, mul_one, hMa, pow_one]
          · have : M i i = 0 := by simp [M, hab.symm, hc0]
            rw [this, pow_zero, mul_one]
          · intro l hl
            have hl1 : l ≠ i := (Finset.mem_erase.mp hl).1
            have hl2 : l ≠ a' := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
            simp [M, hl1, hl2]
        rw [hprod, hZa, hzb]
        exact Ideal.span_singleton_mul_right_unit (isUnit_of_sub_constQ_mem hc0 hc) _
    · have hprod : ∏ l, Z' l ^ M l i = Z' i := by
        rw [Finset.prod_eq_single i (fun l _ hl ↦ by simp [M, hib, hl]) (by simp)]
        simp [M, hib]
      rw [hprod, hZo i hib]
  · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
    have hMi : M l i ≠ 0 := left_ne_zero_of_mul hi
    have hei : exp β i ≠ 0 := right_ne_zero_of_mul hi
    by_cases hib : i = b'
    · subst hib
      by_cases hla : l = a'
      · subst hla
        exact ⟨φ g, by rw [hZa]; exact hexc.symm⟩
      · have hl : l = i ∧ c = 0 := by
          by_contra h
          apply hMi
          simp [M, hla, h]
        obtain ⟨rfl, hc0⟩ := hl
        obtain ⟨f, hf⟩ := hcoord l ⟨β, hei⟩
        rw [hZb, hc0]
        simp only [constQ, map_zero, sub_zero]
        exact coord_div φ I g hIg hg0 hf hzbI hexc hzb
    · have hli : l = i := by
        by_contra h
        apply hMi
        simp [M, hib, h]
      subst hli
      obtain ⟨f, hf⟩ := hcoord l ⟨β, hei⟩
      exact ⟨φ f, by rw [hZo l hib]; exact coord_map φ hf⟩

omit [IsNoetherianRing O] [IsNoetherianRing P] [Algebra k O] [Algebra k P] [IsLocalRing O]
  [IsLocalRing P] [IsLocalHom φ] in
/-- The exponent bookkeeping of the `Z_{a'}`-chart of a crossing blowup. -/
theorem sum_crossing_matrix {m : ℕ} (w : Fin m → ℕ) {a' b' : Fin m} (hab : a' ≠ b') (p : Prop)
    [Decidable p] (l : Fin m) :
    ∑ i, (if i = b' then ((if l = a' then 1 else 0) + (if l = b' ∧ p then 1 else 0))
      else (if l = i then 1 else 0)) * w i =
      Function.update (Function.update w a' (w a' + w b')) b' ((if p then 1 else 0) * w b') l := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b')]
  have hrest : ∑ i ∈ Finset.univ.erase b', (if i = b' then ((if l = a' then 1 else 0) +
      (if l = b' ∧ p then 1 else 0)) else (if l = i then 1 else 0)) * w i =
      if l = b' then 0 else w l := by
    rw [Finset.sum_congr rfl (fun i hi ↦ by rw [if_neg (Finset.mem_erase.mp hi).1])]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    by_cases hl : l = b'
    · simp [hl]
    · simp [hl, Finset.mem_erase]
  rw [hrest, if_pos rfl]
  by_cases hlb : l = b'
  · subst hlb
    simp [hab.symm]
  · rw [Function.update_of_ne hlb]
    by_cases hla : l = a'
    · subst hla
      simp [hlb, add_comm]
    · simp [hla, hlb]

open Classical in
/-- **The blowup step at a crossing** (de Jong 4.27). Let `O` have a node chart `c` with
`n_a = n_b = 1` (`a ≠ b`), and let `φ : O → P` be a chart localization for an ideal `I` with
`I Ô = (U, V, Z_a, Z_b)`. Then `P` has a regular chart with trivial singular trace, or a node
chart obtained from the `Z_{a'}`-chart (`{a', b'} = {a, b}`): `n_{a'}` becomes `0`, `n_{b'}`
becomes `δ ≤ 1`, and the boundary exponents transform by `Z_{b'} = Z_{a'} Z'_{b'}`. -/
theorem crossing_step [IsDomain P]
    (hφk : ∀ c : k, φ (algebraMap k O c) = algebraMap k P c)
    (hresO : Function.Surjective (algebraMap k (ResidueField O)))
    (hresP : Function.Bijective (algebraMap k (ResidueField P)))
    {ι : Type*} {m : ℕ} {N : Ideal O} {E : ι → Ideal O} (c : NodeChart k O m N E)
    {a b : Fin m} (hab : a ≠ b) (hna : c.n a = 1) (hnb : c.n b = 1) (I : Ideal O)
    (hI : I.map (algebraMap O Rh) = Ideal.span {c.e (nodeU k c.n), c.e (nodeV k c.n),
      c.e (nodeZ k c.n a), c.e (nodeZ k c.n b)})
    (g : O) (hg : g ∈ I) (hIg : I.map φ = Ideal.span {φ g}) (hg0 : φ g ≠ 0)
    (hgen : IsChartLocalization φ I g) (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim P) :
    (∃ a' b' : Fin m, ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧ ∃ δ : ℕ, δ ≤ 1 ∧
      ∃ c' : NodeChart k P m ((N.map φ).colon ((I.map φ : Ideal P) : Set P))
        (fun β ↦ (E β).map φ), c'.n = Function.update (Function.update c.n a' 0) b' δ ∧
        c'.exp = fun β ↦ Function.update (Function.update (c.exp β) a'
          (c.exp β a' + c.exp β b')) b' (δ * c.exp β b')) ∨
      (Nonempty (RegChart P m fun β ↦ (E β).map φ) ∧
        ((N.map φ).colon ((I.map φ : Ideal P) : Set P)).map (algebraMap P Qh) = ⊤) := by
  set u := c.e (nodeU k c.n)
  set v := c.e (nodeV k c.n)
  set z : Fin m → Rh := fun i ↦ c.e (nodeZ k c.n i)
  have hzI : ∀ i ∈ ({a, b} : Finset (Fin m)), z i ∈ I.map (algebraMap O Rh) := by
    intro i hi
    rw [hI]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Ideal.subset_span (by simp [z])
    · exact Ideal.subset_span (by simp [z])
  have hE := c.trace_E'
  have hN := c.trace_N
  set G := algebraMap P Qh (φ g)
  -- the `U`- and `V`-charts
  have huv : ∀ (u₀ : Rh) (za zb : Qh) (ca cb : k), completionMap φ (z a) = completionMap φ u₀ * za → completionMap φ (z b) = completionMap φ u₀ * zb →
      Ideal.span {completionMap φ u₀} = Ideal.span {G} → za - constQ (P := P) ca ∈ maximalIdeal Qh →
      zb - constQ (P := P) cb ∈ maximalIdeal Qh →
      Ideal.span (Set.range (Fin.cons (completionMap φ u₀) (Function.update (Function.update
        (fun i ↦ completionMap φ (z i)) a (za - constQ (P := P) ca)) b (zb - constQ (P := P) cb)) :
          Fin (m + 1) → Qh)) = maximalIdeal Qh →
      Nonempty (RegChart P m fun β ↦ (E β).map φ) := by
    intro u₀ za zb ca cb hza hzb hexc hca hcb hmax
    let w : Fin m → Qh := fun i ↦ if i = a then za else zb
    let cc : Fin m → k := fun i ↦ if i = a then ca else cb
    have hfun : (fun i ↦ if i ∈ ({a, b} : Finset (Fin m)) then w i - constQ (P := P) (cc i)
        else completionMap φ (z i)) = Function.update (Function.update (fun i ↦ completionMap φ (z i)) a
          (za - constQ (P := P) ca)) b (zb - constQ (P := P) cb) := by
      funext i
      by_cases hib : i = b
      · subst hib; simp [w, cc, hab.symm]
      · by_cases hia : i = a
        · subst hia; simp [w, cc, hib]
        · simp [hia, hib]
    refine regChart_of_uChart_finset φ u₀ z {a, b} E c.exp hE c.coord I hzI g hIg hg0 w cc ?_
      hexc ?_ (by rw [hfun]; exact hmax)
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp only [w, if_pos rfl]; exact hza
      · simp only [w, if_neg hab.symm]; exact hzb
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simp only [w, cc, if_pos rfl]; exact hca
      · simp only [w, cc, if_neg hab.symm]; exact hcb
  have hGu : Ideal.span {completionMap φ u} = Ideal.span {G} →
      G ∈ Ideal.span {completionMap φ u, completionMap φ v} := by
    intro h
    have : G ∈ Ideal.span {completionMap φ u} := by rw [h]; exact Ideal.mem_span_singleton_self _
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) this
  have hGv : Ideal.span {completionMap φ v} = Ideal.span {G} →
      G ∈ Ideal.span {completionMap φ u, completionMap φ v} := by
    intro h
    have : G ∈ Ideal.span {completionMap φ v} := by rw [h]; exact Ideal.mem_span_singleton_self _
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))) this
  rcases crossing_blowup_chart φ hφk hresO hresP u v z c.n hab hna hnb c.span_eq c.rel I hI g hg
    hIg hg0 hgen with ⟨za, zb, ca, cb, hza, hzb, -, hexc, hca, hcb, hmax⟩ |
    ⟨za, zb, ca, cb, hza, hzb, -, hexc, hca, hcb, hmax⟩ |
    ⟨a', b', hab', u', v', zb, bu, bv, cb, hu, hv, hzb, hexc, hcb, hrel', hcases⟩
  · exact Or.inr ⟨huv u za zb ca cb hza hzb hexc hca hcb hmax,
      trace_colon_eq_top φ N I u v hN g hIg (hGu hexc)⟩
  · exact Or.inr ⟨huv v za zb ca cb hza hzb hexc hca hcb hmax,
      trace_colon_eq_top φ N I u v hN g hIg (hGv hexc)⟩
  · have ha'b' : a' ≠ b' := by rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hab; exact hab.symm]
    have hna' : c.n a' = 1 := by rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hnb' : c.n b' = 1 := by rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hzb'I : z b' ∈ I.map (algebraMap O Rh) := hzI b' (by
      rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp)
    obtain ⟨hxZ, hcoordZ⟩ := crossing_coords φ z c.exp c.coord I ha'b' hzb'I g hIg hg0 zb cb hzb
      hexc hcb
    set Z' := Function.update (fun i ↦ completionMap φ (z i)) b' (zb - constQ (P := P) cb) with hZ'
    have hZo : ∀ i, i ≠ b' → Z' i = completionMap φ (z i) := fun i hi ↦ Function.update_of_ne hi _ _
    have hZb : Z' b' = zb - constQ (P := P) cb := Function.update_self _ _ _
    have hE' : ∀ (δ : ℕ) (hδ : δ = if cb = 0 then 1 else 0) β,
        ((E β).map φ).map (algebraMap P Qh) = Ideal.span {∏ l, Z' l ^ Function.update
          (Function.update (c.exp β) a' (c.exp β a' + c.exp β b')) b' (δ * c.exp β b') l} := by
      intro δ hδ β
      rw [map_map_completion, hE β, Ideal.map_span, Set.image_singleton, map_prod]
      simp_rw [map_pow]
      rw [span_prod_pow_eq _ Z' _ hxZ (c.exp β)]
      congr 2
      refine Finset.prod_congr rfl fun l _ ↦ ?_
      rw [hδ, sum_crossing_matrix (c.exp β) ha'b' (cb = 0) l]
    have hcoord' : ∀ (δ : ℕ) (hδ : δ = if cb = 0 then 1 else 0) l, (∃ β, Function.update
        (Function.update (c.exp β) a' (c.exp β a' + c.exp β b')) b' (δ * c.exp β b') l ≠ 0) →
        ∃ f : P, Ideal.span {algebraMap P Qh f} = Ideal.span {Z' l} := by
      rintro δ hδ l ⟨β, hβ⟩
      refine hcoordZ l ⟨β, ?_⟩
      rwa [sum_crossing_matrix (c.exp β) ha'b' (cb = 0) l, ← hδ]
    rcases hcases with ⟨rfl, rfl, hspan'⟩ | ⟨hbu, hbu', hmax⟩ | ⟨hbv, hbv', hmax⟩
    · refine Or.inl ⟨a', b', hab', ?_⟩
      have hN' := trace_colon_eq_span φ N I u v hN g hIg hg0 _ u' v' hexc hu hv
      have hu'm : u' ∈ maximalIdeal Qh := hspan' ▸ Ideal.subset_span (Set.mem_insert _ _)
      have hprod : ∀ n' : Fin m → ℕ, (∀ i, i ≠ a' → i ≠ b' → n' i = c.n i) → n' a' = 0 →
          ∏ i, Z' i ^ n' i = Z' b' ^ n' b' * ∏ i ∈ (Finset.univ.erase a').erase b',
            completionMap φ (z i) ^ c.n i := by
        intro n' hn'o hn'a
        rw [prod_eq_mul_mul_prod_erase _ ha'b', hn'a, pow_zero, one_mul]
        congr 1
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hi1 : i ≠ b' := (Finset.mem_erase.mp hi).1
        have hi2 : i ≠ a' := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        rw [hZo i hi1, hn'o i hi2 hi1]
      by_cases hcb0 : cb = 0
      · refine ⟨1, le_rfl, ?_⟩
        set n' := Function.update (Function.update c.n a' 0) b' 1
        have hn'o : ∀ i, i ≠ a' → i ≠ b' → n' i = c.n i := fun i h1 h2 ↦ by
          simp [n', Function.update_of_ne h1, Function.update_of_ne h2]
        have hn'a : n' a' = 0 := by simp [n', Function.update_of_ne ha'b']
        have hn'b : n' b' = 1 := by simp [n']
        have hrel'' : u' * v' = ∏ i, Z' i ^ n' i := by
          rw [hprod n' hn'o hn'a, hn'b, pow_one, hZb, hcb0, hrel']
          simp [constQ]
        have hn'pos : ∑ i, n' i ≠ 0 := by
          intro h0
          have := Finset.sum_eq_zero_iff.mp h0 b' (Finset.mem_univ _)
          rw [hn'b] at this
          exact one_ne_zero this
        obtain ⟨c', hc'n, hc'exp⟩ := nodeChart_of_generators hresP _ _ u' v' Z' n' hn'pos hrel''
          hspan' hdim hN' _ (hE' 1 (by simp [hcb0])) (hcoord' 1 (by simp [hcb0]))
        exact ⟨c', hc'n, hc'exp⟩
      · refine ⟨0, zero_le_one, ?_⟩
        have hunit : IsUnit zb := isUnit_of_sub_constQ_mem hcb0 hcb
        set u'' := u' * (hunit.unit⁻¹ : (Qh)ˣ)
        set n' := Function.update (Function.update c.n a' 0) b' 0
        have hn'o : ∀ i, i ≠ a' → i ≠ b' → n' i = c.n i := fun i h1 h2 ↦ by
          simp [n', Function.update_of_ne h1, Function.update_of_ne h2]
        have hn'a : n' a' = 0 := by simp [n', Function.update_of_ne ha'b']
        have hn'b : n' b' = 0 := by simp [n']
        have hrel'' : u'' * v' = ∏ i, Z' i ^ n' i := by
          rw [hprod n' hn'o hn'a, hn'b, pow_zero, one_mul]
          have : (hunit.unit⁻¹ : (Qh)ˣ).val * zb = 1 := hunit.val_inv_mul
          simp only [u'']
          linear_combination ((hunit.unit⁻¹ : (Qh)ˣ).val) * hrel' +
            (∏ i ∈ (Finset.univ.erase a').erase b', completionMap φ (z i) ^ c.n i) * this
        have hu''span : Ideal.span {u''} = Ideal.span {u'} :=
          Ideal.span_singleton_mul_right_unit (Units.isUnit _) _
        have hspan'' : Ideal.span (insert u'' (insert v' (Set.range Z'))) = maximalIdeal Qh := by
          rw [Ideal.span_insert, hu''span, ← Ideal.span_insert]
          exact hspan'
        have hN'' : ((N.map φ).colon ((I.map φ : Ideal P) : Set P)).map (algebraMap P Qh) =
            Ideal.span {u'', v'} := by
          rw [hN', Ideal.span_insert, Ideal.span_insert, hu''span]
        have hn'pos : ∑ i, n' i ≠ 0 := by
          intro h0
          have hone : u'' * v' = 1 := by
            rw [hrel'']
            exact Finset.prod_eq_one fun i _ ↦ by
              rw [Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ _), pow_zero]
          have hu''m : u'' ∈ maximalIdeal Qh := Ideal.mul_mem_right _ _ hu'm
          exact (mem_maximalIdeal _).mp hu''m (IsUnit.of_mul_eq_one _ hone)
        obtain ⟨c', hc'n, hc'exp⟩ := nodeChart_of_generators hresP _ _ u'' v' Z' n' hn'pos hrel''
          hspan'' hdim hN'' _ (hE' 0 (by simp [hcb0])) (hcoord' 0 (by simp [hcb0]))
        exact ⟨c', hc'n, hc'exp⟩
    all_goals
      let M' : Fin m → Fin m → ℕ := fun l i ↦
        if i = b' then ((if l = a' then 1 else 0) + (if l = b' ∧ cb = 0 then 1 else 0))
        else (if l = i then 1 else 0)
      let M : Fin (m + 1) → Fin m → ℕ := fun j i ↦ Fin.cases 0 (fun l ↦ M' l i) j
      have hxT : ∀ (t : Qh) (i : Fin m), Ideal.span {completionMap φ (z i)} =
          Ideal.span {∏ j, (Fin.cons t Z' : Fin (m + 1) → Qh) j ^ M j i} := by
        intro t i
        rw [Fin.prod_univ_succ]
        simp only [M, Fin.cases_zero, pow_zero, one_mul, Fin.cons_succ, Fin.cases_succ]
        exact hxZ i
      have hcoordT : ∀ (t : Qh) (j : Fin (m + 1)), (∃ β, ∑ i, M j i * c.exp β i ≠ 0) →
          ∃ f : P, Ideal.span {algebraMap P Qh f} = Ideal.span {(Fin.cons t Z' : Fin (m + 1) → Qh) j} := by
        rintro t j ⟨β, hβ⟩
        cases j using Fin.cases with
        | zero => simp [M] at hβ
        | succ l =>
          simp only [Fin.cons_succ]
          exact hcoordZ l ⟨β, hβ⟩
    · refine Or.inr ⟨regChart_of_matrix φ z E c.exp hE _ hmax M (hxT _) (hcoordT _),
        trace_colon_eq_top φ N I u v hN g hIg (hGu ?_)⟩
      rw [hu, Ideal.span_singleton_mul_right_unit (isUnit_of_sub_constQ_mem hbu hbu'), hexc]
    · refine Or.inr ⟨regChart_of_matrix φ z E c.exp hE _ hmax M (hxT _) (hcoordT _),
        trace_colon_eq_top φ N I u v hN g hIg (hGv ?_)⟩
      rw [hv, Ideal.span_singleton_mul_right_unit (isUnit_of_sub_constQ_mem hbv hbv'), hexc]

end Step

section Transport

variable {k O P : Type*} [Field k] [CommRing O] [IsLocalRing O] [CommRing P] [IsLocalRing P]
  [IsNoetherianRing O] [IsNoetherianRing P]

local notation "Rh" => AdicCompletion (maximalIdeal O) O
local notation "Qh" => AdicCompletion (maximalIdeal P) P

omit [IsNoetherianRing O] [IsNoetherianRing P] in
/-- **Node charts transport along isomorphisms** of local rings (the blowup is an isomorphism
away from the centre). -/
theorem NodeChart.transport {ι : Type*} {m : ℕ} {N : Ideal O} {E : ι → Ideal O}
    (c : NodeChart k O m N E) (σ : O ≃+* P) :
    ∃ c' : NodeChart k P m (N.map (σ : O →+* P)) (fun β ↦ (E β).map (σ : O →+* P)),
      c'.n = c.n ∧ c'.exp = c.exp := by
  let Φ := completionEquiv σ
  have hΦ : ∀ x, Φ x = completionMap (σ : O →+* P) x := fun _ ↦ rfl
  refine ⟨⟨c.n, c.pos, c.e.trans Φ, ?_, c.exp, ?_, ?_⟩, rfl, rfl⟩
  · rw [map_map_completion, c.trace_N, Ideal.map_span, Set.image_pair]
    rfl
  · intro β
    rw [map_map_completion, c.trace_E β, Ideal.map_span, Set.image_singleton]
    rfl
  · intro i hi
    obtain ⟨f, hf⟩ := c.coord i hi
    exact ⟨σ f, coord_map (σ : O →+* P) hf⟩

/-- **Regular charts transport along isomorphisms** of local rings. -/
theorem RegChart.transport {ι : Type*} {m : ℕ} {E : ι → Ideal O} (c : RegChart O m E)
    (σ : O ≃+* P) : Nonempty (RegChart P m fun β ↦ (E β).map (σ : O →+* P)) := by
  let Φ := completionEquiv σ
  refine ⟨⟨fun j ↦ Φ (c.T j), ?_, c.exp, ?_, ?_⟩⟩
  · rw [← IsLocalRing.map_ringEquiv_maximalIdeal Φ, ← c.span_eq, Ideal.map_span,
      ← Set.range_comp]
    rfl
  · intro β
    rw [map_map_completion, c.trace_E β, Ideal.map_span, Set.image_singleton, map_prod]
    simp_rw [map_pow]
    rfl
  · obtain ⟨f, hf⟩ := c.rad
    refine ⟨σ f, ?_⟩
    have := coord_map (σ : O →+* P) hf
    rw [map_prod] at this
    simp_rw [map_pow] at this
    exact this

/-- **A node chart with `∑ n_i = 1` is a regular chart**: if `n = e_i` then `U V = Z_i`, and
`U, V, Z_j` (`j ≠ i`) are regular coordinates. -/
theorem NodeChart.regChart_of_single {ι : Type*} {m : ℕ} {N : Ideal O} {E : ι → Ideal O}
    (c : NodeChart k O m N E) (i : Fin m) (hn : c.n = Pi.single i 1) :
    Nonempty (RegChart O m E) := by
  classical
  set eU := c.e (nodeU k c.n)
  set eV := c.e (nodeV k c.n)
  set eZ : Fin m → Rh := fun j ↦ c.e (nodeZ k c.n j)
  have hZi : eZ i = eU * eV := by
    have hnj : ∀ j, c.n j = (Pi.single i 1 : Fin m → ℕ) j := fun j ↦ by rw [hn]
    rw [c.rel, Finset.prod_congr rfl fun j _ ↦ by rw [hnj j],
      Finset.prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp [eZ]
  let T : Fin (m + 1) → Rh := Fin.cons eU (Function.update eZ i eV)
  let src : Fin (m + 1) → Fin m := Fin.cases i (fun l ↦ l)
  let M : Fin (m + 1) → Fin m → ℕ := fun j l ↦ if l = src j then 1 else 0
  have hT0 : T 0 = eU := rfl
  have hTs : ∀ l, T l.succ = Function.update eZ i eV l := fun l ↦ rfl
  have hspan : Ideal.span (Set.range T) = maximalIdeal Rh := by
    rw [← c.span_eq]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      cases j using Fin.cases with
      | zero => exact Ideal.subset_span (Set.mem_insert _ _)
      | succ l =>
        rw [hTs]
        by_cases hl : l = i
        · subst hl; rw [Function.update_self]
          exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        · rw [Function.update_of_ne hl]
          exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨l, rfl⟩))
    · rw [Ideal.span_le]
      have hU : eU ∈ Ideal.span (Set.range T) := Ideal.subset_span ⟨0, rfl⟩
      have hV : eV ∈ Ideal.span (Set.range T) := Ideal.subset_span ⟨i.succ, by
        rw [hTs, Function.update_self]⟩
      rintro x (rfl | rfl | ⟨l, rfl⟩)
      · exact hU
      · exact hV
      · by_cases hl : l = i
        · subst hl
          change eZ l ∈ _
          rw [hZi]
          exact Ideal.mul_mem_right _ _ hU
        · exact Ideal.subset_span ⟨l.succ, by rw [hTs, Function.update_of_ne hl]⟩
  have hx : ∀ l, Ideal.span {eZ l} = Ideal.span {∏ j, T j ^ M j l} := by
    intro l
    rw [Fin.prod_univ_succ]
    by_cases hl : l = i
    · subst hl
      have : ∏ j : Fin m, T j.succ ^ M j.succ l = T l.succ := by
        rw [Finset.prod_eq_single l (fun j _ hj ↦ by simp [M, src, Ne.symm hj]) (by simp)]
        simp [M, src]
      rw [this, hTs, Function.update_self, hT0, hZi]
      simp [M, src]
    · have : ∏ j : Fin m, T j.succ ^ M j.succ l = T l.succ := by
        rw [Finset.prod_eq_single l (fun j _ hj ↦ by simp [M, src, Ne.symm hj]) (by simp)]
        simp [M, src]
      rw [this, hTs, Function.update_of_ne hl]
      simp [M, src, hl]
  have hsum : ∀ (w : Fin m → ℕ) j, ∑ l, M j l * w l = w (src j) := by
    intro w j
    simp [M]
  refine ⟨⟨T, hspan, fun β j ↦ ∑ l, M j l * c.exp β l, fun β ↦ ?_, ?_⟩⟩
  · rw [c.trace_E' β]
    exact span_prod_pow_eq _ T M hx (c.exp β)
  · obtain ⟨f, hf⟩ := rad_of_coord (algebraMap O Rh) c.exp c.coord
    refine ⟨f, ?_⟩
    rw [hf]
    change Ideal.span {∏ l, eZ l ^ boundaryExp c.exp l} = _
    rw [span_prod_pow_eq _ T M hx (boundaryExp c.exp)]
    congr 2
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [hsum]
    congr 1
    simp only [boundaryExp, hsum]

end Transport

section Centres

variable {k O : Type*} [Field k] [CommRing O] [IsLocalRing O] [IsNoetherianRing O]

local notation "Rh" => AdicCompletion (maximalIdeal O) O

/-- Extension along a ring isomorphism commutes with colon ideals. -/
theorem map_colon_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (I J : Ideal A) : (I.colon (J : Set A)).map e = (I.map e).colon ((J.map e : Ideal B) : Set B) := by
  ext y
  rw [Ideal.mem_map_of_equiv, Submodule.mem_colon]
  constructor
  · rintro ⟨x, hx, rfl⟩ z hz
    rw [SetLike.mem_coe, Ideal.mem_map_of_equiv] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (by simpa using Submodule.mem_colon.mp hx w hw)
  · intro h
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Submodule.mem_colon]
    intro w hw
    have := h (e w) (Ideal.mem_map_of_mem _ hw)
    rw [smul_eq_mul, Ideal.mem_map_of_equiv] at this
    obtain ⟨x, hx, hxe⟩ := this
    have : e.symm y * w = x := by
      apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply, hxe]
    rw [smul_eq_mul, this]
    exact hx

/-- The completion of a Noetherian local ring is flat. -/
theorem flat_completion : Module.Flat O Rh := by
  have : Module.FaithfullyFlat O Rh := faithfullyFlat O
  infer_instance

/-- **Traces of iterated colons by a boundary ideal** in a node chart:
`(N : E_α^j) Ô = (U, V, Z^{n - j exp_α})`. -/
theorem NodeChart.trace_iterColon {ι : Type*} {m : ℕ} {N : Ideal O} {E : ι → Ideal O}
    (c : NodeChart k O m N E) (α : ι) (j : ℕ) :
    ((fun J : Ideal O ↦ J.colon ((E α : Ideal O) : Set O))^[j] N).map (algebraMap O Rh) =
      (nIdeal k c.n (c.n - j • c.exp α)).map c.e := by
  have := flat_completion (O := O)
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply, c.trace_N, show c.n - 0 • c.exp α = c.n from
      funext fun i ↦ by simp, nIdeal_self, Ideal.map_span, Set.image_pair]
  | succ j ih =>
    rw [Function.iterate_succ_apply', map_colon_of_flat _ _ (Ideal.fg_of_isNoetherianRing _), ih,
      c.trace_E α, show Ideal.span {c.e (nodeZMon k c.n (c.exp α))} =
        (Ideal.span {nodeZMon k c.n (c.exp α)}).map c.e by
          rw [Ideal.map_span, Set.image_singleton], ← map_colon_ringEquiv, Ideal.colon_span,
      nIdeal_colon_nodeZMon k c.n (c.n - j • c.exp α) (c.exp α) (fun i ↦ Nat.sub_le _ _)]
    congr 2
    funext i
    simp only [Pi.sub_apply, succ_nsmul, Pi.add_apply]
    omega

/-- **Traces of the centres** `(N : E_α^{N₀ - 1}) : (N : E_α^{N₀})` in a node chart. -/
theorem NodeChart.trace_centre {ι : Type*} {m : ℕ} {N : Ideal O} {E : ι → Ideal O}
    (c : NodeChart k O m N E) (α : ι) (N₀ : ℕ) :
    (((fun J : Ideal O ↦ J.colon ((E α : Ideal O) : Set O))^[N₀ - 1] N).colon
      ((((fun J : Ideal O ↦ J.colon ((E α : Ideal O) : Set O))^[N₀] N : Ideal O)) : Set O)).map
        (algebraMap O Rh) =
      (nIdeal k c.n ((c.n - (N₀ - 1) • c.exp α) - (c.n - N₀ • c.exp α))).map c.e := by
  have := flat_completion (O := O)
  rw [map_colon_of_flat _ _ (Ideal.fg_of_isNoetherianRing _), c.trace_iterColon, c.trace_iterColon,
    ← map_colon_ringEquiv, nIdeal_colon_nIdeal k c.n (c.n - (N₀ - 1) • c.exp α)
      (c.n - N₀ • c.exp α) (fun i ↦ Nat.sub_le _ _)]

end Centres

end DeJongAlterations.StableModification.Resolution.Global

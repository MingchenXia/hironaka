import DeJongAlterations.StableModification.Resolution.GlobalBlowup

/-!
# The two stages of the resolution of a nodal curve

Let `X` be an integral projective scheme of finite type over `k = k̄`, of dimension `m + 1`, with
a singular-locus ideal sheaf `N` and a finite family of boundary ideal sheaves `E β`, and suppose
that every closed point has a formal chart (`GoodAt`). The resolution (de Jong 1996, 3.4 and
4.27, `references/dejong96-alterations/tex/page-0014.tex`–`page-0015.tex`, `page-0026.tex`–
`page-0027.tex`; blueprint `def:sm-dj-global-centres`, `lem:sm-dj-centre-traces`,
`prop:sm-dj-stage-one`, `prop:sm-dj-stage-two`, `thm:sm-dj-nc-resolution`) proceeds by blowups
along the reduced supports of the **centres**

* stage one: `centreIdeal N (E α) (L + 1) = (N : E_α^L) : (N : E_α^{L+1})`, whose trace at a node
  chart is `(U, V, Z_i)` exactly where `exp α = e_i` and `n_i ≥ L + 1` (`centreExp_single`,
  `NodeChart.trace_centre`), and `(1)` elsewhere; blowing it up lowers the exponent of `α` by `2`
  (`stage1_step`, `stage1_member`, `stage1_list`, invariant `Stage1Inv`);
* stage two: `centreIdeal N (E α) 1 ⊔ centreIdeal N (E β) 1`, whose trace is the crossing ideal
  `(U, V, Z_i, Z_j)` exactly where `α` and `β` are both active (`stage2_centreExp`,
  `nIdeal_single_sup`); blowing it up separates them (`stage2_step`, `stage2_list`, invariant
  `Stage2Inv`).

The centres are defined globally by colon ideals, so no constancy of the exponent `n_T` along a
component `T` of the singular locus is needed (cf. de Jong 3.4, where this constancy is asserted
without proof). Every centre contains `N`, hence is a proper closed subset
(`support_ne_top_of_goodAt`, using `nodeU_ne_zero`). The reduced structure of a centre has the
same prime trace (`map_radical_eq_of_isPrime`).

At the end of stage two every node chart has a single active coordinate, `U V = Z_i`
(`Stage2Inv.eq_single`), hence is a regular chart (`NodeChart.regChart_of_single`):
`exists_regChart_modification` gives an integral projective modification with a formal regular
chart at every closed point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing MvPowerSeries

namespace DeJongAlterations.StableModification.Resolution.Global

set_option backward.isDefEq.respectTransparency false

open Strictify Algebra.NodeFittingIdealSheaf Geometry.BlowupGluing
open Algebra.CompletionRegularityBasics

universe u

section Algebra

variable (k : Type*) [Field k] {m : ℕ} (n : Fin m → ℕ)

/-- The node coordinate `U` is non-zero (`∑ n_i ≥ 1`): setting `V` and all `Z_i` to zero kills
the node equation but not `U`. -/
theorem nodeU_ne_zero (hn : ∑ i, n i ≠ 0) : nodeU k n ≠ 0 := by
  classical
  intro h
  obtain ⟨G, hG⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let S : Finset (Fin (m + 2)) := insert 1 (Finset.univ.image fun i : Fin m ↦ i.succ.succ)
  have hT0 : truncate S (X 0 : MvPowerSeries (Fin (m + 2)) k) = X 0 := by
    rw [X, truncate_monomial]
    intro i hi
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hi
    rcases hi with rfl | ⟨j, rfl⟩
    · simp
    · simp
  have hTF : truncate S (nodeSeries k n) = 0 := by
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    rw [nodeSeries_eq, map_sub, map_mul, map_prod,
      truncate_X_of_mem S (i := 1) (by simp [S]), mul_zero, zero_sub, neg_eq_zero]
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [map_pow, truncate_X_of_mem S (i := j.succ.succ) (by simp [S]), zero_pow hj]
  have := congrArg (truncate S) hG
  rw [map_mul, hTF, mul_zero, hT0] at this
  have hcoeff := congrArg (coeff (Finsupp.single 0 1)) this
  rw [coeff_X, if_pos rfl, map_zero] at hcoeff
  exact one_ne_zero hcoeff.symm

end Algebra

section Centres

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The **centre ideal** `(N : K^{L-1}) : (N : K^L)` (blueprint `def:sm-dj-global-centres`). -/
def centreIdeal (N K : X.IdealSheafData) (L : ℕ) : X.IdealSheafData :=
  colonIdealSheaf (colonIter N K (L - 1)) (colonIter N K L)

theorem stalkIdeal_centreIdeal (N K : X.IdealSheafData) (L : ℕ) (x : X) :
    stalkIdeal (centreIdeal N K L) x =
      ((fun J : Ideal (X.presheaf.stalk x) ↦ J.colon ((stalkIdeal K x : Ideal _) : Set _))^[L - 1]
        (stalkIdeal N x)).colon
      ((((fun J : Ideal (X.presheaf.stalk x) ↦ J.colon ((stalkIdeal K x : Ideal _) : Set _))^[L]
        (stalkIdeal N x) : Ideal _)) : Set _) := by
  rw [centreIdeal, stalkIdeal_colonIdealSheaf, stalkIdeal_colonIter, stalkIdeal_colonIter]

theorem le_centreIdeal (N K : X.IdealSheafData) (L : ℕ) : N ≤ centreIdeal N K L :=
  (le_colonIter N K (L - 1)).trans (le_colonIdealSheaf _ _)

omit [IsLocallyNoetherian X] in
/-- The vanishing ideal of the support of `J` has radical stalks. -/
theorem localIdeal_support (J : X.IdealSheafData) (x : X) :
    localIdeal J.support x = (stalkIdeal J x).radical := by
  rw [localIdeal, Scheme.IdealSheafData.vanishingIdeal_support, stalkIdeal_radical]

omit [IsLocallyNoetherian X] in
/-- A point lies in the support of `J` iff the stalk of `J` is proper. -/
theorem mem_support_iff_stalkIdeal_ne_top (J : X.IdealSheafData) (x : X) :
    x ∈ J.support ↔ stalkIdeal J x ≠ ⊤ := by
  rw [Algebra.NodeFittingGeometricNodeSupport.mem_support_iff_stalkIdeal_le_maximalIdeal]
  exact ⟨fun h htop ↦ (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ h)),
    fun h ↦ le_maximalIdeal h⟩

omit [IsLocallyNoetherian X] in
theorem stalkIdeal_bot (x : X) : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU, Scheme.IdealSheafData.ideal_bot]
  exact Ideal.map_bot

end Centres

section Traces

variable {k O : Type*} [Field k] [CommRing O] [IsLocalRing O] [IsNoetherianRing O]

local notation "Rh" => AdicCompletion (maximalIdeal O) O

/-- An ideal with trivial trace on the completion is trivial (faithful flatness). -/
theorem eq_top_of_map_eq_top {J : Ideal O} (h : J.map (algebraMap O Rh) = ⊤) : J = ⊤ := by
  rw [← comap_map O J, h, Ideal.comap_top]

omit [IsNoetherianRing O] in
/-- **The radical trick**: if the trace of `J` is a prime ideal, the radical of `J` has the same
trace. -/
theorem map_radical_eq_of_isPrime {J : Ideal O} (h : (J.map (algebraMap O Rh)).IsPrime) :
    J.radical.map (algebraMap O Rh) = J.map (algebraMap O Rh) :=
  map_radical_eq_of_isRadical _ J h.isRadical

theorem centreExp_zero {m : ℕ} (n : Fin m → ℕ) (L : ℕ) :
    (n - L • (0 : Fin m → ℕ)) - (n - (L + 1) • (0 : Fin m → ℕ)) = 0 := by
  funext j; simp

theorem centreExp_single {m : ℕ} (n : Fin m → ℕ) (L : ℕ) (i : Fin m) :
    (n - L • Pi.single i 1) - (n - (L + 1) • Pi.single i 1) =
      if L + 1 ≤ n i then Pi.single i 1 else 0 := by
  funext j
  by_cases hj : j = i
  · subst hj
    split_ifs with h
    · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      omega
    · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Pi.zero_apply]
      omega
  · split_ifs <;> simp [hj]

/-- `nodeZMon (e_i) = Z_i`. -/
theorem nodeZMon_single {m : ℕ} (n : Fin m → ℕ) (i : Fin m) :
    nodeZMon k n (Pi.single i 1) = nodeZ k n i := by
  rw [nodeZMon_eq_prod, Finset.prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

end Traces

section Stage1

variable {ι : Type*} {m : ℕ}

/-- **The stage-one invariant** (blueprint `prop:sm-dj-stage-one`): every boundary exponent is a
single coordinate or zero, distinct boundary members have distinct coordinates, every coordinate
of the node equation belongs to a boundary member, all exponents are at most `B`, the members of
`S` have exponent at most `1`, and the member `α` has exponent at most `L`. -/
def Stage1Inv (B : ℕ) (S : Set ι) (α : ι) (L : ℕ) (n : Fin m → ℕ) (exp : ι → Fin m → ℕ) :
    Prop :=
  (∀ β, exp β = 0 ∨ ∃ i, exp β = Pi.single i 1) ∧
  (∀ β β' i, exp β = Pi.single i 1 → exp β' = Pi.single i 1 → β = β') ∧
  (∀ i, n i ≠ 0 → ∃ β, exp β = Pi.single i 1) ∧
  (∀ i, n i ≤ B) ∧
  (∀ β ∈ S, ∀ i, exp β = Pi.single i 1 → n i ≤ 1) ∧
  (∀ i, exp α = Pi.single i 1 → n i ≤ L)

theorem Stage1Inv.step {B : ℕ} {S : Set ι} {α : ι} {L : ℕ} {n : Fin m → ℕ}
    {exp : ι → Fin m → ℕ} (h : Stage1Inv B S α (L + 1) n exp) {i : Fin m}
    (hi : exp α = Pi.single i 1) (hni : L + 1 ≤ n i) :
    Stage1Inv B S α L (Function.update n i (n i - 2)) exp := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, fun j hj ↦ ?_, fun j ↦ ?_, fun β hβ j hj ↦ ?_, fun j hj ↦ ?_⟩
  · by_cases hji : j = i
    · subst hji; exact ⟨α, hi⟩
    · rw [Function.update_of_ne hji] at hj; exact h3 j hj
  · by_cases hji : j = i
    · subst hji; rw [Function.update_self]; exact (Nat.sub_le _ _).trans (h4 _)
    · rw [Function.update_of_ne hji]; exact h4 j
  · by_cases hji : j = i
    · subst hji
      have := h5 β hβ j hj
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hji]; exact h5 β hβ j hj
  · have hji : j = i := by
      rw [hi] at hj
      by_contra hne
      have := congrFun hj i
      simp [Ne.symm hne] at this
    subst hji
    rw [Function.update_self]
    have := h6 j hi
    omega

theorem Stage1Inv.mono {B : ℕ} {S : Set ι} {α : ι} {L : ℕ} {n : Fin m → ℕ}
    {exp : ι → Fin m → ℕ} (h : Stage1Inv B S α (L + 1) n exp)
    (hle : ∀ i, exp α = Pi.single i 1 → n i ≤ L) : Stage1Inv B S α L n exp :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hle⟩

end Stage1

section SchemeStage

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] {ι : Type*}

omit [IsAlgClosed k] in
/-- **Centres containing the singular-locus ideal are proper**: if `X` has charts at its closed
points, an ideal sheaf containing `N` has support `≠ X`. -/
theorem support_ne_top_of_goodAt (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] {m : ℕ}
    (N : X.IdealSheafData) (E : ι → X.IdealSheafData) (Q : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop)
    (hgood : ∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E Q x) (J : X.IdealSheafData)
    (hJ : N ≤ J) : J.support ≠ ⊤ := by
  intro htop
  have hN : N.support = ⊤ := top_unique (htop ▸ Scheme.IdealSheafData.support_antitone hJ)
  have hNbot : N = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp hN
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
    isClosed_univ.isLocallyClosed
  have hNx0 : stalkIdeal N x = ⊥ := by rw [hNbot, stalkIdeal_bot]
  rcases hgood x hx with ⟨c, -⟩ | ⟨-, hNx⟩
  · have h0 : Ideal.span {c.e (nodeU k c.n), c.e (nodeV k c.n)} = ⊥ := by
      rw [← c.trace_N, hNx0, Ideal.map_bot]
    have hU : c.e (nodeU k c.n) = 0 := by
      have : c.e (nodeU k c.n) ∈ (⊥ : Ideal (X.completedLocalRing x)) :=
        h0 ▸ Ideal.subset_span (Set.mem_insert _ _)
      exact this
    exact nodeU_ne_zero k c.n c.pos (c.e.injective (hU.trans (map_zero _).symm))
  · rw [hNx0] at hNx
    exact bot_ne_top hNx

/-- **One stage-one blowup** (de Jong 3.4; blueprint `prop:sm-dj-stage-one`). If all closed
points of `X` have charts with the stage-one invariant for the bound `L + 1` on the member `α`
(`L ≥ 1`), then blowing up the reduced support of the centre `(N : E_α^L) : (N : E_α^{L+1})`
gives a projective modification with charts with the invariant for the bound `L`. -/
theorem stage1_step (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (hp : IsProjectiveOver p)
    {m : ℕ} (hdim : topologicalKrullDim X = (m + 1 : ℕ)) (N : X.IdealSheafData)
    (E : ι → X.IdealSheafData) (B : ℕ) (S : Set ι) (α : ι) (L : ℕ) (hL : 1 ≤ L)
    (h : ∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E (Stage1Inv B S α (L + 1)) x) :
    ∃ (X' : Scheme.{u}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (π : X' ⟶ X)
      (N' : X'.IdealSheafData), IsModification π ∧ IsProjectiveOver (π ≫ p) ∧
      ∀ y : X', IsClosed ({y} : Set X') →
        GoodAt k m N' (fun β ↦ (E β).comap π) (Stage1Inv B S α L) y := by
  classical
  set 𝒲 := centreIdeal N (E α) (L + 1)
  have hW : 𝒲.support ≠ ⊤ :=
    support_ne_top_of_goodAt p N E _ h 𝒲 (le_centreIdeal N (E α) (L + 1))
  -- the trace of the centre at a node chart
  have htrace : ∀ x : X, ∀ c : NodeChart k (X.presheaf.stalk x) m (stalkIdeal N x)
      (fun β ↦ stalkIdeal (E β) x),
      (stalkIdeal 𝒲 x).map (algebraMap _ (X.completedLocalRing x)) =
        (nIdeal k c.n ((c.n - L • c.exp α) - (c.n - (L + 1) • c.exp α))).map c.e := by
    intro x c
    rw [stalkIdeal_centreIdeal]
    exact c.trace_centre α (L + 1)
  have hNle : ∀ x : X, stalkIdeal N x ≤ stalkIdeal 𝒲 x := by
    intro x
    obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
    rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ _ U hxU]
    exact Ideal.map_mono (le_centreIdeal N (E α) (L + 1) U)
  -- membership in the centre
  have hmem : ∀ x : X, ∀ c : NodeChart k (X.presheaf.stalk x) m (stalkIdeal N x)
      (fun β ↦ stalkIdeal (E β) x), Stage1Inv B S α (L + 1) c.n c.exp →
      (x ∈ 𝒲.support ↔ ∃ i, c.exp α = Pi.single i 1 ∧ L + 1 ≤ c.n i) := by
    intro x c hc
    rw [mem_support_iff_stalkIdeal_ne_top]
    constructor
    · intro hne
      by_contra hno
      push Not at hno
      apply hne
      apply eq_top_of_map_eq_top
      rw [htrace x c]
      rcases hc.1 α with h0 | ⟨i, hi⟩
      · rw [h0, centreExp_zero, nIdeal_zero, Ideal.map_top]
      · rw [hi, centreExp_single, if_neg (by have := hno i hi; omega), nIdeal_zero,
          Ideal.map_top]
    · rintro ⟨i, hi, hni⟩ htop
      have hprime : (nIdeal k c.n (Pi.single i 1)).IsPrime :=
        isPrime_nIdeal_single k c.n i (by omega)
      have : ((nIdeal k c.n (Pi.single i 1)).map c.e).IsPrime := inferInstance
      apply this.ne_top
      rw [← centreExp_single c.n L i |>.trans (if_pos hni), ← hi, ← htrace x c, htop,
        Ideal.map_top]
  refine exists_blowup_goodAt p hp N E 𝒲.support hW
    (Stage1Inv B S α L) (goodAt_blowup_branch p hdim N E 𝒲.support hW _ ?_ ?_)
  · intro x hx hxW
    rcases h x hx with ⟨c, hc⟩ | ⟨-, hN⟩
    · obtain ⟨i, hi, hni⟩ := (hmem x c hc).mp hxW
      refine ⟨c, i, by omega, ?_, hc.step hi hni⟩
      rw [localIdeal_support, map_radical_eq_of_isPrime, htrace x c, hi, centreExp_single,
        if_pos hni, nIdeal, Ideal.map_span, nodeZMon_single]
      · simp only [Set.image_insert_eq, Set.image_singleton]
      · rw [htrace x c, hi, centreExp_single, if_pos hni]
        have := isPrime_nIdeal_single k c.n i (by omega)
        infer_instance
    · exfalso
      rw [mem_support_iff_stalkIdeal_ne_top] at hxW
      exact hxW (top_unique (hN ▸ hNle x))
  · intro x hx hxW
    rcases h x hx with ⟨c, hc⟩ | ⟨hr, hN⟩
    · refine Or.inl ⟨c, hc.mono fun i hi ↦ ?_⟩
      by_contra hni
      exact hxW ((hmem x c hc).mpr ⟨i, hi, by omega⟩)
    · exact Or.inr ⟨hr, hN⟩

end SchemeStage

section Reach

variable {k : Type u} [Field k] {ι : Type*}

variable (k) in
/-- `Reach p m E Q`: there is an integral projective modification `π : X' → X` and a singular-locus
ideal sheaf on `X'` such that all closed points of `X'` have `Q`-charts for the pulled back
boundary ideals. -/
def Reach {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (m : ℕ) (E : ι → X.IdealSheafData)
    (Q : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop) : Prop :=
  ∃ (X' : Scheme.{u}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (π : X' ⟶ X)
    (N' : X'.IdealSheafData), IsModification π ∧ IsProjectiveOver (π ≫ p) ∧
    ∀ y : X', IsClosed ({y} : Set X') → GoodAt k m N' (fun β ↦ (E β).comap π) Q y

/-- A scheme with `Q`-charts reaches `Q` (by the identity). -/
theorem reach_refl {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveOver p) {m : ℕ} (N : X.IdealSheafData)
    (E : ι → X.IdealSheafData) (Q : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop)
    (h : ∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E Q x) : Reach k p m E Q := by
  refine ⟨X, inferInstance, inferInstance, 𝟙 X, N, inferInstance, by simpa using hp, ?_⟩
  simp only [Scheme.IdealSheafData.comap_id]
  exact h

/-- **Chaining modifications.** -/
theorem reach_trans {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) {m : ℕ} (E : ι → X.IdealSheafData)
    (Q₁ Q₂ : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop) (h₁ : Reach k p m E Q₁)
    (h₂ : ∀ (X₁ : Scheme.{u}) [IsIntegral X₁] [IsLocallyNoetherian X₁] (π₁ : X₁ ⟶ X)
      (N₁ : X₁.IdealSheafData), IsModification π₁ → IsProjectiveOver (π₁ ≫ p) →
      (∀ y : X₁, IsClosed ({y} : Set X₁) → GoodAt k m N₁ (fun β ↦ (E β).comap π₁) Q₁ y) →
      Reach k (π₁ ≫ p) m (fun β ↦ (E β).comap π₁) Q₂) :
    Reach k p m E Q₂ := by
  obtain ⟨X₁, i₁, l₁, π₁, N₁, hmod₁, hp₁, hg₁⟩ := h₁
  obtain ⟨X₂, i₂, l₂, π₂, N₂, hmod₂, hp₂, hg₂⟩ := h₂ X₁ π₁ N₁ hmod₁ hp₁ hg₁
  refine ⟨X₂, i₂, l₂, π₂ ≫ π₁, N₂, IsModification.comp π₂ π₁, by rwa [Category.assoc], ?_⟩
  simp only [Scheme.IdealSheafData.comap_comp]
  exact hg₂

omit [Field k] in
theorem GoodAt.mono {X : Scheme.{u}} [IsLocallyNoetherian X] [Field k] {m : ℕ}
    {N : X.IdealSheafData} {E : ι → X.IdealSheafData}
    {Q Q' : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop} (hQ : ∀ n exp, Q n exp → Q' n exp) {x : X}
    (h : GoodAt k m N E Q x) : GoodAt k m N E Q' x := by
  rcases h with ⟨c, hc⟩ | h
  · exact Or.inl ⟨c, hQ _ _ hc⟩
  · exact Or.inr h

theorem Reach.mono {X : Scheme.{u}} {p : X ⟶ Spec (.of k)} {m : ℕ} {E : ι → X.IdealSheafData}
    {Q Q' : (Fin m → ℕ) → (ι → Fin m → ℕ) → Prop} (hQ : ∀ n exp, Q n exp → Q' n exp)
    (h : Reach k p m E Q) : Reach k p m E Q' := by
  obtain ⟨X', i, l, π, N', hmod, hp, hg⟩ := h
  exact ⟨X', i, l, π, N', hmod, hp, fun y hy ↦ (hg y hy).mono hQ⟩

end Reach

section Stage1Iteration

variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type*}

/-- **Stage one for one boundary member** (de Jong 3.4): repeated blowups of the centres lower the
exponent of the member `α` to at most `1`. -/
theorem stage1_member {m : ℕ} (B : ℕ) (S : Set ι) (α : ι) :
    ∀ (L : ℕ) {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k))
      [LocallyOfFiniteType p], IsProjectiveOver p → topologicalKrullDim X = (m + 1 : ℕ) →
      ∀ (N : X.IdealSheafData) (E : ι → X.IdealSheafData), 1 ≤ L →
      (∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E (Stage1Inv B S α L) x) →
      Reach k p m E (Stage1Inv B S α 1) := by
  intro L
  induction L with
  | zero => intro X _ _ p _ _ _ N E hL; omega
  | succ L ih =>
    intro X _ _ p _ hp hdim N E _ h
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · exact reach_refl p hp N E _ h
    · refine reach_trans p E _ _ (stage1_step p hp hdim N E B S α L hL h) ?_
      intro X₁ _ _ π₁ N₁ hmod₁ hp₁ hg₁
      have : IsProper (π₁ ≫ p) := hp₁.isProper
      have : IsModification π₁ := hmod₁
      exact ih (π₁ ≫ p) hp₁ (by rw [DeJong.topologicalKrullDim_eq_of_isModification p π₁, hdim])
        N₁ _ hL hg₁

/-- **Stage one** (de Jong 3.4; blueprint `prop:sm-dj-stage-one`): processing the boundary members
of a list one after the other lowers all their exponents to at most `1`. -/
theorem stage1_list {m : ℕ} (B : ℕ) (α₀ : ι) :
    ∀ (l : List ι) (S : Set ι) {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p], IsProjectiveOver p →
      topologicalKrullDim X = (m + 1 : ℕ) →
      ∀ (N : X.IdealSheafData) (E : ι → X.IdealSheafData),
      (∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E (Stage1Inv B S α₀ (B + 1)) x) →
      Reach k p m E (Stage1Inv B (S ∪ {β | β ∈ l}) α₀ (B + 1)) := by
  intro l
  induction l with
  | nil =>
    intro S X _ _ p _ hp hdim N E h
    exact (reach_refl p hp N E _ h).mono fun n exp hne ↦ by simpa using hne
  | cons α l ih =>
    intro S X _ _ p _ hp hdim N E h
    have h' : ∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E (Stage1Inv B S α (B + 1)) x :=
      fun x hx ↦ (h x hx).mono fun n exp hne ↦
        ⟨hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1,
          fun i _ ↦ (hne.2.2.2.1 i).trans (Nat.le_succ B)⟩
    refine reach_trans p E _ _ (stage1_member B S α (B + 1) p hp hdim N E (by omega) h') ?_
    intro X₁ _ _ π₁ N₁ hmod₁ hp₁ hg₁
    have : IsProper (π₁ ≫ p) := hp₁.isProper
    have : IsModification π₁ := hmod₁
    have hdim₁ : topologicalKrullDim X₁ = (m + 1 : ℕ) := by
      rw [DeJong.topologicalKrullDim_eq_of_isModification p π₁, hdim]
    have := ih (insert α S) (π₁ ≫ p) hp₁ hdim₁ N₁ _ fun y hy ↦ (hg₁ y hy).mono
      fun n exp hne ↦ ⟨hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, fun β hβ ↦ by
        rcases hβ with rfl | hβ
        · exact hne.2.2.2.2.2
        · exact hne.2.2.2.2.1 β hβ, fun i _ ↦ (hne.2.2.2.1 i).trans (Nat.le_succ B)⟩
    have hset : S ∪ {β | β ∈ α :: l} = insert α S ∪ {β | β ∈ l} := by
      ext β
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, Set.mem_insert_iff]
      tauto
    rw [hset]
    exact this

end Stage1Iteration

section Stage2

variable {ι : Type*} {m : ℕ}

/-- **The stage-two invariant** (blueprint `prop:sm-dj-stage-two`): all exponents are at most `1`;
every active coordinate (`n_i = 1`) occurs in a boundary monomial; every boundary member has at
most one active coordinate and every active coordinate belongs to at most one member; and no
point has both members of a processed pair active. -/
def Stage2Inv (P : Set (ι × ι)) (n : Fin m → ℕ) (exp : ι → Fin m → ℕ) : Prop :=
  (∀ i, n i ≤ 1) ∧
  (∀ i, n i = 1 → ∃ β, exp β i ≠ 0) ∧
  (∀ β i j, n i = 1 → n j = 1 → exp β i ≠ 0 → exp β j ≠ 0 → i = j) ∧
  (∀ i β β', n i = 1 → exp β i ≠ 0 → exp β' i ≠ 0 → β = β') ∧
  (∀ q ∈ P, ¬ ∃ i j, n i = 1 ∧ n j = 1 ∧ exp q.1 i ≠ 0 ∧ exp q.2 j ≠ 0)

/-- The end of stage one gives the stage-two invariant. -/
theorem stage2Inv_of_stage1Inv {B : ℕ} {α : ι} {L : ℕ} {n : Fin m → ℕ} {exp : ι → Fin m → ℕ}
    (h : Stage1Inv B Set.univ α L n exp) : Stage2Inv ∅ n exp := by
  classical
  obtain ⟨h1, h2, h3, -, h5, -⟩ := h
  have hsingle : ∀ β i, exp β i ≠ 0 → exp β = Pi.single i 1 := by
    intro β i hi
    rcases h1 β with h0 | ⟨j, hj⟩
    · simp [h0] at hi
    · have : j = i := by
        by_contra hne
        rw [hj] at hi
        simp [Ne.symm hne] at hi
      rw [hj, this]
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, fun β i j _ _ hi hj ↦ ?_, fun i β β' _ hi hi' ↦ ?_,
    fun q hq ↦ absurd hq (Set.notMem_empty q)⟩
  · by_cases hn : n i = 0
    · omega
    · obtain ⟨β, hβ⟩ := h3 i hn
      exact h5 β (Set.mem_univ β) i hβ
  · obtain ⟨β, hβ⟩ := h3 i (by omega)
    exact ⟨β, by simp [hβ]⟩
  · have h1' := hsingle β i hi
    have h2' := hsingle β j hj
    rw [h1'] at h2'
    by_contra hne
    have := congrFun h2' i
    simp [hne] at this
  · exact h2 β β' i (hsingle β i hi) (hsingle β' i hi')

/-- **The stage-two invariant is preserved by the crossing transform.** -/
theorem Stage2Inv.cross {P : Set (ι × ι)} {n : Fin m → ℕ} {exp : ι → Fin m → ℕ}
    (h : Stage2Inv P n exp) {α β : ι} {a b : Fin m} (hab : a ≠ b) (hna : n a = 1)
    (hnb : n b = 1) (hαa : exp α a ≠ 0) (hβb : exp β b ≠ 0) {a' b' : Fin m}
    (hab' : (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) {δ : ℕ} (hδ : δ ≤ 1) :
    Stage2Inv (insert (α, β) P) (Function.update (Function.update n a' 0) b' δ)
      (fun γ ↦ Function.update (Function.update (exp γ) a' (exp γ a' + exp γ b')) b'
        (δ * exp γ b')) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have ha'b' : a' ≠ b' := by rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hab; exact hab.symm]
  set n' := Function.update (Function.update n a' 0) b' δ
  set exp' : ι → Fin m → ℕ := fun γ ↦ Function.update (Function.update (exp γ) a'
    (exp γ a' + exp γ b')) b' (δ * exp γ b')
  -- active coordinates of `n'` are active for `n`, and `exp'` agrees with `exp` there
  have hact : ∀ i, n' i = 1 → n i = 1 ∧ ∀ γ, exp' γ i ≠ 0 ↔ exp γ i ≠ 0 := by
    intro i hi
    by_cases hib : i = b'
    · subst hib
      simp only [n', Function.update_self] at hi
      subst hi
      refine ⟨by rcases hab' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption, fun γ ↦ ?_⟩
      simp [exp']
    · by_cases hia : i = a'
      · subst hia
        simp [n', Function.update_of_ne hib] at hi
      · simp only [n', Function.update_of_ne hib, Function.update_of_ne hia] at hi
        refine ⟨hi, fun γ ↦ ?_⟩
        simp [exp', Function.update_of_ne hib, Function.update_of_ne hia]
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, fun γ i j hi hj hγi hγj ↦ ?_, fun i γ γ' hi hγ hγ' ↦ ?_,
    fun q hq ↦ ?_⟩
  · by_cases hib : i = b'
    · subst hib; simp [n', hδ]
    · by_cases hia : i = a'
      · subst hia; simp [n', Function.update_of_ne hib]
      · simp only [n', Function.update_of_ne hib, Function.update_of_ne hia]; exact h1 i
  · obtain ⟨hni, hiff⟩ := hact i hi
    obtain ⟨γ, hγ⟩ := h2 i hni
    exact ⟨γ, (hiff γ).mpr hγ⟩
  · obtain ⟨hni, hiffi⟩ := hact i hi
    obtain ⟨hnj, hiffj⟩ := hact j hj
    exact h3 γ i j hni hnj ((hiffi γ).mp hγi) ((hiffj γ).mp hγj)
  · obtain ⟨hni, hiff⟩ := hact i hi
    exact h4 i γ γ' hni ((hiff γ).mp hγ) ((hiff γ').mp hγ')
  · rintro ⟨i, j, hi, hj, hqi, hqj⟩
    obtain ⟨hni, hiffi⟩ := hact i hi
    obtain ⟨hnj, hiffj⟩ := hact j hj
    rcases hq with rfl | hq
    · -- the processed pair `(α, β)`
      have hia : i = a := h3 α i a hni hna ((hiffi α).mp hqi) hαa
      have hjb : j = b := h3 β j b hnj hnb ((hiffj β).mp hqj) hβb
      subst hia hjb
      -- both `a` and `b` active for `n'` is impossible
      have hpos : ∀ c, (c = a' ∨ c = b') → n' c = 1 → c = b' := by
        rintro c (rfl | rfl) hc
        · simp [n', Function.update_of_ne ha'b'] at hc
        · rfl
      have ha_mem : i = a' ∨ i = b' := by rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      have hb_mem : j = a' ∨ j = b' := by rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      exact hab ((hpos i ha_mem hi).trans (hpos j hb_mem hj).symm)
    · exact h5 q hq ⟨i, j, hni, hnj, (hiffi q.1).mp hqi, (hiffj q.2).mp hqj⟩

/-- At the end of stage two, a node chart has a single active coordinate. -/
theorem Stage2Inv.eq_single {n : Fin m → ℕ} {exp : ι → Fin m → ℕ}
    (h : Stage2Inv {q : ι × ι | q.1 ≠ q.2} n exp) (hn : ∑ i, n i ≠ 0) :
    ∃ i, n = Pi.single i 1 := by
  classical
  obtain ⟨h1, h2, h3, -, h5⟩ := h
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hni : n i = 1 := by have := h1 i; omega
  refine ⟨i, funext fun j ↦ ?_⟩
  by_cases hji : j = i
  · subst hji; simp [hni]
  · rw [Pi.single_apply, if_neg hji]
    by_contra hnj
    have hnj1 : n j = 1 := by have := h1 j; omega
    obtain ⟨γ, hγ⟩ := h2 i hni
    obtain ⟨γ', hγ'⟩ := h2 j hnj1
    by_cases hγγ : γ = γ'
    · subst hγγ
      exact hji (h3 γ j i hnj1 hni hγ' hγ)
    · exact h5 (γ, γ') hγγ ⟨i, j, hni, hnj1, hγ, hγ'⟩

/-- The stage-two centre exponent: `n - (n - e) = min(n, e)` picks the active coordinates. -/
theorem stage2_centreExp {P : Set (ι × ι)} {n : Fin m → ℕ} {exp : ι → Fin m → ℕ}
    (h : Stage2Inv P n exp) (γ : ι) :
    ((n - (1 - 1) • exp γ) - (n - 1 • exp γ) = 0 ∧ ¬ ∃ i, n i = 1 ∧ exp γ i ≠ 0) ∨
    ∃ i, n i = 1 ∧ exp γ i ≠ 0 ∧ (n - (1 - 1) • exp γ) - (n - 1 • exp γ) = Pi.single i 1 := by
  classical
  have hmin : ∀ j, ((n - (1 - 1) • exp γ) - (n - 1 • exp γ)) j =
      if n j = 1 ∧ exp γ j ≠ 0 then 1 else 0 := by
    intro j
    have := h.1 j
    simp only [Pi.sub_apply, Nat.sub_self, zero_smul, Pi.zero_apply, Nat.sub_zero, one_smul]
    split_ifs with hj <;> omega
  by_cases hact : ∃ i, n i = 1 ∧ exp γ i ≠ 0
  · obtain ⟨i, hi, hγi⟩ := hact
    refine Or.inr ⟨i, hi, hγi, funext fun j ↦ ?_⟩
    rw [hmin]
    by_cases hji : j = i
    · subst hji; simp [hi, hγi]
    · rw [Pi.single_apply, if_neg hji, if_neg]
      rintro ⟨hj, hγj⟩
      exact hji (h.2.2.1 γ j i hj hi hγj hγi)
  · refine Or.inl ⟨funext fun j ↦ ?_, hact⟩
    rw [hmin, if_neg fun hj ↦ hact ⟨j, hj⟩]
    rfl

/-- `(U, V, Z_i) + (U, V, Z_j) = (U, V, Z_i, Z_j)`. -/
theorem nIdeal_single_sup {k : Type*} [Field k] (n : Fin m → ℕ) (i j : Fin m) :
    nIdeal k n (Pi.single i 1) ⊔ nIdeal k n (Pi.single j 1) = crossIdeal k n i j := by
  rw [nIdeal, nIdeal, nodeZMon_single, nodeZMon_single, ← Ideal.span_union, crossIdeal]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end Stage2

section Stage2Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] {ι : Type*}

omit [IsIntegral X] [IsLocallyNoetherian X] in
theorem stalkIdeal_sup (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x = stalkIdeal I x ⊔ stalkIdeal J x := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ _ U hxU,
    stalkIdeal_eq_map_germ _ U hxU, Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, Ideal.map_sup]

/-- **One stage-two blowup** (de Jong 4.27; blueprint `prop:sm-dj-stage-two`): blowing up the
reduced support of `((N : (N : E_α)) + (N : (N : E_β)))` separates the members `α ≠ β`. -/
theorem stage2_step (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (hp : IsProjectiveOver p)
    {m : ℕ} (hdim : topologicalKrullDim X = (m + 1 : ℕ)) (N : X.IdealSheafData)
    (E : ι → X.IdealSheafData) (P : Set (ι × ι)) (α β : ι) (hαβ : α ≠ β)
    (h : ∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E (Stage2Inv P) x) :
    Reach k p m E (Stage2Inv (insert (α, β) P)) := by
  classical
  set 𝒲 := centreIdeal N (E α) 1 ⊔ centreIdeal N (E β) 1
  have hW : 𝒲.support ≠ ⊤ :=
    support_ne_top_of_goodAt p N E _ h 𝒲 ((le_centreIdeal N (E α) 1).trans le_sup_left)
  have htrace : ∀ x : X, ∀ c : NodeChart k (X.presheaf.stalk x) m (stalkIdeal N x)
      (fun β ↦ stalkIdeal (E β) x),
      (stalkIdeal 𝒲 x).map (algebraMap _ (X.completedLocalRing x)) =
        (nIdeal k c.n ((c.n - (1 - 1) • c.exp α) - (c.n - 1 • c.exp α)) ⊔
          nIdeal k c.n ((c.n - (1 - 1) • c.exp β) - (c.n - 1 • c.exp β))).map c.e := by
    intro x c
    rw [stalkIdeal_sup, Ideal.map_sup, Ideal.map_sup, stalkIdeal_centreIdeal,
      stalkIdeal_centreIdeal, c.trace_centre α 1, c.trace_centre β 1]
  have hNle : ∀ x : X, stalkIdeal N x ≤ stalkIdeal 𝒲 x := by
    intro x
    rw [stalkIdeal_sup]
    obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
    refine le_sup_of_le_left ?_
    rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ _ U hxU]
    exact Ideal.map_mono (le_centreIdeal N (E α) 1 U)
  have hmem : ∀ x : X, ∀ c : NodeChart k (X.presheaf.stalk x) m (stalkIdeal N x)
      (fun β ↦ stalkIdeal (E β) x), Stage2Inv P c.n c.exp →
      (x ∈ 𝒲.support ↔ ∃ i j, c.n i = 1 ∧ c.n j = 1 ∧ c.exp α i ≠ 0 ∧ c.exp β j ≠ 0) := by
    intro x c hc
    rw [mem_support_iff_stalkIdeal_ne_top]
    constructor
    · intro hne
      by_contra hno
      apply hne
      apply eq_top_of_map_eq_top
      rw [htrace x c]
      rcases stage2_centreExp hc α with ⟨h0, -⟩ | ⟨i, hi, hαi, -⟩
      · rw [h0, nIdeal_zero, top_sup_eq, Ideal.map_top]
      · rcases stage2_centreExp hc β with ⟨h0, -⟩ | ⟨j, hj, hβj, -⟩
        · rw [h0, nIdeal_zero, sup_top_eq, Ideal.map_top]
        · exact absurd ⟨i, j, hi, hj, hαi, hβj⟩ hno
    · rintro ⟨i, j, hi, hj, hαi, hβj⟩ htop
      rcases stage2_centreExp hc α with ⟨-, hno⟩ | ⟨i', hi', hαi', hα⟩
      · exact hno ⟨i, hi, hαi⟩
      rcases stage2_centreExp hc β with ⟨-, hno⟩ | ⟨j', hj', hβj', hβ⟩
      · exact hno ⟨j, hj, hβj⟩
      have : ((crossIdeal k c.n i' j').map c.e).IsPrime := by
        have := isPrime_crossIdeal k c.n i' j' (by omega)
        infer_instance
      apply this.ne_top
      rw [← nIdeal_single_sup, ← hα, ← hβ, ← htrace x c, htop, Ideal.map_top]
  refine exists_blowup_goodAt p hp N E 𝒲.support hW _
    (goodAt_blowup_crossing p hdim N E 𝒲.support hW _ ?_ ?_)
  · intro x hx hxW
    rcases h x hx with ⟨c, hc⟩ | ⟨-, hN⟩
    · obtain ⟨i, j, hi, hj, hαi, hβj⟩ := (hmem x c hc).mp hxW
      have hij : i ≠ j := by
        rintro rfl
        exact hαβ (hc.2.2.2.1 i α β hi hαi hβj)
      rcases stage2_centreExp hc α with ⟨-, hno⟩ | ⟨i', hi', hαi', hα⟩
      · exact absurd ⟨i, hi, hαi⟩ hno
      rcases stage2_centreExp hc β with ⟨-, hno⟩ | ⟨j', hj', hβj', hβ⟩
      · exact absurd ⟨j, hj, hβj⟩ hno
      have hii' : i' = i := hc.2.2.1 α i' i hi' hi hαi' hαi
      have hjj' : j' = j := hc.2.2.1 β j' j hj' hj hβj' hβj
      subst hii' hjj'
      refine ⟨c, i', j', hij, hi, hj, ?_, fun a' b' δ hab' hδ ↦
        hc.cross hij hi hj hαi hβj hab' hδ⟩
      have hprime : ((crossIdeal k c.n i' j').map c.e).IsPrime := by
        have := isPrime_crossIdeal k c.n i' j' (by omega)
        infer_instance
      rw [localIdeal_support, map_radical_eq_of_isPrime, htrace x c, hα, hβ, nIdeal_single_sup,
        crossIdeal, Ideal.map_span]
      · simp only [Set.image_insert_eq, Set.image_singleton]
      · rw [htrace x c, hα, hβ, nIdeal_single_sup]
        exact hprime
    · exfalso
      rw [mem_support_iff_stalkIdeal_ne_top] at hxW
      exact hxW (top_unique (hN ▸ hNle x))
  · intro x hx hxW
    rcases h x hx with ⟨c, hc⟩ | ⟨hr, hN⟩
    · refine Or.inl ⟨c, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, fun q hq ↦ ?_⟩
      rcases hq with rfl | hq
      · exact fun hex ↦ hxW ((hmem x c hc).mpr hex)
      · exact hc.2.2.2.2 q hq
    · exact Or.inr ⟨hr, hN⟩

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- **Stage two** (de Jong 4.27): processing a list of pairs of boundary members. -/
theorem stage2_list {m : ℕ} :
    ∀ (l : List (ι × ι)) (P : Set (ι × ι)) {X : Scheme.{u}} [IsIntegral X]
      [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p],
      IsProjectiveOver p → topologicalKrullDim X = (m + 1 : ℕ) →
      ∀ (N : X.IdealSheafData) (E : ι → X.IdealSheafData),
      (∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E (Stage2Inv P) x) →
      Reach k p m E (Stage2Inv (P ∪ {q | q ∈ l ∧ q.1 ≠ q.2})) := by
  intro l
  induction l with
  | nil =>
    intro P X _ _ p _ hp hdim N E h
    exact (reach_refl p hp N E _ h).mono fun n exp hne ↦ by simpa using hne
  | cons q l ih =>
    intro P X _ _ p _ hp hdim N E h
    by_cases hq : q.1 = q.2
    · have := ih P p hp hdim N E h
      have hset : P ∪ {q' | q' ∈ q :: l ∧ q'.1 ≠ q'.2} = P ∪ {q' | q' ∈ l ∧ q'.1 ≠ q'.2} := by
        ext q'
        simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons]
        constructor
        · rintro (h | ⟨rfl | h, hne⟩)
          · exact Or.inl h
          · exact absurd hq hne
          · exact Or.inr ⟨h, hne⟩
        · rintro (h | ⟨h, hne⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h, hne⟩
      rw [hset]
      exact this
    · refine reach_trans p E _ _ (stage2_step p hp hdim N E P q.1 q.2 hq h) ?_
      intro X₁ _ _ π₁ N₁ hmod₁ hp₁ hg₁
      have : IsProper (π₁ ≫ p) := hp₁.isProper
      have : IsModification π₁ := hmod₁
      have hdim₁ : topologicalKrullDim X₁ = (m + 1 : ℕ) := by
        rw [DeJong.topologicalKrullDim_eq_of_isModification p π₁, hdim]
      have := ih (insert (q.1, q.2) P) (π₁ ≫ p) hp₁ hdim₁ N₁ _ hg₁
      have hset : P ∪ {q' | q' ∈ q :: l ∧ q'.1 ≠ q'.2} =
          insert (q.1, q.2) P ∪ {q' | q' ∈ l ∧ q'.1 ≠ q'.2} := by
        ext q'
        simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_cons, Set.mem_insert_iff,
          Prod.mk.eta]
        constructor
        · rintro (h | ⟨rfl | h, hne⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨h, hne⟩
        · rintro ((rfl | h) | ⟨h, hne⟩)
          · exact Or.inr ⟨Or.inl rfl, hq⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h, hne⟩
      rw [hset]
      exact this

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- **The resolution by the two stages** (de Jong 3.4, 4.27; blueprint
`thm:sm-dj-nc-resolution`). If all closed points of `X` have formal charts with the stage-one
invariant for a bound `B`, there is an integral projective modification `π : X' → X` with a
formal regular chart, for the pulled back boundary ideals, at every closed point. -/
theorem exists_regChart_modification [Fintype ι] {m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X = (m + 1 : ℕ))
    (N : X.IdealSheafData) (E : ι → X.IdealSheafData) (B : ℕ) (α₀ : ι)
    (h : ∀ x : X, IsClosed ({x} : Set X) → GoodAt k m N E (Stage1Inv B ∅ α₀ (B + 1)) x) :
    ∃ (X' : Scheme.{u}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (π : X' ⟶ X),
      IsModification π ∧ IsProjectiveOver (π ≫ p) ∧
      ∀ y : X', IsClosed ({y} : Set X') →
        Nonempty (RegChart (X'.presheaf.stalk y) m fun β ↦ stalkIdeal ((E β).comap π) y) := by
  classical
  have h1 := stage1_list B α₀ (Finset.univ : Finset ι).toList ∅ p hp hdim N E h
  have h1' : Reach k p m E (Stage2Inv ∅) := h1.mono fun n exp hne ↦
    stage2Inv_of_stage1Inv (by simpa using hne)
  have h2 := reach_trans p E _ _ h1' fun X₁ _ _ π₁ N₁ hmod₁ hp₁ hg₁ ↦ by
    have : IsProper (π₁ ≫ p) := hp₁.isProper
    have : IsModification π₁ := hmod₁
    exact stage2_list ((Finset.univ : Finset (ι × ι)).toList) ∅ (π₁ ≫ p) hp₁
      (by rw [DeJong.topologicalKrullDim_eq_of_isModification p π₁, hdim]) N₁ _ hg₁
  obtain ⟨X', i', l', π, N', hmod, hproj, hgood⟩ := h2
  refine ⟨X', i', l', π, hmod, hproj, fun y hy ↦ ?_⟩
  rcases hgood y hy with ⟨c, hc⟩ | ⟨hr, -⟩
  · have hc' : Stage2Inv {q : ι × ι | q.1 ≠ q.2} c.n c.exp := by
      have hset : (∅ : Set (ι × ι)) ∪ {q | q ∈ (Finset.univ : Finset (ι × ι)).toList ∧
          q.1 ≠ q.2} = {q | q.1 ≠ q.2} := by
        ext q; simp
      rw [← hset]; exact hc
    obtain ⟨i, hi⟩ := hc'.eq_single c.pos
    exact c.regChart_of_single i hi
  · exact hr

end Stage2Scheme

end DeJongAlterations.StableModification.Resolution.Global

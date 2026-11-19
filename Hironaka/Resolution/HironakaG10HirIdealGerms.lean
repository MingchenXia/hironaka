import Hironaka.Resolution.HironakaG10PNIdealFamily

/-!
# Spreading stalk-ideal relations of coherent ideal families (lane G10H, run 0080)

For a locally ringed space `X`, an ideal family `J x ⊆ 𝒪_{X,x}` that is *locally finitely
generated on a set `V`* (near every point of `V` the germs of the same finitely many sections span
it at every nearby point of `V`) behaves like a coherent ideal sheaf on `V`: a relation between two
such families at ONE point spreads to a neighbourhood.

* `eventually_germ_mem_span`: a germ relation `u_x ∈ (s'_x)` spreads to `u_y ∈ (s'_y)` near `x`;
* `eventually_le_of_le`, `eventually_eq_of_eq`: `J x ≤ J' x` (resp. `=`) spreads to a neighbourhood;
* `eventually_eq_bot`, `eventually_eq_top`: zero germs and unit ideals spread; in particular the
  support `{J ≠ ⊤}` is closed in `V` (`isClosed_support_inter`).

This is the mechanism behind Hironaka's uniqueness remark Rem. 2.4.4 (p. 529: the flattener is
determined by its germ) and the piecing-together of local flatteners in the proof of Th. 2.4 (p. 527),
H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975).
Generic sheaf theory; no analytic input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.HironakaG10HirIdealGerms

open HironakaG10PNIdealFamily

noncomputable section

universe u

variable {X : LocallyRingedSpace.{u}}

/-- An ideal family is **locally finitely generated on `V`** (coherent on `V`): near every point of
`V` the germs of the same finitely many sections span it at every nearby point of `V`. -/
def IsLocallyFinitelyGeneratedOn (X : LocallyRingedSpace.{u}) (V : Set X)
    (J : ∀ x : X, Ideal (X.presheaf.stalk x)) : Prop :=
  ∀ x ∈ V, ∃ (W : Opens X) (_ : x ∈ W) (r : ℕ) (s : Fin r → X.presheaf.obj (op W)),
    ∀ (y : X) (hy : y ∈ W), y ∈ V →
      J y = Ideal.span (Set.range fun i => X.presheaf.germ W y hy (s i))

theorem IsLocallyFinitelyGeneratedOn.mono {V V' : Set X} {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (h : IsLocallyFinitelyGeneratedOn X V J) (hV : V' ⊆ V) : IsLocallyFinitelyGeneratedOn X V' J := by
  intro x hx
  obtain ⟨W, hxW, r, s, hs⟩ := h x (hV hx)
  exact ⟨W, hxW, r, s, fun y hy hyV => hs y hy (hV hyV)⟩

/-- A (globally) locally finitely generated family is locally finitely generated on every set. -/
theorem isLocallyFinitelyGeneratedOn_of_isLocallyFinitelyGenerated
    {J : ∀ x : X, Ideal (X.presheaf.stalk x)} (h : IsLocallyFinitelyGenerated X J) (V : Set X) :
    IsLocallyFinitelyGeneratedOn X V J := by
  intro x _
  obtain ⟨W, hxW, r, s, hs⟩ := h x
  exact ⟨W, hxW, r, s, fun y hy _ => hs y hy⟩

/-- The zero family is locally finitely generated (by no section). -/
theorem isLocallyFinitelyGeneratedOn_bot (V : Set X) :
    IsLocallyFinitelyGeneratedOn X V fun _ => ⊥ := by
  intro x _
  refine ⟨⊤, trivial, 0, Fin.elim0, fun y _ _ => ?_⟩
  rw [Set.range_eq_empty, Ideal.span_empty]

/-- The unit family is locally finitely generated (by the section `1`). -/
theorem isLocallyFinitelyGeneratedOn_top (V : Set X) :
    IsLocallyFinitelyGeneratedOn X V fun _ => ⊤ := by
  intro x _
  refine ⟨⊤, trivial, 1, fun _ => 1, fun y hy _ => ?_⟩
  rw [eq_comm, Ideal.eq_top_iff_one]
  refine Ideal.subset_span ⟨0, ?_⟩
  exact map_one _

/-- **One germ relation spreads.** If the germ of `u` at `x` lies in the ideal spanned by the germs
of `s'` at `x`, the same holds at every point near `x`. -/
theorem eventually_germ_mem_span {x : X} {W W' : Opens X} (hxW : x ∈ W) (hxW' : x ∈ W')
    {r' : ℕ} (u : X.presheaf.obj (op W)) (s' : Fin r' → X.presheaf.obj (op W'))
    (h : X.presheaf.germ W x hxW u ∈
      Ideal.span (Set.range fun j => X.presheaf.germ W' x hxW' (s' j))) :
    ∀ᶠ y in 𝓝 x, ∀ (hy : y ∈ W) (hy' : y ∈ W'),
      X.presheaf.germ W y hy u ∈
        Ideal.span (Set.range fun j => X.presheaf.germ W' y hy' (s' j)) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  choose U hxU t ht using fun j => X.presheaf.exists_germ_eq (c j)
  let O : Opens X := W' ⊓ ⨅ j, U j
  have hxO : x ∈ O := by
    refine ⟨hxW', ?_⟩
    show x ∈ (((⨅ j, U j) : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact mem_iInter.2 hxU
  have hOW' : O ≤ W' := inf_le_left
  have hOU : ∀ j, O ≤ U j := fun j => inf_le_right.trans (iInf_le _ j)
  let w : X.presheaf.obj (op O) := ∑ j, X.presheaf.map (homOfLE (hOU j)).op (t j) *
    X.presheaf.map (homOfLE hOW').op (s' j)
  have hgw : ∀ (y : X) (hy : y ∈ O), X.presheaf.germ O y hy w =
      ∑ j, X.presheaf.germ (U j) y (hOU j hy) (t j) * X.presheaf.germ W' y (hOW' hy) (s' j) := by
    intro y hy
    simp only [w, map_sum, map_mul, X.presheaf.germ_res_apply]
  have hx : X.presheaf.germ O x hxO w = X.presheaf.germ W x hxW u := by
    rw [hgw, ← hc]
    exact Finset.sum_congr rfl fun j _ => by rw [ht j]
  obtain ⟨N, hxN, iO, iW, he⟩ := X.presheaf.germ_eq x hxO hxW w u hx
  filter_upwards [N.isOpen.mem_nhds hxN] with y hyN hy hy'
  have hyO : y ∈ O := iO.le hyN
  have heq : X.presheaf.germ W y hy u = X.presheaf.germ O y hyO w := by
    rw [← X.presheaf.germ_res_apply iW y hyN, ← he, X.presheaf.germ_res_apply]
  rw [heq, hgw]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- **All generators at once.** -/
theorem eventually_span_le {x : X} {W W' : Opens X} (hxW : x ∈ W) (hxW' : x ∈ W')
    {r r' : ℕ} (s : Fin r → X.presheaf.obj (op W)) (s' : Fin r' → X.presheaf.obj (op W'))
    (h : Ideal.span (Set.range fun i => X.presheaf.germ W x hxW (s i)) ≤
      Ideal.span (Set.range fun j => X.presheaf.germ W' x hxW' (s' j))) :
    ∀ᶠ y in 𝓝 x, ∀ (hy : y ∈ W) (hy' : y ∈ W'),
      Ideal.span (Set.range fun i => X.presheaf.germ W y hy (s i)) ≤
        Ideal.span (Set.range fun j => X.presheaf.germ W' y hy' (s' j)) := by
  have hi : ∀ i, ∀ᶠ y in 𝓝 x, ∀ (hy : y ∈ W) (hy' : y ∈ W'),
      X.presheaf.germ W y hy (s i) ∈
        Ideal.span (Set.range fun j => X.presheaf.germ W' y hy' (s' j)) := fun i =>
    eventually_germ_mem_span hxW hxW' (s i) s' (h (Ideal.subset_span ⟨i, rfl⟩))
  filter_upwards [eventually_all.2 hi] with y hy hyW hyW'
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hy i hyW hyW'

/-- **A stalk inclusion between two coherent families spreads to a neighbourhood.** -/
theorem eventually_le_of_le {V V' : Set X} {J J' : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGeneratedOn X V J) (hJ' : IsLocallyFinitelyGeneratedOn X V' J')
    (hV : IsOpen V) (hV' : IsOpen V') {x : X} (hx : x ∈ V) (hx' : x ∈ V') (h : J x ≤ J' x) :
    ∀ᶠ y in 𝓝 x, J y ≤ J' y := by
  obtain ⟨W, hxW, r, s, hs⟩ := hJ x hx
  obtain ⟨W', hxW', r', s', hs'⟩ := hJ' x hx'
  have h0 := eventually_span_le hxW hxW' s s' (by rw [← hs x hxW hx, ← hs' x hxW' hx']; exact h)
  filter_upwards [h0, W.isOpen.mem_nhds hxW, W'.isOpen.mem_nhds hxW', hV.mem_nhds hx,
    hV'.mem_nhds hx'] with y hy hyW hyW' hyV hyV'
  rw [hs y hyW hyV, hs' y hyW' hyV']
  exact hy hyW hyW'

/-- **Equality at one point spreads** (germ form of Hironaka Rem. 2.4.4). -/
theorem eventually_eq_of_eq {V V' : Set X} {J J' : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGeneratedOn X V J) (hJ' : IsLocallyFinitelyGeneratedOn X V' J')
    (hV : IsOpen V) (hV' : IsOpen V') {x : X} (hx : x ∈ V) (hx' : x ∈ V') (h : J x = J' x) :
    ∀ᶠ y in 𝓝 x, J y = J' y := by
  filter_upwards [eventually_le_of_le hJ hJ' hV hV' hx hx' h.le,
    eventually_le_of_le hJ' hJ hV' hV hx' hx h.ge] with y h1 h2
  exact le_antisymm h1 h2

/-- A coherent family with zero germ at `x` vanishes near `x`. -/
theorem eventually_eq_bot {V : Set X} {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGeneratedOn X V J) (hV : IsOpen V) {x : X} (hx : x ∈ V)
    (h : J x = ⊥) : ∀ᶠ y in 𝓝 x, J y = ⊥ := by
  filter_upwards [eventually_le_of_le hJ (isLocallyFinitelyGeneratedOn_bot univ) hV isOpen_univ hx
    (mem_univ x) h.le] with y hy
  exact le_bot_iff.1 hy

/-- A coherent family which is the unit ideal at `x` is the unit ideal near `x`. -/
theorem eventually_eq_top {V : Set X} {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGeneratedOn X V J) (hV : IsOpen V) {x : X} (hx : x ∈ V)
    (h : J x = ⊤) : ∀ᶠ y in 𝓝 x, J y = ⊤ := by
  filter_upwards [eventually_le_of_le (isLocallyFinitelyGeneratedOn_top univ) hJ isOpen_univ hV
    (mem_univ x) hx h.ge] with y hy
  exact top_le_iff.1 hy

/-- The support `{J ≠ ⊤}` of a family coherent on an open `V` is closed in `V`: its complement in
`V` is open. -/
theorem isOpen_inter_eq_top {V : Set X} {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGeneratedOn X V J) (hV : IsOpen V) :
    IsOpen (V ∩ {x | J x = ⊤}) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxV, hx⟩
  filter_upwards [hV.mem_nhds hxV, eventually_eq_top hJ hV hxV hx] with y hyV hy
  exact ⟨hyV, hy⟩

end

end Hironaka.HironakaG10HirIdealGerms

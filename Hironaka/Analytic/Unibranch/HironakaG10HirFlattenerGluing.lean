import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
import Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum

/-!
# P3 — Hironaka's Theorem 2.4 for a compact `S`: gluing pointwise local flatteners

Lane G10H, run 0080, round 3 (plan P3 of `work/hironaka-resume-20261111/G10H/PSEUDOFREE-ROUTE.md` §4).
Source: H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975),
Th. 2.4 (p. 526) and the piecing-together in its proof (p. 527: `V = ⋃ D_y ∖ ⋃ (D̄_y ∩ D̄_{y'} ∖ N_{yy'})`).

* `exists_localFlattener_of_isCompact` — **Th. 2.4 (2.4.1)+(2.4.2) for a compact `S`**: if `S = V(I_S)` is
  given by an ideal family coherent on an open `W`, its support `|S|` is compact, and `f` is flat over
  `S` along every fibre over `|S|`, then ONE local flattener `Z` has `|S| ⊆ |Z|` and `H_Z ≤ I_S` on `|S|`
  (i.e. `S ⊆ Z`).  From the ONE local input `PersistentLocalFlattener` (P2) only: no connectedness is
  needed (each piece contains `S` near its centre by the flattener property and coherence of `I_S`),
  pieces agree near `|S|` by Rem. 2.4.4 (`LocalFlattener.eventually_eq`), and Hironaka's shrinking glues
  them.
* `isLocallyFinitelyGeneratedOn_of_local` — coherence is local (used for the glued family).
* `trackedDatumOfLocalFlatteners` — the germ-level tracked datum of lane G10C
  (`HironakaG10ChowTrackedDatum.TrackedDatum`) underlying a finite family of local flatteners.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10HirFlattenerGluing

open Hironaka HironakaG10HirIdealGerms
open Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener

noncomputable section

/-- **Coherence is local**: a family which near every point of `V'` agrees (on `V'`) with a family
coherent on some set containing that neighbourhood's points of `V'` is coherent on `V'`. -/
theorem isLocallyFinitelyGeneratedOn_of_local {X : LocallyRingedSpace} {V' : Set X}
    {J' : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hloc : ∀ x ∈ V', ∃ (U : Set X) (V : Set X) (J : ∀ x : X, Ideal (X.presheaf.stalk x)),
      IsOpen U ∧ x ∈ U ∧ x ∈ V ∧ IsLocallyFinitelyGeneratedOn X V J ∧
        ∀ y ∈ U, y ∈ V' → y ∈ V ∧ J' y = J y) :
    IsLocallyFinitelyGeneratedOn X V' J' := by
  intro x hx
  obtain ⟨U, V, J, hU, hxU, hxV, hJ, hJJ'⟩ := hloc x hx
  obtain ⟨W, hxW, r, s, hs⟩ := hJ x hxV
  let O : Opens X := W ⊓ ⟨U, hU⟩
  have hOW : O ≤ W := inf_le_left
  refine ⟨O, ⟨hxW, hxU⟩, r, fun i => X.presheaf.map (homOfLE hOW).op (s i), fun y hy hyV' => ?_⟩
  obtain ⟨hyV, hy'⟩ := hJJ' y hy.2 hyV'
  rw [hy', hs y hy.1 hyV]
  simp only [X.presheaf.germ_res_apply]

variable {X Y : SourceReducedComplexSpace}

/-- **Hironaka Th. 2.4 for a compact `S`** ((2.4.1) + (2.4.2), p. 526; gluing of p. 527) from the
local input. -/
theorem exists_localFlattener_of_isCompact (hP : PersistentLocalFlattener) (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (W : Set X.obj.left) (hW : IsOpen W)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left W IS)
    (hS : IsCompact (W ∩ {x | IS x ≠ ⊤}))
    (hflat : ∀ x ∈ W, IS x ≠ ⊤ → FlatOverAt f x (IS x)) :
    ∃ Z : LocalFlattener f, W ∩ {x | IS x ≠ ⊤} ⊆ Z.support ∧
      ∀ x ∈ W, IS x ≠ ⊤ → Z.H x ≤ IS x := by
  have : T2Space X.obj.left := X.property.1
  have : ParacompactSpace X.obj.left := X.property.2.1
  set S := W ∩ {x | IS x ≠ ⊤} with hSdef
  -- pointwise pieces
  choose Zf hZf using hP X Y f hf
  have hpiece : ∀ x ∈ S, ∃ t ∈ 𝓝 x, IsClosed t ∧
      t ⊆ {y | y ∈ (Zf x).V ∧ y ∈ W ∧ (Zf x).H y ≤ IS y} := by
    intro x hx
    have hle : (Zf x).H x ≤ IS x :=
      ((Zf x).flattener x (hZf x).1 (hZf x).2 (IS x)).1 (hflat x hx.1 hx.2)
    have hev := eventually_le_of_le (Zf x).fg hIS (Zf x).isOpen hW (hZf x).1 hx.1 hle
    refine exists_mem_nhds_isClosed_subset ?_
    filter_upwards [(Zf x).isOpen.mem_nhds (hZf x).1, hW.mem_nhds hx.1, hev] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  choose t ht htc hts using hpiece
  let D : ∀ x ∈ S, Set X.obj.left := fun x hx => interior (t x hx)
  obtain ⟨T, hT⟩ := hS.elim_nhds_subcover' D fun x hx => interior_mem_nhds.2 (ht x hx)
  -- the pieces indexed by the finite subcover
  let Dk : S → Set X.obj.left := fun k => D k.1 k.2
  let Zk : S → LocalFlattener f := fun k => Zf k.1
  have hDk_open : ∀ k, IsOpen (Dk k) := fun k => isOpen_interior
  have hDk_cl : ∀ k, closure (Dk k) ⊆ {y | y ∈ (Zk k).V ∧ y ∈ W ∧ (Zk k).H y ≤ IS y} :=
    fun k => (closure_minimal interior_subset (htc k.1 k.2)).trans (hts k.1 k.2)
  let N : S → S → Set X.obj.left := fun k l => {y | ∀ᶠ z in 𝓝 y, (Zk k).H z = (Zk l).H z}
  have hN_open : ∀ k l, IsOpen (N k l) := fun k l => isOpen_setOfPred_eventually_nhds
  have hSN : ∀ k l, ∀ y ∈ S, y ∈ closure (Dk k) → y ∈ closure (Dk l) → y ∈ N k l := by
    intro k l y hy hyk hyl
    obtain ⟨hk1, -, hk3⟩ := hDk_cl k hyk
    obtain ⟨hl1, -, hl3⟩ := hDk_cl l hyl
    have hk : y ∈ (Zk k).support := ⟨hk1, fun h => hy.2 (top_le_iff.1 (h ▸ hk3))⟩
    have hl : y ∈ (Zk l).support := ⟨hl1, fun h => hy.2 (top_le_iff.1 (h ▸ hl3))⟩
    exact (Zk k).eventually_eq (Zk l) hk hl
  -- the glued open set
  let Bad : Set X.obj.left :=
    ⋃ k ∈ T, ⋃ l ∈ T, (closure (Dk k) ∩ closure (Dk l)) \ N k l
  have hBad : IsClosed Bad :=
    isClosed_biUnion_finset fun k _ => isClosed_biUnion_finset fun l _ =>
      (isClosed_closure.inter isClosed_closure).sdiff (hN_open k l)
  let V : Set X.obj.left := (⋃ k ∈ T, Dk k) \ Bad
  have hV : IsOpen V := (isOpen_biUnion fun k _ => hDk_open k).sdiff hBad
  have hagree : ∀ y ∈ V, ∀ k ∈ T, ∀ l ∈ T, y ∈ Dk k → y ∈ Dk l → (Zk k).H y = (Zk l).H y := by
    intro y hy k hk l hl hyk hyl
    have hyN : y ∈ N k l := by
      by_contra hn
      exact hy.2 (mem_biUnion hk (mem_biUnion hl ⟨⟨subset_closure hyk, subset_closure hyl⟩, hn⟩))
    exact Filter.Eventually.self_of_nhds (p := fun z => (Zk k).H z = (Zk l).H z) hyN
  -- the glued family
  classical
  let H : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x) := fun y =>
    if h : ∃ k ∈ T, y ∈ Dk k then (Zk (Classical.choose h)).H y else ⊤
  have hH : ∀ y ∈ V, ∀ k ∈ T, y ∈ Dk k → H y = (Zk k).H y := by
    intro y hy k hk hyk
    have h : ∃ k ∈ T, y ∈ Dk k := ⟨k, hk, hyk⟩
    simp only [H, dif_pos h]
    exact hagree y hy _ (Classical.choose_spec h).1 k hk (Classical.choose_spec h).2 hyk
  have hDV : ∀ k, Dk k ⊆ (Zk k).V := fun k y hy => (hDk_cl k (subset_closure hy)).1
  have hSV : S ⊆ V := by
    intro y hy
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 (hT hy)
      exact mem_iUnion₂.2 ⟨k, hk, hyk⟩
    · intro hbad
      obtain ⟨k, hk, hbad⟩ := mem_iUnion₂.1 hbad
      obtain ⟨l, hl, ⟨⟨hyk, hyl⟩, hn⟩⟩ := mem_iUnion₂.1 hbad
      exact hn (hSN k l y hy hyk hyl)
  have hle : ∀ y ∈ S, H y ≤ IS y := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 (hT hy)
    rw [hH y (hSV hy) k hk hyk]
    exact (hDk_cl k (subset_closure hyk)).2.2
  refine ⟨⟨V, hV, H, ?_, ?_⟩, fun y hy => ⟨hSV hy, fun h => hy.2 (top_le_iff.1 (h ▸ hle y hy))⟩,
    fun y hyW hy => hle y ⟨hyW, hy⟩⟩
  · refine isLocallyFinitelyGeneratedOn_of_local fun x hx => ?_
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx.1
    exact ⟨V ∩ Dk k, (Zk k).V, (Zk k).H, hV.inter (hDk_open k), ⟨hx, hxk⟩, hDV k hxk, (Zk k).fg,
      fun y hy _ => ⟨hDV k hy.2, hH y hy.1 k hk hy.2⟩⟩
  · intro x hx hne
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx.1
    rw [hH x hx k hk hxk] at hne ⊢
    exact (Zk k).flattener x (hDV k hxk) hne

/-- The germ-level tracked datum (lane G10C, Hironaka Def. 4.4.2 (3)) underlying finitely many
local flatteners: `V_p` and `Z_p = |Z_p|`. -/
def trackedDatumOfLocalFlatteners {q : ℕ} {f : Y ⟶ X} (Z : Fin q → LocalFlattener f) :
    HironakaG10ChowTrackedDatum.TrackedDatum X where
  q := q
  V p := (Z p).V
  Z p := (Z p).support
  isOpen p := (Z p).isOpen
  sub _ _ hx := hx.1

end

end Hironaka.Analytic.Unibranch.HironakaG10HirFlattenerGluing

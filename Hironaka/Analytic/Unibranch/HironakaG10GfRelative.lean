import Hironaka.Analytic.Unibranch.HironakaG10GfSmoothBase

/-!
# Generic flatness over a reduced parameter set at its smooth points (lane G10GF, run 0081, G10-03-05.c2)

Frisch 1967, Prop. (IV,14) (`references/frisch67-points-platitude`, p. 135), at chart level over a parameter
SET `T ⊆ ℂᵈ` (the trace of a reduced analytic subspace, as in Frisch 1968 §2 and the library's
`HironakaG10LocRelative`: identities are imposed only over `T × ℂᵐ`), in the relative Tor₁ form
`HironakaG10LocRelative.RelFibreFlatAt`.

* `FlatChart T p`: a holomorphic parametrization `ι : B → T ∩ O` of `T` near `p` with a holomorphic retraction
  `π : O → ℂᵏ` (`π ∘ ι = id` on `B`, `ι ∘ π = id` on `O ∩ T`).  At a regular point of an analytic set it is given
  by the flattening biholomorphism (`Hironaka.RegularAtDim`).
* **`relFibreFlatAt_of_fibreFlatAt`**: flatness over the smooth parameter space `ℂᵏ` of the pulled-back
  matrix `F(ι ·, ·)` gives flatness over `T` of `F` at the image point.  Purely at the level of functions:
  relative relations over `T` pull back along `ι × id` to honest relations, combinations push forward along
  `π × id`, and the fibres coincide.
* **`exists_forall_relFibreFlatAt`**: every open `V` meeting `T` in a point with a flat chart contains a point
  `q ∈ T` over which `coker F` is flat over `T` at every point of `{q} × K` (from
  `HironakaG10GfSmoothBase.exists_forall_fibreFlatAt`).

No named input.  Blueprint: `hironaka-g10gf-relative.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GfRelative

noncomputable section

open Hironaka OkaRelationSheaf HironakaG10FlatResolutionStart
  HironakaG10LocFibreOpen HironakaG10LocSheafExact HironakaG10LocRelative

/-- Holomorphy at a point is preserved by composition with a map differentiable NEAR the point. -/
theorem holAt_comp_of_eventually {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : F → ℂ} {φ : E → F} {y : E}
    (hf : HolAt f (φ y)) (hφ : ∀ᶠ x in 𝓝 y, DifferentiableAt ℂ φ x) : HolAt (f ∘ φ) y := by
  have hc : ContinuousAt φ y := hφ.self_of_nhds.continuousAt
  filter_upwards [hφ, hc.tendsto.eventually hf] with x hx1 hx2
  exact hx2.comp x hx1

variable {d : ℕ}

/-- **A flat chart of a parameter set `T ⊆ ℂᵈ` at `p`**: an open `O ∋ p`, an open `B ⊆ ℂᵏ`, a holomorphic
parametrization `ι : B → O ∩ T` and a holomorphic retraction `π : O → ℂᵏ` inverse to each other. -/
structure FlatChart (T : Set (EuclideanSpace ℂ (Fin d))) (p : EuclideanSpace ℂ (Fin d)) where
  /-- the dimension of `T` at `p` -/
  k : ℕ
  /-- the open set of `ℂᵈ` where `T` is parametrized -/
  O : Set (EuclideanSpace ℂ (Fin d))
  isOpen_O : IsOpen O
  mem_O : p ∈ O
  /-- the parameter domain -/
  B : Set (EuclideanSpace ℂ (Fin k))
  isOpen_B : IsOpen B
  /-- the parametrization -/
  ι : EuclideanSpace ℂ (Fin k) → EuclideanSpace ℂ (Fin d)
  /-- the retraction -/
  π : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)
  diff_ι : DifferentiableOn ℂ ι B
  diff_π : DifferentiableOn ℂ π O
  mapsTo_ι : MapsTo ι B (O ∩ T)
  π_mem : ∀ q ∈ O ∩ T, π q ∈ B
  π_ι : ∀ s ∈ B, π (ι s) = s
  ι_π : ∀ q ∈ O ∩ T, ι (π q) = q

namespace FlatChart

variable {T : Set (EuclideanSpace ℂ (Fin d))} {p : EuclideanSpace ℂ (Fin d)} (c : FlatChart T p)
  {m : ℕ}

/-- `ι × id`. -/
def up : EuclideanSpace ℂ (Fin c.k) × EuclideanSpace ℂ (Fin m) →
    EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m) := fun r => (c.ι r.1, r.2)

/-- `π × id`. -/
def down : EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m) →
    EuclideanSpace ℂ (Fin c.k) × EuclideanSpace ℂ (Fin m) := fun q => (c.π q.1, q.2)

theorem differentiableAt_up {r : EuclideanSpace ℂ (Fin c.k) × EuclideanSpace ℂ (Fin m)}
    (hr : r.1 ∈ c.B) : DifferentiableAt ℂ (c.up (m := m)) r :=
  ((c.diff_ι.differentiableAt (c.isOpen_B.mem_nhds hr)).comp r differentiableAt_fst).prodMk
    differentiableAt_snd

theorem differentiableAt_down {q : EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m)}
    (hq : q.1 ∈ c.O) : DifferentiableAt ℂ (c.down (m := m)) q :=
  ((c.diff_π.differentiableAt (c.isOpen_O.mem_nhds hq)).comp q differentiableAt_fst).prodMk
    differentiableAt_snd

theorem eventually_differentiableAt_up {r : EuclideanSpace ℂ (Fin c.k) × EuclideanSpace ℂ (Fin m)}
    (hr : r.1 ∈ c.B) : ∀ᶠ r' in 𝓝 r, DifferentiableAt ℂ (c.up (m := m)) r' := by
  filter_upwards [(c.isOpen_B.preimage continuous_fst).mem_nhds hr] with r' hr'
  exact c.differentiableAt_up hr'

theorem eventually_differentiableAt_down {q : EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m)}
    (hq : q.1 ∈ c.O) : ∀ᶠ q' in 𝓝 q, DifferentiableAt ℂ (c.down (m := m)) q' := by
  filter_upwards [(c.isOpen_O.preimage continuous_fst).mem_nhds hq] with q' hq'
  exact c.differentiableAt_down hq'

theorem continuousOn_down : ContinuousOn (c.down (m := m)) (c.O ×ˢ univ) := fun _ hq =>
  (c.differentiableAt_down hq.1).continuousAt.continuousWithinAt

theorem continuousOn_up : ContinuousOn (c.up (m := m)) (c.B ×ˢ univ) := fun _ hr =>
  (c.differentiableAt_up hr.1).continuousAt.continuousWithinAt

end FlatChart

/-- **Flatness over the smooth parameter space of the pulled-back matrix gives flatness over `T`.** -/
theorem relFibreFlatAt_of_fibreFlatAt {T : Set (EuclideanSpace ℂ (Fin d))} {p : EuclideanSpace ℂ (Fin d)}
    (c : FlatChart T p) {m a b : ℕ}
    (F : Fin a → Fin b → EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m) → ℂ)
    {U : Set (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m))} (hU : IsOpen U)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) {s : EuclideanSpace ℂ (Fin c.k)} (hs : s ∈ c.B)
    {z : EuclideanSpace ℂ (Fin m)} (hsz : (c.ι s, z) ∈ U)
    (h : FibreFlatAt (fun i j r => F i j (c.ι r.1, r.2)) (s, z)) :
    RelFibreFlatAt T F (c.ι s, z) := by
  obtain ⟨n, G', W', hW', hsW', hstart, hfib⟩ := h
  let G : Fin b → Fin n → EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m) → ℂ :=
    fun j k q => G' j k (c.π q.1, q.2)
  let W : Set (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m)) :=
    U ∩ (c.O ×ˢ univ ∩ c.down ⁻¹' W')
  have hW : IsOpen W :=
    hU.inter (c.continuousOn_down.isOpen_inter_preimage (c.isOpen_O.prod isOpen_univ) hW')
  have hιs : c.ι s ∈ c.O ∩ T := c.mapsTo_ι hs
  have hpW : (c.ι s, z) ∈ W := by
    refine ⟨hsz, ⟨hιs.1, mem_univ _⟩, ?_⟩
    show (c.π (c.ι s), z) ∈ W'
    rw [c.π_ι s hs]
    exact hsW'
  refine ⟨n, G, W, hW, hpW, ⟨fun i j => (hF i j).mono inter_subset_left, fun j k => ?_, ?_, ?_⟩, ?_⟩
  · -- `G` is holomorphic on `W`
    intro q hq
    exact ((hstart.holG j k).differentiableAt (hW'.mem_nhds hq.2.2)).comp q
      (c.differentiableAt_down hq.2.1.1) |>.differentiableWithinAt
  · -- `F G = 0` over `T`
    intro i k q hq hqT
    have hqO : q.1 ∈ c.O ∩ T := ⟨hq.2.1.1, hqT⟩
    have h0 := hstart.comp i k (c.down q) hq.2.2
    have hq' : q = (c.ι (c.π q.1), q.2) := by rw [c.ι_π q.1 hqO]
    calc ∑ j, F i j q * G j k q = ∑ j, F i j (c.ι (c.π q.1), q.2) * G' j k (c.down q) := by
          rw [← hq']; rfl
      _ = 0 := h0
  · -- relative exactness
    intro p' hp' hp'T
    have hp'O : p'.1 ∈ c.O ∩ T := ⟨hp'.2.1.1, hp'T⟩
    set r' := c.down p' with hr'
    have hr'B : r'.1 ∈ c.B := c.π_mem _ hp'O
    have hupr' : c.up r' = p' := by
      show (c.ι (c.π p'.1), p'.2) = p'
      rw [c.ι_π _ hp'O]
    have hr'W' : r' ∈ W' := hp'.2.2
    intro A hA hAF
    let Ã : Fin b → EuclideanSpace ℂ (Fin c.k) × EuclideanSpace ℂ (Fin m) → ℂ := fun j => A j ∘ c.up
    have hÃ : ∀ j, HolAt (Ã j) r' := fun j =>
      holAt_comp_of_eventually (by rw [hupr']; exact hA j) (c.eventually_differentiableAt_up hr'B)
    have hup_t : Tendsto c.up (𝓝 r') (𝓝 p') := by
      have := (c.differentiableAt_up hr'B).continuousAt.tendsto
      rwa [hupr'] at this
    have hrel : IsRelationAt (fun i j r => F i j (c.ι r.1, r.2)) r' Ã := by
      refine ⟨hÃ, fun i => ?_⟩
      filter_upwards [hup_t.eventually (hAF i), (c.isOpen_B.preimage continuous_fst).mem_nhds hr'B]
        with r hr hrB
      exact hr (c.mapsTo_ι hrB).2
    obtain ⟨C', hC', hC'eq⟩ := hstart.exact r' hr'W' Ã hrel
    refine ⟨fun k => C' k ∘ c.down, fun k => holAt_comp_of_eventually (hC' k)
      (c.eventually_differentiableAt_down hp'O.1), fun j => ?_⟩
    have hdown_t : Tendsto c.down (𝓝 p') (𝓝 r') :=
      (c.differentiableAt_down hp'O.1).continuousAt.tendsto
    filter_upwards [hdown_t.eventually (hC'eq j), (c.isOpen_O.preimage continuous_fst).mem_nhds hp'O.1]
      with q hq hqO hqT
    have hqOT : q.1 ∈ c.O ∩ T := ⟨hqO, hqT⟩
    have hAq : A j q = Ã j (c.down q) := by
      show A j q = A j (c.ι (c.π q.1), q.2)
      rw [c.ι_π _ hqOT]
    rw [hAq, hq]
    rfl
  · -- the fibre at `ι s` is the fibre at `s`
    have efib : fib G (c.ι s) = fib G' s := by
      funext j k x
      show G' j k (c.π (c.ι s), x) = G' j k (s, x)
      rw [c.π_ι s hs]
    intro v hv
    show IsCombinationAt (columns (fib G (c.ι s))) z v
    rw [efib]
    exact hfib v hv

/-- **Generic flatness over a parameter set at a smooth point** (chart level, relative Tor₁ form). -/
theorem exists_forall_relFibreFlatAt {T : Set (EuclideanSpace ℂ (Fin d))} {m a b : ℕ}
    (F : Fin a → Fin b → EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m) → ℂ)
    {U : Set (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin m))} (hU : IsOpen U)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) {V : Set (EuclideanSpace ℂ (Fin d))} (hV : IsOpen V)
    {K : Set (EuclideanSpace ℂ (Fin m))} (hK : IsCompact K)
    (hVK : ∀ q ∈ V ∩ T, ∀ z ∈ K, (q, z) ∈ U) {p : EuclideanSpace ℂ (Fin d)} (hpV : p ∈ V)
    (hpT : p ∈ T) (c : FlatChart T p) :
    ∃ q ∈ V ∩ T, ∀ z ∈ K, RelFibreFlatAt T F (q, z) := by
  have hpOT : p ∈ c.O ∩ T := ⟨c.mem_O, hpT⟩
  let B' : Set (EuclideanSpace ℂ (Fin c.k)) := c.B ∩ c.ι ⁻¹' V
  have hB' : IsOpen B' := c.diff_ι.continuousOn.isOpen_inter_preimage c.isOpen_B hV
  have hB'ne : B'.Nonempty := ⟨c.π p, c.π_mem p hpOT, by
    show c.ι (c.π p) ∈ V
    rw [c.ι_π p hpOT]
    exact hpV⟩
  let Ũ : Set (EuclideanSpace ℂ (Fin c.k) × EuclideanSpace ℂ (Fin m)) :=
    c.B ×ˢ univ ∩ c.up ⁻¹' U
  have hŨ : IsOpen Ũ := c.continuousOn_up.isOpen_inter_preimage (c.isOpen_B.prod isOpen_univ) hU
  have hF' : ∀ i j, DifferentiableOn ℂ (fun r => F i j (c.ι r.1, r.2)) Ũ := by
    intro i j r hr
    exact (((hF i j).differentiableAt (hU.mem_nhds hr.2)).comp r
      (c.differentiableAt_up hr.1.1)).differentiableWithinAt
  have hB'K : B' ×ˢ K ⊆ Ũ := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    exact ⟨⟨hs.1, mem_univ _⟩, hVK _ ⟨hs.2, (c.mapsTo_ι hs.1).2⟩ z hz⟩
  obtain ⟨s, hs, hflat⟩ := HironakaG10GfSmoothBase.exists_forall_fibreFlatAt m c.k
    (EuclideanSpace ℂ (Fin c.k)) finrank_euclideanSpace_fin (fun i j r => F i j (c.ι r.1, r.2))
    hŨ hF' hB' hB'ne hK hB'K
  refine ⟨c.ι s, ⟨hs.2, (c.mapsTo_ι hs.1).2⟩, fun z hz => ?_⟩
  exact relFibreFlatAt_of_fibreFlatAt c F hU hF hs.1
    (hVK _ ⟨hs.2, (c.mapsTo_ι hs.1).2⟩ z hz) (hflat z hz)

end

end Hironaka.Analytic.Unibranch.HironakaG10GfRelative

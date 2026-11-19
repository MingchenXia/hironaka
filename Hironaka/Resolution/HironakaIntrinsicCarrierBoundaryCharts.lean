/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaContactParameterIntrinsicOrder
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Invariant.StepOneLowerDomain
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaIntrinsicCarrierBoundaryCharts
open Hironaka.RegularLocusDense RelativePrincipalizationSpan BlowupTowers Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves GermIdealPullbackCalculus HadamardBridge
  StepOneValue StepOneRegime MaximalOrderStepOneB BlowupTowerTransforms HomogenizedIdealAlong
  GermIdealOrder GiraudAlong DivisorExponentAlong MarkedIdeals MarkedIdeal ResolutionInvariantSpec
  HironakaSmoothSubmersionAdaptedProductCoordinates HironakaSmoothSubmersionCoefficientIdeals HironakaContactParameterIntrinsicOrder HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionContactParameterCoefficientIdeals
  NormalCrossings SimultaneousNormalCrossings BlowupSNCTransform BlowupFlatCoordinates
noncomputable section
variable {n b : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} b}

theorem whole_nonzero_of_actual_local_retraction {σ : Y → X} {r : X → Y}
    {C : Set X} {z : Y}
    (hσ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel n) σ w)
    (hr : ∀ᶠ x in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) r x)
    (hrz : r (σ z) = z)
    (hround : ∀ᶠ x in 𝓝 (σ z), x ∈ C → σ (r x) = x)
    (I : GermIdeal n X) (hI : I.IsCoherent) (hne : IsNonzeroAlongAt C I (σ z)) :
    IsNonzeroAlongAt univ (GermIdeal.pullback (m := b) σ I) z := by
  obtain ⟨g,hg,hfreq⟩ := hne
  have hcomp : (GermIdeal.pullback (m := b) σ I).mem z (g ∘ σ) :=
    GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
      ⟨g,hg,rfl⟩ (holomorphicAt_comp_map hσ (GermIdeal.IsCoherent.holomorphicAt_mem hI hg)))
  refine ⟨g ∘ σ,hcomp,?_⟩
  by_contra hn
  have hz0 : ∀ᶠ w in 𝓝 z, g (σ w) = 0 := by
    have hneg := not_frequently.mp hn
    filter_upwards [hneg] with w hw
    simpa only [mem_univ,true_and,Function.comp_apply,not_not] using hw
  have hx0 : ∀ᶠ x in 𝓝 (σ z), g (σ (r x)) = 0 := by
    have ht := hr.self_of_nhds.continuousAt.eventually (hrz ▸ hz0)
    exact ht
  apply hfreq
  filter_upwards [hx0,hround] with x hx hxround
  intro hh
  exact hh.2 (by rw [← hxround hh.1];exact hx)

private theorem coordinatePlane_min (a : ℕ) :
    complexCoordinatePlane n (min a n) = complexCoordinatePlane n a := by
  ext w
  constructor
  · intro h i hi
    exact h i (by omega)
  · intro h i hi
    exact h i (by have := i.isLt;omega)

theorem exists_centered_full_boundary_chart (hn : 0 < n) {C : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n C E) (x : X) (hx : x ∈ C) :
    ∃ a ≤ n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (s : Fin E.length → Fin n),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i, x ∈ E.get i → (s i).val < a) ∧ Set.InjOn s {i | x ∈ E.get i} ∧
      ∀ z ∈ flatDomain Φ,
        (z ∈ C ↔ flatMap Φ z ∈ complexCoordinatePlane n a) ∧
        ∀ i, z ∈ E.get i ↔ x ∈ E.get i ∧ flatCoord Φ (s i) z = 0 := by
  classical
  obtain ⟨a0,b,Φ,s,hsrc,hsa,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl C) hE hT hT.hasNormalCrossings hx
  let e := chartAt (ComplexModel n) x
  let c := Φ.toFun (e x)
  have hc : c ∈ complexCoordinatePlane n b :=
    (hflat (mem_chart_source _ x) Φ.center_mem_source).2.1.mp hx
  have hci : ∀ i, x ∈ E.get i → c (s i) = 0 := fun i hi =>
    (hflat (mem_chart_source _ x) Φ.center_mem_source).2.2 i hi |>.mp hi
  let Ψ := RegularPatchPullback.subConst Φ c
  let inactive : Finset (Fin E.length) := Finset.univ.filter fun i => x ∉ E.get i
  let O : Set X := ⋂ i ∈ inactive, (E.get i)ᶜ
  have hO : IsOpen O := inactive.finite_toSet.isOpen_biInter fun i _ =>
    (hE.1 _ (List.get_mem E i)).isOpen_compl
  have hxO : x ∈ O := by
    simp only [O,mem_iInter]
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  let B : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' O
  have hB : IsOpen B := e.isOpen_inter_preimage_symm hO
  have hxB : e x ∈ B := ⟨e.map_source (mem_chart_source _ x),by
    change e.symm (e x) ∈ O;rw [e.left_inv (mem_chart_source _ x)];exact hxO⟩
  let Θ := Ψ.restrict B hB (e x) ⟨Ψ.center_mem_source,hxB⟩
  refine ⟨min b n,Nat.min_le_right _ _,Θ,s,?_,?_,?_,hinj,?_⟩
  · intro w hw
    exact hsrc hw.1
  · change Φ.toFun (e x)-c = 0
    exact sub_self _
  · intro i hi
    have hs := hsa i hi
    have hsn := (s i).isLt
    omega
  · intro z hz
    have hzΦ : e z ∈ Φ.source := hz.2.1
    have hzB : e z ∈ B := hz.2.2
    have hzO : z ∈ O := by
      have h := hzB.2
      change e.symm (e z) ∈ O at h
      rwa [e.left_inv hz.1] at h
    have hzOld := hflat hz.1 hzΦ
    have hp : flatMap Θ z ∈ complexCoordinatePlane n (min b n) ↔
        Φ.toFun (e z) ∈ complexCoordinatePlane n b := by
      rw [coordinatePlane_min]
      change Φ.toFun (e z)-c ∈ complexCoordinatePlane n b ↔ _
      constructor
      · intro h i hi
        have h0 := h i hi
        have hc0 := hc i hi
        simpa only [PiLp.sub_apply,hc0,sub_zero] using h0
      · intro h i hi
        change Φ.toFun (e z) i-c i = 0
        rw [h i hi,hc i hi,sub_self]
    refine ⟨hzOld.2.1.trans hp.symm,?_⟩
    intro i
    by_cases hxi : x ∈ E.get i
    · have he := hzOld.2.2 i hxi
      have hs0 := hci i hxi
      change z ∈ E.get i ↔ x ∈ E.get i ∧ (Φ.toFun (e z)-c) (s i) = 0
      simpa only [hxi,true_and,PiLp.sub_apply,hs0,sub_zero] using he
    · have hzi : z ∉ E.get i := by
        have hmem : i ∈ inactive := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxi⟩
        exact mem_iInter₂.mp hzO i hmem
      exact ⟨fun h => False.elim (hzi h),fun h => False.elim (hxi h.1)⟩

theorem exists_zero_dim_full_boundary_chart {X0 : CMfd.{u} 0} {C : Set X0}
    {E : List (Set X0)} (hE : IsSNCDivisor 0 E) (hT : IsTransverse 0 C E)
    (x : X0) (hx : x ∈ C) :
    ∃ Φ : LocalHolomorphicEquivAt (n := 0) (chartAt (ComplexModel 0) x x),
      Φ.source ⊆ (chartAt (ComplexModel 0) x).target ∧
      Φ.toFun (chartAt (ComplexModel 0) x x) = 0 ∧
      ∀ z ∈ flatDomain Φ, z ∈ C ∧ ∀ i : Fin E.length, z ∉ E.get i := by
  classical
  have hmiss : ∀ i : Fin E.length, x ∉ E.get i := by
    obtain ⟨S,_,hcard,_⟩ := hE.2 x
    intro i hi
    have hc := hcard i hi
    have hle := Finset.card_le_univ (S i)
    simp only [Fintype.card_fin] at hle
    omega
  obtain ⟨S0,S,⟨Φ,hsrc,h0,hcoord⟩,_⟩ := hT x hx
  let e := chartAt (ComplexModel 0) x
  let O : Set X0 := ⋂ i ∈ (Finset.univ : Finset (Fin E.length)), (E.get i)ᶜ
  have hO : IsOpen O := (Finset.univ : Finset (Fin E.length)).finite_toSet.isOpen_biInter
    fun i _ => (hE.1 _ (List.get_mem E i)).isOpen_compl
  have hxO : x ∈ O := by simp only [O,mem_iInter];exact fun i _ => hmiss i
  let B : Set (ComplexModel 0) := e.target ∩ e.symm ⁻¹' O
  have hB : IsOpen B := e.isOpen_inter_preimage_symm hO
  have hxB : e x ∈ B := ⟨e.map_source (mem_chart_source _ x),by
    change e.symm (e x) ∈ O;rw [e.left_inv (mem_chart_source _ x)];exact hxO⟩
  let Θ := Φ.restrict B hB (e x) ⟨Φ.center_mem_source,hxB⟩
  refine ⟨Θ,fun _ h => hsrc h.1,h0,?_⟩
  intro z hz
  have hzC : z ∈ C := (hcoord none hx hz.1 hz.2.1).mpr
    (by intro j _;exact j.elim0)
  have hzO : z ∈ O := by
    have h := hz.2.2.2
    change e.symm (e z) ∈ O at h
    rwa [e.left_inv hz.1] at h
  exact ⟨hzC,fun i => mem_iInter₂.mp hzO i (Finset.mem_univ i)⟩

theorem exists_actual_indexed_carrier_boundary_chart {C : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n C E) (x : X) (hx : x ∈ C) :
    ∃ a ≤ n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (s : Fin E.length → Option (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i j, s i = some j → j.val < a) ∧ Set.InjOn s {i | x ∈ E.get i} ∧
      ∀ z ∈ flatDomain Φ,
        (z ∈ C ↔ flatMap Φ z ∈ complexCoordinatePlane n a) ∧
        ∀ i, z ∈ E.get i ↔ ∃ j, s i = some j ∧ flatCoord Φ j z = 0 := by
  classical
  by_cases hn : 0 < n
  · obtain ⟨a,ha,Φ,s,hsrc,h0,hs,hinj,hflat⟩ :=
      exists_centered_full_boundary_chart hn hE hT x hx
    let κ : Fin E.length → Option (Fin n) := fun i => if x ∈ E.get i then some (s i) else none
    refine ⟨a,ha,Φ,κ,hsrc,h0,?_,?_,?_⟩
    · intro i j hj
      by_cases hi : x ∈ E.get i
      · have he : s i = j := Option.some.inj (by simpa only [κ,hi,if_pos] using hj)
        rw [← he];exact hs i hi
      · simp only [κ,hi] at hj
        cases hj
    · intro i hi j hj he
      change x ∈ E.get i at hi
      change x ∈ E.get j at hj
      have hsi : s i = s j := Option.some.inj (by simpa only [κ,hi,hj,if_pos] using he)
      exact hinj hi hj hsi
    · intro z hz
      refine ⟨(hflat z hz).1,?_⟩
      intro i
      have he := (hflat z hz).2 i
      by_cases hi : x ∈ E.get i <;> simpa [κ,hi] using he
  · have hzero : n = 0 := by omega
    subst n
    obtain ⟨Φ,hsrc,h0,hflat⟩ := exists_zero_dim_full_boundary_chart hE hT x hx
    refine ⟨0,le_rfl,Φ,fun _ => none,hsrc,h0,?_,?_,?_⟩
    · intro i j _;exact j.elim0
    · intro i hi j _ _
      exact False.elim ((hflat x (mem_flatDomain_self Φ)).2 i hi)
    · intro z hz
      refine ⟨⟨fun _ i _ => i.elim0,fun _ => (hflat z hz).1⟩,?_⟩
      intro i
      exact ⟨fun hi => False.elim ((hflat z hz).2 i hi),fun ⟨j,_,_⟩ => j.elim0⟩

private def translationCoordinates (x : ComplexModel n) : LocalHolomorphicEquivAt (n := n) x where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ x
  toFun := fun w => w-x
  invFun := fun w => w+x
  toFun_holomorphic := (differentiable_id.sub_const x).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const x).differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => sub_add_cancel _ _
  right_inv := fun _ _ => add_sub_cancel_right _ _

def slotBoundary (j : Option (Fin n)) : Set (ComplexModel n) :=
  j.elim ∅ (fun i => {w | w i = 0})

theorem isSNCDivisor_actual_slotBoundary (L : List (Option (Fin n)))
    (hslot : Set.InjOn (fun i : Fin L.length => L.get i) {i | L.get i ≠ none}) :
    IsSNCDivisor n (L.map slotBoundary) := by
  classical
  let E := L.map slotBoundary
  let c : Fin E.length → Fin L.length := Fin.cast (List.length_map slotBoundary)
  let S : Fin E.length → Finset (Fin n) := fun i => (L.get (c i)).elim ∅ (fun j => {j})
  have hget (i : Fin E.length) : E.get i = slotBoundary (L.get (c i)) := by
    simp [E,c,List.get_eq_getElem]
  refine ⟨?_,fun x => ?_⟩
  · intro H hH
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hH
    cases j with
    | none => exact isClosed_empty
    | some j =>
      exact isClosed_eq (continuous_apply j |>.comp (PiLp.continuous_ofLp 2 _)) continuous_const
  · let Φ := translationCoordinates x
    refine ⟨S,⟨Φ,fun _ _ => mem_univ _,?_,?_⟩,?_,?_⟩
    · exact sub_self x
    · intro i hxi y _ _
      change x ∈ E.get i at hxi
      change y ∈ E.get i ↔ Φ.toFun y ∈ coordSubspace (S i)
      rw [hget i] at hxi ⊢
      cases he : L.get (c i) with
      | none => rw [he] at hxi;exact False.elim hxi
      | some j =>
        rw [he] at hxi
        have hxj : x j = 0 := hxi
        have hS : S i = {j} := by
          dsimp only [S]
          rw [he];rfl
        rw [hS,mem_coordSubspace_singleton]
        change y j = 0 ↔ (y-x) j = 0
        simp only [PiLp.sub_apply,hxj,sub_zero]
    · intro i hxi
      change x ∈ E.get i at hxi
      rw [hget i] at hxi
      cases he : L.get (c i) with
      | none => rw [he] at hxi;exact False.elim hxi
      | some j =>
        change ((L.get (c i)).elim ∅ (fun j => ({j} : Finset (Fin n)))).card = 1
        rw [he];exact Finset.card_singleton j
    · intro i hi j hj hS
      change x ∈ E.get i at hi
      change x ∈ E.get j at hj
      rw [hget i] at hi
      rw [hget j] at hj
      cases hei : L.get (c i) with
      | none => rw [hei] at hi;exact False.elim hi
      | some ri =>
        cases hej : L.get (c j) with
        | none => rw [hej] at hj;exact False.elim hj
        | some rj =>
          have hsi : S i = {ri} := by
            dsimp only [S]
            rw [hei];rfl
          have hsj : S j = {rj} := by
            dsimp only [S]
            rw [hej];rfl
          have hsame : ({ri} : Finset (Fin n)) = {rj} := by rwa [hsi,hsj] at hS
          have hrij : ri = rj := Finset.singleton_injective hsame
          have hc : c i = c j := hslot (by change L.get (c i) ≠ none;rw [hei];simp)
            (by change L.get (c j) ≠ none;rw [hej];simp)
            (by change L.get (c i) = L.get (c j);rw [hei,hej,hrij])
          exact Fin.cast_injective _ hc

private def intrinsicSlot {a : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < a) : Option (Fin a) :=
  match s with
  | none => none
  | some j => some ⟨j.val,hs j rfl⟩

private theorem intrinsicSlot_value {a : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < a) :
    Option.map Fin.val (intrinsicSlot s hs) = Option.map Fin.val s := by
  cases s <;> rfl

private theorem intrinsicSlot_injective {a : ℕ} (s t : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < a) (ht : ∀ j, t = some j → j.val < a)
    (h : intrinsicSlot s hs = intrinsicSlot t ht) : s = t := by
  have hv := congrArg (Option.map Fin.val) h
  rw [intrinsicSlot_value,intrinsicSlot_value] at hv
  cases s with
  | none => cases t with
    | none => rfl
    | some j => cases hv
  | some i => cases t with
    | none => cases hv
    | some j => exact congrArg some (Fin.ext (Option.some.inj hv))

private theorem intrinsicSlot_none_iff {a : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < a) : intrinsicSlot s hs = none ↔ s = none := by
  cases s <;> simp [intrinsicSlot]

theorem coordinateInclusion_actual_slotBoundary {a : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < a) (w : ComplexModel a) :
    coordinateInclusion n a w ∈ slotBoundary s ↔ w ∈ slotBoundary (intrinsicSlot s hs) := by
  cases s with
  | none => rfl
  | some j =>
    simp only [intrinsicSlot,slotBoundary,Option.elim_some,mem_ofPred_eq,
      coordinateInclusion_apply,dif_pos (hs j rfl)]

private theorem slotBoundary_mem_iff (s : Option (Fin n)) (w : ComplexModel n) :
    w ∈ slotBoundary s ↔ ∃ j, s = some j ∧ w j = 0 := by
  cases s <;> simp [slotBoundary]

theorem isSNCDivisor_actual_parameter_boundary {a : ℕ} {x : X} {E : List (Set X)}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (κ : Fin E.length → Option (Fin n))
    (hs : ∀ i j, κ i = some j → j.val < a)
    (hinj : Set.InjOn κ {i | x ∈ E.get i})
    (hflat : ∀ z ∈ flatDomain Φ, ∀ i,
      z ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j z = 0) :
    IsSNCDivisor a (E.map (parameterMapOn Φ a ⁻¹' ·)) := by
  classical
  let τ : Fin E.length → Option (Fin a) := fun i => intrinsicSlot (κ i) (hs i)
  let L := List.ofFn τ
  let c : Fin L.length → Fin E.length := Fin.cast (by simp [L])
  have hget (i : Fin L.length) : L.get i = τ (c i) := by
    change (List.ofFn τ).get i = τ (c i)
    rw [List.get_ofFn]
  have hactive (i : Fin E.length) (hi : κ i ≠ none) : x ∈ E.get i := by
    cases he : κ i with
    | none => exact False.elim (hi he)
    | some j =>
      apply (hflat x (mem_flatDomain_self Φ) i).mpr
      refine ⟨j,he,?_⟩
      change Φ.toFun (chartAt (ComplexModel n) x x) j = 0
      rw [h0];rfl
  have hL : Set.InjOn (fun i : Fin L.length => L.get i) {i | L.get i ≠ none} := by
    intro i hi j hj he
    change L.get i ≠ none at hi
    change L.get j ≠ none at hj
    change L.get i = L.get j at he
    rw [hget i,hget j] at he
    rw [hget i] at hi
    rw [hget j] at hj
    have hki : κ (c i) ≠ none := fun hn => hi ((intrinsicSlot_none_iff _ _).mpr hn)
    have hkj : κ (c j) ≠ none := fun hn => hj ((intrinsicSlot_none_iff _ _).mpr hn)
    have hκ : κ (c i) = κ (c j) := intrinsicSlot_injective _ _ _ _ he
    have hc := hinj (hactive _ hki) (hactive _ hkj) hκ
    exact Fin.cast_injective _ hc
  let B := L.map slotBoundary
  have hB : IsSNCDivisor a B := isSNCDivisor_actual_slotBoundary L hL
  have hBE : E.map (parameterMapOn Φ a ⁻¹' ·) = B.map ((Subtype.val : parameterOpen Φ a → ComplexModel a) ⁻¹' ·) := by
    apply List.ext_getElem
    · simp [B,L]
    · intro i hi hi'
      have hiE : i < E.length := by simpa using hi
      simp only [B,L,List.getElem_map,List.getElem_ofFn]
      ext z
      change parameterMapOn Φ a z ∈ E.get ⟨i,hiE⟩ ↔
        z.val ∈ slotBoundary (τ ⟨i,hiE⟩)
      have hd := parameterMap_flat_dictionary Φ a hsrc z.val z.property
      have he : parameterMapOn Φ a z ∈ E.get ⟨i,hiE⟩ ↔
          coordinateInclusion n a z.val ∈ slotBoundary (κ ⟨i,hiE⟩) := by
        change parameterMap Φ a z.val ∈ E.get ⟨i,hiE⟩ ↔
          coordinateInclusion n a z.val ∈ slotBoundary (κ ⟨i,hiE⟩)
        rw [hflat _ hd.1 _,slotBoundary_mem_iff]
        apply exists_congr
        intro j
        apply and_congr_right
        intro _
        change flatMap Φ (parameterMap Φ a z.val) j = 0 ↔
          coordinateInclusion n a z.val j = 0
        rw [hd.2]
      exact he.trans (coordinateInclusion_actual_slotBoundary _ _ z.val)
  rw [hBE]
  exact NormalCrossingsInvariance.isSNCDivisor_map_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_val (parameterOpen Φ a)) continuous_subtype_val hB

theorem actual_intrinsic_marked_carrier {a : ℕ} {x : X} (M : MarkedIdeal n X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (ha : a ≤ n) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hN : ∀ z ∈ flatDomain Φ, z ∈ M.N ↔ flatMap Φ z ∈ complexCoordinatePlane n a) :
    (markedPullback (m := a) (parameterMapOn Φ a) M).N = univ := by
  ext z
  exact ⟨fun _ => mem_univ _,fun _ =>
    (actual_parameter_retraction_geometry Φ ha hsrc M.N hN z).1 z⟩

theorem whole_actual_intrinsic_marked_dictionary {a : ℕ} {x : X} (M : MarkedIdeal n X)
    (hI : M.ideal.IsCoherent)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (ha : a ≤ n) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hN : ∀ z ∈ flatDomain Φ, z ∈ M.N ↔ flatMap Φ z ∈ complexCoordinatePlane n a) :
    let J := markedPullback (m := a) (parameterMapOn Φ a) M
    J.N = univ ∧ J.E = M.E.map (parameterMapOn Φ a ⁻¹' ·) ∧
    J.ideal = GermIdeal.pullback (m := a) (parameterMapOn Φ a) M.ideal ∧ J.d = M.d ∧
    (∀ z : parameterOpen Φ a, GermIdealOrder.order a J.N J.ideal z =
      GermIdealOrder.order n M.N M.ideal (parameterMapOn Φ a z)) ∧
    J.cosupp = parameterMapOn Φ a ⁻¹' M.cosupp := by
  dsimp only
  have hN' := actual_intrinsic_marked_carrier M Φ ha hsrc hN
  refine ⟨hN',rfl,rfl,rfl,?_,?_⟩
  · intro z
    rw [hN']
    exact actual_parameter_extended_order Φ ha hsrc M.N hN M.ideal hI z
  · change cosupport a (markedPullback (m := a) (parameterMapOn Φ a) M).N
        (GermIdeal.pullback (m := a) (parameterMapOn Φ a) M.ideal) M.d =
      parameterMapOn Φ a ⁻¹' cosupport n M.N M.ideal M.d
    rw [hN']
    exact actual_parameter_cosupport Φ ha hsrc M.N hN M.ideal hI M.d

theorem isInvDomain_actual_intrinsic_marked_model {a k : ℕ} {x : X}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (hx : x ∈ M.N)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (ha : a ≤ n) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hN : ∀ z ∈ flatDomain Φ, z ∈ M.N ↔ flatMap Φ z ∈ complexCoordinatePlane n a)
    (κ : Fin M.E.length → Option (Fin n))
    (hs : ∀ i j, κ i = some j → j.val < a)
    (hinj : Set.InjOn κ {i | x ∈ M.E.get i})
    (hE : ∀ z ∈ flatDomain Φ, ∀ i,
      z ∈ M.E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j z = 0) :
    IsInvDomain k (markedPullback (m := a) (parameterMapOn Φ a) M) := by
  let J := markedPullback (m := a) (parameterMapOn Φ a) M
  have hN' : J.N = univ := actual_intrinsic_marked_carrier M Φ ha hsrc hN
  have hσ := parameterMapOn_contMDiff Φ a hsrc
  have hSNC : IsSNCDivisor a J.E := isSNCDivisor_actual_parameter_boundary Φ hsrc h0 κ hs hinj hE
  have hreg : RegularAtDim (n := n) M.N x a :=
    ⟨ha,hx,Φ,hsrc,h0,fun hy hyΦ => hN _ ⟨hy,hyΦ⟩⟩
  obtain ⟨j,hjk,hj⟩ := hM.dimLE x hx
  have haj := RegularPointDimension.eq_of_regularAtDim hreg hj
  have hak : a ≤ k := by omega
  have hWF : J.IsWellFormed := by
    refine ⟨?_,GermIdealPullbackCalculus.isCoherent_pullback hσ hM.isWellFormed.isCoherent,hSNC,?_⟩
    · rw [hN']
      exact HomogenizedGlueingTower.isClosedSubmanifold_univ
    · rw [hN']
      exact isTransverse_univ_of_isSNCDivisor hSNC
  refine ⟨hWF,?_,hM.one_le_d,?_⟩
  · intro z _
    refine ⟨a,hak,?_⟩
    rw [hN']
    exact AnalyticIrreducibleComponents.regularAtDim_univ z
  · intro z _
    have hgeom := actual_parameter_retraction_geometry Φ ha hsrc M.N hN z
    have hσat : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel n)
        (parameterMapOn Φ a) w := Eventually.of_forall fun w => (hσ w).mdifferentiableAt (by simp)
    rw [hN']
    exact whole_nonzero_of_actual_local_retraction (X := X)
      (Y := CMfd.of (n := a) (parameterOpen Φ a)) (σ := parameterMapOn Φ a)
      (r := actualParameterRetraction Φ a z) (C := M.N) (z := z)
      hσat hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2 M.ideal hM.isWellFormed.isCoherent
      (hM.isNonzeroAlongAt (parameterMapOn Φ a z) (hgeom.1 z))

private def OriginalIntrinsicModel {k : ℕ} (M : MarkedIdeal n X) (x : X) : Prop :=
  ∃ a ≤ n, ∃ Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
    Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
    Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
    (∃ z : parameterOpen Φ a, z.val = 0 ∧ parameterMapOn Φ a z = x) ∧
    IsInvDomain k (markedPullback (m := a) (parameterMapOn Φ a) M) ∧
    let J := markedPullback (m := a) (parameterMapOn Φ a) M
    J.N = univ ∧ J.E = M.E.map (parameterMapOn Φ a ⁻¹' ·) ∧
    J.ideal = GermIdeal.pullback (m := a) (parameterMapOn Φ a) M.ideal ∧ J.d = M.d ∧
    (∀ z : parameterOpen Φ a, order a J.N J.ideal z = order n M.N M.ideal (parameterMapOn Φ a z)) ∧
    J.cosupp = parameterMapOn Φ a ⁻¹' M.cosupp

theorem exists_original_intrinsic_marked_model {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (x : X) (hx : x ∈ M.N) : OriginalIntrinsicModel (k := k) M x := by
  obtain ⟨a,ha,Φ,κ,hsrc,h0,hs,hinj,hflat⟩ :=
    exists_actual_indexed_carrier_boundary_chart hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse x hx
  have hN : ∀ z ∈ flatDomain Φ, z ∈ M.N ↔ flatMap Φ z ∈ complexCoordinatePlane n a :=
    fun z hz => (hflat z hz).1
  have hE : ∀ z ∈ flatDomain Φ, ∀ i,
      z ∈ M.E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j z = 0 := fun z hz => (hflat z hz).2
  have hJ := isInvDomain_actual_intrinsic_marked_model M hM hx Φ ha hsrc h0 hN κ hs hinj hE
  have hp := parameterMap_zero Φ a h0
  let z : parameterOpen Φ a := ⟨0,hp.1⟩
  refine ⟨a,ha,Φ,hsrc,h0,⟨z,rfl,hp.2⟩,hJ,?_⟩
  exact whole_actual_intrinsic_marked_dictionary M hM.isWellFormed.isCoherent Φ ha hsrc hN

theorem original_zero_lower_boundary_dictionary {D : CMfd.{u} n}
    (M : MarkedIdeal n X) (T : BlowupTower X D) (y : D) :
    (lowerMarked M 0 T y).E =
      ((geoTransformAlong (barMarked M) T).E.drop M.E.length).map
        ((Subtype.val : maskB M T y → D) ⁻¹' ·) := by
  change (geoTransformAlong (stepOneMarked M.N M.ideal M.d) T).E.map
      ((Subtype.val : maskB M T y → D) ⁻¹' ·) = _
  have he := congrArg (fun J : MarkedIdeal n D => J.E) (geoTransformAlong_coeffHom_dropE M T)
  rw [he]

theorem exists_original_zero_lower_intrinsic_marked_model {k : ℕ} {D : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower (barMarked M) T)
    (y : D) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp)
    (x : lowerMask M 0 T y) (hx : x ∈ (lowerMarked M 0 T y).N) :
    OriginalIntrinsicModel (X := CMfd.of (n := n) (lowerMask M 0 T y))
      (k := k-1) (lowerMarked M 0 T y) x := by
  have hd := StepOneLowerDomain.isInvDomain_lowerMarked_zero M hM.isWellFormed hM.one_le_d
    hmax T hT hM.dimLE hy
  exact exists_original_intrinsic_marked_model (X := CMfd.of (n := n) (lowerMask M 0 T y))
    (lowerMarked M 0 T y) hd x hx

end
end Hironaka.HironakaIntrinsicCarrierBoundaryCharts

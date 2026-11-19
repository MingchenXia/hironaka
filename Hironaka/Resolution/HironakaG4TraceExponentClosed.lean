import Hironaka.Resolution.HironakaG4SingleBornTrace
import Hironaka.Resolution.HironakaG4FiniteTraceComponents
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4TraceExponentClosed
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG4SingleBornTrace
  NormalCrossings NormalCrossingsComparison HironakaSharpOriginalProductTraceOrder
  HironakaG4PreparedCentreCoordinates HironakaG4CompactWholeMonomialMaskPhase
variable {n : ℕ} {X : CMfd.{u} n}

/-- The positive superlevel sets of a trace-locally-constant exponent are closed. -/
theorem closed_positive_trace_superlevel {T : Set X} (hT : IsClosed T) (f : X → ℕ)
    (hzero : ∀ x ∉ T, f x = 0)
    (hloc : ∀ x ∈ T, ∀ᶠ y in 𝓝 x, y ∈ T → f y = f x)
    (k : ℕ) (hk : 0 < k) : IsClosed {x | k ≤ f x} := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxt : x ∈ T
  · filter_upwards [hloc x hxt] with y hy
    change ¬ k ≤ f y
    by_cases hyt : y ∈ T
    · rw [hy hyt]
      exact hx
    · rw [hzero y hyt]
      omega
  · have hopen : Tᶜ ∈ 𝓝 x := hT.isOpen_compl.mem_nhds hxt
    filter_upwards [hopen] with y hy
    change ¬ k ≤ f y
    rw [hzero y hy]
    omega
/-- Actual boundary-slot exponent superlevels are closed under the ordinary
coherence, transversality and nonzero-along assumptions. -/
theorem actual_positive_exponent_superlevel_closed (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y)
    (i : Fin M.E.length) (k : ℕ) (hk : 0 < k) :
    IsClosed {x | k ≤ divExpAlong n M.N M.ideal (M.E.get i) x} := by
  let T := M.N ∩ M.E.get i
  have hT : IsClosed T := hM.isClosedSubmanifold_N.1.inter (hM.isSNCDivisor.1 _ (List.get_mem M.E i))
  apply closed_positive_trace_superlevel hT _
  · intro x hx
    exact exponent_zero_off_trace hT hx
  · intro x hx
    have he := eventually_divExpAlong_get_eq hn hM.isClosedSubmanifold_N hM.isSNCDivisor
      hM.isTransverse hM.isCoherent hne i hx.1 hx.2
    filter_upwards [he] with y hy hyt
    exact hy hyt.1 hyt.2
  · exact hk
/-- Any fixed componentwise lower bound on a finite row family defines a
closed set on the carrier, including zero entries of the bound. -/
theorem actual_matrix_upper_set_closed {ι : Type*} (hn : 0 < n)
    (N : Set X) (E : List (Set X)) (I : ι → GermIdeal n X)
    (hM : ∀ i, (⟨N,E,I i,1⟩ : MarkedIdeal n X).IsWellFormed)
    (hne : ∀ i y, y ∈ N → IsNonzeroAlongAt N (I i) y)
    (a : ι → Fin E.length → ℕ) :
    IsClosed {x | ∀ i j, a i j ≤ divExpAlong n N (I i) (E.get j) x} := by
  have heq : {x | ∀ i j, a i j ≤ divExpAlong n N (I i) (E.get j) x} =
      ⋂ i, ⋂ j, {x | a i j ≤ divExpAlong n N (I i) (E.get j) x} := by
    ext x
    simp only [mem_ofPred_eq,mem_iInter]
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  by_cases hz : a i j = 0
  · simp [hz]
  · exact actual_positive_exponent_superlevel_closed hn ⟨N,E,I i,1⟩ (hM i) (hne i) j (a i j) (Nat.pos_of_ne_zero hz)
/-- The actual original-row exponent matrix has closed componentwise upper
sets under the standard source geometry. -/
theorem actual_old_matrix_upper_set_closed (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (a : Fin old.length → Fin born.length → ℕ) :
    IsClosed {x | ∀ i j, a i j ≤ divExpAlong n N (oldMonomialPart N old born i) (born.get j) x} := by
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  apply actual_matrix_upper_set_closed hn N born (oldMonomialPart N old born)
  · intro i
    have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
    exact ⟨hN,hParts.2.2.2.2.1,hBorn,hTr⟩
  · intro i y hy
    have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
    exact hParts.2.2.2.2.2.1 y hy
/-- On a closed set with a uniform finite bound, every upward-closed
predicate in the matrix entries has closed actual locus. -/
theorem bounded_upward_predicate_closed {ι : Type*} [Fintype ι]
    (K : Set X) (hK : IsClosed K) (f : X → ι → ℕ) (B : ℕ)
    (hB : ∀ x ∈ K, ∀ i, f x i ≤ B)
    (hClosed : ∀ a : ι → ℕ, IsClosed {x | ∀ i, a i ≤ f x i})
    (P : (ι → ℕ) → Prop)
    (hP : ∀ a b, (∀ i, a i ≤ b i) → P a → P b) :
    IsClosed {x | x ∈ K ∧ P (f x)} := by
  let Q := {c : ι → Fin (B+1) // P (fun i => (c i).val)}
  let U : Q → Set X := fun c => K ∩ {x | ∀ i, (c.val i).val ≤ f x i}
  have heq : {x | x ∈ K ∧ P (f x)} = ⋃ c : Q, U c := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion]
    constructor
    · rintro ⟨hx,hpx⟩
      let c : ι → Fin (B+1) := fun i => ⟨f x i, Nat.lt_succ_of_le (hB x hx i)⟩
      refine ⟨⟨c,?_⟩,hx,?_⟩
      · exact hpx
      · intro i
        exact le_rfl
    · rintro ⟨c,hx,hxc⟩
      exact ⟨hx,hP _ _ hxc c.property⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun c => hK.inter (hClosed _))
/-- On any closed uniformly bounded part of the actual carrier, an
entrywise upward-closed matrix predicate has a closed locus. -/
theorem actual_bounded_upward_predicate_closed (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (K : Set X) (hK : IsClosed K) (B : ℕ)
    (hB : ∀ x ∈ K, ∀ i j, divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B)
    (P : (Fin old.length × Fin born.length → ℕ) → Prop)
    (hP : ∀ a b, (∀ i, a i ≤ b i) → P a → P b) :
    IsClosed {x | x ∈ K ∧ P (fun ij => divExpAlong n N (oldMonomialPart N old born ij.1) (born.get ij.2) x)} := by
  apply bounded_upward_predicate_closed K hK _ B
  · intro x hx ij
    exact hB x hx ij.1 ij.2
  · intro a
    have h := actual_old_matrix_upper_set_closed hn hN hE hTr hdense (fun i j => a (i,j))
    convert h using 1
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · intro hx i j
      exact hx (i,j)
    · intro hx ij
      exact hx ij.1 ij.2
  · exact hP
/-- A componentwise maximal matrix has closed exact fibre on a
closed set, even though arbitrary exact fibres need not be closed. -/
theorem maximal_matrix_fibre_closed {ι : Type*} (K : Set X) (hK : IsClosed K)
    (f : X → ι → ℕ) (a : ι → ℕ)
    (hUpper : IsClosed {x | ∀ i, a i ≤ f x i})
    (hMax : ∀ x ∈ K, (∀ i, a i ≤ f x i) → f x = a) :
    IsClosed {x | x ∈ K ∧ f x = a} := by
  have heq : {x | x ∈ K ∧ f x = a} = K ∩ {x | ∀ i, a i ≤ f x i} := by
    ext x
    constructor
    · rintro ⟨hx,hf⟩
      exact ⟨hx,fun i => by rw [hf]⟩
    · rintro ⟨hx,ha⟩
      exact ⟨hx,hMax x hx ha⟩
  rw [heq]
  exact hK.inter hUpper
/-- Exact fibres of componentwise maximal actual original-row matrices are
closed on any closed source subset. -/
theorem actual_maximal_matrix_fibre_closed (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (K : Set X) (hK : IsClosed K) (a : Fin old.length → Fin born.length → ℕ)
    (hMax : ∀ x ∈ K,
      (∀ i j, a i j ≤ divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) →
      (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) = a) :
    IsClosed {x | x ∈ K ∧
      (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) = a} := by
  have heq : {x | x ∈ K ∧
      (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) = a} =
      K ∩ {x | ∀ i j, a i j ≤ divExpAlong n N (oldMonomialPart N old born i) (born.get j) x} := by
    ext x
    constructor
    · rintro ⟨hx,hf⟩
      refine ⟨hx,?_⟩
      intro i j
      have he := congrFun (congrFun hf i) j
      rw [he]
    · rintro ⟨hx,ha⟩
      exact ⟨hx,hMax x hx ha⟩
  rw [heq]
  exact hK.inter (actual_old_matrix_upper_set_closed hn hN hE hTr hdense a)
/-- A nonempty uniformly bounded family of finite matrices has an attained
componentwise maximal value. -/
theorem exists_bounded_maximal_matrix {ι : Type*} [Fintype ι] (K : Set X)
    (hK : K.Nonempty) (f : X → ι → ℕ) (B : ℕ)
    (hB : ∀ x ∈ K, ∀ i, f x i ≤ B) :
    ∃ p ∈ K, ∀ x ∈ K, (∀ i, f p i ≤ f x i) → f x = f p := by
  let encode : (ι → Fin (B+1)) → (ι → ℕ) := fun c i => (c i).val
  have hfinite : (f '' K).Finite := by
    apply (Set.finite_range encode).subset
    rintro a ⟨x,hx,rfl⟩
    refine ⟨fun i => ⟨f x i, Nat.lt_succ_of_le (hB x hx i)⟩,?_⟩
    rfl
  have hne : (f '' K).Nonempty := hK.image f
  obtain ⟨a,⟨p,hp,rfl⟩,hmax⟩ := hfinite.exists_maximal hne
  refine ⟨p,hp,?_⟩
  intro x hx hle
  apply le_antisymm
  · exact hmax ⟨x,hx,rfl⟩ hle
  · exact hle
/-- On a nonempty closed bounded source subset, an attained componentwise
maximal original-row matrix has a closed nonempty exact fibre. -/
theorem exists_actual_bounded_maximal_matrix_fibre (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (K : Set X) (hK : IsClosed K) (hne : K.Nonempty) (B : ℕ)
    (hB : ∀ x ∈ K, ∀ i j, divExpAlong n N (oldMonomialPart N old born i) (born.get j) x ≤ B) :
    let A := fun x i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
    ∃ p ∈ K, (∀ x ∈ K, (∀ i j, A p i j ≤ A x i j) → A x = A p) ∧
      IsClosed {x | x ∈ K ∧ A x = A p} := by
  let A := fun x i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x
  let f : X → Fin old.length × Fin born.length → ℕ := fun x ij => A x ij.1 ij.2
  have hBound : ∀ x ∈ K, ∀ ij, f x ij ≤ B := fun x hx ij => hB x hx ij.1 ij.2
  obtain ⟨p,hp,hmax⟩ := exists_bounded_maximal_matrix K hne f B hBound
  have hMax : ∀ x ∈ K, (∀ i j, A p i j ≤ A x i j) → A x = A p := by
    intro x hx hle
    have he := hmax x hx (fun ij => hle ij.1 ij.2)
    funext i j
    exact congrFun he (i,j)
  exact ⟨p,hp,hMax,actual_maximal_matrix_fibre_closed hn hN hE hTr hdense K hK (A p) hMax⟩
end
end Hironaka.HironakaG4TraceExponentClosed

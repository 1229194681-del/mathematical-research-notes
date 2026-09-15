import Mathlib


/-! ==================== Core.lean ==================== -/

namespace Scottish164

/-- First and last indices of a nonempty `Fin n`. -/
def firstIdx {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

def lastIdx {n : ℕ} (hn : 0 < n) : Fin n := ⟨n-1, by omega⟩


/-- Generic form of a permissible move for a finite state type with an explicitly
    supplied physical nearest-neighbor relation.  This is used for the block
    constructions before transporting them to a `Fin` indexing. -/
def GMove {α : Type*} (adj : α → α → Prop) (T : α → α) (x y : α) : Prop :=
  y = T x ∨ adj (T x) y

inductive GReachAt {α : Type*} (adj : α → α → Prop) (T : α → α) : ℕ → α → α → Prop
  | refl (x : α) : GReachAt adj T 0 x x
  | tail {m : ℕ} {x y z : α} :
      GReachAt adj T m x y → GMove adj T y z → GReachAt adj T (m+1) x z

namespace GReachAt

lemma one_of_move {α : Type*} {adj : α → α → Prop} {T : α → α} {x y : α}
    (h : GMove adj T x y) : GReachAt adj T 1 x y := by
  exact GReachAt.tail (GReachAt.refl x) h

lemma exact {α : Type*} (adj : α → α → Prop) (T : α → α) (x : α) :
    GReachAt adj T 1 x (T x) := by
  exact one_of_move (Or.inl rfl)

end GReachAt

/-- Generic escape-within predicate for an explicitly ranked/adjacent finite line. -/
def GEscapesWithin {α : Type*} (pos : α → ℝ) (adj : α → α → Prop) (T : α → α)
    (ρ : ℝ) (m : ℕ) (x : α) : Prop :=
  ∃ k ≤ m, ∃ y : α, GReachAt adj T k x y ∧ |pos y - pos x| ≥ ρ

def GAllSlow {α : Type*} (pos : α → ℝ) (adj : α → α → Prop) (T : α → α)
    (ρ : ℝ) (L : ℕ) : Prop :=
  ∀ x : α, ¬ GEscapesWithin pos adj T ρ L x

/-- Physical adjacency for a finite ordered list indexed by `Fin n`. -/
def Adj {n : ℕ} (i j : Fin n) : Prop :=
  i.1 + 1 = j.1 ∨ j.1 + 1 = i.1

lemma adj_symm {n : ℕ} {i j : Fin n} : Adj i j ↔ Adj j i := by
  constructor <;> intro h <;> rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

/-- A permissible one-step move: exact image or a physical nearest neighbor of the image. -/
def Move {n : ℕ} (T : Fin n → Fin n) (i j : Fin n) : Prop :=
  j = T i ∨ Adj (T i) j

lemma exact_move {n : ℕ} (T : Fin n → Fin n) (i : Fin n) : Move T i (T i) := by
  exact Or.inl rfl

/-- Reachability in exactly `m` permissible steps. -/
inductive ReachAt {n : ℕ} (T : Fin n → Fin n) : ℕ → Fin n → Fin n → Prop
  | refl (x : Fin n) : ReachAt T 0 x x
  | tail {m : ℕ} {x y z : Fin n} : ReachAt T m x y → Move T y z → ReachAt T (m+1) x z

namespace ReachAt

lemma one_of_move {n : ℕ} {T : Fin n → Fin n} {x y : Fin n} (h : Move T x y) :
    ReachAt T 1 x y := by
  exact ReachAt.tail (ReachAt.refl x) h

lemma one_exact {n : ℕ} (T : Fin n → Fin n) (x : Fin n) :
    ReachAt T 1 x (T x) := by
  exact one_of_move (exact_move T x)

lemma two_exact {n : ℕ} (T : Fin n → Fin n) (x : Fin n) :
    ReachAt T 2 x (T (T x)) := by
  exact ReachAt.tail (one_exact T x) (exact_move T (T x))

lemma append {n : ℕ} {T : Fin n → Fin n} {a b c : Fin n} {m k : ℕ}
    (h₁ : ReachAt T m a b) (h₂ : ReachAt T k b c) : ReachAt T (m+k) a c := by
  induction h₂ with
  | refl _ => simpa using h₁
  | @tail k b y z hby hyz ih =>
      simpa [Nat.add_assoc] using ReachAt.tail (ih h₁) hyz

end ReachAt

/-- Escape within `m` steps from the starting point `x`. -/
def EscapesWithin {n : ℕ} (pos : Fin n → ℝ) (T : Fin n → Fin n)
    (ρ : ℝ) (m : ℕ) (x : Fin n) : Prop :=
  ∃ k ≤ m, ∃ y : Fin n, ReachAt T k x y ∧ |pos y - pos x| ≥ ρ

/-- No reachable point, at any finite time, gets `ρ` away from its start. -/
def PermanentTrap {n : ℕ} (pos : Fin n → ℝ) (T : Fin n → Fin n) (ρ : ℝ) : Prop :=
  ∀ x : Fin n, ∀ m : ℕ, ∀ y : Fin n, ReachAt T m x y → |pos y - pos x| < ρ

/-- Every start needs more than `L` steps to escape radius `ρ`. -/
def AllSlow {n : ℕ} (pos : Fin n → ℝ) (T : Fin n → Fin n)
    (ρ : ℝ) (L : ℕ) : Prop :=
  ∀ x : Fin n, ¬ EscapesWithin pos T ρ L x

/-- The displacement condition in Problem 164. -/
def JumpCondition {n : ℕ} (pos : Fin n → ℝ) (T : Fin n → Fin n) (ε : ℝ) : Prop :=
  ∀ x : Fin n, |pos (T x) - pos x| > ε

/-- Ordered positions. -/
def Ordered {n : ℕ} (pos : Fin n → ℝ) : Prop := StrictMono pos

lemma no_escape_one_exact {n : ℕ} {pos : Fin n → ℝ} {T : Fin n → Fin n}
    {ρ : ℝ} {x : Fin n}
    (h : ¬ EscapesWithin pos T ρ 1 x) :
    |pos (T x) - pos x| < ρ := by
  by_contra hnot
  have hge : |pos (T x) - pos x| ≥ ρ := le_of_not_gt hnot
  apply h
  refine ⟨1, by omega, T x, ReachAt.one_exact T x, hge⟩

lemma no_escape_two_exact {n : ℕ} {pos : Fin n → ℝ} {T : Fin n → Fin n}
    {ρ : ℝ} {x : Fin n}
    (h : ¬ EscapesWithin pos T ρ 2 x) :
    |pos (T (T x)) - pos x| < ρ := by
  by_contra hnot
  have hge : |pos (T (T x)) - pos x| ≥ ρ := le_of_not_gt hnot
  apply h
  refine ⟨2, by omega, T (T x), ReachAt.two_exact T x, hge⟩

lemma no_escape_of_reach {n : ℕ} {pos : Fin n → ℝ} {T : Fin n → Fin n}
    {ρ : ℝ} {m : ℕ} {x y : Fin n}
    (hno : ¬ EscapesWithin pos T ρ m x)
    (hreach : ReachAt T m x y) : |pos y - pos x| < ρ := by
  by_contra hnot
  have hge : |pos y - pos x| ≥ ρ := le_of_not_gt hnot
  apply hno
  exact ⟨m, le_rfl, y, hreach, hge⟩

end Scottish164

/-! ==================== Literal.lean ==================== -/

namespace Scottish164

noncomputable section

private def trapA (ε : ℝ) : ℝ := (ε + (1/3 : ℝ)) / 2
private def trapB (ε : ℝ) : ℝ := (trapA ε + (1/3 : ℝ)) / 2

/-- The six ordered positions of the permanent trap. -/
def literalTrapPos (ε : ℝ) : Fin 6 → ℝ :=
  ![0, trapA ε, trapB ε, 1 - trapB ε, 1 - trapA ε, 1]

/-- The non-injective map used in the six-point trap. -/
def literalTrapT : Fin 6 → Fin 6 :=
  ![1, 0, 0, 5, 5, 4]

private lemma trap_parameters {ε : ℝ} (_hε0 : 0 < ε) (hε : ε < 1/3) :
    ε < trapA ε ∧ trapA ε < trapB ε ∧ trapB ε < 1/3 := by
  dsimp [trapA, trapB]
  constructor
  · linarith
  constructor <;> linarith

lemma literalTrap_ordered {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3) :
    Ordered (literalTrapPos ε) := by
  have hp := trap_parameters hε0 hε
  rcases hp with ⟨hea, hab, hb⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [literalTrapPos, trapA, trapB] <;> linarith

lemma literalTrap_endpoints (ε : ℝ) :
    literalTrapPos ε 0 = 0 ∧ literalTrapPos ε 5 = 1 := by
  simp [literalTrapPos]

lemma literalTrap_jump {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3) :
    JumpCondition (literalTrapPos ε) literalTrapT ε := by
  have hp := trap_parameters hε0 hε
  rcases hp with ⟨hea, hab, hb⟩
  have ha0 : 0 < trapA ε := lt_trans hε0 hea
  have hb0 : 0 < trapB ε := lt_trans ha0 hab
  intro i
  fin_cases i
  · simp [literalTrapPos, literalTrapT, abs_of_pos ha0]
    exact hea
  · simp [literalTrapPos, literalTrapT, abs_of_neg (neg_lt_zero.mpr ha0)]
    exact hea
  · simp [literalTrapPos, literalTrapT, abs_of_neg (neg_lt_zero.mpr hb0)]
    exact lt_trans hea hab
  · have : 0 < trapB ε := hb0
    simp [literalTrapPos, literalTrapT, abs_of_pos this]
    exact lt_trans hea hab
  · have : 0 < trapA ε := ha0
    simp [literalTrapPos, literalTrapT, abs_of_pos this]
    exact hea
  · simp [literalTrapPos, literalTrapT, abs_of_neg (neg_lt_zero.mpr ha0)]
    exact hea

private def LeftTrap (i : Fin 6) : Prop := i.1 ≤ 2
private def RightTrap (i : Fin 6) : Prop := 3 ≤ i.1

private lemma trap_move_left {i j : Fin 6} (hi : LeftTrap i)
    (h : Move literalTrapT i j) : LeftTrap j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [LeftTrap, Move, Adj, literalTrapT]

private lemma trap_move_right {i j : Fin 6} (hi : RightTrap i)
    (h : Move literalTrapT i j) : RightTrap j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [RightTrap, Move, Adj, literalTrapT]

private lemma trap_reach_left {m : ℕ} {i j : Fin 6} (hi : LeftTrap i)
    (h : ReachAt literalTrapT m i j) : LeftTrap j := by
  induction h with
  | refl x => simpa using hi
  | @tail m x y z hxy hyz ih =>
      exact trap_move_left (ih hi) hyz

private lemma trap_reach_right {m : ℕ} {i j : Fin 6} (hi : RightTrap i)
    (h : ReachAt literalTrapT m i j) : RightTrap j := by
  induction h with
  | refl x => simpa using hi
  | @tail m x y z hxy hyz ih =>
      exact trap_move_right (ih hi) hyz

private lemma left_trap_bounds {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3)
    {i : Fin 6} (hi : LeftTrap i) :
    0 ≤ literalTrapPos ε i ∧ literalTrapPos ε i < 1/3 := by
  rcases trap_parameters hε0 hε with ⟨hea, hab, hb⟩
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i <;> simp_all [LeftTrap]
  rcases hi_cases with rfl | rfl | rfl
  · change 0 ≤ (0 : ℝ) ∧ (0 : ℝ) < 1/3
    norm_num
  · change 0 ≤ trapA ε ∧ trapA ε < 1/3
    exact ⟨le_of_lt (lt_trans hε0 hea), lt_trans hab hb⟩
  · change 0 ≤ trapB ε ∧ trapB ε < 1/3
    exact ⟨le_of_lt (lt_trans (lt_trans hε0 hea) hab), hb⟩

private lemma right_trap_bounds {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3)
    {i : Fin 6} (hi : RightTrap i) :
    2/3 < literalTrapPos ε i ∧ literalTrapPos ε i ≤ 1 := by
  rcases trap_parameters hε0 hε with ⟨hea, hab, hb⟩
  have hi_cases : i = 3 ∨ i = 4 ∨ i = 5 := by
    fin_cases i <;> simp_all [RightTrap]
  rcases hi_cases with rfl | rfl | rfl
  · change 2/3 < 1 - trapB ε ∧ 1 - trapB ε ≤ 1
    constructor <;> linarith
  · change 2/3 < 1 - trapA ε ∧ 1 - trapA ε ≤ 1
    constructor <;> linarith
  · change 2/3 < (1 : ℝ) ∧ (1 : ℝ) ≤ 1
    norm_num

private lemma left_trap_diameter {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3)
    {i j : Fin 6} (hi : LeftTrap i) (hj : LeftTrap j) :
    |literalTrapPos ε j - literalTrapPos ε i| < 1/3 := by
  rcases left_trap_bounds hε0 hε hi with ⟨hi0, hi3⟩
  rcases left_trap_bounds hε0 hε hj with ⟨hj0, hj3⟩
  rw [abs_lt]
  constructor <;> linarith

private lemma right_trap_diameter {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3)
    {i j : Fin 6} (hi : RightTrap i) (hj : RightTrap j) :
    |literalTrapPos ε j - literalTrapPos ε i| < 1/3 := by
  rcases right_trap_bounds hε0 hε hi with ⟨hi23, hi1⟩
  rcases right_trap_bounds hε0 hε hj with ⟨hj23, hj1⟩
  rw [abs_lt]
  constructor <;> linarith

/-- Theorem 2.1 in the paper: a six-point permanent trap for every `0 < ε < 1/3`. -/
theorem literal_permanent_trap (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1/3) :
    Ordered (literalTrapPos ε) ∧
    literalTrapPos ε 0 = 0 ∧ literalTrapPos ε 5 = 1 ∧
    JumpCondition (literalTrapPos ε) literalTrapT ε ∧
    PermanentTrap (literalTrapPos ε) literalTrapT (1/3) := by
  refine ⟨literalTrap_ordered hε0 hε, ?_, ?_, literalTrap_jump hε0 hε, ?_⟩
  · simp [literalTrapPos]
  · simp [literalTrapPos]
  · intro x m y hreach
    by_cases hx : LeftTrap x
    · exact left_trap_diameter hε0 hε hx (trap_reach_left hx hreach)
    · have hxR : RightTrap x := by
        unfold LeftTrap RightTrap at *
        omega
      exact right_trap_diameter hε0 hε hxR (trap_reach_right hxR hreach)

/-- At `ε ≥ 1/3` every exact `T`-move is already an escape. -/
theorem literal_large_epsilon_one_step {n : ℕ} (pos : Fin n → ℝ) (T : Fin n → Fin n)
    (ε : ℝ) (hε : (1/3 : ℝ) ≤ ε) (hj : JumpCondition pos T ε) :
    ∀ x : Fin n, EscapesWithin pos T (1/3) 1 x := by
  intro x
  refine ⟨1, by omega, T x, ReachAt.one_exact T x, ?_⟩
  have hx := hj x
  linarith

/-- A cardinality form of the six-point minimality argument.
    We formulate it for an ordered list with first point `0` and last point `1`. -/
theorem six_points_necessary
    {n : ℕ} (hn : 2 ≤ n) (pos : Fin n → ℝ) (T : Fin n → Fin n)
    (hord : Ordered pos)
    (hzero : pos ⟨0, by omega⟩ = 0)
    (hone : pos ⟨n-1, by omega⟩ = 1)
    (ε : ℝ) (hε0 : 0 < ε)
    (hjump : JumpCondition pos T ε)
    (hno : ∀ x : Fin n, ¬ EscapesWithin pos T (1/3) 1 x) :
    6 ≤ n := by
  let z0 : Fin n := ⟨0, by omega⟩
  let zn : Fin n := ⟨n-1, by omega⟩
  have hT0_ne : T z0 ≠ z0 := by
    intro h
    have := hjump z0
    simp [h] at this
    linarith
  have hz0_lt_T0 : z0 < T z0 := by
    have hval : (T z0).1 ≠ 0 := by
      intro hv
      apply hT0_ne
      apply Fin.ext
      simpa [z0] using hv
    change 0 < (T z0).1
    omega
  have hT0pos : 0 < pos (T z0) := by
    rw [← hzero]
    exact hord hz0_lt_T0
  have hT0small : pos (T z0) < 1/3 := by
    have h := no_escape_one_exact (hno z0)
    rw [abs_of_pos] at h
    · simpa [z0, hzero] using h
    · simpa [z0, hzero] using hT0pos
  have hT0_not_last : T z0 ≠ zn := by
    intro heq
    have : pos (T z0) = 1 := by simpa [zn, heq] using hone
    linarith
  have hT0val : (T z0).1 + 1 < n := by
    have hle : (T z0).1 < n - 1 := by
      have hlast : (T z0).1 ≠ n - 1 := by
        intro hv
        apply hT0_not_last
        apply Fin.ext
        simpa [zn] using hv
      omega
    omega
  let zL : Fin n := ⟨(T z0).1 + 1, hT0val⟩
  have hadjL : Adj (T z0) zL := by
    exact Or.inl rfl
  have hmoveL : Move T z0 zL := by
    exact Or.inr hadjL
  have hzLsmall : pos zL < 1/3 := by
    have h := hno z0
    have hreach : ReachAt T 1 z0 zL := ReachAt.one_of_move hmoveL
    by_contra hnot
    have hzLge : (1/3 : ℝ) ≤ pos zL := le_of_not_gt hnot
    have hzLnonneg : 0 ≤ pos zL := by linarith
    have hge : |pos zL - pos z0| ≥ 1/3 := by
      rw [hzero, sub_zero, abs_of_nonneg hzLnonneg]
      exact hzLge
    exact h ⟨1, by omega, zL, hreach, hge⟩
  have hleft_chain : 0 < (T z0).1 ∧ (T z0).1 < zL.1 := by
    dsimp [z0, zL] at *
    constructor <;> omega

  have hTn_ne : T zn ≠ zn := by
    intro h
    have := hjump zn
    simp [h] at this
    linarith
  have hTn_lt : T zn < zn := by
    have hvne : (T zn).1 ≠ n - 1 := by
      intro hv
      apply hTn_ne
      apply Fin.ext
      simpa [zn] using hv
    change (T zn).1 < n - 1
    have hlt := (T zn).isLt
    omega
  have hTnpos : pos (T zn) < 1 := by
    rw [← hone]
    exact hord hTn_lt
  have hTnlarge : (2/3 : ℝ) < pos (T zn) := by
    have h := no_escape_one_exact (hno zn)
    have hdiff : pos (T zn) - pos zn < 0 := by linarith
    rw [abs_of_neg hdiff] at h
    rw [hone] at h
    linarith
  have hTnvalpos : 0 < (T zn).1 := by
    by_contra hzeroVal
    have hv : (T zn).1 = 0 := by omega
    have heq : T zn = z0 := by
      apply Fin.ext
      simpa [z0] using hv
    have : pos (T zn) = 0 := by simpa [heq, z0] using hzero
    linarith
  let zR : Fin n := ⟨(T zn).1 - 1, by omega⟩
  have hadjR : Adj (T zn) zR := by
    right
    dsimp [zR]
    omega
  have hmoveR : Move T zn zR := by
    exact Or.inr hadjR
  have hzRlarge : (2/3 : ℝ) < pos zR := by
    have h := hno zn
    have hreach : ReachAt T 1 zn zR := ReachAt.one_of_move hmoveR
    by_contra hnot
    have hposle : pos zR ≤ 2/3 := le_of_not_gt hnot
    have hdiff : pos zR - pos zn ≤ -(1/3 : ℝ) := by
      rw [hone]
      linarith
    have habs : |pos zR - pos zn| ≥ 1/3 := by
      rw [abs_of_nonpos]
      · linarith
      · linarith
    exact h ⟨1, by omega, zR, hreach, habs⟩
  have hmid : zL < zR := by
    by_contra hnot
    have hle : zR ≤ zL := le_of_not_gt hnot
    have hp_le : pos zR ≤ pos zL := hord.monotone hle
    linarith [hzLsmall, hzRlarge]
  have hzR_lt_Tn : zR.1 < (T zn).1 := by
    dsimp [zR]
    omega
  have hTn_lt_last : (T zn).1 < n - 1 := by
    change (T zn).1 < zn.1
    exact hTn_lt
  have hzL_lt_zR : zL.1 < zR.1 := by
    exact hmid
  have hT0_lt_zL : (T z0).1 < zL.1 := hleft_chain.2
  have hz0pos : 0 < (T z0).1 := hleft_chain.1
  omega

end

end Scottish164

/-! ==================== Connectivity.lean ==================== -/

namespace Scottish164

noncomputable section

def Reachable {n : ℕ} (T : Fin n → Fin n) (x y : Fin n) : Prop :=
  ∃ m : ℕ, ReachAt T m x y

private lemma reachable_exact {n : ℕ} {T : Fin n → Fin n} {x y : Fin n}
    (h : Reachable T x y) : Reachable T x (T y) := by
  rcases h with ⟨m,hm⟩
  exact ⟨m+1, ReachAt.tail hm (exact_move T y)⟩

/-- Strong connectivity lemma from the paper. -/
theorem permissible_strongly_connected
    {n : ℕ} (_hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    ∀ x y : Fin n, Reachable σ x y := by
  classical
  intro x
  let R : Finset (Fin n) := Finset.univ.filter (fun y => Reachable σ x y)
  have hxR : x ∈ R := by
    change x ∈ Finset.univ.filter (fun y => Reachable σ x y)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨0, ReachAt.refl x⟩⟩
  have hforward : ∀ y ∈ R, σ y ∈ R := by
    intro y hy
    have hyr : Reachable σ x y := by simpa [R] using hy
    have : Reachable σ x (σ y) := reachable_exact hyr
    simpa [R] using this
  have hsub : R.image σ ⊆ R := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z,hz,rfl⟩
    exact hforward z hz
  have hcard : (R.image σ).card = R.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact σ.injective hab
  have heq : R.image σ = R := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hcard]
  have hadjClosed : ∀ {y z : Fin n}, y ∈ R → Adj y z → z ∈ R := by
    intro y z hy hadj
    have hyImage : y ∈ R.image σ := by simpa [heq] using hy
    rcases Finset.mem_image.mp hyImage with ⟨p,hp,hpy⟩
    have hpreach : Reachable σ x p := by simpa [R] using hp
    rcases hpreach with ⟨m,hm⟩
    have hmove : Move σ p z := by
      right
      simpa [hpy] using hadj
    have hzreach : Reachable σ x z := ⟨m+1, ReachAt.tail hm hmove⟩
    simpa [R] using hzreach

  have hright : ∀ j : Fin n, x ≤ j → j ∈ R := by
    have aux : ∀ d : ℕ, ∀ j : Fin n, j.1 - x.1 = d → x ≤ j → j ∈ R := by
      intro d
      induction d with
      | zero =>
          intro j hd hxj
          have hv : j.1 = x.1 := by omega
          have hjeq : j = x := Fin.ext hv
          simpa [hjeq] using hxR
      | succ d ih =>
          intro j hd hxj
          by_cases hjx : j = x
          · simpa [hjx] using hxR
          have hjpos : 0 < j.1 := by omega
          let k : Fin n := ⟨j.1 - 1, by omega⟩
          have hxk : x ≤ k := by
            change x.1 ≤ j.1 - 1
            omega
          have hdk : k.1 - x.1 = d := by
            change (j.1 - 1) - x.1 = d
            omega
          have hk : k ∈ R := ih k hdk hxk
          apply hadjClosed hk
          left
          dsimp [k]
          omega
    intro j hxj
    exact aux (j.1 - x.1) j rfl hxj
  have hleft : ∀ j : Fin n, j ≤ x → j ∈ R := by
    have aux : ∀ d : ℕ, ∀ j : Fin n, x.1 - j.1 = d → j ≤ x → j ∈ R := by
      intro d
      induction d with
      | zero =>
          intro j hd hjx
          have hv : j.1 = x.1 := by omega
          have hjeq : j = x := Fin.ext hv
          simpa [hjeq] using hxR
      | succ d ih =>
          intro j hd hjx
          by_cases hjx' : j = x
          · simpa [hjx'] using hxR
          have hjnext : j.1 + 1 < n := by omega
          let k : Fin n := ⟨j.1 + 1, hjnext⟩
          have hkx : k ≤ x := by
            change j.1 + 1 ≤ x.1
            omega
          have hdk : x.1 - k.1 = d := by
            change x.1 - (j.1 + 1) = d
            omega
          have hk : k ∈ R := ih k hdk hkx
          apply hadjClosed hk
          right
          dsimp [k]
    intro j hjx
    exact aux (x.1 - j.1) j rfl hjx
  intro y
  have hy : y ∈ R := by
    by_cases hxy : x ≤ y
    · exact hright y hxy
    · have hyx : y ≤ x := le_of_not_ge hxy
      exact hleft y hyx
  simpa [R] using hy

end

end Scottish164

/-! ==================== PermutationUpper.lean ==================== -/

namespace Scottish164

noncomputable section

private def RType {n : ℕ} (T : Fin n → Fin n) (x : Fin n) : Prop := x < T x
private def LType {n : ℕ} (T : Fin n → Fin n) (x : Fin n) : Prop := T x < x

private lemma type_dichotomy {n : ℕ} {T : Fin n → Fin n} {pos : Fin n → ℝ} {ε : ℝ}
    (_hord : Ordered pos) (hε0 : 0 < ε) (hjump : JumpCondition pos T ε) (x : Fin n) :
    RType T x ∨ LType T x := by
  have hne : T x ≠ x := by
    intro h
    have hx := hjump x
    simp [h] at hx
    linarith
  exact lt_or_gt_of_ne hne.symm

private lemma exact_direction_alternates_R
    {n : ℕ} {pos : Fin n → ℝ} {T : Fin n → Fin n} {ρ ε : ℝ}
    (hord : Ordered pos)
    (hε0 : 0 < ε)
    (hjump : JumpCondition pos T ε)
    (h2ε : ρ ≤ 2*ε)
    (hno : ∀ x : Fin n, ¬ EscapesWithin pos T ρ 2 x)
    {x : Fin n} (hx : RType T x) : LType T (T x) := by
  have htypes := type_dichotomy hord hε0 hjump (T x)
  rcases htypes with hR | hL
  · exfalso
    have hx1 : pos x < pos (T x) := hord hx
    have hx2 : pos (T x) < pos (T (T x)) := hord hR
    have hj1 := hjump x
    have hj2 := hjump (T x)
    rw [abs_of_pos (sub_pos.mpr hx1)] at hj1
    rw [abs_of_pos (sub_pos.mpr hx2)] at hj2
    have hfar : |pos (T (T x)) - pos x| ≥ ρ := by
      rw [abs_of_pos]
      · linarith
      · linarith
    exact hno x ⟨2, by omega, T (T x), ReachAt.two_exact T x, hfar⟩
  · exact hL

private lemma exact_direction_alternates_L
    {n : ℕ} {pos : Fin n → ℝ} {T : Fin n → Fin n} {ρ ε : ℝ}
    (hord : Ordered pos)
    (hε0 : 0 < ε)
    (hjump : JumpCondition pos T ε)
    (h2ε : ρ ≤ 2*ε)
    (hno : ∀ x : Fin n, ¬ EscapesWithin pos T ρ 2 x)
    {x : Fin n} (hx : LType T x) : RType T (T x) := by
  have htypes := type_dichotomy hord hε0 hjump (T x)
  rcases htypes with hR | hL
  · exact hR
  · exfalso
    have hx1 : pos (T x) < pos x := hord hx
    have hx2 : pos (T (T x)) < pos (T x) := hord hL
    have hj1 := hjump x
    have hj2 := hjump (T x)
    rw [abs_of_neg (sub_neg.mpr hx1)] at hj1
    rw [abs_of_neg (sub_neg.mpr hx2)] at hj2
    have hfar : |pos (T (T x)) - pos x| ≥ ρ := by
      rw [abs_of_neg]
      · linarith
      · linarith
    exact hno x ⟨2, by omega, T (T x), ReachAt.two_exact T x, hfar⟩

private lemma no_adjacent_LR
    {n : ℕ} {pos : Fin n → ℝ} {σ : Equiv.Perm (Fin n)} {ρ ε : ℝ}
    (hord : Ordered pos)
    (hε0 : 0 < ε)
    (hjump : JumpCondition pos σ ε)
    (h2ε : ρ ≤ 2*ε)
    (hno : ∀ x : Fin n, ¬ EscapesWithin pos σ ρ 2 x)
    {y z : Fin n} (hyz : y.1 + 1 = z.1)
    (hy : LType σ y) (hz : RType σ z) : False := by
  let p : Fin n := σ.symm y
  have hpmap : σ p = y := by simp [p]
  have hpR : RType σ p := by
    have htypes := type_dichotomy hord hε0 hjump p
    rcases htypes with hR | hL
    · exact hR
    · have hyR : RType σ y := by
        simpa [hpmap] using exact_direction_alternates_L hord hε0 hjump h2ε hno hL
      exact (lt_asymm hy hyR).elim
  have hp_lt_y : p < y := by simpa [RType, hpmap] using hpR
  have hy_lt_z : y < z := by
    apply Fin.mk_lt_mk.mpr
    omega
  have hz_lt_Tz : z < σ z := hz
  have hpy : pos p < pos y := hord hp_lt_y
  have hyzpos : pos y < pos z := hord hy_lt_z
  have hzT : pos z < pos (σ z) := hord hz_lt_Tz
  have hjp := hjump p
  have hjz := hjump z
  rw [hpmap, abs_of_pos (sub_pos.mpr hpy)] at hjp
  rw [abs_of_pos (sub_pos.mpr hzT)] at hjz
  have hadj : Adj (σ p) z := by
    left
    simpa [hpmap] using hyz
  have hstep1 : Move σ p z := Or.inr hadj
  have hreach : ReachAt σ 2 p (σ z) :=
    ReachAt.tail (ReachAt.one_of_move hstep1) (exact_move σ z)
  have hfar : |pos (σ z) - pos p| ≥ ρ := by
    rw [abs_of_pos]
    · linarith
    · linarith
  exact hno p ⟨2, by omega, σ z, hreach, hfar⟩

/-- If no `L|R` adjacency is allowed, `L` propagates to the right. -/
private lemma L_forward
    {n : ℕ} {R L : Fin n → Prop}
    (hcover : ∀ x, R x ∨ L x)
    (hnoLR : ∀ {i j : Fin n}, i.1 + 1 = j.1 → L i → R j → False)
    {i j : Fin n} (hij : i ≤ j) (hi : L i) : L j := by
  have aux : ∀ d : ℕ, ∀ a b : Fin n,
      b.1 - a.1 = d → a ≤ b → L a → L b := by
    intro d
    induction d with
    | zero =>
        intro a b hd hab ha
        have hv : a.1 = b.1 := by omega
        have heq : a = b := Fin.ext hv
        simpa [heq] using ha
    | succ d ih =>
        intro a b hd hab ha
        by_cases heq : a = b
        · simpa [heq] using ha
        have hbpos : 0 < b.1 := by omega
        let k : Fin n := ⟨b.1 - 1, by omega⟩
        have hak : a ≤ k := by
          change a.1 ≤ b.1 - 1
          omega
        have hdk : k.1 - a.1 = d := by
          change (b.1 - 1) - a.1 = d
          omega
        have hkL : L k := ih a k hdk hak ha
        rcases hcover b with hbR | hbL
        · exact (hnoLR (i:=k) (j:=b) (by dsimp [k]; omega) hkL hbR).elim
        · exact hbL
  exact aux (j.1 - i.1) i j rfl hij hi

/-- General two-step upper bound from the paper. -/
theorem general_two_step_upper
    {n : ℕ} (hn : 2 ≤ n) (pos : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (ρ ε : ℝ)
    (hρ0 : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hε : ρ/2 ≤ ε)
    (hord : Ordered pos)
    (hzero : pos (firstIdx (by omega : 0 < n)) = 0)
    (hone : pos (lastIdx (by omega : 0 < n)) = 1)
    (hjump : JumpCondition pos σ ε) :
    ∃ x : Fin n, EscapesWithin pos σ ρ 2 x := by
  by_contra hcontra
  push Not at hcontra
  have hε0 : 0 < ε := lt_of_lt_of_le (half_pos hρ0) hε
  have h2ε : ρ ≤ 2*ε := by linarith
  let z0 : Fin n := firstIdx (by omega)
  let zn : Fin n := lastIdx (by omega)

  have hcover : ∀ x : Fin n, RType σ x ∨ LType σ x :=
    fun x => type_dichotomy hord hε0 hjump x
  have hnoLR : ∀ {i j : Fin n}, i.1 + 1 = j.1 → LType σ i → RType σ j → False := by
    intro i j hij hi hj
    exact no_adjacent_LR hord hε0 hjump h2ε hcontra hij hi hj

  have hz0R : RType σ z0 := by
    rcases hcover z0 with hR | hL
    · exact hR
    · unfold LType at hL
      change (σ z0).1 < 0 at hL
      omega
  have hznL : LType σ zn := by
    rcases hcover zn with hR | hL
    · unfold RType at hR
      change n - 1 < (σ zn).1 at hR
      have hslt := (σ zn).isLt
      omega
    · exact hL

  have hT0L : LType σ (σ z0) :=
    exact_direction_alternates_R hord hε0 hjump h2ε hcontra hz0R
  have hTnR : RType σ (σ zn) :=
    exact_direction_alternates_L hord hε0 hjump h2ε hcontra hznL

  have hT0small : pos (σ z0) < ρ := by
    have hno1 : ¬ EscapesWithin pos σ ρ 1 z0 := by
      intro he
      rcases he with ⟨k,hk,y,hr,hfar⟩
      exact hcontra z0 ⟨k, by omega, y, hr, hfar⟩
    have h := no_escape_one_exact hno1
    have hpos : 0 < pos (σ z0) := by
      rw [← hzero]
      exact hord hz0R
    rw [abs_of_pos] at h
    · simpa [z0, hzero] using h
    · simpa [z0, hzero] using hpos

  have hR_before_T0 : ∀ r : Fin n, RType σ r → r < σ z0 := by
    intro r hr
    by_contra hnot
    have hle : σ z0 ≤ r := le_of_not_gt hnot
    have hrL : LType σ r := L_forward hcover hnoLR hle hT0L
    exact (lt_asymm hr hrL).elim

  have hRsmall : ∀ r : Fin n, RType σ r → pos r < ρ := by
    intro r hr
    have hir := hR_before_T0 r hr
    exact lt_trans (hord hir) hT0small

  have hTnlarge : 1 - ρ < pos (σ zn) := by
    have hno1 : ¬ EscapesWithin pos σ ρ 1 zn := by
      intro he
      apply hcontra zn
      rcases he with ⟨k,hk,y,hr,hd⟩
      exact ⟨k, by omega, y, hr, hd⟩
    have h := no_escape_one_exact hno1
    have hpos : pos (σ zn) < 1 := by
      rw [← hone]
      have : σ zn < zn := hznL
      exact hord this
    have hneg : pos (σ zn) - pos zn < 0 := by simpa [zn, hone] using sub_neg.mpr hpos
    rw [abs_of_neg hneg] at h
    rw [hone] at h
    linarith
  have hTn_ge_rho : ρ ≤ pos (σ zn) := by
    have : ρ ≤ 1-ρ := by linarith
    linarith
  have hsmall := hRsmall (σ zn) hTnR
  linarith

/-- The sharp upper bound for the original radius `1/3`. -/
theorem problem164_two_step_upper
    {n : ℕ} (hn : 2 ≤ n) (pos : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (ε : ℝ) (hε : (1/6 : ℝ) ≤ ε)
    (hord : Ordered pos)
    (hzero : pos (firstIdx (by omega : 0 < n)) = 0)
    (hone : pos (lastIdx (by omega : 0 < n)) = 1)
    (hjump : JumpCondition pos σ ε) :
    ∃ x : Fin n, EscapesWithin pos σ (1/3) 2 x := by
  apply general_two_step_upper hn pos σ (1/3) ε
  · norm_num
  · norm_num
  · linarith
  · exact hord
  · exact hzero
  · exact hone
  · exact hjump

end



/-! ==================== PermutationLowerCore ==================== -/

namespace LowerCore

/-- Cyclic successor on `Fin (M+1)`. -/
def phaseNext (M : ℕ) (r : Fin (M+1)) : Fin (M+1) :=
  if h : r.1 = M then ⟨0, by omega⟩ else ⟨r.1 + 1, by omega⟩

/-- Cyclic predecessor on `Fin (M+1)`. -/
def phasePrev (M : ℕ) (r : Fin (M+1)) : Fin (M+1) :=
  if h : r.1 = 0 then ⟨M, by omega⟩ else ⟨r.1 - 1, by omega⟩

@[simp] lemma phaseNext_val_of_lt {M : ℕ} (r : Fin (M+1)) (h : r.1 < M) :
    (phaseNext M r).1 = r.1 + 1 := by
  simp [phaseNext, Nat.ne_of_lt h]

@[simp] lemma phaseNext_val_last (M : ℕ) :
    (phaseNext M ⟨M, by omega⟩).1 = 0 := by
  simp [phaseNext]

@[simp] lemma phasePrev_val_of_pos {M : ℕ} (r : Fin (M+1)) (h : 0 < r.1) :
    (phasePrev M r).1 = r.1 - 1 := by
  simp [phasePrev, Nat.ne_of_gt h]

@[simp] lemma phasePrev_val_zero (M : ℕ) :
    (phasePrev M ⟨0, by omega⟩).1 = M := by
  simp [phasePrev]

lemma phasePrev_next (M : ℕ) (r : Fin (M+1)) : phasePrev M (phaseNext M r) = r := by
  apply Fin.ext
  by_cases hM : r.1 = M
  · simp [phaseNext, phasePrev, hM]
  · have hrlt : r.1 < M := by omega
    have hpos : 0 < r.1 + 1 := by omega
    simp [phaseNext, phasePrev, hM]

lemma phaseNext_prev (M : ℕ) (r : Fin (M+1)) : phaseNext M (phasePrev M r) = r := by
  apply Fin.ext
  by_cases h0 : r.1 = 0
  · simp [phaseNext, phasePrev, h0]
  · have hpos : 0 < r.1 := Nat.pos_of_ne_zero h0
    have hrle : r.1 ≤ M := Nat.le_of_lt_succ r.2
    have hpredlt : r.1 - 1 < M := by omega
    have hpredne : r.1 - 1 ≠ M := Nat.ne_of_lt hpredlt
    simp [phaseNext, phasePrev, h0, hpredne, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0)]

/-- The cyclic phase permutation. -/
def phaseEquiv (M : ℕ) : Equiv.Perm (Fin (M+1)) where
  toFun := phaseNext M
  invFun := phasePrev M
  left_inv := phasePrev_next M
  right_inv := phaseNext_prev M

/-- One slow block: `false = L`, `true = R`, with phase `r`. -/
abbrev BlockState (M : ℕ) := Bool × Fin (M+1)

/-- The block permutation changes rail and advances the cyclic phase. -/
def blockEquiv (M : ℕ) : Equiv.Perm (BlockState M) where
  toFun x := (!x.1, phaseNext M x.2)
  invFun x := (!x.1, phasePrev M x.2)
  left_inv := by
    intro x
    rcases x with ⟨b,r⟩
    simp [phasePrev_next]
  right_inv := by
    intro x
    rcases x with ⟨b,r⟩
    simp [phaseNext_prev]

/-- Physical level is the phase index, independent of the rail. -/
def blockLevel {M : ℕ} (x : BlockState M) : ℕ := x.2.1

lemma blockLevel_le (M : ℕ) (x : BlockState M) : blockLevel x ≤ M := by
  exact Nat.le_of_lt_succ x.2.2

/-- Physical adjacency in the two-rail order
    `L₀ < ... < L_M < R_M < ... < R₀`. -/
def BlockAdj (M : ℕ) (x y : BlockState M) : Prop :=
  (x.1 = false ∧ y.1 = false ∧ (x.2.1 + 1 = y.2.1 ∨ y.2.1 + 1 = x.2.1)) ∨
  (x.1 = true ∧ y.1 = true ∧ (x.2.1 + 1 = y.2.1 ∨ y.2.1 + 1 = x.2.1)) ∨
  (x.2.1 = M ∧ y.2.1 = M ∧ x.1 ≠ y.1)

lemma blockAdj_symm {M : ℕ} {x y : BlockState M} (h : BlockAdj M x y) : BlockAdj M y x := by
  rcases h with h | h | h
  · rcases h with ⟨hx,hy,hxy|hyx⟩
    · exact Or.inl ⟨hy,hx,Or.inr hxy⟩
    · exact Or.inl ⟨hy,hx,Or.inl hyx⟩
  · rcases h with ⟨hx,hy,hxy|hyx⟩
    · exact Or.inr (Or.inl ⟨hy,hx,Or.inr hxy⟩)
    · exact Or.inr (Or.inl ⟨hy,hx,Or.inl hyx⟩)
  · exact Or.inr (Or.inr ⟨h.2.1,h.1,Ne.symm h.2.2⟩)

/-- Before a wrap reset, one permissible block move raises the phase level by at most two. -/
lemma block_move_level_upper {M : ℕ} {x y : BlockState M}
    (hmove : GMove (BlockAdj M) (blockEquiv M) x y)
    (hnowrap : (phaseNext M x.2).1 ≠ 0) :
    blockLevel y ≤ blockLevel x + 2 := by
  have hxM : x.2.1 ≠ M := by
    intro hx
    apply hnowrap
    simp [phaseNext, hx]
  have hxlt : x.2.1 < M := by omega
  have hnxt : (phaseNext M x.2).1 = x.2.1 + 1 := phaseNext_val_of_lt x.2 hxlt
  rcases hmove with rfl | hadj
  · change (phaseNext M x.2).1 ≤ x.2.1 + 2
    omega
  · change BlockAdj M (blockEquiv M x) y at hadj
    rcases hadj with h | h | h
    · rcases h with ⟨_,_,h1|h1⟩
      · change (phaseNext M x.2).1 + 1 = y.2.1 at h1
        change y.2.1 ≤ x.2.1 + 2
        omega
      · change y.2.1 + 1 = (phaseNext M x.2).1 at h1
        change y.2.1 ≤ x.2.1 + 2
        omega
    · rcases h with ⟨_,_,h1|h1⟩
      · change (phaseNext M x.2).1 + 1 = y.2.1 at h1
        change y.2.1 ≤ x.2.1 + 2
        omega
      · change y.2.1 + 1 = (phaseNext M x.2).1 at h1
        change y.2.1 ≤ x.2.1 + 2
        omega
    · rcases h with ⟨himg,hy,_⟩
      change (phaseNext M x.2).1 = M at himg
      change y.2.1 = M at hy
      change y.2.1 ≤ x.2.1 + 2
      omega

/-- Along a no-wrap path starting at level zero, the level after `m` steps is at most `2m`. -/
lemma reach_level_upper {M m : ℕ} {x y : BlockState M}
    (hx : blockLevel x = 0)
    (hpath : GReachAt (BlockAdj M) (blockEquiv M) m x y)
    (hnowrap : ∀ k : ℕ, k < m → ∀ u v : BlockState M,
      GReachAt (BlockAdj M) (blockEquiv M) k x u →
      GMove (BlockAdj M) (blockEquiv M) u v →
      (phaseNext M u.2).1 ≠ 0) :
    blockLevel y ≤ 2*m := by
  induction hpath with
  | refl z => simpa using hx.le
  | @tail k a b c hpre hstep ih =>
      have hnw : (phaseNext M b.2).1 ≠ 0 :=
        hnowrap k (by omega) b c hpre hstep
      have hlev : blockLevel c ≤ blockLevel b + 2 :=
        block_move_level_upper hstep hnw
      have hprefix : blockLevel b ≤ 2*k := by
        apply ih hx
        intro j hj u v hu hv
        exact hnowrap j (by omega) u v hu hv
      omega

/-- A path whose phase never wraps from `M` back to `0` needs at least `ceil(M/2)`
    steps to go from level `0` to level `M`.  This is the quantitative core of the
    slow-corridor construction. -/
theorem slow_level_core {M m : ℕ} {x y : BlockState M}
    (hx : blockLevel x = 0) (hy : blockLevel y = M)
    (hpath : GReachAt (BlockAdj M) (blockEquiv M) m x y)
    (hnowrap : ∀ k : ℕ, k < m → ∀ u v : BlockState M,
      GReachAt (BlockAdj M) (blockEquiv M) k x u →
      GMove (BlockAdj M) (blockEquiv M) u v →
      (phaseNext M u.2).1 ≠ 0) :
    M ≤ 2*m := by
  have hbound := reach_level_upper hx hpath hnowrap
  omega

end LowerCore

end Scottish164

/-! ==================== PermutationLowerGlobalSkeleton ==================== -/

namespace Scottish164
namespace LowerGlobal

open LowerCore

/-- A corridor of `q` slow macroblocks. -/
abbrev MultiState (q M : ℕ) := Fin q × BlockState M

/-- Left and right physical portals of a slow block. -/
def leftPortal (M : ℕ) : BlockState M := (false, ⟨0, by omega⟩)
def rightPortal (M : ℕ) : BlockState M := (true, ⟨0, by omega⟩)

@[simp] lemma leftPortal_level (M : ℕ) : blockLevel (leftPortal M) = 0 := rfl
@[simp] lemma rightPortal_level (M : ℕ) : blockLevel (rightPortal M) = 0 := rfl

/-- The global permutation acts independently inside each macroblock. -/
def multiEquiv (q M : ℕ) : Equiv.Perm (MultiState q M) where
  toFun x := (x.1, blockEquiv M x.2)
  invFun x := (x.1, (blockEquiv M).symm x.2)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

@[simp] lemma multiEquiv_fst {q M : ℕ} (x : MultiState q M) :
    (multiEquiv q M x).1 = x.1 := rfl

@[simp] lemma multiEquiv_snd {q M : ℕ} (x : MultiState q M) :
    (multiEquiv q M x).2 = blockEquiv M x.2 := rfl

/-- Physical adjacency in the concatenated corridor.  Besides adjacency inside a
    macroblock, the right portal of block `b` is adjacent to the left portal of
    block `b+1`. -/
def MultiAdj (q M : ℕ) (x y : MultiState q M) : Prop :=
  (x.1 = y.1 ∧ BlockAdj M x.2 y.2) ∨
  (x.1.1 + 1 = y.1.1 ∧ x.2 = rightPortal M ∧ y.2 = leftPortal M) ∨
  (y.1.1 + 1 = x.1.1 ∧ y.2 = rightPortal M ∧ x.2 = leftPortal M)

lemma multiAdj_symm {q M : ℕ} {x y : MultiState q M} (h : MultiAdj q M x y) :
    MultiAdj q M y x := by
  rcases h with h | h | h
  · exact Or.inl ⟨h.1.symm, blockAdj_symm h.2⟩
  · exact Or.inr (Or.inr ⟨h.1, h.2.1, h.2.2⟩)
  · exact Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2⟩)

/-- The cyclic phase advances to zero exactly from the last phase. -/
lemma phaseNext_zero_iff {M : ℕ} (r : Fin (M+1)) :
    (phaseNext M r).1 = 0 ↔ r.1 = M := by
  by_cases h : r.1 = M
  · simp [phaseNext, h]
  · have hrlt : r.1 < M := by omega
    simp [phaseNext, h]

/-- A permissible move that changes macroblock must use one of the two physical
    portals after applying the block permutation. -/
lemma cross_move_portals {q M : ℕ} {x y : MultiState q M}
    (hmove : GMove (MultiAdj q M) (multiEquiv q M) x y)
    (hcross : x.1 ≠ y.1) :
    (((multiEquiv q M x).2 = rightPortal M ∧ y.2 = leftPortal M) ∨
     ((multiEquiv q M x).2 = leftPortal M ∧ y.2 = rightPortal M)) := by
  rcases hmove with hexact | hadj
  · exfalso
    apply hcross
    simp [hexact]
  · rcases hadj with hsame | hright | hleft
    · exfalso
      apply hcross
      simpa using hsame.1
    · exact Or.inl ⟨hright.2.1, hright.2.2⟩
    · exact Or.inr ⟨hleft.2.2, hleft.2.1⟩

/-- Before every cross-macroblock permissible move, the source is at phase
    level `M`.  This is the bridge from the global corridor to `slow_level_core`. -/
lemma cross_move_source_level {q M : ℕ} {x y : MultiState q M}
    (hmove : GMove (MultiAdj q M) (multiEquiv q M) x y)
    (hcross : x.1 ≠ y.1) :
    blockLevel x.2 = M := by
  have hp := cross_move_portals hmove hcross
  rcases hp with hp | hp
  · have hz : (phaseNext M x.2.2).1 = 0 := by
      have hs := congrArg (fun s : BlockState M => s.2.1) hp.1
      simpa [multiEquiv, blockEquiv, rightPortal] using hs
    exact (phaseNext_zero_iff x.2.2).mp hz
  · have hz : (phaseNext M x.2.2).1 = 0 := by
      have hs := congrArg (fun s : BlockState M => s.2.1) hp.1
      simpa [multiEquiv, blockEquiv, leftPortal] using hs
    exact (phaseNext_zero_iff x.2.2).mp hz

/-- After a cross-macroblock move, the destination is at phase level zero. -/
lemma cross_move_target_level {q M : ℕ} {x y : MultiState q M}
    (hmove : GMove (MultiAdj q M) (multiEquiv q M) x y)
    (hcross : x.1 ≠ y.1) :
    blockLevel y.2 = 0 := by
  have hp := cross_move_portals hmove hcross
  rcases hp with hp | hp
  · rw [hp.2]
    rfl
  · rw [hp.2]
    rfl

/-- A move which does not change macroblock is exactly a permissible move in the
    corresponding slow block. -/
lemma same_block_move_local {q M : ℕ} {x y : MultiState q M}
    (hmove : GMove (MultiAdj q M) (multiEquiv q M) x y)
    (hsame : x.1 = y.1) :
    GMove (BlockAdj M) (blockEquiv M) x.2 y.2 := by
  rcases hmove with hexact | hadj
  · left
    have hs := congrArg Prod.snd hexact
    simpa [multiEquiv] using hs
  · rcases hadj with hin | hright | hleft
    · right
      simpa [multiEquiv] using hin.2
    · exfalso
      have : x.1.1 + 1 = x.1.1 := by simpa [hsame] using hright.1
      omega
    · exfalso
      have : x.1.1 + 1 = x.1.1 := by simpa [hsame] using hleft.1
      omega

end LowerGlobal
end Scottish164

/-! ==================== PermutationLowerGlobal ==================== -/

namespace Scottish164
namespace LowerGlobal

open LowerCore

/-- A block move always raises the physical level by at most two.  If the phase
wraps, the source level is `M`, so the assertion is automatic. -/
lemma block_move_level_bound {M : ℕ} {x y : BlockState M}
    (hmove : GMove (BlockAdj M) (blockEquiv M) x y) :
    blockLevel y ≤ blockLevel x + 2 := by
  by_cases hwrap : (phaseNext M x.2).1 = 0
  · have hxM : blockLevel x = M := (phaseNext_zero_iff x.2).mp hwrap
    have hyM : blockLevel y ≤ M := blockLevel_le M y
    omega
  · exact block_move_level_upper hmove hwrap

/-- Block number changes by at most one in a permissible global move. -/
lemma multi_move_block_local {q M : ℕ} {x y : MultiState q M}
    (h : GMove (MultiAdj q M) (multiEquiv q M) x y) :
    y.1.1 = x.1.1 ∨ y.1.1 + 1 = x.1.1 ∨ x.1.1 + 1 = y.1.1 := by
  rcases h with hexact | hadj
  · left
    simp [hexact]
  · rcases hadj with hs | hr | hl
    · left
      exact (congrArg Fin.val hs.1).symm
    · exact Or.inr (Or.inr hr.1)
    · exact Or.inr (Or.inl hl.1)

/-- Coordinates of the concatenated slow corridor. -/
noncomputable def multiPos (q M : ℕ) (D η h : ℝ) (x : MultiState q M) : ℝ :=
  let start := (x.1.1 : ℝ) * (D+h)
  if x.2.1 = false then
    start + (x.2.2.1 : ℝ) * η / M
  else
    start + D - (x.2.2.1 : ℝ) * η / M

private lemma phase_term_bounds {M : ℕ} (hM : 1 ≤ M) {η : ℝ} (hη0 : 0 ≤ η)
    (r : Fin (M+1)) :
    0 ≤ (r.1 : ℝ)*η/M ∧ (r.1 : ℝ)*η/M ≤ η := by
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hr : (r.1:ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt_succ r.isLt)
  constructor
  · positivity
  · apply (div_le_iff₀ hMr).2
    nlinarith

/-- Every exact permutation edge has physical length at least `D-2η`. -/
lemma multiblock_jump_lower
    {q M : ℕ} (hM : 1 ≤ M) (D η h : ℝ) (hη0 : 0 ≤ η)
    (x : MultiState q M) :
    D - 2*η ≤
      |multiPos q M D η h (multiEquiv q M x) - multiPos q M D η h x| := by
  rcases x with ⟨b,⟨side,r⟩⟩
  have hr := phase_term_bounds hM hη0 r
  have hn := phase_term_bounds hM hη0 (phaseNext M r)
  by_cases htriv : D - 2*η ≤ 0
  · exact htriv.trans (abs_nonneg _)
  · have hD : 2*η < D := by linarith
    cases side
    · change D - 2*η ≤
        |(b.1 : ℝ)*(D+h) + D - ((phaseNext M r).1 : ℝ)*η/M -
          ((b.1 : ℝ)*(D+h) + (r.1 : ℝ)*η/M)|
      have hdiff : 0 ≤
          D - ((phaseNext M r).1 : ℝ)*η/M - ((r.1 : ℝ)*η/M) := by
        nlinarith [hr.2, hn.2]
      have heq :
          (b.1 : ℝ)*(D+h) + D - ((phaseNext M r).1 : ℝ)*η/M -
            ((b.1 : ℝ)*(D+h) + (r.1 : ℝ)*η/M) =
          D - ((phaseNext M r).1 : ℝ)*η/M - ((r.1 : ℝ)*η/M) := by
        ring
      rw [heq, abs_of_nonneg hdiff]
      nlinarith [hr.2, hn.2]
    · change D - 2*η ≤
        |(b.1 : ℝ)*(D+h) + ((phaseNext M r).1 : ℝ)*η/M -
          ((b.1 : ℝ)*(D+h) + D - (r.1 : ℝ)*η/M)|
      have hdiff :
          ((phaseNext M r).1 : ℝ)*η/M - (D - (r.1 : ℝ)*η/M) ≤ 0 := by
        nlinarith [hr.2, hn.2]
      have heq :
          (b.1 : ℝ)*(D+h) + ((phaseNext M r).1 : ℝ)*η/M -
            ((b.1 : ℝ)*(D+h) + D - (r.1 : ℝ)*η/M) =
          ((phaseNext M r).1 : ℝ)*η/M - (D - (r.1 : ℝ)*η/M) := by
        ring
      rw [heq, abs_of_nonpos hdiff]
      nlinarith [hr.2, hn.2]

/-- The gap between two adjacent macroblocks is chosen so that the diameter of
any one or two adjacent blocks is strictly smaller than the escape radius `2/q`. -/
lemma adjacent_block_span_lt
    {q : ℕ} (hq : 3 ≤ q) {D : ℝ} (_hD0 : 0 < D) (hDq : D < 1/q) :
    2*D + (1-q*D)/(q-1) < 2/q := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1:ℝ) < (q:ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hq2' : (2:ℝ) < (q:ℝ) := by exact_mod_cast (show 2 < q by omega)
  have hq1 : (0:ℝ) < (q:ℝ)-1 := by linarith
  have hq2 : (0:ℝ) < (q:ℝ)-2 := by linarith
  have hqD : (q:ℝ)*D < 1 := by
    calc
      (q:ℝ)*D < (q:ℝ)*(1/(q:ℝ)) := mul_lt_mul_of_pos_left hDq hq0
      _ = 1 := by field_simp
  have hdiff :
      2/(q:ℝ) - (2*D + (1-(q:ℝ)*D)/((q:ℝ)-1)) =
        ((q:ℝ)-2)*(1-(q:ℝ)*D)/((q:ℝ)*((q:ℝ)-1)) := by
    field_simp
    ring
  have hrhs : 0 < ((q:ℝ)-2)*(1-(q:ℝ)*D)/((q:ℝ)*((q:ℝ)-1)) := by
    positivity
  rw [← sub_pos]
  rw [hdiff]
  exact hrhs

/-- A right-going potential. -/
def rightPotential {q M : ℕ} (x : MultiState q M) : ℕ :=
  x.1.1 * M + blockLevel x.2

/-- A left-going mirror potential. -/
def leftPotential {q M : ℕ} (x : MultiState q M) : ℕ :=
  (q-1-x.1.1) * M + blockLevel x.2

lemma rightPotential_move_bound {q M : ℕ} {x y : MultiState q M}
    (h : GMove (MultiAdj q M) (multiEquiv q M) x y) :
    rightPotential y ≤ rightPotential x + 2 := by
  by_cases hsame : x.1 = y.1
  · have hlocal := same_block_move_local h hsame
    have hlev := block_move_level_bound hlocal
    unfold rightPotential
    have hv : y.1.1 = x.1.1 := congrArg Fin.val hsame.symm
    nlinarith
  · have hxM := cross_move_source_level h hsame
    have hy0 := cross_move_target_level h hsame
    have hblk := multi_move_block_local h
    unfold rightPotential
    rcases hblk with h0 | hleft | hright
    · exfalso
      apply hsame
      exact Fin.ext h0.symm
    · nlinarith
    · nlinarith

lemma leftPotential_move_bound {q M : ℕ} {x y : MultiState q M}
    (h : GMove (MultiAdj q M) (multiEquiv q M) x y) :
    leftPotential y ≤ leftPotential x + 2 := by
  by_cases hsame : x.1 = y.1
  · have hlocal := same_block_move_local h hsame
    have hlev := block_move_level_bound hlocal
    unfold leftPotential
    rw [hsame]
    omega
  · have hxM := cross_move_source_level h hsame
    have hy0 := cross_move_target_level h hsame
    have hblk := multi_move_block_local h
    unfold leftPotential
    rcases hblk with h0 | hleft | hright
    · exfalso
      apply hsame
      exact Fin.ext h0.symm
    · have hfac : q - 1 - y.1.1 = (q - 1 - x.1.1) + 1 := by
        have hxlt := x.1.2
        have hylt := y.1.2
        omega
      rw [hxM, hy0, hfac]
      simp [Nat.add_mul]
    · have hfac : q - 1 - x.1.1 = (q - 1 - y.1.1) + 1 := by
        have hxlt := x.1.2
        have hylt := y.1.2
        omega
      rw [hxM, hy0, hfac]
      simp [Nat.add_mul]
      omega

lemma rightPotential_reach_bound {q M m : ℕ} {x y : MultiState q M}
    (h : GReachAt (MultiAdj q M) (multiEquiv q M) m x y) :
    rightPotential y ≤ rightPotential x + 2*m := by
  induction h with
  | refl z => simp
  | @tail m a b c hab hbc ih =>
      have hs := rightPotential_move_bound hbc
      omega

lemma leftPotential_reach_bound {q M m : ℕ} {x y : MultiState q M}
    (h : GReachAt (MultiAdj q M) (multiEquiv q M) m x y) :
    leftPotential y ≤ leftPotential x + 2*m := by
  induction h with
  | refl z => simp
  | @tail m a b c hab hbc ih =>
      have hs := leftPotential_move_bound hbc
      omega

/-- Moving by at least two macroblock indices costs at least `ceil(M/2)` steps. -/
theorem block_separation_forces_delay {q M m : ℕ} {x y : MultiState q M}
    (hreach : GReachAt (MultiAdj q M) (multiEquiv q M) m x y)
    (hsep : x.1.1 + 2 ≤ y.1.1 ∨ y.1.1 + 2 ≤ x.1.1) :
    (M+1)/2 ≤ m := by
  rcases hsep with hright | hleft
  · have hp := rightPotential_reach_bound hreach
    unfold rightPotential at hp
    have hxlev : blockLevel x.2 ≤ M := blockLevel_le M x.2
    have hylev : 0 ≤ blockLevel y.2 := Nat.zero_le _
    have hmul := Nat.mul_le_mul_right M hright
    simp [Nat.add_mul] at hmul
    omega
  · have hp := leftPotential_reach_bound hreach
    unfold leftPotential at hp
    have hxlev : blockLevel x.2 ≤ M := blockLevel_le M x.2
    have hylev : 0 ≤ blockLevel y.2 := Nat.zero_le _
    have hfac : (q - 1 - x.1.1) + 2 ≤ q - 1 - y.1.1 := by
      have hxlt := x.1.2
      have hylt := y.1.2
      omega
    have hmul := Nat.mul_le_mul_right M hfac
    simp [Nat.add_mul] at hmul
    omega

private lemma localCoord_bounds {M : ℕ} (hM : 1 ≤ M) {D η : ℝ}
    (hη0 : 0 ≤ η) (hηD : η ≤ D/2) (x : BlockState M) :
    0 ≤ (if x.1 = false then (x.2.1 : ℝ)*η/M else D-(x.2.1 : ℝ)*η/M) ∧
    (if x.1 = false then (x.2.1 : ℝ)*η/M else D-(x.2.1 : ℝ)*η/M) ≤ D := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hterm : (x.2.1 : ℝ)*η/M ≤ η := by
    exact (phase_term_bounds hM hη0 x.2).2
  have hterm0 : 0 ≤ (x.2.1 : ℝ)*η/M := by
    exact (phase_term_bounds hM hη0 x.2).1
  cases x.1 <;> simp
  · constructor <;> nlinarith
  · constructor <;> nlinarith

lemma multiPos_block_bounds {q M : ℕ} (hM : 1 ≤ M) (D η h : ℝ)
    (hη0 : 0 ≤ η) (hηD : η ≤ D/2) (x : MultiState q M) :
    (x.1.1 : ℝ)*(D+h) ≤ multiPos q M D η h x ∧
    multiPos q M D η h x ≤ (x.1.1 : ℝ)*(D+h)+D := by
  rcases localCoord_bounds hM hη0 hηD x.2 with ⟨hl,hu⟩
  unfold multiPos
  dsimp
  by_cases hs : x.2.1 = false
  · simp [hs] at hl hu ⊢
    constructor <;> linarith
  · simp [hs] at hl hu ⊢
    constructor <;> linarith

lemma same_or_adjacent_block_close
    {q M : ℕ} (hM : 1 ≤ M) (D η h : ℝ)
    (hD0 : 0 ≤ D) (hh0 : 0 ≤ h) (hη0 : 0 ≤ η) (hηD : η ≤ D/2)
    {x y : MultiState q M}
    (hblk : x.1.1 = y.1.1 ∨ x.1.1 + 1 = y.1.1 ∨ y.1.1 + 1 = x.1.1) :
    |multiPos q M D η h y - multiPos q M D η h x| ≤ 2*D+h := by
  rcases multiPos_block_bounds hM D η h hη0 hηD x with ⟨hxl,hxu⟩
  rcases multiPos_block_bounds hM D η h hη0 hηD y with ⟨hyl,hyu⟩
  rcases hblk with heq | hright | hleft
  · have hb : (x.1.1 : ℝ) = y.1.1 := by exact_mod_cast heq
    rw [abs_le]
    constructor <;> nlinarith
  · have hb : (y.1.1 : ℝ) = x.1.1 + 1 := by
      exact_mod_cast hright.symm
    rw [abs_le]
    constructor <;> nlinarith
  · have hb : (x.1.1 : ℝ) = y.1.1 + 1 := by
      exact_mod_cast hleft.symm
    rw [abs_le]
    constructor <;> nlinarith

/-- All-start slow estimate in the abstract finite-line corridor. -/
theorem multiblock_all_slow
    (q M L : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M)
    (ρ D η : ℝ)
    (hD0 : 0 < D) (hDq : D < 1/q)
    (hη0 : 0 < η) (hηD : η ≤ D/2)
    (hspan : 2*D + (1-q*D)/(q-1) < ρ)
    (hML : L < (M+1)/2) :
    GAllSlow
      (multiPos q M D η ((1-q*D)/(q-1)))
      (MultiAdj q M) (multiEquiv q M) ρ L := by
  intro x hesc
  rcases hesc with ⟨m,hm,y,hreach,hfar⟩
  have hqR : (1:ℝ) < q := by exact_mod_cast hq
  have hqpos : (0:ℝ) < q := by positivity
  have hmul : (q:ℝ)*D < 1 := by
    calc
      (q:ℝ)*D < (q:ℝ)*(1/(q:ℝ)) := mul_lt_mul_of_pos_left hDq hqpos
      _ = 1 := by field_simp
  have hh0 : 0 ≤ (1-q*D)/(q-1) := by
    have hnum : 0 < 1-q*D := by linarith
    have hden : (0:ℝ) < q-1 := by linarith
    exact le_of_lt (div_pos hnum hden)
  have hnotclose :
      ¬ (x.1.1 = y.1.1 ∨ x.1.1+1=y.1.1 ∨ y.1.1+1=x.1.1) := by
    intro hb
    have hc := same_or_adjacent_block_close hM D η ((1-q*D)/(q-1))
      (le_of_lt hD0) hh0 (le_of_lt hη0) hηD hb
    linarith
  have hsep : x.1.1 + 2 ≤ y.1.1 ∨ y.1.1 + 2 ≤ x.1.1 := by omega
  have hdelay := block_separation_forces_delay hreach hsep
  omega

/-- Generic resonant lower bound in the abstract corridor. -/
theorem resonant_arbitrarily_slow_generic
    (q : ℕ) (hq : 4 ≤ q) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1/q)
    (L : ℕ) :
    ∃ M : ℕ, ∃ D η : ℝ,
      1 ≤ M ∧ ε < D ∧ D < 1/q ∧ 0 < η ∧ 2*η < D ∧ η ≤ D/2 ∧
      (∀ x : MultiState q M,
        |multiPos q M D η ((1-q*D)/(q-1)) (multiEquiv q M x) -
         multiPos q M D η ((1-q*D)/(q-1)) x| > ε) ∧
      GAllSlow
        (multiPos q M D η ((1-q*D)/(q-1)))
        (MultiAdj q M) (multiEquiv q M) (2/q) L := by
  let D : ℝ := (ε + 1/q)/2
  have hDε : ε < D := by dsimp [D]; linarith
  have hDq : D < 1/q := by dsimp [D]; linarith
  let η : ℝ := (D-ε)/4
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hηjump : 2*η < D-ε := by dsimp [η]; linarith
  have hηD : η ≤ D/2 := by dsimp [η, D]; linarith [hε0]
  let M : ℕ := 2*L+3
  have hM : 1 ≤ M := by dsimp [M]; omega
  have h2ηD : 2*η < D := by dsimp [η]; linarith [hDε]
  refine ⟨M,D,η,hM,hDε,hDq,hη0,h2ηD,hηD,?_,?_⟩
  · intro x
    have hlow := multiblock_jump_lower (q:=q) (M:=M) hM D η ((1-q*D)/(q-1))
      (le_of_lt hη0) x
    linarith
  · apply multiblock_all_slow q M L (by omega) hM (2/q) D η
    · have : (0 : ℝ) < 1/q := by positivity
      linarith
    · exact hDq
    · exact hη0
    · exact hηD
    · exact adjacent_block_span_lt (q:=q) (by omega) (by linarith) hDq
    · dsimp [M]
      omega

end LowerGlobal
end Scottish164

/-! ==================== Ordered Fin realization ==================== -/

namespace Scottish164
namespace LowerRealization

open LowerCore LowerGlobal

/-- Explicit equivalence `Bool ≃ Fin 2`. -/
def boolFinEquiv : Bool ≃ Fin 2 where
  toFun b := match b with | false => 0 | true => 1
  invFun i := if i = 0 then false else true
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Reverses the phase on the right rail, turning a block into its physical order. -/
def blockLinearEquiv (M : ℕ) : BlockState M ≃ Fin 2 × Fin (M+1) where
  toFun x := (boolFinEquiv x.1, if x.1 then x.2.rev else x.2)
  invFun y :=
    let b := boolFinEquiv.symm y.1
    (b, if b then y.2.rev else y.2)
  left_inv := by
    intro x
    rcases x with ⟨b,r⟩
    cases b <;> simp [boolFinEquiv]
  right_inv := by
    intro y
    rcases y with ⟨s,r⟩
    fin_cases s <;> simp [boolFinEquiv]

/-- Rank inside one block in physical order. -/
def blockRankEquiv (M : ℕ) : BlockState M ≃ Fin (2*(M+1)) :=
  (blockLinearEquiv M).trans finProdFinEquiv

@[simp] lemma blockRank_false_val (M : ℕ) (r : Fin (M+1)) :
    (blockRankEquiv M (false,r)).1 = r.1 := by
  simp [blockRankEquiv, blockLinearEquiv, boolFinEquiv, finProdFinEquiv]

@[simp] lemma blockRank_true_val (M : ℕ) (r : Fin (M+1)) :
    (blockRankEquiv M (true,r)).1 = 2*M+1-r.1 := by
  simp [blockRankEquiv, blockLinearEquiv, boolFinEquiv, finProdFinEquiv]
  omega

/-- Global physical rank. -/
def multiRankEquiv (q M : ℕ) : MultiState q M ≃ Fin (q*(2*(M+1))) :=
  (Equiv.prodCongr (Equiv.refl (Fin q)) (blockRankEquiv M)).trans finProdFinEquiv

@[simp] lemma multiRank_val (q M : ℕ) (x : MultiState q M) :
    (multiRankEquiv q M x).1 =
      (blockRankEquiv M x.2).1 + (2*(M+1))*x.1.1 := by
  simp [multiRankEquiv, finProdFinEquiv]

lemma blockRank_adj_iff {M : ℕ} {x y : BlockState M} :
    Adj (blockRankEquiv M x) (blockRankEquiv M y) ↔ BlockAdj M x y := by
  rcases x with ⟨sx,rx⟩
  rcases y with ⟨sy,ry⟩
  cases sx <;> cases sy <;>
    simp [Adj, BlockAdj, blockRank_false_val, blockRank_true_val] <;> omega

lemma blockRank_zero_iff {M : ℕ} (x : BlockState M) :
    (blockRankEquiv M x).1 = 0 ↔ x = leftPortal M := by
  rcases x with ⟨s,r⟩
  cases s
  · rw [blockRank_false_val]
    constructor
    · intro hr
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa [leftPortal] using hr
    · intro h
      have hr := congrArg (fun z : BlockState M => z.2.1) h
      simpa [leftPortal] using hr
  · rw [blockRank_true_val]
    constructor
    · intro h
      have hr : r.1 ≤ M := Nat.le_of_lt_succ r.isLt
      omega
    · intro h
      have hf := congrArg (fun z : BlockState M => z.1) h
      simp [leftPortal] at hf

lemma blockRank_last_iff {M : ℕ} (x : BlockState M) :
    (blockRankEquiv M x).1 = 2*(M+1)-1 ↔ x = rightPortal M := by
  rcases x with ⟨s,r⟩
  cases s
  · rw [blockRank_false_val]
    constructor
    · intro h
      have hr : r.1 ≤ M := Nat.le_of_lt_succ r.isLt
      have hlast : M < 2*(M+1)-1 := by omega
      omega
    · intro h
      simp [rightPortal] at h
  · rw [blockRank_true_val]
    have hlast : 2*(M+1)-1 = 2*M+1 := by omega
    constructor
    · intro h
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change r.1 = 0
        rw [hlast] at h
        omega
    · intro h
      have hr0 : r.1 = 0 := by
        have hs := congrArg (fun z : BlockState M => z.2.1) h
        simpa [rightPortal] using hs
      rw [hr0, hlast]
      omega

private lemma concat_adj_forward
    {B a b c d : ℕ} (hB : 0 < B) (ha : a < B) (hb : b < B)
    (h : a + B*c + 1 = b + B*d) :
    (c = d ∧ a + 1 = b) ∨ (c + 1 = d ∧ a = B-1 ∧ b = 0) := by
  by_cases hcd : c = d
  · left
    refine ⟨hcd, ?_⟩
    rw [hcd] at h
    omega
  · have hlt : c < d := by
      by_contra hn
      have hdc : d + 1 ≤ c := by omega
      have hm := Nat.mul_le_mul_right B hdc
      simp [Nat.mul_add, Nat.mul_comm] at hm
      omega
    have hstep : c + 1 = d := by
      by_contra hn
      have hgap : c + 2 ≤ d := by omega
      have hm := Nat.mul_le_mul_right B hgap
      simp [Nat.mul_add, Nat.mul_comm] at hm
      omega
    right
    subst d
    simp only [Nat.mul_add, Nat.mul_one] at h
    have hab : a + 1 = b + B := by omega
    have ha1 : a + 1 = B := by omega
    refine ⟨?_, ?_⟩
    · omega
    · omega

/-- The explicit rank equivalence preserves exactly the physical nearest-neighbor relation. -/
theorem multiAdj_rank_iff {q M : ℕ} {x y : MultiState q M} :
    Adj (multiRankEquiv q M x) (multiRankEquiv q M y) ↔ MultiAdj q M x y := by
  have hB : 0 < 2*(M+1) := by omega
  have hxlt : (blockRankEquiv M x.2).1 < 2*(M+1) := (blockRankEquiv M x.2).2
  have hylt : (blockRankEquiv M y.2).1 < 2*(M+1) := (blockRankEquiv M y.2).2
  constructor
  · intro h
    simp [Adj, multiRank_val] at h
    rcases h with hxy | hyx
    · rcases concat_adj_forward hB hxlt hylt hxy with
        ⟨hblk,hloc⟩ | ⟨hblk,hlast,hzero⟩
      · left
        refine ⟨Fin.ext hblk, ?_⟩
        rw [← blockRank_adj_iff]
        simp [Adj]
        exact Or.inl hloc
      · exact Or.inr (Or.inl ⟨hblk,
          (blockRank_last_iff x.2).mp hlast,
          (blockRank_zero_iff y.2).mp hzero⟩)
    · rcases concat_adj_forward hB hylt hxlt hyx with
        ⟨hblk,hloc⟩ | ⟨hblk,hlast,hzero⟩
      · left
        refine ⟨Fin.ext hblk.symm, ?_⟩
        rw [← blockRank_adj_iff]
        simp [Adj]
        exact Or.inr hloc
      · exact Or.inr (Or.inr ⟨hblk,
          (blockRank_last_iff y.2).mp hlast,
          (blockRank_zero_iff x.2).mp hzero⟩)
  · intro h
    rcases h with hsame | hright | hleft
    · rcases hsame with ⟨hb,hadj⟩
      have hv : x.1.1 = y.1.1 := congrArg Fin.val hb
      have hr := (blockRank_adj_iff).2 hadj
      simp [Adj, multiRank_val] at hr ⊢
      rw [hv]
      rcases hr with hr | hr
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rcases hright with ⟨hb,hx,hy⟩
      have hvx := (blockRank_last_iff x.2).2 hx
      have hvy := (blockRank_zero_iff y.2).2 hy
      simp [Adj, multiRank_val, hvx, hvy]
      left
      rw [← hb]
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
      omega
    · rcases hleft with ⟨hb,hy,hx⟩
      have hvy := (blockRank_last_iff y.2).2 hy
      have hvx := (blockRank_zero_iff x.2).2 hx
      simp [Adj, multiRank_val, hvx, hvy]
      right
      rw [← hb]
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
      omega

/-- Conjugated permutation on the standard `Fin` indexing. -/
def indexedPerm (q M : ℕ) : Equiv.Perm (Fin (q*(2*(M+1)))) :=
  (multiRankEquiv q M).symm.trans ((multiEquiv q M).trans (multiRankEquiv q M))

/-- Conjugated coordinates. -/
noncomputable def indexedPos (q M : ℕ) (D η h : ℝ) : Fin (q*(2*(M+1))) → ℝ :=
  fun i => multiPos q M D η h ((multiRankEquiv q M).symm i)

@[simp] lemma indexedPos_rank (q M : ℕ) (D η h : ℝ) (x : MultiState q M) :
    indexedPos q M D η h (multiRankEquiv q M x) = multiPos q M D η h x := by
  simp [indexedPos]

@[simp] lemma indexedPerm_rank (q M : ℕ) (x : MultiState q M) :
    indexedPerm q M (multiRankEquiv q M x) =
      multiRankEquiv q M (multiEquiv q M x) := by
  simp [indexedPerm]

lemma move_rank_iff {q M : ℕ} {x y : MultiState q M} :
    Move (indexedPerm q M) (multiRankEquiv q M x) (multiRankEquiv q M y) ↔
      GMove (MultiAdj q M) (multiEquiv q M) x y := by
  constructor
  · intro h
    rcases h with hex | hadj
    · left
      apply (multiRankEquiv q M).injective
      simpa using hex
    · right
      have hadj' : Adj (multiRankEquiv q M (multiEquiv q M x))
          (multiRankEquiv q M y) := by
        simpa using hadj
      exact (multiAdj_rank_iff).1 hadj'
  · intro h
    rcases h with hex | hadj
    · left
      subst y
      exact (indexedPerm_rank q M x).symm
    · right
      have hadj' : Adj (multiRankEquiv q M (multiEquiv q M x))
          (multiRankEquiv q M y) := (multiAdj_rank_iff).2 hadj
      simpa using hadj'

lemma reach_to_generic {q M m : ℕ}
    {i j : Fin (q*(2*(M+1)))}
    (h : ReachAt (indexedPerm q M) m i j) :
    GReachAt (MultiAdj q M) (multiEquiv q M) m
      ((multiRankEquiv q M).symm i) ((multiRankEquiv q M).symm j) := by
  induction h with
  | refl z => exact GReachAt.refl _
  | @tail k a b c hab hbc ih =>
      apply GReachAt.tail ih
      have hm : Move (indexedPerm q M)
          (multiRankEquiv q M ((multiRankEquiv q M).symm b))
          (multiRankEquiv q M ((multiRankEquiv q M).symm c)) := by
        simpa using hbc
      exact (move_rank_iff).1 hm

lemma reach_from_generic {q M m : ℕ} {x y : MultiState q M}
    (h : GReachAt (MultiAdj q M) (multiEquiv q M) m x y) :
    ReachAt (indexedPerm q M) m (multiRankEquiv q M x) (multiRankEquiv q M y) := by
  induction h with
  | refl z => exact ReachAt.refl _
  | @tail k a b c hab hbc ih =>
      exact ReachAt.tail ih ((move_rank_iff).2 hbc)

lemma reach_rank_iff {q M m : ℕ} {x y : MultiState q M} :
    ReachAt (indexedPerm q M) m (multiRankEquiv q M x) (multiRankEquiv q M y) ↔
      GReachAt (MultiAdj q M) (multiEquiv q M) m x y := by
  constructor
  · intro h
    simpa using (reach_to_generic h)
  · exact reach_from_generic

lemma indexed_all_slow_of_generic {q M L : ℕ} {D η h ρ : ℝ}
    (hs : GAllSlow (multiPos q M D η h) (MultiAdj q M) (multiEquiv q M) ρ L) :
    AllSlow (indexedPos q M D η h) (indexedPerm q M) ρ L := by
  intro i hesc
  let x := (multiRankEquiv q M).symm i
  apply hs x
  rcases hesc with ⟨k,hk,j,hreach,hfar⟩
  let y := (multiRankEquiv q M).symm j
  refine ⟨k,hk,y,?_,?_⟩
  · rw [← reach_rank_iff]
    simpa [x,y]
  · simpa [indexedPos,x,y] using hfar

lemma indexed_jump_of_generic {q M : ℕ} {D η h ε : ℝ}
    (hj : ∀ x : MultiState q M,
      |multiPos q M D η h (multiEquiv q M x) - multiPos q M D η h x| > ε) :
    JumpCondition (indexedPos q M D η h) (indexedPerm q M) ε := by
  intro i
  let x := (multiRankEquiv q M).symm i
  simpa [indexedPos, indexedPerm, x] using hj x

/-- Local physical coordinates increase strictly with physical block rank. -/
lemma block_pos_rank_strict {M : ℕ} (hM : 1 ≤ M) {D η : ℝ}
    (hη0 : 0 < η) (h2ηD : 2*η < D) (x y : BlockState M)
    (hr : (blockRankEquiv M x).1 < (blockRankEquiv M y).1) :
    (if x.1 = false then (x.2.1:ℝ)*η/M else D-(x.2.1:ℝ)*η/M) <
    (if y.1 = false then (y.2.1:ℝ)*η/M else D-(y.2.1:ℝ)*η/M) := by
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rcases x with ⟨sx,rx⟩
  rcases y with ⟨sy,ry⟩
  cases sx <;> cases sy <;>
    simp [blockRank_false_val, blockRank_true_val] at hr ⊢
  · have hrr : (rx.1:ℝ) < ry.1 := by exact_mod_cast hr
    have hmul : (rx.1:ℝ)*η < (ry.1:ℝ)*η := mul_lt_mul_of_pos_right hrr hη0
    exact (div_lt_div_iff_of_pos_right hMr).2 hmul
  · have hxterm : (rx.1:ℝ)*η/M ≤ η := (phase_term_bounds hM (le_of_lt hη0) rx).2
    have hyterm : (ry.1:ℝ)*η/M ≤ η := (phase_term_bounds hM (le_of_lt hη0) ry).2
    nlinarith
  · omega
  · have hrr : (ry.1:ℝ) < rx.1 := by exact_mod_cast (by omega : ry.1 < rx.1)
    have : (ry.1:ℝ)*η/M < (rx.1:ℝ)*η/M := by
      apply (div_lt_div_iff_of_pos_right hMr).2
      nlinarith
    linarith

/-- The transported coordinates are strictly increasing. -/
theorem indexed_ordered
    (q M : ℕ) (_hq : 1 ≤ q) (hM : 1 ≤ M)
    (D η h : ℝ) (hD0 : 0 < D) (hη0 : 0 < η) (hh0 : 0 < h)
    (h2ηD : 2*η < D) (hηD : η ≤ D/2) :
    Ordered (indexedPos q M D η h) := by
  intro i j hij
  let x := (multiRankEquiv q M).symm i
  let y := (multiRankEquiv q M).symm j
  have hrank : (multiRankEquiv q M x).1 < (multiRankEquiv q M y).1 := by
    simpa [x,y] using hij
  have hxl : (blockRankEquiv M x.2).1 < 2*(M+1) := (blockRankEquiv M x.2).2
  have hyl : (blockRankEquiv M y.2).1 < 2*(M+1) := (blockRankEquiv M y.2).2
  have hblock : x.1.1 ≤ y.1.1 := by
    simp [multiRank_val] at hrank
    by_contra hnot
    have hrev : y.1.1 + 1 ≤ x.1.1 := by omega
    have hmul := Nat.mul_le_mul_left (2*(M+1)) hrev
    have hnext :
        (2*(M+1))*y.1.1 + 2*(M+1) ≤ (2*(M+1))*x.1.1 := by
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul
    omega
  by_cases hb : x.1 = y.1
  · have hbv : x.1.1 = y.1.1 := congrArg Fin.val hb
    have hlocal : (blockRankEquiv M x.2).1 < (blockRankEquiv M y.2).1 := by
      simp [multiRank_val, hbv] at hrank
      exact hrank
    have hp := block_pos_rank_strict hM hη0 h2ηD x.2 y.2 hlocal
    change multiPos q M D η h x < multiPos q M D η h y
    unfold multiPos
    dsimp
    have hbR : (x.1.1 : ℝ) = (y.1.1 : ℝ) := by exact_mod_cast hbv
    rw [hbR]
    by_cases hsx : x.2.1 = false <;> by_cases hsy : y.2.1 = false <;>
      simp [hsx, hsy] at hp ⊢ <;> linarith
  · have hbvne : x.1.1 ≠ y.1.1 := by
      intro hv
      exact hb (Fin.ext hv)
    have hbv : x.1.1 < y.1.1 := by omega
    have hx := multiPos_block_bounds hM D η h (le_of_lt hη0) hηD x
    have hy := multiPos_block_bounds hM D η h (le_of_lt hη0) hηD y
    have hbR : (x.1.1:ℝ) + 1 ≤ y.1.1 := by exact_mod_cast hbv
    unfold indexedPos
    simp
    nlinarith

lemma corridor_gap_positive {q : ℕ} (hq : 2 ≤ q) {D : ℝ} (hDq : D < 1/q) :
    0 < (1-q*D)/(q-1) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hden : (0:ℝ) < (q:ℝ)-1 := by linarith
  have hmul : (q:ℝ)*D < 1 := by
    calc
      (q:ℝ)*D < (q:ℝ)*(1/(q:ℝ)) := mul_lt_mul_of_pos_left hDq hq0
      _ = 1 := by field_simp
  norm_num at hDq ⊢
  exact div_pos (by linarith) hden

lemma corridor_endpoints
    (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) (D η : ℝ) :
    multiPos q M D η ((1-q*D)/(q-1))
        ((multiRankEquiv q M).symm (firstIdx (by positivity : 0 < q*(2*(M+1))))) = 0 ∧
    multiPos q M D η ((1-q*D)/(q-1))
        ((multiRankEquiv q M).symm (lastIdx (by positivity : 0 < q*(2*(M+1))))) = 1 := by
  constructor
  · have hz : (multiRankEquiv q M).symm (firstIdx (by positivity : 0 < q*(2*(M+1)))) =
      (⟨0, by omega⟩, leftPortal M) := by
      apply (multiRankEquiv q M).injective
      apply Fin.ext
      have hbr : (blockRankEquiv M (leftPortal M)).1 = 0 :=
        (blockRank_zero_iff (leftPortal M)).2 rfl
      simp [firstIdx, multiRank_val, hbr]
    rw [hz]
    simp [multiPos, leftPortal]
  · have hl : (multiRankEquiv q M).symm (lastIdx (by positivity : 0 < q*(2*(M+1)))) =
      (⟨q-1, by omega⟩, rightPortal M) := by
      apply (multiRankEquiv q M).injective
      apply Fin.ext
      have hbr : (blockRankEquiv M (rightPortal M)).1 = 2*(M+1)-1 :=
        (blockRank_last_iff (rightPortal M)).2 rfl
      simp [lastIdx, multiRank_val, hbr]
      have hqdec : q = (q-1) + 1 := by omega
      rw [hqdec]
      simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
      omega
    rw [hl]
    unfold multiPos
    dsimp
    simp [rightPortal]
    have hq1nat : 1 ≤ q := by omega
    have hcast : (((q-1 : ℕ) : ℝ)) = (q:ℝ)-1 := by
      rw [Nat.cast_sub hq1nat]
      norm_num
    rw [hcast]
    have hden : (q:ℝ)-1 ≠ 0 := by
      have : (1:ℝ) < q := by exact_mod_cast (show 1 < q by omega)
      linarith
    field_simp [hden]
    ring

lemma indexed_unit_interval
    (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M)
    (D η : ℝ) (_hD0 : 0 < D) (hDq : D < 1/q)
    (hη0 : 0 < η) (hηD : η ≤ D/2) :
    ∀ i : Fin (q*(2*(M+1))),
      0 ≤ indexedPos q M D η ((1-q*D)/(q-1)) i ∧
      indexedPos q M D η ((1-q*D)/(q-1)) i ≤ 1 := by
  intro i
  let x := (multiRankEquiv q M).symm i
  have hb := multiPos_block_bounds hM D η ((1-q*D)/(q-1)) (le_of_lt hη0) hηD x
  have hh := corridor_gap_positive hq hDq
  have hstep0 : 0 ≤ D + (1-q*D)/(q-1) := by
    linarith [le_of_lt _hD0, le_of_lt hh]
  change
    0 ≤ multiPos q M D η ((1-q*D)/(q-1)) x ∧
      multiPos q M D η ((1-q*D)/(q-1)) x ≤ 1
  constructor
  · have hx0 : (0 : ℝ) ≤ x.1.1 := by positivity
    have hstart_nonneg :
        0 ≤ (x.1.1 : ℝ) * (D + (1-q*D)/(q-1)) :=
      mul_nonneg hx0 hstep0
    exact le_trans hstart_nonneg hb.1
  · have hq1nat : 1 ≤ q := by omega
    have hbinat : x.1.1 ≤ q-1 := by omega
    have hcast : (((q-1 : ℕ) : ℝ)) = (q:ℝ)-1 := by
      rw [Nat.cast_sub hq1nat]
      norm_num
    have hbi0 : (x.1.1:ℝ) ≤ ((q-1 : ℕ):ℝ) := by exact_mod_cast hbinat
    have hbi : (x.1.1:ℝ) ≤ (q:ℝ)-1 := by
      rw [hcast] at hbi0
      exact hbi0
    have hblock_upper :
        (x.1.1:ℝ)*(D+(1-q*D)/(q-1))+D ≤
          ((q:ℝ)-1)*(D+(1-q*D)/(q-1))+D := by
      simpa [add_comm] using
        (add_le_add_right (mul_le_mul_of_nonneg_right hbi hstep0) D)
    have hid : ((q:ℝ)-1)*(D+(1-q*D)/(q-1))+D = 1 := by
      have hq1R : (1:ℝ) < q := by exact_mod_cast (show 1 < q by omega)
      have hden : (q:ℝ)-1 ≠ 0 := by linarith
      field_simp [hden]
      ring
    calc
      multiPos q M D η ((1-q*D)/(q-1)) x
          ≤ (x.1.1:ℝ)*(D+(1-q*D)/(q-1))+D := hb.2
      _ ≤ (q-1:ℝ)*(D+(1-q*D)/(q-1))+D := hblock_upper
      _ = 1 := hid

/-- Full standard-`Fin` realization of the resonant lower construction. -/
theorem resonant_lower_article_model
    (q : ℕ) (hq : 4 ≤ q) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1/q)
    (L : ℕ) :
    ∃ M : ℕ, ∃ D η : ℝ,
      Ordered (indexedPos q M D η ((1-q*D)/(q-1))) ∧
      indexedPos q M D η ((1-q*D)/(q-1))
        (firstIdx (by positivity : 0 < q*(2*(M+1)))) = 0 ∧
      indexedPos q M D η ((1-q*D)/(q-1))
        (lastIdx (by positivity : 0 < q*(2*(M+1)))) = 1 ∧
      (∀ i, 0 ≤ indexedPos q M D η ((1-q*D)/(q-1)) i ∧
             indexedPos q M D η ((1-q*D)/(q-1)) i ≤ 1) ∧
      JumpCondition (indexedPos q M D η ((1-q*D)/(q-1))) (indexedPerm q M) ε ∧
      AllSlow (indexedPos q M D η ((1-q*D)/(q-1))) (indexedPerm q M) (2/q) L := by
  rcases resonant_arbitrarily_slow_generic q hq ε hε0 hε L with
    ⟨M,D,η,hM,hDε,hDq,hη0,h2ηD,hηD,hjump,hslow⟩
  have hh0 := corridor_gap_positive (by omega : 2 ≤ q) hDq
  refine ⟨M,D,η,?_,?_,?_,?_,?_,?_⟩
  · exact indexed_ordered q M (by omega) hM D η ((1-q*D)/(q-1))
      (by linarith) hη0 hh0 h2ηD hηD
  · exact (corridor_endpoints q M (by omega) hM D η).1
  · exact (corridor_endpoints q M (by omega) hM D η).2
  · exact indexed_unit_interval q M (by omega) hM D η (by linarith) hDq hη0 hηD
  · exact indexed_jump_of_generic hjump
  · exact indexed_all_slow_of_generic hslow

end LowerRealization
end Scottish164

/-! ==================== Sharp two-step example ==================== -/

namespace Scottish164

/-- Exact rational version of the eight-point sharpness example. -/
noncomputable def sharpPos : Fin 8 → ℝ :=
  ![0, (1/4:ℝ), (29/100:ℝ), (12/25:ℝ), (13/25:ℝ),
    (77/100:ℝ), (39/50:ℝ), 1]

def sharpPerm : Equiv.Perm (Fin 8) where
  toFun := ![1,3,0,5,2,4,7,6]
  invFun := ![2,0,4,1,5,3,7,6]
  left_inv := by intro x; fin_cases x <;> rfl
  right_inv := by intro x; fin_cases x <;> rfl

lemma sharp_ordered : Ordered sharpPos := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sharpPos] <;> norm_num

lemma sharp_jump : JumpCondition sharpPos sharpPerm (1/5) := by
  intro x
  fin_cases x <;> simp [sharpPos, sharpPerm] <;> norm_num

lemma sharp_one_move_small {x y : Fin 8} (h : Move sharpPerm x y) :
    |sharpPos y - sharpPos x| < 1/3 := by
  fin_cases x <;> fin_cases y <;>
    simp_all [Move, Adj, sharpPerm, sharpPos] <;> norm_num

lemma sharp_no_one_step (x : Fin 8) :
    ¬ EscapesWithin sharpPos sharpPerm (1/3) 1 x := by
  intro h
  rcases h with ⟨k,hk,y,hreach,hfar⟩
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hkcases with rfl | rfl
  · cases hreach
    norm_num at hfar
  · cases hreach with
    | tail h0 hmove =>
        cases h0
        have hs := sharp_one_move_small hmove
        linarith

lemma sharp_two_step_from_zero :
    EscapesWithin sharpPos sharpPerm (1/3) 2 (0 : Fin 8) := by
  refine ⟨2, by omega, (3 : Fin 8), ?_, ?_⟩
  · have h1 : ReachAt sharpPerm 1 (0 : Fin 8) (1 : Fin 8) := by
      simpa [sharpPerm] using ReachAt.one_exact sharpPerm (0 : Fin 8)
    have h2 : Move sharpPerm (1 : Fin 8) (3 : Fin 8) := Or.inl rfl
    exact ReachAt.tail h1 h2
  · simp [sharpPos]
    norm_num

/-- The two-step theorem cannot in general be improved to one step. -/
theorem two_step_bound_not_one_step :
    JumpCondition sharpPos sharpPerm (1/5) ∧
    (∀ x : Fin 8, ¬ EscapesWithin sharpPos sharpPerm (1/3) 1 x) ∧
    EscapesWithin sharpPos sharpPerm (1/3) 2 (0 : Fin 8) := by
  exact ⟨sharp_jump, sharp_no_one_step, sharp_two_step_from_zero⟩

end Scottish164

/-! ==================== Final article theorems ==================== -/

namespace Scottish164

noncomputable section

/-- A fully admissible permutation example in the exact finite formulation. -/
def PermutationExampleAt (ρ ε : ℝ) (L : ℕ) : Prop :=
  ∃ n : ℕ, ∃ hn : 2 ≤ n, ∃ pos : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n),
    Ordered pos ∧
    pos (firstIdx (by omega : 0 < n)) = 0 ∧
    pos (lastIdx (by omega : 0 < n)) = 1 ∧
    (∀ i : Fin n, 0 ≤ pos i ∧ pos i ≤ 1) ∧
    JumpCondition pos σ ε ∧
    AllSlow pos σ ρ L

def ArbitrarilySlowPermutation (ρ ε : ℝ) : Prop :=
  ∀ L : ℕ, PermutationExampleAt ρ ε L

/-- `c` is the exact threshold at radius `ρ`. -/
def IsExactThreshold (ρ c : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < c → ArbitrarilySlowPermutation ρ ε) ∧
  (∀ ε : ℝ, c ≤ ε → ¬ ArbitrarilySlowPermutation ρ ε)

/-- Complete literal-map phase diagram at radius `1/3`. -/
theorem literal_exact_phase_diagram :
    (∀ ε : ℝ, 0 < ε → ε < 1/3 →
      Ordered (literalTrapPos ε) ∧
      literalTrapPos ε 0 = 0 ∧ literalTrapPos ε 5 = 1 ∧
      JumpCondition (literalTrapPos ε) literalTrapT ε ∧
      PermanentTrap (literalTrapPos ε) literalTrapT (1/3)) ∧
    (∀ {n : ℕ} (pos : Fin n → ℝ) (T : Fin n → Fin n) (ε : ℝ),
      (1/3 : ℝ) ≤ ε → JumpCondition pos T ε →
      ∀ x : Fin n, EscapesWithin pos T (1/3) 1 x) := by
  constructor
  · intro ε hε0 hε
    exact literal_permanent_trap ε hε0 hε
  · intro n pos T ε hε hj x
    exact literal_large_epsilon_one_step pos T ε hε hj x

/-- Resonant lower bound in the exact standard-`Fin` model. -/
theorem resonant_permutation_arbitrarily_slow
    (q : ℕ) (hq : 4 ≤ q) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1/q) :
    ArbitrarilySlowPermutation (2/q) ε := by
  intro L
  rcases LowerRealization.resonant_lower_article_model q hq ε hε0 hε L with
    ⟨M,D,η,hord,hzero,hone,hunit,hjump,hslow⟩
  let n : ℕ := q*(2*(M+1))
  have hn : 2 ≤ n := by
    dsimp [n]
    have hq1 : 1 ≤ q := by omega
    have hB : 2 ≤ 2*(M+1) := by omega
    exact le_trans hB (by simpa using Nat.mul_le_mul_right (2*(M+1)) hq1)
  refine ⟨n,hn,LowerRealization.indexedPos q M D η ((1-q*D)/(q-1)),
    LowerRealization.indexedPerm q M,?_⟩
  simpa [n] using And.intro hord
    (And.intro hzero (And.intro hone (And.intro hunit (And.intro hjump hslow))))

/-- Special lower half of the sharp threshold at radius `1/3`. -/
theorem problem164_permutation_arbitrarily_slow
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1/6) :
    ArbitrarilySlowPermutation (1/3) ε := by
  have hq : (1/6 : ℝ) = 1/(6:ℝ) := by norm_num
  have hrho : (1/3 : ℝ) = 2/(6:ℝ) := by norm_num
  rw [hrho]
  apply resonant_permutation_arbitrarily_slow 6 (by omega) ε hε0
  simpa [hq] using hε

/-- At and above `1/6`, arbitrary all-start delay is impossible. -/
theorem problem164_permutation_not_arbitrarily_slow
    (ε : ℝ) (hε : (1/6 : ℝ) ≤ ε) :
    ¬ ArbitrarilySlowPermutation (1/3) ε := by
  intro hslow
  rcases hslow 2 with ⟨n,hn,pos,σ,hord,hzero,hone,hunit,hjump,hall⟩
  rcases problem164_two_step_upper hn pos σ ε hε hord hzero hone hjump with ⟨x,hesc⟩
  exact hall x hesc

/-- Exact `1/6` permutation threshold at radius `1/3`. -/
theorem problem164_permutation_exact_threshold :
    IsExactThreshold (1/3) (1/6) := by
  exact ⟨problem164_permutation_arbitrarily_slow,
    problem164_permutation_not_arbitrarily_slow⟩

/-- General upper half `ε ≥ ρ/2`. -/
theorem general_half_threshold_upper
    (ρ ε : ℝ) (hρ0 : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hε : ρ/2 ≤ ε) :
    ¬ ArbitrarilySlowPermutation ρ ε := by
  intro hslow
  rcases hslow 2 with ⟨n,hn,pos,σ,hord,hzero,hone,hunit,hjump,hall⟩
  rcases general_two_step_upper hn pos σ ρ ε hρ0 hρhalf hε hord hzero hone hjump with
    ⟨x,hesc⟩
  exact hall x hesc

/-- Exact resonant family `ε_*(2/q)=1/q`. -/
theorem resonant_exact_threshold
    (q : ℕ) (hq : 4 ≤ q) :
    IsExactThreshold (2/q) (1/q) := by
  constructor
  · intro ε hε0 hε
    exact resonant_permutation_arbitrarily_slow q hq ε hε0 hε
  · intro ε hε
    apply general_half_threshold_upper (2/q) ε
    · positivity
    · have hqR : (4:ℝ) ≤ q := by exact_mod_cast hq
      have hqpos : (0:ℝ) < q := by positivity
      apply (div_le_iff₀ hqpos).2
      nlinarith
    · have heq : ((2/(q:ℝ))/2) = 1/(q:ℝ) := by ring
      rw [heq]
      exact hε

end
end Scottish164

#print axioms Scottish164.problem164_permutation_exact_threshold
#print axioms Scottish164.resonant_exact_threshold
#print axioms Scottish164.literal_exact_phase_diagram
#print axioms Scottish164.problem164_two_step_upper
#print axioms Scottish164.LowerRealization.resonant_lower_article_model

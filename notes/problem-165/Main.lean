import Mathlib

/-!
# Scottish Book Problem 165: historical closed-ball interpretation in dimension one

This file gives an axiom-free Lean formalization of a negative answer to the
closed-ball interpretation of Ulam's Problem 165 already in dimension one.

The source sequence is an enumeration of all rational points of `[-1,1]`, with
`0,1` as its first two terms.  The initial one-to-one assignment swaps these two
points.  At each later stage the target is chosen to minimize the exact finite
bi-Lipschitz objective.  We encode the finite Lipschitz constants in `ENNReal`;
a collision has infinite inverse cost.  Compactness therefore gives a genuine
fresh minimizer at every stage.

Finally, a hypothetical uniform finite bound on all stage costs gives a
bi-Lipschitz map on a dense rational subset.  The forward estimate is extended
by the McShane extension theorem (`LipschitzOnWith.extend_real`), while the
inverse estimate extends by density.  Hence one obtains a continuous injective
map of `[-1,1]` to itself sending `0` to `1` and `1` to `0`.  Such a map must be
strictly monotone or strictly antitone, and either possibility is impossible.

There are no `sorry`, `admit`, or user-defined axioms in this file.
-/

namespace Ulam165HistoricalBall

open Set Function Filter Topology
open scoped ENNReal BigOperators

noncomputable section

/-! ## 1. The closed unit interval and its rational points -/

abbrev Ball1 := Set.Icc (-1 : ℝ) 1
abbrev RatBall1 := Set.Icc (-1 : ℚ) 1

def ballNegOne : Ball1 := ⟨-1, by norm_num⟩
def ballZero : Ball1 := ⟨0, by norm_num⟩
def ballOne : Ball1 := ⟨1, by norm_num⟩

def ratZero : RatBall1 := ⟨0, by norm_num⟩
def ratOne : RatBall1 := ⟨1, by norm_num⟩

def ratToBall (q : RatBall1) : Ball1 :=
  ⟨(q.1 : ℝ), by
    constructor
    · exact_mod_cast q.2.1
    · exact_mod_cast q.2.2⟩

@[simp] theorem ratToBall_zero : ratToBall ratZero = ballZero := by
  apply Subtype.ext
  norm_num [ratToBall, ratZero, ballZero]

@[simp] theorem ratToBall_one : ratToBall ratOne = ballOne := by
  apply Subtype.ext
  norm_num [ratToBall, ratOne, ballOne]

theorem ratToBall_injective : Function.Injective ratToBall := by
  intro a b hab
  apply Subtype.ext
  have hreal : (a.1 : ℝ) = (b.1 : ℝ) := congrArg Subtype.val hab
  exact_mod_cast hreal

/-! We reserve `0` and `1` as the first two source points and enumerate every
other rational point afterwards. -/

abbrev RatTail := {q : RatBall1 // q ≠ ratZero ∧ q ≠ ratOne}
abbrev RatNegInterior := Set.Ioo (-1 : ℚ) 0

private def negInteriorToTail (x : RatNegInterior) : RatTail := by
  refine ⟨⟨x.1, ?_⟩, ?_, ?_⟩
  · exact ⟨le_of_lt x.2.1, le_trans (le_of_lt x.2.2) (by norm_num)⟩
  · intro h
    have hv : x.1 = 0 := congrArg (fun q : RatBall1 => q.1) h
    exact (ne_of_lt x.2.2) hv
  · intro h
    have hv : x.1 = 1 := congrArg (fun q : RatBall1 => q.1) h
    linarith [x.2.2]

private theorem negInteriorToTail_injective : Function.Injective negInteriorToTail := by
  intro a b h
  apply Subtype.ext
  have h1 : ((negInteriorToTail a : RatTail) : RatBall1).1 =
      ((negInteriorToTail b : RatTail) : RatBall1).1 :=
    congrArg (fun q : RatTail => ((q : RatBall1).1)) h
  exact h1

noncomputable local instance : Infinite RatTail := by
  let hInf : Infinite RatNegInterior :=
    Set.Ioo.infinite (by norm_num : (-1 : ℚ) < 0)
  exact @Infinite.of_injective RatTail RatNegInterior hInf
    negInteriorToTail negInteriorToTail_injective

noncomputable local instance : Denumerable RatTail :=
  Denumerable.ofEncodableOfInfinite RatTail

noncomputable def tailEquiv : RatTail ≃ ℕ := Denumerable.eqv RatTail

noncomputable local instance : Infinite Ball1 := by
  exact Infinite.of_injective
    (fun q : RatTail => ratToBall (q : RatBall1))
    (ratToBall_injective.comp Subtype.val_injective)

noncomputable def sourceQ : ℕ → RatBall1
  | 0 => ratZero
  | 1 => ratOne
  | n + 2 => (tailEquiv.symm n : RatTail)

@[simp] theorem sourceQ_zero : sourceQ 0 = ratZero := rfl
@[simp] theorem sourceQ_one : sourceQ 1 = ratOne := rfl
@[simp] theorem sourceQ_add_two (n : ℕ) :
    sourceQ (n + 2) = (tailEquiv.symm n : RatTail) := rfl

private theorem sourceQ_tail_ne_zero (n : ℕ) : sourceQ (n + 2) ≠ ratZero := by
  exact (tailEquiv.symm n).2.1

private theorem sourceQ_tail_ne_one (n : ℕ) : sourceQ (n + 2) ≠ ratOne := by
  exact (tailEquiv.symm n).2.2

theorem sourceQ_injective : Function.Injective sourceQ := by
  intro m n h
  rcases m with (_ | _ | m) <;> rcases n with (_ | _ | n)
  · rfl
  · exfalso
    have hv : (0 : ℚ) = 1 := congrArg Subtype.val h
    norm_num at hv
  · exact (sourceQ_tail_ne_zero n (h.symm)).elim
  · exfalso
    have hv : (1 : ℚ) = 0 := congrArg Subtype.val h
    norm_num at hv
  · rfl
  · exact (sourceQ_tail_ne_one n (h.symm)).elim
  · exact (sourceQ_tail_ne_zero m h).elim
  · exact (sourceQ_tail_ne_one m h).elim
  · have ht : tailEquiv.symm m = tailEquiv.symm n := by
      apply Subtype.ext
      exact h
    have hmn : m = n := by
      simpa using congrArg tailEquiv ht
    omega

theorem sourceQ_surjective : Function.Surjective sourceQ := by
  intro q
  by_cases h0 : q = ratZero
  · exact ⟨0, by simp [h0]⟩
  by_cases h1 : q = ratOne
  · exact ⟨1, by simp [h1]⟩
  let t : RatTail := ⟨q, h0, h1⟩
  refine ⟨tailEquiv t + 2, ?_⟩
  change ((tailEquiv.symm (tailEquiv t) : RatTail) : RatBall1) = q
  simp [t]

noncomputable def source (n : ℕ) : Ball1 := ratToBall (sourceQ n)

@[simp] theorem source_zero : source 0 = ballZero := by
  simp [source]

@[simp] theorem source_one : source 1 = ballOne := by
  simp [source]

theorem source_injective : Function.Injective source :=
  ratToBall_injective.comp sourceQ_injective

def IsRationalPoint (x : Ball1) : Prop := ∃ q : ℚ, (q : ℝ) = x.1

theorem source_rational (n : ℕ) : IsRationalPoint (source n) := by
  refine ⟨(sourceQ n).1, ?_⟩
  rfl

/-! Density of the rational source set. -/

private theorem projIcc_real_surjective :
    Function.Surjective (Set.projIcc (-1 : ℝ) 1 (by norm_num)) := by
  intro x
  refine ⟨x.1, ?_⟩
  exact Set.projIcc_val (by norm_num) x

private theorem denseRange_projected_rat :
    DenseRange (fun q : ℚ => Set.projIcc (-1 : ℝ) 1 (by norm_num) (q : ℝ)) := by
  let g : ℝ → Ball1 := Set.projIcc (-1 : ℝ) 1 (by norm_num)
  have hg_dense : DenseRange g := projIcc_real_surjective.denseRange
  have hg_cont : Continuous g := by
    simpa [g] using
      (continuous_projIcc : Continuous (Set.projIcc (-1 : ℝ) 1 (by norm_num)))
  have hcomp := hg_dense.comp (Rat.denseRange_cast (𝕜 := ℝ)) hg_cont
  simpa [Function.comp_def, g] using hcomp

private def clampRat (q : ℚ) : RatBall1 :=
  Set.projIcc (-1 : ℚ) 1 (by norm_num) q

private theorem ratToBall_clampRat (q : ℚ) :
    ratToBall (clampRat q) =
      Set.projIcc (-1 : ℝ) 1 (by norm_num) (q : ℝ) := by
  apply Subtype.ext
  simp [ratToBall, clampRat, Set.coe_projIcc]

private theorem ratToBall_denseRange : DenseRange ratToBall := by
  have hsub :
      Set.range (fun q : ℚ => Set.projIcc (-1 : ℝ) 1 (by norm_num) (q : ℝ)) ⊆
        Set.range ratToBall := by
    rintro x ⟨q, rfl⟩
    exact ⟨clampRat q, ratToBall_clampRat q⟩
  exact Dense.mono hsub denseRange_projected_rat

theorem source_denseRange : DenseRange source := by
  have hrange : Set.range source = Set.range ratToBall := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨sourceQ n, rfl⟩
    · rintro ⟨q, rfl⟩
      rcases sourceQ_surjective q with ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  rw [denseRange_iff_closure_range]
  rw [hrange]
  exact ratToBall_denseRange.closure_range

/-! ## 2. Exact finite bi-Lipschitz objective -/

/-- First `n` points of a sequence. -/
def srcPrefix {α : Type*} (f : ℕ → α) (n : ℕ) : Fin n → α := fun i => f i.1

/-- Extended-real forward Lipschitz record of a finite assignment. -/
def forwardCost {n : ℕ} (p q : Fin n → Ball1) : ENNReal :=
  Finset.univ.sup fun i : Fin n =>
    Finset.univ.sup fun j : Fin n =>
      edist (q i) (q j) / edist (p i) (p j)

/-- Extended-real inverse Lipschitz record of a finite assignment. -/
def inverseCost {n : ℕ} (p q : Fin n → Ball1) : ENNReal :=
  Finset.univ.sup fun i : Fin n =>
    Finset.univ.sup fun j : Fin n =>
      edist (p i) (p j) / edist (q i) (q j)

/-- Ulam's finite objective `L + L'`, embedded in `ENNReal`. -/
def biCost {n : ℕ} (p q : Fin n → Ball1) : ENNReal :=
  forwardCost p q + inverseCost p q

private theorem term_le_forwardCost {n : ℕ} (p q : Fin n → Ball1) (i j : Fin n) :
    edist (q i) (q j) / edist (p i) (p j) ≤ forwardCost p q := by
  apply le_trans (Finset.le_sup (s := Finset.univ) (f := fun j : Fin n =>
    edist (q i) (q j) / edist (p i) (p j)) (Finset.mem_univ j))
  exact Finset.le_sup (s := Finset.univ) (f := fun i : Fin n =>
    Finset.univ.sup fun j : Fin n =>
      edist (q i) (q j) / edist (p i) (p j)) (Finset.mem_univ i)

private theorem term_le_inverseCost {n : ℕ} (p q : Fin n → Ball1) (i j : Fin n) :
    edist (p i) (p j) / edist (q i) (q j) ≤ inverseCost p q := by
  apply le_trans (Finset.le_sup (s := Finset.univ) (f := fun j : Fin n =>
    edist (p i) (p j) / edist (q i) (q j)) (Finset.mem_univ j))
  exact Finset.le_sup (s := Finset.univ) (f := fun i : Fin n =>
    Finset.univ.sup fun j : Fin n =>
      edist (p i) (p j) / edist (q i) (q j)) (Finset.mem_univ i)

private theorem forwardCost_le_biCost {n : ℕ} (p q : Fin n → Ball1) :
    forwardCost p q ≤ biCost p q := by
  exact le_add_right (le_refl _)

private theorem inverseCost_le_biCost {n : ℕ} (p q : Fin n → Ball1) :
    inverseCost p q ≤ biCost p q := by
  exact le_add_left (le_refl _)

private theorem ratio_lt_top_of_injective {n : ℕ}
    {p q : Fin n → Ball1} (hp : Function.Injective p)
    (i j : Fin n) :
    edist (q i) (q j) / edist (p i) (p j) < (⊤ : ENNReal) := by
  by_cases hij : i = j
  · subst j
    simp
  · apply ENNReal.div_lt_top
    · exact edist_ne_top _ _
    · intro h0
      exact hp.ne hij (edist_eq_zero.mp h0)

private theorem inverseRatio_lt_top_of_injective {n : ℕ}
    {p q : Fin n → Ball1} (hq : Function.Injective q)
    (i j : Fin n) :
    edist (p i) (p j) / edist (q i) (q j) < (⊤ : ENNReal) := by
  by_cases hij : i = j
  · subst j
    simp
  · apply ENNReal.div_lt_top
    · exact edist_ne_top _ _
    · intro h0
      exact hq.ne hij (edist_eq_zero.mp h0)

private theorem forwardCost_lt_top_of_injective {n : ℕ}
    {p q : Fin n → Ball1} (hp : Function.Injective p) :
    forwardCost p q < (⊤ : ENNReal) := by
  unfold forwardCost
  rw [Finset.sup_lt_iff (by simp : (⊥ : ENNReal) < ⊤)]
  intro i hi
  rw [Finset.sup_lt_iff (by simp : (⊥ : ENNReal) < ⊤)]
  intro j hj
  exact ratio_lt_top_of_injective hp i j

private theorem inverseCost_lt_top_of_injective {n : ℕ}
    {p q : Fin n → Ball1} (hq : Function.Injective q) :
    inverseCost p q < (⊤ : ENNReal) := by
  unfold inverseCost
  rw [Finset.sup_lt_iff (by simp : (⊥ : ENNReal) < ⊤)]
  intro i hi
  rw [Finset.sup_lt_iff (by simp : (⊥ : ENNReal) < ⊤)]
  intro j hj
  exact inverseRatio_lt_top_of_injective hq i j

private theorem biCost_lt_top_of_injective {n : ℕ}
    {p q : Fin n → Ball1} (hp : Function.Injective p)
    (hq : Function.Injective q) :
    biCost p q < (⊤ : ENNReal) := by
  exact (ENNReal.add_lt_top).2
    ⟨forwardCost_lt_top_of_injective hp,
      inverseCost_lt_top_of_injective hq⟩

/-! ## 3. A genuine greedy minimizer exists at every finite stage -/

structure State (n : ℕ) where
  target : Fin n → Ball1
  target_injective : Function.Injective target

/-- Nondependent wrapper around `Fin.snoc`.  Giving the constant motive explicitly
keeps elaboration stable across Mathlib/Core versions. -/
def finSnoc {n : ℕ} (q : Fin n → Ball1) (y : Ball1) : Fin (n + 1) → Ball1 :=
  Fin.snoc (α := fun _ : Fin (n + 1) => Ball1) q y

@[simp] theorem finSnoc_castSucc {n : ℕ} (q : Fin n → Ball1) (y : Ball1) (i : Fin n) :
    finSnoc q y i.castSucc = q i := by
  simp [finSnoc]

@[simp] theorem finSnoc_last {n : ℕ} (q : Fin n → Ball1) (y : Ball1) :
    finSnoc q y (Fin.last n) = y := by
  simp [finSnoc]

private theorem finSnoc_injective_of_injective {n : ℕ} {q : Fin n → Ball1} {y : Ball1}
    (hq : Function.Injective q) (hy : y ∉ Set.range q) :
    Function.Injective (finSnoc q y) := by
  simpa [finSnoc] using (Fin.snoc_injective_of_injective hq hy)

/-- Cost of adding a candidate image `y` to a finite injective state. -/
def candidateCost {n : ℕ} (s : State n) (y : Ball1) : ENNReal :=
  biCost (srcPrefix source (n + 1)) (finSnoc s.target y)

def IsGreedyChoice {n : ℕ} (s : State n) (y : Ball1) : Prop :=
  ∀ z : Ball1, candidateCost s y ≤ candidateCost s z

private theorem continuous_snoc_eval {n : ℕ} (q : Fin n → Ball1) (i : Fin (n + 1)) :
    Continuous (fun y : Ball1 => finSnoc q y i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hfun : (fun y : Ball1 => finSnoc q y (Fin.last n)) = id := by
      funext y
      exact finSnoc_last q y
    rw [hfun]
    exact continuous_id
  · have hfun : (fun y : Ball1 => finSnoc q y j.castSucc) = (fun _ : Ball1 => q j) := by
      funext y
      exact finSnoc_castSucc q y j
    rw [hfun]
    exact continuous_const

private theorem continuous_forward_ratio {n : ℕ} (s : State n)
    (i j : Fin (n + 1)) :
    Continuous (fun y : Ball1 =>
      edist (finSnoc s.target y i) (finSnoc s.target y j) /
        edist (srcPrefix source (n + 1) i) (srcPrefix source (n + 1) j)) := by
  by_cases hij : i = j
  · subst j
    simpa using (continuous_const : Continuous (fun _ : Ball1 => (0 : ENNReal)))
  · have hnum : Continuous (fun y : Ball1 =>
        edist (finSnoc s.target y i) (finSnoc s.target y j)) :=
      (continuous_snoc_eval s.target i).edist (continuous_snoc_eval s.target j)
    have hpij : srcPrefix source (n + 1) i ≠ srcPrefix source (n + 1) j := by
      intro hsrc
      apply hij
      apply Fin.ext
      exact source_injective hsrc
    have hden : edist (srcPrefix source (n + 1) i) (srcPrefix source (n + 1) j) ≠ 0 := by
      intro h0
      exact hpij (edist_eq_zero.mp h0)
    exact (ENNReal.continuous_div_const _ hden).comp hnum

private theorem continuous_inverse_ratio {n : ℕ} (s : State n)
    (i j : Fin (n + 1)) :
    Continuous (fun y : Ball1 =>
      edist (srcPrefix source (n + 1) i) (srcPrefix source (n + 1) j) /
        edist (finSnoc s.target y i) (finSnoc s.target y j)) := by
  by_cases hij : i = j
  · subst j
    simpa using (continuous_const : Continuous (fun _ : Ball1 => (0 : ENNReal)))
  · have hden : Continuous (fun y : Ball1 =>
        edist (finSnoc s.target y i) (finSnoc s.target y j)) :=
      (continuous_snoc_eval s.target i).edist (continuous_snoc_eval s.target j)
    have hnumtop :
        edist (srcPrefix source (n + 1) i) (srcPrefix source (n + 1) j) ≠ (⊤ : ENNReal) :=
      edist_ne_top _ _
    have hinv : Continuous (fun y : Ball1 =>
        (edist (finSnoc s.target y i) (finSnoc s.target y j))⁻¹) :=
      hden.inv
    have hmul : Continuous
        ((fun x : ENNReal =>
            edist (srcPrefix source (n + 1) i) (srcPrefix source (n + 1) j) * x) ∘
          (fun y : Ball1 =>
            (edist (finSnoc s.target y i) (finSnoc s.target y j))⁻¹)) :=
      (ENNReal.continuous_const_mul hnumtop).comp hinv
    rw [show
      (fun y : Ball1 =>
        edist (srcPrefix source (n + 1) i) (srcPrefix source (n + 1) j) /
          edist (finSnoc s.target y i) (finSnoc s.target y j)) =
      ((fun x : ENNReal =>
          edist (srcPrefix source (n + 1) i) (srcPrefix source (n + 1) j) * x) ∘
        (fun y : Ball1 =>
          (edist (finSnoc s.target y i) (finSnoc s.target y j))⁻¹)) by
        funext y
        simp only [Function.comp_apply, div_eq_mul_inv]]
    exact hmul

private theorem candidateCost_continuous {n : ℕ} (s : State n) :
    Continuous (candidateCost s) := by
  have hf : Continuous (fun y : Ball1 =>
      forwardCost (srcPrefix source (n + 1)) (finSnoc s.target y)) := by
    refine Continuous.finset_sup_apply ?_
    intro i hi
    refine Continuous.finset_sup_apply ?_
    intro j hj
    exact continuous_forward_ratio s i j
  have hi : Continuous (fun y : Ball1 =>
      inverseCost (srcPrefix source (n + 1)) (finSnoc s.target y)) := by
    refine Continuous.finset_sup_apply ?_
    intro i hi
    refine Continuous.finset_sup_apply ?_
    intro j hj
    exact continuous_inverse_ratio s i j
  unfold candidateCost biCost
  exact hf.add hi

private theorem srcPrefix_source_injective (n : ℕ) :
    Function.Injective (srcPrefix source n) := by
  intro i j h
  apply Fin.ext
  exact source_injective h

private theorem exists_fresh_target {n : ℕ} (s : State n) :
    ∃ y : Ball1, y ∉ Set.range s.target := by
  have hfinite : (Set.range s.target).Finite := Set.finite_range s.target
  exact hfinite.exists_notMem

private theorem fresh_candidate_finite {n : ℕ} (s : State n) {y : Ball1}
    (hy : y ∉ Set.range s.target) : candidateCost s y < (⊤ : ENNReal) := by
  have ht : Function.Injective (finSnoc s.target y) :=
    finSnoc_injective_of_injective s.target_injective hy
  exact biCost_lt_top_of_injective (srcPrefix_source_injective (n + 1)) ht

private theorem colliding_candidate_top {n : ℕ} (s : State n) {y : Ball1}
    (hy : y ∈ Set.range s.target) : candidateCost s y = (⊤ : ENNReal) := by
  rcases hy with ⟨i, rfl⟩
  let ilast : Fin (n + 1) := Fin.last n
  let iold : Fin (n + 1) := i.castSucc
  have hsrc : srcPrefix source (n + 1) iold ≠ srcPrefix source (n + 1) ilast := by
    intro hsrc
    have hv : i.1 = n := by
      apply source_injective
      simpa [srcPrefix, iold, ilast] using hsrc
    omega
  have hnum : edist (srcPrefix source (n + 1) iold) (srcPrefix source (n + 1) ilast) ≠ 0 := by
    intro h0
    exact hsrc (edist_eq_zero.mp h0)
  have hden : edist (finSnoc s.target (s.target i) iold)
      (finSnoc s.target (s.target i) ilast) = 0 := by
    simp [iold, ilast]
  have hterm :
      edist (srcPrefix source (n + 1) iold) (srcPrefix source (n + 1) ilast) /
          edist (finSnoc s.target (s.target i) iold)
            (finSnoc s.target (s.target i) ilast) = (⊤ : ENNReal) := by
    exact (ENNReal.div_eq_top).2 (Or.inl ⟨hnum, hden⟩)
  have hinv : inverseCost (srcPrefix source (n + 1))
      (finSnoc s.target (s.target i)) = (⊤ : ENNReal) := by
    apply top_unique
    calc
      (⊤ : ENNReal) =
          edist (srcPrefix source (n + 1) iold) (srcPrefix source (n + 1) ilast) /
            edist (finSnoc s.target (s.target i) iold)
              (finSnoc s.target (s.target i) ilast) := hterm.symm
      _ ≤ Finset.univ.sup (fun j : Fin (n + 1) =>
          edist (srcPrefix source (n + 1) iold) (srcPrefix source (n + 1) j) /
            edist (finSnoc s.target (s.target i) iold)
              (finSnoc s.target (s.target i) j)) := by
        exact Finset.le_sup
          (f := fun j : Fin (n + 1) =>
            edist (srcPrefix source (n + 1) iold) (srcPrefix source (n + 1) j) /
              edist (finSnoc s.target (s.target i) iold)
                (finSnoc s.target (s.target i) j))
          (Finset.mem_univ ilast)
      _ ≤ inverseCost (srcPrefix source (n + 1))
          (finSnoc s.target (s.target i)) := by
        unfold inverseCost
        exact Finset.le_sup
          (f := fun i' : Fin (n + 1) =>
            Finset.univ.sup (fun j : Fin (n + 1) =>
              edist (srcPrefix source (n + 1) i') (srcPrefix source (n + 1) j) /
                edist (finSnoc s.target (s.target i) i')
                  (finSnoc s.target (s.target i) j)))
          (Finset.mem_univ iold)
  simp [candidateCost, biCost, hinv]

theorem exists_greedyChoice {n : ℕ} (s : State n) :
    ∃ y : Ball1, IsGreedyChoice s y ∧ y ∉ Set.range s.target := by
  have hc := candidateCost_continuous s
  rcases isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn with
    ⟨y, hyu, hymin⟩
  rcases exists_fresh_target s with ⟨z, hzfresh⟩
  have hzfinite := fresh_candidate_finite s hzfresh
  have hyfresh : y ∉ Set.range s.target := by
    intro hyold
    have hytop := colliding_candidate_top s hyold
    have hle : candidateCost s y ≤ candidateCost s z := hymin (by simp)
    rw [hytop] at hle
    exact (not_le_of_gt hzfinite) hle
  refine ⟨y, ?_, hyfresh⟩
  intro z'
  exact hymin (by simp)

noncomputable def greedyPoint {n : ℕ} (s : State n) : Ball1 :=
  Classical.choose (exists_greedyChoice s)

theorem greedyPoint_isGreedy {n : ℕ} (s : State n) :
    IsGreedyChoice s (greedyPoint s) :=
  (Classical.choose_spec (exists_greedyChoice s)).1

theorem greedyPoint_fresh {n : ℕ} (s : State n) :
    greedyPoint s ∉ Set.range s.target :=
  (Classical.choose_spec (exists_greedyChoice s)).2

noncomputable def nextState {n : ℕ} (s : State n) : State (n + 1) where
  target := finSnoc s.target (greedyPoint s)
  target_injective :=
    finSnoc_injective_of_injective s.target_injective (greedyPoint_fresh s)

@[simp] theorem nextState_castSucc {n : ℕ} (s : State n) (i : Fin n) :
    (nextState s).target i.castSucc = s.target i := by
  simp [nextState]

@[simp] theorem nextState_last {n : ℕ} (s : State n) :
    (nextState s).target (Fin.last n) = greedyPoint s := by
  simp [nextState]

/-! ## 4. The infinite greedy run -/

private def initialTarget : Fin 2 → Ball1 :=
  Fin.cases ballOne (Fin.cases ballZero Fin.elim0)

private theorem initialTarget_injective : Function.Injective initialTarget := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have hv : (1 : ℝ) = 0 := congrArg Subtype.val hij
    norm_num [initialTarget, ballZero, ballOne] at hv
  · exfalso
    have hv : (0 : ℝ) = 1 := congrArg Subtype.val hij
    norm_num [initialTarget, ballZero, ballOne] at hv
  · rfl

noncomputable def initialState : State 2 where
  target := initialTarget
  target_injective := initialTarget_injective

noncomputable def states : (k : ℕ) → State (Nat.succ (Nat.succ k))
  | 0 => initialState
  | k + 1 => nextState (states k)

noncomputable def runTarget : ℕ → Ball1
  | 0 => ballOne
  | 1 => ballZero
  | n + 2 => greedyPoint (states n)

@[simp] theorem runTarget_zero : runTarget 0 = ballOne := rfl
@[simp] theorem runTarget_one : runTarget 1 = ballZero := rfl
@[simp] theorem runTarget_add_two (n : ℕ) :
    runTarget (n + 2) = greedyPoint (states n) := rfl

theorem states_target_eq_runTarget :
    ∀ (k : ℕ) (i : Fin (Nat.succ (Nat.succ k))),
      (states k).target i = runTarget i.1
  | 0, i => by
      fin_cases i
      · rfl
      · rfl
  | k + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [states, runTarget]
      · simpa [states] using states_target_eq_runTarget k j

theorem runTarget_injective : Function.Injective runTarget := by
  intro i j hij
  let k := max i j
  let ii : Fin (Nat.succ (Nat.succ k)) := ⟨i, by omega⟩
  let jj : Fin (Nat.succ (Nat.succ k)) := ⟨j, by omega⟩
  have hs : (states k).target ii = (states k).target jj := by
    rw [states_target_eq_runTarget k ii, states_target_eq_runTarget k jj]
    simpa [ii, jj] using hij
  have hijFin := (states k).target_injective hs
  exact congrArg Fin.val hijFin

/-- Every post-initial value of the run is an actual global minimizer of Ulam's
finite objective among all points of the closed ball. -/
theorem runTarget_greedy (k : ℕ) :
    IsGreedyChoice (states k) (runTarget (k + 2)) := by
  simpa using greedyPoint_isGreedy (states k)

/-- Exact cost at the stage containing the first `k+2` source points. -/
def stageCost (k : ℕ) : ENNReal :=
  biCost (srcPrefix source (Nat.succ (Nat.succ k))) (states k).target

private theorem stage_forward_pair_le {K : NNReal}
    (hbound : ∀ k : ℕ, stageCost k ≤ (K : ENNReal))
    (i j : ℕ) :
    edist (runTarget i) (runTarget j) ≤
      (K : ENNReal) * edist (source i) (source j) := by
  by_cases hij : i = j
  · subst j
    simp
  let k := max i j
  let ii : Fin (Nat.succ (Nat.succ k)) := ⟨i, by omega⟩
  let jj : Fin (Nat.succ (Nat.succ k)) := ⟨j, by omega⟩
  have hijFin : ii ≠ jj := by
    intro h
    apply hij
    exact congrArg Fin.val h
  have hratio :
      edist ((states k).target ii) ((states k).target jj) /
          edist (srcPrefix source (Nat.succ (Nat.succ k)) ii)
            (srcPrefix source (Nat.succ (Nat.succ k)) jj) ≤ (K : ENNReal) := by
    calc
      _ ≤ forwardCost (srcPrefix source (Nat.succ (Nat.succ k)))
          (states k).target := term_le_forwardCost _ _ ii jj
      _ ≤ stageCost k := forwardCost_le_biCost _ _
      _ ≤ (K : ENNReal) := hbound k
  have hden0 :
      edist (srcPrefix source (Nat.succ (Nat.succ k)) ii)
        (srcPrefix source (Nat.succ (Nat.succ k)) jj) ≠ 0 := by
    intro h0
    exact (srcPrefix_source_injective _).ne hijFin (edist_eq_zero.mp h0)
  have hdenTop :
      edist (srcPrefix source (Nat.succ (Nat.succ k)) ii)
        (srcPrefix source (Nat.succ (Nat.succ k)) jj) ≠ (⊤ : ENNReal) :=
    edist_ne_top _ _
  have hmul := (ENNReal.div_le_iff hden0 hdenTop).1 hratio
  rw [states_target_eq_runTarget k ii, states_target_eq_runTarget k jj] at hmul
  simpa [srcPrefix, ii, jj] using hmul

private theorem stage_inverse_pair_le {K : NNReal}
    (hbound : ∀ k : ℕ, stageCost k ≤ (K : ENNReal))
    (i j : ℕ) :
    edist (source i) (source j) ≤
      (K : ENNReal) * edist (runTarget i) (runTarget j) := by
  by_cases hij : i = j
  · subst j
    simp
  let k := max i j
  let ii : Fin (Nat.succ (Nat.succ k)) := ⟨i, by omega⟩
  let jj : Fin (Nat.succ (Nat.succ k)) := ⟨j, by omega⟩
  have hijFin : ii ≠ jj := by
    intro h
    apply hij
    exact congrArg Fin.val h
  have hratio :
      edist (srcPrefix source (Nat.succ (Nat.succ k)) ii)
          (srcPrefix source (Nat.succ (Nat.succ k)) jj) /
        edist ((states k).target ii) ((states k).target jj) ≤ (K : ENNReal) := by
    calc
      _ ≤ inverseCost (srcPrefix source (Nat.succ (Nat.succ k)))
          (states k).target := term_le_inverseCost _ _ ii jj
      _ ≤ stageCost k := inverseCost_le_biCost _ _
      _ ≤ (K : ENNReal) := hbound k
  have hden0 : edist ((states k).target ii) ((states k).target jj) ≠ 0 := by
    intro h0
    exact (states k).target_injective.ne hijFin (edist_eq_zero.mp h0)
  have hdenTop : edist ((states k).target ii) ((states k).target jj) ≠ (⊤ : ENNReal) :=
    edist_ne_top _ _
  have hmul := (ENNReal.div_le_iff hden0 hdenTop).1 hratio
  rw [states_target_eq_runTarget k ii, states_target_eq_runTarget k jj] at hmul
  simpa [srcPrefix, ii, jj] using hmul

/-! ## 5. Dense extension and the one-dimensional topological obstruction -/

noncomputable def sourceIndex (x : Ball1) : ℕ := by
  classical
  exact if h : x ∈ Set.range source then Classical.choose h else 0

@[simp] theorem sourceIndex_source (n : ℕ) : sourceIndex (source n) = n := by
  classical
  unfold sourceIndex
  split
  · rename_i h
    apply source_injective
    exact Classical.choose_spec h
  · rename_i h
    exact (h ⟨n, rfl⟩).elim

noncomputable def partialTarget (x : Ball1) : Ball1 := runTarget (sourceIndex x)
noncomputable def partialReal (x : Ball1) : ℝ := (partialTarget x).1

@[simp] theorem partialTarget_source (n : ℕ) :
    partialTarget (source n) = runTarget n := by
  simp [partialTarget]

@[simp] theorem partialReal_source (n : ℕ) :
    partialReal (source n) = (runTarget n).1 := by
  simp [partialReal]

private theorem no_uniform_stage_bound (K : NNReal)
    (hbound : ∀ k : ℕ, stageCost k ≤ (K : ENNReal)) : False := by
  have hfwdPair := stage_forward_pair_le hbound
  have hinvPair := stage_inverse_pair_le hbound

  have hLip : LipschitzOnWith K partialReal (Set.range source) := by
    intro x hx y hy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    simpa only [partialReal_source, Subtype.edist_eq] using hfwdPair i j

  rcases hLip.extend_real with ⟨g, hgLip, hgEq⟩
  have hgCont : Continuous g := hgLip.continuous

  have hgSource (n : ℕ) : g (source n) = (runTarget n).1 := by
    have h := hgEq ⟨n, rfl⟩
    symm
    simpa using h

  have hgMaps (x : Ball1) : g x ∈ Set.Icc (-1 : ℝ) 1 := by
    let C : Set Ball1 := g ⁻¹' Set.Icc (-1 : ℝ) 1
    have hCclosed : IsClosed C := isClosed_Icc.preimage hgCont
    have hrange : Set.range source ⊆ C := by
      rintro _ ⟨n, rfl⟩
      change g (source n) ∈ Set.Icc (-1 : ℝ) 1
      rw [hgSource n]
      exact (runTarget n).2
    have hclosure : closure (Set.range source) ⊆ C :=
      closure_minimal hrange hCclosed
    exact hclosure (source_denseRange x)

  have hL : Continuous (fun p : Ball1 × Ball1 => edist p.1 p.2) :=
    continuous_fst.edist continuous_snd
  have hged : Continuous (fun p : Ball1 × Ball1 =>
      edist (g p.1) (g p.2)) :=
    (hgCont.comp continuous_fst).edist (hgCont.comp continuous_snd)
  have hR : Continuous (fun p : Ball1 × Ball1 =>
      (K : ENNReal) * edist (g p.1) (g p.2)) :=
    (ENNReal.continuous_const_mul (by simp : (K : ENNReal) ≠ ⊤)).comp hged
  let R : Set (Ball1 × Ball1) :=
    {p | edist p.1 p.2 ≤ (K : ENNReal) * edist (g p.1) (g p.2)}
  have hRclosed : IsClosed R := by
    exact isClosed_le hL hR
  have hdenseProd : Dense (Set.range source ×ˢ Set.range source) :=
    Dense.prod source_denseRange source_denseRange
  have hprodSub : Set.range source ×ˢ Set.range source ⊆ R := by
    rintro ⟨x, y⟩ ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    change edist (source i) (source j) ≤
      (K : ENNReal) * edist (g (source i)) (g (source j))
    rw [hgSource i, hgSource j]
    simpa only [Subtype.edist_eq] using hinvPair i j
  have hallInv (x y : Ball1) :
      edist x y ≤ (K : ENNReal) * edist (g x) (g y) := by
    have hcl : closure (Set.range source ×ˢ Set.range source) ⊆ R :=
      closure_minimal hprodSub hRclosed
    exact hcl (hdenseProd (x, y))

  have hgInj : Function.Injective g := by
    intro x y hxy
    have h := hallInv x y
    rw [hxy, edist_self, mul_zero] at h
    exact edist_eq_zero.mp (le_zero_iff.mp h)

  let G : ℝ → ℝ := fun x => g (Set.projIcc (-1 : ℝ) 1 (by norm_num) x)
  have hGCont : Continuous G := by
    exact hgCont.comp
      (continuous_projIcc : Continuous (Set.projIcc (-1 : ℝ) 1 (by norm_num)))
  have hG_on {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      G x = g ⟨x, hx⟩ := by
    simp [G, Set.projIcc_of_mem (by norm_num) hx]
  have hGInjOn : Set.InjOn G (Set.Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    have hsub : g ⟨x, hx⟩ = g ⟨y, hy⟩ := by
      calc
        g ⟨x, hx⟩ = G x := (hG_on hx).symm
        _ = G y := hxy
        _ = g ⟨y, hy⟩ := hG_on hy
    have heq := hgInj hsub
    exact congrArg Subtype.val heq

  have hG0 : G 0 = 1 := by
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    rw [hG_on h0]
    have hs0 : (⟨(0 : ℝ), h0⟩ : Ball1) = source 0 := by
      calc
        (⟨(0 : ℝ), h0⟩ : Ball1) = ballZero := by
          apply Subtype.ext
          rfl
        _ = source 0 := source_zero.symm
    rw [hs0, hgSource 0]
    norm_num [runTarget, ballOne]
  have hG1 : G 1 = 0 := by
    have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    rw [hG_on h1]
    have hs1 : (⟨(1 : ℝ), h1⟩ : Ball1) = source 1 := by
      calc
        (⟨(1 : ℝ), h1⟩ : Ball1) = ballOne := by
          apply Subtype.ext
          rfl
        _ = source 1 := source_one.symm
    rw [hs1, hgSource 1]
    norm_num [runTarget, ballZero]

  rcases hGCont.continuousOn.strictMonoOn_of_injOn_Icc'
      (by norm_num : (-1 : ℝ) ≤ 1) hGInjOn with hmono | hanti
  · have h01 := hmono (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) (by norm_num : (0 : ℝ) < 1)
    rw [hG0, hG1] at h01
    linarith
  · have hm10 := hanti (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
        (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) (by norm_num : (-1 : ℝ) < 0)
    rw [hG0] at hm10
    have hmapm1 : G (-1) ∈ Set.Icc (-1 : ℝ) 1 := by
      have hm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
      rw [hG_on hm1]
      exact hgMaps ⟨-1, hm1⟩
    linarith [hmapm1.2]

/-! ## 6. Final closed-ball theorem -/

/-- The actual greedy run has unbounded finite bi-Lipschitz objective.  This is
a negative answer to Ulam's Problem 165 under the historical closed-ball reading,
already for the one-dimensional closed unit ball. -/
theorem historical_closed_ball_problem165_negative :
    ∀ K : NNReal, ∃ k : ℕ, (K : ENNReal) < stageCost k := by
  intro K
  by_contra h
  have hbound : ∀ k : ℕ, stageCost k ≤ (K : ENNReal) := by
    intro k
    exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
  exact no_uniform_stage_bound K hbound

/-- Packaged statement recording the source-side requirements and the greedy run. -/
structure HistoricalClosedBallCounterexample where
  sourceSeq : ℕ → Ball1
  targetSeq : ℕ → Ball1
  source_rational : ∀ n, IsRationalPoint (sourceSeq n)
  source_injective : Function.Injective sourceSeq
  source_dense : DenseRange sourceSeq
  target_injective : Function.Injective targetSeq
  initial_zero_to_one : targetSeq 0 = ballOne
  initial_one_to_zero : targetSeq 1 = ballZero
  greedy : ∀ k : ℕ, IsGreedyChoice (states k) (targetSeq (k + 2))
  unbounded : ∀ K : NNReal, ∃ k : ℕ, (K : ENNReal) < stageCost k

noncomputable def historicalClosedBallCounterexample : HistoricalClosedBallCounterexample where
  sourceSeq := source
  targetSeq := runTarget
  source_rational := source_rational
  source_injective := source_injective
  source_dense := source_denseRange
  target_injective := runTarget_injective
  initial_zero_to_one := rfl
  initial_one_to_zero := rfl
  greedy := runTarget_greedy
  unbounded := historical_closed_ball_problem165_negative

theorem exists_historical_closed_ball_counterexample :
    Nonempty HistoricalClosedBallCounterexample :=
  ⟨historicalClosedBallCounterexample⟩

#print axioms historical_closed_ball_problem165_negative
#print axioms exists_historical_closed_ball_counterexample

end

end Ulam165HistoricalBall

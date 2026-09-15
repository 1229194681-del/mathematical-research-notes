import Mathlib

/-!
# Scottish Book Problem 174 — complete source candidate

This file gives a self-contained formal companion proof of the negative answer
 to Scottish Book Problem 174.

The mathematical note originally used the classical flat-smooth-function
example.  For formal verification we use an elementary, but stronger in the
relevant direction, Fréchet-space counterexample.  The space is the countable
product

    E = ℕ → (ℝ × ℝ)

with its product topology.  On the n-th two-dimensional block we let `U` be
`(n+1)` times the quarter-turn `(x,y) ↦ (-y,x)`.

For every real scalar `lam`, the operator `I - lam U` is a topological linear
isomorphism: its inverse is computed independently on each block by the matrix

    (I - c J)⁻¹ = (I + c J)/(1+c²),   c = lam(n+1),   J² = -I.

On the other hand, for every nonzero `lam` one can choose a block with
`|lam|(n+1) ≥ 1`.  A vector supported in that block has Neumann terms whose
squared Euclidean energy equals `((lam(n+1))²)^k`, so the terms do not tend to
zero.  Hence the Neumann series is not strongly summable.

This construction avoids all auxiliary spectral theory and proves the precise
existential assertion asked in Problem 174 over real B₀/Fréchet spaces.

The file is deliberately written without unproved declarations or proof-hole
commands.  It is a source-complete candidate intended for one subsequent pass
of local Lean/mathlib compilation and API adjustment.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace ScottishBook174

/-! ## 1. The Fréchet phase space -/

/-- One two-dimensional real block. -/
abbrev Block := ℝ × ℝ

/-- The countable product used as the ambient Fréchet space. -/
abbrev PhaseSpace := ℕ → Block

/-- The phase space is locally convex. -/
theorem phaseSpace_locallyConvex : LocallyConvexSpace ℝ PhaseSpace := by
  infer_instance

/-- The countable product is completely metrizable. -/
theorem phaseSpace_completelyMetrizable :
    TopologicalSpace.IsCompletelyMetrizableSpace PhaseSpace := by
  infer_instance

/-- The phase space is a topological additive group. -/
theorem phaseSpace_topologicalAddGroup : IsTopologicalAddGroup PhaseSpace := by
  infer_instance

/-- Scalar multiplication is continuous on the phase space. -/
theorem phaseSpace_continuousSMul : ContinuousSMul ℝ PhaseSpace := by
  infer_instance

/-! ## 2. The block rotation and the global operator -/

/-- The quarter-turn `J(x,y)=(-y,x)`. -/
def quarterTurn (v : Block) : Block := (-v.2, v.1)

@[simp]
theorem quarterTurn_fst (v : Block) : (quarterTurn v).1 = -v.2 := rfl

@[simp]
theorem quarterTurn_snd (v : Block) : (quarterTurn v).2 = v.1 := rfl

/-- Applying the quarter-turn twice gives minus the original vector. -/
theorem quarterTurn_sq (v : Block) : quarterTurn (quarterTurn v) = -v := by
  rcases v with ⟨x, y⟩
  simp [quarterTurn]

/-- The positive weight on the n-th block. -/
def weight (n : ℕ) : ℝ := (n : ℝ) + 1

@[simp]
theorem weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  positivity

@[simp]
theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := le_of_lt (weight_pos n)

/-- The global operator: on block `n`, multiply the quarter-turn by `n+1`. -/
def U (x : PhaseSpace) : PhaseSpace :=
  fun n => weight n • quarterTurn (x n)

/-- `U` is additive. -/
theorem U_add (x y : PhaseSpace) : U (x + y) = U x + U y := by
  funext n
  apply Prod.ext
  · simp [U, quarterTurn]
    ring
  · simp [U, quarterTurn]
    ring

/-- `U` is homogeneous over `ℝ`. -/
theorem U_smul (c : ℝ) (x : PhaseSpace) : U (c • x) = c • U x := by
  funext n
  apply Prod.ext
  · simp [U, quarterTurn]
    ring
  · simp [U, quarterTurn]
    ring

/-- `U` is continuous for the product topology. -/
theorem continuous_U : Continuous U := by
  apply continuous_pi
  intro n
  change Continuous (fun x : PhaseSpace =>
    (weight n * (-(x n).2), weight n * (x n).1))
  fun_prop

/-- `U` bundled as a continuous linear endomorphism. -/
def UCLM : PhaseSpace →L[ℝ] PhaseSpace where
  toLinearMap :=
    { toFun := U
      map_add' := U_add
      map_smul' := U_smul }
  cont := continuous_U

@[simp]
theorem UCLM_apply (x : PhaseSpace) : UCLM x = U x := rfl

/-! ## 3. Explicit inverse of `I - lamU` -/

/-- The operator `I - lamU` as an unbundled function. -/
def A (lam : ℝ) (x : PhaseSpace) : PhaseSpace := x - lam • U x

/-- The inverse of `I-cJ` on one block. -/
def invBlock (c : ℝ) (v : Block) : Block :=
  ((v.1 - c * v.2) / (1 + c^2),
   (c * v.1 + v.2) / (1 + c^2))

/-- The explicit coordinatewise inverse of `I - lamU`. -/
def R (lam : ℝ) (y : PhaseSpace) : PhaseSpace :=
  fun n => invBlock (lam * weight n) (y n)

/-- The denominator in the block inverse never vanishes. -/
theorem invBlock_denom_ne_zero (c : ℝ) : 1 + c^2 ≠ 0 := by
  positivity

/-- The block inverse is a left inverse to `I-cJ`. -/
theorem block_left_inverse (c : ℝ) (v : Block) :
    let w := invBlock c v
    w - c • quarterTurn w = v := by
  dsimp [invBlock, quarterTurn]
  have h : 1 + c^2 ≠ 0 := invBlock_denom_ne_zero c
  apply Prod.ext
  · dsimp
    field_simp [h]
    ring
  · dsimp
    field_simp [h]
    ring

/-- The block inverse is a right inverse to `I-cJ`. -/
theorem block_right_inverse (c : ℝ) (v : Block) :
    invBlock c (v - c • quarterTurn v) = v := by
  rcases v with ⟨x, y⟩
  dsimp [invBlock, quarterTurn]
  have h : 1 + c^2 ≠ 0 := invBlock_denom_ne_zero c
  apply Prod.ext
  · dsimp
    field_simp [h]
    ring
  · dsimp
    field_simp [h]
    ring

/-- `R lam` is a left inverse of `A lam`. -/
theorem A_R (lam : ℝ) (y : PhaseSpace) : A lam (R lam y) = y := by
  funext n
  simpa [A, R, U, smul_smul, mul_assoc] using
    block_left_inverse (lam * weight n) (y n)

/-- `R lam` is a right inverse of `A lam`. -/
theorem R_A (lam : ℝ) (x : PhaseSpace) : R lam (A lam x) = x := by
  funext n
  simpa [A, R, U, smul_smul, mul_assoc] using
    block_right_inverse (lam * weight n) (x n)

/-- `A lam` is additive. -/
theorem A_add (lam : ℝ) (x y : PhaseSpace) : A lam (x + y) = A lam x + A lam y := by
  simp [A, U_add]
  module

/-- `A lam` is homogeneous. -/
theorem A_smul (lam c : ℝ) (x : PhaseSpace) : A lam (c • x) = c • A lam x := by
  simp [A, U_smul, smul_smul]
  module

/-- `A lam` is continuous. -/
theorem continuous_A (lam : ℝ) : Continuous (A lam) := by
  apply continuous_pi
  intro n
  have h : Continuous (fun x : PhaseSpace =>
      ((x n).1 + (lam * weight n) * (x n).2,
       (x n).2 - (lam * weight n) * (x n).1)) := by
    fun_prop
  simpa [A, U, quarterTurn, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using h

/-- `R lam` is additive. -/
theorem R_add (lam : ℝ) (x y : PhaseSpace) : R lam (x + y) = R lam x + R lam y := by
  funext n
  apply Prod.ext
  · simp [R, invBlock]
    ring
  · simp [R, invBlock]
    ring

/-- `R lam` is homogeneous. -/
theorem R_smul (lam c : ℝ) (x : PhaseSpace) : R lam (c • x) = c • R lam x := by
  funext n
  apply Prod.ext
  · simp [R, invBlock]
    ring
  · simp [R, invBlock]
    ring

/-- `R lam` is continuous in the product topology. -/
theorem continuous_R (lam : ℝ) : Continuous (R lam) := by
  apply continuous_pi
  intro n
  unfold R invBlock
  fun_prop

/-- `R lam` bundled as a continuous linear map. -/
def RCLM (lam : ℝ) : PhaseSpace →L[ℝ] PhaseSpace where
  toLinearMap :=
    { toFun := R lam
      map_add' := R_add lam
      map_smul' := R_smul lam }
  cont := continuous_R lam

/-- `I - lamU` is bijective for every real scalar `lam`. -/
theorem A_bijective (lam : ℝ) : Function.Bijective (A lam) := by
  constructor
  · intro x y hxy
    have h := congrArg (R lam) hxy
    simpa [R_A] using h
  · intro y
    exact ⟨R lam y, A_R lam y⟩

/-- In fact, the inverse is continuous and linear. -/
theorem A_is_topological_linear_isomorphism (lam : ℝ) :
    Function.LeftInverse (R lam) (A lam) ∧
    Function.RightInverse (R lam) (A lam) ∧
    Continuous (A lam) ∧ Continuous (R lam) := by
  refine ⟨?_, ?_, continuous_A lam, continuous_R lam⟩
  · intro x
    exact R_A lam x
  · intro y
    exact A_R lam y

/-! ## 4. The Neumann terms -/

/-- Strong summability of the genuine Neumann series for `lamU`. -/
def StronglySummableAt (lam : ℝ) : Prop :=
  ∀ x : PhaseSpace, Summable (fun k : ℕ => (((lam • UCLM) ^ k) x))

/-- Strong summability forces the Neumann terms to tend to zero. -/
theorem neumann_terms_tendsto_zero
    {lam : ℝ} (h : StronglySummableAt lam) (x : PhaseSpace) :
    Tendsto (fun k : ℕ => (((lam • UCLM) ^ k) x)) atTop (𝓝 0) :=
  (h x).tendsto_atTop_zero

/-! ## 5. Energy on one block -/

/-- Squared Euclidean norm on a block. -/
def energyBlock (v : Block) : ℝ := v.1^2 + v.2^2

@[simp]
theorem energyBlock_zero : energyBlock (0 : Block) = 0 := by
  simp [energyBlock]

/-- A quarter-turn preserves squared Euclidean energy. -/
theorem energyBlock_quarterTurn (v : Block) :
    energyBlock (quarterTurn v) = energyBlock v := by
  rcases v with ⟨x, y⟩
  simp [energyBlock, quarterTurn]
  ring

/-- Scalar multiplication scales squared energy quadratically. -/
theorem energyBlock_smul (c : ℝ) (v : Block) :
    energyBlock (c • v) = c^2 * energyBlock v := by
  rcases v with ⟨x, y⟩
  simp [energyBlock]
  ring

/-- Energy of `U x` on block `n`. -/
theorem energy_U_at (x : PhaseSpace) (n : ℕ) :
    energyBlock ((U x) n) = (weight n)^2 * energyBlock (x n) := by
  simp [U, energyBlock_smul, energyBlock_quarterTurn]

/-- Energy of `(lamU)x` on block `n`. -/
theorem energy_scaled_U_at (lam : ℝ) (x : PhaseSpace) (n : ℕ) :
    energyBlock (((lam • UCLM) x) n) =
      (lam * weight n)^2 * energyBlock (x n) := by
  rw [show ((lam • UCLM) x) = lam • U x by rfl]
  rw [Pi.smul_apply, energyBlock_smul, energy_U_at]
  ring

/-- Exact energy formula for the k-th Neumann term. -/
theorem energy_neumann_pow_at (lam : ℝ) (x : PhaseSpace) (n k : ℕ) :
    energyBlock ((((lam • UCLM) ^ k) x) n) =
      (((lam * weight n)^2)^k) * energyBlock (x n) := by
  induction k generalizing x with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ]
      simp only [ContinuousLinearMap.mul_apply]
      rw [ih]
      rw [energy_scaled_U_at]
      ring

/-! ## 6. A vector concentrated in one block -/

/-- The vector `(1,0)` supported only on block `n`. -/
def basisAt (n : ℕ) : PhaseSpace :=
  fun m => if m = n then (1, 0) else (0, 0)

@[simp]
theorem basisAt_self (n : ℕ) : basisAt n n = (1, 0) := by
  simp [basisAt]

@[simp]
theorem energy_basisAt_self (n : ℕ) :
    energyBlock (basisAt n n) = 1 := by
  simp [energyBlock]

/-- Exact energy of the Neumann term on its supporting block. -/
theorem energy_neumann_basisAt (lam : ℝ) (n k : ℕ) :
    energyBlock ((((lam • UCLM) ^ k) (basisAt n)) n) =
      ((lam * weight n)^2)^k := by
  simpa [energyBlock] using energy_neumann_pow_at lam (basisAt n) n k

/-- Evaluation of squared energy at one coordinate is continuous. -/
theorem continuous_energyAt (n : ℕ) :
    Continuous (fun x : PhaseSpace => energyBlock (x n)) := by
  unfold energyBlock
  fun_prop

/-! ## 7. Elementary real-sequence obstruction -/

/-- A geometric progression with ratio of modulus at least one does not tend to zero. -/
theorem pow_not_tendsto_zero {r : ℝ} (hr : 1 ≤ |r|) :
    ¬ Tendsto (fun k : ℕ => r^k) atTop (𝓝 0) := by
  intro h
  have hlt : |r| < 1 := tendsto_pow_atTop_nhds_zero_iff.mp h
  exact (not_lt_of_ge hr) hlt

/-- For every nonzero scalar there is a block on which `|lam|(n+1) ≥ 1`. -/
theorem exists_large_block (lam : ℝ) (hlam : lam ≠ 0) :
    ∃ n : ℕ, 1 ≤ |lam * weight n| := by
  have habs : 0 < |lam| := abs_pos.mpr hlam
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / |lam|)
  refine ⟨n, ?_⟩
  have hn' : (1 / |lam| : ℝ) < weight n := by
    dsimp [weight]
    exact lt_trans hn (by norm_num)
  have hmul : 1 < |lam| * weight n := by
    have := (div_lt_iff₀ habs).mp hn'
    simpa [mul_comm] using this
  have hnonneg : 0 ≤ weight n := weight_nonneg n
  rw [abs_mul, abs_of_nonneg hnonneg]
  exact le_of_lt hmul

/-- Squaring preserves the lower bound `≥1` for a nonnegative modulus. -/
theorem one_le_abs_sq {r : ℝ} (hr : 1 ≤ |r|) : 1 ≤ |r^2| := by
  rw [abs_pow]
  have hnonneg : 0 ≤ |r| := abs_nonneg r
  nlinarith

/-! ## 8. Failure of the Neumann expansion -/

/--
For every nonzero `lam`, the Neumann series for `lamU` is not strongly summable.
-/
theorem neumann_not_stronglySummable (lam : ℝ) (hlam : lam ≠ 0) :
    ¬ StronglySummableAt lam := by
  obtain ⟨n, hn⟩ := exists_large_block lam hlam
  intro hs
  have hterm :
      Tendsto
        (fun k : ℕ => (((lam • UCLM) ^ k) (basisAt n)))
        atTop (𝓝 0) :=
    neumann_terms_tendsto_zero hs (basisAt n)
  have henergy :
      Tendsto
        ((fun x : PhaseSpace => energyBlock (x n)) ∘
          (fun k : ℕ => (((lam • UCLM) ^ k) (basisAt n))))
        atTop (𝓝 0) := by
    have hc := continuous_energyAt n
    have hmapped := hc.continuousAt.tendsto.comp hterm
    simpa [energyBlock] using hmapped
  have hpow :
      Tendsto (fun k : ℕ => ((lam * weight n)^2)^k) atTop (𝓝 0) := by
    have heq :
        (fun k : ℕ => ((lam * weight n)^2)^k) =
          ((fun x : PhaseSpace => energyBlock (x n)) ∘
            (fun k : ℕ => (((lam • UCLM) ^ k) (basisAt n)))) := by
      funext k
      change ((lam * weight n)^2)^k =
        energyBlock ((((lam • UCLM) ^ k) (basisAt n)) n)
      exact (energy_neumann_basisAt lam n k).symm
    rw [heq]
    exact henergy
  exact (pow_not_tendsto_zero (one_le_abs_sq hn)) hpow

/-! ## 9. Finite Neumann identity -/

/-- The first `N` Neumann terms as a continuous linear endomorphism. -/
def neumannPartial (lam : ℝ) (N : ℕ) : PhaseSpace →L[ℝ] PhaseSpace :=
  ∑ k ∈ Finset.range N, (lam • UCLM)^k

/-- Standard finite geometric identity on the left. -/
theorem one_sub_mul_neumannPartial (lam : ℝ) (N : ℕ) :
    (1 - lam • UCLM) * neumannPartial lam N = 1 - (lam • UCLM)^N := by
  simpa [neumannPartial] using (mul_neg_geom_sum (lam • UCLM) N)

/-- Standard finite geometric identity on the right. -/
theorem neumannPartial_mul_one_sub (lam : ℝ) (N : ℕ) :
    neumannPartial lam N * (1 - lam • UCLM) = 1 - (lam • UCLM)^N := by
  simpa [neumannPartial] using (geom_sum_mul_neg (lam • UCLM) N)

/-! ## 10. Final counterexample theorem -/

/--
The concrete formal counterexample answering Scottish Book Problem 174.

* `PhaseSpace` is a real Fréchet space;
* `U` is continuous and real-linear;
* `I - lamU` is bijective for every real scalar `lam` and has a continuous linear
  inverse `R lam`;
* for every nonzero `lam`, the Neumann series fails even strong summability.
-/
theorem scottish_book_174_negative :
    LocallyConvexSpace ℝ PhaseSpace ∧
    TopologicalSpace.IsCompletelyMetrizableSpace PhaseSpace ∧
    Continuous U ∧
    (∀ x y : PhaseSpace, U (x + y) = U x + U y) ∧
    (∀ (c : ℝ) (x : PhaseSpace), U (c • x) = c • U x) ∧
    (∀ lam : ℝ, Function.Bijective (A lam)) ∧
    (∀ lam : ℝ, Continuous (R lam)) ∧
    (∀ lam : ℝ, lam ≠ 0 → ¬ StronglySummableAt lam) := by
  refine ⟨phaseSpace_locallyConvex,
    phaseSpace_completelyMetrizable,
    continuous_U,
    U_add,
    U_smul,
    A_bijective,
    continuous_R,
    ?_⟩
  intro lam hlam
  exact neumann_not_stronglySummable lam hlam

/-- A compact theorem emphasizing the exact logical negation of Problem 174. -/
theorem resolvent_everywhere_but_no_neumann_radius :
    (∀ lam : ℝ, Function.Bijective (A lam)) ∧
    (∀ lam : ℝ, lam ≠ 0 → ¬ StronglySummableAt lam) := by
  exact ⟨A_bijective, neumann_not_stronglySummable⟩

#print axioms scottish_book_174_negative
#print axioms resolvent_everywhere_but_no_neumann_radius

end ScottishBook174

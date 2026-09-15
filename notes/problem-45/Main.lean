-- SCOTTISH45 FORMALIZATION VERSION 10
import Mathlib

open scoped BigOperators
open Filter Topology

namespace Scottish45

/-!
# Scottish Book Problem 45: a four-factor counterexample

This file formalizes an algebraically simplified version of the counterexample.
The analytic `ℓ²(D;ℝ)` Heisenberg group from the paper is replaced by a purely
`𝔽₂` Heisenberg group built from finitely supported functions.  This is enough
for the original Problem 45: we construct a complete metrizable noncommutative
topological group `G` and four algebraic group homomorphisms `U₁,...,U₄ : G →* G`
such that their pointwise product is Baire class one but is not continuous.

No continuity is assumed for the four homomorphisms themselves.
-/

abbrev F2 := ZMod 2
abbrev V0 := ℕ → F2
abbrev V := Multiplicative V0
abbrev M := V →₀ F2

noncomputable section

local instance : DecidableEq V := Classical.decEq V

/-! ## Elementary characteristic-two facts -/

lemma f2_add_self (a : F2) : a + a = 0 := CharTwo.add_self_eq_zero a

@[simp] lemma v_mul_self (x : V) : x * x = 1 := by
  apply Multiplicative.ext
  funext i
  simpa using CharTwo.add_self_eq_zero ((Multiplicative.toAdd x) i)

/-! ## The regular shift on finitely supported functions -/

noncomputable def shift (x : V) (f : M) : M :=
  Finsupp.equivMapDomain (Equiv.mulLeft x) f

@[simp] lemma shift_apply (x : V) (f : M) (y : V) :
    shift x f y = f (x⁻¹ * y) := by
  simp [shift, Finsupp.equivMapDomain_apply]

@[simp] lemma shift_zero (x : V) : shift x (0 : M) = 0 := by
  ext y
  simp [shift_apply]

lemma shift_add (x : V) (f g : M) : shift x (f + g) = shift x f + shift x g := by
  ext y
  simp [shift_apply]

@[simp] lemma shift_one (f : M) : shift (1 : V) f = f := by
  ext y
  simp [shift_apply]

lemma shift_mul (x y : V) (f : M) : shift (x * y) f = shift x (shift y f) := by
  ext z
  simp [shift_apply, mul_assoc]

lemma shift_inv_left (x : V) (f : M) : shift x⁻¹ (shift x f) = f := by
  ext y
  simp [shift_apply]

lemma shift_inv_right (x : V) (f : M) : shift x (shift x⁻¹ f) = f := by
  ext y
  simp [shift_apply]

/-! ## A finite-support dot product -/

def dot (f g : M) : F2 :=
  f.sum fun i a => a * g i

@[simp] lemma dot_zero_left (g : M) : dot 0 g = 0 := by
  simp [dot]

@[simp] lemma dot_single_left (i : V) (a : F2) (g : M) :
    dot (Finsupp.single i a) g = a * g i := by
  simp [dot]

lemma dot_add_left (f g h : M) : dot (f + g) h = dot f h + dot g h := by
  unfold dot
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    ring

lemma dot_add_right (f g h : M) : dot f (g + h) = dot f g + dot f h := by
  unfold dot
  have hfun :
      (fun i a => a * (g + h) i) =
        (fun i a => a * g i + a * h i) := by
    funext i a
    simp [mul_add]
  rw [hfun]
  exact Finsupp.sum_add (f := f)
    (h₁ := fun i a => a * g i)
    (h₂ := fun i a => a * h i)

@[simp] lemma dot_zero_right (f : M) : dot f 0 = 0 := by
  unfold dot
  simp

lemma dot_shift (x : V) (f g : M) : dot (shift x f) (shift x g) = dot f g := by
  unfold dot shift
  rw [Finsupp.sum_equivMapDomain]
  simp [Finsupp.equivMapDomain_apply]

/-! ## The `𝔽₂` Heisenberg group -/

structure Heis where
  a : M
  b : M
  c : F2
  deriving DecidableEq

@[ext] theorem Heis.ext {p q : Heis}
    (ha : p.a = q.a) (hb : p.b = q.b) (hc : p.c = q.c) : p = q := by
  cases p with
  | mk pa pb pc =>
    cases q with
    | mk qa qb qc =>
      cases ha
      cases hb
      cases hc
      rfl

instance : One Heis := ⟨⟨0, 0, 0⟩⟩

noncomputable instance : Mul Heis := ⟨fun p q =>
  ⟨p.a + q.a, p.b + q.b, p.c + q.c + dot p.a q.b⟩⟩

noncomputable instance : Inv Heis := ⟨fun p =>
  ⟨p.a, p.b, p.c + dot p.a p.b⟩⟩

@[simp] lemma one_a : (1 : Heis).a = 0 := rfl
@[simp] lemma one_b : (1 : Heis).b = 0 := rfl
@[simp] lemma one_c : (1 : Heis).c = 0 := rfl
@[simp] lemma mul_a (p q : Heis) : (p * q).a = p.a + q.a := rfl
@[simp] lemma mul_b (p q : Heis) : (p * q).b = p.b + q.b := rfl
@[simp] lemma mul_c (p q : Heis) : (p * q).c = p.c + q.c + dot p.a q.b := rfl
@[simp] lemma inv_a (p : Heis) : p⁻¹.a = p.a := rfl
@[simp] lemma inv_b (p : Heis) : p⁻¹.b = p.b := rfl
@[simp] lemma inv_c (p : Heis) : p⁻¹.c = p.c + dot p.a p.b := rfl

lemma heis_mul_assoc (p q r : Heis) : p * q * r = p * (q * r) := by
  apply Heis.ext
  · simp only [mul_a]
    exact add_assoc _ _ _
  · simp only [mul_b]
    exact add_assoc _ _ _
  · simp only [mul_c, mul_a, mul_b]
    rw [dot_add_left, dot_add_right]
    abel

lemma heis_one_mul (p : Heis) : 1 * p = p := by
  apply Heis.ext <;> simp [dot]

lemma heis_inv_mul (p : Heis) : p⁻¹ * p = 1 := by
  apply Heis.ext
  · simpa using ZModModule.add_self p.a
  · simpa using ZModModule.add_self p.b
  · simp only [mul_c, inv_c, inv_a]
    calc
      (p.c + dot p.a p.b) + p.c + dot p.a p.b
          = (p.c + p.c) + (dot p.a p.b + dot p.a p.b) := by abel
      _ = 0 := by simp [CharTwo.add_self_eq_zero]

noncomputable instance : Group Heis :=
  Group.ofLeftAxioms heis_mul_assoc heis_one_mul heis_inv_mul

/-! ## The shift action by automorphisms -/

noncomputable def alphaHom (x : V) : Heis →* Heis where
  toFun p := ⟨shift x p.a, shift x p.b, p.c⟩
  map_one' := by
    apply Heis.ext <;> simp
  map_mul' p q := by
    apply Heis.ext
    · simp [shift_add]
    · simp [shift_add]
    · simp [dot_shift]

lemma alphaHom_bijective (x : V) : Function.Bijective (alphaHom x) := by
  constructor
  · intro p q hpq
    apply Heis.ext
    · have ha : shift x p.a = shift x q.a := by
        exact congrArg Heis.a hpq
      have ha' := congrArg (shift x⁻¹) ha
      simpa only [shift_inv_left] using ha'
    · have hb : shift x p.b = shift x q.b := by
        exact congrArg Heis.b hpq
      have hb' := congrArg (shift x⁻¹) hb
      simpa only [shift_inv_left] using hb'
    · have hc : (alphaHom x p).c = (alphaHom x q).c :=
        congrArg (fun r : Heis => r.c) hpq
      simpa [alphaHom] using hc
  · intro p
    refine ⟨alphaHom x⁻¹ p, ?_⟩
    apply Heis.ext <;> simp [alphaHom, shift_inv_right]

noncomputable def alphaAut (x : V) : MulAut Heis :=
  MulEquiv.ofBijective (alphaHom x) (alphaHom_bijective x)

@[simp] lemma alphaAut_apply (x : V) (p : Heis) :
    alphaAut x p = ⟨shift x p.a, shift x p.b, p.c⟩ := by
  simp [alphaAut, alphaHom]

noncomputable def alpha : V →* MulAut Heis where
  toFun := alphaAut
  map_one' := by
    apply DFunLike.ext _ _
    intro p
    apply Heis.ext
    · simp [alphaAut_apply]
    · simp [alphaAut_apply]
    · simp [alphaAut_apply]
  map_mul' x y := by
    apply DFunLike.ext _ _
    intro p
    apply Heis.ext
    · simp [alphaAut_apply, shift_mul]
    · simp [alphaAut_apply, shift_mul]
    · simp [alphaAut_apply]

@[simp] lemma alpha_apply (x : V) (p : Heis) : alpha x p = alphaAut x p := rfl

abbrev K0 := Heis ⋊[alpha] V

/-! We deliberately put the discrete topology on the semidirect-product factor. -/

instance : TopologicalSpace K0 := ⊥
instance : DiscreteTopology K0 := ⟨rfl⟩
instance : IsTopologicalGroup K0 := by infer_instance
instance : TopologicalSpace.IsCompletelyMetrizableSpace K0 := by infer_instance

/-! The Cantor Boolean group is completely metrizable. -/

instance : TopologicalSpace.IsCompletelyMetrizableSpace V := by
  change TopologicalSpace.IsCompletelyMetrizableSpace V0
  infer_instance

instance : IsTopologicalGroup V := by infer_instance

abbrev G := V × K0

instance : TopologicalSpace.IsCompletelyMetrizableSpace G := by infer_instance
instance : IsTopologicalGroup G := by infer_instance

/-! ## Distinguished finite-support vectors -/

noncomputable def xi : M := Finsupp.single (1 : V) 1

@[simp] lemma dot_xi_xi : dot xi xi = 1 := by
  simp [xi, dot_single_left]

@[simp] lemma shift_xi (x : V) : shift x xi = Finsupp.single x 1 := by
  simp [shift, xi]

noncomputable def bvec (x : V) : M := xi + shift x xi

lemma shift_bvec (x : V) : shift x (bvec x) = bvec x := by
  rw [bvec, shift_add, ← shift_mul, v_mul_self, shift_one]
  exact add_comm _ _

noncomputable def eps (x : V) : F2 := 1 + dot xi (shift x xi)

lemma dot_bvec_self (x : V) : dot (bvec x) (bvec x) = 0 := by
  rw [bvec, dot_add_left, dot_add_right, dot_add_right, shift_xi]
  by_cases hx : x = 1
  · subst x
    simp [xi, dot_single_left, CharTwo.add_self_eq_zero]
  · simp [xi, dot_single_left, hx, CharTwo.add_self_eq_zero]

@[simp] lemma bvec_add_self (x : V) : bvec x + bvec x = 0 := by
  simpa using ZModModule.add_self (bvec x)

lemma eps_eq (x : V) : eps x = if x = 1 then 0 else 1 := by
  by_cases hx : x = 1
  · subst x
    rw [if_pos rfl]
    change (1 : F2) + dot xi (shift 1 xi) = 0
    rw [shift_one, dot_xi_xi]
    exact f2_add_self 1
  · simp [eps, xi, dot_single_left, hx]

noncomputable def w1 : Heis := ⟨xi, 0, 0⟩
noncomputable def w3 : Heis := ⟨0, xi, 0⟩
noncomputable def w4 : Heis := ⟨xi, xi, 0⟩

noncomputable def cob (x : V) (w : Heis) : Heis := w⁻¹ * alphaAut x w

lemma cob_w1 (x : V) : cob x w1 = ⟨bvec x, 0, 0⟩ := by
  apply Heis.ext <;>
    simp [cob, w1, bvec, alphaAut_apply, dot]

lemma cob_w3 (x : V) : cob x w3 = ⟨0, bvec x, 0⟩ := by
  apply Heis.ext <;>
    simp [cob, w3, bvec, alphaAut_apply, dot]

lemma cob_w4 (x : V) : cob x w4 = ⟨bvec x, bvec x, eps x⟩ := by
  apply Heis.ext
  · simp [cob, w4, bvec, alphaAut_apply]
  · simp [cob, w4, bvec, alphaAut_apply]
  · simp [cob, w4, eps, alphaAut_apply, dot_xi_xi]

/-! ## Four homomorphisms into the semidirect product -/

noncomputable def R : V →* K0 := SemidirectProduct.inr

noncomputable def A (w : Heis) : V →* K0 :=
  (MulAut.conj ((SemidirectProduct.inl w)⁻¹)).toMonoidHom.comp R

lemma A_apply (w : Heis) (x : V) :
    A w x = (SemidirectProduct.inl w)⁻¹ * R x * SemidirectProduct.inl w := by
  simp [A, R]

lemma A_pair (w : Heis) (x : V) :
    A w x = ⟨cob x w, x⟩ := by
  rw [A_apply]
  apply SemidirectProduct.ext
  · simp [cob, R, alpha_apply]
  · simp [R]

noncomputable def A1 : V →* K0 := A w1
noncomputable def A2 : V →* K0 := R
noncomputable def A3 : V →* K0 := A w3
noncomputable def A4 : V →* K0 := A w4

noncomputable def zN : Heis := ⟨0, 0, 1⟩
noncomputable def zK : K0 := SemidirectProduct.inl zN

lemma zN_ne_one : zN ≠ 1 := by
  intro h
  have hc := congrArg Heis.c h
  simp [zN] at hc

lemma zK_ne_one : zK ≠ 1 := by
  intro h
  apply zN_ne_one
  change SemidirectProduct.inl zN = SemidirectProduct.inl (1 : Heis) at h
  exact SemidirectProduct.inl_injective h

lemma alpha_cob_w4 (x : V) : alphaAut x (cob x w4) = (cob x w4)⁻¹ := by
  rw [cob_w4]
  apply Heis.ext
  · simp [alphaAut_apply, shift_bvec]
  · simp [alphaAut_apply, shift_bvec]
  · simp [alphaAut_apply, dot_bvec_self]

lemma A1_mul_A2 (x : V) :
    A1 x * A2 x = SemidirectProduct.inl (cob x w1) := by
  change A w1 x * R x = SemidirectProduct.inl (cob x w1)
  rw [A_pair w1 x]
  change (⟨cob x w1, x⟩ : K0) * SemidirectProduct.inr x = _
  rw [SemidirectProduct.mul_def]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.left_inr, SemidirectProduct.left_inl, map_one, mul_one]
  · simp [v_mul_self]

lemma A3_mul_A4 (x : V) :
    A3 x * A4 x =
      SemidirectProduct.inl (cob x w3 * (cob x w4)⁻¹) := by
  change A w3 x * A w4 x =
    SemidirectProduct.inl (cob x w3 * (cob x w4)⁻¹)
  rw [A_pair w3 x, A_pair w4 x]
  rw [SemidirectProduct.mul_def]
  rw [alpha_apply, alpha_cob_w4]
  apply SemidirectProduct.ext
  · rfl
  · simp [v_mul_self]

lemma cob_product (x : V) :
    cob x w1 * (cob x w3 * (cob x w4)⁻¹) =
      if x = 1 then 1 else zN := by
  rw [cob_w1, cob_w3, cob_w4]
  by_cases hx : x = 1
  · subst x
    apply Heis.ext
    · simp
    · simp
    · rw [if_pos rfl]
      change
        (⟨bvec (1 : V), 0, 0⟩ *
          (⟨0, bvec (1 : V), 0⟩ *
            (⟨bvec (1 : V), bvec (1 : V), eps (1 : V)⟩ : Heis)⁻¹)).c = 0
      simp only [mul_c, inv_c, mul_b, inv_b]
      rw [bvec_add_self]
      rw [dot_zero_left, dot_zero_right]
      simp only [zero_add, add_zero]
      rw [dot_bvec_self]
      simp only [add_zero]
      rw [eps_eq, if_pos rfl]
  · apply Heis.ext
    · simp [hx, zN]
    · simp [hx, zN]
    · rw [if_neg hx]
      change
        (⟨bvec x, 0, 0⟩ *
          (⟨0, bvec x, 0⟩ *
            (⟨bvec x, bvec x, eps x⟩ : Heis)⁻¹)).c = 1
      simp only [mul_c, inv_c, mul_b, inv_b]
      rw [bvec_add_self]
      rw [dot_zero_left, dot_zero_right]
      simp only [zero_add, add_zero]
      rw [dot_bvec_self]
      simp only [add_zero]
      rw [eps_eq, if_neg hx]

lemma four_product_K0 (x : V) :
    A1 x * A2 x * A3 x * A4 x = if x = 1 then 1 else zK := by
  calc
    A1 x * A2 x * A3 x * A4 x
        = (A1 x * A2 x) * (A3 x * A4 x) := by simp [mul_assoc]
    _ = SemidirectProduct.inl (cob x w1) *
          SemidirectProduct.inl (cob x w3 * (cob x w4)⁻¹) := by
          rw [A1_mul_A2, A3_mul_A4]
    _ = SemidirectProduct.inl
          (cob x w1 * (cob x w3 * (cob x w4)⁻¹)) := by
          symm
          exact SemidirectProduct.inl.map_mul _ _
    _ = if x = 1 then 1 else zK := by
          rw [cob_product]
          by_cases hx : x = 1 <;> simp [hx, zK]

/-! ## Lift the four homomorphisms to endomorphisms of one and the same group -/

noncomputable def liftA (B : V →* K0) : G →* G where
  toFun g := (1, B g.1)
  map_one' := by simp
  map_mul' g h := by simp

noncomputable def U1 : G →* G := liftA A1
noncomputable def U2 : G →* G := liftA A2
noncomputable def U3 : G →* G := liftA A3
noncomputable def U4 : G →* G := liftA A4

noncomputable def F (g : G) : G := U1 g * U2 g * U3 g * U4 g

noncomputable def zG : G := (1, zK)

lemma zG_ne_one : zG ≠ 1 := by
  intro h
  have h2 := congrArg Prod.snd h
  exact zK_ne_one (by simpa [zG] using h2)

lemma F_formula (g : G) : F g = if g.1 = 1 then 1 else zG := by
  rcases g with ⟨v, k⟩
  by_cases hv : v = 1
  · simp [F, U1, U2, U3, U4, liftA, hv]
  · simp [F, U1, U2, U3, U4, liftA, four_product_K0, zG, hv]

/-! ## A direct Baire-class-one witness -/

/-- Our exact notion of Baire class one: pointwise limit of continuous maps. -/
def IsBaireOne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∃ fseq : ℕ → X → Y,
    (∀ n, Continuous (fseq n)) ∧
    ∀ x, Tendsto (fun n => fseq n x) atTop (𝓝 (f x))

def coordPrefix (n : ℕ) (v : V) : Fin n → F2 :=
  fun i => (Multiplicative.toAdd v) i.1

lemma continuous_coordPrefix (n : ℕ) : Continuous (coordPrefix n) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i.1).comp continuous_toAdd

noncomputable def flagCode (n : ℕ) (u : Fin n → F2) : F2 :=
  if ∃ i : Fin n, u i = 1 then 1 else 0

lemma continuous_flagCode (n : ℕ) : Continuous (flagCode n) := by
  exact continuous_of_discreteTopology

noncomputable def flag (n : ℕ) (v : V) : F2 :=
  flagCode n (coordPrefix n v)

lemma continuous_flag (n : ℕ) : Continuous (flag n) := by
  exact (continuous_flagCode n).comp (continuous_coordPrefix n)

lemma flag_one (n : ℕ) : flag n (1 : V) = 0 := by
  simp [flag, flagCode, coordPrefix]

lemma f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma exists_coord_one_of_ne_one {v : V} (hv : v ≠ 1) :
    ∃ i : ℕ, (Multiplicative.toAdd v) i = 1 := by
  by_contra h
  push Not at h
  apply hv
  apply Multiplicative.ext
  funext i
  rcases f2_eq_zero_or_one ((Multiplicative.toAdd v) i) with hz | ho
  · simp [hz]
  · exact (h i ho).elim

lemma flag_eventually_one {v : V} (hv : v ≠ 1) :
    ∀ᶠ n in atTop, flag n v = 1 := by
  obtain ⟨i, hi⟩ := exists_coord_one_of_ne_one hv
  filter_upwards [eventually_ge_atTop (i + 1)] with n hn
  have hin : i < n := by omega
  have hex : ∃ j : Fin n, coordPrefix n v j = 1 := by
    refine ⟨⟨i, hin⟩, ?_⟩
    simpa [coordPrefix] using hi
  simp [flag, flagCode, hex]

noncomputable def codeZ (a : F2) : G := if a = 0 then 1 else zG

lemma continuous_codeZ : Continuous codeZ := by
  exact continuous_of_discreteTopology

noncomputable def Fapprox (n : ℕ) (g : G) : G := codeZ (flag n g.1)

lemma continuous_Fapprox (n : ℕ) : Continuous (Fapprox n) := by
  apply continuous_codeZ.comp
  exact (continuous_flag n).comp continuous_fst

lemma Fapprox_tendsto (g : G) :
    Tendsto (fun n => Fapprox n g) atTop (𝓝 (F g)) := by
  by_cases hg : g.1 = 1
  · have heq : ∀ᶠ n in atTop, (fun _ : ℕ => F g) n = Fapprox n g := by
      filter_upwards [] with n
      simp [Fapprox, codeZ, flag_one, F_formula, hg]
    exact tendsto_const_nhds.congr' heq
  · have hflag := flag_eventually_one hg
    have heq : ∀ᶠ n in atTop, (fun _ : ℕ => F g) n = Fapprox n g := by
      filter_upwards [hflag] with n hn
      simp [Fapprox, codeZ, hn, F_formula, hg]
    exact tendsto_const_nhds.congr' heq

lemma F_baireOne : IsBaireOne F := by
  refine ⟨Fapprox, continuous_Fapprox, ?_⟩
  exact Fapprox_tendsto

/-! ## Discontinuity -/

def spikeAdd (n : ℕ) : V0 :=
  fun i => if i = n then 1 else 0

noncomputable def spike (n : ℕ) : V :=
  Multiplicative.ofAdd (spikeAdd n)

lemma spike_ne_one (n : ℕ) : spike n ≠ 1 := by
  intro h
  have hh := congrArg (fun v : V => (Multiplicative.toAdd v) n) h
  simp [spike, spikeAdd] at hh

lemma spikeAdd_tendsto_zero :
    Tendsto spikeAdd atTop (𝓝 (0 : V0)) := by
  rw [tendsto_pi_nhds]
  intro i
  have heq : ∀ᶠ n in atTop,
      (fun _ : ℕ => (0 : F2)) n = spikeAdd n i := by
    filter_upwards [eventually_gt_atTop i] with n hn
    have hne : i ≠ n := by omega
    simp [spikeAdd, hne]
  exact tendsto_const_nhds.congr' heq

lemma spike_tendsto_one : Tendsto spike atTop (𝓝 (1 : V)) := by
  change Tendsto spikeAdd atTop (𝓝 (0 : V0))
  exact spikeAdd_tendsto_zero

noncomputable def badSeq (n : ℕ) : G := (spike n, 1)

lemma badSeq_tendsto : Tendsto badSeq atTop (𝓝 (1 : G)) := by
  change Tendsto (fun n => (spike n, (1 : K0))) atTop
    (𝓝 ((1 : V), (1 : K0)))
  exact spike_tendsto_one.prodMk_nhds tendsto_const_nhds

lemma F_badSeq (n : ℕ) : F (badSeq n) = zG := by
  simp [badSeq, F_formula, spike_ne_one]

lemma F_one : F (1 : G) = 1 := by
  simp [F_formula]

lemma F_not_continuous : ¬ Continuous F := by
  intro hF
  have hlim : Tendsto (fun n => F (badSeq n)) atTop (𝓝 (F (1 : G))) :=
    hF.continuousAt.tendsto.comp badSeq_tendsto
  have hzlim : Tendsto (fun _ : ℕ => zG) atTop (𝓝 zG) := tendsto_const_nhds
  have hlim' : Tendsto (fun _ : ℕ => zG) atTop (𝓝 (1 : G)) := by
    simpa [F_badSeq, F_one] using hlim
  have : zG = 1 := tendsto_nhds_unique hzlim hlim'
  exact zG_ne_one this

/-! ## Noncommutativity of the ambient group -/

noncomputable def hp : Heis := ⟨xi, 0, 0⟩
noncomputable def hq : Heis := ⟨0, xi, 0⟩

lemma hp_hq_ne : hp * hq ≠ hq * hp := by
  intro h
  have hc := congrArg Heis.c h
  simp [hp, hq, dot_xi_xi] at hc

noncomputable def gp : G := (1, SemidirectProduct.inl hp)
noncomputable def gq : G := (1, SemidirectProduct.inl hq)

lemma G_noncommutative : gp * gq ≠ gq * gp := by
  intro h
  have hk := congrArg (fun g : G => (g.2 : K0).left) h
  exact hp_hq_ne (by simpa [gp, gq] using hk)

/-! ## Final packaged result -/

/--
A fully explicit negative solution of Scottish Book Problem 45 for four factors.
The four `Uᵢ` are algebraic endomorphisms of the same complete metrizable
noncommutative topological group `G`; their pointwise product is Baire class one
but not continuous.
-/
theorem scottishBook45_negative :
    TopologicalSpace.IsCompletelyMetrizableSpace G ∧
    IsTopologicalGroup G ∧
    (∃ a b : G, a * b ≠ b * a) ∧
    (∃ U₁ U₂ U₃ U₄ : G →* G,
      let P : G → G := fun g => U₁ g * U₂ g * U₃ g * U₄ g
      IsBaireOne P ∧ ¬ Continuous P) := by
  refine ⟨inferInstance, inferInstance, ⟨gp, gq, G_noncommutative⟩, ?_⟩
  refine ⟨U1, U2, U3, U4, ?_⟩
  change IsBaireOne F ∧ ¬ Continuous F
  exact ⟨F_baireOne, F_not_continuous⟩


end

end Scottish45

#print axioms Scottish45.scottishBook45_negative

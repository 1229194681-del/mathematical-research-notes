import Mathlib

noncomputable section

/-!
# Nikliborc Problem 129 — standalone strict source

This single file contains the concrete core, the explicitly isolated published
interfaces, the shared near-ball construction, and the final formal deduction
for Problem 129.  It does not import any project-local Nikliborc module.
-/

/-!
# Nikliborc Problems 128 and 129: concrete core

This file contains only concrete definitions and elementary deductions used by the
formalizations.  It contains no article-specific existence assumptions, no `sorry`,
and no custom `axiom` declarations.
-/

namespace Nikliborc

open Set MeasureTheory Filter
open scoped BigOperators Topology
open InnerProductSpace

/-- Euclidean three-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Coordinate unit vector. -/
def basisVec (i : Fin 3) : R3 := EuclideanSpace.single i 1

def e1 : R3 := basisVec 0

/-- The elementary polynomial `|x|^2`, written in coordinates. -/
def normSq (x : R3) : ℝ := (x 0)^2 + (x 1)^2 + (x 2)^2

/-- The explicit harmonic cubic used in both papers. -/
def H (x : R3) : ℝ := (x 0)^3 - 3 * (x 0) * (x 1)^2

/-- Ball potential polynomial. -/
def q (a : ℝ) (x : R3) : ℝ := a^2 / 2 - normSq x / 6

/-- Perturbed polynomial. -/
def p (a t : ℝ) (x : R3) : ℝ := q a x + t * H x

def Ball (a : ℝ) : Set R3 := Metric.ball 0 a

def ClosedBall (a : ℝ) : Set R3 := Metric.closedBall 0 a

def Sphere (a : ℝ) : Set R3 := Metric.sphere 0 a

lemma mem_Ball_iff {a : ℝ} {x : R3} : x ∈ Ball a ↔ ‖x‖ < a := by
  simp [Ball, Metric.mem_ball, dist_zero_right]

lemma mem_ClosedBall_iff {a : ℝ} {x : R3} : x ∈ ClosedBall a ↔ ‖x‖ ≤ a := by
  simp [ClosedBall, Metric.mem_closedBall, dist_zero_right]

lemma mem_Sphere_iff {a : ℝ} {x : R3} : x ∈ Sphere a ↔ ‖x‖ = a := by
  simp [Sphere]

lemma H_zero : H (0 : R3) = 0 := by simp [H]

lemma H_e1 : H e1 = 1 := by
  simp [H, e1, basisVec]

lemma norm_e1 : ‖e1‖ = 1 := by
  simp [e1, basisVec]

lemma H_ne_zero : H ≠ (0 : R3 → ℝ) := by
  intro h
  have := congrFun h e1
  simp [H_e1] at this

lemma H_homogeneous_three (s : ℝ) (x : R3) : H (s • x) = s^3 * H x := by
  simp [H, smul_eq_mul]
  ring

/-! ## Algebraic Laplacian certificate -/

/-- A concrete polynomial of total degree at most three in three variables.
This small coefficient model avoids any dependence on the current
`MvPolynomial.pderiv` simplifier API. -/
structure Cubic3 where
  c : ℝ
  l0 : ℝ
  l1 : ℝ
  l2 : ℝ
  q00 : ℝ
  q01 : ℝ
  q02 : ℝ
  q11 : ℝ
  q12 : ℝ
  q22 : ℝ
  c000 : ℝ
  c001 : ℝ
  c002 : ℝ
  c011 : ℝ
  c012 : ℝ
  c022 : ℝ
  c111 : ℝ
  c112 : ℝ
  c122 : ℝ
  c222 : ℝ

namespace Cubic3

def eval (P : Cubic3) (x : R3) : ℝ :=
  P.c + P.l0*x 0 + P.l1*x 1 + P.l2*x 2
    + P.q00*(x 0)^2 + P.q01*(x 0)*(x 1) + P.q02*(x 0)*(x 2)
    + P.q11*(x 1)^2 + P.q12*(x 1)*(x 2) + P.q22*(x 2)^2
    + P.c000*(x 0)^3 + P.c001*(x 0)^2*(x 1) + P.c002*(x 0)^2*(x 2)
    + P.c011*(x 0)*(x 1)^2 + P.c012*(x 0)*(x 1)*(x 2) + P.c022*(x 0)*(x 2)^2
    + P.c111*(x 1)^3 + P.c112*(x 1)^2*(x 2) + P.c122*(x 1)*(x 2)^2
    + P.c222*(x 2)^3

/-- The algebraic Laplacian of a cubic is affine-linear. -/
def lapEval (P : Cubic3) (x : R3) : ℝ :=
  2*(P.q00 + P.q11 + P.q22)
    + (6*P.c000 + 2*P.c011 + 2*P.c022) * x 0
    + (2*P.c001 + 6*P.c111 + 2*P.c122) * x 1
    + (2*P.c002 + 2*P.c112 + 6*P.c222) * x 2

end Cubic3

def Hcubic : Cubic3 := {
  c := 0, l0 := 0, l1 := 0, l2 := 0,
  q00 := 0, q01 := 0, q02 := 0, q11 := 0, q12 := 0, q22 := 0,
  c000 := 1, c001 := 0, c002 := 0, c011 := -3, c012 := 0,
  c022 := 0, c111 := 0, c112 := 0, c122 := 0, c222 := 0 }

def qcubic (a : ℝ) : Cubic3 := {
  c := a^2/2, l0 := 0, l1 := 0, l2 := 0,
  q00 := -(1/6), q01 := 0, q02 := 0, q11 := -(1/6), q12 := 0, q22 := -(1/6),
  c000 := 0, c001 := 0, c002 := 0, c011 := 0, c012 := 0,
  c022 := 0, c111 := 0, c112 := 0, c122 := 0, c222 := 0 }

def pcubic (a t : ℝ) : Cubic3 := {
  c := a^2/2, l0 := 0, l1 := 0, l2 := 0,
  q00 := -(1/6), q01 := 0, q02 := 0, q11 := -(1/6), q12 := 0, q22 := -(1/6),
  c000 := t, c001 := 0, c002 := 0, c011 := -3*t, c012 := 0,
  c022 := 0, c111 := 0, c112 := 0, c122 := 0, c222 := 0 }

lemma H_eq_Hcubic_eval (x : R3) : Hcubic.eval x = H x := by
  simp [Cubic3.eval, Hcubic, H]
  ring

lemma q_eq_qcubic_eval (a : ℝ) (x : R3) : (qcubic a).eval x = q a x := by
  simp [Cubic3.eval, qcubic, q, normSq]
  ring

lemma p_eq_pcubic_eval (a t : ℝ) (x : R3) : (pcubic a t).eval x = p a t x := by
  simp [Cubic3.eval, pcubic, p, q, H, normSq]
  ring

lemma lapEval_Hcubic (x : R3) : Hcubic.lapEval x = 0 := by
  norm_num [Cubic3.lapEval, Hcubic]

lemma lapEval_qcubic (a : ℝ) (x : R3) : (qcubic a).lapEval x = -1 := by
  norm_num [Cubic3.lapEval, qcubic]

lemma lapEval_pcubic (a t : ℝ) (x : R3) : (pcubic a t).lapEval x = -1 := by
  simp [Cubic3.lapEval, pcubic]
  ring

/-! ## Finite-difference obstruction to a quadratic potential -/

def thirdDiffAt (f : R3 → ℝ) (x v : R3) : ℝ :=
  f (x + (3 : ℝ) • v) - 3 * f (x + (2 : ℝ) • v) + 3 * f (x + v) - f x

structure Quadratic3 where
  c : ℝ
  l0 : ℝ
  l1 : ℝ
  l2 : ℝ
  q00 : ℝ
  q01 : ℝ
  q02 : ℝ
  q11 : ℝ
  q12 : ℝ
  q22 : ℝ

namespace Quadratic3

def eval (Q : Quadratic3) (x : R3) : ℝ :=
  Q.c + Q.l0*x 0 + Q.l1*x 1 + Q.l2*x 2
    + Q.q00*(x 0)^2 + Q.q01*(x 0)*(x 1) + Q.q02*(x 0)*(x 2)
    + Q.q11*(x 1)^2 + Q.q12*(x 1)*(x 2) + Q.q22*(x 2)^2

lemma thirdDiffAt_eval (Q : Quadratic3) (x : R3) (s : ℝ) :
    thirdDiffAt Q.eval x (s • e1) = 0 := by
  simp [thirdDiffAt, eval, e1, basisVec, smul_eq_mul]
  ring

end Quadratic3

lemma thirdDiffAt_p_e1 (a t : ℝ) (x : R3) (s : ℝ) :
    thirdDiffAt (p a t) x (s • e1) = 6 * t * s^3 := by
  simp [thirdDiffAt, p, q, H, normSq, e1, basisVec, smul_eq_mul]
  ring

lemma thirdDiffAt_p_e1_ne_zero {a t s : ℝ} (x : R3)
    (ht : t ≠ 0) (hs : s ≠ 0) :
    thirdDiffAt (p a t) x (s • e1) ≠ 0 := by
  rw [thirdDiffAt_p_e1]
  exact mul_ne_zero (mul_ne_zero (by norm_num) ht) (pow_ne_zero 3 hs)

/-! ## Actual Newtonian potential -/

noncomputable def newtonKernel (x y : R3) : ℝ :=
  1 / (4 * Real.pi * ‖x - y‖)

noncomputable def newtonPotential (K : Set R3) (x : R3) : ℝ :=
  ∫ y in K, newtonKernel x y

/-- Characteristic density of a body. -/
noncomputable def bodyDensity (K : Set R3) : R3 → ℝ :=
  K.indicator (fun _ => 1)

/-- Concrete weak meaning of `-Laplacian.laplacianu = g`: integration against every compactly
supported smooth test function. -/
def IsTestFunction (φ : R3 → ℝ) : Prop := ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ

noncomputable def HasDistributionalNegLaplacian (u g : R3 → ℝ) : Prop :=
  ∀ φ : R3 → ℝ, IsTestFunction φ →
    (∫ x, u x * (-(Laplacian.laplacian φ) x)) = ∫ x, g x * φ x

/-- A concrete elementary formulation of convergence to a constant at infinity. -/
def TendsToConstantAtInfinity (f : R3 → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |f x - c| < ε

/-- A concrete global `C^{1,1}` predicate, stronger than the local version and
sufficient for every use below. -/
def IsC11 (u : R3 → ℝ) : Prop :=
  ContDiff ℝ 1 u ∧ ∃ C : NNReal, LipschitzWith C (fderiv ℝ u)

/-- The concrete obstacle-solution properties needed by the argument. -/
structure IsObstacleSolution (h : R3 → ℝ) (c : ℝ) (u : R3 → ℝ) : Prop where
  dominates : ∀ x, h x ≤ u x
  c11 : IsC11 u
  atInfinity : TendsToConstantAtInfinity u c
  /-- The nonnegative obstacle reaction measure/density exists.  It is bundled
  existentially so that `IsObstacleSolution` remains a proposition. -/
  source_spec : ∃ source : R3 → ℝ,
    (∀ᵐ x ∂volume, 0 ≤ source x) ∧
    HasDistributionalNegLaplacian u source ∧
    (∀ᵐ x ∂volume, h x < u x → source x = 0)
  harmonic_noncontact : ∀ x, h x < u x → (Laplacian.laplacian u) x = 0


def contactSet (u h : R3 → ℝ) : Set R3 := {x | u x = h x}

def noncontactSet (u h : R3 → ℝ) : Set R3 := {x | h x < u x}

lemma contact_compl_eq_noncontact {h u : R3 → ℝ}
    (hdom : ∀ x, h x ≤ u x) :
    (contactSet u h)ᶜ = noncontactSet u h := by
  ext x
  constructor
  · intro hx
    have hne : u x ≠ h x := by
      simpa [contactSet] using hx
    show h x < u x
    exact lt_of_le_of_ne (hdom x) (Ne.symm hne)
  · intro hx
    show x ∈ (contactSet u h)ᶜ
    simp only [Set.mem_compl_iff, contactSet, Set.mem_ofPred_eq]
    exact ne_of_gt hx

/-! ## Geometry used in the published stability theorem -/

structure SmoothCutoff (r R : ℝ) where
  χ : R3 → ℝ
  smooth : ContDiff ℝ ⊤ χ
  nonneg : ∀ x, 0 ≤ χ x
  le_one : ∀ x, χ x ≤ 1
  one_on : ∀ x, ‖x‖ ≤ r → χ x = 1
  zero_outside : ∀ x, R ≤ ‖x‖ → χ x = 0
  /-- Standard compact-support strengthening: at every point on or outside the
  support radius the cutoff is identically zero on a neighbourhood. -/
  zero_nhds_outside : ∀ x, R ≤ ‖x‖ → χ =ᶠ[nhds x] (0 : R3 → ℝ)


def obstacle (a t M : ℝ) (χ : R3 → ℝ) (x : R3) : ℝ :=
  χ x * p a t x - (1 - χ x) * M

lemma obstacle_sub_zero (a t M : ℝ) (χ : R3 → ℝ) (x : R3) :
    obstacle a t M χ x - obstacle a 0 M χ x = t * χ x * H x := by
  simp [obstacle, p]
  ring

lemma obstacle_eq_p_of_one {a t M : ℝ} {χ : R3 → ℝ} {x : R3}
    (hχ : χ x = 1) : obstacle a t M χ x = p a t x := by
  simp [obstacle, hχ]

lemma obstacle_eq_negM_of_zero {a t M : ℝ} {χ : R3 → ℝ} {x : R3}
    (hχ : χ x = 0) : obstacle a t M χ x = -M := by
  simp [obstacle, hχ]

/-- Concrete two-sided tangent ball condition. -/
def TwoSidedBallCondition (C : Set R3) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ x ∈ frontier C, ∃ ci co : R3,
    dist ci x = ρ ∧ Metric.ball ci ρ ⊆ interior C ∧
    dist co x = ρ ∧ Metric.ball co ρ ⊆ Cᶜ

/-- A family is smooth in the parameter and space variables. -/
def SmoothFamily (h : ℝ → R3 → ℝ) : Prop :=
  ContDiff ℝ ⊤ (fun z : ℝ × R3 => h z.1 z.2)

/-- Separation of an obstacle from its limiting constant at infinity. -/
def AsymptoticallyBelow (h : R3 → ℝ) (c : ℝ) : Prop :=
  ∃ η > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → h x ≤ c - η

/-- The exact class of whole-space obstacles used in the two notes: smooth and
identically equal to a negative constant outside a fixed ball, with asymptotic
constant zero. -/
structure CompactNegativeObstacle (h : R3 → ℝ) (c M R : ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ h
  M_pos : 0 < M
  R_pos : 0 < R
  outside : ∀ x, R ≤ ‖x‖ → h x = -M
  c_zero : c = 0

/-- A strong smooth-data specialization of the hypotheses (1.4)--(1.11)
of Serfaty--Serra, Theorem 1.1.  The regularity assumptions here are stronger
(`C^∞`) than the finite Hölder regularity required in the paper, so this is a
safe specialization rather than an extra article-specific hypothesis.

Crucially, the theorem is supplied an *actual family of obstacle solutions*
`u t`; it does not manufacture the perturbed solutions as part of the stability
conclusion. -/
structure SSAssumptions
    (h : ℝ → R3 → ℝ) (c : ℝ → ℝ) (u : ℝ → R3 → ℝ)
    (C0 U : Set R3) (ρ R : ℝ) : Prop where
  rho_pos : 0 < ρ
  R_pos : 0 < R
  family_smooth : SmoothFamily h
  c_smooth : ContDiff ℝ 2 c
  /-- `u^t` satisfies the whole-space obstacle problem (1.3), on the parameter
  interval used in Theorem 1.1. -/
  solutions : ∀ t, |t| ≤ 1 → IsObstacleSolution (h t) (c t) (u t)
  /-- (1.4), in the stronger uniform form used by the concrete family. -/
  asymptotic_separation : ∀ t, AsymptoticallyBelow (h t) (c t)
  /-- (1.7): `Laplacian.laplacian(h^t-h^0)` vanishes outside the fixed ball. -/
  laplacian_perturbation_zero_outside : ∀ t x, R ≤ ‖x‖ →
    (Laplacian.laplacian (fun y => h t y - h 0 y)) x = 0
  /-- (1.8), in dimension three. -/
  perturbation_vanishes_at_infinity : ∀ t,
    TendsToConstantAtInfinity (fun x => h t x - h 0 x) 0
  initial_contact : contactSet (u 0) (h 0) = C0
  U_open : IsOpen U
  /-- The explicit requirement `U ⊂ B_R` from (1.10). -/
  U_subset_ball : U ⊆ Ball R
  C0_subset_U : C0 ⊆ U
  /-- The obstacle is active on the initial contact set. -/
  active_initial : ∀ x ∈ C0, (Laplacian.laplacian (h 0)) x < 0
  negative_laplacian : ∀ x ∈ closure U, (Laplacian.laplacian (h 0)) x ≤ -ρ
  positive_gap : ∀ x ∉ U, ρ ≤ u 0 x - h 0 x
  tangent_balls : TwoSidedBallCondition C0 ρ

/-- A genuine `C^1` ambient diffeomorphism, represented by a homeomorphism plus
`C^1` regularity in both directions. -/
structure C1Diffeomorph where
  homeomorph : R3 ≃ₜ R3
  contDiff_to : ContDiff ℝ 1 homeomorph
  contDiff_inv : ContDiff ℝ 1 homeomorph.symm

namespace C1Diffeomorph
instance : CoeFun C1Diffeomorph (fun _ => R3 → R3) := ⟨fun Ψ => Ψ.homeomorph⟩

def inv (Ψ : C1Diffeomorph) : R3 → R3 := Ψ.homeomorph.symm

lemma left_inv (Ψ : C1Diffeomorph) : Function.LeftInverse Ψ.inv Ψ :=
  Ψ.homeomorph.left_inv

lemma right_inv (Ψ : C1Diffeomorph) : Function.RightInverse Ψ.inv Ψ :=
  Ψ.homeomorph.right_inv
end C1Diffeomorph

/-- Raw output of the published Serfaty--Serra theorem, specialized to dimension
three and to smooth data.  This mirrors Theorem 1.1: a differentiable family of
diffeomorphisms maps the initial noncontact set/free boundary to the perturbed
ones, and its velocity is uniformly bounded.  The published theorem also fixes
`Uᶜ`, but the formal deduction below does not need that extra conclusion.

There is deliberately no `ε`-closeness field here; that corollary is proved
below from the velocity bound. -/
structure SSRawOutput
    (h : ℝ → R3 → ℝ) (c : ℝ → ℝ) (u : ℝ → R3 → ℝ)
    (C0 U : Set R3) where
  t0 : ℝ
  t0_pos : 0 < t0
  Ψ : ℝ → C1Diffeomorph
  /-- Normalization supplied by the explicit family constructed in the proof of
  Theorem 1.1 (Step 5): at `t=0` the map is the identity. -/
  psi_zero : ∀ x, Ψ 0 x = x
  noncontact_image : ∀ t, |t| < t0 →
    Ψ t '' noncontactSet (u 0) (h 0) = noncontactSet (u t) (h t)
  free_boundary_image : ∀ t, |t| < t0 →
    Ψ t '' frontier (noncontactSet (u 0) (h 0)) =
      frontier (noncontactSet (u t) (h t))
  velocity : ℝ → R3 → R3
  hasDeriv : ∀ t, |t| < t0 → ∀ x,
    HasDerivAt (fun s => Ψ s x) (velocity t x) t
  velocity_bound : ∃ C > 0, ∀ t, |t| < t0 → ∀ x, ‖velocity t x‖ ≤ C

/-! ## Actual ellipsoids and the historical geometric conclusions -/

def affineImage (c : R3) (L : R3 ≃L[ℝ] R3) (S : Set R3) : Set R3 :=
  (fun x => c + L x) '' S

/-- A (solid) ellipsoid is an invertible affine image of the closed unit ball. -/
def IsSolidEllipsoid (E : Set R3) : Prop :=
  ∃ c : R3, ∃ L : R3 ≃L[ℝ] R3, E = affineImage c L (ClosedBall 1)


def homothety (c : R3) (scale : ℝ) (x : R3) : R3 := c + scale • (x - c)

/-- The conclusion proposed in Problem 129, encoded for the two bounded bodies. -/
def HomotheticEllipsoidPair (K1 K2 : Set R3) : Prop :=
  IsSolidEllipsoid (closure K1) ∧ IsSolidEllipsoid (closure K2) ∧
    ∃ c : R3, ∃ scale > 0,
      frontier (closure K2) = homothety c scale '' frontier (closure K1)

/-- Stronger-than-needed sphere topology: an ambient homeomorphism sends the
standard sphere to the boundary. -/
def SphereBoundaryLike (K : Set R3) (a : ℝ) : Prop :=
  ∃ Ψ : R3 ≃ₜ R3, Ψ '' Sphere a = frontier K

/-- `C^1` version supplied by the Serfaty--Serra ambient diffeomorphism. -/
def C1SphereBoundaryLike (K : Set R3) (a : ℝ) : Prop :=
  ∃ Ψ : C1Diffeomorph, Ψ '' Sphere a = frontier K

/-- Concrete unicoherence of a subset, expressed on the subtype topology. -/
def UnicoherentSet (K : Set R3) : Prop :=
  ∀ A B : Set K,
    IsClosed A → IsClosed B → IsConnected A → IsConnected B →
    A ∪ B = Set.univ → IsConnected (A ∩ B)

/-- Elementary boundedness predicate, avoiding any hidden body abstraction. -/
def NormBounded (K : Set R3) : Prop := ∃ R : ℝ, ∀ x ∈ K, ‖x‖ ≤ R

lemma normBounded_mono {A B : Set R3} (hA : NormBounded A) (hAB : B ⊆ A) :
    NormBounded B := by
  rcases hA with ⟨R, hR⟩
  exact ⟨R, fun x hx => hR x (hAB hx)⟩

lemma open_contains_e1_progression {K : Set R3}
    (hopen : IsOpen K) (hne : K.Nonempty) :
    ∃ x : R3, ∃ s : ℝ, 0 < s ∧
      x ∈ K ∧ x + s • e1 ∈ K ∧
      x + ((2 : ℝ) * s) • e1 ∈ K ∧
      x + ((3 : ℝ) * s) • e1 ∈ K := by
  rcases hne with ⟨x, hx⟩
  rcases Metric.isOpen_iff.1 hopen x hx with ⟨ε, hε, hball⟩
  let s : ℝ := ε / 4
  have hs : 0 < s := by dsimp [s]; linarith
  have hmem (n : ℝ) (hn0 : 0 ≤ n) (hn3 : n ≤ 3) :
      x + (n * s) • e1 ∈ K := by
    apply hball
    rw [Metric.mem_ball]
    rw [dist_eq_norm]
    have hnorm : ‖(n * s) • e1‖ = |n * s| := by
      rw [norm_smul, norm_e1, mul_one, Real.norm_eq_abs]
    rw [show x + (n * s) • e1 - x = (n * s) • e1 by abel, hnorm]
    rw [abs_of_nonneg (mul_nonneg hn0 (le_of_lt hs))]
    dsimp [s]
    nlinarith
  refine ⟨x, s, hs, hx, ?_, ?_, ?_⟩
  · simpa using hmem 1 (by norm_num) (by norm_num)
  · simpa using hmem 2 (by norm_num) (by norm_num)
  · simpa using hmem 3 (by norm_num) (by norm_num)

lemma image_compl_equiv {α β : Type*} (e : α ≃ β) (S : Set α) :
    e '' Sᶜ = (e '' S)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ hmem
    rcases hmem with ⟨z, hz, hzx⟩
    have : z = x := e.injective hzx
    exact hx (this ▸ hz)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro hS
    apply hy
    exact ⟨e.symm y, hS, e.apply_symm_apply y⟩

end Nikliborc


/-! --------------------------------------------------------------------------
    Next embedded module
-------------------------------------------------------------------------- -/

/-!
# Published / standard external inputs for Nikliborc 128 and 129

The user's formalization convention permits results already available in public,
citable literature to be represented as theorem interfaces.  Every field below is
*generic*: none asserts the near-ball construction, nesting, shell identity,
cancellation, nonellipsoidality, or either Scottish Book counterexample.

The interfaces correspond to:
* classical Newtonian potential of a ball;
* standard multivariable-calculus facts for polynomial Laplacians;
* standard whole-space obstacle complementarity / `C^{1,1}` theory;
* Serfaty--Serra, Analysis & PDE 11 (2018), Thm. 1.1;
* distributional Poisson / Newtonian representation uniqueness;
* the classical quadratic interior potential theorem for ellipsoids;
* standard smooth-cutoff, hypersurface-null, and homeomorphism facts.
-/

namespace Nikliborc

open Set MeasureTheory Filter
open scoped Topology

/-- The external mathematical library assumed by the two formalizations.
All article-specific deductions are outside this structure. -/
structure PublishedTheory where

  /- ### Standard polynomial/analytic calculus bridge -/
  /-- Generic calculus fact: for any concrete cubic coefficient vector, the
  analytic Laplacian equals its algebraically computed Laplacian. -/
  laplacian_eval_cubic :
    ∀ (P : Cubic3) (x : R3),
      Laplacian.laplacian P.eval x = P.lapEval x

  laplacian_congr_nhds :
    ∀ {f g : R3 → ℝ} {x : R3}, f =ᶠ[nhds x] g →
      Laplacian.laplacian f x = Laplacian.laplacian g x

  /- ### Smooth cutoffs -/
  smooth_cutoff : ∀ {r R : ℝ}, 0 < r → r < R → SmoothCutoff r R

  /- ### Classical Newtonian potential of a homogeneous ball -/
  ball_inside : ∀ {a : ℝ}, 0 < a → ∀ x, ‖x‖ ≤ a →
    newtonPotential (Ball a) x = q a x

  ball_gap : ∀ {a : ℝ}, 0 < a → ∀ x, a < ‖x‖ →
    newtonPotential (Ball a) x - q a x =
      ((‖x‖ - a)^2 * (‖x‖ + 2*a)) / (6 * ‖x‖)

  ball_positive : ∀ {a : ℝ}, 0 < a → ∀ x,
    0 < newtonPotential (Ball a) x

  ball_c11 : ∀ {a : ℝ}, 0 < a → IsC11 (newtonPotential (Ball a))

  ball_decay : ∀ {a : ℝ}, 0 < a →
    TendsToConstantAtInfinity (newtonPotential (Ball a)) 0

  ball_poisson : ∀ {a : ℝ}, 0 < a →
    HasDistributionalNegLaplacian
      (newtonPotential (Ball a)) (bodyDensity (Ball a))

  /- ### Generic whole-space obstacle theory -/
  /-- Standard complementarity characterization used only to verify the explicit
  unperturbed ball solution. -/
  obstacle_of_complementarity :
    ∀ {h u g : R3 → ℝ} {c : ℝ},
      IsC11 u →
      (∀ x, h x ≤ u x) →
      TendsToConstantAtInfinity u c →
      HasDistributionalNegLaplacian u g →
      (∀ᵐ x ∂volume, 0 ≤ g x) →
      (∀ᵐ x ∂volume, h x < u x → g x = 0) →
      IsObstacleSolution h c u

  /-- Standard existence for the precise compactly perturbed obstacle class used
  in the papers. -/
  obstacle_exists : ∀ {h : R3 → ℝ} {c M R : ℝ},
    CompactNegativeObstacle h c M R →
    ∃ u : R3 → ℝ, IsObstacleSolution h c u

  /-- Uniqueness of the whole-space obstacle solution with fixed obstacle and
  asymptotic constant. -/
  obstacle_unique : ∀ {h : R3 → ℝ} {c : ℝ} {u v : R3 → ℝ},
    IsObstacleSolution h c u → IsObstacleSolution h c v → u = v

  /- ### Serfaty--Serra Theorem 1.1, raw form -/
  ss_stability_raw :
    ∀ {h : ℝ → R3 → ℝ} {c : ℝ → ℝ} {u : ℝ → R3 → ℝ}
      {C0 U : Set R3} {ρ R : ℝ},
      SSAssumptions h c u C0 U ρ R →
      SSRawOutput h c u C0 U

  /- ### Standard weak/distributional Laplacian bridge -/
  bodyDensity_locallyIntegrable : ∀ {K : Set R3}, MeasurableSet K →
    LocallyIntegrable (bodyDensity K) volume

  c11_ae_laplacian_to_distribution :
    ∀ {u g : R3 → ℝ},
      IsC11 u → LocallyIntegrable g volume →
      (∀ᵐ x ∂volume, (Laplacian.laplacian u) x = - g x) →
      HasDistributionalNegLaplacian u g

  /- ### Newtonian representation / uniqueness and regularity -/
  newton_uniqueness :
    ∀ {K : Set R3} {u : R3 → ℝ},
      MeasurableSet K → NormBounded K →
      TendsToConstantAtInfinity u 0 →
      HasDistributionalNegLaplacian u (bodyDensity K) →
      u = newtonPotential K

  newton_continuous : ∀ {K : Set R3},
    MeasurableSet K → NormBounded K → Continuous (newtonPotential K)

  kernel_integrableOn : ∀ {K : Set R3},
    MeasurableSet K → NormBounded K → ∀ x : R3,
      IntegrableOn (newtonKernel x) K

  /- ### Standard geometry/topology of balls and diffeomorphic spheres -/
  closedBall_twoSided : ∀ {a ρ : ℝ}, 0 < ρ → ρ < a →
    TwoSidedBallCondition (ClosedBall a) ρ

  c1_sphere_image_null : ∀ (Ψ : C1Diffeomorph) {a : ℝ}, 0 < a →
    volume (Ψ '' Sphere a) = 0

  ae_not_mem_of_null : ∀ {S : Set R3}, volume S = 0 →
    ∀ᵐ x ∂volume, x ∉ S

  homeomorph_closure_ball : ∀ (Ψ : R3 ≃ₜ R3) {a : ℝ}, 0 < a →
    closure (Ψ '' Ball a) = Ψ '' ClosedBall a

  homeomorph_frontier_ball : ∀ (Ψ : R3 ≃ₜ R3) {a : ℝ}, 0 < a →
    frontier (Ψ '' Ball a) = Ψ '' Sphere a

  homeomorph_interior_closedBall : ∀ (Ψ : R3 ≃ₜ R3) {a : ℝ}, 0 < a →
    interior (Ψ '' ClosedBall a) = Ψ '' Ball a

  closedBall_unicoherent : ∀ {a : ℝ}, 0 < a → UnicoherentSet (ClosedBall a)

  unicoherent_homeomorph_image : ∀ (Ψ : R3 ≃ₜ R3) {K : Set R3},
    UnicoherentSet K → UnicoherentSet (Ψ '' K)

  /- ### Classical ellipsoid theorem -/
  ellipsoid_quadratic_potential : ∀ {E : Set R3},
    IsSolidEllipsoid E →
    ∃ Q : Quadratic3, ∀ x ∈ interior E,
      newtonPotential E x = Q.eval x

/-! ## Consequences of generic published calculus facts -/

lemma laplacian_H (pub : PublishedTheory) (x : R3) : Laplacian.laplacian H x = 0 := by
  have hfun : H = Hcubic.eval := by
    funext y
    exact (H_eq_Hcubic_eval y).symm
  rw [hfun, pub.laplacian_eval_cubic]
  exact lapEval_Hcubic x

lemma laplacian_q (pub : PublishedTheory) (a : ℝ) (x : R3) :
    Laplacian.laplacian (q a) x = -1 := by
  have hfun : q a = (qcubic a).eval := by
    funext y
    exact (q_eq_qcubic_eval a y).symm
  rw [hfun, pub.laplacian_eval_cubic]
  exact lapEval_qcubic a x

lemma laplacian_p (pub : PublishedTheory) (a t : ℝ) (x : R3) :
    Laplacian.laplacian (p a t) x = -1 := by
  have hfun : p a t = (pcubic a t).eval := by
    funext y
    exact (p_eq_pcubic_eval a t y).symm
  rw [hfun, pub.laplacian_eval_cubic]
  exact lapEval_pcubic a t x

/-- The algebraic computation really proves the article's concrete cubic is
harmonic; only the generic calculus bridge is external. -/
def IsHarmonic (f : R3 → ℝ) : Prop := ∀ x, Laplacian.laplacian f x = 0

lemma H_is_harmonic (pub : PublishedTheory) : IsHarmonic H := laplacian_H pub

end Nikliborc


/-! --------------------------------------------------------------------------
    Next embedded module
-------------------------------------------------------------------------- -/

/-!
# Shared near-ball construction

This file proves the article-specific smooth-obstacle construction used by both
Nikliborc 128 and 129.  The only nonlocal inputs are the generic public theorems
in `PublishedTheory`.
-/

namespace Nikliborc

open Set MeasureTheory Filter
open scoped Topology

lemma p_contDiff (a t : ℝ) : ContDiff ℝ ⊤ (p a t) := by
  change ContDiff ℝ ⊤ (fun x : R3 =>
    a^2/2 - ((x 0)^2 + (x 1)^2 + (x 2)^2)/6 +
      t * ((x 0)^3 - 3*(x 0)*(x 1)^2))
  fun_prop

lemma pFamily_contDiff (a : ℝ) :
    ContDiff ℝ ⊤ (fun z : ℝ × R3 => p a z.1 z.2) := by
  change ContDiff ℝ ⊤ (fun z : ℝ × R3 =>
    a^2/2 - ((z.2 0)^2 + (z.2 1)^2 + (z.2 2)^2)/6 +
      z.1 * ((z.2 0)^3 - 3*(z.2 0)*(z.2 1)^2))
  fun_prop

/-- The obstacle family used in the papers. -/
def obstacleFamily (a M : ℝ) {r R : ℝ} (cut : SmoothCutoff r R) :
    ℝ → R3 → ℝ := fun t => obstacle a t M cut.χ

lemma obstacleFamily_smooth {a M r R : ℝ} (cut : SmoothCutoff r R) :
    SmoothFamily (obstacleFamily a M cut) := by
  have hχ : ContDiff ℝ ⊤ (fun z : ℝ × R3 => cut.χ z.2) :=
    cut.smooth.comp contDiff_snd
  have hp : ContDiff ℝ ⊤ (fun z : ℝ × R3 => p a z.1 z.2) := pFamily_contDiff a
  have hOneMinus : ContDiff ℝ ⊤ (fun z : ℝ × R3 => 1 - cut.χ z.2) :=
    contDiff_const.sub hχ
  have hMconst : ContDiff ℝ ⊤ (fun _ : ℝ × R3 => M) := contDiff_const
  exact (hχ.mul hp).sub (hOneMinus.mul hMconst)

lemma obstacleFamily_compact_perturbation {a M r R : ℝ} (cut : SmoothCutoff r R) :
    ∀ t x, R ≤ ‖x‖ → obstacleFamily a M cut t x = obstacleFamily a M cut 0 x := by
  intro t x hx
  have hχ := cut.zero_outside x hx
  simp [obstacleFamily, obstacle, hχ]

lemma obstacleFamily_asymptotically_below
    {a M r R : ℝ} (hM : 0 < M) (cut : SmoothCutoff r R) :
    ∀ t, AsymptoticallyBelow (obstacleFamily a M cut t) 0 := by
  intro t
  refine ⟨M/2, by linarith, max R 1, by positivity, ?_⟩
  intro x hx
  have hR : R ≤ ‖x‖ := le_trans (le_max_left _ _) hx
  have hχ := cut.zero_outside x hR
  simp [obstacleFamily, obstacle, hχ]
  linarith

lemma obstacleFamily_slice_smooth {a M r R : ℝ} (cut : SmoothCutoff r R) (t : ℝ) :
    ContDiff ℝ ⊤ (obstacleFamily a M cut t) := by
  have hFam : ContDiff ℝ ⊤
      (fun z : ℝ × R3 => obstacleFamily a M cut z.1 z.2) :=
    obstacleFamily_smooth cut
  have hIns : ContDiff ℝ ⊤ (fun x : R3 => (t, x)) := by
    fun_prop
  simpa [Function.comp_def, obstacleFamily] using hFam.comp hIns

lemma obstacleFamily_perturbation_tends_zero
    {a M r R : ℝ} (cut : SmoothCutoff r R) (t : ℝ) :
    TendsToConstantAtInfinity
      (fun x => obstacleFamily a M cut t x - obstacleFamily a M cut 0 x) 0 := by
  intro ε hε
  refine ⟨max R 1, by positivity, ?_⟩
  intro x hx
  have hR : R ≤ ‖x‖ := le_trans (le_max_left _ _) hx
  have hχ := cut.zero_outside x hR
  simp [obstacleFamily, obstacle, hχ, hε]

lemma obstacleFamily_laplacian_perturbation_zero_outside
    (pub : PublishedTheory) {a M r R : ℝ} (cut : SmoothCutoff r R) (t : ℝ)
    {x : R3} (hx : R ≤ ‖x‖) :
    (Laplacian.laplacian (fun y => obstacleFamily a M cut t y - obstacleFamily a M cut 0 y)) x = 0 := by
  have hχ := cut.zero_nhds_outside x hx
  have heq :
      (fun y => obstacleFamily a M cut t y - obstacleFamily a M cut 0 y)
        =ᶠ[nhds x] (fun _ : R3 => 0) := by
    filter_upwards [hχ] with y hy
    simp [obstacleFamily, obstacle, hy]
  rw [pub.laplacian_congr_nhds heq]
  simp

/-- Exact initial coincidence set for the smooth cutoff obstacle. -/
lemma initial_contact_eq_closedBall
    (pub : PublishedTheory) {a r R M : ℝ}
    (ha : 0 < a) (har : a < r) (hM : 0 < M)
    (cut : SmoothCutoff r R) :
    contactSet (newtonPotential (Ball a)) (obstacleFamily a M cut 0) = ClosedBall a := by
  ext x
  constructor
  · intro hx
    have heq : newtonPotential (Ball a) x = obstacleFamily a M cut 0 x := by
      simpa [contactSet] using hx
    by_contra hnot
    have hxa : a < ‖x‖ := by
      have : ¬ ‖x‖ ≤ a := by simpa [mem_ClosedBall_iff] using hnot
      exact lt_of_not_ge this
    have hgap : 0 < newtonPotential (Ball a) x - q a x := by
      rw [pub.ball_gap ha x hxa]
      have hxpos : 0 < ‖x‖ := lt_trans ha hxa
      positivity
    have hU : 0 < newtonPotential (Ball a) x := pub.ball_positive ha x
    have hχ0 : 0 ≤ cut.χ x := cut.nonneg x
    have hχ1 : cut.χ x ≤ 1 := cut.le_one x
    have hcalc :
        newtonPotential (Ball a) x - obstacleFamily a M cut 0 x =
          cut.χ x * (newtonPotential (Ball a) x - q a x) +
          (1-cut.χ x) * (newtonPotential (Ball a) x + M) := by
      simp [obstacleFamily, obstacle, p]
      ring
    have hstrict : 0 < newtonPotential (Ball a) x - obstacleFamily a M cut 0 x := by
      rw [hcalc]
      by_cases hc : cut.χ x = 0
      · simp [hc]
        linarith
      · have hcpos : 0 < cut.χ x := lt_of_le_of_ne hχ0 (Ne.symm hc)
        have hsecond : 0 ≤ (1-cut.χ x) * (newtonPotential (Ball a) x + M) := by
          exact mul_nonneg (sub_nonneg.mpr hχ1) (by linarith)
        exact add_pos_of_pos_of_nonneg (mul_pos hcpos hgap) hsecond
    linarith
  · intro hx
    have hnorm : ‖x‖ ≤ a := mem_ClosedBall_iff.mp hx
    have hχ : cut.χ x = 1 := cut.one_on x (le_trans hnorm (le_of_lt har))
    have hball := pub.ball_inside ha x hnorm
    simpa [contactSet, obstacleFamily, obstacle, p, hχ] using hball

lemma initial_obstacle_dominated
    (pub : PublishedTheory) {a r R M : ℝ}
    (ha : 0 < a) (har : a < r) (hM : 0 < M)
    (cut : SmoothCutoff r R) :
    ∀ x, obstacleFamily a M cut 0 x ≤ newtonPotential (Ball a) x := by
  intro x
  by_cases hxa : ‖x‖ ≤ a
  · have hχ : cut.χ x = 1 := cut.one_on x (le_trans hxa (le_of_lt har))
    have hball := pub.ball_inside ha x hxa
    simp [obstacleFamily, obstacle, p, hχ, hball]
  · have hax : a < ‖x‖ := lt_of_not_ge hxa
    have hgap : 0 < newtonPotential (Ball a) x - q a x := by
      rw [pub.ball_gap ha x hax]
      have hxpos : 0 < ‖x‖ := lt_trans ha hax
      positivity
    have hU : 0 < newtonPotential (Ball a) x := pub.ball_positive ha x
    have hχ0 := cut.nonneg x
    have hχ1 := cut.le_one x
    have hcalc :
        newtonPotential (Ball a) x - obstacleFamily a M cut 0 x =
          cut.χ x * (newtonPotential (Ball a) x - q a x) +
          (1-cut.χ x) * (newtonPotential (Ball a) x + M) := by
      simp [obstacleFamily, obstacle, p]
      ring
    rw [← sub_nonneg]
    rw [hcalc]
    exact add_nonneg
      (mul_nonneg hχ0 (le_of_lt hgap))
      (mul_nonneg (sub_nonneg.mpr hχ1) (by linarith))

/-- The unperturbed ball potential is indeed the obstacle solution; the proof
checks complementarity rather than storing this as part of the stability input. -/
lemma initial_ball_is_obstacle_solution
    (pub : PublishedTheory) {a r R M : ℝ}
    (ha : 0 < a) (har : a < r) (hM : 0 < M)
    (cut : SmoothCutoff r R) :
    IsObstacleSolution (obstacleFamily a M cut 0) 0
      (newtonPotential (Ball a)) := by
  apply pub.obstacle_of_complementarity
  · exact pub.ball_c11 ha
  · exact initial_obstacle_dominated pub ha har hM cut
  · exact pub.ball_decay ha
  · exact pub.ball_poisson ha
  · exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ Ball a <;> simp [bodyDensity, hx])
  · exact Filter.Eventually.of_forall (fun x hstrict => by
      by_cases hx : x ∈ Ball a
      · have hnorm : ‖x‖ < a := mem_Ball_iff.mp hx
        have hχ : cut.χ x = 1 := cut.one_on x (le_trans (le_of_lt hnorm) (le_of_lt har))
        have hball := pub.ball_inside ha x (le_of_lt hnorm)
        have heq : obstacleFamily a M cut 0 x = newtonPotential (Ball a) x := by
          simpa [obstacleFamily, obstacle, p, hχ] using hball.symm
        linarith
      · simp [bodyDensity, hx])

/-- Explicit lower bound for the ball gap outside a larger radius. -/
lemma ball_gap_lower_bound
    (pub : PublishedTheory) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {x : R3} (hbx : b ≤ ‖x‖) :
    (b-a)^2 / 6 ≤ newtonPotential (Ball a) x - q a x := by
  have hax : a < ‖x‖ := lt_of_lt_of_le hab hbx
  rw [pub.ball_gap ha x hax]
  have hxpos : 0 < ‖x‖ := lt_trans ha hax
  have hsq : (b-a)^2 ≤ (‖x‖-a)^2 := by nlinarith
  have hratio : 1 ≤ (‖x‖+2*a)/‖x‖ := by
    apply (le_div_iff₀ hxpos).2
    nlinarith
  have hnon : 0 ≤ (‖x‖-a)^2 := sq_nonneg _
  have hmul : (b-a)^2 ≤ (‖x‖-a)^2 * ((‖x‖+2*a)/‖x‖) := by
    calc
      (b-a)^2 ≤ (‖x‖-a)^2 := hsq
      _ ≤ (‖x‖-a)^2 * ((‖x‖+2*a)/‖x‖) := by nlinarith
  calc
    (b-a)^2 / 6 ≤ ((‖x‖-a)^2 * ((‖x‖+2*a)/‖x‖)) / 6 := by
      exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 6)).2 hmul
    _ = ((‖x‖-a)^2 * (‖x‖+2*a)) / (6*‖x‖) := by
      field_simp [ne_of_gt hxpos]

lemma obstacle_positive_gap
    (pub : PublishedTheory) {a b r R M : ℝ}
    (ha : 0 < a) (hab : a < b) (hM : 0 < M)
    (cut : SmoothCutoff r R) :
    ∃ δ > 0, ∀ x, b ≤ ‖x‖ →
      δ ≤ newtonPotential (Ball a) x - obstacleFamily a M cut 0 x := by
  let δ := min ((b-a)^2/6) M
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · have : 0 < b-a := sub_pos.mpr hab
      positivity
    · exact hM
  refine ⟨δ, hδ, ?_⟩
  intro x hbx
  have hA : δ ≤ newtonPotential (Ball a) x - q a x :=
    le_trans (min_le_left _ _) (ball_gap_lower_bound pub ha hab hbx)
  have hB : δ ≤ newtonPotential (Ball a) x + M := by
    have := pub.ball_positive ha x
    have hδM : δ ≤ M := min_le_right _ _
    linarith
  have hχ0 := cut.nonneg x
  have hχ1 := cut.le_one x
  have hcalc :
      newtonPotential (Ball a) x - obstacleFamily a M cut 0 x =
        cut.χ x * (newtonPotential (Ball a) x - q a x) +
        (1-cut.χ x) * (newtonPotential (Ball a) x + M) := by
    simp [obstacleFamily, obstacle, p]
    ring
  rw [hcalc]
  nlinarith

/-- Near points of `ClosedBall b`, the unperturbed cutoff obstacle agrees with `q_a`. -/
lemma obstacle_zero_eq_q_nhds
    {a b r R M : ℝ} (hbr : b < r) (cut : SmoothCutoff r R)
    {x : R3} (hxb : ‖x‖ ≤ b) :
    obstacleFamily a M cut 0 =ᶠ[nhds x] q a := by
  have hxr : ‖x‖ < r := lt_of_le_of_lt hxb hbr
  have hxmem : x ∈ Ball r := mem_Ball_iff.mpr hxr
  have hnhd : Ball r ∈ nhds x := Metric.isOpen_ball.mem_nhds hxmem
  filter_upwards [hnhd] with y hy
  have hyr : ‖y‖ < r := mem_Ball_iff.mp hy
  have hχ := cut.one_on y (le_of_lt hyr)
  simp [obstacleFamily, obstacle, p, hχ]

/-- Build an actual family of whole-space obstacle solutions using only the
standard existence theorem. -/
noncomputable def obstacleSolutionFamily
    (pub : PublishedTheory) {a M r R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (cut : SmoothCutoff r R) : ℝ → R3 → ℝ := fun t =>
  Classical.choose (pub.obstacle_exists ({
    smooth := obstacleFamily_slice_smooth cut t
    M_pos := hM
    R_pos := hR
    outside := fun x hx => by
      have hχ := cut.zero_outside x hx
      simp [obstacleFamily, obstacle, hχ]
    c_zero := rfl
  } : CompactNegativeObstacle (obstacleFamily a M cut t) 0 M R))

lemma obstacleSolutionFamily_spec
    (pub : PublishedTheory) {a M r R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (cut : SmoothCutoff r R) (t : ℝ) :
    IsObstacleSolution (obstacleFamily a M cut t) 0
      (obstacleSolutionFamily (a:=a) pub hM hR cut t) := by
  unfold obstacleSolutionFamily
  exact Classical.choose_spec (pub.obstacle_exists ({
    smooth := obstacleFamily_slice_smooth cut t
    M_pos := hM
    R_pos := hR
    outside := fun x hx => by
      have hχ := cut.zero_outside x hx
      simp [obstacleFamily, obstacle, hχ]
    c_zero := rfl
  } : CompactNegativeObstacle (obstacleFamily a M cut t) 0 M R))

lemma obstacleSolutionFamily_zero_eq_ball
    (pub : PublishedTheory) {a M r R : ℝ}
    (ha : 0 < a) (har : a < r) (hM : 0 < M) (hR : 0 < R)
    (cut : SmoothCutoff r R) :
    obstacleSolutionFamily (a:=a) pub hM hR cut 0 = newtonPotential (Ball a) := by
  apply pub.obstacle_unique
  · exact obstacleSolutionFamily_spec (a:=a) pub hM hR cut 0
  · exact initial_ball_is_obstacle_solution pub ha har hM cut

/-- Full article-specific verification of the hypotheses (1.4)--(1.11) for the
concrete smooth obstacle family. -/
theorem verify_SS
    (pub : PublishedTheory)
    {a b r R M : ℝ}
    (ha : 0 < a) (hab : a < b) (hbr : b < r) (hrR : r < R) (hM : 0 < M)
    (cut : SmoothCutoff r R) :
    ∃ ρ > 0,
      SSAssumptions (obstacleFamily a M cut) (fun _ => 0)
        (obstacleSolutionFamily (a:=a) pub hM (lt_trans ha (lt_trans hab (lt_trans hbr hrR))) cut)
        (ClosedBall a) (Ball b) ρ R := by
  have hRpos : 0 < R := lt_trans ha (lt_trans hab (lt_trans hbr hrR))
  obtain ⟨δ, hδ, hgap⟩ := obstacle_positive_gap pub ha hab hM cut
  let ρ := min δ (min (1/2 : ℝ) (a/2))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply lt_min hδ
    apply lt_min <;> nlinarith
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρhalf : ρ ≤ (1/2 : ℝ) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hρone : ρ ≤ 1 := by linarith
  have hρa : ρ < a := by
    have : ρ ≤ a/2 := le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith
  have hu0 : obstacleSolutionFamily (a:=a) pub hM hRpos cut 0 = newtonPotential (Ball a) :=
    obstacleSolutionFamily_zero_eq_ball (a:=a) pub ha (lt_trans hab hbr) hM hRpos cut
  refine ⟨ρ, hρ, ?_⟩
  refine {
    rho_pos := hρ
    R_pos := hRpos
    family_smooth := obstacleFamily_smooth cut
    c_smooth := by fun_prop
    solutions := ?_
    asymptotic_separation := obstacleFamily_asymptotically_below hM cut
    laplacian_perturbation_zero_outside := ?_
    perturbation_vanishes_at_infinity := ?_
    initial_contact := ?_
    U_open := Metric.isOpen_ball
    U_subset_ball := ?_
    C0_subset_U := ?_
    active_initial := ?_
    negative_laplacian := ?_
    positive_gap := ?_
    tangent_balls := pub.closedBall_twoSided hρ hρa
  }
  · intro t _ht
    exact obstacleSolutionFamily_spec (a:=a) pub hM hRpos cut t
  · intro t x hx
    exact obstacleFamily_laplacian_perturbation_zero_outside pub cut t hx
  · intro t
    exact obstacleFamily_perturbation_tends_zero cut t
  · rw [hu0]
    exact initial_contact_eq_closedBall pub ha (lt_trans hab hbr) hM cut
  · intro x hx
    have hxb : ‖x‖ < b := mem_Ball_iff.mp hx
    exact mem_Ball_iff.mpr (lt_trans hxb (lt_trans hbr hrR))
  · intro x hx
    have hxa : ‖x‖ ≤ a := mem_ClosedBall_iff.mp hx
    exact mem_Ball_iff.mpr (lt_of_le_of_lt hxa hab)
  · intro x hxC
    have hxa : ‖x‖ ≤ a := mem_ClosedBall_iff.mp hxC
    have hxb : ‖x‖ ≤ b := le_trans hxa (le_of_lt hab)
    have heq := obstacle_zero_eq_q_nhds (a:=a) (M:=M) hbr cut hxb
    have hlap : (Laplacian.laplacian (obstacleFamily a M cut 0)) x = -1 := by
      rw [pub.laplacian_congr_nhds heq]
      exact laplacian_q pub a x
    linarith
  · intro x hx
    have hbpos : 0 < b := lt_trans ha hab
    have hcl : closure (Ball b) = ClosedBall b := by
      simpa using pub.homeomorph_closure_ball (Homeomorph.refl R3) hbpos
    have hxb : ‖x‖ ≤ b := by
      rw [hcl] at hx
      exact mem_ClosedBall_iff.mp hx
    have heq := obstacle_zero_eq_q_nhds (a:=a) (M:=M) hbr cut hxb
    have hlap : (Laplacian.laplacian (obstacleFamily a M cut 0)) x = -1 := by
      rw [pub.laplacian_congr_nhds heq]
      exact laplacian_q pub a x
    rw [hlap]
    linarith [hρone]
  · intro x hxU
    rw [hu0]
    have hnorm : b ≤ ‖x‖ := by
      have : ¬ ‖x‖ < b := by simpa [mem_Ball_iff] using hxU
      exact le_of_not_gt this
    exact le_trans hρδ (hgap x hnorm)

/-! ## Passage from the published stability theorem to a genuine polynomial inclusion -/

structure NearBallResult (pub : PublishedTheory) (a t : ℝ) where
  K : Set R3
  C : Set R3
  u : R3 → ℝ
  Ψ : C1Diffeomorph
  K_image : K = Ψ '' Ball a
  C_image : C = Ψ '' ClosedBall a
  closure_eq : closure K = C
  interior_eq : interior C = K
  K_open : IsOpen K
  K_measurable : MeasurableSet K
  K_bounded : NormBounded K
  C_bounded : NormBounded C
  boundary_image : frontier K = Ψ '' Sphere a
  boundary_null : volume (frontier K) = 0
  sphere_boundary : SphereBoundaryLike K a
  c1_sphere_boundary : C1SphereBoundaryLike K a
  potential_inside : ∀ x ∈ K, newtonPotential K x = p a t x
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  psi_close : ∀ x, ‖Ψ x - x‖ < epsilon
  inv_close : ∀ x, ‖Ψ.inv x - x‖ < epsilon

/-- Mean-value corollary: the raw Serfaty--Serra family is uniformly close to
identity for sufficiently small positive `t`.  This is proved here; it is not
part of the free-boundary theorem interface. -/
lemma raw_family_close
    (_pub : PublishedTheory)
    {h : ℝ → R3 → ℝ} {c : ℝ → ℝ} {u : ℝ → R3 → ℝ}
    {C0 U : Set R3}
    (raw : SSRawOutput h c u C0 U)
    {C t ε : ℝ} (hC : 0 < C)
    (hbound : ∀ s, |s| < raw.t0 → ∀ x, ‖raw.velocity s x‖ ≤ C)
    (ht : 0 < t) (ht0 : t < raw.t0) (_hε : 0 < ε)
    (hsmall : t < ε / (C + 1)) :
    ∀ x, ‖raw.Ψ t x - x‖ < ε := by
  intro x
  have hderiv : ∀ s, s ∈ Set.Icc (0:ℝ) t →
      HasDerivAt (fun z => raw.Ψ z x) (raw.velocity s x) s := by
    intro s hs
    have hsabs : |s| < raw.t0 := by
      rw [abs_of_nonneg hs.1]
      exact lt_of_le_of_lt hs.2 ht0
    exact raw.hasDeriv s hsabs x
  have hvel : ∀ s, s ∈ Set.Icc (0:ℝ) t → ‖raw.velocity s x‖ ≤ C := by
    intro s hs
    have hsabs : |s| < raw.t0 := by
      rw [abs_of_nonneg hs.1]
      exact lt_of_le_of_lt hs.2 ht0
    exact hbound s hsabs x
  have hmvt :
      ‖raw.Ψ t x - raw.Ψ 0 x‖ ≤ C * ‖t - (0 : ℝ)‖ := by
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.Icc (0 : ℝ) t)
      (f := fun z => raw.Ψ z x)
      (f' := fun z => raw.velocity z x)
      (C := C)
      (x := (0 : ℝ)) (y := t)
      (fun s hs => (hderiv s hs).hasDerivWithinAt)
      hvel
      (convex_Icc (0 : ℝ) t)
      ⟨le_rfl, le_of_lt ht⟩
      ⟨le_of_lt ht, le_rfl⟩
  have hmvt' : ‖raw.Ψ t x - raw.Ψ 0 x‖ ≤ C * t := by
    simpa [Real.norm_eq_abs, abs_of_pos ht] using hmvt
  rw [raw.psi_zero x] at hmvt'
  have hden : 0 < C + 1 := by linarith
  have hCt : C * t < ε := by
    have hsmall' : t * (C + 1) < ε := (lt_div_iff₀ hden).mp hsmall
    nlinarith
  exact lt_of_le_of_lt hmvt' hCt

lemma raw_family_inv_close
    {h : ℝ → R3 → ℝ} {c : ℝ → ℝ} {u : ℝ → R3 → ℝ}
    {C0 U : Set R3} (raw : SSRawOutput h c u C0 U)
    {t ε : ℝ} (hclose : ∀ x, ‖raw.Ψ t x - x‖ < ε) :
    ∀ x, ‖(raw.Ψ t).inv x - x‖ < ε := by
  intro x
  let y := (raw.Ψ t).inv x
  have hc := hclose y
  have hxy : raw.Ψ t y = x := (raw.Ψ t).right_inv x
  rw [hxy] at hc
  simpa [y, norm_sub_rev] using hc

/-- Contact set equals the image of the initial closed ball, deduced from the
published mapping of the noncontact set. -/
lemma contact_image_of_raw
    {h : ℝ → R3 → ℝ} {c : ℝ → ℝ} {u : ℝ → R3 → ℝ}
    {a : ℝ} {U : Set R3}
    (raw : SSRawOutput h c u (ClosedBall a) U)
    {t : ℝ} (ht : |t| < raw.t0)
    (hcontact0 : contactSet (u 0) (h 0) = ClosedBall a)
    (hdom0 : ∀ x, h 0 x ≤ u 0 x)
    (hdomt : ∀ x, h t x ≤ u t x) :
    contactSet (u t) (h t) = raw.Ψ t '' ClosedBall a := by
  apply compl_injective
  rw [contact_compl_eq_noncontact hdomt]
  rw [← raw.noncontact_image t ht]
  rw [← contact_compl_eq_noncontact hdom0, hcontact0]
  exact image_compl_equiv (raw.Ψ t).homeomorph.toEquiv (ClosedBall a)

/-- The actual shared near-ball lemma.  The published theorem supplies only the
raw differentiable family; all small-parameter, contact-set, Poisson, Newtonian,
and topology conclusions are proved here. -/
theorem nearBall
    (pub : PublishedTheory)
    {a b r R M ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hbr : b < r) (hrR : r < R) (hM : 0 < M)
    (hε : 0 < ε) (hεmargin : ε < r - a) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ →
      ∃ nb : NearBallResult pub a t, nb.epsilon = ε := by
  let cut := pub.smooth_cutoff (lt_trans ha (lt_trans hab hbr)) hrR
  have hRpos : 0 < R := lt_trans ha (lt_trans hab (lt_trans hbr hrR))
  obtain ⟨ρ, hρ, hSS⟩ := verify_SS pub ha hab hbr hrR hM cut
  let raw := pub.ss_stability_raw hSS
  obtain ⟨Cvel, hCvel, hvelBound⟩ := raw.velocity_bound
  let τ := min raw.t0 (min 1 (ε / (Cvel + 1)))
  have hden : 0 < Cvel + 1 := by linarith
  have hτ : 0 < τ := by
    dsimp [τ]
    apply lt_min raw.t0_pos
    apply lt_min (by norm_num)
    exact div_pos hε hden
  refine ⟨τ, hτ, ?_⟩
  intro t htpos htτ
  have ht0 : t < raw.t0 := lt_of_lt_of_le htτ (min_le_left _ _)
  have ht1 : t < 1 :=
    lt_of_lt_of_le htτ (le_trans (min_le_right _ _) (min_le_left _ _))
  have htsmall : t < ε / (Cvel+1) :=
    lt_of_lt_of_le htτ (le_trans (min_le_right _ _) (min_le_right _ _))
  have habst : |t| < raw.t0 := by rw [abs_of_pos htpos]; exact ht0
  have htle1 : |t| ≤ 1 := by rw [abs_of_pos htpos]; exact le_of_lt ht1
  have hsolt := hSS.solutions t htle1
  have hsol0 := hSS.solutions 0 (by norm_num)
  have hclose : ∀ x, ‖raw.Ψ t x-x‖ < ε :=
    raw_family_close pub raw hCvel hvelBound htpos ht0 hε htsmall
  have hinvclose := raw_family_inv_close raw hclose
  let outΨ := raw.Ψ t
  let Cset : Set R3 := contactSet (obstacleSolutionFamily (a:=a) pub hM hRpos cut t) (obstacleFamily a M cut t)
  let K : Set R3 := outΨ '' Ball a
  have hC : Cset = outΨ '' ClosedBall a := by
    dsimp [Cset, outΨ]
    exact contact_image_of_raw raw habst hSS.initial_contact hsol0.dominates hsolt.dominates
  have hclosure : closure K = Cset := by
    dsimp [K, outΨ]
    rw [pub.homeomorph_closure_ball (raw.Ψ t).homeomorph ha, ← hC]
  have hinterior : interior Cset = K := by
    rw [hC]
    simpa [K, outΨ] using pub.homeomorph_interior_closedBall (raw.Ψ t).homeomorph ha
  have hopen : IsOpen K := by rw [← hinterior]; exact isOpen_interior
  have hmeas : MeasurableSet K := hopen.measurableSet
  have hfront : frontier K = outΨ '' Sphere a := by
    simpa [K, outΨ] using pub.homeomorph_frontier_ball (raw.Ψ t).homeomorph ha
  have hnull : volume (frontier K) = 0 := by
    rw [hfront]
    exact pub.c1_sphere_image_null (raw.Ψ t) ha
  have hCinside : Cset ⊆ Ball r := by
    intro x hx
    rw [hC] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hya : ‖y‖ ≤ a := mem_ClosedBall_iff.mp hy
    have htri : ‖raw.Ψ t y‖ ≤ ‖raw.Ψ t y - y‖ + ‖y‖ := by
      calc
        ‖raw.Ψ t y‖ = ‖(raw.Ψ t y - y) + y‖ := by
          rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hc := hclose y
    have hnorm : ‖raw.Ψ t y‖ < r := by linarith
    exact mem_Ball_iff.mpr hnorm
  have hKsubC : K ⊆ Cset := by
    intro x hx
    have hxcl : x ∈ closure K := subset_closure hx
    rw [hclosure] at hxcl
    exact hxcl
  have hu_p : ∀ x ∈ K, obstacleSolutionFamily (a:=a) pub hM hRpos cut t x = p a t x := by
    intro x hx
    have hxC := hKsubC hx
    have hcontact : obstacleSolutionFamily (a:=a) pub hM hRpos cut t x = obstacleFamily a M cut t x := by
      simpa [Cset, contactSet] using hxC
    have hxr : ‖x‖ < r := mem_Ball_iff.mp (hCinside hxC)
    have hχ := cut.one_on x (le_of_lt hxr)
    exact hcontact.trans (obstacle_eq_p_of_one hχ)
  have hbound : NormBounded K := by
    refine ⟨r, ?_⟩
    intro x hx
    exact le_of_lt (mem_Ball_iff.mp (hCinside (hKsubC hx)))
  have hCbound : NormBounded Cset := by
    refine ⟨r, ?_⟩
    intro x hx
    exact le_of_lt (mem_Ball_iff.mp (hCinside hx))
  have haeLap : ∀ᵐ x ∂volume,
      (Laplacian.laplacian (obstacleSolutionFamily (a:=a) pub hM hRpos cut t)) x = - bodyDensity K x := by
    have hoff := pub.ae_not_mem_of_null hnull
    filter_upwards [hoff] with x hxfront
    by_cases hxK : x ∈ K
    · have hnhdK : K ∈ nhds x := hopen.mem_nhds hxK
      have heq : obstacleSolutionFamily (a:=a) pub hM hRpos cut t =ᶠ[nhds x] p a t := by
        filter_upwards [hnhdK] with y hy
        exact hu_p y hy
      have hlap : (Laplacian.laplacian (obstacleSolutionFamily (a:=a) pub hM hRpos cut t)) x = -1 := by
        rw [pub.laplacian_congr_nhds heq]
        exact laplacian_p pub a t x
      simp [bodyDensity, hxK, hlap]
    · have hxnotcl : x ∉ closure K := by
        intro hxcl
        have hxfr : x ∈ frontier K := by rw [hopen.frontier_eq]; exact ⟨hxcl, hxK⟩
        exact hxfront hxfr
      have hxnotC : x ∉ Cset := by simpa [← hclosure] using hxnotcl
      have hxnon : x ∈ noncontactSet (obstacleSolutionFamily (a:=a) pub hM hRpos cut t)
          (obstacleFamily a M cut t) := by
        have hcomp := contact_compl_eq_noncontact hsolt.dominates
        rw [← hcomp]
        simpa [Cset] using hxnotC
      have hlap : (Laplacian.laplacian (obstacleSolutionFamily (a:=a) pub hM hRpos cut t)) x = 0 :=
        hsolt.harmonic_noncontact x hxnon
      simp [bodyDensity, hxK, hlap]
  have hdist : HasDistributionalNegLaplacian
      (obstacleSolutionFamily (a:=a) pub hM hRpos cut t) (bodyDensity K) := by
    apply pub.c11_ae_laplacian_to_distribution hsolt.c11
    · exact pub.bodyDensity_locallyIntegrable hmeas
    · exact haeLap
  have hnewton : obstacleSolutionFamily (a:=a) pub hM hRpos cut t = newtonPotential K :=
    pub.newton_uniqueness hmeas hbound hsolt.atInfinity hdist
  have hpot : ∀ x ∈ K, newtonPotential K x = p a t x := by
    intro x hx
    rw [← hnewton]
    exact hu_p x hx
  refine ⟨{
    K := K
    C := Cset
    u := obstacleSolutionFamily (a:=a) pub hM hRpos cut t
    Ψ := outΨ
    K_image := rfl
    C_image := hC
    closure_eq := hclosure
    interior_eq := hinterior
    K_open := hopen
    K_measurable := hmeas
    K_bounded := hbound
    C_bounded := hCbound
    boundary_image := hfront
    boundary_null := hnull
    sphere_boundary := ⟨outΨ.homeomorph, hfront.symm⟩
    c1_sphere_boundary := ⟨outΨ, hfront.symm⟩
    potential_inside := hpot
    epsilon := ε
    epsilon_pos := hε
    psi_close := hclose
    inv_close := hinvclose
  }, rfl⟩

/-! The following lemmas establish boundary extension and equality of the open and
closed body's volume potentials from the actual integral definition. -/

lemma open_ae_closure (pub : PublishedTheory) {K : Set R3}
    (hopen : IsOpen K) (hnull : volume (frontier K) = 0) :
    K =ᵐ[volume] closure K := by
  have hoff := pub.ae_not_mem_of_null hnull
  filter_upwards [hoff] with x hxfr
  change (x ∈ K) = (x ∈ closure K)
  apply propext
  constructor
  · intro hxK
    exact subset_closure hxK
  · intro hxcl
    by_contra hxK
    exact hxfr (by rw [hopen.frontier_eq]; exact ⟨hxcl, hxK⟩)

lemma newtonPotential_closure_eq
    (pub : PublishedTheory) {a t : ℝ} (nb : NearBallResult pub a t) :
    newtonPotential (closure nb.K) = newtonPotential nb.K := by
  funext x
  unfold newtonPotential
  rw [Measure.restrict_congr_set (open_ae_closure pub nb.K_open nb.boundary_null).symm]

lemma potential_on_closure
    (pub : PublishedTheory) {a t : ℝ} (nb : NearBallResult pub a t) :
    ∀ x ∈ closure nb.K, newtonPotential nb.K x = p a t x := by
  have hcontU : Continuous (newtonPotential nb.K) :=
    pub.newton_continuous nb.K_measurable nb.K_bounded
  have hcontP : Continuous (p a t) := by
    change Continuous (fun x : R3 =>
      a ^ 2 / 2 - ((x 0)^2 + (x 1)^2 + (x 2)^2) / 6 +
        t * ((x 0)^3 - 3 * (x 0) * (x 1)^2))
    fun_prop
  have hclosed : IsClosed {x | newtonPotential nb.K x = p a t x} :=
    isClosed_eq hcontU hcontP
  have hsub : nb.K ⊆ {x | newtonPotential nb.K x = p a t x} := by
    intro x hx
    exact nb.potential_inside x hx
  exact fun x hx => closure_minimal hsub hclosed hx

/-- High-degree obstruction, proved locally on an open segment.  The external
ellipsoid input says only that an ellipsoid has a quadratic interior potential;
the contradiction with the cubic is proved here. -/
lemma nearBall_body_not_ellipsoid
    (pub : PublishedTheory) {a t : ℝ} (ha : 0 < a) (ht : t ≠ 0)
    (nb : NearBallResult pub a t) :
    ¬ IsSolidEllipsoid (closure nb.K) := by
  intro hEll
  obtain ⟨Q, hQ⟩ := pub.ellipsoid_quadratic_potential hEll
  have hvol : newtonPotential (closure nb.K) = newtonPotential nb.K :=
    newtonPotential_closure_eq pub nb
  have hinterior : interior (closure nb.K) = nb.K := by
    rw [nb.closure_eq, nb.interior_eq]
  have hpQ : ∀ y ∈ nb.K, p a t y = Q.eval y := by
    intro y hy
    have hyInt : y ∈ interior (closure nb.K) := by simpa [hinterior] using hy
    have hqy := hQ y hyInt
    rw [hvol] at hqy
    exact (nb.potential_inside y hy).symm.trans hqy
  have hneK : nb.K.Nonempty := by
    rw [nb.K_image]
    refine ⟨nb.Ψ 0, ⟨0, ?_, rfl⟩⟩
    exact mem_Ball_iff.mpr (by simpa using ha)
  obtain ⟨x, s, hs, hx0, hx1, hx2, hx3⟩ :=
    open_contains_e1_progression nb.K_open hneK
  have hdiff : thirdDiffAt (p a t) x (s • e1) =
      thirdDiffAt Q.eval x (s • e1) := by
    simp only [thirdDiffAt, smul_smul]
    rw [hpQ _ hx3, hpQ _ hx2, hpQ _ hx1, hpQ _ hx0]
  have hquad : thirdDiffAt Q.eval x (s • e1) = 0 :=
    Quadratic3.thirdDiffAt_eval Q x s
  have hcubic : thirdDiffAt (p a t) x (s • e1) ≠ 0 :=
    thirdDiffAt_p_e1_ne_zero x ht (ne_of_gt hs)
  exact hcubic (hdiff.trans hquad)

end Nikliborc


/-! --------------------------------------------------------------------------
    Next embedded module
-------------------------------------------------------------------------- -/

/-!
# Complete formal deduction for Nikliborc Problem 129

Every article-specific step L129.1--L129.10 is proved here or in the shared
`NikliborcNearBall` module.  In particular the shell potential is derived from
the actual Newtonian set integral; it is not defined to be a difference.
-/

namespace Nikliborc129

open Set MeasureTheory
open Nikliborc

/-- The physical shell between two genuinely separated bodies. -/
def shell (K1 K2 : Set R3) : Set R3 := K2 \ closure K1

/-- Quantitative closeness of the two published diffeomorphisms gives strict
nesting of the *closed* inner body. -/
lemma strict_nesting_from_quarter_close
    (pub : PublishedTheory) {t : ℝ}
    (n1 : NearBallResult pub 1 t) (n2 : NearBallResult pub 2 t)
    (h1close : ∀ x, ‖n1.Ψ x-x‖ < (1/4 : ℝ))
    (h2invclose : ∀ x, ‖n2.Ψ.inv x-x‖ < (1/4 : ℝ)) :
    closure n1.K ⊆ n2.K := by
  intro x hx
  rw [n1.closure_eq, n1.C_image] at hx
  rcases hx with ⟨y, hy, rfl⟩
  have hy1 : ‖y‖ ≤ 1 := mem_ClosedBall_iff.mp hy
  have hx54 : ‖n1.Ψ y‖ < (5/4 : ℝ) := by
    have htri : ‖n1.Ψ y‖ ≤ ‖n1.Ψ y-y‖ + ‖y‖ := by
      calc
        ‖n1.Ψ y‖ = ‖(n1.Ψ y-y)+y‖ := by
          rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith [h1close y]
  let z := n2.Ψ.inv (n1.Ψ y)
  have hz2 : ‖z‖ < 2 := by
    have htri : ‖z‖ ≤ ‖z-n1.Ψ y‖ + ‖n1.Ψ y‖ := by
      calc
        ‖z‖ = ‖(z-n1.Ψ y)+n1.Ψ y‖ := by
          rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hcl := h2invclose (n1.Ψ y)
    dsimp [z] at htri ⊢
    linarith
  rw [n2.K_image]
  refine ⟨z, mem_Ball_iff.mpr hz2, ?_⟩
  exact n2.Ψ.right_inv (n1.Ψ y)

lemma shell_union_closed_inner {K1 K2 : Set R3}
    (hnest : closure K1 ⊆ K2) :
    shell K1 K2 ∪ closure K1 = K2 := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxShell | hxCl
    · exact hxShell.1
    · exact hnest hxCl
  · intro x hxK2
    by_cases hxCl : x ∈ closure K1
    · exact Or.inr hxCl
    · exact Or.inl ⟨hxK2, hxCl⟩

lemma shell_disjoint_closed_inner {K1 K2 : Set R3} :
    Disjoint (shell K1 K2) (closure K1) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hcl
  exact hx.2 hcl

lemma shell_measurable {K1 K2 : Set R3} (hopen2 : IsOpen K2) :
    MeasurableSet (shell K1 K2) := by
  exact hopen2.measurableSet.diff isClosed_closure.measurableSet

/-- L129.7: derive the shell identity from the integral definition. -/
lemma shell_potential_difference
    (pub : PublishedTheory) {a1 a2 t : ℝ}
    (n1 : NearBallResult pub a1 t) (n2 : NearBallResult pub a2 t)
    (hnest : closure n1.K ⊆ n2.K) :
    ∀ x : R3,
      newtonPotential (shell n1.K n2.K) x =
        newtonPotential n2.K x - newtonPotential n1.K x := by
  intro x
  have hclMeas : MeasurableSet (closure n1.K) := isClosed_closure.measurableSet
  have hintK2 := pub.kernel_integrableOn n2.K_measurable n2.K_bounded x
  have hdiff := MeasureTheory.setIntegral_sdiff
    (f := newtonKernel x) (s := n2.K) (t := closure n1.K)
    hclMeas hintK2 hnest
  have hclosurePot : newtonPotential (closure n1.K) x = newtonPotential n1.K x := by
    exact congrFun (newtonPotential_closure_eq pub n1) x
  have hclosureInt :
      (∫ y in closure n1.K, newtonKernel x y) =
        ∫ y in n1.K, newtonKernel x y := by
    simpa [newtonPotential] using hclosurePot
  unfold shell newtonPotential
  calc
    ∫ y in n2.K \ closure n1.K, newtonKernel x y =
        (∫ y in n2.K, newtonKernel x y) -
          ∫ y in closure n1.K, newtonKernel x y := hdiff
    _ = (∫ y in n2.K, newtonKernel x y) -
          ∫ y in n1.K, newtonKernel x y := by rw [hclosureInt]

/-- L129.8: the shared quadratic and harmonic terms cancel exactly. -/
lemma cancellation_three_halves
    {t : ℝ} {K1 K2 : Set R3}
    (hpot1 : ∀ x ∈ K1, newtonPotential K1 x = p 1 t x)
    (hpot2 : ∀ x ∈ K2, newtonPotential K2 x = p 2 t x)
    (hnest : K1 ⊆ K2)
    (hshell : ∀ x,
      newtonPotential (shell K1 K2) x =
        newtonPotential K2 x - newtonPotential K1 x) :
    ∀ x ∈ K1, newtonPotential (shell K1 K2) x = (3/2 : ℝ) := by
  intro x hx
  have hx2 := hnest hx
  rw [hshell x, hpot2 x hx2, hpot1 x hx]
  simp [p, q]
  ring

/-- Exact counterexample data for the printed Problem 129. -/
structure Counterexample129 (pub : PublishedTheory) where
  inner : Set R3
  outer : Set R3
  material : Set R3
  inner_open : IsOpen inner
  outer_open : IsOpen outer
  inner_bounded : NormBounded inner
  outer_bounded : NormBounded outer
  strict_nested : closure inner ⊆ outer
  inner_boundary_sphere : C1SphereBoundaryLike inner 1
  outer_boundary_sphere : C1SphereBoundaryLike outer 2
  material_eq : material = shell inner outer
  constant_cavity : ∀ x ∈ inner, newtonPotential material x = (3/2 : ℝ)
  inner_nonellipsoid : ¬ IsSolidEllipsoid (closure inner)
  outer_nonellipsoid : ¬ IsSolidEllipsoid (closure outer)
  not_homothetic_ellipsoids : ¬ HomotheticEllipsoidPair inner outer

/-- Negative answer to Problem 129, relative only to the allowed public inputs. -/
theorem negative_answer_129 (pub : PublishedTheory) :
    Nonempty (Counterexample129 pub) := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  have h1b : (1 : ℝ) < 5/4 := by norm_num
  have h1r : (5/4 : ℝ) < 3/2 := by norm_num
  have h1R : (3/2 : ℝ) < 2 := by norm_num
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h2b : (2 : ℝ) < 9/4 := by norm_num
  have h2r : (9/4 : ℝ) < 5/2 := by norm_num
  have h2R : (5/2 : ℝ) < 3 := by norm_num
  have hM : (0 : ℝ) < 1 := by norm_num
  have hε : (0 : ℝ) < 1/8 := by norm_num
  have hεmargin1 : (1/8 : ℝ) < 3/2 - 1 := by norm_num
  have hεmargin2 : (1/8 : ℝ) < 5/2 - 2 := by norm_num
  obtain ⟨τ1, hτ1, hn1⟩ := nearBall pub h1 h1b h1r h1R hM hε hεmargin1
  obtain ⟨τ2, hτ2, hn2⟩ := nearBall pub h2 h2b h2r h2R hM hε hεmargin2
  let τ := min τ1 τ2
  have hτ : 0 < τ := lt_min hτ1 hτ2
  let t : ℝ := τ/2
  have htpos : 0 < t := by dsimp [t]; linarith
  have htτ : t < τ := by dsimp [t]; linarith
  have ht1 : t < τ1 := lt_of_lt_of_le htτ (min_le_left _ _)
  have ht2 : t < τ2 := lt_of_lt_of_le htτ (min_le_right _ _)
  obtain ⟨n1, hn1ε⟩ := hn1 t htpos ht1
  obtain ⟨n2, hn2ε⟩ := hn2 t htpos ht2
  have h1close : ∀ x, ‖n1.Ψ x-x‖ < (1/4 : ℝ) := by
    intro x
    have := n1.psi_close x
    have he : n1.epsilon < (1/4 : ℝ) := by
      rw [hn1ε]
      norm_num
    linarith
  have h2invclose : ∀ x, ‖n2.Ψ.inv x-x‖ < (1/4 : ℝ) := by
    intro x
    have hc := n2.inv_close x
    have he : n2.epsilon < (1/4 : ℝ) := by
      rw [hn2ε]
      norm_num
    linarith
  have hnestClosed : closure n1.K ⊆ n2.K :=
    strict_nesting_from_quarter_close pub n1 n2 h1close h2invclose
  have hnest : n1.K ⊆ n2.K := fun x hx => hnestClosed (subset_closure hx)
  have hshell := shell_potential_difference pub n1 n2 hnestClosed
  have hconst := cancellation_three_halves
    n1.potential_inside n2.potential_inside hnest hshell
  have hnell1 : ¬ IsSolidEllipsoid (closure n1.K) :=
    nearBall_body_not_ellipsoid pub h1 (ne_of_gt htpos) n1
  have hnell2 : ¬ IsSolidEllipsoid (closure n2.K) :=
    nearBall_body_not_ellipsoid pub h2 (ne_of_gt htpos) n2
  have hnotHom : ¬ HomotheticEllipsoidPair n1.K n2.K := by
    intro hhom
    exact hnell1 hhom.1
  exact ⟨{
    inner := n1.K
    outer := n2.K
    material := shell n1.K n2.K
    inner_open := n1.K_open
    outer_open := n2.K_open
    inner_bounded := n1.K_bounded
    outer_bounded := n2.K_bounded
    strict_nested := hnestClosed
    inner_boundary_sphere := n1.c1_sphere_boundary
    outer_boundary_sphere := n2.c1_sphere_boundary
    material_eq := rfl
    constant_cavity := hconst
    inner_nonellipsoid := hnell1
    outer_nonellipsoid := hnell2
    not_homothetic_ellipsoids := hnotHom
  }⟩

end Nikliborc129

#print axioms Nikliborc129.negative_answer_129

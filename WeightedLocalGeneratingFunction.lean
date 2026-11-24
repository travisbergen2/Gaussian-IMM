import WeightedLocalIdealCount

/-!
# WeightedLocalGeneratingFunction — Σₖ N(k) xᵏ = ∏ᵢ (1 − x^{fᵢ})⁻¹

N(k) = #{a ∈ ℕ^g : Σᵢ fᵢ aᵢ = k}, all fᵢ > 0, ‖x‖ < 1. With `WeightedCount`, this is the local
Euler factor at p for any residue-degree pattern (Galois or not).

Route: (1) over the whole tuple space, Σ_a x^{Σ fᵢaᵢ} = ∏ᵢ (1 − x^{fᵢ})⁻¹, by induction on g using
`Fin.consEquiv` and products of absolutely convergent series (real version first, for the norms);
(2) regroup by the weight k (`HasSum.sigma`); each fiber is finite and contributes N(k)·xᵏ.
-/

open Finset

namespace WeightedCount

/-- The weight Σᵢ fᵢ aᵢ. -/
def weight {g : ℕ} (f : Fin g → ℕ) (a : Fin g → ℕ) : ℕ := ∑ i, f i * a i

theorem weight_cons {g : ℕ} (f : Fin (g + 1) → ℕ) (a0 : ℕ) (a : Fin g → ℕ) :
    weight f (Fin.cons a0 a) = f 0 * a0 + weight (Fin.tail f) a := by
  simp [weight, Fin.sum_univ_succ, Fin.tail]

/-- Real version over the tuple space, nonnegative base. -/
theorem hasSum_tuple_real {g : ℕ} (f : Fin g → ℕ) (hf : ∀ i, 0 < f i) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) :
    HasSum (fun a : Fin g → ℕ => r ^ weight f a) (∏ i, (1 - r ^ f i)⁻¹) := by
  induction g with
  | zero =>
    rw [show (fun a : Fin 0 → ℕ => r ^ weight f a) = fun _ => 1 from funext fun a => by simp [weight]]
    simp
  | succ g ih =>
    have hf0 : f 0 ≠ 0 := (hf 0).ne'
    have h1 : r ^ f 0 < 1 := pow_lt_one₀ hr0 hr hf0
    have h0 : HasSum (fun n : ℕ => (r ^ f 0) ^ n) (1 - r ^ f 0)⁻¹ :=
      hasSum_geometric_of_lt_one (pow_nonneg hr0 _) h1
    have ht := ih (Fin.tail f) (fun i => hf _)
    have hs : Summable (fun p : ℕ × (Fin g → ℕ) =>
        (r ^ f 0) ^ p.1 * r ^ weight (Fin.tail f) p.2) :=
      Summable.mul_of_nonneg (f := fun n : ℕ => (r ^ f 0) ^ n)
        (g := fun a : Fin g → ℕ => r ^ weight (Fin.tail f) a) h0.summable ht.summable
        (fun n => pow_nonneg (pow_nonneg hr0 _) n) (fun a => pow_nonneg hr0 _)
    have hprod := h0.mul ht hs
    have key : (fun p : ℕ × (Fin g → ℕ) => r ^ weight f (Fin.cons p.1 p.2)) =
        fun p => (r ^ f 0) ^ p.1 * r ^ weight (Fin.tail f) p.2 :=
      funext fun p => by rw [weight_cons, pow_add, pow_mul]
    rw [Fin.prod_univ_succ, ← (Fin.consEquiv fun _ => ℕ).hasSum_iff]
    show HasSum (fun p : ℕ × (Fin g → ℕ) => r ^ weight f (Fin.cons p.1 p.2)) _
    rw [key]
    exact hprod

theorem hasSum_tuple {g : ℕ} (f : Fin g → ℕ) (hf : ∀ i, 0 < f i) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun a : Fin g → ℕ => x ^ weight f a) (∏ i, (1 - x ^ f i)⁻¹) := by
  induction g with
  | zero =>
    rw [show (fun a : Fin 0 → ℕ => x ^ weight f a) = fun _ => 1 from funext fun a => by simp [weight]]
    simp
  | succ g ih =>
    have hf0 : f 0 ≠ 0 := (hf 0).ne'
    have h1 : ‖x‖ ^ f 0 < 1 := pow_lt_one₀ (norm_nonneg _) hx hf0
    have h0 : HasSum (fun n : ℕ => (x ^ f 0) ^ n) (1 - x ^ f 0)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (by rw [norm_pow]; exact h1)
    have ht := ih (Fin.tail f) (fun i => hf _)
    have hn0 : Summable (fun n : ℕ => ‖(x ^ f 0) ^ n‖) := by
      simp only [norm_pow]
      exact summable_geometric_of_lt_one (pow_nonneg (norm_nonneg _) _) h1
    have hnt : Summable (fun a : Fin g → ℕ => ‖x ^ weight (Fin.tail f) a‖) := by
      simp only [norm_pow]
      exact (hasSum_tuple_real (Fin.tail f) (fun i => hf _) (norm_nonneg _) hx).summable
    have hs : Summable (fun p : ℕ × (Fin g → ℕ) =>
        (x ^ f 0) ^ p.1 * x ^ weight (Fin.tail f) p.2) :=
      summable_mul_of_summable_norm (f := fun n : ℕ => (x ^ f 0) ^ n)
        (g := fun a : Fin g → ℕ => x ^ weight (Fin.tail f) a) hn0 hnt
    have hprod := h0.mul ht hs
    have key : (fun p : ℕ × (Fin g → ℕ) => x ^ weight f (Fin.cons p.1 p.2)) =
        fun p => (x ^ f 0) ^ p.1 * x ^ weight (Fin.tail f) p.2 :=
      funext fun p => by rw [weight_cons, pow_add, pow_mul]
    rw [Fin.prod_univ_succ, ← (Fin.consEquiv fun _ => ℕ).hasSum_iff]
    show HasSum (fun p : ℕ × (Fin g → ℕ) => x ^ weight f (Fin.cons p.1 p.2)) _
    rw [key]
    exact hprod

theorem finite_fiber {g : ℕ} (f : Fin g → ℕ) (hf : ∀ i, 0 < f i) (k : ℕ) :
    Finite {a : Fin g → ℕ // weight f a = k} := by
  refine Finite.of_injective (fun a : {a : Fin g → ℕ // weight f a = k} =>
    fun i => (⟨a.1 i, ?_⟩ : Fin (k + 1))) ?_
  · have hle : f i * a.1 i ≤ k := by
      calc f i * a.1 i ≤ weight f a.1 :=
            single_le_sum (f := fun j => f j * a.1 j) (fun j _ => Nat.zero_le _) (mem_univ i)
        _ = k := a.2
    have := Nat.le_mul_of_pos_left (a.1 i) (hf i)
    omega
  · intro a b h
    apply Subtype.ext; funext i
    have := congrFun h i
    simpa using congrArg Fin.val this

/-- **Weighted local generating function.** -/
theorem hasSum_weighted {g : ℕ} (f : Fin g → ℕ) (hf : ∀ i, 0 < f i) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (Nat.card {a : Fin g → ℕ // ∑ i, f i * a i = k} : ℂ) * x ^ k)
      (∏ i, (1 - x ^ f i)⁻¹) := by
  have htup := hasSum_tuple f hf hx
  rw [← (Equiv.sigmaFiberEquiv (weight f)).hasSum_iff] at htup
  refine htup.sigma fun k => ?_
  have := finite_fiber f hf k
  have : Fintype {a : Fin g → ℕ // weight f a = k} := Fintype.ofFinite _
  have h := hasSum_fintype (fun c : {a : Fin g → ℕ // weight f a = k} => x ^ weight f c.1)
  have hval : (∑ c : {a : Fin g → ℕ // weight f a = k}, x ^ weight f c.1) =
      (Nat.card {a : Fin g → ℕ // weight f a = k} : ℂ) * x ^ k := by
    rw [Finset.sum_congr rfl fun c _ => by rw [c.2], Finset.sum_const, card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
  rw [hval] at h
  exact h

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Ring.HasFiniteQuotients S]

/-- **Local Euler factor for any residue-degree pattern:** if the primes above p are P₁,…,P_g with
N(Pᵢ) = p^{fᵢ}, then Σₖ #{I : N(I) = pᵏ} xᵏ = ∏ᵢ (1 − x^{fᵢ})⁻¹. No Galois hypothesis. -/
theorem localFactor_weighted {g : ℕ} {P : Fin g → Ideal S} {p : ℕ} {f : Fin g → ℕ}
    (hp : 1 < p) (hf : ∀ i, 0 < f i) (hP : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (habove : ∀ Q : Ideal S, Prime Q → Q ∣ Ideal.span {(p : S)} → ∃ i, Q = P i)
    (hnorm : ∀ i, Ideal.absNorm (P i) = p ^ f i) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ => (Nat.card {I : Ideal S // Ideal.absNorm I = p ^ k} : ℂ) * x ^ k)
      (∏ i, (1 - x ^ f i)⁻¹) := by
  simp only [card_ideals_norm_prime_pow_weighted hp hP hinj habove hnorm]
  exact hasSum_weighted f hf hx

end WeightedCount

#print axioms WeightedCount.hasSum_weighted
#print axioms WeightedCount.localFactor_weighted

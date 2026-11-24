import Q5Splitting

/-!
# Q5EulerProduct — Σ A(n) n⁻ˢ = ζ(s) · L(s, χ₋₂₀) for ℚ(√−5), Re s > 1

A thin instance of the generic `quad_LSeries_A_eq_zeta_mul_L` (degree 2 only; Galois derived).
The splitting hypothesis is `Q5.chi20C_eq_splitChar`. ℚ(√−5) has class number 2;
nothing here uses principal ideals or unique factorization of elements.
-/

open NumberField

theorem Q5.LSeries_A_eq_zeta_mul_L {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (IdealCount.A (𝓞 Q5.K5) n : ℂ)) s
      = riemannZeta s * LSeries (fun n => Q5.chi20C n) s :=
  quad_LSeries_A_eq_zeta_mul_L Q5.finrank_K5 Q5.chi20C Q5.chi20C_eq_splitChar hs

#print axioms Q5.LSeries_A_eq_zeta_mul_L

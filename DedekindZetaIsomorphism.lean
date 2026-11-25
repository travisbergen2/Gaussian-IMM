import DedekindIdealCountMultiplicative

/-!
# DedekindZetaIsomorphism — isomorphic fields have the same ideal counts and Dedekind series

Generic (independent of any quadratic or cyclotomic construction).
* `absNorm_comap`: for a ring isomorphism e : S ≃+* T and an ideal J of T, N(e⁻¹(J)) = N(J)
  (the quotients S ⧸ e⁻¹(J) and T ⧸ J are isomorphic);
* `A_eq_of_ringEquiv`: A_S(n) = A_T(n) for every n, through the bijection J ↦ e⁻¹(J) of ideals;
* `A_eq_of_equiv`: for number fields K ≃+* F (e.g. a ℚ-isomorphism), A_K(n) = A_F(n), via the
  induced 𝓞_K ≃+* 𝓞_F;
* `LSeries_eq_of_equiv`: Σ A_K(n) n⁻ˢ = Σ A_F(n) n⁻ˢ for every s (the coefficient sequences agree).
-/

open Ideal NumberField

namespace IdealCountIso

variable {S T : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
  [CommRing T] [IsDedekindDomain T] [Module.Free ℤ T] [Module.Finite ℤ T] [Infinite S] [Infinite T]

omit [Module.Free ℤ S] [Module.Finite ℤ S] [Module.Free ℤ T] [Module.Finite ℤ T] in
/-- **Norms are preserved:** N(e⁻¹ J) = N(J). -/
theorem absNorm_comap (e : S ≃+* T) (J : Ideal T) : absNorm (J.comap e) = absNorm J := by
  rw [absNorm_apply, absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (J.comap e) J e
    (Ideal.map_comap_of_surjective _ e.surjective J).symm).toEquiv

omit [Module.Free ℤ S] [Module.Finite ℤ S] [Module.Free ℤ T] [Module.Finite ℤ T] in
/-- **Ideal counts are preserved** by a ring isomorphism. -/
theorem A_eq_of_ringEquiv (e : S ≃+* T) (n : ℕ) : IdealCount.A S n = IdealCount.A T n := by
  rw [IdealCount.A, IdealCount.A]
  exact (Nat.card_congr (e.idealComapOrderIso.toEquiv.subtypeEquiv fun J => by
    show _ ↔ absNorm (J.comap e) = n
    rw [absNorm_comap])).symm

end IdealCountIso

namespace IdealCountIso

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]

/-- **A_K = A_F** for isomorphic number fields. -/
theorem A_eq_of_equiv (e : K ≃+* F) (n : ℕ) : IdealCount.A (𝓞 K) n = IdealCount.A (𝓞 F) n :=
  A_eq_of_ringEquiv (RingOfIntegers.mapRingEquiv e) n

/-- **ζ_K = ζ_F** as Dirichlet series, for every s. -/
theorem LSeries_eq_of_equiv (e : K ≃+* F) (s : ℂ) :
    LSeries (fun n => (IdealCount.A (𝓞 K) n : ℂ)) s =
      LSeries (fun n => (IdealCount.A (𝓞 F) n : ℂ)) s := by
  simp only [A_eq_of_equiv e]

end IdealCountIso

#print axioms IdealCountIso.absNorm_comap
#print axioms IdealCountIso.A_eq_of_ringEquiv
#print axioms IdealCountIso.LSeries_eq_of_equiv

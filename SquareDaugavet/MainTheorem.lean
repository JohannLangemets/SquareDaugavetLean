import SquareDaugavet.PositiveGlobal
import SquareDaugavet.NegativeSquarePoint

/-!
# The main theorem (Introduction)

It is assembled from Theorem 2.2, Corollary 2.7 and Corollary 2.4; no new argument is needed.
-/

namespace SquareDaugavet

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Main Theorem.** Let `X` be a real normed space with `dim X > 1`. The following are
equivalent:
(i) `X` has the Daugavet property;
(ii) `X` has the positive square Daugavet property;
(iii) `X` has the negative square Daugavet property.
In particular, every extremely non-complex space of dimension greater than one has the Daugavet
property. (The paper assumes `X` Banach; completeness is not needed.) -/
theorem main_theorem (hdim : 1 < Module.rank ℝ X) :
    List.TFAE
        [HasDaugavetProperty X, HasSquareDaugavetProperty X 1, HasSquareDaugavetProperty X (-1)] ∧
      (IsExtremelyNonComplex X → HasDaugavetProperty X) := by
  refine ⟨?_, hasDaugavetProperty_of_isExtremelyNonComplex hdim⟩
  -- (i) ⇔ (ii) is Theorem 2.2, (i) ⇔ (iii) is Corollary 2.7.
  tfae_have 1 ↔ 2 := (hasSquareDaugavetProperty_one_iff_hasDaugavetProperty hdim).symm
  tfae_have 1 ↔ 3 := hasSquareDaugavetProperty_neg_one_iff_hasDaugavetProperty.symm
  tfae_finish

end SquareDaugavet

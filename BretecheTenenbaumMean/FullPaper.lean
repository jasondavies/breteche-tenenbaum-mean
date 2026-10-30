module

public import BretecheTenenbaumMean.TheoremOne
public import BretecheTenenbaumMean.TheoremTwo
public import BretecheTenenbaumMean.PolynomialPrimeCosine
public import BretecheTenenbaumMean.PropositionTwoOne
public import BretecheTenenbaumMean.PropositionTwoOneLower
public import BretecheTenenbaumMean.PropositionTwoTwo
public import BretecheTenenbaumMean.LemmaThreeOne
public import BretecheTenenbaumMean.LemmaThreeOneCentral
public import BretecheTenenbaumMean.GlobalParseval

@[expose] public section

/-! # Completion certificate for the paper's named statements

The lower-tail statement uses the quantified range justified by §3;
`RangeCheck.not_uniform_lower_tail` disproves the unrestricted reading.
The exact Parseval identity is exported by `GlobalParseval`.
-/

namespace BretecheTenenbaumMean

/-- All named targets are proved, including the polynomial consequence (1.7).
There are no additional analytic hypotheses in this theorem. -/
theorem paper_main_results :
    TheoremOne ∧ TheoremTwo ∧ PolynomialMeanBound ∧
      PropositionTwoOneUpper ∧ PropositionTwoOneLower ∧ PropositionTwoTwo ∧
      LemmaThreeOne ∧ LemmaThreeOneCentral :=
  ⟨theoremOne, theoremTwo, polynomialMeanBound, propositionTwoOneUpper,
    propositionTwoOneLower, propositionTwoTwo, lemmaThreeOne, lemmaThreeOneCentral⟩

end BretecheTenenbaumMean

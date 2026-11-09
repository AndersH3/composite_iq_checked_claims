package Admission_Core with SPARK_Mode is
   --  Counts remain exact; no distributional assumption is used here.
   Max_Trials : constant := 100_000_000;
   subtype Count is Long_Long_Integer range 0 .. Max_Trials;
   Scale : constant := 1_000_000_000_000_000;
   subtype Probability_Units is Long_Long_Integer range 0 .. Scale;
   type Rational_Probability is record
      Numerator, Denominator : Probability_Units;
   end record;

   type Event is (Neither, A_Only, B_Only, Both);
   type Counts is record
      N00, N10, N01, N11 : Count := 0;
   end record;

   function Classify (Pass_A, Pass_B : Boolean) return Event with
     Global => null,
     --  Guarded cases retain the complete truth table and avoid a GNAT 13
     --  optimization failure for Boolean equality around Result comparisons.
     Post => (if not Pass_A and not Pass_B then Classify'Result = Neither) and then
       (if Pass_A and not Pass_B then Classify'Result = A_Only) and then
       (if not Pass_A and Pass_B then Classify'Result = B_Only) and then
       (if Pass_A and Pass_B then Classify'Result = Both),
     Depends => (Classify'Result => (Pass_A, Pass_B));

   function Total (C : Counts) return Long_Long_Integer is
     (C.N00 + C.N10 + C.N01 + C.N11) with
     --  These consequences detect a lost or double-counted event cell.
     --  They remain exact integer properties, not statistical estimates.
     Post => (Total'Result = C.N00 + C.N10 + C.N01 + C.N11) and then
       (Total'Result >= 0) and then
       (Total'Result <= 4 * Max_Trials) and then
       (Total'Result >= C.N00) and then
       (Total'Result >= C.N10) and then
       (Total'Result >= C.N01) and then
       (Total'Result >= C.N11) and then
       (if Total'Result = 0 then
          C.N00 = 0 and C.N10 = 0 and C.N01 = 0 and C.N11 = 0),
     Global => null,
     Depends => (Total'Result => C);

   procedure Observe (C : in out Counts; E : Event) with
     Global => null,
     Pre => Total (C) < Max_Trials,
     Post => Total (C) = Total (C'Old) + 1
       and C.N00 = C'Old.N00 + (if E = Neither then 1 else 0)
       and C.N10 = C'Old.N10 + (if E = A_Only then 1 else 0)
       and C.N01 = C'Old.N01 + (if E = B_Only then 1 else 0)
       and C.N11 = C'Old.N11 + (if E = Both then 1 else 0),
     Depends => (C => (C, E));

   function Marginal_A (C : Counts) return Count with
     Global => null,
     Pre => Total (C) <= Max_Trials,
     --  All nonnegative event-cell contributions remain visible,
     --  including both exact zero-cell and zero-marginal boundaries.
     Post => Marginal_A'Result = C.N10 + C.N11
       and Marginal_A'Result <= Total (C)
       and Marginal_A'Result >= C.N10
       and Marginal_A'Result >= C.N11
       and (if C.N10 = 0 then Marginal_A'Result = C.N11)
       and (if C.N11 = 0 then Marginal_A'Result = C.N10)
       and (if Marginal_A'Result = 0 then C.N10 = 0 and C.N11 = 0),
     Depends => (Marginal_A'Result => C);
   function Marginal_B (C : Counts) return Count with
     Global => null,
     Pre => Total (C) <= Max_Trials,
     --  The B marginal conserves each nonnegative contributor,
     --  including the two component-zero and total-zero edge cases.
     Post => Marginal_B'Result = C.N01 + C.N11
       and Marginal_B'Result <= Total (C)
       and Marginal_B'Result >= C.N01
       and Marginal_B'Result >= C.N11
       and (if C.N01 = 0 then Marginal_B'Result = C.N11)
       and (if C.N11 = 0 then Marginal_B'Result = C.N01)
       and (if Marginal_B'Result = 0 then C.N01 = 0 and C.N11 = 0),
     Depends => (Marginal_B'Result => C);
   function Union_Count (C : Counts) return Count with
     Global => null,
     Pre => Total (C) <= Max_Trials,
     --  Compare the union with each disjoint component and the
     --  complete count when the neither-cell is empty.
     Post => Union_Count'Result = C.N10 + C.N01 + C.N11
       and Union_Count'Result <= Total (C)
       and Union_Count'Result >= C.N11
       and Union_Count'Result >= C.N10
       and Union_Count'Result >= C.N01
       and Union_Count'Result >= C.N10 + C.N01
       and (if C.N00 = 0 then Union_Count'Result = Total (C)),
     Depends => (Union_Count'Result => C);

   function Fraction (Numerator, Denominator : Count) return Rational_Probability with
     Global => null,
     Pre => Denominator > 0 and Numerator <= Denominator,
     --  A rational receipt must retain the caller's positive
     --  denominator and exact zero/unit-probability boundary cases.
     Post => Fraction'Result.Numerator = Numerator
       and Fraction'Result.Denominator = Denominator
       and Fraction'Result.Numerator <= Fraction'Result.Denominator
       and Fraction'Result.Denominator > 0
       and (if Numerator = 0 then Fraction'Result.Numerator = 0)
       and (if Numerator = Denominator then
          Fraction'Result.Numerator = Fraction'Result.Denominator),
     Depends => (Fraction'Result => (Numerator, Denominator));

   function Union_Probability (P_A, P_B, Joint : Probability_Units)
     return Probability_Units with
     Global => null,
     Pre => Joint <= P_A and Joint <= P_B and P_A + P_B <= Scale,
     Post => Union_Probability'Result = P_A + P_B - Joint
       and Union_Probability'Result >= P_A
       and Union_Probability'Result >= P_B,
     Depends => (Union_Probability'Result => (P_A, P_B, Joint));

   function Complement (P : Probability_Units) return Probability_Units with
     Global => null,
     --  Preserve exact complement accounting also at the interior
     --  endpoints and on either side of probability one half.
     Post => (Complement'Result + P = Scale) and then
       (if P = 0 then Complement'Result = Scale) and then
       (if P = Scale then Complement'Result = 0) and then
       (Complement'Result = Scale - P) and then
       (if P > 0 then Complement'Result < Scale) and then
       (if P < Scale then Complement'Result > 0) and then
       (if P <= Scale / 2 then Complement'Result >= Scale / 2) and then
       (if P >= Scale / 2 then Complement'Result <= Scale / 2),
     Depends => (Complement'Result => P);

   function Conditional (Joint, Marginal : Probability_Units)
     return Rational_Probability with
     Global => null,
     Pre => Marginal > 0 and Joint <= Marginal,
     --  Conditioned ratios preserve positivity of the selected
     --  denominator and both exact zero and unit boundary cases.
     Post => Conditional'Result.Numerator = Joint
       and Conditional'Result.Denominator = Marginal
       and Conditional'Result.Numerator <= Conditional'Result.Denominator
       and Conditional'Result.Denominator > 0
       and (if Joint = 0 then Conditional'Result.Numerator = 0)
       and (if Joint = Marginal then
          Conditional'Result.Numerator = Conditional'Result.Denominator),
     Depends => (Conditional'Result => (Joint, Marginal));
end Admission_Core;

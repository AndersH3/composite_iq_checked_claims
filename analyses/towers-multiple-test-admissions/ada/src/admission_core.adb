package body Admission_Core with SPARK_Mode is
   function Classify (Pass_A, Pass_B : Boolean) return Event is
   begin
      if Pass_A then
         return (if Pass_B then Both else A_Only);
      else
         return (if Pass_B then B_Only else Neither);
      end if;
   end Classify;

   procedure Observe (C : in out Counts; E : Event) is
   begin
      case E is
         when Neither => C.N00 := C.N00 + 1;
         when A_Only  => C.N10 := C.N10 + 1;
         when B_Only  => C.N01 := C.N01 + 1;
         when Both    => C.N11 := C.N11 + 1;
      end case;
   end Observe;

   function Marginal_A (C : Counts) return Count is
     (C.N10 + C.N11);
   function Marginal_B (C : Counts) return Count is
     (C.N01 + C.N11);
   function Union_Count (C : Counts) return Count is
     (C.N10 + C.N01 + C.N11);
   function Fraction (Numerator, Denominator : Count) return Rational_Probability is
     ((Numerator => Numerator, Denominator => Denominator));
   function Union_Probability (P_A, P_B, Joint : Probability_Units)
     return Probability_Units is (P_A + P_B - Joint);
   function Complement (P : Probability_Units) return Probability_Units is
     (Scale - P);
   function Conditional (Joint, Marginal : Probability_Units)
     return Rational_Probability is
     ((Numerator => Joint, Denominator => Marginal));
end Admission_Core;

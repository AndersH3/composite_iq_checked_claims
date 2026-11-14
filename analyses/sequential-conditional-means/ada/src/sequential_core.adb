package body Sequential_Core with SPARK_Mode is
   function D_Numerator
     (N : Count; C : Correlation_Permille) return Long_Long_Integer
   is
   begin
      --  Integer units retain negative finite-battery eigenvalues during
      --  validation instead of rounding a nearly singular covariance.
      return Scale + Long_Long_Integer (C) * Long_Long_Integer (N - 1);
   end D_Numerator;

   function Calculate
     (R, K : Count; C : Correlation_Permille) return Formula_Values
   is
      --  These bounds express the distinct factors before they are combined.
      --  In addition to preventing arithmetic overflow they make the signs
      --  of the covariance-derived products available to every caller proof.
      subtype Nonnegative_Factor is Long_Long_Integer range 0 .. 2_000_000;
      subtype Nonnegative_Product is Long_Long_Integer range
        0 .. 2_000_000_000_000;
      RI : constant Long_Long_Integer := Long_Long_Integer (R);
      KI : constant Long_Long_Integer := Long_Long_Integer (K);
      CI : constant Long_Long_Integer := Long_Long_Integer (C);
      N  : constant Count := Count (R + K);
      NI : constant Long_Long_Integer := Long_Long_Integer (N);
      DR : constant Long_Long_Integer := D_Numerator (R, C);
      DN : constant Nonnegative_Factor := D_Numerator (N, C);
      Loss : constant Nonnegative_Factor := Scale - CI;
      Next_D : constant Nonnegative_Factor := DR + CI;
      Mean_Num : constant Nonnegative_Product := RI * DN;
      Conditional_Num : constant Nonnegative_Product := KI * Loss * DN;
      Residual_Num : constant Nonnegative_Product := Loss * Next_D;
      Result : Formula_Values :=
        (Prediction => (Num => RI * CI, Den => DR),
         Mean => (Num => Mean_Num, Den => NI * DR),
         Population_Variance => (Num => DN, Den => Scale * NI),
         Conditional_Variance =>
           (Num => Conditional_Num,
            Den => Scale * NI * NI * DR),
         Regression_Coefficient => (Num => CI, Den => DR),
         Residual_Variance =>
           (Num => Residual_Num, Den => Scale * DR),
         Common_Eigenvalue => (Num => DN, Den => Scale),
         Contrast_Eigenvalue => (Num => Scale - CI, Den => Scale),
         Has_Inverse => False,
         Inverse_Diagonal => (Num => 0, Den => 1),
         Inverse_Off_Diagonal => (Num => 0, Den => 1));
   begin
      --  For a 1x1 matrix there is no off-diagonal coordinate, and the
      --  covariance [1] is invertible even at perfect correlation.  Keeping
      --  this case explicit avoids evaluating the rank-one inverse formula
      --  with its vanishing (1-c) factor.
      if R = 1 then
         Result.Has_Inverse := True;
         Result.Inverse_Diagonal := (Num => 1, Den => 1);
      elsif C < 1_000 then
         Result.Has_Inverse := True;
         Result.Inverse_Diagonal :=
           (Num => Scale * (DR - CI), Den => (Scale - CI) * DR);
         Result.Inverse_Off_Diagonal :=
           (Num => -Scale * CI, Den => (Scale - CI) * DR);
      end if;
      return Result;
   end Calculate;

   function Limits
     (R : Count; C : Correlation_Permille) return Limit_Values
   is
      RI : constant Long_Long_Integer := Long_Long_Integer (R);
      CI : constant Long_Long_Integer := Long_Long_Integer (C);
      DR : constant Long_Long_Integer := D_Numerator (R, C);
   begin
      --  Only coefficient construction is performed here.  Convergence of
      --  the finite formulas is the mathematical limit proof in the paper;
      --  this body does not turn a finite loop into a proof about infinity.
      return
        (Prediction => (Num => RI * CI, Den => DR),
         Mean => (Num => RI * CI, Den => DR),
         Population_Variance => (Num => CI, Den => Scale),
         Conditional_Variance =>
           (Num => CI * (Scale - CI), Den => Scale * DR));
   end Limits;
end Sequential_Core;

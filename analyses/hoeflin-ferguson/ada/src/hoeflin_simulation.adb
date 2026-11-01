with Hoeflin_Core;
with Normal_Support;
with Report_IO;
with Interfaces;
procedure Hoeflin_Simulation with SPARK_Mode is
   use Hoeflin_Core;
   Counts : constant array (Positive range <>) of Test_Count :=
     (1, 2, 3, 4, 5, 10, 100, 1_000);
   Trials : Sample_Count;
   Seed : Interfaces.Unsigned_64;
   Q : constant Normal_Support.Rare_Value := Normal_Support.Rare_Quantile;
   Expected_Two : constant Normal_Support.Probability := Normal_Support.Survival (2.0);
   Expected_Three : constant Normal_Support.Probability := Normal_Support.Survival (3.0);
   G : Normal_Support.Generator;
   Common : constant Normal_Support.Unit_Root := Normal_Support.Square_Root (0.6);
   X, Y : Normal_Support.Normal_Value;
   subtype Mean_Score is Real range -18.0 .. 18.0;
   subtype Sample_Z is Real range -40_000.0 .. 40_000.0;
   function Combine
     (Common, Residual : Normal_Support.Unit_Root;
      X, Y : Normal_Support.Normal_Value; Scale : Scale_Value) return Sample_Z
     with Global => null
   is
      Mean_Z : constant Mean_Score := Common * X + Residual * Y;
   begin
      return Mean_Z / Scale;
   end Combine;
   function Frequency (Numerator, Denominator : Sample_Count) return Normal_Support.Probability
   is (Real (Numerator) / Real (Denominator))
     with Global => null, Pre => Denominator > 0 and then Numerator <= Denominator;
   --  Conservative per-sample budgets leave room for binary64 rounding:
   --  |Z| <= 40,000 and Z*Z <= 1.6e9. This ghost lemma is proved, not assumed.
   procedure Count_Step (I : Sample_Count)
     with Ghost, Global => null, Pre => I > 0,
     Post => Real (I) = Real (I - 1) + 1.0
       and then Real (I) * 65_536.0 >= Real (I - 1) * 65_536.0 + 60_000.0
       and then Real (I) * 2.0 ** 32 >= Real (I - 1) * 2.0 ** 32 + 2.0 ** 31;
   procedure Count_Step (I : Sample_Count) is
   begin
      pragma Assert (Real (I) = Real (I - 1) + 1.0);
   end Count_Step;
   procedure Add_To_Sum (I : Sample_Count; Sample : Sample_Z; Running_Total : in out Real)
     with Global => null,
     Pre => I > 0 and then Running_Total in
       -(Real (I - 1) * 65_536.0) .. Real (I - 1) * 65_536.0,
     Post => Running_Total in -(Real (I) * 65_536.0) .. Real (I) * 65_536.0;
   procedure Add_To_Sum (I : Sample_Count; Sample : Sample_Z; Running_Total : in out Real) is
   begin
      Count_Step (I);
      Running_Total := Running_Total + Sample;
   end Add_To_Sum;
   Z : Sample_Z;
   Sum, Sum_Squares, Mean, Variance : Real;
   C : Tail_Counts;
   Scale : Scale_Value;
   Residual : Normal_Support.Unit_Root;
begin
   Report_IO.Read_Simulation_Options (Trials, Seed);
   Report_IO.Simulation_Header (Seed);
   for N of Counts loop
      Normal_Support.Reset (G, Seed);
      C := (others => 0); Sum := 0.0; Sum_Squares := 0.0;
      Scale := Normal_Support.Square_Root (Variance_Factor (N, 600));
      Residual := Normal_Support.Square_Root (0.4 / Real (N));
      for I in 1 .. Trials loop
         pragma Loop_Invariant (Valid (C) and then C.Total = I - 1);
         pragma Loop_Invariant (Sum in -(Real (I - 1) * 65_536.0) .. Real (I - 1) * 65_536.0);
         pragma Loop_Invariant (Sum in -1.0E14 .. 1.0E14);
         pragma Loop_Invariant (Sum_Squares in 0.0 .. Real (I - 1) * 2.0 ** 32);
         pragma Loop_Invariant (Sum_Squares in 0.0 .. 1.0E18);
         Count_Step (I);
         Normal_Support.Normal_Pair (G, X, Y);
         --  The mean of N independent Gaussian residuals is Gaussian, so
         --  this is the same distribution as explicitly averaging N tests.
         Z := Combine (Common, Residual, X, Y, Scale);
         Observe (C, Z, Q);
         Add_To_Sum (I, Z, Sum);
         Sum_Squares := Sum_Squares + Z * Z;
      end loop;
      Mean := Sum / Real (Trials);
      Variance := (Sum_Squares - Sum * Mean) / Real (Trials - 1);
      Report_IO.Simulation_Row
        (N, Trials, Mean, Variance, C, Frequency (C.Above_Two, Trials),
         Frequency (C.Above_Three, Trials), Expected_Two, Expected_Three);
   end loop;
end Hoeflin_Simulation;

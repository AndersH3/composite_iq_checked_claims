--  Trusted command-line / CSV boundary for the separately proved SPARK core.
--
--  This one procedure deliberately keeps filesystem effects, command-line
--  parsing, diagnostic matrix loops and serialization outside SPARK.  It does
--  not manufacture contracts that would purport to prove physical I/O.  Every
--  formula comes from Sequential_Core; every stochastic draw comes from the
--  contracted Sequential_Sampling package.  NumPy/Fraction independently
--  validate the files written here.  Build with assertions and overflow checks.
with Ada.Command_Line;
with Ada.Text_IO;
with Interfaces;
with Shared_Normal_Sampling;
with Sequential_Core;
with Sequential_Experiments;
with Sequential_Sampling;
procedure Sequential_Run with SPARK_Mode => Off is
   use Sequential_Core;
   use type Interfaces.Unsigned_64;
   package IO renames Ada.Text_IO;
   package E renames Sequential_Experiments;
   package S renames Sequential_Sampling;
   type Case_Value is record
      R, K : Count;
      C : Correlation_Permille;
      A : Long_Float;
   end record;
   --  The nine IQ rows, the earlier a=2 illustrations, independent/perfect
   --  correlation, negative definite-interior and singular PSD endpoints.
   Cases : constant array (Positive range <>) of Case_Value :=
     ((1, 1, 600, 10.0 / 3.0), (1, 2, 600, 10.0 / 3.0),
      (1, 10, 600, 10.0 / 3.0), (2, 1, 600, 10.0 / 3.0),
      (2, 2, 600, 10.0 / 3.0), (2, 10, 600, 10.0 / 3.0),
      (3, 1, 600, 10.0 / 3.0), (3, 2, 600, 10.0 / 3.0),
      (3, 10, 600, 10.0 / 3.0),
      (1, 3, 600, 2.0), (2, 3, 600, 2.0), (3, 3, 600, 2.0),
      (1, 2, 0, 10.0 / 3.0), (3, 10, 0, 10.0 / 3.0),
      (1, 2, 1000, 10.0 / 3.0), (3, 10, 1000, 10.0 / 3.0),
      (2, 2, -250, 2.0), (1, 1, -1000, 2.0),
      (1, 2, -500, 2.0), (3, 2, -250, 2.0));
   Trials : Positive range 2 .. 1_000_000 := 200_000;
   Seed : constant Interfaces.Unsigned_64 := 20_261_114;
   G : Shared_Normal_Sampling.Generator;
   Calculation_File, Simulation_File, Check_File : IO.File_Type;
   F : Formula_Values;
   Moments : E.Moment_Values;
   Acc : E.Accumulator;
   Empirical : E.Empirical_Values;
   L : Limit_Values;
   A, Prediction, Mean, Population_Var, Conditional_Var : Long_Float;
   Location, Sigma : Long_Float;
   Sample : S.Sample_Value;
   Sum, Sample_Mean, Sample_Variance : Long_Float;
   Mode_Name : String (1 .. 17);
   Mode_Length : Positive;
   Row_Seed : Interfaces.Unsigned_64 := Seed;
   --  Diagnostic workspaces.  These checks use matrix multiplication and the
   --  original recursion rather than just printing the closed formula twice.
   Running_Sum, Next_Prediction, Residual, Matrix_Value, Inverse_Entry : Long_Float;
   Product, Target, Common_Error, Contrast_Error : Long_Float;
   DR, DN, NN, KK, RR, Growth_Direct, Growth_Identity : Long_Float;
   X : array (1 .. 3) of Long_Float;
   W : constant array (1 .. 3) of Long_Float := (0.25, 0.5, 0.25);
   Y, EX, EX2, EY, EY2, EXY : Long_Float := 0.0;
begin
   --  One optional argument controls the sample count; results are written in
   --  the current directory so the caller chooses the destination explicitly.
   if Ada.Command_Line.Argument_Count > 1 then
      raise Constraint_Error with "usage: sequential_run [trials: 2..1000000]";
   elsif Ada.Command_Line.Argument_Count = 1 then
      Trials := Positive'Value (Ada.Command_Line.Argument (1));
   end if;
   IO.Create (Calculation_File, IO.Out_File, "calculation.csv");
   IO.Create (Simulation_File, IO.Out_File, "simulation.csv");
   IO.Create (Check_File, IO.Out_File, "checks.csv");
   IO.Put_Line (Calculation_File,
     "r,k,c,a_z,prediction_z,mean_z,population_variance,conditional_variance," &
     "prediction_limit_z,mean_limit_z,population_variance_limit,conditional_variance_limit," &
     "prediction_iq,mean_iq,population_sd_iq,conditional_sd_iq," &
     "regression_coefficient,residual_variance,common_eigenvalue,contrast_eigenvalue," &
     "has_inverse,inverse_diagonal,inverse_off_diagonal");
   IO.Put_Line (Simulation_File,
     "mode,r,k,c,a_z,trials,seed,sample_mean_z,sample_variance_z");
   IO.Put_Line (Check_File, "name,actual,expected,tolerance");

   for Case_Index in Cases'Range loop
      declare
         V : constant Case_Value := Cases (Case_Index);
      begin
         F := Calculate (V.R, V.K, V.C);
         A := V.A;
         Moments := E.From_Coefficients (F, A);
         Prediction := Moments.Prediction;
         Mean := Moments.Mean;
         Population_Var := Moments.Population_Variance;
         Conditional_Var := Moments.Conditional_Variance;
         IO.Put (Calculation_File,
           Count'Image (V.R) & "," & Count'Image (V.K) & "," &
           Long_Float'Image (Long_Float (V.C) / 1_000.0) & "," &
           Long_Float'Image (A) & "," & Long_Float'Image (Prediction) & "," &
           Long_Float'Image (Mean) & "," & Long_Float'Image (Population_Var) & "," &
           Long_Float'Image (Conditional_Var) & ",");
         if V.C >= 0 then
            L := Limits (V.R, V.C);
            IO.Put (Calculation_File,
              Long_Float'Image (E.Value (L.Prediction) * A) & "," &
              Long_Float'Image (E.Value (L.Mean) * A) & "," &
              Long_Float'Image (E.Value (L.Population_Variance)) & "," &
              Long_Float'Image (E.Value (L.Conditional_Variance)));
         else
            --  Four blank limit fields: fixed negative c has no infinite-k
            --  admissible covariance sequence, rather than a missing result.
            IO.Put (Calculation_File, ",,,");
         end if;
         IO.Put_Line (Calculation_File,
           "," & Long_Float'Image (100.0 + 15.0 * Prediction) & "," &
           Long_Float'Image (100.0 + 15.0 * Mean) & "," &
           Long_Float'Image (15.0 * S.Checked_Sqrt (Population_Var)) & "," &
           Long_Float'Image (15.0 * S.Checked_Sqrt (Conditional_Var)) & "," &
           Long_Float'Image (E.Value (F.Regression_Coefficient)) & "," &
           Long_Float'Image (E.Value (F.Residual_Variance)) & "," &
           Long_Float'Image (E.Value (F.Common_Eigenvalue)) & "," &
           Long_Float'Image (E.Value (F.Contrast_Eigenvalue)) & "," &
           Boolean'Image (F.Has_Inverse) & "," &
           Long_Float'Image (E.Value (F.Inverse_Diagonal)) & "," &
           Long_Float'Image (E.Value (F.Inverse_Off_Diagonal)));

         for Mode in 1 .. 2 loop
            if Mode = 1 then
               Mode_Name := "population       "; Mode_Length := 10;
               Location := 0.0; Sigma := S.Checked_Sqrt (Population_Var);
            else
               Mode_Name := "conditional      "; Mode_Length := 11;
               Location := Mean; Sigma := S.Checked_Sqrt (Conditional_Var);
            end if;
            Row_Seed := Row_Seed + 1;
            Shared_Normal_Sampling.Reset (G, Row_Seed);
            E.Reset (Acc);
            --  Sampling the proved scalar Gaussian mean law is constant-cost
            --  in k, and handles negative-c and singular finite batteries.
            --  The independent block-matrix validator checks the variance.
            for Trial in 1 .. Trials loop
               S.Draw (G, Location, Sigma, Sample);
               E.Add (Acc, Sample);
            end loop;
            Empirical := E.Finish (Acc);
            Sample_Mean := Empirical.Mean;
            Sample_Variance := Empirical.Unbiased_Variance;
            IO.Put_Line (Simulation_File,
              Mode_Name (1 .. Mode_Length) & "," & Count'Image (V.R) & "," &
              Count'Image (V.K) & "," &
              Long_Float'Image (Long_Float (V.C) / 1_000.0) & "," &
              Long_Float'Image (A) & "," & Positive'Image (Trials) & "," &
              Interfaces.Unsigned_64'Image (Row_Seed) & "," &
              Long_Float'Image (Sample_Mean) & "," & Long_Float'Image (Sample_Variance));
         end loop;
      end;
   end loop;

   --  The infinite-k laws have finite exact moments; sample those limiting
   --  distributions directly, rather than pretending a finite k is infinity.
   for R in Count range 1 .. 3 loop
      L := Limits (R, 600);
      for Mode in 1 .. 2 loop
         if Mode = 1 then
            Mode_Name := "population_limit "; Mode_Length := 16;
            Location := 0.0; Sigma := S.Checked_Sqrt (E.Value (L.Population_Variance));
         else
            Mode_Name := "conditional_limit"; Mode_Length := 17;
            Location := E.Value (L.Mean) * (10.0 / 3.0);
            Sigma := S.Checked_Sqrt (E.Value (L.Conditional_Variance));
         end if;
         Row_Seed := Row_Seed + 1;
         Shared_Normal_Sampling.Reset (G, Row_Seed);
         E.Reset (Acc);
         for Trial in 1 .. Trials loop
            S.Draw (G, Location, Sigma, Sample);
            E.Add (Acc, Sample);
         end loop;
         Empirical := E.Finish (Acc);
         Sample_Mean := Empirical.Mean;
         Sample_Variance := Empirical.Unbiased_Variance;
         IO.Put_Line (Simulation_File,
           Mode_Name (1 .. Mode_Length) & "," & Count'Image (R) & ",0,0.6," &
           Long_Float'Image (10.0 / 3.0) & "," & Positive'Image (Trials) & "," &
           Interfaces.Unsigned_64'Image (Row_Seed) & "," &
           Long_Float'Image (Sample_Mean) & "," & Long_Float'Image (Sample_Variance));
      end loop;
   end loop;

   for R in Count range 1 .. 3 loop
      F := Calculate (R, 10, 600);
      Running_Sum := Long_Float (R) * (10.0 / 3.0);
      Residual := 0.0;
      for J in 1 .. 10 loop
         Next_Prediction := 0.6 * Running_Sum /
           (1.0 + Long_Float (R + J - 2) * 0.6);
         Residual := Long_Float'Max
           (Residual, abs (Next_Prediction - E.Value (F.Prediction) * (10.0 / 3.0)));
         Running_Sum := Running_Sum + Next_Prediction;
      end loop;
      IO.Put_Line (Check_File, "prediction_recursion_r" &
        Character'Val (Character'Pos ('0') + R) & "," &
        Long_Float'Image (Residual) & ",0,1e-11");
      Residual := 0.0;
      for I in 1 .. R loop
         for J in 1 .. R loop
            Product := 0.0;
            for T in 1 .. R loop
               Matrix_Value := (if I = T then 1.0 else 0.6);
               Inverse_Entry := E.Value
                 ((if T = J then F.Inverse_Diagonal else F.Inverse_Off_Diagonal));
               Product := Product + Matrix_Value * Inverse_Entry;
            end loop;
            Target := (if I = J then 1.0 else 0.0);
            Residual := Long_Float'Max (Residual, abs (Product - Target));
         end loop;
      end loop;
      IO.Put_Line (Check_File, "inverse_identity_r" &
        Character'Val (Character'Pos ('0') + R) & "," &
        Long_Float'Image (Residual) & ",0,1e-11");
   end loop;
   F := Calculate (3, 10, 600);
   Common_Error := 0.0; Contrast_Error := 0.0;
   for I in 1 .. 13 loop
      Sum := 0.0;
      for J in 1 .. 13 loop
         Sum := Sum + (if I = J then 1.0 else 0.6);
      end loop;
      Common_Error := Long_Float'Max
        (Common_Error, abs (Sum - E.Value (F.Common_Eigenvalue)));
      Product := (if I = 1 then 1.0 else 0.6) -
        (if I = 2 then 1.0 else 0.6);
      Target := (if I = 1 then E.Value (F.Contrast_Eigenvalue)
                 elsif I = 2 then -E.Value (F.Contrast_Eigenvalue) else 0.0);
      Contrast_Error := Long_Float'Max (Contrast_Error, abs (Product - Target));
   end loop;
   IO.Put_Line (Check_File, "covariance_eigen_common," &
     Long_Float'Image (Common_Error) & ",0,1e-11");
   IO.Put_Line (Check_File, "covariance_eigen_contrast," &
     Long_Float'Image (Contrast_Error) & ",0,1e-11");

   --  Recompute the new variance decomposition and finite-difference
   --  identity, independently of the scalar sampling implementation.
   Common_Error := 0.0; Contrast_Error := 0.0;
   for R in Count range 1 .. 3 loop
      for K in Count range 1 .. 10 loop
         F := Calculate (R, K, 600);
         RR := Long_Float (R); KK := Long_Float (K); NN := RR + KK;
         DR := 1.0 + (RR - 1.0) * 0.6; DN := 1.0 + (NN - 1.0) * 0.6;
         Product := RR * DN * DN / (NN * NN * DR) +
           E.Value (F.Conditional_Variance);
         Common_Error := Long_Float'Max
           (Common_Error, abs (Product - E.Value (F.Population_Variance)));
         Growth_Direct := (KK + 1.0) * (DR + 0.6 * (KK + 1.0)) /
           ((NN + 1.0) * (NN + 1.0)) - KK * (DR + 0.6 * KK) / (NN * NN);
         Growth_Identity := ((1.2 * RR - DR) * KK * KK +
           (1.2 * RR * RR + 1.2 * RR - DR) * KK + RR * RR * (0.6 + DR)) /
           (NN * NN * (NN + 1.0) * (NN + 1.0));
         Contrast_Error := Long_Float'Max
           (Contrast_Error, abs (Growth_Direct - Growth_Identity));
      end loop;
   end loop;
   IO.Put_Line (Check_File, "total_variance_decomposition," &
     Long_Float'Image (Common_Error) & ",0,1e-11");
   IO.Put_Line (Check_File, "conditional_growth_identity," &
     Long_Float'Image (Contrast_Error) & ",0,1e-11");

   --  The paper's non-Gaussian three-atom PMF, evaluated by a weighted sum.
   --  Conditioning on X0=0 is an event of mass 1/2, not a null-event choice.
   X := (-S.Checked_Sqrt (2.0), 0.0, S.Checked_Sqrt (2.0));
   for I in X'Range loop
      Y := X (I) * X (I) - 1.0;
      EX := EX + W (I) * X (I); EX2 := EX2 + W (I) * X (I) * X (I);
      EY := EY + W (I) * Y; EY2 := EY2 + W (I) * Y * Y;
      EXY := EXY + W (I) * X (I) * Y;
   end loop;
   IO.Put_Line (Check_File, "counterexample_mean_x0," & Long_Float'Image (EX) & ",0,1e-11");
   IO.Put_Line (Check_File, "counterexample_variance_x0," & Long_Float'Image (EX2 - EX * EX) & ",1,1e-11");
   IO.Put_Line (Check_File, "counterexample_mean_x1," & Long_Float'Image (EY) & ",0,1e-11");
   IO.Put_Line (Check_File, "counterexample_variance_x1," & Long_Float'Image (EY2 - EY * EY) & ",1,1e-11");
   IO.Put_Line (Check_File, "counterexample_covariance," & Long_Float'Image (EXY - EX * EY) & ",0,1e-11");
   Y := X (2) * X (2) - 1.0;
   IO.Put_Line (Check_File, "counterexample_conditional," & Long_Float'Image (Y) & ",-1,1e-11");
   IO.Put_Line (Check_File, "counterexample_inclusive_mean," & Long_Float'Image ((X (2) + Y) / 2.0) & ",-.5,1e-11");
   IO.Put_Line (Check_File, "counterexample_independent_conditional," & Long_Float'Image (EY) & ",0,1e-11");
   IO.Close (Calculation_File); IO.Close (Simulation_File); IO.Close (Check_File);
end Sequential_Run;

with Ada.Command_Line;
with Ada.Directories;
with Ada.Numerics.Long_Elementary_Functions;
with Ada.Strings.Fixed;
with Ada.Text_IO;
with Admission_Core;
with Normal_Model;

procedure Towers_Demo with SPARK_Mode => Off is
   use Ada.Text_IO;
   use Admission_Core;
   use Ada.Numerics.Long_Elementary_Functions;
   package Real_IO is new Ada.Text_IO.Float_IO (Long_Float);
   function F (X : Long_Float) return String is
      S : String (1 .. 42);
   begin
      Real_IO.Put (S, X, Aft => 17, Exp => 3);
      return Ada.Strings.Fixed.Trim (S, Ada.Strings.Both);
   end F;
   function N (X : Long_Long_Integer) return String is
     (Ada.Strings.Fixed.Trim (X'Image, Ada.Strings.Both));

   Trials : Admission_Core.Count := 1_000_000;
   Seed : Positive := 20_261_030;
   Rho : constant Long_Float := 0.7;
   Names : constant array (1 .. 4) of access constant String :=
     (new String'("equal_top_2_percent"), new String'("equal_top_0_1_percent"),
      new String'("equal_top_1_in_33000"), new String'("mixed_top_2_and_0_1_percent"));
   PA : constant array (1 .. 4) of Long_Float := (0.02, 0.001, 1.0 / 33_000.0, 0.02);
   PB : constant array (1 .. 4) of Long_Float := (0.02, 0.001, 1.0 / 33_000.0, 0.001);
   A, B : array (1 .. 4) of Long_Float;
   Tallies : array (1 .. 4) of Counts;
   G : Normal_Model.Generator;
   Calc, Grid, Sim, Calibration : File_Type;
   J, J_Coarse, U, Phi, X, E, Y : Long_Float;
   Grid_Values : Normal_Model.Grid_Results;
   Cuts : constant array (1 .. 3) of Long_Float := (133.0, 150.0, 164.0);
   C : Counts;
   MA, MB, UC : Admission_Core.Count;

   --  Floating conversion is an explicitly checked numerical boundary.
   function Units (P : Long_Float) return Probability_Units is
      Q : Probability_Units;
   begin
      if P < 0.0 or else P > 1.0 then
         raise Constraint_Error with "probability outside [0,1]";
      end if;
      Q := Probability_Units (P * Long_Float (Scale));
      if abs (Long_Float (Q) / Long_Float (Scale) - P) > 0.51E-15 then
         raise Constraint_Error with "probability quantization bound exceeded";
      end if;
      return Q;
   end Units;

   function Value (P : Rational_Probability) return Long_Float is
   begin
      if P.Denominator = 0 or else P.Numerator > P.Denominator then
         raise Constraint_Error with "invalid rational probability";
      end if;
      return Long_Float (P.Numerator) / Long_Float (P.Denominator);
   end Value;

   function Conditional_Value (Joint, Marginal : Long_Float) return Long_Float is
     (Value (Conditional (Units (Joint), Units (Marginal))));

   function Conditional_Count (Joint, Marginal : Admission_Core.Count) return String is
   begin
      if Marginal = 0 then return "NA"; end if;
      return F (Value (Fraction (Joint, Marginal)));
   end Conditional_Count;

   procedure Wilson (Successes, Denominator : Admission_Core.Count; Lo, Hi : out Long_Float) is
      Z : constant Long_Float := 1.959963984540054;
      NN : constant Long_Float := Long_Float (Denominator);
      P : constant Long_Float := Value (Fraction (Successes, Denominator));
      D : constant Long_Float := 1.0 + Z * Z / NN;
      Centre : constant Long_Float := (P + Z * Z / (2.0 * NN)) / D;
      Half : constant Long_Float := Z * Sqrt (P * (1.0 - P) / NN + Z * Z / (4.0 * NN * NN)) / D;
   begin
      Lo := Long_Float'Max (0.0, Centre - Half);
      Hi := Long_Float'Min (1.0, Centre + Half);
   end Wilson;

   procedure Run (Directory : String) is
      Lower, Upper, Q, Cont_P, Cont_J : Long_Float;
   begin
      Ada.Directories.Create_Path (Directory);
      Create (Calc, Out_File, Directory & "/calculation.csv");
      Put_Line (Calc, "case,rho,cutoff_a_z,cutoff_b_z,p_a,p_b,joint,union,conditional_b_given_a,conditional_a_given_b,phi,joint_refinement_delta,raw_union,raw_conditional_b_given_a,raw_conditional_a_given_b,complement_a_units");
      for K in A'Range loop
         A (K) := Normal_Model.Inverse_SF (PA (K));
         B (K) := Normal_Model.Inverse_SF (PB (K));
         J := Normal_Model.Joint_Tail (A (K), B (K), Rho);
         J_Coarse := Normal_Model.Joint_Tail (A (K), B (K), Rho, 10_000);
         pragma Assert (J >= 0.0 and J <= PA (K) and J <= PB (K));
         U := Long_Float (Union_Probability (Units (PA (K)), Units (PB (K)), Units (J))) / Long_Float (Scale);
         Phi := (J - PA (K) * PB (K))
           / Sqrt (PA (K) * (1.0 - PA (K)) * PB (K) * (1.0 - PB (K)));
         Put_Line (Calc, Names (K).all & "," & F (Rho) & "," & F (A (K)) & "," & F (B (K))
           & "," & F (PA (K)) & "," & F (PB (K)) & "," & F (J) & "," & F (U)
           & "," & F (Conditional_Value (J, PA (K))) & "," & F (Conditional_Value (J, PB (K)))
           & "," & F (Phi) & "," & F (abs (J - J_Coarse))
           & "," & F (PA (K) + PB (K) - J) & "," & F (J / PA (K))
           & "," & F (J / PB (K)) & "," & N (Complement (Units (PA (K)))));
      end loop;
      Close (Calc);

      Grid_Values := Normal_Model.Basic_Grid;
      Create (Grid, Out_File, Directory & "/grid.csv");
      Put_Line (Grid, "cutoff_iq,marginal_continuous,joint_continuous,conditional_continuous,grid_joint,grid_marginal,grid_conditional");
      for K in Cuts'Range loop
         Q := (Cuts (K) - 100.0) / 16.0;
         Cont_P := Normal_Model.SF (Q);
         Cont_J := Normal_Model.Joint_Tail (Q, Q, Rho);
         Put_Line (Grid, F (Cuts (K)) & "," & F (Cont_P) & "," & F (Cont_J)
           & "," & F (Conditional_Value (Cont_J, Cont_P))
           & "," & F (Grid_Values (K).Joint) & "," & F (Grid_Values (K).Marginal)
           & "," & F (Conditional_Value (Grid_Values (K).Joint, Grid_Values (K).Marginal)));
      end loop;
      Close (Grid);

      Q := Normal_Model.Calibrated_OR_Cutoff (0.02, Rho);
      U := Long_Float (Union_Probability (Units (Normal_Model.SF (Q)), Units (Normal_Model.SF (Q)),
                            Units (Normal_Model.Joint_Tail (Q, Q, Rho)))) / Long_Float (Scale);
      Create (Calibration, Out_File, Directory & "/calibration.csv");
      Put_Line (Calibration, "rho,target_union,cutoff_z,cutoff_iq_sd16,marginal,actual_union");
      Put_Line (Calibration, F (Rho) & "," & F (0.02) & "," & F (Q) & ","
        & F (100.0 + 16.0 * Q) & "," & F (Normal_Model.SF (Q)) & "," & F (U));
      Close (Calibration);

      Normal_Model.Reset (G, Seed);
      for Iteration in 1 .. Trials loop
         Normal_Model.Normal_Pair (G, X, E);
         Y := Rho * X + Sqrt (1.0 - Rho * Rho) * E;
         for K in Tallies'Range loop
            Observe (Tallies (K), Classify (X > A (K), Y > B (K)));
         end loop;
      end loop;
      Create (Sim, Out_File, Directory & "/simulation.csv");
      Put_Line (Sim, "case,trials,seed,neither,a_only,b_only,both,marginal_a,marginal_b,union,joint_fraction,conditional_b_given_a,conditional_a_given_b,joint_wilson_lower,joint_wilson_upper");
      for K in Tallies'Range loop
         C := Tallies (K);
         pragma Assert (Total (C) = Trials);
         MA := Marginal_A (C); MB := Marginal_B (C); UC := Union_Count (C);
         Wilson (C.N11, Trials, Lower, Upper);
         Put_Line (Sim, Names (K).all & "," & N (Trials) & "," & N (Long_Long_Integer (Seed))
           & "," & N (C.N00) & "," & N (C.N10) & "," & N (C.N01) & "," & N (C.N11)
           & "," & N (MA) & "," & N (MB) & "," & N (UC)
           & "," & F (Value (Fraction (C.N11, Trials)))
           & "," & Conditional_Count (C.N11, MA) & "," & Conditional_Count (C.N11, MB)
           & "," & F (Lower) & "," & F (Upper));
      end loop;
      Close (Sim);
      Put_Line ("Wrote calculations, BASIC-grid reproduction, calibration and simulation to " & Directory);
      Put_Line ("Simulation seed=" & Seed'Image & "; trials=" & Trials'Image);
   end Run;
begin
   if Ada.Command_Line.Argument_Count > 0 then
      Trials := Admission_Core.Count'Value (Ada.Command_Line.Argument (1));
   end if;
   if Trials = 0 then raise Constraint_Error with "trials must be positive"; end if;
   if Ada.Command_Line.Argument_Count > 1 then
      Seed := Positive'Value (Ada.Command_Line.Argument (2));
   end if;
   if Ada.Command_Line.Argument_Count > 2 then
      Run (Ada.Command_Line.Argument (3));
   else
      Run ("results");
   end if;
end Towers_Demo;

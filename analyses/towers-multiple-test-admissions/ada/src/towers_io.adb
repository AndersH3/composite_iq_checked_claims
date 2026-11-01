with Towers_IO_Models;
with Ada.Command_Line;
with Ada.Directories;
with Ada.Strings.Fixed;
with Ada.Text_IO;
with Admission_Core;
package body Towers_IO with SPARK_Mode => Off is
   use Ada.Text_IO;
   use Admission_Core;
   use Towers_Engine;
   package Real_IO is new Ada.Text_IO.Float_IO (Long_Float);
   function F (X : Long_Float) return String is
      S : String (1 .. 42);
   begin
      Real_IO.Put (S, X, Aft => 17, Exp => 3);
      declare
         Result : constant String := Ada.Strings.Fixed.Trim (S, Ada.Strings.Both);
      begin
         Towers_IO_Models.Check_Real_Field (Result);
         return Result;
      end;
   end F;
   function N (X : Long_Long_Integer) return String is
      Result : constant String := Ada.Strings.Fixed.Trim (X'Image, Ada.Strings.Both);
   begin
      Towers_IO_Models.Check_Integer_Field (Result);
      return Result;
   end N;
   function Name (K : Case_Index) return String is
   begin
      case K is
         when 1 =>
            Towers_IO_Models.Check_Case_Name (K, "equal_top_2_percent");
            return "equal_top_2_percent";
         when 2 =>
            Towers_IO_Models.Check_Case_Name (K, "equal_top_0_1_percent");
            return "equal_top_0_1_percent";
         when 3 =>
            Towers_IO_Models.Check_Case_Name (K, "equal_top_1_in_33000");
            return "equal_top_1_in_33000";
         when 4 =>
            Towers_IO_Models.Check_Case_Name (K, "mixed_top_2_and_0_1_percent");
            return "mixed_top_2_and_0_1_percent";
      end case;
   end Name;
   function Read_Trials return Trial_Count is
   begin
      if Ada.Command_Line.Argument_Count > 0 then
         declare
            Text : constant String := Ada.Command_Line.Argument (1);
            Actual : constant Trial_Count := Trial_Count'Value (Text);
         begin
            Towers_IO_Models.Observe_Option (Text, Actual, Admission_Core.Max_Trials);
            Towers_IO_Models.Check_Trials (Actual);
            return Actual;
         end;
      end if;
      Towers_IO_Models.Check_Trials (1_000_000);
      return 1_000_000;
   end Read_Trials;
   function Read_Seed return Seed_Value is
   begin
      if Ada.Command_Line.Argument_Count > 1 then
         declare
            Text : constant String := Ada.Command_Line.Argument (2);
            Actual : constant Seed_Value := Seed_Value'Value (Text);
         begin
            Towers_IO_Models.Observe_Option (Text, Long_Long_Integer (Actual), 2_147_483_646);
            Towers_IO_Models.Check_Seed (Long_Long_Integer (Actual));
            return Actual;
         end;
      end if;
      Towers_IO_Models.Check_Seed (20_261_030);
      return 20_261_030;
   end Read_Seed;
   procedure Write_Report (Trials : Trial_Count; Seed : Seed_Value; Data : Results) is
      procedure Run (Directory : String) is
         Calc, Grid, Sim, Calibration : File_Type;
         C : Counts;
      begin
         Towers_IO_Models.Check_Report (Trials, Long_Long_Integer (Seed), Data);
         Ada.Directories.Create_Path (Directory);
         Create (Calc, Out_File, Directory & "/calculation.csv");
         Put_Line (Calc, "case,rho,cutoff_a_z,cutoff_b_z,p_a,p_b,joint,union,conditional_b_given_a,conditional_a_given_b,phi,joint_refinement_delta,raw_union,raw_conditional_b_given_a,raw_conditional_a_given_b,complement_a_units");
         for K in Case_Index loop
            declare
               R : Calculation_Row renames Data.Calculations (K);
            begin
               Put_Line (Calc, Name (K) & "," & F (Rho) & "," & F (R.A) & "," & F (R.B)
                 & "," & F (PA (K)) & "," & F (PB (K)) & "," & F (R.Joint) & "," & F (R.Union_P)
                 & "," & F (R.B_Given_A) & "," & F (R.A_Given_B)
                 & "," & F (R.Phi) & "," & F (R.Refinement)
                 & "," & F (R.Raw_Union) & "," & F (R.Raw_B_Given_A)
                 & "," & F (R.Raw_A_Given_B) & "," & N (R.Complement_A));
            end;
         end loop;
         Close (Calc);
         Create (Grid, Out_File, Directory & "/grid.csv");
         Put_Line (Grid, "cutoff_iq,marginal_continuous,joint_continuous,conditional_continuous,grid_joint,grid_marginal,grid_conditional");
         for K in Grid_Index loop
            declare
               R : Grid_Row renames Data.Grid (K);
            begin
               Put_Line (Grid, F (R.Cutoff) & "," & F (R.Marginal) & "," & F (R.Joint)
                 & "," & F (R.Conditional_P) & "," & F (R.Grid_Joint)
                 & "," & F (R.Grid_Marginal) & "," & F (R.Grid_Conditional));
            end;
         end loop;
         Close (Grid);
         Create (Calibration, Out_File, Directory & "/calibration.csv");
         Put_Line (Calibration, "rho,target_union,cutoff_z,cutoff_iq_sd16,marginal,actual_union");
         Put_Line (Calibration, F (Rho) & "," & F (0.02) & "," & F (Data.Calibrated_Z) & ","
           & F (Data.Calibrated_IQ) & "," & F (Data.Calibrated_Marginal)
           & "," & F (Data.Calibrated_Union));
         Close (Calibration);
         Create (Sim, Out_File, Directory & "/simulation.csv");
         Put_Line (Sim, "case,trials,seed,neither,a_only,b_only,both,marginal_a,marginal_b,union,joint_fraction,conditional_b_given_a,conditional_a_given_b,joint_wilson_lower,joint_wilson_upper");
         for K in Case_Index loop
            declare
               R : Simulation_Row renames Data.Simulation (K);
            begin
               C := R.Cells;
               Put_Line (Sim, Name (K) & "," & N (Trials) & "," & N (Long_Long_Integer (Seed))
                 & "," & N (C.N00) & "," & N (C.N10) & "," & N (C.N01) & "," & N (C.N11)
                 & "," & N (R.Marginal_A) & "," & N (R.Marginal_B) & "," & N (R.Union_N)
                 & "," & F (R.Joint_Fraction)
                 & "," & (if R.Has_B_Given_A then F (R.B_Given_A) else "NA")
                 & "," & (if R.Has_A_Given_B then F (R.A_Given_B) else "NA")
                 & "," & F (R.Wilson_Lower) & "," & F (R.Wilson_Upper));
            end;
         end loop;
         Close (Sim);
         Put_Line ("Wrote calculations, BASIC-grid reproduction, calibration and simulation to " & Directory);
         Put_Line ("Simulation seed=" & Seed'Image & "; trials=" & Trials'Image);
      end Run;
   begin
      Towers_IO_Models.Check_Report (Trials, Long_Long_Integer (Seed), Data);
      if Ada.Command_Line.Argument_Count > 2 then
         Run (Ada.Command_Line.Argument (3));
      else
         Run ("results");
      end if;
   end Write_Report;
end Towers_IO;

with Ada.Command_Line;
with Ada.Text_IO;
with Normal_Support;
package body Report_IO with SPARK_Mode => Off is
   package FIO is new Ada.Text_IO.Float_IO (Real);
   procedure Number (X : Real; Digits_After : Natural) is
   begin FIO.Put (X, Fore => 1, Aft => Digits_After, Exp => 0); end Number;
   function Trimmed (N : Natural) return String is
      S : constant String := Natural'Image (N);
   begin return S (S'First + 1 .. S'Last); end Trimmed;
   procedure Read_Simulation_Options
     (Trials : out Sample_Count; Seed : out Interfaces.Unsigned_64) is
   begin
      Trials := 500_000; Seed := 20_261_030;
      if Ada.Command_Line.Argument_Count >= 1 then
         Trials := Sample_Count'Value (Ada.Command_Line.Argument (1));
      end if;
      if Ada.Command_Line.Argument_Count >= 2 then
         Seed := Interfaces.Unsigned_64'Value (Ada.Command_Line.Argument (2));
      end if;
      if Trials < 2 then
         raise Constraint_Error with "trials must be in 2..100000000";
      end if;
   end Read_Simulation_Options;
   procedure Simulation_Header (Seed : Interfaces.Unsigned_64) is
      S : constant String := Interfaces.Unsigned_64'Image (Seed);
   begin
      Ada.Text_IO.Put_Line ("# generator=64-bit LCG, transform=Box-Muller, seed=" & S (S'First + 1 .. S'Last));
      Ada.Text_IO.Put_Line ("# rare-tail counts are descriptive; this run cannot validate a one-in-a-million model");
      Ada.Text_IO.Put_Line ("tests,trials,mean_composite_z,variance_composite_z,above2,above3,above_rare,rate_above2,rate_above3,expected_rate2,expected_rate3");
   end Simulation_Header;
   procedure Simulation_Row
     (N : Test_Count; Trials : Sample_Count; Mean, Variance : Real;
      C : Tail_Counts; Rate_Two, Rate_Three, Expected_Two, Expected_Three : Normal_Support.Probability) is
   begin
      Ada.Text_IO.Put (Trimmed (N) & "," & Trimmed (Trials) & ","); Number (Mean, 12);
      Ada.Text_IO.Put (","); Number (Variance, 12);
      Ada.Text_IO.Put ("," & Trimmed (C.Above_Two) & "," & Trimmed (C.Above_Three) & "," & Trimmed (C.Above_Rare) & ",");
      Number (Rate_Two, 12); Ada.Text_IO.Put (",");
      Number (Rate_Three, 12); Ada.Text_IO.Put (",");
      Number (Expected_Two, 12); Ada.Text_IO.Put (",");
      Number (Expected_Three, 12); Ada.Text_IO.New_Line;
   end Simulation_Row;
   procedure Calculations_Header is
   begin Ada.Text_IO.Put_Line ("tests,variance_factor,mean_z,mean_score_sd16"); end Calculations_Header;
   procedure Named_Row
     (Label : String; Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value) is
   begin
      Ada.Text_IO.Put (Label & ","); Number (Factor, 14);
      Ada.Text_IO.Put (","); Number (Z, 14);
      Ada.Text_IO.Put (","); Number (Score, 14); Ada.Text_IO.New_Line;
   end Named_Row;
   procedure Calculation_Row
     (N : Test_Count; Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value) is
   begin Named_Row (Trimmed (N), Factor, Z, Score); end Calculation_Row;
   procedure Infinite_Row
     (Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value) is
   begin Named_Row ("infinity", Factor, Z, Score); end Infinite_Row;
   procedure Examples_Header is
   begin Ada.Text_IO.Put_Line ("# examples"); end Examples_Header;
   procedure Example (Label : String; X : Real) is
   begin
      Ada.Text_IO.Put (Label & ","); Number (X, 14); Ada.Text_IO.New_Line;
   end Example;
end Report_IO;

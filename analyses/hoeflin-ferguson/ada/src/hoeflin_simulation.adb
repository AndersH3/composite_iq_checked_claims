with Ada.Command_Line;
with Ada.Text_IO;
with Hoeflin_Core;
with Normal_Support;
with Interfaces;
procedure Hoeflin_Simulation with SPARK_Mode => Off is
   use Hoeflin_Core;
   package FIO is new Ada.Text_IO.Float_IO (Real);
   Counts : constant array (Positive range <>) of Test_Count :=
     (1, 2, 3, 4, 5, 10, 100, 1_000);
   Trials : Sample_Count := 500_000;
   Seed : Interfaces.Unsigned_64 := 20_261_030;
   Q : constant Real := Normal_Support.Inverse_Survival (1.0E-6);
   G : Normal_Support.Generator;
   procedure Number (X : Real) is
   begin FIO.Put (X, Fore => 1, Aft => 12, Exp => 0); end Number;
   function Trimmed (N : Natural) return String is
      S : constant String := Natural'Image (N);
   begin return S (S'First + 1 .. S'Last); end Trimmed;
   function Seed_Image return String is
      S : constant String := Interfaces.Unsigned_64'Image (Seed);
   begin return S (S'First + 1 .. S'Last); end Seed_Image;
   Common : constant Real := Normal_Support.Square_Root (0.6);
   X, Y, Mean_Z, Z, Sum, Sum_Squares, Mean, Variance : Real;
   C : Tail_Counts;
   Scale, Residual : Real;
begin
   if Ada.Command_Line.Argument_Count >= 1 then
      Trials := Sample_Count'Value (Ada.Command_Line.Argument (1));
   end if;
   if Ada.Command_Line.Argument_Count >= 2 then
      Seed := Interfaces.Unsigned_64'Value (Ada.Command_Line.Argument (2));
   end if;
   if Trials < 2 then raise Constraint_Error with "trials must be in 2..100000000"; end if;
   Ada.Text_IO.Put_Line ("# generator=64-bit LCG, transform=Box-Muller, seed=" & Seed_Image);
   Ada.Text_IO.Put_Line ("# rare-tail counts are descriptive; this run cannot validate a one-in-a-million model");
   Ada.Text_IO.Put_Line ("tests,trials,mean_composite_z,variance_composite_z,above2,above3,above_rare,rate_above2,rate_above3,expected_rate2,expected_rate3");
   for N of Counts loop
      Normal_Support.Reset (G, Seed);
      C := (others => 0); Sum := 0.0; Sum_Squares := 0.0;
      Scale := Normal_Support.Square_Root (Variance_Factor (N, 600));
      Residual := Normal_Support.Square_Root (0.4 / Real (N));
      for I in 1 .. Trials loop
         Normal_Support.Normal_Pair (G, X, Y);
         --  The mean of N independent Gaussian residuals is Gaussian, so
         --  this is the same distribution as explicitly averaging N tests.
         Mean_Z := Common * X + Residual * Y;
         Z := Mean_Z / Scale;
         Observe (C, Z, Q);
         Sum := Sum + Z; Sum_Squares := Sum_Squares + Z * Z;
      end loop;
      Mean := Sum / Real (Trials);
      Variance := (Sum_Squares - Sum * Mean) / Real (Trials - 1);
      Ada.Text_IO.Put (Trimmed (N) & "," & Trimmed (Trials) & ","); Number (Mean);
      Ada.Text_IO.Put (","); Number (Variance);
      Ada.Text_IO.Put ("," & Trimmed (C.Above_Two) & "," & Trimmed (C.Above_Three) & "," & Trimmed (C.Above_Rare) & ",");
      Number (Real (C.Above_Two) / Real (Trials)); Ada.Text_IO.Put (",");
      Number (Real (C.Above_Three) / Real (Trials)); Ada.Text_IO.Put (",");
      Number (Normal_Support.Survival (2.0)); Ada.Text_IO.Put (",");
      Number (Normal_Support.Survival (3.0)); Ada.Text_IO.New_Line;
   end loop;
end Hoeflin_Simulation;

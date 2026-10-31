with Ada.Text_IO;
with Hoeflin_Core;
with Normal_Support;
procedure Hoeflin_Calculations with SPARK_Mode => Off is
   use Hoeflin_Core;
   package FIO is new Ada.Text_IO.Float_IO (Real);
   Counts : constant array (Positive range <>) of Test_Count :=
     (1, 2, 3, 4, 5, 10, 100, 1_000);
   Q : constant Positive_Z := Normal_Support.Inverse_Survival (1.0E-6);
   procedure Number (X : Real) is
   begin FIO.Put (X, Fore => 1, Aft => 14, Exp => 0); end Number;
   procedure Row (Label : String; Factor : Real) is
      Scale : constant Scale_Value := Normal_Support.Square_Root (Factor);
      Z : constant Positive_Z := Threshold (Q, Scale);
   begin
      Ada.Text_IO.Put (Label & ","); Number (Factor);
      Ada.Text_IO.Put (","); Number (Z);
      Ada.Text_IO.Put (","); Number (IQ (Z)); Ada.Text_IO.New_Line;
   end Row;
   Scale : constant Scale_Value :=
     Normal_Support.Square_Root (Variance_Factor (3, 600));
   Reliability : constant Real := Latent_Reliability (3, 600);
   Latent_Mean : constant Real := Normal_Support.Square_Root (Reliability) * Q;
   Latent_SD : constant Real := Normal_Support.Square_Root (0.4 / 2.2);
   procedure Example (Label : String; X : Real) is
   begin
      Ada.Text_IO.Put (Label & ","); Number (X); Ada.Text_IO.New_Line;
   end Example;
   function Trimmed (N : Test_Count) return String is
      S : constant String := Test_Count'Image (N);
   begin return S (S'First + 1 .. S'Last); end Trimmed;
begin
   Ada.Text_IO.Put_Line ("tests,variance_factor,mean_z,mean_score_sd16");
   for N of Counts loop Row (Trimmed (N), Variance_Factor (N, 600)); end loop;
   Row ("infinity", 0.6);
   Ada.Text_IO.Put_Line ("# examples");
   Example ("upper_tail_quantile", Q);
   Example ("three_test_mean160_composite_iq", IQ (Composite (3.75, Scale)));
   Example ("latent_conditional_mean_iq", 100.0 + 16.0 * Latent_Mean);
   Example ("latent_conditional_sd_iq", 16.0 * Latent_SD);
end Hoeflin_Calculations;

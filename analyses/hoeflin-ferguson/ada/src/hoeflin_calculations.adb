with Hoeflin_Core;
with Normal_Support;
with Report_IO;
procedure Hoeflin_Calculations with SPARK_Mode is
   use Hoeflin_Core;
   Counts : constant array (Positive range <>) of Test_Count :=
     (1, 2, 3, 4, 5, 10, 100, 1_000);
   Q : constant Positive_Z := Normal_Support.Rare_Quantile;
   Scale : constant Scale_Value :=
     Normal_Support.Square_Root (Variance_Factor (3, 600));
   Reliability : constant Real := Latent_Reliability (3, 600);
   Latent_SD : constant Real := Normal_Support.Square_Root (0.4 / 2.2);
   Factor : Variance_Value;
   Z : Positive_Z;
begin
   Report_IO.Calculations_Header;
   for N of Counts loop
      Factor := Variance_Factor (N, 600);
      Z := Threshold (Q, Normal_Support.Square_Root (Factor));
      Report_IO.Calculation_Row (N, Factor, Z, IQ (Z));
   end loop;
   Z := Threshold (Q, Normal_Support.Square_Root (0.6));
   Report_IO.Infinite_Row (0.6, Z, IQ (Z));
   Report_IO.Examples_Header;
   Report_IO.Example ("upper_tail_quantile", Q);
   Report_IO.Example ("three_test_mean160_composite_iq", IQ (Composite (3.75, Scale)));
   Report_IO.Example ("latent_conditional_mean_iq",
                      100.0 + 16.0 * (Normal_Support.Square_Root (Reliability) * Q));
   Report_IO.Example ("latent_conditional_sd_iq", 16.0 * Latent_SD);
end Hoeflin_Calculations;

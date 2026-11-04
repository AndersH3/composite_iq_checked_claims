with Towers_Boundary_Models;
with Ada.Numerics.Long_Elementary_Functions;
package body Towers_Engine with SPARK_Mode is
   use Admission_Core;
   use Normal_Model;
   use Ada.Numerics.Long_Elementary_Functions;

   function Checked_Quantization (P : Probability; Q : Probability_Units)
     return Probability_Units with
     Global => null,
     Post => (Checked_Quantization'Result = Q) and then
       (abs (Long_Float (Checked_Quantization'Result) / Long_Float (Scale) - P) <= 0.51E-15) and then
       (Towers_Boundary_Models.Quantization_Normal_Return (P, Long_Long_Integer (Q), Long_Long_Integer (Checked_Quantization'Result))),
     Depends => (Checked_Quantization'Result => (P, Q));
   function Checked_Quantization (P : Probability; Q : Probability_Units)
     return Probability_Units with SPARK_Mode => Off
   is
   begin
      if abs (Long_Float (Q) / Long_Float (Scale) - P) > 0.51E-15 then
         raise Constraint_Error with "probability quantization bound exceeded";
      end if;
      Towers_Boundary_Models.Observe_Quantization
        (P, Long_Long_Integer (Q), Long_Long_Integer (Q));
      return Q;
   end Checked_Quantization;

   procedure Check_Union_Units (A, B, J : in out Probability_Units) with
     Global => null,
     Post => A = A'Old and B = B'Old and J = J'Old
       and J <= A and J <= B and A + B <= Scale,
     Depends => ((A, B, J) => (A, B, J));
   procedure Check_Union_Units (A, B, J : in out Probability_Units)
     with SPARK_Mode => Off
   is
      Old_A : constant Long_Long_Integer := Long_Long_Integer (A) with Ghost;
      Old_B : constant Long_Long_Integer := Long_Long_Integer (B) with Ghost;
      Old_J : constant Long_Long_Integer := Long_Long_Integer (J) with Ghost;
   begin
      if J > A or else J > B or else A + B > Scale then
         raise Constraint_Error with "invalid union probability units";
      end if;
      Towers_Boundary_Models.Observe_Union
        (Long_Long_Integer (A), Long_Long_Integer (B), Long_Long_Integer (J),
         Old_A, Old_B, Old_J);
   end Check_Union_Units;

   procedure Check_Conditional_Units (J, M : in out Probability_Units) with
     Global => null,
     Post => J = J'Old and M = M'Old and M > 0 and J <= M,
     Depends => ((J, M) => (J, M));
   procedure Check_Conditional_Units (J, M : in out Probability_Units)
     with SPARK_Mode => Off
   is
      Old_J : constant Long_Long_Integer := Long_Long_Integer (J) with Ghost;
      Old_M : constant Long_Long_Integer := Long_Long_Integer (M) with Ghost;
   begin
      if M = 0 or else J > M then
         raise Constraint_Error with "invalid conditional probability units";
      end if;
      Towers_Boundary_Models.Observe_Conditional
        (Long_Long_Integer (J), Long_Long_Integer (M), Old_J, Old_M);
   end Check_Conditional_Units;

   procedure Check_Joint (J : in out Long_Float; A, B : Probability) with
     Global => null,
     Post => J = J'Old and J >= 0.0 and J <= A and J <= B,
     Depends => (J => (J, A, B));
   procedure Check_Joint (J : in out Long_Float; A, B : Probability)
     with SPARK_Mode => Off
   is
      Old_J : constant Long_Float := J with Ghost;
   begin
      if not (J >= 0.0 and J <= A and J <= B) then
         raise Constraint_Error with "joint tail exceeds its marginal";
      end if;
      Towers_Boundary_Models.Observe_Joint (J, A, B, Old_J);
   end Check_Joint;

   function Units (P : Probability) return Probability_Units with
     Global => null,
     Post => (abs (Long_Float (Units'Result) / Long_Float (Scale) - P) <= 0.51E-15) and then
       (Units'Result >= 0) and then
       (Units'Result <= Scale),
     Depends => (Units'Result => P);
   function Units (P : Probability) return Probability_Units is
      Q : constant Probability_Units := Probability_Units (P * Long_Float (Scale));
   begin
      return Checked_Quantization (P, Q);
   end Units;

   function Value (P : Rational_Probability) return Probability is
      Result : constant Long_Float := Long_Float (P.Numerator) / Long_Float (P.Denominator);
   begin
      if not (Result in 0.0 .. 1.0) then
         raise Constraint_Error with "invalid rational probability value";
      end if;
      return Result;
   end Value;

   function Conditional_Value (Joint, Marginal : Probability) return Probability with
     Global => null,
     Post => (Conditional_Value'Result >= 0.0) and then
       (Conditional_Value'Result <= 1.0) and then
       (if Joint = 0.0 then Conditional_Value'Result = 0.0),
     Depends => (Conditional_Value'Result => (Joint, Marginal));
   function Conditional_Value (Joint, Marginal : Probability) return Probability is
      J : Probability_Units := Units (Joint);
      M : Probability_Units := Units (Marginal);
   begin
      Check_Conditional_Units (J, M);
      return Value (Conditional (J, M));
   end Conditional_Value;

   procedure Wilson (Successes : Count; Denominator : Trial_Count;
                     Lo, Hi : out Probability) with
     Global => null,
     Pre => Successes <= Denominator,
     Post => (Lo >= 0.0) and then
       (Hi <= 1.0),
     Depends => ((Lo, Hi) => (Successes, Denominator));
   procedure Wilson (Successes : Count; Denominator : Trial_Count;
                     Lo, Hi : out Probability) is
      Z : constant Long_Float := 1.959963984540054;
      NN : constant Long_Float := Long_Float (Denominator);
      P : constant Long_Float := Value (Fraction (Successes, Denominator));
      D : constant Long_Float := 1.0 + Z * Z / NN;
      Centre : constant Long_Float := (P + Z * Z / (2.0 * NN)) / D;
      Root : constant Long_Float := Square_Root (P * (1.0 - P) / NN + Z * Z / (4.0 * NN * NN));
      Half : Long_Float;
   begin
      if not (Root in 0.0 .. 2.0) then
         raise Constraint_Error with "Wilson root outside checked range";
      end if;
      Half := Z * Root / D;
      Lo := Long_Float'Max (0.0, Centre - Half);
      Hi := Long_Float'Min (1.0, Centre + Half);
   end Wilson;

   type Cutoff_Cases is array (Case_Index) of Z_Value;
   type Tally_Array is array (Case_Index) of Counts;

   procedure Calculate
     (Left, Right : Marginal_Probability; A, B : out Z_Value;
      Row : out Calculation_Row) with
     Global => null,
     Post => Row.A = A and then Row.B = B and then Row.Refinement >= 0.0,
     Depends => (A => Left, B => Right, Row => (Left, Right));
   procedure Calculate
     (Left, Right : Marginal_Probability; A, B : out Z_Value;
      Row : out Calculation_Row)
   is
      J, J_Coarse, Denom, U, Phi : Long_Float;
      PJ, PMA, PMB : Probability_Units;
      Lower_Tail : constant Probability := SF (12.0) with Ghost;
      Upper_Tail : constant Probability := SF (-12.0) with Ghost;
   begin
      Towers_Boundary_Models.Observe_Inverse_Bracket (Left, Lower_Tail, Upper_Tail);
      Towers_Boundary_Models.Observe_Inverse_Bracket (Right, Lower_Tail, Upper_Tail);
      A := Inverse_SF (Left);
      B := Inverse_SF (Right);
      J := Joint_Tail (A, B, Rho);
      J_Coarse := Joint_Tail (A, B, Rho, 10_000);
      Check_Joint (J, Left, Right);
      PMA := Units (Left); PMB := Units (Right); PJ := Units (J);
      Check_Union_Units (PMA, PMB, PJ);
      U := Long_Float (Union_Probability (PMA, PMB, PJ)) / Long_Float (Scale);
      Denom := Square_Root (Left * (1.0 - Left) * Right * (1.0 - Right));
      if not (Denom in 1.0E-15 .. 1.0) then
         raise Constraint_Error with "phi denominator outside checked range";
      end if;
      Phi := (J - Left * Right) / Denom;
      Row :=
        (A => A, B => B, Joint => J, Union_P => U,
         B_Given_A => Conditional_Value (J, Left),
         A_Given_B => Conditional_Value (J, Right), Phi => Phi,
         Refinement => abs (J - J_Coarse),
         Raw_Union => Left + Right - J,
         Raw_B_Given_A => J / Left, Raw_A_Given_B => J / Right,
         Complement_A => Complement (PMA));
   end Calculate;

   procedure Observe_All
     (Tallies : in out Tally_Array; Iteration : Trial_Count;
      X, Y : Long_Float; A, B : Cutoff_Cases) with
     Global => null,
     Pre => (for all K in Case_Index => Total (Tallies (K)) = Iteration - 1),
     Post => (for all K in Case_Index => Total (Tallies (K)) = Iteration) and then (for all K in Case_Index => Tallies (K).N11 <= Iteration),
     Depends => (Tallies => (Tallies, X, Y, A, B), null => Iteration);
   procedure Observe_All
     (Tallies : in out Tally_Array; Iteration : Trial_Count;
      X, Y : Long_Float; A, B : Cutoff_Cases)
   is
   begin
      for K in Case_Index loop
         pragma Loop_Invariant
           (for all L in Case_Index => Total (Tallies (L)) =
              (if L < K then Iteration else Iteration - 1));
         Observe (Tallies (K), Classify (X > A (K), Y > B (K)));
      end loop;
   end Observe_All;

   function Simulation_Row_For (Cells : Counts; Trials : Trial_Count)
     return Simulation_Row with
     Global => null,
     Pre => Total (Cells) = Trials,
     Post => (Simulation_Row_For'Result.Cells = Cells) and then
       (Simulation_Row_For'Result.Marginal_A = Marginal_A (Cells)) and then
       (Simulation_Row_For'Result.Marginal_B = Marginal_B (Cells)) and then
       (Simulation_Row_For'Result.Union_N = Union_Count (Cells)),
     Depends => (Simulation_Row_For'Result => (Cells, Trials));
   function Simulation_Row_For (Cells : Counts; Trials : Trial_Count)
     return Simulation_Row
   is
      Lower, Upper : Probability;
      MA, MB : Count;
   begin
      Wilson (Cells.N11, Trials, Lower, Upper);
      MA := Marginal_A (Cells); MB := Marginal_B (Cells);
      return
        (Cells => Cells, Marginal_A => MA,
         Marginal_B => MB, Union_N => Union_Count (Cells),
         Joint_Fraction => Value (Fraction (Cells.N11, Trials)),
         Has_B_Given_A => MA > 0, Has_A_Given_B => MB > 0,
         B_Given_A => (if MA = 0 then 0.0 else Value (Fraction (Cells.N11, MA))),
         A_Given_B => (if MB = 0 then 0.0 else Value (Fraction (Cells.N11, MB))),
         Wilson_Lower => Lower, Wilson_Upper => Upper);
   end Simulation_Row_For;

   procedure Compute (Trials : Trial_Count; Seed : Seed_Value; Data : out Results) is
      A, B : Cutoff_Cases;
      Tallies : Tally_Array := (others => (others => 0));
      G : Generator;
      PJ, PMA, PMB : Probability_Units;
      Q : Z_Value;
      Cont_P, Cont_J : Probability;
      Grid_Values : Grid_Results;
      subtype IQ_Cutoff is Long_Float range 133.0 .. 164.0;
      Cuts : constant array (Grid_Index) of IQ_Cutoff := (133.0, 150.0, 164.0);
      X, E : Normal_Value;
      Y, Correlation_Root : Long_Float;
   begin
      Data := (others => <>);
      for K in Case_Index loop
         Calculate (PA (K), PB (K), A (K), B (K), Data.Calculations (K));
      end loop;

      Grid_Values := Basic_Grid;
      for K in Grid_Index loop
         Q := (Cuts (K) - 100.0) / 16.0;
         Cont_P := SF (Q);
         Cont_J := Joint_Tail (Q, Q, Rho);
         Data.Grid (K) :=
           (Cutoff => Cuts (K), Marginal => Cont_P, Joint => Cont_J,
            Conditional_P => Conditional_Value (Cont_J, Cont_P),
            Grid_Joint => Grid_Values (K).Joint,
            Grid_Marginal => Grid_Values (K).Marginal,
            Grid_Conditional => Conditional_Value (Grid_Values (K).Joint, Grid_Values (K).Marginal));
      end loop;

      Q := Calibrated_OR_Cutoff (0.02, Rho);
      PMA := Units (SF (Q)); PMB := Units (SF (Q)); PJ := Units (Joint_Tail (Q, Q, Rho));
      Check_Union_Units (PMA, PMB, PJ);
      Data.Calibrated_Union := Long_Float (Union_Probability (PMA, PMB, PJ)) / Long_Float (Scale);
      Data.Calibrated_Z := Q;
      Data.Calibrated_IQ := 100.0 + 16.0 * Q;
      Data.Calibrated_Marginal := SF (Q);

      Reset (G, Seed);
      for Iteration in 1 .. Trials loop
         pragma Loop_Invariant
           (for all K in Case_Index => Total (Tallies (K)) = Iteration - 1);
         Normal_Pair (G, X, E);
         Correlation_Root := Square_Root (1.0 - Rho * Rho);
         if not (Correlation_Root in 0.0 .. 1.0) then
            raise Constraint_Error with "correlation root outside checked range";
         end if;
         Y := Rho * X + Correlation_Root * E;
         Observe_All (Tallies, Iteration, X, Y, A, B);
      end loop;
      for K in Case_Index loop
         pragma Loop_Invariant
           (for all L in Case_Index => Total (Tallies (L)) = Trials);
         pragma Loop_Invariant
           (for all L in Case_Index => (if L < K then
              Total (Data.Simulation (L).Cells) = Trials));
         pragma Loop_Invariant
           (for all L in Case_Index => (if L < K then
              Data.Simulation (L).Marginal_A = Marginal_A (Data.Simulation (L).Cells)
              and then Data.Simulation (L).Marginal_B = Marginal_B (Data.Simulation (L).Cells)));
         Data.Simulation (K) := Simulation_Row_For (Tallies (K), Trials);
      end loop;
   end Compute;
end Towers_Engine;

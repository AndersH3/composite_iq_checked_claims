with Ada.Numerics.Long_Elementary_Functions;
with Ada.Numerics;
with Interfaces.C;

package body Normal_Model with SPARK_Mode is
   use Ada.Numerics.Long_Elementary_Functions;
   Pi : constant Long_Float := Ada.Numerics.Pi;
   function C_Erfc (X : Interfaces.C.double) return Interfaces.C.double
     with Import, Convention => C, External_Name => "erfc", SPARK_Mode => Off;

   --  Small checked elementary-function boundaries. Their bodies execute all
   --  stated bounds before returning; proof uses these contracts conditionally.
   --  They do not prove libm accuracy or that a failed check is impossible.
   function Square_Root (X : Long_Float) return Long_Float
     with SPARK_Mode => Off
   is
      Result : constant Long_Float := Sqrt (X);
   begin
      if not (Result in 0.0 .. 1.0E3)
        or else (X >= 1.0E-30 and then Result < 1.0E-15)
        or else (X >= 0.0625 and then Result < 0.25)
        or else (X >= 1.0 and then Result < 1.0)
        or else (X <= 1.0 and then Result > 1.0)
        or else (X <= 4.0 and then Result > 2.0)
        or else (X <= 64.0 and then Result > 8.0)
      then
         raise Constraint_Error with "sqrt range check failed";
      end if;
      return Result;
   end Square_Root;

   function Checked_Log (X : Long_Float) return Long_Float
     with Global => null, Pre => X in 4.0E-10 .. 0.9999999999,
     Post => Checked_Log'Result in -23.0 .. 0.0;
   function Checked_Log (X : Long_Float) return Long_Float
     with SPARK_Mode => Off
   is
      Result : constant Long_Float := Log (X);
   begin
      if not (Result in -23.0 .. 0.0) then
         raise Constraint_Error with "log range check failed";
      end if;
      return Result;
   end Checked_Log;

   function Checked_Exp (X : Long_Float) return Long_Float
     with Global => null, Pre => X <= 1.0E-9,
     Post => Checked_Exp'Result in 0.0 .. 1.0001;
   function Checked_Exp (X : Long_Float) return Long_Float
     with SPARK_Mode => Off
   is
      Result : constant Long_Float := Exp (X);
   begin
      if not (Result in 0.0 .. 1.0001) then
         raise Constraint_Error with "exp range check failed";
      end if;
      return Result;
   end Checked_Exp;

   function Checked_Exponent (X : Long_Float) return Long_Float
     with Global => null,
     Post => Checked_Exponent'Result = X and
       Checked_Exponent'Result <= 1.0E-9;
   function Checked_Exponent (X : Long_Float) return Long_Float
     with SPARK_Mode => Off
   is
   begin
      if not (X <= 1.0E-9) then
         raise Constraint_Error with "density exponent outside checked range";
      end if;
      return X;
   end Checked_Exponent;

   function Checked_Probability (P : Long_Float) return Probability
     with Global => null, Post => Checked_Probability'Result = P;
   function Checked_Probability (P : Long_Float) return Probability
     with SPARK_Mode => Off
   is
   begin
      if not (P in 0.0 .. 1.0) then
         raise Constraint_Error with "numerical probability outside [0,1]";
      end if;
      return P;
   end Checked_Probability;

   function SF (Z : Long_Float) return Probability with SPARK_Mode => Off is
      Result : constant Long_Float :=
        0.5 * Long_Float (C_Erfc (Interfaces.C.double (Z / Sqrt (2.0))));
   begin
      if not (Result in 0.0 .. 1.0)
        or else (Z >= 10.0 and then Result >= 1.0E-20)
        or else (Z <= -10.0 and then Result <= 1.0 - 1.0E-14)
      then
         raise Constraint_Error with "normal survival boundary check failed";
      end if;
      return Result;
   end SF;

   procedure Count_Step (I : Positive) with Ghost, Global => null,
     Post => Long_Float (I) = Long_Float (I - 1) + 1.0
       and 4.0 * Long_Float (I) >= 4.0 * Long_Float (I - 1) + 2.0
       and 8.0 * Long_Float (I) >= 8.0 * Long_Float (I - 1) + 6.0;
   procedure Count_Step (I : Positive) is
   begin
      pragma Assert (Long_Float (I) = Long_Float (I - 1) + 1.0);
   end Count_Step;

   subtype Integration_Point is Long_Float range 0.0 .. 0.96;
   function Checked_Node (X : Long_Float) return Integration_Point
     with Global => null, Post => Checked_Node'Result = X;
   function Checked_Node (X : Long_Float) return Integration_Point
     with SPARK_Mode => Off
   is
   begin
      if not (X in 0.0 .. 0.96) then
         raise Constraint_Error with "quadrature node outside checked interval";
      end if;
      return X;
   end Checked_Node;

   function Inverse_SF (P : Probability) return Z_Value is
      Lo : Long_Float := -12.0;
      Hi : Long_Float := 12.0;
      Mid : Long_Float;
   begin
      if P <= SF (Hi) or else P >= SF (Lo) then
         raise Constraint_Error with "inverse SF probability outside [-12,12] bracket";
      end if;
      for Iteration in 1 .. 80 loop
         pragma Loop_Invariant (Lo in -12.0 .. 12.0 and Hi in -12.0 .. 12.0);
         pragma Loop_Invariant (Lo <= Hi);
         Mid := (Lo + Hi) / 2.0;
         if SF (Mid) > P then
            Lo := Mid;
         else
            Hi := Mid;
         end if;
      end loop;
      return (Lo + Hi) / 2.0;
   end Inverse_SF;

   function Joint_Tail
     (A, B : Long_Float; Rho : Correlation; Steps : Positive := 20_000)
      return Probability
   is
      function Density (R : Long_Float) return Long_Float
        with Pre => R in 0.0 .. 0.96
          and abs (A) <= 1.0E100 and abs (B) <= 1.0E100,
        Post => Density'Result in 0.0 .. 1.0;
      function Density (R : Long_Float) return Long_Float is
         S : constant Long_Float := 1.0 - R * R;
         Power, Numerator, Root, Result : Long_Float;
      begin
         if not (S in 0.07 .. 1.0) then
            raise Constraint_Error with "density variance outside checked range";
         end if;
         Power := -(A * A - 2.0 * R * A * B + B * B) / (2.0 * S);
         Power := Checked_Exponent (Power);
         Numerator := Checked_Exp (Power);
         Root := Square_Root (S);
         if not (Root in 0.25 .. 1.0) then
            raise Constraint_Error with "density square root outside checked range";
         end if;
         Result := Numerator / (2.0 * Pi * Root);
         if not (Result in 0.0 .. 1.0) then
            raise Constraint_Error with "density outside checked range";
         end if;
         return Result;
      end Density;
      H, Sum : Long_Float;
   begin
      if Rho < 0.0 or else Rho > 0.95 or else Steps mod 2 /= 0 then
         raise Constraint_Error with "joint tail requires 0<=rho<=.95 and even steps";
      end if;
      H := Rho / Long_Float (Steps);
      Sum := Density (0.0) + Density (Rho);
      for I in 1 .. Steps - 1 loop
         pragma Loop_Invariant (H in 0.0 .. 0.95);
         pragma Loop_Invariant (Sum in 0.0 .. 8.0 * Long_Float (I));
         Count_Step (I + 1);
         Sum := Sum + (if I mod 2 = 0 then 2.0 else 4.0)
           * Density (Checked_Node (Long_Float (I) * H));
      end loop;
      declare
         Result : constant Long_Float := SF (A) * SF (B) + H * Sum / 3.0;
      begin
         return Checked_Probability (Result);
      end;
   end Joint_Tail;

   function Calibrated_OR_Cutoff
     (Target : Probability; Rho : Correlation) return Z_Value
   is
      Lo : Long_Float := 0.0;
      Hi : Long_Float := 8.0;
      Mid, Union_P : Long_Float;
   begin
      if Target <= 0.0 or else Target >= 0.5 then
         raise Constraint_Error with "OR target outside supported interval";
      end if;
      for I in 1 .. 65 loop
         pragma Loop_Invariant (Lo in 0.0 .. 8.0 and Hi in 0.0 .. 8.0);
         pragma Loop_Invariant (Lo <= Hi);
         Mid := (Lo + Hi) / 2.0;
         Union_P := 2.0 * SF (Mid) - Joint_Tail (Mid, Mid, Rho, 2_000);
         if Union_P > Target then Lo := Mid; else Hi := Mid; end if;
      end loop;
      return (Lo + Hi) / 2.0;
   end Calibrated_OR_Cutoff;

   type Grid_Accumulator is record
      Joint, Marginal : Long_Float := 0.0;
   end record;
   type Grid_Accumulators is array (1 .. 3) of Grid_Accumulator;
   procedure Add_Grid_Weight
     (I : Positive; Weight : Probability; Running_Total : in out Long_Float)
     with Global => null,
     Pre => Running_Total in 0.0 .. 4.0 * Long_Float (I - 1),
     Post => Running_Total in 0.0 .. 4.0 * Long_Float (I);
   procedure Add_Grid_Weight
     (I : Positive; Weight : Probability; Running_Total : in out Long_Float)
   is
   begin
      Count_Step (I);
      Running_Total := Running_Total + Weight;
   end Add_Grid_Weight;

   procedure Add_Grid_Cutoff
     (I : Positive; Weight : Probability; X, Y, Cutoff : Long_Float;
      Value : in out Grid_Accumulator)
     with Global => null,
     Pre => Value.Joint in 0.0 .. 4.0 * Long_Float (I - 1) and
       Value.Marginal in 0.0 .. 4.0 * Long_Float (I - 1),
     Post => Value.Joint in 0.0 .. 4.0 * Long_Float (I) and
       Value.Marginal in 0.0 .. 4.0 * Long_Float (I);
   procedure Add_Grid_Cutoff
     (I : Positive; Weight : Probability; X, Y, Cutoff : Long_Float;
      Value : in out Grid_Accumulator)
   is
   begin
      Count_Step (I);
      if X >= Cutoff then
         Add_Grid_Weight (I, Weight, Value.Marginal);
         if Y >= Cutoff then
            Add_Grid_Weight (I, Weight, Value.Joint);
         end if;
      end if;
   end Add_Grid_Cutoff;

   procedure Add_Grid_Cell
     (I : Positive; Weight : Probability; X, Y : Long_Float;
      Values : in out Grid_Accumulators)
     with Global => null,
     Pre => (for all K in Values'Range =>
       Values (K).Joint in 0.0 .. 4.0 * Long_Float (I - 1) and
       Values (K).Marginal in 0.0 .. 4.0 * Long_Float (I - 1)),
     Post => (for all K in Values'Range =>
       Values (K).Joint in 0.0 .. 4.0 * Long_Float (I) and
       Values (K).Marginal in 0.0 .. 4.0 * Long_Float (I));
   procedure Add_Grid_Cell
     (I : Positive; Weight : Probability; X, Y : Long_Float;
      Values : in out Grid_Accumulators)
   is
   begin
      --  Three fixed report cutoffs, in the original accumulation order.
      Add_Grid_Cutoff (I, Weight, X, Y, 133.0, Values (1));
      Add_Grid_Cutoff (I, Weight, X, Y, 150.0, Values (2));
      Add_Grid_Cutoff (I, Weight, X, Y, 164.0, Values (3));
   end Add_Grid_Cell;

   procedure Check_Grid_State (Total : in out Long_Float; Values : in out Grid_Accumulators)
     with Global => null,
     Post => Total = Total'Old and Values = Values'Old and
       Total in 1.0E-100 .. 1.0E6 and
       (for all K in Values'Range =>
          Values (K).Joint in 0.0 .. Total and Values (K).Marginal in 0.0 .. Total);
   procedure Check_Grid_State (Total : in out Long_Float; Values : in out Grid_Accumulators)
     with SPARK_Mode => Off
   is
   begin
      if not (Total in 1.0E-100 .. 1.0E6) then
         raise Constraint_Error with "grid normalization total outside checked range";
      end if;
      for K in Values'Range loop
         if not (Values (K).Joint in 0.0 .. Total)
           or else not (Values (K).Marginal in 0.0 .. Total)
         then
            raise Constraint_Error with "grid numerator outside checked range";
         end if;
      end loop;
   end Check_Grid_State;

   function Basic_Grid return Grid_Results is
      Values : Grid_Accumulators := (others => (others => 0.0));
      Result : Grid_Results := (others => (others => 0.0));
      X, Y, D, Power : Long_Float;
      ZX, ZY : Z_Value;
      Total : Long_Float := 0.0;
      R : constant Long_Float := 0.7;
      Root : constant Long_Float := Square_Root (1.0 - R * R);
   begin
      for I in 0 .. 396 loop
         pragma Loop_Invariant (Total in 0.0 .. 4.0 * Long_Float (I * 397));
         pragma Loop_Invariant (for all K in Values'Range =>
           Values (K).Joint in 0.0 .. 4.0 * Long_Float (I * 397) and
           Values (K).Marginal in 0.0 .. 4.0 * Long_Float (I * 397));
         X := 1.0 + 0.5 * Long_Float (I);
         ZX := (X - 100.0) / 16.0;
         for J in 0 .. 396 loop
            pragma Loop_Invariant (Total in 0.0 .. 4.0 * Long_Float (I * 397 + J));
            pragma Loop_Invariant (for all K in Values'Range =>
              Values (K).Joint in 0.0 .. 4.0 * Long_Float (I * 397 + J) and
              Values (K).Marginal in 0.0 .. 4.0 * Long_Float (I * 397 + J));
            Count_Step (I * 397 + J + 1);
            Y := 1.0 + 0.5 * Long_Float (J);
            ZY := (Y - 100.0) / 16.0;
            Power := -(ZX * ZX - 2.0 * R * ZX * ZY + ZY * ZY)
              / (2.0 * (1.0 - R * R));
            Power := Checked_Exponent (Power);
            D := Checked_Exp (Power) / (2.0 * Pi * Root);
            Add_Grid_Weight (I * 397 + J + 1, D, Total);
            Add_Grid_Cell (I * 397 + J + 1, D, X, Y, Values);
         end loop;
      end loop;
      Check_Grid_State (Total, Values);
      for K in Result'Range loop
         Result (K).Joint := Checked_Probability (Values (K).Joint / Total);
         Result (K).Marginal := Checked_Probability (Values (K).Marginal / Total);
      end loop;
      return Result;
   end Basic_Grid;

   procedure Reset (G : out Generator; Seed : Positive) is
   begin
      if Seed >= 2_147_483_647 then
         raise Constraint_Error with "seed must be in 1..2147483646";
      end if;
      G.State := Long_Long_Integer (Seed);
   end Reset;

   procedure Uniform (G : in out Generator; U : out Long_Float)
     with Global => null,
     Post => U in 4.0E-10 .. 0.9999999999
       and G.State = (48_271 * G.State'Old) mod 2_147_483_647
       and U = Long_Float (G.State) / 2_147_483_647.0;
   procedure Uniform (G : in out Generator; U : out Long_Float) is
   begin
      --  Park-Miller multiplicative generator; exact integer recurrence.
      G.State := (48_271 * G.State) mod 2_147_483_647;
      U := Long_Float (G.State) / 2_147_483_647.0;
   end Uniform;

   subtype Radius_Value is Long_Float range 0.0 .. 8.0;
   subtype Trig_Value is Long_Float range -1.0 .. 1.0;
   function Scale_Normal (Radius : Radius_Value; Trig : Trig_Value)
      return Normal_Value with Global => null;
   function Scale_Normal (Radius : Radius_Value; Trig : Trig_Value)
      return Normal_Value is
   begin
      return Radius * Trig;
   end Scale_Normal;

   procedure Normal_Pair (G : in out Generator; X, Y : out Normal_Value) is
      U, V, Log_U, Radius, Angle : Long_Float;
      Cosine, Sine : Trig_Value;
   begin
      Uniform (G, U);
      Uniform (G, V);
      Log_U := Checked_Log (U);
      Radius := Square_Root (-2.0 * Log_U);
      if not (Radius in 0.0 .. 8.0) then
         raise Constraint_Error with "normal radius outside checked range";
      end if;
      Angle := 2.0 * Pi * V;
      Cosine := Cos (Angle);
      X := Scale_Normal (Radius, Cosine);
      Sine := Sin (Angle);
      Y := Scale_Normal (Radius, Sine);
   end Normal_Pair;
end Normal_Model;

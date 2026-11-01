package body Hoeflin_Boundary_Models with SPARK_Mode is
   function Erfc_Scaling (Raw : Real) return Real is
   begin
      return 0.5 * Raw;
   end Erfc_Scaling;
   procedure Observe_Sqrt (X, Value : Real) is null;
   procedure Observe_Probability (Value : Real) is null;
   procedure Observe_Erfc (Raw, Scaled : Real) is null;
   procedure Observe_Inverse_Bracket (P, Lower_SF, Upper_SF : Real) is null;
   procedure Observe_Rare_Quantile (Value : Real) is null;
   procedure Observe_Log_Radius (U, Log_U, Radius : Real) is null;
   procedure Observe_Trig (Value : Real) is null;

   function Transition (Trace : Report_Trace; Event : Event_Kind; Data : Payload)
      return Report_Trace
   is
      Result : Report_Trace := Trace;
   begin
      Result.Last_Event := Event;
      Result.Events := Trace.Events + 1;
      Result.Columns := Column_Count (Event);
      Result.Data := Data;
      Result.Last_Call_Admissible := Can_Emit (Trace, Event, Data);
      case Event is
         when Simulation_Header_Event => Result.Section := Simulation; Result.Rows := 0;
         when Calculations_Header_Event => Result.Section := Calculations; Result.Rows := 0;
         when Examples_Header_Event => Result.Section := Examples; Result.Rows := 0;
         when Simulation_Row_Event | Calculation_Row_Event | Infinite_Row_Event | Example_Event =>
            Result.Rows := Trace.Rows + 1;
         when others => null;
      end case;
      return Result;
   end Transition;

   procedure Note (Trace : in out Report_Trace; Event : Event_Kind; Data : Payload) is
   begin
      Trace := Transition (Trace, Event, Data);
   end Note;

   function Decimal_Image (N : Natural; Text : String) return Boolean is
      Value : Natural := 0;
      Digit : Natural;
   begin
      if not Valid_Column_Label (Text) or else
        (Text'Length > 1 and then Text (Text'First) = '0')
      then
         return False;
      end if;
      for C of Text loop
         if C not in '0' .. '9' then return False; end if;
         Digit := Character'Pos (C) - Character'Pos ('0');
         if Value > (Natural'Last - Digit) / 10 then return False; end if;
         Value := Value * 10 + Digit;
      end loop;
      return Value = N;
   end Decimal_Image;
   procedure Observe_Decimal_Image (N : Natural; Text : String) is null;
   procedure Observe_Number
     (Value : Real; Decimal_Places : Natural; Projection : Number_Projection) is null;
   procedure Observe_Label (Text : String; Projection : Label_Projection) is null;
   function Project_Label (Text : String) return Label_Projection is
      Result : Label_Projection := (Text'Length, 0, 0, 0);
   begin
      for I in Text'Range loop
         pragma Loop_Invariant (Result.Commas <= I - Text'First);
         pragma Loop_Invariant (Result.Line_Feeds <= I - Text'First);
         pragma Loop_Invariant (Result.Carriage_Returns <= I - Text'First);
         if Text (I) = ',' then Result.Commas := Result.Commas + 1; end if;
         if Text (I) = ASCII.LF then Result.Line_Feeds := Result.Line_Feeds + 1; end if;
         if Text (I) = ASCII.CR then Result.Carriage_Returns := Result.Carriage_Returns + 1; end if;
      end loop;
      return Result;
   end Project_Label;
end Hoeflin_Boundary_Models;

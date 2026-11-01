with Hoeflin_Core;
with Interfaces;
package Hoeflin_Boundary_Models with SPARK_Mode, Ghost is
   use Hoeflin_Core;
   use type Interfaces.Unsigned_64;

   --  Executable ghost acceptance models, not axioms about libm accuracy.
   function Probability_Value (Value : Real) return Boolean is
     (Value in 0.0 .. 1.0) with Global => null;
   function Sqrt_Acceptable (X, Value : Real) return Boolean is
     (Value >= 0.0
      and then (if X <= 1.0 then Value <= 1.0)
      and then (if X >= 1.0E-6 then Value >= 0.0005))
     with Global => null;
   function Inverse_Bracket_Acceptable (P, Lower_SF, Upper_SF : Real)
      return Boolean is
     (Lower_SF >= P and then Upper_SF <= P) with Global => null;
   function Rare_Quantile_Acceptable (Value : Real) return Boolean is
     (Value in 3.0 .. 10.0) with Global => null;
   function Log_Acceptable (Value : Real) return Boolean is
     (Value in -38.0 .. 0.0) with Global => null;
   function Radius_Acceptable (U, Radius : Real) return Boolean is
     (U in 2.0 ** (-53) .. 1.0 - 2.0 ** (-53)
      and then Radius in 0.0 .. 9.0) with Global => null;
   function Trig_Acceptable (Value : Real) return Boolean is
     (Value in -1.0 .. 1.0) with Global => null;
   function Erfc_Scaling (Raw : Real) return Real
     with Global => null, Pre => Raw in 0.0 .. 2.0,
     Post => Probability_Value (Erfc_Scaling'Result);
   procedure Observe_Sqrt (X, Value : Real)
     with Global => null, Pre => Sqrt_Acceptable (X, Value);
   procedure Observe_Probability (Value : Real)
     with Global => null, Pre => Probability_Value (Value);
   procedure Observe_Erfc (Raw, Scaled : Real)
     with Global => null, Pre => Raw in 0.0 .. 2.0
       and then Scaled = Erfc_Scaling (Raw) and then Probability_Value (Scaled);
   procedure Observe_Inverse_Bracket (P, Lower_SF, Upper_SF : Real)
     with Global => null,
       Pre => Inverse_Bracket_Acceptable (P, Lower_SF, Upper_SF);
   procedure Observe_Rare_Quantile (Value : Real)
     with Global => null, Pre => Rare_Quantile_Acceptable (Value);
   procedure Observe_Log_Radius (U, Log_U, Radius : Real)
     with Global => null,
       Pre => Log_Acceptable (Log_U) and then Radius_Acceptable (U, Radius);
   procedure Observe_Trig (Value : Real)
     with Global => null, Pre => Trig_Acceptable (Value);

   type Event_Kind is
     (No_Event, Options_Read, Simulation_Header_Event, Simulation_Row_Event,
      Calculations_Header_Event, Calculation_Row_Event, Infinite_Row_Event,
      Examples_Header_Event, Example_Event);
   type Section_Kind is (No_Section, Simulation, Calculations, Examples);
   type Event_Count is mod 2 ** 64;
   type Payload is record
      N : Natural := 0;
      Trials : Sample_Count := 0;
      Seed : Interfaces.Unsigned_64 := 0;
      Mean, Variance, Value : Real := 0.0;
      Counts : Tail_Counts := (others => 0);
      Rate_Two, Rate_Three, Expected_Two, Expected_Three : Real := 0.0;
      Factor : Variance_Value := 1.0;
      Z : Positive_Z := 0.0;
      Score : IQ_Value := 100.0;
      Label_Length : Natural := 0;
   end record;
   Empty_Payload : constant Payload := (others => <>);
   type Report_Trace is record
      Section : Section_Kind := No_Section;
      Last_Event : Event_Kind := No_Event;
      Events : Event_Count := 0;
      Rows : Event_Count := 0;
      Columns : Natural range 0 .. 11 := 0;
      Data : Payload := Empty_Payload;
      Last_Call_Admissible : Boolean := False;
   end record;
   Empty_Trace : constant Report_Trace := (others => <>);

   function Column_Count (Event : Event_Kind) return Natural is
     (case Event is
        when Simulation_Header_Event | Simulation_Row_Event => 11,
        when Calculations_Header_Event | Calculation_Row_Event | Infinite_Row_Event => 4,
        when Example_Event => 2,
        when others => 0) with Global => null;
   function Options_Payload (Trials : Sample_Count; Seed : Interfaces.Unsigned_64)
      return Payload is
     ((Trials => Trials, Seed => Seed, others => <>)) with Global => null;
   function Calculation_Payload
     (N : Natural; Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value)
      return Payload is
     ((N => N, Factor => Factor, Z => Z, Score => Score, others => <>))
     with Global => null;
   function Simulation_Payload
     (N : Test_Count; Trials : Sample_Count; Mean, Variance : Real;
      C : Tail_Counts; Rate_Two, Rate_Three, Expected_Two, Expected_Three : Real)
      return Payload is
     ((N => N, Trials => Trials, Mean => Mean, Variance => Variance, Counts => C,
       Rate_Two => Rate_Two, Rate_Three => Rate_Three,
       Expected_Two => Expected_Two, Expected_Three => Expected_Three, others => <>))
     with Global => null;
   function Example_Payload (Label_Length : Natural; Value : Real) return Payload is
     ((Label_Length => Label_Length, Value => Value, others => <>))
     with Global => null;
   function Can_Emit (Trace : Report_Trace; Event : Event_Kind; Data : Payload)
      return Boolean is
     (case Event is
        when No_Event => False,
        when Options_Read => Data.Trials >= 2,
        when Simulation_Row_Event => Trace.Section = Simulation
          and then Data.Trials >= 2 and then Valid (Data.Counts)
          and then Data.Counts.Total = Data.Trials
          and then Probability_Value (Data.Rate_Two)
          and then Probability_Value (Data.Rate_Three)
          and then Probability_Value (Data.Expected_Two)
          and then Probability_Value (Data.Expected_Three),
        when Calculation_Row_Event | Infinite_Row_Event => Trace.Section = Calculations,
        when Example_Event => Trace.Section = Examples,
        when others => True) with Global => null;
   function Transition (Trace : Report_Trace; Event : Event_Kind; Data : Payload)
      return Report_Trace
     with Global => null,
     Post => Transition'Result.Last_Event = Event
       and then Transition'Result.Events = Trace.Events + 1
       and then Transition'Result.Columns = Column_Count (Event)
       and then Transition'Result.Data = Data
       and then Transition'Result.Last_Call_Admissible = Can_Emit (Trace, Event, Data)
       and then Transition'Result.Section =
         (case Event is
            when Simulation_Header_Event => Simulation,
            when Calculations_Header_Event => Calculations,
            when Examples_Header_Event => Examples,
            when others => Trace.Section);
   procedure Note (Trace : in out Report_Trace; Event : Event_Kind; Data : Payload)
     with Global => null,
     Post => Trace = Transition (Trace'Old, Event, Data);

   function Numeric_Format (Digits_After : Natural) return Boolean is
     (Digits_After = 12 or else Digits_After = 14) with Global => null;
   function Valid_Column_Label (Label : String) return Boolean is
     (Label'Length > 0 and then
        (for all C of Label => C /= ',' and then C /= ASCII.LF and then C /= ASCII.CR))
     with Global => null;
   function Decimal_Image (N : Natural; Text : String) return Boolean
     with Global => null,
     Post => (if Decimal_Image'Result then Valid_Column_Label (Text));
   procedure Observe_Decimal_Image (N : Natural; Text : String)
     with Global => null, Pre => Decimal_Image (N, Text);
   type Number_Projection is record
      Value : Real;
      Decimal_Places : Natural;
   end record;
   function Project_Number (Value : Real; Decimal_Places : Natural)
      return Number_Projection is
     ((Value => Value, Decimal_Places => Decimal_Places)) with Global => null;
   procedure Observe_Number
     (Value : Real; Decimal_Places : Natural; Projection : Number_Projection)
     with Global => null,
       Pre => Projection.Value = Value and then Projection.Decimal_Places = Decimal_Places;
   type Label_Projection is record
      Length, Commas, Line_Feeds, Carriage_Returns : Natural;
   end record;
   function Project_Label (Text : String) return Label_Projection
     with Global => null,
       Post => Project_Label'Result.Length = Text'Length
         and then Project_Label'Result.Commas <= Text'Length
         and then Project_Label'Result.Line_Feeds <= Text'Length
         and then Project_Label'Result.Carriage_Returns <= Text'Length;
   procedure Observe_Label (Text : String; Projection : Label_Projection)
     with Global => null,
       Pre => Projection.Length = Text'Length and then Projection.Commas <= Text'Length
         and then Projection.Line_Feeds <= Text'Length
         and then Projection.Carriage_Returns <= Text'Length;
end Hoeflin_Boundary_Models;

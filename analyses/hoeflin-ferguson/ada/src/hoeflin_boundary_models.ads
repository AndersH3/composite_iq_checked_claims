with Hoeflin_Core;
with Interfaces;
package Hoeflin_Boundary_Models with SPARK_Mode is
   use Hoeflin_Core;
   use type Interfaces.Unsigned_64;

   --  Executable ghost acceptance models, not axioms about libm accuracy.
   function Probability_Value (Value : Real) return Boolean is
     (Value in 0.0 .. 1.0) with
     Global => null,
     Post => (if Probability_Value'Result then Value >= 0.0) and then
       (if Probability_Value'Result then Value <= 1.0) and then
       (if Value in 0.0 .. 1.0 then Probability_Value'Result),
     Depends => (Probability_Value'Result => Value);
   function Sqrt_Acceptable (X, Value : Real) return Boolean is
     (Value >= 0.0
      and then (if X <= 1.0 then Value <= 1.0)
      and then (if X >= 1.0E-6 then Value >= 0.0005)) with
     Global => null,
     Post => (if Sqrt_Acceptable'Result then Value >= 0.0) and then
       (if Sqrt_Acceptable'Result then (if X <= 1.0 then Value <= 1.0) and then (if X >= 1.0E-6 then Value >= 0.0005)) and then
       (if Value >= 0.0
      and then (if X <= 1.0 then Value <= 1.0)
      and then (if X >= 1.0E-6 then Value >= 0.0005) then Sqrt_Acceptable'Result),
     Depends => (Sqrt_Acceptable'Result => (X, Value));
   function Inverse_Bracket_Acceptable (P, Lower_SF, Upper_SF : Real)
      return Boolean is
     (Lower_SF >= P and then Upper_SF <= P) with
     Global => null,
     Post => (if Inverse_Bracket_Acceptable'Result then Lower_SF >= P) and then
       (if Inverse_Bracket_Acceptable'Result then Upper_SF <= P) and then
       (if Lower_SF >= P and then Upper_SF <= P then Inverse_Bracket_Acceptable'Result),
     Depends => (Inverse_Bracket_Acceptable'Result => (P, Lower_SF, Upper_SF));
   function Rare_Quantile_Acceptable (Value : Real) return Boolean is
     (Value in 3.0 .. 10.0) with
     Global => null,
     Post => (if Rare_Quantile_Acceptable'Result then Value >= 3.0) and then
       (if Rare_Quantile_Acceptable'Result then Value <= 10.0) and then
       (if Value in 3.0 .. 10.0 then Rare_Quantile_Acceptable'Result),
     Depends => (Rare_Quantile_Acceptable'Result => Value);
   function Log_Acceptable (Value : Real) return Boolean is
     (Value in -38.0 .. 0.0) with
     Global => null,
     Post => (if Log_Acceptable'Result then Value >= -38.0) and then
       (if Log_Acceptable'Result then Value <= 0.0) and then
       (if Value in -38.0 .. 0.0 then Log_Acceptable'Result),
     Depends => (Log_Acceptable'Result => Value);
   function Radius_Acceptable (U, Radius : Real) return Boolean is
     (U in 2.0 ** (-53) .. 1.0 - 2.0 ** (-53)
      and then Radius in 0.0 .. 9.0) with
     Global => null,
     Post => (if Radius_Acceptable'Result then U in 2.0 ** (-53) .. 1.0 - 2.0 ** (-53)) and then
       (if Radius_Acceptable'Result then Radius in 0.0 .. 9.0) and then
       (if U in 2.0 ** (-53) .. 1.0 - 2.0 ** (-53)
      and then Radius in 0.0 .. 9.0 then Radius_Acceptable'Result),
     Depends => (Radius_Acceptable'Result => (U, Radius));
   function Trig_Acceptable (Value : Real) return Boolean is
     (Value in -1.0 .. 1.0) with
     Global => null,
     Post => (if Trig_Acceptable'Result then Value >= -1.0) and then
       (if Trig_Acceptable'Result then Value <= 1.0) and then
       (if Value in -1.0 .. 1.0 then Trig_Acceptable'Result),
     Depends => (Trig_Acceptable'Result => Value);
   function Erfc_Scaling (Raw : Real) return Real with
     Global => null,
     Pre => Raw in 0.0 .. 2.0,
     Post => (Probability_Value (Erfc_Scaling'Result)) and then
       (Erfc_Scaling'Result = 0.5 * Raw),
     Depends => (Erfc_Scaling'Result => Raw);
   procedure Observe_Sqrt (X, Value : Real) with
     Ghost,
     Global => null,
     Pre => Sqrt_Acceptable (X, Value),
     Post => Value >= 0.0 and then (if X <= 1.0 then Value <= 1.0),
     Depends => (null => (X, Value));
   procedure Observe_Probability (Value : Real) with
     Ghost,
     Global => null,
     Pre => Probability_Value (Value),
     Post => Value >= 0.0 and then Value <= 1.0,
     Depends => (null => Value);
   procedure Observe_Erfc (Raw, Scaled : Real) with Ghost,
     Global => null,
     Pre => Raw in 0.0 .. 2.0
       and then Scaled = Erfc_Scaling (Raw) and then Probability_Value (Scaled),
     Post => Scaled = Erfc_Scaling (Raw),
     Depends => (null => (Raw, Scaled));
   procedure Observe_Inverse_Bracket (P, Lower_SF, Upper_SF : Real) with Ghost,
     Global => null,
     Pre => Inverse_Bracket_Acceptable (P, Lower_SF, Upper_SF),
     Post => Lower_SF >= P and then Upper_SF <= P,
     Depends => (null => (P, Lower_SF, Upper_SF));
   procedure Observe_Rare_Quantile (Value : Real) with
     Ghost,
     Global => null,
     Pre => Rare_Quantile_Acceptable (Value),
     Post => Value >= 3.0 and then Value <= 10.0,
     Depends => (null => Value);
   procedure Observe_Log_Radius (U, Log_U, Radius : Real) with Ghost,
     Global => null,
     Pre => Log_Acceptable (Log_U) and then Radius_Acceptable (U, Radius),
     Post => U > 0.0 and then Radius in 0.0 .. 9.0,
     Depends => (null => (U, Log_U, Radius));
   procedure Observe_Trig (Value : Real) with
     Ghost,
     Global => null,
     Pre => Trig_Acceptable (Value),
     Post => Value >= -1.0 and then Value <= 1.0,
     Depends => (null => Value);

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
        when others => 0) with
     Global => null,
     Post => (if Event in Simulation_Header_Event | Simulation_Row_Event then Column_Count'Result = 11) and then
       (if Event in Calculations_Header_Event | Calculation_Row_Event | Infinite_Row_Event then Column_Count'Result = 4) and then
       (if Event = Example_Event then Column_Count'Result = 2) and then
       (if Event in No_Event | Options_Read | Examples_Header_Event then Column_Count'Result = 0),
     Depends => (Column_Count'Result => Event);
   function Options_Payload (Trials : Sample_Count; Seed : Interfaces.Unsigned_64)
      return Payload is
     ((Trials => Trials, Seed => Seed, others => <>)) with
     Global => null,
     Post => (Options_Payload'Result.Trials = Trials) and then
       (Options_Payload'Result.Seed = Seed) and then
       (Options_Payload'Result.N = 0),
     Depends => (Options_Payload'Result => (Trials, Seed));
   function Calculation_Payload
     (N : Natural; Factor : Variance_Value; Z : Positive_Z; Score : IQ_Value)
      return Payload is
     ((N => N, Factor => Factor, Z => Z, Score => Score, others => <>)) with
     Global => null,
     Post => (Calculation_Payload'Result.N = N) and then
       (Calculation_Payload'Result.Factor = Factor) and then
       (Calculation_Payload'Result.Z = Z) and then
       (Calculation_Payload'Result.Score = Score),
     Depends => (Calculation_Payload'Result => (N, Factor, Z, Score));
   function Simulation_Payload
     (N : Test_Count; Trials : Sample_Count; Mean, Variance : Real;
      C : Tail_Counts; Rate_Two, Rate_Three, Expected_Two, Expected_Three : Real)
      return Payload is
     ((N => N, Trials => Trials, Mean => Mean, Variance => Variance, Counts => C,
       Rate_Two => Rate_Two, Rate_Three => Rate_Three,
       Expected_Two => Expected_Two, Expected_Three => Expected_Three, others => <>)) with
     Global => null,
     Post => (Simulation_Payload'Result.N = N) and then
       (Simulation_Payload'Result.Trials = Trials) and then
       (Simulation_Payload'Result.Mean = Mean) and then
       (Simulation_Payload'Result.Variance = Variance) and then
       (Simulation_Payload'Result.Counts = C) and then
       (Simulation_Payload'Result.Rate_Two = Rate_Two) and then
       (Simulation_Payload'Result.Rate_Three = Rate_Three) and then
       (Simulation_Payload'Result.Expected_Two = Expected_Two) and then
       (Simulation_Payload'Result.Expected_Three = Expected_Three),
     Depends => (Simulation_Payload'Result => (N, Trials, Mean, Variance, C, Rate_Two, Rate_Three, Expected_Two, Expected_Three));
   function Example_Payload (Label_Length : Natural; Value : Real) return Payload is
     ((Label_Length => Label_Length, Value => Value, others => <>)) with
     Global => null,
     Post => (Example_Payload'Result.Label_Length = Label_Length) and then
       (Example_Payload'Result.Value = Value) and then
       (Example_Payload'Result.N = 0),
     Depends => (Example_Payload'Result => (Label_Length, Value));
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
        when others => True) with
     Global => null,
     Post => (if Event = No_Event then not Can_Emit'Result) and then
       (if Event = Options_Read then Can_Emit'Result = (Data.Trials >= 2)) and then
       (if Event = Example_Event then Can_Emit'Result = (Trace.Section = Examples)),
     Depends => (Can_Emit'Result => (Trace, Event, Data));
   function Transition (Trace : Report_Trace; Event : Event_Kind; Data : Payload)
      return Report_Trace with
     Global => null,
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
            when others => Trace.Section),
     Depends => (Transition'Result => (Trace, Event, Data));
   procedure Note (Trace : in out Report_Trace; Event : Event_Kind; Data : Payload) with
     Global => null,
     Post => (Trace = Transition (Trace'Old, Event, Data)) and then
       (Trace.Last_Event = Event) and then
       (Trace.Data = Data),
     Depends => (Trace => (Trace, Event, Data));

   function Numeric_Format (Digits_After : Natural) return Boolean is
     (Digits_After = 12 or else Digits_After = 14) with
     Global => null,
     Post => (if Numeric_Format'Result then Digits_After = 12 or else Digits_After = 14) and then
       (if Digits_After = 12 then Numeric_Format'Result) and then
       (if Digits_After = 14 then Numeric_Format'Result),
     Depends => (Numeric_Format'Result => Digits_After);
   function Valid_Column_Label (Label : String) return Boolean is
     (Label'Length > 0 and then
        (for all C of Label => C /= ',' and then C /= ASCII.LF and then C /= ASCII.CR)) with
     Global => null,
     Post => (if Valid_Column_Label'Result then Label'Length > 0) and then
       (if Valid_Column_Label'Result then (for all C of Label => C /= ',' and then C /= ASCII.LF and then C /= ASCII.CR)) and then
       (if Label'Length > 0 and then (for all C of Label => C /= ',' and then C /= ASCII.LF and then C /= ASCII.CR) then Valid_Column_Label'Result),
     Depends => (Valid_Column_Label'Result => Label);
   function Decimal_Image (N : Natural; Text : String) return Boolean with
     Global => null,
     Post => (if Decimal_Image'Result then Valid_Column_Label (Text)) and then
       (if Text'Length = 0 then not Decimal_Image'Result) and then
       (if Text'Length > 1 and then Text (Text'First) = '0' then not Decimal_Image'Result),
     Depends => (Decimal_Image'Result => (N, Text));
   procedure Observe_Decimal_Image (N : Natural; Text : String) with
     Ghost,
     Global => null,
     Pre => Decimal_Image (N, Text),
     Post => Valid_Column_Label (Text) and then Text'Length > 0,
     Depends => (null => (N, Text));
   type Number_Projection is record
      Value : Real;
      Decimal_Places : Natural;
   end record;
   function Project_Number (Value : Real; Decimal_Places : Natural)
      return Number_Projection is
     ((Value => Value, Decimal_Places => Decimal_Places)) with
     Global => null,
     Pre => Numeric_Format (Decimal_Places),
     Post => (Project_Number'Result.Value = Value) and then
       (Project_Number'Result.Decimal_Places = Decimal_Places),
     Depends => (Project_Number'Result => (Value, Decimal_Places));
   procedure Observe_Number
     (Value : Real; Decimal_Places : Natural; Projection : Number_Projection) with Ghost,
     Global => null,
     Pre => Projection.Value = Value and then Projection.Decimal_Places = Decimal_Places,
     Post => Projection.Value = Value and then Projection.Decimal_Places = Decimal_Places,
     Depends => (null => (Value, Decimal_Places, Projection));
   type Label_Projection is record
      Length, Commas, Line_Feeds, Carriage_Returns : Natural;
   end record;
   function Project_Label (Text : String) return Label_Projection with
     Global => null,
     Post => Project_Label'Result.Length = Text'Length
         and then Project_Label'Result.Commas <= Text'Length
         and then Project_Label'Result.Line_Feeds <= Text'Length
         and then Project_Label'Result.Carriage_Returns <= Text'Length,
     Depends => (Project_Label'Result => Text);
   procedure Observe_Label (Text : String; Projection : Label_Projection) with Ghost,
     Global => null,
     Pre => Projection.Length = Text'Length and then Projection.Commas <= Text'Length
         and then Projection.Line_Feeds <= Text'Length
         and then Projection.Carriage_Returns <= Text'Length,
     Post => Projection.Length = Text'Length,
     Depends => (null => (Text, Projection));
end Hoeflin_Boundary_Models;

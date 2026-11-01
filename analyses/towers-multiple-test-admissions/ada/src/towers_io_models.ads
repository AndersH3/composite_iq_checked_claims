with Admission_Core;
with Towers_Engine;
--  Ghost observations and requests, not a model of operating-system success.
--  Decimal parsing is exact for bounded, unsigned, digit-only input. Other
--  Ada 'Value syntaxes retain their original parser and are not equated to it.
package Towers_IO_Models with SPARK_Mode, Ghost is
   use type Towers_Engine.Results;
   subtype Option_Limit is Long_Long_Integer range 0 .. 2_147_483_646;
   type Decimal_Result is record
      Recognized : Boolean := False;
      Value : Option_Limit := 0;
   end record;
   function Decimal_Input (Text : String; Limit : Option_Limit)
      return Decimal_Result
     with Global => null,
     Post => Decimal_Input'Result.Value <= Limit
       and (if Decimal_Input'Result.Recognized then Text'Length > 0);
   function Option_Agrees
     (Text : String; Actual : Long_Long_Integer; Limit : Option_Limit)
      return Boolean with Global => null;

   function Valid_Trials (Value : Long_Long_Integer) return Boolean
   is (Value in 1 .. Admission_Core.Max_Trials);
   function Valid_Seed (Value : Long_Long_Integer) return Boolean
   is (Value in 1 .. 2_147_483_646);

   function Real_Field (Text : String) return Boolean
   is (Text'Length > 0
       and then (for all C of Text => C in '0' .. '9' or C = '.'
                   or C = 'E' or C = 'e' or C = '+' or C = '-')
       and then (for some C of Text => C in '0' .. '9'));
   function Integer_Field (Text : String) return Boolean
   is (Text'Length > 0
       and then (Text (Text'First) in '0' .. '9' or else
                 (Text (Text'First) = '-' and then Text'Length > 1))
       and then (for all I in Text'Range =>
          (if I /= Text'First then Text (I) in '0' .. '9')));
   function Case_Name (K : Towers_Engine.Case_Index) return String
   is (case K is
         when 1 => "equal_top_2_percent",
         when 2 => "equal_top_0_1_percent",
         when 3 => "equal_top_1_in_33000",
         when 4 => "mixed_top_2_and_0_1_percent");
   function Case_Name_Agrees (K : Towers_Engine.Case_Index; Text : String)
      return Boolean
   is (Text = Case_Name (K));

   function Report_Valid
     (Trials, Seed : Long_Long_Integer; Data : Towers_Engine.Results)
      return Boolean
   is (Valid_Trials (Trials) and then Valid_Seed (Seed)
       and then (for all K in Towers_Engine.Case_Index =>
          Admission_Core.Total (Data.Simulation (K).Cells) = Trials));

   type File_Kind is (Calculations, Grid, Calibration, Simulation);
   function Field_Count (Kind : File_Kind) return Positive
   is (case Kind is
         when Calculations => 16,
         when Grid => 7,
         when Calibration => 6,
         when Simulation => 15);
   function Data_Row_Count (Kind : File_Kind) return Positive
   is (case Kind is
         when Calculations | Simulation => 4,
         when Grid => 3,
         when Calibration => 1);

   type Stage is (Empty, Trials_Observed, Options_Observed,
                  Report_Requested, Normal_Return_Observed);
   type Receipt is record
      Status : Stage := Empty;
      Trials, Seed : Long_Long_Integer := 0;
      Requested_Files : Natural := 0;
      Requested_Data_Rows : Natural := 0;
      Snapshot : Towers_Engine.Results;
   end record;
   procedure Observe_Trials
     (Trace : in out Receipt; Actual : Towers_Engine.Trial_Count)
     with Global => null, Pre => Trace.Status = Empty,
     Post => Trace.Status = Trials_Observed and Trace.Trials = Actual
       and Trace.Seed = Trace.Seed'Old;
   procedure Observe_Seed
     (Trace : in out Receipt; Actual : Towers_Engine.Seed_Value)
     with Global => null, Pre => Trace.Status = Trials_Observed,
     Post => Trace.Status = Options_Observed and Trace.Seed = Long_Long_Integer (Actual)
       and Trace.Trials = Trace.Trials'Old;
   procedure Request_Report
     (Trace : in out Receipt; Trials : Towers_Engine.Trial_Count;
      Seed : Towers_Engine.Seed_Value; Data : Towers_Engine.Results)
     with Global => null,
     Pre => Trace.Status = Options_Observed and Trace.Trials = Trials
       and Trace.Seed = Long_Long_Integer (Seed) and Report_Valid (Trials, Long_Long_Integer (Seed), Data),
     Post => Trace.Status = Report_Requested and Trace.Snapshot = Data
       and Trace.Trials = Trials and Trace.Seed = Long_Long_Integer (Seed)
       and Trace.Requested_Files = 4 and Trace.Requested_Data_Rows = 12;
   procedure Observe_Normal_Return
     (Trace : in out Receipt; Data : Towers_Engine.Results)
     with Global => null,
     Pre => Trace.Status = Report_Requested and Trace.Snapshot = Data,
     Post => Trace.Status = Normal_Return_Observed and Trace.Snapshot = Data
       and Trace.Trials = Trace.Trials'Old and Trace.Seed = Trace.Seed'Old
       and Trace.Requested_Files = Trace.Requested_Files'Old
       and Trace.Requested_Data_Rows = Trace.Requested_Data_Rows'Old;
   procedure Observe_Option
     (Text : String; Actual : Long_Long_Integer; Limit : Option_Limit)
     with Global => null, Pre => Option_Agrees (Text, Actual, Limit);
   procedure Check_Trials (Actual : Long_Long_Integer)
     with Global => null, Pre => Valid_Trials (Actual);
   procedure Check_Seed (Actual : Long_Long_Integer)
     with Global => null, Pre => Valid_Seed (Actual);
   procedure Check_Real_Field (Text : String)
     with Global => null, Pre => Real_Field (Text);
   procedure Check_Integer_Field (Text : String)
     with Global => null, Pre => Integer_Field (Text);
   procedure Check_Case_Name (K : Towers_Engine.Case_Index; Text : String)
     with Global => null, Pre => Case_Name_Agrees (K, Text);
   procedure Check_Report (Trials, Seed : Long_Long_Integer; Data : Towers_Engine.Results)
     with Global => null, Pre => Report_Valid (Trials, Seed, Data);
   procedure Check_Completed (Trace : Receipt)
     with Global => null,
     Pre => Trace.Status = Normal_Return_Observed
       and Trace.Requested_Files = 4 and Trace.Requested_Data_Rows = 12;
end Towers_IO_Models;

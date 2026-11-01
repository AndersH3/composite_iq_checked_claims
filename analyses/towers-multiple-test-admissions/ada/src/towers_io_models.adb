package body Towers_IO_Models with SPARK_Mode is
   function Decimal_Input (Text : String; Limit : Option_Limit)
      return Decimal_Result
   is
      Value : Option_Limit := 0;
      Digit : Long_Long_Integer;
   begin
      if Text'Length = 0 then
         return (Recognized => False, Value => 0);
      end if;
      for C of Text loop
         pragma Loop_Invariant (Value <= Limit);
         if C not in '0' .. '9' then
            return (Recognized => False, Value => 0);
         end if;
         Digit := Character'Pos (C) - Character'Pos ('0');
         if Digit > Limit or else Value > (Limit - Digit) / 10 then
            return (Recognized => False, Value => 0);
         end if;
         Value := Value * 10 + Digit;
      end loop;
      return (Recognized => True, Value => Value);
   end Decimal_Input;

   function Option_Agrees
     (Text : String; Actual : Long_Long_Integer; Limit : Option_Limit)
      return Boolean
   is
      Parsed : constant Decimal_Result := Decimal_Input (Text, Limit);
   begin
      return Actual in 0 .. Limit and then
        (if Parsed.Recognized then Parsed.Value = Actual);
   end Option_Agrees;

   procedure Observe_Trials
     (Trace : in out Receipt; Actual : Towers_Engine.Trial_Count) is
   begin
      Trace.Status := Trials_Observed;
      Trace.Trials := Actual;
   end Observe_Trials;
   procedure Observe_Seed
     (Trace : in out Receipt; Actual : Towers_Engine.Seed_Value) is
   begin
      Trace.Status := Options_Observed;
      Trace.Seed := Long_Long_Integer (Actual);
   end Observe_Seed;
   procedure Request_Report
     (Trace : in out Receipt; Trials : Towers_Engine.Trial_Count;
      Seed : Towers_Engine.Seed_Value; Data : Towers_Engine.Results) is
   begin
      Trace.Status := Report_Requested;
      Trace.Trials := Trials;
      Trace.Seed := Long_Long_Integer (Seed);
      Trace.Snapshot := Data;
      Trace.Requested_Files := 4;
      Trace.Requested_Data_Rows := Data_Row_Count (Calculations) + Data_Row_Count (Grid)
        + Data_Row_Count (Calibration) + Data_Row_Count (Simulation);
   end Request_Report;
   procedure Observe_Normal_Return
     (Trace : in out Receipt; Data : Towers_Engine.Results) is
   begin
      Trace.Status := Normal_Return_Observed;
   end Observe_Normal_Return;
   procedure Observe_Option
     (Text : String; Actual : Long_Long_Integer; Limit : Option_Limit) is
   begin null; end Observe_Option;
   procedure Check_Trials (Actual : Long_Long_Integer) is
   begin null; end Check_Trials;
   procedure Check_Seed (Actual : Long_Long_Integer) is
   begin null; end Check_Seed;
   procedure Check_Real_Field (Text : String) is
   begin null; end Check_Real_Field;
   procedure Check_Integer_Field (Text : String) is
   begin null; end Check_Integer_Field;
   procedure Check_Case_Name (K : Towers_Engine.Case_Index; Text : String) is
   begin null; end Check_Case_Name;
   procedure Check_Report (Trials, Seed : Long_Long_Integer; Data : Towers_Engine.Results) is
   begin null; end Check_Report;
   procedure Check_Completed (Trace : Receipt) is
   begin null; end Check_Completed;
end Towers_IO_Models;

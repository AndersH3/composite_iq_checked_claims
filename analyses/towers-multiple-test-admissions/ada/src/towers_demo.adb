with Towers_Engine;
with Towers_IO;
procedure Towers_Demo with SPARK_Mode,
  Global => (In_Out => Towers_IO.IO_State)
is
   Trials : constant Towers_Engine.Trial_Count := Towers_IO.Read_Trials;
   Seed : constant Towers_Engine.Seed_Value := Towers_IO.Read_Seed;
   Data : Towers_Engine.Results;
begin
   Towers_Engine.Compute (Trials, Seed, Data);
   Towers_IO.Write_Report (Trials, Seed, Data);
end Towers_Demo;

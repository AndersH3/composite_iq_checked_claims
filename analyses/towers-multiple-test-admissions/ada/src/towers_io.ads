with Towers_Engine;
package Towers_IO with SPARK_Mode,
  Abstract_State => IO_State,
  Initializes => IO_State
is
   --  Explicit unproved system boundary. Bodies parse external arguments and
   --  format/write files; their exceptions and operating-system effects are
   --  not certified by the numerical/SPARK proof.
   function Read_Trials return Towers_Engine.Trial_Count
     with Global => (Input => IO_State);
   function Read_Seed return Towers_Engine.Seed_Value
     with Global => (Input => IO_State);
   procedure Write_Report (Trials : Towers_Engine.Trial_Count;
                           Seed : Towers_Engine.Seed_Value;
                           Data : Towers_Engine.Results)
     with Global => (In_Out => IO_State);
end Towers_IO;

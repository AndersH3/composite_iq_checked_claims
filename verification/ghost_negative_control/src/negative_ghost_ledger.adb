package body Negative_Ghost_Ledger with SPARK_Mode is
   procedure Record_Event (Count : in out Event_Count) is
   begin
      Count := Count + 0;
   end Record_Event;
end Negative_Ghost_Ledger;

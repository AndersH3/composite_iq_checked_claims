--  Deliberately wrong Ghost contract: this fixture must not be accepted.
--  It is excluded from both production projects.
package Negative_Ghost_Ledger with SPARK_Mode, Ghost is
   subtype Event_Count is Natural range 0 .. 100;
   procedure Record_Event (Count : in out Event_Count) with
     Global => null,
     Pre => Count < Event_Count'Last,
     Post => Count = Count'Old + 1 and then Count > Count'Old,
     Depends => (Count => Count);
end Negative_Ghost_Ledger;
